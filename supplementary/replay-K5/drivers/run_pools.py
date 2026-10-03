"""run_pools.py — memory-aware two-pool driver for the K = 5 replay (L1_1e, 28 Sep 2026).

Start from Git Bash with the wrapper:  bash .../replay/run_pools.sh [options]

Options
  --light-jobs L     LIGHT pool size (default 16): Data, point records, Cells (≈ 0.3–0.5 GB each). Goes through a
                     COPY of leanrun.sh (replay/light_tools/leanrun.sh: own slot dir, own log, same FREEZE file and timeout),
                     so light files never take a machine-wide slot.
  --heavy-jobs H     HEAVY pool size (default 4): ReplayCommon, leaves (≤ 3.5 GB), Assembly (1.4 GB), Cert (3.5 GB).
                     Goes through the MACHINE-WIDE rh72/lean_tools/leanrun.sh (shared slots). H = 5 or 6 needs --allow-6.
  --allow-6          permit H up to 6.
  --mem-heavy-gb G   hold a heavy launch while free physical memory < G GB (default 4.0); each hold is logged.
  --mem-light-gb G   hold a light launch while free physical memory < G GB (default 1.5).
  --abort-below-gb G stop launching and end the run (exit 6) if free memory falls below G GB (default 0 = off).
  --class c          restrict to class c (repeatable). Default: all 20 classes + the two top files.
  --no-top           do not compile the top files.
  --max-heavy-files N  stop launching heavy files after N launches (tests).
  --budget S         launch nothing new after S seconds (exit 3; resumable).
  --olean DIR        replay olean folder (default replay/olean_lib); --reset empties it.
  --dry-run          print the schedule and the counts per pool; compile nothing.
Schedule: phase 1 = every light file of every class (Cells of a class after its point files) + ReplayCommon (heavy);
phase 2 = leaves of all classes; Assembly after the class's leaves, Cert after Assembly (heavy); phase 3 = ReplayAM5, then
ReplayHeadlines, each ALONE. Memory bound at any moment: L x 0.5 GB (phase 1) or H x 3.5 GB (phase 2), never both.
Guards kept from run_replay.sh: stamp (green commit + manifest sha256) refused if different (exit 4), stop if green changes
(exit 5), .olean.part renaming, stop on the first genuine failure (exit 1), resumability, SUMMARY per class. leanrun exit 75
(no slot within its wait limit) is retried up to --max-retry75 times (default 12). Status file: replay/STATUS.txt (every 60 s).
Log: replay/replay.log (same line format as run_replay.sh; extra lines HOLD, RETRY75, MEM, PHASE).
Exit codes: 0 done, 1 file failed, 2 setup, 3 budget, 4 stale stamp, 5 green changed, 6 memory abort.
"""
import sys, os, re, time, json, hashlib, subprocess, argparse, ctypes, glob
try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

R = os.path.dirname(os.path.abspath(__file__)).replace('\\', '/')
RH72 = os.path.normpath(os.path.join(R, '..', '..', '..')).replace('\\', '/')
HEAVY_LEANRUN = f'{RH72}/lean_tools/leanrun.sh'
LIGHT_LEANRUN = f'{R}/light_tools/leanrun.sh'
GREEN = os.environ.get('LEANRUN_TREE')
if not GREEN:
    raise SystemExit('set the LEANRUN_TREE environment variable to your zeta-23-lean checkout path')
LOG = f'{R}/replay.log'
STATUS = f'{R}/STATUS.txt'
ALL = ['11111', '11112', '11121', '11122', '11211', '11212', '11221', '11222', '12112', '12121', '12122', '12212',
       '12221', '12222', '21112', '21122', '21212', '21222', '22122', '22222']
BAD = ['CheckerBase', 'CheckerLeaves', 'CheckerCoreV3', 'CertSpecAM5', 'NodeDefs', 'ChainV3', 'ChallengeZetaS', 'Interfaces']
# pilot unit costs (lean-seconds) for the progress estimate
COST = {'Data': 2.4, 'Pts': 82.5, 'Cells': 13.3, 'Leaves': 28.7, 'Assembly': 25.0, 'Cert': 16.7, 'Common': 17.5, 'Top': 60.0}

ap = argparse.ArgumentParser()
ap.add_argument('--light-jobs', type=int, default=16); ap.add_argument('--heavy-jobs', type=int, default=4)
ap.add_argument('--allow-6', action='store_true'); ap.add_argument('--mem-heavy-gb', type=float, default=4.0)
ap.add_argument('--mem-light-gb', type=float, default=1.5); ap.add_argument('--abort-below-gb', type=float, default=0.0)
ap.add_argument('--class', dest='classes', action='append'); ap.add_argument('--no-top', action='store_true')
ap.add_argument('--max-heavy-files', type=int, default=0); ap.add_argument('--budget', type=int, default=0)
ap.add_argument('--olean', default=f'{R}/olean_lib'); ap.add_argument('--reset', action='store_true')
ap.add_argument('--dry-run', action='store_true'); ap.add_argument('--max-retry75', type=int, default=12)
ap.add_argument('--bash', default=r'C:\Program Files\Git\usr\bin\bash.exe')
ap.add_argument('--heavy-slots', type=int, default=0)  # tests only: LEAN_SLOTS for heavy leanrun (default: machine-wide SLOT_COUNT)
a = ap.parse_args()
H = max(1, min(a.heavy_jobs, 6 if a.allow_6 else 4)); L = max(1, min(a.light_jobs, 24))
CLASSES = a.classes or ALL
TOP = not a.no_top and not a.classes
O = a.olean.replace('\\', '/')


class MEMORYSTATUSEX(ctypes.Structure):
    _fields_ = [('dwLength', ctypes.c_ulong), ('dwMemoryLoad', ctypes.c_ulong), ('ullTotalPhys', ctypes.c_ulonglong),
                ('ullAvailPhys', ctypes.c_ulonglong), ('ullTotalPageFile', ctypes.c_ulonglong),
                ('ullAvailPageFile', ctypes.c_ulonglong), ('ullTotalVirtual', ctypes.c_ulonglong),
                ('ullAvailVirtual', ctypes.c_ulonglong), ('ullAvailExtendedVirtual', ctypes.c_ulonglong)]


def free_gb():
    m = MEMORYSTATUSEX(); m.dwLength = ctypes.sizeof(MEMORYSTATUSEX)
    ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m))
    return m.ullAvailPhys / 2**30


def log(line):
    with open(LOG, 'a', encoding='utf-8') as f: f.write(time.strftime('%H:%M:%S') + ' ' + line + '\n')


def green_head():
    r = subprocess.run(['git', '-C', GREEN, 'rev-parse', 'HEAD'], capture_output=True, text=True)
    return r.stdout.strip()


def manifest():
    files = []
    for d in sorted(glob.glob(f'{R}/[12]*')) + [f'{R}/common']:
        for f in glob.glob(f'{d}/*.lean'):
            files.append('./' + os.path.relpath(f, R).replace('\\', '/'))
    files.sort(key=lambda s: s.encode())
    text = ''.join(f'{hashlib.sha256(open(os.path.join(R, p[2:]), "rb").read()).hexdigest()} *{p}\n' for p in files)
    open(f'{R}/MANIFEST.sha256', 'w', newline='\n').write(text)
    return hashlib.sha256(text.encode()).hexdigest(), len(files)


# ---------------- tasks
class T:
    def __init__(s, name, path, pool, kind, cls, deps):
        s.name, s.path, s.pool, s.kind, s.cls, s.deps = name, path, pool, kind, cls, deps
        s.state = 'pending'; s.retries = 0; s.proc = None; s.t0 = 0; s.out = None


def sv(p):
    m = re.search(r'(\d+)\.lean$', p); return int(m.group(1)) if m else -1


tasks = {}
def add(name, path, pool, kind, cls, deps): tasks[name] = T(name, path, pool, kind, cls, deps)
add('ReplayCommon', f'{R}/common/ReplayCommon.lean', 'heavy', 'Common', None, [])
for c in CLASSES:
    D = f'{R}/{c}'
    pts = sorted(glob.glob(f'{D}/R{c}_Pts*.lean'), key=sv); lvs = sorted(glob.glob(f'{D}/R{c}_Leaves*.lean'), key=sv)
    add(f'R{c}_Data', f'{D}/R{c}_Data.lean', 'light', 'Data', c, [])
    for p in pts: add(os.path.basename(p)[:-5], p, 'light', 'Pts', c, [])
    add(f'R{c}_Cells', f'{D}/R{c}_Cells.lean', 'light', 'Cells', c, [os.path.basename(p)[:-5] for p in pts])
    for p in lvs: add(os.path.basename(p)[:-5], p, 'heavy', 'Leaves', c, [f'R{c}_Data', f'R{c}_Cells'])
    add(f'R{c}_Assembly', f'{D}/R{c}_Assembly.lean', 'heavy', 'Assembly', c, [os.path.basename(p)[:-5] for p in lvs])
    add(f'R{c}_Cert', f'{D}/R{c}_Cert.lean', 'heavy', 'Cert', c, [f'R{c}_Assembly', 'ReplayCommon'])
if TOP:
    add('ReplayAM5', f'{R}/common/ReplayAM5.lean', 'top', 'Top', None, [f'R{c}_Cert' for c in ALL])
    add('ReplayHeadlines', f'{R}/common/ReplayHeadlines.lean', 'top', 'Top', None, ['ReplayAM5'])

npool = {p: sum(1 for t in tasks.values() if t.pool == p) for p in ('light', 'heavy', 'top')}
if a.dry_run:
    print(f'DRY RUN: classes {len(CLASSES)}, files {len(tasks)}: light {npool["light"]}, heavy {npool["heavy"]}, top {npool["top"]}')
    print(f'  light pool (L={L}, via {LIGHT_LEANRUN}): ' + ', '.join(
        f'{k} {sum(1 for t in tasks.values() if t.pool == "light" and t.kind == k)}' for k in ('Data', 'Pts', 'Cells')))
    print(f'  heavy pool (H={H}, via {HEAVY_LEANRUN}): ' + ', '.join(
        f'{k} {sum(1 for t in tasks.values() if t.pool == "heavy" and t.kind == k)}' for k in ('Common', 'Leaves', 'Assembly', 'Cert')))
    print('  phase 1: ReplayCommon (heavy) + all light files; Cells of class c after its point files')
    print('  phase 2: leaves of all classes (class order), Assembly after its leaves, Cert after Assembly')
    print('  phase 3: ReplayAM5 alone, then ReplayHeadlines alone' if TOP else '  phase 3: none (--no-top or --class)')
    up = sum(1 for t in tasks.values() if os.path.exists(f'{O}/{t.name}.olean') and os.path.getmtime(f'{O}/{t.name}.olean') > os.path.getmtime(t.path))
    est = {p: sum(COST[t.kind] for t in tasks.values() if t.pool == p and not (os.path.exists(f'{O}/{t.name}.olean') and os.path.getmtime(f'{O}/{t.name}.olean') > os.path.getmtime(t.path))) for p in ('light', 'heavy', 'top')}
    print(f'  already up to date in {O}: {up} files (their stamp is checked at a real start)')
    print(f'  estimated lean-seconds still to do: light {est["light"]:.0f}, heavy {est["heavy"]:.0f}, top {est["top"]:.0f}; '
          f'wall ≈ {est["light"]/L/60:.0f} + {est["heavy"]/H/60:.0f} + {est["top"]/60:.0f} min (pilot unit costs, no contention)')
    for c in CLASSES[:2]:
        print(f'  e.g. class {c}: ' + ' -> '.join(f'{k}×{sum(1 for t in tasks.values() if t.cls == c and t.kind == k)}' for k in ('Data', 'Pts', 'Cells', 'Leaves', 'Assembly', 'Cert')))
    sys.exit(0)

# ---------------- guards
os.makedirs(O, exist_ok=True)
for b in BAD:
    if os.path.exists(f'{O}/{b}.olean'): print(f'refusing: {O}/{b}.olean is a private copy of a library module'); sys.exit(2)
head0 = green_head()
if not head0: print('cannot read green commit'); sys.exit(2)
msha, nman = manifest()
stamp = f'green={head0} manifest={msha}'
for f in glob.glob(f'{O}/*.olean.part'): os.remove(f)
if a.reset:
    for f in glob.glob(f'{O}/*.olean') + glob.glob(f'{O}/*.ilean') + glob.glob(f'{O}/REPLAY_STAMP'): os.remove(f)
    print(f'reset: {O} emptied')
if glob.glob(f'{O}/*.olean'):
    old = open(f'{O}/REPLAY_STAMP').read().strip() if os.path.exists(f'{O}/REPLAY_STAMP') else 'none'
    if old != stamp:
        print(f'refusing to resume: {O} holds oleans built under a different state\n  stamp in dir : {old}\n  current      : {stamp}\n'
              f'  -> run again with --reset'); sys.exit(4)
else:
    open(f'{O}/REPLAY_STAMP', 'w').write(stamp + '\n')
log(f'START pools light={L} heavy={H} classes={len(CLASSES)} top={TOP} mem_heavy={a.mem_heavy_gb} {stamp}')
os.makedirs(f'{R}/tmp_out', exist_ok=True)


def up_to_date(t):
    ol = f'{O}/{t.name}.olean'
    return os.path.exists(ol) and os.path.getmtime(ol) > os.path.getmtime(t.path)


for t in tasks.values():
    if up_to_date(t): t.state = 'done'; t.skipped = True
total = len(tasks); T0 = time.time(); stop = None; heavy_launched = 0; holding = {'light': False, 'heavy': False}
min_free = free_gb(); last_mem = 0; last_status = 0; lean_done = 0.0; last_head = time.time()


def launch(t):
    global heavy_launched
    lr = LIGHT_LEANRUN if t.pool == 'light' else HEAVY_LEANRUN
    env = dict(os.environ, LEANRUN_OWNER='L1_1-replay', LEANRUN_TIMEOUT='540')
    if t.pool == 'light': env['LEAN_SLOTS'] = str(L)
    else:
        env.pop('LEAN_SLOTS', None)
        if a.heavy_slots: env['LEAN_SLOTS'] = str(a.heavy_slots)
    t.out = f'{R}/tmp_out/{t.name}.out'
    t.proc = subprocess.Popen([a.bash, lr, t.path, O, '--', '-o', f'{O}/{t.name}.olean.part'], env=env,
                              stdout=open(t.out, 'w'), stderr=subprocess.STDOUT)
    t.state = 'running'; t.t0 = time.time()
    if t.pool != 'light': heavy_launched += 1


def finish(t):
    global stop, lean_done
    rc = t.proc.returncode; txt = open(t.out, encoding='utf-8', errors='replace').read()
    m = re.findall(r'leanrun: exit=\S+ (elapsed=\S+) (peak_mem=\S+)', txt)
    el, pm = m[-1] if m else ('elapsed=?', 'peak_mem=?')
    part = f'{O}/{t.name}.olean.part'
    if rc == 75 and t.retries < a.max_retry75:
        t.retries += 1; t.state = 'pending'
        log(f'RETRY75 {t.name} (no leanrun slot within its wait limit; retry {t.retries}/{a.max_retry75})'); return
    if rc == 0 and os.path.exists(part):
        os.replace(part, f'{O}/{t.name}.olean'); t.state = 'done'
        try: lean_done += float(el.split('=')[1].rstrip('s'))
        except ValueError: pass
    else:
        if os.path.exists(part): os.remove(part)
        t.state = 'failed'; stop = stop or 1
        open(f'{R}/errors_{t.name}.txt', 'w', encoding='utf-8').write(
            '\n'.join(l for l in txt.splitlines() if 'declaration uses' not in l))
    with open(LOG, 'a', encoding='utf-8') as f:
        f.write(f'{time.strftime("%H:%M:%S")} {t.name} exit={rc} {el} {pm}\n')


def ready(t): return t.state == 'pending' and all(tasks[d].state == 'done' for d in t.deps if d in tasks)


def summary(c):
    last = {}
    for line in open(LOG, encoding='utf-8'):
        p = line.split()
        if len(p) >= 5 and p[1].startswith(f'R{c}_') and p[2].startswith('exit='): last[p[1]] = p
    out = []
    def agg(ps):
        t = sum(float(x[3].split('=')[1].rstrip('s')) for x in ps if x[3] != 'elapsed=?')
        mx = max((int(x[4].split('=')[1].rstrip('MB')) for x in ps if x[4][9:-2].isdigit()), default=0)
        return t, mx
    t, mx = agg(list(last.values()))
    out.append(f'class R{c}_: files compiled {len(last)}, failed {sum(1 for x in last.values() if x[2] != "exit=0")}, '
               f'total leanrun time {t:.0f} s, max peak {mx} MB')
    for k in ('Data', 'Pts', 'Cells', 'Leaves', 'Assembly', 'Cert'):
        ps = [x for n, x in last.items() if n.startswith(f'R{c}_{k}')]
        if ps:
            t, mx = agg(ps); out.append(f'  {k:<9} files {len(ps):3d}  time {t:7.1f} s  mean {t/len(ps):6.1f} s  max peak {mx:5d} MB')
    open(f'{R}/{c}/SUMMARY.txt', 'w').write('\n'.join(out) + '\n')


def status(force=False):
    global last_status
    if not force and time.time() - last_status < 60: return
    last_status = time.time()
    done = sum(1 for t in tasks.values() if t.state == 'done'); run = [t for t in tasks.values() if t.state == 'running']
    left = {p: sum(COST[t.kind] for t in tasks.values() if t.pool == p and t.state != 'done') for p in ('light', 'heavy', 'top')}
    eta = left['light'] / L + left['heavy'] / H + left['top']
    open(STATUS, 'w').write(
        f'{time.strftime("%Y-%m-%d %H:%M:%S")}  files done {done}/{total}  running {len(run)} '
        f'(light {sum(1 for t in run if t.pool == "light")}, heavy {sum(1 for t in run if t.pool != "light")})  '
        f'lean-seconds done this run {lean_done:.0f}  elapsed {time.time()-T0:.0f} s  '
        f'estimated time left {eta/60:.0f} min  free memory {free_gb():.1f} GB (min {min_free:.1f})  '
        f'failures {sum(1 for t in tasks.values() if t.state == "failed")}  stop={stop}\n')


done_classes = set()
while True:
    for t in [t for t in tasks.values() if t.state == 'running']:
        if t.proc.poll() is not None: finish(t)
    fg = free_gb(); min_free = min(min_free, fg)
    if time.time() - last_mem >= 5:
        last_mem = time.time()
        rr = [t for t in tasks.values() if t.state == 'running']
        with open(f'{R}/tmp_out/memtrace.txt', 'a') as mf:
            mf.write(f"{time.strftime('%H:%M:%S')} free={fg:.2f}GB light={sum(1 for t in rr if t.pool == 'light')} "
                     f"heavy={sum(1 for t in rr if t.pool != 'light')}\n")
    if a.abort_below_gb and fg < a.abort_below_gb and not stop:
        log(f'MEM abort: free {fg:.2f} GB < {a.abort_below_gb} GB'); stop = 6
    if time.time() - last_head > 60:
        last_head = time.time()
        if green_head() != head0 and not stop: log('green commit changed during the run'); stop = 5
    if a.budget and time.time() - T0 > a.budget and not stop: stop = 3
    for c in CLASSES:
        if c not in done_classes and all(t.state == 'done' for t in tasks.values() if t.cls == c):
            done_classes.add(c)
            if any(not getattr(t, 'skipped', False) for t in tasks.values() if t.cls == c): summary(c)
    running = [t for t in tasks.values() if t.state == 'running']
    if stop:
        if not running: break
    else:
        light_left = any(t.pool == 'light' and t.state != 'done' for t in tasks.values())
        top_running = any(t.pool == 'top' for t in running)
        # phase 1: light pool
        nl = sum(1 for t in running if t.pool == 'light')
        for t in [t for t in tasks.values() if t.pool == 'light' and ready(t)]:
            if nl >= L: break
            if free_gb() < a.mem_light_gb:
                if not holding['light']: log(f'HOLD light: free {free_gb():.2f} GB < {a.mem_light_gb} GB'); holding['light'] = True
                break
            holding['light'] = False; launch(t); nl += 1
        # heavy pool: ReplayCommon at any time; the rest only after every light file (phase 2)
        nh = sum(1 for t in running if t.pool == 'heavy')
        if not top_running:
            for t in [t for t in tasks.values() if t.pool == 'heavy' and ready(t)]:
                if nh >= H: break
                if light_left and t.kind != 'Common': break
                if a.max_heavy_files and heavy_launched >= a.max_heavy_files: break
                fg = free_gb()
                if fg < a.mem_heavy_gb:
                    if not holding['heavy']: log(f'HOLD heavy: free {fg:.2f} GB < {a.mem_heavy_gb} GB'); holding['heavy'] = True
                    break
                holding['heavy'] = False; launch(t); nh += 1
        # phase 3: each top file alone
        if not running and not [t for t in tasks.values() if t.state == 'running']:
            for t in [t for t in tasks.values() if t.pool == 'top' and ready(t)]:
                if free_gb() < a.mem_heavy_gb + 2:
                    if not holding['heavy']: log(f'HOLD top: free {free_gb():.2f} GB'); holding['heavy'] = True
                    break
                launch(t); break
        running = [t for t in tasks.values() if t.state == 'running']
        pending = [t for t in tasks.values() if t.state == 'pending']
        if not running and not pending: break
        if not running and a.max_heavy_files and heavy_launched >= a.max_heavy_files: break
    status()
    time.sleep(2)

status(force=True)
code = stop or 0
log(f'STOP code={code} after {time.time()-T0:.0f} s; min free memory {min_free:.2f} GB')
print(f'replay (pools): stopped with code {code} after {time.time()-T0:.0f} s; min free memory {min_free:.2f} GB; '
      f'status {STATUS}; log {LOG}')
sys.exit(code)
