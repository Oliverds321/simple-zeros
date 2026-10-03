"""(Oct 2026) Run manifest of the sharded CertS8 route (mkinit.sh, round_lb3.sh, run_lb3_loop.sh call this script).

Why: a checksum over the shard files that happen to be in a run folder cannot show that no shard was lost. The
manifest runs/<TAG>/run_manifest.json is written at the initialisation and updated by every round. It records
  * the objective of the run (bnb_lb3.objective_identity: K, alpha or the window coefficients, mu, the claim, the
    sha256 of the weights and window files, the options that fix the checkpoint arguments) and its sha256;
  * the root: init.log (sha256; a fresh start that stopped at its box budget) and init.ckpt (sha256, boxes,
    processed), and the sha256 of the sorted rows of its stack;
  * every round R: N, the shards r<R>_<i>.ckpt as written (name, sha256, boxes), their parents and the sha256 of the
    sorted rows of the union (the partition check of shard_ckpt.py); when the round is closed, the outcome of every
    shard: certified (its log, sha256) or left (its log, and the checkpoint it left: sha256, boxes). The parents of
    round R+1 are exactly the checkpoints left in round R, or, after a change of N, all shards of round R.
A copy of the manifest as it stood when round R opened is kept as runs/<TAG>/manifests/round_<R>.json (lineage).
While a round runs, start/r<R>_<i>.ckpt keeps each shard as written, so that an interrupted round restarts from it.

Commands (cwd = this folder; CERTIFIER ARGS = the arguments of bnb_lb3.py: alpha K muinv claim --weights W EXTRA):
  init    TAG N -- CERTIFIER ARGS        mkinit.sh: shard runs/TAG/init.ckpt into N shards, write the manifest
  begin   TAG R N -- CERTIFIER ARGS      round_lb3.sh: check the run and round R, keep start copies of its shards
  end     TAG R N RC_0 ... RC_N-1 -- ... round_lb3.sh: check the outcome of round R (RC_i = exit status of shard i),
                                         close it and re-shard the boxes left into round R+1
  prepare TAG R N -- CERTIFIER ARGS      run_lb3_loop.sh: check the run; for a new N re-shard the complete round R
  verify  TAG -- CERTIFIER ARGS          check a complete run again and print its receipt
  status  TAG                            print the state of the run (current round, N, state)
Before any round or re-shard: the objective of the command must be the run's (a missing or changed weights or window
file is refused); the run must be neither failed nor complete; R must be its current round; every shard of the round
must be present with its recorded sha256 (or restorable from its start copy after an interruption); every log and
text manifest of the closed rounds must be present unchanged; and no other shard-like file (*.ckpt*, *.manifest.txt,
names like r3_1.log or x3_0.ckpt) may be in the folder. Every check is an explicit test: they hold under python -O.
Output: the last line on standard output is the answer (OK, ROUND R, ALLOK, CONTINUE R, COMPLETE) or, on a refusal,
"s8_manifest.py: <reason>" (also on standard error), with exit status 4 (refused), 2 (a shard ended 'ok': False:
the run has failed for good), 3 (a checkpoint gone without an 'ok': True line), 5 (a shard process failed) or 1 (the
re-shard failed). Interrupt signals are ignored while it runs (it takes seconds), so that an update is not cut short."""
import signal
for _sig in ('SIGINT', 'SIGTERM', 'SIGHUP'):
    if hasattr(signal, _sig):
        signal.signal(getattr(signal, _sig), signal.SIG_IGN)
import sys, os, re, json, time, shutil, hashlib, traceback

FORMAT = 'CertS8 run manifest v1'
MAN = 'run_manifest.json'
SHARDLIKE = re.compile(r'\.ckpt($|\.)|\.manifest\.txt$|^[A-Za-z]*\d+_\d+')


class Refused(Exception):
    def __init__(self, msg, code=4):
        super().__init__(msg)
        self.code = code


def now():
    return time.strftime('%Y-%m-%d %H:%M:%S')


def sha256_file(fn):
    h = hashlib.sha256()
    with open(fn, 'rb') as f:
        for blk in iter(lambda: f.read(1 << 20), b''):
            h.update(blk)
    return h.hexdigest()


def canon_sha(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def write_json(fn, obj):
    tmp = fn + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(obj, f, indent=1)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, fn)


def append_log(D, data):
    """append str lines or raw bytes to DRIVER.log"""
    with open(os.path.join(D, 'DRIVER.log'), 'ab') as f:
        f.write(data if isinstance(data, bytes) else ''.join(l + '\n' for l in data).encode())


def pos_int(s, what, zero=False):
    if not (isinstance(s, str) and s.isascii() and s.isdigit()) or (s != '0' and s.startswith('0')):
        raise Refused(f"{what} must be a {'nonnegative' if zero else 'positive'} integer (got {s!r})")
    v = int(s)
    if v == 0 and not zero:
        raise Refused(f"{what} must be a positive integer (got {s!r})")
    return v


def rundir(tag):
    if not re.fullmatch(r'[A-Za-z0-9._-]+', tag) or tag in ('.', '..'):
        raise Refused(f"invalid run name {tag!r}")
    return os.path.join('runs', tag)


def expected_identity(cargs):
    """the objective of the certifier arguments, computed by bnb_lb3.py itself (same parser, same function)"""
    import bnb_lb3
    try:
        a = bnb_lb3.build_parser().parse_args(cargs)
    except SystemExit:
        raise Refused(f"cannot parse the certifier arguments {cargs}")
    try:
        return bnb_lb3.objective_identity(a)
    except SystemExit as e:
        raise Refused(f"objective of this command: {e.code}")


def load_ckpt(path):
    import shard_ckpt
    try:
        return shard_ckpt.load_checkpoint(path)
    except shard_ckpt.ShardError as e:
        raise Refused(str(e))


def nboxes(ck):
    return sum(len(C) for C, H in ck['stack'])


def check_ckpt(man, path, ck):
    if ck.get('identity') != man['objective_sha256']:
        raise Refused(f"{path} was written for objective sha256={ck.get('identity')}, not the run's "
                      f"{man['objective_sha256']}")
    if repr(ck['args']) != man['args']:
        raise Refused(f"{path} has checkpoint arguments {ck['args']!r}, the run {man['args']}")


def rec(D, name):
    p = os.path.join(D, name)
    if not os.path.isfile(p):
        raise Refused(f"{p} is missing")
    return dict(name=name, sha256=sha256_file(p))


def need(D, r, what):
    p = os.path.join(D, r['name'])
    if not os.path.isfile(p):
        raise Refused(f"{what} {p} is missing")
    if sha256_file(p) != r['sha256']:
        raise Refused(f"{what} {p} has changed (sha256 differs from the run manifest)")


def load_manifest(D):
    fn = os.path.join(D, MAN)
    if not os.path.isfile(fn):
        raise Refused(f"{D} has no run manifest ({MAN}): only a run initialised by mkinit.sh can be continued, "
                      f"and only with its recorded shards")
    try:
        with open(fn) as f:
            man = json.load(f)
    except (OSError, ValueError) as e:
        raise Refused(f"run manifest {fn} is unreadable ({e})")
    if not isinstance(man, dict) or man.get('format') != FORMAT:
        raise Refused(f"{fn} is not a run manifest of this format ({FORMAT})")
    return man


SAME_AT_OPEN = ('round', 'N', 'from', 'parents', 'rows', 'rows_sha256', 'shards', 'text_manifest')


def check_lineage(man, D):
    """the recorded chain from the initial checkpoint to the current round; every evidence file present unchanged"""
    try:
        if canon_sha(man['objective']) != man['objective_sha256']:
            raise Refused("run manifest: the objective does not match its sha256")
        root, rounds = man['root'], man['rounds']
        need(D, root['init_log'], 'initial log')
        if not rounds:
            raise Refused("run manifest: no round")
        for k, rd in enumerate(rounds):
            N, shards, last = rd['N'], rd['shards'], k == len(rounds) - 1
            if rd['round'] != k or not isinstance(N, int) or N < 1 or len(shards) != N:
                raise Refused(f"run manifest: round {k} malformed")
            if [s['name'] for s in shards] != [f"r{k}_{i}.ckpt" for i in range(N)]:
                raise Refused(f"run manifest: round {k}: shard names malformed")
            if sum(s['boxes'] for s in shards) != rd['rows'] or sum(p['boxes'] for p in rd['parents']) != rd['rows']:
                raise Refused(f"run manifest: round {k}: box counts of shards and parents differ")
            need(D, rd['text_manifest'], f"text manifest of round {k}")
            if k == 0:
                if rd['from'] != 'init' or rd['parents'] != [root['init_ckpt']] or rd['rows_sha256'] != root['rows_sha256']:
                    raise Refused("run manifest: round 0 is not the shard set of the initial checkpoint")
            else:
                prev = rounds[k - 1]
                if prev['state'] == 'done':
                    exp, frm = [o['ckpt'] for o in prev['outcome'] if o['result'] == 'left'], 'round'
                elif prev['state'] == 'resharded':
                    exp, frm = prev['shards'], 'reshard'
                else:
                    raise Refused(f"run manifest: round {k - 1} is not closed")
                if rd['from'] != frm or rd['parents'] != exp:
                    raise Refused(f"run manifest: the parents of round {k} are not what round {k - 1} left")
            if rd['state'] == 'done':
                out = rd['outcome']
                if [o['shard'] for o in out] != list(range(N)):
                    raise Refused(f"run manifest: round {k}: outcome of every shard expected")
                for o in out:
                    need(D, o['log'], f"log of shard {o['shard']} of round {k}")
                    if o['log']['name'] != f"r{k}_{o['shard']}.log":
                        raise Refused(f"run manifest: round {k}: log name malformed")
                    if o['result'] == 'left':
                        if o['ckpt']['name'] != shards[o['shard']]['name']:
                            raise Refused(f"run manifest: round {k}: checkpoint name malformed")
                    elif o['result'] != 'certified':
                        raise Refused(f"run manifest: round {k}: unknown outcome {o['result']!r}")
                if last and any(o['result'] != 'certified' for o in out):
                    raise Refused(f"run manifest: round {k} left boxes but no round follows it")
            elif rd['state'] == 'resharded':
                if last:
                    raise Refused(f"run manifest: round {k} was re-sharded but no round follows it")
            elif not (last and rd['state'] in ('open', 'running')):
                raise Refused(f"run manifest: round {k} has state {rd['state']!r}")
        st, lastr = man['status'], rounds[-1]
        if not ((st == 'complete' and lastr['state'] == 'done') or (st == 'open' and lastr['state'] in ('open', 'running'))
                or (st == 'failed' and lastr['state'] == 'running')):
            raise Refused(f"run manifest: status {st!r} does not fit round {lastr['round']} ({lastr['state']})")
        for k, rd in enumerate(rounds):          # the lineage: the manifest as it stood when each round opened
            fn = os.path.join(D, 'manifests', f"round_{k}.json")
            try:
                with open(fn) as f:
                    snap = json.load(f)
            except (OSError, ValueError):
                raise Refused(f"lineage copy {fn} is missing or unreadable")
            if (snap.get('objective_sha256') != man['objective_sha256'] or snap.get('root') != root
                    or len(snap.get('rounds', [])) != k + 1 or snap['rounds'][:k] != rounds[:k]
                    or any(snap['rounds'][k].get(x) != rd[x] for x in SAME_AT_OPEN)):
                raise Refused(f"lineage copy {fn} does not agree with the run manifest")
    except (KeyError, TypeError, IndexError, AttributeError) as e:
        raise Refused(f"run manifest of {D} is malformed ({type(e).__name__}: {e})")


def scan(man, D):
    """refuse any shard-like file that the manifest does not explain (missing ones are refused by the callers)"""
    rounds, st = man['rounds'], man['status']
    cur = rounds[-1]
    R, N = cur['round'], cur['N']
    running = st == 'open' and cur['state'] == 'running'
    allowed = {MAN, MAN + '.tmp', 'DRIVER.log', 'init.log'}
    allowed |= {rd['text_manifest']['name'] for rd in rounds}
    for rd in rounds:
        if rd['state'] == 'done':
            allowed |= {o['log']['name'] for o in rd['outcome']}
    if st == 'open':
        allowed |= {s['name'] for s in cur['shards']}
    if running:
        allowed |= {f"r{R}_{i}{x}" for i in range(N) for x in ('.log', '.ckpt.tmp', '.ckpt.restore')}
    extra = []
    for name in sorted(os.listdir(D)):
        p = os.path.join(D, name)
        if os.path.isdir(p):
            if name == 'attempts':
                continue
            if name == 'manifests':
                ok = {f"round_{k}.json" for k in range(len(rounds))} | {f"round_{k}.json.tmp" for k in range(len(rounds))}
            elif name == 'start':
                ok = ({f"r{R}_{i}.ckpt" for i in range(N)} | {f"r{R}_{i}.ckpt.tmp" for i in range(N)}) if running else set()
            else:
                if SHARDLIKE.search(name):
                    extra.append(name + '/')
                continue
            extra += [f"{name}/{x}" for x in sorted(os.listdir(p)) if x not in ok]
            continue
        if name in allowed:
            continue
        if name == man['root']['init_ckpt']['name'] and sha256_file(p) == man['root']['init_ckpt']['sha256']:
            continue                              # mkinit.sh removes it right after the initialisation
        if SHARDLIKE.search(name):
            extra.append(name)
    if extra:
        more = f" and {len(extra) - 8} more" if len(extra) > 8 else ''
        raise Refused(f"{D} holds files that the run manifest does not explain: {', '.join(extra[:8])}{more} "
                      f"(extra, duplicate or stale shard files are refused)")


def checked_run(tag, cargs, open_only=True):
    D = rundir(tag)
    if not os.path.isdir(D):
        raise Refused(f"no run directory {D}")
    man = load_manifest(D)
    ident, isha = expected_identity(cargs)
    if isha != man.get('objective_sha256'):
        old = man.get('objective') or {}
        diff = [f"{k}: run {old.get(k)!r}, command {ident.get(k)!r}" for k in sorted(set(old) | set(ident))
                if old.get(k) != ident.get(k)]
        raise Refused(f"the objective of this command is not the run's ({'; '.join(diff) or 'manifest objective'})")
    if open_only and man.get('status') == 'failed':
        raise Refused(f"this run has failed ({man.get('failure')}); a failed run cannot be continued: start a new run "
                      f"with mkinit.sh and a new TAG")
    if open_only and man.get('status') == 'complete':
        raise Refused(f"this run is complete (ALL SHARDS OK); nothing to run. Check it again with: "
                      f"python s8_manifest.py verify {tag} -- <certifier arguments>")
    check_lineage(man, D)
    scan(man, D)
    return D, man, isha


def current(man, R, N):
    cur = man['rounds'][-1]
    if R != cur['round']:
        raise Refused(f"round {R} is not the current round of this run, which is round {cur['round']} "
                      f"(N={cur['N']}, {cur['state']})")
    if N is not None and N != cur['N']:
        raise Refused(f"round {R} has N={cur['N']} shards, not {N} (only run_lb3_loop.sh changes N, between rounds)")
    return cur


def shard_files_ok(D, cur):
    """every shard of the current round present with its recorded sha256"""
    for s in cur['shards']:
        p = os.path.join(D, s['name'])
        if not os.path.isfile(p):
            raise Refused(f"shard {p} is missing")
        if sha256_file(p) != s['sha256']:
            raise Refused(f"shard {p} is not the checkpoint recorded for it (sha256 differs: changed or corrupt)")


def recover(D, man, cur):
    """after an interrupted attempt of the current round: restore every shard from its start copy (or keep it if it
    is unchanged), and move the logs of that attempt to attempts/"""
    R, k = cur['round'], cur['attempts']
    for s in cur['shards']:
        p, q = os.path.join(D, s['name']), os.path.join(D, 'start', s['name'])
        if os.path.isfile(p) and sha256_file(p) == s['sha256']:
            continue
        if not (os.path.isfile(q) and sha256_file(q) == s['sha256']):
            raise Refused(f"shard {p}: neither it nor its start copy is the checkpoint recorded for it")
        tmp = p + '.restore'
        shutil.copyfile(q, tmp)
        if sha256_file(tmp) != s['sha256']:
            os.remove(tmp)
            raise Refused(f"shard {p}: copy of the start copy differs")
        os.replace(tmp, p)
    moved = []
    adir = os.path.join(D, 'attempts', f"r{R}_attempt{k}")
    while os.path.exists(adir):
        adir += '_'
    for i in range(cur['N']):
        for name in (f"r{R}_{i}.log", f"r{R}_{i}.ckpt.tmp", f"r{R}_{i}.ckpt.restore"):
            p = os.path.join(D, name)
            if os.path.isfile(p):
                if not name.endswith('.log'):       # partial copies: no evidence
                    os.remove(p)
                    continue
                os.makedirs(adir, exist_ok=True)
                os.replace(p, os.path.join(adir, name))
                moved.append(name)
    append_log(D, [f"{now()} round {R}: attempt {k} did not finish; the {cur['N']} shards restart from their start "
                   f"copies (sha256 as recorded)" + (f"; its {len(moved)} logs are kept in {adir}" if moved else "")])


def snapshot(D, man, k):
    os.makedirs(os.path.join(D, 'manifests'), exist_ok=True)
    write_json(os.path.join(D, 'manifests', f"round_{k}.json"), man)


def reshard(D, man, tag, newR, N, parents):
    """shard_ckpt.shard on the parent checkpoints (names in D, with their recorded sha256 and boxes); returns
    the new round's record and the lines for DRIVER.log. Every written shard is read back and checked."""
    import shard_ckpt
    paths = [f"runs/{tag}/{p['name']}" for p in parents]
    try:
        lines, info = shard_ckpt.shard(N, f"runs/{tag}/r{newR}", paths)
    except shard_ckpt.ShardError as e:
        raise Refused(f"re-shard into round {newR}: {e}", 1)
    if [(q['sha256'], q['boxes']) for q in info['parents']] != [(p['sha256'], p['boxes']) for p in parents]:
        raise Refused(f"re-shard into round {newR}: a parent changed while it was read", 1)
    if info['identity'] != man['objective_sha256'] or repr(info['args']) != man['args']:
        raise Refused(f"re-shard into round {newR}: parents of another objective", 1)
    shards, stacks = [], []
    for fn, nb in zip(info['files'], info['boxes']):
        ck, h = load_ckpt(fn)
        check_ckpt(man, fn, ck)
        if nboxes(ck) != nb:
            raise Refused(f"re-shard into round {newR}: {fn} does not hold {nb} boxes as written", 1)
        shards.append(dict(name=os.path.basename(fn), sha256=h, boxes=nb))
        stacks += ck['stack']
    if shard_ckpt.digest(stacks) != (info['rows_sha256'], info['rows']):
        raise Refused(f"re-shard into round {newR}: the shards read back do not partition the parents", 1)
    rd = dict(round=newR, N=N, parents=parents, rows=info['rows'], rows_sha256=info['rows_sha256'], shards=shards,
              text_manifest=rec(D, os.path.basename(info['text_manifest'])), state='open', attempts=0, outcome=None)
    rd['from'] = 'init' if newR == 0 else None
    return rd, lines


def remove_round_files(D, cur):
    for s in cur['shards']:
        for p in (os.path.join(D, s['name']), os.path.join(D, 'start', s['name'])):
            if os.path.isfile(p):
                os.remove(p)


def receipt(D, man):
    rounds, root = man['rounds'], man['root']
    ncert = sum(1 for rd in rounds if rd['state'] == 'done' for o in rd['outcome'] if o['result'] == 'certified')
    o = man['objective']
    return (f"{now()} objective sha256={man['objective_sha256']} (K={o['K']} alpha={o['alpha']} mu=1/{o['muinv']} "
            f"claim={o['claim']} weights sha256={o['weights_sha256']} window sha256={o['window_sha256']}): coverage "
            f"accounted for from the initial checkpoint ({root['init_ckpt']['boxes']} boxes left after "
            f"{root['processed']} processed) through round {rounds[-1]['round']}: {ncert} shard runs ended 'ok': True, "
            f"every other shard was carried into the next round; {MAN} sha256={sha256_file(os.path.join(D, MAN))}")


# ------------------------------------------------------------------------------------------------- commands
def cmd_init(pos, cargs):
    if len(pos) != 2:
        raise Refused("usage: init TAG N -- CERTIFIER ARGS")
    tag, N = pos[0], pos_int(pos[1], 'N')
    D = rundir(tag)
    if os.path.exists(os.path.join(D, MAN)):
        raise Refused(f"{D} has a run manifest already: initialise a new run under a new TAG")
    ident, isha = expected_identity(cargs)
    logp = os.path.join(D, 'init.log')
    try:
        with open(logp, errors='replace') as f:
            lines = f.read().splitlines()
    except OSError as e:
        raise Refused(f"cannot read {logp}: {e}")
    body = [l for l in lines if l.strip()]
    objs = [l for l in lines if l.startswith('objective: sha256=')]
    if not (body and body[0].startswith('bnb_interval: ') and len(objs) == 1
            and objs[0].startswith(f"objective: sha256={isha} ")):
        raise Refused(f"{logp} is not the log of a run of this objective")
    if any('resumed from' in l for l in lines) or not body[-1].startswith("{'ok': False, 'reason': 'budget'"):
        raise Refused(f"{logp}: the initial run must start afresh and stop at its box budget")
    ckp = os.path.join(D, 'init.ckpt')
    ck, h = load_ckpt(ckp)
    if ck.get('identity') != isha:
        raise Refused(f"{ckp} was written for objective sha256={ck.get('identity')}, not {isha}")
    import shard_ckpt
    d0 = shard_ckpt.digest(ck['stack'])
    man = dict(format=FORMAT, created=now(), objective=ident, objective_sha256=isha, args=repr(ck['args']),
               status='open', failure=None,
               root=dict(init_log=rec(D, 'init.log'), init_ckpt=dict(name='init.ckpt', sha256=h, boxes=nboxes(ck)),
                         processed=ck['stats'].get('processed'), rows_sha256=d0[0], rows=d0[1]),
               rounds=[])
    rd, lines = reshard(D, man, tag, 0, N, [man['root']['init_ckpt']])
    if rd['rows_sha256'] != d0[0]:
        raise Refused("the shards of round 0 do not partition the initial stack", 1)
    man['rounds'].append(rd)
    write_json(os.path.join(D, MAN), man)
    snapshot(D, man, 0)
    print('\n'.join(lines), flush=True)
    return None


def cmd_begin(pos, cargs):
    if len(pos) != 3:
        raise Refused("usage: begin TAG R N -- CERTIFIER ARGS")
    R, N = pos_int(pos[1], 'R', zero=True), pos_int(pos[2], 'N')
    D, man, isha = checked_run(pos[0], cargs)
    cur = current(man, R, N)
    if cur['state'] == 'running':
        recover(D, man, cur)
    else:
        shard_files_ok(D, cur)
    cur['state'], cur['attempts'] = 'running', cur['attempts'] + 1
    write_json(os.path.join(D, MAN), man)
    os.makedirs(os.path.join(D, 'start'), exist_ok=True)
    for s in cur['shards']:
        p, q = os.path.join(D, s['name']), os.path.join(D, 'start', s['name'])
        if os.path.isfile(q) and sha256_file(q) == s['sha256']:
            continue
        shutil.copyfile(p, q + '.tmp')
        if sha256_file(q + '.tmp') != s['sha256']:
            raise Refused(f"start copy of {p} differs from it")
        os.replace(q + '.tmp', q)
    return 'OK'


def result_ok(lines):
    """True if the final result record of a bnb_lb3.py log is {'ok': True, ...}. The record is the last line that starts
    with '{'; Python prints it over several lines when its numpy arrays wrap, so it may be followed by continuation
    lines, which start with white space. Any other line after it (a traceback, other output) makes the result not ok."""
    body = [l for l in lines if l.strip()]
    starts = [k for k, l in enumerate(body) if l.startswith('{')]
    if not starts:
        return False
    k = starts[-1]
    return body[k].startswith("{'ok': True,") and all(l[:1].isspace() for l in body[k + 1:])


def classify(D, tag, R, i, rc, s, man):
    """outcome of shard i of round R: (kind, detail); kind in certified, left, false, gone, failed"""
    lp, cp = os.path.join(D, f"r{R}_{i}.log"), os.path.join(D, s['name'])
    shown = f"runs/{tag}/r{R}_{i}.log"
    if not os.path.isfile(lp):
        return 'failed', f"{shown}: missing (exit status {rc})"
    with open(lp, 'rb') as f:
        raw = f.read()
    text = raw.decode('utf-8', 'replace')
    lines = [l.rstrip('\r') for l in text.split('\n')]
    if "'ok': False" in text:
        return 'false', f"{shown}: " + '\n'.join(l for l in lines if "'ok'" in l)[:400]
    has_ok = result_ok(lines)     # (3 Oct 2026, evening) the result may span lines: the first full S8 run with this tool
    objs = [l for l in lines if l.startswith('objective: sha256=')]
    obj_ok = len(objs) == 1 and objs[0].startswith(f"objective: sha256={man['objective_sha256']} ")
    res_ok = f"  resumed checkpoint sha256={s['sha256']}" in lines
    if not os.path.isfile(cp):
        if not has_ok:
            return 'gone', f"{shown}: checkpoint gone but no ok line"
        if rc == 0 and obj_ok and res_ok:
            return 'certified', dict(raw=raw)
        return 'failed', (f"{shown}: 'ok': True but exit status {rc}" if rc != 0 else
                          f"{shown}: 'ok': True but the log does not name this objective and this shard's sha256")
    if rc == 124 and not has_ok and (obj_ok or not objs):
        ck, h = load_ckpt(cp)
        check_ckpt(man, cp, ck)
        return 'left', dict(raw=raw, ckpt=dict(name=s['name'], sha256=h, boxes=nboxes(ck)))
    return 'failed', f"runs/{tag}/{s['name']} (exit status {rc})"


def cmd_end(pos, cargs):
    if len(pos) < 3:
        raise Refused("usage: end TAG R N RC_0 ... RC_N-1 -- CERTIFIER ARGS")
    tag = pos[0]
    R, N = pos_int(pos[1], 'R', zero=True), pos_int(pos[2], 'N')
    rcs = [pos_int(x, 'exit status', zero=True) for x in pos[3:]]
    D, man, isha = checked_run(tag, cargs)
    cur = current(man, R, N)
    if cur['state'] != 'running' or len(rcs) != N:
        raise Refused(f"round {R} was not begun, or not {N} exit statuses given", 5)
    for s in cur['shards']:
        q = os.path.join(D, 'start', s['name'])
        if not (os.path.isfile(q) and sha256_file(q) == s['sha256']):
            raise Refused(f"start copy {q} is missing or changed", 5)
    res = [classify(D, tag, R, i, rc, s, man) for i, (rc, s) in enumerate(zip(rcs, cur['shards']))]
    false = [d for k, d in res if k == 'false']
    if false:
        man['status'], man['failure'] = 'failed', f"round {R}: {false[0]}"
        write_json(os.path.join(D, MAN), man)
        raise Refused(false[0], 2)
    for kind, code in (('gone', 3), ('failed', 5)):
        bad = [d for k, d in res if k == kind]
        if bad:
            raise Refused(('shard process failed: ' if kind == 'failed' else '') + '; '.join(bad)[:600], code)
    outcome, logb = [], b''
    order = sorted(range(N), key=lambda i: f"r{R}_{i}.log")
    for i in order:        # the lines round_lb3.sh wrote before: grep "'ok': True" log | head -c 600; echo
        if res[i][0] == 'certified':
            parts = res[i][1]['raw'].split(b'\n')
            if res[i][1]['raw'].endswith(b'\n'):
                parts = parts[:-1]
            logb += b''.join(p + b'\n' for p in parts if b"'ok': True" in p)[:600] + b'\n'
    nok = sum(1 for k, d in res if k == 'certified')
    left = [i for i in order if res[i][0] == 'left']
    logb += f"{now()} round {R} done: {nok} shards ok, {len(left)} left\n".encode()
    for i in left:         # tail -n 1 log | cut -c1-200
        parts = res[i][1]['raw'].split(b'\n')
        if res[i][1]['raw'].endswith(b'\n'):
            parts = parts[:-1]
        if parts:
            logb += parts[-1][:200] + b'\n'
    for i, (kind, d) in enumerate(res):
        o = dict(shard=i, result=kind, log=dict(name=f"r{R}_{i}.log", sha256=hashlib.sha256(d['raw']).hexdigest()))
        if kind == 'left':
            o['ckpt'] = d['ckpt']
        outcome.append(o)
    cur['state'], cur['outcome'] = 'done', outcome
    if not left:
        man['status'] = 'complete'
        check_lineage(man, D)                 # the whole chain, before the run is recorded as complete
        write_json(os.path.join(D, MAN), man)
        append_log(D, logb)
        remove_round_files(D, cur)
        append_log(D, [receipt(D, man)])
        return 'ALLOK'
    rd, lines = reshard(D, man, tag, R + 1, N, [outcome[i]['ckpt'] for i in range(N) if res[i][0] == 'left'])
    rd['from'] = 'round'
    man['rounds'].append(rd)
    write_json(os.path.join(D, MAN), man)
    snapshot(D, man, R + 1)
    append_log(D, logb)
    append_log(D, lines)
    remove_round_files(D, cur)
    return f"CONTINUE {R + 1}"


def cmd_prepare(pos, cargs):
    if len(pos) != 3:
        raise Refused("usage: prepare TAG R N -- CERTIFIER ARGS")
    tag = pos[0]
    R, N = pos_int(pos[1], 'R', zero=True), pos_int(pos[2], 'N')
    D, man, isha = checked_run(tag, cargs)
    cur = current(man, R, None)
    if N == cur['N']:
        if cur['state'] == 'open':
            shard_files_ok(D, cur)
        return f"ROUND {R}"
    # an intentional change of N: only from the complete round R, which becomes the parent set of round R+1
    if cur['state'] == 'running':
        recover(D, man, cur)
    shard_files_ok(D, cur)
    note = (f"{now()} round {R}: N changes from {cur['N']} to {N}: all {cur['N']} shards of round {R} are present "
            f"with their recorded sha256 and are re-sharded into round {R + 1}")
    rd, lines = reshard(D, man, tag, R + 1, N, cur['shards'])
    rd['from'] = 'reshard'
    cur['state'], cur['outcome'] = 'resharded', None
    man['rounds'].append(rd)
    write_json(os.path.join(D, MAN), man)
    snapshot(D, man, R + 1)
    append_log(D, [note] + lines)
    remove_round_files(D, cur)
    return f"ROUND {R + 1}"


def cmd_verify(pos, cargs):
    if len(pos) != 1:
        raise Refused("usage: verify TAG -- CERTIFIER ARGS")
    D, man, isha = checked_run(pos[0], cargs, open_only=False)
    if man['status'] != 'complete':
        raise Refused(f"the run is not complete (status {man['status']}: {man.get('failure') or 'rounds remain'})")
    print(receipt(D, man)[20:], flush=True)
    return 'COMPLETE'


def cmd_status(pos, cargs):
    if len(pos) != 1:
        raise Refused("usage: status TAG")
    D = rundir(pos[0])
    man = load_manifest(D)
    cur = man['rounds'][-1]
    return (f"{D}: status {man['status']}; current round {cur['round']} (N={cur['N']}, {cur['state']}, "
            f"{cur['attempts']} attempts); objective sha256={man['objective_sha256']}"
            + (f"; failure: {man['failure']}" if man.get('failure') else ''))


COMMANDS = dict(init=cmd_init, begin=cmd_begin, end=cmd_end, prepare=cmd_prepare, verify=cmd_verify,
                status=cmd_status)


def main(argv):
    if '--' in argv:
        i = argv.index('--')
        head, cargs = argv[:i], argv[i + 1:]
    else:
        head, cargs = argv, None
    try:
        if not head or head[0] not in COMMANDS:
            raise Refused(f"usage: python s8_manifest.py {'|'.join(COMMANDS)} ... (see the doc-string)")
        if (cargs is None) != (head[0] == 'status'):
            raise Refused(f"{head[0]}: the certifier arguments follow '--'" if cargs is None else "status takes no '--'")
        out = COMMANDS[head[0]](head[1:], cargs)
    except Refused as e:
        msg = f"s8_manifest.py: {e}"
        print(msg, flush=True)
        print(msg, file=sys.stderr, flush=True)
        sys.exit(e.code)
    except Exception as e:
        traceback.print_exc()
        msg = f"s8_manifest.py: internal error ({type(e).__name__}: {e})"
        print(msg, flush=True)
        sys.exit(4)
    if out is not None:
        print(out, flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
