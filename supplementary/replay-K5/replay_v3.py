"""Re-run v2 certificates through the FIXED python mirror (v3). Usage: python replay_v3.py P1,P2,..."""
import sys, json, time
if not __debug__:   # (Oct 2026) the mirror's interval code uses assert statements
    sys.exit('run without -O / PYTHONOPTIMIZE: the checks of this script are assert statements')
pats = sys.argv[1].split(','); sys.argv = ['x']
from fractions import Fraction as Fr
import proto_cert as pc, proto_v2 as v2
v2.setup(5)
nfail = 0   # (Oct 2026) failed leaves over all classes, for the exit status
for pat in pats:
    t0 = time.time()
    js = json.load(open(f'v2_K5_{pat}.json')); tree = js['tree']; root = [(Fr(a), Fr(b)) for a, b in js['root']]
    gam, mu, claim = pc.load(pat)
    pos = 0; stack = [([a for a, _ in root], [b for _, b in root])]
    fails = []; nleaf = 0; y3used = 0; outside = 0; ghout = 0
    while stack:
        lo, hi = stack.pop(); n = tree[pos]; pos += 1
        if n[0] == 'S':
            ax = n[1]; m = (lo[ax] + hi[ax])/2; hi1 = hi[:]; hi1[ax] = m; lo2 = lo[:]; lo2[ax] = m
            stack.append((lo2, hi)); stack.append((lo, hi1)); continue
        nleaf += 1
        if n[0] == 'M':
            gh = [Fr(v, 1 << 40) for v in n[1]]; y = n[2]
            if not all(a <= g <= b for a, g, b in zip(lo, gh, hi)): ghout += 1
            c = [(a + b)/2 for a, b in zip(lo, hi)]; h = [(b - a)/2 for a, b in zip(lo, hi)]
            for j, (i, s) in enumerate(v2.SP):
                if y[5*j + 3]:
                    y3used += 1
                    x0 = sum(c[i:i+s]); r = sum(h[i:i+s]); xh = sum(gh[i:i+s])
                    if not (x0 - r <= xh <= x0 + r): outside += 1
        if not v2.check_leaf_v2(gam, mu, claim, lo, hi, n): fails.append(pos - 1)
    print(f'{pat}: leaves {nleaf}, FAIL {len(fails)} {fails[:5]}; LP spans with y3>0: {y3used}, x̂ outside span interval: {outside}; '
          f'LP leaves with ĝ outside box: {ghout}; {time.time()-t0:.0f}s', flush=True)
    nfail += len(fails)
if nfail:
    sys.exit(f'FAIL: {nfail} failed leaves')
