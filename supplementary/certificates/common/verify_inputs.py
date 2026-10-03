"""d8_9: exact cross-file audit of an all-marks certificate's inputs (Fractions only).
Checks: (i) every K-pattern m in {1,2}^K is covered by a certified file xpat_K{K}_{min(m, rev m)}.json;
(ii) all pattern files share ONE base_gam and ONE mu (pattern-independent Lemma D' weights); gam = base_gam * m_i m_{i+s};
(iii) base_gam >= 0, sum over each span length s = 2, reversal-symmetric; mu > 0, symmetric, sum = (K-1)/muinv = nu;
(iv) claim(m) == sum_i b_i(m_i) exactly, with b1, b2 from the claims json; a1 = sum b1, a2 = sum b2, nu as stated;
(v) the certificate log has ok=True for every canonical pattern with exactly that claim.
(Oct 2026) A log entry counts only if its alpha equals the claims file's alpha (exactly, as a rational), the pattern of
its weight check (if printed) is its own pattern, and --sym appears only for a palindromic pattern; the claims file's
own K and muinv, if given, must be those of the command line.
Usage: python verify_inputs.py K muinv claims.json xpatdir certlog [certlog2 ...]"""
import sys, json, itertools, re
if not __debug__:   # (Oct 2026) the checks below are assert statements: refuse to run with them disabled
    sys.exit("verify_inputs.py: run without -O / PYTHONOPTIMIZE (its checks are assert statements)")
from fractions import Fraction as Fr
K, muinv, cj, xd = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
logs = sys.argv[5:]
sp = [(i, s) for s in range(1, K) for i in range(K - s)]
C = json.load(open(cj))
b1 = [Fr(x) for x in C['b1']]; b2 = [Fr(x) for x in C['b2']]
a1, a2, nu = Fr(C['a1']), Fr(C['a2']), Fr(C['nu'])
assert sum(b1) == a1 and sum(b2) == a2 and nu == Fr(K - 1, muinv)
# (Oct 2026) the claims file names its alpha (and K, muinv): log entries are checked against them, not ignored
if 'alpha' not in C:
    sys.exit(f"FAIL: {cj} names no alpha, so the logs cannot be checked against it")
ALPHA = Fr(str(C['alpha']))
if C.get('K', K) != K or C.get('muinv', muinv) != muinv:
    sys.exit(f"FAIL: {cj} is for K={C.get('K')} mu=1/{C.get('muinv')}, not K={K} mu=1/{muinv}")
def same_alpha(s):
    try:
        return Fr(s) == ALPHA
    except (ValueError, ZeroDivisionError):
        return False
canon = sorted({min(p, p[::-1]) for p in itertools.product([1, 2], repeat=K)})
base0 = mu0 = None
okset = {}
nign = 0
for L in logs:
    for line in open(L):
        m = re.match(r"K(\d+) a=(\S+) mu=1/(\d+) (\d+) (--sym )?\s*claim=(\S+) -> "
                     r"(?:X2 weight check passed: pattern (\d+) )?.*?'ok': (True|False)", line)
        if m and int(m.group(1)) == K and int(m.group(3)) == muinv:
            if (not same_alpha(m.group(2)) or (m.group(7) is not None and m.group(7) != m.group(4))
                    or (m.group(5) and m.group(4) != m.group(4)[::-1])):
                nign += 1
                continue
            okset.setdefault(m.group(4), []).append((Fr(m.group(6)), m.group(8) == 'True'))
nok = 0
for p in canon:
    name = ''.join(map(str, p))
    js = json.load(open(f"{xd}/xpat_K{K}_{name}.json"))
    base = [Fr(x) for x in js['base_gam']]; gam = [Fr(x) for x in js['gam']]; mu = [Fr(x) for x in js['mu']]
    if base0 is None: base0, mu0 = base, mu
    assert base == base0 and mu == mu0, f"pattern-dependent base weights in {name}"
    assert js['pattern'] == name and js['K'] == K
    assert all(g == bq * p[i] * p[i + s] for g, bq, (i, s) in zip(gam, base, sp))
    claim = sum(b1[i] if p[i] == 1 else b2[i] for i in range(K))
    assert Fr(C['claims'][name]) == claim, name
    res = okset.get(name, [])
    if any(c >= claim and ok for c, ok in res): nok += 1   # F >= c >= claim (monotone)
    else: print("NOT CERTIFIED:", name, res)
assert all(x >= 0 for x in base0) and all(x > 0 for x in mu0)
for s_ in range(1, K): assert sum(b for b, (i, s) in zip(base0, sp) if s == s_) == 2
assert base0 == [base0[sp.index((K - s - 1 - i, s))] for (i, s) in sp] and mu0 == mu0[::-1] and sum(mu0) == nu
print(f"K={K} mu=1/{muinv}: {len(canon)} canonical patterns (cover all {2**K}); certified ok at a claim >= the required claim: {nok}/{len(canon)}")
print(f"a1 = {a1} = {float(a1):.12f}; a2 = {a2} = {float(a2):.12f}; nu = {nu}")
print("base_gam =", [str(x) for x in base0]); print("mu =", [str(x) for x in mu0])
if nign:   # (Oct 2026)
    print(f"ignored {nign} log entries for K={K} mu=1/{muinv}: alpha other than {C['alpha']}, a weight check of "
          f"another pattern, or --sym on a non-palindromic pattern")
if nok != len(canon):   # (Oct 2026) exit status 0 only if all canonical patterns are certified
    sys.exit(f"FAIL: {len(canon) - nok} of {len(canon)} canonical patterns are not certified in the given log(s)")
