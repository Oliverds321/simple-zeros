"""d8_19: independent exact re-derivation of the all-marks inputs and of Sigma, D and the (OL_L) robustness
conditions from a claims json + the xpat pattern files + certificate log(s).  Independent of d8_9's pexact2.py /
verify_inputs.py: H and k are derived here symbolically (sympy) from their DEFINITIONS and evaluated in Arb through
an exact sympy->arb tree converter (rationals stay exact); log parsing by own regex (finditer, handles concatenated lines).

Definitions used (X2 / d6_6 / d8_3 / d8_8):
  v(s) = cos(alpha s)/Z on [-1/2,1/2], Z = int cos(alpha s) ds;  k(t) = int v(s) cos(2 pi t s) ds  (Gram kernel);
  what(x) = (v*v)(x) = int v(s) v(s+x) ds;   H = 2 - [what(0) + 2 int_0^1 x what(x) dx];
  Sigma >= p = (H + a2/2 - nu)/(1 - a1 + a2/2);  D >= (1 + H + a2 - a1 - nu)/(2 - 2a1 + a2)  (= (1+p)/2);
  (OL_L): c = 2 - 2a1 > (2 beta0 + 4 beta* - 2)^2, 2 beta0 + 4 beta* = 3.206363885243057 (d8_5 t2 / d8_8, exact binary64);
          mu(k*) - max(a1,a2) >= 0, mu(k) = min(2k^2-2a1, 4k^2-2a2, (1/2+sqrt(1/4+2k^2))^2-1-a1-a2), k* = k(3/4);
  d8_8 sec 2.3 bookkeeping table: 2 - 2a2 + 2a1 > 0, 2 - 3a2/2 > 0, 1 + a1 - 2a2 > 0.
Usage: python d819_exact.py K muinv claims.json xpatdir certlog [certlog ...]"""
import sys, json, itertools, re
from fractions import Fraction as Fr
import sympy as sp
from flint import arb, fmpq, ctx

ctx.prec = 256
K, muinv, cjf, xd = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
logs = sys.argv[5:]
ALPHA = Fr(8, 5)

# ---------------- symbolic H and k from the definitions ----------------
s, x, t, a = sp.symbols('s x t a', positive=True)
Zs = sp.integrate(sp.cos(a * s), (s, -sp.Rational(1, 2), sp.Rational(1, 2)))
what_unnorm = sp.integrate(sp.cos(a * s) * sp.cos(a * (s + x)), (s, -sp.Rational(1, 2), sp.Rational(1, 2) - x))  # 0<=x<=1
what0_unnorm = sp.integrate(sp.cos(a * s) ** 2, (s, -sp.Rational(1, 2), sp.Rational(1, 2)))
Rint = sp.integrate(sp.expand(x * what_unnorm), (x, 0, 1))
Hexpr = 2 - (what0_unnorm + 2 * Rint) / Zs ** 2
kexpr = sp.integrate(sp.cos(a * s) * sp.cos(2 * sp.pi * t * s), (s, -sp.Rational(1, 2), sp.Rational(1, 2))) / Zs


def to_arb(e, env):
    """exact sympy -> arb evaluation (rationals exact, pi/sin/cos/sqrt rigorous)."""
    if e.is_Symbol:
        return env[e]
    if e.is_Integer or e.is_Rational:
        return arb(fmpq(int(e.p), int(e.q)))
    if e == sp.pi:
        return arb.pi()
    if e.is_Add:
        r = arb(0)
        for u in e.args: r += to_arb(u, env)
        return r
    if e.is_Mul:
        r = arb(1)
        for u in e.args: r *= to_arb(u, env)
        return r
    if e.is_Pow:
        b, ex = e.args
        if ex.is_Integer:
            bb = to_arb(b, env); n = int(ex)
            return bb ** n if n >= 0 else 1 / (bb ** (-n))
        if ex == sp.Rational(1, 2):
            return to_arb(b, env).sqrt()
        if ex == -sp.Rational(1, 2):
            return 1 / to_arb(b, env).sqrt()
    if isinstance(e, sp.sin):
        return to_arb(e.args[0], env).sin()
    if isinstance(e, sp.cos):
        return to_arb(e.args[0], env).cos()
    if isinstance(e, sp.Piecewise):   # k: generic branch (a != 2 pi t) is the one we need; check it
        for ex, cond in e.args:
            if cond == True or cond.subs({a: sp.Rational(8, 5), t: sp.Rational(3, 4)}) == True:
                return to_arb(ex, env)
    raise ValueError(f"unsupported node {e!r}")


A = arb(fmpq(ALPHA.numerator, ALPHA.denominator))
H = to_arb(sp.simplify(Hexpr), {a: A})
kst = to_arb(kexpr.subs(t, sp.Rational(3, 4)), {a: A})
k0 = to_arb(sp.integrate(sp.cos(a * s), (s, -sp.Rational(1, 2), sp.Rational(1, 2))) / Zs, {a: A})
# independent float cross-checks (mpmath quadrature from the definitions)
import mpmath as mp
mp.mp.dps = 40
al = mp.mpf(8) / 5
Zf = mp.quad(lambda u: mp.cos(al * u), [-0.5, 0.5])
wf = lambda xx: mp.quad(lambda u: mp.cos(al * u) * mp.cos(al * (u + xx)), [-0.5, 0.5 - xx]) / Zf ** 2
Hf = 2 - (wf(0) + 2 * mp.quad(lambda xx: xx * wf(xx), [0, 1]))
kf = mp.quad(lambda u: mp.cos(al * u) * mp.cos(2 * mp.pi * 0.75 * u), [-0.5, 0.5]) / Zf

# ---------------- exact certificate-structure checks ----------------
C = json.load(open(cjf))
b1 = [Fr(q) for q in C['b1']]; b2 = [Fr(q) for q in C['b2']]
a1, a2, nu = sum(b1), sum(b2), Fr(K - 1, muinv)
chk = {}
chk['a1 = sum b1 (json)'] = a1 == Fr(C['a1'])
chk['a2 = sum b2 (json)'] = a2 == Fr(C['a2'])
chk['nu = (K-1)/muinv (json)'] = nu == Fr(C['nu'])
chk['b1, b2 reversal-symmetric'] = b1 == b1[::-1] and b2 == b2[::-1]
chk['all b_i(j) > 0 (boundary-window bookkeeping, d8_10)'] = all(q > 0 for q in b1 + b2)
sp_ = [(i, s_) for s_ in range(1, K) for i in range(K - s_)]          # spans(K): s outer, i inner
need = {}
for m in itertools.product([1, 2], repeat=K):
    need[m] = sum(b1[i] if m[i] == 1 else b2[i] for i in range(K))
canon = sorted({min(m, m[::-1]) for m in need})
chk['claim(m) = claim(rev m) for all 2^K'] = all(need[m] == need[m[::-1]] for m in need)
chk['claims json = sum_i b_i(m_i) (canonical)'] = all(Fr(C['claims'][''.join(map(str, m))]) == need[m] for m in canon)
base0 = mu0 = None; okw = True
for m in canon:
    js = json.load(open(f"{xd}/xpat_K{K}_{''.join(map(str, m))}.json"))
    base = [Fr(q) for q in js['base_gam']]; gam = [Fr(q) for q in js['gam']]; mu = [Fr(q) for q in js['mu']]
    if base0 is None: base0, mu0 = base, mu
    okw &= (base == base0 and mu == mu0 and js['K'] == K and js['pattern'] == ''.join(map(str, m)))
    okw &= all(g == bq * m[i] * m[i + s_] for g, bq, (i, s_) in zip(gam, base, sp_))
chk['one base gamma & one mu in all pattern files; gam = base*m_i*m_{i+s}'] = okw
chk['base gamma >= 0'] = all(q >= 0 for q in base0)
chk['sum_i gamma_{s,i} = 2 for every s'] = all(sum(bq for bq, (i, s_) in zip(base0, sp_) if s_ == ss) == 2 for ss in range(1, K))
chk['base gamma reversal-symmetric'] = all(base0[sp_.index((K - 1 - i - s_, s_))] == base0[j] for j, (i, s_) in enumerate(sp_))
chk['mu > 0, symmetric, sum mu = nu'] = all(q > 0 for q in mu0) and mu0 == mu0[::-1] and sum(mu0) == nu

# ---------------- certificate logs ----------------
pat = re.compile(r"K(\d+) a=(\S+) mu=1/(\d+) ([12]+) (--sym )?\s*claim=(\S+) -> (?:X2 weight check passed: pattern ([12]+) )*\{'ok': (True|False)")
got = {}
for L in logs:
    txt = open(L).read()
    for mm in pat.finditer(txt):
        if int(mm.group(1)) != K or int(mm.group(3)) != muinv or mm.group(2) != '1.6':
            continue
        name = mm.group(4)
        if mm.group(7) is not None and mm.group(7) != name:
            continue
        is_pal = name == name[::-1]
        if mm.group(5) and not is_pal:
            continue                                  # --sym on a non-palindrome would be invalid: ignore
        got.setdefault(name, []).append((Fr(mm.group(6)), mm.group(8) == 'True'))
missing = []
for m in canon:
    name = ''.join(map(str, m))
    if not any(ok and c >= need[m] for c, ok in got.get(name, [])):
        missing.append(name)
chk[f'certified ok at claim >= required, all {len(canon)} canonical patterns'] = not missing

# ---------------- constants ----------------
q = lambda f: arb(fmpq(f.numerator, f.denominator))
A1, A2, NU = q(a1), q(a2), q(nu)
p = (H + A2 / 2 - NU) / (1 - A1 + A2 / 2)
Dv = (1 + H + A2 - A1 - NU) / (2 - 2 * A1 + A2)
cc = 2 - 2 * A1
lam_c = 2 + cc.sqrt()
GB = q(Fr(3206363885243057, 10 ** 15))          # 2 beta0 + 4 beta*, exact decimal of the binary64 value (d8_5/d8_8)
k2 = kst ** 2
m11 = 2 * k2 - 2 * A1; m22 = 4 * k2 - 2 * A2; m12 = (arb(1) / 2 + (arb(1) / 4 + 2 * k2).sqrt()) ** 2 - 1 - A1 - A2
mx = max(a1, a2)
print(f"== K={K} mu=1/{muinv}  claims={cjf}")
print(f"H (sympy closed form -> Arb) = {H.str(25)} ; mpmath quad from definition = {mp.nstr(Hf, 25)}")
print(f"k(0) = {k0.str(10)} ; k(3/4) = {kst.str(22)} ; mpmath quad = {mp.nstr(kf, 22)}")
print(f"a1 = {a1} = {float(a1):.12f}; a2 = {a2} = {float(a2):.12f}; nu = {nu}; max(a1,a2) = {'a2' if a2 >= a1 else 'a1'}")
for kk, v in chk.items():
    print(f"  [{'OK' if v else 'FAIL'}] {kk}")
if missing:
    print(f"  NOT (yet) certified: {len(missing)}: {' '.join(missing)}")
print(f"p   = {p.str(22)}   lower {float(p.lower()):.12f}")
print(f"D   = {Dv.str(22)}   lower {float(Dv.lower()):.12f}")
print(f"D - (1+p)/2 = {(Dv - (1 + p) / 2).str(5)}")
print(f"c = 2-2a1 = {cc.str(15)} ; (2b0+4b*-2)^2 = {((GB - 2) ** 2).str(12)} ; c - that = {(cc - (GB - 2) ** 2).str(10)} ; "
      f"lambda_c = {lam_c.str(12)} ; lambda_c - 3.2063638852 = {(lam_c - GB).str(10)} ; eps'_T threshold = {(lam_c / GB - 1).str(8)}")
print(f"2k*^2 = {(2 * k2).str(12)} ; 2a1 + max(a1,a2) = {float(2 * a1 + mx):.8f} ; (1,1)-margin surplus 2k*^2 - 2a1 - max = {(m11 - q(mx)).str(10)}")
print(f"margins: (1,1) {m11.str(10)}  (2,2) {m22.str(10)}  (1,2) {m12.str(10)} ; per-chain surplus min(...) - max(a1,a2) = "
      f"{(min(m11, m22, m12, key=lambda z: float(z.mid())) - q(mx)).str(10)}")
print(f"sec 2.3 table: 2-2a2+2a1 = {float(2 - 2 * a2 + 2 * a1):.8f}; 2-3a2/2 = {float(2 - Fr(3, 2) * a2):.8f}; 1+a1-2a2 = {float(1 + a1 - 2 * a2):.8f}")
okall = all(chk.values()) and bool(cc > (GB - 2) ** 2) and bool(min(m11, m22, m12, key=lambda z: float(z.mid())) - q(mx) > 0)
print(f"ALL STRUCTURE + ROBUSTNESS CHECKS PASS: {okall}")
sys.exit(0 if okall else 1)   # (Oct 2026) exit status 0 only if every check passes
