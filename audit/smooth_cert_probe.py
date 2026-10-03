"""Can the EXISTING exact-Q engine / Cert format certify a smooth profile v = p^2 (p even polynomial)?
Steps: optimise p (deg 6) numerically -> round to rationals -> v = p^2 / mass EXACTLY on the
two cells [0,1-b], [1-b,b] -> engine's payoff_parts (exact) -> B0q + Cbar*B1q vs 2 - Pcert ->
Bernstein nonnegativity check (with degree elevation if needed)."""
import os, sys, math, numpy as np

# `fb.py` / `payoff_cert_gen.py` are the authoring project's own numerical helpers and are NOT
# part of this repository, so this script cannot be re-run from a clean checkout.  It is kept as
# the record of how the shipped constants were produced; the recorded output is the `.out` file
# of the same name beside it.  To re-run, point the environment variables below at the
# directories holding those modules (defaults: `kit/repo_v1/scripts` and `phase2` alongside the
# repository, which is where they live in the authoring tree).
_HERE = os.path.dirname(os.path.abspath(__file__))
def _extdir(var, *parts):
    return os.environ.get(var, os.path.join(_HERE, os.pardir, os.pardir, *parts))
sys.path.insert(0, _extdir("ZETAQ_PHASE2", "phase2"))
sys.path.insert(0, _extdir("ZETAQ_KIT_SCRIPTS", "kit", "repo_v1", "scripts"))
from fractions import Fraction as Fr
import payoff_cert_gen as E
with open(os.path.join(_HERE, "profile_sq_poly.py")) as _f:   # B_of, make_v, C, gl
    exec(_f.read().split("# sanity: flat profile")[0])
from scipy.optimize import minimize

def obj(x):
    b = x[-1]
    if not (0.5 < b < 0.999): return 10.0
    return B_of(np.concatenate(([1.0], x[:-1])), b)
res = minimize(obj, np.array([-0.3, -0.5, 0.5, 0.62]), method='Nelder-Mead',
               options=dict(xatol=1e-10, fatol=1e-13, maxiter=30000, maxfev=60000))
coeffs = np.concatenate(([1.0], res.x[:-1])); bnum = res.x[-1]
print("float optimum deg-6: B=%.10f P=%.10f b=%.8f lam=%.8f coeffs(x=(t/b)^2)=%s" % (res.fun, 2-res.fun, bnum, 2*bnum, np.array2string(coeffs, precision=8)))

# ---- rationalise: b to den 10^4 (keep 1-b in (0,b)), coefficients of p in the MONOMIAL basis t^{2k} to den 10^6
den_b = 10**4; b = Fr(round(bnum*den_b), den_b)
den_c = 10**6
# p(t) = sum c_k (t/b)^{2k}  ->  monomial coefficients in t: c_k / b^{2k}
p_mono = {}   # power -> Fr
for k, ck in enumerate(coeffs):
    p_mono[2*k] = Fr(round(float(ck)*den_c), den_c) / b**(2*k)
deg_p = 2*(len(coeffs)-1)
# v = p^2 as a polynomial in t (ascending list)
def poly_from_dict(d):
    n = max(d)+1; out = [Fr(0)]*n
    for k, v in d.items(): out[k] = v
    return out
p_list = poly_from_dict(p_mono)
v_list = E.pmul(p_list, p_list)                      # ascending powers of t
# exact mass of v on [-b, b]: 2 * int_0^b
mass = 2*E.pdefint(v_list, Fr(0), b)
v_list = [c/mass for c in v_list]
assert 2*E.pdefint(v_list, Fr(0), b) == 1
# cells [0, 1-b], [1-b, b]; local coefficients in (t - x_i): shift
x1 = 1 - b
nodes = [Fr(0), x1, b]
def shift_to(poly, x0):
    # poly(t) expressed in u = t - x0: poly(u + x0)
    return E.pshift(poly, x0) if hasattr(E, 'pshift') else None
# E.pshift(p, a) semantics: check docstring
import inspect; print("pshift doc:", (E.pshift.__doc__ or "").strip()[:120])
cell0 = E.ptrim([c for c in v_list])                 # around x0 = 0: same
cell1 = E.ptrim(E.pshift(v_list, x1))               # p(u + x1)? verify numerically below
# verify pshift semantics: evaluate
t_test = x1 + Fr(1,7)
lhs = E.peval(v_list, t_test); rhs = E.peval(cell1, Fr(1,7))
print("pshift check: v(t)=%s  vs cell1(t-x1)=%s  ->  %s" % (float(lhs), float(rhs), lhs==rhs))
if lhs != rhs:
    # try the other convention
    cell1 = E.ptrim(E.pshift(v_list, -x1)); rhs = E.peval(cell1, Fr(1,7)); print("  other convention:", lhs==rhs)
coeff = [cell0, cell1]
deg = max(len(cell0), len(cell1)) - 1
print("v degree:", deg, " cells:", [float(x) for x in nodes])
vp = E.cert_pieces(nodes, coeff)
psi0, K0, K1, m, psi = E.payoff_parts(vp)
print("exact: mass=%s psi0=%.12f K0=%.12f K1=%.12f" % (m, float(psi0), float(K0), float(K1)))
B0q, B1q = psi0+K0, K1
Clo, Chi = E.C_bounds()[:2] if isinstance(E.C_bounds(), tuple) else (None, None)
cb = E.C_bounds()
print("C_bounds() ->", cb if not isinstance(cb, dict) else {k: float(v) for k, v in cb.items()})
# use a safe rational upper bound for pi^4/18 if C_bounds layout unknown
Cbar = max(cb[1], cb[2])   # engine's rational upper bounds for pi^4/18
assert float(Cbar) > math.pi**4/18
print('Cbar used = %.12f (pi^4/18 = %.12f)' % (float(Cbar), math.pi**4/18))
Bq = B0q + Cbar*B1q
print("B0q + Cbar*B1q = %.12f  (float B at true C: %.12f)  -> certified P >= %.10f" % (float(Bq), float(B0q) + (math.pi**4/18)*float(B1q), 2-float(Bq)))
for Pc in (Fr(7212,10000), Fr(72125,100000), Fr(721257,1000000)):
    print("  Pcert=%s : slack (2-Pcert) - (B0q+Cbar*B1q) = %+.3e  %s" % (Pc, float(2-Pc-Bq), "OK" if 2-Pc-Bq > 0 else "FAIL"))
# Bernstein nonnegativity at the native degree and with elevation
for n in (deg, deg+4, deg+8, deg+16, deg+32):
    ok, allb, worst = E.bernstein_check(nodes, coeff, n)
    print("Bernstein check at n=%d: ok=%s worst=%.3e" % (n, ok, float(worst)))
# is p > 0 on [0,b]?
ts = np.linspace(0, float(b), 2001); pv = np.array([float(E.peval(p_list, Fr(t))) for t in ts[::40]])
print("min p on [0,b] (sampled):", pv.min())
