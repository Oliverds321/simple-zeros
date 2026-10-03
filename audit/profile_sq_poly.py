"""Can v = p^2 (p an even polynomial on [-b,b]) reach B close to min B = 1.2787164332 at C = pi^4/18?
B(v) = int v^2 + iint W_C(t-s) v(t) v(s),  v normalised to int v = 1,  W_C(y) = |y| (|y|<=1), C|y| (|y|>1).
Exact Gauss-Legendre on the kink-split cells (polynomial integrands)."""
import math, os, sys, numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize

# `fb.py` / `payoff_cert_gen.py` are the authoring project's own numerical helpers and are NOT
# part of this repository, so this script cannot be re-run from a clean checkout.  It is kept as
# the record of how the shipped constants were produced; the recorded output is the `.out` file
# of the same name beside it.  To re-run, point the environment variables below at the
# directories holding those modules (defaults: `kit/repo_v1/scripts` and `phase2` alongside the
# repository, which is where they live in the authoring tree).
_HERE = os.path.dirname(os.path.abspath(__file__))
def _extdir(var, *parts):
    return os.environ.get(var, os.path.join(_HERE, os.pardir, os.pardir, *parts))
sys.path.insert(0, _extdir("ZETAQ_KIT_SCRIPTS", "kit", "repo_v1", "scripts"))
C = math.pi**4/18
NG = 48
xg, wg = leggauss(NG)

def gl(a, b):
    """nodes, weights on [a,b]"""
    m = 0.5*(b-a); c = 0.5*(a+b)
    return c + m*xg, m*wg

def make_v(coeffs, b):
    # p(t) = sum c_k (t/b)^(2k); v = p^2 (unnormalised)
    def p(t):
        x = (t/b)**2
        return np.polyval(coeffs[::-1], x)   # coeffs[0] + coeffs[1] x + ...
    return lambda t: p(t)**2

def B_of(coeffs, b):
    v = make_v(coeffs, b)
    # mass and int v^2
    t, w = gl(-b, b)
    vt = v(t)
    mass = np.dot(w, vt)
    Iv2 = np.dot(w, vt**2)
    # double integral
    def inner(tt):
        # breakpoints in s
        pts = [-b, b]
        for x in (tt-1, tt, tt+1):
            if -b < x < b: pts.append(x)
        pts.sort()
        tot = 0.0
        for i in range(len(pts)-1):
            s, ws = gl(pts[i], pts[i+1])
            d = np.abs(tt - s)
            W = np.where(d <= 1.0, d, C*d)
            tot += np.dot(ws, W*v(s))
        return tot
    outer_pts = [-b, -(1-b), (1-b), b] if (1-b) > 0 else [-b, b]
    Idd = 0.0
    for i in range(len(outer_pts)-1):
        t, w = gl(outer_pts[i], outer_pts[i+1])
        vals = np.array([inner(tt) for tt in t])
        Idd += np.dot(w, v(t)*vals)
    return Iv2/mass**2 + Idd/mass**2

# sanity: flat profile
import fb
for lam in (1.0, 1.2507321515):
    print("flat check lam=%.4f  ours=%.10f  fb=%.10f" % (lam, B_of(np.array([1.0]), lam/2), fb.flat_v_payoff(C, lam)))

def objective(x, m):
    b = x[-1]
    if not (0.5 < b < 0.999): return 10.0
    coeffs = np.concatenate(([1.0], x[:-1]))
    try:
        return B_of(coeffs, b)
    except Exception:
        return 10.0

best_x = None
results = []
for m in range(0, 9):
    if best_x is None:
        x0 = np.array([0.62])            # m=0: flat, only b
    else:
        x0 = np.concatenate((best_x[:-1], [0.0], [best_x[-1]]))  # add one coefficient
    res = minimize(objective, x0, args=(m,), method='Nelder-Mead',
                   options=dict(xatol=1e-10, fatol=1e-12, maxiter=20000, maxfev=40000))
    res2 = minimize(objective, res.x, args=(m,), method='BFGS', options=dict(gtol=1e-10))
    if res2.fun < res.fun: res = res2
    best_x = res.x
    Bm = res.fun
    coeffs = np.concatenate(([1.0], best_x[:-1])); b = best_x[-1]
    # edge value of p and v at t=b
    pb = np.polyval(coeffs[::-1], 1.0)
    print("deg p = %2d   B = %.10f   P = %.10f   lam = 2b = %.8f   p(b)/p(0) = %+.5f   gap to minB = %.2e"
          % (2*m, Bm, 2-Bm, 2*b, pb, Bm-1.2787164332))
    results.append((2*m, Bm, 2*b, coeffs.copy()))
print("\nshipped target: B <= 2 - 0.7212 = 1.2788 ;  min B = 1.2787164332")
# print the best polynomial
d, Bm, lam, coeffs = results[-1]
print("best p coefficients in x=(t/b)^2:", np.array2string(coeffs, precision=8))

# ---- independent cross-check: fine trapezoid grid on the best profile ----
def B_grid(coeffs, b, N=40001):
    v = make_v(coeffs, b)
    t = np.linspace(-b, b, N); h = t[1]-t[0]
    vt = v(t); w = np.full(N, h); w[0]=w[-1]=h/2
    mass = np.dot(w, vt)
    D = np.abs(t[:,None]-t[None,:]); W = np.where(D<=1, D, C*D)
    Idd = w @ (W @ (w*vt)) * 0 + (w*vt) @ W @ (w*vt)
    return (np.dot(w, vt**2) + Idd)/mass**2
for (d, Bm, lam, coeffs) in results:
    if d in (6, 8, 12):
        print("cross-check deg %d: GL B=%.10f  grid(N=8001) B=%.10f" % (d, Bm, B_grid(coeffs, lam/2, N=8001)))
