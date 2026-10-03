"""L1_1 prototype: large-leaf certificate for ONE all-marks local inequality (K = 5, window cos(1.6 s)),
built by a float/LP builder and replayed in EXACT RATIONALS (proxy for a Lean-kernel replay).

Functional (Definition def:zeta-LIm, bnb_lb3_w.py):
    F_m(g) = sum_{spans (i,s)} gam_{i,s} m_i m_{i+s} w(g_i+...+g_{i+s-1}) + sum_i mu_i g_i,   w = k^2,
    k(x) = [sinc(pi x - a) + sinc(pi x + a)] / (2 sinc a),  a = 4/5,     g in [0, oo)^{K-1};  claim C(m).

Certificate = bisection tree (split = axis index, cut at the dyadic midpoint) whose leaves are
    CAP     mu . lo >= claim                                  (F >= mu.g since w >= 0)
    CVX     F convex on the box (Hessian lower bound P = sum gam_s p_s v_s v_s^T is PSD, p_s <= w'' on the span
            interval, PSD checked by an exact LDL^T with pivots >= 0) and F(ghat) + min_box grad F(ghat).(g - ghat)
            >= claim at a rational point ghat (the float minimiser, rounded to 2^-40): the tangent plane of a convex
            function is a global minorant on the box.
    LP      for each span three affine minorants of w valid on the span interval, all DETERMINED BY THE BOX
            (w >= 0; w >= inf_I w; tangent at the span centre with slope mid(w'(x0)) minus the curvature and slope
            corrections), plus the cap row mu.g <= claim; data = rational dual multipliers y >= 0, sum_j y_sj <= gam_s,
            lam >= 0; the checker forms the affine minorant and minimises it over the box exactly.
The checker recomputes every analytic enclosure itself from rational Taylor polynomials of sin/cos (as the kernel
would); the certificate carries only the tree shape, the leaf kinds, ghat (CVX) and the multipliers (LP).

Usage: python proto_cert.py PATTERN [claim_shift] [--maxnodes N]
"""
import sys, os, json, math, time
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog, minimize

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'certificates', 'CertAM5')
K = 5
SP = [(i, s) for s in range(1, K) for i in range(K - s)]
D = K - 1

def load(pattern):
    js = json.load(open(f'{HERE}/xpat_K{K}_{pattern}.json'))
    cj = json.load(open(f'{HERE}/claims_d15e6_a1.6_K5_mu500.json'))
    gam = [Fr(x) for x in js['gam']]
    mu = [Fr(x) for x in js['mu']]
    claim = Fr(cj['claims'][pattern])
    return gam, mu, claim

# ------------------------------------------------------------------------------------------------
# float kernel (builder only)
A = 0.8
def sincf(y):
    y = np.asarray(y, float)
    out = np.empty_like(y); sm = np.abs(y) < 1e-3; ys = y[sm]
    out[sm] = 1 - ys**2/6 + ys**4/120
    yl = y[~sm]; out[~sm] = np.sin(yl)/yl
    return out
def dsincf(y):
    y = np.asarray(y, float); out = np.empty_like(y); sm = np.abs(y) < 1e-3; ys = y[sm]
    out[sm] = -ys/3 + ys**3/30
    yl = y[~sm]; out[~sm] = (np.cos(yl) - np.sin(yl)/yl)/yl
    return out
def d2sincf(y):
    y = np.asarray(y, float); out = np.empty_like(y); sm = np.abs(y) < 1e-3; ys = y[sm]
    out[sm] = -1/3 + ys**2/10
    yl = y[~sm]; s = np.sin(yl)/yl; out[~sm] = -s - 2*(np.cos(yl) - s)/yl/yl
    return out
SA = math.sin(A)/A
def kf(x):
    x = np.asarray(x, float); y1 = math.pi*x - A; y2 = math.pi*x + A
    k0 = (sincf(y1) + sincf(y2))/(2*SA)
    k1 = math.pi*(dsincf(y1) + dsincf(y2))/(2*SA)
    k2 = math.pi**2*(d2sincf(y1) + d2sincf(y2))/(2*SA)
    return k0, k1, k2
M3F = math.pi**3/4

# ------------------------------------------------------------------------------------------------
# exact rational interval arithmetic (the "kernel" side)
SC = 1 << 80
def rdn(q): return Fr((q.numerator * SC) // q.denominator, SC)
def rup(q): return Fr(-((-q.numerator * SC) // q.denominator), SC)
class I:
    __slots__ = ('lo', 'hi')
    def __init__(s, lo, hi=None):
        s.lo = lo; s.hi = lo if hi is None else hi
    def __add__(s, o):
        if not isinstance(o, I): o = I(Fr(o))
        return I(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__
    def __neg__(s): return I(-s.hi, -s.lo)
    def __sub__(s, o):
        if not isinstance(o, I): o = I(Fr(o))
        return I(s.lo - o.hi, s.hi - o.lo)
    def __rsub__(s, o): return (-s) + o
    def __mul__(s, o):
        if not isinstance(o, I):
            o = Fr(o)
            a, b = s.lo*o, s.hi*o
            return I(rdn(min(a, b)), rup(max(a, b)))
        p = (s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi)
        return I(rdn(min(p)), rup(max(p)))
    __rmul__ = __mul__
    def sq(s):
        if s.lo >= 0: return I(rdn(s.lo*s.lo), rup(s.hi*s.hi))
        if s.hi <= 0: return I(rdn(s.hi*s.hi), rup(s.lo*s.lo))
        return I(Fr(0), rup(max(s.lo*s.lo, s.hi*s.hi)))
    def inv(s):
        assert s.lo > 0 or s.hi < 0
        return I(rdn(1/s.hi), rup(1/s.lo))
    def absmax(s): return max(abs(s.lo), abs(s.hi))
    def widen(s, e): return I(s.lo - e, s.hi + e)

PI = I(Fr(314159265358979323846, 10**20), Fr(314159265358979323847, 10**20))   # Real.pi_gt_d20 / pi_lt_d20
FACT = [math.factorial(n) for n in range(60)]

def sin_taylor(t, N=13):            # t interval, |t| <= 2; degree 2N-1, remainder |t|^(2N+1)/(2N+1)!
    t2 = t.sq(); acc = I(Fr((-1)**(N-1), FACT[2*N-1]))
    for j in range(N-2, -1, -1):
        acc = acc*t2 + Fr((-1)**j, FACT[2*j+1])
    m = t.absmax(); return (acc*t).widen(rup(Fr(m)**(2*N+1)/FACT[2*N+1]))
def cos_taylor(t, N=13):            # degree 2N-2, remainder |t|^(2N)/(2N)!
    t2 = t.sq(); acc = I(Fr((-1)**(N-1), FACT[2*N-2]))
    for j in range(N-2, -1, -1):
        acc = acc*t2 + Fr((-1)**j, FACT[2*j])
    m = t.absmax(); return acc.widen(rup(Fr(m)**(2*N)/FACT[2*N]))

AQ = Fr(4, 5)
SINA = sin_taylor(I(AQ)); COSA = cos_taylor(I(AQ))
SINCA = SINA * Fr(5, 4)
INV2SA = (SINCA*2).inv()

def sincos_pi(x):                   # x rational: sin(pi x), cos(pi x) by reduction x = n + f, |f| <= 1/2
    n = math.floor(x + Fr(1, 2)); f = x - n
    t = PI*f; s = sin_taylor(t); c = cos_taylor(t)
    if n % 2: s, c = -s, -c
    return s, c

def sinc_derivs(y, sy, cy):          # y interval; sy, cy enclosures of sin y, cos y
    if y.absmax() <= Fr(1, 2):       # alternating Taylor series, remainder = first omitted term
        N = 12; m = y.absmax(); y2 = y.sq()
        s0 = I(Fr(0)); s1 = I(Fr(0)); s2 = I(Fr(0))
        for j in range(N-1, -1, -1):
            s0 = s0*y2 + Fr((-1)**j, FACT[2*j+1])
        for j in range(N-1, 0, -1):
            s1 = s1*y2 + Fr((-1)**j*2*j, FACT[2*j+1])
            s2 = s2*y2 + Fr((-1)**j*2*j*(2*j-1), FACT[2*j+1])
        s1 = s1*y                    # sum_j (-1)^j 2j y^(2j-1)/(2j+1)!
        e0 = rup(Fr(m)**(2*N)/FACT[2*N+1]); e1 = rup(2*N*Fr(m)**(2*N-1)/FACT[2*N+1])
        e2 = rup(2*N*(2*N-1)*Fr(m)**(2*N-2)/FACT[2*N+1])
        return s0.widen(e0), s1.widen(e1), s2.widen(e2)
    iy = y.inv()
    s0 = sy*iy; s1 = (cy - s0)*iy; s2 = -s0 - (s1*iy)*2
    return s0, s1, s2

KCACHE = {}
def kexact(x):                       # enclosures of k, k', k'' at rational x
    r = KCACHE.get(x)
    if r is not None: return r
    sp, cp = sincos_pi(x)
    px = PI*x
    res = [I(Fr(0)), I(Fr(0)), I(Fr(0))]
    for sg in (-1, 1):
        y = px + (sg*AQ)
        sy = sp*COSA + (cp*SINA)*sg      # sin(pi x + sg a)
        cy = cp*COSA - (sp*SINA)*sg
        d = sinc_derivs(y, sy, cy)
        res = [res[0] + d[0], res[1] + d[1], res[2] + d[2]]
    k0 = res[0]*INV2SA; k1 = (res[1]*INV2SA)*PI; k2 = ((res[2]*INV2SA)*PI)*PI
    KCACHE[x] = (k0, k1, k2)
    return k0, k1, k2

M3Q = rup(PI.hi**3/4)                # |k'''| <= pi^3/4 (v even, >= 0, nonincreasing on [0,1/2])

def span_model(x0, r):
    """Taylor model on [x0-r, x0+r]: returns (k0,k1,k2 at x0), inf-bound of w'' on the interval, enclosure of w."""
    k0, k1, k2 = kexact(x0)
    T = I(-r, r); T2 = I(Fr(0), r*r)
    kI = (k0 + k1*T + (k2*T2)*Fr(1, 2)).widen(rup(M3Q*r**3/6))
    k1I = (k1 + k2*T).widen(rup(M3Q*r*r/2))
    k2I = k2.widen(rup(M3Q*r))
    wpp = (k1I.sq() + kI*k2I)*2
    return (k0, k1, k2), wpp.lo, kI.sq()

# ------------------------------------------------------------------------------------------------
class Problem:
    def __init__(s, pattern, claim_shift=Fr(0)):
        s.pattern = pattern
        s.gam, s.mu, s.claim0 = load(pattern)
        s.claim = s.claim0 + claim_shift
        s.act = [j for j, g in enumerate(s.gam) if g > 0]
        s.V = np.zeros((len(SP), D))
        for j, (i, sl) in enumerate(SP): s.V[j, i:i+sl] = 1
        s.gamf = np.array([float(g) for g in s.gam]); s.muf = np.array([float(m) for m in s.mu])
        s.claimf = float(s.claim)
        # root box: g_i <= claim/mu_i (outside, mu.g > claim), rounded up to a multiple of 1/64
        s.root = [(Fr(0), Fr(math.ceil(s.claim/m*64), 64)) for m in s.mu]

    # ---------------- float side
    def Ff(s, g):
        x = s.V @ g; k0, k1, _ = kf(x)
        return float(s.gamf @ (k0*k0) + s.muf @ g), s.V.T @ (s.gamf*2*k0*k1) + s.muf

    def spanf(s, c, h):
        x0 = s.V @ c; r = s.V @ h
        k0, k1, k2 = kf(x0)
        T = r
        kmax = np.abs(k0) + np.abs(k1)*T + 0.5*np.abs(k2)*T*T + M3F*T**3/6
        klo_abs = np.maximum(0, np.abs(k0) - np.abs(k1)*T - 0.5*np.abs(k2)*T*T - M3F*T**3/6)
        k1a = np.abs(k1) + np.abs(k2)*T + M3F*T*T/2
        k1lo = np.maximum(0, np.abs(k1) - np.abs(k2)*T - M3F*T*T/2)
        k2a = np.abs(k2) + M3F*T
        # w'' >= 2 k1lo^2 - 2 |k| |k''|  (float mirror of the exact Taylor model, slightly cruder)
        kk2lo = np.minimum.reduce([(k0 + s1*k1*T + 0.5*k2*T*T*t2)*(k2 + s2*M3F*T)
                                   for s1 in (-1, 1) for s2 in (-1, 1) for t2 in (0, 1)])
        p = 2*k1lo**2 + 2*kk2lo - 2*(M3F*T**3/6)*k2a - 1e-9
        return x0, r, k0, k1, p, klo_abs**2

    def try_cvx(s, lo, hi):
        c = (lo + hi)/2; h = (hi - lo)/2
        x0, r, k0, k1, p, _ = s.spanf(c, h)
        P = (s.V.T*(s.gamf*p)) @ s.V
        if np.linalg.eigvalsh(P).min() < 1e-10*max(1, np.abs(P).max()): return None
        best = None
        for st in (c, lo + 0.25*(hi-lo), lo + 0.75*(hi-lo)):
            res = minimize(lambda g: s.Ff(g), st, jac=True, method='L-BFGS-B', bounds=list(zip(lo, hi)),
                           options=dict(ftol=1e-15, gtol=1e-13, maxiter=200))
            if best is None or res.fun < best.fun: best = res
        gh = np.clip(np.round(best.x*2**40)/2**40, lo, hi)
        Fv, gr = s.Ff(gh)
        lb = Fv + np.minimum(gr*(lo - gh), gr*(hi - gh)).sum()
        if lb > s.claimf + 1e-9:
            return ('C', [int(round(v*2**40)) for v in gh])
        return None

    def try_lp(s, lo, hi):
        c = (lo + hi)/2; h = (hi - lo)/2
        x0, r, k0, k1, p, wlo = s.spanf(c, h)
        # lines per active span: (slope, intercept at x0)
        rows = []   # each: (span j, slope, value at x0)
        for j in s.act:
            w0 = k0[j]**2; w1 = 2*k0[j]*k1[j]
            rows.append((j, 0.0, 0.0 + 0.0))                                    # w >= 0 (as a line: 0 + 0*(x-x0))
            rows.append((j, 0.0, wlo[j]))                                        # w >= inf w
            rows.append((j, w1, w0 - 0.5*max(0.0, -p[j])*r[j]**2 - 1e-12))       # tangent with correction
        # variables: g (D), e (len(act)); minimise sum gam e + mu g
        na = len(s.act); idx = {j: t for t, j in enumerate(s.act)}
        cobj = np.concatenate([s.muf, s.gamf[s.act]])
        Aub = []; bub = []
        for (j, sl, val) in rows:          # sl*(v.g - x0) + val <= e   ->  sl v.g - e <= sl x0 - val
            a = np.zeros(D + na); a[:D] = sl*s.V[j]; a[D + idx[j]] = -1
            Aub.append(a); bub.append(sl*x0[j] - val)
        a = np.zeros(D + na); a[:D] = s.muf; Aub.append(a); bub.append(s.claimf)   # cap row
        bounds = [(lo[i], hi[i]) for i in range(D)] + [(None, None)]*na
        res = linprog(cobj, A_ub=np.array(Aub), b_ub=np.array(bub), bounds=bounds, method='highs')
        if res.status == 2:   # infeasible: box inside {mu.g > claim} (cannot happen after CAP) -> treat as CAP
            return None
        if res.status != 0 or res.fun < s.claimf + 1e-9: return None
        y = -res.ineqlin.marginals      # >= 0
        yq = [max(0, int(math.floor(v*2**30))) for v in y]
        return ('L', yq)

    # ---------------- exact side
    def check_leaf(s, lo, hi, leaf):
        """exact rational check; lo, hi: lists of Fractions."""
        kind = leaf[0]
        mu, gam, claim = s.mu, s.gam, s.claim
        if kind == 'A':
            return sum(m*l for m, l in zip(mu, lo)) >= claim
        c = [(a + b)/2 for a, b in zip(lo, hi)]; h = [(b - a)/2 for a, b in zip(lo, hi)]
        spans = {}
        for j in s.act:
            i, sl = SP[j]
            spans[j] = span_model(sum(c[i:i+sl]), sum(h[i:i+sl]))
        if kind == 'C':
            gh = [Fr(v, 1 << 40) for v in leaf[1]]
            if not all(a <= v <= b for a, v, b in zip(lo, gh, hi)): return False
            # PSD of P = sum gam_s p_s v_s v_s^T
            ps = {j: spans[j][1] for j in s.act}
            if any(ps[j] < 0 for j in s.act):
                P = [[Fr(0)]*D for _ in range(D)]
                for j in s.act:
                    i, sl = SP[j]; q = gam[j]*ps[j]
                    for a in range(i, i+sl):
                        for b in range(i, i+sl): P[a][b] += q
                if not ldl_psd(P): return False
            F = I(sum(m*v for m, v in zip(mu, gh)))
            grad = [I(m) for m in mu]
            for j in s.act:
                i, sl = SP[j]
                k0, k1, _ = kexact(sum(gh[i:i+sl]))
                F = F + k0.sq()*gam[j]
                wd = (k0*k1)*(2*gam[j])
                for a in range(i, i+sl): grad[a] = grad[a] + wd
            lb = F.lo
            for a in range(D):
                d = I(lo[a] - gh[a], hi[a] - gh[a])
                lb += (grad[a]*d).lo
            return lb >= claim
        if kind == 'L':
            y = [Fr(v, 1 << 30) for v in leaf[1]]
            lam = y[-1]
            rho = [m*(1 + lam) for m in mu]; kap = -lam*claim
            t = 0
            for j in s.act:
                (k0, k1, k2), p, wI = spans[j]
                i, sl = SP[j]; x0 = sum(c[i:i+sl]); r = sum(h[i:i+sl])
                y0, y1, y2 = y[t], y[t+1], y[t+2]; t += 3
                if y0 + y1 + y2 > gam[j]: return False
                # line 1: constant inf w
                kap += y1*max(wI.lo, Fr(0))
                # line 2: tangent at x0 with slope sig = mid(w'(x0)) and corrections
                w0 = k0.sq(); w1 = (k0*k1)*2
                sig = rdn((w1.lo + w1.hi)/2)
                icp = w0.lo - max(abs(w1.lo - sig), abs(w1.hi - sig))*r - max(Fr(0), -p)*r*r/2
                kap += y2*(icp - sig*x0)
                for a in range(i, i+sl): rho[a] += y2*sig
            lb = kap + sum(min(rr*a, rr*b) for rr, a, b in zip(rho, lo, hi))
            return lb >= claim
        return False

def ldl_psd(P):
    n = len(P); A = [row[:] for row in P]
    for k in range(n):
        piv = A[k][k]
        if piv < 0: return False
        if piv == 0:
            if any(A[i][k] != 0 for i in range(k+1, n)): return False
            continue
        for i in range(k+1, n):
            f = A[i][k]/piv
            if f:
                for j in range(k+1, n): A[i][j] -= f*A[k][j]
    return True

# ------------------------------------------------------------------------------------------------
def build(pb, maxnodes=200000, minw=2.0**-18, use_lp=True, use_cvx=True):
    """Depth-first builder; returns preorder list of node records and stats."""
    out = []; stats = dict(A=0, C=0, L=0, S=0)
    stack = [(np.array([float(a) for a, _ in pb.root]), np.array([float(b) for _, b in pb.root]))]
    worst = None
    while stack:
        lo, hi = stack.pop()
        if len(out) > maxnodes: return None, stats, ('maxnodes', worst)
        if float(pb.muf @ lo) >= pb.claimf:          # mirrors exact test up to float error; replay decides
            out.append(('A',)); stats['A'] += 1; continue
        leaf = pb.try_cvx(lo, hi) if use_cvx else None
        if leaf is None and use_lp: leaf = pb.try_lp(lo, hi)
        if leaf is not None:
            out.append(leaf); stats[leaf[0]] += 1; continue
        w = hi - lo; ax = int(np.argmax(w))
        if w[ax] < minw:
            Fc, _ = pb.Ff((lo + hi)/2)
            return None, stats, ('minwidth', (Fc, ((lo+hi)/2).tolist()))
        m = (lo[ax] + hi[ax])/2
        out.append(('S', ax)); stats['S'] += 1
        hi1 = hi.copy(); hi1[ax] = m; lo2 = lo.copy(); lo2[ax] = m
        stack.append((lo2, hi)); stack.append((lo, hi1))
    return out, stats, None

def replay(pb, cert):
    """exact replay of a preorder certificate; returns (ok, nfail, first failures)."""
    pos = 0; fails = []
    stack = [([a for a, _ in pb.root], [b for _, b in pb.root])]
    while stack:
        lo, hi = stack.pop()
        node = cert[pos]; pos += 1
        if node[0] == 'S':
            ax = node[1]; m = (lo[ax] + hi[ax])/2
            hi1 = hi[:]; hi1[ax] = m; lo2 = lo[:]; lo2[ax] = m
            stack.append((lo2, hi)); stack.append((lo, hi1))
        else:
            if not pb.check_leaf(lo, hi, node):
                fails.append((node[0], [float(v) for v in lo], [float(v) for v in hi]))
    return pos == len(cert) and not fails, fails

if __name__ == '__main__':
    pattern = sys.argv[1]
    shift = Fr(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else Fr(0)
    maxnodes = 200000
    if '--maxnodes' in sys.argv: maxnodes = int(sys.argv[sys.argv.index('--maxnodes') + 1])
    modes = dict(use_lp='--nolp' not in sys.argv, use_cvx='--nocvx' not in sys.argv)
    pb = Problem(pattern, shift)
    print(f'pattern {pattern} claim {pb.claim} = {float(pb.claim):.10f} root {[(str(a), str(b)) for a, b in pb.root]} modes {modes}')
    t0 = time.time(); cert, stats, err = build(pb, maxnodes, **modes); tb = time.time() - t0
    print('build', f'{tb:.1f}s', stats, 'error' if err else 'ok', err if err else '')
    if cert is None: sys.exit(1)
    tag = f'{pattern}' + (f'_shift{float(shift):+.2e}' if shift else '') + ''.join(k for k, v in modes.items() if not v)
    blob = json.dumps(cert, separators=(',', ':'))
    open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f'cert_K5_{tag}.json'), 'w').write(blob)
    print('nodes', len(cert), 'leaves', len(cert) - stats['S'], 'bytes(json)', len(blob))
    t0 = time.time(); ok, fails = replay(pb, cert); tr = time.time() - t0
    print('replay', f'{tr:.1f}s', 'ok' if ok else 'FAIL', len(fails), fails[:3], 'kernel points', len(KCACHE))
