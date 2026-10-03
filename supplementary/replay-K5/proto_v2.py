"""L1_1b/c checker v2/v3 (python mirror of CheckerCoreV3 = CheckerBase + CheckerLeaves; v3 fix in the M branch).

Differences from v1/v3:
  * grid 2^-64; sin/cos(pi x) by QUARTER-period reduction x = n/2 + f, |f| <= 1/4, so |pi f| <= pi/4 < 1 and the
    alternating-series bounds of L0_2 (`sin_taylor_bounds`, `cos_taylor_bounds`, 0 <= x <= 1) apply; degrees 17/16;
    sinc series 8 terms for |y| <= 1/2;
  * every analytic enclosure is a RECORD, computed once and stored widened to the grid 2^-60:
      KPt(x)  = (x, k0, k1, k2)            enclosures of k, k', k'' at the rational x
      Cell(n) = (n, plo, phi, wlo)          inf w'', sup w'', inf w on [n/64, (n+1)/64], from KPt((n+1/2)/64)
    leaves only combine stored numbers;
  * a span interval uses its covering cells iff at most 64 of them are needed (else the Taylor model only).
The builder is proto_cert3's float builder; every proposed leaf is accepted only if check_leaf_v2 says so.
"""
import sys, json, math, time
from fractions import Fraction as Fr
import numpy as np

SC = 1 << 64
def rdn(q): return Fr((q.numerator * SC) // q.denominator, SC)
def rup(q): return Fr(-((-q.numerator * SC) // q.denominator), SC)
ST = 1 << 60
def sdn(q): return Fr((q.numerator * ST) // q.denominator, ST) - Fr(1, ST)
def sup_(q): return Fr(-((-q.numerator * ST) // q.denominator), ST) + Fr(1, ST)


class I:
    __slots__ = ('lo', 'hi')
    def __init__(s, lo, hi=None): s.lo = lo; s.hi = lo if hi is None else hi
    def __add__(s, o):
        if not isinstance(o, I): o = I(Fr(o))
        return I(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__
    def __neg__(s): return I(-s.hi, -s.lo)
    def __sub__(s, o):
        if not isinstance(o, I): o = I(Fr(o))
        return I(s.lo - o.hi, s.hi - o.lo)
    def __mul__(s, o):                       # mirrors QI.mul (4 products, rounded) and QI.smul = mul (pt q)
        if not isinstance(o, I): o = I(Fr(o))
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
    def store(s): return I(sdn(s.lo), sup_(s.hi))


PI = I(Fr(314159265358979323846, 10**20), Fr(314159265358979323847, 10**20))
FACT = [math.factorial(n) for n in range(40)]
NS = 9; NC = 9; NSINC = 8


def horner(coeffs, t2):                      # mirrors List.foldr (fun c acc => c + acc * t2) (pt 0)
    acc = I(Fr(0))
    for c in reversed(coeffs):
        acc = I(Fr(c)) + acc*t2
    return acc


def sin_taylor(t):
    cs = [Fr((-1)**j, FACT[2*j+1]) for j in range(NS)]
    return (horner(cs, t.sq())*t).widen(rup(Fr(t.absmax())**(2*NS+1)/FACT[2*NS+1]))


def cos_taylor(t):
    cs = [Fr((-1)**j, FACT[2*j]) for j in range(NC)]
    return horner(cs, t.sq()).widen(rup(Fr(t.absmax())**(2*NC)/FACT[2*NC]))


AQ = Fr(4, 5)
SINA = sin_taylor(I(AQ)); COSA = cos_taylor(I(AQ))
INV2SA = (I(Fr(5, 2))*SINA).inv()


def sincos_pi(x):
    n = math.floor(2*x + Fr(1, 2)); f = x - Fr(n, 2)
    t = I(f)*PI
    s = sin_taylor(t); c = cos_taylor(t)
    m = n % 4
    if m == 0: return s, c
    if m == 1: return c, -s
    if m == 2: return -s, -c
    return -c, s


def sinc_derivs(y, sy, cy):
    if y.absmax() <= Fr(1, 2):
        N = NSINC; m = y.absmax(); y2 = y.sq()
        c0 = [Fr((-1)**j, FACT[2*j+1]) for j in range(N)]
        c1 = [Fr((-1)**(j+1)*2*(j+1), FACT[2*j+3]) for j in range(N-1)]
        c2 = [Fr((-1)**(j+1)*2*(j+1)*(2*j+1), FACT[2*j+3]) for j in range(N-1)]
        e0 = rup(Fr(m)**(2*N)/FACT[2*N+1]); e1 = rup(2*N*Fr(m)**(2*N-1)/FACT[2*N+1])
        e2 = rup(2*N*(2*N-1)*Fr(m)**(2*N-2)/FACT[2*N+1])
        return horner(c0, y2).widen(e0), (horner(c1, y2)*y).widen(e1), horner(c2, y2).widen(e2)
    iy = y.inv(); s0 = sy*iy; s1 = (cy - s0)*iy
    return s0, s1, (-s0) - I(Fr(2))*(s1*iy)


def kencl(x):
    sp, cp = sincos_pi(x)
    px = I(x)*PI
    out = []
    for sg in (-1, 1):
        y = px + I(sg*AQ)
        sy = sp*COSA + I(Fr(sg))*(cp*SINA)
        cy = cp*COSA - I(Fr(sg))*(sp*SINA)
        out.append(sinc_derivs(y, sy, cy))
    m, p = out
    k0 = (m[0] + p[0])*INV2SA
    k1 = ((m[1] + p[1])*INV2SA)*PI
    k2 = (((m[2] + p[2])*INV2SA)*PI)*PI
    return k0, k1, k2


PTS = {}
def kpt(x):
    r = PTS.get(x)
    if r is None:
        k0, k1, k2 = kencl(x); r = (k0.store(), k1.store(), k2.store()); PTS[x] = r
    return r


M3Q = rup(PI.hi**3/4)
CB = 6; CW = Fr(1, 1 << CB); MAXCELLS = 64


def taylor_model(kk, r):
    """(inf w'', sup w'', inf w) on [x0-r, x0+r] from stored k0,k1,k2 at x0 (mirrors CheckerV2.taylorModel)."""
    k0, k1, k2 = kk
    T = I(-r, r); T2 = I(Fr(0), r*r)
    kI = (k0 + k1*T + I(Fr(1, 2))*(k2*T2)).widen(rup(M3Q*r**3/6))
    k1I = (k1 + k2*T).widen(rup(M3Q*r*r/2))
    k2I = k2.widen(rup(M3Q*r))
    wpp = I(Fr(2))*(k1I.sq() + kI*k2I)
    return wpp.lo, wpp.hi, max(Fr(0), kI.sq().lo)


CELLS = {}
def cell(n):
    r = CELLS.get(n)
    if r is None:
        a, b, c = taylor_model(kpt((n + Fr(1, 2))*CW), CW/2)
        r = (sdn(a), sup_(b), max(Fr(0), sdn(c))); CELLS[n] = r
    return r


def cell_range(x0, r):
    n0 = math.floor((x0 - r)/CW); n1 = math.ceil((x0 + r)/CW)
    if n1 == n0: n1 = n0 + 1
    return (n0, n1) if n1 - n0 <= MAXCELLS else None


def span_bounds(x0, r):
    plo, phi, wlo = taylor_model(kpt(x0), r)
    cr = cell_range(x0, r)
    if cr is not None:
        cs = [cell(n) for n in range(*cr)]
        plo = max(plo, min(c[0] for c in cs)); phi = min(phi, max(c[1] for c in cs)); wlo = max(wlo, min(c[2] for c in cs))
    return plo, phi, wlo


SP = None
def setup(K):
    global SP
    SP = [(i, s) for s in range(1, K) for i in range(K - s)]


def check_leaf_v2(gam, mu, claim, lo, hi, leaf):
    """gam: pattern weights in SP order (zeros allowed); mirrors CheckerV2 Leaf.check."""
    d = len(mu)
    if leaf[0] == 'A':
        return sum(m*l for m, l in zip(mu, lo)) >= claim
    c = [(a + b)/2 for a, b in zip(lo, hi)]; h = [(b - a)/2 for a, b in zip(lo, hi)]
    gh = [Fr(v, 1 << 40) for v in leaf[1]]
    if not all(a <= v <= b for a, v, b in zip(lo, gh, hi)): return False
    if leaf[0] == 'C':
        Flo = sum(m*v for m, v in zip(mu, gh)); grad = [I(m) for m in mu]
        P = [[Fr(0)]*d for _ in range(d)]
        for j, (i, sl) in enumerate(SP):
            if gam[j] == 0: continue
            x0 = sum(c[i:i+sl]); r = sum(h[i:i+sl]); xh = sum(gh[i:i+sl])
            plo, _, _ = span_bounds(x0, r)
            k0, k1, _ = kpt(xh)
            Flo += gam[j]*k0.sq().lo
            wd = I(2*gam[j])*(k0*k1)
            for a in range(i, i+sl):
                grad[a] = grad[a] + wd
                for b in range(i, i+sl): P[a][b] += gam[j]*plo
        if not ldl_psd(P): return False
        corr = sum((grad[a]*I(lo[a] - gh[a], hi[a] - gh[a])).lo for a in range(d))
        return Flo + corr >= claim
    if leaf[0] == 'M':
        y = [Fr(v, 1 << 30) for v in leaf[2]]
        lam = y[-1]
        if lam < 0: return False
        rho = [m*(1 + lam) for m in mu]; kap = -lam*claim; t = 0
        for j, (i, sl) in enumerate(SP):
            if gam[j] == 0: continue
            x0 = sum(c[i:i+sl]); r = sum(h[i:i+sl]); xh = sum(gh[i:i+sl])
            yy = y[t:t+5]; t += 5
            if sum(yy) > gam[j] or min(yy) < 0: return False
            if yy[3] != 0 and not (x0 - r <= xh <= x0 + r): return False   # v3 fix (C18): tangent at x̂ only inside
            plo, phi, wlo = span_bounds(x0, r)
            pen = max(Fr(0), -plo)

            def tangent(tp):
                k0, k1, _ = kpt(tp)
                rr = max(abs(x0 - r - tp), abs(x0 + r - tp))
                w0 = k0.sq(); w1 = I(Fr(2))*(k0*k1); sig = rdn((w1.lo + w1.hi)/2)
                return sig, w0.lo - max(abs(w1.lo - sig), abs(w1.hi - sig))*rr - pen*rr*rr/2 - sig*tp
            l2 = tangent(x0); l3 = tangent(xh)
            wa = kpt(x0 - r)[0].sq().lo; wb = kpt(x0 + r)[0].sq().lo
            slp = (wb - wa)/(2*r) if r > 0 else Fr(0); slq = rdn(slp)
            l4 = (slq, wa - slq*(x0 - r) - abs(slp - slq)*2*r - max(phi, Fr(0))*(2*r)**2/8)
            lines = [(Fr(0), Fr(0)), (Fr(0), wlo), l2, l3, l4]
            slope = sum(v*l[0] for v, l in zip(yy, lines)); const = sum(v*l[1] for v, l in zip(yy, lines))
            kap += const
            for a in range(i, i+sl): rho[a] += slope
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
            for j in range(k+1, n): A[i][j] -= f*A[k][j]
    return True
