"""d8_9 (session 3): bnb_lb3_w.py = d6_5's bnb_lb3.py (md5 9be8f8fe...) + X2's all-marks pattern-weight check
(base_gam / pattern / reversal symmetry of the BASE weights, gam' = gam m_i m_{i+s}; from X2_numerics/bnb_interval_w.py),
weights-file md5 in the checkpoint key, Theorem G skipped in pattern mode.  Nothing else changed.

d6_5 (session 3): bnb_lb3.py = d3_1/Z1's bnb_interval_w.py (md5 7c192cdd...) + a third rigorous box bound LB3
and an optional reversal-symmetry reduction.  Changes (everything else untouched):
  * Arb kernel enclosures now also give k''(x) at the exact dyadic span centre (sinc'' = -sinc - 2 sinc'/y, Taylor
    with remainder for |y| < 1/16).
  * LB3 (convex-underestimator bound, rigorous; numpy engine with one-ulp outward rounding):
        on a span interval |x - sc| <= hs:  w''(x) = 2k'(x)^2 + 2k(x)k''(x) >= wlo_s   (Taylor-model enclosure from
        k, k', k'' at sc and |k'''| <= M3 = pi^3/4; valid for v even, >= 0, nonincreasing on [0,1/2] (Chebyshev),
        e.g. cos(alpha s), alpha <= pi).  Hence for delta in the box
        F(c+delta) >= F(c) + g.delta + 1/2 sum_s beta_s wlo_s (v_s.delta)^2 >= F_lo(c) - Nneg + q(delta),
        q(delta) = g.delta + 1/2 delta^T P delta,  P = sum_{wlo_s>0} p_s v_s v_s^T,  0 <= p_s <= beta_s wlo_s,
        Nneg = 1/2 sum_{wlo_s<0} beta_s |wlo_s| hs^2.  q is convex, so for ANY point dhat (a float box-QP minimiser,
        rounded to a dyadic grid so that the span sums u_s = v_s.dhat are exact):
        q(delta) >= -1/2 sum_s p_s u_s^2 - sum_i |g_i + (P dhat)_i| h_i    (g_i ranging over its interval).
    LB3 = F_lo(c) - Nneg - 1/2 sum p_s u_s^2 - sum_i max|g_i + (P dhat)_i| h_i.  A box is accepted iff
    max(LB1, LB2, LB3) > c_claim (upper float of c_claim).  With dhat = 0, p = 0 LB3 is LB2 with the signed
    curvature bound in place of |w''| <= W2.
  * --sym: for exactly reversal-symmetric weights (asserted in Fractions) F(g) = F(reverse g), so it suffices to
    certify on {g_0 >= g_{d-1}}; boxes with c_0 + h_0 < c_{d-1} - h_{d-1} (exact dyadic test) are discarded.
  * --lb3 routes every box through the rigorous numpy engine (the float screen only picks bisection axes).

Original docstring:
Interval-arithmetic (rigorous) branch-and-bound certificate of the K-point local inequality (LI)

    F_K(g) = mu * sum_{i<K} g_i + sum_{s=1}^{K-1} beta_s sum_{i=1}^{K-s} w(g_i + ... + g_{i+s-1}) > c_claim
    for all g in [0, inf)^{K-1},   beta_s = 2/(K-s),  w = k^2,
    k(x) = (1/2)[sinc(pi x - a) + sinc(pi x + a)] / sinc(a),  a = alpha/2   (Gram kernel of v = cos(alpha s)
    on [-1/2,1/2], normalised; v >= 0 for alpha < pi, so |k| <= 1, |k'| <= pi, |k''| <= pi^2).

Same algorithm and box bounds as bnb.py (LB1: Taylor per span; LB2: second-order mean value), but:
  * all box centres / half-widths are exact dyadic rationals (initial cell width a power of two, bisection
    halves) -- asserted every chunk; the float64 bookkeeping is therefore exact, no covering slivers;
  * domain pruning  mu * sum_i (c_i - h_i) >= c_claim  is decided exactly (dyadic float vs rational threshold);
  * a box is ACCEPTED (removed from the stack) only if the lower endpoint of an interval enclosure of
    max(LB1, LB2) is > c_claim (backend: python-flint/Arb ball arithmetic, or mpmath.iv); there is no pad;
  * a box is REJECTED as a counterexample only if the interval enclosure of F(centre) lies entirely < c_claim.
  * Default mode 'hybrid': the float bounds of bnb.py (vectorised numpy) are used only to *choose* which boxes to
    bisect and along which axis (a heuristic that cannot affect soundness); every box the float screen would
    accept is re-checked in interval arithmetic and bisected further if the interval check fails.  '--pure'
    evaluates every box in interval arithmetic.

CLI:  python bnb_interval.py alpha K muinv c_claim [--backend flint|mpmath] [--prec BITS] [--min-width W]
          [--pure] [--workers N] [--checkpoint FILE] [--ckpt-every M] [--resume] [--log-every N] [--max-boxes B]
alpha, muinv and c_claim are parsed as exact decimals (mu = 1/muinv).
"""
import sys, time, os, pickle, argparse
from fractions import Fraction
import numpy as np

DYADIC_BITS = 40          # every centre / half-width is a multiple of 2^-DYADIC_BITS (asserted)


def spans(K):
    """list of (start, length) for all spans; beta_s = 2/(K-s)."""
    return [(i, s) for s in range(1, K) for i in range(0, K - s)]


# --------------------------------------------------------------------------------------------------
# Interval backends.  Each exposes: num(float) exact; q(Fraction) enclosure; lo(I)/hi(I) exact endpoints
# (as point intervals); nonneg(P); minp(P,Q) for points; sinc, dsinc (sinc'), sin, cos; gt(I,J) certain I>J;
# lt(I,J) certain I<J; unit = [-1,1]; mid(I) float.
# --------------------------------------------------------------------------------------------------
class FlintBackend:
    name = 'flint'

    def __init__(self, prec):
        import flint
        flint.ctx.prec = prec
        self.flint = flint
        self.arb = flint.arb
        self.prec = prec
        self.unit = flint.arb(0, 1)
        self.pi = flint.arb.pi()

    def num(self, x):
        return self.arb(x)                       # exact for a python float

    def q(self, fr):
        return self.arb(self.flint.fmpq(fr.numerator, fr.denominator))

    def lo(self, I):
        return I.lower()

    def hi(self, I):
        return I.upper()

    def nonneg(self, P):
        return P.nonnegative_part()

    def minp(self, P, Q):
        return P.min(Q)

    def sinc(self, y):
        return y.sinc()                          # Arb's rigorous sinc (handles intervals containing 0)

    def sin(self, y):
        return y.sin()

    def cos(self, y):
        return y.cos()

    def absupper_float(self, I):
        return float(I.abs_upper().upper())     # only used for a branch decision (upward-rounded)

    def gt(self, I, J):
        return bool(I > J)

    def lt(self, I, J):
        return bool(I < J)

    def mid(self, I):
        return float(I.mid())


class MpmathBackend:
    name = 'mpmath'

    def __init__(self, prec):
        from mpmath import iv
        iv.prec = prec
        self.iv = iv
        self.prec = prec
        self.unit = iv.mpf([-1, 1])
        self.pi = iv.pi

    def num(self, x):
        return self.iv.mpf(x)

    def q(self, fr):
        return self.iv.mpf(fr.numerator) / fr.denominator

    def lo(self, I):
        return I.a

    def hi(self, I):
        return I.b

    def nonneg(self, P):
        return P if P.a > 0 else self.iv.mpf(0)

    def minp(self, P, Q):
        return P if P.b <= Q.a else Q            # points: exact comparison

    def sinc(self, y):
        yu = abs(y).b
        if yu < 0.0625:                          # Taylor, |R| <= |y|^12/13!
            y2 = y * y
            y4 = y2 * y2
            s = 1 - y2 / 6 + y4 / 120 - y4 * y2 / 5040 + y4 * y4 / 362880 - y4 * y4 * y2 / 39916800
            return s + self.unit * (yu ** 12 / 6227020800)
        return self.iv.sin(y) / y

    def sin(self, y):
        return self.iv.sin(y)

    def cos(self, y):
        return self.iv.cos(y)

    def absupper_float(self, I):
        return float(abs(I).b)

    def gt(self, I, J):
        return bool(I.a > J.b)

    def lt(self, I, J):
        return bool(I.b < J.a)

    def mid(self, I):
        return float(I.mid)


def make_backend(name, prec):
    if name == 'flint':
        return FlintBackend(prec)
    if name == 'mpmath':
        return MpmathBackend(prec)
    try:
        return FlintBackend(prec)
    except ImportError:
        return MpmathBackend(prec)


class IntervalCertifier:
    """Rigorous per-box evaluation of k, k', LB1, LB2 and F(centre)."""

    def __init__(self, backend, alpha, K, muinv, c_claim, cache_max=4_000_000, weights=None, polywin=None):
        B = self.B = backend
        self.polywin = polywin
        self.K = K
        self.sp = spans(K)
        # weights = (gam: list of Fractions aligned with spans(K) [(i,s) order], muv: list of K-1 Fractions)
        if weights is None:
            weights = ([Fraction(2, K - s) for (_, s) in self.sp], [1 / Fraction(muinv)] * (K - 1))
        self.gamq, self.muvq = weights
        if polywin is None:
            self.a = B.q(Fraction(alpha)) / 2
        else:
            assert B.name == 'flint', "polynomial windows need the flint backend"
            self.a = B.q(Fraction(1)) / 2          # unused placeholder
            polywin.arb_setup()
        self.sa = B.sinc(self.a)
        self.muv = [B.q(m) for m in self.muvq]
        self.mu = B.q(min(self.muvq))
        self.c = B.q(Fraction(c_claim))
        self.pi = B.pi
        self.pi2 = self.pi * self.pi
        self.pi2h = self.pi2 / 2
        self.piU = B.hi(self.pi)
        self.one = B.num(1.0)
        self.beta = [B.q(g) for g in self.gamq]
        self.beta2 = [2 * b for b in self.beta]
        self.cache = {}
        self.cache_max = cache_max
        self.inv2sa = 1 / (2 * self.sa)
        self.pih_sa = self.pi / (2 * self.sa)
        self.pi2h_sa = self.pi2 / (2 * self.sa)
        self.cache2 = {}
        # |k'''| <= 8 pi^3 E_v|s|^3 <= 8 pi^3 / 32 = pi^3/4 for v even, >= 0, nonincreasing on [0, 1/2]
        # (Chebyshev's integral inequality); v = cos(alpha s) qualifies for 0 < alpha <= pi.
        if polywin is None:
            assert 0 < Fraction(alpha) <= Fraction(314159, 100000)
            self.M3 = self.pi2 * self.pi / 4
        else:
            assert polywin.positive_arb() > 0, "window must be > 0"
            self.M3 = polywin.aM3                  # 8 pi^3 int|s|^3 v / int v >= sup|k'''|

    def dsinc(self, y):
        """sinc'(y) = (cos y - sinc y)/y, with a Taylor expansion + rigorous remainder near 0:
        sinc'(y) = -y/3 + y^3/30 - y^5/840 + y^7/45360 + R, |R| <= |y|^9/(9! * 11)."""
        B = self.B
        yu = B.absupper_float(y)
        if yu < 0.0625:
            y2 = y * y
            y3 = y2 * y
            s = -y / 3 + y3 / 30 - y3 * y2 / 840 + y3 * y2 * y2 / 45360
            return s + B.unit * B.num((yu * (1 + 1e-12)) ** 9 / 3991680 * (1 + 1e-12))
        return (B.cos(y) - B.sinc(y)) / y

    def dsinc2(self, y):
        """sinc''(y) = -sinc(y) - 2 sinc'(y)/y, with Taylor + rigorous remainder near 0:
        sinc''(y) = -1/3 + y^2/10 - y^4/168 + y^6/6480 + R, |R| <= |y|^8/443520 (alternating, decreasing terms)."""
        B = self.B
        yu = B.absupper_float(y)
        if yu < 0.0625:
            y2 = y * y
            y4 = y2 * y2
            s = B.num(-1.0) / 3 + y2 / 10 - y4 / 168 + y4 * y2 / 6480
            return s + B.unit * B.num((yu * (1 + 1e-12)) ** 8 / 400000.0)
        return -B.sinc(y) - 2 * self.dsinc(y) / y

    def kern2(self, x):
        """(k(x), k'(x), k''(x)) enclosures at the exact dyadic point x (cached separately)."""
        r = self.cache2.get(x)
        if r is not None:
            return r
        B = self.B
        if self.polywin is not None:
            r = self.polywin.arb_kernel(B.num(x))
            if len(self.cache2) >= self.cache_max:
                self.cache2.clear()
            self.cache2[x] = r
            return r
        px = self.pi * B.num(x)
        y1 = px - self.a
        y2 = px + self.a
        kk = (B.sinc(y1) + B.sinc(y2)) * self.inv2sa
        kd = (self.dsinc(y1) + self.dsinc(y2)) * self.pih_sa
        k2 = (self.dsinc2(y1) + self.dsinc2(y2)) * self.pi2h_sa
        if len(self.cache2) >= self.cache_max:
            self.cache2.clear()
        self.cache2[x] = (kk, kd, k2)
        return kk, kd, k2

    def kern(self, x):
        """(k(x), k'(x)) enclosures at the exact dyadic point x (cached)."""
        r = self.cache.get(x)
        if r is not None:
            return r
        B = self.B
        if self.polywin is not None:
            kk, kd, _ = self.polywin.arb_kernel(B.num(x))
            if len(self.cache) >= self.cache_max:
                self.cache.clear()
            self.cache[x] = (kk, kd)
            return kk, kd
        px = self.pi * B.num(x)
        y1 = px - self.a
        y2 = px + self.a
        kk = (B.sinc(y1) + B.sinc(y2)) * self.inv2sa
        kd = (self.dsinc(y1) + self.dsinc(y2)) * self.pih_sa
        if len(self.cache) >= self.cache_max:
            self.cache.clear()
        self.cache[x] = (kk, kd)
        return kk, kd

    def box(self, c, h, full=False):
        """c, h: sequences of python floats (exact dyadics).  Returns (accepted, Fc_hi_below_claim, Fc_mid);
        with full=True returns the interval enclosures (LB1, LB2, F(centre)) instead."""
        B = self.B
        # exact span centres / half-widths (sums of dyadics that fit in 53 bits)
        pc = [0.0]
        ph = [0.0]
        for ci, hi in zip(c, h):
            pc.append(pc[-1] + ci)
            ph.append(ph[-1] + hi)
        lin_c = B.num(0.0)
        lin_lo = B.num(0.0)
        for ci, hi, mi in zip(c, h, self.muv):
            lin_c = lin_c + mi * B.num(ci)
            lin_lo = lin_lo + mi * B.num(ci - hi)   # ci - hi exact dyadic
        acc1 = B.num(0.0)
        accF = B.num(0.0)
        accR = B.num(0.0)
        d = self.K - 1
        P = []
        for j, (i, s) in enumerate(self.sp):
            x = pc[i + s] - pc[i]
            hsf = ph[i + s] - ph[i]
            kk, kd = self.kern(x)
            hs = B.num(hsf)
            bj = self.beta[j]
            akl = B.lo(abs(kk))
            akh = B.hi(abs(kk))
            adh = B.hi(abs(kd))
            # LB1:  |k| >= |k(sc)| - |k'(sc)| hs - pi^2 hs^2/2  (clipped at 0), then squared
            hs2 = hs * hs
            t = B.nonneg(B.lo(akl - adh * hs - self.pi2h * hs2))
            acc1 = acc1 + bj * t * t
            # LB2 pieces
            accF = accF + bj * kk * kk
            P.append(self.beta2[j] * kk * kd)
            K1 = B.minp(B.hi(adh + self.pi2 * hs), self.piU)
            K0 = B.minp(B.hi(akh + adh * hs + self.pi2h * hs2), self.one)
            accR = accR + bj * B.hi(2 * (K1 * K1 + K0 * self.pi2)) * hs2
        LB1 = lin_lo + acc1
        if not full and B.gt(LB1, self.c):
            return True, False, None
        Fc = lin_c + accF
        gsum = B.num(0.0)
        for idx in range(d):
            g = self.muv[idx]
            for j, (i, s) in enumerate(self.sp):
                if i <= idx < i + s:
                    g = g + P[j]
            gsum = gsum + B.hi(abs(g)) * B.num(h[idx])
        LB2 = Fc - gsum - accR / 2
        if full:
            return LB1, LB2, Fc
        if B.gt(LB2, self.c):
            return True, False, B.mid(Fc)
        return False, B.lt(Fc, self.c), B.mid(Fc)

    def F_centre(self, g):
        """interval enclosure of F at an exact point g."""
        B = self.B
        pc = [0.0]
        for gi in g:
            pc.append(pc[-1] + gi)
        acc = B.num(0.0)
        for gi, mi in zip(g, self.muv):
            acc = acc + mi * B.num(gi)
        for j, (i, s) in enumerate(self.sp):
            kk, _ = self.kern(pc[i + s] - pc[i])
            acc = acc + self.beta[j] * kk * kk
        return acc


# ----- multiprocessing helpers (hybrid mode: interval check of float-accepted leaves) -----
_W = None


def _winit(backend, prec, alpha, K, muinv, c_claim):
    global _W
    _W = IntervalCertifier(make_backend(backend, prec), alpha, K, muinv, c_claim)


def _wcheck(args):
    C, H = args
    out = np.zeros(len(C), dtype=bool)
    for n in range(len(C)):
        out[n] = _W.box(C[n].tolist(), H[n].tolist())[0]
    return out


def float_bounds(C, Hh, V, beta, mu, k, kp, lin_lo):
    # mu: numpy vector (per-gap penalties); lin_lo = (C-Hh) @ mu
    """bnb.py's float LB (no pad) -- used ONLY as a heuristic screen / bisection-axis selector."""
    PI = np.pi
    sc = C @ V.T
    hs = Hh @ V.T
    kk = k(sc)
    kd = kp(sc)
    ak = np.abs(kk)
    akd = np.abs(kd)
    klo = np.maximum(ak - akd * hs - 0.5 * PI ** 2 * hs ** 2, 0.0)
    LB1 = lin_lo + (klo ** 2) @ beta
    Fc = C @ mu + (kk ** 2) @ beta
    grad = mu + (2 * kk * kd * beta) @ V
    K1 = np.minimum(akd + PI ** 2 * hs, PI)
    K0 = np.minimum(ak + akd * hs + 0.5 * PI ** 2 * hs ** 2, 1.0)
    W2 = 2 * (K1 ** 2 + K0 * PI ** 2)
    LB2 = Fc - np.sum(np.abs(grad) * Hh, axis=1) - 0.5 * (W2 * hs ** 2) @ beta
    return np.maximum(LB1, LB2), Fc, grad


# --------------------------------------------------------------------------------------------------
# Vectorised engine: interval arithmetic on float64 with outward rounding by one ulp after every operation
# (np.nextafter).  Valid because IEEE-754 binary64 +, -, * (numpy elementwise ufuncs, round-to-nearest) return
# a result within 1/2 ulp of the exact value, so [pred(fl(x)), succ(fl(x))] contains the exact value.
# Kernel enclosures k(sc), k'(sc) come from the scalar backend (Arb / mpmath.iv), cached per exact dyadic sc,
# rounded outward to float64.  Only the LOWER endpoints of LB1, LB2 are propagated (plus the upper endpoints of
# the subtracted quantities), so each line below is a directed-rounding chain.
# --------------------------------------------------------------------------------------------------
_UP = lambda x: np.nextafter(x, np.inf)
_DN = lambda x: np.nextafter(x, -np.inf)


class NumpyIntervalLB:
    def __init__(self, cert):
        self.cert = cert
        B = cert.B
        self.sp = cert.sp
        f_lo = lambda I: float(_DN(float(B.lo(I).mid() if B.name == 'flint' else B.lo(I).a)))
        f_hi = lambda I: float(_UP(float(B.hi(I).mid() if B.name == 'flint' else B.hi(I).b)))
        self.f_lo, self.f_hi = f_lo, f_hi
        self.mu_lo = np.array([f_lo(m) for m in cert.muv]); self.mu_hi = np.array([f_hi(m) for m in cert.muv])
        self.pi_hi = f_hi(cert.pi)
        self.pi2_hi = f_hi(cert.pi2)
        self.pi2h_hi = f_hi(cert.pi2h)
        self.b_lo = [f_lo(b) for b in cert.beta]
        self.b_hi = [f_hi(b) for b in cert.beta]
        self.c_up = f_hi(cert.c)                   # >= c_claim
        self.kc = {}                               # sc -> (klo, khi, dlo, dhi) floats
        cert.cache_max = 10000                     # the float-endpoint cache kc is the one that matters here
        # ---- LB3 data ----
        self.use_lb3 = False
        self.qp_sweeps = 12
        self.kc3 = {}                              # sc -> (klo, khi, dlo, dhi, d2lo, d2hi) floats
        self.M3_hi = f_hi(cert.M3)
        self.b_lo_arr = np.array(self.b_lo)
        self.b_hi_arr = np.array(self.b_hi)
        d = cert.K - 1
        self.Vm = np.zeros((len(self.sp), d))
        for j, (i, s) in enumerate(self.sp):
            self.Vm[j, i:i + s] = 1.0
        self.lb3_stats = dict(acc_by_lb3_only=0)

    def kernel_arrays3(self, sc):
        u, inv = np.unique(sc, return_inverse=True)
        tab = np.empty((len(u), 6))
        kc = self.kc3
        for n, x in enumerate(u.tolist()):
            r = kc.get(x)
            if r is None:
                kk, kd, k2 = self.cert.kern2(x)
                r = (self.f_lo(kk), self.f_hi(kk), self.f_lo(kd), self.f_hi(kd), self.f_lo(k2), self.f_hi(k2))
                if len(kc) > 2_000_000:
                    kc.clear()
                kc[x] = r
            tab[n] = r
        inv = inv.reshape(sc.shape)
        return tuple(tab[inv, j] for j in range(6))

    def qp_float(self, gm, p, H):
        """float projected coordinate descent for min_{|delta_i|<=h_i} gm.delta + 1/2 sum_s p_s (v_s.delta)^2
        (heuristic only: any output is admissible in the rigorous LB3 formula)."""
        n, d = gm.shape
        Vm = self.Vm
        delta = np.zeros((n, d))
        u = np.zeros_like(p)
        diag = p @ Vm
        with np.errstate(divide='ignore', invalid='ignore'):
            for sweep in range(self.qp_sweeps):
                for i in range(d):
                    col = Vm[:, i]
                    gi = gm[:, i] + (p * u) @ col
                    Pii = diag[:, i]
                    nd = np.where(Pii > 0, delta[:, i] - gi / np.where(Pii > 0, Pii, 1.0), -np.sign(gi) * H[:, i])
                    nd = np.clip(nd, -H[:, i], H[:, i])
                    dd = nd - delta[:, i]
                    delta[:, i] = nd
                    u += dd[:, None] * col[None, :]
        return delta

    def kernel_arrays(self, sc):
        u, inv = np.unique(sc, return_inverse=True)
        tab = np.empty((len(u), 4))
        kc = self.kc
        for n, x in enumerate(u.tolist()):
            r = kc.get(x)
            if r is None:
                kk, kd = self.cert.kern(x)
                r = (self.f_lo(kk), self.f_hi(kk), self.f_lo(kd), self.f_hi(kd))
                if len(kc) > 2_000_000:
                    kc.clear()
                kc[x] = r
            tab[n] = r
        inv = inv.reshape(sc.shape)
        return tab[inv, 0], tab[inv, 1], tab[inv, 2], tab[inv, 3]

    def lower_bounds(self, C, H):
        """rigorous lower bounds (LB1, LB2) for boxes C +- H (arrays n x d of exact dyadics)."""
        n, d = C.shape
        z = np.zeros((n, 1))
        PC = np.concatenate([z, np.cumsum(C, axis=1)], axis=1)      # exact (dyadic, < 2^52 bits)
        PH = np.concatenate([z, np.cumsum(H, axis=1)], axis=1)
        sc = np.stack([PC[:, i + s] - PC[:, i] for (i, s) in self.sp], axis=1)
        hs = np.stack([PH[:, i + s] - PH[:, i] for (i, s) in self.sp], axis=1)
        if self.use_lb3:
            klo, khi, dlo, dhi, d2lo, d2hi = self.kernel_arrays3(sc)
        else:
            klo, khi, dlo, dhi = self.kernel_arrays(sc)
        ak_lo = np.maximum(np.maximum(klo, -khi), 0.0)
        ak_hi = np.maximum(np.abs(klo), np.abs(khi))
        ad_hi = np.maximum(np.abs(dlo), np.abs(dhi))
        hs2 = _UP(hs * hs)
        adhs = _UP(ad_hi * hs)
        pih = _UP(self.pi2h_hi * hs2)
        # LB1
        t = np.maximum(_DN(_DN(ak_lo - adhs) - pih), 0.0)
        tt = _DN(t * t)
        k2 = _DN(ak_lo * ak_lo)
        # products 2 beta k k'
        p = np.stack([klo * dlo, klo * dhi, khi * dlo, khi * dhi])
        kd_lo, kd_hi = _DN(p.min(axis=0)), _UP(p.max(axis=0))
        K1 = np.minimum(_UP(ad_hi + _UP(self.pi2_hi * hs)), self.pi_hi)
        K0 = np.minimum(_UP(_UP(ak_hi + adhs) + pih), 1.0)
        W2 = 2.0 * _UP(_UP(K1 * K1) + _UP(K0 * self.pi2_hi))
        W2h = _UP(W2 * hs2)
        S_lo = np.sum(C - H, axis=1)                                 # exact
        S_c = PC[:, -1]                                              # exact
        acc1 = np.zeros(n); accF = np.zeros(n)
        for i in range(d):          # (C-H) >= 0 and C >= 0 exact; mu_lo > 0
            acc1 = _DN(acc1 + _DN(self.mu_lo[i] * (C[:, i] - H[:, i])))
            accF = _DN(accF + _DN(self.mu_lo[i] * C[:, i]))
        accR = np.zeros(n)
        glo = np.tile(self.mu_lo, (n, 1))
        ghi = np.tile(self.mu_hi, (n, 1))
        for j, (i, s) in enumerate(self.sp):
            blo, bhi = self.b_lo[j], self.b_hi[j]
            acc1 = _DN(acc1 + _DN(blo * tt[:, j]))
            accF = _DN(accF + _DN(blo * k2[:, j]))
            accR = _UP(accR + _UP(bhi * W2h[:, j]))
            pl = _DN(np.minimum(2 * blo * kd_lo[:, j], 2 * bhi * kd_lo[:, j]))   # 2*b exact
            ph = _UP(np.maximum(2 * blo * kd_hi[:, j], 2 * bhi * kd_hi[:, j]))
            glo[:, i:i + s] = _DN(glo[:, i:i + s] + pl[:, None])
            ghi[:, i:i + s] = _UP(ghi[:, i:i + s] + ph[:, None])
        ag = np.maximum(np.abs(glo), np.abs(ghi))
        gsum = np.zeros(n)
        for i in range(d):
            gsum = _UP(gsum + _UP(ag[:, i] * H[:, i]))
        LB1 = acc1
        LB2 = _DN(_DN(accF - gsum) - 0.5 * accR)
        if not self.use_lb3:
            return LB1, LB2
        # ---------------- LB3 (see module docstring) ----------------
        M3 = self.M3_hi
        A2 = np.maximum(np.abs(d2lo), np.abs(d2hi))                  # >= |k''(sc)|
        hs3 = _UP(hs2 * hs)
        # k'(x) on |x-sc|<=hs:  in [dlo, dhi] + [-e1, e1],  e1 = |k''(sc)| hs + M3 hs^2/2
        e1 = _UP(_UP(A2 * hs) + _UP(0.5 * _UP(M3 * hs2)))
        K1lo = _DN(dlo - e1)
        K1hi = _UP(dhi + e1)
        m1 = np.maximum(np.maximum(K1lo, -K1hi), 0.0)                 # <= min |k'| on the span interval
        kp2 = _DN(m1 * m1)
        # k(x): in [klo, khi] + [-e0, e0],  e0 = |k'(sc)| hs + |k''(sc)| hs^2/2 + M3 hs^3/6
        e0 = _UP(_UP(adhs + _UP(0.5 * _UP(A2 * hs2))) + _UP(_UP(M3 * hs3) / 6.0))
        K0lo = _DN(klo - e0)
        K0hi = _UP(khi + e0)
        # k''(x): in [d2lo, d2hi] + [-M3 hs, M3 hs]
        e2 = _UP(M3 * hs)
        K2lo = _DN(d2lo - e2)
        K2hi = _UP(d2hi + e2)
        pr = np.stack([K0lo * K2lo, K0lo * K2hi, K0hi * K2lo, K0hi * K2hi])
        kk2lo = _DN(pr.min(axis=0))                                  # <= min k k''
        wlo = 2.0 * _DN(kp2 + kk2lo)                                  # <= min w'' on the span interval (2* exact)
        pos = wlo > 0
        pco = np.where(pos, _DN(self.b_lo_arr[None, :] * wlo), 0.0)   # 0 <= p_s <= beta_s wlo_s
        pco = np.maximum(pco, 0.0)
        negt = np.where(pos, 0.0, _UP(self.b_hi_arr[None, :] * _UP((-wlo) * hs2)))
        Nneg = np.zeros(n)
        for j in range(len(self.sp)):
            Nneg = _UP(Nneg + negt[:, j])
        Nneg = 0.5 * Nneg                                            # exact
        # float QP for dhat, rounded to multiples of 2^-30 (span sums then exact in float64)
        gm = 0.5 * (glo + ghi)
        dh = self.qp_float(gm, pco, H)
        dh = np.round(dh * 2.0 ** 30) / 2.0 ** 30
        PCd = np.concatenate([z, np.cumsum(dh, axis=1)], axis=1)     # exact: |dh| < 2^8, 30 fractional bits
        u = np.stack([PCd[:, i + s] - PCd[:, i] for (i, s) in self.sp], axis=1)
        T1 = np.zeros(n)
        Pdl = np.zeros((n, d))
        Pdh = np.zeros((n, d))
        for j, (i, s) in enumerate(self.sp):
            pj = pco[:, j]
            uj = u[:, j]
            T1 = _UP(T1 + _UP(pj * _UP(uj * uj)))
            pu = pj * uj
            Pdl[:, i:i + s] = _DN(Pdl[:, i:i + s] + _DN(pu)[:, None])
            Pdh[:, i:i + s] = _UP(Pdh[:, i:i + s] + _UP(pu)[:, None])
        T1 = 0.5 * T1
        rlo = _DN(glo + Pdl)
        rhi = _UP(ghi + Pdh)
        ra = np.maximum(np.abs(rlo), np.abs(rhi))
        T2 = np.zeros(n)
        for i in range(d):
            T2 = _UP(T2 + _UP(ra[:, i] * H[:, i]))
        LB3 = _DN(_DN(_DN(accF - Nneg) - T1) - T2)
        self.last_parts = (accF, Nneg, T1, T2, LB2)          # diagnostics only
        # bisection heuristic (soundness-neutral): d(loss)/d(h_i) ~ |g_i| + sum_{s ni i} beta_s |wlo_s^-| hs_s
        lossd = np.abs(gm).copy()
        negc = np.where(pos, 0.0, self.b_hi_arr[None, :] * (-wlo) * hs)
        for j, (i, s) in enumerate(self.sp):
            lossd[:, i:i + s] += negc[:, j][:, None]
        self.last_score = H * lossd
        return LB1, LB2, LB3

    def accept(self, C, H):
        LBs = self.lower_bounds(C, H)
        best12 = np.maximum(LBs[0], LBs[1])
        if not self.use_lb3:
            return best12 > self.c_up
        acc12 = best12 > self.c_up
        acc = acc12 | (LBs[2] > self.c_up)
        self.lb3_stats['acc_by_lb3_only'] += int(np.sum(acc & ~acc12))
        return acc


def rigorous_H(alpha, prec=128):
    """Arb enclosure of H(cos(alpha s)) = 2 - R,  R = [psi(0) + 2 int_0^1 t psi(t) dt] / Z^2, closed-form
    psi(t) = (1-t)cos(alpha t)/2 + sin(alpha(1-t))/(2 alpha),  Z = 2 sin(alpha/2)/alpha; the t-integral by
    Arb's rigorous acb.integral."""
    import flint
    from flint import arb, acb, fmpq
    old = flint.ctx.prec
    flint.ctx.prec = prec
    try:
        fa = Fraction(alpha)
        al = arb(fmpq(fa.numerator, fa.denominator))
        Z = 2 * (al / 2).sin() / al
        psi0 = arb(1) / 2 + al.sin() / (2 * al)
        A = acb(al)
        I = acb.integral(lambda t, _: t * (1 - t) * (A * t).cos() / 2 + t * (A * (1 - t)).sin() / (2 * A), 0, 1)
        R = (psi0 + 2 * I.real) / (Z * Z)
        return 2 - R
    finally:
        flint.ctx.prec = old


def aggregate_rigorous(alpha, c_claim, muinv, K, m=None, prec=128, H_exact=None):
    """Theorem G bound  p = (H - (B/A) tau)/(1 - B/m),  A = c(m-K+1), B = Phi_m(A), tau = mu(K-1)(m-K+1)/m,
    Phi_m(E) = E (E <= m/(m-1)), else 2 sqrt((m-1)E/m) - 1 + E/m; all in Arb from exact rationals and the Arb
    enclosure of H.  m: given, or the float optimum of localK.aggregate.  Returns (p_lower (arb), m, H (arb))."""
    import flint
    from flint import arb, fmpq
    old_prec = flint.ctx.prec
    flint.ctx.prec = prec
    H = rigorous_H(alpha, prec) if H_exact is None else arb(fmpq(H_exact.numerator, H_exact.denominator))
    c, mu = Fraction(c_claim), 1 / Fraction(muinv)
    if m is None:
        from localK import aggregate
        m = aggregate(float(H.mid()), float(c), float(mu), K)[1]
    Aq = c * (m - K + 1)
    A = arb(fmpq(Aq.numerator, Aq.denominator))
    if Aq <= Fraction(m, m - 1):
        Bv = A
    else:
        Bv = 2 * (arb(m - 1) * A / m).sqrt() - 1 + A / m
    tq = mu * (K - 1) * (m - K + 1) / m
    tau = arb(fmpq(tq.numerator, tq.denominator))
    p = (H - (Bv / A) * tau) / (1 - Bv / m)
    flint.ctx.prec = old_prec
    return p, m, H


def round_up_float(fr):
    f = float(fr)
    if Fraction(f) < fr:
        f = float(np.nextafter(f, np.inf))
    assert Fraction(f) >= fr
    return f


def certify(alpha, K, muinv, c_claim, backend='auto', prec=64, min_width=1e-10, pure=False, workers=1,
            chunk=50000, init_div=4, max_boxes=5e10, log_every=200, checkpoint=None, ckpt_every=2000,
            resume=False, verbose=True, engine='numpy', weights_file=None, lb3=False, sym=False, qp_sweeps=12,
            axis_rule='grad', window_file=None):
    from localK import span_matrix, cos_kernel
    PW = None
    if window_file:
        from polywin import PolyWindow
        PW = PolyWindow.from_json(window_file)
        fa = None
    else:
        fa = Fraction(alpha)
    fmuinv, fc = Fraction(muinv), Fraction(c_claim)
    W = None
    pattern_mode = False
    wfile_md5 = None
    if weights_file:
        import json
        js = json.load(open(weights_file))
        W = ([Fraction(x) for x in js['gam']], [Fraction(x) for x in js['mu']])
        assert len(W[0]) == len(spans(K)) and len(W[1]) == K - 1
        assert all(x >= 0 for x in W[0]) and all(x > 0 for x in W[1])
        if 'pattern' in js and 'base_gam' in js:   # X2 all-marks + Lemma D' weights (check copied verbatim from
            # X2_numerics/bnb_interval_w.py, md5 5859d7c7...):  gam'_{i,s} = gam_{s,i} m_i m_{i+s}
            mk = [int(ch) for ch in js['pattern']]; assert len(mk) == K and set(mk) <= {1, 2}
            base = [Fraction(x) for x in js['base_gam']]; assert len(base) == len(spans(K)) and all(x >= 0 for x in base)
            assert all(g == bq * mk[i] * mk[i + s] for g, bq, (i, s) in zip(W[0], base, spans(K)))
            for s_ in range(1, K):   # base weights: each pair at index distance s gets total weight exactly 2 (Lemma D')
                assert sum(bq for bq, (i, s) in zip(base, spans(K)) if s == s_) == 2
            assert base == [base[spans(K).index((K - s - 1 - i, s))] for (i, s) in spans(K)], "base weights not reversal-symmetric"
            assert W[1] == W[1][::-1], "mu not reversal-symmetric"
            print('X2 weight check passed: pattern', js['pattern'], flush=True)
            pattern_mode = True
        else:
            for s_ in range(1, K):   # each pair at index distance s gets total weight exactly 2 (Lemma D')
                assert sum(g for g, (i, s) in zip(W[0], spans(K)) if s == s_) == 2
        assert sum(W[1]) == (K - 1) / Fraction(muinv), "sum of mu_i must equal (K-1)/muinv"
        import hashlib
        wfile_md5 = hashlib.md5(open(weights_file, 'rb').read()).hexdigest()
    if workers > 1 and not pure and engine != 'numpy' and (W is not None or PW is not None):
        # (Oct 2026) the pool initialiser _winit builds its certifier without the weights and without the window,
        # so the workers would check another objective: refuse this configuration instead of running it.
        raise SystemExit('error: --workers > 1 with --engine scalar (hybrid mode) does not support --weights or '
                         '--window (the workers would use the default objective); use --workers 1 or --engine numpy')
    cert = IntervalCertifier(make_backend(backend, prec), alpha, K, muinv, c_claim, weights=W, polywin=PW)
    global _WEIGHTS
    _WEIGHTS = W
    bname, bprec = cert.B.name, cert.B.prec
    npe = NumpyIntervalLB(cert) if engine == 'numpy' else None
    if lb3:
        assert npe is not None, "LB3 needs the numpy engine"
        npe.use_lb3 = True
        npe.qp_sweeps = qp_sweeps
    if sym:
        assert W is not None, "--sym needs an explicit (symmetric) weights file"
        spl = spans(K)
        for (i, s), g in zip(spl, W[0]):          # gamma_(i,s) == gamma_(d-i-s, s) exactly
            assert W[0][spl.index((K - 1 - i - s, s))] == g, "weights not reversal-symmetric"
        assert all(W[1][i] == W[1][K - 2 - i] for i in range(K - 1)), "mu not reversal-symmetric"
    ckargs = (alpha if PW is None else 'poly:' + ','.join(str(c) for c in PW.cu), K, muinv, c_claim, bname, bprec, pure,
              engine + ('+lb3' if lb3 else '') + ('+sym' if sym else ''), wfile_md5)   # d8_9: weights md5 in ckpt key
    V, beta = span_matrix(K)
    # the float screen uses the SAME span ordering (s outer, i inner) as spans(K)
    assert [(int(np.argmax(r)), int(r.sum())) for r in V] == spans(K)
    mu = np.array([float(m) for m in cert.muvq])
    beta = np.array([float(g) for g in cert.gamq])
    k, kp = cos_kernel(float(fa)) if PW is None else PW.float_kernels()
    d = K - 1
    T = fc / min(cert.muvq)                          # domain threshold on sum g (exact rational): F >= min(mu) sum g
    T_up = round_up_float(T)                         # sum(c-h) >= T  <=>  sum(c-h) >= T_up (sum is a float)
    assert min_width >= 2.0 ** (-DYADIC_BITS + 2)
    # dyadic initial grid: cell width w0 = 2^e >= T/init_div, n cells cover [0, n w0] >= [0, T]
    e = int(np.ceil(np.log2(float(T) / init_div)))
    w0 = 2.0 ** e
    n0 = int(np.ceil(float(T) / w0))
    while Fraction(n0) * Fraction(w0) < T:
        n0 += 1
    assert (K - 1) * n0 * w0 < 2.0 ** (52 - DYADIC_BITS), "span sums would not be exact in float64"
    mids = (np.arange(n0) + 0.5) * w0
    hw = 0.5 * w0
    t0 = time.time()
    stats = dict(processed=0, domain=0, iv_checked=0, iv_accepted=0, iv_rejected=0, it=0)
    worst = (np.inf, None)
    if resume and checkpoint and os.path.exists(checkpoint):
        with open(checkpoint, 'rb') as f:
            ck = pickle.load(f)
        assert ck['args'] == ckargs, "checkpoint args differ"
        stack, stats, worst, t_prev = ck['stack'], ck['stats'], ck['worst'], ck['time']
        t0 -= t_prev
        if verbose:
            print(f"  resumed from {checkpoint}: processed={stats['processed']:.3e} "
                  f"stack_boxes={sum(len(s[0]) for s in stack):.3e}", flush=True)
    else:
        grids = np.meshgrid(*([mids] * d), indexing='ij')
        C0 = np.stack([g.ravel() for g in grids], axis=1)
        stack = [(C0, np.full_like(C0, hw))]
    pool = None
    if workers > 1 and not pure and npe is None:
        import multiprocessing as mp
        pool = mp.get_context('fork').Pool(workers, initializer=_winit,
                                           initargs=(bname, bprec, alpha, K, muinv, c_claim))
    scale = 2.0 ** DYADIC_BITS

    def result(ok, **kw):
        if pool is not None:
            pool.terminate()
        r = dict(ok=ok, **kw, processed=stats['processed'], worst=worst, time=time.time() - t0,
                 backend=bname, prec=bprec, engine=engine, mode='pure' if pure else 'hybrid',
                 iv_checked=stats['iv_checked'], iv_rejected=stats['iv_rejected'], domain_pruned=stats['domain'],
                 iv_time=round(stats.get('iv_time', 0.0), 3), kernel_cache=len(cert.cache),
                 lb3=lb3, sym=sym, acc_by_lb3_only=(npe.lb3_stats['acc_by_lb3_only'] if npe is not None else 0))
        return r

    while stack:
        C, Hh = stack.pop()
        if len(C) > chunk:
            stack.append((C[chunk:], Hh[chunk:]))
            C, Hh = C[:chunk], Hh[:chunk]
        stats['processed'] += len(C)
        # exact-dyadic invariant (makes all float bookkeeping below exact)
        assert np.all(np.floor(C * scale) == C * scale) and np.all(np.floor(Hh * scale) == Hh * scale)
        assert Hh.min() >= 2.0 ** (-DYADIC_BITS + 1) and np.all(C - Hh >= 0)
        # exact domain pruning
        S = np.sum(C - Hh, axis=1)
        keep = S < T_up
        if sym:                                  # exact dyadic test: box entirely in {g_0 < g_{d-1}}
            keep &= ~((C[:, 0] + Hh[:, 0]) < (C[:, -1] - Hh[:, -1]))
        stats['domain'] += int(np.sum(~keep))
        C, Hh, S = C[keep], Hh[keep], S[keep]
        if len(C) == 0:
            continue
        LBf, Fcf, grad = float_bounds(C, Hh, V, beta, mu, k, kp, (C - Hh) @ mu)
        jm = int(np.argmin(Fcf))
        if Fcf[jm] < worst[0]:
            worst = (float(Fcf[jm]), C[jm].copy())
            FcI = cert.F_centre(C[jm].tolist())
            if cert.B.lt(FcI, cert.c):
                return result(False, reason='counterexample (rigorous)', F=cert.B.mid(FcI), g=C[jm])
        if (pure or lb3) and npe is not None:
            tiv = time.perf_counter()
            acc = npe.accept(C, Hh)
            stats['iv_time'] = stats.get('iv_time', 0.0) + time.perf_counter() - tiv
            stats['iv_checked'] += len(C)
        elif pure:
            acc = np.zeros(len(C), dtype=bool)
            for nb in range(len(C)):
                acc[nb], cex, _ = cert.box(C[nb].tolist(), Hh[nb].tolist())
                if cex:
                    return result(False, reason='counterexample (rigorous)', g=C[nb])
            stats['iv_checked'] += len(C)
        else:
            cand = LBf > fc.numerator / fc.denominator      # float screen: candidates for acceptance
            idx = np.nonzero(cand)[0]
            acc = np.zeros(len(C), dtype=bool)
            if len(idx):
                tiv = time.perf_counter()
                if npe is not None:
                    acc[idx] = npe.accept(C[idx], Hh[idx])
                elif pool is not None:
                    parts = np.array_split(idx, workers * 4)
                    res = pool.map(_wcheck, [(C[p], Hh[p]) for p in parts if len(p)])
                    acc[np.concatenate([p for p in parts if len(p)])] = np.concatenate(res)
                else:
                    for nb in idx:
                        acc[nb] = cert.box(C[nb].tolist(), Hh[nb].tolist())[0]
                stats['iv_time'] = stats.get('iv_time', 0.0) + time.perf_counter() - tiv
                stats['iv_checked'] += len(idx)
                stats['iv_rejected'] += int(len(idx) - acc[idx].sum())
        stats['iv_accepted'] += int(acc.sum())
        bad = ~acc
        C, Hh, grad = C[bad], Hh[bad], grad[bad]
        if len(C) == 0:
            continue
        if np.min(Hh.max(axis=1)) < min_width:
            return result(False, reason='min width reached')
        if axis_rule == 'loss' and lb3:
            g2 = npe.last_score[bad] + Hh * 1e-3
        elif axis_rule in ('grad', 'loss'):
            g2 = np.abs(grad) * Hh + Hh * 1e-3
        else:                                     # 'wide': widest side, ties/gradient as secondary
            g2 = Hh * (1.0 + 1e-3 * np.abs(grad) / (np.abs(grad).max(axis=1, keepdims=True) + 1e-300))
        ax = np.argmax(g2, axis=1)
        ii = np.arange(len(C))
        C1, C2, H1 = C.copy(), C.copy(), Hh.copy()
        H1[ii, ax] *= 0.5                               # exact
        C1[ii, ax] -= H1[ii, ax]                        # exact (dyadic)
        C2[ii, ax] += H1[ii, ax]
        stack.append((np.concatenate([C1, C2]), np.concatenate([H1, H1])))
        stats['it'] += 1
        it = stats['it']
        if verbose and it % log_every == 0:
            print(f"  it={it} processed={stats['processed']:.3e} stack_boxes={sum(len(s[0]) for s in stack):.3e} "
                  f"min centre F={worst[0]:.7f} t={time.time()-t0:.0f}s iv_checked={stats['iv_checked']:.3e} "
                  f"iv_rejected={stats['iv_rejected']}", flush=True)
        if checkpoint and it % ckpt_every == 0:
            tmp = checkpoint + '.tmp'
            with open(tmp, 'wb') as f:
                pickle.dump(dict(args=ckargs, stack=stack, stats=stats,
                                 worst=worst, time=time.time() - t0), f, protocol=4)
            os.replace(tmp, checkpoint)
        if stats['processed'] > max_boxes:
            return result(False, reason='budget')
    if checkpoint and os.path.exists(checkpoint):
        os.remove(checkpoint)
    r = result(True)
    if pattern_mode:          # d8_9: Theorem G is not the all-marks aggregation; skip it
        return r
    try:
        p, m, H = aggregate_rigorous(alpha, c_claim, muinv, K, H_exact=(PW.H_exact() if PW is not None else None))
        r['theoremG'] = dict(m=m, H=H.str(20), p_lower=float(p.lower()), p=p.str(15))
    except ImportError:
        pass
    return r


if __name__ == '__main__':
    if not __debug__:   # (Oct 2026) many checks of this script are assert statements
        sys.exit('run without -O / PYTHONOPTIMIZE: the checks of this script are assert statements')
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('alpha'); ap.add_argument('K', type=int); ap.add_argument('muinv'); ap.add_argument('c_claim')
    ap.add_argument('--backend', default='auto', choices=['auto', 'flint', 'mpmath'])
    ap.add_argument('--prec', type=int, default=64)
    ap.add_argument('--engine', default='numpy', choices=['numpy', 'scalar'],
                    help='numpy: vectorised outward-rounded float64 intervals (kernel from the backend); '
                         'scalar: every LB operation in the backend (Arb / mpmath.iv)')
    ap.add_argument('--min-width', type=float, default=1e-10)
    ap.add_argument('--pure', action='store_true', help='interval-evaluate every box (no float screen)')
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--chunk', type=int, default=50000)
    ap.add_argument('--log-every', type=int, default=200)
    ap.add_argument('--checkpoint', default=None)
    ap.add_argument('--ckpt-every', type=int, default=2000)
    ap.add_argument('--resume', action='store_true')
    ap.add_argument('--max-boxes', type=float, default=5e10)
    ap.add_argument('--weights', default=None, help='JSON {gam: [fractions in spans(K) order], mu: [K-1 fractions]}')
    ap.add_argument('--lb3', action='store_true', help='add the convex-underestimator bound LB3 (all boxes interval-checked)')
    ap.add_argument('--sym', action='store_true', help='reversal-symmetry reduction (symmetric weights asserted)')
    ap.add_argument('--qp-sweeps', type=int, default=12)
    ap.add_argument('--axis', default='grad', choices=['grad', 'wide', 'loss'])
    ap.add_argument('--window', default=None, help='polynomial window JSON (polywin.py); alpha is then only a label')
    a = ap.parse_args()
    print(f"bnb_interval: alpha={a.alpha} K={a.K} mu=1/{a.muinv} c_claim={a.c_claim} backend={a.backend} "
          f"prec={a.prec} engine={a.engine} mode={'pure' if a.pure else 'hybrid'} workers={a.workers} lb3={a.lb3} "
          f"sym={a.sym} axis={a.axis}", flush=True)
    res = certify(a.alpha, a.K, a.muinv, a.c_claim, backend=a.backend, prec=a.prec, min_width=a.min_width,
                  pure=a.pure, workers=a.workers, chunk=a.chunk, log_every=a.log_every, checkpoint=a.checkpoint,
                  ckpt_every=a.ckpt_every, resume=a.resume, max_boxes=a.max_boxes, engine=a.engine,
                  weights_file=a.weights, lb3=a.lb3, sym=a.sym, qp_sweeps=a.qp_sweeps, axis_rule=a.axis,
                  window_file=a.window)
    print(res)
    sys.exit(0 if res.get('ok') is True else 1)   # (Oct 2026) exit status 0 only for a certified claim
