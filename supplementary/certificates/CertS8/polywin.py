"""d6_5: even polynomial window v(s) = sum_j c_j (2s)^{2j} on [-1/2, 1/2] with exact rational c_j (c_0 = 1).
Provides: exact rational Z = int v, exact rational H = 2 - R (R = [int v^2 + iint |x-y| v(x)v(y)]/Z^2, sympy exact);
a rigorous positivity check (Arb on a partition of u = (2s)^2 in [0,1]); the moment bound M3 >= sup|k'''|
(= 8 pi^3 int |s|^3 v / Z); Arb enclosures of k, k', k'' at an exact point x; float (numpy) k, k' for the
heuristic float screen.
Kernel: k(x) = C(v, w)/Z, k'(x) = -2 pi S(s v, w)/Z, k''(x) = -4 pi^2 C(s^2 v, w)/Z with w = 2 pi x, where
C(q,w) = int q(s) cos(ws) ds, S(q,w) = int q(s) sin(ws) ds over [-1/2,1/2]:
  |w| >= W0: closed forms (repeated integration by parts, finite for polynomials)
     even q: C = 2 sum_j (-1)^j [q^(2j)(1/2) sin(w/2)/w^(2j+1) + q^(2j+1)(1/2) cos(w/2)/w^(2j+2)]
     odd  q: S = 2 sum_j (-1)^j [-q^(2j)(1/2) cos(w/2)/w^(2j+1) + q^(2j+1)(1/2) sin(w/2)/w^(2j+2)]
  |w| <  W0: Taylor series with exact rational moments and the rigorous tail
     |R_N| <= |w|^N / N! * max|q| * 2 (1/2)^(N+1)/(N+1)   (N = 60 or 61 here).
"""
import json
import math
from fractions import Fraction
import numpy as np


class Poly:
    """polynomial in s with Fraction coefficients a[k] s^k"""
    def __init__(self, a):
        a = [Fraction(x) for x in a]
        while len(a) > 1 and a[-1] == 0:
            a.pop()
        self.a = a

    def der(self):
        return Poly([k * self.a[k] for k in range(1, len(self.a))] or [0])

    def is_zero(self):
        return all(c == 0 for c in self.a)

    def __call__(self, s):
        s = Fraction(s)
        r = Fraction(0)
        for c in reversed(self.a):
            r = r * s + c
        return r

    def mulx(self, k=1):
        return Poly([Fraction(0)] * k + self.a)

    def moment(self, m):
        """int_{-1/2}^{1/2} q(s) s^m ds (exact)"""
        tot = Fraction(0)
        for k, c in enumerate(self.a):
            e = k + m
            if e % 2 == 0:
                tot += c * 2 * Fraction(1, 2) ** (e + 1) / (e + 1)
        return tot

    def absmax_bound(self):
        return sum(abs(c) * Fraction(1, 2) ** k for k, c in enumerate(self.a))


class PolyWindow:
    W0 = 3.0

    def __init__(self, coeffs_u):
        """coeffs_u: [c_0, c_1, ...] with v = sum c_j (2s)^{2j}"""
        self.cu = [Fraction(x) for x in coeffs_u]
        a = [Fraction(0)] * (2 * len(self.cu) - 1)
        for j, c in enumerate(self.cu):
            a[2 * j] = c * 4 ** j
        self.v = Poly(a)
        self.Z = self.v.moment(0)
        self.q0 = self.v                 # even, for k
        self.q1 = self.v.mulx(1)         # odd,  for k'
        self.q2 = self.v.mulx(2)         # even, for k''
        tot = Fraction(0)                # int |s|^3 v = 2 int_0^{1/2} s^3 v(s) ds   (v >= 0 checked separately)
        for k, c in enumerate(self.v.a):
            tot += c * Fraction(1, 2) ** (k + 4) / (k + 4)
        self.int_abs_s3_v = 2 * tot
        self._arb_ready = False

    @classmethod
    def from_json(cls, fn):
        return cls(json.load(open(fn))['coeffs_u'])

    def float_v(self, s):
        u = (2 * np.asarray(s, float)) ** 2
        return sum(float(c) * u ** j for j, c in enumerate(self.cu))

    # ---------------- exact H ----------------
    def H_exact(self):
        import sympy as sp
        x, y = sp.symbols('x y')
        half = sp.Rational(1, 2)
        vx = sum(sp.Rational(c.numerator, c.denominator) * (2 * x) ** (2 * j) for j, c in enumerate(self.cu))
        vy = vx.subs(x, y)
        Z = sp.integrate(vx, (x, -half, half))
        v2 = sp.integrate(sp.expand(vx ** 2), (x, -half, half))
        inner = sp.integrate(sp.expand((x - y) * vx * vy), (y, -half, x))
        dbl = 2 * sp.integrate(sp.expand(inner), (x, -half, half))
        R = (v2 + dbl) / Z ** 2
        H = sp.nsimplify(2 - R)
        assert Fraction(int(sp.numer(Z)), int(sp.denom(Z))) == self.Z
        return Fraction(int(sp.numer(H)), int(sp.denom(H)))

    # ---------------- rigorous positivity ----------------
    def positive_arb(self, n=4096, prec=128):
        """rigorous lower bound of min v on [-1/2,1/2]: Arb on n subintervals of u in [0,1] (v = poly in u)"""
        import flint
        from flint import arb, fmpq
        old = flint.ctx.prec
        flint.ctx.prec = prec
        try:
            cs = [arb(fmpq(c.numerator, c.denominator)) for c in self.cu]
            lo = None
            for i in range(n):
                u = arb(fmpq(2 * i + 1, 2 * n), fmpq(1, 2 * n))       # ball = [i/n, (i+1)/n]
                val = arb(0)
                for c in reversed(cs):
                    val = val * u + c
                l = float(val.lower())
                lo = l if lo is None else min(lo, l)
            return lo
        finally:
            flint.ctx.prec = old

    # ---------------- Arb kernel ----------------
    def arb_setup(self):
        from flint import arb, fmpq
        self._arb = arb
        q = lambda f: arb(fmpq(f.numerator, f.denominator))
        self.aZ = q(self.Z)
        self.api = arb.pi()
        self._d = {}
        for name, P in (('q0', self.q0), ('q1', self.q1), ('q2', self.q2)):
            ds = []
            D = P
            while not D.is_zero():
                ds.append(q(D(Fraction(1, 2))))
                D = D.der()
            moms = [q(P.moment(m)) for m in range(130)]
            self._d[name] = (ds, moms, q(P.absmax_bound()))
        self._arb_ready = True
        self.aM3 = 8 * self.api ** 3 * q(self.int_abs_s3_v / self.Z)

    def _closed(self, ds, w, even):
        arb = self._arb
        sn, cs = (w / 2).sin(), (w / 2).cos()
        tot = arb(0)
        wp = w
        sign = 1
        for j in range(0, len(ds), 2):
            t = (ds[j] * sn if even else -ds[j] * cs) / wp
            wp = wp * w
            if j + 1 < len(ds):
                t = t + (ds[j + 1] * cs if even else ds[j + 1] * sn) / wp
            wp = wp * w
            tot = tot + sign * t
            sign = -sign
        return 2 * tot

    def _C_even(self, name, w):
        arb = self._arb
        ds, moms, qmax = self._d[name]
        wm = abs(float(w.mid()))
        if wm >= self.W0:
            return self._closed(ds, w, True)
        N = 30                                   # terms n < N: sum (-1)^n w^{2n}/(2n)! M(2n); tail from index 2N
        tot = arb(0)
        term = arb(1)
        w2 = w * w
        for n in range(N):
            tot = tot + term * moms[2 * n]
            term = -term * w2 / ((2 * n + 1) * (2 * n + 2))
        wa = wm + float(w.rad())
        tail = (wa ** (2 * N)) / float(math.factorial(2 * N)) * 2 * 0.5 ** (2 * N + 1) / (2 * N + 1)
        return tot + qmax * arb(0, tail * 2 + 1e-300)

    def _S_odd(self, name, w):
        arb = self._arb
        ds, moms, qmax = self._d[name]
        wm = abs(float(w.mid()))
        if wm >= self.W0:
            return self._closed(ds, w, False)
        N = 30
        tot = arb(0)
        term = w
        w2 = w * w
        for n in range(N):
            tot = tot + term * moms[2 * n + 1]
            term = -term * w2 / ((2 * n + 2) * (2 * n + 3))
        wa = wm + float(w.rad())
        tail = (wa ** (2 * N + 1)) / float(math.factorial(2 * N + 1)) * 2 * 0.5 ** (2 * N + 2) / (2 * N + 2)
        return tot + qmax * arb(0, tail * 2 + 1e-300)

    def arb_kernel(self, x):
        """x: arb (exact point).  Returns (k, k', k'') enclosures."""
        if not self._arb_ready:
            self.arb_setup()
        w = 2 * self.api * x
        kk = self._C_even('q0', w) / self.aZ
        kd = -2 * self.api * self._S_odd('q1', w) / self.aZ
        k2 = -4 * self.api ** 2 * self._C_even('q2', w) / self.aZ
        return kk, kd, k2

    # ---------------- float kernel (heuristic screen only) ----------------
    def float_kernels(self, n=128, xmax=64.0):
        from numpy.polynomial.legendre import leggauss
        xg, wg = leggauss(n)
        s = 0.5 * xg
        w = 0.5 * wg * self.float_v(s) / float(self.Z)
        ts = 2 * np.pi * s
        h = 1.0 / 512
        X = np.arange(0, xmax + 2 * h, h)
        Kt = np.cos(np.multiply.outer(X, ts)) @ w
        Dt = -np.sin(np.multiply.outer(X, ts)) @ (w * ts)
        D2 = -np.cos(np.multiply.outer(X, ts)) @ (w * ts * ts)

        def herm(x, F0, F1):
            x = np.asarray(x, float)
            i = np.clip((x / h).astype(np.int64), 0, len(X) - 2)
            t = x / h - i
            h00 = (1 + 2 * t) * (1 - t) ** 2
            h10 = t * (1 - t) ** 2
            h01 = t * t * (3 - 2 * t)
            h11 = t * t * (t - 1)
            return h00 * F0[i] + h10 * h * F1[i] + h01 * F0[i + 1] + h11 * h * F1[i + 1]
        return (lambda x: herm(x, Kt, Dt)), (lambda x: herm(x, Dt, D2))
