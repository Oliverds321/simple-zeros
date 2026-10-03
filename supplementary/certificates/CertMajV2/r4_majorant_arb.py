"""d7_6 R4: Arb (python-flint) certificate of the delta = 1 Beurling-Selberg-type majorant of d6_6b (b10).
B'(s) = h sinc^2(pi h s) P'(s),  P'(s) = beta_0 + sum_{j=1}^{59} 2 beta_j cos(2 pi j h s),  h = 1/60,
beta_j = the 60 doubles in d6_6b_numerics/majorant_delta1_beta.npy (taken EXACTLY as binary64 rationals; beta_0 includes eta = 1e-3).
Claims certified (interval arithmetic, adaptive bisection, centered form P(I) in P(m) + P'(I)[-r,r]):
 (a) P'(s) > 0 on [0, 30]  (P' even, 60-periodic)  =>  B' >= 0 on R;
 (b) B'(s) - f(s) > 0 on [0, 1/2], f(s) = cos(8s/5)/Z, Z = 2 sin(4/5)/(8/5)  (so int_{-1/2}^{1/2} f = 1)   =>  B' >= f 1_{[-1/2,1/2]} on R;
 (c) supp B'^ in [-1, 1]: structural (B'^(t) = sum_j beta_j Lambda((t - j h)/h), |j| <= 59, Lambda = unit hat) — checked: 59 h + h = 1;
 (d) int B' = B'^(0) = beta_0 (exact double) ;  2 beta_0 < s = 2 + sqrt(2(1 - a1)), a1 = 0.01280197.
Negative controls: beta_0 lowered by d in {1.2e-3, 2e-3}: (b) must FAIL with a certified negative value g(s*) < 0 at a point s*.
Usage: python r4_majorant_arb.py"""
import sys, os, time, numpy as np
from flint import arb, ctx
ctx.prec = 106
BETA = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'majorant_delta1_beta.npy'))
NH = 60
PI = arb.pi()
h = arb(1) / NH
AL = arb(8) / 5
Z = 2 * (arb(4) / 5).sin() / AL
def coefs(beta0_shift=0.0):
    b = [arb(float(x)) for x in BETA]            # exact binary64 values
    if beta0_shift: b[0] = b[0] - arb(beta0_shift)  # control: shift is a double, exact
    return b[0], [2 * b[j] for j in range(1, NH)]
def P_and_dP(c0, c, s_mid, s_ball):
    # P(mid) and P'(ball); argument 2 pi j s /60 = pi * (j s / 30)
    Pm = c0; dP = arb(0)
    for j in range(1, NH):
        t = arb(j) / 30
        Pm += c[j - 1] * (t * s_mid).cos_pi()
        dP -= c[j - 1] * (PI * t) * (t * s_ball).sin_pi()
    return Pm, dP
def check_a(c0, c, lo=0.0, hi=30.0, w0=0.01, maxdepth=40):
    stack = [(lo + k * w0, min(lo + (k + 1) * w0, hi)) for k in range(int(round((hi - lo) / w0)))]
    nev = 0; worst = None
    while stack:
        a, b = stack.pop()
        m = (a + b) / 2; r = (b - a) / 2
        mid = arb(m); ball = arb(m, r)   # m, r doubles (exact); ball = [a, b] exactly up to rounding of r (outward in arb)
        Pm, dP = P_and_dP(c0, c, mid, ball); nev += 1
        enc = Pm + dP * arb(0, r)
        if enc > 0:
            lb = float(enc.lower())
            if worst is None or lb < worst[0]: worst = (lb, m, float(Pm.mid()))
            continue
        if Pm < 0: return False, nev, ("P(%.9g) certified < 0: %s" % (m, Pm.str(5)))
        if r < 1e-12: return False, nev, "undecided at %.12g" % m
        stack.append((a, m)); stack.append((m, b))
    return True, nev, worst
def g_mid_dg(c0, c, s_mid, s_ball, rad):
    # g = h S^2 P - cos(AL s)/Z, S = sinc(pi h s); g' = h (2 S S' P + S^2 P') + AL sin(AL s)/Z
    # S' = pi h sinc'(pi h s), |sinc'(x)| <= |x|/3 (alternating series, |x| <= 1)
    Pm, dP = P_and_dP(c0, c, s_mid, s_ball)
    Sm = (PI * h * s_mid).sinc()
    gm = h * Sm * Sm * Pm - (AL * s_mid).cos() / Z
    # P on ball (for the S' term)
    Pb = Pm + dP * arb(0, rad)
    Sb = (PI * h * s_ball).sinc()
    xmax = float((PI * h * (abs(s_ball))).upper())
    Sp = PI * h * arb(0, xmax / 3 * (1 + 1e-12))
    dg = h * (2 * Sb * Sp * Pb + Sb * Sb * dP) + AL * (AL * s_ball).sin() / Z
    return gm, dg
def check_b(c0, c, lo=0.0, hi=0.5, w0=1e-3):
    stack = [(lo + k * w0, min(lo + (k + 1) * w0, hi)) for k in range(int(round((hi - lo) / w0)))]
    nev = 0; worst = None; best_upper = None
    while stack:
        a, b = stack.pop()
        m = (a + b) / 2; r = (b - a) / 2
        gm, dg = g_mid_dg(c0, c, arb(m), arb(m, r), r); nev += 1
        up = float(gm.upper())
        if best_upper is None or up < best_upper[0]: best_upper = (up, m)
        enc = gm + dg * arb(0, r)
        if enc > 0:
            lb = float(enc.lower())
            if worst is None or lb < worst[0]: worst = (lb, m)
            continue
        if gm < 0: return False, nev, ("g(%.12g) certified < 0: %s" % (m, gm.str(6)))
        if r < 1e-13: return False, nev, "undecided at %.12g" % m
        stack.append((a, m)); stack.append((m, b))
    return True, nev, (worst, best_upper)
if __name__ == "__main__":
    t0 = time.time()
    c0, c = coefs()
    a1 = arb(1280197) / 10**8; cc = 2 * (1 - a1); s_thr = 2 + cc.sqrt()
    print("prec = %d bits; beta_0 (exact double) = %.17g ; I' = int B' = beta_0 ; 2 I' = %s ; s = %s ; 2I' < s : %s"
          % (ctx.prec, float(BETA[0]), (2 * c0).str(12), s_thr.str(12), (2 * c0 < s_thr)))
    print("(c) supp: hat nodes j/60, j = 0..59, each hat of half-width 1/60 -> support of B'^ in [-60/60, 60/60] = [-1, 1]  [structural]")
    ok, nev, info = check_a(c0, c)
    print("(a) P' > 0 on [0,30]: %s  (%d interval evaluations; certified lower bound of min over cells = %s)" % ("CERTIFIED" if ok else "FAIL", nev, info), flush=True)
    allok = ok and bool(2 * c0 < s_thr)   # (Oct 2026) overall verdict for the exit status
    ok, nev, info = check_b(c0, c)
    if ok:
        print("(b) B' - f > 0 on [0,1/2]: %s  (%d evaluations; min certified cell lower bound %.4e at s~%.6f ; smallest certified upper value g(s) <= %.4e at s=%.6f)"
              % ("CERTIFIED" if ok else "FAIL", nev, info[0][0], info[0][1], info[1][0], info[1][1]), flush=True)
    else:   # (Oct 2026) on failure check_b returns a message (a certified negative value or an undecided cell)
        print("(b) B' - f > 0 on [0,1/2]: FAIL  (%d evaluations; %s)" % (nev, info), flush=True)
    allok = allok and ok
    for d in (1.2e-3, 2e-3):
        c0n, cn = coefs(d)
        ok, nev, info = check_b(c0n, cn)
        print("NEGATIVE CONTROL beta_0 - %.1e (int B = %.7f): (b) %s after %d evaluations: %s" % (d, float((c0n).mid()), "PASSES (control broken!)" if ok else "FAILS as required", nev, info), flush=True)
        allok = allok and not ok
    print("elapsed %.1f s" % (time.time() - t0))
    sys.exit(0 if allok else 1)   # (Oct 2026) exit status 0 only if all checks pass and both controls fail
