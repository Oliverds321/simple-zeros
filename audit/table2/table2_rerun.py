# table2_rerun.py -- a MODIFIED COPY of the paper's table2_check.py /
# budget_q.py design model (the shipped scripts are untouched; copies sit in this directory).
# Changes from budget_q.design, all switchable:
#   zone   : 'envelope' = the script's P(C,1) - P(C,a) (profile re-optimised at each a)
#            'fixed'    = the FIXED degree-6 design profile's zone cost (C-1)*2*int_a^1 alpha psi_{v_C}
#   c_buf  : 6 (the sharp zero density, the script) | 'proved' = 3*bufferRowProved(2A0)
#            = 36 pi A0 (1 + log 4T/LL) D0/T, A0 = EFChi.A0 = 10/log(95/84)
#   ends   : ('flat', 3.7e5) = the A2/A6 figure | ('cprime', c) = C1ends(c) + C2ends(c)(1+log L) per Q
#   lam    : 'reopt' (the script's Lspl(a)) | 'star' (the fixed profile's lam* = 1.2507321515)
#   P0     : 'opt' (0.7212835668) | 0.7212 (the certified constant)
#   rebalance : True = minimise c_ramp w/L + c_buf D0/T jointly (the script's procedure, new c_buf)
#               False = keep the (w, D0) of the sharp-buffer design and re-price
# ASCII-only output to table2_rerun.log.
import sys, os
from math import log, pi, sqrt, e, exp
import numpy as np
from numpy.polynomial import polynomial as Pn
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fb, budget_q as bd

out = []
def P(*a): out.append(" ".join(str(x) for x in a))

lq = lambda n: n*log(10)
C_QQ = pi**4/18
A_G, B_G, c4 = bd.A_G, bd.B_G, bd.c4
S_LIN = bd.S_LIN; REC = bd.REC; DPDLOGC = bd.DPDLOGC
A0 = 10/log(95/84)
LAMSTAR = 1.2507321515
PCERT = 0.7212
# the landed qle profile p = 1 + d2 t^2 + d4 t^4 + d6 t^6 on |t| <= lam*/2
cQ = [1.0, 0.0, -81257/125000, 0.0, 3458583/1000000, 0.0, -3669851/200000]

def make_psi(c, lam):
    R = lam/2
    p2 = Pn.polymul(c, c)
    I = Pn.polyval(R, Pn.polyint(p2)) - Pn.polyval(-R, Pn.polyint(p2))
    v = [x/I for x in p2]
    def psi(alpha):
        if alpha >= lam: return 0.0
        shift = [-alpha, 1.0]; q = [0.0]
        for k in range(len(v)-1, -1, -1):
            q = Pn.polyadd(Pn.polymul(q, shift), [v[k]])
        F = Pn.polyint(Pn.polymul(v, q))
        return float(Pn.polyval(R, F) - Pn.polyval(alpha - R, F))
    return psi
PSI_Q = make_psi(cQ, LAMSTAR)
def zone_fixed(a, C=C_QQ, psi=PSI_Q):
    return (C-1)*2*float(mp.quad(lambda x: mp.mpf(float(x)*psi(float(x))), [a, 1]))

def C1ends(c): return 4*(90 + 32*c**2)
def CN2(c): return 100*(1 + abs(log(c)) + abs(c))
def C2ends(c): return 2*(8 + 4*max(0.0, log(c)) + 7*c)*CN2(c)

def opt_ramp_buffer(L, LL, T, c_ramp, c_buf, nw=500):
    D0max = T/3.0; D0min = 10.0*L
    if D0min >= D0max: return None
    def feas(w, D0):
        return (w >= 1.0) and (8*w <= L*(1+1e-12)) and (D0min <= D0 <= D0max*(1+1e-12)) \
            and (bd.closing_margin(w, D0, L, LL, T) >= 0.0)
    best = None
    for w in np.exp(np.linspace(log(1.0), log(L/8), nw)):
        if not feas(w, D0max): continue
        lo, hi = D0min, D0max
        for _ in range(200):
            mid = 0.5*(lo+hi)
            if feas(w, mid): hi = mid
            else: lo = mid
        cost = c_ramp*w/L + c_buf*hi/T
        if best is None or cost < best[2]: best = (w, hi, cost)
    return best

def design(logQ, r=3.5, K=3.0, c_ramp=6.0, zone='fixed', c_buf='proved', ends=('flat', 3.7e5),
           lam='star', P0='cert', rebalance=True, nw=500):
    Pspl, Lspl, Popt = bd.curve(C_QQ)
    T = logQ**r; l = log(T) - log(2*pi); LL = logQ + l
    if T < 10*LL*log(LL): return None
    dp = K*log(LL)/LL
    a = (1-dp)*(1 - l/LL)
    lamv = float(Lspl(a)) if lam == 'reopt' else LAMSTAR
    L = lamv*LL
    zrow = (Popt - float(Pspl(a))) if zone == 'envelope' else zone_fixed(a)
    cb = 6.0 if c_buf == 6 else 36*pi*A0*(1 + log(4*T)/LL)
    if rebalance:
        got = opt_ramp_buffer(L, LL, T, c_ramp, cb, nw=nw)
    else:
        got = opt_ramp_buffer(L, LL, T, c_ramp, 6.0, nw=nw)
    if got is None: return None
    w, D0, _ = got
    if ends[0] == 'flat': cends = ends[1]
    else: cends = C1ends(ends[1]) + C2ends(ends[1])*(1 + log(L))
    rows = dict(zone=zrow, ramp=c_ramp*w/L, buffer=cb*D0/T, ends=cends*LL*log(LL)/T)
    rows['minor'] = (S_LIN*0.5/LL
                     + 1.3*7.7*sqrt(C_QQ*log(T*LL)/(T*LL))
                     + DPDLOGC*2.763953*sqrt(log(L)/(T*L))
                     + 0.35*C_QQ*2.763953*sqrt(log(L)/(T*L))
                     + DPDLOGC*0.2/T
                     + 3*log(LL)**2/L**2
                     + DPDLOGC*exp((lamv-2)*logQ))
    tot = sum(rows.values())
    p0 = Popt if P0 == 'opt' else PCERT
    return dict(logQ=logQ, T=T, LL=LL, l=l, a=a, lam=lamv, L=L, w=w, D0=D0, wD0=w*D0, rows=rows,
                total=tot, P_eff=p0-tot, P0=p0, cends=cends, cb=cb,
                margin=bd.closing_margin(w, D0, L, LL, T))

def threshold(target, lo=20.0, hi=1e12, **kw):
    d = design(hi, **kw)
    if d is None or d['P_eff'] <= target: return None
    for _ in range(90):
        mid = sqrt(lo*hi)
        d = design(mid, **kw)
        if d is not None and d['P_eff'] > target: hi = mid
        else: lo = mid
    return hi

def run(label, **kw):
    P("")
    P("=== %s ===" % label)
    P("  kw: %s" % kw)
    hdr = "%9s %7s %7s %8s %8s %8s %10s %8s %10s | %9s %7s %10s %7s"
    P(hdr % ("Q", "LL", "a", "zone", "ramp", "buffer", "ends", "minor", "TOTAL", "P_eff", "w", "D0", "wD0/LL2"))
    res = {}
    for n in (25, 100, 300, 1000, 3000, 10000):
        d = design(lq(n), **kw); res[n] = d
        if d is None: P("  1e%d: infeasible" % n); continue
        rr = d['rows']
        P(hdr % ("1e%d" % n, "%.1f" % d['LL'], "%.4f" % d['a'], "%.4f" % rr['zone'], "%.4f" % rr['ramp'],
                 "%.4f" % rr['buffer'], "%.4g" % rr['ends'], "%.4f" % rr['minor'], "%.4g" % d['total'],
                 "%+.4f" % d['P_eff'], "%.2f" % d['w'], "%.3e" % d['D0'], "%.2f" % (d['wD0']/d['LL']**2)))
    for tgt, name in ((0.0, "non-vacuous"), (0.5, "P_eff>0.5"), (REC, "P_eff>record (0.6725)"), (2/3., "P_eff>2/3")):
        x = threshold(tgt, **kw)
        P("   %-24s from 1e%s" % (name, ("%.0f" % (x/log(10))) if x else "(>1e12: none)"))
    return res

if __name__ == "__main__":
    P("gates:")
    fb.gates(verbose=False)
    P("  (fb.gates ran at import; see stdout)")
    P("A0 = %.6f, 36 pi A0 = %.3f, lam* = %.10f, P_cert = %.4f, zone_fixed(0.858) = %.5f" % (A0, 36*pi*A0, LAMSTAR, PCERT, zone_fixed(0.858)))
    P("C_ends(c', L) at 1e100 (L = %.3f): c'=4: %.4e ; c'=31.2649: %.4e ; c'=548.0857: %.4e" % (LAMSTAR*(lq(100)+log(lq(100)**3.5)-log(2*pi)),
        C1ends(4)+C2ends(4)*(1+log(LAMSTAR*(lq(100)+log(lq(100)**3.5)-log(2*pi)))),
        C1ends(31.26487817)+C2ends(31.26487817)*(1+log(LAMSTAR*(lq(100)+log(lq(100)**3.5)-log(2*pi)))),
        C1ends(548.0857)+C2ends(548.0857)*(1+log(LAMSTAR*(lq(100)+log(lq(100)**3.5)-log(2*pi))))))

    S0 = run("S0  REPRODUCE THE PRINTED A6 TABLE: envelope zone, buffer 6D0/T, ends 3.7e5 flat, lam reopt, P0 = optimum",
             zone='envelope', c_buf=6, ends=('flat', 3.7e5), lam='reopt', P0='opt')
    S0b = run("S0b as S0 but lam = lam* fixed and P0 = 0.7212 (isolates the lam/P0 convention change)",
              zone='envelope', c_buf=6, ends=('flat', 3.7e5), lam='star', P0='cert')
    S1z = run("S1z fixed-profile zone only (buffer 6, ends 3.7e5, lam*, P0 = 0.7212)",
              zone='fixed', c_buf=6, ends=('flat', 3.7e5), lam='star', P0='cert')
    S1b = run("S1b proved buffer only, rebalanced (envelope zone, ends 3.7e5, lam*, P0 = 0.7212)",
              zone='envelope', c_buf='proved', ends=('flat', 3.7e5), lam='star', P0='cert')
    S1 = run("S1  TASK 2 MAIN: fixed-profile zone + proved buffer (rebalanced) + ends 3.7e5 flat (A2), lam*, P0 = 0.7212",
             zone='fixed', c_buf='proved', ends=('flat', 3.7e5), lam='star', P0='cert')
    S1n = run("S1n as S1 but NOT rebalanced (old (w, D0) of the sharp-buffer design, re-priced at the proved buffer)",
              zone='fixed', c_buf='proved', ends=('flat', 3.7e5), lam='star', P0='cert', rebalance=False)
    S2 = run("S2  as S1 but ends at C_ends(c' = c_rho(rho2) = 31.2649, L) per Q (the Gevrey ramp's own window constant; sharp w/LL-suppressed form)",
             zone='fixed', c_buf='proved', ends=('cprime', 31.26487817), lam='star', P0='cert')
    S2f = run("S2f as S1 but ends at C_ends(c' = 4, L) per Q (the floor, per-Q instead of flat 3.7e5)",
              zone='fixed', c_buf='proved', ends=('cprime', 4.0), lam='star', P0='cert')
    S3 = run("S3  as S1 but ends at C_ends(c' = c_win = 548.0857, L) per Q (THE ARTIFACT'S uniform majorant, Lean Mpoly majorants)",
             zone='fixed', c_buf='proved', ends=('cprime', 548.0857), lam='star', P0='cert')
    S3s = run("S3s as S1 but ends at C_ends(c' = c_win with exact suprema = 248.6855, L) per Q",
              zone='fixed', c_buf='proved', ends=('cprime', 248.6855), lam='star', P0='cert')

    P("")
    P("=== row dominance at 1e100 and 1e300 (which rows dominate) ===")
    for lab, S in (("S1", S1), ("S2", S2), ("S3", S3)):
        for n in (100, 300, 1000):
            d = S[n]
            if d is None: continue
            rr = d['rows']
            order = sorted(rr.items(), key=lambda kv: -kv[1])
            P("  %s 1e%d: " % (lab, n) + ", ".join("%s %.4g" % (k, v) for k, v in order) + "  | total %.4g, P_eff %+.4f" % (d['total'], d['P_eff']))

    open(__file__.replace("table2_rerun.py", "table2_rerun.log"), "w", encoding="utf-8").write("\n".join(out) + "\n")
    print("done")
