"""d8_9: exact (Arb) all-marks value from a claims json, window cos(alpha s).
p = (H + a2/2 - nu)/(1 - a1 + a2/2)  [Sigma >= p],  D >= (1+p)/2 = (1 + H + a2 - a1 - nu)/(2 - 2a1 + a2);
H(cos alpha s) from the certifier's rigorous_H (Arb acb.integral), recomputed here at 200 bits.
(OL_L) robustness (d8_5 sec 3.4 / sec 7): with k* = k(3/4) (Gram kernel of cos(alpha s)),
   min(2k*^2 - 2a1, 4k*^2 - 2a2, (1/2 + sqrt(1/4 + 2k*^2))^2 - 1 - a1 - a2) >= max(a1, a2)   and   c = 2 - 2a1 > 1.4553138.
Usage: python pexact2.py claims.json [alpha]"""
import sys, json
from fractions import Fraction as Fr
from flint import arb, fmpq, ctx
sys.path.insert(0, '.')
from bnb_lb3_w import rigorous_H
cj = json.load(open(sys.argv[1])); alpha = sys.argv[2] if len(sys.argv) > 2 else str(cj['alpha'])
H = rigorous_H(alpha, prec=200)
ctx.prec = 200
q = lambda s: arb(fmpq(Fr(s).numerator, Fr(s).denominator))
a1, a2, nu = q(cj['a1']), q(cj['a2']), q(cj['nu'])
p = (H + a2 / 2 - nu) / (1 - a1 + a2 / 2)
D = (1 + p) / 2
al = q(Fr(alpha)); Zs = 2 * (al / 2).sin() / al
def k(t):
    w = 2 * arb.pi() * t
    return (((al + w) / 2).sinc() + ((al - w) / 2).sinc()) / (2 * Zs)
ks2 = k(q(Fr(3, 4))) ** 2
m11 = 2 * ks2 - 2 * a1; m22 = 4 * ks2 - 2 * a2; m12 = (arb(1) / 2 + (arb(1) / 4 + 2 * ks2).sqrt()) ** 2 - 1 - a1 - a2
mx = a1 if Fr(cj['a1']) >= Fr(cj['a2']) else a2
rob = min(float(m11.lower()), float(m22.lower()), float(m12.lower())) - float(mx.upper())
c = 2 - 2 * a1
print(f"alpha={alpha} a1={cj['a1']} a2={cj['a2']} nu={cj['nu']}")
print(f"H = {H.str(25)}")
print(f"Sigma >= p = {p.str(20)}   (lower {float(p.lower()):.12f})")
print(f"D >= (1+p)/2 = {D.str(20)}   (lower {float(D.lower()):.12f})")
print(f"robustness: 2k(3/4)^2 = {(2*ks2).str(10)}; 2a1+max(a1,a2) = {float(2*Fr(cj['a1'])+max(Fr(cj['a1']),Fr(cj['a2']))):.6f} <= 0.25304: "
      f"{2*Fr(cj['a1'])+max(Fr(cj['a1']),Fr(cj['a2'])) < Fr(25304,100000)}; full condition min(...) - max(a1,a2) >= {rob:.6f} (>0: {rob > 0}); "
      f"c = 2-2a1 = {float(c.lower()):.8f} > 1.4553138: {bool(c > q('1.4553138'))}")
sys.exit(0 if (rob > 0 and bool(c > q('1.4553138'))) else 1)   # (Oct 2026) exit status 0 only if both conditions hold
