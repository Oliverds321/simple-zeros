/-
lean_work/L1_1/CheckerBase.lean — track C checker, BASE module (L1_1c, 28 Sep 2026).
Rational intervals (grid 2⁻⁶⁴), the kernel-evaluated enclosures (π, sin/cos(πx), sinc and derivatives, kEnclQ,
taylorModel) and the verified records `KPt`, `Cell`, `SpanD`. Core Lean only.
Every declaration below is BYTE-IDENTICAL to lines 18–163 of `CheckerCore.lean` (md5 0506685e…, 28 Sep 10:02),
against which nodes C01–C17 and the majorant checker `MajCheck` (L5_2) were proved/built. Future fixes to the leaf
checkers go to `CheckerLeaves.lean` and never touch this module.
-/
namespace ZetaS.CertV2

def qabs (q : Rat) : Rat := if q < 0 then -q else q
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-! ## 1. Rational intervals, grid 2⁻⁶⁴ -/

structure QI where
  lo : Rat
  hi : Rat
  deriving Repr, DecidableEq

namespace QI
def grid : Rat := 2 ^ 64
def rdn (q : Rat) : Rat := ((q * grid).floor : Rat) / grid
def rup (q : Rat) : Rat := ((q * grid).ceil : Rat) / grid
def pt (q : Rat) : QI := ⟨q, q⟩
def add (I J : QI) : QI := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : QI) : QI := ⟨-I.hi, -I.lo⟩
def sub (I J : QI) : QI := add I (neg J)
def mul (I J : QI) : QI :=
  let a := I.lo * J.lo; let b := I.lo * J.hi; let c := I.hi * J.lo; let d := I.hi * J.hi
  ⟨rdn (min (min a b) (min c d)), rup (max (max a b) (max c d))⟩
def smul (q : Rat) (I : QI) : QI := mul (pt q) I
def sq (I : QI) : QI :=
  if 0 ≤ I.lo then ⟨rdn (I.lo * I.lo), rup (I.hi * I.hi)⟩
  else if I.hi ≤ 0 then ⟨rdn (I.hi * I.hi), rup (I.lo * I.lo)⟩
  else ⟨0, rup (max (I.lo * I.lo) (I.hi * I.hi))⟩
def widen (I : QI) (e : Rat) : QI := ⟨I.lo - e, I.hi + e⟩
def absMax (I : QI) : Rat := max (qabs (I.lo)) (qabs (I.hi))
def inv (I : QI) : QI :=
  if 0 < I.lo ∨ I.hi < 0 then ⟨rdn (1 / I.hi), rup (1 / I.lo)⟩ else ⟨-(2 ^ 200), 2 ^ 200⟩
/-- `J ⊆ I` as a Bool (stored interval I contains computed interval J). -/
def superset (I J : QI) : Bool := decide (I.lo ≤ J.lo) && decide (J.hi ≤ I.hi)
end QI

/-! ## 2. Enclosures computed by the kernel (evaluated once per record) -/

def piQ : QI := ⟨314159265358979323846 / 10 ^ 20, 314159265358979323847 / 10 ^ 20⟩

def horner (cs : List Rat) (t2 : QI) : QI := cs.foldr (fun c acc => QI.add (QI.pt c) (QI.mul acc t2)) (QI.pt 0)

def sinQI (n : Nat) (t : QI) : QI :=
  QI.widen (QI.mul (horner ((List.range n).map fun j => ((-1 : Rat) ^ j) / ((fact (2 * j + 1) : Nat) : Rat)) (QI.sq t)) t)
    (QI.rup (t.absMax ^ (2 * n + 1) / ((fact (2 * n + 1) : Nat) : Rat)))

def cosQI (n : Nat) (t : QI) : QI :=
  QI.widen (horner ((List.range n).map fun j => ((-1 : Rat) ^ j) / ((fact (2 * j) : Nat) : Rat)) (QI.sq t))
    (QI.rup (t.absMax ^ (2 * n) / ((fact (2 * n) : Nat) : Rat)))

/-- sin(πx), cos(πx): x = n/2 + f, (qabs (f)) ≤ 1/4. -/
def sinCosPiQ (x : Rat) : QI × QI :=
  let n : Int := (2 * x + 1 / 2).floor
  let t := QI.smul (x - (n : Rat) / 2) piQ
  let s := sinQI 9 t
  let c := cosQI 9 t
  if n % 4 = 0 then (s, c) else if n % 4 = 1 then (c, QI.neg s)
  else if n % 4 = 2 then (QI.neg s, QI.neg c) else (QI.neg c, s)

/-- (sinc, sinc', sinc'') at y from enclosures of y, sin y, cos y; series (8 terms) when (qabs (y)) ≤ 1/2. -/
def sincDerivsQI (y sy cy : QI) : QI × QI × QI :=
  if y.absMax ≤ 1 / 2 then
    let y2 := QI.sq y
    let m := y.absMax
    let f17 : Rat := ((fact 17 : Nat) : Rat)
    (QI.widen (horner ((List.range 8).map fun j => ((-1 : Rat) ^ j) / ((fact (2 * j + 1) : Nat) : Rat)) y2)
        (QI.rup (m ^ 16 / f17)),
     QI.widen (QI.mul (horner ((List.range 7).map fun j =>
        ((-1 : Rat) ^ (j + 1)) * (2 * (j + 1)) / ((fact (2 * j + 3) : Nat) : Rat)) y2) y)
        (QI.rup (16 * m ^ 15 / f17)),
     QI.widen (horner ((List.range 7).map fun j =>
        ((-1 : Rat) ^ (j + 1)) * (2 * (j + 1)) * (2 * j + 1) / ((fact (2 * j + 3) : Nat) : Rat)) y2)
        (QI.rup (16 * 15 * m ^ 14 / f17)))
  else
    let iy := QI.inv y
    let s0 := QI.mul sy iy
    let s1 := QI.mul (QI.sub cy s0) iy
    (s0, s1, QI.sub (QI.neg s0) (QI.smul 2 (QI.mul s1 iy)))

def sinA : QI := sinQI 9 (QI.pt (4 / 5))
def cosA : QI := cosQI 9 (QI.pt (4 / 5))
def inv2sincA : QI := QI.inv (QI.smul (5 / 2) sinA)

def kEnclQ (x : Rat) : QI × QI × QI :=
  let sc := sinCosPiQ x
  let px := QI.smul x piQ
  let one := fun (sg : Rat) =>
    sincDerivsQI (QI.add px (QI.pt (sg * (4 / 5))))
      (QI.add (QI.mul sc.1 cosA) (QI.smul sg (QI.mul sc.2 sinA)))
      (QI.sub (QI.mul sc.2 cosA) (QI.smul sg (QI.mul sc.1 sinA)))
  let m := one (-1)
  let p := one 1
  (QI.mul (QI.add m.1 p.1) inv2sincA,
   QI.mul (QI.mul (QI.add m.2.1 p.2.1) inv2sincA) piQ,
   QI.mul (QI.mul (QI.mul (QI.add m.2.2 p.2.2) inv2sincA) piQ) piQ)

def M3 : Rat := QI.rup (piQ.hi ^ 3 / 4)

/-- (inf w'', sup w'', inf w) on [x0 − r, x0 + r] from enclosures of k, k', k'' at x0 and (qabs (k''')) ≤ M3. -/
def taylorModel (k0 k1 k2 : QI) (r : Rat) : Rat × Rat × Rat :=
  let T : QI := ⟨-r, r⟩
  let T2 : QI := ⟨0, r * r⟩
  let kI := QI.widen (QI.add (QI.add k0 (QI.mul k1 T)) (QI.smul (1 / 2) (QI.mul k2 T2))) (QI.rup (M3 * r ^ 3 / 6))
  let k1I := QI.widen (QI.add k1 (QI.mul k2 T)) (QI.rup (M3 * r * r / 2))
  let k2I := QI.widen k2 (QI.rup (M3 * r))
  let wpp := QI.smul 2 (QI.add (QI.sq k1I) (QI.mul kI k2I))
  (wpp.lo, wpp.hi, max 0 (QI.sq kI).lo)

/-! ## 3. Verified records -/

def kptOk (x : Rat) (k0 k1 k2 : QI) : Bool :=
  let e := kEnclQ x
  QI.superset k0 e.1 && QI.superset k1 e.2.1 && QI.superset k2 e.2.2

/-- An enclosure record: proof field checked once, by the kernel, when the record is declared. -/
structure KPt where
  x : Rat
  k0 : QI
  k1 : QI
  k2 : QI
  ok : kptOk x k0 k1 k2 = true

def cw : Rat := 1 / 64

def cellOk (n : Int) (c : KPt) (plo phi wlo : Rat) : Bool :=
  let m := taylorModel c.k0 c.k1 c.k2 (1 / 128)
  decide (c.x = ((n : Rat) + 1 / 2) * cw) && decide (plo ≤ m.1) && decide (m.2.1 ≤ phi) && decide (wlo ≤ m.2.2)

structure Cell where
  n : Int
  c : KPt
  plo : Rat
  phi : Rat
  wlo : Rat
  ok : cellOk n c plo phi wlo = true

/-- Per-span data of a leaf: records at the span centre x0, at x̂ = span of ĝ, at x0 ∓ r; covering cells (or []). -/
structure SpanD where
  c : KPt
  h : KPt
  a : KPt
  b : KPt
  cells : List Cell

end ZetaS.CertV2
