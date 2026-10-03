/-
lean_work/L1_1/CheckerLeaves.lean — track C checker, LEAVES module, version 3 (L1_1c, 28 Sep 2026).
The instance `LIQ`, boxes, the three leaf checkers, the tree and the shard-assembly lemmas. Core Lean only.

Changes against `CheckerCore.lean` (lines 164–326; everything else byte-identical):
  * `lpSpan` (FIX of the C18 soundness bug found by L5_1): the tangent l3 at x̂ = lsum ĝ is admitted only if
    x0 − r ≤ x̂ ≤ x0 + r (the penalty bounds −w″ only on the span interval). One line changed.
    `checkLP`, `Leaf.check`, `Node.check` are textually unchanged but depend on `lpSpan`.
  * NEW (additions only, used by no existing leaf): `symmTest`, `psdLDLChecked` (psdLDL guarded by an explicit
    symmetry test, for any future caller), `QI.inv?` (option-valued inverse that cannot be misused),
    `sincSideOK` (the side condition of the corrected C07b as a Bool), `Box.ordered`.
  * NOT changed, by decision (L1_1c report §1): `psdLDL`, `checkConvex` (the symmetry of the matrix it builds is proved
    from its construction inside C19b, and a test would invalidate that proof for no gain), `QI.inv`,
    `sincDerivsQI` (their corrected statements with side conditions are proved and all checker calls satisfy them).
-/
import CheckerBase

namespace ZetaS.CertV2

/-! ## 4. The instance and the leaf checks -/

structure LIQ where
  d : Nat
  spans : List (Nat × Nat × Rat)
  mu : List Rat
  claim : Rat

abbrev Box := List (Rat × Rat)
def lsum (v : List Rat) (i s : Nat) : Rat := ((List.range s).map fun t => v.getD (i + t) 0).sum
def Box.center (B : Box) : List Rat := B.map fun p => (p.1 + p.2) / 2
def Box.half (B : Box) : List Rat := B.map fun p => (p.2 - p.1) / 2

def consecCells : Int → List Cell → Bool
  | _, [] => true
  | n, c :: cs => decide (c.n = n) && consecCells (n + 1) cs

/-- (ok, inf w'', sup w'', inf w) on [x0 − r, x0 + r]: best of the span Taylor model and the covering cells. -/
def spanBounds (sd : SpanD) (x0 r : Rat) : Bool × Rat × Rat × Rat :=
  let tm := taylorModel sd.c.k0 sd.c.k1 sd.c.k2 r
  match sd.cells with
  | [] => (decide (sd.c.x = x0), tm.1, tm.2.1, tm.2.2)
  | c0 :: rest =>
    let cov := decide (sd.c.x = x0) && consecCells c0.n (c0 :: rest) &&
      decide ((c0.n : Rat) * cw ≤ x0 - r) && decide (x0 + r ≤ ((c0.n : Rat) + (rest.length + 1 : Nat)) * cw)
    (cov, max tm.1 (rest.foldl (fun a c => min a c.plo) c0.plo),
      min tm.2.1 (rest.foldl (fun a c => max a c.phi) c0.phi),
      max tm.2.2 (rest.foldl (fun a c => min a c.wlo) c0.wlo))

def tangentLine (x0 r tp pen : Rat) (p : KPt) : Rat × Rat :=
  let rr := max (qabs (x0 - r - tp)) (qabs (x0 + r - tp))
  let w1 := QI.smul 2 (QI.mul p.k0 p.k1)
  let sig := QI.rdn ((w1.lo + w1.hi) / 2)
  (sig, (QI.sq p.k0).lo - max (qabs (w1.lo - sig)) (qabs (w1.hi - sig)) * rr - pen * rr * rr / 2 - sig * tp)

def chunks5 : List Rat → List (List Rat)
  | a :: b :: c :: d :: e :: rest => [a, b, c, d, e] :: chunks5 rest
  | _ => []

structure Acc where
  rho : List Rat
  kap : Rat
  ok : Bool

def addOn (rho : List Rat) (i s : Nat) (v : Rat) : List Rat :=
  (List.range rho.length).map fun l => rho.getD l 0 + (if i ≤ l ∧ l < i + s then v else 0)

/-- one span of an LP leaf. -/
def lpSpan (c h gh : List Rat) (acc : Acc) (sp : Nat × Nat × Rat) (sd : SpanD) (yy : List Rat) : Acc :=
  let x0 := lsum c sp.1 sp.2.1
  let r := lsum h sp.1 sp.2.1
  let xh := lsum gh sp.1 sp.2.1
  let sb := spanBounds sd x0 r
  let pen := max 0 (-sb.2.1)
  let l2 := tangentLine x0 r x0 pen sd.c
  let l3 := tangentLine x0 r xh pen sd.h
  let wa := (QI.sq sd.a.k0).lo
  let wb := (QI.sq sd.b.k0).lo
  let slp := if r = 0 then 0 else (wb - wa) / (2 * r)
  let slq := QI.rdn slp
  let l4 : Rat × Rat := (slq, wa - slq * (x0 - r) - (qabs (slp - slq)) * 2 * r - max sb.2.2.1 0 * (2 * r) ^ 2 / 8)
  let y0 := yy.getD 0 0
  let y1 := yy.getD 1 0
  let y2 := yy.getD 2 0
  let y3 := yy.getD 3 0
  let y4 := yy.getD 4 0
  -- records are only required for lines with a nonzero multiplier (a zero multiplier contributes 0 whatever its line)
  let ok := (decide (y1 = 0 ∧ y2 = 0 ∧ y3 = 0 ∧ y4 = 0) ||
      (sb.1 && (decide (y3 = 0) || (decide (sd.h.x = xh) && decide (x0 - r ≤ xh) && decide (xh ≤ x0 + r))) &&
        (decide (y4 = 0) || (decide (sd.a.x = x0 - r) && decide (sd.b.x = x0 + r))))) &&
    decide (0 ≤ y0 ∧ 0 ≤ y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3 ∧ 0 ≤ y4) && decide (y0 + y1 + y2 + y3 + y4 ≤ sp.2.2)
  ⟨addOn acc.rho sp.1 sp.2.1 (y2 * l2.1 + y3 * l3.1 + y4 * l4.1),
   acc.kap + y1 * sb.2.2.2 + y2 * l2.2 + y3 * l3.2 + y4 * l4.2, acc.ok && ok⟩

def minLin (c lo hi : Rat) : Rat := min (c * lo) (c * hi)

def boxMinLin (rho : List Rat) (B : Box) : Rat :=
  ((List.range rho.length).map fun l => minLin (rho.getD l 0) (B.getD l (0, 0)).1 (B.getD l (0, 0)).2).sum

def checkLP (D : LIQ) (B : Box) (gh y : List Rat) (sds : List SpanD) : Bool :=
  let c := B.center
  let h := B.half
  let lam := y.getLastD 0
  let acc0 : Acc := ⟨D.mu.map (fun m => m * (1 + lam)), -lam * D.claim, decide (0 ≤ lam)⟩
  let acc := ((D.spans.zip sds).zip (chunks5 y)).foldl (fun a t => lpSpan c h gh a t.1.1 t.1.2 t.2) acc0
  acc.ok && decide (sds.length = D.spans.length) && decide (y.length = 5 * D.spans.length + 1) &&
    decide (D.claim ≤ acc.kap + boxMinLin acc.rho B)

/-- exact PSD test by symmetric elimination. -/
def psdLDL : Nat → List (List Rat) → Bool
  | 0, _ => true
  | _, [] => true
  | n + 1, (row :: rest) =>
    let piv := row.headD 0
    if piv < 0 then false
    else if piv = 0 then rest.all (fun r => r.headD 0 = 0) && psdLDL n (rest.map List.tail)
    else psdLDL n (rest.map fun r => List.zipWith (fun a b => a - (r.headD 0 / piv) * b) r.tail row.tail)

structure CAcc where
  Flo : Rat
  grad : List QI
  P : List (List Rat)
  ok : Bool

def cvxSpan (c h gh : List Rat) (acc : CAcc) (sp : Nat × Nat × Rat) (sd : SpanD) : CAcc :=
  let x0 := lsum c sp.1 sp.2.1
  let r := lsum h sp.1 sp.2.1
  let xh := lsum gh sp.1 sp.2.1
  let sb := spanBounds sd x0 r
  let wd := QI.smul (2 * sp.2.2) (QI.mul sd.h.k0 sd.h.k1)
  let inS := fun (l : Nat) => decide (sp.1 ≤ l ∧ l < sp.1 + sp.2.1)
  ⟨acc.Flo + sp.2.2 * (QI.sq sd.h.k0).lo,
   (List.range acc.grad.length).map (fun l => if inS l then QI.add (acc.grad.getD l (QI.pt 0)) wd else acc.grad.getD l (QI.pt 0)),
   (List.range acc.P.length).map (fun a => (List.range acc.P.length).map fun b =>
      (acc.P.getD a []).getD b 0 + (if inS a && inS b then sp.2.2 * sb.2.1 else 0)),
   acc.ok && sb.1 && decide (sd.h.x = xh)⟩

def checkConvex (D : LIQ) (B : Box) (gh : List Rat) (sds : List SpanD) : Bool :=
  let c := B.center
  let h := B.half
  let inBox := (List.range D.d).all fun l =>
    decide ((B.getD l (0, 0)).1 ≤ gh.getD l 0) && decide (gh.getD l 0 ≤ (B.getD l (0, 0)).2)
  let acc0 : CAcc := ⟨((List.range D.d).map fun l => D.mu.getD l 0 * gh.getD l 0).sum,
    D.mu.map QI.pt, (List.range D.d).map (fun _ => (List.range D.d).map fun _ => 0), true⟩
  let acc := (D.spans.zip sds).foldl (fun a t => cvxSpan c h gh a t.1 t.2) acc0
  let corr := ((List.range D.d).map fun l =>
    (QI.mul (acc.grad.getD l (QI.pt 0)) ⟨(B.getD l (0, 0)).1 - gh.getD l 0, (B.getD l (0, 0)).2 - gh.getD l 0⟩).lo).sum
  inBox && acc.ok && decide (sds.length = D.spans.length) && psdLDL D.d acc.P && decide (D.claim ≤ acc.Flo + corr)

def checkCap (D : LIQ) (B : Box) : Bool :=
  decide (D.claim ≤ ((List.range D.d).map fun l => D.mu.getD l 0 * (B.getD l (0, 0)).1).sum)

inductive Leaf where
  | cap
  | convex (gh : List Rat) (sds : List SpanD)
  | lp (gh y : List Rat) (sds : List SpanD)

inductive Node where
  | leaf (l : Leaf)
  | split (axis : Nat) (left right : Node)

def Box.splitAt (B : Box) (a : Nat) : Box × Box :=
  let m := ((B.getD a (0, 0)).1 + (B.getD a (0, 0)).2) / 2
  (B.modify a (fun p => (p.1, m)), B.modify a (fun p => (m, p.2)))

def Leaf.check (D : LIQ) (B : Box) : Leaf → Bool
  | .cap => checkCap D B
  | .convex gh sds => checkConvex D B gh sds
  | .lp gh y sds => checkLP D B gh y sds

def Node.check (D : LIQ) : Node → Box → Bool
  | .leaf l, B => l.check D B
  | .split a L R, B => decide (a < D.d) && L.check D (B.splitAt a).1 && R.check D (B.splitAt a).2

/-- Assembly step (no evaluation of the subtrees): a split node checks if its halves do. -/
theorem Node.check_split_of (D : LIQ) (a : Nat) (L R : Node) (B B1 B2 : Box) (hs : B.splitAt a = (B1, B2))
    (ha : decide (a < D.d) = true) (hL : L.check D B1 = true) (hR : R.check D B2 = true) :
    (Node.split a L R).check D B = true := by
  simp only [Node.check, hs, ha, hL, hR, Bool.and_self]

theorem Node.check_leaf_of (D : LIQ) (l : Leaf) (B : Box) (h : l.check D B = true) :
    (Node.leaf l).check D B = true := h


/-! ## 5. Additions of version 3 (no existing definition depends on them) -/

/-- explicit symmetry test for an n×n list matrix. -/
def symmTest (n : Nat) (P : List (List Rat)) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => decide ((P.getD i []).getD j 0 = (P.getD j []).getD i 0)

/-- `psdLDL` guarded by the symmetry test: sound for EVERY input (with `psdLDL_sound_symm`). -/
def psdLDLChecked (n : Nat) (P : List (List Rat)) : Bool := symmTest n P && psdLDL n P

/-- option-valued interval inverse: `none` unless the interval excludes 0. -/
def QI.inv? (I : QI) : Option QI :=
  if 0 < I.lo ∨ I.hi < 0 then some (QI.inv I) else none

/-- the side condition of the corrected C07b (`sincDerivsQI_contains'`) as a Bool. -/
def sincSideOK (Y : QI) : Bool := decide (Y.absMax ≤ 1 / 2 ∨ 0 < Y.lo ∨ Y.hi < 0)

/-- every coordinate interval of a box is ordered (lo ≤ hi). -/
def Box.ordered (B : Box) : Bool := B.all fun p => decide (p.1 ≤ p.2)

end ZetaS.CertV2
