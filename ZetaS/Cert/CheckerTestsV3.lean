/-
lean_work/L1_1/CheckerTestsV3.lean — kernel-checked negative and positive controls of the v3 checker (L1_1c).
Core Lean only; every theorem by `decide +kernel` (level A).

The three counterexamples of L5_1 (`lean_work/L5_1/C18_Counterexample.lean`, `C19a_Counterexample.lean`,
`C07b_Counterexample.lean`):
  * C18 (checker bug): the same `checkLP` call that the v2 checker ACCEPTED is now REJECTED (`neg_C18`).
  * C19a (statement): the two non-symmetric matrices accepted by `psdLDL` are rejected by `symmTest`, hence by
    `psdLDLChecked`; they are excluded from `psdLDL_sound_symm` by its symmetry hypothesis. `checkConvex` builds only
    symmetric matrices (proved inside C19b); `pos_C19a_*` shows the guarded test still accepts PSD symmetric input.
  * C07b (statement): the counterexample interval Y = [−1, 1] violates the side condition (`sincSideOK = false`)
    and `QI.inv? Y = none`; the checker's own sinc arguments satisfy it (`pos_C07b_*`, generic proof: C09 `Y_ok`).
-/
import CheckerCoreV3

namespace ZetaS.CertV2

/-! ### C18: the tangent at x̂ outside the span interval is rejected -/

def cxR0 : KPt := ⟨0, (kEnclQ 0).1, (kEnclQ 0).2.1, (kEnclQ 0).2.2, by decide +kernel⟩
def cxRh : KPt := ⟨1 / 2, (kEnclQ (1 / 2)).1, (kEnclQ (1 / 2)).2.1, (kEnclQ (1 / 2)).2.2, by decide +kernel⟩
def cxD : LIQ := ⟨1, [(0, 1, 1)], [0], 9 / 10⟩
def cxB : Box := [(1 / 2, 1 / 2)]

/-- L5_1's counterexample call (accepted by CheckerCore v2) is rejected by v3. -/
theorem neg_C18 : checkLP cxD cxB [0] [0, 0, 0, 1, 0, 0] [⟨cxRh, cxR0, cxR0, cxR0, []⟩] = false := by
  decide +kernel

/-- the same leaf with ĝ inside the box (x̂ = 1/2) is also rejected: the claim 9/10 is false (F(1/2) ≈ 0.446). -/
theorem neg_C18_inside : checkLP cxD cxB [1 / 2] [0, 0, 0, 1, 0, 0] [⟨cxRh, cxRh, cxR0, cxR0, []⟩] = false := by
  decide +kernel

/-- positive control: a true claim (2/5 < F(1/2)) through the tangent at x̂ = 1/2 is accepted. -/
theorem pos_C18 : checkLP ⟨1, [(0, 1, 1)], [0], 2 / 5⟩ cxB [1 / 2] [0, 0, 0, 1, 0, 0]
    [⟨cxRh, cxRh, cxR0, cxR0, []⟩] = true := by
  decide +kernel

/-! ### C19a: non-symmetric matrices -/

theorem neg_C19a_zeroPivot : psdLDLChecked 2 [[0, 1], [0, 0]] = false := by decide +kernel
theorem neg_C19a_posPivot : psdLDLChecked 2 [[1, 4], [0, 1]] = false := by decide +kernel
theorem neg_C19a_symm : symmTest 2 [[0, 1], [0, 0]] = false ∧ symmTest 2 [[1, 4], [0, 1]] = false := by
  decide +kernel
/-- the unguarded `psdLDL` (unchanged, used by `checkConvex` on symmetric matrices only) still accepts them. -/
theorem psdLDL_unguarded_accepts : psdLDL 2 [[0, 1], [0, 0]] = true ∧ psdLDL 2 [[1, 4], [0, 1]] = true := by
  decide +kernel
theorem pos_C19a : psdLDLChecked 2 [[2, 1], [1, 1]] = true ∧ psdLDLChecked 3 [[1, 1, 0], [1, 1, 0], [0, 0, 0]] = true := by
  decide +kernel
theorem neg_C19a_indef : psdLDLChecked 2 [[1, 2], [2, 1]] = false := by decide +kernel

/-! ### C07b: the quotient branch at an interval containing 0 -/

theorem neg_C07b : sincSideOK ⟨-1, 1⟩ = false ∧ QI.inv? ⟨-1, 1⟩ = none := by decide +kernel
/-- the checker's own arguments y = πx ± 4/5 (here x = 0 and x = 1/4, the latter with |y| < 1/2). -/
theorem pos_C07b : sincSideOK (QI.add (QI.smul 0 piQ) (QI.pt (4 / 5))) = true ∧
    sincSideOK (QI.add (QI.smul 0 piQ) (QI.pt (-(4 / 5)))) = true ∧
    sincSideOK (QI.add (QI.smul (1 / 4) piQ) (QI.pt (-(4 / 5)))) = true := by
  decide +kernel

/-! ### reversed boxes -/

theorem neg_box : Box.ordered [(1, 0)] = false ∧ Box.ordered [(0, 1), (1 / 2, 1 / 2)] = true := by decide +kernel

#print axioms neg_C18
#print axioms pos_C18
#print axioms neg_C19a_zeroPivot
#print axioms neg_C07b

end ZetaS.CertV2
