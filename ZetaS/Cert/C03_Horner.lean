/-
nodes/C03_Horner.lean — track C node C03 (L1_1b, 28 Sep 2026).
Depends on: C02.
Expected proof size: ≤ 60 lines.
PROVED (L5_1, 28 Sep 2026). Imports C02_QIOps.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C02_QIOps

noncomputable section

open Set

namespace ZetaS.CertV2

/-- `horner cs T` encloses Σ_j c_j u^j when `T` contains `u`. -/
theorem horner_contains (cs : List ℚ) {T : QI} {u : ℝ} (hu : T.Contains u) :
    (horner cs T).Contains (((List.range cs.length).map fun j => ((cs.getD j 0 : ℚ) : ℝ) * u ^ j).sum) := by
  induction cs with
  | nil => simp [horner, QI.Contains, QI.pt]
  | cons c cs ih =>
    have hs : ((List.range (c :: cs).length).map fun j => (((c :: cs).getD j 0 : ℚ) : ℝ) * u ^ j).sum
        = (c : ℝ) + ((List.range cs.length).map fun j => ((cs.getD j 0 : ℚ) : ℝ) * u ^ j).sum * u := by
      rw [List.length_cons, List.sum_range_succ', ← List.sum_map_mul_right]
      simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro j _
      rw [pow_succ]
      ring
    rw [hs]
    show (QI.add (QI.pt c) (QI.mul (horner cs T) T)).Contains _
    exact QI.contains_add ⟨le_rfl, le_rfl⟩ (QI.contains_mul ih hu)

end ZetaS.CertV2
