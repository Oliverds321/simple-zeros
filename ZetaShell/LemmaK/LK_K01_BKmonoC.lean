/-
Node K01 (L7_3): `B^K_C(v)` is monotone in `C` (admissible `v`): used to pass from the family constant
`C = π⁴/18` (`ZetaQ.Cfam`, `Family.qle.Cconst`) to the certificate's rational `C⁺ = 541161617/10⁸`
(thm:one-prime: "`Pcert ≤ 2 − B^K_C(v_K)`, computed … with `C = π⁴/18 ≤ C⁺`"). Mirror of `ZetaQ.Payoff.B_mono_C`.
Dependencies: trunk `ZetaQ.Payoff` (`psi_integrable`, `psi_nonneg`). Difficulty: E. PROVED.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace LemmaK

open ZetaQ.Payoff

theorem killedKernel_meas (C : ℝ) : Measurable (killedKernel C) := by
  unfold killedKernel
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    continuous_abs.measurable measurable_const

theorem killedPsi_integrable {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (C : ℝ) :
    Integrable (fun α => killedKernel C α * psi v α) := by
  refine Integrable.mono' (g := fun α => (1 + |C|) * psi v α)
    ((psi_integrable hv).const_mul _)
    (((killedKernel_meas C).aestronglyMeasurable).mul (psi_integrable hv).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun α => ?_
  have hp := psi_nonneg hv α
  have hk : |killedKernel C α| ≤ 1 + |C| := by
    unfold killedKernel
    split_ifs with h
    · rw [abs_abs]; linarith [abs_nonneg C]
    · linarith [abs_nonneg C]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_right hk hp

/-- **K01.** -/
theorem BK_mono_C {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) {C C' : ℝ} (h : C ≤ C') :
    BK C v ≤ BK C' v := by
  unfold BK
  have : ∫ α, killedKernel C α * psi v α ≤ ∫ α, killedKernel C' α * psi v α := by
    apply integral_mono (killedPsi_integrable hv C) (killedPsi_integrable hv C')
    intro α
    apply mul_le_mul_of_nonneg_right _ (psi_nonneg hv α)
    unfold killedKernel
    split_ifs
    · exact le_rfl
    · exact h
  linarith

end LemmaK
end ZetaShell
