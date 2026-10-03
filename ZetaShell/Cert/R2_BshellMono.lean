/-
Node R2 (L7_1): `B_{α′}` is increasing in the level `ℓ` and in the outer constant `C` (ssec:shell-cert "Kernel and
constants", l.1018–1019: "Since `ψ ≥ 0`, `B` is increasing in the constant, so rational upper bounds suffice").
With R1 this passes from the family constant `π⁴/18` (resp. `2π⁴/27`) to the certificate's `C⁺`.
Dependencies: none new (`ψ ≥ 0`, integrability of `ψ` for admissible `v`, as `ZetaQ.Payoff.psi_nonneg`,
`psi_integrable`). Difficulty: E.
-/
import ZetaShell.Interfaces

namespace ZetaShell

private theorem adm_bridge {lam : ℝ} {v : ℝ → ℝ} (hv : AdmissibleS lam v) : ZetaQ.Payoff.Admissible lam v :=
  ⟨hv.nonneg, hv.integrable, hv.mass, hv.supp⟩

private theorem shellKernel_meas (ℓ αp C : ℝ) : Measurable (shellKernel ℓ αp C) := by
  unfold shellKernel
  refine Measurable.ite ?_ measurable_id.abs (Measurable.ite ?_ measurable_const measurable_const)
  · exact measurableSet_le measurable_id.abs measurable_const
  · exact measurableSet_le measurable_id.abs measurable_const

private theorem shellKernel_bdd (ℓ αp C : ℝ) (α : ℝ) : ‖shellKernel ℓ αp C α‖ ≤ max 1 (max |ℓ| |C|) := by
  unfold shellKernel
  split_ifs with h1 h2
  · rw [Real.norm_eq_abs, abs_abs]; exact le_trans h1 (le_max_left _ _)
  · rw [Real.norm_eq_abs]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [Real.norm_eq_abs]; exact le_trans (le_max_right _ _) (le_max_right _ _)

private theorem kpsi_integrable (ℓ αp C : ℝ) {lam : ℝ} {v : ℝ → ℝ} (hv : AdmissibleS lam v) :
    MeasureTheory.Integrable (fun α => shellKernel ℓ αp C α * psiS v α) := by
  have hψ : MeasureTheory.Integrable (psiS v) := ZetaQ.Payoff.psi_integrable (adm_bridge hv)
  exact hψ.bdd_mul (c := max 1 (max |ℓ| |C|)) (shellKernel_meas ℓ αp C).aestronglyMeasurable
    (Filter.Eventually.of_forall fun α => shellKernel_bdd ℓ αp C α)

theorem Bshell_mono {ℓ ℓ' αp C C' lam : ℝ} {v : ℝ → ℝ} (hv : AdmissibleS lam v) (hℓ : ℓ ≤ ℓ')
    (hC : C ≤ C') : Bshell ℓ αp C v ≤ Bshell ℓ' αp C' v := by
  unfold Bshell
  refine add_le_add le_rfl
    (MeasureTheory.integral_mono (kpsi_integrable ℓ αp C hv) (kpsi_integrable ℓ' αp C' hv) ?_)
  intro α
  have hψ : 0 ≤ psiS v α := ZetaQ.Payoff.psi_nonneg' (adm_bridge hv) α
  have hk : shellKernel ℓ αp C α ≤ shellKernel ℓ' αp C' α := by
    unfold shellKernel
    split_ifs <;> linarith
  exact mul_le_mul_of_nonneg_right hk hψ

end ZetaShell
