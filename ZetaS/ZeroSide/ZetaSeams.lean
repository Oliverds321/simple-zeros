/-
lean_work/L3_1/ZetaSeams.lean — seams between the tree's `zetaZeroConfig` counts and the Mathlib-only counts of
`ChallengeDeps`/`ChallengeZetaS` (`Ncount`, `Nsimple`, `Ndist`, `Nsc`), and the cosine-window side conditions,
for the instances W2L-cos / W2L-poly / W1L (agent L3_1).
-/
import ZetaS.ZeroSide.Z9e_Seams
import ZetaS.Window.HeadlineV

noncomputable section

open Filter

namespace ZetaS
namespace ZSeam

open Zeta23

lemma N_eq (T₁ T₂ : ℝ) : zetaZeroConfig.N T₁ T₂ = _root_.Ncount T₁ T₂ := rfl
lemma Ns_eq (T₁ T₂ : ℝ) : zetaZeroConfig.Ns T₁ T₂ = _root_.Nsimple T₁ T₂ := rfl
lemma Nd_eq (T₁ T₂ : ℝ) : zetaZeroConfig.Nd T₁ T₂ = _root_.Ndist T₁ T₂ := rfl
lemma N0s_eq (T₁ T₂ : ℝ) : zetaZeroConfig.N0s T₁ T₂ = _root_.N0simple T₁ T₂ := rfl

/-- `N^sc = N₀ + Nˢ − N₀ˢ` (the simple-or-critical count, cor:oll-SC). -/
lemma Nsc_eq (T₁ T₂ : ℝ) :
    (ZetaS.Nsc T₁ T₂ : ℝ) = (zetaZeroConfig.N0 T₁ T₂ : ℝ) + zetaZeroConfig.Ns T₁ T₂ - zetaZeroConfig.N0s T₁ T₂ := by
  have hW : (zetaZeroConfig.window T₁ T₂).Finite := zetaZeroConfig.finite_window T₁ T₂
  have e0 : (ZetaS.Nsc T₁ T₂ : ℕ) = ∑ᶠ ρ ∈ zetaZeroConfig.window T₁ T₂ ∩
      {ρ | ρ.re = 1 / 2 ∨ zetaZeroConfig.mult ρ = 1}, zetaZeroConfig.mult ρ := rfl
  have a1 := Z9.finsum_inter_eq_sum hW (fun ρ => ρ.re = 1 / 2 ∨ zetaZeroConfig.mult ρ = 1) zetaZeroConfig.mult
  have a2 := Z9.finsum_inter_eq_sum hW (fun ρ => ρ.re = 1 / 2) zetaZeroConfig.mult
  have b1 := Z9.ncard_inter_eq_sum hW (fun ρ => zetaZeroConfig.mult ρ = 1)
  have c1 := Z9.ncard_inter_eq_sum hW (fun ρ => ρ.re = 1 / 2 ∧ zetaZeroConfig.mult ρ = 1)
  rw [e0, a1]
  simp only [ZeroConfig.N0, ZeroConfig.Ns, ZeroConfig.N0s, ZeroConfig.simple, ZeroConfig.onLine]
  rw [Set.inter_assoc (zetaZeroConfig.window T₁ T₂), ← Set.setOf_and, a2, b1, c1,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs <;> first | rfl | simp_all | (exfalso; tauto) | linarith

/-- `∫_{−1/2}^{1/2} cos(αs) ds > 1/2` for `0 < α ≤ 8/5`. -/
lemma half_lt_aC {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) : 1 / 2 < CosWindow.aC α := by
  unfold CosWindow.aC
  have hs := Real.sin_gt_sub_cube (x := α / 2) (by linarith)
  rw [lt_div_iff₀ hα0]
  have h2 : α ^ 2 ≤ 64 / 25 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hα0.le]

end ZSeam
end ZetaS
