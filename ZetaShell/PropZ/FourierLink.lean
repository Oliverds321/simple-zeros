/-
L7_5 (28 Sep 2026), round 8: the Fourier link for Step 4 (Mathlib only).
For `H, G : ℝ → ℂ` smooth with compact support:
  `∫ |F|² = ∫ |𝓕 F|²`                         (`plancherel_cc`, from Schwartz Plancherel),
  `∫ |H ⋆ G|² = ∫ |𝓕 H|² |𝓕 G|²`              (`norm_sq_convolution`, with `Real.fourier_mul_convolution_eq`),
  `|𝓕 F(η)| · |2πη|^N ≤ ∫ |F^{(N)}|`          (`norm_fourier_mul_le`, from `Real.fourier_iteratedDeriv`).
-/
import Mathlib

open MeasureTheory FourierTransform Complex Convolution

namespace ZetaShell.FourierLink

theorem plancherel_cc (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ∫ η, ‖𝓕 F η‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 :=
  SchwartzMap.integral_norm_sq_fourier (hFc.toSchwartzMap hF)

theorem norm_sq_convolution (H G : ℝ → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    ∫ x, ‖(H ⋆[ContinuousLinearMap.mul ℂ ℂ] G) x‖ ^ 2 = ∫ η, ‖𝓕 H η‖ ^ 2 * ‖𝓕 G η‖ ^ 2 := by
  have hHi : Integrable H := hH.continuous.integrable_of_hasCompactSupport hHc
  have hGi : Integrable G := hG.continuous.integrable_of_hasCompactSupport hGc
  have heq : (H ⋆[ContinuousLinearMap.mul ℂ ℂ] G) = (H ⋆[ContinuousLinearMap.mul ℝ ℂ] G) := by
    funext x; simp only [convolution_def, ContinuousLinearMap.mul_apply']
  have hs : ContDiff ℝ (⊤ : ℕ∞) (H ⋆[ContinuousLinearMap.mul ℂ ℂ] G) := by
    rw [heq]; exact hHc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hH hGi.locallyIntegrable
  have hc : HasCompactSupport (H ⋆[ContinuousLinearMap.mul ℂ ℂ] G) := hHc.convolution _ hGc
  rw [← plancherel_cc _ hs hc]
  congr 1; funext η
  rw [Real.fourier_mul_convolution_eq hHi hGi η, norm_mul, mul_pow]

theorem tsupport_iD_c (F : ℝ → ℂ) : ∀ n : ℕ, tsupport (iteratedDeriv n F) ⊆ tsupport F
  | 0 => by simp only [iteratedDeriv_zero]; exact le_rfl
  | n + 1 => by rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans (tsupport_iD_c F n)

theorem norm_fourier_mul_le (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (N : ℕ) (η : ℝ) : ‖𝓕 F η‖ * |2 * Real.pi * η| ^ N ≤ ∫ x, ‖iteratedDeriv N F x‖ := by
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (iteratedDeriv n F) := fun n _ => by
    have hs : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n F) := by
      rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv n hF
    have hc : HasCompactSupport (iteratedDeriv n F) :=
      IsCompact.of_isClosed_subset hFc (isClosed_tsupport _) (tsupport_iD_c F n)
    exact hs.continuous.integrable_of_hasCompactSupport hc
  have h := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (n := N) hF hint le_top
  have h2 : 𝓕 (iteratedDeriv N F) η = (2 * Real.pi * I * η) ^ N • 𝓕 F η := by rw [h]
  have hn : ‖𝓕 (iteratedDeriv N F) η‖ ≤ ∫ x, ‖iteratedDeriv N F x‖ := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x
    rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
  rw [h2, norm_smul, norm_pow] at hn
  have e : ‖(2 * Real.pi * I * η : ℂ)‖ = |2 * Real.pi * η| := by
    rw [show (2 * Real.pi * I * η : ℂ) = ((2 * Real.pi * η : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [e] at hn
  linarith [mul_comm (|2 * Real.pi * η| ^ N) ‖𝓕 F η‖]

end ZetaShell.FourierLink
