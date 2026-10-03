/-
L7_5 (28 Sep 2026), round 5: the second derivative of `D_T`, an input of the pointwise leaf `ZR_phi_pw`.
  `D_T″(v) = ∫_T^{2T} (iτ)² e^{iτv} dτ`,  `|D_T″(v)| ≤ 4T³`  (differentiation under the integral, as for `D_T′`).
Mathlib and `DT_Facts` only; namespace `ZetaShell.DTFacts`.
-/
import ZetaShell.PropZ.DT_Facts

namespace ZetaShell.DTFacts

theorem deriv_DTf_eq (T : ℝ) :
    deriv (DTf T) = fun v : ℝ => ∫ τ in T..(2 * T), Complex.I * τ * Complex.exp (Complex.I * τ * v) := by
  funext v; exact (hasDerivAt_DTf T v).deriv

theorem hasDerivAt_deriv_DTf (T v : ℝ) :
    HasDerivAt (deriv (DTf T))
      (∫ τ in T..(2 * T), Complex.I * τ * (Complex.I * τ * Complex.exp (Complex.I * τ * v))) v := by
  rw [deriv_DTf_eq]
  have key : ∀ τ w : ℝ, HasDerivAt (fun w : ℝ => Complex.I * τ * Complex.exp (Complex.I * τ * w))
      (Complex.I * τ * (Complex.I * τ * Complex.exp (Complex.I * τ * w))) w := by
    intro τ w
    have h1 : HasDerivAt (fun w : ℝ => Complex.I * τ * (w : ℂ)) (Complex.I * τ * 1) w :=
      (Complex.ofRealCLM.hasDerivAt (x := w)).const_mul (Complex.I * τ)
    have := ((Complex.hasDerivAt_exp (Complex.I * τ * w)).comp w h1).const_mul (Complex.I * (τ : ℂ))
    refine this.congr_deriv ?_
    ring
  have hb : ∀ τ w : ℝ, ‖Complex.I * τ * (Complex.I * τ * Complex.exp (Complex.I * τ * w))‖ = |τ| * |τ| := by
    intro τ w
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      show Complex.I * (τ : ℂ) * w = ((τ * w : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume) (a := T)
    (b := 2 * T) (F := fun (w : ℝ) (τ : ℝ) => Complex.I * τ * Complex.exp (Complex.I * τ * w))
    (F' := fun (w : ℝ) (τ : ℝ) => Complex.I * τ * (Complex.I * τ * Complex.exp (Complex.I * τ * w)))
    (x₀ := v) (s := Set.univ)
    (bound := fun τ => |τ| * |τ|) Filter.univ_mem
    (Filter.Eventually.of_forall fun w => (by fun_prop : Continuous fun τ : ℝ =>
      Complex.I * τ * Complex.exp (Complex.I * τ * w)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun τ : ℝ => Complex.I * τ * Complex.exp (Complex.I * τ * v)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun τ : ℝ =>
      Complex.I * τ * (Complex.I * τ * Complex.exp (Complex.I * τ * v))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun τ _ w _ => (hb τ w).le)
    ((continuous_abs.mul continuous_abs).intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun τ _ w _ => key τ w)
  exact this.2

theorem norm_deriv2_DTf_le {T : ℝ} (hT : 0 ≤ T) (v : ℝ) : ‖deriv (deriv (DTf T)) v‖ ≤ 4 * T ^ 3 := by
  rw [(hasDerivAt_deriv_DTf T v).deriv]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T) (C := 4 * T ^ 2)
    (f := fun τ : ℝ => Complex.I * τ * (Complex.I * τ * Complex.exp (Complex.I * τ * v))) (fun τ hτ => by
      rw [Set.uIoc_of_le (by linarith)] at hτ
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        show Complex.I * (τ : ℂ) * v = ((τ * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos (by linarith [hτ.1])]
      nlinarith [hτ.1, hτ.2])
  rw [abs_of_nonneg (by linarith)] at h
  nlinarith

end ZetaShell.DTFacts
