/-
L7_9 round 3: SHARED facts about `D_T(v) = ∫_T^{2T} e^{iτv} dτ` (`ZetaShell.LemmaK.DT`, defined in `LK_Defs`).
Depends only on the definitions (`LK_Defs`). Intended for sharing (e.g. L7_5's `ZP_Bridge`).
* `DT_zero`: `D_T(0) = T`.
* `DT_closed`: `D_T(v) = (e^{2iTv} − e^{iTv})/(iv)` for `v ≠ 0`.
* `DT_norm_le`: `|D_T(v)| ≤ T` (`T ≥ 0`).
* `DT_norm_le_two_div`: `|D_T(v)| ≤ 2/|v|` (`v ≠ 0`).
* `DT_lipschitz`: `|D_T(v) − D_T(v′)| ≤ (3/2)T²|v − v′|` (`T ≥ 0`).
-/
import ZetaShell.Defs.LK_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK
namespace DTFacts

lemma norm_exp_I_mul (τ v : ℝ) : ‖Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ))‖ = 1 := by
  rw [show Complex.I * (τ : ℂ) * (v : ℂ) = ((τ * v : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem DT_zero (T : ℝ) : DT T 0 = T := by
  unfold DT
  simp
  ring

theorem DT_closed (T v : ℝ) (hv : v ≠ 0) :
    DT T v = (Complex.exp (Complex.I * (v : ℂ) * ((2 * T : ℝ) : ℂ))
      - Complex.exp (Complex.I * (v : ℂ) * (T : ℂ))) / (Complex.I * (v : ℂ)) := by
  unfold DT
  have hc : Complex.I * (v : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hv)
  have e : (fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ)))
      = fun τ : ℝ => Complex.exp (Complex.I * (v : ℂ) * τ) := by
    funext τ; ring_nf
  rw [e, integral_exp_mul_complex hc]

theorem DT_norm_le (T v : ℝ) (hT : 0 ≤ T) : ‖DT T v‖ ≤ T := by
  unfold DT
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T) (C := 1)
    (f := fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ)))
    (fun τ _ => (norm_exp_I_mul τ v).le)
  rw [show |2 * T - T| = T by rw [abs_of_nonneg (by linarith)]; ring, one_mul] at h
  exact h

theorem DT_norm_le_two_div (T v : ℝ) (hv : v ≠ 0) : ‖DT T v‖ ≤ 2 / |v| := by
  rw [DT_closed T v hv, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have h1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (v : ℂ) * (x : ℂ))‖ = 1 := by
    intro x
    have := norm_exp_I_mul x v
    rw [show Complex.I * (x : ℂ) * (v : ℂ) = Complex.I * (v : ℂ) * (x : ℂ) by ring] at this
    exact this
  have hnum : ‖Complex.exp (Complex.I * (v : ℂ) * ((2 * T : ℝ) : ℂ))
      - Complex.exp (Complex.I * (v : ℂ) * (T : ℂ))‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (Complex.I * (v : ℂ) * ((2 * T : ℝ) : ℂ))‖
          + ‖Complex.exp (Complex.I * (v : ℂ) * (T : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h1]; norm_num
  exact div_le_div_of_nonneg_right hnum (abs_nonneg v)

/-- `|e^{iτv} − e^{iτv′}| ≤ |τ||v − v′|`. -/
lemma norm_exp_sub_exp_le (τ v v' : ℝ) :
    ‖Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ)) - Complex.exp (Complex.I * (τ : ℂ) * (v' : ℂ))‖
      ≤ |τ| * |v - v'| := by
  have e : Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ)) - Complex.exp (Complex.I * (τ : ℂ) * (v' : ℂ))
      = Complex.exp (Complex.I * (τ : ℂ) * (v' : ℂ))
        * (Complex.exp (Complex.I * ((τ * (v - v') : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e, norm_mul, norm_exp_I_mul, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]

theorem DT_lipschitz (T v v' : ℝ) (hT : 0 ≤ T) :
    ‖DT T v - DT T v'‖ ≤ (3 / 2) * T ^ 2 * |v - v'| := by
  unfold DT
  have hc : ∀ w : ℝ, Continuous (fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (w : ℂ))) := by
    intro w; fun_prop
  rw [← intervalIntegral.integral_sub ((hc v).intervalIntegrable _ _) ((hc v').intervalIntegrable _ _)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (a := T) (b := 2 * T)
    (f := fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ))
      - Complex.exp (Complex.I * (τ : ℂ) * (v' : ℂ)))
    (g := fun τ : ℝ => τ * |v - v'|) (by linarith)
    (Filter.Eventually.of_forall fun τ hτ => by
      have h := norm_exp_sub_exp_le τ v v'
      rw [abs_of_nonneg (by linarith [hτ.1] : (0 : ℝ) ≤ τ)] at h
      exact h)
    ((continuous_id.mul continuous_const).intervalIntegrable (μ := MeasureTheory.volume) _ _)
  refine hb.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, integral_id]
  ring

end DTFacts
end LemmaK
end ZetaShell
