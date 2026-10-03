/-
L7_9 round 4: per-step bound for `w̃` keeping the `D_T` difference (for (a2) `model_outer`).
-/
import ZetaShell.LemmaK.LK9_K6c2_Aux

noncomputable section

namespace ZetaShell
namespace LemmaK
namespace K6

/-- the per-step bound keeping the `D_T` difference. -/
lemma wmod_step2 (T s : ℝ) (hT : 0 ≤ T) (m : ℕ) (hm : 1 ≤ m) :
    ‖wmod T s (m + 1) - wmod T s m‖
      ≤ (2 * Real.pi)⁻¹ * (3 / ((m : ℝ) * Real.sqrt m)) * T
        + (2 * Real.pi)⁻¹ * (Real.sqrt m)⁻¹ * ‖DT T (s - Real.log ((m + 1 : ℕ) : ℝ)) - DT T (s - Real.log m)‖ := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set g : ℕ → ℝ := fun k => (2 * Real.pi)⁻¹ * ((k : ℝ) ^ (-(1 / 2 : ℝ))) * rho6 (Real.log k - s) with hg
  set D : ℕ → ℂ := fun k => DT T (s - Real.log k) with hD
  have hw : ∀ k, wmod T s k = -((g k : ℝ) : ℂ) * D k := fun k => rfl
  have hsplit : wmod T s (m + 1) - wmod T s m
      = -(((g (m + 1) - g m : ℝ) : ℂ) * D (m + 1) + ((g m : ℝ) : ℂ) * (D (m + 1) - D m)) := by
    rw [hw, hw]; push_cast; ring
  have hsq0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  -- |g m| ≤ (2π)⁻¹/√m
  have hgm : |g m| ≤ (2 * Real.pi)⁻¹ * (Real.sqrt m)⁻¹ := by
    simp only [hg]
    rw [rpow_neg_half_eq _ hm0.le, abs_mul, abs_mul, abs_of_pos hpi,
      abs_of_pos (inv_pos.mpr hsq0), abs_of_nonneg (rho6_nonneg _)]
    have := rho6_le_one (Real.log m - s)
    have h0 : 0 ≤ (2 * Real.pi)⁻¹ * (Real.sqrt m)⁻¹ := by positivity
    nlinarith
  -- |g(m+1) − g m| ≤ (2π)⁻¹·3/(m√m)
  have hgd : |g (m + 1) - g m| ≤ (2 * Real.pi)⁻¹ * (3 / ((m : ℝ) * Real.sqrt m)) := by
    simp only [hg]
    push_cast
    rw [rpow_neg_half_eq _ (by linarith), rpow_neg_half_eq _ hm0.le]
    set p := (Real.sqrt ((m : ℝ) + 1))⁻¹
    set q := (Real.sqrt (m : ℝ))⁻¹
    set ρ₁ := rho6 (Real.log ((m : ℝ) + 1) - s)
    set ρ₀ := rho6 (Real.log (m : ℝ) - s)
    have e : (2 * Real.pi)⁻¹ * p * ρ₁ - (2 * Real.pi)⁻¹ * q * ρ₀
        = (2 * Real.pi)⁻¹ * ((p - q) * ρ₁ + q * (ρ₁ - ρ₀)) := by ring
    rw [e, abs_mul, abs_of_pos hpi]
    apply mul_le_mul_of_nonneg_left _ hpi.le
    have hpq := inv_sqrt_diff (m : ℝ) hmR
    have hρ := rho6_lip (Real.log ((m : ℝ) + 1) - s) (Real.log (m : ℝ) - s)
    have hlog := log_succ_sub_le (m : ℝ) hmR
    have hlog0 : 0 ≤ Real.log ((m : ℝ) + 1) - Real.log m :=
      sub_nonneg.mpr (Real.log_le_log hm0 (by linarith))
    rw [show Real.log ((m : ℝ) + 1) - s - (Real.log (m : ℝ) - s)
      = Real.log ((m : ℝ) + 1) - Real.log m by ring, abs_of_nonneg hlog0] at hρ
    have hq0 : 0 < q := inv_pos.mpr hsq0
    have hρ1 : |ρ₁| ≤ 1 := by rw [abs_of_nonneg (rho6_nonneg _)]; exact rho6_le_one _
    have h1 : |(p - q) * ρ₁| ≤ 1 / ((m : ℝ) * Real.sqrt m) := by
      rw [abs_mul]
      calc |p - q| * |ρ₁| ≤ |p - q| * 1 := mul_le_mul_of_nonneg_left hρ1 (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hpq
    have h2 : |q * (ρ₁ - ρ₀)| ≤ 2 / ((m : ℝ) * Real.sqrt m) := by
      rw [abs_mul, abs_of_pos hq0]
      have : |ρ₁ - ρ₀| ≤ 2 * (1 / (m : ℝ)) := by linarith
      calc q * |ρ₁ - ρ₀| ≤ q * (2 * (1 / (m : ℝ))) := mul_le_mul_of_nonneg_left this hq0.le
        _ = 2 / ((m : ℝ) * Real.sqrt m) := by simp only [q]; field_simp
    calc |(p - q) * ρ₁ + q * (ρ₁ - ρ₀)| ≤ |(p - q) * ρ₁| + |q * (ρ₁ - ρ₀)| := abs_add_le _ _
      _ ≤ 1 / ((m : ℝ) * Real.sqrt m) + 2 / ((m : ℝ) * Real.sqrt m) := add_le_add h1 h2
      _ = 3 / ((m : ℝ) * Real.sqrt m) := by ring
  have hD1 : ‖D (m + 1)‖ ≤ T := DTFacts.DT_norm_le T _ hT
  rw [hsplit, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have t1 : |g (m + 1) - g m| * ‖D (m + 1)‖ ≤ (2 * Real.pi)⁻¹ * (3 / ((m : ℝ) * Real.sqrt m)) * T :=
    mul_le_mul hgd hD1 (norm_nonneg _) (by positivity)
  have t2 : |g m| * ‖D (m + 1) - D m‖
      ≤ (2 * Real.pi)⁻¹ * (Real.sqrt m)⁻¹ * ‖D (m + 1) - D m‖ :=
    mul_le_mul_of_nonneg_right hgm (norm_nonneg _)
  have e : D (m + 1) - D m = DT T (s - Real.log ((m + 1 : ℕ) : ℝ)) - DT T (s - Real.log m) := rfl
  rw [e] at t2
  linarith

end K6
end LemmaK
end ZetaShell
