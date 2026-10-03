/-
L7_9 round 3: helpers for (c2) `wmod_var`: elementary difference bounds.
-/
import ZetaShell.LemmaK.LK9_K6_Defs
import ZetaShell.LemmaK.LK9_DT_Facts

noncomputable section

namespace ZetaShell
namespace LemmaK
namespace K6

lemma rpow_neg_half_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow]

lemma inv_sqrt_diff (m : ℝ) (hm : 1 ≤ m) :
    |(Real.sqrt (m + 1))⁻¹ - (Real.sqrt m)⁻¹| ≤ 1 / (m * Real.sqrt m) := by
  set a := Real.sqrt m with ha
  set b := Real.sqrt (m + 1) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = m := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hle : b⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 hab
  rw [abs_of_nonpos (by linarith), neg_sub]
  have hba : b - a = 1 / (a + b) := by
    field_simp
    nlinarith
  have e1 : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
  rw [e1, hba, ← ha2]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos ha0 hb0, mul_pos (mul_pos ha0 ha0) hb0]

lemma rho6_lip (u v : ℝ) : |rho6 u - rho6 v| ≤ 2 * |u - v| := by
  unfold rho6
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 (2 - 2 * |u|)) 0 (min 1 (2 - 2 * |v|))
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (2 - 2 * |u|) 1 (2 - 2 * |v|)
  have h3 : |(2 - 2 * |u|) - (2 - 2 * |v|)| ≤ 2 * |u - v| := by
    rw [show (2 - 2 * |u|) - (2 - 2 * |v|) = 2 * (|v| - |u|) by ring, abs_mul, abs_two]
    have := abs_abs_sub_abs_le_abs_sub v u
    rw [abs_sub_comm v u] at this
    linarith
  have h4 : max |(1 : ℝ) - 1| |(2 - 2 * |u|) - (2 - 2 * |v|)| ≤ 2 * |u - v| := by
    rw [sub_self, abs_zero]
    exact max_le (by positivity) h3
  have h5 : max |(0 : ℝ) - 0| |min 1 (2 - 2 * |u|) - min 1 (2 - 2 * |v|)| ≤ 2 * |u - v| := by
    rw [sub_self, abs_zero]
    exact max_le (by positivity) (h2.trans h4)
  linarith

lemma rho6_nonneg (u : ℝ) : 0 ≤ rho6 u := le_max_left _ _
lemma rho6_le_one (u : ℝ) : rho6 u ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma log_succ_sub_le (m : ℝ) (hm : 1 ≤ m) : Real.log (m + 1) - Real.log m ≤ 1 / m := by
  have hm0 : 0 < m := by linarith
  rw [← Real.log_div (by linarith) hm0.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < (m + 1) / m by positivity)
  have e : (m + 1) / m - 1 = 1 / m := by field_simp; ring
  linarith

/-- the per-step bound `|w̃(m+1) − w̃(m)| ≤ (2π)⁻¹·(3T + 1.5T²)/(m√m)` for `m ≥ 1`, `T ≥ 0`. -/
lemma wmod_step (T s : ℝ) (hT : 0 ≤ T) (m : ℕ) (hm : 1 ≤ m) :
    ‖wmod T s (m + 1) - wmod T s m‖
      ≤ (2 * Real.pi)⁻¹ * (3 * T + (3 / 2) * T ^ 2) / ((m : ℝ) * Real.sqrt m) := by
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
  -- D bounds
  have hD1 : ‖D (m + 1)‖ ≤ T := DTFacts.DT_norm_le T _ hT
  have hDd : ‖D (m + 1) - D m‖ ≤ (3 / 2) * T ^ 2 * (1 / (m : ℝ)) := by
    simp only [hD]
    refine (DTFacts.DT_lipschitz T _ _ hT).trans ?_
    push_cast
    rw [show s - Real.log ((m : ℝ) + 1) - (s - Real.log (m : ℝ))
      = -(Real.log ((m : ℝ) + 1) - Real.log m) by ring, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 (by linarith)))]
    exact mul_le_mul_of_nonneg_left (log_succ_sub_le (m : ℝ) hmR) (by positivity)
  rw [hsplit, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have t1 : |g (m + 1) - g m| * ‖D (m + 1)‖ ≤ (2 * Real.pi)⁻¹ * (3 / ((m : ℝ) * Real.sqrt m)) * T :=
    mul_le_mul hgd hD1 (norm_nonneg _) (by positivity)
  have t2 : |g m| * ‖D (m + 1) - D m‖
      ≤ (2 * Real.pi)⁻¹ * (Real.sqrt m)⁻¹ * ((3 / 2) * T ^ 2 * (1 / (m : ℝ))) :=
    mul_le_mul hgm hDd (norm_nonneg _) (by positivity)
  have e : (2 * Real.pi)⁻¹ * (3 * T + (3 / 2) * T ^ 2) / ((m : ℝ) * Real.sqrt m)
      = (2 * Real.pi)⁻¹ * (3 / ((m : ℝ) * Real.sqrt m)) * T
        + (2 * Real.pi)⁻¹ * (Real.sqrt m)⁻¹ * ((3 / 2) * T ^ 2 * (1 / (m : ℝ))) := by
    field_simp
    try ring
  rw [e]
  linarith

end K6
end LemmaK
end ZetaShell
