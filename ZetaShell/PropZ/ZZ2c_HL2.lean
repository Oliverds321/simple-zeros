/-
L7_5 (28 Sep 2026), round 6: `ZO_H_L2'`: `∫_{t>0} |H_ρ(t)|² ≤ 972 c₁ T`, `c₁ = ∫ (1+x²)^{−1}`, for `0 < β < 1`, `T ≥ 2`.
  `|D_T(v)| ≤ T`, `|D_T(v)||v| ≤ 2` (closed form), hence `|D_T(v)|² (1 + (Tv/2)²) ≤ 2T²`;
  on the support `|log t| < κ ≤ 1`: `|t^{ρ−3/2}| ≤ e² ≤ 9`, `(t−1)² ≤ 9 log² t`;
  majorant `162 T² (1 + (T(t−1)/6)²)^{−1}`, integral `162 T² (6/T) c₁`.
-/
import ZetaShell.PropZ.ZZ0_Defs
import ZetaShell.PropZ.ZB_As

open MeasureTheory

namespace ZetaShell.PropZ

theorem DTf_mul_abs_le (T v : ℝ) (hT : 0 ≤ T) : ‖ZetaShell.DTFacts.DTf T v‖ * |v| ≤ 2 := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, abs_zero, mul_zero]; norm_num
  rcases eq_or_lt_of_le hT with hT0 | hTp
  · rw [← hT0, ZetaShell.DTFacts.DTf_eq_closed]; simp
  have hz : (Complex.I * (T : ℂ) * (v : ℂ)) ≠ 0 := by
    have : (T : ℂ) ≠ 0 := by exact_mod_cast hTp.ne'
    have : (v : ℂ) ≠ 0 := by exact_mod_cast hv
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by assumption)) (by assumption)
  have ez : Complex.I * (T : ℂ) * (v : ℂ) = ((T * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hexp1 : ‖Complex.exp (Complex.I * (T : ℂ) * (v : ℂ))‖ = 1 := by
    rw [ez, Complex.norm_exp_ofReal_mul_I]
  have hnz : ‖Complex.I * (T : ℂ) * (v : ℂ)‖ = T * |v| := by
    rw [ez, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hTp]
  rw [ZetaShell.DTFacts.DTf_eq_closed, ZetaShell.DTFacts.gexp_of_ne hz, norm_mul, norm_mul, norm_div, hexp1,
    hnz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTp]
  have hv' : 0 < |v| := abs_pos.mpr hv
  have e : T * 1 * (‖Complex.exp (Complex.I * (T : ℂ) * (v : ℂ)) - 1‖ / (T * |v|)) * |v|
      = ‖Complex.exp (Complex.I * (T : ℂ) * (v : ℂ)) - 1‖ := by field_simp
  rw [e]
  calc ‖Complex.exp (Complex.I * (T : ℂ) * (v : ℂ)) - 1‖
      ≤ ‖Complex.exp (Complex.I * (T : ℂ) * (v : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [hexp1, norm_one]; norm_num

theorem DTf_sq_le (T v : ℝ) (hT : 0 ≤ T) :
    ‖ZetaShell.DTFacts.DTf T v‖ ^ 2 * (1 + (T * v / 2) ^ 2) ≤ 2 * T ^ 2 := by
  set d := ‖ZetaShell.DTFacts.DTf T v‖ with hd
  have d0 : 0 ≤ d := norm_nonneg _
  have h1 : d ≤ T := ZetaShell.DTFacts.norm_DTf_le hT v
  have h2 : d * |v| ≤ 2 := DTf_mul_abs_le T v hT
  have h1' : d ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ d0 h1 2
  have h2' : (d * |v|) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (mul_nonneg d0 (abs_nonneg v)) h2 2
  have h3 : T ^ 2 * (d * |v|) ^ 2 ≤ T ^ 2 * 2 ^ 2 := mul_le_mul_of_nonneg_left h2' (sq_nonneg T)
  have e : d ^ 2 * (1 + (T * v / 2) ^ 2) = d ^ 2 + T ^ 2 * (d * |v|) ^ 2 / 4 := by
    rw [mul_pow d |v|, sq_abs]; ring
  rw [e]; linarith

theorem ZO_H_L2' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 →
      (∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖ ^ 2) ≤ C * T := by
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = ∫ x : ℝ, (1 + x ^ 2)⁻¹ := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; exact integral_nonneg fun x => by positivity
  refine ⟨972 * c₁, by positivity, fun T hT ρ hρ0 hρ1 => ?_⟩
  have hTp : 0 < T := by linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 6 / T := ⟨_, rfl⟩
  have hbp : 0 < b := by rw [hb]; positivity
  have hGi : Integrable (fun t : ℝ => 162 * T ^ 2 * (1 + ((t - 1) / b) ^ 2)⁻¹) :=
    ((integrable_inv_one_add_sq.comp_div hbp.ne').comp_sub_right 1).const_mul _
  have hG0 : ∀ t : ℝ, 0 ≤ 162 * T ^ 2 * (1 + ((t - 1) / b) ^ 2)⁻¹ := fun t => by positivity
  have hGint : (∫ t : ℝ, 162 * T ^ 2 * (1 + ((t - 1) / b) ^ 2)⁻¹) = 972 * c₁ * T := by
    rw [integral_const_mul]
    have h1 := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => (1 + (y / b) ^ 2)⁻¹) 1
    have h2 := MeasureTheory.Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) b
    beta_reduce at h1 h2
    rw [h1, h2, abs_of_pos hbp, smul_eq_mul, ← hc₁, hb]
    field_simp
    ring
  have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he2 : Real.exp 2 ≤ 9 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hpw : ∀ t : ℝ, (Set.Ioi (0 : ℝ)).indicator (fun t => ‖Hrho T κ Ξ ρ t‖ ^ 2) t
      ≤ 162 * T ^ 2 * (1 + ((t - 1) / b) ^ 2)⁻¹ := by
    intro t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    swap
    · rw [Set.indicator_of_notMem ht]; exact hG0 t
    rw [Set.indicator_of_mem ht]
    have ht0 : 0 < t := ht
    by_cases hz : Ξ (Real.log t / κ) = 0
    · have : Hrho T κ Ξ ρ t = 0 := by unfold Hrho; rw [hz]; simp
      rw [this, norm_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact hG0 t
    have hmem : Real.log t / κ ∈ Set.Ioo (-1 : ℝ) 1 := hΞ.supp (subset_tsupport _ hz)
    set L := Real.log t with hL
    have hLk : |L| < κ := by
      have h := abs_lt.mpr ⟨hmem.1, hmem.2⟩
      rw [abs_div, abs_of_pos hκ, div_lt_one hκ] at h; exact h
    have hL1 : |L| ≤ 1 := by linarith
    -- the power factor
    have hpow : ‖(t : ℂ) ^ (ρ - 3 / 2)‖ ≤ 9 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Real.rpow_def_of_pos ht0, ← hL]
      have hre : (ρ - 3 / 2).re = ρ.re - 3 / 2 := by simp
      rw [hre]
      have hy : |ρ.re - 3 / 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
      have : L * (ρ.re - 3 / 2) ≤ 2 := by
        have := abs_mul L (ρ.re - 3 / 2)
        have h5 : |L| * |ρ.re - 3 / 2| ≤ 1 * 2 := mul_le_mul hL1 hy (abs_nonneg _) (by norm_num)
        linarith [le_abs_self (L * (ρ.re - 3 / 2))]
      exact (Real.exp_le_exp.mpr this).trans he2
    have hXi : ‖((Ξ (L / κ) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΞ.nonneg _)]; exact hΞ.le_one _
    have hH : ‖Hrho T κ Ξ ρ t‖ ≤ ‖ZetaShell.DTFacts.DTf T (-L)‖ * 9 := by
      unfold Hrho; rw [← hL, DT_eq_DTf, norm_mul, norm_mul]
      have := norm_nonneg (ZetaShell.DTFacts.DTf T (-L))
      calc ‖ZetaShell.DTFacts.DTf T (-L)‖ * ‖((Ξ (L / κ) : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (ρ - 3 / 2)‖
          ≤ ‖ZetaShell.DTFacts.DTf T (-L)‖ * 1 * 9 := by gcongr
        _ = ‖ZetaShell.DTFacts.DTf T (-L)‖ * 9 := by ring
    have hH2 : ‖Hrho T κ Ξ ρ t‖ ^ 2 ≤ 81 * ‖ZetaShell.DTFacts.DTf T (-L)‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hH 2
      linarith
    -- `(t−1)² ≤ 9 L²`
    have htL : (t - 1) ^ 2 ≤ 9 * L ^ 2 := by
      rcases le_or_gt 1 t with h1 | h1
      · have hlog := Real.one_sub_inv_le_log_of_pos ht0
        rw [← hL] at hlog
        have ht3 : t ≤ 3 := by
          have : t = Real.exp L := by rw [hL, Real.exp_log ht0]
          rw [this]; exact (Real.exp_le_exp.mpr (by linarith [le_abs_self L])).trans he1
        have htl : t - 1 ≤ t * L := by
          have := mul_le_mul_of_nonneg_left hlog ht0.le
          rw [mul_sub, mul_one, mul_inv_cancel₀ ht0.ne'] at this; linarith
        have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg h1
        have : t * L ≤ 3 * L := mul_le_mul_of_nonneg_right ht3 hL0
        nlinarith
      · have hlog := Real.log_le_sub_one_of_pos ht0
        rw [← hL] at hlog
        nlinarith
    have hsq := DTf_sq_le T (-L) hTp.le
    have hden : ((t - 1) / b) ^ 2 ≤ (T * -L / 2) ^ 2 := by
      rw [hb, div_div_eq_mul_div]
      have e1 : ((t - 1) * T / 6) ^ 2 = T ^ 2 * (t - 1) ^ 2 / 36 := by ring
      have e2 : (T * -L / 2) ^ 2 = T ^ 2 * (9 * L ^ 2) / 36 := by ring
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_left htL (sq_nonneg T)
      linarith
    have hq : 0 < 1 + ((t - 1) / b) ^ 2 := by positivity
    have hD : ‖ZetaShell.DTFacts.DTf T (-L)‖ ^ 2 ≤ 2 * T ^ 2 * (1 + ((t - 1) / b) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hq]
      have := mul_le_mul_of_nonneg_left (show 1 + ((t - 1) / b) ^ 2 ≤ 1 + (T * -L / 2) ^ 2 by linarith)
        (sq_nonneg ‖ZetaShell.DTFacts.DTf T (-L)‖)
      linarith
    have hinv : 0 ≤ (1 + ((t - 1) / b) ^ 2)⁻¹ := by positivity
    nlinarith
  rw [← integral_indicator measurableSet_Ioi]
  calc (∫ t, (Set.Ioi (0 : ℝ)).indicator (fun t => ‖Hrho T κ Ξ ρ t‖ ^ 2) t)
      ≤ ∫ t : ℝ, 162 * T ^ 2 * (1 + ((t - 1) / b) ^ 2)⁻¹ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => by
          simp only [Pi.zero_apply]; exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) t)
          hGi (Filter.Eventually.of_forall hpw)
    _ = 972 * c₁ * T := hGint

end ZetaShell.PropZ
