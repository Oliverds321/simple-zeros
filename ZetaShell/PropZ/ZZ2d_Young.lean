/-
L7_5 (28 Sep 2026), round 7: `ZO_young'` (the statement of the leaf `ZO_young`), Young's inequality
  `μ² ∫ |I_ρ(ξ)|² dξ ≤ (∫_{t>0} |H_ρ|²) (∫ |f_j|)²`,   `I_ρ(ξ) = ∫_{t>0} H_ρ(t) f_j(μ(t−ξ)) dt`.
With `φ = |1_{t>0} H_ρ|` (bounded, compact support) and `w_ξ(t) = |f_j(μ(t−ξ))|`, `W = ∫ w_ξ = μ^{−1} ∫|f_j|`:
  `|I(ξ)| ≤ ∫ φ w_ξ`,  `(∫ φ w_ξ)² ≤ (∫ φ² w_ξ) W`  (from `2φw ≤ λφ²w + w/λ`, `cs_amgm`),
  `∫_ξ ∫_t φ² w_ξ = W ∫ φ²`  (integrable on the product by `Integrable.convolution_integrand`; Fubini).
-/
import ZetaShell.PropZ.ZZ0_Defs
import ZetaShell.PropZ.ZB_As

open MeasureTheory

namespace ZetaShell.PropZ

theorem fj_smooth (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (fj f j) ∧ HasCompactSupport (fj f j)
  | 0 => by
    simp only [fj]
    exact ⟨hf.smooth, IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f)
      (hf.supp.trans Set.Ioo_subset_Icc_self)⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := fj_smooth f hf j
    simp only [fj]
    exact ⟨contDiff_id.mul (contDiff_infty_iff_deriv.mp h1).2, h2.deriv.mul_left (f := fun z : ℝ => z)⟩

theorem norm_DT_le_abs (T v : ℝ) : ‖DT T v‖ ≤ |T| := by
  unfold DT
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T) (C := 1)
    (f := fun τ : ℝ => Complex.exp (Complex.I * τ * v)) (fun τ _ => by
      rw [show Complex.I * (τ : ℂ) * v = ((τ * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])
  rw [show 2 * T - T = T by ring, one_mul] at h
  exact h

theorem Hrho_measurable (κ : ℝ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (T : ℝ) (ρ : ℂ) :
    Measurable (Hrho T κ Ξ ρ) := by
  unfold Hrho
  have h1 : Measurable (fun t : ℝ => DT T (-Real.log t)) :=
    (ZetaShell.DTFacts.DTf_continuous T).measurable.comp Real.measurable_log.neg
  have h2 : Measurable (fun t : ℝ => ((Ξ (Real.log t / κ) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (hΞ.smooth.continuous.measurable.comp (Real.measurable_log.div_const κ))
  have h3 : Measurable (fun t : ℝ => (t : ℂ) ^ (ρ - 3 / 2)) := Complex.measurable_ofReal.pow_const _
  exact (h1.mul h2).mul h3

theorem Hrho_ind_bound (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (T : ℝ) (ρ : ℂ)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (t : ℝ) :
    ‖(Set.Ioi (0 : ℝ)).indicator (Hrho T κ Ξ ρ) t‖
      ≤ |T| * Real.exp (2 * κ) * (Set.Icc (Real.exp (-κ)) (Real.exp κ)).indicator (fun _ => (1 : ℝ)) t := by
  have hR0 : 0 ≤ |T| * Real.exp (2 * κ) * (Set.Icc (Real.exp (-κ)) (Real.exp κ)).indicator (fun _ => (1 : ℝ)) t :=
    mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) t)
  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
  swap
  · rw [Set.indicator_of_notMem ht, norm_zero]; exact hR0
  rw [Set.indicator_of_mem ht]
  have ht0 : 0 < t := ht
  by_cases hz : Ξ (Real.log t / κ) = 0
  · have : Hrho T κ Ξ ρ t = 0 := by unfold Hrho; rw [hz]; simp
    rw [this, norm_zero]; exact hR0
  have hmem : Real.log t / κ ∈ Set.Ioo (-1 : ℝ) 1 := hΞ.supp (subset_tsupport _ hz)
  set L := Real.log t with hL
  have hLk : |L| < κ := by
    have h := abs_lt.mpr ⟨hmem.1, hmem.2⟩
    rw [abs_div, abs_of_pos hκ, div_lt_one hκ] at h; exact h
  have htI : t ∈ Set.Icc (Real.exp (-κ)) (Real.exp κ) := by
    have e : t = Real.exp L := by rw [hL, Real.exp_log ht0]
    have hL' := abs_lt.mp hLk
    rw [e]; exact ⟨Real.exp_le_exp.mpr hL'.1.le, Real.exp_le_exp.mpr hL'.2.le⟩
  rw [Set.indicator_of_mem htI, mul_one]
  have hpow : ‖(t : ℂ) ^ (ρ - 3 / 2)‖ ≤ Real.exp (2 * κ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Real.rpow_def_of_pos ht0, ← hL]
    have hre : (ρ - 3 / 2).re = ρ.re - 3 / 2 := by simp
    rw [hre]
    apply Real.exp_le_exp.mpr
    have hy : |ρ.re - 3 / 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have h5 : |L| * |ρ.re - 3 / 2| ≤ κ * 2 := mul_le_mul hLk.le hy (abs_nonneg _) hκ.le
    have := abs_mul L (ρ.re - 3 / 2)
    linarith [le_abs_self (L * (ρ.re - 3 / 2))]
  have hXi : ‖((Ξ (L / κ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΞ.nonneg _)]; exact hΞ.le_one _
  unfold Hrho; rw [← hL, norm_mul, norm_mul]
  have h1 := norm_DT_le_abs T (-L)
  calc ‖DT T (-L)‖ * ‖((Ξ (L / κ) : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (ρ - 3 / 2)‖
      ≤ |T| * 1 * Real.exp (2 * κ) := by gcongr
    _ = |T| * Real.exp (2 * κ) := by ring

theorem cs_amgm (a A W : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (h : ∀ l : ℝ, 0 < l → 2 * a ≤ l * A + W / l) : a ^ 2 ≤ A * W := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0]; nlinarith [mul_nonneg hA hW]
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · exfalso
    have h1 := h ((W + 1) / a) (by positivity)
    rw [← hA0, mul_zero, zero_add, div_div_eq_mul_div] at h1
    have h2 : W * a / (W + 1) < a := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  · have hAne := hApos.ne'
    have hane := hapos.ne'
    have h1 := h (a / A) (by positivity)
    have e : a / A * A = a := by field_simp
    rw [e, div_div_eq_mul_div] at h1
    have h3 : a ≤ W * A / a := by linarith
    rw [le_div_iff₀ hapos] at h3
    nlinarith

theorem ZO_young' (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (j : ℕ) (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (μ : ℝ) (hμ : 0 < μ) :
    μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2)
      ≤ (∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖ ^ 2) * (∫ z, |fj f j z|) ^ 2 := by
  obtain ⟨hgs, hgc⟩ := fj_smooth f hf j
  have hgi : Integrable (fj f j) := hgs.continuous.integrable_of_hasCompactSupport hgc
  -- the weight `b(z) = |f_j(μz)|`, `W = ∫ b`
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℝ, b = fun z => |fj f j (μ * z)| := ⟨_, rfl⟩
  have hbi : Integrable b := by rw [hb]; exact (hgi.comp_mul_left' hμ.ne').abs
  have hb0 : ∀ z, 0 ≤ b z := fun z => by rw [hb]; exact abs_nonneg _
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∫ z, b z := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact integral_nonneg hb0
  have hμW : μ * W = ∫ z, |fj f j z| := by
    rw [hW, hb, MeasureTheory.Measure.integral_comp_mul_left (fun z => |fj f j z|) μ, abs_of_pos (inv_pos.mpr hμ), smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]
  obtain ⟨bn, hbn⟩ : ∃ bn : ℝ → ℝ, bn = fun z => |fj f j ((-μ) * z)| := ⟨_, rfl⟩
  have hbni : Integrable bn := by rw [hbn]; exact (hgi.comp_mul_left' (neg_ne_zero.mpr hμ.ne')).abs
  -- the amplitude `φ = |1_{t>0} H_ρ|`
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun t => ‖(Set.Ioi (0 : ℝ)).indicator (Hrho T κ Ξ ρ) t‖ := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]; exact ((Hrho_measurable κ Ξ hΞ T ρ).indicator measurableSet_Ioi).norm
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => by rw [hφ]; exact norm_nonneg _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |T| * Real.exp (2 * κ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hφK : ∀ t, φ t ≤ B * (Set.Icc (Real.exp (-κ)) (Real.exp κ)).indicator (fun _ => (1 : ℝ)) t := fun t => by
    rw [hφ, hB]; exact Hrho_ind_bound κ hκ Ξ hΞ T ρ hρ0 hρ1 t
  have hφB : ∀ t, φ t ≤ B := fun t => by
    refine (hφK t).trans ?_
    by_cases hm : t ∈ Set.Icc (Real.exp (-κ)) (Real.exp κ)
    · rw [Set.indicator_of_mem hm, mul_one]
    · rw [Set.indicator_of_notMem hm, mul_zero]; exact hB0
  have hφ2i : Integrable (fun t => φ t ^ 2) := by
    have hIi : Integrable ((Set.Icc (Real.exp (-κ)) (Real.exp κ)).indicator (fun _ => B ^ 2)) :=
      (integrableOn_const (s := Set.Icc (Real.exp (-κ)) (Real.exp κ)) (C := B ^ 2)
        (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
    refine Integrable.mono' hIi (hφm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := hφK t
    by_cases hm : t ∈ Set.Icc (Real.exp (-κ)) (Real.exp κ)
    · rw [Set.indicator_of_mem hm] at h ⊢; rw [mul_one] at h
      exact pow_le_pow_left₀ (hφ0 t) h 2
    · rw [Set.indicator_of_notMem hm] at h ⊢; rw [mul_zero] at h
      have : φ t = 0 := le_antisymm h (hφ0 t)
      rw [this]; norm_num
  -- per `ξ`
  have hwi : ∀ ξ : ℝ, Integrable (fun t => b (t - ξ)) := fun ξ => hbi.comp_sub_right ξ
  have hWξ : ∀ ξ : ℝ, ∫ t, b (t - ξ) = W := fun ξ => by rw [hW]; exact integral_sub_right_eq_self (μ := volume) b ξ
  have hφwi : ∀ ξ : ℝ, Integrable (fun t => φ t * b (t - ξ)) := fun ξ =>
    (hwi ξ).bdd_mul hφm.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 t)]; exact hφB t)
  have hφ2wi : ∀ ξ : ℝ, Integrable (fun t => φ t ^ 2 * b (t - ξ)) := fun ξ =>
    (hwi ξ).bdd_mul (hφm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hφ0 t) (hφB t) 2)
  have hIξ : ∀ ξ : ℝ, ‖Irho T κ Ξ f j ρ μ ξ‖ ≤ ∫ t, φ t * b (t - ξ) := by
    intro ξ
    unfold Irho
    rw [← integral_indicator measurableSet_Ioi]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext t
    rw [Set.indicator_mul_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, hφ, hb]
  have hCS : ∀ ξ : ℝ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2 ≤ W * ∫ t, φ t ^ 2 * b (t - ξ) := by
    intro ξ
    have ha0 : 0 ≤ ∫ t, φ t * b (t - ξ) := integral_nonneg fun t => mul_nonneg (hφ0 t) (hb0 _)
    have hA0 : 0 ≤ ∫ t, φ t ^ 2 * b (t - ξ) := integral_nonneg fun t => mul_nonneg (sq_nonneg _) (hb0 _)
    have hcs := cs_amgm (∫ t, φ t * b (t - ξ)) (∫ t, φ t ^ 2 * b (t - ξ)) W ha0 hA0 hW0 (fun l hl => by
      have hpw : ∀ t, 2 * (φ t * b (t - ξ)) ≤ l * (φ t ^ 2 * b (t - ξ)) + b (t - ξ) / l := fun t => by
        have hq : 0 ≤ b (t - ξ) * (l * φ t - 1) ^ 2 / l := div_nonneg (mul_nonneg (hb0 _) (sq_nonneg _)) hl.le
        have e : l * (φ t ^ 2 * b (t - ξ)) + b (t - ξ) / l - 2 * (φ t * b (t - ξ))
            = b (t - ξ) * (l * φ t - 1) ^ 2 / l := by field_simp; ring
        linarith
      calc 2 * (∫ t, φ t * b (t - ξ)) = ∫ t, 2 * (φ t * b (t - ξ)) := (integral_const_mul _ _).symm
        _ ≤ ∫ t, (l * (φ t ^ 2 * b (t - ξ)) + b (t - ξ) / l) :=
            integral_mono ((hφwi ξ).const_mul 2) (((hφ2wi ξ).const_mul l).add ((hwi ξ).div_const l)) hpw
        _ = l * (∫ t, φ t ^ 2 * b (t - ξ)) + (∫ t, b (t - ξ)) / l := by
            rw [integral_add ((hφ2wi ξ).const_mul l) ((hwi ξ).div_const l), integral_const_mul, integral_div]
        _ = l * (∫ t, φ t ^ 2 * b (t - ξ)) + W / l := by rw [hWξ])
    calc ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2 ≤ (∫ t, φ t * b (t - ξ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hIξ ξ) 2
      _ ≤ (∫ t, φ t ^ 2 * b (t - ξ)) * W := hcs
      _ = W * ∫ t, φ t ^ 2 * b (t - ξ) := by ring
  -- the product integrand and Fubini
  have hF : Integrable (fun p : ℝ × ℝ => φ p.2 ^ 2 * b (p.2 - p.1)) (volume.prod volume) := by
    have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hφ2i hbni
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [ContinuousLinearMap.mul_apply', hb, hbn]
    rw [show -μ * (p.1 - p.2) = μ * (p.2 - p.1) by ring]
  have hAint : Integrable (fun ξ : ℝ => ∫ t, φ t ^ 2 * b (t - ξ)) := hF.integral_prod_left
  have hswap : (∫ ξ : ℝ, ∫ t, φ t ^ 2 * b (t - ξ)) = ∫ t : ℝ, ∫ ξ, φ t ^ 2 * b (t - ξ) :=
    integral_integral_swap (f := fun ξ t => φ t ^ 2 * b (t - ξ)) hF
  have hinner : ∀ t : ℝ, (∫ ξ, φ t ^ 2 * b (t - ξ)) = φ t ^ 2 * W := fun t => by
    rw [integral_const_mul, integral_sub_left_eq_self (μ := volume) b t, ← hW]
  have hφ2 : (∫ t, φ t ^ 2) = ∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖ ^ 2 := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext t
    rw [hφ]
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem ht]
    · simp only [Set.indicator_of_notMem ht, norm_zero]; norm_num
  have hmain : (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ W * ((∫ t, φ t ^ 2) * W) := by
    calc (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ ∫ ξ, W * ∫ t, φ t ^ 2 * b (t - ξ) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by
            simp only [Pi.zero_apply]; positivity) (hAint.const_mul W) (Filter.Eventually.of_forall hCS)
      _ = W * ∫ ξ, ∫ t, φ t ^ 2 * b (t - ξ) := integral_const_mul _ _
      _ = W * ∫ t, φ t ^ 2 * W := by rw [hswap]; simp only [hinner]
      _ = W * ((∫ t, φ t ^ 2) * W) := by rw [integral_mul_const]
  calc μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ μ ^ 2 * (W * ((∫ t, φ t ^ 2) * W)) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg μ)
    _ = (∫ t, φ t ^ 2) * (μ * W) ^ 2 := by ring
    _ = _ := by rw [hμW, hφ2]

end ZetaShell.PropZ
