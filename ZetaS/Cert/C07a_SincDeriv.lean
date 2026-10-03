/-
nodes/C07a_SincDeriv.lean — track C node C07a (L1_1b, 28 Sep 2026).
Depends on: none (Mathlib Real.sinc, Real.hasSum_sin).
Expected proof size: ≤ 120 lines.
PROVED (L5_1, 28 Sep 2026).
  * derivatives away from 0: quotient rule; at 0: a quadratic bound from Mathlib's `Real.sin_bound`/`cos_bound`;
  * `contDiff_sinc`: sinc = dslope sin 0 is analytic (Mathlib `has_fpower_series_dslope_fslope`);
  * series bounds: the series of sinc, −sinc′, −sinc″ are obtained from `Real.hasSum_sin`/`hasSum_cos`
    (shifted, combined termwise), their terms are antitone for 0 ≤ y ≤ 1, and Mathlib's alternating-series
    bounds give |remainder| ≤ first omitted term; y < 0 by parity.
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set Filter Topology Asymptotics

namespace ZetaS.CertV2

/-! ## closed forms away from 0 -/

private lemma sinc1_of_ne {y : ℝ} (hy : y ≠ 0) : sinc1 y = (Real.cos y - Real.sin y / y) / y := by
  rw [sinc1, if_neg hy, Real.sinc_of_ne_zero hy]

private lemma sinc2_of_ne {y : ℝ} (hy : y ≠ 0) : sinc2 y = -Real.sinc y - 2 * sinc1 y / y := by
  rw [sinc2, if_neg hy]

/-! ## derivatives at 0 from quadratic bounds -/

private lemma hasDerivAt_zero_of_sq_bound {f : ℝ → ℝ} {f' : ℝ}
    (h : ∀ y, |y| ≤ 1 → |f y - f 0 - y * f'| ≤ y ^ 2) : HasDerivAt f f' 0 := by
  rw [hasDerivAt_iff_isLittleO]
  have hO : (fun y => f y - f 0 - (y - 0) • f') =O[𝓝 0] (fun y : ℝ => y ^ 2) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with y hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hy
    simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (sq_nonneg y)]
    exact h y hy
  have := hO.trans_isLittleO (isLittleO_pow_id (𝕜 := ℝ) one_lt_two)
  simpa using this

private lemma sinc_quad_bound {y : ℝ} (hy : |y| ≤ 1) :
    |Real.sinc y - Real.sinc 0 - y * sinc1 0| ≤ y ^ 2 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hs := Real.sin_bound hy
  have hpos : 0 < |y| := abs_pos.mpr hy0
  rw [Real.sinc_zero, sinc1, if_pos rfl, mul_zero, sub_zero, Real.sinc_of_ne_zero hy0]
  have e : Real.sin y / y - 1 = (Real.sin y - y) / y := by rw [sub_div, div_self hy0]
  rw [e, abs_div, div_le_iff₀ hpos]
  have h1 : |Real.sin y - y| ≤ |Real.sin y - (y - y ^ 3 / 6)| + |y ^ 3 / 6| := by
    have := abs_add_le (Real.sin y - (y - y ^ 3 / 6)) (-(y ^ 3 / 6))
    rw [abs_neg, show Real.sin y - (y - y ^ 3 / 6) + -(y ^ 3 / 6) = Real.sin y - y by ring] at this
    exact this
  have h2 : |y ^ 3 / 6| = |y| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  have h3 : |y| ^ 5 ≤ |y| ^ 3 := pow_le_pow_of_le_one (abs_nonneg y) hy (by norm_num)
  have h4 : y ^ 2 * |y| = |y| ^ 3 := by rw [← sq_abs]; ring
  have h5 : 0 ≤ |y| ^ 3 := by positivity
  linarith

private lemma sinc1_quad_bound {y : ℝ} (hy : |y| ≤ 1) :
    |sinc1 y - sinc1 0 - y * sinc2 0| ≤ y ^ 2 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp [sinc1, sinc2]
  have hs := Real.sin_bound hy
  have hc := Real.cos_bound hy
  have hy2 : 0 < y ^ 2 := by positivity
  rw [sinc1_of_ne hy0, sinc1, if_pos rfl, sinc2, if_pos rfl]
  have e : (Real.cos y - Real.sin y / y) / y - 0 - y * (-1 / 3) =
      (y * (Real.cos y - (1 - y ^ 2 / 2)) - (Real.sin y - (y - y ^ 3 / 6))) / y ^ 2 := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hy2, div_le_iff₀ hy2]
  have h1 : |y * (Real.cos y - (1 - y ^ 2 / 2)) - (Real.sin y - (y - y ^ 3 / 6))| ≤
      |y| * |Real.cos y - (1 - y ^ 2 / 2)| + |Real.sin y - (y - y ^ 3 / 6)| := by
    have := abs_add_le (y * (Real.cos y - (1 - y ^ 2 / 2))) (-(Real.sin y - (y - y ^ 3 / 6)))
    rw [abs_neg, ← sub_eq_add_neg, abs_mul] at this
    exact this
  have h2 : |y| * |Real.cos y - (1 - y ^ 2 / 2)| ≤ |y| * (|y| ^ 4 * (5 / 96)) :=
    mul_le_mul_of_nonneg_left hc (abs_nonneg y)
  have h3 : |y| ^ 5 ≤ |y| ^ 4 := pow_le_pow_of_le_one (abs_nonneg y) hy (by norm_num)
  have h4 : y ^ 2 * y ^ 2 = |y| ^ 4 := by rw [← sq_abs y]; ring
  have h5 : |y| * (|y| ^ 4 * (5 / 96)) = |y| ^ 5 * (5 / 96) := by ring
  have h6 : 0 ≤ |y| ^ 4 := by positivity
  linarith

theorem hasDerivAt_sinc (y : ℝ) : HasDerivAt Real.sinc (sinc1 y) y := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact hasDerivAt_zero_of_sq_bound (fun y hy => sinc_quad_bound hy)
  · have hev : Real.sinc =ᶠ[𝓝 y] (fun z => Real.sin z / z) := by
      filter_upwards [eventually_ne_nhds hy] with z hz
      rw [Real.sinc_of_ne_zero hz]
    have hd := (Real.hasDerivAt_sin y).div (hasDerivAt_id' y) hy
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [sinc1_of_ne hy]
    field_simp

theorem hasDerivAt_sinc1 (y : ℝ) : HasDerivAt sinc1 (sinc2 y) y := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact hasDerivAt_zero_of_sq_bound (fun y hy => sinc1_quad_bound hy)
  · have hev : sinc1 =ᶠ[𝓝 y] (fun z => (Real.cos z - Real.sin z / z) / z) := by
      filter_upwards [eventually_ne_nhds hy] with z hz
      rw [sinc1_of_ne hz]
    have hd := ((Real.hasDerivAt_cos y).sub ((Real.hasDerivAt_sin y).div (hasDerivAt_id' y) hy)).div
      (hasDerivAt_id' y) hy
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.div_apply]
    rw [sinc2_of_ne hy, sinc1_of_ne hy, Real.sinc_of_ne_zero hy]
    field_simp
    ring

theorem contDiff_sinc : ContDiff ℝ 3 Real.sinc := by
  rw [contDiff_iff_contDiffAt]
  intro y
  apply AnalyticAt.contDiffAt
  rw [Real.sinc_eq_dslope]
  rcases eq_or_ne y 0 with rfl | hy
  · obtain ⟨p, hp⟩ := (Real.analyticAt_sin (x := 0))
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have hev : (fun z => Real.sin z / id z) =ᶠ[𝓝 y] dslope Real.sin 0 := by
      filter_upwards [eventually_ne_nhds hy] with z hz
      rw [dslope_of_ne _ hz, slope_def_field, Real.sin_zero, sub_zero, sub_zero, id]
    exact (Real.analyticAt_sin.div analyticAt_id hy).congr hev

/-! ## series -/

private lemma fac2 (j : ℕ) : ((2 * j + 2).factorial : ℝ) = (2 * j + 2) * (2 * j + 1).factorial := by
  rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring

private lemma fac3 (j : ℕ) :
    ((2 * j + 3).factorial : ℝ) = (2 * j + 3) * (2 * j + 2) * (2 * j + 1).factorial := by
  rw [show 2 * j + 3 = (2 * j + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring

private lemma fac5 (j : ℕ) :
    ((2 * j + 5).factorial : ℝ) = (2 * j + 5) * (2 * j + 4) * (2 * j + 3).factorial := by
  rw [show 2 * j + 5 = (2 * j + 3) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring

private lemma facpos (m : ℕ) : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m

/-- |l − S_N| ≤ f N for an alternating series with antitone terms. -/
private lemma alt_bound {f : ℕ → ℝ} {l : ℝ} (hf : Antitone f) (hs : HasSum (fun i => (-1) ^ i * f i) l)
    (N : ℕ) : |l - ∑ i ∈ Finset.range N, (-1) ^ i * f i| ≤ f N := by
  have ht := hs.tendsto_sum_nat
  have e : ∀ k : ℕ, ((-1 : ℝ)) ^ (2 * k) = 1 := fun k => by rw [pow_mul]; norm_num
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · have h1 := hf.alternating_series_le_tendsto ht k
    have h2 := hf.tendsto_le_alternating_series ht k
    rw [Finset.sum_range_succ, e, one_mul] at h2
    rw [abs_le]; constructor <;> linarith
  · have h1 := hf.alternating_series_le_tendsto ht (k + 1)
    have h2 := hf.tendsto_le_alternating_series ht k
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, pow_succ, e] at h1
    rw [abs_le]; constructor <;> linarith

private lemma hasSum_A {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j * (t ^ (2 * j) / ((2 * j + 1).factorial : ℝ))) (Real.sinc t) := by
  rw [Real.sinc_of_ne_zero ht]
  convert (Real.hasSum_sin t).div_const t using 1
  all_goals try (with_reducible_and_instances rfl)
  funext j
  have hF := (facpos (2 * j + 1)).ne'
  rw [pow_succ]
  field_simp

private lemma hasSum_B {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j * (2 * ((j : ℝ) + 1) * t ^ (2 * j + 1) / ((2 * j + 3).factorial : ℝ)))
      (-sinc1 t) := by
  have hs := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_sin t)
  have hc := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_cos t)
  have h := (hs.sub (hc.mul_left t)).div_const (t ^ 2)
  convert h using 1
  all_goals try (with_reducible_and_instances rfl)
  · funext j
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1) = 2 * j + 2 by ring, fac3, fac2]
    have hF := (facpos (2 * j + 1)).ne'
    have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
    have h2 : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  · rw [sinc1_of_ne ht]
    simp only [Finset.sum_range_one]
    norm_num
    field_simp
    ring

private lemma hasSum_C {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j *
      (2 * ((j : ℝ) + 1) * (2 * (j : ℝ) + 1) * t ^ (2 * j) / ((2 * j + 3).factorial : ℝ))) (-sinc2 t) := by
  have h := (hasSum_A ht).sub ((hasSum_B ht).mul_left (2 / t))
  convert h using 1
  all_goals try (with_reducible_and_instances rfl)
  · funext j
    rw [fac3]
    have hF := (facpos (2 * j + 1)).ne'
    have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
    have h2 : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  · rw [sinc2_of_ne ht]; ring

private lemma antiA {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (fun j : ℕ => t ^ (2 * j) / ((2 * j + 1).factorial : ℝ)) := by
  refine antitone_nat_of_succ_le fun n => ?_
  show t ^ (2 * (n + 1)) / ((2 * (n + 1) + 1).factorial : ℝ) ≤ t ^ (2 * n) / ((2 * n + 1).factorial : ℝ)
  rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring, fac3, show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
  have hF := facpos (2 * n + 1)
  have hp : 0 ≤ t ^ (2 * n) := by positivity
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hk : (1 : ℝ) ≤ (2 * n + 3) * (2 * n + 2) := by nlinarith
  have hX : 0 ≤ t ^ (2 * n) * (2 * n + 1).factorial := mul_nonneg hp hF.le
  rw [div_le_div_iff₀ (by positivity) hF]
  nlinarith [mul_le_mul_of_nonneg_left ht2 hX, mul_le_mul_of_nonneg_left hk hX]

private lemma antiB {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (fun j : ℕ => 2 * ((j : ℝ) + 1) * t ^ (2 * j + 1) / ((2 * j + 3).factorial : ℝ)) := by
  refine antitone_nat_of_succ_le fun n => ?_
  show 2 * (((n + 1 : ℕ) : ℝ) + 1) * t ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 3).factorial : ℝ)
    ≤ 2 * ((n : ℝ) + 1) * t ^ (2 * n + 1) / ((2 * n + 3).factorial : ℝ)
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 by ring, fac5, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, pow_add]
  push_cast
  have hF := facpos (2 * n + 3)
  have hp : 0 ≤ t ^ (2 * n + 1) := by positivity
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hk : ((n : ℝ) + 1 + 1) ≤ ((n : ℝ) + 1) * ((2 * n + 5) * (2 * n + 4)) := by
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3]
  have hX : 0 ≤ t ^ (2 * n + 1) * (2 * n + 3).factorial := mul_nonneg hp hF.le
  have hK0 : (0 : ℝ) ≤ (n : ℝ) + 1 + 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) hF]
  nlinarith [mul_le_mul_of_nonneg_left ht2 (mul_nonneg hX hK0), mul_le_mul_of_nonneg_left hk hX]

private lemma antiC {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (fun j : ℕ => 2 * ((j : ℝ) + 1) * (2 * (j : ℝ) + 1) * t ^ (2 * j) / ((2 * j + 3).factorial : ℝ)) := by
  refine antitone_nat_of_succ_le fun n => ?_
  show 2 * (((n + 1 : ℕ) : ℝ) + 1) * (2 * ((n + 1 : ℕ) : ℝ) + 1) * t ^ (2 * (n + 1)) /
      ((2 * (n + 1) + 3).factorial : ℝ)
    ≤ 2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * t ^ (2 * n) / ((2 * n + 3).factorial : ℝ)
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 by ring, fac5, show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
  push_cast
  have hF := facpos (2 * n + 3)
  have hp : 0 ≤ t ^ (2 * n) := by positivity
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hk : ((n : ℝ) + 1 + 1) * (2 * ((n : ℝ) + 1) + 1) ≤
      ((n : ℝ) + 1) * (2 * n + 1) * ((2 * n + 5) * (2 * n + 4)) := by
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3, pow_nonneg hn 4]
  have hX : 0 ≤ t ^ (2 * n) * (2 * n + 3).factorial := mul_nonneg hp hF.le
  have hK0 : (0 : ℝ) ≤ ((n : ℝ) + 1 + 1) * (2 * ((n : ℝ) + 1) + 1) := by positivity
  rw [div_le_div_iff₀ (by positivity) hF]
  nlinarith [mul_le_mul_of_nonneg_left ht2 (mul_nonneg hX hK0), mul_le_mul_of_nonneg_left hk hX]

private lemma core0 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.sinc t - ∑ j ∈ Finset.range 8, (-1 : ℝ) ^ j * t ^ (2 * j) / (Nat.factorial (2 * j + 1))| ≤
      |t| ^ 16 / Nat.factorial 17 := by
  rcases eq_or_lt_of_le ht0 with rfl | htp
  · norm_num [Finset.sum_range_succ]
  have hb := alt_bound (antiA ht0 ht1) (hasSum_A htp.ne') 8
  rw [abs_of_pos htp]
  simp only [mul_div_assoc]
  convert hb using 2

private lemma core1 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |sinc1 t - ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ (j + 1) * (2 * (j + 1)) * t ^ (2 * j + 1) / (Nat.factorial (2 * j + 3))|
      ≤ 16 * |t| ^ 15 / Nat.factorial 17 := by
  rcases eq_or_lt_of_le ht0 with rfl | htp
  · norm_num [sinc1, Finset.sum_range_succ]
  have hb := alt_bound (antiB ht0 ht1) (hasSum_B htp.ne') 7
  rw [abs_of_pos htp]
  have e : ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ (j + 1) * (2 * (j + 1)) * t ^ (2 * j + 1) / (Nat.factorial (2 * j + 3))
      = -∑ j ∈ Finset.range 7,
        (-1 : ℝ) ^ j * (2 * ((j : ℝ) + 1) * t ^ (2 * j + 1) / ((2 * j + 3).factorial : ℝ)) := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [e, show ∀ a b : ℝ, a - -b = -(-a - b) from fun a b => by ring, abs_neg]
  convert hb using 1
  norm_num

private lemma core2 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |sinc2 t - ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ (j + 1) * (2 * (j + 1)) * (2 * j + 1) * t ^ (2 * j) / (Nat.factorial (2 * j + 3))|
      ≤ 16 * 15 * |t| ^ 14 / Nat.factorial 17 := by
  rcases eq_or_lt_of_le ht0 with rfl | htp
  · norm_num [sinc2, Finset.sum_range_succ, Nat.factorial]
  have hb := alt_bound (antiC ht0 ht1) (hasSum_C htp.ne') 7
  rw [abs_of_pos htp]
  have e : ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ (j + 1) * (2 * (j + 1)) * (2 * j + 1) * t ^ (2 * j) /
        (Nat.factorial (2 * j + 3))
      = -∑ j ∈ Finset.range 7, (-1 : ℝ) ^ j *
        (2 * ((j : ℝ) + 1) * (2 * (j : ℝ) + 1) * t ^ (2 * j) / ((2 * j + 3).factorial : ℝ)) := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [e, show ∀ a b : ℝ, a - -b = -(-a - b) from fun a b => by ring, abs_neg]
  convert hb using 1
  norm_num

private lemma sinc1_neg (t : ℝ) : sinc1 (-t) = -sinc1 t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [sinc1]
  rw [sinc1_of_ne ht, sinc1_of_ne (neg_ne_zero.mpr ht), Real.cos_neg, Real.sin_neg, neg_div_neg_eq, div_neg]

private lemma sinc2_neg (t : ℝ) : sinc2 (-t) = sinc2 t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [sinc2]
  rw [sinc2_of_ne ht, sinc2_of_ne (neg_ne_zero.mpr ht), Real.sinc_neg, sinc1_neg, mul_neg, neg_div_neg_eq]

/-- power series of sinc, sinc′, sinc″ with alternating remainders for |y| ≤ 1/2 (8 terms). -/
theorem sinc_series_bounds {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |Real.sinc y - ∑ j ∈ Finset.range 8, (-1 : ℝ) ^ j * y ^ (2 * j) / (Nat.factorial (2 * j + 1))| ≤ |y| ^ 16 / Nat.factorial 17 ∧
    |sinc1 y - ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ (j + 1) * (2 * (j + 1)) * y ^ (2 * j + 1) / (Nat.factorial (2 * j + 3))|
      ≤ 16 * |y| ^ 15 / Nat.factorial 17 ∧
    |sinc2 y - ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ (j + 1) * (2 * (j + 1)) * (2 * j + 1) * y ^ (2 * j) / (Nat.factorial (2 * j + 3))|
      ≤ 16 * 15 * |y| ^ 14 / Nat.factorial 17 := by
  rcases le_total 0 y with h0 | h0
  · have h1 : y ≤ 1 := by have := le_abs_self y; linarith
    exact ⟨core0 h0 h1, core1 h0 h1, core2 h0 h1⟩
  · obtain ⟨t, rfl⟩ : ∃ t, y = -t := ⟨-y, (neg_neg y).symm⟩
    have t0 : 0 ≤ t := by linarith
    have t1 : t ≤ 1 := by rw [abs_neg, abs_of_nonneg t0] at hy; linarith
    have ev : ∀ j : ℕ, (-t) ^ (2 * j) = t ^ (2 * j) := fun j => by rw [pow_mul, pow_mul, neg_sq]
    have od : ∀ j : ℕ, (-t) ^ (2 * j + 1) = -t ^ (2 * j + 1) := fun j => by rw [pow_succ, ev, pow_succ]; ring
    simp only [ev, od, abs_neg, Real.sinc_neg, sinc1_neg, sinc2_neg]
    refine ⟨core0 t0 t1, ?_, core2 t0 t1⟩
    simp only [mul_neg, neg_div, Finset.sum_neg_distrib]
    rw [show ∀ a b : ℝ, -a - -b = -(a - b) from fun a b => by ring, abs_neg]
    exact core1 t0 t1

end ZetaS.CertV2
