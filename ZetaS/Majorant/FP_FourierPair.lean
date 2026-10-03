/-
Node FP (track M-cert, L2_2, 28 Sep 2026) — the Fourier pair sinc² ↔ triangle:

  ∫_ℝ sinc(πu)² cos(2πωu) du = Λ(ω) = (1 − |ω|)₊   for every real ω.

Proof: Λ is continuous, integrable (compact support), and its Fourier transform is sinc(π·)² (computed on [−1, 1]:
the sine part vanishes by oddness, and 2∫₀¹(1 − v)cos(av)dv = 2(1 − cos a)/a² = sinc(a/2)² with a = 2πw, from the
antiderivative (1 − v)sin(av)/a − cos(av)/a²), which is integrable; Mathlib's Fourier inversion
(`Continuous.fourierInv_fourier_eq`) then gives Λ(ω) = ∫ e(vω) sinc(πv)² dv, whose real part is the claim.
-/
import ZetaS.Interfaces
import ZetaS.Majorant.MCert_Majorant

open Real MeasureTheory Set Complex
open scoped FourierTransform

noncomputable section

namespace ZetaS

namespace MCert

lemma tri_continuous : Continuous tri := by
  unfold tri; fun_prop

lemma tri_neg (u : ℝ) : tri (-u) = tri u := by unfold tri; rw [abs_neg]

lemma tri_of_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : tri u = 1 - u := by
  unfold tri; rw [abs_of_nonneg h0, max_eq_left (by linarith)]

lemma tri_hasCompactSupport : HasCompactSupport tri := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => ?_
  apply tri_eq_zero
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma tri_integrable : Integrable tri := tri_continuous.integrable_of_hasCompactSupport tri_hasCompactSupport

/-- ∫₀¹ (1 − v) cos(a v) dv = (1 − cos a)/a² for a ≠ 0. -/
lemma integral_one_sub_mul_cos {a : ℝ} (ha : a ≠ 0) :
    ∫ v in (0 : ℝ)..1, (1 - v) * Real.cos (a * v) = (1 - Real.cos a) / a ^ 2 := by
  have hderiv : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v => (1 - v) * Real.sin (a * v) / a - Real.cos (a * v) / a ^ 2)
      ((1 - v) * Real.cos (a * v)) v := by
    intro v _
    have h1 : HasDerivAt (fun v => a * v) a v := by simpa using (hasDerivAt_id' v).const_mul a
    have hs := h1.sin
    have hc := h1.cos
    have h2 := (((hasDerivAt_id' v).const_sub 1).mul hs).div_const a
    have h3 := hc.div_const (a ^ 2)
    refine (h2.sub h3).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp only [sub_self, zero_mul, Real.sin_zero, mul_zero, zero_div, mul_one, Real.cos_zero, sub_zero]
    ring
  · apply ContinuousOn.intervalIntegrable
    exact (Continuous.continuousOn (by fun_prop))

/-- the cosine transform of Λ. -/
lemma tri_cos_transform (w : ℝ) : ∫ v, tri v * Real.cos (2 * π * v * w) = Real.sinc (π * w) ^ 2 := by
  -- reduce to [−1, 1]
  have hsupp : ∀ v ∉ Ioc (-1 : ℝ) 1, tri v * Real.cos (2 * π * v * w) = 0 := by
    intro v hv
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hv
    rw [tri_eq_zero, zero_mul]
    rcases hv with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0)]
  rotate_left
  · exact (Continuous.continuousOn (by have := tri_continuous; fun_prop)).intervalIntegrable
  · exact (Continuous.continuousOn (by have := tri_continuous; fun_prop)).intervalIntegrable
  -- the left half equals the right half
  have hleft : ∫ v in (-1 : ℝ)..0, tri v * Real.cos (2 * π * v * w)
      = ∫ v in (0 : ℝ)..1, tri v * Real.cos (2 * π * v * w) := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
      (fun v => tri v * Real.cos (2 * π * v * w))
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [tri_neg, show 2 * π * -v * w = -(2 * π * v * w) by ring, Real.cos_neg]
  have hright : ∫ v in (0 : ℝ)..1, tri v * Real.cos (2 * π * v * w)
      = ∫ v in (0 : ℝ)..1, (1 - v) * Real.cos (2 * π * w * v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    rw [tri_of_nonneg hv.1 hv.2, show 2 * π * v * w = 2 * π * w * v by ring]
  rw [hleft, hright]
  by_cases hw : w = 0
  · subst hw
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, Real.sinc_zero]
    have h12 : ∫ v in (0 : ℝ)..1, (1 - v) = 1 / 2 := by
      have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) (1 : ℝ) (a := 0) (b := 1)
      simp only [sub_zero, sub_self] at this
      rw [this, integral_id]; norm_num
    rw [h12]; norm_num
  · have ha : 2 * π * w ≠ 0 := by positivity
    rw [integral_one_sub_mul_cos ha, Real.sinc_of_ne_zero (by positivity)]
    have hcos : Real.cos (2 * π * w) = 1 - 2 * Real.sin (π * w) ^ 2 := by
      rw [show 2 * π * w = 2 * (π * w) by ring, Real.cos_two_mul, Real.cos_sq']; ring
    rw [hcos]
    field_simp
    ring

/-- the sine transform of Λ vanishes (Λ even). -/
lemma tri_sin_transform (w : ℝ) : ∫ v, tri v * Real.sin (2 * π * v * w) = 0 := by
  have h := integral_neg_eq_self (fun v => tri v * Real.sin (2 * π * v * w)) volume
  have e : (fun v => tri (-v) * Real.sin (2 * π * -v * w)) = fun v => -(tri v * Real.sin (2 * π * v * w)) := by
    funext v; rw [tri_neg, show 2 * π * -v * w = -(2 * π * v * w) by ring, Real.sin_neg]; ring
  rw [e, integral_neg] at h
  linarith

/-- the Fourier transform of Λ (as a complex function) is sinc(π·)². -/
lemma fourier_tri (w : ℝ) : 𝓕 (fun v => (tri v : ℂ)) w = ((Real.sinc (π * w) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpt : (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • (tri v : ℂ))
      = fun v => ((tri v * Real.cos (2 * π * v * w) : ℝ) : ℂ)
          - ((tri v * Real.sin (2 * π * v * w) : ℝ) : ℂ) * Complex.I := by
    funext v
    rw [smul_eq_mul, Complex.exp_mul_I]
    rw [show (-2 * π * v * w : ℝ) = -(2 * π * v * w) by ring]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have hi1 : Integrable (fun v => tri v * Real.cos (2 * π * v * w)) :=
    tri_integrable.mul_bdd (by fun_prop : Continuous fun v => Real.cos (2 * π * v * w)).aestronglyMeasurable
      (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hi2 : Integrable (fun v => tri v * Real.sin (2 * π * v * w)) :=
    tri_integrable.mul_bdd (by fun_prop : Continuous fun v => Real.sin (2 * π * v * w)).aestronglyMeasurable
      (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  rw [hpt, integral_sub hi1.ofReal (hi2.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal, tri_cos_transform, tri_sin_transform]
  simp

/-- **FP**: the Fourier pair sinc² ↔ triangle. -/
theorem fp_holds : FP := by
  intro ω
  set g : ℝ → ℂ := fun v => (tri v : ℂ) with hg
  have hgc : Continuous g := continuous_ofReal.comp tri_continuous
  have hgi : Integrable g := tri_integrable.ofReal
  have hFg : 𝓕 g = fun w => ((Real.sinc (π * w) ^ 2 : ℝ) : ℂ) := funext fourier_tri
  have hFi : Integrable (𝓕 g) := by
    rw [hFg]; exact (sinc_scaled_sq_integrable π Real.pi_pos).ofReal
  have hinv := congrFun (hgc.fourierInv_fourier_eq hgi hFi) ω
  rw [Real.fourierInv_eq', hFg] at hinv
  have hin : ∀ v : ℝ, (inner ℝ v ω : ℝ) = v * ω := fun v => by
    rw [RCLike.inner_apply]; simp [mul_comm]
  have hfun : (fun v : ℝ => Complex.exp (↑(2 * π * inner ℝ v ω) * Complex.I) • ((Real.sinc (π * v) ^ 2 : ℝ) : ℂ))
      = fun v => ((Real.sinc (π * v) ^ 2 * Real.cos (2 * π * ω * v) : ℝ) : ℂ)
          + ((Real.sinc (π * v) ^ 2 * Real.sin (2 * π * ω * v) : ℝ) : ℂ) * Complex.I := by
    funext v
    rw [hin v, smul_eq_mul, Complex.exp_mul_I, show 2 * π * (v * ω) = 2 * π * ω * v by ring]
    push_cast
    ring
  have hs := sinc_scaled_sq_integrable π Real.pi_pos
  have hc1 : Integrable (fun v => Real.sinc (π * v) ^ 2 * Real.cos (2 * π * ω * v)) :=
    hs.mul_bdd (by fun_prop : Continuous fun v => Real.cos (2 * π * ω * v)).aestronglyMeasurable
      (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hc2 : Integrable (fun v => Real.sinc (π * v) ^ 2 * Real.sin (2 * π * ω * v)) :=
    hs.mul_bdd (by fun_prop : Continuous fun v => Real.sin (2 * π * ω * v)).aestronglyMeasurable
      (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  rw [hfun, integral_add hc1.ofReal (hc2.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal] at hinv
  have hre := congrArg Complex.re hinv
  simp only [hg, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
  exact hre

end MCert

end ZetaS

end
