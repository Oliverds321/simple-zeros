/-
L711_S4a_ChangeVar (L7_11, 28 Sep 2026): an ingredient for `step4_profile` (A2a_S4_Profile), not a node.
Per line `j ≥ 1`, the substitution `q = j/(rβ)` turns L7_8's set integral `lineInt` (over
`I_j = {q ∈ [1, Q] : j/(qr) ∈ [η − δ/2, η + δ/2]}`) into an interval integral over the window in `β`, restricted to
`β ∈ [j/(rQ), j/r]`, with Jacobian `j/(rβ²)` (Mathlib's `integral_image_eq_integral_abs_deriv_smul`).
-/
import ZetaShell.Lemma2.A2a_StepDefs

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ZetaShell
namespace TrackF

theorem lineInt_changeVar (F : Fam) (Q r : ℕ) (j : ℤ) (e : ℕ) (η δ : ℝ)
    (hQ : 1 ≤ Q) (hr : 1 ≤ r) (hj : 0 < j) (hδ : 0 < δ) :
    lineInt F Q r j e η δ
      = ∫ β in (η - δ / 2)..(η + δ / 2),
          Set.indicator (Set.Icc ((j : ℝ) / (r * Q)) ((j : ℝ) / r))
            (fun β => (j : ℝ) / (r * β ^ 2) * F.w ((j : ℝ) / (r * β) * e / Q)) β := by
  have hlohi : η - δ / 2 ≤ η + δ / 2 := by linarith
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set s : Set ℝ := Set.Icc (η - δ / 2) (η + δ / 2) ∩ Set.Icc ((j : ℝ) / (r * Q)) ((j : ℝ) / r) with hs
  have hspos : ∀ β ∈ s, 0 < β := fun β hβ => lt_of_lt_of_le (by positivity) hβ.2.1
  set f : ℝ → ℝ := fun β => (j : ℝ) / (r * β) with hf
  have himage : f '' s = {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧
      (j : ℝ) / (q * r) ≤ η + δ / 2} := by
    ext q
    constructor
    · rintro ⟨β, hβ, rfl⟩
      have hb := hspos β hβ
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hβ
      simp only [hf, Set.mem_setOf_eq]
      have e1 : (j : ℝ) / ((j : ℝ) / (r * β) * r) = β := by field_simp
      rw [e1]
      refine ⟨?_, ?_, h1, h2⟩
      · rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ hrR] at h4
        linarith
      · rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ (by positivity)] at h3
        linarith
    · rintro ⟨h1, h2, h3, h4⟩
      have hq : 0 < q := by linarith
      refine ⟨(j : ℝ) / (q * r), ⟨⟨h3, h4⟩, ?_, ?_⟩, ?_⟩
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (j : ℝ) * (q * r) ≤ j * (r * Q) := by
          apply mul_le_mul_of_nonneg_left _ hjR.le; nlinarith
        linarith
      · rw [div_le_div_iff₀ (by positivity) hrR]
        have : (j : ℝ) * r ≤ j * (q * r) := by
          apply mul_le_mul_of_nonneg_left _ hjR.le; nlinarith
        linarith
      · simp only [hf]; field_simp
  have hderiv : ∀ β ∈ s, HasDerivWithinAt f (-((j : ℝ) / (r * β ^ 2))) s β := by
    intro β hβ
    have hb := hspos β hβ
    have hrb : (r : ℝ) * β ≠ 0 := by positivity
    have h1 : HasDerivAt (fun β : ℝ => (r : ℝ) * β) (r : ℝ) β := by
      simpa using (hasDerivAt_id β).const_mul (r : ℝ)
    have h2 := (h1.inv hrb).const_mul (j : ℝ)
    have h3 : HasDerivAt f (-((j : ℝ) / (r * β ^ 2))) β := by
      have hfeq : f = fun β : ℝ => (j : ℝ) * ((r : ℝ) * β)⁻¹ := by
        funext x; simp only [hf, div_eq_mul_inv]
      rw [hfeq]
      refine h2.congr_deriv ?_
      have hb2 : (β : ℝ) ≠ 0 := hb.ne'
      have hr0 : (r : ℝ) ≠ 0 := hrR.ne'
      rw [mul_pow, neg_div, mul_neg, neg_inj]
      field_simp
      try ring
    exact h3.hasDerivWithinAt
  have hinj : InjOn f s := by
    intro x hx y hy hxy
    have hx0 := hspos x hx
    have hy0 := hspos y hy
    simp only [hf] at hxy
    rw [div_eq_div_iff (by positivity) (by positivity)] at hxy
    have : (j : ℝ) * r * (y - x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; have : (0 : ℝ) < j * r := by positivity
      linarith
    · linarith
  have hms : MeasurableSet s := measurableSet_Icc.inter measurableSet_Icc
  unfold lineInt
  rw [← himage, integral_image_eq_integral_abs_deriv_smul hms hderiv hinj]
  rw [intervalIntegral.integral_of_le hlohi, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator measurableSet_Icc]
  apply setIntegral_congr_fun hms
  intro β hβ
  have hb := hspos β hβ
  simp only [hf, smul_eq_mul]
  rw [abs_neg, abs_of_pos (by positivity)]

end TrackF
end ZetaShell
