/-
SigmaHelpers (L2_2, 28 Sep 2026) — small facts about `kPsi` needed to apply the corrected A2
(`A2fix.agg_true_window_of_even`) with `kψ = kPsi ψ` inside A7 (thm:sigd-OLL) and thm:zeta-allmarks(c):
`kPsi ψ` is even, `kPsi ψ 0 = 1`, and `|kPsi ψ x| ≤ 1`, for ψ continuous and positive on [−1/2, 1/2].
-/
import ZetaS.Interfaces

open Set

namespace ZetaS

namespace SigmaHelpers

lemma kPsi_neg (ψ : ℝ → ℝ) (x : ℝ) : kPsi ψ (-x) = kPsi ψ x := by
  unfold kPsi
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [mul_neg, neg_mul, Real.cos_neg]

variable {ψ : ℝ → ℝ} (hcont : ContinuousOn ψ (Icc (-(1 / 2 : ℝ)) (1 / 2)))
  (hpos : ∀ s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), 0 < ψ s)
include hcont hpos

lemma kPsi_den_pos : 0 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s := by
  have hab : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hab]; exact hcont
  · intro s hs; exact hpos s (Ioo_subset_Icc_self hs)
  · norm_num

lemma kPsi_zero : kPsi ψ 0 = 1 := by
  unfold kPsi
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  exact div_self (kPsi_den_pos hcont hpos).ne'

lemma kPsi_abs_le_one (x : ℝ) : |kPsi ψ x| ≤ 1 := by
  have hab : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  have huIcc : uIcc (-(1 / 2 : ℝ)) (1 / 2) = Icc (-(1 / 2 : ℝ)) (1 / 2) := uIcc_of_le hab
  have hint : IntervalIntegrable (fun s => ψ s * Real.cos (2 * Real.pi * x * s))
      MeasureTheory.volume (-(1 / 2 : ℝ)) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hcont.mul (Continuous.continuousOn (by fun_prop))
  have hintψ : IntervalIntegrable ψ MeasureTheory.volume (-(1 / 2 : ℝ)) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hcont
  have hden := kPsi_den_pos hcont hpos
  have hup : (∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s * Real.cos (2 * Real.pi * x * s))
      ≤ ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s := by
    apply intervalIntegral.integral_mono_on hab hint hintψ
    intro s hs
    have := (hpos s hs).le
    have := Real.cos_le_one (2 * Real.pi * x * s)
    nlinarith
  have hlow : -(∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s)
      ≤ ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s * Real.cos (2 * Real.pi * x * s) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on hab hintψ.neg hint
    intro s hs
    have := (hpos s hs).le
    have := Real.neg_one_le_cos (2 * Real.pi * x * s)
    simp only [Pi.neg_apply]
    nlinarith
  unfold kPsi
  rw [abs_div, abs_of_pos hden, div_le_one hden, abs_le]
  exact ⟨hlow, hup⟩

end SigmaHelpers

end ZetaS
