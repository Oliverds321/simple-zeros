/-
A2a_S3b_LineInt (L7_8, round 3): the set integral `lineInt` over `I_j` is the interval integral over `lineIv`.
For `q > 0`, `j/(qr)` is monotone in `q`, so `I_j = [lo, hi]` (possibly empty).
-/
import ZetaShell.Lemma2.A2a_S3_Defs

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace TrackF

/-- the set of `lineInt` as an `Icc` (raw bounds), line `j > 0`. -/
theorem lineSet_pos (Q r : ℕ) (j : ℤ) (η δ : ℝ) (hr : 1 ≤ r) (hj : 0 < j) (hup : 0 < η + δ / 2) :
    {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧ (j : ℝ) / (q * r) ≤ η + δ / 2}
      = Set.Icc (max 1 (|(j : ℝ)| / (r * (η + δ / 2))))
          (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have habs : |(j : ℝ)| = j := abs_of_pos hjR
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_Icc, habs]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hq : 0 < q := by linarith
    have hqr : 0 < q * r := by positivity
    refine ⟨max_le h1 ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hqr] at h4
      nlinarith
    · split_ifs with hdn
      · refine le_min h2 ?_
        rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ hqr] at h3
        nlinarith
      · exact h2
  · rintro ⟨h1, h2⟩
    have hq1 : 1 ≤ q := le_trans (le_max_left _ _) h1
    have hq : 0 < q := by linarith
    have hqr : 0 < q * r := by positivity
    have h1' : (j : ℝ) / (r * (η + δ / 2)) ≤ q := le_trans (le_max_right _ _) h1
    refine ⟨hq1, ?_, ?_, ?_⟩
    · split_ifs at h2 with hdn
      · exact le_trans h2 (min_le_left _ _)
      · exact h2
    · split_ifs at h2 with hdn
      · have h2' : q ≤ (j : ℝ) / (r * (η - δ / 2)) := le_trans h2 (min_le_right _ _)
        rw [le_div_iff₀ hqr]
        rw [le_div_iff₀ (by positivity)] at h2'
        nlinarith
      · push_neg at hdn
        have : 0 ≤ (j : ℝ) / (q * r) := by positivity
        linarith
    · rw [div_le_iff₀ hqr]
      rw [div_le_iff₀ (by positivity)] at h1'
      nlinarith

/-- line `j > 0` with `η + δ/2 ≤ 0`: empty. -/
theorem lineSet_pos_empty (Q r : ℕ) (j : ℤ) (η δ : ℝ) (hr : 1 ≤ r) (hj : 0 < j) (hup : ¬ 0 < η + δ / 2) :
    {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧ (j : ℝ) / (q * r) ≤ η + δ / 2} = ∅ := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, _, _, h4⟩
  have : 0 < (j : ℝ) / (q * r) := by
    have : 0 < q := by linarith
    positivity
  linarith

/-- line `j < 0`: the set as an `Icc`. -/
theorem lineSet_neg (Q r : ℕ) (j : ℤ) (η δ : ℝ) (hr : 1 ≤ r) (hj : j < 0) (hdn : η - δ / 2 < 0) :
    {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧ (j : ℝ) / (q * r) ≤ η + δ / 2}
      = Set.Icc (max 1 (|(j : ℝ)| / (r * (-(η - δ / 2)))))
          (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hjR : (j : ℝ) < 0 := by exact_mod_cast hj
  have habs : |(j : ℝ)| = -j := abs_of_neg hjR
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_Icc, habs]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hq : 0 < q := by linarith
    have hqr : 0 < q * r := by positivity
    refine ⟨max_le h1 ?_, ?_⟩
    · rw [div_le_iff₀ (by nlinarith)]
      rw [le_div_iff₀ hqr] at h3
      nlinarith
    · split_ifs with hup
      · refine le_min h2 ?_
        rw [le_div_iff₀ (by nlinarith)]
        rw [div_le_iff₀ hqr] at h4
        nlinarith
      · exact h2
  · rintro ⟨h1, h2⟩
    have hq1 : 1 ≤ q := le_trans (le_max_left _ _) h1
    have hq : 0 < q := by linarith
    have hqr : 0 < q * r := by positivity
    have h1' : -(j : ℝ) / (r * (-(η - δ / 2))) ≤ q := le_trans (le_max_right _ _) h1
    refine ⟨hq1, ?_, ?_, ?_⟩
    · split_ifs at h2 with hup
      · exact le_trans h2 (min_le_left _ _)
      · exact h2
    · rw [le_div_iff₀ hqr]
      rw [div_le_iff₀ (by nlinarith)] at h1'
      nlinarith
    · split_ifs at h2 with hup
      · have h2' : q ≤ -(j : ℝ) / (r * (-(η + δ / 2))) := le_trans h2 (min_le_right _ _)
        rw [div_le_iff₀ hqr]
        rw [le_div_iff₀ (by nlinarith)] at h2'
        nlinarith
      · push_neg at hup
        have : (j : ℝ) / (q * r) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hjR.le hqr.le
        linarith

theorem lineSet_neg_empty (Q r : ℕ) (j : ℤ) (η δ : ℝ) (hr : 1 ≤ r) (hj : j < 0) (hdn : ¬ η - δ / 2 < 0) :
    {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧ (j : ℝ) / (q * r) ≤ η + δ / 2} = ∅ := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hjR : (j : ℝ) < 0 := by exact_mod_cast hj
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, _, h3, _⟩
  have : (j : ℝ) / (q * r) < 0 := by
    have : 0 < q * r := by have : 0 < q := by linarith
                           positivity
    exact div_neg_of_neg_of_pos hjR this
  push_neg at hdn
  linarith

/-- set integral over `Icc lo hi` as the (possibly empty) interval integral. -/
theorem setIntegral_Icc_eq (f : ℝ → ℝ) (lo hi : ℝ) :
    ∫ q in Set.Icc lo hi, f q = if lo ≤ hi then ∫ q in lo..hi, f q else 0 := by
  split_ifs with h
  · rw [intervalIntegral.integral_of_le h, integral_Icc_eq_integral_Ioc]
  · rw [Set.Icc_eq_empty h, Measure.restrict_empty, integral_zero_measure]

theorem s3_lineInt (F : Fam) (Q r : ℕ) (j : ℤ) (e : ℕ) (η δ : ℝ) (hr : 1 ≤ r) (hj : j ≠ 0) (hδ : 0 < δ) :
    lineInt F Q r j e η δ = ∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q) := by
  unfold lineInt lineIv
  rcases lt_or_gt_of_ne hj with hneg | hpos
  · have hnp : ¬ 0 < j := by omega
    simp only [if_neg hnp]
    by_cases hdn : η - δ / 2 < 0
    · rw [lineSet_neg Q r j η δ hr hneg hdn, setIntegral_Icc_eq]
      by_cases hle : max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
          ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))
      · have hc : η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
            ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ)) :=
          ⟨hdn, hle⟩
        rw [if_pos hc, if_pos hle]
      · have hc : ¬ (η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
            ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))) :=
          fun h => hle h.2
        rw [if_neg hc, if_neg hle, intervalIntegral.integral_same]
    · have hc : ¬ (η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
          ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))) :=
        fun h => hdn h.1
      rw [lineSet_neg_empty Q r j η δ hr hneg hdn, Measure.restrict_empty, integral_zero_measure,
        if_neg hc, intervalIntegral.integral_same]
  · simp only [if_pos hpos]
    by_cases hup : 0 < η + δ / 2
    · rw [lineSet_pos Q r j η δ hr hpos hup, setIntegral_Icc_eq]
      by_cases hle : max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
          ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))
      · have hc : 0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
            ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ)) :=
          ⟨hup, hle⟩
        rw [if_pos hc, if_pos hle]
      · have hc : ¬ (0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
            ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))) :=
          fun h => hle h.2
        rw [if_neg hc, if_neg hle, intervalIntegral.integral_same]
    · have hc : ¬ (0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
          ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))) :=
        fun h => hup h.1
      rw [lineSet_pos_empty Q r j η δ hr hpos hup, Measure.restrict_empty, integral_zero_measure,
        if_neg hc, intervalIntegral.integral_same]

end TrackF
end ZetaShell
