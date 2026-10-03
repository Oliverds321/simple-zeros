/-
A2a_S3c_Irrelevant (L7_8, round 3): lines and `e` with `e|j| > rQ(|η| + δ/2)` contribute nothing (Step 3, "only
`e ≤ J/|j|` contribute", l.339): every `q ∈ I_j` has `q ≥ |j|/(r(|η|+δ/2))`, so `qe > Q` and `w(qe/Q) = 0`; an empty
line (`lineIv = (1/2, 1/2)`) has no integer `q = rk − r′j` (parity) and a zero integral.
PROVED (sorry-free).
-/
import ZetaShell.Lemma2.A2a_S3_Defs

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem Fam.w_eq_zero_of_gt_one (F : Fam) {x : ℝ} (hx : 1 < x) : F.w x = 0 := by
  cases F <;> simp only [Fam.w] <;> split_ifs with h <;> first | rfl | (exfalso; linarith [h.2])

theorem div_aux (A B C r : ℝ) (hr : 0 < r) (hB : 0 < B) (hBC : B ≤ C) (hA : 0 ≤ A) :
    A / (r * C) ≤ A / (r * B) :=
  div_le_div_of_nonneg_left hA (mul_pos hr hB) (mul_le_mul_of_nonneg_left hBC hr.le)

/-- a non-empty `lineIv` starts at or beyond `|j|/(r(|η| + δ/2))`. -/
theorem lineIv_cases (Q r : ℕ) (j : ℤ) (η δ : ℝ) (hr : 1 ≤ r) (hδ : 0 < δ) :
    lineIv Q r j η δ = (1 / 2, 1 / 2) ∨
      |(j : ℝ)| / (r * (|η| + δ / 2)) ≤ (lineIv Q r j η δ).1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold lineIv
  by_cases hj : 0 < j
  · simp only [if_pos hj]
    by_cases hc : 0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
          ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))
    · rw [if_pos hc]; right
      exact le_trans (div_aux _ _ _ _ hr' hc.1 (by linarith [le_abs_self η]) (abs_nonneg _)) (le_max_right _ _)
    · rw [if_neg hc]; left; rfl
  · simp only [if_neg hj]
    by_cases hc : η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
          ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))
    · rw [if_pos hc]; right
      exact le_trans (div_aux _ _ _ _ hr' (by linarith [hc.1]) (by linarith [neg_abs_le η]) (abs_nonneg _))
        (le_max_right _ _)
    · rw [if_neg hc]; left; rfl

theorem s3_irrelevant (F : Fam) (Q r : ℕ) (r' j : ℤ) (e f : ℕ) (η δ : ℝ) (hQ : 1 ≤ Q) (hr : 1 ≤ r)
    (hj : j ≠ 0) (he : 1 ≤ e) (hδ : 0 < δ) (hX : (r : ℝ) * Q * (|η| + δ / 2) < (e : ℝ) * |(j : ℝ)|) :
    lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2 = 0 ∧
      (∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)) = 0 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hpos : (0 : ℝ) < r * (|η| + δ / 2) := by positivity
  rcases lineIv_cases Q r j η δ hr hδ with h | h
  · rw [h]
    simp only [intervalIntegral.integral_same, and_true]
    unfold lineCount
    apply Finset.sum_eq_zero
    intro k hk
    exfalso
    rw [Finset.mem_Icc] at hk
    have h1 := le_trans (Int.le_ceil _) (Int.cast_le.mpr hk.1)
    have h2 := le_trans (Int.cast_le.mpr hk.2) (Int.floor_le _)
    push_cast at h1 h2
    have hk2 : (1 : ℝ) + 2 * r' * j = 2 * r * k := by
      have : ((1 / 2 : ℝ) + r' * j) / r = k := by linarith [h1, h2]
      field_simp at this
      linarith
    have hint : (1 : ℤ) + 2 * r' * j = 2 * r * k := by exact_mod_cast hk2
    have h3 : (1 : ℤ) = 2 * ((r : ℤ) * k - r' * j) := by linear_combination hint
    generalize ((r : ℤ) * k - r' * j) = m at h3
    omega
  · -- every q ≥ lo has qe > Q
    have hlo : (Q : ℝ) < (lineIv Q r j η δ).1 * e := by
      have h1 : (Q : ℝ) < |(j : ℝ)| / (r * (|η| + δ / 2)) * e := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hpos]
        nlinarith
      nlinarith
    have hw : ∀ q : ℝ, (lineIv Q r j η δ).1 ≤ q → F.w (q * e / Q) = 0 := by
      intro q hq
      apply F.w_eq_zero_of_gt_one
      rw [lt_div_iff₀ hQ']
      nlinarith
    constructor
    · unfold lineCount
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Icc] at hk
      have h1 := le_trans (Int.le_ceil _) (Int.cast_le.mpr hk.1)
      push_cast at h1
      have hq : (lineIv Q r j η δ).1 ≤ ((r * k - r' * j : ℤ) : ℝ) := by
        rw [div_le_iff₀ hr'] at h1
        push_cast
        linarith
      rw [hw _ hq]
      simp
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro q hq
        rw [Set.uIcc_of_le (lineIv_le Q r j η δ)] at hq
        exact hw q hq.1
end TrackF
end ZetaShell
