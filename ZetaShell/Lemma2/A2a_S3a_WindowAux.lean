/-
A2a_S3a_WindowAux (L7_8, round 4): helpers for `s3_window_lines`.
* `abs_sub_round_le_distZ`: the nearest integer realises `distZ`;
* `int_eq_of_close`: two representatives within `δ/2 < 1/2` of `θ` coincide;
* `mem_lineIv`: for `q ≥ 1`, `q ∈ [lo_j, hi_j] ↔ q ≤ Q ∧ j/(qr) ∈ [η − δ/2, η + δ/2]`;
* `mem_lineK`: `k ∈ K_j ↔ lo_j ≤ rk − r′j ≤ hi_j`.
-/
import ZetaShell.Lemma2.A2a_S3b_LineInt
import ZetaShell.Lemma2.A2a_S2c_Reparam
import ZetaShell.Lemma2.A2_FareyBasics

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem abs_sub_round_le_distZ (y : ℝ) : |y - round y| ≤ distZ y := by
  obtain ⟨n, hn⟩ := distZ_eq y
  rw [hn]
  exact round_le y n

theorem int_eq_of_close (c θ δ : ℝ) (hδ1 : δ < 1) (n n' : ℤ) (h1 : |c + n - θ| ≤ δ / 2)
    (h2 : |c + n' - θ| ≤ δ / 2) : n = n' := by
  have h3 : |((n - n' : ℤ) : ℝ)| < 1 := by
    have : ((n - n' : ℤ) : ℝ) = (c + n - θ) - (c + n' - θ) := by push_cast; ring
    rw [this]
    calc |(c + n - θ) - (c + n' - θ)| ≤ |c + n - θ| + |c + n' - θ| := abs_sub _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add h1 h2
      _ < 1 := by linarith
  have h4 : |n - n'| < 1 := by
    have : ((|n - n'| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h3
    exact_mod_cast this
  have := abs_lt.mp h4
  omega

theorem mem_lineIv (Q r : ℕ) (j : ℤ) (η δ q : ℝ) (hr : 1 ≤ r) (hj : j ≠ 0) (hq : 1 ≤ q) :
    ((lineIv Q r j η δ).1 ≤ q ∧ q ≤ (lineIv Q r j η δ).2) ↔
      (q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧ (j : ℝ) / (q * r) ≤ η + δ / 2) := by
  have hmemset : (q ∈ {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧ (j : ℝ) / (q * r) ≤ η + δ / 2})
      ↔ (q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧ (j : ℝ) / (q * r) ≤ η + δ / 2) := by
    simp only [Set.mem_setOf_eq]; exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
  rw [← hmemset]
  unfold lineIv
  rcases lt_or_gt_of_ne hj with hneg | hpos
  · have hnp : ¬ 0 < j := by omega
    simp only [if_neg hnp]
    by_cases hdn : η - δ / 2 < 0
    · rw [lineSet_neg Q r j η δ hr hneg hdn]
      by_cases hle : max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
          ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))
      · have hc : η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
            ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ)) :=
          ⟨hdn, hle⟩
        rw [if_pos hc, Set.mem_Icc]
      · have hc : ¬ (η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
            ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))) :=
          fun h => hle h.2
        rw [if_neg hc, Set.mem_Icc]
        constructor
        · rintro ⟨_, h2⟩; simp only at h2; linarith
        · rintro ⟨h1, h2⟩; exact absurd (le_trans h1 h2) hle
    · have hc : ¬ (η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
          ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))) :=
        fun h => hdn h.1
      rw [lineSet_neg_empty Q r j η δ hr hneg hdn, if_neg hc]
      simp only [Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h2; linarith
  · simp only [if_pos hpos]
    by_cases hup : 0 < η + δ / 2
    · rw [lineSet_pos Q r j η δ hr hpos hup]
      by_cases hle : max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
          ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))
      · have hc : 0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
            ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ)) :=
          ⟨hup, hle⟩
        rw [if_pos hc, Set.mem_Icc]
      · have hc : ¬ (0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
            ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))) :=
          fun h => hle h.2
        rw [if_neg hc, Set.mem_Icc]
        constructor
        · rintro ⟨_, h2⟩; simp only at h2; linarith
        · rintro ⟨h1, h2⟩; exact absurd (le_trans h1 h2) hle
    · have hc : ¬ (0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
          ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))) :=
        fun h => hup h.1
      rw [lineSet_pos_empty Q r j η δ hr hpos hup, if_neg hc]
      simp only [Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h2; linarith

theorem mem_lineK (lo hi : ℝ) (r r' j k : ℤ) (hr : 1 ≤ r) :
    k ∈ Finset.Icc ⌈(lo + r' * j) / r⌉ ⌊(hi + r' * j) / r⌋ ↔
      lo ≤ ((r * k - r' * j : ℤ) : ℝ) ∧ ((r * k - r' * j : ℤ) : ℝ) ≤ hi := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
  rw [Finset.mem_Icc, ceil_le_iff_mul hrR, le_floor_iff_mul hrR]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end TrackF
end ZetaShell
