/-
A2a_S3a_Window (L7_8, round 4): the core of `s3_reindex`: the Farey points of the window, re-indexed by lines.
`Σ_{x ∈ 𝔉_Q, ‖x − θ‖ ≤ δ/2} Ω(x.1) = Ω(r)1[|η| ≤ δ/2] + Σ_{0<|j|≤M} Σ_{k ∈ K_j, (k,j)=1} Ω(rk − r′j)`,
`θ = a/r + η`, `ar′ − a′r = 1`, `0 < δ < 1`, `1 ≤ r ≤ Q` (`s3_window_lines`).
Also `lineIv_range` and `lineK_bounds`: every `k ∈ K_j` has `1 ≤ rk − r′j ≤ Q`.
-/
import ZetaShell.Lemma2.A2a_S3a_Collapse
import ZetaShell.Lemma2.A2b_DensityBound
import ZetaShell.Lemma2.A2a_S2c_Reparam

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem lineIv_range (Q r : ℕ) (j : ℤ) (η δ : ℝ) :
    lineIv Q r j η δ = (1 / 2, 1 / 2) ∨ (1 ≤ (lineIv Q r j η δ).1 ∧ (lineIv Q r j η δ).2 ≤ Q) := by
  unfold lineIv
  by_cases hj : 0 < j
  · simp only [if_pos hj]
    by_cases hc : 0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
          ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))
    · rw [if_pos hc]; right
      refine ⟨le_max_left _ _, ?_⟩
      split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    · rw [if_neg hc]; left; rfl
  · simp only [if_neg hj]
    by_cases hc : η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
          ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))
    · rw [if_pos hc]; right
      refine ⟨le_max_left _ _, ?_⟩
      split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    · rw [if_neg hc]; left; rfl

theorem lineK_bounds (Q r : ℕ) (hr : 1 ≤ r) (r' j : ℤ) (η δ : ℝ) :
    ∀ k ∈ Finset.Icc ⌈((lineIv Q r j η δ).1 + r' * j) / (r : ℤ)⌉ ⌊((lineIv Q r j η δ).2 + r' * j) / (r : ℤ)⌋,
      1 ≤ (r : ℤ) * k - r' * j ∧ (r : ℤ) * k - r' * j ≤ Q := by
  intro k hk
  have hrR : (0 : ℝ) < ((r : ℤ) : ℝ) := by push_cast; exact_mod_cast hr
  rw [Finset.mem_Icc, ceil_le_iff_mul hrR, le_floor_iff_mul hrR] at hk
  have h1 : (lineIv Q r j η δ).1 ≤ (((r : ℤ) * k - r' * j : ℤ) : ℝ) := by push_cast; push_cast at hk; linarith [hk.1]
  have h2 : (((r : ℤ) * k - r' * j : ℤ) : ℝ) ≤ (lineIv Q r j η δ).2 := by push_cast; push_cast at hk; linarith [hk.2]
  rcases lineIv_range Q r j η δ with he | ⟨hlo, hhi⟩
  · rw [he] at h1 h2
    simp only at h1 h2
    have heq : (((r : ℤ) * k - r' * j : ℤ) : ℝ) = 1 / 2 := le_antisymm h2 h1
    have h3 : ((2 * ((r : ℤ) * k - r' * j) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; push_cast at heq; linarith
    have h4 : 2 * ((r : ℤ) * k - r' * j) = 1 := by exact_mod_cast h3
    omega
  · constructor
    · have : (1 : ℝ) ≤ (((r : ℤ) * k - r' * j : ℤ) : ℝ) := le_trans hlo h1
      exact_mod_cast this
    · have : (((r : ℤ) * k - r' * j : ℤ) : ℝ) ≤ (Q : ℝ) := le_trans h2 hhi
      exact_mod_cast this

/-- **the core bijection** (open). -/
theorem s3_window_lines (F : Fam) (Q r : ℕ) (a a' r' : ℤ) (η δ : ℝ) (hQ : 2 ≤ Q) (hr : 1 ≤ r) (hrQ : r ≤ Q)
    (hdet : a * r' - a' * (r : ℤ) = 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∑ x ∈ fareyWin Q ((a : ℝ) / r + η) δ, fareyWeight F Q x
      = spike F Q r η δ + ∑ j ∈ lineSet (lineM Q r η δ),
          ∑ k ∈ Finset.Icc ⌈((lineIv Q r j η δ).1 + r' * j) / (r : ℤ)⌉ ⌊((lineIv Q r j η δ).2 + r' * j) / (r : ℤ)⌋,
            (if Int.gcd k j = 1 then ZetaShell.OmegaW Q (F.omega Q) ((r : ℤ) * k - r' * j).toNat else 0) := by
  sorry

end TrackF
end ZetaShell
