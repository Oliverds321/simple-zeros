/-
L7_9 round 3, sub-node (c4) of `pnt_step`: the deterministic assembly. From (c1) Abel summation
`C₀(n) = E(n)w̃(n) − Σ_{m<n}E(m)(w̃(m+1) − w̃(m))`, the support of `w̃` (`e^{s−1} < n < e^{s+1}`), a bound
`|E(m)| ≤ E*` on that support and `sup|w̃|, Σ|Δw̃| ≤ W`: `|C₀(n)| ≤ 2E*W` for `n ≤ ⌊e^{s+1}⌋`.
-/
import ZetaShell.LemmaK.LK9_K6c_Helpers

noncomputable section

namespace ZetaShell
namespace LemmaK

theorem psum_c_bound (T s R W Es : ℝ) (hs : 1 ≤ s) (hEs : 0 ≤ Es)
    (hw : ∀ n : ℕ, ‖K6.wmod T s n‖ ≤ W)
    (hv : ∑ m ∈ Finset.range ⌊Real.exp (s + 1)⌋₊, ‖K6.wmod T s (m + 1) - K6.wmod T s m‖ ≤ W)
    (hE : ∀ m : ℕ, Real.exp (s - 1) - 1 ≤ (m : ℝ) → (m : ℝ) ≤ Real.exp (s + 1) →
      ‖K6.psum m (fun j => ((K6.lamP R j - 1 : ℝ) : ℂ))‖ ≤ Es) :
    ∀ n : ℕ, n ≤ ⌊Real.exp (s + 1)⌋₊ →
      ‖K6.psum n (fun n => K6.asmooth T s R n - K6.wmod T s n)‖ ≤ 2 * Es * W := by
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hw 0)
  -- support of `w̃`
  have hsupp : ∀ m : ℕ, K6.wmod T s m ≠ 0 → Real.exp (s - 1) < m ∧ (m : ℝ) < Real.exp (s + 1) := by
    intro m hm
    have hρ : K6.rho6 (Real.log m - s) ≠ 0 := by
      intro h; apply hm; unfold K6.wmod; rw [h]; simp
    have hlt : |Real.log m - s| < 1 := by
      by_contra hc
      rw [not_lt] at hc
      apply hρ
      unfold K6.rho6
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0] at hlt; simp at hlt; rw [abs_of_nonneg (by linarith)] at hlt; linarith
    have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    rw [abs_lt] at hlt
    constructor
    · rw [← Real.exp_log hmR]; exact Real.exp_lt_exp.mpr (by linarith)
    · rw [← Real.exp_log hmR]; exact Real.exp_lt_exp.mpr (by linarith)
  have hMle : ((⌊Real.exp (s + 1)⌋₊ : ℕ) : ℝ) ≤ Real.exp (s + 1) :=
    Nat.floor_le (Real.exp_pos _).le
  intro n hn
  have hnR : (n : ℝ) ≤ Real.exp (s + 1) := le_trans (by exact_mod_cast hn) hMle
  have hfun : (fun n => K6.asmooth T s R n - K6.wmod T s n)
      = fun m => ((K6.lamP R m - 1 : ℝ) : ℂ) * K6.wmod T s m :=
    funext fun m => K6.asmooth_sub_wmod T s R m
  rw [hfun, K6.psum_mul_abel]
  set a : ℕ → ℂ := fun j => ((K6.lamP R j - 1 : ℝ) : ℂ) with ha
  -- first term
  have t1 : ‖K6.psum n a * K6.wmod T s n‖ ≤ Es * W := by
    rw [norm_mul]
    by_cases h : K6.wmod T s n = 0
    · rw [h, norm_zero, mul_zero]; positivity
    · obtain ⟨h1, _⟩ := hsupp n h
      exact mul_le_mul (hE n (by linarith) hnR) (hw n) (norm_nonneg _) hEs
  -- second term
  have t2 : ‖∑ m ∈ Finset.range n, K6.psum m a * (K6.wmod T s (m + 1) - K6.wmod T s m)‖
      ≤ Es * W := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ m ∈ Finset.range n,
        ‖K6.psum m a * (K6.wmod T s (m + 1) - K6.wmod T s m)‖
          ≤ Es * ‖K6.wmod T s (m + 1) - K6.wmod T s m‖ := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [norm_mul]
      by_cases h : K6.wmod T s (m + 1) - K6.wmod T s m = 0
      · rw [h, norm_zero, mul_zero, mul_zero]
      · have hmR : (m : ℝ) ≤ Real.exp (s + 1) := le_trans (by exact_mod_cast hm.le) hnR
        have hlow : Real.exp (s - 1) - 1 ≤ (m : ℝ) := by
          by_cases h1 : K6.wmod T s (m + 1) = 0
          · have h2 : K6.wmod T s m ≠ 0 := by
              intro h2; apply h; rw [h1, h2, sub_zero]
            have := (hsupp m h2).1
            linarith
          · have := (hsupp (m + 1) h1).1
            push_cast at this
            linarith
        exact mul_le_mul_of_nonneg_right (hE m hlow hmR) (norm_nonneg _)
    calc ∑ m ∈ Finset.range n, ‖K6.psum m a * (K6.wmod T s (m + 1) - K6.wmod T s m)‖
        ≤ ∑ m ∈ Finset.range n, Es * ‖K6.wmod T s (m + 1) - K6.wmod T s m‖ :=
          Finset.sum_le_sum hterm
      _ = Es * ∑ m ∈ Finset.range n, ‖K6.wmod T s (m + 1) - K6.wmod T s m‖ := by
          rw [Finset.mul_sum]
      _ ≤ Es * ∑ m ∈ Finset.range ⌊Real.exp (s + 1)⌋₊, ‖K6.wmod T s (m + 1) - K6.wmod T s m‖ := by
          apply mul_le_mul_of_nonneg_left _ hEs
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn)
            (fun _ _ _ => norm_nonneg _)
      _ ≤ Es * W := mul_le_mul_of_nonneg_left hv hEs
  calc ‖K6.psum n a * K6.wmod T s n
        - ∑ m ∈ Finset.range n, K6.psum m a * (K6.wmod T s (m + 1) - K6.wmod T s m)‖
      ≤ ‖K6.psum n a * K6.wmod T s n‖
        + ‖∑ m ∈ Finset.range n, K6.psum m a * (K6.wmod T s (m + 1) - K6.wmod T s m)‖ :=
        norm_sub_le _ _
    _ ≤ Es * W + Es * W := add_le_add t1 t2
    _ = 2 * Es * W := by ring

end LemmaK
end ZetaShell
