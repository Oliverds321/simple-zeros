/-
Node A1′c (L7_6 statement draft): **Lemma 1′, norm of the far part** (lem:shell-1prime, sec_shell.tex l.241–253,
second claim), with the near/far split of l.174–178.

Draft: "Fix `κ ∈ (0,1]` and `Ξ ∈ C_c^∞((−1,1))` with `0 ≤ Ξ ≤ 1`. Put `a^near_n = a_n Ξ((log n − s)/κ)`,
`a^far = a − a^near`" and "`‖a^far‖² ≤ (2s/(π²κ))(1+o(1))`"; proof: "`‖a^far‖² ≤ (1/4π²) Σ_{|log n−s|>κ}
Λ(n)² n⁻¹ · 4/(log n − s)²`".

**Statement-change request (missing hypothesis).** As written the claim is false: `Ξ ≡ 0` satisfies the draft's
hypotheses, and then `a^far = a`, `‖a^far‖² = ‖a‖² ≍ sT/(2π)`, which is not `≤ (2s/(π²κ))(1+o(1))` as `T → ∞`.
The proof needs `a^far_n = 0` for `|log n − s| ≤ κ`, i.e. `Ξ = 1` on `[−1, 1]`, impossible for
`supp Ξ ⊂ (−1,1)`. Corrected hypothesis: `Ξ = 1` on `[−c, c]` for some `c ∈ (0, 1)`; the constant becomes
`2s/(π² c κ)` and the replacement cost `2√(4C/(π c κ T))`. (Lemma 4's model mass `U(1 − O(K⁻²))` also needs
`Ξ(0) = 1`, see the report.) Since `κ` is free, downstream constants change only by the factor `c`.

Lean form (exact, non-asymptotic): with `0 ≤ Ξ ≤ 1` and `Ξ = 1` on `[−c, c]`,
`Σ_{0<n≤N} |a_n(s)(1 − Ξ((log n − s)/κ))|² ≤ π⁻² Σ_{0<n≤N, |log n − s| > cκ} Λ(n)²/(n (log n − s)²)`.
The asymptotic `(2s/(π² c κ))(1+o(1))` then needs the prime number theorem in short ranges (`PNTErrorTerm`).
Dependencies: `|D_T(v)| ≤ 2/|v|` (`acoefS_normSq_le` of A1′b). Difficulty: E.
**PROVED (L7_6)** (the corrected form; the draft's form is false, see above).
-/
import ZetaShell.Farey.A1p_SmallPrimeNorm

noncomputable section

namespace ZetaShell
namespace TrackF

/-- **A1′c (lem:shell-1prime, far part; corrected hypothesis `Ξ = 1` on `[−c, c]`).** -/
theorem far_norm (N : ℕ) (T s κ c : ℝ) (Ξ : ℝ → ℝ) (hκ : 0 < κ) (hc : 0 < c)
    (hΞ0 : ∀ x, 0 ≤ Ξ x) (hΞ1 : ∀ x, Ξ x ≤ 1) (hΞc : ∀ x, |x| ≤ c → Ξ x = 1) :
    ∑ n ∈ Finset.Ioc 0 N, ‖acoefS T s n * ((1 - Ξ ((Real.log n - s) / κ) : ℝ) : ℂ)‖ ^ 2
      ≤ (1 / Real.pi ^ 2) * ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => c * κ < |Real.log n - s|),
          ArithmeticFunction.vonMangoldt n ^ 2 / ((n : ℝ) * (Real.log n - s) ^ 2) := by
  classical
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [Finset.mem_Ioc] at hn
  have hsplit : ‖acoefS T s n * ((1 - Ξ ((Real.log n - s) / κ) : ℝ) : ℂ)‖ ^ 2
      = ‖acoefS T s n‖ ^ 2 * (1 - Ξ ((Real.log n - s) / κ)) ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hsplit]
  split_ifs with hP
  · have hv : s - Real.log n ≠ 0 := by
      intro h0
      have : |Real.log n - s| = 0 := by rw [abs_eq_zero]; linarith
      have hcκ : 0 < c * κ := mul_pos hc hκ
      linarith
    have h1 := acoefS_normSq_le T s n hn.1 hv
    have hΞ : (1 - Ξ ((Real.log n - s) / κ)) ^ 2 ≤ 1 := by
      have a1 := hΞ0 ((Real.log n - s) / κ)
      have a2 := hΞ1 ((Real.log n - s) / κ)
      nlinarith
    have hsq : (s - Real.log n) ^ 2 = (Real.log n - s) ^ 2 := by ring
    calc ‖acoefS T s n‖ ^ 2 * (1 - Ξ ((Real.log n - s) / κ)) ^ 2 ≤ ‖acoefS T s n‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hΞ (sq_nonneg _)
      _ ≤ ArithmeticFunction.vonMangoldt n ^ 2 / ((n : ℝ) * Real.pi ^ 2 * (s - Real.log n) ^ 2) := by
          rw [mul_one]; exact h1
      _ = 1 / Real.pi ^ 2 * (ArithmeticFunction.vonMangoldt n ^ 2 / ((n : ℝ) * (Real.log n - s) ^ 2)) := by
          rw [hsq]
          field_simp
  · have hle : |(Real.log n - s) / κ| ≤ c := by
      rw [abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
      have hP' := not_lt.mp hP
      linarith
    rw [hΞc _ hle, sub_self]
    simp

end TrackF
end ZetaShell
