/-
Node A1′b (L7_6 statement draft): **Lemma 1′, norm of the small-prime part** (lem:shell-1prime, sec_shell.tex
l.238–249, first claim).

Draft: "`‖a^R(s)‖² ≤ (1+o(1))/(2π²δ₁²) + O(1)`" for `s ≥ (1+δ₁) log Q`; proof: "From `|D_T(v)| ≤ min(T, 2/|v|)`,
`‖a^R‖² ≤ (1/4π²)[Σ_{p≤Q} (log p)² p⁻¹ · 4/(δ₁ log Q)² + O(1)]`; the prime-power peak is `≪ T(log N)² N^{−1/2}`."

Lean form: the exact, non-asymptotic part for all `n ≤ Q` (primes and prime powers `≤ Q`):
`Σ_{0<n≤Q} |a_n(s)|² ≤ (Σ_{0<n≤Q} Λ(n)²/n) / (π²(s − log Q)²)` for `s > log Q`, from `|D_T(v)| ≤ 2/|v|`.
With `s − log Q ≥ δ₁ log Q` and `Σ_{n≤Q} Λ(n)²/n = (½ + o(1)) log² Q` (Mertens-type; not in Mathlib, a separate
classical input) this is the draft's `(1+o(1))/(2π²δ₁²)`.
Not drafted here: the prime powers `p^k > Q` with `p ≤ Q` (the draft's `O(1)` and "prime-power peak"). Remark: with
`|D_T| ≤ T` the peak is `≪ T²(log N)² N^{−1/2}` (the draft prints `T`, not `T²`; harmless since `N ≥ Q` and
`T = (log Q)^{r+ε}`).
No hypothesis on `T` is needed (`|D_T(v)| ≤ 2/|v|` holds for every real `T`).
Dependencies: `|∫_T^{2T} e^{iτv} dτ| ≤ 2/|v|` (Mathlib `integral_exp_mul_complex`), `log n ≤ log Q`. Difficulty: E.
**PROVED (L7_6)** together with the helpers `norm_DTk_le` and `acoefS_normSq_le` (used by A1′c).
-/
import ZetaShell.Defs.TF_Defs

noncomputable section

namespace ZetaShell
namespace TrackF

/-- `|D_T(v)| ≤ 2/|v|` for `v ≠ 0` (any real `T`). -/
theorem norm_DTk_le (T v : ℝ) (hv : v ≠ 0) : ‖DTk T v‖ ≤ 2 / |v| := by
  have hc : (Complex.I * (v : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hv)
  have h1 : DTk T v = ∫ τ in T..(2 * T), Complex.exp ((Complex.I * (v : ℂ)) * (τ : ℂ)) := by
    unfold DTk
    congr 1
    ext τ
    ring_nf
  rw [h1, integral_exp_mul_complex hc, norm_div]
  have hnum : ‖Complex.exp (Complex.I * (v : ℂ) * ((2 * T : ℝ) : ℂ))
      - Complex.exp (Complex.I * (v : ℂ) * ((T : ℝ) : ℂ))‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (Complex.I * (v : ℂ) * ((2 * T : ℝ) : ℂ))‖
          + ‖Complex.exp (Complex.I * (v : ℂ) * ((T : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by
          rw [Complex.norm_exp, Complex.norm_exp]
          simp
          norm_num
  have hden : ‖Complex.I * (v : ℂ)‖ = |v| := by simp
  rw [hden]
  exact div_le_div_of_nonneg_right hnum (abs_nonneg v)

/-- `|a_n(s)|² ≤ Λ(n)²/(π² n (s − log n)²)` for `n ≥ 1`, `s ≠ log n`. -/
theorem acoefS_normSq_le (T s : ℝ) (n : ℕ) (hn : 0 < n) (hv : s - Real.log n ≠ 0) :
    ‖acoefS T s n‖ ^ 2
      ≤ ArithmeticFunction.vonMangoldt n ^ 2 / ((n : ℝ) * Real.pi ^ 2 * (s - Real.log n) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hD := norm_DTk_le T (s - Real.log n) hv
  have hD2 : ‖DTk T (s - Real.log n)‖ ^ 2 ≤ 4 / (s - Real.log n) ^ 2 := by
    have h0 : 0 ≤ ‖DTk T (s - Real.log n)‖ := norm_nonneg _
    calc ‖DTk T (s - Real.log n)‖ ^ 2 ≤ (2 / |s - Real.log n|) ^ 2 := pow_le_pow_left₀ h0 hD 2
      _ = 4 / (s - Real.log n) ^ 2 := by rw [div_pow, sq_abs]; norm_num
  have hnorm : ‖acoefS T s n‖ ^ 2 = ((2 * Real.pi)⁻¹ * ArithmeticFunction.vonMangoldt n
      * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2 * ‖DTk T (s - Real.log n)‖ ^ 2 := by
    rw [acoefS, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hnorm]
  have hc2 : ((2 * Real.pi)⁻¹ * ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2
      = ArithmeticFunction.vonMangoldt n ^ 2 / (4 * Real.pi ^ 2 * n) := by
    rw [mul_pow, mul_pow, hpow]
    field_simp
    ring
  rw [hc2]
  have hv2 : 0 < (s - Real.log n) ^ 2 := by positivity
  calc ArithmeticFunction.vonMangoldt n ^ 2 / (4 * Real.pi ^ 2 * n) * ‖DTk T (s - Real.log n)‖ ^ 2
      ≤ ArithmeticFunction.vonMangoldt n ^ 2 / (4 * Real.pi ^ 2 * n) * (4 / (s - Real.log n) ^ 2) :=
        mul_le_mul_of_nonneg_left hD2 (by positivity)
    _ = ArithmeticFunction.vonMangoldt n ^ 2 / ((n : ℝ) * Real.pi ^ 2 * (s - Real.log n) ^ 2) := by
        field_simp

/-- **A1′b (lem:shell-1prime, small primes).** -/
theorem small_prime_norm (Q : ℕ) (T s : ℝ) (hs : Real.log Q < s) :
    ∑ n ∈ Finset.Ioc 0 Q, ‖acoefS T s n‖ ^ 2
      ≤ (∑ n ∈ Finset.Ioc 0 Q, ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ))
          / (Real.pi ^ 2 * (s - Real.log Q) ^ 2) := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [Finset.mem_Ioc] at hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hlog : Real.log n ≤ Real.log Q := Real.log_le_log hnR (by exact_mod_cast hn.2)
  have hgap : 0 < s - Real.log Q := by linarith
  have hgap' : s - Real.log Q ≤ s - Real.log n := by linarith
  have h1 := acoefS_normSq_le T s n hn.1 (by linarith)
  refine h1.trans ?_
  have hsq : (s - Real.log Q) ^ 2 ≤ (s - Real.log n) ^ 2 := pow_le_pow_left₀ hgap.le hgap' 2
  rw [div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : (n : ℝ) * (Real.pi ^ 2 * (s - Real.log Q) ^ 2) ≤ (n : ℝ) * Real.pi ^ 2 * (s - Real.log n) ^ 2 := by
    have hpi : 0 < Real.pi ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt (mul_pos hnR hpi))]
  exact this

end TrackF
end ZetaShell
