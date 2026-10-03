/-
Node A1′a (L7_6 statement draft): **Lemma 1′, the replacement cost** (lem:shell-1prime, sec_shell.tex l.238–254).

Draft: "Let `s ≥ (1+δ₁) log Q` and `a = a^P + a^R` with `a^P` supported on primes `> Q`. Then
`‖a^R(s)‖² ≤ (1+o(1))/(2π²δ₁²) + O(1)`, and replacing `a` by `a^P` costs a relative `O((δ₁²T log Q)^{−1/2})` in
`𝐅(s)/(|𝔉_Q|‖a‖²)`. Similarly `‖a^far‖² ≤ (2s/(π²κ))(1+o(1))`, and replacing `a` by `a^near` costs a relative
`2√(4C/(πκT)) ≈ 5.2(κT)^{−1/2}`." Proof: "Use `𝐅(a) ≤ (1+η)𝐅(a^P) + (1+η⁻¹)𝐅(a^R)` with `𝐅(a^R) ≤ (𝒳+Q²)‖a^R‖²`
(paper Lemma 6.1) and optimise `η`."

The lemma bundles three different facts. They are split into three nodes (one declaration each):
* **A1′a (this file)**: the replacement cost itself, exact and non-asymptotic:
  `𝐅(b + c) ≤ (√𝐅(b) + √((Q² + πN)‖c‖²))²` for any split `a = b + c` and any family of moduli `M ⊆ [1, Q]`. It is the
  optimised form of the draft's `η`-inequality (`min_η` of the right side is exactly this square), with the trunk's
  proved Gallagher budget `Q² + πN` in place of the paper's `𝒳 + Q²`. Both uses in the draft (`a^P`/`a^R` and
  `a^near`/`a^far`) are instances: the relative cost is `2√((Q²+πN)‖c‖²/𝐅(b)) + (Q²+πN)‖c‖²/𝐅(b)`.
* A1′b (`A1p_SmallPrimeNorm.lean`): the norm of the small-prime part.
* A1′c (`A1p_FarNorm.lean`): the norm of the far part (carries a **statement-change request**, see there).
No hypothesis on the supports is needed for A1′a.
Dependencies: trunk `ZetaQ.Gallagher.multiplicative_large_sieve_gallagher`; Cauchy–Schwarz (Minkowski) in `ℓ²` over the family.
Difficulty: E.
-/
import ZetaShell.Defs.TF_Defs

noncomputable section

namespace ZetaShell
namespace TrackF

/-- **A1′a (lem:shell-1prime, replacement cost).** -/
theorem replace_cost (Q N : ℕ) (M : Finset ℕ) (hM : M ⊆ Finset.Icc 1 Q) (b c : ℕ → ℂ) :
    famF M N (fun n => b n + c n)
      ≤ (Real.sqrt (famF M N b)
          + Real.sqrt (ZetaQ.Gallagher.gallagherBudget N Q * ZetaQ.l2sq N c)) ^ 2 := by
  classical
  have hA0 : 0 ≤ famF M N b :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  have hB0 : 0 ≤ famF M N c :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  have hBB' : famF M N c ≤ ZetaQ.Gallagher.gallagherBudget N Q * ZetaQ.l2sq N c := by
    calc famF M N c
        ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N c χ‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hM
            (fun _ _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
      _ ≤ ZetaQ.Gallagher.gallagherBudget N Q * ZetaQ.l2sq N c :=
          ZetaQ.Gallagher.multiplicative_large_sieve_gallagher Q N c
  have hsplit : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ZetaQ.charSum q N (fun n => b n + c n) χ = ZetaQ.charSum q N b χ + ZetaQ.charSum q N c χ := by
    intro q χ
    simp only [ZetaQ.charSum, add_mul, Finset.sum_add_distrib]
  have hpt : famF M N (fun n => b n + c n) ≤ ∑ q ∈ M, ∑ χ ∈ ZetaQ.primitiveChars q,
      (‖ZetaQ.charSum q N b χ‖ + ‖ZetaQ.charSum q N c χ‖) ^ 2 := by
    unfold famF
    refine Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun χ _ => ?_))
    rw [hsplit]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  have hexp : ∑ q ∈ M, ∑ χ ∈ ZetaQ.primitiveChars q,
      (‖ZetaQ.charSum q N b χ‖ + ‖ZetaQ.charSum q N c χ‖) ^ 2
      = famF M N b + 2 * (∑ q ∈ M, ∑ χ ∈ ZetaQ.primitiveChars q,
          ‖ZetaQ.charSum q N b χ‖ * ‖ZetaQ.charSum q N c χ‖) + famF M N c := by
    unfold famF
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    ring
  have hCS : ∑ q ∈ M, ∑ χ ∈ ZetaQ.primitiveChars q,
      ‖ZetaQ.charSum q N b χ‖ * ‖ZetaQ.charSum q N c χ‖
      ≤ Real.sqrt (famF M N b) * Real.sqrt (famF M N c) := by
    calc ∑ q ∈ M, ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N b χ‖ * ‖ZetaQ.charSum q N c χ‖
        ≤ ∑ q ∈ M, Real.sqrt (∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N b χ‖ ^ 2)
            * Real.sqrt (∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N c χ‖ ^ 2) :=
          Finset.sum_le_sum (fun q _ => Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
      _ ≤ Real.sqrt (∑ q ∈ M, Real.sqrt (∑ χ ∈ ZetaQ.primitiveChars q,
              ‖ZetaQ.charSum q N b χ‖ ^ 2) ^ 2)
            * Real.sqrt (∑ q ∈ M, Real.sqrt (∑ χ ∈ ZetaQ.primitiveChars q,
              ‖ZetaQ.charSum q N c χ‖ ^ 2) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt (famF M N b) * Real.sqrt (famF M N c) := by
          unfold famF
          congr 2
          · refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity))]
          · refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity))]
  have h1 : Real.sqrt (famF M N c)
      ≤ Real.sqrt (ZetaQ.Gallagher.gallagherBudget N Q * ZetaQ.l2sq N c) := Real.sqrt_le_sqrt hBB'
  have h2 : Real.sqrt (famF M N b) ^ 2 = famF M N b := Real.sq_sqrt hA0
  have h3 : Real.sqrt (ZetaQ.Gallagher.gallagherBudget N Q * ZetaQ.l2sq N c) ^ 2
      = ZetaQ.Gallagher.gallagherBudget N Q * ZetaQ.l2sq N c := Real.sq_sqrt (le_trans hB0 hBB')
  have h4 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (famF M N b))
  rw [hexp] at hpt
  nlinarith [Real.sqrt_nonneg (famF M N b), Real.sqrt_nonneg (famF M N c)]

end TrackF
end ZetaShell
