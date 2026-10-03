/-
Node K7c (L7_3, round 3): the plain Gallagher bound for the family `2 ≤ q ≤ Q`, for any coefficients:
`Σ_{2≤q≤Q} Σ*_χ |Σ_{n≤N} a_n χ(n)|² ≤ (Q² + πN)‖a‖²`. Off the hole range Lemma K (i) is this bound (the subtracted term is 0).
From trunk `ZetaQ.Gallagher.multiplicative_large_sieve_gallagher` (sum over `1 ≤ q ≤ Q`, nonnegative terms). PROVED.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK

/-- **K7c.** -/
theorem plain_bound (Qn N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 2 Qn, ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N a χ‖ ^ 2
      ≤ ((Qn : ℝ) ^ 2 + Real.pi * N) * ZetaQ.l2sq N a := by
  have h := ZetaQ.Gallagher.multiplicative_large_sieve_gallagher Qn N a
  have hsub : Finset.Icc 2 Qn ⊆ Finset.Icc 1 Qn := Finset.Icc_subset_Icc (by norm_num) le_rfl
  have h2 : ∑ q ∈ Finset.Icc 2 Qn, ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N a χ‖ ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 Qn, ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N a χ‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have e : ZetaQ.Gallagher.gallagherBudget N Qn = (Qn : ℝ) ^ 2 + Real.pi * N := rfl
  rw [e] at h
  exact h2.trans h

end LemmaK
end ZetaShell
