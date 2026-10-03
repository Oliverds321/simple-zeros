/-
Node K1 (L7_3): Lemma K.1 (lem:K-farey), the Gauss-sum inequality, for every `q ≥ 1` and every `(a_n)`:
`(q/φ(q)) Σ*_{χ mod q} |Σ_n a_n χ(n)|² ≤ Σ*_{b mod q} |S(b/q)|²`. "No support or coprimality condition is imposed on
`(a_n)`." In the tree this is `ZetaQ.primitive_decomposition` (Sieve.lean), stated with the factor `φ(q)/q` on
the right; K1 is its rearrangement. Dependencies: trunk `ZetaQ.primitive_decomposition`. Difficulty: E. PROVED.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK

/-- **K1 (Lemma K.1).** -/
theorem gauss_sum_ineq (q N : ℕ) (hq : 0 < q) (a : ℕ → ℂ) :
    ((q : ℝ) / (Nat.totient q : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N a χ‖ ^ 2
      ≤ ∑ b ∈ ZetaQ.reducedResidues q, ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
  have h := ZetaQ.primitive_decomposition q N hq a
  have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hc : 0 ≤ (q : ℝ) / (Nat.totient q : ℝ) := (div_pos hqR hφ).le
  calc ((q : ℝ) / (Nat.totient q : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N a χ‖ ^ 2
      ≤ ((q : ℝ) / (Nat.totient q : ℝ)) * (((Nat.totient q : ℝ) / (q : ℝ)) *
          ∑ b ∈ ZetaQ.reducedResidues q, ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h hc
    _ = ∑ b ∈ ZetaQ.reducedResidues q, ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
        field_simp

end LemmaK
end ZetaShell
