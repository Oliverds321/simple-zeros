/-
Node K1s (L7_3): eq:K-fareysum — summing Lemma K.1 over `1 < q ≤ Q` and using `φ(q)/q ≤ 1`:
`Σ_{χ ∈ 𝔉_Q} |A_χ|² ≤ Σ_{ξ ∈ 𝔉_Q-Farey} |S(ξ)|²`, the Farey points `b/q`, `1 ≤ q ≤ Q`, `(b,q) = 1`.
"Because Lemma K.1 needs no support condition, primes in `(R₀, Q]` are never removed from `a`."
Dependencies: K1 (`gauss_sum_ineq`; here via trunk `ZetaQ.primitive_decomposition`). Difficulty: E. PROVED.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK

/-- **K1s (eq:K-fareysum).** -/
theorem farey_majorant (Q N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 2 Q, ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N a χ‖ ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ ZetaQ.reducedResidues q,
          ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
  have hsub : Finset.Icc 2 Q ⊆ Finset.Icc 1 Q := Finset.Icc_subset_Icc (by norm_num) le_rfl
  have hper : ∀ q ∈ Finset.Icc 2 Q,
      ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N a χ‖ ^ 2
        ≤ ∑ b ∈ ZetaQ.reducedResidues q, ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
    intro q hq
    have hq0 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have h := ZetaQ.primitive_decomposition q N hq0 a
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
    have hφq : (Nat.totient q : ℝ) / (q : ℝ) ≤ 1 := by
      rw [div_le_one hqR]; exact_mod_cast Nat.totient_le q
    have hR : 0 ≤ ∑ b ∈ ZetaQ.reducedResidues q, ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc _ ≤ _ := h
      _ ≤ 1 * ∑ b ∈ ZetaQ.reducedResidues q, ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hφq hR
      _ = _ := one_mul _
  calc _ ≤ ∑ q ∈ Finset.Icc 2 Q, ∑ b ∈ ZetaQ.reducedResidues q,
          ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := Finset.sum_le_sum hper
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

end LemmaK
end ZetaShell
