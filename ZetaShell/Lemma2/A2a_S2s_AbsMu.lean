/-
A2a_S2s_AbsMu (L7_8, round 3): `Σ_{g | n} |μ(g)| = 2^{ω(n)}` (`n ≥ 1`). PROVED (sorry-free), from Mathlib's
`Nat.sum_divisors_filter_squarefree` (squarefree divisors ↔ subsets of the prime factors).
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem s2_abs_mu (n : ℕ) (hn : n ≠ 0) :
    ∑ g ∈ n.divisors, |((ArithmeticFunction.moebius g : ℤ) : ℝ)|
      = (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) := by
  classical
  have h1 : ∀ g ∈ n.divisors, |((ArithmeticFunction.moebius g : ℤ) : ℝ)| = if Squarefree g then 1 else 0 := by
    intro g _
    rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hn]
  simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one]
  push_cast
  congr 1
  rw [Nat.factors_eq, ArithmeticFunction.cardDistinctFactors_apply]
  first | rfl | simp [Multiset.toFinset, Multiset.coe_dedup]

end TrackF
end ZetaShell
