/-
A2a_S3d_ArithSplit (L7_8, round 4): split of `s3_arith` into two analytic sub-nodes, with the derivation proved.
* `s3_arith_inner` (open): for each line `0 < |j|`,
  `2^{ω(|j|)} Σ_{e≤Q, e|j|≤X} |c_e| Σ_{f≤Q} |λ_e(f)| ≤ C₁(1 + log Q)·g_X(|j|)`,
  `g_X(n) = τ(n)(1 + log(X/n))²` for `n ≤ X`, `0` otherwise
  (from `|λ_e(f)| ≤ gcd(f,e)/f`, `Σ_{f≤Q} gcd(f,e)/f ≤ τ(e)(1 + log Q)`, `Σ_{e≤y}|c_e|τ(e) ≪ (1 + log y)²`,
  `2^ω ≤ τ`);
* `s3_arith_jsum` (open): `Σ_{0<|j|≤X+1} g_X(|j|) ≤ C₂(X + 1)(1 + log(X + 1))`
  (`Σ_{n≤X} τ(n)(1 + log(X/n))² ≪ X(1 + log X)`, both signs of `j`).
* `s3_arith_of_split`: the statement of `s3_arith` follows (`C = C₁C₂`).
-/
import ZetaShell.Lemma2.A2a_S3_Defs

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

def gX (X : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ X then (n.divisors.card : ℝ) * (1 + Real.log (X / n)) ^ 2 else 0

theorem s3_arith_inner : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : FKind) (Q : ℕ) (X : ℝ) (j : ℤ), 2 ≤ Q → 0 ≤ X → j ≠ 0 →
    (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) *
      ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
        |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
      ≤ C * ((1 + Real.log Q) * gX X j.natAbs) := by
  sorry

theorem s3_arith_jsum : ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℝ), 0 ≤ X →
    ∑ j ∈ lineSet (⌊X⌋₊ + 1), gX X j.natAbs ≤ C * ((X + 1) * (1 + Real.log (X + 1))) := by
  sorry

theorem s3_arith_of_split : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : FKind) (Q : ℕ) (X : ℝ), 2 ≤ Q → 0 ≤ X →
    ∑ j ∈ lineSet (⌊X⌋₊ + 1), (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) *
      ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
        |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
      ≤ C * ((X + 1) * (1 + Real.log (X + 1)) * (1 + Real.log Q)) := by
  obtain ⟨C1, hC1, h1⟩ := s3_arith_inner
  obtain ⟨C2, hC2, h2⟩ := s3_arith_jsum
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro k Q X hQ hX
  have hlQ : 0 ≤ 1 + Real.log Q := by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    have := Real.log_nonneg this; linarith
  calc _ ≤ ∑ j ∈ lineSet (⌊X⌋₊ + 1), C1 * ((1 + Real.log Q) * gX X j.natAbs) := by
        apply Finset.sum_le_sum
        intro j hj
        exact h1 k Q X j hQ hX (Finset.mem_filter.mp hj).2
    _ = C1 * (1 + Real.log Q) * ∑ j ∈ lineSet (⌊X⌋₊ + 1), gX X j.natAbs := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ C1 * (1 + Real.log Q) * (C2 * ((X + 1) * (1 + Real.log (X + 1)))) :=
        mul_le_mul_of_nonneg_left (h2 X hX) (mul_nonneg hC1 hlQ)
    _ = C1 * C2 * ((X + 1) * (1 + Real.log (X + 1)) * (1 + Real.log Q)) := by ring

end TrackF
end ZetaShell
