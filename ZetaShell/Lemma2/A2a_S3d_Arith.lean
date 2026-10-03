/-
A2a_S3d_Arith (L7_8, round 3): **the sums over `j`, `e`, `f` with the `2^ω` and logarithmic factors** (Step 3,
sec_shell.tex l.337–340): `Σ_{0<|j|≤X+1} 2^{ω(|j|)} Σ_{e : e|j| ≤ X} |c_e| Σ_{f≤Q} |λ_e(f)| ≪ (X+1)(1+log(X+1))(1+log Q)`.
Ingredients: `Σ_{f≤Q}|λ_e(f)| ≤ 2^{ω(e)}(1 + log Q)`, `Σ_{e≤y}|c_e|2^{ω(e)} ≪ (1 + log y)²`,
`Σ_{j≤X} 2^{ω(j)}(1 + log(X/j))² ≪ X(1 + log X)`. Round 5: DERIVED from `s3_arith_inner4`, `s3_arith_jsum4` (A2a_S3d_Route4, exponent 4, proved; route (b)). Round 4: was derived from `s3_arith_inner_pf` (A2a_S3d_InnerProof; open leaf `ce_tau_le`) and `s3_arith_jsum_pf` (A2a_S3d_JsumProof, proved). Tested numerically (`numerics/step3_split_test.py`).
-/
import ZetaShell.Lemma2.A2a_S3_Defs
import ZetaShell.Skeleton.A2a_S3d_ArithSplit
import ZetaShell.Lemma2.A2a_S3d_JsumProof
import ZetaShell.Lemma2.A2a_S3d_InnerProof
import ZetaShell.Lemma2.A2a_S3d_Route4

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem s3_arith : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : FKind) (Q : ℕ) (X : ℝ), 2 ≤ Q → 0 ≤ X →
    ∑ j ∈ lineSet (⌊X⌋₊ + 1), (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) *
      ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
        |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
      ≤ C * ((X + 1) * (1 + Real.log (X + 1)) * (1 + Real.log Q)) := by
  obtain ⟨C1, hC1, h1⟩ := s3_arith_inner4
  obtain ⟨C2, hC2, h2⟩ := s3_arith_jsum4
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro k Q X hQ hX
  have hlQ : 0 ≤ 1 + Real.log Q := by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    have := Real.log_nonneg this; linarith
  calc _ ≤ ∑ j ∈ lineSet (⌊X⌋₊ + 1), C1 * ((1 + Real.log Q) * gX4 X j.natAbs) := by
        apply Finset.sum_le_sum
        intro j hj
        exact h1 k Q X j hQ hX (Finset.mem_filter.mp hj).2
    _ = C1 * (1 + Real.log Q) * ∑ j ∈ lineSet (⌊X⌋₊ + 1), gX4 X j.natAbs := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ C1 * (1 + Real.log Q) * (C2 * ((X + 1) * (1 + Real.log (X + 1)))) :=
        mul_le_mul_of_nonneg_left (h2 X hX) (mul_nonneg hC1 hlQ)
    _ = C1 * C2 * ((X + 1) * (1 + Real.log (X + 1)) * (1 + Real.log Q)) := by ring

end TrackF
end ZetaShell
