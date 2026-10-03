/-
S1_Defs (L7_5b, 1 Oct 2026): objects for the derivation of S1 (`S1_ring_to_zeros`, L7_10, Theorem S step 1) from
Proposition Z (`propZ_W`, L7_5) and A⋆ (`ring_le_primitive_corr`, L7_6 round 2, open).
* `AstarCorrStmt`: the statement of L7_6's `ZetaShell.TrackF.ring_le_primitive_corr` (lean_work/L7_6/r2/Astar_Corr.lean,
  sha256 in the report), VERBATIM, as a Prop; `S1_AstarLink.lean` checks that L7_6's theorem proves it.
* `Mmod`: the model `M_s(β) = −(2π)⁻¹ ∫_0^∞ A_s(y) e(yβ) dy` subtracted at `r = 1` (the δ_{r=1} term of `Schi`,
  scaled as the coefficients `a_n = −(2π)⁻¹ Λ(n) A_s(n)` of `aNearP`).
* `PPart`: the prime-power part `Σ_{0<n≤N(s), n not prime} Λ(n) χ(n) A_s(n) e(nβ)` (Lemma 5c(1)'s object).
-/
import ZetaShell.ShellS.L10_Defs
import ZetaShell.PropZ.Z5_PropZWdom

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- **A⋆ corrected** (`ZetaShell.TrackF.ring_le_primitive_corr`, L7_6 r2), its statement verbatim as a Prop. -/
def AstarCorrStmt : Prop :=
  ∀ (Q R1 N : ℕ) (K Cμ U : ℝ) (a : ℕ → ℂ) (M : ℝ → ℂ),
    1 ≤ K → 2 * K * R1 ≤ Q → 0 ≤ Cμ →
    (∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → ∀ p : ℕ, p.Prime → p ∣ n → Q < p) →
    (∀ y : ℝ, 0 < y →
      ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
        ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) ≤ Real.log K + Cμ) →
    Continuous M → (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖M β‖ ^ 2) ≤ U →
    TrackF.ringMass Q R1 N K a
      ≤ 2 * (Real.log K + Cμ) * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ χ ∈ ZetaQ.primitiveChars r,
            (∫ β in {β : ℝ | 1 / ((R1 : ℝ) * Q) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Q)},
              ‖TrackF.twistSum N a χ β - (if r = 1 then M β else 0)‖ ^ 2))
        + 2 * (Real.log K + Cμ) * U

/-- the model term `M_s(β) = −(2π)⁻¹ ∫_0^∞ A_s(y) e(yβ) dy`. -/
def Mmod (T κ : ℝ) (Ξ : ℝ → ℝ) (s β : ℝ) : ℂ :=
  -(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ y in Set.Ioi (0 : ℝ), As T κ Ξ s y * eA (y * β)

/-- the prime-power part `Σ_{0<n≤N(s), n not prime} Λ(n) χ(n) A_s(n) e(nβ)`. -/
def PPart {r : ℕ} (χ : DirichletCharacter ℂ r) (T κ : ℝ) (Ξ : ℝ → ℝ) (s β : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter (fun n => ¬ n.Prime),
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * As T κ Ξ s n * eA (n * β)

end ShellS
end ZetaShell
