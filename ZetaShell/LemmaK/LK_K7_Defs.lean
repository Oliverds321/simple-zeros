/-
lean_work/L7_3/skeleton/LK_K7_Defs.lean (L7_3, round 3): the hole integral of Lemma K's proof, eq:K-G-applied / eq:K-hole:
`Hole(S) = Σ_{r ≤ R₀} Σ*_{a mod r} ∫_{|β|≤Δ} |S(a/r + β)|² dβ`, `S = ZetaQ.expSum N a`.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK

/-- `Hole(S) = Σ_{1 ≤ r ≤ ⌊R⌋} Σ_{b reduced mod r} ∫_{−Δ}^{Δ} |S(b/r + β)|² dβ`. -/
def holeInt (N : ℕ) (a : ℕ → ℂ) (R Δ : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 ⌊R⌋₊, ∑ b ∈ ZetaQ.reducedResidues r,
    ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2

end LemmaK
end ZetaShell
