/-
L7_9 round 2, sub-node K6b (Gallagher's `L²` lemma with the explicit constant, lem:K-P Step 2) of `principal_arc_mass` (K6).
Draft: "For `h := 1/(2Δ)` and any finitely supported `(c_n)`,
`∫_{|β|≤Δ}|Σ c_n e(nβ)|² ≤ π²Δ² ∫_ℝ |Σ_{x<n≤x+h} c_n|² dx`" ([Gal70, Lemma 1]): the Fourier transform of
`C(x)` has modulus `|S(−β)|·|sin πhβ|/(π|β|) ≥ |S(−β)|/(πΔ)` on `|β| ≤ Δ`; Plancherel.
-/
import ZetaShell.LemmaK.LK9_K6_Defs

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

theorem gallagher_L2 (N : ℕ) (c : ℕ → ℂ) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N c β‖ ^ 2
      ≤ Real.pi ^ 2 * Δ ^ 2 * ∫ x : ℝ, ‖K6.blockSum N c (1 / (2 * Δ)) x‖ ^ 2 := by
  sorry

end LemmaK
end ZetaShell
