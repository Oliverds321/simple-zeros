/-
L7_9 round 2, sub-node K6a (model mass, lem:K-P Step 1) of `principal_arc_mass` (K6).
Draft: summation by parts and `|1 − e(β)| ≥ 4‖β‖` give `∫_{‖β‖>Δ}|M̃|² ≤ (16Δ²)⁻¹∫|w̃′|²`, with
`∫|w̃′|² ≤ 2.88 T³/N²` (Plancherel: `‖D_T‖₂² = 2πT`, `‖D_T′‖₂² = 14πT³/3`), so the mass outside `|β| ≤ Δ` is
`≤ 4.6U/K²`; also `Σ|w̃(n)|² ≥ U − 1` (sum vs integral). Hence `∫_{|β|≤Δ}|M̃|² ≥ U − 1 − 4.6U/K²`, and with
`K = ℒ`, `U = T/2π ≫ log Q`, this is `≥ (1 − C/log Q)U`. Uses the cutoff `rho6` (`|ϱ′| ≤ 2`) in place of the draft's.
-/
import ZetaShell.LemmaK.LK9_K6_Defs
import ZetaShell.LemmaK.LK9_K6a_Split

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

theorem model_mass (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      (1 - C / Real.log (Qn : ℝ)) * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi))
        ≤ ∫ β in (-(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))..(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)), ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s) β‖ ^ 2 := by
  exact model_mass_of_split lam r ε hlam1 hlam2 hr hε

end LemmaK
end ZetaShell
