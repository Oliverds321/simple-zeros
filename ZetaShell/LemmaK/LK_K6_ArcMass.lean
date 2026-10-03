/-
Node K6 (L7_3): Lemma K.6 (lem:K-P), the principal-arc mass. Draft: "Let `ℓ_K ≤ s ≤ log 𝒳 − 1`, `T ≥ 100` and `K ≥ 3`.
Then `J ≥ (1 − η_P)U`, `η_P := 2/U + 9.2/K² + 2(E₁ + E₂)/√U`", with `J = ∫_{|β|≤Δ} |S′(β)|² dβ`, `U = T/2π`,
`Δ = KT/(2N)`, `N = e^s`; "Size of η_P": `η_P = O((ℒ/T)^{1/2} + ℒ^{−2})`, so for `r ≥ 3`, `η_P = O(1/log Q)`.
Lean form: the asymptotic consequence the consumer (K7) needs — `∃ C, eventually, J ≥ (1 − C/log Q)·U` on
`[ℓ_K, log 𝒳 − 1]` — with `K = ℒ`, `T = (log Q)^{r+ε}`, `a′ = aPrime`, read on `n ≤ ⌊𝒳⌋`.
**PNT input: none displayed.** Step 3 needs `E*/N = o(K^{−1}T^{−3/2})` at `N ≥ QTK`, i.e. `ψ(y) − y = o(y (log y)^{−A})`
for the fixed `A = 2 + 2(r+ε)`; this is `L7_2.psi_sub_id_isLittleO_log_rpow` (imported, level A, from the tree's
`MediumPNT`). **Mertens input:** the draft's unverified "`|R(x)| ≤ 2`" of Step 4 is replaced by the tree's
`Mertens.sum_mangoldt_div_eq_log` (`|Σ_{d≤x} Λ(d)/d − log x| ≤ log 4 + 4`), which changes the E₂ constant
`33.3 → 85` (`E₂²/U ≤ 85 λℒ/T`) and nothing asymptotic.
Dependencies: Steps 1–4 (model mass; Gallagher's `L²` lemma with `π²Δ²`; partial summation with `E(y)`; tails),
`PNTMedium`, trunk Mertens. Difficulty: H (four M sub-nodes: K6a model mass, K6b Gallagher `L²`, K6c PNT step, K6d tails).
-/
import ZetaShell.Defs.LK_Defs
import ZetaShell.PNT.PNTMedium
import ZetaShell.LemmaK.LK9_K6_Derive

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

/-- **K6 (Lemma K.6), asymptotic form.** -/
theorem principal_arc_mass (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      (1 - C / Real.log (Qn : ℝ)) * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi))
        ≤ ∫ β in (-(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))..
              (ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)),
            ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
              (aPrime (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)) β‖ ^ 2 := by
  exact K6.principal_arc_mass_of_nodes lam r ε hlam1 hlam2 hr hε

end LemmaK
end ZetaShell
