/-
Node K2 (L7_3): Lemma K.2 (lem:K-G), Gallagher's inequality with weights and a zero set.
Draft: "Let `Ξ ⊂ ℝ/ℤ` be finite, `w_ξ ≥ 0`, `0 < δ < 1`, `D_δ(θ) := δ⁻¹ Σ_{‖ξ−θ‖≤δ/2} w_ξ` and
`Z := {θ : D_δ(θ) = 0}`. If `(a_n)` is supported on the integers of `[1, 𝒳]`, then
`Σ_ξ w_ξ |S(ξ)|² ≤ sup_θ D_δ(θ) (‖a‖² − ∫_Z |S|² + π𝒳δ‖a‖²)`."
Lean form: `a` is read on `n ∈ (0, N]` (`ZetaQ.expSum N a`, so the support condition is built in, `𝒳 = N`);
`sup D_δ` is any upper bound `Dsup`; `Z` is taken inside one period `[0, 1)`.
Numerics: `numerics/ktests.py` (300 random trials, weights, repeated points; max (LHS − RHS)/‖a‖² = −0.39).
Dependencies: trunk `ZetaQ.Gallagher` (`point_bound_integral`, `parseval_trig`, `integral_normSq_expSumD_le`,
`sum_integral_le_period` — the proof of `gallagher_additive_large_sieve` with `w_ξ` and `Z` added). Difficulty: M.
-/
import ZetaShell.Defs.LK_Defs
import ZetaShell.LemmaK.LK9_K2_Aux

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace LemmaK

/-! Integration note (L0_6, 28 Sep 2026): the frozen K2 statement `gallagher_with_zero_set`
(L7_3's skeleton, closed by `sorry`) is NOT placed in the library, by the lead's brief: it is
false as Lean parses it (refuted below). The node of record is `gallagher_with_zero_set_corr`. -/

/-! L7_9 (28 Sep 2026). The frozen statement (not placed) is FALSE as Lean parses it: the binder of
`∫ θ in A, ‖S θ‖ ^ 2 + π N δ ‖a‖²` extends to the right, so the right side is
`Dsup·(‖a‖² − ∫_{A∩Z}(|S|² + πNδ‖a‖²))`, not the draft's `Dsup·(‖a‖² − ∫_{A∩Z}|S|² + πNδ‖a‖²)`.
`gallagher_with_zero_set_false` refutes it (`s = ∅`, `N = 1`, `a ≡ 1`, `δ = 1/2`, `Dsup = 1`: `0 ≤ −π/2`).
The draft's lem:K-G, with the integral parenthesised, is `gallagher_with_zero_set_corr` (proved). -/

/-- **K2 (Lemma K.2), corrected statement**: the `Z`-integral is parenthesised. -/
theorem gallagher_with_zero_set_corr {ι : Type} (s : Finset ι) (ξ w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (N : ℕ) (a : ℕ → ℂ) (Dsup : ℝ)
    (hD : ∀ θ : ℝ, Ddens s ξ w δ θ ≤ Dsup) :
    ∑ i ∈ s, w i * ‖ZetaQ.expSum N a (ξ i)‖ ^ 2
      ≤ Dsup * (ZetaQ.l2sq N a
          - (∫ θ in Set.Ico (0 : ℝ) 1 ∩ {θ | Ddens s ξ w δ θ = 0}, ‖ZetaQ.expSum N a θ‖ ^ 2)
          + Real.pi * N * δ * ZetaQ.l2sq N a) :=
  K2Aux.gallagher_zero_aux s ξ w hw δ hδ hδ1 N a Dsup hD

/-- The frozen statement of K2, as parsed, is false (instance `ι = Unit`). -/
theorem gallagher_with_zero_set_false :
    ¬ (∀ (s : Finset Unit) (ξ w : Unit → ℝ) (_hw : ∀ i, 0 ≤ w i)
      (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1) (N : ℕ) (a : ℕ → ℂ) (Dsup : ℝ)
      (_hD : ∀ θ : ℝ, Ddens s ξ w δ θ ≤ Dsup),
    ∑ i ∈ s, w i * ‖ZetaQ.expSum N a (ξ i)‖ ^ 2
      ≤ Dsup * (ZetaQ.l2sq N a
          - ∫ θ in Set.Ico (0 : ℝ) 1 ∩ {θ | Ddens s ξ w δ θ = 0}, ‖ZetaQ.expSum N a θ‖ ^ 2
          + Real.pi * N * δ * ZetaQ.l2sq N a)) :=
  K2Aux.gallagher_with_zero_set_false

end LemmaK
end ZetaShell
