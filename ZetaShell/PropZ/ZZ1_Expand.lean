/-
Sub-node Z5Z-1 (L7_5, round 2), Step 3 of prop:shell-Z: scaling `Ṽ_{Nξ,s}(ρ) = N^{ρ−1/2} I_ρ(ξ;μ_s)` and expansion
`Δ²∫|Σ_ρ Ṽ_{x,s}(ρ)|²dx = Σ_{ρ,ρ′} e^{is(γ−γ′)} Ψ_{ρρ′}(s)`, integrated against `W(s−s₀)`; the interchange of `∫ds`,
`∫dx` and the double zero sum is part of the node (absolute convergence: Step 4 and the zero count).
Status: OPEN (sorry) until round 9; see Round 10 below.
Round 5: `Z5Z_expand_S4` is the same statement with Step 4's conclusion `hone` as a hypothesis (Lead, 16:43);
it is weaker than `Z5Z_expand`, is the leaf now used by `Z5ZeroW`. `Z5Z_expand` is kept unchanged.
Round 10 (L7_5b, 1 Oct 2026): BOTH theorems are PROVED, from `Z5Z_expand_S4'` (ZZ1b_Expand.lean, L7_5 round 9),
whose proof does not use `hone`; `Z5Z_expand` instantiates it with `A = 0`, `k = 2` and Step 4 (`Z5Z_oneZero'`).
Statements unchanged.
-/
import ZetaShell.PropZ.ZZ2a_OneZeroSplit
import ZetaShell.PropZ.ZZ1b_Expand

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem Z5Z_expand (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      Integrable (fun s => W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))) ∧
      Summable (pairInt χ T κ Ξ f W Δ s₀) ∧
      (((∫ s, W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))) : ℝ) : ℂ)
        = ∑' p, pairInt χ T κ Ξ f W Δ s₀ p :=
  Z5Z_expand_S4' κ hκ hκ1 Ξ hΞ f hf 0 2 le_rfl (Z5Z_oneZero' κ hκ hκ1 Ξ hΞ f hf 0 2 le_rfl)

theorem Z5Z_expand_S4 (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hk : 2 ≤ k) (hone : ∃ C : ℝ, OneZeroBound κ Ξ f A k C) :
    ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      Integrable (fun s => W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))) ∧
      Summable (pairInt χ T κ Ξ f W Δ s₀) ∧
      (((∫ s, W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))) : ℝ) : ℂ)
        = ∑' p, pairInt χ T κ Ξ f W Δ s₀ p :=
  Z5Z_expand_S4' κ hκ hκ1 Ξ hΞ f hf A k hk hone

end ZetaShell.PropZ
