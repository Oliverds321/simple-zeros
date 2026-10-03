/-
Sub-node Z5Z-3 (L7_5, round 2), Step 5 of prop:shell-Z (one pair, s-averaged), FROM Step 4 (hypothesis `hone`):
`∂_s^jΨ_{ρρ′}` is a bounded combination of `μ_s² e^{s(β+β′−2)} ∫ I_ρ[f_a] conj(I_{ρ′}[f_b])`, `a+b ≤ j`; Cauchy–Schwarz and
Step 4 give `|∂_s^jΨ| ≪ T e^{s(β+β′−2)} ϖ_ρ(μ_s)ϖ_{ρ′}(μ_s)`; for `|s−s₀| ≤ 1`, `e^{s(β+β′−2)} ≤ e²N₀^{β+β′−2}` and
`ϖ(μ_s) ≤ e^kϖ(μ)`; `A` integrations by parts in `s` give `(1+|γ−γ′|)^{−A}` times `‖W‖_{C^A}`.
Status (round 7): proved from the leaf `ZP_deriv_bound` and the proved IBP lemma via `Z5Z_pair'`
(ZZ3a_PairSplit.lean); statement unchanged.
-/
import ZetaShell.PropZ.ZZ2_OneZero
import ZetaShell.PropZ.ZZ3a_PairSplit

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem Z5Z_pair (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k)
    (hone : ∃ C : ℝ, OneZeroBound κ Ξ f A k C) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (ρ ρ' : ℂ), 0 < ρ.re → ρ.re < 1 → 0 < ρ'.re → ρ'.re < 1 →
      ‖∫ s, ((W (s - s₀) : ℝ) : ℂ) * Complex.exp (I * s * (ρ.im - ρ'.im)) * PsiP T κ Ξ f ρ ρ' Δ s‖
        ≤ C₁ * normCA W A * T * (Real.exp s₀ ^ (ρ.re + ρ'.re - 2) * varpi T (Δ * Real.exp s₀) k ρ
            * varpi T (Δ * Real.exp s₀) k ρ' / (1 + |ρ.im - ρ'.im|) ^ A) :=
  Z5Z_pair' κ hκ hκ1 Ξ hΞ f hf A k hA hk hone

end ZetaShell.PropZ
