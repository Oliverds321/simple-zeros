/-
Node Z5R-W (L7_5, round 2): Step 2 of prop:shell-Z for the Weil-form remainder (report §R2.1(a), (a1)–(a10)):
  Δ² ∫ |R^W_{x,s}|² dx ≤ C_R E′(r,Δ)  for |s − s₀| ≤ 1,
uniformly in T ≥ 2, 0 < Δ ≤ 1, s₀ ≥ 3, primitive χ mod r ≤ N₀ = e^{s₀}; C_R = C_R(κ,Ξ,f).
Status (round 4): PROVED from the shared leaves `ZR_phi_bounds`, `ZR_digamma` via `Z5R_W'` (ZR_Remainder.lean).
Statement unchanged. The draft-form `Z5R` (Z5_Steps.lean) is kept untouched.
-/
import ZetaShell.PropZ.ZR_Remainder

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem Z5R_W (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      ∀ s : ℝ, |s - s₀| ≤ 1 →
      Δ ^ 2 * (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2) ≤ C * EerrW T (Real.exp s₀) r Δ :=
  Z5R_W' κ hκ hκ1 Ξ hΞ f hf

end ZetaShell.PropZ
