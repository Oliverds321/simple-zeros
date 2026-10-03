/-
L7_5 (28 Sep 2026), round 4: the two analytic inputs SHARED by `Z5R_W` and `ZB_parts_bounded` (report R2.1).
  * `ZR_phi_bounds` ((a2)–(a4)): with `φ_x(u) = V_{x,s}(e^u)`, `N = e^s`, `m = min(1/Δ, N)`, `X = T + ΔN + 1`,
      `∫ ‖φ_x(u)‖ e^{au} du ≤ C T N^{a−1/2} m/N`,  `∫ ‖φ_x″(u)‖ e^{au} du ≤ C X² T N^{a−1/2} m/N`,  `0 ≤ a ≤ 1`,
    uniformly in `x`.  (`|D_T| ≤ T`, `|D_T′| ≤ 2T²` from `DT_Facts`; `y∂_y` costs `≤ C X`; the `u`-support of
    `f(Δ(e^u−x))` inside `[s−κ, s+κ]` has length `≤ C m/N`.)
  * `ZR_digamma` ((a1)): `|Re ψ(1/4 + e/2 + it/2) + log(r/π)| ≤ C₁ log(r(|t|+2))`, `e ∈ {0,1}`, `r ≥ 1`.
Status: `ZR_digamma` PROVED in round 5 (from `ZR_digamma'`, ZR_Digamma.lean, tree's GammaFactsChi toolkit);
`ZR_phi_bounds` PROVED in round 5 from the pointwise leaf `ZR_phi_pw` (ZR_Phi.lean, OPEN) via `ZR_phi_bounds'`.
-/
import ZetaShell.PropZ.ZDefsW
import ZetaShell.PropZ.ZR_Digamma
import ZetaShell.PropZ.ZR_Phi

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem ZR_phi_bounds (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (x a : ℝ), 0 ≤ a → a ≤ 1 →
      (∫ u, ‖VxsW T κ Ξ f Δ s x (Real.exp u)‖ * Real.exp (a * u))
          ≤ C * T * Real.exp s ^ (a - 1 / 2) * min (1 / Δ) (Real.exp s) / Real.exp s ∧
      (∫ u, ‖deriv (deriv (fun u => VxsW T κ Ξ f Δ s x (Real.exp u))) u‖ * Real.exp (a * u))
          ≤ C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp s ^ (a - 1 / 2) * min (1 / Δ) (Real.exp s)
            / Real.exp s :=
  ZR_phi_bounds' κ hκ hκ1 Ξ hΞ f hf

theorem ZR_digamma : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (e : ℕ), e ≤ 1 → ∀ t : ℝ,
    |(Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi)|
      ≤ C₁ * Real.log (r * (|t| + 2)) :=
  ZR_digamma'

end ZetaShell.PropZ
