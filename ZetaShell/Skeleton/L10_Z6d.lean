/-
Node Z6d (L7_10): **Lemma 6d, counts: low, bulk, mid and near** (lem:shell-6d, sec_shell.tex l.719–733), in the
instantiation (D1′) (`ZeroDensityInput`: Jutila (1.8), `c₀ = 2`, `σ_LF = 4/5`; Montgomery–Bombieri Th. 20,
`c(σ) = 3/(2−σ)`, `A* = 5/2`, `α₀ = 5/3`).
Draft: "(low) `log N₀ Σ b² ≪ N₀^{1−2/α+2ε₂+o(1)} → 0`; (bulk) `log N₀ Σ_bulk b_ρ² ≤ N₀^{−η(1−σ_LF)/2}`;
(mid/near, σ ≥ σ_LF) `N_𝔛(x) := Σ_{x_ρ≤x} ϖ_ρ ≤ Ce^{κ′x}`, `κ′ = c₀(2−2/α′)+ε″`, and
`log N₀ Σ_mid b² ≪ log N₀ e^{−(2−κ′)X₀}`, `(Σ_near b)² ≪ (1+X₀)² e^{2(κ′−1)₊X₀}`."
Lean form: the rest sum (`x_ρ > X₀`: low + bulk + mid) and the near sum (`x_ρ ≤ X₀`), for every `X₀ ≥ 0`, uniformly on
Theorem S's range `SRange α′ B` (so `ε ≥ (log Q)^{−B}`: this is what keeps `𝒵 = N₀^{2−2/α+o(1)}`, see the report,
Part 1 (c)). `ε″ > 0` fixed; `C`, `c` depend on `α′, B, r₀, ε₀, ε″, k`.
Dependencies: Z1 (`ZeroDensityInput → (B), (LF)`, proved by L7_1), Z6b, Z6c, the `σ`-grid of mesh `1/s₀`, partial
summation in `x`. Difficulty: M–H.
-/
import ZetaShell.ShellS.L10_Defs

noncomputable section

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem Z6d_counts (hD : ZeroDensityInput) (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r0 ε0 : ℝ)
    (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (B : ℝ) (hB : 1 ≤ B) (ε'' : ℝ) (hε'' : 0 < ε'') (k : ℕ) (hk : 3 ≤ k) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      ∀ X₀ : ℝ, 0 ≤ X₀ →
        s₀ * restSq Qn (twin Qn r0 ε0) K ε s₀ k X₀
            ≤ C * (Real.exp s₀ ^ (-c) + s₀ * Real.exp (-((2 - kappaD1p αp ε'') * X₀))) ∧
        nearSum Qn (twin Qn r0 ε0) K ε s₀ k X₀
            ≤ C * (1 + X₀) * Real.exp (max (kappaD1p αp ε'' - 1) 0 * X₀) := by
  sorry

end ShellS
end ZetaShell
