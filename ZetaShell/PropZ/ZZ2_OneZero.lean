/-
Sub-node Z5Z-2 (L7_5, round 2), Step 4 of prop:shell-Z (one zero): `‖I_ρ(·;μ)‖₂² = μ^{−2} w_ρ(μ;f_j)` and
`w_ρ(μ; f_j) ≪ T ϖ_ρ(μ)²` for `j ≤ A`, uniformly in `μ > 0`, `T ≥ 2` and `ρ` in the open strip.
(i) `‖H_ρ‖₂² ≤ 2πe^{2κ}T`; (ii) for `D = (|γ|−2T)_+ ≥ 1`, `m = k+2` integrations by parts in `t`.
Status (round 4): PROVED from the leaves `ZO_trivial`, `ZO_ibp` via `Z5Z_oneZero'` (ZZ2a_OneZeroSplit.lean).
Statement unchanged; `OneZeroBound` now lives in ZZ2a_OneZeroSplit.lean (verbatim).
-/
import ZetaShell.PropZ.ZZ2a_OneZeroSplit

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem Z5Z_oneZero (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, OneZeroBound κ Ξ f A k C :=
  Z5Z_oneZero' κ hκ hκ1 Ξ hΞ f hf A k hk

end ZetaShell.PropZ
