/-
L7_5 (28 Sep 2026): the decomposition of Proposition Z (prop:shell-Z) into its proof steps, as statements.
Proposition Z does NOT follow from Z5a and Z5b alone: its proof (Steps 1–5 of the draft) uses Z5a (Step 1) and Z5b
(Step 2, the identity `G_s = −Σ_ρ Ṽ_{x,s}(ρ) + R_{x,s}`), and in addition two analytic estimates that are not
consequences of Z5a or Z5b:
  * `Z5R` (Step 2, remainder): `Δ² ∫ |R_{x,s}|² dx ≪ E(r,Δ)` for `|s − s₀| ≤ 1`, from the Mellin decay of `V_{x,s}`
    on `Re w = −1/2` and Z5b's bound on `L′/L`;
  * `Z5Zero` (Steps 3–5, zero part): scaling, Plancherel for `I_ρ`, the one-zero bound `w_ρ ≪ Tϖ_ρ²`, and `A`
    integrations by parts in `s`; this uses no explicit formula at all.
Proposition Z = Z5a + Z5b + Z5R + Z5Zero + the elementary `|a+b|² ≤ 2|a|² + 2|b|²` and `∫W ≤ 2‖W‖_∞`.
-/
import ZetaShell.PropZ.ZDefs
import ZetaShell.Skeleton.Z5_PropZ

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- `V_{x,s}(y) = A_s(y) f(Δ(y−x))` (proof of prop:shell-Z, Step 1). -/
noncomputable def Vxs (T κ : ℝ) (Ξ f : ℝ → ℝ) (Δ s x : ℝ) (y : ℝ) : ℂ :=
  As T κ Ξ s y * ((f (Δ * (y - x)) : ℝ) : ℂ)

/-- the zero part `Σ_ρ m_ρ Ṽ_{x,s}(ρ)`. -/
noncomputable def zeroPart {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T κ : ℝ) (Ξ f : ℝ → ℝ)
    (Δ s x : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin (Vxs T κ Ξ f Δ s x) ρ.1

open scoped Classical in
/-- the remainder `R_{x,s} = −δ_{r>1,χ even} Ṽ(0) − (1/2π) ∫ (L′/L)(−1/2+it) Ṽ(−1/2+it) dt`. -/
noncomputable def remPart {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T κ : ℝ) (Ξ f : ℝ → ℝ)
    (Δ s x : ℝ) : ℂ :=
  -(if r ≠ 1 ∧ χ.Even then mellin (Vxs T κ Ξ f Δ s x) 0 else 0)
    - (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, logDeriv χ.LFunction (-1 / 2 + t * I)
        * mellin (Vxs T κ Ξ f Δ s x) (-1 / 2 + t * I)

/-- **Z5R** (Step 2 of prop:shell-Z): the remainder is `O(E(r,Δ))`, uniformly in `|s − s₀| ≤ 1`, `T`, `Δ`, `r ≤ N₀`
and the character. -/
theorem Z5R (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      ∀ s : ℝ, |s - s₀| ≤ 1 →
      Δ ^ 2 * ∫ x, ‖remPart χ T κ Ξ f Δ s x‖ ^ 2 ≤ C * Eerr T (Real.exp s₀) r Δ := by
  sorry

/-- **Z5Zero** (Steps 3–5 of prop:shell-Z): the zero part, `s`-averaged. -/
theorem Z5Zero (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k) :
    ∃ C₀ : ℝ, ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      Summable (pairTerm χ T (Δ * Real.exp s₀) s₀ A k) ∧
      ∫ s, W (s - s₀) * (Δ ^ 2 * ∫ x, ‖zeroPart χ T κ Ξ f Δ s x‖ ^ 2)
        ≤ C₀ * normCA W A * T * ∑' p, pairTerm χ T (Δ * Real.exp s₀) s₀ A k p := by
  sorry

end ZetaShell.PropZ
