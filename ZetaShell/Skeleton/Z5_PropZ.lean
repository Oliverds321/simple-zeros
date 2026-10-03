/-
Node Z5 (L7_5, 28 Sep 2026): Proposition Z (sec_shell.tex, prop:shell-Z):
"Let s₀ ≥ 3, N₀ = e^{s₀}, T ≥ 2, 0 < Δ ≤ 1, μ := ΔN₀ and A, k ≥ 2. There is C_Z = C_Z(κ,Ξ,f,W,A,k) such that for
 every primitive χ mod r, 1 ≤ r ≤ N₀,
 ∫ W(s−s₀) ∫_ℝ |S_χ(β;s)|² Φ(β/Δ) dβ ds ≤ C_Z T Σ_{ρ,ρ′} N₀^{β+β′−2} ϖ_ρϖ_ρ′/(1+|γ−γ′|)^A + C_Z E(r,Δ).
 C_Z depends on W only through ‖W‖_{C^A}."
Formalised: `C_Z = C₀(κ,Ξ,f,c,A,k)·‖W‖_{C^A}` (the proof is linear in `W`); the zero pairs are counted with
multiplicity; the double zero sum is asserted to converge (the draft: "the sums converge absolutely").
-/
import ZetaShell.PropZ.ZDefs

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- the summand of the double zero sum of Proposition Z (pairs counted with multiplicity). -/
noncomputable def pairTerm {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T μ s₀ : ℝ) (A k : ℕ)
    (p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) : ℝ :=
  (zmult χ p.1.1 : ℝ) * zmult χ p.2.1 * Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2)
    * varpi T μ k p.1.1 * varpi T μ k p.2.1 / (1 + |p.1.1.im - p.2.1.im|) ^ A

theorem propZ (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c) (hc : ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2)
    (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k) :
    ∃ C₀ : ℝ, ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      Summable (pairTerm χ T (Δ * Real.exp s₀) s₀ A k) ∧
      ∫ s, W (s - s₀) * ∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)
        ≤ C₀ * normCA W A * (T * ∑' p, pairTerm χ T (Δ * Real.exp s₀) s₀ A k p
          + Eerr T (Real.exp s₀) r Δ) := by
  sorry

end ZetaShell.PropZ
