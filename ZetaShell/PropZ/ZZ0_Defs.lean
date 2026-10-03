/-
L7_5 (28 Sep 2026), round 2: objects of Steps 3–5 of prop:shell-Z (sec_shell.tex):
  H_ρ(t) = D_T(−log t) Ξ(log t/κ) t^{ρ−3/2},   f_0 = f, f_{j+1}(z) = z f_j′(z),
  I_ρ(ξ; μ, f_j) = ∫_0^∞ H_ρ(t) f_j(μ(t−ξ)) dt,
  Ψ_{ρρ′}(s) = μ_s² e^{s(β+β′−2)} ∫ I_ρ(ξ;μ_s) conj(I_{ρ′}(ξ;μ_s)) dξ,   μ_s = Δ e^s.
-/
import ZetaShell.PropZ.ZDefsW

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- `H_ρ(t) = D_T(−log t) Ξ(log t/κ) t^{ρ−3/2}` (Step 3). -/
noncomputable def Hrho (T κ : ℝ) (Ξ : ℝ → ℝ) (ρ : ℂ) (t : ℝ) : ℂ :=
  DT T (-Real.log t) * ((Ξ (Real.log t / κ) : ℝ) : ℂ) * (t : ℂ) ^ (ρ - 3 / 2)

/-- `f_0 = f`, `f_{j+1}(z) = z f_j′(z)` (ssec:shell-propZ, "Test functions"). -/
noncomputable def fj (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | j + 1 => fun z => z * deriv (fj f j) z

/-- `I_ρ(ξ; μ, f_j) = ∫_0^∞ H_ρ(t) f_j(μ(t−ξ)) dt` (Step 3). -/
noncomputable def Irho (T κ : ℝ) (Ξ f : ℝ → ℝ) (j : ℕ) (ρ : ℂ) (μ ξ : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), Hrho T κ Ξ ρ t * ((fj f j (μ * (t - ξ)) : ℝ) : ℂ)

/-- `Ψ_{ρρ′}(s) = μ_s² e^{s(β+β′−2)} ∫ I_ρ conj(I_{ρ′}) dξ`, `μ_s = Δe^s` (Step 3). -/
noncomputable def PsiP (T κ : ℝ) (Ξ f : ℝ → ℝ) (ρ ρ' : ℂ) (Δ s : ℝ) : ℂ :=
  (((Δ * Real.exp s) ^ 2 * Real.exp (s * (ρ.re + ρ'.re - 2)) : ℝ) : ℂ)
    * (∫ ξ, Irho T κ Ξ f 0 ρ (Δ * Real.exp s) ξ * (starRingEnd ℂ) (Irho T κ Ξ f 0 ρ' (Δ * Real.exp s) ξ))

/-- the summand of the zero-pair expansion, `s`-averaged: `m_ρ m_ρ′ ∫ W(s−s₀) e^{is(γ−γ′)} Ψ_{ρρ′}(s) ds`. -/
noncomputable def pairInt {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T κ : ℝ) (Ξ f W : ℝ → ℝ)
    (Δ s₀ : ℝ) (p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) : ℂ :=
  ((zmult χ p.1.1 * zmult χ p.2.1 : ℕ) : ℂ)
    * (∫ s, ((W (s - s₀) : ℝ) : ℂ) * Complex.exp (I * s * (p.1.1.im - p.2.1.im)) * PsiP T κ Ξ f p.1.1 p.2.1 Δ s)

end ZetaShell.PropZ
