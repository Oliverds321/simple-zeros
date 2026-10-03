/-
L7_5 (28 Sep 2026), round 2: objects of the Weil-form route (Z5b-W is the provisional form of record).
`EerrW` is the error term E′(r,Δ) of report L7_5_Zchain.md §R2.1(a):
  E′(r,Δ) = T²(Δ² + Δ/N₀) + T²(T + ΔN₀ + 1)² log²(rN₀T)/N₀.
`remPartW` is the Weil remainder R^W_{x,s} = δ_{r=1}Ṽ(0) + (1/2π)∫ Ṽ(1/2+it) w_r(t) dt of §R2.1(a).
-/
import ZetaShell.PropZ.ZDefs

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- `E′(r,Δ)`. -/
noncomputable def EerrW (T N0 r Δ : ℝ) : ℝ :=
  T ^ 2 * (Δ ^ 2 + Δ / N0) + T ^ 2 * (T + Δ * N0 + 1) ^ 2 * Real.log (r * N0 * T) ^ 2 / N0

/-- `V_{x,s}(y) = A_s(y) f(Δ(y−x))` (proof of prop:shell-Z, Step 1). -/
noncomputable def VxsW (T κ : ℝ) (Ξ f : ℝ → ℝ) (Δ s x : ℝ) (y : ℝ) : ℂ :=
  As T κ Ξ s y * ((f (Δ * (y - x)) : ℝ) : ℂ)

open scoped Classical in
/-- the Weil remainder `R^W_{x,s}` (parenthesised integral). -/
noncomputable def remPartW {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T κ : ℝ) (Ξ f : ℝ → ℝ)
    (Δ s x : ℝ) : ℂ :=
  (if r = 1 then mellin (VxsW T κ Ξ f Δ s x) 0 else 0)
    + (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)
        * (((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
            + Real.log (r / Real.pi) : ℝ) : ℂ))

/-- the zero part `Σ_ρ m_ρ Ṽ_{x,s}(ρ)`. -/
noncomputable def zeroPartW {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T κ : ℝ) (Ξ f : ℝ → ℝ)
    (Δ s x : ℝ) : ℂ :=
  ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin (VxsW T κ Ξ f Δ s x) ρ.1

end ZetaShell.PropZ
