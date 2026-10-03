/-
L7_5 (28 Sep 2026), Track F, Proposition Z chain: shared definitions (sec_shell.tex, ssec:shell-propZ).
Mathlib objects only (plus `ChallengeShell` for `IsNtZero`, `zmult`, which are definitionally Zeta23's
`IsNontrivialZeroL`, `zeroMultL`).
-/
import ZetaShell.Challenge

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- `e(x) = exp(2πix)`. -/
noncomputable def eA (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `D_T(v) = ∫_T^{2T} e^{iτv} dτ` (macros.tex, `\DT`). -/
noncomputable def DT (T v : ℝ) : ℂ := ∫ τ in T..(2 * T), Complex.exp (Complex.I * τ * v)

/-- `A_s(y) = y^{-1/2} D_T(s − log y) Ξ((log y − s)/κ)` (eq:shell-As). -/
noncomputable def As (T κ : ℝ) (Ξ : ℝ → ℝ) (s y : ℝ) : ℂ :=
  ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * DT T (s - Real.log y) * ((Ξ ((Real.log y - s) / κ) : ℝ) : ℂ)

/-- `S_χ(β; s) = Σ_n Λ(n)χ(n)A_s(n)e(nβ) − δ_{r=1} ∫_0^∞ A_s(y)e(yβ) dy` (ssec:shell-propZ). -/
noncomputable def Schi {r : ℕ} (χ : DirichletCharacter ℂ r) (T κ : ℝ) (Ξ : ℝ → ℝ) (s β : ℝ) : ℂ :=
  (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * As T κ Ξ s n * eA (n * β))
    - (if r = 1 then ∫ y in Set.Ioi (0 : ℝ), As T κ Ξ s y * eA (y * β) else 0)

/-- `f̂(η) = ∫ f(z) e(−zη) dz`. -/
noncomputable def fhat (f : ℝ → ℝ) (η : ℝ) : ℂ := ∫ z, (f z : ℂ) * eA (-(z * η))

/-- `Φ = f̂²/c` (the draft takes `c = c_f = min_{[-1,1]} f̂²`; any `0 < c ≤ c_f` works below). -/
noncomputable def Phi (f : ℝ → ℝ) (c η : ℝ) : ℝ := ‖fhat f η‖ ^ 2 / c

/-- the test function `f` of ssec:shell-propZ ("Test functions"). -/
structure TestFn (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  supp : tsupport f ⊆ Set.Ioo (-(1 / 8 : ℝ)) (1 / 8)
  even : ∀ z, f (-z) = f z
  nonneg : ∀ z, 0 ≤ f z
  ne_zero : ∃ z, f z ≠ 0

/-- the near cutoff `Ξ ∈ C_c^∞((-1,1))`, `0 ≤ Ξ ≤ 1`. -/
structure NearCutoff (Ξ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) Ξ
  supp : tsupport Ξ ⊆ Set.Ioo (-1 : ℝ) 1
  nonneg : ∀ z, 0 ≤ Ξ z
  le_one : ∀ z, Ξ z ≤ 1

/-- the averaging weight `W ∈ C_c^∞((-1,1))`, `W ≥ 0`. -/
structure AvgWeight (W : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) W
  supp : tsupport W ⊆ Set.Ioo (-1 : ℝ) 1
  nonneg : ∀ z, 0 ≤ W z

/-- `‖W‖_{C^A} = Σ_{j ≤ A} sup |W^{(j)}|`. -/
noncomputable def normCA (W : ℝ → ℝ) (A : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (A + 1), ⨆ x, |iteratedDeriv j W x|

/-- `ϖ_ρ = (1 + (|γ| − 2T)_+/(μ+1))^{-k}`. -/
noncomputable def varpi (T μ : ℝ) (k : ℕ) (ρ : ℂ) : ℝ :=
  (1 + max (|ρ.im| - 2 * T) 0 / (μ + 1)) ^ (-(k : ℝ))

/-- `E(r, Δ) = T²(Δ² + Δ/N₀) + T²(T+μ+1)²(Δ²/N₀ + Δ/N₀²) log²(r N₀ T)`, `μ = Δ N₀`. -/
noncomputable def Eerr (T N0 r Δ : ℝ) : ℝ :=
  T ^ 2 * (Δ ^ 2 + Δ / N0)
    + T ^ 2 * (T + Δ * N0 + 1) ^ 2 * (Δ ^ 2 / N0 + Δ / N0 ^ 2) * Real.log (r * N0 * T) ^ 2

/-- Mellin transform `Ṽ(w) = ∫_0^∞ V(y) y^{w−1} dy` (Mathlib's `mellin`). -/
noncomputable def Vt (V : ℝ → ℝ) (w : ℂ) : ℂ := mellin (fun y => (V y : ℂ)) w

end ZetaShell.PropZ
