/-
L7_5 (28 Sep 2026), round 7: split of `Z5Z_pair` (Step 5) with the derivation COMPILED (`Z5Z_pair'`).
  * `ZP_deriv_bound` (PROVED in round 8 via `ZP_deriv_bound'`, ZZ3d_Deriv.lean): with `g(s) = W(s−s₀) Ψ_{ρρ′}(s)`: `g ∈ C_c^∞` and
      `∫|g| + ∫|g^{(A)}| ≤ C₂ ‖W‖_{C^A} T N₀^{β+β′−2} ϖ_ρ(μ) ϖ_{ρ′}(μ)`   (`μ = ΔN₀`),
    from Step 4 (`hone`) by Cauchy–Schwarz, `∂_s I_ρ[f_a](ξ; Δe^s) = I_ρ[f_{a+1}]`, Leibniz in `s`,
    `e^{s(β+β′−2)} ≤ e² N₀^{β+β′−2}` and `ϖ(μ_s) ≤ e^k ϖ(μ)` on `|s − s₀| ≤ 1`;
  * the `A`-fold integration by parts against `e^{is(γ−γ′)}` (`norm_integral_cexp_I_le`, ZP_IBP.lean, PROVED).
-/
import ZetaShell.PropZ.ZZ2_OneZero
import ZetaShell.PropZ.ZP_IBP
import ZetaShell.PropZ.ZZ3d_Deriv

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem ZP_deriv_bound (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k)
    (hone : ∃ C : ℝ, OneZeroBound κ Ξ f A k C) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (ρ ρ' : ℂ), 0 < ρ.re → ρ.re < 1 → 0 < ρ'.re → ρ'.re < 1 →
      ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => ((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s) ∧
      HasCompactSupport (fun s : ℝ => ((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s) ∧
      (∫ s : ℝ, ‖((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s‖)
        + (∫ s : ℝ, ‖iteratedDeriv A (fun s : ℝ => ((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s) s‖)
        ≤ C₂ * normCA W A * T * (Real.exp s₀ ^ (ρ.re + ρ'.re - 2) * varpi T (Δ * Real.exp s₀) k ρ
            * varpi T (Δ * Real.exp s₀) k ρ') :=
  ZP_deriv_bound' κ hκ hκ1 Ξ hΞ f hf A k hA hk hone

theorem Z5Z_pair' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k)
    (hone : ∃ C : ℝ, OneZeroBound κ Ξ f A k C) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (ρ ρ' : ℂ), 0 < ρ.re → ρ.re < 1 → 0 < ρ'.re → ρ'.re < 1 →
      ‖∫ s, ((W (s - s₀) : ℝ) : ℂ) * Complex.exp (I * s * (ρ.im - ρ'.im)) * PsiP T κ Ξ f ρ ρ' Δ s‖
        ≤ C₁ * normCA W A * T * (Real.exp s₀ ^ (ρ.re + ρ'.re - 2) * varpi T (Δ * Real.exp s₀) k ρ
            * varpi T (Δ * Real.exp s₀) k ρ' / (1 + |ρ.im - ρ'.im|) ^ A) := by
  obtain ⟨C₂, hC₂, hD⟩ := ZP_deriv_bound κ hκ hκ1 Ξ hΞ f hf A k hA hk hone
  refine ⟨2 ^ A * C₂, by positivity, fun W hW s₀ T Δ hs₀ hT hΔ hΔ1 ρ ρ' h1 h2 h3 h4 => ?_⟩
  obtain ⟨hgs, hgc, hgb⟩ := hD W hW s₀ T Δ hs₀ hT hΔ hΔ1 ρ ρ' h1 h2 h3 h4
  have e : (fun s : ℝ => ((W (s - s₀) : ℝ) : ℂ) * Complex.exp (I * s * (ρ.im - ρ'.im)) * PsiP T κ Ξ f ρ ρ' Δ s)
      = fun s : ℝ => (((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s)
          * Complex.exp (((ρ.im - ρ'.im : ℝ) : ℂ) * I * s) := by
    funext s
    have : I * (s : ℂ) * ((ρ.im : ℂ) - (ρ'.im : ℂ)) = ((ρ.im - ρ'.im : ℝ) : ℂ) * I * s := by push_cast; ring
    rw [this]; ring
  rw [e]
  have hib := norm_integral_cexp_I_le _ hgs hgc (ρ.im - ρ'.im) A
  have hq : 0 < (1 + |ρ.im - ρ'.im|) ^ A := by positivity
  rw [← le_div_iff₀ hq] at hib
  refine hib.trans ?_
  rw [div_le_iff₀ hq]
  have hdiv : 2 ^ A * C₂ * normCA W A * T * (Real.exp s₀ ^ (ρ.re + ρ'.re - 2) * varpi T (Δ * Real.exp s₀) k ρ
        * varpi T (Δ * Real.exp s₀) k ρ' / (1 + |ρ.im - ρ'.im|) ^ A) * (1 + |ρ.im - ρ'.im|) ^ A
      = 2 ^ A * (C₂ * normCA W A * T * (Real.exp s₀ ^ (ρ.re + ρ'.re - 2) * varpi T (Δ * Real.exp s₀) k ρ
        * varpi T (Δ * Real.exp s₀) k ρ')) := by
    field_simp
  rw [hdiv]
  exact mul_le_mul_of_nonneg_left hgb (by positivity)

end ZetaShell.PropZ
