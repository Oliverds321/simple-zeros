/-
Sub-node ZP (L7_5, round 2): prop:shell-Z Steps 1–2 pointwise in `s`, FROM Z5a's Plancherel identity (`h5a`) and
Z5b-W (`h5b`), which are passed as hypotheses so that the dependency is explicit:
  ∫|S_χ(β;s)|²Φ(β/Δ)dβ = (Δ²/c)∫|G_s(x)|²dx  (Z5a with ν = Σ Λχ(n)A_s(n)δ_n − δ_{r=1}A_s dy),
  G_s(x) = Σ Λχ(n)V_{x,s}(n) − δ_{r=1}Ṽ_{x,s}(1) = −Σ_ρ m_ρṼ_{x,s}(ρ) + R^W_{x,s}  (Z5b-W; supp V_{x,s} ⊂ (1,∞)),
  |−a+b|² ≤ 2|a|² + 2|b|².
What the proof still has to supply (bridging, all elementary): `Schi` as Z5a's finite sum plus density; continuity and
compact support of `A_s`; smoothness and support of `V_{x,s}`; square-integrability in `x` of both parts.
Status (14:30): PROVED from `h5a`, `h5b` and the bridging sub-nodes `ZB_Schi_form`, `ZB_Vxs_props`,
`ZB_sq_integrable` (ZP_Bridge.lean, open).
-/
import ZetaShell.PropZ.ZDefsW
import ZetaShell.PropZ.ZP_Bridge

open MeasureTheory Complex

namespace ZetaShell.PropZ

open scoped Classical in
theorem ZP_pointwise (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c) (hc : ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2)
    (h5a : ∀ (F : Finset ℝ) (a g : ℝ → ℂ), Continuous g → HasCompactSupport g → ∀ Δ : ℝ, 0 < Δ →
      (∫ β, ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2 * Phi f c (β / Δ))
        = Δ ^ 2 / c * ∫ x, ‖∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)‖ ^ 2)
    (h5b : ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∀ V : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) V → HasCompactSupport V → tsupport V ⊆ Set.Ioi 1 →
      Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℂ) * mellin V ρ.1) ∧
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * V n
        = (if r = 1 then mellin V 1 + mellin V 0 else 0)
          - ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin V ρ.1
          + (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, mellin V (1 / 2 + t * I)
              * (((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
                  + Real.log (r / Real.pi) : ℝ) : ℂ)) :
    ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ))
        ≤ 2 / c * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))
          + 2 / c * (Δ ^ 2 * (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2)) := by
  intro s₀ T Δ s hs₀ hT hΔ hΔ1 hs r _ χ hχ
  obtain ⟨F, a, g, hg, hgs, hS, hG⟩ := ZB_Schi_form κ hκ hκ1 Ξ hΞ f hf s₀ T Δ s hs₀ hT hΔ hΔ1 hs r χ hχ
  obtain ⟨hZi, hRi⟩ := ZB_sq_integrable κ hκ hκ1 Ξ hΞ f hf s₀ T Δ s hs₀ hT hΔ hΔ1 hs r χ hχ
  have hI : (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ))
      = Δ ^ 2 / c * ∫ x, ‖∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)‖ ^ 2 := by
    simp_rw [hS]; exact h5a F a g hg hgs Δ hΔ
  have hGx : ∀ x, ∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)
      = remPartW χ T κ Ξ f Δ s x - zeroPartW χ T κ Ξ f Δ s x := by
    intro x
    obtain ⟨hV1, hV2, hV3⟩ := ZB_Vxs_props κ hκ hκ1 Ξ hΞ f hf s₀ T Δ s x hs₀ hT hΔ hΔ1 hs
    obtain ⟨_, hEF⟩ := h5b r χ hχ (VxsW T κ Ξ f Δ s x) hV1 hV2 hV3
    rw [hG x, hEF]
    simp only [remPartW, zeroPartW]
    split_ifs <;> ring
  have hpt : ∀ x, ‖∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)‖ ^ 2
      ≤ 2 * ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2 + 2 * ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2 := by
    intro x
    rw [hGx x]
    have h1 := norm_sub_le (remPartW χ T κ Ξ f Δ s x) (zeroPartW χ T κ Ξ f Δ s x)
    have h2 := norm_nonneg (remPartW χ T κ Ξ f Δ s x - zeroPartW χ T κ Ξ f Δ s x)
    nlinarith [sq_nonneg (‖remPartW χ T κ Ξ f Δ s x‖ - ‖zeroPartW χ T κ Ξ f Δ s x‖),
      norm_nonneg (remPartW χ T κ Ξ f Δ s x), norm_nonneg (zeroPartW χ T κ Ξ f Δ s x)]
  have hint : (∫ x, ‖∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)‖ ^ 2)
      ≤ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2) + 2 * (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hZi.const_mul 2) (hRi.const_mul 2)]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
      ((hZi.const_mul 2).add (hRi.const_mul 2)) (Filter.Eventually.of_forall hpt)
  rw [hI]
  have hc' : 0 ≤ Δ ^ 2 / c := by positivity
  calc Δ ^ 2 / c * (∫ x, ‖∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)‖ ^ 2)
      ≤ Δ ^ 2 / c * (2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2) + 2 * (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hint hc'
    _ = 2 / c * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))
          + 2 / c * (Δ ^ 2 * (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2)) := by ring

end ZetaShell.PropZ
