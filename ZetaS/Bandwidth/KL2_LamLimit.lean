/-
Node KL2 (track T, bandwidth) — the limit λ → 1⁻ of the headline constants (the tree's pattern: ThmD/Final.lean
`eps_form_HD`, XiPrime `continuousOn_cWin`): if at every bandwidth λ ∈ (λ₀, 1) the ε-form holds with constant f(λ),
f(λ) → f₁ as λ → 1⁻ and c ≤ f₁, then the ε-form holds with c.
-/
import ZetaS.InterfacesV2

open Filter Topology

namespace ZetaS

theorem eps_form_of_lam_limit {N X f : ℝ → ℝ} {f₁ c lam₀ : ℝ} (hlam₀ : lam₀ < 1)
    (hN : ∀ᶠ T in atTop, 0 ≤ N T)
    (hf : ∀ lam ∈ Set.Ioo lam₀ 1, ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (f lam - ε) * N T ≤ X T)
    (hlim : Tendsto f (𝓝[<] 1) (𝓝 f₁)) (hc : c ≤ f₁) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * N T ≤ X T := by
  intro ε hε
  -- a bandwidth λ ∈ (λ₀, 1) with f λ > f₁ − ε/2
  have h1 : ∀ᶠ lam in 𝓝[<] (1 : ℝ), f₁ - ε / 2 < f lam :=
    hlim.eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ lam in 𝓝[<] (1 : ℝ), lam ∈ Set.Ioo lam₀ 1 := Ioo_mem_nhdsLT hlam₀
  obtain ⟨lam, hlf, hlam⟩ := (h1.and h2).exists
  obtain ⟨T₀, hT₀⟩ := hf lam hlam (ε / 2) (by linarith)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hN
  refine ⟨max T₀ T₁, fun T hT => ?_⟩
  have hN0 := hT₁ T (le_trans (le_max_right _ _) hT)
  have hX := hT₀ T (le_trans (le_max_left _ _) hT)
  have : (c - ε) * N T ≤ (f lam - ε / 2) * N T := mul_le_mul_of_nonneg_right (by linarith) hN0
  linarith

end ZetaS
