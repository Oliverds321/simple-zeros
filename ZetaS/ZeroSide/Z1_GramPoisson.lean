/-
Node Z1 (track W/K, zero side) — `gram_eq` of GramData/ZeroFrame from the tree's Poisson lemma
`Zeta23.AdmWindow.hasSum_vHatR_mul` (ThmD/WindowCore.lean:463): for real ordinates γ, γ′ (on-line zeros),
Σ_{0≤k<d} u_γ(k)u_γ′(k) = k(x − x′) − Σ_{k∉[0,d)} u_γ(k)u_γ′(k), x = γL/2π, k = `kWin v L` (x-units), at ANY
bandwidth (L = λℓ). Divide hasSum_vHatR_mul by L∫v² and split ℤ = [0,d) ⊔ offGrid.
-/
import ZetaS.InterfacesV2
import ZetaS.ZeroSide.Helpers

namespace ZetaS

theorem gram_eq_poisson {v : ℝ → ℝ} {L w c : ℝ} (hW : Zeta23.AdmWindow v L w c) (T : ℝ) (d : ℕ)
    (γ γ' : ℝ) :
    ∑ k : Fin d, uR v L T γ (k : ℕ) * uR v L T γ' (k : ℕ)
      = kWin v L ((γ - γ') * L / (2 * Real.pi)) - ∑' k : offGrid d, uR v L T γ k.1 * uR v L T γ' k.1 := by
  have h := ZeroSide.hasSum_uR_mul hW T γ γ'
  have hs := ZeroSide.sum_fin_add_tsum_offGrid h.summable d
  rw [h.tsum_eq] at hs
  exact eq_sub_of_add_eq hs

end ZetaS
