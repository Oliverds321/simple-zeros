/-
Node Z3 (track W/K) — `Etr_psd`: the off-grid Gram matrix (Σ_{k∉[0,d)} u_{γ_i}(k)u_{γ_j}(k))_{ij} of any finite list of
real ordinates is PSD (a Gram matrix in ℓ²; summability from the tree's `vHat_decay`).
-/
import ZetaS.InterfacesV2
import ZetaS.ZeroSide.Helpers

namespace ZetaS

theorem offGrid_psd {v : ℝ → ℝ} {L w c : ℝ} (hW : Zeta23.AdmWindow v L w c) (T : ℝ) (d : ℕ)
    {n : ℕ} (γ : Fin n → ℝ) :
    (Matrix.of fun i j => ∑' k : offGrid d, uR v L T (γ i) k.1 * uR v L T (γ j) k.1).PosSemidef := by
  refine ZeroSide.posSemidef_of_hasSum (fun i (k : offGrid d) => uR v L T (γ i) k.1) _ fun i j => ?_
  have h := ZeroSide.hasSum_uR_mul hW T (γ i) (γ j)
  have hsub : Summable (fun k : offGrid d => uR v L T (γ i) k.1 * uR v L T (γ j) k.1) :=
    h.summable.subtype (fun k : ℤ => k < 0 ∨ (d : ℤ) ≤ k)
  simpa only [Matrix.of_apply] using hsub.hasSum

end ZetaS
