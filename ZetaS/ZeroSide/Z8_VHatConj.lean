/-
Node Z8 (track W) — reflection: for a real even admissible window, v̂(conj z) = conj v̂(z), so the vector of 1 − ρ̄
(ordinate conj γ) is the conjugate of that of ρ and each off-line pair contributes the REAL block 2(xxᵀ − yyᵀ)
(draft l.185–186, 201). Stated for `uC`.
-/
import ZetaS.InterfacesV2
import ZetaS.ZeroSide.Helpers

namespace ZetaS

theorem uC_conj {v : ℝ → ℝ} {L w c : ℝ} (hW : Zeta23.AdmWindow v L w c) (T : ℝ) (γ : ℂ) (k : ℤ) :
    uC v L T ((starRingEnd ℂ) γ) k = (starRingEnd ℂ) (uC v L T γ k) := by
  simp only [uC]
  rw [map_div₀, Complex.conj_ofReal, ← ZeroSide.vHat_conj hW]
  congr 2
  simp [map_sub, map_add, map_mul, map_div₀, Complex.conj_ofReal, map_ofNat]

end ZetaS
