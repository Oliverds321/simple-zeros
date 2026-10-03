/-
Node W2L-poly (track W; replaces v1's W2 for the SC route) — ζ at bandwidth λ ∈ (0,1) with the polynomial window.
The tree realises ψ♮ = (4/5)v (L0_2 `PolyWindow.psiN`, admissible for every 8w ≤ L); k_ψ and R_λ are homogeneous of
degree 0, so the family is stated for the draft's `psiPoly8A = (50000/50037)v` (node Hom). Proof: Z9 + `admWindow_phiP8`.
-/
import ZetaS.InterfacesV2
import ZetaS.Window.W2L_ZetaFramePoly_fix

open Filter Asymptotics

namespace ZetaS

theorem zeta_frameFamily_poly {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    ∃ Fm : FrameFamilyL lam (fun T => (Ncount T (2 * T) : ℝ)) (Rlam lam psiPoly8A) (kPsi psiPoly8A),
      ∃ r : ℝ → ℝ, r =o[atTop] (fun T => (Ncount T (2 * T) : ℝ)) ∧ ∀ᶠ T in atTop,
        ((Fm.F T).NsW : ℝ) ≤ Nsimple T (2 * T) + r T ∧
        ((Fm.F T).NdW : ℝ) ≤ Ndist T (2 * T) + r T ∧
        ((Fm.F T).NscW : ℝ) ≤ Nsc T (2 * T) + r T := by
  obtain ⟨Fm, r, hr, hev⟩ := zeta_frameFamily_poly_fix hl0 hl1
  exact ⟨Fm, r, hr, hev.mono fun T h => ⟨h.1, h.2.1, h.2.2.1⟩⟩

end ZetaS
