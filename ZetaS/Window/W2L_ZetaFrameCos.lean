/-
Node W2L-cos (track W; replaces v1's W2 for the Σ/D route) — ζ at bandwidth λ ∈ (0,1) with ψ = cos(αs), 0 < α ≤ 8/5
(the draft's α = 8/5): a FrameFamilyL against Ncount with R = R_λ(cos α·) and kernel k_ψ, window seams to the Mathlib
counts. Proof: Z9 at Z = ζ (Statement.zetaZeros, `paperInputs_zeta`) with L0_2's `admWindow_phiV_cos` (every 8w ≤ L),
a = 0.8967, b = 0.8124 (`aCos_close`, `bCos_close`); the seam Nsc = N0 + Ns − N0s.
-/
import ZetaS.InterfacesV2
import ZetaS.ZeroSide.Z9_FrameOfZeroConfig
import ZetaS.ZeroSide.ZetaSeams

open Filter Asymptotics

namespace ZetaS

theorem zeta_frameFamily_cos {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1) :
    ∃ Fm : FrameFamilyL lam (fun T => (Ncount T (2 * T) : ℝ)) (Rlam lam (fun s => Real.cos (α * s)))
        (kPsi (fun s => Real.cos (α * s))),
      ∃ r : ℝ → ℝ, r =o[atTop] (fun T => (Ncount T (2 * T) : ℝ)) ∧ ∀ᶠ T in atTop,
        ((Fm.F T).NsW : ℝ) ≤ Nsimple T (2 * T) + r T ∧
        ((Fm.F T).NdW : ℝ) ≤ Ndist T (2 * T) + r T ∧
        ((Fm.F T).NscW : ℝ) ≤ Nsc T (2 * T) + r T := by
  have hP : (Zeta23.paramsOf Zeta23.stdProfile lam).Valid :=
    Zeta23.paramsOf_valid Zeta23.taperProfile_stdProfile hl0 hl1.le
  have hcp := WindowInstances.coreProfile_cosW hα0 hα1
  have h := frameFamily_of_zeroConfig Zeta23.zetaZeroConfig Zeta23.paperInputs_zeta hP hl1
    (CosWindow.cosW_even α) hcp.cont (fun s hs => ⟨hcp.nonneg s hs, hcp.le_one s hs⟩)
    (fun T hT => CosWindow.admWindow_phiV_cos hP hα0 hα1 hT)
    (by rw [CosWindow.integral_cosW hα0.ne']; exact ZSeam.half_lt_aC hα0 hα1)
    (by rw [CosWindow.integral_cosW_sq hα0.ne']; exact WindowInstances.half_lt_bC hα0 hα1)
  obtain ⟨Fm, r, hr, hev⟩ := h
  refine ⟨Fm, r, hr, ?_⟩
  filter_upwards [hev] with T hT
  obtain ⟨h1, h2, h3⟩ := hT
  refine ⟨h1, h2, ?_⟩
  rw [ZSeam.Nsc_eq]
  exact h3

end ZetaS
