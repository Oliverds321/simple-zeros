/-
Node W2L-poly, corrected form (agent L3_1): the skeleton statement plus the fourth seam s₁ = #{simple on-line zeros
of I′} ≤ N₀ˢ(T,2T) + o(N) that W1L needs (see Z9_FrameOfZeroConfig_fix.lean). Proof: Z9-fix at ζ with ψ♮ = (4/5)v
(L0_2 `admWindow_phiP8`), transported to psiPoly8A = (62500/50037)ψ♮ by node Hom.
-/
import ZetaS.InterfacesV2
import ZetaS.ZeroSide.Z9_FrameOfZeroConfig_fix
import ZetaS.ZeroSide.ZetaSeams
import ZetaS.Bandwidth.Hom_Homogeneity

open Filter Asymptotics

namespace ZetaS

theorem zeta_frameFamily_poly_fix {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    ∃ Fm : FrameFamilyL lam (fun T => (Ncount T (2 * T) : ℝ)) (Rlam lam psiPoly8A) (kPsi psiPoly8A),
      ∃ r : ℝ → ℝ, r =o[atTop] (fun T => (Ncount T (2 * T) : ℝ)) ∧ ∀ᶠ T in atTop,
        ((Fm.F T).NsW : ℝ) ≤ Nsimple T (2 * T) + r T ∧
        ((Fm.F T).NdW : ℝ) ≤ Ndist T (2 * T) + r T ∧
        ((Fm.F T).NscW : ℝ) ≤ Nsc T (2 * T) + r T ∧
        ((Fm.F T).sEq 1 : ℝ) ≤ N0simple T (2 * T) + r T := by
  have hP : (Zeta23.paramsOf Zeta23.stdProfile lam).Valid :=
    Zeta23.paramsOf_valid Zeta23.taperProfile_stdProfile hl0 hl1.le
  have heven : ∀ s, PolyWindow.psiN (-s) = PolyWindow.psiN s := fun s => by
    unfold PolyWindow.psiN; rw [PolyWindow.vP8_even]
  have h := frameFamily_of_zeroConfig_fix Zeta23.zetaZeroConfig Zeta23.paperInputs_zeta hP hl1 heven
    PolyWindow.psiN_continuous (fun s hs => ⟨(PolyWindow.psiN_pos s).le, PolyWindow.psiN_le_one s hs⟩)
    (fun T hT => by
      rw [PolyWindow.phiV_eq_phiP8]; exact PolyWindow.admWindow_phiP8 hP.taper hP.one_le_w hT)
    (by rw [← WindowInstances.half_interval, PolyWindow.integral_psiN]; norm_num)
    (by rw [← WindowInstances.half_interval, PolyWindow.integral_psiN_sq]; norm_num)
  have hpsi : psiPoly8A = fun s => (62500 / 50037 : ℝ) * PolyWindow.psiN s := by
    funext s; unfold psiPoly8A PolyWindow.psiN PolyWindow.vP8; ring
  obtain ⟨hk, hR⟩ := kPsi_Rlam_smul PolyWindow.psiN (κ := 62500 / 50037) (by norm_num) lam
  rw [hpsi, hk, hR]
  obtain ⟨Fm, r, hr, hev⟩ := h
  refine ⟨Fm, r, hr, ?_⟩
  filter_upwards [hev] with T hT
  obtain ⟨h1, h2, h3, h4⟩ := hT
  refine ⟨h1, h2, ?_, h4⟩
  rw [ZSeam.Nsc_eq]
  exact h3


end ZetaS
