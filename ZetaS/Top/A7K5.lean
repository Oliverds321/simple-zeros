/-
lean_work/L3_2/top/A7K5.lean — A7 (thm:sigd-OLL) at the K = 5 certificate, and hence A8 at K = 5, PROVED (L3_2, 28 Sep 2026).

`OLL_K5` is L4_1's `OLL` (lean_work/L4_1/A7_OLL.lean) verbatim, with the K = 5 numerals, the K = 5 error constants
(404 = 16K² + 4, 400 = 16K², 10 = 2K) and `OLL5.oll_height` (the K = 5 copy `OLLHeight5.lean` of L4_1's per-height
proof). All credit for the proof to L4_1. The majorant threshold is any β ≤ 33/10 (L2_2's `CertMajV2` has β = 33/10).
`frame_step2_K5'` then gives L2_2's (FI) at K = 5 via `A8b.frame_ineq_at`, and `sigma_K5'`, `dist_K5'` are A8 at K = 5.
-/
import ZetaS.Top.OLLHeight5
import ZetaS.Top.A8K

open Filter Asymptotics Finset

namespace ZetaS
namespace A7K5

open A8b A8aux

lemma dom_nonneg (F : ZeroFrame) {e' : ℝ}
    (hdom : IsPosDefKernel (fun t => (1 + e') * kPsi psiCos16 t - F.k t)) : 0 ≤ e' := by
  have h := (hdom 1 ![0]).diag_nonneg (i := 0)
  simp only [kerMat, Matrix.of_apply, sub_self, F.k_zero,
    SigmaHelpers.kPsi_zero OLL.psi_cont OLL.psi_pos] at h
  linarith

lemma n_le_Nw (F : ZeroFrame) : (F.n : ℝ) ≤ (F.Nw : ℝ) := by
  have h : F.n ≤ F.Nw := by
    calc F.n = ∑ _i : Fin F.n, 1 := by simp
      _ ≤ ∑ i, F.m i := Finset.sum_le_sum fun i _ => F.one_le_m i
      _ ≤ F.Nw := Nat.le_add_right _ _
  exact_mod_cast h

/-- **A7 at K = 5**: (OL_L) for the K = 5 certificate, any majorant threshold `β ≤ 33/10`. -/
theorem OLL_K5 {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM5) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10)
    (hML : ∀ T, ((Fm.F T).ML).IsHermitian) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      trFun (hML T) (kappaCh (2 - 2 * (1280197 / 10 ^ 8)))
        ≤ (Fm.F T).slackOn (Fm.F T).light ((Fm.F T).sEq 1)
          - 1280197 / 10 ^ 8 * ((Fm.F T).sEq 1 : ℝ) - 48749 / 3125000 * ((Fm.F T).sEq 2 : ℝ)
          + 1 / 125 * (Fm.F T).Λ + r T := by
  obtain ⟨W, ha1, ha2, hnu, hcertW⟩ := hcert
  obtain ⟨e, he, hke⟩ := Fm.kernel
  obtain ⟨e', he', hdom⟩ := Fm.dominate
  set B : ℝ := (∑ i, |W.b i 0|) + ∑ i, |W.b i 1| with hB
  refine ⟨fun T => 404 * (∑ i, ((Fm.F T).m i : ℝ) * (Fm.F T).delta i) + 400 * (e T * ((Fm.F T).Nw : ℝ)) + 10 * B,
    ?_, ?_⟩
  · have hNw : (fun T => ((Fm.F T).Nw : ℝ)) =O[atTop] N := by
      have h := Fm.window.isBigO.add (isBigO_refl N atTop)
      simpa using h
    have he_o : e =o[atTop] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).mpr he
    have h2 : (fun T => e T * ((Fm.F T).Nw : ℝ)) =o[atTop] N := by
      have := he_o.mul_isBigO hNw
      simpa only [one_mul] using this
    have h3 : (fun _ : ℝ => 10 * B) =o[atTop] N :=
      isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp Fm.N_tendsto))
    exact ((Fm.defect.const_mul_left 404).add (h2.const_mul_left 400)).add h3
  · have hsmall : ∀ᶠ T in atTop, e T < 1 / 20 := he (Iio_mem_nhds (by norm_num))
    have hsmall' : ∀ᶠ T in atTop, e' T < 1 / 40 := he' (Iio_mem_nhds (by norm_num))
    filter_upwards [hke, hdom, hsmall, hsmall'] with T hkT hdT hsT hs'T
    have he0 : 0 ≤ e T := (abs_nonneg _).trans (hkT 0)
    have he'0 : 0 ≤ e' T := dom_nonneg (Fm.F T) hdT
    have h := OLL5.oll_height (Fm.F T) hcertW hmaj hβ ha1 ha2 hnu he0 hsT.le hkT he'0 hs'T.le hdT (hML T)
    have hn : e T * ((Fm.F T).n : ℝ) ≤ e T * ((Fm.F T).Nw : ℝ) :=
      mul_le_mul_of_nonneg_left (n_le_Nw (Fm.F T)) he0
    rw [← hB] at h
    linarith

/-- (FI) at K = 5 from `OLL_K5`. -/
theorem frame_step2_K5' {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM5) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1280197 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 48749 / 3125000 * ((Fm.F T).sEq 2 : ℝ)
          - 1 / 125 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1280197 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt := by
  obtain ⟨ρ, hρ, hOLL⟩ := OLL_K5 Fm hcert hmaj hβ (fun T => ML_herm (Fm.F T))
  refine ⟨fun T => ρ T + 2 * (((Fm.F T).Nw : ℝ) - RHLinalg.rtrace (Fm.F T).Gt), ?_, ?_⟩
  · have := (hρ.add (Fm.window.const_mul_left 2)).sub (Fm.trace.const_mul_left 2)
    exact this.congr_left (fun T => by ring)
  · filter_upwards [hOLL] with T hT
    have hc : (0 : ℝ) ≤ 2 - 2 * (1280197 / 10 ^ 8) := by norm_num
    have hc0 : kappaCh (2 - 2 * (1280197 / 10 ^ 8)) 0 = 0 := by
      unfold kappaCh; norm_num
    exact frame_ineq_at (Fm.F T) _ _ _ _ _ hc hc0 hT

/-- **A8 at K = 5**, simple zeros (level A). -/
theorem sigma_K5' {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM5) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) - ε) * N T
        ≤ ((Fm.F T).NsW : ℝ) :=
  A8K.sigma_K5_of_FI Fm (frame_step2_K5' Fm hcert hmaj hβ)

/-- **A8 at K = 5**, distinct zeros (level A). -/
theorem dist_K5' {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM5) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) - ε) * N T
        ≤ ((Fm.F T).NdW : ℝ) :=
  A8K.dist_K5_of_FI Fm (frame_step2_K5' Fm hcert hmaj hβ)

end A7K5
end ZetaS
