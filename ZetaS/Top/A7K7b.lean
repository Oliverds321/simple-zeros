/-
lean_work/L3_2/top/A7K7b.lean — L4_1's A7 `OLL` restated for ANY majorant threshold β ≤ 33/10 (the per-height
`OLL.oll_height` already allows it; only the wrapper `OLL` fixes `CertMaj`), and A8 at K = 7 for such β (L3_2).
-/
import ZetaS.Top.A7K5

open Filter Asymptotics Finset

namespace ZetaS
namespace A7K7b

open A8b A8aux A7K5

/-- **A7 at K = 7, any β ≤ 33/10**: (OL_L) for the K = 7 certificate, any majorant threshold `β ≤ 33/10`. -/
theorem OLL_K7b {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM7) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10)
    (hML : ∀ T, ((Fm.F T).ML).IsHermitian) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      trFun (hML T) (kappaCh (2 - 2 * (1824837 / 10 ^ 8)))
        ≤ (Fm.F T).slackOn (Fm.F T).light ((Fm.F T).sEq 1)
          - 1824837 / 10 ^ 8 * ((Fm.F T).sEq 1 : ℝ) - 1168069 / (5 * 10 ^ 7) * ((Fm.F T).sEq 2 : ℝ)
          + 3 / 250 * (Fm.F T).Λ + r T := by
  obtain ⟨W, ha1, ha2, hnu, hcertW⟩ := hcert
  obtain ⟨e, he, hke⟩ := Fm.kernel
  obtain ⟨e', he', hdom⟩ := Fm.dominate
  set B : ℝ := (∑ i, |W.b i 0|) + ∑ i, |W.b i 1| with hB
  refine ⟨fun T => 788 * (∑ i, ((Fm.F T).m i : ℝ) * (Fm.F T).delta i) + 784 * (e T * ((Fm.F T).Nw : ℝ)) + 14 * B,
    ?_, ?_⟩
  · have hNw : (fun T => ((Fm.F T).Nw : ℝ)) =O[atTop] N := by
      have h := Fm.window.isBigO.add (isBigO_refl N atTop)
      simpa using h
    have he_o : e =o[atTop] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).mpr he
    have h2 : (fun T => e T * ((Fm.F T).Nw : ℝ)) =o[atTop] N := by
      have := he_o.mul_isBigO hNw
      simpa only [one_mul] using this
    have h3 : (fun _ : ℝ => 14 * B) =o[atTop] N :=
      isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp Fm.N_tendsto))
    exact ((Fm.defect.const_mul_left 788).add (h2.const_mul_left 784)).add h3
  · have hsmall : ∀ᶠ T in atTop, e T < 1 / 20 := he (Iio_mem_nhds (by norm_num))
    have hsmall' : ∀ᶠ T in atTop, e' T < 1 / 40 := he' (Iio_mem_nhds (by norm_num))
    filter_upwards [hke, hdom, hsmall, hsmall'] with T hkT hdT hsT hs'T
    have he0 : 0 ≤ e T := (abs_nonneg _).trans (hkT 0)
    have he'0 : 0 ≤ e' T := dom_nonneg (Fm.F T) hdT
    have h := OLL.oll_height (Fm.F T) hcertW hmaj hβ ha1 ha2 hnu he0 hsT.le hkT he'0 hs'T.le hdT (hML T)
    have hn : e T * ((Fm.F T).n : ℝ) ≤ e T * ((Fm.F T).Nw : ℝ) :=
      mul_le_mul_of_nonneg_left (n_le_Nw (Fm.F T)) he0
    rw [← hB] at h
    linarith

/-- (FI) at K = 7 from `OLL_K7b`. -/
theorem frame_step2_K7' {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM7) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1824837 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 1168069 / (5 * 10 ^ 7) * ((Fm.F T).sEq 2 : ℝ)
          - 3 / 250 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1824837 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt := by
  obtain ⟨ρ, hρ, hOLL⟩ := OLL_K7b Fm hcert hmaj hβ (fun T => ML_herm (Fm.F T))
  refine ⟨fun T => ρ T + 2 * (((Fm.F T).Nw : ℝ) - RHLinalg.rtrace (Fm.F T).Gt), ?_, ?_⟩
  · have := (hρ.add (Fm.window.const_mul_left 2)).sub (Fm.trace.const_mul_left 2)
    exact this.congr_left (fun T => by ring)
  · filter_upwards [hOLL] with T hT
    have hc : (0 : ℝ) ≤ 2 - 2 * (1824837 / 10 ^ 8) := by norm_num
    have hc0 : kappaCh (2 - 2 * (1824837 / 10 ^ 8)) 0 = 0 := by
      unfold kappaCh; norm_num
    exact frame_ineq_at (Fm.F T) _ _ _ _ _ hc hc0 hT

/-- **A8 at K = 7, any β ≤ 33/10**, simple zeros (level A). -/
theorem sigma_K7' {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM7) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NsW : ℝ) :=
  A8K.sigma_K7b_of_FI Fm (frame_step2_K7' Fm hcert hmaj hβ)

/-- **A8 at K = 7, any β ≤ 33/10**, distinct zeros (level A). -/
theorem dist_K7' {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM7) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NdW : ℝ) :=
  A8K.dist_K7b_of_FI Fm (frame_step2_K7' Fm hcert hmaj hβ)

end A7K7b
end ZetaS
