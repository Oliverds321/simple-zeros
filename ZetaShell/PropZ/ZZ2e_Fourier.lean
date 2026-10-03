/-
L7_5 (28 Sep 2026), round 8: Step 4 on the Fourier side.
`H̃ = 1_{t>0} H_ρ` is smooth with compact support (`Htil_smooth`, `Htil_compact`), `G_μ(z) = f_j(−μz)`, and
  `I_ρ[f_j](ξ; μ) = (H̃ ⋆ G_μ)(ξ)`,   so   `∫|I_ρ|² = ∫ |𝓕H̃|² |𝓕G_μ|²`   (`Irho_L2_fourier`, via `FourierLink`).
-/
import ZetaShell.PropZ.ZZ3b_Irho
import ZetaShell.PropZ.FourierLink

open MeasureTheory FourierTransform Complex Convolution

namespace ZetaShell.PropZ

noncomputable def Htil (T κ : ℝ) (Ξ : ℝ → ℝ) (ρ : ℂ) : ℝ → ℂ := (Set.Ioi (0 : ℝ)).indicator (Hrho T κ Ξ ρ)

noncomputable def Gmu (f : ℝ → ℝ) (j : ℕ) (μ : ℝ) : ℝ → ℂ := fun z => ((fj f j (-μ * z) : ℝ) : ℂ)

theorem Htil_zero_off (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (T : ℝ) (ρ : ℂ)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (t : ℝ) (ht : t ∉ Set.Icc (Real.exp (-κ)) (Real.exp κ)) :
    Htil T κ Ξ ρ t = 0 := by
  unfold Htil
  by_cases h0 : t ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h0]; exact Hrho_zero_off κ hκ Ξ hΞ T ρ hρ0 hρ1 t h0 ht
  · rw [Set.indicator_of_notMem h0]

theorem Htil_compact (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (T : ℝ) (ρ : ℂ)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) : HasCompactSupport (Htil T κ Ξ ρ) := by
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := Real.exp (-κ)) (b := Real.exp κ)) (isClosed_tsupport _) ?_
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hc
  exact ht (Htil_zero_off κ hκ Ξ hΞ T ρ hρ0 hρ1 t hc)

theorem Htil_smooth (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (T : ℝ) (ρ : ℂ)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) : ContDiff ℝ (⊤ : ℕ∞) (Htil T κ Ξ ρ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases le_or_gt x 0 with hx | hx
  · -- near `x ≤ 0` the function vanishes
    have hev : Htil T κ Ξ ρ =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      have hlt : x < Real.exp (-κ) := lt_of_le_of_lt hx (Real.exp_pos _)
      filter_upwards [Iio_mem_nhds hlt] with t ht
      exact Htil_zero_off κ hκ Ξ hΞ T ρ hρ0 hρ1 t fun h => absurd h.1 (not_le.mpr ht)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · -- near `x > 0` it is `H_ρ`, written with `exp` and `log`
    have hev : Htil T κ Ξ ρ =ᶠ[nhds x] fun t => ZetaShell.DTFacts.DTf T (-Real.log t)
        * ((Ξ (Real.log t / κ) : ℝ) : ℂ) * Complex.exp (((Real.log t : ℝ) : ℂ) * (ρ - 3 / 2)) := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      unfold Htil Hrho
      rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from ht), DT_eq_DTf,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)), Complex.ofReal_log ht.le]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hlog : ContDiffAt ℝ (⊤ : ℕ∞) Real.log x := Real.contDiffAt_log.mpr (ne_of_gt hx)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => ZetaShell.DTFacts.DTf T (-Real.log t)) x :=
      (ZetaShell.DTFacts.DTf_contDiff T).contDiffAt.comp x hlog.neg
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => ((Ξ (Real.log t / κ) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (hΞ.smooth.contDiffAt.comp x (hlog.div_const κ))
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => Complex.exp (((Real.log t : ℝ) : ℂ) * (ρ - 3 / 2))) x :=
      Complex.contDiff_exp.contDiffAt.comp x ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog).mul
        contDiffAt_const)
    exact (h1.mul h2).mul h3

theorem Gmu_smooth (f : ℝ → ℝ) (hf : TestFn f) (j : ℕ) (μ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Gmu f j μ) :=
  Complex.ofRealCLM.contDiff.comp ((fj_smooth f hf j).1.comp (contDiff_const.mul contDiff_id))

theorem Gmu_compact (f : ℝ → ℝ) (hf : TestFn f) (j : ℕ) (μ : ℝ) (hμ : 0 < μ) : HasCompactSupport (Gmu f j μ) := by
  have h := ((fj_smooth f hf j).2.comp_smul (neg_ne_zero.mpr hμ.ne'))
  exact h.comp_left (g := fun y : ℝ => ((y : ℝ) : ℂ)) Complex.ofReal_zero

theorem Irho_eq_conv (T κ : ℝ) (Ξ f : ℝ → ℝ) (j : ℕ) (ρ : ℂ) (μ ξ : ℝ) :
    Irho T κ Ξ f j ρ μ ξ = (Htil T κ Ξ ρ ⋆[ContinuousLinearMap.mul ℂ ℂ] Gmu f j μ) ξ := by
  unfold Irho
  rw [convolution_def, ← integral_indicator measurableSet_Ioi]
  congr 1; funext t
  rw [Set.indicator_mul_left, ContinuousLinearMap.mul_apply']
  unfold Htil Gmu
  congr 3; ring

theorem Irho_L2_fourier (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (j : ℕ) (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (μ : ℝ) (hμ : 0 < μ) :
    (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) = ∫ η, ‖𝓕 (Htil T κ Ξ ρ) η‖ ^ 2 * ‖𝓕 (Gmu f j μ) η‖ ^ 2 := by
  simp only [Irho_eq_conv]
  exact ZetaShell.FourierLink.norm_sq_convolution _ _ (Htil_smooth κ hκ Ξ hΞ T ρ hρ0 hρ1)
    (Htil_compact κ hκ Ξ hΞ T ρ hρ0 hρ1) (Gmu_smooth f hf j μ) (Gmu_compact f hf j μ hμ)

end ZetaShell.PropZ
