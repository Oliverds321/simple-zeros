/-
rh72/lean_work/L0_2/ProfileAutocorr.lean — nodes W6 (autocorrelation of the window vs the profile) and W8 (the
moment limit J_T → J and cRatio → c) for an ARBITRARY `CoreProfile` ψ whose window family is admissible.

Generalises XiPrime/QuarticWindow/Moments.lean (`sharpQ_autocorr_eq`, `integral_abs_phiMQsq_sub_sharp`,
`autocorr_phiMQsq_close`) from `vQuartic` to any profile; the only window-specific inputs are continuity, the core
bounds 0 ≤ ψ ≤ 1, and continuity/[0,1]-bounds of the window (from `AdmWindow`):
  gv_close : |g_φ(y) − L·(ψ⋆ψ)(y/L)| ≤ 4w  for y ∈ [0, L]  (g = φ² ⋆ φ², ψ⋆ψ = `XiPrime.vConv ψ`),
and then, through the tree's `XiPrime.tendsto_JT_of_autocorr_close` (kernel D = id) and `tendsto_cRatio_cWin`,
  tendsto_JT : (2/L³)∫₀ᴸ g_T(y) y dy → 𝒥_id(λ;ψ)/λ = 2∫₀¹ r (ψ⋆ψ)(r) dr,
  tendsto_cRatio : cRatio(λ₁(T); a_T, b_T, J_T) → c_λ(ψ) = λ(∫ψ)²/(∫ψ² + λ·𝒥_id(λ;ψ)).
No `sorry`.
-/
import ZetaS.Window.ProfileMoments
import Zeta23.XiPrime.Window

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace ZetaS
namespace ProfileAutocorr

open Zeta23 Zeta23.XiPrime ZetaS.ProfileMoments

variable {v : ℝ → ℝ} {ϱ : ℝ → ℝ} {L w : ℝ}

/-- the sharp window `1_{[−L/2,L/2]}·ψ(·/L)`. -/
def sharpV (v : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ := (Set.Icc (-(L/2)) (L/2)).indicator (fun u => v (u / L)) u

theorem sharpV_autocorr_eq (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    ∫ u, sharpV v L u * sharpV v L (u + y) = L * vConv v (y / L) := by
  have hind : ∀ u : ℝ, sharpV v L u * sharpV v L (u + y)
      = (Set.Icc (-(L/2)) (L/2 - y)).indicator (fun u => v (u / L) * v ((u + y) / L)) u := by
    intro u
    unfold sharpV
    by_cases hu : u ∈ Set.Icc (-(L/2)) (L/2 - y)
    · have hu1 : u ∈ Set.Icc (-(L/2)) (L/2) := ⟨hu.1, by linarith [hu.2]⟩
      have hu2 : u + y ∈ Set.Icc (-(L/2)) (L/2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu1, Set.indicator_of_mem hu2]
    · rw [Set.indicator_of_notMem hu]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u + y)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2 - y)]
  have hsub := intervalIntegral.integral_comp_div (a := -(L/2)) (b := L/2 - y)
    (f := fun s => v s * v (s + y / L)) hL.ne'
  have e1 : -(L/2) / L = -(1:ℝ)/2 := by field_simp
  have e2 : (L/2 - y) / L = 1/2 - y / L := by field_simp
  rw [e1, e2, smul_eq_mul] at hsub
  unfold vConv
  rw [← hsub]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [add_div]

theorem integral_abs_phiVsq_sub_sharp (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) : ∫ u, |phiM (fV v L) ϱ L w u ^ 2 - sharpV v L u| ≤ 2 * w := by
  have hL : 0 < L := by linarith
  set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
      + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add <;>
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hpt : ∀ u : ℝ, |phiM (fV v L) ϱ L w u ^ 2 - sharpV v L u| ≤ maj u := by
    intro u
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    have hval : phiM (fV v L) ϱ L w u ^ 2 = mV v L u * Taper.phi ϱ L w u ^ 2 := phiV_sq_eq hv hϱ hw hL u
    rcases le_or_gt |u| (L/2 - w) with hpl | hedge
    · have huIcc : u ∈ Set.Icc (-(L/2)) (L/2) := by
        rw [abs_le] at hpl
        constructor <;> [linarith [hpl.1]; linarith [hpl.2]]
      rw [hval, Taper.phi_eq_one hϱ hw hpl, one_pow, mul_one, mV_core hv hL huIcc]
      unfold sharpV
      rw [Set.indicator_of_mem huIcc, sub_self, abs_zero]
      exact hmaj0
    · rcases le_or_gt |u| (L/2) with hin | hout
      · have hbound : |phiM (fV v L) ϱ L w u ^ 2 - sharpV v L u| ≤ 1 := by
          have h1' : 0 ≤ phiM (fV v L) ϱ L w u ^ 2 := sq_nonneg _
          have h2' : phiM (fV v L) ϱ L w u ^ 2 ≤ 1 := by
            rw [hval]
            calc mV v L u * Taper.phi ϱ L w u ^ 2 ≤ 1 * 1 ^ 2 :=
                  mul_le_mul (mV_le_one u)
                    (pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2)
                    (sq_nonneg _) zero_le_one
              _ = 1 := by norm_num
          have h3' : 0 ≤ sharpV v L u := by
            unfold sharpV
            apply Set.indicator_nonneg
            intro x hx
            exact hv.nonneg _ (core_abs hL (abs_le.mpr ⟨hx.1, hx.2⟩))
          have h4' : sharpV v L u ≤ 1 := by
            unfold sharpV
            by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
            · rw [Set.indicator_of_mem hm]; exact hv.le_one _ (core_abs hL (abs_le.mpr ⟨hm.1, hm.2⟩))
            · rw [Set.indicator_of_notMem hm]; exact zero_le_one
          rw [abs_le]
          constructor <;> linarith
        have hone : (1:ℝ) ≤ maj u := by
          rw [hmaj]
          show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
            + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
          rcases le_or_gt u 0 with hneg | hpos
          · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
              refine ⟨?_, ?_⟩
              · have : |u| = -u := abs_of_nonpos hneg
                rw [this] at hin
                linarith
              · have : |u| = -u := abs_of_nonpos hneg
                rw [this] at hedge
                linarith
            have := hind0 (Set.Icc (L/2 - w) (L/2)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
          · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
              refine ⟨?_, ?_⟩
              · have : |u| = u := abs_of_pos hpos
                rw [this] at hedge
                linarith
              · have : |u| = u := abs_of_pos hpos
                rw [this] at hin
                linarith
            have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
        linarith
      · have h1' : phiM (fV v L) ϱ L w u = 0 := phiM_eq_zero hϱ hw (le_of_lt hout)
        have h2' : sharpV v L u = 0 := by
          unfold sharpV
          apply Set.indicator_of_notMem
          intro hm
          have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
          linarith
        rw [h1', h2']
        norm_num
        exact hmaj0
  calc ∫ u, |phiM (fV v L) ϱ L w u ^ 2 - sharpV v L u|
      ≤ ∫ u, maj u := by
        apply MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hImaj
          (MeasureTheory.ae_of_all _ hpt)
    _ = 2 * w := by
        rw [hmaj]
        rw [MeasureTheory.integral_add
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))),
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

/-- **W6: `|g_φ(y) − L·(ψ⋆ψ)(y/L)| ≤ 4w` for `y ∈ [0, L]`**, for any admissible profiled window. -/
theorem gv_close (hv : CoreProfile v) (hϱ : TaperProfile ϱ) {c : ℝ}
    (hW : AdmWindow (phiM (fV v L) ϱ L w) L w c) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    |AdmWindow.gv (phiM (fV v L) ϱ L w) y - L * vConv v (y / L)| ≤ 4 * w := by
  have hw0 : 0 < w := hW.w_pos
  have hwL' : 2 * w ≤ L := hW.two_w_le
  have hL : 0 < L := hW.L_pos
  set h : ℝ → ℝ := fun u => phiM (fV v L) ϱ L w u ^ 2 with hhdef
  set k : ℝ → ℝ := sharpV v L with hkdef
  have hh_cont : Continuous h := hW.sq_continuous
  have hh1 : ∀ u, |h u| ≤ 1 := by
    intro u
    rw [hhdef]
    simp only
    rw [abs_of_nonneg (sq_nonneg _)]
    calc phiM (fV v L) ϱ L w u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (hW.nonneg u) (hW.le_one u) 2
      _ = 1 := one_pow 2
  have hk_meas : Measurable k := by
    rw [hkdef]
    unfold sharpV
    exact Measurable.indicator (hv.cont.comp (continuous_id.div_const L)).measurable measurableSet_Icc
  have hk1 : ∀ u, |k u| ≤ 1 := by
    intro u
    rw [hkdef]
    unfold sharpV
    by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
    · have hc := core_abs hL (abs_le.mpr ⟨hm.1, hm.2⟩)
      rw [Set.indicator_of_mem hm, abs_le]
      exact ⟨by linarith [hv.nonneg _ hc], hv.le_one _ hc⟩
    · rw [Set.indicator_of_notMem hm, abs_zero]
      exact zero_le_one
  have hcs : HasCompactSupport h := hW.sq_hasCompactSupport
  have hint_h : Integrable h := hh_cont.integrable_of_hasCompactSupport hcs
  have hint_k : Integrable k := by
    rw [hkdef]
    unfold sharpV
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (((hv.cont.comp (continuous_id.div_const L)).continuousOn).integrableOn_compact isCompact_Icc)
  have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
  have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
  have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
  have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
  have hmeas_hy : MeasureTheory.AEStronglyMeasurable (fun u => h (u + y)) MeasureTheory.volume :=
    hint_hy.aestronglyMeasurable
  have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
    have := hint_d.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) := by
    exact hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hint_hh : Integrable (fun u => h u * h (u + y)) := by
    have := hint_h.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_kk : Integrable (fun u => k u * k (u + y)) := by
    exact hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hCk : ∫ u, k u * k (u + y) = L * vConv v (y / L) := sharpV_autocorr_eq hL hy0 hyL
  have hdecomp : Params.autocorr h y - L * vConv v (y / L)
      = (∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y)) := by
    have e1 : Params.autocorr h y - L * vConv v (y / L)
        = ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
      rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl, ← hCk,
        MeasureTheory.integral_sub hint_hh hint_kk]
    rw [e1, ← MeasureTheory.integral_add hint_p1 hint_p2]
    apply MeasureTheory.integral_congr_ae
    apply MeasureTheory.ae_of_all
    intro u
    ring
  have hd2w := integral_abs_phiVsq_sub_sharp (L := L) hv hϱ hw0 hwL'
  have hint_dabs : Integrable (fun u => |h u - k u|) := hint_d.abs
  have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * w := by
    calc |∫ u, (h u - k u) * h (u + y)| ≤ ∫ u, |(h u - k u) * h (u + y)| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h u - k u| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hint_dabs
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |(h u - k u) * h (u + y)| ≤ |h u - k u|
          rw [abs_mul]
          calc |h u - k u| * |h (u + y)| ≤ |h u - k u| * 1 :=
                mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg _)
            _ = |h u - k u| := mul_one _
      _ ≤ 2 * w := hd2w
  have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * w := by
    have htrans : ∫ u, |h (u + y) - k (u + y)| = ∫ u, |h u - k u| :=
      MeasureTheory.integral_add_right_eq_self (fun u => |h u - k u|) y
    calc |∫ u, k u * (h (u + y) - k (u + y))|
        ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) (hint_dy.abs)
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |k u * (h (u + y) - k (u + y))| ≤ |h (u + y) - k (u + y)|
          rw [abs_mul]
          calc |k u| * |h (u + y) - k (u + y)| ≤ 1 * |h (u + y) - k (u + y)| :=
                mul_le_mul_of_nonneg_right (hk1 u) (abs_nonneg _)
            _ = _ := one_mul _
      _ = ∫ u, |h u - k u| := htrans
      _ ≤ 2 * w := hd2w
  show |Params.autocorr h y - L * vConv v (y / L)| ≤ 4 * w
  calc |Params.autocorr h y - L * vConv v (y / L)|
      = |(∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y))| := by rw [hdecomp]
    _ ≤ |∫ u, (h u - k u) * h (u + y)| + |∫ u, k u * (h (u + y) - k (u + y))| := abs_add_le _ _
    _ ≤ 4 * w := by linarith

/-! ## W8: the moment limits and the ratio limit -/

/-- `J_T := (2/L³)∫₀ᴸ g_T(y) y dy` (ThmD's `concreteDataD.JT`, eq:abJ) for the family `P.phiV ψ`. -/
def JTV (P : Params) (v : ℝ → ℝ) (T : ℝ) : ℝ :=
  2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), AdmWindow.gv (P.phiV v T) y * y

/-- **W8a: `J_T → 2∫₀¹ r (ψ⋆ψ)(r) dr`** (as `jWin id λ ψ / λ`), for an admissible `CoreProfile` family. -/
theorem tendsto_JTV {P : Params} (hP : P.Valid) (hv : CoreProfile v) {c : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w c) :
    Tendsto (JTV P v) atTop (𝓝 (jWin id P.lam v / P.lam)) := by
  have hL : Tendsto P.L atTop atTop := Params.tendsto_L_of_valid hP
  have hl : ∀ᶠ T in atTop, 0 < l T := by
    have hlt : Tendsto l atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
    exact hlt.eventually_gt_atTop 0
  have h8 : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := hL.eventually_ge_atTop _
  have hmain := tendsto_JT_of_autocorr_close (D := id) (v := v) (C := 4) hP continuousOn_id hv.cont
    (g := fun T => AdmWindow.gv (P.phiV v T))
    (by filter_upwards [h8] with T hT using (hadm T hT).gv_continuous)
    (by
      filter_upwards [h8] with T hT y hy
      have := gv_close hv hP.taper (by rw [← phiV_eq_phiM]; exact hadm T hT) hy.1 hy.2
      rwa [← phiV_eq_phiM] at this)
  refine hmain.congr' ?_
  filter_upwards [hl] with T hlT
  unfold JTV
  rw [mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [id]
  field_simp

/-- **W8b: `cRatio(λ₁(T); a_T, b_T, J_T) → c_λ(ψ) = λ(∫ψ)²/(∫ψ² + λ𝒥_id(λ;ψ))`.** -/
theorem tendsto_cRatioV {P : Params} (hP : P.Valid) (hv : CoreProfile v) {c : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w c)
    (hden : 0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + P.lam * jWin id P.lam v) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) (AdmWindow.av (P.phiV v T) (P.L T))
      (AdmWindow.bv (P.phiV v T) (P.L T)) (JTV P v T)) atTop (𝓝 (cWin id P.lam v)) := by
  have hL : Tendsto P.L atTop atTop := Params.tendsto_L_of_valid hP
  have h8 : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := hL.eventually_ge_atTop _
  have hclose : ∀ {f : ℝ → ℝ} {x : ℝ}, (∀ᶠ T in atTop, |f T - x| ≤ 2 * P.w / P.L T) →
      Tendsto f atTop (𝓝 x) := by
    intro f x hf
    have h0 : Tendsto (fun T => 2 * P.w / P.L T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hL
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ h0
    filter_upwards [hf] with T hT
    rw [Real.norm_eq_abs]; exact hT
  have ha : Tendsto (fun T => AdmWindow.av (P.phiV v T) (P.L T)) atTop
      (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), v s)) := hclose (by
    filter_upwards [h8] with T hT
    rw [phiV_eq_phiM]; exact av_close hv hP.taper hP.one_le_w hT)
  have hb : Tendsto (fun T => AdmWindow.bv (P.phiV v T) (P.L T)) atTop
      (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)) := hclose (by
    filter_upwards [h8] with T hT
    rw [phiV_eq_phiM]; exact bv_close hv hP.taper hP.one_le_w hT)
  exact tendsto_cRatio_cWin hP.lam_pos (ThmD.tendsto_lam1 hP.lam_pos) ha hb (tendsto_JTV hP hv hadm) hden

end ProfileAutocorr
end ZetaS

end

#print axioms ZetaS.ProfileAutocorr.gv_close
#print axioms ZetaS.ProfileAutocorr.tendsto_JTV
#print axioms ZetaS.ProfileAutocorr.tendsto_cRatioV
