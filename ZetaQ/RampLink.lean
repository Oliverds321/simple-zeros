/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/RampLink.lean — **the §11 link `B(v_design) ≤ B(v_profile) + O(w/ℒ)` (F58 item 7), PROVED**
(with the bandwidth floor `1 ≤ λ`; see the note before `profileRampLink'`).

Contents.
  §A  the ramp in the scale-free variable (`ramp`), `φ(tℒ) = p(t)·ramp(t)`, and `0 ≤ φ ≤ 1`,
      `φ` continuous under `Valid` ALONE (no `8w ≤ L`);
  §B  `vDesign`: pointwise formula, `0 ≤ vDesign ≤ 1/(λa)`, support, continuity, integrability,
      mass `∫ vDesign = 1`, `Admissible λ (vDesign P)`;
  §C  `vProfile`: the core mass `profMass = ∫_{−λ/2}^{λ/2} p²`, `0 ≤ vProfile ≤ 1/profMass`,
      support, integrability, mass, `Admissible λ (vProfile P)`;
  §D  the L¹ distance: `profMass − λa = ∫_{core} p²(1 − ramp²) ∈ [0, 2w/ℒ]` and
      `‖vDesign − vProfile‖₁ ≤ 2(profMass − λa)/profMass ≤ 4(w/ℒ)/(λa)`;
  §E  `B` is Lipschitz in `L¹` on uniformly bounded admissible profiles:
      `|B C v − B C v′| ≤ (‖v‖∞ + ‖v′‖∞ + 2(1 + C)λ)·‖v − v′‖₁`;
  §F  assembly: `B C (vDesign P) ≤ B C (vProfile P) + (128/(9λ²) + (32/3)(1 + C))·(w/ℒ)` under
      `Valid` alone, and `≤ … + rampCost C P` (constant 64) under `1 ≤ λ`.

Imports only `ZetaQ.PayoffSmooth` (hence `ZetaQ.DesignProfile`, `ZetaQ.Window`, `ZetaQ.Payoff`).
-/
import ZetaQ.PayoffSmooth

noncomputable section

open Real MeasureTheory Set

namespace ZetaQ

/-! ## §A. `φ` facts under `Valid` alone -/

namespace ParamsQ

variable {P : ParamsQ}

/-- `0 ≤ φ` from `Valid` alone (no `8w ≤ L`): off `|u| < L/2` the ramp vanishes, on it `p ≥ 1/6`. -/
theorem Valid.phiQ_nonneg' (hP : P.Valid) (u : ℝ) : 0 ≤ P.phiQ u := by
  rw [hP.phiQ_eq]
  show 0 ≤ P.prof.eval (u / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u
  by_cases h : P.LB / 2 ≤ |u|
  · rw [Zeta23.Taper.phi_eq_zero hP.taper hP.w_pos h, mul_zero]
  · rw [not_le] at h
    have hLL := hP.LL_pos
    have hcore : |u / P.LL| ≤ P.lam / 2 := by
      rw [abs_div, abs_of_pos hLL, div_le_iff₀ hLL]
      have e : P.lam / 2 * P.LL = P.LB / 2 := by unfold LB; ring
      rw [e]; exact h.le
    exact mul_nonneg (by linarith [hP.profile.bulk _ hcore]) (Zeta23.Taper.phi_nonneg hP.taper u)

/-- `φ ≤ 1` from `Valid` alone. -/
theorem Valid.phiQ_le_one' (hP : P.Valid) (u : ℝ) : P.phiQ u ≤ 1 := by
  rw [hP.phiQ_eq]
  show P.prof.eval (u / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u ≤ 1
  by_cases h : P.LB / 2 ≤ |u|
  · rw [Zeta23.Taper.phi_eq_zero hP.taper hP.w_pos h, mul_zero]; exact zero_le_one
  · rw [not_le] at h
    have hLL := hP.LL_pos
    have hcore : |u / P.LL| ≤ P.lam / 2 := by
      rw [abs_div, abs_of_pos hLL, div_le_iff₀ hLL]
      have e : P.lam / 2 * P.LL = P.LB / 2 := by unfold LB; ring
      rw [e]; exact h.le
    have h1 := hP.profile.le_one _ hcore
    have h2 := hP.profile.bulk _ hcore
    have h3 := Zeta23.Taper.phi_nonneg hP.taper (L := P.LB) (w := P.w) u
    have h4 := Zeta23.Taper.phi_le_one hP.taper (L := P.LB) (w := P.w) u
    nlinarith

/-- `φ` is continuous from `Valid` alone (the ramp `ϱ` is `C³`, the profile is a polynomial). -/
theorem Valid.phiQ_continuous' (hP : P.Valid) : Continuous P.phiQ := by
  rw [hP.phiQ_eq]
  refine Continuous.mul (P.prof.continuous.comp (by fun_prop)) ?_
  unfold Zeta23.Taper.phi
  exact hP.taper.contDiff.continuous.comp (by fun_prop)

/-- `λ·a = ∫ φ(tℒ)² dt` — the window's second moment in the scale-free variable (change of
variables `u = tℒ` in `∫ φ² = aL`). -/
theorem Valid.lam_mul_aQ_eq (hP : P.Valid) : P.lam * P.aQ = ∫ t, P.phiQ (t * P.LL) ^ 2 := by
  have hLL := hP.LL_pos
  have h : ∫ t, P.phiQ (t * P.LL) ^ 2 = |P.LL⁻¹| • ∫ u, P.phiQ u ^ 2 :=
    MeasureTheory.Measure.integral_comp_mul_right (fun u => P.phiQ u ^ 2) P.LL
  rw [h, ← P.LB_mul_aQ hP.l_ne_zero hP.LB_pos.ne', abs_of_pos (inv_pos.mpr hLL), smul_eq_mul]
  unfold LB
  field_simp

end ParamsQ

namespace Payoff

variable {P : ParamsQ}

/-- the ramp factor in the scale-free variable `t = u/ℒ`: `ramp(t) = ϱ((L/2 − |t|ℒ)/w)`. -/
def ramp (P : ParamsQ) (t : ℝ) : ℝ := Zeta23.Taper.phi P.ϱ P.LB P.w (t * P.LL)

theorem ramp_nonneg (hP : P.Valid) (t : ℝ) : 0 ≤ ramp P t := Zeta23.Taper.phi_nonneg hP.taper _

theorem ramp_le_one (hP : P.Valid) (t : ℝ) : ramp P t ≤ 1 := Zeta23.Taper.phi_le_one hP.taper _

theorem ramp_sq_le_one (hP : P.Valid) (t : ℝ) : ramp P t ^ 2 ≤ 1 :=
  pow_le_one₀ (ramp_nonneg hP t) (ramp_le_one hP t)

theorem ramp_continuous (hP : P.Valid) : Continuous (ramp P) := by
  unfold ramp Zeta23.Taper.phi
  exact hP.taper.contDiff.continuous.comp (by fun_prop)

/-- `ramp = 1` on the plateau `|t| ≤ λ/2 − w/ℒ`. -/
theorem ramp_eq_one (hP : P.Valid) {t : ℝ} (ht : |t| ≤ P.lam / 2 - P.w / P.LL) : ramp P t = 1 := by
  apply Zeta23.Taper.phi_eq_one hP.taper hP.w_pos
  have hLL := hP.LL_pos
  rw [abs_mul, abs_of_pos hLL]
  have h := mul_le_mul_of_nonneg_right ht hLL.le
  have e : (P.lam / 2 - P.w / P.LL) * P.LL = P.LB / 2 - P.w := by
    rw [sub_mul, div_mul_cancel₀ _ hLL.ne']; unfold ParamsQ.LB; ring
  linarith

/-- `ramp = 0` off the core `|t| ≥ λ/2`. -/
theorem ramp_eq_zero (hP : P.Valid) {t : ℝ} (ht : P.lam / 2 ≤ |t|) : ramp P t = 0 := by
  apply Zeta23.Taper.phi_eq_zero hP.taper hP.w_pos
  have hLL := hP.LL_pos
  rw [abs_mul, abs_of_pos hLL]
  have h := mul_le_mul_of_nonneg_right ht hLL.le
  unfold ParamsQ.LB
  linarith

/-- `φ(tℒ) = p(t)·ramp(t)`. -/
theorem phiQ_mul_LL (hP : P.Valid) (t : ℝ) : P.phiQ (t * P.LL) = P.prof.eval t * ramp P t := by
  rw [hP.phiQ_eq]
  show P.prof.eval (t * P.LL / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w (t * P.LL) = _
  rw [mul_div_cancel_right₀ _ hP.LL_pos.ne']
  rfl

/-! ## §B. `vDesign` -/

theorem vDesign_eq (hP : P.Valid) (t : ℝ) :
    vDesign P t = P.phiQ (t * P.LL) ^ 2 / (P.lam * P.aQ) := by
  unfold vDesign ParamsQ.LB
  have h1 := hP.LL_pos.ne'
  have h2 := hP.lam_pos.ne'
  have h3 := hP.aQ_pos.ne'
  field_simp

theorem vDesign_eq_prof_ramp (hP : P.Valid) (t : ℝ) :
    vDesign P t = (P.prof.eval t) ^ 2 * (ramp P t) ^ 2 / (P.lam * P.aQ) := by
  rw [vDesign_eq hP, phiQ_mul_LL hP, mul_pow]

theorem vDesign_nonneg (hP : P.Valid) (t : ℝ) : 0 ≤ vDesign P t := by
  rw [vDesign_eq hP]; exact div_nonneg (sq_nonneg _) (mul_pos hP.lam_pos hP.aQ_pos).le

/-- the sup bound `vDesign ≤ 1/(λa)` (`≤ 4/(3λ)` by `a ≥ 3/4`). -/
theorem vDesign_le (hP : P.Valid) (t : ℝ) : vDesign P t ≤ 1 / (P.lam * P.aQ) := by
  rw [vDesign_eq hP]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (hP.phiQ_nonneg' _) (hP.phiQ_le_one' _))
    (mul_pos hP.lam_pos hP.aQ_pos).le

theorem vDesign_eq_zero (hP : P.Valid) {t : ℝ} (ht : P.lam / 2 ≤ |t|) : vDesign P t = 0 := by
  rw [vDesign_eq_prof_ramp hP, ramp_eq_zero hP ht]; ring

theorem vDesign_supp (hP : P.Valid) (t : ℝ) (h : vDesign P t ≠ 0) : |t| ≤ P.lam / 2 := by
  by_contra h'
  rw [not_le] at h'
  exact h (vDesign_eq_zero hP h'.le)

theorem vDesign_continuous (hP : P.Valid) : Continuous (vDesign P) := by
  unfold vDesign
  exact (((hP.phiQ_continuous'.comp (by fun_prop)).pow 2).mul continuous_const).div_const _

theorem vDesign_hasCompactSupport (hP : P.Valid) : HasCompactSupport (vDesign P) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(P.lam / 2)) (b := P.lam / 2))
    fun t ht => abs_le.mp (vDesign_supp hP t (Function.mem_support.mp ht))

theorem vDesign_integrable (hP : P.Valid) : Integrable (vDesign P) :=
  (vDesign_continuous hP).integrable_of_hasCompactSupport (vDesign_hasCompactSupport hP)

/-- `∫ vDesign = 1`. -/
theorem integral_vDesign (hP : P.Valid) : ∫ t, vDesign P t = 1 := by
  have hN : 0 < P.lam * P.aQ := mul_pos hP.lam_pos hP.aQ_pos
  simp_rw [vDesign_eq hP]
  rw [integral_div, ← hP.lam_mul_aQ_eq, div_self hN.ne']

/-- **`vDesign` is admissible at `λ`** (under `Valid` alone). -/
theorem vDesign_admissible (hP : P.Valid) : Admissible P.lam (vDesign P) :=
  ⟨vDesign_nonneg hP, vDesign_integrable hP, integral_vDesign hP, vDesign_supp hP⟩

/-! ## §C. `vProfile` -/

/-- the core mass `∫_{−λ/2}^{λ/2} p²` of the profile (the normaliser of `vProfile`). -/
def profMass (P : ParamsQ) : ℝ := ∫ s in (-(P.lam / 2))..(P.lam / 2), (P.prof.eval s) ^ 2

theorem vProfile_eq (P : ParamsQ) (t : ℝ) :
    vProfile P t = if |t| ≤ P.lam / 2 then (P.prof.eval t) ^ 2 / profMass P else 0 := rfl

theorem prof_sq_continuous (P : ParamsQ) : Continuous fun s => (P.prof.eval s) ^ 2 :=
  P.prof.continuous.pow 2

theorem profMass_eq_setIntegral (hP : P.Valid) :
    profMass P = ∫ s in Icc (-(P.lam / 2)) (P.lam / 2), (P.prof.eval s) ^ 2 := by
  unfold profMass
  rw [intervalIntegral.integral_of_le (by linarith [hP.lam_pos]), integral_Icc_eq_integral_Ioc]

/-- `profMass ≥ λ/36` (the bulk floor `p ≥ 1/6`). -/
theorem profMass_ge (hP : P.Valid) : P.lam / 36 ≤ profMass P := by
  unfold profMass
  have h : ∫ s in (-(P.lam / 2))..(P.lam / 2), (1 / 36 : ℝ)
      ≤ ∫ s in (-(P.lam / 2))..(P.lam / 2), (P.prof.eval s) ^ 2 := by
    apply intervalIntegral.integral_mono_on (by linarith [hP.lam_pos]) intervalIntegrable_const
      ((prof_sq_continuous P).intervalIntegrable _ _)
    intro s hs
    have hb := hP.profile.bulk s (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
    nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

theorem profMass_pos (hP : P.Valid) : 0 < profMass P := by
  linarith [profMass_ge hP, hP.lam_pos]

theorem vProfile_nonneg (hP : P.Valid) (t : ℝ) : 0 ≤ vProfile P t := by
  rw [vProfile_eq]
  split_ifs
  · exact div_nonneg (sq_nonneg _) (profMass_pos hP).le
  · exact le_rfl

/-- the sup bound `vProfile ≤ 1/profMass`. -/
theorem vProfile_le (hP : P.Valid) (t : ℝ) : vProfile P t ≤ 1 / profMass P := by
  rw [vProfile_eq]
  split_ifs with h
  · exact div_le_div_of_nonneg_right
      (pow_le_one₀ (by linarith [hP.profile.bulk t h]) (hP.profile.le_one t h)) (profMass_pos hP).le
  · exact (one_div_pos.mpr (profMass_pos hP)).le

theorem vProfile_eq_zero (P : ParamsQ) {t : ℝ} (ht : P.lam / 2 < |t|) : vProfile P t = 0 := by
  rw [vProfile_eq, if_neg (not_le.mpr ht)]

theorem vProfile_supp (P : ParamsQ) (t : ℝ) (h : vProfile P t ≠ 0) : |t| ≤ P.lam / 2 := by
  by_contra h'
  rw [not_le] at h'
  exact h (vProfile_eq_zero P h')

theorem vProfile_eq_indicator (P : ParamsQ) :
    vProfile P = (Icc (-(P.lam / 2)) (P.lam / 2)).indicator
      (fun t => (P.prof.eval t) ^ 2 / profMass P) := by
  funext t
  rw [vProfile_eq]
  by_cases h : |t| ≤ P.lam / 2
  · have hmem : t ∈ Icc (-(P.lam / 2)) (P.lam / 2) := abs_le.mp h
    rw [if_pos h, indicator_of_mem hmem]
  · rw [if_neg h, indicator_of_notMem]
    intro hm
    exact h (abs_le.mpr hm)

theorem vProfile_integrable (P : ParamsQ) : Integrable (vProfile P) := by
  rw [vProfile_eq_indicator, integrable_indicator_iff measurableSet_Icc]
  exact ((prof_sq_continuous P).div_const _).integrableOn_Icc

/-- `∫ vProfile = 1`. -/
theorem integral_vProfile (hP : P.Valid) : ∫ t, vProfile P t = 1 := by
  rw [vProfile_eq_indicator, integral_indicator measurableSet_Icc, integral_div,
    ← profMass_eq_setIntegral hP, div_self (profMass_pos hP).ne']

/-- **`vProfile` is admissible at `λ`**. -/
theorem vProfile_admissible (hP : P.Valid) : Admissible P.lam (vProfile P) :=
  ⟨vProfile_nonneg hP, vProfile_integrable P, integral_vProfile hP, vProfile_supp P⟩

/-! ## §D. The L¹ distance -/

/-- `λa = ∫_{core} p²·ramp²`. -/
theorem lam_mul_aQ_eq_setIntegral (hP : P.Valid) :
    P.lam * P.aQ
      = ∫ t in Icc (-(P.lam / 2)) (P.lam / 2), (P.prof.eval t) ^ 2 * (ramp P t) ^ 2 := by
  rw [hP.lam_mul_aQ_eq]
  simp_rw [phiQ_mul_LL hP, mul_pow]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro t ht
  have h : P.lam / 2 ≤ |t| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith [hP.lam_pos])]; linarith
    · rw [abs_of_pos (by linarith [hP.lam_pos])]; linarith
  rw [ramp_eq_zero hP h]; ring

/-- `profMass − λa = ∫_{core} p²(1 − ramp²)`. -/
theorem profMass_sub_eq (hP : P.Valid) :
    profMass P - P.lam * P.aQ
      = ∫ t in Icc (-(P.lam / 2)) (P.lam / 2), (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) := by
  have hI : IntegrableOn (fun t => (P.prof.eval t) ^ 2) (Icc (-(P.lam / 2)) (P.lam / 2)) :=
    (prof_sq_continuous P).integrableOn_Icc
  have hN : IntegrableOn (fun t => (P.prof.eval t) ^ 2 * (ramp P t) ^ 2)
      (Icc (-(P.lam / 2)) (P.lam / 2)) :=
    ((prof_sq_continuous P).mul ((ramp_continuous hP).pow 2)).integrableOn_Icc
  rw [profMass_eq_setIntegral hP, lam_mul_aQ_eq_setIntegral hP, ← integral_sub hI hN]
  congr 1; funext t; ring

/-- `λa ≤ profMass` (the ramp only removes mass). -/
theorem lam_mul_aQ_le_profMass (hP : P.Valid) : P.lam * P.aQ ≤ profMass P := by
  have h := profMass_sub_eq hP
  have : 0 ≤ ∫ t in Icc (-(P.lam / 2)) (P.lam / 2), (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) := by
    apply setIntegral_nonneg measurableSet_Icc
    intro t _
    exact mul_nonneg (sq_nonneg _) (by linarith [ramp_sq_le_one hP t])
  linarith

/-- **the ramp mass**: `profMass − λa ≤ 2w/ℒ` (the two strips of width `w/ℒ`, integrand `≤ 1`). -/
theorem profMass_sub_le (hP : P.Valid) : profMass P - P.lam * P.aQ ≤ 2 * (P.w / P.LL) := by
  rw [profMass_sub_eq hP]
  have hδ : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hA : MeasurableSet (Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)) := measurableSet_Ioc
  have hB : MeasurableSet (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)) := measurableSet_Ico
  have hintA : Integrable ((Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator fun _ : ℝ => (1 : ℝ)) :=
    (integrable_indicator_iff hA).mpr
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  have hintB : Integrable ((Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator
      fun _ : ℝ => (1 : ℝ)) :=
    (integrable_indicator_iff hB).mpr
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  have hnnA : ∀ t, 0 ≤ (Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator (fun _ : ℝ => (1 : ℝ)) t :=
    fun t => indicator_nonneg (fun _ _ => zero_le_one) t
  have hnnB : ∀ t, 0 ≤ (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator
      (fun _ : ℝ => (1 : ℝ)) t :=
    fun t => indicator_nonneg (fun _ _ => zero_le_one) t
  have hlhs : IntegrableOn (fun t => (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2))
      (Icc (-(P.lam / 2)) (P.lam / 2)) :=
    ((prof_sq_continuous P).mul (continuous_const.sub ((ramp_continuous hP).pow 2))).integrableOn_Icc
  calc ∫ t in Icc (-(P.lam / 2)) (P.lam / 2), (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2)
      ≤ ∫ t in Icc (-(P.lam / 2)) (P.lam / 2),
          ((Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator (fun _ : ℝ => (1 : ℝ)) t
            + (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator (fun _ : ℝ => (1 : ℝ)) t) := by
        apply setIntegral_mono_on hlhs (hintA.add hintB).integrableOn measurableSet_Icc
        intro t ht
        simp only [Pi.add_apply]
        rw [mem_Icc] at ht
        by_cases h1 : |t| ≤ P.lam / 2 - P.w / P.LL
        · rw [ramp_eq_one hP h1]
          simp only [one_pow, sub_self, mul_zero]
          exact add_nonneg (hnnA t) (hnnB t)
        · rw [not_le] at h1
          have hcore : |t| ≤ P.lam / 2 := abs_le.mpr ht
          have hlhs1 : (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) ≤ 1 := by
            have h2 := hP.profile.le_one t hcore
            have h3 := hP.profile.bulk t hcore
            have h4 := ramp_sq_le_one hP t
            have h5 : 0 ≤ ramp P t ^ 2 := sq_nonneg _
            have h6 : (P.prof.eval t) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) h2
            nlinarith
          rcases le_or_gt 0 t with ht0 | ht0
          · rw [abs_of_nonneg ht0] at h1
            have hmem : t ∈ Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2) := ⟨h1, ht.2⟩
            rw [indicator_of_mem hmem]
            linarith [hnnB t]
          · rw [abs_of_neg ht0] at h1
            have hmem : t ∈ Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL) := ⟨ht.1, by linarith⟩
            rw [indicator_of_mem hmem]
            linarith [hnnA t]
    _ = (∫ t in Icc (-(P.lam / 2)) (P.lam / 2),
            (Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator (fun _ : ℝ => (1 : ℝ)) t)
          + ∫ t in Icc (-(P.lam / 2)) (P.lam / 2),
            (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator (fun _ : ℝ => (1 : ℝ)) t :=
        integral_add hintA.integrableOn hintB.integrableOn
    _ ≤ (∫ t, (Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator (fun _ : ℝ => (1 : ℝ)) t)
          + ∫ t, (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator (fun _ : ℝ => (1 : ℝ)) t :=
        add_le_add (setIntegral_le_integral hintA (ae_of_all _ hnnA))
          (setIntegral_le_integral hintB (ae_of_all _ hnnB))
    _ = P.w / P.LL + P.w / P.LL := by
        rw [integral_indicator_const _ hA, integral_indicator_const _ hB,
          Real.volume_real_Ioc_of_le (by linarith), Real.volume_real_Ico_of_le (by linarith),
          smul_eq_mul, smul_eq_mul]
        ring
    _ = 2 * (P.w / P.LL) := by ring

/-- the pointwise comparison: `|vDesign − vProfile| ≤ ((profMass − λa)/profMass)·vDesign +
1_{core}·p²(1 − ramp²)/profMass`. -/
theorem abs_vDesign_sub_vProfile_le (hP : P.Valid) (t : ℝ) :
    |vDesign P t - vProfile P t|
      ≤ (profMass P - P.lam * P.aQ) / profMass P * vDesign P t
        + (Icc (-(P.lam / 2)) (P.lam / 2)).indicator
            (fun t => (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / profMass P) t := by
  have hN := mul_pos hP.lam_pos hP.aQ_pos
  have hI := profMass_pos hP
  have hNI := lam_mul_aQ_le_profMass hP
  by_cases ht : |t| ≤ P.lam / 2
  · have hmem : t ∈ Icc (-(P.lam / 2)) (P.lam / 2) := abs_le.mp ht
    rw [indicator_of_mem hmem, vDesign_eq_prof_ramp hP, vProfile_eq, if_pos ht]
    have hl := hP.lam_pos.ne'
    have ha := hP.aQ_pos.ne'
    have hI' := hI.ne'
    have hp2 : 0 ≤ (P.prof.eval t) ^ 2 := sq_nonneg _
    have hr2 : 0 ≤ (ramp P t) ^ 2 := sq_nonneg _
    have hr2' : (ramp P t) ^ 2 ≤ 1 := ramp_sq_le_one hP t
    have e : (P.prof.eval t) ^ 2 * (ramp P t) ^ 2 / (P.lam * P.aQ) - (P.prof.eval t) ^ 2 / profMass P
        = (profMass P - P.lam * P.aQ) / profMass P
            * ((P.prof.eval t) ^ 2 * (ramp P t) ^ 2 / (P.lam * P.aQ))
          - (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / profMass P := by
      field_simp
      ring
    rw [e]
    have ha : 0 ≤ (profMass P - P.lam * P.aQ) / profMass P
        * ((P.prof.eval t) ^ 2 * (ramp P t) ^ 2 / (P.lam * P.aQ)) :=
      mul_nonneg (div_nonneg (by linarith) hI.le) (div_nonneg (mul_nonneg hp2 hr2) hN.le)
    have hb : 0 ≤ (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / profMass P :=
      div_nonneg (mul_nonneg hp2 (by linarith)) hI.le
    calc |(profMass P - P.lam * P.aQ) / profMass P
            * ((P.prof.eval t) ^ 2 * (ramp P t) ^ 2 / (P.lam * P.aQ))
          - (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / profMass P|
        ≤ |(profMass P - P.lam * P.aQ) / profMass P
            * ((P.prof.eval t) ^ 2 * (ramp P t) ^ 2 / (P.lam * P.aQ))|
          + |(P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / profMass P| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg ha, abs_of_nonneg hb]
  · rw [not_le] at ht
    have hnm : t ∉ Icc (-(P.lam / 2)) (P.lam / 2) := fun hm => ht.not_ge (abs_le.mpr hm)
    rw [indicator_of_notMem hnm, vDesign_eq_zero hP ht.le, vProfile_eq_zero P ht]
    simp

/-- **the L¹ distance, exact form**: `‖vDesign − vProfile‖₁ ≤ 2(profMass − λa)/profMass`. -/
theorem integral_abs_vDesign_sub_vProfile_le (hP : P.Valid) :
    ∫ t, |vDesign P t - vProfile P t| ≤ 2 * (profMass P - P.lam * P.aQ) / profMass P := by
  have hint1 : Integrable (fun t => (profMass P - P.lam * P.aQ) / profMass P * vDesign P t) :=
    (vDesign_integrable hP).const_mul _
  have hint2 : Integrable ((Icc (-(P.lam / 2)) (P.lam / 2)).indicator
      fun t => (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / profMass P) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (((prof_sq_continuous P).mul (continuous_const.sub ((ramp_continuous hP).pow 2))).div_const
        _).integrableOn_Icc
  calc ∫ t, |vDesign P t - vProfile P t|
      ≤ ∫ t, ((profMass P - P.lam * P.aQ) / profMass P * vDesign P t
          + (Icc (-(P.lam / 2)) (P.lam / 2)).indicator
              (fun t => (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / profMass P) t) :=
        integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg _) (hint1.add hint2)
          (ae_of_all _ (abs_vDesign_sub_vProfile_le hP))
    _ = (profMass P - P.lam * P.aQ) / profMass P * (∫ t, vDesign P t)
          + ∫ t in Icc (-(P.lam / 2)) (P.lam / 2),
              (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / profMass P := by
        rw [integral_add hint1 hint2, integral_const_mul, integral_indicator measurableSet_Icc]
    _ = (profMass P - P.lam * P.aQ) / profMass P * 1
          + (profMass P - P.lam * P.aQ) / profMass P := by
        rw [integral_vDesign hP, integral_div, ← profMass_sub_eq hP]
    _ = 2 * (profMass P - P.lam * P.aQ) / profMass P := by ring

/-- **the L¹ distance, explicit form**: `‖vDesign − vProfile‖₁ ≤ 4(w/ℒ)/(λa)`. -/
theorem integral_abs_vDesign_sub_vProfile_le' (hP : P.Valid) :
    ∫ t, |vDesign P t - vProfile P t| ≤ 4 * (P.w / P.LL) / (P.lam * P.aQ) := by
  have h1 := integral_abs_vDesign_sub_vProfile_le hP
  have h2 := profMass_sub_le hP
  have hN := mul_pos hP.lam_pos hP.aQ_pos
  have hNI := lam_mul_aQ_le_profMass hP
  have hI := profMass_pos hP
  have hδ : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  calc ∫ t, |vDesign P t - vProfile P t|
      ≤ 2 * (profMass P - P.lam * P.aQ) / profMass P := h1
    _ ≤ 2 * (2 * (P.w / P.LL)) / profMass P := by gcongr
    _ ≤ 2 * (2 * (P.w / P.LL)) / (P.lam * P.aQ) := by gcongr
    _ = 4 * (P.w / P.LL) / (P.lam * P.aQ) := by ring

/-- `1/(λa) ≤ 4/(3λ)` (from the `Valid` floor `a ≥ 3/4`). -/
theorem one_div_lam_mul_aQ_le (hP : P.Valid) : 1 / (P.lam * P.aQ) ≤ 4 / (3 * P.lam) := by
  have hl := hP.lam_pos
  have ha := hP.a_ge
  rw [div_le_div_iff₀ (mul_pos hl hP.aQ_pos) (by positivity)]
  nlinarith

/-- the sup bound `vDesign ≤ 4/(3λ)`. -/
theorem vDesign_le_four_div (hP : P.Valid) (t : ℝ) : vDesign P t ≤ 4 / (3 * P.lam) :=
  (vDesign_le hP t).trans (one_div_lam_mul_aQ_le hP)

/-- the sup bound `vProfile ≤ 4/(3λ)` (via `λa ≤ profMass`). -/
theorem vProfile_le_four_div (hP : P.Valid) (t : ℝ) : vProfile P t ≤ 4 / (3 * P.lam) :=
  (vProfile_le hP t).trans
    ((one_div_le_one_div_of_le (mul_pos hP.lam_pos hP.aQ_pos) (lam_mul_aQ_le_profMass hP)).trans
      (one_div_lam_mul_aQ_le hP))

/-! ## §E. `B` is Lipschitz in `L¹` on bounded admissible profiles -/

/-- `|W_C(α)| ≤ (1 + C)λ` for `|α| ≤ λ`, `C ≥ 0`. -/
theorem abs_W_le {C lam α : ℝ} (hC : 0 ≤ C) (hα : |α| ≤ lam) : |W C α| ≤ (1 + C) * lam := by
  have h0 : 0 ≤ |α| := abs_nonneg α
  unfold W
  split_ifs with h
  · rw [abs_abs]; nlinarith
  · rw [abs_mul, abs_of_nonneg hC, abs_abs]; nlinarith

/-- `(t, s) ↦ W_C(s − t)·v(t)v(s)` is integrable on `ℝ²` (dominated by `(1 + C)λ·v(t)v(s)`). -/
theorem integrable_W_prod {lam C : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (hC : 0 ≤ C) :
    Integrable (fun z : ℝ × ℝ => W C (z.2 - z.1) * (v z.1 * v z.2)) (volume.prod volume) := by
  have hprod : Integrable (fun z : ℝ × ℝ => v z.1 * v z.2) (volume.prod volume) :=
    hv.integrable.mul_prod hv.integrable
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => W C (z.2 - z.1) * (v z.1 * v z.2))
      (volume.prod volume) :=
    (((W_meas C).comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable).mul
      hprod.aestronglyMeasurable
  refine Integrable.mono' (hprod.const_mul ((1 + C) * lam)) hmeas (ae_of_all _ fun z => ?_)
  have hnn : 0 ≤ v z.1 * v z.2 := mul_nonneg (hv.nonneg _) (hv.nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
  by_cases h : v z.1 * v z.2 = 0
  · rw [h, mul_zero, mul_zero]
  · have ht := abs_le.mp (hv.supp _ (left_ne_zero_of_mul h))
    have hs := abs_le.mp (hv.supp _ (right_ne_zero_of_mul h))
    have hα : |z.2 - z.1| ≤ lam := abs_le.mpr ⟨by linarith, by linarith⟩
    exact mul_le_mul_of_nonneg_right (abs_W_le hC hα) hnn

/-- `∫ W_C ψ_v = ∬ W_C(s − t) v(t) v(s)` (the Fubini bridge `kernel_psi_eq_double`, re-folded
into one product integral). -/
theorem integral_W_psi_eq_prod {lam C : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (hC : 0 ≤ C) :
    ∫ α, W C α * psi v α
      = ∫ z : ℝ × ℝ, W C (z.2 - z.1) * (v z.1 * v z.2) ∂(volume.prod volume) := by
  rw [kernel_psi_eq_double hv (W_meas C) (Mb := (1 + C) * lam) (fun α hα => abs_W_le hC hα),
    integral_prod _ (integrable_W_prod hv hC)]
  congr 1; funext t
  rw [← integral_const_mul]
  congr 1; funext s
  show v t * (W C (s - t) * v s) = W C (s - t) * (v t * v s)
  ring

/-- the pointwise kernel bound for the difference of two Gram integrands. -/
theorem abs_W_sub_le {lam C : ℝ} (hlam : 0 ≤ lam) (hC : 0 ≤ C) {v v' : ℝ → ℝ}
    (hv : Admissible lam v) (hv' : Admissible lam v') (z : ℝ × ℝ) :
    |W C (z.2 - z.1) * (v z.1 * v z.2) - W C (z.2 - z.1) * (v' z.1 * v' z.2)|
      ≤ (1 + C) * lam * (|v z.1 - v' z.1| * v z.2 + v' z.1 * |v z.2 - v' z.2|) := by
  have hM : 0 ≤ (1 + C) * lam := by positivity
  have hR : 0 ≤ |v z.1 - v' z.1| * v z.2 + v' z.1 * |v z.2 - v' z.2| :=
    add_nonneg (mul_nonneg (abs_nonneg _) (hv.nonneg _)) (mul_nonneg (hv'.nonneg _) (abs_nonneg _))
  rw [← mul_sub, abs_mul]
  by_cases h0 : v z.1 * v z.2 - v' z.1 * v' z.2 = 0
  · rw [h0, abs_zero, mul_zero]; exact mul_nonneg hM hR
  · have hts : |z.1| ≤ lam / 2 ∧ |z.2| ≤ lam / 2 := by
      by_cases h1 : v z.1 * v z.2 = 0
      · have h2 : v' z.1 * v' z.2 ≠ 0 := by
          intro h2; apply h0; rw [h1, h2]; ring
        exact ⟨hv'.supp _ (left_ne_zero_of_mul h2), hv'.supp _ (right_ne_zero_of_mul h2)⟩
      · exact ⟨hv.supp _ (left_ne_zero_of_mul h1), hv.supp _ (right_ne_zero_of_mul h1)⟩
    have h1 := abs_le.mp hts.1
    have h2 := abs_le.mp hts.2
    have hα : |z.2 - z.1| ≤ lam := abs_le.mpr ⟨by linarith, by linarith⟩
    have hW := abs_W_le hC hα
    have hdiff : |v z.1 * v z.2 - v' z.1 * v' z.2|
        ≤ |v z.1 - v' z.1| * v z.2 + v' z.1 * |v z.2 - v' z.2| := by
      have e : v z.1 * v z.2 - v' z.1 * v' z.2
          = (v z.1 - v' z.1) * v z.2 + v' z.1 * (v z.2 - v' z.2) := by ring
      rw [e]
      calc |(v z.1 - v' z.1) * v z.2 + v' z.1 * (v z.2 - v' z.2)|
          ≤ |(v z.1 - v' z.1) * v z.2| + |v' z.1 * (v z.2 - v' z.2)| := abs_add_le _ _
        _ = |v z.1 - v' z.1| * v z.2 + v' z.1 * |v z.2 - v' z.2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hv.nonneg _), abs_of_nonneg (hv'.nonneg _)]
    exact mul_le_mul hW hdiff (abs_nonneg _) hM

/-- **`B` is Lipschitz in `L¹` on uniformly bounded admissible profiles**:
`|B C v − B C v′| ≤ (‖v‖∞ + ‖v′‖∞ + 2(1 + C)λ)·‖v − v′‖₁`. -/
theorem abs_B_sub_B_le {lam C : ℝ} (hlam : 0 ≤ lam) (hC : 0 ≤ C) {v v' : ℝ → ℝ}
    (hv : Admissible lam v) (hv' : Admissible lam v') {Mv Mv' : ℝ}
    (hMv : ∀ t, v t ≤ Mv) (hMv' : ∀ t, v' t ≤ Mv') :
    |B C v - B C v'| ≤ (Mv + Mv' + 2 * ((1 + C) * lam)) * ∫ t, |v t - v' t| := by
  have hint_sub : Integrable (fun t => |v t - v' t|) := (hv.integrable.sub hv'.integrable).abs
  have hvv : Integrable (fun t => v t * v t) :=
    hv.integrable.bdd_mul hv.integrable.aestronglyMeasurable (c := Mv)
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hv.nonneg t)]; exact hMv t)
  have hvv' : Integrable (fun t => v' t * v' t) :=
    hv'.integrable.bdd_mul hv'.integrable.aestronglyMeasurable (c := Mv')
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hv'.nonneg t)]; exact hMv' t)
  -- Term 1: `ψ_v(0) − ψ_{v′}(0) = ∫ (v − v′)(v + v′)`
  have h1 : |psi v 0 - psi v' 0| ≤ (Mv + Mv') * ∫ t, |v t - v' t| := by
    have e0 : psi v 0 = ∫ t, v t * v t := by simp only [psi, sub_zero]
    have e0' : psi v' 0 = ∫ t, v' t * v' t := by simp only [psi, sub_zero]
    rw [e0, e0', ← integral_sub hvv hvv']
    calc |∫ t, (v t * v t - v' t * v' t)| ≤ ∫ t, |v t * v t - v' t * v' t| := by
          have := norm_integral_le_integral_norm (μ := volume) (fun t => v t * v t - v' t * v' t)
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∫ t, (Mv + Mv') * |v t - v' t| := by
          refine integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg _) (hint_sub.const_mul _)
            (ae_of_all _ fun t => ?_)
          show |v t * v t - v' t * v' t| ≤ (Mv + Mv') * |v t - v' t|
          have e : v t * v t - v' t * v' t = (v t + v' t) * (v t - v' t) := by ring
          rw [e, abs_mul, abs_of_nonneg (add_nonneg (hv.nonneg t) (hv'.nonneg t))]
          exact mul_le_mul_of_nonneg_right (add_le_add (hMv t) (hMv' t)) (abs_nonneg _)
      _ = (Mv + Mv') * ∫ t, |v t - v' t| := integral_const_mul _ _
  -- Term 2: `∫ W(ψ_v − ψ_{v′}) = ∬ W(s − t)[v(t)v(s) − v′(t)v′(s)]`
  have h2 : |(∫ α, W C α * psi v α) - ∫ α, W C α * psi v' α|
      ≤ 2 * ((1 + C) * lam) * ∫ t, |v t - v' t| := by
    rw [integral_W_psi_eq_prod hv hC, integral_W_psi_eq_prod hv' hC]
    have hF := integrable_W_prod hv hC
    have hF' := integrable_W_prod hv' hC
    rw [← integral_sub hF hF']
    have hG1 : Integrable (fun z : ℝ × ℝ => |v z.1 - v' z.1| * v z.2) (volume.prod volume) :=
      hint_sub.mul_prod hv.integrable
    have hG2 : Integrable (fun z : ℝ × ℝ => v' z.1 * |v z.2 - v' z.2|) (volume.prod volume) :=
      hv'.integrable.mul_prod hint_sub
    have eG1 : ∫ z : ℝ × ℝ, |v z.1 - v' z.1| * v z.2 ∂(volume.prod volume)
        = (∫ t, |v t - v' t|) * 1 := by
      rw [← hv.mass]; exact integral_prod_mul (fun t => |v t - v' t|) v
    have eG2 : ∫ z : ℝ × ℝ, v' z.1 * |v z.2 - v' z.2| ∂(volume.prod volume)
        = 1 * ∫ t, |v t - v' t| := by
      rw [← hv'.mass]; exact integral_prod_mul v' (fun t => |v t - v' t|)
    calc |∫ z : ℝ × ℝ, (W C (z.2 - z.1) * (v z.1 * v z.2)
            - W C (z.2 - z.1) * (v' z.1 * v' z.2)) ∂(volume.prod volume)|
        ≤ ∫ z : ℝ × ℝ, |W C (z.2 - z.1) * (v z.1 * v z.2)
            - W C (z.2 - z.1) * (v' z.1 * v' z.2)| ∂(volume.prod volume) := by
          have := norm_integral_le_integral_norm (μ := volume.prod volume)
            (fun z : ℝ × ℝ => W C (z.2 - z.1) * (v z.1 * v z.2)
              - W C (z.2 - z.1) * (v' z.1 * v' z.2))
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∫ z : ℝ × ℝ, (1 + C) * lam * (|v z.1 - v' z.1| * v z.2 + v' z.1 * |v z.2 - v' z.2|)
            ∂(volume.prod volume) :=
          integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) ((hG1.add hG2).const_mul _)
            (ae_of_all _ fun z => abs_W_sub_le hlam hC hv hv' z)
      _ = (1 + C) * lam * ((∫ t, |v t - v' t|) * 1 + 1 * ∫ t, |v t - v' t|) := by
          rw [integral_const_mul, integral_add hG1 hG2, eG1, eG2]
      _ = 2 * ((1 + C) * lam) * ∫ t, |v t - v' t| := by ring
  have e : B C v - B C v'
      = (psi v 0 - psi v' 0) + ((∫ α, W C α * psi v α) - ∫ α, W C α * psi v' α) := by
    unfold B; ring
  rw [e]
  calc |(psi v 0 - psi v' 0) + ((∫ α, W C α * psi v α) - ∫ α, W C α * psi v' α)|
      ≤ |psi v 0 - psi v' 0| + |(∫ α, W C α * psi v α) - ∫ α, W C α * psi v' α| := abs_add_le _ _
    _ ≤ (Mv + Mv') * (∫ t, |v t - v' t|) + 2 * ((1 + C) * lam) * ∫ t, |v t - v' t| :=
        add_le_add h1 h2
    _ = _ := by ring

/-! ## §F. Assembly -/

/-- the raw comparison: `B(v_design) − B(v_profile) ≤ (2/(λa) + 2(1 + C)λ)·(4(w/ℒ)/(λa))`. -/
theorem B_vDesign_sub_B_vProfile_le {C : ℝ} (hC : 0 ≤ C) (hP : P.Valid) :
    B C (vDesign P) - B C (vProfile P)
      ≤ (2 / (P.lam * P.aQ) + 2 * ((1 + C) * P.lam)) * (4 * (P.w / P.LL) / (P.lam * P.aQ)) := by
  have hN := mul_pos hP.lam_pos hP.aQ_pos
  have hI := profMass_pos hP
  have hNI := lam_mul_aQ_le_profMass hP
  have hLip := abs_B_sub_B_le hP.lam_pos.le hC (vDesign_admissible hP) (vProfile_admissible hP)
    (vDesign_le hP) (vProfile_le hP)
  have hD := integral_abs_vDesign_sub_vProfile_le' hP
  have h1 : 1 / profMass P ≤ 1 / (P.lam * P.aQ) := one_div_le_one_div_of_le hN hNI
  have hD0 : 0 ≤ ∫ t, |vDesign P t - vProfile P t| := integral_nonneg fun t => abs_nonneg _
  calc B C (vDesign P) - B C (vProfile P) ≤ |B C (vDesign P) - B C (vProfile P)| := le_abs_self _
    _ ≤ (1 / (P.lam * P.aQ) + 1 / profMass P + 2 * ((1 + C) * P.lam))
          * ∫ t, |vDesign P t - vProfile P t| := hLip
    _ ≤ (1 / (P.lam * P.aQ) + 1 / (P.lam * P.aQ) + 2 * ((1 + C) * P.lam))
          * (4 * (P.w / P.LL) / (P.lam * P.aQ)) :=
        mul_le_mul (by linarith) hD hD0 (by
          have h5 := (one_div_pos.mpr hN).le
          have h6 : 0 ≤ 2 * ((1 + C) * P.lam) :=
            mul_nonneg (by norm_num) (mul_nonneg (by linarith) hP.lam_pos.le)
          linarith)
    _ = _ := by ring

/-- **the §11 link with an explicit constant, under `Valid` alone**:
`B(v_design) ≤ B(v_profile) + (128/(9λ²) + (32/3)(1 + C))·(w/ℒ)`. -/
theorem B_vDesign_le_explicit {C : ℝ} (hC : 0 ≤ C) (hP : P.Valid) :
    B C (vDesign P)
      ≤ B C (vProfile P) + (128 / (9 * P.lam ^ 2) + 32 / 3 * (1 + C)) * (P.w / P.LL) := by
  have h := B_vDesign_sub_B_vProfile_le hC hP
  have ha := hP.a_ge
  have hl := hP.lam_pos
  have hδ : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hNpos : 0 < P.lam * P.aQ := mul_pos hl hP.aQ_pos
  have hu0 : 0 ≤ 1 / (P.lam * P.aQ) := by positivity
  have hus : 1 / (P.lam * P.aQ) ≤ 4 / (3 * P.lam) := one_div_lam_mul_aQ_le hP
  have e : (2 / (P.lam * P.aQ) + 2 * ((1 + C) * P.lam)) * (4 * (P.w / P.LL) / (P.lam * P.aQ))
      = 8 * (P.w / P.LL) * (1 / (P.lam * P.aQ)) ^ 2
        + 8 * (1 + C) * P.lam * (P.w / P.LL) * (1 / (P.lam * P.aQ)) := by ring
  have e2 : (128 / (9 * P.lam ^ 2) + 32 / 3 * (1 + C)) * (P.w / P.LL)
      = 8 * (P.w / P.LL) * (4 / (3 * P.lam)) ^ 2
        + 8 * (1 + C) * P.lam * (P.w / P.LL) * (4 / (3 * P.lam)) := by
    field_simp
    ring
  rw [e] at h
  rw [e2]
  have h3 : (1 / (P.lam * P.aQ)) ^ 2 ≤ (4 / (3 * P.lam)) ^ 2 := pow_le_pow_left₀ hu0 hus 2
  have h4 : 8 * (P.w / P.LL) * (1 / (P.lam * P.aQ)) ^ 2
      ≤ 8 * (P.w / P.LL) * (4 / (3 * P.lam)) ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : 8 * (1 + C) * P.lam * (P.w / P.LL) * (1 / (P.lam * P.aQ))
      ≤ 8 * (1 + C) * P.lam * (P.w / P.LL) * (4 / (3 * P.lam)) :=
    mul_le_mul_of_nonneg_left hus (by positivity)
  linarith

/-- **THE §11 LINK, with the bandwidth floor `1 ≤ λ`**: for every valid design point with
`8w ≤ L` and `λ ≥ 1`, `B(v_design) ≤ B(v_profile) + rampCost C P` (constant 64; the proof
delivers `128/9 + 32/3 < 25`).

The floor `1 ≤ λ` is NECESSARY for a bound of the shape `K(1 + C)(w/ℒ)`: at `prof = 1`,
`8w = L` and `λ → 0` one has `ψ_design(0) − ψ_profile(0) ≥ 3(1 − c₂)²/(16λ)` with
`c₂ = ∫₀¹ ϱ² < 1`, while `rampCost ≤ 8(1 + C)λ`, so the unconditional `ProfileRampLink` is
FALSE. -/
theorem profileRampLink_of_one_le_lam (C : ℝ) (P : ParamsQ) (hC : 0 ≤ C) (hP : P.Valid)
    (_hw : 8 * P.w ≤ P.LB) (hlam : 1 ≤ P.lam) :
    B C (vDesign P) ≤ B C (vProfile P) + rampCost C P := by
  have h := B_vDesign_le_explicit hC hP
  have hδ : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  unfold rampCost
  have h1 : 128 / (9 * P.lam ^ 2) ≤ 128 / 9 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have h2 : (128 / (9 * P.lam ^ 2) + 32 / 3 * (1 + C)) * (P.w / P.LL)
      ≤ 64 * (1 + C) * (P.w / P.LL) := by
    apply mul_le_mul_of_nonneg_right _ hδ
    nlinarith
  linarith

/-- the link as a `Prop`, with the bandwidth floor. -/
def ProfileRampLink' : Prop :=
  ∀ (C : ℝ) (P : ParamsQ), 0 ≤ C → P.Valid → 8 * P.w ≤ P.LB → 1 ≤ P.lam →
    B C (vDesign P) ≤ B C (vProfile P) + rampCost C P

theorem profileRampLink' : ProfileRampLink' := profileRampLink_of_one_le_lam

/-- **The §11 link of `PayoffSmooth.lean`, `ProfileRampLink`, PROVED**. The `Prop`
carries the bandwidth floor `1 ≤ P.lam` — NECESSARY: without it the bound is FALSE (counterexample:
`prof = 1`, `w = 1`, `8w = L`, `λ → 0`, where `ψ_design(0) − ψ_profile(0) ≥ 3(1−c₂)²/(16λ)` outruns
any `K(1+C)(w/ℒ) ≤ 8K(1+C)λ`); the design of record has `λ = λ* > 1`. The constant actually achieved
is `(128/(9λ²) + (32/3)(1+C))·(w/ℒ) ≤ (224/9)(1+C)(w/ℒ)` at `λ ≥ 1` (`B_vDesign_le_explicit`), so
`rampCost`'s `64` has room. -/
theorem profileRampLink : ProfileRampLink := fun C P hC hP hw hlam =>
  profileRampLink_of_one_le_lam C P hC hP hw hlam

end Payoff
end ZetaQ

end
