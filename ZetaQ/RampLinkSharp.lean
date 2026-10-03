/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/RampLinkSharp.lean (receipt: `audit/RampLinkSharp_REPORT.md`) — a SHARP §11 link at the design of record:
`B(v_design) ≤ B(v_profile) + K_F·(w/L)` with `K_F ≤ 3` for both families.

Route (the "first-order" route, made exact): with `c := profMass/(λa) ≥ 1` and
`u := c·v_profile − v_design ≥ 0` (the ramp REMOVES mass; `u` lives on the two strips, `u ≤ s₀/(λa)`),
`B` is a nonnegative quadratic form `Q(v,v)`, so
  `B(v_design) − B(v_profile) = (c² − 1)·B(v_profile) − c·[Q(v′,u) + Q(u,v′)] + Q(u,u)`
and the cross term is `≤ 0`:
  `B(v_design) − B(v_profile) ≤ (c² − 1)·B(v_profile) + (s₀/(λa))·(c − 1) + (1 + C)λ(c − 1)²`
with `c − 1 = (profMass − λa)/(λa) ≤ 2(w/ℒ)·s₀/(λa)`, `s₀ = sup_strip p² = p(λ/2 − 1/100)²`
(`≈ 0.064` / `0.086`), and `B(v_profile) ≤ 1/profMass + 1 + Cλ·(∫_{|t| ≥ 1 − λ/2} v_profile)²`.
-/
import ZetaQ.RampLink
import ZetaQ.DesignProfile
import ZetaQ.Budget

noncomputable section

open Real MeasureTheory Set

namespace ZetaQ
namespace Payoff

variable {P : ParamsQ}

/-! ## §1. `W ≥ 0`, `B ≥ 0`, and the quadratic expansion -/

theorem W_nonneg' (C : ℝ) (hC : 0 ≤ C) (α : ℝ) : 0 ≤ W C α := by
  unfold W
  split_ifs
  · exact abs_nonneg _
  · exact mul_nonneg hC (abs_nonneg _)

/-- `B C v ≥ 0` for admissible `v` and `C ≥ 0` (both pieces of the Gram form are nonnegative). -/
theorem B_nonneg' {lam C : ℝ} (hC : 0 ≤ C) {v : ℝ → ℝ} (hv : Admissible lam v) :
    0 ≤ B C v := by
  unfold B
  refine add_nonneg (psi_nonneg' hv 0) ?_
  rw [integral_W_psi_eq_prod hv hC]
  exact integral_nonneg fun z =>
    mul_nonneg (W_nonneg' C hC _) (mul_nonneg (hv.nonneg _) (hv.nonneg _))

/-- **the quadratic expansion.** If `v = c·v′ − u` with `u ≥ 0`, `u ≤ Mu`, `v, v′` admissible at
`λ` and bounded, then
`B C v − B C v′ ≤ (c² − 1)·B C v′ + Mu·(c − 1) + (1 + C)λ·(c − 1)²`
(the dropped cross term `−c[Q(v′,u) + Q(u,v′)]` is `≤ 0`; `∫u = c − 1`). -/
theorem B_sub_B_le_quad {lam C : ℝ} (hC : 0 ≤ C) {v v' : ℝ → ℝ}
    (hv : Admissible lam v) (hv' : Admissible lam v') {Mv Mv' : ℝ}
    (hMv : ∀ t, v t ≤ Mv) (hMv' : ∀ t, v' t ≤ Mv')
    {c Mu : ℝ} (hc : 0 ≤ c)
    (hu0 : ∀ t, 0 ≤ c * v' t - v t) (hu1 : ∀ t, c * v' t - v t ≤ Mu) :
    B C v - B C v'
      ≤ (c ^ 2 - 1) * B C v' + Mu * (c - 1) + (1 + C) * lam * (c - 1) ^ 2 := by
  set u : ℝ → ℝ := fun t => c * v' t - v t with hu_def
  have hu_int : Integrable u := (hv'.integrable.const_mul c).sub hv.integrable
  have hu_mass : ∫ t, u t = c - 1 := by
    simp only [hu_def]
    rw [integral_sub (hv'.integrable.const_mul c) hv.integrable, integral_const_mul, hv'.mass,
      hv.mass, mul_one]
  have hu_supp : ∀ t, u t ≠ 0 → |t| ≤ lam / 2 := by
    intro t ht
    by_contra h
    rw [not_le] at h
    apply ht
    have h1 : v t = 0 := by
      by_contra hv0; exact absurd (hv.supp t hv0) (not_le.mpr h)
    have h2 : v' t = 0 := by
      by_contra hv0; exact absurd (hv'.supp t hv0) (not_le.mpr h)
    simp only [hu_def, h1, h2, mul_zero, sub_zero]
  have hvv : Integrable (fun t => v t * v t) :=
    hv.integrable.bdd_mul hv.integrable.aestronglyMeasurable (c := Mv)
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hv.nonneg t)]; exact hMv t)
  have hvv' : Integrable (fun t => v' t * v' t) :=
    hv'.integrable.bdd_mul hv'.integrable.aestronglyMeasurable (c := Mv')
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hv'.nonneg t)]; exact hMv' t)
  -- Term 1: `ψ_v(0) − ψ_{v′}(0) = ∫ (v² − v′²) ≤ (c² − 1)∫v′² + ∫u² ≤ (c² − 1)ψ_{v′}(0) + Mu·∫u`
  have h1 : psi v 0 - psi v' 0 ≤ (c ^ 2 - 1) * psi v' 0 + Mu * (c - 1) := by
    have e0 : psi v 0 = ∫ t, v t * v t := by simp only [psi, sub_zero]
    have e0' : psi v' 0 = ∫ t, v' t * v' t := by simp only [psi, sub_zero]
    rw [e0, e0']
    have hptw : ∀ t, v t * v t - v' t * v' t ≤ (c ^ 2 - 1) * (v' t * v' t) + Mu * u t := by
      intro t
      have hvt : v t = c * v' t - u t := by simp only [hu_def]; ring
      have hu0t : 0 ≤ u t := hu0 t
      have hu1t : u t ≤ Mu := hu1 t
      have hv't := hv'.nonneg t
      have key : v t * v t - v' t * v' t
          = (c ^ 2 - 1) * (v' t * v' t) - 2 * (c * (v' t * u t)) + u t * u t := by
        rw [hvt]; ring
      rw [key]
      have hA : 0 ≤ c * (v' t * u t) := mul_nonneg hc (mul_nonneg hv't hu0t)
      have hB : u t * u t ≤ Mu * u t := mul_le_mul_of_nonneg_right hu1t hu0t
      linarith
    have hint_rhs : Integrable (fun t => (c ^ 2 - 1) * (v' t * v' t) + Mu * u t) :=
      (hvv'.const_mul _).add (hu_int.const_mul _)
    calc (∫ t, v t * v t) - ∫ t, v' t * v' t
        = ∫ t, (v t * v t - v' t * v' t) := (integral_sub hvv hvv').symm
      _ ≤ ∫ t, ((c ^ 2 - 1) * (v' t * v' t) + Mu * u t) :=
          integral_mono (hvv.sub hvv') hint_rhs hptw
      _ = (c ^ 2 - 1) * (∫ t, v' t * v' t) + Mu * (c - 1) := by
          rw [integral_add (hvv'.const_mul _) (hu_int.const_mul _), integral_const_mul,
            integral_const_mul, hu_mass]
  -- Term 2: `∬ W(s−t)[v(t)v(s) − v′(t)v′(s)] ≤ (c² − 1)∬W v′v′ + (1 + C)λ(∫u)²`
  have h2 : (∫ α, W C α * psi v α) - ∫ α, W C α * psi v' α
      ≤ (c ^ 2 - 1) * (∫ α, W C α * psi v' α) + (1 + C) * lam * (c - 1) ^ 2 := by
    rw [integral_W_psi_eq_prod hv hC, integral_W_psi_eq_prod hv' hC]
    have hF := integrable_W_prod hv hC
    have hF' := integrable_W_prod hv' hC
    have hG : Integrable (fun z : ℝ × ℝ => u z.1 * u z.2) (volume.prod volume) :=
      hu_int.mul_prod hu_int
    have eG : ∫ z : ℝ × ℝ, u z.1 * u z.2 ∂(volume.prod volume) = (c - 1) * (c - 1) := by
      rw [← hu_mass]; exact integral_prod_mul u u
    have hptw : ∀ z : ℝ × ℝ,
        W C (z.2 - z.1) * (v z.1 * v z.2) - W C (z.2 - z.1) * (v' z.1 * v' z.2)
          ≤ (c ^ 2 - 1) * (W C (z.2 - z.1) * (v' z.1 * v' z.2))
            + (1 + C) * lam * (u z.1 * u z.2) := by
      intro z
      have hW0 : 0 ≤ W C (z.2 - z.1) := W_nonneg' C hC _
      have hv1 : v z.1 = c * v' z.1 - u z.1 := by simp only [hu_def]; ring
      have hv2 : v z.2 = c * v' z.2 - u z.2 := by simp only [hu_def]; ring
      have hWuu : W C (z.2 - z.1) * (u z.1 * u z.2) ≤ (1 + C) * lam * (u z.1 * u z.2) := by
        by_cases h0 : u z.1 * u z.2 = 0
        · rw [h0, mul_zero, mul_zero]
        · have ht := abs_le.mp (hu_supp _ (left_ne_zero_of_mul h0))
          have hs := abs_le.mp (hu_supp _ (right_ne_zero_of_mul h0))
          have hα : |z.2 - z.1| ≤ lam := abs_le.mpr ⟨by linarith, by linarith⟩
          have hW := abs_W_le hC hα
          have huu : 0 ≤ u z.1 * u z.2 := mul_nonneg (hu0 _) (hu0 _)
          calc W C (z.2 - z.1) * (u z.1 * u z.2)
              ≤ |W C (z.2 - z.1)| * (u z.1 * u z.2) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) huu
            _ ≤ (1 + C) * lam * (u z.1 * u z.2) := mul_le_mul_of_nonneg_right hW huu
      have key : W C (z.2 - z.1) * (v z.1 * v z.2) - W C (z.2 - z.1) * (v' z.1 * v' z.2)
          = (c ^ 2 - 1) * (W C (z.2 - z.1) * (v' z.1 * v' z.2))
            - W C (z.2 - z.1) * (c * (v' z.1 * u z.2))
            - W C (z.2 - z.1) * (c * (u z.1 * v' z.2))
            + W C (z.2 - z.1) * (u z.1 * u z.2) := by
        rw [hv1, hv2]; ring
      rw [key]
      have hA : 0 ≤ W C (z.2 - z.1) * (c * (v' z.1 * u z.2)) :=
        mul_nonneg hW0 (mul_nonneg hc (mul_nonneg (hv'.nonneg _) (hu0 _)))
      have hB : 0 ≤ W C (z.2 - z.1) * (c * (u z.1 * v' z.2)) :=
        mul_nonneg hW0 (mul_nonneg hc (mul_nonneg (hu0 _) (hv'.nonneg _)))
      linarith
    have hint_rhs : Integrable (fun z : ℝ × ℝ =>
        (c ^ 2 - 1) * (W C (z.2 - z.1) * (v' z.1 * v' z.2)) + (1 + C) * lam * (u z.1 * u z.2))
        (volume.prod volume) :=
      (hF'.const_mul _).add (hG.const_mul _)
    calc (∫ z : ℝ × ℝ, W C (z.2 - z.1) * (v z.1 * v z.2) ∂(volume.prod volume))
          - ∫ z : ℝ × ℝ, W C (z.2 - z.1) * (v' z.1 * v' z.2) ∂(volume.prod volume)
        = ∫ z : ℝ × ℝ, (W C (z.2 - z.1) * (v z.1 * v z.2)
            - W C (z.2 - z.1) * (v' z.1 * v' z.2)) ∂(volume.prod volume) :=
          (integral_sub hF hF').symm
      _ ≤ ∫ z : ℝ × ℝ, ((c ^ 2 - 1) * (W C (z.2 - z.1) * (v' z.1 * v' z.2))
            + (1 + C) * lam * (u z.1 * u z.2)) ∂(volume.prod volume) :=
          integral_mono (hF.sub hF') hint_rhs hptw
      _ = (c ^ 2 - 1) * (∫ z : ℝ × ℝ, W C (z.2 - z.1) * (v' z.1 * v' z.2) ∂(volume.prod volume))
            + (1 + C) * lam * (c - 1) ^ 2 := by
          rw [integral_add (hF'.const_mul _) (hG.const_mul _), integral_const_mul,
            integral_const_mul, eG]
          ring
  have e : B C v - B C v'
      = (psi v 0 - psi v' 0) + ((∫ α, W C α * psi v α) - ∫ α, W C α * psi v' α) := by
    unfold B; ring
  have eB : B C v' = psi v' 0 + ∫ α, W C α * psi v' α := rfl
  rw [e, eB]
  calc (psi v 0 - psi v' 0) + ((∫ α, W C α * psi v α) - ∫ α, W C α * psi v' α)
      ≤ ((c ^ 2 - 1) * psi v' 0 + Mu * (c - 1))
        + ((c ^ 2 - 1) * (∫ α, W C α * psi v' α) + (1 + C) * lam * (c - 1) ^ 2) :=
        add_le_add h1 h2
    _ = _ := by ring

/-! ## §2. The strip bound `p(t)² ≤ p(λ/2 − 1/100)²` on `λ/2 − 1/100 ≤ |t| ≤ λ/2` -/

/-- `p` is even and nonincreasing on `[0, λ/2]` with `p ≥ 1/6 > 0`, so on the outer strip
`λ/2 − 1/100 ≤ |t| ≤ λ/2` one has `p(t)² ≤ p(λ/2 − 1/100)²`. -/
theorem prof_sq_le_edge (hP : P.Valid) (hlam : 1 / 50 ≤ P.lam) {t : ℝ}
    (ht1 : P.lam / 2 - 1 / 100 ≤ |t|) (ht2 : |t| ≤ P.lam / 2) :
    (P.prof.eval t) ^ 2 ≤ (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 := by
  have hev : P.prof.eval t = P.prof.eval |t| := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hP.profile.even]
  rw [hev]
  have hmem1 : P.lam / 2 - 1 / 100 ∈ Icc 0 (P.lam / 2) := ⟨by linarith, by linarith⟩
  have hmem2 : |t| ∈ Icc 0 (P.lam / 2) := ⟨abs_nonneg t, ht2⟩
  have hanti := hP.profile.antitone hmem1 hmem2 ht1
  simp only at hanti
  have hpos : 0 ≤ P.prof.eval |t| := by
    have := hP.profile.bulk |t| (by rw [abs_abs]; exact ht2)
    linarith
  exact pow_le_pow_left₀ hpos hanti 2

/-! ## §3. The ramp mass with the strip bound: `profMass − λa ≤ 2(w/ℒ)·s₀` -/

/-- **the ramp mass, refined**: if `p² ≤ s₀` on the two strips `λ/2 − w/ℒ < |t| ≤ λ/2`, then
`profMass − λa = ∫_{core} p²(1 − ramp²) ≤ 2(w/ℒ)·s₀` (`RampLink.profMass_sub_le` is the case
`s₀ = 1`). -/
theorem profMass_sub_le_of_strip (hP : P.Valid) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    (hs : ∀ t, P.lam / 2 - P.w / P.LL < |t| → |t| ≤ P.lam / 2 → (P.prof.eval t) ^ 2 ≤ s₀) :
    profMass P - P.lam * P.aQ ≤ 2 * (P.w / P.LL) * s₀ := by
  rw [profMass_sub_eq hP]
  have hδ : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hA : MeasurableSet (Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)) := measurableSet_Ioc
  have hB : MeasurableSet (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)) := measurableSet_Ico
  have hintA : Integrable ((Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator
      fun _ : ℝ => s₀) :=
    (integrable_indicator_iff hA).mpr
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  have hintB : Integrable ((Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator
      fun _ : ℝ => s₀) :=
    (integrable_indicator_iff hB).mpr
      (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  have hnnA : ∀ t, 0 ≤ (Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator (fun _ : ℝ => s₀) t :=
    fun t => indicator_nonneg (fun _ _ => hs0) t
  have hnnB : ∀ t, 0 ≤ (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator
      (fun _ : ℝ => s₀) t :=
    fun t => indicator_nonneg (fun _ _ => hs0) t
  have hlhs : IntegrableOn (fun t => (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2))
      (Icc (-(P.lam / 2)) (P.lam / 2)) :=
    ((prof_sq_continuous P).mul (continuous_const.sub ((ramp_continuous hP).pow 2))).integrableOn_Icc
  calc ∫ t in Icc (-(P.lam / 2)) (P.lam / 2), (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2)
      ≤ ∫ t in Icc (-(P.lam / 2)) (P.lam / 2),
          ((Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator (fun _ : ℝ => s₀) t
            + (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator (fun _ : ℝ => s₀) t) := by
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
          have hlhs1 : (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) ≤ s₀ := by
            have h2 := hs t h1 hcore
            have h4 := ramp_sq_le_one hP t
            have h5 : 0 ≤ ramp P t ^ 2 := sq_nonneg _
            have hp2 : 0 ≤ (P.prof.eval t) ^ 2 := sq_nonneg _
            calc (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) ≤ (P.prof.eval t) ^ 2 * 1 :=
                  mul_le_mul_of_nonneg_left (by linarith) hp2
              _ ≤ s₀ := by linarith
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
            (Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator (fun _ : ℝ => s₀) t)
          + ∫ t in Icc (-(P.lam / 2)) (P.lam / 2),
            (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator (fun _ : ℝ => s₀) t :=
        integral_add hintA.integrableOn hintB.integrableOn
    _ ≤ (∫ t, (Ioc (P.lam / 2 - P.w / P.LL) (P.lam / 2)).indicator (fun _ : ℝ => s₀) t)
          + ∫ t, (Ico (-(P.lam / 2)) (-(P.lam / 2) + P.w / P.LL)).indicator (fun _ : ℝ => s₀) t :=
        add_le_add (setIntegral_le_integral hintA (ae_of_all _ hnnA))
          (setIntegral_le_integral hintB (ae_of_all _ hnnB))
    _ = P.w / P.LL * s₀ + P.w / P.LL * s₀ := by
        rw [integral_indicator_const _ hA, integral_indicator_const _ hB,
          Real.volume_real_Ioc_of_le (by linarith), Real.volume_real_Ico_of_le (by linarith),
          smul_eq_mul, smul_eq_mul]
        ring
    _ = 2 * (P.w / P.LL) * s₀ := by ring

/-! ## §4. `u := c·vProfile − vDesign`, `c = profMass/(λa)`: `u = 1_core·p²(1 − ramp²)/(λa)` -/

/-- pointwise: `c·vProfile − vDesign = 1_core·p²(1 − ramp²)/(λa)` with `c = profMass/(λa)`. -/
theorem cv_sub_v_eq (hP : P.Valid) (t : ℝ) :
    profMass P / (P.lam * P.aQ) * vProfile P t - vDesign P t
      = (Icc (-(P.lam / 2)) (P.lam / 2)).indicator
          (fun t => (P.prof.eval t) ^ 2 * (1 - (ramp P t) ^ 2) / (P.lam * P.aQ)) t := by
  have hN := mul_pos hP.lam_pos hP.aQ_pos
  have hI := profMass_pos hP
  by_cases ht : |t| ≤ P.lam / 2
  · have hmem : t ∈ Icc (-(P.lam / 2)) (P.lam / 2) := abs_le.mp ht
    rw [indicator_of_mem hmem, vProfile_eq, if_pos ht, vDesign_eq_prof_ramp hP]
    have h1 := hN.ne'
    have h2 := hI.ne'
    field_simp
  · rw [not_le] at ht
    have hnm : t ∉ Icc (-(P.lam / 2)) (P.lam / 2) := fun hm => ht.not_ge (abs_le.mpr hm)
    rw [indicator_of_notMem hnm, vDesign_eq_zero hP ht.le, vProfile_eq_zero P ht]
    ring

theorem cv_sub_v_nonneg (hP : P.Valid) (t : ℝ) :
    0 ≤ profMass P / (P.lam * P.aQ) * vProfile P t - vDesign P t := by
  rw [cv_sub_v_eq hP]
  apply indicator_nonneg
  intro s _
  exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith [ramp_sq_le_one hP s]))
    (mul_pos hP.lam_pos hP.aQ_pos).le

/-- `u ≤ s₀/(λa)`: `u` vanishes on the plateau (`ramp = 1`) and off the core, and on the strips
`p² ≤ s₀`, `0 ≤ 1 − ramp² ≤ 1`. -/
theorem cv_sub_v_le (hP : P.Valid) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    (hs : ∀ t, P.lam / 2 - P.w / P.LL < |t| → |t| ≤ P.lam / 2 → (P.prof.eval t) ^ 2 ≤ s₀)
    (t : ℝ) :
    profMass P / (P.lam * P.aQ) * vProfile P t - vDesign P t ≤ s₀ / (P.lam * P.aQ) := by
  rw [cv_sub_v_eq hP]
  have hN := mul_pos hP.lam_pos hP.aQ_pos
  have hR : 0 ≤ s₀ / (P.lam * P.aQ) := div_nonneg hs0 hN.le
  by_cases hmem : t ∈ Icc (-(P.lam / 2)) (P.lam / 2)
  · rw [indicator_of_mem hmem]
    have hcore : |t| ≤ P.lam / 2 := abs_le.mpr hmem
    apply div_le_div_of_nonneg_right _ hN.le
    by_cases h1 : |t| ≤ P.lam / 2 - P.w / P.LL
    · rw [ramp_eq_one hP h1]; simp only [one_pow, sub_self, mul_zero]; exact hs0
    · rw [not_le] at h1
      have h2 := hs t h1 hcore
      have h4 := ramp_sq_le_one hP t
      have h5 : 0 ≤ ramp P t ^ 2 := sq_nonneg _
      have hp2 : 0 ≤ (P.prof.eval t) ^ 2 := sq_nonneg _
      calc (P.prof.eval t) ^ 2 * (1 - ramp P t ^ 2) ≤ (P.prof.eval t) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) hp2
        _ ≤ s₀ := by linarith
  · rw [indicator_of_notMem hmem]; exact hR

/-- **the expansion at the design profiles**: with `c = profMass/(λa)`,
`B(v_design) − B(v_profile) ≤ (c² − 1)B(v_profile) + (s₀/(λa))(c − 1) + (1 + C)λ(c − 1)²`. -/
theorem B_vDesign_sub_le_quad (hP : P.Valid) {C : ℝ} (hC : 0 ≤ C) {s₀ : ℝ} (hs0 : 0 ≤ s₀)
    (hs : ∀ t, P.lam / 2 - P.w / P.LL < |t| → |t| ≤ P.lam / 2 → (P.prof.eval t) ^ 2 ≤ s₀) :
    B C (vDesign P) - B C (vProfile P)
      ≤ ((profMass P / (P.lam * P.aQ)) ^ 2 - 1) * B C (vProfile P)
        + s₀ / (P.lam * P.aQ) * (profMass P / (P.lam * P.aQ) - 1)
        + (1 + C) * P.lam * (profMass P / (P.lam * P.aQ) - 1) ^ 2 :=
  B_sub_B_le_quad hC (vDesign_admissible hP) (vProfile_admissible hP) (vDesign_le hP)
    (vProfile_le hP) (div_nonneg (profMass_pos hP).le (mul_pos hP.lam_pos hP.aQ_pos).le)
    (cv_sub_v_nonneg hP) (cv_sub_v_le hP hs0 hs)

/-! ## §5. Bounds on `B(v_profile)` -/

/-- the pointwise kernel bound `W(s − t)·f(t)g(s) ≤ (1 + C)λ·f(t)g(s)` for nonnegative `f, g`
supported in `[−λ/2, λ/2]`. -/
theorem W_mul_le_of_supp {lam C : ℝ} (hC : 0 ≤ C) {f g : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    (hf : ∀ t, f t ≠ 0 → |t| ≤ lam / 2) (hg : ∀ t, g t ≠ 0 → |t| ≤ lam / 2) (z : ℝ × ℝ) :
    W C (z.2 - z.1) * (f z.1 * g z.2) ≤ (1 + C) * lam * (f z.1 * g z.2) := by
  by_cases h0 : f z.1 * g z.2 = 0
  · rw [h0, mul_zero, mul_zero]
  · have ht := abs_le.mp (hf _ (left_ne_zero_of_mul h0))
    have hs := abs_le.mp (hg _ (right_ne_zero_of_mul h0))
    have hα : |z.2 - z.1| ≤ lam := abs_le.mpr ⟨by linarith, by linarith⟩
    have hW := abs_W_le hC hα
    have hfg : 0 ≤ f z.1 * g z.2 := mul_nonneg (hf0 _) (hg0 _)
    calc W C (z.2 - z.1) * (f z.1 * g z.2) ≤ |W C (z.2 - z.1)| * (f z.1 * g z.2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hfg
      _ ≤ (1 + C) * lam * (f z.1 * g z.2) := mul_le_mul_of_nonneg_right hW hfg

/-- `ψ_{v_profile}(0) = ∫ v_profile² ≤ 1/profMass`. -/
theorem integral_vProfile_sq_le (hP : P.Valid) :
    ∫ t, vProfile P t * vProfile P t ≤ 1 / profMass P := by
  have hvv : Integrable (fun t => vProfile P t * vProfile P t) :=
    (vProfile_integrable P).bdd_mul (vProfile_integrable P).aestronglyMeasurable
      (c := 1 / profMass P)
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (vProfile_nonneg hP t)]; exact vProfile_le hP t)
  calc ∫ t, vProfile P t * vProfile P t ≤ ∫ t, 1 / profMass P * vProfile P t := by
        refine integral_mono hvv ((vProfile_integrable P).const_mul _) fun t => ?_
        exact mul_le_mul_of_nonneg_right (vProfile_le hP t) (vProfile_nonneg hP t)
    _ = 1 / profMass P := by rw [integral_const_mul, integral_vProfile hP, mul_one]

/-- **the crude bound** `B(v_profile) ≤ 1/profMass + (1 + C)λ`. -/
theorem B_vProfile_le_crude (hP : P.Valid) {C : ℝ} (hC : 0 ≤ C) :
    B C (vProfile P) ≤ 1 / profMass P + (1 + C) * P.lam := by
  have hv' := vProfile_admissible hP
  unfold B
  have e0 : psi (vProfile P) 0 = ∫ t, vProfile P t * vProfile P t := by simp only [psi, sub_zero]
  rw [e0, integral_W_psi_eq_prod hv' hC]
  have hF' := integrable_W_prod hv' hC
  have hG : Integrable (fun z : ℝ × ℝ => vProfile P z.1 * vProfile P z.2) (volume.prod volume) :=
    hv'.integrable.mul_prod hv'.integrable
  have h2 : ∫ z : ℝ × ℝ, W C (z.2 - z.1) * (vProfile P z.1 * vProfile P z.2)
      ∂(volume.prod volume) ≤ (1 + C) * P.lam := by
    calc ∫ z : ℝ × ℝ, W C (z.2 - z.1) * (vProfile P z.1 * vProfile P z.2) ∂(volume.prod volume)
        ≤ ∫ z : ℝ × ℝ, (1 + C) * P.lam * (vProfile P z.1 * vProfile P z.2)
            ∂(volume.prod volume) :=
          integral_mono hF' (hG.const_mul _)
            (W_mul_le_of_supp hC hv'.nonneg hv'.nonneg hv'.supp hv'.supp)
      _ = (1 + C) * P.lam * (1 * 1) := by
          rw [integral_const_mul, integral_prod_mul, hv'.mass]
      _ = (1 + C) * P.lam := by ring
  linarith [integral_vProfile_sq_le hP]

/-! ## §6. Numerical assembly -/

/-- the scalar bookkeeping: with `η = c − 1 ∈ [0, kδ]`, `δ ≤ 1/100`, `0 ≤ B′ ≤ Bmax`,
`A ≥ Amin > 0`, `C ≤ Cmax`:
`(2η + η²)B′ + (s₀/A)η + (1 + C)λη² ≤ k·[(2 + k/100)Bmax + s₀/Amin + (1 + Cmax)λ·k/100]·δ`. -/
theorem assemble_numeric {η δ B' A s₀ C lam k Amin Bmax Cmax Kp : ℝ}
    (hη0 : 0 ≤ η) (hηδ : η ≤ k * δ) (hk : 0 ≤ k) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100)
    (hB0 : 0 ≤ B') (hB : B' ≤ Bmax) (hA : Amin ≤ A) (hAmin : 0 < Amin) (hs0 : 0 ≤ s₀)
    (hC0 : 0 ≤ C) (hC : C ≤ Cmax) (hlam : 0 ≤ lam)
    (hK : k * ((2 + k / 100) * Bmax + s₀ / Amin + (1 + Cmax) * lam * (k / 100)) ≤ Kp) :
    ((1 + η) ^ 2 - 1) * B' + s₀ / A * η + (1 + C) * lam * η ^ 2 ≤ Kp * δ := by
  have hBmax : 0 ≤ Bmax := le_trans hB0 hB
  have hCmax : 0 ≤ Cmax := le_trans hC0 hC
  have hkδ : k * δ ≤ k / 100 := by
    calc k * δ ≤ k * (1 / 100) := mul_le_mul_of_nonneg_left hδ hk
      _ = k / 100 := by ring
  have hηk : η ≤ k / 100 := le_trans hηδ hkδ
  have hbr0 : 0 ≤ (2 + k / 100) * Bmax + s₀ / Amin + (1 + Cmax) * lam * (k / 100) := by
    positivity
  have t1 : ((1 + η) ^ 2 - 1) * B' ≤ η * ((2 + k / 100) * Bmax) := by
    have e : (1 + η) ^ 2 - 1 = η * (2 + η) := by ring
    rw [e]
    calc η * (2 + η) * B' ≤ η * (2 + η) * Bmax :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ η * (2 + k / 100) * Bmax := by gcongr
      _ = η * ((2 + k / 100) * Bmax) := by ring
  have t2 : s₀ / A * η ≤ η * (s₀ / Amin) := by
    have h : s₀ / A ≤ s₀ / Amin := div_le_div_of_nonneg_left hs0 hAmin hA
    calc s₀ / A * η ≤ s₀ / Amin * η := mul_le_mul_of_nonneg_right h hη0
      _ = η * (s₀ / Amin) := by ring
  have t3 : (1 + C) * lam * η ^ 2 ≤ η * ((1 + Cmax) * lam * (k / 100)) := by
    have h1 : (1 + C) * lam ≤ (1 + Cmax) * lam := by gcongr
    have h2 : η ^ 2 ≤ η * (k / 100) := by rw [sq]; exact mul_le_mul_of_nonneg_left hηk hη0
    calc (1 + C) * lam * η ^ 2 ≤ (1 + Cmax) * lam * (η * (k / 100)) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = η * ((1 + Cmax) * lam * (k / 100)) := by ring
  calc ((1 + η) ^ 2 - 1) * B' + s₀ / A * η + (1 + C) * lam * η ^ 2
      ≤ η * ((2 + k / 100) * Bmax + s₀ / Amin + (1 + Cmax) * lam * (k / 100)) := by linarith
    _ ≤ (k * δ) * ((2 + k / 100) * Bmax + s₀ / Amin + (1 + Cmax) * lam * (k / 100)) :=
        mul_le_mul_of_nonneg_right hηδ hbr0
    _ = (k * ((2 + k / 100) * Bmax + s₀ / Amin + (1 + Cmax) * lam * (k / 100))) * δ := by ring
    _ ≤ Kp * δ := mul_le_mul_of_nonneg_right hK hδ0

/-- **the sharp link, generic numerics.** Inputs: the edge value `p(λ/2 − 1/100)² ≤ s₀`, the core
mass floor `Nlo ≤ profMass`, a bound `B(v_profile) ≤ Bmax`, `C ≤ Cmax`, `100w ≤ ℒ`, and the
scalar inequality `hK`. Output: `B(v_design) ≤ B(v_profile) + Kp·(w/ℒ)`. -/
theorem profileRampLink_sharp_of (hP : P.Valid) {C Cmax : ℝ} (hC : 0 ≤ C) (hCmax : C ≤ Cmax)
    (hwL : 100 * P.w ≤ P.LL) (hlam50 : 1 / 50 ≤ P.lam)
    {s₀ Nlo Bmax Kp : ℝ} (hs0 : 0 ≤ s₀)
    (hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ s₀)
    (hNlo : Nlo ≤ profMass P) (hAmin : 0 < Nlo - s₀ / 50)
    (hB : B C (vProfile P) ≤ Bmax)
    (hK : 2 * s₀ / (Nlo - s₀ / 50) * ((2 + 2 * s₀ / (Nlo - s₀ / 50) / 100) * Bmax
            + s₀ / (Nlo - s₀ / 50) + (1 + Cmax) * P.lam * (2 * s₀ / (Nlo - s₀ / 50) / 100))
          ≤ Kp) :
    B C (vDesign P) ≤ B C (vProfile P) + Kp * (P.w / P.LL) := by
  have hLL := hP.LL_pos
  have hw := hP.w_pos
  have hδ0 : 0 ≤ P.w / P.LL := div_nonneg hw.le hLL.le
  have hδ : P.w / P.LL ≤ 1 / 100 := by
    rw [div_le_iff₀ hLL]; linarith
  -- the strip bound
  have hs : ∀ t, P.lam / 2 - P.w / P.LL < |t| → |t| ≤ P.lam / 2 → (P.prof.eval t) ^ 2 ≤ s₀ := by
    intro t h1 h2
    exact le_trans (prof_sq_le_edge hP hlam50 (by linarith) h2) hedge
  have hA := mul_pos hP.lam_pos hP.aQ_pos
  have hN := profMass_pos hP
  have hNA := lam_mul_aQ_le_profMass hP
  have hramp := profMass_sub_le_of_strip hP hs0 hs
  -- `A ≥ Nlo − s₀/50`
  have hAlo : Nlo - s₀ / 50 ≤ P.lam * P.aQ := by
    have : 2 * (P.w / P.LL) * s₀ ≤ 2 * (1 / 100) * s₀ := by
      apply mul_le_mul_of_nonneg_right _ hs0
      linarith
    linarith
  -- `η := c − 1 = (profMass − λa)/(λa) ∈ [0, (2s₀/Amin)·δ]`
  set η := profMass P / (P.lam * P.aQ) - 1 with hη_def
  have hc : profMass P / (P.lam * P.aQ) = 1 + η := by rw [hη_def]; ring
  have hη0 : 0 ≤ η := by
    rw [hη_def, sub_nonneg, le_div_iff₀ hA, one_mul]; exact hNA
  have hηδ : η ≤ 2 * s₀ / (Nlo - s₀ / 50) * (P.w / P.LL) := by
    have e : η = (profMass P - P.lam * P.aQ) / (P.lam * P.aQ) := by
      rw [hη_def, sub_div, div_self hA.ne']
    rw [e]
    calc (profMass P - P.lam * P.aQ) / (P.lam * P.aQ)
        ≤ 2 * (P.w / P.LL) * s₀ / (P.lam * P.aQ) := div_le_div_of_nonneg_right hramp hA.le
      _ ≤ 2 * (P.w / P.LL) * s₀ / (Nlo - s₀ / 50) :=
          div_le_div_of_nonneg_left (by positivity) hAmin hAlo
      _ = 2 * s₀ / (Nlo - s₀ / 50) * (P.w / P.LL) := by ring
  have hquad := B_vDesign_sub_le_quad hP hC hs0 hs
  rw [hc] at hquad
  have hB0 : 0 ≤ B C (vProfile P) := B_nonneg' hC (vProfile_admissible hP)
  have hnum := assemble_numeric (η := η) (δ := P.w / P.LL) (B' := B C (vProfile P))
    (A := P.lam * P.aQ) (s₀ := s₀) (C := C) (lam := P.lam) (k := 2 * s₀ / (Nlo - s₀ / 50))
    (Amin := Nlo - s₀ / 50) (Bmax := Bmax) (Cmax := Cmax) (Kp := Kp)
    hη0 hηδ (by positivity) hδ0 hδ hB0 hB hAlo hAmin hs0 hC hCmax hP.lam_pos.le hK
  linarith

/-! ### The two families (crude `B(v_profile)` bound) -/

/-- `profMass` at a profile `p = 1 + d₁t² + d₂t⁴ + d₃t⁶` is the explicit antiderivative difference. -/
theorem profMass_eq_sqPrim {d1 d2 d3 : ℝ}
    (hprof : ∀ t, P.prof.eval t = 1 + d1 * t ^ 2 + d2 * t ^ 4 + d3 * t ^ 6) :
    profMass P = sqPrim d1 d2 d3 (P.lam / 2) - sqPrim d1 d2 d3 (-(P.lam / 2)) := by
  unfold profMass
  simp_rw [hprof]
  exact integral_sq_poly d1 d2 d3 _ _

theorem Cfam_le : Cfam ≤ 5.412 := by
  have := C_qQ_le
  unfold Cfam
  push_cast at this
  linarith

theorem CfamDyadic_le : CfamDyadic ≤ 7.216 := by
  have h := C_dyad_le
  unfold CfamDyadic
  have h5 : ((2 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) ≤ 7.216 := by
    push_cast
    norm_num
  linarith

theorem Cfam_pos : 0 < Cfam := by unfold Cfam; positivity

theorem CfamDyadic_pos : 0 < CfamDyadic := by unfold CfamDyadic; positivity

/-- **the sharp link for `q ≤ Q`, crude `B(v_profile)` bound**: `B(v_design) ≤ B(v_profile) +
2.4·(w/ℒ)` (`= λ*·2.4·(w/L) ≈ 3.0·(w/L)`). -/
theorem profileRampLink_sharp_qle_crude (hP : P.Valid) (hprof : P.prof = designProfileQle)
    (hlam : P.lam = lamStar) (hwL : 100 * P.w ≤ P.LL) :
    B Cfam (vDesign P) ≤ B Cfam (vProfile P) + (24 / 10) * (P.w / P.LL) := by
  have hlam' : P.lam = 1.2507321515 := hlam
  have hprof' : ∀ t, P.prof.eval t
      = 1 + (-81257 / 125000) * t ^ 2 + (3458583 / 1000000) * t ^ 4
          + (-3669851 / 200000) * t ^ 6 := by
    intro t; rw [hprof]; exact designProfileQle_eval t
  have hC0 := Cfam_pos
  have hCmax := Cfam_le
  have hNlo : (979 / 1000 : ℝ) ≤ profMass P := by
    rw [profMass_eq_sqPrim hprof', hlam']
    unfold sqPrim; norm_num
  have hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ (643 / 10000 : ℝ) := by
    rw [hprof', hlam']; norm_num
  have hB := B_vProfile_le_crude hP hC0.le (C := Cfam)
  have hB' : B Cfam (vProfile P) ≤ 1 / (979 / 1000) + (1 + 5.412) * 1.2507321515 := by
    have h1 : 1 / profMass P ≤ 1 / (979 / 1000) :=
      one_div_le_one_div_of_le (by norm_num) hNlo
    have h2 : (1 + Cfam) * P.lam ≤ (1 + 5.412) * 1.2507321515 := by
      rw [hlam']; gcongr
    linarith
  refine profileRampLink_sharp_of hP hC0.le hCmax hwL (by rw [hlam']; norm_num) (by norm_num)
    hedge hNlo (by norm_num) hB' ?_
  rw [hlam']; norm_num

/-- **the sharp link for the dyadic family, crude `B(v_profile)` bound**: `B(v_design) ≤
B(v_profile) + 3.94·(w/ℒ)` (`= λ*_dyad·3.94·(w/L) ≈ 4.7·(w/L)`). -/
theorem profileRampLink_sharp_dyadic_crude (hP : P.Valid) (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) (hwL : 100 * P.w ≤ P.LL) :
    B CfamDyadic (vDesign P) ≤ B CfamDyadic (vProfile P) + (394 / 100) * (P.w / P.LL) := by
  have hlam' : P.lam = 1.1931581210 := hlam
  have hprof' : ∀ t, P.prof.eval t
      = 1 + (-1014099 / 1000000) * t ^ 2 + (834917 / 100000) * t ^ 4
          + (-16525667 / 500000) * t ^ 6 := by
    intro t; rw [hprof]; exact designProfileDyadic_eval t
  have hC0 := CfamDyadic_pos
  have hCmax := CfamDyadic_le
  have hNlo : (956 / 1000 : ℝ) ≤ profMass P := by
    rw [profMass_eq_sqPrim hprof', hlam']
    unfold sqPrim; norm_num
  have hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ (86 / 1000 : ℝ) := by
    rw [hprof', hlam']; norm_num
  have hB := B_vProfile_le_crude hP hC0.le (C := CfamDyadic)
  have hB' : B CfamDyadic (vProfile P) ≤ 1 / (956 / 1000) + (1 + 7.216) * 1.1931581210 := by
    have h1 : 1 / profMass P ≤ 1 / (956 / 1000) :=
      one_div_le_one_div_of_le (by norm_num) hNlo
    have h2 : (1 + CfamDyadic) * P.lam ≤ (1 + 7.216) * 1.1931581210 := by
      rw [hlam']; gcongr
    linarith
  refine profileRampLink_sharp_of hP hC0.le hCmax hwL (by rw [hlam']; norm_num) (by norm_num)
    hedge hNlo (by norm_num) hB' ?_
  rw [hlam']; norm_num

/-! ## §7. The refined bound `B(v_profile) ≤ 1/profMass + 1 + Cλ·m²`,
`m ≥ ∫_{|t| ≥ 1 − λ/2} v_profile` (the out-zone `|s − t| > 1` forces BOTH points into the far set
`{|t| ≥ 1 − λ/2}`, so the `Cλ` part of the kernel sees only the product of the far masses). -/

theorem measurableSet_far (q : ℝ) : MeasurableSet {t : ℝ | q ≤ |t|} :=
  measurableSet_le measurable_const continuous_abs.measurable

/-- the pointwise kernel bound with the far-set indicator: for nonnegative `f, g` supported in
`[−λ/2, λ/2]`, `W(s − t) f(t) g(s) ≤ f(t) g(s) + Cλ·(1_far f)(t)(1_far g)(s)`. -/
theorem W_mul_le_far {lam C : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) {f g : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    (hf : ∀ t, f t ≠ 0 → |t| ≤ lam / 2) (hg : ∀ t, g t ≠ 0 → |t| ≤ lam / 2) (z : ℝ × ℝ) :
    W C (z.2 - z.1) * (f z.1 * g z.2)
      ≤ f z.1 * g z.2 + C * lam * ({t : ℝ | 1 - lam / 2 ≤ |t|}.indicator f z.1
          * {t : ℝ | 1 - lam / 2 ≤ |t|}.indicator g z.2) := by
  have hfg : 0 ≤ f z.1 * g z.2 := mul_nonneg (hf0 _) (hg0 _)
  have hind : 0 ≤ {t : ℝ | 1 - lam / 2 ≤ |t|}.indicator f z.1
      * {t : ℝ | 1 - lam / 2 ≤ |t|}.indicator g z.2 :=
    mul_nonneg (indicator_nonneg (fun t _ => hf0 t) _) (indicator_nonneg (fun t _ => hg0 t) _)
  have hCl : 0 ≤ C * lam := mul_nonneg hC hlam
  by_cases h0 : f z.1 * g z.2 = 0
  · rw [h0, mul_zero, zero_add]; exact mul_nonneg hCl hind
  · have ha1 : |z.1| ≤ lam / 2 := hf _ (left_ne_zero_of_mul h0)
    have ha2 : |z.2| ≤ lam / 2 := hg _ (right_ne_zero_of_mul h0)
    have ht := abs_le.mp ha1
    have hs := abs_le.mp ha2
    have hα : |z.2 - z.1| ≤ lam := abs_le.mpr ⟨by linarith, by linarith⟩
    unfold W
    split_ifs with h
    · calc |z.2 - z.1| * (f z.1 * g z.2) ≤ 1 * (f z.1 * g z.2) :=
            mul_le_mul_of_nonneg_right h hfg
        _ = f z.1 * g z.2 := one_mul _
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hCl hind)
    · rw [not_le] at h
      have htri : |z.2 - z.1| ≤ |z.2| + |z.1| :=
        abs_le.mpr ⟨by linarith [neg_abs_le z.1, le_abs_self z.1, neg_abs_le z.2, le_abs_self z.2],
          by linarith [neg_abs_le z.1, le_abs_self z.1, neg_abs_le z.2, le_abs_self z.2]⟩
      have hfar1 : z.1 ∈ {t : ℝ | 1 - lam / 2 ≤ |t|} := by
        show 1 - lam / 2 ≤ |z.1|; linarith
      have hfar2 : z.2 ∈ {t : ℝ | 1 - lam / 2 ≤ |t|} := by
        show 1 - lam / 2 ≤ |z.2|; linarith
      rw [indicator_of_mem hfar1, indicator_of_mem hfar2]
      calc C * |z.2 - z.1| * (f z.1 * g z.2) ≤ C * lam * (f z.1 * g z.2) := by gcongr
        _ ≤ f z.1 * g z.2 + C * lam * (f z.1 * g z.2) := le_add_of_nonneg_left hfg

/-- **the refined bound** `B(v_profile) ≤ 1/profMass + 1 + Cλ·m²` for any
`m ≥ ∫_{|t| ≥ 1 − λ/2} v_profile`. -/
theorem B_vProfile_le_refined (hP : P.Valid) {C : ℝ} (hC : 0 ≤ C) {m : ℝ}
    (hm : ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t ≤ m) :
    B C (vProfile P) ≤ 1 / profMass P + 1 + C * P.lam * m ^ 2 := by
  have hv' := vProfile_admissible hP
  have hg_int : Integrable ({t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P)) :=
    (vProfile_integrable P).indicator (measurableSet_far _)
  have hg0 : 0 ≤ ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t :=
    integral_nonneg (indicator_nonneg (fun t _ => vProfile_nonneg hP t))
  have hm0 : 0 ≤ m := le_trans hg0 hm
  unfold B
  have e0 : psi (vProfile P) 0 = ∫ t, vProfile P t * vProfile P t := by simp only [psi, sub_zero]
  rw [e0, integral_W_psi_eq_prod hv' hC]
  have hF' := integrable_W_prod hv' hC
  have hG : Integrable (fun z : ℝ × ℝ => vProfile P z.1 * vProfile P z.2) (volume.prod volume) :=
    hv'.integrable.mul_prod hv'.integrable
  have hGg : Integrable (fun z : ℝ × ℝ =>
      {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) z.1
        * {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) z.2) (volume.prod volume) :=
    hg_int.mul_prod hg_int
  have h2 : ∫ z : ℝ × ℝ, W C (z.2 - z.1) * (vProfile P z.1 * vProfile P z.2)
      ∂(volume.prod volume) ≤ 1 + C * P.lam * m ^ 2 := by
    calc ∫ z : ℝ × ℝ, W C (z.2 - z.1) * (vProfile P z.1 * vProfile P z.2) ∂(volume.prod volume)
        ≤ ∫ z : ℝ × ℝ, (vProfile P z.1 * vProfile P z.2
            + C * P.lam * ({t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) z.1
              * {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) z.2))
            ∂(volume.prod volume) :=
          integral_mono hF' (hG.add (hGg.const_mul _))
            (W_mul_le_far hC hP.lam_pos.le hv'.nonneg hv'.nonneg hv'.supp hv'.supp)
      _ = 1 * 1 + C * P.lam * ((∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t)
            * ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t) := by
          rw [integral_add hG (hGg.const_mul _), integral_const_mul, integral_prod_mul,
            integral_prod_mul, hv'.mass]
      _ ≤ 1 + C * P.lam * m ^ 2 := by
          have hsq : (∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t)
              * ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t ≤ m ^ 2 := by
            rw [sq]; exact mul_le_mul hm hm hg0 hm0
          have hCl : 0 ≤ C * P.lam := mul_nonneg hC hP.lam_pos.le
          have := mul_le_mul_of_nonneg_left hsq hCl
          linarith
  linarith [integral_vProfile_sq_le hP]

/-- `∫_{|t| ≥ q} v_profile ≤ (∫_q^{λ/2} p² + ∫_{−λ/2}^{−q} p²)/profMass` for `0 ≤ q ≤ λ/2`. -/
theorem integral_far_vProfile_le (hP : P.Valid) {q : ℝ} (hq : q ≤ P.lam / 2) :
    ∫ t, {t : ℝ | q ≤ |t|}.indicator (vProfile P) t
      ≤ ((∫ s in q..(P.lam / 2), (P.prof.eval s) ^ 2)
          + ∫ s in (-(P.lam / 2))..(-q), (P.prof.eval s) ^ 2) / profMass P := by
  have hI := profMass_pos hP
  have hcont : Continuous fun s => (P.prof.eval s) ^ 2 / profMass P :=
    (prof_sq_continuous P).div_const _
  have hint1 : Integrable ((Icc q (P.lam / 2)).indicator
      fun s => (P.prof.eval s) ^ 2 / profMass P) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hcont.integrableOn_Icc
  have hint2 : Integrable ((Icc (-(P.lam / 2)) (-q)).indicator
      fun s => (P.prof.eval s) ^ 2 / profMass P) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hcont.integrableOn_Icc
  have hnn : ∀ s, 0 ≤ (P.prof.eval s) ^ 2 / profMass P :=
    fun s => div_nonneg (sq_nonneg _) hI.le
  have hn1 : ∀ t, 0 ≤ (Icc q (P.lam / 2)).indicator
      (fun s => (P.prof.eval s) ^ 2 / profMass P) t :=
    fun t => indicator_nonneg (fun s _ => hnn s) t
  have hn2 : ∀ t, 0 ≤ (Icc (-(P.lam / 2)) (-q)).indicator
      (fun s => (P.prof.eval s) ^ 2 / profMass P) t :=
    fun t => indicator_nonneg (fun s _ => hnn s) t
  have hptw : ∀ t, {t : ℝ | q ≤ |t|}.indicator (vProfile P) t
      ≤ (Icc q (P.lam / 2)).indicator (fun s => (P.prof.eval s) ^ 2 / profMass P) t
        + (Icc (-(P.lam / 2)) (-q)).indicator (fun s => (P.prof.eval s) ^ 2 / profMass P) t := by
    intro t
    have hr0 := add_nonneg (hn1 t) (hn2 t)
    by_cases hmem : t ∈ {t : ℝ | q ≤ |t|}
    · rw [indicator_of_mem hmem]
      have hqt : q ≤ |t| := hmem
      rw [vProfile_eq]
      split_ifs with ht
      · rcases le_or_gt 0 t with ht0 | ht0
        · rw [abs_of_nonneg ht0] at hqt ht
          have hm1 : t ∈ Icc q (P.lam / 2) := ⟨hqt, ht⟩
          rw [indicator_of_mem hm1]
          linarith [hn2 t]
        · rw [abs_of_neg ht0] at hqt ht
          have hm2 : t ∈ Icc (-(P.lam / 2)) (-q) := ⟨by linarith, by linarith⟩
          rw [indicator_of_mem hm2]
          linarith [hn1 t]
      · exact hr0
    · rw [indicator_of_notMem hmem]; exact hr0
  have hg_int : Integrable ({t : ℝ | q ≤ |t|}.indicator (vProfile P)) :=
    (vProfile_integrable P).indicator (measurableSet_far _)
  calc ∫ t, {t : ℝ | q ≤ |t|}.indicator (vProfile P) t
      ≤ ∫ t, ((Icc q (P.lam / 2)).indicator (fun s => (P.prof.eval s) ^ 2 / profMass P) t
        + (Icc (-(P.lam / 2)) (-q)).indicator (fun s => (P.prof.eval s) ^ 2 / profMass P) t) :=
        integral_mono hg_int (hint1.add hint2) hptw
    _ = (∫ s in Icc q (P.lam / 2), (P.prof.eval s) ^ 2 / profMass P)
        + ∫ s in Icc (-(P.lam / 2)) (-q), (P.prof.eval s) ^ 2 / profMass P := by
        rw [integral_add hint1 hint2, integral_indicator measurableSet_Icc,
          integral_indicator measurableSet_Icc]
    _ = ((∫ s in q..(P.lam / 2), (P.prof.eval s) ^ 2)
          + ∫ s in (-(P.lam / 2))..(-q), (P.prof.eval s) ^ 2) / profMass P := by
        rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hq, ← intervalIntegral.integral_of_le (by linarith),
          intervalIntegral.integral_div, intervalIntegral.integral_div, add_div]

/-! ### The two families, refined -/

/-- **the sharp link for `q ≤ Q`**: `B(v_design) ≤ B(v_profile) + 0.675·(w/ℒ)`
(`s₀ = 0.0643`, `profMass ≥ 0.979`, far mass `≤ 0.266/0.979 = 0.272`,
`B(v_profile) ≤ 1/0.979 + 1 + 5.412·λ*·0.272² = 2.52`, `η ≤ 0.1316·(w/ℒ)`). -/
theorem profileRampLink_sharp_qle (hP : P.Valid) (hprof : P.prof = designProfileQle)
    (hlam : P.lam = lamStar) (hwL : 100 * P.w ≤ P.LL) :
    B Cfam (vDesign P) ≤ B Cfam (vProfile P) + (675 / 1000) * (P.w / P.LL) := by
  have hlam' : P.lam = 1.2507321515 := hlam
  have hprof' : ∀ t, P.prof.eval t
      = 1 + (-81257 / 125000) * t ^ 2 + (3458583 / 1000000) * t ^ 4
          + (-3669851 / 200000) * t ^ 6 := by
    intro t; rw [hprof]; exact designProfileQle_eval t
  have hC0 := Cfam_pos
  have hCmax := Cfam_le
  have hNlo : (979 / 1000 : ℝ) ≤ profMass P := by
    rw [profMass_eq_sqPrim hprof', hlam']
    unfold sqPrim; norm_num
  have hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ (643 / 10000 : ℝ) := by
    rw [hprof', hlam']; norm_num
  -- the far mass
  have hfar : ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t
      ≤ (266 / 1000) / (979 / 1000) := by
    have h := integral_far_vProfile_le hP (q := 1 - P.lam / 2) (by rw [hlam']; norm_num)
    have hM : (∫ s in (1 - P.lam / 2)..(P.lam / 2), (P.prof.eval s) ^ 2)
        + ∫ s in (-(P.lam / 2))..(-(1 - P.lam / 2)), (P.prof.eval s) ^ 2 ≤ 266 / 1000 := by
      simp_rw [hprof']
      rw [integral_sq_poly, integral_sq_poly, hlam']
      unfold sqPrim; norm_num
    calc _ ≤ _ := h
      _ ≤ (266 / 1000) / profMass P := div_le_div_of_nonneg_right hM (profMass_pos hP).le
      _ ≤ (266 / 1000) / (979 / 1000) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNlo
  have hB := B_vProfile_le_refined hP hC0.le hfar
  have hB' : B Cfam (vProfile P)
      ≤ 1 / (979 / 1000) + 1 + 5.412 * 1.2507321515 * ((266 / 1000) / (979 / 1000)) ^ 2 := by
    have h1 : 1 / profMass P ≤ 1 / (979 / 1000) :=
      one_div_le_one_div_of_le (by norm_num) hNlo
    have h2 : Cfam * P.lam * ((266 / 1000) / (979 / 1000)) ^ 2
        ≤ 5.412 * 1.2507321515 * ((266 / 1000) / (979 / 1000)) ^ 2 := by
      rw [hlam']; gcongr
    linarith
  refine profileRampLink_sharp_of hP hC0.le hCmax hwL (by rw [hlam']; norm_num) (by norm_num)
    hedge hNlo (by norm_num) hB' ?_
  rw [hlam']; norm_num

/-- **the sharp link for the dyadic family**: `B(v_design) ≤ B(v_profile) + 0.8925·(w/ℒ)`
(`s₀ = 0.086`, `profMass ≥ 0.956`, far mass `≤ 0.199/0.956 = 0.208`,
`B(v_profile) ≤ 1/0.956 + 1 + 7.216·λ*·0.208² = 2.42`, `η ≤ 0.1803·(w/ℒ)`). -/
theorem profileRampLink_sharp_dyadic (hP : P.Valid) (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) (hwL : 100 * P.w ≤ P.LL) :
    B CfamDyadic (vDesign P) ≤ B CfamDyadic (vProfile P) + (8925 / 10000) * (P.w / P.LL) := by
  have hlam' : P.lam = 1.1931581210 := hlam
  have hprof' : ∀ t, P.prof.eval t
      = 1 + (-1014099 / 1000000) * t ^ 2 + (834917 / 100000) * t ^ 4
          + (-16525667 / 500000) * t ^ 6 := by
    intro t; rw [hprof]; exact designProfileDyadic_eval t
  have hC0 := CfamDyadic_pos
  have hCmax := CfamDyadic_le
  have hNlo : (956 / 1000 : ℝ) ≤ profMass P := by
    rw [profMass_eq_sqPrim hprof', hlam']
    unfold sqPrim; norm_num
  have hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ (86 / 1000 : ℝ) := by
    rw [hprof', hlam']; norm_num
  have hfar : ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t
      ≤ (199 / 1000) / (956 / 1000) := by
    have h := integral_far_vProfile_le hP (q := 1 - P.lam / 2) (by rw [hlam']; norm_num)
    have hM : (∫ s in (1 - P.lam / 2)..(P.lam / 2), (P.prof.eval s) ^ 2)
        + ∫ s in (-(P.lam / 2))..(-(1 - P.lam / 2)), (P.prof.eval s) ^ 2 ≤ 199 / 1000 := by
      simp_rw [hprof']
      rw [integral_sq_poly, integral_sq_poly, hlam']
      unfold sqPrim; norm_num
    calc _ ≤ _ := h
      _ ≤ (199 / 1000) / profMass P := div_le_div_of_nonneg_right hM (profMass_pos hP).le
      _ ≤ (199 / 1000) / (956 / 1000) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNlo
  have hB := B_vProfile_le_refined hP hC0.le hfar
  have hB' : B CfamDyadic (vProfile P)
      ≤ 1 / (956 / 1000) + 1 + 7.216 * 1.1931581210 * ((199 / 1000) / (956 / 1000)) ^ 2 := by
    have h1 : 1 / profMass P ≤ 1 / (956 / 1000) :=
      one_div_le_one_div_of_le (by norm_num) hNlo
    have h2 : CfamDyadic * P.lam * ((199 / 1000) / (956 / 1000)) ^ 2
        ≤ 7.216 * 1.1931581210 * ((199 / 1000) / (956 / 1000)) ^ 2 := by
      rw [hlam']; gcongr
    linarith
  refine profileRampLink_sharp_of hP hC0.le hCmax hwL (by rw [hlam']; norm_num) (by norm_num)
    hedge hNlo (by norm_num) hB' ?_
  rw [hlam']; norm_num

/-- `profileRampLink_sharp_qle` at any `C ≤ 10.824` in place of `Cfam` — the same edge, mass and far-mass
inputs, a larger `B(v_profile)` bound and ramp constant `81 / 100`. This is the link the
reflected-sieve families (`Cconst = 2C` at the full design) need in
`profileRampLink_sharp`. -/
theorem profileRampLink_sharp_qle_twoC (hP : P.Valid) (hprof : P.prof = designProfileQle)
    (hlam : P.lam = lamStar) (hwL : 100 * P.w ≤ P.LL) {C : ℝ} (hC0' : 0 ≤ C) (hCmax' : C ≤ 10.824) :
    B C (vDesign P) ≤ B C (vProfile P) + (81 / 100) * (P.w / P.LL) := by
  have hlam' : P.lam = 1.2507321515 := hlam
  have hprof' : ∀ t, P.prof.eval t
      = 1 + (-81257 / 125000) * t ^ 2 + (3458583 / 1000000) * t ^ 4
          + (-3669851 / 200000) * t ^ 6 := by
    intro t; rw [hprof]; exact designProfileQle_eval t
  have hNlo : (979 / 1000 : ℝ) ≤ profMass P := by
    rw [profMass_eq_sqPrim hprof', hlam']
    unfold sqPrim; norm_num
  have hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ (643 / 10000 : ℝ) := by
    rw [hprof', hlam']; norm_num
  -- the far mass
  have hfar : ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t
      ≤ (266 / 1000) / (979 / 1000) := by
    have h := integral_far_vProfile_le hP (q := 1 - P.lam / 2) (by rw [hlam']; norm_num)
    have hM : (∫ s in (1 - P.lam / 2)..(P.lam / 2), (P.prof.eval s) ^ 2)
        + ∫ s in (-(P.lam / 2))..(-(1 - P.lam / 2)), (P.prof.eval s) ^ 2 ≤ 266 / 1000 := by
      simp_rw [hprof']
      rw [integral_sq_poly, integral_sq_poly, hlam']
      unfold sqPrim; norm_num
    calc _ ≤ _ := h
      _ ≤ (266 / 1000) / profMass P := div_le_div_of_nonneg_right hM (profMass_pos hP).le
      _ ≤ (266 / 1000) / (979 / 1000) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNlo
  have hB := B_vProfile_le_refined hP hC0' hfar
  have hB' : B C (vProfile P)
      ≤ 1 / (979 / 1000) + 1 + 10.824 * 1.2507321515 * ((266 / 1000) / (979 / 1000)) ^ 2 := by
    have h1 : 1 / profMass P ≤ 1 / (979 / 1000) :=
      one_div_le_one_div_of_le (by norm_num) hNlo
    have h2 : C * P.lam * ((266 / 1000) / (979 / 1000)) ^ 2
        ≤ 10.824 * 1.2507321515 * ((266 / 1000) / (979 / 1000)) ^ 2 := by
      rw [hlam']; gcongr
    linarith
  refine profileRampLink_sharp_of hP hC0' hCmax' hwL (by rw [hlam']; norm_num) (by norm_num)
    hedge hNlo (by norm_num) hB' ?_
  rw [hlam']; norm_num

/-- `profileRampLink_sharp_dyadic` at any `C ≤ 14.432` in place of `CfamDyadic` — the same edge, mass and far-mass
inputs, a larger `B(v_profile)` bound and ramp constant `104 / 100`. This is the link the
reflected-sieve families (`Cconst = 2C` at the full design) need in
`profileRampLink_sharp`. -/
theorem profileRampLink_sharp_dyadic_twoC (hP : P.Valid) (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) (hwL : 100 * P.w ≤ P.LL) {C : ℝ} (hC0' : 0 ≤ C) (hCmax' : C ≤ 14.432) :
    B C (vDesign P) ≤ B C (vProfile P) + (104 / 100) * (P.w / P.LL) := by
  have hlam' : P.lam = 1.1931581210 := hlam
  have hprof' : ∀ t, P.prof.eval t
      = 1 + (-1014099 / 1000000) * t ^ 2 + (834917 / 100000) * t ^ 4
          + (-16525667 / 500000) * t ^ 6 := by
    intro t; rw [hprof]; exact designProfileDyadic_eval t
  have hNlo : (956 / 1000 : ℝ) ≤ profMass P := by
    rw [profMass_eq_sqPrim hprof', hlam']
    unfold sqPrim; norm_num
  have hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ (86 / 1000 : ℝ) := by
    rw [hprof', hlam']; norm_num
  have hfar : ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t
      ≤ (199 / 1000) / (956 / 1000) := by
    have h := integral_far_vProfile_le hP (q := 1 - P.lam / 2) (by rw [hlam']; norm_num)
    have hM : (∫ s in (1 - P.lam / 2)..(P.lam / 2), (P.prof.eval s) ^ 2)
        + ∫ s in (-(P.lam / 2))..(-(1 - P.lam / 2)), (P.prof.eval s) ^ 2 ≤ 199 / 1000 := by
      simp_rw [hprof']
      rw [integral_sq_poly, integral_sq_poly, hlam']
      unfold sqPrim; norm_num
    calc _ ≤ _ := h
      _ ≤ (199 / 1000) / profMass P := div_le_div_of_nonneg_right hM (profMass_pos hP).le
      _ ≤ (199 / 1000) / (956 / 1000) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNlo
  have hB := B_vProfile_le_refined hP hC0' hfar
  have hB' : B C (vProfile P)
      ≤ 1 / (956 / 1000) + 1 + 14.432 * 1.1931581210 * ((199 / 1000) / (956 / 1000)) ^ 2 := by
    have h1 : 1 / profMass P ≤ 1 / (956 / 1000) :=
      one_div_le_one_div_of_le (by norm_num) hNlo
    have h2 : C * P.lam * ((199 / 1000) / (956 / 1000)) ^ 2
        ≤ 14.432 * 1.1931581210 * ((199 / 1000) / (956 / 1000)) ^ 2 := by
      rw [hlam']; gcongr
    linarith
  refine profileRampLink_sharp_of hP hC0' hCmax' hwL (by rw [hlam']; norm_num) (by norm_num)
    hedge hNlo (by norm_num) hB' ?_
  rw [hlam']; norm_num

/-! ## §7b. The two parity design points

The same computation as §7's two full-family branches, run at

  * even/odd `q ≤ Q` : `p = designProfileEvenQ10`  (deg 10), `λ' = 1.1289788821`, `C = π⁴/9`
  * even/odd dyadic  : `p = designProfileEvenDyad12` (deg 12), `λ' = 1.0955998422`, `C = 4π⁴/27`

Arithmetic (exact from the coefficient lists, then rounded in the safe direction):

  even/odd `q ≤ Q`, `C = π⁴/9 ≤ 10.824`, `λ'/2 = 0.56448944105`
    `profMass = 0.9509110849 → Nlo = 0.950`; `s₀ = p(λ'/2 − 0.01)² = 0.1094816407 → 0.1095`;
    far mass `= 0.1321030704 → M = 0.1322`; `Bmax = 2.2892722029`; `Amin = 0.94781`;
    `k = 2s₀/Amin = 0.2310589675`; `Kp = 1.0929568904 → 1.098`; `K = Kp·λ' = 1.2396 → 1.24`.

  even/odd dyadic, `C = 4π⁴/27 ≤ 14.431`, `λ'/2 = 0.5477999211`
    `profMass = 0.9428579790 → Nlo = 0.942`; `s₀ = 0.1509034645 → 0.1510`;
    far mass `= 0.0972887237 → M = 0.0973`; `Bmax = 2.2302544929`; `Amin = 0.93898`;
    `k = 0.3216255937`; `Kp = 1.5061306903 → 1.51`; `K = Kp·λ' = 1.6544 → 1.66`.

**The old placeholder `107/100` was not attainable on this route.** Tightening `Nlo`, `s₀`,
`M` to their exact values moves `Kp·λ'` only to `1.2317`/`1.6468`, and even discarding every
term of `Kp` except the leading `2k·Bmax` leaves `≥ 1.192` (`q ≤ Q`) and `≥ 1.569` (dyadic).
It is `s₀` that moved: the refit profiles are flatter at the edge (`0.1095`/`0.1510` against
`0.0643`/`0.0860` for the two full families) and `Kp` is essentially linear in `s₀` through
`k = 2s₀/Amin`. -/

theorem CfamEven_pos : 0 < CfamEven := by unfold CfamEven; positivity

theorem CfamEven_le : CfamEven ≤ 10.824 := by
  have h4 : Real.pi ^ 4 ≤ (3.141593 : ℝ) ^ 4 := by
    gcongr
    exact Real.pi_lt_d6.le
  have h5 : (3.141593 : ℝ) ^ 4 ≤ 97.40914 := by norm_num
  unfold CfamEven
  linarith

theorem CfamEvenDyadic_pos : 0 < CfamEvenDyadic := by unfold CfamEvenDyadic; positivity

theorem CfamEvenDyadic_le : CfamEvenDyadic ≤ 14.431 := by
  have h4 : Real.pi ^ 4 ≤ (3.141593 : ℝ) ^ 4 := by
    gcongr
    exact Real.pi_lt_d6.le
  have h5 : (3.141593 : ℝ) ^ 4 ≤ 97.40914 := by norm_num
  unfold CfamEvenDyadic
  linarith

set_option maxHeartbeats 0 in
/-- **the sharp link for the even/odd `q ≤ Q` REFIT design** (`C = π⁴/9`, `p =
designProfileEvenQ10`, `λ' = 1.1289788821`): `B(v_design) ≤ B(v_profile) + 1.098·(w/ℒ)`.
(`s₀ = 0.1095`, `profMass ≥ 0.950`, far mass `≤ 0.1322/0.950 = 0.1392`,
`B(v_profile) ≤ 1/0.950 + 1 + 10.824·λ'·0.1392² = 2.2893`, `η ≤ 0.2311·(w/ℒ)`.) -/
theorem profileRampLink_sharp_evenq10 (hP : P.Valid) (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) (hwL : 100 * P.w ≤ P.LL) :
    B CfamEven (vDesign P) ≤ B CfamEven (vProfile P) + (1098 / 1000) * (P.w / P.LL) := by
  have hlam' : P.lam = 1.1289788821 := hlam
  have hC0 := CfamEven_pos
  have hCmax := CfamEven_le
  have hNlo : (950 / 1000 : ℝ) ≤ profMass P := by
    unfold profMass
    simp_rw [hprof, designProfileEvenQ10_eval]
    rw [integral_sq_designProfileEvenQ10, hlam']
    unfold sqPrimEvenQ10; norm_num
  have hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ (1095 / 10000 : ℝ) := by
    rw [hlam', hprof, designProfileEvenQ10_eval]; norm_num
  -- the far mass
  have hfar : ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t
      ≤ (1322 / 10000) / (950 / 1000) := by
    have h := integral_far_vProfile_le hP (q := 1 - P.lam / 2) (by rw [hlam']; norm_num)
    have hM : (∫ s in (1 - P.lam / 2)..(P.lam / 2), (P.prof.eval s) ^ 2)
        + ∫ s in (-(P.lam / 2))..(-(1 - P.lam / 2)), (P.prof.eval s) ^ 2 ≤ 1322 / 10000 := by
      simp_rw [hprof, designProfileEvenQ10_eval]
      rw [integral_sq_designProfileEvenQ10, integral_sq_designProfileEvenQ10, hlam']
      unfold sqPrimEvenQ10; norm_num
    calc _ ≤ _ := h
      _ ≤ (1322 / 10000) / profMass P := div_le_div_of_nonneg_right hM (profMass_pos hP).le
      _ ≤ (1322 / 10000) / (950 / 1000) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNlo
  have hB := B_vProfile_le_refined hP hC0.le hfar
  have hB' : B CfamEven (vProfile P)
      ≤ 1 / (950 / 1000) + 1 + 10.824 * 1.1289788821 * ((1322 / 10000) / (950 / 1000)) ^ 2 := by
    have h1 : 1 / profMass P ≤ 1 / (950 / 1000) :=
      one_div_le_one_div_of_le (by norm_num) hNlo
    have h2 : CfamEven * P.lam * ((1322 / 10000) / (950 / 1000)) ^ 2
        ≤ 10.824 * 1.1289788821 * ((1322 / 10000) / (950 / 1000)) ^ 2 := by
      rw [hlam']; gcongr
    linarith
  refine profileRampLink_sharp_of hP hC0.le hCmax hwL (by rw [hlam']; norm_num) (by norm_num)
    hedge hNlo (by norm_num) hB' ?_
  rw [hlam']; norm_num

set_option maxHeartbeats 0 in
/-- **the sharp link for the even/odd dyadic REFIT design** (`C = 4π⁴/27`, `p =
designProfileEvenDyad12`, `λ' = 1.0955998422`): `B(v_design) ≤ B(v_profile) + 1.51·(w/ℒ)`.
(`s₀ = 0.1510`, `profMass ≥ 0.942`, far mass `≤ 0.0973/0.942 = 0.1033`,
`B(v_profile) ≤ 1/0.942 + 1 + 14.431·λ'·0.1033² = 2.2303`, `η ≤ 0.3217·(w/ℒ)`.) -/
theorem profileRampLink_sharp_evendyad12 (hP : P.Valid)
    (hprof : P.prof = designProfileEvenDyad12) (hlam : P.lam = lamStarEvenDyad12)
    (hwL : 100 * P.w ≤ P.LL) :
    B CfamEvenDyadic (vDesign P) ≤ B CfamEvenDyadic (vProfile P) + (151 / 100) * (P.w / P.LL) := by
  have hlam' : P.lam = 1.0955998422 := hlam
  have hC0 := CfamEvenDyadic_pos
  have hCmax := CfamEvenDyadic_le
  have hNlo : (942 / 1000 : ℝ) ≤ profMass P := by
    unfold profMass
    simp_rw [hprof, designProfileEvenDyad12_eval]
    rw [integral_sq_designProfileEvenDyad12, hlam']
    unfold sqPrimEvenDyad12; norm_num
  have hedge : (P.prof.eval (P.lam / 2 - 1 / 100)) ^ 2 ≤ (1510 / 10000 : ℝ) := by
    rw [hlam', hprof, designProfileEvenDyad12_eval]; norm_num
  have hfar : ∫ t, {t : ℝ | 1 - P.lam / 2 ≤ |t|}.indicator (vProfile P) t
      ≤ (973 / 10000) / (942 / 1000) := by
    have h := integral_far_vProfile_le hP (q := 1 - P.lam / 2) (by rw [hlam']; norm_num)
    have hM : (∫ s in (1 - P.lam / 2)..(P.lam / 2), (P.prof.eval s) ^ 2)
        + ∫ s in (-(P.lam / 2))..(-(1 - P.lam / 2)), (P.prof.eval s) ^ 2 ≤ 973 / 10000 := by
      simp_rw [hprof, designProfileEvenDyad12_eval]
      rw [integral_sq_designProfileEvenDyad12, integral_sq_designProfileEvenDyad12, hlam']
      unfold sqPrimEvenDyad12; norm_num
    calc _ ≤ _ := h
      _ ≤ (973 / 10000) / profMass P := div_le_div_of_nonneg_right hM (profMass_pos hP).le
      _ ≤ (973 / 10000) / (942 / 1000) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNlo
  have hB := B_vProfile_le_refined hP hC0.le hfar
  have hB' : B CfamEvenDyadic (vProfile P)
      ≤ 1 / (942 / 1000) + 1 + 14.431 * 1.0955998422 * ((973 / 10000) / (942 / 1000)) ^ 2 := by
    have h1 : 1 / profMass P ≤ 1 / (942 / 1000) :=
      one_div_le_one_div_of_le (by norm_num) hNlo
    have h2 : CfamEvenDyadic * P.lam * ((973 / 10000) / (942 / 1000)) ^ 2
        ≤ 14.431 * 1.0955998422 * ((973 / 10000) / (942 / 1000)) ^ 2 := by
      rw [hlam']; gcongr
    linarith
  refine profileRampLink_sharp_of hP hC0.le hCmax hwL (by rw [hlam']; norm_num) (by norm_num)
    hedge hNlo (by norm_num) hB' ?_
  rw [hlam']; norm_num

/-! ## §8. The link in the budget's `w/L` form, and at `DesignOfRecord` -/

/-- the sharp ramp constant in the `w/L` form: `K_qle = 0.85`, `K_dyad = 1.07`
(`= λ*·0.675`, `λ*_dyad·0.8925`, rounded up); and for the four Corollary 3 parity families
`K_evenQle = K_oddQle = 1.24` (`= 1.098·λ'`), `K_evenDyadic = K_oddDyadic = 1.66`
(`= 1.51·λ'`) — the values §7b computes at the two REFIT parity design points. -/
def rampSharpK : Family → ℝ
  | Family.qle => 85 / 100
  | Family.dyadic => 107 / 100
  -- Corollary 3, from `profileRampLink_sharp_evenq10` / `profileRampLink_sharp_evendyad12`
  -- (§7b). These are NOT the parents' `107/100`: the refit profiles are flatter at the edge,
  -- `s₀ = 0.1095`/`0.1510` against `0.0643`/`0.0860`, and the ramp constant is essentially
  -- linear in `s₀`. `107/100` is not attainable on this route — see §7b's docstring.
  | Family.evenQle => 124 / 100
  | Family.oddQle => 124 / 100
  | Family.evenDyadic => 166 / 100
  | Family.oddDyadic => 166 / 100
  -- the reflected-sieve families: the FULL design profiles at the parity `Cconst = 2C`
  -- (`profileRampLink_sharp_qle_twoC` / `_dyadic_twoC`: `0.81·λ* ≤ 1.10`, `1.04·λ*_dy ≤ 1.30`).
  | Family.evenQleR => 110 / 100
  | Family.oddQleR => 110 / 100
  | Family.evenDyadicR => 130 / 100
  | Family.oddDyadicR => 130 / 100

theorem rampSharpK_pos (F : Family) : 0 < rampSharpK F := by
  cases F <;> simp only [rampSharpK] <;> norm_num

/-- the uniform upper bound on `rampSharpK`, at the honest parity values.

**This bound was `≤ 107/100` while the four parity branches carried the placeholder
`107/100`.** It is now `≤ 166/100`, `rampSharpK Family.evenDyadic`'s value. Nothing
downstream is affected: the only consumer chain is `profileRampLink_design_three` →
`profileRampLink_design_L₃` → `ZetaQ/HFrob.lean`, all of which need only
`rampSharpK F ≤ 3`. -/
theorem rampSharpK_le (F : Family) : rampSharpK F ≤ 166 / 100 := by
  cases F <;> simp only [rampSharpK] <;> norm_num

/-- `w/ℒ = λ·(w/L)`. -/
theorem w_div_LL_eq (hP : P.Valid) : P.w / P.LL = P.lam * (P.w / P.LB) := by
  unfold ParamsQ.LB
  have h1 := hP.LL_pos.ne'
  have h2 := hP.lam_pos.ne'
  field_simp

/-- the `w/ℒ → w/L` conversion at the even/odd `q ≤ Q` design: `1.098·λ' = 1.2396 ≤ 1.24`.
Stated for any `K ≥ 124/100` so that it survives a later re-rounding of `rampSharpK`. -/
theorem profileRampLink_sharp_evenQle_of_le (P : ParamsQ) (hP : P.Valid) {K : ℝ}
    (hK : (124 / 100 : ℝ) ≤ K) (hprof : P.prof = Family.evenQle.designProfile)
    (hlam : P.lam = Family.evenQle.lamStar) (hwL : 100 * P.w ≤ P.LL) :
    B Family.evenQle.Cconst (vDesign P)
      ≤ B Family.evenQle.Cconst (vProfile P) + K * (P.w / P.LB) := by
  have hwL0 : 0 ≤ P.w / P.LB := div_nonneg hP.w_pos.le (mul_pos hP.lam_pos hP.LL_pos).le
  have hprof' : P.prof = designProfileEvenQ10 := hprof
  have hlamF : P.lam = lamStarEvenQ10 := hlam
  have h := profileRampLink_sharp_evenq10 hP hprof' hlamF hwL
  rw [w_div_LL_eq hP] at h
  have hlam' : P.lam = 1.1289788821 := hlamF
  rw [hlam'] at h
  show B CfamEven (vDesign P) ≤ B CfamEven (vProfile P) + K * (P.w / P.LB)
  have h1 : (1098 / 1000 : ℝ) * (1.1289788821 * (P.w / P.LB)) ≤ 124 / 100 * (P.w / P.LB) := by
    nlinarith
  have h2 : (124 / 100 : ℝ) * (P.w / P.LB) ≤ K * (P.w / P.LB) :=
    mul_le_mul_of_nonneg_right hK hwL0
  linarith

/-- the `w/ℒ → w/L` conversion at the even/odd dyadic design: `1.51·λ' = 1.6544 ≤ 1.66`. -/
theorem profileRampLink_sharp_evenDyadic_of_le (P : ParamsQ) (hP : P.Valid) {K : ℝ}
    (hK : (166 / 100 : ℝ) ≤ K) (hprof : P.prof = Family.evenDyadic.designProfile)
    (hlam : P.lam = Family.evenDyadic.lamStar) (hwL : 100 * P.w ≤ P.LL) :
    B Family.evenDyadic.Cconst (vDesign P)
      ≤ B Family.evenDyadic.Cconst (vProfile P) + K * (P.w / P.LB) := by
  have hwL0 : 0 ≤ P.w / P.LB := div_nonneg hP.w_pos.le (mul_pos hP.lam_pos hP.LL_pos).le
  have hprof' : P.prof = designProfileEvenDyad12 := hprof
  have hlamF : P.lam = lamStarEvenDyad12 := hlam
  have h := profileRampLink_sharp_evendyad12 hP hprof' hlamF hwL
  rw [w_div_LL_eq hP] at h
  have hlam' : P.lam = 1.0955998422 := hlamF
  rw [hlam'] at h
  show B CfamEvenDyadic (vDesign P) ≤ B CfamEvenDyadic (vProfile P) + K * (P.w / P.LB)
  have h1 : (151 / 100 : ℝ) * (1.0955998422 * (P.w / P.LB)) ≤ 166 / 100 * (P.w / P.LB) := by
    nlinarith
  have h2 : (166 / 100 : ℝ) * (P.w / P.LB) ≤ K * (P.w / P.LB) :=
    mul_le_mul_of_nonneg_right hK hwL0
  linarith

/-- **`profileRampLink_sharp`, branch `evenQle`** — `rampSharpK Family.evenQle = 124/100`. -/
theorem profileRampLink_sharp_evenQle (P : ParamsQ) (hP : P.Valid)
    (hprof : P.prof = Family.evenQle.designProfile) (hlam : P.lam = Family.evenQle.lamStar)
    (hwL : 100 * P.w ≤ P.LL) :
    B Family.evenQle.Cconst (vDesign P)
      ≤ B Family.evenQle.Cconst (vProfile P) + (124 / 100) * (P.w / P.LB) :=
  profileRampLink_sharp_evenQle_of_le P hP le_rfl hprof hlam hwL

/-- **`profileRampLink_sharp`, branch `oddQle`** — `rampSharpK Family.oddQle = 124/100`.
`Family.oddQle` shares `designProfile`, `lamStar` and `Cconst` with `Family.evenQle`. -/
theorem profileRampLink_sharp_oddQle (P : ParamsQ) (hP : P.Valid)
    (hprof : P.prof = Family.oddQle.designProfile) (hlam : P.lam = Family.oddQle.lamStar)
    (hwL : 100 * P.w ≤ P.LL) :
    B Family.oddQle.Cconst (vDesign P)
      ≤ B Family.oddQle.Cconst (vProfile P) + (124 / 100) * (P.w / P.LB) :=
  profileRampLink_sharp_evenQle_of_le P hP le_rfl hprof hlam hwL

/-- **`profileRampLink_sharp`, branch `evenDyadic`** —
`rampSharpK Family.evenDyadic = 166/100`. -/
theorem profileRampLink_sharp_evenDyadic (P : ParamsQ) (hP : P.Valid)
    (hprof : P.prof = Family.evenDyadic.designProfile)
    (hlam : P.lam = Family.evenDyadic.lamStar) (hwL : 100 * P.w ≤ P.LL) :
    B Family.evenDyadic.Cconst (vDesign P)
      ≤ B Family.evenDyadic.Cconst (vProfile P) + (166 / 100) * (P.w / P.LB) :=
  profileRampLink_sharp_evenDyadic_of_le P hP le_rfl hprof hlam hwL

/-- **`profileRampLink_sharp`, branch `oddDyadic`** — `rampSharpK Family.oddDyadic = 166/100`.
`Family.oddDyadic` shares `designProfile`, `lamStar` and `Cconst` with `Family.evenDyadic`. -/
theorem profileRampLink_sharp_oddDyadic (P : ParamsQ) (hP : P.Valid)
    (hprof : P.prof = Family.oddDyadic.designProfile)
    (hlam : P.lam = Family.oddDyadic.lamStar) (hwL : 100 * P.w ≤ P.LL) :
    B Family.oddDyadic.Cconst (vDesign P)
      ≤ B Family.oddDyadic.Cconst (vProfile P) + (166 / 100) * (P.w / P.LB) :=
  profileRampLink_sharp_evenDyadic_of_le P hP le_rfl hprof hlam hwL

/-- **THE SHARP §11 LINK at the design profiles, in the budget's `w/L` form**: for a valid design
point with `prof = designProfile F`, `λ = λ*_F` and `100w ≤ ℒ`,
`B(v_design) ≤ B(v_profile) + K_F·(w/L)` with `K_qle = 0.85`, `K_dyad = 1.07`,
`K_evenQle = K_oddQle = 1.24` and `K_evenDyadic = K_oddDyadic = 1.66`.

**PROVED IN ALL SIX BRANCHES.** Each branch cites a profile-specific ramp lemma: the two full
families use `profileRampLink_sharp_qle` / `profileRampLink_sharp_dyadic` (`ZetaQ/RampLink.lean`,
about `designProfileQle` / `designProfileDyadic` at `C = π⁴/18` / `2π⁴/27`), and the four
parity families use §7b's `profileRampLink_sharp_evenq10` / `profileRampLink_sharp_evendyad12`,
about the two REFIT design profiles `designProfileEvenQ10` (degree 10) and
`designProfileEvenDyad12` (degree 12) at `C = π⁴/9` and `4π⁴/27`. -/
theorem profileRampLink_sharp (F : Family) (P : ParamsQ) (hP : P.Valid)
    (hprof : P.prof = F.designProfile) (hlam : P.lam = F.lamStar) (hwL : 100 * P.w ≤ P.LL) :
    B F.Cconst (vDesign P) ≤ B F.Cconst (vProfile P) + rampSharpK F * (P.w / P.LB) := by
  have hwL0 : 0 ≤ P.w / P.LB := div_nonneg hP.w_pos.le (mul_pos hP.lam_pos hP.LL_pos).le
  cases F with
  | qle =>
    have h := profileRampLink_sharp_qle hP hprof hlam hwL
    rw [w_div_LL_eq hP] at h
    have hlam' : P.lam = 1.2507321515 := hlam
    rw [hlam'] at h
    simp only [Family.Cconst, rampSharpK]
    have : (675 / 1000 : ℝ) * (1.2507321515 * (P.w / P.LB)) ≤ 85 / 100 * (P.w / P.LB) := by
      nlinarith
    linarith
  | dyadic =>
    have h := profileRampLink_sharp_dyadic hP hprof hlam hwL
    rw [w_div_LL_eq hP] at h
    have hlam' : P.lam = 1.1931581210 := hlam
    rw [hlam'] at h
    simp only [Family.Cconst, rampSharpK]
    have : (8925 / 10000 : ℝ) * (1.1931581210 * (P.w / P.LB)) ≤ 107 / 100 * (P.w / P.LB) := by
      nlinarith
    linarith
  -- Corollary 3: §7b's two REFIT parity links, converted to `w/L` above.
  | evenQle => exact profileRampLink_sharp_evenQle P hP hprof hlam hwL
  | oddQle => exact profileRampLink_sharp_oddQle P hP hprof hlam hwL
  | evenDyadic => exact profileRampLink_sharp_evenDyadic P hP hprof hlam hwL
  | oddDyadic => exact profileRampLink_sharp_oddDyadic P hP hprof hlam hwL
  | evenQleR =>
    have hlam' : P.lam = 1.2507321515 := hlam
    have hC2 : CfamEven ≤ 10.824 := by
      have h := Cfam_le
      unfold CfamEven
      unfold Cfam at h
      linarith
    have hCpos : (0 : ℝ) ≤ CfamEven := by unfold CfamEven; positivity
    have h := profileRampLink_sharp_qle_twoC hP hprof hlam hwL hCpos hC2
    rw [w_div_LL_eq hP, hlam'] at h
    simp only [Family.Cconst, rampSharpK]
    have : (81 / 100 : ℝ) * (1.2507321515 * (P.w / P.LB)) ≤ 110 / 100 * (P.w / P.LB) := by
      nlinarith
    linarith
  | oddQleR =>
    have hlam' : P.lam = 1.2507321515 := hlam
    have hC2 : CfamEven ≤ 10.824 := by
      have h := Cfam_le
      unfold CfamEven
      unfold Cfam at h
      linarith
    have hCpos : (0 : ℝ) ≤ CfamEven := by unfold CfamEven; positivity
    have h := profileRampLink_sharp_qle_twoC hP hprof hlam hwL hCpos hC2
    rw [w_div_LL_eq hP, hlam'] at h
    simp only [Family.Cconst, rampSharpK]
    have : (81 / 100 : ℝ) * (1.2507321515 * (P.w / P.LB)) ≤ 110 / 100 * (P.w / P.LB) := by
      nlinarith
    linarith
  | evenDyadicR =>
    have hlam' : P.lam = 1.1931581210 := hlam
    have hC2 : CfamEvenDyadic ≤ 14.432 := by
      have h := CfamDyadic_le
      unfold CfamEvenDyadic
      unfold CfamDyadic at h
      linarith
    have hCpos : (0 : ℝ) ≤ CfamEvenDyadic := by unfold CfamEvenDyadic; positivity
    have h := profileRampLink_sharp_dyadic_twoC hP hprof hlam hwL hCpos hC2
    rw [w_div_LL_eq hP, hlam'] at h
    simp only [Family.Cconst, rampSharpK]
    have : (104 / 100 : ℝ) * (1.1931581210 * (P.w / P.LB)) ≤ 130 / 100 * (P.w / P.LB) := by
      nlinarith
    linarith
  | oddDyadicR =>
    have hlam' : P.lam = 1.1931581210 := hlam
    have hC2 : CfamEvenDyadic ≤ 14.432 := by
      have h := CfamDyadic_le
      unfold CfamEvenDyadic
      unfold CfamDyadic at h
      linarith
    have hCpos : (0 : ℝ) ≤ CfamEvenDyadic := by unfold CfamEvenDyadic; positivity
    have h := profileRampLink_sharp_dyadic_twoC hP hprof hlam hwL hCpos hC2
    rw [w_div_LL_eq hP, hlam'] at h
    simp only [Family.Cconst, rampSharpK]
    have : (104 / 100 : ℝ) * (1.1931581210 * (P.w / P.LB)) ≤ 130 / 100 * (P.w / P.LB) := by
      nlinarith
    linarith

/-- `w = 1` at the design of record for `r ≥ 3`, `ℒ ≥ 1` (the clamp `w = max(1, ℒ^{(3−r)/2})`). -/
theorem w_eq_one_of_design {F : Family} {r ε Q : ℝ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε Q P) (hr : 3 ≤ r) (hLL1 : 1 ≤ P.LL) : P.w = 1 := by
  obtain ⟨-, -, -, -, hw, -⟩ := hdes
  rw [hw]
  unfold wDesign wStar
  exact max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))

/-- **THE SHARP §11 LINK AT THE DESIGN OF RECORD**: for `DesignOfRecord F r ε Q P` with `r ≥ 3`
(so `w = 1`) and `ℒ ≥ 100`, `B(v_design) ≤ B(v_profile) + K_F·(w/L)`, `K_qle = 0.85`,
`K_dyad = 1.07` — both inside the budget's ramp row `L₃ = 6w/L`. -/
theorem profileRampLink_design (F : Family) (r ε Q : ℝ) (P : ParamsQ)
    (hdes : DesignOfRecord F r ε Q P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL) :
    B F.Cconst (vDesign P) ≤ B F.Cconst (vProfile P) + rampSharpK F * (P.w / P.LB) := by
  have hP : P.Valid := hdes.1
  have hlam : P.lam = F.lamStar := hdes.2.2.2.1
  have hprof : P.prof = F.designProfile := hdes.2.2.2.2.2.2.2.2.2.2.2
  have hw : P.w = 1 := w_eq_one_of_design hdes hr (by linarith)
  exact profileRampLink_sharp F P hP hprof hlam (by rw [hw]; linarith)

/-- the same with the uniform constant `3` (the "ideal margin"). -/
theorem profileRampLink_design_three (F : Family) (r ε Q : ℝ) (P : ParamsQ)
    (hdes : DesignOfRecord F r ε Q P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL) :
    B F.Cconst (vDesign P) ≤ B F.Cconst (vProfile P) + 3 * (P.w / P.LB) := by
  have h := profileRampLink_design F r ε Q P hdes hr hLL
  have hP : P.Valid := hdes.1
  have hwL0 : 0 ≤ P.w / P.LB := div_nonneg hP.w_pos.le (mul_pos hP.lam_pos hP.LL_pos).le
  have hK := rampSharpK_le F
  nlinarith

/-- **the ramp cost sits inside the budget's ramp row `L₃ = 6w/L`**:
`B(v_design) ≤ B(v_profile) + L₃ P` at the design of record. -/
theorem profileRampLink_design_L₃ (F : Family) (r ε Q : ℝ) (P : ParamsQ)
    (hdes : DesignOfRecord F r ε Q P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL) :
    B F.Cconst (vDesign P) ≤ B F.Cconst (vProfile P) + L₃ P := by
  have h := profileRampLink_design_three F r ε Q P hdes hr hLL
  have hP : P.Valid := hdes.1
  have hwL0 : 0 ≤ P.w / P.LB := div_nonneg hP.w_pos.le (mul_pos hP.lam_pos hP.LL_pos).le
  have e : L₃ P = 6 * (P.w / P.LB) := by unfold L₃ cRamp; ring
  rw [e]
  linarith

end Payoff
end ZetaQ


end
