/-
Node K8a-2 (L7_3, round 2): the saving, in the units of the master inequality's main term. With
`gQ(ℒα)·ℒ = (aL)²·ψ_design(α)` (the relation behind `FrobAssembly.intervalIntegral_gQ_mul_eq`,
`∫_0^L g(y)y dy = ½ℒ(aL)²(K0 + K1)`), `ℓ_K/ℒ = 1 + O(log ℒ/ℒ)` and `log 𝒳 = λℒ`:
`2·Sav = 2(1 − C₁/log Q)(T/2π)ℒ(aL)²∫_{1+κ}^{λ−1/ℒ}(α − 1 − κ)ψ_d(α)dα ≥ (T/2π)ℒ(aL)²(K1 − K1kill − η)`
eventually, because `K1 − K1kill = ∫_{|α|>1}(|α| − 1)ψ = 2∫_1^λ(α − 1)ψ` and `ψ_d` is bounded (`psi_vDesign_le`).
Draft: sec_lemmaK (d), "the subtracted term `U∫g(s − ℓ_K)₊` is otherwise exact"; the kink shift `log(2πK)/ℒ`, the strip
`σ_g` and `η_P` of eq:EK. Dependencies: trunk `FrobAssembly.gQ_eq_psi_vDesign` (change of variables),
`HFrob.psi_vDesign_le`, `RampLink.vProfile_le_four_div`. Difficulty: M. PROVED (round 2).
-/
import ZetaShell.LemmaK.LK_K8a_Defs

noncomputable section
open Filter MeasureTheory Set

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaQ.Payoff

/-- `ψ` is even (translation invariance of Lebesgue measure). -/
theorem psi_neg' (v : ℝ → ℝ) (α : ℝ) : psi v (-α) = psi v α := by
  rw [psi_shift α]
  unfold psi
  congr 1; funext t
  rw [sub_neg_eq_add, mul_comm]

/-- `∫ ψ(α)(α − 1)₊ = (K1 − K1kill)/2`. -/
theorem integral_psi_posPart {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) :
    ∫ α, psi v α * max (α - 1) 0 = (K1 v - K1kill v) / 2 := by
  have hmeas : AEStronglyMeasurable (psi v) volume := (psi_integrable hv).aestronglyMeasurable
  have hint1 : Integrable (fun α => psi v α * max (α - 1) 0) := by
    refine (absPsi_integrable hv).mono'
      (hmeas.mul (Continuous.aestronglyMeasurable (by fun_prop))) (Filter.Eventually.of_forall fun α => ?_)
    have hp := psi_nonneg hv α
    have hm : 0 ≤ max (α - 1) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hm)]
    have : max (α - 1) 0 ≤ |α| := max_le (by linarith [le_abs_self α]) (abs_nonneg α)
    nlinarith
  have hint2 : Integrable (fun α => psi v α * max (-α - 1) 0) := by
    refine (absPsi_integrable hv).mono'
      (hmeas.mul (Continuous.aestronglyMeasurable (by fun_prop))) (Filter.Eventually.of_forall fun α => ?_)
    have hp := psi_nonneg hv α
    have hm : 0 ≤ max (-α - 1) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hm)]
    have : max (-α - 1) 0 ≤ |α| := max_le (by linarith [neg_abs_le α]) (abs_nonneg α)
    nlinarith
  have hneg : ∫ α, psi v α * max (-α - 1) 0 = ∫ α, psi v α * max (α - 1) 0 := by
    have h := integral_neg_eq_self (fun α => psi v α * max (α - 1) 0) volume
    simp only [psi_neg'] at h
    rw [← h]
  have hpt : ∀ α, psi v α * max (|α| - 1) 0 = psi v α * max (α - 1) 0 + psi v α * max (-α - 1) 0 := by
    intro α
    rcases le_total 0 α with h | h
    · rw [abs_of_nonneg h, max_eq_right (by linarith : -α - 1 ≤ 0)]; ring
    · rw [abs_of_nonpos h, max_eq_right (by linarith : α - 1 ≤ 0)]; ring
  have hind : (fun α => psi v α * max (|α| - 1) 0)
      = Set.indicator {α : ℝ | 1 < |α|} (fun α => |α| * psi v α - psi v α) := by
    funext α
    by_cases h : 1 < |α|
    · rw [Set.indicator_of_mem (show α ∈ {α : ℝ | 1 < |α|} from h), max_eq_left (by linarith)]; ring
    · rw [Set.indicator_of_notMem (show α ∉ {α : ℝ | 1 < |α|} from h),
        max_eq_right (by linarith [not_lt.mp h])]; ring
  have hms : MeasurableSet {α : ℝ | 1 < |α|} := measurableSet_lt measurable_const continuous_abs.measurable
  have habs : ∫ α, psi v α * max (|α| - 1) 0 = K1 v - K1kill v := by
    rw [hind, integral_indicator hms, integral_sub (absPsi_integrable hv).integrableOn
      (psi_integrable hv).integrableOn]
    rfl
  have hsum : ∫ α, psi v α * max (|α| - 1) 0
      = (∫ α, psi v α * max (α - 1) 0) + ∫ α, psi v α * max (-α - 1) 0 := by
    simp_rw [hpt]; exact integral_add hint1 hint2
  rw [hneg] at hsum
  linarith

/-- `ψ_design ≤ 6` (from `ψ_d ≤ c²ψ_p`, `c ≤ 2`, `v_p ≤ 4/(3λ)`). -/
theorem psi_vDesign_le_six {P : ParamsQ} (hP : P.Valid) (hlam1 : 1 ≤ P.lam)
    (hc : profMass P / (P.lam * P.aQ) ≤ 2) (α : ℝ) : psi (vDesign P) α ≤ 6 := by
  have h1 := HFrob.psi_vDesign_le hP α
  have hint : Integrable (fun t => vProfile P t * vProfile P (t - α)) := by
    refine Integrable.bdd_mul (c := 1 / profMass P) ((vProfile_integrable P).comp_sub_right α)
      (vProfile_integrable P).aestronglyMeasurable (ae_of_all _ (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (vProfile_nonneg hP t)]
    exact vProfile_le hP t
  have hp : psi (vProfile P) α ≤ 4 / 3 := by
    unfold psi
    calc ∫ t, vProfile P t * vProfile P (t - α) ≤ ∫ t, vProfile P t * (4 / 3) := by
          apply integral_mono hint ((vProfile_integrable P).mul_const _)
          intro t
          apply mul_le_mul_of_nonneg_left _ (vProfile_nonneg hP t)
          have h4 := vProfile_le_four_div hP (t - α)
          have : 4 / (3 * P.lam) ≤ 4 / 3 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
          linarith
      _ = 4 / 3 := by rw [integral_mul_const, integral_vProfile hP, one_mul]
  have hc0 : 0 ≤ profMass P / (P.lam * P.aQ) := by
    have := profMass_pos hP; have := hP.lam_pos; have := hP.aQ_pos; positivity
  have hc2 : (profMass P / (P.lam * P.aQ)) ^ 2 ≤ 4 := by nlinarith
  have hp0 : 0 ≤ psi (vProfile P) α := psi_nonneg (vProfile_admissible hP) α
  have : (profMass P / (P.lam * P.aQ)) ^ 2 * psi (vProfile P) α ≤ 4 * (4 / 3) :=
    mul_le_mul hc2 hp (hp0) (by norm_num)
  linarith

set_option maxHeartbeats 1000000 in
/-- **K8a-2.** -/
theorem killed_saving (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (C₁ η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K1 (vDesign P) - K1kill (vDesign P) - η)
        ≤ 2 * Sav C₁ Qn P := by
  set K : ℝ := 1000 + 8 * |C₁| / η + 96 / η + 2048 * Real.pi / η ^ 2 + 2 * |C₁| with hKdef
  have hK0a : 0 ≤ 8 * |C₁| / η := by positivity
  have hK0b : 0 ≤ 96 / η := by positivity
  have hK0c : 0 ≤ 2048 * Real.pi / η ^ 2 := by positivity
  have hK0d : 0 ≤ 2 * |C₁| := by positivity
  have hK1 : (1 : ℝ) ≤ K := by linarith
  filter_upwards [FrobAssembly.design_regime Family.qle r ε hr hε K hK1,
    FrobAssembly.design_basic Family.qle r ε hr hε, reg_eventually Family.qle r ε hr hε,
    eventually_ge_atTop 1] with Qn hreg hbas hregQ hQn1
  intro P hdes
  obtain ⟨hlogK, hTK, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam1, hw8, hQn2⟩ := hbas P hdes
  obtain ⟨hP, hw, -, hs8, hs0Q, -⟩ := hregQ P hdes
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hTpos : 0 < P.T := hP.T_pos
  have hpi := Real.pi_pos
  have hlogQ : Real.log Qn ≤ P.LL := LL_ge_log_of_design hdes (by omega)
  have hadm := vDesign_admissible hP
  have hlam2 : P.lam < 2 := hP.lam_lt_two
  have hs' : K1 (vDesign P) - K1kill (vDesign P) ≤ 2 := by
    have h1 := K1_le_two hadm hlam2
    have h2 : 0 ≤ K1kill (vDesign P) := by
      unfold K1kill; exact integral_nonneg (fun α => psi_nonneg hadm α)
    linarith
  have hs'0 : 0 ≤ K1 (vDesign P) - K1kill (vDesign P) := by
    have h := integral_psi_posPart hadm
    have h0 : 0 ≤ ∫ α, psi (vDesign P) α * max (α - 1) 0 :=
      integral_nonneg (fun α => mul_nonneg (psi_nonneg hadm α) (le_max_right _ _))
    linarith
  -- the constant `a₁ = 1 − C₁/log Q`
  have hlogQpos : 0 < Real.log (Qn : ℝ) := by linarith
  have hC1 : |C₁ / Real.log (Qn : ℝ)| ≤ η / 8 := by
    rw [abs_div, abs_of_pos hlogQpos, div_le_iff₀ hlogQpos]
    have : 8 * |C₁| / η ≤ Real.log Qn := by linarith
    rw [div_le_iff₀ hη] at this
    linarith
  have hC1' : |C₁ / Real.log (Qn : ℝ)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hlogQpos, div_le_iff₀ hlogQpos]
    linarith
  set a₁ : ℝ := 1 - C₁ / Real.log (Qn : ℝ) with ha₁
  have ha₁half : 1 / 2 ≤ a₁ := by rw [ha₁]; linarith [(abs_le.mp hC1').2]
  have ha₁lo : 1 - η / 8 ≤ a₁ := by rw [ha₁]; linarith [(abs_le.mp hC1).2]
  have ha₁hi : a₁ ≤ 1 + η / 8 := by rw [ha₁]; linarith [(abs_le.mp hC1).1]
  -- `ℓ_K = ℒ + log(2πℒ)`
  set L2 : ℝ := Real.log (2 * Real.pi * P.LL) with hL2
  have hℓ : ellK P.Q P.T = P.LL + L2 := by
    unfold ellK Lc
    show Real.log (P.Q * P.T * P.LL) = P.LL + L2
    have hQT : 0 < P.Q * P.T / (2 * Real.pi) := by
      have : 0 < P.Q := by rw [hQ]; exact_mod_cast (show 0 < Qn by omega)
      positivity
    rw [show P.Q * P.T * P.LL = (P.Q * P.T / (2 * Real.pi)) * (2 * Real.pi * P.LL) by field_simp,
      Real.log_mul hQT.ne' (by positivity)]
    rfl
  have hL20 : 0 ≤ L2 := by
    have h3 := Real.pi_gt_three
    have : (1 : ℝ) ≤ 2 * Real.pi * P.LL := by nlinarith only [h3, hLL30]
    exact Real.log_nonneg this
  have hL2le : 2 * L2 ≤ η / 8 * P.LL := by
    have h1 := Real.log_le_rpow_div (show 0 ≤ 2 * Real.pi * P.LL by positivity) (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h1
    have hbig : 2048 * Real.pi / η ^ 2 ≤ P.LL := by linarith
    rw [div_le_iff₀ (by positivity)] at hbig
    have h2 : 2 * Real.pi * P.LL ≤ (η * P.LL / 32) ^ 2 := by nlinarith
    have h3 : Real.sqrt (2 * Real.pi * P.LL) ≤ η * P.LL / 32 := by
      calc Real.sqrt (2 * Real.pi * P.LL) ≤ Real.sqrt ((η * P.LL / 32) ^ 2) := Real.sqrt_le_sqrt h2
        _ = η * P.LL / 32 := Real.sqrt_sq (by positivity)
    rw [hL2]; linarith
  have hlam12 : 12 * (P.lam - 1) ≤ η / 8 * P.LL := by
    have hbig : 96 / η ≤ P.LL := by linarith
    rw [div_le_iff₀ hη] at hbig
    linarith
  -- (c) the saving lives on the out-zone: `Sav = ∫ g·savWeight`
  have hℓs0 : P.s0 ≤ ellK P.Q P.T := by
    have h1 : P.s0 ≤ Real.log P.Q := hs0Q
    rw [hQ] at h1
    rw [hℓ]; linarith
  have hSav : Sav C₁ Qn P = ∫ s, P.gQ s * savWeight C₁ Qn P s := by
    unfold Sav
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have hin : s ∈ inZone P := by simpa using hs
    have hs1 : |s| ≤ P.s0 := hin
    have hs2 : s ≤ ellK P.Q P.T := le_trans (le_trans (le_abs_self s) hs1) hℓs0
    unfold savWeight
    rw [max_eq_right (by linarith)]
    ring
  -- (d) change of variables `s = αℒ`
  set m : ℝ → ℝ := fun α => max (α * P.LL - ellK P.Q P.T) 0
    * (if α * P.LL ≤ Real.log P.XQ - 1 then 1 else 0) with hm
  set u : ℝ := a₁ * (P.T / (2 * Real.pi)) with hu
  have hcomp := MeasureTheory.Measure.integral_comp_mul_right (fun s => P.gQ s * savWeight C₁ Qn P s) P.LL
  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hLL0), eq_inv_mul_iff_mul_eq₀ hLL0.ne'] at hcomp
  have e1 : ∀ α : ℝ, P.gQ (α * P.LL) * savWeight C₁ Qn P (α * P.LL)
      = ((P.aQ * P.lam) ^ 2 * P.LL * u) * (psi (vDesign P) α * m α) := by
    intro α
    rw [FrobAssembly.gQ_eq_psi_vDesign hP hw α]
    unfold savWeight
    rw [hm, hu, ha₁]
    ring
  simp_rw [e1] at hcomp
  rw [integral_const_mul] at hcomp
  -- hcomp : ℒ * ((aλ)²ℒu ∫ψm) = ∫ g savW
  -- (e) the pointwise lower bound
  have hψ6 : ∀ α, psi (vDesign P) α ≤ 6 := by
    have hcle := HFrob.c_le hP hlam1
    have hwLL : P.w / P.LL ≤ 1 / 4 := by
      rw [div_le_iff₀ hLL0]
      have h := mul_lt_mul_of_pos_right hlam2 hLL0
      have hLB' : P.LB = P.lam * P.LL := rfl
      linarith
    exact psi_vDesign_le_six hP hlam1 (by linarith)
  have hlogX : Real.log P.XQ = P.LB := by unfold ParamsQ.XQ; exact Real.log_exp _
  have hLBdef : P.LB = P.lam * P.LL := rfl
  set lo : ℝ := P.lam - 1 / P.LL with hlo
  have hpt : ∀ α, P.LL * (psi (vDesign P) α * max (α - 1) 0) - L2 * psi (vDesign P) α
      - 6 * P.LL * (P.lam - 1) * Set.indicator (Set.Ioc lo P.lam) (fun _ => (1 : ℝ)) α
      ≤ psi (vDesign P) α * m α := by
    intro α
    have hp := psi_nonneg hadm α
    have hmdef : m α = max (α * P.LL - ellK P.Q P.T) 0 * (if α * P.LL ≤ Real.log P.XQ - 1 then 1 else 0) := rfl
    by_cases hin : α * P.LL ≤ Real.log P.XQ - 1
    · rw [hmdef, if_pos hin, mul_one]
      have hind0 : 0 ≤ Set.indicator (Set.Ioc lo P.lam) (fun _ => (1 : ℝ)) α :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) α
      have hc : 0 ≤ 6 * P.LL * (P.lam - 1) := by
        have : 0 ≤ P.lam - 1 := by linarith
        positivity
      have hmx : P.LL * max (α - 1) 0 - L2 ≤ max (α * P.LL - ellK P.Q P.T) 0 := by
        rcases le_total α 1 with h | h
        · rw [max_eq_right (by linarith : α - 1 ≤ 0)]; linarith [le_max_right (α * P.LL - ellK P.Q P.T) 0]
        · rw [max_eq_left (by linarith : 0 ≤ α - 1), hℓ]
          have := le_max_left (α * P.LL - (P.LL + L2)) 0
          linarith
      have := mul_le_mul_of_nonneg_left hmx hp
      linarith [mul_nonneg hc hind0]
    · rw [hmdef, if_neg hin, mul_zero, mul_zero]
      push_neg at hin
      rw [hlogX] at hin
      by_cases hα : α ≤ P.lam
      · have hmem : α ∈ Set.Ioc lo P.lam := by
          refine ⟨?_, hα⟩
          rw [hLBdef] at hin
          have h1 : (P.lam - 1 / P.LL) * P.LL < α * P.LL := by
            rw [sub_mul, div_mul_cancel₀ _ hLL0.ne']; linarith
          exact lt_of_mul_lt_mul_right h1 hLL0.le
        rw [Set.indicator_of_mem hmem]
        have h1 : max (α - 1) 0 ≤ P.lam - 1 := max_le (by linarith) (by linarith)
        have h2 : psi (vDesign P) α * max (α - 1) 0 ≤ 6 * (P.lam - 1) :=
          mul_le_mul (hψ6 α) h1 (le_max_right _ _) (by norm_num)
        have := mul_le_mul_of_nonneg_left h2 hLL0.le
        linarith [mul_nonneg hL20 hp]
      · push_neg at hα
        have hz : psi (vDesign P) α = 0 := psi_supp hadm (by
          rw [abs_of_pos (by linarith : (0:ℝ) < α)]; exact hα)
        rw [hz]
        have hind0 : 0 ≤ Set.indicator (Set.Ioc lo P.lam) (fun _ => (1 : ℝ)) α :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) α
        have hc : 0 ≤ 6 * P.LL * (P.lam - 1) := by
          have : 0 ≤ P.lam - 1 := by linarith
          positivity
        have := mul_nonneg hc hind0
        simp only [zero_mul, mul_zero, sub_zero, zero_sub]
        linarith
  -- integrability
  have hmeasm : Measurable m := by
    rw [hm]
    exact (by fun_prop : Measurable fun α => max (α * P.LL - ellK P.Q P.T) 0).mul
      (Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const measurable_const)
  have hmbd : ∀ α, |m α| ≤ P.LL * |α| + |ellK P.Q P.T| := by
    intro α
    have h0 : 0 ≤ m α := by
      rw [hm]; exact mul_nonneg (le_max_right _ _) (by split_ifs <;> norm_num)
    rw [abs_of_nonneg h0, hm]
    simp only
    split_ifs
    · rw [mul_one]
      apply max_le _ (by positivity)
      have h := mul_le_mul_of_nonneg_left (le_abs_self α) hLL0.le
      linarith [neg_abs_le (ellK P.Q P.T)]
    · rw [mul_zero]; positivity
  have hIint : Integrable (fun α => psi (vDesign P) α * m α) := by
    refine (((absPsi_integrable hadm).const_mul P.LL).add ((psi_integrable hadm).const_mul |ellK P.Q P.T|)).mono'
      ((psi_integrable hadm).aestronglyMeasurable.mul hmeasm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun α => ?_)
    have hp := psi_nonneg hadm α
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    have := mul_le_mul_of_nonneg_left (hmbd α) hp
    show _ ≤ P.LL * (|α| * psi (vDesign P) α) + |ellK P.Q P.T| * psi (vDesign P) α
    linarith
  have hposInt : Integrable (fun α => psi (vDesign P) α * max (α - 1) 0) := by
    refine (absPsi_integrable hadm).mono'
      ((psi_integrable hadm).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop)))
      (Filter.Eventually.of_forall fun α => ?_)
    have hp := psi_nonneg hadm α
    have hm0 : 0 ≤ max (α - 1) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hm0)]
    have : max (α - 1) 0 ≤ |α| := max_le (by linarith [le_abs_self α]) (abs_nonneg α)
    nlinarith
  have hindInt : Integrable (Set.indicator (Set.Ioc lo P.lam) (fun _ => (1 : ℝ))) :=
    ((continuous_const (y := (1 : ℝ))).integrableOn_Icc (a := lo) (b := P.lam)).mono_set
      Set.Ioc_subset_Icc_self |>.integrable_indicator measurableSet_Ioc
  have i1 : Integrable (fun α => P.LL * (psi (vDesign P) α * max (α - 1) 0)) := hposInt.const_mul _
  have i2 : Integrable (fun α => L2 * psi (vDesign P) α) := (psi_integrable hadm).const_mul _
  have i3 : Integrable (fun α => 6 * P.LL * (P.lam - 1) * Set.indicator (Set.Ioc lo P.lam) (fun _ => (1 : ℝ)) α) :=
    hindInt.const_mul _
  have hlowInt : Integrable (fun α => P.LL * (psi (vDesign P) α * max (α - 1) 0) - L2 * psi (vDesign P) α
      - 6 * P.LL * (P.lam - 1) * Set.indicator (Set.Ioc lo P.lam) (fun _ => (1 : ℝ)) α) := by
    exact (i1.sub i2).sub i3
  have hI : P.LL * ((K1 (vDesign P) - K1kill (vDesign P)) / 2) - L2 - 6 * (P.lam - 1)
      ≤ ∫ α, psi (vDesign P) α * m α := by
    have hmono := integral_mono hlowInt hIint hpt
    have e1 := integral_sub (μ := volume)
      (f := fun α => P.LL * (psi (vDesign P) α * max (α - 1) 0) - L2 * psi (vDesign P) α)
      (g := fun α => 6 * P.LL * (P.lam - 1) * Set.indicator (Set.Ioc lo P.lam) (fun _ => (1 : ℝ)) α)
      (by exact i1.sub i2) i3
    have e2 := integral_sub (μ := volume)
      (f := fun α => P.LL * (psi (vDesign P) α * max (α - 1) 0)) (g := fun α => L2 * psi (vDesign P) α) i1 i2
    have e3 := integral_const_mul (μ := volume) P.LL (fun α => psi (vDesign P) α * max (α - 1) 0)
    have e4 := integral_const_mul (μ := volume) L2 (fun α => psi (vDesign P) α)
    have e5 := integral_const_mul (μ := volume) (6 * P.LL * (P.lam - 1))
      (fun α => Set.indicator (Set.Ioc lo P.lam) (fun _ => (1 : ℝ)) α)
    have e6 := integral_indicator_const (μ := volume) (1 : ℝ) (measurableSet_Ioc (a := lo) (b := P.lam))
    rw [e1, e2, e3, e4, e5, e6, integral_psi_posPart hadm, psi_total hadm] at hmono
    have hle : lo ≤ P.lam := by
      have h0 : 0 < 1 / P.LL := by positivity
      linarith
    have hvol : volume.real (Set.Ioc lo P.lam) = 1 / P.LL := by
      rw [Real.volume_real_Ioc_of_le hle, hlo]
      ring
    rw [hvol, smul_eq_mul] at hmono
    have e : 6 * P.LL * (P.lam - 1) * (1 / P.LL * 1) = 6 * (P.lam - 1) := by field_simp
    rw [e] at hmono
    linarith
  -- (f) combine
  have hW : (P.aQ * P.LB) ^ 2 = (P.aQ * P.lam) ^ 2 * P.LL * P.LL := by rw [hLBdef]; ring
  have h2Sav : 2 * Sav C₁ Qn P = 2 * ((P.aQ * P.LB) ^ 2 * u * ∫ α, psi (vDesign P) α * m α) := by
    rw [hSav, ← hcomp, hW]; ring
  set s' : ℝ := K1 (vDesign P) - K1kill (vDesign P) with hs'def
  set W : ℝ := (P.aQ * P.LB) ^ 2 with hWdef
  set Uc : ℝ := P.T / (2 * Real.pi) with hUc
  have hW0 : 0 ≤ W := by positivity
  have hUc0 : 0 < Uc := by positivity
  set I : ℝ := ∫ α, psi (vDesign P) α * m α with hIdef
  rw [h2Sav]
  by_cases hη2 : η ≤ 2
  · -- a₁·(ℒs' − 2L2 − 12(λ−1)) ≥ ℒ(s' − η)
    have ha0 : 0 ≤ a₁ := by linarith
    have hY : a₁ * (P.LL * s' - 2 * L2 - 12 * (P.lam - 1)) ≥ P.LL * (s' - η) := by
      have hLs : P.LL * s' ≤ P.LL * 2 := mul_le_mul_of_nonneg_left hs' hLL0.le
      have hLs0 : 0 ≤ P.LL * s' := mul_nonneg hLL0.le hs'0
      have hηL : 0 ≤ η * P.LL := by positivity
      rcases le_total 0 (P.LL * s' - 2 * L2 - 12 * (P.lam - 1)) with hY0 | hY0
      · have h1 := mul_le_mul_of_nonneg_right ha₁lo hY0
        have hYle : P.LL * s' - 2 * L2 - 12 * (P.lam - 1) ≤ 2 * P.LL := by linarith
        have h2 := mul_le_mul_of_nonneg_left hYle (by positivity : (0 : ℝ) ≤ η / 8)
        linarith
      · have h1 := mul_le_mul_of_nonpos_right ha₁hi hY0
        have h3 := mul_le_mul_of_nonpos_right (show 1 + η / 8 ≤ 5 / 4 by linarith) hY0
        linarith
    have hI2 : 2 * I ≥ P.LL * s' - 2 * L2 - 12 * (P.lam - 1) := by linarith
    have hfin : Uc * P.LL * W * (s' - η) ≤ 2 * (W * u * I) := by
      rw [hu]
      have h1 : a₁ * (2 * I) ≥ a₁ * (P.LL * s' - 2 * L2 - 12 * (P.lam - 1)) :=
        mul_le_mul_of_nonneg_left hI2 ha0
      have h2 : Uc * W * (a₁ * (2 * I)) ≥ Uc * W * (P.LL * (s' - η)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have e1 : 2 * (W * (a₁ * Uc) * I) = Uc * W * (a₁ * (2 * I)) := by ring
      have e2 : Uc * P.LL * W * (s' - η) = Uc * W * (P.LL * (s' - η)) := by ring
      rw [e1, e2]; exact h2
    exact hfin
  · -- `η > 2 ≥ s′`: the left side is `≤ 0 ≤ 2·Sav`
    push_neg at hη2
    have hSav0 : 0 ≤ W * u * I := by
      have ha0 : 0 ≤ a₁ := by linarith
      have hI0 : 0 ≤ I := integral_nonneg (fun α => mul_nonneg (psi_nonneg hadm α) (by
        rw [hm]; exact mul_nonneg (le_max_right _ _) (by split_ifs <;> norm_num)))
      rw [hu]; positivity
    have hneg : Uc * P.LL * W * (s' - η) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith

end LemmaK
end ZetaShell
