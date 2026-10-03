/-
F1c-3c2, construction part 4 (L7_3, round 8): **the pointwise excess and its integral**.
* `FS_excess_pt`: on `[0, L + 2]`,
    `F(y)·y ≤ g·wOut·y + I₁ + I₂ + I₃ + K₂`,
  `Iₖ = K₁·1_{Rₖ}` on the three ramp intervals `R₁ = [s₀ − 1 − ρ, s₀]`, `R₂ = [s₁, s₁ + 1 + ρ]`,
  `R₃ = [α′ℒ − 1 − ρ, α′ℒ + 1]`, `K₁ = (aL + 2)·W_max·(L + 2)`, `K₂ = C(aL(V_b − ℒ) + 2V_b) + 2C(L + 2)`,
  `V_b = (1 + 4μ²)(ℒ + 2)`. Region by region: `F = 0` left of `R₁`; `F·y ≤ K₁` on each `Rₖ`; excess `≤ 2Cy` on the
  plateau `(s₀, s₁]`; `≤ K₂` on the `ℒ/s` and `Cℒ/s` stretches (`vF·y ≤ V_b`).
* generic: `integral_indicator_Icc_le` (`∫_a^b K·1_{[u,v]} ≤ K(v − u)`).
* `FS_integral_le`: `∫₀^{L+2} F·y ≤ ∫_{s₀}^{L} g·wOut·y + K₁(3ρ + 4) + K₂(L + 2)`.
-/
import ZetaShell.ShellK.LF_MajConstr3

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

/-- `W_max = C + C·c/(2m)`. -/
def WmaxS (P : ParamsQ) (μ : ℝ) : ℝ := Cfam + Cfam * ((1 + 4 * μ ^ 2) * P.LL / (2 * (μ * P.LL)))

/-- `K₁ = (aL + 2)·W_max·(L + 2)`. -/
def K1S (P : ParamsQ) (μ : ℝ) : ℝ := (P.aQ * P.LB + 2) * WmaxS P μ * (P.LB + 2)

/-- `V_b = (1 + 4μ²)(ℒ + 2)`. -/
def VbS (P : ParamsQ) (μ : ℝ) : ℝ := (1 + 4 * μ ^ 2) * (P.LL + 2)

/-- `K₂ = C(aL(V_b − ℒ) + 2V_b) + 2C(L + 2)`. -/
def K2S (P : ParamsQ) (μ : ℝ) : ℝ :=
  Cfam * (P.aQ * P.LB * (VbS P μ - P.LL) + 2 * VbS P μ) + 2 * Cfam * (P.LB + 2)

def I1S (P : ParamsQ) (μ ρ : ℝ) : ℝ → ℝ := (Icc (P.s0 - 1 - ρ) P.s0).indicator (fun _ => K1S P μ)
def I2S (P : ParamsQ) (μ ρ : ℝ) : ℝ → ℝ := (Icc (sOne P) (sOne P + 1 + ρ)).indicator (fun _ => K1S P μ)
def I3S (P : ParamsQ) (μ ρ : ℝ) : ℝ → ℝ :=
  (Icc (2497 / 1500 * P.LL - 1 - ρ) (2497 / 1500 * P.LL + 1)).indicator (fun _ => K1S P μ)

set_option maxHeartbeats 1000000 in
/-- **The pointwise excess.** -/
theorem FS_excess_pt {P : ParamsQ} (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {μ ρ : ℝ} (h : MajHyp P μ ρ)
    {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ P.LB + 2) :
    FS P μ ρ y * y ≤ P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y + I3S P μ ρ y + K2S P μ := by
  have hLL := h.LL_pos
  have hμ := h.mu_pos
  have hρ := h.rho_pos
  have hC1 := h.C_ge
  have hC0 : (0:ℝ) ≤ Cfam := by linarith
  have hs0 := h.s0_ge
  have hs0l := h.s0_le
  have hgap := h.gap
  have hL2 := h.LL_le_two
  have hsd : sOne P = Real.log P.Q + 4 := rfl
  have hm : 0 < μ * P.LL := mul_pos hμ hLL
  have hc : 0 ≤ (1 + 4 * μ ^ 2) * P.LL := by positivity
  have hg0 := hP.gQ_nonneg hw y
  have hgle := hP.gQ_le_aL hw y
  have ha0 : 0 ≤ P.aQ := by linarith [hP.a_ge]
  have hLB0 : 0 ≤ P.LB := (mul_pos hP.lam_pos hP.LL_pos).le
  have hwo := (wOut_nonneg_le hP y).1
  have hT0 : 0 ≤ P.gQ y * wOut P y * y := mul_nonneg (mul_nonneg hg0 hwo) hy0
  have hWS0 := WS_nonneg h y
  have hst0 := Real.smoothTransition.nonneg (y - P.LB)
  have hst1 := Real.smoothTransition.le_one (y - P.LB)
  have hG0 : 0 ≤ P.gQ y + 2 * (1 - Real.smoothTransition (y - P.LB)) := by linarith
  have hGle : P.gQ y + 2 * (1 - Real.smoothTransition (y - P.LB)) ≤ P.gQ y + 2 := by linarith
  have hGhat : P.gQ y + 2 * (1 - Real.smoothTransition (y - P.LB)) ≤ P.aQ * P.LB + 2 := by linarith
  have hFS := FS_eq P μ ρ y
  have hWmax0 : 0 ≤ WmaxS P μ := by unfold WmaxS; positivity
  have haL0 : 0 ≤ P.aQ * P.LB := mul_nonneg ha0 hLB0
  have hK1 : 0 ≤ K1S P μ := by unfold K1S; positivity
  have hVb : P.LL ≤ VbS P μ := by
    unfold VbS; have := mul_nonneg (sq_nonneg μ) hLL.le; have := sq_nonneg μ; linarith
  have hVb0 : 0 ≤ VbS P μ := by linarith
  have hX0 : 0 ≤ P.aQ * P.LB * (VbS P μ - P.LL) + 2 * VbS P μ :=
    add_nonneg (mul_nonneg haL0 (by linarith)) (by linarith)
  have hK2C : Cfam * (P.aQ * P.LB * (VbS P μ - P.LL) + 2 * VbS P μ) ≤ K2S P μ := by
    unfold K2S; have : 0 ≤ 2 * Cfam * (P.LB + 2) := by positivity
    linarith
  have hK2X : P.aQ * P.LB * (VbS P μ - P.LL) + 2 * VbS P μ ≤ K2S P μ := by
    have := mul_le_mul_of_nonneg_right hC1 hX0
    linarith
  have hK2L : 2 * Cfam * (P.LB + 2) ≤ K2S P μ := by
    unfold K2S; have := mul_nonneg hC0 hX0
    linarith
  have hK20 : 0 ≤ K2S P μ := le_trans (by positivity) hK2L
  have hi1 : 0 ≤ I1S P μ ρ y := by unfold I1S; exact Set.indicator_nonneg (fun _ _ => hK1) y
  have hi2 : 0 ≤ I2S P μ ρ y := by unfold I2S; exact Set.indicator_nonneg (fun _ _ => hK1) y
  have hi3 : 0 ≤ I3S P μ ρ y := by unfold I3S; exact Set.indicator_nonneg (fun _ _ => hK1) y
  -- the general bound `F·y ≤ K₁`
  have hWle : WS P μ ρ y ≤ WmaxS P μ := by
    have := WF_abs_le (ρ := ρ) (a₁ := P.s0 - 1 - ρ) (a₂ := sOne P + 1) (a₃ := 2497 / 1500 * P.LL - 1 - ρ)
      hC1 hc hm y
    exact le_trans (le_abs_self _) this
  have hgen : FS P μ ρ y * y ≤ K1S P μ := by
    rw [hFS]
    unfold K1S
    have h1 := mul_le_mul hGhat hWle hWS0 (by positivity)
    exact mul_le_mul h1 hyL hy0 (by positivity)
  -- `(g + 2)·V_b ≤ gℒ + (aL(V_b − ℒ) + 2V_b)`
  have hK2p : (P.gQ y + 2) * VbS P μ ≤ P.gQ y * P.LL + (P.aQ * P.LB * (VbS P μ - P.LL) + 2 * VbS P μ) := by
    have := mul_le_mul_of_nonneg_right hgle (by linarith : (0:ℝ) ≤ VbS P μ - P.LL)
    linarith
  rcases le_or_gt y (P.s0 - 1 - ρ) with r1 | r1
  · -- left of `R₁`: `F = 0`
    have e : WS P μ ρ y = 0 := by
      unfold WS; exact WF_eq_zero_left hρ r1 (by linarith)
    rw [hFS, e, mul_zero, zero_mul]
    linarith
  rcases le_or_gt y P.s0 with r2 | r2
  · have e : I1S P μ ρ y = K1S P μ := by unfold I1S; exact Set.indicator_of_mem (show y ∈ Icc (P.s0 - 1 - ρ) P.s0 from ⟨r1.le, r2⟩) _
    linarith
  have hin : ¬ |y| ≤ P.s0 := by rw [abs_of_nonneg hy0]; linarith
  rcases le_or_gt y (sOne P) with r3 | r3
  · -- the plateau `(s₀, s₁]`
    have e : WS P μ ρ y = Cfam := by
      unfold WS; exact WF_eq_C hρ (by linarith) (by linarith)
    have hwv : wOut P y = Cfam := by
      unfold wOut shellWt; rw [if_neg hin, if_pos (by linarith)]
    rw [hFS, e, hwv]
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGle hC0) hy0
    have h2 : 2 * Cfam * y ≤ 2 * Cfam * (P.LB + 2) := mul_le_mul_of_nonneg_left hyL (by linarith)
    linarith
  rcases le_or_gt y (sOne P + 1 + ρ) with r4 | r4
  · have e : I2S P μ ρ y = K1S P μ := by unfold I2S; exact Set.indicator_of_mem (show y ∈ Icc (sOne P) (sOne P + 1 + ρ) from ⟨r3.le, r4⟩) _
    linarith
  have hyp : 0 < y := by linarith
  have hyne : y ≠ 0 := hyp.ne'
  have hy2 : P.LL ≤ 2 * (y - 1) := by linarith
  have hV : vF ((1 + 4 * μ ^ 2) * P.LL) (μ * P.LL) y * y ≤ VbS P μ := vF_mul_le hLL hμ hy2
  have hV0 : 0 ≤ vF ((1 + 4 * μ ^ 2) * P.LL) (μ * P.LL) y * y :=
    mul_nonneg (vF_nonneg hc hm (by linarith)) hy0
  have hGV : (P.gQ y + 2 * (1 - Real.smoothTransition (y - P.LB)))
      * (vF ((1 + 4 * μ ^ 2) * P.LL) (μ * P.LL) y * y) ≤ (P.gQ y + 2) * VbS P μ :=
    mul_le_mul hGle hV hV0 (by linarith)
  rcases le_or_gt y (2497 / 1500 * P.LL - 1 - ρ) with r5 | r5
  · -- the `ℒ/s` stretch
    have e : WS P μ ρ y = vF ((1 + 4 * μ ^ 2) * P.LL) (μ * P.LL) y := by
      unfold WS; exact WF_eq_vF hρ r4.le r5
    have hwv : wOut P y = P.LL / y := by
      unfold wOut shellWt; rw [if_neg hin, if_neg (by linarith), if_pos (by linarith)]
    rw [hFS, e, hwv]
    have eT : P.gQ y * (P.LL / y) * y = P.gQ y * P.LL := by rw [mul_assoc, div_mul_cancel₀ _ hyne]
    rw [eT]
    linarith
  rcases le_or_gt y (2497 / 1500 * P.LL + 1) with r6 | r6
  · have e : I3S P μ ρ y = K1S P μ := by unfold I3S; exact Set.indicator_of_mem (show y ∈ Icc (2497 / 1500 * P.LL - 1 - ρ) (2497 / 1500 * P.LL + 1) from ⟨r5.le, r6⟩) _
    linarith
  · -- the `Cℒ/s` stretch
    have e : WS P μ ρ y = Cfam * vF ((1 + 4 * μ ^ 2) * P.LL) (μ * P.LL) y := by
      unfold WS; exact WF_eq_CvF hρ (by linarith) (by linarith)
    have hwv : wOut P y = Cfam * P.LL / y := by
      unfold wOut shellWt; rw [if_neg hin, if_neg (by linarith), if_neg (by linarith)]
    rw [hFS, e, hwv]
    have eT : P.gQ y * (Cfam * P.LL / y) * y = Cfam * (P.gQ y * P.LL) := by
      rw [mul_assoc, div_mul_cancel₀ _ hyne]; ring
    rw [eT]
    have h1 := mul_le_mul_of_nonneg_left hGV hC0
    have h4 := mul_le_mul_of_nonneg_left hK2p hC0
    linarith

/-! ### Integrals -/

theorem indicator_Icc_integrable (u v K : ℝ) : Integrable ((Icc u v).indicator (fun _ : ℝ => K)) :=
  (integrableOn_const (μ := volume) (s := Icc u v) (C := K) measure_Icc_lt_top.ne).integrable_indicator
    measurableSet_Icc

/-- **Generic.** `∫_a^b K·1_{[u,v]} ≤ K(v − u)`. -/
theorem integral_indicator_Icc_le {a b u v K : ℝ} (hab : a ≤ b) (huv : u ≤ v) (hK : 0 ≤ K) :
    (∫ y in a..b, (Icc u v).indicator (fun _ => K) y) ≤ K * (v - u) := by
  have hI := indicator_Icc_integrable u v K
  rw [intervalIntegral.integral_of_le hab]
  calc (∫ y in Ioc a b, (Icc u v).indicator (fun _ => K) y)
      ≤ ∫ y, (Icc u v).indicator (fun _ => K) y :=
        setIntegral_le_integral hI (ae_of_all _ fun y => Set.indicator_nonneg (fun _ _ => hK) y)
    _ = ∫ y in Icc u v, K := integral_indicator measurableSet_Icc
    _ = K * (v - u) := by rw [setIntegral_const, Real.volume_real_Icc_of_le huv, smul_eq_mul]; ring

theorem TS_bound {P : ParamsQ} (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (y : ℝ) :
    |P.gQ y * wOut P y * y| ≤ P.aQ * P.LB * (Cfam + P.LL) * P.LB := by
  have ha0 : 0 ≤ P.aQ := by linarith [hP.a_ge]
  have hLB0 : 0 ≤ P.LB := (mul_pos hP.lam_pos hP.LL_pos).le
  have hC0 : (0:ℝ) < Cfam := by unfold Cfam; positivity
  have hLL0 := hP.LL_pos
  by_cases hy : P.LB ≤ |y|
  · rw [hP.gQ_eq_zero hw hy, zero_mul, zero_mul, abs_zero]; positivity
  · push Not at hy
    have hg0 := hP.gQ_nonneg hw y
    have hwo := wOut_nonneg_le hP y
    rw [abs_mul, abs_mul, abs_of_nonneg hg0, abs_of_nonneg hwo.1]
    exact mul_le_mul (mul_le_mul (hP.gQ_le_aL hw y) hwo.2 hwo.1 (mul_nonneg ha0 hLB0)) hy.le (abs_nonneg _)
      (by positivity)

theorem TS_intervalIntegrable {P : ParamsQ} (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (a b : ℝ) :
    IntervalIntegrable (fun y => P.gQ y * wOut P y * y) volume a b := by
  obtain ⟨hgd, -, -⟩ := gQ_deriv_facts P hP hw
  have hmeas : Measurable (fun y => P.gQ y * wOut P y * y) :=
    (hgd.continuous.measurable.mul (wOut_measurable P)).mul measurable_id
  refine (intervalIntegrable_const (c := P.aQ * P.LB * (Cfam + P.LL) * P.LB)).mono_fun
    hmeas.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  show |P.gQ y * wOut P y * y| ≤ |P.aQ * P.LB * (Cfam + P.LL) * P.LB|
  exact le_trans (TS_bound hP hw y) (le_abs_self _)

/-- **The integral of the excess.** -/
theorem FS_integral_le {P : ParamsQ} (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {μ ρ : ℝ} (h : MajHyp P μ ρ)
    (hs0L : P.s0 ≤ P.LB) :
    (∫ y in (0 : ℝ)..(P.LB + 2), FS P μ ρ y * y)
      ≤ (∫ y in P.s0..P.LB, P.gQ y * wOut P y * y) + K1S P μ * (3 * ρ + 4) + K2S P μ * (P.LB + 2) := by
  obtain ⟨hgd, hgc, -⟩ := gQ_deriv_facts P hP hw
  have hs0 := h.s0_ge
  have hρ := h.rho_pos
  have hLB0 : 0 ≤ P.LB := by linarith
  have ha0 : 0 ≤ P.aQ := by linarith [hP.a_ge]
  have hK1 : 0 ≤ K1S P μ := by
    unfold K1S WmaxS
    have := h.LL_pos; have := h.mu_pos; have := h.C_ge
    have : 0 ≤ Cfam := by linarith
    positivity
  have hFc : Continuous (FS P μ ρ) :=
    (FF_contDiff (contDiff_one_iff_deriv.mpr ⟨hgd, hgc⟩) (mul_pos h.mu_pos h.LL_pos)).continuous
  have hTi := TS_intervalIntegrable hP hw
  have hIi : ∀ (u v a b : ℝ), IntervalIntegrable ((Icc u v).indicator (fun _ : ℝ => K1S P μ)) volume a b :=
    fun u v a b => (indicator_Icc_integrable u v _).intervalIntegrable
  have hI1 : IntervalIntegrable (I1S P μ ρ) volume 0 (P.LB + 2) := hIi _ _ _ _
  have hI2 : IntervalIntegrable (I2S P μ ρ) volume 0 (P.LB + 2) := hIi _ _ _ _
  have hI3 : IntervalIntegrable (I3S P μ ρ) volume 0 (P.LB + 2) := hIi _ _ _ _
  have hA1 : IntervalIntegrable (fun y => P.gQ y * wOut P y * y + I1S P μ ρ y) volume 0 (P.LB + 2) :=
    (hTi 0 (P.LB + 2)).add hI1
  have hA2 : IntervalIntegrable (fun y => P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y)
      volume 0 (P.LB + 2) := hA1.add hI2
  have hA3 : IntervalIntegrable
      (fun y => P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y + I3S P μ ρ y) volume 0 (P.LB + 2) :=
    hA2.add hI3
  have hmono : (∫ y in (0 : ℝ)..(P.LB + 2), FS P μ ρ y * y)
      ≤ ∫ y in (0 : ℝ)..(P.LB + 2),
          (P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y + I3S P μ ρ y + K2S P μ) :=
    intervalIntegral.integral_mono_on (by linarith) ((hFc.mul continuous_id).intervalIntegrable _ _)
      (hA3.add intervalIntegrable_const) (fun y hy => FS_excess_pt hP hw h hy.1 hy.2)
  have e1 : (∫ y in (0 : ℝ)..(P.LB + 2),
          (P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y + I3S P μ ρ y + K2S P μ))
      = (∫ y in (0 : ℝ)..(P.LB + 2), (P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y + I3S P μ ρ y))
        + ∫ _ in (0 : ℝ)..(P.LB + 2), K2S P μ :=
    intervalIntegral.integral_add hA3 intervalIntegrable_const
  have e2 : (∫ y in (0 : ℝ)..(P.LB + 2), (P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y + I3S P μ ρ y))
      = (∫ y in (0 : ℝ)..(P.LB + 2), (P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y))
        + ∫ y in (0 : ℝ)..(P.LB + 2), I3S P μ ρ y :=
    intervalIntegral.integral_add hA2 hI3
  have e3 : (∫ y in (0 : ℝ)..(P.LB + 2), (P.gQ y * wOut P y * y + I1S P μ ρ y + I2S P μ ρ y))
      = (∫ y in (0 : ℝ)..(P.LB + 2), (P.gQ y * wOut P y * y + I1S P μ ρ y))
        + ∫ y in (0 : ℝ)..(P.LB + 2), I2S P μ ρ y :=
    intervalIntegral.integral_add hA1 hI2
  have e4 : (∫ y in (0 : ℝ)..(P.LB + 2), (P.gQ y * wOut P y * y + I1S P μ ρ y))
      = (∫ y in (0 : ℝ)..(P.LB + 2), P.gQ y * wOut P y * y) + ∫ y in (0 : ℝ)..(P.LB + 2), I1S P μ ρ y :=
    intervalIntegral.integral_add (hTi 0 (P.LB + 2)) hI1
  have e5 : (∫ _ in (0 : ℝ)..(P.LB + 2), K2S P μ) = (P.LB + 2 - 0) * K2S P μ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hb1 : (∫ y in (0 : ℝ)..(P.LB + 2), I1S P μ ρ y) ≤ K1S P μ * (P.s0 - (P.s0 - 1 - ρ)) :=
    integral_indicator_Icc_le (by linarith) (by linarith) hK1
  have hb2 : (∫ y in (0 : ℝ)..(P.LB + 2), I2S P μ ρ y) ≤ K1S P μ * (sOne P + 1 + ρ - sOne P) :=
    integral_indicator_Icc_le (by linarith) (by linarith) hK1
  have hb3 : (∫ y in (0 : ℝ)..(P.LB + 2), I3S P μ ρ y)
      ≤ K1S P μ * (2497 / 1500 * P.LL + 1 - (2497 / 1500 * P.LL - 1 - ρ)) :=
    integral_indicator_Icc_le (by linarith) (by linarith) hK1
  -- `∫₀^{L+2} g·wOut·y = ∫_{s₀}^{L} g·wOut·y`
  have s1 := intervalIntegral.integral_add_adjacent_intervals (hTi 0 P.s0) (hTi P.s0 (P.LB + 2))
  have s2 := intervalIntegral.integral_add_adjacent_intervals (hTi P.s0 P.LB) (hTi P.LB (P.LB + 2))
  have z1 : (∫ y in (0 : ℝ)..P.s0, P.gQ y * wOut P y * y) = 0 := by
    have hz : EqOn (fun y => P.gQ y * wOut P y * y) (fun _ => (0 : ℝ)) (uIcc 0 P.s0) := by
      intro y hy
      rw [uIcc_of_le (by linarith)] at hy
      have hwz : wOut P y = 0 := by
        unfold wOut; rw [if_pos (by rw [abs_of_nonneg hy.1]; exact hy.2)]
      simp only [hwz, mul_zero, zero_mul]
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
  have z2 : (∫ y in P.LB..(P.LB + 2), P.gQ y * wOut P y * y) = 0 := by
    have hz : EqOn (fun y => P.gQ y * wOut P y * y) (fun _ => (0 : ℝ)) (uIcc P.LB (P.LB + 2)) := by
      intro y hy
      rw [uIcc_of_le (by linarith)] at hy
      have hgz : P.gQ y = 0 := hP.gQ_eq_zero hw (by rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.1)
      simp only [hgz, zero_mul]
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
  have hT : (∫ y in (0 : ℝ)..(P.LB + 2), P.gQ y * wOut P y * y) = ∫ y in P.s0..P.LB, P.gQ y * wOut P y * y := by
    rw [← s1, ← s2, z1, z2]; ring
  rw [e1, e2, e3, e4, e5, hT] at hmono
  linarith

end F1c
end ShellK
end ZetaShell
