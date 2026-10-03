/-
K3b-I (L7_3c, round 10, resumed): the integrated pieces of K3b at one design point, on `S = (a, ∞)`.
* `gsav_integrable`: `g·savWeight` is integrable (an indicator of `g·(continuous)`).
* `K3b_I`: the left side is integrable on `S` and `I ≤ Q²((1 + δ₁)A + ℒG − W)` (from `integrand_le`).
* `K3b_W`: `κ_C U(Y − ℓ_K G − L) ≤ W` (from `sav_lower_pt`).
* `K3b_B`: the right side is integrable on `S` and `C U(ℒ − 1)(G − 1) ≤ B_S` (from `shell_lower_pt`).
Here `A = ∫_S g‖a‖²`, `G = ∫_S g`, `Y = ∫_S g·s`, `W = ∫_S g·savWeight`, `B_S = ∫_S g‖a‖²·shellWt`.
-/
import ZetaShell.ShellK.LF_K3bA

noncomputable section
open scoped BigOperators ArithmeticFunction
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaShell.LemmaK

/-- `g·savWeight` as an indicator of `g·(continuous)`. -/
theorem gsav_eq (C₁ : ℝ) (Qn : ℕ) (P : ParamsQ) :
    (fun s => P.gQ s * savWeight C₁ Qn P s)
      = (Iic (Real.log P.XQ - 1)).indicator (fun s => P.gQ s
          * ((1 - C₁ / Real.log (Qn : ℝ)) * (P.T / (2 * Real.pi)) * max (s - ellK P.Q P.T) 0)) := by
  funext s
  unfold savWeight
  by_cases h : s ≤ Real.log P.XQ - 1
  · rw [Set.indicator_of_mem (show s ∈ Iic (Real.log P.XQ - 1) from h), if_pos h, mul_one]
  · rw [Set.indicator_of_notMem (show s ∉ Iic (Real.log P.XQ - 1) from h), if_neg h, mul_zero, mul_zero]

theorem gsav_integrable (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (C₁ : ℝ) (Qn : ℕ) :
    Integrable (fun s => P.gQ s * savWeight C₁ Qn P s) := by
  rw [gsav_eq]
  refine Integrable.indicator ?_ measurableSet_Iic
  exact gQ_mul_integrable P hP hw
    (continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const))

theorem errWeight_continuous (P : ParamsQ) (hT : 0 ≤ P.T) : Continuous (errWeight P) := by
  have hR : Continuous (fun s => R0 P.Q P.T s) := by
    unfold R0; exact Real.continuous_exp.div_const _
  unfold errWeight
  exact (continuous_const.mul (normA2_continuous P hT).sqrt).add
    ((continuous_const.add ((continuous_const.max hR).pow 2)).mul (normA2_continuous P hT))

theorem ind_integrable (L : ℝ) : Integrable ((Ioc (L - 1) L).indicator (fun _ => (1 : ℝ))) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))

theorem ind_setIntegral_le (a L : ℝ) :
    ∫ s in Ioi a, (Ioc (L - 1) L).indicator (fun _ => (1 : ℝ)) s ≤ 1 := by
  calc ∫ s in Ioi a, (Ioc (L - 1) L).indicator (fun _ => (1 : ℝ)) s
      ≤ ∫ s, (Ioc (L - 1) L).indicator (fun _ => (1 : ℝ)) s :=
        setIntegral_le_integral (ind_integrable L)
          (ae_of_all _ fun s => Set.indicator_nonneg (fun _ _ => zero_le_one) s)
    _ = 1 := by
        rw [integral_indicator measurableSet_Ioc, setIntegral_const, Real.volume_real_Ioc_of_le (by linarith)]
        simp

theorem ind_setIntegral_nonneg (a L : ℝ) :
    0 ≤ ∫ s in Ioi a, (Ioc (L - 1) L).indicator (fun _ => (1 : ℝ)) s :=
  setIntegral_nonneg measurableSet_Ioi fun s _ => Set.indicator_nonneg (fun _ _ => zero_le_one) s

/-- **K3b-I.** Integrability of the left side and `I ≤ Q²((1 + δ₁)A + ℒG − W)`. -/
theorem K3b_I (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (C₁ : ℝ) (Qn : ℕ)
    (hTL : 1 ≤ P.T * P.LL) (δ₁ : ℝ)
    (hδ : 2 * Real.pi * P.XQ + 4 + (P.XQ / P.Q) ^ 2 + P.Q ^ 2 / P.LL ≤ δ₁ * P.Q ^ 2) (a : ℝ) :
    IntegrableOn
        (fun s => P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
        (Ioi a) ∧
      (∫ s in Ioi a, P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
        ≤ P.Q ^ 2 * ((1 + δ₁) * (∫ s in Ioi a, P.gQ s * normA2 P s) + P.LL * (∫ s in Ioi a, P.gQ s)
            - ∫ s in Ioi a, P.gQ s * savWeight C₁ Qn P s) := by
  have hT := hP.T_pos
  have hA : Integrable (fun s => P.gQ s * normA2 P s) := gQ_mul_integrable P hP hw (normA2_continuous P hT.le)
  have hG : Integrable (fun s => P.gQ s) := hP.gQ_integrable hw
  have hW : Integrable (fun s => P.gQ s * savWeight C₁ Qn P s) := gsav_integrable P hP hw C₁ Qn
  have hE : Integrable (fun s => P.gQ s * errWeight P s) :=
    gQ_mul_integrable P hP hw (errWeight_continuous P hT.le)
  have e : (fun s => P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
      = fun s => sieveBudgetQ P * (P.gQ s * normA2 P s) - P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s)
          + P.gQ s * errWeight P s := by
    funext s; ring
  have hI : Integrable
      (fun s => P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s)) := by
    rw [e]; exact ((hA.const_mul _).sub (hW.const_mul _)).add hE
  refine ⟨hI.integrableOn, ?_⟩
  have hR1 : Integrable (fun s => (1 + δ₁) * (P.gQ s * normA2 P s) + P.LL * P.gQ s) :=
    (hA.const_mul _).add (hG.const_mul _)
  have hR : Integrable (fun s => P.Q ^ 2 * ((1 + δ₁) * (P.gQ s * normA2 P s) + P.LL * P.gQ s)
      - P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s)) :=
    (hR1.const_mul _).sub (hW.const_mul _)
  have hle := setIntegral_mono_on (s := Ioi a) hI.integrableOn hR.integrableOn measurableSet_Ioi (fun s _ => by
    have := integrand_le P hP hw C₁ Qn hTL δ₁ hδ s
    calc _ ≤ _ := this
      _ = _ := by ring)
  have hval : (∫ s in Ioi a, (P.Q ^ 2 * ((1 + δ₁) * (P.gQ s * normA2 P s) + P.LL * P.gQ s)
        - P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s)))
      = P.Q ^ 2 * ((1 + δ₁) * (∫ s in Ioi a, P.gQ s * normA2 P s) + P.LL * (∫ s in Ioi a, P.gQ s)
          - ∫ s in Ioi a, P.gQ s * savWeight C₁ Qn P s) := by
    rw [integral_sub (hR1.const_mul _).integrableOn (hW.const_mul _).integrableOn, integral_const_mul,
      integral_const_mul, integral_add (hA.const_mul _).integrableOn (hG.const_mul _).integrableOn,
      integral_const_mul, integral_const_mul]
    ring
  linarith

/-- **K3b-W.** `κ_C U(Y − ℓ_K G − L) ≤ W`. -/
theorem K3b_W (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (C₁ : ℝ) (Qn : ℕ)
    (hκ : 0 ≤ 1 - C₁ / Real.log Qn) (hℓ0 : 0 ≤ ellK P.Q P.T) (hL1 : 1 ≤ P.LB) (a : ℝ) :
    (1 - C₁ / Real.log Qn) * (P.T / (2 * Real.pi))
        * ((∫ s in Ioi a, P.gQ s * s) - ellK P.Q P.T * (∫ s in Ioi a, P.gQ s) - P.LB)
      ≤ ∫ s in Ioi a, P.gQ s * savWeight C₁ Qn P s := by
  set κU := (1 - C₁ / Real.log Qn) * (P.T / (2 * Real.pi)) with hκU
  have hκU0 : 0 ≤ κU := mul_nonneg hκ (by have := hP.T_pos; positivity)
  have hgy : Integrable (fun s : ℝ => P.gQ s * s) := gQ_mul_integrable P hP hw continuous_id
  have hgint : Integrable (fun s => P.gQ s) := hP.gQ_integrable hw
  have hind := ind_integrable P.LB
  have hL0 : Integrable (fun s => (P.gQ s * s - ellK P.Q P.T * P.gQ s)
      - P.LB * (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s) :=
    (hgy.sub (hgint.const_mul _)).sub (hind.const_mul _)
  have hL : Integrable (fun s => κU * ((P.gQ s * s - ellK P.Q P.T * P.gQ s)
      - P.LB * (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s)) := hL0.const_mul _
  have h1 := setIntegral_mono_on (s := Ioi a) hL.integrableOn (gsav_integrable P hP hw C₁ Qn).integrableOn measurableSet_Ioi
    (fun s _ => by
      have := sav_lower_pt P hP hw C₁ Qn hκ hℓ0 hL1 s
      calc _ = _ := by ring
        _ ≤ _ := this)
  have hval : (∫ s in Ioi a, κU * ((P.gQ s * s - ellK P.Q P.T * P.gQ s)
        - P.LB * (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s))
      = κU * ((∫ s in Ioi a, P.gQ s * s) - ellK P.Q P.T * (∫ s in Ioi a, P.gQ s)
          - P.LB * ∫ s in Ioi a, (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s) := by
    have i1 : Integrable (fun s => P.gQ s * s - ellK P.Q P.T * P.gQ s) := hgy.sub (hgint.const_mul _)
    have i2 : Integrable (fun s => P.LB * (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s) :=
      hind.const_mul _
    have i3 : Integrable (fun s => ellK P.Q P.T * P.gQ s) := hgint.const_mul _
    rw [integral_const_mul, integral_sub i1.integrableOn i2.integrableOn,
      integral_sub hgy.integrableOn i3.integrableOn, integral_const_mul, integral_const_mul]
  rw [hval] at h1
  have hJ := ind_setIntegral_le a P.LB
  have hJ0 := ind_setIntegral_nonneg a P.LB
  have hLJ : P.LB * ∫ s in Ioi a, (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s ≤ P.LB := by
    have := mul_le_mul_of_nonneg_left hJ (by linarith : (0:ℝ) ≤ P.LB)
    linarith
  have h2 := mul_le_mul_of_nonneg_left
    (show (∫ s in Ioi a, P.gQ s * s) - ellK P.Q P.T * (∫ s in Ioi a, P.gQ s) - P.LB
      ≤ (∫ s in Ioi a, P.gQ s * s) - ellK P.Q P.T * (∫ s in Ioi a, P.gQ s)
          - P.LB * ∫ s in Ioi a, (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s by linarith) hκU0
  linarith

/-- **K3b-B.** Integrability of the right side and `C U(ℒ − 1)(G − 1) ≤ B_S`. -/
theorem K3b_B (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (αp : ℝ) (hLL1 : 1 ≤ P.LL)
    (ha1 : Real.log P.Q + 4 ≤ αp * P.LL) (haL : P.LL ≤ αp * P.LL)
    (hlow : ∀ s, αp * P.LL < s → s ≤ P.LB - 1 → P.T / (2 * Real.pi) * (s - 1) ≤ normA2 P s) :
    IntegrableOn (fun s => P.gQ s * (normA2 P s * shellWt P αp s)) (Ioi (αp * P.LL)) ∧
      Cfam * (P.T / (2 * Real.pi)) * (P.LL - 1) * ((∫ s in Ioi (αp * P.LL), P.gQ s) - 1)
        ≤ ∫ s in Ioi (αp * P.LL), P.gQ s * (normA2 P s * shellWt P αp s) := by
  have hT := hP.T_pos
  have ha0 : 0 < αp * P.LL := by linarith
  have hcont : Continuous (fun s => normA2 P s * (Cfam * P.LL / max s (αp * P.LL))) :=
    (normA2_continuous P hT.le).mul (continuous_const.div (continuous_id.max continuous_const)
      (fun s => (lt_of_lt_of_le ha0 (le_max_right _ _)).ne'))
  have hint0 := gQ_mul_integrable P hP hw hcont
  have hB : IntegrableOn (fun s => P.gQ s * (normA2 P s * shellWt P αp s)) (Ioi (αp * P.LL)) := by
    refine hint0.integrableOn.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs' : αp * P.LL < s := hs
    have hsw : shellWt P αp s = Cfam * P.LL / s := by
      unfold shellWt
      rw [if_neg (by linarith), if_neg (by linarith)]
    simp only
    rw [max_eq_left hs'.le, hsw]
  refine ⟨hB, ?_⟩
  set c₀ := Cfam * P.LL * (P.T / (2 * Real.pi)) * (1 - 1 / P.LL) with hc₀
  have hgint : Integrable (fun s => P.gQ s) := hP.gQ_integrable hw
  have hind := ind_integrable P.LB
  have hLi : Integrable (fun s => c₀ * (P.gQ s - (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s)) :=
    (hgint.sub hind).const_mul _
  have h1 := setIntegral_mono_on hLi.integrableOn hB measurableSet_Ioi
    (fun s hs => shell_lower_pt P hP hw αp hLL1 ha1 haL hlow s hs)
  rw [integral_const_mul, integral_sub hgint.integrableOn hind.integrableOn] at h1
  have hJ := ind_setIntegral_le (αp * P.LL) P.LB
  have hc00 : 0 ≤ c₀ := by
    have hC0 : 0 < Cfam := by unfold Cfam; positivity
    have : 0 ≤ 1 - 1 / P.LL := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hLL1
    rw [hc₀]; positivity
  have hc₀' : c₀ = Cfam * (P.T / (2 * Real.pi)) * (P.LL - 1) := by
    rw [hc₀]; field_simp
  have h2 := mul_le_mul_of_nonneg_left
    (show (∫ s in Ioi (αp * P.LL), P.gQ s) - 1 ≤ (∫ s in Ioi (αp * P.LL), P.gQ s)
      - ∫ s in Ioi (αp * P.LL), (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s by linarith) hc00
  rw [← hc₀']
  linarith

end F1c
end ShellK
end ZetaShell
