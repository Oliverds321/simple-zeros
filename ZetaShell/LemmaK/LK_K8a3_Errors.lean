/-
Node K8a-3 (L7_3, round 2): the error rows of Lemma K (i), integrated over the out-zone, are `o(1)` of the main term:
`2·Err ≤ η·Q²·(T/2π)ℒ·(aL)²` eventually. Proof: on the support of `g` (`|s| < L`), `R₀(s) ≤ 𝒳/(QTℒ) ≤ 𝒳/Q`, so
`errWeight ≤ (2Q²/c + π𝒳 + 4 + (𝒳/Q)²)·‖a‖² + Q²c/2` (AM–GM `2√n ≤ n/c·2 + c/2`, `c = 128/η`); then
`∫_{inZoneᶜ} g‖a‖² ≤ ∫g(‖a‖²+‖b‖²) = (T/π)S(1+E_sm) ≤ 8·(T/2π)ℒ(aL)²` (`lemma43_diagonal`, `sumA2gQ_close`,
`intervalIntegral_gQ_mul_eq`, `K0 + K1 ≤ 2`, `a ≥ 3/4`), `∫g = (aL)²` (`gQ_eq_psi_vDesign`, `psi_total`), and
`𝒳 ≤ Q^{3/2} ≤ Q²/(2K)` (`design_regime`). Draft: eq:EK rows 2 and 4. Difficulty: M.
-/
import ZetaShell.LemmaK.LK_K8a_Defs

noncomputable section
open Filter MeasureTheory Set

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaQ.Payoff

/-- `∫ g = (aL)²` (the dictionary `g(αℒ) = (aλ)²ℒ·ψ(α)` and `∫ψ = 1`). -/
theorem integral_gQ_eq {P : ParamsQ} (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    ∫ u, P.gQ u = (P.aQ * P.LB) ^ 2 := by
  have hLL : 0 < P.LL := hP.LL_pos
  have hcomp := MeasureTheory.Measure.integral_comp_mul_right (fun u => P.gQ u) P.LL
  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hLL)] at hcomp
  have e : ∀ α : ℝ, P.gQ (α * P.LL) = ((P.aQ * P.lam) ^ 2 * P.LL) * psi (vDesign P) α := fun α => by
    rw [FrobAssembly.gQ_eq_psi_vDesign hP hw α]
  simp_rw [e] at hcomp
  rw [integral_const_mul, psi_total (vDesign_admissible hP), mul_one,
    eq_inv_mul_iff_mul_eq₀ hLL.ne'] at hcomp
  have hLB : P.LB = P.lam * P.LL := rfl
  rw [← hcomp, hLB]; ring

set_option maxHeartbeats 1000000 in
/-- **K8a-3.** -/
theorem killed_errors (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      2 * Err P ≤ η * (P.Q ^ 2 * (P.T / (2 * Real.pi) * P.LL) * (P.aQ * P.LB) ^ 2) := by
  obtain ⟨Cs, hCs0, hdiag⟩ := lemma43_diagonal (cWinDesign Family.qle)
  obtain ⟨CM, hCM0, hclose⟩ := sumA2gQ_close
  set K : ℝ := 1000 + 1000 / η + 2 * CM + Cs + 512 / η ^ 2 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    have : 0 ≤ 1000 / η := by positivity
    have : 0 ≤ 512 / η ^ 2 := by positivity
    linarith
  filter_upwards [FrobAssembly.design_regime Family.qle r ε hr hε K hK1,
    FrobAssembly.design_basic Family.qle r ε hr hε, eventually_ge_atTop 1] with Qn hreg hbas hQn1
  intro P hdes
  have hP := hdes.1
  obtain ⟨hlogK, hTK, -, -, hQK, hX32, hQhalf, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hT : (0 : ℝ) ≤ P.T := hP.T_pos.le
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hLB0 : 0 < P.LB := hP.LB_pos
  have ha := hP.a_ge
  have ha0 := hP.aQ_pos
  have hadm := vDesign_admissible hP
  have hQpos : (0 : ℝ) < P.Q := by rw [hQ]; exact_mod_cast (show 0 < Qn by omega)
  have hlogQ : Real.log Qn ≤ P.LL := LL_ge_log_of_design hdes (by omega)
  -- the constants
  have hηK : 1000 ≤ η * K := by
    have h1 : 1000 / η ≤ K := by
      have : 0 ≤ 512 / η ^ 2 := by positivity
      linarith
    rw [div_le_iff₀ hη] at h1; linarith
  have hK1000 : (1000 : ℝ) ≤ K := by
    have : 0 ≤ 1000 / η := by positivity
    have : 0 ≤ 512 / η ^ 2 := by positivity
    linarith
  have hCMK : 2 * CM ≤ K := by
    have : 0 ≤ 1000 / η := by positivity
    have : 0 ≤ 512 / η ^ 2 := by positivity
    linarith
  have hCsK : Cs + 1 ≤ K := by
    have : 0 ≤ 1000 / η := by positivity
    have : 0 ≤ 512 / η ^ 2 := by positivity
    linarith
  have hK512 : 512 / η ^ 2 ≤ K := by
    have : 0 ≤ 1000 / η := by positivity
    linarith
  -- the diagonal `D = ∫ g(‖a‖² + ‖b‖²) ≤ 8 X₀ W`
  set W : ℝ := (P.aQ * P.LB) ^ 2 with hW
  set X0 : ℝ := P.T / (2 * Real.pi) * P.LL with hX0
  have hW0 : 0 ≤ W := by positivity
  have hX00 : 0 < X0 := by positivity
  have hcW : P.cWin = cWinDesign Family.qle := cWin_of_design hdes
  have hreg' : RegimeQ P := FrobAssembly.regimeQ_of hP hL8
  obtain ⟨Esm, hEsm, hdg⟩ := hdiag P hP hreg' hw (by rw [hcW])
  have hEsm1 : |Esm| ≤ 1 := by
    refine hEsm.trans ?_
    rw [div_le_one hTpos]; linarith
  have hIL := FrobAssembly.intervalIntegral_gQ_mul_eq hP hw
  have hSle : sumA2gQ P ≤ P.LL * W * (K0 (vDesign P) + K1 (vDesign P)) / 2 + CM * P.LB ^ 2 := by
    have h := (abs_le.mp (hclose P hP hw hL8)).2
    rw [hIL] at h
    linarith
  have hk2 : K0 (vDesign P) + K1 (vDesign P) ≤ 2 :=
    FrobAssembly.K0_add_K1_le_two hadm hP.lam_lt_two.le
  have hk0 : 0 ≤ K0 (vDesign P) + K1 (vDesign P) := FrobAssembly.K0_add_K1_nonneg hadm
  have hLB2 : P.LB ^ 2 ≤ 16 / 9 * W := by
    have : (3 / 4) ^ 2 ≤ P.aQ ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
    have h0 : 0 ≤ P.LB ^ 2 := sq_nonneg _
    have h3 := mul_le_mul_of_nonneg_right this h0
    have e : (P.aQ * P.LB) ^ 2 = P.aQ ^ 2 * P.LB ^ 2 := by ring
    rw [hW, e]; linarith
  have hS0 : sumA2gQ P ≤ P.LL * W + 16 / 9 * CM * W := by
    have h1 : P.LL * W * (K0 (vDesign P) + K1 (vDesign P)) / 2 ≤ P.LL * W := by
      have := mul_le_mul_of_nonneg_left hk2 (mul_nonneg hLL0.le hW0); linarith
    have h2 : CM * P.LB ^ 2 ≤ CM * (16 / 9 * W) := mul_le_mul_of_nonneg_left hLB2 hCM0.le
    linarith
  have hLLCM : 2 * CM ≤ P.LL := le_trans (le_trans hCMK hlogK) hlogQ
  have hD : (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s)) ≤ 8 * X0 * W := by
    rw [hdg]
    have hSpos : 0 ≤ sumA2gQ P := by
      have := sumA2gQ_lower_const P hP hreg' hw
      have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h6 : 0 < 6 - Real.log 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      have h7 : 0 ≤ Real.log 2 ^ 2 / 2 * (6 - Real.log 2) / 1296 := by positivity
      linarith
    have h1 : 1 + Esm ≤ 2 := by linarith [(abs_le.mp hEsm1).2]
    have hTpi : 0 ≤ P.T / Real.pi := by positivity
    calc P.T / Real.pi * sumA2gQ P * (1 + Esm) ≤ P.T / Real.pi * sumA2gQ P * 2 :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hTpi hSpos)
      _ ≤ P.T / Real.pi * (P.LL * W + 16 / 9 * CM * W) * 2 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hS0 hTpi
      _ ≤ 8 * X0 * W := by
          rw [hX0]
          have hpi := Real.pi_pos
          have e : P.T / Real.pi * (P.LL * W + 16 / 9 * CM * W) * 2
              = 4 * (P.T / (2 * Real.pi)) * W * (P.LL + 16 / 9 * CM) := by field_simp; ring
          rw [e]
          have hTW : 0 ≤ 4 * (P.T / (2 * Real.pi)) * W := by positivity
          have : P.LL + 16 / 9 * CM ≤ 2 * P.LL := by linarith
          have := mul_le_mul_of_nonneg_left this hTW
          linarith
  -- `∫_{out} g‖a‖² ≤ D` and `∫_{out} g ≤ W`
  have hNint : Integrable (fun s => P.gQ s * normA2 P s) := gQ_mul_integrable P hP hw (normA2_continuous P hT)
  have hNBint : Integrable (fun s => P.gQ s * (normA2 P s + normB2 P s)) :=
    gQ_mul_integrable P hP hw ((normA2_continuous P hT).add (normB2_continuous P hT))
  have hgint : Integrable (fun s => P.gQ s) := by
    have := gQ_mul_integrable P hP hw (f := fun _ => (1 : ℝ)) continuous_const
    simpa using this
  have hA_le : ∫ s in (inZone P)ᶜ, P.gQ s * normA2 P s ≤ 8 * X0 * W := by
    refine le_trans (setIntegral_le_integral hNint (Filter.Eventually.of_forall fun s =>
      mul_nonneg (lemma42_g_nonneg P s) (normA2_nonneg P s))) (le_trans ?_ hD)
    apply integral_mono hNint hNBint
    intro s
    exact mul_le_mul_of_nonneg_left (by linarith [normB2_nonneg P s]) (lemma42_g_nonneg P s)
  have hg_le : ∫ s in (inZone P)ᶜ, P.gQ s ≤ W := by
    calc ∫ s in (inZone P)ᶜ, P.gQ s ≤ ∫ u, P.gQ u :=
          setIntegral_le_integral hgint (Filter.Eventually.of_forall fun s => lemma42_g_nonneg P s)
      _ = W := (integral_gQ_eq hP hw).trans hW.symm
  -- `𝒳 ≤ Q²/(2K)`
  have hXQ : P.XQ ≤ P.Q ^ 2 * (1 / K / 2) := by
    have hX32' : P.XQ ≤ P.Q ^ ((2 : ℝ) - 1 / 2) := hX32
    have hQh' : 2 * P.Q ^ (-(1 / 2 : ℝ)) ≤ 1 / K := hQhalf
    have h1 : P.Q ^ ((2 : ℝ) - 1 / 2) = P.Q ^ 2 * P.Q ^ (-(1 / 2 : ℝ)) := by
      rw [show (2 : ℝ) - 1 / 2 = 2 + (-(1 / 2)) by norm_num, Real.rpow_add hQpos, Real.rpow_two]
    have h2 : P.Q ^ (-(1 / 2 : ℝ)) ≤ 1 / K / 2 := by linarith
    calc P.XQ ≤ P.Q ^ ((2 : ℝ) - 1 / 2) := hX32'
      _ = P.Q ^ 2 * P.Q ^ (-(1 / 2 : ℝ)) := h1
      _ ≤ P.Q ^ 2 * (1 / K / 2) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hXQ0 : 0 ≤ P.XQ := (Real.exp_pos _).le
  -- the pointwise bound on the support of `g`
  set c : ℝ := 128 / η with hc
  have hc0 : 0 < c := by positivity
  set B2 : ℝ := Real.pi * P.XQ + 4 + (P.XQ / P.Q) ^ 2 with hB2
  have hT1 : (1 : ℝ) ≤ P.T := le_trans hK1 hTK
  have hTLL : 1 ≤ P.T * P.LL := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ P.T * P.LL := mul_le_mul hT1 (by linarith) (by norm_num) (by linarith)
  have hpt : ∀ s, P.gQ s * errWeight P s
      ≤ (2 * P.Q ^ 2 / c + B2) * (P.gQ s * normA2 P s) + P.Q ^ 2 * c / 2 * P.gQ s := by
    intro s
    have hg := lemma42_g_nonneg P s
    have hn := normA2_nonneg P s
    by_cases hgs : P.gQ s = 0
    · rw [hgs]; simp
    · have hsL : s < P.LB := by
        by_contra hcon
        push_neg at hcon
        exact hgs (hP.gQ_eq_zero hw (le_trans hcon (le_abs_self s)))
      have hR0 : R0 P.Q P.T s ≤ P.XQ / P.Q := by
        unfold R0 Lc
        have hLc : Real.log (P.Q * P.T / (2 * Real.pi)) = P.LL := rfl
        rw [hLc]
        have hes : Real.exp s ≤ P.XQ := by
          unfold ParamsQ.XQ; exact Real.exp_le_exp.mpr hsL.le
        rw [div_le_div_iff₀ (by positivity) hQpos]
        have h4 : Real.exp s * P.Q ≤ P.XQ * P.Q := mul_le_mul_of_nonneg_right hes hQpos.le
        have h5 : P.XQ * P.Q ≤ P.XQ * (P.Q * P.T * P.LL) := by
          calc P.XQ * P.Q = P.XQ * P.Q * 1 := by ring
            _ ≤ P.XQ * P.Q * (P.T * P.LL) := mul_le_mul_of_nonneg_left hTLL (by positivity)
            _ = P.XQ * (P.Q * P.T * P.LL) := by ring
        linarith
      have hR00 : 0 ≤ R0 P.Q P.T s := by unfold R0; positivity
      have hmax : (max 2 (R0 P.Q P.T s)) ^ 2 ≤ 4 + (P.XQ / P.Q) ^ 2 := by
        rcases le_total 2 (R0 P.Q P.T s) with h | h
        · rw [max_eq_right h]
          have := pow_le_pow_left₀ hR00 hR0 2
          linarith
        · rw [max_eq_left h]
          have := sq_nonneg (P.XQ / P.Q)
          norm_num; linarith
      have hsq : 2 * Real.sqrt (normA2 P s) ≤ 2 * normA2 P s / c + c / 2 := by
        have h0 := Real.sq_sqrt hn
        have h1 := Real.sqrt_nonneg (normA2 P s)
        have : 0 ≤ (Real.sqrt (normA2 P s) - c / 2) ^ 2 := sq_nonneg _
        have hcn : c * Real.sqrt (normA2 P s) ≤ normA2 P s + c ^ 2 / 4 := by nlinarith only [this, h0]
        rw [div_add_div _ _ hc0.ne' (by norm_num), le_div_iff₀ (by positivity)]
        linarith
      have hw' : errWeight P s ≤ (2 * P.Q ^ 2 / c + B2) * normA2 P s + P.Q ^ 2 * c / 2 := by
        unfold errWeight
        have hQ2 : 0 ≤ P.Q ^ 2 := sq_nonneg _
        have e1 : 2 * P.Q ^ 2 * Real.sqrt (normA2 P s) ≤ P.Q ^ 2 * (2 * normA2 P s / c + c / 2) := by
          have := mul_le_mul_of_nonneg_left hsq hQ2; linarith
        have e2 : (Real.pi * P.XQ + (max 2 (R0 P.Q P.T s)) ^ 2) * normA2 P s ≤ B2 * normA2 P s := by
          apply mul_le_mul_of_nonneg_right _ hn
          rw [hB2]; linarith
        have e3 : P.Q ^ 2 * (2 * normA2 P s / c + c / 2)
            = 2 * P.Q ^ 2 / c * normA2 P s + P.Q ^ 2 * c / 2 := by ring
        linarith
      have := mul_le_mul_of_nonneg_left hw' hg
      linarith
  -- integrate
  have hEint : Integrable (fun s => P.gQ s * errWeight P s) := by
    have hR0c : Continuous (fun s => R0 P.Q P.T s) := by
      unfold R0; exact Real.continuous_exp.div_const _
    have hn := normA2_continuous P hT
    exact gQ_mul_integrable P hP hw ((continuous_const.mul (Real.continuous_sqrt.comp hn)).add
      ((continuous_const.add ((continuous_const.max hR0c).pow 2)).mul hn))
  have hErr : Err P ≤ (2 * P.Q ^ 2 / c + B2) * (8 * X0 * W) + P.Q ^ 2 * c / 2 * W := by
    unfold Err
    have hmono : ∫ s in (inZone P)ᶜ, P.gQ s * errWeight P s
        ≤ ∫ s in (inZone P)ᶜ, ((2 * P.Q ^ 2 / c + B2) * (P.gQ s * normA2 P s) + P.Q ^ 2 * c / 2 * P.gQ s) :=
      setIntegral_mono_on hEint.integrableOn
        (((hNint.const_mul _).add (hgint.const_mul _)).integrableOn) (measurableSet_inZone P).compl
        (fun s _ => hpt s)
    have e1 := integral_add (μ := volume.restrict (inZone P)ᶜ)
      (f := fun s => (2 * P.Q ^ 2 / c + B2) * (P.gQ s * normA2 P s))
      (g := fun s => P.Q ^ 2 * c / 2 * P.gQ s) (hNint.const_mul _).integrableOn (hgint.const_mul _).integrableOn
    have e2 := integral_const_mul (μ := volume.restrict (inZone P)ᶜ) (2 * P.Q ^ 2 / c + B2)
      (fun s => P.gQ s * normA2 P s)
    have e3 := integral_const_mul (μ := volume.restrict (inZone P)ᶜ) (P.Q ^ 2 * c / 2) (fun s => P.gQ s)
    rw [e1, e2, e3] at hmono
    have hB20 : 0 ≤ 2 * P.Q ^ 2 / c + B2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hA_le hB20
    have h2 := mul_le_mul_of_nonneg_left hg_le (by positivity : 0 ≤ P.Q ^ 2 * c / 2)
    linarith
  -- the arithmetic
  have hQK' : K ≤ P.Q := by
    rw [hQ]
    have : K * (1 + Real.log Qn) ^ 2 ≤ Qn := hQK
    have hl : 0 ≤ Real.log (Qn : ℝ) := Real.log_nonneg (by exact_mod_cast hQn1)
    have h1 : (1 : ℝ) ≤ (1 + Real.log Qn) ^ 2 := by nlinarith only [hl]
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ K)
    linarith
  have hX0K : K ≤ X0 := by
    rw [hX0]
    have hpi := Real.pi_pos
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have h8 : P.T * (2 * Real.pi) ≤ P.T * P.LL := mul_le_mul_of_nonneg_left (by linarith) hT
    have : P.T ≤ P.T / (2 * Real.pi) * P.LL := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hB2le : B2 ≤ η / 64 * P.Q ^ 2 := by
    rw [hB2]
    have hQ2pos : 0 < P.Q ^ 2 := by positivity
    have hK0 : 0 < K := by linarith
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hηKK : 1000 * 1000 ≤ η * K * K := by
      have := mul_le_mul hηK hK1000 (by norm_num) (by positivity)
      linarith
    have hX1 : Real.pi * P.XQ ≤ Real.pi * (P.Q ^ 2 * (1 / K / 2)) :=
      mul_le_mul_of_nonneg_left hXQ Real.pi_pos.le
    have hX2 : (P.XQ / P.Q) ^ 2 ≤ (P.Q * (1 / K / 2)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ hQpos]
      have e : P.Q * (1 / K / 2) * P.Q = P.Q ^ 2 * (1 / K / 2) := by ring
      rw [e]; exact hXQ
    have t1 : Real.pi * (P.Q ^ 2 * (1 / K / 2)) ≤ η / 256 * P.Q ^ 2 := by
      have e : Real.pi * (P.Q ^ 2 * (1 / K / 2)) = P.Q ^ 2 * (Real.pi / (2 * K)) := by
        field_simp
      rw [e, show η / 256 * P.Q ^ 2 = P.Q ^ 2 * (η / 256) by ring]
      apply mul_le_mul_of_nonneg_left _ hQ2pos.le
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have t2 : (P.Q * (1 / K / 2)) ^ 2 ≤ η / 256 * P.Q ^ 2 := by
      have e : (P.Q * (1 / K / 2)) ^ 2 = P.Q ^ 2 * (1 / (4 * K ^ 2)) := by field_simp; ring
      rw [e, show η / 256 * P.Q ^ 2 = P.Q ^ 2 * (η / 256) by ring]
      apply mul_le_mul_of_nonneg_left _ hQ2pos.le
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have t3 : (4 : ℝ) ≤ η / 256 * P.Q ^ 2 := by
      have hQ2 : K ^ 2 ≤ P.Q ^ 2 := pow_le_pow_left₀ (by linarith) hQK' 2
      have h4 : (4 : ℝ) ≤ η / 256 * K ^ 2 := by
        have e : η / 256 * K ^ 2 = η * K * K / 256 := by ring
        rw [e]; linarith
      have := mul_le_mul_of_nonneg_left hQ2 (by positivity : (0 : ℝ) ≤ η / 256)
      linarith
    linarith
  -- final: `2·Err ≤ (32/c)Q²X₀W + 16B2·X₀W + Q²cW ≤ η Q² X₀ W`
  have hQXW : 0 ≤ P.Q ^ 2 * X0 * W := by positivity
  have hcX : c ≤ η / 4 * X0 := by
    rw [hc, div_le_iff₀ hη]
    have h512 : 512 / η ^ 2 ≤ X0 := le_trans hK512 hX0K
    rw [div_le_iff₀ (by positivity)] at h512
    have e : η / 4 * X0 * η = X0 * η ^ 2 / 4 := by ring
    rw [e]; linarith
  have f1 : 2 * ((2 * P.Q ^ 2 / c) * (8 * X0 * W)) = η / 4 * (P.Q ^ 2 * X0 * W) := by
    rw [hc]; field_simp; ring
  have f2 : 2 * (B2 * (8 * X0 * W)) ≤ η / 4 * (P.Q ^ 2 * X0 * W) := by
    have := mul_le_mul_of_nonneg_right hB2le (by positivity : 0 ≤ 16 * X0 * W)
    have e1 : 2 * (B2 * (8 * X0 * W)) = B2 * (16 * X0 * W) := by ring
    have e2 : η / 64 * P.Q ^ 2 * (16 * X0 * W) = η / 4 * (P.Q ^ 2 * X0 * W) := by ring
    linarith
  have f3 : 2 * (P.Q ^ 2 * c / 2 * W) ≤ η / 4 * (P.Q ^ 2 * X0 * W) := by
    have := mul_le_mul_of_nonneg_left hcX (by positivity : 0 ≤ P.Q ^ 2 * W)
    have e1 : 2 * (P.Q ^ 2 * c / 2 * W) = P.Q ^ 2 * W * c := by ring
    have e2 : P.Q ^ 2 * W * (η / 4 * X0) = η / 4 * (P.Q ^ 2 * X0 * W) := by ring
    linarith
  have hfin : 2 * Err P ≤ 3 * η / 4 * (P.Q ^ 2 * X0 * W) := by
    have e : 2 * ((2 * P.Q ^ 2 / c + B2) * (8 * X0 * W) + P.Q ^ 2 * c / 2 * W)
        = 2 * ((2 * P.Q ^ 2 / c) * (8 * X0 * W)) + 2 * (B2 * (8 * X0 * W)) + 2 * (P.Q ^ 2 * c / 2 * W) := by
      ring
    linarith [hErr, e, f1, f2, f3]
  have : 3 * η / 4 * (P.Q ^ 2 * X0 * W) ≤ η * (P.Q ^ 2 * X0 * W) :=
    mul_le_mul_of_nonneg_right (by linarith) hQXW
  rw [hX0, hW] at *
  linarith

end LemmaK
end ZetaShell
