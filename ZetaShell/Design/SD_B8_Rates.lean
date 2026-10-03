/-
Node SD-B8 (L7_7, F1b): **the error rows at the Shell rate** `(log Q)^{−θ}`, every `0 < θ < 1`:
  * `r₁ = rowR1 qle P = sZone·(1/2)/(4ℒ)` — `O(1/log Q)`;
  * `r₃ = rowR3Proved A₀ P = 3A₀D₀(ℒ + log 4T)/((T/2π)ℒ)` — `O(ℒ²/T) = O((log Q)^{−1})` by SD-B7 and `r ≥ 3`;
  * `r₄ = rowR4`, `r₅ = rowR5` at any `θ₀ ≤ A₀e^{−m}/L` (SD-B6) — `O(1/(L²T^{3/2}))`.
Sanity (`sanity_L7_7.py`, `A₀ = 162.52`, `r+ε = 3.5`, at `log Q = 2.5·10⁵`): `r₁ = 2.5·10⁻⁷`, `r₃ = 1.4·10⁻⁴`,
`r₄ = 1.1·10⁻⁴²`, `r₅ = 6.1·10⁻³¹`, against `(log Q)^{−0.25} = 0.045`. PROVED (modulo SD-B7) with `c = (4000 + 200K)·A₀`, `K` from SD-B7.
Deps: SD-A8, SD-B7, `Valid.a_ge`, `marginDesign_nonneg`. Difficulty E–M.
-/
import ZetaShell.Design.SD_A8_Scales
import ZetaShell.Design.SD_B7_D0Bound

namespace ZetaShell.Design

open ZetaQ ZetaQ.JoinProved Filter

theorem rows_rate_shell (r ε θ A₀ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hA₀ : 1 ≤ A₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, ShellDesignM S53L75 r ε (Qn : ℝ) P →
      rowR1 Family.qle P ≤ c * shellRate θ Qn ∧
      rowR3Proved A₀ P ≤ c * shellRate θ Qn ∧
      ∀ θ₀ : ℝ, 0 ≤ θ₀ → θ₀ ≤ A₀ * Real.exp (-marginDesign P) / P.LB →
        rowR4 Family.qle P θ₀ ≤ c * shellRate θ Qn ∧ rowR5 Family.qle P θ₀ ≤ c * shellRate θ Qn := by
  obtain ⟨KD, hKD, hD0ev⟩ := D0_le_shell r ε hr hε
  refine ⟨4000 * A₀ + 200 * KD * A₀, by positivity, ?_⟩
  have hre : (0:ℝ) < r + ε := by linarith
  have hu10 : ∀ᶠ Qn : ℕ in atTop, (10 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 10
  filter_upwards [hD0ev, Margin.loglog_le_log_eventually (r + ε) hre, hu10,
    eventually_ge_atTop 3] with Qn hD0 hll hu hQn3
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQn1 : 1 ≤ Qn := by omega
  have hS : (1 : ℝ) ≤ ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  obtain ⟨hT, hLLu, hLLLB, -⟩ := scales_of_shellDesignM hS hdes hr hQn1
  have hD0' := hD0 P hdes
  set u := Real.log (Qn : ℝ) with hudef
  have hu0 : 0 < u := by linarith
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQ3r : (3:ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn3
  have hQpos : (0:ℝ) < (Qn : ℝ) := by linarith
  have hTpos : 0 < P.T := T_posQ hP
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hLLeq : P.LL = u + Real.log P.T - Real.log (2 * Real.pi) := by
    unfold ParamsQ.LL
    rw [hQ, Real.log_div (by positivity) (by positivity), Real.log_mul hQpos.ne' hTpos.ne']
  have hlogT : Real.log P.T = (r + ε) * Real.log u := by
    rw [hT, Real.log_rpow hu0]
  have h2pi0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have h2pi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 * Real.pi by positivity); linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  have hLL2 : P.LL ≤ 2 * u := by rw [hLLeq, hlogT]; linarith
  have hT3 : u ^ 3 ≤ P.T := by
    rw [hT]
    have : u ^ (3:ℝ) ≤ u ^ (r + ε) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [show (u:ℝ) ^ (3:ℝ) = u ^ (3:ℕ) by norm_cast] at this
    exact this
  have hrate : u⁻¹ ≤ shellRate θ Qn := by
    unfold shellRate
    have := Real.rpow_le_rpow_of_exponent_le (x := u) (by linarith) (show (-1:ℝ) ≤ -θ by linarith)
    rwa [Real.rpow_neg_one] at this
  have hc : (0:ℝ) ≤ 4000 * A₀ + 200 * KD * A₀ := by positivity
  have hinv : 0 ≤ u⁻¹ := inv_nonneg.mpr hu0.le
  have key : ∀ K : ℝ, K ≤ 4000 * A₀ + 200 * KD * A₀ → ∀ x : ℝ, x ≤ K * u⁻¹ →
      x ≤ (4000 * A₀ + 200 * KD * A₀) * shellRate θ Qn := by
    intro K hK x hx
    calc x ≤ K * u⁻¹ := hx
      _ ≤ (4000 * A₀ + 200 * KD * A₀) * u⁻¹ := mul_le_mul_of_nonneg_right hK hinv
      _ ≤ (4000 * A₀ + 200 * KD * A₀) * shellRate θ Qn := mul_le_mul_of_nonneg_left hrate hc
  have hLL0 : 0 < P.LL := by linarith
  have hLB0 : 0 < P.LB := by linarith
  have ha : 3 / 4 ≤ P.aQ := hP.a_ge
  have hA₀0 : 0 < A₀ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- `r₁ = sZone·(1/2)/(4ℒ)`
    apply key (1 / 10) (by linarith [mul_nonneg hKD.le hA₀0.le])
    have h1 : P.LL⁻¹ ≤ u⁻¹ := inv_anti₀ hu0 hLLu
    have e : rowR1 Family.qle P = (sZone * (1 / 2) / 4) * P.LL⁻¹ := by
      unfold rowR1 L₆; simp only [Family.conductorShift]; ring
    rw [e]
    calc sZone * (1 / 2) / 4 * P.LL⁻¹ ≤ sZone * (1 / 2) / 4 * u⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (by unfold sZone; norm_num)
      _ ≤ 1 / 10 * u⁻¹ := mul_le_mul_of_nonneg_right (by unfold sZone; norm_num) hinv
  · -- `r₃ = 3A₀D₀(ℒ + log 4T)/((T/2π)ℒ) ≤ 960πA₀/u`
    apply key (192 * KD * A₀) (by linarith [mul_nonneg hKD.le hA₀0.le])
    have hlog4T : Real.log (4 * P.T) ≤ P.LL := by
      rw [Real.log_mul (by norm_num) hTpos.ne', hLLeq]; linarith
    have hnum : 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T))
        ≤ 3 * A₀ * (KD * P.LL ^ 2) * (2 * P.LL) := by
      have hD0nn : 0 ≤ P.D0 := by linarith [one_le_D0Q hP]
      have h1 : P.LL + Real.log (4 * P.T) ≤ 2 * P.LL := by linarith
      have h2 : 0 ≤ P.LL + Real.log (4 * P.T) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ 4 * P.T by linarith); linarith
      calc 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T))
          ≤ 3 * A₀ * (KD * P.LL ^ 2) * (P.LL + Real.log (4 * P.T)) := by gcongr
        _ ≤ 3 * A₀ * (KD * P.LL ^ 2) * (2 * P.LL) := by gcongr
    have hden : 0 < P.T / (2 * Real.pi) * P.LL := by positivity
    show 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) / (P.T / (2 * Real.pi) * P.LL)
      ≤ 192 * KD * A₀ * u⁻¹
    rw [div_le_iff₀ hden]
    have hLLsq : P.LL ^ 2 ≤ 4 * u ^ 2 := by nlinarith
    have hstep : 3 * A₀ * (KD * P.LL ^ 2) * (2 * P.LL) ≤ 192 * KD * A₀ * u⁻¹ * (P.T / (2 * Real.pi) * P.LL) := by
      have e2 : 192 * KD * A₀ * u⁻¹ * (P.T / (2 * Real.pi) * P.LL)
          = (192 * KD / (2 * Real.pi)) * A₀ * P.LL * (P.T / u) := by field_simp
      rw [e2]
      have hTu : u ^ 2 ≤ P.T / u := by rw [le_div_iff₀ hu0]; nlinarith
      have hpc : 24 * KD ≤ 192 * KD / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hpi4.le hKD.le
        linarith
      have hA : 0 ≤ A₀ * P.LL := by positivity
      calc 3 * A₀ * (KD * P.LL ^ 2) * (2 * P.LL) = 6 * KD * (A₀ * P.LL) * P.LL ^ 2 := by ring
        _ ≤ 6 * KD * (A₀ * P.LL) * (4 * u ^ 2) :=
            mul_le_mul_of_nonneg_left hLLsq (by positivity)
        _ ≤ 6 * KD * (A₀ * P.LL) * (4 * (P.T / u)) :=
            mul_le_mul_of_nonneg_left (by linarith [hTu]) (by positivity)
        _ = 24 * KD * ((A₀ * P.LL) * (P.T / u)) := by ring
        _ ≤ (192 * KD / (2 * Real.pi)) * ((A₀ * P.LL) * (P.T / u)) :=
            mul_le_mul_of_nonneg_right hpc (mul_nonneg hA (by positivity))
        _ = (192 * KD / (2 * Real.pi)) * A₀ * P.LL * (P.T / u) := by ring
    linarith
  · -- `r₄`, `r₅` at `θ₀ ≤ A₀e^{−m}/L ≤ A₀/L`
    intro θ₀ hθ0 hθle
    have hm : Real.exp (-marginDesign P) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (marginDesign_nonneg P hP))
    have hθA : θ₀ ≤ A₀ / P.LB := by
      refine le_trans hθle ?_
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hA₀0.le hm) hLB0.le
    have hfam : 1 ≤ famAvgLlow Family.qle P := by
      have hl2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
      have e : famAvgLlow Family.qle P = P.LL - 1 / 2 + (2 * Real.log 2 - 1) - 1 / 100 := by
        unfold famAvgLlow famAvgL rvmSlack; simp only [Family.conductorShift]
      rw [e]; linarith only [hl2, hLLu, hu]
    have hT2pi : 1 ≤ P.T / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith only [hT300, hpi4]
    have hprod : 1 ≤ P.T / (2 * Real.pi) * famAvgLlow Family.qle P := by
      have := mul_le_mul hT2pi hfam zero_le_one (by linarith only [hT2pi])
      simpa using this
    have hsq : 1 ≤ Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow Family.qle P) :=
      Real.one_le_sqrt.mpr hprod
    have hLBu : u ≤ P.LB := le_trans hLLu hLLLB
    have hLB1 : 1 ≤ P.LB := by linarith only [hLBu, hu]
    have hbase : θ₀ / (3 / 4 * P.LB) ≤ 4 / 3 * A₀ * u⁻¹ := by
      have h1 : θ₀ / (3 / 4 * P.LB) ≤ (A₀ / P.LB) / (3 / 4 * P.LB) :=
        div_le_div_of_nonneg_right hθA (by positivity)
      have h2 : (A₀ / P.LB) / (3 / 4 * P.LB) = 4 / 3 * A₀ * (P.LB * P.LB)⁻¹ := by
        field_simp
      have h3 : (P.LB * P.LB)⁻¹ ≤ u⁻¹ :=
        inv_anti₀ hu0 (le_trans hLBu (le_mul_of_one_le_left hLB0.le hLB1))
      have h4 : 4 / 3 * A₀ * (P.LB * P.LB)⁻¹ ≤ 4 / 3 * A₀ * u⁻¹ :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith only [h1, h2, h4]
    have hK : 4 / 3 * A₀ ≤ 4000 * A₀ + 200 * KD * A₀ := by
      linarith [mul_nonneg hKD.le hA₀0.le]
    have haL : 3 / 4 * P.LB ≤ P.aQ * P.LB := mul_le_mul_of_nonneg_right ha hLB0.le
    have haL0 : 0 ≤ P.aQ * P.LB := by positivity
    constructor
    · apply key _ hK
      refine le_trans ?_ hbase
      unfold rowR4
      exact div_le_div_of_nonneg_left hθ0 (by positivity)
        (le_trans haL (le_mul_of_one_le_right haL0 hprod))
    · apply key _ hK
      refine le_trans ?_ hbase
      unfold rowR5
      exact div_le_div_of_nonneg_left hθ0 (by positivity)
        (le_trans haL (le_mul_of_one_le_right haL0 hsq))

end ZetaShell.Design
