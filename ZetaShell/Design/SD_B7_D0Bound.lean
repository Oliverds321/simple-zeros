/-
Node SD-B7 (L7_7, F1b): **`D₀ = O(ℒ²)` along the Shell design**: `D₀ ≤ K·ℒ²` eventually for some `K > 0`. The closing
equality with margin gives `wD₀ = (e²A/64)L²(1+o(1)) = 1.529λ²ℒ²(1+o(1)) = 5.578ℒ²(1+o(1))` at λ = 1.91, `w = 1`.
Statement form accepted by the lead (13:52): existential constant. Sanity (`sanity_L7_7.py`, `r+ε = 3.5`):
`D₀/ℒ² = 5.584` at `log Q = 2.5·10⁵`, 5.58 as `log Q → ∞`.
PROOF (round 2, not a copy of ZetaQ's `D0_le_of_closing_margin`, which is λ*-specific): from the closing clause's upper
half, `c₄t ≤ L/2 + 2 log C_env + log(2(ℒ + log 4T)) + 2 log S(t) + m`, with `log C_env ≤ C_env ≤ 8(2B′ + 2ℒ)`,
`B′ ≤ CB` (a `Q`-independent constant: the coefficient-sum majorants of `S53L75.poly` with `x₁ ≤ 1`), `m ≤ ℒ/2`,
`S ≤ (1 + 10ℒ)(1 + t)` and `log(1 + t) ≤ t/4 + 1`; so `0.9t ≤ 90ℒ + 2`, `t ≤ 103ℒ` and `D₀ = At² ≤ 1.5·10⁷ℒ²` once
`log Q ≥ CB + 100`. No numeric value of `B′` is needed (SD-A4 is not a dependency).
Deps: SD-A7, SD-A8. Difficulty M.
-/
import ZetaShell.Design.SD_A7_Regime
import ZetaShell.Design.SD_A8_Scales

namespace ZetaShell.Design

open ZetaQ Filter

theorem D0_le_shell (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, ShellDesignM S53L75 r ε (Qn : ℝ) P →
      P.D0 ≤ K * P.LL ^ 2 := by
  -- the Gevrey constant of the S53 window is bounded by a `Q`-independent constant `CB`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = S53L75.poly.natDegree := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (191 / 100 : ℝ) / 2 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; norm_num
  have hMnn : ∀ j, 0 ≤ ParamsQ.Mpoly S53L75.poly R j := fun j =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (pow_nonneg hR0 _))
  have hA13 : (13 : ℝ) ≤ gevreyA := by
    unfold gevreyA; rw [le_div_iff₀ (Real.exp_pos 1)]; linarith [Real.exp_one_lt_d9]
  have hA14 : gevreyA ≤ 14 := by
    unfold gevreyA; rw [div_le_iff₀ (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
  have hc4 : (1.4 : ℝ) ≤ c4 := by
    unfold c4; rw [le_div_iff₀ (Real.exp_pos 1)]; linarith [Real.exp_one_lt_d9]
  have hB0 : 0 ≤ gevreyB := by unfold gevreyB; positivity
  have h1 : 0 ≤ ∑ j ∈ Finset.range (N + 1), ParamsQ.Mpoly S53L75.poly R j :=
    Finset.sum_nonneg fun j _ => hMnn j
  have hq0 : 0 ≤ (191 / 100 : ℝ) / gevreyA := div_nonneg (by norm_num) (by linarith)
  have h2 : 0 ≤ ∑ j ∈ Finset.range (N + 1),
      ParamsQ.Mpoly S53L75.poly R j * ((191 / 100 : ℝ) / gevreyA) ^ j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hMnn j) (pow_nonneg hq0 _)
  obtain ⟨CB, hCB⟩ : ∃ CB : ℝ, CB = gevreyB * (∑ j ∈ Finset.range (N + 1), ParamsQ.Mpoly S53L75.poly R j)
      + (∑ j ∈ Finset.range (N + 1),
          ParamsQ.Mpoly S53L75.poly R j * ((191 / 100 : ℝ) / gevreyA) ^ j) / 2 := ⟨_, rfl⟩
  have hCB0 : 0 ≤ CB := by
    rw [hCB]; exact add_nonneg (mul_nonneg hB0 h1) (div_nonneg h2 (by norm_num))
  refine ⟨15000000, by norm_num, ?_⟩
  have hre : (0:ℝ) < r + ε := by linarith
  have hbig : ∀ᶠ Qn : ℕ in atTop, (CB + 100 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [shellDesign_regime S53L75 (by norm_num [S53L75]) r ε hr hε 1 le_rfl,
    Margin.loglog_le_log_eventually (r + ε) hre, hbig, eventually_ge_atTop 3]
    with Qn hreg hll hu hQn3
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQn1 : 1 ≤ Qn := by omega
  have hS : (1 : ℝ) ≤ ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  obtain ⟨hT, hLLu, hLLLB, hw1⟩ := scales_of_shellDesignM hS hdes hr hQn1
  obtain ⟨-, -, -, hLL2u, -, -, -, -⟩ := hreg P hdes
  set u := Real.log (Qn : ℝ) with hudef
  have hu0 : 0 < u := by linarith
  have hLL1 : (1 : ℝ) ≤ P.LL := by linarith
  have hLLCB : CB ≤ P.LL := by linarith
  have hw : P.w = 1 := hw1 hLL1
  have hlamR : P.lam = 191 / 100 := by rw [hdes.2.2.2.1]; norm_num [S53L75]
  have hLBeq : P.LB = 191 / 100 * P.LL := by unfold ParamsQ.LB; rw [hlamR]
  have hLB0 : 0 < P.LB := by rw [hLBeq]; positivity
  have hLB2 : P.LB ≤ 2 * P.LL := by rw [hLBeq]; linarith
  have hTpos : 0 < P.T := T_posQ hP
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQ3r : (3 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn3
  have hQpos : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hlogT : Real.log P.T = (r + ε) * Real.log u := by rw [hT, Real.log_rpow hu0]
  -- (i) the Gevrey constant `B′ ≤ CB`
  have hBp : P.gevreyBprod gevreyA gevreyB ≤ CB := by
    unfold ParamsQ.gevreyBprod ParamsQ.profM
    rw [hdes.2.2.2.2.2.2.2.2.2.2.2, hlamR, hw, ← hN, ← hR]
    have hx0 : 0 ≤ 1 / (P.LL * gevreyA) := by positivity
    have hx1 : 1 / (P.LL * gevreyA) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    rw [hCB]
    gcongr with j hj
    exact mul_le_of_le_one_right (hMnn j) (pow_le_one₀ hx0 hx1)
  -- (ii) `2 log C_env ≤ 64 ℒ`
  have hCenv0 : 0 < CenvDesign P :=
    mul_pos (Real.exp_pos 2) (lt_of_lt_of_le hLB0 (le_max_right _ _))
  have he2 : Real.exp 2 ≤ 8 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hCenv : CenvDesign P ≤ 8 * (2 * CB + 2 * P.LL) := by
    unfold CenvDesign
    have hmax : max (2 * P.gevreyBprod gevreyA gevreyB * P.w) P.LB ≤ 2 * CB + 2 * P.LL := by
      refine max_le ?_ (by linarith)
      rw [hw]; linarith
    exact mul_le_mul he2 hmax (le_trans hLB0.le (le_max_right _ _)) (by norm_num)
  have hlogC : 2 * Real.log (CenvDesign P) ≤ 64 * P.LL := by
    have := Real.log_le_self hCenv0.le; linarith
  -- (iii) `log(2(ℒ + log 4T)) ≤ 4ℒ`
  have hLLeq : P.LL = u + Real.log P.T - Real.log (2 * Real.pi) := by
    unfold ParamsQ.LL
    rw [hQ, Real.log_div (by positivity) (by positivity), Real.log_mul hQpos.ne' hTpos.ne']
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have h2pi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 * Real.pi by positivity); linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  have hlog4T : Real.log (4 * P.T) ≤ P.LL := by
    rw [Real.log_mul (by norm_num) hTpos.ne', hLLeq]; linarith
  have hlog4T0 : 0 ≤ Real.log (4 * P.T) := Real.log_nonneg (by linarith)
  have hlogW : Real.log (2 * (P.LL + Real.log (4 * P.T))) ≤ 4 * P.LL := by
    have := Real.log_le_self (show (0:ℝ) ≤ 2 * (P.LL + Real.log (4 * P.T)) by positivity)
    linarith
  -- (iv) `m ≤ ℒ/2`
  have hm : marginDesign P ≤ P.LL / 2 := by
    unfold marginDesign; rw [hlogT]; linarith
  -- (v) `2 log S ≤ 20ℒ + t/2 + 2`
  set t := tBuffer P with htdef
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hSeq : rowSumFactor P
      = 1 + P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (t / c4 + 1 / c4 ^ 2) := rfl
  have hbeta : P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) ≤ 10 * P.LL := by
    rw [hw, div_one, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e1 : P.LB * (2 * gevreyA) ≤ (2 * P.LL) * 28 :=
      mul_le_mul hLB2 (by linarith) (by positivity) (by positivity)
    have e2 := mul_le_mul_of_nonneg_left hpi3.le (show (0:ℝ) ≤ 20 * P.LL by positivity)
    linarith
  have hbeta0 : 0 ≤ P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) := by rw [hw]; positivity
  have hc40 : 0 < c4 := by linarith only [hc4]
  have hbr : t / c4 + 1 / c4 ^ 2 ≤ t + 1 := by
    have h1 : t / c4 ≤ t := div_le_self ht0 (by linarith only [hc4])
    have hc4sq : 1 ≤ c4 ^ 2 := one_le_pow₀ (by linarith only [hc4])
    have h2 : 1 / c4 ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hc4sq
    linarith only [h1, h2]
  have hbr0 : 0 ≤ t / c4 + 1 / c4 ^ 2 := by positivity
  have hS1 : rowSumFactor P ≤ (1 + 10 * P.LL) * (1 + t) := by
    rw [hSeq]
    have := mul_le_mul hbeta hbr hbr0 (by positivity)
    linarith only [this, ht0]
  have hSpos : 0 < rowSumFactor P := by
    rw [hSeq]; linarith only [mul_nonneg hbeta0 hbr0]
  have hlogS : Real.log (rowSumFactor P) ≤ 10 * P.LL + (t / 4 + 1) := by
    have h1 := Real.log_le_log hSpos hS1
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    have h2 : Real.log (1 + 10 * P.LL) ≤ 10 * P.LL := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 10 * P.LL by positivity)
      linarith only [this]
    have h3 : Real.log (1 + t) ≤ t / 4 + 1 := by
      have e : Real.log (1 + t) = Real.log 4 + Real.log ((1 + t) / 4) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
      have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 + t) / 4 by positivity)
      have h5 : Real.log 4 ≤ 1.39 := by
        have e4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        rw [e4]; linarith only [Real.log_two_lt_d9]
      rw [e]; linarith only [h4, h5]
    linarith only [h1, h2, h3]
  -- (vi) the closing clause's upper half
  have hcl : ClosingAtDesignM P := hdes.2.2.2.2.2.2.2.2.2.1
  have hup := hcl.2
  have hLBd : Real.log (P.LB / 1) = Real.log P.LB := by rw [div_one]
  unfold logPrefactorGev at hup
  rw [hLBd, ← htdef] at hup
  have hLBh : P.LB / 2 ≤ P.LL := by linarith only [hLB2]
  have ht : t ≤ 103 * P.LL := by
    have key : c4 * t ≤ 90 * P.LL + t / 2 + 2 := by
      linarith only [hup, hlogC, hlogW, hlogS, hm, hLBh, hLL1]
    have : (1.4 : ℝ) * t ≤ c4 * t := mul_le_mul_of_nonneg_right hc4 ht0
    linarith only [key, this, hLL1]
  -- (vii) `D₀ = A t²`
  have hD0nn : 0 ≤ P.D0 := by linarith only [one_le_D0Q hP]
  have htsq : t ^ 2 = P.w * P.D0 / gevreyA := Real.sq_sqrt (by rw [hw]; positivity)
  rw [hw, one_mul] at htsq
  have hA0 : 0 < gevreyA := by linarith only [hA13]
  have hD0 : P.D0 = gevreyA * t ^ 2 := by rw [htsq]; field_simp
  rw [hD0]
  have ht2 : t ^ 2 ≤ (103 * P.LL) ^ 2 := pow_le_pow_left₀ ht0 ht 2
  have hfin := mul_le_mul hA14 ht2 (sq_nonneg t) (by norm_num)
  linarith only [hfin, sq_nonneg P.LL]

end ZetaShell.Design
