/-
Node SD-A5 (L7_7, F1a): **the Shell design point exists for every large `Q`** — the intermediate value theorem on the
closing condition with margin, `D₀ ∈ [10L, T/3]`, at `λ = 191/100` and profile S53-L75.
ROUND 2 (statement changed, lead informed): the explicit-threshold form `exists_shellDesignM_at (… hu : 2.5·10⁵ ≤ log Q)`
is replaced by the EVENTUAL form below. Reason: the only consumer (SD-A6, `ShellFrame.exists_design`) needs existence
for large `Q` only; the proof here does not copy ZetaQ's `exists_designOfRecordM_at` (whose endpoint-sign lemmas are
`private` and λ*-specific) but bounds the upper endpoint with the same crude, `Q`-independent constants as SD-B7
(`B′ ≤ CB`), which makes an explicit numeric threshold meaningless. The numerical check of the (true) thresholds,
`sanity_A5.py → .out`, holds at every `r + ε ∈ {3.001, 3.5, 6, 20}` and `log Q ∈ {2.5·10⁵, 10⁶, 10⁷, 10⁹, 10¹², 10²⁰,
10⁴⁰}` (root `D₀/ℒ² = 5.578–5.588`, all side conditions true), and does not depend on `r + ε`.
Proof: `G(d) := c₄√(d/A) − (L/2 + logPrefactorGev + m + log L)` at the point `mk d` (only `D₀ = d` varies) is continuous;
`G(10L) ≤ 0` because every log term is `≥ 0` and `c₄√(10L/A) ≤ L/2` (`L ≥ 7`); `G(T/3) ≥ 0` by SD-B7's upper bounds
(`… ≤ 89.5ℒ + t/2 + 2`) and `√(T/(3A)) ≥ 102ℒ` (`T ≥ (log Q)³`, `log Q ≥ 1.75·10⁶`); the root is the design point.
Deps: SD-A2, SD-A3, SD-A8 (pattern), SD-B7 (pattern). Difficulty M–H.
-/
import ZetaShell.Design.SD_A3_Moments
import ZetaShell.Design.SD_A7_Regime

namespace ZetaShell.Design

open ZetaQ Filter Set

set_option maxHeartbeats 4000000 in
theorem exists_shellDesignM_eventually (hL : S53L75.L75) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, ∃ P : ParamsQ, ShellDesignM S53L75 r ε Q P := by
  -- ## the `Q`-independent constant bounding the Gevrey constant `B′` (as in SD-B7)
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
  have hc4' : c4 ≤ 1.5 := by
    unfold c4; rw [div_le_iff₀ (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
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
  have hre : (0 : ℝ) < r + ε := by linarith
  have hlamR : ((S53L75.lam : ℚ) : ℝ) = 191 / 100 := by norm_num [S53L75]
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (CB + 2000000 : ℝ),
    Real.tendsto_log_atTop.eventually (FrobAssembly.loglog_le_eventually (r + ε) hre)]
    with Q hQ3 hu hll
  -- ## the one-parameter family of design points
  set u := Real.log Q with hudef
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hu0 : 0 < u := by linarith
  let mk : ℝ → ParamsQ := fun d =>
    { Q := Q, T := Twin Q r ε, lam := ((S53L75.lam : ℚ) : ℝ), w := 1, D0 := d,
      ϱ := Zeta23.Taper.rhoTwo, prof := S53L75.poly }
  set P0 := mk 0 with hP0
  have hT : P0.T = u ^ (r + ε) := rfl
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hT3 : u ^ 3 ≤ P0.T := by
    rw [hT]
    have : u ^ (3:ℝ) ≤ u ^ (r + ε) := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    rw [show (u:ℝ) ^ (3:ℝ) = u ^ (3:ℕ) by norm_cast] at this
    exact this
  have hu3 : (8000000000000000000 : ℝ) ≤ u ^ 3 := by
    have : (2000000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    norm_num at this ⊢; linarith
  have hTpos : 0 < P0.T := by linarith
  have hlogT : Real.log P0.T = (r + ε) * Real.log u := by rw [hT, Real.log_rpow hu0]
  have hlogT0 : 0 ≤ Real.log P0.T := Real.log_nonneg (by linarith)
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have h2pi0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have h2pi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 * Real.pi by positivity); linarith
  have hLLeq : P0.LL = u + Real.log P0.T - Real.log (2 * Real.pi) := by
    show Real.log (Q * P0.T / (2 * Real.pi)) = _
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hQ0.ne' hTpos.ne']
  have hlogT2pi : Real.log (2 * Real.pi) ≤ Real.log P0.T :=
    Real.log_le_log (by positivity) (by linarith)
  have hLLu : u ≤ P0.LL := by rw [hLLeq]; linarith
  have hLL2 : P0.LL ≤ 2 * u := by rw [hLLeq, hlogT]; linarith
  have hLL1 : (1 : ℝ) ≤ P0.LL := by linarith
  have hLLCB : CB ≤ P0.LL := by linarith
  have hLBeq : P0.LB = 191 / 100 * P0.LL := by show ((S53L75.lam : ℚ) : ℝ) * P0.LL = _; rw [hlamR]
  have hLB2 : P0.LB ≤ 2 * P0.LL := by rw [hLBeq]; linarith
  have hLBL : P0.LL ≤ P0.LB := by rw [hLBeq]; linarith
  have hLB0 : 0 < P0.LB := by linarith
  -- ## the closing function, as an explicit function of `d`
  set Cn := CenvDesign P0 with hCn
  set W := Real.log (2 * (P0.LL + Real.log (4 * P0.T))) with hW
  set β := P0.LB / (2 * Real.pi) * (2 * gevreyA / 1) with hβ
  set m := marginDesign P0 with hm
  have hCnd : ∀ d, CenvDesign (mk d) = Cn := fun d => rfl
  have hSd : ∀ d, rowSumFactor (mk d)
      = 1 + β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2) := fun d => rfl
  have htd : ∀ d, tBuffer (mk d) = Real.sqrt (1 * d / gevreyA) := fun d => rfl
  let G : ℝ → ℝ := fun d => c4 * Real.sqrt (1 * d / gevreyA)
    - (P0.LB / 2 + (2 * Real.log Cn + W
        + 2 * Real.log (1 + β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2)) - Real.log P0.LB)
        + m + Real.log (P0.LB / 1))
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hc40 : 0 < c4 := by linarith
  have hSpos : ∀ d, 0 < 1 + β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2) := fun d => by
    have : 0 ≤ β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2) := by positivity
    linarith
  have hGcont : Continuous G := by
    have hs : Continuous fun d : ℝ => Real.sqrt (1 * d / gevreyA) := by fun_prop
    have hlg : Continuous fun d : ℝ =>
        Real.log (1 + β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2)) :=
      Continuous.log (by fun_prop) (fun d => (hSpos d).ne')
    show Continuous fun d => c4 * Real.sqrt (1 * d / gevreyA)
      - (P0.LB / 2 + (2 * Real.log Cn + W
        + 2 * Real.log (1 + β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2)) - Real.log P0.LB)
        + m + Real.log (P0.LB / 1))
    fun_prop
  -- ## the two endpoints
  set a := 10 * P0.LB with ha
  set b := P0.T / 3 with hb
  have hab : a ≤ b := by
    rw [ha, hb]
    have e1 : 10 * P0.LB ≤ 40 * u := by linarith only [hLB2, hLL2]
    have e2 : (120 : ℝ) ≤ u * u := by
      have := mul_le_mul (show (120:ℝ) ≤ u by linarith only [hu, hCB0])
        (show (1:ℝ) ≤ u by linarith only [hu1]) (by norm_num) (by linarith only [hu1])
      linarith only [this]
    have e3 : 120 * u ≤ u * u * u := mul_le_mul_of_nonneg_right e2 (by linarith only [hu1])
    have e4 : u ^ 3 = u * u * u := by ring
    rw [le_div_iff₀ (by norm_num)]
    linarith only [e1, e3, e4, hT3]
  -- lower-bound facts for the log terms
  have hCn1 : 1 ≤ Cn := by
    rw [hCn]; unfold CenvDesign
    have h1e : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
    have hm1 : (1 : ℝ) ≤ max (2 * P0.gevreyBprod gevreyA gevreyB * P0.w) P0.LB :=
      le_trans (by linarith only [hLBL, hLL1]) (le_max_right _ _)
    exact one_le_mul_of_one_le_of_one_le h1e hm1
  have hW0 : 0 ≤ W := by
    rw [hW]; apply Real.log_nonneg
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 * P0.T by linarith); linarith
  have hm0 : 0 ≤ m := by rw [hm]; unfold marginDesign; linarith
  have hGa : G a ≤ 0 := by
    have hS1 : 0 ≤ Real.log (1 + β * (Real.sqrt (1 * a / gevreyA) / c4 + 1 / c4 ^ 2)) := by
      apply Real.log_nonneg
      have : 0 ≤ β * (Real.sqrt (1 * a / gevreyA) / c4 + 1 / c4 ^ 2) := by positivity
      linarith
    have hlC : 0 ≤ Real.log Cn := Real.log_nonneg hCn1
    have hsq : Real.sqrt (1 * a / gevreyA) ≤ P0.LB / (2 * c4) := by
      have hin : 1 * a / gevreyA ≤ (P0.LB / (2 * c4)) ^ 2 := by
        rw [div_pow, one_mul, div_le_div_iff₀ (by linarith only [hA13]) (by positivity), ha]
        have hc4sq : (2 * c4) ^ 2 ≤ 9 := by
          have := mul_le_mul hc4' hc4' (by linarith only [hc4]) (by norm_num)
          have e : (2 * c4) ^ 2 = 4 * (c4 * c4) := by ring
          rw [e]; linarith only [this]
        have e1 : 10 * P0.LB * (2 * c4) ^ 2 ≤ 10 * P0.LB * 9 :=
          mul_le_mul_of_nonneg_left hc4sq (by linarith only [hLB0])
        have hL7 : (90 / 13 : ℝ) ≤ P0.LB := by linarith only [hLBL, hLL1, hu, hLLu, hCB0]
        have e2 : 90 / 13 * P0.LB ≤ P0.LB * P0.LB := mul_le_mul_of_nonneg_right hL7 hLB0.le
        have e3 : P0.LB ^ 2 * 13 ≤ P0.LB ^ 2 * gevreyA :=
          mul_le_mul_of_nonneg_left hA13 (sq_nonneg _)
        have e4 : P0.LB ^ 2 = P0.LB * P0.LB := by ring
        linarith only [e1, e2, e3, e4]
      calc Real.sqrt (1 * a / gevreyA) ≤ Real.sqrt ((P0.LB / (2 * c4)) ^ 2) := Real.sqrt_le_sqrt hin
        _ = P0.LB / (2 * c4) := Real.sqrt_sq (by positivity)
    have hmul : c4 * Real.sqrt (1 * a / gevreyA) ≤ P0.LB / 2 := by
      have := mul_le_mul_of_nonneg_left hsq hc40.le
      rw [show c4 * (P0.LB / (2 * c4)) = P0.LB / 2 by field_simp] at this
      exact this
    have hdiv : Real.log (P0.LB / 1) = Real.log P0.LB := by rw [div_one]
    show c4 * Real.sqrt (1 * a / gevreyA)
      - (P0.LB / 2 + (2 * Real.log Cn + W
        + 2 * Real.log (1 + β * (Real.sqrt (1 * a / gevreyA) / c4 + 1 / c4 ^ 2)) - Real.log P0.LB)
        + m + Real.log (P0.LB / 1)) ≤ 0
    rw [hdiv]
    linarith
  have hGb : 0 ≤ G b := by
    -- upper bounds (SD-B7)
    have hBp : P0.gevreyBprod gevreyA gevreyB ≤ CB := by
      unfold ParamsQ.gevreyBprod ParamsQ.profM
      show gevreyB * (∑ j ∈ Finset.range (S53L75.poly.natDegree + 1),
          ParamsQ.Mpoly S53L75.poly (((S53L75.lam : ℚ) : ℝ) / 2) j * (1 / (P0.LL * gevreyA)) ^ j)
          + (∑ j ∈ Finset.range (S53L75.poly.natDegree + 1),
            ParamsQ.Mpoly S53L75.poly (((S53L75.lam : ℚ) : ℝ) / 2) j
              * (((S53L75.lam : ℚ) : ℝ) / gevreyA) ^ j) / 2 ≤ CB
      rw [hlamR, ← hN, ← hR]
      have hx0 : 0 ≤ 1 / (P0.LL * gevreyA) := by positivity
      have hx1 : 1 / (P0.LL * gevreyA) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have := mul_le_mul hLL1 hA13 (by norm_num) (by linarith only [hLL1])
        linarith only [this]
      rw [hCB]
      gcongr with j hj
      exact mul_le_of_le_one_right (hMnn j) (pow_le_one₀ hx0 hx1)
    have he2 : Real.exp 2 ≤ 8 := by
      have h2e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h2e]
      have := mul_le_mul Real.exp_one_lt_d9.le Real.exp_one_lt_d9.le (Real.exp_pos 1).le (by norm_num)
      linarith only [this]
    have hCn8 : Cn ≤ 8 * (2 * CB + 2 * P0.LL) := by
      rw [hCn]; unfold CenvDesign
      have hmax : max (2 * P0.gevreyBprod gevreyA gevreyB * P0.w) P0.LB ≤ 2 * CB + 2 * P0.LL := by
        refine max_le ?_ (by linarith)
        show 2 * P0.gevreyBprod gevreyA gevreyB * 1 ≤ _
        linarith
      exact mul_le_mul he2 hmax (le_trans hLB0.le (le_max_right _ _)) (by norm_num)
    have hlogC : 2 * Real.log Cn ≤ 64 * P0.LL := by
      have := Real.log_le_self (show (0:ℝ) ≤ Cn by linarith); linarith
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
    have hlog4T : Real.log (4 * P0.T) ≤ P0.LL := by
      rw [Real.log_mul (by norm_num) hTpos.ne', hLLeq]; linarith
    have hlog4T0 : 0 ≤ Real.log (4 * P0.T) := Real.log_nonneg (by linarith)
    have hWle : W ≤ 4 * P0.LL := by
      rw [hW]
      have := Real.log_le_self (show (0:ℝ) ≤ 2 * (P0.LL + Real.log (4 * P0.T)) by positivity)
      linarith
    have hmle : m ≤ P0.LL / 2 := by
      rw [hm]; unfold marginDesign; rw [hlogT]; linarith
    set t := Real.sqrt (1 * b / gevreyA) with htdef
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hβle : β ≤ 10 * P0.LL := by
      rw [hβ, div_one, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have e1 : P0.LB * (2 * gevreyA) ≤ (2 * P0.LL) * 28 :=
        mul_le_mul hLB2 (by linarith) (by positivity) (by positivity)
      have e2 := mul_le_mul_of_nonneg_left hpi3.le (show (0:ℝ) ≤ 20 * P0.LL by positivity)
      linarith
    have hbr : t / c4 + 1 / c4 ^ 2 ≤ t + 1 := by
      have e1 : t / c4 ≤ t := div_le_self ht0 (by linarith only [hc4])
      have hc4sq : 1 ≤ c4 ^ 2 := one_le_pow₀ (by linarith only [hc4])
      have e2 : 1 / c4 ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hc4sq
      linarith only [e1, e2]
    have hbr0 : 0 ≤ t / c4 + 1 / c4 ^ 2 := by positivity
    have hS1 : 1 + β * (t / c4 + 1 / c4 ^ 2) ≤ (1 + 10 * P0.LL) * (1 + t) := by
      have := mul_le_mul hβle hbr hbr0 (by positivity)
      linarith only [this, ht0]
    have hlogS : Real.log (1 + β * (t / c4 + 1 / c4 ^ 2)) ≤ 10 * P0.LL + (t / 4 + 1) := by
      have e1 := Real.log_le_log (hSpos b) hS1
      rw [Real.log_mul (by positivity) (by positivity)] at e1
      have e2 : Real.log (1 + 10 * P0.LL) ≤ 10 * P0.LL := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 10 * P0.LL by positivity)
        linarith only [this]
      have e3 : Real.log (1 + t) ≤ t / 4 + 1 := by
        have e : Real.log (1 + t) = Real.log 4 + Real.log ((1 + t) / 4) := by
          rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
        have e4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 + t) / 4 by positivity)
        have e5 : Real.log 4 ≤ 1.39 := by
          have e6 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
          rw [e6]; linarith only [Real.log_two_lt_d9]
        rw [e]; linarith only [e4, e5]
      linarith only [e1, e2, e3]
    -- `t ≥ 102 ℒ`
    have htbig : 102 * P0.LL ≤ t := by
      rw [htdef, one_mul]
      apply Real.le_sqrt_of_sq_le
      rw [hb, div_div, le_div_iff₀ (by positivity)]
      have e1 : (102 * P0.LL) ^ 2 * (3 * gevreyA) ≤ (102 * (2 * u)) ^ 2 * 42 := by
        have := pow_le_pow_left₀ (by positivity) (show 102 * P0.LL ≤ 102 * (2 * u) by linarith) 2
        exact mul_le_mul this (by linarith) (by positivity) (by positivity)
      have e2 : (102 * (2 * u)) ^ 2 * 42 ≤ u ^ 3 := by
        have : (102 * (2 * u)) ^ 2 * 42 = 1747872 * u ^ 2 := by ring
        rw [this]
        have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
        have : u ^ 3 = u * u ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (by linarith) hu2
      linarith
    have hdiv : Real.log (P0.LB / 1) = Real.log P0.LB := by rw [div_one]
    show 0 ≤ c4 * t
      - (P0.LB / 2 + (2 * Real.log Cn + W
        + 2 * Real.log (1 + β * (t / c4 + 1 / c4 ^ 2)) - Real.log P0.LB)
        + m + Real.log (P0.LB / 1))
    rw [hdiv]
    have hLBh : P0.LB / 2 ≤ P0.LL := by linarith only [hLB2]
    have hc4t : (1.4 : ℝ) * t ≤ c4 * t := mul_le_mul_of_nonneg_right hc4 ht0
    linarith only [hlogC, hWle, hmle, hlogS, hLBh, hc4t, htbig, hLL1]
  -- ## the root
  obtain ⟨d, hd, hGd⟩ : ∃ d ∈ Icc a b, G d = 0 := by
    have := intermediate_value_Icc hab hGcont.continuousOn
    exact this ⟨hGa, hGb⟩
  refine ⟨mk d, ?_⟩
  have hda : a ≤ d := hd.1
  have hdb : d ≤ b := hd.2
  have hLLd : (mk d).LL = P0.LL := rfl
  have hLBd : (mk d).LB = P0.LB := rfl
  have hTd : (mk d).T = P0.T := rfl
  have hl : Zeta23.l (mk d).T ≠ 0 := by
    show Real.log (P0.T / (2 * Real.pi)) ≠ 0
    apply ne_of_gt; apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hmom := moments_S53_eventual (mk d) rfl rfl rfl rfl hl (by rw [hLLd]; linarith)
  have hwD : (mk d).w = wDesign (mk d).LL r := by
    show (1 : ℝ) = max 1 ((mk d).LL ^ ((3 - r) / 2))
    rw [hLLd]
    exact (max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))).symm
  have hvalid : (mk d).Valid :=
    { taper := Zeta23.Taper.rhoTwo_taper
      profile := S53L75.profileQ_of_L75 hL
      lam_pos := by show (0 : ℝ) < ((S53L75.lam : ℚ) : ℝ); rw [hlamR]; norm_num
      lam_lt_two := by show ((S53L75.lam : ℚ) : ℝ) < 2; rw [hlamR]; norm_num
      one_le_w := le_refl (1 : ℝ)
      two_le_D0 := by show (2 : ℝ) ≤ d; linarith
      D0_le := by show d + 4 ≤ P0.T; linarith
      T_ge := by show (300 : ℝ) ≤ P0.T; linarith
      Q_ge := hQ3
      a_ge := hmom.1
      b_ge := hmom.2 }
  refine ⟨hvalid, rfl, rfl, rfl, hwD, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, rfl, rfl⟩
  · show 8 * (1 : ℝ) ≤ P0.LB; linarith
  · show Real.exp 2 * gevreyA ≤ 1 * d
    have he2 : Real.exp 2 ≤ 8 := by
      have h2e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h2e]
      have := mul_le_mul Real.exp_one_lt_d9.le Real.exp_one_lt_d9.le (Real.exp_pos 1).le (by norm_num)
      linarith only [this]
    have : Real.exp 2 * gevreyA ≤ 8 * 14 := mul_le_mul he2 hA14 (by linarith) (by norm_num)
    linarith
  · show 10 * P0.LB ≤ d; exact hda
  · show d ≤ P0.T / 3; exact hdb
  · show 10 * P0.LL * Real.log P0.LL ≤ P0.T
    have hlLL : Real.log P0.LL ≤ P0.LL := Real.log_le_self (by linarith)
    have : 10 * P0.LL * Real.log P0.LL ≤ 10 * P0.LL * P0.LL :=
      mul_le_mul_of_nonneg_left hlLL (by linarith)
    have : 10 * P0.LL * P0.LL ≤ 10 * (2 * u) * (2 * u) :=
      mul_le_mul (by linarith) hLL2 (by linarith) (by linarith)
    have : 10 * (2 * u) * (2 * u) ≤ u ^ 3 := by
      have e1 : 40 * (u * u) ≤ u * (u * u) :=
        mul_le_mul_of_nonneg_right (by linarith only [hu, hCB0]) (by positivity)
      have e2 : u ^ 3 = u * (u * u) := by ring
      linarith only [e1, e2]
    linarith
  · -- the closing clause, from `G d = 0`
    have hGd' : c4 * Real.sqrt (1 * d / gevreyA)
        - (P0.LB / 2 + (2 * Real.log Cn + W
          + 2 * Real.log (1 + β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2))
          - Real.log P0.LB) + m + Real.log (P0.LB / 1)) = 0 := hGd
    have hlpg : logPrefactorGev (mk d) = 2 * Real.log Cn + W
        + 2 * Real.log (1 + β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2))
        - Real.log P0.LB := rfl
    have hmd : marginDesign (mk d) = m := rfl
    constructor
    · show (mk d).LB / 2 + (logPrefactorGev (mk d) + marginDesign (mk d)) + Real.log ((mk d).LB / 1)
          ≤ c4 * Real.sqrt ((mk d).w * (mk d).D0 / gevreyA)
      rw [hlpg, hmd, hLBd]
      show P0.LB / 2 + (2 * Real.log Cn + W
          + 2 * Real.log (1 + β * (Real.sqrt (1 * d / gevreyA) / c4 + 1 / c4 ^ 2))
          - Real.log P0.LB + m) + Real.log (P0.LB / 1) ≤ c4 * Real.sqrt (1 * d / gevreyA)
      linarith
    · show c4 * tBuffer (mk d)
          ≤ (mk d).LB / 2 + logPrefactorGev (mk d) + marginDesign (mk d) + Real.log ((mk d).LB / 1)
      rw [hlpg, hmd, hLBd, htd]
      linarith

end ZetaShell.Design
