/-
K3b-P (L7_3c, round 10): the pointwise PNT lower bound for `‖a(s)‖²`.
* `sbp_Ico`: summation by parts on `[m, n)`.
* `model_core_sum`: the integer model sum on the core window `e^{s−1/2} ≤ n < e^{s+1/2}`:
  `Σ n⁻¹|D_T(s − log n)|² ≥ 2πT − 9` once `e^s ≥ 100T³` (L7_9's `model_l2_lower_aux`, steps C–H, verbatim).
* `prime_core_sum`: the same sum over primes, weighted `(log p)²`, by summation by parts against `θ(k) − k`:
  `Σ_p (log p)² p⁻¹|D_T(s − log p)|² ≥ (s − 1/2)(2πT − 9) − 30εT³(s + 2)` when `|θ(k) − k| ≤ εk` on the window.
* `theta_pnt`: `|θ(x) − x| ≤ x(log x)^{−A}` for large `x` (L7_2's `psi_sub_id_isLittleO_log_rpow` and Mathlib's
  `Chebyshev.psi_sub_theta_le`).
* `normA2_ge_prime`: `‖a(s)‖² ≥ (4π²)⁻¹ Σ_{core} c(n) log n · gfun(n)`.
* `normA2_lower` (the node): along the Shell design, `U(s − 1) ≤ ‖a(s)‖²` for `√(log Q) ≤ s ≤ L − 1`.
-/
import ZetaShell.LemmaK.LK9_K6a_L2Final
import ZetaShell.LemmaK.LK_K8d_Bridge
import ZetaShell.PNT.PNTMedium
import ZetaShell.Design.SD_A7_Regime
import ZetaShell.Design.SD_A8_Scales
import ZetaShell.ShellK.L10_KDefs

noncomputable section
open scoped BigOperators ArithmeticFunction Chebyshev
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaShell.LemmaK ZetaShell.LemmaK.K6

/-- Summation by parts on `[m, n)`. -/
theorem sbp_Ico (R F : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.Ico m n, (R (k + 1) - R k) * F (k + 1)
      = R n * F n - R m * F m - ∑ k ∈ Finset.Ico m n, R k * (F (k + 1) - F k) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Finset.sum_Ico_succ_top hmn, Finset.sum_Ico_succ_top hmn, ih]
    ring

set_option maxHeartbeats 1000000 in
/-- The integer model sum on the core window (L7_9's `model_l2_lower_aux`, steps C–H). -/
theorem model_core_sum (T s : ℝ) (hT64 : 64 ≤ T) (hs1' : 1 ≤ s) (hbig : 100 * T ^ 3 ≤ Real.exp s) :
    2 * Real.pi * T - 9
      ≤ ∑ n ∈ Finset.Ico ⌈Real.exp (s - 1 / 2)⌉₊ ⌊Real.exp (s + 1 / 2)⌋₊, gfun T s n := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  have he1 := Real.exp_one_lt_d9
  have he1' := Real.exp_one_gt_d9
  set ea := Real.exp (s - 1 / 2) with hea
  set eb := Real.exp (s + 1 / 2) with heb
  have hea1 : 1 ≤ ea := Real.one_le_exp (by linarith)
  have hea0 : 0 < ea := by linarith
  have heaeb : ea + 1 ≤ eb := by
    have e : eb = ea * Real.exp 1 := by rw [hea, heb, ← Real.exp_add]; congr 1; ring
    rw [e]; nlinarith
  set n₁ := ⌈ea⌉₊ with hn₁
  set n₂ := ⌊eb⌋₊ with hn₂
  have hn₁ea : ea ≤ (n₁ : ℝ) := Nat.le_ceil ea
  have hn₁ea' : (n₁ : ℝ) < ea + 1 := Nat.ceil_lt_add_one hea0.le
  have hn₂eb : (n₂ : ℝ) ≤ eb := Nat.floor_le (by linarith)
  have hn₂eb' : eb < (n₂ : ℝ) + 1 := Nat.lt_floor_add_one eb
  have hn₁1 : 1 ≤ n₁ := by exact_mod_cast (show (1 : ℝ) ≤ n₁ by linarith)
  have hn₁n₂ : n₁ ≤ n₂ := by
    apply Nat.le_floor; linarith
  have hn₁R : (1 : ℝ) ≤ n₁ := by linarith
  -- (C) each term against its unit integral
  have hint : ∀ k : ℕ, 1 ≤ k → IntervalIntegrable (gfun T s) MeasureTheory.volume (k : ℝ) ((k : ℝ) + 1) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact gfun_contOn T s k (k + 1) (by linarith)
  have hC : ∀ n ∈ Finset.Ico n₁ n₂,
      (∫ y in (n : ℝ)..((n : ℝ) + 1), gfun T s y) ≤ gfun T s n + 3 * T ^ 3 / (n : ℝ) ^ 2 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : 1 ≤ n := by omega
    have h := intervalIntegral.integral_mono_on (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) (hint n hn1)
      (intervalIntegrable_const (c := gfun T s n + 3 * T ^ 3 / (n : ℝ) ^ 2))
      (fun y hy => gfun_step_low T s hT1 n hn1 y hy.1 hy.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  -- (D) adjacent intervals
  have hD : ∑ k ∈ Finset.Ico n₁ n₂, (∫ y in (k : ℝ)..((k : ℝ) + 1), gfun T s y)
      = ∫ y in (n₁ : ℝ)..(n₂ : ℝ), gfun T s y := by
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k : ℕ => (k : ℝ))
      (f := gfun T s) (μ := MeasureTheory.volume) hn₁n₂
      (fun k hk => by
        have hk1 : 1 ≤ k := le_trans hn₁1 hk.1
        have := hint k hk1
        push_cast; exact this)
    simpa using h
  -- (E) the two ends
  have hcont : ContinuousOn (gfun T s) (Set.Icc ea eb) := gfun_contOn T s ea eb hea0
  have hii : ∀ c d : ℝ, ea ≤ c → c ≤ d → d ≤ eb →
      IntervalIntegrable (gfun T s) MeasureTheory.volume c d := by
    intro c d hc hcd hd
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hcd]
    exact hcont.mono (Set.Icc_subset_Icc hc hd)
  have hgle : ∀ y ∈ Set.Icc ea eb, gfun T s y ≤ T ^ 2 / ea := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    unfold gfun
    have hD := DTFacts.DT_norm_le T (s - Real.log y) hT0.le
    have hD2 : ‖DT T (s - Real.log y)‖ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
    have hyinv : y⁻¹ ≤ ea⁻¹ := inv_anti₀ hea0 hy.1
    calc y⁻¹ * ‖DT T (s - Real.log y)‖ ^ 2 ≤ ea⁻¹ * T ^ 2 :=
          mul_le_mul hyinv hD2 (sq_nonneg _) (by positivity)
      _ = T ^ 2 / ea := by ring
  have hend : ∀ c d : ℝ, ea ≤ c → c ≤ d → d ≤ eb → d - c ≤ 1 →
      (∫ y in c..d, gfun T s y) ≤ T ^ 2 / ea := by
    intro c d hc hcd hd hl
    have h := intervalIntegral.integral_mono_on hcd (hii c d hc hcd hd)
      (intervalIntegrable_const (c := T ^ 2 / ea))
      (fun y hy => hgle y ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    have : (d - c) * (T ^ 2 / ea) ≤ 1 * (T ^ 2 / ea) := mul_le_mul_of_nonneg_right hl (by positivity)
    linarith
  have hsplit : (∫ y in ea..eb, gfun T s y) = (∫ y in ea..(n₁ : ℝ), gfun T s y)
      + (∫ y in (n₁ : ℝ)..(n₂ : ℝ), gfun T s y) + ∫ y in (n₂ : ℝ)..eb, gfun T s y := by
    have hn₁n₂R : (n₁ : ℝ) ≤ n₂ := by exact_mod_cast hn₁n₂
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _ le_rfl hn₁ea (by linarith))
        (hii _ _ hn₁ea hn₁n₂R hn₂eb),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _ le_rfl (by linarith) hn₂eb)
        (hii _ _ (by linarith) hn₂eb le_rfl)]
  have hn₁n₂R : (n₁ : ℝ) ≤ n₂ := by exact_mod_cast hn₁n₂
  have hE1 := hend ea n₁ le_rfl hn₁ea (by linarith) (by linarith)
  have hE2 := hend n₂ eb (by linarith) hn₂eb le_rfl (by linarith)
  -- (F) the core integral
  have hF : 2 * Real.pi * T - 8 - 32 / T ≤ ∫ y in ea..eb, gfun T s y := by
    rw [hea, heb, gfun_subst T s _ _ (by linarith),
      intervalIntegral.integral_comp_sub_left (fun v => ‖DT T v‖ ^ 2) s]
    rw [show s - (s + 1 / 2) = -(1 / 2 : ℝ) by ring, show s - (s - 1 / 2) = (1 / 2 : ℝ) by ring]
    exact DT_core_mass T hT1
  -- (G) the error sum
  have hG : ∑ n ∈ Finset.Ico n₁ n₂, 3 * T ^ 3 / (n : ℝ) ^ 2 ≤ 1 / 5 := by
    have hterm : ∀ n ∈ Finset.Ico n₁ n₂, 3 * T ^ 3 / (n : ℝ) ^ 2 ≤ 3 * T ^ 3 / ea ^ 2 := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have : ea ≤ (n : ℝ) := le_trans hn₁ea (by exact_mod_cast hn.1)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ hea0.le this 2
    calc ∑ n ∈ Finset.Ico n₁ n₂, 3 * T ^ 3 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Ico n₁ n₂, 3 * T ^ 3 / ea ^ 2 := Finset.sum_le_sum hterm
      _ = ((n₂ - n₁ : ℕ) : ℝ) * (3 * T ^ 3 / ea ^ 2) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ eb * (3 * T ^ 3 / ea ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : ((n₂ - n₁ : ℕ) : ℝ) ≤ n₂ := by exact_mod_cast Nat.sub_le n₂ n₁
          linarith
      _ ≤ 1 / 5 := by
          have h12 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          have hh0 : 0 < Real.exp (1 / 2) := Real.exp_pos _
          have hh : Real.exp (1 / 2) ≤ 1.65 := by nlinarith
          have h32 : Real.exp (3 / 2) ≤ 5 := by
            have e3 : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
              rw [← Real.exp_add]; norm_num
            rw [e3]; nlinarith
          have hq : eb / ea ^ 2 = Real.exp (3 / 2) / Real.exp s := by
            rw [hea, heb, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_sub]
            congr 1; push_cast; ring
          have e : eb * (3 * T ^ 3 / ea ^ 2) = 3 * T ^ 3 * Real.exp (3 / 2) / Real.exp s := by
            rw [show eb * (3 * T ^ 3 / ea ^ 2) = 3 * T ^ 3 * (eb / ea ^ 2) by ring, hq]; ring
          rw [e, div_le_iff₀ (Real.exp_pos s)]
          have := mul_le_mul_of_nonneg_left h32 (by positivity : (0 : ℝ) ≤ 3 * T ^ 3)
          have := Real.exp_pos s
          linarith
  -- (H) collect
  have hsum_g : (∫ y in (n₁ : ℝ)..(n₂ : ℝ), gfun T s y)
      ≤ ∑ n ∈ Finset.Ico n₁ n₂, gfun T s n + 1 / 5 := by
    rw [← hD]
    calc ∑ k ∈ Finset.Ico n₁ n₂, (∫ y in (k : ℝ)..((k : ℝ) + 1), gfun T s y)
        ≤ ∑ k ∈ Finset.Ico n₁ n₂, (gfun T s k + 3 * T ^ 3 / (k : ℝ) ^ 2) := Finset.sum_le_sum hC
      _ = ∑ k ∈ Finset.Ico n₁ n₂, gfun T s k + ∑ k ∈ Finset.Ico n₁ n₂, 3 * T ^ 3 / (k : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ ≤ _ := by linarith
  have hea_big : T ^ 2 / ea ≤ 1 / 50 := by
    rw [div_le_iff₀ hea0]
    have h1 : Real.exp s = ea * Real.exp (1 / 2) := by rw [hea, ← Real.exp_add]; ring_nf
    have h12 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hh0 : 0 < Real.exp (1 / 2) := Real.exp_pos _
    have h2 : Real.exp (1 / 2) ≤ 2 := by nlinarith
    have h3 : 100 * T ^ 2 ≤ 100 * T ^ 3 := by
      have : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT1 (by norm_num)
      linarith
    have h4 : ea * Real.exp (1 / 2) ≤ ea * 2 := mul_le_mul_of_nonneg_left h2 hea0.le
    linarith
  have h32T : 32 / T ≤ 1 / 2 := by
    rw [div_le_iff₀ hT0]
    linarith
  linarith

/-- `c(n) = log n` at primes, `0` elsewhere (the increments of `θ`). -/
def cPr (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

theorem cPr_nonneg (n : ℕ) : 0 ≤ cPr n := by
  unfold cPr
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_refl 0

theorem theta_natCast_succ (k : ℕ) : θ ((k + 1 : ℕ) : ℝ) = θ (k : ℝ) + cPr (k + 1) := by
  rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast, Finset.sum_filter,
    Finset.sum_filter, Finset.sum_Ioc_succ_top (Nat.zero_le k)]
  rfl

theorem gfun_nonneg (T s y : ℝ) (hy : 0 ≤ y) : 0 ≤ gfun T s y := by
  unfold gfun; positivity

/-- `|F(k+1) − F(k)| ≤ 4(1 + log k)T³/k²` for `F(y) = log y · y⁻¹|D_T(s − log y)|²`. -/
theorem F_step (T s : ℝ) (hT1 : 1 ≤ T) (k : ℕ) (hk : 1 ≤ k) :
    |Real.log ((k : ℝ) + 1) * gfun T s ((k : ℝ) + 1) - Real.log k * gfun T s k|
      ≤ 4 * (1 + Real.log k) * T ^ 3 / (k : ℝ) ^ 2 := by
  have hT0 : 0 ≤ T := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk1
  unfold gfun
  set X := ‖DT T (s - Real.log ((k : ℝ) + 1))‖ with hXdef
  set Y := ‖DT T (s - Real.log k)‖ with hYdef
  set d := Real.log ((k : ℝ) + 1) - Real.log k with hd
  have hX0 : 0 ≤ X := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hX : X ≤ T := DTFacts.DT_norm_le T _ hT0
  have hY : Y ≤ T := DTFacts.DT_norm_le T _ hT0
  have hd0 : 0 ≤ d := sub_nonneg.mpr (Real.log_le_log hk0 (by linarith))
  have hd1 : d ≤ 1 / k := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((k : ℝ) + 1) / k by positivity)
    rw [Real.log_div (by positivity) hk0.ne'] at h
    have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
    rw [e] at h
    exact h
  have hkd : (k : ℝ) * d ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hd1 hk0.le
    rwa [mul_one_div_cancel hk0.ne'] at this
  have hXY : |X - Y| ≤ (3 / 2) * T ^ 2 * d := by
    have h1 := DTFacts.DT_lipschitz T (s - Real.log ((k : ℝ) + 1)) (s - Real.log k) hT0
    have e1 : s - Real.log ((k : ℝ) + 1) - (s - Real.log k) = -d := by rw [hd]; ring
    rw [e1, abs_neg, abs_of_nonneg hd0] at h1
    exact (abs_norm_sub_norm_le _ _).trans h1
  have hab : |X ^ 2 - Y ^ 2| ≤ 3 * T ^ 3 / k := by
    have e2 : X ^ 2 - Y ^ 2 = (X - Y) * (X + Y) := by ring
    rw [e2, abs_mul, abs_of_nonneg (by positivity : 0 ≤ X + Y)]
    calc |X - Y| * (X + Y) ≤ ((3 / 2) * T ^ 2 * d) * (2 * T) :=
          mul_le_mul hXY (by linarith) (by positivity) (by positivity)
      _ = 3 * T ^ 3 * d := by ring
      _ ≤ 3 * T ^ 3 * (1 / k) := mul_le_mul_of_nonneg_left hd1 (by positivity)
      _ = 3 * T ^ 3 / k := by ring
  have hq : |Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) - Real.log k / k| ≤ (1 + Real.log k) / (k : ℝ) ^ 2 := by
    have e : Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) - Real.log k / k
        = ((k : ℝ) * d - Real.log k) / ((k : ℝ) * ((k : ℝ) + 1)) := by
      rw [hd]; field_simp; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hnum : |(k : ℝ) * d - Real.log k| ≤ 1 + Real.log k := by
      rw [abs_le]; constructor <;> nlinarith [mul_nonneg hk0.le hd0]
    calc |(k : ℝ) * d - Real.log k| * (k : ℝ) ^ 2 ≤ (1 + Real.log k) * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ (1 + Real.log k) * ((k : ℝ) * ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have e : Real.log ((k : ℝ) + 1) * (((k : ℝ) + 1)⁻¹ * X ^ 2) - Real.log k * ((k : ℝ)⁻¹ * Y ^ 2)
      = (Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) - Real.log k / k) * X ^ 2
        + Real.log k / k * (X ^ 2 - Y ^ 2) := by
    field_simp; ring
  rw [e]
  have hX2 : X ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hX0 hX 2
  have hT23 : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT1 (by norm_num)
  have hlk : 0 ≤ Real.log k / k := by positivity
  calc |(Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) - Real.log k / k) * X ^ 2
          + Real.log k / k * (X ^ 2 - Y ^ 2)|
        ≤ |Real.log ((k : ℝ) + 1) / ((k : ℝ) + 1) - Real.log k / k| * X ^ 2
          + Real.log k / k * |X ^ 2 - Y ^ 2| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg X), abs_of_nonneg hlk]
    _ ≤ (1 + Real.log k) / (k : ℝ) ^ 2 * T ^ 2 + Real.log k / k * (3 * T ^ 3 / k) :=
          add_le_add (mul_le_mul hq hX2 (sq_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left hab hlk)
    _ = ((1 + Real.log k) * T ^ 2 + 3 * Real.log k * T ^ 3) / (k : ℝ) ^ 2 := by
          field_simp
    _ ≤ 4 * (1 + Real.log k) * T ^ 3 / (k : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hT23 (by linarith : (0 : ℝ) ≤ 1 + Real.log k)]

set_option maxHeartbeats 1000000 in
/-- **The prime sum on the core window**, by summation by parts against `θ(k) − k`. -/
theorem prime_core_sum (T s ε : ℝ) (hT64 : 64 ≤ T) (hs : 2 ≤ s) (hbig : 100 * T ^ 3 ≤ Real.exp s)
    (hε0 : 0 ≤ ε)
    (hθ : ∀ k : ℕ, Real.exp (s - 1 / 2) - 1 ≤ k → (k : ℝ) ≤ Real.exp (s + 1 / 2) →
      |θ (k : ℝ) - k| ≤ ε * k) :
    (s - 1 / 2) * (2 * Real.pi * T - 9) - 30 * ε * T ^ 3 * (s + 2)
      ≤ ∑ j ∈ Finset.Ico ⌈Real.exp (s - 1 / 2)⌉₊ ⌊Real.exp (s + 1 / 2)⌋₊,
          cPr j * (Real.log j * gfun T s j) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hT23 : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT1 (by norm_num)
  have hmodel := model_core_sum T s hT64 (by linarith) hbig
  have he1 := Real.exp_one_gt_d9
  have he1' := Real.exp_one_lt_d9
  have hea4 : 4 ≤ Real.exp (s - 1 / 2) := by
    have h1 : Real.exp (3 / 2) ≤ Real.exp (s - 1 / 2) := Real.exp_le_exp.mpr (by linarith)
    have h3 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
    have e3 : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hlogea : Real.log (Real.exp (s - 1 / 2)) = s - 1 / 2 := Real.log_exp _
  have hlogeb : Real.log (Real.exp (s + 1 / 2)) = s + 1 / 2 := Real.log_exp _
  have heb_eq : Real.exp (s + 1 / 2) = Real.exp (s - 1 / 2) * Real.exp 1 := by
    rw [← Real.exp_add]; congr 1; ring
  set ea := Real.exp (s - 1 / 2) with hea
  set eb := Real.exp (s + 1 / 2) with heb
  set n₁ := ⌈ea⌉₊ with hn₁
  set n₂ := ⌊eb⌋₊ with hn₂
  have hn₁ea : ea ≤ (n₁ : ℝ) := Nat.le_ceil ea
  have hn₁ea' : (n₁ : ℝ) < ea + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn₂eb : (n₂ : ℝ) ≤ eb := Nat.floor_le (by nlinarith)
  have hn₂eb' : eb < (n₂ : ℝ) + 1 := Nat.lt_floor_add_one eb
  have hn₁4 : 4 ≤ n₁ := by exact_mod_cast (show (4 : ℝ) ≤ n₁ by linarith)
  have hn₁n₂ : n₁ ≤ n₂ := by apply Nat.le_floor; nlinarith
  have hn₁n₂R : (n₁ : ℝ) ≤ n₂ := by exact_mod_cast hn₁n₂
  set m := n₁ - 1 with hm
  set n := n₂ - 1 with hn
  have hm1 : m + 1 = n₁ := by omega
  have hn1 : n + 1 = n₂ := by omega
  have hmn : m ≤ n := by omega
  have hmR : (m : ℝ) = (n₁ : ℝ) - 1 := by rw [hm, Nat.cast_sub (by omega), Nat.cast_one]
  have hnR : (n : ℝ) = (n₂ : ℝ) - 1 := by rw [hn, Nat.cast_sub (by omega), Nat.cast_one]
  have hm3 : (3 : ℝ) ≤ m := by rw [hmR]; linarith
  -- the summation by parts
  set F : ℕ → ℝ := fun k => Real.log (k : ℝ) * gfun T s (k : ℝ) with hF
  set R : ℕ → ℝ := fun k => θ (k : ℝ) - (k : ℝ) with hR
  have hRstep : ∀ k : ℕ, R (k + 1) - R k = cPr (k + 1) - 1 := by
    intro k
    simp only [hR]
    rw [theta_natCast_succ]
    push_cast
    ring
  have hsbp := sbp_Ico R F hmn
  simp_rw [hRstep] at hsbp
  have hsplit : ∑ k ∈ Finset.Ico m n, (cPr (k + 1) - 1) * F (k + 1)
      = ∑ k ∈ Finset.Ico m n, cPr (k + 1) * F (k + 1) - ∑ k ∈ Finset.Ico m n, F (k + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsh1 : ∑ k ∈ Finset.Ico m n, cPr (k + 1) * F (k + 1) = ∑ j ∈ Finset.Ico n₁ n₂, cPr j * F j := by
    rw [← hm1, ← hn1]; exact Finset.sum_Ico_add' (fun j => cPr j * F j) m n 1
  have hsh2 : ∑ k ∈ Finset.Ico m n, F (k + 1) = ∑ j ∈ Finset.Ico n₁ n₂, F j := by
    rw [← hm1, ← hn1]; exact Finset.sum_Ico_add' F m n 1
  rw [hsplit, hsh1, hsh2] at hsbp
  -- pointwise facts on `F`
  have hFnn : ∀ k : ℕ, 1 ≤ k → 0 ≤ F k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact mul_nonneg (Real.log_nonneg hk1) (gfun_nonneg T s k (by linarith))
  have hFle : ∀ k : ℕ, 1 ≤ k → F k ≤ Real.log k * T ^ 2 / k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    simp only [hF]
    unfold gfun
    have hD := DTFacts.DT_norm_le T (s - Real.log k) hT0.le
    have hD2 : ‖DT T (s - Real.log k)‖ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
    have hl := Real.log_nonneg hk1
    rw [show Real.log k * T ^ 2 / k = Real.log k * ((k : ℝ)⁻¹ * T ^ 2) by field_simp]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD2 (by positivity)) hl
  -- the main term
  have hmain : (s - 1 / 2) * (2 * Real.pi * T - 9) ≤ ∑ j ∈ Finset.Ico n₁ n₂, F j := by
    have h1 : ∀ j ∈ Finset.Ico n₁ n₂, (s - 1 / 2) * gfun T s j ≤ F j := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hjR : ea ≤ (j : ℝ) := le_trans hn₁ea (by exact_mod_cast hj.1)
      have hlog : s - 1 / 2 ≤ Real.log j := by
        rw [← hlogea]; exact Real.log_le_log (by linarith) hjR
      exact mul_le_mul_of_nonneg_right hlog (gfun_nonneg T s j (by linarith))
    calc (s - 1 / 2) * (2 * Real.pi * T - 9)
        ≤ (s - 1 / 2) * ∑ j ∈ Finset.Ico n₁ n₂, gfun T s j :=
          mul_le_mul_of_nonneg_left hmodel (by linarith)
      _ = ∑ j ∈ Finset.Ico n₁ n₂, (s - 1 / 2) * gfun T s j := Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.Ico n₁ n₂, F j := Finset.sum_le_sum h1
  -- the boundary terms
  have hbd : ∀ k : ℕ, ea - 1 ≤ k → (k : ℝ) ≤ eb → 1 ≤ k → |R k * F k| ≤ ε * T ^ 2 * (s + 1 / 2) := by
    intro k hk1 hk2 hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hRk : |R k| ≤ ε * k := hθ k hk1 hk2
    have hlog : Real.log k ≤ s + 1 / 2 := by rw [← hlogeb]; exact Real.log_le_log hk0 hk2
    rw [abs_mul, abs_of_nonneg (hFnn k hk)]
    calc |R k| * F k ≤ (ε * k) * (Real.log k * T ^ 2 / k) :=
          mul_le_mul hRk (hFle k hk) (hFnn k hk) (by positivity)
      _ = ε * T ^ 2 * Real.log k := by field_simp
      _ ≤ ε * T ^ 2 * (s + 1 / 2) := mul_le_mul_of_nonneg_left hlog (by positivity)
  have hEn := hbd n (by rw [hnR]; linarith) (by rw [hnR]; linarith) (by omega)
  have hEm := hbd m (by rw [hmR]; linarith) (by rw [hmR]; linarith) (by omega)
  -- the interior sum
  have hEsum : |∑ k ∈ Finset.Ico m n, R k * (F (k + 1) - F k)| ≤ 12 * ε * T ^ 3 * (s + 3 / 2) := by
    have hterm : ∀ k ∈ Finset.Ico m n, |R k * (F (k + 1) - F k)| ≤ 4 * ε * T ^ 3 * (s + 3 / 2) / m := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hmk : (m : ℝ) ≤ k := by exact_mod_cast hk.1
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.2.le
      have hk1 : 1 ≤ k := by omega
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hk0 : (0 : ℝ) < k := by linarith
      have hRk : |R k| ≤ ε * k := hθ k (by rw [hmR] at hmk; linarith) (by rw [hnR] at hkn; linarith)
      have hlog : Real.log k ≤ s + 1 / 2 := by
        rw [← hlogeb]; exact Real.log_le_log hk0 (by rw [hnR] at hkn; linarith)
      have hstep : |F (k + 1) - F k| ≤ 4 * (1 + Real.log k) * T ^ 3 / (k : ℝ) ^ 2 := by
        have h := F_step T s hT1 k hk1
        simp only [hF]
        push_cast
        exact h
      rw [abs_mul]
      calc |R k| * |F (k + 1) - F k| ≤ (ε * k) * (4 * (1 + Real.log k) * T ^ 3 / (k : ℝ) ^ 2) :=
            mul_le_mul hRk hstep (abs_nonneg _) (by positivity)
        _ = 4 * ε * T ^ 3 * (1 + Real.log k) / k := by field_simp
        _ ≤ 4 * ε * T ^ 3 * (s + 3 / 2) / m := by
            apply div_le_div₀ (by positivity) _ (by linarith) hmk
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hcard : ((n - m : ℕ) : ℝ) ≤ 3 * m := by
      have e : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub hmn]
      rw [e, hnR, hmR]
      nlinarith
    calc |∑ k ∈ Finset.Ico m n, R k * (F (k + 1) - F k)|
        ≤ ∑ k ∈ Finset.Ico m n, |R k * (F (k + 1) - F k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico m n, 4 * ε * T ^ 3 * (s + 3 / 2) / m := Finset.sum_le_sum hterm
      _ = ((n - m : ℕ) : ℝ) * (4 * ε * T ^ 3 * (s + 3 / 2) / m) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (3 * m) * (4 * ε * T ^ 3 * (s + 3 / 2) / m) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 12 * ε * T ^ 3 * (s + 3 / 2) := by field_simp; ring
  -- collect
  have hgoal : ∑ j ∈ Finset.Ico n₁ n₂, cPr j * (Real.log j * gfun T s j)
      = ∑ j ∈ Finset.Ico n₁ n₂, cPr j * F j := rfl
  rw [hgoal]
  have h1 := neg_abs_le (R n * F n)
  have h2 := le_abs_self (R m * F m)
  have h3 := le_abs_self (∑ k ∈ Finset.Ico m n, R k * (F (k + 1) - F k))
  have h4 : ε * T ^ 2 * (s + 1 / 2) ≤ ε * T ^ 3 * (s + 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hT23 hε0) (by linarith) (by linarith) (by positivity)
  have h5 : 12 * ε * T ^ 3 * (s + 3 / 2) ≤ 12 * ε * T ^ 3 * (s + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h6 : 0 ≤ ε * T ^ 3 * (s + 2) := by positivity
  linarith

/-- **PNT for `θ`**: `|θ(x) − x| ≤ x(log x)^{−A}` for large `x`. -/
theorem theta_pnt (A : ℝ) : ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → |θ x - x| ≤ x * Real.log x ^ (-A) := by
  have h1 := (L7_2.psi_sub_id_isLittleO_log_rpow A).bound (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : ∀ᶠ x : ℝ in atTop, 2 * Real.sqrt x * Real.log x ≤ 1 / 2 * (x * Real.log x ^ (-A)) := by
    have hlo := isLittleO_log_rpow_rpow_atTop (A + 1) (by norm_num : (0 : ℝ) < 1 / 2)
    have hb := hlo.bound (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [hb, eventually_ge_atTop (3 : ℝ)] with x hx hx3
    have hl1 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hl0 : 0 < Real.log x := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    have hsq : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    have hpos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hl0 A
    have e1 : Real.log x ^ (-A) = (Real.log x ^ A)⁻¹ := Real.rpow_neg hl0.le A
    have e2 : Real.log x ^ (A + 1) = Real.log x ^ A * Real.log x := by
      rw [Real.rpow_add hl0, Real.rpow_one]
    rw [e1]
    rw [e2, ← hsq] at hx
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    rw [show 1 / 2 * (x * (Real.log x ^ A)⁻¹) = x / (2 * Real.log x ^ A) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have h4 := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt x)
    nlinarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (eventually_ge_atTop (3 : ℝ))))
  refine ⟨max x₀ 3, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨hpsi, hpt, hx3⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  have hx1 : 1 ≤ x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hnn : 0 ≤ x * Real.log x ^ (-A) := mul_nonneg (by linarith) (Real.rpow_nonneg hl0.le _)
  simp only [Pi.sub_apply, id, Real.norm_eq_abs] at hpsi
  rw [abs_of_nonneg hnn] at hpsi
  have hpt' := Chebyshev.psi_sub_theta_le hx1
  have hle := Chebyshev.theta_le_psi x
  rw [abs_le] at hpsi ⊢
  constructor <;> linarith [hpsi.1, hpsi.2]

/-- `‖a_n(s)‖² = (4π²)⁻¹Λ(n)²·gfun(n)`. -/
theorem acoefS_normSq (P : ZetaQ.ParamsQ) (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    ‖ZetaQ.acoefS P n s‖ ^ 2 = 1 / (4 * Real.pi ^ 2) * ((Λ n : ℝ) ^ 2 * gfun P.T s n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hsq0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  unfold ZetaQ.acoefS gfun
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, DT_eq]
  rw [div_pow, mul_pow, neg_sq, hsq]
  field_simp
  ring

/-- `‖a(s)‖²` from below by the prime sum on the core window. -/
theorem normA2_ge_prime (P : ZetaQ.ParamsQ) (s : ℝ) (hX : Real.exp (s + 1 / 2) ≤ P.XQ) :
    1 / (4 * Real.pi ^ 2) * ∑ j ∈ Finset.Ico ⌈Real.exp (s - 1 / 2)⌉₊ ⌊Real.exp (s + 1 / 2)⌋₊,
        cPr j * (Real.log j * gfun P.T s j) ≤ ZetaQ.normA2 P s := by
  unfold ZetaQ.normA2 ZetaQ.primeRangeQ
  rw [Finset.mul_sum]
  have hc1 : 1 ≤ ⌈Real.exp (s - 1 / 2)⌉₊ := Nat.one_le_iff_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (Real.exp_pos _)))
  have hsub : Finset.Ico ⌈Real.exp (s - 1 / 2)⌉₊ ⌊Real.exp (s + 1 / 2)⌋₊ ⊆ Finset.Ioc 0 ⌊P.XQ⌋₊ := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_Ioc]
    have h2 : ⌊Real.exp (s + 1 / 2)⌋₊ ≤ ⌊P.XQ⌋₊ := Nat.floor_le_floor hX
    omega
  refine le_trans (Finset.sum_le_sum fun j hj => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _)
  rw [Finset.mem_Ico] at hj
  have hj1 : 1 ≤ j := le_trans hc1 hj.1
  rw [acoefS_normSq P j hj1 s]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hg := gfun_nonneg P.T s j (by positivity)
  unfold cPr
  split_ifs with hp
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    nlinarith
  · simp only [zero_mul]
    positivity

set_option maxHeartbeats 1000000 in
/-- **K3b-L, the node `normA2_lower`**: along the Shell design, `U(s − 1) ≤ ‖a(s)‖²` for `√(log Q) ≤ s ≤ L − 1`,
`U = T/2π` (PNT medium form for `θ`, summation by parts against the integer model sum). -/
theorem normA2_lower (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ZetaQ.ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∀ s : ℝ, Real.sqrt (Real.log Qn) ≤ s → s ≤ P.LB - 1 →
        P.T / (2 * Real.pi) * (s - 1) ≤ ZetaQ.normA2 P s := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r + ε ≤ N := ⟨⌈r + ε⌉₊, Nat.le_ceil _⟩
  set A : ℕ := 4 * N + 4 with hA
  obtain ⟨x₀, hx₀3, hθ⟩ := theta_pnt (A : ℝ)
  have hS1 : (1 : ℝ) ≤ ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  have E2 : ∀ᶠ x : ℝ in atTop, x₀ + 1 ≤ Real.exp (Real.sqrt x - 1 / 2) := by
    have h := Real.tendsto_exp_atTop.comp
      (tendsto_atTop_add_const_right _ (-(1 / 2 : ℝ)) Real.tendsto_sqrt_atTop)
    filter_upwards [h.eventually_ge_atTop (x₀ + 1)] with x hx
    simpa [sub_eq_add_neg] using hx
  have E3 : ∀ᶠ x : ℝ in atTop, 100 * x ^ (3 * N) ≤ Real.exp (Real.sqrt x) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop (6 * N) (b := (1 : ℝ)) (by norm_num)).def
      (by norm_num : (0 : ℝ) < 1 / 100)
    have h' := Real.tendsto_sqrt_atTop.eventually (h.and (eventually_ge_atTop (0 : ℝ)))
    filter_upwards [h', eventually_ge_atTop (0 : ℝ)] with x hx hx0
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Real.norm_eq_abs, one_mul] at hx1
    rw [abs_of_nonneg (by positivity), Real.abs_exp] at hx1
    have e : Real.sqrt x ^ (6 * N) = x ^ (3 * N) := by
      rw [show 6 * N = 2 * (3 * N) by ring, pow_mul, Real.sq_sqrt hx0]
    rw [e] at hx1
    linarith
  filter_upwards [ZetaQ.tendsto_log_nat_atTop.eventually ((eventually_ge_atTop ((150 : ℝ) * 2 ^ A)).and
      ((eventually_ge_atTop (16 : ℝ)).and (E2.and E3))),
    Design.shellDesign_regime S53L75 hS2 r ε hr hε 1 le_rfl, eventually_ge_atTop 3] with Qn hx hreg hQn3
  obtain ⟨hxA, hx16, hxE2, hxE3⟩ := hx
  intro P hdes s hs1 hs2
  obtain ⟨-, -, -, hLL2, -⟩ := hreg P hdes
  obtain ⟨hT, hlogLL, -, -⟩ := Design.scales_of_shellDesignM hS1 hdes hr (by omega)
  have hlam : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
  set x := Real.log (Qn : ℝ) with hxdef
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hsqx : 4 ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  have hs4 : 4 ≤ s := by linarith
  -- scales
  have hLL0 : 0 ≤ P.LL := by linarith
  have hLB4 : P.LB ≤ 4 * x := by
    have hLB : P.LB = P.lam * P.LL := rfl
    have hl : P.lam ≤ 191 / 100 := by rw [hlam]; exact hS2
    have hl0 : 0 ≤ P.lam := by rw [hlam]; linarith
    have := mul_le_mul hl hLL2 hLL0 (by norm_num)
    rw [hLB]; linarith
  -- T
  have hT3 : x ^ 3 ≤ P.T := by
    rw [hT]
    have := Real.rpow_le_rpow_of_exponent_le hx1 (show (3 : ℝ) ≤ r + ε by linarith)
    rwa [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hTN : P.T ≤ x ^ N := by
    rw [hT]
    have := Real.rpow_le_rpow_of_exponent_le hx1 hN
    rwa [Real.rpow_natCast] at this
  have hx3 : 256 * x ≤ x ^ 3 := by
    have hx2 : (256 : ℝ) ≤ x ^ 2 := by nlinarith
    calc 256 * x ≤ x ^ 2 * x := mul_le_mul_of_nonneg_right hx2 hx0.le
      _ = x ^ 3 := by ring
  have hT64 : 64 ≤ P.T := by nlinarith
  have hT0 : 0 < P.T := by linarith
  -- `100 T³ ≤ e^s`
  have hbig : 100 * P.T ^ 3 ≤ Real.exp s := by
    have h1 : P.T ^ 3 ≤ x ^ (3 * N) := by
      calc P.T ^ 3 ≤ (x ^ N) ^ 3 := pow_le_pow_left₀ hT0.le hTN 3
        _ = x ^ (3 * N) := by rw [← pow_mul, mul_comm]
    have h2 : Real.exp (Real.sqrt x) ≤ Real.exp s := Real.exp_le_exp.mpr hs1
    linarith
  have hX : Real.exp (s + 1 / 2) ≤ P.XQ := Real.exp_le_exp.mpr (by linarith)
  -- `θ` on the window
  set εp : ℝ := (s - 1) ^ (-(A : ℝ)) with hεp
  have hθw : ∀ k : ℕ, Real.exp (s - 1 / 2) - 1 ≤ k → (k : ℝ) ≤ Real.exp (s + 1 / 2) →
      |θ (k : ℝ) - k| ≤ εp * k := by
    intro k hk1 hk2
    have hk_x0 : x₀ ≤ k := by
      have : Real.exp (Real.sqrt x - 1 / 2) ≤ Real.exp (s - 1 / 2) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hkexp : Real.exp (s - 1) ≤ k := by
      have e1 : Real.exp (s - 1 / 2) = Real.exp (s - 1) * Real.exp (1 / 2) := by
        rw [← Real.exp_add]; ring_nf
      have h12 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
      have h3 : (s - 1) + 1 ≤ Real.exp (s - 1) := Real.add_one_le_exp _
      nlinarith
    have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos _) hkexp
    have hlogk : s - 1 ≤ Real.log k := by rw [Real.le_log_iff_exp_le hk0]; exact hkexp
    have h := hθ k hk_x0
    have hmono : Real.log k ^ (-(A : ℝ)) ≤ (s - 1) ^ (-(A : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hlogk (neg_nonpos.mpr (Nat.cast_nonneg _))
    calc |θ (k : ℝ) - k| ≤ k * Real.log k ^ (-(A : ℝ)) := h
      _ ≤ k * εp := mul_le_mul_of_nonneg_left hmono hk0.le
      _ = εp * k := mul_comm _ _
  have hεp0 : 0 ≤ εp := Real.rpow_nonneg (by linarith) _
  have hcore := prime_core_sum P.T s εp hT64 (by linarith) hbig hεp0 hθw
  have hge := normA2_ge_prime P s hX
  -- `30 εp T² (s + 2) ≤ 1`
  have hεbound : 30 * εp * P.T ^ 2 * (s + 2) ≤ 1 := by
    have hD0 : 0 < (s - 1) ^ A := pow_pos (by linarith) A
    have e1 : εp = ((s - 1) ^ A)⁻¹ := by
      rw [hεp, Real.rpow_neg (by linarith), Real.rpow_natCast]
    have hs1' : Real.sqrt x / 2 ≤ s - 1 := by linarith
    have hpow : (Real.sqrt x / 2) ^ A ≤ (s - 1) ^ A := pow_le_pow_left₀ (by positivity) hs1' A
    have e2 : (Real.sqrt x / 2) ^ A = x ^ (2 * N + 2) / 2 ^ A := by
      rw [div_pow, hA, show 4 * N + 4 = 2 * (2 * N + 2) by ring, pow_mul, Real.sq_sqrt hx0.le]
    have hT2 : P.T ^ 2 ≤ x ^ (2 * N) := by
      calc P.T ^ 2 ≤ (x ^ N) ^ 2 := pow_le_pow_left₀ hT0.le hTN 2
        _ = x ^ (2 * N) := by rw [← pow_mul, mul_comm]
    have hnum : 30 * P.T ^ 2 * (s + 2) ≤ 150 * x ^ (2 * N + 1) := by
      have h5 : s + 2 ≤ 5 * x := by linarith
      calc 30 * P.T ^ 2 * (s + 2) ≤ 30 * x ^ (2 * N) * (5 * x) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hT2 (by norm_num)) h5 (by linarith) (by positivity)
        _ = 150 * x ^ (2 * N + 1) := by ring
    have hxpow : 150 * x ^ (2 * N + 1) ≤ x ^ (2 * N + 2) / 2 ^ A := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hxA (by positivity : (0 : ℝ) ≤ x ^ (2 * N + 1))
      calc 150 * x ^ (2 * N + 1) * 2 ^ A = x ^ (2 * N + 1) * (150 * 2 ^ A) := by ring
        _ ≤ x ^ (2 * N + 1) * x := this
        _ = x ^ (2 * N + 2) := by ring
    rw [e1, show 30 * ((s - 1) ^ A)⁻¹ * P.T ^ 2 * (s + 2) = 30 * P.T ^ 2 * (s + 2) / (s - 1) ^ A by ring,
      div_le_one hD0]
    linarith
  have hεT : 30 * εp * P.T ^ 3 * (s + 2) ≤ P.T := by
    have e : 30 * εp * P.T ^ 3 * (s + 2) = P.T * (30 * εp * P.T ^ 2 * (s + 2)) := by ring
    rw [e]
    calc P.T * (30 * εp * P.T ^ 2 * (s + 2)) ≤ P.T * 1 := mul_le_mul_of_nonneg_left hεbound hT0.le
      _ = P.T := mul_one _
  have h9 : 9 * (s - 1 / 2) ≤ P.T := by nlinarith
  have hpi := Real.pi_gt_three
  have key : 2 * Real.pi * P.T * (s - 1)
      ≤ (s - 1 / 2) * (2 * Real.pi * P.T - 9) - 30 * εp * P.T ^ 3 * (s + 2) := by
    nlinarith
  calc P.T / (2 * Real.pi) * (s - 1) = 1 / (4 * Real.pi ^ 2) * (2 * Real.pi * P.T * (s - 1)) := by
        field_simp; ring
    _ ≤ 1 / (4 * Real.pi ^ 2) * ((s - 1 / 2) * (2 * Real.pi * P.T - 9) - 30 * εp * P.T ^ 3 * (s + 2)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ 1 / (4 * Real.pi ^ 2) * ∑ j ∈ Finset.Ico ⌈Real.exp (s - 1 / 2)⌉₊ ⌊Real.exp (s + 1 / 2)⌋₊,
          cPr j * (Real.log j * gfun P.T s j) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ ZetaQ.normA2 P s := hge

end F1c
end ShellK
end ZetaShell
