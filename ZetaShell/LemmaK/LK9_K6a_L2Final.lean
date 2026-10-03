/-
L7_9 round 4: proof of (a1) `model_l2_lower` (statement in `LK9_K6a_Split.lean`):
on `n ∈ [e^{s−1/2}, e^{s+1/2}]` the cutoff is 1 and `|w̃(n)|² = (4π²)⁻¹ n⁻¹|D_T(s − log n)|²`;
sum ≥ integral − `Σ 3T³/n²`; the integral is `∫_{−1/2}^{1/2}|D_T|² ≥ 2πT − 8 − 32/T`.
-/
import ZetaShell.LemmaK.LK9_K6a_L2Lower

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK
namespace K6

lemma gfun_step_low (T s : ℝ) (hT : 1 ≤ T) (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy1 : (n : ℝ) ≤ y)
    (hy2 : y ≤ n + 1) : gfun T s y ≤ gfun T s n + 3 * T ^ 3 / (n : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < y := by linarith
  have hT0 : 0 ≤ T := by linarith
  set Dn := ‖DT T (s - Real.log n)‖ with hDn
  set Dy := ‖DT T (s - Real.log y)‖ with hDy
  have hDn0 : 0 ≤ Dn := norm_nonneg _
  have hDy0 : 0 ≤ Dy := norm_nonneg _
  have hDnT : Dn ≤ T := DTFacts.DT_norm_le T _ hT0
  have hDyT : Dy ≤ T := DTFacts.DT_norm_le T _ hT0
  have hlog : Real.log y - Real.log n ≤ 1 / n := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / n by positivity)
    rw [Real.log_div hy0.ne' hn0.ne'] at h
    have e : y / n - 1 = (y - n) / n := by field_simp
    rw [e] at h
    have : (y - n) / (n : ℝ) ≤ 1 / n := div_le_div_of_nonneg_right (by linarith) hn0.le
    linarith
  have hlog0 : 0 ≤ Real.log y - Real.log n := sub_nonneg.mpr (Real.log_le_log hn0 hy1)
  have hDdiff : Dy - Dn ≤ (3 / 2) * T ^ 2 * (1 / n) := by
    have h1 := DTFacts.DT_lipschitz T (s - Real.log y) (s - Real.log n) hT0
    have h2 : Dy - Dn ≤ ‖DT T (s - Real.log y) - DT T (s - Real.log n)‖ := norm_sub_norm_le _ _
    rw [show s - Real.log y - (s - Real.log n) = -(Real.log y - Real.log n) by ring, abs_neg,
      abs_of_nonneg hlog0] at h1
    calc Dy - Dn ≤ (3 / 2) * T ^ 2 * (Real.log y - Real.log n) := h2.trans h1
      _ ≤ (3 / 2) * T ^ 2 * (1 / n) := mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsq : Dy ^ 2 - Dn ^ 2 ≤ 3 * T ^ 3 / n := by
    have e : Dy ^ 2 - Dn ^ 2 = (Dy - Dn) * (Dy + Dn) := by ring
    rw [e]
    have h2 : Dy + Dn ≤ 2 * T := by linarith
    rcases le_or_gt (Dy - Dn) 0 with h | h
    · have : (Dy - Dn) * (Dy + Dn) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
      have : 0 ≤ 3 * T ^ 3 / n := by positivity
      linarith
    · calc (Dy - Dn) * (Dy + Dn) ≤ ((3 / 2) * T ^ 2 * (1 / n)) * (2 * T) :=
            mul_le_mul hDdiff h2 (by linarith) (by positivity)
        _ = 3 * T ^ 3 / n := by field_simp; try ring
  unfold gfun
  rw [← hDn, ← hDy]
  have hyinv : y⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ hn0 hy1
  have e : y⁻¹ * Dy ^ 2 - (n : ℝ)⁻¹ * Dn ^ 2 = (y⁻¹ - (n : ℝ)⁻¹) * Dy ^ 2 + (n : ℝ)⁻¹ * (Dy ^ 2 - Dn ^ 2) := by
    ring
  have t1 : (y⁻¹ - (n : ℝ)⁻¹) * Dy ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have t2 : (n : ℝ)⁻¹ * (Dy ^ 2 - Dn ^ 2) ≤ (n : ℝ)⁻¹ * (3 * T ^ 3 / n) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have e2 : (n : ℝ)⁻¹ * (3 * T ^ 3 / n) = 3 * T ^ 3 / (n : ℝ) ^ 2 := by field_simp
  linarith

lemma wmod_normsq_core (T s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hρ : |Real.log n - s| ≤ 1 / 2) :
    ‖wmod T s n‖ ^ 2 = (4 * Real.pi ^ 2)⁻¹ * gfun T s n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : rho6 (Real.log n - s) = 1 := by
    unfold rho6; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  unfold wmod gfun
  rw [hr, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, mul_one]
  have h2 : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num; exact Real.rpow_neg_one _
  rw [mul_pow, h2]
  field_simp
  ring


set_option maxHeartbeats 2000000 in
theorem model_l2_lower_aux (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi) - C
        ≤ ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s) := by
  refine ⟨1, ?_⟩
  have hre : 3 ≤ r + ε := by linarith
  have E1 : ∀ᶠ Qn : ℕ in atTop, (100 : ℝ) ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 100)
  have E2 : ∀ᶠ Qn : ℕ in atTop, (4 : ℝ) ≤ Real.log (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 4)
  have E4 : ∀ᶠ Qn : ℕ in atTop, 100 * Real.log (Qn : ℝ) ^ (2 * (r + ε)) ≤ (Qn : ℝ) := by
    have hO := (isLittleO_log_rpow_rpow_atTop (2 * (r + ε)) (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1 / 100)
    have h' : ∀ᶠ y : ℝ in atTop, 100 * Real.log y ^ (2 * (r + ε)) ≤ y := by
      filter_upwards [hO, eventually_ge_atTop (1 : ℝ)] with y hy hy1
      have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _), Real.rpow_one,
        Real.norm_of_nonneg (by linarith)] at hy
      linarith
    exact tendsto_natCast_atTop_atTop.eventually h'
  filter_upwards [E1, E2, E4] with Qn h100 hlog h4 s hs1 hs2
  set x := Real.log (Qn : ℝ) with hx
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  set L := Lc (Qn : ℝ) T with hL
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hT64 : 64 ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 hre
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have : (64 : ℝ) ≤ x ^ 3 := by
      have h4' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hlog 3
      norm_num at h4'; linarith
    rw [hT, ZetaQ.Twin]; linarith
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hT2 : 100 * T ^ 2 ≤ (Qn : ℝ) := by
    have e : T ^ 2 = x ^ (2 * (r + ε)) := by
      rw [hT, ZetaQ.Twin, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      congr 1; push_cast; ring
    rw [e]; exact h4
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  have he1 := Real.exp_one_lt_d9
  have he1' := Real.exp_one_gt_d9
  have hL1 : 1 ≤ L := by
    rw [hL, Lc]
    have hz0 : 0 < (Qn : ℝ) * T / (2 * Real.pi) := by positivity
    rw [Real.le_log_iff_exp_le hz0, le_div_iff₀ (by positivity)]
    nlinarith
  have hQTL : 0 < (Qn : ℝ) * T * L := by positivity
  have hes : (Qn : ℝ) * T * L ≤ Real.exp s := by
    have h := Real.exp_le_exp.mpr hs1
    rw [ellK, ← hL, Real.exp_log hQTL] at h
    exact h
  have hbig : 100 * T ^ 3 ≤ Real.exp s := by
    have h1 : 100 * T ^ 3 ≤ (Qn : ℝ) * T := by
      calc 100 * T ^ 3 = (100 * T ^ 2) * T := by ring
        _ ≤ (Qn : ℝ) * T := mul_le_mul_of_nonneg_right hT2 hT0.le
    have h2 : (Qn : ℝ) * T ≤ (Qn : ℝ) * T * L := le_mul_of_one_le_right (by positivity) hL1
    linarith
  have hs1' : 1 ≤ s := by
    have hQTL100 : (100 : ℝ) ≤ (Qn : ℝ) * T * L := by
      rw [mul_assoc]
      exact le_trans h100 (le_mul_of_one_le_right hQ0.le (one_le_mul_of_one_le_of_one_le hT1 hL1))
    have : Real.log ((Qn : ℝ) * T * L) ≥ Real.log 100 := Real.log_le_log (by norm_num) hQTL100
    have h100' : (1 : ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; linarith
    rw [ellK, ← hL] at hs1; linarith
  set N := ⌊Xlam lam (Qn : ℝ) T⌋₊ with hN
  set ea := Real.exp (s - 1 / 2) with hea
  set eb := Real.exp (s + 1 / 2) with heb
  have hea1 : 1 ≤ ea := Real.one_le_exp (by linarith)
  have hea0 : 0 < ea := by linarith
  have heaeb : ea + 1 ≤ eb := by
    have e : eb = ea * Real.exp 1 := by rw [hea, heb, ← Real.exp_add]; congr 1; ring
    rw [e]; nlinarith
  have hebX : eb ≤ Xlam lam (Qn : ℝ) T := by
    have h := hs2
    rw [Xlam, Real.log_exp] at h
    rw [Xlam]; exact Real.exp_le_exp.mpr (by linarith)
  set n₁ := ⌈ea⌉₊ with hn₁
  set n₂ := ⌊eb⌋₊ with hn₂
  have hn₁ea : ea ≤ (n₁ : ℝ) := Nat.le_ceil ea
  have hn₁ea' : (n₁ : ℝ) < ea + 1 := Nat.ceil_lt_add_one hea0.le
  have hn₂eb : (n₂ : ℝ) ≤ eb := Nat.floor_le (by linarith)
  have hn₂eb' : eb < (n₂ : ℝ) + 1 := Nat.lt_floor_add_one eb
  have hn₁1 : 1 ≤ n₁ := by exact_mod_cast (show (1 : ℝ) ≤ n₁ by linarith)
  have hn₁n₂ : n₁ ≤ n₂ := by
    apply Nat.le_floor; linarith
  have hn₂N : n₂ ≤ N := Nat.floor_le_floor hebX
  have hn₁R : (1 : ℝ) ≤ n₁ := by linarith
  -- (A) restrict the sum
  have hA : ∑ n ∈ Finset.Ico n₁ n₂, ‖wmod T s n‖ ^ 2 ≤ ZetaQ.l2sq N (wmod T s) := by
    unfold ZetaQ.l2sq
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_Ico] at hn
      rw [Finset.mem_Ioc]
      exact ⟨by omega, by omega⟩
    · intro n _ _; exact sq_nonneg _
  -- (B) on the core `w̃` is `gfun`
  have hB : ∀ n ∈ Finset.Ico n₁ n₂, ‖wmod T s n‖ ^ 2 = (4 * Real.pi ^ 2)⁻¹ * gfun T s n := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hnR1 : (n₁ : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnR2 : (n : ℝ) < n₂ := by exact_mod_cast hn.2
    have hn0 : (0 : ℝ) < n := by linarith
    apply wmod_normsq_core T s n (by omega)
    rw [abs_le]
    constructor
    · have := Real.log_le_log hea0 (show ea ≤ n by linarith)
      rw [hea, Real.log_exp] at this; linarith
    · have := Real.log_le_log hn0 (show (n : ℝ) ≤ eb by linarith)
      rw [heb, Real.log_exp] at this; linarith
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
  have h32T : 32 / T ≤ 1 / 2 := by rw [div_le_iff₀ hT0]; linarith
  have hcore : 2 * Real.pi * T - 9 ≤ ∑ n ∈ Finset.Ico n₁ n₂, gfun T s n := by
    linarith
  have hsumw : ∑ n ∈ Finset.Ico n₁ n₂, ‖wmod T s n‖ ^ 2
      = (4 * Real.pi ^ 2)⁻¹ * ∑ n ∈ Finset.Ico n₁ n₂, gfun T s n := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl hB
  have hpi2 : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  have hfin : T / (2 * Real.pi) - 1 ≤ (4 * Real.pi ^ 2)⁻¹ * (2 * Real.pi * T - 9) := by
    have e : (4 * Real.pi ^ 2)⁻¹ * (2 * Real.pi * T - 9) = T / (2 * Real.pi) - 9 / (4 * Real.pi ^ 2) := by
      field_simp; ring
    rw [e]
    have : 9 / (4 * Real.pi ^ 2) ≤ 1 := by rw [div_le_one hpi2]; nlinarith
    linarith
  calc T / (2 * Real.pi) - 1 ≤ (4 * Real.pi ^ 2)⁻¹ * (2 * Real.pi * T - 9) := hfin
    _ ≤ (4 * Real.pi ^ 2)⁻¹ * ∑ n ∈ Finset.Ico n₁ n₂, gfun T s n :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = ∑ n ∈ Finset.Ico n₁ n₂, ‖wmod T s n‖ ^ 2 := hsumw.symm
    _ ≤ ZetaQ.l2sq N (wmod T s) := hA

end K6
end LemmaK
end ZetaShell
