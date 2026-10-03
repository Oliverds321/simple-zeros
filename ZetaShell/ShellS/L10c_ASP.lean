/-
L10c_ASP (L7_10c, 3 Oct 2026): **the PNT upper bound on the near window**:
`Σ_{e^{s−1} ≤ p ≤ e^{s+1}} log p · p⁻¹|D_T(s − log p)|² ≤ 2πT + 1 + 40εT³` when `|θ(k) − k| ≤ εk` on the window,
by summation by parts against `θ(k) − k` (as L7_3c's `prime_core_sum`, upper side) and the integer model sum
`Σ gfun(j) ≤ ∫ gfun + Σ 4T³/j² ≤ 2πT + …` (`gfun_step`, Plancherel `∫|D_T|² = 2πT`).
-/
import ZetaShell.ShellS.L10c_ASC
import ZetaShell.ShellK.LF_K3bP

noncomputable section
open scoped BigOperators Chebyshev
open MeasureTheory

namespace ZetaShell
namespace ShellS
namespace ASc

open ZetaShell.LemmaK ZetaShell.LemmaK.K6 ZetaShell.ShellK.F1c

/-- `∫_{e^a}^{e^b} gfun ≤ 2πT`. -/
theorem gfun_int_le (T s a b : ℝ) (hT : 0 ≤ T) (hab : a ≤ b) :
    ∫ y in Real.exp a..Real.exp b, gfun T s y ≤ 2 * Real.pi * T := by
  rw [gfun_subst T s a b hab]
  have e := intervalIntegral.integral_comp_sub_left (fun v => ‖DT T v‖ ^ 2) s (a := a) (b := b)
  rw [e, intervalIntegral.integral_of_le (by linarith)]
  have hint : Integrable (fun v => ‖DT T v‖ ^ 2) := by
    have h := ZetaQ.DT_normSq_integrable (PT T) hT
    refine h.congr (ae_of_all _ fun v => ?_)
    simp only; rw [DT_eq_PT]
  have hfull : (∫ v : ℝ, ‖DT T v‖ ^ 2) = 2 * Real.pi * T := by
    have h := ZetaQ.DT_sq_integral (PT T) hT
    have hPT : (PT T).T = T := rfl
    rw [hPT] at h
    rw [← h]
    congr 1; funext v; rw [DT_eq_PT]
  rw [← hfull]
  exact setIntegral_le_integral hint (ae_of_all _ fun v => sq_nonneg _)

theorem gfun_diff_le (T s : ℝ) (hT : 1 ≤ T) (k : ℕ) (hk : 1 ≤ k) :
    |gfun T s ((k : ℝ) + 1) - gfun T s k| ≤ 4 * T ^ 3 / (k : ℝ) ^ 2 := by
  have h1 := gfun_step T s hT k hk ((k : ℝ) + 1) (by linarith) le_rfl
  have h2 := gfun_step_low T s hT k hk ((k : ℝ) + 1) (by linarith) le_rfl
  have hpos : (0 : ℝ) ≤ T ^ 3 / (k : ℝ) ^ 2 := by positivity
  have e3 : 3 * T ^ 3 / (k : ℝ) ^ 2 = 3 * (T ^ 3 / (k : ℝ) ^ 2) := by ring
  have e4 : 4 * T ^ 3 / (k : ℝ) ^ 2 = 4 * (T ^ 3 / (k : ℝ) ^ 2) := by ring
  rw [e3] at h2; rw [e4] at h1 ⊢
  rw [abs_le]; constructor <;> linarith

theorem gfun_le_T2 (T s : ℝ) (hT : 0 ≤ T) (y : ℝ) (hy : 0 < y) : gfun T s y ≤ T ^ 2 / y := by
  unfold gfun
  have hD := DTFacts.DT_norm_le T (s - Real.log y) hT
  have hD2 : ‖DT T (s - Real.log y)‖ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hD2 (inv_nonneg.mpr hy.le)

set_option maxHeartbeats 1000000 in
/-- **the prime sum on the near window, upper bound**. -/
theorem prime_window_upper (T s ε : ℝ) (hT1 : 1 ≤ T) (hs : 3 ≤ s) (hbig : 100 * T ^ 3 ≤ Real.exp s)
    (hε0 : 0 ≤ ε)
    (hθ : ∀ k : ℕ, Real.exp (s - 1) - 1 ≤ k → (k : ℝ) ≤ Real.exp (s + 1) → |θ (k : ℝ) - k| ≤ ε * k) :
    ∑ j ∈ Finset.Ico ⌈Real.exp (s - 1)⌉₊ (⌊Real.exp (s + 1)⌋₊ + 1), cPr j * gfun T s j
      ≤ 2 * Real.pi * T + 1 + 34 * ε * T ^ 3 := by
  have hT0 : 0 < T := by linarith
  have hT23 : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT1 (by norm_num)
  have he1 := Real.exp_one_gt_d9
  have he1' := Real.exp_one_lt_d9
  set ea := Real.exp (s - 1) with hea
  set eb := Real.exp (s + 1) with heb
  have hea7 : 7 ≤ ea := by
    have h1 : Real.exp 2 ≤ ea := Real.exp_le_exp.mpr (by linarith)
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have heb_eq : eb = ea * (Real.exp 1 * Real.exp 1) := by
    rw [heb, hea, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hee : Real.exp 1 * Real.exp 1 ≤ 7.4 := by nlinarith
  have hee7 : 7 ≤ Real.exp 1 * Real.exp 1 := by nlinarith
  have heaeb : ea + 1 ≤ eb := by
    rw [heb_eq]
    have : ea * 7 ≤ ea * (Real.exp 1 * Real.exp 1) := mul_le_mul_of_nonneg_left hee7 (by linarith)
    linarith
  have hebea : eb ≤ 7.4 * ea := by
    rw [heb_eq]
    have := mul_le_mul_of_nonneg_left hee (by linarith : (0 : ℝ) ≤ ea)
    linarith
  have hes : Real.exp s = Real.exp 1 * ea := by rw [hea, ← Real.exp_add]; ring_nf
  set n₁ := ⌈ea⌉₊ with hn₁
  set n := ⌊eb⌋₊ with hn
  have hn₁ea : ea ≤ (n₁ : ℝ) := Nat.le_ceil ea
  have hn₁ea' : (n₁ : ℝ) < ea + 1 := Nat.ceil_lt_add_one (by linarith)
  have hneb : (n : ℝ) ≤ eb := Nat.floor_le (by linarith)
  have hneb' : eb < (n : ℝ) + 1 := Nat.lt_floor_add_one eb
  have hn₁7 : 7 ≤ n₁ := by exact_mod_cast (show (7 : ℝ) ≤ n₁ by linarith)
  have hn₁n : n₁ ≤ n := by apply Nat.le_floor; linarith
  set m := n₁ - 1 with hm
  have hm1 : m + 1 = n₁ := by omega
  have hmn : m ≤ n := by omega
  have hmR : (m : ℝ) = (n₁ : ℝ) - 1 := by rw [hm, Nat.cast_sub (by omega), Nat.cast_one]
  have hm6 : (6 : ℝ) ≤ m := by rw [hmR]; linarith
  -- summation by parts
  set F : ℕ → ℝ := fun k => gfun T s (k : ℝ) with hF
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
  have hsh1 : ∑ k ∈ Finset.Ico m n, cPr (k + 1) * F (k + 1) = ∑ j ∈ Finset.Ico n₁ (n + 1), cPr j * F j := by
    rw [← hm1]; exact Finset.sum_Ico_add' (fun j => cPr j * F j) m n 1
  have hsh2 : ∑ k ∈ Finset.Ico m n, F (k + 1) = ∑ j ∈ Finset.Ico n₁ (n + 1), F j := by
    rw [← hm1]; exact Finset.sum_Ico_add' F m n 1
  rw [hsplit, hsh1, hsh2] at hsbp
  have hFnn : ∀ k : ℕ, 0 ≤ F k := fun k => gfun_nonneg T s k (Nat.cast_nonneg k)
  have hFle : ∀ k : ℕ, 1 ≤ k → F k ≤ T ^ 2 / k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    exact gfun_le_T2 T s hT0.le k hk0
  -- the model sum
  have hmodel : ∑ j ∈ Finset.Ico n₁ (n + 1), F j ≤ 2 * Real.pi * T + 1 := by
    have hint : ∀ k : ℕ, 1 ≤ k → IntervalIntegrable (gfun T s) volume (k : ℝ) ((k : ℝ) + 1) := by
      intro k hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      exact gfun_contOn T s k (k + 1) (by linarith)
    have hstep : ∀ j ∈ Finset.Ico n₁ (n + 1),
        F j ≤ (∫ y in (j : ℝ)..((j : ℝ) + 1), gfun T s y) + 4 * T ^ 3 / (n₁ : ℝ) ^ 2 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : 1 ≤ j := by omega
      have hjR : (n₁ : ℝ) ≤ j := by exact_mod_cast hj.1
      have hj0 : (0 : ℝ) < n₁ := by linarith
      have h := intervalIntegral.integral_mono_on (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)
        (intervalIntegrable_const (c := gfun T s j - 4 * T ^ 3 / (j : ℝ) ^ 2)) (hint j hj1)
        (fun y hy => by have := gfun_step T s hT1 j hj1 y hy.1 hy.2; linarith)
      rw [intervalIntegral.integral_const, smul_eq_mul] at h
      have hjj : 4 * T ^ 3 / (j : ℝ) ^ 2 ≤ 4 * T ^ 3 / (n₁ : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hj0.le hjR 2)
      simp only [hF]
      linarith
    have hadj : ∑ k ∈ Finset.Ico n₁ (n + 1), (∫ y in (k : ℝ)..((k : ℝ) + 1), gfun T s y)
        = ∫ y in (n₁ : ℝ)..((n + 1 : ℕ) : ℝ), gfun T s y := by
      have h := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k : ℕ => (k : ℝ))
        (f := gfun T s) (μ := volume) (by omega : n₁ ≤ n + 1)
        (fun k hk => by
          have hk1 : 1 ≤ k := le_trans (by omega) hk.1
          have := hint k hk1
          push_cast; exact this)
      simpa using h
    have hI : (∫ y in (n₁ : ℝ)..((n + 1 : ℕ) : ℝ), gfun T s y) ≤ 2 * Real.pi * T := by
      have hlo : Real.exp (s - 1) ≤ (n₁ : ℝ) := hn₁ea
      have hhi : ((n + 1 : ℕ) : ℝ) ≤ Real.exp (s + 2) := by
        push_cast
        have : Real.exp (s + 1) + 1 ≤ Real.exp (s + 2) := by
          have e : Real.exp (s + 2) = Real.exp (s + 1) * Real.exp 1 := by rw [← Real.exp_add]; ring_nf
          nlinarith [Real.exp_pos (s + 1)]
        linarith
      have hmono := intervalIntegral.integral_mono_interval (μ := volume) (f := gfun T s) hlo
        (show (n₁ : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by push_cast; linarith [show (n₁ : ℝ) ≤ n by exact_mod_cast hn₁n]) hhi
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (ae_of_all _ fun y hy => gfun_nonneg T s y (le_trans (Real.exp_pos _).le hy.1.le)))
        (by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le (Real.exp_le_exp.mpr (by linarith))]
          exact gfun_contOn T s _ _ (Real.exp_pos _))
      exact hmono.trans (gfun_int_le T s (s - 1) (s + 2) hT0.le (by linarith))
    have hcard : ((n + 1 - n₁ : ℕ) : ℝ) ≤ 8 * n₁ := by
      rw [Nat.cast_sub (by omega)]; push_cast
      linarith
    calc ∑ j ∈ Finset.Ico n₁ (n + 1), F j
        ≤ ∑ j ∈ Finset.Ico n₁ (n + 1), ((∫ y in (j : ℝ)..((j : ℝ) + 1), gfun T s y)
            + 4 * T ^ 3 / (n₁ : ℝ) ^ 2) := Finset.sum_le_sum hstep
      _ = (∫ y in (n₁ : ℝ)..((n + 1 : ℕ) : ℝ), gfun T s y)
            + ((n + 1 - n₁ : ℕ) : ℝ) * (4 * T ^ 3 / (n₁ : ℝ) ^ 2) := by
          rw [Finset.sum_add_distrib, hadj, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ 2 * Real.pi * T + (8 * n₁) * (4 * T ^ 3 / (n₁ : ℝ) ^ 2) := by
          gcongr
      _ = 2 * Real.pi * T + 32 * T ^ 3 / n₁ := by
          have hn0 : (n₁ : ℝ) ≠ 0 := by positivity
          field_simp; ring
      _ ≤ 2 * Real.pi * T + 1 := by
          have hn0 : (0 : ℝ) < n₁ := by linarith
          have : 32 * T ^ 3 / n₁ ≤ 1 := by
            rw [div_le_one hn0]
            have h1 : Real.exp 1 * ea ≤ 2.72 * ea := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
            linarith
          linarith
  -- boundary terms
  have hbd : ∀ k : ℕ, ea - 1 ≤ k → (k : ℝ) ≤ eb → 1 ≤ k → |R k * F k| ≤ ε * T ^ 2 := by
    intro k hk1 hk2 hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hRk : |R k| ≤ ε * k := hθ k hk1 hk2
    rw [abs_mul, abs_of_nonneg (hFnn k)]
    calc |R k| * F k ≤ (ε * k) * (T ^ 2 / k) := mul_le_mul hRk (hFle k hk) (hFnn k) (by positivity)
      _ = ε * T ^ 2 := by field_simp
  have hEn := hbd n (by linarith) hneb (by omega)
  have hEm := hbd m (by rw [hmR]; linarith) (by rw [hmR]; linarith) (by omega)
  -- interior
  have hEsum : |∑ k ∈ Finset.Ico m n, R k * (F (k + 1) - F k)| ≤ 32 * ε * T ^ 3 := by
    have hterm : ∀ k ∈ Finset.Ico m n, |R k * (F (k + 1) - F k)| ≤ 4 * ε * T ^ 3 / m := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hmk : (m : ℝ) ≤ k := by exact_mod_cast hk.1
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.2.le
      have hk1 : 1 ≤ k := by omega
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hRk : |R k| ≤ ε * k := hθ k (by rw [hmR] at hmk; linarith) (by linarith)
      have hstep : |F (k + 1) - F k| ≤ 4 * T ^ 3 / (k : ℝ) ^ 2 := by
        have h := gfun_diff_le T s hT1 k hk1
        simp only [hF]; push_cast; exact h
      rw [abs_mul]
      calc |R k| * |F (k + 1) - F k| ≤ (ε * k) * (4 * T ^ 3 / (k : ℝ) ^ 2) :=
            mul_le_mul hRk hstep (abs_nonneg _) (by positivity)
        _ = 4 * ε * T ^ 3 / k := by field_simp
        _ ≤ 4 * ε * T ^ 3 / m := div_le_div_of_nonneg_left (by positivity) (by linarith) hmk
    have hcard : ((n - m : ℕ) : ℝ) ≤ 8 * m := by
      rw [Nat.cast_sub hmn, hmR]
      linarith
    calc |∑ k ∈ Finset.Ico m n, R k * (F (k + 1) - F k)|
        ≤ ∑ k ∈ Finset.Ico m n, |R k * (F (k + 1) - F k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico m n, 4 * ε * T ^ 3 / m := Finset.sum_le_sum hterm
      _ = ((n - m : ℕ) : ℝ) * (4 * ε * T ^ 3 / m) := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (8 * m) * (4 * ε * T ^ 3 / m) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 32 * ε * T ^ 3 := by field_simp; ring
  have hgoal : ∑ j ∈ Finset.Ico n₁ (n + 1), cPr j * gfun T s j = ∑ j ∈ Finset.Ico n₁ (n + 1), cPr j * F j := rfl
  rw [hgoal]
  have h1 := le_abs_self (R n * F n)
  have h2 := neg_abs_le (R m * F m)
  have h3 := neg_abs_le (∑ k ∈ Finset.Ico m n, R k * (F (k + 1) - F k))
  have h4 : ε * T ^ 2 ≤ ε * T ^ 3 := mul_le_mul_of_nonneg_left hT23 hε0
  linarith

theorem aNearP_norm_le (Q T κ : ℝ) (Ξ : ℝ → ℝ) (hΞ : ZetaShell.PropZ.NearCutoff Ξ) (s : ℝ) (n : ℕ) :
    ‖aNearP Q T κ Ξ s n‖ ≤ ‖TrackF.acoefS T s n‖ := by
  unfold aNearP
  split_ifs with h
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΞ.nonneg _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (hΞ.le_one _)
  · simp

theorem aNearP_support (Q T κ : ℝ) (Ξ : ℝ → ℝ) (hΞ : ZetaShell.PropZ.NearCutoff Ξ) (hκ : 0 < κ) (s : ℝ) (n : ℕ)
    (h : aNearP Q T κ Ξ s n ≠ 0) : n.Prime ∧ Q < (n : ℝ) ∧ |Real.log n - s| < κ := by
  unfold aNearP at h
  split_ifs at h with hp
  · refine ⟨hp.1, hp.2, ?_⟩
    have hΞ0 : Ξ ((Real.log n - s) / κ) ≠ 0 := by
      intro h0; apply h; rw [h0]; simp
    have hmem : (Real.log n - s) / κ ∈ Set.Ioo (-1 : ℝ) 1 :=
      hΞ.supp (subset_tsupport _ (Function.mem_support.mpr hΞ0))
    have h1 : |(Real.log n - s) / κ| < 1 := abs_lt.mpr ⟨hmem.1, hmem.2⟩
    rw [abs_div, abs_of_pos hκ, div_lt_one hκ] at h1
    exact h1
  · exact absurd rfl h

/-- **`‖b‖² ≤ (4π²)⁻¹(s+1) Σ_{window} cPr·gfun`** for the near-P vector, `κ ≤ 1`. -/
theorem nearP_l2_le (Q T κ : ℝ) (Ξ : ℝ → ℝ) (hΞ : ZetaShell.PropZ.NearCutoff Ξ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) (Nn : ℕ) :
    ZetaQ.l2sq Nn (aNearP Q T κ Ξ s)
      ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) *
        ∑ j ∈ Finset.Ico ⌈Real.exp (s - 1)⌉₊ (⌊Real.exp (s + 1)⌋₊ + 1), cPr j * gfun T s j := by
  unfold ZetaQ.l2sq
  rw [Finset.mul_sum]
  set W := Finset.Ico ⌈Real.exp (s - 1)⌉₊ (⌊Real.exp (s + 1)⌋₊ + 1) with hW
  have hterm0 : ∀ j, 0 ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) * (cPr j * gfun T s j) := fun j =>
    mul_nonneg (by positivity) (mul_nonneg (cPr_nonneg j) (gfun_nonneg T s j (Nat.cast_nonneg j)))
  calc ∑ n ∈ Finset.Ioc 0 Nn, ‖aNearP Q T κ Ξ s n‖ ^ 2
      = ∑ n ∈ (Finset.Ioc 0 Nn).filter (fun n => aNearP Q T κ Ξ s n ≠ 0), ‖aNearP Q T κ Ξ s n‖ ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        split_ifs with h
        · rfl
        · push Not at h; rw [h]; simp
    _ ≤ ∑ n ∈ (Finset.Ioc 0 Nn).filter (fun n => aNearP Q T κ Ξ s n ≠ 0),
          (4 * Real.pi ^ 2)⁻¹ * (s + 1) * (cPr n * gfun T s n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' := Finset.mem_filter.mp hn
        obtain ⟨hp, -, hclose⟩ := aNearP_support Q T κ Ξ hΞ hκ s n hn'.2
        have hn0 : 0 < n := hp.pos
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
        have h1 : ‖aNearP Q T κ Ξ s n‖ ^ 2 ≤ ‖TrackF.acoefS T s n‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (aNearP_norm_le Q T κ Ξ hΞ s n) 2
        have h2 := LemmaK.K5Aux.norm_acoef_sq T s n hn0
        have hΛ : ArithmeticFunction.vonMangoldt n = Real.log n := ArithmeticFunction.vonMangoldt_apply_prime hp
        have hlog : Real.log n ≤ s + 1 := by linarith [(abs_lt.mp hclose).2]
        have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
        have hc : cPr n = Real.log n := by unfold cPr; rw [if_pos hp]
        refine le_trans h1 (le_of_eq_of_le (show ‖TrackF.acoefS T s n‖ ^ 2 = ‖LemmaK.acoef T s n‖ ^ 2 from rfl) ?_)
        rw [h2, hΛ, hc]
        unfold gfun
        have hD0 : 0 ≤ ‖DT T (s - Real.log n)‖ ^ 2 := sq_nonneg _
        have e : (4 * Real.pi ^ 2)⁻¹ * (Real.log n ^ 2 / n) * ‖DT T (s - Real.log n)‖ ^ 2
            = (4 * Real.pi ^ 2)⁻¹ * Real.log n * (Real.log n * ((n : ℝ)⁻¹ * ‖DT T (s - Real.log n)‖ ^ 2)) := by
          field_simp
        rw [e]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ ∑ n ∈ W, (4 * Real.pi ^ 2)⁻¹ * (s + 1) * (cPr n * gfun T s n) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun j _ _ => hterm0 j)
        intro n hn
        have hn' := Finset.mem_filter.mp hn
        obtain ⟨hp, -, hclose⟩ := aNearP_support Q T κ Ξ hΞ hκ s n hn'.2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hp.pos
        have h1 : s - 1 < Real.log n := by linarith [(abs_lt.mp hclose).1]
        have h2 : Real.log n < s + 1 := by linarith [(abs_lt.mp hclose).2]
        rw [hW, Finset.mem_Ico]
        constructor
        · apply Nat.ceil_le.mpr
          rw [← Real.exp_log hnR]; exact (Real.exp_lt_exp.mpr h1).le
        · apply Nat.lt_succ_of_le; apply Nat.le_floor
          rw [← Real.exp_log hnR]; exact (Real.exp_lt_exp.mpr h2).le

end ASc
end ShellS
end ZetaShell
