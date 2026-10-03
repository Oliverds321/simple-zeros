/-
L7_9 round 4: proof of (a2) `model_outer` (statement in `LK9_K6a_Split.lean`), from the generic outer bound
(`outer_le`) and the difference sum (`dw_sum`): outer mass `≤ (16Δ²)⁻¹Σ|Δw̃|² ≤ C·U/ℒ²`.
-/
import ZetaShell.LemmaK.LK9_K6a_OuterGen
import ZetaShell.LemmaK.LK9_K6a_DwSum

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK
namespace K6

lemma sum_shift_one (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc 0 (N + 1), f n = f 1 + ∑ m ∈ Finset.Ioc 0 N, f (m + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_Ioc_succ_top (by omega)]
    ring

set_option maxHeartbeats 1000000 in
theorem model_outer_aux (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s)
        - ∫ β in (-(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))..(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)), ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s) β‖ ^ 2
        ≤ C * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi)) / Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ^ 2 := by
  set e₁ := Real.exp 1 with he₁
  have he0 : 0 < e₁ := Real.exp_pos 1
  have hCz : 0 ≤ Cz := tsum_nonneg fun k => by positivity
  set K' : ℝ := 18 * e₁ + 36 + 1024 * e₁ * Cz + 512 * Cz with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨4 * Real.pi * e₁ ^ 3 * K', ?_⟩
  have hre : 3 ≤ r + ε := by linarith
  have E1 : ∀ᶠ Qn : ℕ in atTop, (100 : ℝ) ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 100)
  have E2 : ∀ᶠ Qn : ℕ in atTop, (4 : ℝ) ≤ Real.log (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 4)
  have E3 : ∀ᶠ Qn : ℕ in atTop, Real.log (Qn : ℝ) ^ (r + ε) ≤ (Qn : ℝ) := by
    have hO3 := (isLittleO_log_rpow_rpow_atTop (r + ε) (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1)
    have h3 : ∀ᶠ y : ℝ in atTop, Real.log y ^ (r + ε) ≤ y := by
      filter_upwards [hO3, eventually_ge_atTop (1 : ℝ)] with y hy hy1
      have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _), Real.rpow_one,
        Real.norm_of_nonneg (by linarith), one_mul] at hy
      exact hy
    exact tendsto_natCast_atTop_atTop.eventually h3
  filter_upwards [E1, E2, E3] with Qn h100 hlog hTQ s hs1 hs2
  set x := Real.log (Qn : ℝ) with hx
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  set L := Lc (Qn : ℝ) T with hL
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hT64 : 64 ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 hre
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have : (64 : ℝ) ≤ x ^ 3 := by
      have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hlog 3
      norm_num at h4; linarith
    rw [hT, ZetaQ.Twin]; linarith
  have hTQ2 : T ≤ (Qn : ℝ) := hTQ
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  have he1 := Real.exp_one_lt_d9
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
  have hQle : (Qn : ℝ) ≤ (Qn : ℝ) * T * L := by
    rw [mul_assoc]; exact le_mul_of_one_le_right hQ0.le (by nlinarith)
  have h64Q : 64 * (Qn : ℝ) ≤ (Qn : ℝ) * T * L := by
    rw [mul_assoc]
    have : 64 ≤ T * L := le_trans (by norm_num) (mul_le_mul hT64 hL1 (by norm_num) (by linarith))
    nlinarith [mul_le_mul_of_nonneg_left this hQ0.le]
  have hQTL1 : 1 ≤ (Qn : ℝ) * T * L := by linarith
  have hs0 : 0 ≤ s := by
    have : Real.log ((Qn : ℝ) * T * L) ≥ 0 := Real.log_nonneg hQTL1
    rw [ellK, ← hL] at hs1; linarith
  have hs3 : 3 ≤ s := by
    have : x ≤ Real.log ((Qn : ℝ) * T * L) := Real.log_le_log hQ0 hQle
    rw [ellK, ← hL] at hs1; linarith
  set N := ⌊Xlam lam (Qn : ℝ) T⌋₊ with hN
  set xs := Real.exp s with hxs
  have hxs0 : 0 < xs := Real.exp_pos _
  have hTx : T ≤ xs := by linarith
  have hE1 : Real.exp (s - 1) = xs / e₁ := by rw [Real.exp_sub]
  have hTs : T ≤ Real.exp (s - 1) / 2 := by
    rw [hE1, div_div, le_div_iff₀ (by positivity)]
    nlinarith
  -- `Δ ∈ (0, 1/2]`
  set Δ := T * L / (2 * xs) with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have hΔ1 : Δ ≤ 1 / 2 := by
    rw [hΔ, div_le_iff₀ (by positivity)]
    have : T * L ≤ (Qn : ℝ) * T * L := by
      have h1 : (1 : ℝ) ≤ Qn := by linarith
      nlinarith [mul_pos (by linarith : (0 : ℝ) < T) (by linarith : (0 : ℝ) < L)]
    linarith
  -- boundary values of `w̃`
  have hw0 : wmod T s 0 = 0 := wmod_zero_of T s 0 (by simp; rw [abs_of_nonneg hs0]; linarith)
  have hw1 : wmod T s 1 = 0 := wmod_zero_of T s 1 (by simp; rw [abs_of_nonneg hs0]; linarith)
  have hwN : wmod T s (N + 1) = 0 := by
    apply wmod_zero_of
    have hX : Real.exp (s + 1) ≤ Xlam lam (Qn : ℝ) T := by
      have h := hs2
      rw [Xlam, Real.log_exp] at h
      rw [Xlam]; exact Real.exp_le_exp.mpr (by linarith)
    have hN1 : Xlam lam (Qn : ℝ) T < ((N + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have : s + 1 < Real.log ((N + 1 : ℕ) : ℝ) := by
      rw [← Real.log_exp (s + 1)]
      exact Real.log_lt_log (Real.exp_pos _) (lt_of_le_of_lt hX hN1)
    rw [abs_of_pos (by linarith)]; linarith
  -- the outer bound
  have hout := outer_le N (wmod T s) hw0 hwN Δ hΔ0 hΔ1
  have hshift : ZetaQ.l2sq (N + 1) (fun n => wmod T s n - wmod T s (n - 1))
      = ∑ m ∈ Finset.Ioc 0 N, ‖wmod T s (m + 1) - wmod T s m‖ ^ 2 := by
    unfold ZetaQ.l2sq
    rw [sum_shift_one N (fun n => ‖wmod T s n - wmod T s (n - 1)‖ ^ 2)]
    simp only [Nat.add_sub_cancel]
    rw [show (1 - 1 : ℕ) = 0 from rfl, hw1, hw0, sub_self, norm_zero]
    ring_nf
  have hdw := dw_sum T s (by linarith) hs3 hTs N
  rw [hshift] at hout
  -- the size of the difference sum
  have hbr : 8 / Real.exp (s - 1) ^ 3 * (18 * T ^ 2 * (Real.exp (s + 1) + 2)
      + 512 * T ^ 4 * ((2 * Real.exp (s + 1) / T + 1) * Cz)) ≤ 8 * e₁ ^ 3 * K' * T ^ 3 / xs ^ 2 := by
    have hsp : Real.exp (s + 1) = xs * e₁ := by rw [Real.exp_add]
    rw [hE1, hsp]
    have hT0 : 0 < T := by linarith
    have hxs1 : 1 ≤ xs := by linarith
    have e : 8 / (xs / e₁) ^ 3 * (18 * T ^ 2 * (xs * e₁ + 2)
        + 512 * T ^ 4 * ((2 * (xs * e₁) / T + 1) * Cz))
        = 8 * e₁ ^ 3 * (18 * e₁ * T ^ 2 * xs + 36 * T ^ 2 + 1024 * e₁ * Cz * T ^ 3 * xs
          + 512 * Cz * T ^ 4) / xs ^ 3 := by
      field_simp; ring
    rw [e]
    have hnum : 18 * e₁ * T ^ 2 * xs + 36 * T ^ 2 + 1024 * e₁ * Cz * T ^ 3 * xs + 512 * Cz * T ^ 4
        ≤ K' * T ^ 3 * xs := by
      have hT2 : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have h1 : 18 * e₁ * T ^ 2 * xs ≤ 18 * e₁ * T ^ 3 * xs :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT2 (by positivity)) hxs0.le
      have h2 : 36 * T ^ 2 ≤ 36 * T ^ 3 * xs := by
        calc 36 * T ^ 2 ≤ 36 * T ^ 3 := mul_le_mul_of_nonneg_left hT2 (by norm_num)
          _ ≤ 36 * T ^ 3 * xs := le_mul_of_one_le_right (by positivity) hxs1
      have h3 : 512 * Cz * T ^ 4 ≤ 512 * Cz * T ^ 3 * xs := by
        have h4 : T ^ 4 ≤ T ^ 3 * xs := by
          rw [show T ^ 4 = T ^ 3 * T by ring]
          exact mul_le_mul_of_nonneg_left hTx (by positivity)
        calc 512 * Cz * T ^ 4 ≤ 512 * Cz * (T ^ 3 * xs) := mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = 512 * Cz * T ^ 3 * xs := by ring
      have e2 : K' * T ^ 3 * xs = 18 * e₁ * T ^ 3 * xs + 36 * T ^ 3 * xs
          + 1024 * e₁ * Cz * T ^ 3 * xs + 512 * Cz * T ^ 3 * xs := by rw [hK']; ring
      rw [e2]; linarith
    calc 8 * e₁ ^ 3 * (18 * e₁ * T ^ 2 * xs + 36 * T ^ 2 + 1024 * e₁ * Cz * T ^ 3 * xs
          + 512 * Cz * T ^ 4) / xs ^ 3
        ≤ 8 * e₁ ^ 3 * (K' * T ^ 3 * xs) / xs ^ 3 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = 8 * e₁ ^ 3 * K' * T ^ 3 / xs ^ 2 := by field_simp; try ring
  have hc : 0 ≤ (16 * Δ ^ 2)⁻¹ := by positivity
  have hfin : (16 * Δ ^ 2)⁻¹ * (8 * e₁ ^ 3 * K' * T ^ 3 / xs ^ 2)
      = 4 * Real.pi * e₁ ^ 3 * K' * (T / (2 * Real.pi)) / L ^ 2 := by
    rw [hΔ]; field_simp; ring
  calc _ ≤ (16 * Δ ^ 2)⁻¹ * ∑ m ∈ Finset.Ioc 0 N, ‖wmod T s (m + 1) - wmod T s m‖ ^ 2 := hout
    _ ≤ (16 * Δ ^ 2)⁻¹ * (8 * e₁ ^ 3 * K' * T ^ 3 / xs ^ 2) :=
        mul_le_mul_of_nonneg_left (hdw.trans hbr) hc
    _ = _ := hfin

end K6
end LemmaK
end ZetaShell
