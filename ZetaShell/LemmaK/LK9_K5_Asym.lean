/-
L7_9 helper for node K5 (`small_primes_l2`): the asymptotic step. Eventually in `Q`, for
`ℓ_K ≤ s ≤ log 𝒳`: `T ≥ 1`, `ℒ ≥ 1`, `s ≥ ℓ_K ≥ log Q ≥ 2(log 4 + 4) + 4`, `R₀ < e^{s/2}` (as
`s ≤ λℒ < 2ℒ ≤ 2ℓ_K`), and `C₂ (log Q)^{2(r+ε)} Q^{−1/8} ≤ 1`; then `l2_bound` gives
`‖a − a′‖² ≤ 8/(4π²) + 1/(4π²) < 1`.
-/
import ZetaShell.LemmaK.LK9_K5_Main

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK
namespace K5Aux

theorem small_primes_aux (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) →
      ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
        (fun n => acoef (ZetaQ.Twin (Qn : ℝ) r ε) s n
          - aPrime (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s) n) ≤ 1 := by
  set K₁ : ℝ := Real.log 4 + 4 with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hre : 0 < r + ε := by linarith
  -- real-variable eventualities
  have E1 : ∀ᶠ x : ℝ in atTop, (100 : ℝ) ≤ x := eventually_ge_atTop 100
  have E2 : ∀ᶠ x : ℝ in atTop, 2 * K₁ + 4 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have E3 : ∀ᶠ x : ℝ in atTop,
      C2 * (Real.log x ^ (2 * (r + ε)) * x ^ (-(1 / 8 : ℝ))) ≤ 1 := by
    have hO := (isLittleO_log_rpow_rpow_atTop (2 * (r + ε)) (by norm_num : (0 : ℝ) < 1 / 8)).bound
      (one_div_pos.mpr (by linarith [C2_nonneg]) : (0 : ℝ) < 1 / (C2 + 1))
    filter_upwards [hO, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hpos : 0 < x ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _), Real.norm_of_nonneg hpos.le] at hx
    have hinv : x ^ (-(1 / 8 : ℝ)) = (x ^ (1 / 8 : ℝ))⁻¹ := Real.rpow_neg hx0.le _
    rw [hinv]
    have hC2 := C2_nonneg
    have h1 : Real.log x ^ (2 * (r + ε)) * (x ^ (1 / 8 : ℝ))⁻¹ ≤ 1 / (C2 + 1) := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      exact hx
    calc C2 * (Real.log x ^ (2 * (r + ε)) * (x ^ (1 / 8 : ℝ))⁻¹) ≤ C2 * (1 / (C2 + 1)) :=
          mul_le_mul_of_nonneg_left h1 hC2
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (by linarith)]
          linarith
  have Eall := (E1.and (E2.and E3))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually Eall] with Qn hQ s hs1 hs2
  obtain ⟨h100, hlogQ, hC⟩ := hQ
  set x : ℝ := (Qn : ℝ) with hxdef
  set T : ℝ := ZetaQ.Twin x r ε with hTdef
  have hx0 : 0 < x := by linarith
  have hlog4 : 4 ≤ Real.log x := by linarith
  have hlog0 : 0 ≤ Real.log x := by linarith
  -- T ≥ 1
  have hT1 : 1 ≤ T := by
    rw [hTdef, ZetaQ.Twin]
    exact Real.one_le_rpow (by linarith) hre.le
  -- ℒ ≥ 1
  set L : ℝ := Lc x T with hLdef
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  have hL1 : 1 ≤ L := by
    rw [hLdef, Lc]
    have hz : Real.exp 1 ≤ x * T / (2 * Real.pi) := by
      have he := Real.exp_one_lt_d9
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hz0 : 0 < x * T / (2 * Real.pi) := by positivity
    rw [Real.le_log_iff_exp_le hz0]
    exact hz
  have hL0 : 0 < L := by linarith
  -- ℓ_K ≥ log x and ℒ ≤ ℓ_K
  have hxTL : x ≤ x * T * L := by
    have : 1 ≤ T * L := by nlinarith
    nlinarith
  have hxTL0 : 0 < x * T * L := by positivity
  have hell : Real.log x ≤ ellK x T := by
    rw [ellK]
    exact Real.log_le_log hx0 hxTL
  have hLell : L ≤ ellK x T := by
    have hxT : 0 < x * T := mul_pos hx0 (by linarith)
    have h2pL : 1 ≤ 2 * Real.pi * L := by nlinarith
    have hq : x * T / (2 * Real.pi) ≤ x * T * L := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left h2pL hxT.le
      nlinarith
    calc L = Real.log (x * T / (2 * Real.pi)) := by rw [hLdef, Lc]
      _ ≤ Real.log (x * T * L) := Real.log_le_log (by positivity) hq
      _ = ellK x T := by rw [ellK, ← hLdef]
  -- s bounds
  have hs2' : s ≤ lam * L := by
    have h := hs2
    rw [Xlam, Real.log_exp] at h
    exact h
  have hsx : Real.log x ≤ s := hell.trans hs1
  have hs2K : 2 * K₁ + 4 ≤ s := hlogQ.trans hsx
  have hs_ge2 : 2 ≤ s := by linarith
  have hs_lt : s < 2 * ellK x T := by
    have : lam * L < 2 * L := by nlinarith
    linarith
  -- R₀ < e^{s/2}
  have hR : R0 x T s < Real.exp (s / 2) := by
    rw [R0, ← hLdef]
    have hexp : x * T * L = Real.exp (ellK x T) := by
      rw [ellK, ← hLdef, Real.exp_log hxTL0]
    rw [hexp, ← Real.exp_sub]
    apply Real.exp_lt_exp.mpr
    linarith
  -- apply the deterministic bound
  have hmain := l2_bound T s (R0 x T s) ⌊Xlam lam x T⌋₊ (by linarith) hs_ge2 hR
  refine hmain.trans ?_
  -- estimate the two terms
  have hc : (4 * Real.pi ^ 2)⁻¹ ≤ 1 / 36 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hc0 : 0 ≤ (4 * Real.pi ^ 2)⁻¹ := by positivity
  have hs0 : 0 < s := by linarith
  have hA : (8 / s) * (s / 2 + K₁) ≤ 8 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
    nlinarith
  have hT2 : T ^ 2 = Real.log x ^ (2 * (r + ε)) := by
    rw [hTdef, ZetaQ.Twin, ← Real.rpow_natCast, ← Real.rpow_mul hlog0]
    congr 1
    push_cast
    ring
  have hexp8 : Real.exp (s / 2) ^ (-(1 / 4 : ℝ)) ≤ x ^ (-(1 / 8 : ℝ)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hB : T ^ 2 * (C2 * Real.exp (s / 2) ^ (-(1 / 4 : ℝ))) ≤ 1 := by
    rw [hT2]
    have hC20 := C2_nonneg
    have hl0 : 0 ≤ Real.log x ^ (2 * (r + ε)) := Real.rpow_nonneg hlog0 _
    calc Real.log x ^ (2 * (r + ε)) * (C2 * Real.exp (s / 2) ^ (-(1 / 4 : ℝ)))
        ≤ Real.log x ^ (2 * (r + ε)) * (C2 * x ^ (-(1 / 8 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hl0
          exact mul_le_mul_of_nonneg_left hexp8 hC20
      _ = C2 * (Real.log x ^ (2 * (r + ε)) * x ^ (-(1 / 8 : ℝ))) := by ring
      _ ≤ 1 := hC
  have hAB0 : 0 ≤ (8 / s) * (s / 2 + K₁) := by positivity
  calc (4 * Real.pi ^ 2)⁻¹ * (8 / s) * (s / 2 + (Real.log 4 + 4))
        + (4 * Real.pi ^ 2)⁻¹ * T ^ 2 * (C2 * Real.exp (s / 2) ^ (-(1 / 4 : ℝ)))
      = (4 * Real.pi ^ 2)⁻¹ * ((8 / s) * (s / 2 + K₁))
        + (4 * Real.pi ^ 2)⁻¹ * (T ^ 2 * (C2 * Real.exp (s / 2) ^ (-(1 / 4 : ℝ)))) := by
        rw [hK₁]; ring
    _ ≤ (4 * Real.pi ^ 2)⁻¹ * 8 + (4 * Real.pi ^ 2)⁻¹ * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hA hc0
        · exact mul_le_mul_of_nonneg_left hB hc0
    _ ≤ 1 := by linarith [hc]

end K5Aux
end LemmaK
end ZetaShell
