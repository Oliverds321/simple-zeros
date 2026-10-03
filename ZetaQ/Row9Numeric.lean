/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Row-9 numeric lemma (Mathlib-only, `Row2Numeric`-style): the closed-form row-9 majorant sits
inside `c·Q²·T` eventually along the design `T = (log Q)^{r+ε}`, `L = λ*ℒ`, for every `c > 0`.
-/

open Filter Real

namespace ZetaQ
namespace Row9Numeric

/-- Eventual facts in `x = log Q`, with an arbitrary constant `K` on the `x³`-vs-`Q^{0.37}` clause. -/
theorem x_facts3 (r ε K : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop,
      10 ≤ x ∧ (r + ε) * Real.log x ≤ x ∧ K * x ^ 3 ≤ Real.exp (0.37 * x) := by
  have hre : 0 < r + ε := by linarith
  have h1 : ∀ᶠ x : ℝ in atTop, 10 ≤ x := eventually_ge_atTop 10
  have h2 : ∀ᶠ x : ℝ in atTop, (r + ε) * Real.log x ≤ x := by
    have h := Real.isLittleO_log_id_atTop.def (one_div_pos.mpr hre)
    filter_upwards [h, eventually_ge_atTop (0:ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs, id_eq] at hx
    rw [abs_of_nonneg hx0] at hx
    have hla : Real.log x ≤ |Real.log x| := le_abs_self _
    calc (r + ε) * Real.log x ≤ (r + ε) * (1 / (r + ε) * x) := by
          apply mul_le_mul_of_nonneg_left _ hre.le
          linarith
      _ = x := by field_simp
  have h4 : ∀ᶠ x : ℝ in atTop, K * x ^ 3 ≤ Real.exp (0.37 * x) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 3 (b := (0.37:ℝ)) (by norm_num)).def
      (by positivity : (0:ℝ) < 1 / K)
    filter_upwards [h, eventually_ge_atTop (0:ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 3), Real.abs_exp] at hx
    calc K * x ^ 3 ≤ K * (1 / K * Real.exp (0.37 * x)) := by gcongr
      _ = Real.exp (0.37 * x) := by field_simp
  filter_upwards [h1, h2, h4] with x a b d
  exact ⟨a, b, d⟩

set_option maxHeartbeats 800000 in
/-- **The row-9 closed form at an arbitrary positive constant.**  For every `c > 0`, eventually
along the design (`T = (log Q)^{r+ε}`, `ℒ = log(QT/2π)`, `L = λ*ℒ`, `l = log(T/2π)`):
`(24/π)QL√X(1+log Q)(1+L) + (8/π)(44l+24)L√X((3/4)Q(10+6L)+2) ≤ c·Q²·T`, `X = e^L`. -/
theorem row9_closed_eventually (r ε c : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ Q : ℝ in Filter.atTop,
      let T := Real.log Q ^ (r + ε)
      let ℒ := Real.log (Q * T / (2 * Real.pi))
      let L := (1.2507321515 : ℝ) * ℒ
      let l := Real.log (T / (2 * Real.pi))
      24 / Real.pi * Q * L * Real.sqrt (Real.exp L) * (1 + Real.log Q) * (1 + L)
        + 8 / Real.pi * (44 * l + 24) * L * Real.sqrt (Real.exp L) * (3 / 4 * Q * (10 + 6 * L) + 2)
        ≤ c * Q ^ 2 * T := by
  have hre : 0 < r + ε := by linarith
  have hK : (0:ℝ) < 9000 / c := by positivity
  filter_upwards [Real.tendsto_log_atTop.eventually (x_facts3 r ε (9000 / c) hr hε hK),
    eventually_gt_atTop (0:ℝ)] with Q hx hQ0
  obtain ⟨hx10, hlogx, hexp2⟩ := hx
  intro T ℒ L l
  have hT0 : T = Real.log Q ^ (r + ε) := rfl
  have hℒ0 : ℒ = Real.log (Q * T / (2 * Real.pi)) := rfl
  have hL0 : L = 1.2507321515 * ℒ := rfl
  have hl0 : l = Real.log (T / (2 * Real.pi)) := rfl
  clear_value T ℒ L l
  set x := Real.log Q with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hQexp : Real.exp x = Q := by rw [hxdef]; exact Real.exp_log hQ0
  clear_value x
  have hQ1 : 1 ≤ Q := by rw [← hQexp]; exact Real.one_le_exp_iff.mpr hx0.le
  have hQ0' : 0 ≤ Q := hQ0.le
  -- T
  have hT : T = Real.exp ((r + ε) * Real.log x) := by
    rw [hT0, Real.rpow_def_of_pos hx0]; congr 1; ring
  have hTpos : 0 < T := by rw [hT]; exact Real.exp_pos _
  have hlogT : Real.log T = (r + ε) * Real.log x := by rw [hT, Real.log_exp]
  -- pi facts
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi315 : Real.pi < 3.15 := Real.pi_lt_d2
  have hpipos : 0 < Real.pi := Real.pi_pos
  have h2pi : 1 ≤ 2 * Real.pi := by linarith
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg h2pi
  have hlog2pi' : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  -- ℒ, l
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hrl : 0 ≤ (r + ε) * Real.log x := mul_nonneg hre.le hlogx0
  have hℒ : ℒ = x + (r + ε) * Real.log x - Real.log (2 * Real.pi) := by
    rw [hℒ0, Real.log_div (by positivity) (by positivity), Real.log_mul hQ0.ne' hTpos.ne',
      hlogT, ← hxdef]
  have hl : l = (r + ε) * Real.log x - Real.log (2 * Real.pi) := by
    rw [hl0, Real.log_div (by positivity) (by positivity), hlogT]
  have hℒnn : 0 ≤ ℒ := by rw [hℒ]; linarith
  have hℒle : ℒ ≤ x + (r + ε) * Real.log x := by rw [hℒ]; linarith
  have hℒ2x : ℒ ≤ 2 * x := by linarith
  have hl2x : l ≤ 2 * x := by rw [hl]; linarith
  have hlnn : -7 ≤ l := by rw [hl]; linarith
  have hl0' : 0 ≤ 44 * l + 24 := by
    -- l = (r+ε) log x − log 2π ≥ 3 log 10 − log(2π) > 0
    have hlx : Real.log 10 ≤ Real.log x := Real.log_le_log (by norm_num) hx10
    have h10 : (2:ℝ) < Real.log 10 := by
      have := Real.exp_one_lt_d9
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    have : (r + ε) * Real.log x ≥ 3 * 2 := by nlinarith
    rw [hl]; nlinarith
  -- L
  have hLnn : 0 ≤ L := by rw [hL0]; linarith
  have hL : L ≤ 2.52 * x := by rw [hL0]; linarith
  -- the four exponentials
  set a := Real.exp (0.63 * x) with ha
  set b := Real.exp (0.63 * ((r + ε) * Real.log x)) with hb
  set u := Real.exp (0.37 * x) with hu
  set w := Real.exp (0.37 * ((r + ε) * Real.log x)) with hw
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hu0 : 0 < u := Real.exp_pos _
  have hw1 : 1 ≤ w := by
    rw [hw]; exact Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) hrl)
  have hsX_le : Real.sqrt (Real.exp L) ≤ a * b := by
    rw [← Real.exp_half, ha, hb, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hL0]; linarith
  have hQab : Q = a * u := by
    rw [ha, hu, ← Real.exp_add, ← hQexp]; congr 1; ring
  have hTbw : T = b * w := by
    rw [hT, hb, hw, ← Real.exp_add]; congr 1; ring
  have hsX0 : 0 ≤ Real.sqrt (Real.exp L) := Real.sqrt_nonneg _
  -- the polynomial bound: (LHS without √X) ≤ 5000 Q x³
  have hpoly : 24 / Real.pi * Q * L * (1 + x) * (1 + L)
      + 8 / Real.pi * (44 * l + 24) * L * (3 / 4 * Q * (10 + 6 * L) + 2) ≤ 9000 * Q * x ^ 3 := by
    have hi1 : 24 / Real.pi ≤ 8 := by
      rw [div_le_iff₀ hpipos]; linarith
    have hi2 : 8 / Real.pi ≤ 8 / 3 := by
      rw [div_le_div_iff₀ hpipos (by norm_num)]; linarith
    have hQx : 2 ≤ Q * x := by nlinarith
    have h1x : 1 + x ≤ 2 * x := by linarith
    have h1L : 1 + L ≤ 3.52 * x := by linarith
    have hl' : 44 * l + 24 ≤ 91 * x := by linarith
    have h10L : 10 + 6 * L ≤ 16.12 * x := by linarith
    have hA : 24 / Real.pi * Q * L * (1 + x) * (1 + L) ≤ 8 * Q * (2.52 * x) * (2 * x) * (3.52 * x) := by
      have e1 : 24 / Real.pi * Q * L * (1 + x) * (1 + L)
          = (24 / Real.pi) * (Q * (L * ((1 + x) * (1 + L)))) := by ring
      have e2 : 8 * Q * (2.52 * x) * (2 * x) * (3.52 * x)
          = 8 * (Q * ((2.52 * x) * ((2 * x) * (3.52 * x)))) := by ring
      rw [e1, e2]
      apply mul_le_mul hi1 _ (by positivity) (by norm_num)
      apply mul_le_mul_of_nonneg_left _ hQ0'
      apply mul_le_mul hL _ (by positivity) (by positivity)
      apply mul_le_mul h1x h1L (by positivity) (by positivity)
    have hB : 8 / Real.pi * (44 * l + 24) * L * (3 / 4 * Q * (10 + 6 * L) + 2)
        ≤ 8 / 3 * (91 * x) * (2.52 * x) * (3 / 4 * Q * (16.12 * x) + Q * x) := by
      have e1 : 8 / Real.pi * (44 * l + 24) * L * (3 / 4 * Q * (10 + 6 * L) + 2)
          = (8 / Real.pi) * ((44 * l + 24) * (L * (3 / 4 * Q * (10 + 6 * L) + 2))) := by ring
      have e2 : 8 / 3 * (91 * x) * (2.52 * x) * (3 / 4 * Q * (16.12 * x) + Q * x)
          = (8 / 3) * ((91 * x) * ((2.52 * x) * (3 / 4 * Q * (16.12 * x) + Q * x))) := by ring
      rw [e1, e2]
      apply mul_le_mul hi2 _ (by positivity) (by norm_num)
      apply mul_le_mul hl' _ (by positivity) (by positivity)
      apply mul_le_mul hL _ (by positivity) (by positivity)
      apply add_le_add _ hQx
      apply mul_le_mul_of_nonneg_left h10L (by positivity)
    have hQx3 : 0 ≤ Q * x ^ 3 := mul_nonneg hQ0' (pow_nonneg hx0.le 3)
    linarith [hA, hB, hQx3]
  have hmul : (24 / Real.pi * Q * L * (1 + x) * (1 + L)
        + 8 / Real.pi * (44 * l + 24) * L * (3 / 4 * Q * (10 + 6 * L) + 2)) * Real.sqrt (Real.exp L)
      ≤ 9000 * Q * x ^ 3 * (a * b) :=
    mul_le_mul hpoly hsX_le hsX0 (by positivity)
  have hm : 0 ≤ Q * x ^ 3 * (a * b) := by positivity
  have hlhs : 24 / Real.pi * Q * L * Real.sqrt (Real.exp L) * (1 + x) * (1 + L)
      + 8 / Real.pi * (44 * l + 24) * L * Real.sqrt (Real.exp L) * (3 / 4 * Q * (10 + 6 * L) + 2)
      = (24 / Real.pi * Q * L * (1 + x) * (1 + L)
        + 8 / Real.pi * (44 * l + 24) * L * (3 / 4 * Q * (10 + 6 * L) + 2)) * Real.sqrt (Real.exp L) := by
    ring
  rw [hlhs]
  calc (24 / Real.pi * Q * L * (1 + x) * (1 + L)
        + 8 / Real.pi * (44 * l + 24) * L * (3 / 4 * Q * (10 + 6 * L) + 2)) * Real.sqrt (Real.exp L)
      ≤ 9000 * Q * x ^ 3 * (a * b) := hmul
    _ = c * (Q * (a * b)) * (9000 / c * x ^ 3) := by field_simp
    _ ≤ c * (Q * (a * b)) * (u * w) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc 9000 / c * x ^ 3 ≤ u := hexp2
          _ ≤ u * w := le_mul_of_one_le_right hu0.le hw1
    _ = c * Q ^ 2 * T := by rw [hTbw, hQab]; ring


end Row9Numeric
end ZetaQ
