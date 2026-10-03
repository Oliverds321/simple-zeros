/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Row2Numeric.lean — **the row-2 numeric lemma of `trace_row`.**

Mathlib-only.  Receipt: `audit/Row2Numeric_and_Cor3_REPORT.md`, Task 1.
`row2_error_eventually` is step E(ii) of
`audit/MuqUniform_REPORT.md` §4: with `T = (log Q)^{r+ε}`, `ℒ = log(QT/2π)`, `L = λ*ℒ`
(`λ* = 1.2507321515`), the row-2 prime-part error `2L√X(3Q(1+L)+2)/log 2` of
`Budget.abs_trGhatFam_sub_muPart_le` sits inside `(1/100 − 1/(200π))·|𝔉_Q|·T` eventually, at the
effective family-size floor `|𝔉_Q| ≥ (18/π⁴)Q² − 6Q(1+log Q)²` (`Budget.sizeR_qle_lower'`).
Regime (eventual): `log Q ≥ 10`, `(r+ε) log log Q ≤ log Q`, `300(log Q)² ≤ Q`,
`200000(log Q)² ≤ Q^{0.37}` (binding: `Q ≳ 10²⁴`).

`row2_error_eventually_gen` is the same inequality at an ARBITRARY positive constant
`c·Q²·T` on the right — what the dyadic family needs (its `rowR1` is the smaller
`sZone·0.26895/(4ℒ)` and its size floor is `(27/(2π⁴))Q²`).
All declarations are `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

open Filter Real

namespace ZetaQ
namespace Row2Numeric

/-- Eventual facts in the variable `x = log Q`. -/
theorem x_facts (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      10 ≤ x ∧ (r + ε) * Real.log x ≤ x ∧ 300 * x ^ 2 ≤ Real.exp x ∧
        200000 * x ^ 2 ≤ Real.exp (0.37 * x) := by
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
  have h3 : ∀ᶠ x : ℝ in atTop, 300 * x ^ 2 ≤ Real.exp x := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2 (b := (1:ℝ)) one_pos).def
      (by norm_num : (0:ℝ) < 1 / 300)
    filter_upwards [h, eventually_ge_atTop (0:ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs, one_mul] at hx
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2), Real.abs_exp] at hx
    linarith
  have h4 : ∀ᶠ x : ℝ in atTop, 200000 * x ^ 2 ≤ Real.exp (0.37 * x) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2 (b := (0.37:ℝ)) (by norm_num)).def
      (by norm_num : (0:ℝ) < 1 / 200000)
    filter_upwards [h, eventually_ge_atTop (0:ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2), Real.abs_exp] at hx
    linarith
  filter_upwards [h1, h2, h3, h4] with x a b c d
  exact ⟨a, b, c, d⟩

/-- Row-2 prime-part error sits inside the conductor row eventually, with
`c = 1/100 - 1/(200π)`. -/
theorem row2_error_eventually (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in Filter.atTop,
      let T := Real.log Q ^ (r + ε)
      let ℒ := Real.log (Q * T / (2 * Real.pi))
      let L := (1.2507321515 : ℝ) * ℒ
      2 * L * Real.sqrt (Real.exp L) * (3 * Q * (1 + L) + 2) / Real.log 2
        ≤ (1 / 100 - 1 / (200 * Real.pi))
            * ((18 / Real.pi ^ 4) * Q ^ 2 - 6 * Q * (1 + Real.log Q) ^ 2) * T := by
  have hre : 0 < r + ε := by linarith
  filter_upwards [Real.tendsto_log_atTop.eventually (x_facts r ε hr hε),
    eventually_gt_atTop (0:ℝ)] with Q hx hQ0
  obtain ⟨hx10, hlogx, hexp1, hexp2⟩ := hx
  intro T ℒ L
  have hT0 : T = Real.log Q ^ (r + ε) := rfl
  have hℒ0 : ℒ = Real.log (Q * T / (2 * Real.pi)) := rfl
  have hL0 : L = 1.2507321515 * ℒ := rfl
  clear_value T ℒ L
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
  -- ℒ
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hrl : 0 ≤ (r + ε) * Real.log x := mul_nonneg hre.le hlogx0
  have hℒ : ℒ = x + (r + ε) * Real.log x - Real.log (2 * Real.pi) := by
    rw [hℒ0, Real.log_div (by positivity) (by positivity), Real.log_mul hQ0.ne' hTpos.ne',
      hlogT, ← hxdef]
  have hℒnn : 0 ≤ ℒ := by rw [hℒ]; linarith
  have hℒle : ℒ ≤ x + (r + ε) * Real.log x := by rw [hℒ]; linarith
  have hℒ2x : ℒ ≤ 2 * x := by linarith
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
  -- log 2
  have hlog2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  -- constants
  have hc : 1 / 120 ≤ 1 / 100 - 1 / (200 * Real.pi) := by
    have : 1 / (200 * Real.pi) ≤ 1 / 600 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hpi4 : Real.pi ^ 4 ≤ 100 := by
    have : Real.pi ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ hpipos.le hpi315.le 4
    norm_num at this; linarith
  have h18 : 0.18 ≤ 18 / Real.pi ^ 4 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hbr : 0.1 * Q ^ 2 ≤ (18 / Real.pi ^ 4) * Q ^ 2 - 6 * Q * (1 + x) ^ 2 := by
    have hxx : x * 10 ≤ x * x := mul_le_mul_of_nonneg_left hx10 hx0.le
    have h1x : (1 + x) ^ 2 ≤ 4 * x ^ 2 := by linarith
    have h6 : 6 * Q * (1 + x) ^ 2 ≤ 0.08 * Q ^ 2 := by
      calc 6 * Q * (1 + x) ^ 2 ≤ 6 * Q * (4 * x ^ 2) := by gcongr
        _ = 0.08 * Q * (300 * x ^ 2) := by ring
        _ ≤ 0.08 * Q * Real.exp x := by gcongr
        _ = 0.08 * Q ^ 2 := by rw [hQexp]; ring
    have h18' : 0.18 * Q ^ 2 ≤ (18 / Real.pi ^ 4) * Q ^ 2 := by gcongr
    linarith
  -- numerator bound
  have hA : Q * L ≤ Q * (2.52 * x) := mul_le_mul_of_nonneg_left hL hQ0'
  have hB : Q * L ^ 2 ≤ Q * (2.52 * x) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLnn hL 2) hQ0'
  have hC : x ≤ Q * x := le_mul_of_one_le_left hx0.le hQ1
  have hD : Q * x * 10 ≤ Q * x * x := mul_le_mul_of_nonneg_left hx10 (by positivity)
  have hnum : 2 * L * (3 * Q * (1 + L) + 2) ≤ 64 * Q * x ^ 2 := by
    linarith [hA, hB, hC, hD, hL, hLnn]
  have hmul : 2 * L * (3 * Q * (1 + L) + 2) * Real.sqrt (Real.exp L)
      ≤ 64 * Q * x ^ 2 * (a * b) :=
    mul_le_mul hnum hsX_le (Real.sqrt_nonneg _) (by positivity)
  have hm : 0 ≤ Q * x ^ 2 * (a * b) := by positivity
  have hBr0 : 0 ≤ (18 / Real.pi ^ 4) * Q ^ 2 - 6 * Q * (1 + x) ^ 2 := by
    have : 0 ≤ 0.1 * Q ^ 2 := by positivity
    linarith
  calc 2 * L * Real.sqrt (Real.exp L) * (3 * Q * (1 + L) + 2) / Real.log 2
      = 2 * L * (3 * Q * (1 + L) + 2) * Real.sqrt (Real.exp L) / Real.log 2 := by ring
    _ ≤ 64 * Q * x ^ 2 * (a * b) / 0.69 :=
        div_le_div₀ (by positivity) hmul (by norm_num) hlog2.le
    _ ≤ 100 * Q * x ^ 2 * (a * b) := by
        rw [div_le_iff₀ (by norm_num)]; linarith [hm]
    _ ≤ (1 / 1200) * (Q * (a * b)) * (200000 * x ^ 2) := by linarith [hm]
    _ ≤ (1 / 1200) * (Q * (a * b)) * (u * w) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc 200000 * x ^ 2 ≤ u := hexp2
          _ ≤ u * w := le_mul_of_one_le_right hu0.le hw1
    _ = (1 / 120) * (0.1 * Q ^ 2) * T := by rw [hTbw, hQab]; ring
    _ ≤ (1 / 100 - 1 / (200 * Real.pi))
          * ((18 / Real.pi ^ 4) * Q ^ 2 - 6 * Q * (1 + x) ^ 2) * T := by
        apply mul_le_mul_of_nonneg_right _ hTpos.le
        exact mul_le_mul hc hbr (by positivity) (by linarith)

/-! ## The general form: any positive constant `c·Q²·T` on the right -/

/-- Eventual facts in `x = log Q`, with an arbitrary constant `K` on the `x²`-vs-`Q^{0.37}`
clause. -/
theorem x_facts_gen (r ε K : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop,
      10 ≤ x ∧ (r + ε) * Real.log x ≤ x ∧ K * x ^ 2 ≤ Real.exp (0.37 * x) := by
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
  have h4 : ∀ᶠ x : ℝ in atTop, K * x ^ 2 ≤ Real.exp (0.37 * x) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2 (b := (0.37:ℝ)) (by norm_num)).def
      (by positivity : (0:ℝ) < 1 / K)
    filter_upwards [h, eventually_ge_atTop (0:ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2), Real.abs_exp] at hx
    calc K * x ^ 2 ≤ K * (1 / K * Real.exp (0.37 * x)) := by gcongr
      _ = Real.exp (0.37 * x) := by field_simp
  filter_upwards [h1, h2, h4] with x a b d
  exact ⟨a, b, d⟩

/-- **The row-2 inequality at an arbitrary positive constant.**  For every `c > 0`, eventually
`2L√(exp L)(3Q(1+L)+2)/log 2 ≤ c·Q²·T`.  Same route as `row2_error_eventually`. -/
theorem row2_error_eventually_gen (r ε c : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ Q : ℝ in Filter.atTop,
      let T := Real.log Q ^ (r + ε)
      let ℒ := Real.log (Q * T / (2 * Real.pi))
      let L := (1.2507321515 : ℝ) * ℒ
      2 * L * Real.sqrt (Real.exp L) * (3 * Q * (1 + L) + 2) / Real.log 2 ≤ c * Q ^ 2 * T := by
  have hre : 0 < r + ε := by linarith
  have hK : (0:ℝ) < 100 / c := by positivity
  filter_upwards [Real.tendsto_log_atTop.eventually (x_facts_gen r ε (100 / c) hr hε hK),
    eventually_gt_atTop (0:ℝ)] with Q hx hQ0
  obtain ⟨hx10, hlogx, hexp2⟩ := hx
  intro T ℒ L
  have hT0 : T = Real.log Q ^ (r + ε) := rfl
  have hℒ0 : ℒ = Real.log (Q * T / (2 * Real.pi)) := rfl
  have hL0 : L = 1.2507321515 * ℒ := rfl
  clear_value T ℒ L
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
  -- ℒ
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hrl : 0 ≤ (r + ε) * Real.log x := mul_nonneg hre.le hlogx0
  have hℒ : ℒ = x + (r + ε) * Real.log x - Real.log (2 * Real.pi) := by
    rw [hℒ0, Real.log_div (by positivity) (by positivity), Real.log_mul hQ0.ne' hTpos.ne',
      hlogT, ← hxdef]
  have hℒnn : 0 ≤ ℒ := by rw [hℒ]; linarith
  have hℒle : ℒ ≤ x + (r + ε) * Real.log x := by rw [hℒ]; linarith
  have hℒ2x : ℒ ≤ 2 * x := by linarith
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
  -- log 2
  have hlog2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  -- numerator bound
  have hA : Q * L ≤ Q * (2.52 * x) := mul_le_mul_of_nonneg_left hL hQ0'
  have hB : Q * L ^ 2 ≤ Q * (2.52 * x) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLnn hL 2) hQ0'
  have hC : x ≤ Q * x := le_mul_of_one_le_left hx0.le hQ1
  have hD : Q * x * 10 ≤ Q * x * x := mul_le_mul_of_nonneg_left hx10 (by positivity)
  have hnum : 2 * L * (3 * Q * (1 + L) + 2) ≤ 64 * Q * x ^ 2 := by
    linarith [hA, hB, hC, hD, hL, hLnn]
  have hmul : 2 * L * (3 * Q * (1 + L) + 2) * Real.sqrt (Real.exp L)
      ≤ 64 * Q * x ^ 2 * (a * b) :=
    mul_le_mul hnum hsX_le (Real.sqrt_nonneg _) (by positivity)
  have hm : 0 ≤ Q * x ^ 2 * (a * b) := by positivity
  calc 2 * L * Real.sqrt (Real.exp L) * (3 * Q * (1 + L) + 2) / Real.log 2
      = 2 * L * (3 * Q * (1 + L) + 2) * Real.sqrt (Real.exp L) / Real.log 2 := by ring
    _ ≤ 64 * Q * x ^ 2 * (a * b) / 0.69 :=
        div_le_div₀ (by positivity) hmul (by norm_num) hlog2.le
    _ ≤ 100 * Q * x ^ 2 * (a * b) := by
        rw [div_le_iff₀ (by norm_num)]; linarith [hm]
    _ = c * (Q * (a * b)) * (100 / c * x ^ 2) := by field_simp
    _ ≤ c * (Q * (a * b)) * (u * w) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc 100 / c * x ^ 2 ≤ u := hexp2
          _ ≤ u * w := le_mul_of_one_le_right hu0.le hw1
    _ = c * Q ^ 2 * T := by rw [hTbw, hQab]; ring

end Row2Numeric
end ZetaQ
