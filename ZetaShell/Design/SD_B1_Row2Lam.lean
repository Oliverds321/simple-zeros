/-
Node SD-B1 (L7_7, F1b): **"Row 2" (trace prime part) at ANY bandwidth `0 < λ < 2`** — the λ-generic form of
`ZetaQ.Row2Numeric.row2_error_eventually_gen` (`Row2Numeric.lean:219`, literal `λ* = 1.2507321515`).
`2L√X(3Q(1+L)+2)/log 2 ≤ c·Q²T`, `L = λℒ`, `X = e^L`. Saving `Q^{−(2−λ)/2}·T^{−(2−λ)/2}·polylog` (L7_2 I8, L7_4 1b).
The ZetaQ proof uses `polylog ≤ K·exp(0.37·log Q)` (`x_facts_gen`); here the exponent must be `< (2−λ)/2`
(0.045 at λ = 1.91). Sanity (`sanity_L7_7.py`, λ = 1.91, `r+ε = 3.5`, `c = 10⁻⁴`): log(LHS/RHS) = +15.2 at
`log Q = 10²` (false), −21.3 at `10³`, −422 at `10⁴`, −4.5·10⁴ at `10⁶`.
Deps: none (real analysis). Difficulty M.
PROVED: the ZetaQ proof with the split `0.63 + 0.37` of `log Q` replaced by `λ/2 + (1 − λ/2)` and `L ≤ 2.52x` by `L ≤ 4x`.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

open Filter

theorem row2_error_eventually_lam (lam r ε c : ℝ) (hlam0 : 0 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r)
    (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ Q : ℝ in atTop,
      let T := Real.log Q ^ (r + ε)
      let ℒ := Real.log (Q * T / (2 * Real.pi))
      let L := lam * ℒ
      2 * L * Real.sqrt (Real.exp L) * (3 * Q * (1 + L) + 2) / Real.log 2 ≤ c * Q ^ 2 * T := by
  have hre : 0 < r + ε := by linarith
  set κ : ℝ := lam / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hκ1 : 0 < 1 - κ := by rw [hκ]; linarith
  have hK : (0:ℝ) < 200 / c := by positivity
  -- the three eventual facts in `x = log Q`
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
  have h4 : ∀ᶠ x : ℝ in atTop, 200 / c * x ^ 2 ≤ Real.exp ((1 - κ) * x) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2 hκ1).def (by positivity : (0:ℝ) < 1 / (200 / c))
    filter_upwards [h, eventually_ge_atTop (0:ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs] at hx
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2), Real.abs_exp] at hx
    calc 200 / c * x ^ 2 ≤ 200 / c * (1 / (200 / c) * Real.exp ((1 - κ) * x)) := by gcongr
      _ = Real.exp ((1 - κ) * x) := by field_simp
  filter_upwards [Real.tendsto_log_atTop.eventually (h1.and (h2.and h4)),
    eventually_gt_atTop (0:ℝ)] with Q hx hQ0
  obtain ⟨hx10, hlogx, hexp2⟩ := hx
  intro T ℒ L
  have hT0 : T = Real.log Q ^ (r + ε) := rfl
  have hℒ0 : ℒ = Real.log (Q * T / (2 * Real.pi)) := rfl
  have hL0 : L = lam * ℒ := rfl
  clear_value T ℒ L
  set x := Real.log Q with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hQexp : Real.exp x = Q := by rw [hxdef]; exact Real.exp_log hQ0
  clear_value x
  have hQ1 : 1 ≤ Q := by rw [← hQexp]; exact Real.one_le_exp_iff.mpr hx0.le
  have hQ0' : 0 ≤ Q := hQ0.le
  have hT : T = Real.exp ((r + ε) * Real.log x) := by
    rw [hT0, Real.rpow_def_of_pos hx0]; congr 1; ring
  have hTpos : 0 < T := by rw [hT]; exact Real.exp_pos _
  have hlogT : Real.log T = (r + ε) * Real.log x := by rw [hT, Real.log_exp]
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have h2pi : 1 ≤ 2 * Real.pi := by linarith
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg h2pi
  have hpi315 : Real.pi < 3.15 := Real.pi_lt_d2
  have hlog2pi' : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hrl : 0 ≤ (r + ε) * Real.log x := mul_nonneg hre.le hlogx0
  have hℒ : ℒ = x + (r + ε) * Real.log x - Real.log (2 * Real.pi) := by
    rw [hℒ0, Real.log_div (by positivity) (by positivity), Real.log_mul hQ0.ne' hTpos.ne',
      hlogT, ← hxdef]
  have hℒnn : 0 ≤ ℒ := by rw [hℒ]; linarith
  have hℒle : ℒ ≤ x + (r + ε) * Real.log x := by rw [hℒ]; linarith
  have hℒ2x : ℒ ≤ 2 * x := by linarith
  have hLnn : 0 ≤ L := by rw [hL0]; positivity
  have hL : L ≤ 4 * x := by rw [hL0]; nlinarith
  -- the four exponentials: `√X ≤ a·b`, `Q = a·u`, `T = b·w`
  set a := Real.exp (κ * x) with ha
  set b := Real.exp (κ * ((r + ε) * Real.log x)) with hb
  set u := Real.exp ((1 - κ) * x) with hu
  set w := Real.exp ((1 - κ) * ((r + ε) * Real.log x)) with hw
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hu0 : 0 < u := Real.exp_pos _
  have hw1 : 1 ≤ w := by
    rw [hw]; exact Real.one_le_exp_iff.mpr (mul_nonneg hκ1.le hrl)
  have hsX_le : Real.sqrt (Real.exp L) ≤ a * b := by
    rw [← Real.exp_half, ha, hb, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : L / 2 = κ * ℒ := by rw [hL0, hκ]; ring
    rw [this]
    nlinarith
  have hQab : Q = a * u := by
    rw [ha, hu, ← Real.exp_add, ← hQexp]; congr 1; ring
  have hTbw : T = b * w := by
    rw [hT, hb, hw, ← Real.exp_add]; congr 1; ring
  have hlog2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  -- numerator: `2L(3Q(1+L)+2) ≤ 136·Q·x²`
  have hA : Q * L ≤ Q * (4 * x) := mul_le_mul_of_nonneg_left hL hQ0'
  have hB : Q * L ^ 2 ≤ Q * (4 * x) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLnn hL 2) hQ0'
  have hC : x ≤ Q * x := le_mul_of_one_le_left hx0.le hQ1
  have hD : Q * x * 10 ≤ Q * x * x := mul_le_mul_of_nonneg_left hx10 (by positivity)
  have hnum : 2 * L * (3 * Q * (1 + L) + 2) ≤ 136 * Q * x ^ 2 := by
    have hQx2 : 0 ≤ Q * x ^ 2 := mul_nonneg hQ0' (sq_nonneg x)
    linarith [hA, hB, hC, hD, hL, hLnn, hQx2]
  have hmul : 2 * L * (3 * Q * (1 + L) + 2) * Real.sqrt (Real.exp L)
      ≤ 136 * Q * x ^ 2 * (a * b) :=
    mul_le_mul hnum hsX_le (Real.sqrt_nonneg _) (by positivity)
  have hm : 0 ≤ Q * x ^ 2 * (a * b) := by positivity
  calc 2 * L * Real.sqrt (Real.exp L) * (3 * Q * (1 + L) + 2) / Real.log 2
      = 2 * L * (3 * Q * (1 + L) + 2) * Real.sqrt (Real.exp L) / Real.log 2 := by ring
    _ ≤ 136 * Q * x ^ 2 * (a * b) / 0.69 :=
        div_le_div₀ (by positivity) hmul (by norm_num) hlog2.le
    _ ≤ 200 * Q * x ^ 2 * (a * b) := by
        rw [div_le_iff₀ (by norm_num)]; linarith [hm]
    _ = c * (Q * (a * b)) * (200 / c * x ^ 2) := by field_simp
    _ ≤ c * (Q * (a * b)) * (u * w) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc 200 / c * x ^ 2 ≤ u := hexp2
          _ ≤ u * w := le_mul_of_one_le_right hu0.le hw1
    _ = c * Q ^ 2 * T := by rw [hTbw, hQab]; ring

end ZetaShell.Design
