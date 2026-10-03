/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaQ.Budget
import ZetaQ.RampLink
import ZetaQ.FrobAssembly

/-! # The zone Lipschitz data for the `q ≤ Q` design profile (certified; sorry-free).

Receipt: `audit/zone_data/ZoneData_REPORT.md`. `Jzone` and `ZoneLipschitzData` are
`ZetaQ.FrobAssembly`'s, not restated here, so `zoneLipschitzData_qle` plugs directly into
`FrobAssembly.zone_compare_eventually_of_data`.

Certifies `FrobAssembly.ZoneLipschitzData Family.qle r ε` (`ZetaQ/FrobAssembly.lean` §C):
for the design of record (`P.prof = designProfileQle`, `P.lam = lamStar`),
`ψ_{v_profile}(α) ≤ ψ₁ + c(1 − α)` on `[0, 1]` with `ψ₁ = 0.05724`, `c = 1.84`, and the margin
`2(C − 1)ψ₁ < sZone` (`C = π⁴/18 ≤ 5.412`, `2·4.412·0.05724 = 0.50509 < 0.5073`).

Route. `v = p²/M` on `|t| ≤ b = λ*/2` (`vProfile_eq`), `M = profMass = ∫_{−b}^{b} p²`, so for
`0 ≤ α ≤ λ*` the autocorrelation is `ψ(α) = (1/M²) ∫_{α−b}^{b} p(t)² p(t−α)² dt`
(`psi_vProfile_eq`). Then
  * `ψ(1) = (R(b) − R(1−b))/M²` with `R` the explicit antiderivative of the expanded degree-24
    polynomial `p(t)² p(t−1)²` (`rQ`, `RQ`, coefficients exact from `gen.py`), and
    `R(b) − R(1−b) ≤ 0.05724·M²` by `norm_num` (`psi1_num`; `ψ(1) = 0.0572395…`);
  * for `0 ≤ α ≤ 1`: `Ψ(α) − Ψ(1) = ∫_{α−b}^{1−b} p²(t)p²(t−α) + ∫_{1−b}^{b} p²(t)[p²(t−α) − p²(t−1)]`;
    the first is `≤ 1·(1−α)` (`0 ≤ p ≤ 1` on the core), the second `≤ K(1−α)·∫_{1−b}^{b} p²` with
    `K = 5.7 ≥ sup_{core}|(p²)′|` (mean value theorem + Bernstein certificates for the degree-5
    polynomial `4P(x)P′(x)`, `x = s²`), so `ψ(α) ≤ ψ(1) + (1 + K·I₂)/M²·(1−α)` and
    `(1 + 5.7·I₂)/M² = 1.8309 ≤ 1.84` (`cQ_num`).
Implied threshold: `1 − a ≤ (sZone − 2(C̄−1)ψ₁)/((C̄−1)c) = 0.00221/8.118 = 2.7·10⁻⁴`
(`FrobAssembly.zone_compare_eventually` uses `θ = (sZone − 2(C−1)ψ₁)/((C−1)c + 1) = 2.4·10⁻⁴`).

Main results: `zoneLipschitzData_qle : ∀ r ε, ZoneLipschitzData Family.qle r ε` (§5), from
`psi_one_le : ψ_{v_profile}(1) ≤ 0.05724` and `psi_le_psi_one_add : ψ(α) ≤ ψ(1) + 1.84(1−α)`.

Dyadic (§6; `designProfileDyadic`, `λ*_dyad`, `C_dyad = 2π⁴/27`): `ψ_dyad(1) = 0.0438875…`, so
`2(C_dyad − 1)ψ_dyad(1) = 0.5456 > sZone = 0.5073` — the data as DEFINED (against `sZone`) is
FALSE for the dyadic family (`dyadic_margin_fails : sZone < 2(C_dyad − 1)ψ(1)` at every dyadic
design point); against `sZoneDyadic = 0.5485` the analogous data holds with margin `0.0028`
(`zoneLipschitzDataDyadic`, `ψ₁ = 0.0439`, `c = 1.83`).

`FrobAssembly.ZoneLipschitzData` is now family-aware (its margin clause is
against `F.sZoneF`: `sZone` for `q ≤ Q`, `sZoneDyadic` for the dyadic family), and
`zoneLipschitzData_dyadic : ∀ r ε, ZoneLipschitzData Family.dyadic r ε` (§6) re-packages the
dyadic certificate so that `FrobAssembly.zone_compare_eventually_of_data` serves both families. -/

noncomputable section

open MeasureTheory Set Real Filter
open ZetaQ.Payoff

namespace ZetaQ
namespace ZoneData

variable {P : ParamsQ}

/-! ## §0. `Jzone` / `ZoneLipschitzData` are `ZetaQ.FrobAssembly`'s (the scratch file copied them verbatim) -/

open ZetaQ.FrobAssembly (Jzone ZoneLipschitzData)

/-! ## §1. The design polynomial `p` as an explicit function; `p(t)²p(t−1)²` expanded -/

/-- `p(t)` for the `q ≤ Q` design, as an explicit function (`designProfileQle_eval`). -/
def pQ (t : ℝ) : ℝ :=
  1 + (-81257 / 125000) * t ^ 2 + (3458583 / 1000000) * t ^ 4 + (-3669851 / 200000) * t ^ 6

theorem eval_designProfileQle (t : ℝ) : designProfileQle.eval t = pQ t := designProfileQle_eval t

theorem pQ_continuous : Continuous pQ := by unfold pQ; fun_prop

/-- `r(t) = p(t)² p(t−1)²` expanded (degree 24; coefficients exact, from `gen.py`). -/
def rQ (t : ℝ) : ℝ :=
  (3303637043281 / 15625000000 : ℝ) * t ^ 0
    + (-17732655900421 / 6250000000 : ℝ) * t ^ 1
    + (65090193375447041257 / 3906250000000000 : ℝ) * t ^ 2
    + (-44034767933890909731 / 781250000000000 : ℝ) * t ^ 3
    + (29647741258954746485727019 / 244140625000000000000 : ℝ) * t ^ 4
    + (-17498508169588808644858129 / 97656250000000000000 : ℝ) * t ^ 5
    + (845819286576192684494568619 / 3906250000000000000000 : ℝ) * t ^ 6
    + (-1047734100807139195991545673 / 3906250000000000000000 : ℝ) * t ^ 7
    + (2207619253398389470715212621 / 15625000000000000000000 : ℝ) * t ^ 8
    + (222837657126277044898453049 / 250000000000000000000 : ℝ) * t ^ 9
    + (-839586729806477642964073386007 / 250000000000000000000000 : ℝ) * t ^ 10
    + (1548050594863326282458047282631 / 250000000000000000000000 : ℝ) * t ^ 11
    + (-7600284263324107159725377424023 / 1000000000000000000000000 : ℝ) * t ^ 12
    + (100484473762193352399249965651 / 12500000000000000000000 : ℝ) * t ^ 13
    + (-855580236744431281537297701729 / 100000000000000000000000 : ℝ) * t ^ 14
    + (935869929573427317736228360183 / 250000000000000000000000 : ℝ) * t ^ 15
    + (16411674123510659887345155929951 / 1000000000000000000000000 : ℝ) * t ^ 16
    + (-313117816586721456606423138849 / 6250000000000000000000 : ℝ) * t ^ 17
    + (1911038981884286745340755772069 / 25000000000000000000000 : ℝ) * t ^ 18
    + (-151312790260328001066381562007 / 2000000000000000000000 : ℝ) * t ^ 19
    + (2056465738034665332215361697999 / 40000000000000000000000 : ℝ) * t ^ 20
    + (-11999914532897401348508754803 / 500000000000000000000 : ℝ) * t ^ 21
    + (29586118513500227571640818699 / 4000000000000000000000 : ℝ) * t ^ 22
    + (-544145424629225199604693203 / 400000000000000000000 : ℝ) * t ^ 23
    + (181381808209741733201564401 / 1600000000000000000000 : ℝ) * t ^ 24

theorem pQ_sq_mul_pQ_sq_eq (t : ℝ) : pQ t ^ 2 * pQ (t - 1) ^ 2 = rQ t := by
  unfold pQ rQ; ring

/-- the antiderivative of `rQ`. -/
def RQ (t : ℝ) : ℝ :=
  (3303637043281 / 15625000000 : ℝ) * t ^ 1 / 1
    + (-17732655900421 / 6250000000 : ℝ) * t ^ 2 / 2
    + (65090193375447041257 / 3906250000000000 : ℝ) * t ^ 3 / 3
    + (-44034767933890909731 / 781250000000000 : ℝ) * t ^ 4 / 4
    + (29647741258954746485727019 / 244140625000000000000 : ℝ) * t ^ 5 / 5
    + (-17498508169588808644858129 / 97656250000000000000 : ℝ) * t ^ 6 / 6
    + (845819286576192684494568619 / 3906250000000000000000 : ℝ) * t ^ 7 / 7
    + (-1047734100807139195991545673 / 3906250000000000000000 : ℝ) * t ^ 8 / 8
    + (2207619253398389470715212621 / 15625000000000000000000 : ℝ) * t ^ 9 / 9
    + (222837657126277044898453049 / 250000000000000000000 : ℝ) * t ^ 10 / 10
    + (-839586729806477642964073386007 / 250000000000000000000000 : ℝ) * t ^ 11 / 11
    + (1548050594863326282458047282631 / 250000000000000000000000 : ℝ) * t ^ 12 / 12
    + (-7600284263324107159725377424023 / 1000000000000000000000000 : ℝ) * t ^ 13 / 13
    + (100484473762193352399249965651 / 12500000000000000000000 : ℝ) * t ^ 14 / 14
    + (-855580236744431281537297701729 / 100000000000000000000000 : ℝ) * t ^ 15 / 15
    + (935869929573427317736228360183 / 250000000000000000000000 : ℝ) * t ^ 16 / 16
    + (16411674123510659887345155929951 / 1000000000000000000000000 : ℝ) * t ^ 17 / 17
    + (-313117816586721456606423138849 / 6250000000000000000000 : ℝ) * t ^ 18 / 18
    + (1911038981884286745340755772069 / 25000000000000000000000 : ℝ) * t ^ 19 / 19
    + (-151312790260328001066381562007 / 2000000000000000000000 : ℝ) * t ^ 20 / 20
    + (2056465738034665332215361697999 / 40000000000000000000000 : ℝ) * t ^ 21 / 21
    + (-11999914532897401348508754803 / 500000000000000000000 : ℝ) * t ^ 22 / 22
    + (29586118513500227571640818699 / 4000000000000000000000 : ℝ) * t ^ 23 / 23
    + (-544145424629225199604693203 / 400000000000000000000 : ℝ) * t ^ 24 / 24
    + (181381808209741733201564401 / 1600000000000000000000 : ℝ) * t ^ 25 / 25

theorem hasDerivAt_RQ (t : ℝ) : HasDerivAt RQ (rQ t) t := by
  unfold RQ rQ
  have h0 := ((hasDerivAt_pow 1 t).const_mul (3303637043281 / 15625000000 : ℝ)).div_const 1
  have h1 := ((hasDerivAt_pow 2 t).const_mul (-17732655900421 / 6250000000 : ℝ)).div_const 2
  have h2 := ((hasDerivAt_pow 3 t).const_mul (65090193375447041257 / 3906250000000000 : ℝ)).div_const 3
  have h3 := ((hasDerivAt_pow 4 t).const_mul (-44034767933890909731 / 781250000000000 : ℝ)).div_const 4
  have h4 := ((hasDerivAt_pow 5 t).const_mul (29647741258954746485727019 / 244140625000000000000 : ℝ)).div_const 5
  have h5 := ((hasDerivAt_pow 6 t).const_mul (-17498508169588808644858129 / 97656250000000000000 : ℝ)).div_const 6
  have h6 := ((hasDerivAt_pow 7 t).const_mul (845819286576192684494568619 / 3906250000000000000000 : ℝ)).div_const 7
  have h7 := ((hasDerivAt_pow 8 t).const_mul (-1047734100807139195991545673 / 3906250000000000000000 : ℝ)).div_const 8
  have h8 := ((hasDerivAt_pow 9 t).const_mul (2207619253398389470715212621 / 15625000000000000000000 : ℝ)).div_const 9
  have h9 := ((hasDerivAt_pow 10 t).const_mul (222837657126277044898453049 / 250000000000000000000 : ℝ)).div_const 10
  have h10 := ((hasDerivAt_pow 11 t).const_mul (-839586729806477642964073386007 / 250000000000000000000000 : ℝ)).div_const 11
  have h11 := ((hasDerivAt_pow 12 t).const_mul (1548050594863326282458047282631 / 250000000000000000000000 : ℝ)).div_const 12
  have h12 := ((hasDerivAt_pow 13 t).const_mul (-7600284263324107159725377424023 / 1000000000000000000000000 : ℝ)).div_const 13
  have h13 := ((hasDerivAt_pow 14 t).const_mul (100484473762193352399249965651 / 12500000000000000000000 : ℝ)).div_const 14
  have h14 := ((hasDerivAt_pow 15 t).const_mul (-855580236744431281537297701729 / 100000000000000000000000 : ℝ)).div_const 15
  have h15 := ((hasDerivAt_pow 16 t).const_mul (935869929573427317736228360183 / 250000000000000000000000 : ℝ)).div_const 16
  have h16 := ((hasDerivAt_pow 17 t).const_mul (16411674123510659887345155929951 / 1000000000000000000000000 : ℝ)).div_const 17
  have h17 := ((hasDerivAt_pow 18 t).const_mul (-313117816586721456606423138849 / 6250000000000000000000 : ℝ)).div_const 18
  have h18 := ((hasDerivAt_pow 19 t).const_mul (1911038981884286745340755772069 / 25000000000000000000000 : ℝ)).div_const 19
  have h19 := ((hasDerivAt_pow 20 t).const_mul (-151312790260328001066381562007 / 2000000000000000000000 : ℝ)).div_const 20
  have h20 := ((hasDerivAt_pow 21 t).const_mul (2056465738034665332215361697999 / 40000000000000000000000 : ℝ)).div_const 21
  have h21 := ((hasDerivAt_pow 22 t).const_mul (-11999914532897401348508754803 / 500000000000000000000 : ℝ)).div_const 22
  have h22 := ((hasDerivAt_pow 23 t).const_mul (29586118513500227571640818699 / 4000000000000000000000 : ℝ)).div_const 23
  have h23 := ((hasDerivAt_pow 24 t).const_mul (-544145424629225199604693203 / 400000000000000000000 : ℝ)).div_const 24
  have h24 := ((hasDerivAt_pow 25 t).const_mul (181381808209741733201564401 / 1600000000000000000000 : ℝ)).div_const 25
  have h := ((((((((((((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15).add h16).add h17).add h18).add h19).add h20).add h21).add h22).add h23).add h24)
  exact h.congr_deriv (by push_cast; ring)

theorem rQ_continuous : Continuous rQ := by unfold rQ; fun_prop

/-- `∫_{1−b}^{b} p(t)²p(t−1)² = R(b) − R(1−b) ≤ 0.05724·M²`, `M = ∫_{−b}^{b} p²` (exact rationals;
`ψ(1) = 0.0572395…`). -/
theorem psi1_num :
    RQ (lamStar / 2) - RQ (1 - lamStar / 2)
      ≤ (5724 / 100000) * (sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (lamStar / 2)
          - sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (-(lamStar / 2))) ^ 2 := by
  unfold RQ sqPrim lamStar
  norm_num

/-- `1 + 5.7·∫_{1−b}^{b} p² ≤ 1.84·M²` (`(1 + 5.7·I₂)/M² = 1.8309`). -/
theorem cQ_num :
    1 + (57 / 10) * (sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (lamStar / 2)
          - sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (1 - lamStar / 2))
      ≤ (184 / 100) * (sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (lamStar / 2)
          - sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (-(lamStar / 2))) ^ 2 := by
  unfold sqPrim lamStar
  norm_num

/-! ## §2. The derivative of `p²` and its bound on the core -/

/-- `p′`. -/
def pQ' (t : ℝ) : ℝ :=
  2 * (-81257 / 125000) * t + 4 * (3458583 / 1000000) * t ^ 3 + 6 * (-3669851 / 200000) * t ^ 5

theorem hasDerivAt_pQ (t : ℝ) : HasDerivAt pQ (pQ' t) t := by
  unfold pQ pQ'
  have h2 := (hasDerivAt_pow 2 t).const_mul (-81257 / 125000 : ℝ)
  have h4 := (hasDerivAt_pow 4 t).const_mul (3458583 / 1000000 : ℝ)
  have h6 := (hasDerivAt_pow 6 t).const_mul (-3669851 / 200000 : ℝ)
  have h := ((h2.const_add 1).add h4).add h6
  exact h.congr_deriv (by push_cast; ring)

theorem hasDerivAt_pQ_sq (t : ℝ) : HasDerivAt (fun s => pQ s ^ 2) (2 * pQ t * pQ' t) t := by
  have h := (hasDerivAt_pQ t).fun_pow 2
  exact h.congr_deriv (by push_cast; ring)

/-- `|t| ≤ λ*/2` gives `t² ≤ 0.3911` (as in `profileQ_qle`). -/
theorem sq_le_of_core {t : ℝ} (ht : |t| ≤ lamStar / 2) : t ^ 2 ≤ 3911 / 10000 := by
  have h1 : |t| ^ 2 ≤ (lamStar / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at h1
  unfold lamStar at h1
  norm_num at h1
  linarith

/-- `0 ≤ p ≤ 1` on the core (from `profileQ_qle`). -/
theorem pQ_nonneg_le_one {t : ℝ} (ht : |t| ≤ lamStar / 2) : 0 ≤ pQ t ∧ pQ t ≤ 1 := by
  have h1 := profileQ_qle.bulk t ht
  have h2 := profileQ_qle.le_one t ht
  rw [eval_designProfileQle] at h1 h2
  exact ⟨by linarith, h2⟩

/-- `Qd(x) = 4P(x)P′(x)`, `P(x) = 1 + d₂x + d₄x² + d₆x³`, so that `(p²)′(s) = s·Qd(s²)`. -/
def Qd (x : ℝ) : ℝ :=
  4 * (1 + (-81257 / 125000) * x + (3458583 / 1000000) * x ^ 2 + (-3669851 / 200000) * x ^ 3)
    * ((-81257 / 125000) + 2 * (3458583 / 1000000) * x + 3 * (-3669851 / 200000) * x ^ 2)

/-- `−9.1 ≤ Qd ≤ 0` on `[0, 0.3911]` (`sup|Qd| = 8.888` at `x = 0.316`; Bernstein certificates of
`9.1 + Qd` on `[0, .1], [.1, .2], [.2, .3], [.3, .3911]` — all coefficients `≥ 0.06`, `bern.py`). -/
theorem Qd_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3911 / 10000) :
    -91 / 10 ≤ Qd x ∧ Qd x ≤ 0 := by
  unfold Qd
  constructor
  · rcases le_or_gt x (1 / 10) with h1 | h1
    · have a1 : 0 ≤ 1 / 10 - x := by linarith
      nlinarith [mul_nonneg (pow_nonneg hx0 0) (pow_nonneg a1 5),
        mul_nonneg (pow_nonneg hx0 1) (pow_nonneg a1 4),
        mul_nonneg (pow_nonneg hx0 2) (pow_nonneg a1 3),
        mul_nonneg (pow_nonneg hx0 3) (pow_nonneg a1 2),
        mul_nonneg (pow_nonneg hx0 4) (pow_nonneg a1 1),
        mul_nonneg (pow_nonneg hx0 5) (pow_nonneg a1 0)]
    rcases le_or_gt x (2 / 10) with h2 | h2
    · have a0 : 0 ≤ x - 1 / 10 := by linarith
      have a1 : 0 ≤ 2 / 10 - x := by linarith
      nlinarith [mul_nonneg (pow_nonneg a0 0) (pow_nonneg a1 5),
        mul_nonneg (pow_nonneg a0 1) (pow_nonneg a1 4),
        mul_nonneg (pow_nonneg a0 2) (pow_nonneg a1 3),
        mul_nonneg (pow_nonneg a0 3) (pow_nonneg a1 2),
        mul_nonneg (pow_nonneg a0 4) (pow_nonneg a1 1),
        mul_nonneg (pow_nonneg a0 5) (pow_nonneg a1 0)]
    rcases le_or_gt x (3 / 10) with h3 | h3
    · have a0 : 0 ≤ x - 2 / 10 := by linarith
      have a1 : 0 ≤ 3 / 10 - x := by linarith
      nlinarith [mul_nonneg (pow_nonneg a0 0) (pow_nonneg a1 5),
        mul_nonneg (pow_nonneg a0 1) (pow_nonneg a1 4),
        mul_nonneg (pow_nonneg a0 2) (pow_nonneg a1 3),
        mul_nonneg (pow_nonneg a0 3) (pow_nonneg a1 2),
        mul_nonneg (pow_nonneg a0 4) (pow_nonneg a1 1),
        mul_nonneg (pow_nonneg a0 5) (pow_nonneg a1 0)]
    · have a0 : 0 ≤ x - 3 / 10 := by linarith
      have a1 : 0 ≤ 3911 / 10000 - x := by linarith
      nlinarith [mul_nonneg (pow_nonneg a0 0) (pow_nonneg a1 5),
        mul_nonneg (pow_nonneg a0 1) (pow_nonneg a1 4),
        mul_nonneg (pow_nonneg a0 2) (pow_nonneg a1 3),
        mul_nonneg (pow_nonneg a0 3) (pow_nonneg a1 2),
        mul_nonneg (pow_nonneg a0 4) (pow_nonneg a1 1),
        mul_nonneg (pow_nonneg a0 5) (pow_nonneg a1 0)]
  · -- `P ≥ P(0.3911) = 0.177 > 0` and `P′ < 0` (negative discriminant)
    have hr : (0 : ℝ) ≤ 81257 / 125000 - 3458583 / 1000000 * (x + 3911 / 10000)
        + 3669851 / 200000 * (x ^ 2 + x * (3911 / 10000) + (3911 / 10000) ^ 2) := by
      nlinarith [sq_nonneg x]
    have hP : 0 ≤ 1 + (-81257 / 125000) * x + (3458583 / 1000000) * x ^ 2
        + (-3669851 / 200000) * x ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hx) hr]
    have hP' : (-81257 / 125000) + 2 * (3458583 / 1000000) * x + 3 * (-3669851 / 200000) * x ^ 2
        ≤ 0 := by
      nlinarith [sq_nonneg (x - 628 / 10000)]
    nlinarith [mul_nonneg hP (neg_nonneg.2 hP')]

/-- `|(p²)′| ≤ 5.7` on the core (`(p²)′(s) = s·Qd(s²)`, `|s| ≤ 0.6254`, `|Qd| ≤ 9.1`). -/
theorem abs_deriv_pQ_sq_le {s : ℝ} (hs : |s| ≤ lamStar / 2) : |2 * pQ s * pQ' s| ≤ 57 / 10 := by
  have hx : s ^ 2 ≤ 3911 / 10000 := sq_le_of_core hs
  have hx0 : 0 ≤ s ^ 2 := sq_nonneg s
  obtain ⟨hlo, hhi⟩ := Qd_bounds hx0 hx
  have e : 2 * pQ s * pQ' s = s * Qd (s ^ 2) := by unfold pQ pQ' Qd; ring
  rw [e, abs_mul]
  have hQ : |Qd (s ^ 2)| ≤ 91 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |s| * |Qd (s ^ 2)| ≤ (lamStar / 2) * (91 / 10) :=
        mul_le_mul hs hQ (abs_nonneg _) (by unfold lamStar; norm_num)
    _ ≤ 57 / 10 := by unfold lamStar; norm_num

/-- **`p²` is `5.7`-Lipschitz on the core** (mean value theorem). -/
theorem pQ_sq_lip {x y : ℝ} (hx : |x| ≤ lamStar / 2) (hy : |y| ≤ lamStar / 2) :
    |pQ y ^ 2 - pQ x ^ 2| ≤ 57 / 10 * |y - x| := by
  have h := (convex_Icc (-(lamStar / 2)) (lamStar / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => pQ s ^ 2) (f' := fun s => 2 * pQ s * pQ' s) (C := 57 / 10)
    (fun s _ => (hasDerivAt_pQ_sq s).hasDerivWithinAt)
    (fun s hs => by rw [Real.norm_eq_abs]; exact abs_deriv_pQ_sq_le (abs_le.mpr hs))
    (abs_le.mp hx) (abs_le.mp hy)
  simpa only [Real.norm_eq_abs] using h

/-! ## §3. The autocorrelation of `vProfile` as an interval integral -/

theorem vProfile_mul_eq (P : ParamsQ) {α : ℝ} (hα : 0 ≤ α) (t : ℝ) :
    vProfile P t * vProfile P (t - α)
      = (Icc (α - P.lam / 2) (P.lam / 2)).indicator
          (fun t => (P.prof.eval t) ^ 2 * (P.prof.eval (t - α)) ^ 2 / (profMass P) ^ 2) t := by
  rw [vProfile_eq, vProfile_eq]
  by_cases h : t ∈ Icc (α - P.lam / 2) (P.lam / 2)
  · rw [indicator_of_mem h]
    obtain ⟨h1, h2⟩ := h
    rw [if_pos (abs_le.mpr ⟨by linarith, h2⟩), if_pos (abs_le.mpr ⟨by linarith, by linarith⟩)]
    ring
  · rw [indicator_of_notMem h]
    simp only [mem_Icc, not_and_or, not_le] at h
    split_ifs with h1 h2
    · exfalso
      rw [abs_le] at h1 h2
      rcases h with h | h <;> linarith [h1.1, h1.2, h2.1, h2.2]
    all_goals simp

/-- `ψ_{v_profile}(α) = (1/M²)∫_{α−λ/2}^{λ/2} p(t)²p(t−α)² dt` for `0 ≤ α ≤ λ`. -/
theorem psi_vProfile_eq (P : ParamsQ) {α : ℝ} (h0 : 0 ≤ α) (hα : α ≤ P.lam) :
    psi (vProfile P) α
      = (∫ t in (α - P.lam / 2)..(P.lam / 2), (P.prof.eval t) ^ 2 * (P.prof.eval (t - α)) ^ 2)
          / (profMass P) ^ 2 := by
  unfold psi
  simp_rw [vProfile_mul_eq P h0]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_div]

theorem one_le_lamStar : (1 : ℝ) ≤ lamStar := by unfold lamStar; norm_num

/-- the same for the design of record, with `p = pQ`, `b = λ*/2`. -/
theorem psi_vProfile_eq_pQ (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar)
    {α : ℝ} (h0 : 0 ≤ α) (hα : α ≤ 1) :
    psi (vProfile P) α
      = (∫ t in (α - lamStar / 2)..(lamStar / 2), pQ t ^ 2 * pQ (t - α) ^ 2)
          / (profMass P) ^ 2 := by
  rw [psi_vProfile_eq P h0 (by rw [hlam]; linarith [one_le_lamStar]), hlam, hprof]
  simp_rw [eval_designProfileQle]

/-- `profMass = sqPrim(b) − sqPrim(−b)` at the design of record. -/
theorem profMass_eq_qle (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar) :
    profMass P
      = sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (lamStar / 2)
        - sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (-(lamStar / 2)) := by
  unfold profMass
  rw [hlam, hprof]
  simp_rw [designProfileQle_eval]
  exact integral_sq_poly _ _ _ _ _

/-! ## §4. `ψ(1) ≤ 0.05724` and the Lipschitz bound -/

/-- **`ψ_{v_profile}(1) ≤ 0.05724`** (`= 0.0572395…`). -/
theorem psi_one_le (hP : P.Valid) (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar) :
    psi (vProfile P) 1 ≤ 5724 / 100000 := by
  rw [psi_vProfile_eq_pQ hprof hlam zero_le_one le_rfl]
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  rw [div_le_iff₀ hM2, profMass_eq_qle hprof hlam]
  have hval : ∫ t in (1 - lamStar / 2)..(lamStar / 2), pQ t ^ 2 * pQ (t - 1) ^ 2
      = RQ (lamStar / 2) - RQ (1 - lamStar / 2) := by
    simp_rw [pQ_sq_mul_pQ_sq_eq]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_RQ x)
      (rQ_continuous.intervalIntegrable _ _)
  rw [hval]
  exact psi1_num

/-- **The Lipschitz bound** `ψ(α) ≤ ψ(1) + 1.84·(1 − α)` on `[0, 1]`. -/
theorem psi_le_psi_one_add (hP : P.Valid) (hprof : P.prof = designProfileQle)
    (hlam : P.lam = lamStar) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    psi (vProfile P) α ≤ psi (vProfile P) 1 + (184 / 100) * (1 - α) := by
  have hb1 : 1 - lamStar / 2 ≤ lamStar / 2 := by unfold lamStar; norm_num
  have hbh : 1 / 2 < lamStar / 2 := by unfold lamStar; norm_num
  have hbl : lamStar / 2 ≤ 1 := by unfold lamStar; norm_num
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  have hcont : ∀ β : ℝ, Continuous fun t => pQ t ^ 2 * pQ (t - β) ^ 2 := by
    intro β
    have := pQ_continuous
    fun_prop
  have hIα : ∀ a c : ℝ, IntervalIntegrable (fun t => pQ t ^ 2 * pQ (t - α) ^ 2) volume a c :=
    fun a c => (hcont α).intervalIntegrable a c
  have hI1 : ∀ a c : ℝ, IntervalIntegrable (fun t => pQ t ^ 2 * pQ (t - 1) ^ 2) volume a c :=
    fun a c => (hcont 1).intervalIntegrable a c
  rw [psi_vProfile_eq_pQ hprof hlam h0 h1, psi_vProfile_eq_pQ hprof hlam zero_le_one le_rfl]
  -- the split at `1 − b`
  have hsplit : ∫ t in (α - lamStar / 2)..(lamStar / 2), pQ t ^ 2 * pQ (t - α) ^ 2
      = (∫ t in (α - lamStar / 2)..(1 - lamStar / 2), pQ t ^ 2 * pQ (t - α) ^ 2)
        + ∫ t in (1 - lamStar / 2)..(lamStar / 2), pQ t ^ 2 * pQ (t - α) ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hIα _ _) (hIα _ _)).symm
  -- term 1: `≤ 1·(1 − α)`
  have hT1 : ∫ t in (α - lamStar / 2)..(1 - lamStar / 2), pQ t ^ 2 * pQ (t - α) ^ 2
      ≤ 1 * (1 - α) := by
    have hbd : ∀ x ∈ Set.uIoc (α - lamStar / 2) (1 - lamStar / 2), ‖pQ x ^ 2 * pQ (x - α) ^ 2‖ ≤ 1 := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hA := pQ_nonneg_le_one (t := x) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hB := pQ_nonneg_le_one (t := x - α) (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : pQ x ^ 2 * pQ (x - α) ^ 2 ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ hA.1 hA.2) (pow_le_one₀ hB.1 hB.2) (by positivity) zero_le_one
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, show (1 - lamStar / 2) - (α - lamStar / 2) = 1 - α by ring,
      abs_of_nonneg (show (0:ℝ) ≤ 1 - α by linarith)] at this
    exact (le_abs_self _).trans this
  -- term 2: `≤ 5.7(1 − α)·∫_{1−b}^{b} p²`
  have hI2 : ∫ t in (1 - lamStar / 2)..(lamStar / 2), pQ t ^ 2
      = sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (lamStar / 2)
        - sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (1 - lamStar / 2) := by
    unfold pQ
    exact integral_sq_poly _ _ _ _ _
  have hT2 : (∫ t in (1 - lamStar / 2)..(lamStar / 2), pQ t ^ 2 * pQ (t - α) ^ 2)
        - ∫ t in (1 - lamStar / 2)..(lamStar / 2), pQ t ^ 2 * pQ (t - 1) ^ 2
      ≤ (57 / 10 * (1 - α))
          * (sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (lamStar / 2)
            - sqPrim (-81257 / 125000) (3458583 / 1000000) (-3669851 / 200000) (1 - lamStar / 2)) := by
    rw [← intervalIntegral.integral_sub (hIα _ _) (hI1 _ _), ← hI2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hb1 ((hIα _ _).sub (hI1 _ _))
      (((pQ_continuous.pow 2).const_mul _).intervalIntegrable _ _)
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hlip := pQ_sq_lip (x := x - 1) (y := x - α)
      (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [show (x - α) - (x - 1) = 1 - α by ring, abs_of_nonneg (show (0:ℝ) ≤ 1 - α by linarith)] at hlip
    have hd : pQ (x - α) ^ 2 - pQ (x - 1) ^ 2 ≤ 57 / 10 * (1 - α) := (le_abs_self _).trans hlip
    have hsq : 0 ≤ pQ x ^ 2 := sq_nonneg _
    calc pQ x ^ 2 * pQ (x - α) ^ 2 - pQ x ^ 2 * pQ (x - 1) ^ 2
        = pQ x ^ 2 * (pQ (x - α) ^ 2 - pQ (x - 1) ^ 2) := by ring
      _ ≤ pQ x ^ 2 * (57 / 10 * (1 - α)) := mul_le_mul_of_nonneg_left hd hsq
      _ = 57 / 10 * (1 - α) * pQ x ^ 2 := by ring
  -- assemble: `Ψ(α) ≤ Ψ(1) + (1−α)(1 + 5.7·I₂) ≤ Ψ(1) + (1−α)·1.84·M²`
  have hD := cQ_num
  rw [← profMass_eq_qle hprof hlam] at hD
  have hD' := mul_le_mul_of_nonneg_left hD (sub_nonneg.2 h1)
  rw [hsplit, div_le_iff₀ hM2, add_mul, div_mul_cancel₀ _ hM2.ne']
  nlinarith [hT1, hT2, hD']

/-! ## §5. The data -/

theorem Cfam_le_5412 : Cfam ≤ 5412 / 1000 := by
  have h := C_qQ_le
  unfold Cfam
  push_cast at h
  linarith

/-- **`ZoneLipschitzData Family.qle r ε`, certified**: `ψ₁ = 0.05724`, `c = 1.84`,
`2(C−1)ψ₁ ≤ 2·4.412·0.05724 = 0.50509 < 0.5073 = sZone` (margin `≥ 0.0022`). -/
theorem zoneLipschitzData_qle (r ε : ℝ) : ZoneLipschitzData Family.qle r ε := by
  refine ⟨5724 / 100000, 184 / 100, by norm_num, ?_, ?_⟩
  · have := Cfam_le_5412
    simp only [Family.Cconst, Family.sZoneF]
    unfold sZone
    linarith
  · intro Qn P hdes α h0 h1
    obtain ⟨hP, -, -, hlam, -, -, -, -, -, -, -, hprof⟩ := hdes
    have hlam' : P.lam = lamStar := hlam
    have hprof' : P.prof = designProfileQle := hprof
    have h := psi_le_psi_one_add hP hprof' hlam' h0 h1
    have h' := psi_one_le hP hprof' hlam'
    linarith


/-! ## §6. The dyadic family. **Against `sZone` the data is FALSE**: `ψ_dyad(1) = 0.0438875…` and
`2(C_dyad − 1)ψ_dyad(1) ≥ 2·6.2154·0.04388 = 0.5454 > 0.5073` (`dyadic_margin_fails`). Against
`sZoneDyadic = 0.5485` the analogous data holds: `ψ₁ = 0.0439`, `c = 1.83`, margin
`0.5485 − 2·6.21549·0.0439 = 0.0028` (`zoneLipschitzDataDyadic`). Same route as §§1–5 with
`p_d = designProfileDyadic`, `b_d = λ*_dyad/2 = 0.5966`, core `t² ≤ 0.356`, `|Qd_d| ≤ 11.1` on
`[0, 0.356]` (Bernstein, 4 pieces, `gen_dyad.py`), `|(p_d²)′| ≤ 0.5966·11.1 ≤ 6.7`,
`I₂ = ∫_{1−b}^{b} p_d² = 0.09940`, `M_d = 0.95660`, `(1 + 6.7·I₂)/M_d² = 1.8205 ≤ 1.83`. -/

/-- `p_d(t)` for the dyadic design (`designProfileDyadic_eval`). -/
def pD (t : ℝ) : ℝ :=
  1 + (-1014099 / 1000000) * t ^ 2 + (834917 / 100000) * t ^ 4 + (-16525667 / 500000) * t ^ 6

theorem eval_designProfileDyadic (t : ℝ) : designProfileDyadic.eval t = pD t :=
  designProfileDyadic_eval t

theorem pD_continuous : Continuous pD := by unfold pD; fun_prop

/-- `r_d(t) = p_d(t)² p_d(t−1)²` expanded (degree 24; exact, `gen_dyad.py`). -/
def rD (t : ℝ) : ℝ :=
  (610893656685169 / 1000000000000 : ℝ) * t ^ 0
    + (-2063060565423143 / 250000000000 : ℝ) * t ^ 1
    + (24355380359397875802269 / 500000000000000000 : ℝ) * t ^ 2
    + (-20428535130406320606843 / 125000000000000000 : ℝ) * t ^ 3
    + (342699209266770861859501809369 / 1000000000000000000000000 : ℝ) * t ^ 4
    + (-128531877911451839367284620543 / 250000000000000000000000 : ℝ) * t ^ 5
    + (426682191949418047417878803579 / 500000000000000000000000 : ℝ) * t ^ 6
    + (-455341222270660516344863755549 / 250000000000000000000000 : ℝ) * t ^ 7
    + (2311022612744083193455913005289 / 1000000000000000000000000 : ℝ) * t ^ 8
    + (277687488181217017646857626499 / 125000000000000000000000 : ℝ) * t ^ 9
    + (-454587452045452021489809060687 / 31250000000000000000000 : ℝ) * t ^ 10
    + (84643157350849676947966316117 / 3125000000000000000000 : ℝ) * t ^ 11
    + (-4145479631200945373388310676589 / 125000000000000000000000 : ℝ) * t ^ 12
    + (655602728947634999084333449743 / 12500000000000000000000 : ℝ) * t ^ 13
    + (-6462675566916583116722191619981 / 62500000000000000000000 : ℝ) * t ^ 14
    + (114978944503079211442360840809 / 976562500000000000000 : ℝ) * t ^ 15
    + (5333393777559791837133716457197 / 125000000000000000000000 : ℝ) * t ^ 16
    + (-12202358550072133097339262492957 / 31250000000000000000000 : ℝ) * t ^ 17
    + (5507824980409830323849811828059 / 7812500000000000000000 : ℝ) * t ^ 18
    + (-2914676737382839613063008447817 / 3906250000000000000000 : ℝ) * t ^ 19
    + (32773395797778319715626203042909 / 62500000000000000000000 : ℝ) * t ^ 20
    + (-3115827249771098775523443459 / 12500000000000000000 : ℝ) * t ^ 21
    + (2423536313456318048783566435883 / 31250000000000000000000 : ℝ) * t ^ 22
    + (-223747011742194682977991566963 / 15625000000000000000000 : ℝ) * t ^ 23
    + (74582337247398227659330522321 / 62500000000000000000000 : ℝ) * t ^ 24

theorem pD_sq_mul_pD_sq_eq (t : ℝ) : pD t ^ 2 * pD (t - 1) ^ 2 = rD t := by
  unfold pD rD; ring

/-- the antiderivative of `rD`. -/
def RD (t : ℝ) : ℝ :=
  (610893656685169 / 1000000000000 : ℝ) * t ^ 1 / 1
    + (-2063060565423143 / 250000000000 : ℝ) * t ^ 2 / 2
    + (24355380359397875802269 / 500000000000000000 : ℝ) * t ^ 3 / 3
    + (-20428535130406320606843 / 125000000000000000 : ℝ) * t ^ 4 / 4
    + (342699209266770861859501809369 / 1000000000000000000000000 : ℝ) * t ^ 5 / 5
    + (-128531877911451839367284620543 / 250000000000000000000000 : ℝ) * t ^ 6 / 6
    + (426682191949418047417878803579 / 500000000000000000000000 : ℝ) * t ^ 7 / 7
    + (-455341222270660516344863755549 / 250000000000000000000000 : ℝ) * t ^ 8 / 8
    + (2311022612744083193455913005289 / 1000000000000000000000000 : ℝ) * t ^ 9 / 9
    + (277687488181217017646857626499 / 125000000000000000000000 : ℝ) * t ^ 10 / 10
    + (-454587452045452021489809060687 / 31250000000000000000000 : ℝ) * t ^ 11 / 11
    + (84643157350849676947966316117 / 3125000000000000000000 : ℝ) * t ^ 12 / 12
    + (-4145479631200945373388310676589 / 125000000000000000000000 : ℝ) * t ^ 13 / 13
    + (655602728947634999084333449743 / 12500000000000000000000 : ℝ) * t ^ 14 / 14
    + (-6462675566916583116722191619981 / 62500000000000000000000 : ℝ) * t ^ 15 / 15
    + (114978944503079211442360840809 / 976562500000000000000 : ℝ) * t ^ 16 / 16
    + (5333393777559791837133716457197 / 125000000000000000000000 : ℝ) * t ^ 17 / 17
    + (-12202358550072133097339262492957 / 31250000000000000000000 : ℝ) * t ^ 18 / 18
    + (5507824980409830323849811828059 / 7812500000000000000000 : ℝ) * t ^ 19 / 19
    + (-2914676737382839613063008447817 / 3906250000000000000000 : ℝ) * t ^ 20 / 20
    + (32773395797778319715626203042909 / 62500000000000000000000 : ℝ) * t ^ 21 / 21
    + (-3115827249771098775523443459 / 12500000000000000000 : ℝ) * t ^ 22 / 22
    + (2423536313456318048783566435883 / 31250000000000000000000 : ℝ) * t ^ 23 / 23
    + (-223747011742194682977991566963 / 15625000000000000000000 : ℝ) * t ^ 24 / 24
    + (74582337247398227659330522321 / 62500000000000000000000 : ℝ) * t ^ 25 / 25

theorem hasDerivAt_RD (t : ℝ) : HasDerivAt RD (rD t) t := by
  unfold RD rD
  have h0 := ((hasDerivAt_pow 1 t).const_mul (610893656685169 / 1000000000000 : ℝ)).div_const 1
  have h1 := ((hasDerivAt_pow 2 t).const_mul (-2063060565423143 / 250000000000 : ℝ)).div_const 2
  have h2 := ((hasDerivAt_pow 3 t).const_mul (24355380359397875802269 / 500000000000000000 : ℝ)).div_const 3
  have h3 := ((hasDerivAt_pow 4 t).const_mul (-20428535130406320606843 / 125000000000000000 : ℝ)).div_const 4
  have h4 := ((hasDerivAt_pow 5 t).const_mul (342699209266770861859501809369 / 1000000000000000000000000 : ℝ)).div_const 5
  have h5 := ((hasDerivAt_pow 6 t).const_mul (-128531877911451839367284620543 / 250000000000000000000000 : ℝ)).div_const 6
  have h6 := ((hasDerivAt_pow 7 t).const_mul (426682191949418047417878803579 / 500000000000000000000000 : ℝ)).div_const 7
  have h7 := ((hasDerivAt_pow 8 t).const_mul (-455341222270660516344863755549 / 250000000000000000000000 : ℝ)).div_const 8
  have h8 := ((hasDerivAt_pow 9 t).const_mul (2311022612744083193455913005289 / 1000000000000000000000000 : ℝ)).div_const 9
  have h9 := ((hasDerivAt_pow 10 t).const_mul (277687488181217017646857626499 / 125000000000000000000000 : ℝ)).div_const 10
  have h10 := ((hasDerivAt_pow 11 t).const_mul (-454587452045452021489809060687 / 31250000000000000000000 : ℝ)).div_const 11
  have h11 := ((hasDerivAt_pow 12 t).const_mul (84643157350849676947966316117 / 3125000000000000000000 : ℝ)).div_const 12
  have h12 := ((hasDerivAt_pow 13 t).const_mul (-4145479631200945373388310676589 / 125000000000000000000000 : ℝ)).div_const 13
  have h13 := ((hasDerivAt_pow 14 t).const_mul (655602728947634999084333449743 / 12500000000000000000000 : ℝ)).div_const 14
  have h14 := ((hasDerivAt_pow 15 t).const_mul (-6462675566916583116722191619981 / 62500000000000000000000 : ℝ)).div_const 15
  have h15 := ((hasDerivAt_pow 16 t).const_mul (114978944503079211442360840809 / 976562500000000000000 : ℝ)).div_const 16
  have h16 := ((hasDerivAt_pow 17 t).const_mul (5333393777559791837133716457197 / 125000000000000000000000 : ℝ)).div_const 17
  have h17 := ((hasDerivAt_pow 18 t).const_mul (-12202358550072133097339262492957 / 31250000000000000000000 : ℝ)).div_const 18
  have h18 := ((hasDerivAt_pow 19 t).const_mul (5507824980409830323849811828059 / 7812500000000000000000 : ℝ)).div_const 19
  have h19 := ((hasDerivAt_pow 20 t).const_mul (-2914676737382839613063008447817 / 3906250000000000000000 : ℝ)).div_const 20
  have h20 := ((hasDerivAt_pow 21 t).const_mul (32773395797778319715626203042909 / 62500000000000000000000 : ℝ)).div_const 21
  have h21 := ((hasDerivAt_pow 22 t).const_mul (-3115827249771098775523443459 / 12500000000000000000 : ℝ)).div_const 22
  have h22 := ((hasDerivAt_pow 23 t).const_mul (2423536313456318048783566435883 / 31250000000000000000000 : ℝ)).div_const 23
  have h23 := ((hasDerivAt_pow 24 t).const_mul (-223747011742194682977991566963 / 15625000000000000000000 : ℝ)).div_const 24
  have h24 := ((hasDerivAt_pow 25 t).const_mul (74582337247398227659330522321 / 62500000000000000000000 : ℝ)).div_const 25
  have h := ((((((((((((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15).add h16).add h17).add h18).add h19).add h20).add h21).add h22).add h23).add h24)
  exact h.congr_deriv (by push_cast; ring)

theorem rD_continuous : Continuous rD := by unfold rD; fun_prop


theorem psi1D_num_upper :
    RD (lamStarDyadic / 2) - RD (1 - lamStarDyadic / 2)
      ≤ (439 / 10000) * (sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (lamStarDyadic / 2)
          - sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (-(lamStarDyadic / 2))) ^ 2 := by
  unfold RD sqPrim lamStarDyadic
  norm_num

theorem psi1D_num_lower :
    (4388 / 100000) * (sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (lamStarDyadic / 2)
          - sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (-(lamStarDyadic / 2))) ^ 2
      ≤ RD (lamStarDyadic / 2) - RD (1 - lamStarDyadic / 2) := by
  unfold RD sqPrim lamStarDyadic
  norm_num

theorem cD_num :
    1 + (67 / 10) * (sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (lamStarDyadic / 2)
          - sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (1 - lamStarDyadic / 2))
      ≤ (183 / 100) * (sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (lamStarDyadic / 2)
          - sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (-(lamStarDyadic / 2))) ^ 2 := by
  unfold sqPrim lamStarDyadic
  norm_num

/-- `p′`. -/
def pD' (t : ℝ) : ℝ :=
  2 * (-1014099 / 1000000) * t + 4 * (834917 / 100000) * t ^ 3 + 6 * (-16525667 / 500000) * t ^ 5

theorem hasDerivAt_pD (t : ℝ) : HasDerivAt pD (pD' t) t := by
  unfold pD pD'
  have h2 := (hasDerivAt_pow 2 t).const_mul (-1014099 / 1000000 : ℝ)
  have h4 := (hasDerivAt_pow 4 t).const_mul (834917 / 100000 : ℝ)
  have h6 := (hasDerivAt_pow 6 t).const_mul (-16525667 / 500000 : ℝ)
  have h := ((h2.const_add 1).add h4).add h6
  exact h.congr_deriv (by push_cast; ring)

theorem hasDerivAt_pD_sq (t : ℝ) : HasDerivAt (fun s => pD s ^ 2) (2 * pD t * pD' t) t := by
  have h := (hasDerivAt_pD t).fun_pow 2
  exact h.congr_deriv (by push_cast; ring)

/-- `|t| ≤ λ*/2` gives `t² ≤ 0.356` (as in `profileQ_dyadic`). -/
theorem sq_le_of_coreD {t : ℝ} (ht : |t| ≤ lamStarDyadic / 2) : t ^ 2 ≤ 356 / 1000 := by
  have h1 : |t| ^ 2 ≤ (lamStarDyadic / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at h1
  unfold lamStarDyadic at h1
  norm_num at h1
  linarith

/-- `0 ≤ p ≤ 1` on the core (from `profileQ_dyadic`). -/
theorem pD_nonneg_le_one {t : ℝ} (ht : |t| ≤ lamStarDyadic / 2) : 0 ≤ pD t ∧ pD t ≤ 1 := by
  have h1 := profileQ_dyadic.bulk t ht
  have h2 := profileQ_dyadic.le_one t ht
  rw [eval_designProfileDyadic] at h1 h2
  exact ⟨by linarith, h2⟩

/-- `QdD(x) = 4P(x)P′(x)`, `P(x) = 1 + d₂x + d₄x² + d₆x³`, so that `(p²)′(s) = s·QdD(s²)`. -/
def QdD (x : ℝ) : ℝ :=
  4 * (1 + (-1014099 / 1000000) * x + (834917 / 100000) * x ^ 2 + (-16525667 / 500000) * x ^ 3)
    * ((-1014099 / 1000000) + 2 * (834917 / 100000) * x + 3 * (-16525667 / 500000) * x ^ 2)

/-- `−11.1 ≤ QdD ≤ 0` on `[0, 0.356]` (`sup|QdD| = 10.94` at `x = 0.299`; Bernstein certificates of
`11.1 + QdD` on `[0, .1], [.1, .2], [.2, .3], [.3, .3911]` — all coefficients `≥ 0.06`, `bern.py`). -/
theorem QdD_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 356 / 1000) :
    -111 / 10 ≤ QdD x ∧ QdD x ≤ 0 := by
  unfold QdD
  constructor
  · rcases le_or_gt x (1 / 10) with h1 | h1
    · have a1 : 0 ≤ 1 / 10 - x := by linarith
      nlinarith [mul_nonneg (pow_nonneg hx0 0) (pow_nonneg a1 5),
        mul_nonneg (pow_nonneg hx0 1) (pow_nonneg a1 4),
        mul_nonneg (pow_nonneg hx0 2) (pow_nonneg a1 3),
        mul_nonneg (pow_nonneg hx0 3) (pow_nonneg a1 2),
        mul_nonneg (pow_nonneg hx0 4) (pow_nonneg a1 1),
        mul_nonneg (pow_nonneg hx0 5) (pow_nonneg a1 0)]
    rcases le_or_gt x (2 / 10) with h2 | h2
    · have a0 : 0 ≤ x - 1 / 10 := by linarith
      have a1 : 0 ≤ 2 / 10 - x := by linarith
      nlinarith [mul_nonneg (pow_nonneg a0 0) (pow_nonneg a1 5),
        mul_nonneg (pow_nonneg a0 1) (pow_nonneg a1 4),
        mul_nonneg (pow_nonneg a0 2) (pow_nonneg a1 3),
        mul_nonneg (pow_nonneg a0 3) (pow_nonneg a1 2),
        mul_nonneg (pow_nonneg a0 4) (pow_nonneg a1 1),
        mul_nonneg (pow_nonneg a0 5) (pow_nonneg a1 0)]
    rcases le_or_gt x (3 / 10) with h3 | h3
    · have a0 : 0 ≤ x - 2 / 10 := by linarith
      have a1 : 0 ≤ 3 / 10 - x := by linarith
      nlinarith [mul_nonneg (pow_nonneg a0 0) (pow_nonneg a1 5),
        mul_nonneg (pow_nonneg a0 1) (pow_nonneg a1 4),
        mul_nonneg (pow_nonneg a0 2) (pow_nonneg a1 3),
        mul_nonneg (pow_nonneg a0 3) (pow_nonneg a1 2),
        mul_nonneg (pow_nonneg a0 4) (pow_nonneg a1 1),
        mul_nonneg (pow_nonneg a0 5) (pow_nonneg a1 0)]
    · have a0 : 0 ≤ x - 3 / 10 := by linarith
      have a1 : 0 ≤ 356 / 1000 - x := by linarith
      nlinarith [mul_nonneg (pow_nonneg a0 0) (pow_nonneg a1 5),
        mul_nonneg (pow_nonneg a0 1) (pow_nonneg a1 4),
        mul_nonneg (pow_nonneg a0 2) (pow_nonneg a1 3),
        mul_nonneg (pow_nonneg a0 3) (pow_nonneg a1 2),
        mul_nonneg (pow_nonneg a0 4) (pow_nonneg a1 1),
        mul_nonneg (pow_nonneg a0 5) (pow_nonneg a1 0)]
  · -- `P ≥ P(0.356) = 0.206 > 0` and `P′ < 0` (negative discriminant)
    have hr : (0 : ℝ) ≤ 1014099 / 1000000 - 834917 / 100000 * (x + 356 / 1000)
        + 16525667 / 500000 * (x ^ 2 + x * (356 / 1000) + (356 / 1000) ^ 2) := by
      nlinarith [sq_nonneg x]
    have hP : 0 ≤ 1 + (-1014099 / 1000000) * x + (834917 / 100000) * x ^ 2
        + (-16525667 / 500000) * x ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hx) hr]
    have hP' : (-1014099 / 1000000) + 2 * (834917 / 100000) * x + 3 * (-16525667 / 500000) * x ^ 2
        ≤ 0 := by
      nlinarith [sq_nonneg (x - 842 / 10000)]
    nlinarith [mul_nonneg hP (neg_nonneg.2 hP')]

/-- `|(p²)′| ≤ 6.7` on the core (`(p²)′(s) = s·QdD(s²)`, `|s| ≤ 0.5966`, `|QdD| ≤ 11.1`). -/
theorem abs_deriv_pD_sq_le {s : ℝ} (hs : |s| ≤ lamStarDyadic / 2) : |2 * pD s * pD' s| ≤ 67 / 10 := by
  have hx : s ^ 2 ≤ 356 / 1000 := sq_le_of_coreD hs
  have hx0 : 0 ≤ s ^ 2 := sq_nonneg s
  obtain ⟨hlo, hhi⟩ := QdD_bounds hx0 hx
  have e : 2 * pD s * pD' s = s * QdD (s ^ 2) := by unfold pD pD' QdD; ring
  rw [e, abs_mul]
  have hQ : |QdD (s ^ 2)| ≤ 111 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |s| * |QdD (s ^ 2)| ≤ (lamStarDyadic / 2) * (111 / 10) :=
        mul_le_mul hs hQ (abs_nonneg _) (by unfold lamStarDyadic; norm_num)
    _ ≤ 67 / 10 := by unfold lamStarDyadic; norm_num

/-- **`p²` is `6.7`-Lipschitz on the core** (mean value theorem). -/
theorem pD_sq_lip {x y : ℝ} (hx : |x| ≤ lamStarDyadic / 2) (hy : |y| ≤ lamStarDyadic / 2) :
    |pD y ^ 2 - pD x ^ 2| ≤ 67 / 10 * |y - x| := by
  have h := (convex_Icc (-(lamStarDyadic / 2)) (lamStarDyadic / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => pD s ^ 2) (f' := fun s => 2 * pD s * pD' s) (C := 67 / 10)
    (fun s _ => (hasDerivAt_pD_sq s).hasDerivWithinAt)
    (fun s hs => by rw [Real.norm_eq_abs]; exact abs_deriv_pD_sq_le (abs_le.mpr hs))
    (abs_le.mp hx) (abs_le.mp hy)
  simpa only [Real.norm_eq_abs] using h


theorem one_le_lamStarDyadic : (1 : ℝ) ≤ lamStarDyadic := by unfold lamStarDyadic; norm_num

/-- the same for the design of record, with `p = pD`, `b = λ*/2`. -/
theorem psi_vProfile_eq_pD (hprof : P.prof = designProfileDyadic) (hlam : P.lam = lamStarDyadic)
    {α : ℝ} (h0 : 0 ≤ α) (hα : α ≤ 1) :
    psi (vProfile P) α
      = (∫ t in (α - lamStarDyadic / 2)..(lamStarDyadic / 2), pD t ^ 2 * pD (t - α) ^ 2)
          / (profMass P) ^ 2 := by
  rw [psi_vProfile_eq P h0 (by rw [hlam]; linarith [one_le_lamStarDyadic]), hlam, hprof]
  simp_rw [eval_designProfileDyadic]

/-- `profMass = sqPrim(b) − sqPrim(−b)` at the design of record. -/
theorem profMass_eq_dyadic (hprof : P.prof = designProfileDyadic) (hlam : P.lam = lamStarDyadic) :
    profMass P
      = sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (lamStarDyadic / 2)
        - sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (-(lamStarDyadic / 2)) := by
  unfold profMass
  rw [hlam, hprof]
  simp_rw [designProfileDyadic_eval]
  exact integral_sq_poly _ _ _ _ _


/-- **The Lipschitz bound** `ψ(α) ≤ ψ(1) + 1.83·(1 − α)` on `[0, 1]`. -/
theorem psiD_le_psi_one_add (hP : P.Valid) (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    psi (vProfile P) α ≤ psi (vProfile P) 1 + (183 / 100) * (1 - α) := by
  have hb1 : 1 - lamStarDyadic / 2 ≤ lamStarDyadic / 2 := by unfold lamStarDyadic; norm_num
  have hbh : 1 / 2 < lamStarDyadic / 2 := by unfold lamStarDyadic; norm_num
  have hbl : lamStarDyadic / 2 ≤ 1 := by unfold lamStarDyadic; norm_num
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  have hcont : ∀ β : ℝ, Continuous fun t => pD t ^ 2 * pD (t - β) ^ 2 := by
    intro β
    have := pD_continuous
    fun_prop
  have hIα : ∀ a c : ℝ, IntervalIntegrable (fun t => pD t ^ 2 * pD (t - α) ^ 2) volume a c :=
    fun a c => (hcont α).intervalIntegrable a c
  have hI1 : ∀ a c : ℝ, IntervalIntegrable (fun t => pD t ^ 2 * pD (t - 1) ^ 2) volume a c :=
    fun a c => (hcont 1).intervalIntegrable a c
  rw [psi_vProfile_eq_pD hprof hlam h0 h1, psi_vProfile_eq_pD hprof hlam zero_le_one le_rfl]
  -- the split at `1 − b`
  have hsplit : ∫ t in (α - lamStarDyadic / 2)..(lamStarDyadic / 2), pD t ^ 2 * pD (t - α) ^ 2
      = (∫ t in (α - lamStarDyadic / 2)..(1 - lamStarDyadic / 2), pD t ^ 2 * pD (t - α) ^ 2)
        + ∫ t in (1 - lamStarDyadic / 2)..(lamStarDyadic / 2), pD t ^ 2 * pD (t - α) ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hIα _ _) (hIα _ _)).symm
  -- term 1: `≤ 1·(1 − α)`
  have hT1 : ∫ t in (α - lamStarDyadic / 2)..(1 - lamStarDyadic / 2), pD t ^ 2 * pD (t - α) ^ 2
      ≤ 1 * (1 - α) := by
    have hbd : ∀ x ∈ Set.uIoc (α - lamStarDyadic / 2) (1 - lamStarDyadic / 2), ‖pD x ^ 2 * pD (x - α) ^ 2‖ ≤ 1 := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hA := pD_nonneg_le_one (t := x) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hB := pD_nonneg_le_one (t := x - α) (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : pD x ^ 2 * pD (x - α) ^ 2 ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ hA.1 hA.2) (pow_le_one₀ hB.1 hB.2) (by positivity) zero_le_one
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, show (1 - lamStarDyadic / 2) - (α - lamStarDyadic / 2) = 1 - α by ring,
      abs_of_nonneg (show (0:ℝ) ≤ 1 - α by linarith)] at this
    exact (le_abs_self _).trans this
  -- term 2: `≤ 6.7(1 − α)·∫_{1−b}^{b} p²`
  have hI2 : ∫ t in (1 - lamStarDyadic / 2)..(lamStarDyadic / 2), pD t ^ 2
      = sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (lamStarDyadic / 2)
        - sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (1 - lamStarDyadic / 2) := by
    unfold pD
    exact integral_sq_poly _ _ _ _ _
  have hT2 : (∫ t in (1 - lamStarDyadic / 2)..(lamStarDyadic / 2), pD t ^ 2 * pD (t - α) ^ 2)
        - ∫ t in (1 - lamStarDyadic / 2)..(lamStarDyadic / 2), pD t ^ 2 * pD (t - 1) ^ 2
      ≤ (67 / 10 * (1 - α))
          * (sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (lamStarDyadic / 2)
            - sqPrim (-1014099 / 1000000) (834917 / 100000) (-16525667 / 500000) (1 - lamStarDyadic / 2)) := by
    rw [← intervalIntegral.integral_sub (hIα _ _) (hI1 _ _), ← hI2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hb1 ((hIα _ _).sub (hI1 _ _))
      (((pD_continuous.pow 2).const_mul _).intervalIntegrable _ _)
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hlip := pD_sq_lip (x := x - 1) (y := x - α)
      (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [show (x - α) - (x - 1) = 1 - α by ring, abs_of_nonneg (show (0:ℝ) ≤ 1 - α by linarith)] at hlip
    have hd : pD (x - α) ^ 2 - pD (x - 1) ^ 2 ≤ 67 / 10 * (1 - α) := (le_abs_self _).trans hlip
    have hsq : 0 ≤ pD x ^ 2 := sq_nonneg _
    calc pD x ^ 2 * pD (x - α) ^ 2 - pD x ^ 2 * pD (x - 1) ^ 2
        = pD x ^ 2 * (pD (x - α) ^ 2 - pD (x - 1) ^ 2) := by ring
      _ ≤ pD x ^ 2 * (67 / 10 * (1 - α)) := mul_le_mul_of_nonneg_left hd hsq
      _ = 67 / 10 * (1 - α) * pD x ^ 2 := by ring
  -- assemble: `Ψ(α) ≤ Ψ(1) + (1−α)(1 + 6.7·I₂) ≤ Ψ(1) + (1−α)·1.83·M²`
  have hD := cD_num
  rw [← profMass_eq_dyadic hprof hlam] at hD
  have hD' := mul_le_mul_of_nonneg_left hD (sub_nonneg.2 h1)
  rw [hsplit, div_le_iff₀ hM2, add_mul, div_mul_cancel₀ _ hM2.ne']
  nlinarith [hT1, hT2, hD']


theorem psiD_one_eq (hprof : P.prof = designProfileDyadic) (hlam : P.lam = lamStarDyadic) :
    psi (vProfile P) 1
      = (RD (lamStarDyadic / 2) - RD (1 - lamStarDyadic / 2)) / (profMass P) ^ 2 := by
  rw [psi_vProfile_eq_pD hprof hlam zero_le_one le_rfl]
  congr 1
  simp_rw [pD_sq_mul_pD_sq_eq]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_RD x)
    (rD_continuous.intervalIntegrable _ _)

/-- `ψ_dyad(1) ≤ 0.0439`. -/
theorem psiD_one_le (hP : P.Valid) (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) : psi (vProfile P) 1 ≤ 439 / 10000 := by
  rw [psiD_one_eq hprof hlam]
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  rw [div_le_iff₀ hM2, profMass_eq_dyadic hprof hlam]
  exact psi1D_num_upper

/-- `0.04388 ≤ ψ_dyad(1)`. -/
theorem le_psiD_one (hP : P.Valid) (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) : 4388 / 100000 ≤ psi (vProfile P) 1 := by
  rw [psiD_one_eq hprof hlam]
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  rw [le_div_iff₀ hM2, profMass_eq_dyadic hprof hlam]
  exact psi1D_num_lower

/-- **The dyadic zone comparison FAILS against `sZone`**: at every dyadic design point
`2(C_dyad − 1)·ψ_{v_profile}(1) ≥ 2·6.2154·0.04388 = 0.5454 > 0.5073 = sZone`, so the limiting
slope `2(C−1)ψ(1)` of `(C−1)·Jzone a v` exceeds `sZone`, and `ZoneLipschitzData Family.dyadic`
(whose margin clause is against `sZone`) cannot hold at any realised design point. -/
theorem dyadic_margin_fails (hP : P.Valid) (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) :
    sZone < 2 * (CfamDyadic - 1) * psi (vProfile P) 1 := by
  have h := le_psiD_one hP hprof hlam
  have hC : (2 * 97408 / 27000 : ℝ) ≤ CfamDyadic := by
    unfold CfamDyadic
    have := Ends.pi_four_gt
    linarith
  have hC1 : (2 * 97408 / 27000 - 1 : ℝ) ≤ CfamDyadic - 1 := by linarith
  have hm := mul_le_mul hC1 h (by norm_num) (by linarith)
  unfold sZone
  nlinarith [hm]

/-- the dyadic data against `sZoneDyadic` (written when `ZoneLipschitzData`'s margin clause used
`sZone` for both families; since F63 it is literally `ZoneLipschitzData Family.dyadic r ε` —
`zoneLipschitzData_dyadic` below). -/
def ZoneLipschitzDataDyadic (r ε : ℝ) : Prop :=
  ∃ ψ₁ c : ℝ, 0 ≤ c ∧ 2 * (CfamDyadic - 1) * ψ₁ < sZoneDyadic ∧
    ∀ (Qn : ℕ) (P : ParamsQ), DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      ∀ α, 0 ≤ α → α ≤ 1 → psi (vProfile P) α ≤ ψ₁ + c * (1 - α)

theorem CfamDyadic_le : CfamDyadic ≤ 2 * 3141593 ^ 4 / (27 * 10 ^ 24) := by
  have h := C_dyad_le
  unfold CfamDyadic
  push_cast at h
  linarith

/-- **`ZoneLipschitzDataDyadic r ε`, certified**: `ψ₁ = 0.0439`, `c = 1.83`,
`2(C_dyad − 1)ψ₁ ≤ 2·6.21549·0.0439 = 0.54572 < 0.5485 = sZoneDyadic` (margin `0.0028`). -/
theorem zoneLipschitzDataDyadic (r ε : ℝ) : ZoneLipschitzDataDyadic r ε := by
  refine ⟨439 / 10000, 183 / 100, by norm_num, ?_, ?_⟩
  · have := CfamDyadic_le
    unfold sZoneDyadic
    linarith
  · intro Qn P hdes α h0 h1
    obtain ⟨hP, -, -, hlam, -, -, -, -, -, -, -, hprof⟩ := hdes
    have hlam' : P.lam = lamStarDyadic := hlam
    have hprof' : P.prof = designProfileDyadic := hprof
    have h := psiD_le_psi_one_add hP hprof' hlam' h0 h1
    have h' := psiD_one_le hP hprof' hlam'
    linarith

/-- **`ZoneLipschitzData Family.dyadic r ε`, certified**: `zoneLipschitzDataDyadic` read at
the family-aware margin clause (`Family.dyadic.sZoneF = sZoneDyadic`, `Family.dyadic.Cconst =
CfamDyadic`, both `rfl`). -/
theorem zoneLipschitzData_dyadic (r ε : ℝ) : ZoneLipschitzData Family.dyadic r ε := by
  obtain ⟨ψ₁, c, hc, hm, hlip⟩ := zoneLipschitzDataDyadic r ε
  exact ⟨ψ₁, c, hc, hm, hlip⟩


/-! ## §7. The even/odd DYADIC parity family of Corollary 3 (`C = 4π⁴/27`, secant
`sZoneEvenDyadic = 0.6151116`).

The route of §§1–5 at the refitted parity design (`designProfileEvenDyad12`, degree 12,
`λ' = lamStarEvenDyad12 = 1.0955998422`, support `b = λ'/2 = 0.5477999211`): `p(t)²p(t−1)²` is
the degree-48 `rED`, whose antiderivative gives `ψ(1) = 0.0226880402… ≤ 0.0227`, against which

    2(C − 1)ψ₁ ≤ 2·13.430983·0.0227 = 0.609767 < 0.6151116 = sZoneEvenDyadic   (margin 0.0053).

The Lipschitz constant of `p²` on the core is taken CRUDELY — `|(p²)′| ≤ 84` against a true sup
of `12.35`, by `|p| ≤ 1` and `|p′| ≤ 42` — because it enters only the eventual threshold `θ` of
`zone_compare_eventually`, never a margin; whence `c = 6 ≥ (1 + 84·I₂)/M² = 5.72`. Even and odd
share `Family.Cconst`, `Family.sZoneF` and `Family.designProfile`, so ONE certificate serves
both (`zoneLipschitzData_evenDyadic`, `zoneLipschitzData_oddDyadic`). -/

/-- `p(t)` for the even/odd dyadic REFIT design, as an explicit function. -/
def pED (t : ℝ) : ℝ :=
  1 + (-402449 / 1000000) * t ^ 2 + (-142417 / 125000) * t ^ 4 + (-16037751 / 1000000) * t ^ 6
    + (45473063 / 250000) * t ^ 8 + (-2194509137 / 1000000) * t ^ 12

theorem eval_designProfileEvenDyad12 (t : ℝ) : designProfileEvenDyad12.eval t = pED t :=
  designProfileEvenDyad12_eval t

theorem pED_continuous : Continuous pED := by unfold pED; fun_prop

/-- `r(t) = p(t)²p(t−1)²` expanded (degree 48; coefficients exact). -/
def rED (t : ℝ) : ℝ :=
    (4117638114999209241 / 1000000000000 : ℝ) * t ^ 0
    + (-6336307963694201787 / 62500000000 : ℝ) * t ^ 1
    + (594429186208566455364168791 / 500000000000000000 : ℝ) * t ^ 2
    + (-275997448794443890075523637 / 31250000000000000 : ℝ) * t ^ 3
    + (46615633173958766220872942654230841 / 1000000000000000000000000 : ℝ) * t ^ 4
    + (-11605319291955511090191737220312987 / 62500000000000000000000 : ℝ) * t ^ 5
    + (72237120999480754744810495526202937 / 125000000000000000000000 : ℝ) * t ^ 6
    + (-89383286858674579764947678327171317 / 62500000000000000000000 : ℝ) * t ^ 7
    + (281050203557690152588869984264568643 / 100000000000000000000000 : ℝ) * t ^ 8
    + (-1056128687697812991568867440277635837 / 250000000000000000000000 : ℝ) * t ^ 9
    + (2092921369333687960563594711018145251 / 500000000000000000000000 : ℝ) * t ^ 10
    + (-54091032343812305683283912118283149 / 62500000000000000000000 : ℝ) * t ^ 11
    + (-3300361340691406018658548638158066737 / 1000000000000000000000000 : ℝ) * t ^ 12
    + (-168568028762856759299765739364820561 / 15625000000000000000000 : ℝ) * t ^ 13
    + (47620707120821116418055220374027706091 / 500000000000000000000000 : ℝ) * t ^ 14
    + (-81212573647608743935855740577874803721 / 250000000000000000000000 : ℝ) * t ^ 15
    + (138388103581507788131115132928271949051 / 200000000000000000000000 : ℝ) * t ^ 16
    + (-52809790532024006169341838200030254749 / 62500000000000000000000 : ℝ) * t ^ 17
    + (-24889122321058489362852142223414993489 / 100000000000000000000000 : ℝ) * t ^ 18
    + (13492760276706387009199454348727141499 / 3125000000000000000000 : ℝ) * t ^ 19
    + (-12724217785886424698638942625273098913207 / 1000000000000000000000000 : ℝ) * t ^ 20
    + (5914851649673534744144187641091513532971 / 250000000000000000000000 : ℝ) * t ^ 21
    + (-14152475823750422399650250884963689668999 / 500000000000000000000000 : ℝ) * t ^ 22
    + (2607313586909445542715439281951924877447 / 250000000000000000000000 : ℝ) * t ^ 23
    + (316299149541902976069171531005911387199 / 7812500000000000000000 : ℝ) * t ^ 24
    + (-4577865385331617043247997010429293273021 / 50000000000000000000000 : ℝ) * t ^ 25
    + (3224891083480491205843298739962112051059 / 250000000000000000000000 : ℝ) * t ^ 26
    + (26930696576166830270206316240193235975123 / 62500000000000000000000 : ℝ) * t ^ 27
    + (-714276820179520543639816219857363495109621 / 500000000000000000000000 : ℝ) * t ^ 28
    + (170866431527986025809847650658502794864851 / 62500000000000000000000 : ℝ) * t ^ 29
    + (-798520614455284208926336659150595495469263 / 250000000000000000000000 : ℝ) * t ^ 30
    + (84544426327570310867360860970669787245977 / 125000000000000000000000 : ℝ) * t ^ 31
    + (3533764443452442274574390062235685680226043 / 500000000000000000000000 : ℝ) * t ^ 32
    + (-258178297610526770009515015864915449364371 / 12500000000000000000000 : ℝ) * t ^ 33
    + (18775151854013575646631784570280297690206747 / 500000000000000000000000 : ℝ) * t ^ 34
    + (-13091470877879959976993939954974523486404237 / 250000000000000000000000 : ℝ) * t ^ 35
    + (743271948055451434717372079661117164920731 / 12500000000000000000000 : ℝ) * t ^ 36
    + (-14070478378320608386086725773590581166845731 / 250000000000000000000000 : ℝ) * t ^ 37
    + (2801561288969551733401432179727384341196749 / 62500000000000000000000 : ℝ) * t ^ 38
    + (-235174916629212784341109288190831583102191 / 7812500000000000000000 : ℝ) * t ^ 39
    + (16998155957144182720164470814105042486955741 / 1000000000000000000000000 : ℝ) * t ^ 40
    + (-2003725979264019606604394685908686727819657 / 250000000000000000000000 : ℝ) * t ^ 41
    + (194990077400610854710329014311144345698911 / 62500000000000000000000 : ℝ) * t ^ 42
    + (-123201176770148915870135086680434069134477 / 125000000000000000000000 : ℝ) * t ^ 43
    + (123218477677866010336810140509814132331081 / 500000000000000000000000 : ℝ) * t ^ 44
    + (-5867729634477398317273234773794112790333 / 125000000000000000000000 : ℝ) * t ^ 45
    + (1600289900312017722892700392852939851909 / 250000000000000000000000 : ℝ) * t ^ 46
    + (-69577821752696422734465234471866950083 / 125000000000000000000000 : ℝ) * t ^ 47
    + (23192607250898807578155078157288983361 / 1000000000000000000000000 : ℝ) * t ^ 48

theorem pED_sq_mul_pED_sq_eq (t : ℝ) : pED t ^ 2 * pED (t - 1) ^ 2 = rED t := by
  unfold pED rED; ring

/-- the antiderivative of `rED`. -/
def RED (t : ℝ) : ℝ :=
    (4117638114999209241 / 1000000000000 : ℝ) * t ^ 1 / 1
    + (-6336307963694201787 / 62500000000 : ℝ) * t ^ 2 / 2
    + (594429186208566455364168791 / 500000000000000000 : ℝ) * t ^ 3 / 3
    + (-275997448794443890075523637 / 31250000000000000 : ℝ) * t ^ 4 / 4
    + (46615633173958766220872942654230841 / 1000000000000000000000000 : ℝ) * t ^ 5 / 5
    + (-11605319291955511090191737220312987 / 62500000000000000000000 : ℝ) * t ^ 6 / 6
    + (72237120999480754744810495526202937 / 125000000000000000000000 : ℝ) * t ^ 7 / 7
    + (-89383286858674579764947678327171317 / 62500000000000000000000 : ℝ) * t ^ 8 / 8
    + (281050203557690152588869984264568643 / 100000000000000000000000 : ℝ) * t ^ 9 / 9
    + (-1056128687697812991568867440277635837 / 250000000000000000000000 : ℝ) * t ^ 10 / 10
    + (2092921369333687960563594711018145251 / 500000000000000000000000 : ℝ) * t ^ 11 / 11
    + (-54091032343812305683283912118283149 / 62500000000000000000000 : ℝ) * t ^ 12 / 12
    + (-3300361340691406018658548638158066737 / 1000000000000000000000000 : ℝ) * t ^ 13 / 13
    + (-168568028762856759299765739364820561 / 15625000000000000000000 : ℝ) * t ^ 14 / 14
    + (47620707120821116418055220374027706091 / 500000000000000000000000 : ℝ) * t ^ 15 / 15
    + (-81212573647608743935855740577874803721 / 250000000000000000000000 : ℝ) * t ^ 16 / 16
    + (138388103581507788131115132928271949051 / 200000000000000000000000 : ℝ) * t ^ 17 / 17
    + (-52809790532024006169341838200030254749 / 62500000000000000000000 : ℝ) * t ^ 18 / 18
    + (-24889122321058489362852142223414993489 / 100000000000000000000000 : ℝ) * t ^ 19 / 19
    + (13492760276706387009199454348727141499 / 3125000000000000000000 : ℝ) * t ^ 20 / 20
    + (-12724217785886424698638942625273098913207 / 1000000000000000000000000 : ℝ) * t ^ 21 / 21
    + (5914851649673534744144187641091513532971 / 250000000000000000000000 : ℝ) * t ^ 22 / 22
    + (-14152475823750422399650250884963689668999 / 500000000000000000000000 : ℝ) * t ^ 23 / 23
    + (2607313586909445542715439281951924877447 / 250000000000000000000000 : ℝ) * t ^ 24 / 24
    + (316299149541902976069171531005911387199 / 7812500000000000000000 : ℝ) * t ^ 25 / 25
    + (-4577865385331617043247997010429293273021 / 50000000000000000000000 : ℝ) * t ^ 26 / 26
    + (3224891083480491205843298739962112051059 / 250000000000000000000000 : ℝ) * t ^ 27 / 27
    + (26930696576166830270206316240193235975123 / 62500000000000000000000 : ℝ) * t ^ 28 / 28
    + (-714276820179520543639816219857363495109621 / 500000000000000000000000 : ℝ) * t ^ 29 / 29
    + (170866431527986025809847650658502794864851 / 62500000000000000000000 : ℝ) * t ^ 30 / 30
    + (-798520614455284208926336659150595495469263 / 250000000000000000000000 : ℝ) * t ^ 31 / 31
    + (84544426327570310867360860970669787245977 / 125000000000000000000000 : ℝ) * t ^ 32 / 32
    + (3533764443452442274574390062235685680226043 / 500000000000000000000000 : ℝ) * t ^ 33 / 33
    + (-258178297610526770009515015864915449364371 / 12500000000000000000000 : ℝ) * t ^ 34 / 34
    + (18775151854013575646631784570280297690206747 / 500000000000000000000000 : ℝ) * t ^ 35 / 35
    + (-13091470877879959976993939954974523486404237 / 250000000000000000000000 : ℝ) * t ^ 36 / 36
    + (743271948055451434717372079661117164920731 / 12500000000000000000000 : ℝ) * t ^ 37 / 37
    + (-14070478378320608386086725773590581166845731 / 250000000000000000000000 : ℝ) * t ^ 38 / 38
    + (2801561288969551733401432179727384341196749 / 62500000000000000000000 : ℝ) * t ^ 39 / 39
    + (-235174916629212784341109288190831583102191 / 7812500000000000000000 : ℝ) * t ^ 40 / 40
    + (16998155957144182720164470814105042486955741 / 1000000000000000000000000 : ℝ) * t ^ 41 / 41
    + (-2003725979264019606604394685908686727819657 / 250000000000000000000000 : ℝ) * t ^ 42 / 42
    + (194990077400610854710329014311144345698911 / 62500000000000000000000 : ℝ) * t ^ 43 / 43
    + (-123201176770148915870135086680434069134477 / 125000000000000000000000 : ℝ) * t ^ 44 / 44
    + (123218477677866010336810140509814132331081 / 500000000000000000000000 : ℝ) * t ^ 45 / 45
    + (-5867729634477398317273234773794112790333 / 125000000000000000000000 : ℝ) * t ^ 46 / 46
    + (1600289900312017722892700392852939851909 / 250000000000000000000000 : ℝ) * t ^ 47 / 47
    + (-69577821752696422734465234471866950083 / 125000000000000000000000 : ℝ) * t ^ 48 / 48
    + (23192607250898807578155078157288983361 / 1000000000000000000000000 : ℝ) * t ^ 49 / 49

theorem hasDerivAt_RED (t : ℝ) : HasDerivAt RED (rED t) t := by
  unfold RED rED
  have h0 := ((hasDerivAt_pow 1 t).const_mul (4117638114999209241 / 1000000000000 : ℝ)).div_const 1
  have h1 := ((hasDerivAt_pow 2 t).const_mul (-6336307963694201787 / 62500000000 : ℝ)).div_const 2
  have h2 := ((hasDerivAt_pow 3 t).const_mul (594429186208566455364168791 / 500000000000000000 : ℝ)).div_const 3
  have h3 := ((hasDerivAt_pow 4 t).const_mul (-275997448794443890075523637 / 31250000000000000 : ℝ)).div_const 4
  have h4 := ((hasDerivAt_pow 5 t).const_mul (46615633173958766220872942654230841 / 1000000000000000000000000 : ℝ)).div_const 5
  have h5 := ((hasDerivAt_pow 6 t).const_mul (-11605319291955511090191737220312987 / 62500000000000000000000 : ℝ)).div_const 6
  have h6 := ((hasDerivAt_pow 7 t).const_mul (72237120999480754744810495526202937 / 125000000000000000000000 : ℝ)).div_const 7
  have h7 := ((hasDerivAt_pow 8 t).const_mul (-89383286858674579764947678327171317 / 62500000000000000000000 : ℝ)).div_const 8
  have h8 := ((hasDerivAt_pow 9 t).const_mul (281050203557690152588869984264568643 / 100000000000000000000000 : ℝ)).div_const 9
  have h9 := ((hasDerivAt_pow 10 t).const_mul (-1056128687697812991568867440277635837 / 250000000000000000000000 : ℝ)).div_const 10
  have h10 := ((hasDerivAt_pow 11 t).const_mul (2092921369333687960563594711018145251 / 500000000000000000000000 : ℝ)).div_const 11
  have h11 := ((hasDerivAt_pow 12 t).const_mul (-54091032343812305683283912118283149 / 62500000000000000000000 : ℝ)).div_const 12
  have h12 := ((hasDerivAt_pow 13 t).const_mul (-3300361340691406018658548638158066737 / 1000000000000000000000000 : ℝ)).div_const 13
  have h13 := ((hasDerivAt_pow 14 t).const_mul (-168568028762856759299765739364820561 / 15625000000000000000000 : ℝ)).div_const 14
  have h14 := ((hasDerivAt_pow 15 t).const_mul (47620707120821116418055220374027706091 / 500000000000000000000000 : ℝ)).div_const 15
  have h15 := ((hasDerivAt_pow 16 t).const_mul (-81212573647608743935855740577874803721 / 250000000000000000000000 : ℝ)).div_const 16
  have h16 := ((hasDerivAt_pow 17 t).const_mul (138388103581507788131115132928271949051 / 200000000000000000000000 : ℝ)).div_const 17
  have h17 := ((hasDerivAt_pow 18 t).const_mul (-52809790532024006169341838200030254749 / 62500000000000000000000 : ℝ)).div_const 18
  have h18 := ((hasDerivAt_pow 19 t).const_mul (-24889122321058489362852142223414993489 / 100000000000000000000000 : ℝ)).div_const 19
  have h19 := ((hasDerivAt_pow 20 t).const_mul (13492760276706387009199454348727141499 / 3125000000000000000000 : ℝ)).div_const 20
  have h20 := ((hasDerivAt_pow 21 t).const_mul (-12724217785886424698638942625273098913207 / 1000000000000000000000000 : ℝ)).div_const 21
  have h21 := ((hasDerivAt_pow 22 t).const_mul (5914851649673534744144187641091513532971 / 250000000000000000000000 : ℝ)).div_const 22
  have h22 := ((hasDerivAt_pow 23 t).const_mul (-14152475823750422399650250884963689668999 / 500000000000000000000000 : ℝ)).div_const 23
  have h23 := ((hasDerivAt_pow 24 t).const_mul (2607313586909445542715439281951924877447 / 250000000000000000000000 : ℝ)).div_const 24
  have h24 := ((hasDerivAt_pow 25 t).const_mul (316299149541902976069171531005911387199 / 7812500000000000000000 : ℝ)).div_const 25
  have h25 := ((hasDerivAt_pow 26 t).const_mul (-4577865385331617043247997010429293273021 / 50000000000000000000000 : ℝ)).div_const 26
  have h26 := ((hasDerivAt_pow 27 t).const_mul (3224891083480491205843298739962112051059 / 250000000000000000000000 : ℝ)).div_const 27
  have h27 := ((hasDerivAt_pow 28 t).const_mul (26930696576166830270206316240193235975123 / 62500000000000000000000 : ℝ)).div_const 28
  have h28 := ((hasDerivAt_pow 29 t).const_mul (-714276820179520543639816219857363495109621 / 500000000000000000000000 : ℝ)).div_const 29
  have h29 := ((hasDerivAt_pow 30 t).const_mul (170866431527986025809847650658502794864851 / 62500000000000000000000 : ℝ)).div_const 30
  have h30 := ((hasDerivAt_pow 31 t).const_mul (-798520614455284208926336659150595495469263 / 250000000000000000000000 : ℝ)).div_const 31
  have h31 := ((hasDerivAt_pow 32 t).const_mul (84544426327570310867360860970669787245977 / 125000000000000000000000 : ℝ)).div_const 32
  have h32 := ((hasDerivAt_pow 33 t).const_mul (3533764443452442274574390062235685680226043 / 500000000000000000000000 : ℝ)).div_const 33
  have h33 := ((hasDerivAt_pow 34 t).const_mul (-258178297610526770009515015864915449364371 / 12500000000000000000000 : ℝ)).div_const 34
  have h34 := ((hasDerivAt_pow 35 t).const_mul (18775151854013575646631784570280297690206747 / 500000000000000000000000 : ℝ)).div_const 35
  have h35 := ((hasDerivAt_pow 36 t).const_mul (-13091470877879959976993939954974523486404237 / 250000000000000000000000 : ℝ)).div_const 36
  have h36 := ((hasDerivAt_pow 37 t).const_mul (743271948055451434717372079661117164920731 / 12500000000000000000000 : ℝ)).div_const 37
  have h37 := ((hasDerivAt_pow 38 t).const_mul (-14070478378320608386086725773590581166845731 / 250000000000000000000000 : ℝ)).div_const 38
  have h38 := ((hasDerivAt_pow 39 t).const_mul (2801561288969551733401432179727384341196749 / 62500000000000000000000 : ℝ)).div_const 39
  have h39 := ((hasDerivAt_pow 40 t).const_mul (-235174916629212784341109288190831583102191 / 7812500000000000000000 : ℝ)).div_const 40
  have h40 := ((hasDerivAt_pow 41 t).const_mul (16998155957144182720164470814105042486955741 / 1000000000000000000000000 : ℝ)).div_const 41
  have h41 := ((hasDerivAt_pow 42 t).const_mul (-2003725979264019606604394685908686727819657 / 250000000000000000000000 : ℝ)).div_const 42
  have h42 := ((hasDerivAt_pow 43 t).const_mul (194990077400610854710329014311144345698911 / 62500000000000000000000 : ℝ)).div_const 43
  have h43 := ((hasDerivAt_pow 44 t).const_mul (-123201176770148915870135086680434069134477 / 125000000000000000000000 : ℝ)).div_const 44
  have h44 := ((hasDerivAt_pow 45 t).const_mul (123218477677866010336810140509814132331081 / 500000000000000000000000 : ℝ)).div_const 45
  have h45 := ((hasDerivAt_pow 46 t).const_mul (-5867729634477398317273234773794112790333 / 125000000000000000000000 : ℝ)).div_const 46
  have h46 := ((hasDerivAt_pow 47 t).const_mul (1600289900312017722892700392852939851909 / 250000000000000000000000 : ℝ)).div_const 47
  have h47 := ((hasDerivAt_pow 48 t).const_mul (-69577821752696422734465234471866950083 / 125000000000000000000000 : ℝ)).div_const 48
  have h48 := ((hasDerivAt_pow 49 t).const_mul (23192607250898807578155078157288983361 / 1000000000000000000000000 : ℝ)).div_const 49
  have h := ((((((((((((((((((((((((((((((((((((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15).add h16).add h17).add h18).add h19).add h20).add h21).add h22).add h23).add h24).add h25).add h26).add h27).add h28).add h29).add h30).add h31).add h32).add h33).add h34).add h35).add h36).add h37).add h38).add h39).add h40).add h41).add h42).add h43).add h44).add h45).add h46).add h47).add h48)
  exact h.congr_deriv (by push_cast; ring)


theorem rED_continuous : Continuous rED := by unfold rED; fun_prop

set_option maxHeartbeats 1000000 in
/-- `∫_{1−b}^{b} p(t)²p(t−1)² = R(b) − R(1−b) ≤ 0.0227·M²` (exact rationals;
`ψ(1) = 0.0226880402…`). -/
theorem psi1ED_num :
    RED (lamStarEvenDyad12 / 2) - RED (1 - lamStarEvenDyad12 / 2)
      ≤ (227 / 10000) * (sqPrimEvenDyad12 (lamStarEvenDyad12 / 2)
          - sqPrimEvenDyad12 (-(lamStarEvenDyad12 / 2))) ^ 2 := by
  unfold RED sqPrimEvenDyad12 lamStarEvenDyad12
  norm_num

set_option maxHeartbeats 1000000 in
/-- `1 + 84·∫_{1−b}^{b} p² ≤ 6·M²` (`(1 + 84·I₂)/M² = 5.7213`). -/
theorem cED_num :
    1 + (84 : ℝ) * (sqPrimEvenDyad12 (lamStarEvenDyad12 / 2)
          - sqPrimEvenDyad12 (1 - lamStarEvenDyad12 / 2))
      ≤ (6 : ℝ) * (sqPrimEvenDyad12 (lamStarEvenDyad12 / 2)
          - sqPrimEvenDyad12 (-(lamStarEvenDyad12 / 2))) ^ 2 := by
  unfold sqPrimEvenDyad12 lamStarEvenDyad12
  norm_num

/-- `p′`. -/
def pED' (t : ℝ) : ℝ :=
  2 * (-402449 / 1000000) * t + 4 * (-142417 / 125000) * t ^ 3
    + 6 * (-16037751 / 1000000) * t ^ 5 + 8 * (45473063 / 250000) * t ^ 7
    + 12 * (-2194509137 / 1000000) * t ^ 11

theorem hasDerivAt_pED (t : ℝ) : HasDerivAt pED (pED' t) t := by
  unfold pED pED'
  have h2 := (hasDerivAt_pow 2 t).const_mul (-402449 / 1000000 : ℝ)
  have h4 := (hasDerivAt_pow 4 t).const_mul (-142417 / 125000 : ℝ)
  have h6 := (hasDerivAt_pow 6 t).const_mul (-16037751 / 1000000 : ℝ)
  have h8 := (hasDerivAt_pow 8 t).const_mul (45473063 / 250000 : ℝ)
  have h12 := (hasDerivAt_pow 12 t).const_mul (-2194509137 / 1000000 : ℝ)
  have h := ((((h2.const_add 1).add h4).add h6).add h8).add h12
  exact h.congr_deriv (by push_cast; ring)

theorem hasDerivAt_pED_sq (t : ℝ) :
    HasDerivAt (fun s => pED s ^ 2) (2 * pED t * pED' t) t := by
  have h := (hasDerivAt_pED t).fun_pow 2
  exact h.congr_deriv (by push_cast; ring)

/-- `|t| ≤ λ'/2` gives `t² ≤ 0.30009` (as in `profileQ_evendyad12`). -/
theorem sq_le_of_coreED {t : ℝ} (ht : |t| ≤ lamStarEvenDyad12 / 2) :
    t ^ 2 ≤ 30009 / 100000 := by
  have h1 : |t| ^ 2 ≤ (lamStarEvenDyad12 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at h1
  unfold lamStarEvenDyad12 at h1
  norm_num at h1
  linarith

/-- `0 ≤ p ≤ 1` on the core (from `profileQ_evendyad12`). -/
theorem pED_nonneg_le_one {t : ℝ} (ht : |t| ≤ lamStarEvenDyad12 / 2) :
    0 ≤ pED t ∧ pED t ≤ 1 := by
  have h1 := profileQ_evendyad12.bulk t ht
  have h2 := profileQ_evendyad12.le_one t ht
  rw [eval_designProfileEvenDyad12] at h1 h2
  exact ⟨by linarith, h2⟩

/-- `|G| ≤ 75` on `[0, 0.30009]`, `G(x) = 2d₂ + 4d₄x + 6d₆x² + 8d₈x³ + 12d₁₂x⁵`, so that
`p′(s) = s·G(s²)`. The bound is the crude termwise one (`G ∈ [−74.93, 39.33]`). -/
theorem GED_abs_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 30009 / 100000) :
    |2 * (-402449 / 1000000 : ℝ) + 4 * (-142417 / 125000) * x
      + 6 * (-16037751 / 1000000) * x ^ 2 + 8 * (45473063 / 250000) * x ^ 3
      + 12 * (-2194509137 / 1000000) * x ^ 5| ≤ 75 := by
  have h2 : x ^ 2 ≤ (30009 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have h3 : x ^ 3 ≤ (30009 / 100000 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx 3
  have h5 : x ^ 5 ≤ (30009 / 100000 : ℝ) ^ 5 := pow_le_pow_left₀ hx0 hx 5
  have hn2 : (0 : ℝ) ≤ x ^ 2 := by positivity
  have hn3 : (0 : ℝ) ≤ x ^ 3 := by positivity
  have hn5 : (0 : ℝ) ≤ x ^ 5 := by positivity
  norm_num at h2 h3 h5
  rw [abs_le]
  constructor <;> linarith

/-- `|(p²)′| ≤ 84` on the core (`(p²)′(s) = 2p(s)·s·G(s²)`, `|s| ≤ 0.5478`, `|G| ≤ 75`,
`0 ≤ p ≤ 1`). -/
theorem abs_deriv_pED_sq_le {s : ℝ} (hs : |s| ≤ lamStarEvenDyad12 / 2) :
    |2 * pED s * pED' s| ≤ 84 := by
  have hb : |s| ≤ 5478 / 10000 :=
    le_trans hs (by unfold lamStarEvenDyad12; norm_num)
  have hG := GED_abs_le (x := s ^ 2) (sq_nonneg s) (sq_le_of_coreED hs)
  set G : ℝ := 2 * (-402449 / 1000000 : ℝ) + 4 * (-142417 / 125000) * s ^ 2
      + 6 * (-16037751 / 1000000) * (s ^ 2) ^ 2 + 8 * (45473063 / 250000) * (s ^ 2) ^ 3
      + 12 * (-2194509137 / 1000000) * (s ^ 2) ^ 5 with hGdef
  have e : pED' s = s * G := by rw [hGdef]; unfold pED'; ring
  have hd : |pED' s| ≤ 42 := by
    rw [e, abs_mul]
    have h := mul_le_mul hb hG (abs_nonneg G) (by norm_num : (0 : ℝ) ≤ 5478 / 10000)
    linarith
  have hp := pED_nonneg_le_one hs
  have habs : |2 * pED s * pED' s| = 2 * pED s * |pED' s| := by
    rw [abs_mul, abs_of_nonneg (by linarith [hp.1] : (0 : ℝ) ≤ 2 * pED s)]
  rw [habs]
  have hmul : pED s * |pED' s| ≤ 1 * 42 :=
    mul_le_mul hp.2 hd (abs_nonneg _) zero_le_one
  linarith

/-- **`p²` is `84`-Lipschitz on the core** (mean value theorem). -/
theorem pED_sq_lip {x y : ℝ} (hx : |x| ≤ lamStarEvenDyad12 / 2)
    (hy : |y| ≤ lamStarEvenDyad12 / 2) : |pED y ^ 2 - pED x ^ 2| ≤ 84 * |y - x| := by
  have h := (convex_Icc (-(lamStarEvenDyad12 / 2))
      (lamStarEvenDyad12 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => pED s ^ 2) (f' := fun s => 2 * pED s * pED' s) (C := 84)
    (fun s _ => (hasDerivAt_pED_sq s).hasDerivWithinAt)
    (fun s hs => by rw [Real.norm_eq_abs]; exact abs_deriv_pED_sq_le (abs_le.mpr hs))
    (abs_le.mp hx) (abs_le.mp hy)
  simpa only [Real.norm_eq_abs] using h

theorem one_le_lamStarEvenDyad12 : (1 : ℝ) ≤ lamStarEvenDyad12 := by
  unfold lamStarEvenDyad12; norm_num

/-- the autocorrelation at the even/odd dyadic design, with `p = pED`, `b = λ'/2`. -/
theorem psi_vProfile_eq_pED (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) {α : ℝ} (h0 : 0 ≤ α) (hα : α ≤ 1) :
    psi (vProfile P) α
      = (∫ t in (α - lamStarEvenDyad12 / 2)..(lamStarEvenDyad12 / 2),
            pED t ^ 2 * pED (t - α) ^ 2) / (profMass P) ^ 2 := by
  rw [psi_vProfile_eq P h0 (by rw [hlam]; linarith [one_le_lamStarEvenDyad12]), hlam, hprof]
  simp_rw [eval_designProfileEvenDyad12]

/-- `profMass = sqPrimEvenDyad12(b) − sqPrimEvenDyad12(−b)` at the even/odd dyadic design. -/
theorem profMass_eq_evendyad12 (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) :
    profMass P = sqPrimEvenDyad12 (lamStarEvenDyad12 / 2)
      - sqPrimEvenDyad12 (-(lamStarEvenDyad12 / 2)) := by
  unfold profMass
  rw [hlam, hprof]
  simp_rw [designProfileEvenDyad12_eval]
  exact integral_sq_designProfileEvenDyad12 _ _

/-- **`ψ_{v_profile}(1) ≤ 0.0227`** (`= 0.0226880402…`). -/
theorem psiED_one_le (hP : P.Valid) (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) : psi (vProfile P) 1 ≤ 227 / 10000 := by
  rw [psi_vProfile_eq_pED hprof hlam zero_le_one le_rfl]
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  rw [div_le_iff₀ hM2, profMass_eq_evendyad12 hprof hlam]
  have hval : ∫ t in (1 - lamStarEvenDyad12 / 2)..(lamStarEvenDyad12 / 2),
        pED t ^ 2 * pED (t - 1) ^ 2
      = RED (lamStarEvenDyad12 / 2) - RED (1 - lamStarEvenDyad12 / 2) := by
    simp_rw [pED_sq_mul_pED_sq_eq]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_RED x)
      (rED_continuous.intervalIntegrable _ _)
  rw [hval]
  exact psi1ED_num

/-- **The Lipschitz bound** `ψ(α) ≤ ψ(1) + 6·(1 − α)` on `[0, 1]`. -/
theorem psiED_le_psi_one_add (hP : P.Valid) (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    psi (vProfile P) α ≤ psi (vProfile P) 1 + (6 : ℝ) * (1 - α) := by
  have hb1 : 1 - lamStarEvenDyad12 / 2 ≤ lamStarEvenDyad12 / 2 := by
    unfold lamStarEvenDyad12; norm_num
  have hbh : 1 / 2 < lamStarEvenDyad12 / 2 := by unfold lamStarEvenDyad12; norm_num
  have hbl : lamStarEvenDyad12 / 2 ≤ 1 := by unfold lamStarEvenDyad12; norm_num
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  have hcont : ∀ β : ℝ, Continuous fun t => pED t ^ 2 * pED (t - β) ^ 2 := by
    intro β
    have := pED_continuous
    fun_prop
  have hIα : ∀ a c : ℝ, IntervalIntegrable (fun t => pED t ^ 2 * pED (t - α) ^ 2) volume a c :=
    fun a c => (hcont α).intervalIntegrable a c
  have hI1 : ∀ a c : ℝ, IntervalIntegrable (fun t => pED t ^ 2 * pED (t - 1) ^ 2) volume a c :=
    fun a c => (hcont 1).intervalIntegrable a c
  rw [psi_vProfile_eq_pED hprof hlam h0 h1, psi_vProfile_eq_pED hprof hlam zero_le_one le_rfl]
  have hsplit : ∫ t in (α - lamStarEvenDyad12 / 2)..(lamStarEvenDyad12 / 2),
        pED t ^ 2 * pED (t - α) ^ 2
      = (∫ t in (α - lamStarEvenDyad12 / 2)..(1 - lamStarEvenDyad12 / 2),
            pED t ^ 2 * pED (t - α) ^ 2)
        + ∫ t in (1 - lamStarEvenDyad12 / 2)..(lamStarEvenDyad12 / 2),
            pED t ^ 2 * pED (t - α) ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hIα _ _) (hIα _ _)).symm
  have hT1 : ∫ t in (α - lamStarEvenDyad12 / 2)..(1 - lamStarEvenDyad12 / 2),
        pED t ^ 2 * pED (t - α) ^ 2 ≤ 1 * (1 - α) := by
    have hbd : ∀ x ∈ Set.uIoc (α - lamStarEvenDyad12 / 2) (1 - lamStarEvenDyad12 / 2),
        ‖pED x ^ 2 * pED (x - α) ^ 2‖ ≤ 1 := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hA := pED_nonneg_le_one (t := x) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hB := pED_nonneg_le_one (t := x - α) (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : pED x ^ 2 * pED (x - α) ^ 2 ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ hA.1 hA.2) (pow_le_one₀ hB.1 hB.2) (by positivity) zero_le_one
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs,
      show (1 - lamStarEvenDyad12 / 2) - (α - lamStarEvenDyad12 / 2) = 1 - α by ring,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - α by linarith)] at this
    exact (le_abs_self _).trans this
  have hI2 : ∫ t in (1 - lamStarEvenDyad12 / 2)..(lamStarEvenDyad12 / 2), pED t ^ 2
      = sqPrimEvenDyad12 (lamStarEvenDyad12 / 2)
        - sqPrimEvenDyad12 (1 - lamStarEvenDyad12 / 2) := by
    unfold pED
    exact integral_sq_designProfileEvenDyad12 _ _
  have hT2 : (∫ t in (1 - lamStarEvenDyad12 / 2)..(lamStarEvenDyad12 / 2),
          pED t ^ 2 * pED (t - α) ^ 2)
        - ∫ t in (1 - lamStarEvenDyad12 / 2)..(lamStarEvenDyad12 / 2),
          pED t ^ 2 * pED (t - 1) ^ 2
      ≤ (84 * (1 - α)) * (sqPrimEvenDyad12 (lamStarEvenDyad12 / 2)
          - sqPrimEvenDyad12 (1 - lamStarEvenDyad12 / 2)) := by
    rw [← intervalIntegral.integral_sub (hIα _ _) (hI1 _ _), ← hI2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hb1 ((hIα _ _).sub (hI1 _ _))
      (((pED_continuous.pow 2).const_mul _).intervalIntegrable _ _)
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hlip := pED_sq_lip (x := x - 1) (y := x - α)
      (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [show (x - α) - (x - 1) = 1 - α by ring,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - α by linarith)] at hlip
    have hd : pED (x - α) ^ 2 - pED (x - 1) ^ 2 ≤ 84 * (1 - α) := (le_abs_self _).trans hlip
    have hsq : 0 ≤ pED x ^ 2 := sq_nonneg _
    calc pED x ^ 2 * pED (x - α) ^ 2 - pED x ^ 2 * pED (x - 1) ^ 2
        = pED x ^ 2 * (pED (x - α) ^ 2 - pED (x - 1) ^ 2) := by ring
      _ ≤ pED x ^ 2 * (84 * (1 - α)) := mul_le_mul_of_nonneg_left hd hsq
      _ = 84 * (1 - α) * pED x ^ 2 := by ring
  have hD := cED_num
  rw [← profMass_eq_evendyad12 hprof hlam] at hD
  have hD' := mul_le_mul_of_nonneg_left hD (sub_nonneg.2 h1)
  rw [hsplit, div_le_iff₀ hM2, add_mul, div_mul_cancel₀ _ hM2.ne']
  nlinarith [hT1, hT2, hD']

theorem CfamEvenDyadic_le : CfamEvenDyadic ≤ 4 * 3141593 ^ 4 / (27 * 10 ^ 24) := by
  have h := C_dyad_le
  unfold CfamEvenDyadic
  push_cast at h
  linarith

/-- **`ZoneLipschitzData Family.evenDyadic r ε`, certified**: `ψ₁ = 0.0227`, `c = 6`,
`2(C − 1)ψ₁ ≤ 2·13.430983·0.0227 = 0.609767 < 0.6151116 = sZoneEvenDyadic` (margin `0.0053`). -/
theorem zoneLipschitzData_evenDyadic (r ε : ℝ) : ZoneLipschitzData Family.evenDyadic r ε := by
  refine ⟨227 / 10000, 6, by norm_num, ?_, ?_⟩
  · have := CfamEvenDyadic_le
    simp only [Family.Cconst, Family.sZoneF]
    unfold sZoneEvenDyadic
    linarith
  · intro Qn P hdes α h0 h1
    obtain ⟨hP, -, -, hlam, -, -, -, -, -, -, -, hprof⟩ := hdes
    have hlam' : P.lam = lamStarEvenDyad12 := hlam
    have hprof' : P.prof = designProfileEvenDyad12 := hprof
    have h := psiED_le_psi_one_add hP hprof' hlam' h0 h1
    have h' := psiED_one_le hP hprof' hlam'
    linarith

/-- **`ZoneLipschitzData Family.oddDyadic r ε`** — the same certificate (odd and even share
`Cconst`, `sZoneF`, `lamStar` and `designProfile`). -/
theorem zoneLipschitzData_oddDyadic (r ε : ℝ) : ZoneLipschitzData Family.oddDyadic r ε := by
  refine ⟨227 / 10000, 6, by norm_num, ?_, ?_⟩
  · have := CfamEvenDyadic_le
    simp only [Family.Cconst, Family.sZoneF]
    unfold sZoneEvenDyadic
    linarith
  · intro Qn P hdes α h0 h1
    obtain ⟨hP, -, -, hlam, -, -, -, -, -, -, -, hprof⟩ := hdes
    have hlam' : P.lam = lamStarEvenDyad12 := hlam
    have hprof' : P.prof = designProfileEvenDyad12 := hprof
    have h := psiED_le_psi_one_add hP hprof' hlam' h0 h1
    have h' := psiED_one_le hP hprof' hlam'
    linarith


/-! ## §8. The even/odd `q ≤ Q` parity family of Corollary 3 (`C = π⁴/9`, secant
`sZoneEvenQ = 0.5921332`).

The route of §7 at the other refitted parity design (`designProfileEvenQ10`, degree 10,
`λ' = lamStarEvenQ10 = 1.1289788821`, support `b = λ'/2 = 0.56448944105`): `p(t)²p(t−1)²` is the
degree-40 `rEQ` and `ψ(1) = 0.0299319579… ≤ 0.02994`, against which

    2(C − 1)ψ₁ ≤ 2·9.824·0.02994 = 0.588261 < 0.5921332 = sZoneEvenQ   (margin 0.0039),

`C = π⁴/9 ≤ 2·5.412` (`C_qQ_le`). Again the Lipschitz constant is the crude one
(`|(p²)′| ≤ 68` against a true sup of `9.41`), whence `c = 7 ≥ (1 + 68·I₂)/M² = 6.07`. -/

/-- `p(t)` for the even/odd `q ≤ Q` REFIT design, as an explicit function. -/
def pEQ (t : ℝ) : ℝ :=
  1 + (-305071 / 1000000) * t ^ 2 + (-19204 / 3125) * t ^ 4 + (10580251 / 200000) * t ^ 6
    + (-4540317 / 50000) * t ^ 8 + (-262238203 / 1000000) * t ^ 10

theorem eval_designProfileEvenQ10 (t : ℝ) : designProfileEvenQ10.eval t = pEQ t :=
  designProfileEvenQ10_eval t

theorem pEQ_continuous : Continuous pEQ := by unfold pEQ; fun_prop

/-- `r(t) = p(t)²p(t−1)²` expanded (degree 40; coefficients exact). -/
def rEQ (t : ℝ) : ℝ :=
    (93387472197262321 / 1000000000000 : ℝ) * t ^ 0
    + (-467041276880878999 / 250000000000 : ℝ) * t ^ 1
    + (8795049242821847407470209 / 500000000000000000 : ℝ) * t ^ 2
    + (-12953740662676382718396071 / 125000000000000000 : ℝ) * t ^ 3
    + (426904701314925015522667222870161 / 1000000000000000000000000 : ℝ) * t ^ 4
    + (-323129629954550454713391530723959 / 250000000000000000000000 : ℝ) * t ^ 5
    + (1452524706407023356271087692726741 / 500000000000000000000000 : ℝ) * t ^ 6
    + (-1172479113695394200064063561742391 / 250000000000000000000000 : ℝ) * t ^ 7
    + (4982147199422793762374943940100221 / 1000000000000000000000000 : ℝ) * t ^ 8
    + (-15338922196335649363521913834563 / 3906250000000000000000 : ℝ) * t ^ 9
    + (185827650594921876588822046881231 / 15625000000000000000000 : ℝ) * t ^ 10
    + (-3415917479854277343609675644924657 / 62500000000000000000000 : ℝ) * t ^ 11
    + (73080671724431454041590415969508043 / 500000000000000000000000 : ℝ) * t ^ 12
    + (-12658396914974103436141354731015511 / 62500000000000000000000 : ℝ) * t ^ 13
    + (-3012684354586159404949770855112583 / 62500000000000000000000 : ℝ) * t ^ 14
    + (29981094402934977897905993129951137 / 31250000000000000000000 : ℝ) * t ^ 15
    + (-1233821927380037306063945257826677509 / 500000000000000000000000 : ℝ) * t ^ 16
    + (440910145198738401971441430371129729 / 125000000000000000000000 : ℝ) * t ^ 17
    + (-668769704260003839548078988359966039 / 250000000000000000000000 : ℝ) * t ^ 18
    + (97071501816891297827675110026145589 / 125000000000000000000000 : ℝ) * t ^ 19
    + (-4322089597858432935704322378469458481 / 1000000000000000000000000 : ℝ) * t ^ 20
    + (5954542797320057398315237743183832459 / 250000000000000000000000 : ℝ) * t ^ 21
    + (-31078632941508462259157811301226219681 / 500000000000000000000000 : ℝ) * t ^ 22
    + (24159782421342799245224287479135248683 / 250000000000000000000000 : ℝ) * t ^ 23
    + (-71119569488383584936334517031196632961 / 1000000000000000000000000 : ℝ) * t ^ 24
    + (-10353706895487419758560672337812791599 / 125000000000000000000000 : ℝ) * t ^ 25
    + (99114089915328702041067392821612505669 / 250000000000000000000000 : ℝ) * t ^ 26
    + (-102268688485688948903198842868859090343 / 125000000000000000000000 : ℝ) * t ^ 27
    + (24304350414017026534722135556301490743 / 20000000000000000000000 : ℝ) * t ^ 28
    + (-35926997762676597228107244893049078943 / 25000000000000000000000 : ℝ) * t ^ 29
    + (14019662598426764788464765475487170633 / 10000000000000000000000 : ℝ) * t ^ 30
    + (-142910397358993333268917400302596079391 / 125000000000000000000000 : ℝ) * t ^ 31
    + (390552293333009391708248837128652860949 / 500000000000000000000000 : ℝ) * t ^ 32
    + (-11124224550633568313316512112555266663 / 25000000000000000000000 : ℝ) * t ^ 33
    + (2091210026845056420824920328897915941 / 10000000000000000000000 : ℝ) * t ^ 34
    + (-9964957113847169049319913322406138233 / 125000000000000000000000 : ℝ) * t ^ 35
    + (4807148301241285100098143725087041757 / 200000000000000000000000 : ℝ) * t ^ 36
    + (-275784842376916680329287704543823101 / 50000000000000000000000 : ℝ) * t ^ 37
    + (90509039803501121333084119541526811 / 100000000000000000000000 : ℝ) * t ^ 38
    + (-4729158184261894512834100656685681 / 50000000000000000000000 : ℝ) * t ^ 39
    + (4729158184261894512834100656685681 / 1000000000000000000000000 : ℝ) * t ^ 40

theorem pEQ_sq_mul_pEQ_sq_eq (t : ℝ) : pEQ t ^ 2 * pEQ (t - 1) ^ 2 = rEQ t := by
  unfold pEQ rEQ; ring

/-- the antiderivative of `rEQ`. -/
def REQ (t : ℝ) : ℝ :=
    (93387472197262321 / 1000000000000 : ℝ) * t ^ 1 / 1
    + (-467041276880878999 / 250000000000 : ℝ) * t ^ 2 / 2
    + (8795049242821847407470209 / 500000000000000000 : ℝ) * t ^ 3 / 3
    + (-12953740662676382718396071 / 125000000000000000 : ℝ) * t ^ 4 / 4
    + (426904701314925015522667222870161 / 1000000000000000000000000 : ℝ) * t ^ 5 / 5
    + (-323129629954550454713391530723959 / 250000000000000000000000 : ℝ) * t ^ 6 / 6
    + (1452524706407023356271087692726741 / 500000000000000000000000 : ℝ) * t ^ 7 / 7
    + (-1172479113695394200064063561742391 / 250000000000000000000000 : ℝ) * t ^ 8 / 8
    + (4982147199422793762374943940100221 / 1000000000000000000000000 : ℝ) * t ^ 9 / 9
    + (-15338922196335649363521913834563 / 3906250000000000000000 : ℝ) * t ^ 10 / 10
    + (185827650594921876588822046881231 / 15625000000000000000000 : ℝ) * t ^ 11 / 11
    + (-3415917479854277343609675644924657 / 62500000000000000000000 : ℝ) * t ^ 12 / 12
    + (73080671724431454041590415969508043 / 500000000000000000000000 : ℝ) * t ^ 13 / 13
    + (-12658396914974103436141354731015511 / 62500000000000000000000 : ℝ) * t ^ 14 / 14
    + (-3012684354586159404949770855112583 / 62500000000000000000000 : ℝ) * t ^ 15 / 15
    + (29981094402934977897905993129951137 / 31250000000000000000000 : ℝ) * t ^ 16 / 16
    + (-1233821927380037306063945257826677509 / 500000000000000000000000 : ℝ) * t ^ 17 / 17
    + (440910145198738401971441430371129729 / 125000000000000000000000 : ℝ) * t ^ 18 / 18
    + (-668769704260003839548078988359966039 / 250000000000000000000000 : ℝ) * t ^ 19 / 19
    + (97071501816891297827675110026145589 / 125000000000000000000000 : ℝ) * t ^ 20 / 20
    + (-4322089597858432935704322378469458481 / 1000000000000000000000000 : ℝ) * t ^ 21 / 21
    + (5954542797320057398315237743183832459 / 250000000000000000000000 : ℝ) * t ^ 22 / 22
    + (-31078632941508462259157811301226219681 / 500000000000000000000000 : ℝ) * t ^ 23 / 23
    + (24159782421342799245224287479135248683 / 250000000000000000000000 : ℝ) * t ^ 24 / 24
    + (-71119569488383584936334517031196632961 / 1000000000000000000000000 : ℝ) * t ^ 25 / 25
    + (-10353706895487419758560672337812791599 / 125000000000000000000000 : ℝ) * t ^ 26 / 26
    + (99114089915328702041067392821612505669 / 250000000000000000000000 : ℝ) * t ^ 27 / 27
    + (-102268688485688948903198842868859090343 / 125000000000000000000000 : ℝ) * t ^ 28 / 28
    + (24304350414017026534722135556301490743 / 20000000000000000000000 : ℝ) * t ^ 29 / 29
    + (-35926997762676597228107244893049078943 / 25000000000000000000000 : ℝ) * t ^ 30 / 30
    + (14019662598426764788464765475487170633 / 10000000000000000000000 : ℝ) * t ^ 31 / 31
    + (-142910397358993333268917400302596079391 / 125000000000000000000000 : ℝ) * t ^ 32 / 32
    + (390552293333009391708248837128652860949 / 500000000000000000000000 : ℝ) * t ^ 33 / 33
    + (-11124224550633568313316512112555266663 / 25000000000000000000000 : ℝ) * t ^ 34 / 34
    + (2091210026845056420824920328897915941 / 10000000000000000000000 : ℝ) * t ^ 35 / 35
    + (-9964957113847169049319913322406138233 / 125000000000000000000000 : ℝ) * t ^ 36 / 36
    + (4807148301241285100098143725087041757 / 200000000000000000000000 : ℝ) * t ^ 37 / 37
    + (-275784842376916680329287704543823101 / 50000000000000000000000 : ℝ) * t ^ 38 / 38
    + (90509039803501121333084119541526811 / 100000000000000000000000 : ℝ) * t ^ 39 / 39
    + (-4729158184261894512834100656685681 / 50000000000000000000000 : ℝ) * t ^ 40 / 40
    + (4729158184261894512834100656685681 / 1000000000000000000000000 : ℝ) * t ^ 41 / 41

theorem hasDerivAt_REQ (t : ℝ) : HasDerivAt REQ (rEQ t) t := by
  unfold REQ rEQ
  have h0 := ((hasDerivAt_pow 1 t).const_mul (93387472197262321 / 1000000000000 : ℝ)).div_const 1
  have h1 := ((hasDerivAt_pow 2 t).const_mul (-467041276880878999 / 250000000000 : ℝ)).div_const 2
  have h2 := ((hasDerivAt_pow 3 t).const_mul (8795049242821847407470209 / 500000000000000000 : ℝ)).div_const 3
  have h3 := ((hasDerivAt_pow 4 t).const_mul (-12953740662676382718396071 / 125000000000000000 : ℝ)).div_const 4
  have h4 := ((hasDerivAt_pow 5 t).const_mul (426904701314925015522667222870161 / 1000000000000000000000000 : ℝ)).div_const 5
  have h5 := ((hasDerivAt_pow 6 t).const_mul (-323129629954550454713391530723959 / 250000000000000000000000 : ℝ)).div_const 6
  have h6 := ((hasDerivAt_pow 7 t).const_mul (1452524706407023356271087692726741 / 500000000000000000000000 : ℝ)).div_const 7
  have h7 := ((hasDerivAt_pow 8 t).const_mul (-1172479113695394200064063561742391 / 250000000000000000000000 : ℝ)).div_const 8
  have h8 := ((hasDerivAt_pow 9 t).const_mul (4982147199422793762374943940100221 / 1000000000000000000000000 : ℝ)).div_const 9
  have h9 := ((hasDerivAt_pow 10 t).const_mul (-15338922196335649363521913834563 / 3906250000000000000000 : ℝ)).div_const 10
  have h10 := ((hasDerivAt_pow 11 t).const_mul (185827650594921876588822046881231 / 15625000000000000000000 : ℝ)).div_const 11
  have h11 := ((hasDerivAt_pow 12 t).const_mul (-3415917479854277343609675644924657 / 62500000000000000000000 : ℝ)).div_const 12
  have h12 := ((hasDerivAt_pow 13 t).const_mul (73080671724431454041590415969508043 / 500000000000000000000000 : ℝ)).div_const 13
  have h13 := ((hasDerivAt_pow 14 t).const_mul (-12658396914974103436141354731015511 / 62500000000000000000000 : ℝ)).div_const 14
  have h14 := ((hasDerivAt_pow 15 t).const_mul (-3012684354586159404949770855112583 / 62500000000000000000000 : ℝ)).div_const 15
  have h15 := ((hasDerivAt_pow 16 t).const_mul (29981094402934977897905993129951137 / 31250000000000000000000 : ℝ)).div_const 16
  have h16 := ((hasDerivAt_pow 17 t).const_mul (-1233821927380037306063945257826677509 / 500000000000000000000000 : ℝ)).div_const 17
  have h17 := ((hasDerivAt_pow 18 t).const_mul (440910145198738401971441430371129729 / 125000000000000000000000 : ℝ)).div_const 18
  have h18 := ((hasDerivAt_pow 19 t).const_mul (-668769704260003839548078988359966039 / 250000000000000000000000 : ℝ)).div_const 19
  have h19 := ((hasDerivAt_pow 20 t).const_mul (97071501816891297827675110026145589 / 125000000000000000000000 : ℝ)).div_const 20
  have h20 := ((hasDerivAt_pow 21 t).const_mul (-4322089597858432935704322378469458481 / 1000000000000000000000000 : ℝ)).div_const 21
  have h21 := ((hasDerivAt_pow 22 t).const_mul (5954542797320057398315237743183832459 / 250000000000000000000000 : ℝ)).div_const 22
  have h22 := ((hasDerivAt_pow 23 t).const_mul (-31078632941508462259157811301226219681 / 500000000000000000000000 : ℝ)).div_const 23
  have h23 := ((hasDerivAt_pow 24 t).const_mul (24159782421342799245224287479135248683 / 250000000000000000000000 : ℝ)).div_const 24
  have h24 := ((hasDerivAt_pow 25 t).const_mul (-71119569488383584936334517031196632961 / 1000000000000000000000000 : ℝ)).div_const 25
  have h25 := ((hasDerivAt_pow 26 t).const_mul (-10353706895487419758560672337812791599 / 125000000000000000000000 : ℝ)).div_const 26
  have h26 := ((hasDerivAt_pow 27 t).const_mul (99114089915328702041067392821612505669 / 250000000000000000000000 : ℝ)).div_const 27
  have h27 := ((hasDerivAt_pow 28 t).const_mul (-102268688485688948903198842868859090343 / 125000000000000000000000 : ℝ)).div_const 28
  have h28 := ((hasDerivAt_pow 29 t).const_mul (24304350414017026534722135556301490743 / 20000000000000000000000 : ℝ)).div_const 29
  have h29 := ((hasDerivAt_pow 30 t).const_mul (-35926997762676597228107244893049078943 / 25000000000000000000000 : ℝ)).div_const 30
  have h30 := ((hasDerivAt_pow 31 t).const_mul (14019662598426764788464765475487170633 / 10000000000000000000000 : ℝ)).div_const 31
  have h31 := ((hasDerivAt_pow 32 t).const_mul (-142910397358993333268917400302596079391 / 125000000000000000000000 : ℝ)).div_const 32
  have h32 := ((hasDerivAt_pow 33 t).const_mul (390552293333009391708248837128652860949 / 500000000000000000000000 : ℝ)).div_const 33
  have h33 := ((hasDerivAt_pow 34 t).const_mul (-11124224550633568313316512112555266663 / 25000000000000000000000 : ℝ)).div_const 34
  have h34 := ((hasDerivAt_pow 35 t).const_mul (2091210026845056420824920328897915941 / 10000000000000000000000 : ℝ)).div_const 35
  have h35 := ((hasDerivAt_pow 36 t).const_mul (-9964957113847169049319913322406138233 / 125000000000000000000000 : ℝ)).div_const 36
  have h36 := ((hasDerivAt_pow 37 t).const_mul (4807148301241285100098143725087041757 / 200000000000000000000000 : ℝ)).div_const 37
  have h37 := ((hasDerivAt_pow 38 t).const_mul (-275784842376916680329287704543823101 / 50000000000000000000000 : ℝ)).div_const 38
  have h38 := ((hasDerivAt_pow 39 t).const_mul (90509039803501121333084119541526811 / 100000000000000000000000 : ℝ)).div_const 39
  have h39 := ((hasDerivAt_pow 40 t).const_mul (-4729158184261894512834100656685681 / 50000000000000000000000 : ℝ)).div_const 40
  have h40 := ((hasDerivAt_pow 41 t).const_mul (4729158184261894512834100656685681 / 1000000000000000000000000 : ℝ)).div_const 41
  have h := ((((((((((((((((((((((((((((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15).add h16).add h17).add h18).add h19).add h20).add h21).add h22).add h23).add h24).add h25).add h26).add h27).add h28).add h29).add h30).add h31).add h32).add h33).add h34).add h35).add h36).add h37).add h38).add h39).add h40)
  exact h.congr_deriv (by push_cast; ring)


theorem rEQ_continuous : Continuous rEQ := by unfold rEQ; fun_prop

set_option maxHeartbeats 1000000 in
/-- `∫_{1−b}^{b} p(t)²p(t−1)² = R(b) − R(1−b) ≤ 0.02994·M²` (exact rationals;
`ψ(1) = 0.0299319579…`). -/
theorem psi1EQ_num :
    REQ (lamStarEvenQ10 / 2) - REQ (1 - lamStarEvenQ10 / 2)
      ≤ (2994 / 100000) * (sqPrimEvenQ10 (lamStarEvenQ10 / 2)
          - sqPrimEvenQ10 (-(lamStarEvenQ10 / 2))) ^ 2 := by
  unfold REQ sqPrimEvenQ10 lamStarEvenQ10
  norm_num

set_option maxHeartbeats 1000000 in
/-- `1 + 68·∫_{1−b}^{b} p² ≤ 7·M²` (`(1 + 68·I₂)/M² = 6.0732`). -/
theorem cEQ_num :
    1 + (68 : ℝ) * (sqPrimEvenQ10 (lamStarEvenQ10 / 2)
          - sqPrimEvenQ10 (1 - lamStarEvenQ10 / 2))
      ≤ (7 : ℝ) * (sqPrimEvenQ10 (lamStarEvenQ10 / 2)
          - sqPrimEvenQ10 (-(lamStarEvenQ10 / 2))) ^ 2 := by
  unfold sqPrimEvenQ10 lamStarEvenQ10
  norm_num

/-- `p′`. -/
def pEQ' (t : ℝ) : ℝ :=
  2 * (-305071 / 1000000) * t + 4 * (-19204 / 3125) * t ^ 3
    + 6 * (10580251 / 200000) * t ^ 5 + 8 * (-4540317 / 50000) * t ^ 7
    + 10 * (-262238203 / 1000000) * t ^ 9

theorem hasDerivAt_pEQ (t : ℝ) : HasDerivAt pEQ (pEQ' t) t := by
  unfold pEQ pEQ'
  have h2 := (hasDerivAt_pow 2 t).const_mul (-305071 / 1000000 : ℝ)
  have h4 := (hasDerivAt_pow 4 t).const_mul (-19204 / 3125 : ℝ)
  have h6 := (hasDerivAt_pow 6 t).const_mul (10580251 / 200000 : ℝ)
  have h8 := (hasDerivAt_pow 8 t).const_mul (-4540317 / 50000 : ℝ)
  have h10 := (hasDerivAt_pow 10 t).const_mul (-262238203 / 1000000 : ℝ)
  have h := ((((h2.const_add 1).add h4).add h6).add h8).add h10
  exact h.congr_deriv (by push_cast; ring)

theorem hasDerivAt_pEQ_sq (t : ℝ) :
    HasDerivAt (fun s => pEQ s ^ 2) (2 * pEQ t * pEQ' t) t := by
  have h := (hasDerivAt_pEQ t).fun_pow 2
  exact h.congr_deriv (by push_cast; ring)

/-- `|t| ≤ λ'/2` gives `t² ≤ 6373/20000` (as in `profileQ_evenq10`). -/
theorem sq_le_of_coreEQ {t : ℝ} (ht : |t| ≤ lamStarEvenQ10 / 2) : t ^ 2 ≤ 6373 / 20000 := by
  have h1 : |t| ^ 2 ≤ (lamStarEvenQ10 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at h1
  unfold lamStarEvenQ10 at h1
  norm_num at h1
  linarith

/-- `0 ≤ p ≤ 1` on the core (from `profileQ_evenq10`). -/
theorem pEQ_nonneg_le_one {t : ℝ} (ht : |t| ≤ lamStarEvenQ10 / 2) :
    0 ≤ pEQ t ∧ pEQ t ≤ 1 := by
  have h1 := profileQ_evenq10.bulk t ht
  have h2 := profileQ_evenq10.le_one t ht
  rw [eval_designProfileEvenQ10] at h1 h2
  exact ⟨by linarith, h2⟩

/-- `|G| ≤ 59` on `[0, 0.31865]`, `G(x) = 2d₂ + 4d₄x + 6d₆x² + 8d₈x³ + 10d₁₀x⁴`, so that
`p′(s) = s·G(s²)` (crude termwise bound; `G ∈ [−58.99, 32.23]`). -/
theorem GEQ_abs_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 6373 / 20000) :
    |2 * (-305071 / 1000000 : ℝ) + 4 * (-19204 / 3125) * x
      + 6 * (10580251 / 200000) * x ^ 2 + 8 * (-4540317 / 50000) * x ^ 3
      + 10 * (-262238203 / 1000000) * x ^ 4| ≤ 59 := by
  have h2 : x ^ 2 ≤ (6373 / 20000 : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have h3 : x ^ 3 ≤ (6373 / 20000 : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx 3
  have h4 : x ^ 4 ≤ (6373 / 20000 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hx 4
  have hn2 : (0 : ℝ) ≤ x ^ 2 := by positivity
  have hn3 : (0 : ℝ) ≤ x ^ 3 := by positivity
  have hn4 : (0 : ℝ) ≤ x ^ 4 := by positivity
  norm_num at h2 h3 h4
  rw [abs_le]
  constructor <;> linarith

/-- `|(p²)′| ≤ 68` on the core (`|s| ≤ 0.56449`, `|G| ≤ 59`, `0 ≤ p ≤ 1`). -/
theorem abs_deriv_pEQ_sq_le {s : ℝ} (hs : |s| ≤ lamStarEvenQ10 / 2) :
    |2 * pEQ s * pEQ' s| ≤ 68 := by
  have hb : |s| ≤ 56449 / 100000 := le_trans hs (by unfold lamStarEvenQ10; norm_num)
  have hG := GEQ_abs_le (x := s ^ 2) (sq_nonneg s) (sq_le_of_coreEQ hs)
  set G : ℝ := 2 * (-305071 / 1000000 : ℝ) + 4 * (-19204 / 3125) * s ^ 2
      + 6 * (10580251 / 200000) * (s ^ 2) ^ 2 + 8 * (-4540317 / 50000) * (s ^ 2) ^ 3
      + 10 * (-262238203 / 1000000) * (s ^ 2) ^ 4 with hGdef
  have e : pEQ' s = s * G := by rw [hGdef]; unfold pEQ'; ring
  have hd : |pEQ' s| ≤ 34 := by
    rw [e, abs_mul]
    have h := mul_le_mul hb hG (abs_nonneg G) (by norm_num : (0 : ℝ) ≤ 56449 / 100000)
    linarith
  have hp := pEQ_nonneg_le_one hs
  have habs : |2 * pEQ s * pEQ' s| = 2 * pEQ s * |pEQ' s| := by
    rw [abs_mul, abs_of_nonneg (by linarith [hp.1] : (0 : ℝ) ≤ 2 * pEQ s)]
  rw [habs]
  have hmul : pEQ s * |pEQ' s| ≤ 1 * 34 :=
    mul_le_mul hp.2 hd (abs_nonneg _) zero_le_one
  linarith

/-- **`p²` is `68`-Lipschitz on the core** (mean value theorem). -/
theorem pEQ_sq_lip {x y : ℝ} (hx : |x| ≤ lamStarEvenQ10 / 2)
    (hy : |y| ≤ lamStarEvenQ10 / 2) : |pEQ y ^ 2 - pEQ x ^ 2| ≤ 68 * |y - x| := by
  have h := (convex_Icc (-(lamStarEvenQ10 / 2))
      (lamStarEvenQ10 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => pEQ s ^ 2) (f' := fun s => 2 * pEQ s * pEQ' s) (C := 68)
    (fun s _ => (hasDerivAt_pEQ_sq s).hasDerivWithinAt)
    (fun s hs => by rw [Real.norm_eq_abs]; exact abs_deriv_pEQ_sq_le (abs_le.mpr hs))
    (abs_le.mp hx) (abs_le.mp hy)
  simpa only [Real.norm_eq_abs] using h

theorem one_le_lamStarEvenQ10 : (1 : ℝ) ≤ lamStarEvenQ10 := by
  unfold lamStarEvenQ10; norm_num

/-- the autocorrelation at the even/odd `q ≤ Q` design, with `p = pEQ`, `b = λ'/2`. -/
theorem psi_vProfile_eq_pEQ (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) {α : ℝ} (h0 : 0 ≤ α) (hα : α ≤ 1) :
    psi (vProfile P) α
      = (∫ t in (α - lamStarEvenQ10 / 2)..(lamStarEvenQ10 / 2),
            pEQ t ^ 2 * pEQ (t - α) ^ 2) / (profMass P) ^ 2 := by
  rw [psi_vProfile_eq P h0 (by rw [hlam]; linarith [one_le_lamStarEvenQ10]), hlam, hprof]
  simp_rw [eval_designProfileEvenQ10]

/-- `profMass = sqPrimEvenQ10(b) − sqPrimEvenQ10(−b)` at the even/odd `q ≤ Q` design. -/
theorem profMass_eq_evenq10 (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) :
    profMass P = sqPrimEvenQ10 (lamStarEvenQ10 / 2)
      - sqPrimEvenQ10 (-(lamStarEvenQ10 / 2)) := by
  unfold profMass
  rw [hlam, hprof]
  simp_rw [designProfileEvenQ10_eval]
  exact integral_sq_designProfileEvenQ10 _ _

/-- **`ψ_{v_profile}(1) ≤ 0.02994`** (`= 0.0299319579…`). -/
theorem psiEQ_one_le (hP : P.Valid) (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) : psi (vProfile P) 1 ≤ 2994 / 100000 := by
  rw [psi_vProfile_eq_pEQ hprof hlam zero_le_one le_rfl]
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  rw [div_le_iff₀ hM2, profMass_eq_evenq10 hprof hlam]
  have hval : ∫ t in (1 - lamStarEvenQ10 / 2)..(lamStarEvenQ10 / 2),
        pEQ t ^ 2 * pEQ (t - 1) ^ 2
      = REQ (lamStarEvenQ10 / 2) - REQ (1 - lamStarEvenQ10 / 2) := by
    simp_rw [pEQ_sq_mul_pEQ_sq_eq]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_REQ x)
      (rEQ_continuous.intervalIntegrable _ _)
  rw [hval]
  exact psi1EQ_num

/-- **The Lipschitz bound** `ψ(α) ≤ ψ(1) + 7·(1 − α)` on `[0, 1]`. -/
theorem psiEQ_le_psi_one_add (hP : P.Valid) (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    psi (vProfile P) α ≤ psi (vProfile P) 1 + (7 : ℝ) * (1 - α) := by
  have hb1 : 1 - lamStarEvenQ10 / 2 ≤ lamStarEvenQ10 / 2 := by
    unfold lamStarEvenQ10; norm_num
  have hbh : 1 / 2 < lamStarEvenQ10 / 2 := by unfold lamStarEvenQ10; norm_num
  have hbl : lamStarEvenQ10 / 2 ≤ 1 := by unfold lamStarEvenQ10; norm_num
  have hM : 0 < profMass P := profMass_pos hP
  have hM2 : 0 < (profMass P) ^ 2 := by positivity
  have hcont : ∀ β : ℝ, Continuous fun t => pEQ t ^ 2 * pEQ (t - β) ^ 2 := by
    intro β
    have := pEQ_continuous
    fun_prop
  have hIα : ∀ a c : ℝ, IntervalIntegrable (fun t => pEQ t ^ 2 * pEQ (t - α) ^ 2) volume a c :=
    fun a c => (hcont α).intervalIntegrable a c
  have hI1 : ∀ a c : ℝ, IntervalIntegrable (fun t => pEQ t ^ 2 * pEQ (t - 1) ^ 2) volume a c :=
    fun a c => (hcont 1).intervalIntegrable a c
  rw [psi_vProfile_eq_pEQ hprof hlam h0 h1, psi_vProfile_eq_pEQ hprof hlam zero_le_one le_rfl]
  have hsplit : ∫ t in (α - lamStarEvenQ10 / 2)..(lamStarEvenQ10 / 2),
        pEQ t ^ 2 * pEQ (t - α) ^ 2
      = (∫ t in (α - lamStarEvenQ10 / 2)..(1 - lamStarEvenQ10 / 2),
            pEQ t ^ 2 * pEQ (t - α) ^ 2)
        + ∫ t in (1 - lamStarEvenQ10 / 2)..(lamStarEvenQ10 / 2),
            pEQ t ^ 2 * pEQ (t - α) ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals (hIα _ _) (hIα _ _)).symm
  have hT1 : ∫ t in (α - lamStarEvenQ10 / 2)..(1 - lamStarEvenQ10 / 2),
        pEQ t ^ 2 * pEQ (t - α) ^ 2 ≤ 1 * (1 - α) := by
    have hbd : ∀ x ∈ Set.uIoc (α - lamStarEvenQ10 / 2) (1 - lamStarEvenQ10 / 2),
        ‖pEQ x ^ 2 * pEQ (x - α) ^ 2‖ ≤ 1 := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hA := pEQ_nonneg_le_one (t := x) (abs_le.mpr ⟨by linarith, by linarith⟩)
      have hB := pEQ_nonneg_le_one (t := x - α) (abs_le.mpr ⟨by linarith, by linarith⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : pEQ x ^ 2 * pEQ (x - α) ^ 2 ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ hA.1 hA.2) (pow_le_one₀ hB.1 hB.2) (by positivity) zero_le_one
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs,
      show (1 - lamStarEvenQ10 / 2) - (α - lamStarEvenQ10 / 2) = 1 - α by ring,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - α by linarith)] at this
    exact (le_abs_self _).trans this
  have hI2 : ∫ t in (1 - lamStarEvenQ10 / 2)..(lamStarEvenQ10 / 2), pEQ t ^ 2
      = sqPrimEvenQ10 (lamStarEvenQ10 / 2) - sqPrimEvenQ10 (1 - lamStarEvenQ10 / 2) := by
    unfold pEQ
    exact integral_sq_designProfileEvenQ10 _ _
  have hT2 : (∫ t in (1 - lamStarEvenQ10 / 2)..(lamStarEvenQ10 / 2),
          pEQ t ^ 2 * pEQ (t - α) ^ 2)
        - ∫ t in (1 - lamStarEvenQ10 / 2)..(lamStarEvenQ10 / 2),
          pEQ t ^ 2 * pEQ (t - 1) ^ 2
      ≤ (68 * (1 - α)) * (sqPrimEvenQ10 (lamStarEvenQ10 / 2)
          - sqPrimEvenQ10 (1 - lamStarEvenQ10 / 2)) := by
    rw [← intervalIntegral.integral_sub (hIα _ _) (hI1 _ _), ← hI2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hb1 ((hIα _ _).sub (hI1 _ _))
      (((pEQ_continuous.pow 2).const_mul _).intervalIntegrable _ _)
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hlip := pEQ_sq_lip (x := x - 1) (y := x - α)
      (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [show (x - α) - (x - 1) = 1 - α by ring,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - α by linarith)] at hlip
    have hd : pEQ (x - α) ^ 2 - pEQ (x - 1) ^ 2 ≤ 68 * (1 - α) := (le_abs_self _).trans hlip
    have hsq : 0 ≤ pEQ x ^ 2 := sq_nonneg _
    calc pEQ x ^ 2 * pEQ (x - α) ^ 2 - pEQ x ^ 2 * pEQ (x - 1) ^ 2
        = pEQ x ^ 2 * (pEQ (x - α) ^ 2 - pEQ (x - 1) ^ 2) := by ring
      _ ≤ pEQ x ^ 2 * (68 * (1 - α)) := mul_le_mul_of_nonneg_left hd hsq
      _ = 68 * (1 - α) * pEQ x ^ 2 := by ring
  have hD := cEQ_num
  rw [← profMass_eq_evenq10 hprof hlam] at hD
  have hD' := mul_le_mul_of_nonneg_left hD (sub_nonneg.2 h1)
  rw [hsplit, div_le_iff₀ hM2, add_mul, div_mul_cancel₀ _ hM2.ne']
  nlinarith [hT1, hT2, hD']

theorem CfamEven_le : CfamEven ≤ 2 * (5412 / 1000) := by
  have h := C_qQ_le
  unfold CfamEven
  push_cast at h
  linarith

/-- **`ZoneLipschitzData Family.evenQle r ε`, certified**: `ψ₁ = 0.02994`, `c = 7`,
`2(C − 1)ψ₁ ≤ 2·9.824·0.02994 = 0.588261 < 0.5921332 = sZoneEvenQ` (margin `0.0039`). -/
theorem zoneLipschitzData_evenQle (r ε : ℝ) : ZoneLipschitzData Family.evenQle r ε := by
  refine ⟨2994 / 100000, 7, by norm_num, ?_, ?_⟩
  · have := CfamEven_le
    simp only [Family.Cconst, Family.sZoneF]
    unfold sZoneEvenQ
    linarith
  · intro Qn P hdes α h0 h1
    obtain ⟨hP, -, -, hlam, -, -, -, -, -, -, -, hprof⟩ := hdes
    have hlam' : P.lam = lamStarEvenQ10 := hlam
    have hprof' : P.prof = designProfileEvenQ10 := hprof
    have h := psiEQ_le_psi_one_add hP hprof' hlam' h0 h1
    have h' := psiEQ_one_le hP hprof' hlam'
    linarith

/-- **`ZoneLipschitzData Family.oddQle r ε`** — the same certificate. -/
theorem zoneLipschitzData_oddQle (r ε : ℝ) : ZoneLipschitzData Family.oddQle r ε := by
  refine ⟨2994 / 100000, 7, by norm_num, ?_, ?_⟩
  · have := CfamEven_le
    simp only [Family.Cconst, Family.sZoneF]
    unfold sZoneEvenQ
    linarith
  · intro Qn P hdes α h0 h1
    obtain ⟨hP, -, -, hlam, -, -, -, -, -, -, -, hprof⟩ := hdes
    have hlam' : P.lam = lamStarEvenQ10 := hlam
    have hprof' : P.prof = designProfileEvenQ10 := hprof
    have h := psiEQ_le_psi_one_add hP hprof' hlam' h0 h1
    have h' := psiEQ_one_le hP hprof' hlam'
    linarith

end ZoneData
end ZetaQ
