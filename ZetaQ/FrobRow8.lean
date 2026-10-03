/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaQ.Budget
import ZetaQ.PayoffSmooth
import ZetaQ.AbelLogPow

/-!
# Row 8 (family): `Σ_χ 𝓜[μ_χ, μ_χ]` — part A, the SHARP `∫_T^{2T} μ_q²` evaluation.

[R]'s `int_mu_sq` / `IntMuChi.int_muq_sq_uniform` has error `≍ (main)/l(T)²`, which is
`O(1/l²)`-relative — NOT `O(1/ℒ)`.  Here: `∫_T^{2T} μ_q² = (T/4π²)(ℓ_{1,q}² + 1 − 2log²2) +
O(ℓ/T)`, from the exact antiderivative of `log²(cτ)` and Stirling's `|μ − (1/2π)log(qτ/2π)| ≤
(10/π)/τ²` (`GammaChi.muq_stirling_const`, q-free).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaQ
namespace FamRows

open Zeta23.ThmE

/-! ## A1. The antiderivative of `log²(c·t)` -/

theorem hasDerivAt_logc (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ) :
    HasDerivAt (fun t => Real.log (c * t)) (1 / τ) τ := by
  have h : HasDerivAt (fun t => c * t) c τ := by
    simpa using (hasDerivAt_id τ).const_mul c
  have hl := Real.hasDerivAt_log (by positivity : c * τ ≠ 0)
  have := hl.comp τ h
  have e : (c * τ)⁻¹ * c = 1 / τ := by field_simp
  rw [e] at this
  exact this

theorem hasDerivAt_logsq_anti (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ) :
    HasDerivAt (fun t => t * (Real.log (c * t) ^ 2 - 2 * Real.log (c * t) + 2))
      (Real.log (c * τ) ^ 2) τ := by
  have hl := hasDerivAt_logc c τ hc hτ
  have h1 : HasDerivAt (fun t => Real.log (c * t) ^ 2 - 2 * Real.log (c * t) + 2)
      (2 * Real.log (c * τ) * (1 / τ) - 2 * (1 / τ)) τ := by
    have h2 := ((hl.pow 2).sub (hl.const_mul 2)).add_const 2
    refine h2.congr_deriv ?_
    simp
  refine ((hasDerivAt_id' τ).mul h1).congr_deriv ?_
  field_simp
  ring

/-- `∫_T^{2T} log²(c τ) dτ = T·((log(cT) + 2log2 − 1)² + 1 − 2 log²2)`. -/
theorem integral_logsq_Icc (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∫ τ in T..(2 * T), Real.log (c * τ) ^ 2
      = T * ((Real.log (c * T) + 2 * Real.log 2 - 1) ^ 2 + 1 - 2 * Real.log 2 ^ 2) := by
  have hderiv : ∀ x ∈ Set.uIcc T (2 * T),
      HasDerivAt (fun t => t * (Real.log (c * t) ^ 2 - 2 * Real.log (c * t) + 2))
        (Real.log (c * x) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact hasDerivAt_logsq_anti c x hc (by linarith [hx.1])
  have hint : IntervalIntegrable (fun x => Real.log (c * x) ^ 2) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    apply ContinuousOn.pow
    apply ContinuousOn.log (by fun_prop)
    intro x hx; have hx0 : 0 < x := by linarith [hx.1]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h2 : Real.log (c * (2 * T)) = Real.log (c * T) + Real.log 2 := by
    rw [show c * (2 * T) = (c * T) * 2 by ring, Real.log_mul (by positivity) (by norm_num)]
  rw [h2]
  ring

/-! ## A2. `∫_T^{2T} μ_q²`, sharp -/

/-- **The sharp `∫μ_q²` evaluation**: for `T ≥ 2π`, `q ≥ 1`, `κ ≤ 1`,
`|∫_T^{2T} μ_q² − (T/4π²)(ℓ_{1,q}² + 1 − 2log²2)| ≤ (10/π)/T·((ℓ_{1,q}+1)/π + (10/π)/T²)`. -/
theorem int_muq_sq_sharp {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) {T : ℝ} (hT : 2 * Real.pi ≤ T) :
    |(∫ τ in T..(2 * T), muq κ q τ ^ 2)
        - T * (ell1q q T ^ 2 + 1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2)|
      ≤ (10 / Real.pi) / T * ((ell1q q T + 1) / Real.pi + (10 / Real.pi) / T ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  set c : ℝ := q / (2 * Real.pi) with hcdef
  have hc : 0 < c := by positivity
  set m : ℝ → ℝ := fun τ => (1 / (2 * Real.pi)) * Real.log (c * τ) with hmdef
  -- ℓ_{1,q} = log(cT) + 2 log 2 − 1
  have hell : ell1q q T = Real.log (c * T) + 2 * Real.log 2 - 1 := by
    unfold ell1q
    rw [hcdef, show (q : ℝ) * T / (2 * Real.pi) = q / (2 * Real.pi) * T by ring]
  -- ∫ m² exactly
  have hm2 : (∫ τ in T..(2 * T), m τ ^ 2)
      = T * (ell1q q T ^ 2 + 1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2) := by
    have e : (fun τ => m τ ^ 2) = fun τ => (1 / (2 * Real.pi)) ^ 2 * Real.log (c * τ) ^ 2 := by
      funext τ; rw [hmdef]; ring
    rw [e, intervalIntegral.integral_const_mul, integral_logsq_Icc c T hc hT0, hell]
    first | (field_simp; ring) | field_simp
  -- Stirling on [T, 2T]
  have hst : ∀ τ ∈ Set.uIoc T (2 * T), |muq κ q τ - m τ| ≤ (10 / Real.pi) / T ^ 2 := by
    intro τ hτ
    rw [Set.uIoc_of_le (by linarith)] at hτ
    have hτT : T < τ := hτ.1
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_pos (by linarith)]; linarith
    have h := Zeta23.ThmE.GammaChi.muq_stirling_const hκ hq τ hτ1
    have e : (1 / (2 * Real.pi)) * Real.log ((q : ℝ) * |τ| / (2 * Real.pi)) = m τ := by
      simp only [hmdef, hcdef]
      rw [abs_of_pos (by linarith)]
      congr 2
      ring
    rw [e] at h
    refine h.trans ?_
    rw [show (20 : ℝ) / (2 * Real.pi) = 10 / Real.pi by ring]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  -- |m| ≤ m(2T) ≤ (ℓ+1)/(2π) on [T,2T], and m ≥ 0 there
  have hmb : ∀ τ ∈ Set.uIoc T (2 * T), |m τ| ≤ (ell1q q T + 1) / (2 * Real.pi) := by
    intro τ hτ
    rw [Set.uIoc_of_le (by linarith)] at hτ
    have hcτ1 : 1 ≤ c * τ := by
      rw [hcdef]
      have : 2 * Real.pi ≤ τ := by linarith [hτ.1]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hlog0 : 0 ≤ Real.log (c * τ) := Real.log_nonneg hcτ1
    have hlogle : Real.log (c * τ) ≤ Real.log (c * T) + Real.log 2 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      apply Real.log_le_log (by positivity)
      nlinarith [hτ.2]
    have hl2 : Real.log 2 ≤ 2 * Real.log 2 := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
    simp only [hmdef]
    rw [abs_of_nonneg (mul_nonneg (by positivity) hlog0)]
    rw [hell]
    have : Real.log (c * τ) ≤ Real.log (c * T) + 2 * Real.log 2 - 1 + 1 := by linarith
    calc (1 / (2 * Real.pi)) * Real.log (c * τ)
        ≤ (1 / (2 * Real.pi)) * (Real.log (c * T) + 2 * Real.log 2 - 1 + 1) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (Real.log (c * T) + 2 * Real.log 2 - 1 + 1) / (2 * Real.pi) := by ring
  -- the pointwise bound on μ² − m²
  set E : ℝ := (10 / Real.pi) / T ^ 2 with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hpt : ∀ τ ∈ Set.uIoc T (2 * T),
      ‖muq κ q τ ^ 2 - m τ ^ 2‖ ≤ E * (2 * ((ell1q q T + 1) / (2 * Real.pi)) + E) := by
    intro τ hτ
    have h1 := hst τ hτ
    have h2 := hmb τ hτ
    rw [Real.norm_eq_abs]
    have e : muq κ q τ ^ 2 - m τ ^ 2 = (muq κ q τ - m τ) * ((muq κ q τ - m τ) + 2 * m τ) := by
      ring
    rw [e, abs_mul]
    have h3 : |(muq κ q τ - m τ) + 2 * m τ| ≤ E + 2 * ((ell1q q T + 1) / (2 * Real.pi)) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    calc |muq κ q τ - m τ| * |(muq κ q τ - m τ) + 2 * m τ|
        ≤ E * (E + 2 * ((ell1q q T + 1) / (2 * Real.pi))) :=
          mul_le_mul h1 h3 (abs_nonneg _) hE0
      _ = E * (2 * ((ell1q q T + 1) / (2 * Real.pi)) + E) := by ring
  -- integrate
  have hcont : Continuous (muq κ q) := (Zeta23.ThmE.GammaChi.muq_smooth κ q).continuous
  have hmcont : ContinuousOn m (Set.uIcc T (2 * T)) := by
    rw [hmdef, Set.uIcc_of_le (by linarith)]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro x hx; have hx0 : 0 < x := by linarith [hx.1]
    positivity
  have hint1 : IntervalIntegrable (fun τ => muq κ q τ ^ 2) volume T (2 * T) :=
    (hcont.pow 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun τ => m τ ^ 2) volume T (2 * T) :=
    (hmcont.pow 2).intervalIntegrable
  have hsub : (∫ τ in T..(2 * T), muq κ q τ ^ 2) - T * (ell1q q T ^ 2 + 1 - 2 * Real.log 2 ^ 2)
      / (4 * Real.pi ^ 2) = ∫ τ in T..(2 * T), (muq κ q τ ^ 2 - m τ ^ 2) := by
    rw [intervalIntegral.integral_sub hint1 hint2, hm2]
  rw [hsub]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs] at hbound
  refine hbound.trans ?_
  rw [show |2 * T - T| = T by rw [abs_of_pos (by linarith)]; ring]
  rw [hEdef]
  apply le_of_eq
  first | (field_simp; ring) | field_simp


/-! ## B. Per-character row 8 with q-UNIFORM constants, and the family sum -/

/-- `A_q := (log q)/(2π) + (11/π)·l(T)` — the q-uniform sup bound for `|μ_χ|` on `[T,2T]`
(`MuqUniform.muq_abs_le_Icc_uniform`). -/
def Aq (q : ℕ) (T : ℝ) : ℝ := Real.log q / (2 * Real.pi) + 11 / Real.pi * Zeta23.l T

/-- `K := 180/π + 36` — the q-free increment constant (`MuqUniform.muq_increment_bound_explicit`). -/
def Kinc : ℝ := 180 / Real.pi + 36

/-- `Cm8 q T := T(1 − 2log²2)/(4π²) + (10/π)/T·((ℓ_{1,q}+1)/π + (10/π)/T²)` — the sharp
`|∫_T^{2T}μ_q² − Tℓ_{1,q}²/(4π²)|` bound (`int_muq_sq_sharp`); RELATIVELY `O(1/ℓ²) + O(1/T)`. -/
def Cm8 (q : ℕ) (T : ℝ) : ℝ :=
  T * (1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2)
    + (10 / Real.pi) / T * ((ell1q q T + 1) / Real.pi + (10 / Real.pi) / T ^ 2)

/-- the per-character row-8 error at modulus `q` (monotone in `q`):
`2πbL·Cm8 + (A_q² + A_qK)(8 + 8 log(c_W L/4w)) + A_qK(8 + 2(c_W/w)²)`. -/
def err8 (P : ParamsQ) (q : ℕ) : ℝ :=
  2 * Real.pi * P.bQ * P.LB * Cm8 q P.T
    + ((Aq q P.T ^ 2 + Aq q P.T * Kinc) * (8 + 8 * Real.log (P.cWin * P.LB / (4 * P.w)))
      + Aq q P.T * Kinc * (8 + 2 * (P.cWin / P.w) ^ 2))

theorem one_sub_two_logsq_nonneg : 0 ≤ 1 - 2 * Real.log 2 ^ 2 := by
  have h1 := Real.log_two_lt_d9
  have h2 := Real.log_two_gt_d9
  nlinarith

theorem int_muq_sq_Cm8 {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) {T : ℝ} (hT : 2 * Real.pi ≤ T) :
    |(∫ τ in T..(2 * T), muq κ q τ ^ 2) - T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)| ≤ Cm8 q T := by
  have h := int_muq_sq_sharp hκ hq hT
  have hT0 : 0 < T := by linarith [Real.pi_pos]
  have hc : 0 ≤ T * (1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2) :=
    div_nonneg (mul_nonneg hT0.le one_sub_two_logsq_nonneg) (by positivity)
  unfold Cm8
  calc |(∫ τ in T..(2 * T), muq κ q τ ^ 2) - T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)|
      = |((∫ τ in T..(2 * T), muq κ q τ ^ 2)
            - T * (ell1q q T ^ 2 + 1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2))
          + T * (1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2)| := by ring_nf
    _ ≤ |(∫ τ in T..(2 * T), muq κ q τ ^ 2)
            - T * (ell1q q T ^ 2 + 1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2)|
          + |T * (1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2)| := abs_add_le _ _
    _ ≤ (10 / Real.pi) / T * ((ell1q q T + 1) / Real.pi + (10 / Real.pi) / T ^ 2)
          + T * (1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2) := by
        rw [abs_of_nonneg hc]; exact add_le_add h le_rfl
    _ = _ := by ring

theorem T_ge_2pie_of_valid' {P : ParamsQ} (hP : P.Valid) : 2 * Real.pi * Real.exp 1 ≤ P.T := by
  have hT : (300:ℝ) ≤ P.T := hP.T_ge300
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  nlinarith [Real.exp_pos 1]

/-- **LEDGER ROW 8, PER CHARACTER, q-UNIFORM**: at every valid design point with `8w ≤ L`,
`|𝓜[μ_χ,μ_χ] − b·(TL/2π)·ℓ_{1,q}²| ≤ err8 P q`.  No `T₀`, no per-character existential. -/
theorem Mform_mumu_err8 (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {q : ℕ} (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) :
    |Mform P (muDensity q χ) (muDensity q χ)
        - P.bQ * (P.T * P.LB / (2 * Real.pi)) * ell1q q P.T ^ 2| ≤ err8 P q := by
  have hl := one_le_l_of_valid hP
  have hX := one_le_XQ_of_valid hP
  have hT2 : (2:ℝ) ≤ P.T := by linarith [hP.T_ge300]
  have hκ : parity χ ≤ 1 := parity_le_one χ
  have hTe : 2 * Real.pi * Real.exp 1 ≤ P.T := T_ge_2pie_of_valid' hP
  have hA0 : 0 ≤ Aq q P.T := by
    unfold Aq
    have := Real.log_natCast_nonneg q
    positivity
  have hμl : ∀ τ ∈ Set.Icc P.T (2 * P.T), |muDensity q χ τ| ≤ Aq q P.T := fun τ hτ =>
    MuqUniform.muq_abs_le_Icc_uniform hκ hq hTe τ hτ
  have hK0 : 0 ≤ Kinc := by unfold Kinc; positivity
  have hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |muDensity q χ (t + r) - muDensity q χ t| ≤ Kinc * (|r| + r ^ 2) / t :=
    fun t ht r => MuqUniform.muq_increment_bound_explicit hκ q t ht r
  have hT2pi : 2 * Real.pi ≤ P.T := by linarith [hP.T_ge300, Real.pi_lt_four]
  have hCm := int_muq_sq_Cm8 hκ hq hT2pi
  have h := Mform_muDensity_eval P hP hw hl hX hT2 χ hq hA0 hμl hK0 hKinc hCm
  unfold err8
  exact h

/-- (primed: the same helper is also declared in `ZetaQ/FrobRow9.lean` as `log_natCast_mono`;
the two modules are independent, so the Row-8 copy is primed — cf. `T_ge_2pie_of_valid'` below.) -/
theorem log_natCast_mono' {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

theorem ell1q_mono {q Q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q) {T : ℝ} (hT : 0 < T) :
    ell1q q T ≤ ell1q Q T := by
  unfold ell1q
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have : Real.log ((q:ℝ) * T / (2 * Real.pi)) ≤ Real.log ((Q:ℝ) * T / (2 * Real.pi)) := by
    apply Real.log_le_log (by positivity)
    gcongr
  linarith

/-- `err8` is monotone in `q` (every `q`-dependence is through `log q`, `ℓ_{1,q}`, both
nondecreasing, with nonnegative coefficients). -/
theorem err8_mono (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {q Qn : ℕ} (hq : 1 ≤ q)
    (hqQ : q ≤ Qn) : err8 P q ≤ err8 P Qn := by
  have hT0 : 0 < P.T := hP.T_pos
  have hl := one_le_l_of_valid hP
  have hb0 : 0 ≤ P.bQ := hP.bQ_pos.le
  have hL0 : 0 ≤ P.LB := hP.LB_pos.le
  have hw0 : 0 < P.w := hP.w_pos
  have hcW : 4 ≤ P.cWin := hP.four_le_cWin
  have hA : Aq q P.T ≤ Aq Qn P.T := by
    unfold Aq
    have := log_natCast_mono' hqQ
    gcongr
  have hA0 : 0 ≤ Aq q P.T := by
    unfold Aq
    have := Real.log_natCast_nonneg q
    positivity
  have hK0 : 0 ≤ Kinc := by unfold Kinc; positivity
  have hell := ell1q_mono hq hqQ hT0
  have hCm : Cm8 q P.T ≤ Cm8 Qn P.T := by
    unfold Cm8
    gcongr
  have hlog0 : 0 ≤ Real.log (P.cWin * P.LB / (4 * P.w)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hf1 : 0 ≤ 8 + 8 * Real.log (P.cWin * P.LB / (4 * P.w)) := by positivity
  have hf2 : 0 ≤ 8 + 2 * (P.cWin / P.w) ^ 2 := by positivity
  unfold err8
  gcongr

/-- `Σ_{q ∈ 𝔉} φ*(q)·ℓ_{1,q}²` — the family second moment of the conductor term. -/
def famEll1Sq (F : Family) (P : ParamsQ) (Qn : ℕ) : ℝ :=
  ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * ell1q q P.T ^ 2

/-- `MAIN8 := b·(TL/2π)·Σ_{q∈𝔉} φ*(q)·ℓ_{1,q}²` — the μμ main term of the family Frobenius square. -/
def MAIN8 (F : Family) (P : ParamsQ) (Qn : ℕ) : ℝ :=
  P.bQ * (P.T * P.LB / (2 * Real.pi)) * famEll1Sq F P Qn

/-- `abs_familySum_sub_le`, with the per-character bound required only ON the family. -/
theorem abs_familySum_sub_le' (F : Family) (Qn : ℕ)
    (f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) {c : ℝ}
    (h : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q, |f q χ - g q χ| ≤ c) :
    |familySum F Qn f - familySum F Qn g| ≤ F.sizeR Qn * c := by
  classical
  have hsub : familySum F Qn f - familySum F Qn g
      = familySum F Qn (fun q χ => f q χ - g q χ) := by
    unfold familySum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => (Finset.sum_sub_distrib _ _).symm
  rw [hsub, ← familySum_const F Qn c]
  unfold familySum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun q hq => ?_)
  exact le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum fun χ hχ => h q hq χ (F.chars_subset q hχ))

/-! **The same second moment at the family's OWN per-modulus weight.**

`famEll1Sq` / `MAIN8` price each modulus at the FULL `φ*(q)`, while the left-hand `familySum`
of row 8 ranges over `F.chars q` — about half of that on a parity family, so the old statement
of `famMform_mumu_eval` compared a half-sized sum with a full-sized main term and was FALSE
there, not merely unproved. The honest weight is `|F.chars q|`. -/

/-- `Σ_{q ∈ 𝔉} |F.chars q| · ℓ_{1,q}²` — `famEll1Sq` at the family's own per-modulus weight. -/
def famEll1SqChars (F : Family) (P : ParamsQ) (Qn : ℕ) : ℝ :=
  ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * ell1q q P.T ^ 2

/-- `MAIN8` at the family's own per-modulus weight. -/
def MAIN8chars (F : Family) (P : ParamsQ) (Qn : ℕ) : ℝ :=
  P.bQ * (P.T * P.LB / (2 * Real.pi)) * famEll1SqChars F P Qn

theorem famEll1SqChars_eq_of_isFull {F : Family} (h : F.IsFull) (P : ParamsQ) (Qn : ℕ) :
    famEll1SqChars F P Qn = famEll1Sq F P Qn :=
  Finset.sum_congr rfl fun q _ => by rw [F.card_chars_of_isFull h]

theorem MAIN8chars_eq_of_isFull {F : Family} (h : F.IsFull) (P : ParamsQ) (Qn : ℕ) :
    MAIN8chars F P Qn = MAIN8 F P Qn := by
  unfold MAIN8chars MAIN8; rw [famEll1SqChars_eq_of_isFull h]

/-- **LEDGER ROW 8, FAMILY-SUMMED, ALL SIX FAMILIES**:
`|Σ_{χ∈𝔉_Q} 𝓜[μ_χ,μ_χ] − MAIN8chars| ≤ |𝔉_Q|·err8 P Qn`, at every valid design point with
`8w ≤ L`. Cap-free; no threshold beyond `Valid`; no `F.IsFull`.

The proof is `abs_familySum_sub_le'` plus a `Finset.sum_const`, exactly as in the previous
`IsFull` branch — the ONLY change is that the constant per modulus is `|F.chars q|` rather
than `φ*(q)`. `famMform_mumu_eval_of_isFull` recovers the old statement verbatim. -/
theorem famMform_mumu_eval (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (F : Family)
    (Qn : ℕ) :
    |familySum F Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ)) - MAIN8chars F P Qn|
      ≤ F.sizeR Qn * err8 P Qn := by
  have hg : familySum F Qn (fun q _ => P.bQ * (P.T * P.LB / (2 * Real.pi)) * ell1q q P.T ^ 2)
      = MAIN8chars F P Qn := by
    unfold familySum MAIN8chars famEll1SqChars
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [← hg]
  apply abs_familySum_sub_le'
  intro q hq χ _
  have hq1 := one_le_of_mem_moduli hq
  have hqQ := le_Qn_of_mem_moduli hq
  exact (Mform_mumu_err8 P hP hw hq1 χ).trans (err8_mono P hP hw hq1 hqQ)

/-- Row 8 at the FULL-family main term — the check that `famMform_mumu_eval` generalises the
statement it replaced. -/
theorem famMform_mumu_eval_of_isFull (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    {F : Family} (hF : F.IsFull) (Qn : ℕ) :
    |familySum F Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ)) - MAIN8 F P Qn|
      ≤ F.sizeR Qn * err8 P Qn := by
  rw [← MAIN8chars_eq_of_isFull hF]
  exact famMform_mumu_eval P hP hw F Qn

/-! ### B′. The even/odd evaluation of the re-spelled second moment

§12.3's pointwise count (`ZetaQ.ParityCount.abs_two_weight_sub_phiStar_le`) says
`|2|F.chars q| − φ*(q)| ≤ 1` on each parity family, so the re-spelled second moment is HALF
§12.2's up to `Σ_q ℓ_{1,q}² ≤ Q·ℓ_{1,Q}²` — a factor `Q` below the `≍ Q²ℓ²` main term. That
is the even/odd counterpart of `famEll1Sq_qle_eq` / `famEll1Sq_qle_eval`: it reduces the
parity evaluation to the full-family one proved in §C/§D of this file, with no restatement of
the `N2.Alog2 / Alog / Astar` aggregation. -/

theorem abs_two_famEll1SqChars_sub_le {F : Family} (hF : ¬ F.IsFull) (P : ParamsQ) (Qn : ℕ) :
    |2 * famEll1SqChars F P Qn - famEll1Sq F P Qn|
      ≤ ∑ q ∈ F.moduli Qn, ell1q q P.T ^ 2 := by
  unfold famEll1SqChars famEll1Sq
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  have hb := ParityCount.abs_two_weight_sub_phiStar_le hF (ParityCount.one_le_of_mem hq)
  have hsq : (0:ℝ) ≤ ell1q q P.T ^ 2 := sq_nonneg _
  have hkey : 2 * ((((F.chars q).card : ℕ) : ℝ) * ell1q q P.T ^ 2)
        - (phiStar q : ℝ) * ell1q q P.T ^ 2
      = (2 * (((F.chars q).card : ℕ) : ℝ) - (phiStar q : ℝ)) * ell1q q P.T ^ 2 := by ring
  rw [hkey, abs_mul, abs_of_nonneg hsq]
  have := mul_le_mul_of_nonneg_right hb hsq
  linarith

/-- The same, with the error in closed form: `≤ Q·ℓ_{1,Q}(T)²`. -/
theorem abs_two_famEll1SqChars_sub_le_Qn {F : Family} (hF : ¬ F.IsFull) (P : ParamsQ)
    (hP : P.Valid) (Qn : ℕ) :
    |2 * famEll1SqChars F P Qn - famEll1Sq F P Qn| ≤ (Qn : ℝ) * ell1q Qn P.T ^ 2 := by
  refine (abs_two_famEll1SqChars_sub_le hF P Qn).trans ?_
  have hT : 0 < P.T := hP.T_pos
  have hl : (0:ℝ) < Zeta23.l P.T := lt_of_lt_of_le zero_lt_one (one_le_l_of_valid hP)
  have hstep : ∀ q ∈ F.moduli Qn, ell1q q P.T ^ 2 ≤ ell1q Qn P.T ^ 2 := by
    intro q hq
    have h1 := ParityCount.one_le_of_mem hq
    have h2 := ParityCount.le_Qn_of_mem hq
    have h0 : 0 < ell1q q P.T := Zeta23.ThmE.ell1q_pos h1 hT hl
    nlinarith [ell1q_mono h1 h2 hT, h0]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((F.moduli Qn).card : ℝ) ≤ (Qn : ℝ) := by
    exact_mod_cast ParityCount.moduli_card_le F Qn
  exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)

/-- …and the full-family `famEll1Sq` it is compared against is literally §12.2's, because the
four parity families reuse the two modulus ranges verbatim (`rfl` in every branch). So
`famEll1Sq_qle_eq` / `famEll1Sq_qle_eval` apply to the parity families with NO restatement. -/
theorem famEll1Sq_reduce (F : Family) (P : ParamsQ) (Qn : ℕ) :
    famEll1Sq F P Qn = famEll1Sq Family.qle P Qn
      ∨ famEll1Sq F P Qn = famEll1Sq Family.dyadic P Qn := by
  cases F
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

/-! ## C. The N2 evaluation of `famEll1Sq` for `Family.qle` (`⟨log q⟩`, `⟨(log q)²⟩` aggregated) -/

theorem phiStar_one : phiStar 1 = 1 := by
  unfold phiStar; rw [primitiveChars_one]; rfl

/-- `famEll1Sq qle = Alog2 + 2e·Alog + e²(Astar − 1)`, `e = ℓ₁(T) = l(T) + 2log2 − 1`. -/
theorem famEll1Sq_qle_eq (P : ParamsQ) (hT : 0 < P.T) (Qn : ℕ) (hQn : 1 ≤ Qn) :
    famEll1Sq Family.qle P Qn
      = Normalisation.N2.Alog2 Qn + 2 * Zeta23.ell1 P.T * Normalisation.N2.Alog Qn
        + Zeta23.ell1 P.T ^ 2 * (Normalisation.N2.Astar Qn - 1) := by
  unfold famEll1Sq Normalisation.N2.Alog2 Normalisation.N2.Alog Normalisation.N2.Astar
  set e := Zeta23.ell1 P.T with hedef
  have hsplit : ∀ S : Finset ℕ,
      (∑ q ∈ S, (phiStar q : ℝ) * Real.log q ^ 2) + 2 * e * (∑ q ∈ S, (phiStar q : ℝ) * Real.log q)
        + e ^ 2 * (∑ q ∈ S, (phiStar q : ℝ))
      = ∑ q ∈ S, (phiStar q : ℝ) * (e + Real.log q) ^ 2 := by
    intro S
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hmod : Family.qle.moduli Qn = Finset.Icc 2 Qn := rfl
  rw [hmod]
  have h1 : ∑ q ∈ Finset.Icc 1 Qn, (phiStar q : ℝ) * (e + Real.log q) ^ 2
      = (phiStar 1 : ℝ) * (e + Real.log ((1:ℕ):ℝ)) ^ 2
        + ∑ q ∈ Finset.Icc 2 Qn, (phiStar q : ℝ) * (e + Real.log q) ^ 2 := by
    rw [Icc_one_eq_insert Qn hQn, Finset.sum_insert (by simp)]
  have h2 : ∑ q ∈ Finset.Icc 2 Qn, (phiStar q : ℝ) * ell1q q P.T ^ 2
      = ∑ q ∈ Finset.Icc 2 Qn, (phiStar q : ℝ) * (e + Real.log q) ^ 2 := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq1 : 1 ≤ q := by have := (Finset.mem_Icc.mp hq).1; omega
    rw [Zeta23.ThmE.IntMuChi.ell1q_eq hq1 hT, hedef]
  rw [h2]
  have h3 := hsplit (Finset.Icc 1 Qn)
  rw [h1, phiStar_one] at h3
  simp only [Nat.cast_one, Real.log_one, add_zero] at h3
  linarith

/-- **`⟨ℓ_{1,q}²⟩` over the family, EXPLICIT (N2)**: for `Family.qle`, with `ℓ_Q := ℓ_{1,Q}(T)`,
`|Σ_{q∈𝔉}φ*(q)ℓ_{1,q}² − (18/π⁴)Q²·(ℓ_Q² − ℓ_Q + 1/2)|
  ≤ 30Q(1+log Q)⁴ + 26ℓ₁(T)Q(1+log Q)³ + ℓ₁(T)²(5Q(1+log Q)² + 1)`.
Note `ℓ_Q² − ℓ_Q + 1/2 = (ℓ_Q − 1/2)² + 1/4 = ⟨ℓ⟩² + Var`, `Var = 1/4`: the conductor-variance term. -/
theorem famEll1Sq_qle_eval (P : ParamsQ) (hT : 0 < P.T) (he : 0 ≤ Zeta23.ell1 P.T) (Qn : ℕ)
    (hQn : 1 ≤ Qn) :
    |famEll1Sq Family.qle P Qn
        - (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2 * (ell1q Qn P.T ^ 2 - ell1q Qn P.T + 1 / 2)|
      ≤ 30 * (Qn : ℝ) * (1 + Real.log Qn) ^ 4
        + 26 * Zeta23.ell1 P.T * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
        + Zeta23.ell1 P.T ^ 2 * (5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 + 1) := by
  rw [famEll1Sq_qle_eq P hT Qn hQn]
  have h2 := Normalisation.N2.Alog2_bound Qn hQn
  have h1 := Normalisation.N2.Alog_bound Qn hQn
  have h0 := Normalisation.N2.Astar_bound Qn hQn
  have hℓ : ell1q Qn P.T = Zeta23.ell1 P.T + Real.log Qn :=
    Zeta23.ThmE.IntMuChi.ell1q_eq hQn hT
  rw [hℓ]
  set e := Zeta23.ell1 P.T with hedef
  set c : ℝ := 18 / Real.pi ^ 4 with hcdef
  set A2 := Normalisation.N2.Alog2 Qn
  set A1 := Normalisation.N2.Alog Qn
  set A0 := Normalisation.N2.Astar Qn
  set Lq := Real.log (Qn : ℝ)
  have key : A2 + 2 * e * A1 + e ^ 2 * (A0 - 1)
      - c * (Qn:ℝ) ^ 2 * ((e + Lq) ^ 2 - (e + Lq) + 1 / 2)
      = (A2 - c * (Qn:ℝ) ^ 2 * (Lq ^ 2 - Lq + 1 / 2))
        + 2 * e * (A1 - c * (Qn:ℝ) ^ 2 * (Lq - 1 / 2))
        + e ^ 2 * (A0 - c * (Qn:ℝ) ^ 2) - e ^ 2 := by ring
  rw [key]
  have hQ0 : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  have hLq0 : 0 ≤ Lq := Real.log_natCast_nonneg Qn
  have hb1 : |2 * e * (A1 - c * (Qn:ℝ) ^ 2 * (Lq - 1 / 2))|
      ≤ 2 * e * (13 * (Qn:ℝ) * (1 + Lq) ^ 3) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * e)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hb2 : |e ^ 2 * (A0 - c * (Qn:ℝ) ^ 2)| ≤ e ^ 2 * (5 * (Qn:ℝ) * (1 + Lq) ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ e ^ 2)]
    exact mul_le_mul_of_nonneg_left h0 (by positivity)
  have hb3 : |e ^ 2| = e ^ 2 := abs_of_nonneg (by positivity)
  calc |(A2 - c * (Qn:ℝ) ^ 2 * (Lq ^ 2 - Lq + 1 / 2))
        + 2 * e * (A1 - c * (Qn:ℝ) ^ 2 * (Lq - 1 / 2))
        + e ^ 2 * (A0 - c * (Qn:ℝ) ^ 2) - e ^ 2|
      ≤ |(A2 - c * (Qn:ℝ) ^ 2 * (Lq ^ 2 - Lq + 1 / 2))
        + 2 * e * (A1 - c * (Qn:ℝ) ^ 2 * (Lq - 1 / 2))
        + e ^ 2 * (A0 - c * (Qn:ℝ) ^ 2)| + |e ^ 2| := abs_sub _ _
    _ ≤ |(A2 - c * (Qn:ℝ) ^ 2 * (Lq ^ 2 - Lq + 1 / 2))
        + 2 * e * (A1 - c * (Qn:ℝ) ^ 2 * (Lq - 1 / 2))|
        + |e ^ 2 * (A0 - c * (Qn:ℝ) ^ 2)| + |e ^ 2| := by
        gcongr; exact abs_add_le _ _
    _ ≤ |A2 - c * (Qn:ℝ) ^ 2 * (Lq ^ 2 - Lq + 1 / 2)|
        + |2 * e * (A1 - c * (Qn:ℝ) ^ 2 * (Lq - 1 / 2))|
        + |e ^ 2 * (A0 - c * (Qn:ℝ) ^ 2)| + |e ^ 2| := by
        gcongr; exact abs_add_le _ _
    _ ≤ 30 * (Qn:ℝ) * (1 + Lq) ^ 4 + 2 * e * (13 * (Qn:ℝ) * (1 + Lq) ^ 3)
        + e ^ 2 * (5 * (Qn:ℝ) * (1 + Lq) ^ 2) + e ^ 2 := by
        rw [hb3]; gcongr
    _ = _ := by ring

/-- The conductor-variance shape of the main term: `ℓ² − ℓ + 1/2 = (ℓ − 1/2)² + 1/4`. -/
theorem main8_variance_shape (ℓ : ℝ) : ℓ ^ 2 - ℓ + 1 / 2 = (ℓ - 1 / 2) ^ 2 + 1 / 4 := by ring


/-! ## D. The identification with §11's `ψ(0)` — the μμ block IS the `ψ(0)` term of `B` -/

/-- **`ψ(v_design)(0) = b/(λa²)`**: the zeroth autocorrelation of the construction's normalised
profile `v_design(t) = φ(tℒ)²·ℒ/(aL)` is `∫φ⁴·ℒ/(aL)² = bL·ℒ/(a²L²) = b/(λa²)`. -/
theorem psi_vDesign_zero (P : ParamsQ) (hP : P.Valid) :
    Payoff.psi (Payoff.vDesign P) 0 = P.bQ / (P.lam * P.aQ ^ 2) := by
  have hLL : 0 < P.LL := hP.LL_pos
  have hLB : 0 < P.LB := hP.LB_pos
  have ha : 0 < P.aQ := hP.aQ_pos
  have hlam : 0 < P.lam := hP.lam_pos
  have hb : ∫ u, P.phiQ u ^ 4 = P.bQ * P.LB := by
    rw [hP.bQ_eq_bv]; unfold Zeta23.AdmWindow.bv; field_simp
  have e : ∀ t : ℝ, Payoff.vDesign P t * Payoff.vDesign P (t - 0)
      = (P.LL / (P.LB * P.aQ)) ^ 2 * P.phiQ (t * P.LL) ^ 4 := by
    intro t; unfold Payoff.vDesign; rw [sub_zero]; ring
  unfold Payoff.psi
  calc (∫ t, Payoff.vDesign P t * Payoff.vDesign P (t - 0))
      = ∫ t, (P.LL / (P.LB * P.aQ)) ^ 2 * P.phiQ (t * P.LL) ^ 4 :=
        integral_congr_ae (Filter.Eventually.of_forall e)
    _ = (P.LL / (P.LB * P.aQ)) ^ 2 * ∫ t, P.phiQ (t * P.LL) ^ 4 := integral_const_mul _ _
    _ = (P.LL / (P.LB * P.aQ)) ^ 2 * (|P.LL⁻¹| • ∫ u, P.phiQ u ^ 4) := by
        rw [MeasureTheory.Measure.integral_comp_mul_right (fun u => P.phiQ u ^ 4) P.LL]
    _ = (P.LL / (P.LB * P.aQ)) ^ 2 * (P.LL⁻¹ * (P.bQ * P.LB)) := by
        rw [smul_eq_mul, hb, abs_of_pos (inv_pos.mpr hLL)]
    _ = P.bQ / (P.lam * P.aQ ^ 2) := by
        have hLBdef : P.LB = P.lam * P.LL := rfl
        rw [hLBdef]
        first | (field_simp; ring) | field_simp

/-- **`MAIN8` in `ψ(0)`-units**: `MAIN8 = a²L²·ψ(v_design)(0)·(T/2π)·(Σφ*ℓ_{1,q}²)/ℒ`.
Against `𝒩 ≈ (T/2π)·Σφ*ℓ_{1,q}` this says `MAIN8/(a²L²𝒩) ≈ ψ(0)·⟨ℓ²⟩/(ℒ⟨ℓ⟩)`. -/
theorem MAIN8_eq_psi (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) :
    MAIN8 F P Qn
      = P.aQ ^ 2 * P.LB ^ 2 * Payoff.psi (Payoff.vDesign P) 0
          * (P.T / (2 * Real.pi)) * (famEll1Sq F P Qn / P.LL) := by
  rw [psi_vDesign_zero P hP]
  unfold MAIN8
  have hLL : 0 < P.LL := hP.LL_pos
  have ha : 0 < P.aQ := hP.aQ_pos
  have hlam : 0 < P.lam := hP.lam_pos
  have hLBdef : P.LB = P.lam * P.LL := rfl
  rw [hLBdef]
  first | (field_simp; ring) | field_simp

/-- `Σ_{q∈𝔉} φ*(q)·ℓ_{1,q}` — the family first moment (the RvM main term of `𝒩` is
`(T/2π)·famEll1`). -/
def famEll1 (F : Family) (P : ParamsQ) (Qn : ℕ) : ℝ :=
  ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * ell1q q P.T

/-- **THE IDENTIFICATION, STATED WITH ITS HYPOTHESES**: if `|𝒩 − (T/2π)·famEll1| ≤ E_N`
(the family RvM count, `EFChi.rvmChi_main_uniform` summed — `Budget.famRvM_upper_raw` is the
upper half), then
`|MAIN8 − a²L²ψ(0)·𝒩| ≤ a²L²ψ(0)·(E_N + (T/2π)·|famEll1Sq/ℒ − famEll1|)`,
i.e. the μμ block is the `ψ(0)` term of §11's `B` up to the RvM error and the conductor
dispersion `|⟨ℓ²⟩/ℒ − ⟨ℓ⟩|·|𝔉|·T/2π`, which is `O(|𝔉|T)` = `O(𝒩/ℒ)`. -/
theorem MAIN8_sub_psi_N_le (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) {EN : ℝ}
    (hN : |NfamQ P F Qn - (P.T / (2 * Real.pi)) * famEll1 F P Qn| ≤ EN) :
    |MAIN8 F P Qn - P.aQ ^ 2 * P.LB ^ 2 * Payoff.psi (Payoff.vDesign P) 0 * NfamQ P F Qn|
      ≤ P.aQ ^ 2 * P.LB ^ 2 * Payoff.psi (Payoff.vDesign P) 0
          * (EN + (P.T / (2 * Real.pi)) * |famEll1Sq F P Qn / P.LL - famEll1 F P Qn|) := by
  rw [MAIN8_eq_psi P hP F Qn]
  set c := P.aQ ^ 2 * P.LB ^ 2 * Payoff.psi (Payoff.vDesign P) 0 with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef, psi_vDesign_zero P hP]
    have := hP.bQ_pos.le; have := hP.lam_pos; have := hP.aQ_pos
    positivity
  have hT0 : 0 ≤ P.T / (2 * Real.pi) := by have := hP.T_pos.le; positivity
  have e : c * (P.T / (2 * Real.pi)) * (famEll1Sq F P Qn / P.LL) - c * NfamQ P F Qn
      = c * ((P.T / (2 * Real.pi)) * (famEll1Sq F P Qn / P.LL - famEll1 F P Qn)
          - (NfamQ P F Qn - (P.T / (2 * Real.pi)) * famEll1 F P Qn)) := by ring
  rw [e, abs_mul, abs_of_nonneg hc0]
  apply mul_le_mul_of_nonneg_left _ hc0
  calc |(P.T / (2 * Real.pi)) * (famEll1Sq F P Qn / P.LL - famEll1 F P Qn)
        - (NfamQ P F Qn - (P.T / (2 * Real.pi)) * famEll1 F P Qn)|
      ≤ |(P.T / (2 * Real.pi)) * (famEll1Sq F P Qn / P.LL - famEll1 F P Qn)|
        + |NfamQ P F Qn - (P.T / (2 * Real.pi)) * famEll1 F P Qn| := abs_sub _ _
    _ ≤ (P.T / (2 * Real.pi)) * |famEll1Sq F P Qn / P.LL - famEll1 F P Qn| + EN := by
        rw [abs_mul, abs_of_nonneg hT0]; exact add_le_add le_rfl hN
    _ = EN + (P.T / (2 * Real.pi)) * |famEll1Sq F P Qn / P.LL - famEll1 F P Qn| := by ring


/-! ## E. The family averages `⟨log q⟩`, `⟨(log q)²⟩` with EXPLICIT constants
(`ZetaQ.AbelLogPow.avg_bounds_Icc2` instantiated at `a = φ*`, `c = 18/π⁴`, `K = 5`, `m = 2`,
`hF = N2.Astar_bound`), over the certificate's own index set `Icc 2 ⌊x⌋` = `Family.qle.moduli`:
`|⟨log q⟩ − (log x − ½)| ≤ (16 + 90/π⁴)/c₀·(1+log x)³/x`,
`|⟨(log q)²⟩ − ((log x)² − log x + ½)| ≤ (16 + 126/π⁴)/c₀·(1+log x)⁴/x`,
`|⟨(log q)²⟩ − ⟨log q⟩² − ¼| ≤ (38 + 306/π⁴)/c₀·(1+log x)⁴/x` — the conductor VARIANCE is `1/4`. -/

theorem avg_log_qle (x : ℝ) (hx : 1 ≤ x) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hlow : c₀ * x ^ 2 ≤ ∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ)) :
    |(∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ) * Real.log q)
        / (∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ)) - (Real.log x - 1 / 2)|
        ≤ (2 * 5 + 5 * (18 / Real.pi ^ 4) + (phiStar 1 : ℝ)) / c₀ * (1 + Real.log x) ^ (2 + 1) / x ∧
    |(∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ) * Real.log q ^ 2)
        / (∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ))
        - (Real.log x ^ 2 - Real.log x + 1 / 2)|
        ≤ (3 * 5 + 7 * (18 / Real.pi ^ 4) + (phiStar 1 : ℝ)) / c₀ * (1 + Real.log x) ^ (2 + 2) / x ∧
    |(∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ) * Real.log q ^ 2)
        / (∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ))
        - ((∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ) * Real.log q)
            / (∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ))) ^ 2 - 1 / 4|
        ≤ (7 * 5 + 17 * (18 / Real.pi ^ 4) + 3 * (phiStar 1 : ℝ)) / c₀
            * (1 + Real.log x) ^ (2 + 2) / x :=
  AbelLogPow.avg_bounds_Icc2 (fun q => (phiStar q : ℝ)) (18 / Real.pi ^ 4) 5 2 (by positivity)
    (by norm_num) (fun N hN => Normalisation.N2.Astar_bound N hN) (fun q => Nat.cast_nonneg _)
    x hx c₀ hc₀ hlow

/-- the `Icc 2 ⌊x⌋` count IS `Family.qle.sizeR ⌊x⌋`. -/
theorem sum_phiStar_Icc2_eq_sizeR (x : ℝ) :
    ∑ q ∈ Finset.Icc 2 ⌊x⌋₊, (phiStar q : ℝ) = Family.qle.sizeR ⌊x⌋₊ := by
  rw [sizeR_eq_sum_phiStar Family.isFull_qle]; rfl


end FamRows
end ZetaQ
