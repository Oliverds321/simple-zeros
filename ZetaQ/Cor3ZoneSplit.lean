/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Cor3ZoneSplit.lean — the headline route's PP block (`InZone`, in-zone coefficient 1)
with the sieve budget ABSTRACTED, and its parity instance at `Q²/2` (Corollary 3″, second link).

Imports `ZetaQ.InZone` and `ZetaQ.Cor3Reflected`. Nothing existing is modified.

--------------------------------------------------------------------------------------
## What this file does
--------------------------------------------------------------------------------------

The six headlines reach Lemma 6.1 through `InZone.famPP_le_zone_split`, whose out-zone half is
`InZone.famPP_total_le'` — and every use of the sieve there reduces to THREE facts about the
family's character sums at one budget `B`: the `a″`/`a` halves (`sieve_half_coef`) and the χ/χ̄
cross term (`cross_pointwise_family`). `FamSieveAt F Qn P B` packages exactly those three facts,
and `inFormF_full_leB`, `cross_integral_familyB`, `famA_integral_leB`, `famPP_total_leB`,
`famPP_total_leB'` are `InZone`'s `inFormF_full_le`, …, `famPP_total_le'` with `sieveBudgetQ P`
replaced by `B` and `hLS` by `hS : FamSieveAt F Qn P B` — proofs verbatim (generated
mechanically from `InZone.lean`, then checked).

Two instances:
* `famSieveAt_full` — `B = sieveBudgetQ P = Q² + πX`, any family, from `LargeSieveFamily`:
  this recovers the tree's current route;
* `famSieveAt_par` — `B = sieveBudgetQPar P = Q²/2 + π(X + ½)`, a parity family, from the
  reflected sieve (`LargeSieveParity`): the parity class is charged only `Q²/2`.

So `famPP_total_leB'` at `famSieveAt_par` is the headline route's PP block for a parity family
at half the `Q²`, i.e. at the FULL-family constant `C` instead of `2C`. The remaining step of
the route (`InZone.famPP_le_zone_split`, which converts `B` into `F.Cconst·(K1a)·𝒩`) and the
Family/certificate plumbing are recorded in the round report.

Rule 17: as §4.
-/
import ZetaQ.InZone
import ZetaQ.Cor3Reflected

noncomputable section

open scoped BigOperators
open ComplexConjugate MeasureTheory Set

namespace ZetaQ
namespace Cor3Reflected

open ZetaQ.Zones ZetaQ.Payoff ZetaQ.InZone

/-! ## 1. The abstract family sieve -/

/-- **A family sieve at budget `B`**: the three facts about the family's character sums that
the headline route's PP block consumes. -/
structure FamSieveAt (F : Family) (Qn : ℕ) (P : ParamsQ) (B : ℝ) : Prop where
  /-- the budget is nonnegative -/
  nonneg : 0 ≤ B
  /-- the sieve on a coefficient half (`a`, `a″`): `Σ_{χ∈F}|Σ c_nχ(n)|² ≤ B·Σ|c_n|²` -/
  coef : ∀ (c : ℕ → ℝ → ℂ) (s : ℝ),
    familySum F Qn (fun _ χ => ‖AchiC P c χ s‖ ^ 2) ≤ B * ∑ n ∈ primeRangeQ P, ‖c n s‖ ^ 2
  /-- the χ/χ̄ cross term, pointwise in `s` -/
  cross : ∀ s : ℝ,
    |familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re)|
      ≤ 2 * B * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))

/-- **The tree's current route is an instance**: any family, at `sieveBudgetQ P = Q² + πX`. -/
theorem famSieveAt_full (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊) : FamSieveAt F Qn P (sieveBudgetQ P) where
  nonneg := sieveBudgetQ_nonneg P hP
  coef := fun c s =>
    (familySum_le_famSum P F Qn hQn _ fun _ _ => sq_nonneg _).trans
      (sieve_half_coef P hP hLS c s)
  cross := fun s => cross_pointwise_family F Qn P hP hLS hQn s

/-- Parity twin of `sieve_half_coef` (general coefficient family). -/
theorem sieve_half_coef_par (P : ParamsQ) (hP : P.Valid) (hLS : LargeSieveParity) (p : ℕ)
    (c : ℕ → ℝ → ℂ) (s : ℝ) :
    famSum P (fun _ χ => parInd p χ * ‖AchiC P c χ s‖ ^ 2)
      ≤ sieveBudgetQPar P * ∑ n ∈ primeRangeQ P, ‖c n s‖ ^ 2 := by
  rw [famSum_parInd]
  have key := hLS ⌊P.Q⌋₊ ⌊P.XQ⌋₊ p (fun n => c n s)
  have hnn : (0 : ℝ) ≤ ∑ n ∈ primeRangeQ P, ‖c n s‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  refine le_trans key ?_
  refine mul_le_mul_of_nonneg_right ?_ hnn
  have hX : ((⌊P.XQ⌋₊ : ℕ) : ℝ) ≤ P.XQ := Nat.floor_le (Real.exp_nonneg _)
  have hQ : ((⌊P.Q⌋₊ : ℕ) : ℝ) ≤ P.Q := Nat.floor_le (by linarith [hP.Q_ge])
  have hQ0 : (0 : ℝ) ≤ ((⌊P.Q⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hπX : Real.pi * ((⌊P.XQ⌋₊ : ℕ) : ℝ) ≤ Real.pi * P.XQ :=
    mul_le_mul_of_nonneg_left hX Real.pi_pos.le
  unfold sieveBudgetQPar
  nlinarith

/-- The parity-weighted Cauchy–Schwarz tail of `cross_pointwise_par`, isolated. -/
theorem famSum_parInd_cross_le (P : ParamsQ) (hP : P.Valid) (hLS : LargeSieveParity) (p : ℕ)
    (s : ℝ) :
    famSum P (fun _ χ => parInd p χ * (2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)))
      ≤ 2 * sieveBudgetQPar P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
  have hb : (0 : ℝ) ≤ sieveBudgetQPar P := sieveBudgetQPar_nonneg P
  have hrw : famSum P (fun _ χ => parInd p χ * (2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)))
      = 2 * famSum P (fun _ χ => (parInd p χ * ‖Achi P χ s‖) * (parInd p χ * ‖Bchi P χ s‖)) := by
    rw [← famSum_const_mul]
    unfold famSum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    show parInd p χ * (2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖))
        = 2 * ((parInd p χ * ‖Achi P χ s‖) * (parInd p χ * ‖Bchi P χ s‖))
    have e : 2 * ((parInd p χ * ‖Achi P χ s‖) * (parInd p χ * ‖Bchi P χ s‖))
        = parInd p χ ^ 2 * (2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)) := by ring
    rw [e, parInd_sq]
  have hCS := famSum_cauchy_schwarz P (fun _ χ => parInd p χ * ‖Achi P χ s‖)
    (fun _ χ => parInd p χ * ‖Bchi P χ s‖)
  have hsqA : famSum P (fun _ χ => (parInd p χ * ‖Achi P χ s‖) ^ 2)
      = famSum P (fun _ χ => parInd p χ * ‖Achi P χ s‖ ^ 2) := by
    unfold famSum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    show (parInd p χ * ‖Achi P χ s‖) ^ 2 = parInd p χ * ‖Achi P χ s‖ ^ 2
    rw [mul_pow, parInd_sq]
  have hsqB : famSum P (fun _ χ => (parInd p χ * ‖Bchi P χ s‖) ^ 2)
      = famSum P (fun _ χ => parInd p χ * ‖Bchi P χ s‖ ^ 2) := by
    unfold famSum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    show (parInd p χ * ‖Bchi P χ s‖) ^ 2 = parInd p χ * ‖Bchi P χ s‖ ^ 2
    rw [mul_pow, parInd_sq]
  rw [hsqA, hsqB] at hCS
  have hsA : Real.sqrt (famSum P (fun _ χ => parInd p χ * ‖Achi P χ s‖ ^ 2))
      ≤ Real.sqrt (sieveBudgetQPar P) * Real.sqrt (normA2 P s) := by
    rw [← Real.sqrt_mul hb]
    exact Real.sqrt_le_sqrt (sieve_half_A_par P hP hLS p s)
  have hsB : Real.sqrt (famSum P (fun _ χ => parInd p χ * ‖Bchi P χ s‖ ^ 2))
      ≤ Real.sqrt (sieveBudgetQPar P) * Real.sqrt (normB2 P s) := by
    rw [← Real.sqrt_mul hb]
    exact Real.sqrt_le_sqrt (sieve_half_B_par P hP hLS p s)
  have hprod := mul_le_mul hsA hsB (Real.sqrt_nonneg _) (by positivity)
  have hsq : (Real.sqrt (sieveBudgetQPar P) * Real.sqrt (normA2 P s))
        * (Real.sqrt (sieveBudgetQPar P) * Real.sqrt (normB2 P s))
      = sieveBudgetQPar P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
    rw [show (Real.sqrt (sieveBudgetQPar P) * Real.sqrt (normA2 P s))
            * (Real.sqrt (sieveBudgetQPar P) * Real.sqrt (normB2 P s))
          = (Real.sqrt (sieveBudgetQPar P) * Real.sqrt (sieveBudgetQPar P))
            * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) by ring,
      Real.mul_self_sqrt hb]
  rw [hrw]
  have := (hCS.trans hprod).trans (le_of_eq hsq)
  linarith

/-- **The parity instance: a parity family has a family sieve at `Q²/2 + π(X + ½)`.** -/
theorem famSieveAt_par (F : Family) (p : ℕ)
    (hFp : ∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p))
    (Qn : ℕ) (P : ParamsQ) (hP : P.Valid) (hQn : Qn ≤ ⌊P.Q⌋₊) :
    FamSieveAt F Qn P (sieveBudgetQPar P) where
  nonneg := sieveBudgetQPar_nonneg P
  coef := fun c s =>
    (familySum_le_famSum_parInd P F p hFp Qn hQn _ fun _ _ => sq_nonneg _).trans
      (sieve_half_coef_par P hP largeSieveParity_holds p c s)
  cross := fun s => by
    have habs : |familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re)|
        ≤ familySum F Qn (fun _ χ => 2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)) := by
      unfold familySum
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun q _ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun χ _ => ?_
      rw [abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc |(Achi P χ s * conj (Bchi P χ s)).re|
          ≤ ‖Achi P χ s * conj (Bchi P χ s)‖ := Complex.abs_re_le_norm _
        _ = ‖Achi P χ s‖ * ‖Bchi P χ s‖ := by rw [norm_mul, RCLike.norm_conj]
    have hsub := familySum_le_famSum_parInd P F p hFp Qn hQn
      (fun _ χ => 2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)) (fun _ _ => by positivity)
    exact habs.trans (hsub.trans (famSum_parInd_cross_le P hP largeSieveParity_holds p s))

/-! ## 2. The PP-block lemmas of `InZone` at an abstract budget `B` -/

/-- `inFormF_high_le` at budget `B`: `F(a″) ≤ B·zoneR`. -/
theorem inFormF_high_leB (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) {B : ℝ} (hS : FamSieveAt F Qn P B) :
    inFormF F Qn P (acoefHigh P) ≤ B * zoneR P := by
  rw [inFormF_eq_integral F Qn P hP hw _ (acoefHigh_continuous P)]
  unfold zoneR
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ (measurableSet_inZone P) fun s _ => ?_
  · exact (gQ_mul_integrable P hP hw
      (famSum_normSq_continuous F Qn P _ (acoefHigh_continuous P))).integrableOn
  · exact (gQ_coefSum_integrableOn P hP hw _ (acoefHigh_continuous P) _).const_mul _
  · have h := hS.coef (acoefHigh P) s
    have hg := lemma42_g_nonneg P s
    calc P.gQ s * familySum F Qn (fun _ χ => ‖AchiC P (acoefHigh P) χ s‖ ^ 2)
        ≤ P.gQ s * (B * ∑ n ∈ primeRangeQ P, ‖acoefHigh P n s‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hg
      _ = B * (P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefHigh P n s‖ ^ 2) := by ring

/-- `famA_integral_le` at budget `B`: `Σ_{χ∈F} ∫_U g|A_χ|² ≤ B∫_U g‖a‖₂²`. -/
theorem famA_integral_leB (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) {B : ℝ} (hS : FamSieveAt F Qn P B)
    (U : Set ℝ) (hU : MeasurableSet U) :
    familySum F Qn (fun _ χ => ∫ s in U, P.gQ s * ‖Achi P χ s‖ ^ 2)
      ≤ B * ∫ s in U, P.gQ s * normA2 P s := by
  have hT : (0 : ℝ) ≤ P.T := hP.T_pos.le
  have e := famForm_eq_integral F Qn P hP hw (acoefS P) (acoefS_continuous P) U
  unfold Achi
  rw [e, ← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ hU fun s _ => ?_
  · exact (gQ_mul_integrable P hP hw
      (famSum_normSq_continuous F Qn P _ (acoefS_continuous P))).integrableOn
  · exact ((gQ_mul_integrable P hP hw (normA2_continuous P hT)).const_mul _).integrableOn
  · have h12 : familySum F Qn (fun _ χ => ‖AchiC P (acoefS P) χ s‖ ^ 2) ≤ B * normA2 P s :=
      hS.coef (acoefS P) s
    have hg := lemma42_g_nonneg P s
    calc P.gQ s * familySum F Qn (fun _ χ => ‖AchiC P (acoefS P) χ s‖ ^ 2)
        ≤ P.gQ s * (B * normA2 P s) := mul_le_mul_of_nonneg_left h12 hg
      _ = B * (P.gQ s * normA2 P s) := by ring

/-- **Lemma 4.4 over the family of record, in-zone coefficient `|𝔉_Q|`:**
`Σ_{χ∈𝔉_Q} ∫_U g|A_χ|² ≤ (1+ε)(|𝔉_Q| + ERR_in)·P + (1+1/ε)(X+Q²−1)·R` for every `ε > 0`. -/
theorem inFormF_full_leB (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) {B : ℝ} (hS : FamSieveAt F Qn P B) (hs0 : 0 ≤ P.s0)
    {ε : ℝ} (hε : 0 < ε) :
    inFormF F Qn P (acoefS P)
      ≤ (1 + ε) * ((F.sizeR Qn + ERRin P Qn) * zoneP P)
        + (1 + 1 / ε) * (B * zoneR P) := by
  have h1 := inFormF_split F Qn P hP hw hε
  have h2 := inFormF_low_le F Qn P hP hw hs0
  have h3 := inFormF_high_leB F Qn P hP hw hS
  have hε1 : 0 ≤ 1 + ε := by linarith
  have hε2 : 0 ≤ 1 + 1 / ε := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hε1, mul_le_mul_of_nonneg_left h3 hε2]

/-- the integrated cross term over any measurable `U`, family of record:
`|Σ_{χ∈𝔉_Q} 2∫_U g Re(A_χ conj B_χ)| ≤ 2(X + Q² − 1)∫_U g‖a‖₂‖b‖₂`. -/
theorem cross_integral_familyB (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) {B : ℝ} (hS : FamSieveAt F Qn P B)
    (U : Set ℝ) (hU : MeasurableSet U) :
    |familySum F Qn (fun _ χ => 2 * ∫ s in U, P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)|
      ≤ 2 * B
          * ∫ s in U, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s) := by
  classical
  have hintC : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      IntegrableOn (fun s => P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) U :=
    fun q χ => gQ_cross_integrableOn P hP hw χ U
  obtain ⟨-, -, hintX, -, -, -⟩ := rho_integrability P hP hw
  -- exchange the family sum with the integral
  have hex : familySum F Qn (fun _ χ => 2 * ∫ s in U, P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)
      = ∫ s in U, ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
          2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) := by
    unfold familySum
    rw [MeasureTheory.integral_finsetSum _ (fun q _ =>
      MeasureTheory.integrable_finsetSum _ fun χ _ => (hintC q χ).const_mul 2)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun χ _ => (hintC q χ).const_mul 2)]
    exact Finset.sum_congr rfl fun χ _ => (MeasureTheory.integral_const_mul 2 _).symm
  have hpt : ∀ s : ℝ,
      |∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
          2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)|
        ≤ 2 * B
            * (P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
    intro s
    have hg := lemma42_g_nonneg P s
    have hpull : (∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
          2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re))
        = P.gQ s * familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re) := by
      unfold familySum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [hpull, abs_mul, abs_of_nonneg hg]
    have hcross := hS.cross s
    calc P.gQ s * |familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re)|
        ≤ P.gQ s
            * (2 * B * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))) :=
          mul_le_mul_of_nonneg_left hcross hg
      _ = 2 * B
            * (P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by ring
  have hintH : IntegrableOn (fun s => ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
      2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)) U :=
    MeasureTheory.integrable_finsetSum _ fun q _ =>
      MeasureTheory.integrable_finsetSum _ fun χ _ => (hintC q χ).const_mul 2
  have hRint : IntegrableOn (fun s => 2 * B
      * (P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))) U :=
    hintX.integrableOn.const_mul _
  rw [hex, ← MeasureTheory.integral_const_mul, abs_le]
  refine ⟨?_, setIntegral_mono_on hintH hRint hU fun s _ => (abs_le.mp (hpt s)).2⟩
  have hlow := setIntegral_mono_on hRint.neg hintH hU fun s _ => (abs_le.mp (hpt s)).1
  simp only [Pi.neg_apply] at hlow
  rwa [MeasureTheory.integral_neg] at hlow

/-- **THE TOTAL PP BLOCK, POINTWISE (Part 3, master form).** For every `ε > 0`:
`Σ_{χ∈𝔉_Q} 𝓜[P_χ,P_χ] ≤ 2[(1+ε)(|𝔉_Q|+ERR_in)P + (1+1/ε)(X+Q²−1)R]
  + 2(X+Q²−1)∫_{|s|>s₀} g‖a‖₂² + 2(X+Q²−1)∫_ℝ g‖a‖₂‖b‖₂`. -/
theorem famPP_total_leB (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) {B : ℝ} (hS : FamSieveAt F Qn P B) (hs0 : 0 ≤ P.s0)
    {ε : ℝ} (hε : 0 < ε) :
    familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ 2 * ((1 + ε) * ((F.sizeR Qn + ERRin P Qn) * zoneP P)
            + (1 + 1 / ε) * (B * zoneR P))
        + 2 * (B * ∫ s in (inZone P)ᶜ, P.gQ s * normA2 P s)
        + 2 * B
            * ∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s) := by
  have hphi := phiQ_sq_integrable P hP hw
  have hUm : MeasurableSet (inZone P) := measurableSet_inZone P
  -- (1) Parseval
  have h1 : familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      = familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) := by
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact lemma41_parseval_diag P (PXchi P χ) hphi (FrobAssembly.PXchi_integrableOn P χ)
      (FrobAssembly.PXchi_sq_integrableOn P χ)
  -- (2) expansion over the whole line
  have h2 : familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      = familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2)
        + familySum F Qn (fun _ χ => 2 * ∫ s : ℝ,
            P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) := by
    rw [← familySum_add', ← familySum_add']
    refine familySum_congr_prim F Qn fun q χ hχ => ?_
    have := zone_expansion P hP hw χ hχ Set.univ
    simpa only [MeasureTheory.setIntegral_univ] using this
  -- (3) the B-half is the A-half
  have h3 : familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2)
      = familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2) := by
    unfold familySum
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => integral_B_eq_A P χ
  -- (4) the A-half splits at the zone
  have h4 : familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum F Qn (fun _ χ => ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2) := by
    rw [← familySum_add']
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact (MeasureTheory.integral_add_compl hUm
      (gQ_mul_integrable P hP hw ((Achi_continuous P χ).norm.pow 2))).symm
  -- (5) the pieces
  have hin : familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = inFormF F Qn P (acoefS P) := rfl
  have hfull := inFormF_full_leB F Qn P hP hw hS hs0 hε
  have hout := famA_integral_leB F Qn P hP hw hS (inZone P)ᶜ hUm.compl
  have hcross := (abs_le.mp (cross_integral_familyB F Qn P hP hw hS Set.univ
    MeasurableSet.univ)).2
  simp only [MeasureTheory.setIntegral_univ] at hcross
  rw [h1, h2, h3, h4, hin]
  linarith

/-- **THE MASTER INEQUALITY IN ZONE-SPLIT FORM.** With `B = X+Q²−1`, `K = |𝔉_Q| + ERR_in`,
`D_ℝ = ∫g(‖a‖²+‖b‖²)`, `N_ℝ = ∫g‖a‖‖b‖`:
`Σ_χ 𝓜[P_χ,P_χ] ≤ B·D_ℝ + 2B·N_ℝ − 2(B − (1+ε)K)·zoneP + (2/ε)·B·zoneR`. -/
theorem famPP_total_leB' (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) {B : ℝ} (hS : FamSieveAt F Qn P B) (hs0 : 0 ≤ P.s0)
    {ε : ℝ} (hε : 0 < ε) :
    familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ B * (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
        + 2 * B
            * (∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))
        - 2 * (B - (1 + ε) * (F.sizeR Qn + ERRin P Qn)) * zoneP P
        + (2 / ε) * B * zoneR P := by
  have h := famPP_total_leB F Qn P hP hw hS hs0 hε
  rw [outZone_normA2_eq P hP hw] at h
  have e : (2 / ε) * B * zoneR P
      = 2 * (1 + 1 / ε) * (B * zoneR P) - 2 * B * zoneR P := by
    field_simp
    ring
  rw [e]
  linarith

/-! ## 3. The parity PP block at the headline route, at half the `Q²` -/

/-- **The headline route's PP block for a parity family, at the reflected budget.**
`InZone.famPP_total_le'` for Corollary 3's parity families with `B = Q²/2 + π(X + ½)` in place
of `Q² + πX`: the in-zone part (`(|𝔉| + ERR_in)·zoneP`) is unchanged, and every out-zone
occurrence of the budget is halved in its `Q²`. -/
theorem famPP_total_le_par (F : Family) (p : ℕ)
    (hFp : ∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p))
    (Qn : ℕ) (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (hQn : Qn ≤ ⌊P.Q⌋₊)
    (hs0 : 0 ≤ P.s0) {ε : ℝ} (hε : 0 < ε) :
    familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ sieveBudgetQPar P * (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
        + 2 * sieveBudgetQPar P
            * (∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))
        - 2 * (sieveBudgetQPar P - (1 + ε) * (F.sizeR Qn + ERRin P Qn)) * zoneP P
        + (2 / ε) * sieveBudgetQPar P * zoneR P :=
  famPP_total_leB' F Qn P hP hw (famSieveAt_par F p hFp Qn P hP hQn) hs0 hε

/-! ## 4. The headline route's PP block for a parity family, at `C_F / 2` -/

section ZoneSplitPar
open Filter

/-- **THE HEADLINE ROUTE'S PP BLOCK FOR A PARITY FAMILY, AT THE FULL-FAMILY CONSTANT.**
Parity twin of `InZone.famPP_le_zone_split`: for Corollary 3's parity family `F` (class `p`),
along the design of record, for every `ε′ > 0` and all large `Qn`, at every design point `P`:

  `Σ_{χ∈F} 𝓜[P_χ,P_χ] ≤ (aL)²·( K0a(a) + (C_F/2)·K1a(a) + ε′ )·𝒩`,  `a = zoneFactor P`.

`C_F = F.Cconst` is `CfamEven = π⁴/9` (resp. `CfamEvenDyadic = 4π⁴/27`), so `C_F/2` is the FULL
family constant `Cfam = π⁴/18` (resp. `CfamDyadic = 2π⁴/27`): the out-zone kernel of the parity
families is Theorem 1's (Corollary 2's), not twice it. Proof: `InZone.famPP_le_zone_split`'s,
verbatim (generated mechanically), with the reflected sieve (`famPP_total_le_par`, budget
`Q²/2 + π(X + ½)`) in place of `famPP_total_le'`, the budget factorisation
`budget_par_le` in place of `lemma43_budget_is_Qsq`, and `C_F/2` in place of `C_F` in
`final_arith` — the only three edits. -/
theorem famPP_le_zone_split_par (F : Family) (p : ℕ)
    (hFp : ∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p))
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ)
    (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
        ≤ (P.aQ * P.LB) ^ 2
            * (FrobAssembly.K0a (zoneFactor P) (vDesign P)
                + F.Cconst / 2 * FrobAssembly.K1a (zoneFactor P) (vDesign P) + ε')
            * NfamQ P F Qn := by
  obtain ⟨Cs, hCs0, hdiag⟩ := lemma43_diagonal (cWinDesign F)
  obtain ⟨CM, hCM0, hclose⟩ := sumA2gQ_close
  obtain ⟨Lρ, Tρ, hρ⟩ := FrobAssembly.rhoU_univ_le_pointwise (cWinDesign F)
  obtain ⟨C', hC'def⟩ : ∃ C' : ℝ, C' = F.Cconst / 2 := ⟨_, rfl⟩
  have hC : 0 < C' := by rw [hC'def]; have := FrobAssembly.Cconst_pos F; positivity
  rw [← hC'def]
  have hpi := Real.pi_pos
  -- the small parameter
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (ε' / (70 * C' + 10)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδδ : δ ^ 2 ≤ δ := by
    have := mul_le_mul_of_nonneg_left hδ1 hδ0.le
    rw [mul_one] at this
    rw [pow_two]
    exact this
  have hδε : δ * (70 * C' + 10) ≤ ε' := by
    have h : δ ≤ ε' / (70 * C' + 10) := by rw [hδdef]; exact min_le_right _ _
    have hpos : 0 < 70 * C' + 10 := by positivity
    calc δ * (70 * C' + 10) ≤ ε' / (70 * C' + 10) * (70 * C' + 10) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = ε' := div_mul_cancel₀ _ hpos.ne'
  have hδ3 : 0 < δ / 3 := by positivity
  have hδ31 : δ / 3 ≤ 1 := by linarith
  -- the thresholds
  have hK₁ : (1:ℝ) ≤ max 1 (Cs / δ + 1) := le_max_left _ _
  have hK₂ : (1:ℝ) ≤ max 1 (96 / (Real.pi * δ ^ 2)) := le_max_left _ _
  have hK₃ : (1:ℝ) ≤ max 1 (max Lρ Tρ) := le_max_left _ _
  have hK₄ : (1:ℝ) ≤ 500 := by norm_num
  have hK₅ : (1:ℝ) ≤ max 1 (15 / δ) := le_max_left _ _
  have hK₆ : (1:ℝ) ≤ max 1 (128 * C' * CM / (9 * δ)) := le_max_left _ _
  filter_upwards [FrobAssembly.design_regime F r ε hr hε _ hK₁, FrobAssembly.design_regime F r ε hr hε _ hK₂,
    FrobAssembly.design_regime F r ε hr hε _ hK₃, FrobAssembly.design_regime F r ε hr hε _ hK₄,
    FrobAssembly.design_regime F r ε hr hε _ hK₅, FrobAssembly.design_regime F r ε hr hε _ hK₆,
    FrobAssembly.design_basic F r ε hr hε,
    FrobAssembly.NfamQ_sharp_eventually F r ε hr hε hδ3 hδ31,
    zone_facts_eventually F r ε hr hε hδ0,
    zone_facts_eventually F r ε hr hε (ε₀ := δ ^ 2) (by positivity),
    ERRin_small_eventually F r ε hr hε hδ3,
    sizeR_LL_le_NfamQ_eventually F r ε hr hε hδ3 hδ31,
    reg_eventually F r ε hr hε]
    with Qn hreg₁ hreg₂ hreg₃ hreg₄ hreg₅ hreg₆ hbas hsharp hz1 hz2 herr hsN hregQ
  intro P hdes
  have hP := hdes.1
  have hQ := FrobAssembly.Q_of_design hdes
  obtain ⟨hlogK₁, hTK₁, -, -, -, hX32, -, -⟩ := hreg₁ P hdes
  obtain ⟨-, hTK₂, -, -, -, -, -, -⟩ := hreg₂ P hdes
  obtain ⟨hlogK₃, hTK₃, -, -, -, -, -, -⟩ := hreg₃ P hdes
  obtain ⟨-, -, -, -, hszK₄, -, -, -⟩ := hreg₄ P hdes
  obtain ⟨-, -, -, -, -, -, hQhalf₅, -⟩ := hreg₅ P hdes
  obtain ⟨hlogK₆, -, -, -, -, -, -, -⟩ := hreg₆ P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  obtain ⟨-, -, -, hs8, -, -, -, -, -⟩ := hregQ P hdes
  obtain ⟨hz1a, -⟩ := hz1 P hdes
  obtain ⟨-, hz2b⟩ := hz2 P hdes
  have hN := hsharp P hdes
  have herr' := herr P hdes
  have hsN' := hsN P hdes
  have hs0 : 0 ≤ P.s0 := by linarith
  have hQn : Qn ≤ ⌊P.Q⌋₊ := by rw [hQ, Nat.floor_natCast]
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2:ℝ) ≤ Qn := by exact_mod_cast hQn2
  have hQn0 : (0:ℝ) < Qn := by linarith
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hL0 : 0 < P.LB := hP.LB_pos
  have ha := hP.a_ge
  have ha0 := hP.aQ_pos
  have hcW : P.cWin = cWinDesign F := cWin_of_design hdes
  have hreg' : RegimeQ P := FrobAssembly.regimeQ_of hP hL8
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hadm := vDesign_admissible hP
  -- ── (1) the master inequality
  have h1 := famPP_total_le_par F p hFp Qn P hP hw hQn hs0 hδ0
  -- ── (2) the diagonal: `D_ℝ = (T/π) S (1+Esm)`, `|Esm| ≤ Cs/T ≤ δ`, `D_ℝ > 0`
  obtain ⟨Esm, hEsm, hdg⟩ := hdiag P hP hreg' hw (by rw [hcW])
  have hSpos : (0:ℝ) < sumA2gQ P := by
    have h := sumA2gQ_lower_const P hP hreg' hw
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have h6 : 0 < 6 - Real.log 2 := by linarith
    have h7 : 0 < Real.log 2 ^ 2 / 2 * (6 - Real.log 2) / 1296 := by positivity
    linarith only [h, h7]
  have hTCs : Cs / δ + 1 ≤ P.T := le_trans (le_max_right _ _) hTK₁
  have hCsδ : Cs ≤ P.T * δ := by
    have : Cs / δ ≤ P.T := by linarith
    rwa [div_le_iff₀ hδ0] at this
  have hEsmδ : |Esm| ≤ δ := by
    refine hEsm.trans ?_
    rw [div_le_iff₀ hTpos]
    linarith
  have hEsm1 : |Esm| < 1 := by
    refine lt_of_le_of_lt hEsm ?_
    rw [div_lt_one hTpos]
    have : Cs / δ ≥ Cs := by
      rw [ge_iff_le, le_div_iff₀ hδ0]
      exact mul_le_of_le_one_right hCs0.le hδ1
    linarith
  have hTS : 0 < P.T / Real.pi * sumA2gQ P := by positivity
  have hDpos : 0 < ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := by
    rw [hdg]
    exact mul_pos hTS (by linarith [(abs_lt.mp hEsm1).1])
  have hD0 : 0 ≤ ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := hDpos.le
  -- ── (3) the cross term: `2 N_ℝ = ρ D_ℝ`, `ρ ≤ δ`
  have hρ0 : 0 ≤ rhoU P Set.univ := rhoU_nonneg P Set.univ MeasurableSet.univ
  have hNρ : 2 * (∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))
      ≤ rhoU P Set.univ * ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := by
    have hDne : (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s)) ≠ 0 := hDpos.ne'
    have e : rhoU P Set.univ * (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
        = 2 * ∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s) := by
      unfold rhoU
      simp only [MeasureTheory.setIntegral_univ]
      field_simp
    rw [e]
  have hρδ : rhoU P Set.univ ≤ δ := by
    have hLρ : Lρ ≤ P.LB := by
      have : Lρ ≤ max 1 (max Lρ Tρ) := le_trans (le_max_left _ _) (le_max_right _ _)
      linarith [this.trans hlogK₃, hlogQ, FrobAssembly.LL_le_LB hP hlam]
    have hTρ : Tρ ≤ P.T := by
      have : Tρ ≤ max 1 (max Lρ Tρ) := le_trans (le_max_right _ _) (le_max_right _ _)
      linarith [this.trans hTK₃]
    have h := hρ P hP hw (by rw [hcW]) hLρ hTρ
    refine h.trans ?_
    have hT96 : 96 / (Real.pi * δ ^ 2) ≤ P.T := le_trans (le_max_right _ _) hTK₂
    unfold rhoConstConservative
    rw [← Real.sqrt_mul (by positivity)]
    have harg : 48 / Real.pi * (2 / P.T) ≤ δ ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hT96
      rw [show 48 / Real.pi * (2 / P.T) = 96 / (Real.pi * P.T) by
          rw [div_mul_div_comm]; norm_num, div_le_iff₀ (by positivity)]
      linarith
    calc Real.sqrt (48 / Real.pi * (2 / P.T)) ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt harg
      _ = δ := Real.sqrt_sq hδ0.le
  -- ── (4) the Mertens evaluation: `D_ℝ ≤ (X W k + E)(1+δ)`
  have hIL := FrobAssembly.intervalIntegral_gQ_mul_eq hP hw
  have hSle : sumA2gQ P
      ≤ P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2 + CM * P.LB ^ 2 := by
    have h := (abs_le.mp (hclose P hP hw hL8)).2
    rw [hIL] at h
    linarith
  have hDle : (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
      ≤ (P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P))
          + P.T / Real.pi * (CM * P.LB ^ 2)) * (1 + δ) := by
    rw [hdg]
    have hE1 : P.T / Real.pi * sumA2gQ P
        ≤ P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P))
          + P.T / Real.pi * (CM * P.LB ^ 2) := by
      have := mul_le_mul_of_nonneg_left hSle (by positivity : 0 ≤ P.T / Real.pi)
      calc P.T / Real.pi * sumA2gQ P
          ≤ P.T / Real.pi * (P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2
              + CM * P.LB ^ 2) := this
        _ = _ := by ring
    have hE2 : 1 + Esm ≤ 1 + δ := by linarith [(abs_le.mp hEsmδ).2]
    exact mul_le_mul hE1 hE2 (by linarith [(abs_lt.mp hEsm1).1])
      (add_nonneg (mul_nonneg (by positivity) (FrobAssembly.K0_add_K1_nonneg hadm)) (by positivity))
  -- ── (5) the budget: `B ≤ Q²(1+δ)`, `B X ≤ (1+δ)² C N`
  have hQ1 : (1:ℝ) ≤ P.Q := by rw [hQ]; linarith
  have hQ2pos : 0 < P.Q ^ 2 := by rw [hQ]; positivity
  have hBQ : sieveBudgetQPar P ≤ P.Q ^ 2 / 2 * (1 + δ) := by
    -- the reflected budget: `Q²/2 + π(X + ½) ≤ (Q²/2)(1 + 10Q^{−1/2})` (`budget_par_le`), and
    -- `design_regime`'s unchanged `2Q^{−1/2} ≤ 1/max 1 (15/δ) ≤ δ/15` gives `10Q^{−1/2} ≤ δ/3`.
    have hbud := budget_par_le P (δ := 1 / 2) (by norm_num) hX32 hQ1
    have h4 : 10 * Real.rpow P.Q (-(1 / 2)) ≤ δ := by
      have hm : 15 / δ ≤ max 1 (15 / δ) := le_max_right _ _
      have hmpos : 0 < max 1 (15 / δ) := by positivity
      have h5 : 15 ≤ max 1 (15 / δ) * δ := by
        have := mul_le_mul_of_nonneg_right hm hδ0.le
        rwa [div_mul_cancel₀ _ hδ0.ne'] at this
      have h6 : 1 / max 1 (15 / δ) ≤ δ / 15 := by
        rw [div_le_div_iff₀ hmpos (by norm_num)]
        linarith
      have h0 : 0 ≤ Real.rpow P.Q (-(1 / 2)) := Real.rpow_nonneg (by linarith) _
      linarith [hQhalf₅]
    have hQ22 : 0 ≤ P.Q ^ 2 / 2 := by positivity
    calc sieveBudgetQPar P ≤ P.Q ^ 2 / 2 * (1 + 10 * Real.rpow P.Q (-(1 / 2))) := hbud
      _ ≤ P.Q ^ 2 / 2 * (1 + δ) := mul_le_mul_of_nonneg_left (by linarith) hQ22
  have hX0 : 0 ≤ P.T / (2 * Real.pi) * P.LL := by positivity
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hQ2X : P.Q ^ 2 / 2 * (P.T / (2 * Real.pi) * P.LL) ≤ C' * (1 + δ / 3) * NfamQ P F Qn := by
    rw [hQ, hC'def]
    have e : (Qn:ℝ) ^ 2 / 2 * (P.T / (2 * Real.pi) * P.LL)
        = ((Qn:ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL) / 2 := by ring
    have e2 : F.Cconst / 2 * (1 + δ / 3) * NfamQ P F Qn
        = (F.Cconst * (1 + δ / 3) * NfamQ P F Qn) / 2 := by ring
    rw [e, e2]
    exact div_le_div_of_nonneg_right hN (by norm_num)
  have hCN0 : 0 ≤ C' * NfamQ P F Qn := by positivity
  have hBX : sieveBudgetQPar P * (P.T / (2 * Real.pi) * P.LL)
      ≤ (1 + δ) ^ 2 * C' * NfamQ P F Qn := by
    calc sieveBudgetQPar P * (P.T / (2 * Real.pi) * P.LL)
        ≤ P.Q ^ 2 / 2 * (1 + δ) * (P.T / (2 * Real.pi) * P.LL) :=
          mul_le_mul_of_nonneg_right hBQ hX0
      _ = (1 + δ) * (P.Q ^ 2 / 2 * (P.T / (2 * Real.pi) * P.LL)) := by ring
      _ ≤ (1 + δ) * (C' * (1 + δ / 3) * NfamQ P F Qn) :=
          mul_le_mul_of_nonneg_left hQ2X (by linarith)
      _ = (1 + δ) * (1 + δ / 3) * (C' * NfamQ P F Qn) := by ring
      _ ≤ (1 + δ) * (1 + δ) * (C' * NfamQ P F Qn) := by
          apply mul_le_mul_of_nonneg_right _ hCN0
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (1 + δ) ^ 2 * C' * NfamQ P F Qn := by ring
  -- ── (6) `K_f X ≤ (1+δ)² N`, `K_f ≤ B`, `0 ≤ K_f`
  have hS0 : 0 ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hERR0 : 0 ≤ ERRin P Qn := ERRin_nonneg P Qn hs0
  have hK0 : 0 ≤ F.sizeR Qn + ERRin P Qn := by linarith
  have hKfle : F.sizeR Qn + ERRin P Qn ≤ (1 + δ / 3) * F.sizeR Qn := by linarith
  have hKX : (F.sizeR Qn + ERRin P Qn) * (P.T / (2 * Real.pi) * P.LL)
      ≤ (1 + δ) ^ 2 * NfamQ P F Qn := by
    calc (F.sizeR Qn + ERRin P Qn) * (P.T / (2 * Real.pi) * P.LL)
        ≤ (1 + δ / 3) * F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL) :=
          mul_le_mul_of_nonneg_right hKfle hX0
      _ = (1 + δ / 3) * (F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL)) := by ring
      _ ≤ (1 + δ / 3) * ((1 + δ / 3) * NfamQ P F Qn) :=
          mul_le_mul_of_nonneg_left hsN' (by linarith)
      _ = (1 + δ / 3) * (1 + δ / 3) * NfamQ P F Qn := by ring
      _ ≤ (1 + δ) * (1 + δ) * NfamQ P F Qn := by
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      _ = (1 + δ) ^ 2 * NfamQ P F Qn := by ring
  have hsize := FrobAssembly.sizeR_le_point F Qn hQn1 hszK₄
  have hXQ1 : (1:ℝ) ≤ P.XQ := by
    unfold ParamsQ.XQ
    exact Real.one_le_exp hL0.le
  have hKB : F.sizeR Qn + ERRin P Qn ≤ sieveBudgetQPar P := by
    have h1' : F.sizeR Qn + ERRin P Qn ≤ (1 + δ / 3) * (0.2 * (Qn:ℝ) ^ 2) :=
      hKfle.trans (mul_le_mul_of_nonneg_left hsize (by linarith))
    have h2' : (1 + δ / 3) * (0.2 * (Qn:ℝ) ^ 2) ≤ (4 / 3) * (0.2 * (Qn:ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3' : (Qn:ℝ) ^ 2 / 2 ≤ sieveBudgetQPar P := by
      have hπX : 0 ≤ Real.pi * (P.XQ + 1 / 2) := mul_nonneg Real.pi_pos.le (by linarith)
      unfold sieveBudgetQPar; rw [hQ]; linarith
    linarith only [h1', h2', h3', sq_nonneg (Qn:ℝ)]
  -- ── (7) the zone facts
  have hP1 : P.T / (2 * Real.pi) * (∫ u in Set.Icc 0 P.s0, u * P.gQ u) * (1 - δ) ≤ zoneP P := by
    have := (abs_le.mp hz1a).1; linarith only [this]
  have hP2 : zoneP P ≤ P.T / (2 * Real.pi) * (∫ u in Set.Icc 0 P.s0, u * P.gQ u) * (1 + δ) := by
    have := (abs_le.mp hz1a).2; linarith only [this]
  have hR : zoneR P ≤ δ ^ 2 * zoneP P := hz2b
  have hI₀0 : 0 ≤ ∫ u in Set.Icc 0 P.s0, u * P.gQ u :=
    setIntegral_nonneg measurableSet_Icc fun u hu => mul_nonneg hu.1 (lemma42_g_nonneg P u)
  have hM0 : 0 ≤ P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u := by positivity
  have hM : 2 * (P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u)
      = P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * FrobAssembly.K0a (zoneFactor P) (vDesign P) :=
    zoneMain_eq P hP hw hs0
  -- ── (8) the kernel pieces
  have hk : K0 (vDesign P) + K1 (vDesign P)
      = FrobAssembly.K0a (zoneFactor P) (vDesign P) + FrobAssembly.K1a (zoneFactor P) (vDesign P) := by
    rw [FrobAssembly.K0a_add_K1a hadm, K0_add_K1 hadm]
  have hk0 : 0 ≤ FrobAssembly.K0a (zoneFactor P) (vDesign P) := FrobAssembly.K0a_nonneg hadm _
  have hk1 : 0 ≤ FrobAssembly.K1a (zoneFactor P) (vDesign P) := FrobAssembly.K1a_nonneg hadm _
  have hk2 : K0 (vDesign P) + K1 (vDesign P) ≤ 2 :=
    FrobAssembly.K0_add_K1_le_two hadm hP.lam_lt_two.le
  have hW0 : 0 ≤ (P.aQ * P.LB) ^ 2 := by positivity
  -- ── (9) the Mertens-remainder term: `B E ≤ δ W N`
  have hE0 : 0 ≤ P.T / Real.pi * (CM * P.LB ^ 2) := by positivity
  have hBE : sieveBudgetQPar P * (P.T / Real.pi * (CM * P.LB ^ 2))
      ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by
    have hLL128 : 128 * C' * CM / (9 * δ) ≤ P.LL :=
      le_trans (le_trans (le_max_right _ _) hlogK₆) hlogQ
    have hB0 : 0 ≤ sieveBudgetQPar P := hK0.trans hKB
    have e1 : sieveBudgetQPar P * (P.T / Real.pi * (CM * P.LB ^ 2))
        = (sieveBudgetQPar P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL) := by
      field_simp
    have hLB2 : P.LB ^ 2 ≤ 16 / 9 * (P.aQ * P.LB) ^ 2 := by
      have : (3 / 4) ^ 2 ≤ P.aQ ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
      have h0 : 0 ≤ P.LB ^ 2 := sq_nonneg _
      calc P.LB ^ 2 = 16 / 9 * ((3 / 4) ^ 2 * P.LB ^ 2) := by ring
        _ ≤ 16 / 9 * (P.aQ ^ 2 * P.LB ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_right this h0
        _ = 16 / 9 * (P.aQ * P.LB) ^ 2 := by ring
    have hq : 2 * CM * P.LB ^ 2 / P.LL ≤ 32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL := by
      apply div_le_div_of_nonneg_right _ hLL0.le
      have := mul_le_mul_of_nonneg_left hLB2 (by positivity : 0 ≤ 2 * CM)
      linarith only [this]
    have h3 : (sieveBudgetQPar P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL)
        ≤ ((1 + δ) ^ 2 * C' * NfamQ P F Qn)
            * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL) :=
      mul_le_mul hBX hq (by positivity) (mul_nonneg (mul_nonneg (by positivity) hC.le) hN0)
    have h4 : (1 + δ) ^ 2 ≤ 4 := by linarith only [hδδ, hδ1]
    have h5 : 128 / 9 * C' * CM / P.LL ≤ δ := by
      rw [div_le_iff₀ hLL0]
      rw [div_le_iff₀ (by positivity)] at hLL128
      linarith only [hLL128]
    have h6 : ((1 + δ) ^ 2 * C' * NfamQ P F Qn)
          * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL)
        = (1 + δ) ^ 2 * (32 / 9 * C' * CM / P.LL)
            * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
      field_simp
    have hWN0 : 0 ≤ (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by positivity
    have h7 : (1 + δ) ^ 2 * (32 / 9 * C' * CM / P.LL)
          * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn)
        ≤ 4 * (32 / 9 * C' * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
      have h0 : 0 ≤ (32 / 9 * C' * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
        positivity
      have := mul_le_mul_of_nonneg_right h4 h0
      linarith only [this]
    have h8 : 4 * (32 / 9 * C' * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn)
        ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by
      have e : 4 * (32 / 9 * C' * CM / P.LL) = 128 / 9 * C' * CM / P.LL := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right h5 hWN0
      linarith only [this]
    calc sieveBudgetQPar P * (P.T / Real.pi * (CM * P.LB ^ 2))
        = (sieveBudgetQPar P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL) := e1
      _ ≤ ((1 + δ) ^ 2 * C' * NfamQ P F Qn)
            * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL) := h3
      _ = (1 + δ) ^ 2 * (32 / 9 * C' * CM / P.LL)
            * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := h6
      _ ≤ 4 * (32 / 9 * C' * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := h7
      _ ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := h8
  -- ── (10) assemble
  exact final_arith (ρ := rhoU P Set.univ) (X := P.T / (2 * Real.pi) * P.LL)
    (k := K0 (vDesign P) + K1 (vDesign P)) h1 hNρ hρ0 hρδ hD0 hDle hBE hE0 hP1 hP2 hR hM hM0
    hδ0 le_rfl hδ1 hK0 hKB hBX hKX hk hk0 hk1 hk2 hC hW0 hN0 hX0 hδε

end ZoneSplitPar

end Cor3Reflected
end ZetaQ
