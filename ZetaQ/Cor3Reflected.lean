/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Cor3Reflected.lean — §4's out-zone consumption of Lemma 6.1 for ONE PARITY CLASS, at the
reflected budget `Q²/2 + π(X + ½)` (Corollary 3″, first link).

Imports `ZetaQ.Zones` and `ZetaQ.ReflectedSieve`. Nothing existing is modified.

--------------------------------------------------------------------------------------
## Why this file exists
--------------------------------------------------------------------------------------

Corollary 3's four parity families currently run at the family constant `2C` (`CfamEven`,
`CfamEvenDyadic`) because §4's out-zone step bounds a parity class by the WHOLE family's sieve
(`familySum_le_famSum`, then `LargeSieveFamily` at budget `Q² + πX`), while the parity class
has only `½|𝔉_Q| + O(Q)` members. The reflected sieve (`ZetaQ/ReflectedSieve.lean`) charges a
parity class only `Q²/2`; this file threads it through §4's Lemma 4.3 chain
(`lemma43_sieve_half_A/B`, `lemma43_cross_pointwise`, `lemma43_family_pointwise`,
`lemma43_family_consumption`), restricted to a parity class `p`, with the budget
`sieveBudgetQPar P = Q²/2 + π(X + ½)` in place of `sieveBudgetQ P = Q² + πX`.

The restriction is written as a weight `parInd p χ ∈ {0, 1}` inside the existing `famSum`, so
every §4 bookkeeping lemma (`famSum_mono`, `famSum_const_mul`, `famSum_add3`,
`famSum_cauchy_schwarz`) is reused unchanged; `famSum_parInd` converts back to the filtered
double sum that the reflected sieve speaks about.

Each statement below is the parity twin of the named §4 statement, with the same proof
skeleton. What remains for Corollary 3″ (the `C`-threading through FrobAssembly/HFrob/Margin
and the choice of certificate data for the parity families) is recorded in the round report.

Rule 17: as §4 — no λ cap, no `X`–`T` relation, no `D₀`.
-/
import ZetaQ.Zones
import ZetaQ.FrobAssembly
import ZetaQ.ReflectedSieve

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace ZetaQ
namespace Cor3Reflected

open Zones

/-! ## 1. The parity weight, the budget, and the interface -/

/-- The indicator `1_{parity χ = p}` as a real weight. -/
def parInd (p : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ := if parity χ = p then 1 else 0

theorem parInd_nonneg (p : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) : 0 ≤ parInd p χ := by
  unfold parInd; split_ifs <;> norm_num

theorem parInd_sq (p : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    parInd p χ ^ 2 = parInd p χ := by
  unfold parInd; split_ifs <;> norm_num

/-- A parity-weighted `famSum` is the double sum over the parity class. -/
theorem famSum_parInd (P : ParamsQ) (p : ℕ) (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    famSum P (fun q χ => parInd p χ * f q χ)
      = ∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ (primitiveChars q).filter (fun χ => parity χ = p),
          f q χ := by
  classical
  unfold famSum
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : parity χ = p <;> simp [parInd, h]

/-- `Q²/2 + π(X + ½)` — the reflected Gallagher budget of ONE parity class at the paper's real
cut-offs. Compare `sieveBudgetQ P = Q² + πX` for the whole family: the `Q²` is halved, which is
exactly the parity class's share of `|𝔉_Q|`. -/
def sieveBudgetQPar (P : ParamsQ) : ℝ := P.Q ^ 2 / 2 + Real.pi * (P.XQ + 1 / 2)

theorem sieveBudgetQPar_nonneg (P : ParamsQ) : 0 ≤ sieveBudgetQPar P := by
  unfold sieveBudgetQPar
  have hX : (0 : ℝ) < P.XQ := Real.exp_pos _
  have := mul_pos Real.pi_pos (by linarith : (0:ℝ) < P.XQ + 1 / 2)
  nlinarith [sq_nonneg P.Q]

/-- **The reflected Lemma 6.1 as a consumed interface** (the parity twin of
`Zones.LargeSieveFamily`). -/
def LargeSieveParity : Prop :=
  ∀ (Qn N p : ℕ) (a : ℕ → ℂ),
    ∑ q ∈ Finset.Icc 1 Qn, ∑ χ ∈ (primitiveChars q).filter (fun χ => parity χ = p),
        ‖∑ n ∈ Finset.Ioc 0 N, a n * χ (n : ZMod q)‖ ^ 2
      ≤ ((Qn : ℝ) ^ 2 / 2 + Real.pi * ((N : ℝ) + 1 / 2)) * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2

/-- Discharged, sorry-free, by `ZetaQ.Reflected.reflected_large_sieve_gallagher` — a bare
term, as `largeSieveFamily_holds` is for the full family. -/
theorem largeSieveParity_holds : LargeSieveParity :=
  fun Qn N p a => Reflected.reflected_large_sieve_gallagher Qn N p a

/-! ## 2. Lemma 4.3 for one parity class -/

/-- Parity twin of `lemma43_sieve_half_A`. -/
theorem sieve_half_A_par (P : ParamsQ) (hP : P.Valid) (hLS : LargeSieveParity) (p : ℕ)
    (s : ℝ) :
    famSum P (fun _ χ => parInd p χ * ‖Achi P χ s‖ ^ 2) ≤ sieveBudgetQPar P * normA2 P s := by
  rw [famSum_parInd]
  have key := hLS ⌊P.Q⌋₊ ⌊P.XQ⌋₊ p (fun n => acoefS P n s)
  have hnn : (0 : ℝ) ≤ normA2 P s :=
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

/-- Parity twin of `lemma43_sieve_half_B` (the conjugation is per character, so the parity
class needs no closure argument). -/
theorem sieve_half_B_par (P : ParamsQ) (hP : P.Valid) (hLS : LargeSieveParity) (p : ℕ)
    (s : ℝ) :
    famSum P (fun _ χ => parInd p χ * ‖Bchi P χ s‖ ^ 2) ≤ sieveBudgetQPar P * normB2 P s := by
  rw [famSum_parInd]
  have key := hLS ⌊P.Q⌋₊ ⌊P.XQ⌋₊ p (fun n => conj (bcoefS P n s))
  have hB : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ‖Bchi P χ s‖ ^ 2
        = ‖∑ n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊, conj (bcoefS P n s) * χ (n : ZMod q)‖ ^ 2 := by
    intro q χ
    have hstar : conj (∑ n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊, conj (bcoefS P n s) * χ (n : ZMod q))
        = Bchi P χ s := by
      unfold Bchi BchiC primeRangeQ
      rw [map_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [map_mul, Complex.conj_conj]
    rw [← hstar, RCLike.norm_conj]
  have hcoef : ∑ n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊, ‖conj (bcoefS P n s)‖ ^ 2 = normB2 P s :=
    Finset.sum_congr rfl fun n _ => by rw [RCLike.norm_conj]
  rw [hcoef] at key
  have hnn : (0 : ℝ) ≤ normB2 P s :=
    Finset.sum_nonneg fun n _ => by positivity
  have hlhs : ∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ (primitiveChars q).filter (fun χ => parity χ = p),
        ‖Bchi P χ s‖ ^ 2
      = ∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ (primitiveChars q).filter (fun χ => parity χ = p),
          ‖∑ n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊, conj (bcoefS P n s) * χ (n : ZMod q)‖ ^ 2 :=
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => hB q χ
  rw [hlhs]
  refine le_trans key ?_
  refine mul_le_mul_of_nonneg_right ?_ hnn
  have hX : ((⌊P.XQ⌋₊ : ℕ) : ℝ) ≤ P.XQ := Nat.floor_le (Real.exp_nonneg _)
  have hQ : ((⌊P.Q⌋₊ : ℕ) : ℝ) ≤ P.Q := Nat.floor_le (by linarith [hP.Q_ge])
  have hQ0 : (0 : ℝ) ≤ ((⌊P.Q⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hπX : Real.pi * ((⌊P.XQ⌋₊ : ℕ) : ℝ) ≤ Real.pi * P.XQ :=
    mul_le_mul_of_nonneg_left hX Real.pi_pos.le
  unfold sieveBudgetQPar
  nlinarith

/-- Parity twin of `lemma43_cross_pointwise`: Cauchy–Schwarz over the parity class (as the
weighted `famSum`, using `parInd² = parInd`), then the reflected sieve on each factor. -/
theorem cross_pointwise_par (P : ParamsQ) (hP : P.Valid) (hLS : LargeSieveParity) (p : ℕ)
    (s : ℝ) :
    |famSum P (fun _ χ => parInd p χ * (2 * (Achi P χ s * conj (Bchi P χ s)).re))|
      ≤ 2 * sieveBudgetQPar P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
  have hb : (0 : ℝ) ≤ sieveBudgetQPar P := sieveBudgetQPar_nonneg P
  have habs : |famSum P (fun _ χ => parInd p χ * (2 * (Achi P χ s * conj (Bchi P χ s)).re))|
      ≤ famSum P (fun _ χ => |parInd p χ * (2 * (Achi P χ s * conj (Bchi P χ s)).re)|) := by
    unfold famSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun q _ => Finset.abs_sum_le_sum_abs _ _
  have h1 : |famSum P (fun _ χ => parInd p χ * (2 * (Achi P χ s * conj (Bchi P χ s)).re))|
      ≤ famSum P (fun _ χ => 2 * ((parInd p χ * ‖Achi P χ s‖) * (parInd p χ * ‖Bchi P χ s‖))) :=
    habs.trans (famSum_mono P (fun q χ => by
      have hi := parInd_nonneg p χ
      have hre : |(Achi P χ s * conj (Bchi P χ s)).re| ≤ ‖Achi P χ s‖ * ‖Bchi P χ s‖ := by
        calc |(Achi P χ s * conj (Bchi P χ s)).re|
            ≤ ‖Achi P χ s * conj (Bchi P χ s)‖ := Complex.abs_re_le_norm _
          _ = ‖Achi P χ s‖ * ‖Bchi P χ s‖ := by rw [norm_mul, RCLike.norm_conj]
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hi]
      have e : 2 * ((parInd p χ * ‖Achi P χ s‖) * (parInd p χ * ‖Bchi P χ s‖))
          = parInd p χ ^ 2 * (2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)) := by ring
      rw [e, parInd_sq]
      exact mul_le_mul_of_nonneg_left (by linarith) hi))
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
  calc |famSum P (fun _ χ => parInd p χ * (2 * (Achi P χ s * conj (Bchi P χ s)).re))|
      ≤ famSum P (fun _ χ => 2 * ((parInd p χ * ‖Achi P χ s‖) * (parInd p χ * ‖Bchi P χ s‖))) :=
        h1
    _ = 2 * famSum P (fun _ χ => (parInd p χ * ‖Achi P χ s‖) * (parInd p χ * ‖Bchi P χ s‖)) :=
        famSum_const_mul P 2 _
    _ ≤ 2 * (sieveBudgetQPar P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))) := by
        refine mul_le_mul_of_nonneg_left ((hCS.trans hprod).trans (le_of_eq hsq)) (by norm_num)
    _ = 2 * sieveBudgetQPar P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by ring

/-- Parity twin of `lemma43_family_pointwise`. -/
theorem family_pointwise_par (P : ParamsQ) (hP : P.Valid) (hLS : LargeSieveParity) (p : ℕ)
    (hT : 0 ≤ P.T) (s : ℝ) :
    famSum P (fun _ χ => parInd p χ * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      ≤ sieveBudgetQPar P * (normA2 P s + normB2 P s)
        + 2 * sieveBudgetQPar P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
  have hexp : famSum P (fun _ χ => parInd p χ * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      = famSum P (fun _ χ => parInd p χ * ‖Achi P χ s‖ ^ 2)
        + famSum P (fun _ χ => parInd p χ * ‖Bchi P χ s‖ ^ 2)
        + famSum P (fun _ χ => parInd p χ * (2 * (Achi P χ s * conj (Bchi P χ s)).re)) := by
    rw [← famSum_add3]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ hχ => ?_
    have hx : ‖Fwin P (PXchi P χ) s‖ ^ 2
        = ‖Achi P χ s‖ ^ 2 + ‖Bchi P χ s‖ ^ 2 + 2 * (Achi P χ s * conj (Bchi P χ s)).re := by
      rw [lemma43_coeff_display P hT χ (isPrimitive_of_mem_primitiveChars hχ) s,
        ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_add]
    show parInd p χ * ‖Fwin P (PXchi P χ) s‖ ^ 2
        = parInd p χ * ‖Achi P χ s‖ ^ 2 + parInd p χ * ‖Bchi P χ s‖ ^ 2
          + parInd p χ * (2 * (Achi P χ s * conj (Bchi P χ s)).re)
    rw [hx]
    ring
  rw [hexp]
  have hA := sieve_half_A_par P hP hLS p s
  have hB := sieve_half_B_par P hP hLS p s
  have hX := cross_pointwise_par P hP hLS p s
  have hX' := (abs_le.mp hX).2
  nlinarith [hA, hB, hX']

/-- **Parity twin of `lemma43_family_consumption`** (§4's frozen core, Q7.iii(1′)), for one
parity class: `Σ_{χ ∈ 𝔉_Q, parity χ = p} ∫_U g|F_χ|² ≤ (Q²/2 + π(X + ½))(1 + ρ_U)∫_U g(‖a‖² + ‖b‖²)`.
The whole-family statement carries `Q² + πX` here; the parity class carries half the `Q²`. -/
theorem family_consumption_par (P : ParamsQ) (hP : P.Valid) (hLS : LargeSieveParity) (p : ℕ)
    (U : Set ℝ) (hU : MeasurableSet U)
    (hpos : 0 < ∫ s in U, P.gQ s * (normA2 P s + normB2 P s))
    (hint : IntegrableOn (fun s => P.gQ s * (normA2 P s + normB2 P s)) U)
    (hintF : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      IntegrableOn (fun s => P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) U)
    (hintX : IntegrableOn
      (fun s => P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) U) :
    famSum P (fun _ χ => parInd p χ * ∫ s in U, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      ≤ sieveBudgetQPar P * (1 + rhoU P U)
          * ∫ s in U, P.gQ s * (normA2 P s + normB2 P s) := by
  classical
  have hT : (0 : ℝ) ≤ P.T := le_trans Zeta23.Tail.T₀_pos.le hP.T_ge
  have hintF' : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      IntegrableOn (fun s => parInd p χ * (P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)) U :=
    fun q χ => (hintF q χ).const_mul _
  have hLHS : (∫ s in U, ∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ primitiveChars q,
        parInd p χ * (P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2))
      = famSum P (fun _ χ => parInd p χ * ∫ s in U, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) := by
    unfold famSum
    rw [MeasureTheory.integral_finsetSum _
      (fun q _ => MeasureTheory.integrable_finsetSum _ fun χ _ => hintF' q χ)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [MeasureTheory.integral_finsetSum _ fun χ _ => hintF' q χ]
    exact Finset.sum_congr rfl fun χ _ => MeasureTheory.integral_const_mul _ _
  rw [← hLHS]
  have hpt : ∀ s : ℝ,
      (∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ primitiveChars q,
          parInd p χ * (P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2))
        ≤ sieveBudgetQPar P * (P.gQ s * (normA2 P s + normB2 P s))
          + 2 * sieveBudgetQPar P
              * (P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
    intro s
    have hg := lemma42_g_nonneg P s
    have hfam := family_pointwise_par P hP hLS p hT s
    have hpull : (∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ primitiveChars q,
          parInd p χ * (P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2))
        = P.gQ s * famSum P (fun _ χ => parInd p χ * ‖Fwin P (PXchi P χ) s‖ ^ 2) := by
      unfold famSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [hpull]
    nlinarith [hfam, hg]
  have hintLHS : IntegrableOn (fun s => ∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ primitiveChars q,
      parInd p χ * (P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)) U :=
    MeasureTheory.integrable_finsetSum _
      (fun q _ => MeasureTheory.integrable_finsetSum _ fun χ _ => hintF' q χ)
  have hintRHS : IntegrableOn
      (fun s => sieveBudgetQPar P * (P.gQ s * (normA2 P s + normB2 P s))
        + 2 * sieveBudgetQPar P
            * (P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))) U :=
    (hint.const_mul _).add (hintX.const_mul _)
  refine (setIntegral_mono_on hintLHS hintRHS hU (fun s _ => hpt s)).trans (le_of_eq ?_)
  rw [MeasureTheory.integral_add (hint.const_mul _) (hintX.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  unfold rhoU
  field_simp

/-- **The parity class sits inside the family sum it weights** — the parity-family sum of
Corollary 3 (`familySum F Qn f`, `F` a parity family with class `p`, `Qn ≤ ⌊Q⌋`) is at most the
`parInd p`-weighted `famSum` (nonnegative summands). This is the parity twin of
`familySum_le_famSum`, and it is where the factor `2` of `2C` is NOT paid. -/
theorem familySum_le_famSum_parInd (P : ParamsQ) (F : Family) (p : ℕ)
    (hFp : ∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p))
    (Qn : ℕ) (hQn : Qn ≤ ⌊P.Q⌋₊)
    (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (hf : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 0 ≤ f q χ) :
    familySum F Qn f ≤ famSum P (fun q χ => parInd p χ * f q χ) := by
  classical
  rw [famSum_parInd]
  unfold familySum
  simp only [hFp]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun q _ _ => Finset.sum_nonneg fun χ _ => hf q χ)
  intro q hq
  have h1 := Reflected.Family.moduli_subset_Icc_one F Qn hq
  rw [Finset.mem_Icc] at h1 ⊢
  exact ⟨h1.1, h1.2.trans hQn⟩

/-! ## 3. The parity budget is `(Q²/2)(1 + O(Q^{−δ}))` -/

/-- The reflected budget factorises: `Q²/2 + π(X + ½) ≤ (Q²/2)(1 + 10Q^{−δ})` in the sieve range
`X ≤ Q^{2−δ}` (`0 < δ ≤ 2`, `Q ≥ 1`): `πX ≤ πQ²·Q^{−δ}` and `π/2 ≤ (π/2)Q^{2−δ}`, so the excess is
at most `3π·(Q²/2)Q^{−δ}`, and `3π ≤ 10`. Parity twin of `lemma43_budget_is_Qsq`. -/
theorem budget_par_le (P : ParamsQ) {δ : ℝ} (hδ2 : δ ≤ 2)
    (hX : P.XQ ≤ Real.rpow P.Q (2 - δ)) (hQ : (1 : ℝ) ≤ P.Q) :
    sieveBudgetQPar P ≤ P.Q ^ 2 / 2 * (1 + 10 * Real.rpow P.Q (-δ)) := by
  replace hX : P.XQ ≤ P.Q ^ (2 - δ : ℝ) := hX
  show sieveBudgetQPar P ≤ P.Q ^ 2 / 2 * (1 + 10 * P.Q ^ (-δ : ℝ))
  have hQ0 : (0 : ℝ) < P.Q := by linarith
  have hQsq : P.Q ^ (2 : ℝ) = P.Q ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsplit : P.Q ^ (2 - δ : ℝ) = P.Q ^ 2 * P.Q ^ (-δ : ℝ) := by
    rw [show (2 - δ : ℝ) = 2 + -δ by ring, Real.rpow_add hQ0, hQsq]
  have hone : (1 : ℝ) ≤ P.Q ^ (2 - δ : ℝ) := Real.one_le_rpow hQ (by linarith)
  rw [hsplit] at hX hone
  have hr : 0 ≤ P.Q ^ 2 * P.Q ^ (-δ : ℝ) := by positivity
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_d2
  unfold sieveBudgetQPar
  nlinarith [mul_le_mul_of_nonneg_left hX hπ.le, mul_le_mul_of_nonneg_left hone hπ.le]

/-- **Parity twin of `lemma43_family_le_C_diagonal_pointwise`** — §4's main endpoint for ONE
parity class: `Σ_{χ∈𝔉_Q, parity χ = p} 𝓜[P_χ,P_χ] ≤ (Q²/2)(T/π)·Σ_{n≤X}Λ(n)²g(log n)/n·(1+10Q^{−δ})(1+ρ)(1+Cs/T)`.
The whole family gets `Q²` (i.e. `famConstQ·famDiagonal`) here; one parity class gets `Q²/2`. -/
theorem family_le_diagonal_pointwise_par (c₀ : ℝ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (P : ParamsQ) (δ : ℝ) (p : ℕ), P.Valid → RegimeQ P → 8 * P.w ≤ P.LB →
      P.cWin ≤ c₀ → LargeSieveParity → 0 < δ → δ ≤ 2 →
      P.XQ ≤ Real.rpow P.Q (2 - δ) → Cs < P.T →
      (∀ (q : ℕ) (χ : DirichletCharacter ℂ q), IntegrableOn (PXchi P χ) P.IwinQ) →
      (∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        IntegrableOn (fun τ => PXchi P χ τ ^ 2) P.IwinQ) →
      IntegrableOn (fun s => P.gQ s * (normA2 P s + normB2 P s)) Set.univ →
      (∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        IntegrableOn (fun s => P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) Set.univ) →
      IntegrableOn (fun s => P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))
        Set.univ →
      famSum P (fun _ χ => parInd p χ * Mform P (PXchi P χ) (PXchi P χ))
        ≤ P.Q ^ 2 / 2 * (P.T / Real.pi) * sumA2gQ P
            * ((1 + 10 * Real.rpow P.Q (-δ)) * (1 + rhoU P Set.univ) * (1 + Cs / P.T)) := by
  classical
  obtain ⟨Cs, hCs0, hdiag⟩ := lemma43_diagonal c₀
  refine ⟨Cs, hCs0, ?_⟩
  intro P δ p hv hreg hw hcr hLS hδ0 hδ2 hXq hTCs hu husq hint hintF hintX
  obtain ⟨Esm, hEsm, hdg⟩ := hdiag P hv hreg hw hcr
  have hTpos : (0:ℝ) < P.T := hreg.T_pos
  have hQ3 : (3:ℝ) ≤ P.Q := hv.Q_ge
  have hQpos : (0:ℝ) < P.Q := by linarith
  have hQ2 : (0:ℝ) < P.Q ^ 2 := pow_pos hQpos 2
  have hSpos : (0:ℝ) < sumA2gQ P := by
    have h := sumA2gQ_lower_const P hv hreg hw
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    nlinarith [h]
  have hTS : (0:ℝ) < P.T / Real.pi * sumA2gQ P :=
    mul_pos (div_pos hTpos Real.pi_pos) hSpos
  have hCsT : Cs / P.T < 1 := (div_lt_one hTpos).mpr hTCs
  have hEs1 : |Esm| < 1 := lt_of_le_of_lt hEsm hCsT
  have hDpos : (0:ℝ) < ∫ s in Set.univ, P.gQ s * (normA2 P s + normB2 P s) := by
    rw [MeasureTheory.setIntegral_univ, hdg]
    exact mul_pos hTS (by linarith [(abs_lt.mp hEs1).1])
  have hphi := phiQ_sq_integrable P hv hw
  have hLHS : famSum P (fun _ χ => parInd p χ * Mform P (PXchi P χ) (PXchi P χ))
      = famSum P (fun _ χ =>
          parInd p χ * ∫ s in Set.univ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) := by
    unfold famSum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    show parInd p χ * Mform P (PXchi P χ) (PXchi P χ)
        = parInd p χ * ∫ s in Set.univ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2
    rw [lemma41_parseval_diag P (PXchi P χ) hphi (hu _ χ) (husq _ χ),
      MeasureTheory.setIntegral_univ]
  have hcons := family_consumption_par P hv hLS p Set.univ MeasurableSet.univ
    hDpos hint hintF hintX
  have hb1 := budget_par_le P hδ2 hXq (by linarith : (1:ℝ) ≤ P.Q)
  have hb3 : (∫ s in Set.univ, P.gQ s * (normA2 P s + normB2 P s))
      ≤ P.T / Real.pi * sumA2gQ P * (1 + Cs / P.T) := by
    rw [MeasureTheory.setIntegral_univ, hdg]
    exact mul_le_mul_of_nonneg_left
      (by linarith [le_trans (le_abs_self Esm) hEsm]) hTS.le
  have hrp0 : (0:ℝ) ≤ Real.rpow P.Q (-δ) := Real.rpow_nonneg hQpos.le _
  have hnn1 : (0:ℝ) ≤ P.Q ^ 2 / 2 * (1 + 10 * Real.rpow P.Q (-δ)) := by positivity
  have hrho0 : (0:ℝ) ≤ rhoU P Set.univ := rhoU_nonneg P Set.univ MeasurableSet.univ
  have hA : sieveBudgetQPar P * (1 + rhoU P Set.univ)
      ≤ (P.Q ^ 2 / 2 * (1 + 10 * Real.rpow P.Q (-δ))) * (1 + rhoU P Set.univ) :=
    mul_le_mul_of_nonneg_right hb1 (by linarith)
  have hfin : sieveBudgetQPar P * (1 + rhoU P Set.univ)
        * (∫ s in Set.univ, P.gQ s * (normA2 P s + normB2 P s))
      ≤ (P.Q ^ 2 / 2 * (1 + 10 * Real.rpow P.Q (-δ))) * (1 + rhoU P Set.univ)
          * (P.T / Real.pi * sumA2gQ P * (1 + Cs / P.T)) :=
    mul_le_mul hA hb3 hDpos.le (mul_nonneg hnn1 (by linarith))
  rw [hLHS]
  refine le_trans (le_trans hcons hfin) (le_of_eq ?_)
  ring

end Cor3Reflected

/-! ## 4. The PP block of the Frobenius assembly for a parity family, at `Q²/2` -/

namespace Cor3Reflected
open Zones Payoff FrobAssembly

/-- **Parity twin of `FrobAssembly.famPP_le_sieve`: the PP block of a PARITY family is
`Q²/2`, not `Q²`.** For `F` one of Corollary 3's parity families (class `p`):

`Σ_{χ∈F} 𝓜[P_χ,P_χ] ≤ (Q²/2)(T/π)·(½ℒ(aL)²(K0+K1)(v_design) + C_M L²)·(1+10Q^{−δ})(1+ρ_ℝ)(1+Cs/T)`.

The full family's `famPP_le_sieve` has `Q²` here, and the tree currently spends it on the
parity families too (`familySum_le_famSum`), which against `|𝔉^±| = ½|𝔉| + O(Q)` is exactly the
`2C` of `CfamEven`/`CfamEvenDyadic`. With `Q²/2` the parity out-zone constant is the FULL `C`.
This is the input a Corollary 3″ assembly (`A4_eventually` at `F.Cconst / 2`) would consume. -/
theorem famPP_le_sieve_par (c₀ : ℝ) :
    ∃ Cs CM : ℝ, 0 < Cs ∧ 0 < CM ∧
      ∀ (P : ParamsQ) (δ : ℝ) (F : Family) (p : ℕ),
        (∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p)) →
        ∀ (Qn : ℕ), P.Valid → 8 * P.w ≤ P.LB →
        (8 : ℝ) ≤ P.LB → P.cWin ≤ c₀ → 0 < δ → δ ≤ 2 → P.XQ ≤ Real.rpow P.Q (2 - δ) →
        Cs < P.T → Qn ≤ ⌊P.Q⌋₊ →
        familySum F Qn (fun _q χ => Mform P (PXchi P χ) (PXchi P χ))
          ≤ P.Q ^ 2 / 2 * (P.T / Real.pi)
              * (P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2
                  + CM * P.LB ^ 2)
              * ((1 + 10 * Real.rpow P.Q (-δ)) * (1 + rhoU P Set.univ) * (1 + Cs / P.T)) := by
  obtain ⟨Cs, hCs0, hpt⟩ := family_le_diagonal_pointwise_par c₀
  obtain ⟨CM, hCM0, hclose⟩ := sumA2gQ_close
  refine ⟨Cs, CM, hCs0, hCM0, ?_⟩
  intro P δ F p hFp Qn hP hw hL8 hcr hδ0 hδ2 hXQ hTCs hQn
  have hreg : RegimeQ P := regimeQ_of hP hL8
  have hphi := phiQ_sq_integrable P hP hw
  obtain ⟨-, -, hintK, -, -, hintAB⟩ := rho_integrability P hP hw
  have h1 := familySum_le_famSum_parInd P F p hFp Qn hQn
    (fun _q χ => Mform P (PXchi P χ) (PXchi P χ))
    (fun q χ => lemma41_MPP_nonneg P χ hphi (PXchi_integrableOn P χ)
      (PXchi_sq_integrableOn P χ))
  have h2 := hpt P δ p hP hreg hw hcr largeSieveParity_holds hδ0 hδ2 hXQ hTCs
    (fun q χ => PXchi_integrableOn P χ) (fun q χ => PXchi_sq_integrableOn P χ)
    hintAB.integrableOn (fun q χ => gQ_Fwin_PXchi_integrableOn hP hw χ) hintK.integrableOn
  have hsum := hclose P hP hw hL8
  have hsum' : sumA2gQ P ≤ (∫ y in (0:ℝ)..P.LB, P.gQ y * y) + CM * P.LB ^ 2 := by
    linarith [(abs_le.mp hsum).2]
  rw [FrobAssembly.intervalIntegral_gQ_mul_eq hP hw] at hsum'
  have hfac : (0 : ℝ) ≤ (1 + 10 * Real.rpow P.Q (-δ)) * (1 + rhoU P Set.univ)
      * (1 + Cs / P.T) := by
    have hrp0 : (0:ℝ) ≤ Real.rpow P.Q (-δ) := Real.rpow_nonneg (by linarith [hP.Q_ge]) _
    have hrho0 : (0:ℝ) ≤ rhoU P Set.univ := rhoU_nonneg P Set.univ MeasurableSet.univ
    have hT0 : (0:ℝ) < P.T := hP.T_pos
    have : (0:ℝ) ≤ Cs / P.T := div_nonneg hCs0.le hT0.le
    positivity
  have hQT : (0 : ℝ) ≤ P.Q ^ 2 / 2 * (P.T / Real.pi) := by
    have hT0 : (0:ℝ) < P.T := hP.T_pos
    positivity
  calc familySum F Qn (fun _q χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ famSum P (fun _q χ => parInd p χ * Mform P (PXchi P χ) (PXchi P χ)) := h1
    _ ≤ P.Q ^ 2 / 2 * (P.T / Real.pi) * sumA2gQ P
          * ((1 + 10 * Real.rpow P.Q (-δ)) * (1 + rhoU P Set.univ) * (1 + Cs / P.T)) := h2
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hfac
        exact mul_le_mul_of_nonneg_left hsum' hQT

end Cor3Reflected
end ZetaQ
