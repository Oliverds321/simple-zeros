/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaQ.Budget

/-!
# Row 9 (family): the cross term `Σ_χ 𝓜[μ_χ, P_χ]` — part A, the decomposition.

`μ_χ = (log q)/(2π) + m_κ` with `m_κ = muq κ 1` q-free, so the family sum of the cross term is
`(1/2π)·𝓜[1, PXc cLog] + 𝓜[m₀, PXc cEven] + 𝓜[m₁, PXc cOdd]` with the three WEIGHTED family
coefficient sequences `cLog`, `cEven`, `cOdd`.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction
open MeasureTheory Finset

namespace ZetaQ
namespace FamRows

open Zeta23.ThmE Zeta23.PrimeSide

/-! ## A1. The per-character μ-decomposition -/

/-- `μ_χ(τ) = (log q)/(2π) + m_κ(τ)`, `m_κ := muq κ 1`, q-FREE. -/
theorem muDensity_eq_log_add_m {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    muDensity q χ τ = Real.log q / (2 * Real.pi) + muq (parity χ) 1 τ := by
  unfold muDensity Zeta23.ThmE.muq
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  rw [Real.log_div hq0.ne' Real.pi_pos.ne', Nat.cast_one,
    Real.log_div one_ne_zero Real.pi_pos.ne', Real.log_one]
  ring

/-! ## A2. Linearity of `PXc` in the coefficient sequence -/

theorem PXc_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℕ → ℂ) (X τ : ℝ) :
    PXc (fun n => ∑ i ∈ s, c i n) X τ = ∑ i ∈ s, PXc (c i) X τ := by
  unfold PXc
  simp only [Finset.mul_sum, Finset.sum_mul, Complex.re_sum]
  rw [Finset.sum_comm]

theorem PXc_real_smul (w : ℝ) (c : ℕ → ℂ) (X τ : ℝ) :
    PXc (fun n => (w : ℂ) * c n) X τ = w * PXc c X τ := by
  unfold PXc
  have h : ∀ n : ℕ, ((Λ n : ℝ) : ℂ) * ((w : ℂ) * c n) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)
      = (w : ℂ) * (((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)) := by
    intro n; ring
  simp only [h, ← Finset.mul_sum, Complex.re_ofReal_mul]
  ring

theorem PXc_continuous (c : ℕ → ℂ) (X : ℝ) : Continuous (PXc c X) := by
  unfold PXc
  apply Continuous.mul continuous_const
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro n hn
  apply Continuous.mul continuous_const
  exact Continuous.cpow continuous_const (by fun_prop) (by
    intro τ; left; simp only [Complex.natCast_re]; exact_mod_cast (Finset.mem_Ioc.mp hn).1)

/-! ## A3. `Mform` is additive in finite sums (second slot) -/

theorem Mform_sum_right {Φ : ℝ → ℝ} {T : ℝ} (hΦ : Continuous Φ) {u : ℝ → ℝ} (hu : Continuous u)
    {ι : Type*} (s : Finset ι) (v : ι → ℝ → ℝ) (hv : ∀ i ∈ s, Continuous (v i)) :
    Zeta23.PrimeSide.Mform Φ T u (fun τ => ∑ i ∈ s, v i τ)
      = ∑ i ∈ s, Zeta23.PrimeSide.Mform Φ T u (v i) := by
  unfold Zeta23.PrimeSide.Mform
  rw [← integral_finsetSum s (f := fun i (z : ℝ × ℝ) => Φ (z.1 - z.2) ^ 2 * u z.1 * v i z.2)
    (fun i hi => Mform_integrableOn hΦ hu (hv i hi))]
  congr 1; funext z; rw [Finset.mul_sum]

/-! ## A4. The weighted family coefficient sequences -/

/-- `Σ_{q ∈ 𝔉} log q · Σ*_χ χ(n)`. -/
def cLog (F : Family) (Qn : ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ F.moduli Qn, ((Real.log q : ℝ) : ℂ) * primLinSum q n

/-- `Σ_{q ∈ 𝔉} Σ_{χ even prim} χ(n)`. -/
def cEven (F : Family) (Qn : ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q)

/-- `Σ_{q ∈ 𝔉} Σ_{χ odd prim} χ(n)`. -/
def cOdd (F : Family) (Qn : ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q)

/-! ## A5. The pointwise identity for the family sum -/

theorem inner_mu_P_pointwise (P : ParamsQ) {q : ℕ} (hq : 1 ≤ q) (τ τ' : ℝ) :
    ∑ χ ∈ primitiveChars q, muDensity q χ τ * Zones.PXchi P χ τ'
      = (1 / (2 * Real.pi)) * (Real.log q * PXc (fun n => primLinSum q n) P.XQ τ')
        + muq 0 1 τ * PXc (fun n => ∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q)) P.XQ τ'
        + muq 1 1 τ * PXc (fun n => ∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q)) P.XQ τ' := by
  letI := Classical.decEq (DirichletCharacter ℂ q)
  have hsplit : ∀ χ ∈ primitiveChars q, muDensity q χ τ * Zones.PXchi P χ τ'
      = (Real.log q / (2 * Real.pi)) * Zones.PXchi P χ τ'
        + muq (parity χ) 1 τ * Zones.PXchi P χ τ' := by
    intro χ _
    rw [muDensity_eq_log_add_m hq χ τ]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- the linear piece
  have hlin : ∑ χ ∈ primitiveChars q, Zones.PXchi P χ τ'
      = PXc (fun n => primLinSum q n) P.XQ τ' := by
    unfold primLinSum
    rw [PXc_finset_sum]
    rfl
  -- the parity split
  have hpar : ∑ χ ∈ primitiveChars q, muq (parity χ) 1 τ * Zones.PXchi P χ τ'
      = muq 0 1 τ * PXc (fun n => ∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q)) P.XQ τ'
        + muq 1 1 τ * PXc (fun n => ∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q)) P.XQ τ' := by
    rw [← primitiveCharsEven_union_odd q, Finset.sum_union (primitiveCharsEven_disjoint_odd q)]
    have hE : ∑ χ ∈ primitiveCharsEven q, muq (parity χ) 1 τ * Zones.PXchi P χ τ'
        = muq 0 1 τ * ∑ χ ∈ primitiveCharsEven q, Zones.PXchi P χ τ' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [(mem_primitiveCharsEven_iff χ).mp hχ |>.2]
    have hO : ∑ χ ∈ primitiveCharsOdd q, muq (parity χ) 1 τ * Zones.PXchi P χ τ'
        = muq 1 1 τ * ∑ χ ∈ primitiveCharsOdd q, Zones.PXchi P χ τ' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [(mem_primitiveCharsOdd_iff χ).mp hχ |>.2]
    rw [hE, hO, PXc_finset_sum, PXc_finset_sum]
    rfl
  rw [hlin, hpar]
  ring

theorem fam_mu_P_pointwise (P : ParamsQ) (F : Family) (Qn : ℕ) (τ τ' : ℝ) :
    ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q, muDensity q χ τ * Zones.PXchi P χ τ'
      = (1 / (2 * Real.pi)) * PXc (cLog F Qn) P.XQ τ'
        + muq 0 1 τ * PXc (cEven F Qn) P.XQ τ' + muq 1 1 τ * PXc (cOdd F Qn) P.XQ τ' := by
  have hq : ∀ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q, muDensity q χ τ * Zones.PXchi P χ τ'
      = (1 / (2 * Real.pi)) * (Real.log q * PXc (fun n => primLinSum q n) P.XQ τ')
        + muq 0 1 τ * PXc (fun n => ∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q)) P.XQ τ'
        + muq 1 1 τ * PXc (fun n => ∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q)) P.XQ τ' :=
    fun q hq => inner_mu_P_pointwise P (one_le_of_mem_moduli hq) τ τ'
  rw [Finset.sum_congr rfl hq]
  unfold cLog cEven cOdd
  rw [PXc_finset_sum, PXc_finset_sum, PXc_finset_sum]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, PXc_real_smul]


/-! ## B1. The oscillatory bound for `𝓜[u, PXc c X]` with an ARBITRARY complex coefficient
sequence `c` — [R]'s `cross_muP_core_W` mechanism (`Mform_mu_PXc_eq` + `abs_Mform_cos_phase_le`),
with `|c_n.re|, |c_n.im| ≤ ‖c_n‖` in place of `‖c_n‖ ≤ 1`, and `Λ(n)/log n ≤ 1`. -/

theorem abs_Mform_PXc_le {Φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hΦ : ContDiff ℝ 1 Φ)
    (hΦint : Integrable (fun x => Φ x ^ 2)) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {B D : ℝ}
    (hB : ∀ τ ∈ Set.Icc T (2 * T), |u τ| ≤ B) (hD : ∀ τ ∈ Set.Icc T (2 * T), |deriv u τ| ≤ D)
    (hBD : 0 ≤ 4 * B + D * T) (c : ℕ → ℂ) (X : ℝ) :
    |Zeta23.PrimeSide.Mform Φ T u (PXc c X)|
      ≤ (2 / Real.pi) * ((4 * B + D * T) * ∫ x, Φ x ^ 2)
          * ∑ n ∈ Finset.Ioc 1 ⌊X⌋₊, ‖c n‖ / Real.sqrt (n : ℝ) := by
  have hS0 : 0 ≤ ∫ x, Φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  set S : ℝ := ∫ x, Φ x ^ 2 with hSdef
  set K : ℝ := (4 * B + D * T) * S with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hBD hS0
  have hosc : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      |(-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))
          * ((c n).re * Zeta23.PrimeSide.Mform Φ T u (fun t => Real.cos (t * Real.log n))
             + (c n).im * Zeta23.PrimeSide.Mform Φ T u (fun t => Real.sin (t * Real.log n)))|
        ≤ (1 / Real.pi) * (2 * K) * (if 2 ≤ n then ‖c n‖ / Real.sqrt (n : ℝ) else 0) := by
    intro n hn
    have ha0 : (0:ℝ) ≤ (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by
        have : 0 < n := (Finset.mem_Ioc.mp hn).1
        omega
      subst hn1
      simp
    · rw [if_pos h2]
      have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hy : 0 < Real.log n := Real.log_pos (by exact_mod_cast h2)
      have hMc := abs_Mform_cos_phase_le hT hΦ hΦint hu hB hD hy.ne' 0
      simp only [add_zero] at hMc
      rw [abs_of_pos hy] at hMc
      have hsin_eq : Zeta23.PrimeSide.Mform Φ T u (fun t => Real.sin (t * Real.log n))
          = Zeta23.PrimeSide.Mform Φ T u
              (fun t => Real.cos (t * Real.log n + -(Real.pi / 2))) := by
        unfold Zeta23.PrimeSide.Mform
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only []
        rw [show z.2 * Real.log n + -(Real.pi / 2) = z.2 * Real.log n - Real.pi / 2 by ring,
          Real.cos_sub_pi_div_two]
      have hMs := abs_Mform_cos_phase_le hT hΦ hΦint hu hB hD hy.ne' (-(Real.pi / 2))
      rw [abs_of_pos hy] at hMs
      rw [← hsin_eq] at hMs
      have hre : |(c n).re| ≤ ‖c n‖ := Complex.abs_re_le_norm _
      have him : |(c n).im| ≤ ‖c n‖ := Complex.abs_im_le_norm _
      have hKb : (4 * B + D * T) * S / Real.log n = K / Real.log n := by rw [hKdef]
      rw [abs_mul]
      have h1 : |(c n).re * Zeta23.PrimeSide.Mform Φ T u (fun t => Real.cos (t * Real.log n))
            + (c n).im * Zeta23.PrimeSide.Mform Φ T u (fun t => Real.sin (t * Real.log n))|
          ≤ ‖c n‖ * (2 * (K / Real.log n)) := by
        calc |(c n).re * Zeta23.PrimeSide.Mform Φ T u (fun t => Real.cos (t * Real.log n))
              + (c n).im * Zeta23.PrimeSide.Mform Φ T u (fun t => Real.sin (t * Real.log n))|
            ≤ |(c n).re| * |Zeta23.PrimeSide.Mform Φ T u (fun t => Real.cos (t * Real.log n))|
              + |(c n).im|
                * |Zeta23.PrimeSide.Mform Φ T u (fun t => Real.sin (t * Real.log n))| := by
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_mul]
          _ ≤ ‖c n‖ * (K / Real.log n) + ‖c n‖ * (K / Real.log n) := by
                refine add_le_add (mul_le_mul hre (hMc.trans (le_of_eq hKb)) (abs_nonneg _)
                  (norm_nonneg _)) (mul_le_mul him (hMs.trans (le_of_eq hKb)) (abs_nonneg _)
                    (norm_nonneg _))
          _ = ‖c n‖ * (2 * (K / Real.log n)) := by ring
      have hΛ : (Λ n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      have hΛ0 : (0:ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have hconv : (n : ℝ) ^ (-(1/2 : ℝ)) = 1 / Real.sqrt (n : ℝ) := by
        rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
      have hsq0 : (0:ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      calc |(-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))| * |_|
          ≤ (1 / Real.pi * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))
              * (‖c n‖ * (2 * (K / Real.log n))) := by
            rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi),
              abs_of_nonneg ha0]
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (1 / Real.pi) * (2 * K)
              * (((Λ n : ℝ) / Real.log n) * (‖c n‖ / Real.sqrt (n : ℝ))) := by
            rw [hconv]; field_simp
        _ ≤ (1 / Real.pi) * (2 * K) * (1 * (‖c n‖ / Real.sqrt (n : ℝ))) := by
            gcongr
            exact (div_le_one hy).mpr hΛ
        _ = (1 / Real.pi) * (2 * K) * (‖c n‖ / Real.sqrt (n : ℝ)) := by ring
  rw [Mform_mu_PXc_eq hΦ.continuous hu.continuous]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hosc).trans ?_)
  rw [← Finset.mul_sum]
  have hsum : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (if 2 ≤ n then ‖c n‖ / Real.sqrt (n : ℝ) else 0)
      = ∑ n ∈ Finset.Ioc 1 ⌊X⌋₊, ‖c n‖ / Real.sqrt (n : ℝ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [hsum]
  apply le_of_eq
  rw [hKdef]; ring

/-! ## B2. The weighted family character sums -/

/-- `Σ_{q ≤ Q} log q · Σ*_χ χ(n)` — the `log q`-weighted family linear sum over `Icc 1 Q`. -/
def famLogLinSum (Q n : ℕ) : ℂ := ∑ q ∈ Finset.Icc 1 Q, ((Real.log q : ℝ) : ℂ) * primLinSum q n

theorem sum_Icc_one_eq_sum_range_succ (k : ℕ) (f : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 k, f q = ∑ i ∈ Finset.range k, f (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hI : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hI, Finset.sum_insert (by simp), add_comm]

theorem log_natCast_mono {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

/-- **Abel summation of `lemma5_2_crude_linear`**:
`‖Σ_{q≤Q} log q · Σ*_χ χ(n)‖ ≤ Q·τ(n−1)·(1 + log Q)` for `n ≥ 2`. -/
theorem famLogLinSum_norm_le (Q n : ℕ) (hn : 2 ≤ n) :
    ‖famLogLinSum Q n‖ ≤ (Q : ℝ) * (tau (n - 1) : ℝ) * (1 + Real.log Q) := by
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQ1
  · subst hQ0; simp [famLogLinSum]
  have hτ : (0:ℝ) ≤ (tau (n - 1) : ℝ) := Nat.cast_nonneg _
  have hlogQ : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  have hpart : ∀ k : ℕ, ∑ i ∈ Finset.range k, primLinSum (i + 1) n = famLinSum k n := by
    intro k; unfold famLinSum; rw [sum_Icc_one_eq_sum_range_succ]
  have hA : ∀ k : ℕ, ‖famLinSum k n‖ ≤ (k : ℝ) * (tau (n - 1) : ℝ) :=
    fun k => lemma5_2_crude_linear k n hn
  have hbp := Finset.sum_range_by_parts (fun i : ℕ => Real.log ((i + 1 : ℕ) : ℝ))
    (fun i : ℕ => primLinSum (i + 1) n) Q
  have hlhs : famLogLinSum Q n
      = ∑ i ∈ Finset.range Q, Real.log ((i + 1 : ℕ) : ℝ) • primLinSum (i + 1) n := by
    unfold famLogLinSum
    rw [sum_Icc_one_eq_sum_range_succ]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.real_smul]
  rw [hlhs, hbp]
  simp only [hpart]
  have hQ1' : Q - 1 + 1 = Q := Nat.sub_add_cancel hQ1
  rw [hQ1']
  have hd : ∀ i : ℕ, 0 ≤ Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ) ∧
      (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) * ((i + 1 : ℕ) : ℝ) ≤ 1 := by
    intro i
    have h1 : (0:ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < ((i + 1 + 1 : ℕ) : ℝ) := by positivity
    constructor
    · exact sub_nonneg.mpr (Real.log_le_log h1 (by exact_mod_cast Nat.le_succ _))
    · rw [← Real.log_div h2.ne' h1.ne']
      have hx : (0:ℝ) < ((i + 1 + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) := div_pos h2 h1
      have := Real.log_le_sub_one_of_pos hx
      have e : (((i + 1 + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) - 1) * ((i + 1 : ℕ) : ℝ) = 1 := by
        push_cast; field_simp; ring
      nlinarith [this, h1]
  have hsum2 : ‖∑ i ∈ Finset.range (Q - 1),
      (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) • famLinSum (i + 1) n‖
      ≤ ((Q - 1 : ℕ) : ℝ) * (tau (n - 1) : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range (Q - 1),
        ‖(Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) • famLinSum (i + 1) n‖
          ≤ (tau (n - 1) : ℝ) := by
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd i).1]
      calc (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) * ‖famLinSum (i + 1) n‖
          ≤ (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ))
              * (((i + 1 : ℕ) : ℝ) * (tau (n - 1) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hA (i + 1)) (hd i).1
        _ = ((Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) * ((i + 1 : ℕ) : ℝ))
              * (tau (n - 1) : ℝ) := by ring
        _ ≤ 1 * (tau (n - 1) : ℝ) := mul_le_mul_of_nonneg_right (hd i).2 hτ
        _ = (tau (n - 1) : ℝ) := one_mul _
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum1 : ‖Real.log (Q : ℝ) • famLinSum Q n‖
      ≤ Real.log Q * ((Q : ℝ) * (tau (n - 1) : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlogQ]
    exact mul_le_mul_of_nonneg_left (hA Q) hlogQ
  have hQm : ((Q - 1 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast Nat.sub_le Q 1
  calc ‖Real.log (Q : ℝ) • famLinSum Q n - ∑ i ∈ Finset.range (Q - 1),
        (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) • famLinSum (i + 1) n‖
      ≤ ‖Real.log (Q : ℝ) • famLinSum Q n‖ + ‖∑ i ∈ Finset.range (Q - 1),
        (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) • famLinSum (i + 1) n‖ :=
        norm_sub_le _ _
    _ ≤ Real.log Q * ((Q : ℝ) * (tau (n - 1) : ℝ)) + ((Q - 1 : ℕ) : ℝ) * (tau (n - 1) : ℝ) :=
        add_le_add hsum1 hsum2
    _ ≤ Real.log Q * ((Q : ℝ) * (tau (n - 1) : ℝ)) + (Q : ℝ) * (tau (n - 1) : ℝ) := by
        gcongr
    _ = (Q : ℝ) * (tau (n - 1) : ℝ) * (1 + Real.log Q) := by ring


/-! ## C. Bounds on the three weighted family sums (`n ≥ 2`) -/

/-- `Σ_{Icc 1 N} g = g 1 + Σ_{Icc 2 N} g` for `N ≥ 1` (complex-valued). -/
theorem sum_Icc_one_eq_add (N : ℕ) (hN : 1 ≤ N) (g : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 N, g q = g 1 + ∑ q ∈ Finset.Icc 2 N, g q := by
  rw [Icc_one_eq_insert N hN, Finset.sum_insert (by simp)]

/-- dyadic differencing (complex-valued). -/
theorem sum_Ioc_half_eq (N : ℕ) (g : ℕ → ℂ) :
    ∑ q ∈ Finset.Ioc (N / 2) N, g q
      = ∑ q ∈ Finset.Icc 1 N, g q - ∑ q ∈ Finset.Icc 1 (N / 2), g q := by
  have hcons := Finset.sum_Ioc_consecutive g (Nat.zero_le (N / 2)) (Nat.div_le_self N 2)
  rw [Icc_one_eq_Ioc_zero', Icc_one_eq_Ioc_zero', ← hcons]
  ring

/-- `‖cLog F Qn n‖ ≤ (3/2)·Qn·τ(n−1)·(1 + log Qn)` for `n ≥ 2`, both families. -/
theorem cLog_norm_le (F : Family) (Qn n : ℕ) (hn : 2 ≤ n) :
    ‖cLog F Qn n‖ ≤ 3 / 2 * (Qn : ℝ) * (tau (n - 1) : ℝ) * (1 + Real.log Qn) := by
  have hτ : (0:ℝ) ≤ (tau (n - 1) : ℝ) := Nat.cast_nonneg _
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlogQ : 0 ≤ Real.log Qn := Real.log_natCast_nonneg Qn
  -- `cLog` reads `F` only through `F.moduli`, and Corollary 3's four families reuse the two
  -- modulus ranges verbatim, so there are still only two cases to do.
  have hred : cLog F Qn n = cLog Family.qle Qn n ∨ cLog F Qn n = cLog Family.dyadic Qn n := by
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
  rcases hred with hred | hred <;> rw [hred]
  case inl =>
      rcases Nat.eq_zero_or_pos Qn with h0 | h1
      · subst h0
        simp [cLog, Family.moduli]
      · have heq : cLog Family.qle Qn n = famLogLinSum Qn n := by
          unfold cLog famLogLinSum
          rw [sum_Icc_one_eq_add Qn h1]
          simp [Family.moduli]
        rw [heq]
        refine (famLogLinSum_norm_le Qn n hn).trans ?_
        nlinarith [mul_nonneg (mul_nonneg hQ hτ) (by linarith : (0:ℝ) ≤ 1 + Real.log Qn)]
  case inr =>
      have heq : cLog Family.dyadic Qn n = famLogLinSum Qn n - famLogLinSum (Qn / 2) n := by
        unfold cLog famLogLinSum
        show ∑ q ∈ Finset.Ioc (Qn / 2) Qn, ((Real.log q : ℝ) : ℂ) * primLinSum q n = _
        rw [sum_Ioc_half_eq]
      rw [heq]
      have h1 := famLogLinSum_norm_le Qn n hn
      have h2 := famLogLinSum_norm_le (Qn / 2) n hn
      have hhalf : ((Qn / 2 : ℕ) : ℝ) ≤ (Qn : ℝ) / 2 := Nat.cast_div_le
      have hlog : Real.log ((Qn / 2 : ℕ) : ℝ) ≤ Real.log Qn := log_natCast_mono (Nat.div_le_self Qn 2)
      have hlog0 : 0 ≤ Real.log ((Qn / 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
      calc ‖famLogLinSum Qn n - famLogLinSum (Qn / 2) n‖
          ≤ ‖famLogLinSum Qn n‖ + ‖famLogLinSum (Qn / 2) n‖ := norm_sub_le _ _
        _ ≤ (Qn : ℝ) * (tau (n - 1) : ℝ) * (1 + Real.log Qn)
              + ((Qn / 2 : ℕ) : ℝ) * (tau (n - 1) : ℝ) * (1 + Real.log ((Qn / 2 : ℕ) : ℝ)) :=
            add_le_add h1 h2
        _ ≤ (Qn : ℝ) * (tau (n - 1) : ℝ) * (1 + Real.log Qn)
              + (Qn : ℝ) / 2 * (tau (n - 1) : ℝ) * (1 + Real.log Qn) := by
            gcongr
        _ = 3 / 2 * (Qn : ℝ) * (tau (n - 1) : ℝ) * (1 + Real.log Qn) := by ring

/-- The `q = 1` parity-twisted term: `Σ*_{χ mod 1} χ(−1)χ(n)χ̄(1) = 1`. -/
theorem primPairSumNeg_one (n : ℕ) : primPairSumNeg 1 n 1 = 1 := by
  rw [primPairSumNeg, primitiveChars_one, Finset.sum_singleton]
  have h1 : ((n : ℕ) : ZMod 1) = 1 := Subsingleton.elim _ _
  have h2 : ((1 : ℕ) : ZMod 1) = 1 := Subsingleton.elim _ _
  have h3 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [h1, h2, h3]
  simp

/-- The even and odd halves, per modulus, in terms of `primLinSum` and the twisted sum:
`Σ_{χ even} χ(n) = (Σ*χ(n) + Σ*χ(−1)χ(n))/2`, `Σ_{χ odd} χ(n) = (Σ*χ(n) − Σ*χ(−1)χ(n))/2`. -/
theorem sum_even_eq (q n : ℕ) :
    ∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q) = (primLinSum q n + primPairSumNeg q n 1) / 2 := by
  have h := primPairSum_even_eq q n 1
  have hE : primPairSumEven q n 1 = ∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q) := by
    unfold primPairSumEven
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Nat.cast_one, map_one, map_one, mul_one]
  have hL : primPairSum q n 1 = primLinSum q n := by
    unfold primPairSum primLinSum
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Nat.cast_one, map_one, map_one, mul_one]
  rw [← hE, h, hL]

theorem sum_odd_eq (q n : ℕ) :
    ∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q) = (primLinSum q n - primPairSumNeg q n 1) / 2 := by
  have h := primPairSum_odd_eq q n 1
  have hO : primPairSumOdd q n 1 = ∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q) := by
    unfold primPairSumOdd
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Nat.cast_one, map_one, map_one, mul_one]
  have hL : primPairSum q n 1 = primLinSum q n := by
    unfold primPairSum primLinSum
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Nat.cast_one, map_one, map_one, mul_one]
  rw [← hO, h, hL]

/-- The family-aggregated twisted sum `Σ_{q ∈ 𝔉} Σ*_χ χ(−1)χ(n)`. -/
def famNegSum (F : Family) (Qn n : ℕ) : ℂ := ∑ q ∈ F.moduli Qn, primPairSumNeg q n 1

/-- `‖Σ_{q ∈ 𝔉} Σ*_χ χ(−1)χ(n)‖ ≤ (3/2)·Qn·τ(n+1) + 1` (Lemma 5.2′, both families). -/
theorem famNegSum_norm_le (F : Family) (Qn n : ℕ) (hn : 1 ≤ n) :
    ‖famNegSum F Qn n‖ ≤ 3 / 2 * (Qn : ℝ) * (tau (n + 1) : ℝ) + 1 := by
  have hτ : (0:ℝ) ≤ (tau (n + 1) : ℝ) := Nat.cast_nonneg _
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  -- as in `cLog_norm_le`: `famNegSum` reads `F` only through `F.moduli`.
  have hred : famNegSum F Qn n = famNegSum Family.qle Qn n
      ∨ famNegSum F Qn n = famNegSum Family.dyadic Qn n := by
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
  rcases hred with hred | hred <;> rw [hred]
  case inl =>
      rcases Nat.eq_zero_or_pos Qn with h0 | h1
      · subst h0
        simp [famNegSum, Family.moduli]
      · have heq : famNegSum Family.qle Qn n = famPairSumNeg Qn n 1 - 1 := by
          unfold famNegSum famPairSumNeg
          rw [sum_Icc_one_eq_add Qn h1, primPairSumNeg_one]
          show ∑ q ∈ Finset.Icc 2 Qn, primPairSumNeg q n 1 = _
          ring
        rw [heq]
        have h5 := lemma5_2'_crude Qn n 1 hn le_rfl
        calc ‖famPairSumNeg Qn n 1 - 1‖ ≤ ‖famPairSumNeg Qn n 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ (Qn : ℝ) * (tau (n + 1) : ℝ) + 1 := by rw [norm_one]; linarith
          _ ≤ 3 / 2 * (Qn : ℝ) * (tau (n + 1) : ℝ) + 1 := by nlinarith [mul_nonneg hQ hτ]
  case inr =>
      have heq : famNegSum Family.dyadic Qn n = famPairSumNegDyadic Qn n 1 := rfl
      rw [heq]
      have h5 := lemma5_2'_crude_dyadic Qn n 1 hn le_rfl
      linarith

theorem cEven_eq (F : Family) (Qn n : ℕ) :
    cEven F Qn n = (famChiSum F Qn n + famNegSum F Qn n) / 2 := by
  unfold cEven famChiSum famNegSum
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [sum_even_eq]
  rfl

theorem cOdd_eq (F : Family) (Qn n : ℕ) :
    cOdd F Qn n = (famChiSum F Qn n - famNegSum F Qn n) / 2 := by
  unfold cOdd famChiSum famNegSum
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [sum_odd_eq]
  rfl

/-- `‖cEven F Qn n‖ ≤ (3/4)·Qn·(τ(n−1) + τ(n+1)) + 1` for `n ≥ 2`. -/
theorem cEven_norm_le (F : Family) (Qn n : ℕ) (hn : 2 ≤ n) :
    ‖cEven F Qn n‖ ≤ 3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) + 1 := by
  rw [cEven_eq, norm_div, Complex.norm_ofNat]
  have h1 := famChiSum_norm_le F Qn n hn
  have h2 := famNegSum_norm_le F Qn n (by omega)
  have h := norm_add_le (famChiSum F Qn n) (famNegSum F Qn n)
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

theorem cOdd_norm_le (F : Family) (Qn n : ℕ) (hn : 2 ≤ n) :
    ‖cOdd F Qn n‖ ≤ 3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) + 1 := by
  rw [cOdd_eq, norm_div, Complex.norm_ofNat]
  have h1 := famChiSum_norm_le F Qn n hn
  have h2 := famNegSum_norm_le F Qn n (by omega)
  have h := norm_sub_le (famChiSum F Qn n) (famNegSum F Qn n)
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-! ## C′. The divisor sums needed -/

/-- `Σ_{n ≤ N} τ(n+1)/√n ≤ 2√2·√(N+1)·(1 + log(N+1))`. -/
theorem sum_tau_succ_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) := by
  classical
  have hterm : ∀ n ∈ Finset.Ioc 0 N, (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)
      ≤ Real.sqrt 2 * ((tau (n + 1) : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hs1 : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hτ : (0:ℝ) ≤ (tau (n + 1) : ℝ) := Nat.cast_nonneg _
    have hle : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ Real.sqrt 2 * Real.sqrt n := by
      rw [← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt; push_cast; linarith
    have key : 1 / Real.sqrt (n : ℝ) ≤ Real.sqrt 2 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ hs0 hs1]; linarith
    calc (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ) = (tau (n + 1) : ℝ) * (1 / Real.sqrt (n : ℝ)) := by
          ring
      _ ≤ (tau (n + 1) : ℝ) * (Real.sqrt 2 / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left key hτ
      _ = Real.sqrt 2 * ((tau (n + 1) : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hre : ∑ n ∈ Finset.Ioc 0 N, (tau (n + 1) : ℝ) / Real.sqrt ((n + 1 : ℕ) : ℝ)
      = ∑ m ∈ (Finset.Ioc 0 N).image (fun n => n + 1), (tau m : ℝ) / Real.sqrt (m : ℝ) := by
    rw [Finset.sum_image (fun x _ y _ h => Nat.succ_injective h)]
  rw [hre]
  have hsub : (Finset.Ioc 0 N).image (fun n => n + 1) ⊆ Finset.Icc 1 (N + 1) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hmono : ∑ m ∈ (Finset.Ioc 0 N).image (fun n => n + 1), (tau m : ℝ) / Real.sqrt (m : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 (N + 1), (tau m : ℝ) / Real.sqrt (m : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
  have hS := sum_tau_div_sqrt_le (N + 1)
  push_cast at hS
  have h2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  calc Real.sqrt 2 * ∑ m ∈ (Finset.Ioc 0 N).image (fun n => n + 1), (tau m : ℝ) / Real.sqrt (m : ℝ)
      ≤ Real.sqrt 2 * (2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (hmono.trans hS) h2
    _ = 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) := by ring


/-! ## D. Assembly — **LEDGER ROW 9, FAMILY-AVERAGED** -/

theorem sum_cLog_div_sqrt_le (F : Family) (Qn N : ℕ) :
    ∑ n ∈ Finset.Ioc 1 N, ‖cLog F Qn n‖ / Real.sqrt (n : ℝ)
      ≤ 3 / 2 * (Qn : ℝ) * (1 + Real.log Qn) * (2 * Real.sqrt N * (1 + Real.log N)) := by
  have hlogQ : 0 ≤ Real.log Qn := Real.log_natCast_nonneg Qn
  have hQ : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  have hstep : ∀ n ∈ Finset.Ioc 1 N, ‖cLog F Qn n‖ / Real.sqrt (n : ℝ)
      ≤ (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn)) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)) := by
    intro n hn
    have h2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    calc ‖cLog F Qn n‖ / Real.sqrt (n : ℝ)
        ≤ (3 / 2 * (Qn : ℝ) * (tau (n - 1) : ℝ) * (1 + Real.log Qn)) / Real.sqrt (n : ℝ) :=
          div_le_div_of_nonneg_right (cLog_norm_le F Qn n h2) hs.le
      _ = (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn)) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)) := by
          ring
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ioc_subset_Ioc (Nat.zero_le 1) le_rfl) (fun n _ _ => by positivity)) ?_
  exact sum_tau_pred_div_sqrt_le N

theorem sum_par_div_sqrt_le (Qn N : ℕ) (c : ℕ → ℂ)
    (hc : ∀ n, 2 ≤ n → ‖c n‖ ≤ 3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) + 1) :
    ∑ n ∈ Finset.Ioc 1 N, ‖c n‖ / Real.sqrt (n : ℝ)
      ≤ 3 / 4 * (Qn : ℝ) * (2 * Real.sqrt N * (1 + Real.log N)
          + 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)))
        + 2 * Real.sqrt N := by
  have hQ : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  have hstep : ∀ n ∈ Finset.Ioc 1 N, ‖c n‖ / Real.sqrt (n : ℝ)
      ≤ 3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
          + (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)) + 1 / Real.sqrt (n : ℝ) := by
    intro n hn
    have h2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    calc ‖c n‖ / Real.sqrt (n : ℝ)
        ≤ (3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) + 1) / Real.sqrt (n : ℝ) :=
          div_le_div_of_nonneg_right (hc n h2) hs.le
      _ = 3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
            + (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)) + 1 / Real.sqrt (n : ℝ) := by
          field_simp
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hsub : Finset.Ioc 1 N ⊆ Finset.Ioc 0 N := Finset.Ioc_subset_Ioc (Nat.zero_le 1) le_rfl
  have hA : ∑ n ∈ Finset.Ioc 1 N, (tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt N * (1 + Real.log N) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity))
      (sum_tau_pred_div_sqrt_le N)
  have hB : ∑ n ∈ Finset.Ioc 1 N, (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity))
      (sum_tau_succ_div_sqrt_le N)
  have hC : ∑ n ∈ Finset.Ioc 1 N, (1 : ℝ) / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt N :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity))
      (sum_one_div_sqrt_le N)
  have h34 : (0:ℝ) ≤ 3 / 4 * (Qn : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hA hB) h34]

/-- **The explicit row-9 bound.**  With `N = ⌊X⌋`, `S₁ = 2√N(1+log N)` (the `τ(n−1)` sum),
`S₂ = 2√2·√(N+1)(1+log(N+1))` (the `τ(n+1)` sum), `S₀ = 2√N`:
`ROW9 = (8bL/π)·(3/2)Q(1+log Q)·S₁ + 8bL·((44/π)l + 24/π)·((3/4)Q(S₁+S₂) + S₀)`. -/
def ROW9 (F : Family) (P : ParamsQ) (Qn : ℕ) : ℝ :=
  8 * P.bQ * P.LB / Real.pi
      * (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn)
          * (2 * Real.sqrt (⌊P.XQ⌋₊ : ℝ) * (1 + Real.log (⌊P.XQ⌋₊ : ℝ))))
    + 8 * P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi)
      * (3 / 4 * (Qn : ℝ) * (2 * Real.sqrt (⌊P.XQ⌋₊ : ℝ) * (1 + Real.log (⌊P.XQ⌋₊ : ℝ))
            + 2 * Real.sqrt 2 * Real.sqrt ((⌊P.XQ⌋₊ : ℝ) + 1)
              * (1 + Real.log ((⌊P.XQ⌋₊ : ℝ) + 1)))
          + 2 * Real.sqrt (⌊P.XQ⌋₊ : ℝ))

theorem T_ge_2pie_of_valid {P : ParamsQ} (hP : P.Valid) : 2 * Real.pi * Real.exp 1 ≤ P.T := by
  have hT : (300:ℝ) ≤ P.T := hP.T_ge300
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  nlinarith [Real.exp_pos 1]

theorem ROW9_nonneg (F : Family) (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) : 0 ≤ ROW9 F P Qn := by
  have hb0 : 0 ≤ P.bQ := hP.bQ_pos.le
  have hL0 : 0 ≤ P.LB := hP.LB_pos.le
  have hl0 : 0 ≤ Zeta23.l P.T := le_trans zero_le_one (one_le_l_of_valid hP)
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hN1 : (1:ℝ) ≤ (⌊P.XQ⌋₊ : ℝ) := by exact_mod_cast Nat.floor_pos.mpr hX1
  have hlogN : 0 ≤ Real.log ((⌊P.XQ⌋₊ : ℝ)) := Real.log_nonneg hN1
  have hlogN1 : 0 ≤ Real.log ((⌊P.XQ⌋₊ : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlogQ : 0 ≤ Real.log (Qn : ℝ) := Real.log_natCast_nonneg Qn
  unfold ROW9
  positivity

/-! ## E′. THE PARITY ROW 9

`fam_mu_P_pointwise` factors the family sum through `cLog`, `cEven`, `cOdd` and is an identity
about the FULL inner sum `Σ*_{χ mod q}`. On ONE parity class the factorisation is strictly
shorter — `μ_χ = log q/2π + muq (parity χ) 1` and `parity χ` is CONSTANT on the class, so

  `Σ_q Σ_{χ ∈ sel q} μ_χ(τ)P_χ(τ′) = (1/2π)·PXc(cLogSel) τ′ + muq κ 1 τ · PXc(cSel) τ′`

with only TWO terms; the opposite parity's `muq` block disappears.

**⚠ THE ONE HONEST DISCREPANCY — the parity bound is against `3·ROW9`, and `ROW9par ≤ ROW9` is
FALSE.** `ROW9` budgets the `log q`-weighted coefficient against the `τ(n−1)` divisor sum only
(`cLog_norm_le` has no `τ(n+1)` term), whereas the parity coefficient `cLogSel` is
`(cLog ± cLogNeg)/2` and `cLogNeg` — the `log q`-weighted TWISTED family sum — is a `τ(n+1)`
object. The parity row therefore spends `(1 + log Q)·Σ τ(n+1)/√n` where `ROW9` has budgeted
only `(1 + log Q)·Σ τ(n−1)/√n`; the saving it gains elsewhere (one of `ROW9`'s two `(44l+24)`
blocks disappears) is `Q`-uniform while the excess grows like `log Q`. `ROW9par ≤ 3·ROW9`
(`ROW9par_le_three_ROW9`) is what is available, and the enlargement is order-preserving:
`ROW9par` has the same `≍ Q·L²·l·√X` shape, so `ROW9_le_simple`'s closed form absorbs it as a
constant. -/

/-! ### E′1. The `log q`-weighted TWISTED family sum -/

/-- `Σ_{q≤Q} log q · Σ*_χ χ(−1)χ(n)` — the twisted mirror of `famLogLinSum`. -/
def famLogNegSum (Q n : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, ((Real.log q : ℝ) : ℂ) * primPairSumNeg q n 1

/-- **Abel summation of `lemma5_2'_crude`**:
`‖Σ_{q≤Q} log q · Σ*_χ χ(−1)χ(n)‖ ≤ Q·τ(n+1)·(1 + log Q)` for `n ≥ 1`.
Line for line `famLogLinSum_norm_le` with the twisted partial sums. -/
theorem famLogNegSum_norm_le (Q n : ℕ) (hn : 1 ≤ n) :
    ‖famLogNegSum Q n‖ ≤ (Q : ℝ) * (tau (n + 1) : ℝ) * (1 + Real.log Q) := by
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQ1
  · subst hQ0; simp [famLogNegSum]
  have hτ : (0:ℝ) ≤ (tau (n + 1) : ℝ) := Nat.cast_nonneg _
  have hlogQ : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  have hpart : ∀ k : ℕ, ∑ i ∈ Finset.range k, primPairSumNeg (i + 1) n 1
      = famPairSumNeg k n 1 := by
    intro k; unfold famPairSumNeg; rw [sum_Icc_one_eq_sum_range_succ]
  have hA : ∀ k : ℕ, ‖famPairSumNeg k n 1‖ ≤ (k : ℝ) * (tau (n + 1) : ℝ) :=
    fun k => lemma5_2'_crude k n 1 hn le_rfl
  have hbp := Finset.sum_range_by_parts (fun i : ℕ => Real.log ((i + 1 : ℕ) : ℝ))
    (fun i : ℕ => primPairSumNeg (i + 1) n 1) Q
  have hlhs : famLogNegSum Q n
      = ∑ i ∈ Finset.range Q, Real.log ((i + 1 : ℕ) : ℝ) • primPairSumNeg (i + 1) n 1 := by
    unfold famLogNegSum
    rw [sum_Icc_one_eq_sum_range_succ]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.real_smul]
  rw [hlhs, hbp]
  simp only [hpart]
  have hQ1' : Q - 1 + 1 = Q := Nat.sub_add_cancel hQ1
  rw [hQ1']
  have hd : ∀ i : ℕ, 0 ≤ Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ) ∧
      (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) * ((i + 1 : ℕ) : ℝ) ≤ 1 := by
    intro i
    have h1 : (0:ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < ((i + 1 + 1 : ℕ) : ℝ) := by positivity
    constructor
    · exact sub_nonneg.mpr (Real.log_le_log h1 (by exact_mod_cast Nat.le_succ _))
    · rw [← Real.log_div h2.ne' h1.ne']
      have hx : (0:ℝ) < ((i + 1 + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) := div_pos h2 h1
      have := Real.log_le_sub_one_of_pos hx
      have e : (((i + 1 + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) - 1) * ((i + 1 : ℕ) : ℝ) = 1 := by
        push_cast; field_simp; ring
      nlinarith [this, h1]
  have hsum2 : ‖∑ i ∈ Finset.range (Q - 1),
      (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) • famPairSumNeg (i + 1) n 1‖
      ≤ ((Q - 1 : ℕ) : ℝ) * (tau (n + 1) : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range (Q - 1),
        ‖(Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ))
            • famPairSumNeg (i + 1) n 1‖ ≤ (tau (n + 1) : ℝ) := by
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd i).1]
      calc (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ))
            * ‖famPairSumNeg (i + 1) n 1‖
          ≤ (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ))
              * (((i + 1 : ℕ) : ℝ) * (tau (n + 1) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hA (i + 1)) (hd i).1
        _ = ((Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ)) * ((i + 1 : ℕ) : ℝ))
              * (tau (n + 1) : ℝ) := by ring
        _ ≤ 1 * (tau (n + 1) : ℝ) := mul_le_mul_of_nonneg_right (hd i).2 hτ
        _ = (tau (n + 1) : ℝ) := one_mul _
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum1 : ‖Real.log (Q : ℝ) • famPairSumNeg Q n 1‖
      ≤ Real.log Q * ((Q : ℝ) * (tau (n + 1) : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlogQ]
    exact mul_le_mul_of_nonneg_left (hA Q) hlogQ
  have hQm : ((Q - 1 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast Nat.sub_le Q 1
  calc ‖Real.log (Q : ℝ) • famPairSumNeg Q n 1 - ∑ i ∈ Finset.range (Q - 1),
        (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ))
          • famPairSumNeg (i + 1) n 1‖
      ≤ ‖Real.log (Q : ℝ) • famPairSumNeg Q n 1‖ + ‖∑ i ∈ Finset.range (Q - 1),
        (Real.log ((i + 1 + 1 : ℕ) : ℝ) - Real.log ((i + 1 : ℕ) : ℝ))
          • famPairSumNeg (i + 1) n 1‖ := norm_sub_le _ _
    _ ≤ Real.log Q * ((Q : ℝ) * (tau (n + 1) : ℝ)) + ((Q - 1 : ℕ) : ℝ) * (tau (n + 1) : ℝ) :=
        add_le_add hsum1 hsum2
    _ ≤ Real.log Q * ((Q : ℝ) * (tau (n + 1) : ℝ)) + (Q : ℝ) * (tau (n + 1) : ℝ) := by
        gcongr
    _ = (Q : ℝ) * (tau (n + 1) : ℝ) * (1 + Real.log Q) := by ring

/-- `Σ_{q ∈ 𝔉} log q · Σ*_χ χ(−1)χ(n)` — the family-restricted twisted log sum. -/
def cLogNeg (F : Family) (Qn n : ℕ) : ℂ :=
  ∑ q ∈ F.moduli Qn, ((Real.log q : ℝ) : ℂ) * primPairSumNeg q n 1

/-- `‖cLogNeg F Qn n‖ ≤ (3/2)·Qn·τ(n+1)·(1 + log Qn)`, both modulus ranges — the twisted
mirror of `cLog_norm_le`. -/
theorem cLogNeg_norm_le (F : Family) (Qn n : ℕ) (hn : 1 ≤ n) :
    ‖cLogNeg F Qn n‖ ≤ 3 / 2 * (Qn : ℝ) * (tau (n + 1) : ℝ) * (1 + Real.log Qn) := by
  have hτ : (0:ℝ) ≤ (tau (n + 1) : ℝ) := Nat.cast_nonneg _
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlogQ : 0 ≤ Real.log Qn := Real.log_natCast_nonneg Qn
  have hred : cLogNeg F Qn n = cLogNeg Family.qle Qn n
      ∨ cLogNeg F Qn n = cLogNeg Family.dyadic Qn n := by
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
  rcases hred with hred | hred <;> rw [hred]
  case inl =>
      rcases Nat.eq_zero_or_pos Qn with h0 | h1
      · subst h0
        simp [cLogNeg, Family.moduli]
      · have heq : cLogNeg Family.qle Qn n = famLogNegSum Qn n := by
          unfold cLogNeg famLogNegSum
          rw [sum_Icc_one_eq_add Qn h1]
          simp [Family.moduli]
        rw [heq]
        refine (famLogNegSum_norm_le Qn n hn).trans ?_
        nlinarith [mul_nonneg hQ hτ, (by linarith : (0:ℝ) ≤ 1 + Real.log Qn)]
  case inr =>
      have heq : cLogNeg Family.dyadic Qn n = famLogNegSum Qn n - famLogNegSum (Qn / 2) n := by
        unfold cLogNeg famLogNegSum
        show ∑ q ∈ Finset.Ioc (Qn / 2) Qn, ((Real.log q : ℝ) : ℂ) * primPairSumNeg q n 1 = _
        rw [sum_Ioc_half_eq]
      rw [heq]
      have h1 := famLogNegSum_norm_le Qn n hn
      have h2 := famLogNegSum_norm_le (Qn / 2) n hn
      have hhalf : ((Qn / 2 : ℕ) : ℝ) ≤ (Qn : ℝ) / 2 := Nat.cast_div_le
      have hlog : Real.log ((Qn / 2 : ℕ) : ℝ) ≤ Real.log Qn :=
        log_natCast_mono (Nat.div_le_self Qn 2)
      have hlog0 : 0 ≤ Real.log ((Qn / 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
      calc ‖famLogNegSum Qn n - famLogNegSum (Qn / 2) n‖
          ≤ ‖famLogNegSum Qn n‖ + ‖famLogNegSum (Qn / 2) n‖ := norm_sub_le _ _
        _ ≤ (Qn : ℝ) * (tau (n + 1) : ℝ) * (1 + Real.log Qn)
              + ((Qn / 2 : ℕ) : ℝ) * (tau (n + 1) : ℝ) * (1 + Real.log ((Qn / 2 : ℕ) : ℝ)) :=
            add_le_add h1 h2
        _ ≤ (Qn : ℝ) * (tau (n + 1) : ℝ) * (1 + Real.log Qn)
              + (Qn : ℝ) / 2 * (tau (n + 1) : ℝ) * (1 + Real.log Qn) := by
            gcongr
        _ = 3 / 2 * (Qn : ℝ) * (tau (n + 1) : ℝ) * (1 + Real.log Qn) := by ring

/-! ### E′2. The parity coefficient sequences -/

/-- `Σ_{q ∈ 𝔉} Σ_{χ ∈ sel q} χ(n)` — `cEven` / `cOdd` at an arbitrary selector. -/
def cSel (sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q)) (F : Family) (Qn n : ℕ) : ℂ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q, χ (n : ZMod q)

/-- `Σ_{q ∈ 𝔉} log q · Σ_{χ ∈ sel q} χ(n)` — the `log q`-weighted version. -/
def cLogSel (sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q)) (F : Family) (Qn n : ℕ) : ℂ :=
  ∑ q ∈ F.moduli Qn, ((Real.log q : ℝ) : ℂ) * ∑ χ ∈ sel q, χ (n : ZMod q)

theorem cSel_even_eq (F : Family) (Qn n : ℕ) :
    cSel primitiveCharsEven F Qn n = cEven F Qn n := rfl

theorem cSel_odd_eq (F : Family) (Qn n : ℕ) :
    cSel primitiveCharsOdd F Qn n = cOdd F Qn n := rfl

theorem cLogSel_even_eq (F : Family) (Qn n : ℕ) :
    cLogSel primitiveCharsEven F Qn n = (cLog F Qn n + cLogNeg F Qn n) / 2 := by
  unfold cLogSel cLog cLogNeg
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [sum_even_eq]
  ring

theorem cLogSel_odd_eq (F : Family) (Qn n : ℕ) :
    cLogSel primitiveCharsOdd F Qn n = (cLog F Qn n - cLogNeg F Qn n) / 2 := by
  unfold cLogSel cLog cLogNeg
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [sum_odd_eq]
  ring

/-- `‖cLogSel even‖ ≤ (3/4)·Q·(1+log Q)·(τ(n−1) + τ(n+1))` — the parity analogue of
`cLog_norm_le`, with the SECOND divisor kernel that `cLog_norm_le` does not have. -/
theorem cLogSel_even_norm_le (F : Family) (Qn n : ℕ) (hn : 2 ≤ n) :
    ‖cLogSel primitiveCharsEven F Qn n‖
      ≤ 3 / 4 * (Qn : ℝ) * (1 + Real.log Qn) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) := by
  rw [cLogSel_even_eq, norm_div, Complex.norm_ofNat]
  have h1 := cLog_norm_le F Qn n hn
  have h2 := cLogNeg_norm_le F Qn n (by omega)
  have h := norm_add_le (cLog F Qn n) (cLogNeg F Qn n)
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [h, h1, h2]

theorem cLogSel_odd_norm_le (F : Family) (Qn n : ℕ) (hn : 2 ≤ n) :
    ‖cLogSel primitiveCharsOdd F Qn n‖
      ≤ 3 / 4 * (Qn : ℝ) * (1 + Real.log Qn) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) := by
  rw [cLogSel_odd_eq, norm_div, Complex.norm_ofNat]
  have h1 := cLog_norm_le F Qn n hn
  have h2 := cLogNeg_norm_le F Qn n (by omega)
  have h := norm_sub_le (cLog F Qn n) (cLogNeg F Qn n)
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [h, h1, h2]

/-! ### E′3. The two-kernel weighted sum (no `+1` term) -/

theorem sum_kernel2_div_sqrt_le (A : ℝ) (hA : 0 ≤ A) (N : ℕ) (c : ℕ → ℂ)
    (hc : ∀ n, 2 ≤ n → ‖c n‖ ≤ A * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ))) :
    ∑ n ∈ Finset.Ioc 1 N, ‖c n‖ / Real.sqrt (n : ℝ)
      ≤ A * (2 * Real.sqrt N * (1 + Real.log N)
          + 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1))) := by
  have hstep : ∀ n ∈ Finset.Ioc 1 N, ‖c n‖ / Real.sqrt (n : ℝ)
      ≤ A * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
          + (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)) := by
    intro n hn
    have h2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    calc ‖c n‖ / Real.sqrt (n : ℝ)
        ≤ (A * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ))) / Real.sqrt (n : ℝ) :=
          div_le_div_of_nonneg_right (hc n h2) hs.le
      _ = A * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
            + (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)) := by field_simp
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have hsub : Finset.Ioc 1 N ⊆ Finset.Ioc 0 N := Finset.Ioc_subset_Ioc (Nat.zero_le 1) le_rfl
  have hA1 : ∑ n ∈ Finset.Ioc 1 N, (tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt N * (1 + Real.log N) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity))
      (sum_tau_pred_div_sqrt_le N)
  have hB1 : ∑ n ∈ Finset.Ioc 1 N, (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity))
      (sum_tau_succ_div_sqrt_le N)
  linarith

/-! ### E′4. The parity pointwise identity -/

theorem inner_mu_P_pointwise_sel (P : ParamsQ) {q : ℕ} (hq : 1 ≤ q)
    (sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q)) {κ : ℕ}
    (hpar : ∀ χ ∈ sel q, parity χ = κ) (τ τ' : ℝ) :
    ∑ χ ∈ sel q, muDensity q χ τ * Zones.PXchi P χ τ'
      = (1 / (2 * Real.pi))
            * (Real.log q * PXc (fun n => ∑ χ ∈ sel q, χ (n : ZMod q)) P.XQ τ')
        + muq κ 1 τ * PXc (fun n => ∑ χ ∈ sel q, χ (n : ZMod q)) P.XQ τ' := by
  have hsum : ∑ χ ∈ sel q, Zones.PXchi P χ τ'
      = PXc (fun n => ∑ χ ∈ sel q, χ (n : ZMod q)) P.XQ τ' := by
    rw [PXc_finset_sum]
    rfl
  have hsplit : ∀ χ ∈ sel q, muDensity q χ τ * Zones.PXchi P χ τ'
      = (Real.log q / (2 * Real.pi)) * Zones.PXchi P χ τ'
        + muq κ 1 τ * Zones.PXchi P χ τ' := by
    intro χ hχ
    rw [muDensity_eq_log_add_m hq χ τ, hpar χ hχ]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hsum]
  ring

theorem fam_mu_P_pointwise_sel (P : ParamsQ) (F : Family) (Qn : ℕ)
    (sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q)) {κ : ℕ}
    (hpar : ∀ (q : ℕ), ∀ χ ∈ sel q, parity χ = κ) (τ τ' : ℝ) :
    ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q, muDensity q χ τ * Zones.PXchi P χ τ'
      = (1 / (2 * Real.pi)) * PXc (cLogSel sel F Qn) P.XQ τ'
        + muq κ 1 τ * PXc (cSel sel F Qn) P.XQ τ' := by
  have hq : ∀ q ∈ F.moduli Qn, ∑ χ ∈ sel q, muDensity q χ τ * Zones.PXchi P χ τ'
      = (1 / (2 * Real.pi))
            * (Real.log q * PXc (fun n => ∑ χ ∈ sel q, χ (n : ZMod q)) P.XQ τ')
        + muq κ 1 τ * PXc (fun n => ∑ χ ∈ sel q, χ (n : ZMod q)) P.XQ τ' :=
    fun q hq => inner_mu_P_pointwise_sel P (one_le_of_mem_moduli hq) sel (hpar q) τ τ'
  rw [Finset.sum_congr rfl hq, Finset.sum_add_distrib]
  congr 1
  · unfold cLogSel
    rw [PXc_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [PXc_real_smul]
  · unfold cSel
    rw [PXc_finset_sum, Finset.mul_sum]

/-! ### E′5. `ROW9par` -/

/-- `S₁ = 2√N(1+log N)`, the `τ(n−1)` weighted sum, `N = ⌊X⌋`. -/
def S1 (P : ParamsQ) : ℝ :=
  2 * Real.sqrt (⌊P.XQ⌋₊ : ℝ) * (1 + Real.log (⌊P.XQ⌋₊ : ℝ))

/-- `S₂ = 2√2·√(N+1)(1+log(N+1))`, the `τ(n+1)` weighted sum. -/
def S2 (P : ParamsQ) : ℝ :=
  2 * Real.sqrt 2 * Real.sqrt ((⌊P.XQ⌋₊ : ℝ) + 1) * (1 + Real.log ((⌊P.XQ⌋₊ : ℝ) + 1))

/-- `S₀ = 2√N`. -/
def S0 (P : ParamsQ) : ℝ := 2 * Real.sqrt (⌊P.XQ⌋₊ : ℝ)

/-- `ROW9`, in the `S₀/S₁/S₂` spelling (`rfl`). -/
theorem ROW9_eq (F : Family) (P : ParamsQ) (Qn : ℕ) :
    ROW9 F P Qn
      = 8 * P.bQ * P.LB / Real.pi * (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn) * S1 P)
        + 8 * P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi)
            * (3 / 4 * (Qn : ℝ) * (S1 P + S2 P) + S0 P) := rfl

set_option linter.unusedVariables false in
/-- **The parity row-9 constant.**  Two changes from `ROW9`: the `log q`-weighted block runs
against `(3/4)Q(1+log Q)(S₁+S₂)` instead of `(3/2)Q(1+log Q)S₁` (half the characters, but the
twisted `τ(n+1)` kernel joins in), and there is only ONE `(44l+24)` block instead of two
(the opposite parity's `muq` term is absent).  `F` is carried, unused, so that the signature
matches `ROW9`'s (whose body does not mention `F` either). -/
def ROW9par (F : Family) (P : ParamsQ) (Qn : ℕ) : ℝ :=
  8 * P.bQ * P.LB / Real.pi * (3 / 4 * (Qn : ℝ) * (1 + Real.log Qn) * (S1 P + S2 P))
    + 4 * P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi)
        * (3 / 4 * (Qn : ℝ) * (S1 P + S2 P) + S0 P)

theorem S2_le_four_S1 (P : ParamsQ) (hX : 1 ≤ P.XQ) : S2 P ≤ 4 * S1 P := by
  set N := ⌊P.XQ⌋₊ with hN
  have hN1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.floor_pos.mpr hX
  have hN0 : (0:ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hsq : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlog : 1 + Real.log ((N : ℝ) + 1) ≤ 2 * (1 + Real.log (N : ℝ)) := by
    have h1 : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hN0)] at h1
    linarith
  have hlogN1 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsN : (0:ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  unfold S2 S1
  rw [← hN]
  calc 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1))
      ≤ 2 * Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt (N : ℝ)) * (2 * (1 + Real.log (N : ℝ))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) hlog
          (by linarith) (by positivity)
    _ = 4 * (2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ))) := by
        rw [show 2 * Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt (N : ℝ))
          = 2 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt (N : ℝ) by ring, h22]
        ring

/-- **`ROW9par ≤ 3·ROW9`** — the honest price of the parity branch (see §E′'s header). -/
theorem ROW9par_le_three_ROW9 (F : Family) (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) :
    ROW9par F P Qn ≤ 3 * ROW9 F P Qn := by
  have hb0 : 0 ≤ P.bQ := hP.bQ_pos.le
  have hL0 : 0 ≤ P.LB := hP.LB_pos.le
  have hl1 : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ0 : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlogQ : 0 ≤ Real.log Qn := Real.log_natCast_nonneg Qn
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hN1 : (1:ℝ) ≤ (⌊P.XQ⌋₊ : ℝ) := by exact_mod_cast Nat.floor_pos.mpr hX1
  have hlogN : 0 ≤ Real.log ((⌊P.XQ⌋₊ : ℝ)) := Real.log_nonneg hN1
  have hS1 : 0 ≤ S1 P := by unfold S1; positivity
  have hS2 : 0 ≤ S2 P := by
    unfold S2
    have : 0 ≤ 1 + Real.log ((⌊P.XQ⌋₊ : ℝ) + 1) := by
      have := Real.log_nonneg (show (1:ℝ) ≤ (⌊P.XQ⌋₊ : ℝ) + 1 by linarith); linarith
    positivity
  have hS0 : 0 ≤ S0 P := by unfold S0; positivity
  have hkey := S2_le_four_S1 P hX1
  have hK : (0:ℝ) ≤ 8 * P.bQ * P.LB / Real.pi := by positivity
  have hC : (0:ℝ) ≤ 44 / Real.pi * Zeta23.l P.T + 24 / Real.pi := by positivity
  have hV : (0:ℝ) ≤ 3 / 4 * (Qn : ℝ) * (S1 P + S2 P) + S0 P := by positivity
  have hbLC : (0:ℝ) ≤ P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi) := by positivity
  rw [ROW9_eq]
  unfold ROW9par
  have hfirst : 8 * P.bQ * P.LB / Real.pi
        * (3 / 4 * (Qn : ℝ) * (1 + Real.log Qn) * (S1 P + S2 P))
      ≤ 3 * (8 * P.bQ * P.LB / Real.pi
          * (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn) * S1 P)) := by
    have hin : 3 / 4 * (Qn : ℝ) * (1 + Real.log Qn) * (S1 P + S2 P)
        ≤ 3 * (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn) * S1 P) := by
      have hQL : (0:ℝ) ≤ (Qn : ℝ) * (1 + Real.log Qn) := by positivity
      nlinarith [hkey, hQL]
    nlinarith [mul_le_mul_of_nonneg_left hin hK]
  have hsecond : 4 * P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi)
        * (3 / 4 * (Qn : ℝ) * (S1 P + S2 P) + S0 P)
      ≤ 3 * (8 * P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi)
          * (3 / 4 * (Qn : ℝ) * (S1 P + S2 P) + S0 P)) := by
    nlinarith [mul_nonneg hbLC hV]
  linarith

/-! ### E′6. The parity row-9 bound -/

/-- **The generic parity deliverable.**  For ANY per-modulus character selection `sel` of
CONSTANT parity `κ`, with the two coefficient bounds supplied:
`|Σ_q Σ_{χ ∈ sel q} 𝓜[μ_χ, P_{X,χ}]| ≤ ROW9par F P Qn`. -/
theorem abs_sum_sel_mu_P_le (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    (F : Family) (Qn : ℕ) (sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q)) {κ : ℕ}
    (hκ : κ ≤ 1) (hpar : ∀ (q : ℕ), ∀ χ ∈ sel q, parity χ = κ)
    (hcl : ∀ n, 2 ≤ n → ‖cLogSel sel F Qn n‖
        ≤ 3 / 4 * (Qn : ℝ) * (1 + Real.log Qn) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)))
    (hcs : ∀ n, 2 ≤ n → ‖cSel sel F Qn n‖
        ≤ 3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) + 1) :
    |∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q, Mform P (muDensity q χ) (Zones.PXchi P χ)|
      ≤ ROW9par F P Qn := by
  have hΦc : Continuous P.PhiQ := hP.PhiQ_continuous hw
  have hΦ1 : ContDiff ℝ 1 P.PhiQ := hP.PhiQ_contDiff_one hw
  have hΦint : Integrable (fun x => P.PhiQ x ^ 2) := hP.integrable_PhiQ_sq hw
  have hΦsq : ∫ x, P.PhiQ x ^ 2 = 2 * Real.pi * P.bQ * P.LB := hP.integral_PhiQ_sq hw
  have hTpos : 0 < P.T := hP.T_pos
  have hT0 : 0 ≤ P.T := hTpos.le
  have hTe : 2 * Real.pi * Real.exp 1 ≤ P.T := T_ge_2pie_of_valid hP
  have hT1 : (1:ℝ) ≤ P.T := by linarith [hP.T_ge300]
  have hl1 : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hpi : 0 < Real.pi := Real.pi_pos
  have hμc : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (muDensity q χ) :=
    fun q χ => (Zeta23.ThmE.GammaChi.muq_smooth _ _).continuous
  have hPc : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (Zones.PXchi P χ) :=
    fun q χ => by rw [PXchi_eq_PXc]; exact PXc_continuous _ _
  set S : Set (ℝ × ℝ) := Set.Icc P.T (2 * P.T) ×ˢ Set.Icc P.T (2 * P.T) with hSdef
  -- (i) the decomposition — TWO terms, not three
  have hdec : ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q, Mform P (muDensity q χ) (Zones.PXchi P χ)
      = (1 / (2 * Real.pi))
          * Zeta23.PrimeSide.Mform P.PhiQ P.T (fun _ => (1:ℝ)) (PXc (cLogSel sel F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq κ 1) (PXc (cSel sel F Qn) P.XQ) := by
    have e1 : ∀ q ∈ F.moduli Qn,
        ∑ χ ∈ sel q, Mform P (muDensity q χ) (Zones.PXchi P χ)
          = ∫ z in S, ∑ χ ∈ sel q,
              P.PhiQ (z.1 - z.2) ^ 2 * muDensity q χ z.1 * Zones.PXchi P χ z.2 := by
      intro q _
      rw [integral_finsetSum _ (fun χ _ => Mform_integrableOn hΦc (hμc q χ) (hPc q χ))]
      rfl
    have e2 : ∀ z : ℝ × ℝ, ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q,
        P.PhiQ (z.1 - z.2) ^ 2 * muDensity q χ z.1 * Zones.PXchi P χ z.2
        = (1 / (2 * Real.pi)) * (P.PhiQ (z.1 - z.2) ^ 2 * 1 * PXc (cLogSel sel F Qn) P.XQ z.2)
          + P.PhiQ (z.1 - z.2) ^ 2 * muq κ 1 z.1 * PXc (cSel sel F Qn) P.XQ z.2 := by
      intro z
      have e3 : ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q,
          P.PhiQ (z.1 - z.2) ^ 2 * muDensity q χ z.1 * Zones.PXchi P χ z.2
          = P.PhiQ (z.1 - z.2) ^ 2 * ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q,
              muDensity q χ z.1 * Zones.PXchi P χ z.2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        ring
      rw [e3, fam_mu_P_pointwise_sel P F Qn sel hpar z.1 z.2]
      ring
    have hI1 : IntegrableOn (fun z : ℝ × ℝ =>
        (1 / (2 * Real.pi)) * (P.PhiQ (z.1 - z.2) ^ 2 * 1
          * PXc (cLogSel sel F Qn) P.XQ z.2)) S :=
      (Mform_integrableOn hΦc continuous_const (PXc_continuous _ _)).const_mul _
    have hI2 : IntegrableOn (fun z : ℝ × ℝ =>
        P.PhiQ (z.1 - z.2) ^ 2 * muq κ 1 z.1 * PXc (cSel sel F Qn) P.XQ z.2) S :=
      Mform_integrableOn hΦc (Zeta23.ThmE.GammaChi.muq_smooth _ _).continuous
        (PXc_continuous _ _)
    have hL : ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q, Mform P (muDensity q χ) (Zones.PXchi P χ)
        = ∫ z in S, ((1 / (2 * Real.pi))
            * (P.PhiQ (z.1 - z.2) ^ 2 * 1 * PXc (cLogSel sel F Qn) P.XQ z.2)
          + P.PhiQ (z.1 - z.2) ^ 2 * muq κ 1 z.1 * PXc (cSel sel F Qn) P.XQ z.2) := by
      rw [Finset.sum_congr rfl e1, ← integral_finsetSum _ (fun q _ =>
        integrable_finsetSum _ (fun χ _ => Mform_integrableOn hΦc (hμc q χ) (hPc q χ)))]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => e2 z)
    have hR : (1 / (2 * Real.pi))
          * Zeta23.PrimeSide.Mform P.PhiQ P.T (fun _ => (1:ℝ)) (PXc (cLogSel sel F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq κ 1) (PXc (cSel sel F Qn) P.XQ)
        = ∫ z in S, ((1 / (2 * Real.pi))
            * (P.PhiQ (z.1 - z.2) ^ 2 * 1 * PXc (cLogSel sel F Qn) P.XQ z.2)
          + P.PhiQ (z.1 - z.2) ^ 2 * muq κ 1 z.1 * PXc (cSel sel F Qn) P.XQ z.2) := by
      unfold Zeta23.PrimeSide.Mform
      beta_reduce
      rw [← integral_const_mul, ← integral_add hI1 hI2]
    rw [hL, hR]
  -- (ii) the two oscillatory bounds
  have hBm : ∀ τ ∈ Set.Icc P.T (2 * P.T), |muq κ 1 τ| ≤ 11 / Real.pi * Zeta23.l P.T := by
    intro τ hτ
    have h := MuqUniform.muq_abs_le_Icc_uniform (q := 1) hκ le_rfl hTe τ hτ
    simpa using h
  have hDm : ∀ τ ∈ Set.Icc P.T (2 * P.T), |deriv (muq κ 1) τ| ≤ (24 / Real.pi) / P.T := by
    intro τ hτ
    have hτT : P.T ≤ τ := hτ.1
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by linarith)]; linarith
    refine (Zeta23.ThmE.GammaChi.muq_deriv_bound_const (q := 1) hκ τ hτ1).trans ?_
    rw [abs_of_nonneg (by linarith)]
    exact div_le_div_of_nonneg_left (by positivity) hTpos hτT
  have hBD : 0 ≤ 4 * (11 / Real.pi * Zeta23.l P.T) + (24 / Real.pi) / P.T * P.T := by positivity
  have hb1 := abs_Mform_PXc_le hT0 hΦ1 hΦint (u := fun _ => (1:ℝ)) contDiff_const (B := 1)
    (D := 0) (fun τ _ => by simp) (fun τ _ => by simp) (by linarith)
    (cLogSel sel F Qn) P.XQ
  have hb2 := abs_Mform_PXc_le hT0 hΦ1 hΦint
    ((Zeta23.ThmE.GammaChi.muq_smooth κ 1).of_le (by exact_mod_cast le_top))
    hBm hDm hBD (cSel sel F Qn) P.XQ
  rw [hΦsq] at hb1 hb2
  -- (iii) the weighted sums
  set N := ⌊P.XQ⌋₊ with hNdef
  have hAnn : (0:ℝ) ≤ 3 / 4 * (Qn : ℝ) * (1 + Real.log Qn) := by
    have : (0:ℝ) ≤ Real.log Qn := Real.log_natCast_nonneg Qn
    positivity
  have hs1 := sum_kernel2_div_sqrt_le (3 / 4 * (Qn : ℝ) * (1 + Real.log Qn)) hAnn N
    (cLogSel sel F Qn) hcl
  have hs2 := sum_par_div_sqrt_le Qn N (cSel sel F Qn) hcs
  have hb0 : 0 ≤ P.bQ := hP.bQ_pos.le
  have hL0 : 0 ≤ P.LB := hP.LB_pos.le
  have hc1 : (0:ℝ) ≤ (2 / Real.pi) * ((4 * 1 + 0 * P.T) * (2 * Real.pi * P.bQ * P.LB)) := by
    positivity
  have hc2 : (0:ℝ) ≤ (2 / Real.pi)
      * ((4 * (11 / Real.pi * Zeta23.l P.T) + (24 / Real.pi) / P.T * P.T)
        * (2 * Real.pi * P.bQ * P.LB)) := by positivity
  rw [hdec]
  have hTT : (24 / Real.pi) / P.T * P.T = 24 / Real.pi := div_mul_cancel₀ _ hTpos.ne'
  calc |(1 / (2 * Real.pi))
          * Zeta23.PrimeSide.Mform P.PhiQ P.T (fun _ => (1:ℝ)) (PXc (cLogSel sel F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq κ 1) (PXc (cSel sel F Qn) P.XQ)|
      ≤ (1 / (2 * Real.pi))
          * |Zeta23.PrimeSide.Mform P.PhiQ P.T (fun _ => (1:ℝ)) (PXc (cLogSel sel F Qn) P.XQ)|
        + |Zeta23.PrimeSide.Mform P.PhiQ P.T (muq κ 1) (PXc (cSel sel F Qn) P.XQ)| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
    _ ≤ (1 / (2 * Real.pi)) * ((2 / Real.pi) * ((4 * 1 + 0 * P.T) * (2 * Real.pi * P.bQ * P.LB))
            * (3 / 4 * (Qn : ℝ) * (1 + Real.log Qn) * (S1 P + S2 P)))
        + (2 / Real.pi) * ((4 * (11 / Real.pi * Zeta23.l P.T) + (24 / Real.pi) / P.T * P.T)
            * (2 * Real.pi * P.bQ * P.LB))
          * (3 / 4 * (Qn : ℝ) * (S1 P + S2 P) + S0 P) := by
        gcongr
        · exact hb1.trans (mul_le_mul_of_nonneg_left hs1 hc1)
        · exact hb2.trans (mul_le_mul_of_nonneg_left hs2 hc2)
    _ = ROW9par F P Qn := by
        unfold ROW9par
        rw [hTT]
        field_simp
        ring

/-- **LEDGER ROW 9 for Corollary 3's four parity families**, at `ROW9par`. -/
theorem famMform_muP_le_parity (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    (F : Family) (Qn : ℕ)
    (hchars : (∀ q, F.chars q = primitiveCharsEven q)
      ∨ (∀ q, F.chars q = primitiveCharsOdd q)) :
    |familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))|
      ≤ ROW9par F P Qn := by
  rcases hchars with h | h
  · have hrw : familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))
        = ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveCharsEven q,
            Mform P (muDensity q χ) (Zones.PXchi P χ) := by
      unfold familySum
      exact Finset.sum_congr rfl fun q _ => by rw [h q]
    rw [hrw]
    refine abs_sum_sel_mu_P_le P hP hw F Qn primitiveCharsEven (κ := 0) (by norm_num)
      (fun q χ hχ => ((mem_primitiveCharsEven_iff χ).mp hχ).2)
      (fun n hn => cLogSel_even_norm_le F Qn n hn) (fun n hn => ?_)
    rw [cSel_even_eq]
    exact cEven_norm_le F Qn n hn
  · have hrw : familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))
        = ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveCharsOdd q,
            Mform P (muDensity q χ) (Zones.PXchi P χ) := by
      unfold familySum
      exact Finset.sum_congr rfl fun q _ => by rw [h q]
    rw [hrw]
    refine abs_sum_sel_mu_P_le P hP hw F Qn primitiveCharsOdd (κ := 1) le_rfl
      (fun q χ hχ => ((mem_primitiveCharsOdd_iff χ).mp hχ).2)
      (fun n hn => cLogSel_odd_norm_le F Qn n hn) (fun n hn => ?_)
    rw [cSel_odd_eq]
    exact cOdd_norm_le F Qn n hn

/-- Row 9 for the four parity families, against `3·ROW9` and with no hypothesis beyond the
design's own. -/
theorem famMform_muP_le_of_not_isFull (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    {F : Family} (hF : ¬ F.IsFull) (Qn : ℕ) :
    |familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))|
      ≤ 3 * ROW9 F P Qn :=
  (famMform_muP_le_parity P hP hw F Qn (chars_parity_of_not_isFull hF)).trans
    (ROW9par_le_three_ROW9 F P hP Qn)

/-- **LEDGER ROW 9, FAMILY-AVERAGED, on a FULL family** (the §5 orthogonality, weighted).
`|Σ_{χ ∈ 𝔉_Q} 𝓜[μ_χ, P_{X,χ}]| ≤ ROW9 F P Qn`, at every valid design point with `8w ≤ L`.
Cap-free (Rule 17: no λ-cap, `X` is never compared with `T`, `D₀` absent). This is the SHARP
constant; `famMform_muP_le` below pays a factor 3 to cover the parity families too. -/
theorem famMform_muP_le_of_isFull (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    {F : Family} (hF : F.IsFull) (Qn : ℕ) :
    |familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))| ≤ ROW9 F P Qn := by
  have hΦc : Continuous P.PhiQ := hP.PhiQ_continuous hw
  have hΦ1 : ContDiff ℝ 1 P.PhiQ := hP.PhiQ_contDiff_one hw
  have hΦint : Integrable (fun x => P.PhiQ x ^ 2) := hP.integrable_PhiQ_sq hw
  have hΦsq : ∫ x, P.PhiQ x ^ 2 = 2 * Real.pi * P.bQ * P.LB := hP.integral_PhiQ_sq hw
  have hTpos : 0 < P.T := hP.T_pos
  have hT0 : 0 ≤ P.T := hTpos.le
  have hTe : 2 * Real.pi * Real.exp 1 ≤ P.T := T_ge_2pie_of_valid hP
  have hT1 : (1:ℝ) ≤ P.T := by linarith [hP.T_ge300]
  have hl1 : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hpi : 0 < Real.pi := Real.pi_pos
  have hμc : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (muDensity q χ) :=
    fun q χ => (Zeta23.ThmE.GammaChi.muq_smooth _ _).continuous
  have hPc : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (Zones.PXchi P χ) :=
    fun q χ => by rw [PXchi_eq_PXc]; exact PXc_continuous _ _
  set S : Set (ℝ × ℝ) := Set.Icc P.T (2 * P.T) ×ˢ Set.Icc P.T (2 * P.T) with hSdef
  -- (i) the decomposition
  have hdec : familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))
      = (1 / (2 * Real.pi))
          * Zeta23.PrimeSide.Mform P.PhiQ P.T (fun _ => (1:ℝ)) (PXc (cLog F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq 0 1) (PXc (cEven F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq 1 1) (PXc (cOdd F Qn) P.XQ) := by
    have e1 : ∀ q ∈ F.moduli Qn,
        ∑ χ ∈ primitiveChars q, Mform P (muDensity q χ) (Zones.PXchi P χ)
          = ∫ z in S, ∑ χ ∈ primitiveChars q,
              P.PhiQ (z.1 - z.2) ^ 2 * muDensity q χ z.1 * Zones.PXchi P χ z.2 := by
      intro q _
      rw [integral_finsetSum _ (fun χ _ => Mform_integrableOn hΦc (hμc q χ) (hPc q χ))]
      rfl
    have e2 : ∀ z : ℝ × ℝ, ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q,
        P.PhiQ (z.1 - z.2) ^ 2 * muDensity q χ z.1 * Zones.PXchi P χ z.2
        = (1 / (2 * Real.pi)) * (P.PhiQ (z.1 - z.2) ^ 2 * 1 * PXc (cLog F Qn) P.XQ z.2)
          + P.PhiQ (z.1 - z.2) ^ 2 * muq 0 1 z.1 * PXc (cEven F Qn) P.XQ z.2
          + P.PhiQ (z.1 - z.2) ^ 2 * muq 1 1 z.1 * PXc (cOdd F Qn) P.XQ z.2 := by
      intro z
      have e3 : ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q,
          P.PhiQ (z.1 - z.2) ^ 2 * muDensity q χ z.1 * Zones.PXchi P χ z.2
          = P.PhiQ (z.1 - z.2) ^ 2 * ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q,
              muDensity q χ z.1 * Zones.PXchi P χ z.2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        ring
      rw [e3, fam_mu_P_pointwise P F Qn z.1 z.2]
      ring
    have hI1 : IntegrableOn (fun z : ℝ × ℝ =>
        (1 / (2 * Real.pi)) * (P.PhiQ (z.1 - z.2) ^ 2 * 1 * PXc (cLog F Qn) P.XQ z.2)) S :=
      (Mform_integrableOn hΦc continuous_const (PXc_continuous _ _)).const_mul _
    have hI2 : IntegrableOn (fun z : ℝ × ℝ =>
        P.PhiQ (z.1 - z.2) ^ 2 * muq 0 1 z.1 * PXc (cEven F Qn) P.XQ z.2) S :=
      Mform_integrableOn hΦc (Zeta23.ThmE.GammaChi.muq_smooth _ _).continuous
        (PXc_continuous _ _)
    have hI3 : IntegrableOn (fun z : ℝ × ℝ =>
        P.PhiQ (z.1 - z.2) ^ 2 * muq 1 1 z.1 * PXc (cOdd F Qn) P.XQ z.2) S :=
      Mform_integrableOn hΦc (Zeta23.ThmE.GammaChi.muq_smooth _ _).continuous
        (PXc_continuous _ _)
    have hL : familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))
        = ∫ z in S, ((1 / (2 * Real.pi)) * (P.PhiQ (z.1 - z.2) ^ 2 * 1 * PXc (cLog F Qn) P.XQ z.2)
          + P.PhiQ (z.1 - z.2) ^ 2 * muq 0 1 z.1 * PXc (cEven F Qn) P.XQ z.2
          + P.PhiQ (z.1 - z.2) ^ 2 * muq 1 1 z.1 * PXc (cOdd F Qn) P.XQ z.2) := by
      rw [familySum_of_isFull hF]
      rw [Finset.sum_congr rfl e1, ← integral_finsetSum _ (fun q _ =>
        integrable_finsetSum _ (fun χ _ => Mform_integrableOn hΦc (hμc q χ) (hPc q χ)))]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => e2 z)
    have hR : (1 / (2 * Real.pi))
          * Zeta23.PrimeSide.Mform P.PhiQ P.T (fun _ => (1:ℝ)) (PXc (cLog F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq 0 1) (PXc (cEven F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq 1 1) (PXc (cOdd F Qn) P.XQ)
        = ∫ z in S, ((1 / (2 * Real.pi)) * (P.PhiQ (z.1 - z.2) ^ 2 * 1 * PXc (cLog F Qn) P.XQ z.2)
          + P.PhiQ (z.1 - z.2) ^ 2 * muq 0 1 z.1 * PXc (cEven F Qn) P.XQ z.2
          + P.PhiQ (z.1 - z.2) ^ 2 * muq 1 1 z.1 * PXc (cOdd F Qn) P.XQ z.2) := by
      have hI12 : IntegrableOn (fun z : ℝ × ℝ =>
          (1 / (2 * Real.pi)) * (P.PhiQ (z.1 - z.2) ^ 2 * 1 * PXc (cLog F Qn) P.XQ z.2)
          + P.PhiQ (z.1 - z.2) ^ 2 * muq 0 1 z.1 * PXc (cEven F Qn) P.XQ z.2) S := hI1.add hI2
      unfold Zeta23.PrimeSide.Mform
      beta_reduce
      rw [← integral_const_mul, ← integral_add hI1 hI2, ← integral_add hI12 hI3]
    rw [hL, hR]
  -- (ii) the three oscillatory bounds
  have hκ0 : (0:ℕ) ≤ 1 := by norm_num
  have hκ1 : (1:ℕ) ≤ 1 := le_rfl
  have hBm : ∀ κ : ℕ, κ ≤ 1 → ∀ τ ∈ Set.Icc P.T (2 * P.T),
      |muq κ 1 τ| ≤ 11 / Real.pi * Zeta23.l P.T := by
    intro κ hκ τ hτ
    have h := MuqUniform.muq_abs_le_Icc_uniform (q := 1) hκ le_rfl hTe τ hτ
    simpa using h
  have hDm : ∀ κ : ℕ, κ ≤ 1 → ∀ τ ∈ Set.Icc P.T (2 * P.T),
      |deriv (muq κ 1) τ| ≤ (24 / Real.pi) / P.T := by
    intro κ hκ τ hτ
    have hτT : P.T ≤ τ := hτ.1
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by linarith)]; linarith
    refine (Zeta23.ThmE.GammaChi.muq_deriv_bound_const (q := 1) hκ τ hτ1).trans ?_
    rw [abs_of_nonneg (by linarith)]
    exact div_le_div_of_nonneg_left (by positivity) hTpos hτT
  have hBD : 0 ≤ 4 * (11 / Real.pi * Zeta23.l P.T) + (24 / Real.pi) / P.T * P.T := by positivity
  have hb1 := abs_Mform_PXc_le hT0 hΦ1 hΦint (u := fun _ => (1:ℝ)) contDiff_const (B := 1) (D := 0)
    (fun τ _ => by simp) (fun τ _ => by simp) (by linarith) (cLog F Qn) P.XQ
  have hb2 := abs_Mform_PXc_le hT0 hΦ1 hΦint
    ((Zeta23.ThmE.GammaChi.muq_smooth 0 1).of_le (by exact_mod_cast le_top))
    (hBm 0 hκ0) (hDm 0 hκ0) hBD (cEven F Qn) P.XQ
  have hb3 := abs_Mform_PXc_le hT0 hΦ1 hΦint
    ((Zeta23.ThmE.GammaChi.muq_smooth 1 1).of_le (by exact_mod_cast le_top))
    (hBm 1 hκ1) (hDm 1 hκ1) hBD (cOdd F Qn) P.XQ
  rw [hΦsq] at hb1 hb2 hb3
  -- (iii) the weighted sums
  set N := ⌊P.XQ⌋₊ with hNdef
  have hs1 := sum_cLog_div_sqrt_le F Qn N
  have hs2 := sum_par_div_sqrt_le Qn N (cEven F Qn) (fun n hn => cEven_norm_le F Qn n hn)
  have hs3 := sum_par_div_sqrt_le Qn N (cOdd F Qn) (fun n hn => cOdd_norm_le F Qn n hn)
  have hb0 : 0 ≤ P.bQ := hP.bQ_pos.le
  have hL0 : 0 ≤ P.LB := hP.LB_pos.le
  have hc1 : (0:ℝ) ≤ (2 / Real.pi) * ((4 * 1 + 0 * P.T) * (2 * Real.pi * P.bQ * P.LB)) := by
    positivity
  have hc2 : (0:ℝ) ≤ (2 / Real.pi) * ((4 * (11 / Real.pi * Zeta23.l P.T) + (24 / Real.pi) / P.T * P.T)
      * (2 * Real.pi * P.bQ * P.LB)) := by positivity
  rw [hdec]
  have hTT : (24 / Real.pi) / P.T * P.T = 24 / Real.pi := div_mul_cancel₀ _ hTpos.ne'
  calc |(1 / (2 * Real.pi))
          * Zeta23.PrimeSide.Mform P.PhiQ P.T (fun _ => (1:ℝ)) (PXc (cLog F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq 0 1) (PXc (cEven F Qn) P.XQ)
        + Zeta23.PrimeSide.Mform P.PhiQ P.T (muq 1 1) (PXc (cOdd F Qn) P.XQ)|
      ≤ (1 / (2 * Real.pi))
          * |Zeta23.PrimeSide.Mform P.PhiQ P.T (fun _ => (1:ℝ)) (PXc (cLog F Qn) P.XQ)|
        + |Zeta23.PrimeSide.Mform P.PhiQ P.T (muq 0 1) (PXc (cEven F Qn) P.XQ)|
        + |Zeta23.PrimeSide.Mform P.PhiQ P.T (muq 1 1) (PXc (cOdd F Qn) P.XQ)| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _ |>.trans ?_) le_rfl)
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
    _ ≤ (1 / (2 * Real.pi)) * ((2 / Real.pi) * ((4 * 1 + 0 * P.T) * (2 * Real.pi * P.bQ * P.LB))
            * (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn) * (2 * Real.sqrt N * (1 + Real.log N))))
        + (2 / Real.pi) * ((4 * (11 / Real.pi * Zeta23.l P.T) + (24 / Real.pi) / P.T * P.T)
            * (2 * Real.pi * P.bQ * P.LB))
          * (3 / 4 * (Qn : ℝ) * (2 * Real.sqrt N * (1 + Real.log N)
              + 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)))
            + 2 * Real.sqrt N)
        + (2 / Real.pi) * ((4 * (11 / Real.pi * Zeta23.l P.T) + (24 / Real.pi) / P.T * P.T)
            * (2 * Real.pi * P.bQ * P.LB))
          * (3 / 4 * (Qn : ℝ) * (2 * Real.sqrt N * (1 + Real.log N)
              + 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)))
            + 2 * Real.sqrt N) := by
        gcongr
        · exact hb1.trans (mul_le_mul_of_nonneg_left hs1 hc1)
        · exact hb2.trans (mul_le_mul_of_nonneg_left hs2 hc2)
        · exact hb3.trans (mul_le_mul_of_nonneg_left hs3 hc2)
    _ = ROW9 F P Qn := by
        unfold ROW9
        rw [hTT]
        field_simp
        ring

/-- **LEDGER ROW 9, FAMILY-AVERAGED, ALL SIX FAMILIES**:
`|Σ_{χ ∈ 𝔉_Q} 𝓜[μ_χ, P_{X,χ}]| ≤ 3·ROW9 F P Qn`, at every valid design point with `8w ≤ L`.
No `F.IsFull`; this replaces the version whose parity branch was a `sorry`.

**The factor 3 is not a shortcut.** `ROW9par ≤ ROW9` is FALSE for large `Q` — see §E′'s
header — and `3` is the smallest clean constant that covers both regimes. The full families
keep the sharp `ROW9` through `famMform_muP_le_of_isFull`, and the enlargement is
order-preserving (`ROW9par ≍ ROW9 ≍ Q·L²·l·√X`), so downstream only the constant `c` in
`R9fun_eventually` moves. -/
theorem famMform_muP_le (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (F : Family)
    (Qn : ℕ) :
    |familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))|
      ≤ 3 * ROW9 F P Qn := by
  by_cases hF : F.IsFull
  · have h := famMform_muP_le_of_isFull P hP hw hF Qn
    have h0 := ROW9_nonneg F P hP Qn
    linarith
  · exact famMform_muP_le_of_not_isFull P hP hw hF Qn


/-! ## F. A closed-form majorant of `ROW9` in `(Q, L, l(T), √X)` only -/

theorem floor_facts (X : ℝ) (hX : 1 ≤ X) :
    Real.sqrt (⌊X⌋₊ : ℝ) ≤ Real.sqrt X ∧ Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X ∧
    Real.sqrt ((⌊X⌋₊ : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt X ∧
    Real.log ((⌊X⌋₊ : ℝ) + 1) ≤ 1 + Real.log X := by
  have hX0 : 0 ≤ X := by linarith
  have hN : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0
  have hN1 : (1:ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast Nat.floor_pos.mpr hX
  refine ⟨Real.sqrt_le_sqrt hN, Real.log_le_log (by linarith) hN, ?_, ?_⟩
  · rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  · have h2 : Real.log ((⌊X⌋₊ : ℝ) + 1) ≤ Real.log (2 * X) :=
      Real.log_le_log (by linarith) (by linarith)
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    rw [Real.log_mul (by norm_num) (by linarith)] at h2
    linarith

/-- **`ROW9`, closed form**: with `X = P.XQ`, `L = P.LB` (`= log X`), `l = l(T)`, `b = P.bQ`,
`ROW9 ≤ (24b/π)·Q·L·√X·(1+log Q)(1+L) + (8b/π)(44l + 24)·L·√X·((3/4)Q(10 + 6L) + 2)`.
Size: `≍ Q·L²·l·√X`, against `a²L²𝒩 ≍ Q²TL²ℒ` — ratio `≍ l√X/(QTℒ) = (QT)^{λ/2−1}·l/ℒ`,
the F57 power saving `(QT)^{−0.3746}` (≈ 10⁻³⁸ at `Q = 10¹⁰⁰`). -/
theorem ROW9_le_simple (F : Family) (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) :
    ROW9 F P Qn
      ≤ 24 * P.bQ / Real.pi * (Qn : ℝ) * P.LB * Real.sqrt P.XQ * (1 + Real.log Qn) * (1 + P.LB)
        + 8 * P.bQ / Real.pi * (44 * Zeta23.l P.T + 24) * P.LB * Real.sqrt P.XQ
          * (3 / 4 * (Qn : ℝ) * (10 + 6 * P.LB) + 2) := by
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hlogX : Real.log P.XQ = P.LB := Real.log_exp _
  obtain ⟨f1, f2, f3, f4⟩ := floor_facts P.XQ hX1
  rw [hlogX] at f2 f4
  set N := ⌊P.XQ⌋₊ with hN
  have hN1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.floor_pos.mpr hX1
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hlogN10 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hsN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsN1 : 0 ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_nonneg _
  have hsX : 0 ≤ Real.sqrt P.XQ := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hL0 : 0 ≤ P.LB := hP.LB_pos.le
  have hb0 : 0 ≤ P.bQ := hP.bQ_pos.le
  have hl1 : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hQ0 : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  have hlogQ0 : 0 ≤ Real.log (Qn : ℝ) := Real.log_natCast_nonneg Qn
  have hpi : 0 < Real.pi := Real.pi_pos
  have hS1 : 2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) ≤ 2 * Real.sqrt P.XQ * (1 + P.LB) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hS2 : 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1))
      ≤ 4 * Real.sqrt P.XQ * (2 + P.LB) := by
    have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1))
        ≤ 2 * Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt P.XQ) * (1 + (1 + P.LB)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left f3 (by positivity)) (by linarith)
            (by positivity) (by positivity)
      _ = 4 * Real.sqrt P.XQ * (2 + P.LB) := by
          rw [show 2 * Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt P.XQ)
            = 2 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt P.XQ by ring, h22]; ring
  have hS0 : 2 * Real.sqrt (N : ℝ) ≤ 2 * Real.sqrt P.XQ := by linarith
  have hA : 0 ≤ 8 * P.bQ * P.LB / Real.pi := by positivity
  have hc1 : 0 ≤ 3 / 2 * (Qn : ℝ) * (1 + Real.log Qn) := by positivity
  have hB : 0 ≤ 8 * P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi) := by positivity
  have hc2 : 0 ≤ 3 / 4 * (Qn : ℝ) := by positivity
  unfold ROW9
  rw [← hN]
  calc 8 * P.bQ * P.LB / Real.pi
          * (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn)
              * (2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ))))
        + 8 * P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi)
          * (3 / 4 * (Qn : ℝ) * (2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ))
                + 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)))
              + 2 * Real.sqrt (N : ℝ))
      ≤ 8 * P.bQ * P.LB / Real.pi
          * (3 / 2 * (Qn : ℝ) * (1 + Real.log Qn) * (2 * Real.sqrt P.XQ * (1 + P.LB)))
        + 8 * P.bQ * P.LB * (44 / Real.pi * Zeta23.l P.T + 24 / Real.pi)
          * (3 / 4 * (Qn : ℝ) * (2 * Real.sqrt P.XQ * (1 + P.LB) + 4 * Real.sqrt P.XQ * (2 + P.LB))
              + 2 * Real.sqrt P.XQ) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS1 hc1) hA
        · exact mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hS1 hS2) hc2) hS0) hB
    _ = _ := by ring


/-! ## G. `b ≤ 1` and the closed form in the shape `Row9Numeric.row9_closed_eventually` consumes -/

theorem bQ_le_one (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) : P.bQ ≤ 1 := by
  have hl := one_le_l_of_valid hP
  have hX := one_le_XQ_of_valid hP
  have hF := Ends.S2_localHypsCoreW P hP (by linarith) hl hX
  have h1 : (P.toParams.localFun P.T).b ≤ (P.toParams.localFun P.T).a := hF.b_le_a
  have h2 : (P.toParams.localFun P.T).a ≤ 1 := hF.a_le_one
  exact le_trans h1 h2

/-- **ROW 9, CLOSED FORM** (`b ≤ 1` absorbed):
`|Σ_χ 𝓜[μ_χ,P_χ]| ≤ 3·[(24/π)QL√X(1+log Q)(1+L) + (8/π)(44l+24)L√X((3/4)Q(10+6L)+2)]` —
three times the left-hand side of `Row9Numeric.row9_closed_eventually` at `Q = Qn`, `X = e^L`.

**The leading `3`** is `famMform_muP_le`'s parity factor (see there). It is carried into
`FrobAssembly.R9fun`, whose body has the same `3 *` in front, so every downstream statement
that mentions `R9closed` — `frobSq_le_explicit`, `A3_eventually` — is textually unchanged and
only `R9fun_eventually`'s internal `c` moves by a third. -/
theorem famMform_muP_le_closed (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (F : Family)
    (Qn : ℕ) :
    |familySum F Qn (fun q χ => Mform P (muDensity q χ) (Zones.PXchi P χ))|
      ≤ 3 * (24 / Real.pi * (Qn : ℝ) * P.LB * Real.sqrt (Real.exp P.LB) * (1 + Real.log Qn)
            * (1 + P.LB)
        + 8 / Real.pi * (44 * Zeta23.l P.T + 24) * P.LB * Real.sqrt (Real.exp P.LB)
          * (3 / 4 * (Qn : ℝ) * (10 + 6 * P.LB) + 2)) := by
  have hrow9 := ROW9_le_simple F P hP Qn
  refine (famMform_muP_le P hP hw F Qn).trans ?_
  refine le_trans (by linarith : 3 * ROW9 F P Qn ≤ 3 * (24 * P.bQ / Real.pi * (Qn : ℝ) * P.LB
      * Real.sqrt P.XQ * (1 + Real.log Qn) * (1 + P.LB)
    + 8 * P.bQ / Real.pi * (44 * Zeta23.l P.T + 24) * P.LB * Real.sqrt P.XQ
      * (3 / 4 * (Qn : ℝ) * (10 + 6 * P.LB) + 2))) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 3)
  have hb1 := bQ_le_one P hP hw
  have hb0 : 0 ≤ P.bQ := hP.bQ_pos.le
  have hL0 : 0 ≤ P.LB := hP.LB_pos.le
  have hl1 : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hQ0 : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  have hlogQ0 : 0 ≤ Real.log (Qn : ℝ) := Real.log_natCast_nonneg Qn
  have hX : P.XQ = Real.exp P.LB := rfl
  rw [hX]
  have hsX : 0 ≤ Real.sqrt (Real.exp P.LB) := Real.sqrt_nonneg _
  have hpi : 0 < Real.pi := Real.pi_pos
  have e1 : 24 * P.bQ / Real.pi * (Qn : ℝ) * P.LB * Real.sqrt (Real.exp P.LB) * (1 + Real.log Qn)
        * (1 + P.LB)
      = P.bQ * (24 / Real.pi * (Qn : ℝ) * P.LB * Real.sqrt (Real.exp P.LB) * (1 + Real.log Qn)
        * (1 + P.LB)) := by ring
  have e2 : 8 * P.bQ / Real.pi * (44 * Zeta23.l P.T + 24) * P.LB * Real.sqrt (Real.exp P.LB)
        * (3 / 4 * (Qn : ℝ) * (10 + 6 * P.LB) + 2)
      = P.bQ * (8 / Real.pi * (44 * Zeta23.l P.T + 24) * P.LB * Real.sqrt (Real.exp P.LB)
        * (3 / 4 * (Qn : ℝ) * (10 + 6 * P.LB) + 2)) := by ring
  rw [e1, e2]
  have hc1 : 0 ≤ 24 / Real.pi * (Qn : ℝ) * P.LB * Real.sqrt (Real.exp P.LB) * (1 + Real.log Qn)
      * (1 + P.LB) := by positivity
  have hc2 : 0 ≤ 8 / Real.pi * (44 * Zeta23.l P.T + 24) * P.LB * Real.sqrt (Real.exp P.LB)
      * (3 / 4 * (Qn : ℝ) * (10 + 6 * P.LB) + 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hb1 hc1, mul_le_mul_of_nonneg_right hb1 hc2]

/-! ## H. Row 2's PRIME part at `F.chars` — the debt `trGhatFam_eq_split` moved here

`ZetaQ.abs_famPPart_le` is `famPpart_le` verbatim, and `famPpart_le`'s engine
(`famPpart_grid_eq` + `famPpart_bound` + `sum_famChiSum_weight_le`) hard-codes `Σ*_{χ mod q}`
through `ZetaQ.famChiSum`. Now that `ZetaQ.trGhatFam_eq_split` is stated at `famPPartChars`,
that engine has to run at `F.chars` too. It does, VERBATIM: the inner character set enters
`famPpart_grid_eq` only through the one-line `key` step, and `famPpart_bound` uses
`famChiSum F Qn n` only under `‖·‖`. Below is that engine at an arbitrary selector, plus the
parity instance.

The §5 input is then `cEven_norm_le` / `cOdd_norm_le` — `‖cSel n‖ ≤ (3/4)Q(τ(n−1) + τ(n+1)) + 1`
— in place of `famChiSum_norm_le`'s `(3/2)Qτ(n−1) + 1`. As in §E′ the `τ(n+1)` kernel is the
only cost: the final constant is `15/2` where the full family has `3`, i.e. at most `5/2` times
the full-family bound (`abs_famPPartChars_le_three` states the safe `3`). -/

theorem famPpart_grid_eq_sel {cϱ : ℝ} {p : Setting} {Floc : LocalFun}
    (hFl : LocalHypsCoreW cϱ p Floc) (F : Family) (Qn : ℕ)
    (sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q)) :
    ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q,
        ∑ k ∈ Finset.range p.d, ∫ r, Floc.phiHat r ^ 2 *
          PXc (fun n => χ (n : ZMod q)) p.X (p.tau k + r)
      = -2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
            * (cSel sel F Qn n * ∑ k ∈ Finset.range p.d,
                Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re := by
  classical
  have key : ∀ (n : ℕ) (Kc : ℂ) (An : ℝ),
      (∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q, An * ((χ (n : ZMod q)) * Kc).re)
        = An * (cSel sel F Qn n * Kc).re := by
    intro n Kc An
    simp only [cSel, Finset.sum_mul, Complex.re_sum, Finset.mul_sum]
  have hpull : ∀ q : ℕ, (∑ χ ∈ sel q, (-2 : ℝ) * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
        ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
          * ((χ (n : ZMod q)) * ∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re)
      = -2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ∑ χ ∈ sel q,
          ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
            * ((χ (n : ZMod q)) * ∑ k ∈ Finset.range p.d,
                Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re := by
    intro q
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun χ _ =>
        Ppart_grid_eq hFl (fun n => χ (n : ZMod q))))]
  rw [Finset.sum_congr rfl (fun q _ => hpull q), ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun n _ => key n _ _

theorem famPpart_bound_sel {cϱ : ℝ} {p : Setting} {Floc : LocalFun}
    (hFl : LocalHypsCoreW cϱ p Floc) (F : Family) (Qn : ℕ)
    (sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q)) :
    |∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q,
        ∑ k ∈ Finset.range p.d, ∫ r, Floc.phiHat r ^ 2 *
          PXc (fun n => χ (n : ZMod q)) p.X (p.tau k + r)|
      ≤ p.L ^ 2 / Real.log 2
        * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
            (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖cSel sel F Qn n‖ := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [famPpart_grid_eq_sel hFl F Qn sel, abs_mul, abs_neg, abs_two]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      |((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
        * (cSel sel F Qn n * ∑ k ∈ Finset.range p.d,
            Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
      ≤ ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖cSel sel F Qn n‖)
          * (p.L ^ 2 / (2 * Real.log 2)) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
    have ha : (0:ℝ) ≤ (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) := by
      have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hy : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn2)
      have hA0 := hFl.Aphi_nonneg (Real.log n)
      have hre_le : |(cSel sel F Qn n * ∑ k ∈ Finset.range p.d,
            Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
          ≤ ‖cSel sel F Qn n‖ * ‖∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖ := by
        rw [← norm_mul]
        exact Complex.abs_re_le_norm _
      have hkey := Aphi_mul_norm_tauKernel_le hFl hy
      have hnorm0 : (0:ℝ) ≤ ‖cSel sel F Qn n‖ := norm_nonneg _
      calc |((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
            * (cSel sel F Qn n * ∑ k ∈ Finset.range p.d,
                Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
          = ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))) * (Floc.Aphi (Real.log n)
              * |(cSel sel F Qn n * ∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hA0]; ring
        _ ≤ ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))) * (Floc.Aphi (Real.log n)
              * (‖cSel sel F Qn n‖ * ‖∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖)) := by
            gcongr
        _ = ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))) * (‖cSel sel F Qn n‖
              * (Floc.Aphi (Real.log n) * ‖∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖)) := by ring
        _ ≤ ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))) * (‖cSel sel F Qn n‖
              * (p.L ^ 2 / (2 * Real.log 2))) := by
            gcongr
        _ = ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖cSel sel F Qn n‖)
              * (p.L ^ 2 / (2 * Real.log 2)) := by ring
  calc 2 * |∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
        ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
          * (cSel sel F Qn n * ∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
      ≤ 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖cSel sel F Qn n‖)
            * (p.L ^ 2 / (2 * Real.log 2)) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = p.L ^ 2 / Real.log 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖cSel sel F Qn n‖ := by
        rw [← Finset.sum_mul]
        generalize (∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖cSel sel F Qn n‖) = Ssum
        field_simp

/-- The Λ-weighted sum for a TWO-KERNEL coefficient sequence — `sum_famChiSum_weight_le` with
`(3/4)Q(τ(n−1)+τ(n+1)) + 1` in place of `(3/2)Qτ(n−1) + 1`. -/
theorem sum_cSel_weight_le (Qn N : ℕ) (c : ℕ → ℂ)
    (hc : ∀ n, 2 ≤ n → ‖c n‖ ≤ 3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) + 1) :
    ∑ n ∈ Finset.Ioc 0 N, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖c n‖
      ≤ Real.log (N : ℝ)
          * (3 / 4 * (Qn : ℝ) * (2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ))
                + 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)))
              + 2 * Real.sqrt (N : ℝ)) := by
  classical
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hstep : ∀ n ∈ Finset.Ioc 0 N,
      (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖c n‖
        ≤ Real.log (N : ℝ) * (3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
              + (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)) + 1 / Real.sqrt (n : ℝ)) := by
    intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    have hnr : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hconv : (n : ℝ) ^ (-(1/2 : ℝ)) = 1 / Real.sqrt (n : ℝ) := by
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
    have hsq0 : (0:ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
    have hτ : (0:ℝ) ≤ (tau (n - 1) : ℝ) := Nat.cast_nonneg _
    have hτ' : (0:ℝ) ≤ (tau (n + 1) : ℝ) := Nat.cast_nonneg _
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have hL1 : (Λ 1 : ℝ) = 0 := by simp [ArithmeticFunction.vonMangoldt_apply_one]
      rw [hL1]
      have hrhs : 0 ≤ Real.log (N : ℝ) * (3 / 4 * (Qn : ℝ) *
          ((tau (1 - 1) : ℝ) / Real.sqrt ((1:ℕ) : ℝ)
            + (tau (1 + 1) : ℝ) / Real.sqrt ((1:ℕ) : ℝ)) + 1 / Real.sqrt ((1:ℕ) : ℝ)) := by
        have h0 : (0:ℝ) ≤ 3 / 4 * (Qn : ℝ) * ((tau (1 - 1) : ℝ) / Real.sqrt ((1:ℕ) : ℝ)
            + (tau (1 + 1) : ℝ) / Real.sqrt ((1:ℕ) : ℝ)) + 1 / Real.sqrt ((1:ℕ) : ℝ) := by
          positivity
        exact mul_nonneg hlog0 h0
      simpa using hrhs
    · have hLam := vonMangoldt_le_log_of_le n N (by omega) hnN
      have hLam0 : (0:ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have hnorm := hc n h2
      rw [hconv]
      calc (Λ n : ℝ) * (1 / Real.sqrt (n : ℝ)) * ‖c n‖
          ≤ Real.log (N : ℝ) * (1 / Real.sqrt (n : ℝ))
              * (3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) + 1) := by
            gcongr
        _ = Real.log (N : ℝ) * (3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
              + (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)) + 1 / Real.sqrt (n : ℝ)) := by
            field_simp
  refine (Finset.sum_le_sum hstep).trans ?_
  have hA := sum_tau_pred_div_sqrt_le N
  have hA' := sum_tau_succ_div_sqrt_le N
  have hB : ∑ n ∈ Finset.Ioc 0 N, (1:ℝ) / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (N : ℝ) :=
    sum_one_div_sqrt_le N
  calc ∑ n ∈ Finset.Ioc 0 N, Real.log (N : ℝ)
          * (3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
              + (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ)) + 1 / Real.sqrt (n : ℝ))
      = Real.log (N : ℝ) * (3 / 4 * (Qn : ℝ)
          * ((∑ n ∈ Finset.Ioc 0 N, (tau (n - 1) : ℝ) / Real.sqrt (n : ℝ))
              + ∑ n ∈ Finset.Ioc 0 N, (tau (n + 1) : ℝ) / Real.sqrt (n : ℝ))
          + ∑ n ∈ Finset.Ioc 0 N, (1:ℝ) / Real.sqrt (n : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ Real.log (N : ℝ) * (3 / 4 * (Qn : ℝ)
          * (2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ))
              + 2 * Real.sqrt 2 * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)))
          + 2 * Real.sqrt (N : ℝ)) := by
        gcongr

/-- **§5's Ramanujan bound on the re-spelled prime part**, for each of Corollary 3's four
parity families: `|famPPartChars| ≤ L³√X/log 2 · ((15/2)·Q(1+L) + 2)`.
Compare `ZetaQ.famPpart_le` (`= ZetaQ.abs_famPPart_le`), whose constant is `3·Q(1+L) + 2`. -/
theorem abs_famPPartChars_le (P : ParamsQ) (F : Family) (Qn : ℕ) (hP : P.Valid)
    (hw : SideCondWrange P)
    (hchars : (∀ q, F.chars q = primitiveCharsEven q)
      ∨ (∀ q, F.chars q = primitiveCharsOdd q)) :
    |famPPartChars P F Qn|
      ≤ P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2) := by
  have hl : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hlne : Zeta23.l P.T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hl)
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have hwL : P.w ≤ P.LB / 8 := by
    have := hw; unfold SideCondWrange at this; linarith
  have hFl := Ends.S2_localHypsCoreW P hP hwL hl hX1
  obtain ⟨sel, hsel, hcs⟩ :
      ∃ sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q),
        (∀ q, F.chars q = sel q) ∧ ∀ n, 2 ≤ n →
          ‖cSel sel F Qn n‖
            ≤ 3 / 4 * (Qn : ℝ) * ((tau (n - 1) : ℝ) + (tau (n + 1) : ℝ)) + 1 := by
    rcases hchars with h | h
    · exact ⟨primitiveCharsEven, h, fun n hn => by
        rw [cSel_even_eq]; exact cEven_norm_le F Qn n hn⟩
    · exact ⟨primitiveCharsOdd, h, fun n hn => by
        rw [cSel_odd_eq]; exact cOdd_norm_le F Qn n hn⟩
  have hrw : famPPartChars P F Qn
      = ∑ q ∈ F.moduli Qn, ∑ χ ∈ sel q, ∑ k ∈ Finset.range P.dQ,
          ∫ r, P.phiHatQ r ^ 2 * Zones.PXchi P χ (P.tauQ k + r) := by
    unfold famPPartChars
    exact Finset.sum_congr rfl fun q _ => by rw [hsel q]
  rw [hrw]
  have h := famPpart_bound_sel hFl F Qn sel
  rw [Ends.toSetting_d P hlne, Ends.toSetting_X P hlne, Ends.S1_toSetting_L P hlne] at h
  simp only [Ends.toSetting_tau P hlne] at h
  refine le_trans h ?_
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set N := ⌊P.XQ⌋₊ with hN
  have hNpos : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX1)
  have hNle : ((N : ℕ) : ℝ) ≤ P.XQ := Nat.floor_le (by linarith)
  have hs : Real.sqrt ((N : ℕ) : ℝ) ≤ Real.sqrt P.XQ := Real.sqrt_le_sqrt hNle
  have hs0 : (0:ℝ) ≤ Real.sqrt ((N : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hNr : (0:ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hNr1 : (1:ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hlogX : Real.log P.XQ = P.LB := Real.log_exp _
  have ht : Real.log ((N : ℕ) : ℝ) ≤ P.LB := by
    rw [← hlogX]; exact Real.log_le_log hNr hNle
  have ht0 : (0:ℝ) ≤ Real.log ((N : ℕ) : ℝ) := Real.log_nonneg hNr1
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hsX : (0:ℝ) ≤ Real.sqrt P.XQ := Real.sqrt_nonneg _
  have hsum := sum_cSel_weight_le Qn N (cSel sel F Qn) hcs
  have hS21 : S2 P ≤ 4 * S1 P := S2_le_four_S1 P hX1
  have hS2' : 2 * Real.sqrt 2 * Real.sqrt (((N : ℕ) : ℝ) + 1)
        * (1 + Real.log (((N : ℕ) : ℝ) + 1))
      ≤ 4 * (2 * Real.sqrt ((N : ℕ) : ℝ) * (1 + Real.log ((N : ℕ) : ℝ))) := by
    have e2 : S2 P = 2 * Real.sqrt 2 * Real.sqrt (((N : ℕ) : ℝ) + 1)
        * (1 + Real.log (((N : ℕ) : ℝ) + 1)) := by rw [S2, hN]
    have e1 : S1 P = 2 * Real.sqrt ((N : ℕ) : ℝ) * (1 + Real.log ((N : ℕ) : ℝ)) := by
      rw [S1, hN]
    rw [e2, e1] at hS21
    exact hS21
  have hcoef : (0:ℝ) ≤ P.LB ^ 2 / Real.log 2 := by positivity
  calc P.LB ^ 2 / Real.log 2
        * ∑ n ∈ Finset.Ioc 0 N, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖cSel sel F Qn n‖
      ≤ P.LB ^ 2 / Real.log 2 * (Real.log ((N : ℕ) : ℝ)
          * (3 / 4 * (Qn : ℝ) * (2 * Real.sqrt ((N : ℕ) : ℝ) * (1 + Real.log ((N : ℕ) : ℝ))
                + 2 * Real.sqrt 2 * Real.sqrt (((N : ℕ) : ℝ) + 1)
                  * (1 + Real.log (((N : ℕ) : ℝ) + 1)))
              + 2 * Real.sqrt ((N : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left hsum hcoef
    _ ≤ P.LB ^ 2 / Real.log 2 * (Real.log ((N : ℕ) : ℝ)
          * (3 / 4 * (Qn : ℝ) * (5 * (2 * Real.sqrt ((N : ℕ) : ℝ)
                * (1 + Real.log ((N : ℕ) : ℝ)))) + 2 * Real.sqrt ((N : ℕ) : ℝ))) := by
        have hin : 2 * Real.sqrt ((N : ℕ) : ℝ) * (1 + Real.log ((N : ℕ) : ℝ))
              + 2 * Real.sqrt 2 * Real.sqrt (((N : ℕ) : ℝ) + 1)
                * (1 + Real.log (((N : ℕ) : ℝ) + 1))
            ≤ 5 * (2 * Real.sqrt ((N : ℕ) : ℝ) * (1 + Real.log ((N : ℕ) : ℝ))) := by
          linarith
        gcongr
    _ ≤ P.LB ^ 2 / Real.log 2 * (P.LB
          * (3 / 4 * (Qn : ℝ) * (5 * (2 * Real.sqrt P.XQ * (1 + P.LB)))
              + 2 * Real.sqrt P.XQ)) := by
        gcongr
    _ = P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2) := by
        ring

/-- The same, against `3 ×` the FULL-family constant of `ZetaQ.abs_famPPart_le`. -/
theorem abs_famPPartChars_le_three (P : ParamsQ) (F : Family) (Qn : ℕ) (hP : P.Valid)
    (hw : SideCondWrange P)
    (hchars : (∀ q, F.chars q = primitiveCharsEven q)
      ∨ (∀ q, F.chars q = primitiveCharsOdd q)) :
    |famPPartChars P F Qn|
      ≤ 3 * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2)) := by
  refine (abs_famPPartChars_le P F Qn hP hw hchars).trans ?_
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have hsX : (0:ℝ) ≤ Real.sqrt P.XQ := Real.sqrt_nonneg _
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc : (0:ℝ) ≤ P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 := by positivity
  have hin : 15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2
      ≤ 3 * (3 * (Qn : ℝ) * (1 + P.LB) + 2) := by nlinarith [hLB.le, hQ]
  nlinarith [mul_le_mul_of_nonneg_left hin hc]

/-- Row 2's prime part for the four parity families, with no hypothesis beyond the design's
own. -/
theorem abs_famPPartChars_le_of_not_isFull (P : ParamsQ) {F : Family} (hF : ¬ F.IsFull)
    (Qn : ℕ) (hP : P.Valid) (hw : SideCondWrange P) :
    |famPPartChars P F Qn|
      ≤ P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2) :=
  abs_famPPartChars_le P F Qn hP hw (chars_parity_of_not_isFull hF)

/-- **Row 2 of §10.2's ledger at `F.chars`** — the parity counterpart of
`ZetaQ.abs_trGhatFam_sub_muPart_le`, assembled from `ZetaQ.trGhatFam_eq_split` and the bound
just above. This is the statement the four parity families need. -/
theorem abs_trGhatFam_sub_muPartChars_le (P : ParamsQ) {F : Family} (hF : ¬ F.IsFull)
    (Qn : ℕ) (hP : P.Valid) (hw : SideCondWrange P) :
    |trGhatFam P F Qn - (P.aQ * P.LB ^ 2)⁻¹ * famMuPartChars P F Qn|
      ≤ (P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2
              * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2)) := by
  have ha : 0 < P.aQ := aQ_pos_of_valid hP hw
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have hc : (0:ℝ) ≤ (P.aQ * P.LB ^ 2)⁻¹ := by positivity
  rw [trGhatFam_eq_split P F Qn hP hw,
    show (P.aQ * P.LB ^ 2)⁻¹ * (famMuPartChars P F Qn + famPPartChars P F Qn)
        - (P.aQ * P.LB ^ 2)⁻¹ * famMuPartChars P F Qn
      = (P.aQ * P.LB ^ 2)⁻¹ * famPPartChars P F Qn by ring, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_famPPartChars_le_of_not_isFull P hF Qn hP hw) hc


end FamRows

/-! # The trace row (`trace_row_eventually_aux`), at the family's own character set

`ZetaQ.famMuPart_ge` / `ZetaQ.muPart_ge_NfamQ_sub` price each modulus at the FULL `phiStar q`
(through `sizeR_eq_sum_phiStar` and `famRvM_upper_raw`), which is why they carry `F.IsFull`.
Below is the same chain at `|F.chars q|` — which is what `ZetaQ.trGhatFam_eq_split` and
`FamRows.abs_trGhatFam_sub_muPartChars_le` actually deliver on a parity family — and with it
`trace_row_eventually_aux` is proved in all six branches.

**WHY THESE TWO THEOREMS ARE HERE AND NOT IN `ZetaQ/Budget.lean`.** They were moved down one
level from `Budget`'s section `TraceRow`, verbatim apart from the `case neg` branch. The
parity branch's only genuinely new input is `FamRows.abs_trGhatFam_sub_muPartChars_le`, at the
foot of this file, and `FrobRow9` imports `Budget`, so it cannot be cited there. Moving the
two theorems is the least invasive of the three repairs available (the alternatives being an
extra hypothesis threaded through all four call sites, or hoisting the whole `FamRows` chain
into `Budget`): no statement changes and no signature changes. The only other cost is one
added `import ZetaQ.FrobRow9` in `ZetaQ/JoinCert.lean`.

**A finding.** The `sorry` comment this replaces predicted that §12.3's count
`ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn` would be needed to convert
`∑_q |F.chars q|·ℓ₁,q` back to `½·∑_q phiStar q·ℓ₁,q + O(Q log Q)`. It is NOT. Once the
re-spelling is consistent, every other object in the argument (`NfamQ`, `Family.sizeR`,
`rowR1_NfamQ_lower_eventually`, `row2_generic_eventually`, `sizeR_floor_eventually`) is
ALREADY an `F.chars` object proved in all six branches, so the two sides match with no
counting bridge. The `ParityCount` layer is what makes those downstream lemmas true; it is
not spent a second time here.

**A second finding.** `row2_eventually` carries the FULL-family Ramanujan constant
`3·Q(1+L) + 2`, whereas the parity row-2 bound `FamRows.abs_trGhatFam_sub_muPartChars_le`
carries `15/2·Q(1+L) + 2` (2.5× larger — the price of the two-kernel `cEven`/`cOdd`
estimate). `row2_parity_eventually` below re-runs `row2_generic_eventually` at
`Row2Numeric.row2_error_eventually_gen`'s constant `c = 1/30000` instead of `1/10000`, which
buys the factor 3 with room; no other change. -/

section TraceRowChars

open Zeta23.PrimeSide Zeta23.ThmE
open Topology Filter
open Real

/-- **The q-uniform RvM count summed over `𝔉_Q`, UPPER half, at the family's own weight.**
The mirror of `ZetaQ.famRvM_lower_weight`; sharper than `ZetaQ.famRvM_upper_raw`, which
prices each modulus at `phiStar q`. No `F.IsFull`. -/
theorem famRvM_upper_weight (P : ParamsQ) (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn) {A T₀ : ℝ}
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    NfamQ P F Qn
      ≤ ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) *
          (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            + A * Real.log ((q : ℝ) * (P.T + 2))) := by
  have hexp : NfamQ P F Qn
      = ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, NcountQ q χ P.T (2 * P.T) := rfl
  rw [hexp]
  refine Finset.sum_le_sum ?_
  intro q hq
  have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
  have : NeZero q := ⟨by omega⟩
  have hstep : ∀ χ ∈ F.chars q, NcountQ q χ P.T (2 * P.T)
      ≤ P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T + A * Real.log ((q : ℝ) * (P.T + 2)) := by
    intro χ hχ
    have hp : χ.IsPrimitive :=
      EFChi.isPrimitive_of_mem_primitiveChars (F.chars_subset q hχ)
    have hab := abs_le.mp (hrvm q χ hq1 hp P.T hT)
    have hNc : NcountQ q χ P.T (2 * P.T)
        = ((Zeta23.ThmE.NcountL χ P.T (2 * P.T) : ℕ) : ℝ) := by
      unfold NcountQ; rw [dif_neg (show ¬ q = 0 by omega)]
    rw [hNc]
    linarith [hab.2]
  calc ∑ χ ∈ F.chars q, NcountQ q χ P.T (2 * P.T)
      ≤ ∑ _χ ∈ F.chars q,
          (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            + A * Real.log ((q : ℝ) * (P.T + 2))) := Finset.sum_le_sum hstep
    _ = ((F.chars q).card : ℝ) *
          (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            + A * Real.log ((q : ℝ) * (P.T + 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **`ZetaQ.famMuPart_ge` at the family's own character set** — no `F.IsFull`.

`aL²·(T/2π)·∑_q |F.chars q|·ℓ_{1,q} − |𝔉|·muErr ≤ famMuPartChars`. The per-character input
(`ZetaQ.muPart_chi_approx`) does not see the character set at all; the ONLY change from
`famMuPart_ge` is `sizeR_eq_sum_weight` in place of `sizeR_eq_sum_phiStar`. -/
theorem famMuPartChars_ge (P : ParamsQ) (hP : P.Valid) (hw : SideCondWrange P) (F : Family)
    (Qn : ℕ) :
    P.aQ * P.LB ^ 2 * (P.T / (2 * π))
        * (∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * Zeta23.ThmE.ell1q q P.T)
      - F.sizeR Qn * muErr P Qn
      ≤ famMuPartChars P F Qn := by
  have hLB : 0 ≤ P.LB := (EFChi.LB_pos_of_valid hP).le
  have hpi : 0 < π := Real.pi_pos
  have hstep : ∀ q ∈ F.moduli Qn, ∀ χ ∈ F.chars q,
      P.aQ * P.LB ^ 2 * (P.T * Zeta23.ThmE.ell1q q P.T / (2 * π)) - muErr P Qn
        ≤ ∑ k ∈ Finset.range P.dQ, ∫ r, P.phiHatQ r ^ 2 * muDensity q χ (P.tauQ k + r) := by
    intro q hq χ _
    have hq1 : 1 ≤ q := one_le_of_mem_moduli hq
    have h := (abs_le.mp (muPart_chi_approx P hP hw hq1 χ)).1
    have hlog := log_le_log_Qn_of_mem hq
    have hmono : 4 * π * P.LB * (Real.log q / (2 * π) + 11 / π * Zeta23.l P.T)
        ≤ 4 * π * P.LB * (Real.log Qn / (2 * π) + 11 / π * Zeta23.l P.T) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : Real.log q / (2 * π) ≤ Real.log Qn / (2 * π) :=
        div_le_div_of_nonneg_right hlog (by positivity)
      linarith
    unfold muErr
    linarith
  unfold famMuPartChars
  calc P.aQ * P.LB ^ 2 * (P.T / (2 * π))
          * (∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * Zeta23.ThmE.ell1q q P.T)
        - F.sizeR Qn * muErr P Qn
      = ∑ q ∈ F.moduli Qn, ∑ _χ ∈ F.chars q,
          (P.aQ * P.LB ^ 2 * (P.T * Zeta23.ThmE.ell1q q P.T / (2 * π)) - muErr P Qn) := by
        rw [sizeR_eq_sum_weight, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => hstep q hq χ hχ

/-- **`ZetaQ.muPart_ge_NfamQ_sub` at the family's own character set** — no `F.IsFull`:
`(aL²)⁻¹·famMuPartChars ≥ 𝒩 − |𝔉|·(A·log(Q(T+2)) + muErr/(aL²))`.

This is the mu-part lower bound at the parity weight that `trace_row_eventually_aux`'s
`case neg` was missing. Both sides are now `F.chars` objects, so no §12.3 counting bridge is
required — see the section header. -/
theorem muPartChars_ge_NfamQ_sub (P : ParamsQ) (hP : P.Valid) (hw : SideCondWrange P)
    (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn) {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    NfamQ P F Qn
        - F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)) + muErr P Qn / (P.aQ * P.LB ^ 2))
      ≤ (P.aQ * P.LB ^ 2)⁻¹ * famMuPartChars P F Qn := by
  have ha : 0 < P.aQ := hP.aQ_pos
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have haL : 0 < P.aQ * P.LB ^ 2 := by positivity
  have hT0 : 0 < P.T := T_posQ hP
  have hup := famRvM_upper_weight P F Qn hQn hrvm hT
  have hmu := famMuPartChars_ge P hP hw F Qn
  have hS : ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * (A * Real.log ((q:ℝ) * (P.T + 2)))
      ≤ F.sizeR Qn * (A * Real.log ((Qn:ℝ) * (P.T + 2))) := by
    rw [sizeR_eq_sum_weight, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq1 : 1 ≤ q := one_le_of_mem_moduli hq
    have hle : (q:ℝ) ≤ Qn := by exact_mod_cast le_Qn_of_mem_moduli hq
    have hqR : (0:ℝ) < q := by exact_mod_cast hq1
    have hmono : Real.log ((q:ℝ) * (P.T + 2)) ≤ Real.log ((Qn:ℝ) * (P.T + 2)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hA) (by positivity)
  have hsplit : ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T + A * Real.log ((q : ℝ) * (P.T + 2)))
      = P.T / (2 * π) * (∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * Zeta23.ThmE.ell1q q P.T)
        + ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * (A * Real.log ((q:ℝ) * (P.T + 2))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hsplit] at hup
  set S := ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * Zeta23.ThmE.ell1q q P.T with hSdef
  have h1 : (P.aQ * P.LB ^ 2)⁻¹ * (P.aQ * P.LB ^ 2 * (P.T / (2 * π)) * S
        - F.sizeR Qn * muErr P Qn)
      ≤ (P.aQ * P.LB ^ 2)⁻¹ * famMuPartChars P F Qn :=
    mul_le_mul_of_nonneg_left hmu (by positivity)
  have h2 : (P.aQ * P.LB ^ 2)⁻¹ * (P.aQ * P.LB ^ 2 * (P.T / (2 * π)) * S
        - F.sizeR Qn * muErr P Qn)
      = P.T / (2 * π) * S - F.sizeR Qn * (muErr P Qn / (P.aQ * P.LB ^ 2)) := by
    field_simp
  linarith [h1, h2, hup, hS]

/-- **`ZetaQ.trace_row_of_muPart` for the four parity families** — `trGhatFam` reduced to its
`μ_q` part at `F.chars`, with the `15/2` constant that the two-kernel `cEven` / `cOdd` bound
of `FamRows.abs_famPPartChars_le_of_not_isFull` costs. -/
theorem trace_row_of_muPartChars (F : Family) (hF : ¬ F.IsFull) (r ε : ℝ) (Qn : ℕ)
    (P : ParamsQ) (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hmu : (1 - rowR1 F P) * NfamQ P F Qn
        ≤ (P.aQ * P.LB ^ 2)⁻¹ * famMuPartChars P F Qn
          - (P.aQ * P.LB ^ 2)⁻¹
              * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2
                  * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2))) :
    (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn := by
  obtain ⟨hP, -, -, -, -, hw, -, -, -, -⟩ := hdes
  have key := FamRows.abs_trGhatFam_sub_muPartChars_le P hF Qn hP hw
  have h := (abs_le.mp key).1
  linarith

/-- **Row 2, eventually, with the parity `15/2` constant** — `ZetaQ.row2_generic_eventually`
run at `Row2Numeric`'s constant `c = 1/30000` instead of `1/10000`, which buys exactly the
factor `3` that `15/2·Q(1+L) + 2 ≤ 3·(3·Q(1+L) + 2)` costs. Proved for ALL SIX families. -/
theorem row2_parity_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2))
        ≤ traceRowSlack F * Family.sizeR F Qn * P.T
          - 2 * (Family.sizeR F Qn * (P.T / (400 * π))) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Row2Numeric.row2_error_eventually_gen r ε (1 / 30000) hr hε (by norm_num)),
    sizeR_floor_eventually F, eventually_ge_atTop 2] with Qn hrow hsz hQn2
  intro P hdes
  have hP : P.Valid := hdes.1
  have hLL := LL_of_design hdes
  have hT := T_of_design hdes
  dsimp only at hrow
  rw [← hLL, ← hT] at hrow
  have hLL0 : 0 ≤ P.LL :=
    le_trans (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Qn by omega)))
      (LL_ge_log_of_design hdes (by omega))
  have hLB0 : 0 ≤ P.LB := (EFChi.LB_pos_of_valid hP).le
  have ha0 : 0 < P.aQ := hP.aQ_pos
  set Lq := 1.2507321515 * P.LL with hLq
  have hLq0 : 0 ≤ Lq := by rw [hLq]; exact mul_nonneg (by norm_num) hLL0
  have hlamF : F.lamStar ≤ 1.2507321515 := by
    cases F <;>
      simp only [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10, lamStarEvenDyad12] <;>
      norm_num
  have hLBle : P.LB ≤ Lq := by
    rw [LB_of_design hdes, hLq]
    exact mul_le_mul_of_nonneg_right hlamF hLL0
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hQ0 : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  -- the `15/2` constant against `3 ×` the `3` constant, at fixed `(aL²)⁻¹·L³√X/log 2`
  have hfac : (0:ℝ) ≤ (P.aQ * P.LB ^ 2)⁻¹ * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2) := by
    have : (0:ℝ) ≤ Real.sqrt P.XQ := Real.sqrt_nonneg _
    positivity
  have hC : 15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2 ≤ 3 * (3 * (Qn : ℝ) * (1 + P.LB) + 2) := by
    nlinarith
  have h0 : (P.aQ * P.LB ^ 2)⁻¹
        * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2))
      ≤ 3 * ((P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2))) := by
    have h := mul_le_mul_of_nonneg_left hC hfac
    calc (P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2))
        = (P.aQ * P.LB ^ 2)⁻¹ * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2)
            * (15 / 2 * (Qn : ℝ) * (1 + P.LB) + 2) := by ring
      _ ≤ (P.aQ * P.LB ^ 2)⁻¹ * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2)
            * (3 * (3 * (Qn : ℝ) * (1 + P.LB) + 2)) := h
      _ = _ := by ring
  have hmono : 2 * P.LB * Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2)
        / Real.log 2
      ≤ 2 * Lq * Real.sqrt (Real.exp Lq) * (3 * (Qn : ℝ) * (1 + Lq) + 2) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    have hs : Real.sqrt (Real.exp P.LB) ≤ Real.sqrt (Real.exp Lq) :=
      Real.sqrt_le_sqrt (Real.exp_le_exp.mpr hLBle)
    have hb : 3 * (Qn : ℝ) * (1 + P.LB) + 2 ≤ 3 * (Qn : ℝ) * (1 + Lq) + 2 := by nlinarith
    apply mul_le_mul (mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by linarith)) hb
      (by positivity) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  have h1 := row2_term_le P hP Qn
  have hT0 : 0 ≤ P.T := (T_posQ hP).le
  have hS : 0 ≤ Family.sizeR F Qn := by unfold Family.sizeR; positivity
  have hpi : 3 < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  have hslack : (1:ℝ) / 200 ≤ traceRowSlack F := by
    cases F <;> norm_num [traceRowSlack]
  have hc : 1 / 300 ≤ traceRowSlack F - 1 / (200 * π) := by
    have : 1 / (200 * π) ≤ 1 / 600 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hconst : traceRowSlack F * Family.sizeR F Qn * P.T
        - 2 * (Family.sizeR F Qn * (P.T / (400 * π)))
      = (traceRowSlack F - 1 / (200 * π)) * Family.sizeR F Qn * P.T := by
    field_simp; ring
  rw [hconst]
  calc _ ≤ _ := h0
    _ ≤ 3 * (2 * P.LB * Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2)
          / Real.log 2) := by linarith
    _ ≤ 3 * (2 * Lq * Real.sqrt (Real.exp Lq) * (3 * (Qn : ℝ) * (1 + Lq) + 2)
          / Real.log 2) := by linarith
    _ ≤ 3 * (1 / 30000 * (Qn:ℝ) ^ 2 * P.T) := by linarith
    _ = 1 / 10000 * (Qn:ℝ) ^ 2 * P.T := by ring
    _ ≤ 1 / 300 * Family.sizeR F Qn * P.T := by
        have hstep : 1 / 10000 * (Qn:ℝ) ^ 2 ≤ 1 / 300 * Family.sizeR F Qn := by
          linarith [hsz]
        exact mul_le_mul_of_nonneg_right hstep hT0
    _ ≤ (traceRowSlack F - 1 / (200 * π)) * Family.sizeR F Qn * P.T := by
        gcongr

set_option maxHeartbeats 1000000 in
/-- **`trace_row_eventually_aux`'s `¬ F.IsFull` branch.**

The `IsFull` branch's chain is reproduced with `muPart_ge_NfamQ_sub` replaced by
`muPartChars_ge_NfamQ_sub`, `trace_row_of_muPart` by `trace_row_of_muPartChars`, and
`row2_eventually` by `row2_parity_eventually` (the `15/2` constant).
`rowR1_NfamQ_lower_eventually` is used unchanged: it is already proved in all six branches.
`hF` is passed only so that the call site reads as the parity branch it is — the chain itself
never needs it. -/
theorem trace_row_eventually_notFull (F : Family) (hF : ¬ F.IsFull) (r ε : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn := by
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hre : (0:ℝ) < r + ε := by linarith
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
    (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  filter_upwards [rowR1_NfamQ_lower_eventually F r ε hr hε, row2_parity_eventually F r ε hr hε,
    rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀,
    hTtop.eventually_ge_atTop (400 * π * cErr (cWinDesign F)), eventually_ge_atTop 2]
    with Qn hlow hrow2 herr hT0 hTE hQn
  intro P hdes
  apply trace_row_of_muPartChars F hF r ε Qn P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = Qn := hdes.2.1
  have hT : P.T = Twin Qn r ε := hdes.2.2.1
  have hlam : P.lam = F.lamStar := hdes.2.2.2.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hpi0 : 0 < π := Real.pi_pos
  have hS : 0 ≤ Family.sizeR F Qn := by unfold Family.sizeR; positivity
  have h1 := muPartChars_ge_NfamQ_sub P hP hwr F Qn hQn hA.le hrvm (by rw [hT]; exact hT0)
  have h2 := hlow P hdes
  have h3 : A * Real.log ((Qn:ℝ) * (P.T + 2)) ≤ P.T / (400 * π) := by
    rw [hT, le_div_iff₀ (by positivity)]; linarith [herr]
  have h4 : muErr P Qn / (P.aQ * P.LB ^ 2) ≤ P.T / (400 * π) := by
    refine (muErr_div_le P hP Qn (by omega) hQ
      (by rw [hlam]; exact one_le_lamStar_of_family F)).trans ?_
    rw [cWin_of_design hdes, hT, le_div_iff₀ (by positivity)]
    linarith [hTE]
  have h5 := hrow2 P hdes
  have h34 : Family.sizeR F Qn
        * (A * Real.log ((Qn:ℝ) * (P.T + 2)) + muErr P Qn / (P.aQ * P.LB ^ 2))
      ≤ Family.sizeR F Qn * (P.T / (400 * π) + P.T / (400 * π)) :=
    mul_le_mul_of_nonneg_left (add_le_add h3 h4) hS
  linarith [h1, h2, h5, h34]

/-! ### (F) assembly — relocated verbatim from `ZetaQ/Budget.lean`'s section `TraceRow` -/

/-- **`trace_row`, eventually in `Q` along the design of record.**  See the docstring of
`ZetaQ.trace_row` for why the statement at EVERY design point is out of reach of this route.

**PROVED IN ALL SIX BRANCHES.** The `F.IsFull` branch is the original chain
(`muPart_ge_NfamQ_sub` / `trace_row_of_muPart` / `row2_eventually`); the four Corollary 3
parity families go through `trace_row_eventually_notFull`, the same chain at the family's own
character set. -/
theorem trace_row_eventually_aux (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn := by
  by_cases hF : F.IsFull
  case neg => exact trace_row_eventually_notFull F hF r ε hr hε
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hre : (0:ℝ) < r + ε := by linarith
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
    (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  filter_upwards [rowR1_NfamQ_lower_eventually F r ε hr hε, row2_eventually F r ε hr hε,
    rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀,
    hTtop.eventually_ge_atTop (400 * π * cErr (cWinDesign F)), eventually_ge_atTop 2]
    with Qn hlow hrow2 herr hT0 hTE hQn
  intro P hdes
  apply trace_row_of_muPart F hF r ε Qn P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = Qn := hdes.2.1
  have hT : P.T = Twin Qn r ε := hdes.2.2.1
  have hlam : P.lam = F.lamStar := hdes.2.2.2.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hpi0 : 0 < π := Real.pi_pos
  have hS : 0 ≤ Family.sizeR F Qn := by unfold Family.sizeR; positivity
  have h1 := muPart_ge_NfamQ_sub P hP hwr hF Qn hQn hA.le hrvm (by rw [hT]; exact hT0)
  have h2 := hlow P hdes
  have h3 : A * Real.log ((Qn:ℝ) * (P.T + 2)) ≤ P.T / (400 * π) := by
    rw [hT, le_div_iff₀ (by positivity)]; linarith [herr]
  have h4 : muErr P Qn / (P.aQ * P.LB ^ 2) ≤ P.T / (400 * π) := by
    refine (muErr_div_le P hP Qn (by omega) hQ
      (by rw [hlam]; exact one_le_lamStar_of_family F)).trans ?_
    rw [cWin_of_design hdes, hT, le_div_iff₀ (by positivity)]
    linarith [hTE]
  have h5 := hrow2 P hdes
  have h34 : Family.sizeR F Qn
        * (A * Real.log ((Qn:ℝ) * (P.T + 2)) + muErr P Qn / (P.aQ * P.LB ^ 2))
      ≤ Family.sizeR F Qn * (P.T / (400 * π) + P.T / (400 * π)) :=
    mul_le_mul_of_nonneg_left (add_le_add h3 h4) hS
  linarith [h1, h2, h5, h34]

/-- **`trace_row`, eventually — the `∃ Q₀` form matching `assembly_at_lamStar`.** -/
theorem trace_row_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) → ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (trace_row_eventually_aux F r ε hr hε)
  refine ⟨N, fun Qn hQn P hdes => hN Qn ?_ P hdes⟩
  exact_mod_cast hQn

end TraceRowChars

end ZetaQ
