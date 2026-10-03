/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Gallagher.lean — paper §6, Lemma 6.1 by GALLAGHER'S ELEMENTARY LARGE SIEVE.

Imports `ZetaQ.Sieve` ONLY (for `e`, `expSum`, `charSum`, `l2sq`, the Farey spacing
`farey_spaced`, the Gauss-sum transfer `primitive_decomposition` and the orthogonality
`intervalIntegral_e_orth`). Parameter-free, like `Sieve.lean`: no `ParamsQ`, `T`, `λ`, `X`.

--------------------------------------------------------------------------------------
## What this file does, and why it exists
--------------------------------------------------------------------------------------

`Sieve.lean` builds the SHARP multiplicative large sieve `N + Q² − 1` from the Beurling–Selberg
majorant, and its one from-zero gap is `ZetaQ.l2_concentration_exists` (Selberg's extremal
problem; a `sorry`). This file proves, **sorry-free**, the multiplicative large sieve at the
**Gallagher budget** `Q² + πN`:

    Σ_{q≤Q} Σ*_{χ mod q} |Σ_{n≤N} a_n χ(n)|²  ≤  (Q² + πN) Σ_{n≤N} |a_n|²

(`multiplicative_large_sieve_gallagher`, with the subfamily and indexed-family forms), from
Gallagher's additive inequality (Gallagher 1967; Montgomery, Bull. AMS 84 (1978), Thm 1)

    Σ_i |S(θ_i)|²  ≤  (δ⁻¹ + πN) Σ_{n≤N} |a_n|²     for δ-separated θ_i mod 1

(`gallagher_additive_large_sieve`, stated in the exact binder shape of
`ZetaQ.SharpAdditiveLargeSieve` with `N − 1 + δ⁻¹` replaced by `δ⁻¹ + πN`).

**Why the weaker length term is harmless.** The coefficient of `δ⁻¹` — hence of `Q²` at
`δ = Q⁻²` — is exactly `1`, so the family constant `C = Q²/|𝔉_Q|` (`ZetaQ.Cfam`) is
unchanged; only the length term moves, `N − 1 ↦ πN`. Every consumer uses the budget only
through `Q² ≤ B` and `B ≤ Q²(1 + O(Q^{−δ}))` in the sieve-efficient range `X ≤ Q^{2−δ}`
(`Zones.lemma43_budget_is_Qsq`, whose constant is `4` rather than `2` for this reason, and
`Ends.pi_mul_X_le_of_sieve_eff`). The consumers (`Ends.LargeSieveHyp`,
`Zones.LargeSieveFamily`, `Zones.sieveBudgetQ`) are stated at this budget and discharged from
this file; the sharp chain of `Sieve.lean` is kept as the record of the sharp statement and
of `sharpAdditiveLargeSieveUnrestricted_false`, but no headline theorem consumes it.

**The weight is still declined.** `multiplicative_large_sieve_gallagher` drops `φ(q)/q ≤ 1`
exactly as `multiplicative_large_sieve_of_additive_of_le_one` does (paper §6 Remark).

Proof architecture:
  (a) `point_bound` — |f(x)| ≤ δ⁻¹∫_I|f| + ½∫_I|f′| on `I = [x − δ/2, x + δ/2]` (weighted FTC);
  (b1) `parseval_trig` — ∫₀¹|Σ_{n∈s} b_n e(nθ)|² = Σ|b_n|² (orthogonality `intervalIntegral_e_orth`);
  (b2) `hasDerivAt_normSq` + `abs_deriv_normSq_le` — (|S|²)′ = 2⟪S, S′⟫ and |2⟪S,S′⟫| ≤ 2|S||D|,
       where `D = S′ − 2πi·((N+1)/2)·S` is the CENTRED derivative (frequencies `n − (N+1)/2`);
  (b3) `sum_integral_le_period` — Σ_i ∫_{I_i} g ≤ ∫₀¹ g for `g ≥ 0` continuous 1-periodic;
  (b4) `gallagher_additive_large_sieve` — assembly with AM–GM at `κ = πN`;
  (b5) `multiplicative_large_sieve_gallagher` — `Sieve.lean`'s Farey/Gauss deduction, verbatim.

Rule 17: CLEAN — `N` and `Q` are independent naturals with no relating hypothesis.
-/
import ZetaQ.Sieve

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ZetaQ
namespace Gallagher

/-! ## (a) The Sobolev / Gallagher pointwise bound on an interval of length `δ` -/

/-- **Gallagher's lemma at scale `δ`** (Montgomery 1978, Lemma 1, rescaled and centred):
for `f` with a continuous derivative `f'`,
`|f x| ≤ δ⁻¹ ∫_{x−δ/2}^{x+δ/2} |f| + ½ ∫_{x−δ/2}^{x+δ/2} |f'|`.

Proof: FTC for `u ↦ (u − (x−δ/2)) f u` on `[x−δ/2, x]` and for `u ↦ (u − (x+δ/2)) f u` on
`[x, x+δ/2]` gives `δ f x = ∫_I f + ∫_{x−δ/2}^x (u − x + δ/2) f′ + ∫_x^{x+δ/2} (u − x − δ/2) f′`;
both weights are at most `δ/2` in modulus. -/
theorem point_bound {f f' : ℝ → ℝ} {x δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    |f x| ≤ δ⁻¹ * (∫ t in (x - δ / 2)..(x + δ / 2), |f t|)
      + (1 / 2) * ∫ t in (x - δ / 2)..(x + δ / 2), |f' t| := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have h0x : x - δ / 2 ≤ x := by linarith
  have hx1 : x ≤ x + δ / 2 := by linarith
  have h01 : x - δ / 2 ≤ x + δ / 2 := by linarith
  have hw0 : Continuous (fun u : ℝ => (u - (x - δ / 2)) * f' u) :=
    (continuous_id.sub continuous_const).mul hf'
  have hw1 : Continuous (fun u : ℝ => (u - (x + δ / 2)) * f' u) :=
    (continuous_id.sub continuous_const).mul hf'
  -- FTC on the two halves
  have hL : (∫ u in (x - δ / 2)..x, (f u + (u - (x - δ / 2)) * f' u)) = (δ / 2) * f x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => (u - (x - δ / 2)) * f u)]
    · show (x - (x - δ / 2)) * f x - ((x - δ / 2) - (x - δ / 2)) * f (x - δ / 2) = δ / 2 * f x
      ring
    · intro u _
      have h : HasDerivAt (fun y => (y - (x - δ / 2)) * f y)
          (1 * f u + (u - (x - δ / 2)) * f' u) u :=
        ((hasDerivAt_id' u).sub_const (x - δ / 2)).mul (hf u)
      show HasDerivAt (fun u => (u - (x - δ / 2)) * f u) (f u + (u - (x - δ / 2)) * f' u) u
      rw [one_mul] at h
      exact h
    · exact (hfc.add hw0).intervalIntegrable _ _
  have hR : (∫ u in x..(x + δ / 2), (f u + (u - (x + δ / 2)) * f' u)) = (δ / 2) * f x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => (u - (x + δ / 2)) * f u)]
    · show (x + δ / 2 - (x + δ / 2)) * f (x + δ / 2) - (x - (x + δ / 2)) * f x = δ / 2 * f x
      ring
    · intro u _
      have h : HasDerivAt (fun y => (y - (x + δ / 2)) * f y)
          (1 * f u + (u - (x + δ / 2)) * f' u) u :=
        ((hasDerivAt_id' u).sub_const (x + δ / 2)).mul (hf u)
      show HasDerivAt (fun u => (u - (x + δ / 2)) * f u) (f u + (u - (x + δ / 2)) * f' u) u
      rw [one_mul] at h
      exact h
    · exact (hfc.add hw1).intervalIntegrable _ _
  have hL' : (∫ u in (x - δ / 2)..x, f u) + (∫ u in (x - δ / 2)..x, (u - (x - δ / 2)) * f' u)
      = (δ / 2) * f x := by
    rw [← intervalIntegral.integral_add (hfc.intervalIntegrable _ _) (hw0.intervalIntegrable _ _)]
    exact hL
  have hR' : (∫ u in x..(x + δ / 2), f u) + (∫ u in x..(x + δ / 2), (u - (x + δ / 2)) * f' u)
      = (δ / 2) * f x := by
    rw [← intervalIntegral.integral_add (hfc.intervalIntegrable _ _) (hw1.intervalIntegrable _ _)]
    exact hR
  have hadj : (∫ u in (x - δ / 2)..x, f u) + (∫ u in x..(x + δ / 2), f u)
      = ∫ u in (x - δ / 2)..(x + δ / 2), f u :=
    intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)
  -- the three bounds
  have hb1 : |∫ u in (x - δ / 2)..(x + δ / 2), f u| ≤ ∫ u in (x - δ / 2)..(x + δ / 2), |f u| :=
    intervalIntegral.abs_integral_le_integral_abs h01
  have hb2 : |∫ u in (x - δ / 2)..x, (u - (x - δ / 2)) * f' u|
      ≤ ∫ u in (x - δ / 2)..x, (δ / 2) * |f' u| := by
    refine (intervalIntegral.abs_integral_le_integral_abs h0x).trans ?_
    refine intervalIntegral.integral_mono_on h0x (hw0.abs.intervalIntegrable _ _)
      ((continuous_const.mul hf'.abs).intervalIntegrable _ _) ?_
    intro u hu
    rw [abs_mul]
    have : |u - (x - δ / 2)| ≤ δ / 2 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hb3 : |∫ u in x..(x + δ / 2), (u - (x + δ / 2)) * f' u|
      ≤ ∫ u in x..(x + δ / 2), (δ / 2) * |f' u| := by
    refine (intervalIntegral.abs_integral_le_integral_abs hx1).trans ?_
    refine intervalIntegral.integral_mono_on hx1 (hw1.abs.intervalIntegrable _ _)
      ((continuous_const.mul hf'.abs).intervalIntegrable _ _) ?_
    intro u hu
    rw [abs_mul]
    have : |u - (x + δ / 2)| ≤ δ / 2 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hsum : (∫ u in (x - δ / 2)..x, (δ / 2) * |f' u|) + (∫ u in x..(x + δ / 2), (δ / 2) * |f' u|)
      = (δ / 2) * ∫ u in (x - δ / 2)..(x + δ / 2), |f' u| := by
    have hcf : Continuous (fun u : ℝ => (δ / 2) * |f' u|) := continuous_const.mul hf'.abs
    rw [intervalIntegral.integral_add_adjacent_intervals (hcf.intervalIntegrable _ _)
      (hcf.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  -- assemble: `δ |f x| ≤ ∫_I |f| + (δ/2) ∫_I |f'|`
  have hmain : |δ * f x| ≤ (∫ u in (x - δ / 2)..(x + δ / 2), |f u|)
      + (δ / 2) * ∫ u in (x - δ / 2)..(x + δ / 2), |f' u| := by
    have e1 := abs_le.1 hb1
    have e2 := abs_le.1 hb2
    have e3 := abs_le.1 hb3
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hδ] at hmain
  have e1 : δ⁻¹ * (δ / 2) = 1 / 2 := by
    rw [← mul_div_assoc, inv_mul_cancel₀ hδ.ne']
  calc |f x| = δ⁻¹ * (δ * |f x|) := by rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
    _ ≤ δ⁻¹ * ((∫ u in (x - δ / 2)..(x + δ / 2), |f u|)
          + (δ / 2) * ∫ u in (x - δ / 2)..(x + δ / 2), |f' u|) :=
        mul_le_mul_of_nonneg_left hmain (inv_nonneg.2 hδ.le)
    _ = δ⁻¹ * (∫ u in (x - δ / 2)..(x + δ / 2), |f u|)
          + (δ⁻¹ * (δ / 2)) * ∫ u in (x - δ / 2)..(x + δ / 2), |f' u| := by ring
    _ = δ⁻¹ * (∫ t in (x - δ / 2)..(x + δ / 2), |f t|)
          + (1 / 2) * ∫ t in (x - δ / 2)..(x + δ / 2), |f' t| := by rw [e1]

/-- `point_bound` with the right side as ONE integral (the form the sieve consumes). -/
theorem point_bound_integral {f f' : ℝ → ℝ} {x δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    |f x| ≤ ∫ t in (x - δ / 2)..(x + δ / 2), (δ⁻¹ * |f t| + (1 / 2) * |f' t|) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  rw [intervalIntegral.integral_add ((hfc.abs.intervalIntegrable _ _).const_mul _)
      ((hf'.abs.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  exact point_bound hδ hf hf'

/-! ## (b1) Trigonometric polynomials with natural frequencies; Parseval on `[0, 1]` -/

/-- `t ↦ e(r t)` is continuous. -/
theorem continuous_e_mul (r : ℝ) : Continuous (fun t : ℝ => e (r * t)) :=
  continuous_e.comp (continuous_const.mul continuous_id)

/-- A trigonometric polynomial `Σ_{n∈s} b_n e(nt)`. `ZetaQ.expSum N a = trig (Ioc 0 N) a`
definitionally (`expSum_eq_trig`). -/
def trig (s : Finset ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ := ∑ n ∈ s, b n * e ((n : ℝ) * t)

theorem expSum_eq_trig (N : ℕ) (a : ℕ → ℂ) : expSum N a = trig (Finset.Ioc 0 N) a := rfl

theorem continuous_trig (s : Finset ℕ) (b : ℕ → ℂ) : Continuous (trig s b) := by
  unfold trig
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_e_mul _)

theorem trig_periodic (s : Finset ℕ) (b : ℕ → ℂ) : Function.Periodic (trig s b) 1 := by
  intro t
  unfold trig
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : e (n : ℝ) = 1 := by
    have := e_intCast (n : ℤ)
    rwa [Int.cast_natCast] at this
  rw [mul_add, mul_one, e_add, h1, mul_one]

/-- **Parseval for a trigonometric polynomial on `[0,1]`**:
`∫₀¹ |Σ_{n∈s} b_n e(nt)|² dt = Σ_{n∈s} |b_n|²`. -/
theorem parseval_trig (s : Finset ℕ) (b : ℕ → ℂ) :
    (∫ t in (0:ℝ)..1, ‖trig s b t‖ ^ 2) = ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have hkey : ∀ k : ℤ, (∫ t in (0:ℝ)..(1:ℝ), e ((k:ℝ) * t)) = if k = 0 then 1 else 0 := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg hk]
      exact intervalIntegral_e_orth (k := k) (Int.cast_ne_zero.mpr hk) (mul_one _)
  have hpt : ∀ t : ℝ, ((‖trig s b t‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ s, ∑ k ∈ s,
          (b m * (starRingEnd ℂ) (b k)) * e ((((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t) := by
    intro t
    rw [Complex.ofReal_pow, (Complex.mul_conj' (trig s b t)).symm]
    simp only [trig, map_sum, map_mul, conj_e]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    rw [show (((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t = (m:ℝ) * t + (-((k:ℝ) * t)) by push_cast; ring,
      e_add]
    ring
  have hcast : ((∫ t in (0:ℝ)..1, ‖trig s b t‖ ^ 2 : ℝ) : ℂ)
      = ((∑ n ∈ s, ‖b n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp only [hpt]
    have hcm : ∀ m : ℕ, Continuous (fun t : ℝ => ∑ k ∈ s,
        (b m * (starRingEnd ℂ) (b k)) * e ((((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t)) := fun m =>
      continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_e_mul _)
    rw [intervalIntegral.integral_finsetSum
      (f := fun (m : ℕ) (t : ℝ) => ∑ k ∈ s,
        (b m * (starRingEnd ℂ) (b k)) * e ((((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t))
      (fun m _ => (hcm m).intervalIntegrable _ _)]
    have hinner : ∀ m ∈ s, (∫ t in (0:ℝ)..1, ∑ k ∈ s,
        (b m * (starRingEnd ℂ) (b k)) * e ((((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t))
          = ((‖b m‖ ^ 2 : ℝ) : ℂ) := by
      intro m hm
      rw [intervalIntegral.integral_finsetSum
        (f := fun (k : ℕ) (t : ℝ) =>
          (b m * (starRingEnd ℂ) (b k)) * e ((((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t))
        (fun k _ => ((continuous_const.mul (continuous_e_mul _)).intervalIntegrable _ _))]
      simp only [intervalIntegral.integral_const_mul, hkey]
      rw [Finset.sum_eq_single_of_mem m hm (fun k _ hkne => by
        have hne : ((m:ℤ) - (k:ℤ)) ≠ 0 := by omega
        simp [hne])]
      rw [sub_self, if_pos rfl, mul_one, Complex.mul_conj', Complex.ofReal_pow]
    rw [Finset.sum_congr rfl hinner, Complex.ofReal_sum]
  exact_mod_cast hcast

/-- `∫₀¹ |S|² = ‖a‖²`. -/
theorem integral_normSq_expSum (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0:ℝ)..1, ‖expSum N a t‖ ^ 2) = l2sq N a :=
  parseval_trig (Finset.Ioc 0 N) a

/-! ## (b2) The derivative of `|S|²` and its centred bound -/

/-- `d/dt e(r t) = e(r t) · 2πi r`. -/
theorem hasDerivAt_e_mul (r t : ℝ) :
    HasDerivAt (fun u : ℝ => e (r * u))
      (e (r * t) * (2 * (Real.pi : ℂ) * Complex.I * (r : ℂ))) t := by
  have h1 : HasDerivAt (fun u : ℝ => ((r * u : ℝ) : ℂ)) (r : ℂ) t := by
    have := ((hasDerivAt_id' t).const_mul r).ofReal_comp
    rwa [mul_one] at this
  have h2 := (h1.const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
  exact h2

/-- `S′(θ) = Σ a_n · 2πi n · e(nθ)` (uncentred). -/
def expSumDeriv (N : ℕ) (a : ℕ → ℂ) : ℝ → ℂ :=
  trig (Finset.Ioc 0 N) (fun n => a n * (2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)))

/-- The centred multiplier `2πi (n − (N+1)/2)`; `|n − (N+1)/2| ≤ (N−1)/2` on `0 < n ≤ N`. -/
def cmult (N n : ℕ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * ((((n : ℝ) - ((N : ℝ) + 1) / 2 : ℝ)) : ℂ)

/-- The centred derivative `D(θ) = Σ a_n · 2πi (n − (N+1)/2) · e(nθ) = S′ − 2πi·(N+1)/2·S`. -/
def expSumD (N : ℕ) (a : ℕ → ℂ) : ℝ → ℂ :=
  trig (Finset.Ioc 0 N) (fun n => a n * cmult N n)

theorem hasDerivAt_expSum (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    HasDerivAt (expSum N a) (expSumDeriv N a θ) θ := by
  have h : HasDerivAt (fun y => ∑ n ∈ Finset.Ioc 0 N, a n * e ((n:ℝ) * y))
      (∑ n ∈ Finset.Ioc 0 N,
        a n * (e ((n:ℝ) * θ) * (2 * (Real.pi : ℂ) * Complex.I * ((n:ℝ) : ℂ)))) θ :=
    HasDerivAt.fun_sum (fun (n : ℕ) _ => (hasDerivAt_e_mul ((n : ℕ) : ℝ) θ).const_mul (a n))
  have hval : expSumDeriv N a θ = ∑ n ∈ Finset.Ioc 0 N,
      a n * (e ((n:ℝ) * θ) * (2 * (Real.pi : ℂ) * Complex.I * ((n:ℝ) : ℂ))) := by
    unfold expSumDeriv trig
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hval]
  exact h

/-- `(|S|²)′ = 2⟪S, S′⟫_ℝ` (Mathlib `HasDerivAt.norm_sq`). -/
theorem hasDerivAt_normSq (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    HasDerivAt (fun t => ‖expSum N a t‖ ^ 2)
      (2 * inner ℝ (expSum N a θ) (expSumDeriv N a θ)) θ :=
  (hasDerivAt_expSum N a θ).norm_sq

/-- **Centring**: `|(|S|²)′| ≤ 2|S||D|` with `D` the centred derivative. Uses
`⟪S, iλS⟫_ℝ = 0` for real `λ`. -/
theorem abs_deriv_normSq_le (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    |2 * inner ℝ (expSum N a θ) (expSumDeriv N a θ)|
      ≤ 2 * (‖expSum N a θ‖ * ‖expSumD N a θ‖) := by
  set c' : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((((N:ℝ) + 1) / 2 : ℝ) : ℂ) with hc'
  have hsplit : expSumDeriv N a θ = expSumD N a θ + c' * expSum N a θ := by
    simp only [expSumDeriv, expSumD, expSum, trig, cmult, hc', Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have hSS : expSum N a θ * (starRingEnd ℂ) (expSum N a θ)
      = ((‖expSum N a θ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj', Complex.ofReal_pow]
  have hz : c' * expSum N a θ * (starRingEnd ℂ) (expSum N a θ)
      = ((2 * Real.pi * (((N:ℝ) + 1) / 2) * ‖expSum N a θ‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [mul_assoc c', hSS, hc']
    push_cast
    ring
  have hre : inner ℝ (expSum N a θ) (expSumDeriv N a θ)
      = (expSumD N a θ * (starRingEnd ℂ) (expSum N a θ)).re := by
    rw [Complex.inner, hsplit, add_mul, Complex.add_re, hz, Complex.mul_I_re,
      Complex.ofReal_im, neg_zero, add_zero]
  rw [abs_mul, abs_two, hre]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |(expSumD N a θ * (starRingEnd ℂ) (expSum N a θ)).re|
      ≤ ‖expSumD N a θ * (starRingEnd ℂ) (expSum N a θ)‖ := Complex.abs_re_le_norm _
    _ = ‖expSum N a θ‖ * ‖expSumD N a θ‖ := by
        rw [norm_mul, Complex.norm_conj, mul_comm]

/-- `|2πi (n − (N+1)/2)| ≤ π (N − 1)` for `0 < n ≤ N`. -/
theorem norm_cmult_le (N : ℕ) {n : ℕ} (hn : n ∈ Finset.Ioc 0 N) :
    ‖cmult N n‖ ≤ Real.pi * ((N:ℝ) - 1) := by
  rw [Finset.mem_Ioc] at hn
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn.1
  have h2 : (n:ℝ) ≤ N := by exact_mod_cast hn.2
  have habs : |(n:ℝ) - ((N:ℝ) + 1) / 2| ≤ ((N:ℝ) - 1) / 2 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have hnorm : ‖cmult N n‖ = 2 * Real.pi * |(n:ℝ) - ((N:ℝ) + 1) / 2| := by
    simp only [cmult, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, mul_one, Complex.norm_ofNat]
  rw [hnorm]
  have := mul_le_mul_of_nonneg_left habs (by positivity : (0:ℝ) ≤ 2 * Real.pi)
  linarith

/-- `∫₀¹ |D|² = Σ |2π(n − (N+1)/2)|²|a_n|² ≤ π²(N − 1)² ‖a‖²`. -/
theorem integral_normSq_expSumD_le (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0:ℝ)..1, ‖expSumD N a t‖ ^ 2) ≤ (Real.pi * ((N:ℝ) - 1)) ^ 2 * l2sq N a := by
  show (∫ t in (0:ℝ)..1, ‖trig (Finset.Ioc 0 N) (fun n => a n * cmult N n) t‖ ^ 2) ≤ _
  rw [parseval_trig, l2sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [norm_mul, mul_pow]
  have hc2 : ‖cmult N n‖ ^ 2 ≤ (Real.pi * ((N:ℝ) - 1)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_cmult_le N hn) 2
  have := mul_le_mul_of_nonneg_left hc2 (sq_nonneg ‖a n‖)
  linarith

/-! ## (b3) Summing over `δ`-separated points: the intervals tile at most one period -/

/-- **The `δ`-intervals around `δ`-separated points mod 1 fit inside one period.**
For `g ≥ 0` continuous and `1`-periodic, `Σ_i ∫_{θ_i−δ/2}^{θ_i+δ/2} g ≤ ∫₀¹ g`.

Proof: fix `i₀`; move every `θ_i` by the integer `⌊θ_i − θ_{i₀}⌋` into `[θ_{i₀}, θ_{i₀} + 1)`
(periodicity); the separation hypothesis (R10 encoding, verbatim from
`SharpAdditiveLargeSieve`) makes the moved points pairwise `δ`-apart in `ℝ` and puts them in
`[θ_{i₀}, θ_{i₀} + 1 − δ]` for `i ≠ i₀`, so the half-open intervals are pairwise disjoint and lie
in `(θ_{i₀} − δ/2, θ_{i₀} − δ/2 + 1]`. -/
theorem sum_integral_le_period {ι : Type*} [Fintype ι] {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgc : Continuous g) (hper : Function.Periodic g 1)
    (θ : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) :
    ∑ i, (∫ t in (θ i - δ / 2)..(θ i + δ / 2), g t) ≤ ∫ t in (0:ℝ)..1, g t := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact intervalIntegral.integral_nonneg zero_le_one (fun t _ => hg0 t)
  obtain ⟨i₀⟩ := hι
  obtain ⟨k, hk⟩ : ∃ k : ι → ℤ, ∀ i, k i = ⌊θ i - θ i₀⌋ := ⟨_, fun _ => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ι → ℝ, ∀ i, φ i = θ i - (k i : ℝ) := ⟨_, fun _ => rfl⟩
  have hlo : ∀ i, θ i₀ ≤ φ i := by
    intro i
    have := Int.floor_le (θ i - θ i₀)
    rw [hφ, hk]
    linarith
  have hhi : ∀ i, φ i + δ ≤ θ i₀ + 1 := by
    intro i
    by_cases hi : i = i₀
    · rw [hi, hφ, hk, sub_self, Int.floor_zero, Int.cast_zero, sub_zero]
      linarith
    · have h1 := hsep i i₀ hi (k i + 1)
      have h2 := Int.lt_floor_add_one (θ i - θ i₀)
      rw [← hk] at h2
      push_cast at h1
      rw [abs_of_neg (by linarith)] at h1
      rw [hφ]
      linarith
  have hsepφ : ∀ i j, i ≠ j → δ ≤ |φ i - φ j| := by
    intro i j hij
    have e : φ i - φ j = θ i - θ j - ((k i - k j : ℤ) : ℝ) := by
      rw [hφ, hφ]; push_cast; ring
    rw [e]
    exact hsep i j hij (k i - k j)
  have hshift : ∀ i, (∫ t in (θ i - δ / 2)..(θ i + δ / 2), g t)
      = ∫ t in (φ i - δ / 2)..(φ i + δ / 2), g t := by
    intro i
    have hg : ∀ y, g (y + (k i : ℝ)) = g y := fun y => by
      have := hper.int_mul (k i) y
      rwa [mul_one] at this
    have h := intervalIntegral.integral_comp_add_right g (k i : ℝ)
      (a := φ i - δ / 2) (b := φ i + δ / 2)
    simp only [hg] at h
    have e1 : φ i - δ / 2 + (k i : ℝ) = θ i - δ / 2 := by rw [hφ]; ring
    have e2 : φ i + δ / 2 + (k i : ℝ) = θ i + δ / 2 := by rw [hφ]; ring
    rw [h, e1, e2]
  have hint : ∀ a b : ℝ, a ≤ b → IntegrableOn g (Set.Ioc a b) volume := fun a b hab =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hgc.intervalIntegrable a b)
  have hsum : ∑ i, (∫ t in (θ i - δ / 2)..(θ i + δ / 2), g t)
      = ∫ t in ⋃ i, Set.Ioc (φ i - δ / 2) (φ i + δ / 2), g t := by
    rw [integral_iUnion_fintype (fun i => measurableSet_Ioc) ?_
      (fun i => hint _ _ (by linarith))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hshift i, intervalIntegral.integral_of_le (by linarith)]
    · intro i j hij
      simp only [Function.onFun]
      refine Set.disjoint_left.2 fun t ht1 ht2 => ?_
      rw [Set.mem_Ioc] at ht1 ht2
      have h := hsepφ i j hij
      rcases le_or_gt 0 (φ i - φ j) with h0 | h0
      · rw [abs_of_nonneg h0] at h
        linarith [ht1.1, ht1.2, ht2.1, ht2.2]
      · rw [abs_of_neg h0] at h
        linarith [ht1.1, ht1.2, ht2.1, ht2.2]
  have hsub : (⋃ i, Set.Ioc (φ i - δ / 2) (φ i + δ / 2))
      ⊆ Set.Ioc (θ i₀ - δ / 2) (θ i₀ - δ / 2 + 1) := by
    intro t ht
    rw [Set.mem_iUnion] at ht
    obtain ⟨i, hi⟩ := ht
    rw [Set.mem_Ioc] at hi
    have := hlo i
    have := hhi i
    exact Set.mem_Ioc.2 ⟨by linarith, by linarith⟩
  rw [hsum]
  calc (∫ t in ⋃ i, Set.Ioc (φ i - δ / 2) (φ i + δ / 2), g t)
      ≤ ∫ t in Set.Ioc (θ i₀ - δ / 2) (θ i₀ - δ / 2 + 1), g t :=
        setIntegral_mono_set (hint _ _ (by linarith)) (ae_of_all _ fun t => hg0 t)
          (Filter.Eventually.of_forall fun t ht => hsub ht)
    _ = ∫ t in (θ i₀ - δ / 2)..(θ i₀ - δ / 2 + 1), g t :=
        (intervalIntegral.integral_of_le (by linarith)).symm
    _ = ∫ t in (0:ℝ)..(0 + 1), g t := hper.intervalIntegral_add_eq _ _
    _ = ∫ t in (0:ℝ)..1, g t := by rw [zero_add]

/-! ## (b4) Gallagher's additive large sieve -/

/-- `2uv ≤ κu² + κ⁻¹v²` for `κ > 0`. -/
theorem two_mul_le_kappa {κ : ℝ} (hκ : 0 < κ) (u v : ℝ) :
    2 * (u * v) ≤ κ * u ^ 2 + κ⁻¹ * v ^ 2 := by
  have hk : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ.ne'
  have h : κ⁻¹ * (κ * u - v) ^ 2 = κ * u ^ 2 + κ⁻¹ * v ^ 2 - 2 * (u * v) := by
    have e : κ⁻¹ * (κ * u - v) ^ 2
        = (κ⁻¹ * κ) * (κ * u ^ 2) - 2 * (κ⁻¹ * κ) * (u * v) + κ⁻¹ * v ^ 2 := by ring
    rw [e, hk]; ring
  have := mul_nonneg (inv_nonneg.2 hκ.le) (sq_nonneg (κ * u - v))
  linarith

/-- The majorant integrated over each `δ`-interval:
`g(t) = δ⁻¹|S(t)|² + ½(κ|S(t)|² + κ⁻¹|D(t)|²)`. -/
def gMaj (N : ℕ) (a : ℕ → ℂ) (δ κ : ℝ) (t : ℝ) : ℝ :=
  δ⁻¹ * ‖expSum N a t‖ ^ 2 + (1 / 2) * (κ * ‖expSum N a t‖ ^ 2 + κ⁻¹ * ‖expSumD N a t‖ ^ 2)

theorem continuous_gMaj (N : ℕ) (a : ℕ → ℂ) (δ κ : ℝ) : Continuous (gMaj N a δ κ) := by
  have hS : Continuous (expSum N a) := continuous_trig _ _
  have hD : Continuous (expSumD N a) := continuous_trig _ _
  unfold gMaj
  exact (continuous_const.mul (hS.norm.pow 2)).add (continuous_const.mul
    ((continuous_const.mul (hS.norm.pow 2)).add (continuous_const.mul (hD.norm.pow 2))))

theorem gMaj_nonneg (N : ℕ) (a : ℕ → ℂ) {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (t : ℝ) :
    0 ≤ gMaj N a δ κ t := by
  unfold gMaj
  have := inv_pos.2 hδ
  have := inv_pos.2 hκ
  positivity

theorem gMaj_periodic (N : ℕ) (a : ℕ → ℂ) (δ κ : ℝ) : Function.Periodic (gMaj N a δ κ) 1 := by
  intro t
  unfold gMaj
  rw [show expSum N a (t + 1) = expSum N a t from trig_periodic _ _ t,
    show expSumD N a (t + 1) = expSumD N a t from trig_periodic _ _ t]

theorem integral_gMaj (N : ℕ) (a : ℕ → ℂ) (δ κ : ℝ) :
    (∫ t in (0:ℝ)..1, gMaj N a δ κ t)
      = δ⁻¹ * l2sq N a + (1 / 2) * (κ * l2sq N a + κ⁻¹ * ∫ t in (0:ℝ)..1, ‖expSumD N a t‖ ^ 2) := by
  have hS : Continuous (expSum N a) := continuous_trig _ _
  have hD : Continuous (expSumD N a) := continuous_trig _ _
  have iS : IntervalIntegrable (fun t => ‖expSum N a t‖ ^ 2) volume 0 1 :=
    (hS.norm.pow 2).intervalIntegrable _ _
  have iD : IntervalIntegrable (fun t => ‖expSumD N a t‖ ^ 2) volume 0 1 :=
    (hD.norm.pow 2).intervalIntegrable _ _
  unfold gMaj
  rw [intervalIntegral.integral_add (iS.const_mul _) (((iS.const_mul _).add
      (iD.const_mul _)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (iS.const_mul _) (iD.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_normSq_expSum]

/-- **Gallagher's additive large sieve, as a `Prop`**, in the exact binder shape of
`ZetaQ.SharpAdditiveLargeSieve` (Sieve.lean:312) with `N − 1 + δ⁻¹` replaced by `δ⁻¹ + πN`. -/
def GallagherAdditiveLargeSieve : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ℕ) (a : ℕ → ℂ) (θ : ι → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 →
    (∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) →
    ∑ i, ‖expSum N a (θ i)‖ ^ 2 ≤ (δ⁻¹ + Real.pi * N) * l2sq N a

/-- **Gallagher 1967 / Montgomery 1978 Thm 1** — PROVED, sorry-free. -/
theorem gallagher_additive_large_sieve : GallagherAdditiveLargeSieve := by
  intro ι _ N a θ δ hδ hδ1 hsep
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [expSum, l2sq]
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hκ : 0 < Real.pi * N := by positivity
  have hL0 : 0 ≤ l2sq N a := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hS'c : Continuous (expSumDeriv N a) := continuous_trig _ _
  have hSc : Continuous (expSum N a) := continuous_trig _ _
  -- pointwise: `|S(θ_i)|² ≤ ∫_{I_i} g`
  have hpt : ∀ i, ‖expSum N a (θ i)‖ ^ 2
      ≤ ∫ t in (θ i - δ / 2)..(θ i + δ / 2), gMaj N a δ (Real.pi * N) t := by
    intro i
    have hpb := point_bound_integral (f := fun t => ‖expSum N a t‖ ^ 2)
      (f' := fun t => 2 * inner ℝ (expSum N a t) (expSumDeriv N a t)) (x := θ i) hδ
      (fun t => hasDerivAt_normSq N a t) (continuous_const.mul (hSc.inner hS'c))
    rw [abs_of_nonneg (sq_nonneg _)] at hpb
    refine hpb.trans ?_
    refine intervalIntegral.integral_mono_on (by linarith)
      (((hSc.norm.pow 2).abs.intervalIntegrable _ _).const_mul _ |>.add
        (((continuous_const.mul (hSc.inner hS'c)).abs.intervalIntegrable _ _).const_mul _))
      ((continuous_gMaj N a δ _).intervalIntegrable _ _) ?_
    intro t _
    unfold gMaj
    rw [abs_of_nonneg (sq_nonneg ‖expSum N a t‖)]
    have h1 := abs_deriv_normSq_le N a t
    have h2 := two_mul_le_kappa hκ ‖expSum N a t‖ ‖expSumD N a t‖
    linarith
  have hD := integral_normSq_expSumD_le N a
  have hkey : (Real.pi * N)⁻¹ * (∫ t in (0:ℝ)..1, ‖expSumD N a t‖ ^ 2)
      ≤ (Real.pi * N) * l2sq N a := by
    rw [inv_mul_le_iff₀ hκ]
    have hp : (Real.pi * ((N:ℝ) - 1)) ^ 2 ≤ (Real.pi * N) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) 2
    have := mul_le_mul_of_nonneg_right hp hL0
    nlinarith
  calc ∑ i, ‖expSum N a (θ i)‖ ^ 2
      ≤ ∑ i, ∫ t in (θ i - δ / 2)..(θ i + δ / 2), gMaj N a δ (Real.pi * N) t :=
        Finset.sum_le_sum fun i _ => hpt i
    _ ≤ ∫ t in (0:ℝ)..1, gMaj N a δ (Real.pi * N) t :=
        sum_integral_le_period (gMaj_nonneg N a hδ hκ) (continuous_gMaj N a δ _)
          (gMaj_periodic N a δ _) θ hδ hδ1 hsep
    _ = δ⁻¹ * l2sq N a + (1 / 2) * ((Real.pi * N) * l2sq N a
          + (Real.pi * N)⁻¹ * ∫ t in (0:ℝ)..1, ‖expSumD N a t‖ ^ 2) := integral_gMaj N a δ _
    _ ≤ (δ⁻¹ + Real.pi * N) * l2sq N a := by nlinarith

/-- Reindexing `Σ_{M<n≤M+N} f n = Σ_{0<m≤N} f (M+m)`. -/
theorem sum_Ioc_shift {β : Type*} [AddCommMonoid β] (M N : ℕ) (f : ℕ → β) :
    ∑ n ∈ Finset.Ioc M (M + N), f n = ∑ m ∈ Finset.Ioc 0 N, f (M + m) := by
  have h := Finset.map_add_left_Ioc 0 N M
  rw [add_zero] at h
  rw [← h, Finset.sum_map]
  rfl

/-- **Gallagher's inequality on a shifted range `M < n ≤ M + N`** (Montgomery 1978, Thm 1 as
stated there): the length term is `πN`, independent of `M`. Corollary of the `Ioc 0 N` form:
`e((M+m)θ) = e(Mθ)e(mθ)` and `|e(Mθ)| = 1`. -/
theorem gallagher_shifted {ι : Type} [Fintype ι] (M N : ℕ) (a : ℕ → ℂ) (θ : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsep : ∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) :
    ∑ i, ‖∑ n ∈ Finset.Ioc M (M + N), a n * e ((n : ℝ) * θ i)‖ ^ 2
      ≤ (δ⁻¹ + Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hmain := gallagher_additive_large_sieve ι N (fun m => a (M + m)) θ δ hδ hδ1 hsep
  have hL : ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 = l2sq N (fun m => a (M + m)) := by
    rw [sum_Ioc_shift]; rfl
  have hpt : ∀ i, ‖∑ n ∈ Finset.Ioc M (M + N), a n * e ((n : ℝ) * θ i)‖
      = ‖expSum N (fun m => a (M + m)) (θ i)‖ := by
    intro i
    have hfac : ∑ n ∈ Finset.Ioc M (M + N), a n * e ((n : ℝ) * θ i)
        = e ((M : ℝ) * θ i) * expSum N (fun m => a (M + m)) (θ i) := by
      rw [sum_Ioc_shift, expSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      try beta_reduce
      rw [show (((M + m : ℕ) : ℝ) * θ i) = (M : ℝ) * θ i + (m : ℝ) * θ i by push_cast; ring,
        e_add]
      ring
    rw [hfac, norm_mul, norm_e, one_mul]
  simp only [hpt, hL]
  exact hmain

/-! ## (b5) The multiplicative large sieve at the Gallagher budget `Q² + πN`

A verbatim copy of `ZetaQ.multiplicative_large_sieve_of_additive_of_le_one`
(Sieve.lean:2923) with `hadd := gallagher_additive_large_sieve`; only the last `calc` line
changes. The `Q²` term (the family constant) is untouched; `N − 1` becomes `πN`. -/

/-- `Q² + πN` — the Gallagher budget. Compare `ZetaQ.sieveBudget N Q = N + Q² − 1`. -/
def gallagherBudget (N Q : ℕ) : ℝ := (Q : ℝ) ^ 2 + Real.pi * N

/-- **Lemma 6.1 at the Gallagher budget — sorry-free.**
`Σ_{q≤Q} Σ*_χ |Σ_{n≤N} a_n χ(n)|² ≤ (Q² + πN) Σ_{n≤N} |a_n|²`. -/
theorem multiplicative_large_sieve_gallagher (Q N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
      ≤ gallagherBudget N Q * l2sq N a := by
  classical
  have hl2 : (0:ℝ) ≤ l2sq N a := Finset.sum_nonneg fun _ _ => by positivity
  rcases Nat.eq_zero_or_pos Q with rfl | hQ1
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    refine mul_nonneg ?_ hl2
    simp only [gallagherBudget]
    positivity
  · have hQR : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ1
    set T : Finset ((_ : ℕ) × ℕ) := (Finset.Icc 1 Q).sigma reducedResidues with hT
    have hδ : (0:ℝ) < ((Q:ℝ) ^ 2)⁻¹ := by positivity
    have hsep : ∀ i j : {x // x ∈ T}, i ≠ j → ∀ m : ℤ,
        ((Q:ℝ) ^ 2)⁻¹
          ≤ |((i.1.2 : ℝ) / (i.1.1 : ℝ)) - ((j.1.2 : ℝ) / (j.1.1 : ℝ)) - (m : ℝ)| := by
      rintro ⟨⟨q, b⟩, hi⟩ ⟨⟨q', b'⟩, hj⟩ hij m
      have hi' := hi
      have hj' := hj
      rw [hT, Finset.mem_sigma, Finset.mem_Icc, mem_reducedResidues] at hi' hj'
      refine farey_spaced Q hi'.1.1 hj'.1.1 hi'.1.2 hj'.1.2 hi'.2.2 hj'.2.2 ?_ m
      rw [Nat.mod_eq_of_lt hi'.2.1, Nat.mod_eq_of_lt hj'.2.1]
      intro hcontra
      simp only [Prod.mk.injEq] at hcontra
      obtain ⟨rfl, rfl⟩ := hcontra
      exact hij rfl
    have hδ1 : ((Q:ℝ) ^ 2)⁻¹ ≤ 1 := by
      have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ1
      rw [inv_le_one_iff₀]
      right; nlinarith
    have hmain := gallagher_additive_large_sieve {x // x ∈ T} N a
      (fun x => (x.1.2 : ℝ) / (x.1.1 : ℝ)) (((Q:ℝ) ^ 2)⁻¹) hδ hδ1 hsep
    rw [inv_inv] at hmain
    have hsumeq : ∑ i : {x // x ∈ T}, ‖expSum N a ((i.1.2 : ℝ) / (i.1.1 : ℝ))‖ ^ 2
        = ∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ reducedResidues q,
            ‖expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
      rw [Finset.sum_coe_sort T (fun x => ‖expSum N a ((x.2 : ℝ) / (x.1 : ℝ))‖ ^ 2), hT]
      exact Finset.sum_sigma _ _ _
    calc ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
        ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ reducedResidues q,
            ‖expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [Finset.mem_Icc] at hq
          refine (primitive_decomposition q N hq.1 a).trans ?_
          -- the declined weight: `φ(q)/q ≤ 1` is dropped here, exactly as in Sieve.lean
          have h1 : (Nat.totient q : ℝ) / (q : ℝ) ≤ 1 := by
            rw [div_le_one (by exact_mod_cast hq.1)]
            exact_mod_cast Nat.totient_le q
          have h2 : (0:ℝ) ≤ ∑ b ∈ reducedResidues q, ‖expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 :=
            Finset.sum_nonneg fun _ _ => by positivity
          nlinarith
      _ = ∑ i : {x // x ∈ T}, ‖expSum N a ((i.1.2 : ℝ) / (i.1.1 : ℝ))‖ ^ 2 := hsumeq.symm
      _ ≤ ((Q : ℝ) ^ 2 + Real.pi * N) * l2sq N a := hmain
      _ = gallagherBudget N Q * l2sq N a := by rw [gallagherBudget]

/-- **Subfamily form** (the shape the five consumption sites apply), as
`ZetaQ.multiplicative_large_sieve_subfamily` (Sieve.lean:3167) at the Gallagher budget. -/
theorem multiplicative_large_sieve_gallagher_subfamily (Q N : ℕ) (a : ℕ → ℂ)
    (F : Finset ((q : ℕ) × DirichletCharacter ℂ q)) (hF : F ⊆ familyQ Q) :
    ∑ x ∈ F, ‖charSum x.1 N a x.2‖ ^ 2 ≤ gallagherBudget N Q * l2sq N a := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hF (fun _ _ _ => by positivity)) ?_
  rw [sum_familyQ]
  exact multiplicative_large_sieve_gallagher Q N a

/-- **Family (indexed) form**, as `ZetaQ.multiplicative_large_sieve_family` (Sieve.lean:3101)
at the Gallagher budget — the shape of `Ends.LargeSieveHyp`. -/
theorem multiplicative_large_sieve_gallagher_family
    {ι : Type*} [Fintype ι] (Q N : ℕ) (a : ℕ → ℂ)
    (mod : ι → ℕ) (chi : ∀ i, DirichletCharacter ℂ (mod i))
    (hpos : ∀ i, 0 < mod i) (hle : ∀ i, mod i ≤ Q)
    (hprim : ∀ i, (chi i).IsPrimitive)
    (hinj : Function.Injective
      (fun i => (⟨mod i, chi i⟩ : (q : ℕ) × DirichletCharacter ℂ q))) :
    ∑ i, ‖charSum (mod i) N a (chi i)‖ ^ 2 ≤ gallagherBudget N Q * l2sq N a := by
  classical
  have himg : (Finset.univ.image
      (fun i => (⟨mod i, chi i⟩ : (q : ℕ) × DirichletCharacter ℂ q))) ⊆ familyQ Q := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    simp only [familyQ, Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨hpos i, hle i⟩, mem_primitiveChars.mpr (hprim i)⟩
  have hre : ∑ x ∈ Finset.univ.image
        (fun i => (⟨mod i, chi i⟩ : (q : ℕ) × DirichletCharacter ℂ q)),
        ‖charSum x.1 N a x.2‖ ^ 2
      = ∑ i, ‖charSum (mod i) N a (chi i)‖ ^ 2 :=
    Finset.sum_image (fun i _ j _ h => hinj h)
  rw [← hre]
  exact multiplicative_large_sieve_gallagher_subfamily Q N a _ himg

/-- The two budget facts every consumer uses (U4 §1.3): `Q² ≤ B` ... -/
theorem sq_le_gallagherBudget (N Q : ℕ) : (Q : ℝ) ^ 2 ≤ gallagherBudget N Q := by
  unfold gallagherBudget
  have : (0:ℝ) ≤ Real.pi * N := by positivity
  linarith

/-- ... and `B ≤ Q²(1 + πε)` whenever `N ≤ ε Q²`. -/
theorem gallagherBudget_le_of_le {N Q : ℕ} {ε : ℝ} (hN : (N : ℝ) ≤ ε * (Q : ℝ) ^ 2) :
    gallagherBudget N Q ≤ (Q : ℝ) ^ 2 * (1 + Real.pi * ε) := by
  unfold gallagherBudget
  have := mul_le_mul_of_nonneg_left hN Real.pi_pos.le
  nlinarith

/-- Relation to the sharp budget: `B_G − B_sharp = (π − 1)N + 1 ≥ 0`. -/
theorem sieveBudget_le_gallagherBudget (N Q : ℕ) : sieveBudget N Q ≤ gallagherBudget N Q := by
  unfold sieveBudget gallagherBudget
  have h3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

end Gallagher
end ZetaQ
