/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/MuqUniform.lean — q-UNIFORM versions of the μ_χ analytic lemmas of
Zeta23/ThmE/PrimeSideChi.lean (`muq_abs_le` :50, `muq_linear_bound` :240,
`muq_increment_bound` :303, `muq_nonneg_eventually` :354), with EXPLICIT ABSOLUTE constants.

Inputs (all proved, all in Zeta23/ThmE/GammaFactsChiProof.lean, namespace Zeta23.ThmE.GammaChi):
  muq_eq                : μ_χ(τ) = (1/2π) Re ψ(a + iτ/2) + (1/2π) log(q/π),  a = 1/4 + κ/2
  muq_even, muq_monotoneOn, muq_zero_le, neg_one_lt_muq_zero, muq_smooth
  muq_stirling_const    : |μ_χ(τ) − (1/2π) log(q|τ|/2π)| ≤ (20/2π)/τ²   (|τ| ≥ 1)   — q-FREE
  muq_deriv_bound_const : |μ_χ'(τ)| ≤ (24/π)/|τ|                         (|τ| ≥ 1)   — q-FREE

Key observations (no compactness argument anywhere):
  * on [-1,1]:  −1 < μ_χ(0) ≤ μ_χ(τ) ≤ μ_χ(1) ≤ (log q)/2π + 10/π   (even + monotone + Stirling at τ=1)
  * increments are q-FREE:  μ_χ,q(τ₁) − μ_χ,q(τ₂) = μ_χ,1(τ₁) − μ_χ,1(τ₂)   (the log q cancels)

Receipt: `audit/MuqUniform_REPORT.md`.  Imports `Zeta23.ThmE.*` only, so it is independent of the rest of
`ZetaQ`; consumed by `ZetaQ/Budget.lean`'s `TraceRow` section (row 1 of `trace_row`).
All declarations are `[propext, Classical.choice, Quot.sound]`.
-/
import Zeta23.ThmE.GammaFactsChiProof
import Zeta23.ThmE.PrimeSideChi

open Real

noncomputable section

namespace ZetaQ
namespace MuqUniform

open Zeta23.ThmE Zeta23.ThmE.GammaChi

/-! ## 0. The q-free difference identity -/

/-- The log q term of `muq` cancels in differences: increments of `μ_χ` do not depend on `q`. -/
theorem muq_sub_eq (κ q : ℕ) (τ₁ τ₂ : ℝ) :
    muq κ q τ₁ - muq κ q τ₂ = muq κ 1 τ₁ - muq κ 1 τ₂ := by
  simp only [muq_eq]; ring

/-- `l T ≥ 1` for `T ≥ 2πe`. -/
theorem one_le_l_of_ge {T : ℝ} (hT : 2 * π * Real.exp 1 ≤ T) : 1 ≤ Zeta23.l T := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  rw [Zeta23.l, ← Real.log_exp 1]
  apply Real.log_le_log (Real.exp_pos 1)
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem twenty_div_two_pi : (20:ℝ) / (2 * π) = 10 / π := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  rw [div_eq_div_iff (by positivity) (by positivity)]; ring

/-! ## 1. `|μ_χ|` on `[-1,1]` — the q-uniform replacement of the compactness step -/

/-- On `|τ| ≤ 1`: `|μ_χ(τ)| ≤ (log q)/2π + 10/π`.  No compactness: evenness + monotonicity pin
`μ_χ(τ)` between `μ_χ(0) > −1` and `μ_χ(1)`, and Stirling at `τ = 1` bounds `μ_χ(1)`. -/
theorem muq_abs_le_of_abs_le_one {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) (τ : ℝ) (hτ : |τ| ≤ 1) :
    |muq κ q τ| ≤ Real.log q / (2 * π) + 10 / π := by
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_le_four
  have hπ0 := Real.pi_pos
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  -- lower bound: μ_χ(τ) ≥ μ_χ(0) > −1
  have hlow : -1 < muq κ q τ := lt_of_lt_of_le (neg_one_lt_muq_zero hκ hq) (muq_zero_le hκ τ)
  -- upper bound: μ_χ(τ) ≤ μ_χ(1)
  have hup1 : muq κ q τ ≤ muq κ q 1 := by
    rcases le_or_gt 0 τ with h0 | h0
    · exact muq_monotoneOn hκ (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr zero_le_one)
        (by linarith [le_abs_self τ])
    · rw [← muq_even hκ τ]
      exact muq_monotoneOn hκ (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr zero_le_one)
        (by linarith [neg_abs_le τ])
  -- Stirling at τ = 1: μ_χ(1) ≤ (1/2π) log(q/2π) + 10/π ≤ (log q)/2π + 10/π
  have hst := muq_stirling_const hκ hq 1 (by simp)
  have hup2 : muq κ q 1 ≤ Real.log q / (2 * π) + 10 / π := by
    simp only [abs_one, mul_one, one_pow, div_one] at hst
    have hl : Real.log ((q:ℝ) / (2 * π)) = Real.log q - Real.log (2 * π) :=
      Real.log_div (by positivity) (by positivity)
    have hl2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith)
    rw [twenty_div_two_pi, hl] at hst
    have h2 := (abs_le.mp hst).2
    have e : 1 / (2 * π) * (Real.log q - Real.log (2 * π))
        = Real.log q / (2 * π) - Real.log (2 * π) / (2 * π) := by ring
    have hnn : 0 ≤ Real.log (2 * π) / (2 * π) := div_nonneg hl2π (by positivity)
    linarith
  have h10 : (1:ℝ) ≤ 10 / π := by rw [le_div_iff₀ hπ0]; linarith
  have hlq' : 0 ≤ Real.log q / (2 * π) := div_nonneg hlq (by positivity)
  rw [abs_le]; constructor <;> linarith

/-- On `|τ| ≥ 1`: `|μ_χ(τ)| ≤ (log q + log|τ|)/2π + (10/π + 1)`.  (Stirling; the `+1` absorbs
`log(2π)/2π`.) -/
theorem muq_abs_le_of_one_le {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) (τ : ℝ) (hτ : 1 ≤ |τ|) :
    |muq κ q τ| ≤ (Real.log q + Real.log |τ|) / (2 * π) + (10 / π + 1) := by
  have hπ3 := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlτ : 0 ≤ Real.log |τ| := Real.log_nonneg hτ
  have hτ0 : 0 < |τ| := by linarith
  have hst := muq_stirling_const hκ hq τ hτ
  -- Stirling error ≤ 10/π since τ² ≥ 1
  have hE : |muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| ≤ 10 / π := by
    refine hst.trans ?_
    rw [twenty_div_two_pi]
    exact div_le_self (by positivity) (by nlinarith [sq_abs τ])
  -- the log: −2π ≤ −log(2π) ≤ L ≤ log q + log|τ|
  have hL : Real.log ((q:ℝ) * |τ| / (2 * π)) = Real.log q + Real.log |τ| - Real.log (2 * π) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hl2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith)
  have hl2π' : Real.log (2 * π) ≤ 2 * π := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π)]
  have habsL : |Real.log ((q:ℝ) * |τ| / (2 * π))| ≤ Real.log q + Real.log |τ| + 2 * π := by
    rw [hL, abs_le]; constructor <;> linarith
  have h2 : |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))|
      ≤ (Real.log q + Real.log |τ|) / (2 * π) + 1 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
    have hone : 1 / (2 * π) * (2 * π) = 1 := by field_simp
    calc 1 / (2 * π) * |Real.log ((q:ℝ) * |τ| / (2 * π))|
        ≤ 1 / (2 * π) * (Real.log q + Real.log |τ| + 2 * π) := by gcongr
      _ = (Real.log q + Real.log |τ|) / (2 * π) + 1 := by linear_combination hone
  calc |muq κ q τ|
      = |(muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
          + 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| := by ring_nf
    _ ≤ |muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))|
          + |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| := abs_add_le _ _
    _ ≤ 10 / π + ((Real.log q + Real.log |τ|) / (2 * π) + 1) := add_le_add hE h2
    _ = (Real.log q + Real.log |τ|) / (2 * π) + (10 / π + 1) := by ring

/-- **Global q-uniform bound**: for every `τ`,
`|μ_χ(τ)| ≤ (log q + log(|τ|+1))/2π + (10/π + 1)`. -/
theorem muq_abs_le_global {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) (τ : ℝ) :
    |muq κ q τ| ≤ (Real.log q + Real.log (|τ| + 1)) / (2 * π) + (10 / π + 1) := by
  have hπ0 := Real.pi_pos
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  rcases le_or_gt 1 |τ| with h1 | h1
  · have h := muq_abs_le_of_one_le hκ hq τ h1
    have hlog : Real.log |τ| ≤ Real.log (|τ| + 1) := Real.log_le_log (by linarith) (by linarith)
    have : (Real.log q + Real.log |τ|) / (2 * π)
        ≤ (Real.log q + Real.log (|τ| + 1)) / (2 * π) := by gcongr
    linarith
  · have h := muq_abs_le_of_abs_le_one hκ hq τ h1.le
    have hlog : 0 ≤ Real.log (|τ| + 1) := Real.log_nonneg (by linarith [abs_nonneg τ])
    have : Real.log q / (2 * π) ≤ (Real.log q + Real.log (|τ| + 1)) / (2 * π) := by
      gcongr; linarith
    linarith

/-! ## 2. `muq_linear_bound`, q-uniform (replaces PrimeSideChi.lean:240) -/

/-- **q-uniform `muq_linear_bound`** (pointwise, explicit): `|μ_χ(τ)| ≤ (log q)/2π + (10/π + 1) + |τ|`. -/
theorem muq_linear_bound_uniform {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) (τ : ℝ) :
    |muq κ q τ| ≤ Real.log q / (2 * π) + (10 / π + 1) + |τ| := by
  have h := muq_abs_le_global hκ hq τ
  have hπ := Real.pi_gt_three
  have hlog : Real.log (|τ| + 1) ≤ |τ| := by
    linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg τ] : (0:ℝ) < |τ| + 1)]
  have h2 : (Real.log q + Real.log (|τ| + 1)) / (2 * π) ≤ Real.log q / (2 * π) + |τ| := by
    rw [add_div]
    have : Real.log (|τ| + 1) / (2 * π) ≤ |τ| := by
      calc Real.log (|τ| + 1) / (2 * π) ≤ |τ| / (2 * π) := by gcongr
        _ ≤ |τ| := div_le_self (abs_nonneg τ) (by linarith)
    linarith
  linarith

/-- **q-uniform `muq_linear_bound`, existential shape** (mirror of `PrimeSideChi.lean:240`):
`M = (log q)/2π + M₀` with `M₀ = 10/π + 1` absolute. -/
theorem muq_linear_bound_uniform' :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ (κ q : ℕ), κ ≤ 1 → 1 ≤ q →
      ∀ τ, |muq κ q τ| ≤ (Real.log q / (2 * π) + M₀) + |τ| :=
  ⟨10 / π + 1, by positivity, fun κ q hκ hq τ => muq_linear_bound_uniform hκ hq τ⟩

/-- **The compactness step, q-uniform**: on `[-1,1]`, `|μ_χ| ≤ (log q)/2π + M₀`, `M₀ = 10/π`. -/
theorem muq_linear_bound_Icc_uniform :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ (κ q : ℕ), κ ≤ 1 → 1 ≤ q →
      ∀ τ ∈ Set.Icc (-1:ℝ) 1, |muq κ q τ| ≤ Real.log q / (2 * π) + M₀ :=
  ⟨10 / π, by positivity, fun κ q hκ hq τ hτ =>
    muq_abs_le_of_abs_le_one hκ hq τ (abs_le.mpr ⟨hτ.1, hτ.2⟩)⟩

/-! ## 3. `muq_abs_le`, q-uniform (replaces PrimeSideChi.lean:50) -/

/-- On `[T, 2T]`, `T ≥ 2πe`: `|μ_χ(τ)| ≤ (log q)/2π + (11/π)·l(T)`. -/
theorem muq_abs_le_Icc_uniform {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) {T : ℝ}
    (hT : 2 * π * Real.exp 1 ≤ T) (τ : ℝ) (hτ : τ ∈ Set.Icc T (2 * T)) :
    |muq κ q τ| ≤ Real.log q / (2 * π) + (11 / π) * Zeta23.l T := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have he1 : (1:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hT0 : 2 * π ≤ T := by nlinarith
  have hl1 : 1 ≤ Zeta23.l T := one_le_l_of_ge hT
  have hτpos : (0:ℝ) < τ := by nlinarith [hτ.1]
  have hτ1 : 1 ≤ |τ| := by rw [abs_of_pos hτpos]; nlinarith [hτ.1]
  have hst := muq_stirling_const hκ hq τ hτ1
  have hq0 : (0:ℝ) < q := by exact_mod_cast lt_of_lt_of_le zero_lt_one hq
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hx1 : (1:ℝ) ≤ (q:ℝ) * |τ| / (2 * π) := by
    rw [le_div_iff₀ (by positivity), abs_of_pos hτpos]
    nlinarith [le_trans hT0 hτ.1]
  have hlog0 : 0 ≤ Real.log ((q:ℝ) * |τ| / (2 * π)) := Real.log_nonneg hx1
  have hlogup : Real.log ((q:ℝ) * |τ| / (2 * π)) ≤ Real.log q + Real.log 2 + Zeta23.l T := by
    have hτT : |τ| ≤ 2 * T := by rw [abs_of_pos hτpos]; exact hτ.2
    calc Real.log ((q:ℝ) * |τ| / (2 * π)) ≤ Real.log ((q:ℝ) * (2 * T) / (2 * π)) := by
          apply Real.log_le_log (by positivity)
          gcongr
      _ = Real.log q + Real.log 2 + Zeta23.l T := by
          have hTpos : (0:ℝ) < T := by nlinarith
          rw [show (q:ℝ) * (2 * T) / (2 * π) = (q:ℝ) * (2 * (T / (2 * π))) by ring,
            Real.log_mul (ne_of_gt hq0) (by positivity),
            Real.log_mul (by norm_num) (ne_of_gt (by positivity : (0:ℝ) < T / (2 * π))), Zeta23.l]
          ring
  have hE : |muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| ≤ 10 / π := by
    refine hst.trans ?_
    rw [twenty_div_two_pi]
    exact div_le_self (by positivity) (by nlinarith [sq_abs τ])
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hmain : 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))
      ≤ Real.log q / (2 * π) + (1 / π) * Zeta23.l T := by
    calc 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))
        ≤ 1 / (2 * π) * (Real.log q + Real.log 2 + Zeta23.l T) := by gcongr
      _ = Real.log q / (2 * π) + (Real.log 2 + Zeta23.l T) / (2 * π) := by ring
      _ ≤ Real.log q / (2 * π) + (2 * Zeta23.l T) / (2 * π) := by gcongr; linarith
      _ = Real.log q / (2 * π) + (1 / π) * Zeta23.l T := by
          field_simp
  have hnn : 0 ≤ 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)) :=
    mul_nonneg (by positivity) hlog0
  have h10l : 10 / π ≤ (10 / π) * Zeta23.l T := le_mul_of_one_le_right (by positivity) hl1
  calc |muq κ q τ|
      = |(muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
          + 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| := by ring_nf
    _ ≤ |muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))|
          + |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| := abs_add_le _ _
    _ ≤ 10 / π + (Real.log q / (2 * π) + (1 / π) * Zeta23.l T) := by
        rw [abs_of_nonneg hnn]; exact add_le_add hE hmain
    _ ≤ Real.log q / (2 * π) + (11 / π) * Zeta23.l T := by
        have : (11 / π) * Zeta23.l T = (10 / π) * Zeta23.l T + (1 / π) * Zeta23.l T := by ring
        linarith

/-- **q-uniform `muq_abs_le`** (mirror of `PrimeSideChi.lean:50`, `Setting`-typed): with
`C = 11/π` and `T₀ = 2πe`, `|μ_χ(τ)| ≤ ((log q)/2π + C)·l(T)` on `[T, 2T]`. -/
theorem muq_abs_le_uniform :
    ∃ C T₀ : ℝ, 0 < C ∧ ∀ (κ q : ℕ), κ ≤ 1 → 1 ≤ q →
      ∀ p : Zeta23.PrimeSide.Setting, T₀ ≤ p.T →
        ∀ τ ∈ Set.Icc p.T (2 * p.T),
          |muq κ q τ| ≤ (Real.log q / (2 * π) + C) * Zeta23.l p.T := by
  refine ⟨11 / π, 2 * π * Real.exp 1, by positivity, fun κ q hκ hq p hT τ hτ => ?_⟩
  have h := muq_abs_le_Icc_uniform hκ hq hT τ hτ
  have hl1 : 1 ≤ Zeta23.l p.T := one_le_l_of_ge hT
  have hlq : 0 ≤ Real.log q / (2 * π) := div_nonneg (Real.log_nonneg (by exact_mod_cast hq))
    (by positivity)
  calc |muq κ q τ| ≤ Real.log q / (2 * π) + (11 / π) * Zeta23.l p.T := h
    _ ≤ Real.log q / (2 * π) * Zeta23.l p.T + (11 / π) * Zeta23.l p.T := by
        gcongr; exact le_mul_of_one_le_right hlq hl1
    _ = (Real.log q / (2 * π) + 11 / π) * Zeta23.l p.T := by ring

/-! ## 4. `muq_increment_bound`, q-uniform (replaces PrimeSideChi.lean:303) -/

/-- The increment argument of `PrimeSideChi.lean:303`, abstracted over `f` (verbatim body). -/
theorem increment_of_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) {C₁ M : ℝ} (hM0 : 0 ≤ M)
    (hC₁ : ∀ τ : ℝ, 1 ≤ |τ| → |deriv f τ| ≤ C₁ / |τ|)
    (hM : ∀ τ, |f τ| ≤ M + |τ|) (t : ℝ) (ht : 2 ≤ t) (r : ℝ) :
    |f (t + r) - f t| ≤ max (2 * |C₁|) (18 * M + 18) * (|r| + r ^ 2) / t := by
  have ht0 : 0 < t := by linarith
  rw [le_div_iff₀ ht0]
  rcases le_or_gt |r| (t / 2) with hr | hr
  · have hmvt : ‖f (t + r) - f t‖ ≤ (2 * |C₁| / t) * ‖(t + r) - t‖ := by
      apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (t / 2) (3 * t / 2))
      · intro x _
        exact hf.contDiffAt.differentiableAt (by simp)
      · intro x hx
        have hx1 : 1 ≤ |x| := by
          rw [abs_of_pos (by linarith [hx.1])]
          linarith [hx.1]
        calc ‖deriv f x‖ = |deriv f x| := Real.norm_eq_abs _
          _ ≤ C₁ / |x| := hC₁ x hx1
          _ ≤ |C₁| / |x| := by gcongr; exact le_abs_self _
          _ ≤ |C₁| / (t / 2) := by
              apply div_le_div_of_nonneg_left (abs_nonneg _) (by linarith)
              rw [abs_of_pos (by linarith [hx.1])]
              exact hx.1
          _ = 2 * |C₁| / t := by field_simp
      · exact convex_Icc _ _
      · constructor <;> linarith
      · constructor <;> linarith [le_abs_self r, neg_abs_le r]
    simp only [add_sub_cancel_left, Real.norm_eq_abs] at hmvt
    calc |f (t + r) - f t| * t ≤ (2 * |C₁| / t * |r|) * t := by gcongr
      _ = 2 * |C₁| * |r| := by field_simp
      _ ≤ max (2 * |C₁|) (18 * M + 18) * (|r| + r ^ 2) := by
          nlinarith [le_max_left (2 * |C₁|) (18 * M + 18), abs_nonneg r, sq_nonneg r,
            le_max_right (2 * |C₁|) (18 * M + 18)]
  · have h1 : |f (t + r) - f t| ≤ 2 * M + 2 + 7 * |r| := by
      calc |f (t + r) - f t| ≤ |f (t + r)| + |f t| := abs_sub _ _
        _ ≤ (M + |t + r|) + (M + |t|) := add_le_add (hM _) (hM _)
        _ ≤ (M + (|t| + |r|)) + (M + |t|) := by linarith [abs_add_le t r]
        _ = 2 * M + 2 * |t| + |r| := by ring
        _ ≤ 2 * M + 2 + 7 * |r| := by
            rw [abs_of_pos ht0]
            nlinarith
    calc |f (t + r) - f t| * t ≤ (2 * M + 2 + 7 * |r|) * t := by gcongr
      _ ≤ (2 * M + 2 + 7 * |r|) * (2 * |r|) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (4 * M + 4) * |r| + 14 * |r| ^ 2 := by ring
      _ = (4 * M + 4) * |r| + 14 * r ^ 2 := by rw [sq_abs]
      _ ≤ max (2 * |C₁|) (18 * M + 18) * (|r| + r ^ 2) := by
          nlinarith [le_max_right (2 * |C₁|) (18 * M + 18), abs_nonneg r, sq_nonneg r, hM0]

/-- The `q = 1` linear bound with the explicit absolute constant. -/
theorem muq_one_linear_bound {κ : ℕ} (hκ : κ ≤ 1) (τ : ℝ) :
    |muq κ 1 τ| ≤ (10 / π + 1) + |τ| := by
  have h := muq_linear_bound_uniform hκ (le_refl 1) τ
  have h1 : Real.log ((1:ℕ):ℝ) = 0 := by simp
  rw [h1, zero_div, zero_add] at h
  exact h

/-- **q-uniform `muq_increment_bound`, explicit**: `K = 180/π + 36` for ALL `κ ≤ 1` and ALL `q`
(no `1 ≤ q` needed — increments are q-free). -/
theorem muq_increment_bound_explicit {κ : ℕ} (hκ : κ ≤ 1) (q : ℕ) (t : ℝ) (ht : 2 ≤ t) (r : ℝ) :
    |muq κ q (t + r) - muq κ q t| ≤ (180 / π + 36) * (|r| + r ^ 2) / t := by
  have hπ := Real.pi_pos
  rw [muq_sub_eq]
  have h := increment_of_bounds (muq_smooth κ 1) (by positivity : (0:ℝ) ≤ 10 / π + 1)
    (muq_deriv_bound_const hκ) (muq_one_linear_bound hκ) t ht r
  have hK : max (2 * |24 / π|) (18 * (10 / π + 1) + 18) = 180 / π + 36 := by
    rw [abs_of_pos (by positivity), max_eq_right]
    · ring
    · have : (2:ℝ) * (24 / π) ≤ 180 / π := by
        rw [show (2:ℝ) * (24 / π) = 48 / π by ring]
        exact div_le_div_of_nonneg_right (by norm_num) hπ.le
      have e : (18:ℝ) * (10 / π + 1) + 18 = 180 / π + 36 := by ring
      linarith
  rwa [hK] at h

/-- **q-uniform `muq_increment_bound`, existential shape** (mirror of `PrimeSideChi.lean:303`). -/
theorem muq_increment_bound_uniform :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (κ q : ℕ), κ ≤ 1 → ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |muq κ q (t + r) - muq κ q t| ≤ K * (|r| + r ^ 2) / t :=
  ⟨180 / π + 36, by positivity, fun κ q hκ t ht r => muq_increment_bound_explicit hκ q t ht r⟩

/-! ## 5. `muq_nonneg_eventually`, q-uniform (replaces PrimeSideChi.lean:354) -/

/-- `μ_χ(x) ≥ 0` for `x ≥ 2πe`, uniformly in `q ≥ 1` and `κ ≤ 1`. -/
theorem muq_nonneg_of_ge {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) (x : ℝ)
    (hx : 2 * π * Real.exp 1 ≤ x) : 0 ≤ muq κ q x := by
  have hπ3 := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hx12 : 12 ≤ x := by nlinarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ |x| := by rw [abs_of_pos hx0]; linarith
  have hst := muq_stirling_const hκ hq x hx1
  rw [abs_of_pos hx0] at hst
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 1 ≤ Real.log ((q:ℝ) * x / (2 * π)) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hE : (20 / (2 * π)) / x ^ 2 ≤ 1 / (2 * π) := by
    rw [div_le_iff₀ (by positivity)]
    have h20 : (20:ℝ) / (2 * π) = 1 / (2 * π) * 20 := by ring
    rw [h20]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h2 : 1 / (2 * π) ≤ 1 / (2 * π) * Real.log ((q:ℝ) * x / (2 * π)) :=
    le_mul_of_one_le_right (by positivity) hlog
  linarith [(abs_le.mp hst).1]

/-- **q-uniform `muq_nonneg_eventually`** (mirror of `PrimeSideChi.lean:354`): `τ₀ = 2πe`. -/
theorem muq_nonneg_eventually_uniform :
    ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ∀ (κ q : ℕ), κ ≤ 1 → 1 ≤ q → ∀ x, τ₀ ≤ x → 0 ≤ muq κ q x :=
  ⟨2 * π * Real.exp 1, by positivity, fun κ q hκ hq x hx => muq_nonneg_of_ge hκ hq x hx⟩

/-- Two-sided version via evenness: `μ_χ(x) ≥ 0` for `|x| ≥ 2πe`. -/
theorem muq_nonneg_of_abs_ge {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) (x : ℝ)
    (hx : 2 * π * Real.exp 1 ≤ |x|) : 0 ≤ muq κ q x := by
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx; exact muq_nonneg_of_ge hκ hq x hx
  · rw [abs_of_neg h0] at hx
    rw [← muq_even hκ x]; exact muq_nonneg_of_ge hκ hq (-x) hx

/-! ## 6. Sanity: the per-q statements follow from the uniform ones -/

example (κ q : ℕ) (hκ : κ ≤ 1) (hq : 1 ≤ q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, |muq κ q τ| ≤ M + |τ| := by
  obtain ⟨M₀, hM₀, h⟩ := muq_linear_bound_uniform'
  exact ⟨Real.log q / (2 * π) + M₀, by
    have := Real.log_nonneg (by exact_mod_cast hq : (1:ℝ) ≤ q); positivity, h κ q hκ hq⟩


/-! ## 7. The μ-part of `prop_trace_chi` (its steps h1 + h2), re-run q-UNIFORMLY per character

`prop_trace_chi` (`PrimeSideChi.lean:820`) carries `lam ≤ 1`; its μ-part does not need it.  Below is
that μ-part, typed over the cap-free `LocalHypsCoreW` with every constant explicit and q entering
ONLY through `(log q)/2π`. -/

section MuPartCore

open Zeta23.PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {κ q : ℕ}

/-- `h·L = 2π`. -/
theorem h_mul_L (hL : 0 < p.L) : p.h * p.L = 2 * π := by
  simp only [Setting.h]; exact div_mul_cancel₀ _ hL.ne'

/-- **The μ-part of `prop_trace_chi`, q-uniform** (mirror of its `h1`, `h2`, `t1` with the
uniform constants): for `T ≥ 2πe + 1`,
`|Σ_{k<d} ∫ φ̂(r)² μ_χ(τ_k + r) dr − aL² ∫_T^{2T} μ_χ|
   ≤ K(16 + 2cϱ + 2cϱ²) L²/(2π) + 4πL((log q)/2π + (11/π) l(T))`,  `K = 180/π + 36`. -/
theorem muPart_approx_core (hκ : κ ≤ 1) (hq : 1 ≤ q) (hF : LocalHypsCoreW cϱ p F)
    (hT : 2 * π * Real.exp 1 + 1 ≤ p.T) :
    |(∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * muq κ q (p.tau k + r))
        - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ|
      ≤ (180 / π + 36) * (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L ^ 2 / (2 * π)
        + 4 * π * p.L * (Real.log q / (2 * π) + 11 / π * Zeta23.l p.T) := by
  have hΓq : GammaFactsChi κ q := gammaFactsChi hκ hq
  set K : ℝ := 180 / π + 36 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |muq κ q (t + r) - muq κ q t| ≤ K * (|r| + r ^ 2) / t :=
    fun t ht r => muq_increment_bound_explicit hκ q t ht r
  have hπ := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have he1 : (1:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hTe : 2 * π * Real.exp 1 ≤ p.T := by linarith
  have hT0 : (0:ℝ) < p.T := by nlinarith
  have hT2 : (2:ℝ) ≤ p.T := by nlinarith
  have hL := hF.L_pos
  have hL8 := hF.eight_le_L
  have hc4 := hF.four_le_cϱ
  have hc0 : (0:ℝ) ≤ cϱ := by linarith
  have hh0 : 0 < p.h := by simp only [Setting.h]; positivity
  have hhL : p.h * p.L = 2 * π := h_mul_L hL
  have hl1 : (1:ℝ) ≤ Zeta23.l p.T := hF.one_le_l
  have ha1 := hF.a_le_one
  have ha0 := hF.a_pos.le
  set I₁ := ∫ r, F.phiHat r ^ 2 * |r| with hI₁def
  set I₂ := ∫ r, F.phiHat r ^ 2 * r ^ 2 with hI₂def
  have hI₁0 : 0 ≤ I₁ := MeasureTheory.integral_nonneg fun r => by positivity
  have hI₂0 : 0 ≤ I₂ := MeasureTheory.integral_nonneg fun r => by positivity
  have hI₁ : I₁ ≤ 8 + 2 * cϱ * p.L := by
    refine hF.integral_phiHat_sq_mul_abs_le.trans ?_
    have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) :=
      Real.log_le_self (by have := hF.one_le_w; positivity)
    have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith [hF.one_le_w]
    linarith
  have hI₂ : I₂ ≤ 8 + 2 * cϱ ^ 2 := by
    refine hF.integral_phiHat_sq_mul_sq_le.trans ?_
    have h3 : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]
      exact div_le_self (sq_nonneg _) (by nlinarith [hF.one_le_w])
    linarith
  have hτg : ∀ k ∈ Finset.range p.d, p.T ≤ p.tau k ∧ p.tau k ≤ 2 * p.T := fun k hk =>
    p.tau_mem hL hT0.le hk
  set Gμ : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * muq κ q (p.tau k + r) with hGμ
  -- h1: grid-point values
  have h1 : |∑ k ∈ Finset.range p.d, Gμ k - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d,
      muq κ q (p.tau k)| ≤ p.d * (K * (I₁ + I₂) / p.T) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hbd : ∀ k ∈ Finset.range p.d, |Gμ k - 2 * π * F.a * p.L * muq κ q (p.tau k)|
        ≤ K * (I₁ + I₂) / p.T := by
      intro k hk
      have ht2 : 2 ≤ p.tau k := by linarith [(hτg k hk).1, hT2]
      refine (muq_part_bound hΓq hq hF hK0 hK ht2).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) hT0 (hτg k hk).1
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hhT : p.h ≤ p.T := by
    simp only [Setting.h]
    rw [div_le_iff₀ hL]
    nlinarith [Real.pi_lt_four]
  have hh1 : p.h ≤ 1 := by
    simp only [Setting.h]
    rw [div_le_one hL]
    nlinarith [Real.pi_lt_four]
  -- h2: Riemann sum vs integral (monotone, nonneg on [T − h, ∞) since T − h ≥ 2πe)
  have h2 : |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)
      - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ|
      ≤ 4 * π * p.L * (Real.log q / (2 * π) + 11 / π * Zeta23.l p.T) := by
    have hR := riemann_sum_monotone (μ := muq κ q) (T := p.T) hh0 hhT
      ((muq_monotoneOn (q := q) hκ).mono (fun x hx => by
        simp only [Set.mem_Ici] at hx ⊢
        linarith))
      (fun x hx => muq_nonneg_of_ge hκ hq x (by linarith))
    rw [← p.d_eq_floor hL] at hR
    have hsum2 : ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)
        = ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h) := by
      refine Finset.sum_congr rfl fun k _ => by rw [Setting.tau_natCast]
    rw [hsum2]
    have hid : 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h)
        - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ
        = F.a * p.L ^ 2 * (p.h * ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h)
            - ∫ τ in p.T..(2 * p.T), muq κ q τ) := by
      linear_combination (-(F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h))) * hhL
    rw [hid, abs_mul, abs_of_nonneg (by positivity)]
    have hμ2T : muq κ q (2 * p.T) ≤ Real.log q / (2 * π) + 11 / π * Zeta23.l p.T := by
      have hv := muq_abs_le_Icc_uniform hκ hq hTe (2 * p.T) ⟨by linarith, le_rfl⟩
      exact (le_abs_self _).trans hv
    have hμ2T0 : 0 ≤ muq κ q (2 * p.T) := muq_nonneg_of_ge hκ hq _ (by linarith)
    calc F.a * p.L ^ 2 * |p.h * ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h)
          - ∫ τ in p.T..(2 * p.T), muq κ q τ|
        ≤ F.a * p.L ^ 2 * (2 * p.h * muq κ q (2 * p.T)) := by gcongr
      _ ≤ 1 * p.L ^ 2 * (2 * p.h * (Real.log q / (2 * π) + 11 / π * Zeta23.l p.T)) := by
          gcongr
      _ = 4 * π * p.L * (Real.log q / (2 * π) + 11 / π * Zeta23.l p.T) := by
          linear_combination (2 * p.L * (Real.log q / (2 * π) + 11 / π * Zeta23.l p.T)) * hhL
  -- t1: d ≤ LT/2π and I₁ + I₂ ≤ (16 + 2cϱ + 2cϱ²) L
  have hd : (p.d : ℝ) ≤ p.L * p.T / (2 * π) := p.d_le (by positivity)
  have e3 : I₁ + I₂ ≤ (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L := by
    have u1 : (16:ℝ) ≤ 16 * p.L := by nlinarith
    have u3 : 2 * cϱ ^ 2 ≤ 2 * cϱ ^ 2 * p.L := by nlinarith [sq_nonneg cϱ]
    nlinarith
  have hTT : p.T * p.T⁻¹ = 1 := mul_inv_cancel₀ hT0.ne'
  have t1 : (p.d : ℝ) * (K * (I₁ + I₂) / p.T)
      ≤ K * (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L ^ 2 / (2 * π) := by
    calc (p.d : ℝ) * (K * (I₁ + I₂) / p.T)
        ≤ p.L * p.T / (2 * π) * (K * ((16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L) / p.T) := by gcongr
      _ = K * (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L ^ 2 / (2 * π) := by
          linear_combination (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L ^ 2 / (2 * π)) * hTT
  calc |(∑ k ∈ Finset.range p.d, Gμ k) - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ|
      = |(∑ k ∈ Finset.range p.d, Gμ k
            - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k))
          + (2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)
            - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ)| := by ring_nf
    _ ≤ |∑ k ∈ Finset.range p.d, Gμ k
            - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)|
          + |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)
            - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ| := abs_add_le _ _
    _ ≤ _ := by linarith [h1, h2, t1]

/-- **…and against `T ℓ_{1,χ}(T)/2π`** (adds `GammaFactsChiBounded.int_mu` in its explicit form
`IntMuChi.int_muq_uniform (20/2π)`): for `T ≥ 2πe + 1`,
`|Σ_{k<d} ∫ φ̂² μ_χ(τ_k + r) − aL²·Tℓ_{1,χ}(T)/2π|
   ≤ K(16 + 2cϱ + 2cϱ²) L²/(2π) + 4πL((log q)/2π + (11/π) l(T)) + (10/π) L²/T`. -/
theorem muPart_approx_ell1 (hκ : κ ≤ 1) (hq : 1 ≤ q) (hF : LocalHypsCoreW cϱ p F)
    (hT : 2 * π * Real.exp 1 + 1 ≤ p.T) :
    |(∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * muq κ q (p.tau k + r))
        - F.a * p.L ^ 2 * (p.T * ell1q q p.T / (2 * π))|
      ≤ (180 / π + 36) * (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L ^ 2 / (2 * π)
        + 4 * π * p.L * (Real.log q / (2 * π) + 11 / π * Zeta23.l p.T)
        + (10 / π) * p.L ^ 2 / p.T := by
  have hπ := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have he1 : (1:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hT1 : (1:ℝ) ≤ p.T := by nlinarith
  have hT0 : (0:ℝ) < p.T := by linarith
  have hL := hF.L_pos
  have ha1 := hF.a_le_one
  have ha0 := hF.a_pos.le
  have hmain := muPart_approx_core hκ hq hF hT
  have hint := Zeta23.ThmE.IntMuChi.int_muq_uniform (20 / (2 * π)) κ q hq
    (muq_smooth κ q).continuous (muq_stirling_const hκ hq) p.T hT1
  rw [twenty_div_two_pi] at hint
  have hstep : |F.a * p.L ^ 2 * (∫ τ in p.T..(2 * p.T), muq κ q τ)
      - F.a * p.L ^ 2 * (p.T * ell1q q p.T / (2 * π))| ≤ (10 / π) * p.L ^ 2 / p.T := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    calc F.a * p.L ^ 2 * |(∫ τ in p.T..(2 * p.T), muq κ q τ) - p.T * ell1q q p.T / (2 * π)|
        ≤ 1 * p.L ^ 2 * (10 / π / p.T) := by gcongr
      _ = (10 / π) * p.L ^ 2 / p.T := by ring
  calc |(∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * muq κ q (p.tau k + r))
        - F.a * p.L ^ 2 * (p.T * ell1q q p.T / (2 * π))|
      = |((∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * muq κ q (p.tau k + r))
            - F.a * p.L ^ 2 * (∫ τ in p.T..(2 * p.T), muq κ q τ))
          + (F.a * p.L ^ 2 * (∫ τ in p.T..(2 * p.T), muq κ q τ)
            - F.a * p.L ^ 2 * (p.T * ell1q q p.T / (2 * π)))| := by ring_nf
    _ ≤ |(∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * muq κ q (p.tau k + r))
            - F.a * p.L ^ 2 * (∫ τ in p.T..(2 * p.T), muq κ q τ)|
          + |F.a * p.L ^ 2 * (∫ τ in p.T..(2 * p.T), muq κ q τ)
            - F.a * p.L ^ 2 * (p.T * ell1q q p.T / (2 * π))| := abs_add_le _ _
    _ ≤ _ := add_le_add hmain hstep

end MuPartCore

end MuqUniform
end ZetaQ
