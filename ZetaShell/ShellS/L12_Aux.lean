/-
L7_12 (28 Sep 2026): elementary asymptotic helpers for the proofs of S3 and S2 (no `sorry`).
-/
import Mathlib

noncomputable section

namespace ZetaShell
namespace ShellS

/-- eventually `(log n)^M · exp(−b log n) ≤ δ`. -/
lemma L12_ev_rpow_exp (M b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
    ∀ᶠ Qn : ℕ in Filter.atTop, Real.log Qn ^ M * Real.exp (-b * Real.log Qn) ≤ δ := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero M b hb
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact ((h1.comp h2).eventually (Iic_mem_nhds hδ)).mono fun n hn => hn

lemma L12_le_of_mul_exp (x y b δ : ℝ) (h : x * Real.exp (-b * y) ≤ δ) : x ≤ δ * Real.exp (b * y) := by
  have h2 := mul_le_mul_of_nonneg_right h (Real.exp_pos (b * y)).le
  calc x = x * Real.exp (-b * y) * Real.exp (b * y) := by
        rw [mul_assoc, ← Real.exp_add, show -b * y + b * y = 0 by ring, Real.exp_zero, mul_one]
    _ ≤ δ * Real.exp (b * y) := h2

lemma L12_log_eventually_ge (c : ℝ) : ∀ᶠ Qn : ℕ in Filter.atTop, c ≤ Real.log Qn :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop c

/-- eventually `(log log n)^M · exp(−b log log n) ≤ δ`. -/
lemma L12_ev_loglog (M b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
    ∀ᶠ Qn : ℕ in Filter.atTop,
      Real.log (Real.log Qn) ^ M * Real.exp (-b * Real.log (Real.log Qn)) ≤ δ := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero M b hb
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact ((h1.comp h2).eventually (Iic_mem_nhds hδ)).mono fun n hn => hn

lemma L12_loglog_eventually_ge (c : ℝ) : ∀ᶠ Qn : ℕ in Filter.atTop, c ≤ Real.log (Real.log Qn) :=
  (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop c

end ShellS
end ZetaShell
