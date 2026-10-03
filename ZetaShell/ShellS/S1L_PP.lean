/-
S1L_PP (L7_5b, 1 Oct 2026): leaf `pp_window` of S1 (Lemma 5c(1)'s core) — the prime powers `n = p^k`, `k ≥ 2`, in
`(e^{s−1}, e^{s+1}]` carry `Σ Λ(n) n^{−1/2} ≤ e·|C|`, uniformly in `s`: `n^{−1/2} ≤ e^{−(s−1)/2}` there, and
`Σ_{n ≤ X, n not prime} Λ(n) = ψ(X) − θ(X) ≤ C √X` (Mathlib `Chebyshev.psi_sub_theta_le_mul_sqrt`), `X = e^{s+1}`.
-/
import ZetaShell.ShellS.S1_Defs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem pp_window' : ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ s : ℝ,
    ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Cp := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨Real.exp 1 * |C|, by positivity, fun s => ?_⟩
  set X := Real.exp (s + 1) with hX
  set c := Real.exp (s - 1) ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (Real.exp_pos _).le _
  have hterm : ∀ n ∈ (Finset.Ioc 0 (Nnear s)).filter (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ c * (ArithmeticFunction.vonMangoldt n : ℝ) := by
    intro n hn
    have hn' := (Finset.mem_filter.mp hn).2.2
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hle : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ c :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hn'.le (by norm_num)
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * c := mul_le_mul_of_nonneg_left hle hΛ
      _ = c * (ArithmeticFunction.vonMangoldt n : ℝ) := by ring
  have hsub : (Finset.Ioc 0 (Nnear s)).filter (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ))
      ⊆ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n : ℕ => ¬ n.Prime) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have hsum : ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
      (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n : ℕ => ¬ n.Prime), (ArithmeticFunction.vonMangoldt n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hpsi : ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n : ℕ => ¬ n.Prime), (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ |C| * Real.sqrt X := by
    rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime]
    exact (hC X).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))
  have hcX : c * Real.sqrt X = Real.exp 1 := by
    rw [hc, hX, Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; ring
  calc ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
        c * (ArithmeticFunction.vonMangoldt n : ℝ) := Finset.sum_le_sum hterm
    _ = c * ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
        (ArithmeticFunction.vonMangoldt n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ c * (|C| * Real.sqrt X) := mul_le_mul_of_nonneg_left (hsum.trans hpsi) hc0
    _ = Real.exp 1 * |C| := by rw [← hcX]; ring

end ShellS
end ZetaShell
