/-
A2a_S2s_Main (L7_8, round 3): the Möbius main-term identity of Step 2:
`Σ_{g | |j|} μ(g)·[S ≠ ∅]/(r·lcm(g, f_(r))) = (1/r)(φ(|j|)/|j|)∏_{p|f}δ_p`.
Proved ingredients: `mobius_lcm_sum`, `mobius_lcm_sum_eval` (subset form), `admissible_exists`/`_necessary`.
Round 4: PROVED (sorry-free) from `mu_lcm_divisor_sum`, `prod_one_sub_inv_primeFactors`, `deltaProd_eval`,
`deltaProd_zero` (A2a_S2s_MainAux).
-/
import ZetaShell.Lemma2.A2a_S2s_Defs
import ZetaShell.Lemma2.A2a_S2s_MainAux

noncomputable section
open scoped BigOperators
open Classical

namespace ZetaShell
namespace TrackF

theorem s2_main (r j : ℤ) (f : ℕ) (hr : 1 ≤ r) (hj : j ≠ 0) (hf : Squarefree f) :
    ∑ g ∈ j.natAbs.divisors, ((ArithmeticFunction.moebius g : ℤ) : ℝ) *
        (if admissibleP r j f then 1 / ((r : ℝ) * (Nat.lcm g (fOff f r) : ℝ)) else 0)
      = (1 / (r : ℝ)) * ((Nat.totient j.natAbs : ℝ) / j.natAbs) * deltaProd r j f := by
  have hn : j.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hj
  have hF := fOff_pos f r
  by_cases hadm : admissibleP r j f
  · simp only [if_pos hadm]
    have e : ∀ g ∈ j.natAbs.divisors, ((ArithmeticFunction.moebius g : ℤ) : ℝ) *
        (1 / ((r : ℝ) * (Nat.lcm g (fOff f r) : ℝ)))
        = (1 / (r : ℝ)) * (((ArithmeticFunction.moebius g : ℤ) : ℝ) * (1 / ((Nat.lcm g (fOff f r) : ℕ) : ℝ))) := by
      intro g _
      have hr0 : (r : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ r := by exact_mod_cast hr
        linarith
      have hl0 : ((Nat.lcm g (fOff f r) : ℕ) : ℝ) ≠ 0 := by
        have hg : 0 < g := Nat.pos_of_mem_divisors ‹g ∈ j.natAbs.divisors›
        exact_mod_cast (Nat.lcm_pos hg hF).ne'
      field_simp
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, mu_lcm_divisor_sum _ _ hn hF,
      mobius_lcm_sum_eval _ (fun p hp => Nat.prime_of_mem_primeFactors hp), deltaProd_eval r j f hj hadm]
    split_ifs with hc
    · rw [prod_one_sub_inv_primeFactors _ hn]
      ring
    · simp
  · simp only [if_neg hadm, mul_zero, Finset.sum_const_zero]
    rw [deltaProd_zero r j f hadm]
    ring

end TrackF
end ZetaShell
