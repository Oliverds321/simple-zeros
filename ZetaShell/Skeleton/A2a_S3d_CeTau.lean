/-
A2a_S3d_CeTau (L7_8, round 4): `Σ_{1≤e≤y} |c_e| τ(e) ≤ C(1 + log y)²`, split by kind.
* `ce_tau_le_plain` (PROVED): `|c_e| ≤ 1/e`, `Σ_{e≤N} τ(e)/e = Σ_{d≤N} (1/d) Σ_{m≤N/d} 1/m ≤ (1 + log N)²`, `C = 1`;
* `ce_tau_le_qphi` (open): `|c_e| = μ²(e)/φ(e)`; route: `μ²(e) e/φ(e) = Σ_{d|e} μ²(d)/φ(d)`, `τ(dm) ≤ τ(d)τ(m)`,
  and `Σ_{d sqfree} τ(d)/(dφ(d)) ≤ ∏_p (1 + 2/(p(p−1))) < ∞`.
-/
import ZetaShell.Lemma2.A2a_S3d_InnerAux

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem ce_tau_le_plain (y : ℝ) (hy : 1 ≤ y) :
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |cE FKind.plain e| * (e.divisors.card : ℝ) ≤ 1 * (1 + Real.log y) ^ 2 := by
  set N := ⌊y⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hy)
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hlogN : Real.log N ≤ Real.log y := Real.log_le_log (by exact_mod_cast hN1) hNy
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have h1 : ∀ e ∈ Finset.Icc 1 N, |cE FKind.plain e| * (e.divisors.card : ℝ) ≤ ∑ d ∈ e.divisors, 1 / (e : ℝ) := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heR : (0 : ℝ) < e := by exact_mod_cast he1
    rw [Finset.sum_const, nsmul_eq_mul]
    simp only [cE]
    rw [abs_div, abs_of_pos heR]
    have hmu : |((ArithmeticFunction.moebius e : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hτ : (0 : ℝ) ≤ (e.divisors.card : ℝ) := by positivity
    calc |((ArithmeticFunction.moebius e : ℤ) : ℝ)| / e * (e.divisors.card : ℝ)
        ≤ 1 / e * (e.divisors.card : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hτ
          exact div_le_div_of_nonneg_right hmu heR.le
      _ = (e.divisors.card : ℝ) * (1 / e) := by ring
  calc ∑ e ∈ Finset.Icc 1 N, |cE FKind.plain e| * (e.divisors.card : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ e.divisors, 1 / (e : ℝ) := Finset.sum_le_sum h1
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), 1 / ((d * m : ℕ) : ℝ) :=
        divisor_swap (fun _ e => 1 / (e : ℝ)) N
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (1 / (d : ℝ)) * (1 + Real.log N) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
        have e1 : ∑ m ∈ Finset.Icc 1 (N / d), 1 / ((d * m : ℕ) : ℝ)
            = (1 / (d : ℝ)) * ∑ m ∈ Finset.Icc 1 (N / d), 1 / (m : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
          push_cast; rw [one_div_mul_one_div]
        rw [e1]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine le_trans (sum_harmonic_le (N / d)) ?_
        have hNd : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
        rcases Nat.eq_zero_or_pos (N / d) with h0 | hpos
        · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
        · have := Real.log_le_log (by exact_mod_cast hpos) hNd; linarith
    _ = (∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ)) * (1 + Real.log N) := by rw [Finset.sum_mul]
    _ ≤ (1 + Real.log N) * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_right (sum_harmonic_le N) (by linarith)
    _ ≤ 1 * (1 + Real.log y) ^ 2 := by nlinarith

theorem ce_tau_le_qphi : ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ), 1 ≤ y →
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |cE FKind.qphi e| * (e.divisors.card : ℝ) ≤ C * (1 + Real.log y) ^ 2 := by
  sorry

end TrackF
end ZetaShell
