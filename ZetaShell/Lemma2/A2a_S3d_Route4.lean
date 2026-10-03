/-
A2a_S3d_Route4 (L7_8, round 5): route (b) for `s3_arith`: the internal weight `g_X` with exponent 4,
`gX4 X n = τ(n)(1 + log(X/n))⁴` (`n ≤ X`), for which both sub-nodes are proved:
* `s3_arith_jsum4`: `Σ_{0<|j|≤X+1} gX4(|j|) ≤ 26244 (X+1)(1+log(X+1))` (`(1 + log t)⁴ ≤ 6561√t`);
* `s3_arith_inner4`: `2^{ω(|j|)} Σ_{e|j|≤X} |c_e| Σ_{f≤Q} |λ_e(f)| ≤ C(1 + log Q)·gX4(|j|)` (from `ce_tau_le4`).
The extra logarithm is absorbed in the `j`-sum (`Σ_{n≤X} τ(n)(1+log(X/n))^k ≪_k X log X`), so `s3_arith`'s statement
is unchanged.
-/
import ZetaShell.Lemma2.A2a_S3d_Qphi4
import ZetaShell.Lemma2.A2a_S3d_JsumProof

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

def gX4 (X : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ X then (n.divisors.card : ℝ) * (1 + Real.log (X / n)) ^ 4 else 0

theorem one_add_log_pow4_le (t : ℝ) (ht : 1 ≤ t) : (1 + Real.log t) ^ 4 ≤ 6561 * Real.sqrt t := by
  have ht0 : 0 ≤ t := by linarith
  have hlog := Real.log_le_rpow_div ht0 (show (0 : ℝ) < 1 / 8 by norm_num)
  set u := t ^ (1 / 8 : ℝ) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow ht (by norm_num)
  have hsq : Real.sqrt t = u ^ 4 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0, Real.sqrt_eq_rpow]; norm_num
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 : 1 + Real.log t ≤ 9 * u := by
    have : Real.log t ≤ 8 * u := by rw [div_eq_mul_inv] at hlog; norm_num at hlog; linarith
    linarith
  rw [hsq]
  have h2 : (1 + Real.log t) ^ 4 ≤ (9 * u) ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
  calc (1 + Real.log t) ^ 4 ≤ (9 * u) ^ 4 := h2
    _ = 6561 * u ^ 4 := by ring

theorem gX4_le (X : ℝ) (hX : 0 ≤ X) (n : ℕ) (hn : 1 ≤ n) :
    gX4 X n ≤ 6561 * Real.sqrt X * ((n.divisors.card : ℝ) / Real.sqrt n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gX4
  split_ifs with h
  · have ht : 1 ≤ X / n := by rw [le_div_iff₀ hnR]; linarith
    have h1 := one_add_log_pow4_le (X / n) ht
    rw [Real.sqrt_div' _ hnR.le] at h1
    have hτ : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
    calc (n.divisors.card : ℝ) * (1 + Real.log (X / n)) ^ 4
        ≤ (n.divisors.card : ℝ) * (6561 * (Real.sqrt X / Real.sqrt n)) := mul_le_mul_of_nonneg_left h1 hτ
      _ = 6561 * Real.sqrt X * ((n.divisors.card : ℝ) / Real.sqrt n) := by ring
  · positivity

theorem s3_arith_jsum4 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℝ), 0 ≤ X →
    ∑ j ∈ lineSet (⌊X⌋₊ + 1), gX4 X j.natAbs ≤ C * ((X + 1) * (1 + Real.log (X + 1))) := by
  refine ⟨26244, by norm_num, ?_⟩
  intro X hX
  set M := ⌊X⌋₊ + 1 with hM
  rw [lineSet_sum_abs M (gX4 X)]
  have hMX : (M : ℝ) ≤ X + 1 := by
    rw [hM]; push_cast; linarith [Nat.floor_le hX]
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [(Nat.cast_nonneg ⌊X⌋₊ : (0 : ℝ) ≤ ⌊X⌋₊)]
  have h1 : ∑ n ∈ Finset.Icc 1 M, gX4 X n ≤ 6561 * Real.sqrt X * (2 * Real.sqrt M * (1 + Real.log M)) := by
    calc ∑ n ∈ Finset.Icc 1 M, gX4 X n
        ≤ ∑ n ∈ Finset.Icc 1 M, 6561 * Real.sqrt X * ((n.divisors.card : ℝ) / Real.sqrt n) :=
          Finset.sum_le_sum (fun n hn => gX4_le X hX n (Finset.mem_Icc.mp hn).1)
      _ = 6561 * Real.sqrt X * ∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) / Real.sqrt n := by
          rw [Finset.mul_sum]
      _ ≤ 6561 * Real.sqrt X * (2 * Real.sqrt M * (1 + Real.log M)) :=
          mul_le_mul_of_nonneg_left (sum_tau_inv_sqrt_le M) (by positivity)
  have hsX : Real.sqrt X ≤ Real.sqrt (X + 1) := Real.sqrt_le_sqrt (by linarith)
  have hsM : Real.sqrt M ≤ Real.sqrt (X + 1) := Real.sqrt_le_sqrt hMX
  have hss : Real.sqrt (X + 1) * Real.sqrt (X + 1) = X + 1 := Real.mul_self_sqrt (by linarith)
  have hlog : Real.log M ≤ Real.log (X + 1) := Real.log_le_log (by linarith) hMX
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hprod : Real.sqrt X * Real.sqrt M ≤ X + 1 := by
    rw [← hss]
    exact mul_le_mul hsX hsM (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 : 6561 * Real.sqrt X * (2 * Real.sqrt M * (1 + Real.log M))
      ≤ 13122 * ((X + 1) * (1 + Real.log (X + 1))) := by
    have e : 6561 * Real.sqrt X * (2 * Real.sqrt M * (1 + Real.log M))
        = 13122 * ((Real.sqrt X * Real.sqrt M) * (1 + Real.log M)) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul hprod (by linarith) (by linarith) (by linarith)
  linarith

theorem s3_arith_inner4 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : FKind) (Q : ℕ) (X : ℝ) (j : ℤ), 2 ≤ Q → 0 ≤ X → j ≠ 0 →
    (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) *
      ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
        |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
      ≤ C * ((1 + Real.log Q) * gX4 X j.natAbs) := by
  obtain ⟨C, hC, h⟩ := ce_tau_le4
  refine ⟨C, hC, ?_⟩
  intro k Q X j hQ hX hj
  set n := j.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hj
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have habs : |(j : ℝ)| = (n : ℝ) := by rw [hn, Nat.cast_natAbs, Int.cast_abs]
  have hQ1 : 1 ≤ Q := by omega
  have hlQ : 0 ≤ 1 + Real.log Q := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Q by exact_mod_cast hQ1); linarith
  have hsum_nn : 0 ≤ ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
      |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f| :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun f _ => abs_nonneg _)))
  by_cases hnX : (n : ℝ) ≤ X
  · have hy : 1 ≤ X / n := by rw [le_div_iff₀ (by linarith)]; linarith
    have hstep1 : ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
          |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
        ≤ (1 + Real.log Q) * ∑ e ∈ Finset.Icc 1 ⌊X / n⌋₊, |cE k e| * (e.divisors.card : ℝ) := by
      rw [Finset.mul_sum]
      calc _ ≤ ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
              (1 + Real.log Q) * (|cE k e| * (e.divisors.card : ℝ)) := by
            apply Finset.sum_le_sum
            intro e he
            have he1 : 1 ≤ e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
            have := lam_sum_le k e Q he1 hQ1
            calc |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
                ≤ |cE k e| * ((e.divisors.card : ℝ) * (1 + Real.log Q)) :=
                  mul_le_mul_of_nonneg_left this (abs_nonneg _)
              _ = (1 + Real.log Q) * (|cE k e| * (e.divisors.card : ℝ)) := by ring
        _ ≤ ∑ e ∈ Finset.Icc 1 ⌊X / n⌋₊, (1 + Real.log Q) * (|cE k e| * (e.divisors.card : ℝ)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro e he
              obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
              rw [Finset.mem_Icc] at he1 ⊢
              refine ⟨he1.1, Nat.le_floor ?_⟩
              rw [habs] at he2
              rw [le_div_iff₀ (by linarith)]; exact he2
            · intro e _ _; positivity
    have hstep2 := h k (X / n) hy
    have hτ := two_pow_omega_le_tau n hn0
    unfold gX4
    rw [if_pos hnX]
    calc (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) *
          ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
            |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
        ≤ (n.divisors.card : ℝ) * ((1 + Real.log Q) *
            ∑ e ∈ Finset.Icc 1 ⌊X / n⌋₊, |cE k e| * (e.divisors.card : ℝ)) :=
          mul_le_mul hτ hstep1 hsum_nn (by positivity)
      _ ≤ (n.divisors.card : ℝ) * ((1 + Real.log Q) * (C * (1 + Real.log (X / n)) ^ 4)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hstep2 hlQ
      _ = C * ((1 + Real.log Q) * ((n.divisors.card : ℝ) * (1 + Real.log (X / n)) ^ 4)) := by ring
  · have hempty : (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he hle
      have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (Finset.mem_Icc.mp he).1
      rw [habs] at hle
      have : (n : ℝ) ≤ (e : ℝ) * n := by nlinarith
      exact hnX (by linarith)
    rw [hempty, Finset.sum_empty, mul_zero]
    unfold gX4
    rw [if_neg hnX]
    simp

end TrackF
end ZetaShell
