/-
A2a_S3d_JsumProof (L7_8, round 4): proof of `s3_arith_jsum` (same statement, named `s3_arith_jsum_pf`), with `C = 100`:
`Σ_{0<|j|≤X+1} g_X(|j|) ≤ 2·Σ_{n≤X+1} 25√X τ(n)/√n ≤ 100(X+1)(1+log(X+1))`.
-/
import ZetaShell.Skeleton.A2a_S3d_ArithSplit
import ZetaShell.Lemma2.A2a_S3d_JsumAux

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem lineSet_sum_abs (M : ℕ) (h : ℕ → ℝ) :
    ∑ j ∈ lineSet M, h j.natAbs = 2 * ∑ n ∈ Finset.Icc 1 M, h n := by
  classical
  unfold lineSet
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun j : ℤ => 0 < j)]
  have hpos : ∑ j ∈ ((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun j => j ≠ 0)).filter (fun j : ℤ => 0 < j), h j.natAbs
      = ∑ n ∈ Finset.Icc 1 M, h n := by
    apply Finset.sum_nbij' (fun j : ℤ => j.natAbs) (fun n : ℕ => (n : ℤ))
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]; omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      omega
    · intro n _; simp
    · intro j _; rfl
  have hneg : ∑ j ∈ ((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun j => j ≠ 0)).filter (fun j : ℤ => ¬ 0 < j), h j.natAbs
      = ∑ n ∈ Finset.Icc 1 M, h n := by
    apply Finset.sum_nbij' (fun j : ℤ => j.natAbs) (fun n : ℕ => -(n : ℤ))
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]; omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      omega
    · intro n _; simp
    · intro j _; rfl
  rw [hpos, hneg]; ring

theorem gX_le (X : ℝ) (hX : 0 ≤ X) (n : ℕ) (hn : 1 ≤ n) :
    gX X n ≤ 25 * Real.sqrt X * ((n.divisors.card : ℝ) / Real.sqrt n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  unfold gX
  split_ifs with h
  · have ht : 1 ≤ X / n := by rw [le_div_iff₀ hnR]; linarith
    have h1 := one_add_log_sq_le (X / n) ht
    rw [Real.sqrt_div' _ hnR.le] at h1
    have hτ : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
    calc (n.divisors.card : ℝ) * (1 + Real.log (X / n)) ^ 2
        ≤ (n.divisors.card : ℝ) * (25 * (Real.sqrt X / Real.sqrt n)) := mul_le_mul_of_nonneg_left h1 hτ
      _ = 25 * Real.sqrt X * ((n.divisors.card : ℝ) / Real.sqrt n) := by ring
  · positivity

theorem s3_arith_jsum_pf : ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℝ), 0 ≤ X →
    ∑ j ∈ lineSet (⌊X⌋₊ + 1), gX X j.natAbs ≤ C * ((X + 1) * (1 + Real.log (X + 1))) := by
  refine ⟨100, by norm_num, ?_⟩
  intro X hX
  set M := ⌊X⌋₊ + 1 with hM
  rw [lineSet_sum_abs M (gX X)]
  have hMX : (M : ℝ) ≤ X + 1 := by
    rw [hM]; push_cast; linarith [Nat.floor_le hX]
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [(Nat.cast_nonneg ⌊X⌋₊ : (0 : ℝ) ≤ ⌊X⌋₊)]
  have h1 : ∑ n ∈ Finset.Icc 1 M, gX X n ≤ 25 * Real.sqrt X * (2 * Real.sqrt M * (1 + Real.log M)) := by
    calc ∑ n ∈ Finset.Icc 1 M, gX X n
        ≤ ∑ n ∈ Finset.Icc 1 M, 25 * Real.sqrt X * ((n.divisors.card : ℝ) / Real.sqrt n) :=
          Finset.sum_le_sum (fun n hn => gX_le X hX n (Finset.mem_Icc.mp hn).1)
      _ = 25 * Real.sqrt X * ∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) / Real.sqrt n := by
          rw [Finset.mul_sum]
      _ ≤ 25 * Real.sqrt X * (2 * Real.sqrt M * (1 + Real.log M)) :=
          mul_le_mul_of_nonneg_left (sum_tau_inv_sqrt_le M) (by positivity)
  have hsX : Real.sqrt X ≤ Real.sqrt (X + 1) := Real.sqrt_le_sqrt (by linarith)
  have hsM : Real.sqrt M ≤ Real.sqrt (X + 1) := Real.sqrt_le_sqrt hMX
  have hss : Real.sqrt (X + 1) * Real.sqrt (X + 1) = X + 1 := Real.mul_self_sqrt (by linarith)
  have hlog : Real.log M ≤ Real.log (X + 1) := Real.log_le_log (by linarith) hMX
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hprod : Real.sqrt X * Real.sqrt M ≤ X + 1 := by
    rw [← hss]
    exact mul_le_mul hsX hsM (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 : 25 * Real.sqrt X * (2 * Real.sqrt M * (1 + Real.log M))
      ≤ 50 * ((X + 1) * (1 + Real.log (X + 1))) := by
    have e : 25 * Real.sqrt X * (2 * Real.sqrt M * (1 + Real.log M))
        = 50 * ((Real.sqrt X * Real.sqrt M) * (1 + Real.log M)) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul hprod (by linarith) (by linarith) (by linarith)
  linarith

end TrackF
end ZetaShell
