/-
A2a_S3d_InnerProof (L7_8, round 4): `s3_arith_inner` (as `s3_arith_inner_pf`, same statement) derived from the proved
`two_pow_omega_le_tau`, `lam_sum_le` (A2a_S3d_InnerAux) and the sub-node `ce_tau_le`, derived by kind from `ce_tau_le_plain` (proved) and `ce_tau_le_qphi` (open,
A2a_S3d_CeTau):
* `ce_tau_le`: `Σ_{1≤e≤y} |c_e| τ(e) ≤ C(1 + log y)²` for `y ≥ 1`
  (plain: `|c_e| ≤ 1/e`, `Σ τ(e)/e = Σ_{dm≤y} 1/(dm) ≤ (1 + log y)²`; `q/φ`: `μ²(e) e/φ(e) = Σ_{d|e} μ²(d)/φ(d)`,
  `τ(dm) ≤ τ(d)τ(m)`, `Σ_d μ²(d)τ(d)/(dφ(d)) < ∞`).
-/
import ZetaShell.Skeleton.A2a_S3d_ArithSplit
import ZetaShell.Lemma2.A2a_S3d_InnerAux
import ZetaShell.Skeleton.A2a_S3d_CeTau

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem ce_tau_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : FKind) (y : ℝ), 1 ≤ y →
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |cE k e| * (e.divisors.card : ℝ) ≤ C * (1 + Real.log y) ^ 2 := by
  obtain ⟨Cq, hCq, hq⟩ := ce_tau_le_qphi
  refine ⟨max 1 Cq, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro k y hy
  have hl : 0 ≤ (1 + Real.log y) ^ 2 := sq_nonneg _
  cases k
  · exact le_trans (ce_tau_le_plain y hy) (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)
  · exact le_trans (hq y hy) (mul_le_mul_of_nonneg_right (le_max_right _ _) hl)

theorem s3_arith_inner_pf : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : FKind) (Q : ℕ) (X : ℝ) (j : ℤ), 2 ≤ Q → 0 ≤ X → j ≠ 0 →
    (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) *
      ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
        |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
      ≤ C * ((1 + Real.log Q) * gX X j.natAbs) := by
  obtain ⟨C, hC, h⟩ := ce_tau_le
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
    unfold gX
    rw [if_pos hnX]
    have hsum2_nn : 0 ≤ ∑ e ∈ Finset.Icc 1 ⌊X / n⌋₊, |cE k e| * (e.divisors.card : ℝ) :=
      Finset.sum_nonneg (fun e _ => by positivity)
    calc (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) *
          ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
            |cE k e| * ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
        ≤ (n.divisors.card : ℝ) * ((1 + Real.log Q) *
            ∑ e ∈ Finset.Icc 1 ⌊X / n⌋₊, |cE k e| * (e.divisors.card : ℝ)) :=
          mul_le_mul hτ hstep1 hsum_nn (by positivity)
      _ ≤ (n.divisors.card : ℝ) * ((1 + Real.log Q) * (C * (1 + Real.log (X / n)) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hstep2 hlQ
      _ = C * ((1 + Real.log Q) * ((n.divisors.card : ℝ) * (1 + Real.log (X / n)) ^ 2)) := by ring
  · have hempty : (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he hle
      have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (Finset.mem_Icc.mp he).1
      rw [habs] at hle
      have : (n : ℝ) ≤ (e : ℝ) * n := by nlinarith
      exact hnX (by linarith)
    rw [hempty, Finset.sum_empty, mul_zero]
    unfold gX
    rw [if_neg hnX]
    simp

end TrackF
end ZetaShell
