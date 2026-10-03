/-
L7_9 round 3: helpers for (c3) `E_bound`: the decomposition `E(m) = (ψ(m) − m) − D(m)` and the truncation bound
`0 ≤ D(m) = Σ_{j≤m, j=p^k, p≤R} Λ(j) ≤ R·⌊log₂ m⌋·B` (`B ≥ log p` for `p ≤ R`).
-/
import ZetaShell.LemmaK.LK9_K6c_Helpers

noncomputable section
open Finset

namespace ZetaShell
namespace LemmaK
namespace K6

/-- the truncated part `D(m) = Σ_{0<j≤m} (Λ(j) − Λ′(j))`. -/
def truncD (R : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc 0 m, (ArithmeticFunction.vonMangoldt j - lamP R j)

lemma psum_lamP_eq (R : ℝ) (m : ℕ) :
    psum m (fun j => ((lamP R j - 1 : ℝ) : ℂ))
      = (((∑ j ∈ Finset.Ioc 0 m, ArithmeticFunction.vonMangoldt j) - m - truncD R m : ℝ) : ℂ) := by
  unfold psum truncD
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul,
    mul_one, Nat.sub_zero]
  ring

lemma truncD_term_nonneg (R : ℝ) (j : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt j - lamP R j := by
  unfold lamP; split_ifs
  · simp
  · simp only [sub_zero]; exact ArithmeticFunction.vonMangoldt_nonneg

lemma truncD_nonneg (R : ℝ) (m : ℕ) : 0 ≤ truncD R m :=
  Finset.sum_nonneg fun j _ => truncD_term_nonneg R j

lemma truncD_le (R B : ℝ) (m : ℕ) (hR : 0 ≤ R) (hB0 : 0 ≤ B)
    (hB : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ R → Real.log p ≤ B) :
    truncD R m ≤ R * (Nat.log 2 m : ℝ) * B := by
  classical
  set P := (Finset.Icc 1 ⌊R⌋₊).filter Nat.Prime with hP
  set K := Nat.log 2 m with hK
  set S := (Finset.Ioc 0 m).filter (fun j => IsPrimePow j ∧ ¬ (R < (j.minFac : ℝ))) with hS
  -- only `S` contributes
  have h1 : truncD R m = ∑ j ∈ S, ArithmeticFunction.vonMangoldt j := by
    unfold truncD
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold lamP
    by_cases hpp : IsPrimePow j
    · by_cases hR' : R < (j.minFac : ℝ)
      · rw [if_pos ⟨hpp, hR'⟩, if_neg (fun h => h.2 hR')]; ring
      · rw [if_neg (fun h => hR' h.2), if_pos ⟨hpp, hR'⟩]; ring
    · rw [if_neg (fun h => hpp h.1), if_neg (fun h => hpp h.1), sub_zero,
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  have hsub : S ⊆ (P ×ˢ Finset.Icc 1 K).image (fun pk : ℕ × ℕ => pk.1 ^ pk.2) := by
    intro j hj
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hj
    obtain ⟨⟨hj0, hjm⟩, hpp, hR'⟩ := hj
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    rw [Finset.mem_image]
    refine ⟨(p, k), ?_, rfl⟩
    rw [Nat.Prime.pow_minFac hp hk.ne', not_lt] at hR'
    simp only [Finset.mem_product, hP, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨hp.one_lt.le, Nat.le_floor hR'⟩, hp⟩, hk, ?_⟩
    apply Nat.le_log_of_pow_le one_lt_two
    exact (Nat.pow_le_pow_left hp.two_le k).trans hjm
  have hnn : ∀ j, 0 ≤ ArithmeticFunction.vonMangoldt j := fun j => ArithmeticFunction.vonMangoldt_nonneg
  rw [h1]
  calc ∑ j ∈ S, ArithmeticFunction.vonMangoldt j
      ≤ ∑ j ∈ (P ×ˢ Finset.Icc 1 K).image (fun pk : ℕ × ℕ => pk.1 ^ pk.2),
          ArithmeticFunction.vonMangoldt j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnn j)
    _ ≤ ∑ pk ∈ P ×ˢ Finset.Icc 1 K, ArithmeticFunction.vonMangoldt (pk.1 ^ pk.2) :=
        Finset.sum_image_le_of_nonneg (fun j _ => hnn j)
    _ ≤ ∑ pk ∈ P ×ˢ Finset.Icc 1 K, B := by
        refine Finset.sum_le_sum fun pk hpk => ?_
        simp only [Finset.mem_product, hP, Finset.mem_filter, Finset.mem_Icc] at hpk
        obtain ⟨⟨⟨_, hpR⟩, hp⟩, hk1, _⟩ := hpk
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
        exact hB pk.1 hp ((Nat.le_floor_iff hR).mp hpR)
    _ = (P.card : ℝ) * K * B := by
        rw [Finset.sum_const, Finset.card_product, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ ≤ R * K * B := by
        have hPc : (P.card : ℝ) ≤ R := by
          have h1 : P.card ≤ ⌊R⌋₊ := (Finset.card_filter_le _ _).trans (by simp)
          exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hR)
        have := mul_le_mul_of_nonneg_right hPc (by positivity : (0 : ℝ) ≤ (K : ℝ))
        exact mul_le_mul_of_nonneg_right this hB0

lemma nat_log_two_le (m : ℕ) (hm : 1 ≤ m) : (Nat.log 2 m : ℝ) ≤ 2 * Real.log m := by
  have h := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
  have hR : ((2 : ℝ) ^ (Nat.log 2 m)) ≤ m := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) hR
  rw [Real.log_pow] at hl
  have h2 := Real.log_two_gt_d9
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ m by exact_mod_cast hm)]

end K6
end LemmaK
end ZetaShell
