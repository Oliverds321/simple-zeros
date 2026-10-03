/-
L7_9 helper for node K5 (`small_primes_l2`): the tail of `Σ Λ(n)²/n` over proper prime powers.
`Σ_{y < n ≤ X, n = p^k, k ≥ 2} Λ(n)²/n ≤ C₂ y^{−1/4}` with `C₂` independent of `X` and `y`:
`1/n ≤ y^{−1/4} n^{−3/4}`, `n = p^k ↦ (p, k)`, `Σ_{k ≥ 2} p^{−3k/4} ≤ p^{−3/2}/(1 − 2^{−3/4})`,
`(log p)² ≤ 64 p^{1/4}`, and `Σ_m m^{−5/4} < ∞`.
-/
import Mathlib

noncomputable section
open Finset

namespace ZetaShell
namespace LemmaK
namespace K5Aux

/-- the proper prime powers `p^k`, `k ≥ 2`, in `(0, X]`. -/
def ppp (X : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 X).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)

lemma ppp_subset_image (X : ℕ) :
    ppp X ⊆ ((((Finset.Icc 1 X).filter Nat.Prime) ×ˢ Finset.Icc 2 X)).image
      (fun pk : ℕ × ℕ => pk.1 ^ pk.2) := by
  intro n hn
  simp only [ppp, mem_filter, mem_Ioc] at hn
  obtain ⟨⟨hn0, hnX⟩, hpp, hnp⟩ := hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  rw [mem_image]
  refine ⟨(p, k), ?_, rfl⟩
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · have : k = 1 := by omega
      subst this
      exact absurd (by simpa using hp) hnp
    · exact h
  have hple : p ≤ p ^ k := Nat.le_self_pow (by omega) p
  have hkle : k ≤ p ^ k := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
    omega
  simp only [mem_product, mem_filter, mem_Icc]
  exact ⟨⟨⟨hp.one_lt.le, hple.trans hnX⟩, hp⟩, hk2, hkle.trans hnX⟩

lemma log_sq_le (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 64 * x ^ (1 / 4 : ℝ) := by
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (by norm_num : (0 : ℝ) < 1 / 8)
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h8 : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
    have : x ^ (1 / 8 : ℝ) / (1 / 8) = 8 * x ^ (1 / 8 : ℝ) := by ring
    linarith
  have hsq : Real.log x ^ 2 ≤ (8 * x ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hl h8 2
  have e : (8 * x ^ (1 / 8 : ℝ)) ^ 2 = 64 * x ^ (1 / 4 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul (by linarith)]
    norm_num
  linarith

/-- the per-prime bound `(log p)² Σ_{k ∈ [2, X]} p^{−3k/4} ≤ c₀·64·p^{−5/4}`. -/
lemma per_prime (p X : ℕ) (hp : 2 ≤ p) :
    Real.log p ^ 2 * ∑ k ∈ Finset.Icc 2 X, ((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ k
      ≤ (64 * (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹) * (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set x : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by norm_num)
  have h2lt : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hx1 : x < 1 := lt_of_le_of_lt hx2 h2lt
  have hgeom : ∑ k ∈ Finset.Icc 2 X, x ^ k ≤ x ^ 2 / (1 - x) := by
    have : Finset.Icc 2 X = Finset.Ico 2 (X + 1) := by
      ext k; simp only [mem_Icc, mem_Ico]; omega
    rw [this]
    exact geom_sum_Ico_le_of_lt_one hx0 hx1
  have hden : (1 - x)⁻¹ ≤ (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹ := by
    apply inv_anti₀ (by linarith) (by linarith)
  have hx2eq : x ^ 2 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  have hlog := log_sq_le (p : ℝ) (by linarith)
  have hl0 : 0 ≤ Real.log p ^ 2 := sq_nonneg _
  have hcomb : (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) = (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hp0]
    norm_num
  calc Real.log p ^ 2 * ∑ k ∈ Finset.Icc 2 X, x ^ k
      ≤ Real.log p ^ 2 * (x ^ 2 / (1 - x)) := mul_le_mul_of_nonneg_left hgeom hl0
    _ = Real.log p ^ 2 * x ^ 2 * (1 - x)⁻¹ := by ring
    _ ≤ (64 * (p : ℝ) ^ (1 / 4 : ℝ)) * x ^ 2 * (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹ := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hlog (sq_nonneg _)) hden
          (inv_nonneg.2 (by linarith)) (by positivity)
    _ = (64 * (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹) * ((p : ℝ) ^ (1 / 4 : ℝ) * x ^ 2) := by ring
    _ = (64 * (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹) * (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
        rw [hx2eq, hcomb]

/-- the constant `C₂ = 64 c₀ Σ_m m^{−5/4}`. -/
def C2 : ℝ := (64 * (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹) * ∑' m : ℕ, (m : ℝ) ^ (-(5 / 4 : ℝ))

lemma C2_nonneg : 0 ≤ C2 := by
  have h2lt : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  unfold C2
  apply mul_nonneg
  · apply mul_nonneg (by norm_num) (inv_nonneg.2 (by linarith))
  · exact tsum_nonneg fun m => by positivity

/-- `Σ_{n ∈ ppp X} Λ(n)² n^{−3/4} ≤ C₂`. -/
lemma sum_ppp_le (X : ℕ) :
    ∑ n ∈ ppp X, ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ)) ≤ C2 := by
  classical
  set P := (Finset.Icc 1 X).filter Nat.Prime with hP
  have hnn : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ)) :=
    fun n => by positivity
  calc ∑ n ∈ ppp X, ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ))
      ≤ ∑ n ∈ (P ×ˢ Finset.Icc 2 X).image (fun pk : ℕ × ℕ => pk.1 ^ pk.2),
          ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (ppp_subset_image X) (fun n _ _ => hnn n)
    _ ≤ ∑ pk ∈ P ×ˢ Finset.Icc 2 X, ArithmeticFunction.vonMangoldt (pk.1 ^ pk.2) ^ 2
          * ((pk.1 ^ pk.2 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
        sum_image_le_of_nonneg (fun n _ => hnn n)
    _ = ∑ p ∈ P, Real.log p ^ 2 * ∑ k ∈ Finset.Icc 2 X, ((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
        rw [sum_product]
        refine sum_congr rfl fun p hp => ?_
        rw [hP, mem_filter] at hp
        rw [mul_sum]
        refine sum_congr rfl fun k hk => ?_
        rw [mem_Icc] at hk
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
          ArithmeticFunction.vonMangoldt_apply_prime hp.2]
        congr 1
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
          ← Real.rpow_mul (Nat.cast_nonneg _)]
        ring_nf
    _ ≤ ∑ p ∈ P, (64 * (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹) * (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
        refine sum_le_sum fun p hp => ?_
        rw [hP, mem_filter] at hp
        exact per_prime p X hp.2.two_le
    _ = (64 * (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))⁻¹) * ∑ p ∈ P, (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
        rw [mul_sum]
    _ ≤ C2 := by
        unfold C2
        have h2lt : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (inv_nonneg.2 (by linarith)))
        exact (Real.summable_nat_rpow.mpr (by norm_num)).sum_le_tsum P (fun m _ => by positivity)

/-- **The tail bound.** `Σ_{n ∈ ppp X, y < n} Λ(n)²/n ≤ C₂ y^{−1/4}` for `y > 0`. -/
theorem tail_ppp (X : ℕ) (y : ℝ) (hy : 0 < y) :
    ∑ n ∈ (ppp X).filter (fun n : ℕ => y < (n : ℝ)),
        ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ)
      ≤ C2 * y ^ (-(1 / 4 : ℝ)) := by
  classical
  have hpt : ∀ n ∈ (ppp X).filter (fun n : ℕ => y < (n : ℝ)),
      ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ)
        ≤ y ^ (-(1 / 4 : ℝ)) * (ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ))) := by
    intro n hn
    rw [mem_filter] at hn
    have hyn : y < n := hn.2
    have hn0 : (0 : ℝ) < n := by linarith
    have h1 : (n : ℝ)⁻¹ = (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_add hn0]
      norm_num
      exact (Real.rpow_neg_one _).symm
    have h2 : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ y ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hy hyn.le (by norm_num)
    rw [div_eq_mul_inv, h1]
    have h3 : 0 ≤ ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by positivity
    calc ArithmeticFunction.vonMangoldt n ^ 2 * ((n : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-(3 / 4 : ℝ)))
        = (n : ℝ) ^ (-(1 / 4 : ℝ)) * (ArithmeticFunction.vonMangoldt n ^ 2
            * (n : ℝ) ^ (-(3 / 4 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 h3
  calc ∑ n ∈ (ppp X).filter (fun n : ℕ => y < (n : ℝ)), ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ)
      ≤ ∑ n ∈ (ppp X).filter (fun n : ℕ => y < (n : ℝ)),
          y ^ (-(1 / 4 : ℝ)) * (ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ))) :=
        sum_le_sum hpt
    _ = y ^ (-(1 / 4 : ℝ)) * ∑ n ∈ (ppp X).filter (fun n : ℕ => y < (n : ℝ)),
          ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by rw [mul_sum]
    _ ≤ y ^ (-(1 / 4 : ℝ)) * ∑ n ∈ ppp X,
          ArithmeticFunction.vonMangoldt n ^ 2 * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => by positivity)
    _ ≤ y ^ (-(1 / 4 : ℝ)) * C2 := mul_le_mul_of_nonneg_left (sum_ppp_le X) (by positivity)
    _ = C2 * y ^ (-(1 / 4 : ℝ)) := by ring

end K5Aux
end LemmaK
end ZetaShell
