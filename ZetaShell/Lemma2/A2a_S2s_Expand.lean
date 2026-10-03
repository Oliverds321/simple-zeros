/-
A2a_S2s_Expand (L7_8, round 3): Möbius expansion of the coprimality condition in `lineCount`:
`1[(k,j) = 1] = Σ_{g | |j|} μ(g) 1[g | k]`. PROVED (sorry-free), from Mathlib's `μ * ζ = 1`.
-/
import ZetaShell.Lemma2.A2a_S2s_Defs

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem mu_divisor_sum (m : ℕ) :
    ∑ i ∈ m.divisors, (ArithmeticFunction.moebius i : ℤ) = if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

theorem divisors_filter_dvd (n : ℕ) (hn : n ≠ 0) (k : ℤ) :
    n.divisors.filter (fun g : ℕ => (g : ℤ) ∣ k) = (Nat.gcd k.natAbs n).divisors := by
  ext g
  simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd]
  constructor
  · rintro ⟨⟨hgn, _⟩, hgk⟩
    exact ⟨Nat.dvd_gcd hgk hgn, Nat.gcd_ne_zero_right hn⟩
  · rintro ⟨hg, _⟩
    exact ⟨⟨dvd_trans hg (Nat.gcd_dvd_right _ _), hn⟩, dvd_trans hg (Nat.gcd_dvd_left _ _)⟩

theorem s2_expand (F : Fam) (Q : ℕ) (r r' j : ℤ) (e f : ℕ) (lo hi : ℝ) (hj : j ≠ 0) :
    lineCount F Q r r' j e f lo hi
      = ∑ g ∈ j.natAbs.divisors, ((ArithmeticFunction.moebius g : ℤ) : ℝ) * Pg F Q r r' j e f g lo hi := by
  classical
  unfold lineCount Pg
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hn : j.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hj
  by_cases hfq : (f : ℤ) ∣ r * k - r' * j
  · have e1 : ∀ g ∈ j.natAbs.divisors,
        ((ArithmeticFunction.moebius g : ℤ) : ℝ) *
          (if (g : ℤ) ∣ k ∧ (f : ℤ) ∣ r * k - r' * j then F.w (((r * k - r' * j : ℤ) : ℝ) * e / Q) else 0)
        = (if (g : ℤ) ∣ k then ((ArithmeticFunction.moebius g : ℤ) : ℝ) else 0) *
            F.w (((r * k - r' * j : ℤ) : ℝ) * e / Q) := by
      intro g _
      by_cases hgk : (g : ℤ) ∣ k <;> simp [hgk, hfq]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_mul, ← Finset.sum_filter, divisors_filter_dvd _ hn k]
    have hsum : ∑ i ∈ (Nat.gcd k.natAbs j.natAbs).divisors, ((ArithmeticFunction.moebius i : ℤ) : ℝ)
        = if Nat.gcd k.natAbs j.natAbs = 1 then 1 else 0 := by
      have := mu_divisor_sum (Nat.gcd k.natAbs j.natAbs)
      have h2 : ((∑ i ∈ (Nat.gcd k.natAbs j.natAbs).divisors, (ArithmeticFunction.moebius i : ℤ) : ℤ) : ℝ)
          = ((if Nat.gcd k.natAbs j.natAbs = 1 then 1 else 0 : ℤ) : ℝ) := by rw [this]
      push_cast at h2
      rw [h2]
    rw [hsum]
    have hg : Int.gcd k j = Nat.gcd k.natAbs j.natAbs := rfl
    by_cases hc : Nat.gcd k.natAbs j.natAbs = 1
    · rw [if_pos hc, if_pos ⟨by rw [hg]; exact hc, hfq⟩, one_mul]
    · rw [if_neg hc, if_neg (fun h => hc (by rw [← hg]; exact h.1)), zero_mul]
  · rw [if_neg (fun h => hfq h.2)]
    symm
    apply Finset.sum_eq_zero
    intro g _
    rw [if_neg (fun h => hfq h.2), mul_zero]

end TrackF
end ZetaShell
