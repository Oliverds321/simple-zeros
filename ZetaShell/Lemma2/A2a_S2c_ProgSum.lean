/-
A2a_S2c_ProgSum (L7_8, round 4): sum over an arithmetic progression versus the integral, for a function that is
antitone on `[A, B]` with values in `[0, 1]`:
`|Σ_{i : A ≤ c + hi ≤ B} φ(c + hi) − (1/h)∫_A^B φ| ≤ 2`  (`prog_antitone`).
Used for `s2_class` (all three `w` are antitone on their support interval, with values in `[0,1]`).
-/
import Mathlib

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace TrackF

theorem integral_bounds01 (φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hint : IntervalIntegrable φ volume a b)
    (h0 : ∀ x ∈ Set.Icc a b, 0 ≤ φ x) (h1 : ∀ x ∈ Set.Icc a b, φ x ≤ 1) :
    0 ≤ ∫ x in a..b, φ x ∧ ∫ x in a..b, φ x ≤ b - a := by
  refine ⟨intervalIntegral.integral_nonneg hab h0, ?_⟩
  have := intervalIntegral.integral_mono_on hab hint (intervalIntegrable_const) h1
  simpa using this

theorem sum_Icc_int_eq_range (g : ℤ → ℝ) (i1 i2 : ℤ) (h : i1 ≤ i2) :
    ∑ i ∈ Finset.Icc i1 i2, g i = ∑ t ∈ Finset.range ((i2 - i1).toNat + 1), g (i1 + t) := by
  apply Finset.sum_nbij' (fun i => (i - i1).toNat) (fun t => i1 + (t : ℤ))
  · intro i hi
    rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
  · intro t ht
    rw [Finset.mem_range] at ht; rw [Finset.mem_Icc]; omega
  · intro i hi
    rw [Finset.mem_Icc] at hi; omega
  · intro t _; simp
  · intro i hi
    rw [Finset.mem_Icc] at hi
    congr 1
    omega

theorem prog_antitone (φ : ℝ → ℝ) (A B c h : ℝ) (hh : 0 < h) (hAB : A ≤ B)
    (hanti : AntitoneOn φ (Set.Icc A B)) (h0 : ∀ x ∈ Set.Icc A B, 0 ≤ φ x)
    (h1 : ∀ x ∈ Set.Icc A B, φ x ≤ 1) :
    |∑ i ∈ Finset.Icc ⌈(A - c) / h⌉ ⌊(B - c) / h⌋, φ (c + h * i) - (1 / h) * ∫ x in A..B, φ x| ≤ 2 := by
  set i1 := ⌈(A - c) / h⌉ with hi1
  set i2 := ⌊(B - c) / h⌋ with hi2
  have hint : IntervalIntegrable φ volume A B := by
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hAB]; exact hanti
  have hA1 : (A - c) / h ≤ i1 := Int.le_ceil _
  have hA2 : (i1 : ℝ) < (A - c) / h + 1 := Int.ceil_lt_add_one _
  have hB1 : (i2 : ℝ) ≤ (B - c) / h := Int.floor_le _
  have hB2 : (B - c) / h < i2 + 1 := Int.lt_floor_add_one _
  rcases lt_or_ge i2 i1 with hlt | hle
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, zero_sub, abs_neg]
    obtain ⟨hI0, hI1⟩ := integral_bounds01 φ A B hAB hint h0 h1
    have hlt' : (i2 : ℝ) + 1 ≤ i1 := by exact_mod_cast hlt
    have hBA : B - A < h := by
      have : (B - c) / h < (A - c) / h + 1 := by linarith
      rw [div_lt_iff₀ hh, add_mul, div_mul_cancel₀ _ hh.ne'] at this
      linarith
    rw [abs_of_nonneg (by positivity)]
    have : (1 / h) * ∫ x in A..B, φ x ≤ (1 / h) * (B - A) := mul_le_mul_of_nonneg_left hI1 (by positivity)
    have : (1 / h) * (B - A) ≤ 1 := by rw [one_div_mul_eq_div, div_le_one hh]; linarith
    linarith
  · -- points x1 = c + h i1 ≤ ... ≤ xN = c + h i2 in [A, B]
    set n : ℕ := (i2 - i1).toNat with hn
    have hn' : ((n : ℤ)) = i2 - i1 := Int.toNat_of_nonneg (by omega)
    have hnR : (n : ℝ) = (i2 : ℝ) - i1 := by exact_mod_cast hn'
    set x1 := c + h * i1 with hx1
    set xN := c + h * i2 with hxN
    have hAx1 : A ≤ x1 := by
      have := mul_le_mul_of_nonneg_left hA1 hh.le
      rw [mul_div_cancel₀ _ hh.ne'] at this; rw [hx1]; linarith
    have hx1A : x1 - A < h := by
      have := mul_lt_mul_of_pos_left hA2 hh
      rw [mul_add, mul_div_cancel₀ _ hh.ne'] at this; rw [hx1]; linarith
    have hxNB : xN ≤ B := by
      have := mul_le_mul_of_nonneg_left hB1 hh.le
      rw [mul_div_cancel₀ _ hh.ne'] at this; rw [hxN]; linarith
    have hBxN : B - xN < h := by
      have := mul_lt_mul_of_pos_left hB2 hh
      rw [mul_add, mul_div_cancel₀ _ hh.ne'] at this; rw [hxN]; linarith
    have hx1N : x1 ≤ xN := by
      have : (i1 : ℝ) ≤ i2 := by exact_mod_cast hle
      rw [hx1, hxN]; nlinarith
    have hxN' : xN = h * n + x1 := by rw [hxN, hx1, hnR]; ring
    -- split the integral
    have hint1 : IntervalIntegrable φ volume A x1 := hint.mono_set (by
      rw [Set.uIcc_of_le hAx1, Set.uIcc_of_le hAB]; exact Set.Icc_subset_Icc le_rfl (by linarith))
    have hint2 : IntervalIntegrable φ volume x1 xN := hint.mono_set (by
      rw [Set.uIcc_of_le hx1N, Set.uIcc_of_le hAB]; exact Set.Icc_subset_Icc hAx1 hxNB)
    have hint3 : IntervalIntegrable φ volume xN B := hint.mono_set (by
      rw [Set.uIcc_of_le hxNB, Set.uIcc_of_le hAB]; exact Set.Icc_subset_Icc (by linarith) le_rfl)
    have hsplit : ∫ x in A..B, φ x = (∫ x in A..x1, φ x) + (∫ x in x1..xN, φ x) + ∫ x in xN..B, φ x := by
      rw [intervalIntegral.integral_add_adjacent_intervals hint1 hint2,
        intervalIntegral.integral_add_adjacent_intervals (hint1.trans hint2) hint3]
    have hE1 := integral_bounds01 φ A x1 hAx1 hint1 (fun x hx => h0 x ⟨hx.1, by linarith [hx.2]⟩)
      (fun x hx => h1 x ⟨hx.1, by linarith [hx.2]⟩)
    have hE2 := integral_bounds01 φ xN B hxNB hint3 (fun x hx => h0 x ⟨by linarith [hx.1], hx.2⟩)
      (fun x hx => h1 x ⟨by linarith [hx.1], hx.2⟩)
    -- the middle part, rescaled
    set ψ : ℝ → ℝ := fun t => φ (h * t + x1) with hψ
    have hmid : ∫ x in x1..xN, φ x = h * ∫ t in (0 : ℝ)..(0 + (n : ℝ)), ψ t := by
      have := intervalIntegral.integral_comp_mul_add (f := φ) (a := 0) (b := (n : ℝ)) hh.ne' x1
      simp only [mul_zero, zero_add] at this
      rw [zero_add, hψ, this, smul_eq_mul, ← hxN', ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    have hψanti : AntitoneOn ψ (Set.Icc 0 (0 + (n : ℝ))) := by
      intro s hs t ht hst
      apply hanti
      · constructor
        · have := hs.1; nlinarith
        · have := hs.2; rw [zero_add] at this; nlinarith [hxN']
      · constructor
        · have := ht.1; nlinarith
        · have := ht.2; rw [zero_add] at this; nlinarith [hxN']
      · nlinarith
    have hup := AntitoneOn.integral_le_sum hψanti
    have hlo := AntitoneOn.sum_le_integral hψanti
    -- the full sum as a range sum
    have hsum : ∑ i ∈ Finset.Icc i1 i2, φ (c + h * i) = ∑ t ∈ Finset.range (n + 1), ψ t := by
      rw [sum_Icc_int_eq_range _ i1 i2 hle, ← hn]
      apply Finset.sum_congr rfl
      intro t _
      simp only [hψ, hx1]
      congr 1
      push_cast; ring
    have hψ01 : ∀ t : ℕ, t ≤ n → 0 ≤ ψ t ∧ ψ t ≤ 1 := by
      intro t ht
      have htR : (t : ℝ) ≤ n := by exact_mod_cast ht
      have hmem : h * (t : ℝ) + x1 ∈ Set.Icc A B := by
        constructor
        · have : 0 ≤ h * (t : ℝ) := by positivity
          linarith
        · have : h * (t : ℝ) ≤ h * n := mul_le_mul_of_nonneg_left htR hh.le
          linarith [hxN']
      exact ⟨h0 _ hmem, h1 _ hmem⟩
    have hS1 : ∑ t ∈ Finset.range (n + 1), ψ t = ∑ i ∈ Finset.range n, ψ (0 + (i : ℝ)) + ψ n := by
      rw [Finset.sum_range_succ]; simp
    have hS2 : ∑ t ∈ Finset.range (n + 1), ψ t = ∑ i ∈ Finset.range n, ψ (0 + ((i + 1 : ℕ) : ℝ)) + ψ 0 := by
      rw [Finset.sum_range_succ']; simp
    have hψn := hψ01 n le_rfl
    have hψ0 := hψ01 0 (Nat.zero_le _)
    rw [hsum, hsplit, hmid]
    have hh1 : (1 / h) * ((∫ x in A..x1, φ x) + h * (∫ t in (0 : ℝ)..(0 + (n : ℝ)), ψ t) + ∫ x in xN..B, φ x)
        = (1 / h) * (∫ x in A..x1, φ x) + (∫ t in (0 : ℝ)..(0 + (n : ℝ)), ψ t) + (1 / h) * ∫ x in xN..B, φ x := by
      field_simp
    rw [hh1]
    have e1 : (1 / h) * (∫ x in A..x1, φ x) ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hh]; linarith [hE1.2]
    have e1' : 0 ≤ (1 / h) * (∫ x in A..x1, φ x) := by have := hE1.1; positivity
    have e2 : (1 / h) * (∫ x in xN..B, φ x) ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hh]; linarith [hE2.2]
    have e2' : 0 ≤ (1 / h) * (∫ x in xN..B, φ x) := by have := hE2.1; positivity
    simp only [Nat.cast_zero] at hψ0
    rw [abs_le]
    constructor <;> linarith [hup, hlo, hS1, hS2, hψn.1, hψn.2, hψ0.1, hψ0.2]

end TrackF
end ZetaShell
