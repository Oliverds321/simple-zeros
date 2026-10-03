/-
A2a_S2c_ProgGeneral (L7_8, round 4): the progression-sum comparison for a weight `W` that vanishes outside `[a, b]`,
equals an antitone `φ` (values in `[0,1]`) on `(a, b)`, and has values in `[0,1]` (covers `w(qe/Q)` for the three
families, including the dyadic half-open end):
`|Σ_{i : lo ≤ c + hi ≤ hi} W(c + h i) − (1/h)∫_{lo}^{hi} W| ≤ 4`  (`prog_general`).
-/
import ZetaShell.Lemma2.A2a_S2c_ProgSum

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace TrackF

theorem card_prog_eq_le_one (S : Finset ℤ) (c h a : ℝ) (hh : 0 < h) :
    (S.filter (fun i : ℤ => c + h * i = a)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have h1 := (Finset.mem_filter.mp hi).2
  have h2 := (Finset.mem_filter.mp hj).2
  have : h * (i : ℝ) = h * j := by linarith
  have : (i : ℝ) = j := mul_left_cancel₀ hh.ne' this
  exact_mod_cast this

theorem prog_general (W φ : ℝ → ℝ) (a b lo hi c h : ℝ) (hh : 0 < h) (hab : a ≤ b) (hlh : lo ≤ hi)
    (hanti : AntitoneOn φ (Set.Icc a b)) (hφ0 : ∀ x ∈ Set.Icc a b, 0 ≤ φ x)
    (hφ1 : ∀ x ∈ Set.Icc a b, φ x ≤ 1) (hWin : ∀ x ∈ Set.Ioo a b, W x = φ x)
    (hWout : ∀ x, x < a ∨ b < x → W x = 0) (hW0 : ∀ x, 0 ≤ W x) (hW1 : ∀ x, W x ≤ 1) :
    |∑ i ∈ Finset.Icc ⌈(lo - c) / h⌉ ⌊(hi - c) / h⌋, W (c + h * i) - (1 / h) * ∫ x in lo..hi, W x| ≤ 4 := by
  classical
  set A := max lo a with hA
  set B := min hi b with hB
  -- membership of a progression point in the index ranges
  have hmemI : ∀ (u v : ℝ) (i : ℤ), i ∈ Finset.Icc ⌈(u - c) / h⌉ ⌊(v - c) / h⌋ ↔ u ≤ c + h * i ∧ c + h * i ≤ v := by
    intro u v i
    rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hh, le_div_iff₀ hh]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
  rcases lt_or_ge B A with hBA | hAB
  · -- no overlap: W = 0 on [lo, hi]
    have hzero : ∀ x, lo ≤ x → x ≤ hi → W x = 0 := by
      intro x h1 h2
      apply hWout
      by_contra hcon
      push_neg at hcon
      have : A ≤ x := max_le h1 hcon.1
      have : x ≤ B := le_min h2 hcon.2
      linarith
    have hsum : ∑ i ∈ Finset.Icc ⌈(lo - c) / h⌉ ⌊(hi - c) / h⌋, W (c + h * i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi'
      obtain ⟨h1, h2⟩ := (hmemI lo hi i).mp hi'
      exact hzero _ h1 h2
    have hint : ∫ x in lo..hi, W x = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro x hx
        rw [Set.uIcc_of_le hlh] at hx
        exact hzero x hx.1 hx.2
    rw [hsum, hint]; norm_num
  · have hloA : lo ≤ A := le_max_left _ _
    have haA : a ≤ A := le_max_right _ _
    have hBhi : B ≤ hi := min_le_left _ _
    have hBb : B ≤ b := min_le_right _ _
    -- the sum reduces to the points in [A, B]
    have hsub : Finset.Icc ⌈(A - c) / h⌉ ⌊(B - c) / h⌋ ⊆ Finset.Icc ⌈(lo - c) / h⌉ ⌊(hi - c) / h⌋ := by
      intro i hi'
      obtain ⟨h1, h2⟩ := (hmemI A B i).mp hi'
      exact (hmemI lo hi i).mpr ⟨by linarith, by linarith⟩
    have hsum1 : ∑ i ∈ Finset.Icc ⌈(lo - c) / h⌉ ⌊(hi - c) / h⌋, W (c + h * i)
        = ∑ i ∈ Finset.Icc ⌈(A - c) / h⌉ ⌊(B - c) / h⌋, W (c + h * i) := by
      symm
      apply Finset.sum_subset hsub
      intro i hi1 hi2
      obtain ⟨h1, h2⟩ := (hmemI lo hi i).mp hi1
      apply hWout
      by_contra hcon
      push_neg at hcon
      exact hi2 ((hmemI A B i).mpr ⟨max_le h1 hcon.1, le_min h2 hcon.2⟩)
    -- W vs φ on [A, B]: they differ only at a, b
    set I := Finset.Icc ⌈(A - c) / h⌉ ⌊(B - c) / h⌋ with hI
    have hdiff : |∑ i ∈ I, W (c + h * i) - ∑ i ∈ I, φ (c + h * i)| ≤ 2 := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hpt : ∀ i ∈ I, |W (c + h * i) - φ (c + h * i)|
          ≤ (if c + h * i = a then 1 else 0) + (if c + h * i = b then 1 else 0) := by
        intro i hi'
        obtain ⟨h1, h2⟩ := (hmemI A B i).mp hi'
        have hin : c + h * i ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
        by_cases hxa : c + h * i = a
        · have := hφ0 _ hin; have := hφ1 _ hin; have := hW0 (c + h * i); have := hW1 (c + h * i)
          rw [if_pos hxa]
          have : 0 ≤ (if c + h * i = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
          rw [abs_le]; constructor <;> linarith
        · by_cases hxb : c + h * i = b
          · have := hφ0 _ hin; have := hφ1 _ hin; have := hW0 (c + h * i); have := hW1 (c + h * i)
            rw [if_neg hxa, if_pos hxb]
            rw [abs_le]; constructor <;> linarith
          · rw [if_neg hxa, if_neg hxb, hWin _ ⟨lt_of_le_of_ne hin.1 (Ne.symm hxa), lt_of_le_of_ne hin.2 hxb⟩]
            simp
      refine le_trans (Finset.sum_le_sum hpt) ?_
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have h1 := card_prog_eq_le_one I c h a hh
      have h2 := card_prog_eq_le_one I c h b hh
      have h1' : ((I.filter (fun i : ℤ => c + h * i = a)).card : ℝ) ≤ 1 := by exact_mod_cast h1
      have h2' : ((I.filter (fun i : ℤ => c + h * i = b)).card : ℝ) ≤ 1 := by exact_mod_cast h2
      linarith
    -- the integral reduces to ∫_A^B φ (a.e. equality; no integrability needed)
    have hint_eq : ∫ x in lo..hi, W x = ∫ x in A..B, φ x := by
      rw [intervalIntegral.integral_of_le hlh, intervalIntegral.integral_of_le hAB,
        ← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [Measure.ae_ne volume A, Measure.ae_ne volume B] with x hxA hxB
      simp only [Set.indicator, Set.mem_Ioc]
      by_cases hx : A < x ∧ x ≤ B
      · have hx1 : lo < x ∧ x ≤ hi := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        rw [if_pos hx1, if_pos hx]
        exact hWin x ⟨by linarith [hx.1], lt_of_lt_of_le (lt_of_le_of_ne hx.2 hxB) hBb⟩
      · rw [if_neg hx]
        split_ifs with hx1
        · apply hWout
          rcases not_and_or.mp hx with h1 | h1
          · left
            have hlt : x < A := lt_of_le_of_ne (not_lt.mp h1) hxA
            rcases le_total lo a with hla | hla
            · rw [hA, max_eq_right hla] at hlt; exact hlt
            · rw [hA, max_eq_left hla] at hlt; linarith [hx1.1]
          · right
            have hgt : B < x := not_le.mp h1
            rcases le_total hi b with hhb | hhb
            · rw [hB, min_eq_left hhb] at hgt; linarith [hx1.2]
            · rw [hB, min_eq_right hhb] at hgt; exact hgt
        · rfl
    have hG := prog_antitone φ A B c h hh hAB (hanti.mono (Set.Icc_subset_Icc haA hBb))
      (fun x hx => hφ0 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (fun x hx => hφ1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    rw [hsum1, hint_eq]
    calc |∑ i ∈ I, W (c + h * i) - (1 / h) * ∫ x in A..B, φ x|
        = |(∑ i ∈ I, W (c + h * i) - ∑ i ∈ I, φ (c + h * i))
            + (∑ i ∈ I, φ (c + h * i) - (1 / h) * ∫ x in A..B, φ x)| := by ring_nf
      _ ≤ |∑ i ∈ I, W (c + h * i) - ∑ i ∈ I, φ (c + h * i)|
            + |∑ i ∈ I, φ (c + h * i) - (1 / h) * ∫ x in A..B, φ x| := abs_add_le _ _
      _ ≤ 2 + 2 := add_le_add hdiff hG
      _ = 4 := by norm_num

end TrackF
end ZetaShell
