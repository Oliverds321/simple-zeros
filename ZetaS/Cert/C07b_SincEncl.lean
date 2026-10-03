/-
lean_work/L5_1/C07b_SincEncl_fix.lean — L5_1, 28 Sep 2026. PROPOSED corrected statement of node C07b.

The node statement `sincDerivsQI_contains` (nodes/C07b_SincEncl.lean) is FALSE as written; counterexample in
`C07b_Counterexample.lean` (Y = [−1, 1], SY = [0, 0], CY = [1, 1], y = 0). Proposed fix in the STATEMENT: the
hypothesis `hY : Y.absMax ≤ 1/2 ∨ 0 < Y.lo ∨ Y.hi < 0` (the series branch, or an interval away from 0).
The checker's own calls (in `kEnclQ`, Y = πx ± 4/5 with width ≈ |x|·10⁻²⁰ + 2⁻⁶³) satisfy it; C09 discharges it.
This file proves the corrected statement `sincDerivsQI_contains'`, level A.
Imports C03_Horner (hence C02, C01) and C07a_SincDeriv.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C03_Horner
import ZetaS.Cert.C07a_SincDeriv

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fact, ih, Nat.factorial_succ]

private lemma list_range_sum_eq' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

private lemma horner_sum_eq (c : ℕ → ℚ) (n : ℕ) (u : ℝ) :
    ((List.range ((List.range n).map c).length).map
      fun j => ((((List.range n).map c).getD j 0 : ℚ) : ℝ) * u ^ j).sum = ∑ j ∈ Finset.range n, (c j : ℝ) * u ^ j := by
  rw [List.length_map, List.length_range, list_range_sum_eq']
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hj)]
  simp

private lemma widen_near {I : QI} {s x : ℝ} {e : ℚ} (hs : I.Contains s) (h : |x - s| ≤ (e : ℝ)) :
    (QI.widen I e).Contains x := by
  obtain ⟨h1, h2⟩ := hs
  obtain ⟨h3, h4⟩ := abs_le.mp h
  simp only [QI.Contains, QI.widen, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

/-- corrected C07b. -/
theorem sincDerivsQI_contains' {Y SY CY : QI} {y : ℝ} (hY : Y.absMax ≤ 1 / 2 ∨ 0 < Y.lo ∨ Y.hi < 0)
    (hy : Y.Contains y) (hs : SY.Contains (Real.sin y)) (hc : CY.Contains (Real.cos y)) :
    (sincDerivsQI Y SY CY).1.Contains (Real.sinc y) ∧ (sincDerivsQI Y SY CY).2.1.Contains (sinc1 y) ∧
      (sincDerivsQI Y SY CY).2.2.Contains (sinc2 y) := by
  unfold sincDerivsQI
  split_ifs with hm
  · dsimp only
    have hya : |y| ≤ ((Y.absMax : ℚ) : ℝ) := QI.abs_le_absMax hy
    have hm' : ((Y.absMax : ℚ) : ℝ) ≤ 1 / 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hm; push_cast at h; linarith
    obtain ⟨b0, b1, b2⟩ := sinc_series_bounds (le_trans hya hm')
    have hy2 := QI.contains_sq hy
    have hya0 : 0 ≤ |y| := abs_nonneg y
    refine ⟨?_, ?_, ?_⟩
    · have hH := horner_contains ((List.range 8).map fun j => ((-1 : ℚ) ^ j) / ((fact (2 * j + 1) : Nat) : ℚ)) hy2
      rw [horner_sum_eq] at hH
      refine widen_near hH ?_
      have hsum : ∑ j ∈ Finset.range 8, (((-1 : ℚ) ^ j / ((fact (2 * j + 1) : ℕ) : ℚ) : ℚ) : ℝ) * (y ^ 2) ^ j
          = ∑ j ∈ Finset.range 8, (-1 : ℝ) ^ j * y ^ (2 * j) / (Nat.factorial (2 * j + 1)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fact_eq]; push_cast; rw [← pow_mul]; ring
      rw [hsum]
      refine le_trans b0 (le_trans ?_ (Rat.cast_le.mpr (QI.le_rup _)))
      rw [fact_eq]; push_cast; gcongr
    · have hH := horner_contains ((List.range 7).map fun j =>
        ((-1 : ℚ) ^ (j + 1)) * (2 * (j + 1)) / ((fact (2 * j + 3) : Nat) : ℚ)) hy2
      rw [horner_sum_eq] at hH
      refine widen_near (QI.contains_mul hH hy) ?_
      have hsum : (∑ j ∈ Finset.range 7, ((((-1 : ℚ) ^ (j + 1)) * (2 * (j + 1)) /
            ((fact (2 * j + 3) : ℕ) : ℚ) : ℚ) : ℝ) * (y ^ 2) ^ j) * y
          = ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ (j + 1) * (2 * (j + 1)) * y ^ (2 * j + 1) / (Nat.factorial (2 * j + 3)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fact_eq]; push_cast; rw [← pow_mul, pow_succ]; ring
      rw [hsum]
      refine le_trans b1 (le_trans ?_ (Rat.cast_le.mpr (QI.le_rup _)))
      rw [fact_eq]; push_cast; gcongr
    · have hH := horner_contains ((List.range 7).map fun j =>
        ((-1 : ℚ) ^ (j + 1)) * (2 * (j + 1)) * (2 * j + 1) / ((fact (2 * j + 3) : Nat) : ℚ)) hy2
      rw [horner_sum_eq] at hH
      refine widen_near hH ?_
      have hsum : ∑ j ∈ Finset.range 7, ((((-1 : ℚ) ^ (j + 1)) * (2 * (j + 1)) * (2 * j + 1) /
            ((fact (2 * j + 3) : ℕ) : ℚ) : ℚ) : ℝ) * (y ^ 2) ^ j
          = ∑ j ∈ Finset.range 7, (-1 : ℝ) ^ (j + 1) * (2 * (j + 1)) * (2 * j + 1) * y ^ (2 * j) /
              (Nat.factorial (2 * j + 3)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fact_eq]; push_cast; rw [← pow_mul]; ring
      rw [hsum]
      refine le_trans b2 (le_trans ?_ (Rat.cast_le.mpr (QI.le_rup _)))
      rw [fact_eq]; push_cast; gcongr
  · dsimp only
    have hY' : 0 < Y.lo ∨ Y.hi < 0 := hY.resolve_left hm
    have hy0 : y ≠ 0 := by
      obtain ⟨h1, h2⟩ := hy
      rcases hY' with h | h
      · have : (0 : ℝ) < (Y.lo : ℝ) := by exact_mod_cast h
        exact (lt_of_lt_of_le this h1).ne'
      · have : (Y.hi : ℝ) < 0 := by exact_mod_cast h
        exact (lt_of_le_of_lt h2 this).ne
    have hiy := QI.contains_inv hy hY'
    have h0 := QI.contains_mul hs hiy
    have h1 := QI.contains_mul (QI.contains_sub hc h0) hiy
    have h2 := QI.contains_sub (QI.contains_neg h0) (QI.contains_smul 2 (QI.contains_mul h1 hiy))
    have e0 : Real.sinc y = Real.sin y * y⁻¹ := by rw [Real.sinc_of_ne_zero hy0, div_eq_mul_inv]
    have e1 : sinc1 y = (Real.cos y - Real.sin y * y⁻¹) * y⁻¹ := by
      rw [sinc1, if_neg hy0, e0, div_eq_mul_inv]
    have e2 : sinc2 y = -(Real.sin y * y⁻¹) - ((2 : ℚ) : ℝ) * ((Real.cos y - Real.sin y * y⁻¹) * y⁻¹ * y⁻¹) := by
      rw [sinc2, if_neg hy0, e1, e0]; push_cast; ring
    rw [e0, e1, e2]
    exact ⟨h0, h1, h2⟩

end ZetaS.CertV2
