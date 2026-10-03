/-
lean_work/L5_1/C19a_PsdLDL_symm.lean — L5_1, 28 Sep 2026. PROPOSED corrected statement of node C19a.

The node statement `psdLDL_sound` (nodes/C19a_PsdLDL.lean) is FALSE as written: see `C19a_Counterexample.lean`
(P = [[0,1],[0,0]] and [[1,4],[0,1]] are accepted by `psdLDL 2`, the form is negative at v = (1, −1)).
`psdLDL` reads the multipliers from column 0 and the update from row 0, and never checks symmetry.
Proposed fix, in the STATEMENT (the checker's `psdLDL` stays as it is): add the symmetry hypothesis `hsym`.
`checkConvex` builds P = Σ_spans γ'·p·1[a ∈ S]·1[b ∈ S] from the d×d zero matrix, which is symmetric, so C19b can
discharge `hsym`. This file proves the corrected statement (`psdLDL_sound_symm`), level A.
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma quad_split (M : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), M i j * v i * v j =
      M 0 0 * v 0 * v 0 + ∑ j ∈ Finset.range n, M 0 (j + 1) * v 0 * v (j + 1) +
      ∑ i ∈ Finset.range n, M (i + 1) 0 * v (i + 1) * v 0 +
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, M (i + 1) (j + 1) * v (i + 1) * v (j + 1) := by
  simp only [Finset.sum_range_succ', Finset.sum_add_distrib]
  ring

private lemma getD_map_nil {f : List ℚ → List ℚ} (hf : f [] = []) (L : List (List ℚ)) (i : ℕ) :
    (L.map f).getD i [] = f (L.getD i []) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> simp [hf]

private lemma getD_tail (r : List ℚ) (j : ℕ) : r.tail.getD j 0 = r.getD (j + 1) 0 := by
  cases r <;> simp

private lemma headD_eq (r : List ℚ) : r.headD 0 = r.getD 0 0 := by
  cases r <;> rfl

private lemma getD_zipWith (g : ℚ → ℚ → ℚ) (l1 l2 : List ℚ) (j : ℕ) (h1 : j < l1.length) (h2 : j < l2.length) :
    (List.zipWith g l1 l2).getD j 0 = g (l1.getD j 0) (l2.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simp [h1, h2]), List.getElem_zipWith, List.getD_eq_getElem _ _ h1,
    List.getD_eq_getElem _ _ h2]

private lemma getD_mem {rest : List (List ℚ)} {i : ℕ} (hi : i < rest.length) : rest.getD i [] ∈ rest := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

/-- corrected C19a: the Bool elimination test certifies positive semidefiniteness of a SYMMETRIC square
rational matrix. -/
theorem psdLDL_sound_symm (n : ℕ) (P : List (List ℚ)) (hsq : P.length = n ∧ ∀ row ∈ P, row.length = n)
    (hsym : ∀ i < n, ∀ j < n, (P.getD i []).getD j 0 = (P.getD j []).getD i 0)
    (h : psdLDL n P = true) (v : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (((P.getD i []).getD j 0 : ℚ) : ℝ) * v i * v j := by
  induction n generalizing P v with
  | zero => simp
  | succ n ih =>
    obtain ⟨hlen, hrows⟩ := hsq
    obtain ⟨row, rest, rfl⟩ : ∃ row rest, P = row :: rest := by
      cases P with
      | nil => simp at hlen
      | cons r rs => exact ⟨r, rs, rfl⟩
    have hrest : rest.length = n := by simpa using hlen
    have hrow : row.length = n + 1 := hrows row (by simp)
    have hr : ∀ r ∈ rest, r.length = n + 1 := fun r hr => hrows r (by simp [hr])
    -- symmetry, read on the blocks
    have hca : ∀ i < n, (rest.getD i []).getD 0 0 = row.getD (i + 1) 0 := by
      intro i hi
      have := hsym (i + 1) (by omega) 0 (by omega)
      simpa using this
    have hRs : ∀ i < n, ∀ j < n, (rest.getD i []).getD (j + 1) 0 = (rest.getD j []).getD (i + 1) 0 := by
      intro i hi j hj
      have := hsym (i + 1) (by omega) (j + 1) (by omega)
      simpa using this
    have hq := quad_split (fun i j => ((((row :: rest).getD i []).getD j 0 : ℚ) : ℝ)) v n
    rw [hq]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    -- the column sum equals the row sum
    have hcol : ∑ i ∈ Finset.range n, (((rest.getD i []).getD 0 0 : ℚ) : ℝ) * v (i + 1) * v 0 =
        v 0 * ∑ j ∈ Finset.range n, ((row.getD (j + 1) 0 : ℚ) : ℝ) * v (j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hca i (Finset.mem_range.mp hi)]; ring
    have hrowsum : ∑ j ∈ Finset.range n, ((row.getD (j + 1) 0 : ℚ) : ℝ) * v 0 * v (j + 1) =
        v 0 * ∑ j ∈ Finset.range n, ((row.getD (j + 1) 0 : ℚ) : ℝ) * v (j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [hcol, hrowsum]
    simp only [psdLDL] at h
    split_ifs at h with h1 h2
    · -- zero pivot: the first row/column vanish
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      obtain ⟨hz, hpsd⟩ := h
      have ha : ∀ j < n, row.getD (j + 1) 0 = 0 := by
        intro j hj
        rw [← hca j hj, ← headD_eq]
        exact hz _ (getD_mem (by omega))
      have hA : ∑ j ∈ Finset.range n, ((row.getD (j + 1) 0 : ℚ) : ℝ) * v (j + 1) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [ha j (Finset.mem_range.mp hj)]; simp
      have hp : row.getD 0 0 = 0 := by rw [← headD_eq]; exact h2
      rw [hA, hp]
      have hIH := ih (rest.map List.tail)
        ⟨by simp [hrest], fun r' hr' => by
          obtain ⟨r, hr0, rfl⟩ := List.mem_map.mp hr'
          simp [hr r hr0]⟩
        (fun i hi j hj => by
          rw [getD_map_nil rfl, getD_map_nil rfl, getD_tail, getD_tail]
          exact hRs i hi j hj)
        hpsd (fun i => v (i + 1))
      have e : ∀ i j, (((rest.map List.tail).getD i []).getD j 0) = (rest.getD i []).getD (j + 1) 0 := by
        intro i j; rw [getD_map_nil rfl, getD_tail]
      simp only [e] at hIH
      simp only [Rat.cast_zero, zero_mul, mul_zero, zero_add]
      exact hIH
    · -- positive pivot: Schur complement
      set p : ℚ := row.headD 0 with hpdef
      have hp : 0 < p := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
      have hp' : row.getD 0 0 = p := by rw [hpdef, headD_eq]
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
      set S := rest.map fun r => List.zipWith (fun a b => a - r.headD 0 / p * b) r.tail row.tail with hS
      have hSf : ∀ i < n, ∀ j < n, (S.getD i []).getD j 0 =
          (rest.getD i []).getD (j + 1) 0 - row.getD (i + 1) 0 / p * row.getD (j + 1) 0 := by
        intro i hi j hj
        have hmem := getD_mem (rest := rest) (i := i) (by omega)
        have hrl := hr _ hmem
        rw [hS, getD_map_nil (by simp), getD_zipWith _ _ _ _ (by rw [List.length_tail, hrl]; omega)
          (by rw [List.length_tail, hrow]; omega),
          getD_tail, getD_tail, headD_eq, hca i hi]
      have hIH := ih S
        ⟨by simp [hS, hrest], fun r' hr' => by
          obtain ⟨r, hr0, rfl⟩ := List.mem_map.mp hr'
          simp [List.length_zipWith, hr r hr0, hrow]⟩
        (fun i hi j hj => by
          rw [hSf i hi j hj, hSf j hj i hi, hRs i hi j hj]; ring)
        h (fun i => v (i + 1))
      have hIH' : 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          ((((rest.getD i []).getD (j + 1) 0 : ℚ) : ℝ) - ((row.getD (i + 1) 0 : ℚ) : ℝ) / (p : ℝ) *
            ((row.getD (j + 1) 0 : ℚ) : ℝ)) * v (i + 1) * v (j + 1) := by
        convert hIH using 3 with i hi j hj
        rw [hSf i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]
        push_cast; ring
      set A := ∑ j ∈ Finset.range n, ((row.getD (j + 1) 0 : ℚ) : ℝ) * v (j + 1) with hAdef
      have hsplit : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          ((((rest.getD i []).getD (j + 1) 0 : ℚ) : ℝ) - ((row.getD (i + 1) 0 : ℚ) : ℝ) / (p : ℝ) *
            ((row.getD (j + 1) 0 : ℚ) : ℝ)) * v (i + 1) * v (j + 1) =
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            (((rest.getD i []).getD (j + 1) 0 : ℚ) : ℝ) * v (i + 1) * v (j + 1) - A ^ 2 / (p : ℝ) := by
        rw [hAdef, sq, Finset.sum_mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hsplit] at hIH'
      rw [hp']
      have hsq : 0 ≤ ((p : ℝ) * v 0 + A) ^ 2 / (p : ℝ) := div_nonneg (sq_nonneg _) hpR.le
      have hexp : ((p : ℝ) * v 0 + A) ^ 2 / (p : ℝ) = (p : ℝ) * v 0 * v 0 + v 0 * A + v 0 * A + A ^ 2 / (p : ℝ) := by
        field_simp
        ring
      linarith

end ZetaS.CertV2
