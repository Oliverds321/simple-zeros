/-
nodes/C17_CapLeaf.lean — track C node C17 (L1_1b, 28 Sep 2026).
Depends on: C-spec.
Expected proof size: ≤ 30 lines.
PROVED (L5_1, 28 Sep 2026).
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma list_range_sum_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

private lemma getD_nonneg {L : List ℚ} (hL : ∀ m ∈ L, 0 ≤ m) (l : ℕ) : 0 ≤ L.getD l 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases hm : L[l]? with
  | none => simp
  | some m => simpa using hL m (List.mem_of_getElem? hm)

theorem checkCap_sound {D : LIQ} (hwf : D.wf = true) {B : Box} (h : checkCap D B = true) {g : ℕ → ℝ}
    (hg0 : ∀ l, 0 ≤ g l) (hg : B.Mem D.d g) : ((D.claim : ℚ) : ℝ) ≤ D.F g := by
  simp only [LIQ.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hsp, hmu⟩, -⟩ := hwf
  simp only [checkCap, decide_eq_true_eq, list_range_sum_eq] at h
  have h' : ((D.claim : ℚ) : ℝ) ≤ ∑ l ∈ Finset.range D.d,
      ((D.mu.getD l 0 : ℚ) : ℝ) * (((B.getD l (0, 0)).1 : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at this
    exact this
  have hspans : 0 ≤ (D.spans.map fun sp => ((sp.2.2 : ℚ) : ℝ) * kCos (spanVal g sp.1 sp.2.1) ^ 2).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨sp, hsp', rfl⟩ := List.mem_map.mp hx
    have : (0 : ℝ) ≤ ((sp.2.2 : ℚ) : ℝ) := by exact_mod_cast (hsp sp hsp').1.1
    positivity
  have hlin : ∑ l ∈ Finset.range D.d, ((D.mu.getD l 0 : ℚ) : ℝ) * (((B.getD l (0, 0)).1 : ℚ) : ℝ)
      ≤ ∑ l ∈ Finset.range D.d, ((D.mu.getD l 0 : ℚ) : ℝ) * g l := by
    apply Finset.sum_le_sum
    intro l hl
    have hm : (0 : ℝ) ≤ ((D.mu.getD l 0 : ℚ) : ℝ) := by exact_mod_cast getD_nonneg hmu l
    exact mul_le_mul_of_nonneg_left (hg l (Finset.mem_range.mp hl)).1 hm
  unfold LIQ.F
  linarith

end ZetaS.CertV2
