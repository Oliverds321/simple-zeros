/-
nodes/C20_NodeSound.lean — track C node C20 (L1_1b, 28 Sep 2026).
Depends on: C17, C18, C19b.
Expected proof size: ≤ 60 lines.
PROVED (L5_1, 28 Sep 2026) against the STATEMENTS of C18 (`checkLP_sound`, skeleton; currently false for the
checker as written, see C18_Counterexample.lean — the fix belongs in the checker and leaves C18's statement and
this proof unchanged) and C19b (`checkConvex_sound`, skeleton); C17 proved (L5_1).
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C17_CapLeaf
import ZetaS.Cert.C18_LPLeaf
import ZetaS.Cert.C19b_CvxLeaf

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma getD_modify (B : Box) (a l : ℕ) (f : ℚ × ℚ → ℚ × ℚ) :
    (B.modify a f).getD l (0, 0) = if a = l ∧ l < B.length then f (B.getD l (0, 0)) else B.getD l (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_modify, List.getD_eq_getElem?_getD]
  by_cases hl : l < B.length
  · rw [List.getElem?_eq_getElem hl]; by_cases ha : a = l <;> simp [ha, hl]
  · rw [List.getElem?_eq_none (by omega)]; simp [hl]

/-- a point of B lies in one of the two halves of a split. -/
private lemma splitAt_mem {B : Box} {d : ℕ} (a : ℕ) {g : ℕ → ℝ} (hg : B.Mem d g) :
    (B.splitAt a).1.Mem d g ∨ (B.splitAt a).2.Mem d g := by
  set m : ℚ := ((B.getD a (0, 0)).1 + (B.getD a (0, 0)).2) / 2 with hm
  have e1 : (B.splitAt a).1 = B.modify a (fun p => (p.1, m)) := rfl
  have e2 : (B.splitAt a).2 = B.modify a (fun p => (m, p.2)) := rfl
  rw [e1, e2]
  rcases le_total (g a) (m : ℝ) with h | h
  · left
    intro l hl
    rw [getD_modify]
    split_ifs with hc
    · obtain ⟨rfl, -⟩ := hc
      exact ⟨(hg a hl).1, h⟩
    · exact hg l hl
  · right
    intro l hl
    rw [getD_modify]
    split_ifs with hc
    · obtain ⟨rfl, -⟩ := hc
      exact ⟨h, (hg a hl).2⟩
    · exact hg l hl

theorem Node.check_sound {D : LIQ} (hwf : D.wf = true) (n : Node) (B : Box) (h : n.check D B = true)
    {g : ℕ → ℝ} (hg0 : ∀ l, 0 ≤ g l) (hg : B.Mem D.d g) : ((D.claim : ℚ) : ℝ) ≤ D.F g := by
  induction n generalizing B with
  | leaf l =>
    cases l with
    | cap => exact checkCap_sound hwf h hg0 hg
    | convex gh sds => exact checkConvex_sound hwf h hg0 hg
    | lp gh y sds => exact checkLP_sound hwf h hg0 hg
  | split a L R ihL ihR =>
    simp only [Node.check, Bool.and_eq_true] at h
    obtain ⟨⟨-, hL⟩, hR⟩ := h
    rcases splitAt_mem a hg with h1 | h2
    · exact ihL _ hL h1
    · exact ihR _ hR h2

end ZetaS.CertV2
