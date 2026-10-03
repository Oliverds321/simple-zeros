/-
nodes/C21_CertSound.lean — track C node C21 (L1_1b, 28 Sep 2026).
Depends on: C20.
Expected proof size: ≤ 60 lines.
PROVED (L5_1, 28 Sep 2026) from C20 (`Node.check_sound`, L5_1) and the CAP argument outside the root box.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C20_NodeSound

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma getD_nonneg' {L : List ℚ} (hL : ∀ m ∈ L, 0 ≤ m) (l : ℕ) : 0 ≤ L.getD l 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases hm : L[l]? with
  | none => simp
  | some m => simpa using hL m (List.mem_of_getElem? hm)

/-- = `Cert.check_sound` of CertSpecAM5 (the integrator swaps this proof in there). -/
theorem Cert.check_sound' (C : Cert) (h : C.check = true) : C.data.Holds := by
  intro g hg0
  simp only [Cert.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hwf, -⟩, hroot⟩, htree⟩ := h
  by_cases hin : ∀ l < C.data.d, g l ≤ (((C.root.getD l (0, 0)).2 : ℚ) : ℝ)
  · refine Node.check_sound hwf C.tree C.root htree hg0 fun l hl => ⟨?_, hin l hl⟩
    rw [(hroot l (List.mem_range.mpr hl)).1]
    simpa using hg0 l
  · push Not at hin
    obtain ⟨l, hl, hgl⟩ := hin
    have hc := (hroot l (List.mem_range.mpr hl)).2
    have hwf2 := hwf
    simp only [LIQ.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf2
    obtain ⟨⟨hsp, hmu⟩, -⟩ := hwf2
    have hmu' : ∀ j, (0 : ℝ) ≤ ((C.data.mu.getD j 0 : ℚ) : ℝ) := fun j => by exact_mod_cast getD_nonneg' hmu j
    have hspans : 0 ≤ (C.data.spans.map fun sp => ((sp.2.2 : ℚ) : ℝ) * kCos (spanVal g sp.1 sp.2.1) ^ 2).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨sp, hsp', rfl⟩ := List.mem_map.mp hx
      have : (0 : ℝ) ≤ ((sp.2.2 : ℚ) : ℝ) := by exact_mod_cast (hsp sp hsp').1.1
      positivity
    have hsingle : ((C.data.mu.getD l 0 : ℚ) : ℝ) * g l ≤
        ∑ j ∈ Finset.range C.data.d, ((C.data.mu.getD j 0 : ℚ) : ℝ) * g j :=
      Finset.single_le_sum (f := fun j => ((C.data.mu.getD j 0 : ℚ) : ℝ) * g j)
        (fun j _ => mul_nonneg (hmu' j) (hg0 j)) (Finset.mem_range.mpr hl)
    have hmono : ((C.data.mu.getD l 0 : ℚ) : ℝ) * (((C.root.getD l (0, 0)).2 : ℚ) : ℝ) ≤
        ((C.data.mu.getD l 0 : ℚ) : ℝ) * g l := mul_le_mul_of_nonneg_left hgl.le (hmu' l)
    have hcR : ((C.data.claim : ℚ) : ℝ) ≤
        ((C.data.mu.getD l 0 : ℚ) : ℝ) * (((C.root.getD l (0, 0)).2 : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hc
      push_cast at this
      exact this
    unfold LIQ.F
    linarith

end ZetaS.CertV2
