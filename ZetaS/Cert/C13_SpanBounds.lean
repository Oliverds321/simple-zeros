/-
lean_work/L5_2/cnodes/C13_SpanBounds.lean — track C node C13, proved by L5_2 (28 Sep 2026).
Statement byte-identical to `lean_work/L1_1/nodes/C13_SpanBounds.lean`. Depends on: C11, C12 (proved, L5_2).
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C11_TaylorModel
import ZetaS.Cert.C12_CellSound

noncomputable section

open Set

namespace ZetaS.CertV2

namespace C13aux

lemma foldl_min_le {f : Cell → ℚ} : ∀ (L : List Cell) (a : ℚ),
    L.foldl (fun a c => min a (f c)) a ≤ a ∧ ∀ c ∈ L, L.foldl (fun a c => min a (f c)) a ≤ f c
  | [], a => ⟨le_rfl, fun _ h => by simp at h⟩
  | c :: cs, a => by
    obtain ⟨h1, h2⟩ := foldl_min_le cs (min a (f c))
    refine ⟨h1.trans (min_le_left _ _), fun d hd => ?_⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h1.trans (min_le_right _ _)
    · exact h2 d hd

lemma le_foldl_max {f : Cell → ℚ} : ∀ (L : List Cell) (a : ℚ),
    a ≤ L.foldl (fun a c => max a (f c)) a ∧ ∀ c ∈ L, f c ≤ L.foldl (fun a c => max a (f c)) a
  | [], a => ⟨le_rfl, fun _ h => by simp at h⟩
  | c :: cs, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max cs (max a (f c))
    refine ⟨(le_max_left _ _).trans h1, fun d hd => ?_⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact (le_max_right _ _).trans h1
    · exact h2 d hd

lemma cover_cells : ∀ (L : List Cell) (n : ℤ), consecCells n L = true → L ≠ [] →
    ∀ ξ : ℝ, (n : ℝ) / 64 ≤ ξ → ξ ≤ ((n : ℝ) + L.length) / 64 →
      ∃ c ∈ L, (c.n : ℝ) / 64 ≤ ξ ∧ ξ ≤ ((c.n : ℝ) + 1) / 64
  | [], _, _, h, _, _, _ => absurd rfl h
  | c :: cs, n, h, _, ξ, h1, h2 => by
    have h' : (decide (c.n = n) && consecCells (n + 1) cs) = true := h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨hn, hcs⟩ := h'
    rcases le_total ξ (((n : ℝ) + 1) / 64) with hξ | hξ
    · exact ⟨c, List.mem_cons_self .., by rw [hn]; exact h1, by rw [hn]; exact hξ⟩
    · cases cs with
      | nil =>
        simp only [List.length_cons, List.length_nil] at h2
        refine ⟨c, List.mem_cons_self .., by rw [hn]; exact h1, by rw [hn]; push_cast at h2 ⊢; linarith⟩
      | cons d ds =>
        obtain ⟨e, he, he1, he2⟩ := cover_cells (d :: ds) (n + 1) hcs (List.cons_ne_nil _ _) ξ
          (by push_cast; exact hξ)
          (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one] at h2 ⊢; linarith)
        exact ⟨e, List.mem_cons_of_mem _ he, he1, he2⟩

end C13aux

open C13aux in
theorem spanBounds_sound (sd : SpanD) (x0 r : ℚ) (hr : 0 ≤ r) (h : (spanBounds sd x0 r).1 = true) :
    ∀ ξ ∈ Icc ((x0 : ℝ) - r) (x0 + r),
      (((spanBounds sd x0 r).2.1 : ℚ) : ℝ) ≤ wK2 ξ ∧ wK2 ξ ≤ (((spanBounds sd x0 r).2.2.1 : ℚ) : ℝ) ∧
      (((spanBounds sd x0 r).2.2.2 : ℚ) : ℝ) ≤ wK ξ := by
  intro ξ hξ
  unfold spanBounds at h ⊢
  rcases hcl : sd.cells with _ | ⟨c0, rest⟩
  · simp only [hcl, decide_eq_true_eq] at h ⊢
    have hξ' : ξ ∈ Icc ((sd.c.x : ℝ) - r) (sd.c.x + r) := by rw [h]; exact hξ
    exact taylorModel_sound sd.c r hr ξ hξ'
  · simp only [hcl, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨hx, hcons⟩, hlo⟩, hhi⟩ := h
    have hξ' : ξ ∈ Icc ((sd.c.x : ℝ) - r) (sd.c.x + r) := by rw [hx]; exact hξ
    obtain ⟨t1, t2, t3⟩ := taylorModel_sound sd.c r hr ξ hξ'
    have hlo' : ((c0.n : ℝ)) / 64 ≤ ξ := by
      have : (((c0.n : ℚ) * cw : ℚ) : ℝ) ≤ ((x0 - r : ℚ) : ℝ) := by exact_mod_cast hlo
      unfold cw at this; push_cast at this; linarith [hξ.1]
    have hhi' : ξ ≤ ((c0.n : ℝ) + (c0 :: rest).length) / 64 := by
      have : ((x0 + r : ℚ) : ℝ) ≤ ((((c0.n : ℚ) + (rest.length + 1 : ℕ)) * cw : ℚ) : ℝ) := by exact_mod_cast hhi
      unfold cw at this; push_cast at this
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith [hξ.2]
    obtain ⟨c, hcmem, hc1, hc2⟩ := cover_cells (c0 :: rest) c0.n hcons (List.cons_ne_nil _ _) ξ hlo' hhi'
    obtain ⟨s1, s2, s3⟩ := Cell.sound c ξ ⟨hc1, hc2⟩
    have f1 := (foldl_min_le (f := fun c => c.plo) (c0 :: rest) c0.plo).2 c hcmem
    have f2 := (le_foldl_max (f := fun c => c.phi) (c0 :: rest) c0.phi).2 c hcmem
    have f3 := (foldl_min_le (f := fun c => c.wlo) (c0 :: rest) c0.wlo).2 c hcmem
    simp only [List.foldl_cons, min_self, max_self] at f1 f2 f3
    have f1' : ((rest.foldl (fun a c => min a c.plo) c0.plo : ℚ) : ℝ) ≤ ((c.plo : ℚ) : ℝ) := by exact_mod_cast f1
    have f2' : ((c.phi : ℚ) : ℝ) ≤ ((rest.foldl (fun a c => max a c.phi) c0.phi : ℚ) : ℝ) := by exact_mod_cast f2
    have f3' : ((rest.foldl (fun a c => min a c.wlo) c0.wlo : ℚ) : ℝ) ≤ ((c.wlo : ℚ) : ℝ) := by exact_mod_cast f3
    rw [Rat.cast_max, Rat.cast_min, Rat.cast_max]
    exact ⟨max_le t1 (f1'.trans s1), le_min t2 (s2.trans f2'), max_le t3 (f3'.trans s3)⟩

end ZetaS.CertV2
