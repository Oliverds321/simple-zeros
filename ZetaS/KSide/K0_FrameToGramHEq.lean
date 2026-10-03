/-
K0, old form (L0_1, 28 Sep 2026; the lead's "mismatch 9"): the skeleton statement of K0 with `HEq`, as a short corollary
of the accepted `frame_to_gram_fix` (which replaced the `HEq` by a reindexing). W1L's proof was written against this form.
-/
import ZetaS.KSide.K0_FrameToGram

open Finset

namespace ZetaS

private lemma heq_reindex_finCongr {m n : ℕ} (h : m = n) (M : Matrix (Fin m) (Fin m) ℝ) :
    HEq (Matrix.reindex (finCongr h) (finCongr h) M) M := by
  subst h
  simp

/-- The pre-ruling K0 statement (with `HEq`), from `frame_to_gram_fix`. -/
theorem frame_to_gram_heq (F : ZeroFrame) :
    ∃ D : GramData, D.d = F.d ∧ HEq D.Gt F.Gt ∧ D.Nw = F.Nw ∧
      D.s1 = #(univ.filter fun i => F.m i = 1) ∧ D.k = F.k ∧ D.Λ = F.Λ ∧
      RHLinalg.rtrace D.Etr ≤ RHLinalg.rtrace F.Etr := by
  obtain ⟨D, h, hG, hN, hs, hk, hΛ, htr, -⟩ := frame_to_gram_fix F
  refine ⟨D, h.symm, ?_, hN, hs, hk, hΛ, htr⟩
  rw [hG]
  exact heq_reindex_finCongr h F.Gt

end ZetaS
