/-
lean_work/L5_2/cnodes/C12_CellSound.lean — track C node C12, proved by L5_2 (28 Sep 2026).
Statement byte-identical to `lean_work/L1_1/nodes/C12_CellSound.lean`. Depends on: C11 (proved, L5_2).
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C11_TaylorModel

noncomputable section

open Set

namespace ZetaS.CertV2

theorem Cell.sound (c : Cell) :
    ∀ ξ ∈ Icc ((c.n : ℝ) / 64) (((c.n : ℝ) + 1) / 64),
      ((c.plo : ℚ) : ℝ) ≤ wK2 ξ ∧ wK2 ξ ≤ ((c.phi : ℚ) : ℝ) ∧ ((c.wlo : ℚ) : ℝ) ≤ wK ξ := by
  intro ξ hξ
  have h := c.ok
  unfold cellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hx, h1⟩, h2⟩, h3⟩ := h
  have hx' : ((c.c.x : ℚ) : ℝ) = ((c.n : ℝ) + 1 / 2) / 64 := by
    rw [hx]; unfold cw; push_cast; ring
  obtain ⟨a, b, d⟩ := taylorModel_sound c.c (1 / 128) (by norm_num) ξ
    ⟨by rw [hx']; push_cast; linarith [hξ.1], by rw [hx']; push_cast; linarith [hξ.2]⟩
  exact ⟨le_trans (by exact_mod_cast h1) a, le_trans b (by exact_mod_cast h2), le_trans (by exact_mod_cast h3) d⟩

end ZetaS.CertV2
