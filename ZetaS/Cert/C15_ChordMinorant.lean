/-
nodes/C15_ChordMinorant.lean — track C node C15 (L1_1b, 28 Sep 2026).
Depends on: none.
Expected proof size: ≤ 60 lines.
PROVED (L5_1, 28 Sep 2026): φ(s) = w s + Q/2 (s − a)(b − s), Q = max q 0, is concave on [a, b]
(Mathlib `concaveOn_of_hasDerivWithinAt2_nonpos`), so it lies above its chord; and (x − a)(b − x) ≤ (b − a)²/4.
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

theorem chord_minorant {w w1 w2 : ℝ → ℝ} {a b q : ℝ} (hab : a < b) (hw : ∀ x, HasDerivAt w (w1 x) x)
    (hw1 : ∀ x, HasDerivAt w1 (w2 x) x) (hq : ∀ ξ ∈ Icc a b, w2 ξ ≤ q) {x : ℝ} (hx : x ∈ Icc a b) :
    w a + (w b - w a) / (b - a) * (x - a) - max q 0 * (b - a) ^ 2 / 8 ≤ w x := by
  obtain ⟨hxa, hxb⟩ := hx
  set Q := max q 0 with hQ
  have hQ0 : 0 ≤ Q := le_max_right q 0
  have hqQ : q ≤ Q := le_max_left q 0
  have hd1 : ∀ s, HasDerivAt (fun s => w s + Q / 2 * ((s - a) * (b - s))) (w1 s + Q / 2 * (a + b - 2 * s)) s := by
    intro s
    have := (hw s).add ((((hasDerivAt_id s).sub_const a).mul
      ((hasDerivAt_const s b).sub (hasDerivAt_id s))).const_mul (Q / 2))
    refine HasDerivAt.congr_deriv (f := fun s => w s + Q / 2 * ((s - a) * (b - s))) this ?_
    simp only [id, Pi.sub_apply]
    ring
  have hd2 : ∀ s, HasDerivAt (fun s => w1 s + Q / 2 * (a + b - 2 * s)) (w2 s - Q) s := by
    intro s
    have := (hw1 s).add (((hasDerivAt_const s (a + b)).sub ((hasDerivAt_id s).const_mul 2)).const_mul (Q / 2))
    refine HasDerivAt.congr_deriv (f := fun s => w1 s + Q / 2 * (a + b - 2 * s)) this ?_
    ring
  have hconc : ConcaveOn ℝ (Icc a b) (fun s => w s + Q / 2 * ((s - a) * (b - s))) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b)
      (f' := fun s => w1 s + Q / 2 * (a + b - 2 * s)) (f'' := fun s => w2 s - Q)
    · exact fun s _ => (hd1 s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd1 s).hasDerivWithinAt
    · exact fun s _ => (hd2 s).hasDerivWithinAt
    · intro s hs
      have := hq s (interior_subset hs)
      show w2 s - Q ≤ 0
      linarith
  have hba : 0 < b - a := by linarith
  have hθ1 : 0 ≤ (b - x) / (b - a) := div_nonneg (by linarith) hba.le
  have hθ2 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith) hba.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hba.ne']; ring
  have hc := hconc.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hθ1 hθ2 hsum
  have hxeq : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hba.ne']; ring
  simp only [smul_eq_mul] at hc
  rw [hxeq] at hc
  simp only [sub_self, zero_mul, mul_zero, add_zero] at hc
  have hlin : (b - x) / (b - a) * w a + (x - a) / (b - a) * w b = w a + (w b - w a) / (b - a) * (x - a) := by
    have hne : b - a ≠ 0 := hba.ne'
    field_simp
    ring
  have hquad : Q / 2 * ((x - a) * (b - x)) ≤ Q * (b - a) ^ 2 / 8 := by
    have : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg ((x - a) - (b - x))]
    nlinarith [mul_le_mul_of_nonneg_left this hQ0]
  linarith

end ZetaS.CertV2
