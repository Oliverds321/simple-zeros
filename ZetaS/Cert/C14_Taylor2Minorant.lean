/-
nodes/C14_Taylor2Minorant.lean — track C node C14 (L1_1b, 28 Sep 2026).
Depends on: none (Mathlib taylor_mean_remainder_lagrange).
Expected proof size: ≤ 40 lines.
PROVED (L5_1, 28 Sep 2026) by monotonicity (Mathlib `monotoneOn_of_hasDerivWithinAt_nonneg`), not Lagrange.
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

theorem taylor2_minorant {w w1 w2 : ℝ → ℝ} {a b p : ℝ} (hw : ∀ x, HasDerivAt w (w1 x) x)
    (hw1 : ∀ x, HasDerivAt w1 (w2 x) x) (hp : ∀ ξ ∈ Icc a b, p ≤ w2 ξ) {x t : ℝ} (hx : x ∈ Icc a b)
    (ht : t ∈ Icc a b) : w t + w1 t * (x - t) + p / 2 * (x - t) ^ 2 ≤ w x := by
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hta, htb⟩ := ht
  -- u(s) = w1 s − p s is monotone on [a, b]
  have hu : MonotoneOn (fun s => w1 s - p * s) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (f' := fun s => w2 s - p * 1)
    · exact fun s _ => ((hw1 s).continuousAt.sub (continuousAt_const.mul continuousAt_id)).continuousWithinAt
    · exact fun s _ => ((hw1 s).sub ((hasDerivAt_id s).const_mul p)).hasDerivWithinAt
    · intro s hs
      have := hp s (interior_subset hs)
      simp only [mul_one]; linarith
  -- h(s) = w s − w1 t (s − t) − p/2 (s − t)², with h′(s) = u(s) − u(t)
  have hd : ∀ s, HasDerivAt (fun s => w s - w1 t * (s - t) - p / 2 * (s - t) ^ 2)
      ((w1 s - p * s) - (w1 t - p * t)) s := by
    intro s
    have e1 : HasDerivAt (fun s => s - t) 1 s := (hasDerivAt_id s).sub_const t
    have := ((hw s).sub (e1.const_mul (w1 t))).sub ((e1.pow 2).const_mul (p / 2))
    refine HasDerivAt.congr_deriv (f := fun s => w s - w1 t * (s - t) - p / 2 * (s - t) ^ 2) this ?_
    norm_num
    ring
  have h0 : w t - w1 t * (t - t) - p / 2 * (t - t) ^ 2 = w t := by ring
  rcases le_total t x with htx | hxt
  · have hmono : MonotoneOn (fun s => w s - w1 t * (s - t) - p / 2 * (s - t) ^ 2) (Icc t x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t x)
        (f' := fun s => (w1 s - p * s) - (w1 t - p * t))
      · exact fun s _ => (hd s).continuousAt.continuousWithinAt
      · exact fun s _ => (hd s).hasDerivWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have := hu ⟨hta, htb⟩ ⟨by linarith [hs.1], by linarith [hs.2]⟩ hs.1.le
        simp only at this ⊢
        linarith
    have := hmono ⟨le_refl t, htx⟩ ⟨htx, le_refl x⟩ htx
    simp only at this
    linarith
  · have hanti : AntitoneOn (fun s => w s - w1 t * (s - t) - p / 2 * (s - t) ^ 2) (Icc x t) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x t)
        (f' := fun s => (w1 s - p * s) - (w1 t - p * t))
      · exact fun s _ => (hd s).continuousAt.continuousWithinAt
      · exact fun s _ => (hd s).hasDerivWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have := hu ⟨by linarith [hs.1], by linarith [hs.2]⟩ ⟨hta, htb⟩ hs.2.le
        simp only at this ⊢
        linarith
    have := hanti ⟨le_refl x, hxt⟩ ⟨hxt, le_refl t⟩ hxt
    simp only at this
    linarith

end ZetaS.CertV2
