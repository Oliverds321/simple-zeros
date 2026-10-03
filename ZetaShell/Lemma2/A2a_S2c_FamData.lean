/-
A2a_S2c_FamData (L7_8, round 4): for each family, `q ↦ w(qe/Q)` vanishes outside `[a, b]`, equals an antitone
`φ` with values in `[0,1]` on `(a, b)`, and takes values in `[0,1]` (`fam_prog_data`), as `prog_general` needs.
sharp: `[0, Q/e]`, `φ = 1`; dyadic: `[Q/(2e), Q/e]`, `φ = 1`; weighted: `[0, Q/e]`, `φ(q) = (1 − qe/Q)²`.
-/
import ZetaShell.Lemma2.A2a_S2s_Defs

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem fam_prog_data (F : Fam) (Q e : ℕ) (hQ : 1 ≤ Q) (he : 1 ≤ e) :
    ∃ a b : ℝ, ∃ φ : ℝ → ℝ, a ≤ b ∧ AntitoneOn φ (Set.Icc a b) ∧ (∀ x ∈ Set.Icc a b, 0 ≤ φ x) ∧
      (∀ x ∈ Set.Icc a b, φ x ≤ 1) ∧ (∀ x ∈ Set.Ioo a b, F.w (x * e / Q) = φ x) ∧
      (∀ x, x < a ∨ b < x → F.w (x * e / Q) = 0) ∧ (∀ x, 0 ≤ F.w (x * e / Q)) ∧
      (∀ x, F.w (x * e / Q) ≤ 1) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hxe : ∀ x : ℝ, (0 ≤ x * e / Q ↔ 0 ≤ x) := by
    intro x; rw [div_nonneg_iff]; constructor
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · by_contra hx; push_neg at hx; nlinarith
      · linarith
    · intro hx; left; exact ⟨by positivity, hQR.le⟩
  have hxe1 : ∀ x : ℝ, (x * e / Q ≤ 1 ↔ x ≤ Q / e) := by
    intro x; rw [div_le_one hQR, le_div_iff₀ heR]
  have hxe2 : ∀ x : ℝ, (1 / 2 < x * e / Q ↔ Q / (2 * e) < x) := by
    intro x; rw [lt_div_iff₀ hQR, div_lt_iff₀ (by positivity)]; constructor <;> intro h <;> linarith
  cases F
  · -- sharp
    refine ⟨0, Q / e, fun _ => 1, by positivity, fun _ _ _ _ _ => le_rfl, fun _ _ => zero_le_one,
      fun _ _ => le_rfl, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Fam.w]
      rw [if_pos ⟨(hxe x).mpr hx.1.le, (hxe1 x).mpr hx.2.le⟩]
    · intro x hx
      simp only [Fam.w]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      rcases hx with hx | hx
      · linarith [(hxe x).mp h1]
      · linarith [(hxe1 x).mp h2]
    · intro x; simp only [Fam.w]; split_ifs <;> norm_num
    · intro x; simp only [Fam.w]; split_ifs <;> norm_num
  · -- dyadic
    refine ⟨Q / (2 * e), Q / e, fun _ => 1, ?_, fun _ _ _ _ _ => le_rfl, fun _ _ => zero_le_one,
      fun _ _ => le_rfl, ?_, ?_, ?_, ?_⟩
    · apply div_le_div_of_nonneg_left hQR.le heR; linarith
    · intro x hx
      simp only [Fam.w]
      rw [if_pos ⟨(hxe2 x).mpr hx.1, (hxe1 x).mpr hx.2.le⟩]
    · intro x hx
      simp only [Fam.w]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      rcases hx with hx | hx
      · linarith [(hxe2 x).mp h1]
      · linarith [(hxe1 x).mp h2]
    · intro x; simp only [Fam.w]; split_ifs <;> norm_num
    · intro x; simp only [Fam.w]; split_ifs <;> norm_num
  · -- weighted
    refine ⟨0, Q / e, fun x => (1 - x * e / Q) ^ 2, by positivity, ?_, fun _ _ => by positivity, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      have h1 : 0 ≤ 1 - t * e / Q := by linarith [(hxe1 t).mpr ht.2]
      have h2 : t * e / Q - s * e / Q ≥ 0 := by
        rw [← sub_div]; apply div_nonneg _ hQR.le; nlinarith
      simp only
      nlinarith
    · intro x hx
      have h1 := (hxe x).mpr hx.1
      have h2 := (hxe1 x).mpr hx.2
      simp only
      nlinarith
    · intro x hx
      simp only [Fam.w]
      rw [if_pos ⟨(hxe x).mpr hx.1.le, (hxe1 x).mpr hx.2.le⟩]
    · intro x hx
      simp only [Fam.w]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      rcases hx with hx | hx
      · linarith [(hxe x).mp h1]
      · linarith [(hxe1 x).mp h2]
    · intro x; simp only [Fam.w]; split_ifs <;> positivity
    · intro x; simp only [Fam.w]; split_ifs with h
      · nlinarith [h.1, h.2]
      · norm_num

end TrackF
end ZetaShell
