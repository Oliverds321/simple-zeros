/-
L7_5 (28 Sep 2026), Track R helper for node R5: a general reduction of `S.L75` (ChallengeShell) to
  * `q = pR S.d` strictly decreasing on `[0,1]` (in `s = (2t/λ)²`),
  * `q(0) = 1` and `q(1) ≥ 1/6`,
  * the two exact rational moment inequalities `3/4 ≤ Z/2`, `1/2 ≤ Z₂/2` (y-units).
From these: `0 < p ≤ 1` on `|t| ≤ λ/2` (q decreasing: `q(1) ≤ q(s) ≤ q(0)`), `p` strictly decreasing on `[0, λ/2]`
(`s` strictly increasing there), `⟨p²⟩ = Z/2`, `⟨p⁴⟩ = Z₂/2`, `p(λ/2) = q(1)`.
-/
import ZetaShell.Cert.TR_Poly

open MeasureTheory intervalIntegral

namespace ZetaShell.TR
open ZetaShell.CertQ

theorem sig_mem (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) {t : ℝ} (ht : |t| ≤ (S.lam : ℝ) / 2) :
    (2 * t / (S.lam : ℝ)) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  rw [sq_le_one_iff_abs_le_one, abs_div, abs_mul, abs_of_pos hl, abs_two, div_le_one hl]
  linarith

theorem L75_of_cert (S : ShellProfile) (hl : 0 < (S.lam : ℝ))
    (hanti : StrictAntiOn (pR S.d) (Set.Icc 0 1)) (h0 : pR S.d 0 = 1) (hend : (1 : ℝ) / 6 ≤ pR S.d 1)
    (ha : (3 : ℚ) / 4 ≤ pdefint (Ph S) (-1) 1 / 2)
    (hb : (1 : ℚ) / 2 ≤ pdefint (pmul (Ph S) (Ph S)) (-1) 1 / 2) : S.L75 := by
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hlne : (S.lam : ℝ) ≠ 0 := hl.ne'
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun a ha' b hb' hab => ?_, ?_, ?_, ?_⟩
  · -- pos
    have hs := sig_mem S hl ht
    rw [p_eq]
    have := hanti.antitoneOn hs h1mem hs.2
    linarith
  · -- le_one
    have hs := sig_mem S hl ht
    rw [p_eq]
    have := hanti.antitoneOn h0mem hs hs.1
    linarith
  · -- anti
    have hsa : |a| ≤ (S.lam : ℝ) / 2 := by rw [abs_of_nonneg ha'.1]; exact ha'.2
    have hsb : |b| ≤ (S.lam : ℝ) / 2 := by rw [abs_of_nonneg hb'.1]; exact hb'.2
    rw [p_eq, p_eq]
    refine hanti (sig_mem S hl hsa) (sig_mem S hl hsb) ?_
    have hx0 : 0 ≤ 2 * a / (S.lam : ℝ) := by have := ha'.1; positivity
    have hxy : 2 * a / (S.lam : ℝ) < 2 * b / (S.lam : ℝ) := by
      apply div_lt_div_of_pos_right _ hl; linarith
    nlinarith
  · -- a_ge
    have hq : ((3 / 4 : ℚ) : ℝ) ≤ ((pdefint (Ph S) (-1) 1 / 2 : ℚ) : ℝ) := by exact_mod_cast ha
    push_cast at hq
    rw [mass_eq S hl]
    have e : (S.lam : ℝ) / 2 * ((pdefint (Ph S) (-1) 1 : ℚ) : ℝ) / (S.lam : ℝ)
        = ((pdefint (Ph S) (-1) 1 : ℚ) : ℝ) / 2 := by field_simp
    rw [e]; linarith
  · -- b_ge
    have hq : ((1 / 2 : ℚ) : ℝ) ≤ ((pdefint (pmul (Ph S) (Ph S)) (-1) 1 / 2 : ℚ) : ℝ) := by exact_mod_cast hb
    push_cast at hq
    rw [moment4_eq S hl]
    have e : (S.lam : ℝ) / 2 * ((pdefint (pmul (Ph S) (Ph S)) (-1) 1 : ℚ) : ℝ) / (S.lam : ℝ)
        = ((pdefint (pmul (Ph S) (Ph S)) (-1) 1 : ℚ) : ℝ) / 2 := by field_simp
    rw [e]; linarith
  · -- end_ge
    rw [p_eq]
    have e : (2 * ((S.lam : ℝ) / 2) / (S.lam : ℝ)) ^ 2 = 1 := by field_simp
    rw [e]; exact hend

end ZetaShell.TR
