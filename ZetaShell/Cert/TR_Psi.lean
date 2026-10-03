/-
L7_5 (28 Sep 2026), Track R helper for node R3: the autocorrelation `ψ(α) = psiS v_p α` of a Shell profile in
closed form.
  * `psiS_neg`: `ψ` is even (translation invariance of Lebesgue measure; no hypothesis on `v`).
  * `psiS_eq_zero`: `ψ(α) = 0` for `α > λ` (support).
  * `psiS_eq_psiHat`: for `0 ≤ α ≤ λ`, `ψ(α) = (λ/2)·ψ̂(α/(λ/2))/mass²`, where `ψ̂ = pR (psiHat P̂)` is the exact
    polynomial of `ShellCertQ` (change of variables `t = (λ/2)y + α`, then `TR_Biv.pR_psiHat`).
-/
import ZetaShell.Cert.TR_Biv

open MeasureTheory intervalIntegral

namespace ZetaShell.TR
open ZetaShell.CertQ

theorem psiS_neg (v : ℝ → ℝ) (a : ℝ) : psiS v (-a) = psiS v a := by
  unfold psiS
  calc ∫ t, v t * v (t - -a) = ∫ t, (fun u => v u * v (u - -a)) (t - a) :=
        (integral_sub_right_eq_self (fun u => v u * v (u - -a)) a).symm
    _ = ∫ t, v t * v (t - a) := by
        congr 1; funext t
        show v (t - a) * v (t - a - -a) = v t * v (t - a)
        rw [show t - a - -a = t by ring, mul_comm]

theorem psiS_abs (v : ℝ → ℝ) (a : ℝ) : psiS v |a| = psiS v a := by
  rcases le_or_gt 0 a with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, psiS_neg]

theorem vv_eq (S : ShellProfile) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    S.v t * S.v (t - a) = Set.indicator (Set.Icc (a - (S.lam : ℝ) / 2) ((S.lam : ℝ) / 2))
      (fun t => S.p t ^ 2 * S.p (t - a) ^ 2 / S.mass ^ 2) t := by
  have hiff : (|t| ≤ (S.lam : ℝ) / 2 ∧ |t - a| ≤ (S.lam : ℝ) / 2)
      ↔ t ∈ Set.Icc (a - (S.lam : ℝ) / 2) ((S.lam : ℝ) / 2) := by
    rw [abs_le, abs_le, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; refine ⟨⟨?_, h2⟩, ?_, ?_⟩ <;> linarith
  by_cases h3 : t ∈ Set.Icc (a - (S.lam : ℝ) / 2) ((S.lam : ℝ) / 2)
  · obtain ⟨h1, h2⟩ := hiff.mpr h3
    rw [Set.indicator_of_mem h3]
    simp only [ShellProfile.v, if_pos h1, if_pos h2]; ring
  · rw [Set.indicator_apply, if_neg h3]
    by_cases h1 : |t| ≤ (S.lam : ℝ) / 2
    · have h2 : ¬ |t - a| ≤ (S.lam : ℝ) / 2 := fun h2 => h3 (hiff.mp ⟨h1, h2⟩)
      simp only [ShellProfile.v, if_neg h2, mul_zero]
    · simp only [ShellProfile.v, if_neg h1, zero_mul]

theorem psiS_eq_interval (S : ShellProfile) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ (S.lam : ℝ)) :
    psiS S.v a = ∫ t in (a - (S.lam : ℝ) / 2)..((S.lam : ℝ) / 2),
      S.p t ^ 2 * S.p (t - a) ^ 2 / S.mass ^ 2 := by
  unfold psiS
  simp_rw [vv_eq S ha0]
  rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

theorem psiS_eq_zero (S : ShellProfile) {a : ℝ} (ha : (S.lam : ℝ) < a) (hl : 0 < (S.lam : ℝ)) :
    psiS S.v a = 0 := by
  unfold psiS
  have h0 : 0 ≤ a := by linarith
  have he : Set.Icc (a - (S.lam : ℝ) / 2) ((S.lam : ℝ) / 2) = ∅ :=
    Set.Icc_eq_empty (not_le.mpr (by linarith))
  simp_rw [vv_eq S h0, he, Set.indicator_empty]
  simp

/-- `y ↦ P(y) P(y+β)`. -/
def Hf (P : List ℚ) (β : ℝ) (y : ℝ) : ℝ := pR P y * pR P (y + β)

/-- `u ↦ Hf P β (u/b)`. -/
noncomputable def Hs (P : List ℚ) (β b : ℝ) (u : ℝ) : ℝ := Hf P β (u / b)

theorem psiS_eq_psiHat (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a ≤ (S.lam : ℝ)) :
    psiS S.v a = (S.lam : ℝ) / 2 * pR (psiHat (Ph S)) (a / ((S.lam : ℝ) / 2)) / S.mass ^ 2 := by
  rw [psiS_eq_interval S ha0 ha, pR_psiHat]
  have hb : (S.lam : ℝ) / 2 ≠ 0 := by positivity
  have e1 : ∀ t, S.p t ^ 2 * S.p (t - a) ^ 2 / S.mass ^ 2
      = Hs (Ph S) (a / ((S.lam : ℝ) / 2)) ((S.lam : ℝ) / 2) (t - a) / S.mass ^ 2 := by
    intro t
    rw [Hs, Hf, p_sq_eq' S hl, p_sq_eq' S hl,
      show (t - a) / ((S.lam : ℝ) / 2) + a / ((S.lam : ℝ) / 2) = t / ((S.lam : ℝ) / 2) by ring]
    ring
  simp_rw [e1]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_sub_right (Hs (Ph S) (a / ((S.lam : ℝ) / 2)) ((S.lam : ℝ) / 2)) a]
  simp only [Hs]
  rw [intervalIntegral.integral_comp_div (Hf (Ph S) (a / ((S.lam : ℝ) / 2))) hb, smul_eq_mul]
  have e2 : (a - (S.lam : ℝ) / 2 - a) / ((S.lam : ℝ) / 2) = -1 := by
    rw [show a - (S.lam : ℝ) / 2 - a = -((S.lam : ℝ) / 2) by ring, neg_div, div_self hb]
  have e3 : ((S.lam : ℝ) / 2 - a) / ((S.lam : ℝ) / 2) = 1 - a / ((S.lam : ℝ) / 2) := by
    rw [sub_div, div_self hb]
  rw [e2, e3]
  simp only [Hf]

end ZetaShell.TR
