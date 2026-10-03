/-
L7_5 (28 Sep 2026), round 5: the zeroth-order half of the pointwise leaf `ZR_phi_pw`, PROVED:
  `|φ_x(u)| = |V_{x,s}(e^u)| ≤ C T e^{−u/2} 1_K(u)`,  `K = {u : |u − s| ≤ κ, |e^u − x| ≤ 1/(8Δ)}`,
with `C = sup |f|` (from `|D_T| ≤ T`, `0 ≤ Ξ ≤ 1`, and the supports of `Ξ` and `f`).
-/
import ZetaShell.PropZ.ZB_As

open MeasureTheory

namespace ZetaShell.PropZ

theorem ZR_phi_pw0 (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T Δ s : ℝ), 0 ≤ T → 0 < Δ → ∀ (x u : ℝ),
      ‖VxsW T κ Ξ f Δ s x (Real.exp u)‖
          ≤ C * T * Real.exp (-(u / 2))
            * ({u | |u - s| ≤ κ ∧ |Real.exp u - x| ≤ 1 / (8 * Δ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) u := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) (hf.supp.trans Set.Ioo_subset_Icc_self)
  obtain ⟨M, hM⟩ := hf.smooth.continuous.bounded_above_of_compact_support hfc
  refine ⟨max M 0, le_max_right _ _, fun T Δ s hT hΔ x u => ?_⟩
  have hVeq : VxsW T κ Ξ f Δ s x (Real.exp u)
      = ((Real.exp u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * DT T (s - u) * ((Ξ ((u - s) / κ) : ℝ) : ℂ)
        * ((f (Δ * (Real.exp u - x)) : ℝ) : ℂ) := by
    unfold VxsW As; rw [Real.log_exp]
  have hpow : Real.exp u ^ (-(1 / 2 : ℝ)) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_mul]; ring_nf
  by_cases hu : u ∈ ({u | |u - s| ≤ κ ∧ |Real.exp u - x| ≤ 1 / (8 * Δ)} : Set ℝ)
  · rw [Set.indicator_of_mem hu, mul_one, hVeq, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, hpow,
      abs_of_pos (Real.exp_pos _)]
    have h1 : ‖DT T (s - u)‖ ≤ T := by rw [DT_eq_DTf]; exact ZetaShell.DTFacts.norm_DTf_le hT _
    have h2 : |Ξ ((u - s) / κ)| ≤ 1 := by
      rw [abs_of_nonneg (hΞ.nonneg _)]; exact hΞ.le_one _
    have h3 : |f (Δ * (Real.exp u - x))| ≤ max M 0 := by
      have := hM (Δ * (Real.exp u - x)); rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    have he := Real.exp_pos (-(u / 2))
    calc Real.exp (-(u / 2)) * ‖DT T (s - u)‖ * |Ξ ((u - s) / κ)| * |f (Δ * (Real.exp u - x))|
        ≤ Real.exp (-(u / 2)) * T * 1 * max M 0 := by
          gcongr
      _ = max M 0 * T * Real.exp (-(u / 2)) := by ring
  · rw [Set.indicator_of_notMem hu, mul_zero, hVeq]
    simp only [Set.mem_setOf_eq, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · have hz : (u - s) / κ ∉ tsupport Ξ := by
        intro h
        have h' := hΞ.supp h
        have : |(u - s) / κ| < 1 := abs_lt.mpr ⟨h'.1, h'.2⟩
        rw [abs_div, abs_of_pos hκ, div_lt_one hκ] at this
        linarith
      rw [image_eq_zero_of_notMem_tsupport hz]; simp
    · have hz : Δ * (Real.exp u - x) ∉ tsupport f := by
        intro h
        have h' := hf.supp h
        have : |Δ * (Real.exp u - x)| < 1 / 8 := abs_lt.mpr ⟨h'.1, h'.2⟩
        rw [abs_mul, abs_of_pos hΔ] at this
        have h8 : Δ * (1 / (8 * Δ)) = 1 / 8 := by field_simp
        have : Δ * (1 / (8 * Δ)) < Δ * |Real.exp u - x| := mul_lt_mul_of_pos_left hu hΔ
        linarith
      rw [image_eq_zero_of_notMem_tsupport hz]; simp

end ZetaShell.PropZ
