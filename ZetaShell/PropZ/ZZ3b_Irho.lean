/-
L7_5 (28 Sep 2026), round 8: properties of `I_ρ[f_j](ξ; μ) = ∫_{t>0} H_ρ(t) f_j(μ(t−ξ)) dt` used for Step 5:
support in `ξ`, a uniform bound, continuity in `ξ`, and `∂_s I_ρ[f_j](ξ; Δe^s) = I_ρ[f_{j+1}](ξ; Δe^s)`.
-/
import ZetaShell.PropZ.ZZ2d_Young

open MeasureTheory

namespace ZetaShell.PropZ

theorem fj_succ_apply (f : ℝ → ℝ) (j : ℕ) (z : ℝ) : fj f (j + 1) z = z * deriv (fj f j) z := rfl

theorem fj_tsupport (f : ℝ → ℝ) (hf : TestFn f) : ∀ j : ℕ, tsupport (fj f j) ⊆ Set.Ioo (-(1 / 8 : ℝ)) (1 / 8)
  | 0 => by simp only [fj]; exact hf.supp
  | j + 1 => by
    have ih := fj_tsupport f hf j
    have h : tsupport (fj f (j + 1)) ⊆ tsupport (fj f j) := by
      show tsupport (fun z => z * deriv (fj f j) z) ⊆ _
      exact (tsupport_mul_subset_right (f := fun z : ℝ => z) (g := deriv (fj f j))).trans tsupport_deriv_subset
    exact h.trans ih

theorem fj_bound (f : ℝ → ℝ) (hf : TestFn f) (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, |fj f j z| ≤ M := by
  obtain ⟨h1, h2⟩ := fj_smooth f hf j
  obtain ⟨M, hM⟩ := h1.continuous.bounded_above_of_compact_support h2
  exact ⟨max M 0, le_max_right _ _, fun z => by
    have := hM z; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)⟩

theorem Hrho_zero_off (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (T : ℝ) (ρ : ℂ)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (t : ℝ) (ht : 0 < t)
    (htI : t ∉ Set.Icc (Real.exp (-κ)) (Real.exp κ)) : Hrho T κ Ξ ρ t = 0 := by
  have h := Hrho_ind_bound κ hκ Ξ hΞ T ρ hρ0 hρ1 t
  rw [Set.indicator_of_notMem htI, mul_zero, Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from ht)] at h
  exact norm_le_zero_iff.mp h

theorem Hrho_integrableOn (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (T : ℝ) (ρ : ℂ)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) : IntegrableOn (Hrho T κ Ξ ρ) (Set.Ioi 0) := by
  have hIi : Integrable ((Set.Icc (Real.exp (-κ)) (Real.exp κ)).indicator
      (fun _ => |T| * Real.exp (2 * κ))) :=
    (integrableOn_const (s := Set.Icc (Real.exp (-κ)) (Real.exp κ)) (C := |T| * Real.exp (2 * κ))
      (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  have hind : Integrable ((Set.Ioi (0 : ℝ)).indicator (Hrho T κ Ξ ρ)) := by
    refine Integrable.mono' hIi ((Hrho_measurable κ Ξ hΞ T ρ).indicator measurableSet_Ioi).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have h := Hrho_ind_bound κ hκ Ξ hΞ T ρ hρ0 hρ1 t
    by_cases hm : t ∈ Set.Icc (Real.exp (-κ)) (Real.exp κ)
    · rw [Set.indicator_of_mem hm] at h ⊢; rw [mul_one] at h; exact h
    · rw [Set.indicator_of_notMem hm] at h ⊢; rw [mul_zero] at h; exact h
  exact (integrable_indicator_iff measurableSet_Ioi).mp hind

theorem Irho_zero_off (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (j : ℕ) (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (μ : ℝ) (hμ : 0 < μ) (ξ : ℝ)
    (hξ : ξ ∉ Set.Icc (Real.exp (-κ) - 1 / (8 * μ)) (Real.exp κ + 1 / (8 * μ))) :
    Irho T κ Ξ f j ρ μ ξ = 0 := by
  unfold Irho
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  by_cases htI : t ∈ Set.Icc (Real.exp (-κ)) (Real.exp κ)
  · have hz : μ * (t - ξ) ∉ tsupport (fj f j) := by
      intro h
      have h' := fj_tsupport f hf j h
      have habs : |μ * (t - ξ)| < 1 / 8 := abs_lt.mpr ⟨h'.1, h'.2⟩
      rw [abs_mul, abs_of_pos hμ] at habs
      have h8 : μ * (1 / (8 * μ)) = 1 / 8 := by field_simp
      apply hξ
      have hlt : |t - ξ| < 1 / (8 * μ) := by
        by_contra hc; push_neg at hc
        have := mul_le_mul_of_nonneg_left hc hμ.le
        linarith
      have := abs_lt.mp hlt
      exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
    rw [image_eq_zero_of_notMem_tsupport hz]; simp
  · rw [Hrho_zero_off κ hκ Ξ hΞ T ρ hρ0 hρ1 t ht htI, zero_mul]

theorem Irho_bound (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (j : ℕ) (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (M : ℝ) (hM : ∀ z, |fj f j z| ≤ M)
    (μ ξ : ℝ) : ‖Irho T κ Ξ f j ρ μ ξ‖ ≤ (∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖) * M := by
  have hHI := Hrho_integrableOn κ hκ Ξ hΞ T ρ hρ0 hρ1
  unfold Irho
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hHI.norm.mul_const M) (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

theorem Irho_continuous (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (j : ℕ) (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (μ : ℝ) :
    Continuous (fun ξ => Irho T κ Ξ f j ρ μ ξ) := by
  obtain ⟨M, hM0, hM⟩ := fj_bound f hf j
  have hHI := Hrho_integrableOn κ hκ Ξ hΞ T ρ hρ0 hρ1
  have hfc := (fj_smooth f hf j).1.continuous
  unfold Irho
  refine continuous_of_dominated (bound := fun t => ‖Hrho T κ Ξ ρ t‖ * M)
    (fun ξ => ((Hrho_measurable κ Ξ hΞ T ρ).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (hfc.comp (by fun_prop))).aestronglyMeasurable))
    (fun ξ => Filter.Eventually.of_forall fun t => ?_) (hHI.norm.mul_const M)
    (Filter.Eventually.of_forall fun t => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (hfc.comp (by fun_prop)))

theorem Irho_hasDerivAt_s (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (j : ℕ) (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (Δ ξ s₁ : ℝ) :
    HasDerivAt (fun s => Irho T κ Ξ f j ρ (Δ * Real.exp s) ξ) (Irho T κ Ξ f (j + 1) ρ (Δ * Real.exp s₁) ξ) s₁ := by
  obtain ⟨M, hM0, hM⟩ := fj_bound f hf (j + 1)
  have hHI := Hrho_integrableOn κ hκ Ξ hΞ T ρ hρ0 hρ1
  obtain ⟨hs0, _⟩ := fj_smooth f hf j
  obtain ⟨hs1, _⟩ := fj_smooth f hf (j + 1)
  have hd0 : Differentiable ℝ (fj f j) := (hs0.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 _).differentiable one_ne_zero
  have hmeas : ∀ (i : ℕ) (s : ℝ), Continuous (fj f i) →
      AEStronglyMeasurable (fun t => Hrho T κ Ξ ρ t * ((fj f i (Δ * Real.exp s * (t - ξ)) : ℝ) : ℂ))
        (volume.restrict (Set.Ioi 0)) := fun i s hc =>
    (Hrho_measurable κ Ξ hΞ T ρ).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (hc.comp (by fun_prop))).aestronglyMeasurable
  have key : ∀ (t s : ℝ), HasDerivAt (fun s => Hrho T κ Ξ ρ t * ((fj f j (Δ * Real.exp s * (t - ξ)) : ℝ) : ℂ))
      (Hrho T κ Ξ ρ t * ((fj f (j + 1) (Δ * Real.exp s * (t - ξ)) : ℝ) : ℂ)) s := by
    intro t s
    have hin : HasDerivAt (fun s => Δ * Real.exp s * (t - ξ)) (Δ * Real.exp s * (t - ξ)) s :=
      ((Real.hasDerivAt_exp s).const_mul Δ).mul_const (t - ξ)
    have hcomp := ((hd0 (Δ * Real.exp s * (t - ξ))).hasDerivAt.comp s hin).ofReal_comp.const_mul (Hrho T κ Ξ ρ t)
    refine hcomp.congr_deriv ?_
    rw [fj_succ_apply]; push_cast; ring
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Set.Ioi 0))
    (F := fun s t => Hrho T κ Ξ ρ t * ((fj f j (Δ * Real.exp s * (t - ξ)) : ℝ) : ℂ))
    (F' := fun s t => Hrho T κ Ξ ρ t * ((fj f (j + 1) (Δ * Real.exp s * (t - ξ)) : ℝ) : ℂ))
    (x₀ := s₁) (s := Set.univ) (bound := fun t => ‖Hrho T κ Ξ ρ t‖ * M) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => hmeas j s hs0.continuous)
    (by
      obtain ⟨M0, _, hM0'⟩ := fj_bound f hf j
      exact hHI.mul_bdd (c := M0) (Complex.continuous_ofReal.comp (hs0.continuous.comp (by fun_prop))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM0' _))
    (hmeas (j + 1) s₁ hs1.continuous)
    (Filter.Eventually.of_forall fun t s _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
    (hHI.norm.mul_const M)
    (Filter.Eventually.of_forall fun t s _ => key t s)
  exact this.2

end ZetaShell.PropZ
