/-
L7_5 (28 Sep 2026), round 8: `Q_{a,b}(s) = ∫ I_ρ[f_a](ξ; Δe^s) conj(I_{ρ′}[f_b](ξ; Δe^s)) dξ`:
  `Q_{a,b}′ = Q_{a+1,b} + Q_{a,b+1}`  (differentiation under the `ξ`-integral, `ZZ3b_Irho`),
  `|Q_{a,b}(s)|² ≤ ‖I_ρ[f_a]‖₂² ‖I_{ρ′}[f_b]‖₂²`  (Cauchy–Schwarz via `cs_amgm`).
-/
import ZetaShell.PropZ.ZZ3b_Irho

open MeasureTheory

namespace ZetaShell.PropZ

noncomputable def Qab (T κ : ℝ) (Ξ f : ℝ → ℝ) (ρ ρ' : ℂ) (Δ : ℝ) (a b : ℕ) (s : ℝ) : ℂ :=
  ∫ ξ, Irho T κ Ξ f a ρ (Δ * Real.exp s) ξ * (starRingEnd ℂ) (Irho T κ Ξ f b ρ' (Δ * Real.exp s) ξ)

/-- the `ξ`-support box, uniform for `μ ≥ μm`. -/
theorem Irho_zero_off' (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (j : ℕ) (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (μm μ : ℝ) (hμm : 0 < μm) (hμ : μm ≤ μ) (ξ : ℝ)
    (hξ : ξ ∉ Set.Icc (Real.exp (-κ) - 1 / (8 * μm)) (Real.exp κ + 1 / (8 * μm))) :
    Irho T κ Ξ f j ρ μ ξ = 0 := by
  apply Irho_zero_off κ hκ Ξ hΞ f hf T j ρ hρ0 hρ1 μ (by linarith) ξ
  intro h; apply hξ
  have : 1 / (8 * μ) ≤ 1 / (8 * μm) := one_div_le_one_div_of_le (by positivity) (by linarith)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem Iprod_integrable (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (a b : ℕ) (ρ ρ' : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hρ0' : 0 < ρ'.re) (hρ1' : ρ'.re < 1)
    (μ : ℝ) (hμ : 0 < μ) :
    Integrable (fun ξ => Irho T κ Ξ f a ρ μ ξ * (starRingEnd ℂ) (Irho T κ Ξ f b ρ' μ ξ)) := by
  obtain ⟨Ma, hMa0, hMa⟩ := fj_bound f hf a
  obtain ⟨Mb, hMb0, hMb⟩ := fj_bound f hf b
  set Ba := (∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖) * Ma
  set Bb := (∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ' t‖) * Mb
  have hIi : Integrable ((Set.Icc (Real.exp (-κ) - 1 / (8 * μ)) (Real.exp κ + 1 / (8 * μ))).indicator
      (fun _ => Ba * Bb)) :=
    (integrableOn_const (s := Set.Icc (Real.exp (-κ) - 1 / (8 * μ)) (Real.exp κ + 1 / (8 * μ))) (C := Ba * Bb)
      (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  refine Integrable.mono' hIi (((Irho_continuous κ hκ Ξ hΞ f hf T a ρ hρ0 hρ1 μ).mul
    (Complex.continuous_conj.comp (Irho_continuous κ hκ Ξ hΞ f hf T b ρ' hρ0' hρ1' μ))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  by_cases hm : ξ ∈ Set.Icc (Real.exp (-κ) - 1 / (8 * μ)) (Real.exp κ + 1 / (8 * μ))
  · rw [Set.indicator_of_mem hm, norm_mul, Complex.norm_conj]
    exact mul_le_mul (Irho_bound κ hκ Ξ hΞ f hf T a ρ hρ0 hρ1 Ma hMa μ ξ)
      (Irho_bound κ hκ Ξ hΞ f hf T b ρ' hρ0' hρ1' Mb hMb μ ξ) (norm_nonneg _)
      (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hMa0)
  · rw [Set.indicator_of_notMem hm, Irho_zero_off κ hκ Ξ hΞ f hf T a ρ hρ0 hρ1 μ hμ ξ hm, zero_mul, norm_zero]

theorem Qab_hasDerivAt (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (ρ ρ' : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hρ0' : 0 < ρ'.re) (hρ1' : ρ'.re < 1)
    (Δ : ℝ) (hΔ : 0 < Δ) (a b : ℕ) (s₁ : ℝ) :
    HasDerivAt (Qab T κ Ξ f ρ ρ' Δ a b)
      (Qab T κ Ξ f ρ ρ' Δ (a + 1) b s₁ + Qab T κ Ξ f ρ ρ' Δ a (b + 1) s₁) s₁ := by
  obtain ⟨Ma, hMa0, hMa⟩ := fj_bound f hf a
  obtain ⟨Mb, hMb0, hMb⟩ := fj_bound f hf b
  obtain ⟨Ma1, hMa10, hMa1⟩ := fj_bound f hf (a + 1)
  obtain ⟨Mb1, hMb10, hMb1⟩ := fj_bound f hf (b + 1)
  set h1 := ∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖
  set h2 := ∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ' t‖
  have h10 : 0 ≤ h1 := integral_nonneg fun _ => norm_nonneg _
  have h20 : 0 ≤ h2 := integral_nonneg fun _ => norm_nonneg _
  set μm := Δ * Real.exp (s₁ - 1) with hμm
  have hμm0 : 0 < μm := by positivity
  set K := Set.Icc (Real.exp (-κ) - 1 / (8 * μm)) (Real.exp κ + 1 / (8 * μm)) with hK
  have hμs : ∀ s ∈ Metric.ball s₁ 1, μm ≤ Δ * Real.exp s := fun s hs => by
    have := (abs_lt.mp (Real.dist_eq s s₁ ▸ Metric.mem_ball.mp hs)).1
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hΔ.le
  set Cb := h1 * Ma1 * (h2 * Mb) + h1 * Ma * (h2 * Mb1)
  have hbi : Integrable (K.indicator (fun _ => Cb)) :=
    (integrableOn_const (s := K) (C := Cb) (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  have hcont : ∀ (j : ℕ) (r : ℂ), 0 < r.re → r.re < 1 → ∀ μ, Continuous (fun ξ => Irho T κ Ξ f j r μ ξ) :=
    fun j r h0 h1' μ => Irho_continuous κ hκ Ξ hΞ f hf T j r h0 h1' μ
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := s₁)
    (F := fun s ξ => Irho T κ Ξ f a ρ (Δ * Real.exp s) ξ * (starRingEnd ℂ) (Irho T κ Ξ f b ρ' (Δ * Real.exp s) ξ))
    (F' := fun s ξ => Irho T κ Ξ f (a + 1) ρ (Δ * Real.exp s) ξ * (starRingEnd ℂ) (Irho T κ Ξ f b ρ' (Δ * Real.exp s) ξ)
      + Irho T κ Ξ f a ρ (Δ * Real.exp s) ξ * (starRingEnd ℂ) (Irho T κ Ξ f (b + 1) ρ' (Δ * Real.exp s) ξ))
    (s := Metric.ball s₁ 1) (bound := K.indicator (fun _ => Cb)) (Metric.ball_mem_nhds s₁ one_pos)
    (Filter.Eventually.of_forall fun s => ((hcont a ρ hρ0 hρ1 _).mul
      (Complex.continuous_conj.comp (hcont b ρ' hρ0' hρ1' _))).aestronglyMeasurable)
    (Iprod_integrable κ hκ Ξ hΞ f hf T a b ρ ρ' hρ0 hρ1 hρ0' hρ1' _ (by positivity))
    ((((hcont (a + 1) ρ hρ0 hρ1 _).mul (Complex.continuous_conj.comp (hcont b ρ' hρ0' hρ1' _))).add
      ((hcont a ρ hρ0 hρ1 _).mul (Complex.continuous_conj.comp (hcont (b + 1) ρ' hρ0' hρ1' _)))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ s hs => ?_) hbi
    (Filter.Eventually.of_forall fun ξ s hs => ?_)
  · exact this.2.congr_deriv (integral_add (Iprod_integrable κ hκ Ξ hΞ f hf T (a + 1) b ρ ρ' hρ0 hρ1 hρ0' hρ1' _
      (by positivity)) (Iprod_integrable κ hκ Ξ hΞ f hf T a (b + 1) ρ ρ' hρ0 hρ1 hρ0' hρ1' _ (by positivity)))
  · -- the bound
    have hμ := hμs s hs
    by_cases hm : ξ ∈ K
    · rw [Set.indicator_of_mem hm]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      have e1 := Irho_bound κ hκ Ξ hΞ f hf T (a + 1) ρ hρ0 hρ1 Ma1 hMa1 (Δ * Real.exp s) ξ
      have e2 := Irho_bound κ hκ Ξ hΞ f hf T b ρ' hρ0' hρ1' Mb hMb (Δ * Real.exp s) ξ
      have e3 := Irho_bound κ hκ Ξ hΞ f hf T a ρ hρ0 hρ1 Ma hMa (Δ * Real.exp s) ξ
      have e4 := Irho_bound κ hκ Ξ hΞ f hf T (b + 1) ρ' hρ0' hρ1' Mb1 hMb1 (Δ * Real.exp s) ξ
      exact add_le_add (mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg h10 hMa10))
        (mul_le_mul e3 e4 (norm_nonneg _) (mul_nonneg h10 hMa0))
    · rw [Set.indicator_of_notMem hm,
        Irho_zero_off' κ hκ Ξ hΞ f hf T (a + 1) ρ hρ0 hρ1 μm _ hμm0 hμ ξ hm,
        Irho_zero_off' κ hκ Ξ hΞ f hf T a ρ hρ0 hρ1 μm _ hμm0 hμ ξ hm]
      simp
  · -- the derivative
    have ha := Irho_hasDerivAt_s κ hκ Ξ hΞ f hf T a ρ hρ0 hρ1 Δ ξ s
    have hb := (Irho_hasDerivAt_s κ hκ Ξ hΞ f hf T b ρ' hρ0' hρ1' Δ ξ s).star
    exact ha.mul hb

/-- Cauchy–Schwarz in `ξ`. -/
theorem Qab_sq_le (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (ρ ρ' : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hρ0' : 0 < ρ'.re) (hρ1' : ρ'.re < 1)
    (Δ : ℝ) (hΔ : 0 < Δ) (a b : ℕ) (s : ℝ) :
    ‖Qab T κ Ξ f ρ ρ' Δ a b s‖ ^ 2
      ≤ (∫ ξ, ‖Irho T κ Ξ f a ρ (Δ * Real.exp s) ξ‖ ^ 2) * (∫ ξ, ‖Irho T κ Ξ f b ρ' (Δ * Real.exp s) ξ‖ ^ 2) := by
  set μ := Δ * Real.exp s with hμdef
  have hμ : 0 < μ := by positivity
  set u := fun ξ => ‖Irho T κ Ξ f a ρ μ ξ‖ with hu
  set v := fun ξ => ‖Irho T κ Ξ f b ρ' μ ξ‖ with hv
  have hsq : ∀ (j : ℕ) (r : ℂ), 0 < r.re → r.re < 1 → Integrable (fun ξ => ‖Irho T κ Ξ f j r μ ξ‖ ^ 2) := by
    intro j r h0 h1
    have := Iprod_integrable κ hκ Ξ hΞ f hf T j j r r h0 h1 h0 h1 μ hμ
    refine this.norm.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [norm_mul, Complex.norm_conj, sq]
  have huv : Integrable (fun ξ => u ξ * v ξ) := by
    have := Iprod_integrable κ hκ Ξ hΞ f hf T a b ρ ρ' hρ0 hρ1 hρ0' hρ1' μ hμ
    refine this.norm.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hu, hv, norm_mul, Complex.norm_conj]
  have hA := hsq a ρ hρ0 hρ1
  have hB := hsq b ρ' hρ0' hρ1'
  have hQ : ‖Qab T κ Ξ f ρ ρ' Δ a b s‖ ≤ ∫ ξ, u ξ * v ξ := by
    unfold Qab
    rw [← hμdef]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext ξ; simp only [hu, hv, norm_mul, Complex.norm_conj]
  have hcs := cs_amgm (∫ ξ, u ξ * v ξ) (∫ ξ, u ξ ^ 2) (∫ ξ, v ξ ^ 2)
    (integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (integral_nonneg fun ξ => sq_nonneg _) (integral_nonneg fun ξ => sq_nonneg _) (fun l hl => by
      have hpw : ∀ ξ, 2 * (u ξ * v ξ) ≤ l * u ξ ^ 2 + v ξ ^ 2 / l := fun ξ => by
        have e : l * u ξ ^ 2 + v ξ ^ 2 / l - 2 * (u ξ * v ξ) = (l * u ξ - v ξ) ^ 2 / l := by field_simp; ring
        have : 0 ≤ (l * u ξ - v ξ) ^ 2 / l := div_nonneg (sq_nonneg _) hl.le
        linarith
      calc 2 * (∫ ξ, u ξ * v ξ) = ∫ ξ, 2 * (u ξ * v ξ) := (integral_const_mul _ _).symm
        _ ≤ ∫ ξ, (l * u ξ ^ 2 + v ξ ^ 2 / l) := integral_mono (huv.const_mul 2) ((hA.const_mul l).add (hB.div_const l)) hpw
        _ = l * (∫ ξ, u ξ ^ 2) + (∫ ξ, v ξ ^ 2) / l := by
            rw [integral_add (hA.const_mul l) (hB.div_const l), integral_const_mul, integral_div])
  calc ‖Qab T κ Ξ f ρ ρ' Δ a b s‖ ^ 2 ≤ (∫ ξ, u ξ * v ξ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hQ 2
    _ ≤ (∫ ξ, u ξ ^ 2) * (∫ ξ, v ξ ^ 2) := hcs

end ZetaShell.PropZ
