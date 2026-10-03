/-
Node N3 (track K/T) — used in lem:sigd-tight (l.1312): "k_ψ is decreasing on [0,1]
(k_ψ′(t) = −∫2πσ v_ψ(σ) sin(2πtσ) dσ ≤ 0)", for any continuous ψ > 0 on [−1/2, 1/2].

Proof (L2_2): no derivative is needed. For 0 ≤ x ≤ y ≤ 1 and |s| ≤ 1/2 one has
0 ≤ |2πxs| ≤ |2πys| ≤ π, so cos(2πys) ≤ cos(2πxs) (cos is even and decreasing on [0, π]); multiply by ψ(s) ≥ 0,
integrate over [−1/2, 1/2], and divide by ∫ψ > 0. (Only ψ ≥ 0 on the interval and ∫ψ > 0 are used.)
-/
import ZetaS.Interfaces

open Set

namespace ZetaS

theorem kPsi_antitoneOn {ψ : ℝ → ℝ} (hcont : ContinuousOn ψ (Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (hpos : ∀ s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), 0 < ψ s) :
    AntitoneOn (kPsi ψ) (Icc 0 1) := by
  have hab : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  have huIcc : uIcc (-(1 / 2 : ℝ)) (1 / 2) = Icc (-(1 / 2 : ℝ)) (1 / 2) := uIcc_of_le hab
  -- integrability of ψ · cos(2π x ·)
  have hint : ∀ x : ℝ, IntervalIntegrable (fun s => ψ s * Real.cos (2 * Real.pi * x * s))
      MeasureTheory.volume (-(1 / 2 : ℝ)) (1 / 2) := by
    intro x
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hcont.mul (Continuous.continuousOn (by fun_prop))
  have hintψ : IntervalIntegrable ψ MeasureTheory.volume (-(1 / 2 : ℝ)) (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hcont
  -- positivity of the normalisation
  have hden : 0 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hintψ
    · intro s hs
      exact hpos s (Ioo_subset_Icc_self hs)
    · norm_num
  intro x hx y hy hxy
  unfold kPsi
  rw [div_le_div_iff_of_pos_right hden]
  apply intervalIntegral.integral_mono_on hab (hint y) (hint x)
  intro s hs
  have hψ : 0 ≤ ψ s := (hpos s hs).le
  apply mul_le_mul_of_nonneg_left _ hψ
  -- cos(2π y s) ≤ cos(2π x s)
  have hsabs : |s| ≤ 1 / 2 := abs_le.2 ⟨hs.1, hs.2⟩
  have hx0 : 0 ≤ x := hx.1
  have hy1 : y ≤ 1 := hy.2
  have hpi : 0 < Real.pi := Real.pi_pos
  have e1 : |2 * Real.pi * x * s| = 2 * Real.pi * x * |s| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * x)]
  have e2 : |2 * Real.pi * y * s| = 2 * Real.pi * y * |s| := by
    rw [abs_mul, abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 2 * Real.pi * y)]
  rw [← Real.cos_abs (2 * Real.pi * y * s), ← Real.cos_abs (2 * Real.pi * x * s), e1, e2]
  have hs0 : 0 ≤ |s| := abs_nonneg s
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · -- 2π y |s| ≤ π
    have : y * |s| ≤ 1 / 2 := by nlinarith
    nlinarith
  · -- 2π x |s| ≤ 2π y |s|
    have : x * |s| ≤ y * |s| := mul_le_mul_of_nonneg_right hxy hs0
    nlinarith

end ZetaS
