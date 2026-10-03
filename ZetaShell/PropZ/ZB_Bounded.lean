/-
L7_5 (28 Sep 2026), round 4: `ZB_parts_bounded` (both parts bounded in `x`), PROVED from the shared estimates
(`mellin_Vxs_bounds` ← `MellinDecay` + leaf `ZR_phi_bounds`), the leaf `ZR_digamma`, and `zero_sum_inv_sq`
(proved, round 3). Zero part: `‖Ṽ(ρ)‖ ≤ min(K₀, K₂/‖ρ‖²) ≤ (5/2)(K₀+K₂)/(1+|γ_ρ|²)`, summed with the zero count.
Remainder: `‖Ṽ(1/2+it)‖·|w_r(t)| ≤ K₂C₁ log(r(|t|+2))/(1/4+t²) ≤ 8K₂C₁(log r+4)(1+|t|)^{−3/2}`, integrable.
-/
import ZetaShell.PropZ.ZR_Mellin
import ZetaShell.PropZ.ZZ4_Count

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem log_div_quad_le (r : ℝ) (hr : 1 ≤ r) (t : ℝ) :
    Real.log (r * (|t| + 2)) / (1 / 4 + t ^ 2) ≤ 8 * (Real.log r + 4) * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
  set a := 1 + |t| with ha
  have ha1 : 1 ≤ a := by have := abs_nonneg t; linarith
  have ha0 : 0 < a := by linarith
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hsq : 1 ≤ a ^ (1 / 2 : ℝ) := Real.one_le_rpow ha1 (by norm_num)
  have hlog2 : Real.log (|t| + 2) ≤ 4 * a ^ (1 / 2 : ℝ) := by
    have h1 := Real.log_le_rpow_div (x := |t| + 2) (ε := 1 / 2) (by positivity) (by norm_num)
    have h2 : (|t| + 2) ^ (1 / 2 : ℝ) ≤ (2 * a) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have h3 : (2 * a) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) ha0.le
    have h4 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h5 : 0 ≤ a ^ (1 / 2 : ℝ) := by positivity
    nlinarith
  have hnum : Real.log (r * (|t| + 2)) ≤ (Real.log r + 4) * a ^ (1 / 2 : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    nlinarith
  have hden : a ^ 2 / 8 ≤ 1 / 4 + t ^ 2 := by
    have : a ^ 2 = 1 + 2 * |t| + t ^ 2 := by rw [ha, ← sq_abs t]; ring
    rw [this]
    nlinarith [sq_nonneg (|t| - 1 / 7), abs_nonneg t, sq_abs t]
  have hpow : a ^ (1 / 2 : ℝ) / a ^ 2 = a ^ (-(3 / 2 : ℝ)) := by
    rw [show (-(3 / 2 : ℝ)) = 1 / 2 - 2 by norm_num, Real.rpow_sub ha0, Real.rpow_two]
  have hq : 0 < 1 / 4 + t ^ 2 := by positivity
  calc Real.log (r * (|t| + 2)) / (1 / 4 + t ^ 2)
      ≤ (Real.log r + 4) * a ^ (1 / 2 : ℝ) / (a ^ 2 / 8) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 8 * (Real.log r + 4) * (a ^ (1 / 2 : ℝ) / a ^ 2) := by field_simp
    _ = 8 * (Real.log r + 4) * a ^ (-(3 / 2 : ℝ)) := by rw [hpow]

open scoped Classical in
theorem ZB_parts_bounded' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∃ C : ℝ, ∀ x : ℝ, ‖zeroPartW χ T κ Ξ f Δ s x‖ ≤ C ∧ ‖remPartW χ T κ Ξ f Δ s x‖ ≤ C := by
  intro s₀ T Δ s hs₀ hT hΔ hΔ1 hs r _ χ hχ
  obtain ⟨C, hC0, hC⟩ := mellin_Vxs_bounds κ hκ hκ1 Ξ hΞ f hf
  obtain ⟨C₁, hC₁0, hdig⟩ := ZR_digamma
  have hN1 : 1 ≤ Real.exp s := Real.one_le_exp (by have := (abs_le.mp hs).1; linarith)
  have hN0 : 0 < Real.exp s := Real.exp_pos s
  have hm0 : 0 ≤ min (1 / Δ) (Real.exp s) := le_min (by positivity) hN0.le
  have hexp : ∀ a : ℝ, a ≤ 1 → Real.exp s ^ (a - 1 / 2) ≤ Real.exp s ^ (1 / 2 : ℝ) := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hT0 : 0 ≤ T := by linarith
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = C * T * Real.exp s ^ (1 / 2 : ℝ) * min (1 / Δ) (Real.exp s) / Real.exp s :=
    ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp s ^ (1 / 2 : ℝ)
      * min (1 / Δ) (Real.exp s) / Real.exp s := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  -- the two Mellin bounds in simplified form
  have hb0 : ∀ (x : ℝ) (w : ℂ), 0 ≤ w.re → w.re ≤ 1 → ‖mellin (VxsW T κ Ξ f Δ s x) w‖ ≤ K₀ := by
    intro x w h0 h1
    refine (hC s₀ T Δ s hs₀ hT hΔ hΔ1 hs x w h0 h1).1.trans ?_
    rw [hK₀]
    gcongr
    linarith
  have hb2 : ∀ (x : ℝ) (w : ℂ), 0 ≤ w.re → w.re ≤ 1 → w ≠ 0 →
      ‖mellin (VxsW T κ Ξ f Δ s x) w‖ ≤ K₂ / ‖w‖ ^ 2 := by
    intro x w h0 h1 hw
    refine ((hC s₀ T Δ s hs₀ hT hΔ hΔ1 hs x w h0 h1).2 hw).trans ?_
    rw [div_eq_mul_one_div K₂, mul_comm K₂, hK₂]
    gcongr
    linarith
  -- zero part
  set S := ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1)) with hS
  have hSs := zero_sum_inv_sq r χ hχ
  have hzb : ∀ (x : ℝ) (ρ : {ρ : ℂ // IsNtZero χ ρ}),
      ‖(zmult χ ρ.1 : ℂ) * mellin (VxsW T κ Ξ f Δ s x) ρ.1‖
        ≤ (5 / 2 * (K₀ + K₂)) * ((zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) := by
    intro x ρ
    have hρ := ρ.2
    have hre0 : 0 ≤ ρ.1.re := hρ.2.1.le
    have hre1 : ρ.1.re ≤ 1 := hρ.2.2.le
    have hρ0 : ρ.1 ≠ 0 := fun h => by
      have := hρ.2.1; rw [h] at this; simp at this
    have hns : Complex.normSq (Zeta23.gammaOf ρ.1) ≤ ρ.1.im ^ 2 + 1 / 4 := by
      rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
      nlinarith [hρ.2.1, hρ.2.2]
    have hnρ : ρ.1.im ^ 2 ≤ ‖ρ.1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [sq_nonneg ρ.1.re]
    have hpos : 0 < 1 + Complex.normSq (Zeta23.gammaOf ρ.1) := by
      have := Complex.normSq_nonneg (Zeta23.gammaOf ρ.1); linarith
    have hV : ‖mellin (VxsW T κ Ξ f Δ s x) ρ.1‖
        ≤ 5 / 2 * (K₀ + K₂) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1)) := by
      rw [le_div_iff₀ hpos]
      rcases le_or_gt 1 (ρ.1.im ^ 2) with hg | hg
      · have h2 := hb2 x ρ.1 hre0 hre1 hρ0
        have hn2 : 0 < ‖ρ.1‖ ^ 2 := by positivity
        have : ‖mellin (VxsW T κ Ξ f Δ s x) ρ.1‖ * ‖ρ.1‖ ^ 2 ≤ K₂ := by
          rw [le_div_iff₀ hn2] at h2; exact h2
        have hmn := norm_nonneg (mellin (VxsW T κ Ξ f Δ s x) ρ.1)
        nlinarith
      · have h0 := hb0 x ρ.1 hre0 hre1
        have hmn := norm_nonneg (mellin (VxsW T κ Ξ f Δ s x) ρ.1)
        nlinarith
    rw [norm_mul, Complex.norm_natCast]
    calc (zmult χ ρ.1 : ℝ) * ‖mellin (VxsW T κ Ξ f Δ s x) ρ.1‖
        ≤ (zmult χ ρ.1 : ℝ) * (5 / 2 * (K₀ + K₂) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) :=
          mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)
      _ = _ := by ring
  have hzs : ∀ x : ℝ, ‖zeroPartW χ T κ Ξ f Δ s x‖ ≤ 5 / 2 * (K₀ + K₂) * S := by
    intro x
    have hmaj : Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} =>
        (5 / 2 * (K₀ + K₂)) * ((zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1)))) :=
      hSs.mul_left _
    have hnorm : Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} =>
        ‖(zmult χ ρ.1 : ℂ) * mellin (VxsW T κ Ξ f Δ s x) ρ.1‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hzb x) hmaj
    calc ‖zeroPartW χ T κ Ξ f Δ s x‖ ≤ ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
          ‖(zmult χ ρ.1 : ℂ) * mellin (VxsW T κ Ξ f Δ s x) ρ.1‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
          (5 / 2 * (K₀ + K₂)) * ((zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) :=
          hnorm.tsum_le_tsum (hzb x) hmaj
      _ = 5 / 2 * (K₀ + K₂) * S := tsum_mul_left
  -- remainder part
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  set M := K₂ * C₁ * (8 * (Real.log r + 4)) with hM
  have hM0 : 0 ≤ M := by have := Real.log_nonneg hr1; positivity
  have hgi : Integrable (fun t : ℝ => M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)).const_mul M
  have hpt : ∀ (x t : ℝ), ‖mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)
      * (((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
          + Real.log (r / Real.pi) : ℝ) : ℂ)‖ ≤ M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
    intro x t
    have hw0 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
    have hnw : ‖(1 / 2 + (t : ℂ) * I)‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have h2 := hb2 x (1 / 2 + t * I) (by rw [hre]; norm_num) (by rw [hre]; norm_num) hw0
    rw [hnw] at h2
    have hd := hdig r (by exact_mod_cast hr1) (if χ.Even then 0 else 1) (by split_ifs <;> norm_num) t
    have hlg := log_div_quad_le r hr1 t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hq : 0 < 1 / 4 + t ^ 2 := by positivity
    have hmn := norm_nonneg (mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I))
    have habs := abs_nonneg ((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
          + Real.log (r / Real.pi))
    calc ‖mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)‖
          * |(Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
            + Real.log (r / Real.pi)|
        ≤ (K₂ / (1 / 4 + t ^ 2)) * (C₁ * Real.log (r * (|t| + 2))) := mul_le_mul h2 hd habs (by positivity)
      _ = K₂ * C₁ * (Real.log (r * (|t| + 2)) / (1 / 4 + t ^ 2)) := by ring
      _ ≤ K₂ * C₁ * (8 * (Real.log r + 4) * (1 + |t|) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by rw [Real.norm_eq_abs, hM]; ring
  have hrs : ∀ x : ℝ, ‖remPartW χ T κ Ξ f Δ s x‖ ≤ K₀ + 1 / (2 * Real.pi) * ∫ t : ℝ, M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
    intro x
    unfold remPartW
    refine (norm_add_le _ _).trans ?_
    gcongr
    · split_ifs
      · exact hb0 x 0 (by simp) (by simp)
      · simpa using hK₀0
    · rw [norm_mul]
      have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
        rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        simp
      rw [hc]
      gcongr
      exact norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall (hpt x))
  refine ⟨max (5 / 2 * (K₀ + K₂) * S) (K₀ + 1 / (2 * Real.pi) * ∫ t : ℝ, M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))),
    fun x => ⟨(hzs x).trans (le_max_left _ _), (hrs x).trans (le_max_right _ _)⟩⟩

end ZetaShell.PropZ
