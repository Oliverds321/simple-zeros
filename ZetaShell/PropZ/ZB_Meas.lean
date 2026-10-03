/-
L7_5 (28 Sep 2026), round 7: `ZB_parts_measurable'` (the statement of the leaf `ZB_parts_measurable`): both parts
are CONTINUOUS in `x`, hence a.e.-strongly measurable.
  * `mellin_cont_line`: `t ↦ Ṽ(c + it)` is continuous (dominated convergence, `Ṽ(w) = ∫ V(e^u) e^{wu} du`);
  * `mellin_Vxs_cont_x`: `x ↦ Ṽ_{x,s}(w)` is continuous (dominated by `sup|f| · |A_s(e^u)| e^{u Re w}`);
  * zero part: `continuous_tsum` with the `x`-uniform majorant `(5/2)(K₀+K₂) m_ρ/(1+|γ_ρ|²)` (summable);
  * remainder: dominated convergence in `t` with the `x`-uniform majorant `M (1+|t|)^{−3/2}`; the digamma term is
    `2π μ_χ(t)`, continuous by the tree's `muq_smooth`.
-/
import ZetaShell.PropZ.ZB_Bounded
import ZetaShell.PropZ.ZR_Digamma

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem mellin_cont_line (V : ℝ → ℂ) (hV : Continuous V) (hVc : HasCompactSupport V)
    (hVpos : tsupport V ⊆ Set.Ioi 1) (c : ℂ) : Continuous (fun t : ℝ => mellin V (c + t * I)) := by
  have e : (fun t : ℝ => mellin V (c + t * I))
      = fun t : ℝ => ∫ u : ℝ, V (Real.exp u) * Complex.exp ((c + t * I) * u) :=
    funext fun t => mellin_eq_integral_phi V hVpos _
  rw [e]
  have hφc := phi_hasCompactSupport V hVc hVpos
  have hφ : Continuous (fun u : ℝ => V (Real.exp u)) := hV.comp Real.continuous_exp
  refine continuous_of_dominated (bound := fun u => ‖V (Real.exp u)‖ * Real.exp (c.re * u))
    (fun t => (hφ.mul (by fun_prop)).aestronglyMeasurable)
    (fun t => Filter.Eventually.of_forall fun u => ?_) ?_ (Filter.Eventually.of_forall fun u => by fun_prop)
  · rw [norm_mul, norm_cexp_mul_ofReal]; simp
  · exact (hφ.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hφc.norm.mul_right

theorem mellin_Vxs_cont_x (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (T Δ s₀ s : ℝ) (hs₀ : 3 ≤ s₀) (hs : |s - s₀| ≤ 1) (w : ℂ) :
    Continuous (fun x => mellin (VxsW T κ Ξ f Δ s x) w) := by
  have e : (fun x => mellin (VxsW T κ Ξ f Δ s x) w)
      = fun x => ∫ u : ℝ, VxsW T κ Ξ f Δ s x (Real.exp u) * Complex.exp (w * u) :=
    funext fun x => mellin_eq_integral_phi _ (VxsW_tsupport_Ioi T κ hκ hκ1 Ξ hΞ f Δ s₀ s x hs₀ hs) w
  rw [e]
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) (hf.supp.trans Set.Ioo_subset_Icc_self)
  obtain ⟨M, hM⟩ := hf.smooth.continuous.bounded_above_of_compact_support hfc
  have hAc : Continuous (As T κ Ξ s) := (As_contDiff T κ hκ Ξ hΞ s).continuous
  have hs1 : 0 < s - κ := by have := (abs_le.mp hs).1; linarith
  have hApos : tsupport (As T κ Ξ s) ⊆ Set.Ioi 1 := by
    refine (As_tsupport T κ hκ Ξ hΞ s).trans fun y hy => ?_
    have := Real.add_one_lt_exp (ne_of_gt hs1)
    exact lt_of_lt_of_le (by linarith) hy.1
  have hAcs : HasCompactSupport (As T κ Ξ s) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (As_tsupport T κ hκ Ξ hΞ s)
  have hφc := phi_hasCompactSupport _ hAcs hApos
  have hφ : Continuous (fun u : ℝ => As T κ Ξ s (Real.exp u)) := hAc.comp Real.continuous_exp
  refine continuous_of_dominated (bound := fun u => ‖As T κ Ξ s (Real.exp u)‖ * M * Real.exp (w.re * u))
    (fun x => (((VxsW_contDiff T κ hκ Ξ hΞ f hf Δ s x).continuous.comp Real.continuous_exp).mul
      (by fun_prop)).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun u => ?_) ?_ (Filter.Eventually.of_forall fun u => ?_)
  · rw [norm_mul, norm_cexp_mul_ofReal]
    unfold VxsW
    rw [norm_mul, Complex.norm_real]
    have h1 := hM (Δ * (Real.exp u - x))
    have h2 := norm_nonneg (As T κ Ξ s (Real.exp u))
    have h3 := Real.exp_pos (w.re * u)
    gcongr
  · exact ((hφ.norm.mul continuous_const).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hφc.norm.mul_right.mul_right)
  · unfold VxsW
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (hf.smooth.continuous.comp
      (by fun_prop)))).mul continuous_const

open scoped Classical in
theorem ZB_parts_measurable' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      AEStronglyMeasurable (fun x => zeroPartW χ T κ Ξ f Δ s x) volume ∧
        AEStronglyMeasurable (fun x => remPartW χ T κ Ξ f Δ s x) volume := by
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
  have hcx := mellin_Vxs_cont_x κ hκ hκ1 Ξ hΞ f hf T Δ s₀ s hs₀ hs
  refine ⟨?_, ?_⟩
  · -- zero part: uniform majorant and `continuous_tsum`
    have hSs := zero_sum_inv_sq r χ hχ
    have hzb : ∀ (ρ : {ρ : ℂ // IsNtZero χ ρ}) (x : ℝ),
        ‖(zmult χ ρ.1 : ℂ) * mellin (VxsW T κ Ξ f Δ s x) ρ.1‖
          ≤ (5 / 2 * (K₀ + K₂)) * ((zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) := by
      intro ρ x
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
    have hcont : Continuous (fun x => zeroPartW χ T κ Ξ f Δ s x) := by
      unfold zeroPartW
      exact continuous_tsum (fun ρ => continuous_const.mul (hcx ρ.1)) (hSs.mul_left _) hzb
    exact hcont.aestronglyMeasurable
  · -- remainder: dominated convergence in `t`
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
    set M := K₂ * C₁ * (8 * (Real.log r + 4)) with hM
    have hgi : Integrable (fun t : ℝ => M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)).const_mul M
    set e : ℕ := (if χ.Even then 0 else 1 : ℕ) with he
    have he1 : e ≤ 1 := by rw [he]; split_ifs <;> norm_num
    have hpt : ∀ (x t : ℝ), ‖mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)
        * (((Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re
            + Real.log (r / Real.pi) : ℝ) : ℂ)‖ ≤ M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
      intro x t
      have hw0 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this
      have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
      have hnw : ‖(1 / 2 + (t : ℂ) * I)‖ ^ 2 = 1 / 4 + t ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
      have h2 := hb2 x (1 / 2 + t * I) (by rw [hre]; norm_num) (by rw [hre]; norm_num) hw0
      rw [hnw] at h2
      have hd := hdig r (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)) e he1 t
      have hlg := log_div_quad_le r hr1 t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hq : 0 < 1 / 4 + t ^ 2 := by positivity
      have habs := abs_nonneg ((Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi))
      calc ‖mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)‖
            * |(Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi)|
          ≤ (K₂ / (1 / 4 + t ^ 2)) * (C₁ * Real.log (r * (|t| + 2))) := mul_le_mul h2 hd habs (by positivity)
        _ = K₂ * C₁ * (Real.log (r * (|t| + 2)) / (1 / 4 + t ^ 2)) := by ring
        _ ≤ K₂ * C₁ * (8 * (Real.log r + 4) * (1 + |t|) ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by rw [Real.norm_eq_abs, hM]; ring
    -- continuity in `t` of the digamma term
    have h2π : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by field_simp
    have hψ : (fun t : ℝ => (Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi))
        = fun t => 2 * Real.pi * Zeta23.ThmE.muq e r t := by
      funext t
      unfold Zeta23.ThmE.muq
      calc (Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi)
          = (2 * Real.pi * (1 / (2 * Real.pi))) * (Real.log (r / Real.pi)
              + (Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re) := by rw [h2π]; ring
        _ = _ := by ring
    have hψc : Continuous (fun t : ℝ => (Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re
        + Real.log (r / Real.pi)) := by
      rw [hψ]; exact continuous_const.mul (Zeta23.ThmE.GammaChi.muq_smooth e r).continuous
    have hint : Continuous (fun x => ∫ t : ℝ, mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)
        * (((Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi) : ℝ) : ℂ)) := by
      refine continuous_of_dominated (bound := fun t => M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)))
        (fun x => ?_) (fun x => Filter.Eventually.of_forall (hpt x)) hgi
        (Filter.Eventually.of_forall fun t => (hcx _).mul continuous_const)
      exact ((mellin_cont_line _ (VxsW_contDiff T κ hκ Ξ hΞ f hf Δ s x).continuous
        (VxsW_hasCompactSupport T κ hκ Ξ hΞ f Δ s x) (VxsW_tsupport_Ioi T κ hκ hκ1 Ξ hΞ f Δ s₀ s x hs₀ hs)
        (1 / 2)).mul (Complex.continuous_ofReal.comp hψc)).aestronglyMeasurable
    have hcont : Continuous (fun x => remPartW χ T κ Ξ f Δ s x) := by
      unfold remPartW
      refine Continuous.add ?_ (continuous_const.mul hint)
      split_ifs
      · exact hcx 0
      · exact continuous_const
    exact hcont.aestronglyMeasurable

end ZetaShell.PropZ
