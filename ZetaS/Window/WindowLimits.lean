/-
rh72/lean_work/L0_2/WindowLimits.lean — node W8 instantiated: the ratio limit for the two draft windows, with the
limit identified with the exact constants.
  * poly8A (ψ♮ = (4/5)v): cRatio(λ₁(T); a_T, b_T, J_T) → ThmD.cRatio λ a b J with the exact rationals a, b, J of v
    (PolyWindow: integral_vP8, integral_vP8_sq, jP8), and 2 − 1/ThmD.cRatio 1 a b J = H(ψ̃) = 26957030199857/40103091391077.
  * cos(α s), 0 < α ≤ 8/5: cRatio(…) → ThmD.cRatio λ a(α) b(α) J(α), with (ψ⋆ψ)(r) and J(α) = (sin α − α cos α)/α³ in
    closed form, and 2 − 1/ThmD.cRatio 1 a b J = H(α) (CosWindow.HC; enclosure of H(8/5) there).
No `sorry`.
-/
import ZetaS.Window.PolyWindow
import ZetaS.Window.CosWindow
import ZetaS.Window.ProfileAutocorr
import ZetaS.Window.WindowInstances

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace ZetaS
namespace WindowLimits

open Zeta23 Zeta23.XiPrime ZetaS.ProfileMoments ZetaS.ProfileAutocorr

/-! ## poly8A -/

theorem vConv_psiN (r : ℝ) : vConv PolyWindow.psiN r = 16 / 25 * vConv PolyWindow.vP8 r := by
  unfold vConv PolyWindow.psiN
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- `𝒥_id(λ; ψ♮) = λ·(16/25)·J(v)`. -/
theorem jWin_psiN (lam : ℝ) :
    jWin id lam PolyWindow.psiN = lam * (16 / 25) * (166041852098299 / 606230625000000) := by
  unfold jWin
  have h : (fun r => id (lam * r) * vConv PolyWindow.psiN r)
      = fun r => lam * (16 / 25) * (r * vConv PolyWindow.vP8 r) := by
    funext r; rw [vConv_psiN]; simp only [id]; ring
  rw [h, intervalIntegral.integral_const_mul, ← PolyWindow.jP8]
  ring

/-- `c_λ(ψ♮) = ThmD.cRatio λ a b J` with the exact moments of v (degree-0 homogeneity). -/
theorem cWin_psiN {lam : ℝ} (h0 : 0 < lam) :
    cWin id lam PolyWindow.psiN
      = ThmD.cRatio lam (40497 / 43750) (16536677606497 / 19144125000000) (166041852098299 / 606230625000000) := by
  unfold cWin ThmD.cRatio
  rw [PolyWindow.integral_psiN, PolyWindow.integral_psiN_sq, jWin_psiN]
  field_simp
  ring

/-- **W8 for poly8A.** -/
theorem tendsto_cRatioP8 {P : Params} (hP : P.Valid) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) (AdmWindow.av (P.phiV PolyWindow.psiN T) (P.L T))
      (AdmWindow.bv (P.phiV PolyWindow.psiN T) (P.L T)) (JTV P PolyWindow.psiN T)) atTop
      (𝓝 (ThmD.cRatio P.lam (40497 / 43750) (16536677606497 / 19144125000000)
        (166041852098299 / 606230625000000))) := by
  rw [← cWin_psiN hP.lam_pos]
  refine tendsto_cRatioV hP WindowInstances.coreProfile_psiN
    (fun T hT => by rw [PolyWindow.phiV_eq_phiP8]; exact PolyWindow.admWindow_phiP8 hP.taper hP.one_le_w hT) ?_
  rw [PolyWindow.integral_psiN_sq, jWin_psiN]
  have := hP.lam_pos
  positivity

/-- at bandwidth one the limit constant is the draft's: `2 − 1/cRatio(1; a, b, J) = H(ψ̃)`. -/
theorem HD_P8 :
    2 - 1 / ThmD.cRatio 1 (40497 / 43750) (16536677606497 / 19144125000000) (166041852098299 / 606230625000000)
      = 26957030199857 / 40103091391077 := by
  unfold ThmD.cRatio; norm_num

/-! ## cos(α s) -/

/-- **W8 for the cosine windows** (limit `c_λ(cos α·)`; its closed form is node W8c). -/
theorem tendsto_cRatioCos {P : Params} (hP : P.Valid) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5)
    (hJ : 0 ≤ jWin id P.lam (CosWindow.cosW α)) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) (AdmWindow.av (P.phiV (CosWindow.cosW α) T) (P.L T))
      (AdmWindow.bv (P.phiV (CosWindow.cosW α) T) (P.L T)) (JTV P (CosWindow.cosW α) T)) atTop
      (𝓝 (cWin id P.lam (CosWindow.cosW α))) := by
  refine tendsto_cRatioV hP (WindowInstances.coreProfile_cosW hα0 hα1)
    (fun T hT => CosWindow.admWindow_phiV_cos hP hα0 hα1 hT) ?_
  rw [WindowInstances.half_interval, CosWindow.integral_cosW_sq hα0.ne']
  have := WindowInstances.half_lt_bC hα0 hα1
  have := hP.lam_pos
  positivity

/-! ### W8c: the closed forms `(ψ_α⋆ψ_α)(r) = (1−r)cos(αr)/2 + sin(α(1−r))/(2α)` and `J(α) = (sin α − α cos α)/α³` -/

theorem vConv_cosW {α : ℝ} (hα : α ≠ 0) (r : ℝ) :
    vConv (CosWindow.cosW α) r = (1 - r) * Real.cos (α * r) / 2 + Real.sin (α * (1 - r)) / (2 * α) := by
  unfold vConv CosWindow.cosW
  have hF : ∀ s, HasDerivAt (fun s => s * Real.cos (α * r) / 2 + Real.sin (α * (2 * s + r)) / (4 * α))
      (Real.cos (α * s) * Real.cos (α * (s + r))) s := by
    intro s
    have hlin : HasDerivAt (fun s : ℝ => α * (2 * s + r)) (α * (2 * 1)) s :=
      (((hasDerivAt_id s).const_mul 2).add_const r).const_mul α
    have h1 := (((hasDerivAt_id s).mul_const (Real.cos (α * r))).div_const 2).add
      (((Real.hasDerivAt_sin (α * (2 * s + r))).comp s hlin).div_const (4 * α))
    refine h1.congr_deriv ?_
    have e1 : Real.cos (α * r) = Real.cos (α * (s + r) - α * s) := by ring_nf
    have e2 : Real.cos (α * (2 * s + r)) = Real.cos (α * s + α * (s + r)) := by ring_nf
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [show α * (2 * (1 / 2 - r) + r) = α * (1 - r) by ring,
    show α * (2 * (-(1:ℝ) / 2) + r) = -(α * (1 - r)) by ring, Real.sin_neg]
  field_simp
  ring

theorem jC_eq {α : ℝ} (hα : α ≠ 0) : CosWindow.jC α = (Real.sin α - α * Real.cos α) / α ^ 3 := by
  unfold CosWindow.jC CosWindow.aC CosWindow.bC
  have hs : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    have h := Real.sin_two_mul (α / 2)
    rw [show 2 * (α / 2) = α by ring] at h
    exact h
  have hc : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
    have h := Real.cos_two_mul (α / 2)
    rw [show 2 * (α / 2) = α by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (α / 2)]
  rw [hs, hc]
  field_simp
  ring

/-- **`2∫₀¹ r (ψ_α⋆ψ_α)(r) dr = J(α)`** (= ∬|u−v|ψ_α(u)ψ_α(v), `CosWindow.jInt_cosW`). -/
theorem jvConv_cosW {α : ℝ} (hα : α ≠ 0) :
    2 * ∫ r in (0:ℝ)..1, r * vConv (CosWindow.cosW α) r = CosWindow.jC α := by
  rw [jC_eq hα]
  have hG : ∀ r, HasDerivAt (fun r => (-α ^ 2 * (r ^ 2 * Real.sin (α * r)) + α ^ 2 * (r * Real.sin (α * r))
        - 2 * α * (r * Real.cos (α * r)) + α * (r * Real.cos (α * (r - 1))) + α * Real.cos (α * r)
        + 2 * Real.sin (α * r) - Real.sin (α * (r - 1))) / (2 * α ^ 3))
      (r * ((1 - r) * Real.cos (α * r) / 2 + Real.sin (α * (1 - r)) / (2 * α))) r := by
    intro r
    have hl : HasDerivAt (fun r : ℝ => α * r) (α * 1) r := (hasDerivAt_id r).const_mul α
    have hl1 : HasDerivAt (fun r : ℝ => α * (r - 1)) (α * 1) r := ((hasDerivAt_id r).sub_const 1).const_mul α
    have hS := (Real.hasDerivAt_sin (α * r)).comp r hl
    have hC := (Real.hasDerivAt_cos (α * r)).comp r hl
    have hS1 := (Real.hasDerivAt_sin (α * (r - 1))).comp r hl1
    have hC1 := (Real.hasDerivAt_cos (α * (r - 1))).comp r hl1
    have ht1 := (hasDerivAt_pow 2 r).mul hS
    have ht2 := (hasDerivAt_id r).mul hS
    have ht3 := (hasDerivAt_id r).mul hC
    have ht4 := (hasDerivAt_id r).mul hC1
    have h := (((((((ht1.const_mul (-α ^ 2)).add (ht2.const_mul (α ^ 2))).sub (ht3.const_mul (2 * α))).add
      (ht4.const_mul α)).add (hC.const_mul α)).add (hS.const_mul 2)).sub hS1).div_const (2 * α ^ 3)
    refine h.congr_deriv ?_
    simp only [Function.comp_def, id]
    rw [show α * (1 - r) = -(α * (r - 1)) by ring, Real.sin_neg]
    field_simp
    ring
  rw [intervalIntegral.integral_congr (fun r _ => by rw [vConv_cosW hα r]),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hG r)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [sub_self, mul_zero, zero_sub, one_mul, mul_one, Real.cos_zero, Real.sin_zero,
    zero_mul, zero_add, pow_two]
  rw [show α * -1 = -α by ring, Real.sin_neg]
  field_simp
  ring

/-- `c_λ(ψ_α) = ThmD.cRatio λ a(α) b(α) J(α)`. -/
theorem cWin_cosW {α lam : ℝ} (hα : α ≠ 0) (h0 : 0 < lam) :
    cWin id lam (CosWindow.cosW α) = ThmD.cRatio lam (CosWindow.aC α) (CosWindow.bC α) (CosWindow.jC α) := by
  have hj : jWin id lam (CosWindow.cosW α) = lam * CosWindow.jC α := by
    unfold jWin
    rw [← jvConv_cosW hα]
    have h : (fun r => id (lam * r) * vConv (CosWindow.cosW α) r)
        = fun r => lam * (r * vConv (CosWindow.cosW α) r) := by funext r; simp only [id]; ring
    rw [h, intervalIntegral.integral_const_mul]; ring
  unfold cWin ThmD.cRatio
  rw [WindowInstances.half_interval, CosWindow.integral_cosW hα, CosWindow.integral_cosW_sq hα, hj]
  field_simp

/-- **W8 for the cosine windows, with the exact limit** `cRatio(λ; a(α), b(α), J(α))`. -/
theorem tendsto_cRatioCos' {P : Params} (hP : P.Valid) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) (AdmWindow.av (P.phiV (CosWindow.cosW α) T) (P.L T))
      (AdmWindow.bv (P.phiV (CosWindow.cosW α) T) (P.L T)) (JTV P (CosWindow.cosW α) T)) atTop
      (𝓝 (ThmD.cRatio P.lam (CosWindow.aC α) (CosWindow.bC α) (CosWindow.jC α))) := by
  rw [← cWin_cosW hα0.ne' hP.lam_pos]
  refine tendsto_cRatioCos hP hα0 hα1 ?_
  have hj : jWin id P.lam (CosWindow.cosW α) = P.lam * CosWindow.jC α := by
    unfold jWin
    rw [← jvConv_cosW hα0.ne']
    have h : (fun r => id (P.lam * r) * vConv (CosWindow.cosW α) r)
        = fun r => P.lam * (r * vConv (CosWindow.cosW α) r) := by funext r; simp only [id]; ring
    rw [h, intervalIntegral.integral_const_mul]; ring
  rw [hj, ← CosWindow.jInt_cosW hα0.ne']
  have hcore := WindowInstances.coreProfile_cosW hα0 hα1
  apply mul_nonneg hP.lam_pos.le
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro v hv
  have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
  have hv' : |v| ≤ 1 / 2 := abs_le.mpr ⟨hv.1, hv.2⟩
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (hcore.nonneg u hu')) (hcore.nonneg v hv')

/-- at bandwidth one: `2 − 1/cRatio(1; a(α), b(α), J(α)) = H(α)` (so, with `CosWindow.HC_eight_fifths`,
the limit constant of the cosine window is the draft's `H(cos 1.6 s)`). -/
theorem HD_cos {α : ℝ} (ha : CosWindow.aC α ≠ 0) :
    2 - 1 / ThmD.cRatio 1 (CosWindow.aC α) (CosWindow.bC α) (CosWindow.jC α) = CosWindow.HC α := by
  unfold ThmD.cRatio CosWindow.HC
  field_simp

end WindowLimits
end ZetaS

end

#print axioms ZetaS.WindowLimits.cWin_psiN
#print axioms ZetaS.WindowLimits.tendsto_cRatioP8
#print axioms ZetaS.WindowLimits.HD_P8
#print axioms ZetaS.WindowLimits.tendsto_cRatioCos
#print axioms ZetaS.WindowLimits.vConv_cosW
#print axioms ZetaS.WindowLimits.jvConv_cosW
#print axioms ZetaS.WindowLimits.cWin_cosW
#print axioms ZetaS.WindowLimits.tendsto_cRatioCos'
#print axioms ZetaS.WindowLimits.HD_cos
