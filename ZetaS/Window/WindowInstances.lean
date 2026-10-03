/-
rh72/lean_work/L0_2/WindowInstances.lean — nodes W5/W7 instantiated for the two windows of the draft:
  * poly8A in the admissible normalisation ψ♮ = (4/5)v (thm:zeta-mainw2; PolyWindow.lean),
  * cos(α s), 0 < α ≤ 8/5 (α = 8/5: thm:zeta-allmarks, thm:sigd-Sigma/D; α = 37/25: thm:zeta-mainw; CosWindow.lean).
For each: |a_T − a| ≤ 2w/L, |b_T − b| ≤ 2w/L with the exact a, b, and the §5 `LocalHypsCore` for all large T.
Imports the author's own modules PolyWindow, CosWindow, ProfileMoments (compiled with `leanrun.sh … -o`).
No `sorry`.
-/
import ZetaS.Window.PolyWindow
import ZetaS.Window.CosWindow
import ZetaS.Window.ProfileMoments

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace ZetaS
namespace WindowInstances

open Zeta23 Zeta23.XiPrime ZetaS.ProfileMoments

/-! ## poly8A (ψ♮ = (4/5)v) -/

theorem coreProfile_psiN : CoreProfile PolyWindow.psiN where
  cont := PolyWindow.psiN_continuous
  nonneg := fun s _ => (PolyWindow.psiN_pos s).le
  le_one := fun s hs => PolyWindow.psiN_le_one s hs

theorem aP8_close {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.av (P.phiV PolyWindow.psiN T) (P.L T) - 4 / 5 * (40497 / 43750)| ≤ 2 * P.w / P.L T := by
  rw [← PolyWindow.integral_psiN, phiV_eq_phiM]
  exact av_close coreProfile_psiN hP.taper hP.one_le_w hwL

theorem bP8_close {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.bv (P.phiV PolyWindow.psiN T) (P.L T) - 16 / 25 * (16536677606497 / 19144125000000)|
      ≤ 2 * P.w / P.L T := by
  rw [← PolyWindow.integral_psiN_sq, phiV_eq_phiM]
  exact bv_close coreProfile_psiN hP.taper hP.one_le_w hwL

/-- **W7 for poly8A.** -/
theorem localHypsCoreP8_eventually {P : Params} (hP : P.Valid) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      PrimeSide.LocalHypsCore (PolyWindow.cP8 P.ϱ) (P.toSetting T)
        (AdmWindow.localFun (P.phiV PolyWindow.psiN T) (P.L T)) :=
  localHypsCore_eventually hP coreProfile_psiN (K := 8) le_rfl
    (fun T hT => by
      rw [PolyWindow.phiV_eq_phiP8]
      exact PolyWindow.admWindow_phiP8 hP.taper hP.one_le_w hT)
    (by rw [PolyWindow.integral_psiN_sq]; norm_num)

/-! ## cos(α s), 0 < α ≤ 8/5 -/

theorem coreProfile_cosW {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) : CoreProfile (CosWindow.cosW α) where
  cont := by unfold CosWindow.cosW; fun_prop
  nonneg := fun s hs => by
    unfold CosWindow.cosW
    have hb : |α * s| ≤ 4 / 5 := by
      rw [abs_mul, abs_of_pos hα0]
      calc α * |s| ≤ 8 / 5 * (1 / 2) := mul_le_mul hα1 hs (abs_nonneg s) (by norm_num)
        _ = 4 / 5 := by norm_num
    have hpi := Real.pi_gt_three
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [neg_abs_le (α * s), le_abs_self (α * s)]
  le_one := fun s _ => Real.cos_le_one _

theorem half_interval : (-(1:ℝ) / 2) = -(1 / 2) := by norm_num

theorem aCos_close {P : Params} (hP : P.Valid) {T : ℝ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5)
    (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.av (P.phiV (CosWindow.cosW α) T) (P.L T) - CosWindow.aC α| ≤ 2 * P.w / P.L T := by
  rw [← CosWindow.integral_cosW hα0.ne', ← half_interval, phiV_eq_phiM]
  exact av_close (coreProfile_cosW hα0 hα1) hP.taper hP.one_le_w hwL

theorem bCos_close {P : Params} (hP : P.Valid) {T : ℝ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5)
    (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.bv (P.phiV (CosWindow.cosW α) T) (P.L T) - CosWindow.bC α| ≤ 2 * P.w / P.L T := by
  rw [← CosWindow.integral_cosW_sq hα0.ne', ← half_interval, phiV_eq_phiM]
  exact bv_close (coreProfile_cosW hα0 hα1) hP.taper hP.one_le_w hwL

theorem half_lt_bC {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) : 1 / 2 < CosWindow.bC α := by
  unfold CosWindow.bC
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_gt_three])
  have : 0 < Real.sin α / (2 * α) := by positivity
  linarith

/-- **W7 for the cosine windows.** -/
theorem localHypsCoreCos_eventually {P : Params} (hP : P.Valid) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      PrimeSide.LocalHypsCore (CosWindow.cCos P.ϱ) (P.toSetting T)
        (AdmWindow.localFun (P.phiV (CosWindow.cosW α) T) (P.L T)) :=
  localHypsCore_eventually hP (coreProfile_cosW hα0 hα1) (K := 8) le_rfl
    (fun T hT => CosWindow.admWindow_phiV_cos hP hα0 hα1 hT)
    (by rw [half_interval, CosWindow.integral_cosW_sq hα0.ne']; exact half_lt_bC hα0 hα1)

end WindowInstances
end ZetaS

end

#print axioms ZetaS.WindowInstances.aP8_close
#print axioms ZetaS.WindowInstances.bP8_close
#print axioms ZetaS.WindowInstances.localHypsCoreP8_eventually
#print axioms ZetaS.WindowInstances.aCos_close
#print axioms ZetaS.WindowInstances.bCos_close
#print axioms ZetaS.WindowInstances.localHypsCoreCos_eventually
