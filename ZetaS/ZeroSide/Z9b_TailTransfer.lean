/-
Sub-node Z9b (agent L3_1) — "all zeros versus I′" (L0_2c §4): W9.8 (`GramV.gram_asymptotics_V`, for
Ĝ = hat(Gz), all zeros) transferred to the window matrix hat(Az) through the tree's tail inputs
(`XiPrime.eventually_tailPackageV_of`: |tr Ê| ≤ B, ‖Ê‖²_F ≤ B², B ≤ θ₀/(aL) → 0, Gz = Az + Ez), and the
nondegeneracy ∫φ_T² ≠ 0 eventually (a_V ≥ 1/2 eventually, as in `HeadlineV.simple_V_lam_abstract`).
-/
import ZetaS.ZeroSide.Z9s_Spec
import ZetaS.Window.GramV
import ZetaS.ZeroSide.Z9b0_Asymp

noncomputable section

open Filter Asymptotics Topology RHLinalg

namespace ZetaS
namespace Z9

open Zeta23

variable (Z : ZeroConfig) (H : PaperInputs Z) {P : Params} (hP : P.Valid) (hlam : P.lam < 1) {ψ : ℝ → ℝ}
  (heven : ∀ s, ψ (-s) = ψ s) (hcont : Continuous ψ) (hcore : ∀ s, |s| ≤ 1 / 2 → 0 ≤ ψ s ∧ ψ s ≤ 1) {c : ℝ}
  (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV ψ T) (P.L T) P.w c)
  (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s) (hb : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s ^ 2)
include hP heven hcont hcore hadm hb

/-- `a_V(T) ≥ 1/2` eventually (from `ProfileMoments.bv_ge_half` and `b ≤ a`). -/
theorem eventually_a_ge_half : ∀ᶠ T in atTop, 1 / 2 ≤ (P.atV ψ T).a T := by
  have hv : ProfileMoments.CoreProfile ψ := ⟨hcont, fun s hs => (hcore s hs).1, fun s hs => (hcore s hs).2⟩
  have hb' : 1 / 2 < ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ψ s ^ 2 := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by norm_num]; exact hb
  filter_upwards [Params.eventually_w8 hP, (Params.tendsto_L_of_valid hP).eventually_ge_atTop
    (2 * P.w / ((∫ s in (-(1 : ℝ) / 2)..(1 / 2), ψ s ^ 2) - 1 / 2))] with T h8 hLb
  have hW := hadm T h8
  have hb2 : 1 / 2 ≤ AdmWindow.bv (P.phiV ψ T) (P.L T) :=
    ProfileMoments.bv_ge_half hv hP.taper hP.one_le_w h8 hb' hLb
  rw [Params.atV_a T hP heven]
  linarith [hW.bv_le_av]

/-- `∫ φ_T² ≠ 0` eventually (indeed `a_V(T) ≥ 1/2`). -/
theorem eventually_int_sq_ne_zero : ∀ᶠ T in atTop, (∫ u, P.phiV ψ T u ^ 2) ≠ 0 := by
  filter_upwards [eventually_a_ge_half hP heven hcont hcore hadm hb, Params.eventually_w8 hP] with T ha h8
  rw [Params.atV_a T hP heven] at ha
  have hL0 := (hadm T h8).L_pos
  intro h0
  have : AdmWindow.av (P.phiV ψ T) (P.L T) = 0 := by simp [AdmWindow.av, h0]
  linarith

include H hlam ha in
/-- W9.8 on the window matrix hat(Az). -/
theorem hatAz_asymptotics (hJ : 0 ≤ XiPrime.jWin id P.lam ψ) :
    (fun T => rtrace ((P.atV ψ T).hat T (Z.Az (P.atV ψ T) T)) - (Z.N T (2 * T) : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧
    (fun T => frobSq ((P.atV ψ T).hat T (Z.Az (P.atV ψ T) T))
        - (XiPrime.cWin id P.lam ψ)⁻¹ * (Z.N T (2 * T) : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧
    (fun T => (Z.NIprime T : ℝ) - (Z.N T (2 * T) : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  have hv : ProfileMoments.CoreProfile ψ := ⟨hcont, fun s hs => (hcore s hs).1, fun s hs => (hcore s hs).2⟩
  have ha' : 1 / 2 < ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ψ s := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by norm_num]; exact ha
  have hb' : 1 / 2 < ∫ s in (-(1 : ℝ) / 2)..(1 / 2), ψ s ^ 2 := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by norm_num]; exact hb
  obtain ⟨hG1, hG2, hG3⟩ := GramV.gram_asymptotics_V Z H P hP hlam hv heven hadm ha' hb' hJ
  have haV := eventually_a_ge_half hP heven hcont hcore hadm hb
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := XiPrime.eventually_tailPackageV_of hP heven hadm haV Z hA₀ hloc
  have hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop := Assembly.tendsto_N_atTop Z H.RvM
  have hAGE : ∀ T, (P.atV ψ T).hat T (Z.Az (P.atV ψ T) T)
      = GramV.Ghat Z P ψ T - (P.atV ψ T).hat T (Z.Ez (P.atV ψ T) T) := by
    intro T
    simp only [GramV.Ghat, Params.hat, ZeroConfig.Ez, ← smul_sub, sub_sub_cancel]
  have hsmall : ∀ᶠ T in atTop, 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) ≤ 1 := by
    have := (Assembly.tendsto_theta_over_L P hP.lam_pos hlam.le).const_mul (2 * |Cθ|)
    rw [mul_zero] at this
    exact this.eventually (Iic_mem_nhds one_pos)
  have hEb : ∀ᶠ T in atTop, |rtrace ((P.atV ψ T).hat T (Z.Ez (P.atV ψ T) T))| ≤ 1 ∧
      frobSq ((P.atV ψ T).hat T (Z.Ez (P.atV ψ T) T)) ≤ 1 := by
    filter_upwards [hTail, haV, hθ, hsmall, Assembly.eventually_l_pos, eventually_gt_atTop 0]
      with T hTl ha2 hθT hs hl hT0
    obtain ⟨B, hB0, htr, hfr, hBle⟩ := hTl.hat
    have hLpos : 0 < P.L T := mul_pos hP.lam_pos hl
    have hx : 0 ≤ l T * T ^ (P.lam / 2 - 1) := mul_nonneg hl.le (Real.rpow_nonneg hT0.le _)
    have hB1 : B ≤ 1 := by
      calc B ≤ θ₀ T / ((P.atV ψ T).a T * (P.atV ψ T).L T) := hBle
        _ ≤ (|Cθ| * (l T * T ^ (P.lam / 2 - 1))) / ((1 / 2) * P.L T) := by
            apply div_le_div₀ (by positivity) ?_ (by positivity) ?_
            · calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
                _ = Cθ * (l T * T ^ (P.lam / 2 - 1)) := by ring
                _ ≤ |Cθ| * (l T * T ^ (P.lam / 2 - 1)) := mul_le_mul_of_nonneg_right (le_abs_self _) hx
            · exact mul_le_mul_of_nonneg_right ha2 hLpos.le
        _ = 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) := by field_simp
        _ ≤ 1 := hs
    exact ⟨htr.trans hB1, hfr.trans (by nlinarith)⟩
  have hone : (fun _ => (1 : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    refine IsLittleO.of_bound fun ε hε => ?_
    filter_upwards [hNtop.eventually_ge_atTop (1 / ε), hNtop.eventually_ge_atTop 0] with T h h0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, abs_of_nonneg h0]
    rw [div_le_iff₀ hε] at h; linarith
  refine ⟨?_, ?_, hG3⟩
  · have hE : (fun T => rtrace ((P.atV ψ T).hat T (Z.Ez (P.atV ψ T) T))) =o[atTop]
        (fun T => (Z.N T (2 * T) : ℝ)) :=
      (IsBigO.of_bound 1 (hEb.mono fun T h => by simpa using h.1)).trans_isLittleO hone
    refine (hG1.sub hE).congr' (Eventually.of_forall fun T => ?_) EventuallyEq.rfl
    simp only [hAGE, rtrace_sub]; ring
  · have hGb : ∀ᶠ T in atTop, frobSq (GramV.Ghat Z P ψ T)
        ≤ (|(XiPrime.cWin id P.lam ψ)⁻¹| + 1) * (Z.N T (2 * T) : ℝ) := by
      filter_upwards [hG2.bound one_pos, hNtop.eventually_ge_atTop 0] with T h h0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, one_mul] at h
      have := (abs_le.mp h).2
      nlinarith [le_abs_self (XiPrime.cWin id P.lam ψ)⁻¹]
    have hsq : (fun T => 2 * Real.sqrt (frobSq (GramV.Ghat Z P ψ T)) + 1) =o[atTop]
        (fun T => (Z.N T (2 * T) : ℝ)) := by
      have h1 : (fun T => Real.sqrt (frobSq (GramV.Ghat Z P ψ T))) =O[atTop]
          (fun T => Real.sqrt (Z.N T (2 * T) : ℝ)) := by
        refine IsBigO.of_bound (Real.sqrt (|(XiPrime.cWin id P.lam ψ)⁻¹| + 1)) ?_
        filter_upwards [hGb, hNtop.eventually_ge_atTop 0] with T h h0
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt h
      exact ((h1.trans_isLittleO (sqrt_isLittleO hNtop)).const_mul_left 2).add hone
    have hD : (fun T => frobSq ((P.atV ψ T).hat T (Z.Az (P.atV ψ T) T)) - frobSq (GramV.Ghat Z P ψ T))
        =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
      refine IsBigO.trans_isLittleO ?_ hsq
      refine IsBigO.of_bound 1 ?_
      filter_upwards [hEb] with T h
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, hAGE]
      exact (frobSq_close _ _ h.2).trans (le_abs_self _)
    refine (hG2.add hD).congr' (Eventually.of_forall fun T => ?_) EventuallyEq.rfl
    ring

end Z9
end ZetaS
