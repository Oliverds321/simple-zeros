/-
rh72/lean_work/L0_2/HeadlineV.lean — nodes W9.5 (zero side for `P.atV ψ`) and W9.7 (headline at bandwidth λ < 1, then
λ → 1⁻), and the first end-to-end theorems of track W:

  zeta_simple_poly8A : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (26957030199857/40103091391077 − ε)·N(T,2T) ≤ N₀ˢ(T,2T),
  zeta_simple_cos85  : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (H(cos 1.6 s) − ε)·N(T,2T) ≤ N₀ˢ(T,2T),   H(8/5) ≥ 0.6719815510003707,

for Mathlib's `riemannZeta`, with the tree's counting functions (Zeta23/Statement.lean: `Ncount`, `N0simple` = simple
zeros on the critical line), NO hypotheses; and the distinct-zeros companions (c = 3 endgame)
  zeta_dist_poly8A / zeta_dist_cos85 : ((1 + H)/2 − ε)·N(T,2T) ≤ N_d(T,2T)   ((1+H)/2 = 0.83609… / 0.83599…).  These are the paper-level AF bounds 2 − R(ψ) (draft eq:zeta-R, l.99–103)
for the two windows of the draft (thm:zeta-mainw2's poly8A, thm:zeta-allmarks' cos 1.6s) — weaker than the draft's
records, but complete.

Assembly (at fixed λ < 1): W7 (`localHypsCore_eventually`) → W9.4 (`tracesBoundsV`) + W8 (`tendsto_cRatioV`) +
W9.5 (the tree's generic `atV` zero side: `XiPrime.blockInputsV_of'`, `eventually_tailPackageV_of`, `GzGpV_of'`,
`Params.atV_trGtilde…`) → W9.6 (`thmV_mult2_abstract`); then ζ (`zetaZeroConfig`, `paperInputs_zeta`,
`paramsOf stdProfile λ`), then λ → 1⁻ (`ThmD.eps_form_of_approx`).  No `sorry`.
-/
import ZetaS.Window.EndgameV
import ZetaS.Window.WindowLimits

noncomputable section

open Filter Asymptotics Topology Real

namespace ZetaS
namespace HeadlineV

open Zeta23 Zeta23.ThmD Zeta23.Assembly ZetaS.ProfileMoments ZetaS.ProfileAutocorr ZetaS.TracesV

/-- **W9.5 + W9.7 at fixed λ < 1, abstract zero configuration**: for any even `CoreProfile` ψ whose window family is
admissible, with ∫ψ, ∫ψ² > 1/2: (2 − 1/c_λ(ψ) − ε)·N ≤ N₀ˢ eventually, c_λ(ψ) = λ(∫ψ)²/(∫ψ² + λ𝒥_id(λ;ψ)). -/
theorem simple_V_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    {v : ℝ → ℝ} (hv : CoreProfile v) (heven : ∀ s, v (-s) = v s) {cW : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w cW)
    (ha : 1 / 2 < ∫ s in (-(1:ℝ)/2)..(1/2), v s) (hb : 1 / 2 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)
    (hJ : 0 ≤ XiPrime.jWin id P.lam v) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - (XiPrime.cWin id P.lam v)⁻¹ - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  have hLoc : LocalHypsCoreVEventually P v cW := localHypsCore_eventually hP hv (K := 8) le_rfl hadm hb
  have hTr := tracesBoundsV (Z := Z) hP H hadm hLoc
  have hLJ : 0 ≤ P.lam * XiPrime.jWin id P.lam v := mul_nonneg hP.lam_pos.le hJ
  have hden : 0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + P.lam * XiPrime.jWin id P.lam v := by linarith
  have hc := tendsto_cRatioV hP hv hadm hden
  have hc0 : 0 < XiPrime.cWin id P.lam v := by
    unfold XiPrime.cWin
    exact div_pos (mul_pos hP.lam_pos (pow_pos (by linarith) 2)) hden
  have hab := (concreteFactsV hP H hadm hLoc).ab_range
  have ha' : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataV P v Z).aT T ∧ (concreteDataV P v Z).aT T ≤ 1 :=
    hab.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  have haV : ∀ᶠ T in atTop, 1 / 2 ≤ (P.atV v T).a T := ha'.mono fun T h => by
    rw [Params.atV_a T hP heven]; exact h.1
  have h8 : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := Params.eventually_w8 hP
  have hBlock : ∀ᶠ T in atTop, BlockInputs Z (P.atV v T) T := by
    filter_upwards [h8, haV] with T hT haT
    exact XiPrime.blockInputsV_of' hP heven hadm Z hT (by linarith)
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨θ₀, hTail, hθ₀⟩ := XiPrime.eventually_tailPackageV_of hP heven hadm haV Z hA₀ hloc
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atV v T) T = (P.atV v T).Gp T := by
    filter_upwards [h8] with T hT
    exact XiPrime.GzGpV_of' hP heven hadm Z H.EF hT
  have hId : ∀ᶠ T in atTop, (P.atV v T).trGtilde T = (concreteDataV P v Z).trG T ∧
      (P.atV v T).trGtildeSq T = (concreteDataV P v Z).trG2 T ∧
      (P.atV v T).a T = (concreteDataV P v Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atV_trGtilde T hP heven, Params.atV_trGtildeSq T hP heven, Params.atV_a T hP heven⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  exact EndgameV.thmV_mult2_abstract Z H P hP heven hadm hlam _ _ _ _ _ hTr hc0 hc ha' hBlock θ₀ hTail hθ₀
    hNII hGzGp hId hcalE

/-- the distinct-zeros line (c = 3): (3/2 − 1/(2c_λ(ψ)) − ε)·N ≤ N_d eventually. -/
theorem dist_V_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    {v : ℝ → ℝ} (hv : CoreProfile v) (heven : ∀ s, v (-s) = v s) {cW : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w cW)
    (ha : 1 / 2 < ∫ s in (-(1:ℝ)/2)..(1/2), v s) (hb : 1 / 2 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)
    (hJ : 0 ≤ XiPrime.jWin id P.lam v) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - (XiPrime.cWin id P.lam v)⁻¹ / 2 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T) := by
  have hLoc : LocalHypsCoreVEventually P v cW := localHypsCore_eventually hP hv (K := 8) le_rfl hadm hb
  have hTr := tracesBoundsV (Z := Z) hP H hadm hLoc
  have hLJ : 0 ≤ P.lam * XiPrime.jWin id P.lam v := mul_nonneg hP.lam_pos.le hJ
  have hden : 0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + P.lam * XiPrime.jWin id P.lam v := by linarith
  have hc := tendsto_cRatioV hP hv hadm hden
  have hc0 : 0 < XiPrime.cWin id P.lam v := by
    unfold XiPrime.cWin
    exact div_pos (mul_pos hP.lam_pos (pow_pos (by linarith) 2)) hden
  have hab := (concreteFactsV hP H hadm hLoc).ab_range
  have ha' : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataV P v Z).aT T ∧ (concreteDataV P v Z).aT T ≤ 1 :=
    hab.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  have haV : ∀ᶠ T in atTop, 1 / 2 ≤ (P.atV v T).a T := ha'.mono fun T h => by
    rw [Params.atV_a T hP heven]; exact h.1
  have h8 : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := Params.eventually_w8 hP
  have hBlock : ∀ᶠ T in atTop, BlockInputs Z (P.atV v T) T := by
    filter_upwards [h8, haV] with T hT haT
    exact XiPrime.blockInputsV_of' hP heven hadm Z hT (by linarith)
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨θ₀, hTail, hθ₀⟩ := XiPrime.eventually_tailPackageV_of hP heven hadm haV Z hA₀ hloc
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atV v T) T = (P.atV v T).Gp T := by
    filter_upwards [h8] with T hT
    exact XiPrime.GzGpV_of' hP heven hadm Z H.EF hT
  have hId : ∀ᶠ T in atTop, (P.atV v T).trGtilde T = (concreteDataV P v Z).trG T ∧
      (P.atV v T).trGtildeSq T = (concreteDataV P v Z).trG2 T ∧
      (P.atV v T).a T = (concreteDataV P v Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atV_trGtilde T hP heven, Params.atV_trGtildeSq T hP heven, Params.atV_a T hP heven⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  exact EndgameV.thmV_mult3_abstract Z H P hP heven hadm hlam _ _ _ _ _ hTr hc0 hc ha' hBlock θ₀ hTail hθ₀
    hNII hGzGp hId hcalE

/-- the λ → 1⁻ step for a constant of the form `2 − 1/cRatio(λ; a, b, J)`. -/
theorem eps_lift {a b J : ℝ} (ha : a ≠ 0) (hbJ : b + J ≠ 0) {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 - (ThmD.cRatio lam a b J)⁻¹ - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 - (ThmD.cRatio 1 a b J)⁻¹ - ε) * N T ≤ lower T := by
  refine eps_form_of_approx (g := fun lam => 2 - (ThmD.cRatio lam a b J)⁻¹)
    (approx_of_continuousWithinAt (g := fun lam => 2 - (ThmD.cRatio lam a b J)⁻¹) ?_) hN h
  have hden : b + (1:ℝ) ^ 2 * J ≠ 0 := by simpa using hbJ
  have hc : ContinuousAt (fun lam : ℝ => ThmD.cRatio lam a b J) 1 := by
    unfold ThmD.cRatio
    exact (continuousAt_id.mul continuousAt_const).div
      (continuousAt_const.add ((continuousAt_id.pow 2).mul continuousAt_const)) hden
  have hne : ThmD.cRatio 1 a b J ≠ 0 := by
    unfold ThmD.cRatio
    exact div_ne_zero (by simpa using pow_ne_zero 2 ha) hden
  exact (continuousAt_const.sub (hc.inv₀ hne)).continuousWithinAt

/-- the λ → 1⁻ step for the distinct-zeros constant `3/2 − 1/(2 cRatio(λ; a, b, J))`. -/
theorem eps_lift_dist {a b J : ℝ} (ha : a ≠ 0) (hbJ : b + J ≠ 0) {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (3 / 2 - (ThmD.cRatio lam a b J)⁻¹ / 2 - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (3 / 2 - (ThmD.cRatio 1 a b J)⁻¹ / 2 - ε) * N T ≤ lower T := by
  refine eps_form_of_approx (g := fun lam => 3 / 2 - (ThmD.cRatio lam a b J)⁻¹ / 2)
    (approx_of_continuousWithinAt (g := fun lam => 3 / 2 - (ThmD.cRatio lam a b J)⁻¹ / 2) ?_) hN h
  have hden : b + (1:ℝ) ^ 2 * J ≠ 0 := by simpa using hbJ
  have hc : ContinuousAt (fun lam : ℝ => ThmD.cRatio lam a b J) 1 := by
    unfold ThmD.cRatio
    exact (continuousAt_id.mul continuousAt_const).div
      (continuousAt_const.add ((continuousAt_id.pow 2).mul continuousAt_const)) hden
  have hne : ThmD.cRatio 1 a b J ≠ 0 := by
    unfold ThmD.cRatio
    exact div_ne_zero (by simpa using pow_ne_zero 2 ha) hden
  exact (continuousAt_const.sub ((hc.inv₀ hne).div_const 2)).continuousWithinAt

/-! ## ζ, poly8A (ψ♮ = (4/5)v) -/

/-- ζ at fixed λ ∈ (0,1), poly8A: (2 − 1/cRatio(λ; a, b, J) − ε)N ≤ N₀ˢ, UNCONDITIONAL. -/
theorem zeta_simple_poly8A_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - (ThmD.cRatio lam (40497 / 43750) (16536677606497 / 19144125000000)
        (166041852098299 / 606230625000000))⁻¹ - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have heven : ∀ s, PolyWindow.psiN (-s) = PolyWindow.psiN s := fun s => by
    unfold PolyWindow.psiN; rw [PolyWindow.vP8_even]
  have h := simple_V_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
    WindowInstances.coreProfile_psiN heven
    (fun T hT => by
      rw [PolyWindow.phiV_eq_phiP8]; exact PolyWindow.admWindow_phiP8 hP.taper hP.one_le_w hT)
    (by rw [PolyWindow.integral_psiN]; norm_num) (by rw [PolyWindow.integral_psiN_sq]; norm_num)
    (by rw [WindowLimits.jWin_psiN]; have := hP.lam_pos; positivity)
  rw [WindowLimits.cWin_psiN hP.lam_pos] at h
  simpa [paramsOf] using h

/-- **ζ, poly8A window: (H(ψ̃) − ε)·N(T,2T) ≤ N₀ˢ(T,2T), H(ψ̃) = 26957030199857/40103091391077 = 0.67219…,
UNCONDITIONAL** (the AF bound 2 − R(ψ) for the window of thm:zeta-mainw2; `Ncount`, `N0simple` of Statement.lean). -/
theorem zeta_simple_poly8A :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (26957030199857 / 40103091391077 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have h := eps_lift (a := 40497 / 43750) (b := 16536677606497 / 19144125000000)
    (J := 166041852098299 / 606230625000000) (by norm_num) (by norm_num)
    (N := fun T => (Ncount T (2 * T) : ℝ)) (lower := fun T => (N0simple T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam hl1 hl2 => zeta_simple_poly8A_lam (by linarith) hl2
  have e : (2 : ℝ) - (ThmD.cRatio 1 (40497 / 43750) (16536677606497 / 19144125000000)
      (166041852098299 / 606230625000000))⁻¹ = 26957030199857 / 40103091391077 := by
    rw [← one_div]; exact WindowLimits.HD_P8
  rw [e] at h
  exact h

/-! ## ζ, cos(8/5 · s) -/

theorem aC_eight_fifths : 1 / 2 < CosWindow.aC (8 / 5) := by
  unfold CosWindow.aC
  rw [show (8 / 5 : ℝ) / 2 = 4 / 5 by norm_num]
  have := CosWindow.sin_four_fifths.1
  rw [lt_div_iff₀ (by norm_num)]
  linarith

theorem jWin_cosW (α lam : ℝ) (hα : α ≠ 0) :
    XiPrime.jWin id lam (CosWindow.cosW α) = lam * CosWindow.jC α := by
  unfold XiPrime.jWin
  rw [← WindowLimits.jvConv_cosW hα]
  have h : (fun r => id (lam * r) * XiPrime.vConv (CosWindow.cosW α) r)
      = fun r => lam * (r * XiPrime.vConv (CosWindow.cosW α) r) := by funext r; simp only [id]; ring
  rw [h, intervalIntegral.integral_const_mul]; ring

theorem jC_nonneg {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) : 0 ≤ CosWindow.jC α := by
  rw [← CosWindow.jInt_cosW hα0.ne']
  have hcore := WindowInstances.coreProfile_cosW hα0 hα1
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro v hv
  have hu' : |u| ≤ 1 / 2 := abs_le.mpr ⟨hu.1, hu.2⟩
  have hv' : |v| ≤ 1 / 2 := abs_le.mpr ⟨hv.1, hv.2⟩
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (hcore.nonneg u hu')) (hcore.nonneg v hv')

/-- ζ at fixed λ ∈ (0,1), window cos(8/5·s): (2 − 1/cRatio(λ; a, b, J) − ε)N ≤ N₀ˢ, UNCONDITIONAL. -/
theorem zeta_simple_cos85_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - (ThmD.cRatio lam (CosWindow.aC (8 / 5)) (CosWindow.bC (8 / 5)) (CosWindow.jC (8 / 5)))⁻¹ - ε)
        * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have hα0 : (0:ℝ) < 8 / 5 := by norm_num
  have hα1 : (8 / 5 : ℝ) ≤ 8 / 5 := le_rfl
  have h := simple_V_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
    (WindowInstances.coreProfile_cosW hα0 hα1) (CosWindow.cosW_even (8 / 5))
    (fun T hT => CosWindow.admWindow_phiV_cos hP hα0 hα1 hT)
    (by rw [WindowInstances.half_interval, CosWindow.integral_cosW hα0.ne']; exact aC_eight_fifths)
    (by rw [WindowInstances.half_interval, CosWindow.integral_cosW_sq hα0.ne']
        exact WindowInstances.half_lt_bC hα0 hα1)
    (by rw [jWin_cosW _ _ hα0.ne']; exact mul_nonneg hP.lam_pos.le (jC_nonneg hα0 hα1))
  rw [WindowLimits.cWin_cosW hα0.ne' hP.lam_pos] at h
  simpa [paramsOf] using h

/-- **ζ, window cos(1.6 s): (H(cos 1.6 s) − ε)·N(T,2T) ≤ N₀ˢ(T,2T), UNCONDITIONAL**, H = `CosWindow.HC (8/5)`
= 3/2 − (57/80)cot(4/5) − (7/100)/sin²(4/5) ∈ [0.6719815510003707, 0.6719815510003708]. -/
theorem zeta_simple_cos85 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (CosWindow.HC (8 / 5) - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hα0 : (0:ℝ) < 8 / 5 := by norm_num
  have ha0 : CosWindow.aC (8 / 5) ≠ 0 := (lt_trans (by norm_num) aC_eight_fifths).ne'
  have hbJ : CosWindow.bC (8 / 5) + CosWindow.jC (8 / 5) ≠ 0 := by
    have := WindowInstances.half_lt_bC hα0 le_rfl
    have := jC_nonneg hα0 le_rfl
    linarith
  have h := eps_lift ha0 hbJ (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0simple T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam hl1 hl2 => zeta_simple_cos85_lam (by linarith) hl2
  have e : (2 : ℝ) - (ThmD.cRatio 1 (CosWindow.aC (8 / 5)) (CosWindow.bC (8 / 5)) (CosWindow.jC (8 / 5)))⁻¹
      = CosWindow.HC (8 / 5) := by
    rw [← one_div]; exact WindowLimits.HD_cos ha0
  rw [e] at h
  exact h

/-- the same with the decimal lower bound of `CosWindow.HC_eight_fifths`. -/
theorem zeta_simple_cos85' :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (0.6719815510003707 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := zeta_simple_cos85 ε hε
  refine ⟨T₀, fun T hT => le_trans ?_ (hT₀ T hT)⟩
  exact mul_le_mul_of_nonneg_right (by linarith [CosWindow.HC_eight_fifths.1]) (Nat.cast_nonneg _)

/-! ## distinct zeros: (1 + H)/2 for both windows -/

theorem zeta_dist_poly8A_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - (ThmD.cRatio lam (40497 / 43750) (16536677606497 / 19144125000000)
        (166041852098299 / 606230625000000))⁻¹ / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have heven : ∀ s, PolyWindow.psiN (-s) = PolyWindow.psiN s := fun s => by
    unfold PolyWindow.psiN; rw [PolyWindow.vP8_even]
  have h := dist_V_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
    WindowInstances.coreProfile_psiN heven
    (fun T hT => by
      rw [PolyWindow.phiV_eq_phiP8]; exact PolyWindow.admWindow_phiP8 hP.taper hP.one_le_w hT)
    (by rw [PolyWindow.integral_psiN]; norm_num) (by rw [PolyWindow.integral_psiN_sq]; norm_num)
    (by rw [WindowLimits.jWin_psiN]; have := hP.lam_pos; positivity)
  rw [WindowLimits.cWin_psiN hP.lam_pos] at h
  simpa [paramsOf] using h

/-- **ζ, poly8A window, distinct zeros: ((1 + H(ψ̃))/2 − ε)·N(T,2T) ≤ N_d(T,2T), UNCONDITIONAL**
((1 + H)/2 = 0.83609…). -/
theorem zeta_dist_poly8A :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1 + 26957030199857 / 40103091391077) / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have h := eps_lift_dist (a := 40497 / 43750) (b := 16536677606497 / 19144125000000)
    (J := 166041852098299 / 606230625000000) (by norm_num) (by norm_num)
    (N := fun T => (Ncount T (2 * T) : ℝ)) (lower := fun T => (Ndist T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam hl1 hl2 => zeta_dist_poly8A_lam (by linarith) hl2
  have e : (3 / 2 : ℝ) - (ThmD.cRatio 1 (40497 / 43750) (16536677606497 / 19144125000000)
      (166041852098299 / 606230625000000))⁻¹ / 2 = (1 + 26957030199857 / 40103091391077) / 2 := by
    have := WindowLimits.HD_P8
    rw [one_div] at this
    linarith
  rw [e] at h
  exact h

theorem zeta_dist_cos85_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 - (ThmD.cRatio lam (CosWindow.aC (8 / 5)) (CosWindow.bC (8 / 5)) (CosWindow.jC (8 / 5)))⁻¹ / 2 - ε)
        * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have hα0 : (0:ℝ) < 8 / 5 := by norm_num
  have hα1 : (8 / 5 : ℝ) ≤ 8 / 5 := le_rfl
  have h := dist_V_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
    (WindowInstances.coreProfile_cosW hα0 hα1) (CosWindow.cosW_even (8 / 5))
    (fun T hT => CosWindow.admWindow_phiV_cos hP hα0 hα1 hT)
    (by rw [WindowInstances.half_interval, CosWindow.integral_cosW hα0.ne']; exact aC_eight_fifths)
    (by rw [WindowInstances.half_interval, CosWindow.integral_cosW_sq hα0.ne']
        exact WindowInstances.half_lt_bC hα0 hα1)
    (by rw [jWin_cosW _ _ hα0.ne']; exact mul_nonneg hP.lam_pos.le (jC_nonneg hα0 hα1))
  rw [WindowLimits.cWin_cosW hα0.ne' hP.lam_pos] at h
  simpa [paramsOf] using h

/-- **ζ, window cos(1.6 s), distinct zeros: ((1 + H(cos 1.6s))/2 − ε)·N(T,2T) ≤ N_d(T,2T), UNCONDITIONAL**
((1 + H)/2 ≥ 0.83599077550018535). -/
theorem zeta_dist_cos85 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1 + CosWindow.HC (8 / 5)) / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have hα0 : (0:ℝ) < 8 / 5 := by norm_num
  have ha0 : CosWindow.aC (8 / 5) ≠ 0 := (lt_trans (by norm_num) aC_eight_fifths).ne'
  have hbJ : CosWindow.bC (8 / 5) + CosWindow.jC (8 / 5) ≠ 0 := by
    have := WindowInstances.half_lt_bC hα0 le_rfl
    have := jC_nonneg hα0 le_rfl
    linarith
  have h := eps_lift_dist ha0 hbJ (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (Ndist T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam hl1 hl2 => zeta_dist_cos85_lam (by linarith) hl2
  have e : (3 / 2 : ℝ) - (ThmD.cRatio 1 (CosWindow.aC (8 / 5)) (CosWindow.bC (8 / 5)) (CosWindow.jC (8 / 5)))⁻¹ / 2
      = (1 + CosWindow.HC (8 / 5)) / 2 := by
    have := WindowLimits.HD_cos ha0
    rw [one_div] at this
    linarith
  rw [e] at h
  exact h

end HeadlineV
end ZetaS

end

#print axioms ZetaS.HeadlineV.simple_V_lam_abstract
#print axioms ZetaS.HeadlineV.zeta_simple_poly8A
#print axioms ZetaS.HeadlineV.zeta_simple_cos85
#print axioms ZetaS.HeadlineV.zeta_simple_cos85'
#print axioms ZetaS.HeadlineV.dist_V_lam_abstract
#print axioms ZetaS.HeadlineV.zeta_dist_poly8A
#print axioms ZetaS.HeadlineV.zeta_dist_cos85
