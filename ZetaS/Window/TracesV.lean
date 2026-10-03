/-
rh72/lean_work/L0_2/TracesV.lean — nodes W9.1–W9.4: the tree's Theorem-D trace assembly (`ThmD.FactsD`,
`ThmD.TracesBoundsD`) for the window family `P.phiV ψ` of ANY admissible profile ψ (bandwidth λ = P.lam ≤ 1).

Copy of Zeta23/ThmD/Concrete.lean (`concreteDataD`, `evBound_of_eventuallyAtCoreD`, `concreteFactsD`,
`tracesBoundsD_concrete`) with the Montgomery–Taylor data `P.localFunD` replaced by `AdmWindow.localFun (P.phiV ψ T)`
and its window constant `cDT` by the family's constant `c`; the two φ_D-specific inputs are replaced by generic ones:
`gD_deriv_facts` ↦ `XiPrime.gv_deriv_facts` (from `AdmWindow.l1_deriv_sq`), `phiD_eq_zero` ↦ `AdmWindow.gv_eq_zero`.
Hypotheses: admissibility of the family at every 8w ≤ L and the eventual `LocalHypsCore` (node W7).
No `sorry`.
-/
import ZetaS.Window.ProfileAutocorr
import Zeta23.ThmD.Concrete
import Zeta23.XiPrime.PrimeSide.Concrete

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace ZetaS
namespace TracesV

open Zeta23 Zeta23.ThmD Zeta23.PrimeSide Zeta23.PaperParams

/-- the abstract local data of the window `P.phiV ψ` at height `T`. -/
def localFunV (P : Params) (v : ℝ → ℝ) (T : ℝ) : PrimeSide.LocalFun :=
  AdmWindow.localFun (P.phiV v T) (P.L T)

/-- **W9.1** the concrete D-data of the family (as `ThmD.concreteDataD`, window φ_D ↦ `P.phiV ψ`). -/
def concreteDataV (P : Params) (v : ℝ → ℝ) (Z : ZeroConfig) : DataD P where
  aT := fun T => (localFunV P v T).a
  bT := fun T => (localFunV P v T).b
  trG := fun T => trGtA (P.toSetting T) (localFunV P v T)
  trG2 := fun T => trGt2A (P.toSetting T) (localFunV P v T)
  Ncnt := fun T => (Z.N T (2 * T) : ℝ)
  Mtot := fun T => MtotalA (P.toSetting T) (localFunV P v T)
  Mmumu := fun T => Mform (localFunV P v T).Phi T Zeta23.mu Zeta23.mu
  MPP := fun T => Mform (localFunV P v T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PX (P.X T))
  MmuP := fun T => Mform (localFunV P v T).Phi T Zeta23.mu (Zeta23.PX (P.X T))
  MmuPi := fun T => Mform (localFunV P v T).Phi T Zeta23.mu (Zeta23.PiX (P.X T))
  MPPi := fun T => Mform (localFunV P v T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PiX (P.X T))
  MPiPi := fun T => Mform (localFunV P v T).Phi T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2
  sumL2g := fun T => sumA2g (P.X T) (localFunV P v T).g
  JT := fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunV P v T).g y * y

/-- the eventual `LocalHypsCore` of the family (the conclusion of node W7). -/
def LocalHypsCoreVEventually (P : Params) (v : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → PrimeSide.LocalHypsCore c (P.toSetting T) (localFunV P v T)

variable {P : Params} {v : ℝ → ℝ} {c : ℝ}

lemma evBound_of_eventuallyAtCoreV (hLoc : LocalHypsCoreVEventually P v c)
    {f g : Setting → LocalFun → ℝ}
    (h : ∃ C : ℝ, EventuallyAtCore c P.lam (fun p F => |f p F| ≤ C * g p F))
    (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (localFunV P v T)) :
    EvBound (fun T => f (P.toSetting T) (localFunV P v T))
      (fun T => g (P.toSetting T) (localFunV P v T)) := by
  obtain ⟨T₀, hT₀⟩ := hLoc
  obtain ⟨C, T₁, hT₁⟩ := h
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hg
  refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
  have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
  have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have := hT₁ (P.toSetting T) (localFunV P v T) rfl h1 (hT₀ T h0)
  calc |f (P.toSetting T) (localFunV P v T)| ≤ C * g (P.toSetting T) (localFunV P v T) := this
    _ ≤ max C 1 * g (P.toSetting T) (localFunV P v T) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (hT₂ T h2)

/-- **W9.2–W9.3: `FactsD` for the window family of an admissible profile.** -/
theorem concreteFactsV {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w c)
    (hLoc : LocalHypsCoreVEventually P v c) : FactsD (concreteDataV P v Z) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hΓ := inp.Gamma
  have hcheb := inp.cheb
  have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ l T ∧ 0 ≤ Real.log (l T) ∧ 0 ≤ P.L T ∧ 0 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
      eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T₀, hT₀⟩ := id hLoc
  have e_ends := evBound_of_eventuallyAtCoreV hLoc
    (PrimeSide.lem_ends c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
  have e_mumu := evBound_of_eventuallyAtCoreV hLoc
    (PrimeSide.prop_mumu c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
  have e_PP := evBound_of_eventuallyAtCoreV hLoc
    (PrimeSide.prop_PP (cϱ := c) (lam := P.lam) hcheb inp.MV hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (sq_nonneg _) hX)
  have e_muP := evBound_of_eventuallyAtCoreV hLoc
    (PrimeSide.prop_cross_muP c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hl (Real.sqrt_nonneg _))
  have e_muPi := evBound_of_eventuallyAtCoreV hLoc
    (PrimeSide.prop_cross_muPi c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg hl hL) (Real.sqrt_nonneg _))
  have e_PPi := evBound_of_eventuallyAtCoreV hLoc
    (PrimeSide.prop_cross_PPi c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hL hX)
  have e_PiPi := evBound_of_eventuallyAtCoreV hLoc
    (PrimeSide.prop_cross_PiPi c P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact div_nonneg (mul_nonneg hL hX) hT)
  refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, ?ab_range, rvm_evBound inp.RvM, ?muints2,
    ?prop_trace, e_ends, ?Msplit, e_mumu, e_PP, ?sumJ, e_muP, e_muPi, e_PPi, e_PiPi⟩
  case ab_range =>
    filter_upwards [eventually_ge_atTop T₀, eventually_L_ge P hP.lam_pos 8,
      eventually_L_ge P hP.lam_pos (8 * P.w)] with T hT hL8 hLw
    have hF := hT₀ T hT
    have hL0 : 0 < P.L T := by linarith
    refine ⟨hF.b_ge_half, hF.b_le_a, hF.a_le_one, ?_, ?_⟩
    · apply mul_nonneg (by positivity)
      apply intervalIntegral.integral_nonneg (by linarith : (0:ℝ) ≤ P.L T)
      intro y hy
      exact mul_nonneg (hF.g_nonneg y) hy.1
    · have hgcont : Continuous (localFunV P v T).g := (XiPrime.gv_deriv_facts (hadm T hLw)).1.continuous
      have hgle : ∀ y ∈ Set.Icc (0:ℝ) (P.L T), (localFunV P v T).g y * y ≤ P.L T * y := by
        intro y hy
        apply mul_le_mul_of_nonneg_right _ hy.1
        calc (localFunV P v T).g y ≤ (localFunV P v T).Aphi y := hF.g_le_Aphi y
          _ ≤ max ((P.toSetting T).L - |y|) 0 := hF.Aphi_le y
          _ ≤ P.L T := by
              apply max_le _ hL0.le
              have := abs_nonneg y
              show (P.toSetting T).L - |y| ≤ P.L T
              have e : (P.toSetting T).L = P.L T := rfl
              rw [e]
              linarith
      have hIle : ∫ y in (0:ℝ)..(P.L T), (localFunV P v T).g y * y
          ≤ ∫ y in (0:ℝ)..(P.L T), P.L T * y := by
        apply intervalIntegral.integral_mono_on (by linarith : (0:ℝ) ≤ P.L T) ?_ ?_ hgle
        · exact (hgcont.mul continuous_id).intervalIntegrable 0 (P.L T)
        · exact (continuous_const.mul continuous_id).intervalIntegrable 0 (P.L T)
      have hIval : ∫ y in (0:ℝ)..(P.L T), P.L T * y = P.L T ^ 3 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      calc 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunV P v T).g y * y
          ≤ 2 / P.L T ^ 3 * (P.L T ^ 3 / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← hIval]
            exact hIle
        _ = 1 := by field_simp
  case muints2 =>
    obtain ⟨C, T₁, hC⟩ := hΓ.int_mu_sq
    refine ⟨max C 1, by positivity, max T₁ 0, fun T hT =>
      (hC T ((le_max_left _ _).trans hT)).trans ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact div_nonneg (div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by positivity)) (sq_nonneg _)
  case prop_trace =>
    obtain ⟨A, hA, T₁, hN⟩ := rvm_evBound inp.RvM
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_trace c P.lam hΓ hcheb hlam A
    refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hF := hT₀ T h0
    have := hC (P.toSetting T) (localFunV P v T) rfl h2 hF (Z.N T (2 * T) : ℝ) (hN T h1)
    refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
  case Msplit =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact eq_Msplit c hΓ (P.toSetting T) (localFunV P v T) (hT₀ T hT)
  case sumJ =>
    obtain ⟨C, hC0, hC⟩ := ThmD.sumA2g_close hcheb
    refine ⟨C, hC0, ?_⟩
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (eventually_L_ge P hP.lam_pos 8)
    obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_L_ge P hP.lam_pos (8 * P.w))
    refine ⟨max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hL8 : 8 ≤ P.L T := hT₁ T h1
    have hLw : 8 * P.w ≤ P.L T := hT₂ T h2
    have hW := hadm T hLw
    have hg := XiPrime.gv_deriv_facts hW
    have hgsupp : ∀ y : ℝ, P.L T ≤ y → (localFunV P v T).g y = 0 := by
      intro y hy
      exact hW.gv_eq_zero (by rw [abs_of_nonneg (by linarith [hW.L_pos])]; exact hy)
    have key := hC (P.L T) (P.X T) (localFunV P v T).g hL8 (by
        show P.X T = Real.exp (P.L T)
        rfl) hg.1 hg.2.1 hg.2.2 hgsupp
    have e : P.L T ^ 3 / 2 * ((concreteDataV P v Z).JT T)
        = ∫ y in (0:ℝ)..(P.L T), (localFunV P v T).g y * y := by
      show P.L T ^ 3 / 2 * (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunV P v T).g y * y) = _
      have hL0 : 0 < P.L T := by linarith
      field_simp
    show |sumA2g (P.X T) (localFunV P v T).g - P.L T ^ 3 / 2 * ((concreteDataV P v Z).JT T)|
      ≤ C * P.L T ^ 2
    rw [e]
    exact key

/-- **W9.4: `TracesBoundsD` for the window family of an admissible profile.** -/
theorem tracesBoundsV {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w c)
    (hLoc : LocalHypsCoreVEventually P v c) :
    TracesBoundsD P (concreteDataV P v Z).aT (concreteDataV P v Z).bT (concreteDataV P v Z).JT
      (concreteDataV P v Z).trG (concreteDataV P v Z).trG2 (concreteDataV P v Z).Ncnt :=
  tracesBoundsD_of_factsD _ (concreteFactsV hP inp hadm hLoc)

end TracesV
end ZetaS

end

#print axioms ZetaS.TracesV.concreteFactsV
#print axioms ZetaS.TracesV.tracesBoundsV
