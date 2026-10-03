/-
Node Z6 (track W) — `defect` field (lem:sigd-residue (iv)): Σ_{on-line ρ, γ ∈ I′} m_ρ δ_ρ ≪ √T log T = o(N), with
δ_ρ = Σ_{k∉[0,d)} u_γ(k)², I′ = (T − √T, 2T + √T] (the tree's `D0 T = √T`), at bandwidth λ = P.lam < 1.
Uses |u_γ(k)| ≤ min{1, λ_φ ξ⁻²} and the RvM local count (`H.RvM.local_count`).

Proof (L3_2), statement unchanged. The core estimate `Z6.defect_core` (file `Z6Core.lean`) needs `∫φ_T² ≥ κ·L(T)`
eventually for some κ > 0. From admissibility alone this follows by a dichotomy:
  * `a_T = L⁻¹∫φ_T² = ∫ max(0, ψ(s))·ϱ(L(1/2 − |s|)/w)² ds` is NONDECREASING in L (the ramp ϱ is monotone), and L(T)
    is nondecreasing in T; so if `∫φ_{T₀}² > 0` at one admissible height T₀ > 0, then κ := a_{T₀} works for all T ≥ T₀;
  * otherwise `∫φ_T² = 0` at every admissible height, so `u_γ = v̂/√0 = 0` (Lean's x/0 = 0) and every δ_γ = 0.
The hypothesis `λ < 1` is not used.
-/
import ZetaS.InterfacesV2
import Zeta23.Hypotheses
import ZetaS.ZeroSide.Z6Core

open Filter Asymptotics

namespace ZetaS

namespace Z6

open Zeta23 MeasureTheory Real

/-- `φ_T(Ls)² = max(0, ψ(s))·ϱ(L(1/2 − |s|)/w)²`. -/
lemma phiV_scaled_sq (P : Params) (ψ : ℝ → ℝ) (T : ℝ) (hL : 0 < P.L T) (s : ℝ) :
    P.phiV ψ T (P.L T * s) ^ 2 = max 0 (ψ s) * P.ϱ (P.L T * (1 / 2 - |s|) / P.w) ^ 2 := by
  unfold Params.phiV Params.phi
  rw [mul_pow, Real.sq_sqrt (le_max_left _ _), mul_div_cancel_left₀ s hL.ne', abs_mul, abs_of_pos hL,
    show (P.L T / 2 - P.L T * |s|) / P.w = P.L T * (1 / 2 - |s|) / P.w by ring]

lemma ramp_sq_mono {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {L₀ L w : ℝ} (hw : 0 < w) (hL₀ : 0 ≤ L₀)
    (hLL : L₀ ≤ L) (s : ℝ) :
    ϱ (L₀ * (1 / 2 - |s|) / w) ^ 2 ≤ ϱ (L * (1 / 2 - |s|) / w) ^ 2 := by
  rcases le_or_gt 0 (1 / 2 - |s|) with h | h
  · have hmono : L₀ * (1 / 2 - |s|) / w ≤ L * (1 / 2 - |s|) / w :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLL h) hw.le
    exact pow_le_pow_left₀ (hϱ.nonneg _) (hϱ.monotone hmono) 2
  · have h0 : L₀ * (1 / 2 - |s|) / w ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hL₀ h.le) hw.le
    rw [hϱ.eq_zero _ h0, zero_pow two_ne_zero]
    exact sq_nonneg _

lemma a_eq (P : Params) (ψ : ℝ → ℝ) (T : ℝ) (hL : 0 < P.L T) :
    (P.L T)⁻¹ * ∫ u, P.phiV ψ T u ^ 2 = ∫ s, P.phiV ψ T (P.L T * s) ^ 2 := by
  have h := Measure.integral_comp_mul_left (fun u => P.phiV ψ T u ^ 2) (P.L T)
  rw [h, abs_of_pos (inv_pos.mpr hL), smul_eq_mul]

lemma L_mono {P : Params} (hP : P.Valid) {T₀ T : ℝ} (hT₀ : 0 < T₀) (h : T₀ ≤ T) : P.L T₀ ≤ P.L T := by
  unfold Params.L l
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right h (by positivity))) hP.lam_pos.le

/-- `a_T = L⁻¹∫φ_T²` is nondecreasing along admissible heights. -/
lemma a_mono {P : Params} (hP : P.Valid) {ψ : ℝ → ℝ} {c : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV ψ T) (P.L T) P.w c)
    {T₀ T : ℝ} (h8 : 8 * P.w ≤ P.L T₀) (hLL : P.L T₀ ≤ P.L T) :
    (P.L T₀)⁻¹ * ∫ u, P.phiV ψ T₀ u ^ 2 ≤ (P.L T)⁻¹ * ∫ u, P.phiV ψ T u ^ 2 := by
  have hw := hP.one_le_w
  have hL0 : 0 < P.L T₀ := by linarith
  have hL : 0 < P.L T := by linarith
  have h8' : 8 * P.w ≤ P.L T := h8.trans hLL
  rw [a_eq P ψ T₀ hL0, a_eq P ψ T hL]
  have hi : ∀ T', 8 * P.w ≤ P.L T' → Integrable (fun s => P.phiV ψ T' (P.L T' * s) ^ 2) := by
    intro T' h
    have hW := hadm T' h
    exact (hW.integrable_pow (n := 2) (by norm_num)).comp_mul_left' hW.L_pos.ne'
  refine integral_mono (hi T₀ h8) (hi T h8') fun s => ?_
  simp only
  rw [phiV_scaled_sq P ψ T₀ hL0, phiV_scaled_sq P ψ T hL]
  exact mul_le_mul_of_nonneg_left (ramp_sq_mono hP.taper (by linarith) hL0.le hLL s) (le_max_left _ _)

lemma deltaW_eq_zero_of {v : ℝ → ℝ} {L T : ℝ} {d : ℕ} (h : ∫ u, v u ^ 2 = 0) (γ : ℝ) :
    deltaW v L T d γ = 0 := by
  unfold deltaW uR
  simp [h]

end Z6

theorem defect_littleO (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z) {P : Zeta23.Params}
    (hP : P.Valid) (hlam : P.lam < 1) {ψ : ℝ → ℝ} {c : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → Zeta23.AdmWindow (P.phiV ψ T) (P.L T) P.w c) :
    (fun T => ∑ᶠ ρ ∈ Z.window (T - Real.sqrt T) (2 * T + Real.sqrt T) ∩ {ρ : ℂ | ρ.re = 1 / 2},
        (Z.mult ρ : ℝ) * deltaW (P.phiV ψ T) (P.L T) T (P.d T) ρ.im)
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  have hw := hP.one_le_w
  by_cases hex : ∃ T₀, 0 < T₀ ∧ 8 * P.w ≤ P.L T₀ ∧ 0 < ∫ u, P.phiV ψ T₀ u ^ 2
  · obtain ⟨T₀, hT₀, h8, hpos⟩ := hex
    have hL0 : 0 < P.L T₀ := by linarith
    refine Z6.defect_core Z H hP (κ := (P.L T₀)⁻¹ * ∫ u, P.phiV ψ T₀ u ^ 2) (by positivity) hadm ?_
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hLL := Z6.L_mono hP hT₀ hT
    have hL : 0 < P.L T := by linarith
    have hm := Z6.a_mono hP hadm h8 hLL
    calc (P.L T₀)⁻¹ * (∫ u, P.phiV ψ T₀ u ^ 2) * P.L T
        ≤ (P.L T)⁻¹ * (∫ u, P.phiV ψ T u ^ 2) * P.L T := mul_le_mul_of_nonneg_right hm hL.le
      _ = ∫ u, P.phiV ψ T u ^ 2 := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  · push_neg at hex
    have hl : Tendsto Zeta23.l atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
    have hLt : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
    refine (isLittleO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [hLt.eventually_ge_atTop (8 * P.w), eventually_gt_atTop 0] with T h8 hT
    have h0 : ∫ u, P.phiV ψ T u ^ 2 = 0 :=
      le_antisymm (hex T hT h8) (MeasureTheory.integral_nonneg fun u => sq_nonneg _)
    symm
    refine finsum_mem_eq_zero_of_forall_eq_zero fun ρ _ => ?_
    rw [Z6.deltaW_eq_zero_of h0, mul_zero]

end ZetaS
