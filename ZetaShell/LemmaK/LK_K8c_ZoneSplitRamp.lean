/-
Node K8c (L7_3): the two algebraic links between K8a and K8b, killed versions of ZetaQ's
`FrobAssembly.B_eq_zoneSplit` and of the ramp domination behind `HFrob.hfrob_qle_of_sep`:
* `BK_eq_zoneSplit`: `B^K_C(v) = ψ(0) + K0a(a) + C·(Jzone(a) + K1kill) − (C − 1)·Jzone(a)` for admissible `v`,
  `0 ≤ a ≤ 1` — i.e. the in-zone assembly of K8a, `ψ(0) + K0a + C(Jzone + K1kill)`, is `B^K_C + (C−1)Jzone`
  (sec_lemmaK (e): the zone-edge strip keeps `C|α|`, beyond `|α| = 1` the kernel is `C`).
* `BK_vDesign_le`: `B^K_C(v_design) ≤ c²·B^K_C(v_profile)`, `c = profMass/(λa)` (from ZetaQ's pointwise
  `HFrob.psi_vDesign_le`; the killed kernel is `≥ 0`), for `C ≥ 0`.
Dependencies: trunk `FrobAssembly.K0_eq_K0a_add_Jzone`, `Payoff.compl_Icc_one`, `HFrob.psi_vDesign_le`,
`RampLink.vDesign_admissible`, `vProfile_admissible`; K01 (`killedPsi_integrable`). Difficulty: E–M. PROVED.
-/
import ZetaShell.LemmaK.LK_K00_BKleB
import ZetaShell.LemmaK.LK_K01_BKmonoC

noncomputable section
open MeasureTheory Set

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Payoff ZetaQ.FrobAssembly

/-- `B^K_C(v) = ψ(0) + K0 v + C·K1kill v`. -/
theorem BK_eq_K0_add {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (C : ℝ) :
    BK C v = psi v 0 + K0 v + C * K1kill v := by
  unfold BK K0 K1kill
  have hint := killedPsi_integrable hv C
  have hsplit := integral_add_compl (s := Icc (-1 : ℝ) 1) measurableSet_Icc hint
  rw [compl_Icc_one] at hsplit
  have h1 : ∫ α in Icc (-1 : ℝ) 1, killedKernel C α * psi v α = ∫ α in Icc (-1 : ℝ) 1, |α| * psi v α := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro α hα
    have : |α| ≤ 1 := abs_le.mpr ⟨hα.1, hα.2⟩
    simp [killedKernel, this]
  have h2 : ∫ α in {α : ℝ | 1 < |α|}, killedKernel C α * psi v α
      = ∫ α in {α : ℝ | 1 < |α|}, C * psi v α := by
    apply setIntegral_congr_fun (measurableSet_lt measurable_const continuous_abs.measurable)
    intro α hα
    have : ¬ |α| ≤ 1 := not_le.mpr hα
    simp [killedKernel, this]
  rw [h1, h2, integral_const_mul] at hsplit
  linarith

/-- **K8c (a).** The killed zone split. -/
theorem BK_eq_zoneSplit {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (C : ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ 1) :
    BK C v = psi v 0 + K0a a v + C * (Jzone a v + K1kill v) - (C - 1) * Jzone a v := by
  rw [BK_eq_K0_add hv C, K0_eq_K0a_add_Jzone hv ha0 ha]
  ring

/-- **K8c (b).** The killed ramp domination `B^K_C(v_design) ≤ c²·B^K_C(v_profile)`. -/
theorem BK_vDesign_le {P : ParamsQ} (hP : P.Valid) {C : ℝ} (hC : 0 ≤ C) :
    BK C (vDesign P) ≤ (profMass P / (P.lam * P.aQ)) ^ 2 * BK C (vProfile P) := by
  set c : ℝ := profMass P / (P.lam * P.aQ) with hc
  have hD := vDesign_admissible hP
  have hPr := vProfile_admissible hP
  have h0 := HFrob.psi_vDesign_le hP 0
  have hI : ∫ α, killedKernel C α * psi (vDesign P) α ≤ ∫ α, killedKernel C α * (c ^ 2 * psi (vProfile P) α) :=
    integral_mono (killedPsi_integrable hD C) ((killedPsi_integrable hPr C).const_mul (c ^ 2) |>.congr
      (Filter.Eventually.of_forall fun α => by ring))
      (fun α => mul_le_mul_of_nonneg_left (HFrob.psi_vDesign_le hP α) (killedKernel_nonneg hC α))
  have hI' : ∫ α, killedKernel C α * (c ^ 2 * psi (vProfile P) α)
      = c ^ 2 * ∫ α, killedKernel C α * psi (vProfile P) α := by
    rw [← integral_const_mul]; congr 1; ext α; ring
  unfold BK
  rw [hI'] at hI
  nlinarith

end LemmaK
end ZetaShell
