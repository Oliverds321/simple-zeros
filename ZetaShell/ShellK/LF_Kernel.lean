/-
Nodes F1c-5, F1c-6, F1c-7 (L7_3, round 4): the kernel algebra of the Shell Frobenius row (Shell analogues of L7_3's
K8c `BK_eq_zoneSplit`, `BK_vDesign_le` and K8b's `vProfile_eq_profDesignQle`).
* F1c-5 `kernel_split`: `ψ_v(0) + K0a(a) + KoutShell(C, α′, a) = B_{α′}(v) + (C−1)·Jzone(a)` (`B_{α′} = Bshell 1 α′ C`,
  ChallengeShell's functional; `psiS` is ZetaQ's `psi` by `rfl`), for admissible `v`, `0 ≤ a ≤ 1 ≤ α′`.
* F1c-6 `Bshell_vDesign_le`: the ramp link `B_{α′}(v_design) ≤ c²·B_{α′}(v_profile)` (`HFrob.psi_vDesign_le`,
  the Shell kernel is `≥ 0` for `C ≥ 0`).
* F1c-7 `vProfile_S53`: along `ShellDesignM S53L75`, ZetaQ's `vProfile P` is ChallengeShell's `S53L75.v` (A1
  `poly_eval`).
-/
import ZetaShell.ShellK.LF_Defs
import ZetaShell.Design.SD_A1_PolyEval

noncomputable section
open MeasureTheory Set

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Payoff ZetaQ.FrobAssembly

theorem psiS_eq_psi (v : ℝ → ℝ) : psiS v = psi v := rfl

theorem shellKernel_measurable (αp C : ℝ) : Measurable (shellKernel 1 αp C) := by
  unfold shellKernel
  refine Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    continuous_abs.measurable ?_
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_const
    measurable_const

theorem shellKernel_bound (αp C α : ℝ) : ‖shellKernel 1 αp C α‖ ≤ max 1 |C| := by
  unfold shellKernel
  split_ifs with h1 h2
  · rw [Real.norm_eq_abs, abs_abs]; exact le_trans h1 (le_max_left _ _)
  · rw [Real.norm_eq_abs, abs_one]; exact le_max_left _ _
  · rw [Real.norm_eq_abs]; exact le_max_right _ _

theorem shellKernel_nonneg {αp C : ℝ} (hC : 0 ≤ C) (α : ℝ) : 0 ≤ shellKernel 1 αp C α := by
  unfold shellKernel
  split_ifs
  · exact abs_nonneg α
  · exact zero_le_one
  · exact hC

theorem shellPsi_integrable {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (αp C : ℝ) :
    Integrable (fun α => shellKernel 1 αp C α * psi v α) :=
  Integrable.bdd_mul (c := max 1 |C|) (psi_integrable hv) (shellKernel_measurable αp C).aestronglyMeasurable
    (ae_of_all _ (fun α => shellKernel_bound αp C α))

/-- **F1c-5.** -/
theorem kernel_split {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (C αp a : ℝ) (hαp : 1 ≤ αp)
    (ha0 : 0 ≤ a) (ha : a ≤ 1) :
    psi v 0 + K0a a v + KoutShell C αp a v = Bshell 1 αp C v + (C - 1) * Jzone a v := by
  have hint := shellPsi_integrable hv αp C
  have hsplit := integral_add_compl (s := Icc (-1 : ℝ) 1) measurableSet_Icc hint
  rw [compl_Icc_one] at hsplit
  have h1 : ∫ α in Icc (-1 : ℝ) 1, shellKernel 1 αp C α * psi v α = ∫ α in Icc (-1 : ℝ) 1, |α| * psi v α := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro α hα
    have : |α| ≤ 1 := abs_le.mpr ⟨hα.1, hα.2⟩
    simp [shellKernel, this]
  have hMm : MeasurableSet {α : ℝ | |α| ≤ αp} := measurableSet_le continuous_abs.measurable measurable_const
  have e2 := integral_inter_add_diff hMm (hint.integrableOn (s := {α : ℝ | 1 < |α|}))
  have hs1 : {α : ℝ | 1 < |α|} ∩ {α : ℝ | |α| ≤ αp} = {α : ℝ | 1 < |α| ∧ |α| ≤ αp} := rfl
  have hs2 : {α : ℝ | 1 < |α|} \ {α : ℝ | |α| ≤ αp} = {α : ℝ | αp < |α|} := by
    ext α
    simp only [mem_diff, mem_setOf_eq, not_le]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨lt_of_le_of_lt hαp h, h⟩
  rw [hs1, hs2] at e2
  have hmid : ∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ αp}, shellKernel 1 αp C α * psi v α
      = ∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ αp}, psi v α := by
    apply setIntegral_congr_fun ((measurableSet_lt measurable_const continuous_abs.measurable).inter hMm)
    intro α hα
    have h1' : ¬ |α| ≤ 1 := not_le.mpr hα.1
    have h2' : |α| ≤ αp := hα.2
    simp [shellKernel, h1', h2']
  have htop : ∫ α in {α : ℝ | αp < |α|}, shellKernel 1 αp C α * psi v α
      = C * ∫ α in {α : ℝ | αp < |α|}, psi v α := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_lt measurable_const continuous_abs.measurable)
    intro α hα
    have hα' : αp < |α| := hα
    have h1' : ¬ |α| ≤ 1 := not_le.mpr (lt_of_le_of_lt hαp hα')
    have h2' : ¬ |α| ≤ αp := not_le.mpr hα'
    simp [shellKernel, h1', h2']
  have hK0 := K0_eq_K0a_add_Jzone hv ha0 ha
  unfold K0 at hK0
  unfold Bshell KoutShell
  rw [psiS_eq_psi]
  have hB : ∫ α, shellKernel 1 αp C α * psi v α
      = (∫ α in Icc (-1 : ℝ) 1, |α| * psi v α) + (∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ αp}, psi v α)
        + C * ∫ α in {α : ℝ | αp < |α|}, psi v α := by
    rw [← hsplit, h1, ← e2, hmid, htop]
    ring
  rw [hB, hK0]
  ring

/-- **F1c-6.** The ramp link for the Shell kernel. -/
theorem Bshell_vDesign_le {P : ParamsQ} (hP : P.Valid) {C : ℝ} (hC : 0 ≤ C) (αp : ℝ) :
    Bshell 1 αp C (vDesign P) ≤ cRampS P ^ 2 * Bshell 1 αp C (vProfile P) := by
  have hD := vDesign_admissible hP
  have hPr := vProfile_admissible hP
  have h0 := HFrob.psi_vDesign_le hP 0
  have hI : ∫ α, shellKernel 1 αp C α * psi (vDesign P) α
      ≤ ∫ α, shellKernel 1 αp C α * (cRampS P ^ 2 * psi (vProfile P) α) :=
    integral_mono (shellPsi_integrable hD αp C) ((shellPsi_integrable hPr αp C).const_mul (cRampS P ^ 2) |>.congr
      (Filter.Eventually.of_forall fun α => by ring))
      (fun α => mul_le_mul_of_nonneg_left (HFrob.psi_vDesign_le hP α) (shellKernel_nonneg hC α))
  have hI' : ∫ α, shellKernel 1 αp C α * (cRampS P ^ 2 * psi (vProfile P) α)
      = cRampS P ^ 2 * ∫ α, shellKernel 1 αp C α * psi (vProfile P) α := by
    rw [← integral_const_mul]; congr 1; ext α; ring
  unfold Bshell
  rw [psiS_eq_psi, psiS_eq_psi]
  rw [hI'] at hI
  unfold cRampS at hI ⊢
  nlinarith

/-- **F1c-7.** Along the Shell design, ZetaQ's certified profile is S53-L75's `v`. -/
theorem vProfile_S53 {r ε Q : ℝ} {P : ParamsQ} (hdes : Design.ShellDesignM S53L75 r ε Q P) :
    vProfile P = S53L75.v := by
  have hlam : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
  have hprof : P.prof = S53L75.poly := hdes.2.2.2.2.2.2.2.2.2.2.2
  funext t
  simp only [vProfile, ShellProfile.v, ShellProfile.mass, hlam, hprof, ShellProfile.poly_eval]

end F1c
end ShellK
end ZetaShell
