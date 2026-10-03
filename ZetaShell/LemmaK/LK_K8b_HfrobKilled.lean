/-
Node K8b (L7_3): the Frobenius row at the killed kernel, `frobSq ≤ (2 − 0.7235 + rowR2)·𝒩`, along ZetaQ's own design
(profile `designProfileQle`, `λ*`) — the mirror of `ZetaQ.HFrob.hfrob_qle_of_sep` (under `hsep`) and of
`ZetaQ.Margin.hfrob_qle_of_designM` (margin design, `hsep` discharged), with `κ_cert = 2 − 0.7212` replaced by
`2 − 0.7235`. PROVED here modulo K8a (`frobenius_inzone_killed`) ONLY; the certificate enters through KCa
(`certKD_core`, level A: real-valued `B^K_{C⁺}(v_p) ≤ 2 − 0.72351`, 0.72351 = 0.7235 + 10⁻⁵):
  frobSq ≤ [ψ(0) + K0a + C(Jzone + K1kill) + ε′]𝒩                         (K8a, ε′ = 2·10⁻⁶)
        = [B^K_C(v_d) + (C−1)Jzone(v_d) + ε′]𝒩                           (K8c `BK_eq_zoneSplit`)
        ≤ [c²·B^K_C(v_p) + (C−1)c²Jzone(v_p) + ε′]𝒩                      (K8c `BK_vDesign_le`, `Jzone_vDesign_le`)
        ≤ [c²(2 − 0.72351) + c²·zoneRowLinear + ε′]𝒩                     (KCa + K01 at `C = π⁴/18 ≤ C⁺`; zone data)
        ≤ [2 − 0.7235 + rowR2]𝒩                                         (`c² − 1 ≤ 8/ℒ ≤ 4·10⁻⁶`, `ℒ ≥ 2·10⁶`).
Draft: thm:one-prime's proof ("Proposition 3.1 is applied with `κ_C := B^K_C(v_K)`"), at the design profile.
-/
import ZetaShell.LemmaK.LK_K8_FrobKilled
import ZetaShell.LemmaK.LK_K8c_ZoneSplitRamp
import ZetaShell.LemmaK.LK_KCa_CertCore

noncomputable section
open MeasureTheory Set Real Filter
open ZetaQ ZetaQ.Payoff ZetaQ.Zones ZetaQ.Ends ZetaQ.FamRows ZetaQ.FrobAssembly ZetaQ.HFrob

namespace ZetaShell
namespace LemmaK

/-- ZetaQ's certified profile `vProfile P` at the design is the killed-kernel profile `profDesignQle.v`. -/
theorem vProfile_eq_profDesignQle {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord Family.qle r ε (Qn : ℝ) P) : vProfile P = profDesignQle.v := by
  have hlam : P.lam = ((profDesignQle.lam : ℚ) : ℝ) := by
    rw [hdes.2.2.2.1]
    simp only [Family.lamStar, profDesignQle, lamStarQ, ZetaQ.lamStar]
    norm_num
  have hprof : ∀ t, P.prof.eval t = profDesignQle.p t := by
    intro t
    rw [hdes.2.2.2.2.2.2.2.2.2.2.2]
    simp [Family.designProfile, designProfileQle, KProfile.p, profDesignQle, ZetaQ.Payoff.evalPoly]
    ring
  funext t
  simp only [vProfile, KProfile.v, KProfile.mass, hlam, hprof]

/-- **K8b under `hsep`** (mirror of `HFrob.hfrob_qle_of_sep`). -/
theorem hfrob_killed_of_sep (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P Family.qle Qn
        ≤ ((2 - ((PcertKD : ℚ) : ℝ)) + rowR2 Family.qle P) * NfamQ P Family.qle Qn := by
  have hε' : (0 : ℝ) < 2 / 1000000 := by norm_num
  obtain ⟨hCle, hadmK, hBK⟩ := certKD_core
  filter_upwards [frobenius_inzone_killed r ε hr hε _ hε',
    zone_compare_eventually_of_data Family.qle r ε hr hε (ZoneData.zoneLipschitzData_qle r ε),
    one_sub_zoneFactor_le_eventually Family.qle r ε hr hε 1 one_pos,
    design_regime Family.qle r ε hr hε 2000000 (by norm_num),
    design_basic Family.qle r ε hr hε] with Qn hfr hzone hzf hreg hbas
  intro P hdes hsep
  have hP := hdes.1
  obtain ⟨hlogK, -, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam1, hw8, hQn2⟩ := hbas P hdes
  obtain ⟨ha0, h1a0, h1a1⟩ := hzf P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : Real.log Qn ≤ P.LL := LL_ge_log_of_design hdes hQn1
  have hLLK : (2000000 : ℝ) ≤ P.LL := le_trans hlogK hLL
  have hw1 : P.w = 1 := w_eq_one_of_design hdes hr (by linarith)
  have hadmD := vDesign_admissible hP
  have hadmP := vProfile_admissible hP
  have ha1 : zoneFactor P ≤ 1 := by linarith
  have hC1 : (1 : ℝ) ≤ Family.qle.Cconst := one_le_Cconst Family.qle
  have hC0 : (0 : ℝ) ≤ Family.qle.Cconst := by linarith
  -- the pieces
  have h1 := hfr P hdes hsep
  have h2 := BK_eq_zoneSplit hadmD Family.qle.Cconst ha0 ha1
  have h3 := BK_vDesign_le hP hC0
  have h4 : BK Family.qle.Cconst (vProfile P) ≤ 2 - 72351 / 100000 := by
    rw [vProfile_eq_profDesignQle hdes]
    have hmono := BK_mono_C hadmK (show Family.qle.Cconst ≤ ((profDesignQle.Cplus : ℚ) : ℝ) from hCle)
    have : ((72351 / 100000 : ℚ) : ℝ) = 72351 / 100000 := by norm_num
    linarith
  have h5 := Jzone_vDesign_le hP (zoneFactor P)
  have h6 := hzone P hdes
  set c : ℝ := profMass P / (P.lam * P.aQ) with hc
  have hc1 : 1 ≤ c := one_le_c hP
  have hcle : c ≤ 1 + 8 / 3 * (P.w / P.LL) := c_le hP hlam1
  have hwLL : P.w / P.LL ≤ 1 / 2000000 := by
    rw [hw1]; exact one_div_le_one_div_of_le (by norm_num) hLLK
  have hwLL0 : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hcsq : c ^ 2 - 1 ≤ 8 * (P.w / P.LL) := by nlinarith
  have hc2 : c ^ 2 - 1 ≤ 4 / 1000000 := by linarith
  have hsZ0 : (0 : ℝ) ≤ sZone := by unfold sZone; norm_num
  have hsZ1 : sZone ≤ 51 / 100 := by unfold sZone; norm_num
  have hzrdef : zoneRowLinear Family.qle P = sZone * (1 - zoneFactor P) := rfl
  have hzr0 : 0 ≤ zoneRowLinear Family.qle P := by rw [hzrdef]; exact mul_nonneg hsZ0 h1a0
  have hzr : zoneRowLinear Family.qle P ≤ sZone := by rw [hzrdef]; nlinarith
  have hrows := minor_rows_nonneg Family.qle P
  have hL3 : 0 ≤ L₃ P := by
    unfold L₃ cRamp
    exact div_nonneg (mul_nonneg (by norm_num) hP.w_pos.le) (by linarith)
  have hrow : rowR2 Family.qle P
      = zoneRowLinear Family.qle P + L₃ P
        + (L₇ Family.qle P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ Family.qle P) := by
    unfold rowR2; ring
  have hN0 : 0 ≤ NfamQ P Family.qle Qn := NfamQ_nonneg P Family.qle Qn
  -- the chain
  have hA : Family.qle.Cconst * (Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P))
        + psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
      = BK Family.qle.Cconst (vDesign P) + (Family.qle.Cconst - 1) * Jzone (zoneFactor P) (vDesign P) := by
    rw [h2]; ring
  have hB : BK Family.qle.Cconst (vDesign P) ≤ c ^ 2 * (2 - 72351 / 100000) :=
    le_trans h3 (mul_le_mul_of_nonneg_left h4 (sq_nonneg c))
  have hJ : (Family.qle.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
      ≤ c ^ 2 * zoneRowLinear Family.qle P := by
    calc (Family.qle.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
        ≤ (Family.qle.Cconst - 1) * (c ^ 2 * Jzone (zoneFactor P) (vProfile P)) :=
          mul_le_mul_of_nonneg_left h5 (by linarith)
      _ = c ^ 2 * ((Family.qle.Cconst - 1) * Jzone (zoneFactor P) (vProfile P)) := by ring
      _ ≤ c ^ 2 * zoneRowLinear Family.qle P := mul_le_mul_of_nonneg_left h6 (sq_nonneg c)
  have hsmall : c ^ 2 * (2 - 72351 / 100000) + c ^ 2 * zoneRowLinear Family.qle P
      ≤ (2 - 72351 / 100000) + zoneRowLinear Family.qle P + 8 / 1000000 := by
    have e : c ^ 2 * (2 - 72351 / 100000) + c ^ 2 * zoneRowLinear Family.qle P
        = (2 - 72351 / 100000) + zoneRowLinear Family.qle P
          + (c ^ 2 - 1) * ((2 - 72351 / 100000) + zoneRowLinear Family.qle P) := by ring
    have hb : (c ^ 2 - 1) * ((2 - 72351 / 100000) + zoneRowLinear Family.qle P)
        ≤ 4 / 1000000 * 2 := by
      have hc20 : 0 ≤ c ^ 2 - 1 := by nlinarith
      calc (c ^ 2 - 1) * ((2 - 72351 / 100000) + zoneRowLinear Family.qle P)
          ≤ 4 / 1000000 * ((2 - 72351 / 100000) + zoneRowLinear Family.qle P) :=
            mul_le_mul_of_nonneg_right hc2 (by linarith)
        _ ≤ 4 / 1000000 * 2 := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  have hκ : ((PcertKD : ℚ) : ℝ) = 7235 / 10000 := by norm_num [PcertKD]
  have hcoef : psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
        + Family.qle.Cconst * (Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P)) + 2 / 1000000
      ≤ (2 - ((PcertKD : ℚ) : ℝ)) + rowR2 Family.qle P := by
    rw [hκ, hrow]
    linarith [hA, hB, hJ, hsmall, hrows, hL3]
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcoef hN0)

/-- **K8b.** Along ZetaQ's MARGIN design, `hsep` discharged (mirror of `Margin.hfrob_qle_of_designM`). -/
theorem hfrob_killed_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.qle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.qle Qn
        ≤ ((2 - ((PcertKD : ℚ) : ℝ)) + rowR2 Family.qle P) * NfamQ P Family.qle Qn :=
  Margin.eventually_M_of_D0free Family.qle r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.qle Qn
      ≤ ((2 - ((PcertKD : ℚ) : ℝ)) + rowR2 Family.qle P) * NfamQ P Family.qle Qn)
    (fun _ _ _ h => h)
    (by
      filter_upwards [hfrob_killed_of_sep r ε hr hε, hsep_of_design r ε hr hε] with Qn h1 h2
      intro P hdes
      exact h1 P hdes (h2 P hdes))

end LemmaK
end ZetaShell
