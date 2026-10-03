/-
Node F1c-4 (L7_3, round 4): **the Frobenius assembly at the Shell design** — `HFrob.frobenius_inzone_eventually`'s
proof (as in L7_3's K8a `frobenius_inzone_killed`) with the PP block as a premise, DERIVED from F1c-4a (rows 8 and 9:
`A1_shell`, `A2_shell` in `LF_Rows8`, `shell_row9`), F1c-4b restated (`shell_hsepS`, envelope `c₁ = 0.52`, `LF_HsepS`) and F1c-4c at that envelope (`shell_endsS`);
the ends step is `frobSqGhatFam_le_Mform_add_ends_S` (`LF_EndsS`). Round 5: was `shell_hsep`/`shell_ends`/ZetaQ's ends step.
-/
import ZetaShell.ShellK.LF_Rows8
import ZetaShell.ShellK.LF_HsepS

noncomputable section
open MeasureTheory Set Real Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Payoff ZetaQ.Zones ZetaQ.Ends ZetaQ.FamRows ZetaQ.FrobAssembly

/-- **F1c-4a.** Rows 8 and 9 along the Shell design (ZetaQ's `A1_eventually`, `A2_eventually`, `A3_eventually`). -/
theorem shell_rows89 (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars Family.qle P Qn
          ≤ (psi (vDesign P) 0 + ε' / 8) * NfamQ P Family.qle Qn ∧
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (Family.qle.sizeR Qn * err8 P Qn) ≤ ε' / 8 * NfamQ P Family.qle Qn ∧
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn) ≤ ε' / 8 * NfamQ P Family.qle Qn := by
  filter_upwards [A1_shell r ε hr hε ε' hε', A2_shell r ε hr hε ε' hε', shell_row9 r ε hr hε ε' hε']
    with Qn h1 h2 h3
  intro P hdes
  exact ⟨h1 P hdes, h2 P hdes, h3 P hdes⟩

/-- **F1c-4.** The Frobenius assembly at the Shell design, for any bound `Y` on the PP block. DERIVED from F1c-4a,
4b, 4c (the body of `HFrob.frobenius_inzone_eventually`). -/
theorem shell_assembly (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P → ∀ Y : ℝ,
      familySum Family.qle Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
          ≤ (P.aQ * P.LB) ^ 2 * Y * NfamQ P Family.qle Qn →
      frobSqGhatFam P Family.qle Qn ≤ (psi (vDesign P) 0 + Y + ε') * NfamQ P Family.qle Qn := by
  set K : ℝ := max 1 (max ((2 * Real.pi) ^ 2) (2 * Real.pi * Real.exp 8)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  filter_upwards [shell_rows89 r ε hr hε ε' hε', shell_hsepS r ε hr hε, shell_endsS r ε hr hε ε' hε',
    Design.shellDesign_regime S53L75 hS2 r ε hr hε K hK1] with Qn hrows hsep' hends hreg
  intro P hdes Y hPP
  have hP : P.Valid := hdes.1
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hsep := hsep' P hdes
  obtain ⟨-, hTK, -, -, -, -, -, -⟩ := hreg P hdes
  have hT1 : (2 * Real.pi) ^ 2 ≤ P.T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTK
  have hT2 : 2 * Real.pi * Real.exp 8 ≤ P.T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTK
  have hl : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hX : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have h0 := frobSqGhatFam_le_Mform_add_ends_S hP hw hl hX Family.qle Qn hT1 hT2 hsep
  rw [familySum_Mform_nuQ_split hP hw Family.qle Qn] at h0
  have h8 := famMform_mumu_eval P hP hw Family.qle Qn
  have h9 := famMform_muP_le_closed P hP hw Family.qle Qn
  have hc0 : 0 ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹ := by
    have := hP.aQ_pos; have := hP.LB_pos; positivity
  have h8' : familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
      ≤ MAIN8chars Family.qle P Qn + Family.qle.sizeR Qn * err8 P Qn := by
    linarith [(abs_le.mp h8).2]
  have h9' : familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ)) ≤ R9closed P Qn := by
    unfold R9closed R9fun; exact (le_abs_self _).trans h9
  obtain ⟨ha1, ha2, ha3⟩ := hrows P hdes
  have ha5 := hends P hdes
  have hone : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (P.aQ * P.LB) ^ 2 = 1 := by
    have := hP.aQ_pos.ne'; have := hP.LB_pos.ne'; field_simp
  have hN0 : 0 ≤ NfamQ P Family.qle Qn := NfamQ_nonneg P Family.qle Qn
  have hsum : familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
        + 2 * familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ))
        + familySum Family.qle Qn (fun q χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ MAIN8chars Family.qle P Qn + Family.qle.sizeR Qn * err8 P Qn + 2 * R9closed P Qn
        + (P.aQ * P.LB) ^ 2 * Y * NfamQ P Family.qle Qn := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hc0
  have e : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (MAIN8chars Family.qle P Qn + Family.qle.sizeR Qn * err8 P Qn
        + 2 * R9closed P Qn + (P.aQ * P.LB) ^ 2 * Y * NfamQ P Family.qle Qn)
      = (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars Family.qle P Qn
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (Family.qle.sizeR Qn * err8 P Qn)
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
        + Y * NfamQ P Family.qle Qn := by
    have e2 : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * ((P.aQ * P.LB) ^ 2 * Y * NfamQ P Family.qle Qn)
        = ((P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (P.aQ * P.LB) ^ 2) * (Y * NfamQ P Family.qle Qn) := by ring
    rw [mul_add, mul_add, mul_add, e2, hone, one_mul]
  have hfin : (psi (vDesign P) 0 + ε' / 8) * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
        + ε' / 8 * NfamQ P Family.qle Qn + Y * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
      ≤ (psi (vDesign P) 0 + Y + ε') * NfamQ P Family.qle Qn := by
    have e3 : (psi (vDesign P) 0 + ε' / 8) * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
        + ε' / 8 * NfamQ P Family.qle Qn + Y * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
        = (psi (vDesign P) 0 + Y + 1 / 2 * ε') * NfamQ P Family.qle Qn := by ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right (by linarith) hN0
  calc frobSqGhatFam P Family.qle Qn
      ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹
          * (familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
            + 2 * familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ))
            + familySum Family.qle Qn (fun q χ => Mform P (PXchi P χ) (PXchi P χ))) + endsMajS P := h0
    _ ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (MAIN8chars Family.qle P Qn + Family.qle.sizeR Qn * err8 P Qn
          + 2 * R9closed P Qn + (P.aQ * P.LB) ^ 2 * Y * NfamQ P Family.qle Qn) + endsMajS P := by
        linarith [hmul]
    _ = (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars Family.qle P Qn
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (Family.qle.sizeR Qn * err8 P Qn)
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
        + Y * NfamQ P Family.qle Qn + endsMajS P := by rw [e]
    _ ≤ (psi (vDesign P) 0 + ε' / 8) * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
        + ε' / 8 * NfamQ P Family.qle Qn + Y * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn := by
        linarith [ha1, ha2, ha3, ha5]
    _ ≤ _ := hfin

end F1c
end ShellK
end ZetaShell
