/-
Node K8a (L7_3): the CONSUMER of Lemma K in ZetaQ's Frobenius row. (K8b is in `LK_K8b_HfrobKilled.lean`.)

K8a `frobenius_inzone_killed`: the mirror of trunk `ZetaQ.HFrob.frobenius_inzone_eventually` (the in-zone Frobenius
assembly `frobSq ≤ [ψ(0) + K0a(a) + C·K1a(a) + ε′]·𝒩`) with the out-zone moment `K1a(a) = ∫_{|α|>a}|α|ψ` replaced by
the killed one `Jzone(a) + K1kill = ∫_{a<|α|≤1}|α|ψ + ∫_{|α|>1}ψ` (sec_lemmaK (e): "the zone-edge strip
`(1−δ′)log Q/ℒ < |α| ≤ 1` keeps its kernel `C|α|` (row L₁ unchanged) … §11's out-zone term becomes `C∫_{1<|α|≤λ}ψ`").
Proof: `frobenius_inzone_eventually`'s proof with the PP block `InZone.famPP_le_zone_split` replaced by its killed
version, whose out-zone half is Lemma K (ii) = K7 integrated against the window (draft (d): diagonal evaluation,
`s − (s − ℓ_K)₊ = min(s, ℓ_K) ≤ min(s, ℒ) + log(2πK)`, the rows of eq:EK, all `o(1)` hence `≤ ε′` eventually).

K8b `hfrob_killed_design`: the mirror of `ZetaQ.Margin.hfrob_qle_of_designM` (= `HFrob.hfrob_qle_of_sep` with `hsep`
discharged by `hsep_of_design`, transferred to the MARGIN design by `Margin.eventually_M_of_D0free`) with
`κ_cert = 2 − 0.7212` replaced by `2 − P_c`, `P_c = PcertKD = 0.7235`, at ZetaQ's OWN design (profile
`designProfileQle`, `λ*`): `B^K_{C}(v_profile) ≤ 2 − 0.7235 − 1.1·10⁻⁵` (node KC, `KCert profDesignQle`; exact value
`0.7235110849`), the killed ramp link `B^K(v_design) ≤ c²·B^K(v_profile)` (`v_design ≤ c·v_profile`, kernel `≥ 0`),
the zone split `ψ(0) + K0a + C(Jzone + K1kill) = B^K_C + (C−1)Jzone` (as `B_eq_zoneSplit`), and ZetaQ's zone row.
The slack `1.1·10⁻⁵` (against ZetaQ's `5·10⁻⁵`) needs `ε′ = 5·10⁻⁶` and `ℒ ≥ 10⁶` for `(c²−1)·sZone`; both eventual.
Difficulty: K8a M–H (a copy of ~600 lines of `InZone`/`Cor3ZoneSplit` with one block changed), K8b M.

ROUND 2 (L7_3): K8a is DERIVED here from its four sub-nodes — K8a-1 `killed_master` (killed master inequality;
consumes K7), K8a-2 `killed_saving`, K8a-3 `killed_errors`, K8a-4 `killed_chain` — through the killed PP block
`famPP_killed`; the Frobenius assembly below is `HFrob.frobenius_inzone_eventually`'s proof verbatim with
`InZone.famPP_le_zone_split` replaced by `famPP_killed`. The statement of K8a is unchanged.
-/
import ZetaShell.LemmaK.LK_K8a1_KilledMaster
import ZetaShell.LemmaK.LK_K8a2_Saving
import ZetaShell.LemmaK.LK_K8a3_Errors
import ZetaShell.LemmaK.LK_K8a4_Chain

noncomputable section
open MeasureTheory Set Real Filter
open ZetaQ ZetaQ.Payoff ZetaQ.Zones ZetaQ.Ends ZetaQ.FamRows ZetaQ.FrobAssembly

namespace ZetaShell
namespace LemmaK

/-- **The killed PP block** (the mirror of `InZone.famPP_le_zone_split` at `Family.qle`): in-zone coefficient 1,
zone edge `C·Jzone`, out-zone `C·K1kill`. From K8a-1…K8a-4. -/
theorem famPP_killed (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      familySum Family.qle Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
        ≤ (P.aQ * P.LB) ^ 2
            * (K0a (zoneFactor P) (vDesign P)
              + Family.qle.Cconst * (Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P)) + ε')
            * NfamQ P Family.qle Qn := by
  obtain ⟨e, η, he, hη, hD⟩ := killed_chain r ε hr hε ε' hε'
  obtain ⟨C₁, hA⟩ := killed_master r ε hr hε
  filter_upwards [hA, killed_saving r ε hr hε C₁ η hη, killed_errors r ε hr hε η hη, hD]
    with Qn hA' hB hC hD'
  intro P hdes
  exact le_trans (hA' P hdes e he) (hD' P hdes _ _ (hB P hdes) (hC P hdes))

/-- **K8a.** The in-zone Frobenius assembly at the killed out-zone kernel (`Family.qle`). -/
theorem frobenius_inzone_killed (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P Family.qle Qn
        ≤ (psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
            + Family.qle.Cconst * (Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P)) + ε')
          * NfamQ P Family.qle Qn := by
  set K : ℝ := max 1 (max ((2 * Real.pi) ^ 2) (2 * Real.pi * Real.exp 8)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hε8 : 0 < ε' / 8 := by positivity
  filter_upwards [A1_eventually Family.qle r ε hr hε ε' hε', A2_eventually Family.qle r ε hr hε ε' hε',
    A3_eventually Family.qle r ε hr hε ε' hε', A5_eventually Family.qle r ε hr hε ε' hε',
    famPP_killed r ε hr hε (ε' / 8) hε8, design_basic Family.qle r ε hr hε,
    design_regime Family.qle r ε hr hε K hK1] with Qn h1 h2 h3 h5 hPP hbas hreg
  intro P hdes hsep
  have hP := hdes.1
  obtain ⟨-, hTK, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hT1 : (2 * Real.pi) ^ 2 ≤ P.T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTK
  have hT2 : 2 * Real.pi * Real.exp 8 ≤ P.T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTK
  have hl : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hX : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have h0 := frobSqGhatFam_le_Mform_add_ends hP hw hl hX Family.qle Qn hT1 hT2 hsep
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
  have hpp := hPP P hdes
  have ha1 := h1 P hdes
  have ha2 := h2 P hdes
  have ha3 := h3 P hdes
  have ha5 := h5 P hdes
  have hone : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (P.aQ * P.LB) ^ 2 = 1 := by
    have := hP.aQ_pos.ne'; have := hP.LB_pos.ne'; field_simp
  have hN0 : 0 ≤ NfamQ P Family.qle Qn := NfamQ_nonneg P Family.qle Qn
  set X : ℝ := K0a (zoneFactor P) (vDesign P)
    + Family.qle.Cconst * (Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P)) + ε' / 8 with hX
  have hsum : familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
        + 2 * familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ))
        + familySum Family.qle Qn (fun q χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ MAIN8chars Family.qle P Qn + Family.qle.sizeR Qn * err8 P Qn + 2 * R9closed P Qn
        + (P.aQ * P.LB) ^ 2 * X * NfamQ P Family.qle Qn := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hc0
  have e : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (MAIN8chars Family.qle P Qn + Family.qle.sizeR Qn * err8 P Qn
        + 2 * R9closed P Qn + (P.aQ * P.LB) ^ 2 * X * NfamQ P Family.qle Qn)
      = (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars Family.qle P Qn
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (Family.qle.sizeR Qn * err8 P Qn)
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
        + X * NfamQ P Family.qle Qn := by
    have e2 : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * ((P.aQ * P.LB) ^ 2 * X * NfamQ P Family.qle Qn)
        = ((P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (P.aQ * P.LB) ^ 2) * (X * NfamQ P Family.qle Qn) := by ring
    rw [mul_add, mul_add, mul_add, e2, hone, one_mul]
  have hfin : (psi (vDesign P) 0 + ε' / 8) * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
        + ε' / 8 * NfamQ P Family.qle Qn + X * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
      ≤ (psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
          + Family.qle.Cconst * (Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P)) + ε')
          * NfamQ P Family.qle Qn := by
    have e3 : (psi (vDesign P) 0 + ε' / 8) * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
        + ε' / 8 * NfamQ P Family.qle Qn + X * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
        = (psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
          + Family.qle.Cconst * (Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P)) + 5 / 8 * ε')
          * NfamQ P Family.qle Qn := by
      rw [hX]; ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right (by linarith) hN0
  calc frobSqGhatFam P Family.qle Qn
      ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹
          * (familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
            + 2 * familySum Family.qle Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ))
            + familySum Family.qle Qn (fun q χ => Mform P (PXchi P χ) (PXchi P χ))) + endsMaj P := h0
    _ ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (MAIN8chars Family.qle P Qn + Family.qle.sizeR Qn * err8 P Qn
          + 2 * R9closed P Qn + (P.aQ * P.LB) ^ 2 * X * NfamQ P Family.qle Qn) + endsMaj P := by
        linarith [hmul]
    _ = (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars Family.qle P Qn
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (Family.qle.sizeR Qn * err8 P Qn)
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
        + X * NfamQ P Family.qle Qn + endsMaj P := by rw [e]
    _ ≤ (psi (vDesign P) 0 + ε' / 8) * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn
        + ε' / 8 * NfamQ P Family.qle Qn + X * NfamQ P Family.qle Qn + ε' / 8 * NfamQ P Family.qle Qn := by
        linarith [ha1, ha2, ha3, ha5]
    _ ≤ _ := hfin

end LemmaK
end ZetaShell
