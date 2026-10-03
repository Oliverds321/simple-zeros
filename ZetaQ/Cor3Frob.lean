/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Cor3Frob.lean — the in-zone Frobenius assembly for a PARITY family at the full-family
out-zone constant (Corollary 3″, third link).

Imports `ZetaQ.HFrob` and `ZetaQ.Cor3ZoneSplit`. Nothing existing is modified.

`frobenius_inzone_eventually_par` is `HFrob.frobenius_inzone_eventually` (proof verbatim,
generated mechanically) with its PP block taken from `Cor3Reflected.famPP_le_zone_split_par`
(the reflected sieve) instead of `InZone.famPP_le_zone_split`: for Corollary 3's parity families
the Frobenius bound is `ψ(0) + K0a + (C_F/2)·K1a + ε′`, where `C_F/2` is the FULL family constant
(`CfamEven/2 = Cfam`, `CfamEvenDyadic/2 = CfamDyadic`). This is the last analytic link of
Corollary 3″ along the tree's route: what remains is to evaluate this bound at the full
family's design (profile and bandwidth), i.e. the `Family`/design plumbing recorded in the round
report — the certificate `B_cert_le` (`B Cfam certQQsmooth ≤ 2 − 0.7212 − …`) and
`B_cert_le_dyad` are already in `HFrob`.
-/
import ZetaQ.HFrob
import ZetaQ.Cor3ZoneSplit

noncomputable section

open MeasureTheory Set Real Filter
open ZetaQ.Payoff ZetaQ.Zones ZetaQ.Ends ZetaQ.FamRows ZetaQ.FrobAssembly ZetaQ.HFrob

namespace ZetaQ
namespace Cor3Reflected

/-- **The in-zone Frobenius assembly for a parity family, at `C_F/2`.** Parity twin of
`HFrob.frobenius_inzone_eventually`:
`‖Ĝ_fam‖²_F ≤ (ψ(0) + K0a(a) + (C_F/2)·K1a(a) + ε′)·𝒩` along the design of record, under
Lemma 8.1′ (`hsep`). -/
theorem frobenius_inzone_eventually_par (F : Family) (p : ℕ)
    (hFp : ∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p))
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P F Qn
        ≤ (psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
            + F.Cconst / 2 * K1a (zoneFactor P) (vDesign P) + ε') * NfamQ P F Qn := by
  set K : ℝ := max 1 (max ((2 * Real.pi) ^ 2) (2 * Real.pi * Real.exp 8)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hε8 : 0 < ε' / 8 := by positivity
  filter_upwards [A1_eventually F r ε hr hε ε' hε', A2_eventually F r ε hr hε ε' hε',
    A3_eventually F r ε hr hε ε' hε', A5_eventually F r ε hr hε ε' hε',
    famPP_le_zone_split_par F p hFp r ε hr hε (ε' / 8) hε8, design_basic F r ε hr hε,
    design_regime F r ε hr hε K hK1] with Qn h1 h2 h3 h5 hPP hbas hreg
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
  have h0 := frobSqGhatFam_le_Mform_add_ends hP hw hl hX F Qn hT1 hT2 hsep
  rw [familySum_Mform_nuQ_split hP hw F Qn] at h0
  have h8 := famMform_mumu_eval P hP hw F Qn
  have h9 := famMform_muP_le_closed P hP hw F Qn
  have hc0 : 0 ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹ := by
    have := hP.aQ_pos; have := hP.LB_pos; positivity
  have h8' : familySum F Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
      ≤ MAIN8chars F P Qn + F.sizeR Qn * err8 P Qn := by linarith [(abs_le.mp h8).2]
  have h9' : familySum F Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ)) ≤ R9closed P Qn := by
    unfold R9closed R9fun; exact (le_abs_self _).trans h9
  have hpp := hPP P hdes
  have ha1 := h1 P hdes
  have ha2 := h2 P hdes
  have ha3 := h3 P hdes
  have ha5 := h5 P hdes
  have hone : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (P.aQ * P.LB) ^ 2 = 1 := by
    have := hP.aQ_pos.ne'; have := hP.LB_pos.ne'; field_simp
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  set X : ℝ := K0a (zoneFactor P) (vDesign P) + F.Cconst / 2 * K1a (zoneFactor P) (vDesign P)
    + ε' / 8 with hX
  have hsum : familySum F Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
        + 2 * familySum F Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ))
        + familySum F Qn (fun q χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ MAIN8chars F P Qn + F.sizeR Qn * err8 P Qn + 2 * R9closed P Qn
        + (P.aQ * P.LB) ^ 2 * X * NfamQ P F Qn := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hc0
  have e : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (MAIN8chars F P Qn + F.sizeR Qn * err8 P Qn + 2 * R9closed P Qn
        + (P.aQ * P.LB) ^ 2 * X * NfamQ P F Qn)
      = (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars F P Qn
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (F.sizeR Qn * err8 P Qn)
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
        + X * NfamQ P F Qn := by
    have e2 : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * ((P.aQ * P.LB) ^ 2 * X * NfamQ P F Qn)
        = ((P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (P.aQ * P.LB) ^ 2) * (X * NfamQ P F Qn) := by ring
    rw [mul_add, mul_add, mul_add, e2, hone, one_mul]
  have hfin : (psi (vDesign P) 0 + ε' / 8) * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn
        + ε' / 8 * NfamQ P F Qn + X * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn
      ≤ (psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
          + F.Cconst / 2 * K1a (zoneFactor P) (vDesign P) + ε') * NfamQ P F Qn := by
    have e3 : (psi (vDesign P) 0 + ε' / 8) * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn
        + ε' / 8 * NfamQ P F Qn + X * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn
        = (psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
          + F.Cconst / 2 * K1a (zoneFactor P) (vDesign P) + 5 / 8 * ε') * NfamQ P F Qn := by
      rw [hX]; ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right (by linarith) hN0
  calc frobSqGhatFam P F Qn
      ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹
          * (familySum F Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
            + 2 * familySum F Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ))
            + familySum F Qn (fun q χ => Mform P (PXchi P χ) (PXchi P χ))) + endsMaj P := h0
    _ ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (MAIN8chars F P Qn + F.sizeR Qn * err8 P Qn + 2 * R9closed P Qn
          + (P.aQ * P.LB) ^ 2 * X * NfamQ P F Qn) + endsMaj P := by linarith [hmul]
    _ = (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars F P Qn
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (F.sizeR Qn * err8 P Qn)
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
        + X * NfamQ P F Qn + endsMaj P := by rw [e]
    _ ≤ (psi (vDesign P) 0 + ε' / 8) * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn
        + ε' / 8 * NfamQ P F Qn + X * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn := by
        linarith [ha1, ha2, ha3, ha5]
    _ ≤ _ := hfin

/-- **The Frobenius row at `κ_cert = 2 − 0.7098` for a PARITY character set run at the dyadic
design** (Corollary 3″, dyadic, conditional on the design data). Parity twin of
`HFrob.hfrob_dyadic_of_sep` (proof generated verbatim): for any `F` whose characters are one parity
class (`hFp`) and whose design data are the DYADIC family's (`hC : F.Cconst / 2 = CfamDyadic`,
`hs`, `hκ`, `hprofF`, `hlamF`), with the zone comparison at `C_F/2` (`hzoneE`, what
`ZoneData.zoneLipschitzData_dyadic` certifies for `C = CfamDyadic` at the dyadic profile), the
Frobenius row holds at Corollary 2's `κ_cert`. The out-zone half comes from the reflected sieve
(`frobenius_inzone_eventually_par`); the payoff certificate is Corollary 2's own
(`B_vProfile_le_dyad`). No current `Family` constructor has these data — the four parity
constructors carry their refit designs — so this is the statement the Corollary 3″ plumbing
(a parity family with the full family's design) instantiates, by `rfl`. -/
theorem hfrob_par_dyad_of_sep {F : Family} {p : ℕ}
    (hFp : ∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p))
    (hC : F.Cconst / 2 = CfamDyadic) (hs : F.sZoneF = sZoneDyadic)
    (hκ : F.kappaCert = 2 - 7098 / 10000)
    (hprofF : F.designProfile = designProfileDyadic) (hlamF : F.lamStar = lamStarDyadic)
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hzoneE : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (F.Cconst / 2 - 1) * Jzone (zoneFactor P) (vProfile P) ≤ zoneRowLinear F P) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P F Qn
        ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn := by
  have hε' : (0 : ℝ) < 2 / 100000 := by norm_num
  filter_upwards [frobenius_inzone_eventually_par F p hFp r ε hr hε _ hε',
    hzoneE,
    one_sub_zoneFactor_le_eventually F r ε hr hε 1 one_pos,
    design_regime F r ε hr hε 250000 (by norm_num),
    design_basic F r ε hr hε] with Qn hfr hzone hzf hreg hbas
  intro P hdes hsep
  have hP := hdes.1
  obtain ⟨hlogK, -, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam1, hw8, hQn2⟩ := hbas P hdes
  obtain ⟨ha0, h1a0, h1a1⟩ := hzf P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : Real.log Qn ≤ P.LL := LL_ge_log_of_design hdes hQn1
  have hLLK : (250000 : ℝ) ≤ P.LL := le_trans hlogK hLL
  have hw1 : P.w = 1 := w_eq_one_of_design hdes hr (by linarith)
  have hprof : P.prof = designProfileDyadic := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.2, hprofF]
  have hlam : P.lam = lamStarDyadic := by rw [hdes.2.2.2.1, hlamF]
  have hadmD := vDesign_admissible hP
  have ha1 : zoneFactor P ≤ 1 := by linarith
  have h1 := hfr P hdes hsep
  have h2 := B_eq_zoneSplit hadmD (F.Cconst / 2) ha0 ha1
  -- the ramp link at the dyadic design, directly (`profileRampLink_sharp_dyadic`), inside `L₃`
  have h3 : B (F.Cconst / 2) (vDesign P) ≤ B (F.Cconst / 2) (vProfile P) + L₃ P := by
    have hwL : 100 * P.w ≤ P.LL := by rw [hw1]; linarith
    have h := profileRampLink_sharp_dyadic hP hprof hlam hwL
    rw [hC]
    have ht : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
    have e : L₃ P = 6 * (P.w / P.LB) := by unfold L₃ cRamp; ring
    have e2 : P.w / P.LB = (P.w / P.LL) * (1 / lamStarDyadic) := by
      show P.w / (P.lam * P.LL) = _
      rw [hlam]
      have hLL0 : P.LL ≠ 0 := hP.LL_pos.ne'
      have hl0 : lamStarDyadic ≠ 0 := by unfold lamStarDyadic; norm_num
      field_simp
    have hnum : (8925 / 10000 : ℝ) ≤ 6 * (1 / lamStarDyadic) := by
      unfold lamStarDyadic; norm_num
    rw [e, e2]
    nlinarith [mul_le_mul_of_nonneg_left hnum ht]
  have h4 : B (F.Cconst / 2) (vProfile P) ≤ 2 - 7098 / 10000 - 4 / 100000 := by
    rw [hC]
    exact B_vProfile_le_dyad hprof hlam
  have h5 := Jzone_vDesign_le hP (zoneFactor P)
  have h6 : ((F.Cconst / 2) - 1) * Jzone (zoneFactor P) (vProfile P)
      ≤ zoneRowLinear F P := hzone P hdes
  set c : ℝ := profMass P / (P.lam * P.aQ) with hc
  have hc1 : 1 ≤ c := one_le_c hP
  have hcle : c ≤ 1 + 8 / 3 * (P.w / P.LL) := c_le hP hlam1
  have hwLL : P.w / P.LL ≤ 1 / 250000 := by
    rw [hw1]; exact one_div_le_one_div_of_le (by norm_num) hLLK
  have hwLL0 : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hc2 : c ≤ 2 := by linarith
  have hcsq : c ^ 2 - 1 ≤ 8 * (P.w / P.LL) := by nlinarith
  have hsD0 : (0 : ℝ) ≤ sZoneDyadic := by unfold sZoneDyadic; norm_num
  have hsD1 : sZoneDyadic ≤ 55 / 100 := by unfold sZoneDyadic; norm_num
  -- the family-aware zone row, at `F`, is `sZoneDyadic·(1 − a)` (`rfl`)
  have hzrdef : zoneRowLinear F P = sZoneDyadic * (1 - zoneFactor P) := by
    unfold zoneRowLinear; rw [hs]
  have hzD0 : 0 ≤ zoneRowLinear F P := by rw [hzrdef]; exact mul_nonneg hsD0 h1a0
  have hzD : zoneRowLinear F P ≤ sZoneDyadic := by rw [hzrdef]; nlinarith
  have hC1 : 0 ≤ F.Cconst / 2 - 1 := by
    have h1d : (1 : ℝ) ≤ CfamDyadic := one_le_Cconst Family.dyadic
    rw [hC]; linarith
  have hJ : ((F.Cconst / 2) - 1) * Jzone (zoneFactor P) (vDesign P)
      ≤ zoneRowLinear F P + 2 / 100000 := by
    have hA : (c ^ 2 - 1) * zoneRowLinear F P
        ≤ 8 * (P.w / P.LL) * sZoneDyadic := by
      calc (c ^ 2 - 1) * zoneRowLinear F P
          ≤ 8 * (P.w / P.LL) * zoneRowLinear F P :=
            mul_le_mul_of_nonneg_right hcsq hzD0
        _ ≤ 8 * (P.w / P.LL) * sZoneDyadic := mul_le_mul_of_nonneg_left hzD (by positivity)
    have hB : 8 * (P.w / P.LL) * sZoneDyadic ≤ 2 / 100000 := by
      calc 8 * (P.w / P.LL) * sZoneDyadic ≤ 8 * (1 / 250000) * (55 / 100) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hwLL (by norm_num)) hsD1 hsD0 (by norm_num)
        _ ≤ 2 / 100000 := by norm_num
    calc ((F.Cconst / 2) - 1) * Jzone (zoneFactor P) (vDesign P)
        ≤ ((F.Cconst / 2) - 1) * (c ^ 2 * Jzone (zoneFactor P) (vProfile P)) :=
          mul_le_mul_of_nonneg_left h5 hC1
      _ = c ^ 2 * (((F.Cconst / 2) - 1) * Jzone (zoneFactor P) (vProfile P)) := by ring
      _ ≤ c ^ 2 * zoneRowLinear F P := mul_le_mul_of_nonneg_left h6 (sq_nonneg c)
      _ = zoneRowLinear F P + (c ^ 2 - 1) * zoneRowLinear F P := by
          ring
      _ ≤ zoneRowLinear F P + 2 / 100000 := by linarith
  have hrows := minor_rows_nonneg F P
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hrow : rowR2 F P
      = zoneRowLinear F P + L₃ P
        + (L₇ F P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ F P) := by
    unfold rowR2; ring
  have hcoef : psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
        + (F.Cconst / 2) * K1a (zoneFactor P) (vDesign P) + 2 / 100000
      ≤ F.kappaCert + rowR2 F P := by
    rw [hκ, hrow]
    linarith [h2, h3, h4, hJ, hrows]
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcoef hN0)

/-- **The Frobenius row at `κ_cert = 2 − 0.7212` for a PARITY character set run at the `q ≤ Q`
design** (Corollary 3″, `q ≤ Q`, conditional on the design data): parity twin of
`HFrob.hfrob_qle_of_sep`, exactly as `hfrob_par_dyad_of_sep` is of `hfrob_dyadic_of_sep`. -/
theorem hfrob_par_qle_of_sep {F : Family} {p : ℕ}
    (hFp : ∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p))
    (hC : F.Cconst / 2 = Cfam) (hs : F.sZoneF = sZone)
    (hκ : F.kappaCert = 2 - 7212 / 10000)
    (hprofF : F.designProfile = designProfileQle) (hlamF : F.lamStar = lamStar)
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hzoneE : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (F.Cconst / 2 - 1) * Jzone (zoneFactor P) (vProfile P) ≤ zoneRowLinear F P) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P F Qn
        ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn := by
  have hε' : (0 : ℝ) < 25 / 1000000 := by norm_num
  filter_upwards [frobenius_inzone_eventually_par F p hFp r ε hr hε _ hε',
    hzoneE,
    one_sub_zoneFactor_le_eventually F r ε hr hε 1 one_pos,
    design_regime F r ε hr hε 200000 (by norm_num),
    design_basic F r ε hr hε] with Qn hfr hzone hzf hreg hbas
  intro P hdes hsep
  have hP := hdes.1
  obtain ⟨hlogK, -, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam1, hw8, hQn2⟩ := hbas P hdes
  obtain ⟨ha0, h1a0, h1a1⟩ := hzf P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : Real.log Qn ≤ P.LL := LL_ge_log_of_design hdes hQn1
  have hLLK : (200000 : ℝ) ≤ P.LL := le_trans hlogK hLL
  have hw1 : P.w = 1 := w_eq_one_of_design hdes hr (by linarith)
  have hprof : P.prof = designProfileQle := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.2, hprofF]
  have hlam : P.lam = lamStar := by rw [hdes.2.2.2.1, hlamF]
  have hadmD := vDesign_admissible hP
  have ha1 : zoneFactor P ≤ 1 := by linarith
  -- the pieces
  have h1 := hfr P hdes hsep
  have h2 := B_eq_zoneSplit hadmD (F.Cconst / 2) ha0 ha1
  -- the ramp link at the q ≤ Q design, directly (`profileRampLink_sharp_qle`), inside `L₃`
  have h3 : B (F.Cconst / 2) (vDesign P) ≤ B (F.Cconst / 2) (vProfile P) + L₃ P := by
    have hwL : 100 * P.w ≤ P.LL := by rw [hw1]; linarith
    have h := profileRampLink_sharp_qle hP hprof hlam hwL
    rw [hC]
    have ht : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
    have e : L₃ P = 6 * (P.w / P.LB) := by unfold L₃ cRamp; ring
    have e2 : P.w / P.LB = (P.w / P.LL) * (1 / lamStar) := by
      show P.w / (P.lam * P.LL) = _
      rw [hlam]
      have hLL0 : P.LL ≠ 0 := hP.LL_pos.ne'
      have hl0 : lamStar ≠ 0 := by unfold lamStar; norm_num
      field_simp
    have hnum : (675 / 1000 : ℝ) ≤ 6 * (1 / lamStar) := by
      unfold lamStar; norm_num
    rw [e, e2]
    nlinarith [mul_le_mul_of_nonneg_left hnum ht]
  have h4 : B (F.Cconst / 2) (vProfile P) ≤ 2 - 7212 / 10000 - 5 / 100000 := by
    rw [hC]
    exact B_vProfile_le hprof hlam
  have h5 := Jzone_vDesign_le hP (zoneFactor P)
  have h6 := hzone P hdes
  -- `c = profMass/(λa)`: `1 ≤ c ≤ 1 + (8/3)/ℒ ≤ 2`, `c² − 1 ≤ 8/ℒ`
  set c : ℝ := profMass P / (P.lam * P.aQ) with hc
  have hc1 : 1 ≤ c := one_le_c hP
  have hcle : c ≤ 1 + 8 / 3 * (P.w / P.LL) := c_le hP hlam1
  have hwLL : P.w / P.LL ≤ 1 / 200000 := by
    rw [hw1]; exact one_div_le_one_div_of_le (by norm_num) hLLK
  have hwLL0 : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hc2 : c ≤ 2 := by linarith
  have hcsq : c ^ 2 - 1 ≤ 8 * (P.w / P.LL) := by nlinarith
  have hsZ0 : (0 : ℝ) ≤ sZone := by unfold sZone; norm_num
  have hsZ1 : sZone ≤ 51 / 100 := by unfold sZone; norm_num
  -- the family-aware zone row, at `F`, is `sZone·(1 − a)` (`rfl`)
  have hzrdef : zoneRowLinear F P = sZone * (1 - zoneFactor P) := by
    unfold zoneRowLinear; rw [hs]
  have hzr0 : 0 ≤ zoneRowLinear F P := by rw [hzrdef]; exact mul_nonneg hsZ0 h1a0
  have hzr : zoneRowLinear F P ≤ sZone := by
    rw [hzrdef]; nlinarith
  have hC1 : 0 ≤ F.Cconst / 2 - 1 := by
    have h1d : (1 : ℝ) ≤ Cfam := one_le_Cconst Family.qle
    rw [hC]; linarith
  have hJ : ((F.Cconst / 2) - 1) * Jzone (zoneFactor P) (vDesign P)
      ≤ zoneRowLinear F P + 25 / 1000000 := by
    have hA : (c ^ 2 - 1) * zoneRowLinear F P ≤ 8 * (P.w / P.LL) * sZone := by
      calc (c ^ 2 - 1) * zoneRowLinear F P
          ≤ 8 * (P.w / P.LL) * zoneRowLinear F P :=
            mul_le_mul_of_nonneg_right hcsq hzr0
        _ ≤ 8 * (P.w / P.LL) * sZone := mul_le_mul_of_nonneg_left hzr (by positivity)
    have hB : 8 * (P.w / P.LL) * sZone ≤ 25 / 1000000 := by
      calc 8 * (P.w / P.LL) * sZone ≤ 8 * (1 / 200000) * (51 / 100) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hwLL (by norm_num)) hsZ1 hsZ0 (by norm_num)
        _ ≤ 25 / 1000000 := by norm_num
    calc ((F.Cconst / 2) - 1) * Jzone (zoneFactor P) (vDesign P)
        ≤ ((F.Cconst / 2) - 1) * (c ^ 2 * Jzone (zoneFactor P) (vProfile P)) :=
          mul_le_mul_of_nonneg_left h5 hC1
      _ = c ^ 2 * (((F.Cconst / 2) - 1) * Jzone (zoneFactor P) (vProfile P)) := by ring
      _ ≤ c ^ 2 * zoneRowLinear F P := mul_le_mul_of_nonneg_left h6 (sq_nonneg c)
      _ = zoneRowLinear F P + (c ^ 2 - 1) * zoneRowLinear F P := by ring
      _ ≤ zoneRowLinear F P + 25 / 1000000 := by linarith
  have hrows := minor_rows_nonneg F P
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hrow : rowR2 F P
      = zoneRowLinear F P + L₃ P
        + (L₇ F P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ F P) := by
    unfold rowR2; ring
  have hcoef : psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
        + (F.Cconst / 2) * K1a (zoneFactor P) (vDesign P) + 25 / 1000000
      ≤ F.kappaCert + rowR2 F P := by
    rw [hκ, hrow]
    linarith [h2, h3, h4, hJ, hrows]
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcoef hN0)

end Cor3Reflected
end ZetaQ
