/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/HFrob.lean — **THE LAST INPUT OF THEOREM 1: the Frobenius row at `κ_cert + rowR2`**,
for `Family.qle` (§4) and for `Family.dyadic` (§7), under the
family-ends separation `hsep` (Lemma 8.1′, discharged along the design in §6 for both families).

Route (every piece landed, nothing restated):
  frobSq ≤ (a²L²)⁻¹[Σ𝓜μμ + 2Σ𝓜μP + ΣPP] + endsMaj            (`frobSqGhatFam_le_Mform_add_ends`)
         ≤ [ψ(0) + K0a(a) + C·K1a(a) + ε′]·𝒩                   (A1, A2, A3, A5 + `famPP_le_zone_split`)
         = [B_C(v_design) + (C−1)·Jzone_a(v_design) + ε′]·𝒩    (`B_eq_zoneSplit`)
         ≤ [B_C(v_profile) + L₃ + c²·(C−1)·Jzone_a(v_profile) + ε′]·𝒩
                                                   (`profileRampLink_design_L₃`; `v_design ≤ c·v_profile`,
                                                    `c = profMass/(λa) = 1 + O(w/ℒ)`, `cv_sub_v_nonneg`)
         ≤ [2 − 0.7212 − 5·10⁻⁵ + L₃ + zoneRowLinear + (c²−1)·sZone + ε′]·𝒩
                                                   (cert slack `B0 + 5.412·B1 ≤ 2 − 0.7212 − 5·10⁻⁵`,
                                                    `v_profile =ᵐ certQQsmooth.toFun`; `zone_compare_eventually_of_data`
                                                    + `zoneLipschitzData_qle`)
         ≤ [κ_cert + rowR2]·𝒩                                  (ε′ := 2.5·10⁻⁵, (c²−1)·sZone ≤ 2.5·10⁻⁵ once ℒ ≥ 2·10⁵).

The FIXED certificate slack `5·10⁻⁵` (= 2 − 0.7212 − (B0 + 5.412·B1) = 5.04·10⁻⁵) absorbs every
`o(1)` term of the landed `ε′`-lemmas, so `hfrob` holds EXACTLY (no `cX/ℒ` variant is needed).

**The zone row is family-aware** (`zoneRowLinear F P = F.sZoneF·(1 − a)`,
`sZoneDyadic = 0.5485` for the dyadic family), so §7's dyadic row is now EXACT too —
`hfrob_dyadic_of_sep : ‖Ĝ_fam‖²_F ≤ (κ_cert + rowR2 Family.dyadic)·𝒩` (no excess term), through
`zone_compare_eventually_of_data` at `ZoneData.zoneLipschitzData_dyadic` — and
`hsep_of_design_dyadic` discharges `hsep` for the dyadic family. Corollary 2 at the certified
constant therefore carries no named hypothesis (`JoinProved.corollary_two_dyadic_proved'`).
-/
import ZetaQ.FrobAssembly
import ZetaQ.InZone
import ZetaQ.ZoneData
import ZetaQ.RampLinkSharp
import ZetaQ.JoinCert
import ZetaQ.PayoffSmooth

noncomputable section

open MeasureTheory Set Real Filter
open ZetaQ.Payoff ZetaQ.Zones ZetaQ.Ends ZetaQ.FamRows ZetaQ.FrobAssembly

namespace ZetaQ
namespace HFrob

variable {P : ParamsQ}

/-! ## §1. The `q ≤ Q` smooth certificate IS `v_profile` at the design, with slack -/

/-- the exact core mass `M = ∫_{−λ*/2}^{λ*/2} p²` of the `q ≤ Q` design profile. -/
def Mqle : ℝ :=
  (911157075163965985000909686906805446389956404111949405356457505494671648996269134536639987279976667019962850846654410639923208299895409103 : ℝ)
    / 930128855040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem profMass_val (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar) :
    profMass P = Mqle := by
  rw [ZoneData.profMass_eq_qle hprof hlam]; unfold sqPrim lamStar Mqle; norm_num

theorem block0_eq (u : ℝ) :
    evalPoly (certQQsmooth.coeff.getD 0 []) u = ZoneData.pQ u ^ 2 / Mqle := by
  unfold Mqle
  norm_num [certQQsmooth, evalPoly, ZoneData.pQ]
  ring

theorem block1_eq (u : ℝ) :
    evalPoly (certQQsmooth.coeff.getD 1 []) (u - 1498535697 / 4000000000)
      = ZoneData.pQ u ^ 2 / Mqle := by
  unfold Mqle
  norm_num [certQQsmooth, evalPoly, ZoneData.pQ]
  ring

theorem cert_slack :
    (B0_certQQsmooth : ℚ) + 5412 / 1000 * B1_certQQsmooth ≤ 2 - 7212 / 10000 - 5 / 100000 := by
  norm_num [B0_certQQsmooth, B1_certQQsmooth]

theorem toFunNonneg_unfold (u : ℝ) :
    certQQsmooth.toFunNonneg u
      = Set.indicator (Set.Ico (0 : ℝ) (1498535697 / 4000000000))
          (fun t => evalPoly (certQQsmooth.coeff.getD 0 []) (t - 0)) u
        + Set.indicator (Set.Ico (1498535697 / 4000000000 : ℝ) (2501464303 / 4000000000))
          (fun t => evalPoly (certQQsmooth.coeff.getD 1 []) (t - 1498535697 / 4000000000)) u := by
  have hlen : certQQsmooth.xs.length = 1 := rfl
  have hn0 : ((certQQsmooth.node 0 : ℚ) : ℝ) = 0 := by simp [Cert.node, Cert.nodes, certQQsmooth]
  have hn1 : ((certQQsmooth.node 1 : ℚ) : ℝ) = 1498535697 / 4000000000 := by
    simp [Cert.node, Cert.nodes, certQQsmooth]
  have hn2 : ((certQQsmooth.node 2 : ℚ) : ℝ) = 2501464303 / 4000000000 := by
    simp [Cert.node, Cert.nodes, certQQsmooth]
  simp only [Cert.toFunNonneg, hlen, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hn0, hn1, hn2]

theorem pQ_abs (t : ℝ) : ZoneData.pQ |t| = ZoneData.pQ t := by
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> unfold ZoneData.pQ <;> ring

/-- `certQQsmooth.toFun = v_profile` off the two points `|t| = λ*/2`. -/
theorem toFun_eq_vProfile (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar)
    (t : ℝ) (ht : |t| ≠ lamStar / 2) : certQQsmooth.toFun t = vProfile P t := by
  have hb : lamStar / 2 = 2501464303 / 4000000000 := by unfold lamStar; norm_num
  have htf : certQQsmooth.toFun t = certQQsmooth.toFunNonneg |t| := rfl
  have hpM : (P.prof.eval t) ^ 2 / profMass P = ZoneData.pQ t ^ 2 / Mqle := by
    rw [hprof, ZoneData.eval_designProfileQle, profMass_val hprof hlam]
  have hu0 : 0 ≤ |t| := abs_nonneg t
  rw [htf, toFunNonneg_unfold, vProfile_eq, hlam, hb]
  rw [hb] at ht
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · rw [if_pos hlt.le, hpM]
    by_cases h2 : |t| < 1498535697 / 4000000000
    · rw [indicator_of_mem (Set.mem_Ico.mpr ⟨hu0, h2⟩),
        indicator_of_notMem (fun h => absurd h.1 (not_le.mpr h2)), sub_zero, block0_eq, pQ_abs]
      ring
    · rw [indicator_of_notMem (fun h => h2 h.2),
        indicator_of_mem (Set.mem_Ico.mpr ⟨not_lt.mp h2, hlt⟩), block1_eq, pQ_abs]
      ring
  · rw [if_neg (not_le.mpr hgt)]
    have h3 : ¬ |t| < 1498535697 / 4000000000 := by
      intro h; linarith
    rw [indicator_of_notMem (fun h => h3 h.2),
      indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hgt.le))]
    ring

theorem vProfile_ae_eq (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar) :
    vProfile P =ᵐ[volume] certQQsmooth.toFun := by
  rw [Filter.EventuallyEq, ae_iff]
  have hS : {t : ℝ | ¬ vProfile P t = certQQsmooth.toFun t} ⊆ {lamStar / 2, -(lamStar / 2)} := by
    intro t ht
    simp only [mem_setOf_eq] at ht
    by_contra hmem
    apply ht
    rw [toFun_eq_vProfile hprof hlam t]
    intro habs
    apply hmem
    rcases abs_eq (by unfold lamStar; norm_num : (0 : ℝ) ≤ lamStar / 2) |>.mp habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hS (((Set.finite_singleton _).insert _).measure_zero volume)

theorem psi_vProfile_eq_cert (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar) :
    psi (vProfile P) = psi certQQsmooth.toFun := by
  funext α
  unfold psi
  apply integral_congr_ae
  have h1 := vProfile_ae_eq hprof hlam
  have h2 : (vProfile P ∘ fun t => t - α) =ᵐ[volume] (certQQsmooth.toFun ∘ fun t => t - α) :=
    (measurePreserving_sub_right volume α).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with t ht1 ht2
  simp only [Function.comp] at ht2
  rw [ht1, ht2]

/-- the certificate with slack: `B_{π⁴/18}(cert) ≤ 2 − 0.7212 − 5·10⁻⁵`. -/
theorem B_cert_le : B Cfam certQQsmooth.toFun ≤ 2 - 7212 / 10000 - 5 / 100000 := by
  have hadm := certQQsmooth.admissible certQQsmooth_NonnegOK certQQsmooth_MassOK
  have hB1 : 0 ≤ B1 certQQsmooth.toFun := B1_nonneg hadm
  have hC : Cfam ≤ ((5412 / 1000 : ℚ) : ℝ) := by unfold Cfam; exact C_qQ_le
  calc B Cfam certQQsmooth.toFun
      = B0 certQQsmooth.toFun + Cfam * B1 certQQsmooth.toFun := B_eq_B0_add_C_mul_B1 _ hadm
    _ ≤ B0 certQQsmooth.toFun + ((5412 / 1000 : ℚ) : ℝ) * B1 certQQsmooth.toFun := by
        nlinarith [mul_le_mul_of_nonneg_right hC hB1]
    _ = ((B0_certQQsmooth + 5412 / 1000 * B1_certQQsmooth : ℚ) : ℝ) := by
        rw [B0B1_certQQsmooth.1, B0B1_certQQsmooth.2]; push_cast; ring
    _ ≤ ((2 - 7212 / 10000 - 5 / 100000 : ℚ) : ℝ) := by exact_mod_cast cert_slack
    _ = 2 - 7212 / 10000 - 5 / 100000 := by push_cast; ring

/-- **`B_{π⁴/18}(v_profile) ≤ 2 − 0.7212 − 5·10⁻⁵` at the `q ≤ Q` design** (the identification
`v_profile =ᵐ certQQsmooth.toFun` + the certificate with slack). -/
theorem B_vProfile_le (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar) :
    B Cfam (vProfile P) ≤ 2 - 7212 / 10000 - 5 / 100000 := by
  have h := B_cert_le
  unfold B at h ⊢
  rwa [psi_vProfile_eq_cert hprof hlam]

/-! ## §2. `v_design ≤ c·v_profile` pointwise, hence `ψ`, `Jzone` dominated by `c²·(…)` -/

theorem psi_vDesign_le (hP : P.Valid) (α : ℝ) :
    psi (vDesign P) α ≤ (profMass P / (P.lam * P.aQ)) ^ 2 * psi (vProfile P) α := by
  set c : ℝ := profMass P / (P.lam * P.aQ) with hc
  have hc0 : 0 ≤ c := div_nonneg (profMass_pos hP).le (mul_pos hP.lam_pos hP.aQ_pos).le
  have hle : ∀ t, vDesign P t ≤ c * vProfile P t := fun t => by linarith [cv_sub_v_nonneg hP t]
  have hint : Integrable (fun t => vProfile P t * vProfile P (t - α)) := by
    refine Integrable.bdd_mul (c := 1 / profMass P) ((vProfile_integrable P).comp_sub_right α)
      (vProfile_integrable P).aestronglyMeasurable (ae_of_all _ (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (vProfile_nonneg hP t)]
    exact vProfile_le hP t
  unfold psi
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact ae_of_all _ (fun t => mul_nonneg (vDesign_nonneg hP t) (vDesign_nonneg hP _))
  · exact hint.const_mul _
  · refine ae_of_all _ (fun t => ?_)
    have h := mul_le_mul (hle t) (hle (t - α)) (vDesign_nonneg hP (t - α))
      (mul_nonneg hc0 (vProfile_nonneg hP t))
    calc vDesign P t * vDesign P (t - α) ≤ (c * vProfile P t) * (c * vProfile P (t - α)) := h
      _ = c ^ 2 * (vProfile P t * vProfile P (t - α)) := by ring

theorem Jzone_vDesign_le (hP : P.Valid) (a : ℝ) :
    Jzone a (vDesign P) ≤ (profMass P / (P.lam * P.aQ)) ^ 2 * Jzone a (vProfile P) := by
  unfold Jzone
  rw [← integral_const_mul]
  apply setIntegral_mono_on
  · exact (absPsi_integrable (vDesign_admissible hP)).integrableOn
  · exact ((absPsi_integrable (vProfile_admissible hP)).const_mul _).integrableOn
  · exact measurableSet_strip a
  · intro x _
    have h := psi_vDesign_le hP x
    have h0 := abs_nonneg x
    calc |x| * psi (vDesign P) x
        ≤ |x| * ((profMass P / (P.lam * P.aQ)) ^ 2 * psi (vProfile P) x) :=
          mul_le_mul_of_nonneg_left h h0
      _ = (profMass P / (P.lam * P.aQ)) ^ 2 * (|x| * psi (vProfile P) x) := by ring

/-- `c = profMass/(λa) ≤ 1 + (8/3)·(w/ℒ)` for `λ ≥ 1` (from `profMass − λa ≤ 2w/ℒ`, `a ≥ 3/4`). -/
theorem c_le (hP : P.Valid) (hlam1 : 1 ≤ P.lam) :
    profMass P / (P.lam * P.aQ) ≤ 1 + 8 / 3 * (P.w / P.LL) := by
  have hN : 0 < P.lam * P.aQ := mul_pos hP.lam_pos hP.aQ_pos
  have hwL0 : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hla : 3 / 4 ≤ P.lam * P.aQ :=
    le_trans hP.a_ge (le_mul_of_one_le_left hP.aQ_pos.le hlam1)
  have hsub := profMass_sub_le hP
  rw [div_le_iff₀ hN]
  nlinarith [mul_le_mul_of_nonneg_left hla hwL0]

theorem one_le_c (hP : P.Valid) : 1 ≤ profMass P / (P.lam * P.aQ) := by
  rw [le_div_iff₀ (mul_pos hP.lam_pos hP.aQ_pos), one_mul]
  exact lam_mul_aQ_le_profMass hP

/-! ## §3. The in-zone Frobenius assembly, eventually: `ψ(0) + K0a + C·K1a + ε′`
(the mirror of `frobenius_sieve_eventually` with the PP block from `famPP_le_zone_split`). -/

theorem frobenius_inzone_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P F Qn
        ≤ (psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
            + F.Cconst * K1a (zoneFactor P) (vDesign P) + ε') * NfamQ P F Qn := by
  set K : ℝ := max 1 (max ((2 * Real.pi) ^ 2) (2 * Real.pi * Real.exp 8)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hε8 : 0 < ε' / 8 := by positivity
  filter_upwards [A1_eventually F r ε hr hε ε' hε', A2_eventually F r ε hr hε ε' hε',
    A3_eventually F r ε hr hε ε' hε', A5_eventually F r ε hr hε ε' hε',
    InZone.famPP_le_zone_split F r ε hr hε (ε' / 8) hε8, design_basic F r ε hr hε,
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
  set X : ℝ := K0a (zoneFactor P) (vDesign P) + F.Cconst * K1a (zoneFactor P) (vDesign P)
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
          + F.Cconst * K1a (zoneFactor P) (vDesign P) + ε') * NfamQ P F Qn := by
    have e3 : (psi (vDesign P) 0 + ε' / 8) * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn
        + ε' / 8 * NfamQ P F Qn + X * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn
        = (psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
          + F.Cconst * K1a (zoneFactor P) (vDesign P) + 5 / 8 * ε') * NfamQ P F Qn := by
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

/-! ## §4. THE FROBENIUS ROW AT `κ_cert + rowR2` FOR `Family.qle`, eventually, under `hsep` -/

theorem minor_rows_nonneg (F : Family) (P : ParamsQ) :
    0 ≤ L₇ F P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ F P := by
  have hd : 0 ≤ dPdlogC := by
    unfold dPdlogC
    exact div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  have hcc : 0 ≤ cCross := Real.sqrt_nonneg _
  have hCq : 0 ≤ F.Cconst := (Cconst_pos F).le
  have h7 : 0 ≤ L₇ F P := by unfold L₇; positivity
  have h8 : 0 ≤ L₈ P := by unfold L₈; exact mul_nonneg (mul_nonneg hd hcc) (Real.sqrt_nonneg _)
  have h10 : 0 ≤ L₁₀ P := by unfold L₁₀; positivity
  have h11 : 0 ≤ L₁₁ P := by unfold L₁₁; exact mul_nonneg hd (Real.exp_pos _).le
  have h12 : 0 ≤ L₁₂ F P := by
    unfold L₁₂ sensInzone
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCq) hcc) (Real.sqrt_nonneg _)
  linarith

/-- **THE LAST INPUT OF THEOREM 1** (`hfrob` of `theorem_one_generic_cert`), under the family-ends
separation `hsep` (Lemma 8.1′, threaded exactly as in `frobenius_sieve_eventually`):
along the design of record for `Family.qle`, eventually in `Q`, at every design point,
`‖Ĝ_fam‖²_F ≤ (κ_cert + rowR2)·𝒩`, `κ_cert = 2 − 0.7212`. -/
theorem hfrob_qle_of_sep (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P Family.qle Qn
        ≤ (Family.qle.kappaCert + rowR2 Family.qle P) * NfamQ P Family.qle Qn := by
  have hε' : (0 : ℝ) < 25 / 1000000 := by norm_num
  filter_upwards [frobenius_inzone_eventually Family.qle r ε hr hε _ hε',
    zone_compare_eventually_of_data Family.qle r ε hr hε (ZoneData.zoneLipschitzData_qle r ε),
    one_sub_zoneFactor_le_eventually Family.qle r ε hr hε 1 one_pos,
    design_regime Family.qle r ε hr hε 200000 (by norm_num),
    design_basic Family.qle r ε hr hε] with Qn hfr hzone hzf hreg hbas
  intro P hdes hsep
  have hP := hdes.1
  obtain ⟨hlogK, -, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam1, hw8, hQn2⟩ := hbas P hdes
  obtain ⟨ha0, h1a0, h1a1⟩ := hzf P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : Real.log Qn ≤ P.LL := LL_ge_log_of_design hdes hQn1
  have hLLK : (200000 : ℝ) ≤ P.LL := le_trans hlogK hLL
  have hw1 : P.w = 1 := w_eq_one_of_design hdes hr (by linarith)
  have hprof : P.prof = designProfileQle := hdes.2.2.2.2.2.2.2.2.2.2.2
  have hlam : P.lam = lamStar := hdes.2.2.2.1
  have hadmD := vDesign_admissible hP
  have ha1 : zoneFactor P ≤ 1 := by linarith
  -- the pieces
  have h1 := hfr P hdes hsep
  have h2 := B_eq_zoneSplit hadmD Family.qle.Cconst ha0 ha1
  have h3 := profileRampLink_design_L₃ Family.qle r ε Qn P hdes hr (by linarith)
  have h4 : B Family.qle.Cconst (vProfile P) ≤ 2 - 7212 / 10000 - 5 / 100000 := by
    show B Cfam (vProfile P) ≤ _
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
  -- the family-aware zone row, at `Family.qle`, is `sZone·(1 − a)` (`rfl`)
  have hzrdef : zoneRowLinear Family.qle P = sZone * (1 - zoneFactor P) := rfl
  have hzr0 : 0 ≤ zoneRowLinear Family.qle P := by rw [hzrdef]; exact mul_nonneg hsZ0 h1a0
  have hzr : zoneRowLinear Family.qle P ≤ sZone := by
    rw [hzrdef]; nlinarith
  have hC1 : 0 ≤ Family.qle.Cconst - 1 := by linarith [one_le_Cconst Family.qle]
  have hJ : (Family.qle.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
      ≤ zoneRowLinear Family.qle P + 25 / 1000000 := by
    have hA : (c ^ 2 - 1) * zoneRowLinear Family.qle P ≤ 8 * (P.w / P.LL) * sZone := by
      calc (c ^ 2 - 1) * zoneRowLinear Family.qle P
          ≤ 8 * (P.w / P.LL) * zoneRowLinear Family.qle P :=
            mul_le_mul_of_nonneg_right hcsq hzr0
        _ ≤ 8 * (P.w / P.LL) * sZone := mul_le_mul_of_nonneg_left hzr (by positivity)
    have hB : 8 * (P.w / P.LL) * sZone ≤ 25 / 1000000 := by
      calc 8 * (P.w / P.LL) * sZone ≤ 8 * (1 / 200000) * (51 / 100) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hwLL (by norm_num)) hsZ1 hsZ0 (by norm_num)
        _ ≤ 25 / 1000000 := by norm_num
    calc (Family.qle.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
        ≤ (Family.qle.Cconst - 1) * (c ^ 2 * Jzone (zoneFactor P) (vProfile P)) :=
          mul_le_mul_of_nonneg_left h5 hC1
      _ = c ^ 2 * ((Family.qle.Cconst - 1) * Jzone (zoneFactor P) (vProfile P)) := by ring
      _ ≤ c ^ 2 * zoneRowLinear Family.qle P := mul_le_mul_of_nonneg_left h6 (sq_nonneg c)
      _ = zoneRowLinear Family.qle P + (c ^ 2 - 1) * zoneRowLinear Family.qle P := by ring
      _ ≤ zoneRowLinear Family.qle P + 25 / 1000000 := by linarith
  have hrows := minor_rows_nonneg Family.qle P
  have hN0 : 0 ≤ NfamQ P Family.qle Qn := NfamQ_nonneg P Family.qle Qn
  have hκ : Family.qle.kappaCert = 2 - 7212 / 10000 := kappaCert_qle
  have hrow : rowR2 Family.qle P
      = zoneRowLinear Family.qle P + L₃ P
        + (L₇ Family.qle P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ Family.qle P) := by
    unfold rowR2; ring
  have hcoef : psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
        + Family.qle.Cconst * K1a (zoneFactor P) (vDesign P) + 25 / 1000000
      ≤ Family.qle.kappaCert + rowR2 Family.qle P := by
    rw [hκ, hrow]
    linarith [h2, h3, h4, hJ, hrows]
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcoef hN0)

/-! ## §5. Theorem 1 at `P_cert = 0.7212` with `hsep` in place of `hfrob` -/

/-- **Theorem 1, r-generic, at `P_cert = 0.7212`, with the Frobenius row DISCHARGED**: the named
inputs are now `hsharp` (the paper's `SharpZeroDensity`), `hsep` (Lemma 8.1′ along the design —
discharged by `hsep_of_design` below) and the regime `r + ε ≤ 7`. -/
theorem theorem_one_generic_cert_of_sep (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hre : r + ε ≤ 7)
    (hsharp : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      SharpZeroDensity Family.qle Qn P)
    (hsep : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      ∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) :=
  JoinCert.theorem_one_generic_cert r ε hr hε hre hsharp (by
    filter_upwards [hfrob_qle_of_sep r ε hr hε, hsep] with Qn h1 h2
    intro P hdes
    exact h1 P hdes (h2 P hdes))

/-! ## §6. `hsep` is DISCHARGED along the design: `Ends.Bfam_le_sep` — whose unused
`hΓ`/`hcoeff` hypotheses (the former quantified over ALL `q : ℕ` and false at `q = 0`) are gone —
plus the tree's `largeSieve_holds`, `P.Q = Qn`, `X ≤ Q^{3/2}`, `Q ≥ 10⁹`. `coeffUnimodular_all` is
kept as the record that the coefficient hypothesis held for every `q` anyway. -/

theorem coeffUnimodular_all (q : ℕ) (χ : DirichletCharacter ℂ q) :
    Zeta23.ThmE.CoeffUnimodular q (fun n => χ (n : ZMod q)) where
  norm_le := fun n => χ.norm_le_one _
  vanish := fun n hn => by
    have : ¬ IsUnit ((n : ZMod q)) := by rwa [ZMod.isUnit_iff_coprime]
    exact χ.map_nonunit this
  norm_eq := fun n _ hn => by
    have hu : IsUnit ((n : ZMod q)) := by rwa [ZMod.isUnit_iff_coprime]
    simpa using χ.unit_norm_eq_one hu.unit

/-- **`hsep` along the design of record, from the tree**: `Ends.Bfam_le_sep` at `δ = 1/2`,
`X = P.XQ`, fed by `largeSieve_holds` (Lemma 6.1), `P.Q = Qn` (`Q_of_design`), `X ≤ Q^{3/2}`
(`design_regime`) and `Q ≥ 10⁹` (eventually). No hypothesis is named. -/
theorem hsep_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      ∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ := by
  filter_upwards [design_regime Family.qle r ε hr hε 1 le_rfl,
    eventually_ge_atTop 1000000000] with Qn hreg hQn
  intro P hdes τ
  have hP := hdes.1
  have hQ := Q_of_design hdes
  obtain ⟨-, -, -, -, -, hX, -, -⟩ := hreg P hdes
  have h := Bfam_le_sep P Qn P.XQ (1 / 2) hP largeSieve_holds (by rw [hQ]) le_rfl
    (one_le_XQ_of_valid hP) hX (by rw [hQ]; exact_mod_cast hQn) τ
  rw [scale_mul_envSep]
  exact h

/-- **`hsep` along the design of record for the DYADIC family**: the same tree inputs as
`hsep_of_design` (`Ends.Bfam_le_sep` at `δ = 1/2`, `largeSieve_holds`, `Q_of_design`,
`design_regime`, `Q ≥ 10⁹`) — none of them is family-specific. No hypothesis is named. -/
theorem hsep_of_design_dyadic (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      ∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ := by
  filter_upwards [design_regime Family.dyadic r ε hr hε 1 le_rfl,
    eventually_ge_atTop 1000000000] with Qn hreg hQn
  intro P hdes τ
  have hP := hdes.1
  have hQ := Q_of_design hdes
  obtain ⟨-, -, -, -, -, hX, -, -⟩ := hreg P hdes
  have h := Bfam_le_sep P Qn P.XQ (1 / 2) hP largeSieve_holds (by rw [hQ]) le_rfl
    (one_le_XQ_of_valid hP) hX (by rw [hQ]; exact_mod_cast hQn) τ
  rw [scale_mul_envSep]
  exact h


/-! ## §7. The dyadic family: the Frobenius row at `κ_cert + rowR2 Family.dyadic`, EXACT.
`ZoneData.dyadic_margin_fails`: the zone comparison against `sZone = 0.5073` is FALSE for the dyadic
profile (`2(C_dyad − 1)ψ(1) = 0.5456 > 0.5073`) — which is why the frozen zone row (`sZone` for both
families) could not carry the dyadic Frobenius clause, and why F63 made `zoneRowLinear F P =
F.sZoneF·(1 − a)` family-aware with `Family.dyadic.sZoneF = sZoneDyadic = 0.5485`. Against
`sZoneDyadic` the comparison holds with margin `0.0028` (`ZoneData.zoneLipschitzData_dyadic`), so the
route of §4 goes through verbatim: `‖Ĝ_fam‖²_F ≤ (κ_cert + rowR2 Family.dyadic)·𝒩`,
`κ_cert = 2 − 0.7098`. (Before F63 this section proved the same bound with the explicit excess
`(sZoneDyadic − sZone)·(1 − zoneFactor P)` outside `rowR2`.) The dyadic certificate slack is
`2 − 0.7098 − (B0 + C̄·B1) = 4.09·10⁻⁵ ≥ 4·10⁻⁵`, split `2·10⁻⁵` (in-zone assembly) + `2·10⁻⁵`
(the `(c²−1)·zone` cross term, once `ℒ ≥ 2.5·10⁵`). -/

/-- the exact core mass of the dyadic design profile. -/
def Mdyad : ℝ :=
  (8824874672578143209723885819185827358332316691131835546248134156374990903156856187872192984552816209139779168219934392948691451964038597 : ℝ)
    / 9225216000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem profMass_val_dyad (hprof : P.prof = designProfileDyadic) (hlam : P.lam = lamStarDyadic) :
    profMass P = Mdyad := by
  rw [ZoneData.profMass_eq_dyadic hprof hlam]; unfold sqPrim lamStarDyadic Mdyad; norm_num

theorem block0_eq_dyad (u : ℝ) :
    evalPoly (certDyadSmooth.coeff.getD 0 []) u = ZoneData.pD u ^ 2 / Mdyad := by
  unfold Mdyad
  norm_num [certDyadSmooth, evalPoly, ZoneData.pD]
  ring

theorem block1_eq_dyad (u : ℝ) :
    evalPoly (certDyadSmooth.coeff.getD 1 []) (u - 806841879 / 2000000000)
      = ZoneData.pD u ^ 2 / Mdyad := by
  unfold Mdyad
  norm_num [certDyadSmooth, evalPoly, ZoneData.pD]
  ring

theorem cert_slack_dyad :
    (B0_certDyadSmooth : ℚ) + (2 * 3141593 ^ 4 / (27 * 10 ^ 24)) * B1_certDyadSmooth
      ≤ 2 - 7098 / 10000 - 4 / 100000 := by
  norm_num [B0_certDyadSmooth, B1_certDyadSmooth]

theorem toFunNonneg_unfold_dyad (u : ℝ) :
    certDyadSmooth.toFunNonneg u
      = Set.indicator (Set.Ico (0 : ℝ) (806841879 / 2000000000))
          (fun t => evalPoly (certDyadSmooth.coeff.getD 0 []) (t - 0)) u
        + Set.indicator (Set.Ico (806841879 / 2000000000 : ℝ) (1193158121 / 2000000000))
          (fun t => evalPoly (certDyadSmooth.coeff.getD 1 []) (t - 806841879 / 2000000000)) u := by
  have hlen : certDyadSmooth.xs.length = 1 := rfl
  have hn0 : ((certDyadSmooth.node 0 : ℚ) : ℝ) = 0 := by
    simp [Cert.node, Cert.nodes, certDyadSmooth]
  have hn1 : ((certDyadSmooth.node 1 : ℚ) : ℝ) = 806841879 / 2000000000 := by
    simp [Cert.node, Cert.nodes, certDyadSmooth]
  have hn2 : ((certDyadSmooth.node 2 : ℚ) : ℝ) = 1193158121 / 2000000000 := by
    simp [Cert.node, Cert.nodes, certDyadSmooth]
  simp only [Cert.toFunNonneg, hlen, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hn0, hn1, hn2]

theorem pD_abs (t : ℝ) : ZoneData.pD |t| = ZoneData.pD t := by
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> unfold ZoneData.pD <;> ring

theorem toFun_eq_vProfile_dyad (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) (t : ℝ) (ht : |t| ≠ lamStarDyadic / 2) :
    certDyadSmooth.toFun t = vProfile P t := by
  have hb : lamStarDyadic / 2 = 1193158121 / 2000000000 := by unfold lamStarDyadic; norm_num
  have htf : certDyadSmooth.toFun t = certDyadSmooth.toFunNonneg |t| := rfl
  have hpM : (P.prof.eval t) ^ 2 / profMass P = ZoneData.pD t ^ 2 / Mdyad := by
    rw [hprof, ZoneData.eval_designProfileDyadic, profMass_val_dyad hprof hlam]
  have hu0 : 0 ≤ |t| := abs_nonneg t
  rw [htf, toFunNonneg_unfold_dyad, vProfile_eq, hlam, hb]
  rw [hb] at ht
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · rw [if_pos hlt.le, hpM]
    by_cases h2 : |t| < 806841879 / 2000000000
    · rw [indicator_of_mem (Set.mem_Ico.mpr ⟨hu0, h2⟩),
        indicator_of_notMem (fun h => absurd h.1 (not_le.mpr h2)), sub_zero, block0_eq_dyad, pD_abs]
      ring
    · rw [indicator_of_notMem (fun h => h2 h.2),
        indicator_of_mem (Set.mem_Ico.mpr ⟨not_lt.mp h2, hlt⟩), block1_eq_dyad, pD_abs]
      ring
  · rw [if_neg (not_le.mpr hgt)]
    have h3 : ¬ |t| < 806841879 / 2000000000 := by
      intro h; linarith
    rw [indicator_of_notMem (fun h => h3 h.2),
      indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hgt.le))]
    ring

theorem vProfile_ae_eq_dyad (hprof : P.prof = designProfileDyadic) (hlam : P.lam = lamStarDyadic) :
    vProfile P =ᵐ[volume] certDyadSmooth.toFun := by
  rw [Filter.EventuallyEq, ae_iff]
  have hS : {t : ℝ | ¬ vProfile P t = certDyadSmooth.toFun t}
      ⊆ {lamStarDyadic / 2, -(lamStarDyadic / 2)} := by
    intro t ht
    simp only [mem_setOf_eq] at ht
    by_contra hmem
    apply ht
    rw [toFun_eq_vProfile_dyad hprof hlam t]
    intro habs
    apply hmem
    rcases abs_eq (by unfold lamStarDyadic; norm_num : (0 : ℝ) ≤ lamStarDyadic / 2) |>.mp habs
      with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hS (((Set.finite_singleton _).insert _).measure_zero volume)

theorem psi_vProfile_eq_cert_dyad (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) : psi (vProfile P) = psi certDyadSmooth.toFun := by
  funext α
  unfold psi
  apply integral_congr_ae
  have h1 := vProfile_ae_eq_dyad hprof hlam
  have h2 : (vProfile P ∘ fun t => t - α) =ᵐ[volume] (certDyadSmooth.toFun ∘ fun t => t - α) :=
    (measurePreserving_sub_right volume α).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with t ht1 ht2
  simp only [Function.comp] at ht2
  rw [ht1, ht2]

theorem B_cert_le_dyad : B CfamDyadic certDyadSmooth.toFun ≤ 2 - 7098 / 10000 - 4 / 100000 := by
  have hadm := certDyadSmooth.admissible certDyadSmooth_NonnegOK certDyadSmooth_MassOK
  have hB1 : 0 ≤ B1 certDyadSmooth.toFun := B1_nonneg hadm
  have hC : CfamDyadic ≤ ((2 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) := by
    unfold CfamDyadic; exact C_dyad_le
  calc B CfamDyadic certDyadSmooth.toFun
      = B0 certDyadSmooth.toFun + CfamDyadic * B1 certDyadSmooth.toFun :=
        B_eq_B0_add_C_mul_B1 _ hadm
    _ ≤ B0 certDyadSmooth.toFun
        + ((2 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) * B1 certDyadSmooth.toFun := by
        nlinarith [mul_le_mul_of_nonneg_right hC hB1]
    _ = ((B0_certDyadSmooth + (2 * 3141593 ^ 4 / (27 * 10 ^ 24)) * B1_certDyadSmooth : ℚ) : ℝ) := by
        rw [B0B1_certDyadSmooth.1, B0B1_certDyadSmooth.2]; push_cast; ring
    _ ≤ ((2 - 7098 / 10000 - 4 / 100000 : ℚ) : ℝ) := by exact_mod_cast cert_slack_dyad
    _ = 2 - 7098 / 10000 - 4 / 100000 := by push_cast; ring

/-- `B_{2π⁴/27}(v_profile) ≤ 2 − 0.7098 − 4·10⁻⁵` at the dyadic design. -/
theorem B_vProfile_le_dyad (hprof : P.prof = designProfileDyadic) (hlam : P.lam = lamStarDyadic) :
    B CfamDyadic (vProfile P) ≤ 2 - 7098 / 10000 - 4 / 100000 := by
  have h := B_cert_le_dyad
  unfold B at h ⊢
  rwa [psi_vProfile_eq_cert_dyad hprof hlam]

/-- The zone comparison for the dyadic family at ITS secant: `zone_compare_eventually_of_data`
fed by `ZoneData.zoneLipschitzData_dyadic` (margin `0.0028` against `sZoneDyadic`); the right side is
the dyadic zone row `zoneRowLinear Family.dyadic P = sZoneDyadic·(1 − zoneFactor P)`. -/
theorem zone_compare_dyadic_eventually (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      (Family.dyadic.Cconst - 1) * Jzone (zoneFactor P) (vProfile P)
        ≤ zoneRowLinear Family.dyadic P :=
  zone_compare_eventually_of_data Family.dyadic r ε hr hε (ZoneData.zoneLipschitzData_dyadic r ε)

/-- **The dyadic Frobenius row, EXACT**: along the design of record for `Family.dyadic`,
eventually in `Q`, at every design point, `‖Ĝ_fam‖²_F ≤ (κ_cert + rowR2 Family.dyadic)·𝒩`,
`κ_cert = 2 − 0.7098`, under `hsep` (discharged by `hsep_of_design_dyadic`). The route is §4's
with `sZone ↦ sZoneDyadic`, `200000 ↦ 250000`, `2.5·10⁻⁵ ↦ 2·10⁻⁵`. -/
theorem hfrob_dyadic_of_sep (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P Family.dyadic Qn
        ≤ (Family.dyadic.kappaCert + rowR2 Family.dyadic P) * NfamQ P Family.dyadic Qn := by
  have hε' : (0 : ℝ) < 2 / 100000 := by norm_num
  filter_upwards [frobenius_inzone_eventually Family.dyadic r ε hr hε _ hε',
    zone_compare_dyadic_eventually r ε hr hε,
    one_sub_zoneFactor_le_eventually Family.dyadic r ε hr hε 1 one_pos,
    design_regime Family.dyadic r ε hr hε 250000 (by norm_num),
    design_basic Family.dyadic r ε hr hε] with Qn hfr hzone hzf hreg hbas
  intro P hdes hsep
  have hP := hdes.1
  obtain ⟨hlogK, -, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam1, hw8, hQn2⟩ := hbas P hdes
  obtain ⟨ha0, h1a0, h1a1⟩ := hzf P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : Real.log Qn ≤ P.LL := LL_ge_log_of_design hdes hQn1
  have hLLK : (250000 : ℝ) ≤ P.LL := le_trans hlogK hLL
  have hw1 : P.w = 1 := w_eq_one_of_design hdes hr (by linarith)
  have hprof : P.prof = designProfileDyadic := hdes.2.2.2.2.2.2.2.2.2.2.2
  have hlam : P.lam = lamStarDyadic := hdes.2.2.2.1
  have hadmD := vDesign_admissible hP
  have ha1 : zoneFactor P ≤ 1 := by linarith
  have h1 := hfr P hdes hsep
  have h2 := B_eq_zoneSplit hadmD Family.dyadic.Cconst ha0 ha1
  have h3 := profileRampLink_design_L₃ Family.dyadic r ε Qn P hdes hr (by linarith)
  have h4 : B Family.dyadic.Cconst (vProfile P) ≤ 2 - 7098 / 10000 - 4 / 100000 := by
    show B CfamDyadic (vProfile P) ≤ _
    exact B_vProfile_le_dyad hprof hlam
  have h5 := Jzone_vDesign_le hP (zoneFactor P)
  have h6 : (Family.dyadic.Cconst - 1) * Jzone (zoneFactor P) (vProfile P)
      ≤ zoneRowLinear Family.dyadic P := hzone P hdes
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
  -- the family-aware zone row, at `Family.dyadic`, is `sZoneDyadic·(1 − a)` (`rfl`)
  have hzrdef : zoneRowLinear Family.dyadic P = sZoneDyadic * (1 - zoneFactor P) := rfl
  have hzD0 : 0 ≤ zoneRowLinear Family.dyadic P := by rw [hzrdef]; exact mul_nonneg hsD0 h1a0
  have hzD : zoneRowLinear Family.dyadic P ≤ sZoneDyadic := by rw [hzrdef]; nlinarith
  have hC1 : 0 ≤ Family.dyadic.Cconst - 1 := by linarith [one_le_Cconst Family.dyadic]
  have hJ : (Family.dyadic.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
      ≤ zoneRowLinear Family.dyadic P + 2 / 100000 := by
    have hA : (c ^ 2 - 1) * zoneRowLinear Family.dyadic P
        ≤ 8 * (P.w / P.LL) * sZoneDyadic := by
      calc (c ^ 2 - 1) * zoneRowLinear Family.dyadic P
          ≤ 8 * (P.w / P.LL) * zoneRowLinear Family.dyadic P :=
            mul_le_mul_of_nonneg_right hcsq hzD0
        _ ≤ 8 * (P.w / P.LL) * sZoneDyadic := mul_le_mul_of_nonneg_left hzD (by positivity)
    have hB : 8 * (P.w / P.LL) * sZoneDyadic ≤ 2 / 100000 := by
      calc 8 * (P.w / P.LL) * sZoneDyadic ≤ 8 * (1 / 250000) * (55 / 100) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hwLL (by norm_num)) hsD1 hsD0 (by norm_num)
        _ ≤ 2 / 100000 := by norm_num
    calc (Family.dyadic.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
        ≤ (Family.dyadic.Cconst - 1) * (c ^ 2 * Jzone (zoneFactor P) (vProfile P)) :=
          mul_le_mul_of_nonneg_left h5 hC1
      _ = c ^ 2 * ((Family.dyadic.Cconst - 1) * Jzone (zoneFactor P) (vProfile P)) := by ring
      _ ≤ c ^ 2 * zoneRowLinear Family.dyadic P := mul_le_mul_of_nonneg_left h6 (sq_nonneg c)
      _ = zoneRowLinear Family.dyadic P + (c ^ 2 - 1) * zoneRowLinear Family.dyadic P := by
          ring
      _ ≤ zoneRowLinear Family.dyadic P + 2 / 100000 := by linarith
  have hrows := minor_rows_nonneg Family.dyadic P
  have hN0 : 0 ≤ NfamQ P Family.dyadic Qn := NfamQ_nonneg P Family.dyadic Qn
  have hκ : Family.dyadic.kappaCert = 2 - 7098 / 10000 := kappaCert_dyadic
  have hrow : rowR2 Family.dyadic P
      = zoneRowLinear Family.dyadic P + L₃ P
        + (L₇ Family.dyadic P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ Family.dyadic P) := by
    unfold rowR2; ring
  have hcoef : psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
        + Family.dyadic.Cconst * K1a (zoneFactor P) (vDesign P) + 2 / 100000
      ≤ Family.dyadic.kappaCert + rowR2 Family.dyadic P := by
    rw [hκ, hrow]
    linarith [h2, h3, h4, hJ, hrows]
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcoef hN0)

/-! ## §8. Theorem 1 with ONLY `hsharp` named -/

/-- **Theorem 1 at `P_cert = 0.7212`** under `hsharp` (the paper's `SharpZeroDensity`) and the F52
regime `r + ε ≤ 7` — nothing else is named: `hsep` is `hsep_of_design`, `hfrob` is
`hfrob_qle_of_sep`, `hrvm` is `famRvMLower_of_design`. (Its predecessor
`theorem_one_generic_cert_of_gammaZero` carried the vacuous `GammaFactsChi (parity χ) 0` that
`Ends.Bfam_le_sep`'s former `hΓ` quantified over; that hypothesis is gone from the tree.) -/
theorem theorem_one_generic_cert_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hre : r + ε ≤ 7)
    (hsharp : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      SharpZeroDensity Family.qle Qn P) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) :=
  theorem_one_generic_cert_of_sep r ε hr hε hre hsharp (hsep_of_design r ε hr hε)


/-! ## §9. Corollary 3's even/odd DYADIC family: the Frobenius row at `κ_cert + rowR2`.

The route of §7 at the refitted parity design (`designProfileEvenDyad12`, `λ' = lamStarEvenDyad12`,
certificate `certEvenDyadSmooth`, `C = 4π⁴/27`), with `sZoneDyadic ↦ sZoneEvenDyadic = 0.6151116`
(`ZoneData.zoneLipschitzData_evenDyadic`, margin `0.0053`), `250000 ↦ 800000` and
`2·10⁻⁵ ↦ 7·10⁻⁶`. The certificate slack is `2 − 0.6919 − (B0 + C̄·B1) = 1.4439·10⁻⁵ ≥
1.4·10⁻⁵`, split `7·10⁻⁶` (in-zone assembly) + `7·10⁻⁶` (the `(c²−1)·zone` cross term, once
`ℒ ≥ 8·10⁵`). Even and odd share every constant, so §9 serves both. -/

/-- the exact core mass `M = ∫_{−λ'/2}^{λ'/2} p²` of the even/odd dyadic REFIT design profile. -/
def MevenDyad : ℝ :=
  (5443708399197993678451653375732603882998180427836132916809654507101416459882587278571971073095542157273665163614724388656022255054785631957377237585100830927899926995435442561389082604862897354508701507453109350427373559302844857197601124348409442336052257289644240591 : ℝ)
    / 5773625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000


theorem profMass_val_evendyad (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) : profMass P = MevenDyad := by
  rw [ZoneData.profMass_eq_evendyad12 hprof hlam]
  unfold sqPrimEvenDyad12 lamStarEvenDyad12 MevenDyad
  norm_num

set_option maxHeartbeats 1000000 in
theorem block0_eq_evendyad (u : ℝ) :
    evalPoly (certEvenDyadSmooth.coeff.getD 0 []) u = ZoneData.pED u ^ 2 / MevenDyad := by
  unfold MevenDyad
  norm_num [certEvenDyadSmooth, evalPoly, ZoneData.pED]
  ring

set_option maxHeartbeats 1000000 in
theorem block1_eq_evendyad (u : ℝ) :
    evalPoly (certEvenDyadSmooth.coeff.getD 1 []) (u - 4522000789 / 10000000000)
      = ZoneData.pED u ^ 2 / MevenDyad := by
  unfold MevenDyad
  norm_num [certEvenDyadSmooth, evalPoly, ZoneData.pED]
  ring

theorem cert_slack_evendyad :
    (B0_certEvenDyadSmooth : ℚ) + (4 * 3141593 ^ 4 / (27 * 10 ^ 24)) * B1_certEvenDyadSmooth
      ≤ 2 - 6919 / 10000 - 14 / 1000000 := by
  norm_num [B0_certEvenDyadSmooth, B1_certEvenDyadSmooth]

theorem toFunNonneg_unfold_evendyad (u : ℝ) :
    certEvenDyadSmooth.toFunNonneg u
      = Set.indicator (Set.Ico (0 : ℝ) (4522000789 / 10000000000))
          (fun t => evalPoly (certEvenDyadSmooth.coeff.getD 0 []) (t - 0)) u
        + Set.indicator (Set.Ico (4522000789 / 10000000000 : ℝ) (5477999211 / 10000000000))
          (fun t => evalPoly (certEvenDyadSmooth.coeff.getD 1 [])
            (t - 4522000789 / 10000000000)) u := by
  have hlen : certEvenDyadSmooth.xs.length = 1 := rfl
  have hn0 : ((certEvenDyadSmooth.node 0 : ℚ) : ℝ) = 0 := by
    simp [Cert.node, Cert.nodes, certEvenDyadSmooth]
  have hn1 : ((certEvenDyadSmooth.node 1 : ℚ) : ℝ) = 4522000789 / 10000000000 := by
    simp [Cert.node, Cert.nodes, certEvenDyadSmooth]
  have hn2 : ((certEvenDyadSmooth.node 2 : ℚ) : ℝ) = 5477999211 / 10000000000 := by
    simp [Cert.node, Cert.nodes, certEvenDyadSmooth]
  simp only [Cert.toFunNonneg, hlen, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hn0, hn1, hn2]

theorem pED_abs (t : ℝ) : ZoneData.pED |t| = ZoneData.pED t := by
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> unfold ZoneData.pED <;> ring

theorem toFun_eq_vProfile_evendyad (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) (t : ℝ) (ht : |t| ≠ lamStarEvenDyad12 / 2) :
    certEvenDyadSmooth.toFun t = vProfile P t := by
  have hb : lamStarEvenDyad12 / 2 = 5477999211 / 10000000000 := by
    unfold lamStarEvenDyad12; norm_num
  have htf : certEvenDyadSmooth.toFun t = certEvenDyadSmooth.toFunNonneg |t| := rfl
  have hpM : (P.prof.eval t) ^ 2 / profMass P = ZoneData.pED t ^ 2 / MevenDyad := by
    rw [hprof, ZoneData.eval_designProfileEvenDyad12, profMass_val_evendyad hprof hlam]
  have hu0 : 0 ≤ |t| := abs_nonneg t
  rw [htf, toFunNonneg_unfold_evendyad, vProfile_eq, hlam, hb]
  rw [hb] at ht
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · rw [if_pos hlt.le, hpM]
    by_cases h2 : |t| < 4522000789 / 10000000000
    · rw [indicator_of_mem (Set.mem_Ico.mpr ⟨hu0, h2⟩),
        indicator_of_notMem (fun h => absurd h.1 (not_le.mpr h2)), sub_zero, block0_eq_evendyad,
        pED_abs]
      ring
    · rw [indicator_of_notMem (fun h => h2 h.2),
        indicator_of_mem (Set.mem_Ico.mpr ⟨not_lt.mp h2, hlt⟩), block1_eq_evendyad, pED_abs]
      ring
  · rw [if_neg (not_le.mpr hgt)]
    have h3 : ¬ |t| < 4522000789 / 10000000000 := by
      intro h; linarith
    rw [indicator_of_notMem (fun h => h3 h.2),
      indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hgt.le))]
    ring

theorem vProfile_ae_eq_evendyad (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) :
    vProfile P =ᵐ[volume] certEvenDyadSmooth.toFun := by
  rw [Filter.EventuallyEq, ae_iff]
  have hS : {t : ℝ | ¬ vProfile P t = certEvenDyadSmooth.toFun t}
      ⊆ {lamStarEvenDyad12 / 2, -(lamStarEvenDyad12 / 2)} := by
    intro t ht
    simp only [mem_setOf_eq] at ht
    by_contra hmem
    apply ht
    rw [toFun_eq_vProfile_evendyad hprof hlam t]
    intro habs
    apply hmem
    rcases abs_eq (by unfold lamStarEvenDyad12; norm_num :
      (0 : ℝ) ≤ lamStarEvenDyad12 / 2) |>.mp habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hS (((Set.finite_singleton _).insert _).measure_zero volume)

theorem psi_vProfile_eq_cert_evendyad (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) : psi (vProfile P) = psi certEvenDyadSmooth.toFun := by
  funext α
  unfold psi
  apply integral_congr_ae
  have h1 := vProfile_ae_eq_evendyad hprof hlam
  have h2 : (vProfile P ∘ fun t => t - α) =ᵐ[volume] (certEvenDyadSmooth.toFun ∘ fun t => t - α) :=
    (measurePreserving_sub_right volume α).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with t ht1 ht2
  simp only [Function.comp] at ht2
  rw [ht1, ht2]

theorem B_cert_le_evendyad :
    B CfamEvenDyadic certEvenDyadSmooth.toFun ≤ 2 - 6919 / 10000 - 14 / 1000000 := by
  have hadm := certEvenDyadSmooth.admissible certEvenDyadSmooth_NonnegOK certEvenDyadSmooth_MassOK
  have hB1 : 0 ≤ B1 certEvenDyadSmooth.toFun := B1_nonneg hadm
  have hC : CfamEvenDyadic ≤ ((4 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) := by
    have h := ZoneData.CfamEvenDyadic_le
    have e : ((4 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ)
        = 4 * 3141593 ^ 4 / (27 * 10 ^ 24) := by push_cast; norm_num
    rw [e]; exact h
  calc B CfamEvenDyadic certEvenDyadSmooth.toFun
      = B0 certEvenDyadSmooth.toFun + CfamEvenDyadic * B1 certEvenDyadSmooth.toFun :=
        B_eq_B0_add_C_mul_B1 _ hadm
    _ ≤ B0 certEvenDyadSmooth.toFun
        + ((4 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) * B1 certEvenDyadSmooth.toFun := by
        nlinarith [mul_le_mul_of_nonneg_right hC hB1]
    _ = ((B0_certEvenDyadSmooth
          + (4 * 3141593 ^ 4 / (27 * 10 ^ 24)) * B1_certEvenDyadSmooth : ℚ) : ℝ) := by
        rw [B0B1_certEvenDyadSmooth.1, B0B1_certEvenDyadSmooth.2]; push_cast; ring
    _ ≤ ((2 - 6919 / 10000 - 14 / 1000000 : ℚ) : ℝ) := by exact_mod_cast cert_slack_evendyad
    _ = 2 - 6919 / 10000 - 14 / 1000000 := by push_cast; ring

/-- `B_{4π⁴/27}(v_profile) ≤ 2 − 0.6919 − 1.4·10⁻⁵` at the even/odd dyadic design. -/
theorem B_vProfile_le_evendyad (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) :
    B CfamEvenDyadic (vProfile P) ≤ 2 - 6919 / 10000 - 14 / 1000000 := by
  have h := B_cert_le_evendyad
  unfold B at h ⊢
  rwa [psi_vProfile_eq_cert_evendyad hprof hlam]

/-- `hsep` along the design of record for the even/odd DYADIC families: the same tree inputs as
`hsep_of_design` — none of them is family-specific. -/
theorem hsep_of_design_parity (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      ∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ := by
  filter_upwards [design_regime F r ε hr hε 1 le_rfl,
    eventually_ge_atTop 1000000000] with Qn hreg hQn
  intro P hdes τ
  have hP := hdes.1
  have hQ := Q_of_design hdes
  obtain ⟨-, -, -, -, -, hX, -, -⟩ := hreg P hdes
  have h := Bfam_le_sep P Qn P.XQ (1 / 2) hP largeSieve_holds (by rw [hQ]) le_rfl
    (one_le_XQ_of_valid hP) hX (by rw [hQ]; exact_mod_cast hQn) τ
  rw [scale_mul_envSep]
  exact h

/-- **The even/odd dyadic Frobenius row**: along the design of record, eventually in `Q`, at
every design point, `‖Ĝ_fam‖²_F ≤ (κ_cert + rowR2 F)·𝒩`, `κ_cert = 2 − 0.6919`, under `hsep`
(discharged by `hsep_of_design_parity`). `F` ranges over the two dyadic parity families through
`hprof`/`hlam`/`hκ`/`hzr`, all of which they share. -/
theorem hfrob_evendyad_of_sep {F : Family} (hC : F.Cconst = CfamEvenDyadic)
    (hs : F.sZoneF = sZoneEvenDyadic) (hκ : F.kappaCert = 2 - 6919 / 10000)
    (hprofF : F.designProfile = designProfileEvenDyad12)
    (hlamF : F.lamStar = lamStarEvenDyad12) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hdata : FrobAssembly.ZoneLipschitzData F r ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P F Qn ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn := by
  have hε' : (0 : ℝ) < 7 / 1000000 := by norm_num
  filter_upwards [frobenius_inzone_eventually F r ε hr hε _ hε',
    zone_compare_eventually_of_data F r ε hr hε hdata,
    one_sub_zoneFactor_le_eventually F r ε hr hε 1 one_pos,
    design_regime F r ε hr hε 800000 (by norm_num),
    design_basic F r ε hr hε] with Qn hfr hzone hzf hreg hbas
  intro P hdes hsep
  have hP := hdes.1
  obtain ⟨hlogK, -, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam1, hw8, hQn2⟩ := hbas P hdes
  obtain ⟨ha0, h1a0, h1a1⟩ := hzf P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : Real.log Qn ≤ P.LL := LL_ge_log_of_design hdes hQn1
  have hLLK : (800000 : ℝ) ≤ P.LL := le_trans hlogK hLL
  have hw1 : P.w = 1 := w_eq_one_of_design hdes hr (by linarith)
  have hprof : P.prof = designProfileEvenDyad12 := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.2, hprofF]
  have hlam : P.lam = lamStarEvenDyad12 := by rw [hdes.2.2.2.1, hlamF]
  have hadmD := vDesign_admissible hP
  have ha1 : zoneFactor P ≤ 1 := by linarith
  have h1 := hfr P hdes hsep
  have h2 := B_eq_zoneSplit hadmD F.Cconst ha0 ha1
  have h3 := profileRampLink_design_L₃ F r ε Qn P hdes hr (by linarith)
  have h4 : B F.Cconst (vProfile P) ≤ 2 - 6919 / 10000 - 14 / 1000000 := by
    rw [hC]; exact B_vProfile_le_evendyad hprof hlam
  have h5 := Jzone_vDesign_le hP (zoneFactor P)
  have h6 : (F.Cconst - 1) * Jzone (zoneFactor P) (vProfile P) ≤ zoneRowLinear F P := hzone P hdes
  set c : ℝ := profMass P / (P.lam * P.aQ) with hc
  have hc1 : 1 ≤ c := one_le_c hP
  have hcle : c ≤ 1 + 8 / 3 * (P.w / P.LL) := c_le hP hlam1
  have hwLL : P.w / P.LL ≤ 1 / 800000 := by
    rw [hw1]; exact one_div_le_one_div_of_le (by norm_num) hLLK
  have hwLL0 : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hc2 : c ≤ 2 := by linarith
  have hcsq : c ^ 2 - 1 ≤ 8 * (P.w / P.LL) := by nlinarith
  have hsD0 : (0 : ℝ) ≤ sZoneEvenDyadic := by unfold sZoneEvenDyadic; norm_num
  have hsD1 : sZoneEvenDyadic ≤ 62 / 100 := by unfold sZoneEvenDyadic; norm_num
  have hzrdef : zoneRowLinear F P = sZoneEvenDyadic * (1 - zoneFactor P) := by
    unfold zoneRowLinear; rw [hs]
  have hzD0 : 0 ≤ zoneRowLinear F P := by rw [hzrdef]; exact mul_nonneg hsD0 h1a0
  have hzD : zoneRowLinear F P ≤ sZoneEvenDyadic := by rw [hzrdef]; nlinarith
  have hC1 : 0 ≤ F.Cconst - 1 := by linarith [one_le_Cconst F]
  have hJ : (F.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
      ≤ zoneRowLinear F P + 7 / 1000000 := by
    have hA : (c ^ 2 - 1) * zoneRowLinear F P ≤ 8 * (P.w / P.LL) * sZoneEvenDyadic := by
      calc (c ^ 2 - 1) * zoneRowLinear F P
          ≤ 8 * (P.w / P.LL) * zoneRowLinear F P := mul_le_mul_of_nonneg_right hcsq hzD0
        _ ≤ 8 * (P.w / P.LL) * sZoneEvenDyadic := mul_le_mul_of_nonneg_left hzD (by positivity)
    have hB : 8 * (P.w / P.LL) * sZoneEvenDyadic ≤ 7 / 1000000 := by
      calc 8 * (P.w / P.LL) * sZoneEvenDyadic ≤ 8 * (1 / 800000) * (62 / 100) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hwLL (by norm_num)) hsD1 hsD0 (by norm_num)
        _ ≤ 7 / 1000000 := by norm_num
    calc (F.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
        ≤ (F.Cconst - 1) * (c ^ 2 * Jzone (zoneFactor P) (vProfile P)) :=
          mul_le_mul_of_nonneg_left h5 hC1
      _ = c ^ 2 * ((F.Cconst - 1) * Jzone (zoneFactor P) (vProfile P)) := by ring
      _ ≤ c ^ 2 * zoneRowLinear F P := mul_le_mul_of_nonneg_left h6 (sq_nonneg c)
      _ = zoneRowLinear F P + (c ^ 2 - 1) * zoneRowLinear F P := by ring
      _ ≤ zoneRowLinear F P + 7 / 1000000 := by linarith
  have hrows := minor_rows_nonneg F P
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hrow : rowR2 F P
      = zoneRowLinear F P + L₃ P + (L₇ F P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ F P) := by
    unfold rowR2; ring
  have hcoef : psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
        + F.Cconst * K1a (zoneFactor P) (vDesign P) + 7 / 1000000
      ≤ F.kappaCert + rowR2 F P := by
    rw [hκ, hrow]
    linarith [h2, h3, h4, hJ, hrows]
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcoef hN0)

/-- `hfrob` for `Family.evenDyadic` along the design, with `hsep` discharged. -/
theorem hfrob_evenDyadic_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.evenDyadic r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.evenDyadic Qn
        ≤ (Family.evenDyadic.kappaCert + rowR2 Family.evenDyadic P)
            * NfamQ P Family.evenDyadic Qn := by
  filter_upwards [hfrob_evendyad_of_sep (F := Family.evenDyadic) rfl rfl kappaCert_evenDyadic
      rfl rfl r ε hr hε (ZoneData.zoneLipschitzData_evenDyadic r ε),
    hsep_of_design_parity Family.evenDyadic r ε hr hε] with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

/-- `hfrob` for `Family.oddDyadic` along the design, with `hsep` discharged. -/
theorem hfrob_oddDyadic_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.oddDyadic r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.oddDyadic Qn
        ≤ (Family.oddDyadic.kappaCert + rowR2 Family.oddDyadic P)
            * NfamQ P Family.oddDyadic Qn := by
  filter_upwards [hfrob_evendyad_of_sep (F := Family.oddDyadic) rfl rfl kappaCert_oddDyadic
      rfl rfl r ε hr hε (ZoneData.zoneLipschitzData_oddDyadic r ε),
    hsep_of_design_parity Family.oddDyadic r ε hr hε] with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)


/-! ## §10. Corollary 3's even/odd `q ≤ Q` family: the Frobenius row at `κ_cert + rowR2`.

§9 at the other refitted parity design (`designProfileEvenQ10`, `λ' = lamStarEvenQ10`, certificate
`certEvenQSmooth`, `C = π⁴/9 ≤ 10.824` by `C_qQ_le`), with `sZoneEvenQ = 0.5921332`
(`ZoneData.zoneLipschitzData_evenQle`, margin `0.0039`), `800000 ↦ 250000` and
`7·10⁻⁶ ↦ 2.3·10⁻⁵`. The certificate slack is `2 − 0.698 − (B0 + C̄·B1) = 4.7075·10⁻⁵ ≥
4.6·10⁻⁵`, split in half. -/

/-- the exact core mass of the even/odd `q ≤ Q` REFIT design profile. -/
def MevenQ : ℝ :=
  (967158555322483623443330080569977021363301150371031388416414717725062159061434586532834364589882348013103300457144409101029142813360954270938877234417715130329823658450846080608675322837414584897285992567384977102632326764494777193721 : ℝ)
    / 1017086214144000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000


theorem profMass_val_evenq (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) : profMass P = MevenQ := by
  rw [ZoneData.profMass_eq_evenq10 hprof hlam]
  unfold sqPrimEvenQ10 lamStarEvenQ10 MevenQ
  norm_num

set_option maxHeartbeats 1000000 in
theorem block0_eq_evenq (u : ℝ) :
    evalPoly (certEvenQSmooth.coeff.getD 0 []) u = ZoneData.pEQ u ^ 2 / MevenQ := by
  unfold MevenQ
  norm_num [certEvenQSmooth, evalPoly, ZoneData.pEQ]
  ring

set_option maxHeartbeats 1000000 in
theorem block1_eq_evenq (u : ℝ) :
    evalPoly (certEvenQSmooth.coeff.getD 1 []) (u - 8710211179 / 20000000000)
      = ZoneData.pEQ u ^ 2 / MevenQ := by
  unfold MevenQ
  norm_num [certEvenQSmooth, evalPoly, ZoneData.pEQ]
  ring

theorem cert_slack_evenq :
    (B0_certEvenQSmooth : ℚ) + (10824 / 1000) * B1_certEvenQSmooth
      ≤ 2 - 349 / 500 - 46 / 1000000 := by
  norm_num [B0_certEvenQSmooth, B1_certEvenQSmooth]

theorem toFunNonneg_unfold_evenq (u : ℝ) :
    certEvenQSmooth.toFunNonneg u
      = Set.indicator (Set.Ico (0 : ℝ) (8710211179 / 20000000000))
          (fun t => evalPoly (certEvenQSmooth.coeff.getD 0 []) (t - 0)) u
        + Set.indicator (Set.Ico (8710211179 / 20000000000 : ℝ) (11289788821 / 20000000000))
          (fun t => evalPoly (certEvenQSmooth.coeff.getD 1 [])
            (t - 8710211179 / 20000000000)) u := by
  have hlen : certEvenQSmooth.xs.length = 1 := rfl
  have hn0 : ((certEvenQSmooth.node 0 : ℚ) : ℝ) = 0 := by
    simp [Cert.node, Cert.nodes, certEvenQSmooth]
  have hn1 : ((certEvenQSmooth.node 1 : ℚ) : ℝ) = 8710211179 / 20000000000 := by
    simp [Cert.node, Cert.nodes, certEvenQSmooth]
  have hn2 : ((certEvenQSmooth.node 2 : ℚ) : ℝ) = 11289788821 / 20000000000 := by
    simp [Cert.node, Cert.nodes, certEvenQSmooth]
  simp only [Cert.toFunNonneg, hlen, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hn0, hn1, hn2]

theorem pEQ_abs (t : ℝ) : ZoneData.pEQ |t| = ZoneData.pEQ t := by
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> unfold ZoneData.pEQ <;> ring

theorem toFun_eq_vProfile_evenq (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) (t : ℝ) (ht : |t| ≠ lamStarEvenQ10 / 2) :
    certEvenQSmooth.toFun t = vProfile P t := by
  have hb : lamStarEvenQ10 / 2 = 11289788821 / 20000000000 := by
    unfold lamStarEvenQ10; norm_num
  have htf : certEvenQSmooth.toFun t = certEvenQSmooth.toFunNonneg |t| := rfl
  have hpM : (P.prof.eval t) ^ 2 / profMass P = ZoneData.pEQ t ^ 2 / MevenQ := by
    rw [hprof, ZoneData.eval_designProfileEvenQ10, profMass_val_evenq hprof hlam]
  have hu0 : 0 ≤ |t| := abs_nonneg t
  rw [htf, toFunNonneg_unfold_evenq, vProfile_eq, hlam, hb]
  rw [hb] at ht
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · rw [if_pos hlt.le, hpM]
    by_cases h2 : |t| < 8710211179 / 20000000000
    · rw [indicator_of_mem (Set.mem_Ico.mpr ⟨hu0, h2⟩),
        indicator_of_notMem (fun h => absurd h.1 (not_le.mpr h2)), sub_zero, block0_eq_evenq,
        pEQ_abs]
      ring
    · rw [indicator_of_notMem (fun h => h2 h.2),
        indicator_of_mem (Set.mem_Ico.mpr ⟨not_lt.mp h2, hlt⟩), block1_eq_evenq, pEQ_abs]
      ring
  · rw [if_neg (not_le.mpr hgt)]
    have h3 : ¬ |t| < 8710211179 / 20000000000 := by
      intro h; linarith
    rw [indicator_of_notMem (fun h => h3 h.2),
      indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hgt.le))]
    ring

theorem vProfile_ae_eq_evenq (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) : vProfile P =ᵐ[volume] certEvenQSmooth.toFun := by
  rw [Filter.EventuallyEq, ae_iff]
  have hS : {t : ℝ | ¬ vProfile P t = certEvenQSmooth.toFun t}
      ⊆ {lamStarEvenQ10 / 2, -(lamStarEvenQ10 / 2)} := by
    intro t ht
    simp only [mem_setOf_eq] at ht
    by_contra hmem
    apply ht
    rw [toFun_eq_vProfile_evenq hprof hlam t]
    intro habs
    apply hmem
    rcases abs_eq (by unfold lamStarEvenQ10; norm_num :
      (0 : ℝ) ≤ lamStarEvenQ10 / 2) |>.mp habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hS (((Set.finite_singleton _).insert _).measure_zero volume)

theorem psi_vProfile_eq_cert_evenq (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) : psi (vProfile P) = psi certEvenQSmooth.toFun := by
  funext α
  unfold psi
  apply integral_congr_ae
  have h1 := vProfile_ae_eq_evenq hprof hlam
  have h2 : (vProfile P ∘ fun t => t - α) =ᵐ[volume] (certEvenQSmooth.toFun ∘ fun t => t - α) :=
    (measurePreserving_sub_right volume α).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with t ht1 ht2
  simp only [Function.comp] at ht2
  rw [ht1, ht2]

theorem B_cert_le_evenq :
    B CfamEven certEvenQSmooth.toFun ≤ 2 - 349 / 500 - 46 / 1000000 := by
  have hadm := certEvenQSmooth.admissible certEvenQSmooth_NonnegOK certEvenQSmooth_MassOK
  have hB1 : 0 ≤ B1 certEvenQSmooth.toFun := B1_nonneg hadm
  have hC : CfamEven ≤ ((10824 / 1000 : ℚ) : ℝ) := by
    have h := ZoneData.CfamEven_le
    have e : ((10824 / 1000 : ℚ) : ℝ) = 2 * (5412 / 1000) := by push_cast; norm_num
    rw [e]; exact h
  calc B CfamEven certEvenQSmooth.toFun
      = B0 certEvenQSmooth.toFun + CfamEven * B1 certEvenQSmooth.toFun :=
        B_eq_B0_add_C_mul_B1 _ hadm
    _ ≤ B0 certEvenQSmooth.toFun + ((10824 / 1000 : ℚ) : ℝ) * B1 certEvenQSmooth.toFun := by
        nlinarith [mul_le_mul_of_nonneg_right hC hB1]
    _ = ((B0_certEvenQSmooth + (10824 / 1000) * B1_certEvenQSmooth : ℚ) : ℝ) := by
        rw [B0B1_certEvenQSmooth.1, B0B1_certEvenQSmooth.2]; push_cast; ring
    _ ≤ ((2 - 349 / 500 - 46 / 1000000 : ℚ) : ℝ) := by exact_mod_cast cert_slack_evenq
    _ = 2 - 349 / 500 - 46 / 1000000 := by push_cast; ring

/-- `B_{π⁴/9}(v_profile) ≤ 2 − 0.698 − 4.6·10⁻⁵` at the even/odd `q ≤ Q` design. -/
theorem B_vProfile_le_evenq (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) :
    B CfamEven (vProfile P) ≤ 2 - 349 / 500 - 46 / 1000000 := by
  have h := B_cert_le_evenq
  unfold B at h ⊢
  rwa [psi_vProfile_eq_cert_evenq hprof hlam]

/-- **The even/odd `q ≤ Q` Frobenius row**, under `hsep` (discharged by
`hsep_of_design_parity`). -/
theorem hfrob_evenq_of_sep {F : Family} (hC : F.Cconst = CfamEven)
    (hs : F.sZoneF = sZoneEvenQ) (hκ : F.kappaCert = 2 - 698 / 1000)
    (hprofF : F.designProfile = designProfileEvenQ10)
    (hlamF : F.lamStar = lamStarEvenQ10) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hdata : FrobAssembly.ZoneLipschitzData F r ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P F Qn ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn := by
  have hε' : (0 : ℝ) < 23 / 1000000 := by norm_num
  filter_upwards [frobenius_inzone_eventually F r ε hr hε _ hε',
    zone_compare_eventually_of_data F r ε hr hε hdata,
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
  have hprof : P.prof = designProfileEvenQ10 := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.2, hprofF]
  have hlam : P.lam = lamStarEvenQ10 := by rw [hdes.2.2.2.1, hlamF]
  have hadmD := vDesign_admissible hP
  have ha1 : zoneFactor P ≤ 1 := by linarith
  have h1 := hfr P hdes hsep
  have h2 := B_eq_zoneSplit hadmD F.Cconst ha0 ha1
  have h3 := profileRampLink_design_L₃ F r ε Qn P hdes hr (by linarith)
  have h4 : B F.Cconst (vProfile P) ≤ 2 - 349 / 500 - 46 / 1000000 := by
    rw [hC]; exact B_vProfile_le_evenq hprof hlam
  have h5 := Jzone_vDesign_le hP (zoneFactor P)
  have h6 : (F.Cconst - 1) * Jzone (zoneFactor P) (vProfile P) ≤ zoneRowLinear F P := hzone P hdes
  set c : ℝ := profMass P / (P.lam * P.aQ) with hc
  have hc1 : 1 ≤ c := one_le_c hP
  have hcle : c ≤ 1 + 8 / 3 * (P.w / P.LL) := c_le hP hlam1
  have hwLL : P.w / P.LL ≤ 1 / 250000 := by
    rw [hw1]; exact one_div_le_one_div_of_le (by norm_num) hLLK
  have hwLL0 : 0 ≤ P.w / P.LL := div_nonneg hP.w_pos.le hP.LL_pos.le
  have hc2 : c ≤ 2 := by linarith
  have hcsq : c ^ 2 - 1 ≤ 8 * (P.w / P.LL) := by nlinarith
  have hsD0 : (0 : ℝ) ≤ sZoneEvenQ := by unfold sZoneEvenQ; norm_num
  have hsD1 : sZoneEvenQ ≤ 60 / 100 := by unfold sZoneEvenQ; norm_num
  have hzrdef : zoneRowLinear F P = sZoneEvenQ * (1 - zoneFactor P) := by
    unfold zoneRowLinear; rw [hs]
  have hzD0 : 0 ≤ zoneRowLinear F P := by rw [hzrdef]; exact mul_nonneg hsD0 h1a0
  have hzD : zoneRowLinear F P ≤ sZoneEvenQ := by rw [hzrdef]; nlinarith
  have hC1 : 0 ≤ F.Cconst - 1 := by linarith [one_le_Cconst F]
  have hJ : (F.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
      ≤ zoneRowLinear F P + 23 / 1000000 := by
    have hA : (c ^ 2 - 1) * zoneRowLinear F P ≤ 8 * (P.w / P.LL) * sZoneEvenQ := by
      calc (c ^ 2 - 1) * zoneRowLinear F P
          ≤ 8 * (P.w / P.LL) * zoneRowLinear F P := mul_le_mul_of_nonneg_right hcsq hzD0
        _ ≤ 8 * (P.w / P.LL) * sZoneEvenQ := mul_le_mul_of_nonneg_left hzD (by positivity)
    have hB : 8 * (P.w / P.LL) * sZoneEvenQ ≤ 23 / 1000000 := by
      calc 8 * (P.w / P.LL) * sZoneEvenQ ≤ 8 * (1 / 250000) * (60 / 100) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hwLL (by norm_num)) hsD1 hsD0 (by norm_num)
        _ ≤ 23 / 1000000 := by norm_num
    calc (F.Cconst - 1) * Jzone (zoneFactor P) (vDesign P)
        ≤ (F.Cconst - 1) * (c ^ 2 * Jzone (zoneFactor P) (vProfile P)) :=
          mul_le_mul_of_nonneg_left h5 hC1
      _ = c ^ 2 * ((F.Cconst - 1) * Jzone (zoneFactor P) (vProfile P)) := by ring
      _ ≤ c ^ 2 * zoneRowLinear F P := mul_le_mul_of_nonneg_left h6 (sq_nonneg c)
      _ = zoneRowLinear F P + (c ^ 2 - 1) * zoneRowLinear F P := by ring
      _ ≤ zoneRowLinear F P + 23 / 1000000 := by linarith
  have hrows := minor_rows_nonneg F P
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hrow : rowR2 F P
      = zoneRowLinear F P + L₃ P + (L₇ F P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ F P) := by
    unfold rowR2; ring
  have hcoef : psi (vDesign P) 0 + K0a (zoneFactor P) (vDesign P)
        + F.Cconst * K1a (zoneFactor P) (vDesign P) + 23 / 1000000
      ≤ F.kappaCert + rowR2 F P := by
    rw [hκ, hrow]
    linarith [h2, h3, h4, hJ, hrows]
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcoef hN0)

/-- `hfrob` for `Family.evenQle` along the design, with `hsep` discharged. -/
theorem hfrob_evenQle_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.evenQle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.evenQle Qn
        ≤ (Family.evenQle.kappaCert + rowR2 Family.evenQle P) * NfamQ P Family.evenQle Qn := by
  filter_upwards [hfrob_evenq_of_sep (F := Family.evenQle) rfl rfl kappaCert_evenQle
      rfl rfl r ε hr hε (ZoneData.zoneLipschitzData_evenQle r ε),
    hsep_of_design_parity Family.evenQle r ε hr hε] with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

/-- `hfrob` for `Family.oddQle` along the design, with `hsep` discharged. -/
theorem hfrob_oddQle_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.oddQle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.oddQle Qn
        ≤ (Family.oddQle.kappaCert + rowR2 Family.oddQle P) * NfamQ P Family.oddQle Qn := by
  filter_upwards [hfrob_evenq_of_sep (F := Family.oddQle) rfl rfl kappaCert_oddQle
      rfl rfl r ε hr hε (ZoneData.zoneLipschitzData_oddQle r ε),
    hsep_of_design_parity Family.oddQle r ε hr hε] with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

end HFrob
end ZetaQ

end

-- provenance of `sorryAx`: none since the Gallagher rethread (Lemma 6.1 consumed at `Q² + πN`,
-- `ZetaQ/Gallagher.lean`); before it, the single `sorryAx` came from
-- `ZetaQ.l2_concentration_exists` through `Ends.largeSieve_holds`.
