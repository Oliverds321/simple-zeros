/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Cor3Full.lean — **Corollary 3″: the four parity headlines at the FULL-family constants**
`P_cert = 0.7212` (`q ≤ Q`) and `0.7098` (`Q/2 < q ≤ Q`), with NO named hypothesis beyond
`3 ≤ r`, `0 < ε`.

The reflected large sieve (`ZetaQ/ReflectedSieve.lean`) charges one parity class of primitive
characters `Q²/2 + π(N + ½)`, half of Gallagher's `Q² + πN`, so a parity family's out-zone
constant is `C_F/2` — the FULL family's `C` (`CfamEven/2 = Cfam`, `CfamEvenDyadic/2 = CfamDyadic`)
— and Theorem 1's / Corollary 2's certificates apply to it verbatim (`Cor3Reflected`:
`famPP_le_zone_split_par`, `frobenius_inzone_eventually_par`, and the two conditional rows
`hfrob_par_qle_of_sep` / `hfrob_par_dyad_of_sep`). Those rows need a `Family` value whose
characters are one parity class but whose DESIGN (bandwidth, profile, zone secant, payoff,
`κ_cert`) is the full family's; `Family.evenQleR` / `oddQleR` / `evenDyadicR` / `oddDyadicR`
(`ZetaQ/Certificate.lean`) are exactly that. Their moduli, characters and size are the parity
families', so their zero counts ARE `evenQle`'s / … / `oddDyadic`'s, by `rfl` (§1).

What this file does:
  * §1 the `rfl` bridges `NfamCount Family.evenQleR = NfamCount Family.evenQle` (and `N0sFamCount`,
    all four);
  * §2 the design data: `C_F/2` is the full constant; the zone comparison at `C_F/2` from the FULL
    families' certified `ZoneLipschitzData` (`ZoneData.zoneLipschitzData_qle` / `_dyadic`) —
    a design point of `evenQleR` IS a design point of `qle` (same `λ*`, same profile);
  * §3 the four Frobenius rows along `DesignOfRecord` (the conditional rows of `Cor3Frob` with
    every hypothesis discharged: `hFp`, `hC`, `hs`, `hκ`, `hprofF`, `hlamF` by `rfl`/§2, `hzoneE`
    by §2, Lemma 8.1′ by `HFrob.hsep_of_design_parity`), carried to the margin design by
    `Margin.eventually_M_of_D0free`;
  * §4 the four headlines at the R families (the proofs of `JoinProved.corollary_three_*_proved'`
    with the R family and the §3 row), and **the four headlines about the EXISTING parity
    families' zero counts**, `JoinProved.corollary_three_{even,odd}_{qQ,dyadic}_full_proved'` —
    the same objects as `corollary_three_*_proved'` (0.698 / 0.6919), at 0.7212 / 0.7098.

Axioms: `[propext, Classical.choice, Quot.sound]` (`audit/final_axioms.lean`).
-/
import ZetaQ.Margin
import ZetaQ.Cor3Frob

noncomputable section

open Filter Asymptotics
open ZetaQ.Payoff ZetaQ.Zones ZetaQ.Ends ZetaQ.FamRows ZetaQ.FrobAssembly ZetaQ.HFrob

namespace ZetaQ
namespace Cor3Full

open JoinCert JoinProved Margin

/-! ## 1. The R families count the parity families' zeros, by `rfl` -/

theorem NfamCount_evenQleR (Qn : ℕ) (T₁ T₂ : ℝ) :
    NfamCount Family.evenQleR Qn T₁ T₂ = NfamCount Family.evenQle Qn T₁ T₂ := rfl

theorem N0sFamCount_evenQleR (Qn : ℕ) (T₁ T₂ : ℝ) :
    N0sFamCount Family.evenQleR Qn T₁ T₂ = N0sFamCount Family.evenQle Qn T₁ T₂ := rfl

theorem NfamCount_oddQleR (Qn : ℕ) (T₁ T₂ : ℝ) :
    NfamCount Family.oddQleR Qn T₁ T₂ = NfamCount Family.oddQle Qn T₁ T₂ := rfl

theorem N0sFamCount_oddQleR (Qn : ℕ) (T₁ T₂ : ℝ) :
    N0sFamCount Family.oddQleR Qn T₁ T₂ = N0sFamCount Family.oddQle Qn T₁ T₂ := rfl

theorem NfamCount_evenDyadicR (Qn : ℕ) (T₁ T₂ : ℝ) :
    NfamCount Family.evenDyadicR Qn T₁ T₂ = NfamCount Family.evenDyadic Qn T₁ T₂ := rfl

theorem N0sFamCount_evenDyadicR (Qn : ℕ) (T₁ T₂ : ℝ) :
    N0sFamCount Family.evenDyadicR Qn T₁ T₂ = N0sFamCount Family.evenDyadic Qn T₁ T₂ := rfl

theorem NfamCount_oddDyadicR (Qn : ℕ) (T₁ T₂ : ℝ) :
    NfamCount Family.oddDyadicR Qn T₁ T₂ = NfamCount Family.oddDyadic Qn T₁ T₂ := rfl

theorem N0sFamCount_oddDyadicR (Qn : ℕ) (T₁ T₂ : ℝ) :
    N0sFamCount Family.oddDyadicR Qn T₁ T₂ = N0sFamCount Family.oddDyadic Qn T₁ T₂ := rfl

/-! ## 2. The design data at `C_F/2` -/

theorem Cconst_half_qleR {F : Family} (hF : F.Cconst = CfamEven) : F.Cconst / 2 = Cfam := by
  rw [hF]; unfold CfamEven Cfam; ring

theorem Cconst_half_dyadicR {F : Family} (hF : F.Cconst = CfamEvenDyadic) :
    F.Cconst / 2 = CfamDyadic := by
  rw [hF]; unfold CfamEvenDyadic CfamDyadic; ring

/-- **The zone comparison at `C_F/2 = C_qle`** for a family whose design points are `qle`'s
design points and whose zone secant is `sZone`: `ZoneData.zoneLipschitzData_qle`'s certified
`(ψ₁, c)` through `FrobAssembly.zone_compare_eventually`. -/
theorem zoneE_qleR {F : Family} (hC : F.Cconst / 2 = Cfam) (hs : F.sZoneF = sZone)
    (hdes_eq : ∀ (r ε Q : ℝ) (P : ParamsQ), DesignOfRecord F r ε Q P →
      DesignOfRecord Family.qle r ε Q P)
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (F.Cconst / 2 - 1) * Jzone (zoneFactor P) (vProfile P) ≤ zoneRowLinear F P := by
  obtain ⟨ψ₁, c, hc, hmargin, hlip⟩ := ZoneData.zoneLipschitzData_qle r ε
  have h1 : (1 : ℝ) ≤ Cfam := FrobAssembly.one_le_Cconst Family.qle
  have hm : 2 * (Cfam - 1) * ψ₁ < sZone := hmargin
  filter_upwards [FrobAssembly.zone_compare_eventually F r ε hr hε Cfam sZone ψ₁ c h1 hc hm
    (fun Qn P hdes => hlip Qn P (hdes_eq r ε Qn P hdes))] with Qn h
  intro P hdes
  rw [hC]
  unfold zoneRowLinear
  rw [hs]
  exact h P hdes

/-- The dyadic twin of `zoneE_qleR` (`ZoneData.zoneLipschitzData_dyadic`, secant `sZoneDyadic`). -/
theorem zoneE_dyadicR {F : Family} (hC : F.Cconst / 2 = CfamDyadic) (hs : F.sZoneF = sZoneDyadic)
    (hdes_eq : ∀ (r ε Q : ℝ) (P : ParamsQ), DesignOfRecord F r ε Q P →
      DesignOfRecord Family.dyadic r ε Q P)
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (F.Cconst / 2 - 1) * Jzone (zoneFactor P) (vProfile P) ≤ zoneRowLinear F P := by
  obtain ⟨ψ₁, c, hc, hmargin, hlip⟩ := ZoneData.zoneLipschitzData_dyadic r ε
  have h1 : (1 : ℝ) ≤ CfamDyadic := FrobAssembly.one_le_Cconst Family.dyadic
  have hm : 2 * (CfamDyadic - 1) * ψ₁ < sZoneDyadic := hmargin
  filter_upwards [FrobAssembly.zone_compare_eventually F r ε hr hε CfamDyadic sZoneDyadic ψ₁ c h1
    hc hm
    (fun Qn P hdes => hlip Qn P (hdes_eq r ε Qn P hdes))] with Qn h
  intro P hdes
  rw [hC]
  unfold zoneRowLinear
  rw [hs]
  exact h P hdes

/-! ## 3. The four Frobenius rows at `κ_cert(0.7212)` / `κ_cert(0.7098)` -/

theorem hfrob_evenQleR_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.evenQleR r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.evenQleR Qn
        ≤ (Family.evenQleR.kappaCert + rowR2 Family.evenQleR P) * NfamQ P Family.evenQleR Qn := by
  have hC : Family.evenQleR.Cconst / 2 = Cfam := Cconst_half_qleR rfl
  filter_upwards [Cor3Reflected.hfrob_par_qle_of_sep (F := Family.evenQleR) (p := 0)
      (fun _ => rfl) hC rfl kappaCert_evenQleR rfl rfl r ε hr hε
      (zoneE_qleR hC rfl (fun _ _ _ _ h => h) r ε hr hε),
    hsep_of_design_parity Family.evenQleR r ε hr hε] with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

theorem hfrob_oddQleR_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.oddQleR r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.oddQleR Qn
        ≤ (Family.oddQleR.kappaCert + rowR2 Family.oddQleR P) * NfamQ P Family.oddQleR Qn := by
  have hC : Family.oddQleR.Cconst / 2 = Cfam := Cconst_half_qleR rfl
  filter_upwards [Cor3Reflected.hfrob_par_qle_of_sep (F := Family.oddQleR) (p := 1)
      (fun _ => rfl) hC rfl kappaCert_oddQleR rfl rfl r ε hr hε
      (zoneE_qleR hC rfl (fun _ _ _ _ h => h) r ε hr hε),
    hsep_of_design_parity Family.oddQleR r ε hr hε] with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

theorem hfrob_evenDyadicR_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.evenDyadicR r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.evenDyadicR Qn
        ≤ (Family.evenDyadicR.kappaCert + rowR2 Family.evenDyadicR P)
            * NfamQ P Family.evenDyadicR Qn := by
  have hC : Family.evenDyadicR.Cconst / 2 = CfamDyadic := Cconst_half_dyadicR rfl
  filter_upwards [Cor3Reflected.hfrob_par_dyad_of_sep (F := Family.evenDyadicR) (p := 0)
      (fun _ => rfl) hC rfl kappaCert_evenDyadicR rfl rfl r ε hr hε
      (zoneE_dyadicR hC rfl (fun _ _ _ _ h => h) r ε hr hε),
    hsep_of_design_parity Family.evenDyadicR r ε hr hε] with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

theorem hfrob_oddDyadicR_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.oddDyadicR r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.oddDyadicR Qn
        ≤ (Family.oddDyadicR.kappaCert + rowR2 Family.oddDyadicR P)
            * NfamQ P Family.oddDyadicR Qn := by
  have hC : Family.oddDyadicR.Cconst / 2 = CfamDyadic := Cconst_half_dyadicR rfl
  filter_upwards [Cor3Reflected.hfrob_par_dyad_of_sep (F := Family.oddDyadicR) (p := 1)
      (fun _ => rfl) hC rfl kappaCert_oddDyadicR rfl rfl r ε hr hε
      (zoneE_dyadicR hC rfl (fun _ _ _ _ h => h) r ε hr hε),
    hsep_of_design_parity Family.oddDyadicR r ε hr hε] with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

/-! ### … along the MARGIN design (`Margin.eventually_M_of_D0free`) -/

theorem hfrob_evenQleR_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.evenQleR r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.evenQleR Qn
        ≤ (Family.evenQleR.kappaCert + rowR2 Family.evenQleR P) * NfamQ P Family.evenQleR Qn :=
  eventually_M_of_D0free Family.evenQleR r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.evenQleR Qn
      ≤ (Family.evenQleR.kappaCert + rowR2 Family.evenQleR P) * NfamQ P Family.evenQleR Qn)
    (fun _ _ _ h => h) (hfrob_evenQleR_of_design r ε hr hε)

theorem hfrob_oddQleR_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.oddQleR r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.oddQleR Qn
        ≤ (Family.oddQleR.kappaCert + rowR2 Family.oddQleR P) * NfamQ P Family.oddQleR Qn :=
  eventually_M_of_D0free Family.oddQleR r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.oddQleR Qn
      ≤ (Family.oddQleR.kappaCert + rowR2 Family.oddQleR P) * NfamQ P Family.oddQleR Qn)
    (fun _ _ _ h => h) (hfrob_oddQleR_of_design r ε hr hε)

theorem hfrob_evenDyadicR_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.evenDyadicR r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.evenDyadicR Qn
        ≤ (Family.evenDyadicR.kappaCert + rowR2 Family.evenDyadicR P)
            * NfamQ P Family.evenDyadicR Qn :=
  eventually_M_of_D0free Family.evenDyadicR r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.evenDyadicR Qn
      ≤ (Family.evenDyadicR.kappaCert + rowR2 Family.evenDyadicR P)
          * NfamQ P Family.evenDyadicR Qn)
    (fun _ _ _ h => h) (hfrob_evenDyadicR_of_design r ε hr hε)

theorem hfrob_oddDyadicR_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.oddDyadicR r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.oddDyadicR Qn
        ≤ (Family.oddDyadicR.kappaCert + rowR2 Family.oddDyadicR P)
            * NfamQ P Family.oddDyadicR Qn :=
  eventually_M_of_D0free Family.oddDyadicR r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.oddDyadicR Qn
      ≤ (Family.oddDyadicR.kappaCert + rowR2 Family.oddDyadicR P)
          * NfamQ P Family.oddDyadicR Qn)
    (fun _ _ _ h => h) (hfrob_oddDyadicR_of_design r ε hr hε)

/-! ## 4. The headlines at the R families -/

/-- Corollary 3″ (even, `q ≤ Q`) at the R family: `P_cert = 0.7212`. The proof is
`JoinProved.corollary_three_even_qQ_proved'`'s with `Family.evenQleR` and the §3 row. -/
theorem corollary_three_evenQleR (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.evenQleR Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.evenQleR Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 4 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 4 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.evenQleR r ε
    (DesignOfRecordM Family.evenQleR r ε)
    (exists_designOfRecordM Family.evenQleR r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (4 * A₀) Family.evenQleR)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (4 * A₀) hA₀' Family.evenQleR r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.evenQleR r ε hr hε (4 * A₀) hA₀' hloc'
    (famNIIUpper_parity_qle_of_designM not_isFull_evenQleR rfl (fun _ => rfl) r ε hA₀ hloc)
    (hfrob_evenQleR_of_designM r ε hr hε)
    (famRvMLower_parity_of_designM not_isFull_evenQleR rfl (fun _ => rfl) r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- Corollary 3″ (odd, `q ≤ Q`) at the R family: `P_cert = 0.7212`. -/
theorem corollary_three_oddQleR (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.oddQleR Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.oddQleR Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 4 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 4 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.oddQleR r ε
    (DesignOfRecordM Family.oddQleR r ε)
    (exists_designOfRecordM Family.oddQleR r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (4 * A₀) Family.oddQleR)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (4 * A₀) hA₀' Family.oddQleR r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.oddQleR r ε hr hε (4 * A₀) hA₀' hloc'
    (famNIIUpper_parity_qle_of_designM not_isFull_oddQleR rfl (fun _ => rfl) r ε hA₀ hloc)
    (hfrob_oddQleR_of_designM r ε hr hε)
    (famRvMLower_parity_of_designM not_isFull_oddQleR rfl (fun _ => rfl) r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- Corollary 3″ (even, dyadic) at the R family: `P_cert = 0.7098`. -/
theorem corollary_three_evenDyadicR (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.evenDyadicR Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.evenDyadicR Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 4 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 4 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.evenDyadicR r ε
    (DesignOfRecordM Family.evenDyadicR r ε)
    (exists_designOfRecordM Family.evenDyadicR r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (4 * A₀) Family.evenDyadicR)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (4 * A₀) hA₀' Family.evenDyadicR r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.evenDyadicR r ε hr hε (4 * A₀) hA₀'
    hloc'
    (famNIIUpper_parity_dyadic_of_designM not_isFull_evenDyadicR rfl (fun _ => rfl) r ε hA₀ hloc)
    (hfrob_evenDyadicR_of_designM r ε hr hε)
    (famRvMLower_parity_dyadic_of_designM not_isFull_evenDyadicR rfl (fun _ => rfl) r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- Corollary 3″ (odd, dyadic) at the R family: `P_cert = 0.7098`. -/
theorem corollary_three_oddDyadicR (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.oddDyadicR Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.oddDyadicR Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 4 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 4 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.oddDyadicR r ε
    (DesignOfRecordM Family.oddDyadicR r ε)
    (exists_designOfRecordM Family.oddDyadicR r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (4 * A₀) Family.oddDyadicR)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (4 * A₀) hA₀' Family.oddDyadicR r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.oddDyadicR r ε hr hε (4 * A₀) hA₀'
    hloc'
    (famNIIUpper_parity_dyadic_of_designM not_isFull_oddDyadicR rfl (fun _ => rfl) r ε hA₀ hloc)
    (hfrob_oddDyadicR_of_designM r ε hr hε)
    (famRvMLower_parity_dyadic_of_designM not_isFull_oddDyadicR rfl (fun _ => rfl) r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

end Cor3Full

namespace JoinProved

open Cor3Full

/-! ## 5. **COROLLARY 3″** — the four parity headlines at the FULL-family constants, about the
EXISTING parity families' zero counts (`Family.evenQle`, …): the same objects as
`corollary_three_*_proved'` (which stay, at 0.698 / 0.6919), now at `P_cert = 0.7212` (`q ≤ Q`)
and `0.7098` (dyadic) — Theorem 1's and Corollary 2's constants. NO named hypothesis beyond
`3 ≤ r`, `0 < ε`. Axioms: `[propext, Classical.choice, Quot.sound]`. -/

/-- **Corollary 3″ (even, `q ≤ Q`) at `P_cert = 0.7212`** — Theorem 1's constant, for the even
primitive characters of modulus `2 ≤ q ≤ Q`. -/
theorem corollary_three_even_qQ_full_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.evenQle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.evenQle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  simpa only [NfamCount_evenQleR, N0sFamCount_evenQleR] using corollary_three_evenQleR r ε hr hε

/-- **Corollary 3″ (odd, `q ≤ Q`) at `P_cert = 0.7212`**. -/
theorem corollary_three_odd_qQ_full_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.oddQle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.oddQle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  simpa only [NfamCount_oddQleR, N0sFamCount_oddQleR] using corollary_three_oddQleR r ε hr hε

/-- **Corollary 3″ (even, dyadic) at `P_cert = 0.7098`** — Corollary 2's constant, for the even
primitive characters of modulus `Q/2 < q ≤ Q` (the family of the Sono comparison). -/
theorem corollary_three_even_dyadic_full_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.evenDyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.evenDyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  simpa only [NfamCount_evenDyadicR, N0sFamCount_evenDyadicR] using
    corollary_three_evenDyadicR r ε hr hε

/-- **Corollary 3″ (odd, dyadic) at `P_cert = 0.7098`**. -/
theorem corollary_three_odd_dyadic_full_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.oddDyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.oddDyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  simpa only [NfamCount_oddDyadicR, N0sFamCount_oddDyadicR] using
    corollary_three_oddDyadicR r ε hr hε

end JoinProved
end ZetaQ

end
