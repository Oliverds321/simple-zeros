/-
**Theorem K (the Shell kernel)** (thm:shell-K, sec_shell.tex l.71–90, proof l.897–933), (D1′) instantiation, sharp
family `𝔉_Q`, on the Shell design S53-L75 (`λ = 191/100`), in ZetaQ's objects, L7_10.
Draft: "`∫_out g F ≤ (1 + O(η_Q))|𝔉_Q| ∫_out g ‖a‖² k̃_{α′}(s/ℒ)/|s/ℒ| ds`, `k̃ = k` except on the strip
`Σ_Q = {(1−δ′)log Q ≤ |s| ≤ log Q + 4}`, where `k̃ = C|α|`; `η_Q ≪ (log log Q)^{O(1)}(log Q)^{−θ(α′)}`."
Lean form: `out = (inZone P)ᶜ = {|s| > (1−δ′)log Q}` (ZetaQ's zone edge); the weight `shellWt` (L10_KDefs: strip `C`,
`ℒ/s` on `(log Q+4, α′ℒ]`, `Cℒ/s` beyond; for `s < −s₀` the sieve weight `C`); `C = π⁴/18`; rate `(log Q)^{−θ}` for
every `θ < θ(α′)`. Only classical hypothesis: `ZeroDensityInput` (no `PNTErrorTerm`, no certificate).
THIS FILE: Theorem K DERIVED from K1 (strip and `s < −s₀`, pointwise), K2 (Shell zone, integral), K3 (killed zone,
integral) and KInt, with `sorry`
only in those nodes. (K2 in turn rests on AS, S and KT; that derivation is listed in K2's header, not compiled.)
-/
import ZetaShell.ShellK.L10_K1_Strip
import ZetaShell.ShellK.L10_K2_ShellZone
import ZetaShell.ShellK.L10_K3_Killed
import ZetaShell.ShellK.L10_KInt

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ MeasureTheory ZetaShell.ShellS

theorem thmK (hD : ZeroDensityInput) (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r ε θ : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (hθ : θ < thetaD1p αp) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (∫ s in (inZone P)ᶜ, P.gQ s * FfamZ P Qn s)
        ≤ (1 + c * Real.log Qn ^ (-θ)) * Family.qle.sizeR Qn
            * ∫ s in (inZone P)ᶜ, P.gQ s * (normA2 P s * shellWt P αp s) := by
  have hθ1 : θ < 1 := lt_of_lt_of_le hθ (min_le_left _ _)
  obtain ⟨c1, hc1, h1⟩ := K1_strip αp hα1 hα2 r ε θ hr hε hθ1
  obtain ⟨c2, hc2, h2⟩ := K2_shellZone hD αp hα1 hα2 r ε θ hr hε hθ
  obtain ⟨c3, hc3, h3⟩ := K3_killed αp hα1 hα2 r ε θ hr hε hθ1
  have h4 := K_int αp hα1 hα2 r ε hr hε
  refine ⟨c1 + c2 + c3, by linarith, ?_⟩
  filter_upwards [h1, h2, h3, h4] with Qn e1 e2 e3 e4
  intro P hP
  obtain ⟨hG, hH, hg0, hw0, hlog⟩ := e4 P hP
  set S := (inZone P)ᶜ with hSdef
  set Z := shellZone P αp with hZdef
  set rr := Real.log (Qn : ℝ) ^ (-θ) with hrr
  set sR := Family.qle.sizeR Qn with hsR
  set c := c1 + c2 + c3 with hc
  have hr0 : 0 ≤ rr := Real.rpow_nonneg hlog _
  have hsR0 : 0 ≤ sR := Nat.cast_nonneg _
  have hSm : MeasurableSet S := measurableSet_outZone P
  have hZm : MeasurableSet Z := measurableSet_Ioc
  -- the factor comparison `(1 + cᵢ r) sR ≤ (1 + c r) sR`
  have hfac : ∀ ci : ℝ, ci ≤ c → (1 + ci * rr) * sR ≤ (1 + c * rr) * sR := by
    intro ci hci
    apply mul_le_mul_of_nonneg_right _ hsR0
    nlinarith
  -- split both integrals at the Shell zone
  have eG := integral_inter_add_sdiff hZm hG
  have eH := integral_inter_add_sdiff hZm hH
  -- the Shell zone part (K2)
  have hZpart : (∫ s in S ∩ Z, P.gQ s * FfamZ P Qn s)
      ≤ (1 + c * rr) * sR * ∫ s in S ∩ Z, P.gQ s * (normA2 P s * shellWt P αp s) := by
    have hI0 : 0 ≤ ∫ s in S ∩ Z, P.gQ s * (normA2 P s * shellWt P αp s) :=
      setIntegral_nonneg (hSm.inter hZm) fun s hs => mul_nonneg (hg0 s) (hw0 s hs.1)
    calc (∫ s in S ∩ Z, P.gQ s * FfamZ P Qn s)
        ≤ (1 + c2 * rr) * sR * ∫ s in S ∩ Z, P.gQ s * (normA2 P s * shellWt P αp s) := e2 P hP
      _ ≤ (1 + c * rr) * sR * ∫ s in S ∩ Z, P.gQ s * (normA2 P s * shellWt P αp s) :=
          mul_le_mul_of_nonneg_right (hfac c2 (by linarith)) hI0
  -- above the zone (K3, integral form): `(S \ Z) ∩ Y = S ∩ Y`, `Y = (α′ℒ, ∞)`
  set Y := Set.Ioi (αp * P.LL) with hYdef
  have hYm : MeasurableSet Y := measurableSet_Ioi
  have hSZY : (S \ Z) ∩ Y = S ∩ Y := by
    ext s
    constructor
    · rintro ⟨⟨hs, _⟩, hy⟩; exact ⟨hs, hy⟩
    · rintro ⟨hs, hy⟩
      refine ⟨⟨hs, fun hz => ?_⟩, hy⟩
      have h1 : s ≤ αp * P.LL := hz.2
      have h2 : αp * P.LL < s := hy
      linarith
  have hGd : IntegrableOn (fun s => P.gQ s * FfamZ P Qn s) (S \ Z) := hG.mono_set Set.sdiff_subset
  have hHd : IntegrableOn (fun s => P.gQ s * (normA2 P s * shellWt P αp s)) (S \ Z) := hH.mono_set Set.sdiff_subset
  have eG2 := integral_inter_add_sdiff hYm hGd
  have eH2 := integral_inter_add_sdiff hYm hHd
  rw [hSZY] at eG2 eH2
  have hYpart : (∫ s in S ∩ Y, P.gQ s * FfamZ P Qn s)
      ≤ (1 + c * rr) * sR * ∫ s in S ∩ Y, P.gQ s * (normA2 P s * shellWt P αp s) := by
    have hI0 : 0 ≤ ∫ s in S ∩ Y, P.gQ s * (normA2 P s * shellWt P αp s) :=
      setIntegral_nonneg (hSm.inter hYm) fun s hs => mul_nonneg (hg0 s) (hw0 s hs.1)
    calc (∫ s in S ∩ Y, P.gQ s * FfamZ P Qn s)
        ≤ (1 + c3 * rr) * sR * ∫ s in S ∩ Y, P.gQ s * (normA2 P s * shellWt P αp s) := e3 P hP
      _ ≤ (1 + c * rr) * sR * ∫ s in S ∩ Y, P.gQ s * (normA2 P s * shellWt P αp s) :=
          mul_le_mul_of_nonneg_right (hfac c3 (by linarith)) hI0
  -- below the zone (K1, pointwise): on `(S \ Z) \ Y` one has `s ≤ log Q + 4`
  have hLpart : (∫ s in (S \ Z) \ Y, P.gQ s * FfamZ P Qn s)
      ≤ (1 + c * rr) * sR * ∫ s in (S \ Z) \ Y, P.gQ s * (normA2 P s * shellWt P αp s) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hGd.mono_set Set.sdiff_subset)
      (Integrable.const_mul (hHd.mono_set Set.sdiff_subset) _) ((hSm.diff hZm).diff hYm) ?_
    intro s hs
    have hsS : s ∈ S := hs.1.1
    have hsZ : s ∉ Z := hs.1.2
    have hsY : s ∉ Y := hs.2
    have hlow : s ≤ Real.log P.Q + 4 := by
      by_contra hcon
      have h1 : s ≤ αp * P.LL := le_of_not_gt hsY
      exact hsZ ⟨lt_of_not_ge hcon, h1⟩
    have hnn : 0 ≤ normA2 P s * shellWt P αp s := hw0 s hsS
    have hpt : FfamZ P Qn s ≤ (1 + c * rr) * sR * (normA2 P s * shellWt P αp s) :=
      calc FfamZ P Qn s ≤ (1 + c1 * rr) * sR * (normA2 P s * shellWt P αp s) := e1 P hP s hsS hlow
        _ ≤ (1 + c * rr) * sR * (normA2 P s * shellWt P αp s) :=
            mul_le_mul_of_nonneg_right (hfac c1 (by linarith)) hnn
    calc P.gQ s * FfamZ P Qn s ≤ P.gQ s * ((1 + c * rr) * sR * (normA2 P s * shellWt P αp s)) :=
          mul_le_mul_of_nonneg_left hpt (hg0 s)
      _ = (1 + c * rr) * sR * (P.gQ s * (normA2 P s * shellWt P αp s)) := by ring
  rw [← eG, ← eH, ← eG2, ← eH2]
  nlinarith [hZpart, hYpart, hLpart]

end ShellK
end ZetaShell
