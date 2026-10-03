/-
Node K8a-1 (L7_3, round 2): the KILLED master inequality. ZetaQ's `InZone.famPP_total_le` bounds the PP block by
`masterRHS`, whose out-zone term is the pointwise sieve `familySum ∫_{inZoneᶜ} gQ|A_χ|² ≤ sieveBudgetQ·∫_{inZoneᶜ} gQ·normA2`
(`InZone.famA_integral_le`). With K7 (Lemma K (i), `killed_pointwise`) in place of the sieve on the out-zone, pointwise
`Σ_χ|A_χ(s)|² ≤ sieveBudgetQ·normA2 − Q²·savWeight + errWeight`; integrating against `gQ ≥ 0` over `inZoneᶜ`
subtracts `2Q²·Sav` and adds `2·Err` (the factor 2: the B-half equals the A-half, `integral_B_eq_A`).
Dependencies: K7 (`killed_pointwise` at `λ = λ*`), K8d (the bridge `charSum = AchiC`, `l2sq = normA2`,
`Xlam = XQ`), trunk `famPP_total_le`'s steps (copied verbatim, with `famA_integral_le` replaced).
Difficulty: M. PROVED here modulo K7.
-/
import ZetaShell.LemmaK.LK_K8a_Defs
import ZetaShell.LemmaK.LK_K7_Pointwise
import ZetaShell.LemmaK.LK_K8d_Bridge

noncomputable section
open Filter MeasureTheory Set

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaQ.Payoff

/-- K7 at a design point, in ZetaQ's objects: `Σ_χ|A_χ(s)|² ≤ sieveBudgetQ·normA2 − Q²·savWeight + errWeight`. -/
theorem killed_pointwise_at {r ε : ℝ} {Qn : ℕ} {P : ParamsQ} (C₁ : ℝ)
    (hdes : DesignOfRecord Family.qle r ε (Qn : ℝ) P)
    (hk : ∀ s : ℝ,
      ∑ q ∈ Finset.Icc 2 Qn, ∑ χ ∈ ZetaQ.primitiveChars q,
          ‖ZetaQ.charSum q ⌊Xlam ZetaQ.lamStar (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
            (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s) χ‖ ^ 2
        ≤ (Qn : ℝ) ^ 2 *
            (ZetaQ.l2sq ⌊Xlam ZetaQ.lamStar (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
              - (1 - C₁ / Real.log (Qn : ℝ)) * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi))
                  * max (s - ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) 0
                  * (if s ≤ Real.log (Xlam ZetaQ.lamStar (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 then 1 else 0)
              + 2 * Real.sqrt (ZetaQ.l2sq ⌊Xlam ZetaQ.lamStar (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
                  (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)))
          + (2 * Real.pi * Xlam ZetaQ.lamStar (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)
              + (max 2 (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)) ^ 2)
            * ZetaQ.l2sq ⌊Xlam ZetaQ.lamStar (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
                (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s))
    (s : ℝ) :
    familySum Family.qle Qn (fun _ χ => ‖Achi P χ s‖ ^ 2)
      ≤ sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s := by
  have hQR : P.Q = (Qn : ℝ) := hdes.2.1
  have hTT : ZetaQ.Twin (Qn : ℝ) r ε = P.T := hdes.2.2.1.symm
  have hlam : P.lam = ZetaQ.lamStar := hdes.2.2.2.1
  have hXX : Xlam ZetaQ.lamStar (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) = P.XQ := by
    rw [hTT, ← hlam, ← hQR]; exact Xlam_eq_XQ P
  have hcs : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ZetaQ.charSum q ⌊P.XQ⌋₊ (acoef P.T s) χ = Achi P χ s := by
    intro q χ
    have h := charSum_eq_AchiC P χ s
    rw [Xlam_eq_XQ] at h
    exact h
  have hl2 : ZetaQ.l2sq ⌊P.XQ⌋₊ (acoef P.T s) = normA2 P s := by
    have h := l2sq_eq_normA2 P s
    rw [Xlam_eq_XQ] at h
    exact h
  have hk' := hk s
  rw [hXX, hTT, hl2] at hk'
  simp only [hcs] at hk'
  have hfs : familySum Family.qle Qn (fun _ χ => ‖Achi P χ s‖ ^ 2)
      = ∑ q ∈ Finset.Icc 2 Qn, ∑ χ ∈ ZetaQ.primitiveChars q, ‖Achi P χ s‖ ^ 2 := rfl
  rw [hfs]
  unfold savWeight errWeight sieveBudgetQ
  rw [hQR]
  linarith [hk']

/-- **K8a-1.** -/
theorem killed_master (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C₁ : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      ∀ e : ℝ, 0 < e →
        familySum Family.qle Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
          ≤ masterRHS Family.qle Qn P e - 2 * (P.Q ^ 2 * Sav C₁ Qn P) + 2 * Err P := by
  have hl1 : (1 : ℝ) < ZetaQ.lamStar := by norm_num [ZetaQ.lamStar]
  have hl2 : ZetaQ.lamStar < 2 := by norm_num [ZetaQ.lamStar]
  obtain ⟨C₁, hK7⟩ := killed_pointwise ZetaQ.lamStar r ε hl1 hl2 hr hε
  refine ⟨C₁, ?_⟩
  filter_upwards [hK7, reg_eventually Family.qle r ε hr hε] with Qn hk hreg
  intro P hdes e he
  obtain ⟨hP, hw, -, hs8, -⟩ := hreg P hdes
  have hs0 : 0 ≤ P.s0 := by linarith
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQn : Qn ≤ ⌊P.Q⌋₊ := by rw [hQ, Nat.floor_natCast]
  have hLS := largeSieveFamily_holds
  have hT : (0 : ℝ) ≤ P.T := hP.T_pos.le
  have hphi := phiQ_sq_integrable P hP hw
  have hUm : MeasurableSet (inZone P) := measurableSet_inZone P
  have hUc : MeasurableSet (inZone P)ᶜ := hUm.compl
  -- (1)–(4): famPP_total_le's steps, verbatim
  have h1 : familySum Family.qle Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      = familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) := by
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact lemma41_parseval_diag P (PXchi P χ) hphi (FrobAssembly.PXchi_integrableOn P χ)
      (FrobAssembly.PXchi_sq_integrableOn P χ)
  have h2 : familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      = familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2)
        + familySum Family.qle Qn (fun _ χ => 2 * ∫ s : ℝ,
            P.gQ s * (Achi P χ s * (starRingEnd ℂ) (Bchi P χ s)).re) := by
    rw [← familySum_add', ← familySum_add']
    refine familySum_congr_prim Family.qle Qn fun q χ hχ => ?_
    have := zone_expansion P hP hw χ hχ Set.univ
    simpa only [MeasureTheory.setIntegral_univ] using this
  have h3 : familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2)
      = familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2) := by
    unfold familySum
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => integral_B_eq_A P χ
  have h4 : familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = familySum Family.qle Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum Family.qle Qn (fun _ χ => ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2) := by
    rw [← familySum_add']
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact (MeasureTheory.integral_add_compl hUm
      (gQ_mul_integrable P hP hw ((Achi_continuous P χ).norm.pow 2))).symm
  have hin : familySum Family.qle Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = inFormF Family.qle Qn P (acoefS P) := rfl
  have hfull := inFormF_full_le Family.qle Qn P hP hw hLS hQn hs0 he
  have hcross := (abs_le.mp (cross_integral_family Family.qle Qn P hP hw hLS hQn Set.univ
    MeasurableSet.univ)).2
  simp only [MeasureTheory.setIntegral_univ] at hcross
  -- (5′) the out-zone half with K7 in place of the sieve
  have hAint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      Integrable (fun s => P.gQ s * ‖Achi P χ s‖ ^ 2) :=
    fun q χ => gQ_mul_integrable P hP hw ((Achi_continuous P χ).norm.pow 2)
  have hNint : Integrable (fun s => P.gQ s * normA2 P s) := gQ_mul_integrable P hP hw (normA2_continuous P hT)
  have hR0c : Continuous (fun s => R0 P.Q P.T s) := by
    unfold R0; exact Real.continuous_exp.div_const _
  have hEc : Continuous (errWeight P) := by
    unfold errWeight
    have hn := normA2_continuous P hT
    exact (continuous_const.mul (Real.continuous_sqrt.comp hn)).add
      ((continuous_const.add ((continuous_const.max hR0c).pow 2)).mul hn)
  have hEint : Integrable (fun s => P.gQ s * errWeight P s) := gQ_mul_integrable P hP hw hEc
  have hSeq : (fun s => P.gQ s * savWeight C₁ Qn P s)
      = Set.indicator {s : ℝ | s ≤ Real.log P.XQ - 1}
          (fun s => P.gQ s * ((1 - C₁ / Real.log (Qn : ℝ)) * (P.T / (2 * Real.pi))
            * max (s - ellK P.Q P.T) 0)) := by
    funext s
    unfold savWeight
    by_cases h : s ≤ Real.log P.XQ - 1
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have hSint : Integrable (fun s => P.gQ s * savWeight C₁ Qn P s) := by
    rw [hSeq]
    refine Integrable.indicator (gQ_mul_integrable P hP hw ?_)
      (measurableSet_le measurable_id measurable_const)
    exact continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)
  have hswap : familySum Family.qle Qn (fun _ χ => ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = ∫ s in (inZone P)ᶜ, P.gQ s * familySum Family.qle Qn (fun _ χ => ‖Achi P χ s‖ ^ 2) := by
    have hin' : ∀ q ∈ Family.qle.moduli Qn,
        ∫ s in (inZone P)ᶜ, ∑ χ ∈ Family.qle.chars q, P.gQ s * ‖Achi P χ s‖ ^ 2
          = ∑ χ ∈ Family.qle.chars q, ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2 :=
      fun q _ => integral_finset_sum _ (fun χ _ => (hAint q χ).integrableOn)
    have hout' : ∫ s in (inZone P)ᶜ, ∑ q ∈ Family.qle.moduli Qn, ∑ χ ∈ Family.qle.chars q,
          P.gQ s * ‖Achi P χ s‖ ^ 2
        = ∑ q ∈ Family.qle.moduli Qn, ∫ s in (inZone P)ᶜ, ∑ χ ∈ Family.qle.chars q,
          P.gQ s * ‖Achi P χ s‖ ^ 2 :=
      integral_finset_sum _ (fun q _ =>
        (integrable_finset_sum _ (fun χ _ => hAint q χ)).integrableOn)
    have hfun : (fun s => P.gQ s * familySum Family.qle Qn (fun _ χ => ‖Achi P χ s‖ ^ 2))
        = fun s => ∑ q ∈ Family.qle.moduli Qn, ∑ χ ∈ Family.qle.chars q, P.gQ s * ‖Achi P χ s‖ ^ 2 := by
      funext s; unfold familySum; simp [Finset.mul_sum]
    rw [hfun, hout']
    unfold familySum
    exact (Finset.sum_congr rfl hin').symm
  have hpt := killed_pointwise_at C₁ hdes hk
  have hmono : ∫ s in (inZone P)ᶜ, P.gQ s * familySum Family.qle Qn (fun _ χ => ‖Achi P χ s‖ ^ 2)
      ≤ ∫ s in (inZone P)ᶜ, (sieveBudgetQ P * (P.gQ s * normA2 P s)
          - P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s) + P.gQ s * errWeight P s) := by
    apply setIntegral_mono_on _ _ hUc
    · intro s _
      have hg := lemma42_g_nonneg P s
      have := mul_le_mul_of_nonneg_left (hpt s) hg
      nlinarith [this]
    · have : Integrable (fun s => P.gQ s * familySum Family.qle Qn (fun _ χ => ‖Achi P χ s‖ ^ 2)) := by
        unfold familySum
        have : Integrable (fun s => ∑ q ∈ Family.qle.moduli Qn, ∑ χ ∈ Family.qle.chars q,
            P.gQ s * ‖Achi P χ s‖ ^ 2) :=
          integrable_finset_sum _ (fun q _ => integrable_finset_sum _ (fun χ _ => hAint q χ))
        refine this.congr (Filter.Eventually.of_forall fun s => ?_)
        simp [Finset.mul_sum]
      exact this.integrableOn
    · exact (((hNint.const_mul (sieveBudgetQ P)).sub (hSint.const_mul (P.Q ^ 2))).add hEint).integrableOn
  have iA : IntegrableOn (fun s => sieveBudgetQ P * (P.gQ s * normA2 P s)) (inZone P)ᶜ :=
    (hNint.const_mul _).integrableOn
  have iB : IntegrableOn (fun s => P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s)) (inZone P)ᶜ :=
    (hSint.const_mul _).integrableOn
  have iC : IntegrableOn (fun s => P.gQ s * errWeight P s) (inZone P)ᶜ := hEint.integrableOn
  have e1 := integral_add (μ := volume.restrict (inZone P)ᶜ)
    (f := fun s => sieveBudgetQ P * (P.gQ s * normA2 P s) - P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s))
    (g := fun s => P.gQ s * errWeight P s) (by exact iA.sub iB) iC
  have e2 := integral_sub (μ := volume.restrict (inZone P)ᶜ)
    (f := fun s => sieveBudgetQ P * (P.gQ s * normA2 P s))
    (g := fun s => P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s)) iA iB
  have e3 := integral_const_mul (μ := volume.restrict (inZone P)ᶜ) (sieveBudgetQ P)
    (fun s => P.gQ s * normA2 P s)
  have e4 := integral_const_mul (μ := volume.restrict (inZone P)ᶜ) (P.Q ^ 2)
    (fun s => P.gQ s * savWeight C₁ Qn P s)
  have hsplit : ∫ s in (inZone P)ᶜ, (sieveBudgetQ P * (P.gQ s * normA2 P s)
          - P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s) + P.gQ s * errWeight P s)
      = sieveBudgetQ P * (∫ s in (inZone P)ᶜ, P.gQ s * normA2 P s) - P.Q ^ 2 * Sav C₁ Qn P + Err P := by
    unfold Sav Err
    rw [e1, e2, e3, e4]
  have hout : familySum Family.qle Qn (fun _ χ => ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2)
      ≤ sieveBudgetQ P * (∫ s in (inZone P)ᶜ, P.gQ s * normA2 P s) - P.Q ^ 2 * Sav C₁ Qn P + Err P := by
    rw [hswap, ← hsplit]; exact hmono
  unfold masterRHS
  rw [h1, h2, h3, h4, hin]
  linarith
