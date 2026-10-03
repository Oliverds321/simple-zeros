/-
Node K9 (L7_3): the killed-kernel frames for `Family.qle` at the rate `log log Q/log Q`.
* `killed_frame_design` — PROVED here modulo K8b (`hfrob_killed_design`): along ZetaQ's MARGIN design
  `DesignOfRecordM Family.qle r ε` (profile `designProfileQle`, `λ = lamStar`, matching `profDesignQle`), with
  `κ = 2 − 0.7235`. The display, trace, NII, Btr and BF rows and the bracket are ZetaQ's, re-run exactly as in
  `Margin.assembly_eventually_provedM` / `Margin.assembly_clauses_at_design_proved_of_valid` (same lemmas, same
  order), with ZetaQ's Frobenius row replaced by K8b; the bracket at `κ = 2 − 0.7235` is below ZetaQ's at
  `κ_cert = 2 − 0.7212` (`√(κ + r₂)` is monotone, `r₅ ≥ 0`), hence `≤ budgetTotalProved = O(log log Q/log Q)`
  (`Margin.budgetTotalProved_isBigO_of_designM`) along ONE chosen design map (the frame's `Des`).
* `killed_frame_lamStar8` — sorry: the same at a NEW design, ZetaQ's margin design with `P.prof` the degree-8
  profile `profLamStar8` (same `λ*`), `κ = 2 − 0.7237`. Needs the profile-dependent design data re-proved for the new
  profile: `ProfileQ` (even, antitone, `≥ 1/6` on `[0, λ*/2]`), the zone Lipschitz data (`ZoneData`), the ramp-link
  pins (`RampLinkSharp`), `HPre`'s prefactor, the IVT closing (`exists_designOfRecordM`) with the new mass, and a
  `Family`-level profile parameter (ZetaQ's `DesignOfRecordM` pins `P.prof = F.designProfile`). Difficulty: H
  (refactor of the design layer at FIXED `λ*`; no λ-refactor).
-/
import ZetaShell.LemmaK.LK_K8b_HfrobKilled

noncomputable section
open Filter Asymptotics

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Margin ZetaQ.JoinCert ZetaQ.JoinProved

private theorem rateLL_nonneg' : ∀ᶠ Qn : ℕ in atTop, 0 ≤ rateLL Qn := by
  filter_upwards [eventually_ge_atTop 3] with Qn hQn
  have h3 : (3 : ℝ) ≤ Qn := by exact_mod_cast hQn
  have hl : 1 ≤ Real.log (Qn : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h3
  unfold rateLL
  exact div_nonneg (Real.log_nonneg hl) (by linarith)

/-- **K9 (a).** PROVED modulo K8b. -/
theorem killed_frame_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    Nonempty (KFrame ZetaQ.Family.qle r ε profDesignQle (2 - ((PcertKD : ℚ) : ℝ)) rateLL) := by
  classical
  obtain ⟨Q₁, hQ₁⟩ := exists_designOfRecordM Family.qle r ε hr hε
  let dmap : ℝ → ParamsQ := fun Q =>
    if h : Q₁ ≤ Q then Classical.choose (hQ₁ Q h) else Classical.choose (hQ₁ Q₁ le_rfl)
  have hdmap : ∀ Q, Q₁ ≤ Q → DesignOfRecordM Family.qle r ε Q (dmap Q) := by
    intro Q hQ
    simp only [dmap, dif_pos hQ]
    exact Classical.choose_spec (hQ₁ Q hQ)
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 2 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 2 * A₀) hloc
  have hO := budgetTotalProved_isBigO_of_designM (2 * A₀) hA₀' Family.qle r ε hr hε dmap
    (eventually_atTop.mpr ⟨Q₁, hdmap⟩)
  obtain ⟨c₀, hc₀⟩ := (hO.comp_tendsto tendsto_natCast_atTop_atTop).bound
  have hQ1ev : ∀ᶠ Qn : ℕ in atTop, Q₁ ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop Q₁
  refine ⟨{
    Des := fun Q P => Q₁ ≤ Q ∧ P = dmap Q
    exists_design := ⟨Q₁, fun Q hQ => ⟨dmap Q, hQ, rfl⟩⟩
    T_eq := fun Q P h => by obtain ⟨hQ, rfl⟩ := h; exact (hdmap Q hQ).2.2.1
    Q_eq := fun Q P h => by obtain ⟨hQ, rfl⟩ := h; exact (hdmap Q hQ).2.1
    lam_eq := fun Q P h => by
      obtain ⟨hQ, rfl⟩ := h
      rw [(hdmap Q hQ).2.2.2.1]
      simp only [Family.lamStar, profDesignQle, lamStarQ, ZetaQ.lamStar]
      norm_num
    valid := fun Q P h => by obtain ⟨hQ, rfl⟩ := h; exact (hdmap Q hQ).1
    prof_eq := fun Q P h t => by
      obtain ⟨hQ, rfl⟩ := h
      rw [(hdmap Q hQ).2.2.2.2.2.2.2.2.2.2.2]
      simp [Family.designProfile, designProfileQle, KProfile.p, profDesignQle, ZetaQ.Payoff.evalPoly]
      ring
    rows := ⟨max c₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩ }⟩
  filter_upwards [trace_row_eventually_M Family.qle r ε hr hε,
    tail_clauses_certM_eventually Family.qle r ε hr (2 * A₀) hA₀' hloc',
    famNIIUpper_qle_of_designM r ε hA₀ hloc, hfrob_killed_design r ε hr hε,
    famRvMLower_of_designM r ε hr hε, eventually_ge_atTop 2, hc₀, rateLL_nonneg', hQ1ev]
    with Qn htr htail hs hfK hv hQn hbound hrate0 hQ1
  intro P hDes
  obtain ⟨-, rfl⟩ := hDes
  have hdes := hdmap (Qn : ℝ) hQ1
  set P := dmap (Qn : ℝ) with hPdef
  have hP := hdes.1
  have hwr := hdes.2.2.2.2.2.1
  have hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.1]; exact gevreyProfile_rhoTwoQ
  obtain ⟨θ₀, hθ, hpair, hblock⟩ := htail P hdes hϱ
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLB : (0 : ℝ) < P.LB := EFChi.LB_pos_of_valid hP
  have ha0 : (0 : ℝ) < P.aQ := hP.aQ_pos
  have haL : (0 : ℝ) < P.aQ * P.LB := mul_pos ha0 hLB
  have hB0 : (0 : ℝ) ≤ θ₀ / (P.aQ * P.LB) := div_nonneg hθ haL.le
  have hS : (0 : ℝ) ≤ Family.qle.sizeR Qn := by unfold Family.sizeR; positivity
  have hBtr0 : (0 : ℝ) ≤ Btr P Family.qle Qn θ₀ := by
    show (0 : ℝ) ≤ Family.qle.sizeR Qn * θ₀ / (P.aQ * P.LB)
    exact div_nonneg (mul_nonneg hS hθ) haL.le
  have hBF0 : (0 : ℝ) ≤ BF P Family.qle Qn θ₀ := by
    show (0 : ℝ) ≤ Real.sqrt (Family.qle.sizeR Qn) * θ₀ / (P.aQ * P.LB)
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hθ) haL.le
  have hNII' : NIIFamQ P Family.qle Qn ≤ rowR3Proved (2 * A₀) P * NfamQ P Family.qle Qn := by
    unfold rowR3Proved
    exact buffer_row_proved_of_valid Family.qle Qn P (2 * A₀) hP hA₀'
      (hloc_moduli_of_uniform Family.qle Qn hQn hloc') (hs P hdes) (hv P hdes)
  obtain ⟨hBtr', hBF'⟩ := pair_rows_of_valid Family.qle Qn P θ₀ hP hwr hθ (hv P hdes)
  have hbr := propBracketProved_le_budgetTotalProved' (2 * A₀) Family.qle P θ₀ hpair
  have hdisp := EFChi.certificate_display_fam_of_bridge P hP Family.qle Qn θ₀ EFChi.famZc
    (EFChi.famZeroConfig_famZc Family.qle Qn hQn) (EFChi.famGramBridge_famZc P hP Family.qle Qn hQn hwr) hwr
    (abs_trGz_sub_trAhat_fam_le_Btr P Family.qle Qn θ₀ EFChi.famZc hl hblock)
    (sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF P Family.qle Qn θ₀ EFChi.famZc hl hB0 hblock)
    hBtr0 hBF0
  have hr2 : 0 ≤ rowR2 Family.qle P := rowR2_nonneg Family.qle P hP
  have hκK : (2 : ℝ) - ((PcertKD : ℚ) : ℝ) ≤ Family.qle.kappaCert := by
    rw [kappaCert_qle]; norm_num [PcertKD]
  have hκK0 : (0 : ℝ) ≤ 2 - ((PcertKD : ℚ) : ℝ) := by norm_num [PcertKD]
  have hr5 : 0 ≤ rowR5 Family.qle P θ₀ := by
    unfold rowR5
    exact div_nonneg hθ (mul_nonneg (mul_nonneg ha0.le hLB.le) (Real.sqrt_nonneg _))
  have hsq : Real.sqrt (2 - ((PcertKD : ℚ) : ℝ) + rowR2 Family.qle P)
      ≤ Real.sqrt (Family.qle.kappaCert + rowR2 Family.qle P) := Real.sqrt_le_sqrt (by linarith)
  refine ⟨rowR1 Family.qle P, rowR2 Family.qle P, rowR3Proved (2 * A₀) P, rowR4 Family.qle P θ₀,
    rowR5 Family.qle P θ₀, θ₀, hθ, hBtr0, hBF0, by linarith, hdisp, htr P hdes, hfK P hdes, hNII', hBtr',
    hBF', ?_⟩
  -- the bracket at `κ = 2 − 0.7235` is below ZetaQ's bracket at `κ_cert`, hence below the budget
  have hbudget : budgetTotalProved (2 * A₀) Family.qle P ≤ max c₀ 1 * rateLL Qn := by
    have h1 : budgetTotalProved (2 * A₀) Family.qle P ≤ c₀ * ‖rateLL Qn‖ :=
      le_trans (le_abs_self _) (by simpa [Function.comp, rateLL, hPdef] using hbound)
    rw [Real.norm_eq_abs, abs_of_nonneg hrate0] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hrate0)
  have hbracket : propBracketProved (2 * A₀) Family.qle P θ₀
      = 4 * rowR1 Family.qle P + rowR2 Family.qle P + 3 * rowR3Proved (2 * A₀) P + 4 * rowR4 Family.qle P θ₀
        + 2 * rowR5 Family.qle P θ₀ * Real.sqrt (Family.qle.kappaCert + rowR2 Family.qle P)
        + rowR5 Family.qle P θ₀ ^ 2 := rfl
  have hmono : 2 * rowR5 Family.qle P θ₀ * Real.sqrt (2 - ((PcertKD : ℚ) : ℝ) + rowR2 Family.qle P)
      ≤ 2 * rowR5 Family.qle P θ₀ * Real.sqrt (Family.qle.kappaCert + rowR2 Family.qle P) :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  linarith [hbr, hbracket.le, hbracket.ge, hbudget, hmono]

/-- **K9 (b).** -/
theorem killed_frame_lamStar8 (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    Nonempty (KFrame ZetaQ.Family.qle r ε profLamStar8 (2 - ((PcertK : ℚ) : ℝ)) rateLL) := by
  sorry

end LemmaK
end ZetaShell
