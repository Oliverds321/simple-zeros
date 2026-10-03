/-
F1c-4, base (L7_3, round 4): the Shell-design inputs of **the Frobenius assembly** (`LF_Assembly.lean`).
* `design_basic_shell`, `NfamQ_sharp_shell`, `NfamQ_crude_shell`: ZetaQ's `design_basic`, `NfamQ_sharp_eventually`
  (branch `qle`), `NfamQ_crude_eventually` along `ShellDesignM` (A7 for `design_regime`, B4 for `famRvMLower`). PROVED.
* F1c-4a (Row 9) `shell_row9`: ZetaQ's `A3_eventually` with its literal `λ* = 1.2507321515` replaced by `λ = 191/100`
  and `Row9Numeric.row9_closed_eventually` by L7_7's B2 `row9_closed_eventually_lam` (`R9fun_eventually_lam`).
  (Rows 8, A1 and A2, are in `LF_Rows8.lean`.)
* F1c-4b `shell_hsep`: `Bfam ≤ c_μ·Q·envSep` along the Shell design. ZetaQ's `hsep_of_design` uses `Bfam_le_sep` at
  `δ = 1/2` (from `X ≤ Q^{3/2}`), which does not hold at `λ = 1.91`; `Bfam_le_sep` requires `1/2 ≤ δ`. Needs the ends
  estimate at `δ = 9/200` (A7: `X ≤ Q^{2−9/200}`; L7_4 D4; C3's `c₁ = 0.52`). Round 5: this old form (envelope
  `c₁ = 0.41`) is NOT USED; the restated `shell_hsepS` (`LF_HsepS`, `c₁ = 0.52`) is proved and consumed instead.
* F1c-4c `shell_ends`: ZetaQ's `A5_eventually` (`endsMaj ≤ ε′/8·𝒩`) along the Shell design (`Kends (cWinShell)`). PROVED.
-/
import ZetaShell.ShellK.LF_Defs
import ZetaShell.Design.SD_A7_Regime
import ZetaShell.Design.SD_A8_Scales
import ZetaShell.Design.SD_B2_Row9Lam
import ZetaShell.Design.SD_B4_RvMLower
import ZetaShell.Design.SD_C1_CWin

noncomputable section
open MeasureTheory Set Real Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Payoff ZetaQ.Zones ZetaQ.Ends ZetaQ.FamRows ZetaQ.FrobAssembly

/-- ZetaQ's `design_basic` along the Shell design. -/
theorem design_basic_shell (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      30 ≤ P.LL ∧ 8 ≤ P.LB ∧ 1 ≤ P.lam ∧ 8 * P.w ≤ P.LB ∧ 2 ≤ Qn := by
  have hS : (1 : ℝ) ≤ ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  filter_upwards [Design.shellDesign_regime S53L75 hS2 r ε hr hε 30 (by norm_num), eventually_ge_atTop 2]
    with Qn hreg hQn2
  intro P hdes
  obtain ⟨h30, -⟩ := hreg P hdes
  have hQn1 : 1 ≤ Qn := by omega
  obtain ⟨-, hLL, hLB, -⟩ := Design.scales_of_shellDesignM hS hdes hr hQn1
  have hlam : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
  exact ⟨by linarith, by linarith, by rw [hlam]; exact hS, hdes.2.2.2.2.2.1, hQn2⟩

/-- **F1c-4b, OLD FORM — NOT USED (round 5).** `hsep` along the Shell design with ZetaQ's envelope `envSep`
(`c₁ = 0.41`). The tree's route (`Bfam_le_sep`: Minkowski + large sieve) needs `c₁ ≥ 1.955/(√2π) + 3/(√2π³) = 0.5085`
at `λ = 1.91`, so this form is not reachable by it; it is superseded by `shell_hsepS` (`LF_HsepS`, envelope
`c₁ = 0.52`, PROVED), which `shell_assembly` now consumes. Kept under its name, with its `sorry`, for the record. -/
theorem shell_hsep (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ := by
  sorry

/-- ZetaQ's `NfamQ_sharp_eventually` (branch `qle`) along the Shell design: A7 in place of `design_regime`, L7_7's B4
`famRvMLower_shell` in place of `famRvMLower_of_design`; then `NfamQ_sharp_qle` verbatim. -/
theorem NfamQ_sharp_shell (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL ≤ Family.qle.Cconst * (1 + η) * NfamQ P Family.qle Qn := by
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hpi4 : (97.408 : ℝ) < Real.pi ^ 4 := Ends.pi_four_gt
  have hK1 : (1:ℝ) ≤ 6 * Real.pi ^ 4 / η := by
    rw [le_div_iff₀ hη]; nlinarith
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  filter_upwards [Design.shellDesign_regime S53L75 hS2 r ε hr hε (6 * Real.pi ^ 4 / η) hK1,
    Design.shellDesign_regime S53L75 hS2 r ε hr hε (max 1 (max (8 * 0.307 / η) (48 * Real.pi * A / η)))
      (le_max_left _ _),
    Design.famRvMLower_shell S53L75 r ε hr hε, eventually_ge_atTop 2] with Qn hreg1 hreg2 hrvmq hQn2
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  obtain ⟨hlogQ1, -, -, -, hsz1, -, -, -⟩ := hreg1 P hdes
  obtain ⟨hlogQ2, hT2, -, -, -, -, -, hlog3⟩ := hreg2 P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hLLge : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hmax1 : 8 * 0.307 / η ≤ P.LL :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hlogQ2.trans hLLge)
  have hlogQ0 : 0 ≤ Real.log Qn := Real.log_natCast_nonneg Qn
  apply NfamQ_sharp_qle P hP Qn hQn1 hQ (hrvmq P hdes) hη hη1
  · have h2 := hsz1
    rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
    have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
    nlinarith
  · rw [div_le_iff₀ hη] at hmax1; nlinarith

/-- ZetaQ's `NfamQ_crude_eventually` along the Shell design. -/
theorem NfamQ_crude_shell (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * Family.qle.Cconst) ≤ NfamQ P Family.qle Qn := by
  filter_upwards [NfamQ_sharp_shell r ε hr hε (η := 1) one_pos le_rfl] with Qn h
  intro P hdes
  have h1 := h P hdes
  have hC : 0 < Family.qle.Cconst := Cconst_pos Family.qle
  have hpi := Real.pi_pos
  calc (Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * Family.qle.Cconst)
      = ((Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL) / (2 * Family.qle.Cconst) := by
        field_simp; ring
    _ ≤ (Family.qle.Cconst * (1 + 1) * NfamQ P Family.qle Qn) / (2 * Family.qle.Cconst) := by gcongr
    _ = NfamQ P Family.qle Qn := by field_simp; ring

/-- **F1c-4c.** The ends majorant along the Shell design: ZetaQ's `A5_eventually` verbatim, with A7,
`design_basic_shell`, `NfamQ_crude_shell` and C1 (`cWin_of_shellDesignM`). PROVED. (The bandwidth enters the ends only
through `hsep`, F1c-4b; `endsMaj_le` needs `1 ≤ λ` only.) -/
theorem shell_ends (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      endsMaj P ≤ ε' / 8 * NfamQ P Family.qle Qn := by
  have hC := Cconst_pos Family.qle
  set Ke : ℝ := Kends (Design.cWinShell S53L75) with hKe
  set K : ℝ := max 1 (32 * Real.pi * Family.qle.Cconst * Ke / ε') with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  filter_upwards [Design.shellDesign_regime S53L75 hS2 r ε hr hε K hK1, design_basic_shell r ε hr hε,
    NfamQ_crude_shell r ε hr hε] with Qn hreg hbas hcrude
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  obtain ⟨-, -, hTK, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hN := hcrude P hdes
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := by linarith
  have hpi := Real.pi_pos
  have hcW : P.cWin = Design.cWinShell S53L75 := Design.cWin_of_shellDesignM hdes
  have hc0 : 0 ≤ Design.cWinShell S53L75 := by rw [← hcW]; exact hP.cWin_pos.le
  have hKe0 : 0 ≤ Ke := Kends_nonneg hc0
  have hends := endsMaj_le hP hLL30 hlam hL8
  rw [hcW, hQ] at hends
  have hK' : 32 * Real.pi * Family.qle.Cconst * Ke * P.LL ^ 2 ≤ ε' * P.T := by
    have h1 : 32 * Real.pi * Family.qle.Cconst * Ke / ε' ≤ K := le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg P.LL)
    rw [div_mul_eq_mul_div, div_le_iff₀ hε'] at h2
    have h3 := mul_le_mul_of_nonneg_right hTK hε'.le
    linarith
  have hfin : Ke * (Qn : ℝ) ^ 2 * P.LL ^ 3
      ≤ ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * Family.qle.Cconst)) := by
    rw [show Ke * (Qn : ℝ) ^ 2 * P.LL ^ 3
        = (32 * Real.pi * Family.qle.Cconst * Ke * P.LL ^ 2) * ((Qn : ℝ) ^ 2 * P.LL)
          / (32 * Real.pi * Family.qle.Cconst) by
          first | (field_simp; ring) | field_simp,
      show ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * Family.qle.Cconst))
        = (ε' * P.T) * ((Qn : ℝ) ^ 2 * P.LL) / (32 * Real.pi * Family.qle.Cconst) by ring]
    gcongr
  calc endsMaj P ≤ Ke * (Qn : ℝ) ^ 2 * P.LL ^ 3 := hends
    _ ≤ ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * Family.qle.Cconst)) := hfin
    _ ≤ ε' / 8 * NfamQ P Family.qle Qn := by gcongr

/-- ZetaQ's `R9fun_eventually` at a free bandwidth `λ < 2`, from L7_7's B2. -/
theorem R9fun_eventually_lam (lam r ε c : ℝ) (hlam0 : 0 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε)
    (hc : 0 < c) :
    ∀ᶠ Q : ℝ in atTop,
      R9fun Q (Real.log (Real.log Q ^ (r + ε) / (2 * Real.pi)))
          (lam * Real.log (Q * Real.log Q ^ (r + ε) / (2 * Real.pi)))
        ≤ c * Q ^ 2 * Real.log Q ^ (r + ε) := by
  filter_upwards [Design.row9_closed_eventually_lam lam r ε (c / 3) hlam0 hlam2 hr hε (by positivity)] with Q hQ
  dsimp only at hQ
  have h3 : (3:ℝ) * (c / 3 * Q ^ 2 * Real.log Q ^ (r + ε)) = c * Q ^ 2 * Real.log Q ^ (r + ε) := by
    ring
  unfold R9fun
  linarith [mul_le_mul_of_nonneg_left hQ (by norm_num : (0:ℝ) ≤ 3)]

set_option maxHeartbeats 4000000 in
/-- **F1c-4a (Row 9).** ZetaQ's `A3_eventually` along the Shell design: its proof verbatim, with the literal
`λ* = 1.2507321515` replaced by `λ = 191/100` (`R9fun_eventually_lam`, from B2) and the design facts by A7,
`design_basic_shell`, `NfamQ_crude_shell`. -/
theorem shell_row9 (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn) ≤ ε' / 8 * NfamQ P Family.qle Qn := by
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  have hC := Cconst_pos Family.qle
  have hR9 := tendsto_natCast_atTop_atTop.eventually
    (R9fun_eventually_lam (191 / 100) r ε 1 (by norm_num) (by norm_num) hr hε one_pos)
  set K : ℝ := max 1 (358 * Family.qle.Cconst / ε') with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  filter_upwards [Design.shellDesign_regime S53L75 hS2 r ε hr hε K hK1, design_basic_shell r ε hr hε,
    NfamQ_crude_shell r ε hr hε, hR9, eventually_ge_atTop 1] with Qn hreg hbas hcrude hR9' hQn1
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hT : P.T = Real.log (Qn : ℝ) ^ (r + ε) := by rw [hdes.2.2.1]; rfl
  obtain ⟨hlogK, -, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hN := hcrude P hdes
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := by linarith
  have hpi := Real.pi_pos
  have hpi4 : Real.pi ≤ 3.1416 := Real.pi_lt_d4.le
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hK' : 358 * Family.qle.Cconst ≤ ε' * P.LL := by
    have := (le_max_right _ _ : 358 * Family.qle.Cconst / ε' ≤ K).trans (hlogK.trans hlogQ)
    rw [div_le_iff₀ hε'] at this; linarith
  -- `R9closed ≤ Qn² T`
  have hLLeq : P.LL = Real.log ((Qn : ℝ) * Real.log (Qn : ℝ) ^ (r + ε) / (2 * Real.pi)) := by
    unfold ParamsQ.LL; rw [hQ, hT]
  have hl : Zeta23.l P.T = Real.log (Real.log Qn ^ (r + ε) / (2 * Real.pi)) := by
    unfold Zeta23.l; rw [hT]
  have hR9'' : R9fun (Qn : ℝ) (Zeta23.l P.T) (191 / 100 * P.LL) ≤ 1 * (Qn : ℝ) ^ 2 * P.T := by
    rw [hl, hLLeq, hT]; exact hR9'
  have hQn1R : (1:ℝ) ≤ Qn := by exact_mod_cast hQn1
  have hLB1 : P.LB ≤ 191 / 100 * P.LL := by
    have hlam' : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
    have h191 : ((S53L75.lam : ℚ) : ℝ) = 191 / 100 := by norm_num [S53L75]
    show P.lam * P.LL ≤ _
    rw [hlam', h191]
  have hR9c : R9closed P Qn ≤ (Qn : ℝ) ^ 2 * P.T := by
    unfold R9closed
    refine (R9fun_mono hQn1R (l_nonneg hP) hP.LB_pos.le hLB1).trans ?_
    linarith
  have hR9c0 : 0 ≤ R9closed P Qn := by
    unfold R9closed R9fun
    have := l_nonneg hP
    have := hP.LB_pos
    have hlogQ0 : 0 ≤ Real.log (Qn:ℝ) := Real.log_natCast_nonneg Qn
    positivity
  have hinv := inv_aL_le hP hlam
  have hmain : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
      ≤ (16 / 9) / P.LL ^ 2 * (2 * ((Qn : ℝ) ^ 2 * P.T)) := by
    apply mul_le_mul hinv (by linarith) (by positivity) (by positivity)
  have hkey : (32 / 9 : ℝ) * (32 * Real.pi * Family.qle.Cconst) ≤ ε' * P.LL ^ 3 := by
    have h1 : (32 / 9 : ℝ) * (32 * Real.pi * Family.qle.Cconst) ≤ 358 * Family.qle.Cconst := by
      have := mul_le_mul_of_nonneg_right hpi4 hC.le
      linarith
    have hLL3 : P.LL ≤ P.LL ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hLL3 hε'.le]
  have hfin : (16 / 9) / P.LL ^ 2 * (2 * ((Qn : ℝ) ^ 2 * P.T))
      ≤ ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * Family.qle.Cconst)) := by
    rw [show (16 / 9) / P.LL ^ 2 * (2 * ((Qn : ℝ) ^ 2 * P.T))
        = ((32 / 9) * (32 * Real.pi * Family.qle.Cconst)) * ((Qn : ℝ) ^ 2 * P.T * P.LL)
          / (32 * Real.pi * Family.qle.Cconst * P.LL ^ 3) by first | (field_simp; ring) | field_simp,
      show ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * Family.qle.Cconst))
        = (ε' * P.LL ^ 3) * ((Qn : ℝ) ^ 2 * P.T * P.LL) / (32 * Real.pi * Family.qle.Cconst * P.LL ^ 3) by
          first | (field_simp; ring) | field_simp]
    gcongr
  calc (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
      ≤ (16 / 9) / P.LL ^ 2 * (2 * ((Qn : ℝ) ^ 2 * P.T)) := hmain
    _ ≤ ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * Family.qle.Cconst)) := hfin
    _ ≤ ε' / 8 * NfamQ P Family.qle Qn := by gcongr

end F1c
end ShellK
end ZetaShell
