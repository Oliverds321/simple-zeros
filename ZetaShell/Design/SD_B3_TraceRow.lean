/-
Node SD-B3 (L7_7, F1b): **the trace row along the Shell design**, `𝒩(1 − r₁) ≤ tr Ĝ_fam`, `r₁ = rowR1 qle P`.
Copy of `ZetaQ.trace_row_eventually_aux`'s `IsFull` branch (`FrobRow9.lean:2198–2234`) with: `row2_eventually`
(literal λ*) ↦ SD-B1 at λ = 191/100 via the same `sizeR_floor_eventually` step (`Budget.lean:8304`'s body);
`rowR1_NfamQ_lower_eventually` ↦ its Shell copy (reads only `famRvMLower`, SD-B4, and `log Q ≥ 30`);
`cWin_of_design` ↦ SD-C1 (`P.cWin = cWinShell S`, a constant); `one_le_lamStar_of_family` ↦ `1 ≤ 191/100`.
`trace_row_of_muPart` (`Budget.lean:7384`) takes a whole `DesignOfRecord`, so its 3-line body is copied
(`abs_trGhatFam_sub_muPart_le`, design-free). Paper §9, §12.2; draft rem:shell-interface.
Deps: SD-B1, SD-B4, SD-C1, `EFChi.rvmChi_main_uniform`, `muPart_ge_NfamQ_sub`, `muErr_div_le`,
`rowR1_NfamQ_lower_qle`, `row2_term_le`, `sizeR_floor_eventually`. Difficulty M. PROVED.
-/
import ZetaShell.Design.SD_B1_Row2Lam
import ZetaShell.Design.SD_B4_RvMLower
import ZetaShell.Design.SD_C1_CWin

namespace ZetaShell.Design

open ZetaQ Filter Real

theorem trace_row_shell_eventually (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (1 - rowR1 Family.qle P) * NfamQ P Family.qle Qn ≤ trGhatFam P Family.qle Qn := by
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hre : (0:ℝ) < r + ε := by linarith
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
    (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  have hLL30 : ∀ᶠ Qn : ℕ in atTop, (30:ℝ) ≤ Real.log Qn :=
    tendsto_log_nat_atTop.eventually_ge_atTop 30
  have hF : Family.qle.IsFull := Family.isFull_qle
  filter_upwards [famRvMLower_shell S53L75 r ε hr hε, hLL30,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (row2_error_eventually_lam (191 / 100) r ε (1 / 10000) (by norm_num) (by norm_num) hr hε
        (by norm_num)),
    sizeR_floor_eventually Family.qle,
    rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀,
    hTtop.eventually_ge_atTop (400 * π * cErr (cWinShell S53L75)), eventually_ge_atTop 2]
    with Qn hrvmL h30 hrow hsz herr hT0 hTE hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hT : P.T = Twin (Qn : ℝ) r ε := hdes.2.2.1
  have hlam' : P.lam = 191 / 100 := by rw [hdes.2.2.2.1]; norm_num [S53L75]
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hQn1 : 1 ≤ Qn := by omega
  have hLLu : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hpi0 : 0 < π := Real.pi_pos
  have hpi : 3 < π := Real.pi_gt_three
  have hS : 0 ≤ Family.sizeR Family.qle Qn := by unfold Family.sizeR; positivity
  have hT0' : 0 ≤ P.T := (T_posQ hP).le
  -- (a) the lower bound `traceRowSlack·|𝔉|·T ≤ r₁·𝒩` (qle branch of `rowR1_NfamQ_lower_eventually`)
  have h2 : traceRowSlack Family.qle * Family.sizeR Family.qle Qn * P.T
      ≤ rowR1 Family.qle P * NfamQ P Family.qle Qn :=
    rowR1_NfamQ_lower_qle P hP Qn (hrvmL P hdes) (le_trans h30 hLLu)
  -- (b) Row 2 at λ = 191/100 (`row2_generic_eventually`'s body; here `L = (191/100)ℒ` exactly)
  have h5 : (P.aQ * P.LB ^ 2)⁻¹
        * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2))
      ≤ traceRowSlack Family.qle * Family.sizeR Family.qle Qn * P.T
        - 2 * (Family.sizeR Family.qle Qn * (P.T / (400 * π))) := by
    dsimp only at hrow
    have hLLd : P.LL = Real.log ((Qn : ℝ) * Real.log (Qn : ℝ) ^ (r + ε) / (2 * π)) := by
      unfold ParamsQ.LL; rw [hQ, hT]; rfl
    have hTd : P.T = Real.log (Qn : ℝ) ^ (r + ε) := by rw [hT]; rfl
    rw [← hLLd, ← hTd] at hrow
    have hLBeq : (191 / 100 : ℝ) * P.LL = P.LB := by unfold ParamsQ.LB; rw [hlam']
    rw [hLBeq] at hrow
    have h1 := row2_term_le P hP Qn
    have hconst : traceRowSlack Family.qle * Family.sizeR Family.qle Qn * P.T
          - 2 * (Family.sizeR Family.qle Qn * (P.T / (400 * π)))
        = (traceRowSlack Family.qle - 1 / (200 * π)) * Family.sizeR Family.qle Qn * P.T := by
      field_simp; ring
    have hc : 1 / 300 ≤ traceRowSlack Family.qle - 1 / (200 * π) := by
      have : 1 / (200 * π) ≤ 1 / 600 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      have e : traceRowSlack Family.qle = 1 / 100 := rfl
      rw [e]; linarith
    rw [hconst]
    calc _ ≤ _ := h1
      _ ≤ 1 / 10000 * (Qn:ℝ) ^ 2 * P.T := hrow
      _ ≤ 1 / 300 * Family.sizeR Family.qle Qn * P.T := by
          have hstep : 1 / 10000 * (Qn:ℝ) ^ 2 ≤ 1 / 300 * Family.sizeR Family.qle Qn := by
            linarith [hsz]
          exact mul_le_mul_of_nonneg_right hstep hT0'
      _ ≤ (traceRowSlack Family.qle - 1 / (200 * π)) * Family.sizeR Family.qle Qn * P.T := by
          gcongr
  -- (c) the μ-part (`trace_row_eventually_aux`'s `IsFull` branch)
  have h1 := muPart_ge_NfamQ_sub P hP hwr hF Qn hQn hA.le hrvm (by rw [hT]; exact hT0)
  have h3 : A * Real.log ((Qn:ℝ) * (P.T + 2)) ≤ P.T / (400 * π) := by
    rw [hT, le_div_iff₀ (by positivity)]; linarith [herr]
  have h4 : muErr P Qn / (P.aQ * P.LB ^ 2) ≤ P.T / (400 * π) := by
    refine (muErr_div_le P hP Qn (by omega) hQ (by rw [hlam']; norm_num)).trans ?_
    rw [cWin_of_shellDesignM hdes, hT, le_div_iff₀ (by positivity)]
    linarith [hTE]
  have h34 : Family.sizeR Family.qle Qn
        * (A * Real.log ((Qn:ℝ) * (P.T + 2)) + muErr P Qn / (P.aQ * P.LB ^ 2))
      ≤ Family.sizeR Family.qle Qn * (P.T / (400 * π) + P.T / (400 * π)) :=
    mul_le_mul_of_nonneg_left (add_le_add h3 h4) hS
  have hmu : (1 - rowR1 Family.qle P) * NfamQ P Family.qle Qn
      ≤ (P.aQ * P.LB ^ 2)⁻¹ * famMuPart P Family.qle Qn
        - (P.aQ * P.LB ^ 2)⁻¹
            * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2)) := by
    linarith [h1, h2, h5, h34]
  -- (d) `trace_row_of_muPart`'s body
  have key := abs_trGhatFam_sub_muPart_le P hF Qn hP hwr
  have h := (abs_le.mp key).1
  linarith

end ZetaShell.Design
