/-
L7_7: **L7_1's node F1 (`shell_frame_qle`, `lean_work/L7_1/skeleton/F1_ShellFrameQle.lean`) DERIVED from the design
layer's nodes** — the consumption check. The statement is L7_1's verbatim; the proof uses only the node statements
(SD-A1, A6, B3, B4, B5, B6, B8, D1, F1c) and green ZetaQ lemmas (`EFChi.localCountChi_uniform`, `hloc_mono`,
`buffer_row_proved_of_valid`, `pair_rows_of_valid`, `hloc_moduli_of_uniform`, `NfamQ_nonneg`). Every `sorry` it
depends on is in a node file. The frame's design predicate is `ShellDesignM S53L75 r ε`; the certificate hypothesis
supplies the profile's L75 side conditions (`hcert.2.2.2.2.1`). Constant `c = c_frob + c_rate`.
-/
import ZetaShell.Design.SD_A6_Exists
import ZetaShell.Design.SD_B3_TraceRow
import ZetaShell.Design.SD_B4_RvMLower
import ZetaShell.Design.SD_B5_NIIUpper
import ZetaShell.Design.SD_B6_Tail
import ZetaShell.Design.SD_B8_Rates
import ZetaShell.Design.SD_D1_Display
import ZetaShell.Skeleton.SD_F1c_FrobRow

namespace ZetaShell.Design

open ZetaQ ZetaQ.JoinCert ZetaQ.JoinProved Filter

theorem shell_frame_qle_of_nodes (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertS53)
    (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    Nonempty (ShellFrame ZetaQ.Family.qle r ε S53L75 (2 - ((PcertS53 : ℚ) : ℝ)) (shellRate θ)) := by
  have hL : S53L75.L75 := hcert.2.2.2.2.1
  have hθ1 : θ < 1 := by linarith
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 2 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 2 * A₀) hloc
  obtain ⟨c₁, hc₁, hfrob⟩ := frob_row_shell hD hP hcert r ε θ hr hε hθ hθ'
  obtain ⟨c₂, hc₂, hrate⟩ := rows_rate_shell r ε θ (2 * A₀) hr hε hθ hθ1 hA₀'
  refine ⟨{
    Des := ShellDesignM S53L75 r ε
    exists_design := exists_shellDesignM hL r ε hr hε
    T_eq := fun _ _ h => h.2.2.1
    Q_eq := fun _ _ h => h.2.1
    lam_eq := fun _ _ h => h.2.2.2.1
    valid := fun _ _ h => h.1
    prof_eq := fun _ _ h t => by rw [h.2.2.2.2.2.2.2.2.2.2.2, ShellProfile.poly_eval]
    rows := ?_ }⟩
  refine ⟨c₁ + c₂, by positivity, ?_⟩
  have hlog1 : ∀ᶠ Qn : ℕ in atTop, (1 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [trace_row_shell_eventually r ε hr hε, famRvMLower_shell S53L75 r ε hr hε,
    famNIIUpper_shell S53L75 r ε hA₀ hloc, tail_shell_eventually r ε hr (2 * A₀) hA₀' hloc',
    hfrob, hrate, eventually_ge_atTop 2, hlog1] with Qn htr hrvm hNII htail hfr hrt hQn hlog
  intro P hdes
  have hPv : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  obtain ⟨θ₀, hθ0, hθle, hblock⟩ := htail P hdes
  obtain ⟨hBtr0, hBF0, hdisp⟩ := display_shell P hPv hwr Family.qle Qn hQn θ₀ hθ0 hblock
  obtain ⟨hr1, hr3, hr45⟩ := hrt P hdes
  obtain ⟨hr4, hr5⟩ := hr45 θ₀ hθ0 hθle
  have hN : 0 ≤ NfamQ P Family.qle Qn := NfamQ_nonneg P Family.qle Qn
  have hR : 0 ≤ shellRate θ Qn := Real.rpow_nonneg (by linarith) _
  have hNII' : NIIFamQ P Family.qle Qn ≤ rowR3Proved (2 * A₀) P * NfamQ P Family.qle Qn :=
    buffer_row_proved_of_valid Family.qle Qn P (2 * A₀) hPv hA₀'
      (hloc_moduli_of_uniform Family.qle Qn hQn hloc') (hNII P hdes) (hrvm P hdes)
  obtain ⟨hBtr', hBF'⟩ := pair_rows_of_valid Family.qle Qn P θ₀ hPv hwr hθ0 (hrvm P hdes)
  have hc2 : c₂ * shellRate θ Qn ≤ (c₁ + c₂) * shellRate θ Qn := by nlinarith
  have hc1 : c₁ * shellRate θ Qn ≤ (c₁ + c₂) * shellRate θ Qn := by nlinarith
  refine ⟨θ₀, hθ0, hBtr0, hBF0, hdisp, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 := htr P hdes
    have h1 : (1 - (c₁ + c₂) * shellRate θ Qn) * NfamQ P Family.qle Qn
        ≤ (1 - rowR1 Family.qle P) * NfamQ P Family.qle Qn :=
      mul_le_mul_of_nonneg_right (by linarith) hN
    linarith
  · have h0 := hfr P hdes
    have h1 : (2 - ((PcertS53 : ℚ) : ℝ) + c₁ * shellRate θ Qn) * NfamQ P Family.qle Qn
        ≤ (2 - ((PcertS53 : ℚ) : ℝ) + (c₁ + c₂) * shellRate θ Qn) * NfamQ P Family.qle Qn :=
      mul_le_mul_of_nonneg_right (by linarith) hN
    linarith
  · have h1 : rowR3Proved (2 * A₀) P * NfamQ P Family.qle Qn
        ≤ (c₁ + c₂) * shellRate θ Qn * NfamQ P Family.qle Qn :=
      mul_le_mul_of_nonneg_right (by linarith) hN
    linarith
  · have h1 : rowR4 Family.qle P θ₀ * NfamQ P Family.qle Qn
        ≤ (c₁ + c₂) * shellRate θ Qn * NfamQ P Family.qle Qn :=
      mul_le_mul_of_nonneg_right (by linarith) hN
    linarith
  · have h1 : rowR5 Family.qle P θ₀ * Real.sqrt (NfamQ P Family.qle Qn)
        ≤ (c₁ + c₂) * shellRate θ Qn * Real.sqrt (NfamQ P Family.qle Qn) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    linarith

end ZetaShell.Design
