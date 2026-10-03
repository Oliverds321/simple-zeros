/-
L7_1c (round 2, cloud, 3 Oct 2026): **the Shell frame without `PNTErrorTerm` and without the certificate
hypothesis.** `shell_frame_qle_of_K_noP` is L7_3's `ShellK/LF_Frame.shell_frame_qle_of_K` with two changes and
nothing else:
- the Frobenius row is taken from L7_10's `ShellK.frob_row_shell_of_K` (hypothesis `ZeroDensityInput` only) instead
  of its wrapper `ShellK.frob_row_shell'`, whose `hP : PNTErrorTerm` and `hcert : CertS53` are not used (its proof
  is `frob_row_shell_of_K hD …`); `hP` was consumed nowhere else in `shell_frame_qle_of_K`;
- the profile's L75 side conditions are the theorem `S53L75_L75` (Track R, level A) instead of `hcert.2.2.2.2.1`.
The medium PNT (`ZetaShell.PNT.PNTMedium`, a theorem) is used below `frob_row_shell_of_K`, through Theorem K's
killed zone (`K3_killed` ← `K3b_integrated` ← `normA2_lower` ← `theta_pnt`).
The original `shell_frame_qle_of_K` (with `hP`, `hcert`) is kept unchanged in `ShellK/LF_Frame`.
-/
import ZetaShell.ShellK.LF_Frame
import ZetaShell.Cert.R5_ProfileL75

namespace ZetaShell.Design

open ZetaQ ZetaQ.JoinCert ZetaQ.JoinProved Filter

/-- **The Shell frame for `1 < q ≤ Q` at S53-L75**, hypothesis `ZeroDensityInput` only: `shell_frame_qle_of_K`
(L7_1's F1 statement, `shell_frame_qle`) without `hP : PNTErrorTerm` and `hcert : CertS53`. -/
theorem shell_frame_qle_of_K_noP (hD : ZeroDensityInput)
    (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    Nonempty (ShellFrame ZetaQ.Family.qle r ε S53L75 (2 - ((PcertS53 : ℚ) : ℝ)) (shellRate θ)) := by
  have hL : S53L75.L75 := S53L75_L75
  have hθ1 : θ < 1 := by linarith
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 2 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 2 * A₀) hloc
  obtain ⟨c₁, hc₁, hfrob⟩ := ZetaShell.ShellK.frob_row_shell_of_K hD r ε θ hr hε hθ hθ'
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
