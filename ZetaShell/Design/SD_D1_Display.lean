/-
Node SD-D1 (L7_7, F1d): **the display (H1) along the new design** — at any design point with `Valid`, `8w ≤ L`,
`Qn ≥ 2`, and a per-block tail bound `θ₀ ≥ 0` with `TailInputsD` at every member, the family certificate display
`CertificateDisplay` holds with `B_tr, B_F ≥ 0`. This is `Margin.assembly_clauses_at_design_proved_of_valid`'s
display step (`Margin.lean:598–623`) on its own: H1 (`EFChi.h1_fam`, rank–trace/inertia at a free buffer, off-line
pairs handled by `ZeroBlockData.mult_two`) + H2 (`EFChi.famGramBridge_famZc`) + §7.3's pair split
(`abs_trGz_sub_trAhat_fam_le_Btr`, `sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF`). No bandwidth, no profile, no
design predicate: it applies at λ = 191/100 as it stands. Paper §3 (H1), §7.3, §9 (H2). Deps: none. Difficulty E.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

open ZetaQ ZetaQ.JoinCert ZetaQ.JoinProved

theorem display_shell (P : ParamsQ) (hP : P.Valid) (hwr : SideCondWrange P) (F : Family) (Qn : ℕ)
    (hQn : 2 ≤ Qn) (θ₀ : ℝ) (hθ : 0 ≤ θ₀)
    (hblock : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) :
    0 ≤ Btr P F Qn θ₀ ∧ 0 ≤ BF P F Qn θ₀ ∧
      CertificateDisplay (N0sFamQ P F Qn) (NfamQ P F Qn) (NIIFamQ P F Qn)
        (trGhatFam P F Qn) (frobSqGhatFam P F Qn) (Btr P F Qn θ₀) (BF P F Qn θ₀) := by
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLB : (0 : ℝ) < P.LB := EFChi.LB_pos_of_valid hP
  have ha0 : (0 : ℝ) < P.aQ := hP.aQ_pos
  have haL : (0 : ℝ) < P.aQ * P.LB := mul_pos ha0 hLB
  have hB0 : (0 : ℝ) ≤ θ₀ / (P.aQ * P.LB) := div_nonneg hθ haL.le
  have hS : (0 : ℝ) ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hBtr0 : (0 : ℝ) ≤ Btr P F Qn θ₀ := by
    show (0 : ℝ) ≤ F.sizeR Qn * θ₀ / (P.aQ * P.LB)
    exact div_nonneg (mul_nonneg hS hθ) haL.le
  have hBF0 : (0 : ℝ) ≤ BF P F Qn θ₀ := by
    show (0 : ℝ) ≤ Real.sqrt (F.sizeR Qn) * θ₀ / (P.aQ * P.LB)
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hθ) haL.le
  refine ⟨hBtr0, hBF0, ?_⟩
  exact EFChi.certificate_display_fam_of_bridge P hP F Qn θ₀ EFChi.famZc
    (EFChi.famZeroConfig_famZc F Qn hQn) (EFChi.famGramBridge_famZc P hP F Qn hQn hwr) hwr
    (abs_trGz_sub_trAhat_fam_le_Btr P F Qn θ₀ EFChi.famZc hl hblock)
    (sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF P F Qn θ₀ EFChi.famZc hl hB0 hblock)
    hBtr0 hBF0

end ZetaShell.Design
