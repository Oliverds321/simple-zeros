/-
Node SD-B6 (L7_7, F1b): **the tail (paper §7) along the Shell design**: a per-block perturbation bound `θ₀` with
`TailInputsD` at every member of the family (what the display H1 consumes) and the target `θ₀ ≤ A₀e^{−m}/L`,
`m = ½ log T` (what the pair rows consume). Copy of the chain `Margin.theta0Fam_le_of_designM_A0` (`Margin.lean:261`)
+ `Margin.tail_clauses_at_design_of_closing_A0_certM` (`Margin.lean:481`, θ₀ := `theta0Fam …`), with `hdes` the Shell's:
the chain reads `Valid`, `P.Q`, `wrange`, `w = 1`, `ℒ ≤ L` (λ ≥ 1), `ClosingAtDesignM`, `ϱ = ϱ₂`; the Gevrey
constant `B′` enters only `CenvDesign` on both sides of the closing equality (no numeric gate).
Paper §7.1–7.3; L7_2 I9, L7_4 1c (`wD₀ = 1.529λ²ℒ²(1+o(1))`, all admissibility conditions eventual for r ≥ 3).
The pair clause `hpair` of ZetaQ (against `κ_cert + r₂`) is NOT stated: the Shell frame consumes `rowR4`, `rowR5`
directly (SD-B8). Deps: SD-A8; `HPre.hpre_of_closing`, `theta0Q_le_of_closing`, `famTailInputsD_at`, `theta0Fam_nonneg`.
Difficulty M. PROVED (the three ZetaQ lemmas are design-free; the copy replaces only `LB_ge_LL_of_designM` and
`w_eq_one_of_designM` by SD-A8).
-/
import ZetaShell.Design.SD_A8_Scales

namespace ZetaShell.Design

open ZetaQ ZetaQ.JoinCert ZetaQ.JoinProved Filter

theorem tail_shell_eventually (r ε : ℝ) (hr : 3 ≤ r) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧ θ₀ ≤ A₀ * Real.exp (-marginDesign P) / P.LB ∧
        (∀ q ∈ Family.qle.moduli Qn, ∀ χ ∈ primitiveChars q,
          Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have hu : ∀ᶠ Qn : ℕ in atTop, (100 + 8 * A₀ : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hu, eventually_ge_atTop 2] with Qn hu hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hQn1 : 1 ≤ Qn := by omega
  have hS : (1 : ℝ) ≤ ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  obtain ⟨-, hLLu, hLLLB, hw1⟩ := scales_of_shellDesignM hS hdes hr hQn1
  have hLL : (100 : ℝ) ≤ P.LL := by linarith
  have hLB : (100 : ℝ) ≤ P.LB := le_trans hLL hLLLB
  have hA₀L : 8 * A₀ ≤ P.LB := by linarith
  have hwe : P.w = 1 := hw1 (by linarith)
  have hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.1]; exact gevreyProfile_rhoTwoQ
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hCenv0 : (0 : ℝ) ≤ CenvDesign P :=
    mul_nonneg (Real.exp_pos (2 : ℝ)).le (le_trans hLB0.le (le_max_right _ _))
  have hθ0 := theta0Fam_nonneg P A₀ (CenvDesign P) (Qn : ℝ) hP hwr hA₀ hCenv0
    (by exact_mod_cast hQn1)
  refine ⟨_, hθ0, ?_, famTailInputsD_at Family.qle Qn P A₀ hQn hP hwr hϱ hA₀ hloc⟩
  -- `hpre` at `A₀` (copy of `Margin.hpre_of_designM` / `hpre_of_designM_A0`)
  have hcl : ClosingAtDesignM P := hdes.2.2.2.2.2.2.2.2.2.1
  obtain ⟨h0, h1⟩ := HPre.hpre_of_closing Qn P 1 hP hdes.2.1 hdes.2.2.2.2.2.2.2.1 hwe hLL hLB
    (closingCondition_of_closingAtDesignM P hP hcl) le_rfl (by linarith)
  have e : prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
      = A₀ * prefactorQ P.toParams P.T 1 gevreyA (CenvDesign P) P.D0 (Qn : ℝ) := by
    unfold prefactorQ; ring
  have hA₀0 : 0 < A₀ := by linarith
  have hpre0 : 0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) := by
    rw [e]; positivity
  have hpre : Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
      ≤ logPrefactorGev P + Real.log A₀ := by
    rw [e, Real.log_mul (ne_of_gt hA₀0) (ne_of_gt h0)]
    linarith
  -- `θ₀_fam ≤ A₀ e^{−m}/L` (copy of `Margin.theta0Fam_le_of_designM_A0`)
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hww : P.toParams.w = P.w := rfl
  have hw : (0 : ℝ) < P.w := EFChi.w_pos_of_valid hP
  have hL0 : (0 : ℝ) < P.toParams.L P.T := by rw [hLb]; exact hLB0
  have hA : (0 : ℝ) < gevreyA := by unfold gevreyA; positivity
  have hD0 : (0 : ℝ) ≤ P.D0 := by linarith [one_le_D0Q hP]
  have hη0 : (0 : ℝ) < A₀ * Real.exp (-marginDesign P) := by positivity
  have hcc : P.LB / 2 + (logPrefactorGev P + marginDesign P) + Real.log (P.LB / 1)
      ≤ c4 * Real.sqrt (P.w * P.D0 / gevreyA) := hcl.1
  have hc4 : c4 = 4 / Real.exp 1 := rfl
  rw [hc4, div_one] at hcc
  have hlogdiv : Real.log (P.LB / (A₀ * Real.exp (-marginDesign P)))
      = Real.log P.LB - Real.log A₀ + marginDesign P := by
    rw [Real.log_div (ne_of_gt hLB0) (ne_of_gt hη0),
      Real.log_mul (ne_of_gt hA₀0) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hclose : P.toParams.L P.T / 2
        + Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        + Real.log (P.toParams.L P.T / (A₀ * Real.exp (-marginDesign P)))
      ≤ (4 / Real.exp 1) * Real.sqrt (P.toParams.w * P.D0 / gevreyA) := by
    rw [hLb, hww, hlogdiv]
    linarith
  have h := theta0Q_le_of_closing (η := A₀ * Real.exp (-marginDesign P)) hL0 hη0 hw hA hD0
    hpre0 hclose
  rw [hLb] at h
  exact h

end ZetaShell.Design
