/-
F1c-3c2, construction part 5 (L7_3, round 8): **the eventual assembly** `majorant_excess_proof`, with the
statement of `majorant_excess` (LF_Majorant) verbatim.
Constants (fixed per `η`, `η₁ = min η 1`): `μ = η₁/1000`, `θ = μη₁/3000`, `ρ = θℒ`, `V₀ = (1 + 4μ²)/(2μ)`,
`W = C(1 + V₀)`, `R = 2CS/θ + C(1 + 4μ²)/μ² + 2CV₀S/θ` (`S = sup|smoothTransition′|`), `M = (1 + S)W + 2aR + 1`.
With `Z = aL²ℒ`: ramps `≤ 12θW·Z + 16W·aL²`, plateau/stretches `≤ 8Cμ²·Z + 84C·aL²`, Abel `≤ 8Cab((1+S)W + 1 + R)·aL²`,
so the excess is `≤ (3η₁/8)·Z ≤ η₁·ℒ(aL)²/2` once `ℒ ≥ 8(16W + 84C + 8Cab((1+S)W + 1 + R))/η₁`.
-/
import ZetaShell.ShellK.LF_MajConstr4
import ZetaShell.ShellK.LF_KernelWin
import ZetaShell.ShellK.LF_Small

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

theorem Cfam_le_six : Cfam ≤ 6 := by
  unfold Cfam
  have h1 := Real.pi_lt_d2
  have hp : Real.pi ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ Real.pi_pos.le h1.le 4
  rw [div_le_iff₀ (by norm_num)]
  norm_num at hp ⊢
  linarith

theorem Cfam_ge_two : (2 : ℝ) ≤ Cfam := by
  have : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) this.le 4
  unfold Cfam; rw [le_div_iff₀ (by norm_num)]; linarith

set_option maxHeartbeats 1000000 in
/-- **F1c-3c2, proved.** Same statement as `majorant_excess`. -/
theorem majorant_excess_proof (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (Cab : ℝ) (hCab : 0 ≤ Cab) (η : ℝ)
    (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∃ F : ℝ → ℝ, ∃ M : ℝ, 0 < M ∧ Differentiable ℝ F ∧ Continuous (deriv F) ∧
        (∀ y, |deriv F y| ≤ 2 * M) ∧ (∀ y, P.LB + 2 ≤ y → F y = 0) ∧ (∀ y, 0 ≤ F y) ∧
        (∀ y, 0 ≤ y → y ≤ P.LB → hsupP P y ≤ F y) ∧
        (∫ y in (0 : ℝ)..(P.LB + 2), F y * y) + M * (Cab * (P.LB + 2) ^ 2)
          ≤ (∫ y in P.s0..P.LB, P.gQ y * wOut P y * y) + η * (P.LL * (P.aQ * P.LB) ^ 2 / 2) := by
  obtain ⟨S, hS0, hS⟩ := st_deriv_bound
  have hC2 := Cfam_ge_two
  have hC6 := Cfam_le_six
  have hC0 : (0:ℝ) ≤ Cfam := by linarith
  have hC1 : (1:ℝ) ≤ Cfam := by linarith
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : ℝ, η₁ = min η 1 := ⟨_, rfl⟩
  have hη₁0 : 0 < η₁ := by rw [hη₁]; exact lt_min hη one_pos
  have hη₁1 : η₁ ≤ 1 := by rw [hη₁]; exact min_le_right _ _
  have hη₁η : η₁ ≤ η := by rw [hη₁]; exact min_le_left _ _
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = η₁ / 1000 := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hμ1 : μ ≤ 1 := by rw [hμ]; linarith
  have hμ2 : μ ^ 2 ≤ 1 := by nlinarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = μ * η₁ / 3000 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 / 3000 := by
    rw [hθ]
    have : μ * η₁ ≤ 1 * 1 := mul_le_mul hμ1 hη₁1 hη₁0.le (by norm_num)
    linarith
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : ℝ, V₀ = (1 + 4 * μ ^ 2) / (2 * μ) := ⟨_, rfl⟩
  have hV₀0 : 0 ≤ V₀ := by rw [hV₀]; positivity
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = Cfam + Cfam * V₀ := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ,
      R = 2 * Cfam * S / θ + Cfam * (1 + 4 * μ ^ 2) / μ ^ 2 + 2 * Cfam * V₀ * S / θ := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 16 * W + 84 * Cfam + 8 * Cab * ((1 + S) * W + 1 + R) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  obtain ⟨Kth, hKth⟩ : ∃ K : ℝ, K = max (2 * Real.pi * Real.exp 4) (max 30 (8 * E / η₁)) := ⟨_, rfl⟩
  have hKpi : 2 * Real.pi * Real.exp 4 ≤ Kth := by rw [hKth]; exact le_max_left _ _
  have hK30 : 30 ≤ Kth := by rw [hKth]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKE : 8 * E / η₁ ≤ Kth := by rw [hKth]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- the constant inequalities
  have hμW : μ * W ≤ 21 := by
    have e : μ * W = Cfam * μ + Cfam * (1 + 4 * μ ^ 2) / 2 := by
      rw [hW, hV₀]; field_simp; try ring
    rw [e]
    have t1 : Cfam * μ ≤ 6 * 1 := mul_le_mul hC6 hμ1 hμ0.le (by norm_num)
    have t2 : Cfam * (1 + 4 * μ ^ 2) ≤ 6 * 5 := mul_le_mul hC6 (by linarith) (by positivity) (by norm_num)
    linarith
  have hθW : 12 * θ * W ≤ η₁ / 8 := by
    have e : 12 * θ * W = 12 * η₁ / 3000 * (μ * W) := by rw [hθ]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hμW (by positivity : (0:ℝ) ≤ 12 * η₁ / 3000)
    linarith
  have hCμ : 8 * Cfam * μ ^ 2 ≤ η₁ / 8 := by
    have e : μ ^ 2 = η₁ * η₁ / 1000000 := by rw [hμ]; ring
    have h1 : η₁ * η₁ ≤ η₁ * 1 := mul_le_mul_of_nonneg_left hη₁1 hη₁0.le
    have h2 : 8 * Cfam * μ ^ 2 ≤ 48 * μ ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg μ)
    rw [e] at h2 ⊢
    linarith
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  have hK1 : (1 : ℝ) ≤ Kth := by linarith
  filter_upwards [one_sub_zoneFactor_shell r ε hr hε (1 / 2) (by norm_num),
    Design.shellDesign_regime S53L75 hS2 r ε hr hε Kth hK1] with Qn hz hreg
  intro P hdes
  have hP : P.Valid := hdes.1
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  obtain ⟨ha0', h1a, h1a2⟩ := hz P hdes
  obtain ⟨hKlog, -, -, hLL2, -, -, -, -⟩ := hreg P hdes
  have hlam : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
  have hlam1 : (1 : ℝ) ≤ P.lam := by rw [hlam]; norm_num [S53L75]
  have hlam2 : P.lam < 2 := hP.lam_lt_two
  have hQpos : 0 < P.Q := by linarith [hP.Q_ge]
  have hT : 0 < P.T := hP.T_pos
  have hLL : 0 < P.LL := hP.LL_pos
  have hLLne : P.LL ≠ 0 := hLL.ne'
  have hsplit : P.LL = Real.log P.Q + Real.log (P.T / (2 * Real.pi)) := by
    unfold ParamsQ.LL
    rw [mul_div_assoc, Real.log_mul hQpos.ne' (by positivity)]
  have hTK : Kth ≤ P.T := (hreg P hdes).2.1
  have hl4 : 4 ≤ Real.log (P.T / (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith
  have hlogQ : Real.log P.Q = Real.log (Qn : ℝ) := by rw [hQ]
  have hlQK : Kth ≤ Real.log P.Q := by rw [hlogQ]; exact hKlog
  have hb1 : Real.log P.Q + 4 ≤ P.LL := by linarith
  have hlQ1 : 1 ≤ Real.log P.Q := by linarith
  have hLK : Kth ≤ P.LL := by linarith
  have hL30 : 30 ≤ P.LL := by linarith
  have hbC : P.LL ≤ Cfam * (Real.log P.Q + 4) := by
    have hl2 : P.LL ≤ 2 * Real.log P.Q := by rw [hlogQ]; exact hLL2
    have := mul_le_mul_of_nonneg_right hC2 (by linarith : (0:ℝ) ≤ Real.log P.Q + 4)
    linarith
  have hLLtwo : P.LL ≤ 2 * (sOne P - 2) := by
    have hl2 : P.LL ≤ 2 * Real.log P.Q := by rw [hlogQ]; exact hLL2
    show P.LL ≤ 2 * (Real.log P.Q + 4 - 2)
    linarith
  -- `s₀`
  have hs0z : P.s0 = zoneFactor P * P.LL := s0_eq_zoneFactor P hP
  have hs0ge : P.LL / 2 ≤ P.s0 := by
    rw [hs0z]
    have := mul_le_mul_of_nonneg_right (show (1:ℝ) / 2 ≤ zoneFactor P by linarith) hLL.le
    linarith
  have hδ : 0 ≤ P.deltaPrime := by
    show 0 ≤ 3 * Real.log (Real.log P.Q) / Real.log P.Q
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hlQ1)) (by linarith)
  have hs0le : P.s0 ≤ Real.log P.Q := by
    show (1 - P.deltaPrime) * Real.log P.Q ≤ Real.log P.Q
    have := mul_nonneg hδ (by linarith : (0:ℝ) ≤ Real.log P.Q)
    linarith
  have hLB : P.LB = P.lam * P.LL := rfl
  have hLLB : P.LL ≤ P.LB := by
    rw [hLB]; have := mul_le_mul_of_nonneg_right hlam1 hLL.le; linarith
  have hLB2 : P.LB ≤ 2 * P.LL := by
    rw [hLB]; exact mul_le_mul_of_nonneg_right hlam2.le hLL.le
  have hs0L : P.s0 ≤ P.LB := by linarith
  have ha : (3:ℝ) / 4 ≤ P.aQ := hP.a_ge
  have ha0 : 0 ≤ P.aQ := by linarith
  have hLB0 : 0 ≤ P.LB := by linarith
  -- the hypotheses of the construction
  set ρ := θ * P.LL with hρdef
  have hρ0 : 0 < ρ := mul_pos hθ0 hLL
  have hρle : ρ ≤ P.LL / 3000 := by
    rw [hρdef]; have := mul_le_mul_of_nonneg_right hθ1 hLL.le; linarith
  have hMH : MajHyp P μ ρ :=
    { mu_pos := hμ0, rho_pos := hρ0, LL_pos := hLL, C_ge := hC1,
      s0_ge := by linarith,
      s0_le := by show P.s0 ≤ Real.log P.Q + 4; linarith,
      LL_le_C := by show P.LL ≤ Cfam * (Real.log P.Q + 4); exact hbC,
      LL_le_two := hLLtwo,
      gap := by show Real.log P.Q + 4 + 1 + ρ ≤ 2497 / 1500 * P.LL - 1 - ρ; linarith }
  obtain ⟨hgd, hgc, hg'⟩ := gQ_deriv_facts P hP hw
  have hgC1 : ContDiff ℝ 1 P.gQ := contDiff_one_iff_deriv.mpr ⟨hgd, hgc⟩
  have hm : 0 < μ * P.LL := mul_pos hμ0 hLL
  have hc : 0 ≤ (1 + 4 * μ ^ 2) * P.LL := by positivity
  have hFC : ContDiff ℝ 1 (FS P μ ρ) := FF_contDiff hgC1 hm
  -- the rewriting of the constants
  have hWe : Cfam + Cfam * ((1 + 4 * μ ^ 2) * P.LL / (2 * (μ * P.LL))) = W := by
    rw [hW, hV₀]; field_simp; try ring
  have hX : 2 * Cfam * S / ρ + Cfam * ((1 + 4 * μ ^ 2) * P.LL / (μ * P.LL) ^ 2)
      + 2 * Cfam * ((1 + 4 * μ ^ 2) * P.LL / (2 * (μ * P.LL))) * S / ρ = R / P.LL := by
    rw [hρdef, hR, hV₀]; field_simp; try ring
  -- `M`
  set M := (1 + S) * W + 2 * P.aQ * R + 1 with hMdef
  have hM0 : 0 < M := by rw [hMdef]; positivity
  refine ⟨FS P μ ρ, M, hM0, hFC.differentiable one_ne_zero, hFC.continuous_deriv le_rfl, ?_,
    fun y hy => FS_zero hP hw μ ρ hy, FS_nonneg hP hw hMH, fun y hy0 hyL => hsupP_le_FS hP hw hMH hy0 hyL, ?_⟩
  · -- the derivative bound
    intro y
    have hd := FF_deriv_abs_le (L := P.LB) (a₁ := P.s0 - 1 - ρ) (a₂ := sOne P + 1)
      (a₃ := 2497 / 1500 * P.LL - 1 - ρ) hgd hg' (fun y => hP.gQ_nonneg hw y) (fun y => hP.gQ_le_aL hw y)
      hC1 hc hm hρ0 hS y
    change |deriv (FS P μ ρ) y| ≤ _ at hd
    rw [hX, hWe] at hd
    have hq1 : P.aQ * P.LB + 2 ≤ 4 * P.aQ * P.LL := by
      have t1 := mul_le_mul_of_nonneg_left hLB2 ha0
      have t2 : (3:ℝ) / 4 * 30 ≤ P.aQ * P.LL := mul_le_mul ha hL30 (by norm_num) ha0
      linarith
    have hq : (P.aQ * P.LB + 2) * (R / P.LL) ≤ 4 * P.aQ * R := by
      rw [mul_div_assoc', div_le_iff₀ hLL]
      have := mul_le_mul_of_nonneg_right hq1 hR0
      linarith
    show |deriv (FS P μ ρ) y| ≤ 2 * M
    rw [hMdef]
    have hW2 : (2 + 2 * S) * W = 2 * ((1 + S) * W) := by ring
    linarith
  · -- the integral inequality
    have hI := FS_integral_le hP hw hMH hs0L
    set Z := P.aQ * P.LB ^ 2 * P.LL with hZ
    have haL2 : 2 ≤ P.aQ * P.LB := by
      have := mul_le_mul ha (show (30:ℝ) ≤ P.LB by linarith) (by norm_num) ha0
      linarith
    have hL22 : P.LB + 2 ≤ 2 * P.LB := by linarith
    -- (P1) the ramps
    have hK1W : K1S P μ = (P.aQ * P.LB + 2) * W * (P.LB + 2) := by
      unfold K1S WmaxS; rw [hWe]
    have P1 : K1S P μ * (3 * ρ + 4) ≤ 12 * θ * W * Z + 16 * W * (P.aQ * P.LB ^ 2) := by
      rw [hK1W]
      have a1 : (P.aQ * P.LB + 2) * W * (P.LB + 2) ≤ (2 * (P.aQ * P.LB)) * W * (2 * P.LB) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hW0) hL22 (by positivity) (by positivity)
      have a2 := mul_le_mul_of_nonneg_right a1 (by positivity : (0:ℝ) ≤ 3 * ρ + 4)
      have e : (2 * (P.aQ * P.LB)) * W * (2 * P.LB) * (3 * ρ + 4)
          = 12 * θ * W * Z + 16 * W * (P.aQ * P.LB ^ 2) := by rw [hZ, hρdef]; ring
      linarith
    -- (P2) the plateau and the `ℒ/s`, `Cℒ/s` stretches
    have v1 : VbS P μ - P.LL ≤ 4 * μ ^ 2 * P.LL + 10 := by unfold VbS; linarith
    have v2 : VbS P μ ≤ 5 * P.LL + 10 := by
      unfold VbS
      have := mul_le_mul_of_nonneg_right hμ2 hLL.le
      linarith
    have hVb : P.LL ≤ VbS P μ := by
      unfold VbS; have := mul_nonneg (sq_nonneg μ) hLL.le; have := sq_nonneg μ; linarith
    have k1 : K2S P μ ≤ 4 * Cfam * μ ^ 2 * (P.aQ * P.LB) * P.LL + 42 * Cfam * (P.aQ * P.LB) := by
      unfold K2S
      have t1 := mul_le_mul_of_nonneg_left v1 (by positivity : (0:ℝ) ≤ P.aQ * P.LB)
      have t2 : P.aQ * P.LB * (VbS P μ - P.LL) + 2 * VbS P μ
          ≤ P.aQ * P.LB * (4 * μ ^ 2 * P.LL + 10) + (10 * P.LL + 20) := by linarith
      have t3 := mul_le_mul_of_nonneg_left t2 hC0
      have t4 : 10 * P.LL + 20 + 2 * (P.LB + 2) ≤ 32 * (P.aQ * P.LB) := by
        have := mul_le_mul_of_nonneg_right ha hLB0
        linarith
      have t5 := mul_le_mul_of_nonneg_left t4 hC0
      linarith
    have hK20 : 0 ≤ K2S P μ := by
      unfold K2S
      have : 0 ≤ P.aQ * P.LB * (VbS P μ - P.LL) + 2 * VbS P μ :=
        add_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
      positivity
    have P2 : K2S P μ * (P.LB + 2) ≤ 8 * Cfam * μ ^ 2 * Z + 84 * Cfam * (P.aQ * P.LB ^ 2) := by
      have a1 := mul_le_mul k1 hL22 (by positivity) (le_trans hK20 k1)
      have e : (4 * Cfam * μ ^ 2 * (P.aQ * P.LB) * P.LL + 42 * Cfam * (P.aQ * P.LB)) * (2 * P.LB)
          = 8 * Cfam * μ ^ 2 * Z + 84 * Cfam * (P.aQ * P.LB ^ 2) := by rw [hZ]; ring
      linarith
    -- (P3) the Abel error
    have P3 : M * (Cab * (P.LB + 2) ^ 2) ≤ 8 * Cab * ((1 + S) * W + 1 + R) * (P.aQ * P.LB ^ 2) := by
      have q1 : (P.LB + 2) ^ 2 ≤ 4 * P.LB ^ 2 := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ P.LB - 2) (by linarith : (0:ℝ) ≤ 3 * P.LB + 2)
        linarith
      have q2 : P.LB ^ 2 ≤ 2 * (P.aQ * P.LB ^ 2) := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * P.aQ - 1) (sq_nonneg P.LB)
        linarith
      have hMC : 0 ≤ M * Cab := mul_nonneg hM0.le hCab
      have r1 := mul_le_mul_of_nonneg_left q1 hMC
      have r2 := mul_le_mul_of_nonneg_left q2
        (by positivity : (0:ℝ) ≤ 4 * Cab * ((1 + S) * W + 1))
      have e : M * Cab * (4 * P.LB ^ 2)
          = 4 * Cab * ((1 + S) * W + 1) * P.LB ^ 2 + 8 * Cab * R * (P.aQ * P.LB ^ 2) := by
        rw [hMdef]; ring
      have e2 : M * (Cab * (P.LB + 2) ^ 2) = M * Cab * (P.LB + 2) ^ 2 := by ring
      rw [e2]
      linarith
    -- the budget
    have hEℓ : E ≤ η₁ * P.LL / 8 := by
      have := le_trans hKE hLK
      rw [div_le_iff₀ hη₁0] at this
      linarith
    have haL0 : 0 ≤ P.aQ * P.LB ^ 2 := by positivity
    have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
    have b1 := mul_le_mul_of_nonneg_right hθW hZ0
    have b2 := mul_le_mul_of_nonneg_right hCμ hZ0
    have b3 := mul_le_mul_of_nonneg_right hEℓ haL0
    have eE : 16 * W * (P.aQ * P.LB ^ 2) + 84 * Cfam * (P.aQ * P.LB ^ 2)
        + 8 * Cab * ((1 + S) * W + 1 + R) * (P.aQ * P.LB ^ 2) = E * (P.aQ * P.LB ^ 2) := by rw [hE]; ring
    have eZ : η₁ * P.LL / 8 * (P.aQ * P.LB ^ 2) = η₁ / 8 * Z := by rw [hZ]; ring
    have htot : K1S P μ * (3 * ρ + 4) + K2S P μ * (P.LB + 2) + M * (Cab * (P.LB + 2) ^ 2)
        ≤ 3 * η₁ / 8 * Z := by linarith
    have hfin : 3 * η₁ / 8 * Z ≤ η * (P.LL * (P.aQ * P.LB) ^ 2 / 2) := by
      have e : P.LL * (P.aQ * P.LB) ^ 2 / 2 = P.aQ * Z / 2 := by rw [hZ]; ring
      rw [e]
      have h1 : 3 * η₁ / 8 * Z ≤ η₁ * (P.aQ * Z / 2) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha hZ0) (by positivity : (0:ℝ) ≤ η₁ / 2)
        linarith
      have h2 : η₁ * (P.aQ * Z / 2) ≤ η * (P.aQ * Z / 2) :=
        mul_le_mul_of_nonneg_right hη₁η (by positivity)
      linarith
    linarith

end F1c
end ShellK
end ZetaShell
