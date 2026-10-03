/-
F1c-3c2, construction part 3 (L7_3, round 8): **the majorant property**.
Generic pieces (reusable, e.g. by K3 for the weight `1 − ℒ/s`):
* `lip2_le`: `|g′| ≤ 2 ⇒ g(s) ≤ g(y) + 2|s − y|`;
* `sSup_ball_le`, `sSup_ball_prod_le`: `sup_{|s−y|<1} g·w ≤ (g(y) + 2)·Ŵ(y)` whenever `w(s) ≤ Ŵ(y)` on the ball;
* the values of `WF` on the regions between its ramps (`WF_eq_zero_left`, `WF_eq_C`, `WF_eq_vF`, `WF_eq_CvF`),
  `WF_nonneg`, `WF_ge_of_A`; `vF_mul_le` (`vF·y ≤ (1 + 4μ²)(ℒ + 2)` once `ℒ ≤ 2(y − 1)`).
Shell-specific: the data `WS`, `FS` (ramps at `s₀ − 1 − ρ`, `log Q + 5`, `α′ℒ − 1 − ρ`; `c = (1 + 4μ²)ℒ`, `m = μℒ`),
the hypotheses `MajHyp`, and `wOut_le_WS` (`wOut(s) ≤ WS(y)` on unit balls, `y ≥ 0`), `hsupP_le_FS`.
-/
import ZetaShell.ShellK.LF_MajConstr2

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

/-! ### Generic pieces -/

theorem lip2_le {g : ℝ → ℝ} (hgd : Differentiable ℝ g) (hg' : ∀ y, |deriv g y| ≤ 2) (s y : ℝ) :
    g s ≤ g y + 2 * |s - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.univ) (x := y) (y := s)
    (fun x _ => hgd x) (fun x _ => by rw [Real.norm_eq_abs]; exact hg' x) convex_univ trivial trivial
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have := le_abs_self (g s - g y)
  linarith

theorem sSup_ball_le {h : ℝ → ℝ} {y B : ℝ} (hle : ∀ s, |s - y| < 1 → h s ≤ B) :
    sSup (h '' Metric.ball y 1) ≤ B := by
  apply csSup_le
  · exact ⟨h y, y, Metric.mem_ball_self one_pos, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    apply hle
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact hs

/-- **Generic product majorant on unit balls.** -/
theorem sSup_ball_prod_le {g w : ℝ → ℝ} (hgd : Differentiable ℝ g) (hg' : ∀ y, |deriv g y| ≤ 2)
    (hg0 : ∀ s, 0 ≤ g s) (hw0 : ∀ s, 0 ≤ w s) {y Wy : ℝ} (hW : ∀ s, |s - y| < 1 → w s ≤ Wy) :
    sSup ((fun s => g s * w s) '' Metric.ball y 1) ≤ (g y + 2) * Wy := by
  apply sSup_ball_le
  intro s hs
  have h1 := lip2_le hgd hg' s y
  have h2 : g s ≤ g y + 2 := by linarith
  exact mul_le_mul h2 (hW s hs) (hw0 s) (by linarith [hg0 y])

/-! ### `WF` on the regions between its ramps -/

section WFregions
variable {C c m ρ a₁ a₂ a₃ y : ℝ}

theorem WF_eq_zero_left (hρ : 0 < ρ) (h1 : y ≤ a₁) (h2 : y ≤ a₂) : WF C c m ρ a₁ a₂ a₃ y = 0 := by
  unfold WF; rw [rampF_zero hρ h1, rampF_zero hρ h2]; ring

theorem WF_eq_C (hρ : 0 < ρ) (h1 : a₁ + ρ ≤ y) (h2 : y ≤ a₂) : WF C c m ρ a₁ a₂ a₃ y = C := by
  unfold WF; rw [rampF_one hρ h1, rampF_zero hρ h2]; ring

theorem WF_eq_vF (hρ : 0 < ρ) (h2 : a₂ + ρ ≤ y) (h3 : y ≤ a₃) : WF C c m ρ a₁ a₂ a₃ y = vF c m y := by
  unfold WF; rw [rampF_one hρ h2, rampF_zero hρ h3]; ring

theorem WF_eq_CvF (hρ : 0 < ρ) (h2 : a₂ + ρ ≤ y) (h3 : a₃ + ρ ≤ y) :
    WF C c m ρ a₁ a₂ a₃ y = C * vF c m y := by
  unfold WF; rw [rampF_one hρ h2, rampF_one hρ h3]; ring

theorem WF_nonneg (hC : 1 ≤ C) (hc : 0 ≤ c) (hm : 0 < m) (hρ : 0 < ρ) (ha₂ : 1 ≤ a₂) :
    0 ≤ WF C c m ρ a₁ a₂ a₃ y := by
  unfold WF
  have hA0 := rampF_nonneg a₁ ρ y
  have hB0 := rampF_nonneg a₂ ρ y
  have hB1 := rampF_le_one a₂ ρ y
  have hD0 := rampF_nonneg a₃ ρ y
  have t1 : 0 ≤ C * rampF a₁ ρ y * (1 - rampF a₂ ρ y) :=
    mul_nonneg (mul_nonneg (by linarith) hA0) (by linarith)
  have hE : 0 ≤ 1 + (C - 1) * rampF a₃ ρ y := by nlinarith
  have t2 : 0 ≤ vF c m y * rampF a₂ ρ y := by
    by_cases hy : y ≤ a₂
    · rw [rampF_zero hρ hy, mul_zero]
    · exact mul_nonneg (vF_nonneg hc hm (by linarith)) hB0
  linarith [mul_nonneg t2 hE]

theorem WF_ge_of_A (hC : 1 ≤ C) (hc : 0 ≤ c) (hm : 0 < m) (hρ : 0 < ρ) (h1 : a₁ + ρ ≤ y) (hy1 : 1 ≤ y)
    {t : ℝ} (htC : t ≤ C) (htv : t ≤ vF c m y) : t ≤ WF C c m ρ a₁ a₂ a₃ y := by
  unfold WF
  rw [rampF_one hρ h1]
  have hB0 := rampF_nonneg a₂ ρ y
  have hB1 := rampF_le_one a₂ ρ y
  have hD0 := rampF_nonneg a₃ ρ y
  have hv0 := vF_nonneg hc hm hy1
  have hvB := mul_nonneg hv0 hB0
  have hE : 1 ≤ 1 + (C - 1) * rampF a₃ ρ y := by nlinarith
  have e1 : vF c m y * rampF a₂ ρ y ≤ vF c m y * rampF a₂ ρ y * (1 + (C - 1) * rampF a₃ ρ y) := by
    have := mul_le_mul_of_nonneg_left hE hvB
    linarith
  have e2 := mul_le_mul_of_nonneg_right htC (by linarith : (0:ℝ) ≤ 1 - rampF a₂ ρ y)
  have e3 := mul_le_mul_of_nonneg_right htv hB0
  nlinarith

end WFregions

/-- `vF·y ≤ (1 + 4μ²)(ℒ + 2)` once `ℒ ≤ 2(y − 1)`. -/
theorem vF_mul_le {LL μ y : ℝ} (hL : 0 < LL) (hμ : 0 < μ) (hy : LL ≤ 2 * (y - 1)) :
    vF ((1 + 4 * μ ^ 2) * LL) (μ * LL) y * y ≤ (1 + 4 * μ ^ 2) * (LL + 2) := by
  have hy1 : 1 < y := by linarith
  have hm : 0 < μ * LL := mul_pos hμ hL
  have hc : 0 ≤ (1 + 4 * μ ^ 2) * LL := by positivity
  have h1 := vF_le hc hm hy1
  have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ y)
  refine le_trans h2 ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have := mul_nonneg (by positivity : (0:ℝ) ≤ 1 + 4 * μ ^ 2) (by linarith : (0:ℝ) ≤ 2 * (y - 1) - LL)
  nlinarith

/-! ### The Shell data -/

/-- `s₁ = log Q + 4`, the lower end of the Shell zone. -/
def sOne (P : ParamsQ) : ℝ := Real.log P.Q + 4

/-- the Shell weight majorant. -/
def WS (P : ParamsQ) (μ ρ : ℝ) : ℝ → ℝ :=
  WF Cfam ((1 + 4 * μ ^ 2) * P.LL) (μ * P.LL) ρ (P.s0 - 1 - ρ) (sOne P + 1) (2497 / 1500 * P.LL - 1 - ρ)

/-- the Shell majorant `F`. -/
def FS (P : ParamsQ) (μ ρ : ℝ) : ℝ → ℝ :=
  FF P.gQ P.LB Cfam ((1 + 4 * μ ^ 2) * P.LL) (μ * P.LL) ρ (P.s0 - 1 - ρ) (sOne P + 1)
    (2497 / 1500 * P.LL - 1 - ρ)

theorem FS_eq (P : ParamsQ) (μ ρ y : ℝ) :
    FS P μ ρ y = (P.gQ y + 2 * (1 - Real.smoothTransition (y - P.LB))) * WS P μ ρ y := rfl

/-- the hypotheses on the data (all design facts, eventually true). -/
structure MajHyp (P : ParamsQ) (μ ρ : ℝ) : Prop where
  mu_pos : 0 < μ
  rho_pos : 0 < ρ
  LL_pos : 0 < P.LL
  C_ge : 1 ≤ Cfam
  s0_ge : 1 ≤ P.s0
  s0_le : P.s0 ≤ sOne P
  LL_le_C : P.LL ≤ Cfam * sOne P
  LL_le_two : P.LL ≤ 2 * (sOne P - 2)
  gap : sOne P + 1 + ρ ≤ 2497 / 1500 * P.LL - 1 - ρ

/-- **`wOut(s) ≤ WS(y)` on unit balls** (`y ≥ 0`). -/
theorem wOut_le_WS {P : ParamsQ} {μ ρ : ℝ} (h : MajHyp P μ ρ) {y s : ℝ} (hy : 0 ≤ y) (hs : |s - y| < 1) :
    wOut P s ≤ WS P μ ρ y := by
  have hsy := abs_lt.mp hs
  have hLL := h.LL_pos
  have hm : 0 < μ * P.LL := mul_pos h.mu_pos hLL
  have hc : 0 ≤ (1 + 4 * μ ^ 2) * P.LL := by positivity
  have hC0 : (0:ℝ) ≤ Cfam := by linarith [h.C_ge]
  have hs0 := h.s0_ge
  have hs0l := h.s0_le
  have hgap := h.gap
  have hL2 := h.LL_le_two
  have hLC := h.LL_le_C
  have hρ := h.rho_pos
  unfold WS
  by_cases hin : |s| ≤ P.s0
  · have e : wOut P s = 0 := by unfold wOut; rw [if_pos hin]
    rw [e]
    exact WF_nonneg h.C_ge hc hm hρ (by linarith)
  · have hs0' : P.s0 < s := by
      rcases le_or_gt 0 s with h0 | h0
      · rw [abs_of_nonneg h0] at hin; linarith
      · exfalso; apply hin; rw [abs_of_neg h0]; linarith
    have e : wOut P s = shellWt P (2497 / 1500) s := by unfold wOut; rw [if_neg hin]
    rw [e]
    unfold shellWt
    split_ifs with h1 h2
    · rw [WF_eq_C hρ (by linarith) (by unfold sOne; linarith)]
    · have hs1 : sOne P < s := by unfold sOne; linarith
      have hsp : 0 < s := by linarith
      have hy2 : P.LL ≤ 2 * (y - 1) := by linarith
      apply WF_ge_of_A h.C_ge hc hm hρ (by linarith) (by linarith)
      · rw [div_le_iff₀ hsp]
        have := mul_le_mul_of_nonneg_left hs1.le hC0
        linarith
      · have hq : P.LL ^ 2 ≤ (2 * (y - 1)) ^ 2 := pow_le_pow_left₀ hLL.le hy2 2
        have hκ : (μ * P.LL) ^ 2 ≤ 4 * μ ^ 2 * (y - 1) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hq (sq_nonneg μ)
          have e1 : (μ * P.LL) ^ 2 = μ ^ 2 * P.LL ^ 2 := by ring
          have e2 : 4 * μ ^ 2 * (y - 1) ^ 2 = μ ^ 2 * (2 * (y - 1)) ^ 2 := by ring
          rw [e1, e2]; exact this
        have hyv := vF_ge (LL := P.LL) (κ := 4 * μ ^ 2) (m := μ * P.LL) (y := y) hLL.le hm (by linarith) hκ
        refine le_trans ?_ hyv
        exact div_le_div_of_nonneg_left hLL.le (by linarith) (by linarith)
    · have hs2 : 2497 / 1500 * P.LL < s := lt_of_not_ge h2
      have hs1 : sOne P < s := by unfold sOne; linarith
      have hsp : 0 < s := by linarith
      have hy2 : P.LL ≤ 2 * (y - 1) := by linarith
      rw [WF_eq_CvF hρ (by linarith) (by linarith)]
      have hq : P.LL ^ 2 ≤ (2 * (y - 1)) ^ 2 := pow_le_pow_left₀ hLL.le hy2 2
      have hκ : (μ * P.LL) ^ 2 ≤ 4 * μ ^ 2 * (y - 1) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hq (sq_nonneg μ)
        have e1 : (μ * P.LL) ^ 2 = μ ^ 2 * P.LL ^ 2 := by ring
        have e2 : 4 * μ ^ 2 * (y - 1) ^ 2 = μ ^ 2 * (2 * (y - 1)) ^ 2 := by ring
        rw [e1, e2]; exact this
      have hyv := vF_ge (LL := P.LL) (κ := 4 * μ ^ 2) (m := μ * P.LL) (y := y) hLL.le hm (by linarith) hκ
      have h3 : P.LL / s ≤ P.LL / (y - 1) := div_le_div_of_nonneg_left hLL.le (by linarith) (by linarith)
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (le_trans h3 hyv) hC0

theorem WS_nonneg {P : ParamsQ} {μ ρ : ℝ} (h : MajHyp P μ ρ) (y : ℝ) : 0 ≤ WS P μ ρ y := by
  have hm : 0 < μ * P.LL := mul_pos h.mu_pos h.LL_pos
  have hc : 0 ≤ (1 + 4 * μ ^ 2) * P.LL := by have := h.LL_pos; positivity
  have := h.s0_ge
  have := h.s0_le
  exact WF_nonneg h.C_ge hc hm h.rho_pos (by linarith)

/-- **The majorant property.** -/
theorem hsupP_le_FS {P : ParamsQ} (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {μ ρ : ℝ} (h : MajHyp P μ ρ)
    {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ P.LB) : hsupP P y ≤ FS P μ ρ y := by
  obtain ⟨hgd, -, hg'⟩ := gQ_deriv_facts P hP hw
  have hst : Real.smoothTransition (y - P.LB) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [FS_eq, hst, sub_zero, mul_one]
  exact sSup_ball_prod_le hgd hg' (fun s => hP.gQ_nonneg hw s) (fun s => (wOut_nonneg_le hP s).1)
    (fun s hs => wOut_le_WS h hy0 hs)

theorem FS_nonneg {P : ParamsQ} (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {μ ρ : ℝ} (h : MajHyp P μ ρ) (y : ℝ) :
    0 ≤ FS P μ ρ y := by
  rw [FS_eq]
  have := Real.smoothTransition.le_one (y - P.LB)
  exact mul_nonneg (by linarith [hP.gQ_nonneg hw y]) (WS_nonneg h y)

theorem FS_zero {P : ParamsQ} (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (μ ρ : ℝ) {y : ℝ} (hy : P.LB + 2 ≤ y) :
    FS P μ ρ y = 0 := by
  have hLB : 0 ≤ P.LB := by linarith [hP.one_le_w]
  rw [FS_eq, hP.gQ_eq_zero hw (by rw [abs_of_nonneg (by linarith)]; linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  ring

end F1c
end ShellK
end ZetaShell
