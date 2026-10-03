/-
F1c-3c split (L7_3, round 7). `smooth_majorant` = the kernel identity (F1c-3c1, `kernel_window`, PROVED here from
`kernel_window_at`) + the majorant construction (F1c-3c2, `majorant_excess`, OPEN).
* `kernel_window`: eventually along the Shell design, `∫_{s₀}^{L} g·wOut·y ≤ (ℒ(aL)²/2)·KoutShell(a)`, with the design
  facts `0 ≤ a ≤ 1` (`one_sub_zoneFactor_shell`), `log Q + 4 ≤ ℒ` (`ℒ = log Q + log(T/2π)`, `T ≥ 2πe⁴`),
  `ℒ ≤ C(log Q + 4)` (`ℒ ≤ 2 log Q`, A7) and `α′ ≤ λ = 1.91`.
* `majorant_excess` (PROVED round 8 as `majorant_excess_proof`, LF_MajConstr5; construction LF_MajConstr1–4): a `C¹` majorant `F ≥ hsupP` on `[0, L]`, `F = 0` beyond `L + 2`, `|F′| ≤ 2M`, whose window
  integral plus the Abel error exceeds the exact main term `∫_{s₀}^{L} g·wOut·y` by at most `η·ℒ(aL)²/2`.
  Orders (report R7.1): main term `≍ ℒ³`; ramps of width `ℒ^{1/2}` at the jumps of `wOut` (heights `≍ ℒ`) give
  `M ≍ ℒ^{1/2}`, Abel error `M·Cab·(L+2)² ≍ ℒ^{5/2}`, ramp cost `≍ ℒ^{5/2}`; near `L` the window is on its taper ramp,
  `g(L − u) ≤ u`, so `hsupP ≤ C` on `[L − 1, L]` and the fall to `0` on `[L, L + 2]` costs a slope `O(1)`. So the
  cutoff `L + 2` is compatible with `M = o(ℒ)`, and the statement is kept as it stands.
-/
import ZetaShell.ShellK.LF_KernelWin
import ZetaShell.ShellK.LF_Small
import ZetaShell.ShellK.LF_MajConstr5

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

/-- **F1c-3c1.** The kernel identity, eventually along the Shell design. -/
theorem kernel_window (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (∫ y in P.s0..P.LB, P.gQ y * wOut P y * y)
        ≤ P.LL * (P.aQ * P.LB) ^ 2 / 2 * KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) := by
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  have hK1 : (1 : ℝ) ≤ 2 * Real.pi * Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    have := Real.pi_gt_three
    nlinarith
  filter_upwards [one_sub_zoneFactor_shell r ε hr hε 1 one_pos,
    Design.shellDesign_regime S53L75 hS2 r ε hr hε (2 * Real.pi * Real.exp 4) hK1,
    eventually_ge_atTop 3] with Qn hz hreg hQn3
  intro P hdes
  have hP : P.Valid := hdes.1
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  obtain ⟨ha0, h1a, -⟩ := hz P hdes
  obtain ⟨-, hTK, -, hLL2, -, -, -, -⟩ := hreg P hdes
  have hlam : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
  have hlam' : (2497 : ℝ) / 1500 ≤ P.lam := by rw [hlam]; norm_num [S53L75]
  have hQpos : 0 < P.Q := by linarith [hP.Q_ge]
  have hT : 0 < P.T := hP.T_pos
  have hsplit : P.LL = Real.log P.Q + Real.log (P.T / (2 * Real.pi)) := by
    unfold ParamsQ.LL
    rw [mul_div_assoc, Real.log_mul hQpos.ne' (by positivity)]
  have hl4 : 4 ≤ Real.log (P.T / (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith
  have hb1 : Real.log P.Q + 4 ≤ P.LL := by linarith
  have hlogQ0 : 0 ≤ Real.log P.Q := Real.log_nonneg (by linarith [hP.Q_ge])
  have hC2 : (2 : ℝ) ≤ Cfam := by
    have : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) this.le 4
    unfold Cfam; rw [le_div_iff₀ (by norm_num)]; linarith
  have hbC : P.LL ≤ Cfam * (Real.log P.Q + 4) := by
    have hlogQn : 0 ≤ Real.log (Qn : ℝ) := Real.log_natCast_nonneg Qn
    rw [hQ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hlogQn]
  exact kernel_window_at P hP hw ha0 (by linarith) hb1 hbC hlam'

/-- **F1c-3c2 (PROVED, round 8, `LF_MajConstr*.lean`).** The `C¹` majorant and its excess over the exact main term. -/
theorem majorant_excess (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (Cab : ℝ) (hCab : 0 ≤ Cab) (η : ℝ)
    (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∃ F : ℝ → ℝ, ∃ M : ℝ, 0 < M ∧ Differentiable ℝ F ∧ Continuous (deriv F) ∧
        (∀ y, |deriv F y| ≤ 2 * M) ∧ (∀ y, P.LB + 2 ≤ y → F y = 0) ∧ (∀ y, 0 ≤ F y) ∧
        (∀ y, 0 ≤ y → y ≤ P.LB → hsupP P y ≤ F y) ∧
        (∫ y in (0 : ℝ)..(P.LB + 2), F y * y) + M * (Cab * (P.LB + 2) ^ 2)
          ≤ (∫ y in P.s0..P.LB, P.gQ y * wOut P y * y) + η * (P.LL * (P.aQ * P.LB) ^ 2 / 2) :=
  majorant_excess_proof r ε hr hε Cab hCab η hη

end F1c
end ShellK
end ZetaShell
