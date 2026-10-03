/-
L10c_Scales (L7_10c, 3 Oct 2026): the scales of a Shell design S53-L75 used by `KT_transfer` and the K2 derivation:
`P.Q = Q`, `T = (log Q)^{r+ε}`, `w = 1`, `L = (191/100)ℒ`, `log Q ≤ ℒ ≤ 2 log Q`, `ℒ ≤ log Q + (r+ε) log log Q`.
-/
import ZetaShell.ShellK.L10c_Window
import ZetaShell.Design.SD_A7_Regime
import ZetaShell.Design.SD_A8_Scales

noncomputable section
open Filter

namespace ZetaShell
namespace ShellK
namespace K2c

open ZetaQ

/-- `ℒ ≤ log Q + (r+ε) log log Q` on a Shell design. -/
theorem LL_le_of_design (r ε : ℝ) {Qn : ℕ} (hQ3 : 3 ≤ Qn) {P : ParamsQ}
    (hdes : Design.ShellDesignM S53L75 r ε (Qn : ℝ) P) :
    P.LL ≤ Real.log Qn + (r + ε) * Real.log (Real.log Qn) := by
  have hQ : P.Q = Qn := hdes.2.1
  have hT : P.T = Real.log Qn ^ (r + ε) := by rw [hdes.2.2.1]; rfl
  have hQ3' : (3 : ℝ) ≤ Qn := by exact_mod_cast hQ3
  have hQpos : (0 : ℝ) < Qn := by linarith
  have hy : 1 < Real.log Qn := by
    rw [Real.lt_log_iff_exp_lt hQpos]; linarith [Real.exp_one_lt_d9]
  have hTpos : 0 < Real.log Qn ^ (r + ε) := Real.rpow_pos_of_pos (by linarith) _
  unfold ParamsQ.LL
  rw [hQ, hT, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hTpos.ne',
    Real.log_rpow (by linarith)]
  have : 0 < Real.log (2 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  linarith

/-- the design facts, eventually along `Qn`. -/
theorem design_facts (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      P.Valid ∧ 8 * P.w ≤ P.LB ∧ P.w = 1 ∧ P.Q = Qn ∧ P.T = Real.log Qn ^ (r + ε) ∧ P.lam = 191 / 100 ∧
        P.LB = 191 / 100 * P.LL ∧ Real.log Qn ≤ P.LL ∧ P.LL ≤ 2 * Real.log Qn ∧
        P.LL ≤ Real.log Qn + (r + ε) * Real.log (Real.log Qn) ∧ 1 < Real.log Qn := by
  have hS1 : (1 : ℝ) ≤ (S53L75.lam : ℝ) := by norm_num [S53L75]
  have hS2 : (S53L75.lam : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  filter_upwards [Design.shellDesign_regime S53L75 hS2 r ε hr hε 1 le_rfl, eventually_ge_atTop 3]
    with Qn hreg hQ3 P hdes
  have hQ3' : (3 : ℝ) ≤ Qn := by exact_mod_cast hQ3
  have hQpos : (0 : ℝ) < Qn := by linarith
  have hy : 1 < Real.log Qn := by
    rw [Real.lt_log_iff_exp_lt hQpos]; linarith [Real.exp_one_lt_d9]
  obtain ⟨hT, hyLL, -, hw1⟩ := Design.scales_of_shellDesignM hS1 hdes hr (by omega)
  have hlam : P.lam = 191 / 100 := by rw [hdes.2.2.2.1]; norm_num [S53L75]
  obtain ⟨-, -, -, hLL2, -⟩ := hreg P hdes
  refine ⟨hdes.1, hdes.2.2.2.2.2.1, hw1 (by linarith), hdes.2.1, hT, hlam, ?_, hyLL, hLL2,
    LL_le_of_design r ε hQ3 hdes, hy⟩
  show P.lam * P.LL = _
  rw [hlam]

end K2c
end ShellK
end ZetaShell
