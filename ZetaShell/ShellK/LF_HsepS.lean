/-
F1c-4b RESTATED (L7_3, round 5): **the ends separation at the Shell envelope `c₁ = 0.52`**, and the ends majorant at
that envelope.
* `shell_hsepS` (the restated F1c-4b): `Bfam ≤ c_μ·Q·envSepS` along the Shell design, from `Bfam_le_sep_S`
  (`LF_EndsS`) with A7's regime: `X ≤ Q^{2−9/200}` gives `log X ≤ 1.955·log Q`, and `2Q^{−9/200} ≤ 1/K` with
  `K = 20000` gives `πX ≤ 10⁻⁴Q²`; `Q ≥ 10⁹` eventually; `largeSieve_holds`.
* `shell_endsS` (F1c-4c at the new envelope): `endsMajS = (0.52/0.41)²·endsMaj` (`endsMajS_eq`), so `shell_ends` at
  `ε′/2` gives `endsMajS ≤ ε′/8·𝒩`.
The old `shell_hsep` (ZetaQ's envelope with `c₁ = 0.41`, `LF_AsmBase`) is kept under its name and is NOT used: the
tree's route cannot reach `c₁ = 0.41` at `λ = 1.91` (it needs `c₁ ≥ 0.5085`).
-/
import ZetaShell.ShellK.LF_EndsS
import ZetaShell.Skeleton.LF_AsmBase

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Ends ZetaQ.Payoff ZetaQ.FrobAssembly

/-- **F1c-4b, restated.** The ends separation along the Shell design at `c₁ = 0.52`. -/
theorem shell_hsepS (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSepS P τ := by
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  filter_upwards [Design.shellDesign_regime S53L75 hS2 r ε hr hε 20000 (by norm_num),
    eventually_ge_atTop 1000000000] with Qn hreg hQn
  intro P hdes τ
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  obtain ⟨-, -, -, -, -, hX, hQd, -⟩ := hreg P hdes
  have hQ0 : (1000000000 : ℝ) ≤ P.Q := by rw [hQ]; exact_mod_cast hQn
  have hQpos : (0 : ℝ) < P.Q := by linarith
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hXpos : (0 : ℝ) < P.XQ := by linarith
  have hδ : Design.deltaShell = 9 / 200 := rfl
  rw [hδ] at hX hQd
  have hY : Real.log P.XQ ≤ 1.955 * Real.log P.Q := by
    have hX' : P.XQ ≤ P.Q ^ ((2 : ℝ) - 9 / 200) := hX
    have h1 := Real.log_le_log hXpos hX'
    rw [Real.log_rpow hQpos] at h1
    have e : (2 : ℝ) - 9 / 200 = 1.955 := by norm_num
    rw [e] at h1
    exact h1
  have hXb : Real.pi * P.XQ ≤ 0.0001 * P.Q ^ 2 := by
    have hsplit : Real.rpow P.Q (2 - 9 / 200) = P.Q ^ 2 * Real.rpow P.Q (-(9 / 200)) := by
      have e : (2 : ℝ) - 9 / 200 = 2 + (-(9 / 200)) := by ring
      rw [e]
      show P.Q ^ ((2 : ℝ) + (-(9 / 200))) = P.Q ^ 2 * P.Q ^ (-((9 : ℝ) / 200))
      rw [Real.rpow_add hQpos, Real.rpow_two]
    have hsmall : Real.rpow P.Q (-(9 / 200)) ≤ 1 / 40000 := by linarith
    have hQ2 : 0 ≤ P.Q ^ 2 := sq_nonneg _
    have h1 : P.XQ ≤ P.Q ^ 2 * (1 / 40000) := by
      rw [hsplit] at hX
      exact le_trans hX (mul_le_mul_of_nonneg_left hsmall hQ2)
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith [Real.pi_pos]
  have hQnQ : (Qn : ℝ) ≤ P.Q := by rw [hQ]
  have h := Bfam_le_sep_S P Qn P.XQ hP largeSieve_holds hQnQ hX1 hY hXb hQ0 τ
  rw [scale_mul_envSep_S]
  exact h

/-- `endsMajS = (0.52/0.41)²·endsMaj`. -/
theorem endsMajS_eq (P : ParamsQ) : endsMajS P = (52 / 41) ^ 2 * endsMaj P := by
  unfold endsMajS endsMaj c1S c1Ends
  ring

/-- **F1c-4c at the new envelope.** -/
theorem shell_endsS (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      endsMajS P ≤ ε' / 8 * NfamQ P Family.qle Qn := by
  filter_upwards [shell_ends r ε hr hε (ε' / 2) (by positivity)] with Qn h
  intro P hdes
  have h1 := h P hdes
  have hN0 : 0 ≤ NfamQ P Family.qle Qn := NfamQ_nonneg P Family.qle Qn
  rw [endsMajS_eq]
  have h2 : (52 / 41 : ℝ) ^ 2 ≤ 2 := by norm_num
  have h5 : 0 ≤ ε' / 2 / 8 * NfamQ P Family.qle Qn := mul_nonneg (by positivity) hN0
  have h4 : (52 / 41 : ℝ) ^ 2 * endsMaj P ≤ (52 / 41) ^ 2 * (ε' / 2 / 8 * NfamQ P Family.qle Qn) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h6 := mul_le_mul_of_nonneg_right h2 h5
  linarith

end F1c
end ShellK
end ZetaShell
