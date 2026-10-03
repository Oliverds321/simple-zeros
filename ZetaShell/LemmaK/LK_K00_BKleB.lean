/-
Node K00 (L7_3): the killed functional is below ZetaQ's: `B^K_C(v) ≤ B_C(v)` for admissible `v` and `C ≥ 0`.
Draft: sec_lemmaK.tex, ssec "(e) The functional": "Since `min(|α|,1) ≤ |α|`, `B^K_C ≤ B` for every `v`"
(the kernel `C` on `|α| > 1` is `≤ C|α|` there). Dependencies: trunk `ZetaQ.Payoff` (`Wpsi_integrable`,
`psi_nonneg`). Difficulty: E. PROVED.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace LemmaK

open ZetaQ.Payoff

theorem killedKernel_nonneg {C : ℝ} (hC : 0 ≤ C) (α : ℝ) : 0 ≤ killedKernel C α := by
  unfold killedKernel; split_ifs <;> first | exact abs_nonneg _ | exact hC

theorem killedKernel_le_W {C : ℝ} (hC : 0 ≤ C) (α : ℝ) : killedKernel C α ≤ W C α := by
  unfold killedKernel W
  split_ifs with h
  · exact le_rfl
  · have h' : 1 < |α| := lt_of_not_ge h
    nlinarith

/-- **K00.** `B^K_C(v) ≤ B_C(v)` (admissible `v`, `C ≥ 0`). -/
theorem BK_le_B {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) {C : ℝ} (hC : 0 ≤ C) :
    BK C v ≤ B C v := by
  unfold BK B
  have h : ∫ α, killedKernel C α * psi v α ≤ ∫ α, W C α * psi v α := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun α =>
        mul_nonneg (killedKernel_nonneg hC α) (psi_nonneg hv α)
    · exact Wpsi_integrable hv C
    · exact Filter.Eventually.of_forall fun α =>
        mul_le_mul_of_nonneg_right (killedKernel_le_W hC α) (psi_nonneg hv α)
  linarith

end LemmaK
end ZetaShell
