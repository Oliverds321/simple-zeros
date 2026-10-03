/-
Node SD-A8 (L7_7, F1a): the Shell design's scales — `T = (log Q)^{r+ε}`, `log Q ≤ ℒ`, `ℒ ≤ L` (`λ ≥ 1`),
`w = 1` (`r ≥ 3`, the clamp; L7_4 correction 2). Copy of `ZetaQ.Margin` §1 (`Margin.lean:64–85`). Deps: none.
Difficulty E.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

open ZetaQ

theorem scales_of_shellDesignM {S : ShellProfile} (hS : 1 ≤ (S.lam : ℝ)) {r ε : ℝ} {Qn : ℕ}
    {P : ParamsQ} (hdes : ShellDesignM S r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hQn : 1 ≤ Qn) :
    P.T = Real.log (Qn : ℝ) ^ (r + ε) ∧ Real.log (Qn : ℝ) ≤ P.LL ∧ P.LL ≤ P.LB ∧
      (1 ≤ P.LL → P.w = 1) := by
  have hT : P.T = Real.log (Qn : ℝ) ^ (r + ε) := by rw [hdes.2.2.1]; rfl
  have hLLu : Real.log (Qn : ℝ) ≤ P.LL := (log_Qn_le_LL hdes.1 hQn hdes.2.1).1
  have hlog0 : 0 ≤ Real.log (Qn : ℝ) := Real.log_nonneg (by exact_mod_cast hQn)
  have hLL0 : 0 ≤ P.LL := le_trans hlog0 hLLu
  refine ⟨hT, hLLu, ?_, ?_⟩
  · have hlam : P.lam = (S.lam : ℝ) := hdes.2.2.2.1
    unfold ParamsQ.LB
    rw [hlam]
    nlinarith
  · intro hLL1
    have hw : P.w = wDesign P.LL r := hdes.2.2.2.2.1
    rw [hw]
    unfold wDesign wStar
    exact max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))

end ZetaShell.Design
