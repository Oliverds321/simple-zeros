/-
**F1c from Theorem K** (L7_10). L7_7's open node `frob_row_shell` (`lean_work/L7_7/nodes/SD_F1c_FrobRow.lean`),
the Frobenius row at the Shell constant, DERIVED from Theorem K (`thmK`, L10_K, at `α′ = 2497/1500`) and the chain
node `F1c_chain` (L10_F1cChain), with `sorry` only in those inputs (and, below them, in K1, K2, K3, KInt).
`frob_row_shell_of_K` has L7_7's conclusion with ONLY `ZeroDensityInput` as hypothesis; `frob_row_shell'` then
reproduces L7_7's exact signature (which also carries `PNTErrorTerm` and `CertS53`, unused).
-/
import ZetaShell.ShellK.L10_K
import ZetaShell.ShellK.L10_F1cChain

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ Filter ZetaShell.ShellS

theorem thetaD1p_S53 : thetaD1p (2497 / 1500) = 503 / 1994 := by
  unfold thetaD1p
  rw [min_eq_right (by norm_num)]
  norm_num

theorem frob_row_shell_of_K (hD : ZeroDensityInput) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 503 / 1994) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.qle Qn
        ≤ (2 - ((PcertS53 : ℚ) : ℝ) + c * shellRate θ Qn) * NfamQ P Family.qle Qn := by
  obtain ⟨c₀, hc₀, hK⟩ := thmK hD (2497 / 1500) (by norm_num) (by norm_num) r ε θ hr hε
    (by rw [thetaD1p_S53]; exact hθ')
  obtain ⟨c, hc, hch⟩ := F1c_chain r ε θ hr hε hθ hθ' c₀ hc₀
  refine ⟨c, hc, ?_⟩
  filter_upwards [hK, hch] with Qn h1 h2
  intro P hP
  exact h2 P hP (h1 P hP)

/-- L7_7's signature of F1c (`SD_F1c_FrobRow.frob_row_shell`), verbatim; `hP` and `hcert` are not used. -/
theorem frob_row_shell' (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertS53) (r ε θ : ℝ)
    (hr : 3 ≤ r) (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.qle Qn
        ≤ (2 - ((PcertS53 : ℚ) : ℝ) + c * shellRate θ Qn) * NfamQ P Family.qle Qn :=
  frob_row_shell_of_K hD r ε θ hr hε hθ hθ'

end ShellK
end ZetaShell
