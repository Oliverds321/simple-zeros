/-
Node B1 (L7_1): the Mathlib-only counts of `ChallengeShell` ARE ZetaQ's counts (definitional).
`famN (modQle Q) = ZetaQ.NfamCount Family.qle Q`, same for `N0s`, same for the dyadic family; `twin = ZetaQ.Twin`.
Draft: sec_shell.tex l.37 (𝔉_Q = primitive χ mod q, 1 < q ≤ Q). Dependencies: none. Difficulty: E.
-/
import ZetaShell.Interfaces

namespace ZetaShell

theorem famN_qle_eq (Qn : ℕ) (T₁ T₂ : ℝ) :
    famN (modQle Qn) T₁ T₂ = ZetaQ.NfamCount ZetaQ.Family.qle Qn T₁ T₂ := rfl

theorem famN0s_qle_eq (Qn : ℕ) (T₁ T₂ : ℝ) :
    famN0s (modQle Qn) T₁ T₂ = ZetaQ.N0sFamCount ZetaQ.Family.qle Qn T₁ T₂ := rfl

theorem famN_dyadic_eq (Qn : ℕ) (T₁ T₂ : ℝ) :
    famN (modDyadic Qn) T₁ T₂ = ZetaQ.NfamCount ZetaQ.Family.dyadic Qn T₁ T₂ := rfl

theorem famN0s_dyadic_eq (Qn : ℕ) (T₁ T₂ : ℝ) :
    famN0s (modDyadic Qn) T₁ T₂ = ZetaQ.N0sFamCount ZetaQ.Family.dyadic Qn T₁ T₂ := rfl

theorem twin_eq (Q r ε : ℝ) : twin Q r ε = ZetaQ.Twin Q r ε := rfl

end ZetaShell
