/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution/FollowUpFamily.lean — the two statements of Challenge/FollowUpFamily.lean, byte-for-byte (generated from one
list by `gen_family.py`), PROVED by delegating to the ZetaShell library (untrusted; checked by comparator):
  * `family_simple_on_line_killed`: `ZetaShell.LemmaK.theorem_one_prime_design` (ZetaShell/LemmaK/LK_KT_Headline.lean),
    stated over ZetaQ's counts `ZetaQ.NfamCount Family.qle`, `ZetaQ.N0sFamCount Family.qle`, `ZetaQ.Twin` and the constant
    `ZetaShell.LemmaK.PcertKD = 7235/10000 : ℚ`;
  * `family_simple_on_line_shell`: `ZetaShell.shell_S53_qle_reduced` (ZetaShell/Top/HeadlineReduced.lean), stated over
    the architect's layer `ZetaShell.famN`, `famN0s`, `modQle`, `twin`, `ZeroDensityInput` and the constant
    `ZetaShell.PcertS53 = 9059137927/10^10 : ℚ`.
Bridges (§ below): every count and `twin` of ChallengeDeps/FollowUpFamily.lean agrees with the library's by `rfl`; the
hypothesis `FollowUpFamily.ZeroDensityInput` is converted field by field to `ZetaShell.ZeroDensityInput` (each field by
unfolding); the two rational constants are rewritten to the real numerals of the statements by `norm_num`.
-/
import ChallengeDeps.FollowUpFamily
import ZetaShell.Top.HeadlineReduced
import ZetaShell.LemmaK.LK_KT_Headline

open FollowUpFamily

noncomputable section

namespace FollowUpFamily.Sol

/-! ### The counts and the height are the library's (definitional) -/

theorem famN_qle_eq (Qn : ℕ) (T₁ T₂ : ℝ) :
    famN (modQle Qn) T₁ T₂ = ZetaQ.NfamCount ZetaQ.Family.qle Qn T₁ T₂ := rfl

theorem famN0s_qle_eq (Qn : ℕ) (T₁ T₂ : ℝ) :
    famN0s (modQle Qn) T₁ T₂ = ZetaQ.N0sFamCount ZetaQ.Family.qle Qn T₁ T₂ := rfl

theorem twin_eq_Twin (Q r ε : ℝ) : twin Q r ε = ZetaQ.Twin Q r ε := rfl

theorem famN_eq_shell (M : Finset ℕ) (T₁ T₂ : ℝ) : famN M T₁ T₂ = ZetaShell.famN M T₁ T₂ := rfl

theorem famN0s_eq_shell (M : Finset ℕ) (T₁ T₂ : ℝ) : famN0s M T₁ T₂ = ZetaShell.famN0s M T₁ T₂ := rfl

theorem modQle_eq_shell (Q : ℕ) : modQle Q = ZetaShell.modQle Q := rfl

theorem twin_eq_shell (Q r ε : ℝ) : twin Q r ε = ZetaShell.twin Q r ε := rfl

/-! ### The hypothesis is the library's (field by field, each by unfolding) -/

theorem zdi_to_shell (h : FollowUpFamily.ZeroDensityInput) : ZetaShell.ZeroDensityInput :=
  ⟨h.jutila, h.montgomery⟩

theorem zdi_of_shell (h : ZetaShell.ZeroDensityInput) : FollowUpFamily.ZeroDensityInput :=
  ⟨h.jutila, h.montgomery⟩

/-! ### The two constants -/

theorem PcertKD_eq : ((ZetaShell.LemmaK.PcertKD : ℚ) : ℝ) = (7235 : ℝ) / 10 ^ 4 := by
  rw [ZetaShell.LemmaK.PcertKD]; norm_num

theorem PcertS53_eq : ((ZetaShell.PcertS53 : ℚ) : ℝ) = (9059137927 : ℝ) / 10 ^ 10 := by
  rw [ZetaShell.PcertS53]; norm_num

/-! ### The two theorems over the ChallengeDeps definitions -/

theorem killed (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ((7235 : ℝ) / 10 ^ 4 - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * famN (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₀, c, hc, h⟩ := ZetaShell.LemmaK.theorem_one_prime_design r ε hr hε
  refine ⟨Q₀, c, hc, fun Qn hQn => ?_⟩
  rw [famN_qle_eq, famN0s_qle_eq, twin_eq_Twin, ← PcertKD_eq]
  exact h Qn hQn

theorem shell (hD : FollowUpFamily.ZeroDensityInput) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ((9059137927 : ℝ) / 10 ^ 10 - c * Real.log (Qn : ℝ) ^ (-θ))
          * famN (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₀, c, hc, h⟩ := ZetaShell.shell_S53_qle_reduced (zdi_to_shell hD) r ε θ hr hε hθ hθ'
  refine ⟨Q₀, c, hc, fun Qn hQn => ?_⟩
  rw [famN_eq_shell, famN0s_eq_shell, modQle_eq_shell, twin_eq_shell, ← PcertS53_eq]
  exact h Qn hQn

end FollowUpFamily.Sol

/-- **Theorem thm:one-prime (killed kernel)** of the family paper: for `T = (log Q)^{r+ε}`, `r ≥ 3`, `ε > 0`, there are
`Q₀` and `c > 0` such that for every integer `Q ≥ Q₀`
`(0.7235 − c·log log Q/log Q) · Σ_{1<q≤Q} Σ*_χ N_χ(T,2T) ≤ Σ_{1<q≤Q} Σ*_χ N^s_{0,χ}(T,2T)`.
No hypothesis. (In the library: `ZetaShell.LemmaK.theorem_one_prime_design`.) -/
theorem family_simple_on_line_killed (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ((7235 : ℝ) / 10 ^ 4 - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * famN (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) :=
  FollowUpFamily.Sol.killed r ε hr hε

/-- **Theorem thm:shell (the Shell kernel)** of the family paper: assume the zero-density estimates (J) and (M)
(`ZeroDensityInput`). For `T = (log Q)^{r+ε}`, `r ≥ 3`, `ε > 0`, and `0 < θ < 503/1994`, there are `Q₀` and `c > 0`
such that for every integer `Q ≥ Q₀`
`(0.9059137927 − c·(log Q)^{−θ}) · Σ_{1<q≤Q} Σ*_χ N_χ(T,2T) ≤ Σ_{1<q≤Q} Σ*_χ N^s_{0,χ}(T,2T)`.
(In the library: `ZetaShell.shell_S53_qle_reduced`.) -/
theorem family_simple_on_line_shell (hD : ZeroDensityInput) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ((9059137927 : ℝ) / 10 ^ 10 - c * Real.log (Qn : ℝ) ^ (-θ))
          * famN (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) :=
  FollowUpFamily.Sol.shell hD r ε θ hr hε hθ hθ'

end
