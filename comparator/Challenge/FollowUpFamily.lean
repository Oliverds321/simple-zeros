/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Challenge/FollowUpFamily.lean — the TRUSTED statements of the comparator topic `FollowUpFamily` (the family follow-up
paper): WHAT IS CLAIMED. Two theorem statements, each with proof `sorry` (challenge side):
  * `family_simple_on_line_killed` (Theorem thm:one-prime, constant 0.7235, rate log log Q/log Q), no hypothesis;
  * `family_simple_on_line_shell` (Theorem thm:shell, constant 0.9059137927, rate (log Q)^{−θ} for 0 < θ < 503/1994),
    with the one displayed hypothesis `ZeroDensityInput` (the zero-density estimates (J) of Jutila and (M) of
    Montgomery–Bombieri, defined with their sources in ChallengeDeps/FollowUpFamily.lean).
Both are about the family of primitive Dirichlet characters χ mod q, 1 < q ≤ Q, at the height T = (log Q)^{r+ε}: the
zeros of L(s,χ) with T < Im ρ ≤ 2T and 0 < Re ρ < 1 that are simple and on the critical line make up at least the
stated proportion of all of them (counted with multiplicity), up to the stated error term, for every Q ≥ Q₀.
Solution/FollowUpFamily.lean proves exactly these statements (untrusted); see README_followup_family.md.
The `sorry`s below are deliberate.
-/
import ChallengeDeps.FollowUpFamily

open FollowUpFamily

noncomputable section

/-- **Theorem thm:one-prime (killed kernel)** of the family paper: for `T = (log Q)^{r+ε}`, `r ≥ 3`, `ε > 0`, there are
`Q₀` and `c > 0` such that for every integer `Q ≥ Q₀`
`(0.7235 − c·log log Q/log Q) · Σ_{1<q≤Q} Σ*_χ N_χ(T,2T) ≤ Σ_{1<q≤Q} Σ*_χ N^s_{0,χ}(T,2T)`.
No hypothesis. (In the library: `ZetaShell.LemmaK.theorem_one_prime_design`.) -/
theorem family_simple_on_line_killed (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ((7235 : ℝ) / 10 ^ 4 - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * famN (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
  sorry

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
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
  sorry

end
