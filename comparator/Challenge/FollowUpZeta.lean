/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Challenge/FollowUpZeta.lean — the TRUSTED statements of the comparator topic `FollowUpZeta` (the ζ follow-up paper):
WHAT IS CLAIMED. Fourteen theorem statements, each with proof `sorry` (challenge side):
  * six headlines, each with one certificate hypothesis (`CertAM5`, `CertAM7` or `CertS8`, defined with their provenance
    in ChallengeDeps/FollowUpZeta.lean): simple zeros ≥ 0.675158622 / 0.676102666, distinct zeros ≥ 0.837579311 /
    0.838051333, simple zeros on the critical line ≥ 0.6733736895, zeros simple or on the critical line ≥ 0.8879195,
    on the dyadic windows T < Im ρ ≤ 2T;
  * the same six on the cumulative windows 0 < Im ρ ≤ T;
  * two non-vacuity companions (every window is finite; N(T, 2T) → ∞).
"liminf_{T→∞} X(T)/N(T) ≥ c" is written "∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)", N counting the nontrivial zeros
WITH multiplicity. Solution/FollowUpZeta.lean proves exactly these statements (untrusted); see README_followup.md.
The `sorry`s below are deliberate.
-/
import ChallengeDeps.FollowUpZeta

open FollowUpZeta

noncomputable section

/-- **Simple zeros (K = 5 certificate)**, thm:sigd-Sigma with the K = 5 row of rem:sigd-cert: at least 0.675158622 of
the nontrivial zeros with T < Im ρ ≤ 2T (counted with multiplicity) are simple, for all large T. -/
theorem zeta_simple_K5 (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) := by
  sorry

/-- `zeta_simple_K5` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_simple_K5_cumulative (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T := by
  sorry

/-- **Distinct zeros (K = 5 certificate)**, thm:sigd-D with the K = 5 row of rem:sigd-cert: at least 0.837579311. -/
theorem zeta_distinct_K5 (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  sorry

/-- `zeta_distinct_K5` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_distinct_K5_cumulative (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T := by
  sorry

/-- **Simple zeros**, thm:sigd-Sigma (K = 7 certificate): at least 0.676102666. -/
theorem zeta_simple_K7 (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) := by
  sorry

/-- `zeta_simple_K7` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_simple_K7_cumulative (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T := by
  sorry

/-- **Distinct zeros**, thm:sigd-D (K = 7 certificate): at least 0.838051333. -/
theorem zeta_distinct_K7 (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  sorry

/-- `zeta_distinct_K7` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_distinct_K7_cumulative (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T := by
  sorry

/-- **Simple zeros on the critical line**, thm:zeta-mainw2 (window ψ̃, K = 8): at least 0.6733736895. -/
theorem zeta_simple_on_line (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6733736895 : ℝ) / 10 ^ 10 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- `zeta_simple_on_line` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_simple_on_line_cumulative (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6733736895 : ℝ) / 10 ^ 10 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  sorry

/-- **Zeros that are simple or on the critical line**, cor:oll-SC (on-line zeros with multiplicity plus simple
off-line zeros): at least 0.8879195. -/
theorem zeta_simple_or_critical (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((8879195 : ℝ) / 10 ^ 7 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsc T (2 * T) := by
  sorry

/-- `zeta_simple_or_critical` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_simple_or_critical_cumulative (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((8879195 : ℝ) / 10 ^ 7 - ε) * (Ncount 0 T : ℝ) ≤ Nsc 0 T := by
  sorry

/-- Non-vacuity companion: every window T₁ < Im ρ ≤ T₂ holds finitely many nontrivial zeros, so `Ncount`, `Nsc`
(finite sums) and `Nsimple`, `Ndist`, `N0simple` (`Set.ncard`) are genuine counts (Lean's `finsum` and `ncard` would
return 0 on an infinite set). -/
theorem zeta_zerosIn_finite (T₁ T₂ : ℝ) :
    (zerosIn T₁ T₂).Finite := by
  sorry

/-- Non-vacuity companion: the denominator N(T, 2T) tends to infinity. -/
theorem zeta_tendsto_Ncount :
    Filter.Tendsto (fun T : ℝ => (Ncount T (2 * T) : ℝ)) Filter.atTop Filter.atTop := by
  sorry

end
