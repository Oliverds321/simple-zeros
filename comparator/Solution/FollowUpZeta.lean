/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution/FollowUpZeta.lean — the fourteen statements of Challenge/FollowUpZeta.lean, byte-for-byte (generated from one list
by `gen_followup.py`), PROVED by delegating to the ZetaS library (untrusted; checked by comparator):
  * the headlines: `ZetaS.Top.zeta_{simple,distinct}_K{5,7}_final` (ZetaS/Top/TopFinal.lean) and
    `ZetaS.Top.zeta_simple_on_line`, `ZetaS.Top.zeta_simple_or_critical` (ZetaS/Top/TopSSC.lean);
  * the certificate Props of ChallengeDeps/FollowUpZeta.lean are converted to the library's copies (`ZetaS.CertAM5`,
    `ZetaS.CertAM7`, `ZetaS.CertS8`) by rebuilding the weight structures field by field (`toLW`, `toMW`); every other
    definition agrees with the library's by unfolding;
  * the cumulative forms: interval additivity of the counts and the tree's dyadic summation
    (`Zeta23.cumulative_of_dyadic`, with `Zeta23.riemannVonMangoldt_zeta`);
  * the companions: `Zeta23.zerosIn_finite`, and `Zeta23.Assembly.tendsto_N_atTop` with the same RvM theorem.
-/
import ChallengeDeps.FollowUpZeta
import ZetaS.Top.TopFinal
import ZetaS.Top.TopSSC
import Zeta23.Final

open FollowUpZeta

noncomputable section

namespace FollowUpZeta.Sol

/-! ### The certificate Props, converted to the library's copies -/

/-- The library's position weights with the same fields. -/
def toLW {K : ℕ} (W : FollowUpZeta.LocalWeights K) : ZetaS.LocalWeights K where
  γ := W.γ
  μ := W.μ
  two_le := W.two_le
  γ_nonneg := W.γ_nonneg
  γ_sum := W.γ_sum
  μ_nonneg := W.μ_nonneg

/-- The library's all-marks weights with the same fields. -/
def toMW {K : ℕ} (W : FollowUpZeta.MarkWeights K) : ZetaS.MarkWeights K where
  toLocalWeights := toLW W.toLocalWeights
  b := W.b

theorem certS8 (h : FollowUpZeta.CertS8) : ZetaS.CertS8 := by
  obtain ⟨W, h1, h2⟩ := h
  exact ⟨toLW W, h1, h2⟩

theorem certAM5 (h : FollowUpZeta.CertAM5) : ZetaS.CertAM5 := by
  obtain ⟨W, h1, h2, h3, h4⟩ := h
  exact ⟨toMW W, h1, h2, h3, h4⟩

theorem certAM7 (h : FollowUpZeta.CertAM7) : ZetaS.CertAM7 := by
  obtain ⟨W, h1, h2, h3, h4⟩ := h
  exact ⟨toMW W, h1, h2, h3, h4⟩

/-! ### Finite windows, interval additivity, dyadic ⇒ cumulative -/

theorem zerosIn_split {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    zerosIn a d = zerosIn a b ∪ zerosIn b d := by
  ext ρ
  simp only [zerosIn, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨h0, h1, h2⟩
    by_cases h : ρ.im ≤ b
    · exact Or.inl ⟨h0, h1, h⟩
    · exact Or.inr ⟨h0, lt_of_not_ge h, h2⟩
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · exact ⟨h0, h1, h2.trans hbd⟩
    · exact ⟨h0, hab.trans_lt h1, h2⟩

theorem zerosIn_disj (a b d : ℝ) : Disjoint (zerosIn a b) (zerosIn b d) := by
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, h2⟩ ⟨_, h1, _⟩
  exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

theorem Nsimple_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    Nsimple a d = Nsimple a b + Nsimple b d := by
  unfold Nsimple
  rw [zerosIn_split hab hbd, Set.union_inter_distrib_right]
  exact Set.ncard_union_eq ((zerosIn_disj a b d).mono Set.inter_subset_left Set.inter_subset_left)
    ((Zeta23.zerosIn_finite a b).subset Set.inter_subset_left)
    ((Zeta23.zerosIn_finite b d).subset Set.inter_subset_left)

theorem Nsc_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    FollowUpZeta.Nsc a d = FollowUpZeta.Nsc a b + FollowUpZeta.Nsc b d := by
  unfold FollowUpZeta.Nsc
  rw [zerosIn_split hab hbd, Set.union_inter_distrib_right]
  exact finsum_mem_union ((zerosIn_disj a b d).mono Set.inter_subset_left Set.inter_subset_left)
    ((Zeta23.zerosIn_finite a b).subset Set.inter_subset_left)
    ((Zeta23.zerosIn_finite b d).subset Set.inter_subset_left)

theorem Ndist_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) : Ndist a d = Ndist a b + Ndist b d :=
  Zeta23.Ndist_add' Zeta23.zetaSeam hab hbd

theorem N0simple_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    N0simple a d = N0simple a b + N0simple b d :=
  Zeta23.N0simple_add' Zeta23.zetaSeam hab hbd

/-- The dyadic ε-form gives the cumulative one (windows (0,T]) for any interval-additive count. -/
theorem cumulative {c : ℝ} {f : ℝ → ℝ → ℕ}
    (hf_add : ∀ a b d : ℝ, a ≤ b → b ≤ d → f a d = f a b + f b d)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount T (2 * T) : ℝ) ≤ f T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount 0 T : ℝ) ≤ f 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.riemannVonMangoldt_zeta hf_add h

theorem tendsto_Ncount :
    Filter.Tendsto (fun T : ℝ => (Ncount T (2 * T) : ℝ)) Filter.atTop Filter.atTop := by
  have h := Zeta23.Assembly.tendsto_N_atTop Zeta23.zetaZeroConfig Zeta23.riemannVonMangoldt_zeta
  simp only [Zeta23.zetaZeroConfig_N] at h
  exact h

end FollowUpZeta.Sol

/-- **Simple zeros (K = 5 certificate)**, thm:sigd-Sigma with the K = 5 row of rem:sigd-cert: at least 0.675158622 of
the nontrivial zeros with T < Im ρ ≤ 2T (counted with multiplicity) are simple, for all large T. -/
theorem zeta_simple_K5 (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  ZetaS.Top.zeta_simple_K5_final (FollowUpZeta.Sol.certAM5 hcert)

/-- `zeta_simple_K5` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_simple_K5_cumulative (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T :=
  FollowUpZeta.Sol.cumulative (fun _ _ _ => FollowUpZeta.Sol.Nsimple_add) (zeta_simple_K5 hcert)

/-- **Distinct zeros (K = 5 certificate)**, thm:sigd-D with the K = 5 row of rem:sigd-cert: at least 0.837579311. -/
theorem zeta_distinct_K5 (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  ZetaS.Top.zeta_distinct_K5_final (FollowUpZeta.Sol.certAM5 hcert)

/-- `zeta_distinct_K5` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_distinct_K5_cumulative (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  FollowUpZeta.Sol.cumulative (fun _ _ _ => FollowUpZeta.Sol.Ndist_add) (zeta_distinct_K5 hcert)

/-- **Simple zeros**, thm:sigd-Sigma (K = 7 certificate): at least 0.676102666. -/
theorem zeta_simple_K7 (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  ZetaS.Top.zeta_simple_K7_final (FollowUpZeta.Sol.certAM7 hcert)

/-- `zeta_simple_K7` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_simple_K7_cumulative (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount 0 T : ℝ) ≤ Nsimple 0 T :=
  FollowUpZeta.Sol.cumulative (fun _ _ _ => FollowUpZeta.Sol.Nsimple_add) (zeta_simple_K7 hcert)

/-- **Distinct zeros**, thm:sigd-D (K = 7 certificate): at least 0.838051333. -/
theorem zeta_distinct_K7 (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  ZetaS.Top.zeta_distinct_K7_final (FollowUpZeta.Sol.certAM7 hcert)

/-- `zeta_distinct_K7` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_distinct_K7_cumulative (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  FollowUpZeta.Sol.cumulative (fun _ _ _ => FollowUpZeta.Sol.Ndist_add) (zeta_distinct_K7 hcert)

/-- **Simple zeros on the critical line**, thm:zeta-mainw2 (window ψ̃, K = 8): at least 0.6733736895. -/
theorem zeta_simple_on_line (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6733736895 : ℝ) / 10 ^ 10 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  ZetaS.Top.zeta_simple_on_line (FollowUpZeta.Sol.certS8 hcert)

/-- `zeta_simple_on_line` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_simple_on_line_cumulative (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6733736895 : ℝ) / 10 ^ 10 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  FollowUpZeta.Sol.cumulative (fun _ _ _ => FollowUpZeta.Sol.N0simple_add) (zeta_simple_on_line hcert)

/-- **Zeros that are simple or on the critical line**, cor:oll-SC (on-line zeros with multiplicity plus simple
off-line zeros): at least 0.8879195. -/
theorem zeta_simple_or_critical (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((8879195 : ℝ) / 10 ^ 7 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsc T (2 * T) :=
  ZetaS.Top.zeta_simple_or_critical (FollowUpZeta.Sol.certS8 hcert)

/-- `zeta_simple_or_critical` on the cumulative windows 0 < Im ρ ≤ T (same constant). -/
theorem zeta_simple_or_critical_cumulative (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((8879195 : ℝ) / 10 ^ 7 - ε) * (Ncount 0 T : ℝ) ≤ Nsc 0 T :=
  FollowUpZeta.Sol.cumulative (fun _ _ _ => FollowUpZeta.Sol.Nsc_add) (zeta_simple_or_critical hcert)

/-- Non-vacuity companion: every window T₁ < Im ρ ≤ T₂ holds finitely many nontrivial zeros, so `Ncount`, `Nsc`
(finite sums) and `Nsimple`, `Ndist`, `N0simple` (`Set.ncard`) are genuine counts (Lean's `finsum` and `ncard` would
return 0 on an infinite set). -/
theorem zeta_zerosIn_finite (T₁ T₂ : ℝ) :
    (zerosIn T₁ T₂).Finite :=
  Zeta23.zerosIn_finite T₁ T₂

/-- Non-vacuity companion: the denominator N(T, 2T) tends to infinity. -/
theorem zeta_tendsto_Ncount :
    Filter.Tendsto (fun T : ℝ => (Ncount T (2 * T) : ℝ)) Filter.atTop Filter.atTop :=
  FollowUpZeta.Sol.tendsto_Ncount

end
