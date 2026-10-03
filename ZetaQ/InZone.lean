/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaQ.FrobAssembly

/-! # The in-zone mean value and the PP block with in-zone coefficient 1 (§5's evaluation).

This module is sorry-free. Receipt: `audit/inzone/InZone_REPORT.md`.

CONTENTS (every lemma named; everything is `[propext, Classical.choice, Quot.sound]` —
including `famPP_le_zone_split`, which until the Gallagher rethread inherited the tree's
`sorryAx` through `largeSieveFamily_holds`):

 §1  `meanValue_generic` / `meanValue_upper` / `meanValue_lower`: for ANY finite set `S` of
     moduli, coefficient vector `c` on `N ⊆ [1,Y]`, and pair-sum bound
     `‖Σ_{q∈S}Σ*_χ χ(n)χ̄(m)‖ ≤ c_Q τ(|n−m|)` (n ≠ m):
       `|Σ_{q∈S}Σ*_χ ‖Σ_n c_n χ(n)‖² − Σ_n ‖c_n‖²·N_S(n)| ≤ c_Q·2Y(1+log Y)·‖c‖²`,
     `N_S(n) = Σ_{q∈S}Σ*_χ ‖χ(n)‖² ≤ |𝔉_S|` (coprimality-weighted diagonal). Lemma 5.2 crude
     + `sum_tau_le` + Schur/AM–GM (`schur_tau`, `tau_rowSum_le`).
 §2  `pairSumS_family_le`: the pair-sum bound `2Q·τ(|n−m|)` for BOTH families of record
     (`q ∈ [2,Q]` via `lemma5_2_crude`, dyadic via `lemma5_2_crude_dyadic`).
 §3  the instantiation at `a′(s)` (= `acoefLow`): `inZone_meanValue_pointwise` (both
     directions), `inZone_meanValue_upper/lower`, with the EXPLICIT
       `ERRin P Qn = 2·Qn·(2·Y_n·(1 + log Y_n))`, `Y_n = ⌊Q^{1−δ′}⌋₊`.
 §4  integrated against `g` over `U`: `inFormF_low_le` (upper), `inFormF_low_two_sided`.
 §5  Lemma 4.4's `a′/a″` split over the family of record: `inFormF_split`, `inFormF_high_le`
     (sieve on `a″`), `inFormF_full_le`.
 §6  the mirror `B_χ(s) = conj A_χ(−s)`: `Bchi_eq_conj_Achi_neg`, `integral_inZone_B_eq_A`,
     `integral_B_eq_A`, `integral_normB2_eq_normA2`.
 §7  the χ/χ̄ cross term over the family of record, pointwise and integrated on any
     measurable `U`: `cross_pointwise_family`, `cross_integral_family`.
 §8  **Part 2**: `famPP_inZone_le` (the in-zone PP form), `zone_diag_eq`
     (`∫_U g(‖a‖²+‖b‖²) = 2(P+R)`), `zone_normA2_eq`.
 §9  **Part 3, pointwise**: `famA_integral_le` (sieve on `A` over any `U`), `famPP_total_le`,
     `outZone_normA2_eq`, `famPP_total_le'` (master inequality in zone-split form).
 §10 the transfer `DesignFamily → DesignOfRecord`: `designFamily_of_DoR`,
     `transfer_of_designFamily`, `zone_facts_family`, `zone_facts_eventually`, `reg_eventually`.
 §11 eventual bookkeeping: `Cconst_mul_sizeR_le`, `sizeR_ge_point`, `ERRin_le_sizeR`
     (`ERR_in ≤ 80|𝔉|/(log Q)²`), `ERRin_small_eventually`, `sizeR_LL_le_NfamQ_eventually`.
 §12 the dictionary `integral_Icc_abs_eq_two`, `s0_div_LL_eq_zoneFactor`, `zoneMain_eq`, the
     arithmetic `final_arith`, and **the deliverable `famPP_le_zone_split`**.
 §13 the same mean value for §4's own `famSum` (`q ≤ ⌊Q⌋₊`): `famSum_low_pointwise`,
     `inZoneFormFam_low_le` (the UPPER bound on the object of `lemma44_zone_boundary`'s `hmv`),
     `inZoneFormFam_low_two_sided`. -/
noncomputable section

open scoped BigOperators
open ComplexConjugate MeasureTheory Set

namespace ZetaQ
namespace InZone

open ZetaQ.Zones ZetaQ.Payoff

/-! ## 1. The generic mean value over a finite set `S` of moduli -/

/-- `Σ_{q∈S} Σ*_{χ mod q} χ(n)χ̄(m)` — the pair sum over an arbitrary finite set of moduli. -/
def pairSumS (S : Finset ℕ) (n m : ℕ) : ℂ := ∑ q ∈ S, primPairSum q n m

/-- `N_S(n) := Σ_{q∈S} Σ*_χ ‖χ(n)‖²` — the coprimality-weighted family count at `n`
(`= #{χ : (n, q_χ) = 1}`, since `‖χ(n)‖ ∈ {0,1}`). -/
def famCountAt (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ q ∈ S, ∑ χ ∈ primitiveChars q, ‖χ (n : ZMod q)‖ ^ 2

/-- `|𝔉_S| := Σ_{q∈S} φ*(q)`. -/
def sizeS (S : Finset ℕ) : ℝ := ∑ q ∈ S, (phiStar q : ℝ)

theorem famCountAt_nonneg (S : Finset ℕ) (n : ℕ) : 0 ≤ famCountAt S n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem famCountAt_le (S : Finset ℕ) (n : ℕ) : famCountAt S n ≤ sizeS S := by
  unfold famCountAt sizeS phiStar
  refine Finset.sum_le_sum fun q _ => ?_
  calc ∑ χ ∈ primitiveChars q, ‖χ (n : ZMod q)‖ ^ 2
      ≤ ∑ _χ ∈ primitiveChars q, (1 : ℝ) := by
        refine Finset.sum_le_sum fun χ _ => ?_
        have h := χ.norm_le_one (n : ZMod q)
        have h0 := norm_nonneg (χ (n : ZMod q))
        nlinarith
    _ = _ := by simp

/-- `‖z‖² = (z·z̄).re`. -/
theorem norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj, Complex.ofReal_re]

/-- the per-character expansion of `‖Σ_n c_n χ(n)‖²`. -/
theorem normSq_charSum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (N : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2
      = ∑ n ∈ N, ∑ m ∈ N,
          (c n * conj (c m) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))).re := by
  rw [norm_sq_eq_re_mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  ring_nf

/-- `pairSumS S n n = N_S(n)` (as a complex number). -/
theorem pairSumS_diag (S : Finset ℕ) (n : ℕ) :
    pairSumS S n n = ((famCountAt S n : ℝ) : ℂ) := by
  unfold pairSumS famCountAt primPairSum
  push_cast
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- the four-fold interchange `Σ_q Σ_χ Σ_n Σ_m = Σ_n Σ_m Σ_q Σ_χ`. -/
theorem sum4_comm (S : Finset ℕ) (N M : Finset ℕ)
    (F : ∀ q : ℕ, DirichletCharacter ℂ q → ℕ → ℕ → ℝ) :
    (∑ q ∈ S, ∑ χ ∈ primitiveChars q, ∑ n ∈ N, ∑ m ∈ M, F q χ n m)
      = ∑ n ∈ N, ∑ m ∈ M, ∑ q ∈ S, ∑ χ ∈ primitiveChars q, F q χ n m := by
  calc (∑ q ∈ S, ∑ χ ∈ primitiveChars q, ∑ n ∈ N, ∑ m ∈ M, F q χ n m)
      = ∑ q ∈ S, ∑ n ∈ N, ∑ m ∈ M, ∑ χ ∈ primitiveChars q, F q χ n m :=
        Finset.sum_congr rfl fun q _ =>
          Finset.sum_comm.trans (Finset.sum_congr rfl fun n _ => Finset.sum_comm)
    _ = ∑ n ∈ N, ∑ q ∈ S, ∑ m ∈ M, ∑ χ ∈ primitiveChars q, F q χ n m := Finset.sum_comm
    _ = ∑ n ∈ N, ∑ m ∈ M, ∑ q ∈ S, ∑ χ ∈ primitiveChars q, F q χ n m :=
        Finset.sum_congr rfl fun n _ => Finset.sum_comm

/-- **The family expansion**: diagonal (coprimality-weighted) plus off-diagonal. -/
theorem famS_expand (S N : Finset ℕ) (c : ℕ → ℂ) :
    (∑ q ∈ S, ∑ χ ∈ primitiveChars q, ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2)
      = ∑ n ∈ N, ‖c n‖ ^ 2 * famCountAt S n
        + (∑ n ∈ N, ∑ m ∈ N.erase n, c n * conj (c m) * pairSumS S n m).re := by
  classical
  -- (1) the full double sum `D`
  have h1 : (∑ q ∈ S, ∑ χ ∈ primitiveChars q, ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2)
      = ∑ n ∈ N, ∑ m ∈ N, (c n * conj (c m) * pairSumS S n m).re := by
    have e1 : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2
        = ∑ n ∈ N, ∑ m ∈ N,
            (c n * conj (c m) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))).re :=
      fun q χ => normSq_charSum_eq χ N c
    have e2 : ∀ n m : ℕ, (c n * conj (c m) * pairSumS S n m).re
        = ∑ q ∈ S, ∑ χ ∈ primitiveChars q,
            (c n * conj (c m) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))).re := by
      intro n m
      unfold pairSumS primPairSum
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum, Complex.re_sum]
    simp_rw [e1, e2]
    exact sum4_comm S N N _
  rw [h1]
  -- (2) split the inner sum at `m = n`
  have h2 : ∀ n ∈ N, ∑ m ∈ N, (c n * conj (c m) * pairSumS S n m).re
      = ‖c n‖ ^ 2 * famCountAt S n
        + (∑ m ∈ N.erase n, c n * conj (c m) * pairSumS S n m).re := by
    intro n hn
    rw [← Finset.add_sum_erase N _ hn, Complex.re_sum]
    congr 1
    rw [pairSumS_diag, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Complex.re_sum]

/-- the off-diagonal, bounded by the pair-sum hypothesis. -/
theorem offdiag_re_le (S N : Finset ℕ) (c : ℕ → ℂ) {cQ : ℝ}
    (hpair : ∀ n m : ℕ, n ≠ m →
      ‖pairSumS S n m‖ ≤ cQ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)) :
    |(∑ n ∈ N, ∑ m ∈ N.erase n, c n * conj (c m) * pairSumS S n m).re|
      ≤ cQ * ∑ n ∈ N, ∑ m ∈ N.erase n,
          ‖c n‖ * ‖c m‖ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  have hne : n ≠ m := (Finset.ne_of_mem_erase hm).symm
  have h := hpair n m hne
  have h0 : 0 ≤ ‖c n‖ * ‖c m‖ := by positivity
  calc ‖c n‖ * ‖c m‖ * ‖pairSumS S n m‖
      ≤ ‖c n‖ * ‖c m‖ * (cQ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)) :=
        mul_le_mul_of_nonneg_left h h0
    _ = cQ * (‖c n‖ * ‖c m‖ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)) := by ring

/-! ### the divisor row sum -/

theorem tau_natAbs_symm (n m : ℕ) :
    ((n : ℤ) - (m : ℤ)).natAbs = ((m : ℤ) - (n : ℤ)).natAbs := by
  rw [← Int.natAbs_neg, neg_sub]

/-- `Σ_{m ∈ [1,Y], m ≠ n} τ(|n − m|) ≤ 2·Σ_{k ≤ Y} τ(k)` for `n ≤ Y`. -/
theorem tau_rowSum_le (Y n : ℕ) (hn : n ≤ Y) :
    ∑ m ∈ (Finset.Icc 1 Y).erase n, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
      ≤ 2 * ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) := by
  classical
  set A := (Finset.Icc 1 Y).filter (fun m => m < n) with hA
  set B := (Finset.Icc 1 Y).filter (fun m => n < m) with hB
  have hsplit : (Finset.Icc 1 Y).erase n = A ∪ B := by
    ext m
    simp only [hA, hB, Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint A B := by
    rw [hA, hB, Finset.disjoint_filter]
    intro m _ h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hnn : ∀ k ∈ Finset.Icc 1 Y, (0 : ℝ) ≤ (tau k : ℝ) := fun _ _ => Nat.cast_nonneg _
  -- the `m < n` half: `m ↦ n − m`
  have hA1 : ∑ m ∈ A, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
      = ∑ m ∈ A, (tau (n - m) : ℝ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [hA, Finset.mem_filter, Finset.mem_Icc] at hm
    congr 2
    omega
  have hA2 : ∑ m ∈ A, (tau (n - m) : ℝ) = ∑ k ∈ A.image (fun m => n - m), (tau k : ℝ) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    simp only [hA, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    dsimp only at hab
    omega
  have hA3 : A.image (fun m => n - m) ⊆ Finset.Icc 1 Y := by
    intro k hk
    simp only [hA, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨m, ⟨⟨hm1, hm2⟩, hm3⟩, rfl⟩ := hk
    simp only [Finset.mem_Icc]
    omega
  have hAle : ∑ m ∈ A, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) ≤ ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) := by
    rw [hA1, hA2]
    exact Finset.sum_le_sum_of_subset_of_nonneg hA3 (fun k hk _ => hnn k hk)
  -- the `n < m` half: `m ↦ m − n`
  have hB1 : ∑ m ∈ B, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
      = ∑ m ∈ B, (tau (m - n) : ℝ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [hB, Finset.mem_filter, Finset.mem_Icc] at hm
    congr 2
    omega
  have hB2 : ∑ m ∈ B, (tau (m - n) : ℝ) = ∑ k ∈ B.image (fun m => m - n), (tau k : ℝ) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    simp only [hB, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    dsimp only at hab
    omega
  have hB3 : B.image (fun m => m - n) ⊆ Finset.Icc 1 Y := by
    intro k hk
    simp only [hB, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨m, ⟨⟨hm1, hm2⟩, hm3⟩, rfl⟩ := hk
    simp only [Finset.mem_Icc]
    omega
  have hBle : ∑ m ∈ B, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) ≤ ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) := by
    rw [hB1, hB2]
    exact Finset.sum_le_sum_of_subset_of_nonneg hB3 (fun k hk _ => hnn k hk)
  linarith

/-- **The Schur bound**: `Σ_{n≠m∈N} |c_n||c_m|τ(|n−m|) ≤ 2Y(1+log Y)·‖c‖²` for `N ⊆ [1, Y]`. -/
theorem schur_tau (N : Finset ℕ) (Y : ℕ) (hY : 1 ≤ Y) (hN : N ⊆ Finset.Icc 1 Y) (c : ℕ → ℂ) :
    ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ * ‖c m‖ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
      ≤ 2 * ((Y : ℝ) * (1 + Real.log Y)) * ∑ n ∈ N, ‖c n‖ ^ 2 := by
  classical
  set W : ℝ := 2 * ((Y : ℝ) * (1 + Real.log Y)) with hW
  set τ : ℕ → ℕ → ℝ := fun n m => (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) with hτ
  have hτnn : ∀ n m, 0 ≤ τ n m := fun n m => Nat.cast_nonneg _
  have hτsymm : ∀ n m, τ n m = τ m n := fun n m => by
    simp only [hτ]; rw [tau_natAbs_symm]
  -- row sums
  have hrow : ∀ n ∈ N, ∑ m ∈ N.erase n, τ n m ≤ W := by
    intro n hn
    have hnY : n ≤ Y := (Finset.mem_Icc.mp (hN hn)).2
    have hsub : N.erase n ⊆ (Finset.Icc 1 Y).erase n := Finset.erase_subset_erase n hN
    calc ∑ m ∈ N.erase n, τ n m
        ≤ ∑ m ∈ (Finset.Icc 1 Y).erase n, τ n m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hτnn n m)
      _ ≤ 2 * ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) := tau_rowSum_le Y n hnY
      _ ≤ W := by
          rw [hW]
          have := sum_tau_le Y hY
          linarith
  -- AM–GM termwise
  have hAM : ∀ n m, ‖c n‖ * ‖c m‖ * τ n m
      ≤ (‖c n‖ ^ 2 * τ n m + ‖c m‖ ^ 2 * τ n m) / 2 := by
    intro n m
    have h1 : ‖c n‖ * ‖c m‖ ≤ (‖c n‖ ^ 2 + ‖c m‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖c n‖ - ‖c m‖)]
    have h2 := hτnn n m
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  -- the symmetric double sum
  have hsymm : ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c m‖ ^ 2 * τ n m
      = ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ ^ 2 * τ n m := by
    rw [Finset.sum_comm' (t' := N) (s' := fun m => N.erase m)]
    · refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [hτsymm]
    · intro x y
      simp only [Finset.mem_erase]
      constructor
      · rintro ⟨hx, hyx, hy⟩; exact ⟨⟨Ne.symm hyx, hx⟩, hy⟩
      · rintro ⟨⟨hxy, hx⟩, hy⟩; exact ⟨hx, Ne.symm hxy, hy⟩
  calc ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ * ‖c m‖ * τ n m
      ≤ ∑ n ∈ N, ∑ m ∈ N.erase n, (‖c n‖ ^ 2 * τ n m + ‖c m‖ ^ 2 * τ n m) / 2 :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => hAM n m
    _ = ((∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ ^ 2 * τ n m)
          + ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c m‖ ^ 2 * τ n m) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ ^ 2 * τ n m := by rw [hsymm]; ring
    _ = ∑ n ∈ N, ‖c n‖ ^ 2 * ∑ m ∈ N.erase n, τ n m := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ N, ‖c n‖ ^ 2 * W :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg _)
    _ = W * ∑ n ∈ N, ‖c n‖ ^ 2 := by rw [← Finset.sum_mul]; ring

/-- **The generic mean value, both directions.** For `N ⊆ [1, Y]` and a pair-sum bound
`‖Σ_{q∈S}Σ*_χ χ(n)χ̄(m)‖ ≤ c_Q·τ(|n−m|)` (`n ≠ m`):
`| Σ_{q∈S}Σ*_χ ‖Σ_{n∈N} c_n χ(n)‖² − Σ_n ‖c_n‖²·N_S(n) | ≤ c_Q·2Y(1+log Y)·Σ_n ‖c_n‖²`. -/
theorem meanValue_generic (S N : Finset ℕ) (c : ℕ → ℂ) {cQ : ℝ} (hcQ : 0 ≤ cQ) (Y : ℕ)
    (hY : 1 ≤ Y) (hN : N ⊆ Finset.Icc 1 Y)
    (hpair : ∀ n m : ℕ, n ≠ m →
      ‖pairSumS S n m‖ ≤ cQ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)) :
    |(∑ q ∈ S, ∑ χ ∈ primitiveChars q, ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2)
        - ∑ n ∈ N, ‖c n‖ ^ 2 * famCountAt S n|
      ≤ cQ * (2 * ((Y : ℝ) * (1 + Real.log Y))) * ∑ n ∈ N, ‖c n‖ ^ 2 := by
  rw [famS_expand, add_sub_cancel_left]
  refine (offdiag_re_le S N c hpair).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (schur_tau N Y hY hN c) hcQ

/-- the upper half: `≤ (|𝔉_S| + c_Q·2Y(1+log Y))·‖c‖²`. -/
theorem meanValue_upper (S N : Finset ℕ) (c : ℕ → ℂ) {cQ : ℝ} (hcQ : 0 ≤ cQ) (Y : ℕ)
    (hY : 1 ≤ Y) (hN : N ⊆ Finset.Icc 1 Y)
    (hpair : ∀ n m : ℕ, n ≠ m →
      ‖pairSumS S n m‖ ≤ cQ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)) :
    (∑ q ∈ S, ∑ χ ∈ primitiveChars q, ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2)
      ≤ (sizeS S + cQ * (2 * ((Y : ℝ) * (1 + Real.log Y)))) * ∑ n ∈ N, ‖c n‖ ^ 2 := by
  have h := (abs_le.mp (meanValue_generic S N c hcQ Y hY hN hpair)).2
  have hd : ∑ n ∈ N, ‖c n‖ ^ 2 * famCountAt S n ≤ sizeS S * ∑ n ∈ N, ‖c n‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => by
      rw [mul_comm (sizeS S)]
      exact mul_le_mul_of_nonneg_left (famCountAt_le S n) (sq_nonneg _)
  nlinarith

/-- the lower half: `≥ Σ_n ‖c_n‖²·N_S(n) − c_Q·2Y(1+log Y)·‖c‖²`. -/
theorem meanValue_lower (S N : Finset ℕ) (c : ℕ → ℂ) {cQ : ℝ} (hcQ : 0 ≤ cQ) (Y : ℕ)
    (hY : 1 ≤ Y) (hN : N ⊆ Finset.Icc 1 Y)
    (hpair : ∀ n m : ℕ, n ≠ m →
      ‖pairSumS S n m‖ ≤ cQ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)) :
    (∑ n ∈ N, ‖c n‖ ^ 2 * famCountAt S n)
        - cQ * (2 * ((Y : ℝ) * (1 + Real.log Y))) * ∑ n ∈ N, ‖c n‖ ^ 2
      ≤ ∑ q ∈ S, ∑ χ ∈ primitiveChars q, ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2 := by
  have h := (abs_le.mp (meanValue_generic S N c hcQ Y hY hN hpair)).1
  linarith

/-! ## 2. The pair-sum bound for the two families of record -/

theorem one_le_tau {k : ℕ} (hk : k ≠ 0) : (1 : ℝ) ≤ (tau k : ℝ) := by
  have h : 1 ≤ tau k := by
    unfold tau
    exact Finset.card_pos.mpr ⟨k, Nat.mem_divisors_self k hk⟩
  exact_mod_cast h

theorem natAbs_sub_ne_zero {n m : ℕ} (hne : n ≠ m) : ((n : ℤ) - (m : ℤ)).natAbs ≠ 0 := by
  omega

/-- `‖Σ*_{χ mod 1} χ(n)χ̄(m)‖ ≤ 1`. -/
theorem norm_primPairSum_one_le (n m : ℕ) : ‖primPairSum 1 n m‖ ≤ 1 := by
  unfold primPairSum
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ χ ∈ primitiveChars 1, ‖χ (n : ZMod 1) * conj (χ (m : ZMod 1))‖ ≤ 1 := by
    intro χ _
    rw [norm_mul, RCLike.norm_conj]
    have h1 := χ.norm_le_one (n : ZMod 1)
    have h2 := χ.norm_le_one (m : ZMod 1)
    have h3 := norm_nonneg (χ (n : ZMod 1))
    nlinarith
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (primitiveChars 1).card = 1 := phiStar_one
  rw [this]; norm_num

theorem Icc_one_eq_insert (Qn : ℕ) (hQn : 1 ≤ Qn) :
    Finset.Icc 1 Qn = insert 1 (Finset.Icc 2 Qn) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- the `q ≤ Q` family of record (`q ∈ [2, Q]`). -/
theorem pairSumS_qle_le (Qn n m : ℕ) (hne : n ≠ m) :
    ‖pairSumS (Family.moduli Family.qle Qn) n m‖
      ≤ 2 * (Qn : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := by
  have hτ1 : (1 : ℝ) ≤ (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := one_le_tau (natAbs_sub_ne_zero hne)
  have hmod : Family.moduli Family.qle Qn = Finset.Icc 2 Qn := rfl
  rw [hmod]
  rcases Nat.eq_zero_or_pos Qn with h0 | hpos
  · subst h0
    simp [pairSumS]
  · have hfam : famPairSum Qn n m = primPairSum 1 n m + pairSumS (Finset.Icc 2 Qn) n m := by
      unfold famPairSum pairSumS
      rw [Icc_one_eq_insert Qn hpos, Finset.sum_insert (by simp)]
    have h1 := lemma5_2_crude Qn n m hne
    have h2 := norm_primPairSum_one_le n m
    have h3 : pairSumS (Finset.Icc 2 Qn) n m = famPairSum Qn n m - primPairSum 1 n m := by
      rw [hfam]; ring
    rw [h3]
    refine (norm_sub_le _ _).trans ?_
    have hQ1 : (1 : ℝ) ≤ Qn := by exact_mod_cast hpos
    nlinarith

/-- the dyadic family of record (`Q/2 < q ≤ Q`). -/
theorem pairSumS_dyadic_le (Qn n m : ℕ) (hne : n ≠ m) :
    ‖pairSumS (Family.moduli Family.dyadic Qn) n m‖
      ≤ 2 * (Qn : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := by
  have hmod : pairSumS (Family.moduli Family.dyadic Qn) n m = famPairSumDyadic Qn n m := rfl
  rw [hmod]
  refine (lemma5_2_crude_dyadic Qn n m hne).trans ?_
  have hτ0 : (0 : ℝ) ≤ (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ Qn := Nat.cast_nonneg _
  nlinarith

/-- **Lemma 5.2, crude, for the family of record**: `‖Σ_{χ∈𝔉_Q} χ(n)χ̄(m)‖ ≤ 2Q·τ(|n−m|)`. -/
theorem pairSumS_family_le (F : Family) (Qn n m : ℕ) (hne : n ≠ m) :
    ‖pairSumS (F.moduli Qn) n m‖
      ≤ 2 * (Qn : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := by
  cases F with
  | qle => exact pairSumS_qle_le Qn n m hne
  | dyadic => exact pairSumS_dyadic_le Qn n m hne
  -- the four Corollary 3 families reuse the two modulus ranges verbatim, and `pairSumS`
  -- reads `F` only through `F.moduli`.
  | evenQle => exact pairSumS_qle_le Qn n m hne
  | oddQle => exact pairSumS_qle_le Qn n m hne
  | evenDyadic => exact pairSumS_dyadic_le Qn n m hne
  | oddDyadic => exact pairSumS_dyadic_le Qn n m hne
  | evenQleR => exact pairSumS_qle_le Qn n m hne
  | oddQleR => exact pairSumS_qle_le Qn n m hne
  | evenDyadicR => exact pairSumS_dyadic_le Qn n m hne
  | oddDyadicR => exact pairSumS_dyadic_le Qn n m hne

/-- `|𝔉_S| = Σ_{q ∈ S} φ*(q)` at `S = F.moduli Qn` — TRUE in all six branches, by definition
of `sizeS`. This is the honest content of `sizeS_moduli` below. -/
theorem sizeS_moduli_eq (F : Family) (Qn : ℕ) :
    sizeS (F.moduli Qn) = ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) := rfl

/-- `|𝔉_S| = F.sizeR` at `S = F.moduli Qn`, for either FULL family.

**`F.IsFull` is now CARRIED.** `sizeS` counts ALL primitive characters of each modulus,
so for a parity family it is about twice `F.sizeR Qn` — precisely,
`|2·F.sizeR Qn − sizeS (F.moduli Qn)| ≤ Qn` by
`Budget.ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn`. An earlier form of this declaration
consumed the then-`sorry`ing `Budget.sizeR_eq_sum_phiStar` while generic in `F` and so
reached `sorryAx` silently. -/
theorem sizeS_moduli {F : Family} (hF : F.IsFull) (Qn : ℕ) :
    sizeS (F.moduli Qn) = F.sizeR Qn :=
  (sizeR_eq_sum_phiStar hF Qn).symm

/-! ## 3. Instantiation at the design: the in-zone coefficient vector `a′(s)` -/

/-- `Y_n := ⌊Y⌋₊ = ⌊Q^{1−δ′}⌋₊`. -/
def Yn (P : ParamsQ) : ℕ := ⌊P.zoneY⌋₊

/-- the in-zone index set `{n ≤ X : n ≤ Y}`. -/
def Nlow (P : ParamsQ) : Finset ℕ := (primeRangeQ P).filter (fun n => (n : ℝ) ≤ P.zoneY)

theorem Nlow_subset (P : ParamsQ) : Nlow P ⊆ Finset.Icc 1 (Yn P) := by
  intro n hn
  simp only [Nlow, primeRangeQ, Finset.mem_filter, Finset.mem_Ioc] at hn
  simp only [Finset.mem_Icc]
  exact ⟨hn.1.1, Nat.le_floor hn.2⟩

theorem one_le_Yn (P : ParamsQ) (hs0 : 0 ≤ P.s0) : 1 ≤ Yn P := by
  unfold Yn
  have h : (1 : ℝ) ≤ P.zoneY := by
    unfold ParamsQ.zoneY
    exact Real.one_le_exp hs0
  exact Nat.le_floor (by simpa using h)

/-- `A′_χ(s) = Σ_{n ∈ Nlow} a_n(s) χ(n)`. -/
theorem AchiC_low_eq (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℝ) :
    AchiC P (acoefLow P) χ s = ∑ n ∈ Nlow P, acoefS P n s * χ (n : ZMod q) := by
  unfold AchiC Nlow acoefLow
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- `‖a′(s)‖₂² = Σ_{n ∈ Nlow} ‖a_n(s)‖²`. -/
theorem normA2_low_eq (P : ParamsQ) (s : ℝ) :
    ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 = ∑ n ∈ Nlow P, ‖acoefS P n s‖ ^ 2 := by
  unfold Nlow acoefLow
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- **`ERR_in := 2Q·2Y_n(1 + log Y_n)`** — the explicit in-zone mean-value error coefficient
(relative to `|𝔉|`, this is `≍ Q^{−δ′}·log Q = (log Q)^{−2}`). -/
def ERRin (P : ParamsQ) (Qn : ℕ) : ℝ :=
  2 * (Qn : ℝ) * (2 * ((Yn P : ℝ) * (1 + Real.log (Yn P))))

theorem ERRin_nonneg (P : ParamsQ) (Qn : ℕ) (hs0 : 0 ≤ P.s0) : 0 ≤ ERRin P Qn := by
  unfold ERRin
  have h1 : (1 : ℝ) ≤ (Yn P : ℝ) := by exact_mod_cast one_le_Yn P hs0
  have h2 : 0 ≤ Real.log (Yn P : ℝ) := Real.log_nonneg h1
  positivity

/-- the coprimality-weighted in-zone diagonal at `s`:
`Σ_{n ≤ Y} ‖a_n(s)‖²·#{χ ∈ 𝔉 : (n, q_χ) = 1}`. -/
def diagLowW (F : Family) (Qn : ℕ) (P : ParamsQ) (s : ℝ) : ℝ :=
  ∑ n ∈ Nlow P, ‖acoefS P n s‖ ^ 2 * famCountAt (F.moduli Qn) n

/-- The honest, all-six-branches form: `diagLowW` is built from `famCountAt`, which counts ALL
primitive characters, so the bound it obeys is at `sizeS (F.moduli Qn) = Σ_q φ*(q)`. -/
theorem diagLowW_le_sizeS (F : Family) (Qn : ℕ) (P : ParamsQ) (s : ℝ) :
    diagLowW F Qn P s ≤ sizeS (F.moduli Qn) * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 := by
  unfold diagLowW
  rw [normA2_low_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [mul_comm (sizeS (F.moduli Qn))]
  exact mul_le_mul_of_nonneg_left (famCountAt_le _ n) (sq_nonneg _)

/-- **`F.IsFull` is now CARRIED** — see `sizeS_moduli`. For a parity family `diagLowW` is
still the FULL-family diagonal (`famCountAt` ranges over `ZetaQ.primitiveChars`) while
`F.sizeR Qn` is halved, so the bound as stated is FALSE there; `diagLowW_le_sizeS` above is
the version that holds in all six branches. -/
theorem diagLowW_le {F : Family} (hF : F.IsFull) (Qn : ℕ) (P : ParamsQ) (s : ℝ) :
    diagLowW F Qn P s ≤ F.sizeR Qn * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 := by
  rw [← sizeS_moduli hF Qn]
  exact diagLowW_le_sizeS F Qn P s

theorem diagLowW_nonneg (F : Family) (Qn : ℕ) (P : ParamsQ) (s : ℝ) : 0 ≤ diagLowW F Qn P s :=
  Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (famCountAt_nonneg _ n)

/-! ## 3′. THE PARITY IN-ZONE MEAN VALUE

`pairSumS` / `famCountAt` / `sizeS` above hard-code `primitiveChars q`. The four Corollary 3
families range over `F.chars q` — about half of that — and their off-diagonal kernel is
TWO-term rather than one-term. This section frees both.

**The one new piece of mathematics is a SHARP two-term Schur row bound.** The parity
per-modulus pair sum is `½(primPairSum ± primPairSumNeg)`, so

  `‖Σ_{q∈S} Σ_{χ ∈ sel q} χ(n)χ̄(m)‖ ≤ Q·τ(|n − m|) + Q·τ(n + m)`

(Lemma 5.2 + Lemma 5.2′, crude), where the full family has the ONE-term `2Q·τ(|n−m|)`.
`schur_tau` handles only the one-term kernel, and bounding the two rows SEPARATELY
(`Σ_{m≤Y} τ(|n−m|) ≤ 2Y(1+log Y)`, `Σ_{m≤Y} τ(n+m) ≤ 2Y(1+log 2Y)`) costs an extra `2QY·log 2`
— i.e. it proves the theorems only with `ERRin` enlarged. `row_two_le` removes that loss by
bounding the `m < n` branch of `τ(|n−m|)` and the whole `τ(n+m)` row JOINTLY: their images
under `m ↦ n − m` and `m ↦ n + m` are DISJOINT subsets of `[1, 2Y]` (`≤ n−1` versus `≥ n+1`),
while `m > n` lands in `[1, Y−n] ⊆ [1,Y]`. So the whole two-term row costs
`Σ_{k ≤ 2Y} τ(k) + Σ_{k ≤ Y} τ(k) ≤ 3Y(1+log Y) + 2Y log 2` against the budget
`ERRin/Q = 4Y(1 + log Y)`; the slack is `Y(1 + log Y) − 2Y log 2 ≥ 0` for `Y ≥ 2`, and `Y = 1`
empties the row. That is what makes the parity statements land at `ERRin` UNCHANGED.

Only `ZetaQ.sum_tau_le` is used, at `Y` and at `2Y` — no new arithmetic input. -/

/-! ### 3′.1 A character-SELECTED family -/

/-- A per-modulus selection of Dirichlet characters. -/
abbrev CharSel := ∀ q : ℕ, Finset (DirichletCharacter ℂ q)

/-- `Σ_{q∈S} Σ_{χ ∈ sel q} χ(n)χ̄(m)` — the pair sum over a character-selected family.
`sel := primitiveChars` recovers `pairSumS` by `rfl`. -/
def pairSumSel (sel : CharSel) (S : Finset ℕ) (n m : ℕ) : ℂ :=
  ∑ q ∈ S, ∑ χ ∈ sel q, χ (n : ZMod q) * conj (χ (m : ZMod q))

/-- `N_{sel,S}(n) := Σ_{q∈S} Σ_{χ ∈ sel q} ‖χ(n)‖²` — the coprimality-weighted count at `n`. -/
def famCountAtSel (sel : CharSel) (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ q ∈ S, ∑ χ ∈ sel q, ‖χ (n : ZMod q)‖ ^ 2

/-- `|𝔉_{sel,S}| := Σ_{q∈S} #(sel q)`. -/
def sizeSel (sel : CharSel) (S : Finset ℕ) : ℝ := ∑ q ∈ S, ((sel q).card : ℝ)

theorem pairSumSel_congr {sel sel' : CharSel} (h : ∀ q, sel q = sel' q) (S : Finset ℕ)
    (n m : ℕ) : pairSumSel sel S n m = pairSumSel sel' S n m := by
  unfold pairSumSel
  exact Finset.sum_congr rfl fun q _ => by rw [h q]

theorem famCountAtSel_nonneg (sel : CharSel) (S : Finset ℕ) (n : ℕ) :
    0 ≤ famCountAtSel sel S n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem famCountAtSel_le (sel : CharSel) (S : Finset ℕ) (n : ℕ) :
    famCountAtSel sel S n ≤ sizeSel sel S := by
  unfold famCountAtSel sizeSel
  refine Finset.sum_le_sum fun q _ => ?_
  calc ∑ χ ∈ sel q, ‖χ (n : ZMod q)‖ ^ 2
      ≤ ∑ _χ ∈ sel q, (1 : ℝ) := by
        refine Finset.sum_le_sum fun χ _ => ?_
        have h := χ.norm_le_one (n : ZMod q)
        have h0 := norm_nonneg (χ (n : ZMod q))
        nlinarith
    _ = _ := by simp

/-- `pairSumSel sel S n n = N_{sel,S}(n)`. -/
theorem pairSumSel_diag (sel : CharSel) (S : Finset ℕ) (n : ℕ) :
    pairSumSel sel S n n = ((famCountAtSel sel S n : ℝ) : ℂ) := by
  unfold pairSumSel famCountAtSel
  push_cast
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- the four-fold interchange, for a selected family. -/
theorem sum4_comm_sel (sel : CharSel) (S N M : Finset ℕ)
    (F : ∀ q : ℕ, DirichletCharacter ℂ q → ℕ → ℕ → ℝ) :
    (∑ q ∈ S, ∑ χ ∈ sel q, ∑ n ∈ N, ∑ m ∈ M, F q χ n m)
      = ∑ n ∈ N, ∑ m ∈ M, ∑ q ∈ S, ∑ χ ∈ sel q, F q χ n m := by
  calc (∑ q ∈ S, ∑ χ ∈ sel q, ∑ n ∈ N, ∑ m ∈ M, F q χ n m)
      = ∑ q ∈ S, ∑ n ∈ N, ∑ m ∈ M, ∑ χ ∈ sel q, F q χ n m :=
        Finset.sum_congr rfl fun q _ =>
          Finset.sum_comm.trans (Finset.sum_congr rfl fun n _ => Finset.sum_comm)
    _ = ∑ n ∈ N, ∑ q ∈ S, ∑ m ∈ M, ∑ χ ∈ sel q, F q χ n m := Finset.sum_comm
    _ = ∑ n ∈ N, ∑ m ∈ M, ∑ q ∈ S, ∑ χ ∈ sel q, F q χ n m :=
        Finset.sum_congr rfl fun n _ => Finset.sum_comm

/-- **The selected-family expansion**: diagonal plus off-diagonal (`famS_expand` with
`primitiveChars` replaced by `sel`). -/
theorem famSel_expand (sel : CharSel) (S N : Finset ℕ) (c : ℕ → ℂ) :
    (∑ q ∈ S, ∑ χ ∈ sel q, ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2)
      = ∑ n ∈ N, ‖c n‖ ^ 2 * famCountAtSel sel S n
        + (∑ n ∈ N, ∑ m ∈ N.erase n, c n * conj (c m) * pairSumSel sel S n m).re := by
  classical
  have h1 : (∑ q ∈ S, ∑ χ ∈ sel q, ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2)
      = ∑ n ∈ N, ∑ m ∈ N, (c n * conj (c m) * pairSumSel sel S n m).re := by
    have e1 : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2
        = ∑ n ∈ N, ∑ m ∈ N,
            (c n * conj (c m) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))).re :=
      fun q χ => normSq_charSum_eq χ N c
    have e2 : ∀ n m : ℕ, (c n * conj (c m) * pairSumSel sel S n m).re
        = ∑ q ∈ S, ∑ χ ∈ sel q,
            (c n * conj (c m) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))).re := by
      intro n m
      unfold pairSumSel
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum, Complex.re_sum]
    simp_rw [e1, e2]
    exact sum4_comm_sel sel S N N _
  rw [h1]
  have h2 : ∀ n ∈ N, ∑ m ∈ N, (c n * conj (c m) * pairSumSel sel S n m).re
      = ‖c n‖ ^ 2 * famCountAtSel sel S n
        + (∑ m ∈ N.erase n, c n * conj (c m) * pairSumSel sel S n m).re := by
    intro n hn
    rw [← Finset.add_sum_erase N _ hn, Complex.re_sum]
    congr 1
    rw [pairSumSel_diag, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Complex.re_sum]

/-! ### 3′.2 Schur/AM–GM for an arbitrary symmetric kernel

`schur_tau` inlines the kernel `τ(|n−m|)` and its row bound; the proof uses nothing about `τ`
beyond nonnegativity, symmetry and a uniform row bound. -/

/-- **Generic Schur bound.** For any kernel `K ≥ 0` symmetric in its two arguments whose rows
over `N` are bounded by `W`, `Σ_{n≠m∈N} |c_n||c_m| K(n,m) ≤ W·Σ_n |c_n|²`. -/
theorem schur_kernel (N : Finset ℕ) (K : ℕ → ℕ → ℝ) (W : ℝ) (c : ℕ → ℂ)
    (hKnn : ∀ n m, 0 ≤ K n m) (hKsymm : ∀ n m, K n m = K m n)
    (hrow : ∀ n ∈ N, ∑ m ∈ N.erase n, K n m ≤ W) :
    ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ * ‖c m‖ * K n m ≤ W * ∑ n ∈ N, ‖c n‖ ^ 2 := by
  classical
  have hAM : ∀ n m, ‖c n‖ * ‖c m‖ * K n m
      ≤ (‖c n‖ ^ 2 * K n m + ‖c m‖ ^ 2 * K n m) / 2 := by
    intro n m
    have h1 : ‖c n‖ * ‖c m‖ ≤ (‖c n‖ ^ 2 + ‖c m‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖c n‖ - ‖c m‖)]
    have h2 := hKnn n m
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  have hsymm : ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c m‖ ^ 2 * K n m
      = ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ ^ 2 * K n m := by
    rw [Finset.sum_comm' (t' := N) (s' := fun m => N.erase m)]
    · refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [hKsymm]
    · intro x y
      simp only [Finset.mem_erase]
      constructor
      · rintro ⟨hx, hyx, hy⟩; exact ⟨⟨Ne.symm hyx, hx⟩, hy⟩
      · rintro ⟨⟨hxy, hx⟩, hy⟩; exact ⟨hx, Ne.symm hxy, hy⟩
  calc ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ * ‖c m‖ * K n m
      ≤ ∑ n ∈ N, ∑ m ∈ N.erase n, (‖c n‖ ^ 2 * K n m + ‖c m‖ ^ 2 * K n m) / 2 :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => hAM n m
    _ = ((∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ ^ 2 * K n m)
          + ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c m‖ ^ 2 * K n m) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ ^ 2 * K n m := by rw [hsymm]; ring
    _ = ∑ n ∈ N, ‖c n‖ ^ 2 * ∑ m ∈ N.erase n, K n m := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ N, ‖c n‖ ^ 2 * W :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg _)
    _ = W * ∑ n ∈ N, ‖c n‖ ^ 2 := by rw [← Finset.sum_mul]; ring

/-! ### 3′.3 THE SHARP TWO-TERM ROW BOUND -/

theorem row_two_le (Y n : ℕ) (N : Finset ℕ) (hN : N ⊆ Finset.Icc 1 Y) (hn : n ∈ N) :
    ∑ m ∈ N.erase n, ((tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + (tau (n + m) : ℝ))
      ≤ (∑ k ∈ Finset.Icc 1 (2 * Y), (tau k : ℝ)) + ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) := by
  classical
  obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.mp (hN hn)
  have hEbd : ∀ m ∈ N.erase n, 1 ≤ m ∧ m ≤ Y ∧ m ≠ n := by
    intro m hm
    have h2 := Finset.mem_Icc.mp (hN (Finset.mem_of_mem_erase hm))
    exact ⟨h2.1, h2.2, Finset.ne_of_mem_erase hm⟩
  have hinjA : ∀ a ∈ (N.erase n).filter (fun m => m < n),
      ∀ b ∈ (N.erase n).filter (fun m => m < n), n - a = n - b → a = b := by
    intro a ha b hb hab
    have ha' : a < n := (Finset.mem_filter.mp ha).2
    have hb' : b < n := (Finset.mem_filter.mp hb).2
    omega
  have hinjB : ∀ a ∈ (N.erase n).filter (fun m => ¬ m < n),
      ∀ b ∈ (N.erase n).filter (fun m => ¬ m < n), a - n = b - n → a = b := by
    intro a ha b hb hab
    have ha' : ¬ a < n := (Finset.mem_filter.mp ha).2
    have ha'' := hEbd a (Finset.mem_filter.mp ha).1
    have hb' : ¬ b < n := (Finset.mem_filter.mp hb).2
    have hb'' := hEbd b (Finset.mem_filter.mp hb).1
    have ha3 : a ≠ n := ha''.2.2
    have hb3 : b ≠ n := hb''.2.2
    omega
  have hinjC : ∀ a ∈ N.erase n, ∀ b ∈ N.erase n, n + a = n + b → a = b := by
    intro a _ b _ hab; omega
  have hsumA : ∑ m ∈ (N.erase n).filter (fun m => m < n),
        (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
      = ∑ k ∈ ((N.erase n).filter (fun m => m < n)).image (fun m => n - m), (tau k : ℝ) := by
    rw [Finset.sum_image hinjA]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hlt : m < n := (Finset.mem_filter.mp hm).2
    have hnat : ((n : ℤ) - (m : ℤ)).natAbs = n - m := by omega
    rw [hnat]
  have hsumB : ∑ m ∈ (N.erase n).filter (fun m => ¬ m < n),
        (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
      = ∑ k ∈ ((N.erase n).filter (fun m => ¬ m < n)).image (fun m => m - n), (tau k : ℝ) := by
    rw [Finset.sum_image hinjB]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hge : ¬ m < n := (Finset.mem_filter.mp hm).2
    have hnat : ((n : ℤ) - (m : ℤ)).natAbs = m - n := by omega
    rw [hnat]
  have hsumC : ∑ m ∈ N.erase n, (tau (n + m) : ℝ)
      = ∑ k ∈ (N.erase n).image (fun m => n + m), (tau k : ℝ) := by
    rw [Finset.sum_image hinjC]
  have hdisj : Disjoint (((N.erase n).filter (fun m => m < n)).image (fun m => n - m))
      ((N.erase n).image (fun m => n + m)) := by
    rw [Finset.disjoint_left]
    intro k hkA hkC
    simp only [Finset.mem_image, Finset.mem_filter] at hkA hkC
    obtain ⟨a, ⟨haE, halt⟩, rfl⟩ := hkA
    obtain ⟨b, hbE, hb⟩ := hkC
    have hb1 := (hEbd b hbE).1
    omega
  have hsubAC : (((N.erase n).filter (fun m => m < n)).image (fun m => n - m))
      ∪ ((N.erase n).image (fun m => n + m)) ⊆ Finset.Icc 1 (2 * Y) := by
    intro k hk
    rw [Finset.mem_union] at hk
    simp only [Finset.mem_Icc]
    rcases hk with hk | hk
    · simp only [Finset.mem_image, Finset.mem_filter] at hk
      obtain ⟨a, ⟨haE, halt⟩, rfl⟩ := hk
      have ha := hEbd a haE
      omega
    · simp only [Finset.mem_image] at hk
      obtain ⟨b, hbE, rfl⟩ := hk
      have hb := hEbd b hbE
      omega
  have hsubB : ((N.erase n).filter (fun m => ¬ m < n)).image (fun m => m - n)
      ⊆ Finset.Icc 1 Y := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_filter] at hk
    obtain ⟨b, ⟨hbE, hbge⟩, rfl⟩ := hk
    have hb := hEbd b hbE
    simp only [Finset.mem_Icc]
    have hb3 : b ≠ n := hb.2.2
    omega
  calc ∑ m ∈ N.erase n, ((tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + (tau (n + m) : ℝ))
      = (∑ m ∈ N.erase n, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ))
          + ∑ m ∈ N.erase n, (tau (n + m) : ℝ) := Finset.sum_add_distrib
    _ = ((∑ m ∈ (N.erase n).filter (fun m => m < n),
              (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ))
          + ∑ m ∈ (N.erase n).filter (fun m => ¬ m < n),
              (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ))
          + ∑ m ∈ N.erase n, (tau (n + m) : ℝ) := by
        rw [Finset.sum_filter_add_sum_filter_not]
    _ = ((∑ k ∈ ((N.erase n).filter (fun m => m < n)).image (fun m => n - m), (tau k : ℝ))
            + ∑ k ∈ (N.erase n).image (fun m => n + m), (tau k : ℝ))
          + ∑ k ∈ ((N.erase n).filter (fun m => ¬ m < n)).image (fun m => m - n),
              (tau k : ℝ) := by
        rw [hsumA, hsumB, hsumC]; ring
    _ = (∑ k ∈ (((N.erase n).filter (fun m => m < n)).image (fun m => n - m))
              ∪ ((N.erase n).image (fun m => n + m)), (tau k : ℝ))
          + ∑ k ∈ ((N.erase n).filter (fun m => ¬ m < n)).image (fun m => m - n),
              (tau k : ℝ) := by
        rw [Finset.sum_union hdisj]
    _ ≤ (∑ k ∈ Finset.Icc 1 (2 * Y), (tau k : ℝ)) + ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) :=
        add_le_add
          (Finset.sum_le_sum_of_subset_of_nonneg hsubAC fun k _ _ => Nat.cast_nonneg _)
          (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun k _ _ => Nat.cast_nonneg _)

/-- **The two-term row bound at the `ERR_in` budget.** For `N ⊆ [1,Y]`, `n ∈ N` and `c_q ≥ 0`,
`Σ_{m ∈ N \ {n}} (c_q τ(|n−m|) + c_q τ(n+m)) ≤ 2c_q·2Y(1 + log Y)` — the SAME right-hand side
`schur_tau` uses for the one-term kernel with `c_Q = 2c_q`, hence the same `ERRin`. -/
theorem row_two_bound (Y n : ℕ) (hY : 1 ≤ Y) (N : Finset ℕ) (hN : N ⊆ Finset.Icc 1 Y)
    (hn : n ∈ N) {cq : ℝ} (hcq : 0 ≤ cq) :
    ∑ m ∈ N.erase n, (cq * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + cq * (tau (n + m) : ℝ))
      ≤ 2 * cq * (2 * ((Y : ℝ) * (1 + Real.log (Y : ℝ)))) := by
  classical
  have hfactor : ∑ m ∈ N.erase n,
        (cq * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + cq * (tau (n + m) : ℝ))
      = cq * ∑ m ∈ N.erase n,
          ((tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + (tau (n + m) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hfactor]
  rcases Nat.lt_or_ge Y 2 with hY1 | hY2
  · have hYeq : Y = 1 := by omega
    have hempty : N.erase n = (∅ : Finset ℕ) := by
      refine Finset.subset_empty.mp fun m hm => ?_
      exfalso
      have h2 := Finset.mem_Icc.mp (hN (Finset.mem_of_mem_erase hm))
      have h3 := Finset.mem_Icc.mp (hN hn)
      have h4 : m ≠ n := Finset.ne_of_mem_erase hm
      omega
    rw [hempty, Finset.sum_empty, mul_zero]
    have h1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have h2 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg h1
    positivity
  · have hY0 : (0 : ℝ) < (Y : ℝ) := by
      have : (0 : ℕ) < Y := by omega
      exact_mod_cast this
    have hY2R : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY2
    have hlog2Y : Real.log (2 * (Y : ℝ)) = Real.log 2 + Real.log (Y : ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hY0)
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog2leY : Real.log 2 ≤ Real.log (Y : ℝ) := Real.log_le_log (by norm_num) hY2R
    have hS2Y := sum_tau_le (2 * Y) (by omega)
    have hcast : ((2 * Y : ℕ) : ℝ) = 2 * (Y : ℝ) := by push_cast; ring
    rw [hcast, hlog2Y] at hS2Y
    have hSY := sum_tau_le Y hY
    have hrow := row_two_le Y n N hN hn
    have hbudget : (∑ k ∈ Finset.Icc 1 (2 * Y), (tau k : ℝ))
        + ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ)
        ≤ 2 * (2 * ((Y : ℝ) * (1 + Real.log (Y : ℝ)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog2le1 (le_of_lt hY0),
        mul_le_mul_of_nonneg_left hlog2leY (le_of_lt hY0)]
    calc cq * ∑ m ∈ N.erase n,
            ((tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + (tau (n + m) : ℝ))
        ≤ cq * ((∑ k ∈ Finset.Icc 1 (2 * Y), (tau k : ℝ))
            + ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ)) := mul_le_mul_of_nonneg_left hrow hcq
      _ ≤ cq * (2 * (2 * ((Y : ℝ) * (1 + Real.log (Y : ℝ))))) :=
          mul_le_mul_of_nonneg_left hbudget hcq
      _ = 2 * cq * (2 * ((Y : ℝ) * (1 + Real.log (Y : ℝ)))) := by ring

/-- the one-term row bound (`c₂ = 0`) at the `ERR_in` budget — `tau_rowSum_le` packaged for
`meanValue_generic_W`. -/
theorem row_one_bound (Y n : ℕ) (hY : 1 ≤ Y) (N : Finset ℕ) (hN : N ⊆ Finset.Icc 1 Y)
    (hn : n ∈ N) {cq : ℝ} (hcq : 0 ≤ cq) :
    ∑ m ∈ N.erase n, (cq * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + 0 * (tau (n + m) : ℝ))
      ≤ cq * (2 * ((Y : ℝ) * (1 + Real.log (Y : ℝ)))) := by
  have hnY : n ≤ Y := (Finset.mem_Icc.mp (hN hn)).2
  have hsubE : N.erase n ⊆ (Finset.Icc 1 Y).erase n := Finset.erase_subset_erase n hN
  have h1 : ∑ m ∈ N.erase n, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
      ≤ 2 * ((Y : ℝ) * (1 + Real.log (Y : ℝ))) := by
    calc ∑ m ∈ N.erase n, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
        ≤ ∑ m ∈ (Finset.Icc 1 Y).erase n, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubE fun m _ _ => Nat.cast_nonneg _
      _ ≤ 2 * ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) := tau_rowSum_le Y n hnY
      _ ≤ 2 * ((Y : ℝ) * (1 + Real.log (Y : ℝ))) := by have := sum_tau_le Y hY; linarith
  have hz : ∑ m ∈ N.erase n,
        (cq * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + 0 * (tau (n + m) : ℝ))
      = cq * ∑ m ∈ N.erase n, (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hz]
  exact mul_le_mul_of_nonneg_left h1 hcq

/-! ### 3′.4 The generalised mean value

`offdiag_re_le` / `meanValue_generic` with the character set and the kernel both freed.

**Added hypotheses, deliberately.** The two-term `hpair` carries `1 ≤ n` and `1 ≤ m` where
`offdiag_re_le`'s carries only `n ≠ m`. That is NOT a convenience: `ZetaQ.lemma5_2'_crude` —
the only available bound on `famPairSumNeg` — genuinely requires `1 ≤ n`, `1 ≤ m`, because
`τ(n + m)` is `τ(0) = 0` at `n = m = 0` while the character sum is not. The hypothesis is free
at the point of use: `N ⊆ Finset.Icc 1 Y` already forces `1 ≤ n` for every `n ∈ N`. -/

/-- the off-diagonal under the two-term pair bound. -/
theorem offdiag_re_le_two (sel : CharSel) (S N : Finset ℕ) (c : ℕ → ℂ) {c₁ c₂ : ℝ}
    (hN1 : ∀ n ∈ N, 1 ≤ n)
    (hpair : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n ≠ m →
      ‖pairSumSel sel S n m‖
        ≤ c₁ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + c₂ * (tau (n + m) : ℝ)) :
    |(∑ n ∈ N, ∑ m ∈ N.erase n, c n * conj (c m) * pairSumSel sel S n m).re|
      ≤ ∑ n ∈ N, ∑ m ∈ N.erase n, ‖c n‖ * ‖c m‖ *
          (c₁ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + c₂ * (tau (n + m) : ℝ)) := by
  classical
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun n hn => ?_
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun m hm => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  have hne : n ≠ m := (Finset.ne_of_mem_erase hm).symm
  have hmN : m ∈ N := Finset.mem_of_mem_erase hm
  have h0 : (0 : ℝ) ≤ ‖c n‖ * ‖c m‖ := by positivity
  exact mul_le_mul_of_nonneg_left (hpair n m (hN1 n hn) (hN1 m hmN) hne) h0

/-- **THE GENERALISED IN-ZONE MEAN VALUE, at an abstract row bound `W`.** For any per-modulus
character selection `sel`, any finite `S` of moduli, any `N` of indices `≥ 1`, and a TWO-TERM
off-diagonal bound `‖Σ_{q∈S} Σ_{χ ∈ sel q} χ(n)χ̄(m)‖ ≤ c₁·τ(|n−m|) + c₂·τ(n+m)`:

`| Σ_{q∈S} Σ_{χ ∈ sel q} ‖Σ_{n∈N} c_n χ(n)‖² − Σ_n ‖c_n‖²·N_{sel,S}(n) | ≤ W·Σ_n ‖c_n‖²`. -/
theorem meanValue_generic_W (sel : CharSel) (S N : Finset ℕ) (c : ℕ → ℂ) {c₁ c₂ W : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hN1 : ∀ n ∈ N, 1 ≤ n)
    (hrow : ∀ n ∈ N, ∑ m ∈ N.erase n,
        (c₁ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + c₂ * (tau (n + m) : ℝ)) ≤ W)
    (hpair : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n ≠ m →
      ‖pairSumSel sel S n m‖
        ≤ c₁ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + c₂ * (tau (n + m) : ℝ)) :
    |(∑ q ∈ S, ∑ χ ∈ sel q, ‖∑ n ∈ N, c n * χ (n : ZMod q)‖ ^ 2)
        - ∑ n ∈ N, ‖c n‖ ^ 2 * famCountAtSel sel S n|
      ≤ W * ∑ n ∈ N, ‖c n‖ ^ 2 := by
  rw [famSel_expand, add_sub_cancel_left]
  refine (offdiag_re_le_two sel S N c hN1 hpair).trans ?_
  refine schur_kernel N
    (fun n m => c₁ * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + c₂ * (tau (n + m) : ℝ)) W c
    (fun n m => add_nonneg (mul_nonneg hc₁ (Nat.cast_nonneg _))
      (mul_nonneg hc₂ (Nat.cast_nonneg _)))
    (fun n m => by rw [tau_natAbs_symm n m, Nat.add_comm n m]) hrow

/-! ### 3′.5 The parity pair bound over the families of record -/

/-- `Σ_{q∈S} Σ*_χ χ(−1)χ(n)χ̄(m)` — the parity-twisted pair sum over an arbitrary `S`. -/
def pairSumSNeg (S : Finset ℕ) (n m : ℕ) : ℂ := ∑ q ∈ S, primPairSumNeg q n m

/-- the even projector, over an arbitrary set of moduli. -/
theorem pairSumSel_even_eq (S : Finset ℕ) (n m : ℕ) :
    pairSumSel primitiveCharsEven S n m = (pairSumS S n m + pairSumSNeg S n m) / 2 := by
  have hq : ∀ q : ℕ, (∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q) * conj (χ (m : ZMod q)))
      = (primPairSum q n m + primPairSumNeg q n m) / 2 := fun q => primPairSum_even_eq q n m
  unfold pairSumSel pairSumS pairSumSNeg
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun q _ => hq q

/-- the odd projector, over an arbitrary set of moduli. -/
theorem pairSumSel_odd_eq (S : Finset ℕ) (n m : ℕ) :
    pairSumSel primitiveCharsOdd S n m = (pairSumS S n m - pairSumSNeg S n m) / 2 := by
  have hq : ∀ q : ℕ, (∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q) * conj (χ (m : ZMod q)))
      = (primPairSum q n m - primPairSumNeg q n m) / 2 := fun q => primPairSum_odd_eq q n m
  unfold pairSumSel pairSumS pairSumSNeg
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun q _ => hq q

/-- `‖Σ*_{χ mod 1} χ(−1)χ(n)χ̄(m)‖ ≤ 1` — the `q = 1` correction, mirroring
`norm_primPairSum_one_le`. -/
theorem norm_primPairSumNeg_one_le (n m : ℕ) : ‖primPairSumNeg 1 n m‖ ≤ 1 := by
  unfold primPairSumNeg
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ χ ∈ primitiveChars 1,
      ‖χ (-1 : ZMod 1) * (χ (n : ZMod 1) * conj (χ (m : ZMod 1)))‖ ≤ 1 := by
    intro χ _
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    have h1 := χ.norm_le_one (-1 : ZMod 1)
    have h2 := χ.norm_le_one (n : ZMod 1)
    have h3 := χ.norm_le_one (m : ZMod 1)
    have n1 := norm_nonneg (χ (-1 : ZMod 1))
    have n2 := norm_nonneg (χ (n : ZMod 1))
    have n3 := norm_nonneg (χ (m : ZMod 1))
    have hbc0 : (0 : ℝ) ≤ ‖χ (n : ZMod 1)‖ * ‖χ (m : ZMod 1)‖ := mul_nonneg n2 n3
    have hbc : ‖χ (n : ZMod 1)‖ * ‖χ (m : ZMod 1)‖ ≤ 1 := by nlinarith
    linarith [mul_le_mul_of_nonneg_right h1 hbc0]
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : (primitiveChars 1).card = 1 := phiStar_one
  rw [hc]
  norm_num

/-- Lemma 5.2′, crude, over `q ∈ [2, Q]` (the `qle` / `evenQle` / `oddQle` modulus range). -/
theorem pairSumSNeg_Icc2_le (Qn n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖pairSumSNeg (Finset.Icc 2 Qn) n m‖ ≤ 2 * (Qn : ℝ) * (tau (n + m) : ℝ) := by
  have hτ1 : (1 : ℝ) ≤ (tau (n + m) : ℝ) := one_le_tau (by omega)
  rcases Nat.eq_zero_or_pos Qn with h0 | hpos
  · subst h0
    simp [pairSumSNeg]
  · have hfam : famPairSumNeg Qn n m
        = primPairSumNeg 1 n m + pairSumSNeg (Finset.Icc 2 Qn) n m := by
      unfold famPairSumNeg pairSumSNeg
      rw [Icc_one_eq_insert Qn hpos, Finset.sum_insert (by simp)]
    have h1 := lemma5_2'_crude Qn n m hn hm
    have h2 := norm_primPairSumNeg_one_le n m
    have h3 : pairSumSNeg (Finset.Icc 2 Qn) n m
        = famPairSumNeg Qn n m - primPairSumNeg 1 n m := by
      rw [hfam]; ring
    rw [h3]
    refine (norm_sub_le _ _).trans ?_
    have hQ1 : (1 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hpos
    nlinarith

/-- Lemma 5.2′, crude, over the dyadic range. -/
theorem pairSumSNeg_Ioc_le (Qn n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖pairSumSNeg (Finset.Ioc (Qn / 2) Qn) n m‖ ≤ 2 * (Qn : ℝ) * (tau (n + m) : ℝ) := by
  have hmod : pairSumSNeg (Finset.Ioc (Qn / 2) Qn) n m = famPairSumNegDyadic Qn n m := rfl
  rw [hmod]
  refine (lemma5_2'_crude_dyadic Qn n m hn hm).trans ?_
  have hQ0 : (0 : ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (tau (n + m) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **Lemma 5.2′, crude, for the family of record** — all SIX branches, mirroring
`pairSumS_family_le`: the four Corollary 3 families reuse the two modulus ranges verbatim, and
`pairSumSNeg` reads `F` only through `F.moduli`. -/
theorem pairSumSNeg_family_le (F : Family) (Qn n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖pairSumSNeg (F.moduli Qn) n m‖ ≤ 2 * (Qn : ℝ) * (tau (n + m) : ℝ) := by
  cases F with
  | qle => exact pairSumSNeg_Icc2_le Qn n m hn hm
  | dyadic => exact pairSumSNeg_Ioc_le Qn n m hn hm
  | evenQle => exact pairSumSNeg_Icc2_le Qn n m hn hm
  | oddQle => exact pairSumSNeg_Icc2_le Qn n m hn hm
  | evenDyadic => exact pairSumSNeg_Ioc_le Qn n m hn hm
  | oddDyadic => exact pairSumSNeg_Ioc_le Qn n m hn hm
  | evenQleR => exact pairSumSNeg_Icc2_le Qn n m hn hm
  | oddQleR => exact pairSumSNeg_Icc2_le Qn n m hn hm
  | evenDyadicR => exact pairSumSNeg_Ioc_le Qn n m hn hm
  | oddDyadicR => exact pairSumSNeg_Ioc_le Qn n m hn hm

theorem norm_two_complex : ‖(2 : ℂ)‖ = 2 := by norm_num

/-- **The two-term pair bound for the EVEN primitive family of record**:
`‖Σ_{q∈𝔉} Σ_{χ even prim mod q} χ(n)χ̄(m)‖ ≤ Q·τ(|n−m|) + Q·τ(n+m)`. -/
theorem pairSumSel_even_family_le (F : Family) (Qn n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hne : n ≠ m) :
    ‖pairSumSel primitiveCharsEven (F.moduli Qn) n m‖
      ≤ (Qn : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + (Qn : ℝ) * (tau (n + m) : ℝ) := by
  rw [pairSumSel_even_eq, norm_div, norm_two_complex]
  have h1 := pairSumS_family_le F Qn n m hne
  have h2 := pairSumSNeg_family_le F Qn n m hn hm
  have h3 := norm_add_le (pairSumS (F.moduli Qn) n m) (pairSumSNeg (F.moduli Qn) n m)
  linarith

/-- **The two-term pair bound for the ODD primitive family of record.** -/
theorem pairSumSel_odd_family_le (F : Family) (Qn n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hne : n ≠ m) :
    ‖pairSumSel primitiveCharsOdd (F.moduli Qn) n m‖
      ≤ (Qn : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + (Qn : ℝ) * (tau (n + m) : ℝ) := by
  rw [pairSumSel_odd_eq, norm_div, norm_two_complex]
  have h1 := pairSumS_family_le F Qn n m hne
  have h2 := pairSumSNeg_family_le F Qn n m hn hm
  have h3 := norm_sub_le (pairSumS (F.moduli Qn) n m) (pairSumSNeg (F.moduli Qn) n m)
  linarith

/-- **The two-term pair bound at `Family.chars`, for each of Corollary 3's four families.**
This is the `hpair` that `meanValue_generic_W` consumes, with `c₁ = c₂ = Q`. The bridge from
`F.chars` to §5's parity classes is `ZetaQ.chars_parity_of_not_isFull` (`Zones.lean`), the one
canonical version. -/
theorem pairSumSel_chars_family_le (F : Family) (hF : ¬ F.IsFull) (Qn n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hne : n ≠ m) :
    ‖pairSumSel F.chars (F.moduli Qn) n m‖
      ≤ (Qn : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + (Qn : ℝ) * (tau (n + m) : ℝ) := by
  rcases chars_parity_of_not_isFull hF with h | h
  · rw [pairSumSel_congr h]
    exact pairSumSel_even_family_le F Qn n m hn hm hne
  · rw [pairSumSel_congr h]
    exact pairSumSel_odd_family_le F Qn n m hn hm hne

/-- at a FULL family `pairSumSel F.chars` IS `pairSumS`, so Lemma 5.2 crude applies with
`c₁ = 2Q`, `c₂ = 0`. -/
theorem pairSumSel_chars_full_le {F : Family} (hF : F.IsFull) (Qn n m : ℕ) (hne : n ≠ m) :
    ‖pairSumSel F.chars (F.moduli Qn) n m‖
      ≤ 2 * (Qn : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) + 0 * (tau (n + m) : ℝ) := by
  rw [pairSumSel_congr (F.chars_eq_of_isFull hF)]
  have hrfl : pairSumSel primitiveChars (F.moduli Qn) n m = pairSumS (F.moduli Qn) n m := rfl
  rw [hrfl, zero_mul, add_zero]
  exact pairSumS_family_le F Qn n m hne

/-! ### 3′.6 The family's OWN diagonal

`diagLowW`'s weight is `famCountAt`, which runs over the FULL primitive set at every `F`, while
the left-hand side of the mean value runs over `F.chars q` — about half of it on a parity
family. The gap is `≈ ½·|𝔉|·‖a′‖²`, a MAIN term against an `ERRin`-sized budget
(`ERRin_le_sizeR`), so `inZone_meanValue_pointwise` at `diagLowW` is FALSE for large `Q` at a
parity family, not merely unproved. `diagLowWFam` is the honest object; it IS `diagLowW` on
`qle` / `dyadic` (`diagLowWFam_eq_diagLowW_of_isFull`). -/

/-- the family's own coprimality-weighted in-zone diagonal at `s`. -/
def diagLowWFam (F : Family) (Qn : ℕ) (P : ParamsQ) (s : ℝ) : ℝ :=
  ∑ n ∈ Nlow P, ‖acoefS P n s‖ ^ 2 * famCountAtSel F.chars (F.moduli Qn) n

theorem famCountAtSel_chars_eq (F : Family) (Qn n : ℕ) :
    famCountAtSel F.chars (F.moduli Qn) n
      = familySum F Qn (fun q χ => ‖χ (n : ZMod q)‖ ^ 2) := rfl

theorem diagLowWFam_eq (F : Family) (Qn : ℕ) (P : ParamsQ) (s : ℝ) :
    diagLowWFam F Qn P s
      = ∑ n ∈ Nlow P, ‖acoefS P n s‖ ^ 2 * familySum F Qn (fun q χ => ‖χ (n : ZMod q)‖ ^ 2) :=
  rfl

/-- at a FULL family the re-weighted diagonal IS `diagLowW`. -/
theorem diagLowWFam_eq_diagLowW_of_isFull {F : Family} (hF : F.IsFull) (Qn : ℕ) (P : ParamsQ)
    (s : ℝ) : diagLowWFam F Qn P s = diagLowW F Qn P s := by
  unfold diagLowWFam diagLowW famCountAtSel famCountAt
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun q _ => by rw [F.chars_eq_of_isFull hF]

theorem diagLowWFam_nonneg (F : Family) (Qn : ℕ) (P : ParamsQ) (s : ℝ) :
    0 ≤ diagLowWFam F Qn P s :=
  Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (famCountAtSel_nonneg _ _ n)

/-- `Σ_{q ∈ F.moduli Qn} |F.chars q| = F.sizeR Qn` — `Family.size_eq`, cast to `ℝ`. -/
theorem sizeSel_chars_eq (F : Family) (Qn : ℕ) :
    sizeSel F.chars (F.moduli Qn) = F.sizeR Qn := by
  unfold sizeSel Family.sizeR
  rw [Family.size_eq]
  push_cast
  ring

/-- **the parity counterpart of `diagLowW_le`, with NO `F.IsFull`** — the family's own diagonal
is bounded by the family's own size. -/
theorem diagLowWFam_le (F : Family) (Qn : ℕ) (P : ParamsQ) (s : ℝ) :
    diagLowWFam F Qn P s ≤ F.sizeR Qn * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 := by
  unfold diagLowWFam
  rw [normA2_low_eq, ← sizeSel_chars_eq F Qn, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [mul_comm (sizeSel F.chars (F.moduli Qn))]
  exact mul_le_mul_of_nonneg_left (famCountAtSel_le _ _ n) (sq_nonneg _)

/-- **THE IN-ZONE MEAN VALUE, POINTWISE IN `s`, BOTH DIRECTIONS — ALL SIX FAMILIES.**
`| Σ_{χ∈𝔉_Q} |A′_χ(s)|² − Σ_{n≤Y} ‖a_n(s)‖²·N_𝔉(n) | ≤ ERR_in·‖a′(s)‖₂²`, with `ERR_in`
UNCHANGED and no `F.IsFull`.

**This is a CHANGE OF OBJECT, and it is a correction, not a weakening.** The statement used to
subtract `diagLowW`, whose weight `famCountAt` runs over the FULL primitive set at every `F`,
while the left-hand `familySum F Qn` runs over `F.chars q` — about half of it on a parity
family. The gap is `≈ ½·|𝔉|·‖a′‖²`, a MAIN term against an `ERR_in`-sized budget
(`ERRin_le_sizeR`), so the old statement was FALSE for large `Q` there, not merely unproved.
`diagLowWFam` is the family's own diagonal; `inZone_meanValue_pointwise_of_isFull` just below
recovers the previous statement, `diagLowW` and all, on `qle` / `dyadic`.

The `by_cases hF : F.IsFull` survives only as a choice of KERNEL: both branches run through the
same `meanValue_generic_W`, the full families at the one-term `c₁ = 2Q`, `c₂ = 0` and the
parity families at the two-term `c₁ = c₂ = Q` with the sharp row bound `row_two_bound`. No
`InZoneProjector` packaging is needed — the file goes through the pair bounds directly.

*Import-graph note (the previous docstring got this backwards).*
`ZetaQ.Normalisation.InZoneProjector` IS on this file's import path, via
`InZone → FrobAssembly → Budget → Zones → Normalisation`. What is genuinely out of scope is
`ZetaQ/EvenFam.lean` itself, which is a terminal consumer imported only by the umbrella root;
nothing here needs it. -/
theorem inZone_meanValue_pointwise (F : Family) (Qn : ℕ) (P : ParamsQ) (hs0 : 0 ≤ P.s0)
    (s : ℝ) :
    |familySum F Qn (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2) - diagLowWFam F Qn P s|
      ≤ ERRin P Qn * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 := by
  have hY : 1 ≤ Yn P := one_le_Yn P hs0
  have hfs : familySum F Qn (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2)
      = ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
          ‖∑ n ∈ Nlow P, acoefS P n s * χ (n : ZMod q)‖ ^ 2 := by
    unfold familySum
    exact Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun χ _ => by
        show ‖AchiC P (acoefLow P) χ s‖ ^ 2 = _
        rw [AchiC_low_eq]
  by_cases hF : F.IsFull
  · have h := meanValue_generic_W F.chars (F.moduli Qn) (Nlow P) (fun n => acoefS P n s)
      (c₁ := 2 * (Qn : ℝ)) (c₂ := 0) (W := ERRin P Qn)
      (by positivity) le_rfl
      (fun n hn => (Finset.mem_Icc.mp (Nlow_subset P hn)).1)
      (fun n hn => row_one_bound (Yn P) n hY (Nlow P) (Nlow_subset P) hn (by positivity))
      (fun n m _ _ hne => pairSumSel_chars_full_le hF Qn n m hne)
    rw [hfs, normA2_low_eq]
    exact h
  · have h := meanValue_generic_W F.chars (F.moduli Qn) (Nlow P) (fun n => acoefS P n s)
      (c₁ := (Qn : ℝ)) (c₂ := (Qn : ℝ)) (W := ERRin P Qn)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (fun n hn => (Finset.mem_Icc.mp (Nlow_subset P hn)).1)
      (fun n hn => row_two_bound (Yn P) n hY (Nlow P) (Nlow_subset P) hn (Nat.cast_nonneg _))
      (fun n m hn hm hne => pairSumSel_chars_family_le F hF Qn n m hn hm hne)
    rw [hfs, normA2_low_eq]
    exact h

/-- receipt: on a FULL family `inZone_meanValue_pointwise` IS the tree's previous statement,
`diagLowW` and all. Existing full-family consumers cite this. -/
theorem inZone_meanValue_pointwise_of_isFull {F : Family} (hF : F.IsFull) (Qn : ℕ)
    (P : ParamsQ) (hs0 : 0 ≤ P.s0) (s : ℝ) :
    |familySum F Qn (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2) - diagLowW F Qn P s|
      ≤ ERRin P Qn * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 := by
  rw [← diagLowWFam_eq_diagLowW_of_isFull hF Qn P s]
  exact inZone_meanValue_pointwise F Qn P hs0 s

/-- the upper half: `Σ_{χ∈𝔉_Q} |A′_χ(s)|² ≤ (|𝔉_Q| + ERR_in)·‖a′(s)‖₂²`. -/
theorem inZone_meanValue_upper (F : Family) (Qn : ℕ) (P : ParamsQ) (hs0 : 0 ≤ P.s0) (s : ℝ) :
    familySum F Qn (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2)
      ≤ (F.sizeR Qn + ERRin P Qn) * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 := by
  have h := (abs_le.mp (inZone_meanValue_pointwise F Qn P hs0 s)).2
  have hd := diagLowWFam_le F Qn P s
  linarith

/-- the lower half, at the family's own diagonal. -/
theorem inZone_meanValue_lower (F : Family) (Qn : ℕ) (P : ParamsQ) (hs0 : 0 ≤ P.s0) (s : ℝ) :
    diagLowWFam F Qn P s - ERRin P Qn * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2
      ≤ familySum F Qn (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2) := by
  have h := (abs_le.mp (inZone_meanValue_pointwise F Qn P hs0 s)).1
  linarith

/-! ## 4. Integration against `g` over `U = {|s| ≤ s₀}` -/

/-- the in-zone family form over the family of record at an arbitrary coefficient family. -/
def inFormF (F : Family) (Qn : ℕ) (P : ParamsQ) (c : ℕ → ℝ → ℂ) : ℝ :=
  familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖AchiC P c χ s‖ ^ 2)

theorem inFormF_nonneg (F : Family) (Qn : ℕ) (P : ParamsQ) (c : ℕ → ℝ → ℂ) :
    0 ≤ inFormF F Qn P c := by
  unfold inFormF familySum
  refine Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun χ _ => ?_
  exact setIntegral_nonneg (measurableSet_inZone P) fun s _ =>
    mul_nonneg (lemma42_g_nonneg P s) (sq_nonneg _)

theorem famSum_normSq_continuous (F : Family) (Qn : ℕ) (P : ParamsQ) (c : ℕ → ℝ → ℂ)
    (hc : ∀ n, Continuous (c n)) :
    Continuous (fun s => familySum F Qn (fun _ χ => ‖AchiC P c χ s‖ ^ 2)) := by
  unfold familySum
  exact continuous_finsetSum _ fun q _ => continuous_finsetSum _ fun χ _ =>
    (AchiC_continuous P c hc χ).norm.pow 2

/-- the family sum and the zone integral commute. -/
theorem inFormF_eq_integral (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (c : ℕ → ℝ → ℂ) (hc : ∀ n, Continuous (c n)) :
    inFormF F Qn P c
      = ∫ s in inZone P, P.gQ s * familySum F Qn (fun _ χ => ‖AchiC P c χ s‖ ^ 2) := by
  unfold inFormF familySum
  have hint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      IntegrableOn (fun s => P.gQ s * ‖AchiC P c χ s‖ ^ 2) (inZone P) :=
    fun q χ => gQ_AchiC_integrableOn P hP hw c hc χ _
  dsimp only
  have e : ∀ s : ℝ, P.gQ s * ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, ‖AchiC P c χ s‖ ^ 2
      = ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, P.gQ s * ‖AchiC P c χ s‖ ^ 2 := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
  simp_rw [e]
  rw [MeasureTheory.integral_finsetSum _ (fun q _ =>
    MeasureTheory.integrable_finsetSum _ fun χ _ => hint q χ)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun χ _ => hint q χ)]

/-- **The integrated in-zone mean value, upper half**:
`Σ_{χ∈𝔉_Q} ∫_U g|A′_χ|² ≤ (|𝔉_Q| + ERR_in)·P`, `P = zoneP = ∫_U g‖a′‖₂²`. -/
theorem inFormF_low_le (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hs0 : 0 ≤ P.s0) :
    inFormF F Qn P (acoefLow P) ≤ (F.sizeR Qn + ERRin P Qn) * zoneP P := by
  rw [inFormF_eq_integral F Qn P hP hw _ (acoefLow_continuous P)]
  unfold zoneP
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ (measurableSet_inZone P) ?_
  · exact (gQ_mul_integrable P hP hw
      (famSum_normSq_continuous F Qn P _ (acoefLow_continuous P))).integrableOn
  · exact (gQ_coefSum_integrableOn P hP hw _ (acoefLow_continuous P) _).const_mul _
  · intro s _
    have h := inZone_meanValue_upper F Qn P hs0 s
    have hg := lemma42_g_nonneg P s
    calc P.gQ s * familySum F Qn (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2)
        ≤ P.gQ s * ((F.sizeR Qn + ERRin P Qn) * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hg
      _ = _ := by ring

theorem diagLowW_continuous (F : Family) (Qn : ℕ) (P : ParamsQ) :
    Continuous (fun s => diagLowW F Qn P s) := by
  unfold diagLowW
  exact continuous_finsetSum _ fun n _ =>
    ((acoefS_continuous P n).norm.pow 2).mul continuous_const

theorem diagLowWFam_continuous (F : Family) (Qn : ℕ) (P : ParamsQ) :
    Continuous (fun s => diagLowWFam F Qn P s) := by
  unfold diagLowWFam
  exact continuous_finsetSum _ fun n _ =>
    ((acoefS_continuous P n).norm.pow 2).mul continuous_const

/-- **The integrated in-zone mean value, both directions**:
`| Σ_{χ∈𝔉_Q} ∫_U g|A′_χ|² − ∫_U g·Σ_{n≤Y}‖a_n‖²N_𝔉(n) | ≤ ERR_in·zoneP`.
At the family's own diagonal `diagLowWFam`, matching `inZone_meanValue_pointwise`. -/
theorem inFormF_low_two_sided (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hs0 : 0 ≤ P.s0) :
    |inFormF F Qn P (acoefLow P) - ∫ s in inZone P, P.gQ s * diagLowWFam F Qn P s|
      ≤ ERRin P Qn * zoneP P := by
  rw [inFormF_eq_integral F Qn P hP hw _ (acoefLow_continuous P)]
  have hi1 : IntegrableOn
      (fun s => P.gQ s * familySum F Qn (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2))
      (inZone P) :=
    (gQ_mul_integrable P hP hw
      (famSum_normSq_continuous F Qn P _ (acoefLow_continuous P))).integrableOn
  have hi2 : IntegrableOn (fun s => P.gQ s * diagLowWFam F Qn P s) (inZone P) :=
    (gQ_mul_integrable P hP hw (diagLowWFam_continuous F Qn P)).integrableOn
  have hi3 : IntegrableOn
      (fun s => ERRin P Qn * (P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2))
      (inZone P) :=
    (gQ_coefSum_integrableOn P hP hw _ (acoefLow_continuous P) _).const_mul _
  rw [← MeasureTheory.integral_sub hi1 hi2]
  unfold zoneP
  rw [← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
  refine MeasureTheory.norm_integral_le_of_norm_le hi3 ?_
  refine Filter.Eventually.of_forall fun s => ?_
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (lemma42_g_nonneg P s)]
  have h := inZone_meanValue_pointwise F Qn P hs0 s
  have hg := lemma42_g_nonneg P s
  calc P.gQ s * |familySum F Qn (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2) - diagLowWFam F Qn P s|
      ≤ P.gQ s * (ERRin P Qn * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h hg
    _ = _ := by ring

/-! ## 5. Lemma 4.4's `a′/a″` split over the family of record, and the `a″` sieve -/

theorem AchiC_split (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℝ) :
    AchiC P (acoefS P) χ s = AchiC P (acoefLow P) χ s + AchiC P (acoefHigh P) χ s := by
  unfold AchiC
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold acoefLow acoefHigh
  by_cases h : (n : ℝ) ≤ P.zoneY <;> simp [h]

theorem normSq_Achi_split_le (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ‖AchiC P (acoefS P) χ s‖ ^ 2
      ≤ (1 + ε) * ‖AchiC P (acoefLow P) χ s‖ ^ 2
        + (1 + 1 / ε) * ‖AchiC P (acoefHigh P) χ s‖ ^ 2 := by
  have htri : ‖AchiC P (acoefS P) χ s‖
      ≤ ‖AchiC P (acoefLow P) χ s‖ + ‖AchiC P (acoefHigh P) χ s‖ := by
    rw [AchiC_split P χ s]; exact norm_add_le _ _
  have hsq : ‖AchiC P (acoefS P) χ s‖ ^ 2
      ≤ (‖AchiC P (acoefLow P) χ s‖ + ‖AchiC P (acoefHigh P) χ s‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have heps := sq_add_le_eps (a := ‖AchiC P (acoefLow P) χ s‖)
    (b := ‖AchiC P (acoefHigh P) χ s‖) hε
  linarith

/-- **The CS step over the family of record**: `F_𝔉(a) ≤ (1+ε)F_𝔉(a′) + (1+1/ε)F_𝔉(a″)`. -/
theorem inFormF_split (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) {ε : ℝ} (hε : 0 < ε) :
    inFormF F Qn P (acoefS P)
      ≤ (1 + ε) * inFormF F Qn P (acoefLow P) + (1 + 1 / ε) * inFormF F Qn P (acoefHigh P) := by
  classical
  have hUm : MeasurableSet (inZone P) := measurableSet_inZone P
  have hper : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (∫ s in inZone P, P.gQ s * ‖AchiC P (acoefS P) χ s‖ ^ 2)
        ≤ (1 + ε) * (∫ s in inZone P, P.gQ s * ‖AchiC P (acoefLow P) χ s‖ ^ 2)
          + (1 + 1 / ε) * (∫ s in inZone P, P.gQ s * ‖AchiC P (acoefHigh P) χ s‖ ^ 2) := by
    intro q χ
    have i1 := gQ_AchiC_integrableOn P hP hw _ (acoefS_continuous P) χ (inZone P)
    have i2 := gQ_AchiC_integrableOn P hP hw _ (acoefLow_continuous P) χ (inZone P)
    have i3 := gQ_AchiC_integrableOn P hP hw _ (acoefHigh_continuous P) χ (inZone P)
    have hRint : IntegrableOn
        (fun s => (1 + ε) * (P.gQ s * ‖AchiC P (acoefLow P) χ s‖ ^ 2)
          + (1 + 1 / ε) * (P.gQ s * ‖AchiC P (acoefHigh P) χ s‖ ^ 2)) (inZone P) :=
      (i2.const_mul (1 + ε)).add (i3.const_mul (1 + 1 / ε))
    have hmono := setIntegral_mono_on i1 hRint hUm (fun s _ => by
      have hg := lemma42_g_nonneg P s
      have h := normSq_Achi_split_le P χ s hε
      nlinarith [mul_le_mul_of_nonneg_left h hg])
    rwa [MeasureTheory.integral_add (i2.const_mul _) (i3.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  unfold inFormF familySum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun χ _ => hper q χ

/-- **Lemma 6.1 on the `a″` half, family of record**: `F_𝔉(a″) ≤ (X + Q² − 1)·zoneR`. -/
theorem inFormF_high_le (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊) :
    inFormF F Qn P (acoefHigh P) ≤ sieveBudgetQ P * zoneR P := by
  refine le_trans ?_ (inZoneFormFam_high_le P hP hw hLS)
  unfold inFormF inZoneFormFam
  exact familySum_le_famSum P F Qn hQn _ fun q χ =>
    setIntegral_nonneg (measurableSet_inZone P) fun s _ =>
      mul_nonneg (lemma42_g_nonneg P s) (sq_nonneg _)

/-- **Lemma 4.4 over the family of record, in-zone coefficient `|𝔉_Q|`:**
`Σ_{χ∈𝔉_Q} ∫_U g|A_χ|² ≤ (1+ε)(|𝔉_Q| + ERR_in)·P + (1+1/ε)(X+Q²−1)·R` for every `ε > 0`. -/
theorem inFormF_full_le (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊) (hs0 : 0 ≤ P.s0)
    {ε : ℝ} (hε : 0 < ε) :
    inFormF F Qn P (acoefS P)
      ≤ (1 + ε) * ((F.sizeR Qn + ERRin P Qn) * zoneP P)
        + (1 + 1 / ε) * (sieveBudgetQ P * zoneR P) := by
  have h1 := inFormF_split F Qn P hP hw hε
  have h2 := inFormF_low_le F Qn P hP hw hs0
  have h3 := inFormF_high_le F Qn P hP hw hLS hQn
  have hε1 : 0 ≤ 1 + ε := by linarith
  have hε2 : 0 ≤ 1 + 1 / ε := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hε1, mul_le_mul_of_nonneg_left h3 hε2]

/-! ## 6. The mirror `s ↦ −s` for the `B`-half (Lemma 4.3: "the `s < 0` half is identical") -/

theorem bcoefS_continuous (P : ParamsQ) (n : ℕ) : Continuous (fun s => bcoefS P n s) := by
  unfold bcoefS
  exact continuous_const.mul ((DT_continuous P).comp (continuous_id.add continuous_const))

theorem Bchi_continuous (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (fun s => Bchi P χ s) := by
  unfold Bchi BchiC
  exact continuous_finsetSum _ fun n _ => (bcoefS_continuous P n).mul continuous_const

theorem Achi_continuous (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (fun s => Achi P χ s) :=
  AchiC_continuous P _ (acoefS_continuous P) χ

/-- `B_χ(s) = conj(A_χ(−s))` — the band-separation identity at the level of the sums. -/
theorem Bchi_eq_conj_Achi_neg (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℝ) :
    Bchi P χ s = conj (Achi P χ (-s)) := by
  unfold Bchi BchiC Achi AchiC
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, lemma43_band_separation]

theorem norm_Bchi_eq (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℝ) :
    ‖Bchi P χ s‖ = ‖Achi P χ (-s)‖ := by
  rw [Bchi_eq_conj_Achi_neg, RCLike.norm_conj]

/-- the zone integral of the `B`-half equals that of the `A`-half (`g` even, `U` symmetric). -/
theorem integral_inZone_B_eq_A (P : ParamsQ) (hs0 : 0 ≤ P.s0) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∫ s in inZone P, P.gQ s * ‖Bchi P χ s‖ ^ 2)
      = ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2 := by
  rw [inZone_eq_Icc]
  have hle : (-P.s0 : ℝ) ≤ P.s0 := by linarith
  have h1 : Set.EqOn (fun s : ℝ => P.gQ s * ‖Bchi P χ s‖ ^ 2)
      (fun s : ℝ => P.gQ (-s) * ‖Achi P χ (-s)‖ ^ 2) (Set.Icc (-P.s0) P.s0) := by
    intro s _
    show P.gQ s * ‖Bchi P χ s‖ ^ 2 = P.gQ (-s) * ‖Achi P χ (-s)‖ ^ 2
    rw [lemma42_g_even, norm_Bchi_eq]
  rw [setIntegral_congr_fun measurableSet_Icc h1,
    MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
  have hcn := intervalIntegral.integral_comp_neg (a := (-P.s0 : ℝ)) (b := P.s0)
    (f := fun t : ℝ => P.gQ t * ‖Achi P χ t‖ ^ 2)
  rw [neg_neg] at hcn
  exact hcn

/-- the whole-line version. -/
theorem integral_B_eq_A (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2) = ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2 := by
  have h1 : (fun s : ℝ => P.gQ s * ‖Bchi P χ s‖ ^ 2)
      = fun s : ℝ => (fun t => P.gQ t * ‖Achi P χ t‖ ^ 2) (-s) := by
    funext s
    simp only [lemma42_g_even, norm_Bchi_eq]
  rw [h1]
  exact MeasureTheory.integral_neg_eq_self (fun t : ℝ => P.gQ t * ‖Achi P χ t‖ ^ 2) volume

/-- `∫ g‖b‖₂² = ∫ g‖a‖₂²` on the whole line. -/
theorem integral_normB2_eq_normA2 (P : ParamsQ) :
    (∫ s : ℝ, P.gQ s * normB2 P s) = ∫ s : ℝ, P.gQ s * normA2 P s := by
  have h1 : (fun s : ℝ => P.gQ s * normB2 P s)
      = fun s : ℝ => (fun t => P.gQ t * normA2 P t) (-s) := by
    funext s
    simp only [lemma42_g_even, lemma43_normB_mirror]
  rw [h1]
  exact MeasureTheory.integral_neg_eq_self (fun t : ℝ => P.gQ t * normA2 P t) volume

/-! ## 7. The χ/χ̄ cross term over the family of record (CS-in-χ + Lemma 6.1, pointwise) -/

/-- pointwise in `s`, for the subfamily `𝔉_Q ⊆ {q ≤ ⌊Q⌋₊}`:
`|Σ_{χ∈𝔉_Q} 2Re(A_χ conj B_χ)| ≤ 2(X + Q² − 1)‖a(s)‖₂‖b(s)‖₂`. -/
theorem cross_pointwise_family (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊) (s : ℝ) :
    |familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re)|
      ≤ 2 * sieveBudgetQ P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
  have hb : (0 : ℝ) ≤ sieveBudgetQ P := sieveBudgetQ_nonneg P hP
  have habs : |familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re)|
      ≤ familySum F Qn (fun _ χ => 2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)) := by
    unfold familySum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun q _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun χ _ => ?_
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc |(Achi P χ s * conj (Bchi P χ s)).re|
        ≤ ‖Achi P χ s * conj (Bchi P χ s)‖ := Complex.abs_re_le_norm _
      _ = ‖Achi P χ s‖ * ‖Bchi P χ s‖ := by rw [norm_mul, RCLike.norm_conj]
  have hsub : familySum F Qn (fun _ χ => 2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖))
      ≤ famSum P (fun _ χ => 2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)) :=
    familySum_le_famSum P F Qn hQn _ fun q χ => by positivity
  have hCS : famSum P (fun q χ => ‖Achi P χ s‖ * ‖Bchi P χ s‖)
      ≤ Real.sqrt (famSum P (fun _ χ => ‖Achi P χ s‖ ^ 2))
        * Real.sqrt (famSum P (fun _ χ => ‖Bchi P χ s‖ ^ 2)) :=
    famSum_cauchy_schwarz P (fun _ χ => ‖Achi P χ s‖) (fun _ χ => ‖Bchi P χ s‖)
  have hsA : Real.sqrt (famSum P (fun _ χ => ‖Achi P χ s‖ ^ 2))
      ≤ Real.sqrt (sieveBudgetQ P) * Real.sqrt (normA2 P s) := by
    rw [← Real.sqrt_mul hb]
    exact Real.sqrt_le_sqrt (lemma43_sieve_half_A P hP hLS s)
  have hsB : Real.sqrt (famSum P (fun _ χ => ‖Bchi P χ s‖ ^ 2))
      ≤ Real.sqrt (sieveBudgetQ P) * Real.sqrt (normB2 P s) := by
    rw [← Real.sqrt_mul hb]
    exact Real.sqrt_le_sqrt (lemma43_sieve_half_B P hP hLS s)
  have hprod : Real.sqrt (famSum P (fun _ χ => ‖Achi P χ s‖ ^ 2))
        * Real.sqrt (famSum P (fun _ χ => ‖Bchi P χ s‖ ^ 2))
      ≤ (Real.sqrt (sieveBudgetQ P) * Real.sqrt (normA2 P s))
        * (Real.sqrt (sieveBudgetQ P) * Real.sqrt (normB2 P s)) :=
    mul_le_mul hsA hsB (Real.sqrt_nonneg _) (by positivity)
  have hsq : (Real.sqrt (sieveBudgetQ P) * Real.sqrt (normA2 P s))
        * (Real.sqrt (sieveBudgetQ P) * Real.sqrt (normB2 P s))
      = sieveBudgetQ P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
    rw [show (Real.sqrt (sieveBudgetQ P) * Real.sqrt (normA2 P s))
            * (Real.sqrt (sieveBudgetQ P) * Real.sqrt (normB2 P s))
          = (Real.sqrt (sieveBudgetQ P) * Real.sqrt (sieveBudgetQ P))
            * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) by ring,
      Real.mul_self_sqrt hb]
  calc |familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re)|
      ≤ famSum P (fun _ χ => 2 * (‖Achi P χ s‖ * ‖Bchi P χ s‖)) := habs.trans hsub
    _ = 2 * famSum P (fun q χ => ‖Achi P χ s‖ * ‖Bchi P χ s‖) :=
        famSum_const_mul P 2 (fun _ χ => ‖Achi P χ s‖ * ‖Bchi P χ s‖)
    _ ≤ 2 * (sieveBudgetQ P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))) := by
        refine mul_le_mul_of_nonneg_left ((hCS.trans hprod).trans (le_of_eq hsq)) (by norm_num)
    _ = 2 * sieveBudgetQ P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by ring

theorem gQ_cross_integrableOn (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (U : Set ℝ) :
    IntegrableOn (fun s => P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) U :=
  (gQ_mul_integrable P hP hw (Complex.continuous_re.comp
    ((Achi_continuous P χ).mul (Complex.continuous_conj.comp (Bchi_continuous P χ))))).integrableOn

/-- the integrated cross term over any measurable `U`, family of record:
`|Σ_{χ∈𝔉_Q} 2∫_U g Re(A_χ conj B_χ)| ≤ 2(X + Q² − 1)∫_U g‖a‖₂‖b‖₂`. -/
theorem cross_integral_family (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊)
    (U : Set ℝ) (hU : MeasurableSet U) :
    |familySum F Qn (fun _ χ => 2 * ∫ s in U, P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)|
      ≤ 2 * sieveBudgetQ P
          * ∫ s in U, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s) := by
  classical
  have hintC : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      IntegrableOn (fun s => P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) U :=
    fun q χ => gQ_cross_integrableOn P hP hw χ U
  obtain ⟨-, -, hintX, -, -, -⟩ := rho_integrability P hP hw
  -- exchange the family sum with the integral
  have hex : familySum F Qn (fun _ χ => 2 * ∫ s in U, P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)
      = ∫ s in U, ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
          2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) := by
    unfold familySum
    rw [MeasureTheory.integral_finsetSum _ (fun q _ =>
      MeasureTheory.integrable_finsetSum _ fun χ _ => (hintC q χ).const_mul 2)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun χ _ => (hintC q χ).const_mul 2)]
    exact Finset.sum_congr rfl fun χ _ => (MeasureTheory.integral_const_mul 2 _).symm
  have hpt : ∀ s : ℝ,
      |∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
          2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)|
        ≤ 2 * sieveBudgetQ P
            * (P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by
    intro s
    have hg := lemma42_g_nonneg P s
    have hpull : (∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
          2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re))
        = P.gQ s * familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re) := by
      unfold familySum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [hpull, abs_mul, abs_of_nonneg hg]
    have hcross := cross_pointwise_family F Qn P hP hLS hQn s
    calc P.gQ s * |familySum F Qn (fun _ χ => 2 * (Achi P χ s * conj (Bchi P χ s)).re)|
        ≤ P.gQ s
            * (2 * sieveBudgetQ P * (Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))) :=
          mul_le_mul_of_nonneg_left hcross hg
      _ = 2 * sieveBudgetQ P
            * (P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)) := by ring
  have hintH : IntegrableOn (fun s => ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
      2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)) U :=
    MeasureTheory.integrable_finsetSum _ fun q _ =>
      MeasureTheory.integrable_finsetSum _ fun χ _ => (hintC q χ).const_mul 2
  have hRint : IntegrableOn (fun s => 2 * sieveBudgetQ P
      * (P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))) U :=
    hintX.integrableOn.const_mul _
  rw [hex, ← MeasureTheory.integral_const_mul, abs_le]
  refine ⟨?_, setIntegral_mono_on hintH hRint hU fun s _ => (abs_le.mp (hpt s)).2⟩
  have hlow := setIntegral_mono_on hRint.neg hintH hU fun s _ => (abs_le.mp (hpt s)).1
  simp only [Pi.neg_apply] at hlow
  rwa [MeasureTheory.integral_neg] at hlow

/-! ## 8. The in-zone PP form at in-zone coefficient `|𝔉_Q|` (Parts 1+2 assembled) -/

theorem gQ_Fwin_sq_integrableOn (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (U : Set ℝ) :
    IntegrableOn (fun s => P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) U :=
  (gQ_mul_integrable P hP hw
    ((FrobAssembly.Fwin_continuous P (FrobAssembly.PXchi_continuous P χ)).norm.pow 2)).integrableOn

theorem gQ_Achi_sq_integrableOn (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (U : Set ℝ) :
    IntegrableOn (fun s => P.gQ s * ‖Achi P χ s‖ ^ 2) U :=
  (gQ_mul_integrable P hP hw ((Achi_continuous P χ).norm.pow 2)).integrableOn

theorem gQ_Bchi_sq_integrableOn (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (U : Set ℝ) :
    IntegrableOn (fun s => P.gQ s * ‖Bchi P χ s‖ ^ 2) U :=
  (gQ_mul_integrable P hP hw ((Bchi_continuous P χ).norm.pow 2)).integrableOn

/-- the per-character zone expansion `∫_U g|F_χ|² = ∫_U g|A|² + ∫_U g|B|² + 2∫_U g Re(A conj B)`. -/
theorem zone_expansion (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (U : Set ℝ) :
    (∫ s in U, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      = (∫ s in U, P.gQ s * ‖Achi P χ s‖ ^ 2) + (∫ s in U, P.gQ s * ‖Bchi P χ s‖ ^ 2)
        + 2 * ∫ s in U, P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re := by
  have hT : (0 : ℝ) ≤ P.T := hP.T_pos.le
  have e : (fun s => P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      = fun s => P.gQ s * ‖Achi P χ s‖ ^ 2 + P.gQ s * ‖Bchi P χ s‖ ^ 2
          + 2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) := by
    funext s
    rw [lemma45_expansion P hT χ hχ s]
    ring
  have hAB : IntegrableOn (fun s => P.gQ s * ‖Achi P χ s‖ ^ 2 + P.gQ s * ‖Bchi P χ s‖ ^ 2) U :=
    (gQ_Achi_sq_integrableOn P hP hw χ U).add (gQ_Bchi_sq_integrableOn P hP hw χ U)
  have hC : IntegrableOn (fun s => 2 * (P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re)) U :=
    (gQ_cross_integrableOn P hP hw χ U).const_mul 2
  rw [e, MeasureTheory.integral_add hAB hC,
    MeasureTheory.integral_add (gQ_Achi_sq_integrableOn P hP hw χ U)
      (gQ_Bchi_sq_integrableOn P hP hw χ U), MeasureTheory.integral_const_mul]

theorem familySum_add' (F : Family) (Qn : ℕ) (f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    familySum F Qn (fun q χ => f q χ + g q χ) = familySum F Qn f + familySum F Qn g := by
  unfold familySum
  simp only [Finset.sum_add_distrib]

/-- membership in the family sum is membership in `primitiveChars`: a congruence lemma. -/
theorem familySum_congr_prim (F : Family) (Qn : ℕ) {f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ}
    (h : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ.IsPrimitive → f q χ = g q χ) :
    familySum F Qn f = familySum F Qn g := by
  unfold familySum
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ hχ =>
    h q χ (isPrimitive_of_mem_primitiveChars (F.chars_subset q hχ))

/-- **THE IN-ZONE PP FORM, FAMILY OF RECORD (Part 2).** For every `ε > 0`:
`Σ_{χ∈𝔉_Q} ∫_U g|F_χ|² ≤ 2[(1+ε)(|𝔉_Q| + ERR_in)·P + (1+1/ε)(X+Q²−1)·R] + 2(X+Q²−1)∫_U g‖a‖₂‖b‖₂`,
where `∫_U g(‖a‖²+‖b‖²) = 2(P + R)` and `2∫_U g‖a‖‖b‖ = ρ_U·∫_U g(‖a‖²+‖b‖²)`: i.e. the in-zone
form is `≤ [(1+ε)(|𝔉_Q| + ERR_in) + (X+Q²−1)ρ_U]·∫_U g(‖a‖²+‖b‖²) + 2(1+1/ε)(X+Q²−1)R`. -/
theorem famPP_inZone_le (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊) (hs0 : 0 ≤ P.s0)
    {ε : ℝ} (hε : 0 < ε) :
    familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      ≤ 2 * ((1 + ε) * ((F.sizeR Qn + ERRin P Qn) * zoneP P)
            + (1 + 1 / ε) * (sieveBudgetQ P * zoneR P))
        + 2 * sieveBudgetQ P
            * ∫ s in inZone P, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s) := by
  have hexp : familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      = familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Bchi P χ s‖ ^ 2)
        + familySum F Qn (fun _ χ => 2 * ∫ s in inZone P,
            P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) := by
    rw [← familySum_add', ← familySum_add']
    exact familySum_congr_prim F Qn fun q χ hχ => zone_expansion P hP hw χ hχ _
  have hB : familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Bchi P χ s‖ ^ 2)
      = inFormF F Qn P (acoefS P) := by
    unfold inFormF
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact integral_inZone_B_eq_A P hs0 χ
  have hA : familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = inFormF F Qn P (acoefS P) := rfl
  have hfull := inFormF_full_le F Qn P hP hw hLS hQn hs0 hε
  have hcross := (abs_le.mp (cross_integral_family F Qn P hP hw hLS hQn (inZone P)
    (measurableSet_inZone P))).2
  rw [hexp, hA, hB]
  linarith

/-- `∫_U g(‖a‖₂² + ‖b‖₂²) = 2(P + R)` — the in-zone diagonal in Lemma 4.4's `P`, `R`. -/
theorem zone_diag_eq (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (hs0 : 0 ≤ P.s0) :
    (∫ s in inZone P, P.gQ s * (normA2 P s + normB2 P s)) = 2 * (zoneP P + zoneR P) := by
  have hsplit : ∀ s : ℝ, normA2 P s
      = (∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2) + ∑ n ∈ primeRangeQ P, ‖acoefHigh P n s‖ ^ 2 := by
    intro s
    unfold normA2
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold acoefLow acoefHigh
    by_cases h : (n : ℝ) ≤ P.zoneY <;> simp [h]
  have hT : (0 : ℝ) ≤ P.T := hP.T_pos.le
  have hiA : IntegrableOn (fun s => P.gQ s * normA2 P s) (inZone P) :=
    (gQ_mul_integrable P hP hw (normA2_continuous P hT)).integrableOn
  have hiB : IntegrableOn (fun s => P.gQ s * normB2 P s) (inZone P) :=
    (gQ_mul_integrable P hP hw (normB2_continuous P hT)).integrableOn
  have hiL : IntegrableOn (fun s => P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2) (inZone P) :=
    gQ_coefSum_integrableOn P hP hw _ (acoefLow_continuous P) _
  have hiH : IntegrableOn (fun s => P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefHigh P n s‖ ^ 2) (inZone P) :=
    gQ_coefSum_integrableOn P hP hw _ (acoefHigh_continuous P) _
  have e1 : (fun s => P.gQ s * (normA2 P s + normB2 P s))
      = fun s => P.gQ s * normA2 P s + P.gQ s * normB2 P s := by funext s; ring
  have e2 : (fun s => P.gQ s * normA2 P s)
      = fun s => P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2
        + P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefHigh P n s‖ ^ 2 := by
    funext s; rw [hsplit s]; ring
  have hBA : (∫ s in inZone P, P.gQ s * normB2 P s) = ∫ s in inZone P, P.gQ s * normA2 P s := by
    rw [inZone_eq_Icc]; exact zone_normB_eq_normA P hs0
  rw [e1, MeasureTheory.integral_add hiA hiB, hBA]
  unfold zoneP zoneR
  rw [e2, MeasureTheory.integral_add hiL hiH]
  ring

/-- `∫_U g‖a‖₂² = P + R`. -/
theorem zone_normA2_eq (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    (∫ s in inZone P, P.gQ s * normA2 P s) = zoneP P + zoneR P := by
  have hsplit : ∀ s : ℝ, normA2 P s
      = (∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2) + ∑ n ∈ primeRangeQ P, ‖acoefHigh P n s‖ ^ 2 := by
    intro s
    unfold normA2
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold acoefLow acoefHigh
    by_cases h : (n : ℝ) ≤ P.zoneY <;> simp [h]
  have hiL : IntegrableOn (fun s => P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2) (inZone P) :=
    gQ_coefSum_integrableOn P hP hw _ (acoefLow_continuous P) _
  have hiH : IntegrableOn (fun s => P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefHigh P n s‖ ^ 2) (inZone P) :=
    gQ_coefSum_integrableOn P hP hw _ (acoefHigh_continuous P) _
  have e2 : (fun s => P.gQ s * normA2 P s)
      = fun s => P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2
        + P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefHigh P n s‖ ^ 2 := by
    funext s; rw [hsplit s]; ring
  unfold zoneP zoneR
  rw [e2, MeasureTheory.integral_add hiL hiH]

/-! ## 9. The total PP block, pointwise: in-zone at `|𝔉_Q|`, out-zone at the sieve,
cross term over the whole line (Part 3, the master inequality at one design point) -/

/-- the family sum and a zone integral commute (any measurable set, any continuous
coefficient family). -/
theorem famForm_eq_integral (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (c : ℕ → ℝ → ℂ) (hc : ∀ n, Continuous (c n)) (U : Set ℝ) :
    familySum F Qn (fun _ χ => ∫ s in U, P.gQ s * ‖AchiC P c χ s‖ ^ 2)
      = ∫ s in U, P.gQ s * familySum F Qn (fun _ χ => ‖AchiC P c χ s‖ ^ 2) := by
  unfold familySum
  have hint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      IntegrableOn (fun s => P.gQ s * ‖AchiC P c χ s‖ ^ 2) U :=
    fun q χ => gQ_AchiC_integrableOn P hP hw c hc χ _
  dsimp only
  have e : ∀ s : ℝ, P.gQ s * ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, ‖AchiC P c χ s‖ ^ 2
      = ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, P.gQ s * ‖AchiC P c χ s‖ ^ 2 := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
  simp_rw [e]
  rw [MeasureTheory.integral_finsetSum _ (fun q _ =>
    MeasureTheory.integrable_finsetSum _ fun χ _ => hint q χ)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun χ _ => hint q χ)]

/-- the sieve on the `A`-half over any measurable `U`, family of record:
`Σ_{χ∈𝔉_Q} ∫_U g|A_χ|² ≤ (X + Q² − 1)∫_U g‖a‖₂²`. -/
theorem famA_integral_le (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊)
    (U : Set ℝ) (hU : MeasurableSet U) :
    familySum F Qn (fun _ χ => ∫ s in U, P.gQ s * ‖Achi P χ s‖ ^ 2)
      ≤ sieveBudgetQ P * ∫ s in U, P.gQ s * normA2 P s := by
  have hT : (0 : ℝ) ≤ P.T := hP.T_pos.le
  have e := famForm_eq_integral F Qn P hP hw (acoefS P) (acoefS_continuous P) U
  unfold Achi
  rw [e, ← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ hU fun s _ => ?_
  · exact (gQ_mul_integrable P hP hw
      (famSum_normSq_continuous F Qn P _ (acoefS_continuous P))).integrableOn
  · exact ((gQ_mul_integrable P hP hw (normA2_continuous P hT)).const_mul _).integrableOn
  · have h1 : familySum F Qn (fun _ χ => ‖AchiC P (acoefS P) χ s‖ ^ 2)
        ≤ famSum P (fun _ χ => ‖Achi P χ s‖ ^ 2) :=
      familySum_le_famSum P F Qn hQn _ fun _ _ => sq_nonneg _
    have h2 := lemma43_sieve_half_A P hP hLS s
    have hg := lemma42_g_nonneg P s
    calc P.gQ s * familySum F Qn (fun _ χ => ‖AchiC P (acoefS P) χ s‖ ^ 2)
        ≤ P.gQ s * (sieveBudgetQ P * normA2 P s) := mul_le_mul_of_nonneg_left (h1.trans h2) hg
      _ = sieveBudgetQ P * (P.gQ s * normA2 P s) := by ring

/-- **THE TOTAL PP BLOCK, POINTWISE (Part 3, master form).** For every `ε > 0`:
`Σ_{χ∈𝔉_Q} 𝓜[P_χ,P_χ] ≤ 2[(1+ε)(|𝔉_Q|+ERR_in)P + (1+1/ε)(X+Q²−1)R]
  + 2(X+Q²−1)∫_{|s|>s₀} g‖a‖₂² + 2(X+Q²−1)∫_ℝ g‖a‖₂‖b‖₂`. -/
theorem famPP_total_le (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊) (hs0 : 0 ≤ P.s0)
    {ε : ℝ} (hε : 0 < ε) :
    familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ 2 * ((1 + ε) * ((F.sizeR Qn + ERRin P Qn) * zoneP P)
            + (1 + 1 / ε) * (sieveBudgetQ P * zoneR P))
        + 2 * (sieveBudgetQ P * ∫ s in (inZone P)ᶜ, P.gQ s * normA2 P s)
        + 2 * sieveBudgetQ P
            * ∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s) := by
  have hphi := phiQ_sq_integrable P hP hw
  have hUm : MeasurableSet (inZone P) := measurableSet_inZone P
  -- (1) Parseval
  have h1 : familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      = familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) := by
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact lemma41_parseval_diag P (PXchi P χ) hphi (FrobAssembly.PXchi_integrableOn P χ)
      (FrobAssembly.PXchi_sq_integrableOn P χ)
  -- (2) expansion over the whole line
  have h2 : familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      = familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2)
        + familySum F Qn (fun _ χ => 2 * ∫ s : ℝ,
            P.gQ s * (Achi P χ s * conj (Bchi P χ s)).re) := by
    rw [← familySum_add', ← familySum_add']
    refine familySum_congr_prim F Qn fun q χ hχ => ?_
    have := zone_expansion P hP hw χ hχ Set.univ
    simpa only [MeasureTheory.setIntegral_univ] using this
  -- (3) the B-half is the A-half
  have h3 : familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2)
      = familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2) := by
    unfold familySum
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => integral_B_eq_A P χ
  -- (4) the A-half splits at the zone
  have h4 : familySum F Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum F Qn (fun _ χ => ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2) := by
    rw [← familySum_add']
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact (MeasureTheory.integral_add_compl hUm
      (gQ_mul_integrable P hP hw ((Achi_continuous P χ).norm.pow 2))).symm
  -- (5) the pieces
  have hin : familySum F Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = inFormF F Qn P (acoefS P) := rfl
  have hfull := inFormF_full_le F Qn P hP hw hLS hQn hs0 hε
  have hout := famA_integral_le F Qn P hP hw hLS hQn (inZone P)ᶜ hUm.compl
  have hcross := (abs_le.mp (cross_integral_family F Qn P hP hw hLS hQn Set.univ
    MeasurableSet.univ)).2
  simp only [MeasureTheory.setIntegral_univ] at hcross
  rw [h1, h2, h3, h4, hin]
  linarith

/-- the out-zone diagonal: `∫_{|s|>s₀} g‖a‖₂² = ½∫_ℝ g(‖a‖₂²+‖b‖₂²) − (P + R)`. -/
theorem outZone_normA2_eq (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    (∫ s in (inZone P)ᶜ, P.gQ s * normA2 P s)
      = (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s)) / 2 - (zoneP P + zoneR P) := by
  have hT : (0 : ℝ) ≤ P.T := hP.T_pos.le
  have hiA : Integrable (fun s => P.gQ s * normA2 P s) :=
    gQ_mul_integrable P hP hw (normA2_continuous P hT)
  have hiB : Integrable (fun s => P.gQ s * normB2 P s) :=
    gQ_mul_integrable P hP hw (normB2_continuous P hT)
  have e1 : (fun s => P.gQ s * (normA2 P s + normB2 P s))
      = fun s => P.gQ s * normA2 P s + P.gQ s * normB2 P s := by funext s; ring
  rw [e1, MeasureTheory.integral_add hiA hiB, integral_normB2_eq_normA2,
    ← MeasureTheory.integral_add_compl (measurableSet_inZone P) hiA, zone_normA2_eq P hP hw]
  ring

/-- **THE MASTER INEQUALITY IN ZONE-SPLIT FORM.** With `B = X+Q²−1`, `K = |𝔉_Q| + ERR_in`,
`D_ℝ = ∫g(‖a‖²+‖b‖²)`, `N_ℝ = ∫g‖a‖‖b‖`:
`Σ_χ 𝓜[P_χ,P_χ] ≤ B·D_ℝ + 2B·N_ℝ − 2(B − (1+ε)K)·zoneP + (2/ε)·B·zoneR`. -/
theorem famPP_total_le' (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    (hw : 8 * P.w ≤ P.LB) (hLS : LargeSieveFamily) (hQn : Qn ≤ ⌊P.Q⌋₊) (hs0 : 0 ≤ P.s0)
    {ε : ℝ} (hε : 0 < ε) :
    familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ sieveBudgetQ P * (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
        + 2 * sieveBudgetQ P
            * (∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))
        - 2 * (sieveBudgetQ P - (1 + ε) * (F.sizeR Qn + ERRin P Qn)) * zoneP P
        + (2 / ε) * sieveBudgetQ P * zoneR P := by
  have h := famPP_total_le F Qn P hP hw hLS hQn hs0 hε
  rw [outZone_normA2_eq P hP hw] at h
  have e : (2 / ε) * sieveBudgetQ P * zoneR P
      = 2 * (1 + 1 / ε) * (sieveBudgetQ P * zoneR P) - 2 * sieveBudgetQ P * zoneR P := by
    field_simp
    ring
  rw [e]
  linarith

/-! ## 10. From `DesignFamily` (the tree's asymptotic idiom) to the design of record

`lemma44_P_main`, `lemma44_R_bound`, `zoneRP_facts`, `designFamily_reg` are stated along a
`DesignFamily D r` with `∀ᶠ Q in atTop`; the deliverable quantifies over every design point
`P` with `DesignOfRecord F r ε Qn P`. The bridge: every design-of-record selection is a
`DesignFamily` at exponent `r + ε`, and a predicate that holds eventually along EVERY design
family holds eventually at every design point (by contradiction, choosing a family of
counterexamples). -/

section Transfer
open Filter

/-- a design-of-record selection is a `DesignFamily` at exponent `r + ε`. -/
theorem designFamily_of_DoR (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (D : ℝ → ParamsQ) (hD : ∀ᶠ Q : ℝ in atTop, DesignOfRecord F r ε Q (D Q)) :
    DesignFamily D (r + ε) where
  valid := hD.mono fun _ h => h.1
  Q_eq := hD.mono fun _ h => h.2.1
  r_ge := by linarith
  T_eq := hD.mono fun Q h => by rw [h.2.2.1]; rfl
  crho_bdd := ⟨cWinDesign F, hD.mono fun _ h => le_of_eq (cWin_of_design h)⟩
  LB_atTop := by
    have hlow : ∀ᶠ Q : ℝ in atTop, Real.log Q + (-2) ≤ (D Q).LB := by
      filter_upwards [hD, eventually_gt_atTop (0 : ℝ)] with Q h hQ0
      have hv := h.1
      have hQ := h.2.1
      have hlam : 1 ≤ (D Q).lam := by rw [h.2.2.2.1]; exact one_le_lamStar_of_family F
      have hT1 : (1 : ℝ) ≤ (D Q).T := by linarith [hv.T_ge300]
      have hT0 : (0 : ℝ) < (D Q).T := by linarith
      have hpi0 : 0 < Real.pi := Real.pi_pos
      have h2pi : Real.log (2 * Real.pi) ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by positivity)]
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [this]
        have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        have he2 : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 := by
          nlinarith
        have hpi : Real.pi < 3.15 := Real.pi_lt_d2
        linarith
      have hLL : Real.log Q + (-2) ≤ (D Q).LL := by
        unfold ParamsQ.LL
        rw [hQ, Real.log_div (by positivity) (by positivity), Real.log_mul hQ0.ne' hT0.ne']
        have := Real.log_nonneg hT1
        linarith
      have hLL0 : 0 ≤ (D Q).LL := hv.LL_pos.le
      show Real.log Q + (-2) ≤ (D Q).lam * (D Q).LL
      nlinarith
    exact tendsto_atTop_mono' _ hlow (tendsto_atTop_add_const_right _ _ Real.tendsto_log_atTop)
  wrange := hD.mono fun _ h => h.2.2.2.2.2.1

/-- **The transfer**: a predicate holding eventually along every design family holds
eventually at every design point of record. -/
theorem transfer_of_designFamily (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (X : ParamsQ → Prop)
    (h : ∀ D : ℝ → ParamsQ, DesignFamily D (r + ε) → ∀ᶠ Q : ℝ in atTop, X (D Q)) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P → X P := by
  classical
  obtain ⟨Q₀, hQ₀⟩ := exists_designOfRecord F r ε hr hε
  obtain ⟨P₀⟩ : Nonempty ParamsQ := ⟨⟨0, 0, 0, 0, 0, fun _ => 0, 0⟩⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ → ParamsQ, D = fun Q =>
      if h1 : ∃ P, DesignOfRecord F r ε Q P ∧ ¬ X P then Classical.choose h1
      else if h2 : ∃ P, DesignOfRecord F r ε Q P then Classical.choose h2 else P₀ := ⟨_, rfl⟩
  have hDoR : ∀ᶠ Q : ℝ in atTop, DesignOfRecord F r ε Q (D Q) := by
    filter_upwards [eventually_ge_atTop Q₀] with Q hQ
    rw [hDdef]
    dsimp only
    split_ifs with h1 h2
    · exact (Classical.choose_spec h1).1
    · exact Classical.choose_spec h2
    · exact absurd (hQ₀ Q hQ) h2
  have hX := h D (designFamily_of_DoR F r ε hr hε D hDoR)
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.mp hX
  refine eventually_atTop.mpr ⟨⌈Q₁⌉₊, fun Qn hQn P hP => ?_⟩
  by_contra hnot
  have h1 : ∃ P', DesignOfRecord F r ε (Qn : ℝ) P' ∧ ¬ X P' := ⟨P, hP, hnot⟩
  have hQ : Q₁ ≤ (Qn : ℝ) := le_trans (Nat.le_ceil Q₁) (by exact_mod_cast hQn)
  have hXD := hQ₁ (Qn : ℝ) hQ
  rw [hDdef] at hXD
  dsimp only at hXD
  rw [dif_pos h1] at hXD
  exact (Classical.choose_spec h1).2 hXD

/-- the zone facts along a design family: `zoneP = (T/2π)∫₀^{s₀}u g(u)du·(1 ± ε₀)` and
`zoneR ≤ ε₀·zoneP`, eventually, for every `ε₀ > 0` (from `lemma44_P_main`, `zoneRP_facts`). -/
theorem zone_facts_family (D : ℝ → ParamsQ) (r : ℝ) (hD : DesignFamily D r) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) :
    ∀ᶠ Q in atTop,
      |zoneP (D Q) - (D Q).T / (2 * Real.pi) * ∫ u in Set.Icc 0 (D Q).s0, u * (D Q).gQ u|
          ≤ ε₀ * ((D Q).T / (2 * Real.pi) * ∫ u in Set.Icc 0 (D Q).s0, u * (D Q).gQ u)
        ∧ zoneR (D Q) ≤ ε₀ * zoneP (D Q) := by
  obtain ⟨ηP, hηP, hPeq⟩ := lemma44_P_main D r hD
  have hη : ∀ᶠ Q in atTop, |ηP Q| < ε₀ := by
    have := Metric.tendsto_nhds.mp hηP ε₀ hε₀
    filter_upwards [this] with Q hQ
    rwa [Real.dist_eq, sub_zero] at hQ
  have hTL : Tendsto (fun Q => (D Q).T * (D Q).LL) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ hD.T_atTop
    filter_upwards [LL_bounds D r hD, hD.valid] with Q hLL hv
    have hT0 : 0 ≤ (D Q).T := hv.T_pos.le
    nlinarith [hLL.1]
  have hsmall : ∀ᶠ Q in atTop,
      2654208 * Real.log ((D Q).T * (D Q).LL) / ((D Q).T * (D Q).LL) ≤ ε₀ := by
    have hK : (0 : ℝ) < 2654208 / ε₀ := by positivity
    filter_upwards [hTL.eventually (FrobAssembly.loglog_le_eventually _ hK),
      hTL.eventually (eventually_gt_atTop (0 : ℝ))] with Q hQ hpos
    rw [div_le_iff₀ hpos]
    rw [div_mul_eq_mul_div, div_le_iff₀ hε₀] at hQ
    linarith
  filter_upwards [hPeq, hη, zoneRP_facts D r hD, hsmall, designFamily_reg D r hD]
    with Q hP hηQ hfacts hsm hreg
  obtain ⟨hv, -, -, -, -, -, -, -, -⟩ := hreg
  obtain ⟨hPpos, -, -, hRP, -⟩ := hfacts
  have hT0 : 0 < (D Q).T := hv.T_pos
  have hI0 : 0 ≤ ∫ u in Set.Icc 0 (D Q).s0, u * (D Q).gQ u :=
    setIntegral_nonneg measurableSet_Icc fun u hu => mul_nonneg hu.1 (lemma42_g_nonneg _ u)
  have hM0 : 0 ≤ (D Q).T / (2 * Real.pi) * ∫ u in Set.Icc 0 (D Q).s0, u * (D Q).gQ u := by
    positivity
  refine ⟨?_, ?_⟩
  · rw [hP]
    rw [show (D Q).T / (2 * Real.pi) * (∫ u in Set.Icc 0 (D Q).s0, u * (D Q).gQ u) * (1 + ηP Q)
          - (D Q).T / (2 * Real.pi) * ∫ u in Set.Icc 0 (D Q).s0, u * (D Q).gQ u
        = ((D Q).T / (2 * Real.pi) * ∫ u in Set.Icc 0 (D Q).s0, u * (D Q).gQ u) * ηP Q by ring]
    rw [abs_mul, abs_of_nonneg hM0, mul_comm]
    exact mul_le_mul_of_nonneg_right hηQ.le hM0
  · have := hRP.trans hsm
    rwa [div_le_iff₀ hPpos] at this

/-- **the zone facts at every design point of record, eventually** (transferred). -/
theorem zone_facts_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      |zoneP P - P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u|
          ≤ ε₀ * (P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u)
        ∧ zoneR P ≤ ε₀ * zoneP P :=
  transfer_of_designFamily F r ε hr hε _ (fun D hD => zone_facts_family D (r + ε) hD hε₀)

/-- the regime facts of `designFamily_reg`, transferred. -/
theorem reg_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      P.Valid ∧ 8 * P.w ≤ P.LB ∧ (8:ℝ) ≤ P.LB ∧ (8:ℝ) ≤ P.s0 ∧
        P.s0 ≤ Real.log P.Q ∧ P.LB ≤ 4 * Real.log P.Q ∧
        Real.log P.Q ^ 3 ≤ P.T ∧ (144:ℝ) ≤ Real.log P.Q ∧
        Real.log P.Q / 2 ≤ P.s0 := by
  refine transfer_of_designFamily F r ε hr hε _ (fun D hD => ?_)
  filter_upwards [designFamily_reg D (r + ε) hD, hD.Q_eq] with Q h hQ
  rw [hQ]
  exact h

end Transfer

/-! ## 11. The eventual bookkeeping: `ERR_in`, the family sizes, the NfamQ floors -/

section Eventual
open Filter

/-! ### §12.3's count, in the two forms the size bounds below consume.

`Budget.ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn` gives `|2·|𝔉_Q| − Σ_q φ*(q)| ≤ Qn`
for each of the four parity families, and `ZetaQ.two_sizeR_parity_qle` /
`ZetaQ.two_sizeR_parity_dyadic` (`Budget.lean`, next to `sizeR_dyadic_lower`) put it against
the two full-family closed forms `N2.Astar Qn − 1` and `N2.Astar Qn − N2.Astar (Qn/2)`. They
live in `Budget` rather than here because `Budget.sizeR_floor_eventually` needs them too; the
four `not_isFull_*` lemmas are there for the same reason. Both are used unqualified below. -/

/-- The `Icc 2 Qn` core of `Cconst_mul_sizeR_le`, with the constant kept sharp so that the
parity branches have room for the `Qn` that §12.3's count costs. -/
theorem Cconst_core_qle (Qn : ℕ) (hQn : 2 ≤ Qn) :
    Real.pi ^ 4 / 18 * (Normalisation.N2.Astar Qn - 1)
      ≤ (Qn : ℝ) ^ 2 + 28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2 : ℝ) ≤ Qn := by exact_mod_cast hQn
  have hQn0 : (0 : ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log Qn := Real.log_nonneg (by linarith)
  have hsq0 : (0 : ℝ) ≤ (1 + Real.log Qn) ^ 2 := sq_nonneg _
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpi4' : Real.pi ^ 4 ≤ 98.5 := by
    have h1 : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have h0 : 0 ≤ Real.pi := Real.pi_pos.le
    have h2 : Real.pi ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ h0 h1 4
    nlinarith
  have hA := abs_le.mp (Normalisation.N2.Astar_bound Qn hQn1)
  have hcpos : (0 : ℝ) ≤ Real.pi ^ 4 / 18 := by positivity
  have h4 := mul_le_mul_of_nonneg_left hA.2 hcpos
  have h5 : Real.pi ^ 4 / 18 * (18 / Real.pi ^ 4 * (Qn : ℝ) ^ 2) = (Qn : ℝ) ^ 2 := by
    field_simp
  have h6 : Real.pi ^ 4 / 18 * (5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2)
      ≤ 28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
    nlinarith [hpi4', mul_nonneg hQn0 hsq0]
  linarith [h4, h5, h6, hcpos]

/-- The dyadic core of `Cconst_mul_sizeR_le`, likewise kept sharp. -/
theorem Cconst_core_dyadic (Qn : ℕ) (hQn : 2 ≤ Qn) :
    2 * Real.pi ^ 4 / 27 * (Normalisation.N2.Astar Qn - Normalisation.N2.Astar (Qn / 2))
      ≤ (Qn : ℝ) ^ 2 + 80 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2 : ℝ) ≤ Qn := by exact_mod_cast hQn
  have hQn0 : (0 : ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log Qn := Real.log_nonneg (by linarith)
  have hsq0 : (0 : ℝ) ≤ (1 + Real.log Qn) ^ 2 := sq_nonneg _
  have hsq1 : (1 : ℝ) ≤ (1 + Real.log Qn) ^ 2 := by nlinarith
  have hpi4 : (97.408 : ℝ) < Real.pi ^ 4 := Ends.pi_four_gt
  have hpi4' : Real.pi ^ 4 ≤ 98.5 := by
    have h1 : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have h0 : 0 ≤ Real.pi := Real.pi_pos.le
    have h2 : Real.pi ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ h0 h1 4
    nlinarith
  have hA := abs_le.mp (Normalisation.N2.Astar_bound Qn hQn1)
  have hhalf1 : 1 ≤ Qn / 2 := by omega
  have hB := abs_le.mp (Normalisation.N2.Astar_bound (Qn / 2) hhalf1)
  have hh1 : ((Qn / 2 : ℕ) : ℝ) ≤ Qn := by exact_mod_cast Nat.div_le_self Qn 2
  have hh2 : (Qn : ℝ) - 1 ≤ 2 * ((Qn / 2 : ℕ) : ℝ) := by
    have : Qn - 1 ≤ 2 * (Qn / 2) := by omega
    have h' : ((Qn - 1 : ℕ) : ℝ) ≤ ((2 * (Qn / 2) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast [Nat.cast_sub hQn1] at h'
    linarith
  have hh0 : (0 : ℝ) ≤ ((Qn / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlogh : Real.log ((Qn / 2 : ℕ) : ℝ) ≤ Real.log Qn := by
    have hpos : (0 : ℝ) < ((Qn / 2 : ℕ) : ℝ) := by exact_mod_cast hhalf1
    exact Real.log_le_log hpos hh1
  have hlogh0 : 0 ≤ Real.log ((Qn / 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hhalf1)
  have hsqh : (1 + Real.log ((Qn / 2 : ℕ) : ℝ)) ^ 2 ≤ (1 + Real.log Qn) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hlow : (18 / Real.pi ^ 4) * ((Qn / 2 : ℕ) : ℝ) ^ 2 - 5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2
      ≤ Normalisation.N2.Astar (Qn / 2) := by
    have := hB.1
    have h5 : 5 * ((Qn / 2 : ℕ) : ℝ) * (1 + Real.log ((Qn / 2 : ℕ) : ℝ)) ^ 2
        ≤ 5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
      apply mul_le_mul (by linarith) hsqh (by positivity) (by positivity)
    linarith
  have hh3 : (Qn : ℝ) ^ 2 / 4 - (Qn : ℝ) / 2 ≤ ((Qn / 2 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hpos18 : (0 : ℝ) < 18 / Real.pi ^ 4 := by positivity
  have hC1 : 2 * Real.pi ^ 4 / 27 * (18 / Real.pi ^ 4) = 4 / 3 := by field_simp; ring
  have hmain : Normalisation.N2.Astar Qn - Normalisation.N2.Astar (Qn / 2)
      ≤ (18 / Real.pi ^ 4) * (3 / 4 * (Qn : ℝ) ^ 2 + (Qn : ℝ) / 2)
        + 10 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
    nlinarith [hA.2, hlow, mul_le_mul_of_nonneg_left hh3 hpos18.le]
  have hCpos : (0 : ℝ) ≤ 2 * Real.pi ^ 4 / 27 := by positivity
  have hthis := mul_le_mul_of_nonneg_left hmain hCpos
  have e : 2 * Real.pi ^ 4 / 27 * ((18 / Real.pi ^ 4) * (3 / 4 * (Qn : ℝ) ^ 2 + (Qn : ℝ) / 2)
        + 10 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2)
      = 4 / 3 * (3 / 4 * (Qn : ℝ) ^ 2 + (Qn : ℝ) / 2)
        + (20 * Real.pi ^ 4 / 27) * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
    field_simp; ring
  rw [e] at hthis
  have hpi20 : (20 * Real.pi ^ 4 / 27) ≤ 73 := by nlinarith
  have hQL : (Qn : ℝ) ≤ (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by nlinarith
  nlinarith [hthis, hQL,
    mul_le_mul_of_nonneg_right hpi20
      (by positivity : (0:ℝ) ≤ (Qn : ℝ) * (1 + Real.log Qn) ^ 2)]

/-- `C_F·|𝔉_Q| ≤ Qn² + 100·Qn(1+log Qn)²` — **proved in all SIX branches.**

For the four parity families `C_F` doubles (`CfamEven = 2·Cfam`, `CfamEvenDyadic = 2·CfamDyadic`,
`ZetaQ/Defs.lean`) while `|𝔉_Q|` halves, so the product is unchanged to leading order.
What was missing was exactly the HALVING, and that is now
`Budget.ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn` — §12.3's `S(q)` bookkeeping. The
extra `Qn` it costs is absorbed by the `100`: the qle core needs `28`, the dyadic core `80`,
and the two parity branches add `≤ 6` resp. `≤ 8` on top. -/
theorem Cconst_mul_sizeR_le (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn) :
    F.Cconst * F.sizeR Qn ≤ (Qn : ℝ) ^ 2 + 100 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
  have hpi4 : (97.408 : ℝ) < Real.pi ^ 4 := Ends.pi_four_gt
  have hpi4' : Real.pi ^ 4 ≤ 98.5 := by
    have h1 : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have h0 : 0 ≤ Real.pi := Real.pi_pos.le
    have h2 : Real.pi ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ h0 h1 4
    nlinarith
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2 : ℝ) ≤ Qn := by exact_mod_cast hQn
  have hQn0 : (0 : ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log Qn := Real.log_nonneg (by linarith)
  have hA := abs_le.mp (Normalisation.N2.Astar_bound Qn hQn1)
  have hsq0 : 0 ≤ (1 + Real.log Qn) ^ 2 := sq_nonneg _
  have hsq1 : 1 ≤ (1 + Real.log Qn) ^ 2 := by nlinarith
  have hQL0 : (0 : ℝ) ≤ (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := mul_nonneg hQn0 hsq0
  have hQL : (Qn : ℝ) ≤ (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by nlinarith
  have hcq := Cconst_core_qle Qn hQn
  have hcd := Cconst_core_dyadic Qn hQn
  have hextq : Real.pi ^ 4 / 18 * (Qn : ℝ) ≤ 6 * ((Qn : ℝ) * (1 + Real.log Qn) ^ 2) := by
    nlinarith [hpi4', hQn0, hQL]
  have hextd : 2 * Real.pi ^ 4 / 27 * (Qn : ℝ) ≤ 8 * ((Qn : ℝ) * (1 + Real.log Qn) ^ 2) := by
    nlinarith [hpi4', hQn0, hQL]
  cases F with
  | qle =>
      rw [show Family.Cconst Family.qle = Real.pi ^ 4 / 18 from rfl,
        sizeR_qle_eq_Astar_sub_one Qn hQn1]
      linarith [hcq, hQL0]
  | dyadic =>
      rw [show Family.Cconst Family.dyadic = 2 * Real.pi ^ 4 / 27 from rfl,
        sizeR_dyadic_eq Qn]
      linarith [hcd, hQL0]
  | evenQle =>
      rw [show Family.Cconst Family.evenQle = Real.pi ^ 4 / 9 from rfl]
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_evenQle Qn hQn1 rfl)
      have h3 := mul_le_mul_of_nonneg_left hpar.2
        (by positivity : (0:ℝ) ≤ Real.pi ^ 4 / 18)
      linarith [hcq, hextq, hQL0, h3]
  | oddQle =>
      rw [show Family.Cconst Family.oddQle = Real.pi ^ 4 / 9 from rfl]
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_oddQle Qn hQn1 rfl)
      have h3 := mul_le_mul_of_nonneg_left hpar.2
        (by positivity : (0:ℝ) ≤ Real.pi ^ 4 / 18)
      linarith [hcq, hextq, hQL0, h3]
  | evenDyadic =>
      rw [show Family.Cconst Family.evenDyadic = 4 * Real.pi ^ 4 / 27 from rfl]
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_evenDyadic Qn rfl)
      have h3 := mul_le_mul_of_nonneg_left hpar.2
        (by positivity : (0:ℝ) ≤ 2 * Real.pi ^ 4 / 27)
      linarith [hcd, hextd, hQL0, h3]
  | oddDyadic =>
      rw [show Family.Cconst Family.oddDyadic = 4 * Real.pi ^ 4 / 27 from rfl]
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_oddDyadic Qn rfl)
      have h3 := mul_le_mul_of_nonneg_left hpar.2
        (by positivity : (0:ℝ) ≤ 2 * Real.pi ^ 4 / 27)
      linarith [hcd, hextd, hQL0, h3]
  | evenQleR =>
      rw [show Family.Cconst Family.evenQleR = Real.pi ^ 4 / 9 from rfl]
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_evenQleR Qn hQn1 rfl)
      have h3 := mul_le_mul_of_nonneg_left hpar.2
        (by positivity : (0:ℝ) ≤ Real.pi ^ 4 / 18)
      linarith [hcq, hextq, hQL0, h3]
  | oddQleR =>
      rw [show Family.Cconst Family.oddQleR = Real.pi ^ 4 / 9 from rfl]
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_oddQleR Qn hQn1 rfl)
      have h3 := mul_le_mul_of_nonneg_left hpar.2
        (by positivity : (0:ℝ) ≤ Real.pi ^ 4 / 18)
      linarith [hcq, hextq, hQL0, h3]
  | evenDyadicR =>
      rw [show Family.Cconst Family.evenDyadicR = 4 * Real.pi ^ 4 / 27 from rfl]
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_evenDyadicR Qn rfl)
      have h3 := mul_le_mul_of_nonneg_left hpar.2
        (by positivity : (0:ℝ) ≤ 2 * Real.pi ^ 4 / 27)
      linarith [hcd, hextd, hQL0, h3]
  | oddDyadicR =>
      rw [show Family.Cconst Family.oddDyadicR = 4 * Real.pi ^ 4 / 27 from rfl]
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_oddDyadicR Qn rfl)
      have h3 := mul_le_mul_of_nonneg_left hpar.2
        (by positivity : (0:ℝ) ≤ 2 * Real.pi ^ 4 / 27)
      linarith [hcd, hextd, hQL0, h3]


/-- `|𝔉_Q| ≥ 0.05·Qn²` once `500(1+log Qn)² ≤ Qn` — **all SIX families.**

**The constant was HALVED, from `0.1` to `0.05`, and that was forced.** `0.1` is FALSE for the
parity families: `|𝔉_even| ~ (9/π⁴)Qn² = 0.0924·Qn²` and
`|𝔉_even,dyad| ~ (27/(4π⁴))Qn² = 0.0693·Qn²`, both below `0.1`. At `0.05` the proved margins
under the hypothesis `500(1+log Qn)² ≤ Qn` are `≥ 0.083·Qn²` (parity qle) and `≥ 0.058·Qn²`
(parity dyadic), against `≥ 0.166·Qn²` and `≥ 0.117·Qn²` for the two full families, so ONE
statement covers all six.

**Downstream re-tuning (all of it).** The only consumer is `ERRin_le_sizeR` below, whose
constant `80` becomes `160` — the product is unchanged (`160·0.05 = 80·0.1 = 8`), so the bound
on `ERR_in` itself does not move, only its expression relative to `|𝔉_Q|`. That in turn
raises `ERRin_small_eventually`'s regime threshold from `80/δ + 36` to `160/δ + 36`; its
STATEMENT (`ERR_in ≤ δ·|𝔉_Q|` eventually, for every `δ > 0`) is unchanged, so nothing further
downstream moves. -/
theorem sizeR_ge_point (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hsz : 500 * (1 + Real.log Qn) ^ 2 ≤ Qn) : 0.05 * (Qn : ℝ) ^ 2 ≤ F.sizeR Qn := by
  have hpi4' : Real.pi ^ 4 ≤ 98.5 := by
    have h1 : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have h0 : 0 ≤ Real.pi := Real.pi_pos.le
    have h2 : Real.pi ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ h0 h1 4
    nlinarith
  have hpi4 : (97.408 : ℝ) < Real.pi ^ 4 := Ends.pi_four_gt
  have h18 : (0.18 : ℝ) ≤ 18 / Real.pi ^ 4 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2 : ℝ) ≤ Qn := by exact_mod_cast hQn
  have hlog0 : 0 ≤ Real.log Qn := Real.log_nonneg (by linarith)
  have hsq1 : 1 ≤ (1 + Real.log Qn) ^ 2 := by nlinarith
  have hQ2 : (Qn : ℝ) * (1 + Real.log Qn) ^ 2 ≤ (Qn : ℝ) ^ 2 / 500 := by
    have := mul_le_mul_of_nonneg_left hsz (by positivity : (0:ℝ) ≤ Qn)
    nlinarith
  have hQn0 : (0 : ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hQn500 : (500 : ℝ) ≤ (Qn : ℝ) := by nlinarith [hsz, hsq1]
  have hQle : (Qn : ℝ) ≤ (Qn : ℝ) ^ 2 / 500 := by nlinarith [hQn500, hQn0]
  have h18' := mul_le_mul_of_nonneg_right h18 (sq_nonneg (Qn : ℝ))
  cases F with
  | qle =>
      have := sizeR_qle_lower' Qn hQn1
      nlinarith [mul_le_mul_of_nonneg_right h18 (sq_nonneg (Qn : ℝ))]
  | dyadic =>
      rw [sizeR_dyadic_eq Qn]
      have hA := abs_le.mp (Normalisation.N2.Astar_bound Qn hQn1)
      have hhalf1 : 1 ≤ Qn / 2 := by omega
      have hB := abs_le.mp (Normalisation.N2.Astar_bound (Qn / 2) hhalf1)
      have hh1 : ((Qn / 2 : ℕ) : ℝ) ≤ Qn := by exact_mod_cast Nat.div_le_self Qn 2
      have hh0 : (0 : ℝ) ≤ ((Qn / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hh4 : 2 * ((Qn / 2 : ℕ) : ℝ) ≤ Qn := by
        have : 2 * (Qn / 2) ≤ Qn := Nat.mul_div_le Qn 2
        exact_mod_cast this
      have hlogh : Real.log ((Qn / 2 : ℕ) : ℝ) ≤ Real.log Qn := by
        have hpos : (0 : ℝ) < ((Qn / 2 : ℕ) : ℝ) := by exact_mod_cast hhalf1
        exact Real.log_le_log hpos hh1
      have hlogh0 : 0 ≤ Real.log ((Qn / 2 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hhalf1)
      have hsqh : (1 + Real.log ((Qn / 2 : ℕ) : ℝ)) ^ 2 ≤ (1 + Real.log Qn) ^ 2 := by
        apply pow_le_pow_left₀ (by linarith) (by linarith)
      have hup : Normalisation.N2.Astar (Qn / 2)
          ≤ (18 / Real.pi ^ 4) * ((Qn : ℝ) ^ 2 / 4) + 5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
        have h5 : 5 * ((Qn / 2 : ℕ) : ℝ) * (1 + Real.log ((Qn / 2 : ℕ) : ℝ)) ^ 2
            ≤ 5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
          apply mul_le_mul (by linarith) hsqh (by positivity) (by positivity)
        have h6 : ((Qn / 2 : ℕ) : ℝ) ^ 2 ≤ (Qn : ℝ) ^ 2 / 4 := by nlinarith
        have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0:ℝ) ≤ 18 / Real.pi ^ 4)
        linarith [hB.2]
      nlinarith [hA.1, mul_le_mul_of_nonneg_right h18 (sq_nonneg (Qn : ℝ))]
  -- the four parity branches at the halved threshold, from §12.3's count.
  | evenQle =>
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_evenQle Qn hQn1 rfl)
      linarith [hpar.1, sizeR_qle_eq_Astar_sub_one Qn hQn1, sizeR_qle_lower' Qn hQn1,
        h18', hQ2, hQle]
  | oddQle =>
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_oddQle Qn hQn1 rfl)
      linarith [hpar.1, sizeR_qle_eq_Astar_sub_one Qn hQn1, sizeR_qle_lower' Qn hQn1,
        h18', hQ2, hQle]
  | evenDyadic =>
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_evenDyadic Qn rfl)
      linarith [hpar.1, sizeR_dyadic_eq Qn, sizeR_dyadic_lower Qn hQn, h18', hQ2, hQle]
  | oddDyadic =>
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_oddDyadic Qn rfl)
      linarith [hpar.1, sizeR_dyadic_eq Qn, sizeR_dyadic_lower Qn hQn, h18', hQ2, hQle]
  | evenQleR =>
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_evenQleR Qn hQn1 rfl)
      linarith [hpar.1, sizeR_qle_eq_Astar_sub_one Qn hQn1, sizeR_qle_lower' Qn hQn1,
        h18', hQ2, hQle]
  | oddQleR =>
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_oddQleR Qn hQn1 rfl)
      linarith [hpar.1, sizeR_qle_eq_Astar_sub_one Qn hQn1, sizeR_qle_lower' Qn hQn1,
        h18', hQ2, hQle]
  | evenDyadicR =>
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_evenDyadicR Qn rfl)
      linarith [hpar.1, sizeR_dyadic_eq Qn, sizeR_dyadic_lower Qn hQn, h18', hQ2, hQle]
  | oddDyadicR =>
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_oddDyadicR Qn rfl)
      linarith [hpar.1, sizeR_dyadic_eq Qn, sizeR_dyadic_lower Qn hQn, h18', hQ2, hQle]

/-- `ERR_in ≤ 160·|𝔉_Q|/(log Qn)²` — the zone-edge calibration `Y = Q(log Q)^{−3}`.

The constant was `80` while `sizeR_ge_point` still claimed `0.1·Qn²`; the halved
threshold `0.05·Qn²` doubles it. The bound on `ERR_in` itself is untouched — both readings
are `ERR_in ≤ 8·Qn²/(log Qn)²`. -/
theorem ERRin_le_sizeR (F : Family) (Qn : ℕ) (P : ParamsQ) (_hP : P.Valid) (hQ : P.Q = Qn)
    (hQn : 2 ≤ Qn) (h36 : 36 ≤ Real.log Qn) (hsz : 500 * (1 + Real.log Qn) ^ 2 ≤ Qn) :
    ERRin P Qn ≤ 160 / Real.log Qn ^ 2 * F.sizeR Qn := by
  have hQnR : (2 : ℝ) ≤ Qn := by exact_mod_cast hQn
  have hQ0 : (0 : ℝ) < P.Q := by rw [hQ]; linarith
  have hlog1 : (1 : ℝ) ≤ Real.log Qn := by linarith
  have hlog0 : (0 : ℝ) < Real.log Qn := by linarith
  have hlogQ : Real.log P.Q = Real.log Qn := by rw [hQ]
  -- `Y = Q·(log Q)^{-3}`
  have hY : P.zoneY = Qn * (Real.log Qn) ^ (-(3 : ℝ)) := by
    rw [zoneY_eq_rpow P hQ0, sub_eq_add_neg, Real.rpow_add hQ0, Real.rpow_one,
      rpow_neg_deltaPrime P hQ0 (by rw [hlogQ]; exact hlog0), hQ]
  have hY' : P.zoneY = Qn / (Real.log Qn) ^ 3 := by
    rw [hY, Real.rpow_neg hlog0.le, div_eq_mul_inv]
    congr 1
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- `log Y = s₀ ≤ log Q`, `s₀ ≥ 0`
  have hs0 : 0 ≤ P.s0 := by
    rw [s0_eq_of_Q_eq hQ hlog0.ne']
    have := mul_log_le_self (k := 3) (z := Real.log Qn) (by norm_num) hlog1 (by nlinarith)
    linarith
  have hYpos : 0 < P.zoneY := Real.exp_pos _
  have hYn1 : 1 ≤ Yn P := one_le_Yn P hs0
  have hYnR : (1 : ℝ) ≤ (Yn P : ℝ) := by exact_mod_cast hYn1
  have hYnle : (Yn P : ℝ) ≤ P.zoneY := Nat.floor_le hYpos.le
  have hlogYn : Real.log (Yn P : ℝ) ≤ Real.log Qn := by
    calc Real.log (Yn P : ℝ) ≤ Real.log P.zoneY := Real.log_le_log (by linarith) hYnle
      _ = P.s0 := by rw [ParamsQ.zoneY, Real.log_exp]
      _ ≤ Real.log Qn := by
          rw [s0_eq_of_Q_eq hQ hlog0.ne']
          have := Real.log_nonneg hlog1
          linarith
  have hsize := sizeR_ge_point F Qn hQn hsz
  have hlogYn0 : 0 ≤ Real.log (Yn P : ℝ) := Real.log_nonneg hYnR
  -- assemble
  unfold ERRin
  have h1 : (Yn P : ℝ) * (1 + Real.log (Yn P : ℝ)) ≤ (Qn / Real.log Qn ^ 3) * (1 + Real.log Qn) := by
    rw [← hY']
    apply mul_le_mul hYnle (by linarith) (by linarith) hYpos.le
  have h2 : 2 * (Qn : ℝ) * (2 * ((Qn / Real.log Qn ^ 3) * (1 + Real.log Qn)))
      = 4 * (Qn : ℝ) ^ 2 * (1 + Real.log Qn) / Real.log Qn ^ 3 := by
    ring
  have h3 : (1 + Real.log Qn) / Real.log Qn ^ 3 ≤ 2 / Real.log Qn ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hlog0 2, pow_pos hlog0 3]
  calc 2 * (Qn : ℝ) * (2 * ((Yn P : ℝ) * (1 + Real.log (Yn P : ℝ))))
      ≤ 2 * (Qn : ℝ) * (2 * ((Qn / Real.log Qn ^ 3) * (1 + Real.log Qn))) := by
        gcongr
    _ = 4 * (Qn : ℝ) ^ 2 * ((1 + Real.log Qn) / Real.log Qn ^ 3) := by rw [h2]; ring
    _ ≤ 4 * (Qn : ℝ) ^ 2 * (2 / Real.log Qn ^ 2) := by gcongr
    _ = 160 / Real.log Qn ^ 2 * (0.05 * (Qn : ℝ) ^ 2) := by ring
    _ ≤ 160 / Real.log Qn ^ 2 * F.sizeR Qn := by gcongr

/-- `ERR_in ≤ δ·|𝔉_Q|` eventually along the design, for every `δ > 0`. -/
theorem ERRin_small_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      ERRin P Qn ≤ δ * F.sizeR Qn := by
  have hK1 : (1 : ℝ) ≤ max 500 (160 / δ + 36) := le_trans (by norm_num) (le_max_left _ _)
  filter_upwards [FrobAssembly.design_regime F r ε hr hε _ hK1, eventually_ge_atTop 2] with Qn hreg hQn2
  intro P hdes
  obtain ⟨hlogK, -, -, -, hszK, -, -, -⟩ := hreg P hdes
  have hP := hdes.1
  have hQ := FrobAssembly.Q_of_design hdes
  have h500 : (500 : ℝ) ≤ max 500 (160 / δ + 36) := le_max_left _ _
  have h80 : 160 / δ + 36 ≤ max 500 (160 / δ + 36) := le_max_right _ _
  have hsz : 500 * (1 + Real.log Qn) ^ 2 ≤ Qn :=
    le_trans (mul_le_mul_of_nonneg_right h500 (sq_nonneg _)) hszK
  have h36 : 36 ≤ Real.log Qn := by
    have : 160 / δ + 36 ≤ Real.log Qn := h80.trans hlogK
    have : 0 ≤ 160 / δ := by positivity
    linarith
  have h := ERRin_le_sizeR F Qn P hP hQ hQn2 h36 hsz
  refine h.trans ?_
  have hS0 : 0 ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  refine mul_le_mul_of_nonneg_right ?_ hS0
  have hlog : 160 / δ ≤ Real.log Qn := by linarith [h80.trans hlogK]
  have hlogpos : 0 < Real.log Qn := by linarith [show (0:ℝ) < 160 / δ by positivity]
  rw [div_le_iff₀ (by positivity)]
  have h1 : 160 ≤ Real.log Qn * δ := (div_le_iff₀ hδ).mp hlog
  have h2 : Real.log Qn ≤ Real.log Qn ^ 2 := by nlinarith
  nlinarith

/-- `|𝔉_Q|·(T/2π)·ℒ ≤ (1+η)·𝒩` eventually (from `NfamQ_sharp_eventually` and the size bound). -/
theorem sizeR_LL_le_NfamQ_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL) ≤ (1 + η) * NfamQ P F Qn := by
  have hC := FrobAssembly.Cconst_pos F
  have hK1 : (1 : ℝ) ≤ 300 / η := by rw [le_div_iff₀ hη]; linarith
  have hη3 : 0 < η / 3 := by positivity
  filter_upwards [FrobAssembly.design_regime F r ε hr hε _ hK1,
    FrobAssembly.NfamQ_sharp_eventually F r ε hr hε hη3 (by linarith), eventually_ge_atTop 2]
    with Qn hreg hsharp hQn2
  intro P hdes
  obtain ⟨-, -, -, -, hszK, -, -, -⟩ := hreg P hdes
  have hP := hdes.1
  have hQ := FrobAssembly.Q_of_design hdes
  have hN := hsharp P hdes
  have hT0 : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hQn0 : (0 : ℝ) < Qn := by exact_mod_cast (show 0 < Qn by omega)
  have hX0 : 0 ≤ P.T / (2 * Real.pi) * P.LL := by positivity
  have hsz := Cconst_mul_sizeR_le F Qn hQn2
  -- `100 Qn (1+log Qn)² ≤ (η/3) Qn²`
  have h100 : 100 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 ≤ η / 3 * (Qn : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hszK hQn0.le
    have e : (Qn : ℝ) * (300 / η * (1 + Real.log Qn) ^ 2) = (300 / η) * ((Qn : ℝ) * (1 + Real.log Qn) ^ 2) := by ring
    rw [e] at this
    have h2 : (300 / η) * ((Qn : ℝ) * (1 + Real.log Qn) ^ 2) ≤ (Qn : ℝ) ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
    nlinarith
  have hCS : F.Cconst * F.sizeR Qn ≤ (1 + η / 3) * (Qn : ℝ) ^ 2 := by nlinarith
  have hS0 : 0 ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  -- `|𝔉| X ≤ (1+η/3) Qn² X / C ≤ (1+η/3)² N`
  have h1 : F.Cconst * (F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL))
      ≤ (1 + η / 3) * ((Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi) * P.LL)) := by
    have := mul_le_mul_of_nonneg_right hCS hX0
    nlinarith
  have h2 : (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi) * P.LL) ≤ F.Cconst * (1 + η / 3) * NfamQ P F Qn := by
    have := hN
    nlinarith
  have hN0 := NfamQ_nonneg P F Qn
  have h3 : F.Cconst * (F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL))
      ≤ F.Cconst * ((1 + η / 3) * (1 + η / 3) * NfamQ P F Qn) := by
    calc F.Cconst * (F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL))
        ≤ (1 + η / 3) * ((Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi) * P.LL)) := h1
      _ ≤ (1 + η / 3) * (F.Cconst * (1 + η / 3) * NfamQ P F Qn) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have h4 := le_of_mul_le_mul_left h3 hC
  have h5 : (1 + η / 3) * (1 + η / 3) ≤ 1 + η := by nlinarith
  calc F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL)
      ≤ (1 + η / 3) * (1 + η / 3) * NfamQ P F Qn := h4
    _ ≤ (1 + η) * NfamQ P F Qn := mul_le_mul_of_nonneg_right h5 hN0

end Eventual

/-! ## 12. The dictionary for the in-zone main term, and the final assembly -/

section Final
open Filter

/-- `∫_{|u|≤s₀} |u| g(u) du = 2∫_0^{s₀} u g(u) du` (`g` even). -/
theorem integral_Icc_abs_eq_two (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    (hs0 : 0 ≤ P.s0) :
    (∫ u in Set.Icc (-P.s0) P.s0, |u| * P.gQ u) = 2 * ∫ u in Set.Icc 0 P.s0, u * P.gQ u := by
  have hg : Continuous P.gQ := hP.gQ_continuous hw
  have hle : -P.s0 ≤ P.s0 := by linarith
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => |u| * P.gQ u) volume a b :=
    fun a b => (continuous_abs.mul hg).intervalIntegrable a b
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-P.s0) 0) (hint 0 P.s0)]
  have hneg : (∫ u in (-P.s0)..0, |u| * P.gQ u) = ∫ u in (0:ℝ)..P.s0, |u| * P.gQ u := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := P.s0)
      (fun u => |u| * P.gQ u)
    simp only [neg_zero, abs_neg, lemma42_g_even] at h
    exact h.symm
  have hpos : (∫ u in (0:ℝ)..P.s0, |u| * P.gQ u) = ∫ u in (0:ℝ)..P.s0, u * P.gQ u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hs0] at hu
    simp only [abs_of_nonneg hu.1]
  rw [hneg, hpos, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hs0]
  ring

/-- `s₀/ℒ = zoneFactor`: the in-zone breakpoint `|s| ≤ s₀ = (1−δ′)log Q` is `|α| ≤ a`,
`a = (1−δ′)(1 − l(T)/ℒ)` (paper: "the α-zones are zones of `s = αℒ`"). -/
theorem s0_div_LL_eq_zoneFactor (P : ParamsQ) (hP : P.Valid) : P.s0 / P.LL = zoneFactor P := by
  have hLL : 0 < P.LL := hP.LL_pos
  have hQ : 0 < P.Q := by linarith [hP.Q_ge]
  have hT : 0 < P.T := hP.T_pos
  have hl : P.LL = Real.log P.Q + Zeta23.l P.T := by
    have e : P.Q * P.T / (2 * Real.pi) = P.Q * (P.T / (2 * Real.pi)) := by ring
    unfold ParamsQ.LL Zeta23.l
    rw [e, Real.log_mul hQ.ne' (by positivity)]
  unfold zoneFactor ParamsQ.s0
  have hlogQ : Real.log P.Q = P.LL - Zeta23.l P.T := by linarith
  rw [hlogQ, div_eq_iff hLL.ne']
  field_simp

/-- **The in-zone main term in §11's vocabulary**:
`2·(T/2π)∫_0^{s₀} u g(u) du = (T/2π)·ℒ·(aL)²·K0a(zoneFactor)(v_design)`. -/
theorem zoneMain_eq (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (hs0 : 0 ≤ P.s0) :
    2 * (P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u)
      = P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2
          * FrobAssembly.K0a (zoneFactor P) (vDesign P) := by
  have h1 := FrobAssembly.integral_abs_gQ_Icc_eq hP hw P.s0
  rw [s0_div_LL_eq_zoneFactor P hP] at h1
  have h2 := integral_Icc_abs_eq_two P hP hw hs0
  rw [show 2 * (P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u)
      = P.T / (2 * Real.pi) * (2 * ∫ u in Set.Icc 0 P.s0, u * P.gQ u) by ring, ← h2, h1]
  unfold FrobAssembly.K0a
  ring


/-- **The pure arithmetic of the zone-split assembly.** -/
theorem final_arith {total B K Pz Rz Dr Nr ρ M X W N C k k0 k1 E ε₀ δ ε' : ℝ}
    (h1 : total ≤ B * Dr + 2 * B * Nr - 2 * (B - (1 + ε₀) * K) * Pz + (2 / ε₀) * B * Rz)
    (hN : 2 * Nr ≤ ρ * Dr) (_hρ0 : 0 ≤ ρ) (hρ : ρ ≤ δ) (hD0 : 0 ≤ Dr)
    (hD : Dr ≤ (X * W * k + E) * (1 + δ)) (hE : B * E ≤ δ * W * N) (hE0 : 0 ≤ E)
    (hP1 : M * (1 - ε₀) ≤ Pz) (hP2 : Pz ≤ M * (1 + ε₀)) (hR : Rz ≤ ε₀ ^ 2 * Pz)
    (hM : 2 * M = X * W * k0) (hM0 : 0 ≤ M)
    (hε₀ : 0 < ε₀) (hε₀δ : ε₀ ≤ δ) (hδ1 : δ ≤ 1)
    (hK0 : 0 ≤ K) (hKB : K ≤ B) (hBX : B * X ≤ (1 + δ) ^ 2 * C * N)
    (hKX : K * X ≤ (1 + δ) ^ 2 * N)
    (hk : k = k0 + k1) (hk0 : 0 ≤ k0) (hk1 : 0 ≤ k1) (hk2 : k ≤ 2) (hC : 0 < C)
    (hW : 0 ≤ W) (hNn : 0 ≤ N) (hX : 0 ≤ X)
    (hδε : δ * (70 * C + 10) ≤ ε') :
    total ≤ W * (k0 + C * k1 + ε') * N := by
  have hB0 : 0 ≤ B := hK0.trans hKB
  have hδ0 : 0 ≤ δ := hε₀.le.trans hε₀δ
  have hε₀1 : ε₀ ≤ 1 := hε₀δ.trans hδ1
  have hδδ : δ ^ 2 ≤ δ := by
    have := mul_le_mul_of_nonneg_left hδ1 hδ0
    rw [mul_one] at this
    rw [pow_two]
    exact this
  have hPz0 : 0 ≤ Pz := le_trans (mul_nonneg hM0 (by linarith)) hP1
  -- Step A: `(2/ε₀) B Rz ≤ 2 ε₀ B Pz`
  have hA : (2 / ε₀) * B * Rz ≤ 2 * ε₀ * B * Pz := by
    have h : (2 / ε₀) * B * Rz ≤ (2 / ε₀) * B * (ε₀ ^ 2 * Pz) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    have e : (2 / ε₀) * B * (ε₀ ^ 2 * Pz) = 2 * ε₀ * B * Pz := by
      field_simp
    linarith
  -- Step B: `total ≤ B Dr (1+δ) − 2(B−K)Pz + 4 ε₀ B Pz`
  have hB1 : 2 * B * Nr ≤ B * (δ * Dr) := by
    have e : 2 * B * Nr = B * (2 * Nr) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (hN.trans (mul_le_mul_of_nonneg_right hρ hD0)) hB0
  have hKPz : 2 * ε₀ * K * Pz ≤ 2 * ε₀ * B * Pz := by
    have h := mul_le_mul_of_nonneg_right hKB hPz0
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * ε₀)
    linarith
  have hB2 : total ≤ B * Dr * (1 + δ) - 2 * (B - K) * Pz + 4 * ε₀ * B * Pz := by
    linarith [h1, hA, hB1, hKPz]
  -- Step C: replace `Pz` by `M`
  have hBK : 0 ≤ B - K := by linarith
  have hC1 : -(2 * (B - K) * Pz) ≤ -(2 * (B - K) * M) + 2 * ε₀ * B * M := by
    have h := mul_le_mul_of_nonneg_left hP1 hBK
    have h' : 0 ≤ ε₀ * K * M := by positivity
    linarith
  have hC2 : 4 * ε₀ * B * Pz ≤ 8 * ε₀ * B * M := by
    have h := mul_le_mul_of_nonneg_left hP2 (by positivity : 0 ≤ 4 * ε₀ * B)
    have h'' : ε₀ * ε₀ * B * M ≤ ε₀ * B * M := by
      have h0 : 0 ≤ ε₀ * B * M := by positivity
      have := mul_le_mul_of_nonneg_right hε₀1 h0
      linarith
    linarith
  have hC3 : total ≤ B * Dr * (1 + δ) - 2 * (B - K) * M + 10 * δ * B * M := by
    have h : 10 * ε₀ * B * M ≤ 10 * δ * B * M := by
      have := mul_le_mul_of_nonneg_right hε₀δ (mul_nonneg hB0 hM0)
      linarith
    linarith [hB2, hC1, hC2, h]
  -- Step D: `B Dr (1+δ) ≤ B X W k (1+δ)² + 4 δ W N`
  have hD1 : B * Dr * (1 + δ) ≤ B * X * W * k * (1 + δ) ^ 2 + 4 * δ * W * N := by
    have h1' : B * Dr ≤ B * ((X * W * k + E) * (1 + δ)) := mul_le_mul_of_nonneg_left hD hB0
    have h2' : B * E * (1 + δ) ^ 2 ≤ 4 * δ * W * N := by
      have h4 : (1 + δ) ^ 2 ≤ 4 := by linarith only [hδδ, hδ1]
      have h3 : 0 ≤ B * E := mul_nonneg hB0 hE0
      calc B * E * (1 + δ) ^ 2 ≤ B * E * 4 := mul_le_mul_of_nonneg_left h4 h3
        _ ≤ δ * W * N * 4 := mul_le_mul_of_nonneg_right hE (by norm_num)
        _ = 4 * δ * W * N := by ring
    have h3' : B * Dr * (1 + δ) ≤ B * ((X * W * k + E) * (1 + δ)) * (1 + δ) :=
      mul_le_mul_of_nonneg_right h1' (by linarith)
    have e : B * ((X * W * k + E) * (1 + δ)) * (1 + δ)
        = B * X * W * k * (1 + δ) ^ 2 + B * E * (1 + δ) ^ 2 := by ring
    linarith
  -- Step E: collect
  have hE1 : 2 * (B - K) * M = B * X * W * k0 - K * X * W * k0 := by
    have e : 2 * (B - K) * M = (B - K) * (2 * M) := by ring
    rw [e, hM]; ring
  have hE2 : 10 * δ * B * M = 5 * δ * (B * X * W * k0) := by
    have e : 10 * δ * B * M = 5 * δ * B * (2 * M) := by ring
    rw [e, hM]; ring
  have hBXW : 0 ≤ B * X * W := by positivity
  have hF : total ≤ B * X * W * (k * (1 + δ) ^ 2 - k0 + 5 * δ * k0) + K * X * W * k0
      + 4 * δ * W * N := by
    linarith [hC3, hD1, hE1, hE2]
  have hG : k * (1 + δ) ^ 2 - k0 + 5 * δ * k0 ≤ k1 + 16 * δ := by
    have e : k * (1 + δ) ^ 2 - k0 + 5 * δ * k0
        = k1 + (k0 + k1) * (2 * δ + δ ^ 2) + 5 * δ * k0 := by rw [hk]; ring
    rw [e]
    have hkδ : (k0 + k1) * (2 * δ + δ ^ 2) ≤ 2 * (2 * δ + δ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hδδ : δ ^ 2 ≤ δ := by
      have := mul_le_mul_of_nonneg_left hδ1 hδ0
      rw [mul_one] at this
      rw [pow_two]
      exact this
    have h5 : 5 * δ * k0 ≤ 5 * δ * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith only [hkδ, hδδ, h5]
  have hH : B * X * W * (k * (1 + δ) ^ 2 - k0 + 5 * δ * k0) ≤ B * X * W * (k1 + 16 * δ) :=
    mul_le_mul_of_nonneg_left hG hBXW
  have hsq : (1 + δ) ^ 2 ≤ 1 + 3 * δ := by linarith only [hδδ]
  have hI : B * X * W * (k1 + 16 * δ) ≤ (1 + 3 * δ) * C * N * W * (k1 + 16 * δ) := by
    have h1' : B * X * W ≤ (1 + δ) ^ 2 * C * N * W := mul_le_mul_of_nonneg_right hBX hW
    have h2' : (1 + δ) ^ 2 * C * N * W ≤ (1 + 3 * δ) * C * N * W := by
      have h0 : 0 ≤ C * N * W := by positivity
      have := mul_le_mul_of_nonneg_right hsq h0
      linarith
    exact mul_le_mul_of_nonneg_right (h1'.trans h2') (by positivity)
  have hJ : K * X * W * k0 ≤ (1 + 3 * δ) * N * W * k0 := by
    have h1' : K * X * W ≤ (1 + δ) ^ 2 * N * W := mul_le_mul_of_nonneg_right hKX hW
    have h2' : (1 + δ) ^ 2 * N * W ≤ (1 + 3 * δ) * N * W := by
      have h0 : 0 ≤ N * W := by positivity
      have := mul_le_mul_of_nonneg_right hsq h0
      linarith
    exact mul_le_mul_of_nonneg_right (h1'.trans h2') hk0
  have hWN : 0 ≤ W * N := mul_nonneg hW hNn
  have hk1' : k1 ≤ 2 := by linarith
  have hk0' : k0 ≤ 2 := by linarith
  have hfin0 : (1 + 3 * δ) * C * (k1 + 16 * δ) + (1 + 3 * δ) * k0 + 4 * δ
      ≤ k0 + C * k1 + ε' := by
    have hδC : 0 ≤ δ * C := mul_nonneg hδ0 hC.le
    have h1' : 3 * δ * C * k1 ≤ 3 * δ * C * 2 :=
      mul_le_mul_of_nonneg_left hk1' (by positivity)
    have h2' : 48 * δ * C * δ ≤ 48 * δ * C * 1 :=
      mul_le_mul_of_nonneg_left hδ1 (by positivity)
    have h3' : 3 * δ * k0 ≤ 3 * δ * 2 := mul_le_mul_of_nonneg_left hk0' (by positivity)
    linarith only [h1', h2', h3', hδε]
  have hfin : (1 + 3 * δ) * C * N * W * (k1 + 16 * δ) + (1 + 3 * δ) * N * W * k0
      + 4 * δ * W * N ≤ W * (k0 + C * k1 + ε') * N := by
    have := mul_le_mul_of_nonneg_left hfin0 hWN
    linarith
  linarith only [hF, hH, hI, hJ, hfin]

/-- **THE FROBENIUS PP BLOCK WITH THE IN-ZONE COEFFICIENT 1 (the deliverable).**
Along the design of record, for every `ε′ > 0` and all large `Qn`, at every design point `P`:

  `Σ_{χ∈𝔉_Q} 𝓜[P_χ,P_χ] ≤ (aL)²·( K0a(a) + C_F·K1a(a) + ε′ )·𝒩`,  `a = zoneFactor P`,

i.e. in-zone kernel coefficient `1`, out-zone coefficient `C_F = Q²/|𝔉_Q|`. Sorry-free,
including the inherited `largeSieveFamily_holds` (Gallagher budget `Q² + πN`; before the
Gallagher rethread it carried `sorryAx` from Selberg's extremal problem). -/
theorem famPP_le_zone_split (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ)
    (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
        ≤ (P.aQ * P.LB) ^ 2
            * (FrobAssembly.K0a (zoneFactor P) (vDesign P)
                + F.Cconst * FrobAssembly.K1a (zoneFactor P) (vDesign P) + ε')
            * NfamQ P F Qn := by
  obtain ⟨Cs, hCs0, hdiag⟩ := lemma43_diagonal (cWinDesign F)
  obtain ⟨CM, hCM0, hclose⟩ := sumA2gQ_close
  obtain ⟨Lρ, Tρ, hρ⟩ := FrobAssembly.rhoU_univ_le_pointwise (cWinDesign F)
  have hC := FrobAssembly.Cconst_pos F
  have hpi := Real.pi_pos
  -- the small parameter
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (ε' / (70 * F.Cconst + 10)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδδ : δ ^ 2 ≤ δ := by
    have := mul_le_mul_of_nonneg_left hδ1 hδ0.le
    rw [mul_one] at this
    rw [pow_two]
    exact this
  have hδε : δ * (70 * F.Cconst + 10) ≤ ε' := by
    have h : δ ≤ ε' / (70 * F.Cconst + 10) := by rw [hδdef]; exact min_le_right _ _
    have hpos : 0 < 70 * F.Cconst + 10 := by positivity
    calc δ * (70 * F.Cconst + 10) ≤ ε' / (70 * F.Cconst + 10) * (70 * F.Cconst + 10) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = ε' := div_mul_cancel₀ _ hpos.ne'
  have hδ3 : 0 < δ / 3 := by positivity
  have hδ31 : δ / 3 ≤ 1 := by linarith
  -- the thresholds
  have hK₁ : (1:ℝ) ≤ max 1 (Cs / δ + 1) := le_max_left _ _
  have hK₂ : (1:ℝ) ≤ max 1 (96 / (Real.pi * δ ^ 2)) := le_max_left _ _
  have hK₃ : (1:ℝ) ≤ max 1 (max Lρ Tρ) := le_max_left _ _
  have hK₄ : (1:ℝ) ≤ 500 := by norm_num
  have hK₅ : (1:ℝ) ≤ max 1 (3 / δ) := le_max_left _ _
  have hK₆ : (1:ℝ) ≤ max 1 (128 * F.Cconst * CM / (9 * δ)) := le_max_left _ _
  filter_upwards [FrobAssembly.design_regime F r ε hr hε _ hK₁, FrobAssembly.design_regime F r ε hr hε _ hK₂,
    FrobAssembly.design_regime F r ε hr hε _ hK₃, FrobAssembly.design_regime F r ε hr hε _ hK₄,
    FrobAssembly.design_regime F r ε hr hε _ hK₅, FrobAssembly.design_regime F r ε hr hε _ hK₆,
    FrobAssembly.design_basic F r ε hr hε,
    FrobAssembly.NfamQ_sharp_eventually F r ε hr hε hδ3 hδ31,
    zone_facts_eventually F r ε hr hε hδ0,
    zone_facts_eventually F r ε hr hε (ε₀ := δ ^ 2) (by positivity),
    ERRin_small_eventually F r ε hr hε hδ3,
    sizeR_LL_le_NfamQ_eventually F r ε hr hε hδ3 hδ31,
    reg_eventually F r ε hr hε]
    with Qn hreg₁ hreg₂ hreg₃ hreg₄ hreg₅ hreg₆ hbas hsharp hz1 hz2 herr hsN hregQ
  intro P hdes
  have hP := hdes.1
  have hQ := FrobAssembly.Q_of_design hdes
  obtain ⟨hlogK₁, hTK₁, -, -, -, hX32, -, -⟩ := hreg₁ P hdes
  obtain ⟨-, hTK₂, -, -, -, -, -, -⟩ := hreg₂ P hdes
  obtain ⟨hlogK₃, hTK₃, -, -, -, -, -, -⟩ := hreg₃ P hdes
  obtain ⟨-, -, -, -, hszK₄, -, -, -⟩ := hreg₄ P hdes
  obtain ⟨-, -, -, -, -, -, hQhalf₅, -⟩ := hreg₅ P hdes
  obtain ⟨hlogK₆, -, -, -, -, -, -, -⟩ := hreg₆ P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  obtain ⟨-, -, -, hs8, -, -, -, -, -⟩ := hregQ P hdes
  obtain ⟨hz1a, -⟩ := hz1 P hdes
  obtain ⟨-, hz2b⟩ := hz2 P hdes
  have hN := hsharp P hdes
  have herr' := herr P hdes
  have hsN' := hsN P hdes
  have hs0 : 0 ≤ P.s0 := by linarith
  have hQn : Qn ≤ ⌊P.Q⌋₊ := by rw [hQ, Nat.floor_natCast]
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2:ℝ) ≤ Qn := by exact_mod_cast hQn2
  have hQn0 : (0:ℝ) < Qn := by linarith
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hL0 : 0 < P.LB := hP.LB_pos
  have ha := hP.a_ge
  have ha0 := hP.aQ_pos
  have hcW : P.cWin = cWinDesign F := cWin_of_design hdes
  have hreg' : RegimeQ P := FrobAssembly.regimeQ_of hP hL8
  have hLS := largeSieveFamily_holds
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hadm := vDesign_admissible hP
  -- ── (1) the master inequality
  have h1 := famPP_total_le' F Qn P hP hw hLS hQn hs0 hδ0
  -- ── (2) the diagonal: `D_ℝ = (T/π) S (1+Esm)`, `|Esm| ≤ Cs/T ≤ δ`, `D_ℝ > 0`
  obtain ⟨Esm, hEsm, hdg⟩ := hdiag P hP hreg' hw (by rw [hcW])
  have hSpos : (0:ℝ) < sumA2gQ P := by
    have h := sumA2gQ_lower_const P hP hreg' hw
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have h6 : 0 < 6 - Real.log 2 := by linarith
    have h7 : 0 < Real.log 2 ^ 2 / 2 * (6 - Real.log 2) / 1296 := by positivity
    linarith only [h, h7]
  have hTCs : Cs / δ + 1 ≤ P.T := le_trans (le_max_right _ _) hTK₁
  have hCsδ : Cs ≤ P.T * δ := by
    have : Cs / δ ≤ P.T := by linarith
    rwa [div_le_iff₀ hδ0] at this
  have hEsmδ : |Esm| ≤ δ := by
    refine hEsm.trans ?_
    rw [div_le_iff₀ hTpos]
    linarith
  have hEsm1 : |Esm| < 1 := by
    refine lt_of_le_of_lt hEsm ?_
    rw [div_lt_one hTpos]
    have : Cs / δ ≥ Cs := by
      rw [ge_iff_le, le_div_iff₀ hδ0]
      exact mul_le_of_le_one_right hCs0.le hδ1
    linarith
  have hTS : 0 < P.T / Real.pi * sumA2gQ P := by positivity
  have hDpos : 0 < ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := by
    rw [hdg]
    exact mul_pos hTS (by linarith [(abs_lt.mp hEsm1).1])
  have hD0 : 0 ≤ ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := hDpos.le
  -- ── (3) the cross term: `2 N_ℝ = ρ D_ℝ`, `ρ ≤ δ`
  have hρ0 : 0 ≤ rhoU P Set.univ := rhoU_nonneg P Set.univ MeasurableSet.univ
  have hNρ : 2 * (∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))
      ≤ rhoU P Set.univ * ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := by
    have hDne : (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s)) ≠ 0 := hDpos.ne'
    have e : rhoU P Set.univ * (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
        = 2 * ∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s) := by
      unfold rhoU
      simp only [MeasureTheory.setIntegral_univ]
      field_simp
    rw [e]
  have hρδ : rhoU P Set.univ ≤ δ := by
    have hLρ : Lρ ≤ P.LB := by
      have : Lρ ≤ max 1 (max Lρ Tρ) := le_trans (le_max_left _ _) (le_max_right _ _)
      linarith [this.trans hlogK₃, hlogQ, FrobAssembly.LL_le_LB hP hlam]
    have hTρ : Tρ ≤ P.T := by
      have : Tρ ≤ max 1 (max Lρ Tρ) := le_trans (le_max_right _ _) (le_max_right _ _)
      linarith [this.trans hTK₃]
    have h := hρ P hP hw (by rw [hcW]) hLρ hTρ
    refine h.trans ?_
    have hT96 : 96 / (Real.pi * δ ^ 2) ≤ P.T := le_trans (le_max_right _ _) hTK₂
    unfold rhoConstConservative
    rw [← Real.sqrt_mul (by positivity)]
    have harg : 48 / Real.pi * (2 / P.T) ≤ δ ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hT96
      rw [show 48 / Real.pi * (2 / P.T) = 96 / (Real.pi * P.T) by
          rw [div_mul_div_comm]; norm_num, div_le_iff₀ (by positivity)]
      linarith
    calc Real.sqrt (48 / Real.pi * (2 / P.T)) ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt harg
      _ = δ := Real.sqrt_sq hδ0.le
  -- ── (4) the Mertens evaluation: `D_ℝ ≤ (X W k + E)(1+δ)`
  have hIL := FrobAssembly.intervalIntegral_gQ_mul_eq hP hw
  have hSle : sumA2gQ P
      ≤ P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2 + CM * P.LB ^ 2 := by
    have h := (abs_le.mp (hclose P hP hw hL8)).2
    rw [hIL] at h
    linarith
  have hDle : (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
      ≤ (P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P))
          + P.T / Real.pi * (CM * P.LB ^ 2)) * (1 + δ) := by
    rw [hdg]
    have hE1 : P.T / Real.pi * sumA2gQ P
        ≤ P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P))
          + P.T / Real.pi * (CM * P.LB ^ 2) := by
      have := mul_le_mul_of_nonneg_left hSle (by positivity : 0 ≤ P.T / Real.pi)
      calc P.T / Real.pi * sumA2gQ P
          ≤ P.T / Real.pi * (P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2
              + CM * P.LB ^ 2) := this
        _ = _ := by ring
    have hE2 : 1 + Esm ≤ 1 + δ := by linarith [(abs_le.mp hEsmδ).2]
    exact mul_le_mul hE1 hE2 (by linarith [(abs_lt.mp hEsm1).1])
      (add_nonneg (mul_nonneg (by positivity) (FrobAssembly.K0_add_K1_nonneg hadm)) (by positivity))
  -- ── (5) the budget: `B ≤ Q²(1+δ)`, `B X ≤ (1+δ)² C N`
  have hQ1 : (1:ℝ) ≤ P.Q := by rw [hQ]; linarith
  have hQ2pos : 0 < P.Q ^ 2 := by rw [hQ]; positivity
  have hBQ : sieveBudgetQ P ≤ P.Q ^ 2 * (1 + δ) := by
    have hbud := lemma43_budget_is_Qsq P (δ := 1 / 2) (by norm_num) (by norm_num) hX32 hQ1
    have h3 : sieveBudgetQ P / P.Q ^ 2 ≤ 1 + 4 * Real.rpow P.Q (-(1 / 2)) := by
      linarith [(abs_le.mp hbud).2]
    -- Gallagher budget: `lemma43_budget_is_Qsq`'s constant is `4` (was `2`); `design_regime`'s
    -- unchanged `2Q^{−1/2} ≤ 1/max 1 (3/δ) ≤ δ/3` still gives `4Q^{−1/2} ≤ 2δ/3 ≤ δ`.
    have h4 : 4 * Real.rpow P.Q (-(1 / 2)) ≤ δ := by
      have hm : 3 / δ ≤ max 1 (3 / δ) := le_max_right _ _
      have hmpos : 0 < max 1 (3 / δ) := by positivity
      have h5 : 3 ≤ max 1 (3 / δ) * δ := by
        have := mul_le_mul_of_nonneg_right hm hδ0.le
        rwa [div_mul_cancel₀ _ hδ0.ne'] at this
      have h6 : 1 / max 1 (3 / δ) ≤ δ / 3 := by
        rw [div_le_div_iff₀ hmpos (by norm_num)]
        linarith
      linarith [hQhalf₅]
    calc sieveBudgetQ P = sieveBudgetQ P / P.Q ^ 2 * P.Q ^ 2 :=
          (div_mul_cancel₀ _ hQ2pos.ne').symm
      _ ≤ (1 + δ) * P.Q ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hQ2pos.le
      _ = P.Q ^ 2 * (1 + δ) := by ring
  have hX0 : 0 ≤ P.T / (2 * Real.pi) * P.LL := by positivity
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hQ2X : P.Q ^ 2 * (P.T / (2 * Real.pi) * P.LL) ≤ F.Cconst * (1 + δ / 3) * NfamQ P F Qn := by
    rw [hQ]
    calc (Qn:ℝ) ^ 2 * (P.T / (2 * Real.pi) * P.LL)
        = (Qn:ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL := by ring
      _ ≤ _ := hN
  have hCN0 : 0 ≤ F.Cconst * NfamQ P F Qn := by positivity
  have hBX : sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)
      ≤ (1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn := by
    calc sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)
        ≤ P.Q ^ 2 * (1 + δ) * (P.T / (2 * Real.pi) * P.LL) :=
          mul_le_mul_of_nonneg_right hBQ hX0
      _ = (1 + δ) * (P.Q ^ 2 * (P.T / (2 * Real.pi) * P.LL)) := by ring
      _ ≤ (1 + δ) * (F.Cconst * (1 + δ / 3) * NfamQ P F Qn) :=
          mul_le_mul_of_nonneg_left hQ2X (by linarith)
      _ = (1 + δ) * (1 + δ / 3) * (F.Cconst * NfamQ P F Qn) := by ring
      _ ≤ (1 + δ) * (1 + δ) * (F.Cconst * NfamQ P F Qn) := by
          apply mul_le_mul_of_nonneg_right _ hCN0
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn := by ring
  -- ── (6) `K_f X ≤ (1+δ)² N`, `K_f ≤ B`, `0 ≤ K_f`
  have hS0 : 0 ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hERR0 : 0 ≤ ERRin P Qn := ERRin_nonneg P Qn hs0
  have hK0 : 0 ≤ F.sizeR Qn + ERRin P Qn := by linarith
  have hKfle : F.sizeR Qn + ERRin P Qn ≤ (1 + δ / 3) * F.sizeR Qn := by linarith
  have hKX : (F.sizeR Qn + ERRin P Qn) * (P.T / (2 * Real.pi) * P.LL)
      ≤ (1 + δ) ^ 2 * NfamQ P F Qn := by
    calc (F.sizeR Qn + ERRin P Qn) * (P.T / (2 * Real.pi) * P.LL)
        ≤ (1 + δ / 3) * F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL) :=
          mul_le_mul_of_nonneg_right hKfle hX0
      _ = (1 + δ / 3) * (F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL)) := by ring
      _ ≤ (1 + δ / 3) * ((1 + δ / 3) * NfamQ P F Qn) :=
          mul_le_mul_of_nonneg_left hsN' (by linarith)
      _ = (1 + δ / 3) * (1 + δ / 3) * NfamQ P F Qn := by ring
      _ ≤ (1 + δ) * (1 + δ) * NfamQ P F Qn := by
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      _ = (1 + δ) ^ 2 * NfamQ P F Qn := by ring
  have hsize := FrobAssembly.sizeR_le_point F Qn hQn1 hszK₄
  have hXQ1 : (1:ℝ) ≤ P.XQ := by
    unfold ParamsQ.XQ
    exact Real.one_le_exp hL0.le
  have hKB : F.sizeR Qn + ERRin P Qn ≤ sieveBudgetQ P := by
    have h1' : F.sizeR Qn + ERRin P Qn ≤ (1 + δ / 3) * (0.2 * (Qn:ℝ) ^ 2) :=
      hKfle.trans (mul_le_mul_of_nonneg_left hsize (by linarith))
    have h2' : (1 + δ / 3) * (0.2 * (Qn:ℝ) ^ 2) ≤ (4 / 3) * (0.2 * (Qn:ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3' : (Qn:ℝ) ^ 2 ≤ sieveBudgetQ P := by
      have hπX : 0 ≤ Real.pi * P.XQ := mul_nonneg Real.pi_pos.le (by linarith)
      unfold sieveBudgetQ; rw [hQ]; linarith
    linarith only [h1', h2', h3', sq_nonneg (Qn:ℝ)]
  -- ── (7) the zone facts
  have hP1 : P.T / (2 * Real.pi) * (∫ u in Set.Icc 0 P.s0, u * P.gQ u) * (1 - δ) ≤ zoneP P := by
    have := (abs_le.mp hz1a).1; linarith only [this]
  have hP2 : zoneP P ≤ P.T / (2 * Real.pi) * (∫ u in Set.Icc 0 P.s0, u * P.gQ u) * (1 + δ) := by
    have := (abs_le.mp hz1a).2; linarith only [this]
  have hR : zoneR P ≤ δ ^ 2 * zoneP P := hz2b
  have hI₀0 : 0 ≤ ∫ u in Set.Icc 0 P.s0, u * P.gQ u :=
    setIntegral_nonneg measurableSet_Icc fun u hu => mul_nonneg hu.1 (lemma42_g_nonneg P u)
  have hM0 : 0 ≤ P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u := by positivity
  have hM : 2 * (P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u)
      = P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * FrobAssembly.K0a (zoneFactor P) (vDesign P) :=
    zoneMain_eq P hP hw hs0
  -- ── (8) the kernel pieces
  have hk : K0 (vDesign P) + K1 (vDesign P)
      = FrobAssembly.K0a (zoneFactor P) (vDesign P) + FrobAssembly.K1a (zoneFactor P) (vDesign P) := by
    rw [FrobAssembly.K0a_add_K1a hadm, K0_add_K1 hadm]
  have hk0 : 0 ≤ FrobAssembly.K0a (zoneFactor P) (vDesign P) := FrobAssembly.K0a_nonneg hadm _
  have hk1 : 0 ≤ FrobAssembly.K1a (zoneFactor P) (vDesign P) := FrobAssembly.K1a_nonneg hadm _
  have hk2 : K0 (vDesign P) + K1 (vDesign P) ≤ 2 :=
    FrobAssembly.K0_add_K1_le_two hadm hP.lam_lt_two.le
  have hW0 : 0 ≤ (P.aQ * P.LB) ^ 2 := by positivity
  -- ── (9) the Mertens-remainder term: `B E ≤ δ W N`
  have hE0 : 0 ≤ P.T / Real.pi * (CM * P.LB ^ 2) := by positivity
  have hBE : sieveBudgetQ P * (P.T / Real.pi * (CM * P.LB ^ 2))
      ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by
    have hLL128 : 128 * F.Cconst * CM / (9 * δ) ≤ P.LL :=
      le_trans (le_trans (le_max_right _ _) hlogK₆) hlogQ
    have hB0 : 0 ≤ sieveBudgetQ P := hK0.trans hKB
    have e1 : sieveBudgetQ P * (P.T / Real.pi * (CM * P.LB ^ 2))
        = (sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL) := by
      field_simp
    have hLB2 : P.LB ^ 2 ≤ 16 / 9 * (P.aQ * P.LB) ^ 2 := by
      have : (3 / 4) ^ 2 ≤ P.aQ ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
      have h0 : 0 ≤ P.LB ^ 2 := sq_nonneg _
      calc P.LB ^ 2 = 16 / 9 * ((3 / 4) ^ 2 * P.LB ^ 2) := by ring
        _ ≤ 16 / 9 * (P.aQ ^ 2 * P.LB ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_right this h0
        _ = 16 / 9 * (P.aQ * P.LB) ^ 2 := by ring
    have hq : 2 * CM * P.LB ^ 2 / P.LL ≤ 32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL := by
      apply div_le_div_of_nonneg_right _ hLL0.le
      have := mul_le_mul_of_nonneg_left hLB2 (by positivity : 0 ≤ 2 * CM)
      linarith only [this]
    have h3 : (sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL)
        ≤ ((1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn)
            * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL) :=
      mul_le_mul hBX hq (by positivity) (mul_nonneg (mul_nonneg (by positivity) hC.le) hN0)
    have h4 : (1 + δ) ^ 2 ≤ 4 := by linarith only [hδδ, hδ1]
    have h5 : 128 / 9 * F.Cconst * CM / P.LL ≤ δ := by
      rw [div_le_iff₀ hLL0]
      rw [div_le_iff₀ (by positivity)] at hLL128
      linarith only [hLL128]
    have h6 : ((1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn)
          * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL)
        = (1 + δ) ^ 2 * (32 / 9 * F.Cconst * CM / P.LL)
            * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
      field_simp
    have hWN0 : 0 ≤ (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by positivity
    have h7 : (1 + δ) ^ 2 * (32 / 9 * F.Cconst * CM / P.LL)
          * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn)
        ≤ 4 * (32 / 9 * F.Cconst * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
      have h0 : 0 ≤ (32 / 9 * F.Cconst * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
        positivity
      have := mul_le_mul_of_nonneg_right h4 h0
      linarith only [this]
    have h8 : 4 * (32 / 9 * F.Cconst * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn)
        ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by
      have e : 4 * (32 / 9 * F.Cconst * CM / P.LL) = 128 / 9 * F.Cconst * CM / P.LL := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right h5 hWN0
      linarith only [this]
    calc sieveBudgetQ P * (P.T / Real.pi * (CM * P.LB ^ 2))
        = (sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL) := e1
      _ ≤ ((1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn)
            * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL) := h3
      _ = (1 + δ) ^ 2 * (32 / 9 * F.Cconst * CM / P.LL)
            * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := h6
      _ ≤ 4 * (32 / 9 * F.Cconst * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := h7
      _ ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := h8
  -- ── (10) assemble
  exact final_arith (ρ := rhoU P Set.univ) (X := P.T / (2 * Real.pi) * P.LL)
    (k := K0 (vDesign P) + K1 (vDesign P)) h1 hNρ hρ0 hρδ hD0 hDle hBE hE0 hP1 hP2 hR hM hM0
    hδ0 le_rfl hδ1 hK0 hKB hBX hKX hk hk0 hk1 hk2 hC hW0 hN0 hX0 hδε

end Final

end InZone
end ZetaQ

namespace ZetaQ
namespace InZone
open ZetaQ.Zones ZetaQ.Payoff

/-! ## 13. The same mean value for §4's own family sum `famSum` (`q ≤ ⌊Q⌋₊`), i.e. for the
objects `inZoneFormFam P (acoefLow P)` / `zoneP P` of `lemma44_zone_boundary`'s `hmv` -/

section FamSumVersion

theorem pairSumS_famRange_le (P : ParamsQ) (n m : ℕ) (hne : n ≠ m) :
    ‖pairSumS (Finset.Icc 1 ⌊P.Q⌋₊) n m‖
      ≤ (⌊P.Q⌋₊ : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) :=
  lemma5_2_crude ⌊P.Q⌋₊ n m hne

theorem sizeS_famRange (P : ParamsQ) : sizeS (Finset.Icc 1 ⌊P.Q⌋₊) = (famCardQ P : ℝ) := by
  unfold sizeS famCardQ famCard
  push_cast
  rfl

/-- the `famSum` error coefficient `ERR′_in := ⌊Q⌋₊·2Y_n(1 + log Y_n)`. -/
def ERRinQ (P : ParamsQ) : ℝ := (⌊P.Q⌋₊ : ℝ) * (2 * ((Yn P : ℝ) * (1 + Real.log (Yn P))))

/-- the coprimality-weighted diagonal for the `q ≤ ⌊Q⌋₊` family. -/
def diagLowWQ (P : ParamsQ) (s : ℝ) : ℝ :=
  ∑ n ∈ Nlow P, ‖acoefS P n s‖ ^ 2 * famCountAt (Finset.Icc 1 ⌊P.Q⌋₊) n

/-- **the `famSum` mean value, pointwise, both directions.** -/
theorem famSum_low_pointwise (P : ParamsQ) (hs0 : 0 ≤ P.s0) (s : ℝ) :
    |famSum P (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2) - diagLowWQ P s|
      ≤ ERRinQ P * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 := by
  have h := meanValue_generic (Finset.Icc 1 ⌊P.Q⌋₊) (Nlow P) (fun n => acoefS P n s)
    (cQ := (⌊P.Q⌋₊ : ℝ)) (Nat.cast_nonneg _) (Yn P) (one_le_Yn P hs0) (Nlow_subset P)
    (fun n m hne => pairSumS_famRange_le P n m hne)
  unfold famSum ERRinQ diagLowWQ
  simp_rw [AchiC_low_eq]
  rw [normA2_low_eq]
  exact h

theorem famSum_low_pointwise_upper (P : ParamsQ) (hs0 : 0 ≤ P.s0) (s : ℝ) :
    famSum P (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2)
      ≤ ((famCardQ P : ℝ) + ERRinQ P) * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2 := by
  have h := meanValue_upper (Finset.Icc 1 ⌊P.Q⌋₊) (Nlow P) (fun n => acoefS P n s)
    (cQ := (⌊P.Q⌋₊ : ℝ)) (Nat.cast_nonneg _) (Yn P) (one_le_Yn P hs0) (Nlow_subset P)
    (fun n m hne => pairSumS_famRange_le P n m hne)
  unfold famSum ERRinQ
  simp_rw [AchiC_low_eq]
  rw [normA2_low_eq, ← sizeS_famRange]
  exact h

theorem famSum_normSq_continuous' (P : ParamsQ) (c : ℕ → ℝ → ℂ) (hc : ∀ n, Continuous (c n)) :
    Continuous (fun s => famSum P (fun _ χ => ‖AchiC P c χ s‖ ^ 2)) := by
  unfold famSum
  exact continuous_finsetSum _ fun q _ => continuous_finsetSum _ fun χ _ =>
    (AchiC_continuous P c hc χ).norm.pow 2

/-- `inZoneFormFam P c = ∫_U g·famSum(‖A_χ‖²)`. -/
theorem inZoneFormFam_eq_integral (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    (c : ℕ → ℝ → ℂ) (hc : ∀ n, Continuous (c n)) :
    inZoneFormFam P c
      = ∫ s in inZone P, P.gQ s * famSum P (fun _ χ => ‖AchiC P c χ s‖ ^ 2) := by
  unfold inZoneFormFam famSum
  have hint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      IntegrableOn (fun s => P.gQ s * ‖AchiC P c χ s‖ ^ 2) (inZone P) :=
    fun q χ => gQ_AchiC_integrableOn P hP hw c hc χ _
  dsimp only
  have e : ∀ s : ℝ, P.gQ s * ∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ primitiveChars q,
        ‖AchiC P c χ s‖ ^ 2
      = ∑ q ∈ Finset.Icc 1 ⌊P.Q⌋₊, ∑ χ ∈ primitiveChars q, P.gQ s * ‖AchiC P c χ s‖ ^ 2 := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
  simp_rw [e]
  rw [MeasureTheory.integral_finsetSum _ (fun q _ =>
    MeasureTheory.integrable_finsetSum _ fun χ _ => hint q χ)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun χ _ => hint q χ)]

/-- **the integrated `famSum` mean value, upper half** — the UPPER bound on the object of
`lemma44_zone_boundary`'s `hmv`: `inZoneFormFam P (acoefLow P) ≤ (|𝔉_Q| + ERR′_in)·zoneP`. -/
theorem inZoneFormFam_low_le (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    (hs0 : 0 ≤ P.s0) :
    inZoneFormFam P (acoefLow P) ≤ ((famCardQ P : ℝ) + ERRinQ P) * zoneP P := by
  rw [inZoneFormFam_eq_integral P hP hw _ (acoefLow_continuous P)]
  unfold zoneP
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ (measurableSet_inZone P) ?_
  · exact (gQ_mul_integrable P hP hw
      (famSum_normSq_continuous' P _ (acoefLow_continuous P))).integrableOn
  · exact (gQ_coefSum_integrableOn P hP hw _ (acoefLow_continuous P) _).const_mul _
  · intro s _
    have h := famSum_low_pointwise_upper P hs0 s
    have hg := lemma42_g_nonneg P s
    calc P.gQ s * famSum P (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2)
        ≤ P.gQ s * (((famCardQ P : ℝ) + ERRinQ P) * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hg
      _ = _ := by ring

theorem diagLowWQ_continuous (P : ParamsQ) : Continuous (fun s => diagLowWQ P s) := by
  unfold diagLowWQ
  exact continuous_finsetSum _ fun n _ =>
    ((acoefS_continuous P n).norm.pow 2).mul continuous_const

/-- **the integrated `famSum` mean value, both directions**:
`|inZoneFormFam P (acoefLow P) − ∫_U g·Σ_{n≤Y}‖a_n‖²N_𝔉(n)| ≤ ERR′_in·zoneP`. -/
theorem inZoneFormFam_low_two_sided (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    (hs0 : 0 ≤ P.s0) :
    |inZoneFormFam P (acoefLow P) - ∫ s in inZone P, P.gQ s * diagLowWQ P s|
      ≤ ERRinQ P * zoneP P := by
  rw [inZoneFormFam_eq_integral P hP hw _ (acoefLow_continuous P)]
  have hi1 : IntegrableOn
      (fun s => P.gQ s * famSum P (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2)) (inZone P) :=
    (gQ_mul_integrable P hP hw (famSum_normSq_continuous' P _ (acoefLow_continuous P))).integrableOn
  have hi2 : IntegrableOn (fun s => P.gQ s * diagLowWQ P s) (inZone P) :=
    (gQ_mul_integrable P hP hw (diagLowWQ_continuous P)).integrableOn
  have hi3 : IntegrableOn
      (fun s => ERRinQ P * (P.gQ s * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2)) (inZone P) :=
    (gQ_coefSum_integrableOn P hP hw _ (acoefLow_continuous P) _).const_mul _
  rw [← MeasureTheory.integral_sub hi1 hi2]
  unfold zoneP
  rw [← MeasureTheory.integral_const_mul, ← Real.norm_eq_abs]
  refine MeasureTheory.norm_integral_le_of_norm_le hi3 ?_
  refine Filter.Eventually.of_forall fun s => ?_
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (lemma42_g_nonneg P s)]
  have h := famSum_low_pointwise P hs0 s
  have hg := lemma42_g_nonneg P s
  calc P.gQ s * |famSum P (fun _ χ => ‖AchiC P (acoefLow P) χ s‖ ^ 2) - diagLowWQ P s|
      ≤ P.gQ s * (ERRinQ P * ∑ n ∈ primeRangeQ P, ‖acoefLow P n s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h hg
    _ = _ := by ring

end FamSumVersion

end InZone
end ZetaQ
