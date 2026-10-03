/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/EvenFam.lean — the EVEN and ODD primitive subfamilies as `ZetaQ.Normalisation.Subfamily`
terms, together with their `SubfamilyAdmissible … (1/2)` certificates.

This discharges the `hdens` hypothesis of `ZetaQ.Cor3.corollary3_even_dyadic`,
`ZetaQ.Cor3.corollary3_odd_dyadic` and `ZetaQ.Cor3.corollary3_even_qQ`
(`ZetaQ/Normalisation.lean`).

Every result lives in the namespace `ZetaQ.Cor3.EvenFamInstance`; no existing declaration is
changed.

# ⚠ THIS FILE IS A TERMINAL CONSUMER — deliberately, and checked

`ZetaQ/EvenFam.lean` is imported by NOTHING except the umbrella root `ZetaQ.lean`. That is not
an oversight and it is not the `Cor3Smooth.lean` trap: the three `corollary3_*` theorems in §6
below ARE the deliverable — they are Corollary 3's statements with the `hdens` hypothesis
discharged, and they are what `audit/final_axioms.lean` prints axioms for. `inZoneProjector_*`
and `admissible_*` exist to feed them and are consumed in this file, one section down.

In particular the §§4–10 spine does NOT want this file:

  * the parity IN-ZONE mean value (`ZetaQ/InZone.lean` §3′) does not route through
    `Normalisation.InZoneProjector`. It goes through the pair bounds directly, at the sharper
    per-modulus constant `Q·τ(|n−m|) + Q·τ(n+m)` over `F.moduli Qn`, where `pair_bound` below
    gives `2Q·τ(|n−m|) + 2Q·τ(n+m)` over `Finset.Icc 1 Q` — related, but neither implies the
    other, and neither is a duplicate of the other.
  * the character-set bridge that WAS shared is now proved once, in
    `ZetaQ/Normalisation.lean` §12.3 (`ZetaQ.Cor3.primitiveCharsEven_eq` / `primitiveCharsOdd_eq`);
    §1 below cites it.

`import ZetaQ.EvenFam` in `ZetaQ/InZone.lean` would be acyclic (`EvenFam` imports only
`Normalisation`) and is available if a future landing prefers the projector route. Nothing in
the tree needs it today.
-/
import ZetaQ.Normalisation

open scoped BigOperators
open Filter Asymptotics

namespace ZetaQ.Cor3.EvenFamInstance

open ZetaQ.Normalisation

/-! ## 1. Glue — the `CharSums` spelling and the `Cor3` spelling of the parity classes agree.

`ZetaQ.primitiveCharsEven` filters on `DirichletCharacter.Even`; `ZetaQ.Cor3.evenPrimitiveChars`
filters on the frozen `ZetaQ.parity χ = 0`. Equal, but NOT `rfl`.

**The bridge is proved ONCE, in `ZetaQ/Normalisation.lean` §12.3**
(`ZetaQ.Cor3.primitiveCharsEven_eq` / `primitiveCharsOdd_eq`, the earliest file that sees both
spellings). The two names below are kept as aliases because this file's callers use them; they
are citations, not second proofs. -/

theorem primitiveCharsEven_eq (q : ℕ) :
    ZetaQ.primitiveCharsEven q = ZetaQ.Cor3.evenPrimitiveChars q :=
  ZetaQ.Cor3.primitiveCharsEven_eq q

theorem primitiveCharsOdd_eq (q : ℕ) :
    ZetaQ.primitiveCharsOdd q = ZetaQ.Cor3.oddPrimitiveChars q :=
  ZetaQ.Cor3.primitiveCharsOdd_eq q

/-! ## 2. The two subfamilies. -/

/-- The even primitive subfamily as a `Subfamily`. -/
noncomputable def evenFam : Subfamily where
  sel := ZetaQ.Cor3.evenPrimitiveChars
  sub := fun _ => Finset.filter_subset _ _

/-- The odd primitive subfamily as a `Subfamily`. -/
noncomputable def oddFam : Subfamily where
  sel := ZetaQ.Cor3.oddPrimitiveChars
  sub := fun _ => Finset.filter_subset _ _

@[simp] theorem evenFam_sel (q : ℕ) : evenFam.sel q = ZetaQ.Cor3.evenPrimitiveChars q := rfl

@[simp] theorem oddFam_sel (q : ℕ) : oddFam.sel q = ZetaQ.Cor3.oddPrimitiveChars q := rfl

/-! ## 3. Obligation (ii): the in-zone orthogonality projector. -/

/-- Every Dirichlet character takes the value `±1` at `−1`, so `‖1 + χ(−1)‖ ≤ 2`. -/
theorem norm_one_add_chi_neg_one_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖(1 : ℂ) + χ (-1 : ZMod q)‖ ≤ 2 := by
  rcases χ.even_or_odd with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- The odd mirror: `‖1 − χ(−1)‖ ≤ 2`. -/
theorem norm_one_sub_chi_neg_one_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖(1 : ℂ) - χ (-1 : ZMod q)‖ ≤ 2 := by
  rcases χ.even_or_odd with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- The `θ = 1 + χ(−1)` twist turns the full-family bilinear sum into
`famPairSum + famPairSumNeg`. -/
theorem twisted_sum_add (Q n m : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q,
        ((1 : ℂ) + χ (-1 : ZMod q)) * (χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q))))
      = ZetaQ.famPairSum Q n m + ZetaQ.famPairSumNeg Q n m := by
  rw [ZetaQ.famPairSum, ZetaQ.famPairSumNeg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ZetaQ.primPairSum, ZetaQ.primPairSumNeg, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun χ _ => by ring

/-- The `θ = 1 − χ(−1)` twist turns the full-family bilinear sum into
`famPairSum − famPairSumNeg`. -/
theorem twisted_sum_sub (Q n m : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q,
        ((1 : ℂ) - χ (-1 : ZMod q)) * (χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q))))
      = ZetaQ.famPairSum Q n m - ZetaQ.famPairSumNeg Q n m := by
  rw [ZetaQ.famPairSum, ZetaQ.famPairSumNeg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ZetaQ.primPairSum, ZetaQ.primPairSumNeg, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun χ _ => by ring

/-- The common numeric step: `‖A ± B‖ ≤ Q·τ(|n−m|) + Q·τ(n+m) ≤ 2Q·τ(|n−m|) + 2Q·τ(n+m)`,
by Lemma 5.2 and Lemma 5.2′ in their crude forms. -/
theorem pair_bound (Q n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hne : n ≠ m)
    (z : ℂ) (hz : z = ZetaQ.famPairSum Q n m + ZetaQ.famPairSumNeg Q n m ∨
                 z = ZetaQ.famPairSum Q n m - ZetaQ.famPairSumNeg Q n m) :
    ‖z‖ ≤ 2 * (Q : ℝ) * ((((n : ℤ) - (m : ℤ)).natAbs.divisors.card : ℕ) : ℝ)
        + 2 * (Q : ℝ) * (((n + m).divisors.card : ℕ) : ℝ) := by
  have h1 : ‖ZetaQ.famPairSum Q n m‖
      ≤ (Q : ℝ) * ((((n : ℤ) - (m : ℤ)).natAbs.divisors.card : ℕ) : ℝ) :=
    ZetaQ.lemma5_2_crude Q n m hne
  have h2 : ‖ZetaQ.famPairSumNeg Q n m‖ ≤ (Q : ℝ) * (((n + m).divisors.card : ℕ) : ℝ) :=
    ZetaQ.lemma5_2'_crude Q n m hn hm
  have hQ : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have ht1 : (0 : ℝ) ≤ ((((n : ℤ) - (m : ℤ)).natAbs.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht2 : (0 : ℝ) ≤ (((n + m).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hp1 := mul_nonneg hQ ht1
  have hp2 := mul_nonneg hQ ht2
  rcases hz with hz | hz
  · rw [hz]
    have := norm_add_le (ZetaQ.famPairSum Q n m) (ZetaQ.famPairSumNeg Q n m)
    linarith
  · rw [hz]
    have := norm_sub_le (ZetaQ.famPairSum Q n m) (ZetaQ.famPairSumNeg Q n m)
    linarith

theorem inZoneProjector_even : InZoneProjector evenFam (1 / 2 : ℝ) := by
  refine ⟨fun q χ => (1 : ℂ) + χ (-1 : ZMod q), fun q χ => norm_one_add_chi_neg_one_le χ,
    ?_, ?_⟩
  · intro q f
    show ∑ χ ∈ ZetaQ.Cor3.evenPrimitiveChars q, f χ = _
    rw [ZetaQ.Cor3.parity_projector_even f]
    push_cast
    ring
  · intro Q n m hn hm hne
    rw [twisted_sum_add]
    exact pair_bound Q n m hn hm hne _ (Or.inl rfl)

theorem inZoneProjector_odd : InZoneProjector oddFam (1 / 2 : ℝ) := by
  refine ⟨fun q χ => (1 : ℂ) - χ (-1 : ZMod q), fun q χ => norm_one_sub_chi_neg_one_le χ,
    ?_, ?_⟩
  · intro q f
    show ∑ χ ∈ ZetaQ.Cor3.oddPrimitiveChars q, f χ = _
    rw [ZetaQ.Cor3.parity_projector_odd f]
    push_cast
    ring
  · intro Q n m hn hm hne
    rw [twisted_sum_sub]
    exact pair_bound Q n m hn hm hne _ (Or.inr rfl)

/-! ## 4. A general admissibility criterion at `α = 1/2`.

Both parity classes satisfy `2·#(S q) = φ*(q) ± S(q)` with `|S(q)| ≤ 1`
(`evenPrimCount_eq` / `oddPrimCount_eq`, `abs_Sq_le_one`). Everything else — the density
`1/2` and the matching of conductor averages — follows from that single arithmetic input,
so it is proved once here and instantiated twice. -/

/-- `Σ_{q ≤ x} a(q)`, as a real. -/
noncomputable def intSum (a : ℕ → ℤ) (x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, ((a q : ℤ) : ℝ)

/-- `Σ_{q ≤ x} a(q)·log q`, as a real. -/
noncomputable def intLogSum (a : ℕ → ℤ) (x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, ((a q : ℤ) : ℝ) * Real.log (q : ℝ)

theorem abs_intSum_le (a : ℕ → ℤ) (ha : ∀ q : ℕ, 1 ≤ q → |a q| ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    |intSum a x| ≤ x := by
  have h1 : |intSum a x| ≤ ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, |((a q : ℤ) : ℝ)| := by
    unfold intSum
    exact Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, |((a q : ℤ) : ℝ)| ≤ ∑ _q ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.mem_Icc] at hq
    have hb := ha q hq.1
    have hcr : ((|a q| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hb
    rwa [Int.cast_abs] at hcr
  have h3 : (∑ _q ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ)) = (⌊x⌋₊ : ℝ) := by simp
  have h4 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  linarith

theorem abs_intLogSum_le (a : ℕ → ℤ) (ha : ∀ q : ℕ, 1 ≤ q → |a q| ≤ 1) (x : ℝ) (hx : 1 ≤ x) :
    |intLogSum a x| ≤ x * Real.log x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : |intLogSum a x|
      ≤ ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, |((a q : ℤ) : ℝ) * Real.log (q : ℝ)| := by
    unfold intLogSum
    exact Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, |((a q : ℤ) : ℝ) * Real.log (q : ℝ)|
      ≤ ∑ _q ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x := by
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.mem_Icc] at hq
    have hq1 : 1 ≤ q := hq.1
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hqx : (q : ℝ) ≤ x :=
      le_trans (by exact_mod_cast hq.2) (Nat.floor_le (le_of_lt hx0))
    have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
    have hlqx : Real.log (q : ℝ) ≤ Real.log x := Real.log_le_log hqpos hqx
    have hab : |((a q : ℤ) : ℝ)| ≤ 1 := by
      have hb := ha q hq1
      have hcr : ((|a q| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hb
      rwa [Int.cast_abs] at hcr
    rw [abs_mul, abs_of_nonneg hlq]
    calc |((a q : ℤ) : ℝ)| * Real.log (q : ℝ)
        ≤ 1 * Real.log x := mul_le_mul hab hlqx hlq zero_le_one
      _ = Real.log x := one_mul _
  have h3 : (∑ _q ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x) = (⌊x⌋₊ : ℝ) * Real.log x := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have h4 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (le_of_lt hx0)
  have h5 : (⌊x⌋₊ : ℝ) * Real.log x ≤ x * Real.log x := mul_le_mul_of_nonneg_right h4 hlx
  linarith

/-- `(A/t)/(B/t) = A/B` for `t ≠ 0` — used to pass from `x²`-normalised limits to raw ratios. -/
theorem div_div_div_cancel (A B t : ℝ) (ht : t ≠ 0) : (A / t) / (B / t) = A / B := by
  rw [div_div_eq_mul_div, div_mul_cancel₀ A ht]

/-- `log x / x → 0`. -/
theorem tendsto_log_div_atTop : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
  simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- `⟨log q⟩_{φ*,q≤x} / x → 0`: the conductor average grows like `log x`. -/
theorem tendsto_avgLogCond_div_atTop :
    Tendsto (fun x : ℝ => avgLogCond x / x) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => (avgLogCond x - Real.log x) * x⁻¹) atTop
      (nhds ((-(1 : ℝ) / 2) * 0)) := avgLogCond_asymp.mul tendsto_inv_atTop_zero
  rw [mul_zero] at h1
  have h2 := h1.add tendsto_log_div_atTop
  rw [add_zero] at h2
  refine h2.congr fun x => ?_
  ring

/-- **The criterion.** A subfamily whose per-modulus count satisfies
`2·#(S q) = φ*(q) + a(q)` with `|a(q)| ≤ 1`, and which admits the in-zone projector at
`α = 1/2`, is `SubfamilyAdmissible … (1/2)`. -/
theorem admissible_half (S : Subfamily) (a : ℕ → ℤ)
    (hcard : ∀ q : ℕ, (2 : ℤ) * (((S.sel q).card : ℕ) : ℤ) = ((ZetaQ.phiStar q : ℕ) : ℤ) + a q)
    (ha : ∀ q : ℕ, 1 ≤ q → |a q| ≤ 1)
    (hproj : InZoneProjector S (1 / 2 : ℝ)) :
    SubfamilyAdmissible S (1 / 2 : ℝ) := by
  -- the two counting identities, transported to ℝ
  have hcardR : ∀ x : ℝ, 2 * subfamCardR S x = famCardR x + intSum a x := by
    intro x
    have h : (2 : ℤ) * ((subfamCard S ⌊x⌋₊ : ℕ) : ℤ)
        = ((ZetaQ.famCard ⌊x⌋₊ : ℕ) : ℤ) + ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, a q := by
      unfold subfamCard ZetaQ.famCard
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => hcard q
    unfold subfamCardR famCardR intSum
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  have hlogsum : ∀ x : ℝ,
      2 * (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (((S.sel q).card : ℕ) : ℝ) * Real.log (q : ℝ))
        = (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, ((ZetaQ.phiStar q : ℕ) : ℝ) * Real.log (q : ℝ))
          + intLogSum a x := by
    intro x
    unfold intLogSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hr : (2 : ℝ) * (((S.sel q).card : ℕ) : ℝ)
        = ((ZetaQ.phiStar q : ℕ) : ℝ) + ((a q : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (hcard q)
    calc (2 : ℝ) * ((((S.sel q).card : ℕ) : ℝ) * Real.log (q : ℝ))
        = ((2 : ℝ) * (((S.sel q).card : ℕ) : ℝ)) * Real.log (q : ℝ) := by ring
      _ = (((ZetaQ.phiStar q : ℕ) : ℝ) + ((a q : ℤ) : ℝ)) * Real.log (q : ℝ) := by rw [hr]
      _ = ((ZetaQ.phiStar q : ℕ) : ℝ) * Real.log (q : ℝ)
            + ((a q : ℤ) : ℝ) * Real.log (q : ℝ) := by ring
  -- `Σ a(q) / x² → 0`
  have hCz : Tendsto (fun x : ℝ => intSum a x / x ^ 2) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_inv_atTop_zero (𝕜 := ℝ))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    have hb := abs_intSum_le a ha x (le_of_lt hx0)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx2, div_le_iff₀ hx2]
    have hxx : x⁻¹ * x ^ 2 = x := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx0), one_mul]
    rw [hxx]
    exact hb
  -- the subfamily has half the mass
  have hMlim : Tendsto (fun x : ℝ => subfamCardR S x / x ^ 2) atTop
      (nhds (9 / Real.pi ^ 4)) := by
    have h1 : Tendsto (fun x : ℝ => famCardR x / x ^ 2 / 2 + intSum a x / x ^ 2 / 2) atTop
        (nhds ((18 / Real.pi ^ 4) / 2 + 0 / 2)) :=
      (famCard_asymp.div_const 2).add (hCz.div_const 2)
    have hval : (18 / Real.pi ^ 4 : ℝ) / 2 + 0 / 2 = 9 / Real.pi ^ 4 := by ring
    rw [hval] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hkey := hcardR x
    field_simp
    linarith
  have hpiN : (0 : ℝ) < 18 / Real.pi ^ 4 := by positivity
  have hpiM : (0 : ℝ) < 9 / Real.pi ^ 4 := by positivity
  -- eventual non-vanishing of both denominators
  have hNne : ∀ᶠ x : ℝ in atTop, famCardR x ≠ 0 := by
    have hp : ∀ᶠ x : ℝ in atTop, 0 < famCardR x / x ^ 2 :=
      famCard_asymp.eventually (eventually_gt_nhds hpiN)
    filter_upwards [hp] with x hx h
    rw [h, zero_div] at hx
    exact lt_irrefl 0 hx
  have hMne : ∀ᶠ x : ℝ in atTop, subfamCardR S x ≠ 0 := by
    have hp : ∀ᶠ x : ℝ in atTop, 0 < subfamCardR S x / x ^ 2 :=
      hMlim.eventually (eventually_gt_nhds hpiM)
    filter_upwards [hp] with x hx h
    rw [h, zero_div] at hx
    exact lt_irrefl 0 hx
  refine ⟨by norm_num, ?_, ?_, hproj⟩
  · -- density
    have h := hMlim.div famCard_asymp (ne_of_gt hpiN)
    have hval : (9 / Real.pi ^ 4 : ℝ) / (18 / Real.pi ^ 4) = 1 / 2 := by
      have h4 : (Real.pi : ℝ) ^ 4 ≠ 0 := by positivity
      field_simp
      norm_num
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx2 : (x : ℝ) ^ 2 ≠ 0 := by positivity
    exact div_div_div_cancel _ _ _ hx2
  · -- conductor matching
    have habs : Tendsto (fun x : ℝ => |avgLogCond x| / x) atTop (nhds 0) := by
      have h0 : Tendsto (fun x : ℝ => |avgLogCond x| / |x|) atTop (nhds 0) := by
        simpa [Real.norm_eq_abs] using
          tendsto_zero_iff_norm_tendsto_zero.mp tendsto_avgLogCond_div_atTop
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [abs_of_pos hx]
    have hg : Tendsto (fun x : ℝ => Real.log x / x + |avgLogCond x| / x) atTop (nhds 0) := by
      have := tendsto_log_div_atTop.add habs
      rwa [add_zero] at this
    -- the numerator is `o(x²)`
    have hnum : Tendsto
        (fun x : ℝ => (intLogSum a x - avgLogCond x * intSum a x) / x ^ 2) atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      have hxne : x ≠ 0 := ne_of_gt hx0
      have hx2 : (0 : ℝ) < x ^ 2 := by positivity
      have hA1 : |intLogSum a x| ≤ x * Real.log x := abs_intLogSum_le a ha x hx
      have hB1 : |intSum a x| ≤ x := abs_intSum_le a ha x (le_of_lt hx0)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx2, div_le_iff₀ hx2]
      have h1 : |intLogSum a x - avgLogCond x * intSum a x|
          ≤ |intLogSum a x| + |avgLogCond x| * |intSum a x| := by
        calc |intLogSum a x - avgLogCond x * intSum a x|
            = |intLogSum a x + -(avgLogCond x * intSum a x)| := by rw [sub_eq_add_neg]
          _ ≤ |intLogSum a x| + |-(avgLogCond x * intSum a x)| := abs_add_le _ _
          _ = |intLogSum a x| + |avgLogCond x| * |intSum a x| := by rw [abs_neg, abs_mul]
      have h2 : |avgLogCond x| * |intSum a x| ≤ |avgLogCond x| * x :=
        mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)
      have h3 : (Real.log x / x + |avgLogCond x| / x) * x ^ 2
          = x * Real.log x + |avgLogCond x| * x := by
        field_simp
      linarith
    -- the denominator is `≍ x²`
    have hden : Tendsto (fun x : ℝ => 2 * subfamCardR S x / x ^ 2) atTop
        (nhds (18 / Real.pi ^ 4)) := by
      have h1 : Tendsto (fun x : ℝ => 2 * (subfamCardR S x / x ^ 2)) atTop
          (nhds (2 * (9 / Real.pi ^ 4))) := hMlim.const_mul 2
      have hval : (2 : ℝ) * (9 / Real.pi ^ 4) = 18 / Real.pi ^ 4 := by ring
      rw [hval] at h1
      refine h1.congr fun x => ?_
      rw [mul_div_assoc]
    -- the exact algebraic identity, wherever both denominators are non-zero
    have hid : ∀ᶠ x : ℝ in atTop, subfamAvgLogCond S x - avgLogCond x
        = (intLogSum a x - avgLogCond x * intSum a x) / (2 * subfamCardR S x) := by
      filter_upwards [hNne, hMne] with x hN hM
      have h1 := hlogsum x
      have h2 := hcardR x
      have hA : intLogSum a x
          = 2 * (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (((S.sel q).card : ℕ) : ℝ) * Real.log (q : ℝ))
            - (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, ((ZetaQ.phiStar q : ℕ) : ℝ) * Real.log (q : ℝ)) := by
        linarith
      have hB : intSum a x = 2 * subfamCardR S x - famCardR x := by linarith
      unfold subfamAvgLogCond avgLogCond
      rw [hA, hB]
      field_simp
      ring
    have hquot := hnum.div hden (ne_of_gt hpiN)
    rw [zero_div] at hquot
    refine hquot.congr' ?_
    filter_upwards [hid, eventually_gt_atTop (0 : ℝ)] with x hxid hx
    have hx2 : (x : ℝ) ^ 2 ≠ 0 := by positivity
    show (intLogSum a x - avgLogCond x * intSum a x) / x ^ 2
        / (2 * subfamCardR S x / x ^ 2) = subfamAvgLogCond S x - avgLogCond x
    rw [div_div_div_cancel _ _ _ hx2]
    exact hxid.symm

/-! ## 5. The two instances. -/

/-- **Obligations (i) and (ii) of §12.3 for the EVEN primitive family, at `α = 1/2`.** -/
theorem admissible_even : SubfamilyAdmissible evenFam (1 / 2 : ℝ) := by
  refine admissible_half evenFam ZetaQ.Cor3.Sq ?_ ZetaQ.Cor3.abs_Sq_le_one inZoneProjector_even
  intro q
  show (2 : ℤ) * ((ZetaQ.Cor3.evenPrimCount q : ℕ) : ℤ)
      = ((ZetaQ.phiStar q : ℕ) : ℤ) + ZetaQ.Cor3.Sq q
  exact ZetaQ.Cor3.evenPrimCount_eq q

/-- **Obligations (i) and (ii) of §12.3 for the ODD primitive family, at `α = 1/2`.** -/
theorem admissible_odd : SubfamilyAdmissible oddFam (1 / 2 : ℝ) := by
  refine admissible_half oddFam (fun q => -(ZetaQ.Cor3.Sq q)) ?_ ?_ inZoneProjector_odd
  · intro q
    have h := ZetaQ.Cor3.oddPrimCount_eq q
    show (2 : ℤ) * ((ZetaQ.Cor3.oddPrimCount q : ℕ) : ℤ)
        = ((ZetaQ.phiStar q : ℕ) : ℤ) + -(ZetaQ.Cor3.Sq q)
    linarith
  · intro q hq
    rw [abs_neg]
    exact ZetaQ.Cor3.abs_Sq_le_one q hq

/-! ## 6. The three Corollary-3 instances, with `hdens` discharged. -/

theorem corollary3_even_dyadic (I : Normalisation.PassageInterface ZetaQ.CfamDyadic) :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Payoff.Admissible lam v ∧
      ((Payoff.Pcert_even : ℚ) : ℝ) ≤ I.pay evenFam v :=
  ZetaQ.Cor3.corollary3_even_dyadic evenFam admissible_even I

theorem corollary3_odd_dyadic (I : Normalisation.PassageInterface ZetaQ.CfamDyadic) :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Payoff.Admissible lam v ∧
      ((Payoff.Pcert_even : ℚ) : ℝ) ≤ I.pay oddFam v :=
  ZetaQ.Cor3.corollary3_odd_dyadic oddFam admissible_odd I

theorem corollary3_even_qQ (I : Normalisation.PassageInterface ZetaQ.Cfam) :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Payoff.Admissible lam v ∧
      ((Payoff.Pcert_evenQ : ℚ) : ℝ) ≤ I.pay evenFam v :=
  ZetaQ.Cor3.corollary3_even_qQ evenFam admissible_even I

end ZetaQ.Cor3.EvenFamInstance
