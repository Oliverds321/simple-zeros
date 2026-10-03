/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/CharSums.lean — paper §5, "The character-sum arithmetic".

Mathlib-only: apart from the notation in `ZetaQ/Defs.lean`, this file is independent of the
rest of `ZetaQ`.

Statement source of truth: paper §5. Derivations: `LEMMA_Q5` §Q5.i–§Q5.v. On the zone
exponent, **`K = 3` is the design value and `K = 2` is the proved minimum**: §5 proves the
latter, and the design of record charges the former.
Consumers of the parity bridge: paper §1.1 Corollary 3 and §12.3.

IMPORT: `ZetaQ.Defs` only (which is FROZEN and is not edited here). `primitiveChars`,
`phiStar`, `famCard`, `famCardDyadic` and `parity` come from Defs; everything else in this
file is §5-local and owned here.

## RULE 17 — section-wide verdict

**λ, X, w and D₀ do not occur anywhere in paper §5.** `T` occurs only inside ℒ, and only
through the *lower* bound `log Q ≤ ℒ` (true by definition, `ℒ = log(QT/2π)`), which is an
upper bound on nothing. Not one declaration below carries `λ ≤ 1`, `X ≤ T` or `D₀ = √T`.

Two places a reader could misread a cap, both cleared:

  * **the zone cutoff `Y = Q^{1−δ′} < Q`.** This is the certificate's *s*-zone split
    (paper §4: "the in-zone breakpoint is |s| ≤ (1 − δ′)·log Q"), NOT a bandwidth
    restriction. §5 never mentions `X`; the whole point of the two-zone architecture is
    that `n` runs to `X = Q^λ` with **λ > 1** and that §5 is only ever asked about the
    sub-range `n, m ≤ Y`. Paper §12.3: "positivity OUT-ZONE at C → 2C (the projection
    route fails there at λ > 1 by Q^{λ−1})".
  * **`n + m ≤ Q`.** Corollary 3 and §12.3 both say "in-zone n + m ≤ 2Q^{1−δ′} ≪ Q". That
    is a statement about *where the corollary applies* Lemmas 5.2′/5.3′, **not a hypothesis
    of them**. It is deliberately KEPT OUT of every signature below:
    at Lean level it would be indistinguishable from an `X ≤ Q`-style bandwidth cap.
    The smallness comes from the calibration at `Y = Q^{1−δ′}`, never from a hypothesis.

## Two transcription corrections, both recorded in the docstrings

  * Paper §5's "and ≤ Q·τ(n−1) for the linear sums" is **false at n = 1**
    (RHS `= Q·τ(0) = 0`, LHS `= Σ_{q≤Q} φ*(q) > 0`). `RAMANUJAN_NOTE §2` states the correct
    range "for n ≥ 2"; `2 ≤ n` is restored in `lemma5_2_crude_linear` and in
    `lemma5_2_linear`. Harmless in application: `Λ(1) = 0` forces `n, m ≥ 2` (paper §4).
  * Lemma 5.3's constant `C` is **absolute but NOT explicit** (`LEMMA_Q5 § Attack surface`
    item 2: "The sublemma's constant C is not optimized"). Stated existentially throughout;
    no numeral is invented.

## What §5 does NOT claim

  * **not** the χ/χ̄ cross term — paper §4 Lemma 4.5: "the χ/χ̄ cross term … is NOT covered
    by Lemma 5.2's orthogonality" (`LEMMA_Q7` item (1) is REFUTED at λ > 1);
  * **not** any pointwise divisor bound `τ ≤ Y^ε` (`LEMMA_Q5 §Q5.iii`: the pointwise
    ε = c/log log Y is not o(δ′) and would poison the zone edge; the divisor AVERAGE is
    used instead — `RAMANUJAN_NOTE §3`'s ε-route is superseded and is not transcribed);
  * **not** PNT — `M(y) = o(y)` sharpens constants only (paper §5, `LEMMA_Q5 §Q5.ii`);
  * **not** the identification of the normalising `Q²ℒ²` with §4's family diagonal
    (an obligation of the assembly, not of §5; the zone forms below divide by an
    explicit `Q²·ℒ²` and nothing more);
  * **not** the window/taper polylog factors (`LEMMA_Q5 §Q5.v` — a §7/LEMMA_QT obligation);
  * **not** `S(q) := Σ*_χ χ(−1)`, its multiplicative closed form, `Σ_{q≤Q} S(q) = O(Q)`, or
    `𝒩_even = ½𝒩 + O(QTℒ)` — those are **Corollary-3** objects (paper §1.1 L76–82), not §5
    ones, so that two files do not both define them. Note `S(q)` is
    exactly `primPairSumNeg q 1 1`, so the interface they need is already here.

## A note on parameters

`ParamsQ` is not used by §5 at all: every statement below is a statement about `ℕ` and `ℝ`.
The final section supplies the two bridge lemmas that connect `ParamsQ.zoneY` and
`ParamsQ.deltaPrime` to the `Y = Q^{1−δ′}` / `K = 3` shape used here, so the assembly
does not have to re-derive them.
-/
import ZetaQ.Defs

noncomputable section

open scoped BigOperators
open ComplexConjugate

namespace ZetaQ

/-! ## 0. §5-local objects

These are owned by this file. `primitiveChars`, `phiStar`, `famCard`, `famCardDyadic` and
`parity` are NOT redefined here — they live in the frozen `ZetaQ/Defs.lean`.

Decidability: every `Finset.filter` below carries a `letI := Classical.decPred` exactly as
`Defs.primitiveChars` does. `(n : ZMod f) = (m : ZMod f)` is in fact decidable for every `f`
(`ZMod.decidableEq`), and so is `Nat.Coprime`, but the classical instance is used uniformly
so that no signature depends on an instance-search outcome. -/

/-- `τ(k) = #{d : d ∣ k}` — the divisor function of paper §5. Note `τ(0) = 0` in Lean
(`Nat.divisors 0 = ∅`), which is why `n ≠ m` appears in Lemma 5.2 and `2 ≤ n` in its linear
form: see the file header. `ArithmeticFunction.sigma 0` agrees on the nose.

Paper §5 (456). Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: Mathlib only.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def tau (k : ℕ) : ℕ := k.divisors.card

/-- `M_{k}(N) := Σ_{r ≤ N, (r,k) = 1} μ(r)` — the **coprimality-restricted Mertens
function** named (but not defined) by paper §5 and defined by `LEMMA_Q5 §Q5.ii`. Written
`M_{nm}` in the paper, i.e. `k = n·m` at the call sites.

**Not in Mathlib** — Mathlib has no Mertens function at all. The argument is `N : ℕ = ⌊y⌋`:
the paper's `M_{nm}(Q/f)` is `mertensCoprime (n*m) (Q / f)` with ℕ-division, which is exactly
faithful since the summation condition `r ≤ Q/f` is `f·r ≤ Q`, i.e. `r ≤ ⌊Q/f⌋`. This is
also the convention of the shipped anchor `q5_check.py` (`M_coprime(Q // f, n*m)`).

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: Mathlib only.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def mertensCoprime (k N : ℕ) : ℤ :=
  letI := Classical.decPred (fun r : ℕ => Nat.Coprime r k)
  ∑ r ∈ (Finset.Icc 1 N).filter (fun r => Nat.Coprime r k),
    ArithmeticFunction.moebius r

/-- The real-argument variant `M_k(y) := M_k(⌊y⌋)`, for the crude bound `|M_k(y)| ≤ y`.

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: `mertensCoprime`.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def mertensCoprimeR (k : ℕ) (y : ℝ) : ℤ := mertensCoprime k ⌊y⌋₊

/-- `{f : f ∣ q and n ≡ m (mod f)}` — the index set of Lemma 5.1's right-hand side.

The paper writes `f | q, f | (n−m)`; `LEMMA_Q5 §Q5.i` writes `n ≡ m (mod f)`. Equivalent.
Resolved **in favour of the congruence form here** — it avoids ℕ-subtraction
and matches the proof route — and in favour of the divisor form at Lemma 5.2, where the
index set must be a `Finset`. `divisorsCong_eq_divisors_filter` is the bridge.

Paper §5. Derivation: `LEMMA_Q5` §Q5.i.
Depends on: Mathlib only.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def divisorsCong (q n m : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun f : ℕ => (n : ZMod f) = (m : ZMod f))
  q.divisors.filter (fun f => (n : ZMod f) = (m : ZMod f))

/-- `{f : f ∣ q and n ≡ 1 (mod f)}` — the index set of `LEMMA_Q5 §Q5.i` identity (A).

Paper §5 (the `m = 1` case). Derivation: `LEMMA_Q5` §Q5.i (A).
Depends on: Mathlib only.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def divisorsCongOne (q n : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun f : ℕ => (n : ZMod f) = 1)
  q.divisors.filter (fun f => (n : ZMod f) = 1)

/-- `{f : f ∣ q and n + m ≡ 0 (mod f)}` — the index set of the `n + m` variant, i.e.
Lemma 5.1 "applied at the congruence −n ≡ m (mod f)" (paper §5, Lemmas 5.2′/5.3′).

Paper §5. Derivation: none in the notes — see the FLAG on `lemma5_1'`.
Depends on: Mathlib only.
Rule 17: a definition with no hypotheses; in particular **no `n + m ≤ Q`** — see header. -/
def divisorsCongNeg (q n m : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun f : ℕ => ((n + m : ℕ) : ZMod f) = 0)
  q.divisors.filter (fun f => ((n + m : ℕ) : ZMod f) = 0)

/-- `{f : f ∣ k, f ≤ Q, (f, j) = 1}` — the index set of the aggregated identities
(Lemma 5.2 at `k = |n−m|`, Lemma 5.2′ at `k = n+m`, both at `j = nm`).

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: Mathlib only.
Rule 17: `f ≤ Q` is the paper's own summation range `f ≤ Q`, a condition on the *divisor*,
not on `n`, `m` or any analytic scale. λ, X, T, D₀ absent. -/
def aggDivisors (Q k j : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun f : ℕ => f ≤ Q ∧ Nat.Coprime f j)
  k.divisors.filter (fun f => f ≤ Q ∧ Nat.Coprime f j)

/-! ### The character sums -/

/-- `Σ*_{χ mod q} χ(n)χ̄(m)` — the per-modulus **pair** sum of Lemma 5.1.

`χ̄` is `conj`, following the paper (Mathlib's orthogonality is stated in the *inverse*
form; under `(m, q) = 1` the two agree — a one-line bridge for
`conj_char_eq_char_inv` below).

Paper §5. Derivation: `LEMMA_Q5` §Q5.i (B).
Depends on: `Defs.primitiveChars`.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def primPairSum (q n m : ℕ) : ℂ :=
  ∑ χ ∈ primitiveChars q, χ (n : ZMod q) * conj (χ (m : ZMod q))

/-- `Σ*_{χ mod q} χ(n)` — the per-modulus **linear** sum (`LEMMA_Q5 §Q5.i` identity (A)).
The paper compresses (A) into Lemma 5.1's `m = 1` case; it is separately consumed by ledger
rows 2 and 9 (`E6_ENUMERATION.md:161,168`).

Paper §5 ("the linear sums"). Derivation: `LEMMA_Q5` §Q5.i (A).
Depends on: `Defs.primitiveChars`.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def primLinSum (q n : ℕ) : ℂ := ∑ χ ∈ primitiveChars q, χ (n : ZMod q)

/-- `Σ*_{χ mod q} χ(−1)·χ(n)χ̄(m)` — the **parity-twisted** per-modulus pair sum: the object
Corollary 3's projector `½Σ*(1 ± χ(−1))` pairs against, and the one the `n + m` identity
governs. (`primPairSumNeg q 1 1` is Corollary 3's `S(q)`; that corollary owns the closed
form, not §5.)

Paper §5 / §1.1. Derivation: none in the notes.
Depends on: `Defs.primitiveChars`.
Rule 17: a definition with no hypotheses; **no `n + m ≤ Q`** — see the header. -/
def primPairSumNeg (q n m : ℕ) : ℂ :=
  ∑ χ ∈ primitiveChars q, χ (-1 : ZMod q) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))

/-- `Σ_{q≤Q} Σ*_{χ mod q} χ(n)χ̄(m)` — the aggregated family pair sum of Lemma 5.2.
`q = 1` contributes the trivial character's `1` (`LEMMA_Q5 §Q5.ii`: "matching f = r = 1").

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: `primPairSum`.
Rule 17: a definition with no hypotheses; no coupling of `Q` to `n`, `m`. -/
def famPairSum (Q n m : ℕ) : ℂ := ∑ q ∈ Finset.Icc 1 Q, primPairSum q n m

/-- `Σ_{q≤Q} Σ*_{χ mod q} χ(n)` — the aggregated family linear sum.

Paper §5. Derivation: `LEMMA_Q5` §Q5.i (A), §Q5.v.
Depends on: `primLinSum`.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def famLinSum (Q n : ℕ) : ℂ := ∑ q ∈ Finset.Icc 1 Q, primLinSum q n

/-- `Σ_{q≤Q} Σ*_{χ mod q} χ(−1)χ(n)χ̄(m)` — the aggregated parity-twisted sum: **the object
of Lemma 5.2′**, and the second half of Corollary 3's in-zone projector.

Paper §5. Derivation: none in the notes.
Depends on: `primPairSumNeg`.
Rule 17: a definition with no hypotheses; **no `n + m ≤ Q`**. -/
def famPairSumNeg (Q n m : ℕ) : ℂ := ∑ q ∈ Finset.Icc 1 Q, primPairSumNeg q n m

/-- `Σ_{Q/2 < q ≤ Q} Σ*_χ χ(n)χ̄(m)` — the **dyadic** family of Corollary 2 (`C = 2π⁴/27`).
The paper does not state a dyadic §5 lemma; `LEMMA_Q5 §Q5.ii` supplies it ("Dyadic family by
differencing"). `Finset.Ioc (Q/2) Q` with ℕ-division is the correct real-inequality dyadic
set for every `Q` and matches `Defs.famCardDyadic`.

Paper §5 (the "no case split" paragraph). Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: `primPairSum`.
Rule 17: a definition with no hypotheses; the dyadic range is a *conductor* restriction. -/
def famPairSumDyadic (Q n m : ℕ) : ℂ := ∑ q ∈ Finset.Ioc (Q / 2) Q, primPairSum q n m

/-- Dyadic parity-twisted family sum — Corollary 3 is stated for the **even primitive,
dyadic** family, so it needs this one as well as `famPairSumNeg`.

Paper §1.1 Corollary 3. Derivation: none in the notes.
Depends on: `primPairSumNeg`.
Rule 17: a definition with no hypotheses; **no `n + m ≤ Q`**. -/
def famPairSumNegDyadic (Q n m : ℕ) : ℂ := ∑ q ∈ Finset.Ioc (Q / 2) Q, primPairSumNeg q n m

/-! ### The even / odd primitive subfamilies (Corollary 3's projector targets) -/

/-- The **even** primitive characters mod `q`. `DirichletCharacter.Even ψ` is `ψ(−1) = 1`;
`Defs.parity` is `0` on exactly these.

Paper §1.1 Corollary 3, §2.2 (parity κ). Derivation: none in the notes.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def primitiveCharsEven (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.Even)
  (primitiveChars q).filter (fun χ => χ.Even)

/-- The **odd** primitive characters mod `q` (paper §1.1: "The identical argument with the
projector ½Σ*(1 − χ(−1)) gives the ODD primitive family at the same constants").

Paper §1.1 Corollary 3. Derivation: none in the notes.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def primitiveCharsOdd (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.Odd)
  (primitiveChars q).filter (fun χ => χ.Odd)

/-- `Σ_{χ even prim mod q} χ(n)χ̄(m)` — the per-modulus even-subfamily pair sum.

Paper §1.1 Corollary 3. Derivation: none in the notes.
Depends on: `primitiveCharsEven`.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def primPairSumEven (q n m : ℕ) : ℂ :=
  ∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q) * conj (χ (m : ZMod q))

/-- `Σ_{χ odd prim mod q} χ(n)χ̄(m)` — the per-modulus odd-subfamily pair sum.

Paper §1.1 Corollary 3. Derivation: none in the notes.
Depends on: `primitiveCharsOdd`.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def primPairSumOdd (q n m : ℕ) : ℂ :=
  ∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q) * conj (χ (m : ZMod q))

/-- `Σ_{q≤Q} Σ_{χ even prim} χ(n)χ̄(m)` — Corollary 3's in-zone object over `q ≤ Q`
("Even primitive over q ≤ Q: 0.6980745436 at C = π⁴/9").

Paper §1.1, §12.3. Derivation: none in the notes.
Depends on: `primPairSumEven`.
Rule 17: a definition with no hypotheses; **no `n + m ≤ Q`**. -/
def famPairSumEven (Q n m : ℕ) : ℂ := ∑ q ∈ Finset.Icc 1 Q, primPairSumEven q n m

/-- `Σ_{q≤Q} Σ_{χ odd prim} χ(n)χ̄(m)`.

Paper §1.1. Derivation: none in the notes.
Depends on: `primPairSumOdd`.
Rule 17: a definition with no hypotheses; **no `n + m ≤ Q`**. -/
def famPairSumOdd (Q n m : ℕ) : ℂ := ∑ q ∈ Finset.Icc 1 Q, primPairSumOdd q n m

/-- `Σ_{Q/2<q≤Q} Σ_{χ even prim} χ(n)χ̄(m)` — **the** Corollary-3 object
(`P_even,dyad = 0.6919434301`).

Paper §1.1, §12.3. Derivation: none in the notes.
Depends on: `primPairSumEven`.
Rule 17: a definition with no hypotheses; **no `n + m ≤ Q`**. -/
def famPairSumEvenDyadic (Q n m : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc (Q / 2) Q, primPairSumEven q n m

/-- `Σ_{Q/2<q≤Q} Σ_{χ odd prim} χ(n)χ̄(m)` (`P_odd,dyad = 0.6919434301`).

Paper §1.1. Derivation: none in the notes.
Depends on: `primPairSumOdd`.
Rule 17: a definition with no hypotheses; **no `n + m ≤ Q`**. -/
def famPairSumOddDyadic (Q n m : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc (Q / 2) Q, primPairSumOdd q n m

/-! ### The zone sums -/

/-- `S(Y) := Σ_{n ≠ m ≤ Y} Λ(n)Λ(m)(nm)^{−1/2}·τ(|n−m|)` — the low–low zone divisor-weighted
double prime sum of Lemma 5.3. Ordered pairs with the diagonal removed; `Λ(1) = 0` makes the
`n = 1` and `m = 1` terms vanish automatically, which is why no `2 ≤ n` is needed here.

Paper §5. Derivation: `LEMMA_Q5` §Q5.iii.
Depends on: `tau`.
Rule 17: a definition with no hypotheses. `Y` is a bare `ℕ`; the identification
`Y = Q^{1−δ′}` happens only in the *zone forms* below, and is a zone split, not a cap. -/
def zoneSum (Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ (Finset.Icc 1 Y).erase n,
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
      / Real.sqrt ((n : ℝ) * (m : ℝ)) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)

/-- `S′(Y) := Σ_{n, m ≤ Y} Λ(n)Λ(m)(nm)^{−1/2}·τ(n+m)` — the `n + m` analogue of `S(Y)`.

**Note the FULL square range**: no diagonal is excluded, faithful to paper §5's "with no
excluded diagonal (n = −m is impossible for positive n, m)".

Paper §5. Derivation: none in the notes (see the FLAG on `lemma5_3'`).
Depends on: `tau`.
Rule 17: a definition with no hypotheses; **no `n + m ≤ Q`**. -/
def zoneSumPlus (Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 Y,
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
      / Real.sqrt ((n : ℝ) * (m : ℝ)) * (tau (n + m) : ℝ)

/-! ## 1. Lemma 5.1 — primitive-character orthogonality

The hardest single item in §5, and not because of the algebra: **Mathlib has no
primitive decomposition of the character group**. The bijection
`{χ mod q} ≃ Σ_{f | q} {primitive ψ mod f}` (via `conductor` / `primitiveCharacter` /
`changeLevel`) has to be built. Once it exists, complete orthogonality plus Möbius inversion
over `Nat.divisors q` finishes quickly. -/

/-- **Sublemma** (the congruence/divisibility bridge).
`n ≡ m (mod f)` in the `ZMod f` sense is `f ∣ (n − m)` in ℤ. Stated as its own lemma rather
than reached for by Mathlib name, so that the two index conventions of §5 are related once.

Paper §5 ("f|(n−m)") vs `LEMMA_Q5` §Q5.i ("n ≡ m (mod f)").
Depends on: Mathlib only.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem cong_iff_dvd_sub (n m f : ℕ) :
    ((n : ZMod f) = (m : ZMod f)) ↔ (f : ℤ) ∣ ((n : ℤ) - (m : ℤ)) := by
  rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd, dvd_sub_comm]

/-- **Sublemma.** `−n ≡ m (mod f)` is `f ∣ (n + m)`. The `n + m` half of the R2 bridge.

Paper §5 ("applied at the congruence −n ≡ m (mod f) … over f | (n + m)").
Depends on: Mathlib only.
Rule 17: no hypotheses; **no `n + m ≤ Q`**. -/
theorem cong_neg_iff_dvd_add (n m f : ℕ) :
    (((n + m : ℕ) : ZMod f) = 0) ↔ f ∣ (n + m) := by
  rw [show ((n + m : ℕ) : ZMod f) = (((n + m : ℕ) : ℤ) : ZMod f) by push_cast; ring,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast]

/-- **Sublemma**. For `(m, q) = 1`, `χ̄(m) = χ(m⁻¹)`. The paper
writes `χ̄`, Mathlib's orthogonality is stated in the inverse form; this is the bridge, and
it is recorded here so that it does not have to be rediscovered.

Paper §5.
Depends on: Mathlib only.
Rule 17: `(m, q) = 1` only; λ, X, T, D₀ absent. -/
theorem conj_char_eq_char_inv {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ)
    (hm : Nat.Coprime m q) :
    conj (χ (m : ZMod q)) = χ ((m : ZMod q)⁻¹) := by
  have h1 : (m : ZMod q) * ((m : ZMod q))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one m hm
  have h2 : χ (m : ZMod q) * χ ((m : ZMod q)⁻¹) = 1 := by
    rw [← map_mul, h1, map_one]
  have hb1 : ‖χ (m : ZMod q)‖ ≤ 1 := χ.norm_le_one _
  have hb2 : ‖χ ((m : ZMod q)⁻¹)‖ ≤ 1 := χ.norm_le_one _
  have hprod : ‖χ (m : ZMod q)‖ * ‖χ ((m : ZMod q)⁻¹)‖ = 1 := by
    rw [← norm_mul, h2, norm_one]
  have hn : ‖χ (m : ZMod q)‖ = 1 := by
    nlinarith [norm_nonneg (χ (m : ZMod q)), norm_nonneg (χ ((m : ZMod q)⁻¹))]
  rw [← Complex.inv_eq_conj hn]
  exact inv_eq_of_mul_eq_one_right h2

/-- `{f : f ∣ q and f ∣ (n − m)}` — the paper's own spelling of Lemma 5.1's index set
("Σ_{f|q, f|(n−m)}"), as opposed to `divisorsCong`'s congruence spelling.
Both are carried so that neither §5 consumer has to translate; `divisorsCong_eq` is the
bridge.

Paper §5.
Depends on: Mathlib only.
Rule 17: a definition with no hypotheses; λ, X, T, D₀ absent. -/
def divisorsDvdSub (q n m : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun f : ℕ => (f : ℤ) ∣ ((n : ℤ) - (m : ℤ)))
  q.divisors.filter (fun f => (f : ℤ) ∣ ((n : ℤ) - (m : ℤ)))

/-- **Sublemma.** The two spellings of Lemma 5.1's index set agree — the paper's
`f | q, f | (n−m)` and `LEMMA_Q5 §Q5.i`'s `f | q, n ≡ m (mod f)`.

Paper §5.
Depends on: `cong_iff_dvd_sub`.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem divisorsCong_eq (q n m : ℕ) : divisorsCong q n m = divisorsDvdSub q n m := by
  letI := Classical.decPred (fun f : ℕ => (n : ZMod f) = (m : ZMod f))
  letI := Classical.decPred (fun f : ℕ => (f : ℤ) ∣ ((n : ℤ) - (m : ℤ)))
  ext f
  have h1 : f ∈ divisorsCong q n m ↔ f ∈ q.divisors ∧ ((n : ZMod f) = (m : ZMod f)) :=
    Finset.mem_filter
  have h2 : f ∈ divisorsDvdSub q n m ↔ f ∈ q.divisors ∧ ((f : ℤ) ∣ ((n : ℤ) - (m : ℤ))) :=
    Finset.mem_filter
  rw [h1, h2, cong_iff_dvd_sub]

/-- **THE KEYSTONE — the primitive decomposition of the Dirichlet character group.**

`{χ mod q} ≃ ⨆_{d ∣ q} {primitive ψ mod d}`, in the summed form that both §5 and Corollary 3
consume: for any family `G` of character functionals that is invariant under `changeLevel`,

    Σ_{χ mod q} G_q(χ) = Σ_{d ∣ q} Σ*_{ψ mod d} G_d(ψ).

**Not in Mathlib.** The bijection is `χ ↦ (conductor χ, primitiveCharacter χ)` with inverse
`(d, ψ) ↦ changeLevel ψ`; the proof fibres `Finset.univ` over `conductor` and identifies each
fibre with `primitiveChars d` through `changeLevel_injective` /
`mem_conductorSet_iff_conductor_dvd` / `conductor_changeLevel`.

The hypothesis `hG` is the *invariance* of the functional, i.e. exactly the statement that the
induced character agrees with its primitive inducer; at `G d ψ = ψ(n)ψ̄(m)` it is
`changeLevel_eq_cast_of_dvd'` under `(nm, q) = 1`, and at `G d ψ = ψ(−1)` it is the same with
`a = −1`, which is coprime to every modulus.

Paper §5 (the route sentence). Derivation: `LEMMA_Q5` §Q5.i.
It is also what gives `Σ_{d ∣ q} S(d) = 𝔖(q)`, hence `S(q) = μ(q) + [2∣q]μ(q/2)`, which
Corollary 3's even/odd split uses.
Depends on: Mathlib's conductor API only.
Rule 17: `NeZero q` only. λ, X, T, D₀ absent. -/
theorem sum_all_chars_eq_sum_divisors {q : ℕ} [NeZero q]
    (G : ∀ d : ℕ, DirichletCharacter ℂ d → ℂ)
    (hG : ∀ (d : ℕ) (hd : d ∣ q) (ψ : DirichletCharacter ℂ d),
        G q (DirichletCharacter.changeLevel hd ψ) = G d ψ) :
    ∑ χ : DirichletCharacter ℂ q, G q χ
      = ∑ d ∈ q.divisors, ∑ ψ ∈ primitiveChars d, G d ψ := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hmaps : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      χ.conductor ∈ q.divisors := fun χ _ =>
    Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq0⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun χ => G q χ)]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  refine (Finset.sum_bij (fun ψ _ => DirichletCharacter.changeLevel hdq ψ) ?_ ?_ ?_ ?_).symm
  · intro ψ hψ
    simp only [primitiveChars, Finset.mem_filter, Finset.mem_univ, true_and,
      DirichletCharacter.isPrimitive_def] at hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [DirichletCharacter.conductor_changeLevel, hψ]
  · intro ψ₁ _ ψ₂ _ h
    exact DirichletCharacter.changeLevel_injective hdq h
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    have hft : DirichletCharacter.FactorsThrough χ d :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hdq).mpr (by rw [hχ])
    refine ⟨hft.χ₀, ?_, (hft.eq_changeLevel).symm⟩
    simp only [primitiveChars, Finset.mem_filter, Finset.mem_univ, true_and,
      DirichletCharacter.isPrimitive_def]
    have h1 : (DirichletCharacter.changeLevel hft.dvd hft.χ₀).conductor
        = (hft.χ₀).conductor := DirichletCharacter.conductor_changeLevel _ _
    rw [← hft.eq_changeLevel] at h1
    rw [← h1, hχ]
  · intro ψ _
    exact (hG d hdq ψ).symm

/-- **Complete orthogonality, pair form.** `Σ_{χ mod d} χ(n)χ̄(m) = φ(d)·[n ≡ m (mod d)]` for
`(m, d) = 1` — `DirichletCharacter.sum_char_inv_mul_char_eq` composed with the `χ̄ = χ∘inv`
bridge `conj_char_eq_char_inv`.

Depends on: Mathlib, `conj_char_eq_char_inv`.
Rule 17: `NeZero d` and `(m, d) = 1` only. -/
theorem sum_all_chars_pair {d : ℕ} [NeZero d] (n m : ℕ) (hm : Nat.Coprime m d) :
    ∑ χ : DirichletCharacter ℂ d, χ (n : ZMod d) * conj (χ (m : ZMod d))
      = if (n : ZMod d) = (m : ZMod d) then (d.totient : ℂ) else 0 := by
  have hu : IsUnit ((m : ZMod d)) := (ZMod.isUnit_iff_coprime m d).mpr hm
  have hstep : ∀ χ : DirichletCharacter ℂ d, χ (n : ZMod d) * conj (χ (m : ZMod d))
      = χ ((m : ZMod d))⁻¹ * χ (n : ZMod d) := by
    intro χ; rw [conj_char_eq_char_inv χ m hm]; ring
  rw [Finset.sum_congr rfl (fun χ _ => hstep χ),
    DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod d)]
  by_cases h : (n : ZMod d) = (m : ZMod d)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- **The conductor-graded orthogonality relation** — the keystone at `G d ψ = ψ(n)ψ̄(m)`:
`Σ_{d ∣ q} Σ*_{ψ mod d} ψ(n)ψ̄(m) = φ(q)·[n ≡ m (mod q)]` for `(nm, q) = 1`. Möbius inversion
of this over the divisor lattice of `q` is Lemma 5.1.

Paper §5. Derivation: `LEMMA_Q5` §Q5.i.
Depends on: `sum_all_chars_eq_sum_divisors`, `sum_all_chars_pair`.
Rule 17: `0 < q` and the paper's own `(nm, q) = 1`. -/
theorem sum_divisors_primPairSum {q : ℕ} (hq : 0 < q) (n m : ℕ)
    (hnm : Nat.Coprime (n * m) q) :
    ∑ d ∈ q.divisors, primPairSum d n m
      = if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0 := by
  have : NeZero q := ⟨by omega⟩
  have hn : Nat.Coprime n q := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
  have hm : Nat.Coprime m q := Nat.Coprime.coprime_dvd_left (Dvd.intro_left n rfl) hnm
  have hcompat : ∀ (d : ℕ) (hd : d ∣ q) (ψ : DirichletCharacter ℂ d),
      (DirichletCharacter.changeLevel hd ψ) (n : ZMod q)
          * conj ((DirichletCharacter.changeLevel hd ψ) (m : ZMod q))
        = ψ (n : ZMod d) * conj (ψ (m : ZMod d)) := by
    intro d hd ψ
    have hcn : IsCoprime ((n : ℤ)) ((q : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
    have hcm : IsCoprime ((m : ℤ)) ((q : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hm
    have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' (R := ℂ) (χ := ψ) hd hcn
    have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' (R := ℂ) (χ := ψ) hd hcm
    push_cast at h1 h2
    rw [h1, h2]
  have key := sum_all_chars_eq_sum_divisors (q := q)
    (fun d ψ => ψ (n : ZMod d) * conj (ψ (m : ZMod d))) hcompat
  rw [sum_all_chars_pair (d := q) n m hm] at key
  simp only [primPairSum]
  exact key.symm

/-- **Lemma 5.1** (primitive-character orthogonality, pair form). For `(nm, q) = 1`,
`Σ*_{χ mod q} χ(n)χ̄(m) = Σ_{f | q, f | (n−m)} μ(q/f)·φ(f)` — "the standard
primitive-character orthogonality relation, in the form displayed in [CIS1, §3]".

Proof route fixed by `LEMMA_Q5 §Q5.i`: every χ mod q is induced by a unique primitive ψ mod
f(χ) | q with χ(n) = ψ(n) for (n,q) = 1; grouping by conductor gives
`Σ_{all χ mod q} χ(a) = Σ_{f|q} Σ*_{ψ mod f} ψ(a)`; the left side is `φ(q)·1_{a≡1(q)}`;
Möbius inversion in the divisor lattice of `q` inverts it. Then (B) follows from (A) at
`a = n·m̄`. Anchor: `Σ_{q≤60} φ*(q) = 662` vs `(18/π⁴)·60² = 665.2` (log_q5.txt).

Paper §5. Derivation: `LEMMA_Q5` §Q5.i identity (B).
The primitive decomposition of the character group is not in Mathlib, so it is built here.
Depends on: Mathlib only.
Rule 17: hypotheses are `NeZero q` (well-formedness of `DirichletCharacter ℂ q`) and the
paper's own `(nm, q) = 1`. No bandwidth hypothesis of any kind: Lemma 5.1 is λ-free, X-free,
T-free, D₀-free. -/
theorem lemma5_1 {q : ℕ} [NeZero q] (n m : ℕ) (hnm : Nat.Coprime (n * m) q) :
    primPairSum q n m
      = ∑ f ∈ divisorsCong q n m,
          ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) * (Nat.totient f : ℂ) := by
  classical
  set g : ℕ → ℂ := fun d => if (n : ZMod d) = (m : ZMod d) then (d.totient : ℂ) else 0
    with hgdef
  set F : ℕ → ℂ := fun d => primPairSum d n m with hFdef
  have hs : ∀ a b : ℕ, a ∣ b → b ∈ {d : ℕ | Nat.Coprime (n * m) d} →
      a ∈ {d : ℕ | Nat.Coprime (n * m) d} := fun a b hab hb =>
    Nat.Coprime.coprime_dvd_right hab hb
  have hmain : ∀ d > 0, d ∈ {d : ℕ | Nat.Coprime (n * m) d} →
      (∑ e ∈ d.divisors, F e) = g d := fun d hd hds =>
    sum_divisors_primPairSum hd n m hds
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on (R := ℂ)
      (f := F) (g := g) {d : ℕ | Nat.Coprime (n * m) d} hs).mp hmain q
      (Nat.pos_of_ne_zero (NeZero.ne q)) hnm
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun x y => ((ArithmeticFunction.moebius x : ℤ) : ℂ) * g y)] at hinv
  have hinv' : primPairSum q n m
      = ∑ i ∈ q.divisors, ((ArithmeticFunction.moebius (q / i) : ℤ) : ℂ) * g i := hinv.symm
  rw [hinv', divisorsCong, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [hgdef]
  by_cases h : (n : ZMod d) = (m : ZMod d)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **Lemma 5.1a** (linear form; `LEMMA_Q5 §Q5.i` identity **(A)**, which the paper
compresses into Lemma 5.1's `m = 1` case). For `(n, q) = 1`,
`Σ*_{χ mod q} χ(n) = Σ_{f | q, n ≡ 1 (mod f)} μ(q/f)·φ(f)`.

Transcribed as a *derived* corollary, not an axiom: it is (B) at `m = 1`,
but it is separately consumed by ledger rows 2 and 9 (`E6_ENUMERATION.md:161,168`) and it is
what paper §5's "and ≤ Q·τ(n−1) for the linear sums" rests on.
Anchor: `RAMANUJAN_NOTE §4`, "identity (A) exact in 26/26 spot checks".

Paper §5 (452). Derivation: `LEMMA_Q5` §Q5.i identity (A).
Depends on: `lemma5_1`.
Rule 17: `(n, q) = 1` and `NeZero q` only. λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_1_linear {q : ℕ} [NeZero q] (n : ℕ) (hn : Nat.Coprime n q) :
    primLinSum q n
      = ∑ f ∈ divisorsCongOne q n,
          ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) * (Nat.totient f : ℂ) := by
  have hnm : Nat.Coprime (n * 1) q := by simpa using hn
  have hpair : primPairSum q n 1 = primLinSum q n := by
    rw [primPairSum, primLinSum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Nat.cast_one, map_one, map_one, mul_one]
  have hset : divisorsCong q n 1 = divisorsCongOne q n := by
    letI := Classical.decPred (fun f : ℕ => (n : ZMod f) = ((1 : ℕ) : ZMod f))
    letI := Classical.decPred (fun f : ℕ => (n : ZMod f) = 1)
    ext f
    have e1 : f ∈ divisorsCong q n 1
        ↔ f ∈ q.divisors ∧ ((n : ZMod f) = ((1 : ℕ) : ZMod f)) := Finset.mem_filter
    have e2 : f ∈ divisorsCongOne q n
        ↔ f ∈ q.divisors ∧ ((n : ZMod f) = 1) := Finset.mem_filter
    rw [e1, e2, Nat.cast_one]
  rw [← hpair, lemma5_1 (q := q) n 1 hnm, hset]

/-- **Lemma 5.1′** — Lemma 5.1 at the congruence `−n ≡ m (mod f)`: for `(nm, q) = 1`,
`Σ*_χ χ(−1)χ(n)χ̄(m) = Σ_{f | q, f | (n+m)} μ(q/f)·φ(f)`. Paper §5, first clause of the
5.2′/5.3′ paragraph; stated separately because Lemma 5.2′ is its aggregation.

Derivation (two lines, from 5.1): `χ(−1)χ(n) = χ(−n)`, so 5.1 applies at the pair
`(−n mod q, m)`, and `−n ≡ m (mod f) ⟺ f | (n + m)`.

⚠️ **FLAG.** `LEMMA_Q5.md` contains **no `n + m`
material whatsoever**, and there is **no numerical anchor** for the `n + m` branch: the 9/9
integer-exact anchor of `q5_check.py` tests the `n − m` identity only. 5.1′/5.2′/5.3′ exist
only in paper §5's five sentences; they postdate the note. Recommended (receipt obligation,
not a Lean one): add an `n + m` branch to `q5_check.py`.

Paper §5. Derivation: **none in the notes** — see the FLAG.
Depends on: `lemma5_1`.
Rule 17: `(nm, q) = 1` and `NeZero q` only. **`n + m ≤ Q` is deliberately absent** — that is
where Corollary 3 applies this, not a hypothesis of it (header). -/
theorem lemma5_1' {q : ℕ} [NeZero q] (n m : ℕ) (hnm : Nat.Coprime (n * m) q) :
    primPairSumNeg q n m
      = ∑ f ∈ divisorsCongNeg q n m,
          ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) * (Nat.totient f : ℂ) := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  -- `n' ≡ −n (mod q)`, a natural-number representative of `−n`
  set n' : ℕ := (q - 1) * n with hn'def
  have hcastq : ((q - 1 : ℕ) : ZMod q) = -1 := by
    have hsub : ((q - 1 : ℕ) : ZMod q) = ((q : ℕ) : ZMod q) - ((1 : ℕ) : ZMod q) :=
      Nat.cast_sub hq
    rw [hsub, ZMod.natCast_self, Nat.cast_one]
    ring
  have hn'cast : ((n' : ℕ) : ZMod q) = -((n : ℕ) : ZMod q) := by
    rw [hn'def, Nat.cast_mul, hcastq]
    ring
  -- coprimality is a statement about the residue, and `−x` is a unit iff `x` is
  have hcop : Nat.Coprime (n' * m) q := by
    rw [← ZMod.isUnit_iff_coprime]
    have hmul : ((n' * m : ℕ) : ZMod q) = -(((n * m : ℕ)) : ZMod q) := by
      have h1 : ((n' * m : ℕ) : ZMod q) = ((n' : ℕ) : ZMod q) * ((m : ℕ) : ZMod q) :=
        Nat.cast_mul _ _
      have h2 : ((n * m : ℕ) : ZMod q) = ((n : ℕ) : ZMod q) * ((m : ℕ) : ZMod q) :=
        Nat.cast_mul _ _
      rw [h1, h2, hn'cast]
      ring
    rw [hmul]
    exact ((ZMod.isUnit_iff_coprime (n * m) q).mpr hnm).neg
  -- `χ(−1)χ(n) = χ(n′)`
  have hchar : primPairSumNeg q n m = primPairSum q n' m := by
    rw [primPairSumNeg, primPairSum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [hn'cast, show -((n : ℕ) : ZMod q) = (-1 : ZMod q) * ((n : ℕ) : ZMod q) by ring, map_mul]
    ring
  -- `n′ ≡ m (mod f)` is `f ∣ (n + m)` for every `f ∣ q`
  have hsets : divisorsCong q n' m = divisorsCongNeg q n m := by
    letI := Classical.decPred (fun f : ℕ => ((n' : ℕ) : ZMod f) = ((m : ℕ) : ZMod f))
    letI := Classical.decPred (fun f : ℕ => ((n + m : ℕ) : ZMod f) = 0)
    ext f
    have e1 : f ∈ divisorsCong q n' m
        ↔ f ∈ q.divisors ∧ (((n' : ℕ)) : ZMod f) = ((m : ℕ) : ZMod f) := Finset.mem_filter
    have e2 : f ∈ divisorsCongNeg q n m
        ↔ f ∈ q.divisors ∧ (((n + m : ℕ)) : ZMod f) = 0 := Finset.mem_filter
    rw [e1, e2]
    constructor
    · rintro ⟨hf, hc⟩
      refine ⟨hf, ?_⟩
      rw [cong_neg_iff_dvd_add, ← Int.natCast_dvd_natCast]
      rw [cong_iff_dvd_sub] at hc
      have hfq : (f : ℤ) ∣ (q : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_divisors hf)
      have hqn : (f : ℤ) ∣ (q : ℤ) * (n : ℤ) := hfq.mul_right _
      have hn'Z : ((n' : ℕ) : ℤ) = ((q : ℤ) - 1) * (n : ℤ) := by
        rw [hn'def, Nat.cast_mul, Nat.cast_sub hq, Nat.cast_one]
      rw [hn'Z] at hc
      have h2 : (f : ℤ) ∣ (q : ℤ) * (n : ℤ) - (((q : ℤ) - 1) * (n : ℤ) - (m : ℤ)) :=
        dvd_sub hqn hc
      have heq : (q : ℤ) * (n : ℤ) - (((q : ℤ) - 1) * (n : ℤ) - (m : ℤ))
          = ((n + m : ℕ) : ℤ) := by push_cast; ring
      rwa [heq] at h2
    · rintro ⟨hf, hc⟩
      refine ⟨hf, ?_⟩
      rw [cong_neg_iff_dvd_add, ← Int.natCast_dvd_natCast] at hc
      rw [cong_iff_dvd_sub]
      have hfq : (f : ℤ) ∣ (q : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_divisors hf)
      have hqn : (f : ℤ) ∣ (q : ℤ) * (n : ℤ) := hfq.mul_right _
      have hn'Z : ((n' : ℕ) : ℤ) = ((q : ℤ) - 1) * (n : ℤ) := by
        rw [hn'def, Nat.cast_mul, Nat.cast_sub hq, Nat.cast_one]
      have h2 : (f : ℤ) ∣ (q : ℤ) * (n : ℤ) - ((n + m : ℕ) : ℤ) := dvd_sub hqn hc
      have heq : (q : ℤ) * (n : ℤ) - ((n + m : ℕ) : ℤ)
          = ((q : ℤ) - 1) * (n : ℤ) - (m : ℤ) := by push_cast; ring
      rw [hn'Z]
      rwa [heq] at h2
  rw [hchar, lemma5_1 (q := q) n' m hcop, hsets]

/-- **Anchor of `LEMMA_Q5 §Q5.i`.** `n ≡ 1 (mod q)` in identity (A) recovers
`φ*(q) = Σ_{f | q} μ(q/f)·φ(f)` (which vanishes for `q ≡ 2 mod 4`). Free once
`lemma5_1_linear` is in. `phiStar` is the frozen `Defs.phiStar`.

Paper §5. Derivation: `LEMMA_Q5` §Q5.i, sanity anchors.
Depends on: `lemma5_1_linear`.
Rule 17: `NeZero q` only. λ-free, X-free, T-free, D₀-free.

The *asymptotic* `Σ_{q≤x} φ*(q) = (18/π⁴)x² + O(x log x)` is **not** stated here: it is a
§12.2 obligation, owned by `ZetaQ/Normalisation.lean`. -/
theorem phiStar_eq_moebius_sum (q : ℕ) [NeZero q] :
    (phiStar q : ℤ)
      = ∑ f ∈ q.divisors, ArithmeticFunction.moebius (q / f) * (Nat.totient f : ℤ) := by
  have h := lemma5_1_linear (q := q) 1 (Nat.coprime_one_left q)
  have hlin : primLinSum q 1 = (phiStar q : ℂ) := by
    have hone : ∀ χ ∈ primitiveChars q, χ (((1 : ℕ)) : ZMod q) = (1 : ℂ) := by
      intro χ _
      rw [Nat.cast_one, map_one]
    rw [primLinSum, Finset.sum_congr rfl hone, Finset.sum_const, phiStar]
    simp
  have hset : divisorsCongOne q 1 = q.divisors := by
    letI := Classical.decPred (fun f : ℕ => (((1 : ℕ)) : ZMod f) = 1)
    ext f
    have e : f ∈ divisorsCongOne q 1 ↔ f ∈ q.divisors ∧ (((1 : ℕ)) : ZMod f) = 1 :=
      Finset.mem_filter
    rw [e]
    simp
  rw [hlin, hset] at h
  have hZ : ((phiStar q : ℤ) : ℂ)
      = ((∑ f ∈ q.divisors,
          ArithmeticFunction.moebius (q / f) * (Nat.totient f : ℤ) : ℤ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast hZ

/-! ## 2. Lemma 5.2 — the aggregated identity, exact, and its crude consequences -/

/-- **Sublemma.** `|M_k(N)| ≤ N`, from `|μ(r)| ≤ 1`. This is the "trivially" of
`LEMMA_Q5 §Q5.ii`'s crude-bound chain, and the reason the whole of §5 is **PNT-free**:
`M(y) = o(y)` would sharpen the constant only.

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii, "Crude bound".
Depends on: `mertensCoprime`.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem abs_mertensCoprime_le (k N : ℕ) :
    |((mertensCoprime k N : ℤ) : ℝ)| ≤ (N : ℝ) := by
  letI := Classical.decPred (fun r : ℕ => Nat.Coprime r k)
  have hz : |mertensCoprime k N| ≤ (N : ℤ) := by
    have h1 : |mertensCoprime k N|
        ≤ ∑ r ∈ (Finset.Icc 1 N).filter (fun r => Nat.Coprime r k),
            |ArithmeticFunction.moebius r| := by
      rw [mertensCoprime]
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ r ∈ (Finset.Icc 1 N).filter (fun r => Nat.Coprime r k),
        |ArithmeticFunction.moebius r|
        ≤ ∑ _r ∈ (Finset.Icc 1 N).filter (fun r => Nat.Coprime r k), (1 : ℤ) :=
      Finset.sum_le_sum (fun r _ => ArithmeticFunction.abs_moebius_le_one)
    have h3 : ∑ _r ∈ (Finset.Icc 1 N).filter (fun r => Nat.Coprime r k), (1 : ℤ)
        ≤ (N : ℤ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have := Finset.card_filter_le (Finset.Icc 1 N) (fun r => Nat.Coprime r k)
      have h4 : (Finset.Icc 1 N).card = N := by simp
      omega
    linarith
  calc |((mertensCoprime k N : ℤ) : ℝ)| = ((|mertensCoprime k N| : ℤ) : ℝ) := by
        rw [Int.cast_abs]
    _ ≤ (N : ℝ) := by exact_mod_cast hz

/-- **Sublemma.** `Σ_{f | k} φ(f)/f ≤ τ(k)` — the second step of the crude-bound chain
(`φ(f) ≤ f` termwise, `τ(k)` terms).

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii, "Crude bound".
Depends on: `tau`.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem sum_totient_div_le_tau (k : ℕ) :
    ∑ f ∈ k.divisors, (Nat.totient f : ℝ) / (f : ℝ) ≤ (tau k : ℝ) := by
  have h : ∑ f ∈ k.divisors, (Nat.totient f : ℝ) / (f : ℝ)
      ≤ ∑ _f ∈ k.divisors, (1 : ℝ) := by
    refine Finset.sum_le_sum (fun f hf => ?_)
    have hf0 : 0 < f := Nat.pos_of_mem_divisors hf
    rw [div_le_one (by exact_mod_cast hf0)]
    exact_mod_cast Nat.totient_le f
  simpa [tau] using h

/-- Membership in `aggDivisors`, with the frozen `Classical.decPred` instance discharged once. -/
theorem mem_aggDivisors {Q k j f : ℕ} :
    f ∈ aggDivisors Q k j ↔ f ∈ k.divisors ∧ (f ≤ Q ∧ Nat.Coprime f j) := by
  letI := Classical.decPred (fun f : ℕ => f ≤ Q ∧ Nat.Coprime f j)
  exact Finset.mem_filter

/-- **The `q = f·r` reindex, done once.** The shared engine of Lemmas 5.2, 5.2-linear and 5.2′:
given a per-modulus quantity `P` that vanishes off `(j, q) = 1` and equals
`Σ_{f | q, f | k} μ(q/f)φ(f)` on it, the aggregate over `q ≤ Q` is
`Σ_{f | k, f ≤ Q, (f,j) = 1} φ(f)·M_j(Q/f)`.

The bijection is `(q, f) ↦ (f, q/f)` between `{(q,f) : q ≤ Q, (j,q) = 1, f | q, f | k}` and
`{(f,r) : f | k, f ≤ Q, (f,j) = 1, r ≤ Q/f, (r,j) = 1}` — the "fiddly step"
`(q, j) = 1 ↔ (f, j) = 1 ∧ (r, j) = 1` for `q = f·r` of the ledger note.

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: `aggDivisors`, `mertensCoprime`.
Rule 17: `k ≠ 0` only (else `Nat.divisors 0 = ∅`); nothing relates `Q` to `k` or `j`. -/
theorem agg_reindex (Q j k : ℕ) (hk : k ≠ 0) (P : ℕ → ℂ)
    (hzero : ∀ q, 1 ≤ q → ¬ Nat.Coprime j q → P q = 0)
    (hid : ∀ q, 1 ≤ q → Nat.Coprime j q →
        P q = ∑ f ∈ q.divisors.filter (fun f => f ∣ k),
                ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) * (Nat.totient f : ℂ)) :
    ∑ q ∈ Finset.Icc 1 Q, P q
      = ∑ f ∈ aggDivisors Q k j,
          (Nat.totient f : ℂ) * ((mertensCoprime j (Q / f) : ℤ) : ℂ) := by
  classical
  letI dcop := Classical.decPred (fun r : ℕ => Nat.Coprime r j)
  -- restrict to the coprime moduli
  have hres : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.Coprime j q), P q
      = ∑ q ∈ Finset.Icc 1 Q, P q := by
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun q hq hnq => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    exact hzero q hq1 (fun hc => hnq (Finset.mem_filter.mpr ⟨hq, hc⟩))
  rw [← hres]
  have hexp : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.Coprime j q), P q
      = ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.Coprime j q),
          ∑ f ∈ q.divisors.filter (fun f => f ∣ k),
            ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) * (Nat.totient f : ℂ) := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    obtain ⟨hqI, hqc⟩ := Finset.mem_filter.mp hq
    exact hid q (Finset.mem_Icc.mp hqI).1 hqc
  have hrhs : ∑ f ∈ aggDivisors Q k j,
        (Nat.totient f : ℂ) * ((mertensCoprime j (Q / f) : ℤ) : ℂ)
      = ∑ f ∈ aggDivisors Q k j,
          ∑ r ∈ (Finset.Icc 1 (Q / f)).filter (fun r => Nat.Coprime r j),
            (Nat.totient f : ℂ) * ((ArithmeticFunction.moebius r : ℤ) : ℂ) := by
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [mertensCoprime, Int.cast_sum, Finset.mul_sum]
  rw [hexp, hrhs,
    Finset.sum_sigma' ((Finset.Icc 1 Q).filter (fun q => Nat.Coprime j q))
      (fun q => q.divisors.filter (fun f => f ∣ k))
      (fun q f => ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) * (Nat.totient f : ℂ)),
    Finset.sum_sigma' (aggDivisors Q k j)
      (fun f => (Finset.Icc 1 (Q / f)).filter (fun r => Nat.Coprime r j))
      (fun f r => (Nat.totient f : ℂ) * ((ArithmeticFunction.moebius r : ℤ) : ℂ))]
  refine Finset.sum_nbij' (fun x => (⟨x.2, x.1 / x.2⟩ : (_ : ℕ) × ℕ))
    (fun y => (⟨y.1 * y.2, y.1⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, f⟩ hx
    simp only [Finset.mem_sigma] at hx
    obtain ⟨hq, hf⟩ := hx
    obtain ⟨hqI, hqc⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hqI
    obtain ⟨hfdiv, hfk⟩ := Finset.mem_filter.mp hf
    have hfq : f ∣ q := (Nat.mem_divisors.mp hfdiv).1
    have hf0 : 0 < f := Nat.pos_of_dvd_of_pos hfq (by omega)
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [mem_aggDivisors]
      refine ⟨Nat.mem_divisors.mpr ⟨hfk, hk⟩, ?_, ?_⟩
      · exact le_trans (Nat.le_of_dvd (by omega) hfq) hqQ
      · exact (Nat.Coprime.coprime_dvd_right hfq hqc).symm
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · exact (Nat.one_le_div_iff hf0).mpr (Nat.le_of_dvd hq1 hfq)
      · exact Nat.div_le_div_right hqQ
      · exact (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hfq) hqc).symm
  · rintro ⟨f, r⟩ hy
    simp only [Finset.mem_sigma] at hy
    obtain ⟨hf, hr⟩ := hy
    obtain ⟨hfk, hfQ, hfc⟩ := mem_aggDivisors.mp hf
    obtain ⟨hrI, hrc⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1, hrQ⟩ := Finset.mem_Icc.mp hrI
    have hf0 : 0 < f := Nat.pos_of_mem_divisors hfk
    have hfrQ : f * r ≤ Q := by
      have h := (Nat.le_div_iff_mul_le hf0).mp hrQ
      rwa [Nat.mul_comm] at h
    have hfr0 : 0 < f * r := Nat.mul_pos hf0 (by omega)
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hfr0, hfrQ⟩, ?_⟩, ?_⟩
    · exact Nat.Coprime.mul_right hfc.symm hrc.symm
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right f r, hfr0.ne'⟩,
        (Nat.mem_divisors.mp hfk).1⟩
  · rintro ⟨q, f⟩ hx
    simp only [Finset.mem_sigma] at hx
    have hfq : f ∣ q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hx.2).1).1
    show (⟨f * (q / f), f⟩ : (_ : ℕ) × ℕ) = ⟨q, f⟩
    rw [Nat.mul_div_cancel' hfq]
  · rintro ⟨f, r⟩ hy
    simp only [Finset.mem_sigma] at hy
    have hf0 : 0 < f := Nat.pos_of_mem_divisors (mem_aggDivisors.mp hy.1).1
    show (⟨f, f * r / f⟩ : (_ : ℕ) × ℕ) = ⟨f, r⟩
    rw [Nat.mul_div_cancel_left r hf0]
  · rintro ⟨q, f⟩ _
    exact mul_comm _ _

/-- The `n − m` index set in the `f ∣ k` form `agg_reindex` consumes (this
time bridging the congruence spelling to a *natural-number* divisibility). -/
theorem divisorsCong_eq_filter_dvd (q n m : ℕ) :
    divisorsCong q n m = q.divisors.filter (fun f => f ∣ ((n : ℤ) - (m : ℤ)).natAbs) := by
  letI := Classical.decPred (fun f : ℕ => (n : ZMod f) = (m : ZMod f))
  ext f
  have h1 : f ∈ divisorsCong q n m ↔ f ∈ q.divisors ∧ ((n : ZMod f) = (m : ZMod f)) :=
    Finset.mem_filter
  have hbridge : (f ∣ ((n : ℤ) - (m : ℤ)).natAbs) ↔ ((f : ℤ) ∣ ((n : ℤ) - (m : ℤ))) := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  rw [h1, Finset.mem_filter, cong_iff_dvd_sub, hbridge]

/-- The `n + m` index set in the `f ∣ k` form `agg_reindex` consumes. -/
theorem divisorsCongNeg_eq_filter_dvd (q n m : ℕ) :
    divisorsCongNeg q n m = q.divisors.filter (fun f => f ∣ (n + m)) := by
  letI := Classical.decPred (fun f : ℕ => ((n + m : ℕ) : ZMod f) = 0)
  ext f
  have h1 : f ∈ divisorsCongNeg q n m ↔ f ∈ q.divisors ∧ (((n + m : ℕ)) : ZMod f) = 0 :=
    Finset.mem_filter
  rw [h1, Finset.mem_filter, cong_neg_iff_dvd_add]

/-- A Dirichlet character vanishes off coprimality — the "*said, not assumed*" clause of
`LEMMA_Q5 §Q5.ii` (discharging `RAMANUJAN_NOTE §5` item 3). -/
theorem char_apply_eq_zero_of_not_coprime {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ℕ) (ha : ¬ Nat.Coprime a q) : χ (a : ZMod q) = 0 :=
  χ.map_nonunit (fun hu => ha ((ZMod.isUnit_iff_coprime a q).mp hu))

/-- Moduli with `(q, nm) > 1` contribute nothing to the family pair sum. -/
theorem primPairSum_eq_zero {q : ℕ} [NeZero q] (n m : ℕ)
    (h : ¬ Nat.Coprime (n * m) q) : primPairSum q n m = 0 := by
  rw [primPairSum]
  refine Finset.sum_eq_zero (fun χ _ => ?_)
  by_cases hn : Nat.Coprime n q
  · have hm : ¬ Nat.Coprime m q := fun hm => h (Nat.Coprime.mul_left hn hm)
    rw [char_apply_eq_zero_of_not_coprime χ m hm, map_zero, mul_zero]
  · rw [char_apply_eq_zero_of_not_coprime χ n hn, zero_mul]

/-- Moduli with `(q, nm) > 1` contribute nothing to the parity-twisted family sum. -/
theorem primPairSumNeg_eq_zero {q : ℕ} [NeZero q] (n m : ℕ)
    (h : ¬ Nat.Coprime (n * m) q) : primPairSumNeg q n m = 0 := by
  rw [primPairSumNeg]
  refine Finset.sum_eq_zero (fun χ _ => ?_)
  by_cases hn : Nat.Coprime n q
  · have hm : ¬ Nat.Coprime m q := fun hm => h (Nat.Coprime.mul_left hn hm)
    rw [char_apply_eq_zero_of_not_coprime χ m hm, map_zero, mul_zero, mul_zero]
  · rw [char_apply_eq_zero_of_not_coprime χ n hn, zero_mul, mul_zero]

/-- **Lemma 5.2** (aggregated, exact). For `n ≠ m`,
`Σ_{q≤Q} Σ*_χ χ(n)χ̄(m) = Σ_{f | (n−m), f ≤ Q, (f, nm) = 1} φ(f)·M_{nm}(Q/f)`,
with `M_{nm}` the coprimality-restricted Mertens function.

An **EXACT** identity: no error term, no PNT. Moduli with `(q, nm) > 1` contribute zero
because χ vanishes off coprimality — *said, not assumed* (`LEMMA_Q5 §Q5.ii`, discharging
`RAMANUJAN_NOTE §5` item 3), so no coprimality hypothesis appears in the signature.
`q = 1` contributes the trivial character's `1`, matching `f = r = 1`. The proof reindexes
`q = f·r` over the surviving moduli.
Anchor (1): verified to **integer precision at Q = 60 in 9/9 pairs**, including prime
powers, equal-parity pairs, and `(2, 32)` shared-factor exclusions (`log_q5.txt`).

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: `lemma5_1`, `mertensCoprime`, `aggDivisors`.
Rule 17: the ONLY hypothesis is the paper's own `n ≠ m` (needed so that
`((n:ℤ)−m).natAbs ≠ 0`, else `Nat.divisors 0 = ∅`). **No hypothesis relates `Q` to `n` or
`m`** — Lemma 5.2 is uniform over `q ≤ Q` and holds whether or not `n, m ≤ Q`; that
uniformity is exactly what Rule 17 protects. λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_2 (Q n m : ℕ) (hne : n ≠ m) :
    famPairSum Q n m
      = ∑ f ∈ aggDivisors Q ((n : ℤ) - (m : ℤ)).natAbs (n * m),
          (Nat.totient f : ℂ) * ((mertensCoprime (n * m) (Q / f) : ℤ) : ℂ) := by
  have hk : ((n : ℤ) - (m : ℤ)).natAbs ≠ 0 := by
    simp only [ne_eq, Int.natAbs_eq_zero, sub_eq_zero, Nat.cast_inj]
    exact hne
  rw [famPairSum]
  refine agg_reindex Q (n * m) _ hk (fun q => primPairSum q n m) ?_ ?_
  · intro q hq1 hnc
    haveI : NeZero q := ⟨by omega⟩
    exact primPairSum_eq_zero n m hnc
  · intro q hq1 hc
    haveI : NeZero q := ⟨by omega⟩
    rw [lemma5_1 n m hc, divisorsCong_eq_filter_dvd]

/-- **Lemma 5.2, linear form** — the aggregation of identity (A):
`Σ_{q≤Q} Σ*_χ χ(n) = Σ_{f | (n−1), f ≤ Q, (f, n) = 1} φ(f)·M_n(Q/f)`.
The exact identity underlying paper §5's "and ≤ Q·τ(n−1) for the linear sums"; ledger
rows 2 and 9 (`E6_ENUMERATION.md:161,168`).

Paper §5. Derivation: `LEMMA_Q5` §Q5.i (A) + §Q5.ii.
Depends on: `lemma5_1_linear`, `mertensCoprime`.
Rule 17: `2 ≤ n` only — see `lemma5_2_crude_linear` for why (the `n = 1` failure is on the
RHS, `Nat.divisors 0 = ∅`). λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_2_linear (Q n : ℕ) (hn : 2 ≤ n) :
    famLinSum Q n
      = ∑ f ∈ aggDivisors Q (n - 1) n,
          (Nat.totient f : ℂ) * ((mertensCoprime n (Q / f) : ℤ) : ℂ) := by
  have hne : n ≠ 1 := by omega
  have hfam : famLinSum Q n = famPairSum Q n 1 := by
    rw [famLinSum, famPairSum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [primLinSum, primPairSum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Nat.cast_one, map_one, map_one, mul_one]
  have hk : ((n : ℤ) - ((1 : ℕ) : ℤ)).natAbs = n - 1 := by push_cast; omega
  have hj : n * 1 = n := mul_one n
  rw [hfam, lemma5_2 Q n 1 hne, hk, hj]

/-- **Fill-local helper** for the three crude bounds below: the `LEMMA_Q5 §Q5.ii` chain
`|Σ_{f ∈ aggDivisors Q k j} φ(f)·M_j(Q/f)| ≤ Σ φ(f)·(Q/f) ≤ Q·Σ_{f|k} φ(f)/f ≤ Q·τ(k)`,
run once at the level of the right-hand side shared by Lemmas 5.2, 5.2-linear and 5.2′. -/
private theorem agg_norm_bound (Q k j : ℕ) :
    ‖∑ f ∈ aggDivisors Q k j, (Nat.totient f : ℂ) * ((mertensCoprime j (Q / f) : ℤ) : ℂ)‖
      ≤ (Q : ℝ) * (tau k : ℝ) := by
  have hsub : aggDivisors Q k j ⊆ k.divisors := by
    letI := Classical.decPred (fun f : ℕ => f ≤ Q ∧ Nat.Coprime f j)
    exact Finset.filter_subset _ _
  have step1 : ‖∑ f ∈ aggDivisors Q k j,
        (Nat.totient f : ℂ) * ((mertensCoprime j (Q / f) : ℤ) : ℂ)‖
      ≤ ∑ f ∈ aggDivisors Q k j, (Q : ℝ) * ((Nat.totient f : ℝ) / (f : ℝ)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun f hf => ?_))
    have hfd : f ∈ k.divisors := hsub hf
    have hf0 : 0 < f := Nat.pos_of_mem_divisors hfd
    rw [norm_mul]
    have h1 : ‖(Nat.totient f : ℂ)‖ = (Nat.totient f : ℝ) := by simp
    have h2 : ‖((mertensCoprime j (Q / f) : ℤ) : ℂ)‖
        = |((mertensCoprime j (Q / f) : ℤ) : ℝ)| := by
      rw [show ((mertensCoprime j (Q / f) : ℤ) : ℂ)
            = (((mertensCoprime j (Q / f) : ℤ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [h1, h2]
    have h6 : |((mertensCoprime j (Q / f) : ℤ) : ℝ)| ≤ (Q : ℝ) / (f : ℝ) :=
      (abs_mertensCoprime_le j (Q / f)).trans Nat.cast_div_le
    have h5 : (0 : ℝ) ≤ (Nat.totient f : ℝ) := by positivity
    calc (Nat.totient f : ℝ) * |((mertensCoprime j (Q / f) : ℤ) : ℝ)|
        ≤ (Nat.totient f : ℝ) * ((Q : ℝ) / (f : ℝ)) := mul_le_mul_of_nonneg_left h6 h5
      _ = (Q : ℝ) * ((Nat.totient f : ℝ) / (f : ℝ)) := by ring
  refine step1.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg Q)
  refine le_trans ?_ (sum_totient_div_le_tau k)
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => ?_)
  positivity

/-- **Lemma 5.2, crude consequence** — *the in-zone workhorse*:
`|Σ_{q≤Q} Σ*_χ χ(n)χ̄(m)| ≤ Q·τ(|n−m|)`.

The paper's "two-line consequence"; `LEMMA_Q5 §Q5.ii` gives the chain in full:
`|M| ≤ y` trivially, so `|·| ≤ Σ_{f|(n−m), f≤Q} φ(f)(Q/f) ≤ Q Σ_{f|(n−m)} φ(f)/f ≤ Q·τ(|n−m|)`.
**No PNT is used.**

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii, "Crude bound".
Depends on: `lemma5_2`, `abs_mertensCoprime_le`, `sum_totient_div_le_tau`.
Rule 17: `n ≠ m` only. λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_2_crude (Q n m : ℕ) (hne : n ≠ m) :
    ‖famPairSum Q n m‖ ≤ (Q : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := by
  rw [lemma5_2 Q n m hne]
  exact agg_norm_bound Q _ _

/-- **Lemma 5.2, crude consequence, linear form**: `|Σ_{q≤Q} Σ*_χ χ(n)| ≤ Q·τ(n−1)`.

⚠️ **The paper's statement is compressed and is FALSE at `n = 1`**:
at `n = 1` the RHS is `Q·τ(0) = 0` in Lean (`Nat.divisors 0 = ∅`) while the LHS is
`Σ_{q≤Q} φ*(q) > 0`. `RAMANUJAN_NOTE §2` states the correct range, "for n ≥ 2". **`2 ≤ n` is
restored in this signature.** It is harmless in application: paper §4 records that
"Λ(1) = 0 forces n, m ≥ 2", so every pair reaching this bound already has `n ≥ 2`.
(Recommended four-word paper edit: add "for n ≥ 2" to §5.)

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii; range from RAMANUJAN_NOTE §2.
Depends on: `lemma5_2_linear`, `abs_mertensCoprime_le`, `sum_totient_div_le_tau`.
Rule 17: `2 ≤ n` only — a *restored* range condition on the summation index, not an
analytic cap. λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_2_crude_linear (Q n : ℕ) (hn : 2 ≤ n) :
    ‖famLinSum Q n‖ ≤ (Q : ℝ) * (tau (n - 1) : ℝ) := by
  rw [lemma5_2_linear Q n hn]
  exact agg_norm_bound Q _ _

/-- **Fill-local helper**: `Icc 1 N = Ioc 0 N` in `ℕ`, the form the dyadic differencing wants. -/
private theorem Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- **Fill-local helper**: differencing the `q ≤ Q` and `q ≤ Q/2` families onto the dyadic
block `Q/2 < q ≤ Q` (`LEMMA_Q5 §Q5.ii`, "Dyadic family by differencing"). -/
private theorem dyadic_sub (Q : ℕ) (g : ℕ → ℂ) :
    ∑ q ∈ Finset.Ioc (Q / 2) Q, g q
      = (∑ q ∈ Finset.Icc 1 Q, g q) - ∑ q ∈ Finset.Icc 1 (Q / 2), g q := by
  have hcons := Finset.sum_Ioc_consecutive g (Nat.zero_le (Q / 2)) (Nat.div_le_self Q 2)
  rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero, ← hcons]
  ring

/-- **Fill-local helper**: the `3/2` of the dyadic crude bounds, i.e. `Q + ⌊Q/2⌋ ≤ (3/2)Q`
against a nonnegative weight. -/
private theorem dyadic_three_halves (Q : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (Q : ℝ) * t + ((Q / 2 : ℕ) : ℝ) * t ≤ (3 / 2 : ℝ) * (Q : ℝ) * t := by
  have hhalf : ((Q / 2 : ℕ) : ℝ) ≤ (Q : ℝ) / 2 := Nat.cast_div_le
  nlinarith

/-- **Lemma 5.2, dyadic crude bound**: `|Σ_{Q/2<q≤Q} Σ*_χ χ(n)χ̄(m)| ≤ (3/2)·Q·τ(|n−m|)`.

**Not stated in the paper** — supplied by `LEMMA_Q5 §Q5.ii` ("Dyadic family by
differencing"), and needed by Corollary 2 (`C = 2π⁴/27`). The `3/2` is `1 + 1/2`, from
differencing the `q ≤ Q` and `q ≤ Q/2` bounds.

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: `lemma5_2_crude`.
Rule 17: `n ≠ m` only; the dyadic range is a conductor restriction, not a bandwidth one. -/
theorem lemma5_2_crude_dyadic (Q n m : ℕ) (hne : n ≠ m) :
    ‖famPairSumDyadic Q n m‖
      ≤ (3 / 2 : ℝ) * (Q : ℝ) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := by
  have hd : famPairSumDyadic Q n m = famPairSum Q n m - famPairSum (Q / 2) n m := by
    rw [famPairSumDyadic, famPairSum, famPairSum, dyadic_sub]
  rw [hd]
  have h1 := lemma5_2_crude Q n m hne
  have h2 := lemma5_2_crude (Q / 2) n m hne
  have ht : (0 : ℝ) ≤ (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) := Nat.cast_nonneg _
  refine (norm_sub_le _ _).trans ?_
  refine le_trans (by linarith) (dyadic_three_halves Q _ ht)

/-! ## 3. Lemma 5.2′ — the `n + m` variant -/

/-- **Lemma 5.2′** (aggregated, exact, `n + m` form): "the identical identity with the
divisor sum over `f | (n + m)`",
`Σ_{q≤Q} Σ*_χ χ(−1)χ(n)χ̄(m) = Σ_{f | (n+m), f ≤ Q, (f, nm) = 1} φ(f)·M_{nm}(Q/f)`.

**No excluded diagonal**: `n = m` is allowed (paper §5: "n = −m is impossible for positive
n, m"). This is the form Corollary 3's in-zone parity projection consumes (§1.1, §12.3).

⚠️ **FLAG.** No anchor exists for this identity — see `lemma5_1'`.

Paper §5. Derivation: **none in the notes**.
Depends on: `lemma5_1'`, `mertensCoprime`, `aggDivisors`.
Rule 17: hypotheses are `1 ≤ n`, `1 ≤ m` only, and only so that `n + m ≠ 0`
(`Nat.divisors 0 = ∅`). The paper's `n, m ≥ 2` is a remark about where it is applied (via
`Λ(1) = 0`); the **weaker** `1 ≤ ·` is stated, a deliberate and recorded weakening.

**`n + m ≤ Q` is deliberately ABSENT, and that is the important point:**
Corollary 3's "in-zone n + m ≤ 2Q^{1−δ′} ≪ Q" says where the identity is applied, and
smuggling it in would be (i) unfaithful and (ii) indistinguishable at Lean level from an
`X ≤ Q` bandwidth cap. λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_2' (Q n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    famPairSumNeg Q n m
      = ∑ f ∈ aggDivisors Q (n + m) (n * m),
          (Nat.totient f : ℂ) * ((mertensCoprime (n * m) (Q / f) : ℤ) : ℂ) := by
  have hk : n + m ≠ 0 := by omega
  rw [famPairSumNeg]
  refine agg_reindex Q (n * m) _ hk (fun q => primPairSumNeg q n m) ?_ ?_
  · intro q hq1 hnc
    haveI : NeZero q := ⟨by omega⟩
    exact primPairSumNeg_eq_zero n m hnc
  · intro q hq1 hc
    haveI : NeZero q := ⟨by omega⟩
    rw [lemma5_1' n m hc, divisorsCongNeg_eq_filter_dvd]

/-- **Lemma 5.2′, crude consequence**: `|Σ_{q≤Q} Σ*_χ χ(−1)χ(n)χ̄(m)| ≤ Q·τ(n+m)`.

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii, transported.
Depends on: `lemma5_2'`, `abs_mertensCoprime_le`, `sum_totient_div_le_tau`.
Rule 17: `1 ≤ n`, `1 ≤ m` only. **No `n + m ≤ Q`.** λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_2'_crude (Q n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖famPairSumNeg Q n m‖ ≤ (Q : ℝ) * (tau (n + m) : ℝ) := by
  rw [lemma5_2' Q n m hn hm]
  exact agg_norm_bound Q _ _

/-- **Lemma 5.2′, dyadic crude bound**: `|Σ_{Q/2<q≤Q} Σ*_χ χ(−1)χ(n)χ̄(m)| ≤ (3/2)Q·τ(n+m)`.
Corollary 3 is stated for the even primitive **dyadic** family, so it needs the dyadic
`n + m` bound as well as the `q ≤ Q` one.

Paper §1.1 / §5. Derivation: `LEMMA_Q5` §Q5.ii.
Depends on: `lemma5_2'_crude`.
Rule 17: `1 ≤ n`, `1 ≤ m` only. **No `n + m ≤ Q`.** -/
theorem lemma5_2'_crude_dyadic (Q n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖famPairSumNegDyadic Q n m‖ ≤ (3 / 2 : ℝ) * (Q : ℝ) * (tau (n + m) : ℝ) := by
  have hd : famPairSumNegDyadic Q n m = famPairSumNeg Q n m - famPairSumNeg (Q / 2) n m := by
    rw [famPairSumNegDyadic, famPairSumNeg, famPairSumNeg, dyadic_sub]
  rw [hd]
  have h1 := lemma5_2'_crude Q n m hn hm
  have h2 := lemma5_2'_crude (Q / 2) n m hn hm
  have ht : (0 : ℝ) ≤ (tau (n + m) : ℝ) := Nat.cast_nonneg _
  refine (norm_sub_le _ _).trans ?_
  refine le_trans (by linarith) (dyadic_three_halves Q _ ht)

/-! ## 4. Lemma 5.3 — the zone bound (divisor AVERAGE)

`LEMMA_Q5 §Q5.iii` gives the whole proof, which the paper compresses to the two words
"divisor average". It runs on four auxiliary summation facts; they are stated and proved here as their own
lemmas, since two of them are **not in Mathlib**.

**Explicitly NOT used:** any pointwise divisor bound `τ ≤ Y^ε`. `RAMANUJAN_NOTE §3`'s ε-route
is superseded by `§Q5.iii`: the pointwise `ε = c/log log Y` is not `o(δ′)` and would poison
the zone edge. No `Y^ε` occurs anywhere in this file. -/

/-- **Toolkit 1** (`Σ_{n ≤ N} n^{−1/2} ≤ 2√N`). Re-proved locally rather than imported:
`Zeta23.Cheb.sum_one_div_sqrt_le` (`Zeta23/Chebyshev.lean:332`) is the identical statement,
but §5 is Mathlib-only and fully independent, and this is the only [R] item §5
wants (recommendation (b) — ~25 lines).

Paper §5. Derivation: `LEMMA_Q5` §Q5.iii, the "≤ 2" step.
Depends on: Mathlib only.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem sum_one_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (1 : ℝ) / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    have hb2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have ha2 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hapos : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hbnn : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have key : (1 : ℝ) / Real.sqrt ((N : ℝ) + 1)
        ≤ 2 * Real.sqrt ((N : ℝ) + 1) - 2 * Real.sqrt (N : ℝ) := by
      rw [div_le_iff₀ hapos]
      nlinarith [sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ))]
    push_cast
    linarith

/-- **Fill-local helper**: `1/(x+1) ≤ log(x+1) − log x` for `x ≥ 1`, from
`log t ≤ t − 1` at `t = x/(x+1)`. The one step of the harmonic bound. -/
private theorem inv_succ_le_log_sub (x : ℝ) (hx : 1 ≤ x) :
    (1 : ℝ) / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have hxp : (0 : ℝ) < x := by linarith
  have hx1p : (0 : ℝ) < x + 1 := by linarith
  have hlog : Real.log (x / (x + 1)) ≤ x / (x + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hxp) (ne_of_gt hx1p)] at hlog
  have hval : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
  rw [hval] at hlog
  linarith

/-- **Fill-local helper** (harmonic tail): `Σ_{a < m ≤ b} 1/m ≤ log b − log a` for `1 ≤ a`,
by telescoping `inv_succ_le_log_sub`. Used by Toolkits 2, 3 and 5. -/
private theorem sum_inv_Ioc_le_log_sub (a : ℕ) (ha : 1 ≤ a) :
    ∀ b : ℕ, a ≤ b →
      ∑ m ∈ Finset.Ioc a b, (1 : ℝ) / (m : ℝ) ≤ Real.log (b : ℝ) - Real.log (a : ℝ) := by
  intro b
  induction b with
  | zero => intro h; omega
  | succ b ih =>
    intro h
    by_cases hab : a ≤ b
    · rw [Finset.sum_Ioc_succ_top hab]
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : 1 ≤ b)
      have hstep := inv_succ_le_log_sub (b : ℝ) hb1
      have h1 := ih hab
      push_cast
      linarith
    · have hae : a = b + 1 := by omega
      subst hae
      simp

/-- **Fill-local helper** (harmonic bound): `Σ_{1 ≤ d ≤ Y} 1/d ≤ 1 + log Y`. -/
private theorem sum_inv_Icc_le_one_add_log (Y : ℕ) (hY : 1 ≤ Y) :
    ∑ d ∈ Finset.Icc 1 Y, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (Y : ℝ) := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨le_refl 1, hY⟩
  have hset : Finset.Icc 1 Y = insert 1 (Finset.Ioc 1 Y) := by
    rw [← Finset.Icc_erase_left, Finset.insert_erase h1]
  rw [hset, Finset.sum_insert (by simp), Nat.cast_one, div_one]
  have htail := sum_inv_Ioc_le_log_sub 1 (le_refl 1) Y hY
  simp only [Nat.cast_one, Real.log_one, sub_zero] at htail
  linarith

/-- **Toolkit 2** (the Dirichlet divisor average, `Σ_{k ≤ Y} τ(k) ≤ Y(1 + log Y)`).

**NOT in Mathlib** — there are no divisor-summatory asymptotics in `Mathlib/NumberTheory/`.
Route: `Σ_{k≤Y} τ(k) = Σ_{d≤Y} ⌊Y/d⌋ ≤ Y·H_Y ≤ Y(1 + log Y)` (harmonic bound). The explicit
constant is stated rather than a `≪` so that the collection step of Lemma 5.3 can chain.

Paper §5. Derivation: `LEMMA_Q5` §Q5.iii, "Σ_{k≤Y}τ(k) ≪ Y log Y".
Depends on: Mathlib only.
Rule 17: `1 ≤ Y` only, a well-formedness condition. λ, X, T, D₀ absent. -/
theorem sum_tau_le (Y : ℕ) (hY : 1 ≤ Y) :
    ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) ≤ (Y : ℝ) * (1 + Real.log (Y : ℝ)) := by
  classical
  -- `τ(k) = #{d ≤ Y : d ∣ k}` for `k ≤ Y`
  have hcount : ∀ k ∈ Finset.Icc 1 Y,
      tau k = ((Finset.Icc 1 Y).filter (fun d => d ∣ k)).card := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    rw [tau]
    congr 1
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) hk2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  -- double counting: `Σ_k #{d ∣ k} = Σ_d #{k : d ∣ k} = Σ_d ⌊Y/d⌋`
  have hswap : ∑ k ∈ Finset.Icc 1 Y, ((Finset.Icc 1 Y).filter (fun d => d ∣ k)).card
      = ∑ d ∈ Finset.Icc 1 Y, ((Finset.Icc 1 Y).filter (fun k => d ∣ k)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hdiv : ∀ d : ℕ, ((Finset.Icc 1 Y).filter (fun k => d ∣ k)).card = Y / d := by
    intro d
    rw [Icc_one_eq_Ioc_zero]
    exact Nat.Ioc_filter_dvd_card_eq_div Y d
  have hnat : ∑ k ∈ Finset.Icc 1 Y, tau k = ∑ d ∈ Finset.Icc 1 Y, Y / d := by
    rw [Finset.sum_congr rfl hcount, hswap]
    exact Finset.sum_congr rfl (fun d _ => hdiv d)
  have hcast : ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ)
      = ((∑ k ∈ Finset.Icc 1 Y, tau k : ℕ) : ℝ) := by rw [Nat.cast_sum]
  rw [hcast, hnat, Nat.cast_sum]
  calc ∑ d ∈ Finset.Icc 1 Y, ((Y / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 Y, (Y : ℝ) / (d : ℝ) :=
        Finset.sum_le_sum (fun d _ => Nat.cast_div_le)
    _ = (Y : ℝ) * ∑ d ∈ Finset.Icc 1 Y, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d _ => by ring)
    _ ≤ (Y : ℝ) * (1 + Real.log (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_Icc_le_one_add_log Y hY) (Nat.cast_nonneg Y)

/-- **Fill-local helper**: `Σ_{1 ≤ j ≤ N} log j = log(N!)`. -/
private theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, Real.log (j : ℝ) = Real.log (Nat.factorial N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    ring

/-- **Fill-local helper**: `N·log N ≤ log(N!) + N`, i.e. the Stirling-free `N^N ≤ N!·e^N`.
Elementary: the inductive step is exactly `log(1 + 1/N) ≤ 1/N`, i.e. `log t ≤ t − 1`. -/
private theorem nat_mul_log_le_log_factorial (N : ℕ) :
    (N : ℝ) * Real.log (N : ℝ) ≤ Real.log (Nat.factorial N : ℝ) + (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
      have hfac : Real.log (Nat.factorial (N + 1) : ℝ)
          = Real.log ((N : ℝ) + 1) + Real.log (Nat.factorial N : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        rw [Real.log_mul (by positivity) (by positivity)]
      have hlog : Real.log (((N : ℝ) + 1) / (N : ℝ)) ≤ 1 / (N : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (x := ((N : ℝ) + 1) / (N : ℝ)) (by positivity)
        have heq : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by
          field_simp
          ring
        linarith [heq ▸ h]
      have hstep : (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) ≤ 1 := by
        rw [← Real.log_div (by positivity) (by positivity)]
        calc (N : ℝ) * Real.log (((N : ℝ) + 1) / (N : ℝ))
            ≤ (N : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = 1 := by field_simp
      push_cast
      rw [hfac]
      nlinarith [ih, hstep]

/-- **Fill-local helper**: `Σ_{1 ≤ j ≤ ⌊x⌋} log(x/j) ≤ x` for `x ≥ 0` — the summand is a
lower Riemann sum for `∫_0^x log(x/t) dt = x`, but no integral is used: this is
`N^N ≤ N!·e^N` plus `log t ≤ t − 1` at `t = x/N`. -/
private theorem sum_log_div_le (x : ℝ) (hx : 0 ≤ x) :
    ∑ j ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / (j : ℝ)) ≤ x := by
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with hN | hN
  · rw [hN, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    exact hx
  · set N : ℕ := ⌊x⌋₊ with hNdef
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hxN : (N : ℝ) ≤ x := Nat.floor_le hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hterm : ∀ j ∈ Finset.Icc 1 N,
        Real.log (x / (j : ℝ)) = Real.log x - Real.log (j : ℝ) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      exact Real.log_div (ne_of_gt hxpos) (ne_of_gt hjR)
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
      sum_log_eq_log_factorial N, Nat.card_Icc, nsmul_eq_mul]
    have hcard : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by simp
    rw [hcard]
    have hA := nat_mul_log_le_log_factorial N
    have hB : Real.log (x / (N : ℝ)) ≤ x / (N : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hB' : Real.log x - Real.log (N : ℝ) ≤ x / (N : ℝ) - 1 := by
      rwa [Real.log_div (ne_of_gt hxpos) (ne_of_gt hNpos)] at hB
    have hB2 : (N : ℝ) * (Real.log x - Real.log (N : ℝ)) ≤ x - (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hB' hNpos.le
      have heq : (N : ℝ) * (x / (N : ℝ) - 1) = x - (N : ℝ) := by field_simp
      linarith [heq ▸ h]
    nlinarith [hA, hB2]

/-- **Toolkit 3** (`Σ_{k ≤ Y} τ(k)·log(Y/k) ≤ Y(1 + log Y)`).

**NOT in Mathlib.** Route (`LEMMA_Q5 §Q5.iii`): `Σ_{k≤Y} τ(k)log(Y/k) = Σ_d Σ_{j≤Y/d}
log(Y/(dj)) ≤ Σ_d (Y/d) ≤ Y(1 + log Y)`, using `Σ_{j≤J} log(J/j) ≤ J` (Stirling-free: the
summand is a lower Riemann sum for `∫_0^J log(J/t) dt = J`).

Paper §5. Derivation: `LEMMA_Q5` §Q5.iii.
Depends on: Mathlib only.
Rule 17: `1 ≤ Y` only. λ, X, T, D₀ absent. -/
theorem sum_tau_mul_log_le (Y : ℕ) (hY : 1 ≤ Y) :
    ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) * Real.log ((Y : ℝ) / (k : ℝ))
      ≤ (Y : ℝ) * (1 + Real.log (Y : ℝ)) := by
  classical
  -- `τ(k) = #{d ≤ Y : d ∣ k}` for `k ≤ Y`, weighted by `log(Y/k)`
  have hcount : ∀ k ∈ Finset.Icc 1 Y,
      (tau k : ℝ) * Real.log ((Y : ℝ) / (k : ℝ))
        = ∑ d ∈ Finset.Icc 1 Y, (if d ∣ k then Real.log ((Y : ℝ) / (k : ℝ)) else 0) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hset : tau k = ((Finset.Icc 1 Y).filter (fun d => d ∣ k)).card := by
      rw [tau]
      congr 1
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hd) hk2⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, by omega⟩
    rw [hset, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hcount, Finset.sum_comm]
  -- for each `d ≤ Y` the inner sum is `Σ_{j ≤ Y/d} log((Y/d)/j) ≤ Y/d`
  have hinner : ∀ d ∈ Finset.Icc 1 Y,
      ∑ k ∈ Finset.Icc 1 Y, (if d ∣ k then Real.log ((Y : ℝ) / (k : ℝ)) else 0)
        ≤ (Y : ℝ) / (d : ℝ) := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    have hd0 : 0 < d := hd1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [← Finset.sum_filter]
    have hbij : ∑ k ∈ (Finset.Icc 1 Y).filter (fun k => d ∣ k), Real.log ((Y : ℝ) / (k : ℝ))
        = ∑ j ∈ Finset.Icc 1 (Y / d), Real.log (((Y : ℝ) / (d : ℝ)) / (j : ℝ)) := by
      refine (Finset.sum_nbij' (fun j => d * j) (fun k => k / d) ?_ ?_ ?_ ?_ ?_).symm
      · intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Dvd.intro j rfl⟩
        · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        · have h := (Nat.le_div_iff_mul_le hd0).mp hj2
          rwa [Nat.mul_comm] at h
      · intro k hk
        obtain ⟨hkI, hdk⟩ := Finset.mem_filter.mp hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hkI
        refine Finset.mem_Icc.mpr ⟨(Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd hk1 hdk), ?_⟩
        exact Nat.div_le_div_right hk2
      · intro j _
        exact Nat.mul_div_cancel_left j hd0
      · intro k hk
        exact Nat.mul_div_cancel' (Finset.mem_filter.mp hk).2
      · intro j _
        rw [Nat.cast_mul, div_div]
    rw [hbij]
    have hfl : ⌊(Y : ℝ) / (d : ℝ)⌋₊ = Y / d := Nat.floor_div_eq_div Y d
    have hmain := sum_log_div_le ((Y : ℝ) / (d : ℝ)) (by positivity)
    rwa [hfl] at hmain
  refine le_trans (Finset.sum_le_sum hinner) ?_
  have hsplit : ∑ d ∈ Finset.Icc 1 Y, (Y : ℝ) / (d : ℝ)
      = (Y : ℝ) * ∑ d ∈ Finset.Icc 1 Y, (1 : ℝ) / (d : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (sum_inv_Icc_le_one_add_log Y hY) (Nat.cast_nonneg Y)

/-- **Toolkit 4** (`Λ(n) ≤ log Y` on the range `n ≤ Y`). Mathlib has
`ArithmeticFunction.vonMangoldt_le_log`; the monotonicity step is stated with it here so
that Lemma 5.3's "bound Λ ≤ log Y twice" is a single citation.

Paper §5. Derivation: `LEMMA_Q5` §Q5.iii, "Bound Λ ≤ log Y twice".
Depends on: Mathlib only.
Rule 17: `1 ≤ n`, `n ≤ Y` only — a range condition on a summation index. -/
theorem vonMangoldt_le_log_of_le (n Y : ℕ) (hn : 1 ≤ n) (hnY : n ≤ Y) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log (Y : ℝ) := by
  refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
  exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnY)

/-- **Toolkit 5** (the inner sum of the `n − m` computation):
for `1 ≤ k ≤ Y`, `Σ_{m ≤ Y} (m(m+k))^{−1/2} ≤ 2 + log(Y/k)`.

`LEMMA_Q5 §Q5.iii` verbatim: split at `m ≤ k`, use `Σ_{m≤k}(mk)^{−1/2} ≤ 2` (Toolkit 1) and
`Σ_{k<m≤Y} 1/m ≤ log(Y/k)`.

Paper §5. Derivation: `LEMMA_Q5` §Q5.iii.
Depends on: `sum_one_div_sqrt_le`, harmonic bounds.
Rule 17: `1 ≤ k` and `k ≤ Y` only — both range conditions on summation indices (`k ≤ Y` is
automatic at the call site, where `k = |n−m|` with `n, m ≤ Y`). λ, X, T, D₀ absent. -/
theorem inner_sqrt_shift_le (Y k : ℕ) (hk : 1 ≤ k) (hkY : k ≤ Y) :
    ∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ)))
      ≤ 2 + Real.log ((Y : ℝ) / (k : ℝ)) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (le_trans hk hkY)
  have hsqk : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  -- split the range at `m = k`
  have hsplit : ∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ)))
      = (∑ m ∈ Finset.Ioc 0 k, (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ))))
        + ∑ m ∈ Finset.Ioc k Y, (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ))) := by
    rw [Icc_one_eq_Ioc_zero]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le k) hkY).symm
  -- low part: `m + k ≥ k`, then Toolkit 1
  have hA : ∑ m ∈ Finset.Ioc 0 k, (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ))) ≤ 2 := by
    have hstep : ∀ m ∈ Finset.Ioc 0 k,
        (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ)))
          ≤ (1 / Real.sqrt (k : ℝ)) * ((1 : ℝ) / Real.sqrt (m : ℝ)) := by
      intro m hm
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hm).1
      have hle : Real.sqrt ((m : ℝ) * (k : ℝ))
          ≤ Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ))) := by
        apply Real.sqrt_le_sqrt; nlinarith
      have hpos : (0 : ℝ) < Real.sqrt ((m : ℝ) * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
      have heq : Real.sqrt ((m : ℝ) * (k : ℝ)) = Real.sqrt (m : ℝ) * Real.sqrt (k : ℝ) :=
        Real.sqrt_mul hmR.le _
      have hsqm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
      calc (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ)))
          ≤ (1 : ℝ) / Real.sqrt ((m : ℝ) * (k : ℝ)) := one_div_le_one_div_of_le hpos hle
        _ = (1 / Real.sqrt (k : ℝ)) * ((1 : ℝ) / Real.sqrt (m : ℝ)) := by
            rw [heq]; field_simp
    calc ∑ m ∈ Finset.Ioc 0 k, (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ)))
        ≤ ∑ m ∈ Finset.Ioc 0 k, (1 / Real.sqrt (k : ℝ)) * ((1 : ℝ) / Real.sqrt (m : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = (1 / Real.sqrt (k : ℝ)) * ∑ m ∈ Finset.Ioc 0 k, (1 : ℝ) / Real.sqrt (m : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / Real.sqrt (k : ℝ)) * (2 * Real.sqrt (k : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le k) (by positivity)
      _ = 2 := by field_simp
  -- high part: `m + k ≥ m`, then the harmonic tail
  have hB : ∑ m ∈ Finset.Ioc k Y, (1 : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ)))
      ≤ Real.log (Y : ℝ) - Real.log (k : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun m hm => ?_)) (sum_inv_Ioc_le_log_sub k hk Y hkY)
    have hmk : k < m := (Finset.mem_Ioc.mp hm).1
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hle : (m : ℝ) ≤ Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ))) := by
      have h2 : Real.sqrt ((m : ℝ) * (m : ℝ))
          ≤ Real.sqrt ((m : ℝ) * ((m : ℝ) + (k : ℝ))) := by
        apply Real.sqrt_le_sqrt
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      rwa [Real.sqrt_mul_self hmR.le] at h2
    exact one_div_le_one_div_of_le hmR hle
  rw [hsplit, Real.log_div (ne_of_gt hYR) (ne_of_gt hkR)]
  linarith

/-- **Fill-local helper** for Toolkit 6: on the *small* half `n ≤ k/2` one has `k − n ≥ k/2`,
so `(n(k−n))^{−1/2} ≤ (k/2)^{−1/2}·n^{−1/2}`, and Toolkit 1 sums that to
`(k/2)^{−1/2}·2√(k/2) = 2`. -/
private theorem inner_split_half_le (k : ℕ) (hk : 2 ≤ k) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc 0 (k / 2)) :
    ∑ n ∈ S, (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ))) ≤ 2 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hhalf : (0 : ℝ) < (k : ℝ) / 2 := by linarith
  have hsq : (0 : ℝ) < Real.sqrt ((k : ℝ) / 2) := Real.sqrt_pos.mpr hhalf
  have hterm : ∀ n ∈ S, (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ)))
      ≤ (1 / Real.sqrt ((k : ℝ) / 2)) * ((1 : ℝ) / Real.sqrt (n : ℝ)) := by
    intro n hn
    have hmem := Finset.mem_Ioc.mp (hS hn)
    have hn1 : 1 ≤ n := hmem.1
    have hn2 : 2 * n ≤ k := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnk : (2 : ℝ) * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hn2
    have hle : Real.sqrt ((n : ℝ) * ((k : ℝ) / 2))
        ≤ Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ))) := by
      apply Real.sqrt_le_sqrt; nlinarith
    have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ) * ((k : ℝ) / 2)) := Real.sqrt_pos.mpr (by positivity)
    have heq : Real.sqrt ((n : ℝ) * ((k : ℝ) / 2))
        = Real.sqrt (n : ℝ) * Real.sqrt ((k : ℝ) / 2) := Real.sqrt_mul hnR.le _
    have hsqn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    calc (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ)))
        ≤ (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) / 2)) := one_div_le_one_div_of_le hpos hle
      _ = (1 / Real.sqrt ((k : ℝ) / 2)) * ((1 : ℝ) / Real.sqrt (n : ℝ)) := by
          rw [heq]; field_simp
  have hcd : (((k / 2 : ℕ)) : ℝ) ≤ (k : ℝ) / 2 := by
    have h := Nat.cast_div_le (α := ℝ) (m := k) (n := 2)
    simpa using h
  calc ∑ n ∈ S, (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ)))
      ≤ ∑ n ∈ S, (1 / Real.sqrt ((k : ℝ) / 2)) * ((1 : ℝ) / Real.sqrt (n : ℝ)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Ioc 0 (k / 2),
          (1 / Real.sqrt ((k : ℝ) / 2)) * ((1 : ℝ) / Real.sqrt (n : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS (fun n _ _ => by positivity)
    _ = (1 / Real.sqrt ((k : ℝ) / 2))
          * ∑ n ∈ Finset.Ioc 0 (k / 2), (1 : ℝ) / Real.sqrt (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (1 / Real.sqrt ((k : ℝ) / 2)) * (2 * Real.sqrt (((k / 2 : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le (k / 2)) (by positivity)
    _ ≤ (1 / Real.sqrt ((k : ℝ) / 2)) * (2 * Real.sqrt ((k : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := Real.sqrt_le_sqrt hcd
        linarith
    _ = 2 := by field_simp

/-- **Toolkit 6** (the inner sum of the `n + m` computation): `Σ_{n < k} (n(k−n))^{−1/2} ≤ 4`,
**absolutely bounded, with no `log(Y/k)` term at all**.

⚠️ This is the precise content of paper §5's "the n + m case is, if anything, easier", and it
is **a different computation** from Toolkit 5, not the same one (
the paper's word "verbatim" over-claims; "mutatis mutandis" is what is meant). Recorded so
it is not a surprise. Route: for `n ≤ k/2` one has `k − n ≥ k/2`, so the half-sum
is `≤ √(2/k)·2√(k/2) = 2`; symmetry doubles it.

Paper §5. Derivation: **none in the notes** — reconstructed, see Q2.
Depends on: `sum_one_div_sqrt_le`.
Rule 17: `2 ≤ k` only (so the range is nonempty). λ, X, T, D₀ absent. -/
theorem inner_sqrt_split_le (k : ℕ) (hk : 2 ≤ k) :
    ∑ n ∈ Finset.Ico 1 k, (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ))) ≤ 4 := by
  classical
  -- split at the midpoint
  have hAB : (∑ n ∈ (Finset.Ico 1 k).filter (fun n => 2 * n ≤ k),
        (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ))))
      + ∑ n ∈ (Finset.Ico 1 k).filter (fun n => ¬ (2 * n ≤ k)),
        (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ)))
      = ∑ n ∈ Finset.Ico 1 k, (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ))) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  -- the big half reflects onto the small half through `n ↦ k − n`
  have hinj : ∀ x ∈ (Finset.Ico 1 k).filter (fun n => ¬ (2 * n ≤ k)),
      ∀ y ∈ (Finset.Ico 1 k).filter (fun n => ¬ (2 * n ≤ k)), k - x = k - y → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
    omega
  have hrefl : ∑ n ∈ (Finset.Ico 1 k).filter (fun n => ¬ (2 * n ≤ k)),
        (1 : ℝ) / Real.sqrt ((n : ℝ) * ((k : ℝ) - (n : ℝ)))
      = ∑ j ∈ ((Finset.Ico 1 k).filter (fun n => ¬ (2 * n ≤ k))).image (fun n => k - n),
        (1 : ℝ) / Real.sqrt ((j : ℝ) * ((k : ℝ) - (j : ℝ))) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    have hnk : n ≤ k := by omega
    have hcast : ((k - n : ℕ) : ℝ) = (k : ℝ) - (n : ℝ) := Nat.cast_sub hnk
    rw [hcast]
    ring_nf
  -- both halves sit inside `Ioc 0 ⌊k/2⌋`
  have hAsub : (Finset.Ico 1 k).filter (fun n => 2 * n ≤ k) ⊆ Finset.Ioc 0 (k / 2) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    simp only [Finset.mem_Ioc]
    omega
  have hBsub : ((Finset.Ico 1 k).filter (fun n => ¬ (2 * n ≤ k))).image (fun n => k - n)
      ⊆ Finset.Ioc 0 (k / 2) := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨n, hn, hje⟩ := hj
    simp only [Finset.mem_Ioc]
    omega
  have h1 := inner_split_half_le k hk _ hAsub
  have h2 := inner_split_half_le k hk _ hBsub
  rw [← hAB, hrefl]
  linarith

/-- **Fill-local helper**: an injection of a set of pairs into an index set bounds the sum,
provided the target summand is nonnegative. The regrouping engine of Lemmas 5.3 and 5.3′. -/
private theorem inject_sum_bound {β : Type*} [DecidableEq β] (A : Finset (ℕ × ℕ))
    (T : Finset β) (φ : ℕ × ℕ → β) (hφ : ∀ x ∈ A, φ x ∈ T)
    (hinj : ∀ x ∈ A, ∀ y ∈ A, φ x = φ y → x = y)
    (F : ℕ × ℕ → ℝ) (H : β → ℝ) (hH : ∀ y, 0 ≤ H y)
    (hval : ∀ x ∈ A, F x = H (φ x)) :
    ∑ x ∈ A, F x ≤ ∑ y ∈ T, H y := by
  classical
  rw [Finset.sum_congr rfl hval, ← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => hH y)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact hφ x hx

/-- **Fill-local helper**: the `n − m` regrouping. Writing `k = |n − m|` and `p = min(n,m)`,
the off-diagonal double sum splits into the two halves `m < n` and `n < m`, each of which
injects into `{(k,p) : k, p ≤ Y}` — whence the factor 2. -/
private theorem offdiag_pair_bound (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ (Finset.Icc 1 Y).erase n,
        (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ))
      ≤ 2 * ∑ k ∈ Finset.Icc 1 Y, ∑ p ∈ Finset.Icc 1 Y,
          (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((p : ℝ) + (k : ℝ))) := by
  classical
  set g : ℕ × ℕ → ℝ := fun x =>
    (tau ((x.1 : ℤ) - (x.2 : ℤ)).natAbs : ℝ) / Real.sqrt ((x.1 : ℝ) * (x.2 : ℝ)) with hg
  set H : ℕ × ℕ → ℝ := fun y =>
    (tau y.1 : ℝ) / Real.sqrt ((y.2 : ℝ) * ((y.2 : ℝ) + (y.1 : ℝ))) with hH
  have hHnn : ∀ y : ℕ × ℕ, 0 ≤ H y := by
    intro y
    show (0 : ℝ) ≤ (tau y.1 : ℝ) / Real.sqrt ((y.2 : ℝ) * ((y.2 : ℝ) + (y.1 : ℝ)))
    positivity
  set S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y).filter (fun x => x.1 ≠ x.2) with hS
  have hmemS : ∀ x : ℕ × ℕ,
      x ∈ S ↔ ((1 ≤ x.1 ∧ x.1 ≤ Y) ∧ (1 ≤ x.2 ∧ x.2 ≤ Y)) ∧ x.1 ≠ x.2 := by
    intro x
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  have hLHS : ∑ x ∈ S, g x
      = ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ (Finset.Icc 1 Y).erase n, g (n, m) := by
    rw [hS, Finset.sum_filter,
      Finset.sum_product' (s := Finset.Icc 1 Y) (t := Finset.Icc 1 Y)
        (f := fun n m => if n ≠ m then g (n, m) else 0)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← Finset.filter_ne (Finset.Icc 1 Y) n, Finset.sum_filter]
  rw [← hLHS]
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun x => x.2 < x.1) g
  rw [← hsplit]
  have hprod : ∑ y ∈ Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y, H y
      = ∑ k ∈ Finset.Icc 1 Y, ∑ p ∈ Finset.Icc 1 Y,
          (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((p : ℝ) + (k : ℝ))) :=
    Finset.sum_product' (s := Finset.Icc 1 Y) (t := Finset.Icc 1 Y)
      (f := fun k p => (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((p : ℝ) + (k : ℝ))))
  have hA : ∑ x ∈ S.filter (fun x => x.2 < x.1), g x
      ≤ ∑ y ∈ Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y, H y := by
    refine inject_sum_bound _ (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y)
      (fun x => (x.1 - x.2, x.2)) ?_ ?_ g H hHnn ?_
    · rintro ⟨n, m⟩ hx
      rw [Finset.mem_filter, hmemS] at hx
      obtain ⟨⟨⟨⟨hn1, hnY⟩, hm1, hmY⟩, hne⟩, hmn⟩ := hx
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rintro ⟨n, m⟩ hx ⟨n2, m2⟩ hy hxy
      rw [Finset.mem_filter, hmemS] at hx hy
      have h1 : n - m = n2 - m2 := congrArg Prod.fst hxy
      have h2 : m = m2 := congrArg Prod.snd hxy
      have hmn : m < n := hx.2
      have hmn2 : m2 < n2 := hy.2
      rw [Prod.mk.injEq]
      omega
    · rintro ⟨n, m⟩ hx
      rw [Finset.mem_filter, hmemS] at hx
      have hmn : m < n := hx.2
      have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub (le_of_lt hmn)
      have htau : ((n : ℤ) - (m : ℤ)).natAbs = n - m := by omega
      have harg : (n : ℝ) * (m : ℝ) = (m : ℝ) * ((m : ℝ) + ((n - m : ℕ) : ℝ)) := by
        rw [hcast]; ring
      show (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ))
          = (tau (n - m) : ℝ) / Real.sqrt ((m : ℝ) * ((m : ℝ) + ((n - m : ℕ) : ℝ)))
      rw [htau, harg]
  have hB : ∑ x ∈ S.filter (fun x => ¬ x.2 < x.1), g x
      ≤ ∑ y ∈ Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y, H y := by
    refine inject_sum_bound _ (Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y)
      (fun x => (x.2 - x.1, x.1)) ?_ ?_ g H hHnn ?_
    · rintro ⟨n, m⟩ hx
      rw [Finset.mem_filter, hmemS] at hx
      obtain ⟨⟨⟨⟨hn1, hnY⟩, hm1, hmY⟩, hne⟩, hmn⟩ := hx
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rintro ⟨n, m⟩ hx ⟨n2, m2⟩ hy hxy
      rw [Finset.mem_filter, hmemS] at hx hy
      have h1 : m - n = m2 - n2 := congrArg Prod.fst hxy
      have h2 : n = n2 := congrArg Prod.snd hxy
      have hne : n ≠ m := hx.1.2
      have hne2 : n2 ≠ m2 := hy.1.2
      have hmn : ¬ m < n := hx.2
      have hmn2 : ¬ m2 < n2 := hy.2
      rw [Prod.mk.injEq]
      omega
    · rintro ⟨n, m⟩ hx
      rw [Finset.mem_filter, hmemS] at hx
      have hne : n ≠ m := hx.1.2
      have hmn : n < m := by
        have h := hx.2
        omega
      have hcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := Nat.cast_sub (le_of_lt hmn)
      have htau : ((n : ℤ) - (m : ℤ)).natAbs = m - n := by omega
      have harg : (n : ℝ) * (m : ℝ) = (n : ℝ) * ((n : ℝ) + ((m - n : ℕ) : ℝ)) := by
        rw [hcast]; ring
      show (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ))
          = (tau (m - n) : ℝ) / Real.sqrt ((n : ℝ) * ((n : ℝ) + ((m - n : ℕ) : ℝ)))
      rw [htau, harg]
  rw [hprod] at hA hB
  linarith

/-- **Fill-local helper**: the `n + m` regrouping. Writing `k = n + m` and `p = n`, the FULL
square injects into `{(k,p) : k ≤ 2Y, 1 ≤ p < k}` — a single injection, no factor 2, which is
the precise sense in which "the n + m case is, if anything, easier". -/
private theorem sumplus_pair_bound (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 Y,
        (tau (n + m) : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ))
      ≤ ∑ k ∈ Finset.Icc 1 (2 * Y), ∑ p ∈ Finset.Ico 1 k,
          (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((k : ℝ) - (p : ℝ))) := by
  classical
  have hT : ∑ y ∈ (Finset.Icc 1 (2 * Y)).sigma (fun k => Finset.Ico 1 k),
        (tau y.1 : ℝ) / Real.sqrt ((y.2 : ℝ) * ((y.1 : ℝ) - (y.2 : ℝ)))
      = ∑ k ∈ Finset.Icc 1 (2 * Y), ∑ p ∈ Finset.Ico 1 k,
          (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((k : ℝ) - (p : ℝ))) :=
    (Finset.sum_sigma' (Finset.Icc 1 (2 * Y)) (fun k => Finset.Ico 1 k)
      (fun k p => (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((k : ℝ) - (p : ℝ))))).symm
  rw [← hT]
  have hsrc : ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 Y,
        (tau (n + m) : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ))
      = ∑ x ∈ Finset.Icc 1 Y ×ˢ Finset.Icc 1 Y,
          (tau (x.1 + x.2) : ℝ) / Real.sqrt ((x.1 : ℝ) * (x.2 : ℝ)) :=
    (Finset.sum_product' (s := Finset.Icc 1 Y) (t := Finset.Icc 1 Y)
      (f := fun n m => (tau (n + m) : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ)))).symm
  rw [hsrc]
  refine inject_sum_bound _ _ (fun x => (⟨x.1 + x.2, x.1⟩ : (_ : ℕ) × ℕ)) ?_ ?_ _
    (fun y => (tau y.1 : ℝ) / Real.sqrt ((y.2 : ℝ) * ((y.1 : ℝ) - (y.2 : ℝ)))) ?_ ?_
  · rintro ⟨n, m⟩ hx
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hx
    obtain ⟨⟨hn1, hnY⟩, hm1, hmY⟩ := hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · rintro ⟨n, m⟩ _ ⟨n2, m2⟩ _ hxy
    have h1 : n + m = n2 + m2 := congrArg Sigma.fst hxy
    have h2 : n = n2 := by
      have h := congrArg Sigma.snd hxy
      simpa using h
    rw [Prod.mk.injEq]
    omega
  · intro y
    positivity
  · rintro ⟨n, m⟩ _
    have harg : (n : ℝ) * (m : ℝ) = (n : ℝ) * (((n + m : ℕ) : ℝ) - (n : ℝ)) := by
      push_cast; ring
    show (tau (n + m) : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ))
        = (tau (n + m) : ℝ) / Real.sqrt ((n : ℝ) * (((n + m : ℕ) : ℝ) - (n : ℝ)))
    rw [harg]

/-- **Lemma 5.3 (zone bound).** `S(Y) ≤ C·Y·(log Y)³` **unconditionally** — the divisor
AVERAGE, with no pointwise `τ ≤ Y^ε` (whose ε is not `o(δ′)` and would poison the zone edge).

`C` is stated **existentially**: it is absolute but **not explicit**. `LEMMA_Q5 § Attack
surface` item 2, verbatim: *"The sublemma's constant C is not optimized; if a later stage
needs the low–low error at a specific finite Q, compute S(Y) directly (the script does)."*
Nothing downstream consumes a numerical value — §10 prices the zone row by `s·δ′` with
`s = 0.5073`, not by `C`; **no numeral is invented here**.
Anchor (3): the measured growth exponent `j` in `S(Y) ~ Y(log Y)^j` is ≈ 1.5 and falling at
`Y ≤ 4000` (`log_q5.txt`: 2.14, 1.67, 1.65, 1.54 at Y = 500, 1000, 2000, 4000) — the proved
`j = 3` is comfortably conservative.

Paper §5. Derivation: `LEMMA_Q5` §Q5.iii, Sublemma.
Depends on: Toolkits 1–5. **Independent
of `lemma5_1`/`lemma5_2`** — a pure divisor-average estimate; can be filled in parallel.
Rule 17: the only hypothesis is `3 ≤ Y` (so `log Y > 1`; any fixed absolute threshold is
admissible since `C` is absolute). `Y` is a bare `ℕ` here — the identification with
`Q^{1−δ′}` happens only in the zone form. λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_3 : ∃ C : ℝ, 0 < C ∧
    ∀ Y : ℕ, 3 ≤ Y → zoneSum Y ≤ C * (Y : ℝ) * (Real.log (Y : ℝ)) ^ (3 : ℕ) := by
  refine ⟨12, by norm_num, ?_⟩
  intro Y hY3
  have hY1 : 1 ≤ Y := by omega
  have hYR : (3 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY3
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlogY : (1 : ℝ) ≤ Real.log (Y : ℝ) :=
    le_trans hlog3 (Real.log_le_log (by norm_num) hYR)
  set L : ℝ := Real.log (Y : ℝ) with hL
  set W : ℝ := ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ (Finset.Icc 1 Y).erase n,
    (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ)) with hW
  -- Step A: `Λ ≤ log Y` twice (Toolkit 4)
  have hA : zoneSum Y ≤ L ^ 2 * W := by
    rw [zoneSum, hW, Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun m hm => ?_)
    obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hm1, hmY⟩ := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hm)
    have hLn := vonMangoldt_le_log_of_le n Y hn1 hnY
    have hLm := vonMangoldt_le_log_of_le m Y hm1 hmY
    have hnn := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hnm := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    have hprodle :
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m ≤ L ^ 2 := by
      rw [hL]
      nlinarith
    have hq : (0 : ℝ) ≤ (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
        / Real.sqrt ((n : ℝ) * (m : ℝ)) := by positivity
    have hrw : ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
          / Real.sqrt ((n : ℝ) * (m : ℝ)) * (tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
        = (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m)
          * ((tau ((n : ℤ) - (m : ℤ)).natAbs : ℝ)
              / Real.sqrt ((n : ℝ) * (m : ℝ))) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hprodle hq
  -- Step B: regroup by `k = |n − m|`
  have hB : W ≤ 2 * ∑ k ∈ Finset.Icc 1 Y, ∑ p ∈ Finset.Icc 1 Y,
      (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((p : ℝ) + (k : ℝ))) := offdiag_pair_bound Y
  -- Step C: Toolkit 5 termwise
  have hC : ∑ k ∈ Finset.Icc 1 Y, ∑ p ∈ Finset.Icc 1 Y,
        (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((p : ℝ) + (k : ℝ)))
      ≤ ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) * (2 + Real.log ((Y : ℝ) / (k : ℝ))) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    obtain ⟨hk1, hkY⟩ := Finset.mem_Icc.mp hk
    have hin := inner_sqrt_shift_le Y k hk1 hkY
    have hfac : ∑ p ∈ Finset.Icc 1 Y, (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((p : ℝ) + (k : ℝ)))
        = (tau k : ℝ) * ∑ p ∈ Finset.Icc 1 Y,
            (1 : ℝ) / Real.sqrt ((p : ℝ) * ((p : ℝ) + (k : ℝ))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hin (Nat.cast_nonneg _)
  -- Step D: Toolkits 2 and 3
  have hD : ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) * (2 + Real.log ((Y : ℝ) / (k : ℝ)))
      ≤ 3 * ((Y : ℝ) * (1 + L)) := by
    have hexp : ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) * (2 + Real.log ((Y : ℝ) / (k : ℝ)))
        = 2 * (∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ))
          + ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) * Real.log ((Y : ℝ) / (k : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hexp]
    have h1 := sum_tau_le Y hY1
    have h2 := sum_tau_mul_log_le Y hY1
    rw [← hL] at h1 h2
    linarith
  have hfin : W ≤ 6 * ((Y : ℝ) * (1 + L)) := by linarith
  have hL2 : (0 : ℝ) ≤ L ^ 2 := by positivity
  have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg L, hlogY]
  have hcube : (Y : ℝ) * L ^ 2 ≤ (Y : ℝ) * L ^ 3 := mul_le_mul_of_nonneg_left hL23 hY0.le
  calc zoneSum Y ≤ L ^ 2 * W := hA
    _ ≤ L ^ 2 * (6 * ((Y : ℝ) * (1 + L))) := mul_le_mul_of_nonneg_left hfin hL2
    _ ≤ 12 * (Y : ℝ) * L ^ (3 : ℕ) := by linarith

/-- **Lemma 5.3′** (the `n + m` zone bound): `S′(Y) ≤ C·Y·(log Y)³`, `C` absolute,
unconditional, no pointwise `τ ≤ Y^ε`. Paper §5: "Lemma 5.3's divisor average applies
verbatim with τ(n + m) — the n + m case is, if anything, easier."

⚠️ **FLAG.** There is no `S′(Y)` in `LEMMA_Q5.md`, no proof and no anchor;
and "verbatim" is not verbatim — the inner estimate genuinely differs (Toolkit 6 versus
Toolkit 5), the `n + m` version being the easier of the two. The *conclusion* is right and
"if anything, easier" is right; only the word "verbatim" over-claims.

Paper §5. Derivation: **none in the notes**.
Depends on: Toolkits 2–4 and 6.
Rule 17: `3 ≤ Y` only. The full square range (diagonal included) is faithful to "with no
excluded diagonal". **No `n + m ≤ Q`.** λ-free, X-free, T-free, D₀-free. -/
theorem lemma5_3' : ∃ C : ℝ, 0 < C ∧
    ∀ Y : ℕ, 3 ≤ Y → zoneSumPlus Y ≤ C * (Y : ℝ) * (Real.log (Y : ℝ)) ^ (3 : ℕ) := by
  refine ⟨24, by norm_num, ?_⟩
  intro Y hY3
  have hY1 : 1 ≤ Y := by omega
  have hYR : (3 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY3
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlogY : (1 : ℝ) ≤ Real.log (Y : ℝ) :=
    le_trans hlog3 (Real.log_le_log (by norm_num) hYR)
  set L : ℝ := Real.log (Y : ℝ) with hL
  set W : ℝ := ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 Y,
    (tau (n + m) : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ)) with hW
  have hA : zoneSumPlus Y ≤ L ^ 2 * W := by
    rw [zoneSumPlus, hW, Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun m hm => ?_)
    obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hm1, hmY⟩ := Finset.mem_Icc.mp hm
    have hLn := vonMangoldt_le_log_of_le n Y hn1 hnY
    have hLm := vonMangoldt_le_log_of_le m Y hm1 hmY
    have hnn := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hnm := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    have hprodle :
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m ≤ L ^ 2 := by
      rw [hL]
      nlinarith
    have hq : (0 : ℝ) ≤ (tau (n + m) : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ)) := by positivity
    have hrw : ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
          / Real.sqrt ((n : ℝ) * (m : ℝ)) * (tau (n + m) : ℝ)
        = (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m)
          * ((tau (n + m) : ℝ) / Real.sqrt ((n : ℝ) * (m : ℝ))) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hprodle hq
  have hB := sumplus_pair_bound Y
  -- Toolkit 6 termwise: the inner sum is bounded by the ABSOLUTE constant 4
  have hC : ∑ k ∈ Finset.Icc 1 (2 * Y), ∑ p ∈ Finset.Ico 1 k,
        (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((k : ℝ) - (p : ℝ)))
      ≤ ∑ k ∈ Finset.Icc 1 (2 * Y), 4 * (tau k : ℝ) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    obtain ⟨hk1, hkY⟩ := Finset.mem_Icc.mp hk
    rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
    · simp
    · have hin := inner_sqrt_split_le k hk2
      have hfac : ∑ p ∈ Finset.Ico 1 k,
            (tau k : ℝ) / Real.sqrt ((p : ℝ) * ((k : ℝ) - (p : ℝ)))
          = (tau k : ℝ) * ∑ p ∈ Finset.Ico 1 k,
              (1 : ℝ) / Real.sqrt ((p : ℝ) * ((k : ℝ) - (p : ℝ))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
      rw [hfac]
      have h := mul_le_mul_of_nonneg_left hin (Nat.cast_nonneg (tau k))
      linarith
  have hD : ∑ k ∈ Finset.Icc 1 (2 * Y), 4 * (tau k : ℝ)
      ≤ 4 * ((2 * (Y : ℝ)) * (1 + (Real.log 2 + L))) := by
    have h1 := sum_tau_le (2 * Y) (by omega)
    have hcast : ((2 * Y : ℕ) : ℝ) = 2 * (Y : ℝ) := by push_cast; ring
    rw [hcast] at h1
    have hlog2 : Real.log (2 * (Y : ℝ)) = Real.log 2 + L := by
      rw [hL, ← Real.log_mul (by norm_num) (ne_of_gt hY0)]
    rw [hlog2] at h1
    rw [← Finset.mul_sum]
    linarith
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_two_lt_d9
    linarith
  have hL2 : (0 : ℝ) ≤ L ^ 2 := by positivity
  have hWle : W ≤ 4 * ((2 * (Y : ℝ)) * (1 + (Real.log 2 + L))) := by linarith
  have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg L, hlogY]
  have hcube : (Y : ℝ) * L ^ 2 ≤ (Y : ℝ) * L ^ 3 := mul_le_mul_of_nonneg_left hL23 hY0.le
  have hYL2 : (0 : ℝ) ≤ (Y : ℝ) * L ^ 2 := by positivity
  have hlogterm : (Y : ℝ) * L ^ 2 * Real.log 2 ≤ (Y : ℝ) * L ^ 2 := by nlinarith
  calc zoneSumPlus Y ≤ L ^ 2 * W := hA
    _ ≤ L ^ 2 * (4 * ((2 * (Y : ℝ)) * (1 + (Real.log 2 + L)))) :=
        mul_le_mul_of_nonneg_left hWle hL2
    _ ≤ 24 * (Y : ℝ) * L ^ (3 : ℕ) := by nlinarith [hcube, hlogterm]

/-! ### The join: from Lemma 5.2's crude bound to Lemma 5.3's zone sum

`LEMMA_Q5 §Q5.iii`, first sentence: "The low–low zone error (both n, m ≤ Y = Q^{1−δ′}) is,
**by Q5.ii's crude bound**, ≤ Q·S(Y)". These four lemmas are that step, stated so the §4 /
Corollary 3 does not re-derive it. -/

/-- The Λ-weight of the zone sums is nonnegative — the only analytic input to the four
zone-join lemmas below. -/
private theorem zone_weight_nonneg (n m : ℕ) :
    (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
      / Real.sqrt ((n : ℝ) * (m : ℝ)) :=
  div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)

/-- Termwise `‖(w : ℂ) * G‖ ≤ c * (w * t)` from `‖G‖ ≤ c * t` and `0 ≤ w`. -/
private theorem zone_term_le (w c t : ℝ) (G : ℂ) (hw : 0 ≤ w) (hG : ‖G‖ ≤ c * t) :
    ‖(w : ℂ) * G‖ ≤ c * (w * t) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  calc w * ‖G‖ ≤ w * (c * t) := mul_le_mul_of_nonneg_left hG hw
    _ = c * (w * t) := by ring

/-- **Zone join** (`n − m`, full family): the Λ-weighted low–low family off-diagonal is
`≤ Q·S(Y)`. This is `lemma5_2_crude` applied termwise inside `zoneSum`.

Paper §5. Derivation: `LEMMA_Q5` §Q5.iii, first sentence.
Depends on: `lemma5_2_crude`.
Rule 17: no hypotheses at all. `Y` and `Q` are unrelated here; the zone identification is
made downstream. λ-free, X-free, T-free, D₀-free. -/
theorem zone_offdiag_le (Q Y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ (Finset.Icc 1 Y).erase n,
        ((ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
            / Real.sqrt ((n : ℝ) * (m : ℝ)) : ℝ) : ℂ) * famPairSum Q n m‖
      ≤ (Q : ℝ) * zoneSum Y := by
  rw [zoneSum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
  exact zone_term_le _ _ _ _ (zone_weight_nonneg n m)
    (lemma5_2_crude Q n m (Finset.ne_of_mem_erase hm).symm)

/-- **Zone join** (`n + m`, full family) — the object Corollary 3's in-zone parity
projection must show negligible.

Paper §5, §1.1. Derivation: transported from §Q5.iii.
Depends on: `lemma5_2'_crude`.
Rule 17: no hypotheses at all. **No `n + m ≤ Q`.** -/
theorem zone_offdiag_neg_le (Q Y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
            / Real.sqrt ((n : ℝ) * (m : ℝ)) : ℝ) : ℂ) * famPairSumNeg Q n m‖
      ≤ (Q : ℝ) * zoneSumPlus Y := by
  rw [zoneSumPlus, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
  exact zone_term_le _ _ _ _ (zone_weight_nonneg n m)
    (lemma5_2'_crude Q n m (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1)

/-- **Zone join** (`n − m`, dyadic family) — Corollary 2's version, at the `3/2`.

Paper §5. Derivation: `LEMMA_Q5` §Q5.ii–iii.
Rule 17: no hypotheses at all; the dyadic range is a conductor restriction. -/
theorem zone_offdiag_dyadic_le (Q Y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ (Finset.Icc 1 Y).erase n,
        ((ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
            / Real.sqrt ((n : ℝ) * (m : ℝ)) : ℝ) : ℂ) * famPairSumDyadic Q n m‖
      ≤ (3 / 2 : ℝ) * (Q : ℝ) * zoneSum Y := by
  rw [zoneSum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
  exact zone_term_le _ _ _ _ (zone_weight_nonneg n m)
    (lemma5_2_crude_dyadic Q n m (Finset.ne_of_mem_erase hm).symm)

/-- **Zone join** (`n + m`, dyadic family) — **the** Corollary-3 in-zone error object
(even primitive, dyadic conductor).

Paper §1.1 (102–104), §12.3.
Rule 17: no hypotheses at all. **No `n + m ≤ Q`.** -/
theorem zone_offdiag_neg_dyadic_le (Q Y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
            / Real.sqrt ((n : ℝ) * (m : ℝ)) : ℝ) : ℂ) * famPairSumNegDyadic Q n m‖
      ≤ (3 / 2 : ℝ) * (Q : ℝ) * zoneSumPlus Y := by
  rw [zoneSumPlus, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
  exact zone_term_le _ _ _ _ (zone_weight_nonneg n m)
    (lemma5_2'_crude_dyadic Q n m (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1)

/-! ## 5. The zone forms and the δ′ = K·log log Q/log Q calibration

`LEMMA_Q5 §Q5.iv` — the section's one genuine finding, and the source of paper §5's
"needs **K ≥ 2**" sentence.

**Normalisation warning.** Lemma 5.3's second sentence ("≪ Q^{−δ′}ℒ
·(family diagonal)") mixes a §5 arithmetic bound with a §4/§10 normalisation. `§Q5.iv`
normalises by "the family diagonal ≍ (Q²-density)·ℒ²", i.e. by `Q²ℒ²` **with no factor of
`T`**, whereas §2.2 has `𝒩 ≍ Q²Tℒ`. Dropping `T ≥ (log Q)³` from the denominator makes the
ratio conservative by a factor `T` — safe, but it is a normalisation, not an identity. The
zone forms below therefore divide by an **explicit `Q²·ℒ²`** and leave the identification
with §4's family diagonal to the assembly. §5's obligation is thereby pure arithmetic.
Likewise the window/taper polylog factors (`§Q5.v`, `LEMMA_QT.a` at `|Im| = 0`) are §7
objects and are NOT silently absorbed here. -/

/-- **Fill-local helper**: `S(Y) ≥ 0` for the low–low zone sum (`Λ ≥ 0`, `√ ≥ 0`, `τ ≥ 0`). -/
private theorem zoneSum_nonneg (Y : ℕ) : 0 ≤ zoneSum Y := by
  refine Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun m _ => ?_))
  exact mul_nonneg (zone_weight_nonneg n m) (Nat.cast_nonneg _)

/-- **Fill-local helper**: `S′(Y) ≥ 0`. -/
private theorem zoneSumPlus_nonneg (Y : ℕ) : 0 ≤ zoneSumPlus Y := by
  refine Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun m _ => ?_))
  exact mul_nonneg (zone_weight_nonneg n m) (Nat.cast_nonneg _)

/-- **Fill-local helper**: `1 ≤ log 3`, i.e. `e ≤ 3` — the only numeric input to the zone
forms, used to know `1 ≤ ℒ` from `3 ≤ Q` and `log Q ≤ ℒ`. -/
private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith [Real.exp_one_lt_d9]

/-- **Fill-local helper — `LEMMA_Q5 §Q5.iv`, the zone-form calculation, done once.**

Given a nonnegative zone functional `S` obeying Lemma 5.3's bound `S(Y) ≤ C·Y·(log Y)³` for
`Y ≥ 3`, the normalised family off-diagonal at `Y = ⌊Q^{1−δ′}⌋` is `≤ C′·Q^{−δ′}·ℒ`:
`Q·C·Q^{1−δ′}·ℒ³ / (Q²ℒ²) = C·Q^{−δ′}·ℒ`, using `Y ≤ Q^{1−δ′}` and
`log Y ≤ (1−δ′)log Q ≤ log Q ≤ ℒ`.

The small-`Y` range `Y ≤ 2` is **not** covered by Lemma 5.3 (`3 ≤ Y` there) and is absorbed
into the constant: `S` is bounded there by the fixed real `S 0 + S 1 + S 2`, and `1 ≤ ℒ`
makes `ℒ³ ≥ 1` pay for it. This is exactly why `C` is existential. -/
private theorem zone_form_of_bound (S : ℕ → ℝ) (hSnn : ∀ Y, 0 ≤ S Y) (C : ℝ) (hC : 0 < C)
    (hS : ∀ Y : ℕ, 3 ≤ Y → S Y ≤ C * (Y : ℝ) * (Real.log (Y : ℝ)) ^ (3 : ℕ)) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (Q : ℕ) (δ' Lscr : ℝ), 3 ≤ Q → 0 < δ' → δ' < 1 → Real.log (Q : ℝ) ≤ Lscr →
        (Q : ℝ) * S ⌊(Q : ℝ) ^ ((1 : ℝ) - δ')⌋₊ / ((Q : ℝ) ^ (2 : ℕ) * Lscr ^ (2 : ℕ))
          ≤ C' * (Q : ℝ) ^ (-δ') * Lscr := by
  set D : ℝ := S 0 + S 1 + S 2 with hDdef
  set C' : ℝ := max C (D + 1) with hC'def
  have hCC' : C ≤ C' := le_max_left _ _
  have hC' : 0 < C' := lt_of_lt_of_le hC hCC'
  have hDC' : D ≤ C' := le_trans (by linarith) (le_max_right C (D + 1))
  refine ⟨C', hC', ?_⟩
  intro Q δ' Lscr hQ hδ0 hδ1 hL
  have hQ3 : (3 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith
  have hlogQ : (1 : ℝ) ≤ Real.log (Q : ℝ) :=
    le_trans one_le_log_three (Real.log_le_log (by norm_num) hQ3)
  have hL1 : (1 : ℝ) ≤ Lscr := le_trans hlogQ hL
  have hL0 : (0 : ℝ) < Lscr := by linarith
  have hL3 : (1 : ℝ) ≤ Lscr ^ (3 : ℕ) := one_le_pow₀ hL1
  set Y : ℕ := ⌊(Q : ℝ) ^ ((1 : ℝ) - δ')⌋₊ with hYdef
  have hden : (0 : ℝ) < (Q : ℝ) ^ (2 : ℕ) * Lscr ^ (2 : ℕ) := by positivity
  have hpow : (Q : ℝ) ^ (-δ') * ((Q : ℝ) ^ (2 : ℕ)) = (Q : ℝ) ^ ((2 : ℝ) - δ') := by
    rw [show ((Q : ℝ) ^ (2 : ℕ)) = (Q : ℝ) ^ ((2 : ℝ)) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
      ← Real.rpow_add hQ0]
    ring_nf
  rw [div_le_iff₀ hden]
  have hRHS : C' * (Q : ℝ) ^ (-δ') * Lscr * ((Q : ℝ) ^ (2 : ℕ) * Lscr ^ (2 : ℕ))
      = C' * ((Q : ℝ) ^ ((2 : ℝ) - δ')) * Lscr ^ (3 : ℕ) := by
    rw [← hpow]; ring
  rw [hRHS]
  by_cases hY3 : 3 ≤ Y
  · -- Lemma 5.3's own range
    have hYle : (Y : ℝ) ≤ (Q : ℝ) ^ ((1 : ℝ) - δ') := Nat.floor_le (Real.rpow_nonneg hQ0.le _)
    have hYnn : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg _
    have hYpos : (0 : ℝ) < (Y : ℝ) := by
      have : 0 < Y := by omega
      exact_mod_cast this
    have hlogYnn : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
    have hlogYL : Real.log (Y : ℝ) ≤ Lscr := by
      calc Real.log (Y : ℝ) ≤ Real.log ((Q : ℝ) ^ ((1 : ℝ) - δ')) := Real.log_le_log hYpos hYle
        _ = ((1 : ℝ) - δ') * Real.log (Q : ℝ) := Real.log_rpow hQ0 _
        _ ≤ Real.log (Q : ℝ) := by nlinarith
        _ ≤ Lscr := hL
    have hqnn : (0 : ℝ) ≤ (Q : ℝ) ^ ((1 : ℝ) - δ') := Real.rpow_nonneg hQ0.le _
    have hpownn : (0 : ℝ) ≤ (Real.log (Y : ℝ)) ^ (3 : ℕ) := by positivity
    have hlogpow : (Real.log (Y : ℝ)) ^ (3 : ℕ) ≤ Lscr ^ (3 : ℕ) :=
      pow_le_pow_left₀ hlogYnn hlogYL 3
    have hpow2 : (Q : ℝ) * ((Q : ℝ) ^ ((1 : ℝ) - δ')) = (Q : ℝ) ^ ((2 : ℝ) - δ') := by
      have hsplit : (Q : ℝ) ^ ((2 : ℝ) - δ')
          = (Q : ℝ) ^ ((1 : ℝ)) * (Q : ℝ) ^ ((1 : ℝ) - δ') := by
        rw [← Real.rpow_add hQ0]
        ring_nf
      rw [hsplit, Real.rpow_one]
    calc (Q : ℝ) * S Y
        ≤ (Q : ℝ) * (C * (Y : ℝ) * (Real.log (Y : ℝ)) ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_left (hS Y hY3) hQ0.le
      _ ≤ (Q : ℝ) * (C' * ((Q : ℝ) ^ ((1 : ℝ) - δ')) * Lscr ^ (3 : ℕ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hQ0.le
          calc C * (Y : ℝ) * (Real.log (Y : ℝ)) ^ (3 : ℕ)
              ≤ C' * ((Q : ℝ) ^ ((1 : ℝ) - δ')) * (Real.log (Y : ℝ)) ^ (3 : ℕ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul hCC' hYle hYnn hC'.le) hpownn
            _ ≤ C' * ((Q : ℝ) ^ ((1 : ℝ) - δ')) * Lscr ^ (3 : ℕ) :=
                mul_le_mul_of_nonneg_left hlogpow (mul_nonneg hC'.le hqnn)
      _ = C' * ((Q : ℝ) * ((Q : ℝ) ^ ((1 : ℝ) - δ'))) * Lscr ^ (3 : ℕ) := by ring
      _ = C' * ((Q : ℝ) ^ ((2 : ℝ) - δ')) * Lscr ^ (3 : ℕ) := by rw [hpow2]
  · -- the `Y ≤ 2` remainder, absorbed into `C'`
    have hSY : S Y ≤ D := by
      have h0 := hSnn 0
      have h1 := hSnn 1
      have h2 := hSnn 2
      have hcase : Y = 0 ∨ Y = 1 ∨ Y = 2 := by omega
      rcases hcase with h | h | h <;> rw [h] <;> rw [hDdef] <;> linarith
    have hstep : D ≤ C' * Lscr ^ (3 : ℕ) := by
      have : C' * 1 ≤ C' * Lscr ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hL3 hC'.le
      linarith
    have hexp : (Q : ℝ) ≤ (Q : ℝ) ^ ((2 : ℝ) - δ') := by
      have h := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : (1 : ℝ) ≤ (2 : ℝ) - δ')
      rwa [Real.rpow_one] at h
    calc (Q : ℝ) * S Y ≤ (Q : ℝ) * D := mul_le_mul_of_nonneg_left hSY hQ0.le
      _ ≤ (Q : ℝ) * (C' * Lscr ^ (3 : ℕ)) := mul_le_mul_of_nonneg_left hstep hQ0.le
      _ ≤ ((Q : ℝ) ^ ((2 : ℝ) - δ')) * (C' * Lscr ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = C' * ((Q : ℝ) ^ ((2 : ℝ) - δ')) * Lscr ^ (3 : ℕ) := by ring

/-- **Lemma 5.3, zone form.** At `Y = Q^{1−δ′}`, the family off-diagonal normalised by
`Q²ℒ²` is `≤ C·Q^{−δ′}·ℒ` (`LEMMA_Q5 §Q5.iv`, first display, at the proved `j = 3`).

Paper §5. Derivation: `LEMMA_Q5` §Q5.iv.
Depends on: `lemma5_3`.
Rule 17: hypotheses are `3 ≤ Q` (so `log log Q > 0`), `0 < δ′ < 1` (structural, so
`1 ≤ Y = Q^{1−δ′}`) and `log Q ≤ ℒ`. The last is **true by definition** in the paper
(`ℒ = log(QT/2π) ≥ log Q` for `T ≥ 2π`); it is stated as a hypothesis so that §5 need not
import `ℒ`'s definition or `T` at all, and it is a **lower** bound on ℒ — an upper bound on
nothing. **`Y = Q^{1−δ′}` is the certificate's s-zone split (paper §4: "the in-zone
breakpoint is |s| ≤ (1 − δ′)·log Q"), NOT a bandwidth restriction**: `n` runs to `X = Q^λ`
with λ > 1 out-zone, handled by the sieve, never by §5. λ-free, X-free, D₀-free; `T` enters
only through the lower bound `log Q ≤ ℒ`. -/
theorem lemma5_3_zone : ∃ C : ℝ, 0 < C ∧
    ∀ (Q : ℕ) (δ' Lscr : ℝ), 3 ≤ Q → 0 < δ' → δ' < 1 → Real.log (Q : ℝ) ≤ Lscr →
      (Q : ℝ) * zoneSum ⌊(Q : ℝ) ^ ((1 : ℝ) - δ')⌋₊ / ((Q : ℝ) ^ (2 : ℕ) * Lscr ^ (2 : ℕ))
        ≤ C * (Q : ℝ) ^ (-δ') * Lscr := by
  obtain ⟨C, hC, h⟩ := lemma5_3
  exact zone_form_of_bound zoneSum zoneSum_nonneg C hC h

/-- **Lemma 5.3′, zone form** — the `n + m` analogue, i.e. the object Corollary 3's in-zone
parity projection needs to be negligible "at the same zone-edge calibration" (paper §1.1).

Paper §5, §1.1. Derivation: transported from §Q5.iv.
Depends on: `lemma5_3'`.
Rule 17: as `lemma5_3_zone`. **`n + m ≤ Q` is ABSENT**: `n + m ≤ 2Y = 2Q^{1−δ′}` is a
*consequence* of the zone range here, never a hypothesis. λ-free, X-free,
D₀-free; `T` only through `log Q ≤ ℒ`. -/
theorem lemma5_3'_zone : ∃ C : ℝ, 0 < C ∧
    ∀ (Q : ℕ) (δ' Lscr : ℝ), 3 ≤ Q → 0 < δ' → δ' < 1 → Real.log (Q : ℝ) ≤ Lscr →
      (Q : ℝ) * zoneSumPlus ⌊(Q : ℝ) ^ ((1 : ℝ) - δ')⌋₊
          / ((Q : ℝ) ^ (2 : ℕ) * Lscr ^ (2 : ℕ))
        ≤ C * (Q : ℝ) ^ (-δ') * Lscr := by
  obtain ⟨C, hC, h⟩ := lemma5_3'
  exact zone_form_of_bound zoneSumPlus zoneSumPlus_nonneg C hC h

/-- **The zone-edge identity.** With `δ′ = K·log log Q/log Q` one has *exactly*
`Q^{−δ′} = (log Q)^{−K}`. The whole calibration finding is this one line plus arithmetic.

Paper §5. Derivation: `LEMMA_Q5` §Q5.iv, "Repair".
Depends on: Mathlib only (`Real.rpow_natCast`-free; it is
`exp/log` bookkeeping).
Rule 17: `0 < Q` and `0 < log Q` only, both well-formedness conditions for `rpow`/`log`.
λ, X, T, D₀ absent. -/
theorem rpow_neg_zoneEdge (Q K : ℝ) (hQ : 0 < Q) (hlogQ : 0 < Real.log Q) :
    Q ^ (-(K * Real.log (Real.log Q) / Real.log Q)) = (Real.log Q) ^ (-K) := by
  rw [Real.rpow_def_of_pos hQ, Real.rpow_def_of_pos hlogQ]
  congr 1
  field_simp

/-- **The calibration, positive half: `K ≥ 2` suffices.** The Lemma 5.3 zone bound at
`δ′ = K·log log Q/log Q` is `O((log Q)^{1−K})`, which tends to `0` exactly when `K > 1`;
`K = 2` is the **proved minimum** and the design adopts `K = 3` (paper §2.2's
`δ′ := 3 log log Q/log Q`, `Defs.ParamsQ.deltaPrime`) — "a conservative choice, not a forced
one (the budget constant s(r + K) prices each unit of K at 0.5073)".

⚠️ Read `LEMMA_Q5 §Q5.iv` with its R4/R5 banners: the sentence "the LEMMA adopts K = 2" there
is **historical**. K = 3 is final. (The shipped `q5_check.py` still prints "the LEMMA adopts
K = 2 as proved-safe" — a stale comment string; no computed number depends on it. The
§0.1 / open question Q3.)

Paper §5. Derivation: `LEMMA_Q5` §Q5.iv.
Depends on: Mathlib only.
Rule 17: `2 ≤ K` only. λ, X, T, D₀ absent. -/
theorem zoneEdge_calibration_needs_two {K : ℝ} (hK : 2 ≤ K) :
    Filter.Tendsto (fun x : ℝ => (Real.log x) ^ (1 - K)) Filter.atTop (nhds 0) := by
  have h : (0 : ℝ) < K - 1 := by linarith
  have h2 := (tendsto_rpow_neg_atTop h).comp Real.tendsto_log_atTop
  refine h2.congr (fun x => ?_)
  simp only [Function.comp_apply]
  congr 1
  ring

/-- **The calibration, negative half: `K = 1` fails.** At `K = 1` the relative error is
`(log Q)^0 = 1` — `Θ(1)`, not `o(1)`. This is the finding: "δ′ → 0 slowly" was too loose.
Anchor (4), `log_q5.txt`: "the K = 1 column sits at exactly 1.000 for every log Q".

Paper §5. Derivation: `LEMMA_Q5` §Q5.iv.
Depends on: Mathlib only.
Rule 17: `log x ≠ 0` only. λ, X, T, D₀ absent. -/
theorem zoneEdge_calibration_K_one (x : ℝ) (hx : Real.log x ≠ 0) :
    (Real.log x) ^ (1 - (1 : ℝ)) = 1 := by
  norm_num

/-- **Lemma 5.3, zone form at the calibrated edge** — `lemma5_3_zone` composed with
`rpow_neg_zoneEdge`: at `δ′ = K·log log Q/log Q` the normalised low–low off-diagonal is
`≤ C·(log Q)^{−K}·ℒ`. This is the shape §4/§10 consume; with `K ≥ 2` and `log Q ≤ ℒ` it is
`O(ℒ^{1−K}) = o(1)`, which is the content of "needs K ≥ 2".

Paper §5. Derivation: `LEMMA_Q5` §Q5.iv.
Depends on: `lemma5_3_zone`, `rpow_neg_zoneEdge`.
Rule 17: as `lemma5_3_zone`, plus `0 < K` and `0 < log log Q / log Q < 1/K` folded into the
same structural `0 < δ′ < 1`. λ-free, X-free, D₀-free; `T` only through `log Q ≤ ℒ`. -/
theorem lemma5_3_zone_calibrated : ∃ C : ℝ, 0 < C ∧
    ∀ (Q : ℕ) (K Lscr : ℝ), 3 ≤ Q → 0 < K →
      0 < K * Real.log (Real.log (Q : ℝ)) / Real.log (Q : ℝ) →
      K * Real.log (Real.log (Q : ℝ)) / Real.log (Q : ℝ) < 1 →
      Real.log (Q : ℝ) ≤ Lscr →
      (Q : ℝ) * zoneSum
          ⌊(Q : ℝ) ^ ((1 : ℝ) - K * Real.log (Real.log (Q : ℝ)) / Real.log (Q : ℝ))⌋₊
          / ((Q : ℝ) ^ (2 : ℕ) * Lscr ^ (2 : ℕ))
        ≤ C * (Real.log (Q : ℝ)) ^ (-K) * Lscr := by
  obtain ⟨C, hC, h⟩ := lemma5_3_zone
  refine ⟨C, hC, ?_⟩
  intro Q K Lscr hQ _ hδ0 hδ1 hL
  have hQ3 : (3 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  have hlogQ : (0 : ℝ) < Real.log (Q : ℝ) :=
    lt_of_lt_of_le zero_lt_one
      (le_trans one_le_log_three (Real.log_le_log (by norm_num) hQ3))
  have key := h Q (K * Real.log (Real.log (Q : ℝ)) / Real.log (Q : ℝ)) Lscr hQ hδ0 hδ1 hL
  rwa [rpow_neg_zoneEdge (Q : ℝ) K hQ0 hlogQ] at key

/-- **Lemma 5.3′, zone form at the calibrated edge** — the `n + m` analogue, i.e. exactly
the statement paper §1.1 makes when it says the χ(−1)-half "is negligible at the same
zone-edge calibration".

Paper §1.1, §5. Derivation: `LEMMA_Q5` §Q5.iv.
Depends on: `lemma5_3'_zone`, `rpow_neg_zoneEdge`.
Rule 17: as `lemma5_3_zone_calibrated`. **No `n + m ≤ Q`.** -/
theorem lemma5_3'_zone_calibrated : ∃ C : ℝ, 0 < C ∧
    ∀ (Q : ℕ) (K Lscr : ℝ), 3 ≤ Q → 0 < K →
      0 < K * Real.log (Real.log (Q : ℝ)) / Real.log (Q : ℝ) →
      K * Real.log (Real.log (Q : ℝ)) / Real.log (Q : ℝ) < 1 →
      Real.log (Q : ℝ) ≤ Lscr →
      (Q : ℝ) * zoneSumPlus
          ⌊(Q : ℝ) ^ ((1 : ℝ) - K * Real.log (Real.log (Q : ℝ)) / Real.log (Q : ℝ))⌋₊
          / ((Q : ℝ) ^ (2 : ℕ) * Lscr ^ (2 : ℕ))
        ≤ C * (Real.log (Q : ℝ)) ^ (-K) * Lscr := by
  obtain ⟨C, hC, h⟩ := lemma5_3'_zone
  refine ⟨C, hC, ?_⟩
  intro Q K Lscr hQ _ hδ0 hδ1 hL
  have hQ3 : (3 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  have hlogQ : (0 : ℝ) < Real.log (Q : ℝ) :=
    lt_of_lt_of_le zero_lt_one
      (le_trans one_le_log_three (Real.log_le_log (by norm_num) hQ3))
  have key := h Q (K * Real.log (Real.log (Q : ℝ)) / Real.log (Q : ℝ)) Lscr hQ hδ0 hδ1 hL
  rwa [rpow_neg_zoneEdge (Q : ℝ) K hQ0 hlogQ] at key

/-! ## 6. The parity-projector bridge — the ONLY interface Corollary 3 uses into §5

Paper §1.1 Corollary 3 and §12.3 consume Lemmas 5.2/5.2′ **only** through the projector
`Σ_{χ even} = ½ Σ*_χ (1 + χ(−1))`. Paper §5 closes: "No case split between the dyadic and
full families, and no subfamily sieve, occurs anywhere in this section — Lemmas 5.2/5.2′ are
uniform over q ≤ Q (the parity SUBFAMILY appears only in Corollary 3's projector, which
consumes them at full-family level)." The bridge is therefore stated here, at full-family
level, and Corollary 3 imports it rather than re-deriving it.

**Ownership note — these are NOT in §5 and must not leak into it:** `S(q) := Σ*_χ χ(−1)` and
its multiplicative closed form, `Σ_{q≤Q} S(q) = O(Q)`, `#even-prim(q) = (φ*(q)+S(q))/2` and
`𝒩_even = ½𝒩 + O(QTℒ)` are **Corollary-3** objects and are deliberately NOT stated here.
`S(q)` is `primPairSumNeg q 1 1`, so the interface is already there. -/

/-- **Fill-local helper**: `Defs.parity χ = 0` is `χ.Even`, unfolding the frozen
`Classical.decPred` `if`. -/
private theorem parity_eq_zero_iff {q : ℕ} (χ : DirichletCharacter ℂ q) :
    parity χ = 0 ↔ χ.Even := by
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.Even)
  by_cases h : χ.Even
  · simp [parity, h]
  · simp [parity, h]

/-- **Fill-local helper**: `Defs.parity χ = 1` is `χ.Odd`. Uses
`DirichletCharacter.even_or_odd` (ℂ has no zero divisors) and `not_even_and_odd`
(`(2 : ℂ) ≠ 0`) — the two facts that make the parity split exact. -/
private theorem parity_eq_one_iff {q : ℕ} (χ : DirichletCharacter ℂ q) :
    parity χ = 1 ↔ χ.Odd := by
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.Even)
  by_cases h : χ.Even
  · simp only [parity, if_pos h]
    constructor
    · intro hc; exact absurd hc (by norm_num)
    · intro ho; exact absurd ⟨h, ho⟩ (DirichletCharacter.not_even_and_odd χ)
  · simp only [parity, if_neg h]
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    rcases DirichletCharacter.even_or_odd χ with he | ho
    · exact absurd he h
    · exact ho

/-- Membership in the even primitive subfamily, in terms of the frozen `Defs.parity`
(`parity χ = 0 ↔ χ.Even`). Stated so the Corollary-3 and §9 tracks can move between the two
spellings without unfolding `parity`'s `Classical.decPred`.

Paper §2.2 (parity κ) / §1.1 Corollary 3. Derivation: none needed.
Depends on: `Defs.parity`, `primitiveCharsEven`.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem mem_primitiveCharsEven_iff {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ ∈ primitiveCharsEven q ↔ χ ∈ primitiveChars q ∧ parity χ = 0 := by
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.Even)
  have h : χ ∈ primitiveCharsEven q ↔ χ ∈ primitiveChars q ∧ χ.Even := Finset.mem_filter
  rw [h, parity_eq_zero_iff]

/-- Membership in the odd primitive subfamily, in terms of `Defs.parity` (`parity χ = 1`).

Paper §2.2 / §1.1 Corollary 3. Derivation: none needed.
Depends on: `Defs.parity`, `primitiveCharsOdd`.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem mem_primitiveCharsOdd_iff {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ ∈ primitiveCharsOdd q ↔ χ ∈ primitiveChars q ∧ parity χ = 1 := by
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.Odd)
  have h : χ ∈ primitiveCharsOdd q ↔ χ ∈ primitiveChars q ∧ χ.Odd := Finset.mem_filter
  rw [h, parity_eq_one_iff]

/-- The two parity classes are disjoint (`DirichletCharacter.not_even_and_odd`).

Paper §1.1 Corollary 3. Derivation: none needed.
Depends on: Mathlib only.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem primitiveCharsEven_disjoint_odd (q : ℕ) :
    Disjoint (primitiveCharsEven q) (primitiveCharsOdd q) := by
  rw [Finset.disjoint_left]
  intro χ h1 h2
  rw [mem_primitiveCharsEven_iff] at h1
  rw [mem_primitiveCharsOdd_iff] at h2
  rw [h1.2] at h2
  exact absurd h2.2 (by norm_num)

/-- The two parity classes exhaust the primitive family (`DirichletCharacter.even_or_odd`,
available since ℂ has no zero divisors). Together with disjointness this is what makes the
projector an exact decomposition — Corollary 3's "The even subfamily carries exactly half
the character mass" rests on it.

Paper §1.1 Corollary 3. Derivation: none needed.
Depends on: Mathlib only.
Rule 17: no hypotheses; λ, X, T, D₀ absent. -/
theorem primitiveCharsEven_union_odd (q : ℕ) :
    letI := Classical.decEq (DirichletCharacter ℂ q)
    primitiveCharsEven q ∪ primitiveCharsOdd q = primitiveChars q := by
  letI := Classical.decEq (DirichletCharacter ℂ q)
  ext χ
  rw [Finset.mem_union, mem_primitiveCharsEven_iff, mem_primitiveCharsOdd_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases DirichletCharacter.even_or_odd χ with he | ho
    · exact Or.inl ⟨h, (parity_eq_zero_iff χ).mpr he⟩
    · exact Or.inr ⟨h, (parity_eq_one_iff χ).mpr ho⟩

/-- **Fill-local helper**: the primitive family splits as even ⊔ odd, so the untwisted pair
sum is the sum of its two parity halves. -/
private theorem primPairSum_split (q n m : ℕ) :
    letI := Classical.decEq (DirichletCharacter ℂ q)
    primPairSum q n m
      = (∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q) * conj (χ (m : ZMod q)))
        + (∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q) * conj (χ (m : ZMod q))) := by
  letI := Classical.decEq (DirichletCharacter ℂ q)
  rw [primPairSum, ← primitiveCharsEven_union_odd q,
    Finset.sum_union (primitiveCharsEven_disjoint_odd q)]

/-- **Fill-local helper**: the χ(−1)-twisted pair sum is the *difference* of the two parity
halves, since `χ(−1) = 1` on the even half and `= −1` on the odd half. -/
private theorem primPairSumNeg_split (q n m : ℕ) :
    letI := Classical.decEq (DirichletCharacter ℂ q)
    primPairSumNeg q n m
      = (∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q) * conj (χ (m : ZMod q)))
        - (∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q) * conj (χ (m : ZMod q))) := by
  letI := Classical.decEq (DirichletCharacter ℂ q)
  have hE : ∑ χ ∈ primitiveCharsEven q,
        χ (-1 : ZMod q) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))
      = ∑ χ ∈ primitiveCharsEven q, χ (n : ZMod q) * conj (χ (m : ZMod q)) := by
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    rw [mem_primitiveCharsEven_iff, parity_eq_zero_iff] at hχ
    have he : χ (-1 : ZMod q) = 1 := hχ.2
    rw [he, one_mul]
  have hO : ∑ χ ∈ primitiveCharsOdd q,
        χ (-1 : ZMod q) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))
      = -∑ χ ∈ primitiveCharsOdd q, χ (n : ZMod q) * conj (χ (m : ZMod q)) := by
    have h1 : ∑ χ ∈ primitiveCharsOdd q,
          χ (-1 : ZMod q) * (χ (n : ZMod q) * conj (χ (m : ZMod q)))
        = ∑ χ ∈ primitiveCharsOdd q,
          (-1 : ℂ) * (χ (n : ZMod q) * conj (χ (m : ZMod q))) := by
      refine Finset.sum_congr rfl (fun χ hχ => ?_)
      rw [mem_primitiveCharsOdd_iff, parity_eq_one_iff] at hχ
      have ho : χ (-1 : ZMod q) = -1 := hχ.2
      rw [ho]
    rw [h1, ← Finset.mul_sum, neg_one_mul]
  rw [primPairSumNeg, ← primitiveCharsEven_union_odd q,
    Finset.sum_union (primitiveCharsEven_disjoint_odd q), hE, hO]
  ring

/-- **The in-zone parity projector, per modulus** (paper §1.1 Corollary 3, §12.3):
`Σ_{χ even prim mod q} χ(n)χ̄(m) = ½ Σ*_χ (1 + χ(−1)) χ(n)χ̄(m)`.
The atom from which every family form below follows.

Paper §1.1, §12.3. Derivation: none in the notes.
Depends on: `primitiveCharsEven_union_odd`, `Even.eval_neg`.
Rule 17: **no hypotheses at all** — in particular no `n + m ≤ Q`. λ, X, T, D₀ absent. -/
theorem primPairSum_even_eq (q n m : ℕ) :
    primPairSumEven q n m = (primPairSum q n m + primPairSumNeg q n m) / 2 := by
  letI := Classical.decEq (DirichletCharacter ℂ q)
  rw [primPairSum_split q n m, primPairSumNeg_split q n m, primPairSumEven]
  ring

/-- **The odd projector, per modulus**, `½Σ*(1 − χ(−1))` — paper §1.1: "The identical
argument with the projector ½Σ*(1 − χ(−1)) gives the ODD primitive family at the same
constants".

Paper §1.1. Derivation: none in the notes.
Depends on: `primitiveCharsEven_union_odd`, `Odd.eval_neg`.
Rule 17: no hypotheses at all. -/
theorem primPairSum_odd_eq (q n m : ℕ) :
    primPairSumOdd q n m = (primPairSum q n m - primPairSumNeg q n m) / 2 := by
  letI := Classical.decEq (DirichletCharacter ℂ q)
  rw [primPairSum_split q n m, primPairSumNeg_split q n m, primPairSumOdd]
  ring

/-- **The in-zone parity projector, `q ≤ Q`** — the shape Corollary 3 consumes for the
`q ≤ Q` even primitive family ("Even primitive over q ≤ Q: 0.6980745436 at C = π⁴/9").
With it, Corollary 3's in-zone term is `½(famPairSum + famPairSumNeg)`, whose first half is
"half the full-family form, in step with the halved denominator" and whose second half is
governed by Lemma 5.2′ and shown negligible by `lemma5_3'_zone_calibrated`.

Paper §1.1 (104–105), §12.3.
Rule 17: **no hypotheses at all.** In particular NOT `n + m ≤ Q`: that inequality is where
Corollary 3 applies this, not a condition for the projector to hold. λ, X, T, D₀ absent. -/
theorem parity_projector_even (Q n m : ℕ) :
    famPairSumEven Q n m = (famPairSum Q n m + famPairSumNeg Q n m) / 2 := by
  rw [famPairSumEven, famPairSum, famPairSumNeg, ← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl (fun q _ => primPairSum_even_eq q n m)

/-- **The odd projector, `q ≤ Q`.**

Paper §1.1.
Rule 17: no hypotheses at all. -/
theorem parity_projector_odd (Q n m : ℕ) :
    famPairSumOdd Q n m = (famPairSum Q n m - famPairSumNeg Q n m) / 2 := by
  rw [famPairSumOdd, famPairSum, famPairSumNeg, ← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl (fun q _ => primPairSum_odd_eq q n m)

/-- **The in-zone parity projector, dyadic** — **the** Corollary-3 shape
(`P_even,dyad = 0.6919434301`, `C = 4π⁴/27`, the Sono-comparable statement).

Paper §1.1, §12.3.
Rule 17: **no hypotheses at all**; the dyadic range is a conductor restriction and the
`n + m ≤ 2Q^{1−δ′}` of §1.1 is deliberately absent. λ, X, T, D₀ absent. -/
theorem parity_projector_even_dyadic (Q n m : ℕ) :
    famPairSumEvenDyadic Q n m
      = (famPairSumDyadic Q n m + famPairSumNegDyadic Q n m) / 2 := by
  rw [famPairSumEvenDyadic, famPairSumDyadic, famPairSumNegDyadic, ← Finset.sum_add_distrib,
    Finset.sum_div]
  exact Finset.sum_congr rfl (fun q _ => primPairSum_even_eq q n m)

/-- **The odd projector, dyadic** (`P_odd,dyad = 0.6919434301`; "a class in which the
literature contains no result at all").

Paper §1.1.
Rule 17: no hypotheses at all. -/
theorem parity_projector_odd_dyadic (Q n m : ℕ) :
    famPairSumOddDyadic Q n m
      = (famPairSumDyadic Q n m - famPairSumNegDyadic Q n m) / 2 := by
  rw [famPairSumOddDyadic, famPairSumDyadic, famPairSumNegDyadic, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  exact Finset.sum_congr rfl (fun q _ => primPairSum_odd_eq q n m)

/-! ## 7. Bridge to `ParamsQ`

§5 itself is parameter-free — every statement above is about `ℕ` and `ℝ`. These two lemmas
connect the frozen `Defs.ParamsQ.zoneY` / `Defs.ParamsQ.deltaPrime` to the `Y = Q^{1−δ′}` and
`K = 3` shapes used above, so the assembly does not re-derive them. -/

/-- `Y := e^{s₀} = Q^{1−δ′}` — `Defs.ParamsQ.zoneY` in the `rpow` form the zone lemmas use.
(`zoneY = exp s₀`, `s₀ = (1 − δ′)·log Q`.)

Paper §2.2 (the zone cutoff) / §5. Derivation: definitional unfolding.
Depends on: `Defs.ParamsQ.zoneY`, `Defs.ParamsQ.s0`.
Rule 17: `0 < P.Q` only (implied by `Valid.Q_ge : 3 ≤ P.Q`). **This is a zone split, not a
bandwidth cap**: nothing here relates `Y` to `X = e^{λℒ}`, and §5 never mentions `X`. -/
theorem zoneY_eq_rpow (P : ParamsQ) (hQ : 0 < P.Q) :
    P.zoneY = P.Q ^ ((1 : ℝ) - P.deltaPrime) := by
  rw [ParamsQ.zoneY, ParamsQ.s0, Real.rpow_def_of_pos hQ]
  congr 1
  ring

/-- The design value `K = 3` instance of `rpow_neg_zoneEdge`:
`Q^{−δ′} = (log Q)^{−3}` for `Defs.ParamsQ.deltaPrime = 3 log log Q / log Q`.
Since `3 ≥ 2`, the calibration `K ≥ 2` of Lemma 5.3 is met with margin — "the design adopts
K = 3, a conservative choice, not a forced one".

Paper §2.2 (`δ′ := 3 log log Q/log Q`) / §5.
Derivation: `LEMMA_Q5` §Q5.iv with the R4/R5 banners (K = 3 final).
Depends on: `rpow_neg_zoneEdge`.
Rule 17: `0 < P.Q` and `0 < log P.Q` only. λ, X, T, D₀ absent. -/
theorem rpow_neg_deltaPrime (P : ParamsQ) (hQ : 0 < P.Q) (hlogQ : 0 < Real.log P.Q) :
    P.Q ^ (-P.deltaPrime) = (Real.log P.Q) ^ (-(3 : ℝ)) := by
  have h := rpow_neg_zoneEdge P.Q 3 hQ hlogQ
  rw [ParamsQ.deltaPrime]
  exact h

end ZetaQ
