/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Sieve.lean — paper §6: the sharp multiplicative large sieve (Lemma 6.1).

Imports `ZetaQ.Defs` ONLY. Lemma 6.1 is parameter-free — no `ParamsQ`, no `T`, no `λ`,
no `X` — which is why this file sits at the bottom of the import graph.

Statement source of truth: paper §6, together with its Remark declining the `q/φ(q)`
weight.

--------------------------------------------------------------------------------------
## STATUS AFTER THE GALLAGHER RETHREAD — this file is no longer on the headline route
--------------------------------------------------------------------------------------

The six headline theorems (`ZetaQ.JoinProved.*_proved'`) no longer consume anything in this
file that depends on `l2_concentration_exists`. Lemma 6.1 is now consumed at the
**Gallagher budget** `Q² + πN`, proved sorry-free in `ZetaQ/Gallagher.lean`
(`ZetaQ.Gallagher.multiplicative_large_sieve_gallagher`, from Gallagher's elementary
additive inequality `Σ|S(θ_i)|² ≤ (δ⁻¹ + πN)‖a‖²`); the interfaces `Ends.LargeSieveHyp` and
`Zones.LargeSieveFamily` and the budget `Zones.sieveBudgetQ = Q² + πX` are stated at that
budget and discharged from it. What made this possible: the coefficient of `δ⁻¹` — hence of
`Q²` — is exactly `1` in Gallagher's inequality too, and `Q²` is the ONLY term of the budget
that reaches the family constant `C = Q²/|𝔉_Q|`; the length term (`N − 1` here, `πN` there)
enters every consumer only through `budget ≤ Q²(1 + O(Q^{−δ}))` in the range `X ≤ Q^{2−δ}`.
So the sentence below "the sharp constant `N + Q² − 1` IS the family constant `C`" is right
about the `Q²` and wrong about the `N`: the length term's coefficient does not matter.

Everything below is KEPT, unchanged, as the record of the sharp statement (and of the
machine-checked refutation `sharpAdditiveLargeSieveUnrestricted_false`): the sharp
`multiplicative_large_sieve` still rests on `l2_concentration_exists`, which remains a
`sorry` — but a sorry that no headline reaches (`audit/final_axioms.lean`).

--------------------------------------------------------------------------------------
## MATERIAL FINDING — the additive engine is NOT in the tree, and has to be built here
--------------------------------------------------------------------------------------

It is natural to expect that Lemma 6.1 is a short multiplicative deduction (duality +
Gauss sums + primitive decomposition) on top of the Montgomery–Vaughan Hilbert
inequality already present in `Zeta23/MV/`. **That is not so, and the reason is that the
sharp constant `N + Q² − 1` IS the family constant `C`.** What is actually proved in
`Zeta23/MV/` is `Zeta23.MV.mvDiag_thirteen : MVDiag 13`
(`Zeta23/MV/Final.lean:27`) and `Zeta23.MV.mv_hilbert : ∃ C, 0 < C ∧ MVHilbert C` at
`C = 26` (`Zeta23/MV/Final.lean:30`) — i.e. **MV74 Theorem 2**, the *non-periodic,
per-index-weighted* ("generalised") Hilbert inequality, **at an abstract constant**. The
file's own header says so (`Zeta23/MV.lean:23–26`): "*Any absolute constant in place of
3π/2 would suffice below … the headline result only needs ∃ C, so C is kept abstract*".

The sharp large-sieve budget `N + Q² − 1` requires the **additive** large sieve at
constant exactly `N − 1 + δ⁻¹` (`sharp_additive_large_sieve` below, at `δ := Q⁻²`).
`MVDiag 13` cannot deliver that: routing through it yields an `N + 13·δ⁻¹`-shaped budget,
which multiplies the family constant `C = Q²/|𝔉_Q| → π⁴/18` (`ZetaQ.Cfam`) by ≈ 13 and
therefore changes the headline `P` of Theorem 1. A lossy additive constant is therefore not a
cosmetic loss here: it moves the headline.

Grep receipt: `large sieve`,
`largeSieve`, `Hilbert inequality`, `Montgomery`, `Vaughan`, `Beurling`, `Selberg`,
`Farey`, `cosec`, `cot` — **zero hits** across the vendored Mathlib and across `Zeta23/`.

**Consequences, recorded here so nobody re-derives them:**

1. `Zeta23/MV/` is an **architectural template, not a reusable input**. What transfers is
   the *shape* (`Adm` / `EigenBound` / duality skeleton, and the integral-comparison
   technique of `Zeta23/MV/Spacing.lean`); the numerics do not — `spacing_sq ≤ 9/δ_s`
   (`Spacing.lean:183`) and `Uform_le ≤ 73` (`Quadratic.lean:54`) are precisely the crude
   steps that produce 13. This file follows that template *stylistically* (the
   `Prop`-valued `SharpAdditiveLargeSieve` below is the `MVDiag`/`MVHilbert` pattern) and
   reuses nothing from it.
2. **The sharp additive large sieve is a from-zero build.** It is
   `sharp_additive_large_sieve` below, and it is the bulk of this file.
3. The natural itemisation is inverted: the "multiplicative deduction" is the half
   Mathlib largely already has (`gaussSum_mulShift_of_isPrimitive`,
   `DirichletCharacter.sum_char_inv_mul_char_eq`), and the additive engine one expects to
   find in the tree is the half that is missing entirely.
4. Two candidate routes for the additive step, **both from zero**, both named at
   `sharp_additive_large_sieve`'s docstring: (a) Beurling–Selberg extremal majorant +
   Poisson summation (IK Thm 7.7) — *recommended*, sharp by construction; (b) re-run the
   `Zeta23/MV/` architecture for the periodic/cosecant kernel at constant 1 instead of 13
   (`periodic_hilbert_sharp` below is that route's anchor, OPTIONAL). Mathlib has no
   Beurling–Selberg majorant either, so (a) buys sharpness, not reuse.

This finding does **not** affect the paper: §6 cites the literature ([Ga67], [MV73],
[MV74], [IK Thm 7.13], [Va Thm 4], [PT25 (1.1)]), not the tree.

--------------------------------------------------------------------------------------
## `SharpAdditiveLargeSieve` WAS FALSE AS FIRST ENCODED, and the repair
--------------------------------------------------------------------------------------

As first frozen, `SharpAdditiveLargeSieve` quantified over all `δ > 0`, but its separation
hypothesis is vacuous on a one-point index set, and `N − 1 + δ⁻¹ < N` once `δ > 1`. The
disproof survives as `ZetaQ.sharpAdditiveLargeSieveUnrestricted_false` (refuting the
`…Unrestricted` copy of the old shape) and is machine-checked and `sorry`-free. Only the
ENCODING was wrong — the mathematics of §6 is untouched, and adding `δ ≤ 1` (which is
where Poisson summation needs it, and which every consumer already has, since
`farey_spaced` supplies `δ = Q⁻²`) restores exactly [IK, Thm 7.7] / [Va, Thm 3].

`δ ≤ 1` is now folded into `SharpAdditiveLargeSieve`, so that statement and
`SharpAdditiveLargeSieveOfLeOne` are the same proposition and
`sharp_additive_large_sieve` is proved — it is `sharp_additive_large_sieve_of_le_one`. To
make that citation legal the declaration was **moved** (statement, name and docstring
unchanged) from §1 down to immediately after its proof source, since Lean has no forward
references. Its `sorry` debt is now exactly `l2_concentration_exists` (the debt of the SHARP
chain only — see the status block above: no headline consumes it any more). The `…OfLeOne`
duplicate and `SharpAdditiveLargeSieve.toLeOne` are deprecated aliases and may be deleted
by the owner of the freeze.

Route (a) is built in §1.1: `SelbergMajorant` is the Beurling–Selberg
majorant as a five-field interface, and `dual_of_majorant` / `additive_of_majorant` /
`sharp_additive_large_sieve_of_le_one` are PROVED from it. **The single remaining
from-zero gap in the whole of Lemma 6.1 is the existence of that majorant** —
parameter-free real/Fourier analysis, no number theory in it.

That gap is now partly closed. `selberg_majorant_exists` itself is proved, by
splitting on `δ`: the regime `1/2 ≤ δ ≤ 1` is discharged unconditionally and elementarily
(`selberg_majorant_of_half_le` — there the extremal `F` is *finitely supported*, because
`vanishing` is vacuous above `1/2` and tests the single point `α ≡ 1/2` at `1/2`), and only
`selberg_majorant_of_lt_half` (`0 < δ < 1/2`) is left. Its docstring records the reduction
of that residue to an `L²` concentration problem on an interval of length `δ`, which
removes entire functions, Paley–Wiener and Poisson summation from the required toolkit.

That reduction is now machine-checked in both halves (`selbergMajorant_of_concentration`),
so **the ONE remaining from-zero gap of Lemma 6.1 is `l2_concentration_exists`** — a
statement of pure `L²` analysis mentioning no majorant, no exponential sum and no circle.
It is proved for
  * the whole band `(N − 1)δ ≤ 1`, at every bandwidth, with an explicit two-modulation
    witness (`l2_concentration_of_band_le_one`, hence `selbergMajorant_of_band_le_one` at
    unbounded `N`) — this subsumes the earlier small-band lemma `(N − 1)δ ≤ 1/2`
    (`l2_concentration_of_small_band`) and the earlier `N ≤ 1` lemma; and
  * the whole bandwidth `δ = 1`, at every `N`, hence with the band UNBOUNDED, by the
    orthonormal witness `Σ_{n≤N} e(nt)` (`l2_concentration_of_delta_one`, hence
    `selbergMajorant_of_delta_one`), where Parseval is exact and the budget provably tight.
The residue is therefore exactly `δ < 1` together with `(N − 1)δ > 1`, and
`l2_concentration_exists`'s docstring shows that this corner is genuinely Selberg's extremal
problem — Beurling's function, Selberg's shift, Krein/Fejér–Riesz and Paley–Wiener, none of
them in Mathlib. It also records why the elementary equal-moduli family stops at
`(N − 1)δ = 1` and why the linear chirp cannot replace Selberg.

Two further sorry-free theorems settle *why* the residue resists:
`l2_concentration_mass_ge` and `l2_concentration_no_cheaper` show, by Parseval along one
residue class of the sublattice `1 + qℤ`, that at `(N, δ) = (qm + 1, q⁻¹)` the budget
`N − 1 + δ⁻¹` is **attained with equality** — the mass is forced, not merely available. Those
points are interior to the residue for `q, m ≥ 2` (e.g. `(5, 1/2)`, `(7, 1/3)`, `(11, 1/5)`),
so any putative band anchor `(N−1)δ ≤ c` with `c ≥ 2` must produce an *exactly* extremal
witness — and for `1 < c < 2` an asymptotically extremal one, by the continuum limit `δ → 0` at
fixed `(N−1)δ`. So the band `L ≤ 1` is the end of every elementary method, and
what remains really is Selberg's function. The same docstring records that the relaxation the
`SelbergMajorant` interface would allow (`F ≥ 0` rather than `F = |ψ̂|²`, i.e. a positive
operator of any rank in place of a rank-one one) is numerically *exactly as expensive*, so
`selbergMajorant_of_concentration` loses nothing; and that only the `δ < 1/2` part of
`l2_concentration_exists` is load-bearing, since `selberg_majorant_exists` already covers
`δ ≥ 1/2` unconditionally.

--------------------------------------------------------------------------------------
## The weight, declined on the record
--------------------------------------------------------------------------------------

Paper §6's Remark declines the sharp *weighted* form
`Σ_{q≤Q}(q/φ(q))Σ*_χ|·|² ≤ (N + Q²)Σ|a_n|²` **deliberately**: adopting it would move the
family constant from `C = π⁴/18` (`ZetaQ.Cfam`) to `C_w ≈ 4.174` and move the headline.
**Nothing in this file may be strengthened to the weighted form**, and the weighted
statement is deliberately NOT declared here. The
factor `φ(q)/q` produced by `primitive_decomposition` below is exactly the reciprocal of
that weight; dropping it via `φ(q)/q ≤ 1` inside `multiplicative_large_sieve_of_additive`
IS the declension.

--------------------------------------------------------------------------------------
## RULE 17 — CLEAN, and structurally so
--------------------------------------------------------------------------------------

No declaration in this file mentions `ParamsQ`, `T`, `λ`, `X` or `D₀` at all. In
particular `N` and `Q` are **independent naturals with no relating hypothesis** — there is
no `N ≤ Q²` anywhere. This is load-bearing: the consumers instantiate `N := ⌊X⌋₊` with
`X = (QT/2π)^λ` at `λ* = 1.2507321515 > 1` (`ZetaQ.lamStar`), and the paper's own
`X ≤ Q^{2−δ}` is a *consequence at the design point*, never a hypothesis of Lemma 6.1. Lemma 6.1 being parameter-free is the *reason* the design
may run λ > 1.

--------------------------------------------------------------------------------------
## LOCAL OBJECTS
--------------------------------------------------------------------------------------

`e`, `expSum`, `sieveBudget`, `charSum`, `l2sq`, `familyQ`, `familyDyadic` are defined
locally in §0 below rather than in the frozen `ZetaQ/Defs.lean`; no other file in the
library redefines them.
-/
import ZetaQ.Defs

noncomputable section

open scoped BigOperators

namespace ZetaQ

/-! ## 0. Local objects

`ZetaQ/Defs.lean` already owns `primitiveChars`, `phiStar`, `famCard`, `famCardDyadic`,
`parity`, `Cfam`, `CfamDyadic`, `CfamEvenDyadic`; the objects below are the ones it does
not have. All have real bodies; none is a `sorry`.

Encoding conventions in force here: the index set for `n` is `Finset.Ioc 0 N` (that is
[R]'s own convention for "n ≤ X", `Zeta23/ThmE/Hypotheses.lean:55`) and the `ℓ²` norm on
the right runs over the **same** index set; `N : ℕ`; `Q : ℕ`; the coefficients are
`ℂ`-valued and total on `ℕ`; no shifted range `Σ_{M<n≤M+N}` is needed (Lemma 4.4's split
zero-pads rather than shifts). -/

/-- `e(x) := exp(2πix)` — the additive character. Used by the additive engine and by the
Farey exponential sums of `primitive_decomposition`. The bridge to Mathlib's Gauss-sum
machinery is `stdAddChar_eq_e` below. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

/-- `S(θ) := Σ_{n ≤ N} a_n e(nθ)` — the additive (exponential) sum. -/
def expSum (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, a n * e ((n : ℝ) * θ)

/-- `S_χ := Σ_{n ≤ N} a_n χ(n)` — the multiplicative (character) sum, `q` the modulus. -/
def charSum (q N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, a n * χ (n : ZMod q)

/-- `‖a‖₂² := Σ_{n ≤ N} |a_n|²`, over the SAME index set as the character sum (R2). -/
def l2sq (N : ℕ) (a : ℕ → ℂ) : ℝ := ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2

/-- `N + Q² − 1` — the sieve budget of Lemma 6.1. **The object whose sharpness is
load-bearing**: `C = Q²/|𝔉_Q| → π⁴/18` (`ZetaQ.Cfam`) is literally this `Q²` divided by
the family count, so any inflation of the constant inflates `C` and moves Theorem 1's `P`.

Rule 17: `N` and `Q` are independent arguments and there is deliberately no side
condition relating them. -/
def sieveBudget (N Q : ℕ) : ℝ := (N : ℝ) + (Q : ℝ) ^ 2 - 1

/-- `𝔉_Q` — the family of paper §1.1, as a `Finset` of dependent pairs `(q, χ)` with `χ`
primitive mod `q` and `1 ≤ q ≤ Q`. Its cardinality is `ZetaQ.famCard Q`. -/
def familyQ (Q : ℕ) : Finset ((q : ℕ) × DirichletCharacter ℂ q) :=
  (Finset.Icc 1 Q).sigma primitiveChars

/-- The dyadic subfamily `q ∈ (Q/2, Q]` of Corollary 2. Cardinality `ZetaQ.famCardDyadic Q`.
Note the natural division `Q / 2` — matching `famCardDyadic` in the frozen Defs exactly. -/
def familyDyadic (Q : ℕ) : Finset ((q : ℕ) × DirichletCharacter ℂ q) :=
  (Finset.Ioc (Q / 2) Q).sigma primitiveChars

/-- The reduced residues mod `q`, as a `Finset ℕ` — the Farey numerators at denominator `q`.
Classical decidability, deliberately: `Nat.Coprime` decidability at this Mathlib pin was
not verified, and an unverified instance is not worth reaching for here.
Same device as `ZetaQ.primitiveChars` in the frozen Defs. -/
def reducedResidues (q : ℕ) : Finset ℕ :=
  letI := Classical.decPred (fun b : ℕ => Nat.Coprime b q)
  (Finset.range q).filter (fun b => Nat.Coprime b q)

/-- The units of `ZMod q`, as a `Finset (ZMod q)`. Classical decidability for the same
reason as `reducedResidues`: no `DecidablePred (IsUnit : ZMod q → Prop)` was verified. -/
def unitResidues (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  letI := Classical.decPred (fun b : ZMod q => IsUnit b)
  Finset.univ.filter (fun b : ZMod q => IsUnit b)

/-- Helper: membership in the frozen `ZetaQ.primitiveChars`, with the classical instance
discharged. -/
theorem mem_primitiveChars {q : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ primitiveChars q ↔ χ.IsPrimitive := by
  classical
  simp [primitiveChars]

/-- Helper: membership in `unitResidues`, with the classical instance discharged. -/
theorem mem_unitResidues {q : ℕ} [NeZero q] {b : ZMod q} :
    b ∈ unitResidues q ↔ IsUnit b := by
  classical
  simp [unitResidues]

/-- Helper: membership in `reducedResidues`, with the classical instance discharged. -/
theorem mem_reducedResidues {q b : ℕ} :
    b ∈ reducedResidues q ↔ b < q ∧ Nat.Coprime b q := by
  classical
  simp [reducedResidues]

/-! ### Elementary facts about `ZetaQ.e`. -/

/-- `|e(x)| = 1`. -/
theorem norm_e (u : ℝ) : ‖e u‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))
      = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e, h, Complex.norm_exp]
  simp

/-- `e(u + v) = e(u)·e(v)`. -/
theorem e_add (u v : ℝ) : e (u + v) = e u * e v := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast; ring

@[simp] theorem e_zero : e 0 = 1 := by simp [e]

/-- `conj e(u) = e(−u)`. -/
theorem conj_e (u : ℝ) : (starRingEnd ℂ) (e u) = e (-u) := by
  have h : ∀ y : ℝ, (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ))
      = ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by intro y; push_cast; ring
  rw [e, e, h, h, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast; ring

/-- Helper: a Dirichlet character has unimodular values at units. -/
theorem norm_char_apply_of_isUnit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ZMod q} (hx : IsUnit x) : ‖χ x‖ = 1 := by
  have h : ((‖χ x‖ : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← Complex.mul_conj', starRingEnd_apply, MulChar.star_apply', ← MulChar.mul_apply,
      mul_inv_cancel, MulChar.one_apply hx]
  have h2 : ‖χ x‖ ^ 2 = 1 := by exact_mod_cast h
  nlinarith [norm_nonneg (χ x)]

/-- Helper: the `Finset`-sigma face of the `Σ_{q≤Q} Σ*_χ` double sum. Identical to
`sum_familyQ` in §5.1, declared here so that the §5 assembly theorems (which precede §5.1
in the frozen file order) can cite it. -/
theorem sum_familyQ_aux (Q : ℕ) (F : ((q : ℕ) × DirichletCharacter ℂ q) → ℝ) :
    ∑ x ∈ familyQ Q, F x = ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, F ⟨q, χ⟩ :=
  Finset.sum_sigma _ _ _

/-! ## 1. The additive engine — THE GAP

Step (I1), and the single from-zero build of this file. It is
stated in the `Prop`-valued style of [R]'s `Zeta23.MVDiag` (`Zeta23/MV.lean:52`) and
`Zeta23.MVHilbert` (`Zeta23/Hypotheses.lean:107`) — *stylistically only*: see the module
header, nothing in `Zeta23/MV/` is consumed here. -/

/-- **Sharp additive large sieve, as a `Prop`** — `δ`-separated points mod 1, constant
exactly `N − 1 + δ⁻¹`.

`Σ_i |Σ_{n ≤ N} a_n e(nθ_i)|² ≤ (N − 1 + δ⁻¹)·Σ_{n ≤ N} |a_n|²`.

Encoding (R10): separation is `∀ m : ℤ, δ ≤ |θ i − θ j − m|` rather than an `AddCircle`
norm — instance-free, and it makes the Farey instantiation (`farey_spaced`) a bare
inequality on `ℝ`. The index type is `Type` (not `Type*`), matching `MVDiag`'s binder
shape; every consumer's index type lives in `Type 0`.

**The constant is the whole point.** `C·(N + δ⁻¹)` for any `C > 1` is USELESS here: at
`δ := Q⁻²` it inflates `ZetaQ.Cfam` by `C` and moves Theorem 1's `P`. -/
def SharpAdditiveLargeSieve : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ℕ) (a : ℕ → ℂ) (θ : ι → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 →
    (∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) →
    ∑ i, ‖expSum N a (θ i)‖ ^ 2 ≤ ((N : ℝ) - 1 + δ⁻¹) * l2sq N a

/-- The large sieve WITHOUT the side condition `δ ≤ 1` — i.e. the shape this file first
froze. Retained only so that `sharpAdditiveLargeSieveUnrestricted_false` below can refute
it; nothing cites it. -/
def SharpAdditiveLargeSieveUnrestricted : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ℕ) (a : ℕ → ℂ) (θ : ι → ℝ) (δ : ℝ), 0 < δ →
    (∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) →
    ∑ i, ‖expSum N a (θ i)‖ ^ 2 ≤ ((N : ℝ) - 1 + δ⁻¹) * l2sq N a

/-- **Why `SharpAdditiveLargeSieve` carries `δ ≤ 1`: without it the statement is FALSE.**

Machine-checked. With a one-point index set the separation hypothesis is vacuous, so `δ` is
unconstrained; at `δ = 2`, `N = 1` the claimed budget `N − 1 + δ⁻¹ = 1/2` is beaten by the
trivial coefficient vector, whose left side is `1`.

This file originally froze the unrestricted form, and the refutation is here. The
side condition has since been folded into `SharpAdditiveLargeSieve` itself,
which restores [IK, Thm 7.7] / [Va, Thm 3] verbatim — and `δ ≤ 1` is exactly what the
Poisson-summation step needs, since it makes `0` the only integer in `[−δ, δ]`. The
refutation is kept as the record of why the hypothesis is not optional. It is `sorry`-free. -/
theorem sharpAdditiveLargeSieveUnrestricted_false :
    ¬ SharpAdditiveLargeSieveUnrestricted := by
  intro h
  have key := h Unit 1 (fun _ => 1) (fun _ => 0) 2 (by norm_num)
    (by rintro ⟨⟩ ⟨⟩ hij; exact absurd rfl hij)
  rw [show l2sq 1 (fun _ => (1:ℂ)) = 1 by simp [l2sq]] at key
  rw [show (∑ _i : Unit, ‖expSum 1 (fun _ => (1:ℂ)) 0‖ ^ 2) = 1 by
        simp [expSum, e]] at key
  norm_num at key

/-- **The corrected sharp additive large sieve** — `SharpAdditiveLargeSieve` with the
missing side condition `δ ≤ 1` restored. This is [IK, Thm 7.7] / [Va, Thm 3] verbatim,
and it is what every consumer in this file actually needs (`farey_spaced` supplies
`δ = Q⁻²`, and `Q ≥ 1` on the nonempty range).

Everything else — index type in `Type 0`, the instance-free separation encoding (R10),
and above all **the constant `N − 1 + δ⁻¹`** — is unchanged from the frozen statement.
`C·(N + δ⁻¹)` for any `C > 1` remains useless here. -/
@[deprecated SharpAdditiveLargeSieve (since := "2026-08-19")]
abbrev SharpAdditiveLargeSieveOfLeOne : Prop := SharpAdditiveLargeSieve

/-- The frozen statement implies the corrected one (it is strictly stronger — indeed too
strong to be true). Kept so that `multiplicative_large_sieve_of_additive`, whose signature
is frozen at `SharpAdditiveLargeSieve`, still goes through. -/
@[deprecated SharpAdditiveLargeSieve (since := "2026-08-19")]
theorem SharpAdditiveLargeSieve.toLeOne (h : SharpAdditiveLargeSieve) :
    SharpAdditiveLargeSieve := h

/-! ### 1.1 Route (a): the Beurling–Selberg majorant

Everything below `selberg_majorant_exists` is PROVED. **The whole from-zero content of
Lemma 6.1 is the existence of the majorant**, and it is a statement of pure real/Fourier
analysis with no number theory and no parameters in it.

The section is now in three parts: §1.1.a proves the majorant outright for `1/2 ≤ δ ≤ 1`
(finitely supported, no analysis); §1.1.b isolates the residue `0 < δ < 1/2` as
`selberg_majorant_of_lt_half` and records its reduction to an `L²` concentration problem;
`selberg_majorant_exists` is the case split of the two.

Reconnaissance at pin `51e6992efd06126df61a496bebf8f49482a4e129` (here): Mathlib
has Poisson summation (`Real.tsum_eq_tsum_fourier_of_rpow_decay`,
`SchwartzMap.tsum_eq_tsum_fourier`, `Mathlib/Analysis/Fourier/PoissonSummation.lean`) but
**no** Beurling–Selberg majorant, **no** Fejér kernel, and no large sieve of any kind —
`Beurling`, `large sieve`, `Fejér`, `band-limited`, `Farey`, `cosec` all return zero hits.
(`Mathlib/NumberTheory/SelbergSieve.lean` is the combinatorial Selberg sieve, unrelated.)
-/

/-- **The Beurling–Selberg majorant of the indicator of `(0, N]`, as an interface.**

`F` is the *restriction to the integers* of Selberg's entire majorant of exponential type
`2πδ`; the fields are exactly the properties the large sieve consumes, with Poisson
summation already applied. Concretely, if `f : ℝ → ℝ` is entire of exponential type `2πδ`
with `f ≥ 𝟙_{[1,N]}`, `f ≥ 0` and `∫f = N − 1 + δ⁻¹`, then `F := f ∘ (↑·)` satisfies all
five fields: `total` and `vanishing` are Poisson summation
`Σ_{n∈ℤ} F(n)e(nα) = Σ_{m∈ℤ} f̂(m − α)` at `α = 0` and at `α` `δ`-far from `ℤ`
respectively, using `supp f̂ ⊆ [−δ, δ]` — and `total` is where `δ ≤ 1` is needed, since it
is what makes `0` the only integer in `[−δ, δ]`.

Fields:
* `nonneg`, `majorizes` — it dominates the indicator of `(0, N]` at the integers;
* `summable` — absolute convergence of `Σ_{n∈ℤ} F(n)`;
* `total` — **the sharp constant**, `Σ_{n∈ℤ} F(n) = N − 1 + δ⁻¹`;
* `vanishing` — band-limitedness, in the only form the sieve uses. -/
structure SelbergMajorant (N : ℕ) (δ : ℝ) : Type where
  /-- the majorant, sampled at the integers -/
  F : ℤ → ℝ
  /-- (M1) `F ≥ 0` -/
  nonneg : ∀ n : ℤ, 0 ≤ F n
  /-- (M2) `F` majorises the indicator of `(0, N]` at the integers -/
  majorizes : ∀ n : ℤ, 0 < n → n ≤ (N : ℤ) → 1 ≤ F n
  /-- (M3) `Σ_{n∈ℤ} F(n)` converges absolutely -/
  summable : Summable F
  /-- (M4) **the sharp total mass** — Poisson summation at `α = 0` (uses `δ ≤ 1`) -/
  total : ∑' n : ℤ, F n = (N : ℝ) - 1 + δ⁻¹
  /-- (M5) band-limitedness — Poisson summation at `α` further than `δ` from every integer -/
  vanishing : ∀ α : ℝ, (∀ m : ℤ, δ ≤ |α - (m : ℝ)|) →
    ∑' n : ℤ, (F n : ℂ) * e ((n : ℝ) * α) = 0

/-! #### 1.1.a The regime `1/2 ≤ δ ≤ 1` — no analysis needed

`vanishing` constrains `α` only where `dist(α, ℤ) ≥ δ`. Every real is within `1/2` of an
integer, so that set is **empty** when `δ > 1/2` and is exactly `ℤ + 1/2` when `δ = 1/2`.
Consequently on `[1/2, 1]` the majorant may be taken **finitely supported**:

  `F := 𝟙_{(0,N]} + c·(δ₀ + δ_{N+1})`,   `c := (δ⁻¹ − 1)/2 ≥ 0`  (here `δ ≤ 1` is used),

whose total mass is `N + 2c = N − 1 + δ⁻¹` by construction. At `δ = 1/2` one has `c = 1/2`,
i.e. `F = ½(𝟙_{[0,N]} + 𝟙_{[1,N+1]})`, and `Σ_n F(n)(−1)ⁿ = 0` because the alternating sums
of the two blocks of consecutive integers cancel. No Fourier analysis is involved.

The three helper lemmas below (`e_intCast`, `e_intCast_div_two`, `alternating_sum_Ioc`) are
what turns `vanishing` at `α ∈ ℤ + 1/2` into that finite alternating sum. -/

/-- `e` is `1` at every integer — `e(k) = exp(2πik) = 1`. -/
theorem e_intCast (k : ℤ) : e (k : ℝ) = 1 := by
  rw [e, show (2 * (Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- `e(n/2) = (−1)ⁿ` — the only value of `e` the `δ = 1/2` case of `vanishing` ever sees. -/
theorem e_intCast_div_two (n : ℤ) : e ((n : ℝ) / 2) = (-1 : ℂ) ^ n := by
  rw [e, show (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) / 2 : ℝ) : ℂ))
      = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- `Σ_{0 < n ≤ M} (−1)ⁿ = ((−1)^M − 1)/2`, over the integer interval `Ioc 0 M`. -/
theorem alternating_sum_Ioc (M : ℕ) :
    ∑ n ∈ Finset.Ioc (0 : ℤ) (M : ℤ), (-1 : ℂ) ^ n = ((-1 : ℂ) ^ (M : ℤ) - 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hins : Finset.Ioc (0 : ℤ) ((M : ℤ) + 1)
        = insert ((M : ℤ) + 1) (Finset.Ioc (0 : ℤ) (M : ℤ)) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnot : ((M : ℤ) + 1) ∉ Finset.Ioc (0 : ℤ) (M : ℤ) := by
      simp only [Finset.mem_Ioc]
      omega
    push_cast
    rw [hins, Finset.sum_insert hnot, ih, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    ring

/-- The indicator of `(0, N]` inside `[0, N+1]`: a weighted sum over `Icc 0 (N+1)` whose
summand is cut off outside `(0, N]` is a sum over `Ioc 0 N`. Used for both the real
(`total`) and the complex (`vanishing`) computation. -/
theorem sum_ite_Ioc {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℤ → M) :
    ∑ n ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1), (if 0 < n ∧ n ≤ (N : ℤ) then g n else 0)
      = ∑ n ∈ Finset.Ioc (0 : ℤ) (N : ℤ), g n := by
  have hsub : Finset.Ioc (0 : ℤ) (N : ℤ) ⊆ Finset.Icc (0 : ℤ) ((N : ℤ) + 1) := by
    intro x hx
    simp only [Finset.mem_Ioc] at hx
    simp only [Finset.mem_Icc]
    omega
  rw [← Finset.sum_subset hsub
    (fun x _ hnx => if_neg fun hcc => hnx (Finset.mem_Ioc.mpr hcc))]
  exact Finset.sum_congr rfl fun x hx => if_pos (Finset.mem_Ioc.mp hx)

/-- **The Beurling–Selberg majorant at bandwidth `1/2 ≤ δ ≤ 1`, unconditionally.**

At these bandwidths the extremal function is *finitely supported* — `𝟙_{(0,N]}` plus mass
`(δ⁻¹ − 1)/2` at each of `0` and `N+1` — because `vanishing` is vacuous for `δ > 1/2` and
only tests the single point `α ≡ 1/2 (mod 1)` at `δ = 1/2`. `δ ≤ 1` is exactly what makes
the extra mass nonnegative, which is the same place the general construction needs it.

Fully proved; no Fourier analysis, no Poisson summation. -/
theorem selberg_majorant_of_half_le (N : ℕ) {δ : ℝ} (hδ : 1 / 2 ≤ δ) (hδ1 : δ ≤ 1) :
    Nonempty (SelbergMajorant N δ) := by
  have hδ0 : (0 : ℝ) < δ := lt_of_lt_of_le (by norm_num) hδ
  have hinv : (1 : ℝ) ≤ δ⁻¹ := by
    have h1 : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ0.ne'
    have h2 : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ0
    nlinarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (δ⁻¹ - 1) / 2 := ⟨_, rfl⟩
  have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; linarith
  obtain ⟨F, hFdef⟩ : ∃ F : ℤ → ℝ, F = fun n : ℤ =>
      (if 0 < n ∧ n ≤ (N : ℤ) then (1 : ℝ) else 0) + (if n = 0 then c else 0)
        + (if n = (N : ℤ) + 1 then c else 0) := ⟨_, rfl⟩
  have h0s : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hNs : ((N : ℤ) + 1) ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hsupp : ∀ n ∉ Finset.Icc (0 : ℤ) ((N : ℤ) + 1), F n = 0 := by
    intro n hn
    have h : ¬ (0 ≤ n ∧ n ≤ (N : ℤ) + 1) := fun hh => hn (Finset.mem_Icc.mpr hh)
    simp only [hFdef]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  have hcard : ∑ _n ∈ Finset.Ioc (0 : ℤ) (N : ℤ), (1 : ℝ) = (N : ℝ) := by
    simp [Finset.sum_const, Int.card_Ioc]
  have htotal : ∑ n ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1), F n = (N : ℝ) - 1 + δ⁻¹ := by
    have e1 : ∑ n ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1), F n
        = (∑ n ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1),
              (if 0 < n ∧ n ≤ (N : ℤ) then (1 : ℝ) else 0))
          + (∑ n ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1), (if n = 0 then c else 0))
          + (∑ n ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1), (if n = (N : ℤ) + 1 then c else 0)) := by
      simp only [hFdef]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [e1, sum_ite_Ioc N (fun _ => (1 : ℝ)), hcard,
      Finset.sum_ite_eq' (Finset.Icc (0 : ℤ) ((N : ℤ) + 1)) (0 : ℤ) (fun _ => c), if_pos h0s,
      Finset.sum_ite_eq' (Finset.Icc (0 : ℤ) ((N : ℤ) + 1)) ((N : ℤ) + 1) (fun _ => c),
      if_pos hNs, hcdef]
    ring
  have hvanish : ∀ α : ℝ, (∀ m : ℤ, δ ≤ |α - (m : ℝ)|) →
      ∑' n : ℤ, (F n : ℂ) * e ((n : ℝ) * α) = 0 := by
    intro α hα
    have hfl : ((⌊α⌋ : ℤ) : ℝ) ≤ α := Int.floor_le α
    have hfl2 : α < ((⌊α⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one α
    have h1 := hα ⌊α⌋
    have h2 := hα (⌊α⌋ + 1)
    push_cast at h2
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ α - ((⌊α⌋ : ℤ) : ℝ))] at h1
    rw [abs_of_nonpos (by linarith : α - (((⌊α⌋ : ℤ) : ℝ) + 1) ≤ 0)] at h2
    obtain ⟨k, hk⟩ : ∃ k : ℤ, α = (k : ℝ) + 1 / 2 := ⟨⌊α⌋, by linarith⟩
    have hc2 : c = 1 / 2 := by
      have hδhalf : δ = 1 / 2 := by linarith
      rw [hcdef, hδhalf]; norm_num
    have he : ∀ n : ℤ, e ((n : ℝ) * α) = (-1 : ℂ) ^ n := by
      intro n
      rw [show (n : ℝ) * α = ((n * k : ℤ) : ℝ) + (n : ℝ) / 2 by
            rw [hk]; push_cast; ring,
        e_add, e_intCast, one_mul, e_intCast_div_two]
    have hsupp' : ∀ n ∉ Finset.Icc (0 : ℤ) ((N : ℤ) + 1),
        (F n : ℂ) * e ((n : ℝ) * α) = 0 := by
      intro n hn
      rw [hsupp n hn]
      simp
    have e2 : ∀ n : ℤ, (F n : ℂ) * e ((n : ℝ) * α)
        = (if 0 < n ∧ n ≤ (N : ℤ) then (-1 : ℂ) ^ n else 0)
          + (if n = 0 then (c : ℂ) * (-1 : ℂ) ^ n else 0)
          + (if n = (N : ℤ) + 1 then (c : ℂ) * (-1 : ℂ) ^ n else 0) := by
      intro n
      rw [he n]
      simp only [hFdef]
      split_ifs <;> push_cast <;> ring
    rw [tsum_eq_sum hsupp', Finset.sum_congr rfl (fun n _ => e2 n),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_ite_Ioc N (fun n : ℤ => (-1 : ℂ) ^ n),
      Finset.sum_ite_eq' (Finset.Icc (0 : ℤ) ((N : ℤ) + 1)) (0 : ℤ)
        (fun n : ℤ => (c : ℂ) * (-1 : ℂ) ^ n), if_pos h0s,
      Finset.sum_ite_eq' (Finset.Icc (0 : ℤ) ((N : ℤ) + 1)) ((N : ℤ) + 1)
        (fun n : ℤ => (c : ℂ) * (-1 : ℂ) ^ n), if_pos hNs,
      alternating_sum_Ioc N, hc2, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_zero]
    push_cast
    ring
  refine ⟨⟨F, ?_, ?_, summable_of_ne_finset_zero hsupp, ?_, hvanish⟩⟩
  · intro n
    simp only [hFdef]
    split_ifs <;> linarith
  · intro n hn1 hn2
    simp only [hFdef]
    rw [if_pos (⟨hn1, hn2⟩ : 0 < n ∧ n ≤ (N : ℤ))]
    split_ifs <;> linarith
  · rw [tsum_eq_sum hsupp, htotal]

/-! #### 1.1.b The residual regime `0 < δ < 1/2` — and its reformulation

Below `1/2` the constraint set `{α : dist(α, ℤ) ≥ δ}` has positive measure, so
`Σ_n F(n)e(nα)` — a *continuous* function of `α` once `F` is summable — must vanish on a
set of positive measure. A finitely supported `F` would make it a trigonometric polynomial,
which then vanishes identically; so `F` is necessarily of infinite support and the finite
construction of §1.1.a cannot be pushed. This is where the genuine analysis lives. -/

/-! ##### The Fourier glue — PROVED: `L²` concentration ⟹ the five fields

`selbergMajorant_of_concentration` below is the whole of the reduction recorded in
`selberg_majorant_of_lt_half`'s docstring, machine-checked. It takes ONE function
`ψ ∈ L²(ℝ)` supported in `(0, δ]` and manufactures the `SelbergMajorant` interface from it,
so the only thing left in the whole of Lemma 6.1 is to *write down* that `ψ`
(`l2_concentration_exists`). No entire functions, no Poisson summation, no Paley–Wiener.

Three auxiliaries, all sorry-free:
* `intervalIntegral_eq_of_support` — moving the interval of integration of a function that
  vanishes off `(s₀, s₁]`. This is what replaces every periodisation argument: it lets the
  translate of `ψ` be integrated over `[0,1]` and over `[−β, 1−β]` interchangeably.
* `fourierCoeffOn_eq_e` — Mathlib's `fourierCoeffOn (0 < 1)` **is** `∫₀¹ ψ(t)·e(−nt) dt` in
  this file's own `ZetaQ.e`. After this lemma the circle `ℝ/ℤ` is never mentioned again.
* `tsum_conj_mul_fourierCoeffOn` — the **sesquilinear** Parseval identity
  `Σ_n conj(f̂ n)·ĝ n = (b−a)⁻¹·∫_a^b conj(f)·g`. Mathlib has only the diagonal case
  (`tsum_sq_fourierCoeffOn`); the polarised form is read off `fourierBasis` together with
  `HilbertBasis.tsum_inner_mul_inner`. **This is the lemma that converts band-limitedness
  into disjointness of supports**, and it is the only genuinely new Fourier content here.
-/

section Concentration

open MeasureTheory

/-- Moving the interval of integration across a function that vanishes off `(s₀, s₁]`: if
`(s₀, s₁] ⊆ (u, v]` then the two interval integrals agree. Used twice — once to see the
`[0,1]` Fourier coefficient of `ψ` as an integral over `[0, δ]`, and once to undo the
translation `t ↦ t − β` in the `vanishing` computation. -/
theorem intervalIntegral_eq_of_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v s₀ s₁ : ℝ} {G : ℝ → E} (huv : u ≤ v) (hs : s₀ ≤ s₁)
    (hsub : Set.Ioc s₀ s₁ ⊆ Set.Ioc u v)
    (hz : ∀ t, t ∉ Set.Ioc s₀ s₁ → G t = 0) :
    ∫ t in u..v, G t = ∫ t in s₀..s₁, G t := by
  rw [intervalIntegral.integral_of_le huv, intervalIntegral.integral_of_le hs]
  exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    measurableSet_Ioc.nullMeasurableSet hsub (Filter.Eventually.of_forall fun x hx => hz x hx.2)

/-- Mathlib's `fourierCoeffOn` on `[0,1]` is exactly `∫₀¹ ψ(t)·e(−nt) dt` in this file's
`ZetaQ.e` notation. The period is `1`, so there is no normalising factor. -/
theorem fourierCoeffOn_eq_e (h01 : (0:ℝ) < 1) (ψ : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn h01 ψ n = ∫ t in (0:ℝ)..1, ψ t * e (-((n:ℝ) * t)) := by
  rw [fourierCoeffOn_eq_integral]
  have key : ∀ x : ℝ, (fourier (-n) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • ψ x
      = ψ x * e (-((n:ℝ) * x)) := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul, e, mul_comm]
    congr 1
    push_cast
    norm_num
    congr 1
    ring
  simp only [key]
  norm_num

/-- **Sesquilinear Parseval on an interval.** Mathlib has the diagonal case only
(`tsum_sq_fourierCoeffOn`); this is the polarised form, obtained from the Hilbert basis
`fourierBasis` via `HilbertBasis.tsum_inner_mul_inner`.

It is the engine of `vanishing`: applied to `ψ` and to a translate of `ψ` whose support is
disjoint from `supp ψ`, the right-hand side is the integral of the identically-zero
function, and the left-hand side is `Σ_n |ψ̂(n)|² e(nα)`. -/
theorem tsum_conj_mul_fourierCoeffOn {a b : ℝ} {f g : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a b))) :
    ∑' i : ℤ, (starRingEnd ℂ) (fourierCoeffOn hab f i) * fourierCoeffOn hab g i
      = (b - a)⁻¹ • ∫ x in a..b, (starRingEnd ℂ) (f x) * g x := by
  have hfa : Fact (0 < b - a) := Fact.mk (by linarith)
  rw [← add_sub_cancel a b] at hf hg
  have hF := hf.memLp_liftIoc.haarAddCircle
  have hG := hg.memLp_liftIoc.haarAddCircle
  have hcF : ∀ i : ℤ, fourierCoeff (⇑hF.toLp) i = fourierCoeffOn hab f i := by
    intro i; rw [fourierCoeff_congr_ae hF.coeFn_toLp]; rfl
  have hcG : ∀ i : ℤ, fourierCoeff (⇑hG.toLp) i = fourierCoeffOn hab g i := by
    intro i; rw [fourierCoeff_congr_ae hG.coeFn_toLp]; rfl
  have key := (fourierBasis (T := b - a)).tsum_inner_mul_inner hF.toLp hG.toLp
  have hL : ∀ i : ℤ,
      (inner ℂ hF.toLp ((fourierBasis (T := b - a)) i) : ℂ)
        * (inner ℂ ((fourierBasis (T := b - a)) i) hG.toLp : ℂ)
      = (starRingEnd ℂ) (fourierCoeffOn hab f i) * fourierCoeffOn hab g i := by
    intro i
    rw [← inner_conj_symm hF.toLp ((fourierBasis (T := b - a)) i)]
    rw [← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply,
      fourierBasis_repr, fourierBasis_repr, hcF, hcG]
  rw [tsum_congr hL] at key
  rw [key, MeasureTheory.L2.inner_def]
  have hint : ∫ (t : AddCircle (b - a)), (inner ℂ (⇑hF.toLp t) (⇑hG.toLp t) : ℂ)
        ∂AddCircle.haarAddCircle
      = ∫ t : AddCircle (b - a),
          AddCircle.liftIoc (b - a) a (fun x => (starRingEnd ℂ) (f x) * g x) t
        ∂AddCircle.haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with t h1 h2
    rw [h1, h2, RCLike.inner_apply']
    rfl
  rw [hint, AddCircle.integral_haarAddCircle,
    AddCircle.integral_liftIoc_eq_intervalIntegral, add_sub_cancel]

/-- **THE FOURIER GLUE — `L²` concentration ⟹ the Beurling–Selberg majorant.** PROVED.

Given a single `ψ ∈ L²(ℝ)` supported in `(0, δ]` with
`∫₀^δ |ψ|² = N − 1 + δ⁻¹` and `|∫₀^δ ψ(t)e(−nt) dt| ≥ 1` for `1 ≤ n ≤ N`, the sequence
`F n := |ψ̂(n)|²` satisfies all five fields of `SelbergMajorant N δ`:

* `nonneg` — definitional;
* `majorizes` — the hypothesis `1 ≤ |ψ̂(n)|`, squared;
* `summable`, `total` — Parseval (`hasSum_sq_fourierCoeffOn`, `tsum_sq_fourierCoeffOn`),
  the interval being `[0,1]` so that there is no normalising factor;
* `vanishing` — `tsum_conj_mul_fourierCoeffOn` applied to `ψ` and to `χ := ψ(· − β)`,
  where `β ∈ [δ, 1 − δ]` is the fractional part of `α`. The hypothesis
  `∀ m, δ ≤ |α − m|` is used exactly twice: `δ ≤ β` puts `supp χ = (β, β+δ]` beyond
  `supp ψ = (0, δ]`, making the Parseval right-hand side the integral of `0`; and
  `β ≤ 1 − δ` keeps `supp χ` inside `[0,1]`, so the translation does not wrap.
  Band-limitedness has become disjointness of supports, as advertised.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` and `δ` are unrelated. -/
theorem selbergMajorant_of_concentration (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ψ : ℝ → ℂ} (hmem : MemLp ψ 2 volume)
    (hsupp : ∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0)
    (hnorm : (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) = (N:ℝ) - 1 + δ⁻¹)
    (hcoef : ∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
      1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖) :
    Nonempty (SelbergMajorant N δ) := by
  have h01 : (0:ℝ) < 1 := zero_lt_one
  set c : ℤ → ℂ := fun n => ∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t)) with hcdef
  have hmem1 : MemLp ψ 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := hmem.restrict _
  have hsub1 : Set.Ioc (0:ℝ) δ ⊆ Set.Ioc (0:ℝ) 1 := Set.Ioc_subset_Ioc le_rfl hδ1
  have hcoeff : ∀ n : ℤ, fourierCoeffOn h01 ψ n = c n := by
    intro n
    rw [fourierCoeffOn_eq_e]
    exact intervalIntegral_eq_of_support zero_le_one hδ.le hsub1
      (fun t ht => by rw [hsupp t ht]; ring)
  refine ⟨⟨fun n => ‖c n‖ ^ 2, fun n => sq_nonneg _, ?_, ?_, ?_, ?_⟩⟩
  · intro n hn1 hn2
    have h := hcoef n hn1 hn2
    nlinarith [norm_nonneg (c n)]
  · have hs := (hasSum_sq_fourierCoeffOn h01 hmem1).summable
    simpa only [hcoeff] using hs
  · have ht := tsum_sq_fourierCoeffOn h01 hmem1
    simp only [hcoeff] at ht
    rw [ht, intervalIntegral_eq_of_support zero_le_one hδ.le hsub1
      (fun t ht' => by rw [hsupp t ht']; simp), hnorm]
    norm_num
  · intro α hα
    set k : ℤ := ⌊α⌋ with hkdef
    set β : ℝ := α - (k : ℝ) with hβdef
    have hfl : ((k : ℤ) : ℝ) ≤ α := Int.floor_le α
    have hfl2 : α < ((k : ℤ) : ℝ) + 1 := Int.lt_floor_add_one α
    have hβ0 : 0 ≤ β := by rw [hβdef]; linarith
    have hdb : δ ≤ β := by
      have h := hα k
      rwa [abs_of_nonneg (by rw [hβdef] at hβ0; linarith : (0:ℝ) ≤ α - (k : ℝ))] at h
    have hdb2 : β ≤ 1 - δ := by
      have h := hα (k + 1)
      push_cast at h
      rw [abs_of_nonpos (by linarith : α - ((k : ℝ) + 1) ≤ 0)] at h
      rw [hβdef]; linarith
    set χ : ℝ → ℂ := fun t => ψ (t - β) with hχdef
    have hχmem : MemLp χ 2 volume :=
      hmem.comp_measurePreserving (measurePreserving_sub_right volume β)
    have hχmem1 : MemLp χ 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := hχmem.restrict _
    have hcχ : ∀ n : ℤ, fourierCoeffOn h01 χ n = e (-((n:ℝ) * β)) * c n := by
      intro n
      rw [fourierCoeffOn_eq_e]
      have hstep : ∀ t : ℝ, χ t * e (-((n:ℝ) * t))
          = e (-((n:ℝ) * β)) * ((fun x => ψ x * e (-((n:ℝ) * x))) (t - β)) := by
        intro t
        simp only [hχdef]
        rw [show -((n:ℝ) * t) = -((n:ℝ) * β) + -((n:ℝ) * (t - β)) by ring, e_add]
        ring
      rw [intervalIntegral.integral_congr (fun t _ => hstep t),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun x => ψ x * e (-((n:ℝ) * x))) β]
      congr 1
      exact intervalIntegral_eq_of_support (by linarith) hδ.le
        (Set.Ioc_subset_Ioc (by linarith) (by linarith))
        (fun t ht => by rw [hsupp t ht]; ring)
    have hpars := tsum_conj_mul_fourierCoeffOn h01 hχmem1 hmem1
    simp only [hcχ, hcoeff] at hpars
    have hzero : ∀ x : ℝ, (starRingEnd ℂ) (χ x) * ψ x = 0 := by
      intro x
      by_cases hx : x ∈ Set.Ioc (0:ℝ) δ
      · have hcz : χ x = 0 := by
          simp only [hχdef]
          refine hsupp _ (fun hm => ?_)
          have h2 := hx.2
          simp only [Set.mem_Ioc] at hm
          linarith [hm.1]
        rw [hcz]; simp
      · rw [hsupp x hx]; ring
    rw [show (∫ x in (0:ℝ)..1, (starRingEnd ℂ) (χ x) * ψ x) = 0 by
      simp only [hzero]; simp] at hpars
    have heα : ∀ n : ℤ, e ((n:ℝ) * α) = e ((n:ℝ) * β) := by
      intro n
      rw [show (n:ℝ) * α = (n:ℝ) * β + ((n * k : ℤ) : ℝ) by rw [hβdef]; push_cast; ring,
        e_add, e_intCast, mul_one]
    have hterm : ∀ n : ℤ, ((‖c n‖ ^ 2 : ℝ) : ℂ) * e ((n:ℝ) * α)
        = (starRingEnd ℂ) (e (-((n:ℝ) * β)) * c n) * c n := by
      intro n
      rw [heα n]
      push_cast
      rw [map_mul, conj_e, neg_neg, ← Complex.mul_conj']
      ring
    rw [tsum_congr hterm]
    simpa using hpars

/-- `e` is continuous — needed only to see the explicit witnesses of §1.1.b as `L²`
functions. -/
theorem continuous_e : Continuous e := by
  unfold e
  exact Complex.continuous_exp.comp (by fun_prop)

/-- **(C) at `N ≤ 1`, with the extremal `ψ` written down explicitly — PROVED.**

`ψ := r·e(N·t)·𝟙_{(0,δ]}` with `r := √((N − 1 + δ⁻¹)/δ)`. At `N = 1` this is exactly the
sharp witness recorded in `selberg_majorant_of_lt_half`'s docstring, `ψ = δ⁻¹e(t)𝟙_{(0,δ]}`
(there `r = δ⁻¹`, `ψ̂(1) = 1` — equality in Cauchy–Schwarz — and `‖ψ‖² = δ⁻¹`); at `N = 0`
the modulation is trivial and only the mass `δ⁻¹ − 1 ≥ 0` matters, which is where `δ ≤ 1`
enters.

This lemma is **not** a step towards the general case — it is the certificate that (C) is
satisfiable at all, and hence that `selbergMajorant_of_concentration` is not vacuous: via
`selbergMajorant_of_le_one` it produces honest `SelbergMajorant N δ` objects at arbitrarily
small bandwidth, sorry-free, which the finitely-supported construction of §1.1.a cannot do.
-/
theorem l2_concentration_of_le_one {N : ℕ} (hN : N ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ ψ : ℝ → ℂ, MemLp ψ 2 volume ∧ (∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0) ∧
      (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) = (N:ℝ) - 1 + δ⁻¹ ∧
      (∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
        1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖) := by
  have hδinv : (1:ℝ) ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ]; simpa using hδ1
  have hB : 0 ≤ ((N:ℝ) - 1 + δ⁻¹) / δ := by
    apply div_nonneg _ hδ.le
    have h : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    linarith
  set r : ℝ := Real.sqrt (((N:ℝ) - 1 + δ⁻¹) / δ) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = ((N:ℝ) - 1 + δ⁻¹) / δ := Real.sq_sqrt hB
  have hcont : Continuous (fun t : ℝ => (r : ℂ) * e ((N:ℝ) * t)) :=
    continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))
  refine ⟨Set.indicator (Set.Ioc (0:ℝ) δ) (fun t => (r : ℂ) * e ((N:ℝ) * t)), ?_, ?_, ?_, ?_⟩
  · refine (memLp_indicator_iff_restrict measurableSet_Ioc).mpr ?_
    refine MemLp.of_bound hcont.aestronglyMeasurable r ?_
    filter_upwards with t
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  · intro t ht
    exact Set.indicator_of_notMem ht _
  · rw [intervalIntegral.integral_of_le hδ.le,
      setIntegral_congr_fun measurableSet_Ioc
        (show Set.EqOn (fun t => ‖Set.indicator (Set.Ioc (0:ℝ) δ)
              (fun t => (r : ℂ) * e ((N:ℝ) * t)) t‖ ^ 2)
            (fun _ => r ^ 2) (Set.Ioc (0:ℝ) δ) from fun t ht => by
          simp only [Set.indicator_of_mem ht, norm_mul, norm_e, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hr0]),
      setIntegral_const, Real.volume_real_Ioc_of_le hδ.le, sub_zero, smul_eq_mul, hr2]
    field_simp
  · intro n hn1 hn2
    have hN1 : N = 1 := by omega
    have hn : n = 1 := by omega
    subst hN1
    subst hn
    have hrv : r = δ⁻¹ := by
      have h1 : ((1:ℕ):ℝ) - 1 + δ⁻¹ = δ⁻¹ := by push_cast; ring
      rw [hrdef, h1, show δ⁻¹ / δ = δ⁻¹ * δ⁻¹ by field_simp]
      exact Real.sqrt_mul_self (le_of_lt (inv_pos.mpr hδ))
    rw [intervalIntegral.integral_of_le hδ.le,
      setIntegral_congr_fun measurableSet_Ioc
        (show Set.EqOn (fun t => Set.indicator (Set.Ioc (0:ℝ) δ)
              (fun t => (r : ℂ) * e (((1:ℕ):ℝ) * t)) t * e (-(((1:ℤ):ℝ) * t)))
            (fun _ => (r : ℂ)) (Set.Ioc (0:ℝ) δ) from fun t ht => by
          simp only [Set.indicator_of_mem ht]
          push_cast
          rw [mul_assoc, ← e_add, show (1:ℝ) * t + -(1 * t) = 0 by ring, e_zero, mul_one]),
      setIntegral_const, Real.volume_real_Ioc_of_le hδ.le, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ.le, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0, hrv, mul_inv_cancel₀ hδ.ne']

/-- **Non-vacuity of the glue: the Beurling–Selberg majorant EXISTS for `N ≤ 1`, at every
bandwidth `0 < δ ≤ 1`.** Sorry-free, and — unlike §1.1.a — valid below `δ = 1/2`, where the
majorant provably cannot be finitely supported. It is `l2_concentration_of_le_one` run
through `selbergMajorant_of_concentration`. -/
theorem selbergMajorant_of_le_one {N : ℕ} (hN : N ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Nonempty (SelbergMajorant N δ) := by
  obtain ⟨ψ, hmem, hsupp, hnorm, hcoef⟩ := l2_concentration_of_le_one hN hδ hδ1
  exact selbergMajorant_of_concentration N hδ hδ1 hmem hsupp hnorm hcoef

/-! ##### Work-saver 1, now PROVED: in (C) the mass condition may be relaxed to `≤`

An **approximate** construction suffices for `l2_concentration_exists`, provided it does not
overshoot the budget. This is the first of the two remarks recorded in
`l2_concentration_exists`'s docstring, discharged so that it need not be re-derived: a
future construction only has to produce `∫₀^δ|ψ|² ≤ N − 1 + δ⁻¹`, never the exact value. -/

/-- **Work-saver 1 — the mass condition of (C) may be relaxed from `=` to `≤`.** PROVED.

If `1 ≤ N` and `ψ` is supported in `(0, δ]` with `|ψ̂(n)| ≥ 1` for `1 ≤ n ≤ N` and mass at
**most** `N − 1 + δ⁻¹`, then `l2_concentration_exists`'s conclusion holds verbatim.

The witness is `√(B/V)·ψ` with `B := N − 1 + δ⁻¹` and `V := ∫₀^δ|ψ|²`. The hypothesis
`1 ≤ N` is what makes the frequency `n = 1` available, and hence `V > 0`: if `V` vanished
then `ψ = 0` a.e. on `(0, δ]`, forcing `ψ̂(1) = 0` and contradicting `1 ≤ |ψ̂(1)|`. With
`0 < V ≤ B` the scaling factor is `≥ 1`, so it preserves every coefficient bound while
raising the mass to exactly `B`.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` and `δ` are unrelated. -/
theorem l2_concentration_of_le {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ)
    {ψ : ℝ → ℂ} (hmem : MemLp ψ 2 volume)
    (hsupp : ∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0)
    (hnorm : (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) ≤ (N:ℝ) - 1 + δ⁻¹)
    (hcoef : ∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
      1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖) :
    ∃ ψ' : ℝ → ℂ, MemLp ψ' 2 volume ∧ (∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ' t = 0) ∧
      (∫ t in (0:ℝ)..δ, ‖ψ' t‖ ^ 2) = (N:ℝ) - 1 + δ⁻¹ ∧
      (∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
        1 ≤ ‖∫ t in (0:ℝ)..δ, ψ' t * e (-((n:ℝ) * t))‖) := by
  have hN1 : (1:ℤ) ≤ (N:ℤ) := by exact_mod_cast hN
  set B : ℝ := (N:ℝ) - 1 + δ⁻¹ with hBdef
  set V : ℝ := ∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2 with hVdef
  have hsq : Integrable (fun t => ‖ψ t‖ ^ 2) volume := hmem.norm.integrable_sq
  have hVnn : 0 ≤ V := intervalIntegral.integral_nonneg hδ.le fun _ _ => sq_nonneg _
  have hV0 : 0 < V := by
    rcases hVnn.lt_or_eq with h | h
    · exact h
    exfalso
    have hz : (fun t => ‖ψ t‖ ^ 2) =ᵐ[volume.restrict (Set.Ioc (0:ℝ) δ)] 0 :=
      (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hδ.le
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hsq.intervalIntegrable).mp h.symm
    have hz' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0:ℝ) δ → ‖ψ t‖ ^ 2 = 0 :=
      (ae_restrict_iff' measurableSet_Ioc).mp hz
    have hψz : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) δ →
        ψ t * e (-(((1:ℤ):ℝ) * t)) = (fun _ : ℝ => (0:ℂ)) t := by
      filter_upwards [hz'] with t ht htm
      rw [Set.uIoc_of_le hδ.le] at htm
      have hn0 : ‖ψ t‖ = 0 := by nlinarith [norm_nonneg (ψ t), ht htm]
      rw [norm_eq_zero.mp hn0, zero_mul]
    have hzero : (∫ t in (0:ℝ)..δ, ψ t * e (-(((1:ℤ):ℝ) * t))) = 0 := by
      rw [intervalIntegral.integral_congr_ae hψz]
      simp
    have h0 := hcoef 1 le_rfl hN1
    rw [hzero, norm_zero] at h0
    linarith
  have hB0 : 0 < B := lt_of_lt_of_le hV0 hnorm
  set r : ℝ := Real.sqrt (B / V) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = B / V := Real.sq_sqrt (by positivity)
  have hr1 : (1:ℝ) ≤ r := by
    rw [hrdef, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hV0]; linarith)
  refine ⟨fun t => (r : ℂ) * ψ t, hmem.const_mul _, ?_, ?_, ?_⟩
  · intro t ht
    show (r : ℂ) * ψ t = 0
    rw [hsupp t ht, mul_zero]
  · have hpt : ∀ t : ℝ, ‖(r : ℂ) * ψ t‖ ^ 2 = r ^ 2 * ‖ψ t‖ ^ 2 := by
      intro t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, mul_pow]
    simp only [hpt]
    rw [intervalIntegral.integral_const_mul, ← hVdef, hr2, div_mul_cancel₀ _ hV0.ne']
  · intro n hn1 hn2
    have hpt : ∀ t : ℝ, (r : ℂ) * ψ t * e (-((n:ℝ) * t))
        = (r : ℂ) * (ψ t * e (-((n:ℝ) * t))) := fun t => by ring
    simp only [hpt]
    rw [intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    nlinarith [hcoef n hn1 hn2, norm_nonneg (∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t)))]

/-! ##### The small-band regime — a second explicit solution of (C)

Beyond `N ≤ 1` there is a whole regime of (C) with a completely explicit witness. Measure
the spread of the constrained frequencies by

  `L := (N − 1)·δ`

— the band `[δ, Nδ]` of work-saver 2's rescaled picture. When `L ≤ 1/2` the **modulated**
indicator

  `ψ := A·e(μt)·𝟙_{(0,δ]}`,   `μ := (N+1)/2`,   `A := (1 + L/3)/δ`

already solves (C): its mass is `A²δ = (1+L/3)²/δ ≤ (1+L)/δ = N − 1 + δ⁻¹` (work-saver 1
then rescales it to equality), and its coefficients satisfy
`|ψ̂(n)| = A·|sin(π(μ−n)δ)|/(π|μ−n|) ≥ Aδ(1 − π²L²/24) = (1+L/3)(1 − π²L²/24) ≥ 1`,
because `|μ − n| ≤ (N−1)/2` for every `1 ≤ n ≤ N`.

**This is not the dead end recorded at `selberg_majorant_of_lt_half`.** That entry concerns
the *unmodulated* indicator, which centres the band at `0` rather than at the midpoint `μ`
of `[1, N]`, and which indeed fails already at `N = 1`. Modulating to the band centre is
what makes the first-order phase cancel; only the second-order (cosine) loss `π²L²/24`
remains, and the slack `√(1+L) − 1 ≈ L/2` pays for it as long as `L = O(1)`. -/

/-- `‖e y − 1‖ = 2|sin(πy)|`. Elementary: `(e y − 1)·conj(e y − 1) = 2 − 2cos(2πy)` and
`cos 2θ = 1 − 2 sin²θ`. -/
theorem norm_e_sub_one (y : ℝ) : ‖e y - 1‖ = 2 * |Real.sin (Real.pi * y)| := by
  have he1 : e y = Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have he2 : e (-y) = Complex.exp (-((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have hcos : e y + e (-y) = 2 * ((Real.cos (2 * Real.pi * y) : ℝ) : ℂ) := by
    rw [he1, he2, Complex.ofReal_cos, Complex.two_cos]
  have h1 : e y * e (-y) = 1 := by rw [← e_add]; simp
  have hprod : (e y - 1) * (starRingEnd ℂ) (e y - 1)
      = 2 - 2 * ((Real.cos (2 * Real.pi * y) : ℝ) : ℂ) := by
    rw [map_sub, map_one, conj_e]
    linear_combination h1 - hcos
  have hnorm2 : ((‖e y - 1‖ : ℝ) : ℂ) ^ 2
      = 2 - 2 * ((Real.cos (2 * Real.pi * y) : ℝ) : ℂ) := by
    rw [← hprod, Complex.mul_conj']
  have hreal : ‖e y - 1‖ ^ 2 = 2 - 2 * Real.cos (2 * Real.pi * y) := by
    exact_mod_cast hnorm2
  have hdouble : Real.cos (2 * Real.pi * y) = 1 - 2 * Real.sin (Real.pi * y) ^ 2 := by
    have hd := Real.cos_two_mul' (Real.pi * y)
    have hp := Real.sin_sq_add_cos_sq (Real.pi * y)
    rw [show 2 * (Real.pi * y) = 2 * Real.pi * y by ring] at hd
    linarith
  have hfin : ‖e y - 1‖ ^ 2 = (2 * |Real.sin (Real.pi * y)|) ^ 2 := by
    rw [hreal, hdouble, mul_pow, sq_abs]; ring
  nlinarith [hfin, norm_nonneg (e y - 1), abs_nonneg (Real.sin (Real.pi * y))]

/-- **The one estimate the small-band witness needs:** `‖∫₀^δ e(xt) dt‖ ≥ δ(1 − (πxδ)²/6)`.

The integral is `(e(xδ) − 1)/(2πix)`, of modulus `|sin(πxδ)|/(π|x|)` by `norm_e_sub_one`,
and `sin u > u − u³/6` for `u > 0` (`Real.sin_gt_sub_cube`). The bound is second order in
`xδ`: that is exactly why the *modulated* indicator succeeds where the unmodulated one
cannot. -/
theorem norm_integral_e_ge {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    δ * (1 - (Real.pi * x * δ) ^ 2 / 6) ≤ ‖∫ t in (0:ℝ)..δ, e (x * t)‖ := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    have hz : (∫ t in (0:ℝ)..δ, e (0 * t)) = ((δ : ℝ) : ℂ) := by
      simp
    rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ.le]
    have : Real.pi * 0 * δ = 0 := by ring
    rw [this]
    norm_num
  · set C : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) with hC
    have hCne : C ≠ 0 := by
      rw [hC]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hx)
    have hrw : ∀ t : ℝ, e (x * t) = Complex.exp (C * (t : ℂ)) := by
      intro t; rw [e, hC]; congr 1; push_cast; ring
    have hval : (∫ t in (0:ℝ)..δ, e (x * t)) = (e (x * δ) - 1) / C := by
      simp only [hrw]
      rw [integral_exp_mul_complex hCne]
      have h1 : Complex.exp (C * (((δ : ℝ)) : ℂ)) = e (x * δ) := by
        rw [e, hC]; congr 1; push_cast; ring
      have h2 : Complex.exp (C * (((0 : ℝ)) : ℂ)) = 1 := by simp
      rw [h1, h2]
    have hCnorm : ‖C‖ = 2 * Real.pi * |x| := by
      rw [hC]
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one]
      rw [abs_of_nonneg Real.pi_pos.le]
      norm_num
    rw [hval, norm_div, norm_e_sub_one, hCnorm]
    set w : ℝ := Real.pi * x * δ with hw
    have hxpos : 0 < |x| := abs_pos.mpr hx
    have hwabs : |w| = Real.pi * |x| * δ := by
      rw [hw, abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg hδ.le]
    have hwpos : 0 < |w| := by rw [hwabs]; positivity
    have hsinabs : Real.sin |w| ≤ |Real.sin w| := by
      rcases abs_cases w with ⟨h3, _⟩ | ⟨h3, _⟩
      · rw [h3]; exact le_abs_self _
      · rw [h3, Real.sin_neg]; exact neg_le_abs _
    have hsin : |w| - |w| ^ 3 / 6 < |Real.sin w| :=
      lt_of_lt_of_le (Real.sin_gt_sub_cube hwpos) hsinabs
    have harg : Real.pi * (x * δ) = w := by rw [hw]; ring
    rw [harg]
    have hchain : δ * (1 - w ^ 2 / 6) ≤ δ * (|Real.sin w| / |w|) := by
      refine mul_le_mul_of_nonneg_left ?_ hδ.le
      rw [le_div_iff₀ hwpos]
      nlinarith [hsin, sq_abs w, abs_nonneg w]
    refine hchain.trans (le_of_eq ?_)
    rw [hwabs]
    field_simp

/-- **(C) in the small-band regime `(N − 1)δ ≤ 1/2` — PROVED, with an explicit witness.**

The modulated indicator `((1 + L/3)/δ)·e(((N+1)/2)·t)·𝟙_{(0,δ]}`, `L := (N−1)δ`, satisfies
(C) up to `≤` in the mass, and `l2_concentration_of_le` upgrades that to equality. Together
with `l2_concentration_of_le_one` (the case `N ≤ 1`, i.e. `L = 0`) this is everything of
`l2_concentration_exists` that is currently proved.

It does **not** close `l2_concentration_exists`: the residue is the large-band regime
`(N − 1)δ > 1/2`, where no single modulation can work — see that theorem's docstring.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` and `δ` are unrelated. -/
theorem l2_concentration_of_small_band (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hband : ((N:ℝ) - 1) * δ ≤ 1 / 2) :
    ∃ ψ : ℝ → ℂ, MemLp ψ 2 volume ∧ (∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0) ∧
      (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) = (N:ℝ) - 1 + δ⁻¹ ∧
      (∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
        1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖) := by
  rcases le_or_gt N 1 with hN | hN
  · exact l2_concentration_of_le_one hN hδ hδ1
  have hNr : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  set L : ℝ := ((N:ℝ) - 1) * δ with hLdef
  have hL0 : 0 < L := by rw [hLdef]; have : (1:ℝ) ≤ (N:ℝ) - 1 := by linarith
                         positivity
  have hL2 : L ≤ 1 / 2 := hband
  set A : ℝ := (1 + L / 3) / δ with hAdef
  have hA0 : 0 < A := by rw [hAdef]; positivity
  set μ : ℝ := ((N:ℝ) + 1) / 2 with hμdef
  have hAδ : A * δ = 1 + L / 3 := by rw [hAdef]; field_simp
  -- the explicit witness
  have hcont : Continuous (fun t : ℝ => (A : ℂ) * e (μ * t)) :=
    continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))
  set ψ : ℝ → ℂ := Set.indicator (Set.Ioc (0:ℝ) δ) (fun t => (A : ℂ) * e (μ * t)) with hψdef
  have hmem : MemLp ψ 2 volume := by
    rw [hψdef]
    refine (memLp_indicator_iff_restrict measurableSet_Ioc).mpr ?_
    refine MemLp.of_bound hcont.aestronglyMeasurable A ?_
    filter_upwards with t
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0.le]
  have hsupp : ∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0 := fun t ht =>
    Set.indicator_of_notMem ht _
  -- mass: `A²δ = (1 + L/3)²/δ ≤ (1 + L)/δ = N − 1 + δ⁻¹`
  have hmass : (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) = A ^ 2 * δ := by
    rw [intervalIntegral.integral_of_le hδ.le,
      setIntegral_congr_fun measurableSet_Ioc
        (show Set.EqOn (fun t => ‖ψ t‖ ^ 2) (fun _ => A ^ 2) (Set.Ioc (0:ℝ) δ) from
          fun t ht => by
            simp only [hψdef, Set.indicator_of_mem ht, norm_mul, norm_e, mul_one,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0.le]),
      setIntegral_const, Real.volume_real_Ioc_of_le hδ.le, sub_zero, smul_eq_mul, mul_comm]
  have hnorm : (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) ≤ (N:ℝ) - 1 + δ⁻¹ := by
    rw [hmass]
    have hbud : (N:ℝ) - 1 + δ⁻¹ = (1 + L) / δ := by
      rw [hLdef]; field_simp; ring
    rw [hbud, le_div_iff₀ hδ]
    have hA2 : A ^ 2 * δ * δ = (1 + L / 3) ^ 2 := by
      rw [← hAδ]; ring
    nlinarith [hA2, hL0, hL2]
  -- coefficients
  have hcoef : ∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
      1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖ := by
    intro n hn1 hn2
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have hn2r : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn2
    set x : ℝ := μ - (n:ℝ) with hxdef
    have hxabs : |x| ≤ ((N:ℝ) - 1) / 2 := by
      rw [hxdef, hμdef, abs_le]
      constructor <;> linarith
    have hEq : (∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t)))
        = (A : ℂ) * ∫ t in (0:ℝ)..δ, e (x * t) := by
      rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le,
        ← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      simp only [hψdef, Set.indicator_of_mem ht]
      rw [mul_assoc, ← e_add]
      congr 2
      rw [hxdef]; ring
    rw [hEq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0.le]
    have hlow := norm_integral_e_ge (δ := δ) hδ x
    have hpisq : Real.pi ^ 2 ≤ 9.9225 := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hband2 : (Real.pi * x * δ) ^ 2 ≤ Real.pi ^ 2 * L ^ 2 / 4 := by
      have hx2 : x ^ 2 ≤ (((N:ℝ) - 1) / 2) ^ 2 := by
        have h0 : (0:ℝ) ≤ ((N:ℝ) - 1) / 2 := by linarith
        nlinarith [abs_nonneg x, sq_abs x, hxabs]
      have : (Real.pi * x * δ) ^ 2 = Real.pi ^ 2 * x ^ 2 * δ ^ 2 := by ring
      rw [this, hLdef]
      nlinarith [sq_nonneg δ, Real.pi_pos, sq_nonneg Real.pi, hx2, sq_nonneg (Real.pi * δ)]
    have hstep : 1 ≤ A * (δ * (1 - Real.pi ^ 2 * L ^ 2 / 24)) := by
      have hkey : (1 + L / 3) * (1 - Real.pi ^ 2 * L ^ 2 / 24) ≥ 1 := by
        nlinarith [hL0, hL2, hpisq, sq_nonneg L, mul_pos hL0 hL0]
      calc (1:ℝ) ≤ (1 + L / 3) * (1 - Real.pi ^ 2 * L ^ 2 / 24) := hkey
        _ = A * (δ * (1 - Real.pi ^ 2 * L ^ 2 / 24)) := by rw [← hAδ]; ring
    refine hstep.trans ?_
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hA0.le) (mul_le_mul_of_nonneg_left hlow hA0.le)
    have : (0:ℝ) < δ := hδ
    nlinarith [hband2, hδ]
  exact l2_concentration_of_le (by omega) hδ hmem hsupp hnorm hcoef

/-- **The Beurling–Selberg majorant EXISTS at every bandwidth `0 < δ ≤ 1` whenever the band
`(N − 1)δ` is at most `1/2` — for arbitrarily large `N`.** Sorry-free.

This is `l2_concentration_of_small_band` run through `selbergMajorant_of_concentration`. It
strictly extends `selbergMajorant_of_le_one`, and it is the evidence that the reduction of
§1.1.b is not merely non-vacuous but has an *infinite* supply of honest witnesses with `N`
unbounded. The general case still needs `l2_concentration_exists`. -/
theorem selbergMajorant_of_small_band (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hband : ((N:ℝ) - 1) * δ ≤ 1 / 2) : Nonempty (SelbergMajorant N δ) := by
  obtain ⟨ψ, hmem, hsupp, hnorm, hcoef⟩ := l2_concentration_of_small_band N hδ hδ1 hband
  exact selbergMajorant_of_concentration N hδ hδ1 hmem hsupp hnorm hcoef

/-! ##### Widening the proved band from `(N − 1)δ ≤ 1/2` to `(N − 1)δ ≤ 1`

The small-band witness is a SINGLE modulation `e(μt)` at the midpoint `μ = (N+1)/2` of the
constrained band `[1, N]`, and it runs out of slack at `L := (N−1)δ ≈ 0.83`. The next
witness in the same family is the *difference of two* modulations whose frequencies differ
by exactly `δ⁻¹` — the gap that makes them ORTHOGONAL on `(0, δ]`, so that the mass stays
exactly computable — placed symmetrically about the midpoint:

  `ψ := A·(e(μt) − e(μ′t))·𝟙_{(0,δ]}`,  `μ := (N+1)/2 − 1/(2δ)`,  `μ′ := (N+1)/2 + 1/(2δ)`,
  `A := s/δ`,  `s := √((1+L)/2)`.

Mass `= 2A²δ = (1+L)/δ = N − 1 + δ⁻¹` — the budget, EXACTLY, so `l2_concentration_of_le` is
not even needed. For the coefficients write `z := ((N+1)/2 − n)·δ`, so that `|z| ≤ L/2` for
every `1 ≤ n ≤ N`; the two frequencies sit at `xδ = z − 1/2` and `x′δ = z + 1/2`, and since
`e((x+δ⁻¹)δ) = e(xδ)` the two Dirichlet kernels combine into a single interpolation kernel:

  `|ψ̂(n)| = s·cos(πz) / (π(1/4 − z²))`.

The function `cos(πz)/(π(1/4 − z²))` is `≥ 1` on `(−1/2, 1/2)` with limit exactly `1` at
both endpoints, and `s ≤ 1` is exactly what the budget pays for; so the entire band
`|z| ≤ 1/2`, i.e. `L ≤ 1`, is available, with equality at `L = 1` (there `s = 1`, and the
constraints at `n = 1` and `n = N` are met with equality — the kernel degenerates, one of
the two frequencies being `0`, which is why that case is split off below).

**Why this family stops at `L = 1`** (numerical finding, recorded so it is not re-derived).
In the finite-dimensional picture of `l2_concentration_exists`'s docstring, `ψ` on `(0,δ]`
is *always* `δ⁻¹Σ_k c_k e(kt/δ)` — that lattice is an orthogonal basis — and the constraints
read `|F(y_n)| ≥ 1`, `F(y) := (sin πy/π)·Σ_k c_k/(y+k)`, `Σ_k|c_k|² ≤ 1 + L`, with the `y_n`
spanning an interval of length `L`. The exact identity `Σ_k (−1)^k/(y+k) = π/sin(πy)` makes
`c_k = (−1)^k` give `F ≡ 1` with infinite energy; the above is its `K = 2` truncation
`c = (a, −a)`, `a = s`. The `K`-term truncation has `F(−j) = |c_j|` at each of its `K`
interior integers, so it needs `|c_j| ≥ 1` there and hence `K ≤ 1 + L`; combined with the
window length `K − 1 ≥ L` this forces `L = K − 1`. `K = 2` is therefore the last member of
the family covering an *interval* of `L`'s (`L ≤ 1` is available only because an interval of
length `L < 1` can be placed strictly between two consecutive integers). Concretely at
`L = 1.5`, `K = 3`: the two endpoint constraints force `a_0 + a_2 ≥ 1.814` while the budget
allows only `a_0 + a_2 ≤ √(2·1.5) = 1.732`. Beyond `L = 1` the `|c_k|` must stop being equal
and the phases must become a chirp — and that is exactly Selberg.

**AMENDED, in both directions.** (a) At the pinned values `L = K − 1` the
`K`-term truncation really does solve (C) — but *only* for `K ≤ 3`. Writing the truncation in
Shannon form, `R(w) = Σ_{k=1}^{K}sinc(w − k)`, one has `min_{[1,K]}R = 1` for `K = 1, 2, 3` and
`R(5/2) = 0.848826 < 1` already at `K = 4`. So `L = 2` is one further provable (but
measure-zero) point, and from `L = 3` on the extremal coefficients are unimodular yet complex.
(b) The band `L ≤ 1` is now known to be the end of *every* elementary method, not just of the
equal-moduli family: by `l2_concentration_mass_ge` the budget is attained with EQUALITY at
`(N, δ) = (qm + 1, q⁻¹)`, and letting `q → ∞` at fixed `m` those points force any putative
`L ≤ c` anchor (`c > 1`) to be asymptotically extremal. See item 2 of the finding block in
`l2_concentration_exists`'s docstring. -/

/-- The exact value of `∫₀^b e(x t) dt` at `x ≠ 0`. This computation appeared inline inside
`norm_integral_e_ge`; the two-modulation witness needs the value, not just its modulus. -/
theorem intervalIntegral_e_eq (b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    (∫ t in (0:ℝ)..b, e (x * t))
      = (e (x * b) - 1) / (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by
  set C : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) with hC
  have hCne : C ≠ 0 := by
    rw [hC]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hx)
  have hrw : ∀ t : ℝ, e (x * t) = Complex.exp (C * (t : ℂ)) := by
    intro t; rw [e, hC]; congr 1; push_cast; ring
  simp only [hrw]
  rw [integral_exp_mul_complex hCne]
  have h1 : Complex.exp (C * ((b : ℝ) : ℂ)) = e (x * b) := by
    rw [e, hC]; congr 1; push_cast; ring
  have h2 : Complex.exp (C * (((0 : ℝ)) : ℂ)) = 1 := by simp
  rw [h1, h2]

/-- **Orthogonality on `(0, δ]`:** `∫₀^δ e(xt) dt = 0` as soon as `xδ` is a nonzero integer.
This is what makes the frequency gap `δ⁻¹` the right one for the two-modulation witness. -/
theorem intervalIntegral_e_orth {δ x : ℝ} (hx : x ≠ 0) {k : ℤ} (hxδ : x * δ = (k : ℝ)) :
    (∫ t in (0:ℝ)..δ, e (x * t)) = 0 := by
  rw [intervalIntegral_e_eq δ hx, hxδ, e_intCast, sub_self, zero_div]

/-- The polynomial core of the two-modulation estimate: with `s² = (1+L)/2` and
`v ≥ (1−L)/2` (the distance from the constraint point to the nearer pole of the kernel),
`1 − v ≤ s(1 − (5/3)v²)`. The constant `5/3` is a safe upper bound for `π²/6`.

`f(v) := s(1 − (5/3)v²) + v − 1` is CONCAVE in `v`, so it suffices to check the two
endpoints `v = 1 − s²` and `v = 1/2`; the identity `hid` below is exactly the statement that
a concave quadratic dominates the chord through its endpoint values. -/
theorem band_poly_ineq {s v : ℝ} (hs0 : 0 < s) (hs2 : 3 / 4 ≤ s ^ 2) (hs1 : s ≤ 1)
    (hv0 : 1 - s ^ 2 ≤ v) (hv1 : v ≤ 1 / 2) :
    1 - v ≤ s * (1 - (5 / 3) * v ^ 2) := by
  have hs67 : (6:ℝ) / 7 ≤ s := by nlinarith [hs2, hs0]
  have hgap : (0:ℝ) < s ^ 2 - 1 / 2 := by linarith
  have hlo : (0:ℝ) ≤ v - (1 - s ^ 2) := by linarith
  have hhi : (0:ℝ) ≤ 1 / 2 - v := by linarith
  have hf1 : (0:ℝ) ≤ s * (1 - (5 / 3) * (1 / 2 : ℝ) ^ 2) + 1 / 2 - 1 := by nlinarith [hs67]
  have hf0 : (0:ℝ) ≤ s * (1 - (5 / 3) * (1 - s ^ 2) ^ 2) + (1 - s ^ 2) - 1 := by
    have h3 : (0:ℝ) ≤ 1 - s := by linarith
    have h1 : (1:ℝ) - s ≤ 1 / 7 := by linarith
    have h2 : (1 + s) ^ 2 ≤ 4 := by nlinarith
    have h4 : (1 - s) * (1 + s) ^ 2 ≤ (1 / 7) * 4 :=
      mul_le_mul h1 h2 (sq_nonneg _) (by norm_num)
    have hfac : s * (1 - (5 / 3) * (1 - s ^ 2) ^ 2) + (1 - s ^ 2) - 1
        = s * (1 - s) * (1 - (5 / 3) * ((1 - s) * (1 + s) ^ 2)) := by ring
    rw [hfac]
    exact mul_nonneg (mul_nonneg hs0.le h3) (by linarith)
  have hid : (s ^ 2 - 1 / 2) * (s * (1 - (5 / 3) * v ^ 2) + v - 1)
      = (1 / 2 - v) * (s * (1 - (5 / 3) * (1 - s ^ 2) ^ 2) + (1 - s ^ 2) - 1)
        + (v - (1 - s ^ 2)) * (s * (1 - (5 / 3) * (1 / 2 : ℝ) ^ 2) + 1 / 2 - 1)
        + (5 / 3) * s * ((v - (1 - s ^ 2)) * ((1 / 2 - v) * (s ^ 2 - 1 / 2))) := by ring
  nlinarith [hid, mul_nonneg hhi hf0, mul_nonneg hlo hf1,
    mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (5 / 3) * s) hlo)
      (mul_nonneg hhi hgap.le), hgap]

/-- The trigonometric form of `band_poly_ineq`, which is what the coefficient bound needs:
`π·v(1−v) ≤ s·sin(πv)`. Uses `Real.sin_gt_sub_cube` (`sin u > u − u³/6` for `u > 0`). -/
theorem band_sin_ineq {s v : ℝ} (hs0 : 0 < s) (hs2 : 3 / 4 ≤ s ^ 2) (hs1 : s ≤ 1)
    (hv0 : 1 - s ^ 2 ≤ v) (hvnn : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    Real.pi * (v * (1 - v)) ≤ s * Real.sin (Real.pi * v) := by
  rcases eq_or_lt_of_le hvnn with h | hvpos
  · rw [← h]; simp
  · have hpv : 0 < Real.pi * v := by positivity
    have hsin := Real.sin_gt_sub_cube hpv
    have hpoly := band_poly_ineq hs0 hs2 hs1 hv0 hv1
    have hpi2 : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have haux : (0:ℝ) ≤ s * v ^ 2 * (10 - Real.pi ^ 2) :=
      mul_nonneg (mul_nonneg hs0.le (sq_nonneg v)) (by linarith)
    have hstep : 1 - v ≤ s * (1 - Real.pi ^ 2 * v ^ 2 / 6) := by
      have hid : s * (1 - Real.pi ^ 2 * v ^ 2 / 6)
          = s * (1 - (5 / 3) * v ^ 2) + s * v ^ 2 * (10 - Real.pi ^ 2) / 6 := by ring
      rw [hid]; linarith
    have h2 : (Real.pi * v) * (1 - v) ≤ (Real.pi * v) * (s * (1 - Real.pi ^ 2 * v ^ 2 / 6)) :=
      mul_le_mul_of_nonneg_left hstep hpv.le
    have h1 : s * (Real.pi * v - (Real.pi * v) ^ 3 / 6) ≤ s * Real.sin (Real.pi * v) :=
      mul_le_mul_of_nonneg_left hsin.le hs0.le
    nlinarith [h1, h2]

/-- **(C) on the whole band `(N − 1)δ ≤ 1` — PROVED, with an explicit witness.**

This strictly extends `l2_concentration_of_small_band` (band `≤ 1/2`), which it cites for
the small band and which in turn subsumes `l2_concentration_of_le_one`. The witness in the
remaining range `1/2 < L ≤ 1` is the difference of the two modulations at
`μ = (N+1)/2 ∓ 1/(2δ)` described in the section note above; its mass is *exactly* the budget
`N − 1 + δ⁻¹`, so no rescaling through `l2_concentration_of_le` is needed.

It does **not** close `l2_concentration_exists`: the residue is `(N − 1)δ > 1`, where the
kernel coefficients must stop having equal moduli — see the section note and that theorem's
docstring.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` and `δ` are unrelated. -/
theorem l2_concentration_of_band_le_one (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hband : ((N:ℝ) - 1) * δ ≤ 1) :
    ∃ ψ : ℝ → ℂ, MemLp ψ 2 volume ∧ (∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0) ∧
      (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) = (N:ℝ) - 1 + δ⁻¹ ∧
      (∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
        1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖) := by
  rcases le_or_gt (((N:ℝ) - 1) * δ) (1 / 2) with hsmall | hlarge
  · exact l2_concentration_of_small_band N hδ hδ1 hsmall
  have hδne : δ ≠ 0 := hδ.ne'
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  set L : ℝ := ((N:ℝ) - 1) * δ with hLdef
  clear_value L
  have hNr : (2:ℝ) ≤ (N:ℝ) := by
    rcases Nat.lt_or_ge N 2 with h | h
    · exfalso
      have hN1 : N ≤ 1 := by omega
      have hN1r : (N:ℝ) ≤ 1 := by exact_mod_cast hN1
      have hle : L ≤ 0 := by rw [hLdef]; nlinarith
      linarith
    · exact_mod_cast h
  -- the amplitude, fixed by the budget
  set s : ℝ := Real.sqrt ((1 + L) / 2) with hsdef
  have hs2 : s ^ 2 = (1 + L) / 2 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  clear_value s
  have hs1 : s ≤ 1 := by nlinarith [hs2, hs0]
  have hs34 : 3 / 4 ≤ s ^ 2 := by rw [hs2]; linarith
  set A : ℝ := s / δ with hAdef
  clear_value A
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hAδ : A * δ = s := by rw [hAdef]; field_simp
  -- the two frequencies, symmetric about the midpoint `(N+1)/2`, at gap `δ⁻¹`
  set μ : ℝ := ((N:ℝ) + 1) / 2 - 1 / (2 * δ) with hμdef
  set ν : ℝ := ((N:ℝ) + 1) / 2 + 1 / (2 * δ) with hνdef
  clear_value μ ν
  have hmm : μ - ν = -δ⁻¹ := by rw [hμdef, hνdef]; field_simp; ring
  have hmm' : ν - μ = δ⁻¹ := by rw [hμdef, hνdef]; field_simp; ring
  have hmmne : μ - ν ≠ 0 := by rw [hmm]; simpa using hδne
  have hmm'ne : ν - μ ≠ 0 := by rw [hmm']; simpa using hδne
  have hc : ∀ w : ℝ, IntervalIntegrable (fun t : ℝ => e (w * t)) volume 0 δ := fun w =>
    (continuous_e.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hcont : Continuous (fun t : ℝ => (A : ℂ) * (e (μ * t) - e (ν * t))) :=
    continuous_const.mul
      ((continuous_e.comp (continuous_const.mul continuous_id)).sub
        (continuous_e.comp (continuous_const.mul continuous_id)))
  set ψ : ℝ → ℂ :=
    Set.indicator (Set.Ioc (0:ℝ) δ) (fun t => (A : ℂ) * (e (μ * t) - e (ν * t))) with hψdef
  have hmem : MemLp ψ 2 volume := by
    rw [hψdef]
    refine (memLp_indicator_iff_restrict measurableSet_Ioc).mpr ?_
    refine MemLp.of_bound hcont.aestronglyMeasurable (A * 2) ?_
    filter_upwards with t
    have hb : ‖e (μ * t) - e (ν * t)‖ ≤ 2 := by
      calc ‖e (μ * t) - e (ν * t)‖ ≤ ‖e (μ * t)‖ + ‖e (ν * t)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_e, norm_e]; norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0.le]
    exact mul_le_mul_of_nonneg_left hb hA0.le
  have hsupp : ∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0 := fun t ht =>
    Set.indicator_of_notMem ht _
  clear_value ψ
  -- MASS: the two modulations are orthogonal on `(0, δ]`, so the mass is exactly `2A²δ`
  have hI : (∫ t in (0:ℝ)..δ, ‖e (μ * t) - e (ν * t)‖ ^ 2) = 2 * δ := by
    have hint : ∀ t : ℝ, ((‖e (μ * t) - e (ν * t)‖ ^ 2 : ℝ) : ℂ)
        = 2 - e ((μ - ν) * t) - e ((ν - μ) * t) := by
      intro t
      have h2 : e (μ * t) * e (-(ν * t)) = e ((μ - ν) * t) := by
        rw [← e_add]; congr 1; ring
      have h3 : e (ν * t) * e (-(μ * t)) = e ((ν - μ) * t) := by
        rw [← e_add]; congr 1; ring
      have h4 : e (μ * t) * e (-(μ * t)) = 1 := by rw [← e_add]; simp
      have h5 : e (ν * t) * e (-(ν * t)) = 1 := by rw [← e_add]; simp
      push_cast
      rw [(Complex.mul_conj' (e (μ * t) - e (ν * t))).symm, map_sub, conj_e, conj_e,
        show (e (μ * t) - e (ν * t)) * (e (-(μ * t)) - e (-(ν * t)))
            = e (μ * t) * e (-(μ * t)) + e (ν * t) * e (-(ν * t))
              - e (μ * t) * e (-(ν * t)) - e (ν * t) * e (-(μ * t)) from by ring,
        h2, h3, h4, h5]
      ring
    have hz1 : (∫ t in (0:ℝ)..δ, e ((μ - ν) * t)) = 0 :=
      intervalIntegral_e_orth (k := -1) hmmne (by rw [hmm]; push_cast; field_simp)
    have hz2 : (∫ t in (0:ℝ)..δ, e ((ν - μ) * t)) = 0 :=
      intervalIntegral_e_orth (k := 1) hmm'ne (by rw [hmm']; push_cast; field_simp)
    have hcast : ((∫ t in (0:ℝ)..δ, ‖e (μ * t) - e (ν * t)‖ ^ 2 : ℝ) : ℂ)
        = ((2 * δ : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      simp only [hint]
      rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub (hc _)) (hc _),
        intervalIntegral.integral_sub intervalIntegrable_const (hc _), hz1, hz2]
      simp only [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
      push_cast
      ring
    exact_mod_cast hcast
  have hmass : (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) = (N:ℝ) - 1 + δ⁻¹ := by
    have hcongr : (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2)
        = ∫ t in (0:ℝ)..δ, A ^ 2 * ‖e (μ * t) - e (ν * t)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      simp only [hψdef, Set.indicator_of_mem ht, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hA0.le, mul_pow]
    rw [hcongr, intervalIntegral.integral_const_mul, hI, hAdef, div_pow, hs2, hLdef]
    field_simp
    ring
  -- COEFFICIENTS
  have hcoef : ∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
      1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖ := by
    intro n hn1 hn2
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have hn2r : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn2
    set x : ℝ := μ - (n:ℝ) with hxdef
    set y : ℝ := ν - (n:ℝ) with hydef
    set z : ℝ := (((N:ℝ) + 1) / 2 - (n:ℝ)) * δ with hzdef
    clear_value x y z
    have hxz : x * δ = z - 1 / 2 := by rw [hxdef, hμdef, hzdef]; field_simp; ring
    have hyz : y * δ = z + 1 / 2 := by rw [hydef, hνdef, hzdef]; field_simp; ring
    have hdx : y - x = δ⁻¹ := by rw [hxdef, hydef]; linear_combination hmm'
    have hzabs : |z| ≤ L / 2 := by
      rw [hzdef, abs_mul, abs_of_pos hδ, hLdef]
      have h1 : |((N:ℝ) + 1) / 2 - (n:ℝ)| ≤ ((N:ℝ) - 1) / 2 := by
        rw [abs_le]; constructor <;> linarith
      nlinarith [h1, hδ, abs_nonneg (((N:ℝ) + 1) / 2 - (n:ℝ))]
    have hEq : (∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t)))
        = (A : ℂ) * ((∫ t in (0:ℝ)..δ, e (x * t)) - ∫ t in (0:ℝ)..δ, e (y * t)) := by
      have hstep : (∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t)))
          = ∫ t in (0:ℝ)..δ, (A : ℂ) * (e (x * t) - e (y * t)) := by
        rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le]
        refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
        have h1 : e (μ * t) * e (-((n:ℝ) * t)) = e (x * t) := by
          rw [← e_add]; congr 1; rw [hxdef]; ring
        have h2 : e (ν * t) * e (-((n:ℝ) * t)) = e (y * t) := by
          rw [← e_add]; congr 1; rw [hydef]; ring
        simp only [hψdef, Set.indicator_of_mem ht]
        calc (A : ℂ) * (e (μ * t) - e (ν * t)) * e (-((n:ℝ) * t))
            = (A : ℂ) * (e (μ * t) * e (-((n:ℝ) * t)) - e (ν * t) * e (-((n:ℝ) * t))) := by
              ring
          _ = (A : ℂ) * (e (x * t) - e (y * t)) := by rw [h1, h2]
      rw [hstep, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (hc x) (hc y)]
    by_cases hzA : z = 1 / 2
    · -- left endpoint, only reachable at `L = 1`: the first frequency degenerates to `0`
      have h1L : (1:ℝ) ≤ L := by
        have hh : |(1:ℝ) / 2| ≤ L / 2 := by rw [← hzA]; exact hzabs
        rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)] at hh
        linarith
      have hLone : L = 1 := le_antisymm hband h1L
      have hsone : s = 1 := by rw [hsdef, hLone]; norm_num
      have hx0 : x = 0 := by
        rcases mul_eq_zero.mp (show x * δ = 0 by rw [hxz, hzA]; ring) with h | h
        · exact h
        · exact absurd h hδne
      have hyne : y ≠ 0 := by
        intro h
        rw [h, zero_mul, hzA] at hyz
        norm_num at hyz
      have hint1 : (∫ t in (0:ℝ)..δ, e (x * t)) = ((δ : ℝ) : ℂ) := by rw [hx0]; simp
      have hint2 : (∫ t in (0:ℝ)..δ, e (y * t)) = 0 :=
        intervalIntegral_e_orth (k := 1) hyne (by rw [hyz, hzA]; push_cast; ring)
      rw [hEq, hint1, hint2, sub_zero, ← Complex.ofReal_mul, hAδ, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hs0.le, hsone]
    by_cases hzB : z = -(1 / 2)
    · -- right endpoint, only reachable at `L = 1`: the second frequency degenerates to `0`
      have h1L : (1:ℝ) ≤ L := by
        have hh : |(-(1:ℝ) / 2)| ≤ L / 2 := by
          rw [show (-(1:ℝ) / 2) = z by rw [hzB]; ring]; exact hzabs
        rw [abs_of_nonpos (by norm_num : (-(1:ℝ) / 2) ≤ 0)] at hh
        linarith
      have hLone : L = 1 := le_antisymm hband h1L
      have hsone : s = 1 := by rw [hsdef, hLone]; norm_num
      have hy0 : y = 0 := by
        rcases mul_eq_zero.mp (show y * δ = 0 by rw [hyz, hzB]; ring) with h | h
        · exact h
        · exact absurd h hδne
      have hxne : x ≠ 0 := by
        intro h
        rw [h, zero_mul, hzB] at hxz
        norm_num at hxz
      have hint2 : (∫ t in (0:ℝ)..δ, e (y * t)) = ((δ : ℝ) : ℂ) := by rw [hy0]; simp
      have hint1 : (∫ t in (0:ℝ)..δ, e (x * t)) = 0 :=
        intervalIntegral_e_orth (k := -1) hxne (by rw [hxz, hzB]; push_cast; ring)
      rw [hEq, hint1, hint2, zero_sub,
        show (A : ℂ) * -((δ : ℝ) : ℂ) = -(((A * δ : ℝ)) : ℂ) by push_cast; ring,
        norm_neg, Complex.norm_real, Real.norm_eq_abs, hAδ, abs_of_nonneg hs0.le, hsone]
    -- the generic case `|z| < 1/2`: both frequencies are nonzero
    have hzlt : |z| < 1 / 2 := by
      rcases lt_or_eq_of_le (hzabs.trans (by linarith : L / 2 ≤ 1 / 2)) with h | h
      · exact h
      · exact absurd ((abs_eq (by norm_num : (0:ℝ) ≤ 1 / 2)).mp h) (by tauto)
    have hzu := (abs_lt.mp hzlt).2
    have hzl := (abs_lt.mp hzlt).1
    have hz1' : (0:ℝ) < 1 / 2 - z := by linarith
    have hz2' : (0:ℝ) < 1 / 2 + z := by linarith
    have hz1ne : (1:ℝ) / 2 - z ≠ 0 := ne_of_gt hz1'
    have hz2ne : (1:ℝ) / 2 + z ≠ 0 := ne_of_gt hz2'
    have hxne : x ≠ 0 := by
      intro h; rw [h, zero_mul] at hxz; linarith
    have hyne : y ≠ 0 := by
      intro h; rw [h, zero_mul] at hyz; linarith
    have hxC : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxne
    have hyC : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hyne
    have hpiC : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hIC : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hcosnn : 0 ≤ Real.cos (Real.pi * z) := by
      refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    have hW : ‖e (x * δ) - 1‖ = 2 * Real.cos (Real.pi * z) := by
      rw [norm_e_sub_one, hxz]
      have h1 : Real.sin (Real.pi * (z - 1 / 2)) = -Real.cos (Real.pi * z) := by
        have h := Real.sin_sub (Real.pi * z) (Real.pi / 2)
        rw [Real.cos_pi_div_two, Real.sin_pi_div_two] at h
        rw [show Real.pi * (z - 1 / 2) = Real.pi * z - Real.pi / 2 by ring, h]
        ring
      rw [h1, abs_neg, abs_of_nonneg hcosnn]
    have hxval : x = (z - 1 / 2) / δ := (eq_div_iff hδne).mpr hxz
    have hyval : y = (z + 1 / 2) / δ := (eq_div_iff hδne).mpr hyz
    have habsx : |x| = (1 / 2 - z) / δ := by
      rw [hxval, abs_div, abs_of_pos hδ, abs_of_nonpos (by linarith : z - 1 / 2 ≤ 0)]
      ring
    have habsy : |y| = (1 / 2 + z) / δ := by
      rw [hyval, abs_div, abs_of_pos hδ, abs_of_nonneg (by linarith : (0:ℝ) ≤ z + 1 / 2)]
      ring
    have hint2 : (∫ t in (0:ℝ)..δ, e (y * t))
        = (e (x * δ) - 1) / (2 * (Real.pi : ℂ) * Complex.I * ((y : ℝ) : ℂ)) := by
      rw [intervalIntegral_e_eq δ hyne]
      congr 2
      rw [show y * δ = x * δ + 1 by rw [hxz, hyz]; ring, e_add,
        show e 1 = 1 by simpa using e_intCast 1, mul_one]
    have hfac : (A : ℂ) * ((e (x * δ) - 1) / (2 * (Real.pi : ℂ) * Complex.I * ((x : ℝ) : ℂ))
          - (e (x * δ) - 1) / (2 * (Real.pi : ℂ) * Complex.I * ((y : ℝ) : ℂ)))
        = ((A * (y - x) : ℝ) : ℂ) * (e (x * δ) - 1)
            / (((2 * Real.pi * x * y : ℝ) : ℂ) * Complex.I) := by
      push_cast
      field_simp
    have hAabs : |A| = A := abs_of_nonneg hA0.le
    have hyxabs : |y - x| = δ⁻¹ := by rw [hdx]; exact abs_of_nonneg (by positivity)
    have h2abs : |(2:ℝ)| = 2 := by norm_num
    have hpiabs : |Real.pi| = Real.pi := abs_of_nonneg Real.pi_pos.le
    have hval : ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖
        = s * Real.cos (Real.pi * z) / (Real.pi * ((1 / 2 - z) * (1 / 2 + z))) := by
      rw [hEq, intervalIntegral_e_eq δ hxne, hint2, hfac]
      simp only [norm_div, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
        mul_one]
      rw [hW, hAabs, hyxabs, h2abs, hpiabs, habsx, habsy, hAdef]
      field_simp
    set v : ℝ := 1 / 2 - |z| with hvdef
    clear_value v
    have hcos : Real.sin (Real.pi * v) = Real.cos (Real.pi * z) := by
      have h1 : Real.pi * |z| = |Real.pi * z| := by
        rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
      rw [hvdef, show Real.pi * (1 / 2 - |z|) = Real.pi / 2 - Real.pi * |z| by ring,
        Real.sin_pi_div_two_sub, h1, Real.cos_abs]
    have hquad : v * (1 - v) = (1 / 2 - z) * (1 / 2 + z) := by
      have h := sq_abs z
      rw [hvdef]; linear_combination -h
    have hkey := band_sin_ineq (s := s) (v := v) hs0 hs34 hs1
      (by rw [hvdef, hs2]; linarith) (by rw [hvdef]; linarith)
      (by rw [hvdef]; linarith [abs_nonneg z])
    rw [hval, le_div_iff₀ (by positivity : (0:ℝ) < Real.pi * ((1 / 2 - z) * (1 / 2 + z))),
      one_mul, ← hquad, ← hcos]
    exact hkey
  exact ⟨ψ, hmem, hsupp, hmass, hcoef⟩

/-- **The Beurling–Selberg majorant EXISTS at every bandwidth `0 < δ ≤ 1` whenever the band
`(N − 1)δ` is at most `1`.** Sorry-free; strictly extends `selbergMajorant_of_small_band`.
It is `l2_concentration_of_band_le_one` run through `selbergMajorant_of_concentration`. -/
theorem selbergMajorant_of_band_le_one (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hband : ((N:ℝ) - 1) * δ ≤ 1) : Nonempty (SelbergMajorant N δ) := by
  obtain ⟨ψ, hmem, hsupp, hnorm, hcoef⟩ := l2_concentration_of_band_le_one N hδ hδ1 hband
  exact selbergMajorant_of_concentration N hδ hδ1 hmem hsupp hnorm hcoef

/-- **(C) at `δ = 1`, for EVERY `N` — PROVED, with Parseval exact.**

At the top of the allowed range of bandwidths the problem trivialises in the direction
opposite to the small band: `{e(nt)}_{n∈ℤ}` is *orthonormal* on `(0, 1]`, so

  `ψ := (Σ_{n=1}^N e(nt))·𝟙_{(0,1]}`

has `ψ̂(n) = 1` exactly for every `1 ≤ n ≤ N`, and mass exactly `N = N − 1 + 1⁻¹` — the
budget, with no slack whatsoever.

This is the second anchor of `l2_concentration_exists`, complementary to
`l2_concentration_of_band_le_one`: it is the one bandwidth at which the band
`L := (N−1)δ = N−1` is *unbounded* and (C) is nevertheless settled. It is also the case
where the budget is provably tight — Parseval forces `∫₀^1|ψ|² ≥ Σ_{n=1}^N|ψ̂(n)|² ≥ N` for
any competitor — which is the concrete evidence that `l2_concentration_exists` is a sharp
statement and not a slack one.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` and `δ` are unrelated. -/
theorem l2_concentration_of_delta_one (N : ℕ) {δ : ℝ} (hδone : δ = 1) :
    ∃ ψ : ℝ → ℂ, MemLp ψ 2 volume ∧ (∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0) ∧
      (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) = (N:ℝ) - 1 + δ⁻¹ ∧
      (∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
        1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖) := by
  subst hδone
  -- the orthonormality of `{e(kt)}` on `(0,1]`
  have hkey : ∀ k : ℤ, (∫ t in (0:ℝ)..(1:ℝ), e ((k:ℝ) * t)) = if k = 0 then 1 else 0 := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg hk]
      exact intervalIntegral_e_orth (k := k) (Int.cast_ne_zero.mpr hk) (mul_one _)
  have hc1 : ∀ w : ℝ, IntervalIntegrable (fun t : ℝ => e (w * t)) volume 0 1 := fun w =>
    (continuous_e.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hcsum : ∀ (T : Finset ℕ) (g : ℕ → ℝ),
      IntervalIntegrable (fun t : ℝ => ∑ k ∈ T, e (g k * t)) volume 0 1 := by
    intro T g
    exact (continuous_finsetSum T fun k _ =>
      continuous_e.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  set S : ℝ → ℂ := fun t => ∑ m ∈ Finset.Icc 1 N, e ((m:ℝ) * t) with hSdef
  have hScont : Continuous S := by
    rw [hSdef]
    exact continuous_finsetSum _ fun m _ =>
      continuous_e.comp (continuous_const.mul continuous_id)
  have hSbound : ∀ t : ℝ, ‖S t‖ ≤ (N:ℝ) := by
    intro t
    calc ‖S t‖ ≤ ∑ m ∈ Finset.Icc 1 N, ‖e ((m:ℝ) * t)‖ := by
          rw [hSdef]; exact norm_sum_le _ _
      _ = (N:ℝ) := by simp [norm_e, Nat.card_Icc]
  -- MASS: `∫₀¹ |S|² = N` by orthonormality
  have hmassaux : (∫ t in (0:ℝ)..(1:ℝ), ‖S t‖ ^ 2) = (N:ℝ) := by
    have hpt : ∀ t : ℝ, ((‖S t‖ ^ 2 : ℝ) : ℂ)
        = ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            e ((((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t) := by
      intro t
      rw [Complex.ofReal_pow, (Complex.mul_conj' (S t)).symm]
      simp only [hSdef, map_sum, conj_e]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      rw [← e_add]; congr 1; push_cast; ring
    have hcast : ((∫ t in (0:ℝ)..(1:ℝ), ‖S t‖ ^ 2 : ℝ) : ℂ) = ((N:ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      simp only [hpt]
      rw [intervalIntegral.integral_finsetSum
        (f := fun (m : ℕ) (t : ℝ) =>
          ∑ k ∈ Finset.Icc 1 N, e ((((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t))
        (fun m _ => hcsum (Finset.Icc 1 N) (fun k => (((m:ℤ) - (k:ℤ) : ℤ) : ℝ)))]
      have hinner : ∀ m ∈ Finset.Icc 1 N,
          (∫ t in (0:ℝ)..(1:ℝ), ∑ k ∈ Finset.Icc 1 N, e ((((m:ℤ) - (k:ℤ) : ℤ) : ℝ) * t))
            = 1 := by
        intro m hm
        rw [intervalIntegral.integral_finsetSum (fun k _ => hc1 _)]
        simp only [hkey]
        rw [Finset.sum_eq_single_of_mem m hm (fun b _ hbne => if_neg (by omega))]
        simp
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, Nat.card_Icc]
      simp
    exact_mod_cast hcast
  -- COEFFICIENTS: `Ŝ(n) = 1` for `1 ≤ n ≤ N`
  have hcoefaux : ∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
      (∫ t in (0:ℝ)..(1:ℝ), S t * e (-((n:ℝ) * t))) = 1 := by
    intro n hn1 hn2
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, (n₀ : ℤ) = n :=
      ⟨n.toNat, Int.toNat_of_nonneg (by linarith)⟩
    have hmem : n₀ ∈ Finset.Icc 1 N := by rw [Finset.mem_Icc]; omega
    have hpt : ∀ t : ℝ, S t * e (-((n:ℝ) * t))
        = ∑ m ∈ Finset.Icc 1 N, e ((((m:ℤ) - n : ℤ) : ℝ) * t) := by
      intro t
      simp only [hSdef, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← e_add]; congr 1; push_cast; ring
    simp only [hpt]
    rw [intervalIntegral.integral_finsetSum (fun m _ => hc1 _)]
    simp only [hkey]
    rw [Finset.sum_eq_single_of_mem n₀ hmem (fun b _ hbne => if_neg (by omega))]
    simp [hn₀]
  refine ⟨Set.indicator (Set.Ioc (0:ℝ) 1) S, ?_, ?_, ?_, ?_⟩
  · refine (memLp_indicator_iff_restrict measurableSet_Ioc).mpr ?_
    refine MemLp.of_bound hScont.aestronglyMeasurable (N:ℝ) ?_
    filter_upwards with t
    exact hSbound t
  · intro t ht
    exact Set.indicator_of_notMem ht _
  · have hcongr : (∫ t in (0:ℝ)..(1:ℝ), ‖Set.indicator (Set.Ioc (0:ℝ) 1) S t‖ ^ 2)
        = ∫ t in (0:ℝ)..(1:ℝ), ‖S t‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_of_le zero_le_one]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [Set.indicator_of_mem ht]
    rw [hcongr, hmassaux]
    norm_num
  · intro n hn1 hn2
    have hcongr : (∫ t in (0:ℝ)..(1:ℝ),
          Set.indicator (Set.Ioc (0:ℝ) 1) S t * e (-((n:ℝ) * t)))
        = ∫ t in (0:ℝ)..(1:ℝ), S t * e (-((n:ℝ) * t)) := by
      rw [intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_of_le zero_le_one]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [Set.indicator_of_mem ht]
    rw [hcongr, hcoefaux n hn1 hn2, norm_one]

/-- **The Beurling–Selberg majorant EXISTS at `δ = 1` for every `N`.** Sorry-free; the
`δ = 1` companion of `selbergMajorant_of_band_le_one`, and the only `SelbergMajorant`
existence statement in this file whose band `(N − 1)δ` is unbounded. -/
theorem selbergMajorant_of_delta_one (N : ℕ) : Nonempty (SelbergMajorant N 1) := by
  obtain ⟨ψ, hmem, hsupp, hnorm, hcoef⟩ := l2_concentration_of_delta_one N (rfl : (1:ℝ) = 1)
  exact selbergMajorant_of_concentration N one_pos le_rfl hmem hsupp hnorm hcoef

/-! ##### How sharp (C) is: an exact matching lower bound at `δ = 1/q`

The two proved anchors both hit the budget `N − 1 + δ⁻¹` with *equality*, which raises the
question of how much slack a general construction may hope for. The answer, proved below, is
**none at all on an infinite family of parameters interior to the residue**, and the proof is
a sublattice Parseval identity that costs nothing.

Fix `q : ℕ`, `q ≥ 1`, and take `δ := q⁻¹`. For each residue `r` the modulated lattice
`{√q · e((r + kq)t)}_{k ∈ ℤ}` is an ORTHONORMAL BASIS of `L²(0, q⁻¹]` — the frequency gap is
`q = δ⁻¹`. Parseval in that basis reads

  `∫₀^{1/q} |ψ|² = q · Σ_{k ∈ ℤ} |ψ̂(r + kq)|²`   for every `r : ℤ`,

i.e. the mass is recovered *from each residue class separately*. Taking `r = 1` and keeping
only the `k` with `1 + kq ∈ [1, N]` gives `∫|ψ|² ≥ q · #{k ≥ 0 : 1 + kq ≤ N}`. When
`N = qm + 1` that count is exactly `m + 1`, so

  `∫₀^{1/q}|ψ|² ≥ q(m + 1) = (N − 1) + q = N − 1 + δ⁻¹` — **the budget, exactly.**

So at every `(N, δ) = (qm + 1, q⁻¹)` the mass in (C) is not merely achievable, it is
*forced*: no witness can come in under budget, and `l2_concentration_of_le`'s rescaling trick
has zero room to work with. This family sits strictly inside the residue as soon as
`m ≥ 2` (then `(N − 1)δ = m > 1` and `δ = q⁻¹ < 1` for `q ≥ 2`), e.g. `(N, δ) = (5, 1/2)`,
`(7, 1/3)`, `(9, 1/2)`, `(11, 1/5)`, `(21, 1/10)`. `q = 1` recovers
`l2_concentration_of_delta_one`'s tightness, and `m = 1` recovers the equality case `L = 1`
of `l2_concentration_of_band_le_one`; both are now special cases of one lemma. -/

/-- The Fourier coefficient of `ψ(t)·e(−t)` on `[0, q⁻¹]` at index `k` is `q` times the
`(1 + kq)`-th coefficient of `ψ` on that interval. This is the only computation needed to
run Parseval along the residue class `1 mod q`, and it is where `δ⁻¹ = q` is used: the
lattice `AddCircle q⁻¹` sees the frequency `k/δ = kq`. -/
theorem fourierCoeffOn_inv_nat_eq_e (q : ℕ) (hδ : (0:ℝ) < ((q:ℝ))⁻¹) (ψ : ℝ → ℂ) (k : ℤ) :
    fourierCoeffOn hδ (fun t => ψ t * e (-t)) k
      = ((q:ℝ)) • ∫ t in (0:ℝ)..((q:ℝ))⁻¹,
          ψ t * e (-((((1 + k * (q:ℤ)) : ℤ) : ℝ) * t)) := by
  have hq0 : ((q:ℝ)) ≠ 0 := by
    rcases eq_or_ne ((q:ℝ)) 0 with h | h
    · rw [h] at hδ; simp at hδ
    · exact h
  rw [fourierCoeffOn_eq_integral]
  have harg : ∀ x : ℝ,
      (2 * (Real.pi : ℂ) * Complex.I * ((-k : ℤ) : ℂ) * (x : ℂ)) / ((((q:ℝ))⁻¹ - 0 : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * ((-((k : ℝ) * (q:ℝ) * x) : ℝ) : ℂ) := by
    intro x
    have h1 : ((((q:ℝ))⁻¹ - 0 : ℝ) : ℂ) = ((q:ℂ))⁻¹ := by push_cast; ring
    rw [h1, div_eq_mul_inv, inv_inv]
    push_cast
    ring
  have key : ∀ x : ℝ, (fourier (-k) (x : AddCircle (((q:ℝ))⁻¹ - 0)) : ℂ) • (ψ x * e (-x))
      = ψ x * e (-((((1 + k * (q:ℤ)) : ℤ) : ℝ) * x)) := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul, harg x,
      show Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-((k : ℝ) * (q:ℝ) * x) : ℝ) : ℂ))
          = e (-((k : ℝ) * (q:ℝ) * x)) from rfl,
      show -((((1 + k * (q:ℤ)) : ℤ) : ℝ) * x) = -((k : ℝ) * (q:ℝ) * x) + -x by push_cast; ring,
      e_add]
    ring
  simp only [key]
  rw [sub_zero, one_div, inv_inv]

/-- **(C) IS EXACTLY SHARP AT `δ = 1/q` WHEN `q ∣ N − 1` — a matching lower bound.**

Every `ψ` supported in `(0, q⁻¹]` whose Fourier coefficients satisfy `|ψ̂(n)| ≥ 1` for
`1 ≤ n ≤ qm + 1` has `∫₀^{1/q}|ψ|² ≥ q(m + 1)`, which is precisely the budget
`N − 1 + δ⁻¹` at `N = qm + 1`, `δ = q⁻¹`. Proof: Parseval along the single residue class
`1 mod q`, using that `{√q·e((1 + kq)t)}_{k∈ℤ}` is an orthonormal basis of `L²(0, q⁻¹]`.

Consequences recorded in the section note above and in `l2_concentration_exists`'s
docstring: the budget of (C) is attained with equality on an infinite family of points
*interior to the residue*, so no approximate or lossy construction can ever discharge a
neighbourhood of one of them.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`. -/
theorem l2_concentration_mass_ge (q m : ℕ) (hq : 0 < q) {ψ : ℝ → ℂ}
    (hmem : MemLp ψ 2 volume)
    (hcoef : ∀ n : ℤ, 1 ≤ n → n ≤ ((q * m + 1 : ℕ) : ℤ) →
      1 ≤ ‖∫ t in (0:ℝ)..((q:ℝ))⁻¹, ψ t * e (-((n:ℝ) * t))‖) :
    ((q:ℝ)) * ((m:ℝ) + 1) ≤ ∫ t in (0:ℝ)..((q:ℝ))⁻¹, ‖ψ t‖ ^ 2 := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hδ : (0:ℝ) < ((q:ℝ))⁻¹ := inv_pos.mpr hqR
  set δ : ℝ := ((q:ℝ))⁻¹ with hδdef
  set φ : ℝ → ℂ := fun t => ψ t * e (-t) with hφdef
  set d : ℤ → ℂ := fun k => ∫ t in (0:ℝ)..δ,
    ψ t * e (-((((1 + k * (q:ℤ)) : ℤ) : ℝ) * t)) with hddef
  -- `φ` is `L²` on `(0, δ]`, with the same pointwise norm as `ψ`
  have hnormφ : ∀ t : ℝ, ‖φ t‖ = ‖ψ t‖ := by
    intro t; rw [hφdef]; simp only [norm_mul, norm_e, mul_one]
  have hψr : MemLp ψ 2 (volume.restrict (Set.Ioc (0:ℝ) δ)) := hmem.restrict _
  have hφmeas : AEStronglyMeasurable φ (volume.restrict (Set.Ioc (0:ℝ) δ)) := by
    have hcont : Continuous fun t : ℝ => e (-t) := continuous_e.comp continuous_neg
    rw [hφdef]
    exact hψr.1.mul hcont.aestronglyMeasurable
  have hφr : MemLp φ 2 (volume.restrict (Set.Ioc (0:ℝ) δ)) :=
    hψr.of_le hφmeas (Filter.Eventually.of_forall fun t => le_of_eq (hnormφ t))
  -- the coefficients of `φ` on `[0, δ]` are `q · d k`
  have hcf : ∀ k : ℤ, fourierCoeffOn hδ φ k = ((q:ℝ)) • d k :=
    fun k => fourierCoeffOn_inv_nat_eq_e q hδ ψ k
  have hnormcf : ∀ k : ℤ, ‖fourierCoeffOn hδ φ k‖ ^ 2 = (q:ℝ) ^ 2 * ‖d k‖ ^ 2 := by
    intro k
    rw [hcf k, norm_smul, Real.norm_eq_abs, abs_of_pos hqR, mul_pow]
  -- Parseval on `[0, δ]`
  have hpars := tsum_sq_fourierCoeffOn hδ hφr
  have hmassφ : (∫ x in (0:ℝ)..δ, ‖φ x‖ ^ 2) = ∫ x in (0:ℝ)..δ, ‖ψ x‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hnormφ t]
  have hinv : (δ - 0)⁻¹ = (q:ℝ) := by rw [sub_zero, hδdef, inv_inv]
  rw [hmassφ, hinv] at hpars
  simp only [hnormcf] at hpars
  -- summability of the squared coefficients of `ψ` along the class `1 mod q`
  have hsum0 : Summable fun k : ℤ => (q:ℝ) ^ 2 * ‖d k‖ ^ 2 := by
    have h := (hasSum_sq_fourierCoeffOn hδ hφr).summable
    simpa only [hnormcf] using h
  have hsumd : Summable fun k : ℤ => ‖d k‖ ^ 2 := by
    have h := hsum0.mul_left ((q:ℝ) ^ 2)⁻¹
    refine h.congr fun k => ?_
    field_simp
  rw [tsum_mul_left] at hpars
  -- the mass is `q` times the class sum
  have hmass : (∫ x in (0:ℝ)..δ, ‖ψ x‖ ^ 2) = (q:ℝ) * ∑' k : ℤ, ‖d k‖ ^ 2 := by
    rw [smul_eq_mul] at hpars
    have hstep : (q:ℝ) * ((q:ℝ) * ∑' k : ℤ, ‖d k‖ ^ 2)
        = (q:ℝ) * ∫ x in (0:ℝ)..δ, ‖ψ x‖ ^ 2 := by
      rw [← hpars]; ring
    exact (mul_left_cancel₀ (ne_of_gt hqR) hstep).symm
  -- each of the `m + 1` terms with `1 + kq ∈ [1, N]` is at least `1`
  have hterm : ∀ k : ℤ, k ∈ Finset.Icc (0:ℤ) (m:ℤ) → (1:ℝ) ≤ ‖d k‖ ^ 2 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hqZ : (0:ℤ) < (q:ℤ) := by exact_mod_cast hq
    have h1 : (1:ℤ) ≤ 1 + k * (q:ℤ) := by
      have : (0:ℤ) ≤ k * (q:ℤ) := mul_nonneg hk.1 hqZ.le
      linarith
    have h2 : 1 + k * (q:ℤ) ≤ ((q * m + 1 : ℕ) : ℤ) := by
      have hkm : k * (q:ℤ) ≤ (m:ℤ) * (q:ℤ) :=
        mul_le_mul_of_nonneg_right hk.2 hqZ.le
      push_cast
      linarith [hkm]
    have hc := hcoef (1 + k * (q:ℤ)) h1 h2
    have hdk : ‖d k‖
        = ‖∫ t in (0:ℝ)..δ, ψ t * e (-((((1 + k * (q:ℤ)) : ℤ) : ℝ) * t))‖ := rfl
    rw [hdk]
    nlinarith [norm_nonneg (∫ t in (0:ℝ)..δ,
      ψ t * e (-((((1 + k * (q:ℤ)) : ℤ) : ℝ) * t))), hc]
  have hcard : ((Finset.Icc (0:ℤ) (m:ℤ)).card : ℝ) = (m:ℝ) + 1 := by
    have hc2 : ((m:ℤ) + 1 - 0).toNat = m + 1 := by omega
    rw [Int.card_Icc, hc2]
    push_cast
    ring
  have hlow : ((m:ℝ) + 1) ≤ ∑' k : ℤ, ‖d k‖ ^ 2 := by
    have hfin : ((m:ℝ) + 1) ≤ ∑ k ∈ Finset.Icc (0:ℤ) (m:ℤ), ‖d k‖ ^ 2 := by
      calc ((m:ℝ) + 1) = ∑ _k ∈ Finset.Icc (0:ℤ) (m:ℤ), (1:ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
        _ ≤ ∑ k ∈ Finset.Icc (0:ℤ) (m:ℤ), ‖d k‖ ^ 2 :=
            Finset.sum_le_sum hterm
    refine hfin.trans ?_
    exact hsumd.sum_le_tsum _ (fun k _ => sq_nonneg _)
  rw [hmass]
  exact mul_le_mul_of_nonneg_left hlow hqR.le

/-- **NO WITNESS OF (C) CAN COME IN UNDER BUDGET AT `δ = 1/q`, `N = qm + 1`.** The `<` form of
the mass condition of `l2_concentration_exists` is refutable at every such pair — machine-checked
counterpart of `sharpAdditiveLargeSieveUnrestricted_false`, but here it is the *statement being
sharp*, not an encoding error.

Instantiating at `q = 2, m = 2` gives `(N, δ) = (5, 1/2)`, which lies strictly inside the residue
`δ < 1 ∧ (N − 1)δ > 1` of `l2_concentration_exists` (there `(N − 1)δ = 2`). So the residue
contains points at which the budget `N − 1 + δ⁻¹` is *exactly* the minimum, and therefore no
construction with any loss at all — however small, however local — can discharge a neighbourhood
of one of them. This is the precise reason the band `(N − 1)δ ≤ 1` of
`l2_concentration_of_band_le_one` cannot be widened by any elementary family; see
`l2_concentration_exists`'s docstring.

Note that no support hypothesis on `ψ` is needed: the mass and the coefficients in (C) are both
integrals over `(0, δ]`, so the lower bound is a statement about `ψ|_{(0,δ]}` alone. -/
theorem l2_concentration_no_cheaper (q m : ℕ) (hq : 0 < q) :
    ¬ ∃ ψ : ℝ → ℂ, MemLp ψ 2 volume ∧
      (∫ t in (0:ℝ)..((q:ℝ))⁻¹, ‖ψ t‖ ^ 2) < ((q * m + 1 : ℕ) : ℝ) - 1 + (((q:ℝ))⁻¹)⁻¹ ∧
      (∀ n : ℤ, 1 ≤ n → n ≤ ((q * m + 1 : ℕ) : ℤ) →
        1 ≤ ‖∫ t in (0:ℝ)..((q:ℝ))⁻¹, ψ t * e (-((n:ℝ) * t))‖) := by
  rintro ⟨ψ, hmem, hlt, hcoef⟩
  have hbud : ((q * m + 1 : ℕ) : ℝ) - 1 + (((q:ℝ))⁻¹)⁻¹ = (q:ℝ) * ((m:ℝ) + 1) := by
    rw [inv_inv]
    push_cast
    ring
  rw [hbud] at hlt
  linarith [l2_concentration_mass_ge q m hq hmem hcoef]

/-- **(C) THE `L²` CONCENTRATION PROBLEM — the single remaining from-zero gap of §6.**

For `0 < δ ≤ 1` and any `N`, there is `ψ ∈ L²(ℝ)` supported in `(0, δ]` with

  `∫₀^δ |ψ|² = N − 1 + δ⁻¹`  and  `|∫₀^δ ψ(t)e(−nt) dt| ≥ 1` for every `1 ≤ n ≤ N`.

This is exactly statement **(C)** of `selberg_majorant_of_lt_half`'s docstring, and by
`selbergMajorant_of_concentration` (proved above) it is now *equivalent* to the existence of
the Beurling–Selberg majorant: nothing else is missing from Lemma 6.1.

Depends on: nothing. Literature: Selberg; Beurling; [IK, Thm 7.7]; [Va, Thm 3]; Vaaler.

**What is and is not left.** Parseval forces `∫₀^δ|ψ|² = Σ_{n∈ℤ}|ψ̂(n)|² ≥ N`, and
`N − 1 + δ⁻¹ ≥ N` exactly because `δ ≤ 1`; so (C) is sharp and cannot be met by a cheap
`ψ`. **What is proved is:**
* the whole band `L := (N − 1)δ ≤ 1` — `l2_concentration_of_band_le_one`, explicit witness,
  `N` arbitrary, mass exactly on budget. It subsumes `l2_concentration_of_small_band`
  (`L ≤ 1/2`) and hence `l2_concentration_of_le_one` (`N ≤ 1`, i.e. `L = 0`);
* the whole bandwidth `δ = 1`, at every `N` and hence with `L = N − 1` UNBOUNDED —
  `l2_concentration_of_delta_one`, witness `Σ_{n=1}^N e(nt)·𝟙_{(0,1]}`, orthonormal, with
  Parseval exact and the budget provably tight.

**What is left is exactly `(N − 1)δ > 1` together with `δ < 1`** — the proof below
discharges the other two branches, so the residual `sorry` sees only that corner. The
extremal `ψ` there is the Krein/Fejér–Riesz square root of Selberg's own majorant. Note that
this residue reaches *arbitrarily small* `δ` (for every `N ≥ 4` it contains
`δ ∈ (1/(N−1), 1)`), and the small-`δ` end is the hard one: there the `N` constraint points
are dense in the band and the problem degenerates to the continuum extremal problem.

**Only the part of this statement with `δ < 1/2` is load-bearing.** The consumer is
`selberg_majorant_of_lt_half`; `selberg_majorant_exists` discharges `1/2 ≤ δ ≤ 1`
unconditionally through `selberg_majorant_of_half_le`. So the slice of the residue that
Lemma 6.1 actually needs is `N ≥ 4` together with `1/(N−1) < δ < 1/2` — which is, however,
exactly the harder (small-`δ`, near-continuum) half of it.

**(C) is true.** Selberg's majorant `f` of `𝟙_{[1,N]}` is entire of exponential type `2πδ`,
`f ≥ 𝟙_{[1,N]} ≥ 0`, `f ∈ L¹` and `∫f = (N−1) + δ⁻¹`. Krein/Fejér–Riesz factors it as
`f = |h|²` with `h` entire of type `πδ` in `L²`, and Paley–Wiener gives `h = ĝ` with
`g ∈ L²` supported in an interval of length `δ`; translating `g` onto `(0,δ]` yields `ψ`,
with `ψ̂(n) = ĝ(n)` (legitimate because `δ ≤ 1`), `|ψ̂(n)|² = f(n) ≥ 1` on `[1,N]`, and
`∫₀^δ|ψ|² = ‖g‖² = ∫f` by Plancherel. So the remaining work is a *construction*, not a
search: there is no risk that this statement is the false one.

**Two remarks that shorten the remaining work.** Remark 1 is now MACHINE-CHECKED; remark 2
is still on paper.
1. *Only `≤` is really needed in the mass condition, provided `1 ≤ N`* — **PROVED, as
   `l2_concentration_of_le`.** If `ψ` satisfies the coefficient bounds with
   `V := ∫₀^δ|ψ|² ≤ N − 1 + δ⁻¹`, then `V > 0` (else `ψ̂(1) = 0`), and `√((N−1+δ⁻¹)/V)·ψ`
   satisfies (C) verbatim — scaling by a factor `≥ 1` preserves `|ψ̂(n)| ≥ 1`. So an
   approximate construction suffices, as long as it does not overshoot. Cite that lemma;
   do not redo this.
2. *Rescaling removes `δ`.* Writing `ψ(t) = δ⁻¹u(t/δ)` with `u ∈ L²(0,1]` turns (C) into:
   find `u` with `‖u‖²_{L²(0,1]} = 1 + (N−1)δ` and `|û(nδ)| ≥ 1` for `1 ≤ n ≤ N`, where
   `û(ξ) = ∫₀¹ u(s)e(−ξs) ds`. The `N` constrained frequencies are equally spaced by `δ` in
   a band of length `L := (N−1)δ`, and the budget is exactly `1 + L`. In that form the
   statement is Selberg's theorem with `δ` scaled out of it entirely. (Not formalised: the
   `MemLp` transfer along `t ↦ t/δ` needs `Real.map_volume_mul_left` plumbing.)

--------------------------------------------------------------------------------------
**FINDING: there is NO shortcut through the point constraints —
the residue is genuinely Selberg's extremal problem, and its cost is `L`, not `L²`.**
--------------------------------------------------------------------------------------

It is tempting to hope that constraining `f := |ψ̂|²` at the `N` *integers* `1..N` is much
weaker than Selberg's `f ≥ 𝟙_{[1,N]}` on the whole interval, and so admits a cheaper `f`.
It is not. `f` is nonnegative of exponential type `2πδ`, so by Bernstein it varies on scale
`δ⁻¹ ≥ 1`, i.e. slowly compared with the spacing `1` of the constraint points: `f(n) ≥ 1`
for `n = 1..N` already forces `f ≳ 1` throughout `[1, N]`, and the extremal value of `∫f` is
Selberg's `N − 1 + δ⁻¹` all the same. Concretely, in the rescaled picture of remark 2 the
minimum of `‖u‖²` grows **linearly** in the band length `L = (N−1)δ`, with slope exactly 1
and intercept exactly 1 — which is why the budget is `1 + L` and why no construction can be
sloppy by more than `o(1)` per unit of band.

Two consequences, recorded so they are not re-derived.
* **Minimum-norm interpolation is the modulation ansatz.** For prescribed values
  `ψ̂(n) = c_n`, `n = 1..N`, the minimising `ψ` supported on `(0, δ]` lies in the span of
  `{e(nt)}_{n=1}^N`, with `‖ψ‖² = c*G⁻¹c` for the Toeplitz Gram matrix
  `G_{mn} = ∫₀^δ e((m−n)t) dt = δ·e^{πi(m−n)δ}·sinc((m−n)δ)`. So (C) is *equivalent* to a
  finite-dimensional statement: `∃ c ∈ ℂ^N, (∀ n, |c_n| ≥ 1) ∧ c*G⁻¹c ≤ N − 1 + δ⁻¹`.
  **The phases of `c` are the whole content.** At `N = 2` the phase-optimal value is
  `2/(δ + sin(πδ)/π)`, and `2/(δ + sin(πδ)/π) ≤ 1 + δ⁻¹` reduces to
  `δ(1 − δ) ≤ (1 + δ)·sin(πδ)/π`, which holds on `(0, 1]` — so (C) is satisfiable there
  with room. The naive `c = 𝟙`, by contrast, gives `2δ/(δ² − (sin(πδ)/π)²)`, i.e. `≈ 6.73`
  at `δ = 1/2` against a budget of `3`: it fails by more than a factor of two.
  Asymptotically the optimal phases are quadratic in `n` — a chirp — which is the same
  object as Selberg's majorant seen through Krein's factorisation.
* **`L ≤ 1` is the honest limit of the elementary (equal-moduli) method — this is now a
  theorem plus a numerical check, not a guess.** A SINGLE modulation loses `π²L²/24` to the
  second-order (cosine) term against an available slack of `√(1+L) − 1 ≈ L/2`, so it survives
  only while `L = O(1)`: the threshold `1/2` in `l2_concentration_of_small_band` is Mathlib's
  `Real.sin_gt_sub_cube` being spent, and a sharper trig bound would push it only to
  `L ≈ 0.83`. TWO orthogonal modulations at frequency gap `δ⁻¹` reach exactly `L ≤ 1`
  (`l2_concentration_of_band_le_one`), with equality of every constraint at `L = 1`. That is
  the END of the family, and the reason is structural: in the `c`-picture of the previous
  bullet — `ψ = δ⁻¹Σ_k c_k e(kt/δ)`, `|F(y_n)| ≥ 1` with
  `F(y) = (sin πy/π)Σ_k c_k/(y+k)` and `Σ_k|c_k|² ≤ 1 + L` — the `K`-term truncation of the
  exact solution `c_k = (−1)^k` (which gives `F ≡ 1` at infinite energy) has `|F(−j)| = |c_j|`
  at each of the `K` integers inside its window, so it needs `|c_j| ≥ 1` there, i.e.
  `K ≤ 1 + L`; combined with the window length `K − 1 ≥ L` this pins `L = K − 1` for every
  `K ≥ 3`. An *interval* of `L`'s is available only for `K = 2`, where the window `(−1, 0)`
  contains no integer. Numerical instance, so it is not re-derived: at `L = 1.5`, `K = 3`, the
  two endpoint constraints force `a_0 + a_2 ≥ 1.814` while the budget allows only
  `√(2·1.5) = 1.732`. Beyond `L = 1` the moduli `|c_k|` must stop being equal and the phases
  must become a chirp — which is precisely Selberg. The full derivation is in the section note
  above `l2_concentration_of_band_le_one`.

* **Why the pure linear chirp cannot replace Selberg** — the MECHANISM behind the third
  "heuristic dead end" of `selberg_majorant_of_lt_half`'s docstring, so that the entry is no
  longer merely indicative. Since the optimal phases are asymptotically quadratic, the
  obvious next attempt is `ψ := A·e(βt²)·𝟙_{(0,δ]}`, whose instantaneous frequency `2βt`
  sweeps the constrained band. Completing the square,
  `ψ̂(ξ) = A·e(−ξ²/4β)·(2β)^{−1/2}·(F(X) + F(Y))`, where `F(T) := ∫₀^T e^{πiv²} dv` and
  `X, Y ≥ 0` are the rescaled distances from the stationary point to the two ends of the
  sweep. Because `F(∞) = e^{iπ/4}/2`, a constraint point *interior* to the sweep gets
  `|F(X)+F(Y)| ≈ 1` — exactly right — while one at an *end* gets `≈ 1/2`, i.e. `|ψ̂|² ≈ 1/4`,
  short by a factor 4. Widening the sweep by `R` on each side until every constraint point is
  interior needs `R ≳ √(N/δ)`, and the mass becomes `N − 1 + 2R = N + Θ(√(N/δ))`, overshooting
  the budget's `δ⁻¹` for all large `N`. Selberg's `½(B(δ(a−z)) + B(δ(z−b)))` is precisely the
  fix — two one-sided pieces, each worth `1/2` in the interior and `1` at its own end — and
  the `δ⁻¹` in the budget is exactly the price of the two ends.
* **The residual corner was audited numerically and (C) holds there with room.** The
  finite-dimensional form of the first bullet was minimised directly (both as `c*G⁻¹c` over
  unit-modulus phase vectors and as the well-conditioned primal `b*Gb` subject to
  `|(Gb)_n| ≥ 1`) over `N ∈ {3,…,30}` and `δ ∈ {0.52,…,0.99}` restricted to the residue
  `(N−1)δ > 1`. In every instance the minimum came out just above `N` and strictly below the
  budget `N + (δ⁻¹ − 1)`; the worst ratio observed was `0.99` at `N = 3, δ = 0.52`.
  **AMENDED below: that sweep missed most of the residue, and its "worst point" is not the
  worst point — there are points of the residue with slack exactly `0`.**

--------------------------------------------------------------------------------------
**FINDING: THE BUDGET IS ATTAINED WITH EQUALITY INSIDE THE RESIDUE.
Consequently the band `(N − 1)δ ≤ 1` CANNOT be widened by any elementary family, and the
only remaining route is Selberg's extremal function itself. Machine-checked.**
--------------------------------------------------------------------------------------

1. **The sharpness theorem** (`l2_concentration_mass_ge`, and its contrapositive
   `l2_concentration_no_cheaper`, both sorry-free). At `δ = q⁻¹` with `q : ℕ`, the modulated
   lattice `{√q·e((r + kq)t)}_{k∈ℤ}` is an orthonormal basis of `L²(0, q⁻¹]` for *each*
   residue `r`, so Parseval recovers the mass from a single residue class:
   `∫₀^{1/q}|ψ|² = q·Σ_{k∈ℤ}|ψ̂(r + kq)|²`. Taking `r = 1` and `N = qm + 1`, the `m + 1`
   constrained frequencies `1, 1+q, …, 1+mq` already give
   `∫₀^{1/q}|ψ|² ≥ q(m + 1) = N − 1 + δ⁻¹` — **the budget exactly**. So at
   `(N, δ) = (qm + 1, q⁻¹)` the mass condition of (C) is *forced*, not merely achievable, and
   `l2_concentration_of_le`'s rescaling has zero room. This family sits strictly inside the
   residue for `q ≥ 2, m ≥ 2`: `(5, 1/2)`, `(7, 1/3)`, `(9, 1/2)`, `(11, 1/5)`, `(13, 1/6)`,
   `(21, 1/10)`, … . It also *explains* both proved anchors: `q = 1` is
   `l2_concentration_of_delta_one`'s tightness, `m = 1` is the equality case `L = 1` of
   `l2_concentration_of_band_le_one`.
2. **Hence no band widening.** Suppose some `c > 1` admitted an anchor "`(N−1)δ ≤ c ⟹ (C)`".
   * If `c ≥ 2`: item 1 applies *literally inside the band*, at every `(qm+1, q⁻¹)` with
     `2 ≤ m ≤ c` — infinitely many points, `q` arbitrary — and there the witness must meet the
     budget with **exact** equality. This half is machine-checked.
   * If `1 < c < 2`: item 1's points inside the band are only `m = 1`, i.e. the boundary
     `L = 1`. Here the obstruction is the continuum limit instead: fix `L ∈ (1, c]` and let
     `δ → 0` with `(N−1)δ = L`; the `N` constraint points become dense in the band, so the
     minimum tends to the continuum extremal value, which is exactly `1 + L` (Selberg's, and
     Selberg's is extremal). The witness must therefore be *asymptotically* extremal. This half
     rests on the classical extremality of Selberg's majorant, not on anything proved here.

   Either way **no truncation, no finite lattice family and no soft/inequality argument can
   produce such a witness.** The two proved anchors are exactly the two places where the
   extremal object happens to be finite. This supersedes the "L ≤ 1 is the honest limit of the
   equal-moduli method" bullet above: it is the honest limit of *every* elementary method.
3. **The Shannon form of (C), which is the cleanest statement of what is left.** Rescaling
   (remark 2) and expanding in the lattice basis, (C) is equivalent to: *find `R` band-limited
   to `[−1/2, 1/2]` (entire of exponential type `π`) with `‖R‖²_{L²(ℝ)} ≤ 1 + L` and
   `|R(w_n)| ≥ 1` at the `N` points `w_n = (n − β)δ`, `β` free.* Sampling is a bijection onto
   `ℓ²(ℤ)`: `R(w) = Σ_k b_k·sinc(w − k)` with `b_k = R(k)` and `‖R‖² = Σ_k|b_k|²`. The
   continuum version (`|R| ≥ 1` on the whole interval of length `L`) is *literally* Selberg's
   extremal problem, with extremal value exactly `1 + L` for every real `L`.
4. **Where the equal-moduli truncation really stops: `K ≤ 3`, i.e. `L ≤ 2`.** In the Shannon
   form the truncation of item 1's exact solution is `b_k = 1` on `k = 1..K`, i.e.
   `R(w) = Σ_{k=1}^{K}sinc(w − k)`. Then `min_{[1,K]}|R| = 1` (attained at the integers) for
   `K = 1, 2, 3`, but **fails for every `K ≥ 4`**: `R(5/2) = 0.848826` at `K = 4`,
   `R(3.658) = 0.971701` at `K = 5`, `R(4.5225) = 0.884923` at `K = 6`, …. So the elementary
   truncation settles the integer band `L = K − 1` only up to `L = 2`; from `L = 3` on, the
   extremal `b` is unimodular but genuinely *complex* (a discrete chirp), which is Selberg
   again. `L = 2` (`K = 3`) is a genuine, provable, but measure-zero extra point.
5. **Rank does not help, so `selbergMajorant_of_concentration` is NOT lossy.** The
   `SelbergMajorant` interface only asks `F ≥ 0`, not `F = |ψ̂|²`; the natural relaxation is
   therefore to a positive trace-class `Ψ` on `L²(0,δ]` with `⟨e_n, Ψ e_n⟩ ≥ 1` and
   `tr Ψ = N − 1 + δ⁻¹` — an SDP, `min tr(TX)` over `X ⪰ 0` with `(TXT)_{nn} ≥ 1`, of which
   the concentration problem is the rank-one case. Solved numerically, **the SDP value equals
   the rank-one minimum at every point tested** (`N = 3..20`, `δ` across the whole residue).
   So there is no cheaper route to `selberg_majorant_of_lt_half` through a non-square `F`, and
   nothing is lost by going through `ψ`.
6. **The audit redone over the whole residue.** The residue is `δ < 1 ∧ δ > 1/(N−1)`, which
   for `N ≥ 4` reaches *arbitrarily small* `δ` — the earlier sweep `δ ∈ {0.52,…,0.99}` never
   touched it, and small `δ` is the hard (continuum) end. Redone with the SDP of item 5 over
   `N ∈ {3,…,40}` and `δ` from just above `1/(N−1)` up to `0.99` (94 instances): every one
   feasible, no counterexample, minimum slack `0.0101` at `δ = 0.99` (where
   `budget − N = δ⁻¹ − 1 = 0.0101` and the minimum is exactly `N`). Slack is largest,
   `≈ 0.3–0.8`, for `δ ∈ [0.55, 0.7]`, and shrinks to `0` at the tight points of item 1.
7. **Even the `N = 3` slice needs a sharp inequality.** For `N = 3` the optimum is attained at
   the unimodular `c = (e^{−iα}, 1, e^{iα})` with `cos α = s₁(1 − s₂)/(2(s₁² − s₂))`,
   `s_k := sin(πkδ)/(πkδ)`, giving a closed-form `‖R‖²(δ)`. Its slack against `1 + 2δ` is `0`
   at `δ = 1/2` and at `δ = 1` — both endpoints being exactly the proved anchors — and peaks at
   only `0.148` at `δ = 3/4`. So an `N = 3` anchor is a one-variable trig inequality that is an
   *equality at both ends of its range*; there is no slack to spend on crude bounds.

**What must actually be built**, in the order the analysis needs it:
Beurling's function `B = H + K` and `B ≥ sgn` with `∫(B − sgn) = 1`; Selberg's shift
`f(z) = ½(B(δ(a−z)) + B(δ(z−b)))` at `[a,b] = [1,N]`; the Krein (Fejér–Riesz) factorisation
`f = |h|²` for `f ≥ 0` entire of exponential type and integrable; Paley–Wiener to get
`h = ĝ` with `g ∈ L²` on an interval of length `δ`. Mathlib has none of these. This is the
one genuinely research-scale item left in Lemma 6.1, and it is orthogonal to everything
else in this file.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` and `δ` are unrelated. -/
theorem l2_concentration_exists (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ ψ : ℝ → ℂ, MemLp ψ 2 volume ∧ (∀ t, t ∉ Set.Ioc (0:ℝ) δ → ψ t = 0) ∧
      (∫ t in (0:ℝ)..δ, ‖ψ t‖ ^ 2) = (N:ℝ) - 1 + δ⁻¹ ∧
      (∀ n : ℤ, 1 ≤ n → n ≤ (N:ℤ) →
        1 ≤ ‖∫ t in (0:ℝ)..δ, ψ t * e (-((n:ℝ) * t))‖) := by
  -- Band `(N − 1)δ ≤ 1`: the two-modulation witness, at every bandwidth.
  rcases le_or_gt (((N:ℝ) - 1) * δ) 1 with hband | hband
  · exact l2_concentration_of_band_le_one N hδ hδ1 hband
  -- Bandwidth `δ = 1`: the orthonormal witness, at every `N` (band unbounded).
  by_cases hone : δ = 1
  · exact l2_concentration_of_delta_one N hone
  -- RESIDUE: `δ < 1` and `(N − 1)δ > 1` — Selberg proper. See the docstring.
  sorry

end Concentration

/-- **(I1a′) THE ONE REMAINING FROM-ZERO SORRY OF §6**, now confined to `δ < 1/2`.
Existence of the Beurling–Selberg majorant of the indicator of `(0, N]` at bandwidth `δ`,
in the only regime `selberg_majorant_of_half_le` does not already cover.

Paper §6. Literature: Beurling; Selberg; [IK, Thm 7.7]; [Va, Thm 3];
Vaaler, *Some extremal problems in Fourier analysis*.
Depends on: nothing.

--------------------------------------------------------------------------------------
**FINDING: the majorant is equivalent to an `L²` CONCENTRATION
problem on an interval of length `δ`, with no entire functions in it.**
--------------------------------------------------------------------------------------

The five fields only ever see `F` **at the integers**, so the classical route through an
entire function of exponential type `2πδ` (Beurling's `B`, Selberg's shift, Paley–Wiener
for `supp f̂ ⊆ [−δ, δ]`, Poisson summation) is not forced. Write everything on the circle
`ℝ/ℤ` instead. Let `ψ ∈ L²(ℝ/ℤ)` be supported in `[0, δ]` (legitimate: `δ ≤ 1`) and put

  `c n := ∫₀^δ ψ(t) e(−nt) dt`   (its Fourier coefficients),   `F n := |c n|²`.

Then **all five fields are automatic except one inequality**:
* `nonneg` — `F n = |c n|² ≥ 0`, by construction;
* `summable`, `total` — Parseval, `Σ_n |c n|² = ∫₀^δ |ψ|²`
  (Mathlib: `tsum_sq_fourierCoeffOn` / `hasSum_sq_fourierCoeffOn`, `AddCircle.lean`);
* `vanishing` — the sesquilinear Parseval identity
  `Σ_n |c n|² e(nα) = ∫₀¹ ψ(t) conj(ψ(t − α)) dt`, whose integrand is identically `0`
  as soon as `[0, δ]` and `α + [0, δ]` are disjoint mod `1`, i.e. exactly when
  `dist(α, ℤ) ≥ δ`. **Band-limitedness has become disjointness of supports.**

So the whole theorem reduces to the *concentration statement*

  **(C)** for `0 < δ ≤ 1` and `N : ℕ` there is `ψ ∈ L²[0, δ]` with `|ĉ(n)| ≥ 1` for
  `1 ≤ n ≤ N` and `∫₀^δ |ψ|² = N − 1 + δ⁻¹`.

(C) is not a weakening — the classical majorant already has this form. Selberg's `f` is
entire of exponential type `2πδ`, integrable and `≥ 0` on `ℝ`; by the Krein (Fejér–Riesz)
factorisation of a nonnegative entire function of exponential type, `f = |h|²` with `h`
entire of type `πδ` and `h ∈ L²`, so `h = ĝ` for some `g ∈ L²` supported in
`[−δ/2, δ/2]` (Paley–Wiener). Then `f(n) = |ĝ(n)|²`, `∫f = ‖g‖²` (Plancherel), and — since
`supp g` has length `δ ≤ 1` — the transform of `g` at the integers *is* its circle Fourier
coefficient sequence. Translating `g` to `[0, δ]` gives (C). Nor is (C) a strengthening:
`Σ_n |ĉ(n)|² = ‖ψ‖²` forces `‖ψ‖² ≥ N`, and `N − 1 + δ⁻¹ ≥ N` precisely because `δ ≤ 1`.

Two further remarks, recorded so they are not re-derived.

* **Worked case `N = 1`, sharp and explicit.** `ψ(t) := δ⁻¹ e(t)·𝟙_{[0,δ]}` gives
  `ĉ(1) = 1` (equality in Cauchy–Schwarz), `‖ψ‖² = δ⁻¹`, and
  `F n = (sin(πδ(n−1))/(πδ(n−1)))²` — the sampled Fejér kernel, i.e. Selberg's majorant of
  a point. This is a complete, sharp instance of (C).
* **Heuristic dead ends** (indicative computations, not theorems, listed only to stop them
  being retried): the plain indicator `ψ = c·𝟙_{[0,δ]}` normalised to `‖ψ‖² = δ⁻¹` gives
  `|ĉ(1)| = sin(πδ)/(πδ) < 1`, so it fails already at `N = 1`; a single modulation
  `ψ = c·e(μt)` can only hold `|ĉ(n)| ≥ 1` across a band of width `≲ δ⁻¹`, and paying for
  the worst `n ∈ [1, N]` overshoots `N − 1 + δ⁻¹`; and the linear chirp `ψ = c·e(βt²)`,
  whose stationary-phase cost `≈ N` is tantalisingly close to the budget, loses an extra
  `≈ √(N/δ)` to band-edge roll-off against an available slack of only `δ⁻¹ − 1`. The
  extremal `ψ` really is Selberg's; the remaining work is to write it down and verify (C).

  **AMENDED.** The first two entries above are too pessimistic, and
  the correction is now a theorem. It is the *centring* that matters: the modulated
  indicator `ψ = A·e(((N+1)/2)·t)·𝟙_{(0,δ]}` — modulated at the **midpoint** of `[1, N]`,
  not at `0` and not at an endpoint — makes the first-order phase cancel, and it solves (C)
  outright for every `N` with `L := (N − 1)δ ≤ 1/2` (`l2_concentration_of_small_band`,
  sorry-free); what kills it beyond that band is only the second-order loss `π²L²/24`
  against a slack `√(1+L) − 1 ≈ L/2`. A *difference of two* modulations, at the frequency
  gap `δ⁻¹` that makes them orthogonal on `(0, δ]`, then reaches the full band `L ≤ 1`
  (`l2_concentration_of_band_le_one`, sorry-free, mass exactly on budget); and at `δ = 1`
  the orthonormal witness `Σ_{n≤N} e(nt)` settles every `N`
  (`l2_concentration_of_delta_one`, sorry-free). The third entry (the chirp) STANDS, and
  `l2_concentration_exists`'s docstring now records the mechanism: the Fresnel value
  `∫₀^∞ e^{πiv²}dv = e^{iπ/4}/2` means a constraint point at an *end* of the frequency sweep
  gets `|ψ̂|² ≈ 1/4`, and pushing every constraint point into the interior is exactly what
  costs the `√(N/δ)`.

--------------------------------------------------------------------------------------
**The reduction above is MACHINE-CHECKED, in both of its halves.**
--------------------------------------------------------------------------------------

This theorem is no longer a `sorry`. The Fourier half of the reduction —
"`ψ` concentrated on `(0, δ]` ⟹ all five fields" — is
`selbergMajorant_of_concentration` immediately above, proved from Mathlib's `AddCircle`
Fourier theory plus one new lemma, the sesquilinear Parseval identity
`tsum_conj_mul_fourierCoeffOn`. What remains is precisely **(C)**, isolated as
`l2_concentration_exists`, which contains no reference to `SelbergMajorant` at all.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` and `δ` are unrelated. -/
theorem selberg_majorant_of_lt_half (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2) :
    Nonempty (SelbergMajorant N δ) := by
  obtain ⟨ψ, hmem, hsupp, hnorm, hcoef⟩ := l2_concentration_exists N hδ (by linarith)
  exact selbergMajorant_of_concentration N hδ (by linarith) hmem hsupp hnorm hcoef

/-- **(I1a) Existence of the Beurling–Selberg majorant of the indicator of `(0, N]` at
bandwidth `δ` — reduced to the regime `δ < 1/2`.**

Paper §6. Literature: Beurling; Selberg; [IK, Thm 7.7] and the
discussion around it; [Va, Thm 3]; Vaaler, *Some extremal problems in Fourier analysis*.
Depends on: nothing.

**This is the ONLY remaining gap in Lemma 6.1.** `dual_of_majorant`,
`additive_of_majorant`, `sharp_additive_large_sieve_of_le_one` and everything downstream
of them in this file are proved from these five fields alone.

**STATUS.** This statement is not a bare `sorry`: the regime
`1/2 ≤ δ ≤ 1` is discharged unconditionally and elementarily by
`selberg_majorant_of_half_le` (there `vanishing` is vacuous or tests one point, and the
extremal `F` is *finitely supported*). What is left is `selberg_majorant_of_lt_half`, whose
docstring records the reduction of the residual case to an `L²` concentration problem on an
interval of length `δ` — no entire functions, no Paley–Wiener, no Poisson summation.

The originally suggested route, kept for reference:
1. Build Beurling's function `B(z) = H(z) + K(z)`, `H` the Hilbert-type interpolation of
   `sgn` and `K(z) = (sin πz / πz)²` the Fejér kernel, giving `B ≥ sgn` with
   `∫(B − sgn) = 1`; Mathlib has neither, but `Real.sin`/`Complex.sin` and
   `Mathlib/Analysis/Fourier/` supply the ingredients.
2. Selberg's shift: `f(z) = ½(B(δ(a − z)) + B(δ(z − b)))` majorises `𝟙_{[a,b]}` and has
   `∫f = (b − a) + δ⁻¹`, with `supp f̂ ⊆ [−δ, δ]` by exponential type `2πδ`.
3. Instantiate at `[a, b] = [1, N]` (`b − a = N − 1`) and apply Poisson summation
   (`Real.tsum_eq_tsum_fourier_of_rpow_decay`) to get `total` and `vanishing`.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` and `δ` are unrelated. -/
theorem selberg_majorant_exists (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Nonempty (SelbergMajorant N δ) := by
  rcases lt_or_ge δ (1 / 2) with h | h
  · exact selberg_majorant_of_lt_half N hδ h
  · exact selberg_majorant_of_half_le N h hδ1

variable {N : ℕ} {δ : ℝ}

/-- Absolute convergence of the twisted total `Σ_n F(n)e(nα)`, for every `α`. -/
theorem SelbergMajorant.summable_mul (M : SelbergMajorant N δ) (α : ℝ) :
    Summable (fun n : ℤ => (M.F n : ℂ) * e ((n : ℝ) * α)) := by
  refine Summable.of_norm ?_
  have h : ∀ n : ℤ, ‖(M.F n : ℂ) * e ((n : ℝ) * α)‖ = M.F n := by
    intro n
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (M.nonneg n)]
  simp only [h]
  exact M.summable

/-- The budget `N − 1 + δ⁻¹` is nonnegative — it is the total mass of a nonnegative
function, so this costs nothing and saves carrying `δ ≤ 1` through the duality step. -/
theorem SelbergMajorant.budget_nonneg (M : SelbergMajorant N δ) :
    0 ≤ (N : ℝ) - 1 + δ⁻¹ := by
  rw [← M.total]
  exact tsum_nonneg M.nonneg

/-- **The DUAL sharp additive large sieve, from the majorant.** This is the step where the
constant is created: majorise `𝟙_{(0,N]}` by `F`, expand the square, and kill every
off-diagonal term with `M.vanishing` — the diagonal contributes `Σ_n F(n) = N − 1 + δ⁻¹`
exactly.

Fully proved from the `SelbergMajorant` fields. -/
theorem dual_of_majorant (M : SelbergMajorant N δ)
    {ι : Type} [Fintype ι] (θ : ι → ℝ) (x : ι → ℂ)
    (hsep : ∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) :
    ∑ n ∈ Finset.Ioc (0:ℤ) (N:ℤ), ‖∑ i, x i * e ((n : ℝ) * θ i)‖ ^ 2
      ≤ ((N : ℝ) - 1 + δ⁻¹) * ∑ i, ‖x i‖ ^ 2 := by
  classical
  set G : ℤ → ℂ := fun n => ∑ i, x i * e ((n : ℝ) * θ i) with hGdef
  have hGb : ∀ n : ℤ, ‖G n‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 := by
    intro n
    have h1 : ‖G n‖ ≤ ∑ i, ‖x i‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, norm_e, mul_one]
    have h2 : (0:ℝ) ≤ ‖G n‖ := norm_nonneg _
    nlinarith
  have hsum : Summable (fun n : ℤ => M.F n * ‖G n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (M.nonneg n) (sq_nonneg _))
      (fun n => ?_) (M.summable.mul_left ((∑ i, ‖x i‖) ^ 2))
    nlinarith [M.nonneg n, hGb n]
  have e1 : ∀ n : ℤ, ((M.F n * ‖G n‖ ^ 2 : ℝ) : ℂ)
      = ∑ i, ∑ j, ((M.F n : ℂ) * e ((n : ℝ) * (θ i - θ j))) * (x i * (starRingEnd ℂ) (x j)) := by
    intro n
    push_cast
    rw [← Complex.mul_conj', hGdef]
    simp only [map_sum, map_mul]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conj_e]
    have key : e ((n : ℝ) * θ i) * e (-((n : ℝ) * θ j)) = e ((n : ℝ) * (θ i - θ j)) := by
      rw [← e_add]; congr 1; ring
    linear_combination ((M.F n : ℂ) * x i * (starRingEnd ℂ) (x j)) * key
  have hinner : ∀ i j : ι,
      (∑' n : ℤ, (M.F n : ℂ) * e ((n : ℝ) * (θ i - θ j))) * (x i * (starRingEnd ℂ) (x j))
        = if i = j then (((N : ℝ) - 1 + δ⁻¹ : ℝ) : ℂ) * ((‖x i‖ : ℝ) : ℂ) ^ 2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, sub_self]
      simp only [mul_zero, e_zero, mul_one]
      rw [← Complex.ofReal_tsum, M.total, Complex.mul_conj']
    · rw [if_neg hij, M.vanishing _ (hsep i j hij), zero_mul]
  have hvalC : ((∑' n : ℤ, M.F n * ‖G n‖ ^ 2 : ℝ) : ℂ)
      = (((N : ℝ) - 1 + δ⁻¹ : ℝ) : ℂ) * ∑ i, ((‖x i‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_tsum, tsum_congr e1]
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ =>
      ((M.summable_mul (θ i - θ j)).mul_right (x i * (starRingEnd ℂ) (x j)))))]
    have step : ∀ i : ι, (∑' n : ℤ, ∑ j, ((M.F n : ℂ) * e ((n : ℝ) * (θ i - θ j)))
          * (x i * (starRingEnd ℂ) (x j)))
        = ∑ j, (∑' n : ℤ, (M.F n : ℂ) * e ((n : ℝ) * (θ i - θ j)))
          * (x i * (starRingEnd ℂ) (x j)) := by
      intro i
      rw [Summable.tsum_finsetSum (fun j _ => (M.summable_mul (θ i - θ j)).mul_right _)]
      exact Finset.sum_congr rfl fun j _ => (tsum_mul_right)
    rw [Finset.sum_congr rfl fun i _ => step i]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hinner i j]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
  have hval : ∑' n : ℤ, M.F n * ‖G n‖ ^ 2 = ((N : ℝ) - 1 + δ⁻¹) * ∑ i, ‖x i‖ ^ 2 := by
    have h : ((∑' n : ℤ, M.F n * ‖G n‖ ^ 2 : ℝ) : ℂ)
        = ((((N : ℝ) - 1 + δ⁻¹) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
      rw [hvalC]; push_cast; ring
    exact_mod_cast h
  rw [← hval]
  refine le_trans (Finset.sum_le_sum ?_)
    (Summable.sum_le_tsum _ (fun n _ => mul_nonneg (M.nonneg n) (sq_nonneg _)) hsum)
  intro n hn
  rw [Finset.mem_Ioc] at hn
  have h1 : (1:ℝ) ≤ M.F n := M.majorizes n hn.1 hn.2
  nlinarith [sq_nonneg ‖G n‖]

/-- **The PRIMAL sharp additive large sieve, from the majorant** — `dual_of_majorant` plus
the operator-norm duality `‖A‖ = ‖A*‖`, run by hand as Cauchy–Schwarz on the test vector
`x_i := conj S(θ_i)`.

Fully proved from the `SelbergMajorant` fields. -/
theorem additive_of_majorant (M : SelbergMajorant N δ)
    {ι : Type} [Fintype ι] (a : ℕ → ℂ) (θ : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) :
    ∑ i, ‖expSum N a (θ i)‖ ^ 2 ≤ ((N : ℝ) - 1 + δ⁻¹) * l2sq N a := by
  classical
  have hl0 : 0 ≤ l2sq N a := Finset.sum_nonneg fun _ _ => by positivity
  set Δ : ℝ := (N : ℝ) - 1 + δ⁻¹ with hΔdef
  have hΔ0 : 0 ≤ Δ := M.budget_nonneg
  set S : ι → ℂ := fun i => expSum N a (θ i) with hSdef
  set V : ℝ := ∑ i, ‖S i‖ ^ 2 with hVdef
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => by positivity
  set x : ι → ℂ := fun i => (starRingEnd ℂ) (S i) with hxdef
  have hxn : ∀ i, ‖x i‖ = ‖S i‖ := by intro i; simp [hxdef]
  set W : ℤ → ℂ := fun n => ∑ i, x i * e ((n : ℝ) * θ i) with hWdef
  have hVC : ((V : ℝ) : ℂ) = ∑ n ∈ Finset.Ioc 0 N, a n * W (n : ℤ) := by
    rw [hVdef]
    push_cast
    have h1 : ∀ i : ι, ((‖S i‖ : ℝ) : ℂ)
        ^ 2 = ∑ n ∈ Finset.Ioc 0 N, a n * (x i * e ((n : ℝ) * θ i)) := by
      intro i
      rw [← Complex.mul_conj']
      simp only [hxdef, hSdef, expSum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hWdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hnorm : V ≤ ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ * ‖W (n : ℤ)‖ := by
    have hv : V = ‖((V : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hV0]
    rw [hv, hVC]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => norm_mul _ _))
  have hCS : (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ * ‖W (n : ℤ)‖) ^ 2
      ≤ (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) * ∑ n ∈ Finset.Ioc 0 N, ‖W (n : ℤ)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have himg : (Finset.Ioc (0:ℕ) N).image (fun n : ℕ => (n : ℤ)) = Finset.Ioc (0:ℤ) (N:ℤ) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_Ioc]
    constructor
    · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩
  have hdual : ∑ n ∈ Finset.Ioc (0:ℕ) N, ‖W (n : ℤ)‖ ^ 2 ≤ Δ * V := by
    have h := dual_of_majorant M θ x hsep
    rw [← himg, Finset.sum_image (fun p _ q _ hpq => by exact_mod_cast hpq)] at h
    refine h.trans (le_of_eq ?_)
    rw [hVdef]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [hxn i])
  rcases eq_or_lt_of_le hV0 with hV | hV
  · rw [← hV]
    exact mul_nonneg hΔ0 hl0
  · have h2 : V ^ 2 ≤ (l2sq N a) * (Δ * V) := by
      calc V ^ 2 ≤ (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ * ‖W (n : ℤ)‖) ^ 2 := by
            nlinarith [hnorm, hV0]
        _ ≤ (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) * ∑ n ∈ Finset.Ioc 0 N, ‖W (n : ℤ)‖ ^ 2 := hCS
        _ ≤ (l2sq N a) * (Δ * V) := mul_le_mul_of_nonneg_left hdual hl0
    have h3 : V * V ≤ (Δ * l2sq N a) * V := by nlinarith [h2]
    exact le_of_mul_le_mul_right h3 hV

/-- **The corrected sharp additive large sieve — PROVED, modulo the majorant.**
This is what `multiplicative_large_sieve` cites. See `sharpAdditiveLargeSieve_false` for
why the frozen `sharp_additive_large_sieve` above is not usable.

Its only `sorry` is `selberg_majorant_exists`. -/
theorem sharp_additive_large_sieve_of_le_one : SharpAdditiveLargeSieveOfLeOne := by
  intro ι _ N a θ δ hδ hδ1 hsep
  obtain ⟨M⟩ := selberg_majorant_exists N hδ hδ1
  exact additive_of_majorant M a θ hsep

/-- **(I1) THE SHARP ADDITIVE LARGE SIEVE — THE ONE FROM-ZERO SORRY OF §6.**
For `δ`-separated `θ_i` mod 1, `Σ_i |Σ_{n≤N} a_n e(nθ_i)|² ≤ (N − 1 + δ⁻¹)‖a‖₂²`.

Paper §6 ("the additive N − 1 + δ⁻¹ input"); literature: Selberg,
Montgomery–Vaughan [MV73]; textbook [IK, Thm 7.7], [Va].
Depends on: nothing in this repository.

**READ THE MODULE HEADER FIRST.** Nothing in `Zeta23/MV/` proves this and nothing in
`Zeta23/MV/` can be pushed to prove it without redoing the numerics: what is in tree is
`MVDiag 13` / `MVHilbert 26` — MV74 **Theorem 2**, the non-periodic weighted Hilbert
inequality, at an **abstract** constant whose own docstring says any absolute constant
would do (`Zeta23/MV.lean:23–26`). Mathlib has no large sieve in any form
(zero grep hits).

**TWO CANDIDATE ROUTES, both from zero:**

* **(a) Beurling–Selberg extremal majorant + Poisson summation** ([IK, Thm 7.7]). Build
  the extremal majorant of the indicator of an interval, apply Poisson summation.
  *RECOMMENDED*: self-contained, and its constant is sharp **by construction** rather than
  by improving an already-proved one. Caveat: Mathlib has no Beurling–Selberg majorant
  either (`Beurling` → 0 hits), so the majorant is part of the build.
* **(b) Sharp periodic (cosecant) Hilbert inequality**, then duality. Re-run the
  `Zeta23/MV/` architecture — `Spacing → Quadratic → EigenIdentity → Eigen → Duality` —
  for the periodic kernel and push the constant from 13 down to 1. The *architecture*
  transfers as a template; the numerics do not (`spacing_sq ≤ 9/δ_s`,
  `Uform_le ≤ 73` are exactly the crude steps that produce 13). Anchor:
  `periodic_hilbert_sharp` below.

Rule 17: none — no `ParamsQ`, no `T`, no `λ`; `N` is a bare natural with no relation to
anything.

--------------------------------------------------------------------------------------
**HISTORY: this statement WAS false as encoded; decision D22 repaired it.**
--------------------------------------------------------------------------------------

As originally frozen, `SharpAdditiveLargeSieve` quantified over ALL `δ > 0`, but its
separation hypothesis is **vacuous** when `ι` has at most one element, and the constant
`N − 1 + δ⁻¹` is then *below* the sharp Cauchy–Schwarz value `N` as soon as `δ > 1`. That
disproof survives as `ZetaQ.sharpAdditiveLargeSieveUnrestricted_false`, refuting the
`…Unrestricted` copy of the old shape, and is machine-checked:

  `ι := Unit`, `N := 1`, `a := 1`, `θ := 0`, `δ := 2`
  LHS `= ‖a 1‖² = 1`,  RHS `= (1 − 1 + 2⁻¹)·1 = 1/2`.

Only the ENCODING was wrong; the mathematics of §6 was untouched. Every real use is at
`δ = Q⁻² ≤ 1` (`multiplicative_large_sieve_of_additive`, via `farey_spaced`), and with
`δ ≤ 1` the statement is the standard [IK, Thm 7.7] / [Va, Thm 3] one and is TRUE. The
side condition is also exactly what the Beurling–Selberg route needs: the majorant's
Fourier transform is supported in `[−δ, δ]`, so Poisson summation collapses
`Σ_{n∈ℤ} F(n)` to `∫F` **only** when no nonzero integer lies in `[−δ, δ]`, i.e. `δ ≤ 1`.

Decision **D22** folded `δ ≤ 1` into `SharpAdditiveLargeSieve` itself, so the frozen
statement and `SharpAdditiveLargeSieveOfLeOne` are now literally the same proposition and
this theorem is `sharp_additive_large_sieve_of_le_one`. **The only edit here made
to the declaration is its position in the file** — its type, name and docstring are the
frozen ones; it was moved down from §1 to just below its proof source, since Lean has no
forward references. Its remaining `sorry` debt is `l2_concentration_exists`, via
`selberg_majorant_exists`. -/
theorem sharp_additive_large_sieve : SharpAdditiveLargeSieve :=
  sharp_additive_large_sieve_of_le_one

/-- **(I1b, OPTIONAL — route (b) anchor only.)** The sharp periodic ("cosecant") Hilbert
inequality at constant `1`: for `δ`-separated `θ_i` mod 1,
`|Σ_{i≠j} x_i x̄_j cosec(π(θ_i − θ_j))| ≤ δ⁻¹ Σ_i |x_i|²`.

Paper §6 (the "[MV74] Hilbert inequality" citation). Route (b).
Depends on: nothing.

**Declare-only, and only if route (b) is chosen.** `multiplicative_large_sieve` does NOT
depend on this statement; delete it if route (a) is taken. The double sum is written in
[R]'s `MVDiag` shape (`Zeta23/MV.lean:52`) so that the `Zeta23/MV/` files can be used as a
line-by-line template.

**Fidelity caveat, flagged rather than guessed:** the kernel is recorded here
as `cosec(π(θ_r − θ_s))`; the classical MV73 Theorem 1 is frequently quoted with `cot`
instead. Confirm the kernel against [MV73]/[MV74] before proving. Since this lemma is
optional scaffolding and no other declaration in this file cites it, the ambiguity is
contained here.

Rule 17: none. 
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: optional scaffolding for route (b) of Lemma 6.1.  The artifact takes route (a)
(Selberg / Beurling–Selberg), so nothing cites this — and its kernel (`cosec` vs `cot`) has a
recorded ambiguity against [MV73] that a prover would have to settle first. -/
def PeriodicHilbertSharp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (θ : ι → ℝ) (x : ι → ℂ) (δ : ℝ), 0 < δ →
    (∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) →
    ‖∑ i, ∑ j, if i = j then (0 : ℂ) else
        x i * (starRingEnd ℂ) (x j) *
          (((Real.sin (Real.pi * (θ i - θ j)))⁻¹ : ℝ) : ℂ)‖
      ≤ δ⁻¹ * ∑ i, ‖x i‖ ^ 2

/-- **(I2) Farey spacing.** Distinct reduced fractions `a/q ≠ a'/q'` of order `Q` are
`Q⁻²`-separated mod 1. This is the instantiation `δ := Q⁻²` that turns
`sharp_additive_large_sieve` into the additive input at a whole modulus range, and it is
where the `Q²` of `sieveBudget` comes from.

Paper §6 (implicit in "the multiplicative deduction is classical").
Depends on: nothing.

Encoding: distinctness of the Farey *points* is `(q, a % q) ≠ (q', a' % q')`, i.e. the
fractions are compared in reduced form with the numerator taken mod the denominator. The
conclusion is a bare inequality on `ℝ`, matching `SharpAdditiveLargeSieve`'s R10
separation hypothesis with no `AddCircle` glue.

Rule 17: none — `Q` alone, no `N`, no parameters. -/
theorem farey_spaced (Q : ℕ) {q q' a a' : ℕ}
    (hq : 0 < q) (hq' : 0 < q') (hqQ : q ≤ Q) (hq'Q : q' ≤ Q)
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime a' q')
    (hne : (q, a % q) ≠ (q', a' % q')) (m : ℤ) :
    ((Q : ℝ) ^ 2)⁻¹ ≤ |(a : ℝ) / q - (a' : ℝ) / q' - (m : ℝ)| := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq'R : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'
  -- the numerator `a q' − a' q − m q q'` is a nonzero integer
  have hDne : (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - m * (q : ℤ) * (q' : ℤ) ≠ 0 := by
    intro h0
    apply hne
    have hdvd1 : q ∣ a * q' := by
      have h : ((q : ℕ) : ℤ) ∣ ((a * q' : ℕ) : ℤ) :=
        ⟨(a' : ℤ) + m * (q' : ℤ), by push_cast; linear_combination h0⟩
      exact_mod_cast h
    have hdvd2 : q' ∣ a' * q := by
      have h : ((q' : ℕ) : ℤ) ∣ ((a' * q : ℕ) : ℤ) :=
        ⟨(a : ℤ) - m * (q : ℤ), by push_cast; linear_combination -h0⟩
      exact_mod_cast h
    have e1 : q ∣ q' := hcop.symm.dvd_of_dvd_mul_left hdvd1
    have e2 : q' ∣ q := hcop'.symm.dvd_of_dvd_mul_left hdvd2
    have heq : q = q' := Nat.dvd_antisymm e1 e2
    subst heq
    have hq0 : ((q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have hz : (q : ℤ) * ((a : ℤ) - (a' : ℤ) - m * (q : ℤ)) = 0 := by linear_combination h0
    have h2 := (mul_eq_zero.mp hz).resolve_left hq0
    have hmod : Nat.ModEq q a a' :=
      Nat.modEq_iff_dvd.mpr ⟨-m, by linear_combination -h2⟩
    exact congrArg (fun z : ℕ => ((q : ℕ), z)) hmod
  set D : ℤ := (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - m * (q : ℤ) * (q' : ℤ) with hDdef
  have hz1 : (1 : ℤ) ≤ |D| := by
    have := abs_pos.mpr hDne
    linarith
  have hR1 : (1 : ℝ) ≤ |(D : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hz1
  have key : (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) - (m : ℝ)
      = (D : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    rw [hDdef]
    push_cast
    field_simp
  have hprod : (q : ℝ) * (q' : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
    have h2 : (q' : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq'Q
    nlinarith
  rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q : ℝ) * (q' : ℝ)), inv_eq_one_div]
  calc (1 : ℝ) / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * (q' : ℝ)) := by
        exact one_div_le_one_div_of_le (by positivity) hprod
    _ ≤ |(D : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by gcongr

/-! ## 2. Gauss sums (step I3)

The *transfer identity* is already in
Mathlib in exactly the right generality; the *modulus* `‖τ(χ)‖ = √q` is a genuine gap. -/

/-- Helper, NOT in Mathlib at this pin: the inverse of a primitive character is primitive.
`FactorsThrough` is stable under `ψ ↦ ψ⁻¹` because `DirichletCharacter.changeLevel` is a
`MonoidHom` into a `CommGroup`, so the two conductor sets coincide.

Needed because `gaussSum_mulShift_of_isPrimitive` must be applied at `χ⁻¹` (the transfer
identity of `gaussSum_transfer` is stated with `τ(χ⁻¹)` on the left). -/
theorem isPrimitive_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  have key : ∀ (ψ : DirichletCharacter ℂ q) (d : ℕ),
      ψ.FactorsThrough d → (ψ⁻¹).FactorsThrough d := by
    rintro ψ d ⟨hd, ψ₀, rfl⟩
    exact ⟨hd, ψ₀⁻¹, (map_inv (DirichletCharacter.changeLevel hd) ψ₀).symm⟩
  have h1 : (χ⁻¹).conductor ≤ χ.conductor :=
    Nat.sInf_le (key χ _ (DirichletCharacter.factorsThrough_conductor χ))
  have h2 : χ.conductor ≤ (χ⁻¹).conductor := by
    have hm : (χ⁻¹).conductor ∈ DirichletCharacter.conductorSet (χ⁻¹)⁻¹ :=
      key χ⁻¹ _ (DirichletCharacter.factorsThrough_conductor χ⁻¹)
    rw [inv_inv] at hm
    exact Nat.sInf_le hm
  rw [DirichletCharacter.isPrimitive_def] at hχ ⊢
  omega

/-- **(I3a) Gauss-sum transfer.** For **primitive** `χ` mod `q`,
`χ(n)·τ(χ⁻¹) = Σ_{b mod q} χ⁻¹(b) e(bn/q)` for **every** `n : ZMod q` — primitivity is
exactly what removes the usual `gcd(n,q) = 1` restriction, and that is why the family in
Lemma 6.1 is the *primitive* one.

Paper §6 ("duality + Gauss sums + primitive decomposition").
This is Mathlib's
`gaussSum_mulShift_of_isPrimitive` (`Mathlib/NumberTheory/DirichletCharacter/GaussSum.lean:57`,
verified present at pin `51e6992efd06126df61a496bebf8f49482a4e129`) instantiated at
`e := ZMod.stdAddChar`, applied at `χ⁻¹`, and unfolded with `AddChar.mulShift_apply`.
Depends on: nothing in this file.

Rule 17: none. -/
theorem gaussSum_transfer {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n * gaussSum χ⁻¹ ZMod.stdAddChar =
      ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar (b * n) := by
  have h := gaussSum_mulShift_of_isPrimitive
    (ZMod.stdAddChar (N := q)) (isPrimitive_inv hχ) n
  rw [inv_inv] at h
  rw [← h, gaussSum]
  exact Finset.sum_congr rfl fun b _ => by
    rw [AddChar.mulShift_apply, mul_comm n b]

/-- **(I3b) `‖τ(χ)‖ = √q` for primitive `χ` mod `q`.** The normalisation that makes the
Gauss-sum transfer lossless — it is what turns the `Σ*_χ` of Lemma 6.1 into exactly
`(φ(q)/q)·Σ_{(b,q)=1}` in `primitive_decomposition`, with no slack.

Paper §6.
Depends on: nothing in this file.

**GAP — this does NOT exist in Mathlib at this pin.** Explicitly searched and NOT FOUND:
`norm_gaussSum`, `abs_gaussSum`, any `‖gaussSum χ ψ‖ = Real.sqrt q`, any
`‖rootNumber χ‖ = 1`. It must be derived from
`star_gaussSum_eq` (`Mathlib/NumberTheory/GaussSum.lean:89`) plus
`gaussSum_mul_gaussSum_eq_card` (`GaussSum.lean:188`), which together give
`‖τ(χ)‖² = Fintype.card (ZMod q) = q`. Two care points: (i)
`gaussSum_mul_gaussSum_eq_card` carries `χ ≠ 1`, which follows from primitivity when
`1 < q` via `DirichletCharacter.eq_one_iff_conductor_eq_one`
(`DirichletCharacter/Basic.lean:268`); (ii) `q = 1` is a separate one-line case
(`τ = 1 = √1`) — and note `primitiveChars 1 = {χ₀}` is NONEMPTY under Mathlib's
`IsPrimitive` (`isPrimitive_one_level_one`, `Basic.lean:296`), which is the reading
adopted here, so the `q = 1` case is reachable and must be discharged.

Rule 17: none. -/
theorem norm_gaussSum_of_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt (q : ℝ) := by
  classical
  set ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar with hψdef
  have hψ : ψ.IsPrimitive := by rw [hψdef]; exact ZMod.isPrimitive_stdAddChar q
  have hV : 0 < ∑ x : ZMod q, ‖χ x‖ ^ 2 := by
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨1, Finset.mem_univ 1, ?_⟩
    rw [norm_char_apply_of_isUnit χ isUnit_one]
    norm_num
  -- Side A: `gaussSum χ (ψ.mulShift a) = χ⁻¹ a · τ(χ)` for every `a`, by primitivity.
  have sideA : ∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2
      = (∑ x : ZMod q, ‖χ x‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gaussSum_mulShift_of_isPrimitive ψ hχ a, norm_mul, mul_pow,
      ← MulChar.star_apply' χ a, norm_star]
  -- Side B: expand the square and collapse the `a`-sum by primitivity of `ψ`.
  have sideB : ((∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 : ℝ) : ℂ)
      = (q : ℂ) * ((∑ x : ZMod q, ‖χ x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have e1 : ∀ a : ZMod q, ((‖gaussSum χ (ψ.mulShift a)‖ : ℝ) : ℂ) ^ 2
        = ∑ x : ZMod q, ∑ y : ZMod q,
            (χ x * (starRingEnd ℂ) (χ y)) * ψ (a * (x - y)) := by
      intro a
      rw [← Complex.mul_conj', gaussSum, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [map_mul, AddChar.mulShift_apply]
      rw [← AddChar.map_neg_eq_conj ψ (a * y),
        show a * (x - y) = a * x + -(a * y) by ring, AddChar.map_add_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => e1 a]
    have swap : ∑ a : ZMod q, ∑ x : ZMod q, ∑ y : ZMod q,
          (χ x * (starRingEnd ℂ) (χ y)) * ψ (a * (x - y))
        = ∑ x : ZMod q, ∑ y : ZMod q,
          (χ x * (starRingEnd ℂ) (χ y)) * ∑ a : ZMod q, ψ (a * (x - y)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
    have final : ∑ x : ZMod q, ∑ y : ZMod q,
          (χ x * (starRingEnd ℂ) (χ y)) * ∑ a : ZMod q, ψ (a * (x - y))
        = ∑ x : ZMod q, (q : ℂ) * ((‖χ x‖ : ℝ) : ℂ) ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single x]
      · rw [AddChar.sum_mulShift (x - x) hψ, sub_self, if_pos rfl, ZMod.card q,
          ← Complex.mul_conj']
        ring
      · intro y _ hyx
        rw [AddChar.sum_mulShift (x - y) hψ, if_neg (sub_ne_zero.mpr (Ne.symm hyx))]
        simp
      · intro h
        exact absurd (Finset.mem_univ x) h
    rw [swap, final, ← Finset.mul_sum]
  rw [sideA] at sideB
  have hreal : (∑ x : ZMod q, ‖χ x‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2
      = (∑ x : ZMod q, ‖χ x‖ ^ 2) * (q : ℝ) := by
    have h : (∑ x : ZMod q, ‖χ x‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2
        = (q : ℝ) * (∑ x : ZMod q, ‖χ x‖ ^ 2) := by exact_mod_cast sideB
    rw [h]; ring
  have hsq : ‖gaussSum χ ψ‖ ^ 2 = (q : ℝ) := mul_left_cancel₀ hV.ne' hreal
  rw [← hsq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- **(I3c) Glue: Mathlib's standard additive character IS `ZetaQ.e` at `b/q`.**
`stdAddChar (b : ZMod q) = e(b/q)` for a natural `b`. This is the only bridge between the
Gauss-sum half (stated over `ZMod q` with `ZMod.stdAddChar`) and the additive half (stated
over `ℝ` with `ZetaQ.e`), and without it milestones (I3)/(I4) and (I1)/(I2) do not meet.

Paper §6.
Depends on: `e`.

Rule 17: none. -/
theorem stdAddChar_eq_e {q : ℕ} [NeZero q] (b : ℕ) :
    ZMod.stdAddChar (b : ZMod q) = e ((b : ℝ) / (q : ℝ)) := by
  have h := ZMod.stdAddChar_coe (N := q) (b : ℤ)
  rw [show (((b : ℤ) : ZMod q)) = ((b : ℕ) : ZMod q) by push_cast; ring] at h
  rw [h, e]
  congr 1
  push_cast
  ring

/-! ## 3. Orthogonality and the primitive decomposition (step I4)

The orthogonality *engine* is in Mathlib
(`DirichletCharacter.sum_char_inv_mul_char_eq`, `Orthogonality.lean:80`), so (I4) is an
assembly job. Two residual gaps: no `Finset` of primitive characters and no
`DecidablePred IsPrimitive` (handled by the frozen `ZetaQ.primitiveChars`, which is
classical), and the `[HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]` instance
carried by every lemma in `Orthogonality.lean` — **UNVERIFIED at this pin**.
That instance is deliberately NOT written into
the statements below; if it fails to fire at `R = ℂ`, a hand-built instance is a
prerequisite of this whole section, and checking it is the cheapest de-risking available.
Run it first. -/

/-- **(I4a) Orthogonality of Dirichlet characters, `ℓ²` form.**
`Σ_{χ mod q} |Σ_b χ(b) f(b)|² = φ(q)·Σ_{b a unit} |f(b)|²` — the engine of the primitive
decomposition, and where the `φ(q)` of `primitive_decomposition` is born.

Paper §6 ("primitive decomposition").
Expand the square as
`Σ_{b,c} χ(b)χ⁻¹(c) f(b) conj(f c)` (using `MulChar.star_eq_inv`,
`Mathlib/NumberTheory/MulChar/Lemmas.lean:73`) and collapse the `χ`-sum with
`DirichletCharacter.sum_char_inv_mul_char_eq`
(`Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean:80`).
Depends on: `unitResidues`.

Note the sum over `χ : DirichletCharacter ℂ q` uses `DirichletCharacter.fintype`
(`Orthogonality.lean:27`) — the same instance the frozen `ZetaQ.primitiveChars` already
relies on, so its availability is not a new obligation.

Rule 17: none. -/
theorem sum_sq_over_all_chars {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ b * f b‖ ^ 2
      = (Nat.totient q : ℝ) * ∑ b ∈ unitResidues q, ‖f b‖ ^ 2 := by
  classical
  -- only units contribute to a character sum
  have hres : ∀ χ : DirichletCharacter ℂ q,
      ∑ b : ZMod q, χ b * f b = ∑ b ∈ unitResidues q, χ b * f b := by
    intro χ
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    rw [MulChar.map_nonunit χ (fun h => hx (mem_unitResidues.mpr h)), zero_mul]
  -- on units, complex conjugation of a character value is evaluation at the inverse
  have hconj : ∀ (χ : DirichletCharacter ℂ q) (c : ZMod q), IsUnit c →
      (starRingEnd ℂ) (χ c) = χ c⁻¹ := by
    intro χ c hc
    have h1 : χ c * (starRingEnd ℂ) (χ c) = 1 := by
      have hs : (starRingEnd ℂ) (χ c) = χ⁻¹ c := MulChar.star_apply' χ c
      rw [hs, ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hc]
    have h2 : χ c * χ c⁻¹ = 1 := by
      rw [← map_mul, ZMod.mul_inv_of_unit c hc, MulChar.map_one]
    have hne : χ c ≠ 0 := by
      intro h
      rw [h, zero_mul] at h1
      exact zero_ne_one h1
    exact mul_left_cancel₀ hne (h1.trans h2.symm)
  refine Complex.ofReal_inj.mp ?_
  push_cast
  -- expand each squared modulus as a double sum over units
  have expand : ∀ χ : DirichletCharacter ℂ q,
      ((‖∑ b : ZMod q, χ b * f b‖ : ℂ)) ^ 2
        = ∑ b ∈ unitResidues q, ∑ c ∈ unitResidues q,
            (χ c⁻¹ * χ b) * (f b * (starRingEnd ℂ) (f c)) := by
    intro χ
    rw [hres χ, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c hc => ?_
    rw [map_mul, hconj χ c (mem_unitResidues.mp hc)]
    ring
  rw [Finset.sum_congr rfl fun χ (_ : χ ∈ Finset.univ) => expand χ]
  -- pull the character sum inside and collapse it by orthogonality
  have swap : ∑ χ : DirichletCharacter ℂ q, ∑ b ∈ unitResidues q, ∑ c ∈ unitResidues q,
        (χ c⁻¹ * χ b) * (f b * (starRingEnd ℂ) (f c))
      = ∑ b ∈ unitResidues q, ∑ c ∈ unitResidues q,
        (∑ χ : DirichletCharacter ℂ q, χ c⁻¹ * χ b) * (f b * (starRingEnd ℂ) (f c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => (Finset.sum_mul _ _ _).symm
  rw [swap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.sum_eq_single b]
  · rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (mem_unitResidues.mp hb) b, if_pos rfl,
      ← Complex.mul_conj']
  · intro c hc hcb
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (mem_unitResidues.mp hc) b,
      if_neg hcb, zero_mul]
  · intro hb'
    exact absurd hb hb'

/-- **(I4b) Primitive decomposition at one modulus.**
`Σ*_{χ mod q} |Σ_{n≤N} a_n χ(n)|² ≤ (φ(q)/q)·Σ_{(b,q)=1} |Σ_{n≤N} a_n e(nb/q)|²` —
the step that converts one modulus' *primitive* character sums into Farey exponential
sums, ready for the additive engine.

Paper §6 ("duality + Gauss sums + primitive decomposition").
Depends on: `gaussSum_transfer`, `norm_gaussSum_of_isPrimitive`, `sum_sq_over_all_chars`,
`stdAddChar_eq_e`, `primitiveChars` (frozen Defs), `reducedResidues`.

**The `φ(q)/q` here is exactly the reciprocal of the `q/φ(q)` weight paper §6's Remark
declines**. It is dropped, via `φ(q)/q ≤ 1`, inside
`multiplicative_large_sieve_of_additive` — that drop IS the declension, and it must not be
"optimised away" by exporting a weighted statement.

Rule 17: none — `q` and `N` independent, no parameters. -/
theorem primitive_decomposition (q N : ℕ) (hq : 0 < q) (a : ℕ → ℂ) :
    ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
      ≤ ((Nat.totient q : ℝ) / (q : ℝ)) *
          ∑ b ∈ reducedResidues q, ‖expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
  classical
  have : NeZero q := ⟨hq.ne'⟩
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hval : ∀ b : ZMod q, ((b.val : ℕ) : ZMod q) = b := by
    intro b; simp [ZMod.natCast_val, ZMod.cast_id]
  set f : ZMod q → ℂ := fun b => expSum N a ((b.val : ℝ) / (q : ℝ)) with hfdef
  -- (1) Gauss-sum transfer, applied to the whole coefficient sum.
  have transfer : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      charSum q N a χ * gaussSum χ⁻¹ ZMod.stdAddChar = ∑ b : ZMod q, χ⁻¹ b * f b := by
    intro χ hχ
    rw [charSum, Finset.sum_mul]
    have step : ∀ n ∈ Finset.Ioc 0 N,
        a n * χ (n : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar
          = ∑ b : ZMod q, χ⁻¹ b * (a n * ZMod.stdAddChar (b * (n : ZMod q))) := by
      intro n _
      rw [mul_assoc, gaussSum_transfer hχ (n : ZMod q), Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    simp only [hfdef, expSum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show b * (n : ZMod q) = ((b.val * n : ℕ) : ZMod q) by
      push_cast [hval b]; ring, stdAddChar_eq_e]
    congr 2
    push_cast
    ring
  -- (2) `‖τ(χ⁻¹)‖ = √q` turns the transfer into an exact identity of squares.
  have hnorm : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      (q : ℝ) * ‖charSum q N a χ‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * f b‖ ^ 2 := by
    intro χ hχ
    have h := congrArg norm (transfer χ hχ)
    rw [norm_mul, norm_gaussSum_of_isPrimitive (isPrimitive_inv hχ)] at h
    rw [← h, mul_pow, Real.sq_sqrt hqR.le]
    ring
  -- (3) drop from the primitive characters to all characters (nonnegative terms).
  have key : (q : ℝ) * ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * f b‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun χ hχ => hnorm χ (mem_primitiveChars.mp hχ))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)
  -- (4) `χ ↦ χ⁻¹` is a bijection of the character group.
  have reindex : ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * f b‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ b * f b‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q)) _ _ (fun _ => rfl)
  -- (5) the units of `ZMod q` are the Farey numerators at denominator `q`.
  have himg : (unitResidues q).image (fun b : ZMod q => b.val) = reducedResidues q := by
    ext c
    simp only [Finset.mem_image, mem_unitResidues, mem_reducedResidues]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨ZMod.val_lt b, (ZMod.isUnit_iff_coprime b.val q).mp (by rw [hval b]; exact hb)⟩
    · rintro ⟨hlt, hcop⟩
      exact ⟨(c : ZMod q), (ZMod.isUnit_iff_coprime c q).mpr hcop,
        ZMod.val_natCast_of_lt hlt⟩
  have hsum5 : ∑ b ∈ unitResidues q, ‖f b‖ ^ 2
      = ∑ c ∈ reducedResidues q, ‖expSum N a ((c : ℝ) / (q : ℝ))‖ ^ 2 := by
    rw [← himg, Finset.sum_image]
    intro b _ c _ h
    have h' : b.val = c.val := h
    rw [← hval b, ← hval c, h']
  have final : (q : ℝ) * ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
      ≤ (Nat.totient q : ℝ) * ∑ c ∈ reducedResidues q, ‖expSum N a ((c : ℝ) / (q : ℝ))‖ ^ 2 := by
    refine key.trans ?_
    rw [reindex, sum_sq_over_all_chars f, hsum5]
  rw [div_mul_eq_mul_div, le_div_iff₀ hqR]
  linarith [final]

/-! ## 4. The assembly bridge (step I6a)

The additive engine is abstracted as an explicit hypothesis rather than cited directly.
That is deliberate and it is the point of the module header: it makes the file's single
from-zero dependency **auditable in the signature** — exactly the discipline
`Zeta23.PaperInputs.MV` uses for `MVHilbert` in [R]'s tree. `farey_spaced` and
`primitive_decomposition` are NOT abstracted: they are in-file lemmas the proof cites
directly, because neither is a gap. -/

/-- **(I6a), at the corrected hypothesis.** Same bridge as
`multiplicative_large_sieve_of_additive` below, but assuming only
`SharpAdditiveLargeSieveOfLeOne` — which is what is TRUE (see
`sharpAdditiveLargeSieve_false`). This is the version `multiplicative_large_sieve`
actually cites; the frozen one is derived from it.

The `δ ≤ 1` side condition costs nothing: the engine is applied at `δ = Q⁻²` with
`Q ≥ 1`. -/
theorem multiplicative_large_sieve_of_additive_of_le_one
    (hadd : SharpAdditiveLargeSieveOfLeOne) (Q N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
      ≤ sieveBudget N Q * l2sq N a := by
  classical
  have hl2 : (0:ℝ) ≤ l2sq N a := Finset.sum_nonneg fun _ _ => by positivity
  rcases Nat.eq_zero_or_pos Q with rfl | hQ1
  · -- degenerate range: the left side is empty
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    rcases Nat.eq_zero_or_pos N with rfl | hN1
    · rw [show l2sq 0 a = 0 by simp [l2sq]]
      simp
    · refine mul_nonneg ?_ hl2
      have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
      simp only [sieveBudget]
      push_cast
      linarith
  · have hQR : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ1
    -- the Farey points of order `Q`, as a `Finset` of pairs `(q, b)`
    set T : Finset ((_ : ℕ) × ℕ) := (Finset.Icc 1 Q).sigma reducedResidues with hT
    have hδ : (0:ℝ) < ((Q:ℝ) ^ 2)⁻¹ := by positivity
    have hsep : ∀ i j : {x // x ∈ T}, i ≠ j → ∀ m : ℤ,
        ((Q:ℝ) ^ 2)⁻¹
          ≤ |((i.1.2 : ℝ) / (i.1.1 : ℝ)) - ((j.1.2 : ℝ) / (j.1.1 : ℝ)) - (m : ℝ)| := by
      rintro ⟨⟨q, b⟩, hi⟩ ⟨⟨q', b'⟩, hj⟩ hij m
      have hi' := hi
      have hj' := hj
      rw [hT, Finset.mem_sigma, Finset.mem_Icc, mem_reducedResidues] at hi' hj'
      refine farey_spaced Q hi'.1.1 hj'.1.1 hi'.1.2 hj'.1.2 hi'.2.2 hj'.2.2 ?_ m
      rw [Nat.mod_eq_of_lt hi'.2.1, Nat.mod_eq_of_lt hj'.2.1]
      intro hcontra
      simp only [Prod.mk.injEq] at hcontra
      obtain ⟨rfl, rfl⟩ := hcontra
      exact hij rfl
    have hδ1 : ((Q:ℝ) ^ 2)⁻¹ ≤ 1 := by
      have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ1
      rw [inv_le_one_iff₀]
      right; nlinarith
    have hmain := hadd {x // x ∈ T} N a
      (fun x => (x.1.2 : ℝ) / (x.1.1 : ℝ)) (((Q:ℝ) ^ 2)⁻¹) hδ hδ1 hsep
    rw [inv_inv] at hmain
    have hsumeq : ∑ i : {x // x ∈ T}, ‖expSum N a ((i.1.2 : ℝ) / (i.1.1 : ℝ))‖ ^ 2
        = ∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ reducedResidues q,
            ‖expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
      rw [Finset.sum_coe_sort T (fun x => ‖expSum N a ((x.2 : ℝ) / (x.1 : ℝ))‖ ^ 2), hT]
      exact Finset.sum_sigma _ _ _
    calc ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
        ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ reducedResidues q,
            ‖expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [Finset.mem_Icc] at hq
          refine (primitive_decomposition q N hq.1 a).trans ?_
          -- **the declined weight**: `φ(q)/q ≤ 1` is dropped here
          have h1 : (Nat.totient q : ℝ) / (q : ℝ) ≤ 1 := by
            rw [div_le_one (by exact_mod_cast hq.1)]
            exact_mod_cast Nat.totient_le q
          have h2 : (0:ℝ) ≤ ∑ b ∈ reducedResidues q, ‖expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2 :=
            Finset.sum_nonneg fun _ _ => by positivity
          nlinarith
      _ = ∑ i : {x // x ∈ T}, ‖expSum N a ((i.1.2 : ℝ) / (i.1.1 : ℝ))‖ ^ 2 := hsumeq.symm
      _ ≤ ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * l2sq N a := hmain
      _ = sieveBudget N Q * l2sq N a := by rw [sieveBudget]; ring

/-- **(I6a) The bridge that assembles Lemma 6.1** — sharp additive engine + Farey spacing
at `δ := Q⁻²` + primitive decomposition, with the `φ(q)/q ≤ 1` drop, gives Lemma 6.1.

Paper §6.
Depends on: `SharpAdditiveLargeSieve` (hypothesis), `farey_spaced`,
`primitive_decomposition`, `familyQ`/`primitiveChars`, `sieveBudget`, `l2sq`.

Proof shape: `Σ_{q≤Q} Σ*_χ ≤ Σ_{q≤Q} (φ(q)/q) Σ_{(b,q)=1} |S(b/q)|²` by
`primitive_decomposition`; drop `φ(q)/q ≤ 1` (**the declined weight**); the resulting
Farey points are `Q⁻²`-separated by `farey_spaced`, so `hadd` at `δ := (Q:ℝ)⁻²` (whose
`δ⁻¹` is `Q²`) gives the budget `N − 1 + Q² = sieveBudget N Q`. Index type for `hadd`:
the Farey points of order `Q`, i.e. a subtype of `(Finset.Icc 1 Q).sigma reducedResidues`.

Rule 17: none — and note that `hadd`'s `N` is universally quantified with no relation to
`Q`, which is what keeps the composite statement free of any `N ≤ Q²`. -/
theorem multiplicative_large_sieve_of_additive (hadd : SharpAdditiveLargeSieve)
    (Q N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
      ≤ sieveBudget N Q * l2sq N a :=
  multiplicative_large_sieve_of_additive_of_le_one hadd.toLeOne Q N a

/-! ## 5. Lemma 6.1 — the two forms

Form 1 is the literal transcription of (fidelity). Form 2 is the subfamily
form the consumers actually apply. Both ship, because §6's
own sentence "consumed in Lemma 4.3 … Lemma 8.1 … and nowhere else" undercounts — the
paper's §4 names Lemma 4.4 and Lemma 4.5 as further
consumers, `Q_ASPECT_V2` records an error-schema consumption (Q8), and
§12.3's Corollary-3 parity argument consumes it out-zone at `C → 2C`. That is **five**
sites, and at every one of them the family is a SUBFAMILY (dyadic; parity; in-zone /
out-zone splits). Not a mathematical error — 4.4/4.5 are sub-lemmas of the §4 block that
Lemma 4.3 heads — but it does mean the interface must be the subfamily one. -/

/-- **Lemma 6.1** (paper §6) — the sharp multiplicative large sieve, in the paper's
UNWEIGHTED form: `Σ_{q≤Q} Σ*_{χ mod q} |Σ_{n≤N} a_n χ(n)|² ≤ (N + Q² − 1) Σ_{n≤N} |a_n|²`.

Paper §6 (the inequality is line 482). Attribution as the paper gives it:
Gallagher [Ga67]; Montgomery–Vaughan [MV73], [MV74]; [IK, Thm 7.13]; [Va, Thm 4]; in the
exact form quoted, [PT25, (1.1)].
All the work is
in `sharp_additive_large_sieve`.
Depends on: `sharp_additive_large_sieve`, `multiplicative_large_sieve_of_additive`.

Fidelity/encoding: `N : ℕ` with `n` over `Finset.Ioc 0 N` — [R]'s own
`PX`/`PXc` convention (`Zeta23/ThmE/Hypotheses.lean:55`); the `ℓ²` norm on the right runs
over the SAME index set (R2); `Q : ℕ`; `a : ℕ → ℂ` total on `ℕ` (both consumption sites
carry complex coefficients — `D_T(s − log n)` at Lemma 4.3, `n^{−1/2−iτ}` at Lemma 8.1).
Consumers recover the paper's real `X + Q² − 1` by instantiating `N := ⌊X⌋₊` and using
`(⌊X⌋₊ : ℝ) ≤ X` with monotonicity of `sieveBudget` in `N`.

**The `q/φ(q)` weight is DELIBERATELY DECLINED** (paper §6 Remark).
Do NOT strengthen this to the weighted form: it would move `C = π⁴/18` (`ZetaQ.Cfam`) to
`C_w ≈ 4.174` and change Theorem 1's headline `P`.

Rule 17: **there is deliberately NO hypothesis relating `N` and `Q`** — in particular no
`N ≤ Q²`. The paper runs `N = X = (QT/2π)^λ` at `λ* = 1.2507321515 > 1` (`ZetaQ.lamStar`),
and `X ≤ Q^{2−δ}` is a consequence at the design point, never a hypothesis here. No
`ParamsQ`, no `T`, no `X`, no `D₀` occurs in this statement at all. -/
theorem multiplicative_large_sieve (Q N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
      ≤ sieveBudget N Q * l2sq N a :=
  multiplicative_large_sieve_of_additive_of_le_one sharp_additive_large_sieve_of_le_one Q N a

/-- Helper carrying the Form 1 → Form 2 re-indexing argument. Declared here so that both
`multiplicative_large_sieve_family` and `multiplicative_large_sieve_family_of_full` (which
states the same thing but is placed later in the frozen file order) can cite it. -/
theorem family_le_of_full
    (hfull : ∀ (Q N : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
        ≤ sieveBudget N Q * l2sq N a)
    {ι : Type*} [Fintype ι] (Q N : ℕ) (a : ℕ → ℂ)
    (mod : ι → ℕ) (chi : ∀ i, DirichletCharacter ℂ (mod i))
    (hpos : ∀ i, 0 < mod i) (hle : ∀ i, mod i ≤ Q)
    (hprim : ∀ i, (chi i).IsPrimitive)
    (hinj : Function.Injective
      (fun i => (⟨mod i, chi i⟩ : (q : ℕ) × DirichletCharacter ℂ q))) :
    ∑ i, ‖charSum (mod i) N a (chi i)‖ ^ 2 ≤ sieveBudget N Q * l2sq N a := by
  classical
  have himg : (Finset.univ.image
      (fun i => (⟨mod i, chi i⟩ : (q : ℕ) × DirichletCharacter ℂ q))) ⊆ familyQ Q := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    simp only [familyQ, Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨hpos i, hle i⟩, mem_primitiveChars.mpr (hprim i)⟩
  have hre : ∑ x ∈ Finset.univ.image
        (fun i => (⟨mod i, chi i⟩ : (q : ℕ) × DirichletCharacter ℂ q)),
        ‖charSum x.1 N a x.2‖ ^ 2
      = ∑ i, ‖charSum (mod i) N a (chi i)‖ ^ 2 :=
    Finset.sum_image (fun i _ j _ h => hinj h)
  rw [← hre]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg himg
    (fun _ _ _ => by positivity)) ?_
  rw [sum_familyQ_aux]
  exact hfull Q N a

/-- **Lemma 6.1, family (subfamily) form** — the form the consumers apply. Any finite
family of pairs `(q, χ)` with `χ` primitive mod `q`, `1 ≤ q ≤ Q`, and no repeated pair,
obeys the same budget `N + Q² − 1`.

Paper §6, read through its five consumption sites.
Depends on: `multiplicative_large_sieve`, `multiplicative_large_sieve_family_of_full`.

**Why this is the load-bearing form.** It makes the subfamilies *definitional* rather than
extra work: the dyadic subfamily `q ∈ (Q/2, Q]` of Corollary 2 and the parity subfamilies
of §12.3 are instances at the SAME budget, so `LEMMA_Q7`'s "positivity of
the summands lets the dyadic family sit inside the `q ≤ Q` sum" costs nothing here — and
the F10 load-bearing choice (the dyadic budget keeps the same `Q²`, not `3Q²/4`,
`Q_ASPECT_V2`) is automatic rather than a separate argument.

Encoding: `hinj` says the pairs are distinct *as pairs* — the injectivity is on the
Sigma-valued map, so two different `i` may share a modulus provided the characters differ.
`Fintype ι` only; no `DecidableEq ι`, no instance on the character type.

Rule 17: none — `N` and `Q` still independent, no parameters. -/
theorem multiplicative_large_sieve_family
    {ι : Type*} [Fintype ι] (Q N : ℕ) (a : ℕ → ℂ)
    (mod : ι → ℕ) (chi : ∀ i, DirichletCharacter ℂ (mod i))
    (hpos : ∀ i, 0 < mod i) (hle : ∀ i, mod i ≤ Q)
    (hprim : ∀ i, (chi i).IsPrimitive)
    (hinj : Function.Injective
      (fun i => (⟨mod i, chi i⟩ : (q : ℕ) × DirichletCharacter ℂ q))) :
    ∑ i, ‖charSum (mod i) N a (chi i)‖ ^ 2 ≤ sieveBudget N Q * l2sq N a :=
  family_le_of_full multiplicative_large_sieve Q N a mod chi hpos hle hprim hinj

/-- **(I6b) Bridge Form 1 → Form 2.** The full-family statement, quantified over all
`Q`, `N`, `a`, implies the subfamily statement.

Paper §6.
No gap.
Depends on: `multiplicative_large_sieve` (as hypothesis), `sum_familyQ`, `familyQ`.

The hypothesis is stated as a `∀`-quantified copy of Form 1 rather than by citing
`multiplicative_large_sieve` directly, so that the bridge is provable independently of the
additive gap and the dependency is visible in the signature.

Rule 17: none. -/
theorem multiplicative_large_sieve_family_of_full
    (hfull : ∀ (Q N : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q N a χ‖ ^ 2
        ≤ sieveBudget N Q * l2sq N a)
    {ι : Type*} [Fintype ι] (Q N : ℕ) (a : ℕ → ℂ)
    (mod : ι → ℕ) (chi : ∀ i, DirichletCharacter ℂ (mod i))
    (hpos : ∀ i, 0 < mod i) (hle : ∀ i, mod i ≤ Q)
    (hprim : ∀ i, (chi i).IsPrimitive)
    (hinj : Function.Injective
      (fun i => (⟨mod i, chi i⟩ : (q : ℕ) × DirichletCharacter ℂ q))) :
    ∑ i, ‖charSum (mod i) N a (chi i)‖ ^ 2 ≤ sieveBudget N Q * l2sq N a :=
  family_le_of_full hfull Q N a mod chi hpos hle hprim hinj

/-! ### 5.1 The `Finset` face of the subfamily form

The five consumption sites sum over a `Finset` of `(q, χ)` pairs — `familyQ Q`,
`familyDyadic Q`, or a `Finset.filter` of one of them by `ZetaQ.parity` (§12.3's parity
subfamilies). These three declarations are the glue that lets them do so directly. -/

/-- **Glue: the `Σ_{q≤Q} Σ*_χ` double sum IS the sum over `familyQ Q`.**

Paper §1.1, §2.2 (`𝔉_Q`); §6.
Depends on: `familyQ`.

Rule 17: none. -/
theorem sum_familyQ (Q : ℕ) (F : ((q : ℕ) × DirichletCharacter ℂ q) → ℝ) :
    ∑ x ∈ familyQ Q, F x = ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, F ⟨q, χ⟩ :=
  Finset.sum_sigma _ _ _

/-- **Lemma 6.1 for an arbitrary sub-`Finset` of the family** — the shape the five
consumption sites literally apply.

Paper §6, consumed at Lemma 4.3, Lemma 4.4,
Lemma 4.5, Lemma 8.1, and
§12.3's parity projector.
Depends on: `multiplicative_large_sieve_family`, `sum_familyQ`, `familyQ`.

**Instances, at no further cost:** the dyadic family of Corollary 2 is
`F := familyDyadic Q` with `familyDyadic_subset_familyQ`; the parity subfamilies of §12.3
are `F := (familyQ Q).filter (fun x => ZetaQ.parity x.2 = 0)` (resp. `= 1`), which is a
subset of `familyQ Q` by `Finset.filter_subset`. Both keep the SAME budget
`sieveBudget N Q` — the F10 choice (`Q_ASPECT_V2`).

Rule 17: none. -/
theorem multiplicative_large_sieve_subfamily (Q N : ℕ) (a : ℕ → ℂ)
    (F : Finset ((q : ℕ) × DirichletCharacter ℂ q)) (hF : F ⊆ familyQ Q) :
    ∑ x ∈ F, ‖charSum x.1 N a x.2‖ ^ 2 ≤ sieveBudget N Q * l2sq N a := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hF (fun _ _ _ => by positivity)) ?_
  rw [sum_familyQ]
  exact multiplicative_large_sieve Q N a

/-- The dyadic family of Corollary 2 sits inside the `q ≤ Q` family — the hypothesis
`multiplicative_large_sieve_subfamily` needs to deliver Corollary 2's sieve step at the
**same** budget `N + Q² − 1`.

Paper: Corollary 2 (the dyadic family `q ∈ (Q/2, Q]`); the same-`Q²` choice is
`Q_ASPECT_V2` (round-3 finding F10).
Depends on: `familyQ`, `familyDyadic`.

Rule 17: none. -/
theorem familyDyadic_subset_familyQ (Q : ℕ) : familyDyadic Q ⊆ familyQ Q :=
  Finset.sigma_mono
    (fun x hx => by
      simp only [Finset.mem_Ioc] at hx
      simp only [Finset.mem_Icc]
      omega)
    (fun _ => Finset.Subset.refl _)

end ZetaQ

