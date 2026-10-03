/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ChallengeDeps/FollowUpFamily.lean — the TRUSTED definition layer of the comparator topic `FollowUpFamily` (the family
follow-up paper: simple zeros on the critical line in the family of primitive Dirichlet L-functions of modulus
1 < q ≤ Q). Definitions only; no theorem. Imports only Mathlib.

Everything here lives in the namespace `FollowUpFamily`. Each `def`/`structure` is a character-for-character copy of the
one of the same name in the Lean development's statement layer `ZetaShell/Challenge.lean` (namespace `ZetaShell`, the
architect's Mathlib-only layer); only the doc-strings are edited. `Solution/FollowUpFamily.lean` converts between the two
(by `rfl` and field by field: proofs, checked by comparator, not trusted).

Contents
  §1 primitive characters; the nontrivial zeros of Mathlib's `DirichletCharacter.LFunction` (0 < Re ρ < 1), their
     multiplicity (`analyticOrderAt`); the window counts N_χ(T₁,T₂) (with multiplicity) and N^s_{0,χ}(T₁,T₂) (simple
     zeros on the critical line); the family sums over the moduli 1 < q ≤ Q; the height T = (log Q)^{r+ε};
  §2 the rectangle count N*(σ,T,Q) (ζ included) and the one displayed analytic hypothesis `ZeroDensityInput`: the
     zero-density estimates (J) of Jutila and (M) of Montgomery (in Bombieri's form), Paper B §ssec:shell-density,
     stated as in the sources.
Nothing else is needed: the constants 0.7235 and 0.9059137927 are written out in the statements.
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace FollowUpFamily

/-! ## §1 Primitive characters, zeros, window counts -/

open DirichletCharacter in
/-- `Σ*_{χ mod q}`: the primitive Dirichlet characters mod `q` (Mathlib's `DirichletCharacter.IsPrimitive`:
conductor = q). For `q = 1` this is the trivial character, whose L-function is `riemannZeta`. -/
def primChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  Finset.univ.filter (fun χ => χ.IsPrimitive)

section zeros
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- `ρ` is a nontrivial zero of `L(s,χ)`: `L(ρ,χ) = 0` with `0 < Re ρ < 1`. -/
def IsNtZero (ρ : ℂ) : Prop := χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- `m_ρ`: the order of vanishing of `L(·,χ)` at `ρ`. -/
def zmult (ρ : ℂ) : ℕ := (analyticOrderAt χ.LFunction ρ).toNat

/-- The nontrivial zeros `ρ` with `T₁ < Im ρ ≤ T₂`. -/
def zerosWin (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNtZero χ ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- `N_χ(T₁,T₂)`: the nontrivial zeros with `T₁ < Im ρ ≤ T₂`, counted with multiplicity. -/
def Nwin (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosWin χ T₁ T₂, zmult χ ρ

/-- `N^s_{0,χ}(T₁,T₂)`: the zeros of the window that are simple and lie on the critical line. -/
def N0sWin (T₁ T₂ : ℝ) : ℕ :=
  (zerosWin χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zmult χ ρ = 1}).ncard

/-- The zeros in the closed rectangle `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` (of Jutila and Bombieri; for `σ > 0` they are
nontrivial zeros). -/
def zerosRect (σ T : ℝ) : Set ℂ := {ρ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T}

/-- `N(σ,T,χ)`: the zeros of the rectangle, counted with multiplicity. -/
def NrectC (σ T : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosRect χ σ T, zmult χ ρ

end zeros

/-- `N_χ(T₁,T₂)` as a real number. The guard `q = 0` (where Mathlib's `LFunction` needs `NeZero q`) is never reached:
the sums below run over `q ≥ 1`. -/
def Nchi (q : ℕ) (χ : DirichletCharacter ℂ q) (T₁ T₂ : ℝ) : ℝ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩; ((Nwin χ T₁ T₂ : ℕ) : ℝ)

/-- `N^s_{0,χ}(T₁,T₂)` as a real number (same guard). -/
def N0schi (q : ℕ) (χ : DirichletCharacter ℂ q) (T₁ T₂ : ℝ) : ℝ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩; ((N0sWin χ T₁ T₂ : ℕ) : ℝ)

/-- `N(σ,T,χ)` as a real number (same guard). -/
def Nrect (q : ℕ) (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℝ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩; ((NrectC χ σ T : ℕ) : ℝ)

/-- The moduli of the family `𝔉_Q` of the paper: `1 < q ≤ Q` (ζ excluded). -/
def modQle (Q : ℕ) : Finset ℕ := Finset.Icc 2 Q

/-- `Σ_{q∈M} Σ*_{χ mod q} N_χ(T₁,T₂)`. -/
def famN (M : Finset ℕ) (T₁ T₂ : ℝ) : ℝ := ∑ q ∈ M, ∑ χ ∈ primChars q, Nchi q χ T₁ T₂

/-- `Σ_{q∈M} Σ*_{χ mod q} N^s_{0,χ}(T₁,T₂)`. -/
def famN0s (M : Finset ℕ) (T₁ T₂ : ℝ) : ℝ := ∑ q ∈ M, ∑ χ ∈ primChars q, N0schi q χ T₁ T₂

/-- The window height of both theorems: `T = (log Q)^{r+ε}`. -/
def twin (Q r ε : ℝ) : ℝ := Real.log Q ^ (r + ε)

/-! ## §2 The zero-density input (the one displayed analytic hypothesis of Theorem thm:shell) -/

/-- `N*(σ,T,Q) = Σ_{q ≤ Q} Σ*_{χ mod q} N(σ,T,χ)`, over PRIMITIVE characters, `q = 1` (that is, `ζ`) INCLUDED, as in
both sources (Paper B, ssec:shell-density). -/
def Nstar (Q : ℕ) (σ T : ℝ) : ℝ := ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primChars q, Nrect q χ σ T

/-- **(J): Jutila 1977, Theorem 1, (1.8)** [Math. Scand. 41 (1977)], as quoted in Paper B, ssec:shell-density: for
every `ε > 0`, `N*(α,T,Q) ≪_ε (Q²T)^{(2+ε)(1−α)}` for `4/5 ≤ α ≤ 1`, `T ≥ 1`, `Q ≥ 1`; the implied constant depends on
`ε` only; no factor of `log`. -/
def JutilaHybrid : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T → ∀ α : ℝ, 4 / 5 ≤ α → α ≤ 1 →
    Nstar Q α T ≤ C * ((Q : ℝ) ^ 2 * T) ^ ((2 + ε) * (1 - α))

/-- **(M): Montgomery's hybrid estimate, in the form of Bombieri, Astérisque 18, §10, Théorème 20** (p. 77), as quoted in
Paper B, ssec:shell-density: there is `A` such that `N*(α,T,Q) ≪ (TQ²)^{3(1−α)/(2−α)} (log TQ)^A` for `1/2 ≤ α ≤ 1`,
`T ≥ 2`, `Q ≥ 1`, with an absolute implied constant. The power `A` is existential (Bombieri's proof gives `A = 19`), so
this Prop is implied by the printed statement. -/
def MontgomeryHybrid : Prop :=
  ∃ A C : ℝ, ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 2 ≤ T → ∀ α : ℝ, 1 / 2 ≤ α → α ≤ 1 →
    Nstar Q α T ≤ C * ((T * (Q : ℝ) ^ 2) ^ (3 * (1 - α) / (2 - α)) * Real.log (T * Q) ^ A)

/-- **`ZeroDensityInput`**: (J) and (M) together, the hypothesis of Theorem thm:shell. Both are published unconditional
theorems; the development does not prove them, so they are displayed as a hypothesis. -/
structure ZeroDensityInput : Prop where
  jutila : JutilaHybrid
  montgomery : MontgomeryHybrid

end FollowUpFamily
