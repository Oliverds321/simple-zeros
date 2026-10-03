# Comparator topic `FollowUpFamily`: the family follow-up paper

The files of this topic let a third party check, with [comparator](https://github.com/leanprover/comparator), **what** the
family paper's Lean development proves about the zeros of Mathlib's `DirichletCharacter.LFunction`. You do not need to read
the proofs.

The general layout and the comparator conventions are in `README.md` in this directory.

## What is proved

Let 𝔉_Q be the primitive Dirichlet characters χ mod q with 1 < q ≤ Q. For χ ∈ 𝔉_Q let N_χ(T₁,T₂) be the number of zeros ρ of
L(s,χ) with 0 < Re ρ < 1 and T₁ < Im ρ ≤ T₂, counted **with multiplicity**, and N^s_{0,χ}(T₁,T₂) the number of those that are
simple and have Re ρ = 1/2. Fix r ≥ 3, ε > 0 and put T = (log Q)^{r+ε}. Both theorems say: there are Q₀ and c > 0 such that for
every integer Q ≥ Q₀

  (P − c·E(Q)) · Σ_{χ∈𝔉_Q} N_χ(T,2T) ≤ Σ_{χ∈𝔉_Q} N^s_{0,χ}(T,2T),

with

| theorem | paper | P | E(Q) | hypothesis | level |
|---|---|---|---|---|---|
| `family_simple_on_line_killed` | Theorem thm:one-prime (killed kernel) | 0.7235 | log log Q / log Q | none | A |
| `family_simple_on_line_shell` | Theorem thm:shell (the Shell kernel) | 0.9059137927 | (log Q)^{−θ}, any 0 < θ < 503/1994 | `ZeroDensityInput` | C (one displayed hypothesis) |

**Axioms.** Both theorems use only `propext`, `Classical.choice` and `Quot.sound`. Neither contains `sorry` or
`native_decide`, and neither declares an `axiom`. The hypothesis of the second enters as an explicit binder, not as an axiom.

## The hypothesis `ZeroDensityInput`

It is the conjunction of two published zero-density estimates for N*(σ,T,Q) = Σ_{q≤Q} Σ*_{χ mod q} N(σ,T,χ), where N(σ,T,χ)
counts the zeros of L(s,χ) in the closed rectangle σ ≤ Re ρ ≤ 1, |Im ρ| ≤ T with multiplicity, over primitive characters,
with ζ (the character mod 1) included, as in both sources:

| field | source | statement |
|---|---|---|
| `jutila` (J) | Jutila, Math. Scand. 41 (1977), Theorem 1, (1.8) | for every ε > 0: N*(α,T,Q) ≪_ε (Q²T)^{(2+ε)(1−α)} for 4/5 ≤ α ≤ 1, T ≥ 1, Q ≥ 1 |
| `montgomery` (M) | Montgomery (1969), in the form of Bombieri, Astérisque 18, §10, Théorème 20 | there is A with N*(α,T,Q) ≪ (TQ²)^{3(1−α)/(2−α)} (log TQ)^A for 1/2 ≤ α ≤ 1, T ≥ 2, Q ≥ 1 |

Neither is strengthened: Jutila's exponent, range and ε-dependence are kept, and Bombieri's power A (his proof gives A = 19)
is existential. Both are unconditional theorems in the literature; the development does not prove them, so the paper and
this package display them as the one hypothesis of Theorem thm:shell.

## Trusted and untrusted files

| file | trusted? | role |
|---|---|---|
| `ChallengeDeps/FollowUpFamily.lean` | yes | Mathlib only: primitive characters, zeros, multiplicity (`analyticOrderAt`), the window counts and family sums, T = (log Q)^{r+ε}, N*, (J), (M), `ZeroDensityInput` |
| `Challenge/FollowUpFamily.lean` | yes | the two statements, proofs `sorry` |
| `config-followup-family.json` | yes | the theorem names and the permitted axioms |
| `Solution/FollowUpFamily.lean`, libraries `ZetaShell`, `ZetaQ`, `Zeta23` | no | the proofs; comparator checks them |

## Reading notes

- The family excludes q = 1 (ζ); the density sums N* include it, as the sources do.
- Windows are T < Im ρ ≤ 2T (positive ordinates); a zero ρ of L(s,χ) with Im ρ < 0 gives the zero ρ̄ of L(s,χ̄), and χ̄
  is in the family.
- The counts are real numbers built with a guard `q = 0` that the sums never reach (Mathlib's `LFunction` needs
  `NeZero q`).
- Lean's `finsum` and `ncard` return 0 on an infinite set. Every window of a family member is finite, and the family count
  Σ_χ N_χ(T,2T) tends to infinity (both follow from theorems of the development at level A; they are not stated as
  theorems of this topic), so the counts are genuine and the inequality is not trivial. In the hypothesis a junk value
  could only make (J) and (M) weaker.
- c·log log Q/log Q is written `c * Real.log (Real.log Q) / Real.log Q`, i.e. (c·log log Q)/log Q.

## How to check

The quick check needs no extra tooling. Every line must read `… depends on axioms: [propext, Classical.choice, Quot.sound]`.

```bash
lake build Challenge.FollowUpFamily Solution.FollowUpFamily
lake env lean comparator/PrintAxioms/FollowUpFamily.lean
```

(`lake build Challenge Solution` builds only the root modules `Challenge.lean`, `Solution.lean`; name the topic modules.)

**Full comparator run.** Follow the steps of `README.md`, with the config of this topic:

```bash
lake env /path/to/comparator comparator/config-followup-family.json
```

Comparator builds `Challenge.FollowUpFamily` and `Solution.FollowUpFamily` in its sandbox, checks that the two statements
coincide, audits the axioms and replays the proofs in the kernel (optionally also in nanoda).
