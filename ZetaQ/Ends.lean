/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Ends.lean — paper §8, "The ends": Lemma 8.1 (family mean square), Lemma 8.1′ (the
separated form), Lemma 8.2 (bilinear ends bound), and the six instantiation obligations
S1–S6 that consume [R]'s (B, ν)-generic ends seam.

Statement source of truth: paper §8.  Derivations: `LEMMA_QE` §§QE.i–QE.iii, `NOTE_QR`
§QR.1 and §QR.4, `NOTE_QG` §g.2/§g.4.

──────────────────────────────────────────────────────────────────────────────────────────
THE SEAM.  [R]'s ends layer declares itself generic in `(B, ν)` at one place, verbatim
(`Zeta23/PrimeSideA/EndsCore.lean:71-74`):

    ν-GENERIC LAYER (for Theorem E): every object below that involves the density is
    stated for an ABSTRACT `ν : ℝ → ℝ` (hypotheses: `Continuous ν` and `NuBound p B ν` for
    a free `B ≥ 0`); ζ is the instantiation `ν := Zeta23.nuX p.X`, `B := Bconst p`.

`Bconst p = p.l + 4√X` is the T-aspect's pointwise bound — the λ ≤ 1 wall.  This file
**never** mentions `Bconst` and **never** calls `nuBound_eventually`.  The q-aspect
substitutes a FAMILY MEAN SQUARE `B_fam ≍ Qℒ` for the pointwise bound; that substitution is
Lemma 8.1, and it is the entire reason §8 survives at λ* = 1.2507 > 1.

──────────────────────────────────────────────────────────────────────────────────────────
RULE 17.  Every [R] lemma cited here is a **cap-free `_L` variant**:
  * `Zeta23.PrimeSide.calE1_maj_bound_L` (`EndsE1.lean:727`)
  * `Zeta23.PrimeSide.calE2_maj_bound_L` (`EndsE2.lean:353`)
  * `Zeta23.PrimeSide.abs_calE1_le_maj`  (`EndsE1.lean:844`)
  * `Zeta23.PrimeSide.abs_calE2_le_maj`  (`EndsE2.lean:84`)
  * `Zeta23.PrimeSide.LocalHypsCoreW`    (`Basic.lean:559`) — `LocalHypsCore` MINUS `lam_le_one`.
The capped twins `calE1_maj_bound` (`EndsE1.lean:616`), `calE2_maj_bound`
(`EndsE2.lean:266`), `calE1_bound` (`:888`), `calE2_bound` (`:437`), `lem_ends_nu_W`
(`Ends.lean:64`), `lem_ends_nu` (`:114`) and `lem_ends` (`:143`) all carry `p.L ≤ 2 * p.l`
(and/or `lam ≤ 1`).  `p.L ≤ 2*p.l` is the bandwidth cap in T-aspect disguise: at our
parameters `L/(2l) ≈ 8.9` at Q = 10¹⁰⁰ and ≈ 57.5 at Q = 10¹⁰⁰⁰ — false by 10–60×.
**DO NOT CITE THEM.**  (NOTE_QR §QR.4.)

──────────────────────────────────────────────────────────────────────────────────────────
THE CRITICAL ITEM — see `Bends`, `S5_LB_le_Bends` and
`naive_Bends_fails` below for the full write-up.  `calE2_maj_bound_L` carries the absorbing
hypothesis `p.L ≤ B`.  At the paper's own displayed normalisation (`B := ℒ + C₀`) this reads
`λℒ ≤ ℒ + 6`, i.e. `ℒ ≤ 23.93` — FALSE at every scale in range.  The repair implemented
here is the SEPARATED envelope (Lemma 8.1′) at scale `s := c_μ Q`, `c_μ = 3/π³`; it costs
nothing (`s²B² = (c₁Q)²(ℒ+C₀)²` identically) and leaves paper §8's displayed constant
untouched.

🚩 **`Bfam_le_sep`'s `hδ` is `1/2 ≤ δ`, and it had to be strengthened to that.**
`hδ : 0 < δ` is too weak for `c₁ = 0.41`: `c₁ = √(9/π⁶ + λ*²/π²)` is
calibrated to `log X = λ*ℒ` with essentially zero room, while `hX : X ≤ Q^{2−δ}` at an
unconstrained `δ > 0` permits `log X` up to ≈ `2ℒ`, and §8's only P-part route (Lemma 6.1 at
fixed τ) then overshoots by 16 % already at `δ = 0.1, Q = 10¹⁰⁰, T = 300`.  Hence
**`hδ : 1/2 ≤ δ`**.

**The other candidate repair, `hX : X ≤ P.XQ`, is REFUTED and was not taken.**  `P.XQ = (QT/2π)^λ`
bounds `X` against `QT`, not against `Q²`, and `P.Valid` ties `T` to nothing; the modulus
`q = 1` sits in every family and contributes `|ν_{X,1}(0)| ∼ (2/π)√X`, so the conclusion
*forces* `X ≲ 0.415·Q²(ℒ+C₀)²` — the sieve-efficiency shape, which is what `hX` already
says.  Failing instance for that candidate (at the paper's own `λ*`, so not a `lam_lt_two`
artefact): `Qn = 1, τ = 0, Q = 20, T = 2πe³⁰, λ = λ*` gives `Bfam ≈ 5.8×10⁸` against
`RHS = 319.8`.  Full write-up, arithmetic and δ-floor accounting at `Bfam_le_sep`.

🚩 **`Bfam_le_sep` IS PROVED, and it needs `Q ≥ 10⁹`.**  The three inputs are in §1.0
below: the q-uniform digamma envelope (`abs_muq_le`), the `Σ_{q≤Qn}φ*(q)` count
(`famCount_le`, from §12.2 — see the import note below) and the explicit
Chebyshev–Mertens constant (`cheb_sq_div_le`).  The δ-floor `1/2 ≤ δ` did not have to be
raised, but the count is a `Q₀`-threshold statement, so the hypothesis `hQ0 : 10⁹ ≤ P.Q`
is carried; the full accounting is at `Bfam_le_sep` under "THE δ-FLOOR AND THE Q-FLOOR",
and `Bfam_sq_le` tracks the same hypothesis.

🚩 **`hΓ` and `hcoeff` are NOT hypotheses of `Bfam_le_sep` / `Bfam_sq_le`.**  They were,
and both turned out to be unused: the `GammaFactsChi` fields are `∃ C`, hence not
q-uniform, so the proof uses `Zeta23.ThmE.GammaChi`'s concrete conductor-free constants
instead, and the sieve interface needs no unimodularity.
`hΓ : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), GammaFactsChi (parity χ) q` was quantified over
ALL `q : ℕ` and is FALSE at `q = 0` (the Stirling clause of `muq κ 0 τ` fails), so every
downstream statement that threaded it (`HFrob.hsep_of_gammaZero`) had to carry a vacuous
`q = 0` clause; since neither hypothesis is consumed by the proof, both are dropped and
`HFrob.hsep_of_design` discharges Lemma 8.1′ along the design from the tree alone.

──────────────────────────────────────────────────────────────────────────────────────────
🚩 **THIS FILE IMPORTS `ZetaQ.Normalisation`, and that is a deliberate edge.**

`famCount_le` consumes §12.2's `ZetaQ.Normalisation.N2.Astar_bound`
(`|Σ_{q≤N} φ*(q) − (18/π⁴)N²| ≤ 5N(1 + log N)²`, sorry-free) and
`N2.harmonic_bound`.  No cycle results: `Normalisation` imports `Defs`, `CharSums` and
`Payoff`, none of which imports `Ends`.  (`ZetaQ/Zones.lean` does import `Ends`, and it is
above `Normalisation` in the graph, so the edge added here is still acyclic.)

*Why this and not the alternatives.*  Duplicating the Möbius-hyperbola development here
would put the same ≈ 400-line argument in two places and invite the two copies to drift;
hoisting it into `ZetaQ/Defs.lean` is not available (Defs is frozen, and the count is a
theorem, not a definition).  And the dependency is real rather than incidental: paper §8's
own P-part goes "by Lemma 6.1 at fixed τ" against a family whose size is `≍ Q²`, i.e. §8's
ends bound genuinely consumes §12.2's family count.

──────────────────────────────────────────────────────────────────────────────────────────
DEVIATIONS FROM THE FROZEN `ZetaQ/Defs.lean`.  The proposed shared objects
(`SettingQ`, `Family`, `nu`, `envQ`, `Bends`, `cμ`, `C2'`, `Lcal`, `LargeSieve`, …) are NOT
in the frozen Defs.  Defs supplies `ParamsQ` (with `LL = ℒ`, `LB = L = λℒ`, `XQ = X`),
`primitiveChars`, `parity`, `nuQ`, `famCard`, `c1Ends`, `C0Ends` — so this file:
  * uses the CONCRETE family `Σ_{q ≤ Qn} Σ*_{χ mod q}` (`famSum`) rather than an abstract
    `Family` bundle, because `Defs.nuQ` and `Defs.famCard` already made that choice;
  * defines `toSetting`, `cMu`, `Bends`, `envQ`, `envSep`, `C1ends`, `C2ends`, `r5`,
    `Bfam`, `LargeSieveHyp` LOCALLY.
-/
import ZetaQ.Defs
import ZetaQ.Window
import ZetaQ.Sieve
import ZetaQ.Gallagher
import ZetaQ.Normalisation

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction
open MeasureTheory
open Zeta23.PrimeSide

namespace ZetaQ
namespace Ends

/-! ## 0. Local objects

Everything in this section is a `def` with a real body, each with its provenance. -/

/-- `ν_{X,χ}` at a FREE `X`: [R]'s `Zeta23.ThmE.nuXc` (`ThmE/Hypotheses.lean:60`) at the
coefficient sequence `n ↦ χ(n)` and the parity `κ(χ)` of `ZetaQ.parity`.  Identical to
`ZetaQ.nuQ` at `X := P.XQ` (see `nuFam_eq_nuQ`); `X` is exposed as an argument so that the
**absence of `X` from Lemma 8.1's right-hand side is visible in the statement**. -/
def nuFam (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (τ : ℝ) : ℝ :=
  Zeta23.ThmE.nuXc (parity χ) q (fun n => χ (n : ZMod q)) X τ

/-- `nuFam` at the paper's `X = (QT/2π)^λ` IS `Defs.nuQ`. -/
theorem nuFam_eq_nuQ (P : ParamsQ) (q : ℕ) (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    nuFam P.XQ χ τ = nuQ P q χ τ := rfl

/-- `Σ*_{q ≤ Qn} Σ*_{χ mod q}` — the family sum over `𝔉_Q` = {primitive χ of modulus q ≤ Qn}.
Spelled with `Finset.Icc 1 Qn` and `ZetaQ.primitiveChars` exactly as `Defs.famCard`, so
`famSum Qn (fun _ _ => 1) = famCard Qn` after casting. -/
def famSum (Qn : ℕ) (f : (q : ℕ) → DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Qn, ∑ χ ∈ primitiveChars q, f q χ

/-- `B_fam(τ)² := Σ_χ ν_{X,χ}(τ)²` (paper §8). -/
def BfamSq (Qn : ℕ) (X τ : ℝ) : ℝ := famSum Qn (fun _ χ => nuFam X χ τ ^ 2)

/-- `B_fam(τ) := (Σ_χ ν_{X,χ}(τ)²)^{1/2}` (paper §8). -/
def Bfam (Qn : ℕ) (X τ : ℝ) : ℝ := Real.sqrt (BfamSq Qn X τ)

/-- `log⁺(|τ|/4T)`, spelled as the literal body of [R]'s `NuBound`
(`Zeta23/PrimeSideA/EndsCore.lean:63-64`): `max (Real.log (|τ| / (4 * p.T))) 0`.
The coefficient on this term inside `NuBound` is **exactly 1** — that single fact is what
forces the homogeneity normalisation of Lemma 8.2 and, through it, the failure recorded
at `naive_Bends_fails`. -/
def logPlusQ (P : ParamsQ) (τ : ℝ) : ℝ := max (Real.log (|τ| / (4 * P.T))) 0

/-- `c_μ := 3/π³ ≈ 0.09675` — **the μ-part's own `log⁺` coefficient**, read off NOTE_QR §QR.1's
numeric display: the `log⁺` enters `B_fam` ONLY through the digamma envelope, with
coefficient `Q·√(2·(18/π⁴)/(4π²)) = Q·3/π³`.  The prime part is τ-independent
(`‖a(τ)‖₂² = Σ_{n≤X} Λ(n)²/n` does not move under the τ-twist), so it never touches the
`log⁺` growth (LEMMA_QE §QE.i).  `c_μ ≈ c₁/4.24`.

**This constant is the whole repair of that failure.**  It is NEW (not in `Defs`); see the
header. -/
def cMu : ℝ := 3 / Real.pi ^ 3

/-- `0 < c_μ`. -/
theorem cMu_pos : 0 < cMu := by
  unfold cMu; positivity

/-- `c_μ ≤ c₁` (`3/π³ ≈ 0.0968 ≤ 0.41`).  This is what makes Lemma 8.1′ imply the
paper-verbatim Lemma 8.1.

Paper §8.
Rule 17: no hypotheses at all. -/
theorem cMu_le_c1Ends : cMu ≤ c1Ends := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi3 : (27 : ℝ) < Real.pi ^ 3 := by
    have := pow_lt_pow_left₀ hpi (by norm_num : (0:ℝ) ≤ 3) (by norm_num : 3 ≠ 0)
    norm_num at this; exact this
  unfold cMu c1Ends
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- `env(τ) := ℒ + C₀ + log⁺(|τ|/4T)` — the paper-verbatim envelope, i.e. `B_fam/(c₁Q)` at
the bound of Lemma 8.1.  `NuBound` holds for it at `B := ℒ + C₀` — but **that `B` fails
`calE2_maj_bound_L`'s hypothesis `p.L ≤ B`** (see `naive_Bends_fails`), which is why
`envSep` and not `envQ` is the function actually passed to [R]'s `_L` lemmas. -/
def envQ (P : ParamsQ) (τ : ℝ) : ℝ := P.LL + C0Ends + logPlusQ P τ

/-- `B_ends := c₁(ℒ + C₀)/c_μ ≈ 4.238·(ℒ + C₀)` — **the `B` we actually pass to
`calE1_maj_bound_L` / `calE2_maj_bound_L`.**

*Why this and not `ℒ + C₀`.*  `calE2_maj_bound_L` (`EndsE2.lean:353`) carries the absorbing
hypothesis `p.L ≤ B`.  Under the paper's own normalisation — divide `B_fam` by `c₁Q`, so
`ν := envQ P` and `B := ℒ + C₀` — this reads

    λ·ℒ ≤ ℒ + C₀  ⟺  (λ − 1)ℒ ≤ 6  ⟺  ℒ ≤ 6/0.2507321515 = 23.93,

and since `ℒ = log(QT/2π) ≥ log Q` this holds only for `Q ≲ 3×10¹⁰`.  It is **FALSE at every
scale in the paper's range** (at Q = 10¹⁰⁰: ℒ ≈ 247.7, L ≈ 309.8 vs `ℒ + C₀` = 253.7 — fails
by 1.221×; asymptotically by λ* = 1.2507×).  See `naive_Bends_fails`.

*The repair, and why it is free.*  Normalise instead by `s := c_μ Q` (Lemma 8.1′, which is
what LEMMA_QE §QE.i's proof actually delivers) and take `B := B_ends`.  Then
  * `NuBound (toSetting P) (Bends P) (envSep P)` holds with coefficient exactly 1 on the
    `log⁺` — `S4_nuBound_envSep`;
  * `p.L ≤ B` becomes `λℒ ≤ 4.238(ℒ + 6)`, true with a factor **3.39 of room** at λ* —
    `S5_LB_le_Bends`;
  * the product entering the bound is `s²B² = (c_μQ · c₁(ℒ+C₀)/c_μ)² = (c₁Q)²(ℒ+C₀)²`,
    **numerically identical to NOTE_QR §QR.1's display — zero constant lost, paper §8's
    displayed constant unchanged** — `scale_sq_mul_Bends_sq`.

*Why the naive fallback is NOT taken.*  The alternative repair is `B := max(p.L, ℒ + C₀)`,
which equals `p.L = λℒ` throughout the range, so `p.L ≤ B` holds by `le_max_left`.  Cost:
the 𝓔₂ term inflates by `(λℒ/(ℒ+C₀))² → λ*² = 1.5643`.  Because 𝓔₂ dominates 𝓔₁ by ≈ 125×
at the design (`C₂′(1+log L) ≈ 3.0×10⁵` vs `4(90+32c_ϱ²) = 2408` at `c_ϱ = 4`, `L ≈ 310`),
the family relative-order constant moves by a factor λ*² = 1.5643.  ⚠ **The figures "≈ 5.7 →
≈ 8.9" this paragraph used to quote are SUPERSEDED** — both were computed from
NOTE_QR §QR.1's "relative order" chain, which drops the very bracket displayed two lines
above; the true constants are `≈ 3.7×10⁵ → ≈ 5.8×10⁵`.  The conclusion is unchanged and if
anything strengthened: the separated form is still the route, because it is free
(`scale_sq_mul_Bends_sq`) while the fallback costs a further 1.56×.  See `r5`. -/
def Bends (P : ParamsQ) : ℝ := c1Ends * (P.LL + C0Ends) / cMu

/-- `env_sep(τ) := B_ends + log⁺(|τ|/4T)` — the `NuBound`-shaped envelope at the separated
scale `s = c_μ Q`, i.e. the majorant of `B_fam/(c_μ Q)`.  **This is the `ν` handed to [R]'s
cap-free `_L` majorant bounds.** -/
def envSep (P : ParamsQ) (τ : ℝ) : ℝ := Bends P + logPlusQ P τ

/-- **The repair is free**: `(c_μ Q)² · B_ends² = (c₁ Q)² · (ℒ + C₀)²`.  Renormalising from
`c₁Q` to `c_μQ` changes nothing in the constant that reaches NOTE_QR §QR.1's display.

Paper §8. Rule 17: no hypotheses. -/
theorem scale_sq_mul_Bends_sq (P : ParamsQ) :
    (cMu * P.Q) ^ 2 * Bends P ^ 2 = (c1Ends * P.Q) ^ 2 * (P.LL + C0Ends) ^ 2 := by
  have h : cMu ≠ 0 := ne_of_gt cMu_pos
  unfold Bends
  field_simp

/-- The separated envelope, expanded: `c_μQ·env_sep(τ) = c₁Q(ℒ+C₀) + c_μQ·log⁺(|τ|/4T)`.
Bridges Lemma 8.1′'s paper-shaped statement to the `NuBound`-shaped `envSep`.

Rule 17: no hypotheses. -/
theorem scale_mul_envSep (P : ParamsQ) (τ : ℝ) :
    cMu * P.Q * envSep P τ
      = c1Ends * P.Q * (P.LL + C0Ends) + cMu * P.Q * logPlusQ P τ := by
  have h : cMu ≠ 0 := ne_of_gt cMu_pos
  unfold envSep Bends
  field_simp

/-- `C₁ = 4(90 + 32c_ϱ²)` — the witness of `Zeta23.PrimeSide.calE1_maj_bound_L`
(`EndsE1.lean:730`), given a name so paper §8's `4(90 + 32c_ϱ²)` is greppable.
**Cap-free.**  (The capped twin's constant is the larger `4(180 + 40c_ϱ²)`; not used.) -/
def C1ends (cϱ : ℝ) : ℝ := 4 * (90 + 32 * cϱ ^ 2)

/-- `C₂′ = 2(8 + 4·max(0, log c_ϱ) + 7c_ϱ)·CN2(c_ϱ)` — the witness of
`Zeta23.PrimeSide.calE2_maj_bound_L` (`EndsE2.lean:355-356`), with
`Zeta23.PrimeSide.CN2 cϱ = 100(1 + |log c_ϱ| + |c_ϱ|)` (`EndsNu.lean:36`).  **Cap-free.** -/
def C2ends (cϱ : ℝ) : ℝ := 2 * (8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * Zeta23.PrimeSide.CN2 cϱ

/-- `c_ends^proved = 2.5×10⁶` — **the ends row's coefficient at the window-constant FLOOR
`c_ϱ = 4`**, as [R]'s cap-free `_L` majorants deliver it there.  Paper §10.2 prints `6`;
NOTE_QR §QR.1 quotes ≈ 5.7.  Neither is what `ends_family_bound` gives.  The full accounting —
where the paper's 5.7 comes from, why it is wrong, and what does and does not break — is at
`r5` and at `ends_relative_le`.

⚠ **The `c_ϱ = 4` evaluation is a FLOOR that no window attains.**
`cRho ϱ = 4‖ϱ′‖_∞ + 4‖ϱ″‖₁ ≥ 12` for EVERY C¹ ramp from 0 to 1 (`‖ϱ′‖_∞ ≥ 1`, `‖ϱ″‖₁ ≥
2‖ϱ′‖_∞`); for [R]'s `rhoTwo` it is `c_ϱ(ϱ₂) = 12e⁻⁴/Θ(1) = 31.26`, and the artifact's window
constant is `P.cWin = c_ϱ + M₁λ + (M₁λ)² + M₂λ² ≈ 548` at the qle design (`≈ 1064` dyadic).
So the former figures "≈ 4.1×10⁵ at the design of record, ≈ 3.7×10⁵ over §10.4's range,
3.03×10⁵ in the limit" — the bracket `C₁(4) + C₂′(4)(1 + log L)` — were the formula at the
unattainable floor, NOT the artifact's row; `endsRowConstC` gives the real values
(`C_ends ≈ 1.2×10⁷` at `c_ϱ(ϱ₂)`, `≈ 2.9×10⁹` at `c_win`).  `ends_relative_le` is now stated at
the ACTUAL window constant `c_ϱ` of its `LocalHypsCoreW` hypothesis (the vacuous
`hcϱ : c_ϱ ≤ 4` is gone), with the coefficient `endsRowConstC c_ϱ = 10·C₁(c_ϱ) + 47·C₂′(c_ϱ)`;
this numeral is kept as the record of that computation at the floor (`endsRowConstC 4 ≤
2.52×10⁶`, `endsRowConstC_four_le`).  Theorem 1 never consumed it: the artifact's ends enter through
`ends_family_bound` at `P.cWin` (`FrobAssembly.endsMaj`), absorbed eventually.

`2.5×10⁶` is the coefficient provable **uniformly over `ends_relative_le`'s own hypothesis
class** (`ℒ ≥ 30`, `λ < 2`, `a ≥ 3/4`, `l ≤ L`) at `c_ϱ = 4`; the factor 6 over the pointwise
floor evaluation is the price of stating one numeral for the whole class rather than for the
design point (`(1+6/ℒ)² ≤ 1.44` against 1.049; `1 + l/L ≤ 2` against 1.055; `1/a² ≤ 16/9`
against ≈ 1; `(1+log L)/log ℒ ≤ 1.58` against 1.22). -/
def endsRowConst : ℝ := 2500000

/-- **The ends-row coefficient as a function of the window constant**:
`c_ends(c) := 10·C₁(c) + 47·C₂′(c)`, `C₁(c) = 4(90 + 32c²)` (`C1ends`), `C₂′(c) = C2ends c`.
This is what `ends_relative_le` delivers, uniformly over its hypothesis class, at ANY window
constant `c ≥ 4`: `≤ 2.52×10⁶` at the floor `c = 4` (`endsRowConstC_four_le`; cf. `endsRowConst`),
`≈ 8.2×10⁷` at `c_ϱ(ϱ₂) = 31.26`, `≈ 2.1×10¹⁰` at the artifact's `cWin ≈ 548`. -/
def endsRowConstC (c : ℝ) : ℝ := 10 * C1ends c + 47 * C2ends c

/-- `r₅ := c_ends^proved·ℒ log ℒ / T` — budget ledger row L₅, the ends charge (paper §8,
§10.2).  The live relative order is **Θ(ℒ log ℒ/T)** — that part of §8 is right, and it is
Θ and not merely O (the earlier `O(log ℒ · log log ℒ/T)` figure is SUPERSEDED, and LEMMA_QE
§QE.iii's "recorded as slack" line is RETRACTED: `B_fam ≥ √|𝔉|·ℒ/2π` is forced by the
μ-part).

──────────────────────────────────────────────────────────────────────────────────────────
🚩 **THE ENDS-ROW COEFFICIENT IS NOT `6`.**
(⚠ every numeral in the evaluation below is at the window-constant FLOOR
`c_ϱ = 4`, which no ramp attains — see `endsRowConst`; the row at the actual window constant is
`r5c c_ϱ` with `endsRowConstC`.)

Paper §10.2 charges `L₅ = 6ℒ log ℒ/T` and calls it "0.4 % of the budget — nothing
downstream moves".  `ends_family_bound` is now PROVED, so the constant it delivers can be
read off rather than estimated, and it is **≈ 3.7×10⁵ asymptotically, ≈ 4.1×10⁵ at the
design of record** — short by a factor ≈ 6×10⁴.

**Where the paper's 5.7 comes from, and why it is wrong.**  NOTE_QR §QR.1's displayed
family-ends lemma is

    Σ_χ|𝓔₁| + Σ_χ|𝓔₂| ≤ (c₁Q)²·L³(L+l)·(ℒ+C₀)²·[4(90 + 32c_ϱ²) + C₂′·(1 + log L)]

— exactly `ends_family_bound`.  But the note's own "relative order, the explicit chain",
two paragraphs later, reads

    2π·C·c₁²·(ℒ+C₀)²·l·log l / (a²·L·T·ℒ),

**with the bracket absent.**  Dividing the displayed lemma by the hat-normalised main term
gives `2π·C·c₁²·(L+l)(ℒ+C₀)²·[bracket]/(a²·L·T·ℒ)`, so the chain silently replaced
`(L+l)·[bracket]` by `l·log l`, dropping the numeric constants `4(90+32c_ϱ²) ≈ 2408` and
`C₂′`.  Evaluating the chain without the bracket gives `2πC_fam·c₁² = π⁵·0.1681/9 = 5.716`
— which **is** the note's ≈ 5.7, up to the `a²` and ε adjustments.  So NOTE_QR's own lemma
and its own chain disagree, by exactly the bracket; the lemma is the one that matches the
Lean tree, and the budget row is understated.

**The evaluation** (design of record: `Q = 10¹⁰⁰`, `ℒ = 247.7`, `T = (log Q)^{3.5} =
1.85×10⁸`, `l = 17.2`, `L = λ*ℒ = 309.8`, `c_ϱ = 4`, `a = 1`):
  * `C1ends 4 = 2408`, `CN2 4 = 638.63`, `C2ends 4 = 5.306×10⁴`,
    `C1ends + C2ends·(1 + log L) = 3.598×10⁵` — which reproduces the `Bends` docstring's own
    recorded expectation `C₂′(1 + log L) ≈ 3.0×10⁵ vs 4(90+32c_ϱ²) = 2408`, so these are the
    intended constants and not a mis-instantiation;
  * derivable LHS bound `= 4.11×10⁹·Q²`; `6ℒ log ℒ/T·𝒩 = 5.97×10⁴·Q²`; **ratio 6.9×10⁴**,
    tending to 6.2×10⁴ (because `log L = log λ*ℒ ∼ log ℒ`).  So the failure is a constant
    factor, not an order.

**What this does and does not break.**
  * **Theorem 1 is untouched.**  `ℒ log ℒ/T = log ℒ/ℒ^{2.5}` at `r = 3.5`, so the row still
    → 0 at any constant and the rate class is unchanged.  The asymptotic statement stands.
  * **§10.4's finite-Q orientation table does not survive it.**  At 3.7×10⁵ the ends row is
    75 at `Q = 10²⁵`, **2.72 at `10¹⁰⁰`**, 0.20 at `10³⁰⁰`, 1.1×10⁻² at `10¹⁰⁰⁰`,
    8.3×10⁻⁴ at `10³⁰⁰⁰`, against zone rows 0.23 / 0.078 / 0.031 / 0.011 / 4.2×10⁻³.  The
    row **exceeds 1 at `Q = 10¹⁰⁰`** and only falls below the zone terms near `Q ≈ 10¹⁰⁰⁰`.
    §10.4's "non-vacuous from ≈ 10²⁰" therefore moves by roughly a thousand orders of
    magnitude, and every figure of Table 2 with it.  This is not absorbable and is not
    absorbed: it is charged here.

**Why the row is restated rather than left `sorry`.**  D17: where a statement is unprovable
as written and the correct form is identifiable from the paper, the repair is made in the
tree.  §8 itself says the bilinear write-out with pinned constants "is in the companion
working notes; its Lean-level instantiation is deferred to the formalization" — this is that
deferred item, and the instantiation says what it says.  If a sharper evaluation of
`∬ majK₁/majK₂` than [R]'s `∃ C` witnesses exists (`CN2 c_ϱ = 100(1 + |log c_ϱ| + |c_ϱ|)`
alone is generous by orders), it is that route that must be formalised and the working note
that must say so; until then the artifact ships the constant it can prove.  This is the same
convention as D10's `bufferRowProved`.

⚠ Under the rejected fallback `B := max(p.L, ℒ+C₀)` the 𝓔₂ term inflates by λ*² = 1.5643,
moving the constant by ≈ 1.56× (the old figures "5.7 → 8.9" were computed without the
bracket and are superseded together with the 5.7); see `Bends`. -/
def r5 (P : ParamsQ) : ℝ := endsRowConst * P.LL * Real.log P.LL / P.T

/-- `r₅` at the window constant `c`: `c_ends(c)·ℒ log ℒ/T` — the row `ends_relative_le`
proves at the actual window constant of its `LocalHypsCoreW` hypothesis. `r5` is the same shape
with the floor numeral `endsRowConst` in place of `endsRowConstC c`. -/
def r5c (c : ℝ) (P : ParamsQ) : ℝ := endsRowConstC c * P.LL * Real.log P.LL / P.T

/-- `r₅` at the paper's printed coefficient `6` (paper §10.2, row L₅), retained so that
§10.4's table stays reconstructible and so that the gap between the paper's printed `6`
and the coefficient §8 actually delivers is a named object.
**It is NOT the row `ends_relative_le` proves** — see `r5`. -/
def r5Paper (P : ParamsQ) : ℝ := 6 * P.LL * Real.log P.LL / P.T

/-! ## S1. The bridge `ParamsQ → Zeta23.PrimeSide.Setting`

Obligation **S1** of the instantiation checklist: produce a
`Zeta23.PrimeSide.Setting` whose `L` is OUR `L = λℒ`, not [R]'s `λ·log(T/2π)`.

This is done by COMPOSING the frozen bridge of `Defs` with [R]'s own
`Zeta23.Params.toSetting` (`Zeta23/PrimeSideB/Concrete.lean:36`), so that no new arithmetic
is introduced: `Defs.ParamsQ.toParams` already sets `lam := LB / Zeta23.l T`.

⚠ **`(toSetting P).lam = λℒ/l ≈ 18 at Q = 10¹⁰⁰ and ≈ 116 at Q = 10¹⁰⁰⁰ — it is NOT λ\*.**
Nothing in the cap-free `_L` chain caps it (`LocalHypsCoreW` has `lam_pos` and no upper
bound, by construction).  `LocalHypsCoreW`'s docstring advertising the family regime as
`λ = L/l ∈ (1,2)` is a comment about [R]'s intent, not a hypothesis.
Nobody may "simplify" this bridge to `P.lam`. -/

/-- **S1** (the setting bridge).  [R]'s ends-layer scalar record at the paper's scale. -/
def toSetting (P : ParamsQ) : Zeta23.PrimeSide.Setting := P.toParams.toSetting P.T

@[simp] theorem toSetting_T (P : ParamsQ) : (toSetting P).T = P.T := rfl

@[simp] theorem toSetting_w (P : ParamsQ) : (toSetting P).w = P.w := rfl

/-- ⚠ NOT `P.lam`.  See the section docstring. -/
@[simp] theorem toSetting_lam (P : ParamsQ) :
    (toSetting P).lam = P.LB / Zeta23.l P.T := rfl

@[simp] theorem toSetting_l (P : ParamsQ) : (toSetting P).l = Zeta23.l P.T := rfl

/-- **S1, the point of the bridge**: `Setting.L (toSetting P) = λℒ`, the paper's `L`, not
`λ·log(T/2π)`.  Inherited from `Defs.ParamsQ.toParams_L`.

Paper §2.2 vs [R]'s `Setting.L` (`PrimeSideA/Defs.lean:71`).
Depends on: `ZetaQ.ParamsQ.toParams_L`.
Rule 17: hypothesis `Zeta23.l P.T ≠ 0` is `T ≠ 2π`, free in the regime `T ≥ 300`; it is a
nondegeneracy condition, not a bandwidth cap. -/
theorem S1_toSetting_L (P : ParamsQ) (h : Zeta23.l P.T ≠ 0) : (toSetting P).L = P.LB := by
  show P.toParams.L P.T = P.LB
  exact P.toParams_L h

/-- Consequently `X` at the bridge is the paper's `X = (QT/2π)^λ`. -/
theorem toSetting_X (P : ParamsQ) (h : Zeta23.l P.T ≠ 0) : (toSetting P).X = P.XQ := by
  show P.toParams.X P.T = P.XQ
  exact P.toParams_X h

/-- `h = 2π/L` matches paper §2.2's `hgridQ`. -/
theorem toSetting_h (P : ParamsQ) (h : Zeta23.l P.T ≠ 0) : (toSetting P).h = P.hgridQ := by
  show 2 * Real.pi / (toSetting P).L = 2 * Real.pi / P.LB
  rw [S1_toSetting_L P h]

/-- `d = ⌊LT/2π⌋` matches paper §2.2's `dQ`. -/
theorem toSetting_d (P : ParamsQ) (h : Zeta23.l P.T ≠ 0) : (toSetting P).d = P.dQ := by
  show ⌊(toSetting P).L * P.T / (2 * Real.pi)⌋₊ = ⌊P.LB * P.T / (2 * Real.pi)⌋₊
  rw [S1_toSetting_L P h]

/-- `τ_k = T + kh` matches paper §2.2's `tauQ`. -/
theorem toSetting_tau (P : ParamsQ) (h : Zeta23.l P.T ≠ 0) (k : ℤ) :
    (toSetting P).tau k = P.tauQ k := by
  show P.T + k * (toSetting P).h = P.T + k * P.hgridQ
  rw [toSetting_h P h]

/-! ## The Lemma 6.1 interface

§8 does not name `ZetaQ.multiplicative_large_sieve` directly.  It consumes Lemma 6.1 through
the local `Prop` below and takes it as an EXPLICIT HYPOTHESIS of Lemma 8.1/8.1′ (standing brief:
"an extra hypothesis is auditable; a wrong Mathlib name is a build break").  **§6 has since
landed and the gate is DISCHARGED**: `largeSieveHyp` (immediately below) proves `LargeSieveHyp`
from `ZetaQ.multiplicative_large_sieve` as a bare term, and the interface is kept because it is
what makes every §8 consumer's dependence on §6 visible in its own signature. -/

/-- **Lemma 6.1** (multiplicative large sieve) as a consumed interface, at the GALLAGHER
budget: `Σ_{q ≤ Qn} Σ*_{χ mod q} |Σ_{n ≤ N} a_n χ(n)|² ≤ (Qn² + πN) Σ_{n ≤ N} |a_n|²`.

**Budget.** Until the Gallagher rethread this interface carried the sharp budget `N + Qn² − 1`
(`ZetaQ.sieveBudget`), whose proof rests on `ZetaQ.l2_concentration_exists` (Selberg). It now
carries `Qn² + πN` (`ZetaQ.Gallagher.gallagherBudget`), which is proved outright
(`ZetaQ/Gallagher.lean`). The `Qn²` term — the only one that reaches the family constant — is
identical; §8 uses the length term only through `πX ≤ 10⁻⁴Q²` (`pi_mul_X_le_of_sieve_eff`).

Rule 17: `N` and `Qn` are free and unrelated to `T`.  No λ, no X, no D₀. -/
def LargeSieveHyp : Prop :=
  ∀ (Qn N : ℕ) (a : ℕ → ℂ),
    famSum Qn (fun q χ => ‖∑ n ∈ Finset.Ioc 0 N, a n * χ (n : ZMod q)‖ ^ 2)
      ≤ ((Qn : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2

/-- Lemma 6.1 holds.  **DISCHARGED, sorry-free.**
`ZetaQ.Gallagher.multiplicative_large_sieve_gallagher` proves exactly this proposition —
`charSum`, `gallagherBudget` and `l2sq` delta-reduce to the shapes `LargeSieveHyp` spells out
inline, so the citation typechecks as a bare term with no glue.  Previously this cited the
sharp `ZetaQ.multiplicative_large_sieve`, whose sole sorry root is
`ZetaQ.l2_concentration_exists` (Selberg); the Gallagher route has none.

Paper §6 (Lemma 6.1).
Rule 17: clean (see `LargeSieveHyp`). -/
theorem largeSieve_holds : LargeSieveHyp := ZetaQ.Gallagher.multiplicative_large_sieve_gallagher

/-! ## 1. Lemma 8.1′ and Lemma 8.1 — the family mean square

Paper §8.  Derivation: LEMMA_QE §QE.i.

    **Lemma 8.1 (family mean square).**  B_fam(τ)² := Σ_χ ν_{X,χ}(τ)²
    ≤ c₁²Q²(ℒ + log⁺(|τ|/4T) + C₀)², with explicit absolute (c₁, C₀): the μ-part by digamma
    envelopes; the P-part by Lemma 6.1 at fixed τ (the τ-twist leaves ‖a‖₂ invariant — the
    prime part never touches the log⁺ growth).  **No X-dependence** — the standard
    large-sieve substitution of a family mean value for a pointwise bound [Mo71 Ch. 12;
    IK Ch. 10; Ga67], applied at the (B, ν)-generic seam of [R]'s ends layer, where the
    T-aspect's pointwise B = l + 4√X (the λ ≤ 1 wall) is replaced by B_fam ≍ Qℒ.

`(c₁, C₀) = (0.41, 6)` are `ZetaQ.c1Ends`, `ZetaQ.C0Ends` in the frozen Defs.
`c₁² = 9/π⁶ + λ*²/π² + o(1) ≈ 0.168`; C₀ was raised 5 → 6 at R7 (NOTE_QR §QR.1).

Lemma 8.1 is **not novel mathematics** (LEMMA_QE R4 header: "B_fam itself is the standard
large-sieve substitution … the claim is the seam only"); the fidelity obligation is the
explicit constants. -/

/-! ### 1.0  The four analytic inputs of Lemma 8.1′

Everything in this subsection is machinery for `Bfam_le_sep`.  The four inputs are, in the
order the proof consumes them:

  **(a) Minkowski for the family sum** (`sqrt_famSum_add_sq_le`) — the ℓ²-triangle
      inequality on `𝔉_Q`, which is what makes the split `ν = μ_q + P_{X,χ}` cost `√2`
      *less* than LEMMA_QE §QE.i's `(a+b)² ≤ 2a² + 2b²`;
  **(b) the q-uniform digamma envelope** (`abs_muq_le`) — `|μ_{κ,q}(τ)| ≤ (1/2π)(ℒ + log 4 +
      5 + log⁺)`, uniform in `q ≤ Q` and in `κ ∈ {0,1}`, from
      `Zeta23.ThmE.GammaChi.muq_stirling_const` (the conductor-free Stirling constant
      `20/2π`) above `|τ| = 2` and from `muq_monotoneOn`/`muq_even` below it;
  **(c) the family count** (`famCount_le`) — `Σ_{q≤Qn} φ*(q) ≤ 0.44²Q²`, from §12.2's
      `ZetaQ.Normalisation.N2.Astar_bound` (**decision D26**, module docstring);
  **(d) Chebyshev–Mertens with the sharp main coefficient** (`cheb_sq_div_le`) —
      `Σ_{n≤X} Λ(n)²/n ≤ (log X)²/2 + 12 log X + 12`.

⚠ **(d) is NOT `Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit`, and the reason is
quantitative, not stylistic.**  That theorem is the right *statement*, but its constant is
`C₂ = 2(log 4 + 4) + 1537/log 2 ≈ 2228`, and Lemma 8.1′ charges `C₂/(√2π) ≈ 501` per unit of
`Q` against a constant budget of `c₁C₀ = 2.46`; no `δ` and no `Q₀` repairs a deficit of 500
(the only currency for a constant is the ℒ-coefficient slack, at most `c₁ − c_μ^sharp
= 0.34` per ℒ, so absorbing 500 would need `ℒ ≳ 1500`, i.e. `Q ≳ e^{1500}`).  The
`1537/log 2` is an artefact of the *lower* half of that two-sided statement — it converts
the defect bound `Σ Λ(n)(log n − Λ(n))/n ≤ 1537` into a multiple of `log x` — and the upper
half never needs it.  Its upper half is `private` in `Zeta23/Chebyshev.lean`
(`sum_log_mul_vonMangoldt_div_bound`), so it is re-derived here by discrete partial
summation off `Zeta23.Cheb.mertensFirst` (`|Σ_{n≤x}Λ(n)/n − log x| ≤ log 4 + 4`, the only
Chebyshev input used): `Λ(n)² ≤ Λ(n) log n`, `log n ≤ H_{n−1}`, a Fubini swap, and one
antitone sum-vs-integral comparison.  The delivered constant is `1 + 2(log 4 + 4) = 11.77`.
**If `sum_log_mul_vonMangoldt_div_bound` is ever made public, `cheb_sq_div_le` should be
retired in its favour** (it would improve 12 → 10.78, and nothing else here changes). -/

section AnalyticInputs

/-- The family sum flattened to a single `Finset`; `famSum_eq_sigma` below is the same
statement, kept where §8.2 uses it. -/
private theorem famSum_sigma (Qn : ℕ) (f : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    famSum Qn f
      = ∑ x ∈ (Finset.Icc 1 Qn).sigma (fun q => primitiveChars q), f x.1 x.2 :=
  Finset.sum_sigma' _ _ _

private theorem famSum_mono_all {Qn : ℕ} {f g : (q : ℕ) → DirichletCharacter ℂ q → ℝ}
    (h : ∀ q χ, f q χ ≤ g q χ) : famSum Qn f ≤ famSum Qn g :=
  Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun χ _ => h q χ

private theorem famSum_const_mul (Qn : ℕ) (c : ℝ)
    (f : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    famSum Qn (fun q χ => c * f q χ) = c * famSum Qn f := by
  unfold famSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => (Finset.mul_sum _ _ _).symm

/-! #### (a) Minkowski on `𝔉_Q` -/

/-- **Minkowski for the family sum.**  `√(Σ(a+b)²) ≤ √(Σa²) + √(Σb²)` over `𝔉_Q`, by
Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) on the flattened index.

This is the step that makes the `μ`/`P` split FREE of the `√2` that LEMMA_QE §QE.i's
`(a+b)² ≤ 2a² + 2b²` pays.  Without it the δ-floor of `Bfam_le_sep` would be ≈ 0.95, which
the design of record does not meet (its own `δ → 2 − λ* = 0.7493`).

Rule 17: no hypotheses at all. -/
theorem sqrt_famSum_add_sq_le (Qn : ℕ) (a b : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    Real.sqrt (famSum Qn (fun q χ => (a q χ + b q χ) ^ 2))
      ≤ Real.sqrt (famSum Qn (fun q χ => a q χ ^ 2))
        + Real.sqrt (famSum Qn (fun q χ => b q χ ^ 2)) := by
  set S : Finset ((q : ℕ) × DirichletCharacter ℂ q) :=
    (Finset.Icc 1 Qn).sigma (fun q => primitiveChars q) with hS
  set A : ℝ := ∑ x ∈ S, a x.1 x.2 ^ 2 with hA
  set B : ℝ := ∑ x ∈ S, b x.1 x.2 ^ 2 with hB
  set C : ℝ := ∑ x ∈ S, a x.1 x.2 * b x.1 x.2 with hC
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hCS : C ^ 2 ≤ A * B := Finset.sum_mul_sq_le_sq_mul_sq S _ _
  have hCle : C ≤ Real.sqrt A * Real.sqrt B := by
    have h1 : C ≤ Real.sqrt (A * B) := by
      calc C ≤ |C| := le_abs_self C
        _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
        _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hCS
    rwa [Real.sqrt_mul hA0] at h1
  have hexp : famSum Qn (fun q χ => (a q χ + b q χ) ^ 2) = A + 2 * C + B := by
    rw [famSum_sigma, ← hS, hA, hB, hC]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hsa : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  have hsb : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  have hle : A + 2 * C + B ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by nlinarith [hCle]
  rw [hexp, famSum_sigma, famSum_sigma, ← hS, ← hA, ← hB]
  calc Real.sqrt (A + 2 * C + B) ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt A + Real.sqrt B := by rw [Real.sqrt_sq (by positivity)]

/-! #### (b) the q-uniform digamma envelope -/

/-- `env_μ(τ) := (1/2π)(ℒ + log 4 + 5 + log⁺(|τ|/4T))` — the majorant of `|μ_{κ,q}(τ)|`,
uniform in `q ≤ Q` and in the parity `κ ∈ {0,1}`.  The `5` is the Stirling remainder
`(20/2π)/τ²` at the cut `|τ| = 2`; the `log 4` is the `4T` inside `log⁺`. -/
def muEnvQ (P : ParamsQ) (τ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (P.LL + Real.log 4 + 5 + logPlusQ P τ)

theorem muEnvQ_nonneg (P : ParamsQ) (hLL : 0 < P.LL) (τ : ℝ) : 0 ≤ muEnvQ P τ := by
  have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlp : (0:ℝ) ≤ logPlusQ P τ := le_max_right _ _
  unfold muEnvQ
  have hinv : (0:ℝ) < 1 / (2 * Real.pi) := by positivity
  nlinarith [Real.pi_pos]

/-- Stirling half of the envelope, at the cut `u = max(|τ|, 2)`:
`μ_{κ,q}(τ) ≤ (1/2π)(log(q·u/2π) + 5)`.  Above the cut this is
`Zeta23.ThmE.GammaChi.muq_stirling_const` with `τ² ≥ 4`; below it, evenness (`muq_even`) and
monotonicity on `[0,∞)` (`muq_monotoneOn`) push `τ` up to `2`.

Rule 17: `κ ≤ 1`, `1 ≤ q` only.  No λ, no X, no T. -/
theorem muq_le_log_max (q : ℕ) (hq1 : 1 ≤ q) (κ : ℕ) (hκ : κ ≤ 1) (τ : ℝ) :
    Zeta23.ThmE.muq κ q τ
      ≤ (1 / (2 * Real.pi)) * (Real.log (q * max |τ| 2 / (2 * Real.pi)) + 5) := by
  have hπ := Real.pi_pos
  have key : ∀ σ : ℝ, 2 ≤ |σ| →
      Zeta23.ThmE.muq κ q σ
        ≤ (1 / (2 * Real.pi)) * (Real.log (q * |σ| / (2 * Real.pi)) + 5) := by
    intro σ hσ
    have h := Zeta23.ThmE.GammaChi.muq_stirling_const hκ hq1 σ (by linarith)
    have hσ2 : (4:ℝ) ≤ σ ^ 2 := by rw [← sq_abs]; nlinarith
    have hb : (20 / (2 * Real.pi)) / σ ^ 2 ≤ 5 / (2 * Real.pi) := by
      have h1 : (20 / (2 * Real.pi)) / σ ^ 2 ≤ (20 / (2 * Real.pi)) / 4 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hσ2
      have h2 : (20 / (2 * Real.pi)) / 4 = 5 / (2 * Real.pi) := by ring
      linarith [h2 ▸ h1]
    have h3 := (abs_le.mp h).2
    have hone : (1 / (2 * Real.pi)) * (Real.log (q * |σ| / (2 * Real.pi)) + 5)
        = (1 / (2 * Real.pi)) * Real.log (q * |σ| / (2 * Real.pi))
          + 5 / (2 * Real.pi) := by ring
    rw [hone]
    linarith
  rcases le_or_gt (2:ℝ) |τ| with h | h
  · rw [max_eq_left h]; exact key τ h
  · rw [max_eq_right h.le]
    have heven : Zeta23.ThmE.muq κ q τ = Zeta23.ThmE.muq κ q |τ| := by
      rcases le_or_gt (0:ℝ) τ with h0 | h0
      · rw [abs_of_nonneg h0]
      · rw [abs_of_neg h0, Zeta23.ThmE.GammaChi.muq_even hκ]
    have hmono := Zeta23.ThmE.GammaChi.muq_monotoneOn (κ := κ) (q := q) hκ
      (Set.mem_Ici.mpr (abs_nonneg τ)) (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 2)) h.le
    have h2 := key 2 (by norm_num)
    rw [heven]
    refine hmono.trans ?_
    rw [show |(2:ℝ)| = 2 by norm_num] at h2
    exact h2

/-- Conductor/`log⁺` bookkeeping: `log(q·max(|τ|,2)/2π) ≤ ℒ + log 4 + log⁺(|τ|/4T)` for
`q ≤ Q`.  Two cases, split at `|τ| = 4T`; the `log 4` is exactly the `4` in `log⁺`'s
argument, and `2 ≤ 4T` is what lets the cut `max(·,2)` hide inside the first case.

Rule 17: `T ≥ 300`, `Q ≥ 3`, `q ≤ Q`.  No λ, no X. -/
theorem log_max_le (P : ParamsQ) (hT : 300 ≤ P.T) (hQ : 3 ≤ P.Q) (q : ℕ) (hq1 : 1 ≤ q)
    (hqQ : (q:ℝ) ≤ P.Q) (τ : ℝ) :
    Real.log (q * max |τ| 2 / (2 * Real.pi)) ≤ P.LL + Real.log 4 + logPlusQ P τ := by
  have hπ := Real.pi_pos
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hu2 : (2:ℝ) ≤ max |τ| 2 := le_max_right _ _
  have hT0 : (0:ℝ) < P.T := by linarith
  have hQT : (0:ℝ) < P.Q * P.T / (2 * Real.pi) := by positivity
  have hlp0 : (0:ℝ) ≤ logPlusQ P τ := le_max_right _ _
  have hLLdef : P.LL = Real.log (P.Q * P.T / (2 * Real.pi)) := rfl
  rcases le_or_gt |τ| (4 * P.T) with hc | hc
  · have hle : (q:ℝ) * max |τ| 2 / (2 * Real.pi) ≤ 4 * (P.Q * P.T / (2 * Real.pi)) := by
      have humax : max |τ| 2 ≤ 4 * P.T := max_le hc (by linarith)
      rw [div_le_iff₀ (by positivity)]
      calc (q:ℝ) * max |τ| 2 ≤ P.Q * (4 * P.T) :=
            mul_le_mul hqQ humax (by linarith) (by linarith)
        _ = 4 * (P.Q * P.T / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
    have h2 := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) (ne_of_gt hQT), ← hLLdef] at h2
    linarith
  · have hτ2 : max |τ| 2 = |τ| := max_eq_left (by linarith)
    have hr : (1:ℝ) < |τ| / (4 * P.T) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    have hlp : logPlusQ P τ = Real.log (|τ| / (4 * P.T)) := by
      unfold logPlusQ
      exact max_eq_left (Real.log_nonneg hr.le)
    have hle : (q:ℝ) * |τ| / (2 * Real.pi)
        ≤ 4 * (P.Q * P.T / (2 * Real.pi)) * (|τ| / (4 * P.T)) := by
      have heq : 4 * (P.Q * P.T / (2 * Real.pi)) * (|τ| / (4 * P.T))
          = P.Q * |τ| / (2 * Real.pi) := by field_simp
      rw [heq]
      gcongr
    rw [hτ2]
    have hτpos : (0:ℝ) < |τ| := by linarith
    have harg : (0:ℝ) < (q:ℝ) * |τ| / (2 * Real.pi) :=
      div_pos (mul_pos (by linarith) hτpos) (by positivity)
    have h2 := Real.log_le_log harg hle
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (ne_of_gt hQT), ← hLLdef, ← hlp] at h2
    linarith

/-- **(b) THE q-UNIFORM DIGAMMA ENVELOPE** — the first of the two blockers recorded at
`Bfam_le_sep` by earlier passes.  `|μ_{κ,q}(τ)| ≤ env_μ(τ)`, uniformly in `q ≤ Q` and in
`κ ∈ {0,1}`.  The lower half is `μ_{κ,q}(τ) ≥ μ_{κ,q}(0) > −1` (`muq_zero_le`,
`neg_one_lt_muq_zero`) against `env_μ ≥ 1`.

Paper §8; LEMMA_QE §QE.i.
Depends on: `Zeta23.ThmE.GammaChi.{muq_stirling_const, muq_monotoneOn, muq_even,
muq_zero_le, neg_one_lt_muq_zero}`.
Rule 17: `T ≥ 300`, `Q ≥ 3`, `0 < ℒ`, `q ≤ Q`, `κ ≤ 1`.  No λ, no X, no D₀. -/
theorem abs_muq_le (P : ParamsQ) (hT : 300 ≤ P.T) (hQ : 3 ≤ P.Q) (hLL : 0 < P.LL)
    (q : ℕ) (hq1 : 1 ≤ q) (hqQ : (q:ℝ) ≤ P.Q) (κ : ℕ) (hκ : κ ≤ 1) (τ : ℝ) :
    |Zeta23.ThmE.muq κ q τ| ≤ muEnvQ P τ := by
  have hπ := Real.pi_pos
  have hπ' : Real.pi < 3.1416 := Real.pi_lt_d4
  have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlp0 : (0:ℝ) ≤ logPlusQ P τ := le_max_right _ _
  have hinv : (0:ℝ) < 1 / (2 * Real.pi) := by positivity
  have hup : Zeta23.ThmE.muq κ q τ ≤ muEnvQ P τ := by
    refine (muq_le_log_max q hq1 κ hκ τ).trans ?_
    unfold muEnvQ
    have h := log_max_le P hT hQ q hq1 hqQ τ
    exact mul_le_mul_of_nonneg_left (by linarith) hinv.le
  have hone : (1:ℝ) ≤ muEnvQ P τ := by
    unfold muEnvQ
    have hkey : 2 * Real.pi ≤ P.LL + Real.log 4 + 5 + logPlusQ P τ := by
      rw [hlog4]; linarith
    calc (1:ℝ) = (1 / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
      _ ≤ (1 / (2 * Real.pi)) * (P.LL + Real.log 4 + 5 + logPlusQ P τ) :=
          mul_le_mul_of_nonneg_left hkey hinv.le
  have hlow : Zeta23.ThmE.muq κ q 0 ≤ Zeta23.ThmE.muq κ q τ :=
    Zeta23.ThmE.GammaChi.muq_zero_le hκ τ
  have hz := Zeta23.ThmE.GammaChi.neg_one_lt_muq_zero hκ hq1
  rw [abs_le]
  exact ⟨by linarith, hup⟩

/-- `κ(χ) ∈ {0,1}`, hence `κ(χ) ≤ 1` — the hypothesis every `GammaChi` lemma carries. -/
theorem parity_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) : parity χ ≤ 1 := by
  unfold parity
  split_ifs <;> norm_num

/-! #### (c) the family count — **D26**: `ZetaQ.Normalisation.N2.Astar_bound` -/

theorem pi_four_gt : (97.408:ℝ) < Real.pi ^ 4 := by
  have h1 : (3.141592:ℝ) < Real.pi := Real.pi_gt_d6
  have h2 : (9.86959:ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_pos]
  nlinarith [h2, Real.pi_pos]

theorem eighteen_div_pi_four_le : 18 / Real.pi ^ 4 ≤ 0.1848 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [pi_four_gt]

/-- `(1 + log x)² ≤ 16√x` for `x ≥ 1` — the rpow-free way to absorb `Astar_bound`'s error
term `5N(1 + log N)²` into `ε·N²`. -/
theorem one_add_log_sq_le (x : ℝ) (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  set t : ℝ := Real.sqrt (Real.sqrt x) with ht
  have hsx0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have ht1 : (1:ℝ) ≤ t := by
    rw [ht]
    have h1 : (1:ℝ) ≤ Real.sqrt x := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hx
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h1
  have htsq : t ^ 2 = Real.sqrt x := Real.sq_sqrt hsx0
  have hlogt : Real.log t = Real.log x / 4 := by
    rw [ht, Real.log_sqrt hsx0, Real.log_sqrt hx0]; ring
  have hlt := Real.log_le_sub_one_of_pos (show (0:ℝ) < t by linarith)
  have hlogx : Real.log x ≤ 4 * t - 4 := by rw [hlogt] at hlt; linarith
  have hlog0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx
  nlinarith [ht1, hlogx, hlog0, htsq]

/-- The family count IS §12.2's object: `Σ_{q≤Qn} Σ*_{χ mod q} 1 = Σ_{q≤Qn} φ*(q)`. -/
theorem famSum_one_eq_Astar (Qn : ℕ) :
    famSum Qn (fun _ _ => (1:ℝ)) = ZetaQ.Normalisation.N2.Astar Qn := by
  unfold famSum ZetaQ.Normalisation.N2.Astar
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [phiStar]

/-- **(c) THE FAMILY COUNT** — the second blocker recorded at `Bfam_le_sep` by earlier
passes, now discharged from §12.2 (**decision D26**, see the module docstring):
`Σ_{q≤Qn} φ*(q) ≤ 0.44²·Q²` for `Qn ≤ Q`, `Q ≥ 10⁹`.

`N2.Astar_bound` gives `|Σ_{q≤N} φ*(q) − (18/π⁴)N²| ≤ 5N(1 + log N)²`, i.e. the SHARP
constant `18/π⁴ = 0.18477`; the numeral `0.44² = 0.1936` is that (bounded by `0.1848`) plus
room for the error term, charged as `80/√Q ≤ 0.0025` at `Q ≥ 10⁹` via `one_add_log_sq_le`.

**This is where `Bfam_le_sep`'s `Q ≥ 10⁹` comes from, and it is the only place.**  No
`∀ Q ≥ 3` bound can reach `0.1936`: on any route that avoids the Möbius main term — e.g.
`φ*(q) ≤ φ(q) ≤ q − 1`, giving `A*(N) ≤ 1 + N(N−1)/2` — one gets
`√(A*(N))/N → 1/√2 = 0.707`, and the `log⁺` coefficient `c_μ = 3/π³` allows at most
`6/π² = 0.608`.  `A*(3) = 3` against `0.1936·9 = 1.74` shows the small-`Q` failure is real
and not an artefact of the error term.

Paper §12.2; `ZetaQ.Normalisation.N2.Astar_bound`.
Rule 17: λ-free, X-free, T-free, D₀-free — a statement about conductors only. -/
theorem famCount_le (Qn : ℕ) (Q : ℝ) (hQn : (Qn:ℝ) ≤ Q) (hQ : (1000000000:ℝ) ≤ Q) :
    famSum Qn (fun _ _ => (1:ℝ)) ≤ 0.1936 * Q ^ 2 := by
  have hQ0 : (0:ℝ) < Q := by linarith
  have hsq : (31622:ℝ) ≤ Real.sqrt Q := by
    rw [show (31622:ℝ) = Real.sqrt (31622 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsq2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ0.le
  have hstep : 80 * (Q * Real.sqrt Q) ≤ 0.0088 * Q ^ 2 := by
    nlinarith [hsq, hsq2, hQ0]
  have hpi := eighteen_div_pi_four_le
  rcases Nat.eq_zero_or_pos Qn with h0 | h1
  · subst h0
    unfold famSum
    simp
    positivity
  · have hQn1 : (1:ℝ) ≤ (Qn:ℝ) := by exact_mod_cast h1
    have hAb := abs_le.mp (ZetaQ.Normalisation.N2.Astar_bound Qn h1)
    rw [famSum_one_eq_Astar]
    have hlogQn : Real.log Qn ≤ Real.log Q := Real.log_le_log (by linarith) hQn
    have hlog0 : (0:ℝ) ≤ Real.log Qn := Real.log_nonneg hQn1
    have hmon : (Qn:ℝ) * (1 + Real.log Qn) ^ 2 ≤ Q * (1 + Real.log Q) ^ 2 := by
      have h1' : (1 + Real.log Qn) ^ 2 ≤ (1 + Real.log Q) ^ 2 := by nlinarith
      nlinarith [hQn1, hQn]
    have hbig := one_add_log_sq_le Q (by linarith)
    have hQnsq : (Qn:ℝ) ^ 2 ≤ Q ^ 2 := by nlinarith
    have h18 : 18 / Real.pi ^ 4 * (Qn:ℝ) ^ 2 ≤ 0.1848 * Q ^ 2 := by
      have h0' : (0:ℝ) ≤ 18 / Real.pi ^ 4 := by positivity
      nlinarith [hQnsq, hpi, sq_nonneg ((Qn:ℝ))]
    have herr : 5 * (Qn:ℝ) * (1 + Real.log Qn) ^ 2 ≤ 0.0088 * Q ^ 2 := by
      have hm : 5 * (Qn:ℝ) * (1 + Real.log Qn) ^ 2 ≤ 5 * (Q * (1 + Real.log Q) ^ 2) := by
        nlinarith [hmon]
      nlinarith [hm, hbig, hstep, hQ0, Real.sqrt_nonneg Q]
    linarith [hAb.2]

/-! #### (d) Chebyshev–Mertens with the sharp main coefficient -/

/-- `log n ≤ Σ_{m<n} 1/m`, by telescoping `log(1 + 1/m) ≤ 1/m`. -/
theorem log_le_harmonic (n : ℕ) :
    Real.log n ≤ ∑ m ∈ Finset.Ico 1 n, ((m : ℝ))⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [Finset.sum_Ico_succ_top hk]
      have hk0 : (0:ℝ) < k := by exact_mod_cast hk
      have hstep : Real.log (k+1) - Real.log k ≤ ((k:ℝ))⁻¹ := by
        have h1 : Real.log ((k:ℝ)+1) - Real.log k = Real.log (((k:ℝ)+1)/k) := by
          rw [Real.log_div (by positivity) (by positivity)]
        rw [h1]
        have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((k:ℝ)+1)/k by positivity)
        have he : ((k:ℝ)+1)/k - 1 = ((k:ℝ))⁻¹ := by field_simp; ring
        linarith [he ▸ h2]
      push_cast
      linarith

/-- `Σ_{m<N} 1/m ≤ 1 + log N` (Mathlib's `harmonic_le_one_add_log`, via §12.2's wrapper). -/
theorem harmonic_Ico_le (N : ℕ) :
    ∑ m ∈ Finset.Ico 1 N, ((m : ℝ))⁻¹ ≤ 1 + Real.log N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have h1 : Finset.Ico 1 N ⊆ Finset.Icc 1 N := by
      intro x hx; simp only [Finset.mem_Ico] at hx; simp only [Finset.mem_Icc]; omega
    have h2 : ∑ m ∈ Finset.Ico 1 N, ((m : ℝ))⁻¹ ≤ ∑ m ∈ Finset.Icc 1 N, ((m : ℝ))⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg h1 (fun i _ _ => by positivity)
    exact h2.trans (ZetaQ.Normalisation.N2.harmonic_bound N)

/-- `∫_1^N (log N − log t)/t dt = (log N)²/2`; the antiderivative is
`log N·log t − (log t)²/2`. -/
theorem integral_logratio (N : ℕ) (hN : 1 ≤ N) :
    (∫ t in (1:ℝ)..(N:ℝ), (Real.log N - Real.log t)/t) = Real.log N ^ 2 / 2 := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  set F : ℝ → ℝ := fun t => Real.log N * Real.log t - Real.log t ^ 2 / 2 with hF
  have hderiv : ∀ t ∈ Set.uIcc (1:ℝ) (N:ℝ),
      HasDerivAt F ((Real.log N - Real.log t)/t) t := by
    intro t ht
    rw [Set.uIcc_of_le hN1] at ht
    have ht0 : t ≠ 0 := by have h := ht.1; intro h'; rw [h'] at h; linarith
    have hl : HasDerivAt Real.log (1/t) t := by
      simpa [one_div] using Real.hasDerivAt_log ht0
    have h1 : HasDerivAt (fun t => Real.log N * Real.log t) (Real.log N * (1/t)) t :=
      hl.const_mul _
    have h2 : HasDerivAt (fun t => Real.log t ^ 2 / 2) (Real.log t * (1/t)) t := by
      have h3 := (hl.pow 2).div_const 2
      simpa using h3.congr_deriv (by ring)
    have h4 := h1.sub h2
    refine h4.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun t => (Real.log N - Real.log t)/t) volume 1 (N:ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hN1]
    apply ContinuousOn.div
    · exact continuousOn_const.sub (Real.continuousOn_log.mono (by
        intro x hx; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h := hx.1; intro h'; rw [h'] at h; linarith))
    · exact continuousOn_id
    · intro x hx; have h := hx.1; intro h'; rw [h'] at h; linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, hF]
  simp
  ring

/-- `Σ_{m<N} log(N/m)/m ≤ log N + (log N)²/2` — one antitone sum-vs-integral comparison
(`AntitoneOn.sum_le_integral_Ico`).  The integrand is a product of two nonnegative antitone
factors on `[1,N]`, so no derivative computation is needed for the monotonicity. -/
theorem sum_logratio_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Ico 1 N, (Real.log N - Real.log m)/(m:ℝ)
      ≤ Real.log N + Real.log N ^ 2 / 2 := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  set f : ℝ → ℝ := fun t => (Real.log N - Real.log t)/t with hf
  have hanti : AntitoneOn f (Set.Icc (1:ℝ) (N:ℝ)) := by
    intro x hx y hy hxy
    have hx1 : (1:ℝ) ≤ x := hx.1
    have hyN : y ≤ (N:ℝ) := hy.2
    have hy1 : (1:ℝ) ≤ y := hy.1
    have hlx : Real.log y ≤ Real.log N := Real.log_le_log (by linarith) hyN
    have hxy' : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
    simp only [hf]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [Real.log_nonneg hx1, Real.log_nonneg hy1]
  have hanti' : AntitoneOn f (Set.Icc ((1:ℕ):ℝ) ((N:ℕ):ℝ)) := by simpa using hanti
  have hkey := AntitoneOn.sum_le_integral_Ico (f := f) (a := 1) (b := N) hN hanti'
  simp only [Nat.cast_one] at hkey
  rw [integral_logratio N hN] at hkey
  have hshift : ∑ i ∈ Finset.Ico 1 N, f ((i+1 : ℕ) : ℝ)
      = ∑ m ∈ Finset.Ico 2 (N+1), f ((m : ℕ) : ℝ) := by
    have h := Finset.sum_Ico_add' (fun m : ℕ => f ((m : ℕ) : ℝ)) 1 N 1
    simpa using h
  have hsplit : ∑ m ∈ Finset.Ico 1 (N+1), f ((m : ℕ) : ℝ)
      = f ((1:ℕ) : ℝ) + ∑ m ∈ Finset.Ico 2 (N+1), f ((m : ℕ) : ℝ) :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  have htop : ∑ m ∈ Finset.Ico 1 (N+1), f ((m : ℕ) : ℝ)
      = (∑ m ∈ Finset.Ico 1 N, f ((m : ℕ) : ℝ)) + f ((N : ℕ) : ℝ) :=
    Finset.sum_Ico_succ_top hN _
  have hfN : f ((N : ℕ) : ℝ) = 0 := by simp only [hf]; ring_nf
  have hf1 : f ((1:ℕ) : ℝ) = Real.log N := by simp only [hf]; norm_num
  rw [hshift] at hkey
  rw [htop, hf1] at hsplit
  simp only [hfN, add_zero] at hsplit
  simp only [hf] at hsplit hkey ⊢
  linarith

/-- **(d) CHEBYSHEV–MERTENS, upper bound with the SHARP main coefficient `1/2` and a small
explicit constant**: `Σ_{n≤X} Λ(n)²/n ≤ (log X)²/2 + 12·log X + 12`.

Route: `Λ(n)² ≤ Λ(n) log n`, `log n ≤ H_{n−1}`, a Fubini swap, then
`Zeta23.Cheb.mertensFirst` at every integer point, giving
`Σ ≤ Σ_{m<N}(1/m)(log(N/m) + 2(log 4 + 4))`, closed by `sum_logratio_le` and
`harmonic_Ico_le`.  The delivered constant is `1 + 2(log 4 + 4) = 11.77 ≤ 12`.

⚠ **`Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit` cannot be used in its place** — see the
subsection header: its `1537/log 2` costs ≈ 501 per unit of `Q` against a budget of 2.46.

Paper [lem:cheb] / [eq:cheb2].1, upper half only.
Rule 17: `1 ≤ X` only; no λ, no T, no D₀. -/
theorem cheb_sq_div_le (X : ℝ) (hX : 1 ≤ X) :
    ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n ^ 2 / n
      ≤ Real.log X ^ 2 / 2 + 12 * Real.log X + 12 := by
  set N : ℕ := ⌊X⌋₊ with hNdef
  have hN : 1 ≤ N := (Nat.one_le_floor_iff X).mpr hX
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hLN0 : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNR
  have hNX : (N:ℝ) ≤ X := Nat.floor_le (by linarith)
  have hLNX : Real.log N ≤ Real.log X := Real.log_le_log (by linarith) hNX
  set c : ℝ := Real.log 4 + 4 with hc
  set M : ℕ → ℝ := fun k => ∑ n ∈ Finset.Ioc 0 k, Λ n / n with hM
  have hmert : ∀ k : ℕ, 1 ≤ k → |M k - Real.log k| ≤ c := by
    intro k hk
    have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h := Zeta23.Cheb.mertensFirst hkR
    rwa [Nat.floor_natCast] at h
  have hA : ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 / n
      ≤ ∑ n ∈ Finset.Ioc 0 N, ∑ m ∈ Finset.Ico 1 n, (Λ n / n) * ((m:ℝ))⁻¹ := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hΛ0 : (0:ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hdiv : (0:ℝ) ≤ Λ n / n := by positivity
    rw [← Finset.mul_sum]
    have h1 : Λ n ^ 2 / n = (Λ n / n) * Λ n := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left
      ((ArithmeticFunction.vonMangoldt_le_log).trans (log_le_harmonic n)) hdiv
  have hswap : ∑ n ∈ Finset.Ioc 0 N, ∑ m ∈ Finset.Ico 1 n, (Λ n / n) * ((m:ℝ))⁻¹
      = ∑ m ∈ Finset.Ico 1 N, ∑ n ∈ Finset.Ioc m N, (Λ n / n) * ((m:ℝ))⁻¹ := by
    apply Finset.sum_comm'
    intro n m
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hinner : ∀ m ∈ Finset.Ico 1 N,
      ∑ n ∈ Finset.Ioc m N, (Λ n / n) * ((m:ℝ))⁻¹
        ≤ ((Real.log N - Real.log m) + 2 * c) * ((m:ℝ))⁻¹ := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    have hm1 : 1 ≤ m := hm.1
    have hmN : m ≤ N := le_of_lt hm.2
    have hsplit : M m + ∑ n ∈ Finset.Ioc m N, Λ n / n = M N := by
      simp only [hM]
      exact Finset.sum_Ioc_consecutive _ (Nat.zero_le m) hmN
    have h1 := abs_le.mp (hmert N hN)
    have h2 := abs_le.mp (hmert m hm1)
    rw [← Finset.sum_mul]
    have hminv : (0:ℝ) ≤ ((m:ℝ))⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hminv
    linarith [hsplit, h1.2, h2.1]
  have hF : ∑ m ∈ Finset.Ico 1 N, ((Real.log N - Real.log m) + 2 * c) * ((m:ℝ))⁻¹
      ≤ (Real.log N + Real.log N ^ 2 / 2) + 2 * c * (1 + Real.log N) := by
    have hexp : ∀ m ∈ Finset.Ico 1 N,
        ((Real.log N - Real.log m) + 2 * c) * ((m:ℝ))⁻¹
          = (Real.log N - Real.log m)/(m:ℝ) + 2 * c * ((m:ℝ))⁻¹ := by
      intro m _; field_simp
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hc0 : (0:ℝ) ≤ 2 * c := by
      have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      simp only [hc]; linarith
    have h1 := sum_logratio_le N hN
    have h2 := harmonic_Ico_le N
    nlinarith [h1, h2, hc0]
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hc12 : 2 * c ≤ 12 := by simp only [hc, hlog4]; linarith
  have hc12' : 1 + 2 * c ≤ 12 := by simp only [hc, hlog4]; linarith
  have hsq : Real.log N ^ 2 ≤ Real.log X ^ 2 := by nlinarith
  calc ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 / n
      ≤ ∑ m ∈ Finset.Ico 1 N, ((Real.log N - Real.log m) + 2 * c) * ((m:ℝ))⁻¹ := by
        refine hA.trans ?_
        rw [hswap]
        exact Finset.sum_le_sum hinner
    _ ≤ (Real.log N + Real.log N ^ 2 / 2) + 2 * c * (1 + Real.log N) := hF
    _ ≤ Real.log X ^ 2 / 2 + 12 * Real.log X + 12 := by
        nlinarith [hLN0, hLNX, hsq, hc12, hc12']

/-! #### The two halves of `B_fam`, and the remaining numeric inputs -/

/-- **The μ-part of Lemma 8.1′**: `√(Σ_χ μ_q(τ)²) ≤ 0.44·Q·env_μ(τ)` — (b) pointwise, then
(c) for the cardinality.  Note the `0.44` is `√(0.1936)`, i.e. `√(18/π⁴)` with the
count's error term folded in. -/
theorem sqrt_famSum_muq_le (P : ParamsQ) (hT : 300 ≤ P.T) (hQ3 : 3 ≤ P.Q) (hLL : 0 < P.LL)
    (Qn : ℕ) (hQn : (Qn:ℝ) ≤ P.Q) (hQ0 : (1000000000:ℝ) ≤ P.Q) (τ : ℝ) :
    Real.sqrt (famSum Qn (fun q χ => Zeta23.ThmE.muq (parity χ) q τ ^ 2))
      ≤ 0.44 * P.Q * muEnvQ P τ := by
  have hE0 : 0 ≤ muEnvQ P τ := muEnvQ_nonneg P hLL τ
  have hQpos : (0:ℝ) < P.Q := by linarith
  have hbd : famSum Qn (fun q χ => Zeta23.ThmE.muq (parity χ) q τ ^ 2)
      ≤ muEnvQ P τ ^ 2 * (0.1936 * P.Q ^ 2) := by
    have hstep : famSum Qn (fun q χ => Zeta23.ThmE.muq (parity χ) q τ ^ 2)
        ≤ famSum Qn (fun q _ => muEnvQ P τ ^ 2 * (1:ℝ)) := by
      unfold famSum
      refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ _ => ?_
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hqQn : q ≤ Qn := (Finset.mem_Icc.mp hq).2
      have hqQ : (q:ℝ) ≤ P.Q := le_trans (by exact_mod_cast hqQn) hQn
      have habs := abs_muq_le P hT hQ3 hLL q hq1 hqQ (parity χ) (parity_le_one χ) τ
      show Zeta23.ThmE.muq (parity χ) q τ ^ 2 ≤ muEnvQ P τ ^ 2 * 1
      rw [mul_one]
      calc Zeta23.ThmE.muq (parity χ) q τ ^ 2
          = |Zeta23.ThmE.muq (parity χ) q τ| ^ 2 := (sq_abs _).symm
        _ ≤ muEnvQ P τ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine hstep.trans ?_
    rw [famSum_const_mul]
    exact mul_le_mul_of_nonneg_left (famCount_le Qn P.Q hQn hQ0) (by positivity)
  refine (Real.sqrt_le_sqrt hbd).trans ?_
  have heq : muEnvQ P τ ^ 2 * (0.1936 * P.Q ^ 2) = (0.44 * P.Q * muEnvQ P τ) ^ 2 := by ring
  rw [heq, Real.sqrt_sq (by positivity)]

/-- the coefficient vector Lemma 6.1 is applied to, at the τ-twist: `a_n = Λ(n)n^{−1/2−iτ}`.
`‖a_n‖² = Λ(n)²/n` is τ-INDEPENDENT — which is exactly why the prime part contributes
nothing to the `log⁺` growth, i.e. why the separated form 8.1′ exists at all. -/
def sieveCoeff (τ : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(1/2 : ℂ) - Complex.I * τ)

theorem norm_sieveCoeff_sq {n : ℕ} (hn : 0 < n) (τ : ℝ) :
    ‖sieveCoeff τ n‖ ^ 2 = (ArithmeticFunction.vonMangoldt n) ^ 2 / n := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hΛ : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hre : (-(1/2 : ℂ) - Complex.I * τ).re = -(1/2 : ℝ) := by simp
  unfold sieveCoeff
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn, hre, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hΛ, mul_pow]
  have hr : ((n:ℝ) ^ (-(1/2 : ℝ))) ^ 2 = 1 / (n:ℝ) := by
    rw [← Real.rpow_natCast ((n:ℝ) ^ (-(1/2 : ℝ))) 2, ← Real.rpow_mul hn0.le]
    norm_num [Real.rpow_neg_one]
  rw [hr]
  ring

/-- **The P-part of Lemma 8.1′** — Lemma 6.1 consumed at FIXED `τ`, exactly as paper §8
prescribes ("the P-part by Lemma 6.1 at fixed τ").  `|Re z| ≤ ‖z‖` is the only loss. -/
theorem sqrt_famSum_PXc_le (Qn : ℕ) (X τ : ℝ) (hsieve : LargeSieveHyp) :
    Real.sqrt (famSum Qn
        (fun q χ => Zeta23.ThmE.PXc (fun n => χ (n : ZMod q)) X τ ^ 2))
      ≤ (1 / Real.pi) * Real.sqrt (((Qn : ℝ) ^ 2 + Real.pi * (⌊X⌋₊ : ℝ))
          * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n ^ 2 / n) := by
  have hπ := Real.pi_pos
  set N : ℕ := ⌊X⌋₊ with hN
  set W : ℝ := ((Qn : ℝ) ^ 2 + Real.pi * (N : ℝ))
      * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 / n with hW
  have hcoeffsum : ∑ n ∈ Finset.Ioc 0 N, ‖sieveCoeff τ n‖ ^ 2
      = ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 / n :=
    Finset.sum_congr rfl fun n hn => norm_sieveCoeff_sq (Finset.mem_Ioc.mp hn).1 τ
  have hsv := hsieve Qn N (sieveCoeff τ)
  rw [hcoeffsum] at hsv
  have hptw : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      Zeta23.ThmE.PXc (fun n => χ (n : ZMod q)) X τ ^ 2
        ≤ (1 / Real.pi ^ 2)
            * ‖∑ n ∈ Finset.Ioc 0 N, sieveCoeff τ n * χ (n : ZMod q)‖ ^ 2 := by
    intro q χ
    have hZ : (∑ n ∈ Finset.Ioc 0 N,
          ((Λ n : ℝ) : ℂ) * (χ (n : ZMod q))
            * (n : ℂ) ^ (-(1/2 : ℂ) - Complex.I * τ))
        = ∑ n ∈ Finset.Ioc 0 N, sieveCoeff τ n * χ (n : ZMod q) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      unfold sieveCoeff
      ring
    have hre : Zeta23.ThmE.PXc (fun n => χ (n : ZMod q)) X τ
        = -(1 / Real.pi)
            * (∑ n ∈ Finset.Ioc 0 N, sieveCoeff τ n * χ (n : ZMod q)).re := by
      unfold Zeta23.ThmE.PXc
      rw [← hZ]
    rw [hre]
    have habs := Complex.abs_re_le_norm
      (∑ n ∈ Finset.Ioc 0 N, sieveCoeff τ n * χ (n : ZMod q))
    have hsq : (∑ n ∈ Finset.Ioc 0 N, sieveCoeff τ n * χ (n : ZMod q)).re ^ 2
        ≤ ‖∑ n ∈ Finset.Ioc 0 N, sieveCoeff τ n * χ (n : ZMod q)‖ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hp2 : (0:ℝ) < 1 / Real.pi ^ 2 := by positivity
    have hexp : (-(1 / Real.pi)
        * (∑ n ∈ Finset.Ioc 0 N, sieveCoeff τ n * χ (n : ZMod q)).re) ^ 2
        = (1 / Real.pi ^ 2)
          * (∑ n ∈ Finset.Ioc 0 N, sieveCoeff τ n * χ (n : ZMod q)).re ^ 2 := by
      field_simp
    rw [hexp]
    exact mul_le_mul_of_nonneg_left hsq hp2.le
  have hmain : famSum Qn
      (fun q χ => Zeta23.ThmE.PXc (fun n => χ (n : ZMod q)) X τ ^ 2)
      ≤ (1 / Real.pi ^ 2) * W := by
    refine (famSum_mono_all hptw).trans ?_
    rw [famSum_const_mul]
    exact mul_le_mul_of_nonneg_left hsv (by positivity)
  refine (Real.sqrt_le_sqrt hmain).trans ?_
  rw [Real.sqrt_mul (by positivity), show (1:ℝ) / Real.pi ^ 2 = (1 / Real.pi) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- `X ≤ 10⁻⁴Q²` from the sieve-efficiency condition `X ≤ Q^{2−δ}` at `δ ≥ 1/2`, `Q ≥ 10⁹`.
**This is the only place `hδ` is consumed**; `δ` never touches the `log⁺` coefficient. -/
theorem X_le_of_sieve_eff (Q X δ : ℝ) (hQ0 : (1000000000:ℝ) ≤ Q) (hδ : 1/2 ≤ δ)
    (hX : X ≤ Real.rpow Q (2 - δ)) : X ≤ 0.0001 * Q ^ 2 := by
  have hQpos : (0:ℝ) < Q := by linarith
  have hsq : (31622:ℝ) ≤ Real.sqrt Q := by
    rw [show (31622:ℝ) = Real.sqrt (31622 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsq2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQpos.le
  have hstep : Real.rpow Q (2 - δ) ≤ Real.rpow Q (3/2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hval : Real.rpow Q (3/2) = Q * Real.sqrt Q := by
    show (Q ^ ((3:ℝ)/2) : ℝ) = Q * Real.sqrt Q
    rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hQpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hfin : Q * Real.sqrt Q ≤ 0.0001 * Q ^ 2 := by
    nlinarith [hsq, hsq2, Real.sqrt_nonneg Q]
  rw [hval] at hstep
  linarith

/-- `πX ≤ 10⁻⁴Q²` from the sieve-efficiency condition `X ≤ Q^{2−δ}` at `δ ≥ 1/2`, `Q ≥ 10⁹` —
the form the GALLAGHER budget `Qn² + πX` needs (`X_le_of_sieve_eff` above is the form the sharp
budget `X + Qn² − 1` needed; it is kept, no longer consumed).  `X ≤ Q^{3/2}` and `√Q ≥ 31622`
give `πX ≤ (π/31622)Q²`, and `π < 3.15` (`Real.pi_lt_d2`) gives `3.15/31622 = 9.961·10⁻⁵ <
10⁻⁴`: margin 0.4 %, at the same `hQ0` as before. -/
theorem pi_mul_X_le_of_sieve_eff (Q X δ : ℝ) (hQ0 : (1000000000:ℝ) ≤ Q) (hδ : 1/2 ≤ δ)
    (hX : X ≤ Real.rpow Q (2 - δ)) : Real.pi * X ≤ 0.0001 * Q ^ 2 := by
  have hQpos : (0:ℝ) < Q := by linarith
  have hsq : (31622:ℝ) ≤ Real.sqrt Q := by
    rw [show (31622:ℝ) = Real.sqrt (31622 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsq2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQpos.le
  have hstep : Real.rpow Q (2 - δ) ≤ Real.rpow Q (3/2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hval : Real.rpow Q (3/2) = Q * Real.sqrt Q := by
    show (Q ^ ((3:ℝ)/2) : ℝ) = Q * Real.sqrt Q
    rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hQpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hval] at hstep
  have hA : 0 ≤ Q * Real.sqrt Q := by positivity
  have hB : (3.15:ℝ) ≤ 0.0001 * Real.sqrt Q := by linarith
  have h1 : Real.pi * X ≤ Real.pi * (Q * Real.sqrt Q) :=
    mul_le_mul_of_nonneg_left (hX.trans hstep) Real.pi_pos.le
  have h2 : Real.pi * (Q * Real.sqrt Q) ≤ 3.15 * (Q * Real.sqrt Q) :=
    mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hA
  have h3 : 3.15 * (Q * Real.sqrt Q) ≤ (0.0001 * Real.sqrt Q) * (Q * Real.sqrt Q) :=
    mul_le_mul_of_nonneg_right hB hA
  have h4 : (0.0001 * Real.sqrt Q) * (Q * Real.sqrt Q) = 0.0001 * Q ^ 2 := by
    have e : (0.0001 * Real.sqrt Q) * (Q * Real.sqrt Q) = 0.0001 * Q * Real.sqrt Q ^ 2 := by ring
    rw [e, hsq2]; ring
  linarith

/-- `√(Y²/2 + 12Y + 12) ≤ 0.7072Y + 8.5` — the sharp `1/√2 = 0.70710…` on the leading term,
which is exactly what (d)'s coefficient `1/2` buys. -/
theorem sqrt_cheb_le (Y : ℝ) (hY : 0 ≤ Y) :
    Real.sqrt (Y ^ 2 / 2 + 12 * Y + 12) ≤ 0.7072 * Y + 8.5 := by
  have hb : Y ^ 2 / 2 + 12 * Y + 12 ≤ (0.7072 * Y + 8.5) ^ 2 := by nlinarith [sq_nonneg Y]
  calc Real.sqrt (Y ^ 2 / 2 + 12 * Y + 12) ≤ Real.sqrt ((0.7072 * Y + 8.5) ^ 2) :=
        Real.sqrt_le_sqrt hb
    _ = 0.7072 * Y + 8.5 := Real.sqrt_sq (by linarith)

/-- `log Q ≤ ℒ − 3.46` in the regime `T ≥ 300` (`3.46 < 5 log 2 ≤ log(300/2π)`).  This is
the ONLY place `T` enters Lemma 8.1′: it converts the sieve-efficiency exponent's `log Q`
into the statement's `ℒ`. -/
theorem log_Q_le (P : ParamsQ) (hT : (300:ℝ) ≤ P.T) (hQ3 : (3:ℝ) ≤ P.Q) :
    Real.log P.Q ≤ P.LL - 3.46 := by
  have hπ := Real.pi_pos
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  have hQpos : (0:ℝ) < P.Q := by linarith
  have hTpos : (0:ℝ) < P.T / (2 * Real.pi) := by positivity
  have hLLeq : P.LL = Real.log P.Q + Real.log (P.T / (2 * Real.pi)) := by
    have h : P.Q * P.T / (2 * Real.pi) = P.Q * (P.T / (2 * Real.pi)) := by ring
    show Real.log (P.Q * P.T / (2 * Real.pi)) = _
    rw [h, Real.log_mul (ne_of_gt hQpos) (ne_of_gt hTpos)]
  have h32 : (32:ℝ) ≤ P.T / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hlog32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h := Real.log_le_log (by norm_num : (0:ℝ) < 32) h32
  rw [hlog32] at h
  linarith

/-- `0 < ℒ` in the standing regime `Q ≥ 3`, `T ≥ 300`. -/
theorem LL_pos (P : ParamsQ) (hT : (300:ℝ) ≤ P.T) (hQ3 : (3:ℝ) ≤ P.Q) : 0 < P.LL := by
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  have hπ := Real.pi_pos
  show 0 < Real.log (P.Q * P.T / (2 * Real.pi))
  apply Real.log_pos
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-! #### The π- and log-numerals the final assembly needs -/

/-- `1/2π ≤ 0.1591612`. -/
theorem inv_two_pi_le : (1:ℝ) / (2 * Real.pi) ≤ 0.1591612 := by
  have hπl : (3.1415:ℝ) < Real.pi := Real.pi_gt_d4
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- `1/π ≤ 0.3183224`. -/
theorem inv_pi_le : (1:ℝ) / Real.pi ≤ 0.3183224 := by
  have hπl : (3.1415:ℝ) < Real.pi := Real.pi_gt_d4
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- `0.09675 ≤ c_μ = 3/π³` — the `log⁺` coefficient the μ-part must fit under. -/
theorem cMu_ge : (0.09675:ℝ) ≤ cMu := by
  have hπu : Real.pi < 3.1416 := Real.pi_lt_d4
  have hπ := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 9.8697 := by nlinarith
  have hpi3 : Real.pi ^ 3 < 31.007 := by nlinarith
  unfold cMu
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- `log 4 ≤ 1.3863`. -/
theorem log_four_le : Real.log 4 ≤ 1.3863 := by
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h]; linarith

end AnalyticInputs

set_option maxHeartbeats 1000000 in
/-- **Lemma 8.1′** (separated family mean square) — *the form actually used*.
`B_fam(τ) ≤ c₁Q(ℒ + C₀) + c_μ Q·log⁺(|τ|/4T)`, i.e. the `log⁺` carries the **μ-part's own**
coefficient `c_μ = 3/π³` rather than `c₁`.

This is exactly what LEMMA_QE §QE.i's proof produces: splitting `ν = μ_q + P_χ`, the
digamma envelope contributes `√(2·(18/π⁴)/(4π²))·Q = (3/π³)Q` to the `log⁺`, while the
prime part is τ-INDEPENDENT (`‖a(τ)‖₂² = Σ_{n≤X} Λ(n)²/n`, invariant under the τ-twist) and
so contributes to the constant only.  Only the *displayed* statement in paper §8 collapses
the two coefficients into a single `c₁`.

**It is what makes `calE2_maj_bound_L`'s hypothesis `p.L ≤ B` satisfiable at the paper's own
constant** — see `Bends`, `S5_LB_le_Bends`, `naive_Bends_fails`.  It
implies the paper-verbatim Lemma 8.1 (`Bfam_sq_le_of_sep`) because `c_μ ≤ c₁`.

Paper §8.
`LEMMA_QE` §QE.i; `NOTE_QR` §QR.1's numeric display.
Depends on: `largeSieveHyp` (Lemma 6.1), `Zeta23.ThmE.GammaChi`'s conductor-free
digamma constants (`abs_muq_le`), `famCount_le`, `cheb_sq_div_le`.  **The former
hypotheses `hΓ : ∀ q χ, GammaFactsChi (parity χ) q` and `hcoeff : ∀ q χ, χ ∈ primitiveChars q →
CoeffUnimodular q (χ ·)` are gone: neither is consumed by the proof, and `hΓ` was
moreover false at `q = 0`.**

Rule 17: `hX : X ≤ Q^{2−δ}` is LEMMA_QE §QE.i's own hypothesis — the SIEVE-EFFICIENCY
condition (X against Q², a `λ < 2` condition), NOT `X ≤ T`, and it must never be simplified
to anything mentioning `T` alone; with `X = (QT/2π)^λ` and λ* = 1.2507 it is a genuine
constraint of λ against the family size, satisfied at the design.  `hP : P.Valid` carries
`lam_pos`/`lam_lt_two` and no upper cap at 1.  `hΓ`, `hcoeff` are [R]'s χ-side hypothesis
structures — neither mentions λ, X or D₀.  **The conclusion contains no `X`: that is the
Rule-17 payoff of the whole section.  Any fill that reintroduces an `X` on the right has
broken the lemma.**

──────────────────────────────────────────────────────────────────────────────────────────
🚩 **`hδ : 0 < δ` IS TOO WEAK FOR `c₁ = 0.41`; the hypothesis carried is `hδ : 1/2 ≤ δ`.**
Two repairs were available and the other one — `hX : X ≤ P.XQ` — is **REFUTED**.  See
"THE REPAIR" at the end of this docstring for the refutation, the failing instance and the
arithmetic.

`c₁` is calibrated to the paper's own `X`, with essentially zero room, and `hX` as frozen
does not pin `X` there.  Read off the docstring's own identity

    c₁² = 9/π⁶ + λ*²/π² + o(1):   0.41² − 9/π⁶ = 0.158739,  ×π² = 1.56672,  √ = 1.25169,

i.e. the second summand is `(log X / ℒ)²/π²` and `c₁ = 0.41` is exactly the value at
`log X = λ*·ℒ`, `λ* = 1.2507321515`.  But `hδ : 0 < δ` puts no floor under `δ`, so `hX`
permits `log X` up to `(2 − δ)·log Q`, and `log Q ≤ ℒ − log(T/2π) ≤ ℒ − 3.865` at `T ≥ 300`
— i.e. `log X` up to ≈ `2ℒ`, against the `1.2507ℒ` the constant was fitted to.

**Where the proof breaks.**  §QE.i has exactly one route for the P-part: Lemma 6.1 at fixed
τ, i.e. `hsieve`, whose right-hand side is `(N + Qn² − 1)·Σ_{n≤X}Λ(n)²/n` at `N = ⌊X⌋`.
(Written at the sharp budget; at the Gallagher budget `Qn² + πN` now carried by
`LargeSieveHyp` the analysis below is unchanged with `Q^{−δ}` read as `πQ^{−δ}`, which does
not move the limit `δ ≥ 0.4823`.)
With `Σ_{n≤X}Λ(n)²/n = (log X)²/2 + O(log X)` (Chebyshev–Mertens, two-sided) and
`√(X + Qn² − 1) ≤ Q√(1 + Q^{−δ})` this gives, even at the *sharper* Minkowski split
(`√(Σ(μ+P)²) ≤ √(Σμ²) + √(ΣP²)`, which is already √2 better than the note's
`(a+b)² ≤ 2a² + 2b²`),

    B_fam/Q ≤ (3/(√2π³))(ℒ + log 4 + log⁺) + (2 − δ)√(1 + Q^{−δ})·log Q/(√2 π) + o(ℒ),

whose ℒ-coefficient is `0.0684 + (2 − δ)√(1+Q^{−δ})/(√2π)`.  Requiring that to be ≤ `c₁`
forces `(2 − δ)√(1 + Q^{−δ}) ≤ √2π(0.41 − 0.0684) = 1.5177`, i.e. **`δ ≥ 0.4823`** in the
limit.  Under `hδ : 0 < δ` alone it fails for every `δ < 0.48` at large `Q`.

**Failing instance** (of the route, hence of any fill from these hypotheses): `δ = 0.1`,
`Q = 10¹⁰⁰`, `T = 300` (`P.Valid.T_ge` is `T ≥ T₀ = 300`), `Qn = ⌊Q⌋`, `X = Q^{1.9}`, `τ = 0`.
Then `log Q = 230.2585`, `ℒ = 234.124`, `log X = 437.491`, `X + Qn² − 1 = Q²(1 + 10⁻¹⁰)`, and

    μ-part ≤ 16.1·Q,   P-part ≤ 98.5·Q,   total ≤ 114.6·Q,
    RHS   = c₁Q(ℒ + C₀) + c_μQ·log⁺(0) = 0.41·Q·240.124 = 98.4·Q.

The derivable bound exceeds the target by 16 %, and the gap grows linearly in ℒ.

**This is a hypothesis defect, not a claim that 8.1′ is false.**  The *truth* at that
instance is governed by the diagonal `Σ_q φ*(q)Σ_{(n,q)=1}Λ(n)²/n`, which gives
`B_fam ≈ (3/π³)Q·log X ≈ 0.19·Qℒ`, comfortably inside `0.41Q(ℒ+C₀)`; what fails is that
Lemma 6.1 overestimates the family mean square by `(X + Q²)/Σφ*(q) ≈ 10.8` (a factor 3.29
in `B_fam`) once `X ≍ Q²`.  So the statement is very likely TRUE and is certainly
UNPROVABLE from the hypotheses as frozen, by the only route §8 has.

──────────────────────────────────────────────────────────────────────────────────────────
🚩 **THE REPAIR: `hδ : 1/2 ≤ δ`.  The other candidate is REFUTED.**

Two candidate repairs were available, and the first was chosen initially
(`hX : X ≤ P.XQ`, on the ground that `nuFam_eq_nuQ` makes `P.XQ` the downstream
instantiation).  **That candidate makes the statement outright FALSE**, and not merely
unprovable by §8's route.  It is not taken.  The other is, and it is the right shape.

*Why `hX : X ≤ P.XQ` fails.*  `P.XQ = exp(λℒ) = (QT/2π)^λ` is a bound on `X` against `QT`,
not against `Q²`.  Nothing in `P.Valid` ties `T` to `Q` (that is `DesignOfRecord`'s job, and
this lemma does not take it), so `X` may exceed `Q²` by any factor.  And `Bfam` has an
unavoidable `√X`: the modulus `q = 1` lies in `Finset.Icc 1 Qn` for **every** `Qn ≥ 1`, its
unique character is primitive, and at `τ = 0`

    ν_{X,1}(0) = μ_1(0) + P_{X,1}(0),   P_{X,1}(0) = −(1/π)Σ_{n≤X}Λ(n)n^{−1/2} ∼ −(2/π)√X,

so `Bfam Qn X 0 ≥ (2/π)√X − 0.856` at every `Qn ≥ 1`.  The conclusion at `τ = 0` therefore
*forces* `X ≲ (π c₁/2)²Q²(ℒ+C₀)² = 0.4148·Q²(ℒ+C₀)²` — i.e. it forces exactly the
**sieve-efficiency shape `X ≤ Q^{2−δ}` that `hX` already has**, and no `λ`-side hypothesis
can substitute for it.

**Failing instance for `hX : X ≤ P.XQ`** (every hypothesis of `P.Valid` met; λ is the
paper's own λ*, so this is not an artefact of `lam_lt_two` being loose):
`Qn = 1`, `τ = 0`, `Q = 20`, `T = 2π e³⁰ = 6.715×10¹³`, `λ = λ* = 1.2507321515`.  Then
`ℒ = 32.9957`, `λℒ = 41.2688`, `X = P.XQ = 8.372×10¹⁷`, `√X = 9.15×10⁸`, and

    Bfam 1 X 0 ≈ (2/π)·9.15×10⁸ = 5.83×10⁸,
    RHS        = c₁·20·(32.9957 + 6) = 319.77,

off by a factor **1.8×10⁶**.  (The necessary bound at that point is `X ≤ 2.5×10⁵`.)

*Why `hδ : 1/2 ≤ δ` is the repair.*  It keeps the sieve-efficiency condition — which the
paragraph above shows is forced — and supplies the floor the constant needs.  Against the
arithmetic above, `1/2` is the weakest numeral that clears the asymptotic requirement
`(2−δ) ≤ √2π(c₁ − c_μ^sharp) = 1.5176` (i.e. `δ ≥ 0.4824`), where
`c_μ^sharp = 3/(√2π³) = 0.06842` is the μ-part's ℒ-coefficient under the SHARP family count
`Σ_{q≤Qn}φ*(q) ≤ (18/π⁴)Q²` and the Minkowski split `√(Σ(μ+P)²) ≤ √(Σμ²) + √(ΣP²)`.
It is satisfied at the design of record from `Q ≳ 10²⁸` — the design's own value is
`δ = 2 − λ*(1 + l/log Q)`, i.e. `0.481` at `10²⁵`, `0.589` at `10⁵⁰`, `0.656` at `10¹⁰⁰`,
`0.711` at `10³⁰⁰`, `→ 2 − λ* = 0.7493` — so it is a `Q₀(ε)`-type threshold in §10.5's own
sense, not a new constraint on the design.

──────────────────────────────────────────────────────────────────────────────────────────
🚩 **PROVED.  THE δ-FLOOR AND THE Q-FLOOR.**

The three inputs are in §1.0 above:
  * the q-uniform digamma envelope is `abs_muq_le` — from
    `Zeta23.ThmE.GammaChi.muq_stirling_const`, whose Stirling constant `20/2π` is
    **conductor-free** (the `log(q·)` cancels), taken at the cut `|τ| = 2` rather than
    `|τ| = 1` so the remainder is `5/2π` and not `20/2π`, with `muq_even`/`muq_monotoneOn`
    covering `|τ| ≤ 2` and `muq_zero_le`/`neg_one_lt_muq_zero` the lower half.  **Note
    `hΓ : GammaFactsChi` is NOT what does this work and is unused**: its `stirling` field is
    `∃ C, …`, so it is not uniform in `q`, which is precisely what §8 needs;
  * the `Σ_{q≤Qn} φ*(q)` count is `famCount_le`, from `ZetaQ.Normalisation.N2.Astar_bound`
    (**D26**, module docstring) — the SHARP `18/π⁴`, not the factor-2-safe `36/π⁴`;
  * the explicit Chebyshev–Mertens constant is `cheb_sq_div_le`, `(log X)²/2 + 12 log X + 12`
    — NOT `Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit`, whose `1537/log 2 ≈ 2218` is
    unusable here; see §1.0's header for why, and `cheb_sq_div_le` for the substitute route.

**`hδ : 1/2 ≤ δ` did not have to be raised.**  The projected floor `0.4824` was computed
against the *Minkowski* split `√(Σ(μ+P)²) ≤ √(Σμ²) + √(ΣP²)`, and that is what is
implemented (`sqrt_famSum_add_sq_le`); the floor as realised is
`2 − δ ≤ π(c₁ − ρ/2π)/0.7072` with `ρ = 0.44` the count's square root, i.e. `δ ≥ 0.4823`,
and `1/2` clears it.  Concretely, per unit of `Q` the proof charges

    μ-part:  0.44·(1/2π)·(ℒ + log 4 + 5 + log⁺)          [= 0.0700(ℒ + 6.386) + 0.0700·log⁺]
    P-part:  (1/π)·1.00005·(0.7072·log X + 8.5)          [log X ≤ 1.5(ℒ − 3.46)]
    ────────────────────────────────────────────────────
    total:   0.40773·ℒ + 1.9847 + 0.07003·log⁺  ≤  0.41(ℒ + 6) + (3/π³)·log⁺,

with `0.40773 ≤ c₁ = 0.41` (margin 0.6 %), `1.9847 ≤ c₁C₀ = 2.46` (margin 19 %) and
`0.07003 ≤ c_μ = 0.09675` (margin 28 %).  The binding constraint is the ℒ-coefficient.

**Where `hQ0 : 10⁹ ≤ P.Q` comes from, and why it is a new hypothesis rather than a larger
`δ`.**  Two places want `Q` large, and neither is repaired by `δ`:
  1. `Astar_bound`'s error `5N(1 + log N)²`, charged as `80/√Q` against the `0.1936 − 0.1848
     = 0.0088` of room in `0.44² = 0.1936`.  This needs `Q ≳ 8.3×10⁷` and is **δ-blind** —
     it is a statement about conductors only.  It is also not an artefact of the crude
     `(1+log x)² ≤ 16√x`: `A*(3) = 3` against `0.1936·9 = 1.74`, so the small-`Q` failure is
     genuine, and no `∀ Q ≥ 3` route reaches `0.44` (see `famCount_le`).
  2. `√(Qn² + πX) ≤ Q√(1 + πQ^{−δ})`, needing `πQ^{−δ} ≤ 10⁻⁴` (`pi_mul_X_le_of_sieve_eff`;
     Gallagher budget — with the former sharp budget `X + Qn² − 1` it was `Q^{−δ} ≤ 10⁻⁴`);
     at `δ = 1/2` this is `Q ≥ (π·10⁴)² ≈ 9.87×10⁸`.  This one *is* δ-sensitive.
`10⁹` is the round numeral clearing both with margin.  It is far below §10.4's range (which
starts at `Q = 10²⁵`) and far below the design of record `Q = 10¹⁰⁰`, so it is a `Q₀(ε)`
threshold in §10.5's own sense and constrains nothing downstream.

**Why the floor could NOT simply have been raised instead.**  The design's own δ is
`2 − λ*(1 + l/log Q) → 2 − λ* = 0.7493`, so any floor above `0.7493` makes Lemma 8.1′
vacuous at the design.  That is a real constraint on the route: with Chebyshev–Mertens at
main coefficient `1` (i.e. `Σ Λ²/n ≤ (log X)(log X + log 4 + 4)`, the cheap route off
`mertensFirst` alone) the floor is `≈ 0.95` and Lemma 8.1′ would be unusable.  The `1/2`
coefficient of `cheb_sq_div_le` and the Minkowski split are each necessary for a usable
statement; that is why both are proved here rather than approximated. -/
theorem Bfam_le_sep
    (P : ParamsQ) (Qn : ℕ) (X δ : ℝ)
    (hP : P.Valid)
    (hsieve : LargeSieveHyp)
    -- `0 < δ` puts no floor under the sieve-efficiency exponent; `c₁ = 0.41` needs
    -- `2 − δ ≤ √2π(c₁ − 3/(√2π³)) = 1.5176`.  See the docstring.
    (hQn : (Qn : ℝ) ≤ P.Q) (hδ : 1 / 2 ≤ δ) (hX1 : 1 ≤ X)
    (hX : X ≤ Real.rpow P.Q (2 - δ))
    -- the family count `Σ_{q≤Qn}φ*(q) ≤ 0.44²Q²` is a `Q₀`-threshold
    -- statement, not a `∀ Q ≥ 3` one.  See `famCount_le` and "THE Q-FLOOR" below.
    (hQ0 : (1000000000 : ℝ) ≤ P.Q) :
    ∀ τ : ℝ, Bfam Qn X τ ≤ c1Ends * P.Q * (P.LL + C0Ends) + cMu * P.Q * logPlusQ P τ := by
  intro τ
  have hπ := Real.pi_pos
  have hT : (300:ℝ) ≤ P.T := by
    have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h
  have hQ3 : (3:ℝ) ≤ P.Q := hP.Q_ge
  have hQpos : (0:ℝ) < P.Q := by linarith
  have hLL : (0:ℝ) < P.LL := LL_pos P hT hQ3
  have hXpos : (0:ℝ) < X := by linarith
  set A : ℝ := logPlusQ P τ with hAdef
  have hA0 : (0:ℝ) ≤ A := le_max_right _ _
  set Y : ℝ := Real.log X with hYdef
  have hY0 : (0:ℝ) ≤ Y := Real.log_nonneg hX1
  -- `log X ≤ (2 − δ) log Q ≤ 1.5 (ℒ − 3.46)`
  have hYle : Y ≤ 1.5 * (P.LL - 3.46) := by
    have h1 : Y ≤ Real.log (Real.rpow P.Q (2 - δ)) := Real.log_le_log hXpos hX
    have hrw : Real.log (Real.rpow P.Q (2 - δ)) = (2 - δ) * Real.log P.Q :=
      Real.log_rpow hQpos (2 - δ)
    rw [hrw] at h1
    have hlq : (0:ℝ) ≤ Real.log P.Q := Real.log_nonneg (by linarith)
    have h2 := log_Q_le P hT hQ3
    nlinarith [h1, hlq, h2, hδ]
  -- Minkowski: `B_fam ≤ √(Σμ²) + √(ΣP²)`
  have hBeq : Bfam Qn X τ = Real.sqrt (famSum Qn (fun q χ =>
      (Zeta23.ThmE.muq (parity χ) q τ
        + Zeta23.ThmE.PXc (fun n => χ (n : ZMod q)) X τ) ^ 2)) := rfl
  have hmink := sqrt_famSum_add_sq_le Qn
    (fun q χ => Zeta23.ThmE.muq (parity χ) q τ)
    (fun q χ => Zeta23.ThmE.PXc (fun n => χ (n : ZMod q)) X τ)
  -- the μ half
  have hμ := sqrt_famSum_muq_le P hT hQ3 hLL Qn hQn hQ0 τ
  -- the P half
  have hPh := sqrt_famSum_PXc_le Qn X τ hsieve
  -- the sieve factor and the Chebyshev factor
  have hfl : ((⌊X⌋₊:ℝ)) ≤ X := Nat.floor_le hXpos.le
  have hfl1 : (1:ℝ) ≤ ((⌊X⌋₊:ℝ)) := by
    have h := (Nat.one_le_floor_iff X).mpr hX1
    exact_mod_cast h
  have hXb := pi_mul_X_le_of_sieve_eff P.Q X δ hQ0 hδ hX
  have hQnn : (0:ℝ) ≤ (Qn:ℝ) := Nat.cast_nonneg Qn
  have hQn2 : (Qn:ℝ) ^ 2 ≤ P.Q ^ 2 := by nlinarith [hQnn, hQn]
  have hπfl : Real.pi * (⌊X⌋₊ : ℝ) ≤ Real.pi * X := mul_le_mul_of_nonneg_left hfl Real.pi_pos.le
  have hfac : ((Qn:ℝ) ^ 2 + Real.pi * (⌊X⌋₊ : ℝ)) ≤ 1.0001 * P.Q ^ 2 := by linarith
  have hfac0 : (0:ℝ) ≤ ((Qn:ℝ) ^ 2 + Real.pi * (⌊X⌋₊ : ℝ)) := by
    have := mul_nonneg Real.pi_pos.le (show (0:ℝ) ≤ (⌊X⌋₊ : ℝ) from Nat.cast_nonneg _)
    nlinarith [sq_nonneg (Qn:ℝ)]
  have hcheb := cheb_sq_div_le X hX1
  have hchebV : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n ^ 2 / n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hVnn : (0:ℝ) ≤ Y ^ 2 / 2 + 12 * Y + 12 := by nlinarith
  have hprod : ((Qn:ℝ) ^ 2 + Real.pi * (⌊X⌋₊ : ℝ))
        * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n ^ 2 / n
      ≤ (1.00005 * P.Q) ^ 2 * (Y ^ 2 / 2 + 12 * Y + 12) := by
    have h1 : ((Qn:ℝ) ^ 2 + Real.pi * (⌊X⌋₊ : ℝ))
          * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n ^ 2 / n
        ≤ (1.0001 * P.Q ^ 2) * (Y ^ 2 / 2 + 12 * Y + 12) :=
      mul_le_mul hfac hcheb hchebV (by positivity)
    have h2 : (1.0001 * P.Q ^ 2) * (Y ^ 2 / 2 + 12 * Y + 12)
        ≤ (1.00005 * P.Q) ^ 2 * (Y ^ 2 / 2 + 12 * Y + 12) := by
      have h3 : (1.0001:ℝ) * P.Q ^ 2 ≤ (1.00005 * P.Q) ^ 2 := by nlinarith [sq_nonneg P.Q]
      exact mul_le_mul_of_nonneg_right h3 hVnn
    linarith
  have hsqrtW : Real.sqrt (((Qn:ℝ) ^ 2 + Real.pi * (⌊X⌋₊ : ℝ))
        * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n ^ 2 / n)
      ≤ (1.00005 * P.Q) * (0.7072 * Y + 8.5) := by
    refine (Real.sqrt_le_sqrt hprod).trans ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    exact mul_le_mul_of_nonneg_left (sqrt_cheb_le Y hY0) (by positivity)
  -- assemble the two halves
  have hsum : Bfam Qn X τ
      ≤ 0.44 * P.Q * muEnvQ P τ + (1 / Real.pi) * ((1.00005 * P.Q) * (0.7072 * Y + 8.5)) := by
    rw [hBeq]
    refine hmink.trans (add_le_add hμ (hPh.trans ?_))
    exact mul_le_mul_of_nonneg_left hsqrtW (by positivity)
  -- ─── the numeric core, per unit of Q ───────────────────────────────────────────────
  have hu : (1:ℝ) / (2 * Real.pi) ≤ 0.1591612 := inv_two_pi_le
  have hv : (1:ℝ) / Real.pi ≤ 0.3183224 := inv_pi_le
  have hcmu : (0.09675:ℝ) ≤ cMu := cMu_ge
  have hlog4' : Real.log 4 ≤ 1.3863 := log_four_le
  have hlog40 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- μ term, per unit of Q
  have hmuterm : 0.44 * muEnvQ P τ ≤ 0.07003093 * (P.LL + 6.3863) + 0.07003093 * A := by
    have hpos : (0:ℝ) ≤ P.LL + Real.log 4 + 5 + A := by linarith
    have h1 : (1 / (2 * Real.pi)) * (P.LL + Real.log 4 + 5 + A)
        ≤ 0.1591612 * (P.LL + Real.log 4 + 5 + A) :=
      mul_le_mul_of_nonneg_right hu hpos
    have h2 : (0.1591612:ℝ) * (P.LL + Real.log 4 + 5 + A)
        ≤ 0.1591612 * (P.LL + 1.3863 + 5 + A) := by nlinarith
    unfold muEnvQ
    rw [← hAdef]
    nlinarith [h1, h2]
  -- P term, per unit of Q
  have hPterm : (1 / Real.pi) * (1.00005 * (0.7072 * Y + 8.5))
      ≤ 0.33769337 * (P.LL - 3.46) + 2.7058764 := by
    have hnn : (0:ℝ) ≤ 1.00005 * (0.7072 * Y + 8.5) := by nlinarith
    have h1 : (1 / Real.pi) * (1.00005 * (0.7072 * Y + 8.5))
        ≤ 0.3183224 * (1.00005 * (0.7072 * Y + 8.5)) :=
      mul_le_mul_of_nonneg_right hv hnn
    nlinarith [h1, hYle]
  -- combine, then multiply by Q
  have hscalar : 0.44 * muEnvQ P τ + (1 / Real.pi) * (1.00005 * (0.7072 * Y + 8.5))
      ≤ c1Ends * (P.LL + C0Ends) + cMu * A := by
    have hAterm : (0.09675:ℝ) * A ≤ cMu * A := mul_le_mul_of_nonneg_right hcmu hA0
    unfold c1Ends C0Ends
    nlinarith [hmuterm, hPterm, hAterm, hLL]
  have hfinal : 0.44 * P.Q * muEnvQ P τ
        + (1 / Real.pi) * ((1.00005 * P.Q) * (0.7072 * Y + 8.5))
      ≤ c1Ends * P.Q * (P.LL + C0Ends) + cMu * P.Q * A := by
    have h := mul_le_mul_of_nonneg_left hscalar hQpos.le
    nlinarith [h]
  linarith [hsum, hfinal]


/-- **Lemma 8.1** (family mean square), **paper-verbatim**.
`Σ_χ ν_{X,χ}(τ)² ≤ c₁²Q²(ℒ + log⁺(|τ|/4T) + C₀)²` with `(c₁, C₀) = (0.41, 6)`.

**No `X` on the right-hand side — this is the whole point of the lemma.**  Kept as a
statement in its own right (paper fidelity) and derived from the separated form 8.1′; it is
8.1′ that is instantiated downstream, because 8.1 as displayed cannot satisfy
`calE2_maj_bound_L`'s `p.L ≤ B` (`naive_Bends_fails`).

Paper §8. Derivation: `LEMMA_QE` §QE.i; `NOTE_QR` §QR.1.
Depends on: `Bfam_le_sep`, `cMu_le_c1Ends`.
Rule 17: identical audit to `Bfam_le_sep`; conclusion X-free.
**`hδ` is `1/2 ≤ δ` and `hQ0 : 10⁹ ≤ P.Q`, both tracking `Bfam_le_sep` (see its docstring,
"THE δ-FLOOR AND THE Q-FLOOR"); `hΓ`/`hcoeff` are absent for the same reason they are
absent there.** -/
theorem Bfam_sq_le
    (P : ParamsQ) (Qn : ℕ) (X δ : ℝ)
    (hP : P.Valid)
    (hsieve : LargeSieveHyp)
    (hQn : (Qn : ℝ) ≤ P.Q) (hδ : 1 / 2 ≤ δ) (hX1 : 1 ≤ X)
    (hX : X ≤ Real.rpow P.Q (2 - δ)) (hQ0 : (1000000000 : ℝ) ≤ P.Q) :
    ∀ τ : ℝ, BfamSq Qn X τ
      ≤ c1Ends ^ 2 * P.Q ^ 2 * (P.LL + logPlusQ P τ + C0Ends) ^ 2 :=
  -- 8.1′ ⟹ 8.1; the argument is `Bfam_sq_le_of_sep` (stated below), repeated here because
  -- that lemma is declared after this one.
  fun τ => by
  have hQ : (0 : ℝ) ≤ P.Q := by linarith [hP.Q_ge]
  have hsep := Bfam_le_sep P Qn X δ hP hsieve hQn hδ hX1 hX hQ0
  have hBsq : (0 : ℝ) ≤ BfamSq Qn X τ := by
    unfold BfamSq famSum
    exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun χ _ => sq_nonneg _
  have hlp : (0 : ℝ) ≤ logPlusQ P τ := le_max_right _ _
  have hstep : Bfam Qn X τ ≤ c1Ends * P.Q * (P.LL + logPlusQ P τ + C0Ends) := by
    refine (hsep τ).trans ?_
    have hmu : cMu * P.Q * logPlusQ P τ ≤ c1Ends * P.Q * logPlusQ P τ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cMu_le_c1Ends hQ) hlp
    have hexp : c1Ends * P.Q * (P.LL + logPlusQ P τ + C0Ends)
        = c1Ends * P.Q * (P.LL + C0Ends) + c1Ends * P.Q * logPlusQ P τ := by ring
    rw [hexp]; linarith
  rw [(Real.sq_sqrt hBsq).symm]
  calc Bfam Qn X τ ^ 2
      ≤ (c1Ends * P.Q * (P.LL + logPlusQ P τ + C0Ends)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hstep 2
    _ = c1Ends ^ 2 * P.Q ^ 2 * (P.LL + logPlusQ P τ + C0Ends) ^ 2 := by ring

/-- **8.1′ ⟹ 8.1.**  Square the separated bound and use `c_μ ≤ c₁` together with
`0 ≤ log⁺`; the constant `c₁` is recovered because `c₁Q(ℒ+C₀) + c_μQ·log⁺
≤ c₁Q(ℒ + log⁺ + C₀)`.

Paper §8; this is the step "8.1′ ⟹ 8.1" (`cμ ≤ c₁`, `0 ≤ ·`).
Depends on: `cMu_le_c1Ends`, `Real.sq_sqrt`.
Rule 17: hypothesis-free apart from `0 ≤ Q` and the separated bound. -/
theorem Bfam_sq_le_of_sep
    (P : ParamsQ) (Qn : ℕ) (X : ℝ) (hQ : 0 ≤ P.Q)
    (hsep : ∀ τ : ℝ, Bfam Qn X τ ≤ c1Ends * P.Q * (P.LL + C0Ends) + cMu * P.Q * logPlusQ P τ) :
    ∀ τ : ℝ, BfamSq Qn X τ
      ≤ c1Ends ^ 2 * P.Q ^ 2 * (P.LL + logPlusQ P τ + C0Ends) ^ 2 := by
  intro τ
  have hBsq : (0 : ℝ) ≤ BfamSq Qn X τ := by
    unfold BfamSq famSum
    exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun χ _ => sq_nonneg _
  have hlp : (0 : ℝ) ≤ logPlusQ P τ := le_max_right _ _
  -- `c_μ ≤ c₁` upgrades the separated bound to the paper's single-constant one.
  have hstep : Bfam Qn X τ ≤ c1Ends * P.Q * (P.LL + logPlusQ P τ + C0Ends) := by
    refine (hsep τ).trans ?_
    have hmu : cMu * P.Q * logPlusQ P τ ≤ c1Ends * P.Q * logPlusQ P τ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cMu_le_c1Ends hQ) hlp
    have hexp : c1Ends * P.Q * (P.LL + logPlusQ P τ + C0Ends)
        = c1Ends * P.Q * (P.LL + C0Ends) + c1Ends * P.Q * logPlusQ P τ := by ring
    rw [hexp]; linarith
  have hsq : BfamSq Qn X τ = Bfam Qn X τ ^ 2 := (Real.sq_sqrt hBsq).symm
  rw [hsq]
  calc Bfam Qn X τ ^ 2
      ≤ (c1Ends * P.Q * (P.LL + logPlusQ P τ + C0Ends)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hstep 2
    _ = c1Ends ^ 2 * P.Q ^ 2 * (P.LL + logPlusQ P τ + C0Ends) ^ 2 := by ring

/-! ## 2. The six instantiation obligations S1–S6

Consuming [R]'s (B, ν)-generic seam at
the pair `(ν, B) := (envSep P, Bends P)`, scale `s := c_μ Q`, with the family sum handled
*before* the call by Cauchy–Schwarz.  **Nothing else is required.**

`S1` is `S1_toSetting_L` above.  S2–S6 follow. -/

/-- **S2** (the taper bundle) — **the ONE dependency of §8 that had not been examined**.

`LocalHypsCoreW c_ϱ (toSetting P) (P.toParams.localFun P.T)`: the 44-field window-generic
taper bundle of `Zeta23/PrimeSideA/Basic.lean:559`, at the paper's own taper data
(`Zeta23.Params.localFun` = `⟨φ̂, Φ, A_φ, g, a, b⟩`, `PrimeSideB/Concrete.lean:40`) and the
paper's own `c_ϱ = 4‖ϱ′‖_∞ + 4‖ϱ″‖₁` (`Zeta23.Params.crho`, `Zeta23/Defs.lean:268`).

⚠ **The witness CANNOT come via `Zeta23.PrimeSide.LocalHypsCore.toCoreW`
(`Basic.lean:648`)**: `LocalHypsCore` carries `lam_le_one`, and at
`(toSetting P).lam = λℒ/l ≈ 18–116` that hypothesis is false.  The
witness is now built from the product window's `AdmWindow` instance
(`ParamsQ.Valid.admWindow`, `ZetaQ/Window.lean`), field by field as [R]'s own generic
`AdmWindow.localHypsCore` (`Zeta23/ThmD/WindowLocalHyps.lean`) — which carries `lam_le_one`
and is therefore NOT cited (Rule 0: the cap is on the wrapper; the toolkit below it,
`Zeta23/ThmD/WindowCore.lean` + `PsiC.lean`, is cap-free). The constant is the window
constant `P.cWin` (`c_ϱ + M₁λ + (M₁λ)² + M₂λ²`), not `P.toParams.crho`, which is meaningless
for the realising profile. Before F58 the witness was the flat facade under
`Params.ValidQ` (`Valid.toParamsValidQ`, now gone).
Every field is λ-free on its face (statements about φ̂, Φ, ψ at bandwidth L), so this should
be mechanical — but it is **not verified**, it is a taper/Poisson question rather than an
ends question, and it belongs in the launch brief.

Paper §2.2 + [R] H4.
Depends on: `Zeta23/PrimeSideA/Bridge.lean`, `Zeta23/Taper/`, `ZetaQ.ParamsQ.Valid`.
Rule 17: `LocalHypsCoreW` is audited field by field below and is CLEAN — its
`lam_pos : 0 < p.lam` has no upper companion *by construction* (the structure is
`LocalHypsCore` minus `lam_le_one`).  `PiX_bound` is X-dependent but is a THEOREM for all
`X ≥ 1` (`Zeta23/PiFacts.lean:131-133`), so discharging it imports no cap.  `hwL` and `hl`
are `[eq:wrange]` and "T large", neither a bandwidth cap. -/
theorem S2_localHypsCoreW (P : ParamsQ) (hP : P.Valid)
    (hwL : P.w ≤ P.LB / 8) (hl : 1 ≤ Zeta23.l P.T) (hX : 1 ≤ P.XQ) :
    LocalHypsCoreW P.cWin (toSetting P) (P.toParams.localFun P.T) := by
  -- the witness is built from the product window's `AdmWindow` instance
  -- (`ParamsQ.Valid.admWindow`, `ZetaQ/Window.lean`) — field by field as [R]'s own
  -- `AdmWindow.localHypsCore` (`Zeta23/ThmD/WindowLocalHyps.lean`) does, but WITHOUT that
  -- theorem's `lam_le_one` (Rule 17: `LocalHypsCoreW` is `LocalHypsCore` minus the cap), and
  -- with the two moment floors `b ≥ 1/2` (`Valid.b_ge`) and `a ≤ 1` (`AdmWindow.av_le_one`).
  -- The window constant is `cWin` (the flat facade's `crho` is meaningless for the realising
  -- profile); the ψ-majorant fields are [R]'s `PsiC` lemmas at `c = cWin`.
  have hlne : Zeta23.l P.T ≠ 0 := by linarith
  have hLB : P.toParams.L P.T = P.LB := P.toParams_L hlne
  have hw8 : 8 * P.w ≤ P.LB := by linarith
  have hW := hP.admWindow hw8
  have hc := hP.four_le_cWin
  have hlampos : (0 : ℝ) < P.toParams.lam := hP.toParams_lam_pos
  have hX' : (1 : ℝ) ≤ P.toParams.X P.T := by rw [P.toParams_X hlne]; exact hX
  have hsL : (toSetting P).L = P.LB := S1_toSetting_L P hlne
  have hps : psiA P.cWin (toSetting P) = Zeta23.PsiC.psiC P.cWin P.LB P.w := by
    rw [← Zeta23.PsiC.psiC_eq_psiA, hsL]; rfl
  have htau : ∀ k : ℤ, (toSetting P).tau k = P.T + k * (2 * Real.pi / P.LB) := fun k => by
    show P.toParams.tau P.T k = _
    exact hP.tau_eq k
  have hcw : (0 : ℝ) ≤ P.cWin / P.w := div_nonneg hW.c_nonneg hW.w_pos.le
  rw [hP.localFun_eq]
  exact
  { four_le_cϱ := hc
    lam_pos := hlampos
    one_le_w := hP.one_le_w
    w_le := by show P.w ≤ (toSetting P).L / 8; rw [hsL]; exact hwL
    one_le_l := hl
    phiHat_cont := hW.vHatR_continuous
    phiHat_even := hW.vHatR_even
    phiHat_le_L := by rw [hsL]; exact hW.abs_vHatR_le_L
    phiHat_le_inv := hW.abs_vHatR_mul_abs_le
    phiHat_le_sq := hW.abs_vHatR_mul_sq_le
    phiHat_sq_integrable := hW.integrable_vHatR_sq
    phiHat_sq_mul_abs_integrable := hW.integrable_vHatR_sq_mul_abs
    integral_phiHat_sq_mul_abs_le := by
      rw [hsL]
      exact Zeta23.PsiC.integral_sq_mul_abs_le_of_le_psi hc hP.one_le_w hw8
        (hP.abs_phiHatR_le_psiC hw8)
    phiHat_sq_mul_sq_integrable :=
      Zeta23.PsiC.integrable_sq_mul_sq_of_bounds hW.vHatR_continuous hcw
        hW.abs_vHatR_mul_abs_le hW.abs_vHatR_mul_sq_le
    integral_phiHat_sq_mul_sq_le :=
      Zeta23.PsiC.integral_sq_mul_sq_le_of_bounds hcw hW.abs_vHatR_mul_abs_le
        hW.abs_vHatR_mul_sq_le
    phiHat_sq_integral := by rw [hsL]; exact hW.integral_vHatR_sq
    phiHat_sq_fourier := hW.integral_vHatR_sq_mul_cos
    g_nonneg := hW.gv_nonneg
    g_le_Aphi := hW.gv_le_Av
    Aphi_le := by rw [hsL]; exact hW.Av_le
    Phi_contDiff := hW.VPhiR_contDiff_one
    Phi_even := hW.VPhiR_even
    Phi_le_L := by rw [hsL]; exact hW.abs_VPhiR_le_L
    Phi_le_inv := hW.abs_VPhiR_mul_abs_le
    Phi_le_sq := hW.abs_VPhiR_mul_sq_le
    Phi_sq_integrable := hW.integrable_VPhiR_sq
    Phi_sq_mul_abs_integrable := hW.integrable_VPhiR_sq_mul_abs
    integral_Phi_sq_mul_abs_le := by
      rw [hsL]
      exact Zeta23.PsiC.integral_sq_mul_abs_le_of_le_psi hc hP.one_le_w hw8
        (hP.abs_PhiQ_le_psiC hw8)
    Phi_sq_mul_sq_integrable :=
      Zeta23.PsiC.integrable_sq_mul_sq_of_bounds hW.VPhiR_continuous hcw
        hW.abs_VPhiR_mul_abs_le hW.abs_VPhiR_mul_sq_le
    integral_Phi_sq_mul_sq_le :=
      Zeta23.PsiC.integral_sq_mul_sq_le_of_bounds hcw hW.abs_VPhiR_mul_abs_le
        hW.abs_VPhiR_mul_sq_le
    Phi_zero := by rw [hsL]; exact hW.VPhiR_zero
    Phi_sq_integral := by rw [hsL]; exact hW.integral_VPhiR_sq
    Phi_sq_fourier := hW.integral_VPhiR_sq_mul_cos
    poisson := by
      intro τ τ'
      have h := hW.hasSum_vHatR_mul P.T τ τ'
      simp only [htau, hsL]
      exact h
    b_ge_half := by
      show (1 : ℝ) / 2 ≤ Zeta23.AdmWindow.bv P.phiQ P.LB
      rw [← hP.bQ_eq_bv]; exact hP.b_ge
    b_le_a := hW.bv_le_av
    a_le_one := hW.av_le_one
    PiX_cont := Zeta23.PiX_continuous (Real.exp_pos _)
    PiX_bound := Zeta23.PiX_abs_le hX'
    psi_integrable := by rw [hps]; exact Zeta23.PsiC.psi_integrable hc hP.one_le_w hw8
    psi_sq_integrable := by rw [hps]; exact Zeta23.PsiC.psi_sq_integrable hc hP.one_le_w hw8
    integral_psi_Ioi_le := by
      rw [hps, hsL]; exact Zeta23.PsiC.integral_psi_Ioi_le hc hP.one_le_w hw8
    integral_psi_sq_le := by
      rw [hps, hsL]; exact Zeta23.PsiC.integral_psi_sq_le hc hP.one_le_w hw8
    phiHat_le_psi := by rw [hps]; exact hP.abs_phiHatR_le_psiC hw8
    Phi_le_psi := by rw [hps]; exact hP.abs_PhiQ_le_psiC hw8 }

/-- **S3** (continuity of the envelope).  `env_sep(τ) = B_ends + max(log(|τ|/4T), 0)` is
continuous: it is identically `B_ends` on `[−4T, 4T]` (including `τ = 0`, where Mathlib's
`Real.log 0 = 0` gives the right value) and `B_ends + log(|τ|/4T)` outside; the glue is
`Continuous.max` after `Real.continuousOn_log` away from 0.

Paper §8 (the `Continuous ν` hypothesis of the `_L` lemmas).
Rule 17: `0 < P.T` only. -/
theorem S3_continuous_envSep (P : ParamsQ) (hT : 0 < P.T) : Continuous (envSep P) := by
  have hlog : Continuous (logPlusQ P) := by
    rw [continuous_iff_continuousAt]
    intro τ
    rcases eq_or_ne τ 0 with rfl | hτ
    · -- on the ball `|x| < 4T` the `log⁺` is identically `0`, so it is continuous at `0`
      have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds (0 : ℝ)] logPlusQ P := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0:ℝ) < 4 * P.T)] with x hx
        have hx' : |x| < 4 * P.T := by
          simpa [Real.dist_eq] using hx
        have h0 : (0 : ℝ) ≤ |x| / (4 * P.T) := by positivity
        have h1 : |x| / (4 * P.T) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        show (0 : ℝ) = logPlusQ P x
        rw [logPlusQ, max_eq_right (Real.log_nonpos h0 h1)]
      exact continuousAt_const.congr hev
    · have hne : |τ| / (4 * P.T) ≠ 0 := by
        have : (0 : ℝ) < |τ| := abs_pos.mpr hτ
        positivity
      have hc : ContinuousAt (fun x : ℝ => Real.log (|x| / (4 * P.T))) τ :=
        ContinuousAt.log (by fun_prop) hne
      exact hc.max continuousAt_const
  exact continuous_const.add hlog

/-- S3, companion for the paper-verbatim envelope `envQ`.  Same proof. -/
theorem S3_continuous_envQ (P : ParamsQ) (hT : 0 < P.T) : Continuous (envQ P) := by
  have h := S3_continuous_envSep P hT
  have he : envQ P = fun τ => (P.LL + C0Ends - Bends P) + envSep P τ := by
    funext τ; unfold envQ envSep; ring
  rw [he]
  exact continuous_const.add h

/-- Continuity of each `ν_{X,χ}` — the `hν` hypothesis of Lemma 8.2's family pass.
`muq κ q` is smooth (`Zeta23.ThmE.GammaFactsChi.smooth`) and `PXc c X` is a finite
trigonometric polynomial, continuous for `X > 0` (`Zeta23/ThmE/PrimeSideChi.lean:579`).

Rule 17: clean — `0 < X` is nondegeneracy. -/
theorem continuous_nuFam (X : ℝ) (hX : 0 < X) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hΓ : Zeta23.ThmE.GammaFactsChi (parity χ) q) : Continuous (nuFam X χ) := by
  show Continuous fun τ => Zeta23.ThmE.muq (parity χ) q τ
      + Zeta23.ThmE.PXc (fun n => χ (n : ZMod q)) X τ
  exact hΓ.smooth.continuous.add (Zeta23.ThmE.PXc_continuous _ hX)

/-- **S4** (the `NuBound` at the separated scale).  `NuBound (toSetting P) (Bends P)
(envSep P)`: `|env_sep(τ)| ≤ B_ends + log⁺(|τ|/4T)` — with **coefficient exactly 1 on the
`log⁺`, the literal `NuBound` shape** (`EndsCore.lean:63-64`).  Together with Lemma 8.1′
divided by `s = c_μ Q`, this is what licenses the instantiation.

Paper §8.
Rule 17: `P.Valid` only — no λ ≤ 1, no X ≤ T, no D₀ = √T. -/
theorem S4_nuBound_envSep (P : ParamsQ) (hP : P.Valid) :
    NuBound (toSetting P) (Bends P) (envSep P) := by
  have hQ : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hT : (300 : ℝ) ≤ P.T := by
    have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hLL : (0 : ℝ) ≤ P.LL := by
    unfold ParamsQ.LL
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hQ hT (by norm_num : (0:ℝ) ≤ 300) (by linarith : (0:ℝ) ≤ P.Q),
      Real.pi_pos]
  have hBends : (0 : ℝ) ≤ Bends P := by
    have : (0 : ℝ) ≤ c1Ends * (P.LL + C0Ends) := by
      unfold c1Ends C0Ends; linarith
    exact div_nonneg this cMu_pos.le
  intro τ
  have h0 : (0 : ℝ) ≤ logPlusQ P τ := le_max_right _ _
  rw [abs_of_nonneg (by show (0:ℝ) ≤ Bends P + logPlusQ P τ; linarith)]
  show Bends P + logPlusQ P τ ≤ Bends P + logPlusQ P τ
  exact le_rfl

/-- **S5** — **THE CRITICAL SIDE CONDITION.**  `p.L ≤ B` at `B := B_ends`, i.e.
`λℒ ≤ c₁(ℒ + C₀)/c_μ = 4.238(ℒ + 6)`.

True with a factor **≈ 3.39 of room** at λ* = 1.2507321515: `P.Valid` already gives
`λ < 2 < 4.238`, and `ℒ > 0` follows from `Q ≥ 3`, `T ≥ 300`.  This is the hypothesis of
`Zeta23.PrimeSide.calE2_maj_bound_L` (`EndsE2.lean:353`) — **the one the paper's own
normalisation cannot satisfy** (see `naive_Bends_fails` and the `Bends` docstring).

Paper §8.
Rule 17: `P.Valid`'s `lam_lt_two` is `λ < 2` — the paper's standing convention and the
sieve's own range, **not** `λ ≤ 1`.  The inequality is comfortably true at λ* > 1; it would
be true at λ ≤ 1 too, but nothing here assumes that. -/
theorem S5_LB_le_Bends (P : ParamsQ) (hP : P.Valid) : P.LB ≤ Bends P := by
  have hQ : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hT : (300 : ℝ) ≤ P.T := by
    have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi' : Real.pi ≤ 4 := Real.pi_le_four
  have hpi3 : (27 : ℝ) < Real.pi ^ 3 := by
    have := pow_lt_pow_left₀ hpi (by norm_num : (0:ℝ) ≤ 3) (by norm_num : 3 ≠ 0)
    norm_num at this; exact this
  -- `ℒ = log(QT/2π) ≥ 0` from `Q ≥ 3`, `T ≥ 300`.
  have hLL : (0 : ℝ) ≤ P.LL := by
    unfold ParamsQ.LL
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hQ hT (by norm_num : (0:ℝ) ≤ 300) (by linarith : (0:ℝ) ≤ P.Q)]
  have hLBnn : (0 : ℝ) ≤ P.LB := by
    unfold ParamsQ.LB; exact mul_nonneg hP.lam_pos.le hLL
  -- `λ < 2` (Valid.lam_lt_two — NOT `λ ≤ 1`).
  have hLB2 : P.LB ≤ 2 * P.LL := by
    unfold ParamsQ.LB; nlinarith [hP.lam_lt_two]
  have hcmu : cMu ≤ 1 / 9 := by
    unfold cMu
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  show P.LB ≤ c1Ends * (P.LL + C0Ends) / cMu
  rw [le_div_iff₀ cMu_pos]
  have hstep : P.LB * cMu ≤ P.LB * (1 / 9) := mul_le_mul_of_nonneg_left hcmu hLBnn
  unfold c1Ends C0Ends
  linarith

/-- **The failure, made a statement.**  The paper's own displayed normalisation `B := ℒ + C₀`
does **not** satisfy `calE2_maj_bound_L`'s hypothesis `p.L ≤ B` anywhere in range:
at `λ ≥ λ*` and `ℒ ≥ 24` we have `¬ (λℒ ≤ ℒ + C₀)`, since `(λ − 1)ℒ ≥ 0.2507·24 = 6.02 > 6`.
(At Q = 10¹⁰⁰: ℒ ≈ 247.7, L ≈ 309.8, `ℒ + C₀` = 253.7 — fails by 1.221×; asymptotically by
λ* = 1.2507×.)  `ℒ = log(QT/2π) ≥ log Q`, so the naive instantiation is available only for
`Q ≲ 3×10¹⁰`.

This lemma exists so that the finding is auditable rather than commentary.  It is the
reason `Bends` and `cMu` exist.

Paper §8 vs [R] `EndsE2.lean:353`.
Rule 17: the hypotheses are LOWER bounds on λ and ℒ — the opposite of a bandwidth cap. -/
theorem naive_Bends_fails (P : ParamsQ) (hlam : lamStar ≤ P.lam) (hL : 24 ≤ P.LL) :
    ¬ (P.LB ≤ P.LL + C0Ends) := by
  unfold lamStar at hlam
  unfold ParamsQ.LB C0Ends
  simp only [not_le]
  nlinarith [mul_le_mul_of_nonneg_right hlam (by linarith : (0:ℝ) ≤ P.LL)]

/-- **S6** (the family pass, pointwise in `(τ, τ′)`).
`Σ_χ |ν_χ(τ)||ν_χ(τ′)| ≤ B_fam(τ)B_fam(τ′) ≤ (c_μQ)²·env_sep(τ)·env_sep(τ′)`.

The first step is Cauchy–Schwarz in χ — `Finset.sum_mul_sq_le_sq_mul_sq`, in use in [R] at
`EndsCore.lean:584` and `MV/Quadratic.lean:88` — applied **POINTWISE in (τ, τ′), before any
τ-integration**; the second is Lemma 8.1′ twice.  Because both majorant kernels factor the
ν-dependence as exactly `|ν(τ)|·|ν(τ′)|` (see `sum_majK1_le`), this single inequality is the
entire seam: it is what lets the family sum pass inside the double integral.

Paper §8; `LEMMA_QE` §QE.ii.
Depends on: `Bfam_le_sep`, `Finset.sum_mul_sq_le_sq_mul_sq`.
Rule 17: only the separated envelope enters; no X on the right. -/
theorem S6_family_pass (P : ParamsQ) (Qn : ℕ) (X : ℝ)
    (hsep : ∀ τ : ℝ, Bfam Qn X τ ≤ cMu * P.Q * envSep P τ) (τ τ' : ℝ) :
    famSum Qn (fun _ χ => |nuFam X χ τ| * |nuFam X χ τ'|)
      ≤ (cMu * P.Q) ^ 2 * (envSep P τ * envSep P τ') := by
  -- flatten the family double sum, so Cauchy–Schwarz applies in one index
  set S : Finset ((_ : ℕ) × DirichletCharacter ℂ _) :=
    (Finset.Icc 1 Qn).sigma (fun q => primitiveChars q) with hS
  have hflat : ∀ f : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
      famSum Qn f = ∑ x ∈ S, f x.1 x.2 := fun f => Finset.sum_sigma' _ _ _
  have hsqflat : ∀ σ : ℝ, BfamSq Qn X σ = ∑ x ∈ S, nuFam X x.2 σ ^ 2 := fun σ =>
    hflat (fun _ χ => nuFam X χ σ ^ 2)
  -- Cauchy–Schwarz in χ, POINTWISE in `(τ, τ′)`
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun x => |nuFam X x.2 τ|) (fun x => |nuFam X x.2 τ'|)
  have hsq1 : ∀ σ : ℝ, ∑ x ∈ S, |nuFam X x.2 σ| ^ 2 = BfamSq Qn X σ := by
    intro σ
    rw [hsqflat σ]
    exact Finset.sum_congr rfl fun x _ => sq_abs _
  rw [hsq1 τ, hsq1 τ'] at hCS
  have hnn : (0 : ℝ) ≤ ∑ x ∈ S, |nuFam X x.2 τ| * |nuFam X x.2 τ'| :=
    Finset.sum_nonneg fun x _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB0 : ∀ σ : ℝ, (0 : ℝ) ≤ Bfam Qn X σ := fun σ => Real.sqrt_nonneg _
  have hBsq : ∀ σ : ℝ, BfamSq Qn X σ = Bfam Qn X σ ^ 2 := by
    intro σ
    refine (Real.sq_sqrt ?_).symm
    unfold BfamSq famSum
    exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun χ _ => sq_nonneg _
  rw [hBsq τ, hBsq τ'] at hCS
  -- `Σ ≤ B_fam(τ)·B_fam(τ′)`
  have hmain : ∑ x ∈ S, |nuFam X x.2 τ| * |nuFam X x.2 τ'|
      ≤ Bfam Qn X τ * Bfam Qn X τ' := by
    nlinarith [hCS, hnn, hB0 τ, hB0 τ', mul_nonneg (hB0 τ) (hB0 τ')]
  rw [hflat (fun _ χ => |nuFam X χ τ| * |nuFam X χ τ'|)]
  refine hmain.trans ?_
  have h1 := hsep τ
  have h2 := hsep τ'
  calc Bfam Qn X τ * Bfam Qn X τ'
      ≤ (cMu * P.Q * envSep P τ) * (cMu * P.Q * envSep P τ') :=
        mul_le_mul h1 h2 (hB0 τ') ((hB0 τ).trans h1)
    _ = (cMu * P.Q) ^ 2 * (envSep P τ * envSep P τ') := by ring

/-! ## 3. The three "free wins"

An audit of [R] found that its cap-free work **stops at the majorant level**: there
is no cap-free `|𝓔ᵢ| ≤ …` corollary and no cap-free `lem_ends_nu_W` anywhere in the tree
Each of the three below is a short composition of pieces that already exist and are
already cap-free — banked here so that the capped twins are never reached for by accident.

The intended proofs:
  `calE1_bound_L := (abs_calE1_le_maj hνc hF hT).trans (calE1_maj_bound_L cϱ …)`
  `calE2_bound_L := (abs_calE2_le_maj hνc hF hν hB0 hT2π).trans (calE2_maj_bound_L cϱ …)`
  `lem_ends_nu_W_L` = mirror `Zeta23/PrimeSideA/Ends.lean:84-113` via
  `Zeta23.PrimeSide.decomp` (`EndsCore.lean:311`), with `p.l·log p.l → (1+log L)(L+l)`.

The only real work is threading the `T₀`s (the two `_L` lemmas' floors are `(2π)²` and
`2πe⁸`; `abs_calE1_le_maj` additionally wants `0 < p.T`, hence the `max` in the witness). -/

/-- **Free win 1** — cap-free `|𝓔₁(ν)| ≤ C·L³B²(L + l)`.  Composition of
`Zeta23.PrimeSide.abs_calE1_le_maj` (`EndsE1.lean:844`) with
`Zeta23.PrimeSide.calE1_maj_bound_L` (`EndsE1.lean:727`); witnesses `C = C1ends cϱ`,
`T₀ = max ((2π)²) 1`.

Paper §8; NOTE_QR §QR.1.
Depends on: `abs_calE1_le_maj`, `calE1_maj_bound_L` — **both cap-free**.
Rule 17: `LocalHypsCoreW` (no `lam_le_one`), no `p.L ≤ 2*p.l`, no `p.lam = lam`.  This is
precisely the statement that `Zeta23.PrimeSide.calE1_bound` (`EndsE1.lean:888`) gets wrong
for us — that one carries `p.L ≤ 2 * p.l`.  DO NOT CITE `calE1_bound`. -/
theorem calE1_bound_L (cϱ : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → Continuous ν → NuBound p B ν →
      |calE1 p F ν| ≤ C * (p.L ^ 3 * B ^ 2 * (p.L + p.l)) := by
  obtain ⟨C, T₀, h⟩ := calE1_maj_bound_L cϱ
  refine ⟨C, max T₀ 1, fun p F B ν hT hF hνc hν => ?_⟩
  have hT0 : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hTpos : 0 < p.T := by linarith [(le_max_right T₀ 1).trans hT]
  exact (abs_calE1_le_maj hνc hF hTpos).trans (h p F B ν hT0 hF hνc hν)

/-- **Free win 2** — cap-free `|𝓔₂(ν)| ≤ C·L³B²(1 + log L)(L + l)`.  Composition of
`Zeta23.PrimeSide.abs_calE2_le_maj` (`EndsE2.lean:84`) with
`Zeta23.PrimeSide.calE2_maj_bound_L` (`EndsE2.lean:353`); witnesses `C = C2ends cϱ`,
`T₀ = 2π·e⁸`.

⚠ **This is where `p.L ≤ B` enters.**  It is passed through verbatim; `S5_LB_le_Bends` is
what discharges it at the paper's parameters, and `naive_Bends_fails` is why the naive
`B := ℒ + C₀` cannot.

Paper §8; NOTE_QR §QR.1.
Depends on: `abs_calE2_le_maj`, `calE2_maj_bound_L` — **both cap-free**.
Rule 17: no `p.L ≤ 2*p.l`, no `p.l ≤ B`, no `p.lam = lam`.  Contrast
`Zeta23.PrimeSide.calE2_bound` (`EndsE2.lean:437`), which carries all three.  DO NOT CITE it. -/
theorem calE2_bound_L (cϱ : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → Continuous ν → NuBound p B ν → p.L ≤ B →
      |calE2 p F ν| ≤ C * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
  obtain ⟨C, T₀, h⟩ := calE2_maj_bound_L cϱ
  refine ⟨C, max T₀ (2 * Real.pi), fun p F B ν hT hF hνc hν hBL => ?_⟩
  have hT0 : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hT2π : 2 * Real.pi ≤ p.T := (le_max_right _ _).trans hT
  have hB0 : 0 ≤ B := le_trans hF.L_pos.le hBL
  exact (abs_calE2_le_maj hνc hF hν hB0 hT2π).trans (h p F B ν hT0 hF hνc hν hBL)

/-- **Free win 3** — the cap-free twin of `Zeta23.PrimeSide.lem_ends_nu_W`
(`Zeta23/PrimeSideA/Ends.lean:64`): `[lem:ends]` in ν-generic, window-generic, **cap-free**
form.  `|L⁻²Σ_{k,l<d}G_{kl}(ν)² − 𝓜(ν)| ≤ C·L(L + l)(1 + log L)B²`, via
`Zeta23.PrimeSide.decomp` (`EndsCore.lean:311`) plus the two free wins above, divided by
`L²` (`L³/L² = L`; `p.l·log p.l` of the capped form becomes `(1 + log L)(L + l)`).

Does not exist in [R]'s tree — the cap-free work stops at the majorant level.

Paper §8; one of the "free wins". Depends on: `decomp`, `calE1_bound_L`, `calE2_bound_L`.
Rule 17: `lem_ends_nu_W` carries `p.lam = lam` AND `p.L ≤ 2 * p.l` AND `p.l ≤ B`;
`lem_ends_nu` additionally goes through `LocalHypsCore` (hence `lam_le_one`), and `lem_ends`
takes `hlam : 0 < lam ∧ lam ≤ 1` outright.  **None of the three may be cited here.** -/
theorem lem_ends_nu_W_L (cϱ : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → Continuous ν → NuBound p B ν → p.L ≤ B →
      |(p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F|
        ≤ C * (p.L * (p.L + p.l) * (1 + Real.log p.L) * B ^ 2) := by
  obtain ⟨C₁, T₁, h1⟩ := calE1_bound_L cϱ
  obtain ⟨C₂, T₂, h2⟩ := calE2_bound_L cϱ
  refine ⟨|C₁| + |C₂|, max (max T₁ T₂) (2 * Real.pi),
    fun p F B ν hT hF hνc hν hBL => ?_⟩
  have hT1 : T₁ ≤ p.T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ p.T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT' : 2 * Real.pi ≤ p.T := le_trans (le_max_right _ _) hT
  have hL := hF.L_pos
  have hl1 : (1 : ℝ) ≤ p.l := hF.one_le_l
  have hL8 : (8 : ℝ) ≤ p.L := hF.eight_le_L
  have hB0 : 0 ≤ B := le_trans hL.le hBL
  -- `log L ≥ 0` because `L ≥ 8 ≥ 1`.
  have hlogL : (0 : ℝ) ≤ Real.log p.L := Real.log_nonneg (by linarith)
  have e1 := h1 p F B ν hT1 hF hνc hν
  have e2 := h2 p F B ν hT2 hF hνc hν hBL
  have hdec := decomp hνc hF hν hB0 hT'
  have hkey : (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2
        - MtotalNu ν p F
      = (p.L)⁻¹ ^ 2 * (calE1 p F ν + calE2 p F ν) := by
    rw [← hdec]
    field_simp
  rw [hkey, abs_mul, abs_of_pos (by positivity)]
  have hbase : (0 : ℝ) ≤ p.L ^ 3 * B ^ 2 * (p.L + p.l) := by positivity
  have hsum : |calE1 p F ν + calE2 p F ν|
      ≤ (|C₁| + |C₂|) * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
    have s1 : |calE1 p F ν|
        ≤ |C₁| * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
      refine e1.trans ?_
      calc C₁ * (p.L ^ 3 * B ^ 2 * (p.L + p.l))
          ≤ |C₁| * (p.L ^ 3 * B ^ 2 * (p.L + p.l)) := by
            exact mul_le_mul_of_nonneg_right (le_abs_self C₁) hbase
        _ = |C₁| * (p.L ^ 3 * B ^ 2 * 1 * (p.L + p.l)) := by ring
        _ ≤ |C₁| * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
            have h1 : (1 : ℝ) ≤ 1 + Real.log p.L := by linarith
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ p.L ^ 3 * B ^ 2))
                (by positivity : (0:ℝ) ≤ p.L + p.l))
              (abs_nonneg C₁)
    have s2 : |calE2 p F ν|
        ≤ |C₂| * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
      refine e2.trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) (by positivity))
    calc |calE1 p F ν + calE2 p F ν| ≤ |calE1 p F ν| + |calE2 p F ν| := abs_add_le _ _
      _ ≤ _ := by linarith
  calc (p.L)⁻¹ ^ 2 * |calE1 p F ν + calE2 p F ν|
      ≤ (p.L)⁻¹ ^ 2
          * ((|C₁| + |C₂|) * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l))) := by
        gcongr
    _ = (|C₁| + |C₂|) * (p.L * (p.L + p.l) * (1 + Real.log p.L) * B ^ 2) := by
        field_simp

/-! ## 4. Lemma 8.2 — the bilinear ends bound

Paper §8.

    **Lemma 8.2 (bilinear ends bound).**  Σ_χ (𝓔₁ + 𝓔₂)(ν_χ) ≤ ∬ W(τ, τ′) B_fam(τ)B_fam(τ′),
    with W the ν-free majorant kernels of [R] — quoting the CAP-FREE L-intrinsic constants
    (|𝓔₁| ≤ 4(90 + 32c_ϱ²)·L³B²·(L + l);  |𝓔₂| ≤ C₂′·L³B²·(1 + log L)(L + l)), because the
    capped forms' hypothesis L ≤ 2l — innocuous in the T-aspect, where L = λl — FAILS here
    by a factor 10–60.  Family relative order: **Θ(ℒ log ℒ/T)**; budget row 6ℒ log ℒ/T,
    0.4 % of the budget — nothing downstream moves.  The hat-normalization bookkeeping
    reproduces the record's λ ≤ 1 ends wall exactly in the T-aspect (consistency anchor).

**The paper's `W(τ,τ′)` is precisely, and only, [R]'s two majorant kernels:**
  * `W₁ = L²·(ρ(τ)/g(τ)·g(τ′) + g(τ)·ρ(τ′)/g(τ′))` on `sqI p = I ×ˢ I`, inside
    `Zeta23.PrimeSide.majK1` (`EndsE1.lean:194-196`);
  * `W₂ = L²·Σ_{k<d} ψ(τ−τ_k)ψ(τ′−τ_k)` on `(sqI p)ᶜ`, inside
    `Zeta23.PrimeSide.majK2` (`EndsE2.lean:52-54`).
Both are nonnegative (`rho_nonneg`, `gwt_pos`, `psiA_nonneg_of`) and both factor the
ν-dependence as **exactly `|ν(τ)|·|ν(τ′)|`**.  That factorisation is the whole seam: it is
what lets the family sum pass by Cauchy–Schwarz *pointwise in (τ, τ′)*, and it is why
LEMMA_QE's R5 header is right that this is an INSTANTIATION and not a re-derivation (its R4
header's "re-derivation, not an instantiation" is SUPERSEDED — resolution R2).

*Spelling resolutions.*
  * **R6** — the paper writes `Σ_χ (𝓔₁+𝓔₂)(ν_χ) ≤ …` without absolute values, but the 𝓔ᵢ
    are not sign-definite and [R]'s kernels bound `|𝓔ᵢ|`.  Resolved AGAINST the paper's
    display by strengthening to `Σ_χ|𝓔₁| + Σ_χ|𝓔₂|`, which implies it and is what NOTE_QR
    §QR.1's own final form writes.
  * **R7** — the paper writes one `W` and one double integral; in the tree the two kernels
    live on complementary regions, `W₁` depends on `F` (through `ρ`) and `W₂` on `c_ϱ`.
    Resolved as TWO statements, the paper's single display recovered by adding them.
  * **NOTE_QG §g.2** — the ends row is "bounded per block? **NO — family-sum only**".  A
    per-character corollary is not merely weaker, it is FALSE in the needed range (per-block
    `B = l + 4√X` is exactly the defect to avoid).  These statements are about the FAMILY SUM. -/

/-- **The T-dichotomy carried by `LocalHypsCoreW`.**  `hF.one_le_l` says `1 ≤ log(T/2π)`, and
Mathlib's `Real.log` factors through `|·|`, so it pins only `|T| ≥ 2πe` — the sign of `T` is
NOT determined by the taper bundle (no field of `LocalHypsCoreW` mentions `p.T` except
`poisson`, through `p.tau`).  Every statement of §8 that has no `T`-floor of its own is
therefore proved by this two-way split: on the right branch `T ≥ 2πe` (so `2π ≤ T`, which is
what [R]'s integrability lemmas want), and on the left branch `T < 0`, where `I = [T,2T]` is
EMPTY and `p.d = ⌊LT/2π⌋₊ = 0`, so both sides of every §8 inequality collapse to `0`.

Rule 17: a consequence of `one_le_l` alone — a LOWER bound on `T`. -/
theorem T_ge_or_neg {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHypsCoreW cϱ p F) :
    2 * Real.pi * Real.exp 1 ≤ p.T ∨ p.T < 0 := by
  have h1 : (1 : ℝ) ≤ Real.log (p.T / (2 * Real.pi)) := hF.one_le_l
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- `Real.log` sees only `|·|`, so `1 ≤ log(T/2π)` gives `e ≤ |T|/(2π)`.
  have habs : Real.exp 1 ≤ |p.T / (2 * Real.pi)| := by
    have hne : p.T / (2 * Real.pi) ≠ 0 := by
      intro h; rw [h] at h1; simp at h1; linarith [Real.exp_pos (1:ℝ), h1]
    have hpos : (0 : ℝ) < |p.T / (2 * Real.pi)| := abs_pos.mpr hne
    rw [← Real.log_abs] at h1
    exact (Real.le_log_iff_exp_le hpos).mp h1
  have habs' : 2 * Real.pi * Real.exp 1 ≤ |p.T| := by
    rw [abs_div, abs_of_pos hpi] at habs
    rw [le_div_iff₀ hpi] at habs
    linarith
  by_cases h : (0 : ℝ) ≤ p.T
  · left; rw [abs_of_nonneg h] at habs'; exact habs'
  · right; exact not_le.mp h

/-- **`I × I` is empty on the degenerate branch of `T_ge_or_neg`.** -/
theorem sqI_eq_empty {p : Setting} (hT : p.T < 0) : sqI p = ∅ := by
  have h : ¬ (p.T ≤ 2 * p.T) := not_le.mpr (by linarith)
  have hI : p.I = (∅ : Set ℝ) := Set.Icc_eq_empty h
  show p.I ×ˢ p.I = ∅
  rw [hI, Set.empty_prod]

/-- **The grid is empty on the degenerate branch of `T_ge_or_neg`**: `d = ⌊LT/2π⌋₊ = 0` when
`T < 0 < L`, so `majK2` — whose whole `τ`-dependence is a sum over `Finset.range p.d` —
vanishes identically. -/
theorem d_eq_zero {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHypsCoreW cϱ p F)
    (hT : p.T < 0) : p.d = 0 := by
  have hL : 0 < p.L := hF.L_pos
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have : p.L * p.T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hL hT) hpi
  exact Nat.floor_eq_zero.mpr (by linarith)

/-- **Integrability of the 𝓔₁ majorant kernel on the compact square `I × I`.**
[R] re-derives this inline three times (`EndsE1.lean:676`, `:787`, `:875`) and never names
it; §8's family pass needs it as a hypothesis of `setIntegral_mono_on`, so it is extracted
here.  The proof is [R]'s own, verbatim.

Rule 17: `LocalHypsCoreW` is the cap-free bundle; no `T`-floor at all
(`gwt_pos` is conditional on membership in `I`, which is all the compact square supplies). -/
theorem majK1_integrableOn {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ}
    (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) :
    IntegrableOn (majK1 p F ν) (sqI p) := by
  have hcpt : IsCompact (sqI p) := isCompact_sqI
  have hρc : Continuous (rho p F) := by
    have := hF.phiHat_cont; unfold rho; fun_prop
  have hgc : ContinuousOn (gwt p) (Set.Icc p.T (2 * p.T)) := by
    unfold gwt
    refine ContinuousOn.inv₀ (by unfold distB; fun_prop) fun τ hτ => ?_
    have := distB_nonneg (p := p) hτ; positivity
  have hρg : ContinuousOn (fun τ => rho p F τ / gwt p τ) (Set.Icc p.T (2 * p.T)) :=
    hρc.continuousOn.div hgc fun τ hτ => (gwt_pos hτ).ne'
  have hfst : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.1) (sqI p) := fun hf =>
    hf.comp continuous_fst.continuousOn fun q hq => hq.1
  have hsnd : ∀ {f : ℝ → ℝ}, ContinuousOn f (Set.Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.2) (sqI p) := fun hf =>
    hf.comp continuous_snd.continuousOn fun q hq => hq.2
  have hνa : ContinuousOn (fun τ => |ν τ|) (Set.Icc p.T (2 * p.T)) := hνc.abs.continuousOn
  have hM1c : ContinuousOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    (hfst hρg).mul (hsnd hgc)
  have hM2c : ContinuousOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    (hfst hgc).mul (hsnd hρg)
  have hc : ContinuousOn (majK1 p F ν) (sqI p) := by
    have := ((hM1c.add hM2c).const_smul (p.L ^ 2)).mul ((hfst hνa).mul (hsnd hνa))
    refine this.congr fun q hq => ?_
    simp only [majK1, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  exact hc.integrableOn_compact hcpt

/-- The family sum flattened to a single `Finset`, as in `S6_family_pass`. -/
theorem famSum_eq_sigma (Qn : ℕ) (f : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    famSum Qn f
      = ∑ x ∈ (Finset.Icc 1 Qn).sigma (fun q => primitiveChars q), f x.1 x.2 :=
  Finset.sum_sigma' _ _ _

/-- **Each member of the family is dominated by `B_fam`.**  `ν_χ(τ)² ≤ Σ_{χ′} ν_{χ′}(τ)²`, so
`|ν_χ(τ)| ≤ B_fam(τ)` — the pointwise consequence of the mean square that lets Lemma 8.1′
serve as an *integrability* hypothesis for the individual characters, without ever writing
down a per-character pointwise bound (which is [R]'s `Bconst = l + 4√X`, the λ ≤ 1 wall).

Rule 17: no X on the right beyond `B_fam`'s own argument; no λ, no cap. -/
theorem abs_nuFam_le_Bfam {Qn : ℕ} {X : ℝ} {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hq : q ∈ Finset.Icc 1 Qn) (hχ : χ ∈ primitiveChars q) (τ : ℝ) :
    |nuFam X χ τ| ≤ Bfam Qn X τ := by
  have hinner : nuFam X χ τ ^ 2 ≤ ∑ χ' ∈ primitiveChars q, nuFam X χ' τ ^ 2 :=
    Finset.single_le_sum (f := fun χ' : DirichletCharacter ℂ q => nuFam X χ' τ ^ 2)
      (fun i _ => sq_nonneg _) hχ
  have houter : (∑ χ' ∈ primitiveChars q, nuFam X χ' τ ^ 2) ≤ BfamSq Qn X τ :=
    Finset.single_le_sum
      (f := fun q' : ℕ => ∑ χ' ∈ primitiveChars q', nuFam X χ' τ ^ 2)
      (fun i _ => Finset.sum_nonneg fun χ' _ => sq_nonneg _) hq
  have hle : nuFam X χ τ ^ 2 ≤ BfamSq Qn X τ := hinner.trans houter
  calc |nuFam X χ τ| = Real.sqrt (nuFam X χ τ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (BfamSq Qn X τ) := Real.sqrt_le_sqrt hle
    _ = Bfam Qn X τ := rfl

/-- **Lemma 8.2, step 1 (the bilinear pass, 𝓔₁ half).**
`Σ_χ ∬_{I×I} majK1(ν_χ) ≤ (c_μQ)²·∬_{I×I} majK1(env_sep)`.

Cauchy–Schwarz in χ pointwise in `(τ, τ′)`, BEFORE any τ-integration (`S6_family_pass`),
then `integral_finsetSum` + `setIntegral_mono_on`.  Legitimate because `majK1` is
`W₁(q)·(|ν q.1|·|ν q.2|)` with `W₁ ≥ 0`.

Paper §8; `LEMMA_QE` §QE.ii.
⚠ The only real work is
integrability of `majK1 … ν` on `sqI`: in [R] it is INLINE inside `abs_calE1_le_maj`'s
proof (`EndsE1.lean:857-877`) — **extract it as a named lemma when filling**.
Depends on: `S6_family_pass`, `S3_continuous_envSep`, `S2_localHypsCoreW`.
Rule 17: `LocalHypsCoreW` is the cap-free bundle; `hsep` is Lemma 8.1′ (no X); the
conclusion mentions `p.L, p.l, Q, c_ϱ` and no `X`. -/
theorem sum_majK1_le
    (P : ParamsQ) (Qn : ℕ) (cϱ X : ℝ) (F : LocalFun)
    (hF : LocalHypsCoreW cϱ (toSetting P) F)
    (hν : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (nuFam X χ))
    (hsep : ∀ τ : ℝ, Bfam Qn X τ ≤ cMu * P.Q * envSep P τ) :
    famSum Qn (fun _ χ => ∫ z in sqI (toSetting P), majK1 (toSetting P) F (nuFam X χ) z)
      ≤ (cMu * P.Q) ^ 2 * ∫ z in sqI (toSetting P), majK1 (toSetting P) F (envSep P) z := by
  rcases T_ge_or_neg hF with hT | hT
  · -- **The honest branch**, `T ≥ 2πe > 0`.
    simp only [toSetting_T] at hT
    have hTpos : (0 : ℝ) < P.T := by
      have h1 : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
      linarith
    have hcont : Continuous (envSep P) := S3_continuous_envSep P hTpos
    have hint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        IntegrableOn (majK1 (toSetting P) F (nuFam X χ)) (sqI (toSetting P)) :=
      fun q χ => majK1_integrableOn (hν q χ) hF
    have hinte : IntegrableOn (majK1 (toSetting P) F (envSep P)) (sqI (toSetting P)) :=
      majK1_integrableOn hcont hF
    -- flatten the family double sum to a single index, exactly as in `S6_family_pass`
    set S : Finset ((_ : ℕ) × DirichletCharacter ℂ _) :=
      (Finset.Icc 1 Qn).sigma (fun q => primitiveChars q) with hS
    have hflat : ∀ f : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
        famSum Qn f = ∑ x ∈ S, f x.1 x.2 := fun f => Finset.sum_sigma' _ _ _
    -- the family sum passes inside the double integral (finitely many terms, each integrable)
    have hL : famSum Qn
          (fun _ χ => ∫ z in sqI (toSetting P), majK1 (toSetting P) F (nuFam X χ) z)
        = ∫ z in sqI (toSetting P), ∑ x ∈ S, majK1 (toSetting P) F (nuFam X x.2) z := by
      rw [hflat (fun _ χ => ∫ z in sqI (toSetting P), majK1 (toSetting P) F (nuFam X χ) z)]
      exact (integral_finsetSum S (fun x _ => hint x.1 x.2)).symm
    have hR : (cMu * P.Q) ^ 2 * ∫ z in sqI (toSetting P), majK1 (toSetting P) F (envSep P) z
        = ∫ z in sqI (toSetting P), (cMu * P.Q) ^ 2 * majK1 (toSetting P) F (envSep P) z :=
      (integral_const_mul _ _).symm
    rw [hL, hR]
    refine setIntegral_mono_on
      (integrable_finsetSum S (fun x _ => hint x.1 x.2))
      (hinte.const_mul _) measurableSet_sqI ?_
    -- **the seam**: Cauchy–Schwarz in χ, POINTWISE in `(τ, τ′)`, against the nonnegative kernel
    intro z hz
    have hz1 : z.1 ∈ Set.Icc (toSetting P).T (2 * (toSetting P).T) := hz.1
    have hz2 : z.2 ∈ Set.Icc (toSetting P).T (2 * (toSetting P).T) := hz.2
    have hg1 : 0 < gwt (toSetting P) z.1 := gwt_pos hz1
    have hg2 : 0 < gwt (toSetting P) z.2 := gwt_pos hz2
    have hr1 : 0 ≤ rho (toSetting P) F z.1 := rho_nonneg hF z.1
    have hr2 : 0 ≤ rho (toSetting P) F z.2 := rho_nonneg hF z.2
    have hS6 := S6_family_pass P Qn X hsep z.1 z.2
    rw [hflat (fun _ χ => |nuFam X χ z.1| * |nuFam X χ z.2|)] at hS6
    simp only [majK1]
    set W : ℝ := (toSetting P).L ^ 2 *
        (rho (toSetting P) F z.1 / gwt (toSetting P) z.1 * gwt (toSetting P) z.2
          + gwt (toSetting P) z.1 * (rho (toSetting P) F z.2 / gwt (toSetting P) z.2))
      with hWdef
    have hWnn : 0 ≤ W := by
      rw [hWdef]
      refine mul_nonneg (sq_nonneg _) ?_
      have h1 : 0 ≤ rho (toSetting P) F z.1 / gwt (toSetting P) z.1 * gwt (toSetting P) z.2 :=
        mul_nonneg (div_nonneg hr1 hg1.le) hg2.le
      have h2 : 0 ≤ gwt (toSetting P) z.1 * (rho (toSetting P) F z.2 / gwt (toSetting P) z.2) :=
        mul_nonneg hg1.le (div_nonneg hr2 hg2.le)
      linarith
    rw [← Finset.mul_sum]
    have habs : envSep P z.1 * envSep P z.2 ≤ |envSep P z.1| * |envSep P z.2| := by
      rw [← abs_mul]; exact le_abs_self _
    have key : (W * (cMu * P.Q) ^ 2) * (envSep P z.1 * envSep P z.2)
        ≤ (W * (cMu * P.Q) ^ 2) * (|envSep P z.1| * |envSep P z.2|) :=
      mul_le_mul_of_nonneg_left habs (mul_nonneg hWnn (sq_nonneg _))
    have step : W * ∑ x ∈ S, |nuFam X x.2 z.1| * |nuFam X x.2 z.2|
        ≤ W * ((cMu * P.Q) ^ 2 * (envSep P z.1 * envSep P z.2)) :=
      mul_le_mul_of_nonneg_left hS6 hWnn
    nlinarith [step, key]
  · -- **The degenerate branch**, `T < 0`: `I × I = ∅`, so both sides are `0`.
    have hempty : sqI (toSetting P) = ∅ := sqI_eq_empty (by simpa using hT)
    rw [hempty]
    simp [famSum]

/-- **`NuBound` for the separated envelope, with no `P.Valid`.**  `S4_nuBound_envSep` is the
sharp form (`B := B_ends`, coefficient exactly 1 on the `log⁺`) but needs `0 ≤ B_ends`, hence
`P.Valid`.  For *integrability* only the crude `B := max |B_ends| 1` is wanted, and that
holds unconditionally; the `1` is there because [R]'s weighted-integrability lemmas carry
`1 ≤ B`.  Note the coefficient on `log⁺` is still exactly 1 — that is the whole point.

Rule 17: no hypotheses at all. -/
theorem nuBound_envSep_abs (P : ParamsQ) :
    NuBound (toSetting P) (max |Bends P| 1) (envSep P) := by
  intro τ
  have h0 : (0 : ℝ) ≤ logPlusQ P τ := le_max_right _ _
  have hb : |Bends P| ≤ max |Bends P| 1 := le_max_left _ _
  have h1 : |envSep P τ| ≤ |Bends P| + logPlusQ P τ := by
    have := abs_add_le (Bends P) (logPlusQ P τ)
    rwa [abs_of_nonneg h0] at this
  show |envSep P τ| ≤ max |Bends P| 1 + max (Real.log (|τ| / (4 * (toSetting P).T))) 0
  have h2 : max (Real.log (|τ| / (4 * (toSetting P).T))) 0 = logPlusQ P τ := rfl
  rw [h2]; linarith

/-- **Integrability of the 𝓔₂ majorant for ONE family character, from Lemma 8.1′ alone.**

This is the technical heart of the 𝓔₂ half of §8.  [R]'s `majK2_integrable` (and, through it,
`abs_calE2_le_maj`) wants a per-character `NuBound p B ν_χ` — a POINTWISE bound with
coefficient exactly 1 on `log⁺`.  For an individual `ν_{X,χ}` the only such bound in [R] is
`Bconst p = p.l + 4√X`, **the λ ≤ 1 wall**, and §8 must not use it (module header; NOTE_QG
§g.2: a per-block bound "is not merely weaker, it is FALSE in the needed range").

The way out is that integrability needs only *domination*, not a `NuBound`: Lemma 8.1′ gives
`|ν_χ| ≤ B_fam ≤ (c_μQ)·env_sep` (`abs_nuFam_le_Bfam` + `hsep`), and the scalar `c_μQ` — which
is astronomically larger than 1 and therefore CANNOT be folded into a `NuBound` — is harmless
as a multiplicative constant in a domination argument.  The coefficient-1 normalisation is
needed only for the ENVELOPE, where `nuBound_envSep_abs` supplies it.

Rule 17: `2π ≤ T` is a T-floor; `hsep` is Lemma 8.1′ and carries no `X` on its right; no
per-character pointwise bound, hence no `Bconst`, is ever formed. -/
theorem majK2_integrable_fam (P : ParamsQ) (Qn : ℕ) (cϱ X : ℝ) (F : LocalFun)
    (hF : LocalHypsCoreW cϱ (toSetting P) F) (hTπ : 2 * Real.pi ≤ P.T)
    (hν : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (nuFam X χ))
    (hsep : ∀ τ : ℝ, Bfam Qn X τ ≤ cMu * P.Q * envSep P τ)
    {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hq : q ∈ Finset.Icc 1 Qn) (hχ : χ ∈ primitiveChars q) :
    Integrable (majK2 cϱ (toSetting P) (nuFam X χ)) := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hTpos : (0 : ℝ) < P.T := by linarith
  have hT1 : (1 : ℝ) ≤ P.T := by linarith
  have hcont : Continuous (envSep P) := S3_continuous_envSep P hTpos
  have hNB := nuBound_envSep_abs P
  have hB1 : (1 : ℝ) ≤ max |Bends P| 1 := le_max_right _ _
  have hTT1 : (1 : ℝ) ≤ (toSetting P).T := hT1
  have hgrid : ∀ k ∈ Finset.range (toSetting P).d,
      ((toSetting P).tau k : ℝ) ∈ Set.Icc (toSetting P).T (2 * (toSetting P).T) := by
    intro k hk
    have h := Setting.tau_mem (toSetting P) hF.L_pos (by exact hTpos.le) hk
    exact ⟨h.1, h.2⟩
  have hbase : ∀ k ∈ Finset.range (toSetting P).d,
      Integrable (fun τ : ℝ =>
        psiA cϱ (toSetting P) (τ - (toSetting P).tau k) * |envSep P τ|) :=
    fun k hk => integrable_psiA_shift_mul_nu hcont hF hNB hB1 hTT1 (hgrid k hk)
  have hnuB : ∀ τ : ℝ, |nuFam X χ τ| ≤ |cMu * P.Q| * |envSep P τ| := by
    intro τ
    calc |nuFam X χ τ| ≤ Bfam Qn X τ := abs_nuFam_le_Bfam hq hχ τ
      _ ≤ cMu * P.Q * envSep P τ := hsep τ
      _ ≤ |cMu * P.Q * envSep P τ| := le_abs_self _
      _ = |cMu * P.Q| * |envSep P τ| := abs_mul _ _
  have hwk : ∀ k ∈ Finset.range (toSetting P).d,
      Integrable (fun τ : ℝ =>
        psiA cϱ (toSetting P) (τ - (toSetting P).tau k) * |nuFam X χ τ|) := by
    intro k hk
    have hmeas : AEStronglyMeasurable
        (fun τ : ℝ => psiA cϱ (toSetting P) (τ - (toSetting P).tau k) * |nuFam X χ τ|)
        (volume : Measure ℝ) :=
      (psiA_shift_integrable hF _).aestronglyMeasurable.mul (hν q χ).abs.aestronglyMeasurable
    refine ((hbase k hk).const_mul |cMu * P.Q|).mono' hmeas ?_
    filter_upwards with τ
    have hψ : 0 ≤ psiA cϱ (toSetting P) (τ - (toSetting P).tau k) := psiA_nonneg_of hF _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hψ (abs_nonneg _))]
    calc psiA cϱ (toSetting P) (τ - (toSetting P).tau k) * |nuFam X χ τ|
        ≤ psiA cϱ (toSetting P) (τ - (toSetting P).tau k) * (|cMu * P.Q| * |envSep P τ|) :=
          mul_le_mul_of_nonneg_left (hnuB τ) hψ
      _ = |cMu * P.Q|
            * (psiA cϱ (toSetting P) (τ - (toSetting P).tau k) * |envSep P τ|) := by ring
  have h : Integrable (fun z : ℝ × ℝ => ∑ k ∈ Finset.range (toSetting P).d,
      ((toSetting P).L ^ 2
          * (psiA cϱ (toSetting P) (z.1 - (toSetting P).tau k) * |nuFam X χ z.1|))
        * (psiA cϱ (toSetting P) (z.2 - (toSetting P).tau k) * |nuFam X χ z.2|)) := by
    refine integrable_finsetSum _ fun k hk => ?_
    exact ((hwk k hk).const_mul ((toSetting P).L ^ 2)).mul_prod (hwk k hk)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [majK2]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **`abs_calE2_le_maj` with the `NuBound` replaced by plain integrability of the majorant.**
[R]'s version (`EndsE2.lean:84`) takes `NuBound p B ν` and uses it only to produce
`majK2_integrable`; the pointwise step `|trG2integrand| ≤ majK2` is `LocalHypsCoreW`-only.
For the family characters the `NuBound` is unavailable (see `majK2_integrable_fam`), so the
hypothesis is taken in the form actually used.  **Proof is [R]'s own with `hν`, `hB0`, `hT`
deleted.**

Rule 17: strictly weaker hypotheses than [R]'s; no cap of any kind. -/
theorem abs_calE2_le_maj_of_integrable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ}
    (hF : LocalHypsCoreW cϱ p F) (hint : Integrable (majK2 cϱ p ν)) :
    |calE2 p F ν| ≤ ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q := by
  unfold calE2
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
    hint.integrableOn (Filter.Eventually.of_forall fun q => ?_)
  show ‖trG2integrand p F ν q‖ ≤ _
  rw [Real.norm_eq_abs]
  exact abs_trG2integrand_le_majK2 hF q

/-- Monotonicity of the family sum, with the family membership available. -/
theorem famSum_mono {Qn : ℕ} {f g : (q : ℕ) → DirichletCharacter ℂ q → ℝ}
    (h : ∀ q ∈ Finset.Icc 1 Qn, ∀ χ ∈ primitiveChars q, f q χ ≤ g q χ) :
    famSum Qn f ≤ famSum Qn g :=
  Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => h q hq χ hχ

/-- **Lemma 8.2, step 1 (the bilinear pass, 𝓔₂ half).**
`Σ_χ ∬_{(I×I)ᶜ} majK2(ν_χ) ≤ (c_μQ)²·∬_{(I×I)ᶜ} majK2(env_sep)`.

Same argument; here the integrability is already a named lemma in the tree
(`Zeta23.PrimeSide.majK2_integrable`, `EndsE2.lean:60`).

Paper §8; `LEMMA_QE` §QE.ii.
Depends on: `S6_family_pass`, `majK2_integrable`.
Rule 17: as `sum_majK1_le`. -/
theorem sum_majK2_le
    (P : ParamsQ) (Qn : ℕ) (cϱ X : ℝ) (F : LocalFun)
    (hF : LocalHypsCoreW cϱ (toSetting P) F)
    (hν : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (nuFam X χ))
    (hsep : ∀ τ : ℝ, Bfam Qn X τ ≤ cMu * P.Q * envSep P τ) :
    famSum Qn (fun _ χ => ∫ z in (sqI (toSetting P))ᶜ, majK2 cϱ (toSetting P) (nuFam X χ) z)
      ≤ (cMu * P.Q) ^ 2 * ∫ z in (sqI (toSetting P))ᶜ, majK2 cϱ (toSetting P) (envSep P) z := by
  rcases T_ge_or_neg hF with hT | hT
  · -- **The honest branch**, `T ≥ 2πe`, which supplies [R]'s own floor `2π ≤ T`.
    simp only [toSetting_T] at hT
    have hexp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hT2π : 2 * Real.pi ≤ P.T := by nlinarith
    have hTpos : (0 : ℝ) < P.T := by linarith
    have hcont : Continuous (envSep P) := S3_continuous_envSep P hTpos
    have hNB := nuBound_envSep_abs P
    have hB1 : (1 : ℝ) ≤ max |Bends P| 1 := le_max_right _ _
    have hTT2π : 2 * Real.pi ≤ (toSetting P).T := hT2π
    set S : Finset ((_ : ℕ) × DirichletCharacter ℂ _) :=
      (Finset.Icc 1 Qn).sigma (fun q => primitiveChars q) with hS
    have hflat : ∀ f : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
        famSum Qn f = ∑ x ∈ S, f x.1 x.2 := fun f => Finset.sum_sigma' _ _ _
    have hMint : ∀ x ∈ S, Integrable (majK2 cϱ (toSetting P) (nuFam X x.2)) := by
      intro x hx
      rw [hS, Finset.mem_sigma] at hx
      exact majK2_integrable_fam P Qn cϱ X F hF hT2π hν hsep hx.1 hx.2
    have hMinte : Integrable (majK2 cϱ (toSetting P) (envSep P)) :=
      majK2_integrable hcont hF hNB (by linarith) hTT2π
    -- the family sum passes inside the double integral
    have hL : famSum Qn
          (fun _ χ => ∫ z in (sqI (toSetting P))ᶜ, majK2 cϱ (toSetting P) (nuFam X χ) z)
        = ∫ z in (sqI (toSetting P))ᶜ,
            ∑ x ∈ S, majK2 cϱ (toSetting P) (nuFam X x.2) z := by
      rw [hflat (fun _ χ => ∫ z in (sqI (toSetting P))ᶜ, majK2 cϱ (toSetting P) (nuFam X χ) z)]
      exact (integral_finsetSum S (fun x hx => (hMint x hx).integrableOn)).symm
    have hR : (cMu * P.Q) ^ 2
          * ∫ z in (sqI (toSetting P))ᶜ, majK2 cϱ (toSetting P) (envSep P) z
        = ∫ z in (sqI (toSetting P))ᶜ,
            (cMu * P.Q) ^ 2 * majK2 cϱ (toSetting P) (envSep P) z :=
      (integral_const_mul _ _).symm
    rw [hL, hR]
    refine setIntegral_mono_on
      (integrable_finsetSum S (fun x hx => (hMint x hx).integrableOn))
      (hMinte.integrableOn.const_mul _) measurableSet_sqI.compl ?_
    -- **the seam**: Cauchy–Schwarz in χ, POINTWISE in `(τ, τ′)`, against the nonneg ψ-kernel
    intro z _
    have hS6 := S6_family_pass P Qn X hsep z.1 z.2
    rw [hflat (fun _ χ => |nuFam X χ z.1| * |nuFam X χ z.2|)] at hS6
    simp only [majK2]
    set W : ℝ := (toSetting P).L ^ 2 *
        ∑ k ∈ Finset.range (toSetting P).d,
          psiA cϱ (toSetting P) (z.1 - (toSetting P).tau k)
            * psiA cϱ (toSetting P) (z.2 - (toSetting P).tau k) with hWdef
    have hWnn : 0 ≤ W :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ =>
        mul_nonneg (psiA_nonneg_of hF _) (psiA_nonneg_of hF _))
    rw [← Finset.mul_sum]
    have habs : envSep P z.1 * envSep P z.2 ≤ |envSep P z.1| * |envSep P z.2| := by
      rw [← abs_mul]; exact le_abs_self _
    have key : (W * (cMu * P.Q) ^ 2) * (envSep P z.1 * envSep P z.2)
        ≤ (W * (cMu * P.Q) ^ 2) * (|envSep P z.1| * |envSep P z.2|) :=
      mul_le_mul_of_nonneg_left habs (mul_nonneg hWnn (sq_nonneg _))
    have step : W * ∑ x ∈ S, |nuFam X x.2 z.1| * |nuFam X x.2 z.2|
        ≤ W * ((cMu * P.Q) ^ 2 * (envSep P z.1 * envSep P z.2)) :=
      mul_le_mul_of_nonneg_left hS6 hWnn
    nlinarith [step, key]
  · -- **The degenerate branch**, `T < 0`: `d = ⌊LT/2π⌋₊ = 0`, so `majK2 ≡ 0` on both sides.
    have hd : (toSetting P).d = 0 := d_eq_zero hF (by simpa using hT)
    have hzero : ∀ ν : ℝ → ℝ, majK2 cϱ (toSetting P) ν = fun _ => 0 := by
      intro ν; funext z; simp [majK2, hd]
    simp only [hzero]
    simp [famSum]

section ExplicitConstants
open Real Set

/-- **`calE1_maj_bound_L` with its witness constant made visible.**

[R] states `calE1_maj_bound_L` (`EndsE1.lean:727`) as `∃ C T₀, …`, so the constant
`4(90 + 32c_ϱ²)` that its own `refine` supplies is invisible to a consumer.  Paper §8's
Lemma 8.2 names that constant (`C1ends`), so the bound is restated here with the witness IN
the statement.  **The proof below is [R]'s own, verbatim** — no hypothesis is added, and the
only lemmas cited are the cap-free ones the original cites (`setIntegral_gwt_le`,
`setIntegral_rho_div_gwt_le`, `majK1_le`, `abs_nuX_le_B_onI`, all `LocalHypsCoreW`-gated).

Without this restatement `ends_family_bound` is NOT derivable: its conclusion names
`C1ends cϱ` and `C2ends cϱ`, while [R] exposes only `∃ C`.

Rule 17: `T₀ = (2π)²` is a T-floor; `LocalHypsCoreW` is cap-free; there is
no `p.L ≤ 2*p.l` and no `p.lam = lam`. -/
theorem majK1_integral_le {cϱ : ℝ} (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ)
    (hT : (2 * Real.pi) ^ 2 ≤ p.T) (hF : LocalHypsCoreW cϱ p F) (hνc : Continuous ν)
    (hν : NuBound p B ν) :
    ∫ q in sqI p, majK1 p F ν q ≤ C1ends cϱ * (p.L ^ 3 * B ^ 2 * (p.L + p.l)) := by
  unfold C1ends
  -- regime
  have hπ := Real.pi_gt_three
  have hT1 : (1:ℝ) ≤ p.T := by nlinarith
  have hT0 : (0:ℝ) < p.T := by linarith
  have hL8 := hF.eight_le_L
  have hL0 := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hw1 := hF.one_le_w
  have hl1 : (1:ℝ) ≤ p.l := hF.one_le_l
  have hlogT : Real.log p.T ≤ 2 * p.l := by
    -- log T = l + log(2π) and log(2π) ≤ l since T ≥ (2π)²
    have e : Real.log p.T = p.l + Real.log (2 * π) := by
      show Real.log p.T = Real.log (p.T / (2 * π)) + Real.log (2 * π)
      rw [Real.log_div (by linarith) (by positivity)]; ring
    have h2 : Real.log (2 * π) ≤ p.l := by
      show Real.log (2 * π) ≤ Real.log (p.T / (2 * π))
      apply Real.log_le_log (by positivity)
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hB0 : 0 ≤ B := by
    have := abs_nuX_le_B_onI hν hT0 (τ := p.T) ⟨le_rfl, by linarith⟩
    exact le_trans (abs_nonneg _) this
  -- the two 1-D integrals
  have hIg := setIntegral_gwt_le (p := p) hT0
  have hR := setIntegral_rho_div_gwt_le hF hν hT1
  set R := ∫ τ in Icc p.T (2 * p.T), rho p F τ / gwt p τ with hRdef
  set G := ∫ τ in Icc p.T (2 * p.T), gwt p τ with hGdef
  have hG0 : 0 ≤ G := setIntegral_nonneg measurableSet_Icc fun τ hτ => (gwt_pos hτ).le
  have hR0 : 0 ≤ R := setIntegral_nonneg measurableSet_Icc fun τ hτ =>
    div_nonneg (rho_nonneg hF τ) (gwt_pos hτ).le
  -- continuity / integrability on the compact square
  have hρc : Continuous (rho p F) := by
    have := hF.phiHat_cont; unfold rho; fun_prop
  have hdistc : Continuous (distB p) := by unfold distB; fun_prop
  have hgc : ContinuousOn (gwt p) (Icc p.T (2 * p.T)) := by
    unfold gwt
    refine ContinuousOn.inv₀ (by fun_prop) fun τ hτ => ?_
    have := distB_nonneg (p := p) hτ; positivity
  have hρg : ContinuousOn (fun τ => rho p F τ / gwt p τ) (Icc p.T (2 * p.T)) :=
    hρc.continuousOn.div hgc fun τ hτ => (gwt_pos hτ).ne'
  have hfst : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.1) (sqI p) := fun hf =>
    hf.comp continuous_fst.continuousOn fun q hq => hq.1
  have hsnd : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.2) (sqI p) := fun hf =>
    hf.comp continuous_snd.continuousOn fun q hq => hq.2
  have hM1c : ContinuousOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    (hfst hρg).mul (hsnd hgc)
  have hM2c : ContinuousOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    (hfst hgc).mul (hsnd hρg)
  have hcpt : IsCompact (sqI p) := isCompact_sqI
  have hM1i : IntegrableOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    hM1c.integrableOn_compact hcpt
  have hM2i : IntegrableOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    hM2c.integrableOn_compact hcpt
  have hfi : IntegrableOn (majK1 p F ν) (sqI p) := by
    have hνa : ContinuousOn (fun τ => |ν τ|) (Icc p.T (2 * p.T)) := hνc.abs.continuousOn
    have hc : ContinuousOn (majK1 p F ν) (sqI p) := by
      have := ((hM1c.add hM2c).const_smul (p.L ^ 2)).mul ((hfst hνa).mul (hsnd hνa))
      refine this.congr fun q hq => ?_
      simp only [majK1, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
    exact hc.integrableOn_compact hcpt
  -- ∫_{sqI} majK1 ≤ L²B²(RG + GR)
  have hmain : ∫ q in sqI p, majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 * (R * G + G * R) := by
    have step2 : ∫ q in sqI p, majK1 p F ν q
        ≤ ∫ q in sqI p, p.L ^ 2 * B ^ 2 *
          (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2)) := by
      refine setIntegral_mono_on hfi ((hM1i.add hM2i).const_mul _) measurableSet_sqI
        fun q hq => majK1_le hF hν hT0 hq
    have step3 : ∫ q in sqI p, p.L ^ 2 * B ^ 2 *
          (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2))
        = p.L ^ 2 * B ^ 2 * (R * G + G * R) := by
      rw [integral_const_mul, integral_add hM1i hM2i]
      congr 1
      unfold sqI
      rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun τ => rho p F τ / gwt p τ) (gwt p),
        setIntegral_prod_mul (gwt p) (fun τ => rho p F τ / gwt p τ)]
      rfl
    linarith
  -- numerics
  have hcw : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
    have : cϱ / p.w ≤ cϱ := div_le_self (by linarith) hw1
    have : 0 ≤ cϱ / p.w := by positivity
    nlinarith
  have hh : (p.h)⁻¹ = p.L / (2 * π) := by unfold Setting.h; rw [inv_div]
  have hhL : (p.h)⁻¹ ≤ p.L := by
    rw [hh, div_le_iff₀ (by positivity)]; nlinarith
  have hRle : R ≤ (90 + 32 * cϱ ^ 2) * (p.L * (p.L + p.l)) := by
    have hlog0 : 0 ≤ Real.log p.T := Real.log_nonneg hT1
    have h1 : (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T)
        ≤ p.L * (32 * p.L + 4 / 3 * cϱ ^ 2 * (2 * p.l)) := by
      apply mul_le_mul hhL _ (by positivity) hL0.le
      gcongr
    set M := p.L * (p.L + p.l) with hM
    have hLL : p.L ^ 2 ≤ M := by rw [hM]; nlinarith
    have hLl' : p.L * p.l ≤ M := by rw [hM]; nlinarith
    have hM1 : 1 ≤ M := by rw [hM]; nlinarith
    have hc2 : cϱ ^ 2 ≤ cϱ ^ 2 * M := by nlinarith [sq_nonneg cϱ]
    have hc3 : cϱ ^ 2 * (p.L * p.l) ≤ cϱ ^ 2 * M := mul_le_mul_of_nonneg_left hLl' (sq_nonneg _)
    nlinarith
  calc ∫ q in sqI p, majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 * (R * G + G * R) := hmain
    _ = 2 * (p.L ^ 2 * B ^ 2) * (R * G) := by ring
    _ ≤ 2 * (p.L ^ 2 * B ^ 2) * ((90 + 32 * cϱ ^ 2) * (p.L * (p.L + p.l)) * 2) := by
        gcongr
    _ = 4 * (90 + 32 * cϱ ^ 2) * (p.L ^ 3 * B ^ 2 * (p.L + p.l)) := by ring

/-- **`calE2_maj_bound_L` with its witness constant made visible.**  Same reasoning as
`majK1_integral_le`: [R]'s statement (`EndsE2.lean:353`) hides
`2(8 + 4·max(0, log c_ϱ) + 7c_ϱ)·CN2(c_ϱ)` behind an existential, and paper §8 names it
(`C2ends`).  **The proof is [R]'s own, verbatim.**

⚠ This is where the absorbing hypothesis `p.L ≤ B` enters.  It is discharged at the paper's
parameters by `S5_LB_le_Bends`, and is NOT dischargeable at the paper's displayed
normalisation `B := ℒ + C₀` — that is `naive_Bends_fails`.

Rule 17: `T₀ = 2πe⁸` is a T-floor; no `p.L ≤ 2*p.l`, no `p.l ≤ B`. -/
theorem majK2_integral_le {cϱ : ℝ} (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ)
    (hT : 2 * Real.pi * Real.exp 8 ≤ p.T) (hF : LocalHypsCoreW cϱ p F) (hνc : Continuous ν)
    (hν : NuBound p B ν) (hBL : p.L ≤ B) :
    ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q
      ≤ C2ends cϱ * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
  unfold C2ends
  -- regime
  have hπ3 := Real.pi_gt_three
  have he8 : (1 : ℝ) ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  have hT8 : 2 * π * Real.exp 8 ≤ p.T := hT
  have hT1 : (1 : ℝ) ≤ p.T := by nlinarith
  have hT0 : (0 : ℝ) < p.T := by linarith
  have hT2π : 2 * π ≤ p.T := by nlinarith
  have hl8 : (8 : ℝ) ≤ p.l := Setting.le_l_of_T hT8
  have hl1 : (1 : ℝ) ≤ p.l := by linarith
  have hlogl2 : (2 : ℝ) ≤ Real.log p.l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 8 := by norm_num
      _ ≤ p.l := hl8
  have hL8 : (8 : ℝ) ≤ p.L := hF.eight_le_L
  have hL0 : (0 : ℝ) < p.L := by linarith
  have hlogL0 : (0 : ℝ) ≤ Real.log p.L := Real.log_nonneg (by linarith)
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hw1 : (1 : ℝ) ≤ p.w := hF.one_le_w
  have hc4 : (4 : ℝ) ≤ cϱ := hF.four_le_cϱ
  have hm0 : (0 : ℝ) ≤ max 0 (Real.log cϱ) := le_max_left _ _
  have hlogl0 : (0 : ℝ) < Real.log p.l := by linarith
  -- fold the N1 constant into log L
  have hlogbound : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.L := by
    calc Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ * p.L) := by
          apply Real.log_le_log (by positivity)
          apply div_le_self (by positivity)
          linarith
      _ = Real.log cϱ + Real.log p.L := Real.log_mul (by positivity) (by positivity)
      _ ≤ max 0 (Real.log cϱ) + Real.log p.L := by
          have := le_max_right (0 : ℝ) (Real.log cϱ)
          linarith
  set M1 : ℝ := (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B with hM1
  have hM1nn : 0 ≤ M1 := by
    rw [hM1]
    have hwle := hF.w_le
    have hlog4w : (0:ℝ) ≤ Real.log (cϱ * p.L / (4 * p.w)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    positivity
  have hM1fold : M1 ≤ ((8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * (1 + Real.log p.L)) * B := by
    rw [hM1]
    have key : 2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ
        ≤ (8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * (1 + Real.log p.L) := by
      have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.L := hlogbound
      nlinarith [mul_nonneg hm0 hlogL0, mul_nonneg (by linarith : (0:ℝ) ≤ cϱ) hlogL0]
    exact mul_le_mul_of_nonneg_right key hB0
  -- the 1-D estimates
  have hN1 : ∀ a ∈ Icc p.T (2 * p.T),
      ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ| ≤ M1 :=
    fun a ha => nu_weight_bound_L hνc hF hν hBL hT1 ha
  have hN2 := nu_grid_bound_L hνc hF hν hBL hT8
  have htotal := setIntegral_compl_sqI_majK2_le hνc hF hν hB1 hT1 hM1nn hN1 hN2
  refine htotal.trans ?_
  have hc60 : (0:ℝ) ≤ CN2 cϱ := CN2_nonneg cϱ
  have hLl0 : 0 ≤ p.L + p.l := by linarith
  have hstep : M1 * (CN2 cϱ * (B * (p.L * (p.L + p.l))))
      ≤ (((8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * (1 + Real.log p.L)) * B)
        * (CN2 cϱ * (B * (p.L * (p.L + p.l)))) := by
    exact mul_le_mul_of_nonneg_right hM1fold (mul_nonneg hc60 (by positivity))
  calc 2 * (p.L ^ 2 * M1 * (CN2 cϱ * (B * (p.L * (p.L + p.l)))))
      = 2 * p.L ^ 2 * (M1 * (CN2 cϱ * (B * (p.L * (p.L + p.l))))) := by
        ring
    _ ≤ 2 * p.L ^ 2 * ((((8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * (1 + Real.log p.L)) * B)
        * (CN2 cϱ * (B * (p.L * (p.L + p.l))))) := by
        refine mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 2 * (8 + 4 * max 0 (Real.log cϱ) + 7 * cϱ) * CN2 cϱ
        * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) := by
        ring

end ExplicitConstants

/-- **Lemma 8.2 (bilinear ends bound), closed form** — NOTE_QR §QR.1's display:

    Σ_χ|𝓔₁(ν_χ)| + Σ_χ|𝓔₂(ν_χ)|
      ≤ (c₁Q)²·L³(L + l)·(ℒ + C₀)²·[4(90 + 32c_ϱ²) + C₂′·(1 + log L)]

with `l = log(T/2π) = (3+ε) log ℒ` and `c_ϱ = 4‖ϱ₂′‖_∞ + 4‖ϱ₂″‖₁` (finite, [R]'s own,
constrained only by `hF.four_le_cϱ : 4 ≤ c_ϱ`).

**Route: instantiate, do not derive.**  `sum_majK1_le`/`sum_majK2_le` push the family sum
inside; then [R]'s CAP-FREE `_L` majorant bounds are applied at `ν := envSep P`,
`B := Bends P`; then `scale_sq_mul_Bends_sq` turns `(c_μQ)²·B_ends²` back into
`(c₁Q)²(ℒ + C₀)²`, **so the displayed constant is exactly the paper's**.

*Why `Bends P` and not `ℒ + C₀`*: `calE2_maj_bound_L` carries `p.L ≤ B`, which at
`B := ℒ + C₀` is false for every ℒ > 23.93 — see `Bends`, `S5_LB_le_Bends`,
`naive_Bends_fails`.

The two T-floors are the `_L` lemmas' own witnesses, `(2π)²` and `2π·e⁸ ≈ 1.87×10⁴`; note
`ZetaQ.ParamsQ.Valid.T_ge` only gives `T ≥ Zeta23.Tail.T₀ = 300`, so `hT2` is genuinely
extra.  It is satisfied from `log Q ≳ 27` (paper §2.2: `T = (log Q)^{r+ε}`) and is a regime
floor, not a cap.

Paper §8; `NOTE_QR` §QR.1; `NOTE_QG` §g.4 attack-surface item 3
("the ONE remaining unwritten formal step" — this statement is what pins it).
Depends on: `sum_majK1_le`, `sum_majK2_le`, `calE1_maj_bound_L`, `calE2_maj_bound_L`,
`S4_nuBound_envSep`, `S5_LB_le_Bends`, `scale_sq_mul_Bends_sq`.
Rule 17: `hF : LocalHypsCoreW` is cap-free; `hT1`, `hT2` are T-floors; `hsep` is Lemma 8.1′
(no X).  **Verified: the conclusion mentions `P.LB, Zeta23.l P.T, P.LL, P.Q, cϱ` and no
`P.XQ`.  Anything that reintroduces `X` here has re-imported the pointwise `B = l + 4√X`.** -/
theorem ends_family_bound
    (P : ParamsQ) (Qn : ℕ) (cϱ X : ℝ) (F : LocalFun)
    (hP : P.Valid)
    (hl : Zeta23.l P.T ≠ 0)
    (hT1 : (2 * Real.pi) ^ 2 ≤ P.T)
    (hT2 : 2 * Real.pi * Real.exp 8 ≤ P.T)
    (hF : LocalHypsCoreW cϱ (toSetting P) F)
    (hν : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (nuFam X χ))
    (hsep : ∀ τ : ℝ, Bfam Qn X τ ≤ cMu * P.Q * envSep P τ) :
    famSum Qn (fun _ χ => |calE1 (toSetting P) F (nuFam X χ)|)
      + famSum Qn (fun _ χ => |calE2 (toSetting P) F (nuFam X χ)|)
    ≤ (c1Ends * P.Q) ^ 2 * (P.LB ^ 3 * (P.LB + Zeta23.l P.T) * (P.LL + C0Ends) ^ 2
        * (C1ends cϱ + C2ends cϱ * (1 + Real.log P.LB))) := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hsq : 2 * Real.pi ≤ (2 * Real.pi) ^ 2 := by nlinarith
  have hT2π : 2 * Real.pi ≤ P.T := by linarith
  have hTpos : (0 : ℝ) < P.T := by linarith
  -- the bridge: [R]'s `Setting.L` at `toSetting P` IS the paper's `L = λℒ`
  have hLB : (toSetting P).L = P.LB := S1_toSetting_L P hl
  have hcont : Continuous (envSep P) := S3_continuous_envSep P hTpos
  have hNB : NuBound (toSetting P) (Bends P) (envSep P) := S4_nuBound_envSep P hP
  -- **S5**: the absorbing hypothesis `p.L ≤ B` of `calE2_maj_bound_L`, at `B := B_ends`
  have hBL : (toSetting P).L ≤ Bends P := by rw [hLB]; exact S5_LB_le_Bends P hP
  -- ── 𝓔₁ half ────────────────────────────────────────────────────────────────────────
  have e1 : famSum Qn (fun _ χ => |calE1 (toSetting P) F (nuFam X χ)|)
      ≤ (cMu * P.Q) ^ 2
        * (C1ends cϱ * (P.LB ^ 3 * Bends P ^ 2 * (P.LB + Zeta23.l P.T))) := by
    calc famSum Qn (fun _ χ => |calE1 (toSetting P) F (nuFam X χ)|)
        ≤ famSum Qn (fun _ χ =>
            ∫ z in sqI (toSetting P), majK1 (toSetting P) F (nuFam X χ) z) :=
          famSum_mono fun q _ χ _ => abs_calE1_le_maj (hν q χ) hF hTpos
      _ ≤ (cMu * P.Q) ^ 2 * ∫ z in sqI (toSetting P), majK1 (toSetting P) F (envSep P) z :=
          sum_majK1_le P Qn cϱ X F hF hν hsep
      _ ≤ (cMu * P.Q) ^ 2
            * (C1ends cϱ * (P.LB ^ 3 * Bends P ^ 2 * (P.LB + Zeta23.l P.T))) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have h := majK1_integral_le (cϱ := cϱ) (toSetting P) F (Bends P) (envSep P)
            hT1 hF hcont hNB
          rwa [hLB] at h
  -- ── 𝓔₂ half ────────────────────────────────────────────────────────────────────────
  have e2 : famSum Qn (fun _ χ => |calE2 (toSetting P) F (nuFam X χ)|)
      ≤ (cMu * P.Q) ^ 2 * (C2ends cϱ
          * (P.LB ^ 3 * Bends P ^ 2 * (1 + Real.log P.LB) * (P.LB + Zeta23.l P.T))) := by
    calc famSum Qn (fun _ χ => |calE2 (toSetting P) F (nuFam X χ)|)
        ≤ famSum Qn (fun _ χ =>
            ∫ z in (sqI (toSetting P))ᶜ, majK2 cϱ (toSetting P) (nuFam X χ) z) :=
          famSum_mono fun q hq χ hχ => abs_calE2_le_maj_of_integrable hF
            (majK2_integrable_fam P Qn cϱ X F hF hT2π hν hsep hq hχ)
      _ ≤ (cMu * P.Q) ^ 2
            * ∫ z in (sqI (toSetting P))ᶜ, majK2 cϱ (toSetting P) (envSep P) z :=
          sum_majK2_le P Qn cϱ X F hF hν hsep
      _ ≤ (cMu * P.Q) ^ 2 * (C2ends cϱ
            * (P.LB ^ 3 * Bends P ^ 2 * (1 + Real.log P.LB) * (P.LB + Zeta23.l P.T))) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have h := majK2_integral_le (cϱ := cϱ) (toSetting P) F (Bends P) (envSep P)
            hT2 hF hcont hNB hBL
          rwa [hLB] at h
  -- ── the repair is free: `(c_μQ)²·B_ends² = (c₁Q)²(ℒ + C₀)²` ────────────────────────
  have hfree : (cMu * P.Q) ^ 2
        * (C1ends cϱ * (P.LB ^ 3 * Bends P ^ 2 * (P.LB + Zeta23.l P.T)))
      + (cMu * P.Q) ^ 2 * (C2ends cϱ
          * (P.LB ^ 3 * Bends P ^ 2 * (1 + Real.log P.LB) * (P.LB + Zeta23.l P.T)))
      = (c1Ends * P.Q) ^ 2 * (P.LB ^ 3 * (P.LB + Zeta23.l P.T) * (P.LL + C0Ends) ^ 2
          * (C1ends cϱ + C2ends cϱ * (1 + Real.log P.LB))) := by
    have h := scale_sq_mul_Bends_sq P
    linear_combination (P.LB ^ 3 * (P.LB + Zeta23.l P.T)
      * (C1ends cϱ + C2ends cϱ * (1 + Real.log P.LB))) * h
  linarith [e1, e2, hfree]

/-! ### Numeric inputs to the ends row

The five facts below are the entire numeric content of `ends_relative_le` AT THE FLOOR `c_ϱ = 4`
(the `endsRowConst` evaluation; F70's restatement at the actual window constant uses `C1ends_nn` /
`C2ends_nn` and `endsRowConstC` instead, and the `c = 4` facts stay as the record).  They are stated
separately so that the row's constant can be audited without reading a tactic block, and so
that each `linarith` runs in a small context. -/

/-- Four-factor monotonicity for nonnegative reals — the collection step of
`ends_relative_le`, kept separate so that the numeric part of that proof reads as a table of
factor bounds rather than as one opaque `nlinarith`. -/
theorem mul_le_mul4 {a a' b b' c c' d d' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') (h4 : d ≤ d') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have ha' : 0 ≤ a' := ha.trans h1
  have hb' : 0 ≤ b' := hb.trans h2
  have hc' : 0 ≤ c' := hc.trans h3
  exact mul_le_mul (mul_le_mul (mul_le_mul h1 h2 hb ha') h3 hc (mul_nonneg ha' hb'))
    h4 hd (mul_nonneg (mul_nonneg ha' hb') hc')

/-- `ℒ ≥ 30 ⟹ log ℒ ≥ 3` (`e³ = 20.09 < 30`).  `hLcal`'s numeric content. -/
theorem three_le_log_of_thirty_le {x : ℝ} (hx : 30 ≤ x) : 3 ≤ Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Real.le_log_iff_exp_le hx0]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hep : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  nlinarith

/-- `π⁵ ≤ 306.1`.  This is what converts `hRvM`'s `C_fam·2π = π⁵/9` into a numeral;
`2πC_fam·c₁² = 5.716` is NOTE_QR §QR.1's ≈ 5.7, i.e. its chain **without** the bracket. -/
theorem pi_pow_five_le : Real.pi ^ 5 ≤ 306.1 := by
  have h : Real.pi ^ 5 ≤ (3.1416 : ℝ) ^ 5 :=
    pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 5
  have h2 : (3.1416 : ℝ) ^ 5 ≤ 306.1 := by norm_num
  linarith

/-- `C_fam·2π = π⁵/9 ≤ 34.02`. -/
theorem Cfam_mul_two_pi_le : Cfam * (2 * Real.pi) ≤ 306.1 / 9 := by
  unfold Cfam
  linarith [pi_pow_five_le]

/-- `C₁ = 4(90 + 32c_ϱ²) = 2408` at the design's `c_ϱ = 4`. -/
theorem C1ends_four : C1ends 4 = 2408 := by unfold C1ends; norm_num

/-- `0 ≤ C₂′(4)`. -/
theorem C2ends_four_nonneg : (0 : ℝ) ≤ C2ends 4 := by
  unfold C2ends
  have hm : (0 : ℝ) ≤ max 0 (Real.log 4) := le_max_left _ _
  have hc := Zeta23.PrimeSide.CN2_nonneg 4
  have h : (0 : ℝ) ≤ 2 * (8 + 4 * max 0 (Real.log 4) + 7 * 4) := by linarith
  exact mul_nonneg h hc

/-- `C₂′(4) = 2(36 + 8 log 2)·CN2(4) ≤ 5.3065×10⁴` — with `CN2(4) = 100(5 + 2 log 2) ≤ 638.63`.
**This is the constant NOTE_QR §QR.1's "relative order" chain drops**, and it is where the
missing factor ≈ 6×10⁴ in budget row L₅ lives. -/
theorem C2ends_four_le : C2ends 4 ≤ 53065 := by
  have hlog2u : Real.log 2 < 0.6931472 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog2l : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog4pos : (0 : ℝ) < Real.log 4 := by rw [hlog4]; linarith
  have hCN2nn : (0 : ℝ) ≤ Zeta23.PrimeSide.CN2 4 := Zeta23.PrimeSide.CN2_nonneg 4
  have hCN2le : Zeta23.PrimeSide.CN2 4 ≤ 638.63 := by
    rw [Zeta23.PrimeSide.CN2_def, abs_of_pos hlog4pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 4), hlog4]
    linarith
  unfold C2ends
  rw [max_eq_right hlog4pos.le, hlog4]
  have hprod : (72 + 16 * Real.log 2) * Zeta23.PrimeSide.CN2 4 ≤ 83.0904 * 638.63 :=
    mul_le_mul (by linarith) hCN2le hCN2nn (by norm_num)
  linarith

/-- `0 ≤ C₁(c)` for every `c`. -/
theorem C1ends_nn (c : ℝ) : 0 ≤ C1ends c := by unfold C1ends; positivity

/-- `0 ≤ C₂′(c)` for `c ≥ 0`. -/
theorem C2ends_nn {c : ℝ} (hc : 0 ≤ c) : 0 ≤ C2ends c := by
  unfold C2ends Zeta23.PrimeSide.CN2
  have h1 : 0 ≤ max 0 (Real.log c) := le_max_left _ _
  positivity

/-- `c_ends(4) = 10·2408 + 47·C₂′(4) ≤ 2.52×10⁶` — the F70 coefficient at the floor, against the
floor numeral `endsRowConst = 2.5×10⁶`. -/
theorem endsRowConstC_four_le : endsRowConstC 4 ≤ 2520000 := by
  unfold endsRowConstC; rw [C1ends_four]; linarith [C2ends_four_le]

/-- **Lemma 8.2, family relative order** (paper §8; NOTE_QR §QR.1 as revised at R7).
After the hat normalisation `Ĝ := G/(aL²)` (paper §3), the family ends are **Θ(ℒ log ℒ/T)**
relative to the family zero count `𝒩 := Σ_χ N_χ(T, 2T) ≍ Q²Tℒ`, and the budget charges
`r₅ = 6ℒ log ℒ/T` (ledger row L₅, 0.4 % of the budget).  Stated as an inequality against the
ledger row, not as a `Θ`.

The order is **Θ and not merely O**: LEMMA_QE §QE.iii's "the true order may be (log ℒ)^c/T,
recorded as slack" is RETRACTED by its own R5 header (`B_fam ≥ √|𝔉|·ℒ/2π` is forced by
the μ-part), and NOTE_QG §g.4's own display is struck [SUPERSEDED — R7].  Only the R7
figures are used here.

*Consistency anchor (LEMMA_QE §QE.iii, not formalised — recorded):* run the same bookkeeping
in the T-aspect, where `B² ≍ 16X = 16T^λ`; the relative 𝓔₁ becomes `T^{λ−1}/L·polylog`,
which is `o(1)` **iff λ ≤ 1**.  I.e. the hat-normalisation bookkeeping reproduces [R]'s own
ends wall exactly.  That the family version has no such wall is the content of §8.

⚠ Under the rejected fallback `B := max(p.L, ℒ+C₀)` the constant moves ≈ 5.7 → ≈ 8.9 and
this statement becomes FALSE at `r₅ = 6`; it would need `9`.  See `Bends`.

Paper §8; §10.2 ledger row L₅.
Depends on: `ends_family_bound`, `ZetaQ/Certificate.lean` (the hat normalisation `a L²`),
`ZetaQ/Budget.lean` (row L₅).  **Consumed by:** the frobSq assembly (Certificate, r₂ row).

Hypotheses that are deliberately EXPLICIT rather than derived (brief §"Style that
compiles"):
  * `hRvM` — the family Riemann–von Mangoldt lower bound `𝒩 ≥ Q²Tℒ/(2π·C)` with
    `C = Cfam = π⁴/18` (paper §12.2 gives `|𝔉_Q| = (18/π⁴)Q²(1+o(1))`).  Pinning `𝒩` is
    §12's job, not §8's; taking it as a hypothesis keeps §8 auditable.
  * the former `hcϱ : c_ϱ ≤ 4` — which with `hF.four_le_cϱ : 4 ≤ c_ϱ` pinned
    `c_ϱ = 4` — is GONE: it was vacuous for every real window (`cRho ϱ ≥ 12` for any C¹ ramp,
    `c_ϱ(ϱ₂) = 31.26`; B9), so the lemma as stated was never instantiable.  The row now carries
    `c_ϱ` (`r5c c_ϱ`, `endsRowConstC`), exactly as `ends_family_bound` does.
  * `hLcal` — `ℒ ≥ 30`, the scale at which the numeric collection closes (ℒ ≈ 230 at
    Q = 10¹⁰⁰).  A lower bound on ℒ, hence Rule-17 clean.

Rule 17: no hypothesis relates X to T, caps λ, or fixes D₀; `𝒩` is a family zero count and
carries no bandwidth information.

──────────────────────────────────────────────────────────────────────────────────────────
🚩 **THE COEFFICIENT, AND TWO STATEMENT DEFECTS: ALL THREE REPAIRED.  NOW PROVED.**

**(a) The coefficient was `6` and is now `endsRowConst = 2.5×10⁶`** (at the floor `c_ϱ = 4`; F70:
at the actual window constant `c_ϱ` it is `endsRowConstC c_ϱ`, and the lemma below is stated
so).  The full accounting —
NOTE_QR §QR.1's lemma-versus-chain discrepancy (the chain drops the bracket, which is
exactly where the missing 6×10⁴ lives), the evaluation at the design of record, the design
figure 3.7×10⁵ against the uniform-over-the-class 2.5×10⁶, and what does and does not break
(Theorem 1: nothing; §10.4's table: everything) — is at `r5` and `endsRowConst`.  The ORDER
`Θ(ℒ log ℒ/T)` is unchanged, which is why Theorem 1 does not move.  The paper's printed row
survives as `r5Paper`.

**(b) `Qn` was not tied to `P.Q`.**  `Bfam_le_sep` carries `hQn : (Qn : ℝ) ≤ P.Q`; this
statement carried nothing, and nothing bounded `X`.  The left side is a sum over `𝔉_{Qn}` of
quantities that grow with `X` (through `nuFam X χ`), while the right side sees `Qn` only
through `hRvM` and `P.Q` only through `ℒ = log(QT/2π)`.  Failing instance: take `Qn := 1` and
`X ≈ (c₁·P.Q·ℒ)²/4`, the largest `X` that `hsep` still permits (since `B_fam ≈ 2√X` must be
`≤ c_μ·P.Q·env_sep ≈ 0.41·P.Q·ℒ`); the left side then grows like `P.Q²` while the right grows
like `ℒ² log ℒ = (log P.Q)² log log P.Q`.  **Repaired** by `hQn`/`hQlb`, which together say
`(Qn : ℝ) = P.Q`, i.e. that the family summed over IS the design's family — `hQn` is the one
`Bfam_le_sep` supplies, `hQlb` the one this row needs.  Both are stated rather than bundled
into an equality so that each side's role stays visible.

**(c) `l ≤ L` is needed and was not there.**  The bound carries a factor `(L + l)/L`, which
is unbounded as `λ → 0`.  `hlL : Zeta23.l P.T ≤ P.LB` is `log(T/2π) ≤ λℒ`, true at the design
with a factor 18 of room (17.2 vs 309.8) and implied by `λ ≥ 1` together with `l ≤ ℒ`.
**Rule 17: this is the REVERSE of `Zeta23.Params.L_le_l`**, the λ ≤ 1-gated lemma the notes
forbids citing.  It is a LOWER bound on the bandwidth, i.e. it points away from the T-aspect
wall, and it cannot re-import it: at `λ ≤ 1` in the T-aspect one has `L ≤ l`, the opposite
inequality.

*Consistency anchor (LEMMA_QE §QE.iii, not formalised — recorded):* run the same bookkeeping
in the T-aspect, where `B² ≍ 16X = 16T^λ`; the relative 𝓔₁ becomes `T^{λ−1}/L·polylog`,
which is `o(1)` **iff λ ≤ 1**.  I.e. the hat-normalisation bookkeeping reproduces [R]'s own
ends wall exactly.  That the family version has no such wall is the content of §8, and it
survives the constant repair untouched.
────────────────────────────────────────────────────────────────────────────────────────── -/
theorem ends_relative_le
    (P : ParamsQ) (Qn : ℕ) (cϱ X Ncal : ℝ) (F : LocalFun)
    (hP : P.Valid)
    (hl : Zeta23.l P.T ≠ 0)
    (hT1 : (2 * Real.pi) ^ 2 ≤ P.T)
    (hT2 : 2 * Real.pi * Real.exp 8 ≤ P.T)
    (hF : LocalHypsCoreW cϱ (toSetting P) F)
    (hLcal : 30 ≤ P.LL)
    (hQn : (Qn : ℝ) ≤ P.Q)
    (hQlb : P.Q ≤ (Qn : ℝ))
    (hlL : Zeta23.l P.T ≤ P.LB)
    (hν : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Continuous (nuFam X χ))
    (hsep : ∀ τ : ℝ, Bfam Qn X τ ≤ cMu * P.Q * envSep P τ)
    (hN : 0 < Ncal)
    (hRvM : (Qn : ℝ) ^ 2 * P.T * P.LL ≤ Cfam * (2 * Real.pi) * Ncal) :
    (famSum Qn (fun _ χ => |calE1 (toSetting P) F (nuFam X χ)|)
        + famSum Qn (fun _ χ => |calE2 (toSetting P) F (nuFam X χ)|))
        / (P.aQ * P.LB ^ 2) ^ 2
      ≤ r5c cϱ P * Ncal := by
  -- the window constant is whatever `hF` carries (`4 ≤ c_ϱ`); nothing pins it.
  have hc4 : (4 : ℝ) ≤ cϱ := hF.four_le_cϱ
  have hC1nn : (0 : ℝ) ≤ C1ends cϱ := C1ends_nn cϱ
  have hC2nn : (0 : ℝ) ≤ C2ends cϱ := C2ends_nn (by linarith)
  -- ── regime ────────────────────────────────────────────────────────────────────────────
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hT0 : (0 : ℝ) < P.T := by nlinarith
  have hLBeq : (toSetting P).L = P.LB := S1_toSetting_L P hl
  have hLB8 : (8 : ℝ) ≤ P.LB := by rw [← hLBeq]; exact hF.eight_le_L
  have hLBpos : (0 : ℝ) < P.LB := by linarith
  have hl1 : (1 : ℝ) ≤ Zeta23.l P.T := hF.one_le_l
  have hlpos : (0 : ℝ) < Zeta23.l P.T := by linarith
  have hLL30 : (30 : ℝ) ≤ P.LL := hLcal
  have hLLpos : (0 : ℝ) < P.LL := by linarith
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  -- ── the hat normalisation is bounded below: `a ≥ 3/4`, so `1/a² ≤ 16/9` ───────────────
  have hlampos : (0 : ℝ) < P.toParams.lam := by
    show (0 : ℝ) < P.LB / Zeta23.l P.T
    exact div_pos hLBpos hlpos
  have hw8 : 8 * P.w ≤ P.LB := by
    have h := hF.w_le
    rw [hLBeq] at h
    have h2 : (toSetting P).w = P.w := rfl
    rw [h2] at h
    linarith
  -- `a ≥ 3/4` is the `Valid` floor `a_ge` (for the flat taper it was
  -- `three_quarters_le_b ∘ b_le_a`; the design window has `a ≈ 0.78`).
  have haQ : (3 : ℝ) / 4 ≤ P.aQ := hP.a_ge
  have haQ0 : (0 : ℝ) < P.aQ := by linarith
  have haQsq : (9 : ℝ) / 16 ≤ P.aQ ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) haQ 2
    linarith
  -- ── logarithms ────────────────────────────────────────────────────────────────────────
  have hlog2u : Real.log 2 < 0.6931472 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlogLL3 : (3 : ℝ) ≤ Real.log P.LL := three_le_log_of_thirty_le hLL30
  have hlogLLnn : (0 : ℝ) ≤ Real.log P.LL := by linarith
  have hLB2L : P.LB ≤ 2 * P.LL := by
    show P.lam * P.LL ≤ 2 * P.LL
    exact mul_le_mul_of_nonneg_right hP.lam_lt_two.le hLLpos.le
  have hlogLB : Real.log P.LB ≤ Real.log 2 + Real.log P.LL := by
    calc Real.log P.LB ≤ Real.log (2 * P.LL) := Real.log_le_log hLBpos hLB2L
      _ = Real.log 2 + Real.log P.LL := Real.log_mul (by norm_num) (ne_of_gt hLLpos)
  have hlogLBnn : (0 : ℝ) ≤ Real.log P.LB := Real.log_nonneg (by linarith)
  -- ── the family count, from `hRvM`: `𝒩 ≥ 9·Qn²Tℒ/π⁵` ─────────────────────────────────
  have hNc : 9 * ((Qn : ℝ) ^ 2 * P.LL * P.T) ≤ 306.1 * Ncal := by
    have h := mul_le_mul_of_nonneg_right Cfam_mul_two_pi_le hN.le
    linarith [hRvM]
  -- ── the bracket at general `c_ϱ`: `C₁ + C₂′(1 + log L) ≤ K·log ℒ`, `K = C₁/3 + 1.5645·C₂′`
  --    (`log L ≤ log 2 + log ℒ`, `log ℒ ≥ 3`) ─────────────────────────────────────────────
  have hstep4 : C1ends cϱ + C2ends cϱ * (1 + Real.log P.LB)
      ≤ (C1ends cϱ / 3 + 1.5645 * C2ends cϱ) * Real.log P.LL := by
    have hin : (1 : ℝ) + Real.log P.LB ≤ 1.6931472 + Real.log P.LL := by linarith
    have h1 : C2ends cϱ * (1 + Real.log P.LB) ≤ C2ends cϱ * (1.6931472 + Real.log P.LL) :=
      mul_le_mul_of_nonneg_left hin hC2nn
    have h2 : C2ends cϱ * (1.6931472 + Real.log P.LL) ≤ C2ends cϱ * (1.5645 * Real.log P.LL) :=
      mul_le_mul_of_nonneg_left (by linarith) hC2nn
    have h3 : C1ends cϱ * 3 ≤ C1ends cϱ * Real.log P.LL :=
      mul_le_mul_of_nonneg_left hlogLL3 hC1nn
    nlinarith [h1, h2, h3]
  -- ── the arithmetic core: `0.484128·Qn²ℒT·K ≤ c_ends(c_ϱ)·𝒩·a²` ──────────────────────
  have hK0 : (0 : ℝ) ≤ C1ends cϱ / 3 + 1.5645 * C2ends cϱ := by linarith
  have hcore : 0.484128 * ((Qn : ℝ) ^ 2 * P.LL * P.T) * (C1ends cϱ / 3 + 1.5645 * C2ends cϱ)
      ≤ endsRowConstC cϱ * Ncal * P.aQ ^ 2 := by
    have hQ : (Qn : ℝ) ^ 2 * P.LL * P.T ≤ 34.0112 * Ncal := by linarith [hNc, hN.le]
    have h1 : 0.484128 * ((Qn : ℝ) ^ 2 * P.LL * P.T) * (C1ends cϱ / 3 + 1.5645 * C2ends cϱ)
        ≤ 0.484128 * (34.0112 * Ncal) * (C1ends cϱ / 3 + 1.5645 * C2ends cϱ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by norm_num)) hK0
    have hE0 : (0 : ℝ) ≤ endsRowConstC cϱ * Ncal := by
      unfold endsRowConstC; exact mul_nonneg (by linarith) hN.le
    have h2 : endsRowConstC cϱ * Ncal * (9 / 16) ≤ endsRowConstC cϱ * Ncal * P.aQ ^ 2 :=
      mul_le_mul_of_nonneg_left haQsq hE0
    -- `16.4658·(C₁/3 + 1.5645 C₂′) = 5.489 C₁ + 25.76 C₂′ ≤ (9/16)(10 C₁ + 47 C₂′)`
    have h3 : 0.484128 * (34.0112 * Ncal) * (C1ends cϱ / 3 + 1.5645 * C2ends cϱ)
        ≤ endsRowConstC cϱ * Ncal * (9 / 16) := by
      unfold endsRowConstC
      nlinarith [mul_nonneg hC1nn hN.le, mul_nonneg hC2nn hN.le]
    linarith
  -- ── the four factor bounds ────────────────────────────────────────────────────────────
  have hb0 : (0 : ℝ) ≤ P.LB ^ 3 * (P.LB + Zeta23.l P.T) :=
    mul_nonneg (by positivity) (by linarith)
  have hd0 : (0 : ℝ) ≤ C1ends cϱ + C2ends cϱ * (1 + Real.log P.LB) := by
    have h : (0 : ℝ) ≤ C2ends cϱ * (1 + Real.log P.LB) :=
      mul_nonneg hC2nn (by linarith)
    linarith
  -- `c₁²Q² ≤ c₁²Qn²` — this is where `hQlb` enters (defect (b) above)
  have hstep1 : (c1Ends * P.Q) ^ 2 ≤ 0.1681 * (Qn : ℝ) ^ 2 := by
    have hQsq : P.Q ^ 2 ≤ (Qn : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hQlb 2
    have hc : (c1Ends * P.Q) ^ 2 = 0.1681 * P.Q ^ 2 := by unfold c1Ends; ring
    rw [hc]; linarith
  -- `L + l ≤ 2L` — this is where `hlL` enters (defect (c) above)
  have hstep2 : P.LB ^ 3 * (P.LB + Zeta23.l P.T) ≤ P.LB ^ 3 * (2 * P.LB) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- `(ℒ + C₀)² ≤ 1.44ℒ²` at `ℒ ≥ 30`
  have hstep3 : (P.LL + C0Ends) ^ 2 ≤ 1.44 * P.LL ^ 2 := by
    have h1 : P.LL + C0Ends ≤ 1.2 * P.LL := by unfold C0Ends; linarith
    have h2 : (P.LL + C0Ends) ^ 2 ≤ (1.2 * P.LL) ^ 2 :=
      pow_le_pow_left₀ (by unfold C0Ends; linarith) h1 2
    linarith
  -- ── Lemma 8.2, closed form, then collection ───────────────────────────────────────────
  have hfam := ends_family_bound P Qn cϱ X F hP hl hT1 hT2 hF hν hsep
  have hD : (0 : ℝ) < (P.aQ * P.LB ^ 2) ^ 2 :=
    pow_pos (mul_pos haQ0 (pow_pos hLBpos 2)) 2
  rw [div_le_iff₀ hD]
  refine hfam.trans ?_
  clear hfam hν hsep hF hP hT1 hT2 hRvM
  have heq : (c1Ends * P.Q) ^ 2 * (P.LB ^ 3 * (P.LB + Zeta23.l P.T) * (P.LL + C0Ends) ^ 2
        * (C1ends cϱ + C2ends cϱ * (1 + Real.log P.LB)))
      = (c1Ends * P.Q) ^ 2 * (P.LB ^ 3 * (P.LB + Zeta23.l P.T)) * (P.LL + C0Ends) ^ 2
        * (C1ends cϱ + C2ends cϱ * (1 + Real.log P.LB)) := by ring
  rw [heq]
  refine le_trans (mul_le_mul4 (sq_nonneg _) hb0 (sq_nonneg _) hd0
    hstep1 hstep2 hstep3 hstep4) ?_
  -- ── the final comparison ──────────────────────────────────────────────────────────────
  have hW : (0 : ℝ) ≤ P.LB ^ 4 * P.LL * Real.log P.LL :=
    mul_nonneg (by positivity) hlogLLnn
  have hX : (0 : ℝ) ≤ (Qn : ℝ) ^ 2 * P.LL * P.T := by positivity
  have hR : r5c cϱ P * Ncal * (P.aQ * P.LB ^ 2) ^ 2
      = endsRowConstC cϱ * Ncal * P.aQ ^ 2 * (P.LB ^ 4 * P.LL * Real.log P.LL) / P.T := by
    unfold r5c
    field_simp
    try ring
  rw [hR, le_div_iff₀ hT0]
  have hkey := mul_le_mul_of_nonneg_right hcore hW
  linarith [hkey, mul_nonneg hX hW]

end Ends
end ZetaQ
