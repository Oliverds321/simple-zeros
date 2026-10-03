/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ — a Lean 4 formalization in the CONDUCTOR (q-) aspect: a positive proportion of the
zeros of the Dirichlet L-functions of a family of primitive characters are simple and on the
critical line. Built on `Zeta23`, the vendored critical-line library (see the top-level
README.md), which supplies the explicit formula for L(s,χ), Riemann–von Mangoldt, the
rank–trace inequality, the taper/window layer and the Montgomery–Vaughan inequality.

Full orientation, including how to read the docstrings: `ZetaQ/README.md`.

============================================================================================
WHAT IS PROVED — six headline theorems, namespace `ZetaQ.JoinProved`, all in `ZetaQ/Margin.lean`
============================================================================================
Each takes only `(r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)` and no further hypothesis. With
`T = Twin Q r ε = (log Q)^{r+ε}` the window height, `𝒩 = Σ_χ N_χ(T, 2T)` the family zero count
and `Σ_χ N⁰ˢ_χ(T, 2T)` the count of family zeros that are SIMPLE and ON the critical line, each
asserts

    ∃ Q₀ c, 0 < c ∧ ∀ Q ≥ Q₀,  (P_cert − c·log log Q / log Q) · 𝒩  ≤  Σ_χ N⁰ˢ_χ

over the family named on its line:

  theorem_one_generic_proved'           P_cert = 0.7212   q ≤ Q            `Family.qle`
  corollary_two_dyadic_proved'          P_cert = 0.7098   Q/2 < q ≤ Q      `Family.dyadic`
  corollary_three_even_qQ_proved'       P_cert = 0.698    q ≤ Q, χ even    `Family.evenQle`
  corollary_three_odd_qQ_proved'        P_cert = 0.698    q ≤ Q, χ odd     `Family.oddQle`
  corollary_three_even_dyadic_proved'   P_cert = 0.6919   Q/2 < q ≤ Q, χ even
  corollary_three_odd_dyadic_proved'    P_cert = 0.6919   Q/2 < q ≤ Q, χ odd

and, on branch `reflected-sieve`, COROLLARY 3″ (`ZetaQ/Cor3Full.lean`, same namespace) — the
SAME four parity families' zero counts at the FULL families' constants:

  corollary_three_even_qQ_full_proved'       P_cert = 0.7212   q ≤ Q, χ even
  corollary_three_odd_qQ_full_proved'        P_cert = 0.7212   q ≤ Q, χ odd
  corollary_three_even_dyadic_full_proved'   P_cert = 0.7098   Q/2 < q ≤ Q, χ even
  corollary_three_odd_dyadic_full_proved'    P_cert = 0.7098   Q/2 < q ≤ Q, χ odd

The reflected large sieve (`ZetaQ/ReflectedSieve.lean`) charges one parity class `Q²/2 + π(N + ½)`,
so a parity family's out-zone constant is the full family's `C`; the proof runs the parity
characters at the full design through the reflected-sieve constructors `Family.*R`.

The counting functions are `ZetaQ.NcountQ` / `ZetaQ.N0sQ` (`ZetaQ/Certificate.lean` §3.2),
thin wrappers on `Zeta23.ThmE.NcountL` / `N0simpleL`, which are defined directly against
Mathlib's `DirichletCharacter.LFunction`. The families are the constructors of
`ZetaQ.Family` (`ZetaQ/Certificate.lean`), each a modulus range together with a character
selector on the primitive characters of that modulus (the four reflected-sieve constructors
`evenQleR`, … carry a parity family's characters with a full family's design).

The certified constants are FEASIBILITY constants at four digits (`ZetaQ.Payoff.Pcert_*_smooth`),
deliberately weaker than the paper's ten-digit variational optima `ZetaQ.Pconst` etc.; see
`ZetaQ/Payoff.lean` (the two symbols are kept distinct on purpose) and `ZetaQ/JoinCert.lean`.

============================================================================================
WHAT IS ASSUMED
============================================================================================
Nothing. `#print axioms` on each of the ten reports `[propext, Classical.choice, Quot.sound]`,
Lean's three standard axioms, and `#print sorries` on each returns nothing. No `axiom` is
declared anywhere in this library.

Lemma 6.1, the multiplicative large sieve, is consumed at the GALLAGHER budget `Q² + πN`
(`ZetaQ/Gallagher.lean`: Gallagher's elementary inequality `Σ|S(θ_i)|² ≤ (δ⁻¹ + πN)‖a‖²`,
Gallagher 1967 / Montgomery, Bull. AMS 84 (1978), Thm 1, proved here from FTC, Parseval and a
centred derivative). Its `Q²` — the only term that reaches the family constant — is the same
as in the sharp budget `N + Q² − 1`, so no certified constant moved. The sharp chain of
`ZetaQ/Sieve.lean` is kept as a record and is consumed by nothing above; its one gap,

    ZetaQ.l2_concentration_exists    (`ZetaQ/Sieve.lean`)

— Selberg's extremal problem (Beurling's function, the Krein / Fejér–Riesz factorisation,
Paley–Wiener), which Mathlib does not have — is still a `sorry`, proved for the band
`(N−1)δ ≤ 1` and for `δ = 1`, open for `δ < 1` with `(N−1)δ > 1`.

Receipts, runnable against a built tree:
    lake env lean audit/final_check.lean     -- `#print sorries` on all six
    lake env lean audit/final_axioms.lean    -- `#print axioms` on the headline route

Three further `sorry`s live in `ZetaQ/Budget.lean` — `trace_row`, `frobenius_row` and
`assembly_at_lamStar`. They are SUPERSEDED statements, kept frozen together with the record of
why the paper's method does not reach them AS STATED, and replaced by the proved eventual /
certified-constant forms (`trace_row_eventually`, `ZetaQ/HFrob.lean`, `ZetaQ/JoinCert.lean`).
No proved theorem consumes them; `audit/RevDepZetaQ.lean` is the reverse-dependency check.

============================================================================================
BUILD
============================================================================================
    lake build ZetaQ

This library is deliberately OUTSIDE `defaultTargets`, so that a bare `lake build` remains the
`Zeta23` record's own sorry-free gate. Expect exactly four `declaration uses 'sorry'` warnings,
one for each declaration named above (none of which any headline consumes), and no errors.

============================================================================================
THE FILES
============================================================================================
Section numbers (§n) are those of the q-aspect paper this library formalizes.

  the shared layer
    ZetaQ/Defs.lean            §2.2 notation: `ParamsQ`, the scales, the family, the constants
    ZetaQ/Window.lean          the design window is an admissible window (product profile×ramp)
    ZetaQ/Certificate.lean     §3 grid Gram, hat units, `Family`, the counts, Proposition 3.1

  the analytic layers
    ZetaQ/Sieve.lean           §6 the sharp multiplicative large sieve (Lemma 6.1)
    ZetaQ/CharSums.lean        §5 the character-sum arithmetic
    ZetaQ/Zones.lean           §4 the two-zone analysis in the dual variable
    ZetaQ/Tail.lean            §7 the tail
    ZetaQ/Ends.lean            §8 the ends (Lemmas 8.1, 8.1', 8.2)
    ZetaQ/EFChi.lean           §9 the explicit-formula / archimedean layer, uniformly in q
    ZetaQ/MuqUniform.lean      q-uniform μ_χ bounds with explicit absolute constants
    ZetaQ/AbelLogPow.lean      Abel summation of `log q`, `(log q)²` (Mathlib-only)

  the variational layer (§11)
    ZetaQ/Payoff.lean          the payoff functional `B`, the exact-ℚ certificate engine
    ZetaQ/DesignProfile.lean   the degree-6 design profiles `p` of the two full families
    ZetaQ/PayoffSmooth.lean    the feasibility certificates at the smooth design profiles
    ZetaQ/Cor3Smooth.lean      the same, for Corollary 3's two even families
    ZetaQ/RampLink.lean        `B(v_design) ≤ B(v_profile) + O(w/ℒ)`
    ZetaQ/RampLinkSharp.lean   the sharp form `+ K_F·(w/L)`, `K_F ≤ 3`

  the ledger and the assembly (§10, §12)
    ZetaQ/Budget.lean          the ledger, the design of record, the eight-clause assembly
    ZetaQ/Normalisation.lean   §12 normalisation and Corollary 3's obligations
    ZetaQ/EvenFam.lean         §12.3 the even/odd subfamilies and their density certificates
    ZetaQ/Dyadic.lean          the dyadic family by differencing the `q ≤ Q` counts

  the Frobenius row (the paper's main estimate, §§4-6 in budget units)
    ZetaQ/FrobRow8.lean        row 8: `Σ_χ 𝓜[μ_χ, μ_χ]`, the sharp `∫ μ_q²`
    ZetaQ/FrobRow9.lean        row 9: the cross term `Σ_χ 𝓜[μ_χ, P_χ]`
    ZetaQ/Row2Numeric.lean     row 2's numeric threshold lemma (Mathlib-only)
    ZetaQ/Row9Numeric.lean     row 9's numeric threshold lemma (Mathlib-only)
    ZetaQ/FrobAssembly.lean    the assembly of the Frobenius row
    ZetaQ/InZone.lean          the in-zone mean value and the PP block
    ZetaQ/ZoneData.lean        the certified zone Lipschitz data
    ZetaQ/HFrob.lean           the Frobenius row at `κ_cert + rowR2`, all six families

  the join
    ZetaQ/HPre.lean            the tail prefactor `hpre` at the design of record
    ZetaQ/JoinCert.lean        the assembly and rate step at the CERTIFIED constant
    ZetaQ/JoinProved.lean      the same without the sharp zero-density hypothesis
    ZetaQ/Margin.lean          the margin design, removing `r + ε ≤ 7`; THE SIX HEADLINES

  Corollary 3″ (the reflected large sieve)
    ZetaQ/ReflectedSieve.lean  the parity-class sieve at `Q²/2 + π(N + ½)`
    ZetaQ/Cor3Reflected.lean   §4's Lemma 4.3 chain for one parity class
    ZetaQ/Cor3ZoneSplit.lean   the headline route's PP block at `C_F/2`
    ZetaQ/Cor3Frob.lean        the parity Frobenius rows at the full `κ_cert`
    ZetaQ/Cor3Full.lean        THE FOUR COROLLARY 3″ HEADLINES (0.7212 / 0.7098)
-/
import ZetaQ.Defs
import ZetaQ.Certificate
import ZetaQ.Sieve
import ZetaQ.Gallagher
import ZetaQ.ReflectedSieve
import ZetaQ.Cor3Reflected
import ZetaQ.Cor3ZoneSplit
import ZetaQ.Cor3Frob
import ZetaQ.Cor3Full
import ZetaQ.CharSums
import ZetaQ.Zones
import ZetaQ.Tail
import ZetaQ.Ends
import ZetaQ.EFChi
import ZetaQ.Payoff
import ZetaQ.Budget
import ZetaQ.Normalisation
import ZetaQ.Window
import ZetaQ.DesignProfile
import ZetaQ.PayoffSmooth
import ZetaQ.RampLink
import ZetaQ.MuqUniform
import ZetaQ.Row2Numeric
import ZetaQ.AbelLogPow
import ZetaQ.HPre
import ZetaQ.Row9Numeric
import ZetaQ.FrobRow9
import ZetaQ.FrobRow8
import ZetaQ.RampLinkSharp
import ZetaQ.Cor3Smooth
import ZetaQ.JoinCert
import ZetaQ.FrobAssembly
import ZetaQ.InZone
import ZetaQ.ZoneData
import ZetaQ.Dyadic
import ZetaQ.HFrob
import ZetaQ.JoinProved
import ZetaQ.Margin
import ZetaQ.EvenFam
