# ZetaQ — the conductor-aspect library

`ZetaQ` is an addition to this repository by Oliver D'Souza (2026), released under the
Apache License 2.0. It builds on `Zeta23/`, the vendored critical-line formalization
described in the top-level [`README.md`](../README.md), and proves a conductor-aspect
("q-aspect") analogue: for families of primitive Dirichlet characters, a positive proportion
of the zeros of `L(s, χ)` in a height window are **simple and on the critical line**.

The full orientation — the six headline theorems and their constants, exactly what is
assumed, and a one-line description of every file — is the module docstring at the top of
[`../ZetaQ.lean`](../ZetaQ.lean). Read that first. This file covers the things a reader
needs in order to make sense of the *docstrings inside* the library.

## Building

```bash
lake build ZetaQ
```

`ZetaQ` is deliberately outside `defaultTargets`, so a bare `lake build` still builds only
the sorry-free `Zeta23` library. Expect exactly four `declaration uses 'sorry'` warnings:
`ZetaQ.l2_concentration_exists` (`Sieve.lean`, the Beurling–Selberg input of the SHARP large
sieve — Selberg's extremal problem — kept as the record of the sharp statement) and the three
superseded, frozen statements `trace_row`, `frobenius_row`, `assembly_at_lamStar` in
`Budget.lean`. **No proved theorem consumes any of the four**: since the Gallagher rethread the
six headline theorems report `[propext, Classical.choice, Quot.sound]` under `#print axioms`
(`audit/final_axioms.lean`).

Receipts:

```bash
lake env lean audit/final_check.lean    # `#print sorries` on the six headline theorems
lake env lean audit/final_axioms.lean   # `#print axioms` on the headline route
```

## Reading the docstrings

The docstrings in `ZetaQ/` are long, and deliberately so: a large part of them is the record
of what was tried and did not work — statements that were false as first written, with the
counterexample; hypotheses that turned out to be load-bearing; routes that are blocked for a
reason, so that nobody walks them twice. Four conventions recur.

**`[R]`** is the `Zeta23/` library — "the record", the critical-line formalization this one
is built on. `[R]'s X` means the declaration `Zeta23.X`. Citations of the form
`Zeta23/ThmD/Functional.lean:432` are file:line into that library.

**`§n`** is a section of the conductor-aspect paper that this library formalizes. That paper
is not part of this repository; the section numbers identify which step of the argument a
declaration corresponds to, the same way the `[prop:PP]`-style labels do in `Zeta23/`. Names
in capitals such as `LEMMA_QT §QT.b(5)` or `NOTE_QR §QR.1` are the paper's own derivation
notes, also not shipped; like the `[XF′ …]` labels under `Zeta23/XiPrime/` they record
provenance only. **What is relied upon is in every case the Lean statement the docstring
introduces**, and nothing in the build depends on any unshipped file.

**`F<n>` and `D<n>`** are stable labels for findings and design decisions, used so that a
note in one place can refer to one in another. They are not names of Lean declarations and
no proof depends on them. Each is stated in substance where it matters — the module headers
of `ZetaQ/Budget.lean` and `ZetaQ/Zones.lean` carry the two largest groups, and each of those
headers glosses the labels its own body cites — so a reader who ignores the numbers loses
nothing.

**Rule 17** is a standing prohibition, stated in `Defs.lean`, on three hypotheses that would
silently collapse the theorem: `λ ≤ 1`, `X ≤ T`, and `D₀ = √T`. Each is *true* in the
critical-line setting of `Zeta23/` and *false*, or fatal, here — the conductor-aspect design
runs at bandwidth `λ* ≈ 1.25 > 1`, where the payoff functional is strictly better than the
Montgomery–Taylor value it degenerates to at `λ = 1`. A `Rule 17:` line in a docstring is
the audit note recording that the statement above it is free of all three.

## The large sieve: Gallagher's budget, and the Selberg input no longer consumed

Lemma 6.1 is consumed at the **Gallagher budget** `Q² + πN`:
`ZetaQ.Gallagher.multiplicative_large_sieve_gallagher` (`Gallagher.lean`) proves
`Σ_{q≤Q}Σ*_χ|Σ_{n≤N}a_nχ(n)|² ≤ (Q² + πN)Σ|a_n|²` sorry-free, from Gallagher's elementary
additive inequality `Σ_i|S(θ_i)|² ≤ (δ⁻¹ + πN)Σ|a_n|²` (Gallagher 1967; Montgomery, Bull. AMS
84 (1978), Thm 1: a Sobolev bound on each `δ`-interval, Parseval, and a centred derivative).
The coefficient of `δ⁻¹`, hence of `Q²`, is exactly `1`, and `Q²` is the only term of the
budget that reaches the family constant `C = Q²/|𝔉_Q|`; the length term enters every consumer
only through `budget ≤ Q²(1 + 4Q^{−δ})` in the range `X ≤ Q^{2−δ}`. So no headline constant
moved when the sharp budget `N + Q² − 1` was replaced. The interfaces `Ends.LargeSieveHyp`,
`Zones.LargeSieveFamily` and the budget `Zones.sieveBudgetQ = Q² + πX` are stated at the
Gallagher budget and discharged from `Gallagher.lean`.

The sharp chain of `Sieve.lean` is kept, unconsumed, as the record of the sharp statement.
Its one gap is the following.

`ZetaQ.l2_concentration_exists` (`Sieve.lean`) asserts, for `N : ℕ` and `0 < δ ≤ 1`, the
existence of an `L²` function supported on `(0, δ]` with mass exactly `N − 1 + δ⁻¹` whose
Fourier coefficients at `1, …, N` all have modulus at least 1. It is proved in this file for
the whole band `(N−1)δ ≤ 1` and for `δ = 1`; what remains open is `δ < 1` together with
`(N−1)δ > 1`, which its docstring shows to be Selberg's extremal problem proper (Beurling's
function, Selberg's shift, the Krein / Fejér–Riesz factorisation, Paley–Wiener) — none of it
in Mathlib. Everything else in the sharp multiplicative large sieve `N + Q² − 1` is proved
from it; nothing on the headline route uses it.

## Corollary 3″: the reflected large sieve, and the parity headlines at 0.7212 / 0.7098

Four modules carry the parity families from the constant `2C` towards the full-family `C`
(branch `reflected-sieve`; no existing statement is changed):

* `ReflectedSieve.lean` — `Reflected.reflected_large_sieve_gallagher`: for a parity class,
  `Σ_{q≤Q} Σ*_{χ, parity χ = p} |Σ_{n≤N} a_nχ(n)|² ≤ (Q²/2 + π(N + ½)) Σ|a_n|²` (the reflection trick,
  realised in `ℕ` by translating by `(Q + N + 1)!`, plus a windowed Gallagher sieve);
* `Cor3Reflected.lean` — §4's Lemma 4.3 chain for one parity class at the budget
  `Q²/2 + π(X + ½)`, and the parity PP block of the `B_{C,C}` route (`famPP_le_sieve_par`);
* `Cor3ZoneSplit.lean` — the headline route's PP block at an abstract budget (`FamSieveAt`),
  whose full-family instance recovers the current route, and its parity instance
  `famPP_le_zone_split_par`: out-zone coefficient `F.Cconst / 2` — the FULL family constant;
* `Cor3Frob.lean` — `frobenius_inzone_eventually_par`, the in-zone Frobenius assembly for a
  parity family at `F.Cconst / 2`.

* `Cor3Full.lean` — **the four headlines**
  `JoinProved.corollary_three_{even,odd}_{qQ,dyadic}_full_proved'`: the parity families'
  zero counts (the same objects as `corollary_three_*_proved'`) at `P_cert = 0.7212` (`q ≤ Q`)
  and `0.7098` (dyadic), with no hypothesis beyond `3 ≤ r`, `0 < ε`; axioms
  `[propext, Classical.choice, Quot.sound]`.

The plumbing: `Family` has four more constructors, `evenQleR`, `oddQleR`, `evenDyadicR`,
`oddDyadicR` (`Certificate.lean`) — the parity families' moduli, characters, size and
`Cconst = 2C`, but the FULL families' bandwidth `λ*`, profile, zone secant, payoff and
`κ_cert` — so `Cor3Frob`'s conditional rows discharge by `rfl`, the zone comparison at `C_F/2`
is the full families' certified `ZoneLipschitzData`, and the whole generic route
(`exists_designOfRecordM`, `assembly_at_lamStar_provedM`, the Margin counting rows, the rate)
runs unchanged. `NfamCount Family.evenQleR = NfamCount Family.evenQle` is `rfl` (all four).
Every per-constructor site gained its four branches; the only new mathematics is the sharp ramp
link of the full profiles at `C = 2C_F` (`Payoff.profileRampLink_sharp_qle_twoC` /
`_dyadic_twoC`, `K = 0.81` / `1.04` in `w/ℒ` units), which `profileRampLink_sharp` needs for
the new branches. The 0.698 / 0.6919 headlines are untouched.
