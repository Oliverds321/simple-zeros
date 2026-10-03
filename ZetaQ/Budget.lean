/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Budget.lean — paper §10: the ledger (§10.2), the budget / design of record (§10.3),
the assembly (§10.5), and **Theorem 1** and **Corollary 2**.

Imports `ZetaQ.Defs`, `ZetaQ.Certificate`, `ZetaQ.EFChi`, `ZetaQ.Tail`, `ZetaQ.Zones`,
`ZetaQ.DesignProfile`, `ZetaQ.MuqUniform`, `ZetaQ.Row2Numeric`; re-exported by the library
root `ZetaQ.lean`. Several later modules — `Dyadic`, `FrobRow8`, `FrobRow9`, `FrobAssembly`,
`HPre`, `ZoneData`, `RampLinkSharp` — import this file; none of them is imported by anything
this file imports, so the graph is acyclic, and the build checks it.

Statement source of truth: paper §§1.1, 10.2–10.5. The `def`s carry real bodies, each with
its provenance.

**The `D<n>` labels used in the docstrings below** are the design decisions this file rests
on. They are recorded here once so that a local `(D35)` can stay a bare cross-reference:

  * **D10 / D34 / D35** — how the buffer row is priced. D10 charged the row at the constant
    §9 proves; D34 enlarged `budgetTotal` to accommodate that; **D35 reverses both** and
    charges the paper's own `L₄` at the sharp zero density, under the *named* hypothesis
    `SharpZeroDensity`. See "THE MANDATED LEDGER FLAG" below for the argument, and note that
    the shipped theorems of `ZetaQ/JoinProved.lean` avoid the assumption altogether.
  * **D14 / D17** — the standing repair policy: a demonstrably false statement is repaired in
    place, with the counterexample recorded, rather than preserved.
  * **D16 / D18** — when a row needs an input another file owns, it is threaded in as an
    explicit hypothesis rather than added as a field of `DesignOfRecord`.
  * **D27** — `DesignOfRecord`'s closing clause is PINNED (`ClosingAtDesign`) at §7.2's
    determinate Gevrey prefactor and margin 0, replacing an existentially quantified clause
    that asserted nothing.
  * **D28** — a hypothesis that is unsatisfiable is deprecated, not kept as a convenience.

**The `F<n>` labels** are findings, each argued in full in one of the sections below or in the
file it belongs to. The ones this file cites, with the section that carries the argument:

  * **F18** — `bufferRowProved` was mis-transcribed at [R]'s ζ-only log scale ("three
    statements were false as frozen").
  * **F19 / F24** — the `(T/2π)·ℒ` surrogate for `𝒩/|𝔉|` was false for `Family.qle`, and the
    repair is `famAvgL` ("the RvM lower bound the rows needed was FALSE").
  * **F23** — the ends row's coefficient is `≈ 3.7×10⁵`, not `6`.
  * **F27 / F28** — `ends_row` needed a `Q₀`; `buffer_row_proved` needs the conductor-averaged
    `FamNIIUpper` ("three statements were false as frozen", closing paragraph).
  * **F32** — the family is the primitive χ of modulus `1 < q ≤ Q`, and the assembly's `r₃`
    slot admits only the sharp density ("what still blocks `assembly_at_lamStar`").
  * **F50** — §12.2 is proved in the tree, and `FamRvMLower` still has zero slack at `famAvgL`.
  * **F52** — the `r + ε ≤ 7` constraint, and the margin design that removes it ("§7's two
    assembly clauses").
  * **F58** — the design window must carry a profile.
  * **F59** — `trace_row` is proved eventually in `Q`, not at every design point.
  * **F60 / F61** — the family-count lemmas are carried at the family's own character set
    `F.chars`, with `F.IsFull` where the full-family form is meant; see `ParityCount`.
  * **F63** — the zone row is family-aware.

--------------------------------------------------------------------------------------
## STATUS — THE THREE `sorry`s IN THIS FILE, AND WHY THEY ARE HERE

This file contains **the only `sorry`s in `ZetaQ` outside `ZetaQ/Sieve.lean`**, and all three
are SUPERSEDED statements, kept frozen with the record of why the paper's method does not
reach them as stated. **No proved theorem consumes any of them** — checked by proof-term
reverse-dependency scan (`audit/RevDepZetaQ.lean`), not by grep.

  * `trace_row` — Prop 3.1(i) at EVERY design point. Proved EVENTUALLY in `Q`
    (`trace_row_eventually`, section `TraceRow` at the foot of this file); the pointwise form
    is out of reach of the route's row-2 majorant below `Q ≈ 10¹⁰`, which `DesignOfRecord` does
    not force. See "`trace_row` is proved eventually" below.
  * `frobenius_row` — Prop 3.1(ii) at `F.kappaC = 2 − Pconst`, the paper's TEN-DIGIT constant.
    Not provable at that constant by this route (see "the design window must carry a profile"
    below, and `ZetaQ/JoinCert.lean`). The proved replacement is the row at the CERTIFIED
    four-digit constant, `ZetaQ/HFrob.lean`'s `hfrob_*_of_design`, which is what the shipped
    theorems use.
  * `assembly_at_lamStar` — the eight-clause assembly at the ten-digit constant, downstream of
    the two above. The proved replacement is `JoinCert.assembly_at_lamStar_cert` /
    `JoinProved`'s and `Margin`'s `assembly_at_lamStar_proved*`.

The theorems the artifact ships are the six primed ones in `ZetaQ/Margin.lean`; they route
through none of the three. `theorem_one` / `theorem_one_generic` / `corollary_two_dyadic`
below are the paper's own ten-digit statements, are proved as wiring, and are
`sorry`-DEPENDENT through `assembly_at_lamStar`. Keep the two families of names distinct.

--------------------------------------------------------------------------------------
## RULE 17 for this file

Forbidden: **λ ≤ 1**, **X ≤ T**, **D₀ = √T**. None occurs below.
  * `λ` enters only as `Family.lamStar` (`1.2507321515` / `1.1931581210`, **both > 1**) and
    through `ParamsQ.Valid`, which has `lam_pos` and `lam_lt_two` and NO `lam_le_one`.
  * `X` never appears; the scale is `P.LL = log(QT/2π)`, `P.LB = λℒ` throughout.
  * `D₀` is the FREE field `ParamsQ.D0`. Its side conditions are `10L ≤ D₀ ≤ T/3`,
    `wD₀ ≫ e²A` and the Gevrey closing condition — **none of them is `D₀ = √T`**, and paper
    §7.1 states the stakes: forcing `√T` "makes the ramp row Θ(ℒ^{1−r/2}),
    which breaks the theorem's rate class for every r < 4". At the design of record
    `D₀ ≈ T/1000` at `Q = 10¹⁰⁰`, against `√T ≈ 1.5×10⁴`.
  * `w ≥ 1` (`ParamsQ.Valid.one_le_w`) is **kept** and is NOT a Rule-17 item: it is a
    genuine hypothesis of the reused cap-free ends lemmas, satisfied by the design's clamp
    `w = max(1, w*)`, and it **costs** `6/(λℒ)` in the budget. Recorded, not
    dropped.
  * The buffer counting object is `ZetaQ.NIIFam` at the free `P.D0` (which mirrors
    `Zeta23.Assembly.NIID`, `WindowD.lean:100`), never `Zeta23.Assembly.NII`
    (`Assembly/Inputs.lean:33`), which is definitionally at `√T`.

  A Rule-17 audit was run mechanically over the constant closures of the five headline
  routes (68032 / 66154 / 67413 / 57983 / 57053 constants): **zero gated hits**
  (`Zeta23.D0` and `Params.Valid.lam_le_one` both absent). The `one_le_w` projections that do
  appear are the regime FLOOR `w ≥ 1` the paper itself carries (§10.3, "clamped at the regime
  floor `w ≥ 1` carried by the reused lemmas"). `X` occurs only as `P.XQ = exp P.LB` and is
  **never compared with `T`**; `s₀`, `deltaPrime`, `zoneY` never appear; `P.D0` never appears.

--------------------------------------------------------------------------------------
## THE DESIGN WINDOW MUST CARRY A PROFILE — a flat taper cannot reach `κ_C`

This is the largest correction the library records, and the reason `ZetaQ/Window.lean`,
`ZetaQ/DesignProfile.lean` and `ZetaQ/PayoffSmooth.lean` exist at all. The receipts are
`audit/flat_vs_profile_receipt.py` and `audit/ProductWindow_REPORT.md`.

**The failure.** `κ_C` is defined as `Family.kappaC = 2 − Pconst`, `Pconst = 0.7212835668`
= §11's `min B` over profiles `v = φ²` (paper §4, Lemma 4.2), attained by the `cos(√2 t)`-bulk
profile. But the window the tree actually built was [R]'s FLAT ramp taper
`φ = ϱ((L/2 − |u|)/w)` (`Zeta23/Defs.lean:251`), for which `v` is the indicator of
`[−λ/2, λ/2]` and

    B_flat(λ) = 2/λ − 2/(3λ²) + C(λ/3 − 1/λ + 2/(3λ²)):

at `λ* = 1.2507`, `C = π⁴/18` this is **1.4085520** (the paper's own `fb.flat_v_payoff`), i.e.
`P = 0.5914`; the flat taper's own best `λ ≈ 1.072` gives `B = 1.3105`, `P = 0.6895`. The gap
`1.4086 − 1.2787 = 0.13` exceeds `rowR2` at every design point (`≈ 0.10` at `Q = 10¹⁰⁰`, `→ 0`),
so `frobSqGhatFam ≤ (κ_C + rowR2)·𝒩` **cannot** be proved by §§4–6's route, which delivers the
sieve majorant `C·∫_{|α|>1}|α|ψ` out-zone — exactly `B(v_flat)`. (The statement may be TRUE —
the true family out-zone moment is conjecturally smaller, GRH territory — but not by this
method with that taper.) Same for `corollary_two_dyadic` (flat at `λ*_dyad`: `1.4092` vs
`1.2901`). The defect is a statement-level omission in the paper, inherited by the tree: paper
§2.2 transcribes only the flat `φ(u) := ϱ₂((L/2 − |u|)/w)` (from [R]'s §2.2, the Theorems A–C
window), so what is missing is not a lemma but an OBJECT. [R] itself realises the optimal
profile elsewhere — `Zeta23/ThmD/Window.lean:38`'s `phiD = √(v*(u/L))·φ_flat`, packaged as
`Params.atD` (`ThmD/ParamsD.lean:39`), with the prime-side facts taken from the generic
`AdmWindow` layer (`ThmD/WindowCore.lean`) rather than from the flat facade.

**The repair, carried out.** The construction's window is now the profile-weighted product
`φ = p(u/ℒ)·ϱ₂((L/2 − |u|)/w)` with `p` an even degree-6 polynomial, realised with [R]'s `atD`
idiom so that `phiQ = toParams.phi` stays definitional: `ZetaQ/Defs.lean` `ParamsQ.prof` and
`toParams`; `ZetaQ/Window.lean` the `AdmWindow` instance replacing the flat facade;
`ZetaQ/DesignProfile.lean` the two design profiles, their `ProfileQ` class, moment floors and
Gevrey constant; `ZetaQ/PayoffSmooth.lean` the smooth certificates `B(p²) ≤ 2 − 0.7212`
(q ≤ Q) / `≤ 2 − 0.7098` (dyadic) at the design support, and the §11 link `ProfileRampLink`.
`DesignOfRecord` below pins `ϱ = ϱ₂` and `prof = F.designProfile`. Gevrey survives by Leibniz
(finitely many terms, same `A`, `B′ = B(1 + Σ_j M_j(λ/8A)^j)). The numerics (exact
Gauss–Legendre on the kink-split cells, `audit/profile_sq_poly.py`): degree-6 `p` gives
`B = 1.2787421`, `P = 0.7212579 ≥ 0.7212`, `λ = 1.2428`, `a = 0.788`, `b = 0.689 ≥ 1/2`;
degree 12 would give `P = 0.7212797`.

**Blast radius, as measured before the repair** (`audit/FlatTaperAudit.lean`): direct citations
of the `Zeta23.Taper.*` facade ≈ 23 declarations, `TaperProfile` 9, `Valid.taper` 7,
`Params.crho` 20, `Params.a/b` 32; `ZetaQ.Tail` 45/77 touch the Gevrey/tail chain; `CharSums`,
`Sieve`, `Normalisation`, `Payoff` are window-free. The big theorems reach the flat facts only
through `Ends.S2_localHypsCoreW` (158 facade names in its closure), whose generic twin
`AdmWindow.localHypsCore` exists in [R] (it needs `b = L⁻¹∫φ⁴ ≥ 1/2`, used only for
positivity). `norm_paperFT_le_gevrey` is generic in the L¹-derivative bounds; only the ramp
lemma `Taper.integral_abs_iteratedDeriv_phi_le` (which uses the plateau) needed a
product-window twin.

**The alternative that was NOT taken**, recorded because it is the cheap way out: keep the flat
taper and restate at `λ ≈ 1.072`, `κ_C = B_flat(λ)` in closed form, `P ≈ 0.6895`. Lean closes
fast; the headline is downgraded by 0.03.

--------------------------------------------------------------------------------------
## `trace_row` IS PROVED EVENTUALLY IN `Q`, FOR BOTH FAMILIES — and only eventually

`trace_row_eventually` (section `TraceRow`, foot of this file) proves Prop 3.1(i) for all
sufficiently large `Q`. The statement at EVERY design point stays `sorry`, because the row-2
(prime-part) bound is a power saving in `Q` that only bites near `Q ≈ 10¹⁰`, and nothing in
`DesignOfRecord` forces `Q` that large.

* **The prime side is proved outright.** `trGhatFam_eq_split`: `trGhatFam = (aL²)⁻¹(famMuPart
  + famPPart)` — ledger row 1 plus row 2. Row 2 is `famPpart_le` /
  `abs_trGhatFam_sub_muPart_le`, from `P.Valid` and `8w ≤ L` alone. The per-character P-part
  bound is `L²√X/log 2`; summed naively over `|𝔉| ≈ 0.185Q²` characters it is hopeless.
  `CharSums.lemma5_2_crude_linear` replaces the per-`n` factor `|𝔉|` by
  `‖Σ_{q,χ}χ(n)‖ ≤ (3/2)Qτ(n−1) + 1` — **a full power of `Q`**. The row-2 error is then
  `≈ 8.7·Q·L²·√X` against `rowR1·𝒩 ≈ 0.00187·Q²T`, a ratio `≈ 2360·ℒ²·(QT)^{−0.3746}`, i.e.
  `≈ 10⁻³²` at `Q = 10¹⁰⁰`, dropping below 1 near `Q ≈ 10¹⁰`. **Row 2 costs nothing at any
  printed design point, and `rowR1`'s constant is NOT the obstruction** — it would be
  affordable even at `L₆/40`.
* **The chain (section `TraceRow`).** (B) `muPart_chi_approx`: `MuqUniform.muPart_approx_ell1`
  through `Ends.S2_localHypsCoreW` (window constant `cWin`). (C) `famRvM_upper_raw`: the
  two-sided `EFChi.rvmChi_main_uniform` summed (upper half; `famRvM_lower_raw` is the lower).
  (D) `famMuPart_ge`, `muPart_ge_NfamQ_sub`:
  `(aL²)⁻¹·famMuPart ≥ 𝒩 − |𝔉|·(A·log(Q(T+2)) + muErr/(aL²))`. (E-a)
  `rowR1_NfamQ_lower_eventually`: `c_F·|𝔉|·T ≤ rowR1·𝒩` with `c_qle = 1/100` (from
  `famRvMLower_of_design`, the exact §12.2 average, at `ℒ ≥ 30`) and `c_dyad = 1/200` (from
  `ℓ_{1,q} ≥ ℒ + log 2 − 1` for `q > Q/2`, RvM's error at `T/400π`). (E-i) `rvm_error_small`.
  (E-ii) `muErr_div_le`: `muErr/(aL²) ≤ cErr(c_W) = (4/3)(K(16+2c_W+2c_W²)/2π + 47)`, ONE
  number per family at the design (`cWin_of_design`: `c_W = cWinDesign F`), absorbed by
  `T ≥ 400π·cErr(c_W)` eventually. (E-iii) `row2_eventually`: the row-2 term
  `≤ c_F|𝔉|T − 2|𝔉|·T/(400π)` eventually — `qle` from `Row2Numeric.row2_error_eventually` +
  `sizeR_qle_lower'`; `dyadic` from `row2_error_eventually_gen` at `1/4000`, monotonicity in
  `L` (`λ*_dyad < λ*`) and `sizeR_dyadic_lower` (`|𝔉| ≥ (3/4)(18/π⁴)Q² − 8Q(1+log Q)²`, from
  `N2.Astar_bound` twice). (F) `trace_row_eventually_aux` feeds `trace_row_of_muPart`;
  `trace_row_eventually` is the `∃ Q₀` form in `assembly_at_lamStar`'s shape. Every declaration
  is `[propext, Classical.choice, Quot.sound]`.
* **Why not at every design point.** `trace_row_of_muPart`'s `hmu` is `rowR1·𝒩 ≥ (row-2 bound)
  + (RvM error) + (μ-part error)`. The row-2 bound
  `(aL²)⁻¹·L³√X(3Q(1+L)+2)/log 2 ≈ 8.7·Q·L²·√X` against `rowR1·𝒩 ≈ 0.0101·|𝔉|·T` is the ratio
  `≈ 2360·ℒ²·(QT)^{−0.3746}` above: `> 1` below `Q ≈ 10¹⁰` (at `Q = 10³`, `r = 3`, `T = 330`:
  `≈ 10⁹` against `≈ 6×10⁵`). `DesignOfRecord` gives only `Q ≥ 3`, `T ≥ 300`,
  `10ℒ log ℒ ≤ T`, `10L ≤ D₀ ≤ T/3` and the closing condition — none implies `Q ≳ 10¹⁰`; and
  the μ-part error needs `T ≥ 400π·cErr(c_W)` with `c_W ≥ 4`, i.e. `T ≳ 10⁵`, which `T ≥ 300`
  does not give either. So the eventual form is what this route proves; `trace_row` at small
  `Q` is NOT refuted (the true prime part is presumably far below its Ramanujan majorant), it
  is out of reach of the bound. Rule 17: the route runs at `λ* > 1` through the cap-free
  `LocalHypsCoreW`; `X` is never compared with `T`; `D₀` never appears.
* **Downstream.** `assembly_clauses_at_design` consumes `trace_row` at ONE design point, but its
  only consumer `assembly_at_lamStar` is `∃ Q₀, ∀ Qn ≥ Q₀, …`, so the eventual form SUFFICES for
  the join: thread `htr : (1 − rowR1)𝒩 ≤ trGhatFam` as a hypothesis of
  `assembly_clauses_at_design` (as `hrvm`/`hsharp` already are) and take `Q₀` as the max with
  `trace_row_eventually`'s threshold. That rewiring is NOT done here; note that
  `trace_row_eventually` sits AFTER `assembly_at_lamStar` in this file because it needs the
  `TraceRungs` section, so citing it there needs a reordering or a forward-stated hypothesis.

**Why the per-character seam is dead at `λ* > 1`, settled on the mechanism.**
`EFChi.gridGramEntry_eq` identifies §3's `gridGramEntry` with `Zeta23.ThmE.GentryChi`, and
`rtrace_hatQ_gridGram_eq_Gz` / `frobSq_hatQ_gridGram_eq_Gz` identify the prime-side hat moments
with the zero-side `Ĝ_χ`. Those are **identities, not evaluations**: they move the trace to the
zero side, where the only quantitative seam in the graph is `Zeta23.ThmE.seamBChi`
(`Zeta23/ThmE/AssemblyQ.lean:239`), whose error term is `C₁·√X/a` with `X = (QT/2π)^λ`. At
`λ* = 1.2507 > 1` that is `(QT/2π)^{0.625}`, which **exceeds `𝒩` itself** — `10^{67}` against
`7×10^9` per character at `Q = 10¹⁰⁰`, and still larger after summing over `𝔉_Q`. That is
exactly why the paper does not go through the per-character seam but through §5's family
Ramanujan orthogonality and §§4–6's two-zone decomposition, which live in
`ZetaQ/CharSums.lean`, `ZetaQ/Zones.lean` and `ZetaQ/Sieve.lean` — none of them on this file's
path, and none of them expressible as a non-circular `Prop` in
`trGhatFam`/`frobSqGhatFam`/`NfamQ`. (The whole cap-free core under `prop_trace_chi` is
citable: `prop_trace_chi` (`PrimeSideChi.lean:820`) itself carries `lam ≤ 1`, but one layer
down `P_part_chi_eq` (`:544`), `Aphi_mul_norm_tauKernel_le` (`:455`), `sum_P_part_chi_bound`
(`:730`), `GentryChiA_diag_eq` (`:708`), `muq_part_bound` (`:598`), `muq_part_integrable`
(`:653`) and `PXc_part_integrable` (`:679`) are all typed over `LocalHypsCoreW` and all
λ-cap-free.)

--------------------------------------------------------------------------------------
## THE ZONE ROW IS FAMILY-AWARE

`zoneRowLinear F P = F.sZoneF·(1 − zoneFactor P)`, with `sZoneF qle = sZone = 0.5073` and
`sZoneF dyadic = sZoneDyadic = 0.5485` (paper §10.5).

**What went wrong when it was not.** A single `zoneRowLinear P = sZone·(1 − a)` priced BOTH
families' zone rows at the `q ≤ Q` secant `0.5073`, although `sZoneDyadic = 0.5485` was already
defined ("recorded, not used"). `ZoneData.dyadic_margin_fails` proves that the dyadic design
profile's zone cost `2(C_dyad − 1)ψ(1) = 0.5456` EXCEEDS `0.5073`, so the dyadic Frobenius
clause (`frobenius_row` at `rowR2 Family.dyadic`, hence `corollary_two_dyadic`) could not hold
asymptotically as written; against `sZoneDyadic` it holds with margin `0.0028`
(`ZoneData.zoneLipschitzDataDyadic`).

**The fix.** `Family.sZoneF`; `zoneRowLinear F P`; `rowR2 F P` and `budgetTotal F P` through
it; every consumer follows (`row_zone`, `rowR2_nonneg`, `HPre.rowR2_le_of_facts` — its crude
`79` is unchanged —, `FrobAssembly.ZoneLipschitzData` (margin against `F.sZoneF`), `ZoneData`,
`HFrob`, `JoinProved`, `Margin`). For `Family.qle` NOTHING moves (`sZoneF_qle :
Family.qle.sZoneF = sZone` is `rfl`), so `budgetTotal Family.qle` still reproduces the paper's
own TOTAL column. Consequence: `HFrob.hfrob_dyadic_of_sep` is the exact dyadic row
`‖Ĝ‖²_F ≤ (κ_cert + rowR2 Family.dyadic)·𝒩`, and `JoinProved.corollary_two_dyadic_proved'` has
NO named hypothesis (its only `sorryAx` comes through the Sieve).

--------------------------------------------------------------------------------------
## §7's TWO ASSEMBLY CLAUSES, AND A REAL CONSTRAINT ON `r`

`hblock` (checklist item 6) is **DISCHARGED**; `hpair` (item 4) reduces to two named inputs,
one of which is not in the tree — and reducing it exposed a genuine constraint on `r`.

* **`hblock` was never missing mathematics — it was unwired.** `ZetaQ.theta0Fam` and
  `ZetaQ.theta0Q_le_theta0Fam` (`ZetaQ/Tail.lean`) are *"one `θ₀` for every conductor
  `q ≤ Q`"*, PROVED, and were cited by nothing outside `Tail.lean` — while item 6 called the
  common `θ₀` the missing piece. The chain `EFChi.localCountChi_uniform` →
  `TailHypQ.of_profile` → `TailHypQ.tailInputsQ` → `theta0Q_le_theta0Fam` is all proved; the
  only genuinely new lemma is `tailInputsD_mono`.
* **`hconj` is FREE, everywhere.** `Zeta23.Params.phiHat_conj` (`Zeta23/Taper.lean:47`) is
  hypothesis-free, yet every docstring in `Tail.lean` used to treat `hconj` as a side condition
  to be supplied by the caller.
* **⚠ THE FINDING: `hpair` at the design constrains `r + ε ≤ 7`.** The standing premise — that
  `θ₀` is *superexponentially small* — is FALSE at the design of record. `ClosingAtDesign` pins
  the closing condition at margin **0** and `η = 1`, which is what paper §7.2 asserts of the
  design ("sits ON the constraint by construction … the margin is 0 nats at every Q"); the
  `exp(−c₄√(wD₀/A))` is then exactly cancelled by `e^{L/2}·prefactor`, and the sharpest `θ₀`
  available is `Θ(1/L)`, not superexponential. At `θ₀ = 1/L` the dominant pair term is
  `2·rowR5·√(κ_C+r₂)`, and against `L₅ = 6ℒ log ℒ/T` the clause reduces to roughly

      √T  ≤  0.46 · ℒ^{3.5} · log ℒ,

  i.e. **`r + ε ≤ 7`**, since `T = (log Q)^{r+ε}` and `ℒ ≍ log Q`. At the design of record
  (`r + ε = 3.5`, `Q = 10¹⁰⁰`) that is `1.4×10⁴` against `6×10⁸` — 4.6 orders of margin — so
  **nothing about Theorem 1 at the design moves**. But `assembly_at_lamStar` is stated for
  *every* `r ≥ 3`, and at `r > 7` this route fails at large `Q`. `L₉` does not help: it is also
  `Θ(1/T)`. The way out taken by the shipped theorems is a sharper `hpre` — a margin of `m`
  nats gives `θ₀ ≤ e^{−m}/L`, and any `m = Ω(log ℒ)` restores all `r`; that is
  `ClosingAtDesignM` / `DesignOfRecordM` below and `ZetaQ/Margin.lean`.
* **`hpre` is the one genuinely missing analytic input.** Unfolded it is
  `A₀·sideWQ L (w/A) (4/e) (2T+4) D₀ Q ≤ (ℒ + log 4T)·rowSumFactor²` — LEMMA_QT §QT.b(4)→(5).
  Nothing anywhere relates `prefactorQ`/`prefactorG` to `logPrefactorGev`:
  `theta0Q_le_of_closing` and `ClosingAtDesign` had never been connected, which is why item 4
  looked like bookkeeping. It is proved in `ZetaQ/HPre.lean`.
* **Namespace note.** `ZetaQ/Tail.lean` opens only `namespace ZetaQ` — there is **no `Tail`
  namespace**. Citations here are `ZetaQ.theta0Fam`, `ZetaQ.theta0G_le`, `ZetaQ.prop_tailQ`,
  `ZetaQ.CenvQ`, `ZetaQ.card_famIdx`.

--------------------------------------------------------------------------------------
## §12.2 IS PROVED — AND `FamRvMLower` STILL CANNOT BE DISCHARGED

* **§12.2's family conductor spread IS proved in the tree.** Three docstrings here used to say
  it "is not proved anywhere in the tree" (`FamRvMLower`, `FamNIIUpper`, and the RvM-surrogate
  block). All three were wrong. It is `Normalisation.avgLogCond_asymp` (N6) and
  `avgLogCondDyadic_asymp` (N7) — and, in the form actually usable,
  `Normalisation.N2.Alog_bound`, which carries an EXPLICIT two-sided error at every `N`.
  `Budget → Zones → Normalisation`, so all of it was citable from here with no import change.
  The N6/N7 limits match `Family.conductorShift` exactly (`1/2`; `1/2 − log2/3`).
* **`FamNIIUpper`'s stated reason for being a `Prop` was also false**: it said `Budget.lean`
  does not import `EFChi`, but it does. `NIIFam_avg_le` below is the "re-proved one step
  earlier" form that docstring asks for, for both families.
* ✅ **`famRvMLower_of_design` IS proved**, once the surrogate was lowered — see `rvmSlack`.
* **The finding: `FamRvMLower` AT `famAvgL` has ZERO slack by construction and is not reachable
  there, in any eventual form.** `ell1q q T = log(qT/2π) + 2log2 − 1`, so the φ*-average of
  `ell1q` over `𝔉_Q` is `ℒ − ⟨shift⟩ + 2log2 − 1` — **exactly** `famAvgL`. That surrogate was
  chosen deliberately, and the price is that this `Prop` asserts RvM's aggregate error is
  favourably signed. `EFChi.rvmChi_main_uniform` is two-sided. Shortfall `≈ 2πA/T`, i.e.
  `Θ(1/T)` relative.
* **The repair its docstring used to propose does not exist.** The `0.0397`-nat slack is
  `(2log2 − 1) − (log2)/2`, the BUFFER comparison; it belongs to
  `buffer_row_sharp`/`SharpZeroDensity`. In `FamRvMLower` there is nothing to absorb into.
* **`FamNIIUpper` is short only by the §12.2 residue**, `Θ(log³Q/(Q·ℒ))` relative, and even
  that cannot be signed away: `⟨log q⟩_{φ*} − log Q + ½` **oscillates in sign** (measured to
  `N = 4×10⁵`). `famNII_upper_eps_from_tree` proves the statement verbatim except
  `⟨shift⟩ ↦ ⟨shift⟩ − ε`, for every `ε > 0`, with no free hypotheses. The `Prop` itself is
  **not refuted** — `A₀ = 81.26` carries ≈214× slack over the measured local count.
* **Consequence for the ledger, recorded and NOT patched.** An RvM row of size `Θ(1/T)` is
  owed. It is dominated by `L₄ = 6D₀/T` (`D₀ = Θ(ℒ²)`), so no printed figure and no rate class
  moves.

--------------------------------------------------------------------------------------
## THE RvM LOWER BOUND THE ROWS NEEDED WAS **FALSE** FOR `Family.qle`

The rows `rowR3`/`rowR4`/`rowR5` used `(T/2π)·ℒ` as an *equality* surrogate for `𝒩/|𝔉|`,
citing §7.3's `𝒩 ≍ |𝔉|(T/2π)ℒ`. The `≍` is off by exactly the conductor-spread row `L₆`, and
it leans the wrong way. Summing the q-uniform RvM over the family,

    𝒩 = |𝔉|·(T/2π)·(ℒ − ⟨shift⟩ + 2 log 2 − 1) + O(|𝔉|·log QT),
    2 log 2 − 1 = +0.386294,   ⟨shift⟩ = 1/2 (qle) or 1/2 − (log 2)/3 = 0.268951 (dyadic),

so `𝒩 = |𝔉|(T/2π)(ℒ − 0.113706)` for **`Family.qle`** — strictly BELOW `|𝔉|(T/2π)·ℒ` — and
`|𝔉|(T/2π)(ℒ + 0.117345)` for `Family.dyadic`, strictly above. The deficit `0.1137·(T/2π)` per
character dominates the RvM error term `A·log(q(T+2)) = O(ℒ + log T)` by a factor `≈ T/ℒ` (at
the design `T = 1.85×10⁸`, `ℒ = 247.7`), so it is not an artefact of the error term.
**Consequently `pair_rows` was FALSE for `Family.qle` at every `θ₀ > 0`** — its first conjunct
is *equivalent* to `|𝔉|(T/2π)ℒ ≤ 𝒩`, and its second to the same inequality under `√`. A named
hypothesis `|𝔉|(T/2π)ℒ ≤ 𝒩` was deliberately NOT added: it would be unsatisfiable for
Theorem 1's own family, i.e. it would make the theorems vacuous rather than blocked.

**The repair, made in the tree.** `famAvgL F P := ℒ − ⟨shift⟩ + (2 log 2 − 1)` — the true
family average `𝒩/(|𝔉|(T/2π))` — replaces `ℒ` in `rowR4`, `rowR5` and `SharpZeroDensity`, so
the conductor spread is priced once (in `L₆`) instead of twice. `FamRvMLower` names the family
RvM **lower** bound at that average and is threaded into `pair_rows` and `buffer_row_sharp`
explicitly. At the true average it is satisfiable for **both** families, which is the entire
difference between a vacuous hypothesis and a real one. **`pair_rows` and `buffer_row_sharp`
are now PROVED.** Cost: `4.6×10⁻⁴` relative at `Q = 10¹⁰⁰`, invisible in §10.4;
`rowR4`/`rowR5` are absorbed by `hpair` inside `propBracket_le_budgetTotal`, so **Theorem 1
does not move**. Details at `famAvgL`.

--------------------------------------------------------------------------------------
## THREE STATEMENTS IN THIS FILE WERE FALSE AS FROZEN, WITH COUNTEREXAMPLES

The standing policy of this library is that a demonstrably false statement is repaired, not
preserved. Each repair is recorded in the docstring of the declaration it touches: what was
wrong, the failing instance, what it now says, and why the new form is the paper's claim
rather than a weakening.

  * **`bufferRowProved` was mis-transcribed** at [R]'s ζ-only `3A₀D₀·log(4T)` where
    the q-uniform §9 bound (which its own consumer's hypothesis `hloc` assumes, and which
    `ZetaQ.EFChi.NII_fam_le` proves) is `3A₀D₀·log(4qT) = 3A₀D₀(ℒ + log 4T)`. As coded,
    `bufferRowProved/L₄ = πA₀·log(4T)/ℒ` crosses 1 near `Q ≈ 10³⁴⁰⁰`, beyond which the
    "proved" row sits *below* the sharp density — so `buffer_row_gap` and
    `buffer_row_proved` were both false there. **Repaired:** `bufferRowProved` now carries
    the q-uniform summand, at which the ratio is the constant `πA₀ ≈ 255` at every `Q`.
    `buffer_row_gap` is repaired (also taking `P.Valid`, without which `P.Q = 0` gives
    `P.LL = 0`) and is now **PROVED**. `bufferRowProvedQ` / `buffer_row_gap'` survive as
    one-line aliases so nothing that cites them breaks.
  * **`propBracket_le_budgetTotal` was false twice over** — by the un-folded `3·L₆` residue,
    and, fatally and independently, because `θ₀` carried only `0 ≤ θ₀` while `rowR4` is
    linear in it, so the left side was unbounded above. **Repaired:** `rowR1 := L₆/4` (the
    reading under which `budgetTotal` is the paper's own TOTAL column and §10.4's
    `P_eff = P − TOTAL` reproduces), and §7's closing bound on `θ₀` enters as the explicit
    hypothesis `hpair` it always had to be. Now **PROVED**.
  * **`budgetTotal_isBigO` was false** because `DesignOfRecord` does not pin `D₀` from
    above: `SideCondD0range` permits `D₀ = T/3`, at which `L₄ = 6D₀/T = 2`, a constant, and
    the closing clause is vacuous as written (`logPrefactor` is existentially quantified and
    unconstrained, so taking it very negative satisfies it for every `P`). **Repaired** by
    the explicit hypothesis `hD0 : D₀ = O(ℒ²)`, which is exactly what §7.2's margin-0
    closing condition forces and exactly what `DesignOfRecord` failed to carry — and the
    vacuity itself is repaired by `ClosingAtDesign`, so `D0_le_of_design` now proves
    `D₀ ≤ 2×10⁴(log Q)²` outright and `budgetTotal_isBigO_of_design` needs no side
    hypothesis.

Two further defects of the same kind, both repaired and both recorded at their declarations:
`ends_row` was FALSE as frozen (it fails by 1.93× at `Qn = 12, r+ε = 6.32`, by 1.39× at
`Qn = 65, r+ε = 4`, by 1.29× at `Qn = 100`, and first holds near `Qn = 10³`), because
`DesignOfRecord` carries no `Q₀` — repaired by the explicit `hQ0 : endsQ0 ≤ P.Q`,
`endsQ0 = 10¹⁶`, which is four orders below §10.4's own "non-vacuous from ≈ 10²⁰"; and
`buffer_row_proved` needs `FamNIIUpper` at the **conductor-averaged** step, NOT at its printed
`log q ≤ ℒ` form, from which the row would be *equivalent* to `⟨shift⟩ ≤ 2 log 2 − 1`, false
for `Family.qle` by the same `0.1137` nats.

--------------------------------------------------------------------------------------
## THE ENDS ROW'S COEFFICIENT IS `≈ 3.7×10⁵`, NOT `6`

`ZetaQ.Ends.ends_family_bound` is proved, so the ends relative-order constant is a computed
quantity. The ORDER `Θ(ℒ log ℒ/T)` is right; the coefficient is not. NOTE_QR §QR.1's displayed
lemma and its own "relative order" chain disagree by the whole bracket
`[4(90+32c_ϱ²) + C₂′(1+log L)] ≈ 3.6×10⁵`, and the chain — which is what produced the paper's
≈ 5.7 — dropped it. `ZetaQ.Ends.ends_relative_le` is restated and **PROVED** at the true
constant. Here that is recorded as `cEndsProved`/`L₅proved`; `L₅` and `budgetTotal` are left at
the paper's printed `6`, exactly the convention used for `L₄`. **Theorem 1 is untouched;
§10.4's finite-Q table is not** — see `L₅proved`.

Two different ends constants appear below and must not be conflated: `≈ 3.7×10⁵` is the
RELATIVE-ORDER constant of `Ends.ends_relative_le`, while `cEnds = endsRowConst ≈ 2.5×10⁶`
is the ROW constant `10·C₁ + 47·C₂′`, and both are quoted at the window-constant floor
`c_ϱ = 4`, which no ramp attains — `Ends.endsRowConstC c` is the honest function of `c`.
See `cEnds` for the arithmetic.

--------------------------------------------------------------------------------------
## WHAT STILL BLOCKS `assembly_at_lamStar`

Itemised at the statement. The design-point construction is a THEOREM
(`exists_designOfRecord`): the obligation to solve
`c₄√(wD₀/A) = L/2 + logPrefactorGev P + log L` for `D₀` and meet the five side conditions at
the root is carried out by `exists_root_of_signs` (the IVT, `intermediate_value_Icc` plus
continuity of the gap), `closingAtDesign_of_root` (the root equation IS `ClosingAtDesign`, the
two `log L` terms cancelling), and `design_low_sign` / `design_high_sign` (the two endpoint
signs at `10L` and `T/3`). Witness: `λ = λ*`, `w = 1`, `T = (log Q)^{r+ε}`, taper from
`Zeta23.exists_taperProfile`, `D₀` the root, floor `log Q ≥ 200`.
`Zones.exists_designFamily_regime` is NOT reusable (`λ=1, w=1, D₀=2` fails `SideCondD0range`,
`SideCondWD0` and `ClosingAtDesign`).

What remains are `hsharp`/`hNII` (§9), `hrvm` (§12.2 at finite `Q`), `hpair` and `hblock` (§7,
coupled to each other), `hZc`/`hB` (§9's seam), and `trace_row`/`frobenius_row`. The family is
the primitive χ of modulus `1 < q ≤ Q`: `Family.moduli Family.qle Qn` is `Finset.Icc 2 Qn`, so
`hZc`/`hB` are not blocked by a `q = 1` member (ζ's zero configuration for the unique primitive
character mod 1, for which H2 has no pole-free form). `Family.size`'s `qle` body is written out
over the same `Icc 2 Qn` rather than citing `famCard` (whose range is `Icc 1 Qn`) so that
`sizeR` stays exactly `|𝔉_Q|`: that keeps `Btr`/`BF`, `SharpZeroDensity`, `FamRvMLower`,
`FamNIIUpper` and `FamSizeLower` at their intended meanings and keeps `ZetaQ.card_famIdx`
(`|famIdx| = sizeR`, `rfl`) an identity — the alternative was checked and **breaks
`ZetaQ/Tail.lean`**. The residue is one `Defs`-level step, `sizeR = famCard − 1` for
`Family.qle`, `O(Q^{-2})` relative; recorded at `ZetaQ.Family.size` and `ZetaQ.FamRvMLower`.

`assembly_clauses_at_design` proves the ENTIRE eight-clause body of `assembly_at_lamStar` at
one design point, from six named inputs, modulo `trace_row` and `frobenius_row`. Route:
`EFChi.prop31_fam` (§9's family display `certificate_display_fam_of_bridge` composed with
Prop 3.1) fed by `ZetaQ.Tail`'s two §7.3 pair-split exports
`abs_trGz_sub_trAhat_fam_le_Btr` / `sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF`, joined to
this file's four row lemmas. The two side conditions those exports carry (`hl : l T ≠ 0`,
`hB0 : 0 ≤ θ₀/(aL)`) are **discharged**, not hypothesised: `EFChi.l_ne_zero_of_valid` and
`a ≥ 3/4` from `Valid` + `SideCondWrange`.

`payoff_rate_of_assembly` is the rate step re-indexed over the naturals, and that re-indexing
is necessary rather than cosmetic: `payoff_rate_of_designs` wants `design : ℝ → ParamsQ` with
`∀ᶠ Q in atTop` over ℝ, while the assembly produces design points at natural `Qn` only and
`DesignOfRecord … Q P` pins `P.Q = Q`, so no real-variable design map is extractable from it.

--------------------------------------------------------------------------------------
## 🚩 THE MANDATED LEDGER FLAG — the buffer row L₄

Paper §10.3, verbatim:

> buffer 6D₀/T — priced at the **SHARP zero density** (N_II at the true T/2π-per-χ scale),
> not at the proved absolute A₀ of §9, which is larger: charging the proved constant would
> move the finite-Q thresholds, never the asymptotics, and §10.4 states which convention
> its table uses

and §10.4, verbatim:

> the buffer row at the sharp zero density (§10.3 — **the one row NOT charged at its proved
> constant**)

**Lean consequence: `L₄` is NOT dischargeable from H6 alone.** What §9/H6 proves is
`N_{II,χ} ≤ 3·A₀·D₀·log(4qT)` with the *absolute* `A₀` — in Lean already, as
`Zeta23.Tail.NIID_le` (`Zeta23/Tail/GevreyTail.lean:1878–1881`) for ζ, and q-uniformly as
`ZetaQ.EFChi.NIID_chi_le` / `NII_fam_le`. What the budget charges is `6·D₀/T`, i.e. `N_II`
at the sharp density `T/2π` per character. The two are stated separately below (`L₄` and
`bufferRowProved`, `buffer_row_sharp` and `buffer_row_proved`), and the gap between them is
its own named statement, `buffer_row_gap`, whose direction (`L₄ ≤ bufferRowProved`) is
exactly the wrong way round for discharging `L₄` from `H6`.

**Which convention this file ships.** `L₄`/`rowR3` are the rows `budgetTotal` charges and
`buffer_row_sharp` is the row lemma the assembly consumes; its hypothesis **`SharpZeroDensity`
is the assumption, stated**, and it is the paper's own — §10.3 flags this row as priced at the
sharp density and §10.4 calls it "the ONE row not charged at its proved constant", so an
artifact that charged `≈ πA₀ ≈ 255×` more would be a *different* accounting presented as the
same one. The pattern is `ZetaQ.l2_concentration_exists`, which likewise names §6's cited
Lemma 6.1 instead of re-proving it: **two named, paper-declared assumptions, and everything
else proved.** (The shipped theorems of `ZetaQ/JoinProved.lean` and `ZetaQ/Margin.lean` do
*not* even assume this one: they charge `bufferRowProved` instead, at the price of a larger
effectively-computable `c(ε)`.)

`bufferRowProved` / `bufferRowProvedQ`, `buffer_row_proved`, `buffer_row_gap` /
`buffer_row_gap'`, `one_le_A0` and the private `A0_bounds` / `bufferProved_le_L4` are all
**retained**: they are the record of what §9/H6 *does* prove outright, and of the size and
direction of the gap between the two conventions. That disclosure is what makes the assumption
honest rather than hidden. The finite-Q arithmetic is kept at `budgetTotal`: proved-buffer :
rate-term `= 84 / 23 / 9.7 / 4.3` at `Q = 10²⁵ / 10¹⁰⁰ / 10³⁰⁰ / 10¹⁰⁰⁰`.

**Net effect on §10.4.** At the proved constants the non-vacuity threshold moves from `≈10²⁰`
to `≈10²⁹⁰`; the buffer row is `≈20%` of that damage and charging it at the sharp density
removes its share at zero cost to rigour. The ends row at the constant Lemma 8.2 delivers
(`L₅proved`) is the other `≈80%`, and it stands.

--------------------------------------------------------------------------------------
## §10.2 — the 17-row ledger (the error-term taxonomy)

Recorded as a table rather than as Lean objects: it is a *classification of terms*, and
each row's mathematics lives in its own file. Classes: [P]
pointwise-summable, [R] linear-in-χ orthogonality (Ramanujan), [CS] Cauchy–Schwarz-in-χ +
LS via B_fam, [LS] the positive-form large-sieve consumption, [X] exact orthogonality,
[M] mechanical mirror of the record's file.

|  # | term                                              | class    | size            | § | budget row |
|---:|---------------------------------------------------|----------|-----------------|---|-----------|
|  1 | trace, μ_q-part (conductor (log q)/2π; parity κ(χ))| [P][M]   | **main**        | 9, 2.2 | — |
|  2 | trace, prime part                                 | [R]      | power saving    | 5, 9 | absorbed |
|  3 | RvM per character                                 | [P]      | O(1/T)          | 9 | absorbed |
|  4 | H-EF per character (Gz = Gp, Weil, no pole)       | [M]      | in 3, 5         | 9 | — |
|  5 | archimedean layer (no Stirling regime)            | [P]      | O(polylog/T)    | 9 | absorbed |
|  6 | ends 𝓔₁ (grid truncation)                         | [CS]     | Θ(ℒ log ℒ/T)   | 8 | **L₅** |
|  7 | ends 𝓔₂ (outside I×I)                             | [CS][M]  | same as 6       | 8 | **L₅** |
|  8 | 𝓜[μ,μ]                                            | [P][M]   | **main**        | 4 | — |
|  9 | 𝓜[μ,P] cross                                      | [R]      | power saving    | 5 | absorbed |
| 10 | 𝓜[P,P] diagonal (coprimality-corrected)           | [P][M]   | **main**        | 4 | **L₃** |
| 11 | 𝓜[P,P] off-diagonal, low–low                      | [X]      | Q^{−δ′+2ε}      | 5 | **L₂** |
| 12 | 𝓜[P,P] off-diagonal, high zone                    | **[LS]** | **it IS κ_C**   | 4, 6 | — |
| 13 | zone-boundary cross (Lemma 4.4)                   | [CS]     | o(1)            | 4 | **L₇** |
| 14 | grid resonance shells                             | [P]      | negligible      | 4, 9 | **L₁₀** |
| 15 | tail zeros (θ₀ operator-norm; D₀ buffer width)    | [M]      | ramp + buffer   | 7 | **L₃**, **L₄** |
| 16 | Π_X pole terms (ζ only)                           | —        | **absent**      | 2.2 | — |
| 17 | zero-side seam/inertia at λ* = 1.2507             | [M]      | —               | 3 | — |

One bookkeeping caveat, recorded: the enumeration this table follows predates **Lemma 4.5**,
whose in-zone cross row is `L₁₂` and is a distinct object from row 13 — on the current text the
ledger arguably has 18 rows.

--------------------------------------------------------------------------------------
## Discrepancies D-1 … D-5 between the paper's prose and its own scripts — all immaterial

**D-1.** Lemma 4.5's prose quotes `δP ≈ 1.6×10⁻⁴` at `Q = 10¹⁰⁰`; the
script's `L₁₂ = 0.35·C·2.763953·√(log L/(TL))` evaluates to **5.41×10⁻⁵** there, ~3× smaller.
The prose's "ρ_U ≈ 5×10⁻⁴" coincides exactly with **Lemma 4.4's** row value (`minor` term 2
= 5.389×10⁻⁴), i.e. the Lemma 4.5 prose appears to quote Lemma 4.4's number. What *does*
reconcile exactly is the paper's "the in-zone charge is ~50× larger":
`L₁₂/L₈ = 0.35·C/(dP/dlogC) = 56.6×`. ✔ L₁₂ is three orders below the total at every Q, so
nothing downstream moves.

**D-2.** §4's cross-term figures mix two designs: the paper's "δP ≈ 2×10⁻⁵ at
Q = 10²⁵ falling to ≈ 3×10⁻⁶ at 10¹⁰⁰" is the **r = 3.5** value at 10²⁵ (1.88×10⁻⁵) and the
**r = 3** value at 10¹⁰⁰ (3.74×10⁻⁶); at r = 3.5 the 10¹⁰⁰ value is 9.57×10⁻⁷. (The paper is
self-aware about this in Lemma 4.4 but not in Lemma 4.3.)

**D-3.** §10.3 writes the zone breakpoint as `s·(log T)/ℒ`; the paper's own design scripts
compute `s·(log T − log 2π)/ℒ`. §2.2's `ℒ := log(QT/2π)`
makes `l = log(T/2π)` the consistent quantity, so the prose is shorthand. **`L₁` below uses
`Zeta23.l P.T = log(T/2π)`, per this resolution.**

**D-4.** The `zone` row is **not** `L₁ + L₂`. The design script sets
`a = (1 − δ′)(1 − l/ℒ)` and charges `zone = P(C,1) − P(C,a)` — the two zone effects compose
**multiplicatively inside the payoff**, not additively; the linear model `s·(1 − a)` is the
no-curvature fallback. Both are `s(r+K)·log ℒ/ℒ` to leading order. Below: `zoneRowCurv`
is the script's form (payoff passed as a parameter, since §11's `P(C,·)` lives in
`ZetaQ/Payoff.lean`), and `zoneRowLinear` is the fallback used in `budgetTotal` so that the
total has a real body.

**D-5** (a confirmation, not a discrepancy). Every §10.4 headline figure reproduces exactly
from the paper's own Table 2 run: `P_eff = +0.20 / +0.61 / +0.68 / +0.71 → 0.72128`;
non-vacuous from ≈ 10²⁰; > 0.5 from ≈ 10⁵¹; > the per-character record from ≈ 10²³⁶;
`w* = 1.00` at 10¹⁰⁰; `wD₀/ℒ² = 3.80` at 10¹⁰⁰; measured rate constants 3.560 (6w/L) / 3.450
(4w/L) at `log Q = 2.3×10⁶` against `s(r+K) = 3.297`. The four calibration gates pass.

--------------------------------------------------------------------------------------
## Accounting note, from §10.3's own reading

§10.3's rows are the **priced** relative errors — Prop 3.1's coefficients `4, 1, 3, 4` are
already folded into the row constants (e.g. the buffer row `6D₀/T` is `3·r₃` at
`r₃ = 2D₀/T`). `budgetTotal` below is therefore the *bracket* of Prop 3.1, i.e. the TOTAL
column of the paper's Table 2, and the assembly statement `assembly_at_lamStar` asserts
`4r₁ + r₂ + 3r₃ + 4r₄ + 2r₅√(κ_C+r₂) + r₅² ≤ budgetTotal`, with `≤` rather than `=` so that
the convention question of §10.3's closing paragraph — whether [R]'s trace-side `w/L` is
a separate charge, making the conservative reading `r₂ + 4r₁ = 10w/L` — stays open. `cRamp`
is exposed as a `def` for exactly that reason.
-/
import ZetaQ.Defs
import ZetaQ.Certificate
import ZetaQ.EFChi
import ZetaQ.Tail
import ZetaQ.Zones
import ZetaQ.DesignProfile
import ZetaQ.MuqUniform
import ZetaQ.Row2Numeric

noncomputable section

open scoped BigOperators
open Filter Asymptotics

namespace ZetaQ

/-! # §10.3 — the constants of the design of record

Every constant is a `def` with provenance. The constants already frozen
in `ZetaQ/Defs.lean` — `gevreyA` (A = 36/e), `gevreyB` (B = 2e⁸), `c1Ends` (c₁ = 0.41),
`C0Ends` (C₀ = 6), `Cfam`, `CfamDyadic`, `Pconst`, `PconstDyadic`, `lamStar`,
`lamStarDyadic` — are **used, not redefined**. -/

/-! ## Zone constants -/

/-- `s = 0.5073` — the measured small-δ payoff **SECANT** at `C = π⁴/18` (the secant at
δ ≈ 0.005). Paper §10.3: "the δ → 0 slope is 0.5042, and Table 2 uses the
larger secant at the actual design offset — these two pin the rate class".
Provenance: paper §10.3; `budget_q.S_LIN = 0.5073`.
Rule 17: a bare numeral. -/
def sZone : ℝ := 0.5073

/-- `0.5042` — the δ → 0 payoff slope at `C = π⁴/18`. Recorded because §10.3 says the two
figures together "pin the rate class"; **not** what Table 2 charges. -/
def sZoneSlope : ℝ := 0.5042

/-- `0.5485` — the dyadic small-δ secant. Paper §10.5 warns it "is not usable at finite Q";
the dyadic finite-Q arithmetic uses the measured secant at the design offset (0.64 at the
10¹⁰⁰ offset). **USED — it is the dyadic family's zone secant
`Family.sZoneF Family.dyadic`, hence the dyadic `zoneRowLinear` / `rowR2` / `budgetTotal` zone
row.** (Before F63 it was recorded only, and both families' zone rows were priced at `sZone`.) -/
def sZoneDyadic : ℝ := 0.5485

/-- **PROVISIONAL (Corollary 3).** `0.5921332` — the zone secant of the even/odd family over
`q ≤ Q`, at `C = π⁴/9`. Computed off-line by the same route as `sZone` / `sZoneDyadic`
(the payoff secant at the design offset) but **not yet certified inside Lean**: there is no
`ZoneData` Lipschitz record for it, so nothing here proves it is the right number.
Every statement that reads it is flagged. -/
def sZoneEvenQ : ℝ := 0.5921332

/-- **PROVISIONAL (Corollary 3).** `0.6151116` — the zone secant of the even/odd dyadic
family, at `C = 4π⁴/27`. See `sZoneEvenQ` for the provenance caveat. -/
def sZoneEvenDyadic : ℝ := 0.6151116

/-- **The zone secant is a property of the FAMILY**: `sZone = 0.5073` for `q ≤ Q`
(`C = π⁴/18`), `sZoneDyadic = 0.5485` for the dyadic family (`C = 2π⁴/27`; paper §10.5).
`ZoneData.dyadic_margin_fails` shows that the dyadic design profile's zone cost
`2(C_dyad − 1)ψ(1) = 0.5456` EXCEEDS `sZone = 0.5073`, so a zone row priced at `sZone` for both
families (the frozen reading) made the dyadic Frobenius clause false asymptotically; against
`sZoneDyadic` it holds with margin `0.0028` (`ZoneData.zoneLipschitzDataDyadic`). `zoneRowLinear`,
`rowR2` and `budgetTotal` are family-aware through this function. -/
def Family.sZoneF : Family → ℝ
  | Family.qle => sZone
  | Family.dyadic => sZoneDyadic
  | Family.evenQle => sZoneEvenQ
  | Family.oddQle => sZoneEvenQ
  | Family.evenDyadic => sZoneEvenDyadic
  | Family.oddDyadic => sZoneEvenDyadic
  | Family.evenQleR => sZone
  | Family.oddQleR => sZone
  | Family.evenDyadicR => sZoneDyadic
  | Family.oddDyadicR => sZoneDyadic

theorem sZoneF_qle : Family.qle.sZoneF = sZone := rfl
theorem sZoneF_dyadic : Family.dyadic.sZoneF = sZoneDyadic := rfl
theorem sZoneF_evenQle : Family.evenQle.sZoneF = sZoneEvenQ := rfl
theorem sZoneF_oddQle : Family.oddQle.sZoneF = sZoneEvenQ := rfl
theorem sZoneF_evenDyadic : Family.evenDyadic.sZoneF = sZoneEvenDyadic := rfl
theorem sZoneF_oddDyadic : Family.oddDyadic.sZoneF = sZoneEvenDyadic := rfl

/-- `0 ≤ s_F` for all six families (`0.5073`, `0.5485`, `0.5921`, `0.6151`). -/
theorem sZoneF_nonneg (F : Family) : 0 ≤ F.sZoneF := by
  cases F <;>
    norm_num [Family.sZoneF, sZone, sZoneDyadic, sZoneEvenQ, sZoneEvenDyadic]

/-- **`s_F ≤ 0.62`, all six families.** `qle` 0.5073, `dyadic` 0.5485, the even/odd `q ≤ Q`
pair 0.5921332, the even/odd dyadic pair 0.6151116.

**The threshold was RAISED from `0.55` to `0.62`.** At the larger family
constants (`C = π⁴/9`, `4π⁴/27`) the zone secant genuinely rises above `0.55`, so the old
bound was FALSE on the four parity branches — the secants are measured, not adjustable, and
were not lowered to fit. Raising the threshold is the same move F63 made when
`sZoneDyadic = 0.5485` was introduced. Both consumers absorbed it without further change:
`zoneRowLinear_le` (restated at `0.62`) and `Budget.lean`'s `s_F ≤ 1` step. The one numeric
consequence is in `HPre.rowR2_le_of_facts`, where the zone row's contribution moves
`2.2 → 2.48` against a total budget of `79` — checked, and `linarith` closes unchanged. -/
theorem sZoneF_le (F : Family) : F.sZoneF ≤ 62 / 100 := by
  cases F
  · norm_num [Family.sZoneF, sZone]
  · norm_num [Family.sZoneF, sZoneDyadic]
  · norm_num [Family.sZoneF, sZoneEvenQ]
  · norm_num [Family.sZoneF, sZoneEvenQ]
  · norm_num [Family.sZoneF, sZoneEvenDyadic]
  · norm_num [Family.sZoneF, sZoneEvenDyadic]
  · norm_num [Family.sZoneF, sZone]
  · norm_num [Family.sZoneF, sZone]
  · norm_num [Family.sZoneF, sZoneDyadic]
  · norm_num [Family.sZoneF, sZoneDyadic]

/-- `K = 3` in `δ′ = K·log log Q/log Q`. §5 **proves** only `K ≥ 2`; `K = 3` is a
conservative design choice, not forced, and the budget prices each unit of `K` at
`s = 0.5073`. Provenance: paper §2.2 (`δ′ := 3 log log Q/log Q`), §5;
`budget_q` `K = 3.0`. Consistent with the frozen
`ZetaQ.ParamsQ.deltaPrime`, whose body is `3·log log Q/log Q`.
Rule 17: a bare numeral. -/
def KZone : ℝ := 3

/-- `K ≥ 2` — what §5 actually proves. Recorded so the gap between proved and adopted is
visible (the design's extra unit of K costs `s·log ℒ/ℒ`). -/
def KZoneProvedMin : ℝ := 2

/-- `dP/d log C = (0.7212835668 − 0.6980745436)/log 2 = 0.0334835427` — the sensitivity that
converts a relative inflation of `C` into a `δP` charge (rows L₈, L₉, L₁₁).
Provenance: `budget_q.DPDLOGC` (`budget_q.py:24`); the two payoff values are `Pconst` and
`P_evenQle` (paper §1.1 Corollary 3 parenthetical, `C = π⁴/9 = 2·π⁴/18`).
Rule 17: a bare numeral. -/
def dPdlogC : ℝ := (0.7212835668 - 0.6980745436) / Real.log 2

/-! ## Budget-row coefficients -/

/-- **`c_ramp = 6`** — the ramp row is `r₂ = 6w/L`. Paper §10.3: the
diagonal sandwich `(L−2w)³/6` gives relative deficit
`1 − (1 − 2w/L)³ = 6w/L − 12(w/L)² + 8(w/L)³`, "so 6w/L is sharp and charging it in full
over-charges for every w > 0"; charged conservatively in full.
The previously quoted **4w/L ([R]'s calE shape) is RETIRED** (see `cRampRetired`).
Provenance: paper §10.3; [R] `PrimeSideB.lean:384/:386`; `table2_check.table(6.0, "…THE
PRINTED TABLE")`. Exposed as a `def` so both readings of §10.3's open accounting question
(Q7) compile.
Rule 17: a bare numeral. -/
def cRamp : ℝ := 6

/-- `4` — the **retired** ramp coefficient ([R]'s calE shape). Recorded only so that
`table2_check.py`'s second column can be reproduced; §10.3 withdraws it, together with the
`w* ≈ 2.3` it implied. -/
def cRampRetired : ℝ := 4

/-- **🚩 `c_buffer = 6`** — the buffer row is `6·D₀/T`, **priced at the SHARP zero density**
(`N_II` at the true `T/2π`-per-χ scale), NOT at the proved absolute `A₀` of §9, which is
larger. Paper §10.3 and §10.4 both flag this as the ONE row not charged at its proved
constant. See the module header's mandated flag and `buffer_row_gap`.
Provenance: paper §10.3, §10.4; `budget_q` `6*D0/T`.
Rule 17: the row is a function of the FREE `P.D0`; `√T` occurs nowhere. -/
def cBuffer : ℝ := 6

/-- `c_ends = 6` — the ends row is `6·ℒ·log ℒ/T`. Raised from 4 to 6 at R7 (NOTE_QG g.4);
the relative family-ends order is **Θ(ℒ log ℒ/T)** with the CAP-FREE `_L` shapes, and
NOTE_QG g.4's earlier `O(log ℒ log log ℒ/T)` is [SUPERSEDED — R7] and was not used.
Provenance: paper §8; `table2_check.py` docstring ("charged at OUR budget's
coefficient 6·ℒ·logℒ/T (DRAFT §8 / Lemma 8.2), not the reviewer's 4").
Rule 17: **the ends lemmas cited must be the cap-free `_L` variants**
(`calE1_maj_bound_L`, `calE2_maj_bound_L`); the capped forms require `L ≤ 2l`, which is
false here by 10–60× and is a λ ≤ 1 smuggle in disguise. -/
def cEnds : ℝ := 6

/-- `√(24/π) = 2.7639…` — the cross-term constant in
`ρ ≤ √(24/π)·√((log L + O(1))/(TL))`.
Provenance: paper §4 Lemma 4.3 ("the closed form of the constant 2.7640");
`budget_q` literal `2.763953`. Rows L₈ and L₁₂.
Rule 17: no λ, X or D₀. -/
def cCross : ℝ := Real.sqrt (24 / Real.pi)

/-- `0.35` — the in-zone sensitivity of row L₁₂, "conservative vs the review-computed ~0.32".
Provenance: `budget_q.py` inline comment on the `# L12: IN-ZONE cross (Lemma 4.5)` term. -/
def sensInzone : ℝ := 0.35

/-- `⟨log q⟩_{φ*} = log Q − 1/2` over `q ≤ Q` (dyadic: `log Q − (1/2 − (log 2)/3)`) — the
conductor spread of row L₆. Provenance: paper §12.2; `budget_q` `S_LIN*0.5/LL`.
**The dyadic value is the EXACT `1/2 − (log 2)/3 = 0.26895094…`** (paper §12.2:
`⟨log q⟩ = log Q + (log 2)/3 − 1/2`; `Dyadic.famLogCond_dyadic_bound`); the frozen literal
`0.26895` sat `9.4·10⁻⁷` BELOW it — the unsafe direction, swamped by `rvmSlack`
(`Dyadic.conductorShift_dyadic_err`, now an identity). -/
def Family.conductorShift : Family → ℝ
  | Family.qle => 1 / 2
  | Family.dyadic => 1 / 2 - Real.log 2 / 3
  | Family.evenQle => 1 / 2
  | Family.oddQle => 1 / 2
  | Family.evenDyadic => 1 / 2 - Real.log 2 / 3
  | Family.oddDyadic => 1 / 2 - Real.log 2 / 3
  | Family.evenQleR => 1 / 2
  | Family.oddQleR => 1 / 2
  | Family.evenDyadicR => 1 / 2 - Real.log 2 / 3
  | Family.oddDyadicR => 1 / 2 - Real.log 2 / 3

/-- `0.26895 ≤ ⟨shift⟩_dyadic = 1/2 − (log 2)/3 < 0.268951` (the old literal was a lower bound). -/
theorem conductorShift_dyadic_bounds :
    (0.26895 : ℝ) ≤ Family.dyadic.conductorShift ∧ Family.dyadic.conductorShift < 0.268951 := by
  simp only [Family.conductorShift]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- `⟨shift⟩ ≤ 1/2` for both families (`1/2` and `1/2 − (log 2)/3`). -/
theorem conductorShift_le_half (F : Family) : F.conductorShift ≤ 1 / 2 := by
  cases F <;>
    simp only [Family.conductorShift] <;> linarith [Real.log_two_gt_d9]

/-- `0 ≤ ⟨shift⟩` for all six families. -/
theorem conductorShift_nonneg (F : Family) : 0 ≤ F.conductorShift := by
  cases F <;>
    simp only [Family.conductorShift] <;> linarith [Real.log_two_lt_d9]

/-- **The true family average `𝒩/(|𝔉|·(T/2π))`, in `ℒ`-units:**
`⟨ℒ⟩_𝔉 := ℒ − ⟨shift⟩ + (2 log 2 − 1)`.

**F24, IMPLEMENTED.**  `rowR3`/`rowR4`/`rowR5` used
`(T/2π)·ℒ` as an *equality* surrogate for `𝒩/|𝔉|`, i.e. they read §7.3's
`𝒩 ≍ |𝔉|(T/2π)ℒ` as an identity.  It is not one.  The q-uniform Riemann–von Mangoldt count
(`Zeta23.ThmE.mainChi_uniform_aux`, composed as `ZetaQ.EFChi.rvmChi_main_uniform`) is
`|N_χ(T,2T) − (T/2π)·ell1q q T| ≤ A·log(q(T+2))` with

    ell1q q T = log(qT/2π) + 2 log 2 − 1,

and averaging `log q` over `𝔉_Q` with §12.2's conductor spread `⟨log q⟩ = log Q − ⟨shift⟩`
(`Family.conductorShift`) gives

    𝒩 = |𝔉|·(T/2π)·(ℒ − ⟨shift⟩ + 2 log 2 − 1) + O(|𝔉|·log QT).

With `2 log 2 − 1 = +0.386294` that is `|𝔉|(T/2π)(ℒ − 0.113706)` for **`Family.qle`** —
**strictly below** the surrogate `|𝔉|(T/2π)ℒ` — and `|𝔉|(T/2π)(ℒ + 0.117345)` for
`Family.dyadic`.  Since `pair_rows`' two conjuncts are *equivalent* (after cancelling
`θ₀/(aL) > 0`) to `|𝔉|(T/2π)ℒ ≤ 𝒩`, the surrogate made `pair_rows` FALSE at every `θ₀ > 0`
for Theorem 1's own family.

**Why this is the right repair and not a weakening.**  The surrogate ignores exactly the
conductor spread that row `L₆` already prices, i.e. it double-counts it, and in the wrong
direction.  Stating the rows against `famAvgL` keeps the paper's accounting — the spread is
priced once, in `L₆` — and makes the pair rows satisfiable for *both* families.  The
alternative repair recorded at F24 (keep the rows, give `pair_rows`/`buffer_row_sharp` an
explicit `(1 + ε_Q)` slack with `ε_Q = Θ(1/ℒ)`) is equivalent in content and less faithful
to §12.2, so it is not the one taken.

**Cost: none downstream.**  The change is `0.1137/ℒ = 4.6×10⁻⁴` relative at `Q = 10¹⁰⁰`,
against rows that are themselves `Θ(1/ℒ)`, so no §10.4 figure moves at printed precision;
and `rowR4`/`rowR5` are absorbed by `hpair` inside `propBracket_le_budgetTotal`, so
**Theorem 1 does not move at all**.  A hypothesis `|𝔉|(T/2π)ℒ ≤ 𝒩` was considered by an
earlier pass and correctly REJECTED — in that form it is unsatisfiable for `Family.qle`, so
it would have converted a blocked statement into a vacuous one.  `FamRvMLower` below is the
same fact at the *true* average, and it is satisfiable for both families. -/
def famAvgL (F : Family) (P : ParamsQ) : ℝ :=
  P.LL - F.conductorShift + (2 * Real.log 2 - 1)

/-- `0 < ⟨ℒ⟩_𝔉` in the standing regime (`Q ≥ 3`, `T ≥ 300` give `ℒ ≥ 4.9`, against a shift
of at most `1/2 − 2 log 2 + 1 = 0.114`). -/
theorem famAvgL_pos (F : Family) (P : ParamsQ) (hP : P.Valid) : 0 < famAvgL F P := by
  have hQ : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hQT : (900 : ℝ) ≤ P.Q * P.T := by nlinarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hLL : (1 : ℝ) ≤ P.LL := by
    unfold ParamsQ.LL
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    have h1 : Real.exp 1 * (2 * Real.pi) ≤ 2.7182818286 * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right he.le (by positivity)
    have h2 : (2.7182818286 : ℝ) * (2 * Real.pi) ≤ 2.7182818286 * 8 := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsh := conductorShift_le_half F
  unfold famAvgL
  linarith

/-- **The RvM slack** — `1/100` nat.  **Finding F50: `famAvgL` IS the exact
asymptotic family average of `Zeta23.ThmE.ell1q`** (`ell1q q T = log(qT/2π) + 2log2 − 1`, whose
φ*-average over `𝔉_Q` is `ℒ − ⟨shift⟩ + 2log2 − 1`), **so any statement asserting
`|𝔉|(T/2π)·famAvgL ≤ 𝒩` asserts that RvM's aggregate error is FAVOURABLY SIGNED** — and
`EFChi.rvmChi_main_uniform` is two-sided.  The surrogate for `𝒩/|𝔉|` must therefore sit
strictly below the average.  `famRvM_lower_from_tree` measures the shortfall at `≈ 2πA/T` plus
a §12.2 residue `Θ(log³Q/Q)`, so any fixed positive slack is eventually enough, and `1/100` is
chosen for two reasons:

* it is **inside the `0.0397`-nat margin** the F19 block measures for `buffer_row_sharp`
  (`(2 log 2 − 1) − (log 2)/2 = 0.0397`), with a factor ≈ 4 to spare — which matters because
  `buffer_row_sharp`'s `le_trans` forces `SharpZeroDensity` to be lowered by the same slack,
  and that keeps it inside what is true;
* it is `4×10⁻⁵` **relative** at `Q = 10¹⁰⁰` (`famAvgL ≈ 247.4`), so `rowR4`/`rowR5` grow by a
  factor `1 + 1/(100·ℒ)` — invisible, and those rows carry a superexponentially small `θ₀`.

**This is what the paper's own §7.3 licenses and no more.**  The paper writes
`𝒩 ≍ |𝔉|(T/2π)ℒ` and needs only `θ₀/𝒩 → 0` ("per-block `θ₀ → 0` only: no negative power of `Q`
is demanded anywhere"); it is the Lean rows that pinned the surrogate to the exact average.
Third correction in one chain: **F19** found the surrogate `ℒ` was on the wrong side, **F24**
repaired it to `famAvgL`, and **F50** finds that `famAvgL` is exactly right and therefore cannot
carry a `≥`.
Rule 17: a numeral. -/
def rvmSlack : ℝ := 1 / 100

/-- **The surrogate for `𝒩/|𝔉|` the rows actually use** — the family average less `rvmSlack`.
See `rvmSlack` for why the slack is necessary, why it is this size, and why §7.3 licenses it. -/
def famAvgLlow (F : Family) (P : ParamsQ) : ℝ := famAvgL F P - rvmSlack

/-- `0 < ⟨ℒ⟩_𝔉 − rvmSlack`.  Same route as `famAvgL_pos`, which gets `1 ≤ ℒ`; with
`⟨shift⟩ ≤ 1/2` and `2 log 2 − 1 > 0.386` that gives `famAvgL > 0.886`, against a slack of
`0.01`. -/
theorem famAvgLlow_pos (F : Family) (P : ParamsQ) (hP : P.Valid) : 0 < famAvgLlow F P := by
  have hQ : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hQT : (900 : ℝ) ≤ P.Q * P.T := by nlinarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hLL : (1 : ℝ) ≤ P.LL := by
    unfold ParamsQ.LL
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    have h1 : Real.exp 1 * (2 * Real.pi) ≤ 2.7182818286 * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right he.le (by positivity)
    have h2 : (2.7182818286 : ℝ) * (2 * Real.pi) ≤ 2.7182818286 * 8 := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsh := conductorShift_le_half F
  unfold famAvgLlow famAvgL rvmSlack
  linarith

/-- `c₄ = 4/e` — the closing-condition rate constant, from the two-factor (mirrored) tail
bound `exp(−(4/e)√(w·dist/A))`. Provenance: paper §7.2; `budget_q.c4`.
Rule 17: the closing condition is a relation between `w`, `D₀` and `L` — it is what makes
the FREE `D₀` admissible, and it is the opposite of `D₀ = √T`. -/
def c4 : ℝ := 4 / Real.exp 1

/-- `3/2 − (1/√2)·cot(1/√2) = 0.672500703679412` — [R]'s per-character constant, the
calibration gate and the "record" threshold that §10.4's `10²³⁶` refers to.
Provenance: paper §1.2; `fb.gates()`; `budget_q.REC`. Not part of any statement below. -/
def recordConst : ℝ :=
  3 / 2 - (1 / Real.sqrt 2) * Real.cos (1 / Real.sqrt 2) / Real.sin (1 / Real.sqrt 2)

/-- `s·(r + K)` — the asymptotic budget constant at `T = (log Q)^{r+ε}`,
`δ′ = K log log Q/log Q`: ≈ 3.297 at the design `(r,K) = (3.5,3)`; 2.54 at `(3,2)`; ≈ 4.6 at
`(6,3)` (the choice that sits inside [CIS2]'s `(log Q)⁶` window floor).
**COMPUTED, NOT PROVED, and deliberately NOT part of Theorem 1** (paper §10.3 remark,;
§1.5). Measured at `log Q = 2.3×10⁶` with the `w ≥ 1` clamp: 3.560.
Provenance: paper §10.3 remark; `log_table2.txt` final block. -/
def rateConst (r K : ℝ) : ℝ := sZone * (r + K)

/-! ## The design shape: `w*`, the clamp, and the side conditions -/

/-- `w* = Θ(ℒ^{(3−r)/2})` — shape only (Θ(1) at r = 3, slowly decreasing for r > 3).
Provenance: paper §10.3; `budget_q.opt_ramp_buffer`. -/
def wStar (LL r : ℝ) : ℝ := LL ^ ((3 - r) / 2)

/-- `w = max(1, w*)` — the design's clamp at the regime floor carried by the reused cap-free
ends lemmas and by `ParamsQ.Valid.one_le_w`. It binds from `Q ≈ 10⁵⁰` and equals 1 at
`Q = 10¹⁰⁰`; the previously quoted `≈ 2.3` was the r = 3 optimum under the RETIRED `4w/L`
objective and is withdrawn. **The clamp contributes `6/(λℒ)` to the budget — the same order,
with constant `6/λ*`**.
Rule 17: `w ≥ 1` is a regime hypothesis of the reused lemmas, not a smuggle; recorded. -/
def wDesign (LL r : ℝ) : ℝ := max 1 (wStar LL r)

/-- Side condition `8w ≤ L` — [R]'s admissibility `[eq:wrange]`. Stated where used and
deliberately NOT bundled into `ParamsQ.Valid` (`Defs.lean` §5's note). Benign: not a λ/X/D₀
gate. Provenance: paper §10.3; `budget_q.feas`. -/
def SideCondWrange (P : ParamsQ) : Prop := 8 * P.w ≤ P.LB

/-- Side condition `w·D₀ ≫ e²A` (the QT.a optimisation). Provenance: paper §10.3.
Rule 17: a LOWER bound on `wD₀`; the opposite of pinning `D₀`. -/
def SideCondWD0 (P : ParamsQ) : Prop := Real.exp 2 * gevreyA ≤ P.w * P.D0

/-- Side condition `10L ≤ D₀ ≤ T/3`. Provenance: `budget_q` docstring (`D0min = 10*L`,
`D0max = T/3`); paper §10.3.
**Rule 17: this is the whole point — `D₀` is pinned only between `10L` and `T/3`, and at the
design of record sits at ≈ `T/1000` at `Q = 10¹⁰⁰`, nowhere near `√T`.** -/
def SideCondD0range (P : ParamsQ) : Prop := 10 * P.LB ≤ P.D0 ∧ P.D0 ≤ P.T / 3

/-- Side condition `T ≥ 10·ℒ·log ℒ`. Provenance: `budget_q` docstring. -/
def SideCondTfloor (P : ParamsQ) : Prop := 10 * P.LL * Real.log P.LL ≤ P.T

/-- **The honest Gevrey closing condition** (§7.2, §10.3):
`(4/e)·√(w·D₀/A) ≥ L/2 + log(prefactor) + log(L/η)`.
The design of record sits ON this constraint by construction (margin 0 nats at every Q); it
is what balances the ramp row `6w/L` against the buffer row `6D₀/T` and yields
`w* = Θ(ℒ^{(3−r)/2})`.
Provenance: paper §7.2, §10.3;
`budget_q.closing_margin` (LHS − RHS with the LEMMA_QT.b(5) prefactor).
Rule 17: relates `w`, `D₀`, `L` only; `√T` occurs nowhere. -/
def ClosingCondition (P : ParamsQ) (logPrefactor eta : ℝ) : Prop :=
  P.LB / 2 + logPrefactor + Real.log (P.LB / eta) ≤ c4 * Real.sqrt (P.w * P.D0 / gevreyA)

/-! ## §7.2's prefactor, PINNED (decision D27)

`ClosingCondition` above is the general §7.2 relation and is left exactly as frozen — it is
the shape `ZetaQ.theta0G_le` / `theta0Q_le_of_closing` consume. What follows is the
**determinate** `θ₀^Gev` prefactor at which the design of record meets it, so that
`DesignOfRecord`'s closing clause asserts something. LEMMA_QT §QT.b(5), verbatim:

> `θ₀^Gev := A₀·C_env²·2(ℒ + log 4T)·S(D₀)²·L⁻¹·e^{L/2}·exp(−(4/e)·√(wD₀/A))`

with `S(D) := 1 + (L/2π)·(2A/w)·(t_D/c₄ + 1/c₄²)`, `t_D := √(wD/A)` (§QT.b(3)); this is
exactly the `logpre` of the paper's own design script, whose `closing_margin` is
what the shipped optimiser drives to zero.

**Why these are restated here rather than imported.** The `Budget → Tail` edge exists, but
importing `Tail`'s prefactors would not save any work: `Tail`'s
`prefactorG`/`prefactorQ` (`ZetaQ/Tail.lean`) are written against
`Zeta23.Tail.sideW`, the **uncollected** four-term window weight, whereas §7.2/§10.3 and the
optimiser both use §QT.b(4)–(5)'s **collected** `2(ℒ + log 4T)·S(D₀)²`. Extracting the
collected shape from `sideW` is a separate `Tail`-side obligation (its `monoW₀…₃` constants),
and adding a 2000-line file with its own open items to Theorem 1's critical path buys
nothing. So the collected prefactor is restated, with the provenance above, and the two
`Tail` objects stay the record of the uncollected form. `CenvDesign` is
`ZetaQ.CenvQ P gevreyB` (`ZetaQ/Tail.lean`) verbatim. -/

/-- `C_env = e²·max(2·B′·w, L)` — the §7.1 envelope constant at the design window.
The Gevrey constant is the PRODUCT-window constant
`B′ = gevreyBprod gevreyA gevreyB = B·Σ_j M_j (w/(ℒA))^j + ½Σ_j M_j (λ/A)^j` (`ZetaQ/Defs.lean`,
`ZetaQ/Window.lean` `Valid.gevreyPhiBound`), not the flat taper's `B = 2e⁸`; at the design
`B′ ≤ 40000` (`design_gevreyBprod_le`, `ZetaQ/DesignProfile.lean`), against `B ≤ 6000`, which
moves `2 log C_env` by `≈ 2 log 3 ≈ 2.2` nats in `logPrefactorGev` (the closing condition's
root `D₀` moves by a few percent; `design_D0_isBigO` and the IVT bounds of
`exists_designOfRecord_at` are re-verified below at `B′ ≤ 40000`).
Provenance: `ZetaQ.CenvQ P B′` (`ZetaQ/Tail.lean`); `budget_q.closing_margin`'s
`C_env = e**2 * max(2*B_G*w, L)` with `B_G` the window's Gevrey constant.
Rule 17: a function of `(w, L, ℒ, λ, p)` only. CLEAN. -/
def CenvDesign (P : ParamsQ) : ℝ :=
  Real.exp 2 * max (2 * P.gevreyBprod gevreyA gevreyB * P.w) P.LB

/-- `t_{D₀} = √(w·D₀/A)` — the Gevrey exponent variable of LEMMA_QT §QT.b(3). It is the
argument of the tail's `exp(−c₄·t_{D₀})`, and it is the quantity the closing condition pins.
Rule 17: the FREE field `P.D0`; `√T` occurs nowhere. -/
def tBuffer (P : ParamsQ) : ℝ := Real.sqrt (P.w * P.D0 / gevreyA)

/-- `S(D₀) = 1 + (L/2π)·(2A/w)·(t_{D₀}/c₄ + 1/c₄²)` — LEMMA_QT §QT.b(3)'s row-sum factor
(first term + the exactly-evaluated integral comparison, `h = 2π/L`).
Provenance: `LEMMA_QT` §QT.b(3); `budget_q.closing_margin`'s `S`.
Rule 17: a function of `(L, w, D₀)`; free `D₀`. CLEAN. -/
def rowSumFactor (P : ParamsQ) : ℝ :=
  1 + P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (tBuffer P / c4 + 1 / c4 ^ 2)

/-- **`log(prefactor)` of `θ₀^Gev`** — LEMMA_QT §QT.b(5)'s prefactor with the off-line
amplification `e^{L/2}` and the Gevrey exponential `exp(−c₄ t_{D₀})` stripped out, i.e.
`log(C_env²·2(ℒ + log 4T)·S(D₀)²/L)`. Provenance: `LEMMA_QT` §QT.b(4)–(5);
`budget_q.py:44–50` (`logpre`).

**On the `A₀` factor.** §QT.b(5)'s `θ₀^Gev` carries the local-count constant `A₀` as an extra
multiplicative factor, and `budget_q.closing_margin` omits it. That
discrepancy is **not** inherited here, because `A₀` enters the closing condition only through
`log A₀`, additively and in the same slot as `−log η`:

  `L/2 + log(A₀·pre) + log(L/η)  =  L/2 + log pre + log(L/(η/A₀))`.

So "margin 0 at this `A₀`-free prefactor with `η = 1`" **is** "margin 0 at §QT.b(5)'s full
prefactor with `η = A₀`", and the tail target it delivers is `θ₀ ≤ A₀/L`, which is still
`O(1/L) → 0` — all §7.2 asks for ("θ₀ → 0 faster than any required rate"). Pinning `η = 1`
here is therefore a normalisation of `η`, not a dropped constant, and it keeps `A₀` out of
`DesignOfRecord`'s signature (which every statement in this file takes as a hypothesis).

Rule 17: functions of `(Q, T, w, L, ℒ, D₀)` only; the free `D₀`, never `√T`. CLEAN. -/
def logPrefactorGev (P : ParamsQ) : ℝ :=
  2 * Real.log (CenvDesign P) + Real.log (2 * (P.LL + Real.log (4 * P.T)))
    + 2 * Real.log (rowSumFactor P) - Real.log P.LB

/-- **The design of record's closing clause: §7.2's condition at §QT.b(5)'s prefactor, met
with MARGIN 0** (decision D27). Paper §7.2, verbatim:

> the design of record sits ON the constraint by construction — the optimiser drives `D₀` to
> the boundary, so the margin is 0 nats at every `Q` (`table2_check.py`)

and that is what `budget_q.opt_ramp_buffer` does: it bisects for the **smallest** `D₀` with
`closing_margin ≥ 0`. So the clause is the conjunction of the two halves,

  * `ClosingCondition P (logPrefactorGev P) 1` — `needed ≤ supplied`, the half §7's tail
    lemma consumes (`Tail.theta0G_le`), pinned at the determinate prefactor; and
  * `supplied ≤ needed` — the half the optimiser's boundary supplies,

i.e. an equality, written as two separately auditable inequalities. **This is what replaces
the vacuous `∃ logPrefactor eta, …`** of the previous transcription, under which
`logPrefactor` was unconstrained and the clause asserted nothing (see `DesignOfRecord`).

### ✅ SATISFIABILITY — checked, not assumed (the D28 lesson)

A pinned hypothesis is worth nothing if no design meets it, so: at fixed `(Q, r, ε)` the only
free quantity here is `D₀`, and
`g(D₀) := c₄√(wD₀/A) − (L/2 + logPrefactorGev + log L)` is **continuous and eventually
increasing** in `D₀` — the supplied side grows like `√D₀`, while the only `D₀`-dependent term
on the needed side is `2 log S(D₀)`, which grows like `log D₀`. At the lower end of
`SideCondD0range`, `D₀ = 10L`, the supplied exponent is `c₄√(10L/A) ≈ 1.28√L` against a
needed `≈ L/2`, so `g(10L) < 0` for every `L ≥ 30` or so (at `Q = 10¹⁰⁰`: `22.5` against
`≈ 175`); and `g(T/3) > 0` at every design scale. So a root exists strictly inside
`(10L, T/3)` by the intermediate value theorem, and it sits at `wD₀ ≈ A(L/2)²/c₄² = 6.1 L²`,
comfortably above `SideCondWD0`'s `e²A ≈ 97.9` and far below `T/3`. That root is exactly what
`budget_q.opt_ramp_buffer` bisects to (it returns the SMALLEST feasible `D₀`, and the design
of record is that point), and `table2_check.py` reports margin 0 at every `Q` in the table.

⚠ **Cost, recorded:** this makes `assembly_at_lamStar` a strictly stronger statement, since
its `∃ P, DesignOfRecord …` must now exhibit a `P` meeting an equality rather than a vacuity.
That is the intended trade — without it Theorem 1 does not follow from the assembly at all
(see `payoff_rate_of_assembly`) — but it does mean the design-point construction, which was
already checklist item 1 there and which no section owns, now has a real obligation in it.

Rule 17: relates `w`, `D₀`, `L`, `ℒ`, `T` only. **This clause is the reason `D₀` need not be
tied to `√T`**: it is what makes the free `D₀` admissible, and it forces
`wD₀ ≍ A(L/2)²/c₄²`, i.e. `D₀ = Θ(ℒ²)` at the clamp `w = 1` — a different function of `Q`
from `√T = (log Q)^{(r+ε)/2}` (see `design_D0_isBigO`). CLEAN. -/
def ClosingAtDesign (P : ParamsQ) : Prop :=
  ClosingCondition P (logPrefactorGev P) 1 ∧
    c4 * tBuffer P ≤ P.LB / 2 + logPrefactorGev P + Real.log (P.LB / 1)

/-- `T(Q) = (log Q)^{r+ε}` — the window height. Paper §1.1: `r = 3` is the headline and
"the same statement holds at `T = (log Q)^{r+ε}` for every `r ≥ 3`".
Rule 17: `r ≥ 3` is the paper's own regime hypothesis (§2.2, the buffer/rate trade), not a
smuggle; nothing here relates `T` to `X`. -/
def Twin (Q r ε : ℝ) : ℝ := Real.log Q ^ (r + ε)

/-- **The design of record at `(F, r, ε, Q)`** (§10.3), as a single `Prop`: the validity
class, the design point's identifications, the clamp, and every side condition — bundled
HERE (a statement-level object) rather than in `ParamsQ.Valid`, so that each side condition
stays visible to the Rule-17 audit at its call site.
### ✅ THE CLOSING CLAUSE IS NOW PINNED — decision **D27**, implemented here.

**What it used to say, and why that was a defect.** The last clause read
`∃ logPrefactor eta, 0 < eta ∧ ClosingCondition P logPrefactor eta`, with `logPrefactor`
existentially quantified and unconstrained — so taking it sufficiently negative (or `eta`
sufficiently large) satisfied it for *every* `P`, and the clause asserted nothing. `D₀` was
then pinned only by `SideCondD0range`'s `10L ≤ D₀ ≤ T/3`, i.e. not from above in any useful
sense: at `D₀ = T/3` the buffer row is `L₄ = 6D₀/T = 2`, a constant. That vacuity broke three
things — it made `budgetTotal_isBigO` false as first stated, it stopped
`assembly_at_lamStar`'s existential from supplying `hD0`, and it therefore blocked
`theorem_one_generic` and `corollary_two_dyadic` even though the `calc` joining them to the
budget (`payoff_rate_of_designs`) was already proved.

**What it says now.** `ClosingAtDesign P`: §7.2's condition at LEMMA_QT §QT.b(5)'s
determinate `θ₀^Gev` prefactor (`logPrefactorGev`), met with **margin 0** — which is what
paper §7.2 asserts of the design of record in so many words ("sits ON the constraint by
construction … the margin is 0 nats at every Q"), and what `budget_q.opt_ramp_buffer`
computes by bisecting to the smallest feasible `D₀`. This is a faithfulness repair, not a
weakening of the transcription: the existential was **our** looseness, since the paper's
closing condition is stated at that prefactor and nowhere quantifies over it.

**Consequence (the point of D27):** `wD₀ ≍ A(L/2)²/c₄²`, hence `D₀ = O((log Q)²)` — proved as
`design_D0_isBigO`, so `budgetTotal_isBigO`'s `hD0` is now *derivable* from `hdesign`
(`budgetTotal_isBigO_of_design`) instead of hypothesised, and the two headline theorems close
against `assembly_at_lamStar` alone (`payoff_rate_of_assembly`).

Rule 17: `P.lam = F.lamStar` is `1.2507321515 > 1`; `P.D0` is constrained by
`SideCondD0range`, `SideCondWD0` and `ClosingAtDesign` — and note that the last of these
gives an `O(ℒ²)` UPPER bound, which is **not** `D₀ = √T`: at `T = (log Q)^{r+ε}` the two are
different functions of `Q`, and at `Q = 10¹⁰⁰` the design sits at `D₀ ≈ T/1000 ≈ 1.85×10⁵`
against `√T ≈ 1.5×10⁴`.

**✅ THE FLAT TAPER IS REPAIRED HERE.** This used to pin the FLAT taper (`P.Valid`
carried only `TaperProfile ϱ`, so `phiQ = ϱ((L/2 − |u|)/w)` and `v = φ²` was the indicator of
`[−λ/2, λ/2]`, for which `B = 1.4086 ≠ κ_C = 1.2787` at `λ*`). Now `ParamsQ` carries the even
polynomial profile `prof`, `toParams` realises `x ↦ p((L/2 − w·x)/ℒ)·ϱ(x)` (so
`phiQ u = p(u/ℒ)·ϱ₂((L/2 − |u|)/w)`), and this predicate PINS both the ramp `ϱ = ϱ₂`
(`Zeta23.Taper.rhoTwo`, the paper's §2.2 Gevrey-2 ramp, so every Gevrey hypothesis downstream is
dischargeable from `hdes`) and the profile `prof = F.designProfile` (`ZetaQ/DesignProfile.lean`:
the even degree-6 polynomial whose square is §11's certified profile on the design support
`[−λ*/2, λ*/2]`; `v = p²` has `B ≤ 2 − 0.7212` for `q ≤ Q`, `≤ 2 − 0.7098` dyadic). The two new
clauses are LAST, so every existing `⟨hP, …, -⟩` destructuring is unchanged. See the module
header. -/
def DesignOfRecord (F : Family) (r ε Q : ℝ) (P : ParamsQ) : Prop :=
  P.Valid ∧ P.Q = Q ∧ P.T = Twin Q r ε ∧ P.lam = F.lamStar ∧ P.w = wDesign P.LL r ∧
    SideCondWrange P ∧ SideCondWD0 P ∧ SideCondD0range P ∧ SideCondTfloor P ∧
    ClosingAtDesign P ∧ P.ϱ = Zeta23.Taper.rhoTwo ∧ P.prof = F.designProfile

/-! ## The design of record WITH A MARGIN — decision **F52**

`ClosingAtDesign` meets §7.2's condition at LEMMA_QT §QT.b(5)'s prefactor with margin 0 and
delivers `θ₀_fam ≤ A₀/L` (`HPre.theta0Fam_le_of_design_A0`); against the pair rows
`L₅ + L₉ ≈ 6ℒ log ℒ/T` that needs `√T ≲ 0.4·ℒ^{3.5} log ℒ/A₀`, i.e. the regime `r + ε ≤ 7`
(`HPre.hregime_eventually`; `audit/HPre_REPORT.md` §(c)). Adding `m = ½ log T` nats to BOTH
halves of the closing equality moves the root by `Δt = m/c₄` (≈ 6.5 against `t ≈ 143` at
`Q = 10¹⁰⁰`, i.e. `D₀ = A t²` up ≈ 9 %), keeps `D₀ = O(ℒ²)` (`designM_D0_isBigO`) and both IVT
endpoint signs (`exists_designOfRecordM_at`: the high endpoint had `2.8u` against `2.12u`, and
`m ≤ u/4` in the regime), and makes the tail target `θ₀_fam ≤ A₀ e^{−m}/L = A₀/(L√T)`
(`Margin.theta0Fam_le_of_designM_A0`) — `√T`-free against the pair rows, so §7's regime
inequality holds for EVERY `r ≥ 3` (`Margin.hregime_M_eventually`) and Theorem 1 loses the
hypothesis `r + ε ≤ 7` (`JoinProved.theorem_one_generic_proved'`).

The margin is introduced as NEW clauses beside the frozen ones (`ClosingAtDesign`,
`DesignOfRecord` are untouched): `DesignOfRecordM` is `DesignOfRecord` with `ClosingAtDesignM`
in the SAME position, so every projection `hdes.1`, `hdes.2.1`, … reads the same field.
Rule 17: `m` is a function of `T` alone; `D₀` stays FREE, pinned only by the (shifted) closing
equality; nothing relates `X` to `T` or caps `λ`. -/

/-- The F52 margin, `m := ½ log T` nats. -/
def marginDesign (P : ParamsQ) : ℝ := Real.log P.T / 2

/-- `ClosingAtDesign` with `marginDesign P` added to BOTH halves: §7.2's condition at §QT.b(5)'s
prefactor met with margin `m = ½ log T`, and the boundary equality at the same shifted target. -/
def ClosingAtDesignM (P : ParamsQ) : Prop :=
  ClosingCondition P (logPrefactorGev P + marginDesign P) 1 ∧
    c4 * tBuffer P ≤ P.LB / 2 + logPrefactorGev P + marginDesign P + Real.log (P.LB / 1)

/-- **The design of record WITH MARGIN**: `DesignOfRecord`'s conjuncts verbatim, with
`ClosingAtDesignM` in place of `ClosingAtDesign` (same position). -/
def DesignOfRecordM (F : Family) (r ε Q : ℝ) (P : ParamsQ) : Prop :=
  P.Valid ∧ P.Q = Q ∧ P.T = Twin Q r ε ∧ P.lam = F.lamStar ∧ P.w = wDesign P.LL r ∧
    SideCondWrange P ∧ SideCondWD0 P ∧ SideCondD0range P ∧ SideCondTfloor P ∧
    ClosingAtDesignM P ∧ P.ϱ = Zeta23.Taper.rhoTwo ∧ P.prof = F.designProfile

/-- The projection: every conjunct of `DesignOfRecord` except the closing clause. -/
theorem DesignOfRecordM.core {F : Family} {r ε Q : ℝ} {P : ParamsQ}
    (h : DesignOfRecordM F r ε Q P) :
    P.Valid ∧ P.Q = Q ∧ P.T = Twin Q r ε ∧ P.lam = F.lamStar ∧ P.w = wDesign P.LL r ∧
      SideCondWrange P ∧ SideCondWD0 P ∧ SideCondD0range P ∧ SideCondTfloor P ∧
      P.ϱ = Zeta23.Taper.rhoTwo ∧ P.prof = F.designProfile := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h12⟩

/-- `m ≥ 0` (`T ≥ 300`). -/
theorem marginDesign_nonneg (P : ParamsQ) (hP : P.Valid) : 0 ≤ marginDesign P := by
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  unfold marginDesign
  have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ P.T)
  linarith

/-- `e^{−m} = 1/√T`. -/
theorem exp_neg_marginDesign (P : ParamsQ) (hT : 0 < P.T) :
    Real.exp (-marginDesign P) = (Real.sqrt P.T)⁻¹ := by
  unfold marginDesign
  rw [Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hT]
  ring_nf

/-- The margin clause implies the margin-0 LOWER half (`m ≥ 0`) — what `Tail.theta0G_le`
consumes. -/
theorem closingCondition_of_closingAtDesignM (P : ParamsQ) (hP : P.Valid)
    (h : ClosingAtDesignM P) : ClosingCondition P (logPrefactorGev P) 1 := by
  have hm := marginDesign_nonneg P hP
  have h1 := h.1
  unfold ClosingCondition at h1 ⊢
  linarith

/-! # §10.3 — the budget rows L₁ … L₁₂

Operational definitions, taken from `budget_q.py` (`design`, `budget_q.py:71–83`) and
`r4_design_check.py:11–17` (which names L₁–L₅ verbatim); the `minor` bundle's provenance
comment is `budget_q.py:10`, *"minor : L6..L11 of round 5"*, plus the inline label
`# L12: IN-ZONE cross (Lemma 4.5)`. Verified values at `Q = 10²⁵ / 10¹⁰⁰ / 10³⁰⁰` are quoted
in each docstring from `log_table2.txt`.

Rule 17, for every row below: each is a function of `(P.Q, P.T, P.lam, P.w, P.D0)` only;
no row assumes `λ ≤ 1`, none relates `X` to `T`, and the buffer row is a function of the
FREE field `P.D0`. -/

/-- **L₁ — zone breakpoint.** `s·(log T − log 2π)/ℒ`.
Shape: relative (coefficient normalization). Source: §4 (Lemma 4.4), §5; the in-zone
breakpoint is `|s| ≤ (1−δ′)·log Q`, **not** `(1−δ′)ℒ`, and this row is exactly the
difference (the frozen `ParamsQ.s0`).
**D-3 resolution applied:** the paper writes `s·(log T)/ℒ`, the scripts compute
`s·(log T − log 2π)/ℒ`; §2.2's `ℒ = log(QT/2π)` makes `Zeta23.l P.T = log(T/2π)` the
consistent quantity, so that is what is used.
In the script: folded into `zone` via `a = (1−δ′)(1 − l/ℒ)`. -/
def L₁ (P : ParamsQ) : ℝ := sZone * Zeta23.l P.T / P.LL

/-- **L₂ — zone edge.** `s·δ′ = s·K·log log Q/log Q`.
Shape: relative. Source: §5 (Lemma 5.3; K ≥ 2 proved, K = 3 adopted).
Uses the frozen `ParamsQ.deltaPrime`.
In the script: folded into `zone`. -/
def L₂ (P : ParamsQ) : ℝ := sZone * P.deltaPrime

/-- `a = (1 − δ′)(1 − l/ℒ)` — the zone factor the script feeds to the payoff.
Provenance: `budget_q.design`. See D-4. -/
def zoneFactor (P : ParamsQ) : ℝ := (1 - P.deltaPrime) * (1 - Zeta23.l P.T / P.LL)

/-- **The `zone` row as the script charges it (curvature-honest, D-4):**
`P(C, 1) − P(C, a)` with `a = zoneFactor` — L₁ and L₂ compose **multiplicatively inside the
payoff**, not additively. §11's payoff `P(C, ·)` lives in `ZetaQ/Payoff.lean`, so it is passed as a
parameter here rather than invented.
Verified: 0.2514 / 0.0784 / 0.0305 at `Q = 10²⁵ / 10¹⁰⁰ / 10³⁰⁰`. -/
def zoneRowCurv (payoff : ℝ → ℝ → ℝ) (F : Family) (P : ParamsQ) : ℝ :=
  payoff F.Cconst 1 - payoff F.Cconst (zoneFactor P)

/-- The linear fallback for the `zone` row (`curvature=False` in `budget_q.design`):
`s_F·(1 − a)`. Agrees with `zoneRowCurv` to leading order — both are `s(r+K)·log ℒ/ℒ` — and is
what `budgetTotal` uses so that the total has a real body. See D-4.
**Family-aware.** The secant is `Family.sZoneF F` — `sZone = 0.5073` for
`q ≤ Q`, `sZoneDyadic = 0.5485` for the dyadic family (paper §10.5) — where the frozen reading
took `sZone` for both (see the module header). For `Family.qle` the row is unchanged
(`sZoneF_qle` is `rfl`). -/
def zoneRowLinear (F : Family) (P : ParamsQ) : ℝ := F.sZoneF * (1 - zoneFactor P)

/-- `0 ≤ zoneRowLinear F P` whenever `zoneFactor P ≤ 1`. -/
theorem zoneRowLinear_nonneg (F : Family) (P : ParamsQ) (h : 0 ≤ 1 - zoneFactor P) :
    0 ≤ zoneRowLinear F P :=
  mul_nonneg (sZoneF_nonneg F) h

/-- `zoneRowLinear F P ≤ 0.62·(1 − zoneFactor P)` whenever `zoneFactor P ≤ 1` (all six families). -/
theorem zoneRowLinear_le (F : Family) (P : ParamsQ) (h : 0 ≤ 1 - zoneFactor P) :
    zoneRowLinear F P ≤ 62 / 100 * (1 - zoneFactor P) :=
  mul_le_mul_of_nonneg_right (sZoneF_le F) h

/-- **L₃ — ramp.** `c_ramp·w/L = 6w/L`.
Shape: relative, in the frobSq PP-diagonal main term. Source: §10.3 (the diagonal sandwich
`(L−2w)³/6`; [R] `PrimeSideB.lean:384/:386`), §7 (the ramp side of the tail row).
The retired reading is `4w/L`; see `cRampRetired` and Q7.
Verified: 0.1201 / 0.0210 / 0.0070.
Rule 17: `P.LB = λℒ` is the q-aspect `L`. -/
def L₃ (P : ParamsQ) : ℝ := cRamp * P.w / P.LB

/-- **🚩 L₄ — buffer, AT THE SHARP ZERO DENSITY.** `c_buffer·D₀/T = 6·D₀/T`.
Shape: relative. Source: §7, §9.
**THE MANDATED FLAG.** Paper §10.3: this row is priced at the sharp zero density (`N_II` at
the true `T/2π`-per-χ scale), **not** at the proved absolute `A₀` of §9, which is larger —
"the ONE row NOT charged at its proved constant" (§10.4). The proved
version is `bufferRowProved`; the gap is `buffer_row_gap`; the Lean consequence is that
`buffer_row_sharp` is **not dischargeable from H6 alone** and needs the named hypothesis
`SharpZeroDensity`. See the module header — a coordinating decision.
Verified: 0.1202 / 0.0075 / 0.0010.
**D35 (reversing D10 and D34): this IS the row `budgetTotal` charges**, and the sharp density
it is priced at is carried as the explicit named hypothesis `SharpZeroDensity` — exactly the
paper's own position. `bufferRowProved` is retained as the record of what §9/H6 proves
outright, and `buffer_row_gap` as the record of the `≈ πA₀ ≈ 255` factor between them.
Rule 17: `P.D0` is the FREE field. -/
def L₄ (P : ParamsQ) : ℝ := cBuffer * P.D0 / P.T

/-- **✅ The buffer row AT THE PROVED CONSTANT, q-UNIFORMLY — the row D10 shipped, retained
under D35 as the record of what §9/H6 proves outright. REPAIRED IN PASS 2; see the
module header.**

The relative form of what §9/H6 actually proves, per character
(`ZetaQ.EFChi.NIID_chi_le`): `N_{II,χ} ≤ 3·A₀·D₀·log(4qT)`, and
`log(4qT) = log q + log 4T ≤ log Q + log 4T ≤ ℒ + log 4T` for `q ≤ Q` at `T ≥ 2π` — which is
verbatim the conclusion of `ZetaQ.EFChi.NII_fam_le`,
`Σ_χ N_{II,χ}(D₀) ≤ 3A₀D₀(ℒ + log 4T)·|𝔉|`. Divided by the per-character main term
`(T/2π)·ℒ` of the Riemann–von Mangoldt count `N_χ(T,2T) = (T/2π)log(qT/2π) + O(T)`.

**WHAT WAS WRONG.** This row read `3·A₀·D₀·log(4T)`, i.e. [R]'s ζ-only
`Zeta23.Tail.NIID_le` (`Zeta23/Tail/GevreyTail.lean:1878–1881`), whose local-count
hypothesis is `A₀·log(|t|+3)` with **no conductor** — while `buffer_row_proved`'s own
hypothesis `hloc` is the q-uniform `A₀·log(q(|t|+3))`. Failing instance: cancelling the
common `D₀/T > 0`, `L₄ ≤ bufferRowProved A₀ P` is equivalent to `ℒ ≤ π·A₀·log(4T)`, i.e. at
`T = (log Q)^{r+ε}` to `log Q ≲ π·A₀·(r+ε)·log log Q` — true up to `Q ≈ 10³⁴⁰⁰` and false
for every larger `Q`. Beyond that crossing the "proved" row sits BELOW the sharp density,
which is the truth, so `buffer_row_gap` and `buffer_row_proved` were both false there, and
Theorem 1 is a statement about all large `Q`.

**WHY THE NEW FORM IS THE PAPER'S CLAIM AND NOT A WEAKENING.** §9 proves the q-uniform
bound; the ζ-only one is a mis-citation, not a sharper result we are giving up. The repaired
row is *larger*, so `buffer_row_proved`'s conclusion `NIIFamQ ≤ bufferRowProved·NfamQ` is a
weaker bound on `NIIFamQ` — the conservative direction, which is precisely the direction
D10 chose ("a formal artifact must not depend on a row it cannot discharge from its own
imports") — a direction D35 no longer *charges*, but which this row still records. Against
`L₄` the ratio is now `π·A₀·(ℒ + log 4T)/ℒ ≈ π·A₀ ≈ 255` uniformly in
`Q` (`EFChi.NII_fam_le`'s own docstring quotes that figure), instead of decaying like
`log log Q/log Q` and crossing 1. The row is `Θ(D₀/T)` either way, so the rate class and `P`
are untouched and only §10.4's finite-Q orientation figures move — D10's own cost claim.

**F24 note — this row keeps the `(T/2π)·ℒ` surrogate in its denominator, ON PURPOSE.**  The
same substitution that made `pair_rows` false is present here, but it is harmless: it costs a
relative `0.1137/ℒ = 4.6×10⁻⁴`, while this row is charged at `π·A₀ ≈ 255` times the truth by
construction (that is exactly what `buffer_row_gap` says).  So `buffer_row_proved` is true
with a factor-255 margin against a `4.6×10⁻⁴` defect, and rewriting the denominator at
`famAvgL` would only churn `buffer_row_gap`/`bufferRowProvedQ` for no gain.  What still
blocks `buffer_row_proved` is that `ZetaQ/EFChi` (hence `NII_fam_le`) is not in this file's
import graph, and an RvM lower bound for `NfamQ` — now available in its correct form as
`FamRvMLower`, but at `famAvgL`, so a consumer must absorb the same `4.6×10⁻⁴` into the
factor-255 margin.

Provenance: paper §9; `ZetaQ/EFChi.lean` `NIID_chi_le`, `NII_fam_le`.
Rule 17: `D` is the FREE `P.D0`; `NIID_le`'s own hypotheses are `2 ≤ D` and
`D + 4 ≤ T`, both fields of `ParamsQ.Valid` — never `D = √T`. -/
def bufferRowProved (A₀ : ℝ) (P : ParamsQ) : ℝ :=
  3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) / (P.T / (2 * Real.pi) * P.LL)

/-- **Alias, retained for continuity.** The previous pass, treating `bufferRowProved` as
frozen, introduced this shadow copy to carry the corrected (q-uniform) body. F18 is now
repaired at the source, so the two are the same row and this name is kept only so that
anything citing it still compiles. Prefer `bufferRowProved`. -/
def bufferRowProvedQ (A₀ : ℝ) (P : ParamsQ) : ℝ := bufferRowProved A₀ P

/-- **L₅ — ends.** `c_ends·ℒ·log ℒ/T = 6·ℒ·log ℒ/T`.
Shape: relative, hat normalization, via `B_fam/√|𝔉|`. Source: §8 (Lemma 8.2).
Ledger rows 6 and 7 (𝓔₁ grid truncation, 𝓔₂ outside I×I) both land here.
Verified: 0.00123 / 0.00004 / 0.00000.
Rule 17: cap-free `_L` ends lemmas only — see `cEnds`.

🚩 **The coefficient `6` is NOT what §8 delivers — see `L₅proved`.**  Retained
unchanged as the paper's printed row (§10.2/§10.4's table), exactly as `L₄` is the paper's
buffer row — and, under **D35**, `budgetTotal` charges the paper's row in both cases. The
difference is that the buffer's assumption is *named* (`SharpZeroDensity`) while F23's is not
yet: §8's own constant is `L₅proved`, and no hypothesis of this file asserts `cEnds = 6`. -/
def L₅ (P : ParamsQ) : ℝ := cEnds * P.LL * Real.log P.LL / P.T

/-- 🚩 **`c_ends` AT THE CONSTANT §8 ACTUALLY PROVES: `2.5×10⁶`, not `6`.**

The numeral is `ZetaQ.Ends.endsRowConst`, copied rather than imported because `ZetaQ/Budget`
does not import `ZetaQ/Ends` DIRECTLY (it reaches it only through `ZetaQ.Zones`, which is
above `Ends`), the same reason `EndsFamBound` is a local `Prop`.

⚠ **`2.5×10⁶` — and the "≈ 4.1×10⁵ / 3.7×10⁵ / 3.03×10⁵" figures below —
are the evaluation at the window-constant FLOOR `c_ϱ = 4`, which no ramp attains** (`cRho ϱ ≥ 12`
for any C¹ ramp; `c_ϱ(ϱ₂) = 31.26`; the artifact's `P.cWin ≈ 548`).  `ZetaQ.Ends.ends_relative_le`
is now stated at the actual window constant with the coefficient `Ends.endsRowConstC c =
10·C₁(c) + 47·C₂′(c)` (`≈ 8.2×10⁷` at `c_ϱ(ϱ₂)`, `≈ 2.1×10¹⁰` at `cWin`); the real §10.4 ends
figures are `C_ends ≈ 2.9×10⁹` at `c_win` (`ZetaQ.Ends.endsRowConstC`).  Theorem 1 does not
consume this row: its ends enter through `Ends.ends_family_bound` at `P.cWin`
(`FrobAssembly.endsMaj`), absorbed into the certificate slack eventually.

**F23, implemented in `ZetaQ/Ends.lean`, where
`ZetaQ.Ends.ends_relative_le` is now PROVED at it.**  With `ends_family_bound` (Lemma 8.2,
closed form) proved, the relative-order constant can be read off instead of estimated.  The
ORDER `Θ(ℒ log ℒ/T)` is right; the coefficient is not `6`.  Two figures, both recorded
because they answer different questions:
  * `≈ 4.1×10⁵` **at the design of record**, `≈ 3.7×10⁵` over §10.4's whole range, with
    limit `2πC_fam·c₁²·C₂′(4) = 3.03×10⁵` (approached only logarithmically slowly, through
    `(1+log L)/log ℒ → 1`) — these are the numbers to recompute §10.4's table with;
  * `2.5×10⁶` **uniformly over §8's own hypothesis class** (`ℒ ≥ 30`, `λ < 2`, `a ≥ 3/4`,
    `l ≤ L`) — the number the Lean row is proved at, and the body of `cEndsProved`.

**Where the paper's ≈ 5.7 came from.**  NOTE_QR §QR.1's displayed family-ends lemma carries
the bracket `[4(90 + 32c_ϱ²) + C₂′(1 + log L)]`, but its own "relative order, the explicit
chain" two paragraphs later reads `2πC·c₁²(ℒ+C₀)²·l log l/(a²LTℒ)` — **with the bracket
absent**.  `2πC_fam·c₁² = π⁵·0.1681/9 = 5.716` is exactly the quoted 5.7, so the note's own
lemma and its own chain disagree by the bracket, which at the design is `3.6×10⁵`.  The
lemma is what the Lean tree instantiates.  Full write-up at `ZetaQ.Ends.r5`. -/
def cEndsProved : ℝ := 2500000

/-- 🚩 **The ends row at the proved constant.**  Same convention as `L₄`/`bufferRowProved`
under **D35**: `L₅` stays as the paper's printed row, `budgetTotal` charges that row, and this
is the named object recording what §8 proves.  (The buffer row's counterpart of this gap is
`bufferRowProved`, and its assumption is named as `SharpZeroDensity`; F23's is the ≈80% of
§10.4's finite-Q damage that D35 does **not** remove.)

**Consequences of F23.**  Theorem 1 is untouched — `ℒ log ℒ/T = log ℒ/ℒ^{2.5}` at `r = 3.5`,
so the row → 0 at any constant and the rate class does not move.  §10.4's finite-Q table does
not survive it: at the design constant `3.7×10⁵` the row is `75 / 2.72 / 0.20 / 1.1×10⁻² /
8.3×10⁻⁴` at `Q = 10²⁵/10¹⁰⁰/10³⁰⁰/10¹⁰⁰⁰/10³⁰⁰⁰` against zone rows
`0.23 / 0.078 / 0.031 / 0.011 / 4.2×10⁻³`, i.e. it **exceeds 1 at `Q = 10¹⁰⁰`** and only
falls below the zone terms near `Q ≈ 10¹⁰⁰⁰`.  §10.4's "non-vacuous from ≈ 10²⁰" therefore
moves by roughly a thousand orders of magnitude, and every figure of Table 2 with it.  Any
recomputation of §10.4 must substitute this row for `L₅`. -/
def L₅proved (P : ParamsQ) : ℝ := cEndsProved * P.LL * Real.log P.LL / P.T

/-- **L₆ — conductor spread.** `s·⟨shift⟩/ℒ` = `s·0.5/ℒ` over `q ≤ Q`.
Shape: relative. Source: §12.2 (`⟨log q⟩_{φ*} = log Q − 1/2`).
In the script: `minor` term 1. Verified: 3.63e−3 / 1.03e−3 / 3.56e−4.
This is the row that prices Prop 3.1's `r₁` (the trace deficit). -/
def L₆ (F : Family) (P : ParamsQ) : ℝ := sZone * F.conductorShift / P.LL

/-- **L₇ — zone boundary (Lemma 4.4).** `1.3·7.7·√(C·log(Tℒ)/(Tℒ))`.
Shape: relative. Source: §4 (Lemma 4.4).
In the script: `minor` term 2. Verified: 9.94e−3 / **5.39e−4** / 5.09e−5.
(That 5.39e−4 is the figure Lemma 4.5's prose appears to have borrowed — see D-1.) -/
def L₇ (F : Family) (P : ParamsQ) : ℝ :=
  1.3 * 7.7 * Real.sqrt (F.Cconst * Real.log (P.T * P.LL) / (P.T * P.LL))

/-- **L₈ — out-zone cross term.** `(dP/d log C)·√(24/π)·√(log L/(T·L))`.
Shape: `δP` (payoff units). Source: §4 (Lemma 4.3;
`ρ ≤ √(24/π)·√((log L + O(1))/(TL))`).
In the script: `minor` term 3. Verified: 1.88e−5 / 9.57e−7 / 8.81e−8.
See D-2: §4's quoted figures mix the r = 3 and r = 3.5 designs. -/
def L₈ (P : ParamsQ) : ℝ := dPdlogC * cCross * Real.sqrt (Real.log P.LB / (P.T * P.LB))

/-- **L₉ — the D_T-smearing class.** `(dP/d log C)·0.2/T`.
Shape: `δP`. Source: §4 ("the D_T-smearing, which is O(1/T)").
**Label inferred** — `budget_q.py` attributes it only to "L6..L11 of round 5", a document
that is not shipped. In the script: `minor` term 5.
Verified: 4.63e−9 / 3.62e−11 / 7.73e−13. -/
def L₉ (P : ParamsQ) : ℝ := dPdlogC * 0.2 / P.T

/-- **L₁₀ — the grid/shell class.** `3·(log ℒ)²/L²`.
Shape: relative. Source: §4/§9 (grid resonance shells, ledger row 14).
**Label inferred**, and note that this is the **second-largest** minor row
(1.06e−2 at 10²⁵, 1.12e−3 at 10¹⁰⁰) — not negligible bookkeeping; it deserves a named prose
source. In the script: `minor` term 6. Verified: 1.06e−2 / 1.12e−3 / 1.75e−4. -/
def L₁₀ (P : ParamsQ) : ℝ := 3 * (Real.log P.LL) ^ 2 / P.LB ^ 2

/-- **L₁₁ — sieve budget correction.** `(dP/d log C)·Q^{λ−2}`, written
`exp((λ − 2)·log Q)`.
Shape: `δP`. Source: §4 (`X + Q² − 1 = Q²(1 + O(Q^{−δ}))`).
**Label inferred**. In the script: `minor` term 7.
Verified: 1.4e−26 / 7.3e−87 / ~1e−240.
**Rule 17:** the exponent is `λ − 2`, which is negative precisely because `λ < 2`
(`ParamsQ.Valid.lam_lt_two`) — it is a `λ < 2` fact and has nothing to do with `λ ≤ 1`. -/
def L₁₁ (P : ParamsQ) : ℝ := dPdlogC * Real.exp ((P.lam - 2) * Real.log P.Q)

/-- **L₁₂ — in-zone cross term (Lemma 4.5).** `0.35·C·√(24/π)·√(log L/(T·L))`.
Shape: `δP`. Source: §4 (Lemma 4.5) — **new since rev 1**, and NOT one of
E6_ENUMERATION §5's 17 rows. Distinct from L₇/ledger row 13: "the out-zone
pricing does NOT cover this — the in-zone charge is ~50× larger and was previously
unpriced"; the script's ratio `L₁₂/L₈ = 56.6×` reproduces that.
In the script: `minor` term 4, explicitly labelled `# L12: IN-ZONE cross (Lemma 4.5)`.
Verified: 1.06e−3 / **5.41e−5** / 4.99e−6 — see **D-1** for the prose/script mismatch. -/
def L₁₂ (F : Family) (P : ParamsQ) : ℝ :=
  sensInzone * F.Cconst * cCross * Real.sqrt (Real.log P.LB / (P.T * P.LB))

/-- The `minor` bundle: `L₆ + L₇ + L₈ + L₉ + L₁₀ + L₁₁ + L₁₂`.
Verified: 0.02519 / 0.00274 / 0.00059, reproducing `log_table2.txt`'s `minor` column to all
printed digits. -/
def minorRows (F : Family) (P : ParamsQ) : ℝ :=
  L₆ F P + L₇ F P + L₈ P + L₉ P + L₁₀ P + L₁₁ P + L₁₂ F P

/-- **§10.3's TOTAL**: `zone + ramp + buffer + ends + minor`, and, by the accounting note in
the module header, Proposition 3.1's bracket. The `zone` row is taken in the linear form so
that this `def` has a real body; `budgetTotalCurv` is the script's curvature-honest form
(D-4).
Paper §10.3: "**Total = O(log log Q/log Q)**, pinned by the two zone terms".

### 🚩 **DECISION D35: the buffer row of this total is `L₄` — the
### paper's own row, at the SHARP zero density, which the artifact ASSUMES and says so.**
### **D34 is REVERSED here. D10 is reversed with it.**

**History, in one paragraph.** Fill pass 9's finding **F32** was that the frozen body
(`… + L₄ P + …`) and decision **D10** ("the artifact ships the PROVED buffer constant") are
inconsistent: with `r₁, r₂, r₄, r₅` forced to the budget's own rows, clause 7 of
`assembly_at_lamStar` plus the ring identity of `propBracket_le_budgetTotal` gives
`3r₃ ≤ L₄ + L₅ + L₉`, hence — once D27's margin-0 closing condition pins `D₀ = Θ(ℒ²)` —
`r₃ ≤ rowR3·(1 + O(log ℒ/ℒ))`, the SHARP density; while
`bufferRowProved A₀ P / L₄ P = πA₀(ℒ + log 4T)/ℒ ≈ πA₀ ≈ 255` uniformly in `Q`. **D34**
resolved that in D10's favour, by enlarging this total to charge `bufferRowProved EFChi.A0`.
**D35 resolves it the other way**, and that is what this body now is.

**Why the reversal is right.** D10's rationale was that a formal artifact must not depend on a
row it cannot discharge from its own imports. But the **paper already depends on it and says
so**: §10.3 flags this row as "priced at the SHARP zero density …, not at the proved absolute
`A₀` of §9, which is larger" and calls it "the ONE row not at its proved constant" (§10.4,
). An artifact that silently charges `≈ πA₀ ≈ 255×` more is not more faithful;
it is a *different accounting presented as the same one*. Naming the assumption instead
reproduces the paper's own epistemic position exactly — the same pattern as
`ZetaQ.l2_concentration_exists`, which reproduces §6's citation of Lemma 6.1 rather than
re-proving it. And it keeps this total frozen at the paper's own rows, which is what
`assembly_at_lamStar`'s `r₃` slot wants (that is D34's own analysis, quoted above).

**Where the assumption is named:** `SharpZeroDensity F Qn P` (below), threaded as an explicit
hypothesis on `buffer_row_sharp` and hence on `assembly_clauses_at_design`. Nothing about the
sharp density is hidden inside a `def`.

**The disclosure that goes with it, all RETAINED and none of it deleted:** `bufferRowProved`
(§9's q-uniform row at the proved `A₀`), `buffer_row_proved` (that row, *proved* from `H6` via
`FamNIIUpper` + `FamRvMLower`), `buffer_row_gap` (`L₄ ≤ bufferRowProved`, the mandated-flag
direction) and the private `bufferProved_le_L4` (`bufferRowProved EFChi.A0 ≤ 1000·L₄` in the
design regime, i.e. the `≈ πA₀` factor, machine-checked). Together they are the record of
exactly what *is* provable from the artifact's own imports and of the price of the two
conventions' difference. That record is what makes the assumption honest rather than hidden.

**The finite-Q evidence that motivated D34, kept as the record of why D10 could not simply be
left in place.** At the proved constant the buffer row is `≈ 255×` its printed value — `1.9`
instead of `7.5×10⁻³` at `Q = 10¹⁰⁰` — and the ratio buffer-row : rate-term at `r = 3.5` runs

| log Q | 58 (10²⁵) | 230 (10¹⁰⁰) | 691 (10³⁰⁰) | 2302 (10¹⁰⁰⁰) |
|---|---|---|---|---|
| proved buffer / rate | 84 | 23 | 9.7 | 4.3 |

i.e. **the proved row dominates the rate term across the whole range §10.4 tabulates**,
becoming subordinate only far beyond `Q = 10¹⁰⁰⁰` (the rate class is nevertheless preserved,
exactly on the paper's range `r + ε > 3` — D34's "checked, not assumed"). Together with **F23**
(the ends row at the constant Lemma 8.2 actually delivers exceeds 1 at `Q = 10¹⁰⁰`; see
`L₅proved`) the two rows pushed §10.4's non-vacuity threshold from `≈10²⁰` to `≈10²⁹⁰`.
**D35 removes the buffer's ≈20% share of that damage at zero cost to rigour**, because the
assumption it substitutes is the paper's own, declared. F23 (≈80%) stands, and §10.4 remains
an orientation table whose convention is now the same one the artifact charges.

**The zone row is `zoneRowLinear F P` — family-aware, `sZoneDyadic = 0.5485`
for the dyadic family (paper §10.5). For `Family.qle` the body is unchanged; see the module
header.** -/
def budgetTotal (F : Family) (P : ParamsQ) : ℝ :=
  zoneRowLinear F P + L₃ P + L₄ P + L₅ P + minorRows F P

/-- `budgetTotal` with the script's curvature-honest zone row (D-4); the payoff `P(C,·)` of
§11 is a parameter because it lives in `ZetaQ/Payoff.lean`. Carries the same buffer row (`L₄`, D35), so
that the two totals differ in the zone row and nowhere else. -/
def budgetTotalCurv (payoff : ℝ → ℝ → ℝ) (F : Family) (P : ParamsQ) : ℝ :=
  zoneRowCurv payoff F P + L₃ P + L₄ P + L₅ P + minorRows F P

/-! # §10.3 → Proposition 3.1: each `rᵢ` bounded by its row

Paper §3: "the explicit budget of §10.3 (whose rows are exactly the `rᵢ`)"; §10.5's wiring
table:

| Prop 3.1 hypothesis                   | supplied by            | rows |
|---------------------------------------|------------------------|------|
| (ii) `tr Ĝ ≥ (1−r₁)𝒩`                 | §9 trace               | L₆ (+ the L₃ trace-side residue, argued to cancel — Q7) |
| (ii) `‖Ĝ‖²_F ≤ (κ_C+r₂)𝒩`             | §4 + §5 + §6           | L₁, L₂, L₃, L₇, L₈, L₁₀, L₁₁, L₁₂ |
| (iii) `N_{II,fam} ≤ r₃𝒩`              | §9                     | **L₄** 🚩 |
| (iv) `B_tr ≤ r₄𝒩`, `B_F ≤ r₅√𝒩`       | §7 + §7.3              | absorbed (θ₀ superexponentially small); L₅ separate |
-/

/-- `r₁`'s row: the trace deficit, priced by the conductor-spread row L₆ — **at `L₆/4`,
because the printed rows are the FOLDED ones. REPAIRED THIS PASS (D14).**

**WHAT WAS WRONG.** This read `rowR1 := L₆`, which contradicts the module header's own
accounting note ("Prop 3.1's coefficients `4, 1, 3, 4` are already folded into the row
constants") and the way its sibling `rowR3 := L₄/3` implements exactly that. The consequence
was that `propBracket` charged `4·rowR1 = 4L₆` while `budgetTotal` contains `L₆` once, so
`propBracket_le_budgetTotal` failed by a positive residue `3L₆ − L₅ − L₉`, verified at
`+9.7×10⁻³` (`Q = 10²⁵`), `+3.1×10⁻³` (`10¹⁰⁰`), `+1.1×10⁻³` (`10³⁰⁰`) — and positive at
every design point, since `L₆ = Θ(1/ℒ)` while `L₅ = Θ(ℒ log ℒ/T)` with `r ≥ 3`, so
`L₆/L₅ → ∞`.

**WHY `L₆/4` IS THE PAPER'S READING.** `budgetTotal` reproduces `log_table2.txt`'s TOTAL
column to all printed digits, and §10.4's headline `P_eff = P − TOTAL` reproduces
`+0.20 / +0.61 / +0.68 / +0.71`. Since §3's Prop 3.1 subtracts its bracket from `2 − κ_C`,
"the budget rows ARE the `rᵢ`" can only mean bracket = TOTAL, i.e.
`4·r₁ = L₆`. **The clause that disagrees is §10.5's wiring table, which reads `r₁ = L₆`.**

**THE ALTERNATIVE, RECORDED RATHER THAN HIDDEN.** If §9's trace theorem can deliver only
`(1 − L₆)·𝒩 ≤ tr Ĝ`, then the wiring table is right and it is §10.3's Table 2 that
undercharges the conductor row by `3L₆`; the repair is then `budgetTotal += 3·L₆` instead,
and §10.4's `P_eff` figures fall by `0.010 / 0.003 / 0.001` at `10²⁵ / 10¹⁰⁰ / 10³⁰⁰`.
**Either way the headline is untouched**, because `3L₆ = Θ(1/ℒ) = o(log log Q/log Q)` — the
rate class and `P` do not move. Suggested paper edit: make §10.5's wiring table say
`4r₁ = L₆`, matching `3r₃ = L₄` in the row above it.

Q7 recorded, unchanged: §10.3 argues [R]'s trace-side `w/L` is NOT a separate charge here
(the hat normalisation `a := L⁻¹∫φ²` is computed for the TAPERED φ, so the taper's
first-order mass deficit cancels in `tr Ĝ` against `a𝒩`); the fully conservative alternative
reading is `r₂ + 4r₁ = 10w/L`, costing ≤ 0.012 at `Q ≥ 10¹⁰⁰`. `cRamp` is a `def` so both
compile. -/
def rowR1 (F : Family) (P : ParamsQ) : ℝ := L₆ F P / 4

/-- `r₂`'s row: the Frobenius excess over `κ_C·𝒩` — the zone rows, the ramp row, and the
five `δP`/relative minor rows that are not L₆. The zone row is at the family's secant
(`zoneRowLinear F P`, `sZoneDyadic` for the dyadic family). -/
def rowR2 (F : Family) (P : ParamsQ) : ℝ :=
  zoneRowLinear F P + L₃ P + L₇ F P + L₈ P + L₁₀ P + L₁₁ P + L₁₂ F P

/-- `r₃`'s row: the buffer, `2D₀/T` (so that Prop 3.1's `3r₃` is the printed `6D₀/T` = L₄).
🚩 Same flag as `L₄`: priced at the sharp zero density. -/
def rowR3 (P : ParamsQ) : ℝ := L₄ P / 3

/-- `r₄`'s row: `B_tr/𝒩 = θ₀/(aL·(T/2π)ℒ)`, using `𝒩 ≍ |𝔉|·(T/2π)·ℒ` — the `|𝔉|` cancels,
which is §7.3's point that "no negative power of Q is demanded anywhere".
Superexponentially small: §7 bounds `θ₀ ≤ exp(−(4/e)√(wD₀/A))·prefactor` at the FREE `D₀`.

🚩 **THE `≍` WAS USED AS `=`, AND IT LEANED THE WRONG WAY.  REPAIRED THIS PASS
(policy D17); the reasoning is at `famAvgL`.**  Because `Btr = |𝔉|θ₀/(aL)`, the clause
`Btr ≤ rowR4·𝒩` of `pair_rows` is *equivalent* (for `θ₀ > 0`, `aL > 0`) to
"`𝒩/|𝔉| ≥` the row's surrogate for `𝒩/|𝔉|`".  At the old surrogate `(T/2π)·ℒ` that reads
`|𝔉|(T/2π)ℒ ≤ 𝒩`, and the family Riemann–von Mangoldt count is
`𝒩 = |𝔉|(T/2π)(ℒ − ⟨log q⟩-shift + 2 log 2 − 1) + O(|𝔉| log QT)` — for `Family.qle`,
`|𝔉|(T/2π)(ℒ − 0.113706)`, **below** the required value at every `Q`.  So the frozen row
made `pair_rows` FALSE at every `θ₀ > 0` for Theorem 1's own family.  (For `Family.dyadic`,
shift `0.26895`, the old surrogate erred the safe way.)

**The surrogate is now the true family average `famAvgL F P = ℒ − ⟨shift⟩ + 2 log 2 − 1`**,
which is what RvM + §12.2 deliver, which prices the conductor spread once (in `L₆`) instead
of twice, and which makes the pair rows satisfiable for both families.  See `famAvgL` for
the derivation, the rejected alternative, and the (nil) cost downstream: the change is
`4.6×10⁻⁴` relative at `Q = 10¹⁰⁰` and `rowR4`/`rowR5` are absorbed by `hpair` inside
`propBracket_le_budgetTotal`, so Theorem 1 does not move. -/
def rowR4 (F : Family) (P : ParamsQ) (θ₀ : ℝ) : ℝ :=
  θ₀ / (P.aQ * P.LB * (P.T / (2 * Real.pi) * famAvgLlow F P))

/-- `r₅`'s row: `B_F/√𝒩 = θ₀/(aL·√((T/2π)⟨ℒ⟩_𝔉))` — again `√|𝔉|` cancels.  Same F24 repair
as `rowR4`: the surrogate for `𝒩/|𝔉|` is the true family average, not `(T/2π)ℒ`. -/
def rowR5 (F : Family) (P : ParamsQ) (θ₀ : ℝ) : ℝ :=
  θ₀ / (P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P))

/-- **Prop 3.1's bracket at the design of record.** -/
def propBracket (F : Family) (P : ParamsQ) (θ₀ : ℝ) : ℝ :=
  4 * rowR1 F P + rowR2 F P + 3 * rowR3 P + 4 * rowR4 F P θ₀
    + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P) + rowR5 F P θ₀ ^ 2

/-- **Prop 3.1 (ii), trace side, at its budget row.** §9's trace input (μ_q main term +
RvM + the prime part by §5's Ramanujan orthogonality) delivers `(1 − r₁)𝒩 ≤ tr Ĝ_fam` with
`r₁ = rowR1 = L₆/4`, the conductor-spread row of §12.2 **at its folded coefficient**.

**Note the change of reading (D14).** `rowR1` was `L₆`; it is now `L₆/4`, which
is what makes `budgetTotal` the TOTAL column of `log_table2.txt` and `propBracket` its
bracket — see `rowR1`'s docstring for the failing instance, the alternative reading, and the
suggested paper edit. This *strengthens* the statement fourfold, so it is the one place in
this repair where the burden moves onto §9 rather than off it; if §9 can supply only
`(1 − L₆)·𝒩 ≤ tr Ĝ`, the repair to make instead is `budgetTotal += 3·L₆`, at a cost of
`≤ 0.010` in §10.4's finite-Q orientation figures and nothing at all asymptotically.

Paper §10.3, §10.5; §9; §12.2.
Depends on: `ZetaQ.trGhatFam`, `ZetaQ.NfamQ`, `L₆`.
Rule 17: hypotheses are `DesignOfRecord`, whose `lam = F.lamStar > 1` and whose `D₀` is
constrained only from below by `10L` and above by `T/3`. No λ ≤ 1, no X ≤ T, no D₀ = √T.

**Deliberately NOT given an explicit hypothesis from another section.**  The D18
pattern was applied to every row where a *distinct* named fact exists upstream
(`FamRvMLower`, `FamNIIUpper`, `FamSizeLower`, `SharpZeroDensity`, `hpair`).  Here it does
not: this file's entire vocabulary on the trace side is `trGhatFam`, `NfamQ` and `rowR1`, so
any `Prop` naming §9's deliverable would be this inequality with the quantifier moved.  The
statement is therefore left as the genuine interface to §9, to be discharged where
`gridGramEntry` is actually evaluated (`ZetaQ/EFChi.lean` + `ZetaQ/CharSums.lean`).  Note
the `L₆/4` reading (D14) makes the burden on §9 fourfold; if §9 delivers only `(1 − L₆)𝒩`,
the repair is `budgetTotal += 3L₆`, not a weakening here — see `rowR1`.

**Fill pass 9 — re-checked with `ZetaQ.EFChi` NOW IN THE IMPORT GRAPH, and the conclusion is
unchanged.**  `EFChi.gridGramEntry_eq` does evaluate `gridGramEntry` — as
`Zeta23.ThmE.GentryChi P.toParams (parity χ) q (χ ·) P.T k l` — and
`EFChi.rtrace_hatQ_gridGram_eq_Gz` carries the hat trace across to the zero side.  But both
are IDENTITIES.  Downstream of them the only quantitative statement in the graph is
`Zeta23.ThmE.seamBChi` (`Zeta23/ThmE/AssemblyQ.lean:239`), which gives
`|tr Ĝ_χ − N_χ| ≤ C₁√(X)/a` — and at `λ* = 1.2507 > 1`, `√X = (QT/2π)^{0.6254}` is `10^{67}`
against a per-character `N_χ ≈ 7×10^9` at `Q = 10¹⁰⁰`, i.e. the seam's error exceeds the
quantity being estimated by 57 orders, and still does after summing over `𝔉_Q`.  That is
precisely why the paper's trace theorem is §5's family Ramanujan orthogonality and not the
per-character seam — plus `rtrace_hatQ_gridGram_eq_Gz` needs `1 < q`, which `Family.qle`'s
`q = 1` member fails.  So the imports do NOT unlock a non-circular statement here; the finding
is now settled on the mechanism rather than on absence of search, and is not to be
re-opened.

**✅ F59 — PROVED EVENTUALLY IN `Q`: `trace_row_eventually` (section `TraceRow`, foot of
this file), for BOTH families, `[propext, Classical.choice, Quot.sound]`.** Row 1 is closed by the
q-uniform μ_χ chain (`ZetaQ/MuqUniform.lean`) through `trace_row_of_muPart`; its obligation `hmu`
is `rowR1·𝒩 ≥ (row-2 Ramanujan bound) + (RvM error) + (μ-part error)`, and each term is absorbed
only EVENTUALLY: the row-2 bound `≈ 8.7·Q·L²·√X` falls below `rowR1·𝒩 ≈ 0.0101·|𝔉|·T` from
`Q ≈ 10¹⁰` on (`Row2Numeric.row2_error_eventually`; at `Q = 10³`, `r = 3` it exceeds it by
`≈ 10³`), RvM's `A·log(Q(T+2))` needs `400πA·log(Q(T+2)) ≤ T` (`rvm_error_small`), and the μ-part's
`cErr(c_W)` needs `T ≥ 400π·cErr(c_W)`. `DesignOfRecord`'s own clauses (`Q ≥ 3`, `T ≥ 300`,
`10ℒ log ℒ ≤ T`, `10L ≤ D₀ ≤ T/3`, the closing condition) imply none of these thresholds, so THIS
statement, at every design point, is not reached by the route — and not refuted either. It stays
`sorry`, frozen; see the module header for the downstream consequence (the eventual form
suffices for `assembly_at_lamStar`'s `∃ Q₀`). **Nothing in the tree consumes this declaration**
(`audit/RevDepZetaQ.lean`); the shipped theorems use `trace_row_eventually` through
`ZetaQ/JoinCert.lean`. -/
theorem trace_row (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) :
    (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn := sorry

/-- **Prop 3.1 (ii), Frobenius side, at its budget row.** §4's two-zone decomposition
(Lemmas 4.1–4.5) + §5's orthogonality (Lemmas 5.1–5.3) + §6's multiplicative large sieve
(Lemma 6.1) deliver `‖Ĝ_fam‖²_F ≤ (κ_C + r₂)𝒩` with `r₂ = rowR2`.

Paper §10.5's wiring table; §§4, 5, 6.
Depends on: `ZetaQ.frobSqGhatFam`, `Family.kappaC`, `rowR2`.
Rule 17: as `trace_row`. Note `L₁₁`'s exponent `λ − 2 < 0` uses `lam_lt_two`, never
`lam ≤ 1`.

**Fill pass 6 — same reason as `trace_row` for not pre-wiring**: `frobSqGhatFam`, `NfamQ`
and `rowR2` are this file's whole Frobenius vocabulary, so a named hypothesis would restate
the conclusion.  This is the paper's main estimate and belongs where the two-zone
decomposition lives (`ZetaQ/Zones.lean` + `ZetaQ/Sieve.lean` + `ZetaQ/CharSums.lean`).

**Fill pass 9 — re-checked with `ZetaQ.EFChi` imported; unchanged, for `trace_row`'s reason
verbatim.**  `EFChi.frobSq_hatQ_gridGram_eq_Gz` is an identity between the prime- and
zero-side Frobenius squares, and `Zeta23.ThmE.seamBChi`'s Frobenius half needs `[eq:tr2]-χ`
(`htr2`, the second-moment trace bound) as an input — which is §§4–6's two-zone estimate, the
very thing this statement asks for.  Circular, so nothing is gained.

**⚠ SUPERSEDED.** That circularity finding is correct ABOUT THIS FILE'S OWN VOCABULARY and about the
`seamBChi` route, and it remains the reason not to attempt `frobenius_row` from `EFChi` alone.
It is NOT a statement that no route exists: `ZetaQ/Zones.lean` §12 and §14 now carry a proved,
cap-free §4 → §3 bridge (`frobSq_gridGram_sub_Mform_le`, on `Ends.lem_ends_nu_W_L`), and
`Budget` imports `Zones`.  What remains for `frobenius_row` is the `μ_q` main-term half
([R]'s `ThmE.mainTr2Chi`, never wired into `ZetaQ`) plus §4's endpoints; it is no longer
"unreachable".  See `Zones.bridge_route_marker`.  Note also that `rowR2`
is now known nonnegative (`rowR2_nonneg`), which is what `EFChi.prop31_fam`'s `hκr₂` slot
needs and which `assembly_clauses_at_design` consumes.

**⚠ F58 — NOT PROVABLE BY THE PAPER'S METHOD AS STATED; see the F58 block in the
module header, F58).** `DesignOfRecord` pins the FLAT taper
(`phiQ = ϱ((L/2 − |u|)/w)`, `TaperProfile ϱ`) at `λ = λ*`, while `F.kappaC = 2 − 0.7212835668`
is §11's optimum over profiles `v = φ²`. §§4–6 deliver, for the flat taper, exactly
`B_flat(λ*) = 1.4085520` (paper's `fb.flat_v_payoff`), against `κ_C + rowR2 ≈ 1.38` at
`Q = 10¹⁰⁰` and `→ 1.2787`. The three gaps listed above (row 8 summed, row 9 at the family, the
§11 link) are downstream of this: the §11 link is unstatable because the construction's
profile and the certified profile are different objects. Repair requires the profile-weighted
window (`φ = p(u/ℒ)·ϱ₂((L/2−|u|)/w)`, [R]'s `Params.atD` idiom) or a restatement at the flat
constant.

✅ **BOTH WERE DONE, ELSEWHERE, AND THIS STATEMENT IS FROZEN.** The window was repaired
(`ZetaQ/Defs.lean` + `ZetaQ/Window.lean` + `ZetaQ/DesignProfile.lean`) and the row was
restated at the CERTIFIED four-digit constant `κ_cert = 2 − P_cert` instead of the ten-digit
`F.kappaC` — `ZetaQ/JoinCert.lean` for why, `ZetaQ/HFrob.lean` `hfrob_*_of_design` for the
proved row, at all six families. This declaration keeps the paper's ten-digit statement and
its `sorry`; **nothing in the tree consumes it** (`audit/RevDepZetaQ.lean`). -/
theorem frobenius_row (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) :
    frobSqGhatFam P F Qn ≤ (F.kappaC + rowR2 F P) * NfamQ P F Qn := sorry

/-- **🚩 The sharp-zero-density hypothesis** — option (b) of the buffer-row decision.
`N_{II,χ}` at the true `T/2π`-per-character scale, aggregated: what §10.3's budget charges
and what §9's *proved* absolute constant does not give. Carried as a NAMED `Prop` so that
every consumer of `buffer_row_sharp` is auditable.
Paper §10.3, §10.4.

**F24 repair (D17), same as the rows.**  This read `2·(D₀/2π)·ℒ·|𝔉|`, i.e. the same
`ℒ`-surrogate for `𝒩/|𝔉|` that `rowR4`/`rowR5` carried, and it therefore *overshot* the row
it was supposed to feed by `⟨shift⟩ − (2 log 2 − 1) = 0.1137` nats for `Family.qle` — which
is why the earlier passes recorded that "the route through `SharpZeroDensity` cannot close
`buffer_row_sharp` at all".  At the true family average `famAvgL` the two line up, and the
hypothesis stays satisfiable with room: what §9 actually produces at the sharp density is
`(D₀/π)|𝔉|(ℒ − ⟨shift⟩ + (log 2)/2)`, and `(log 2)/2 = 0.3466 < 0.3863 = 2 log 2 − 1`, so
this `Prop` is weaker than the truth by the same `0.0397` nats the module header quotes. -/
def SharpZeroDensity (F : Family) (Qn : ℕ) (P : ParamsQ) : Prop :=
  NIIFamQ P F Qn ≤ 2 * (P.D0 / (2 * Real.pi)) * famAvgLlow F P * F.sizeR Qn

/-- **The family Riemann–von Mangoldt LOWER bound, at the true family average.**
`|𝔉|·(T/2π)·⟨ℒ⟩_𝔉 ≤ 𝒩`.

This is the input every previous pass recorded as "missing from the import graph", and F19
named it in the form `|𝔉|(T/2π)·ℒ ≤ 𝒩` — which is **FALSE** for `Family.qle` and was
correctly refused as a hypothesis, because assuming it would have made the theorems vacuous
rather than blocked.  At the true average `famAvgL` it is exactly the leading term of the
q-uniform RvM count summed over `𝔉_Q` (`ZetaQ.EFChi.rvmChi_main_uniform` + §12.2's conductor
spread), so it is satisfiable for **both** families, and it is threaded in explicitly —
the D18 pattern — rather than assumed silently.

⚠ **WHAT IS OWED — BOTH HALVES OF THIS PARAGRAPH WERE WRONG. CORRECTED (finding F50,
and it is proved); see the `FamilyBridge` section below for the argument and the Lean.**

*It used to read:* "Discharging this `Prop` needs the FAMILY step of §12.2
(`⟨log q⟩_{φ*} = log Q − ⟨shift⟩`), which is `Family.conductorShift` here but is not proved
anywhere in the tree, plus absorption of RvM's `O(|𝔉|·log QT)` error into the `0.0397`-nat
slack that `famAvgL` leaves against the true `(log 2)/2` average.  That absorption is
legitimate — the error is smaller by a factor `≈ T/ℒ` — but it is §12's obligation, not
§10's, which is precisely why this is a hypothesis and not a lemma."

**(a) §12.2's family step IS proved** — `Normalisation.avgLogCond_asymp` (N6) and, in the form
that is actually usable here, `Normalisation.N2.Alog_bound` with an explicit two-sided error at
every `N`.  `Budget → Zones → Normalisation`, so it was citable all along.  It is now cited:
`famLogCond_qle_bound` below is §12.2's family step at the effective constant.

**(b) The absorption does not exist.**  `0.0397 = (2log2 − 1) − (log 2)/2` is the BUFFER
comparison of the F19 block — it belongs to `buffer_row_sharp`/`SharpZeroDensity`.  Here there
is nothing to absorb into: `Zeta23.ThmE.ell1q q T = log(qT/2π) + 2log2 − 1`, so the φ*-average
of `ell1q` over `𝔉_Q` is `ℒ − ⟨shift⟩ + 2log2 − 1`, which is **exactly** `famAvgL`.  This
`Prop` therefore asserts precisely that RvM's aggregate error is FAVOURABLY SIGNED, and
`EFChi.rvmChi_main_uniform` is two-sided.  **The shortfall is `≈ 2πA/T`, i.e. `Θ(1/T)`, and it
is not absorbable at any `Q`.**  `famRvM_lower_from_tree` below is this display minus that
residue and the (negligible) §12.2 one, with no free hypotheses.  Discharging the `Prop` itself
needs `famAvgL` lowered by a `Θ(1/T)` row — **which is exactly what `rvmSlack` now does, so
this `Prop` IS discharged: `famRvMLower_of_design`.**  The cost is dominated by
`L₄ = 6D₀/T` and moving no printed figure.

**🚩 F32 does NOT change the content of this `Prop`, and that is deliberate.** The `q = 1`
exclusion (`Family.moduli Family.qle Qn = Finset.Icc 2 Qn`) removes one character from `NfamQ`,
and `ZetaQ.Family.size` was written out over the *same* index set so that `F.sizeR` remains
exactly `|𝔉_Q|` — so both sides drop the same member and the inequality is the same statement
about a family one character smaller. What F32 *does* leave here is a `Defs`-level bookkeeping
step for whoever discharges it: `sizeR = famCard − 1` for `Family.qle`, since `famCard` is
frozen at `Finset.Icc 1 Qn` and `φ*(1) = 1`. That is `O(Q^{-2})` relative against
`|𝔉_Q| ≍ (18/π⁴)Q²` and is spelled out at `ZetaQ.Family.size`.
Paper §12.2; §9. -/
def FamRvMLower (F : Family) (Qn : ℕ) (P : ParamsQ) : Prop :=
  F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgLlow F P) ≤ NfamQ P F Qn

/-- **§9's family buffer bound, as a named `Prop`** — `ZetaQ.EFChi.NII_fam_le` **at the
conductor-averaged step**:

    N_{II,fam} ≤ 3A₀D₀·(ℒ − ⟨shift⟩ + log 8π)·|𝔉|.

⚠ **The stated REASON for this being a `Prop` is false and is corrected.**  It read
"`ZetaQ/Budget.lean` does not import `ZetaQ/EFChi.lean` (same reason as `EndsFamBound`)" —
but this file **does** `import ZetaQ.EFChi`.  §9's
deliverable is reachable from here directly, and `NIIFam_avg_le` below is exactly the
"re-proved one step earlier" form this docstring asks for, for BOTH families.  What keeps
this a `Prop` is the §12.2 residue, not the import graph: see `FamilyBridge` below, where
`famNII_upper_eps_from_tree` proves this statement verbatim except `⟨shift⟩ ↦ ⟨shift⟩ − ε`
for every `ε > 0`, and the exact form is shown to be out of reach of any two-sided conductor
envelope (the deviation `⟨log q⟩ − log Q + ½` oscillates in sign).  The `Prop` is threaded in
explicitly — the D18 pattern.

**Why the conductor-averaged form and not `NII_fam_le`'s printed one.**  `EFChi.NII_fam_le`
prints `3A₀D₀(ℒ + log 4T)|𝔉|`, having used `log q ≤ log Q ≤ ℒ` per character.  Keeping
`log Q = ℒ − l` and averaging `log q` over `𝔉_Q` with §12.2's spread
(`⟨log q⟩ = log Q − ⟨shift⟩`, `Family.conductorShift`) gives instead
`Σ_q φ*(q)·3A₀D₀(log q + log 4T) = 3A₀D₀|𝔉|(ℒ − ⟨shift⟩ + log 8π)`, since
`log 4T − l = log 4T − log(T/2π) = log 8π`.  **This one nat matters**: from the printed form
the row is not provable.  Cancelling the common `3A₀D₀(ℒ+log4T)|𝔉| > 0`,
`buffer_row_proved` against the printed form is *equivalent* to `ℒ ≤ ⟨ℒ⟩_𝔉`, i.e. to
`⟨shift⟩ ≤ 2 log 2 − 1 = 0.3863` — **false for `Family.qle`** (`⟨shift⟩ = 1/2`) by exactly
the `0.1137` nats of F19/F24, at every `Q`.  The averaged form clears it with room: the
residue is `(2 log 2 − 1 + log 4T − log 8π)·ℒ + log 4T·(2 log 2 − 1 − ⟨shift⟩) ≥ 3.12` at
`ℒ ≥ 1`, `T ≥ 300`.

So this is the same F19/F24 diagnosis a third time — a step that replaces `⟨log q⟩` by its
crude majorant `log Q` double-prices the conductor spread that `L₆` already charges — and it
is fixed the same way, at the average §12.2 actually delivers.  Discharging this `Prop`
needs `EFChi.NII_fam_le` re-proved one step earlier (its own proof is `log(4qT) = log q +
log 4T`, so the averaged form is the sum before the `log q ≤ ℒ` bound) plus §12.2's spread —
the same two obligations `FamRvMLower` carries.
Paper §9, §12.2; `ZetaQ.EFChi.NII_fam_le`. -/
def FamNIIUpper (F : Family) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ) : Prop :=
  NIIFamQ P F Qn
    ≤ 3 * A₀ * P.D0 * (P.LL - F.conductorShift + Real.log (8 * Real.pi)) * F.sizeR Qn

/-! # §12.2 → §10: THE FAMILY BRIDGE, AND WHY THE TWO `Prop`s ABOVE STAY `Prop`s

**Finding F50.** Both docstrings above say the blocker is that §12.2's
conductor spread `⟨log q⟩_{φ*} = log Q − ⟨shift⟩` "**is not proved anywhere in the tree**"
(and in the module header). **That claim is false.** It is proved, in
`ZetaQ/Normalisation.lean`, and reachable from here today with no import change
(`Budget → Zones → Normalisation`):

  * `Normalisation.avgLogCond_asymp` (`:1776`) — N6, `⟨log q⟩_{φ*, q≤Q} = log Q − 1/2 + o(1)`;
  * `Normalisation.avgLogCondDyadic_asymp` (`:1803`) — N7, limit `log 2/3 − 1/2`;
  * `Normalisation.N2.Alog_bound` (`:686`) — **the usable form**, the same statement with an
    EXPLICIT two-sided error at every `N`: `|Σ_{q≤N}φ*(q)log q − (18/π⁴)N²(log N − ½)| ≤
    13N(1+log N)³`; and `N2.Astar_bound` (`:487`) for the denominator.

The two limits match `Family.conductorShift` exactly — `1/2` for `qle`, and
`1/2 − (log 2)/3 = 0.2689509…`, now the coded value for `dyadic` (the literal `0.26895`,
`9.4·10⁻⁷` below it, was the coded value before). The bridge is built
below, and `famLogCond_qle_bound` is §12.2's family step at the effective constant.

**What the bridge then shows, and it is the point of this section: NEITHER `Prop` is
dischargeable, and the two fail for DIFFERENT reasons.**

* **`FamRvMLower` has ZERO slack, by construction.** `Zeta23.ThmE.ell1q q T =
  log(qT/2π) + 2log2 − 1`, so the φ*-average of `ell1q` over `𝔉_Q` is
  `⟨log q⟩ + l + 2log2 − 1 = ℒ − ⟨shift⟩ + 2log2 − 1`, which is **exactly** `famAvgL`. The F24
  repair made that the surrogate deliberately (it "prices the conductor spread once"), and the
  price is that `FamRvMLower` now asserts precisely that RvM's aggregate error is
  **favourably signed**. `EFChi.rvmChi_main_uniform` is two-sided (`|·| ≤ A log(q(T+2))`) and
  gives `𝒩 ≥ main − error`, never `≥ main`. Nothing in the graph supplies an error-free lower
  bound, and the shortfall is `≈ 2πA/T` relative — `Θ(1/T)`.
* **The `FamRvMLower` docstring's proposed repair does not exist.** It offered "absorption of
  RvM's `O(|𝔉|log QT)` error into the `0.0397`-nat slack that `famAvgL` leaves against the true
  `(log 2)/2` average". `0.0397 = (2log2 − 1) − (log 2)/2` is the **buffer** comparison — it
  belongs to `buffer_row_sharp`/`SharpZeroDensity`, and the F19 block above states it in that
  role. In `FamRvMLower` there is nothing to absorb into, because `famAvgL` IS the RvM
  average. That sentence made an unreachable row look reachable; it is corrected in place.
* **`FamNIIUpper` is short only by the §12.2 residue**, `Θ(log³Q/(Q·ℒ))` relative —
  astronomically small but not zero, and it cannot be signed away: the exact route needs
  `Σφ*(q)log q ≤ |𝔉|(log Q − 1/2)`, and `avgLogCond(N) − log N + 1/2` **oscillates in sign**
  (measured, φ* by Möbius–totient sieve: `+1.4e−4 / +2.0e−4 / −4.5e−5 / +2.0e−5 / −3.2e−6 /
  +4.3e−6 / −5.5e−7 / −1.8e−6` at `N = 10³, 5·10³, 10⁴, 5·10⁴, 10⁵, 2·10⁵, 3·10⁵, 4·10⁵`).
  So no two-sided envelope can produce the one-sided statement. `famNII_upper_eps_from_tree`
  below is `FamNIIUpper` verbatim except `⟨shift⟩ ↦ ⟨shift⟩ − ε` for every `ε > 0`, with every
  input taken from the artifact's own imports and no free hypotheses. **`FamNIIUpper` itself is
  NOT refuted** — `A₀ = 81.26` carries ≈214× slack over the measured local count, so `NIIFamQ`
  sits far below §9's majorant; it is this ROUTE that is blocked.

**Consequence for the ledger, recorded and NOT patched here.** If §10 wants the RvM row it
must lower `famAvgL` by `≈ 2πA/T`, i.e. add a `Θ(1/T)` row. That is dominated by the buffer
row `L₄ = 6D₀/T` already charged (`D₀ = Θ(ℒ²)` by `design_D0_isBigO`, so `L₄/newrow = Θ(ℒ²)`),
so **no printed figure and no rate class moves** — but it is an accounting change, not
bookkeeping. Both `Prop`s therefore stay `Prop`s, threaded by the
D18 pattern, and everything below is stated as what the tree actually proves.

Every declaration in this section is proved and `[propext, Classical.choice, Quot.sound]`.
Rule 17: no declaration below caps λ, relates `X` to `T`, or pins `D₀`; the regime inputs are
`P.Valid`, `2 ≤ Qn`, `P.Q = (Qn:ℝ)` and `1 ≤ A₀`, and `P.D0` occurs only as the free field. -/

section FamilyBridge

open ZetaQ.Normalisation
open Topology

/-! ## Part 1 — the FAMILY step of §12.2, EFFECTIVE and two-sided. -/

/-- `|𝔉_Q| = Σ_{q ∈ 𝔉's moduli} |F.chars q|` — TRUE in all six branches. This is
`Family.size_eq` cast to `ℝ`, and it is the honest replacement for `sizeR_eq_sum_phiStar`
below. -/
theorem sizeR_eq_sum_weight (F : Family) (Qn : ℕ) :
    Family.sizeR F Qn = ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) := by
  unfold Family.sizeR
  rw [F.size_eq, Nat.cast_sum]

/-! ## Part 1a — §12.3's PARITY COUNTING LAYER (the `S(q)` bookkeeping).

**IMPORT FINDING.** `ZetaQ.Normalisation` IS on this file's import path: `Budget`
imports `ZetaQ.Zones` (module header) and `Zones` imports `ZetaQ.Normalisation`
(see its header). So §12.3's `Cor3.Sq`, `Cor3.evenPrimCount_eq`, `Cor3.oddPrimCount_eq`
and `Cor3.abs_Sq_le_one` — all PROVED in `Normalisation.lean` §§O2–O6 — are usable here
verbatim, and nothing has to be moved, duplicated or re-proved. The note that used to sit at
`sizeR_eq_sum_phiStar` ("the ingredients exist … but are not on this import path") was
MISTAKEN: what this section opens is the namespace `ZetaQ.Normalisation`, whereas the parity
block lives in the sibling namespace `ZetaQ.Cor3`, so those names merely failed to resolve
unqualified.

**ONE DEFINITION ONLY.** `chars_evenQle` / `chars_oddQle` / `chars_evenDyadic` /
`chars_oddDyadic` (`ZetaQ/Zones.lean`) already identify `Family.chars` on the four
parity families with `Cor3.evenPrimitiveChars` / `Cor3.oddPrimitiveChars` by `rfl`, and
`Cor3.primitiveCharsEven_eq` (`Normalisation.lean` §12.3, the ONE canonical bridge) identifies
those with §5's `ZetaQ.primitiveCharsEven` / `primitiveCharsOdd`. The composite is
`ZetaQ.chars_evenQle_eq` and friends (`Zones.lean`). Everything below goes through that single
spelling; no fourth one is introduced. -/

namespace ParityCount

/-- `1 ≤ q` for every modulus of every family. (F32's `q = 1` exclusion is stronger; this is
all the counting layer needs, and it is exactly what `Cor3.abs_Sq_le_one` asks for.) -/
theorem one_le_of_mem {F : Family} {Qn q : ℕ} (hq : q ∈ F.moduli Qn) : 1 ≤ q := by
  cases F <;>
    · simp only [Family.moduli, Finset.mem_Icc, Finset.mem_Ioc] at hq
      omega

theorem le_Qn_of_mem {F : Family} {Qn q : ℕ} (hq : q ∈ F.moduli Qn) : q ≤ Qn := by
  cases F <;>
    · simp only [Family.moduli, Finset.mem_Icc, Finset.mem_Ioc] at hq
      omega

/-- `#(F.moduli Qn) ≤ Qn` — the number of TERMS, which is the entire error budget below. -/
theorem moduli_card_le (F : Family) (Qn : ℕ) : (F.moduli Qn).card ≤ Qn := by
  cases F <;> simp only [Family.moduli, Nat.card_Icc, Nat.card_Ioc] <;> omega

/-! ### The `Family.chars` count of the four parity families IS §12.3's count, by `rfl`. -/

theorem card_chars_evenQle (q : ℕ) :
    (Family.evenQle.chars q).card = Cor3.evenPrimCount q := rfl

theorem card_chars_oddQle (q : ℕ) :
    (Family.oddQle.chars q).card = Cor3.oddPrimCount q := rfl

theorem card_chars_evenDyadic (q : ℕ) :
    (Family.evenDyadic.chars q).card = Cor3.evenPrimCount q := rfl

theorem card_chars_oddDyadic (q : ℕ) :
    (Family.oddDyadic.chars q).card = Cor3.oddPrimCount q := rfl

/-- `|S(q)| ≤ 1` over `ℝ` (`Cor3.abs_Sq_le_one` is stated over `ℤ`). -/
theorem abs_Sq_le_one_real {q : ℕ} (hq : 1 ≤ q) : |(Cor3.Sq q : ℝ)| ≤ 1 := by
  have h : ((|Cor3.Sq q| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast Cor3.abs_Sq_le_one q hq
  rwa [Int.cast_abs] at h

theorem two_evenPrimCount_sub (q : ℕ) :
    2 * ((Cor3.evenPrimCount q : ℕ) : ℝ) - (phiStar q : ℝ) = (Cor3.Sq q : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (Cor3.evenPrimCount_eq q)
  push_cast at h
  linarith

theorem two_oddPrimCount_sub (q : ℕ) :
    2 * ((Cor3.oddPrimCount q : ℕ) : ℝ) - (phiStar q : ℝ) = -(Cor3.Sq q : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (Cor3.oddPrimCount_eq q)
  push_cast at h
  linarith

/-- **§12.3, POINTWISE.** On each of Corollary 3's four parity families the character count at
a modulus is `(φ*(q) ± S(q))/2`, and `|S(q)| ≤ 1`. This is O6/O6′
(`Cor3.evenPrimCount_eq`, `Cor3.oddPrimCount_eq`) together with O2+O3
(`Cor3.abs_Sq_le_one`), read through `Family.chars`. -/
theorem abs_two_weight_sub_phiStar_le {F : Family} (hF : ¬ F.IsFull) {q : ℕ} (hq : 1 ≤ q) :
    |2 * (((F.chars q).card : ℕ) : ℝ) - (phiStar q : ℝ)| ≤ 1 := by
  have hSR := abs_Sq_le_one_real hq
  cases F with
  | qle => exact absurd Family.isFull_qle hF
  | dyadic => exact absurd Family.isFull_dyadic hF
  | evenQle => rw [card_chars_evenQle, two_evenPrimCount_sub]; exact hSR
  | oddQle => rw [card_chars_oddQle, two_oddPrimCount_sub, abs_neg]; exact hSR
  | evenDyadic => rw [card_chars_evenDyadic, two_evenPrimCount_sub]; exact hSR
  | oddDyadic => rw [card_chars_oddDyadic, two_oddPrimCount_sub, abs_neg]; exact hSR
  | evenQleR =>
    rw [show (Family.evenQleR.chars q).card = Cor3.evenPrimCount q from rfl,
      two_evenPrimCount_sub]; exact hSR
  | oddQleR =>
    rw [show (Family.oddQleR.chars q).card = Cor3.oddPrimCount q from rfl,
      two_oddPrimCount_sub, abs_neg]; exact hSR
  | evenDyadicR =>
    rw [show (Family.evenDyadicR.chars q).card = Cor3.evenPrimCount q from rfl,
      two_evenPrimCount_sub]; exact hSR
  | oddDyadicR =>
    rw [show (Family.oddDyadicR.chars q).card = Cor3.oddPrimCount q from rfl,
      two_oddPrimCount_sub, abs_neg]; exact hSR

/-- **§12.3, THE COUNT.** For each of the four parity families

    |2·|𝔉_Q| − Σ_{q ∈ F.moduli Qn} φ*(q)| ≤ #(F.moduli Qn),

i.e. the even/odd subfamily has relative density exactly `1/2` with an error of at most ONE
per modulus. NO partial summation is used: `|S(q)| ≤ 1` termwise is the whole argument (the
`EvenFam.lean` idea), so the error is just the number of terms. -/
theorem abs_two_sizeR_sub_sum_phiStar_le {F : Family} (hF : ¬ F.IsFull) (Qn : ℕ) :
    |2 * Family.sizeR F Qn - ∑ q ∈ F.moduli Qn, (phiStar q : ℝ)|
      ≤ ((F.moduli Qn).card : ℝ) := by
  rw [sizeR_eq_sum_weight, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q ∈ F.moduli Qn, |2 * (((F.chars q).card : ℕ) : ℝ) - (phiStar q : ℝ)|
      ≤ ∑ _q ∈ F.moduli Qn, (1 : ℝ) :=
        Finset.sum_le_sum fun q hq => abs_two_weight_sub_phiStar_le hF (one_le_of_mem hq)
    _ = ((F.moduli Qn).card : ℝ) := by simp

/-- The same with `#(F.moduli Qn) ≤ Qn` already spent — the form every consumer uses:
`|2·|𝔉_Q| − Σ_q φ*(q)| ≤ Qn`. Against the main term `Σ_{q ≤ Q} φ*(q) = (18/π⁴)Q² + O(Q(1+log Q)²)`
(`N2.Astar_bound`) this reads `|𝔉_Q| = (9/π⁴)Q² + O(Q(1+log Q)²)`. -/
theorem abs_two_sizeR_sub_sum_phiStar_le_Qn {F : Family} (hF : ¬ F.IsFull) (Qn : ℕ) :
    |2 * Family.sizeR F Qn - ∑ q ∈ F.moduli Qn, (phiStar q : ℝ)| ≤ (Qn : ℝ) :=
  (abs_two_sizeR_sub_sum_phiStar_le hF Qn).trans (by exact_mod_cast moduli_card_le F Qn)

/-- **§12.3, THE CONDUCTOR AVERAGE.**
`|Σ_q 2|F.chars q|·log q − Σ_q φ*(q)·log q| ≤ Qn·log Qn`.

Again NO partial summation and no `AbelLogPow`: `|S(q)| ≤ 1` termwise gives
`|Σ_{q ≤ x} S(q)·log q| ≤ x·log x` directly, which is `o(x²)` — exactly the route
`ZetaQ/EvenFam.lean` takes for `zeroCountEven_asymp`. -/
theorem abs_two_sum_weight_log_sub_le {F : Family} (hF : ¬ F.IsFull) (Qn : ℕ) :
    |∑ q ∈ F.moduli Qn, 2 * (((F.chars q).card : ℕ) : ℝ) * Real.log q
        - ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * Real.log q|
      ≤ (Qn : ℝ) * Real.log Qn := by
  rcases Nat.eq_zero_or_pos Qn with rfl | hQn0
  · cases F <;> simp [Family.moduli]
  have hQnR : (1 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn0
  have hlogQn : 0 ≤ Real.log Qn := Real.log_nonneg hQnR
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ q ∈ F.moduli Qn,
      |2 * (((F.chars q).card : ℕ) : ℝ) * Real.log q - (phiStar q : ℝ) * Real.log q|
        ≤ Real.log Qn := by
    intro q hq
    have hq1 := one_le_of_mem hq
    have hqQ := le_Qn_of_mem hq
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have hlog0 : 0 ≤ Real.log q := Real.log_nonneg hq1R
    have hlogle : Real.log q ≤ Real.log Qn :=
      Real.log_le_log (by linarith) (by exact_mod_cast hqQ)
    have he : 2 * (((F.chars q).card : ℕ) : ℝ) * Real.log q - (phiStar q : ℝ) * Real.log q
        = (2 * (((F.chars q).card : ℕ) : ℝ) - (phiStar q : ℝ)) * Real.log q := by ring
    rw [he, abs_mul, abs_of_nonneg hlog0]
    have hb := abs_two_weight_sub_phiStar_le hF (F := F) (q := q) hq1
    nlinarith [abs_nonneg (2 * (((F.chars q).card : ℕ) : ℝ) - (phiStar q : ℝ))]
  calc ∑ q ∈ F.moduli Qn,
        |2 * (((F.chars q).card : ℕ) : ℝ) * Real.log q - (phiStar q : ℝ) * Real.log q|
      ≤ ∑ _q ∈ F.moduli Qn, Real.log Qn := Finset.sum_le_sum hterm
    _ = ((F.moduli Qn).card : ℝ) * Real.log Qn := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Qn : ℝ) * Real.log Qn := by
        have hc : ((F.moduli Qn).card : ℝ) ≤ (Qn : ℝ) := by
          exact_mod_cast moduli_card_le F Qn
        nlinarith

end ParityCount

/-- `|𝔉_Q| = Σ_{q ∈ 𝔉's moduli} φ*(q)`, for either FULL family.

**F60 REPAIR — `F.IsFull` is now CARRIED, and this lemma is sorry-free.** The identity is
FALSE for Corollary 3's four parity families (by very nearly a factor of two), so it is no
longer stated for them; the correct parity statement is
`ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn` above,

    |2·|𝔉_Q| − Σ_{q ∈ F.moduli Qn} φ*(q)| ≤ Qn,

proved from §12.3's `Cor3.evenPrimCount_eq` / `Cor3.oddPrimCount_eq` and `|S(q)| ≤ 1`.
`sizeR_eq_sum_weight` (above) is the identity that holds in ALL six branches.

**What the hypothesis changed.** Before F60 this lemma carried four `sorry`s while FOUR
declarations consumed it generically in `F`, so each silently acquired `sorryAx` — unsound at
a parity family, with no `sorry` of its own and no `declaration uses sorry` warning:
`ZetaQ.famMuPart_ge`, `ZetaQ.muPart_ge_NfamQ_sub`, `ZetaQ.FrobAssembly.famEll1_le`,
`ZetaQ.InZone.sizeS_moduli`. All four now carry `F.IsFull` as well, and the parity obligation
each of them leaves is recorded as an EXPLICIT `sorry` in the one genuinely `F`-generic
consumer of each (`trace_row_eventually_aux` here, `FrobAssembly.A1_eventually`,
`InZone.inZone_meanValue_upper`). Nothing is silently weakened and nothing silently reaches
`sorryAx`. -/
theorem sizeR_eq_sum_phiStar {F : Family} (hF : F.IsFull) (Qn : ℕ) :
    Family.sizeR F Qn = ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) := by
  rcases hF with rfl | rfl
  · simp only [Family.sizeR, Family.size, Family.moduli, Nat.cast_sum]
  · simp only [Family.sizeR, Family.size, Family.moduli, famCardDyadic, Nat.cast_sum]

/-! ### F60 record — what the pre-F60 `sizeR_eq_sum_phiStar` said, and why it is gone.

**⚠ SORRY for Corollary 3's four parity families, and the identity is FALSE there** — by
very nearly a factor of two. The correct count is `Σ_q evenPrimCount q` (resp. `oddPrimCount`),
which is `Σ_q (φ*(q) ± S(q))/2` with `S(q) = Σ*_{χ mod q} χ(−1)` the parity defect of §12.3
(`ZetaQ.Cor3.evenPrimCount_eq`, `Sq_eq_sum_chi_neg_one`). So the right statement for
those branches is

    sizeR F Qn = (Σ_{q ∈ F.moduli Qn} φ*(q) ± Σ_{q} S(q)) / 2,

and `Σ_{q ≤ Q} S(q) = O(Q^{3/2})` is what makes it `½·Σφ* (1 + O(Q^{-1/2}))`.

**This lemma is the single most load-bearing debt introduced by the Corollary 3
constructors.** Most of its call sites are at a FIXED family (`Family.qle` / `Family.dyadic`)
and are therefore unaffected. EXACTLY FOUR consume it while generic in `F`, and each of them
silently acquires this `sorryAx` — i.e. is UNSOUND at a parity family, without carrying a
`sorry` of its own:

  * `ZetaQ.famMuPart_ge` (this file),
  * `ZetaQ.muPart_ge_NfamQ_sub` (this file),
  * `ZetaQ.FrobAssembly.famEll1_le`,
  * `ZetaQ.InZone.sizeS_moduli`.

The repair for each is the same: restrict to `Family.IsFull`, or re-state at
`((F.chars q).card : ℝ)` using `sizeR_eq_sum_weight` above and re-derive the §12.2 evaluation
with the `±S(q)/2` correction.
`sizeR_eq_sum_weight` (above) is the true, proved statement; the repair is to route those
call sites through it. Needs: new mathematics (the `S(q)` bookkeeping of §12.3) — the
ingredients exist in `ZetaQ/Normalisation.lean` §O6 but are not on this import path.

**F60.** That last sentence was WRONG — see the IMPORT FINDING at `ParityCount`
above — and the `S(q)` bookkeeping it asked for is now proved there. The `(F : Family)`-generic
declaration this paragraph described no longer exists; it is replaced by the
`{F : Family} (hF : F.IsFull)` version above, which is sorry-free. -/
theorem Icc_one_eq_insert (N : ℕ) (hN : 1 ≤ N) :
    Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- F32 bookkeeping: `|𝔉_Q| = famCard Q − 1` for `Family.qle`, via `phiStar_one`. -/
theorem sizeR_qle_eq_Astar_sub_one (N : ℕ) (hN : 1 ≤ N) :
    Family.sizeR Family.qle N = N2.Astar N - 1 := by
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
  have hA : N2.Astar N
      = (phiStar 1 : ℝ) + ∑ q ∈ Finset.Icc 2 N, (phiStar q : ℝ) := by
    show (∑ q ∈ Finset.Icc 1 N, (phiStar q : ℝ)) = _
    rw [Icc_one_eq_insert N hN, Finset.sum_insert hnot]
  rw [hA, phiStar_one, sizeR_eq_sum_phiStar Family.isFull_qle]
  simp only [Family.moduli]
  push_cast
  ring

theorem sum_qle_log_eq_Alog (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Family.qle.moduli N, (phiStar q : ℝ) * Real.log q = N2.Alog N := by
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
  have hA : N2.Alog N
      = (phiStar 1 : ℝ) * Real.log ((1 : ℕ) : ℝ)
        + ∑ q ∈ Finset.Icc 2 N, (phiStar q : ℝ) * Real.log q := by
    show (∑ q ∈ Finset.Icc 1 N, (phiStar q : ℝ) * Real.log q) = _
    rw [Icc_one_eq_insert N hN, Finset.sum_insert hnot]
  rw [hA]
  simp only [Family.moduli, Nat.cast_one, Real.log_one, mul_zero, zero_add]

/-- **The FAMILY step of §12.2 for `Family.qle`, with an EXPLICIT two-sided error.**
`|Σ_{q ∈ 𝔉_Q} φ*(q)·log q − |𝔉_Q|·(log Q − ⟨shift⟩)| ≤ 19·Q·(1 + log Q)³`,
where `⟨shift⟩ = Family.qle.conductorShift = 1/2`. -/
theorem famLogCond_qle_bound (N : ℕ) (hN : 2 ≤ N) :
    |(∑ q ∈ Family.qle.moduli N, (phiStar q : ℝ) * Real.log q)
        - Family.sizeR Family.qle N * (Real.log N - Family.qle.conductorShift)|
      ≤ 19 * (N : ℝ) * (1 + Real.log N) ^ 3 := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha := N2.Alog_bound N hN1
  have hb := N2.Astar_bound N hN1
  rw [sum_qle_log_eq_Alog N hN1, sizeR_qle_eq_Astar_sub_one N hN1]
  simp only [Family.conductorShift]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLge : (0.6931471803 : ℝ) ≤ Real.log (N : ℝ) :=
    le_trans hlog2.le (Real.log_le_log (by norm_num) hNR)
  set L : ℝ := Real.log (N : ℝ) with hLdef
  set c : ℝ := 18 / Real.pi ^ 4 with hc
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hhalf : (0 : ℝ) ≤ L - 1 / 2 := by linarith
  have hpos3 : (0 : ℝ) < (1 + L) ^ 3 := by positivity
  have hcube : (1 : ℝ) + 3 * L ≤ (1 + L) ^ 3 := by nlinarith [sq_nonneg L, hL0]
  have h3 : L - 1 / 2 ≤ (N : ℝ) * (1 + L) ^ 3 := by nlinarith [hcube, hNR, hpos3, hL0]
  have hbb : |(N2.Astar N - c * (N : ℝ) ^ 2) * (L - 1 / 2)| ≤ 5 * (N : ℝ) * (1 + L) ^ 3 := by
    rw [abs_mul, abs_of_nonneg hhalf]
    have h1 : L - 1 / 2 ≤ 1 + L := by linarith
    have h2 : (0 : ℝ) ≤ 5 * (N : ℝ) * (1 + L) ^ 2 := by positivity
    calc |N2.Astar N - c * (N : ℝ) ^ 2| * (L - 1 / 2)
        ≤ (5 * (N : ℝ) * (1 + L) ^ 2) * (1 + L) := mul_le_mul hb h1 hhalf h2
      _ = 5 * (N : ℝ) * (1 + L) ^ 3 := by ring
  have hsplit : N2.Alog N - (N2.Astar N - 1) * (L - 1 / 2)
      = (N2.Alog N - c * (N : ℝ) ^ 2 * (L - 1 / 2))
        - (N2.Astar N - c * (N : ℝ) ^ 2) * (L - 1 / 2) + (L - 1 / 2) := by ring
  rw [hsplit]
  rw [abs_le] at ha hbb ⊢
  constructor
  · linarith [ha.1, hbb.2, h3]
  · linarith [ha.2, hbb.1, h3]

/-! ## Part 2 — the family RvM lower bound, exact, with its error kept. -/

/-- **The q-uniform RvM count summed over `𝔉_Q`.** No asymptotics: the error term is kept.

**PROVED IN ALL SIX BRANCHES; the `sorry` is closed.** The repair is the one the
previous docstring named. The honest weight is `|F.chars q|`, not `φ*(q)`: a parity family
carries only `Cor3.evenPrimCount q` / `Cor3.oddPrimCount q` characters at each modulus, so
with `φ*(q)` the left-hand side over-counted by nearly a factor of two and the inequality was
FALSE there. Restated at `((F.chars q).card : ℝ)` the proof goes through verbatim (every step
is a per-character inequality summed over the index set), and at a FULL family the two
weights are the same natural number (`Family.card_chars_of_isFull`), so `famRvM_lower_raw`
below recovers the old statement with `F.IsFull` carried. -/
theorem famRvM_lower_weight (P : ParamsQ) (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn)
    {A T₀ : ℝ}
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    (∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
          - A * Real.log ((q : ℝ) * (P.T + 2))))
      ≤ NfamQ P F Qn := by
  have hexp : NfamQ P F Qn
      = ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, NcountQ q χ P.T (2 * P.T) := rfl
  rw [hexp]
  refine Finset.sum_le_sum ?_
  intro q hq
  have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
  haveI : NeZero q := ⟨by omega⟩
  have hstep : ∀ χ ∈ F.chars q,
      P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T - A * Real.log ((q : ℝ) * (P.T + 2))
        ≤ NcountQ q χ P.T (2 * P.T) := by
    intro χ hχ
    have hp : χ.IsPrimitive :=
      EFChi.isPrimitive_of_mem_primitiveChars (F.chars_subset q hχ)
    have hab := abs_le.mp (hrvm q χ hq1 hp P.T hT)
    have hNc : NcountQ q χ P.T (2 * P.T)
        = ((Zeta23.ThmE.NcountL χ P.T (2 * P.T) : ℕ) : ℝ) := by
      unfold NcountQ; rw [dif_neg (show ¬ q = 0 by omega)]
    rw [hNc]
    linarith [hab.1]
  calc (((F.chars q).card : ℕ) : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
          - A * Real.log ((q : ℝ) * (P.T + 2)))
      = ∑ _χ ∈ F.chars q,
          (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            - A * Real.log ((q : ℝ) * (P.T + 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ χ ∈ F.chars q, NcountQ q χ P.T (2 * P.T) := Finset.sum_le_sum hstep

/-- **The q-uniform RvM count summed over `𝔉_Q`, priced at the FULL weight `φ*(q)`.**

F60: this is `famRvM_lower_weight` with `F.IsFull` carried — exactly the hypothesis under
which `|F.chars q| = φ*(q)`. For the four parity families the `φ*(q)`-weighted statement is
FALSE (off by nearly a factor of two) and is deliberately NOT stated; use
`famRvM_lower_weight` there. -/
theorem famRvM_lower_raw (P : ParamsQ) {F : Family} (hF : F.IsFull) (Qn : ℕ) (hQn : 2 ≤ Qn)
    {A T₀ : ℝ}
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    (∑ q ∈ F.moduli Qn, (phiStar q : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
          - A * Real.log ((q : ℝ) * (P.T + 2))))
      ≤ NfamQ P F Qn := by
  refine le_trans (le_of_eq ?_) (famRvM_lower_weight P F Qn hQn hrvm hT)
  exact Finset.sum_congr rfl fun q _ => by rw [Family.card_chars_of_isFull hF]

/-! ## Part 3 — §9's family buffer bound, at the CONDUCTOR-AVERAGED step. -/

/-- **`EFChi.NII_fam_le` re-proved one step earlier**: `log q` is kept, not majorised by `ℒ`.

**PROVED IN ALL SIX BRANCHES; the `sorry` is closed.** The right-hand side prices each
modulus at the FULL `φ*(q)`, and in THIS direction that makes the stated bound TRUE for a
parity family as well; the only missing step was the monotonicity
`Σ_{χ ∈ F.chars q} … ≤ Σ_{χ ∈ primitiveChars q} …`, from the summand's nonnegativity
(`NcountQ_nonneg`) and `Family.chars_subset`. That step is `hmono` below. -/
theorem NIIFam_avg_le (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn)
    {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    NIIFamQ P F Qn
      ≤ 3 * A₀ * P.D0
          * ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T)) := by
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hexp : NIIFamQ P F Qn
      = ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
          (NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0)) := rfl
  rw [hexp, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro q hq
  have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
  haveI : NeZero q := ⟨by omega⟩
  -- the `Family.chars_subset` monotonicity step; see the docstring.
  have hmono : ∑ χ ∈ F.chars q,
        (NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0))
      ≤ ∑ χ ∈ primitiveChars q,
        (NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (F.chars_subset q)
      (fun χ _ _ => add_nonneg (NcountQ_nonneg q χ _ _) (NcountQ_nonneg q χ _ _))
  refine hmono.trans ?_
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hstep : ∀ χ ∈ primitiveChars q,
      NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0)
        ≤ 3 * A₀ * P.D0 * (Real.log q + Real.log (4 * P.T)) := by
    intro χ hχ
    have hp : χ.IsPrimitive := EFChi.isPrimitive_of_mem_primitiveChars hχ
    have hlocZ : ∀ t : ℝ,
        (((ZChi hq1 hp).N t (t + 1) : ℕ) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)) := by
      intro t
      rw [EFChi.ZChi_N hq1 hp t (t + 1)]
      have hNc : NcountQ q χ t (t + 1) = ((Zeta23.ThmE.NcountL χ t (t + 1) : ℕ) : ℝ) := by
        unfold NcountQ; rw [dif_neg (show ¬ q = 0 by omega)]
      rw [hNc]
      exact hloc q χ hq1 hp t
    have hmain := EFChi.NIID_chi_le_Q P hP (ZChi hq1 hp) hq1 hA₀ hlocZ
    rw [NIIfree_eq, EFChi.ZChi_N hq1 hp (P.T - P.D0) P.T,
      EFChi.ZChi_N hq1 hp (2 * P.T) (2 * P.T + P.D0)] at hmain
    have h4T : (0 : ℝ) < 4 * P.T := by linarith
    rw [Real.log_mul (ne_of_gt hqR) (ne_of_gt h4T)] at hmain
    exact hmain
  calc ∑ χ ∈ primitiveChars q,
        (NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0))
      ≤ ∑ _χ ∈ primitiveChars q, 3 * A₀ * P.D0 * (Real.log q + Real.log (4 * P.T)) :=
        Finset.sum_le_sum hstep
    _ = 3 * A₀ * P.D0 * ((phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T))) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          show ((primitiveChars q).card : ℕ) = phiStar q from rfl]
        ring

/-! ## Part 4 — `FamNIIUpper` with the residue kept explicit. -/

private theorem log_LL_add_log8pi (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hQ : P.Q = (Qn : ℝ)) :
    P.LL + Real.log (8 * Real.pi) = Real.log (Qn : ℝ) + Real.log (4 * P.T) := by
  have hQnR : (2 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : (0 : ℝ) < (Qn : ℝ) * P.T / (2 * Real.pi) :=
    div_pos (mul_pos hQ0 hT0) (by linarith)
  have h2 : (0 : ℝ) < 8 * Real.pi := by linarith
  have h3 : (0 : ℝ) < 4 * P.T := by linarith
  unfold ParamsQ.LL
  rw [hQ, ← Real.log_mul (ne_of_gt h1) (ne_of_gt h2),
    ← Real.log_mul (ne_of_gt hQ0) (ne_of_gt h3)]
  congr 1
  field_simp
  ring

/-- **`FamNIIUpper` for `Family.qle`, with the §12.2 residue kept explicit.**
This is `FamNIIUpper F Qn P A₀` verbatim except for the extra
`+ 19·Q·(1 + log Q)³` inside the bracket. -/
theorem famNII_upper_with_residue (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hQ : P.Q = (Qn : ℝ)) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    NIIFamQ P Family.qle Qn
      ≤ 3 * A₀ * P.D0
          * ((P.LL - Family.qle.conductorShift + Real.log (8 * Real.pi))
                * Family.sizeR Family.qle Qn
              + 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3) := by
  have hbase := NIIFam_avg_le P hP Family.qle Qn hQn hA₀ hloc
  have hD := hP.two_le_D0
  have hA0D : (0 : ℝ) ≤ 3 * A₀ * P.D0 := by nlinarith
  have hsplit : ∑ q ∈ Family.qle.moduli Qn,
        (phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T))
      = (∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Real.log q)
        + Family.sizeR Family.qle Qn * Real.log (4 * P.T) := by
    rw [sizeR_eq_sum_phiStar Family.isFull_qle, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have hbound : (∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Real.log q)
      ≤ Family.sizeR Family.qle Qn * (Real.log Qn - Family.qle.conductorShift)
        + 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 :=
    by linarith [(abs_le.mp (famLogCond_qle_bound Qn hQn)).2]
  have hrw : P.LL - Family.qle.conductorShift + Real.log (8 * Real.pi)
      = (Real.log (Qn : ℝ) - Family.qle.conductorShift) + Real.log (4 * P.T) := by
    have := log_LL_add_log8pi P hP Qn hQn hQ
    linarith
  refine hbase.trans ?_
  rw [hsplit, hrw]
  refine mul_le_mul_of_nonneg_left ?_ hA0D
  have hgoal : ((Real.log (Qn : ℝ) - Family.qle.conductorShift) + Real.log (4 * P.T))
        * Family.sizeR Family.qle Qn + 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
      = (Family.sizeR Family.qle Qn * (Real.log Qn - Family.qle.conductorShift)
          + 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
        + Family.sizeR Family.qle Qn * Real.log (4 * P.T) := by ring
  rw [hgoal]
  linarith

/-- **`FamNIIUpper` for `Family.qle` under an explicit smallness side-condition** — the
`Prop` itself with `⟨shift⟩` relaxed to `⟨shift⟩ − ε`. -/
theorem famNII_upper_of_residue_small (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hQ : P.Q = (Qn : ℝ)) {A₀ ε : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hres : 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 ≤ ε * Family.sizeR Family.qle Qn) :
    NIIFamQ P Family.qle Qn
      ≤ 3 * A₀ * P.D0
          * (P.LL - (Family.qle.conductorShift - ε) + Real.log (8 * Real.pi))
          * Family.sizeR Family.qle Qn := by
  have hD := hP.two_le_D0
  have hA0D : (0 : ℝ) ≤ 3 * A₀ * P.D0 := by nlinarith
  have hkey : (P.LL - Family.qle.conductorShift + Real.log (8 * Real.pi))
        * Family.sizeR Family.qle Qn + 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
      ≤ (P.LL - (Family.qle.conductorShift - ε) + Real.log (8 * Real.pi))
        * Family.sizeR Family.qle Qn := by
    have hexp : (P.LL - (Family.qle.conductorShift - ε) + Real.log (8 * Real.pi))
          * Family.sizeR Family.qle Qn
        = (P.LL - Family.qle.conductorShift + Real.log (8 * Real.pi))
            * Family.sizeR Family.qle Qn + ε * Family.sizeR Family.qle Qn := by ring
    rw [hexp]
    linarith
  refine (famNII_upper_with_residue P hP Qn hQn hQ hA₀ hloc).trans ?_
  calc 3 * A₀ * P.D0 * ((P.LL - Family.qle.conductorShift + Real.log (8 * Real.pi))
          * Family.sizeR Family.qle Qn + 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
      ≤ 3 * A₀ * P.D0 * ((P.LL - (Family.qle.conductorShift - ε) + Real.log (8 * Real.pi))
          * Family.sizeR Family.qle Qn) := mul_le_mul_of_nonneg_left hkey hA0D
    _ = 3 * A₀ * P.D0 * (P.LL - (Family.qle.conductorShift - ε) + Real.log (8 * Real.pi))
          * Family.sizeR Family.qle Qn := by ring

/-! ### F60 — §12.3's count against `Family.qle`'s closed form `Astar Qn − 1`.

`ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn` gives `|2·|𝔉_Q| − Σ_q φ*(q)| ≤ Qn` for the
four parity families. The `evenQle`/`oddQle` modulus range IS `Family.qle`'s (`Family.moduli`
returns `Finset.Icc 2 Qn` for all three, by `rfl`), so `Σ_q φ*(q)` over it is
`Family.qle.sizeR Qn = N2.Astar Qn − 1`. -/

theorem not_isFull_evenQle : ¬ Family.evenQle.IsFull := by
  rintro (h | h) <;> exact Family.noConfusion h

theorem not_isFull_oddQle : ¬ Family.oddQle.IsFull := by
  rintro (h | h) <;> exact Family.noConfusion h

theorem not_isFull_evenDyadic : ¬ Family.evenDyadic.IsFull := by
  rintro (h | h) <;> exact Family.noConfusion h

theorem not_isFull_oddDyadic : ¬ Family.oddDyadic.IsFull := by
  rintro (h | h) <;> exact Family.noConfusion h

theorem not_isFull_evenQleR : ¬ Family.evenQleR.IsFull := by
  rintro (h | h) <;> exact Family.noConfusion h

theorem not_isFull_oddQleR : ¬ Family.oddQleR.IsFull := by
  rintro (h | h) <;> exact Family.noConfusion h

theorem not_isFull_evenDyadicR : ¬ Family.evenDyadicR.IsFull := by
  rintro (h | h) <;> exact Family.noConfusion h

theorem not_isFull_oddDyadicR : ¬ Family.oddDyadicR.IsFull := by
  rintro (h | h) <;> exact Family.noConfusion h

/-- `|2·|𝔉_Q| − (Astar Qn − 1)| ≤ Qn` for the two `Icc 2 Qn` parity families. -/
theorem two_sizeR_parity_qle {F : Family} (hF : ¬ F.IsFull) (Qn : ℕ) (hQn : 1 ≤ Qn)
    (hmod : F.moduli Qn = Family.qle.moduli Qn) :
    |2 * F.sizeR Qn - (N2.Astar Qn - 1)| ≤ (Qn : ℝ) := by
  have hsum : ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) = N2.Astar Qn - 1 := by
    rw [hmod, ← sizeR_eq_sum_phiStar Family.isFull_qle Qn]
    exact sizeR_qle_eq_Astar_sub_one Qn hQn
  have h := ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn hF Qn
  rwa [hsum] at h

/-! ## Part 5 — `FamRvMLower` with the two residues kept explicit. -/

/-- **`FamRvMLower` for `Family.qle`, with BOTH residues kept explicit** — the §12.2 conductor
residue `(T/2π)·19Q(1+log Q)³` and the q-uniform RvM error `A·|𝔉|·log(Q(T+2))`. -/
theorem famRvM_lower_with_residue (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hQ : P.Q = (Qn : ℝ)) {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    Family.sizeR Family.qle Qn * (P.T / (2 * Real.pi) * famAvgL Family.qle P)
        - P.T / (2 * Real.pi) * (19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
        - A * (Family.sizeR Family.qle Qn * Real.log ((Qn : ℝ) * (P.T + 2)))
      ≤ NfamQ P Family.qle Qn := by
  have hbase := famRvM_lower_raw P Family.isFull_qle Qn hQn hrvm hT
  have hQnR : (2 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hM : (0 : ℝ) ≤ P.T / (2 * Real.pi) := by positivity
  have hdiv : (0 : ℝ) < P.T / (2 * Real.pi) := div_pos hT0 (by linarith)
  set G : ℝ := Real.log (P.T / (2 * Real.pi)) + 2 * Real.log 2 - 1 with hG
  have hLLsplit : P.LL = Real.log (Qn : ℝ) + Real.log (P.T / (2 * Real.pi)) := by
    unfold ParamsQ.LL
    rw [hQ, show (Qn : ℝ) * P.T / (2 * Real.pi) = (Qn : ℝ) * (P.T / (2 * Real.pi)) by ring]
    exact Real.log_mul (ne_of_gt hQ0) (ne_of_gt hdiv)
  have hell : ∀ q ∈ Family.qle.moduli Qn,
      Zeta23.ThmE.ell1q q P.T = Real.log (q : ℝ) + G := by
    intro q hq
    have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli_qle hq
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    unfold Zeta23.ThmE.ell1q
    rw [show (q : ℝ) * P.T / (2 * Real.pi) = (q : ℝ) * (P.T / (2 * Real.pi)) by ring,
      Real.log_mul (ne_of_gt hqR) (ne_of_gt hdiv), hG]
    ring
  have hsum1 : ∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T
      = (∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Real.log q)
        + Family.sizeR Family.qle Qn * G := by
    rw [sizeR_eq_sum_phiStar Family.isFull_qle, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [hell q hq]; ring
  have hsum2 : ∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Real.log ((q : ℝ) * (P.T + 2))
      ≤ Family.sizeR Family.qle Qn * Real.log ((Qn : ℝ) * (P.T + 2)) := by
    rw [sizeR_eq_sum_phiStar Family.isFull_qle, Finset.sum_mul]
    refine Finset.sum_le_sum (fun q hq => ?_)
    have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli_qle hq
    have hqle : (q : ℝ) ≤ (Qn : ℝ) := by
      have h : q ∈ Finset.Icc 2 Qn := hq
      rw [Finset.mem_Icc] at h
      exact_mod_cast h.2
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    have hmono : Real.log ((q : ℝ) * (P.T + 2)) ≤ Real.log ((Qn : ℝ) * (P.T + 2)) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hsplitL : ∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
          - A * Real.log ((q : ℝ) * (P.T + 2)))
      = P.T / (2 * Real.pi)
          * (∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T)
        - A * (∑ q ∈ Family.qle.moduli Qn,
            (phiStar q : ℝ) * Real.log ((q : ℝ) * (P.T + 2))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have hS : Family.sizeR Family.qle Qn * (Real.log (Qn : ℝ) - 1 / 2)
        - 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
      ≤ ∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Real.log q := by
    have h := (abs_le.mp (famLogCond_qle_bound Qn hQn)).1
    simp only [Family.conductorShift] at h
    linarith
  have hfa : famAvgL Family.qle P = (Real.log (Qn : ℝ) - 1 / 2) + G := by
    unfold famAvgL
    simp only [Family.conductorShift]
    rw [hLLsplit, hG]
    ring
  have step1 : P.T / (2 * Real.pi)
        * ((Family.sizeR Family.qle Qn * (Real.log (Qn : ℝ) - 1 / 2)
              - 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
            + Family.sizeR Family.qle Qn * G)
      ≤ P.T / (2 * Real.pi)
        * (∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T) := by
    rw [hsum1]
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  have step2 : A * (∑ q ∈ Family.qle.moduli Qn,
        (phiStar q : ℝ) * Real.log ((q : ℝ) * (P.T + 2)))
      ≤ A * (Family.sizeR Family.qle Qn * Real.log ((Qn : ℝ) * (P.T + 2))) :=
    mul_le_mul_of_nonneg_left hsum2 hA
  have heq : Family.sizeR Family.qle Qn * (P.T / (2 * Real.pi) * famAvgL Family.qle P)
        - P.T / (2 * Real.pi) * (19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
      = P.T / (2 * Real.pi)
        * ((Family.sizeR Family.qle Qn * (Real.log (Qn : ℝ) - 1 / 2)
              - 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
            + Family.sizeR Family.qle Qn * G) := by
    rw [hfa]; ring
  refine le_trans ?_ hbase
  rw [hsplitL, heq]
  linarith

/-- **`FamRvMLower`'s content for the two `Icc 2 Qn` PARITY families, both residues explicit**
.

Identical to `famRvM_lower_with_residue` except that the per-modulus weight is `|F.chars q|`
(via `famRvM_lower_weight` and `sizeR_eq_sum_weight`) and the §12.2 conductor bound
`famLogCond_qle_bound` is transported across §12.3's count:

  * `ParityCount.abs_two_sum_weight_log_sub_le` : `|Σ_q 2|F.chars q|·log q − Σ_q φ*(q)·log q| ≤ Qn·log Qn`,
  * `two_sizeR_parity_qle` : `|2·|𝔉_Q| − (Astar Qn − 1)| ≤ Qn`,

which together turn `Σ_q φ*(q) log q ≥ |𝔉^full_Q|(log Qn − ½) − 19Q(1+log Q)³` into
`Σ_q |F.chars q| log q ≥ |𝔉_Q|(log Qn − ½) − 21Q(1+log Q)³`. The residue grows from `19` to
`21`; nothing else changes, and in particular `famAvgL F P = famAvgL Family.qle P` because
`Family.conductorShift` is `1/2` on `evenQle`/`oddQle` too. No partial summation. -/
theorem famRvM_lower_with_residue_parity (P : ParamsQ) (hP : P.Valid) {F : Family}
    (hF : ¬ F.IsFull) (hsh : F.conductorShift = 1 / 2) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hmod : F.moduli Qn = Family.qle.moduli Qn)
    (hQ : P.Q = (Qn : ℝ)) {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgL F P)
        - P.T / (2 * Real.pi) * (21 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
        - A * (F.sizeR Qn * Real.log ((Qn : ℝ) * (P.T + 2)))
      ≤ NfamQ P F Qn := by
  have hbase := famRvM_lower_weight P F Qn hQn hrvm hT
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hM : (0 : ℝ) ≤ P.T / (2 * Real.pi) := by positivity
  have hdiv : (0 : ℝ) < P.T / (2 * Real.pi) := div_pos hT0 (by linarith)
  set G : ℝ := Real.log (P.T / (2 * Real.pi)) + 2 * Real.log 2 - 1 with hG
  have hLLsplit : P.LL = Real.log (Qn : ℝ) + Real.log (P.T / (2 * Real.pi)) := by
    unfold ParamsQ.LL
    rw [hQ, show (Qn : ℝ) * P.T / (2 * Real.pi) = (Qn : ℝ) * (P.T / (2 * Real.pi)) by ring]
    exact Real.log_mul (ne_of_gt hQ0) (ne_of_gt hdiv)
  have hell : ∀ q ∈ F.moduli Qn, Zeta23.ThmE.ell1q q P.T = Real.log (q : ℝ) + G := by
    intro q hq
    rw [hmod] at hq
    have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli_qle hq
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    unfold Zeta23.ThmE.ell1q
    rw [show (q : ℝ) * P.T / (2 * Real.pi) = (q : ℝ) * (P.T / (2 * Real.pi)) by ring,
      Real.log_mul (ne_of_gt hqR) (ne_of_gt hdiv), hG]
    ring
  have hsum1 : ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Zeta23.ThmE.ell1q q P.T
      = (∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Real.log q) + F.sizeR Qn * G := by
    rw [sizeR_eq_sum_weight, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [hell q hq]; ring
  have hsum2 : ∑ q ∈ F.moduli Qn,
        (((F.chars q).card : ℕ) : ℝ) * Real.log ((q : ℝ) * (P.T + 2))
      ≤ F.sizeR Qn * Real.log ((Qn : ℝ) * (P.T + 2)) := by
    rw [sizeR_eq_sum_weight, Finset.sum_mul]
    refine Finset.sum_le_sum (fun q hq => ?_)
    rw [hmod] at hq
    have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli_qle hq
    have hqle : (q : ℝ) ≤ (Qn : ℝ) := by
      have h : q ∈ Finset.Icc 2 Qn := hq
      rw [Finset.mem_Icc] at h
      exact_mod_cast h.2
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    have hmono : Real.log ((q : ℝ) * (P.T + 2)) ≤ Real.log ((Qn : ℝ) * (P.T + 2)) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hsplitL : ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
          - A * Real.log ((q : ℝ) * (P.T + 2)))
      = P.T / (2 * Real.pi)
          * (∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Zeta23.ThmE.ell1q q P.T)
        - A * (∑ q ∈ F.moduli Qn,
            (((F.chars q).card : ℕ) : ℝ) * Real.log ((q : ℝ) * (P.T + 2))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  -- §12.3's conductor average, against §12.2's `famLogCond_qle_bound`
  have hlogQ0 : (0 : ℝ) ≤ Real.log (Qn : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL2 : Real.log 2 ≤ Real.log (Qn : ℝ) := Real.log_le_log (by norm_num) hQnR
  have hL12 : (0 : ℝ) ≤ Real.log (Qn : ℝ) - 1 / 2 := by linarith
  have hcube : Real.log (Qn : ℝ) ≤ (1 + Real.log (Qn : ℝ)) ^ 3 := by
    nlinarith [hlogQ0, mul_nonneg hlogQ0 hlogQ0,
      mul_nonneg (mul_nonneg hlogQ0 hlogQ0) hlogQ0]
  have hNL : (Qn : ℝ) * Real.log (Qn : ℝ) ≤ (Qn : ℝ) * (1 + Real.log (Qn : ℝ)) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  have h2s : ∑ q ∈ F.moduli Qn, 2 * (((F.chars q).card : ℕ) : ℝ) * Real.log q
      = 2 * ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Real.log q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hpc := abs_le.mp (ParityCount.abs_two_sum_weight_log_sub_le hF Qn)
  rw [h2s] at hpc
  have hfl := (abs_le.mp (famLogCond_qle_bound Qn hQn)).1
  simp only [Family.conductorShift] at hfl
  rw [← hmod] at hfl
  have hpar := (abs_le.mp (two_sizeR_parity_qle hF Qn hQn1 hmod)).2
  have hqeq := sizeR_qle_eq_Astar_sub_one Qn hQn1
  have hsQ : 2 * F.sizeR Qn - (Qn : ℝ) ≤ Family.sizeR Family.qle Qn := by
    rw [hqeq]; linarith
  have hmul := mul_le_mul_of_nonneg_right hsQ hL12
  have hS : F.sizeR Qn * (Real.log (Qn : ℝ) - 1 / 2)
        - 21 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
      ≤ ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Real.log q := by
    nlinarith [hpc.1, hfl, hmul, hNL, hlogQ0, hQ0]
  have hfa : famAvgL F P = (Real.log (Qn : ℝ) - 1 / 2) + G := by
    unfold famAvgL
    rw [hsh, hLLsplit, hG]
    ring
  have step1 : P.T / (2 * Real.pi)
        * ((F.sizeR Qn * (Real.log (Qn : ℝ) - 1 / 2)
              - 21 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
            + F.sizeR Qn * G)
      ≤ P.T / (2 * Real.pi)
        * (∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Zeta23.ThmE.ell1q q P.T) := by
    rw [hsum1]
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  have step2 : A * (∑ q ∈ F.moduli Qn,
        (((F.chars q).card : ℕ) : ℝ) * Real.log ((q : ℝ) * (P.T + 2)))
      ≤ A * (F.sizeR Qn * Real.log ((Qn : ℝ) * (P.T + 2))) :=
    mul_le_mul_of_nonneg_left hsum2 hA
  have heq : F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgL F P)
        - P.T / (2 * Real.pi) * (21 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
      = P.T / (2 * Real.pi)
        * ((F.sizeR Qn * (Real.log (Qn : ℝ) - 1 / 2)
              - 21 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
            + F.sizeR Qn * G) := by
    rw [hfa]; ring
  refine le_trans ?_ hbase
  rw [hsplitL, heq]
  linarith

/-- The family size from below, effective — the companion that makes the residues of
Parts 4 and 5 quantitatively negligible (`|𝔉_Q| ≍ (18/π⁴)Q²` against `O(Q log³Q)`). -/
theorem sizeR_qle_lower (N : ℕ) (hN : 1 ≤ N) :
    (18 / Real.pi ^ 4) * (N : ℝ) ^ 2 - 5 * (N : ℝ) * (1 + Real.log N) ^ 2 - 1
      ≤ Family.sizeR Family.qle N := by
  have hb := abs_le.mp (N2.Astar_bound N hN)
  rw [sizeR_qle_eq_Astar_sub_one N hN]
  linarith [hb.1]

theorem sizeR_qle_lower' (N : ℕ) (hN : 1 ≤ N) :
    (18 / Real.pi ^ 4) * (N : ℝ) ^ 2 - 6 * (N : ℝ) * (1 + Real.log N) ^ 2
      ≤ Family.sizeR Family.qle N := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have h1 : (1 : ℝ) ≤ (N : ℝ) * (1 + Real.log N) ^ 2 := by nlinarith
  have h2 := sizeR_qle_lower N hN
  linarith

/-! ## Part 6 — the residue IS eventually negligible: the ε-form is reachable. -/

private theorem logpow_div_tendsto (n : ℕ) :
    Tendsto (fun x : ℝ => Real.log x ^ n / x) atTop (nhds 0) := by
  simpa using (Real.isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero

private theorem one_add_log_sq_div_tendsto :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ 2 / x) atTop (nhds 0) := by
  have hcomb : Tendsto (fun x : ℝ =>
      Real.log x ^ 0 / x + 2 * (Real.log x ^ 1 / x) + Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa using ((logpow_div_tendsto 0).add ((logpow_div_tendsto 1).const_mul 2)).add
      (logpow_div_tendsto 2)
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [pow_zero, pow_one]
  field_simp
  ring

private theorem one_add_log_cube_div_tendsto :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ 3 / x) atTop (nhds 0) := by
  have hcomb : Tendsto (fun x : ℝ =>
      Real.log x ^ 0 / x + 3 * (Real.log x ^ 1 / x) + 3 * (Real.log x ^ 2 / x)
        + Real.log x ^ 3 / x) atTop (nhds 0) := by
    simpa using (((logpow_div_tendsto 0).add ((logpow_div_tendsto 1).const_mul 3)).add
      ((logpow_div_tendsto 2).const_mul 3)).add (logpow_div_tendsto 3)
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [pow_zero, pow_one]
  field_simp
  ring

/-- **The §12.2 residue is eventually below any fixed multiple of `|𝔉_Q|`.**
This is what makes the ε-relaxed forms of Parts 4/5 nonvacuous. -/
theorem residue_small_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      19 * (N : ℝ) * (1 + Real.log N) ^ 3 ≤ ε * Family.sizeR Family.qle N := by
  have hc : (0 : ℝ) < ε * (18 / Real.pi ^ 4) := by
    have : (0 : ℝ) < 18 / Real.pi ^ 4 := by positivity
    positivity
  have hH : Tendsto (fun x : ℝ =>
      19 * ((1 + Real.log x) ^ 3 / x) + 6 * ε * ((1 + Real.log x) ^ 2 / x))
      atTop (nhds 0) := by
    simpa using (one_add_log_cube_div_tendsto.const_mul 19).add
      (one_add_log_sq_div_tendsto.const_mul (6 * ε))
  have hev : ∀ᶠ x : ℝ in atTop,
      19 * ((1 + Real.log x) ^ 3 / x) + 6 * ε * ((1 + Real.log x) ^ 2 / x)
        < ε * (18 / Real.pi ^ 4) := hH.eventually_lt_const hc
  have hevN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  filter_upwards [hevN, eventually_ge_atTop 1] with N hN1 hN2
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hN1.le (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
  have hexpand : (19 * ((1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ))
        + 6 * ε * ((1 + Real.log (N : ℝ)) ^ 2 / (N : ℝ))) * (N : ℝ) ^ 2
      = 19 * (N : ℝ) * (1 + Real.log N) ^ 3
        + 6 * ε * (N : ℝ) * (1 + Real.log N) ^ 2 := by
    field_simp
  rw [hexpand] at hmul
  have hsz2 := mul_le_mul_of_nonneg_left (sizeR_qle_lower' N hN2) hε.le
  linarith

/-- **The §12.2+§12.3 residue is eventually below any fixed multiple of `|𝔉_Q|`, for the two
`Icc 2 Qn` PARITY families**. Same shape as `residue_small_eventually`, at the larger
constant `21` and against `|𝔉_Q| ≥ ½(|𝔉^full_Q| − Q)`. -/
theorem residue_small_parity_eventually {F : Family} (hF : ¬ F.IsFull)
    (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.qle.moduli Qn) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      21 * (N : ℝ) * (1 + Real.log N) ^ 3 ≤ ε * Family.sizeR F N := by
  have hc : (0 : ℝ) < ε * (18 / Real.pi ^ 4) := by
    have : (0 : ℝ) < 18 / Real.pi ^ 4 := by positivity
    positivity
  have hH : Tendsto (fun x : ℝ =>
      42 * ((1 + Real.log x) ^ 3 / x) + 7 * ε * ((1 + Real.log x) ^ 2 / x))
      atTop (nhds 0) := by
    simpa using (one_add_log_cube_div_tendsto.const_mul 42).add
      (one_add_log_sq_div_tendsto.const_mul (7 * ε))
  have hev : ∀ᶠ x : ℝ in atTop,
      42 * ((1 + Real.log x) ^ 3 / x) + 7 * ε * ((1 + Real.log x) ^ 2 / x)
        < ε * (18 / Real.pi ^ 4) := hH.eventually_lt_const hc
  have hevN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  filter_upwards [hevN, eventually_ge_atTop 1] with N hN1 hN2
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hsq1 : (1 : ℝ) ≤ (1 + Real.log (N : ℝ)) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hN1.le (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
  have hexpand : (42 * ((1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ))
        + 7 * ε * ((1 + Real.log (N : ℝ)) ^ 2 / (N : ℝ))) * (N : ℝ) ^ 2
      = 42 * (N : ℝ) * (1 + Real.log N) ^ 3
        + 7 * ε * (N : ℝ) * (1 + Real.log N) ^ 2 := by
    field_simp
  rw [hexpand] at hmul
  have hsz2 := mul_le_mul_of_nonneg_left (sizeR_qle_lower' N hN2) hε.le
  have hpar := (abs_le.mp (two_sizeR_parity_qle hF N hN2 (hmod N))).1
  have hqeq := sizeR_qle_eq_Astar_sub_one N hN2
  have hsQ : Family.sizeR Family.qle N - (N : ℝ) ≤ 2 * Family.sizeR F N := by
    rw [hqeq]; linarith
  have hsQ' := mul_le_mul_of_nonneg_left hsQ hε.le
  have hstepN : (N : ℝ) * 1 ≤ (N : ℝ) * (1 + Real.log N) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq1 (by positivity : (0 : ℝ) ≤ (N : ℝ))
  rw [mul_one] at hstepN
  have hNsq : ε * (N : ℝ) ≤ ε * ((N : ℝ) * (1 + Real.log N) ^ 2) :=
    mul_le_mul_of_nonneg_left hstepN hε.le
  linarith [hmul, hsz2, hsQ', hNsq]

/-! ## Part 7 — the capstones, with EVERY input taken from the tree (no free hypotheses). -/

/-- **`FamNIIUpper` for `Family.qle`, ε-relaxed, from the artifact's own imports.**
`hloc` is `EFChi.localCountChi_uniform` (H6); the residue is `residue_small_eventually`. -/
theorem famNII_upper_eps_from_tree :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, P.Valid → P.Q = (Qn : ℝ) →
        NIIFamQ P Family.qle Qn
          ≤ 3 * A₀ * P.D0
              * (P.LL - (Family.qle.conductorShift - ε) + Real.log (8 * Real.pi))
              * Family.sizeR Family.qle Qn := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  refine ⟨A₀, hA₀, fun ε hε => ?_⟩
  filter_upwards [residue_small_eventually hε, eventually_ge_atTop 2] with Qn hres hQn
  intro P hP hQ
  exact famNII_upper_of_residue_small P hP Qn hQn hQ hA₀ hloc hres

/-- **`FamRvMLower` for `Family.qle` with both residues, from the artifact's own imports.**
`hrvm` is `EFChi.rvmChi_main_uniform`. -/
theorem famRvM_lower_from_tree :
    ∃ A T₀ : ℝ, 0 < A ∧
      ∀ (P : ParamsQ), P.Valid → T₀ ≤ P.T → ∀ Qn : ℕ, 2 ≤ Qn → P.Q = (Qn : ℝ) →
        Family.sizeR Family.qle Qn * (P.T / (2 * Real.pi) * famAvgL Family.qle P)
            - P.T / (2 * Real.pi) * (19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
            - A * (Family.sizeR Family.qle Qn * Real.log ((Qn : ℝ) * (P.T + 2)))
          ≤ NfamQ P Family.qle Qn := by
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  exact ⟨A, T₀, hA, fun P hP hT Qn hQn hQ =>
    famRvM_lower_with_residue P hP Qn hQn hQ hA.le hrvm hT⟩

/-- `log n → ∞` along `ℕ`. -/
theorem tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- **The RvM error is eventually below `T/(400π)`.**  With `T = (log Q)^{r+ε}` and `r ≥ 3`,
`A·log(Q(T+2))` is `O(log Q)` while `T ≥ (log Q)³`.  Note `log T = (r+ε)·log log Q`, which is
smaller still; the proof uses only `log log Q ≤ log Q`. -/
theorem rvm_error_small (r ε A : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop,
      400 * Real.pi * A * Real.log ((n : ℝ) * (Twin (n : ℝ) r ε + 2))
        ≤ Twin (n : ℝ) r ε := by
  have hre3 : (3 : ℝ) ≤ r + ε := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnn : (0 : ℝ) ≤ 400 * Real.pi * A * (2 + r + ε) := by positivity
  filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop
      (Real.sqrt (400 * Real.pi * A * (2 + r + ε)) + 2),
    eventually_ge_atTop 2] with n hu hn2
  have hK0 : (0 : ℝ) ≤ Real.sqrt (400 * Real.pi * A * (2 + r + ε)) := Real.sqrt_nonneg _
  have hu2 : (2 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hu1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hu0 : (0 : ℝ) < Real.log (n : ℝ) := by linarith
  set u : ℝ := Real.log (n : ℝ)
  have hTeq : Twin (n : ℝ) r ε = u ^ (r + ε) := rfl
  -- `u³ ≤ u^(r+ε)`
  have hcube : u ^ (3 : ℕ) ≤ u ^ (r + ε) := by
    have h1 : u ^ (3 : ℝ) ≤ u ^ (r + ε) := Real.rpow_le_rpow_of_exponent_le hu1 hre3
    have h2 : u ^ (3 : ℝ) = u ^ (3 : ℕ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← h2]; exact h1
  have hT0 : (0 : ℝ) < u ^ (r + ε) := Real.rpow_pos_of_pos hu0 _
  have hcube8 : (8 : ℝ) ≤ u ^ (3 : ℕ) := by
    have : u ^ (3 : ℕ) = u * u * u := by ring
    rw [this]; nlinarith
  have hT2 : (2 : ℝ) ≤ u ^ (r + ε) := by linarith
  -- `log(n(T+2)) = u + log(T+2)`, and `log(T+2) ≤ log 2 + (r+ε)·log u ≤ log 2 + (r+ε)·u`
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hsplit : Real.log ((n : ℝ) * (u ^ (r + ε) + 2))
      = u + Real.log (u ^ (r + ε) + 2) := by
    rw [Real.log_mul (ne_of_gt hn0) (by positivity)]
  have hloglog : Real.log u ≤ u := by
    have := Real.log_le_sub_one_of_pos hu0; linarith
  have hre0 : (0 : ℝ) ≤ r + ε := by linarith
  have hlogT : Real.log (u ^ (r + ε) + 2) ≤ Real.log 2 + (r + ε) * u := by
    have hle : u ^ (r + ε) + 2 ≤ 2 * u ^ (r + ε) := by linarith
    have hstep : Real.log (u ^ (r + ε) + 2) ≤ Real.log (2 * u ^ (r + ε)) :=
      Real.log_le_log (by positivity) hle
    have heval : Real.log (2 * u ^ (r + ε)) = Real.log 2 + (r + ε) * Real.log u := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hT0), Real.log_rpow hu0]
    nlinarith [hstep, heval.le, heval.ge, hloglog]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hbound : Real.log ((n : ℝ) * (u ^ (r + ε) + 2)) ≤ (2 + r + ε) * u := by
    rw [hsplit]; nlinarith [hlogT, hu1]
  -- `400πA(2+r+ε) ≤ u²`
  have hsq : 400 * Real.pi * A * (2 + r + ε) ≤ u ^ (2 : ℕ) := by
    have h1 : Real.sqrt (400 * Real.pi * A * (2 + r + ε)) ≤ u := by linarith
    have h2 : u ^ (2 : ℕ) = u * u := by ring
    nlinarith [Real.sq_sqrt hnn, hK0]
  have hcoef : (0 : ℝ) < 400 * Real.pi * A := by positivity
  calc 400 * Real.pi * A * Real.log ((n : ℝ) * (Twin (n : ℝ) r ε + 2))
      = 400 * Real.pi * A * Real.log ((n : ℝ) * (u ^ (r + ε) + 2)) := by rw [hTeq]
    _ ≤ 400 * Real.pi * A * ((2 + r + ε) * u) :=
        mul_le_mul_of_nonneg_left hbound hcoef.le
    _ = (400 * Real.pi * A * (2 + r + ε)) * u := by ring
    _ ≤ u ^ (2 : ℕ) * u := mul_le_mul_of_nonneg_right hsq hu0.le
    _ = u ^ (3 : ℕ) := by ring
    _ ≤ u ^ (r + ε) := hcube
    _ = Twin (n : ℝ) r ε := hTeq.symm

/-- **`FamRvMLower` HOLDS ALONG THE DESIGN OF RECORD — finding F50's row, DISCHARGED.**

`famRvM_lower_from_tree` delivers the RvM count with its two residues explicit; each is
absorbed into half of `rvmSlack`:

  * §12.2's conductor residue `19·Q(1+log Q)³`, by `residue_small_eventually` at `1/200`
    (it is `Θ(log³Q/(Q·ℒ))` relative — astronomically small);
  * RvM's own error `A·|𝔉|·log(Q(T+2))`, by `rvm_error_small` — the `Θ(1/T)` term that
    F50 shows cannot be absorbed at `famAvgL` itself.

This is why `rvmSlack` exists.  Every input is the artifact's own; no free hypotheses.
Rule 17: `r ≥ 3` is the paper's regime; nothing caps λ, relates `X` to `T`, or pins `D₀`. -/
theorem famRvMLower_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord Family.qle r ε (n : ℝ) P → FamRvMLower Family.qle n P := by
  obtain ⟨A, T₀, hA, hlow⟩ := famRvM_lower_from_tree
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop := by
    have hre : (0 : ℝ) < r + ε := by linarith
    exact (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  filter_upwards [residue_small_eventually (ε := 1 / 200) (by norm_num),
    rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀,
    eventually_ge_atTop 2] with n hres herr hT0 hn2
  intro P hdes
  obtain ⟨hP, hQ, hT, -⟩ := hdes
  have hTpos : (0 : ℝ) < P.T := T_posQ hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey := hlow P hP (by rw [hT]; exact hT0) n hn2 hQ
  have hM0 : (0 : ℝ) < P.T / (2 * Real.pi) := by positivity
  have hS0 : (0 : ℝ) ≤ Family.sizeR Family.qle n := by
    unfold Family.sizeR; positivity
  -- (i) the §12.2 residue, at half the slack
  have h1 : P.T / (2 * Real.pi) * (19 * (n : ℝ) * (1 + Real.log n) ^ 3)
      ≤ Family.sizeR Family.qle n * (P.T / (2 * Real.pi)) / 200 := by
    have h := mul_le_mul_of_nonneg_left hres hM0.le
    nlinarith [h]
  -- (ii) RvM's own error, at the other half
  have hlogpos : (0 : ℝ) ≤ Real.log ((n : ℝ) * (P.T + 2)) := by
    apply Real.log_nonneg
    have hn : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    nlinarith
  have h2 : A * (Family.sizeR Family.qle n * Real.log ((n : ℝ) * (P.T + 2)))
      ≤ Family.sizeR Family.qle n * (P.T / (2 * Real.pi)) / 200 := by
    have herr' : 400 * Real.pi * A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T := by
      rw [hT]; exact herr
    have hstep : A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T / (2 * Real.pi) / 200 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith [herr']
    nlinarith [mul_le_mul_of_nonneg_left hstep hS0]
  -- assemble
  unfold FamRvMLower famAvgLlow rvmSlack
  have hexp : Family.sizeR Family.qle n
        * (P.T / (2 * Real.pi) * (famAvgL Family.qle P - 1 / 100))
      = Family.sizeR Family.qle n * (P.T / (2 * Real.pi) * famAvgL Family.qle P)
        - Family.sizeR Family.qle n * (P.T / (2 * Real.pi)) / 200
        - Family.sizeR Family.qle n * (P.T / (2 * Real.pi)) / 200 := by ring
  rw [hexp]
  linarith [hkey, h1, h2]

/-- **`FamRvMLower` ALONG THE DESIGN OF RECORD FOR THE TWO `Icc 2 Qn` PARITY FAMILIES**.

Exactly `famRvMLower_of_design`'s assembly, with `famRvM_lower_with_residue_parity` in place
of `famRvM_lower_from_tree` and `residue_small_parity_eventually` in place of
`residue_small_eventually`. Both residues are again absorbed into half of `rvmSlack`. -/
theorem famRvMLower_parity_of_design {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = 1 / 2) (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.qle.moduli Qn)
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord F r ε (n : ℝ) P → FamRvMLower F n P := by
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop := by
    have hre : (0 : ℝ) < r + ε := by linarith
    exact (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  filter_upwards [residue_small_parity_eventually hF hmod (ε := 1 / 200) (by norm_num),
    rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀,
    eventually_ge_atTop 2] with n hres herr hT0 hn2
  intro P hdes
  obtain ⟨hP, hQ, hT, -⟩ := hdes
  have hTpos : (0 : ℝ) < P.T := T_posQ hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey := famRvM_lower_with_residue_parity P hP hF hsh n hn2 (hmod n) hQ hA.le hrvm
    (by rw [hT]; exact hT0)
  have hM0 : (0 : ℝ) < P.T / (2 * Real.pi) := by positivity
  have hS0 : (0 : ℝ) ≤ Family.sizeR F n := by unfold Family.sizeR; positivity
  have h1 : P.T / (2 * Real.pi) * (21 * (n : ℝ) * (1 + Real.log n) ^ 3)
      ≤ Family.sizeR F n * (P.T / (2 * Real.pi)) / 200 := by
    have h := mul_le_mul_of_nonneg_left hres hM0.le
    nlinarith [h]
  have hlogpos : (0 : ℝ) ≤ Real.log ((n : ℝ) * (P.T + 2)) := by
    apply Real.log_nonneg
    have hn : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    nlinarith
  have h2 : A * (Family.sizeR F n * Real.log ((n : ℝ) * (P.T + 2)))
      ≤ Family.sizeR F n * (P.T / (2 * Real.pi)) / 200 := by
    have herr' : 400 * Real.pi * A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T := by
      rw [hT]; exact herr
    have hstep : A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T / (2 * Real.pi) / 200 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith [herr']
    nlinarith [mul_le_mul_of_nonneg_left hstep hS0]
  unfold FamRvMLower famAvgLlow rvmSlack
  have hexp : Family.sizeR F n * (P.T / (2 * Real.pi) * (famAvgL F P - 1 / 100))
      = Family.sizeR F n * (P.T / (2 * Real.pi) * famAvgL F P)
        - Family.sizeR F n * (P.T / (2 * Real.pi)) / 200
        - Family.sizeR F n * (P.T / (2 * Real.pi)) / 200 := by ring
  rw [hexp]
  linarith [hkey, h1, h2]

end FamilyBridge

/-- **✅ Prop 3.1 (iii) AT THE PROVED CONSTANT — what §9/H6 gives OUTRIGHT, with no
zero-density assumption. Retained under D35 as the disclosure, not as the shipped row.**

**Status.** **D10** made this the row every downstream budget
statement consumes, and **D34** enlarged `budgetTotal` to accommodate it. **D35 reverses
both**: `budgetTotal` charges `L₄` and the assembly consumes `buffer_row_sharp`, whose
hypothesis `SharpZeroDensity` names the paper's own assumption (§10.3's flag). This theorem is
**kept, unchanged**, because it is the honest counterweight to that assumption: it is exactly
what the artifact *could* prove from its own imports, and `buffer_row_gap` (direction) plus the
private `bufferProved_le_L4` (`≤ 1000·L₄` in the design regime) quantify what charging it
instead would have cost — `≈ πA₀ ≈ 255×` on that row, `84/23/9.7/4.3` times the rate term at
`Q = 10²⁵/10¹⁰⁰/10³⁰⁰/10¹⁰⁰⁰`. Nothing here is deleted or weakened by D35.

**F18 repaired (D14).** The conclusion used to price [R]'s ζ-only `3A₀D₀·log(4T)` while
`hloc` below is the q-uniform local count, whose §9 consequence is `3A₀D₀·log(4qT)`; the
statement was therefore FALSE for `Q ≳ 10³⁴⁰⁰`, where the coded row falls below the sharp
density (`rowR3`), which is the truth. `bufferRowProved`'s body now carries the q-uniform
summand, so the conclusion below is the one §9 proves. Nothing else in the statement moved.

What §9/H6 actually gives, q-uniformly:
`N_{II,χ} ≤ 3·A₀·D₀·log(4qT)` per character (`ZetaQ.EFChi.NIID_chi_le`), summed over 𝔉_Q as
`ZetaQ.EFChi.NII_fam_le` and divided by `𝒩`.

Paper §9; `ZetaQ/EFChi.lean` `NIID_chi_le`, `NII_fam_le`; [R] `Tail/GevreyTail.lean:1878` for
the ζ-only ancestor.
Depends on: `ZetaQ.EFChi.NII_fam_le`, `ZetaQ.NIIFamQ`.
**Rule 17: `NIID_le` is the FREE-buffer bound.** Its hypotheses `2 ≤ D` and `D + 4 ≤ T` are
exactly `ParamsQ.Valid.two_le_D0` and `D0_le`; [R]'s version got both free from `√T ≥ 17`,
which is why ours states them (`Defs.lean` §5's note). `Zeta23.Assembly.NII` and
`Zeta23.D0` do not occur.

✅ **F28 — PRE-WIRED AND NOW PROVED, from its two inputs elsewhere in the tree.**
The two things every previous pass recorded as blocking this row are now named `Prop`s and
threaded in explicitly (the D18 pattern), so the row itself is discharged here and the join
is one `exact` apiece when §9/§12.2 land:
  * `hNII : FamNIIUpper F Qn P A₀` — §9's family buffer bound. **Read its docstring**: it is
    `EFChi.NII_fam_le` at the CONDUCTOR-AVERAGED step, and from `NII_fam_le`'s printed form
    (`log q ≤ ℒ` per character) this row is NOT provable — it would be equivalent to
    `⟨shift⟩ ≤ 2 log 2 − 1`, false for `Family.qle` by the same `0.1137` nats as F19/F24.
    That is a third instance of the same defect, and it is charged there, not hidden here.
  * `hrvm : FamRvMLower F Qn P` — the family RvM **lower** bound at the true family average.
`hloc` is retained unused: it is the hypothesis from which §9 derives `hNII`, and keeping it
in the signature keeps the provenance auditable at every call site. -/
theorem buffer_row_proved_of_valid (F : Family) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hP : P.Valid) (hA₀ : 1 ≤ A₀)
    -- H6, q-uniformly: the local zero count of `L(s,χ)`
    (hloc : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q, ∀ t : ℝ,
      NcountQ q χ t (t + 1) ≤ A₀ * Real.log ((q : ℝ) * (|t| + 3)))
    -- **F28**: §9's family aggregate of `hloc`, and the family RvM lower bound.
    (hNII : FamNIIUpper F Qn P A₀) (hrvm : FamRvMLower F Qn P) :
    NIIFamQ P F Qn ≤ bufferRowProved A₀ P * NfamQ P F Qn := by
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hD2 : (2 : ℝ) ≤ P.D0 := hP.two_le_D0
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  -- `ℒ ≥ 1`, from `Q ≥ 3` and `T ≥ 300`
  have hLL1 : (1 : ℝ) ≤ P.LL := by
    unfold ParamsQ.LL
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h1 : Real.exp 1 * (2 * Real.pi) ≤ 2.7182818286 * 8 := by nlinarith [Real.exp_pos 1]
    nlinarith [mul_nonneg (sub_nonneg.2 hQ3) (sub_nonneg.2 hT300)]
  have hLL0 : (0 : ℝ) < P.LL := by linarith
  -- `log 4T ≥ 7` (`e⁷ = 1096.6 ≤ 1200 ≤ 4T`)
  have hlog4T : (7 : ℝ) ≤ Real.log (4 * P.T) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h7 : Real.exp 1 ^ (7 : ℕ) = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
    have hle : Real.exp 7 ≤ (2.7182818286 : ℝ) ^ (7 : ℕ) := by
      rw [← h7]; exact pow_le_pow_left₀ (Real.exp_pos 1).le he.le 7
    have hnum : (2.7182818286 : ℝ) ^ (7 : ℕ) ≤ 1097 := by norm_num
    linarith
  -- `log 8π ≤ 5 log 2 ≤ 3.4658`
  have hlog8pi : Real.log (8 * Real.pi) ≤ 3.4658 := by
    have h1 : (8 : ℝ) * Real.pi ≤ 32 := by linarith
    have h2 : Real.log (8 * Real.pi) ≤ Real.log 32 := Real.log_le_log (by positivity) h1
    have h3 : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    linarith [Real.log_two_lt_d9]
  have hs2 : F.conductorShift ≤ 1 / 2 := conductorShift_le_half F
  have hs0 : (0 : ℝ) ≤ F.conductorShift := conductorShift_nonneg F
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsz : (0 : ℝ) ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  -- ── the scalar core: `(ℒ − s + log 8π)·ℒ ≤ (ℒ + log 4T)·⟨ℒ⟩_𝔉` ─────────────────────
  have hkey : (P.LL - F.conductorShift + Real.log (8 * Real.pi)) * P.LL
      ≤ (P.LL + Real.log (4 * P.T)) * famAvgLlow F P := by
    unfold famAvgLlow famAvgL rvmSlack
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.log (4 * P.T) - 7)
        (by linarith : (0:ℝ) ≤ P.LL - 0.1238),
      mul_nonneg (by linarith : (0:ℝ) ≤ Real.log (4 * P.T))
        (by linarith : (0:ℝ) ≤ 2 * Real.log 2 - 1 - F.conductorShift - 1/100 + 0.1238),
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * Real.log 2 - 1 - Real.log (8 * Real.pi) + 3.0796)
        (by linarith : (0:ℝ) ≤ P.LL)]
  -- ── assemble ──────────────────────────────────────────────────────────────────────
  have hNII' : NIIFamQ P F Qn
      ≤ 3 * A₀ * P.D0 * (P.LL - F.conductorShift + Real.log (8 * Real.pi)) * F.sizeR Qn :=
    hNII
  have hrvm' : F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgLlow F P) ≤ NfamQ P F Qn := hrvm
  have hc : (0 : ℝ) ≤ 3 * A₀ * P.D0 * F.sizeR Qn := by
    have : (0 : ℝ) ≤ 3 * A₀ * P.D0 := by nlinarith
    exact mul_nonneg this hsz
  have hfin : NIIFamQ P F Qn
      ≤ 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) * F.sizeR Qn * famAvgLlow F P / P.LL := by
    rw [le_div_iff₀ hLL0]
    refine (mul_le_mul_of_nonneg_right hNII' hLL0.le).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hkey hc]
  have hbr0 : (0 : ℝ) ≤ bufferRowProved A₀ P := by
    unfold bufferRowProved
    have h1 : (0 : ℝ) ≤ 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) :=
      mul_nonneg (by nlinarith) (by linarith)
    exact div_nonneg h1 (mul_nonneg (by positivity) hLL0.le)
  have hrw : bufferRowProved A₀ P * (F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgLlow F P))
      = 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) * F.sizeR Qn * famAvgLlow F P / P.LL := by
    have hTne : P.T ≠ 0 := ne_of_gt hT0
    have hpine : Real.pi ≠ 0 := ne_of_gt hpi0
    have hLLne : P.LL ≠ 0 := ne_of_gt hLL0
    unfold bufferRowProved
    field_simp
  calc NIIFamQ P F Qn
      ≤ 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) * F.sizeR Qn * famAvgLlow F P / P.LL := hfin
    _ = bufferRowProved A₀ P * (F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgLlow F P)) := hrw.symm
    _ ≤ bufferRowProved A₀ P * NfamQ P F Qn := mul_le_mul_of_nonneg_left hrvm' hbr0

/-- `buffer_row_proved_of_valid` at the design of record — the statement the join consumes.
The body moved to `buffer_row_proved_of_valid` (it reads `P.Valid` only), so that the
row serves the margin design `DesignOfRecordM` too. -/
theorem buffer_row_proved (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q, ∀ t : ℝ,
      NcountQ q χ t (t + 1) ≤ A₀ * Real.log ((q : ℝ) * (|t| + 3)))
    (hNII : FamNIIUpper F Qn P A₀) (hrvm : FamRvMLower F Qn P) :
    NIIFamQ P F Qn ≤ bufferRowProved A₀ P * NfamQ P F Qn :=
  buffer_row_proved_of_valid F Qn P A₀ hdes.1 hA₀ hloc hNII hrvm

/-- **🚩 Prop 3.1 (iii) AS THE PAPER CHARGES IT — `L₄ = 6D₀/T` at the sharp zero density,
i.e. `r₃ = rowR3 = 2D₀/T`. Under D35 this IS the artifact's row.**

**Decision D35, reversing D10 and D34: this is the row the budget
consumes**, and `assembly_clauses_at_design` wires it in. (D10 had said the opposite — "the row
the downstream statements take is `buffer_row_proved`, do not wire `buffer_row_sharp` into
`assembly_at_lamStar`" — and D34 enlarged `budgetTotal` to make that consistent. Both are
reversed; the reasoning is at `budgetTotal`.)

**NOT DISCHARGEABLE FROM H6 ALONE — and that is stated, not hidden.** The hypothesis
`SharpZeroDensity` is exactly the content the proved absolute `A₀` of §9 does not supply, and
it is the paper's own assumption: §10.3 prices this row at the sharp density and §10.4 calls it
"the one row NOT charged at its proved constant". Carrying it as a named hypothesis reproduces
the paper's epistemic position exactly (the same pattern as
`ZetaQ.l2_concentration_exists` for §6's Lemma 6.1), so every consumer is auditable. What
§9/H6 *does* prove outright is `buffer_row_proved`, retained, with the gap named in
`buffer_row_gap` and quantified in the private `bufferProved_le_L4`.

Paper §10.3.
Depends on: `SharpZeroDensity`, `FamRvMLower`.
Rule 17: `P.D0` free throughout; neither added hypothesis mentions `λ`, `X` or `√T`.

✅ **REPAIRED AND NOW PROVED (policy D17).**  Two earlier passes recorded this as
BLOCKED, and the diagnosis was right but the cause was upstream of the statement.  With
`NIIFamQ = (D₀/π)|𝔉|(ℒ − shift + (log 2)/2) + o(·)` and
`rowR3·𝒩 = (D₀/π)|𝔉|(ℒ − shift + 2 log 2 − 1)`, the conclusion is true by a margin of
`(2 log 2 − 1) − (log 2)/2 = 0.0397` nats — a relative `1.6×10⁻⁴` at the design — while the
frozen `SharpZeroDensity` (at the `ℒ`-surrogate) *overshot* the target by
`shift − (2 log 2 − 1) = 0.1137` nats for `Family.qle`, i.e. by nearly three times the
available margin.  So the route could not close, and the missing RvM lower bound was named
in a form (`𝒩 ≥ |𝔉|(T/2π)ℒ`) that is FALSE for `qle`.

Both defects are the same one — the `ℒ`-surrogate for `𝒩/|𝔉|` — and both are fixed at their
source: `SharpZeroDensity` and `FamRvMLower` are now stated at the true family average
`famAvgL`.  At that average the two sides line up exactly (`hsharp`'s bound equals
`(2D₀/T)·|𝔉|(T/2π)⟨ℒ⟩_𝔉`), so the proof is `hrvm` scaled by `2D₀/T ≥ 0`.  (F24's repair was
independent of the sharp/proved convention and is unaffected by D35; what D35 changed is only
which of the two rows `budgetTotal` charges.) -/
theorem buffer_row_sharp (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hsharp : SharpZeroDensity F Qn P)
    (hrvm : FamRvMLower F Qn P) :
    NIIFamQ P F Qn ≤ rowR3 P * NfamQ P F Qn := by
  obtain ⟨hP, -⟩ := hdes
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hD0 : (0 : ℝ) ≤ P.D0 := by linarith [hP.two_le_D0]
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hscale : (0 : ℝ) ≤ 2 * P.D0 / P.T := by positivity
  have hstep := mul_le_mul_of_nonneg_left hrvm hscale
  have hL : 2 * P.D0 / P.T * (F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgLlow F P))
      = 2 * (P.D0 / (2 * Real.pi)) * famAvgLlow F P * F.sizeR Qn := by
    field_simp
  have hR : 2 * P.D0 / P.T * NfamQ P F Qn = rowR3 P * NfamQ P F Qn := by
    unfold rowR3 L₄ cBuffer; ring
  rw [hL, hR] at hstep
  exact le_trans hsharp hstep

/-- **🚩 THE GAP, NAMED.** The budget's buffer row is *smaller* than the proved one:
`L₄ ≤ bufferRowProved A₀`. That is the wrong direction for discharging `L₄` from H6 — which
is precisely why `buffer_row_sharp` needs `SharpZeroDensity` and `buffer_row_proved` does
not. Paper §10.3: charging the proved constant "would move the finite-Q thresholds, never
the asymptotics", and §10.4 states which convention its table uses.

**This was a coordinating decision** — (a) restate the row at `3A₀` and
re-run §10.4's table, or (b) keep `SharpZeroDensity` as a named hypothesis. `D10` took (a),
`D34` enlarged `budgetTotal` to make (a) consistent with the assembly, and
**D35 reverses both and takes (b)** — because (b) is what the paper
itself does and says it does. This statement is the record of the gap either way, and it is
untouched by the reversal; the private `bufferProved_le_L4` quantifies it in the design regime.

**REPAIRED THIS PASS (D14) AND NOW PROVED.** As frozen the statement was FALSE, for two
independent reasons, and both are fixed:

1. **`bufferRowProved`'s body dropped the conductor** (module header, F18). Cancelling the
   common `D₀/T > 0`, the claim was equivalent to `ℒ ≤ π·A₀·log(4T)`. At the design of
   record `T = (log Q)^{r+ε}` this reads `log Q ≲ π·A₀·(r+ε)·log log Q`, which holds only up
   to `Q ≈ 10³⁴⁰⁰` and fails for every larger `Q` — the *opposite* of the intended reading,
   and fatal because Theorem 1 is a statement about all large `Q`. **Fixed at the source:**
   `bufferRowProved` now carries `(ℒ + log 4T)`, so the content here is
   `ℒ ≤ π·A₀·(ℒ + log 4T)`, true with room to spare (`π·A₀ ≥ π > 3`) uniformly in `Q`.
2. **Nothing bounded `P.Q` from below.** The old `hA₀`, `hT : T₀ ≤ P.T`, `hD : 2 ≤ P.D0` left
   `P.Q` free, so `P.Q = 0` gives `P.LL = Real.log 0 = 0`, hence `bufferRowProved A₀ P = 0`
   (division by zero in Lean) while `L₄ P = 6·P.D0/P.T > 0`. **Fixed** by taking `P.Valid`,
   whose `Q_ge : 3 ≤ P.Q` and `T_ge : 300 ≤ P.T` together give `0 < P.LL`, and which
   subsumes both discarded facts (`T_ge` is `hT`; `two_le_D0` is `hD`). `P.Valid` is strictly
   the hypothesis class every other row in this file already runs under, so this is not an
   added assumption in any operative sense.

Neither repair weakens the statement: `hA₀ : 1 ≤ A₀` is untouched, the conclusion is the
same inequality at the row §9 actually proves, and the direction (`L₄` below the proved row)
is unchanged — which is exactly why `buffer_row_sharp` needs `SharpZeroDensity` while
`buffer_row_proved` does not, and why D10 shipped the proved row (until D35 reversed it).

Paper §10.3, §10.4.
Rule 17: `P.D0` free; the facts consumed from `P.Valid` are `Q_ge`, `T_ge`, `two_le_D0`,
none of which relates `D₀` to `√T`. -/
theorem buffer_row_gap (P : ParamsQ) (hP : P.Valid) (A₀ : ℝ) (hA₀ : 1 ≤ A₀) :
    L₄ P ≤ bufferRowProved A₀ P := by
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hD0 : (0 : ℝ) < P.D0 := by linarith [hP.two_le_D0]
  have hQ : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi' : Real.pi < 4 := Real.pi_lt_four
  have hπ2 : (0 : ℝ) < 2 * Real.pi := by linarith
  -- `ℒ = log(QT/2π) > 0`, from `Q ≥ 3` and `T ≥ 300`.
  have hLL : (0 : ℝ) < P.LL := by
    unfold ParamsQ.LL
    refine Real.log_pos ((one_lt_div hπ2).mpr ?_)
    nlinarith [mul_nonneg (sub_nonneg.2 hQ) (sub_nonneg.2 hT)]
  have hlog4T : (0 : ℝ) < Real.log (4 * P.T) := Real.log_pos (by linarith)
  unfold L₄ bufferRowProved cBuffer
  rw [div_le_div_iff₀ hT0 (mul_pos (div_pos hT0 hπ2) hLL)]
  -- `T/(2π)·ℒ ≤ T·ℒ/6`, since `2π > 6`.
  have hdiv : P.T / (2 * Real.pi) * P.LL ≤ P.T * P.LL / 6 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hπ2 (by norm_num : (0 : ℝ) < 6)]
    nlinarith [mul_pos hT0 hLL]
  -- `ℒ ≤ 3A₀(ℒ + log 4T)`, since `A₀ ≥ 1`.
  have hmain : P.LL ≤ 3 * A₀ * (P.LL + Real.log (4 * P.T)) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A₀ - 1)
      (by linarith : (0 : ℝ) ≤ P.LL + Real.log (4 * P.T))]
  have hDT : (0 : ℝ) < P.D0 * P.T := mul_pos hD0 hT0
  calc 6 * P.D0 * (P.T / (2 * Real.pi) * P.LL)
      ≤ 6 * P.D0 * (P.T * P.LL / 6) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = P.D0 * P.T * P.LL := by ring
    _ ≤ P.D0 * P.T * (3 * A₀ * (P.LL + Real.log (4 * P.T))) :=
        mul_le_mul_of_nonneg_left hmain hDT.le
    _ = 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) * P.T := by ring

/-- **Alias, retained for continuity.** The previous pass, treating `buffer_row_gap` as
frozen while it was false, proved the repaired statement under this name. F18 is now
repaired at the source, so this is literally `buffer_row_gap`. Prefer that name. -/
theorem buffer_row_gap' (P : ParamsQ) (hP : P.Valid) (A₀ : ℝ) (hA₀ : 1 ≤ A₀) :
    L₄ P ≤ bufferRowProvedQ A₀ P := buffer_row_gap P hP A₀ hA₀

/-- `1 ≤ A₀` at §9's proved local-count constant `EFChi.A0 = 10/log(95/84) = 81.2611…`.

Introduced because **D34** made `budgetTotal` charge the buffer row at that constant, and every
row lemma about `bufferRowProved` carries `hA₀ : 1 ≤ A₀`.  **D35** reverses D34, and this is
RETAINED (D35's keep-list): it is what lets `buffer_row_gap` and `buffer_row_proved` be
instantiated at §9's actual constant, which is the disclosure the named assumption needs. Proof: `log(95/84) ≤ 95/84 − 1 =
11/84 ≤ 10` and `log(95/84) > 0`, so `10/log(95/84) ≥ 1` (in fact `≥ 76`).
Rule 17: a numeral. -/
theorem one_le_A0 : (1 : ℝ) ≤ EFChi.A0 := by
  have h1 : (0 : ℝ) < Real.log (95 / 84) := Real.log_pos (by norm_num)
  have h2 : Real.log (95 / 84) ≤ 10 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 95 / 84 by norm_num)
    linarith
  show (1 : ℝ) ≤ 10 / Real.log (95 / 84)
  rw [le_div_iff₀ h1]; linarith

/-- **Prop 3.1 (iv), the pair rows.** §7's Gevrey tail gives `θ₀ → 0` per block
(superexponentially, `θ₀ ≤ exp(−(4/e)√(wD₀/A))·prefactor` under `ClosingCondition`), and
§7.3 aggregates it additively in trace and √-additively in Frobenius. **No negative power of
Q is demanded**.

Paper §7, §7.3.
Depends on: `ZetaQ.Btr`, `ZetaQ.BF`, `rowR4`, `rowR5`.
Rule 17: the tail bound is at the FREE `D₀`, via `ClosingCondition`; forcing `D₀ = √T` is
what §7.1 says breaks the rate class.

✅ **WAS FALSE FOR `Family.qle` AT EVERY `θ₀ > 0`; REPAIRED AND NOW PROVED (D17).**
Both conjuncts reduce, after cancelling `θ₀/(a·L) > 0`, to the single inequality
"`|𝔉|·(row's surrogate for 𝒩/|𝔉|) ≤ 𝒩`" (the second under `√`).  At the frozen surrogate
`(T/2π)·ℒ` that is `|𝔉|(T/2π)ℒ ≤ 𝒩`, and the family RvM count is
`|𝔉|(T/2π)(ℒ − 0.113706) + O(|𝔉| log QT)` for `q ≤ Q` — false, at every `Q`, by a full
`0.1137/ℒ`.  The defect was in `rowR4`/`rowR5`, not in §7.3: the surrogate double-priced the
conductor spread that `L₆` already charges.  See `famAvgL`.

The rows now use the true family average, and the content of both conjuncts is exactly
`FamRvMLower`, which is threaded in as an explicit hypothesis (the D18 pattern).  An earlier
pass considered adding `|𝔉|(T/2π)ℒ ≤ 𝒩` and correctly REJECTED it, because in *that* form it
is unsatisfiable for Theorem 1's own family and would have converted a blocked statement into
a vacuous one.  `FamRvMLower` is the same fact at the average RvM actually delivers, and is
satisfiable for both families — that is the whole difference. -/
theorem pair_rows_of_valid (F : Family) (Qn : ℕ) (P : ParamsQ) (θ₀ : ℝ)
    (hP : P.Valid) (hwr : SideCondWrange P) (hθ : 0 ≤ θ₀)
    (hrvm : FamRvMLower F Qn P) :
    Btr P F Qn θ₀ ≤ rowR4 F P θ₀ * NfamQ P F Qn ∧
      BF P F Qn θ₀ ≤ rowR5 F P θ₀ * Real.sqrt (NfamQ P F Qn) := by
  -- the regime
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  -- `ℒ > 0`, hence `L = λℒ > 0`
  have hLL : (0 : ℝ) < P.LL := by
    unfold ParamsQ.LL
    refine Real.log_pos ((one_lt_div (by positivity)).mpr ?_)
    nlinarith
  have hLB : (0 : ℝ) < P.LB := mul_pos hP.lam_pos hLL
  -- `l = log(T/2π) > 0`, hence `toParams.lam > 0` and the taper facts are available
  have hlpos : (0 : ℝ) < Zeta23.l P.T := by
    show (0 : ℝ) < Real.log (P.T / (2 * Real.pi))
    refine Real.log_pos ((one_lt_div (by positivity)).mpr ?_)
    linarith
  have hlne : Zeta23.l P.T ≠ 0 := ne_of_gt hlpos
  have hlampos : (0 : ℝ) < P.toParams.lam := by
    show (0 : ℝ) < P.LB / Zeta23.l P.T
    exact div_pos hLB hlpos
  have hwL' : 8 * P.toParams.w ≤ P.toParams.L P.T := by
    rw [P.toParams_L hlne]; exact hwr
  -- the hat normalisation `a = L⁻¹∫φ²` is bounded below by `3/4` (never `0`) — F58: the
  -- `Valid` floor `a_ge` (for the flat taper it was `three_quarters_le_b ∘ b_le_a`).
  have haQ : (3 : ℝ) / 4 ≤ P.aQ := hP.a_ge
  have ha0 : (0 : ℝ) < P.aQ := by linarith
  -- the abbreviations
  have hA : (0 : ℝ) < P.aQ * P.LB := mul_pos ha0 hLB
  have hM : (0 : ℝ) < P.T / (2 * Real.pi) * famAvgLlow F P :=
    mul_pos (by positivity) (famAvgLlow_pos F P hP)
  have hS : (0 : ℝ) ≤ F.sizeR Qn := by
    unfold Family.sizeR; positivity
  have hN : (0 : ℝ) ≤ NfamQ P F Qn := le_trans (mul_nonneg hS hM.le) hrvm
  constructor
  · -- `Btr ≤ r₄·𝒩` ⟺ `|𝔉|·(T/2π)⟨ℒ⟩ ≤ 𝒩`
    unfold Btr rowR4
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hA (mul_pos hA hM)]
    nlinarith [mul_nonneg (mul_nonneg hθ hA.le) (sub_nonneg.2 hrvm)]
  · -- the `√` half: the same inequality under `Real.sqrt`
    unfold BF rowR5
    have hsqM : (0 : ℝ) < Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) := Real.sqrt_pos.mpr hM
    have hsplit : Real.sqrt (F.sizeR Qn) * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
        = Real.sqrt (F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgLlow F P)) :=
      (Real.sqrt_mul hS _).symm
    have hsq : Real.sqrt (F.sizeR Qn) * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
        ≤ Real.sqrt (NfamQ P F Qn) := by
      rw [hsplit]; exact Real.sqrt_le_sqrt hrvm
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hA (mul_pos hA hsqM)]
    nlinarith [mul_nonneg (mul_nonneg hθ hA.le) (sub_nonneg.2 hsq)]

/-- `pair_rows_of_valid` at the design of record — the statement the join consumes. The
body moved to `pair_rows_of_valid` (it reads `P.Valid` and `SideCondWrange P` only), so that the
rows serve the margin design `DesignOfRecordM` too. -/
theorem pair_rows (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (θ₀ : ℝ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hθ : 0 ≤ θ₀)
    (hrvm : FamRvMLower F Qn P) :
    Btr P F Qn θ₀ ≤ rowR4 F P θ₀ * NfamQ P F Qn ∧
      BF P F Qn θ₀ ≤ rowR5 F P θ₀ * Real.sqrt (NfamQ P F Qn) :=
  pair_rows_of_valid F Qn P θ₀ hdes.1 hdes.2.2.2.2.2.1 hθ hrvm

/-- §8 Lemma 8.1's family ends input in its raw shape:
`B_fam(τ)² ≤ c₁²·Q²·(ℒ + log⁺(|τ|/4T) + C₀)²` with the explicit absolute constants
`c₁ = 0.41`, `C₀ = 6` (frozen as `ZetaQ.c1Ends`, `ZetaQ.C0Ends`). Carried as a named `Prop`
because §8 lives in `ZetaQ/Ends.lean`, which `ZetaQ/Budget.lean` does not import directly.
Provenance: paper §8 (580).
Rule 17: the CAP-FREE `_L` ends lemmas are the only admissible producers — see `cEnds`. -/
def EndsFamBound (Qn : ℕ) (P : ParamsQ) (endsFam : ℝ) : Prop :=
  ∀ τ : ℝ, endsFam ≤ c1Ends ^ 2 * (Qn : ℝ) ^ 2 *
    (P.LL + Real.log (max 1 (|τ| / (4 * P.T))) + C0Ends) ^ 2

/-- **🚩 `Q₀` for the ends row — `10¹⁶`.  F27, implemented (policy D17); raised for
Corollary 3.**

Paper §10.5, verbatim: *"Q₀(ε) is the largest of §§5–9's thresholds"*.  Theorem 1 is an
asymptotic statement with an explicit `Q ≥ Q₀(ε)`; `DesignOfRecord` simply fails to carry
one, and **without one `ends_row` is FALSE at the smallest admissible design points** — the
failing instances are recorded at `ends_row`.  Adding the threshold as an explicit
hypothesis rather than as a `DesignOfRecord` field is deliberate: D16 says not to re-freeze
`DesignOfRecord`, and only this one row needs it.

*The numeral is calibrated in `ℒ`, not in `Q`.*  Since `ℒ = log(QT/2π)` and `Valid.T_ge`
gives `T ≥ 300`, `Q ≥ 10¹⁶` forces `ℒ ≥ log(10¹⁶·300/2π) = 40.71`, and the proof runs at the
round `ℒ ≥ 40`.

*Why `10¹⁶` and not the old `2.5×10⁵`.*  `2.5×10⁵` buys `ℒ ≥ 16.295`, which is what the
numeric core needs at `π·C ≤ 22.68` — i.e. on the two FULL families only (exact crossings
`ℒ ≈ 13.9` family-uniformly and `ℒ ≈ 10.6` for `Family.qle` alone).  Corollary 3's four
parity families carry `π·C = π⁵/9 = 34.00` (`evenQle`/`oddQle`) and `4π⁵/27 = 45.34`
(`evenDyadic`/`oddDyadic`), at which the crossings are `ℒ = 22.12` and `ℒ = 33.65`; the
uniform chain `ends_row` now runs, at `π·C ≤ 45.4`, crosses at `ℒ = 34.12`.  So `ℒ ≥ 16` is
genuinely insufficient — this is a feature of the row (at `C = 4π⁴/27` the ends charge really
is `2.6×` its Theorem-1 value while `L₅·𝒩` is unchanged), not an artefact of the bounding.
At `ℒ ≥ 40` the core holds with ≈ 8 % of room (`17647.6` against `16148.8`).

**Cost: none.**  §10.5 quantifies over `Q ≥ Q₀(ε)` and calls `Q₀(ε)` "the largest of §§5–9's
thresholds"; `10¹⁶` is still four orders of magnitude below §10.4's own "non-vacuous from
`≈ 10²⁰`", and vastly below the figure F23 moves that to, so the threshold is absorbed and no
printed figure moves. -/
def endsQ0 : ℝ := 10000000000000000

/-- **The §12.2 family-size count, as a named `Prop`:** `Q² ≤ C·|𝔉_Q|`, i.e.
`|𝔉_Q| ≥ Q²/C` — which is §2.2's defining relation `C := Q²/|𝔉_Q|` (`Family.Cconst`) read
as a lower bound.  Concretely `|𝔉_Q| ≥ (18/π⁴)Q²` for `qle` and `≥ (13.5/π⁴)Q²` for
`dyadic`; both are the leading term of `Σ_{q ≤ Q} φ*(q) = (18/π⁴)Q² + O(Q log Q)`, verified
numerically here at `Q = 12, 65, 100, 10³, 2·10³` (ratios `0.1875, 0.1870, 0.1816, 0.18483,
0.18498` against `18/π⁴ = 0.184788`).

Threaded in explicitly (the D18 pattern) because §12.2's count is **not proved anywhere in
this tree** — it is the same obligation `ZetaQ.Ends.Bfam_le_sep` names, and the previous
passes recorded it as one of the two things blocking the ends row. -/
def FamSizeLower (F : Family) (Qn : ℕ) : Prop := (Qn : ℝ) ^ 2 ≤ F.Cconst * F.sizeR Qn

/-- **Row L₅ (ends) is a separate charge**, not folded into `rowR1`/`rowR2`: §8's family
ends bound is stated only in family sum (one of the "exactly three components bounded only
in family sum", §10.2's aggregation discharge), and enters through `B_fam/√|𝔉|` in hat
units. This statement is the interface §8 must meet.

Paper §8 (Lemma 8.2), §10.2.
Depends on: `L₅`.
Rule 17: **cap-free `_L` ends lemmas ONLY** (`calE1_maj_bound_L`,
`Zeta23/PrimeSideA/EndsE1.lean:727`; `calE2_maj_bound_L`, `EndsE2.lean:353`). The capped
forms require `L ≤ 2l`, false here by 10–60×, and that is a λ ≤ 1 smuggle in disguise.

**F23 note — this statement is NOT the one whose constant moved.**  `EndsFamBound` is the
RAW `B_fam²` bound `c₁²Qn²(ℒ + log⁺ + C₀)²`, not the hat-normalised relative order; against
`L₅·𝒩 ≈ 6ℒ log ℒ/T · (18/π⁴)Qn²(T/2π)ℒ` the ratio is `≈ 0.95/log ℒ < 1`, so the conclusion
here is comfortable at `c_ends = 6` **once `ℒ` is large enough** — and the previous passes'
"≈ 0.95/log ℒ" is exactly the statement that it is NOT comfortable while `log ℒ ≲ 0.95`'s
finite-`ℒ` corrections bite.  The row whose coefficient F23 moves is the relative one,
`ZetaQ.Ends.ends_relative_le` — see `L₅proved`.

──────────────────────────────────────────────────────────────────────────────────────────
🚩 **THIS STATEMENT WAS FALSE AS FROZEN.  REPAIRED AND NOW PROVED (policy D17).**

**The diagnosis, verified.**  `hfam` at `τ = 0` gives the tightest bound it has,
`endsFam ≤ c₁²Qn²(ℒ + C₀)² = 0.1681·Qn²(ℒ+6)²`, and the right-hand side, given §12.2's
family-size count and the family RvM lower bound, is at least
`L₅·|𝔉|(T/2π)⟨ℒ⟩_𝔉 = (3/(πC))·Qn²·ℒ·log ℒ·⟨ℒ⟩_𝔉`, i.e. `(54/π⁵)Qn²ℒ(ℒ−0.1137)log ℒ` for
`Family.qle` and `(81/2π⁵)Qn²ℒ(ℒ+0.1173)log ℒ` for `Family.dyadic`.  So the row reduces to

    0.1681(ℒ + 6)²  ≤  (3/(πC))·ℒ·log ℒ·⟨ℒ⟩_𝔉,

which needs `ℒ ≳ 10.6` (qle) / `ℒ ≳ 13.7` (dyadic).  **`DesignOfRecord` admits far smaller
`ℒ`**: it fixes `T = (log Q)^{r+ε}` and `Valid.T_ge` only asks `T ≥ 300`, so `log Q` may be
as small as `300^{1/(r+ε)}`, and nothing in `ends_row` bounds `r + ε`.  The binding side
condition is `SideCondWrange` (`8w ≤ λℒ` with `w = 1`), which floors `ℒ` at `8/λ* = 6.40`
and no higher.

**Failing instances** (all with `F = Family.qle`, `endsFam` taken at its largest admissible
value `c₁²Qn²(ℒ+C₀)²`, `𝒩` evaluated from the q-uniform RvM main term with the exact
`Σ_{q≤Qn} φ*(q)` and `Σ_{q≤Qn} φ*(q) log q`; every clause of `DesignOfRecord` checked):

| `Qn` | `r+ε` | `T` | `ℒ` | `\|𝔉\|` | LHS | RHS | LHS/RHS |
|---|---|---|---|---|---|---|---|
| 12 | 6.32 | 315.0 | 6.400 | 27 | 3721.8 | 1930.6 | **1.928** |
| 20 | 5.50 | 417.6 | 7.192 | 80 | 11702 | 7720 | **1.516** |
| 65 | 4.00 | 303.7 | 8.052 | 790 | 140247 | 100687 | **1.393** |
| 100 | 3.90 | 386.1 | 8.723 | 1816 | 364399 | 281851 | **1.293** |
| 1000 | 3.00 | 329.6 | 10.868 | 184830 | 4.783e7 | 4.922e7 | 0.972 ✓ |

The `Qn = 65, r+ε = 4` line is the instance the previous pass conjectured (it could not pin
`NfamQ` there); it is confirmed, at `1.393` rather than the estimated `1.42`.  The RvM error
term is irrelevant to the refutation: at `Qn = 12` it is `≤ 27·A·log(12·317) ≈ 223A` against
`𝒩 = 8533`, so even `A = 4` moves the ratio by under 11 %.

**The repair, and why it is the paper's own form.**  §10.5 states outright that Theorem 1
carries an explicit `Q ≥ Q₀(ε)` and that *"Q₀(ε) is the largest of §§5–9's thresholds"*.
This row is one of those thresholds; `DesignOfRecord` merely fails to carry it.  The
threshold enters as the explicit hypothesis `hQ0 : endsQ0 ≤ P.Q` (`endsQ0 = 10¹⁶`, which
forces `ℒ ≥ 40.71`) rather than as a new `DesignOfRecord` field, per D16 — no other
statement in this file needs it, and re-freezing `DesignOfRecord` would ripple through
every theorem here.  `hsize` and `hrvm` are the two inputs from elsewhere that earlier notes
recorded as missing (§12.2's count and the family RvM lower bound); they are threaded in
explicitly, the D18 pattern, so the join is one `exact` when those tracks land.

**Cost.**  None asymptotically: Theorem 1 quantifies over `Q ≥ Q₀` already, and
`ℒ ≥ 40.71` is `Q ≥ 10¹⁶`, four orders of magnitude below §10.4's own
"non-vacuous from ≈ 10²⁰" (and ≈ 1000 orders below where F23 moves that figure to).  The
threshold is therefore absorbed by `Q₀(ε)` and changes no printed figure.

──────────────────────────────────────────────────────────────────────────────────────────
**COROLLARY 3 — ONE CHAIN, ALL SIX FAMILIES; the `¬ F.IsFull` `sorry` is closed.**

The only place `F` enters the numeric core is `π·C`.  The chain used to be run at
`hpiC : π·C ≤ 22.68`, which is FALSE on the four parity families: `Family.Cconst` is
`CfamEven = π⁴/9` on `evenQle`/`oddQle` (`π·C = π⁵/9 = 34.0027`) and `CfamEvenDyadic = 4π⁴/27`
on `evenDyadic`/`oddDyadic` (`π·C = 4π⁵/27 = 45.3367`).  A single uniform bound
`π·C ≤ 45.4` covers all six constants (`17.0013 / 22.6684 / 34.0027 / 34.0027 / 45.3367 /
45.3367`), so no separate parity chain is needed and the `by_cases F.IsFull` is gone.

The price is the threshold.  `(★)`, the core after cancelling `Qn²` and clearing
`L₅ = 6ℒ log ℒ/T`, reads `c₁²·(ℒ + C₀)²·(π·C) ≤ 3·ℒ·log ℒ·⟨ℒ⟩_low`; at `π·C = 45.4` and
`⟨ℒ⟩_low ≥ ℒ − 0.1238` that is `7.63174·(ℒ + 6)² ≤ 3·ℒ·log ℒ·(ℒ − 0.1238)`, whose crossing is
`ℒ = 34.12`.  Hence `endsQ0` is raised from `2.5×10⁵` (`ℒ ≥ 16.295`) to `10¹⁶`
(`ℒ ≥ 40.71`); see `endsQ0` for why that costs nothing.  The two numerals that moved in the
proof are `hpiC` (`22.68 ↦ 45.4`) and the `ℒ` floor (`16`, `log ℒ ≥ 2.772` ↦ `40`,
`log ℒ ≥ 3.6657`); everything else is the previous `IsFull` proof verbatim. -/
theorem ends_row (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (endsFam : ℝ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    -- **F27**: §10.5's `Q ≥ Q₀(ε)`, which `DesignOfRecord` does not carry.
    (hQ0 : endsQ0 ≤ P.Q)
    -- §12.2's family-size count, and the family RvM lower bound (both from §12).
    (hsize : FamSizeLower F Qn)
    (hrvm : FamRvMLower F Qn P)
    (hfam : EndsFamBound Qn P endsFam) :
    endsFam ≤ L₅ P * NfamQ P F Qn := by
  obtain ⟨hP, -⟩ := hdes
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpiu : Real.pi < 3.1416 := Real.pi_lt_d4
  have hQ16 : (10000000000000000 : ℝ) ≤ P.Q := by unfold endsQ0 at hQ0; linarith
  have hQ0' : (0 : ℝ) < P.Q := by linarith
  -- ── `ℒ ≥ 40`, from `Q ≥ 10¹⁶` and `T ≥ 300` ───────────────────────────────────────
  have hexp40 : Real.exp 40 ≤ 242000000000000000 := by
    have he : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h40 : Real.exp 1 ^ (40 : ℕ) = Real.exp 40 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [← h40]
    calc Real.exp 1 ^ (40 : ℕ) ≤ (2.72 : ℝ) ^ (40 : ℕ) :=
          pow_le_pow_left₀ (Real.exp_pos 1).le he.le 40
      _ ≤ 242000000000000000 := by norm_num
  have hLL40 : (40 : ℝ) ≤ P.LL := by
    unfold ParamsQ.LL
    rw [Real.le_log_iff_exp_le (div_pos (mul_pos hQ0' hT0) (by positivity)),
      le_div_iff₀ (by positivity)]
    have hb1 : Real.exp 40 * (2 * Real.pi) ≤ 242000000000000000 * (2 * 3.1416) :=
      mul_le_mul hexp40 (by linarith) (by positivity) (by norm_num)
    have hb2 : (3000000000000000000 : ℝ) ≤ P.Q * P.T := by
      nlinarith [mul_nonneg (sub_nonneg.2 hQ16) (sub_nonneg.2 hT300)]
    linarith
  -- `log ℒ ≥ log 40 = 5 log 2 + log(5/4) ≥ 3.46573 + 0.2`
  have hlog40 : (3.6657 : ℝ) ≤ Real.log P.LL := by
    have h54 : (1 / 5 : ℝ) ≤ Real.log (5 / 4) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
      have hinv : Real.log (5 / 4 : ℝ) = -Real.log (4 / 5 : ℝ) := by
        rw [show (5 / 4 : ℝ) = (4 / 5 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hinv]; linarith
    have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    have h40 : Real.log (40 : ℝ) = Real.log 32 + Real.log (5 / 4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have hmono : Real.log 40 ≤ Real.log P.LL := Real.log_le_log (by norm_num) hLL40
    have hl2 := Real.log_two_gt_d9
    rw [h40, h32] at hmono
    linarith
  -- ── the family constant: `0 < C` and `π·C ≤ 45.4` for ALL SIX families ─────────────
  have hpi5 : Real.pi ^ 5 ≤ 306.024 := by
    have h : Real.pi ^ 5 ≤ (3.1416 : ℝ) ^ 5 :=
      pow_le_pow_left₀ Real.pi_pos.le hpiu.le 5
    have h2 : (3.1416 : ℝ) ^ 5 ≤ 306.024 := by norm_num
    linarith
  have hC0 : (0 : ℝ) < F.Cconst := by
    cases F <;>
      simp only [Family.Cconst, Cfam, CfamDyadic, CfamEven, CfamEvenDyadic] <;> positivity
  -- `π⁵/18 = 17.00`, `2π⁵/27 = 22.67`, `π⁵/9 = 34.00`, `4π⁵/27 = 45.34`.
  have hpiC : Real.pi * F.Cconst ≤ 45.4 := by
    cases F
    · simp only [Family.Cconst, Cfam]
      have h : Real.pi * (Real.pi ^ 4 / 18) = Real.pi ^ 5 / 18 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamDyadic]
      have h : Real.pi * (2 * Real.pi ^ 4 / 27) = 2 * Real.pi ^ 5 / 27 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamEven]
      have h : Real.pi * (Real.pi ^ 4 / 9) = Real.pi ^ 5 / 9 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamEven]
      have h : Real.pi * (Real.pi ^ 4 / 9) = Real.pi ^ 5 / 9 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamEvenDyadic]
      have h : Real.pi * (4 * Real.pi ^ 4 / 27) = 4 * Real.pi ^ 5 / 27 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamEvenDyadic]
      have h : Real.pi * (4 * Real.pi ^ 4 / 27) = 4 * Real.pi ^ 5 / 27 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamEven]
      have h : Real.pi * (Real.pi ^ 4 / 9) = Real.pi ^ 5 / 9 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamEven]
      have h : Real.pi * (Real.pi ^ 4 / 9) = Real.pi ^ 5 / 9 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamEvenDyadic]
      have h : Real.pi * (4 * Real.pi ^ 4 / 27) = 4 * Real.pi ^ 5 / 27 := by ring
      rw [h]; linarith
    · simp only [Family.Cconst, CfamEvenDyadic]
      have h : Real.pi * (4 * Real.pi ^ 4 / 27) = 4 * Real.pi ^ 5 / 27 := by ring
      rw [h]; linarith
  have hpiC0 : (0 : ℝ) < Real.pi * F.Cconst := mul_pos hpi0 hC0
  -- ── the left-hand side: `hfam` at `τ = 0` (`log⁺ = 0`) ─────────────────────────────
  have hlhs : endsFam ≤ c1Ends ^ 2 * (Qn : ℝ) ^ 2 * (P.LL + C0Ends) ^ 2 := by
    have h := hfam 0
    rwa [abs_zero, zero_div, max_eq_left (zero_le_one : (0:ℝ) ≤ 1), Real.log_one,
      add_zero] at h
  -- ── the right-hand side: `|𝔉| ≥ Qn²/C` then the family RvM lower bound ─────────────
  have hM : (0 : ℝ) < P.T / (2 * Real.pi) * famAvgLlow F P :=
    mul_pos (by positivity) (famAvgLlow_pos F P hP)
  have hsize' : (Qn : ℝ) ^ 2 ≤ F.Cconst * F.sizeR Qn := hsize
  have hsz : (Qn : ℝ) ^ 2 / F.Cconst ≤ F.sizeR Qn :=
    (div_le_iff₀ hC0).2 (by linarith)
  have hN : (Qn : ℝ) ^ 2 / F.Cconst * (P.T / (2 * Real.pi) * famAvgLlow F P) ≤ NfamQ P F Qn :=
    le_trans (mul_le_mul_of_nonneg_right hsz hM.le) hrvm
  have hL5 : (0 : ℝ) ≤ L₅ P := by
    unfold L₅ cEnds
    exact div_nonneg (by nlinarith [hLL40, hlog40]) hT0.le
  -- ── the numeric core: `0.1681(ℒ+6)²·45.4 ≤ 3ℒ·log ℒ·⟨ℒ⟩_𝔉` at `ℒ ≥ 40` ────────────
  have hm : P.LL - 0.1238 ≤ famAvgLlow F P := by
    have := conductorShift_le_half F
    have hl2 := Real.log_two_gt_d9
    unfold famAvgLlow famAvgL rvmSlack; linarith
  have hm0 : (0 : ℝ) ≤ famAvgLlow F P := by linarith
  have h3 : 3.6657 * (P.LL - 0.1238) ≤ Real.log P.LL * famAvgLlow F P := by
    have ha : 3.6657 * famAvgLlow F P ≤ Real.log P.LL * famAvgLlow F P :=
      mul_le_mul_of_nonneg_right hlog40 hm0
    linarith
  have hcore : c1Ends ^ 2 * (P.LL + C0Ends) ^ 2 * 45.4
      ≤ 3 * P.LL * (Real.log P.LL * famAvgLlow F P) := by
    unfold c1Ends C0Ends
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 3 * P.LL), hLL40,
      sq_nonneg (P.LL - 40)]
  have hstep : c1Ends ^ 2 * (P.LL + C0Ends) ^ 2 * (Real.pi * F.Cconst)
      ≤ 3 * P.LL * Real.log P.LL * famAvgLlow F P := by
    have hnn : (0 : ℝ) ≤ c1Ends ^ 2 * (P.LL + C0Ends) ^ 2 := by positivity
    nlinarith [hcore, hpiC, hnn]
  -- ── assemble ──────────────────────────────────────────────────────────────────────
  have hA : (0 : ℝ) ≤ (Qn : ℝ) ^ 2 := sq_nonneg _
  have hrw : L₅ P * ((Qn : ℝ) ^ 2 / F.Cconst * (P.T / (2 * Real.pi) * famAvgLlow F P))
      = 3 * P.LL * Real.log P.LL * (Qn : ℝ) ^ 2 * famAvgLlow F P / (Real.pi * F.Cconst) := by
    have hTne : P.T ≠ 0 := ne_of_gt hT0
    have hpine : Real.pi ≠ 0 := ne_of_gt hpi0
    have hCne : F.Cconst ≠ 0 := ne_of_gt hC0
    unfold L₅ cEnds
    field_simp
    ring
  have hkey : c1Ends ^ 2 * (Qn : ℝ) ^ 2 * (P.LL + C0Ends) ^ 2
      ≤ L₅ P * ((Qn : ℝ) ^ 2 / F.Cconst * (P.T / (2 * Real.pi) * famAvgLlow F P)) := by
    rw [hrw, le_div_iff₀ hpiC0]
    nlinarith [mul_le_mul_of_nonneg_left hstep hA]
  calc endsFam ≤ c1Ends ^ 2 * (Qn : ℝ) ^ 2 * (P.LL + C0Ends) ^ 2 := hlhs
    _ ≤ L₅ P * ((Qn : ℝ) ^ 2 / F.Cconst * (P.T / (2 * Real.pi) * famAvgLlow F P)) := hkey
    _ ≤ L₅ P * NfamQ P F Qn := mul_le_mul_of_nonneg_left hN hL5

/-- **The accounting identity of §10.3, as an inequality.** Prop 3.1's bracket at the design
of record is at most §10.3's printed TOTAL: the coefficients `4, 1, 3, 4` of Prop 3.1 are
already folded into the row constants (e.g. `3·rowR3 = 6D₀/T = L₄`), so `budgetTotal` IS the
bracket. `≤` rather than `=` deliberately keeps §10.3's open accounting question (Q7: [R]'s
trace-side `w/L`, whose conservative reading is `r₂ + 4r₁ = 10w/L`) open — `cRamp` is a
`def` so both readings compile.

**REPAIRED THIS PASS (D14) AND NOW PROVED.** As frozen the statement was FALSE, twice over.
The rows telescope exactly, and what was left over is *positive*:

    propBracket − budgetTotal  =  3·L₆ − L₅ − L₉ + (4·rowR4 + 2·rowR5·√(κ_C+r₂) + rowR5²)

(`rowR2` already contains `zone + L₃ + L₇ + L₈ + L₁₀ + L₁₁ + L₁₂`, and `3·rowR3 = L₄`, so
every other row cancels; `minorRows` contributes `L₆` once.) The two failures, and the two
repairs:

1. **`rowR1` was not folded, but `budgetTotal` assumes it is.** The module's accounting note
   says Prop 3.1's coefficients `4, 1, 3, 4` are *already folded into the row constants* —
   and `rowR3 := L₄/3` does exactly that, so that `3·rowR3 = L₄`. But `rowR1` was `L₆`, so
   `4·rowR1 = 4L₆` entered the bracket while `budgetTotal` charges `L₆` once. The residue
   `3L₆` was not covered: `3L₆ − L₅ − L₉` is `+9.7×10⁻³` at `Q = 10²⁵`, `+3.1×10⁻³` at
   `10¹⁰⁰`, `+1.1×10⁻³` at `10³⁰⁰`, and positive at every design point — `L₆ = Θ(1/ℒ)` while
   `L₅ = Θ(ℒ log ℒ/T) = Θ(log ℒ/ℒ^{r+ε−1})` with `r ≥ 3`, so `L₆/L₅ → ∞`.
   **Repaired at `rowR1 := L₆/4`** — see `rowR1`'s docstring for why that is the paper's own
   reading (it is what makes `budgetTotal` the TOTAL column of `log_table2.txt`, whence
   §10.4's `P_eff = P − TOTAL` reproduces `+0.20/+0.61/+0.68/+0.71`), which clause of §10.5
   disagrees, and what the alternative repair would cost (`budgetTotal += 3L₆`: `≤ 0.010` in
   §10.4's finite-Q figures, nothing asymptotically).
2. **`θ₀` was unbounded.** The only hypothesis on it was `hθ : 0 ≤ θ₀`, and `rowR4` is linear
   in `θ₀` with a positive coefficient, so the left-hand side was unbounded above while
   `budgetTotal` does not mention `θ₀` at all. (Positive coefficient: `rowR4`'s denominator
   is `a·L·(T/2π)ℒ`, and the hat normalisation `a := L⁻¹∫φ²` is `> 0` for any non-null taper,
   as are `L`, `T`, `ℒ` under `P.Valid`.) Fatal on its own, independently of (1), and
   the reason the `≤` could not be read as "conservative". **Repaired** by the explicit
   hypothesis `hpair`, which is §10.5's own wiring-table clause for Prop 3.1 (iv) —
   *"absorbed (θ₀ superexponentially small); L₅ separate"* — written down as an inequality
   instead of as prose: the pair block is absorbed by the slack §10.3's printed table
   leaves, namely `L₅ + L₉`. It is discharged from §7's closing bound
   `θ₀ ≤ exp(−(4/e)√(wD₀/A))·prefactor` under `ClosingCondition`, which `DesignOfRecord`
   carries but which nothing in the frozen statement *used*.

Neither repair weakens the claim in the sense that matters: the conclusion is unchanged, and
`hpair` is not slack invented for the proof but the missing half of Prop 3.1 (iv)'s wiring.

Paper §3 (: "whose rows are exactly the rᵢ"), §10.3,
§10.5's wiring table. Depends on: every `Lᵢ`, `rowR1`–`rowR5`.
Rule 17: no λ ≤ 1, X ≤ T or D₀ = √T; `hpair` relates `θ₀` to the ends and smearing rows and
mentions neither `X` nor `√T`.

### ✅ **D35: back to the exact ring identity.**

D34 had briefly raised `budgetTotal`'s buffer row to `bufferRowProved EFChi.A0`, which made
this statement *weaker* (`L₄ P ≤ bufferRowProved A₀ P` by `buffer_row_gap`) and its proof "the
ring identity, then one application of `buffer_row_gap`". **D35 reverses that**, so
`budgetTotal` is again `zone + L₃ + L₄ + L₅ + minor` and this is again the exact accounting
identity of §10.3 — the folded coefficients `3·rowR3 = L₄` and `4·rowR1 = L₆` cancel and what
is left over is precisely `(L₅ + L₉) − (pair block)`, which is `hpair`. No majorant slack is
used anywhere in the proof; the `≤` in the statement is there only for Q7, as above. -/
theorem propBracket_le_budgetTotal (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (θ₀ : ℝ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hθ : 0 ≤ θ₀)
    -- §10.5's Prop 3.1 (iv) row, as an inequality: the pair block is absorbed.
    (hpair : 4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) :
    propBracket F P θ₀ ≤ budgetTotal F P := by
  -- the sharp-density total (D35), at which the folded coefficients cancel exactly
  have key : budgetTotal F P - propBracket F P θ₀
      = (L₅ P + L₉ P)
        - (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P)
            + rowR5 F P θ₀ ^ 2) := by
    unfold budgetTotal propBracket minorRows rowR1 rowR2 rowR3
    ring
  linarith

/-! ## Row-by-row asymptotics — the private bookkeeping behind `budgetTotal_isBigO`

Every row of `budgetTotal` is estimated in one regime, written in `u = log Q` and
`v = log log Q`:

    8 ≤ u,    3 ≤ v,    (2(r + ε) + 10)·v ≤ u,

which `atTop` supplies eventually at each fixed `(r, ε)` — the last clause because
`log log Q = o(log Q)` (`isLittleO_loglog_log`).  In that regime a `DesignOfRecord` point
satisfies

    T = u^{r+ε} ≥ u³,   ℒ = u + (r+ε)v − log 2π ∈ [u/2, 2u],   L = λℒ ∈ [u/2, 3u],
    w = 1,              0 ≤ l(T) ≤ (r+ε)v,                     δ′ = 3v/u,

and every row is then bounded by an explicit constant multiple of `v/u`:

| row | bound |
|-----|-------|
| `zoneRowLinear` | `(2(r+ε) + 3)·v/u` |
| `L₃` (ramp) | `12·v/u` |
| **`L₄`** (buffer, **D35**) | `6c·v/u`, from `hD0 : D₀ ≤ c(log Q)²` against `T ≥ u³` (`row_L4`) |
| `L₅` (ends) | `24·v/u` |
| `L₆` (conductor spread) | `1·v/u` |
| `L₇` (zone boundary) | `(11(r+ε) + 22)·v/u` |
| `L₈` (out-zone cross) | `6·v/u` |
| `L₉` (`D_T` smearing) | `1·v/u` |
| `L₁₀` (grid/shell) | `48·v/u` |
| `L₁₁` (sieve correction) | `2·v/u`, from `λ ≤ 1.26 < 2` |
| `L₁₂` (in-zone cross) | `42·v/u` |

`w = 1` is where `r ≥ 3` is used (`ℒ^{(3−r)/2} ≤ 1` at `ℒ ≥ 1`), and the buffer row is where
`hD0` is used — the two clauses the statement's docstring singles out.  The total is
`13(r+ε) + 6c + 161 ≤ 20(r+ε) + 6c + 200` times `v/u`.

**D35 note (reversing D34).** D34 had charged the buffer at `bufferRowProved EFChi.A0`, which
cost one extra factor `πA₀·(ℒ + log 4T)/ℒ ≤ (5/2)πA₀ ≤ 870 < 1000` — isolated then, and
retained now, in the private `bufferProved_le_L4` — taking the buffer constant to `6000c` and
the witness to `20(r+ε) + 6000c + 200`.  D35 charges `L₄`, so the row is back to `6c·v/u`,
`row_L4` is consumed directly, and `bufferProved_le_L4` / `A0_bounds` are no longer part of
this bound.  **They are deliberately kept**: they are the machine-checked record of the
`≈ πA₀ ≈ 255` factor between the paper's convention and the proved one, which is the
disclosure that goes with naming `SharpZeroDensity` as a hypothesis (see `budgetTotal`).

These declarations are `private` bookkeeping; they are not part of the paper's statement
record and nothing outside this file may cite them. -/

private theorem log_two_pi_le_three : Real.log (2 * Real.pi) ≤ 3 := by
  have h8 : (2 : ℝ) * Real.pi ≤ 8 := by linarith [Real.pi_le_four]
  have h1 : Real.log (2 * Real.pi) ≤ Real.log 8 := Real.log_le_log (by positivity) h8
  have h2 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  linarith [Real.log_two_lt_d9]

private theorem log_two_pi_nonneg : 0 ≤ Real.log (2 * Real.pi) :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])

/-! ### Numeric bookkeeping for the closing condition (D27)

Crude two-sided bounds on `e`, `e²`, `e⁴`, `e⁸`, and on the four `Real.log` constants the
`D₀ = O(ℒ²)` derivation needs. Everything is deliberately generous: only the ORDER of the
resulting `D₀` bound matters (`budgetTotal_le_of_regime` takes the constant as a parameter),
so no effort is spent sharpening. -/

private theorem exp_pow_bounds :
    (7.29 : ℝ) ≤ Real.exp 2 ∧ Real.exp 2 ≤ 7.4 ∧ (53 : ℝ) ≤ Real.exp 4
      ∧ (2800 : ℝ) ≤ Real.exp 8 ∧ Real.exp 8 ≤ 3000 := by
  have hlo : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hhi : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have h8 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have e2lo : (7.29 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith
  have e2hi : Real.exp 2 ≤ 7.4 := by rw [h2]; nlinarith [Real.exp_pos 1]
  have e4lo : (53 : ℝ) ≤ Real.exp 4 := by rw [h4]; nlinarith
  have e4hi : Real.exp 4 ≤ 55 := by rw [h4]; nlinarith [Real.exp_pos 2]
  refine ⟨e2lo, e2hi, e4lo, ?_, ?_⟩
  · rw [h8]; nlinarith
  · rw [h8]; nlinarith [Real.exp_pos 4]

private theorem log_const_bounds :
    Real.log 4 ≤ 2 ∧ Real.log 6 ≤ 2 ∧ Real.log 100 ≤ 5 ∧ Real.log 100000 ≤ 12 := by
  obtain ⟨e2lo, e2hi, e4lo, e8lo, e8hi⟩ := exp_pow_bounds
  have h5 : (100 : ℝ) ≤ Real.exp 5 := by
    have : Real.exp 5 = Real.exp 4 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_one_gt_d9]
  have h12 : (100000 : ℝ) ≤ Real.exp 12 := by
    have : Real.exp 12 = Real.exp 8 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Real.log_le_log (by norm_num : (0:ℝ) < 4) (by linarith : (4:ℝ) ≤ Real.exp 2)
    rwa [Real.log_exp] at h
  · have h := Real.log_le_log (by norm_num : (0:ℝ) < 6) (by linarith : (6:ℝ) ≤ Real.exp 2)
    rwa [Real.log_exp] at h
  · have h := Real.log_le_log (by norm_num : (0:ℝ) < 100) h5
    rwa [Real.log_exp] at h
  · have h := Real.log_le_log (by norm_num : (0:ℝ) < 100000) h12
    rwa [Real.log_exp] at h

private theorem gevreyA_bounds : (13 : ℝ) ≤ gevreyA ∧ gevreyA ≤ 14 := by
  have hlo : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hhi : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  unfold gevreyA
  exact ⟨by rw [le_div_iff₀ he]; linarith, by rw [div_le_iff₀ he]; linarith⟩

private theorem c4_bounds : (1.4 : ℝ) ≤ c4 ∧ c4 ≤ 1.5 := by
  have hlo : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hhi : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  unfold c4
  exact ⟨by rw [le_div_iff₀ he]; linarith, by rw [div_le_iff₀ he]; linarith⟩

private theorem gevreyB_le : gevreyB ≤ 6000 := by
  obtain ⟨-, -, -, -, e8hi⟩ := exp_pow_bounds
  unfold gevreyB; linarith

/-- The elementary algebra behind `S(D₀) ≤ (1 + M)(1 + t)`: the row-sum factor is affine in
`t` with a nonnegative coefficient, so it is dominated by the product of the two factors it
would have if `t` and the coefficient were separated. -/
private theorem rowSum_prod_le {K t c : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t) (hc : 0 < c) :
    1 + K * (t / c + 1 / c ^ 2) ≤ (1 + K * (1 / c + 1 / c ^ 2)) * (1 + t) := by
  have h1 : 0 ≤ K * (1 / c) := by positivity
  have h2 : 0 ≤ K * (1 / c ^ 2) * t := by positivity
  have key : (1 + K * (1 / c + 1 / c ^ 2)) * (1 + t) - (1 + K * (t / c + 1 / c ^ 2))
      = t + K * (1 / c) + K * (1 / c ^ 2) * t := by ring
  linarith

private theorem lamStar_bounds (F : Family) : 1 ≤ F.lamStar ∧ F.lamStar ≤ 1.26 := by
  cases F <;>
    refine ⟨by norm_num [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10, lamStarEvenDyad12],
            by norm_num [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10,
              lamStarEvenDyad12]⟩

private theorem Cconst_bounds (F : Family) : 0 < F.Cconst ∧ F.Cconst ≤ 20 := by
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have h4 : Real.pi ^ 4 ≤ 98.5 := by
    have h := pow_le_pow_left₀ hpi0.le Real.pi_lt_d4.le 4
    nlinarith [h]
  have h4' : (0 : ℝ) < Real.pi ^ 4 := by positivity
  cases F <;>
    refine ⟨by simp only [Family.Cconst, Cfam, CfamDyadic, CfamEven, CfamEvenDyadic]; linarith,
            by simp only [Family.Cconst, Cfam, CfamDyadic, CfamEven, CfamEvenDyadic];
               linarith⟩

private theorem conductorShift_bounds (F : Family) :
    0 ≤ F.conductorShift ∧ F.conductorShift ≤ 1 / 2 :=
  ⟨conductorShift_nonneg F, conductorShift_le_half F⟩

private theorem dPdlogC_bounds : 0 ≤ dPdlogC ∧ dPdlogC ≤ 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨div_nonneg (by norm_num) hlog2.le, ?_⟩
  unfold dPdlogC
  rw [div_le_one hlog2]
  linarith [Real.log_two_gt_d9]

private theorem cCross_bounds : 0 ≤ cCross ∧ cCross ≤ 3 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  unfold cCross
  have h9 : (24 : ℝ) / Real.pi ≤ 9 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  calc Real.sqrt (24 / Real.pi) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt h9
    _ = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]



private theorem rowBound_key {u v x K : ℝ} (hu : 0 < u) (h : x * u ≤ K * v) : x ≤ K * (v / u) := by
  rw [← mul_div_assoc, le_div_iff₀ hu]; exact h

private theorem row_zone (F : Family) (P : ParamsQ) (rr u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hrr : 3 ≤ rr)
    (hdel : P.deltaPrime = 3 * v / u)
    (hllo : 0 ≤ Zeta23.l P.T) (hlhi : Zeta23.l P.T ≤ rr * v)
    (hlLL : Zeta23.l P.T ≤ P.LL) (hLLlo : u / 2 ≤ P.LL) (hLL0 : 0 < P.LL) :
    0 ≤ zoneRowLinear F P ∧ zoneRowLinear F P ≤ (2 * rr + 3) * (v / u) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have ht0 : (0 : ℝ) ≤ Zeta23.l P.T / P.LL := div_nonneg hllo hLL0.le
  have ht1 : Zeta23.l P.T / P.LL ≤ 1 := (div_le_one hLL0).2 hlLL
  have hdel0 : (0 : ℝ) ≤ P.deltaPrime := by rw [hdel]; positivity
  have hdelb : P.deltaPrime = 3 * (v / u) := by rw [hdel]; ring
  have htb : Zeta23.l P.T / P.LL ≤ 2 * rr * (v / u) := by
    refine rowBound_key hu0 ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hLL0]
    nlinarith [mul_le_mul_of_nonneg_right hlhi hu0.le,
      mul_le_mul_of_nonneg_left hLLlo (by positivity : (0:ℝ) ≤ 2 * rr * v)]
  have hzoneX0 : (0 : ℝ) ≤ 1 - zoneFactor P := by
    unfold zoneFactor
    nlinarith [mul_nonneg hdel0 (sub_nonneg.2 ht1)]
  have hzoneX : 1 - zoneFactor P ≤ P.deltaPrime + Zeta23.l P.T / P.LL := by
    unfold zoneFactor
    nlinarith [mul_nonneg hdel0 ht0]
  constructor
  · exact zoneRowLinear_nonneg F P hzoneX0
  · -- `s_F ≤ 1` for both families, so `s_F(1 − a) ≤ 1 − a ≤ δ′ + l/ℒ ≤ (2rr + 3)·v/u`
    have hs1 : F.sZoneF ≤ 1 := le_trans (sZoneF_le F) (by norm_num)
    calc zoneRowLinear F P = F.sZoneF * (1 - zoneFactor P) := rfl
      _ ≤ 1 * (1 - zoneFactor P) := mul_le_mul_of_nonneg_right hs1 hzoneX0
      _ ≤ (2 * rr + 3) * (v / u) := by linarith

private theorem row_L3 (P : ParamsQ) (u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hwe : P.w = 1) (hLBlo : u / 2 ≤ P.LB) :
    0 ≤ L₃ P ∧ L₃ P ≤ 12 * (v / u) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  refine ⟨by unfold L₃ cRamp; rw [hwe]; exact div_nonneg (by norm_num) hLB0.le, ?_⟩
  refine rowBound_key hu0 ?_
  unfold L₃ cRamp
  rw [hwe]
  have h1 : (6 : ℝ) * 1 / P.LB * u ≤ 12 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hLB0]; linarith
  linarith

private theorem row_L4 (P : ParamsQ) (u v c : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hc : 0 ≤ c) (hD0 : 0 < P.D0)
    (hD : P.D0 ≤ c * u ^ 2) (hT3 : u ^ 3 ≤ P.T) (hTpos : 0 < P.T) :
    0 ≤ L₄ P ∧ L₄ P ≤ 6 * c * (v / u) := by
  have hu0 : (0 : ℝ) < u := by linarith
  refine ⟨by unfold L₄ cBuffer; exact div_nonneg (by linarith) hTpos.le, ?_⟩
  refine rowBound_key hu0 ?_
  unfold L₄ cBuffer
  have h1 : (6 : ℝ) * P.D0 / P.T * u ≤ 6 * c := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hTpos]
    nlinarith [mul_le_mul_of_nonneg_right hD hu0.le,
      mul_le_mul_of_nonneg_left hT3 (by positivity : (0:ℝ) ≤ 6 * c)]
  nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ v - 1)]

/-- Numeric envelope for §9's proved local-count constant: `1 ≤ A₀ ≤ 87`.
`A₀ = 10/log(95/84) = 81.2611…`; the upper bound is `log(95/84) ≥ 11/95`, i.e.
`−log(84/95) ≥ 1 − 84/95`. Introduced for **D34**'s buffer row; under **D35** it is no longer
consumed by `budgetTotal_le_of_regime` and is retained, with `bufferProved_le_L4`, as the
record of the two conventions' ratio. -/
private theorem A0_bounds : (1 : ℝ) ≤ EFChi.A0 ∧ EFChi.A0 ≤ 87 := by
  have hlogpos : (0 : ℝ) < Real.log (95 / 84) := Real.log_pos (by norm_num)
  have hlo : (11 : ℝ) / 95 ≤ Real.log (95 / 84) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 84 / 95 by norm_num)
    have he : Real.log (84 / 95) = -Real.log (95 / 84) := by
      rw [show (84 : ℝ) / 95 = ((95 : ℝ) / 84)⁻¹ by norm_num, Real.log_inv]
    rw [he] at h; linarith
  refine ⟨one_le_A0, ?_⟩
  show (10 : ℝ) / Real.log (95 / 84) ≤ 87
  rw [div_le_iff₀ hlogpos]; linarith

/-- **The proved buffer row against the paper's, quantified: `bufferRowProved A₀ ≤ 1000·L₄` in
the design regime — the `≈ πA₀ ≈ 255` factor, machine-checked.**

The exact ratio is `πA₀·(ℒ + log 4T)/ℒ`; in the regime `log 4T ≤ (3/2)ℒ` that is at most
`(5/2)πA₀ ≤ (5/2)·4·87 = 870 < 1000`.

**Status under D35.** This was D34's one new step: isolating the comparison here let
`budgetTotal_le_of_regime` re-use `row_L4` verbatim while charging `bufferRowProved`, the whole
change being one extra factor in the buffer constant (`6c ↦ 6000c`). D35 reverses that, so the
lemma is no longer consumed — and it is **kept on purpose**, as the quantitative half of the
disclosure that accompanies naming `SharpZeroDensity` a hypothesis: `buffer_row_gap` gives the
*direction* (`L₄ ≤ bufferRowProved`), this gives the *size* of the gap in the regime where the
theorem lives. Together with `buffer_row_proved` they say exactly what the artifact could have
charged instead, and what it would have cost. Nothing outside this file may cite it (it is
`private`); `buffer_row_gap` is the public statement of the same fact's direction. -/
private theorem bufferProved_le_L4 (P : ParamsQ)
    (hTpos : 0 < P.T) (hD0 : 0 ≤ P.D0) (hLL0 : 0 < P.LL)
    (hlog4T0 : 0 ≤ Real.log (4 * P.T))
    (hlog4T : Real.log (4 * P.T) ≤ 3 / 2 * P.LL) :
    bufferRowProved EFChi.A0 P ≤ 1000 * L₄ P := by
  obtain ⟨hA1, hA87⟩ := A0_bounds
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hden : (0 : ℝ) < P.T / (2 * Real.pi) * P.LL :=
    mul_pos (div_pos hTpos (by linarith)) hLL0
  have hY0 : (0 : ℝ) ≤ P.LL + Real.log (4 * P.T) := by linarith
  have hY : P.LL + Real.log (4 * P.T) ≤ 5 / 2 * P.LL := by linarith
  have hL4 : 1000 * L₄ P = 6000 * P.D0 / P.T := by unfold L₄ cBuffer; ring
  rw [hL4]
  unfold bufferRowProved
  rw [div_le_div_iff₀ hden hTpos]
  have e1 : 3 * EFChi.A0 * P.D0 ≤ 261 * P.D0 := by
    nlinarith [mul_nonneg hD0 (sub_nonneg.2 hA87)]
  have e3 : 3 * EFChi.A0 * P.D0 * (P.LL + Real.log (4 * P.T))
      ≤ 261 * P.D0 * (5 / 2 * P.LL) :=
    mul_le_mul e1 hY hY0 (by linarith)
  have e4 : 3 * EFChi.A0 * P.D0 * (P.LL + Real.log (4 * P.T)) * P.T
      ≤ 261 * P.D0 * (5 / 2 * P.LL) * P.T :=
    mul_le_mul_of_nonneg_right e3 hTpos.le
  have hprod : (0 : ℝ) ≤ P.D0 * P.LL * P.T :=
    mul_nonneg (mul_nonneg hD0 hLL0.le) hTpos.le
  have hstep : P.T * P.LL / 8 ≤ P.T / (2 * Real.pi) * P.LL := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [mul_pos hTpos hLL0]
  have hRHS : 261 * P.D0 * (5 / 2 * P.LL) * P.T
      ≤ 6000 * P.D0 * (P.T / (2 * Real.pi) * P.LL) := by
    nlinarith [mul_le_mul_of_nonneg_left hstep (by linarith : (0:ℝ) ≤ 6000 * P.D0)]
  linarith

private theorem row_L5 (P : ParamsQ) (u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hvle : v ≤ u)
    (hLL0 : 0 < P.LL) (hLLhi : P.LL ≤ 2 * u)
    (hlogLL0 : 0 ≤ Real.log P.LL) (hlogLL : Real.log P.LL ≤ 2 * v)
    (hT3 : u ^ 3 ≤ P.T) (hTpos : 0 < P.T) :
    0 ≤ L₅ P ∧ L₅ P ≤ 24 * (v / u) := by
  have hu0 : (0 : ℝ) < u := by linarith
  refine ⟨by
    unfold L₅ cEnds
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hLL0.le) hlogLL0) hTpos.le, ?_⟩
  refine rowBound_key hu0 ?_
  unfold L₅ cEnds
  have hstep : P.LL * Real.log P.LL ≤ (2 * u) * (2 * v) :=
    mul_le_mul hLLhi hlogLL hlogLL0 (by linarith)
  have h1 : (6 : ℝ) * P.LL * Real.log P.LL / P.T * u ≤ 24 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hTpos]
    nlinarith [mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 6 * u),
      mul_le_mul_of_nonneg_left hvle (by positivity : (0:ℝ) ≤ 24 * u ^ 2),
      mul_le_mul_of_nonneg_left hT3 (by norm_num : (0:ℝ) ≤ 24)]
  linarith

private theorem row_L6 (F : Family) (P : ParamsQ) (u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hLLlo : u / 2 ≤ P.LL) (hLL0 : 0 < P.LL) :
    0 ≤ L₆ F P ∧ L₆ F P ≤ 1 * (v / u) := by
  obtain ⟨hsh0, hsh1⟩ := conductorShift_bounds F
  have hu0 : (0 : ℝ) < u := by linarith
  refine ⟨by
    unfold L₆ sZone
    exact div_nonneg (mul_nonneg (by norm_num) hsh0) hLL0.le, ?_⟩
  refine rowBound_key hu0 ?_
  unfold L₆ sZone
  rw [div_mul_eq_mul_div, div_le_iff₀ hLL0]
  nlinarith [mul_le_mul_of_nonneg_right hv hLL0.le,
    mul_le_mul_of_nonneg_right hsh1 hu0.le]

private theorem row_L7 (F : Family) (P : ParamsQ) (rr u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hrr : 3 ≤ rr)
    (hlogTL0 : 0 ≤ Real.log (P.T * P.LL))
    (hlogTL : Real.log (P.T * P.LL) ≤ (rr + 2) * v)
    (hTLlo : u ^ 4 / 2 ≤ P.T * P.LL) (hTLpos : 0 < P.T * P.LL) :
    0 ≤ L₇ F P ∧ L₇ F P ≤ (11 * rr + 22) * (v / u) := by
  obtain ⟨hC0, hC20⟩ := Cconst_bounds F
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hg0 : (0 : ℝ) < v / u := by positivity
  have hu2 : (64 : ℝ) ≤ u ^ 2 := by nlinarith
  have hsq7 : Real.sqrt (F.Cconst * Real.log (P.T * P.LL) / (P.T * P.LL))
      ≤ (rr + 2) * v / u := by
    have hY0 : (0 : ℝ) ≤ (rr + 2) * v / u :=
      div_nonneg (mul_nonneg (by linarith) hv0.le) hu0.le
    rw [show ((rr + 2) * v / u) = Real.sqrt (((rr + 2) * v / u) ^ 2) from
      (Real.sqrt_sq hY0).symm]
    apply Real.sqrt_le_sqrt
    rw [div_pow, div_le_div_iff₀ hTLpos (by positivity)]
    have hAB : (960 : ℝ) ≤ ((rr + 2) * v) * u ^ 2 := by nlinarith
    have hL : F.Cconst * Real.log (P.T * P.LL) * u ^ 2
        ≤ 20 * ((rr + 2) * v) * u ^ 2 := by
      have h1 : F.Cconst * Real.log (P.T * P.LL) ≤ 20 * ((rr + 2) * v) := by nlinarith
      nlinarith
    have hR : ((rr + 2) * v) ^ 2 * (u ^ 4 / 2) ≤ ((rr + 2) * v) ^ 2 * (P.T * P.LL) :=
      mul_le_mul_of_nonneg_left hTLlo (sq_nonneg _)
    have hXX : 20 * (((rr + 2) * v) * u ^ 2) ≤ (((rr + 2) * v) * u ^ 2) ^ 2 / 2 := by
      nlinarith [hAB]
    nlinarith [hL, hR, hXX]
  refine ⟨by unfold L₇; positivity, ?_⟩
  unfold L₇
  have hs : Real.sqrt (F.Cconst * Real.log (P.T * P.LL) / (P.T * P.LL))
      ≤ (rr + 2) * (v / u) :=
    hsq7.trans (le_of_eq (by ring))
  nlinarith [hs, mul_nonneg (by linarith : (0:ℝ) ≤ 0.99 * rr + 1.98) hg0.le]

private theorem sqrt8 (P : ParamsQ) (u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hlogLB : Real.log P.LB ≤ 2 * v)
    (hTLBlo : u ^ 4 / 2 ≤ P.T * P.LB) (hTLBpos : 0 < P.T * P.LB) :
    Real.sqrt (Real.log P.LB / (P.T * P.LB)) ≤ 2 * v / u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hu2 : (64 : ℝ) ≤ u ^ 2 := by nlinarith
  have hY0 : (0 : ℝ) ≤ 2 * v / u := div_nonneg (by linarith) hu0.le
  rw [show (2 * v / u) = Real.sqrt ((2 * v / u) ^ 2) from (Real.sqrt_sq hY0).symm]
  apply Real.sqrt_le_sqrt
  rw [div_pow, div_le_div_iff₀ hTLBpos (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hlogLB (by positivity : (0:ℝ) ≤ u ^ 2),
    mul_le_mul_of_nonneg_left hTLBlo (by positivity : (0:ℝ) ≤ (2 * v) ^ 2),
    mul_nonneg (by positivity : (0:ℝ) ≤ 2 * v * u ^ 2)
      (by nlinarith : (0:ℝ) ≤ v * u ^ 2 - 1)]

private theorem row_L8 (P : ParamsQ) (u v : ℝ)
    (hsq8 : Real.sqrt (Real.log P.LB / (P.T * P.LB)) ≤ 2 * v / u) :
    0 ≤ L₈ P ∧ L₈ P ≤ 6 * (v / u) := by
  obtain ⟨hdP0, hdP1⟩ := dPdlogC_bounds
  obtain ⟨hcC0, hcC3⟩ := cCross_bounds
  have hS0 : (0 : ℝ) ≤ Real.sqrt (Real.log P.LB / (P.T * P.LB)) := Real.sqrt_nonneg _
  refine ⟨by unfold L₈; exact mul_nonneg (mul_nonneg hdP0 hcC0) hS0, ?_⟩
  unfold L₈
  have h1 : dPdlogC * cCross ≤ 3 := by nlinarith
  calc dPdlogC * cCross * Real.sqrt (Real.log P.LB / (P.T * P.LB))
      ≤ 3 * (2 * v / u) := mul_le_mul h1 hsq8 hS0 (by norm_num)
    _ = 6 * (v / u) := by ring

private theorem row_L9 (P : ParamsQ) (u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hT3 : u ^ 3 ≤ P.T) (hTpos : 0 < P.T) :
    0 ≤ L₉ P ∧ L₉ P ≤ 1 * (v / u) := by
  obtain ⟨hdP0, hdP1⟩ := dPdlogC_bounds
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  refine ⟨by unfold L₉; exact div_nonneg (mul_nonneg hdP0 (by norm_num)) hTpos.le, ?_⟩
  refine rowBound_key hu0 ?_
  unfold L₉
  rw [div_mul_eq_mul_div, div_le_iff₀ hTpos]
  nlinarith [mul_le_mul_of_nonneg_right hdP1 (by positivity : (0:ℝ) ≤ 0.2 * u),
    mul_le_mul hv hT3 (by positivity : (0:ℝ) ≤ u ^ 3) hv0.le,
    mul_nonneg hu0.le (by nlinarith : (0:ℝ) ≤ u ^ 2 - 64)]

private theorem row_L10 (P : ParamsQ) (u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hvle : v ≤ u)
    (hlogLL0 : 0 ≤ Real.log P.LL) (hlogLL : Real.log P.LL ≤ 2 * v)
    (hLBlo : u / 2 ≤ P.LB) (hLB0 : 0 < P.LB) :
    0 ≤ L₁₀ P ∧ L₁₀ P ≤ 48 * (v / u) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  refine ⟨by unfold L₁₀; exact div_nonneg (by positivity) (by positivity), ?_⟩
  refine rowBound_key hu0 ?_
  unfold L₁₀
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hLB0 2)]
  have hsq : Real.log P.LL ^ 2 ≤ (2 * v) ^ 2 := pow_le_pow_left₀ hlogLL0 hlogLL 2
  have hLB2 : (u / 2) ^ 2 ≤ P.LB ^ 2 :=
    pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ u / 2) hLBlo 2
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 3 * u),
    mul_le_mul_of_nonneg_left hLB2 (by positivity : (0:ℝ) ≤ 48 * v),
    mul_le_mul_of_nonneg_left hvle (by positivity : (0:ℝ) ≤ 12 * v * u)]

private theorem row_L11 (P : ParamsQ) (Q u v : ℝ)
    (hu : 8 ≤ u) (hv : 3 ≤ v) (hQeq : P.Q = Q) (hueq : u = Real.log Q)
    (hlamP2 : P.lam ≤ 1.26) :
    0 ≤ L₁₁ P ∧ L₁₁ P ≤ 2 * (v / u) := by
  obtain ⟨hdP0, hdP1⟩ := dPdlogC_bounds
  have hu0 : (0 : ℝ) < u := by linarith
  refine ⟨by unfold L₁₁; exact mul_nonneg hdP0 (Real.exp_pos _).le, ?_⟩
  refine rowBound_key hu0 ?_
  unfold L₁₁
  have hexpb : Real.exp ((P.lam - 2) * Real.log P.Q) * u ≤ 2 := by
    rw [hQeq, ← hueq]
    have h1 : (P.lam - 2) * u ≤ -(0.74 * u) := by nlinarith
    have h2 : Real.exp ((P.lam - 2) * u) ≤ Real.exp (-(0.74 * u)) := Real.exp_le_exp.2 h1
    have he : 0.74 * u + 1 ≤ Real.exp (0.74 * u) := Real.add_one_le_exp _
    have hepos : (0 : ℝ) < Real.exp (0.74 * u) := Real.exp_pos _
    have h3 : Real.exp (-(0.74 * u)) * u ≤ 2 := by
      rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ hepos]; linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hu0.le]
  nlinarith [mul_le_mul_of_nonneg_right hdP1
    (mul_nonneg (Real.exp_pos ((P.lam - 2) * Real.log P.Q)).le hu0.le)]

private theorem row_L12 (F : Family) (P : ParamsQ) (u v : ℝ)
    (hsq8 : Real.sqrt (Real.log P.LB / (P.T * P.LB)) ≤ 2 * v / u) :
    0 ≤ L₁₂ F P ∧ L₁₂ F P ≤ 42 * (v / u) := by
  obtain ⟨hC0, hC20⟩ := Cconst_bounds F
  obtain ⟨hcC0, hcC3⟩ := cCross_bounds
  have hS0 : (0 : ℝ) ≤ Real.sqrt (Real.log P.LB / (P.T * P.LB)) := Real.sqrt_nonneg _
  refine ⟨by
    unfold L₁₂ sensInzone
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0.le) hcC0) hS0, ?_⟩
  unfold L₁₂ sensInzone
  have h1 : 0.35 * F.Cconst * cCross ≤ 21 := by nlinarith
  calc 0.35 * F.Cconst * cCross * Real.sqrt (Real.log P.LB / (P.T * P.LB))
      ≤ 21 * (2 * v / u) := mul_le_mul h1 hsq8 hS0 (by norm_num)
    _ = 42 * (v / u) := by ring



set_option maxHeartbeats 1000000 in
private theorem budgetTotal_le_of_regime_core (F : Family) (r ε Q c : ℝ) (P : ParamsQ)
    (hr : 3 ≤ r) (hε : 0 < ε) (hc : 0 ≤ c)
    (hP : P.Valid) (hQeq : P.Q = Q) (hTeq : P.T = Twin Q r ε) (hlameq : P.lam = F.lamStar)
    (hweq : P.w = wDesign P.LL r)
    (hQ0 : 0 < Q)
    (hu : 8 ≤ Real.log Q)
    (hv : 3 ≤ Real.log (Real.log Q))
    (hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q)
    (hD : P.D0 ≤ c * Real.log Q ^ 2) :
    0 ≤ budgetTotal F P ∧
      budgetTotal F P ≤ (20 * (r + ε) + 6 * c + 200) *
        (Real.log (Real.log Q) / Real.log Q) := by
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hu1 : (1 : ℝ) ≤ Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := by linarith
  have hre : (3 : ℝ) ≤ r + ε := by linarith
  have hvle : Real.log (Real.log Q) ≤ Real.log Q := by
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (r + ε) + 9) hv0.le]
  have hg0 : (0 : ℝ) < Real.log (Real.log Q) / Real.log Q := div_pos hv0 hu0
  -- T
  unfold Twin at hTeq
  have hTpos : (0 : ℝ) < P.T := by rw [hTeq]; exact Real.rpow_pos_of_pos hu0 _
  have hT3 : Real.log Q ^ 3 ≤ P.T := by
    rw [hTeq]
    calc Real.log Q ^ 3 = Real.log Q ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast _ 3).symm
      _ ≤ Real.log Q ^ (r + ε) :=
          Real.rpow_le_rpow_of_exponent_le hu1 (by push_cast; linarith)
  have hlogT : Real.log P.T = (r + ε) * Real.log (Real.log Q) := by
    rw [hTeq]; exact Real.log_rpow hu0 _
  -- ℒ
  have hLLeq : P.LL
      = Real.log Q + (r + ε) * Real.log (Real.log Q) - Real.log (2 * Real.pi) := by
    unfold ParamsQ.LL
    rw [hQeq, Real.log_div (mul_ne_zero (ne_of_gt hQ0) (ne_of_gt hTpos)) (by positivity),
      Real.log_mul (ne_of_gt hQ0) (ne_of_gt hTpos), hlogT]
  have hprod : (r + ε) * Real.log (Real.log Q) ≤ Real.log Q := by
    linarith [mul_le_mul_of_nonneg_right
      (by linarith : r + ε ≤ 2 * (r + ε) + 10) hv0.le]
  have hLLlo : Real.log Q / 2 ≤ P.LL := by
    have h1 : (0 : ℝ) ≤ (r + ε) * Real.log (Real.log Q) :=
      mul_nonneg (by linarith) hv0.le
    linarith [log_two_pi_le_three]
  have hLLhi : P.LL ≤ 2 * Real.log Q := by linarith [log_two_pi_nonneg]
  have hLL0 : (0 : ℝ) < P.LL := by linarith
  have hLL1 : (1 : ℝ) ≤ P.LL := by linarith
  -- L = λℒ
  obtain ⟨hlam1, hlam2⟩ := lamStar_bounds F
  have hLBeq : P.LB = P.lam * P.LL := rfl
  have hlamP1 : (1 : ℝ) ≤ P.lam := by rw [hlameq]; exact hlam1
  have hlamP2 : P.lam ≤ 1.26 := by rw [hlameq]; exact hlam2
  have hLBlo : Real.log Q / 2 ≤ P.LB := by
    rw [hLBeq]; linarith [mul_le_mul_of_nonneg_right hlamP1 hLL0.le]
  have hLBhi : P.LB ≤ 3 * Real.log Q := by
    rw [hLBeq]; linarith [mul_le_mul_of_nonneg_right hlamP2 hLL0.le]
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hLB1 : (1 : ℝ) ≤ P.LB := by linarith
  -- w = 1
  have hwe : P.w = 1 := by
    rw [hweq]
    unfold wDesign wStar
    exact max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))
  -- l(T)
  have hleq : Zeta23.l P.T
      = (r + ε) * Real.log (Real.log Q) - Real.log (2 * Real.pi) := by
    show Real.log (P.T / (2 * Real.pi)) = _
    rw [Real.log_div (ne_of_gt hTpos) (by positivity), hlogT]
  have hllo : (0 : ℝ) ≤ Zeta23.l P.T := by
    rw [hleq]
    linarith [log_two_pi_le_three,
      mul_le_mul hre hv (by norm_num : (0:ℝ) ≤ 3) (by linarith : (0:ℝ) ≤ r + ε)]
  have hlhi : Zeta23.l P.T ≤ (r + ε) * Real.log (Real.log Q) := by
    rw [hleq]; linarith [log_two_pi_nonneg]
  have hlLL : Zeta23.l P.T ≤ P.LL := by rw [hleq, hLLeq]; linarith
  -- δ′
  have hdel : P.deltaPrime = 3 * Real.log (Real.log Q) / Real.log Q := by
    unfold ParamsQ.deltaPrime; rw [hQeq]
  -- D₀
  have hD0pos : (0 : ℝ) < P.D0 := by linarith [hP.two_le_D0]
  -- log ℒ, log L
  have hlogLL0 : (0 : ℝ) ≤ Real.log P.LL := Real.log_nonneg hLL1
  have hlogLL : Real.log P.LL ≤ 2 * Real.log (Real.log Q) := by
    have h1 : Real.log P.LL ≤ Real.log (2 * Real.log Q) := Real.log_le_log hLL0 hLLhi
    have h2 : Real.log (2 * Real.log Q) = Real.log 2 + Real.log (Real.log Q) :=
      Real.log_mul (by norm_num) (ne_of_gt hu0)
    linarith [Real.log_two_lt_d9]
  have hlogLB0 : (0 : ℝ) ≤ Real.log P.LB := Real.log_nonneg hLB1
  have hlogLB : Real.log P.LB ≤ 2 * Real.log (Real.log Q) := by
    have h1 : Real.log P.LB ≤ Real.log (3 * Real.log Q) := Real.log_le_log hLB0 hLBhi
    have h2 : Real.log (3 * Real.log Q) = Real.log 3 + Real.log (Real.log Q) :=
      Real.log_mul (by norm_num) (ne_of_gt hu0)
    have h3 : Real.log 3 ≤ 2 := by
      have : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    linarith
  -- the two `T·(scale)` products
  have hTLpos : (0 : ℝ) < P.T * P.LL := mul_pos hTpos hLL0
  have hTLlo : Real.log Q ^ 4 / 2 ≤ P.T * P.LL := by
    linarith [mul_le_mul hT3 hLLlo (by linarith : (0:ℝ) ≤ Real.log Q / 2) hTpos.le]
  have hu4 : (4096 : ℝ) ≤ Real.log Q ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) hu 4
    norm_num at this; exact this
  have hlogTL0 : (0 : ℝ) ≤ Real.log (P.T * P.LL) := Real.log_nonneg (by linarith)
  have hlogTL : Real.log (P.T * P.LL) ≤ (r + ε + 2) * Real.log (Real.log Q) := by
    rw [Real.log_mul (ne_of_gt hTpos) (ne_of_gt hLL0), hlogT]; linarith
  have hTLBpos : (0 : ℝ) < P.T * P.LB := mul_pos hTpos hLB0
  have hTLBlo : Real.log Q ^ 4 / 2 ≤ P.T * P.LB := by
    linarith [mul_le_mul hT3 hLBlo (by linarith : (0:ℝ) ≤ Real.log Q / 2) hTpos.le]
  -- the rows
  obtain ⟨hz0, hz⟩ := row_zone F P (r + ε) _ _ hu hv hre hdel hllo hlhi hlLL hLLlo hLL0
  obtain ⟨h30, h3⟩ := row_L3 P _ _ hu hv hwe hLBlo
  obtain ⟨h40, h4⟩ := row_L4 P _ _ c hu hv hc hD0pos hD hT3 hTpos
  obtain ⟨h50, h5⟩ := row_L5 P _ _ hu hv hvle hLL0 hLLhi hlogLL0 hlogLL hT3 hTpos
  obtain ⟨h60, h6⟩ := row_L6 F P _ _ hu hv hLLlo hLL0
  obtain ⟨h70, h7⟩ := row_L7 F P (r + ε) _ _ hu hv hre hlogTL0 hlogTL hTLlo hTLpos
  have hsq8 := sqrt8 P _ _ hu hv hlogLB hTLBlo hTLBpos
  obtain ⟨h80, h8⟩ := row_L8 P _ _ hsq8
  obtain ⟨h90, h9⟩ := row_L9 P _ _ hu hv hT3 hTpos
  obtain ⟨h100, h10⟩ := row_L10 P _ _ hu hv hvle hlogLL0 hlogLL hLBlo hLB0
  obtain ⟨h110, h11⟩ := row_L11 P Q _ _ hu hv hQeq rfl hlamP2
  obtain ⟨h120, h12⟩ := row_L12 F P _ _ hsq8
  -- **D35**: the shipped buffer row is `L₄` again (the paper's row, at the sharp density,
  -- assumed via `SharpZeroDensity`), so `row_L4` is consumed directly and the buffer's
  -- per-row constant is `6c·v/u`. D34's extra `πA₀` factor — and with it
  -- `bufferProved_le_L4` — is no longer part of this bound; both are retained below as the
  -- record of what the proved convention would have cost.
  refine ⟨by unfold budgetTotal minorRows; linarith, ?_⟩
  unfold budgetTotal minorRows
  linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 7 * (r + ε) + 39) hg0.le]

/-! ### D27 — the closing clause forces `D₀ = O(ℒ²)`

The analytic core, isolated over bare reals: the closing condition supplies
`c₄·t ≤ B + 2 log(1+M) + 2 log(1+t)` with `t = t_{D₀}` and `B`, `M` both `O(ℒ)`, and the two
logarithms are sublinear in `t`, so `t = O(ℒ)` and `D₀ = A·t² = O(ℒ²)`. -/

private theorem t_bound_of_closing {t M B : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M)
    (h : c4 * t ≤ B + 2 * Real.log (1 + M) + 2 * Real.log (1 + t)) :
    1.38 * t ≤ B + 2 * M + 9 := by
  obtain ⟨hc4lo, -⟩ := c4_bounds
  obtain ⟨-, -, hl100, -⟩ := log_const_bounds
  have h1 : Real.log (1 + M) ≤ M := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + M by linarith); linarith
  have h2 : Real.log (1 + t) ≤ 4 + (1 + t) / 100 := by
    have h3 : Real.log ((1 + t) / 100) ≤ (1 + t) / 100 - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    rw [Real.log_div (ne_of_gt (by linarith : (0:ℝ) < 1 + t)) (by norm_num)] at h3
    linarith
  have h4 : 1.4 * t ≤ c4 * t := mul_le_mul_of_nonneg_right hc4lo ht
  linarith

/-- `budgetTotal_le_of_regime_core` from `DesignOfRecord` (the five pinned scales). -/
private theorem budgetTotal_le_of_regime (F : Family) (r ε Q c : ℝ) (P : ParamsQ)
    (hr : 3 ≤ r) (hε : 0 < ε) (hc : 0 ≤ c)
    (hdes : DesignOfRecord F r ε Q P)
    (hQ0 : 0 < Q)
    (hu : 8 ≤ Real.log Q)
    (hv : 3 ≤ Real.log (Real.log Q))
    (hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q)
    (hD : P.D0 ≤ c * Real.log Q ^ 2) :
    0 ≤ budgetTotal F P ∧
      budgetTotal F P ≤ (20 * (r + ε) + 6 * c + 200) *
        (Real.log (Real.log Q) / Real.log Q) :=
  budgetTotal_le_of_regime_core F r ε Q c P hr hε hc hdes.1 hdes.2.1 hdes.2.2.1 hdes.2.2.2.1
    hdes.2.2.2.2.1 hQ0 hu hv hvu hD

set_option maxHeartbeats 1000000 in
/-- **✅ D27's payoff, pointwise: the pinned closing clause forces `D₀ ≤ 2×10⁴·(log Q)²`.**

This is the statement the vacuous `∃ logPrefactor eta, …` could not deliver. Reading the
boundary half of `ClosingAtDesign` as an upper bound on the *supplied* Gevrey exponent,

  `c₄·√(wD₀/A) = L/2 + log(C_env²·2(ℒ + log 4T)·S(D₀)²/L) + log L`,

every term on the right except `L/2` is `O(log ℒ)` **and** `S(D₀)` depends on `t_{D₀}` only
logarithmically, so `c₄ t_{D₀} ≤ L/2·(1 + o(1))`, i.e. `wD₀ ≍ A(L/2)²/c₄²`; at the clamp
`w = 1` (which is where `r ≥ 3` enters, via `ℒ^{(3−r)/2} ≤ 1`) that is `D₀ = Θ(ℒ²)`.

The constant `2×10⁴` is crude by a factor ≈ 2000: the true design has
`D₀ ≈ e²A L²/16 ≈ 6.1 L² ≈ 9.6 ℒ²`, and at `Q = 10¹⁰⁰` (`ℒ = 247.7`) that is `≈ 5.9×10⁵`
against `T/3 = 6.2×10⁷`. Only the ORDER is used downstream — `budgetTotal_le_of_regime` takes
the constant as a parameter — so nothing is spent sharpening it.

Rule 17: an `O(ℒ²)` **upper** bound on the FREE `P.D0`, derived from §7.2's closing
condition. It is not `D₀ = √T`: at `T = (log Q)^{r+ε}`, `√T = (log Q)^{(r+ε)/2}` is a
different function of `Q`, and for `r + ε > 4` it is the LARGER of the two.

**Stated at the closing EQUALITY'S UPPER HALF WITH A MARGIN `m ≤ ¼ log Q`**
(`hbnd`), so that it serves both `ClosingAtDesign` (`m = 0`, `D0_le_of_design`) and
`ClosingAtDesignM` (`m = ½ log T ≤ ¼ log Q` in the regime, `D0_le_of_designM`); the margin
costs `m/c₄ ≤ 0.18 log Q` on `t`, inside the slack of the crude `t ≤ 32 log Q`. -/
private theorem D0_le_of_closing_margin (F : Family) (r ε Q : ℝ) (P : ParamsQ)
    (hr : 3 ≤ r) (hε : 0 < ε)
    (hP : P.Valid) (hQeq : P.Q = Q) (hTeq : P.T = Twin Q r ε) (hlameq : P.lam = F.lamStar)
    (hweq : P.w = wDesign P.LL r) (hprof : P.prof = F.designProfile)
    (m : ℝ) (hm : m ≤ Real.log Q / 4)
    (hbnd : c4 * tBuffer P ≤ P.LB / 2 + logPrefactorGev P + m + Real.log (P.LB / 1))
    (hQ0 : 0 < Q)
    (hu : 8 ≤ Real.log Q)
    (hv : 3 ≤ Real.log (Real.log Q))
    (hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q) :
    P.D0 ≤ 20000 * Real.log Q ^ 2 := by
  -- ## the regime (the same block as `budgetTotal_le_of_regime`, at the terms needed here)
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hu1 : (1 : ℝ) ≤ Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := by linarith
  have hre : (3 : ℝ) ≤ r + ε := by linarith
  unfold Twin at hTeq
  have hTpos : (0 : ℝ) < P.T := by rw [hTeq]; exact Real.rpow_pos_of_pos hu0 _
  have hu3 : (512 : ℝ) ≤ Real.log Q ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) hu 3
    norm_num at this; exact this
  have hT3 : Real.log Q ^ 3 ≤ P.T := by
    rw [hTeq]
    calc Real.log Q ^ 3 = Real.log Q ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast _ 3).symm
      _ ≤ Real.log Q ^ (r + ε) :=
          Real.rpow_le_rpow_of_exponent_le hu1 (by push_cast; linarith)
  have hlogT : Real.log P.T = (r + ε) * Real.log (Real.log Q) := by
    rw [hTeq]; exact Real.log_rpow hu0 _
  have hLLeq : P.LL
      = Real.log Q + (r + ε) * Real.log (Real.log Q) - Real.log (2 * Real.pi) := by
    unfold ParamsQ.LL
    rw [hQeq, Real.log_div (mul_ne_zero (ne_of_gt hQ0) (ne_of_gt hTpos)) (by positivity),
      Real.log_mul (ne_of_gt hQ0) (ne_of_gt hTpos), hlogT]
  have hprod : (r + ε) * Real.log (Real.log Q) ≤ Real.log Q / 2 := by
    have h1 := mul_le_mul_of_nonneg_right
      (by linarith : 2 * (r + ε) ≤ 2 * (r + ε) + 10) hv0.le
    nlinarith
  have hLLlo : Real.log Q / 2 ≤ P.LL := by
    have h1 : (0 : ℝ) ≤ (r + ε) * Real.log (Real.log Q) := mul_nonneg (by linarith) hv0.le
    linarith [log_two_pi_le_three]
  have hLLhi : P.LL ≤ 2 * Real.log Q := by linarith [log_two_pi_nonneg]
  have hLL0 : (0 : ℝ) < P.LL := by linarith
  have hLL1 : (1 : ℝ) ≤ P.LL := by linarith
  obtain ⟨hlam1, hlam2⟩ := lamStar_bounds F
  have hLBeq : P.LB = P.lam * P.LL := rfl
  have hlamP1 : (1 : ℝ) ≤ P.lam := by rw [hlameq]; exact hlam1
  have hlamP2 : P.lam ≤ 1.26 := by rw [hlameq]; exact hlam2
  have hLBlo : Real.log Q / 2 ≤ P.LB := by
    rw [hLBeq]; linarith [mul_le_mul_of_nonneg_right hlamP1 hLL0.le]
  have hLBhi : P.LB ≤ 3 * Real.log Q := by
    rw [hLBeq]; linarith [mul_le_mul_of_nonneg_right hlamP2 hLL0.le]
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  -- the clamp: `w = 1`, which is where `r ≥ 3` enters
  have hwe : P.w = 1 := by
    rw [hweq]
    unfold wDesign wStar
    exact max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))
  have hw0 : (0 : ℝ) < P.w := by rw [hwe]; norm_num
  have hvle : 16 * Real.log (Real.log Q) ≤ Real.log Q := by
    have h1 := mul_le_mul_of_nonneg_right
      (by linarith : (16 : ℝ) ≤ 2 * (r + ε) + 10) hv0.le
    linarith
  -- ## the constants
  obtain ⟨hAlo, hAhi⟩ := gevreyA_bounds
  obtain ⟨hc4lo, hc4hi⟩ := c4_bounds
  obtain ⟨-, he2hi, -, -, -⟩ := exp_pow_bounds
  obtain ⟨hl4, hl6, hl100, hl1e5⟩ := log_const_bounds
  have hA0 : (0 : ℝ) < gevreyA := by linarith
  have hAne : gevreyA ≠ 0 := ne_of_gt hA0
  have hc40 : (0 : ℝ) < c4 := by linarith
  have hpi6 : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  -- ## `t = t_{D₀} = √(wD₀/A)`
  have hD0nn : (0 : ℝ) ≤ P.D0 := by linarith [hP.two_le_D0]
  have hratio : (0 : ℝ) ≤ P.w * P.D0 / gevreyA :=
    div_nonneg (mul_nonneg hw0.le hD0nn) hA0.le
  have htnn : (0 : ℝ) ≤ tBuffer P := Real.sqrt_nonneg _
  have htsq : tBuffer P ^ 2 = P.w * P.D0 / gevreyA := Real.sq_sqrt hratio
  -- ## the envelope constant: `2 log C_env ≤ 24 + 2 log log Q`
  have hCpos : (0 : ℝ) < CenvDesign P :=
    mul_pos (Real.exp_pos 2) (lt_of_lt_of_le hLB0 (le_max_right _ _))
  have hCle : CenvDesign P ≤ 100000 * Real.log Q := by
    -- `B′ ≤ 40000` at the design (`design_gevreyBprod_le`; needs `ℒ ≥ 4`)
    have hBp : P.gevreyBprod gevreyA gevreyB ≤ 40000 :=
      design_gevreyBprod_le F P hprof hlameq hwe (by linarith)
    have hmax : max (2 * P.gevreyBprod gevreyA gevreyB * P.w) P.LB
        ≤ 80000 + 3 * Real.log Q := by
      refine max_le ?_ (by linarith)
      rw [hwe]; linarith
    have hmaxnn : (0 : ℝ) ≤ max (2 * P.gevreyBprod gevreyA gevreyB * P.w) P.LB :=
      le_trans hLB0.le (le_max_right _ _)
    have h1 : CenvDesign P ≤ 7.4 * (80000 + 3 * Real.log Q) := by
      unfold CenvDesign
      exact mul_le_mul he2hi hmax hmaxnn (by norm_num)
    linarith
  have hlogC : Real.log (CenvDesign P) ≤ 12 + Real.log (Real.log Q) := by
    have h1 : Real.log (CenvDesign P) ≤ Real.log (100000 * Real.log Q) :=
      Real.log_le_log hCpos hCle
    rw [Real.log_mul (by norm_num) (ne_of_gt hu0)] at h1
    linarith
  -- ## the window-log factor: `log(2(ℒ + log 4T)) ≤ 2 + log log Q`
  have hlog4Tnn : (0 : ℝ) ≤ Real.log (4 * P.T) := Real.log_nonneg (by linarith)
  have hlog4T : Real.log (4 * P.T) ≤ 2 + Real.log Q / 2 := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hTpos), hlogT]
    linarith
  have hBpos : (0 : ℝ) < 2 * (P.LL + Real.log (4 * P.T)) := by linarith
  have hBle : 2 * (P.LL + Real.log (4 * P.T)) ≤ 6 * Real.log Q := by linarith
  have hlogB : Real.log (2 * (P.LL + Real.log (4 * P.T)))
      ≤ 2 + Real.log (Real.log Q) := by
    have h1 := Real.log_le_log hBpos hBle
    rw [Real.log_mul (by norm_num) (ne_of_gt hu0)] at h1
    linarith
  -- ## the row-sum factor `S(D₀)`: affine in `t`, so its log is sublinear in `t`
  have hK0 : (0 : ℝ) ≤ P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) :=
    mul_nonneg (div_nonneg hLB0.le (by linarith)) (div_nonneg (by linarith) hw0.le)
  have hKle : P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) ≤ 14 * Real.log Q := by
    have h1 : P.LB / (2 * Real.pi) ≤ 3 * Real.log Q / 6 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * Real.log Q)
        (by linarith : (0:ℝ) ≤ 2 * Real.pi - 6)]
    rw [hwe, div_one]
    calc P.LB / (2 * Real.pi) * (2 * gevreyA)
        ≤ 3 * Real.log Q / 6 * 28 :=
          mul_le_mul h1 (by linarith) (by linarith) (by linarith)
      _ = 14 * Real.log Q := by ring
  have hbrk0 : (0 : ℝ) ≤ 1 / c4 + 1 / c4 ^ 2 :=
    add_nonneg (by positivity) (div_nonneg zero_le_one (sq_nonneg c4))
  have hbrkle : 1 / c4 + 1 / c4 ^ 2 ≤ 1.3 := by
    have h1 : 1 / c4 ≤ 1 / 1.4 := one_div_le_one_div_of_le (by norm_num) hc4lo
    have h2 : (1.4 : ℝ) ^ 2 ≤ c4 ^ 2 := by nlinarith
    have h3 : 1 / c4 ^ 2 ≤ 1 / (1.4 : ℝ) ^ 2 := one_div_le_one_div_of_le (by norm_num) h2
    have h4 : (1 : ℝ) / 1.4 + 1 / (1.4 : ℝ) ^ 2 ≤ 1.3 := by norm_num
    linarith
  have hM0 : (0 : ℝ) ≤ P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (1 / c4 + 1 / c4 ^ 2) :=
    mul_nonneg hK0 hbrk0
  have hMle : P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (1 / c4 + 1 / c4 ^ 2)
      ≤ 19 * Real.log Q := by
    calc P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (1 / c4 + 1 / c4 ^ 2)
        ≤ 14 * Real.log Q * 1.3 := mul_le_mul hKle hbrkle hbrk0 (by linarith)
      _ ≤ 19 * Real.log Q := by linarith
  have hSpos : (0 : ℝ) < rowSumFactor P := by
    have h1 : (0 : ℝ) ≤ P.LB / (2 * Real.pi) * (2 * gevreyA / P.w)
        * (tBuffer P / c4 + 1 / c4 ^ 2) :=
      mul_nonneg hK0 (add_nonneg (div_nonneg htnn hc40.le)
        (div_nonneg zero_le_one (sq_nonneg c4)))
    unfold rowSumFactor; linarith
  have hSle : rowSumFactor P
      ≤ (1 + P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (1 / c4 + 1 / c4 ^ 2))
        * (1 + tBuffer P) := by
    unfold rowSumFactor
    exact rowSum_prod_le hK0 htnn hc40
  have hlogS : Real.log (rowSumFactor P)
      ≤ Real.log (1 + P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (1 / c4 + 1 / c4 ^ 2))
        + Real.log (1 + tBuffer P) := by
    have h1 := Real.log_le_log hSpos hSle
    rwa [Real.log_mul (ne_of_gt (by linarith :
        (0:ℝ) < 1 + P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (1 / c4 + 1 / c4 ^ 2)))
      (ne_of_gt (by linarith : (0:ℝ) < 1 + tBuffer P))] at h1
  -- ## the closing clause, in the shape `t_bound_of_closing` consumes
  unfold logPrefactorGev at hbnd
  rw [div_one] at hbnd
  have hcore : c4 * tBuffer P
      ≤ (P.LB / 2 + 2 * Real.log (CenvDesign P)
          + Real.log (2 * (P.LL + Real.log (4 * P.T))) + m)
        + 2 * Real.log
            (1 + P.LB / (2 * Real.pi) * (2 * gevreyA / P.w) * (1 / c4 + 1 / c4 ^ 2))
        + 2 * Real.log (1 + tBuffer P) := by linarith
  have hkey := t_bound_of_closing htnn hM0 hcore
  -- ## `t = O(log Q)`, hence `D₀ = A t² = O((log Q)²)`
  have ht32 : tBuffer P ≤ 32 * Real.log Q := by linarith
  have hsq : tBuffer P ^ 2 ≤ (32 * Real.log Q) ^ 2 := by nlinarith
  have hD0eq : P.D0 = gevreyA * tBuffer P ^ 2 := by
    rw [htsq, hwe, one_mul]; field_simp
  calc P.D0 = gevreyA * tBuffer P ^ 2 := hD0eq
    _ ≤ 14 * (32 * Real.log Q) ^ 2 :=
        mul_le_mul hAhi hsq (sq_nonneg _) (by norm_num)
    _ ≤ 20000 * Real.log Q ^ 2 := by nlinarith [sq_nonneg (Real.log Q)]

/-- `D0_le_of_closing_margin` at `m = 0`: the original statement, from `DesignOfRecord`. -/
private theorem D0_le_of_design (F : Family) (r ε Q : ℝ) (P : ParamsQ)
    (hr : 3 ≤ r) (hε : 0 < ε)
    (hdes : DesignOfRecord F r ε Q P)
    (hQ0 : 0 < Q)
    (hu : 8 ≤ Real.log Q)
    (hv : 3 ≤ Real.log (Real.log Q))
    (hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q) :
    P.D0 ≤ 20000 * Real.log Q ^ 2 := by
  obtain ⟨hP, hQeq, hTeq, hlameq, hweq, -, -, -, -, hclose, -, hprof⟩ := hdes
  have hbnd : c4 * tBuffer P ≤ P.LB / 2 + logPrefactorGev P + 0 + Real.log (P.LB / 1) := by
    have h := hclose.2; linarith
  exact D0_le_of_closing_margin F r ε Q P hr hε hP hQeq hTeq hlameq hweq hprof 0
    (by linarith) hbnd hQ0 hu hv hvu

/-- `D0_le_of_closing_margin` at `m = marginDesign P = ½ log T = ½(r+ε) log log Q ≤ ¼ log Q`:
the margin design's `D₀ ≤ 2×10⁴·(log Q)²`. -/
private theorem D0_le_of_designM (F : Family) (r ε Q : ℝ) (P : ParamsQ)
    (hr : 3 ≤ r) (hε : 0 < ε)
    (hdes : DesignOfRecordM F r ε Q P)
    (hQ0 : 0 < Q)
    (hu : 8 ≤ Real.log Q)
    (hv : 3 ≤ Real.log (Real.log Q))
    (hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q) :
    P.D0 ≤ 20000 * Real.log Q ^ 2 := by
  obtain ⟨hP, hQeq, hTeq, hlameq, hweq, -, -, -, -, hclose, -, hprof⟩ := hdes
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := by linarith
  have hlogT : Real.log P.T = (r + ε) * Real.log (Real.log Q) := by
    rw [hTeq]; unfold Twin; exact Real.log_rpow hu0 _
  have hm : marginDesign P ≤ Real.log Q / 4 := by
    unfold marginDesign
    rw [hlogT]
    have h1 := mul_le_mul_of_nonneg_right
      (by linarith : 2 * (r + ε) ≤ 2 * (r + ε) + 10) hv0.le
    linarith
  exact D0_le_of_closing_margin F r ε Q P hr hε hP hQeq hTeq hlameq hweq hprof
    (marginDesign P) hm hclose.2 hQ0 hu hv hvu

private theorem isLittleO_loglog_log :
    (fun Q : ℝ => Real.log (Real.log Q)) =o[atTop] (fun Q : ℝ => Real.log Q) :=
  Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop

/-- **✅ D27, in filter form: `D₀ = O((log Q)²)` is DERIVABLE from `DesignOfRecord` alone.**

This is precisely the clause that three separate statements had to hypothesise while
`DesignOfRecord`'s closing condition was the vacuous `∃ logPrefactor eta, …`
(`budgetTotal_isBigO`'s `hD0`; `assembly_at_lamStar`'s checklist item 2;
`payoff_rate_of_designs`'s `hD0`). With the prefactor pinned to LEMMA_QT §QT.b(5)'s
`θ₀^Gev` and the margin at 0 (`ClosingAtDesign`), it is a theorem — `D0_le_of_design`
pointwise, eventually in the regime `8 ≤ log Q`, `3 ≤ log log Q`,
`(2(r+ε)+10)·log log Q ≤ log Q` that `log log Q = o(log Q)` supplies.

Paper §7.2, §10.3.
Depends on: `D0_le_of_design`, `isLittleO_loglog_log`.
Rule 17: an UPPER bound on the FREE `P.D0`, forced by §7.2's margin-0 closing condition, and
emphatically not `D₀ = √T`. -/
theorem design_D0_isBigO (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q)) :
    (fun Q => (design Q).D0) =O[atTop] (fun Q => Real.log Q ^ 2) := by
  have hK : (0 : ℝ) < 2 * (r + ε) + 10 := by linarith
  have hlo := isLittleO_loglog_log.def (c := 1 / (2 * (r + ε) + 10)) (by positivity)
  rw [Asymptotics.isBigO_iff]
  refine ⟨20000, ?_⟩
  filter_upwards [hdesign, hlo, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (3 : ℝ)]
    with Q hdes hlo' hQ0 hu hv'
  have hv : (3 : ℝ) ≤ Real.log (Real.log Q) := hv'
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := by linarith
  have hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0.le,
      abs_of_nonneg hu0.le] at hlo'
    have h2 := mul_le_mul_of_nonneg_left hlo' hK.le
    rw [show (2 * (r + ε) + 10) * (1 / (2 * (r + ε) + 10) * Real.log Q) = Real.log Q by
      field_simp] at h2
    exact h2
  have hD := D0_le_of_design F r ε Q (design Q) hr hε hdes hQ0 hu hv hvu
  have hD0pos : (0 : ℝ) < (design Q).D0 := by linarith [hdes.1.two_le_D0]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0pos.le,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.log Q ^ 2)]
  linarith

/-- **The total is `O(log log Q/log Q)`**, pinned by the two zone terms (paper §10.3,
). The asymptotic constant `s·(r + K) ≈ 3.3` is **computed, not proved**, and is
deliberately NOT in this statement (paper §10.3's remark; §1.5).

**REPAIRED THIS PASS (D14): as frozen the statement was FALSE, because `DesignOfRecord`
does not pin `D₀` from above.** `budgetTotal` contains `L₄ = 6·D₀/T`, so the conclusion
requires `D₀/T = O(log log Q/log Q)`. What `DesignOfRecord` gives is `SideCondD0range`, i.e.
`10L ≤ D₀ ≤ T/3` — an upper bound of `T/3`, at which `L₄ = 2`, a constant. Every other clause
is compatible with that choice: `SideCondWD0` and `SideCondWrange` are lower bounds, and the
closing clause is `∃ logPrefactor eta, 0 < eta ∧ ClosingCondition P logPrefactor eta`, which
is **vacuous** as written — `logPrefactor` is existentially quantified and unconstrained, so
taking it very negative satisfies it for any `P`. So `design Q := (the design with
D₀ := T/3)` witnessed `budgetTotal F (design Q) ≥ 2` eventually, and
`2 ≠ O(log log Q/log Q)`.

**✅ SUPERSEDED IN PART (decision D27): `hD0` is now DERIVABLE.** The statement
below is unchanged — it is the statement of record, and keeping `hD0` explicit keeps visible
that exactly one row (`L₄ = 6D₀/T`) consumes it. But `DesignOfRecord`'s closing clause is no
longer vacuous: it is `ClosingAtDesign`, LEMMA_QT §QT.b(5)'s determinate prefactor at margin
0, which forces `wD₀ ≍ A(L/2)²/c₄²`. So `hD0` follows from `hdesign` by `design_D0_isBigO`,
and `budgetTotal_isBigO_of_design` is this theorem with the hypothesis discharged. The
diagnosis below stands as the record of the defect.

**The repair is the explicit hypothesis `hD0 : D₀ = O(ℒ²)`**, and it is exactly the content
the statement needs and `DesignOfRecord` fails to carry. At the *actual* design of record
the row does decay (`L₄` verified at `0.1202 / 0.0075 / 0.0010`) because §7.2's closing
condition is met **with margin 0**, which forces
`D₀ ≍ A·(L/2)²/(c₄²·w) = Θ(ℒ²)` at the clamp `w = max(1, w*) = 1` for `r ≥ 3`; hence
`D₀/T = Θ(ℒ²/ℒ^{r+ε}) = O(ℒ^{−1−ε}) = o(log ℒ/ℒ)`. Writing it as `(log Q)²` rather than
`P.LL²` costs nothing, since `ℒ = log(QT/2π) ≍ log Q` at `T = (log Q)^{r+ε}`.

**Why not repair `DesignOfRecord` instead.** That is the other honest option, and it is the
better one for the artifact in the long run: either `ClosingCondition` gets LEMMA_QT.b(5)'s
*fixed* prefactor (as `budget_q.closing_margin` uses) instead of an existential one, or
`SideCondD0range` gets a real upper bound. Both re-freeze a definition that every statement
in this file takes as a hypothesis, so both are coordinating calls; and the vacuity errs in
the safe direction everywhere except here (a weaker hypothesis makes the other theorems
*stronger*). The defect is recorded at `DesignOfRecord` and in the module header, and the
one statement it made false is repaired here, locally.

✅ **PROVED.**  Two earlier passes recorded this as "true but not a
fill-level task"; it is the row-by-row asymptotic of all eleven rows against
`T = (log Q)^{r+ε}`, and it is carried out in the `private` block immediately above, whose
docstring tabulates the per-row constants.  The total is `(13(r+ε) + 6c + 161)·log log Q/log Q`
eventually, where `c` is `hD0`'s implied constant; the witness passed to `isBigO_iff` is the
rounder `20(r+ε) + 6|c| + 200`.  `hD0` is consumed in exactly one row — the buffer row —
against `T ≥ (log Q)³`, which is precisely the gap `DesignOfRecord` leaves and this hypothesis
closes.

✅ **RE-PROVED at D35's `budgetTotal`, which is a REVERT to `L₄` (D34 reversed).**  The
statement is unchanged, and so is the proof, in both directions: D34 had charged the buffer at
`bufferRowProved EFChi.A0`, which cost one extra factor (`bufferProved_le_L4`:
`bufferRowProved EFChi.A0 P ≤ 1000·L₄ P` in the regime) and took the buffer row from `6c·v/u`
to `6000c·v/u` and the witness from `20(r+ε) + 6|c| + 200` to `20(r+ε) + 6000|c| + 200`.  D35
charges `L₄` again, so that step drops out, `row_L4` is consumed directly, and both the row and
the witness are back at `6|c|`.  The regime preamble (`budgetTotal_le_of_regime`'s `ℒ`, `L`,
`w = 1`, `l(T)`, `δ′` block) was never touched by either pass, and `hD0` is still consumed in
exactly one row — the buffer.  **The rate class `O(log log Q/log Q)` holds under both
conventions** (D34 checked that, on the paper's range `r + ε > 3`); what D35 recovers is the
finite-Q factor `≈ πA₀ ≈ 255` on that row.  See `budgetTotal` for the full accounting and for
why the sharp density is now a named hypothesis rather than a silently larger charge.

Paper §10.3.
Depends on: every `Lᵢ`.
Rule 17: the design map is quantified over; each `DesignOfRecord` instance carries
`lam = F.lamStar > 1` and a free `D₀`. **`hD0` is an `O(ℒ²)` UPPER bound on `D₀`, which is
what §7.2's margin-0 condition forces — it is emphatically not `D₀ = √T`** (at
`T = (log Q)^{r+ε}`, `√T = (log Q)^{(r+ε)/2}` is a different function of `Q` from `ℒ²`, and
the design of record sits at `D₀ ≈ T/1000` at `Q = 10¹⁰⁰` against `√T ≈ 1.5×10⁴`). -/
theorem budgetTotal_isBigO (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q))
    -- the clause `DesignOfRecord` does not carry: §7.2's closing condition at margin 0.
    (hD0 : (fun Q => (design Q).D0) =O[atTop] (fun Q => Real.log Q ^ 2)) :
    (fun Q => budgetTotal F (design Q))
      =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q) := by
  obtain ⟨c, hcb⟩ := Asymptotics.isBigO_iff.mp hD0
  have hK : (0 : ℝ) < 2 * (r + ε) + 10 := by linarith
  have hlo := isLittleO_loglog_log.def (c := 1 / (2 * (r + ε) + 10)) (by positivity)
  rw [Asymptotics.isBigO_iff]
  refine ⟨20 * (r + ε) + 6 * |c| + 200, ?_⟩
  filter_upwards [hdesign, hcb, hlo, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (3 : ℝ)]
    with Q hdes hb hlo' hQ0 hu hv'
  have hv : (3 : ℝ) ≤ Real.log (Real.log Q) := hv'
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := by linarith
  -- the smallness clause `log log Q = o(log Q)`, at the scale the rows need
  have hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0.le,
      abs_of_nonneg hu0.le] at hlo'
    have h2 := mul_le_mul_of_nonneg_left hlo' hK.le
    rw [show (2 * (r + ε) + 10) * (1 / (2 * (r + ε) + 10) * Real.log Q) = Real.log Q by
      field_simp] at h2
    exact h2
  -- the buffer clause, at the nonnegative constant `|c|`
  have hD : (design Q).D0 ≤ |c| * Real.log Q ^ 2 := by
    have hD0pos : (0 : ℝ) < (design Q).D0 := by linarith [hdes.1.two_le_D0]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0pos.le,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.log Q ^ 2)] at hb
    have : c * Real.log Q ^ 2 ≤ |c| * Real.log Q ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    linarith
  obtain ⟨hpos, hle⟩ :=
    budgetTotal_le_of_regime F r ε Q |c| (design Q) hr hε (abs_nonneg c) hdes hQ0 hu hv
      hvu hD
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos,
    abs_of_nonneg (div_nonneg hv0.le hu0.le)]
  exact hle

/-- **`budgetTotal_isBigO` with `hD0` discharged (D27).** The hypothesis-free form: a design
map is all it takes. `budgetTotal_isBigO` itself is left exactly as it stands — it is the
statement of record, and keeping `hD0` explicit there keeps visible *which* row consumes it
(`L₄ = 6D₀/T`, and only that one). What D27 changed is that the hypothesis is now a theorem,
`design_D0_isBigO`.

Paper §10.3.
Depends on: `budgetTotal_isBigO`, `design_D0_isBigO`. Rule 17: as `budgetTotal_isBigO`. -/
theorem budgetTotal_isBigO_of_design (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q)) :
    (fun Q => budgetTotal F (design Q))
      =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q) :=
  budgetTotal_isBigO F r ε hr hε design hdesign
    (design_D0_isBigO F r ε hr hε design hdesign)

/-- **`D₀ = O((log Q)²)` along every MARGIN design map** — `design_D0_isBigO` for
`DesignOfRecordM`, from `D0_le_of_designM`. Rule 17: as `design_D0_isBigO`. -/
theorem designM_D0_isBigO (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop, DesignOfRecordM F r ε Q (design Q)) :
    (fun Q => (design Q).D0) =O[atTop] (fun Q => Real.log Q ^ 2) := by
  have hK : (0 : ℝ) < 2 * (r + ε) + 10 := by linarith
  have hlo := isLittleO_loglog_log.def (c := 1 / (2 * (r + ε) + 10)) (by positivity)
  rw [Asymptotics.isBigO_iff]
  refine ⟨20000, ?_⟩
  filter_upwards [hdesign, hlo, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (3 : ℝ)]
    with Q hdes hlo' hQ0 hu hv'
  have hv : (3 : ℝ) ≤ Real.log (Real.log Q) := hv'
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := by linarith
  have hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0.le,
      abs_of_nonneg hu0.le] at hlo'
    have h2 := mul_le_mul_of_nonneg_left hlo' hK.le
    rw [show (2 * (r + ε) + 10) * (1 / (2 * (r + ε) + 10) * Real.log Q) = Real.log Q by
      field_simp] at h2
    exact h2
  have hD := D0_le_of_designM F r ε Q (design Q) hr hε hdes hQ0 hu hv hvu
  have hD0pos : (0 : ℝ) < (design Q).D0 := by linarith [hdes.1.two_le_D0]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0pos.le,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.log Q ^ 2)]
  linarith

/-- **`budgetTotal_isBigO_of_design` along every MARGIN design map**: the rows are the same
functions of `(Q, T, λ, w, D₀)`, `D₀ = O(ℒ²)` by `designM_D0_isBigO`, and the regime block of
`budgetTotal_le_of_regime_core` reads only the five pinned scales. Rule 17: as
`budgetTotal_isBigO`. -/
theorem budgetTotal_isBigO_of_designM (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop, DesignOfRecordM F r ε Q (design Q)) :
    (fun Q => budgetTotal F (design Q))
      =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q) := by
  obtain ⟨c, hcb⟩ :=
    Asymptotics.isBigO_iff.mp (designM_D0_isBigO F r ε hr hε design hdesign)
  have hK : (0 : ℝ) < 2 * (r + ε) + 10 := by linarith
  have hlo := isLittleO_loglog_log.def (c := 1 / (2 * (r + ε) + 10)) (by positivity)
  rw [Asymptotics.isBigO_iff]
  refine ⟨20 * (r + ε) + 6 * |c| + 200, ?_⟩
  filter_upwards [hdesign, hcb, hlo, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (3 : ℝ)]
    with Q hdes hb hlo' hQ0 hu hv'
  have hv : (3 : ℝ) ≤ Real.log (Real.log Q) := hv'
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := by linarith
  -- the smallness clause `log log Q = o(log Q)`, at the scale the rows need
  have hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0.le,
      abs_of_nonneg hu0.le] at hlo'
    have h2 := mul_le_mul_of_nonneg_left hlo' hK.le
    rw [show (2 * (r + ε) + 10) * (1 / (2 * (r + ε) + 10) * Real.log Q) = Real.log Q by
      field_simp] at h2
    exact h2
  -- the buffer clause, at the nonnegative constant `|c|`
  have hD : (design Q).D0 ≤ |c| * Real.log Q ^ 2 := by
    have hD0pos : (0 : ℝ) < (design Q).D0 := by linarith [hdes.1.two_le_D0]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0pos.le,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.log Q ^ 2)] at hb
    have : c * Real.log Q ^ 2 ≤ |c| * Real.log Q ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    linarith
  obtain ⟨hpos, hle⟩ :=
    budgetTotal_le_of_regime_core F r ε Q |c| (design Q) hr hε (abs_nonneg c) hdes.1 hdes.2.1
      hdes.2.2.1 hdes.2.2.2.1 hdes.2.2.2.2.1 hQ0 hu hv hvu hD
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos,
    abs_of_nonneg (div_nonneg hv0.le hu0.le)]
  exact hle


/-! ## Two sign facts the assembly join needs

`EFChi.prop31_fam`'s `hκr₂ : 0 ≤ κ_C + r₂` is the only hypothesis of §3's certificate that is
not one of §10's rows, and at `r₂ := rowR2` it is elementary. Both halves are recorded as
named lemmas because both are consumed again by anything that instantiates
`assembly_clauses_at_design`. -/

/-- `0 ≤ κ_C` for both families (`1.2787…` / `1.2900…`).
Rule 17: numerals only. -/
theorem kappaC_nonneg (F : Family) : 0 ≤ F.kappaC := by
  cases F <;>
    norm_num [Family.kappaC, kappaCof, Family.payoff, Pconst, PconstDyadic, PconstEven,
      PconstEvenDyadic]

/-- `0 ≤ r₂` at a valid design point — every summand of `rowR2` is nonnegative.

The only non-obvious one is the zone row `s·(1 − a)` with `a = (1 − δ′)(1 − l/ℒ)`: it needs
`0 ≤ l ≤ ℒ` (from `T ≥ 300` and `Q ≥ 3`, so `0 < log(T/2π) ≤ log(QT/2π)`) and `0 ≤ δ′` (from
`Q ≥ 3`, so `log log Q ≥ 0`), after which `a ≤ 1` — note that `δ′ > 1` is *permitted* here
(`δ′ = 3 log log Q/log Q` peaks at `1.10` near `Q = 15`), which only makes `a` negative and
the row larger. `L₁₁`'s exponent `λ − 2 < 0` plays no role: `exp` is positive either way.

Depends on: `EFChi.LL_pos_of_valid`,
`EFChi.l_pos_of_valid`. Rule 17: uses `Valid.Q_ge`, `Valid.T_ge`, `Valid.one_le_w` and
`lam_pos` only — no λ cap, no `X`, no `D₀`. -/
theorem rowR2_nonneg (F : Family) (P : ParamsQ) (hP : P.Valid) : 0 ≤ rowR2 F P := by
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hLL : (0 : ℝ) < P.LL := EFChi.LL_pos_of_valid hP
  have hLB : (0 : ℝ) < P.LB := EFChi.LB_pos_of_valid hP
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  -- `0 < l ≤ ℒ`, so `1 − l/ℒ ∈ [0,1]`
  have hlLL : Zeta23.l P.T ≤ P.LL := by
    show Real.log (P.T / (2 * Real.pi)) ≤ Real.log (P.Q * P.T / (2 * Real.pi))
    have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
    have hT0 : (0 : ℝ) < P.T := by linarith
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hl0 : (0 : ℝ) < Zeta23.l P.T := EFChi.l_pos_of_valid hP
  have hy0 : (0 : ℝ) ≤ 1 - Zeta23.l P.T / P.LL := by
    rw [sub_nonneg, div_le_one hLL]; exact hlLL
  have hy1 : (1 : ℝ) - Zeta23.l P.T / P.LL ≤ 1 := by
    have : (0 : ℝ) ≤ Zeta23.l P.T / P.LL := by positivity
    linarith
  -- `δ′ ≥ 0`, from `Q ≥ 3 > e`
  have hlogQ : (1 : ℝ) ≤ Real.log P.Q := by
    have h1 := Real.log_le_log (by norm_num : (0:ℝ) < 3) hQ3
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      nlinarith [Real.exp_one_lt_d9]
    linarith
  have hdp : (0 : ℝ) ≤ P.deltaPrime := by
    unfold ParamsQ.deltaPrime
    have : (0 : ℝ) ≤ Real.log (Real.log P.Q) := Real.log_nonneg hlogQ
    positivity
  have hdpc : (0 : ℝ) ≤ dPdlogC := dPdlogC_bounds.1
  have hcc : (0 : ℝ) ≤ cCross := cCross_bounds.1
  have hC : (0 : ℝ) < F.Cconst := (Cconst_bounds F).1
  have hzone : (0 : ℝ) ≤ zoneRowLinear F P := by
    refine zoneRowLinear_nonneg F P ?_
    unfold zoneFactor
    nlinarith [mul_nonneg hdp hy0]
  have hL3 : (0 : ℝ) ≤ L₃ P := by
    unfold L₃ cRamp; have := hP.one_le_w; positivity
  have hL7 : (0 : ℝ) ≤ L₇ F P := by unfold L₇; positivity
  have hL8 : (0 : ℝ) ≤ L₈ P := by unfold L₈; positivity
  have hL10 : (0 : ℝ) ≤ L₁₀ P := by unfold L₁₀; positivity
  have hL11 : (0 : ℝ) ≤ L₁₁ P := by unfold L₁₁; positivity
  have hL12 : (0 : ℝ) ≤ L₁₂ F P := by unfold L₁₂ sensInzone; positivity
  unfold rowR2
  linarith

/-- **🟢 THE ASSEMBLY JOIN AT ONE DESIGN POINT — `assembly_at_lamStar`'s entire eight-clause
body, PROVED (modulo `trace_row`/`frobenius_row`) from explicitly named inputs.**

This is fill pass 9's deliverable, and it is what the two new import edges (`ZetaQ.EFChi`,
`ZetaQ.Tail`) buy. Given a design point `P` at `Qn` it produces

  `∃ r₁ r₂ r₃ r₄ r₅ θ, 0 ≤ θ ∧ (the six row clauses) ∧ bracket ≤ budgetTotal ∧ §3's display`

— i.e. exactly the body of `assembly_at_lamStar` under its `∃ P, DesignOfRecord … ∧ ·`. So
`assembly_at_lamStar` is now **one existential away** from this lemma: what it still needs is
the design point (checklist item 1) plus the six inputs below. It replaces the prose checklist
items 3–5 with a typed signature, which is the whole point: each remaining obligation now has
a machine-checked shape rather than a paragraph.

**The witnesses are the budget's own rows**, `r₁ := rowR1`, `r₂ := rowR2`, `r₃ := rowR3`,
`r₄ := rowR4`, `r₅ := rowR5`, `θ := θ₀`. That choice is FORCED, not convenient — see the
buffer-row finding below.

### What the six inputs are, and whose they are

  1. `hsharp : SharpZeroDensity F Qn P` — **§9's buffer count at the SHARP density.**
     🚩 See the finding below: this, and *not* `buffer_row_proved`, is what the assembly's
     `r₃` slot admits.
  2. `hrvm : FamRvMLower F Qn P` — the family RvM lower bound at `famAvgL` (§12.2 + §9).
     Used twice, by the buffer row and by both pair rows.
  3. `hpair` — §10.5's Prop 3.1 (iv) row: the pair block is absorbed by `L₅ + L₉`. Discharged
     from §7's `ClosingCondition`, which `DesignOfRecord` now carries at a determinate
     prefactor (`ClosingAtDesign`), so this is a §7 computation and no longer a vacuity.
  4. `hZc : EFChi.FamZeroConfig F Qn Zc` and 5. `hB : EFChi.FamGramBridge P F Qn Zc` — §9's
     per-character seam and `Ĝ`-side identification. ⚠ **Not yet dischargeable for
     `Family.qle`**: `EFChi`'s own 🚩 FINDING records that `Family.moduli Family.qle Qn`
     contains `q = 1`, whose unique primitive character has `L = ζ`, while
     `EFChi.rtrace_hatQ_gridGram_eq_Gz` / `frobSq_hatQ_gridGram_eq_Gz` (H2, the Weil explicit
     formula with no pole term) need `1 < q`. `Zc` is abstract here for exactly that reason —
     the `q = 1` member must be handed ζ's own configuration. That residue is `O(Q^{-2})`
     relative and is the last piece of checklist item 3.
  6. `hblock` — §7's per-character tail package at the FREE buffer, `Zeta23.Assembly.
     TailInputsD (Zc q χ) P.toParams P.T P.D0 θ₀` for every member of `𝔉_Q`. This is what
     `ZetaQ.tailInputs_of_profileQ` / `ZetaQ.TailHypQ.tailInputsQ` produce, at a common `θ₀`;
     it carries the design taper's Gevrey profile and §9's local count with it.

`hl : Zeta23.l P.T ≠ 0` and `hB0 : 0 ≤ θ₀/(aL)` — the two side conditions the `ZetaQ.Tail`
exports carry — are **not** hypotheses here: both are discharged from `DesignOfRecord`
(`EFChi.l_ne_zero_of_valid` for the first; `Valid` + `SideCondWrange` +
`Zeta23.Params.three_quarters_le_b`/`b_le_a` give `a ≥ 3/4 > 0`, hence the second).

### 🚩 FINDING: the assembly's `r₃` slot admits ONLY the sharp density, so
### **decision D10's row cannot supply it.**
### ✅ **SETTLED by decision D35: reading (i) below is the decision.**
### `budgetTotal` charges `L₄`, the sharp density is the named hypothesis `SharpZeroDensity`,
### and this lemma's `hsharp` is that assumption, declared. (Fill pass 10 had briefly taken
### reading (ii), by D34; D35 reverses it. Nothing in this lemma's statement or proof moved
### under either decision — it has consumed `buffer_row_sharp`/`hsharp` from the start.)

D10 shipped `buffer_row_proved`, and `buffer_row_sharp`'s docstring used to say in so many
words "do not wire `buffer_row_sharp` into `assembly_at_lamStar`". Both could not hold at once,
and it is D10's side that fails — for a reason that is pure arithmetic on the frozen
definitions, not a proof difficulty:

With `r₁ = rowR1`, `r₂ = rowR2`, `r₄ = rowR4`, `r₅ = rowR5` (which is forced: `trace_row` and
`frobenius_row` deliver exactly those, and *lowering* `r₁` or `r₂` makes their own clauses
harder, not easier), the ring identity inside `propBracket_le_budgetTotal` turns clause 7 into

    3·r₃ + [pair block]  ≤  L₄ + L₅ + L₉,        L₄ = 6D₀/T,  L₅ = 6ℒ log ℒ/T,

so any admissible `r₃` satisfies `r₃ ≤ rowR3 P · (1 + ℒ log ℒ/D₀ + o(1))`. Under D27 the
closing condition forces `wD₀ ≍ A(L/2)²/c₄²`, i.e. `D₀ = Θ(ℒ²)`, so the correction factor is
`1 + O(log ℒ/ℒ) → 1`: **`r₃` must be the sharp density up to `1 + o(1)`.** Against that,
`bufferRowProved A₀ P / L₄ P = π·A₀·(ℒ + log 4T)/ℒ ≈ π·A₀ ≈ 255` *uniformly in Q* (F18's own
figure), so `3·bufferRowProved ≤ L₄ + L₅ + L₉` fails by a factor `≈ 765·D₀/(ℒ log ℒ) → ∞`.
No choice of `A₀ ≥ 1` helps: the factor is increasing in `A₀`.

**This was a coordinating decision, not something this file could repair — and it has been
made: D35 takes reading (i).** The two consistent
readings are: (i) keep `budgetTotal` as frozen (charging `L₄` at the sharp density, which is
what §10.3–§10.4's printed table does) and accept that the assembly consumes
`SharpZeroDensity` — i.e. D10's "the artifact ships the proved constant" does **not** survive
into §10.5; or (ii) re-charge the buffer row of `budgetTotal` at `bufferRowProved`, which
moves §10.4's finite-Q figures (the row grows by `≈ 255×`, from `7.5×10⁻³` to `1.9` at
`Q = 10¹⁰⁰`) but not the rate class, since the row is `Θ(D₀/T) = Θ(ℒ^{2−r−ε})` either way.
Reading (ii) is the one D10's cost claim describes and the one `assembly_at_lamStar`'s own
docstring anticipates ("the budget total consumed here must be recomputed with
`bufferRowProvedQ A₀ P` in place of `L₄ P`") — but it cannot be *executed* while
`budgetTotal` is frozen, because `budgetTotal` is what the assembly's clause 7 names. This
lemma therefore takes reading (i), which is the one that compiles — and **D35 has now adopted
reading (i) as the decision**, for the further reason that (i) is what the paper itself does:
§10.3 prices this row at the sharp density and says so, so assuming it *by name* is faithful
while charging `≈255×` more silently is not.

Paper §3 Prop 3.1, §7.3, §9, §10.3, §10.5.
Depends on: `EFChi.prop31_fam`, `ZetaQ.abs_trGz_sub_trAhat_fam_le_Btr`,
`ZetaQ.sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF`, `trace_row`, `frobenius_row`,
`buffer_row_sharp`, `pair_rows`, `propBracket_le_budgetTotal`, `kappaC_nonneg`,
`rowR2_nonneg`, `NfamQ_nonneg`.
**Rule 17: CLEAN.** Every buffer occurrence is the FREE field `P.D0` (`NIIFamQ`,
`SharpZeroDensity`, `TailInputsD … P.D0`); `λ` enters only as `DesignOfRecord`'s
`P.lam = F.lamStar > 1`; `P.XQ` is compared with nothing. The `ZetaQ.Tail` exports cited are
the `AzD`/`EzD` (free-`D`) ones, never `Az`/`Ez`, and `Zeta23.Assembly.TailInputs` (whose `D`
is `√T`) does not occur. -/
theorem assembly_clauses_at_design (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (θ₀ : ℝ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hθ : 0 ≤ θ₀)
    (hsharp : SharpZeroDensity F Qn P) (hrvm : FamRvMLower F Qn P)
    (hpair : 4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P)
    (hZc : EFChi.FamZeroConfig F Qn Zc) (hB : EFChi.FamGramBridge P F Qn Zc)
    (hblock : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      Zeta23.Assembly.TailInputsD (Zc q χ) P.toParams P.T P.D0 θ₀) :
    ∃ r₁ r₂ r₃ r₄ r₅ θ : ℝ,
      0 ≤ θ ∧
      (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn ∧
      frobSqGhatFam P F Qn ≤ (F.kappaC + r₂) * NfamQ P F Qn ∧
      NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn ∧
      Btr P F Qn θ ≤ r₄ * NfamQ P F Qn ∧
      BF P F Qn θ ≤ r₅ * Real.sqrt (NfamQ P F Qn) ∧
      4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
          + 2 * r₅ * Real.sqrt (F.kappaC + r₂) + r₅ ^ 2 ≤ budgetTotal F P ∧
      (2 - F.kappaC - budgetTotal F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLB : (0 : ℝ) < P.LB := EFChi.LB_pos_of_valid hP
  have hwL' : 8 * P.toParams.w ≤ P.toParams.L P.T := by
    rw [P.toParams_L hl]; exact hwr
  -- the hat normalisation is bounded below by `3/4`, so `a > 0` and `Tail`'s `hB0` is free
  -- (the `Valid` floor `a_ge`)
  have ha0 : (0 : ℝ) < P.aQ := hP.aQ_pos
  have haL : (0 : ℝ) < P.aQ * P.LB := mul_pos ha0 hLB
  have hB0 : (0 : ℝ) ≤ θ₀ / (P.aQ * P.LB) := div_nonneg hθ haL.le
  have hS : (0 : ℝ) ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hBtr0 : (0 : ℝ) ≤ Btr P F Qn θ₀ := by
    show (0 : ℝ) ≤ F.sizeR Qn * θ₀ / (P.aQ * P.LB)
    exact div_nonneg (mul_nonneg hS hθ) haL.le
  have hBF0 : (0 : ℝ) ≤ BF P F Qn θ₀ := by
    show (0 : ℝ) ≤ Real.sqrt (F.sizeR Qn) * θ₀ / (P.aQ * P.LB)
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hθ) haL.le
  have hκ : (0 : ℝ) ≤ F.kappaC + rowR2 F P := by
    linarith [kappaC_nonneg F, rowR2_nonneg F P hP]
  -- §10.3's six rows
  have htr := trace_row F r ε Qn P hdes
  have hfrob := frobenius_row F r ε Qn P hdes
  have hNII := buffer_row_sharp F r ε Qn P hdes hsharp hrvm
  obtain ⟨hBtr', hBF'⟩ := pair_rows F r ε Qn P θ₀ hdes hθ hrvm
  have hbr := propBracket_le_budgetTotal F r ε Qn P θ₀ hdes hθ hpair
  -- §9's family display joined to §7.3's pair split, then Prop 3.1
  have hlast := EFChi.prop31_fam P hP F Qn θ₀ (rowR1 F P) (rowR2 F P) (rowR3 P)
    (rowR4 F P θ₀) (rowR5 F P θ₀) Zc hZc hB hwr
    (abs_trGz_sub_trAhat_fam_le_Btr P F Qn θ₀ Zc hl hblock)
    (sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF P F Qn θ₀ Zc hl hB0 hblock)
    hBtr0 hBF0 hκ htr hfrob hNII hBtr' hBF'
  have hN : (0 : ℝ) ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hbracket : propBracket F P θ₀
      = 4 * rowR1 F P + rowR2 F P + 3 * rowR3 P + 4 * rowR4 F P θ₀
        + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P) + rowR5 F P θ₀ ^ 2 := rfl
  refine ⟨rowR1 F P, rowR2 F P, rowR3 P, rowR4 F P θ₀, rowR5 F P θ₀, θ₀,
    hθ, htr, hfrob, hNII, hBtr', hBF', ?_, ?_⟩
  · rw [← hbracket]; exact hbr
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hN) hlast
    linarith [hbr, hbracket.le, hbracket.ge]

/-! ### §7 → §10.5: THE TAIL CLAUSES OF THE ASSEMBLY, DISCHARGED

`hblock` and `hpair` — checklist items 6 and 4 of `assembly_at_lamStar` — are built here.
Every declaration is proved; `assembly_clauses_at_design_tailfree` is the one exception and
its `sorryAx` is inherited from `assembly_clauses_at_design`, i.e. from `trace_row` and
`frobenius_row`, not from anything below. -/

theorem tailInputsD_mono {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T D θ₁ θ₂ : ℝ}
    (H : Zeta23.Assembly.TailInputsD Z P T D θ₁) (hθ : θ₁ ≤ θ₂)
    (haL : 0 ≤ P.a T * P.L T) :
    Zeta23.Assembly.TailInputsD Z P T D θ₂ := by
  obtain ⟨hEt, ht⟩ := H.tilde
  obtain ⟨B, hB0, hB1, hB2, hB3⟩ := H.hat
  refine ⟨le_trans H.theta_nonneg hθ, ⟨hEt, fun i => (ht i).trans hθ⟩,
    ⟨B, hB0, hB1, hB2, hB3.trans ?_⟩⟩
  exact div_le_div_of_nonneg_right hθ haL

/-! ## 2. `q ≤ Qn` on the family -/

theorem le_of_mem_moduli {F : Family} {Qn q : ℕ} (hq : q ∈ F.moduli Qn) : q ≤ Qn := by
  cases F <;>
    · simp only [Family.moduli, Finset.mem_Icc, Finset.mem_Ioc] at hq
      omega

/-! ## 3. `hblock` at a COMMON `θ₀` -/

theorem famTailInputsD_at (F : Family) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hQn : 2 ≤ Qn) (hP : P.Valid) (hwr : SideCondWrange P)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0
        (theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)) := by
  classical
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hw : (0 : ℝ) < P.w := EFChi.w_pos_of_valid hP
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hwL' : 8 * P.toParams.w ≤ P.toParams.L P.T := by rw [hLb]; exact hwrange
  have hLB8 : (8 : ℝ) ≤ P.LB := by linarith
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hL2 : (2 : ℝ) ≤ P.toParams.L P.T := by rw [hLb]; linarith
  have hL0 : (0 : ℝ) < P.toParams.L P.T := by linarith
  -- `a > 0` is the `Valid` floor `a_ge`
  have ha : (0 : ℝ) < P.toParams.a P.T := hP.aQ_pos
  have haL : (0 : ℝ) ≤ P.toParams.a P.T * P.toParams.L P.T := le_of_lt (mul_pos ha hL0)
  have hD1 : (1 : ℝ) ≤ P.D0 := one_le_D0Q hP
  have hT : Zeta23.Tail.T₀ ≤ P.T := hP.T_ge
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hA : (0 : ℝ) < gevreyA := hϱ.A_pos
  have hCenv0 : (0 : ℝ) ≤ CenvDesign P := by
    have h : (0 : ℝ) ≤ max (2 * P.gevreyBprod gevreyA gevreyB * P.w) P.LB :=
      le_trans hLB0.le (le_max_right _ _)
    have := (Real.exp_pos (2 : ℝ)).le
    exact mul_nonneg this h
  intro q hq χ hχ
  have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
  have : NeZero q := ⟨by omega⟩
  have hprim : χ.IsPrimitive := EFChi.isPrimitive_of_mem_primitiveChars hχ
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1.le
  have hqQ : (q : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast le_of_mem_moduli hq
  have hlocZ : ∀ t : ℝ, ((EFChi.famZc q χ).N t (t + 1) : ℝ)
      ≤ A₀ * Real.log ((q : ℝ) * (|t| + 3)) := by
    intro t
    rw [EFChi.famZc_eq_ZChi hq1 hprim]
    have h : (ZChi hq1 hprim).N t (t + 1) = Zeta23.ThmE.NcountL χ t (t + 1) :=
      Zeta23.ThmE.LZeros_N (Zeta23.ThmE.LSeam_of hq1 hprim) t (t + 1)
    rw [h]
    exact hloc q χ hq1 hprim t
  -- the q-uniform tail bundle from the PRODUCT window's §7.1 envelope
  -- (`ParamsQ.Valid.norm_phiHat_le_gevrey`, constant `B′ = gevreyBprod A B`), through
  -- `TailHypQ.of_envelope` instead of `TailHypQ.of_profile` (which needed `toParams.ValidQ`).
  have H : TailHypQ (EFChi.famZc q χ) P.toParams P.T A₀ gevreyA
      (Real.exp 2 * max (2 * P.gevreyBprod gevreyA gevreyB * P.toParams.w) (P.toParams.L P.T))
      P.D0 (q : ℝ) :=
    TailHypQ.of_envelope hϱ.A_pos (hP.gevreyBprod_pos hϱ.A_pos hϱ.B_pos) hw hT hL2 hA₀ hqR
      hlocZ hD1 (fun z => by rw [hLb]; exact hP.norm_phiHat_le_gevrey hwrange hϱ z)
  rw [hLb] at H
  have hTI := H.tailInputsQ ha (fun z => Zeta23.Params.phiHat_conj z)
  refine tailInputsD_mono hTI ?_ haL
  exact theta0Q_le_theta0Fam hL0 hqR hqQ hCenv0 hA₀ hw hA (by linarith) hT

/-! ## 4. `θ₀_fam ≥ 0` -/

theorem theta0Fam_nonneg (P : ParamsQ) (A₀ Cenv Qr : ℝ)
    (hP : P.Valid) (hwr : SideCondWrange P) (hA₀ : 1 ≤ A₀) (hCenv : 0 ≤ Cenv)
    (hQr : 1 ≤ Qr) :
    0 ≤ theta0Fam P.toParams P.T A₀ gevreyA Cenv P.D0 Qr := by
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hw : (0 : ℝ) < P.w := EFChi.w_pos_of_valid hP
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hL0 : (0 : ℝ) < P.toParams.L P.T := by rw [hLb]; exact hLB0
  have hA : (0 : ℝ) < gevreyA := by unfold gevreyA; positivity
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hD1 : (1 : ℝ) ≤ P.D0 := one_le_D0Q hP
  have hb : 0 < P.toParams.w / gevreyA := div_pos hw hA
  have hc : (0 : ℝ) < 2 * (2 / Real.exp 1) := by positivity
  have hB1 : (1 : ℝ) ≤ 2 * P.T + 4 := by linarith
  have hside : 0 ≤ Zeta23.Tail.sideW (P.toParams.L P.T) (P.toParams.w / gevreyA)
      (2 * (2 / Real.exp 1)) (2 * P.T + 4) P.D0 :=
    Zeta23.Tail.sideW_nonneg hL0.le hb hc hB1 (by linarith)
  have hfac : (0 : ℝ) ≤ 1 + Real.log Qr / Real.log (2 * P.T + 4) := by
    have h : (0 : ℝ) ≤ Real.log Qr / Real.log (2 * P.T + 4) :=
      div_nonneg (Real.log_nonneg hQr) (Real.log_nonneg hB1)
    linarith
  have hK : (0 : ℝ) ≤ Real.exp (P.toParams.L P.T / 4) * Cenv := by positivity
  unfold theta0Fam theta0Q sideWQ
  positivity

/-! ## 5. `hblock` in the existential shape `assembly_clauses_at_design` wants -/

theorem exists_famTailInputsD (F : Family) (Qn : ℕ) (P : ParamsQ)
    (hQn : 2 ≤ Qn) (hP : P.Valid) (hwr : SideCondWrange P)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) :
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧ ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀ := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  refine ⟨theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ), ?_,
    famTailInputsD_at F Qn P A₀ hQn hP hwr hϱ hA₀ hloc⟩
  have hw : (0 : ℝ) < P.w := EFChi.w_pos_of_valid hP
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hCenv0 : (0 : ℝ) ≤ CenvDesign P := by
    have h : (0 : ℝ) ≤ max (2 * P.gevreyBprod gevreyA gevreyB * P.w) P.LB :=
      le_trans hLB0.le (le_max_right _ _)
    exact mul_nonneg (Real.exp_pos (2 : ℝ)).le h
  exact theta0Fam_nonneg P A₀ (CenvDesign P) (Qn : ℝ) hP hwr hA₀ hCenv0
    (by exact_mod_cast Nat.one_le_of_lt hQn)

/-! ## 6. `hpair`: the pair block is absorbed once `θ₀` is small -/

private theorem pair_arith {θ m X k Lr : ℝ} (hθ : 0 ≤ θ) (hm : 0 < m) (hX : 1 ≤ X)
    (hone : θ ≤ m * Real.sqrt X)
    (hsmall : θ * (5 + 2 * k) ≤ m * Real.sqrt X * Lr) :
    4 * (θ / (m * X)) + 2 * (θ / (m * Real.sqrt X)) * k
        + (θ / (m * Real.sqrt X)) ^ 2 ≤ Lr := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt X := by
    have h := Real.sqrt_le_sqrt hX
    simpa using h
  have hs0 : (0 : ℝ) < Real.sqrt X := by linarith
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsX : Real.sqrt X ≤ X := by nlinarith
  have hms : (0 : ℝ) < m * Real.sqrt X := mul_pos hm hs0
  have hmX : (0 : ℝ) < m * X := mul_pos hm hX0
  have hu0 : (0 : ℝ) ≤ θ / (m * Real.sqrt X) := div_nonneg hθ hms.le
  have hu1 : θ / (m * Real.sqrt X) ≤ 1 := (div_le_one hms).2 hone
  have hu2 : (θ / (m * Real.sqrt X)) ^ 2 ≤ θ / (m * Real.sqrt X) := by nlinarith
  have huL : θ / (m * Real.sqrt X) * (5 + 2 * k) ≤ Lr := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hms, mul_comm Lr]
    exact hsmall
  have h4 : θ / (m * X) ≤ θ / (m * Real.sqrt X) := by
    rw [div_le_div_iff₀ hmX hms]
    nlinarith [mul_le_mul_of_nonneg_left hsX (mul_nonneg hθ hm.le)]
  nlinarith [h4, hu2, huL, hu0]

/-- `1 ≤ (T/2π)·⟨ℒ⟩_low` at any valid design point. -/
theorem one_le_TfamAvg (F : Family) (P : ParamsQ) (hP : P.Valid) :
    (1 : ℝ) ≤ P.T / (2 * Real.pi) * famAvgLlow F P := by
  have hQ : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hQT : (900 : ℝ) ≤ P.Q * P.T := by nlinarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hLL : (1 : ℝ) ≤ P.LL := by
    unfold ParamsQ.LL
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    have h1 : Real.exp 1 * (2 * Real.pi) ≤ 2.7182818286 * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right he.le (by positivity)
    have h2 : (2.7182818286 : ℝ) * (2 * Real.pi) ≤ 2.7182818286 * 8 := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsh := conductorShift_le_half F
  have hlow : (0.87 : ℝ) ≤ famAvgLlow F P := by
    unfold famAvgLlow famAvgL rvmSlack
    linarith
  have hTpi : (37 : ℝ) ≤ P.T / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hstep := mul_le_mul_of_nonneg_right hTpi (by linarith : (0 : ℝ) ≤ famAvgLlow F P)
  linarith

/-- **§10.5's `hpair` from a smallness bound on `θ₀`.** -/
theorem pair_absorbed_of_theta_small (F : Family) (P : ParamsQ) (θ₀ : ℝ)
    (hP : P.Valid) (hwr : SideCondWrange P) (hθ : 0 ≤ θ₀)
    (hone : θ₀ ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P))
    (hsmall : θ₀ * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P))
        ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) * (L₅ P + L₉ P)) :
    4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P := by
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hwL' : 8 * P.toParams.w ≤ P.toParams.L P.T := by rw [hLb]; exact hwrange
  -- `a > 0` is the `Valid` floor `a_ge`
  have ha0 : (0 : ℝ) < P.aQ := hP.aQ_pos
  have hm0 : (0 : ℝ) < P.aQ * P.LB := mul_pos ha0 hLB0
  unfold rowR4 rowR5
  exact pair_arith hθ hm0 (one_le_TfamAvg F P hP) hone hsmall

/-! ## 7. `hblock` + `hpair` together, at the canonical `famZc` -/

theorem tail_clauses_at_design (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hQn : 2 ≤ Qn) (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hone : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
        ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P))
    (hsmall : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
          * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P))
        ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P)) :
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
      (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) ∧
      (∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
        Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hw : (0 : ℝ) < P.w := EFChi.w_pos_of_valid hP
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hCenv0 : (0 : ℝ) ≤ CenvDesign P :=
    mul_nonneg (Real.exp_pos (2 : ℝ)).le (le_trans hLB0.le (le_max_right _ _))
  have hθ0 : 0 ≤ theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) :=
    theta0Fam_nonneg P A₀ (CenvDesign P) (Qn : ℝ) hP hwr hA₀ hCenv0
      (by exact_mod_cast Nat.one_le_of_lt hQn)
  exact ⟨_, hθ0,
    pair_absorbed_of_theta_small F P _ hP hwr hθ0 hone hsmall,
    famTailInputsD_at F Qn P A₀ hQn hP hwr hϱ hA₀ hloc⟩

/-! ## 8. The eight-clause body of `assembly_at_lamStar`, with §7's two clauses discharged -/

theorem assembly_clauses_at_design_tailfree (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (A₀ : ℝ) (hQn : 2 ≤ Qn) (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hone : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
        ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P))
    (hsmall : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
          * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P))
        ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P))
    (hsharp : SharpZeroDensity F Qn P) (hrvm : FamRvMLower F Qn P) :
    ∃ r₁ r₂ r₃ r₄ r₅ θ : ℝ,
      0 ≤ θ ∧
      (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn ∧
      frobSqGhatFam P F Qn ≤ (F.kappaC + r₂) * NfamQ P F Qn ∧
      NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn ∧
      Btr P F Qn θ ≤ r₄ * NfamQ P F Qn ∧
      BF P F Qn θ ≤ r₅ * Real.sqrt (NfamQ P F Qn) ∧
      4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
          + 2 * r₅ * Real.sqrt (F.kappaC + r₂) + r₅ ^ 2 ≤ budgetTotal F P ∧
      (2 - F.kappaC - budgetTotal F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  obtain ⟨θ₀, hθ, hpair, hblock⟩ :=
    tail_clauses_at_design F r ε Qn P A₀ hQn hdes hϱ hA₀ hloc hone hsmall
  exact assembly_clauses_at_design F r ε Qn P θ₀ EFChi.famZc hdes hθ hsharp hrvm hpair
    (EFChi.famZeroConfig_famZc F Qn hQn)
    (EFChi.famGramBridge_famZc P hP F Qn hQn hwr) hblock

/-! ## 9. `ClosingAtDesign` ⟹ `θ₀_fam ≤ 1/L` -/

theorem theta0Fam_le_of_design (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hpre0 : 0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
    (hpre : Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        ≤ logPrefactorGev P) :
    theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) ≤ 1 / P.LB := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hcl : ClosingAtDesign P := hdes.2.2.2.2.2.2.2.2.2.1
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hww : P.toParams.w = P.w := rfl
  have hw : (0 : ℝ) < P.w := EFChi.w_pos_of_valid hP
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hL0 : (0 : ℝ) < P.toParams.L P.T := by rw [hLb]; exact hLB0
  have hA : (0 : ℝ) < gevreyA := by unfold gevreyA; positivity
  have hD0 : (0 : ℝ) ≤ P.D0 := by linarith [one_le_D0Q hP]
  have hcc : P.LB / 2 + logPrefactorGev P + Real.log (P.LB / 1)
      ≤ c4 * Real.sqrt (P.w * P.D0 / gevreyA) := hcl.1
  have hc4 : c4 = 4 / Real.exp 1 := rfl
  rw [hc4] at hcc
  have hclose : P.toParams.L P.T / 2
        + Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        + Real.log (P.toParams.L P.T / 1)
      ≤ (4 / Real.exp 1) * Real.sqrt (P.toParams.w * P.D0 / gevreyA) := by
    rw [hLb, hww]
    linarith
  have h := theta0Q_le_of_closing (η := 1) hL0 one_pos hw hA hD0 hpre0 hclose
  rw [hLb] at h
  exact h

/-! ## 10. `hone` is free at any valid design point -/

theorem inv_LB_le_aL_sqrt (F : Family) (P : ParamsQ) (hP : P.Valid) (hwr : SideCondWrange P) :
    1 / P.LB ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) := by
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB8 : (8 : ℝ) ≤ P.LB := by linarith
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hwL' : 8 * P.toParams.w ≤ P.toParams.L P.T := by rw [hLb]; exact hwrange
  -- the `Valid` floor `a_ge`
  have ha : (3 : ℝ) / 4 ≤ P.aQ := hP.a_ge
  have hs1 : (1 : ℝ) ≤ Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) := by
    have h := Real.sqrt_le_sqrt (one_le_TfamAvg F P hP)
    simpa using h
  have t1 : (3 : ℝ) / 4 * 8 ≤ P.aQ * P.LB :=
    mul_le_mul ha hLB8 (by norm_num) (by linarith)
  have t2 : (3 : ℝ) / 4 * 8 * 1
      ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) :=
    mul_le_mul t1 hs1 (by norm_num) (by linarith)
  rw [div_le_iff₀ hLB0]
  nlinarith [t2, hLB8]

/-! ## 11. The two §7 clauses from the design's OWN closing condition -/

theorem tail_clauses_at_design_of_closing (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (A₀ : ℝ) (hQn : 2 ≤ Qn) (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hpre0 : 0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
    (hpre : Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        ≤ logPrefactorGev P)
    (hregime : 5 + 2 * Real.sqrt (F.kappaC + rowR2 F P)
        ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P)) :
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
      (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) ∧
      (∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
        Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hθle := theta0Fam_le_of_design F r ε Qn P A₀ hdes hpre0 hpre
  have hk : (0 : ℝ) ≤ Real.sqrt (F.kappaC + rowR2 F P) := Real.sqrt_nonneg _
  refine tail_clauses_at_design F r ε Qn P A₀ hQn hdes hϱ hA₀ hloc
    (le_trans hθle (inv_LB_le_aL_sqrt F P hP hwr)) ?_
  have hstep : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
        * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P))
      ≤ 1 / P.LB * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P)) :=
    mul_le_mul_of_nonneg_right hθle (by linarith)
  refine le_trans hstep ?_
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hLB0]
  have heq : P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
        * (L₅ P + L₉ P) * P.LB
      = P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
        * (L₅ P + L₉ P) := by ring
  rw [heq]
  exact hregime

/-! # §10.5 — the assembly, Theorem 1 and Corollary 2

Paper §10.5, verbatim:

> Combining §§4–9 into Proposition 3.1's hypotheses at λ = λ* proves Theorem 1 at each fixed
> ε > 0, with the rate carried by the budget rows rᵢ — **no ε-limit is taken**, and Q₀(ε) is
> the largest of §§5–9's thresholds; the dyadic corollary runs the same argument at
> C = 2π⁴/27 (its finite-Q arithmetic from the measured dyadic P(δ) secant at the design
> offset — 0.64 at the 10¹⁰⁰ offset; the small-δ secant 0.5485 is not usable at finite Q).

Fidelity consequence: the rate comes from Prop 3.1's **quantitative** fixed-
`(Q,T)` conclusion at the budget rows, NOT from [R]'s `∀ ε > 0, ∃ T₀` filter form. See also
`ZetaQ.h1_block_free` (the per-block H1 display, proved with no rank–trace hypothesis; the
former `h1_block_fixed_free` is `@[deprecated]` under D28) and the CLOSED open question Q2
in `ZetaQ/Certificate.lean`. -/

/-! ## 🟢 §10.3 — THE DESIGN POINT EXISTS (`assembly_at_lamStar`'s checklist item 1)

The construction obligation D27 created and that no section owned: `∃ P, DesignOfRecord F r ε Q P`
at every large `Q`. Since D27 the closing clause is an **equality** (`ClosingAtDesign`, margin
0), so the construction has to *solve*

    c₄·√(w·D₀/A)  =  L/2 + logPrefactorGev P + log L

for `D₀`, and then check the five side conditions at the root. That is an intermediate-value
argument in one variable, exactly as `ClosingAtDesign`'s satisfiability note describes, and it
is carried out below in four pieces:

  * `exists_root_of_signs` — the IVT itself, over bare reals. The gap
    `g(D) = c₄√(wD/A) − Nc − 2 log S(D)` is continuous (`S(D) ≥ 1 > 0`, so `log ∘ S` is), so
    `g(a) ≤ 0 ≤ g(b)` gives a root in `[a,b]` by `intermediate_value_Icc`.
  * `closingAtDesign_of_root` — the root equation IS `ClosingAtDesign` (the `−log L` of
    `logPrefactorGev` cancels the `+log(L/1)` of `ClosingCondition`, leaving
    `needed = L/2 + 2 log C_env + log(2(ℒ + log 4T)) + 2 log S`).
  * `design_low_sign` / `design_high_sign` — the two endpoint signs at `a = 10L`, `b = T/3`,
    the interval `SideCondD0range` allows. At the low end `c₄√(10L/A) ≤ 1.5√L ≤ L/2 + 4` while
    `2 log C_env ≥ 4` (as `C_env ≥ e²`), so `g(10L) ≤ 0` for every `L ≥ 100` — *no* regime
    hypothesis is needed there. At the high end, in the regime `log Q ≥ 200` and
    `16 log log Q ≤ log Q`, the needed side is `≤ 1.5u + 5 log u + 60 ≤ 2.12u` while the
    supplied side is `c₄√(T/3A) ≥ 0.2√T ≥ 2.8u` (using `T ≥ u³`), so `g(T/3) ≥ 0`.
  * `exists_designOfRecord_at` / `exists_designOfRecord` — the assembly: `w = 1` (the clamp,
    which is where `r ≥ 3` enters, via `ℒ^{(3−r)/2} ≤ 1`), `λ = λ*`, `T = (log Q)^{r+ε}`, the
    taper from `Zeta23.exists_taperProfile`, `D₀` the root, and then `Valid`,
    `SideCondWrange`, `SideCondWD0`, `SideCondD0range`, `SideCondTfloor` all read off the
    regime.

The root sits at `wD₀ ≍ A(L/2)²/c₄² ≈ 6.1L²`, which is where `design_D0_isBigO` picks it up —
so this lemma and D27's `D₀ = O(ℒ²)` are the two halves of the same fact.

**`Zones.exists_designFamily_regime` is not reusable** and was not reused: its witness
(`λ = 1`, `w = 1`, `D₀ = 2`) fails `SideCondD0range` (`10L ≤ D₀`), `SideCondWD0`
(`e²A ≈ 98 ≤ wD₀`) and `ClosingAtDesign` alike.

**Rule 17: CLEAN.** `λ = F.lamStar > 1`; `D₀` is the IVT root, an `Θ(ℒ²)` quantity pinned by
the closing equality and compared with `10L` and `T/3` only — `Real.sqrt P.T` appears in the
proof of the *high endpoint sign* purely as a majorant of `√(T/3A)`, never as a value for
`D₀`. `X` does not occur. -/

/-- **The intermediate-value solve for the buffer, over bare reals.**
`Nc` is the `D₀`-independent part of the needed side, `Kc` the row-sum factor's coefficient,
`wv` the ramp width, `[a,b]` the bracket. Continuity is the only analytic input; the two
signs are the caller's.
Rule 17: `wv`, `Kc`, `Nc`, `a`, `b` are bare reals. -/
private theorem exists_root_of_signs (wv Kc Nc a b : ℝ)
    (hKc : 0 ≤ Kc) (hab : a ≤ b)
    (hlow : c4 * Real.sqrt (wv * a / gevreyA) ≤ Nc)
    (hhigh : Nc + 2 * Real.log (1 + Kc * (Real.sqrt (wv * b / gevreyA) / c4 + 1 / c4 ^ 2))
        ≤ c4 * Real.sqrt (wv * b / gevreyA)) :
    ∃ D, a ≤ D ∧ D ≤ b ∧
      c4 * Real.sqrt (wv * D / gevreyA)
        = Nc + 2 * Real.log (1 + Kc * (Real.sqrt (wv * D / gevreyA) / c4 + 1 / c4 ^ 2)) := by
  obtain ⟨hc4lo, hc4hi⟩ := c4_bounds
  have hc40 : (0 : ℝ) < c4 := by linarith
  have hSge : ∀ D : ℝ,
      (1 : ℝ) ≤ 1 + Kc * (Real.sqrt (wv * D / gevreyA) / c4 + 1 / c4 ^ 2) := by
    intro D
    have hs : (0 : ℝ) ≤ Real.sqrt (wv * D / gevreyA) := Real.sqrt_nonneg _
    have h1 : (0 : ℝ) ≤ Real.sqrt (wv * D / gevreyA) / c4 := div_nonneg hs hc40.le
    have h2 : (0 : ℝ) ≤ 1 / c4 ^ 2 := by positivity
    nlinarith [mul_nonneg hKc (by linarith : (0:ℝ) ≤ Real.sqrt (wv * D / gevreyA) / c4
      + 1 / c4 ^ 2)]
  have hsq : Continuous fun D : ℝ => Real.sqrt (wv * D / gevreyA) :=
    Real.continuous_sqrt.comp ((continuous_const.mul continuous_id).div_const _)
  have hcont : Continuous fun D : ℝ =>
      c4 * Real.sqrt (wv * D / gevreyA)
        - (Nc + 2 * Real.log
            (1 + Kc * (Real.sqrt (wv * D / gevreyA) / c4 + 1 / c4 ^ 2))) := by
    refine (continuous_const.mul hsq).sub (continuous_const.add (continuous_const.mul ?_))
    refine Continuous.log ?_ (fun D => ne_of_gt (lt_of_lt_of_le zero_lt_one (hSge D)))
    exact continuous_const.add (continuous_const.mul ((hsq.div_const _).add continuous_const))
  have h1 : c4 * Real.sqrt (wv * a / gevreyA)
      - (Nc + 2 * Real.log
          (1 + Kc * (Real.sqrt (wv * a / gevreyA) / c4 + 1 / c4 ^ 2))) ≤ 0 := by
    have := Real.log_nonneg (hSge a); linarith
  have h2 : (0 : ℝ) ≤ c4 * Real.sqrt (wv * b / gevreyA)
      - (Nc + 2 * Real.log
          (1 + Kc * (Real.sqrt (wv * b / gevreyA) / c4 + 1 / c4 ^ 2))) := by linarith
  obtain ⟨D, hDmem, hDval⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨h1, h2⟩
  refine ⟨D, hDmem.1, hDmem.2, ?_⟩
  have hz : c4 * Real.sqrt (wv * D / gevreyA)
      - (Nc + 2 * Real.log
          (1 + Kc * (Real.sqrt (wv * D / gevreyA) / c4 + 1 / c4 ^ 2))) = 0 := hDval
  linarith

/-- **The margin-0 closing clause is exactly the root equation.** `logPrefactorGev` carries
`− log L` and `ClosingCondition … 1` supplies `+ log(L/1)`, so the two cancel and
`ClosingAtDesign P` says precisely

    c₄·t_{D₀}  =  L/2 + 2 log C_env + log(2(ℒ + log 4T)) + 2 log S(D₀),

an equality written as two inequalities. Rule 17: CLEAN. -/
theorem closingAtDesign_of_root (P : ParamsQ)
    (hroot : c4 * Real.sqrt (P.w * P.D0 / gevreyA)
      = P.LB / 2 + 2 * Real.log (CenvDesign P)
        + Real.log (2 * (P.LL + Real.log (4 * P.T)))
        + 2 * Real.log (rowSumFactor P)) :
    ClosingAtDesign P := by
  have hLB : Real.log (P.LB / 1) = Real.log P.LB := by rw [div_one]
  constructor
  · show P.LB / 2 + logPrefactorGev P + Real.log (P.LB / 1)
        ≤ c4 * Real.sqrt (P.w * P.D0 / gevreyA)
    unfold logPrefactorGev
    rw [hLB]; linarith
  · show c4 * tBuffer P ≤ P.LB / 2 + logPrefactorGev P + Real.log (P.LB / 1)
    unfold logPrefactorGev tBuffer
    rw [hLB]; linarith

/-- The two joined: a buffer inside `[a,b]` at which `ClosingAtDesign` holds.
Rule 17: as `exists_root_of_signs`. -/
private theorem exists_closing_in (P₀ : ParamsQ) (a b : ℝ) (hab : a ≤ b)
    (hKc : 0 ≤ P₀.LB / (2 * Real.pi) * (2 * gevreyA / P₀.w))
    (hlow : c4 * Real.sqrt (P₀.w * a / gevreyA)
        ≤ P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
          + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T))))
    (hhigh : P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
          + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T)))
          + 2 * Real.log (rowSumFactor { P₀ with D0 := b })
        ≤ c4 * Real.sqrt (P₀.w * b / gevreyA)) :
    ∃ D, a ≤ D ∧ D ≤ b ∧ ClosingAtDesign { P₀ with D0 := D } := by
  obtain ⟨D, hDa, hDb, hroot⟩ := exists_root_of_signs P₀.w
    (P₀.LB / (2 * Real.pi) * (2 * gevreyA / P₀.w))
    (P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
      + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T))))
    a b hKc hab hlow hhigh
  exact ⟨D, hDa, hDb, closingAtDesign_of_root { P₀ with D0 := D } hroot⟩

/-- **The low endpoint: `g(10L) ≤ 0`, with no regime hypothesis beyond `L, ℒ ≥ 100`.**
`c₄√(10L/A) ≤ 1.5√L ≤ L/2 + 4` (the discriminant of `x²/2 − 1.5x + 4` is negative), and the
needed side already carries `2 log C_env ≥ 4` because `C_env ≥ e²·max(2Bw, L) ≥ e²`. -/
private theorem design_low_sign (Bp LB LL T : ℝ)
    (hLB : 100 ≤ LB) (hLL : 100 ≤ LL) (hT1 : 1 ≤ 4 * T) :
    c4 * Real.sqrt (1 * (10 * LB) / gevreyA)
      ≤ LB / 2 + 2 * Real.log (Real.exp 2 * max (2 * Bp * 1) LB)
        + Real.log (2 * (LL + Real.log (4 * T))) := by
  obtain ⟨hA13, hA14⟩ := gevreyA_bounds
  obtain ⟨hc4lo, hc4hi⟩ := c4_bounds
  have hLB0 : (0:ℝ) < LB := by linarith
  have hlog4T0 : (0:ℝ) ≤ Real.log (4 * T) := Real.log_nonneg hT1
  have hmax1 : (1:ℝ) ≤ max (2 * Bp * 1) LB := le_trans (by linarith) (le_max_right _ _)
  have hCge : Real.exp 2 ≤ Real.exp 2 * max (2 * Bp * 1) LB := by
    nlinarith [mul_nonneg (Real.exp_pos 2).le (sub_nonneg.2 hmax1)]
  have hlogC : (2:ℝ) ≤ Real.log (Real.exp 2 * max (2 * Bp * 1) LB) := by
    have h := Real.log_le_log (Real.exp_pos 2) hCge
    rwa [Real.log_exp] at h
  have hlogbig : (0:ℝ) ≤ Real.log (2 * (LL + Real.log (4 * T))) :=
    Real.log_nonneg (by linarith)
  have hin : 1 * (10 * LB) / gevreyA ≤ LB := by
    rw [one_mul, div_le_iff₀ (by linarith : (0:ℝ) < gevreyA)]
    nlinarith [mul_nonneg hLB0.le (sub_nonneg.2 hA13)]
  have hs1 : Real.sqrt (1 * (10 * LB) / gevreyA) ≤ Real.sqrt LB := Real.sqrt_le_sqrt hin
  have hx : Real.sqrt LB ^ 2 = LB := Real.sq_sqrt hLB0.le
  have e1 : c4 * Real.sqrt (1 * (10 * LB) / gevreyA) ≤ 1.5 * Real.sqrt LB := by
    calc c4 * Real.sqrt (1 * (10 * LB) / gevreyA)
        ≤ 1.5 * Real.sqrt (1 * (10 * LB) / gevreyA) :=
          mul_le_mul_of_nonneg_right hc4hi (Real.sqrt_nonneg _)
      _ ≤ 1.5 * Real.sqrt LB := mul_le_mul_of_nonneg_left hs1 (by norm_num)
  nlinarith [sq_nonneg (Real.sqrt LB - 3/2), hx, e1]

set_option maxHeartbeats 1000000 in
/-- **The high endpoint: `g(T/3) ≥ 0` in the regime `u = log Q ≥ 200`, `16 log u ≤ u`.**
Row by row, with `√T ≥ 14u` from `T ≥ u³`:
`L/2 ≤ u`; `2 log C_env ≤ 24 + 2 log u` (as `C_env ≤ e²(2B + L) ≤ 460u`);
`log(2(ℒ + log 4T)) ≤ 12 + log u` (as `2(ℒ + log 4T) ≤ 5u`);
`2 log S(T/3) ≤ 24 + 2 log u + u/2` (as `S ≤ 13u√T`, using `S`'s coefficient `≤ 10u` and
`√(T/3A)/c₄ ≤ √T/8`). Total `≤ 1.5u + 5 log u + 60 ≤ 2.12u`, against a supplied
`c₄√(T/3A) ≥ 1.4·√T/7 ≥ 2.8u`.
Stated with an extra margin `m ≤ u/4` on the needed side (the slack `2.8u − 2.12u`
absorbs it); `design_high_sign` below is the case `m = 0`. -/
private theorem design_high_sign_margin (Bp LB LL T u m : ℝ) (hBp : Bp ≤ 40000)
    (hu : 200 ≤ u) (h16 : 16 * Real.log u ≤ u)
    (hLB : 100 ≤ LB) (hLBhi : LB ≤ 2 * u) (hLL : 100 ≤ LL) (hLLhi : LL ≤ 3/2 * u)
    (hTpos : 0 < T) (hT3 : u ^ 3 ≤ T)
    (hlogT0 : 0 ≤ Real.log T) (hlogT : Real.log T ≤ u / 2) (hm : m ≤ u / 4) :
    LB / 2 + 2 * Real.log (Real.exp 2 * max (2 * Bp * 1) LB)
        + Real.log (2 * (LL + Real.log (4 * T))) + m
        + 2 * Real.log (1 + LB / (2 * Real.pi) * (2 * gevreyA / 1)
            * (Real.sqrt (1 * (T / 3) / gevreyA) / c4 + 1 / c4 ^ 2))
      ≤ c4 * Real.sqrt (1 * (T / 3) / gevreyA) := by
  obtain ⟨hA13, hA14⟩ := gevreyA_bounds
  obtain ⟨hc4lo, hc4hi⟩ := c4_bounds
  obtain ⟨he2lo, he2hi, -, -, -⟩ := exp_pow_bounds
  obtain ⟨hl4, -, -, hl1e5⟩ := log_const_bounds
  have hl40 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hu0 : (0:ℝ) < u := by linarith
  have hLB0 : (0:ℝ) < LB := by linarith
  have hc40 : (0:ℝ) < c4 := by linarith
  have hc4sq : (1.96:ℝ) ≤ c4 ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1.4) hc4lo 2
    norm_num at h; linarith
  -- `√T ≥ 14u ≥ 1`
  have hsqTpos : (0:ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsT : 14 * u ≤ Real.sqrt T := by
    have h1 : (14 * u) ^ 2 ≤ T := by
      linarith [mul_nonneg (sq_nonneg u) (by linarith : (0:ℝ) ≤ u - 196)]
    calc 14 * u = Real.sqrt ((14 * u) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt h1
  have hsT1 : (1:ℝ) ≤ Real.sqrt T := by linarith
  -- the envelope row
  -- `B′ ≤ 40000`, so `max(2B′, L) ≤ 402u` and `C_env ≤ 2975u` (was `62u`, `460u` at
  -- `B ≤ 6000`); `log 2975 ≤ 12` still, so the row `2 log C_env ≤ 24 + 2 log u` is unchanged.
  have hmax1 : (1:ℝ) ≤ max (2 * Bp * 1) LB := le_trans (by linarith) (le_max_right _ _)
  have hmax0 : (0:ℝ) ≤ max (2 * Bp * 1) LB := by linarith
  have hmaxle : max (2 * Bp * 1) LB ≤ 402 * u := max_le (by linarith) (by linarith)
  have hCpos : (0:ℝ) < Real.exp 2 * max (2 * Bp * 1) LB :=
    mul_pos (Real.exp_pos 2) (lt_of_lt_of_le zero_lt_one hmax1)
  have hCle : Real.exp 2 * max (2 * Bp * 1) LB ≤ 2975 * u := by
    linarith [mul_le_mul he2hi hmaxle hmax0 (by norm_num : (0:ℝ) ≤ 7.4)]
  have hlogCle : Real.log (Real.exp 2 * max (2 * Bp * 1) LB) ≤ 12 + Real.log u := by
    have h1 := Real.log_le_log hCpos hCle
    have h2 : Real.log (2975 * u) = Real.log 2975 + Real.log u :=
      Real.log_mul (by norm_num) (ne_of_gt hu0)
    have h3 : Real.log 2975 ≤ 12 :=
      le_trans (Real.log_le_log (by norm_num) (by norm_num : (2975:ℝ) ≤ 100000)) hl1e5
    linarith
  -- the `2(ℒ + log 4T)` row
  have hlog4T : Real.log (4 * T) = Real.log 4 + Real.log T :=
    Real.log_mul (by norm_num) (ne_of_gt hTpos)
  have hbigpos : (0:ℝ) < 2 * (LL + Real.log (4 * T)) := by rw [hlog4T]; linarith
  have hbigle : 2 * (LL + Real.log (4 * T)) ≤ 5 * u := by rw [hlog4T]; linarith
  have hlogbigle : Real.log (2 * (LL + Real.log (4 * T))) ≤ 12 + Real.log u := by
    have h1 := Real.log_le_log hbigpos hbigle
    have h2 : Real.log (5 * u) = Real.log 5 + Real.log u :=
      Real.log_mul (by norm_num) (ne_of_gt hu0)
    have h3 : Real.log 5 ≤ 12 :=
      le_trans (Real.log_le_log (by norm_num) (by norm_num : (5:ℝ) ≤ 100000)) hl1e5
    linarith
  -- the row-sum factor at `D₀ = T/3`
  have ht0 : (0:ℝ) ≤ Real.sqrt (1 * (T / 3) / gevreyA) := Real.sqrt_nonneg _
  have htle : Real.sqrt (1 * (T / 3) / gevreyA) ≤ Real.sqrt T / 6 := by
    have hin2 : 1 * (T / 3) / gevreyA ≤ (Real.sqrt T / 6) ^ 2 := by
      rw [one_mul, div_div, div_pow, Real.sq_sqrt hTpos.le,
        div_le_div_iff₀ (by linarith : (0:ℝ) < 3 * gevreyA) (by norm_num : (0:ℝ) < (6:ℝ)^2)]
      linarith [mul_nonneg hTpos.le (by linarith : (0:ℝ) ≤ 3 * gevreyA - 36)]
    calc Real.sqrt (1 * (T / 3) / gevreyA) ≤ Real.sqrt ((Real.sqrt T / 6) ^ 2) :=
          Real.sqrt_le_sqrt hin2
      _ = Real.sqrt T / 6 := Real.sqrt_sq (by positivity)
  have htge : Real.sqrt T / 7 ≤ Real.sqrt (1 * (T / 3) / gevreyA) := by
    have hin3 : (Real.sqrt T / 7) ^ 2 ≤ 1 * (T / 3) / gevreyA := by
      rw [one_mul, div_div, div_pow, Real.sq_sqrt hTpos.le,
        div_le_div_iff₀ (by norm_num : (0:ℝ) < (7:ℝ)^2) (by linarith : (0:ℝ) < 3 * gevreyA)]
      linarith [mul_nonneg hTpos.le (by linarith : (0:ℝ) ≤ 49 - 3 * gevreyA)]
    calc Real.sqrt T / 7 = Real.sqrt ((Real.sqrt T / 7) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hin3
  have hbr0 : (0:ℝ) ≤ Real.sqrt (1 * (T / 3) / gevreyA) / c4 + 1 / c4 ^ 2 := by
    have h1 : (0:ℝ) ≤ Real.sqrt (1 * (T / 3) / gevreyA) / c4 := div_nonneg ht0 hc40.le
    have h2 : (0:ℝ) ≤ 1 / c4 ^ 2 := by positivity
    linarith
  have hbracket : Real.sqrt (1 * (T / 3) / gevreyA) / c4 + 1 / c4 ^ 2
      ≤ Real.sqrt T / 8 + 1 := by
    have h1 : Real.sqrt (1 * (T / 3) / gevreyA) / c4 ≤ Real.sqrt T / 8 := by
      rw [div_le_div_iff₀ hc40 (by norm_num)]
      linarith [mul_nonneg (Real.sqrt_nonneg T) (sub_nonneg.2 hc4lo)]
    have h2 : 1 / c4 ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < c4 ^ 2)]; linarith
    linarith
  have hKc0 : (0:ℝ) ≤ LB / (2 * Real.pi) * (2 * gevreyA / 1) :=
    mul_nonneg (div_nonneg hLB0.le (by linarith)) (by rw [div_one]; linarith)
  have hKcle : LB / (2 * Real.pi) * (2 * gevreyA / 1) ≤ 10 * u := by
    have hLBpi : LB / (2 * Real.pi) ≤ u / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith [mul_nonneg hu0.le (by linarith : (0:ℝ) ≤ 2 * Real.pi - 6)]
    have hAw : 2 * gevreyA / 1 ≤ 28 := by rw [div_one]; linarith
    have hAw0 : (0:ℝ) ≤ 2 * gevreyA / 1 := by rw [div_one]; linarith
    linarith [mul_le_mul hLBpi hAw hAw0 (by linarith : (0:ℝ) ≤ u / 3)]
  have hus : (1:ℝ) ≤ u * Real.sqrt T := by
    linarith [mul_nonneg hu0.le (by linarith : (0:ℝ) ≤ Real.sqrt T - 1)]
  have hRS0 : (0:ℝ) < 1 + LB / (2 * Real.pi) * (2 * gevreyA / 1)
      * (Real.sqrt (1 * (T / 3) / gevreyA) / c4 + 1 / c4 ^ 2) := by
    linarith [mul_nonneg hKc0 hbr0]
  have hRSle : 1 + LB / (2 * Real.pi) * (2 * gevreyA / 1)
        * (Real.sqrt (1 * (T / 3) / gevreyA) / c4 + 1 / c4 ^ 2)
      ≤ 13 * u * Real.sqrt T := by
    linarith [mul_le_mul hKcle hbracket hbr0 (by linarith : (0:ℝ) ≤ 10 * u),
      mul_nonneg hu0.le (by linarith : (0:ℝ) ≤ Real.sqrt T - 1), hus]
  have hlogRS : Real.log (1 + LB / (2 * Real.pi) * (2 * gevreyA / 1)
        * (Real.sqrt (1 * (T / 3) / gevreyA) / c4 + 1 / c4 ^ 2))
      ≤ 12 + Real.log u + u / 4 := by
    have h1 := Real.log_le_log hRS0 hRSle
    have h2 : Real.log (13 * u * Real.sqrt T)
        = Real.log 13 + Real.log u + Real.log (Real.sqrt T) := by
      rw [Real.log_mul (ne_of_gt (by linarith : (0:ℝ) < 13 * u)) (ne_of_gt hsqTpos),
        Real.log_mul (by norm_num) (ne_of_gt hu0)]
    have h3 : Real.log (Real.sqrt T) = Real.log T / 2 := Real.log_sqrt hTpos.le
    have h4 : Real.log 13 ≤ 12 :=
      le_trans (Real.log_le_log (by norm_num) (by norm_num : (13:ℝ) ≤ 100000)) hl1e5
    rw [h2, h3] at h1
    linarith
  have hsupp : 2.8 * u ≤ c4 * Real.sqrt (1 * (T / 3) / gevreyA) := by
    linarith [mul_nonneg (sub_nonneg.2 hc4lo) ht0]
  linarith


/-- `design_high_sign_margin` at `m = 0` — the original statement. -/
private theorem design_high_sign (Bp LB LL T u : ℝ) (hBp : Bp ≤ 40000)
    (hu : 200 ≤ u) (h16 : 16 * Real.log u ≤ u)
    (hLB : 100 ≤ LB) (hLBhi : LB ≤ 2 * u) (hLL : 100 ≤ LL) (hLLhi : LL ≤ 3/2 * u)
    (hTpos : 0 < T) (hT3 : u ^ 3 ≤ T)
    (hlogT0 : 0 ≤ Real.log T) (hlogT : Real.log T ≤ u / 2) :
    LB / 2 + 2 * Real.log (Real.exp 2 * max (2 * Bp * 1) LB)
        + Real.log (2 * (LL + Real.log (4 * T)))
        + 2 * Real.log (1 + LB / (2 * Real.pi) * (2 * gevreyA / 1)
            * (Real.sqrt (1 * (T / 3) / gevreyA) / c4 + 1 / c4 ^ 2))
      ≤ c4 * Real.sqrt (1 * (T / 3) / gevreyA) := by
  have h := design_high_sign_margin Bp LB LL T u 0 hBp hu h16 hLB hLBhi hLL hLLhi hTpos hT3
    hlogT0 hlogT (by linarith)
  rwa [add_zero] at h
/-- `10L ≤ T/3`, so the bracket `SideCondD0range` allows is non-degenerate: `10L ≤ 20u` while
`T/3 ≥ u³/3 ≥ 13333u`. -/
private theorem design_ab (LB T u : ℝ) (hu : 200 ≤ u) (hLBhi : LB ≤ 2 * u)
    (hT3 : u ^ 3 ≤ T) : 10 * LB ≤ T / 3 := by
  have hu0 : (0:ℝ) < u := by linarith
  linarith [mul_nonneg hu0.le (by nlinarith : (0:ℝ) ≤ u ^ 2 - 40000)]

set_option maxHeartbeats 1000000 in
/-- **🟢 THE DESIGN POINT AT ONE `Q`** — `assembly_at_lamStar`'s checklist item 1, pointwise.
`w = 1`, `λ = λ*`, `T = (log Q)^{r+ε}`, taper from `Zeta23.exists_taperProfile`, and `D₀` the
root of the margin-0 closing equality inside `(10L, T/3)`.

The regime is `log Q ≥ 200` and `(2(r+ε)+10)·log log Q ≤ log Q`, both of which `atTop`
supplies eventually at each fixed `(r, ε)` — see `exists_designOfRecord`.
Rule 17: see the section note above; `w = 1` uses `r ≥ 3`. -/
theorem exists_designOfRecord_at (F : Family) (r ε Q : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hQ3 : 3 ≤ Q) (hQ0 : 0 < Q)
    (hu : 200 ≤ Real.log Q)
    (hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q) :
    ∃ P : ParamsQ, DesignOfRecord F r ε Q P := by
  obtain ⟨hlam1, hlam126⟩ := lamStar_bounds F
  obtain ⟨hA13, hA14⟩ := gevreyA_bounds
  obtain ⟨he2lo, he2hi, -, -, -⟩ := exp_pow_bounds
  have h2pi0 := log_two_pi_nonneg
  have h2pi3 := log_two_pi_le_three
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  -- ## the regime
  have hu0 : (0:ℝ) < Real.log Q := by linarith
  have hu1 : (1:ℝ) ≤ Real.log Q := by linarith
  have hv0 : (0:ℝ) < Real.log (Real.log Q) := Real.log_pos (by linarith)
  have hre : (3:ℝ) ≤ r + ε := by linarith
  have h16v : 16 * Real.log (Real.log Q) ≤ Real.log Q := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : (16:ℝ) ≤ 2*(r+ε)+10) hv0.le]
  have hhalf : (r+ε) * Real.log (Real.log Q) ≤ Real.log Q / 2 := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : 2*(r+ε) ≤ 2*(r+ε)+10) hv0.le]
  have hrev : (0:ℝ) ≤ (r+ε) * Real.log (Real.log Q) := mul_nonneg (by linarith) hv0.le
  have hTpos : (0:ℝ) < Real.log Q ^ (r+ε) := Real.rpow_pos_of_pos hu0 _
  have hT3 : Real.log Q ^ 3 ≤ Real.log Q ^ (r+ε) := by
    calc Real.log Q ^ 3 = Real.log Q ^ ((3:ℕ):ℝ) := (Real.rpow_natCast _ 3).symm
      _ ≤ Real.log Q ^ (r+ε) :=
          Real.rpow_le_rpow_of_exponent_le hu1 (by push_cast; linarith)
  -- ## the design point, scales carried by their projection equations
  -- the design point carries the ramp `ϱ₂` and the profile `designProfile F`
  have hϱ : Zeta23.TaperProfile Zeta23.Taper.rhoTwo := Zeta23.Taper.gevreyProfile_rhoTwo.taper
  obtain ⟨P₀, hQ', hT', hlam', hw', hrho', hprof'⟩ :
      ∃ P₀ : ParamsQ, P₀.Q = Q ∧ P₀.T = Real.log Q ^ (r + ε) ∧ P₀.lam = F.lamStar
        ∧ P₀.w = 1 ∧ P₀.ϱ = Zeta23.Taper.rhoTwo ∧ P₀.prof = F.designProfile :=
    ⟨⟨Q, Real.log Q ^ (r + ε), F.lamStar, 1, 2, Zeta23.Taper.rhoTwo, F.designProfile⟩,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hTpos' : (0:ℝ) < P₀.T := by rw [hT']; exact hTpos
  have hT3' : Real.log Q ^ 3 ≤ P₀.T := by rw [hT']; exact hT3
  have hTbig : (1000000:ℝ) ≤ P₀.T := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 200) hu 3
    norm_num at h; linarith
  have hlogT' : Real.log P₀.T = (r+ε) * Real.log (Real.log Q) := by
    rw [hT']; exact Real.log_rpow hu0 _
  have hLLeq : P₀.LL = Real.log Q + (r+ε)*Real.log (Real.log Q) - Real.log (2*Real.pi) := by
    show Real.log (P₀.Q * P₀.T / (2*Real.pi)) = _
    rw [hQ', hT', Real.log_div (mul_ne_zero (ne_of_gt hQ0) (ne_of_gt hTpos)) (by positivity),
      Real.log_mul (ne_of_gt hQ0) (ne_of_gt hTpos), Real.log_rpow hu0]
  have hLLlo : Real.log Q / 2 ≤ P₀.LL := by rw [hLLeq]; linarith
  have hLLhi : P₀.LL ≤ 3/2 * Real.log Q := by rw [hLLeq]; linarith
  have hLL0 : (0:ℝ) < P₀.LL := by linarith
  have hLL1 : (1:ℝ) ≤ P₀.LL := by linarith
  have hLL100 : (100:ℝ) ≤ P₀.LL := by linarith
  have hLBeq : P₀.LB = F.lamStar * P₀.LL := by show P₀.lam * P₀.LL = _; rw [hlam']
  have hLBlo : Real.log Q / 2 ≤ P₀.LB := by
    rw [hLBeq]; linarith [mul_nonneg (sub_nonneg.2 hlam1) hLL0.le]
  have hLBhi : P₀.LB ≤ 2 * Real.log Q := by
    rw [hLBeq]
    linarith [mul_le_mul hlam126 hLLhi hLL0.le (by norm_num : (0:ℝ) ≤ 1.26)]
  have hLB100 : (100:ℝ) ≤ P₀.LB := by linarith
  have hLB0 : (0:ℝ) < P₀.LB := by linarith
  -- ## the bracket and the two endpoint signs
  have hab : 10 * P₀.LB ≤ P₀.T / 3 := design_ab P₀.LB P₀.T (Real.log Q) hu hLBhi hT3'
  have hKc0 : (0:ℝ) ≤ P₀.LB / (2 * Real.pi) * (2 * gevreyA / P₀.w) :=
    mul_nonneg (div_nonneg hLB0.le (by linarith)) (by rw [hw', div_one]; linarith)
  have hrs : ∀ b : ℝ, rowSumFactor { P₀ with D0 := b }
      = 1 + P₀.LB/(2*Real.pi)*(2*gevreyA/P₀.w)
          * (Real.sqrt (P₀.w * b/gevreyA)/c4 + 1/c4^2) := fun b => rfl
  have hBp : P₀.gevreyBprod gevreyA gevreyB ≤ 40000 :=
    design_gevreyBprod_le F P₀ hprof' hlam' hw' (by linarith)
  have hlow : c4 * Real.sqrt (P₀.w * (10 * P₀.LB) / gevreyA)
      ≤ P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
        + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T))) := by
    unfold CenvDesign
    rw [hw']
    exact design_low_sign _ P₀.LB P₀.LL P₀.T hLB100 hLL100 (by linarith)
  have hhigh : P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
        + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T)))
        + 2 * Real.log (rowSumFactor { P₀ with D0 := P₀.T / 3 })
      ≤ c4 * Real.sqrt (P₀.w * (P₀.T / 3) / gevreyA) := by
    rw [hrs (P₀.T / 3)]
    unfold CenvDesign
    rw [hw']
    exact design_high_sign _ P₀.LB P₀.LL P₀.T (Real.log Q) hBp
      hu h16v hLB100 hLBhi hLL100 hLLhi hTpos' hT3' (by rw [hlogT']; linarith)
      (by rw [hlogT']; linarith)
  -- ## the root, and the side conditions at it
  obtain ⟨D, hDa, hDb, hclose⟩ :=
    exists_closing_in P₀ (10 * P₀.LB) (P₀.T / 3) hab hKc0 hlow hhigh
  have hD1000 : (1000:ℝ) ≤ D := by linarith
  have hlne : Zeta23.l P₀.T ≠ 0 := by
    unfold Zeta23.l
    apply ne_of_gt
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    linarith [Real.pi_le_four]
  -- the two `Valid` moment floors at the design (`design_moments`, `ZetaQ/DesignProfile.lean`)
  have hmom := design_moments F { P₀ with D0 := D } hprof' (by rw [hrho']; exact hϱ) hlam' hw'
    hLL100 hlne
  refine ⟨{ P₀ with D0 := D },
    ⟨?_, hQ', hT', hlam', ?_, ?_, ?_, ⟨hDa, hDb⟩, ?_, hclose, hrho', hprof'⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmom.1, hmom.2⟩
    · show Zeta23.TaperProfile P₀.ϱ
      rw [hrho']; exact hϱ
    · show ParamsQ.ProfileQ P₀.prof P₀.lam
      rw [hprof', hlam']; exact profileQ_design F
    · show (0:ℝ) < P₀.lam
      rw [hlam']; linarith
    · show P₀.lam < 2
      rw [hlam']; linarith
    · show (1:ℝ) ≤ P₀.w
      rw [hw']
    · show (2:ℝ) ≤ D
      linarith
    · show D + 4 ≤ P₀.T
      linarith
    · show Zeta23.Tail.T₀ ≤ P₀.T
      show (300:ℝ) ≤ P₀.T
      linarith
    · show (3:ℝ) ≤ P₀.Q
      rw [hQ']; exact hQ3
  · show P₀.w = wDesign P₀.LL r
    rw [hw']
    unfold wDesign wStar
    exact (max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))).symm
  · show (8:ℝ) * P₀.w ≤ P₀.LB
    rw [hw']; linarith
  · show Real.exp 2 * gevreyA ≤ P₀.w * D
    rw [hw', one_mul]
    linarith [mul_le_mul he2hi hA14 (by linarith : (0:ℝ) ≤ gevreyA)
      (by norm_num : (0:ℝ) ≤ 7.4)]
  · show 10 * P₀.LL * Real.log P₀.LL ≤ P₀.T
    have hlogLL0 : (0:ℝ) ≤ Real.log P₀.LL := Real.log_nonneg hLL1
    have hlogLLle : Real.log P₀.LL ≤ 3/2 * Real.log Q := by
      linarith [Real.log_le_sub_one_of_pos hLL0]
    linarith [mul_le_mul hLLhi hlogLLle hlogLL0
        (by linarith : (0:ℝ) ≤ 3/2 * Real.log Q),
      mul_nonneg (sq_nonneg (Real.log Q)) (by linarith : (0:ℝ) ≤ Real.log Q - 23)]

/-- **🟢 `assembly_at_lamStar`'s CHECKLIST ITEM 1, DISCHARGED**: a design point exists at
every large `Q`. Stated in the `∃ Q₀, ∀ Q ≥ Q₀` shape the assembly consumes.

The floor is `log Q ≥ 200` (i.e. `Q ≥ e²⁰⁰ ≈ 10⁸⁷`) together with
`(2(r+ε)+10)·log log Q ≤ log Q`, which `isLittleO_loglog_log` supplies eventually. Neither is
sharp; both are chosen so the endpoint estimates close with room, and `assembly_at_lamStar`
quantifies over `Q ≥ Q₀` anyway (as does Theorem 1, over `Q ≥ Q₀(ε)`).

Depends on: `exists_designOfRecord_at`, `isLittleO_loglog_log`,
`Zeta23.exists_taperProfile`. Rule 17: as the section note. -/
theorem exists_designOfRecord (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∃ P : ParamsQ, DesignOfRecord F r ε Q P := by
  have hK : (0 : ℝ) < 2 * (r + ε) + 10 := by linarith
  have hlo := isLittleO_loglog_log.def (c := 1 / (2 * (r + ε) + 10)) (by positivity)
  refine eventually_atTop.mp ?_
  filter_upwards [hlo, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (200 : ℝ)] with Q hlo' hQ0 hQ3 hu
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := Real.log_pos (by linarith)
  have hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0.le,
      abs_of_nonneg hu0.le] at hlo'
    have h2 := mul_le_mul_of_nonneg_left hlo' hK.le
    rw [show (2 * (r + ε) + 10) * (1 / (2 * (r + ε) + 10) * Real.log Q) = Real.log Q by
      field_simp] at h2
    exact h2
  exact exists_designOfRecord_at F r ε Q hr hε hQ3 hQ0 hu hvu

/-- **The margin-0 closing clause WITH MARGIN is exactly the shifted root equation**:
`ClosingAtDesignM P` says precisely

    c₄·t_{D₀}  =  L/2 + 2 log C_env + log(2(ℒ + log 4T)) + m + 2 log S(D₀),   m = ½ log T,

an equality written as two inequalities (`closingAtDesign_of_root` is the case `m = 0`). -/
theorem closingAtDesignM_of_root (P : ParamsQ)
    (hroot : c4 * Real.sqrt (P.w * P.D0 / gevreyA)
      = P.LB / 2 + 2 * Real.log (CenvDesign P)
        + Real.log (2 * (P.LL + Real.log (4 * P.T))) + marginDesign P
        + 2 * Real.log (rowSumFactor P)) :
    ClosingAtDesignM P := by
  have hLB : Real.log (P.LB / 1) = Real.log P.LB := by rw [div_one]
  constructor
  · show P.LB / 2 + (logPrefactorGev P + marginDesign P) + Real.log (P.LB / 1)
        ≤ c4 * Real.sqrt (P.w * P.D0 / gevreyA)
    unfold logPrefactorGev
    rw [hLB]; linarith
  · show c4 * tBuffer P ≤ P.LB / 2 + logPrefactorGev P + marginDesign P + Real.log (P.LB / 1)
    unfold logPrefactorGev tBuffer
    rw [hLB]; linarith

/-- `exists_closing_in` with the margin: a buffer inside `[a,b]` at which `ClosingAtDesignM`
holds. Rule 17: as `exists_root_of_signs`. -/
private theorem exists_closing_in_M (P₀ : ParamsQ) (a b : ℝ) (hab : a ≤ b)
    (hKc : 0 ≤ P₀.LB / (2 * Real.pi) * (2 * gevreyA / P₀.w))
    (hlow : c4 * Real.sqrt (P₀.w * a / gevreyA)
        ≤ P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
          + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T))) + marginDesign P₀)
    (hhigh : P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
          + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T))) + marginDesign P₀
          + 2 * Real.log (rowSumFactor { P₀ with D0 := b })
        ≤ c4 * Real.sqrt (P₀.w * b / gevreyA)) :
    ∃ D, a ≤ D ∧ D ≤ b ∧ ClosingAtDesignM { P₀ with D0 := D } := by
  obtain ⟨D, hDa, hDb, hroot⟩ := exists_root_of_signs P₀.w
    (P₀.LB / (2 * Real.pi) * (2 * gevreyA / P₀.w))
    (P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
      + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T))) + marginDesign P₀)
    a b hKc hab hlow hhigh
  exact ⟨D, hDa, hDb, closingAtDesignM_of_root { P₀ with D0 := D } hroot⟩

set_option maxHeartbeats 1000000 in
/-- **🟢 THE MARGIN DESIGN POINT AT ONE `Q`** — `exists_designOfRecord_at` verbatim with the
root of the SHIFTED closing equality: `w = 1`, `λ = λ*`, `T = (log Q)^{r+ε}`, ramp `ϱ₂`,
profile `designProfile F`, and `D₀` the root of `c₄ t = needed + m` inside `(10L, T/3)`. The
low endpoint sign only improves (`m ≥ 0`); the high one has `m ≤ u/4` against the slack
`2.8u − 2.12u` (`design_high_sign_margin`). Same regime: `log Q ≥ 200`,
`(2(r+ε)+10)·log log Q ≤ log Q`. Rule 17: as `exists_designOfRecord_at`. -/
theorem exists_designOfRecordM_at (F : Family) (r ε Q : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hQ3 : 3 ≤ Q) (hQ0 : 0 < Q)
    (hu : 200 ≤ Real.log Q)
    (hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q) :
    ∃ P : ParamsQ, DesignOfRecordM F r ε Q P := by
  obtain ⟨hlam1, hlam126⟩ := lamStar_bounds F
  obtain ⟨hA13, hA14⟩ := gevreyA_bounds
  obtain ⟨he2lo, he2hi, -, -, -⟩ := exp_pow_bounds
  have h2pi0 := log_two_pi_nonneg
  have h2pi3 := log_two_pi_le_three
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  -- ## the regime
  have hu0 : (0:ℝ) < Real.log Q := by linarith
  have hu1 : (1:ℝ) ≤ Real.log Q := by linarith
  have hv0 : (0:ℝ) < Real.log (Real.log Q) := Real.log_pos (by linarith)
  have hre : (3:ℝ) ≤ r + ε := by linarith
  have h16v : 16 * Real.log (Real.log Q) ≤ Real.log Q := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : (16:ℝ) ≤ 2*(r+ε)+10) hv0.le]
  have hhalf : (r+ε) * Real.log (Real.log Q) ≤ Real.log Q / 2 := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : 2*(r+ε) ≤ 2*(r+ε)+10) hv0.le]
  have hrev : (0:ℝ) ≤ (r+ε) * Real.log (Real.log Q) := mul_nonneg (by linarith) hv0.le
  have hTpos : (0:ℝ) < Real.log Q ^ (r+ε) := Real.rpow_pos_of_pos hu0 _
  have hT3 : Real.log Q ^ 3 ≤ Real.log Q ^ (r+ε) := by
    calc Real.log Q ^ 3 = Real.log Q ^ ((3:ℕ):ℝ) := (Real.rpow_natCast _ 3).symm
      _ ≤ Real.log Q ^ (r+ε) :=
          Real.rpow_le_rpow_of_exponent_le hu1 (by push_cast; linarith)
  -- ## the design point, scales carried by their projection equations
  -- the design point carries the ramp `ϱ₂` and the profile `designProfile F`
  have hϱ : Zeta23.TaperProfile Zeta23.Taper.rhoTwo := Zeta23.Taper.gevreyProfile_rhoTwo.taper
  obtain ⟨P₀, hQ', hT', hlam', hw', hrho', hprof'⟩ :
      ∃ P₀ : ParamsQ, P₀.Q = Q ∧ P₀.T = Real.log Q ^ (r + ε) ∧ P₀.lam = F.lamStar
        ∧ P₀.w = 1 ∧ P₀.ϱ = Zeta23.Taper.rhoTwo ∧ P₀.prof = F.designProfile :=
    ⟨⟨Q, Real.log Q ^ (r + ε), F.lamStar, 1, 2, Zeta23.Taper.rhoTwo, F.designProfile⟩,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hTpos' : (0:ℝ) < P₀.T := by rw [hT']; exact hTpos
  have hT3' : Real.log Q ^ 3 ≤ P₀.T := by rw [hT']; exact hT3
  have hTbig : (1000000:ℝ) ≤ P₀.T := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 200) hu 3
    norm_num at h; linarith
  have hlogT' : Real.log P₀.T = (r+ε) * Real.log (Real.log Q) := by
    rw [hT']; exact Real.log_rpow hu0 _
  have hLLeq : P₀.LL = Real.log Q + (r+ε)*Real.log (Real.log Q) - Real.log (2*Real.pi) := by
    show Real.log (P₀.Q * P₀.T / (2*Real.pi)) = _
    rw [hQ', hT', Real.log_div (mul_ne_zero (ne_of_gt hQ0) (ne_of_gt hTpos)) (by positivity),
      Real.log_mul (ne_of_gt hQ0) (ne_of_gt hTpos), Real.log_rpow hu0]
  have hLLlo : Real.log Q / 2 ≤ P₀.LL := by rw [hLLeq]; linarith
  have hLLhi : P₀.LL ≤ 3/2 * Real.log Q := by rw [hLLeq]; linarith
  have hLL0 : (0:ℝ) < P₀.LL := by linarith
  have hLL1 : (1:ℝ) ≤ P₀.LL := by linarith
  have hLL100 : (100:ℝ) ≤ P₀.LL := by linarith
  have hLBeq : P₀.LB = F.lamStar * P₀.LL := by show P₀.lam * P₀.LL = _; rw [hlam']
  have hLBlo : Real.log Q / 2 ≤ P₀.LB := by
    rw [hLBeq]; linarith [mul_nonneg (sub_nonneg.2 hlam1) hLL0.le]
  have hLBhi : P₀.LB ≤ 2 * Real.log Q := by
    rw [hLBeq]
    linarith [mul_le_mul hlam126 hLLhi hLL0.le (by norm_num : (0:ℝ) ≤ 1.26)]
  have hLB100 : (100:ℝ) ≤ P₀.LB := by linarith
  have hLB0 : (0:ℝ) < P₀.LB := by linarith
  -- ## the bracket and the two endpoint signs
  have hab : 10 * P₀.LB ≤ P₀.T / 3 := design_ab P₀.LB P₀.T (Real.log Q) hu hLBhi hT3'
  have hKc0 : (0:ℝ) ≤ P₀.LB / (2 * Real.pi) * (2 * gevreyA / P₀.w) :=
    mul_nonneg (div_nonneg hLB0.le (by linarith)) (by rw [hw', div_one]; linarith)
  have hrs : ∀ b : ℝ, rowSumFactor { P₀ with D0 := b }
      = 1 + P₀.LB/(2*Real.pi)*(2*gevreyA/P₀.w)
          * (Real.sqrt (P₀.w * b/gevreyA)/c4 + 1/c4^2) := fun b => rfl
  have hBp : P₀.gevreyBprod gevreyA gevreyB ≤ 40000 :=
    design_gevreyBprod_le F P₀ hprof' hlam' hw' (by linarith)
  -- the margin `m = ½ log T = ½(r+ε) log log Q ∈ [0, u/4]`
  have hm0 : 0 ≤ marginDesign P₀ := by
    unfold marginDesign; rw [hlogT']; linarith
  have hm4 : marginDesign P₀ ≤ Real.log Q / 4 := by
    unfold marginDesign; rw [hlogT']; linarith
  have hlow : c4 * Real.sqrt (P₀.w * (10 * P₀.LB) / gevreyA)
      ≤ P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
        + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T))) + marginDesign P₀ := by
    have h := design_low_sign (P₀.gevreyBprod gevreyA gevreyB) P₀.LB P₀.LL P₀.T hLB100 hLL100
      (by linarith)
    unfold CenvDesign
    rw [hw']
    linarith
  have hhigh : P₀.LB / 2 + 2 * Real.log (CenvDesign P₀)
        + Real.log (2 * (P₀.LL + Real.log (4 * P₀.T))) + marginDesign P₀
        + 2 * Real.log (rowSumFactor { P₀ with D0 := P₀.T / 3 })
      ≤ c4 * Real.sqrt (P₀.w * (P₀.T / 3) / gevreyA) := by
    rw [hrs (P₀.T / 3)]
    unfold CenvDesign
    rw [hw']
    exact design_high_sign_margin _ P₀.LB P₀.LL P₀.T (Real.log Q) (marginDesign P₀) hBp
      hu h16v hLB100 hLBhi hLL100 hLLhi hTpos' hT3' (by rw [hlogT']; linarith)
      (by rw [hlogT']; linarith) hm4
  -- ## the root, and the side conditions at it
  obtain ⟨D, hDa, hDb, hclose⟩ :=
    exists_closing_in_M P₀ (10 * P₀.LB) (P₀.T / 3) hab hKc0 hlow hhigh
  have hD1000 : (1000:ℝ) ≤ D := by linarith
  have hlne : Zeta23.l P₀.T ≠ 0 := by
    unfold Zeta23.l
    apply ne_of_gt
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    linarith [Real.pi_le_four]
  -- the two `Valid` moment floors at the design (`design_moments`, `ZetaQ/DesignProfile.lean`)
  have hmom := design_moments F { P₀ with D0 := D } hprof' (by rw [hrho']; exact hϱ) hlam' hw'
    hLL100 hlne
  refine ⟨{ P₀ with D0 := D },
    ⟨?_, hQ', hT', hlam', ?_, ?_, ?_, ⟨hDa, hDb⟩, ?_, hclose, hrho', hprof'⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmom.1, hmom.2⟩
    · show Zeta23.TaperProfile P₀.ϱ
      rw [hrho']; exact hϱ
    · show ParamsQ.ProfileQ P₀.prof P₀.lam
      rw [hprof', hlam']; exact profileQ_design F
    · show (0:ℝ) < P₀.lam
      rw [hlam']; linarith
    · show P₀.lam < 2
      rw [hlam']; linarith
    · show (1:ℝ) ≤ P₀.w
      rw [hw']
    · show (2:ℝ) ≤ D
      linarith
    · show D + 4 ≤ P₀.T
      linarith
    · show Zeta23.Tail.T₀ ≤ P₀.T
      show (300:ℝ) ≤ P₀.T
      linarith
    · show (3:ℝ) ≤ P₀.Q
      rw [hQ']; exact hQ3
  · show P₀.w = wDesign P₀.LL r
    rw [hw']
    unfold wDesign wStar
    exact (max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))).symm
  · show (8:ℝ) * P₀.w ≤ P₀.LB
    rw [hw']; linarith
  · show Real.exp 2 * gevreyA ≤ P₀.w * D
    rw [hw', one_mul]
    linarith [mul_le_mul he2hi hA14 (by linarith : (0:ℝ) ≤ gevreyA)
      (by norm_num : (0:ℝ) ≤ 7.4)]
  · show 10 * P₀.LL * Real.log P₀.LL ≤ P₀.T
    have hlogLL0 : (0:ℝ) ≤ Real.log P₀.LL := Real.log_nonneg hLL1
    have hlogLLle : Real.log P₀.LL ≤ 3/2 * Real.log Q := by
      linarith [Real.log_le_sub_one_of_pos hLL0]
    linarith [mul_le_mul hLLhi hlogLLle hlogLL0
        (by linarith : (0:ℝ) ≤ 3/2 * Real.log Q),
      mul_nonneg (sq_nonneg (Real.log Q)) (by linarith : (0:ℝ) ≤ Real.log Q - 23)]

/-- **A margin design point exists at every large `Q`** — `exists_designOfRecord` for
`DesignOfRecordM`, same floor. Depends on: `exists_designOfRecordM_at`, `isLittleO_loglog_log`. -/
theorem exists_designOfRecordM (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∃ P : ParamsQ, DesignOfRecordM F r ε Q P := by
  have hK : (0 : ℝ) < 2 * (r + ε) + 10 := by linarith
  have hlo := isLittleO_loglog_log.def (c := 1 / (2 * (r + ε) + 10)) (by positivity)
  refine eventually_atTop.mp ?_
  filter_upwards [hlo, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (200 : ℝ)] with Q hlo' hQ0 hQ3 hu
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log Q) := Real.log_pos (by linarith)
  have hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0.le,
      abs_of_nonneg hu0.le] at hlo'
    have h2 := mul_le_mul_of_nonneg_left hlo' hK.le
    rw [show (2 * (r + ε) + 10) * (1 / (2 * (r + ε) + 10) * Real.log Q) = Real.log Q by
      field_simp] at h2
    exact h2
  exact exists_designOfRecordM_at F r ε Q hr hε hQ3 hQ0 hu hvu

/-- **§10.5's assembly step.** §§4–9 combine into Proposition 3.1's hypotheses at
`λ = λ*`, at each fixed `(Q, T, ε)`, with the bracket bounded by `budgetTotal`. This is what
consumes `prop_3_1_pair_moment_certificate` together with the budget rows of §10.3, and it
is where "no ε-limit is taken" is discharged.

`≤` rather than `=` in the bracket clause keeps §10.3's open accounting question (Q7) open.

Paper §10.5.
Depends on: `trace_row`, `frobenius_row`, **`buffer_row_sharp`** (decision **D35** — the row
`r₃` is supplied at the SHARP zero density, under the named hypothesis `SharpZeroDensity`,
which is the paper's own assumption for this one row; **not** `buffer_row_proved`, which is
retained as the record of what §9/H6 proves outright),
`pair_rows`, `ends_row`, `prop_3_1_pair_moment_certificate`.
Note that the `r₃` clause below is an existential in `r₃`, so switching the supplier between
the two rows changes only which lemma is applied here — the statement does not move. What
*would* move is the last two clauses, which are bounded by `budgetTotal F P`; under **D35**
`budgetTotal` is the paper's own total and no recomputation is needed. The difference between
the two conventions is `Θ(D₀/T)` either way, so the rate class and `P` are untouched and only
§10.4's orientation figures move — which is why D35 keeps the paper's convention and states
its assumption rather than charging `≈255×` more.
Rule 17: `λ*` and `D₀` are chosen INSIDE the existential — that is the content of this
statement, and it is why no hypothesis anywhere bounds λ by 1 or ties `D₀` to `√T`.

--------------------------------------------------------------------------------------
**WHY THIS STATEMENT IS STILL `sorry`, ITEM BY ITEM.**

`assembly_clauses_at_design` proves the ENTIRE eight-clause body below at one design point,
from six named inputs, modulo `trace_row` and `frobenius_row` — `EFChi.prop31_fam` fed by
`ZetaQ.Tail`'s two §7.3 pair-split exports and this file's four rows. So what is left is not
an object mismatch but the inputs themselves. `ZetaQ.EFChi` and `ZetaQ.Tail` are imported here
(see the module header for the acyclicity check).

  1. ✅ **The design point EXISTS.** `ZetaQ.exists_designOfRecord` (and its pointwise form
     `exists_designOfRecord_at`): `∃ Q₀, ∀ Q ≥ Q₀, ∃ P, DesignOfRecord F r ε Q P`, proved. The
     obligation is real work rather than bookkeeping, because `ClosingAtDesign` pins the closing
     clause at an EQUALITY: the construction has to solve
     `c₄√(wD₀/A) = L/2 + logPrefactorGev P + log L` for `D₀` and then meet the five side
     conditions at the root. That is `exists_root_of_signs` (an intermediate-value argument;
     `ClosingAtDesign`'s docstring checks the two signs and locates the root at
     `wD₀ ≈ A(L/2)²/c₄² ≈ 6.1L²`) plus `closingAtDesign_of_root`, `design_low_sign` and
     `design_high_sign`. Witness: `λ = λ*`, `w = 1` (the clamp — this is where `r ≥ 3` enters),
     `T = (log Q)^{r+ε}`, taper from `Zeta23.exists_taperProfile`, `D₀` the root, strictly
     inside `(10L, T/3)`; floor `log Q ≥ 200`, well inside Theorem 1's own `Q₀(ε)`.
     `Zones.exists_designFamily_regime` is the analogous existence proof but is NOT reusable:
     its witness `λ = 1, w = 1, D₀ = 2` fails `SideCondD0range`, `SideCondWD0` and
     `ClosingAtDesign` alike. **This was the last piece of the checklist that §10 itself owned.**
  2. 🚩 `hsharp : SharpZeroDensity F Qn P` — **an assumption, not a gap.** It is the paper's own
     sharp zero density (§10.3's flagged row; §10.4 calls it "the ONE row not charged at its
     proved constant"), and no amount of §9 will discharge it from H6 — that is exactly the
     content of `buffer_row_gap`, whose direction is the wrong way round. See "THE MANDATED
     LEDGER FLAG" in the module header.
  3. ✅ **`famRvMLower_of_design`.** §12.2's conductor spread IS proved
     (`Normalisation.avgLogCond_asymp`, effectively `N2.Alog_bound`), and the row follows once
     the surrogate carries `rvmSlack` — see there for why it must. `ZetaQ/Normalisation.lean`
     §N6 has only the `⟨log q⟩ = log Q − 1/2 + o(1)` form, so a consumer that needs it at a
     fixed `Qn` must take it as a hypothesis and say so.
  4. 🟨 `hpair` reduces to `pair_absorbed_of_theta_small` + `theta0Fam_le_of_design`, leaving
     `hpre` — `log(prefactorQ …) ≤ logPrefactorGev`, i.e. LEMMA_QT §QT.b(4)→(5), which nothing
     in the tree relates — and one regime inequality `hregime`. ⚠ **The regime inequality is
     where a REAL constraint appears: `r + ε ≤ 7`.** See "§7's two assembly clauses" in the
     module header; `hpre` itself is proved in `ZetaQ/HPre.lean`, and `ZetaQ/Margin.lean`
     removes the regime constraint with the margin design.
  5. ✅ **`EFChi.famZeroConfig_famZc` and `EFChi.famGramBridge_famZc`** at
     `Zc := EFChi.famZc`, both sorry-free. Per member these are theorems for `1 < q`
     (`EFChi.ZChi_N`, `EFChi.ZChi_N0s`, `EFChi.rtrace_hatQ_gridGram_eq_Gz`,
     `EFChi.frobSq_hatQ_gridGram_eq_Gz`), and the family is the primitive χ of modulus
     `1 < q ≤ Q` — `Family.moduli Family.qle Qn` is `Finset.Icc 2 Qn` — so the `q = 1` member
     that used to block them (ζ's zero configuration, for which H2 has no pole-free form) is
     not in the family. ([R]'s Theorem E is stated for `q > 1`; paper §2.2 says "primitive
     χ ≠ χ₀"; only §1.1's family definition omitted the bound.) Cost: one character out of
     `|𝔉_Q| ≍ (18/π⁴)Q²`, relative `O(Q^{−2})`; the only place §10 feels it is `FamRvMLower`,
     recorded there and at `ZetaQ.Family.size`.
  6. ✅ **`exists_famTailInputsD` / `famTailInputsD_at`.** The COMMON `θ₀` is `theta0Fam`, and
     `theta0Q_le_theta0Fam` — the statement that gives it — was proved in `Tail.lean` all along
     and cited by nothing outside that file.
  7. ⬜ `trace_row` / `frobenius_row`. `frobenius_row`'s entry is superseded by its own
     docstring; `trace_row` stands. The distinction matters: the Frobenius side has a proved
     bridge in `Zones` §14, while the trace side has no analogue — `Ends`'s cap-free `_L` chain
     covers `Σ_{k,l} G²` only, and every route through `ThmE.FactsChi` consumes `lam_le_one` to
     reach the Rule-17-forbidden `X ≤ T`. That no non-circular hypothesis pattern exists in
     this file's vocabulary is settled on the mechanism, not on absence of search: the `EFChi`
     identifications are identities, not evaluations, and the only quantitative seam downstream,
     `Zeta23.ThmE.seamBChi`, carries an error `C₁√X/a ≈ 10⁶⁷` at `Q = 10¹⁰⁰` against a
     `𝒩 ≈ 7×10⁹` per character — which is why the paper uses §5's family Ramanujan step instead.

`hsize`, `hQ0`, `hfam`, `hloc` and `hNII` are NOT clauses of this statement: they are consumed
by `ends_row` and `buffer_row_proved`, neither of which appears below (`endsFam` does not
occur, and `r₃` is supplied by item 2).

**Item 2 is of a different KIND from the rest.** Items 3–7 are unproved deliverables of other
sections: each becomes a theorem. Item 2 is an assumption. Because this statement is frozen and
existentially quantified it cannot carry the hypothesis, so the honest reading is that **this
`sorry`, once items 3–7 land, would close only *modulo* `SharpZeroDensity`** — and the form
that says so explicitly, with the hypothesis on the left, is `assembly_clauses_at_design`.

**And item 7 is blocked for a reason not on the list at all:** `DesignOfRecord` pins the design
window, and at the flat taper `frobenius_row` is not provable by the paper's method (see "the
design window must carry a profile" in the module header). Closing this statement requires the
profile-weighted design *and* a restatement at a reachable constant.

✅ **BOTH WERE DONE, ELSEWHERE, AND THIS STATEMENT IS FROZEN.** The design window was repaired
and the assembly was restated at the CERTIFIED constant and without `SharpZeroDensity`:
`ZetaQ/JoinCert.lean` (`assembly_at_lamStar_cert`), `ZetaQ/JoinProved.lean` (the buffer row at
the PROVED q-uniform local-count constant in place of the sharp density) and `ZetaQ/Margin.lean`
(the margin design, removing `r + ε ≤ 7`). Consequently **the artifact declares exactly ONE
assumption, §6's `ZetaQ.l2_concentration_exists`**, not two: `SharpZeroDensity` is not used by
any shipped theorem. This declaration keeps the paper's ten-digit, sharp-density statement and
its `sorry`; **nothing in the tree consumes it** (`audit/RevDepZetaQ.lean`). -/
theorem assembly_at_lamStar (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ∃ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P ∧
        ∃ r₁ r₂ r₃ r₄ r₅ θ₀ : ℝ,
          0 ≤ θ₀ ∧
          (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn ∧
          frobSqGhatFam P F Qn ≤ (F.kappaC + r₂) * NfamQ P F Qn ∧
          NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn ∧
          Btr P F Qn θ₀ ≤ r₄ * NfamQ P F Qn ∧
          BF P F Qn θ₀ ≤ r₅ * Real.sqrt (NfamQ P F Qn) ∧
          4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
              + 2 * r₅ * Real.sqrt (F.kappaC + r₂) + r₅ ^ 2 ≤ budgetTotal F P ∧
          (2 - F.kappaC - budgetTotal F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := sorry

/-- **✅ The assembly → Theorem 1 rate step, PROVED — and the 🚩 finding that it needs one
clause `assembly_at_lamStar` does not deliver.**

This is the whole of "`theorem_one_generic` = `assembly_at_lamStar` + `budgetTotal_isBigO` +
`2 − κ_C = P`", isolated as its own lemma and discharged. Given

  * a **design map** `design : ℝ → ParamsQ` with `∀ᶠ Q, DesignOfRecord F r ε Q (design Q)`
    (this is `assembly_at_lamStar`'s existential, made into a function by choice — checklist
    item 1 there),
  * `hD0`, the `D₀ = O(ℒ²)` clause `budgetTotal_isBigO` consumes in exactly one row (`L₄`),
  * and `hassembly`, `assembly_at_lamStar`'s **last** conclusion clause at each `Qn`,

Theorem 1's r-generic shape follows: `budgetTotal_isBigO` turns `budgetTotal` into
`c·log log Q/log Q`, `two_sub_kappaC` turns `2 − κ_C` into `F.payoff` (= `Pconst` for
`Family.qle`, `PconstDyadic` for `Family.dyadic`), and `NfamCount_nonneg` licenses the one
`mul_le_mul`. Stated family-generically so that **both** `theorem_one_generic` and
`corollary_two_dyadic` are one `exact` from it.

### 🚩 THE FINDING: `theorem_one_generic` is NOT "one `calc` from the assembly"

Earlier passes recorded `theorem_one_generic` and `corollary_two_dyadic` as "one `calc` from
the assembly, and neither is a fill difficulty". **That is wrong, and this lemma isolates
exactly why.** `assembly_at_lamStar`'s conclusion is an *existential over `P`* whose only
constraints on `P.D0` are `DesignOfRecord`'s, i.e. `SideCondD0range`'s `10L ≤ D₀ ≤ T/3`
together with the closing clause — **which is vacuous** (module header; `DesignOfRecord`;
`budgetTotal_isBigO`). So the assembly is satisfied by designs with `D₀ = T/3`, at which

    L₄ = 6·D₀/T = 2,   hence  budgetTotal F P ≥ 2 − o(1),

a CONSTANT. Theorem 1's conclusion needs `budgetTotal F P ≤ c·log log Q/log Q → 0` for a
*fixed* `c`, so no `c` can work against such a design: the step
`P − c·log log Q/log Q ≤ 2 − κ_C − budgetTotal F P` fails for every large `Q`. This is the
**same** `DesignOfRecord` vacuity that made `budgetTotal_isBigO` false, biting a second
time — and it is not repairable inside `theorem_one_generic`, whose statement mentions
neither `D₀` nor a design map, and which is TRUE (it is the paper's theorem), so D14/D17 give
no licence to add a hypothesis to it.

**The repair is the coordinating call this file has now flagged three times**: make
`DesignOfRecord` itself imply `D₀ = O(ℒ²)`, either by giving `ClosingCondition` LEMMA_QT.b(5)'s
*fixed* prefactor (what `budget_q.closing_margin` computes with) instead of an existentially
quantified one, or by giving `SideCondD0range` a real upper bound. Then `hD0` becomes
derivable from `hdesign`, `budgetTotal_isBigO` loses its extra hypothesis, and
`theorem_one_generic` really is one `exact` from `assembly_at_lamStar` plus this lemma.

### ✅ UPDATE: the coordinating call was TAKEN — decision **D27**

The first of the two options was adopted: `DesignOfRecord`'s closing clause is now
`ClosingAtDesign`, §7.2's condition at LEMMA_QT §QT.b(5)'s determinate `θ₀^Gev` prefactor met
with margin 0. `hD0` is a theorem (`design_D0_isBigO`), `budgetTotal_isBigO_of_design` is the
hypothesis-free form of the budget asymptotic, and `theorem_one_generic` /
`corollary_two_dyadic` are proved from `assembly_at_lamStar` — via
`payoff_rate_of_assembly`, which is this lemma re-indexed over the naturals (the assembly
supplies design points at natural `Qn` only, and `DesignOfRecord … Q P` pins `P.Q = Q`, so the
real-variable `design : ℝ → ParamsQ` this lemma takes is genuinely not extractable from it).

**This lemma's statement and proof are unchanged**, and the diagnosis above is left standing
as the record of why the coordinating call had to be made. The honest statement of the gap is
now: **Theorem 1 is blocked on `assembly_at_lamStar` alone** — the design-point construction,
the §9/§7 bridge to §3's display, and `trace_row`/`frobenius_row`.

Paper §10.3, §10.5, §1.1.
Depends on: `budgetTotal_isBigO`, `ZetaQ.two_sub_kappaC`,
`ZetaQ.NfamCount_nonneg`.
Rule 17: `hD0` is an `O(ℒ²)` UPPER bound on the FREE `D₀`, forced by §7.2's margin-0 closing
condition; it is emphatically not `D₀ = √T` (see `budgetTotal_isBigO`'s Rule-17 note). No
λ ≤ 1 and no X ≤ T occurs. -/
theorem payoff_rate_of_designs (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q))
    (hD0 : (fun Q => (design Q).D0) =O[atTop] fun Q => Real.log Q ^ 2)
    (hassembly : ∀ Qn : ℕ,
      (2 - F.kappaC - budgetTotal F (design (Qn : ℝ))) * NfamQ (design (Qn : ℝ)) F Qn
        ≤ N0sFamQ (design (Qn : ℝ)) F Qn) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (F.payoff - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨c0, hc0⟩ :=
    Asymptotics.isBigO_iff.mp (budgetTotal_isBigO F r ε hr hε design hdesign hD0)
  have hev : ∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q) ∧
      ‖budgetTotal F (design Q)‖ ≤ c0 * ‖Real.log (Real.log Q) / Real.log Q‖ ∧
      (1 : ℝ) ≤ Real.log Q ∧ (0 : ℝ) ≤ Real.log (Real.log Q) := by
    filter_upwards [hdesign, hc0,
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (0 : ℝ)]
      with Q h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.mp hev
  refine ⟨Q₁, |c0| + 1, by positivity, ?_⟩
  intro Qn hQn
  obtain ⟨hdes, hb, hu1, hv0⟩ := hQ₁ (Qn : ℝ) hQn
  have hu0 : (0 : ℝ) < Real.log (Qn : ℝ) := by linarith
  have hvu : (0 : ℝ) ≤ Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ) :=
    div_nonneg hv0 hu0.le
  have hT : (design (Qn : ℝ)).T = Twin (Qn : ℝ) r ε := hdes.2.2.1
  -- the rate bound on the budget total, at a nonnegative constant
  have hbt : budgetTotal F (design (Qn : ℝ))
      ≤ (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hvu] at hb
    have h1 : budgetTotal F (design (Qn : ℝ)) ≤ |budgetTotal F (design (Qn : ℝ))| :=
      le_abs_self _
    have h2 : c0 * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
        ≤ (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self c0]) hvu
    linarith
  -- the assembly's last clause, at the design's own window `I = [T, 2T]`
  have hkey := hassembly Qn
  have hNfam : NfamQ (design (Qn : ℝ)) F Qn
      = NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
    unfold NfamQ; rw [hT]
  have hN0s : N0sFamQ (design (Qn : ℝ)) F Qn
      = N0sFamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
    unfold N0sFamQ; rw [hT]
  rw [hNfam, hN0s] at hkey
  have hN : (0 : ℝ) ≤ NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) :=
    NfamCount_nonneg _ _ _ _
  have hcoef : F.payoff - (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
      ≤ 2 - F.kappaC - budgetTotal F (design (Qn : ℝ)) := by
    rw [two_sub_kappaC]; linarith
  have hgd : (|c0| + 1) * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)
      = (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)) :=
    mul_div_assoc _ _ _
  rw [hgd]
  exact le_trans (mul_le_mul_of_nonneg_right hcoef hN) hkey

/-- **✅ The assembly → Theorem 1 rate step, taking the assembly EXACTLY as
`assembly_at_lamStar` states it (D27).**

`payoff_rate_of_designs` above is the same content phrased against a *real*-variable design
map `design : ℝ → ParamsQ` with `∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q)`, because
that is the shape `budgetTotal_isBigO` is stated in. `assembly_at_lamStar` does not deliver
that shape and cannot be made to: it produces a design point only at each **natural** `Qn`
(and only above its own `Q₀`), whereas `DesignOfRecord F r ε Q P` pins `P.Q = Q`, so a design
at real `Q` is a genuinely different object that no clause of the assembly asserts to exist.

So the rate step is redone here at the assembly's own indexing. Nothing about the argument
changes — `budgetTotal_le_of_regime` is already pointwise, and `budgetTotal_isBigO` is only
its `filter_upwards` wrapper — and with D27 in place the missing `hD0` is supplied pointwise
by `D0_le_of_design` instead of hypothesised. The explicit rate constant that comes out is
`c = 20(r+ε) + 120200`, dominated by the crude `D₀`-constant of `D0_le_of_design`; the
paper's own (computed, not proved) value is `s(r+K) ≈ 3.3` (`rateConst`), and the gap is
entirely that crudeness, not the argument.

Paper §10.3, §10.5, §1.1.
Depends on: `D0_le_of_design`, `budgetTotal_le_of_regime`,
`ZetaQ.two_sub_kappaC`, `ZetaQ.NfamCount_nonneg`.
Rule 17: the `D₀` bound consumed here is `D0_le_of_design`'s `O(ℒ²)`, from §7.2's closing
condition; no `λ ≤ 1`, no `X ≤ T`, no `D₀ = √T`. -/
theorem payoff_rate_of_assembly (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hassembly : ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ∃ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P ∧
        (2 - F.kappaC - budgetTotal F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (F.payoff - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₀, hQ₀⟩ := hassembly
  have hK : (0 : ℝ) < 2 * (r + ε) + 10 := by linarith
  have hlo := isLittleO_loglog_log.def (c := 1 / (2 * (r + ε) + 10)) (by positivity)
  have hev : ∀ᶠ Q in atTop, (0 : ℝ) < Q ∧ 8 ≤ Real.log Q ∧ 3 ≤ Real.log (Real.log Q)
      ∧ (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q := by
    filter_upwards [hlo, eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (3 : ℝ)]
      with Q hlo' hQ0 hu hv'
    have hv : (3 : ℝ) ≤ Real.log (Real.log Q) := hv'
    have hu0 : (0 : ℝ) < Real.log Q := by linarith
    have hv0 : (0 : ℝ) < Real.log (Real.log Q) := by linarith
    refine ⟨hQ0, hu, hv, ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0.le,
      abs_of_nonneg hu0.le] at hlo'
    have h2 := mul_le_mul_of_nonneg_left hlo' hK.le
    rw [show (2 * (r + ε) + 10) * (1 / (2 * (r + ε) + 10) * Real.log Q) = Real.log Q by
      field_simp] at h2
    exact h2
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.mp hev
  -- D35 (reversing D34): the buffer row is `L₄` again, so its constant is back to `6·c`
  refine ⟨max Q₀ Q₁, 20 * (r + ε) + 6 * 20000 + 200, by linarith, ?_⟩
  intro Qn hQn
  obtain ⟨P, hdes, hlast⟩ := hQ₀ Qn (le_trans (le_max_left _ _) hQn)
  obtain ⟨hQ0, hu, hv, hvu⟩ := hQ₁ (Qn : ℝ) (le_trans (le_max_right _ _) hQn)
  have hD := D0_le_of_design F r ε (Qn : ℝ) P hr hε hdes hQ0 hu hv hvu
  obtain ⟨-, hle⟩ :=
    budgetTotal_le_of_regime F r ε (Qn : ℝ) 20000 P hr hε (by norm_num) hdes hQ0 hu hv hvu hD
  -- the counts, at the design's own window `I = [T, 2T]`
  have hT : P.T = Twin (Qn : ℝ) r ε := hdes.2.2.1
  have hNfam : NfamQ P F Qn
      = NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
    unfold NfamQ; rw [hT]
  have hN0s : N0sFamQ P F Qn
      = N0sFamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
    unfold N0sFamQ; rw [hT]
  rw [hNfam, hN0s] at hlast
  have hN : (0 : ℝ) ≤ NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) :=
    NfamCount_nonneg _ _ _ _
  have hcoef : F.payoff
      - (20 * (r + ε) + 6 * 20000 + 200)
          * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)
      ≤ 2 - F.kappaC - budgetTotal F P := by
    rw [two_sub_kappaC, mul_div_assoc]
    linarith
  exact le_trans (mul_le_mul_of_nonneg_right hcoef hN) hlast

/-- **Theorem 1, r-generic form** — the parenthetical of: "The same statement
holds at `T = (log Q)^{r+ε}` for every `r ≥ 3`, with `c = c(r, ε)` effectively computable".
The budget constant `s(r+K)` at the design `(r,K) = (3.5,3)` is ≈ 3.3 — a *computed, not
proved* property, explicitly outside this statement (§10.3's remark; `rateConst`).

Paper §1.1.
Depends on: `assembly_at_lamStar`, `payoff_rate_of_assembly`. Rule 17: as `theorem_one`.

### ✅ PROVED from `assembly_at_lamStar` — decision **D27** closed the gap

Fill pass 7 recorded, correctly, that this was **not** one `calc` from the assembly: the
derivation "assembly + `budgetTotal_isBigO` + `2 − κ_C = Pconst`" additionally needs
`hD0 : D₀ = O((log Q)²)`, and while `DesignOfRecord`'s closing clause was the vacuous
`∃ logPrefactor eta, …` the assembly could not supply it (`D₀ = T/3` was admissible, at which
`L₄ = 2` and `budgetTotal` is a constant, so no fixed `c` works).

D27 pinned that clause to LEMMA_QT §QT.b(5)'s `θ₀^Gev` prefactor at margin 0
(`ClosingAtDesign`), and `hD0` became a theorem (`design_D0_isBigO`, pointwise
`D0_le_of_design`). So this is now exactly one `exact` from the assembly, via
`payoff_rate_of_assembly` — which is `payoff_rate_of_designs` re-indexed over the naturals,
because the assembly produces design points at natural `Qn` only and `DesignOfRecord … Q P`
pins `P.Q = Q` (see `payoff_rate_of_assembly` for why that re-indexing is unavoidable rather
than cosmetic). The whole remaining content of Theorem 1 is `assembly_at_lamStar`.
`#print axioms theorem_one_generic` still reports `sorryAx`, through that one statement. -/
theorem theorem_one_generic (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (Pconst - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  refine payoff_rate_of_assembly Family.qle r ε hr hε ?_
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar Family.qle r ε hr hε
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  -- the last of the eight clauses: §3's display at the design's own budget total
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- **Theorem 1** — paper §1.1, verbatim:

> Fix ε > 0. There are Q₀(ε) and an effectively computable c(ε) such that for Q ≥ Q₀(ε) and
> T = T(Q) = (log Q)^{3+ε}, unconditionally,
> `Σ_{χ∈𝔉_Q} N^s_{0,χ}(T, 2T) ≥ (P − c(ε)·(log log Q)/(log Q)) · Σ_{χ∈𝔉_Q} N_χ(T, 2T)`,
> where **P = 0.7212835668…** is the value of an explicit variational problem (§10) at
> C = π⁴/18.

`𝔉_Q` is the primitive characters of modulus `q ≤ Q` (`Family.qle`); `N^s_{0,χ}` counts the
zeros that are **simple and on the critical line**. `P` is the frozen `ZetaQ.Pconst`, which
`ZetaQ/Payoff.lean` ships as a FEASIBILITY certificate (`≥ 0.7212`), not as an equality. Unconditional; **no ε-limit is taken** (§10.5).

**PROVED — as the `r = 3` instance of `theorem_one_generic`, which is declared just
above for that reason.**  This is a wiring step, not a mathematical one: the two statements
are literally the same proposition at `r := 3`, so the whole content is still owed by
`theorem_one_generic` (and, through it, by `assembly_at_lamStar`).  It is recorded this way
so that Theorem 1 lands automatically the moment §10.5's assembly does, and so that the
paper's own reading of §1.1 — the headline is the `r = 3` case of the parenthetical — is
visible in the tree.  `#print axioms theorem_one` still reports `sorryAx`.

Paper §1.1; assembled in §10.5.
Depends on: `theorem_one_generic`, and through it `assembly_at_lamStar`,
`prop_3_1_pair_moment_certificate`, `budgetTotal_isBigO`.
**Rule 17: CLEAN.** No λ, X or D₀ occurs in the statement at all; `λ*` and `D₀` are chosen
inside `assembly_at_lamStar`. `T = (log Q)^{3+ε}` is the paper's own regime hypothesis
(§2.2's buffer/rate trade), not a smuggle — and note it is `≥ (log Q)³`, i.e. `T` is
polylogarithmic in `Q` while `X = (QT/2π)^λ` is a power of `Q`: `X ≫ T` at every λ. -/
theorem theorem_one (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (Pconst - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.qle Qn (Twin (Qn : ℝ) 3 ε) (2 * Twin (Qn : ℝ) 3 ε)
        ≤ N0sFamCount Family.qle Qn (Twin (Qn : ℝ) 3 ε) (2 * Twin (Qn : ℝ) 3 ε) :=
  -- Theorem 1 IS the r-generic statement at `r = 3`: the two conclusions are the same
  -- proposition once `r := 3`, so nothing is proved here that is not proved there.  The
  -- mathematical content sits in `theorem_one_generic`, which is proved but routes through
  -- the frozen `assembly_at_lamStar` and so is `sorry`-DEPENDENT.  The theorems the artifact
  -- ships are the primed ones in `ZetaQ/Margin.lean`, at the certified constant; this
  -- ten-digit form is kept as the paper's own statement.
  theorem_one_generic 3 ε le_rfl hε

/-- **Corollary 2 (dyadic)** — paper §1.1, verbatim first sentence:

> The same holds for the dyadic subfamily `q ∈ (Q/2, Q]` with **P_dyad = 0.7099167448…**
> (C = 2π⁴/27, λ* = 1.1931581210), for every `T = (log Q)^{r+ε}`, `r ≥ 3`.

The remainder of §1.1's Corollary 2 is comparison prose ([CIS2], +14.99 points) and is
**not** formalized, by design.

Paper §1.1; §10.5's dyadic run at `C = 2π⁴/27`.
Depends on: `assembly_at_lamStar` at `Family.dyadic`,
`payoff_rate_of_assembly`. Rule 17: `λ*_dyad = 1.1931581210 > 1`, same as Theorem 1.

### ✅ PROVED from `assembly_at_lamStar` at `Family.dyadic` — same route as
### `theorem_one_generic`, unblocked by decision D27

`payoff_rate_of_assembly` is family-generic, so this is literally the same three lines at
`F := Family.dyadic` (where `F.payoff = PconstDyadic` by `rfl`). Fill pass 7 recorded it as
blocked by the missing `hD0`; D27 pinned `DesignOfRecord`'s closing clause to LEMMA_QT
§QT.b(5)'s prefactor at margin 0, `hD0` became `design_D0_isBigO`, and the block is gone.
`Family.kappaC` and `Family.payoff` carry the dyadic constants, so nothing else moves. -/
theorem corollary_two_dyadic (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (PconstDyadic - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  refine payoff_rate_of_assembly Family.dyadic r ε hr hε ?_
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar Family.dyadic r ε hr hε
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩


/-! # §9 → §10.5: THE TRACE RUNGS — ledger rows 1 and 2

`trace_row` is the trace side of Prop 3.1(ii).  §10.2's 17-row ledger splits it into row 1 (the
`μ_q` archimedean main term), row 2 (the prime part, class **[R]** = family Ramanujan) and row 3
(RvM per character).  **Row 2 is proved here**, and with it `trGhatFam` splits into `famMuPart`
+ `famPPart`; row 1 is what remains, and `trace_row_of_muPart` names it once, precisely, without
restating the conclusion.  Every declaration below is proved.

**This section is the first citation of `ZetaQ/CharSums.lean` — and of `ZetaQ/Zones.lean` — from
anywhere on the spine.**  `Budget` has imported `Zones` since fill pass 9 and until now used
nothing from it. -/

section TraceRungs

open Zones
open scoped ArithmeticFunction ComplexConjugate
open MeasureTheory Topology


/-! ### 1. The trace, entrywise (mirror of `Zones.frobSq_hatQ_gridGram_entrywise`) -/

theorem rtrace_hatQ_gridGram_entrywise (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    RHLinalg.rtrace (hatQ P (gridGram P χ))
      = ((P.aQ * P.LB ^ 2)⁻¹) * ∑ k : Fin P.dQ, gridGramEntry P χ (k : ℕ) (k : ℕ) := by
  rw [hatQ, Zeta23.Assembly.rtrace_smul_ofReal]
  congr 1
  simp [RHLinalg.rtrace, Matrix.trace, Matrix.diag, gridGram]

theorem trGhatFam_entrywise (P : ParamsQ) (F : Family) (Qn : ℕ) :
    trGhatFam P F Qn
      = familySum F Qn (fun _q χ => ((P.aQ * P.LB ^ 2)⁻¹)
          * ∑ k : Fin P.dQ, gridGramEntry P χ (k : ℕ) (k : ℕ)) := by
  unfold trGhatFam familySum
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ =>
    rtrace_hatQ_gridGram_entrywise P χ

/-! ### 2. `primLinSum 1 n = 1` -/

theorem primitiveChars_one : primitiveChars 1 = {(1 : DirichletCharacter ℂ 1)} := by
  ext χ
  simp only [primitiveChars, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  exact ⟨fun _ => DirichletCharacter.level_one χ,
    fun h => by rw [h]; exact DirichletCharacter.isPrimitive_one_level_one⟩

theorem primLinSum_one (n : ℕ) : primLinSum 1 n = 1 := by
  rw [primLinSum, primitiveChars_one]
  have h1 : ((n : ℕ) : ZMod 1) = 1 := Subsingleton.elim _ _
  simp [h1]

/-! ### 3. bridging the abstract setting -/

open Zeta23.PrimeSide in
theorem gridGramEntry_eq_GentryChiA (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (k l : ℤ) :
    gridGramEntry P χ k l
      = Zeta23.ThmE.GentryChiA (parity χ) q (fun n => χ (n : ZMod q))
          (Ends.toSetting P) (P.toParams.localFun P.T) k l := by
  rw [EFChi.gridGramEntry_eq P hl χ k l]
  rfl
open Zeta23.PrimeSide
open Zeta23.ThmE

/-! ### The per-character grid sum of P-parts, in kernel form -/

theorem Ppart_grid_eq {cϱ : ℝ} {p : Setting} {Floc : LocalFun}
    (hF : LocalHypsCoreW cϱ p Floc) (c : ℕ → ℂ) :
    ∑ k ∈ Finset.range p.d, ∫ r, Floc.phiHat r ^ 2 * PXc c p.X (p.tau k + r)
      = -2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
            * (c n * ∑ k ∈ Finset.range p.d,
                Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re := by
  have hre : ∀ (z : ℂ) (θ : ℝ), z.re * Real.cos θ + z.im * Real.sin θ
      = (z * Complex.exp ((-θ : ℝ) * Complex.I)).re := by
    intro z θ
    rw [Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im, Real.cos_neg, Real.sin_neg, Complex.I_re, Complex.I_im]
    ring
  simp_rw [P_part_chi_eq hF c]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hre (c n) (p.tau k * Real.log n)]

/-! ### The family character sum -/

/-- `Σ_{q ∈ 𝔉's moduli} Σ*_{χ mod q} χ(n)` — the certificate family's linear character sum. -/
def famChiSum (F : Family) (Qn : ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q, χ (n : ZMod q)


theorem famChiSum_eq_sum_primLinSum (F : Family) (Qn : ℕ) (n : ℕ) :
    famChiSum F Qn n = ∑ q ∈ F.moduli Qn, primLinSum q n := rfl

/-! ### The FAMILY grid sum of P-parts: identity and Ramanujan bound -/

theorem famPpart_grid_eq {cϱ : ℝ} {p : Setting} {Floc : LocalFun}
    (hF : LocalHypsCoreW cϱ p Floc) (F : Family) (Qn : ℕ) :
    ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q,
        ∑ k ∈ Finset.range p.d, ∫ r, Floc.phiHat r ^ 2 *
          PXc (fun n => χ (n : ZMod q)) p.X (p.tau k + r)
      = -2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
            * (famChiSum F Qn n * ∑ k ∈ Finset.range p.d,
                Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re := by
  classical
  have key : ∀ (n : ℕ) (Kc : ℂ) (An : ℝ),
      (∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q, An * ((χ (n : ZMod q)) * Kc).re)
        = An * (famChiSum F Qn n * Kc).re := by
    intro n Kc An
    simp only [famChiSum, Finset.sum_mul, Complex.re_sum, Finset.mul_sum]
  have hpull : ∀ q : ℕ, (∑ χ ∈ primitiveChars q, (-2 : ℝ) * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
        ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
          * ((χ (n : ZMod q)) * ∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re)
      = -2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ∑ χ ∈ primitiveChars q,
          ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
            * ((χ (n : ZMod q)) * ∑ k ∈ Finset.range p.d,
                Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re := by
    intro q
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun χ _ =>
        Ppart_grid_eq hF (fun n => χ (n : ZMod q))))]
  rw [Finset.sum_congr rfl (fun q _ => hpull q), ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun n _ => key n _ _

theorem famPpart_bound {cϱ : ℝ} {p : Setting} {Floc : LocalFun}
    (hF : LocalHypsCoreW cϱ p Floc) (F : Family) (Qn : ℕ) :
    |∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q,
        ∑ k ∈ Finset.range p.d, ∫ r, Floc.phiHat r ^ 2 *
          PXc (fun n => χ (n : ZMod q)) p.X (p.tau k + r)|
      ≤ p.L ^ 2 / Real.log 2
        * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
            (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖ := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 ≠ 0 := ne_of_gt hlog2
  rw [famPpart_grid_eq hF F Qn, abs_mul, abs_neg, abs_two]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      |((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
        * (famChiSum F Qn n * ∑ k ∈ Finset.range p.d,
            Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
      ≤ ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖)
          * (p.L ^ 2 / (2 * Real.log 2)) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
    have ha : (0:ℝ) ≤ (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) := by
      have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hy : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn2)
      have hA0 := hF.Aphi_nonneg (Real.log n)
      have hre_le : |(famChiSum F Qn n * ∑ k ∈ Finset.range p.d,
            Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
          ≤ ‖famChiSum F Qn n‖ * ‖∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖ := by
        rw [← norm_mul]
        exact Complex.abs_re_le_norm _
      have hkey := Aphi_mul_norm_tauKernel_le hF hy
      have hnorm0 : (0:ℝ) ≤ ‖famChiSum F Qn n‖ := norm_nonneg _
      calc |((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
            * (famChiSum F Qn n * ∑ k ∈ Finset.range p.d,
                Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
          = ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))) * (Floc.Aphi (Real.log n)
              * |(famChiSum F Qn n * ∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hA0]; ring
        _ ≤ ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))) * (Floc.Aphi (Real.log n)
              * (‖famChiSum F Qn n‖ * ‖∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖)) := by
            gcongr
        _ = ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))) * (‖famChiSum F Qn n‖
              * (Floc.Aphi (Real.log n) * ‖∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖)) := by ring
        _ ≤ ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))) * (‖famChiSum F Qn n‖
              * (p.L ^ 2 / (2 * Real.log 2))) := by
            gcongr
        _ = ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖)
              * (p.L ^ 2 / (2 * Real.log 2)) := by ring
  calc 2 * |∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
        ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * Floc.Aphi (Real.log n))
          * (famChiSum F Qn n * ∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
      ≤ 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖)
            * (p.L ^ 2 / (2 * Real.log 2)) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = p.L ^ 2 / Real.log 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖ := by
        rw [← Finset.sum_mul]
        generalize (∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖) = Ssum
        field_simp


/-! ### §5's Ramanujan bound on the family character sum -/

theorem Icc_one_eq_Ioc_zero' (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

theorem famChiSum_norm_le (F : Family) (Qn n : ℕ) (hn : 2 ≤ n) :
    ‖famChiSum F Qn n‖ ≤ 3 / 2 * (Qn : ℝ) * (tau (n - 1) : ℝ) + 1 := by
  have hτ : (0:ℝ) ≤ (tau (n - 1) : ℝ) := Nat.cast_nonneg _
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  -- `famChiSum` reads `F` only through `F.moduli`, and Corollary 3's four families reuse the
  -- two modulus ranges verbatim, so there are still only two cases to do.
  have hred : famChiSum F Qn n = famChiSum Family.qle Qn n
      ∨ famChiSum F Qn n = famChiSum Family.dyadic Qn n := by
    cases F
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  rcases hred with hred | hred <;> rw [hred]
  case inl =>
      rcases Nat.eq_zero_or_pos Qn with h0 | h1
      · subst h0
        have hemp : Family.moduli Family.qle 0 = (∅ : Finset ℕ) := by
          simp [Family.moduli]
        rw [famChiSum, hemp, Finset.sum_empty]
        norm_num
      · have hins : Finset.Icc 1 Qn = insert 1 (Finset.Icc 2 Qn) := Icc_one_eq_insert Qn h1
        have hnot : (1:ℕ) ∉ Finset.Icc 2 Qn := by simp
        have hsplit : famLinSum Qn n = 1 + famChiSum Family.qle Qn n := by
          rw [famChiSum_eq_sum_primLinSum, famLinSum,
            show Family.moduli Family.qle Qn = Finset.Icc 2 Qn from rfl, hins,
            Finset.sum_insert hnot, primLinSum_one]
        have heq : famChiSum Family.qle Qn n = famLinSum Qn n - 1 := by rw [hsplit]; ring
        have h5 := lemma5_2_crude_linear Qn n hn
        rw [heq]
        calc ‖famLinSum Qn n - 1‖ ≤ ‖famLinSum Qn n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ (Qn : ℝ) * (tau (n - 1) : ℝ) + 1 := by rw [norm_one]; linarith
          _ ≤ 3 / 2 * (Qn : ℝ) * (tau (n - 1) : ℝ) + 1 := by
              nlinarith [mul_nonneg hQ hτ]
  case inr =>
      have hcons := Finset.sum_Ioc_consecutive (fun q => primLinSum q n)
        (Nat.zero_le (Qn / 2)) (Nat.div_le_self Qn 2)
      have heq : famChiSum Family.dyadic Qn n = famLinSum Qn n - famLinSum (Qn / 2) n := by
        rw [famChiSum_eq_sum_primLinSum,
          show Family.moduli Family.dyadic Qn = Finset.Ioc (Qn / 2) Qn from rfl,
          famLinSum, famLinSum, Icc_one_eq_Ioc_zero', Icc_one_eq_Ioc_zero', ← hcons]
        ring
      have h5 := lemma5_2_crude_linear Qn n hn
      have h5' := lemma5_2_crude_linear (Qn / 2) n hn
      have hhalf : ((Qn / 2 : ℕ) : ℝ) ≤ (Qn : ℝ) / 2 := Nat.cast_div_le
      rw [heq]
      calc ‖famLinSum Qn n - famLinSum (Qn / 2) n‖
          ≤ ‖famLinSum Qn n‖ + ‖famLinSum (Qn / 2) n‖ := norm_sub_le _ _
        _ ≤ (Qn : ℝ) * (tau (n - 1) : ℝ) + ((Qn / 2 : ℕ) : ℝ) * (tau (n - 1) : ℝ) := by
            linarith
        _ ≤ 3 / 2 * (Qn : ℝ) * (tau (n - 1) : ℝ) + 1 := by
            nlinarith [mul_le_mul_of_nonneg_right hhalf hτ]

/-! ### Toolkit: the divisor-weighted square-root sum -/

theorem sum_inv_Icc_le (K : ℕ) :
    ∑ d ∈ Finset.Icc 1 K, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (K : ℝ) := by
  have h := harmonic_le_one_add_log K
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

theorem sum_tau_div_sqrt_le (Y : ℕ) :
    ∑ k ∈ Finset.Icc 1 Y, (tau k : ℝ) / Real.sqrt (k : ℝ)
      ≤ 2 * Real.sqrt (Y : ℝ) * (1 + Real.log (Y : ℝ)) := by
  classical
  have hcount : ∀ k ∈ Finset.Icc 1 Y,
      (tau k : ℝ) / Real.sqrt (k : ℝ)
        = ∑ d ∈ Finset.Icc 1 Y, (if d ∣ k then (1 : ℝ) / Real.sqrt (k : ℝ) else 0) := by
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
    ring
  rw [Finset.sum_congr rfl hcount, Finset.sum_comm]
  have hinner : ∀ d ∈ Finset.Icc 1 Y,
      ∑ k ∈ Finset.Icc 1 Y, (if d ∣ k then (1 : ℝ) / Real.sqrt (k : ℝ) else 0)
        ≤ 2 * Real.sqrt (Y : ℝ) / (d : ℝ) := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    have hd0 : 0 < d := hd1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdsq : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
    have hne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hdsq
    rw [← Finset.sum_filter]
    have hbij : ∑ k ∈ (Finset.Icc 1 Y).filter (fun k => d ∣ k), (1 : ℝ) / Real.sqrt (k : ℝ)
        = ∑ j ∈ Finset.Icc 1 (Y / d), (1 : ℝ) / Real.sqrt ((d : ℝ) * (j : ℝ)) := by
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
        rw [Nat.cast_mul]
    rw [hbij]
    have hfac : ∀ j : ℕ, (1 : ℝ) / Real.sqrt ((d : ℝ) * (j : ℝ))
        = (1 / Real.sqrt (d : ℝ)) * (1 / Real.sqrt (j : ℝ)) := by
      intro j
      rw [Real.sqrt_mul (by positivity)]
      field_simp
    simp_rw [hfac]
    rw [← Finset.mul_sum, Icc_one_eq_Ioc_zero']
    have hs := sum_one_div_sqrt_le (Y / d)
    have hsd : Real.sqrt ((Y / d : ℕ) : ℝ) ≤ Real.sqrt ((Y : ℝ) / (d : ℝ)) :=
      Real.sqrt_le_sqrt Nat.cast_div_le
    have hstep : ∑ n ∈ Finset.Ioc 0 (Y / d), (1 : ℝ) / Real.sqrt (n : ℝ)
        ≤ 2 * Real.sqrt ((Y : ℝ) / (d : ℝ)) := by linarith
    have hdiv : Real.sqrt ((Y : ℝ) / (d : ℝ))
        = Real.sqrt (Y : ℝ) / Real.sqrt (d : ℝ) := by
      rw [div_eq_mul_inv, Real.sqrt_mul (Nat.cast_nonneg Y), Real.sqrt_inv, div_eq_mul_inv]
    have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
      Real.mul_self_sqrt hdR.le
    have hcollapse : (1 / Real.sqrt (d : ℝ)) * (2 * (Real.sqrt (Y : ℝ) / Real.sqrt (d : ℝ)))
        = 2 * Real.sqrt (Y : ℝ) / (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) := by
      field_simp
    calc (1 / Real.sqrt (d : ℝ)) * ∑ n ∈ Finset.Ioc 0 (Y / d), (1 : ℝ) / Real.sqrt (n : ℝ)
        ≤ (1 / Real.sqrt (d : ℝ)) * (2 * Real.sqrt ((Y : ℝ) / (d : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 2 * Real.sqrt (Y : ℝ) / (d : ℝ) := by rw [hdiv, hcollapse, hsq]
  refine (Finset.sum_le_sum hinner).trans ?_
  have hsplit : ∑ d ∈ Finset.Icc 1 Y, 2 * Real.sqrt (Y : ℝ) / (d : ℝ)
      = 2 * Real.sqrt (Y : ℝ) * ∑ d ∈ Finset.Icc 1 Y, (1 : ℝ) / (d : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (sum_inv_Icc_le Y) (by positivity)


theorem tau_zero : tau 0 = 0 := by simp [tau]

theorem sum_tau_pred_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
      ≤ 2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  classical
  have hterm : ∀ n ∈ Finset.Ioc 0 N,
      (tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)
        ≤ (tau (n - 1) : ℝ) / Real.sqrt ((n - 1 : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      subst this
      simp [tau_zero]
    · have hpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
        have : 1 ≤ n - 1 := by omega
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
      have hle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.sub_le n 1
      have hsq : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hle
      have hsqpos : (0 : ℝ) < Real.sqrt ((n - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hpos
      gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  have hshift : ∑ n ∈ Finset.Ioc 0 N, (tau (n - 1) : ℝ) / Real.sqrt ((n - 1 : ℕ) : ℝ)
      = ∑ k ∈ Finset.range N, (tau k : ℝ) / Real.sqrt (k : ℝ) := by
    refine Finset.sum_nbij' (fun n => n - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
      exact Finset.mem_range.mpr (by omega)
    · intro k hk
      have := Finset.mem_range.mp hk
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro n hn
      obtain ⟨hn0, _⟩ := Finset.mem_Ioc.mp hn
      omega
    · intro k _
      omega
    · intro n _
      rfl
  rw [hshift]
  have hz : ((tau 0 : ℝ) / Real.sqrt ((0 : ℕ) : ℝ)) = 0 := by simp [tau_zero]
  have herase : ∑ k ∈ (Finset.range N).erase 0, (tau k : ℝ) / Real.sqrt (k : ℝ)
      = ∑ k ∈ Finset.range N, (tau k : ℝ) / Real.sqrt (k : ℝ) :=
    Finset.sum_erase _ (by simp [tau_zero])
  rw [← herase]
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (sum_tau_div_sqrt_le N)
  · intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hkr : k < N := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k _ _
    positivity

theorem sum_famChiSum_weight_le (F : Family) (Qn N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖
      ≤ Real.log (N : ℝ)
          * (3 / 2 * (Qn : ℝ) * (2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)))
              + 2 * Real.sqrt (N : ℝ)) := by
  classical
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hstep : ∀ n ∈ Finset.Ioc 0 N,
      (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖
        ≤ Real.log (N : ℝ) * (3 / 2 * (Qn : ℝ) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ))
            + 1 / Real.sqrt (n : ℝ)) := by
    intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    have hnr : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hconv : (n : ℝ) ^ (-(1/2 : ℝ)) = 1 / Real.sqrt (n : ℝ) := by
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
    have hsq0 : (0:ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnr
    have hτ : (0:ℝ) ≤ (tau (n - 1) : ℝ) := Nat.cast_nonneg _
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have : (Λ 1 : ℝ) = 0 := by simp [ArithmeticFunction.vonMangoldt_apply_one]
      rw [this]
      have hrhs : 0 ≤ Real.log (N : ℝ) * (3 / 2 * (Qn : ℝ) *
          ((tau (1 - 1) : ℝ) / Real.sqrt ((1:ℕ) : ℝ)) + 1 / Real.sqrt ((1:ℕ) : ℝ)) := by
        have : (0:ℝ) ≤ 3 / 2 * (Qn : ℝ) * ((tau (1 - 1) : ℝ) / Real.sqrt ((1:ℕ) : ℝ))
            + 1 / Real.sqrt ((1:ℕ) : ℝ) := by positivity
        exact mul_nonneg hlog0 this
      simpa using hrhs
    · have hΛ := vonMangoldt_le_log_of_le n N (by omega) hnN
      have hΛ0 : (0:ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have hnorm := famChiSum_norm_le F Qn n h2
      rw [hconv]
      calc (Λ n : ℝ) * (1 / Real.sqrt (n : ℝ)) * ‖famChiSum F Qn n‖
          ≤ Real.log (N : ℝ) * (1 / Real.sqrt (n : ℝ))
              * (3 / 2 * (Qn : ℝ) * (tau (n - 1) : ℝ) + 1) := by
            gcongr
        _ = Real.log (N : ℝ) * (3 / 2 * (Qn : ℝ) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ))
              + 1 / Real.sqrt (n : ℝ)) := by
            field_simp
  refine (Finset.sum_le_sum hstep).trans ?_
  have hA := sum_tau_pred_div_sqrt_le N
  have hB : ∑ n ∈ Finset.Ioc 0 N, (1:ℝ) / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (N : ℝ) :=
    sum_one_div_sqrt_le N
  calc ∑ n ∈ Finset.Ioc 0 N, Real.log (N : ℝ)
          * (3 / 2 * (Qn : ℝ) * ((tau (n - 1) : ℝ) / Real.sqrt (n : ℝ)) + 1 / Real.sqrt (n : ℝ))
      = Real.log (N : ℝ) * (3 / 2 * (Qn : ℝ)
          * (∑ n ∈ Finset.Ioc 0 N, (tau (n - 1) : ℝ) / Real.sqrt (n : ℝ))
          + ∑ n ∈ Finset.Ioc 0 N, (1:ℝ) / Real.sqrt (n : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ Real.log (N : ℝ) * (3 / 2 * (Qn : ℝ)
          * (2 * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ))) + 2 * Real.sqrt (N : ℝ)) := by
        gcongr


/-! ### Row 2 of §10.2's ledger, at a valid design point -/

theorem one_le_l_of_valid {P : ParamsQ} (hP : P.Valid) : 1 ≤ Zeta23.l P.T := by
  have hT : (300:ℝ) ≤ P.T := by
    have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  rw [Zeta23.l, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  nlinarith

theorem one_le_XQ_of_valid {P : ParamsQ} (hP : P.Valid) : 1 ≤ P.XQ :=
  Real.one_le_exp (EFChi.LB_pos_of_valid hP).le

theorem famPpart_le (P : ParamsQ) (F : Family) (Qn : ℕ) (hP : P.Valid)
    (hw : SideCondWrange P) :
    |∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q, ∑ k ∈ Finset.range P.dQ,
        ∫ r, P.phiHatQ r ^ 2 * Zones.PXchi P χ (P.tauQ k + r)|
      ≤ P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2) := by
  have hl : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hlne : Zeta23.l P.T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hl)
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have hwL : P.w ≤ P.LB / 8 := by
    have := hw; unfold SideCondWrange at this; linarith
  have hF := Ends.S2_localHypsCoreW P hP hwL hl hX1
  have h := famPpart_bound hF F Qn
  rw [Ends.toSetting_d P hlne, Ends.toSetting_X P hlne, Ends.S1_toSetting_L P hlne] at h
  simp only [Ends.toSetting_tau P hlne] at h
  refine le_trans h ?_
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set N := ⌊P.XQ⌋₊ with hN
  have hNpos : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX1)
  have hNle : ((N : ℕ) : ℝ) ≤ P.XQ := Nat.floor_le (by linarith)
  have hs : Real.sqrt ((N : ℕ) : ℝ) ≤ Real.sqrt P.XQ := Real.sqrt_le_sqrt hNle
  have hs0 : (0:ℝ) ≤ Real.sqrt ((N : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hNr : (0:ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hlogX : Real.log P.XQ = P.LB := Real.log_exp _
  have ht : Real.log ((N : ℕ) : ℝ) ≤ P.LB := by
    rw [← hlogX]; exact Real.log_le_log hNr hNle
  have ht0 : (0:ℝ) ≤ Real.log ((N : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hNpos)
  have hQ : (0:ℝ) ≤ (Qn : ℝ) := Nat.cast_nonneg _
  calc P.LB ^ 2 / Real.log 2
        * ∑ n ∈ Finset.Ioc 0 N, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖famChiSum F Qn n‖
      ≤ P.LB ^ 2 / Real.log 2 * (Real.log ((N : ℕ) : ℝ)
          * (3 / 2 * (Qn : ℝ) * (2 * Real.sqrt ((N : ℕ) : ℝ) * (1 + Real.log ((N : ℕ) : ℝ)))
              + 2 * Real.sqrt ((N : ℕ) : ℝ))) := by
        have := sum_famChiSum_weight_le F Qn N
        have hcoef : (0:ℝ) ≤ P.LB ^ 2 / Real.log 2 := by positivity
        exact mul_le_mul_of_nonneg_left this hcoef
    _ ≤ P.LB ^ 2 / Real.log 2 * (P.LB
          * (3 / 2 * (Qn : ℝ) * (2 * Real.sqrt P.XQ * (1 + P.LB)) + 2 * Real.sqrt P.XQ)) := by
        have hcoef : (0:ℝ) ≤ P.LB ^ 2 / Real.log 2 := by positivity
        gcongr
    _ = P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2) := by
        ring


/-! ### The μ / prime split of the family trace -/

theorem one_le_of_mem_moduli {F : Family} {Qn q : ℕ} (hq : q ∈ F.moduli Qn) : 1 ≤ q := by
  cases F <;>
    · simp only [Family.moduli, Finset.mem_Icc, Finset.mem_Ioc] at hq
      omega

theorem coeffOK_char {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    Zeta23.ThmE.CoeffOK q (fun n => χ (n : ZMod q)) := by
  have : NeZero q := ⟨Nat.one_le_iff_ne_zero.mp hq⟩
  exact
    { norm_le := fun n => χ.norm_le_one _
      vanish := fun n hn => χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]) }

/-- The family μ_q-part of the trace (row 1 of §10.2's ledger, un-evaluated). -/
def famMuPart (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q, ∑ k ∈ Finset.range P.dQ,
      ∫ r, P.phiHatQ r ^ 2 * muDensity q χ (P.tauQ k + r)

/-- The family prime-part of the trace (row 2 of §10.2's ledger). -/
def famPPart (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q, ∑ k ∈ Finset.range P.dQ,
      ∫ r, P.phiHatQ r ^ 2 * Zones.PXchi P χ (P.tauQ k + r)

/-! **The same two parts at the family's OWN character set.**

`famMuPart` / `famPPart` above price every modulus at the FULL `ZetaQ.primitiveChars q`, while
`trGhatFam` is a `familySum` and ranges over `F.chars q` — about half of that on a parity
family. The split `trGhatFam = (aL²)⁻¹(famMuPart + famPPart)` is therefore not merely unproved
at a parity family, it is an equation between objects of different size. The honest split is at
the objects below, which are `famMuPart` / `famPPart` on the nose whenever `F.IsFull`. -/

/-- `famMuPart`, priced at the family's OWN character set. -/
def famMuPartChars (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, ∑ k ∈ Finset.range P.dQ,
      ∫ r, P.phiHatQ r ^ 2 * muDensity q χ (P.tauQ k + r)

/-- `famPPart`, priced at the family's OWN character set. -/
def famPPartChars (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, ∑ k ∈ Finset.range P.dQ,
      ∫ r, P.phiHatQ r ^ 2 * Zones.PXchi P χ (P.tauQ k + r)

/-- On a FULL family the re-spelling changes nothing. -/
theorem famMuPartChars_eq_of_isFull {F : Family} (h : F.IsFull) (P : ParamsQ) (Qn : ℕ) :
    famMuPartChars P F Qn = famMuPart P F Qn :=
  Finset.sum_congr rfl fun q _ => by rw [F.chars_eq_of_isFull h]

theorem famPPartChars_eq_of_isFull {F : Family} (h : F.IsFull) (P : ParamsQ) (Qn : ℕ) :
    famPPartChars P F Qn = famPPart P F Qn :=
  Finset.sum_congr rfl fun q _ => by rw [F.chars_eq_of_isFull h]

theorem sum_gridGramEntry_diag_eq (P : ParamsQ) (hP : P.Valid) (hw : SideCondWrange P)
    {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    ∑ k : Fin P.dQ, gridGramEntry P χ (k : ℕ) (k : ℕ)
      = (∑ k ∈ Finset.range P.dQ, ∫ r, P.phiHatQ r ^ 2 * muDensity q χ (P.tauQ k + r))
        + ∑ k ∈ Finset.range P.dQ, ∫ r, P.phiHatQ r ^ 2 * Zones.PXchi P χ (P.tauQ k + r) := by
  have hl : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hlne : Zeta23.l P.T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hl)
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hwL : P.w ≤ P.LB / 8 := by
    have := hw; unfold SideCondWrange at this; linarith
  have hF := Ends.S2_localHypsCoreW P hP hwL hl hX1
  have hT : (300:ℝ) ≤ P.T := by
    have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h
  have hΓ : Zeta23.ThmE.GammaFactsChi (parity χ) q :=
    Zeta23.ThmE.GammaChi.gammaFactsChi (by unfold parity; split <;> omega) hq
  have hc := coeffOK_char hq χ
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => gridGramEntry P χ (k : ℤ) (k : ℤ)) P.dQ,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ∈ Finset.range (Ends.toSetting P).d := by rwa [Ends.toSetting_d P hlne]
  have hτ : 0 < (Ends.toSetting P).tau (k : ℤ) := by
    have hmem := Zeta23.PrimeSide.Setting.tau_mem (Ends.toSetting P) hF.L_pos
      (by simp only [Ends.toSetting_T]; linarith) hkm
    have : (Ends.toSetting P).T ≤ (Ends.toSetting P).tau (k : ℤ) := hmem.1
    simp only [Ends.toSetting_T] at this
    linarith
  rw [gridGramEntry_eq_GentryChiA P hlne χ (k : ℤ) (k : ℤ),
    Zeta23.ThmE.GentryChiA_diag_eq hΓ hq hF hc (k : ℤ) hτ]
  simp only [Ends.toSetting_tau P hlne, Ends.toSetting_X P hlne]
  rfl

/-- **PROVED IN ALL SIX BRANCHES — at the family's own character set.**

`trGhatFam = (aL²)⁻¹(famMuPartChars + famPPartChars)`, with no `F.IsFull`.

**This is a CHANGE OF OBJECT, not a weakening.** The previous statement subtracted the
FULL-family `famMuPart` / `famPPart` (double sums over the frozen `ZetaQ.primitiveChars`)
from a `trGhatFam` that is a `familySum` over `F.chars`; on a parity family those differ by
a factor of about two, so the old statement was false there, not merely unproved. At the
family's own weights the proof is the pointwise `sum_gridGramEntry_diag_eq` under two
`Finset.sum_congr`s, uniformly in `F` — exactly what the old `sorry`'s docstring predicted.

`trGhatFam_eq_split_of_isFull` just below recovers the old statement verbatim on
`qle` / `dyadic`, so this really is a generalisation. The debt it moves downstream is the
§5-Ramanujan bound on `famPPartChars`, which is discharged for the parity families by
`ZetaQ.FamRows.abs_famPPartChars_le_of_not_isFull` (`ZetaQ/FrobRow9.lean`, where the even/odd
character sums `cEven` / `cOdd` live). -/
theorem trGhatFam_eq_split (P : ParamsQ) (F : Family) (Qn : ℕ) (hP : P.Valid)
    (hw : SideCondWrange P) :
    trGhatFam P F Qn
      = (P.aQ * P.LB ^ 2)⁻¹ * (famMuPartChars P F Qn + famPPartChars P F Qn) := by
  rw [trGhatFam_entrywise P F Qn]
  unfold familySum famMuPartChars famPPartChars
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  beta_reduce
  rw [sum_gridGramEntry_diag_eq P hP hw (one_le_of_mem_moduli hq) χ]

/-- The FULL-family split, recovered from the re-spelled one — the check that
`trGhatFam_eq_split` really generalises the statement it replaced. -/
theorem trGhatFam_eq_split_of_isFull (P : ParamsQ) {F : Family} (hF : F.IsFull) (Qn : ℕ)
    (hP : P.Valid) (hw : SideCondWrange P) :
    trGhatFam P F Qn = (P.aQ * P.LB ^ 2)⁻¹ * (famMuPart P F Qn + famPPart P F Qn) := by
  rw [trGhatFam_eq_split P F Qn hP hw, famMuPartChars_eq_of_isFull hF,
    famPPartChars_eq_of_isFull hF]


/-! ### Row 2, at the spine: the trace minus its μ_q part -/

theorem aQ_pos_of_valid {P : ParamsQ} (hP : P.Valid) (hw : SideCondWrange P) : 0 < P.aQ := by
  have hl : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hwL : P.w ≤ P.LB / 8 := by
    have := hw; unfold SideCondWrange at this; linarith
  exact (Ends.S2_localHypsCoreW P hP hwL hl hX1).a_pos

theorem abs_famPPart_le (P : ParamsQ) (F : Family) (Qn : ℕ) (hP : P.Valid)
    (hw : SideCondWrange P) :
    |famPPart P F Qn|
      ≤ P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2) :=
  famPpart_le P F Qn hP hw

/-- **Row 2 of §10.2's ledger, at the spine.**  The family trace differs from its `μ_q` part
by at most the §5-Ramanujan prime-part bound — a power saving in `Q` at every `λ < 2`.

**`F.IsFull` is now CARRIED.** `famMuPart` / `famPPart` are the FULL-family objects and
`abs_famPPart_le`'s engine (`famPpart_grid_eq` + `famChiSum_norm_le`) hard-codes
`Σ*_{χ mod q}`, so this statement is about the full family and only about it; before F61 it
was generic in `F` and silently inherited `trGhatFam_eq_split`'s parity `sorryAx`. The parity
counterpart is `ZetaQ.FamRows.abs_trGhatFam_sub_muPartChars_le` (`ZetaQ/FrobRow9.lean`), at
`famMuPartChars` and with the `15/2` constant the two-kernel `cEven` / `cOdd` bound costs. -/
theorem abs_trGhatFam_sub_muPart_le (P : ParamsQ) {F : Family} (hF : F.IsFull) (Qn : ℕ)
    (hP : P.Valid) (hw : SideCondWrange P) :
    |trGhatFam P F Qn - (P.aQ * P.LB ^ 2)⁻¹ * famMuPart P F Qn|
      ≤ (P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2)) := by
  have ha : 0 < P.aQ := aQ_pos_of_valid hP hw
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have hc : (0:ℝ) ≤ (P.aQ * P.LB ^ 2)⁻¹ := by positivity
  rw [trGhatFam_eq_split_of_isFull P hF Qn hP hw,
    show (P.aQ * P.LB ^ 2)⁻¹ * (famMuPart P F Qn + famPPart P F Qn)
        - (P.aQ * P.LB ^ 2)⁻¹ * famMuPart P F Qn
      = (P.aQ * P.LB ^ 2)⁻¹ * famPPart P F Qn by ring, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_famPPart_le P F Qn hP hw) hc

/-- **`ZetaQ.trace_row` REDUCED to its `μ_q` main term (row 1 of §10.2's ledger).**

The conclusion is `Budget.trace_row`'s, character for character.  The one hypothesis is row 1
with row 2's proved Ramanujan budget already subtracted: everything on the prime side of §9's
trace theorem is discharged here, and what remains is exactly the archimedean evaluation
`(aL²)⁻¹·famMuPart ≈ 𝒩`. -/
theorem trace_row_of_muPart (F : Family) (hF : F.IsFull) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hmu : (1 - rowR1 F P) * NfamQ P F Qn
        ≤ (P.aQ * P.LB ^ 2)⁻¹ * famMuPart P F Qn
          - (P.aQ * P.LB ^ 2)⁻¹
              * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2
                  * (3 * (Qn : ℝ) * (1 + P.LB) + 2))) :
    (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn := by
  obtain ⟨hP, -, -, -, -, hw, -, -, -, -⟩ := hdes
  have key := abs_trGhatFam_sub_muPart_le P hF Qn hP hw
  have h := (abs_le.mp key).1
  linarith

end TraceRungs


/-! # §9 → §10.5: THE TRACE ROW, EVENTUALLY IN `Q`

Row 1 of §10.2's ledger — the archimedean `μ_q` main term that `trace_row_of_muPart` names as the
residual obligation — is closed here from the q-uniform μ_χ chain of `ZetaQ/MuqUniform.lean`
(`MuqUniform.muPart_approx_ell1`, per character, cap-free over `LocalHypsCoreW`), the two-sided
per-character RvM count `EFChi.rvmChi_main_uniform`, the family lower bounds (`famRvMLower_of_design`
for `qle`; the trivial `ℓ_{1,q} ≥ ℒ + log 2 − 1` for `dyadic`), and the two numeric lemmas of
`ZetaQ/Row2Numeric.lean`.  The result is `trace_row_eventually`: `trace_row`'s conclusion at every
design point with `Q ≥ Q₀(F, r, ε)`, for BOTH families.  Why not at every design point: see the
docstring of `trace_row` and the module header.  Every declaration below is proved and
`[propext, Classical.choice, Quot.sound]`.

Rule 17: the chain runs at `λ = λ* > 1` through the cap-free `LocalHypsCoreW`; `X` occurs only as
`P.XQ = exp P.LB` inside the row-2 bound and is never compared with `T`; `P.D0` never appears. -/

section TraceRow

open Zeta23.PrimeSide Zeta23.ThmE
open MeasureTheory Topology
open Real

/-! ### (B) the per-character μ-part bridge -/

/-- The per-character μ-part error of `MuqUniform.muPart_approx_ell1`, in `ParamsQ` vocabulary,
with `log q` majorised by `log Qn`. -/
def muErr (P : ParamsQ) (Qn : ℕ) : ℝ :=
  (180 / π + 36) * (16 + 2 * P.cWin + 2 * P.cWin ^ 2) * P.LB ^ 2 / (2 * π)
    + 4 * π * P.LB * (Real.log Qn / (2 * π) + 11 / π * Zeta23.l P.T)
    + (10 / π) * P.LB ^ 2 / P.T

theorem T_ge_2pie_add_one_of_valid {P : ParamsQ} (hP : P.Valid) :
    2 * π * Real.exp 1 + 1 ≤ P.T := by
  have hT : (300:ℝ) ≤ P.T := by
    have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpi : π < 4 := Real.pi_lt_four
  have hpi0 : 0 < π := Real.pi_pos
  nlinarith [Real.exp_pos 1]

theorem muPart_chi_approx (P : ParamsQ) (hP : P.Valid) (hw : SideCondWrange P) {q : ℕ}
    (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    |(∑ k ∈ Finset.range P.dQ, ∫ r, P.phiHatQ r ^ 2 * muDensity q χ (P.tauQ k + r))
        - P.aQ * P.LB ^ 2 * (P.T * ell1q q P.T / (2 * π))|
      ≤ (180 / π + 36) * (16 + 2 * P.cWin + 2 * P.cWin ^ 2) * P.LB ^ 2 / (2 * π)
        + 4 * π * P.LB * (Real.log q / (2 * π) + 11 / π * Zeta23.l P.T)
        + (10 / π) * P.LB ^ 2 / P.T := by
  have hl : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hlne : Zeta23.l P.T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hl)
  have hX1 : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have hwL : P.w ≤ P.LB / 8 := by
    have := hw; unfold SideCondWrange at this; linarith
  have hF := Ends.S2_localHypsCoreW P hP hwL hl hX1
  have hT : 2 * π * Real.exp 1 + 1 ≤ (Ends.toSetting P).T := by
    rw [Ends.toSetting_T]; exact T_ge_2pie_add_one_of_valid hP
  have hκ : parity χ ≤ 1 := by unfold parity; split <;> omega
  have h := MuqUniform.muPart_approx_ell1 hκ hq hF hT
  rw [Ends.toSetting_d P hlne, Ends.S1_toSetting_L P hlne] at h
  simp only [Ends.toSetting_tau P hlne, Ends.toSetting_T] at h
  exact h

/-! ### (C) the per-character RvM upper bound, summed -/

theorem famRvM_upper_raw (P : ParamsQ) (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn) {A T₀ : ℝ}
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    NfamQ P F Qn
      ≤ ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) *
          (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            + A * Real.log ((q : ℝ) * (P.T + 2))) := by
  -- `NfamQ` is a `familySum`, i.e. already an `F.chars`-sum; the `Family.chars_subset`
  -- monotonicity step (a parity family carries FEWER characters, and `NcountQ ≥ 0`) makes
  -- this bound hold in ALL SIX branches, so the `by_cases F.IsFull` and its `sorry` are gone.
  have hexp : NfamQ P F Qn
      = ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, NcountQ q χ P.T (2 * P.T) := rfl
  rw [hexp]
  refine Finset.sum_le_sum ?_
  intro q hq
  have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
  have : NeZero q := ⟨by omega⟩
  have hmono : ∑ χ ∈ F.chars q, NcountQ q χ P.T (2 * P.T)
      ≤ ∑ χ ∈ primitiveChars q, NcountQ q χ P.T (2 * P.T) :=
    Finset.sum_le_sum_of_subset_of_nonneg (F.chars_subset q)
      (fun χ _ _ => NcountQ_nonneg q χ _ _)
  refine hmono.trans ?_
  have hstep : ∀ χ ∈ primitiveChars q,
      NcountQ q χ P.T (2 * P.T)
        ≤ P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            + A * Real.log ((q : ℝ) * (P.T + 2)) := by
    intro χ hχ
    have hp : χ.IsPrimitive := EFChi.isPrimitive_of_mem_primitiveChars hχ
    have hab := abs_le.mp (hrvm q χ hq1 hp P.T hT)
    have hNc : NcountQ q χ P.T (2 * P.T)
        = ((Zeta23.ThmE.NcountL χ P.T (2 * P.T) : ℕ) : ℝ) := by
      unfold NcountQ; rw [dif_neg (show ¬ q = 0 by omega)]
    rw [hNc]
    linarith [hab.2]
  calc ∑ χ ∈ primitiveChars q, NcountQ q χ P.T (2 * P.T)
      ≤ ∑ _χ ∈ primitiveChars q,
          (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            + A * Real.log ((q : ℝ) * (P.T + 2))) := Finset.sum_le_sum hstep
    _ = (phiStar q : ℝ) *
          (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            + A * Real.log ((q : ℝ) * (P.T + 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          show ((primitiveChars q).card : ℕ) = phiStar q from rfl]

/-! ### (D) the family sum of the μ-part -/

theorem le_Qn_of_mem_moduli {F : Family} {Qn q : ℕ} (hq : q ∈ F.moduli Qn) : q ≤ Qn := by
  cases F <;>
    · simp only [Family.moduli, Finset.mem_Icc, Finset.mem_Ioc] at hq
      omega

theorem log_le_log_Qn_of_mem {F : Family} {Qn q : ℕ} (hq : q ∈ F.moduli Qn) :
    Real.log q ≤ Real.log Qn := by
  have h1 : 1 ≤ q := one_le_of_mem_moduli hq
  have hle : q ≤ Qn := le_Qn_of_mem_moduli hq
  exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast hle)

theorem famMuPart_ge (P : ParamsQ) (hP : P.Valid) (hw : SideCondWrange P) {F : Family}
    (hF : F.IsFull) (Qn : ℕ) :
    P.aQ * P.LB ^ 2 * (P.T / (2 * π))
        * (∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T)
      - F.sizeR Qn * muErr P Qn
      ≤ famMuPart P F Qn := by
  have hLB : 0 ≤ P.LB := (EFChi.LB_pos_of_valid hP).le
  have hpi : 0 < π := Real.pi_pos
  have hstep : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      P.aQ * P.LB ^ 2 * (P.T * Zeta23.ThmE.ell1q q P.T / (2 * π)) - muErr P Qn
        ≤ ∑ k ∈ Finset.range P.dQ, ∫ r, P.phiHatQ r ^ 2 * muDensity q χ (P.tauQ k + r) := by
    intro q hq χ _
    have hq1 : 1 ≤ q := one_le_of_mem_moduli hq
    have h := (abs_le.mp (muPart_chi_approx P hP hw hq1 χ)).1
    have hlog := log_le_log_Qn_of_mem hq
    have hmono : 4 * π * P.LB * (Real.log q / (2 * π) + 11 / π * Zeta23.l P.T)
        ≤ 4 * π * P.LB * (Real.log Qn / (2 * π) + 11 / π * Zeta23.l P.T) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : Real.log q / (2 * π) ≤ Real.log Qn / (2 * π) :=
        div_le_div_of_nonneg_right hlog (by positivity)
      linarith
    unfold muErr
    linarith
  unfold famMuPart
  calc P.aQ * P.LB ^ 2 * (P.T / (2 * π))
          * (∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T)
        - F.sizeR Qn * muErr P Qn
      = ∑ q ∈ F.moduli Qn, ∑ _χ ∈ primitiveChars q,
          (P.aQ * P.LB ^ 2 * (P.T * Zeta23.ThmE.ell1q q P.T / (2 * π)) - muErr P Qn) := by
        rw [sizeR_eq_sum_phiStar hF, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul,
          show ((primitiveChars q).card : ℕ) = phiStar q from rfl]
        ring
    _ ≤ _ := Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => hstep q hq χ hχ

/-- **Row 1's μ-part, against the RvM count**: `(aL²)⁻¹·famMuPart ≥ 𝒩 − |𝔉|·(A·log(Q(T+2)) +
muErr/(aL²))`. -/
theorem muPart_ge_NfamQ_sub (P : ParamsQ) (hP : P.Valid) (hw : SideCondWrange P) {F : Family}
    (hF : F.IsFull) (Qn : ℕ) (hQn : 2 ≤ Qn) {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    NfamQ P F Qn
        - F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)) + muErr P Qn / (P.aQ * P.LB ^ 2))
      ≤ (P.aQ * P.LB ^ 2)⁻¹ * famMuPart P F Qn := by
  have ha : 0 < P.aQ := hP.aQ_pos
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have haL : 0 < P.aQ * P.LB ^ 2 := by positivity
  have hT0 : 0 < P.T := T_posQ hP
  have hup := famRvM_upper_raw P F Qn hQn hrvm hT
  have hmu := famMuPart_ge P hP hw hF Qn
  have hS : ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * (A * Real.log ((q:ℝ) * (P.T + 2)))
      ≤ F.sizeR Qn * (A * Real.log ((Qn:ℝ) * (P.T + 2))) := by
    rw [sizeR_eq_sum_phiStar hF, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq1 : 1 ≤ q := one_le_of_mem_moduli hq
    have hle : (q:ℝ) ≤ Qn := by exact_mod_cast le_Qn_of_mem_moduli hq
    have hqR : (0:ℝ) < q := by exact_mod_cast hq1
    have hmono : Real.log ((q:ℝ) * (P.T + 2)) ≤ Real.log ((Qn:ℝ) * (P.T + 2)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hA) (by positivity)
  have hsplit : ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T + A * Real.log ((q : ℝ) * (P.T + 2)))
      = P.T / (2 * π) * (∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T)
        + ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * (A * Real.log ((q:ℝ) * (P.T + 2))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hsplit] at hup
  set S := ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T with hSdef
  have h1 : (P.aQ * P.LB ^ 2)⁻¹ * (P.aQ * P.LB ^ 2 * (P.T / (2 * π)) * S
        - F.sizeR Qn * muErr P Qn)
      ≤ (P.aQ * P.LB ^ 2)⁻¹ * famMuPart P F Qn :=
    mul_le_mul_of_nonneg_left hmu (by positivity)
  have h2 : (P.aQ * P.LB ^ 2)⁻¹ * (P.aQ * P.LB ^ 2 * (P.T / (2 * π)) * S
        - F.sizeR Qn * muErr P Qn)
      = P.T / (2 * π) * S - F.sizeR Qn * (muErr P Qn / (P.aQ * P.LB ^ 2)) := by
    field_simp
  linarith [h1, h2, hup, hS]

/-! ### The window constant at the design is ONE number per family -/

/-- `c_W` at the design of record: `cRho ϱ₂ + M₁λ* + (M₁λ*)² + M₂λ*²` with `M_j` the derivative
bounds of `F.designProfile` on `[−λ*/2, λ*/2]`. -/
def cWinDesign (F : Family) : ℝ :=
  Zeta23.Taper.cRho Zeta23.Taper.rhoTwo
    + ParamsQ.Mpoly F.designProfile (F.lamStar / 2) 1 * F.lamStar
    + (ParamsQ.Mpoly F.designProfile (F.lamStar / 2) 1 * F.lamStar) ^ 2
    + ParamsQ.Mpoly F.designProfile (F.lamStar / 2) 2 * F.lamStar ^ 2

theorem cWin_of_design {F : Family} {r ε Q : ℝ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε Q P) : P.cWin = cWinDesign F := by
  obtain ⟨-, -, -, hlam, -, -, -, -, -, -, hϱ, hprof⟩ := hdes
  unfold ParamsQ.cWin ParamsQ.profM cWinDesign
  rw [hlam, hϱ, hprof]

/-- The per-character error, divided by `aL²`, is bounded by a constant depending only on the
window constant: `(4/3)·(K(16+2c+2c²)/(2π) + 47)`. -/
def cErr (c : ℝ) : ℝ := 4 / 3 * ((180 / π + 36) * (16 + 2 * c + 2 * c ^ 2) / (2 * π) + 47)

theorem one_le_lamStar_of_family (F : Family) : 1 ≤ F.lamStar := by
  cases F <;>
    simp [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10, lamStarEvenDyad12] <;> norm_num

theorem log_Qn_le_LL {P : ParamsQ} (hP : P.Valid) {Qn : ℕ} (hQn : 1 ≤ Qn) (hQ : P.Q = Qn) :
    Real.log Qn ≤ P.LL ∧ Zeta23.l P.T ≤ P.LL := by
  have hT : (300:ℝ) ≤ P.T := by
    have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h
  have hpi : π < 4 := Real.pi_lt_four
  have hpi0 : 0 < π := Real.pi_pos
  have hQnR : (1:ℝ) ≤ Qn := by exact_mod_cast hQn
  have hQ0 : (0:ℝ) < Qn := by linarith
  have hdiv : (0:ℝ) < P.T / (2 * π) := by positivity
  have hLL : P.LL = Real.log Qn + Real.log (P.T / (2 * π)) := by
    unfold ParamsQ.LL
    rw [hQ, show (Qn : ℝ) * P.T / (2 * π) = (Qn : ℝ) * (P.T / (2 * π)) by ring]
    exact Real.log_mul (ne_of_gt hQ0) (ne_of_gt hdiv)
  have h1 : 0 ≤ Real.log (P.T / (2 * π)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; linarith
  have h2 : 0 ≤ Real.log (Qn : ℝ) := Real.log_nonneg hQnR
  refine ⟨by rw [hLL]; linarith, ?_⟩
  show Real.log (P.T / (2 * π)) ≤ P.LL
  rw [hLL]; linarith

theorem muErr_div_le (P : ParamsQ) (hP : P.Valid) (Qn : ℕ)
    (hQn : 1 ≤ Qn) (hQ : P.Q = Qn) (hlam : 1 ≤ P.lam) :
    muErr P Qn / (P.aQ * P.LB ^ 2) ≤ cErr P.cWin := by
  have ha : 0 < P.aQ := hP.aQ_pos
  have ha34 : 3 / 4 ≤ P.aQ := hP.a_ge
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have haL : 0 < P.aQ * P.LB ^ 2 := by positivity
  have hT : (300:ℝ) ≤ P.T := by
    have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h
  have hpi : π < 4 := Real.pi_lt_four
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  obtain ⟨hlogQ, hlT⟩ := log_Qn_le_LL hP hQn hQ
  have hLL0 : 0 ≤ P.LL := le_trans (Real.log_nonneg (by exact_mod_cast hQn)) hlogQ
  have hLLLB : P.LL ≤ P.LB := by
    unfold ParamsQ.LB; nlinarith
  have hc4 : 4 ≤ P.cWin := hP.four_le_cWin
  set K := (180 / π + 36) * (16 + 2 * P.cWin + 2 * P.cWin ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hmid : 4 * π * P.LB * (Real.log Qn / (2 * π) + 11 / π * Zeta23.l P.T)
      = 2 * P.LB * Real.log Qn + 44 * P.LB * Zeta23.l P.T := by
    field_simp; ring
  have hA : 2 * P.LB * Real.log Qn ≤ 2 * P.LB * P.LL := by gcongr
  have hB : 44 * P.LB * Zeta23.l P.T ≤ 44 * P.LB * P.LL := by gcongr
  have hC : 46 * P.LB * P.LL ≤ 46 * P.LB * P.LB := by gcongr
  have hD : (10 / π) * P.LB ^ 2 / P.T ≤ P.LB ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have : 10 / π ≤ P.T := by
      rw [div_le_iff₀ hpi0]; nlinarith
    nlinarith [sq_nonneg P.LB]
  have hE : (K / (2 * π) + 47) * P.LB ^ 2 ≤ cErr P.cWin * (P.aQ * P.LB ^ 2) := by
    unfold cErr
    rw [← hK]
    have h43 : 1 ≤ 4 / 3 * P.aQ := by linarith
    have hpos : 0 ≤ (K / (2 * π) + 47) * P.LB ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h43 hpos]
  rw [div_le_iff₀ haL]
  unfold muErr
  rw [hmid, ← hK]
  have hKsplit : K * P.LB ^ 2 / (2 * π) = K / (2 * π) * P.LB ^ 2 := by ring
  rw [hKsplit]
  nlinarith [hA, hB, hC, hD, hE]


/-! ### (E-a) the family lower bound `c_F·|𝔉|·T ≤ rowR1·𝒩` -/

/-- The slack `trace_row` spends per family: `1/100` (`qle`, from `FamRvMLower` at the exact
§12.2 average) and `1/200` (`dyadic`, from the trivial `log q ≥ log(Q/2)` average). -/
def traceRowSlack : Family → ℝ
  | Family.qle => 1 / 100
  | Family.dyadic => 1 / 200
  | Family.evenQle => 1 / 100
  | Family.oddQle => 1 / 100
  | Family.evenDyadic => 1 / 200
  | Family.oddDyadic => 1 / 200
  | Family.evenQleR => 1 / 100
  | Family.oddQleR => 1 / 100
  | Family.evenDyadicR => 1 / 200
  | Family.oddDyadicR => 1 / 200

theorem traceRowSlack_pos (F : Family) : 0 < traceRowSlack F := by
  cases F <;> norm_num [traceRowSlack]

theorem rowR1_nonneg (F : Family) (P : ParamsQ) (hLL : 0 < P.LL) : 0 ≤ rowR1 F P := by
  unfold rowR1 L₆ sZone
  have h0 : 0 ≤ F.conductorShift := conductorShift_nonneg F
  positivity

/-- `qle`: from `FamRvMLower` (the exact average, `famRvMLower_of_design`) and `ℒ ≥ 30`. -/
theorem rowR1_NfamQ_lower_qle (P : ParamsQ) (hP : P.Valid) (Qn : ℕ)
    (hrvm : FamRvMLower Family.qle Qn P) (hLL : 30 ≤ P.LL) :
    traceRowSlack Family.qle * Family.sizeR Family.qle Qn * P.T
      ≤ rowR1 Family.qle P * NfamQ P Family.qle Qn := by
  have hT0 : 0 ≤ P.T := (T_posQ hP).le
  have hS : 0 ≤ Family.sizeR Family.qle Qn := by unfold Family.sizeR; positivity
  have hLL0 : 0 < P.LL := by linarith
  have hr1 : 0 ≤ rowR1 Family.qle P := rowR1_nonneg _ _ hLL0
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hfA : P.LL - 0.124 ≤ famAvgLlow Family.qle P := by
    unfold famAvgLlow famAvgL rvmSlack Family.conductorShift; linarith
  have hfA0 : 0 ≤ famAvgLlow Family.qle P := by linarith
  have hr1eq : rowR1 Family.qle P = 0.5073 / (8 * P.LL) := by
    unfold rowR1 L₆ sZone Family.conductorShift; field_simp; ring
  have key : traceRowSlack Family.qle * P.T
      ≤ rowR1 Family.qle P * (P.T / (2 * π) * famAvgLlow Family.qle P) := by
    rw [hr1eq, show 0.5073 / (8 * P.LL) * (P.T / (2 * π) * famAvgLlow Family.qle P)
        = 0.5073 * P.T * famAvgLlow Family.qle P / (16 * π * P.LL) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    unfold traceRowSlack
    have h1 : 1 / 100 * P.T * (16 * π * P.LL) ≤ 1 / 100 * P.T * (16 * 3.15 * P.LL) := by
      gcongr
    have h2 : 0.5073 * P.T * (P.LL - 0.124) ≤ 0.5073 * P.T * famAvgLlow Family.qle P := by
      gcongr
    nlinarith [mul_nonneg hT0 (sub_nonneg.2 hLL)]
  calc traceRowSlack Family.qle * Family.sizeR Family.qle Qn * P.T
      = Family.sizeR Family.qle Qn * (traceRowSlack Family.qle * P.T) := by ring
    _ ≤ Family.sizeR Family.qle Qn
          * (rowR1 Family.qle P * (P.T / (2 * π) * famAvgLlow Family.qle P)) :=
        mul_le_mul_of_nonneg_left key hS
    _ = rowR1 Family.qle P
          * (Family.sizeR Family.qle Qn * (P.T / (2 * π) * famAvgLlow Family.qle P)) := by ring
    _ ≤ rowR1 Family.qle P * NfamQ P Family.qle Qn := mul_le_mul_of_nonneg_left hrvm hr1

/-- `dyadic`: `ℓ_{1,q}(T) ≥ ℒ + log 2 − 1` for `q > Q/2`, RvM's error at `T/(400π)`, `ℒ ≥ 30`. -/
theorem rowR1_NfamQ_lower_dyadic (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hQ : P.Q = Qn) {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T)
    (herr : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ P.T / (400 * π)) (hLL : 30 ≤ P.LL) :
    traceRowSlack Family.dyadic * Family.sizeR Family.dyadic Qn * P.T
      ≤ rowR1 Family.dyadic P * NfamQ P Family.dyadic Qn := by
  have hT0 : 0 < P.T := T_posQ hP
  have hS : 0 ≤ Family.sizeR Family.dyadic Qn := by unfold Family.sizeR; positivity
  have hLL0 : 0 < P.LL := by linarith
  have hr1 : 0 ≤ rowR1 Family.dyadic P := rowR1_nonneg _ _ hLL0
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hQnR : (2:ℝ) ≤ Qn := by exact_mod_cast hQn
  have hQ0 : (0:ℝ) < Qn := by linarith
  have hdiv : (0:ℝ) < P.T / (2 * π) := by positivity
  have hLLsplit : P.LL = Real.log Qn + Real.log (P.T / (2 * π)) := by
    unfold ParamsQ.LL
    rw [hQ, show (Qn : ℝ) * P.T / (2 * π) = (Qn : ℝ) * (P.T / (2 * π)) by ring]
    exact Real.log_mul (ne_of_gt hQ0) (ne_of_gt hdiv)
  have hlow := famRvM_lower_raw P Family.isFull_dyadic Qn hQn hrvm hT
  -- each summand is at least `(T/2π)(ℒ − 1)`
  have hterm : ∀ q ∈ Family.dyadic.moduli Qn,
      (phiStar q : ℝ) * (P.T / (2 * π) * (P.LL - 1))
        ≤ (phiStar q : ℝ) * (P.T / (2 * π) * Zeta23.ThmE.ell1q q P.T
            - A * Real.log ((q : ℝ) * (P.T + 2))) := by
    intro q hq
    have hmem : q ∈ Finset.Ioc (Qn / 2) Qn := hq
    rw [Finset.mem_Ioc] at hmem
    have h2q : Qn ≤ 2 * q := by omega
    have h2qR : (Qn : ℝ) ≤ 2 * q := by exact_mod_cast h2q
    have hq1 : (1:ℝ) ≤ q := by
      have : 1 ≤ q := by omega
      exact_mod_cast this
    have hqR : (0:ℝ) < q := by linarith
    have hlogq : Real.log Qn - Real.log 2 ≤ Real.log q := by
      rw [← Real.log_div (ne_of_gt hQ0) (by norm_num)]
      exact Real.log_le_log (by positivity) (by linarith)
    have hell : P.LL + Real.log 2 - 1 ≤ Zeta23.ThmE.ell1q q P.T := by
      unfold Zeta23.ThmE.ell1q
      rw [show (q : ℝ) * P.T / (2 * π) = (q : ℝ) * (P.T / (2 * π)) by ring,
        Real.log_mul (ne_of_gt hqR) (ne_of_gt hdiv), hLLsplit]
      linarith
    have hlogle : A * Real.log ((q:ℝ) * (P.T + 2)) ≤ A * Real.log ((Qn:ℝ) * (P.T + 2)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      have hle : (q:ℝ) ≤ Qn := by exact_mod_cast hmem.2
      exact Real.log_le_log (by positivity) (by nlinarith)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 : P.T / (2 * π) * (P.LL + Real.log 2 - 1)
        ≤ P.T / (2 * π) * Zeta23.ThmE.ell1q q P.T :=
      mul_le_mul_of_nonneg_left hell hdiv.le
    have h2 : P.T / (400 * π) ≤ P.T / (2 * π) * (Real.log 2 - 1 / 200) := by
      have e : P.T / (2 * π) * (Real.log 2 - 1 / 200)
          = P.T * (200 * (Real.log 2 - 1 / 200)) / (400 * π) := by
        field_simp; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    nlinarith [h1, h2, herr, hlogle]
  have hsum : Family.sizeR Family.dyadic Qn * (P.T / (2 * π) * (P.LL - 1))
      ≤ NfamQ P Family.dyadic Qn := by
    refine le_trans ?_ hlow
    rw [sizeR_eq_sum_phiStar Family.isFull_dyadic, Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  -- the exact dyadic shift `1/2 − (log 2)/3 ≥ 0.26895` (the former literal was a lower bound)
  have hshlo : (0.26895 : ℝ) ≤ Family.dyadic.conductorShift := conductorShift_dyadic_bounds.1
  have hr1ge : 0.5073 * 0.26895 / (4 * P.LL) ≤ rowR1 Family.dyadic P := by
    have hr1eq : rowR1 Family.dyadic P = 0.5073 * Family.dyadic.conductorShift / (4 * P.LL) := by
      unfold rowR1 L₆ sZone; field_simp
    rw [hr1eq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [hshlo]
  have key : traceRowSlack Family.dyadic * P.T
      ≤ rowR1 Family.dyadic P * (P.T / (2 * π) * (P.LL - 1)) := by
    have hpos : 0 ≤ P.T / (2 * π) * (P.LL - 1) := mul_nonneg hdiv.le (by linarith)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hr1ge hpos)
    rw [show 0.5073 * 0.26895 / (4 * P.LL) * (P.T / (2 * π) * (P.LL - 1))
        = 0.5073 * 0.26895 * P.T * (P.LL - 1) / (8 * π * P.LL) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    unfold traceRowSlack
    have h1 : 1 / 200 * P.T * (8 * π * P.LL) ≤ 1 / 200 * P.T * (8 * 3.15 * P.LL) := by
      gcongr
    nlinarith [mul_nonneg hT0.le (sub_nonneg.2 hLL)]
  calc traceRowSlack Family.dyadic * Family.sizeR Family.dyadic Qn * P.T
      = Family.sizeR Family.dyadic Qn * (traceRowSlack Family.dyadic * P.T) := by ring
    _ ≤ Family.sizeR Family.dyadic Qn
          * (rowR1 Family.dyadic P * (P.T / (2 * π) * (P.LL - 1))) :=
        mul_le_mul_of_nonneg_left key hS
    _ = rowR1 Family.dyadic P
          * (Family.sizeR Family.dyadic Qn * (P.T / (2 * π) * (P.LL - 1))) := by ring
    _ ≤ rowR1 Family.dyadic P * NfamQ P Family.dyadic Qn := mul_le_mul_of_nonneg_left hsum hr1


/-- **The `qle`-shaped row-1 floor, for ANY family whose conductor shift is `1/2` and whose
row-1 slack is `1/100`** — `rowR1_NfamQ_lower_qle` with `Family.qle` generalised. Every
step reads `F` only through `F.conductorShift` (in `rowR1` and in `famAvgLlow`) and through
`traceRowSlack F`, so the two `Icc 2 Qn` parity families are covered verbatim once
`FamRvMLower F Qn P` is supplied — which is `famRvMLower_parity_of_design`. -/
theorem rowR1_NfamQ_lower_parity_qle (P : ParamsQ) (hP : P.Valid) {F : Family}
    (hsh : F.conductorShift = 1 / 2) (hslack : traceRowSlack F = 1 / 100) (Qn : ℕ)
    (hrvm : FamRvMLower F Qn P) (hLL : 30 ≤ P.LL) :
    traceRowSlack F * Family.sizeR F Qn * P.T ≤ rowR1 F P * NfamQ P F Qn := by
  have hT0 : 0 ≤ P.T := (T_posQ hP).le
  have hS : 0 ≤ Family.sizeR F Qn := by unfold Family.sizeR; positivity
  have hLL0 : 0 < P.LL := by linarith
  have hr1 : 0 ≤ rowR1 F P := rowR1_nonneg _ _ hLL0
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hfA : P.LL - 0.124 ≤ famAvgLlow F P := by
    unfold famAvgLlow famAvgL rvmSlack
    rw [hsh]; linarith
  have hfA0 : 0 ≤ famAvgLlow F P := by linarith
  have hr1eq : rowR1 F P = 0.5073 / (8 * P.LL) := by
    unfold rowR1 L₆ sZone
    rw [hsh]; field_simp; ring
  have key : traceRowSlack F * P.T
      ≤ rowR1 F P * (P.T / (2 * π) * famAvgLlow F P) := by
    rw [hr1eq, show 0.5073 / (8 * P.LL) * (P.T / (2 * π) * famAvgLlow F P)
        = 0.5073 * P.T * famAvgLlow F P / (16 * π * P.LL) by field_simp; ring]
    rw [le_div_iff₀ (by positivity), hslack]
    have h1 : 1 / 100 * P.T * (16 * π * P.LL) ≤ 1 / 100 * P.T * (16 * 3.15 * P.LL) := by
      gcongr
    have h2 : 0.5073 * P.T * (P.LL - 0.124) ≤ 0.5073 * P.T * famAvgLlow F P := by
      gcongr
    nlinarith [mul_nonneg hT0 (sub_nonneg.2 hLL)]
  calc traceRowSlack F * Family.sizeR F Qn * P.T
      = Family.sizeR F Qn * (traceRowSlack F * P.T) := by ring
    _ ≤ Family.sizeR F Qn * (rowR1 F P * (P.T / (2 * π) * famAvgLlow F P)) :=
        mul_le_mul_of_nonneg_left key hS
    _ = rowR1 F P * (Family.sizeR F Qn * (P.T / (2 * π) * famAvgLlow F P)) := by ring
    _ ≤ rowR1 F P * NfamQ P F Qn := mul_le_mul_of_nonneg_left hrvm hr1

/-- **The dyadic-shaped row-1 floor, for ANY family on the dyadic modulus range** —
`rowR1_NfamQ_lower_dyadic` with the per-modulus weight moved from `φ*(q)` to `|F.chars q|`
(`famRvM_lower_weight`, `sizeR_eq_sum_weight`). The crude conductor average
`ℓ_{1,q}(T) ≥ ℒ + log 2 − 1` for `q > Q/2` is a per-modulus statement, so it does not care which
characters of `q` are kept: no §12.2 or §12.3 input is needed here at all. -/
theorem rowR1_NfamQ_lower_parity_dyadic (P : ParamsQ) (hP : P.Valid) {F : Family}
    (hsh : F.conductorShift = Family.dyadic.conductorShift)
    (hslack : traceRowSlack F = 1 / 200) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hmod : F.moduli Qn = Family.dyadic.moduli Qn)
    (hQ : P.Q = Qn) {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T)
    (herr : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ P.T / (400 * π)) (hLL : 30 ≤ P.LL) :
    traceRowSlack F * Family.sizeR F Qn * P.T ≤ rowR1 F P * NfamQ P F Qn := by
  have hT0 : 0 < P.T := T_posQ hP
  have hS : 0 ≤ Family.sizeR F Qn := by unfold Family.sizeR; positivity
  have hLL0 : 0 < P.LL := by linarith
  have hr1 : 0 ≤ rowR1 F P := rowR1_nonneg _ _ hLL0
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hQnR : (2:ℝ) ≤ Qn := by exact_mod_cast hQn
  have hQ0 : (0:ℝ) < Qn := by linarith
  have hdiv : (0:ℝ) < P.T / (2 * π) := by positivity
  have hLLsplit : P.LL = Real.log Qn + Real.log (P.T / (2 * π)) := by
    unfold ParamsQ.LL
    rw [hQ, show (Qn : ℝ) * P.T / (2 * π) = (Qn : ℝ) * (P.T / (2 * π)) by ring]
    exact Real.log_mul (ne_of_gt hQ0) (ne_of_gt hdiv)
  have hlow := famRvM_lower_weight P F Qn hQn hrvm hT
  have hterm : ∀ q ∈ F.moduli Qn,
      (((F.chars q).card : ℕ) : ℝ) * (P.T / (2 * π) * (P.LL - 1))
        ≤ (((F.chars q).card : ℕ) : ℝ) * (P.T / (2 * π) * Zeta23.ThmE.ell1q q P.T
            - A * Real.log ((q : ℝ) * (P.T + 2))) := by
    intro q hq
    rw [hmod] at hq
    have hmem : q ∈ Finset.Ioc (Qn / 2) Qn := hq
    rw [Finset.mem_Ioc] at hmem
    have h2q : Qn ≤ 2 * q := by omega
    have h2qR : (Qn : ℝ) ≤ 2 * q := by exact_mod_cast h2q
    have hq1 : (1:ℝ) ≤ q := by
      have : 1 ≤ q := by omega
      exact_mod_cast this
    have hqR : (0:ℝ) < q := by linarith
    have hlogq : Real.log Qn - Real.log 2 ≤ Real.log q := by
      rw [← Real.log_div (ne_of_gt hQ0) (by norm_num)]
      exact Real.log_le_log (by positivity) (by linarith)
    have hell : P.LL + Real.log 2 - 1 ≤ Zeta23.ThmE.ell1q q P.T := by
      unfold Zeta23.ThmE.ell1q
      rw [show (q : ℝ) * P.T / (2 * π) = (q : ℝ) * (P.T / (2 * π)) by ring,
        Real.log_mul (ne_of_gt hqR) (ne_of_gt hdiv), hLLsplit]
      linarith
    have hlogle : A * Real.log ((q:ℝ) * (P.T + 2)) ≤ A * Real.log ((Qn:ℝ) * (P.T + 2)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      have hle : (q:ℝ) ≤ Qn := by exact_mod_cast hmem.2
      exact Real.log_le_log (by positivity) (by nlinarith)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 : P.T / (2 * π) * (P.LL + Real.log 2 - 1)
        ≤ P.T / (2 * π) * Zeta23.ThmE.ell1q q P.T :=
      mul_le_mul_of_nonneg_left hell hdiv.le
    have h2 : P.T / (400 * π) ≤ P.T / (2 * π) * (Real.log 2 - 1 / 200) := by
      have e : P.T / (2 * π) * (Real.log 2 - 1 / 200)
          = P.T * (200 * (Real.log 2 - 1 / 200)) / (400 * π) := by
        field_simp; ring
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    nlinarith [h1, h2, herr, hlogle]
  have hsum : Family.sizeR F Qn * (P.T / (2 * π) * (P.LL - 1)) ≤ NfamQ P F Qn := by
    refine le_trans ?_ hlow
    rw [sizeR_eq_sum_weight, Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hshlo : (0.26895 : ℝ) ≤ F.conductorShift := by
    rw [hsh]; exact conductorShift_dyadic_bounds.1
  have hr1ge : 0.5073 * 0.26895 / (4 * P.LL) ≤ rowR1 F P := by
    have hr1eq : rowR1 F P = 0.5073 * F.conductorShift / (4 * P.LL) := by
      unfold rowR1 L₆ sZone; field_simp
    rw [hr1eq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [hshlo]
  have key : traceRowSlack F * P.T ≤ rowR1 F P * (P.T / (2 * π) * (P.LL - 1)) := by
    have hpos : 0 ≤ P.T / (2 * π) * (P.LL - 1) := mul_nonneg hdiv.le (by linarith)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hr1ge hpos)
    rw [show 0.5073 * 0.26895 / (4 * P.LL) * (P.T / (2 * π) * (P.LL - 1))
        = 0.5073 * 0.26895 * P.T * (P.LL - 1) / (8 * π * P.LL) by field_simp; ring]
    rw [le_div_iff₀ (by positivity), hslack]
    have h1 : 1 / 200 * P.T * (8 * π * P.LL) ≤ 1 / 200 * P.T * (8 * 3.15 * P.LL) := by
      gcongr
    nlinarith [mul_nonneg hT0.le (sub_nonneg.2 hLL)]
  calc traceRowSlack F * Family.sizeR F Qn * P.T
      = Family.sizeR F Qn * (traceRowSlack F * P.T) := by ring
    _ ≤ Family.sizeR F Qn * (rowR1 F P * (P.T / (2 * π) * (P.LL - 1))) :=
        mul_le_mul_of_nonneg_left key hS
    _ = rowR1 F P * (Family.sizeR F Qn * (P.T / (2 * π) * (P.LL - 1))) := by ring
    _ ≤ rowR1 F P * NfamQ P F Qn := mul_le_mul_of_nonneg_left hsum hr1

/-! ### The dyadic family size from below (companion of `sizeR_qle_lower'`) -/

theorem sizeR_dyadic_eq (N : ℕ) :
    Family.sizeR Family.dyadic N
      = Normalisation.N2.Astar N - Normalisation.N2.Astar (N / 2) := by
  have hcons := Finset.sum_Ioc_consecutive (fun q => (phiStar q : ℝ))
    (Nat.zero_le (N / 2)) (Nat.div_le_self N 2)
  rw [sizeR_eq_sum_phiStar Family.isFull_dyadic]
  unfold Normalisation.N2.Astar
  rw [Icc_one_eq_Ioc_zero', Icc_one_eq_Ioc_zero']
  show ∑ q ∈ Finset.Ioc (N / 2) N, (phiStar q : ℝ) = _
  linarith [hcons]

/-- `|𝔉_Q| ≥ (3/4)(18/π⁴)Q² − 8Q(1+log Q)²` for the dyadic family (`27/(2π⁴) = (3/4)(18/π⁴)`). -/
theorem sizeR_dyadic_lower (N : ℕ) (hN : 2 ≤ N) :
    3 / 4 * (18 / π ^ 4) * (N : ℝ) ^ 2 - 8 * (N : ℝ) * (1 + Real.log N) ^ 2
      ≤ Family.sizeR Family.dyadic N := by
  rw [sizeR_dyadic_eq]
  have hN2 : 1 ≤ N / 2 := by omega
  have h1 := abs_le.mp (Normalisation.N2.Astar_bound N (by omega))
  have h2 := abs_le.mp (Normalisation.N2.Astar_bound (N / 2) hN2)
  have hhalf : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
  have hhalf1 : (1 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hN2
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log ((N / 2 : ℕ) : ℝ) ≤ Real.log N :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log ((N / 2 : ℕ) : ℝ) := Real.log_nonneg hhalf1
  have hc : (0:ℝ) ≤ 18 / π ^ 4 := by positivity
  have hsq : (18 / π ^ 4) * ((N / 2 : ℕ) : ℝ) ^ 2 ≤ (18 / π ^ 4) * ((N : ℝ) / 2) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hc
    exact pow_le_pow_left₀ (by positivity) hhalf 2
  have hB : 5 * ((N / 2 : ℕ) : ℝ) * (1 + Real.log ((N / 2 : ℕ) : ℝ)) ^ 2
      ≤ 5 * ((N : ℝ) / 2) * (1 + Real.log N) ^ 2 := by
    apply mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      (by positivity) (by positivity)
  have hpos : 0 ≤ (N : ℝ) * (1 + Real.log N) ^ 2 := by positivity
  linarith [h1.1, h2.2, hsq, hB, hpos]

/-! ### F60 — §12.3's count against the DYADIC full-family closed form.

The `Icc 2 Qn` half of this (`not_isFull_*`, `two_sizeR_parity_qle`) sits earlier, inside
`section FamilyBridge`, because §12.2's `FamRvMLower` chain needs it there. -/

/-- `|2·|𝔉_Q| − (Astar Qn − Astar (Qn/2))| ≤ Qn` for the two dyadic parity families. -/
theorem two_sizeR_parity_dyadic {F : Family} (hF : ¬ F.IsFull) (Qn : ℕ)
    (hmod : F.moduli Qn = Family.dyadic.moduli Qn) :
    |2 * F.sizeR Qn - (Normalisation.N2.Astar Qn - Normalisation.N2.Astar (Qn / 2))| ≤ (Qn : ℝ) := by
  have hsum : ∑ q ∈ F.moduli Qn, (phiStar q : ℝ)
      = Normalisation.N2.Astar Qn - Normalisation.N2.Astar (Qn / 2) := by
    rw [hmod, ← sizeR_eq_sum_phiStar Family.isFull_dyadic Qn]
    exact sizeR_dyadic_eq Qn
  have h := ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn hF Qn
  rwa [hsum] at h

theorem one_add_log_sq_div_tendsto' :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ 2 / x) atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ 0 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 0)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 1 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 1)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hcomb : Tendsto (fun x : ℝ =>
      Real.log x ^ 0 / x + 2 * (Real.log x ^ 1 / x) + Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa using (h0.add (h1.const_mul 2)).add h2
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [pow_zero, pow_one]
  field_simp
  ring

/-- Eventually `|𝔉_Q| ≥ Q²/10` for the dyadic family. -/
theorem sizeR_dyadic_floor_eventually :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ 2 / 10 ≤ Family.sizeR Family.dyadic N := by
  have hev : ∀ᶠ x : ℝ in atTop, (1 + Real.log x) ^ 2 / x < 1 / 250 :=
    one_add_log_sq_div_tendsto'.eventually_lt_const (by norm_num)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev,
    eventually_ge_atTop 2] with N hN hN2
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0:ℝ) < N := by linarith
  have hlow := sizeR_dyadic_lower N hN2
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  have hpi4 : π ^ 4 ≤ 100 := by
    have : π ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ hpi0.le hpi.le 4
    norm_num at this; linarith
  have hc : 0.18 ≤ 18 / π ^ 4 := by rw [le_div_iff₀ (by positivity)]; linarith
  have h8 : 8 * (N:ℝ) * (1 + Real.log N) ^ 2 ≤ 8 / 250 * (N:ℝ) ^ 2 := by
    have h := hN
    rw [div_lt_iff₀ hN0] at h
    nlinarith
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg (N:ℝ))
  nlinarith [hlow, hc', h8]

/-- **Eventually `|𝔉_Q| ≥ Q²/25`, for ALL SIX families**.

The two full families sit at `≥ 0.156·Q²` (`qle`) and `≥ 0.1·Q²` (`dyadic`); §12.3's count
(`two_sizeR_parity_qle` / `two_sizeR_parity_dyadic`) halves those and costs a further `Q`,
leaving `≥ 0.076·Q²` and `≥ 0.048·Q²` — all four above `1/25 = 0.04`. This is the floor the
row-2 comparison spends; the `Q²/10` of `sizeR_dyadic_floor_eventually` is FALSE for the
parity families (they sit at `0.069·Q²`), so a common floor has to be below that. -/
theorem sizeR_floor_eventually (F : Family) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ 2 / 25 ≤ Family.sizeR F N := by
  have hev : ∀ᶠ x : ℝ in atTop, (1 + Real.log x) ^ 2 / x < 1 / 250 :=
    one_add_log_sq_div_tendsto'.eventually_lt_const (by norm_num)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev,
    sizeR_dyadic_floor_eventually, eventually_ge_atTop 2] with N hN hdy hN2
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0:ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by omega
  have hlogN : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_natCast_nonneg N
  have hsq1 : (1:ℝ) ≤ (1 + Real.log (N:ℝ)) ^ 2 := by nlinarith
  have hdiv := hN
  rw [div_lt_iff₀ hN0] at hdiv
  have hNbig : (250:ℝ) < (N:ℝ) := by nlinarith
  have hNle : (N:ℝ) ≤ (N:ℝ) ^ 2 / 250 := by nlinarith
  have h6 : 6 * (N:ℝ) * (1 + Real.log N) ^ 2 ≤ 6 / 250 * (N:ℝ) ^ 2 := by nlinarith
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  have hpi4 : π ^ 4 ≤ 100 := by
    have : π ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ hpi0.le hpi.le 4
    norm_num at this; linarith
  have hc : (0.18:ℝ) ≤ 18 / π ^ 4 := by rw [le_div_iff₀ (by positivity)]; linarith
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg (N:ℝ))
  have hqle := sizeR_qle_lower' N hN1
  have hqeq := sizeR_qle_eq_Astar_sub_one N hN1
  have hdeq := sizeR_dyadic_eq N
  cases F with
  | qle => linarith [hqle, hc', h6]
  | dyadic => linarith [hdy]
  | evenQle =>
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_evenQle N hN1 rfl)
      linarith [hpar.1, hqeq, hqle, hc', h6, hNle]
  | oddQle =>
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_oddQle N hN1 rfl)
      linarith [hpar.1, hqeq, hqle, hc', h6, hNle]
  | evenDyadic =>
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_evenDyadic N rfl)
      linarith [hpar.1, hdeq, hdy, hNle]
  | oddDyadic =>
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_oddDyadic N rfl)
      linarith [hpar.1, hdeq, hdy, hNle]
  | evenQleR =>
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_evenQleR N hN1 rfl)
      linarith [hpar.1, hqeq, hqle, hc', h6, hNle]
  | oddQleR =>
      have hpar := abs_le.mp (two_sizeR_parity_qle not_isFull_oddQleR N hN1 rfl)
      linarith [hpar.1, hqeq, hqle, hc', h6, hNle]
  | evenDyadicR =>
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_evenDyadicR N rfl)
      linarith [hpar.1, hdeq, hdy, hNle]
  | oddDyadicR =>
      have hpar := abs_le.mp (two_sizeR_parity_dyadic not_isFull_oddDyadicR N rfl)
      linarith [hpar.1, hdeq, hdy, hNle]

/-! ### (E-iii) the row-2 term, at the spine -/

theorem row2_term_le (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) :
    (P.aQ * P.LB ^ 2)⁻¹
        * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2))
      ≤ 2 * P.LB * Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2)
          / Real.log 2 := by
  have ha34 : 3 / 4 ≤ P.aQ := hP.a_ge
  have ha : 0 < P.aQ := hP.aQ_pos
  have hLB : 0 < P.LB := EFChi.LB_pos_of_valid hP
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hX : P.XQ = Real.exp P.LB := rfl
  rw [hX]
  have hs : 0 ≤ Real.sqrt (Real.exp P.LB) := Real.sqrt_nonneg _
  have hB : 0 ≤ 3 * (Qn : ℝ) * (1 + P.LB) + 2 := by positivity
  have e : (P.aQ * P.LB ^ 2)⁻¹
        * (P.LB ^ 3 * Real.sqrt (Real.exp P.LB) / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2))
      = (P.LB / P.aQ)
        * (Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2) / Real.log 2) := by
    field_simp
  rw [e]
  have hdiv : P.LB / P.aQ ≤ 2 * P.LB := by
    rw [div_le_iff₀ ha]; nlinarith
  calc (P.LB / P.aQ)
        * (Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2) / Real.log 2)
      ≤ (2 * P.LB)
        * (Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2) / Real.log 2) :=
        mul_le_mul_of_nonneg_right hdiv (by positivity)
    _ = 2 * P.LB * Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2)
          / Real.log 2 := by ring

/-! ### The design point's scales, in the numeric lemmas' vocabulary -/

theorem LL_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) :
    P.LL = Real.log ((Qn : ℝ) * Real.log (Qn : ℝ) ^ (r + ε) / (2 * π)) := by
  obtain ⟨-, hQ, hT, -⟩ := hdes
  unfold ParamsQ.LL; rw [hQ, hT]; rfl

theorem LB_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) : P.LB = F.lamStar * P.LL := by
  obtain ⟨-, -, -, hlam, -⟩ := hdes
  unfold ParamsQ.LB; rw [hlam]

theorem T_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) : P.T = Real.log (Qn : ℝ) ^ (r + ε) := by
  obtain ⟨-, -, hT, -⟩ := hdes
  rw [hT]; rfl

theorem LL_ge_log_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hQn : 1 ≤ Qn) : Real.log Qn ≤ P.LL :=
  (log_Qn_le_LL hdes.1 hQn hdes.2.1).1

/-- **Row 2 for `qle`, eventually**: `Row2Numeric.row2_error_eventually` at the design. -/
theorem row2_qle_eventually (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      (P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2))
        ≤ traceRowSlack Family.qle * Family.sizeR Family.qle Qn * P.T
          - 2 * (Family.sizeR Family.qle Qn * (P.T / (400 * π))) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Row2Numeric.row2_error_eventually r ε hr hε), eventually_ge_atTop 1] with Qn hrow hQn1
  intro P hdes
  have hP : P.Valid := hdes.1
  have hLL := LL_of_design hdes
  have hLB : P.LB = 1.2507321515 * P.LL := by rw [LB_of_design hdes]; rfl
  have hT := T_of_design hdes
  dsimp only at hrow
  rw [← hLL, ← hLB, ← hT] at hrow
  have h1 := row2_term_le P hP Qn
  have hsz := sizeR_qle_lower' Qn hQn1
  have hT0 : 0 ≤ P.T := (T_posQ hP).le
  have hpi : 3 < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  have hc0 : 0 ≤ 1 / 100 - 1 / (200 * π) := by
    have : 1 / (200 * π) ≤ 1 / 600 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hconst : (1 / 100 - 1 / (200 * π)) * Family.sizeR Family.qle Qn * P.T
      = traceRowSlack Family.qle * Family.sizeR Family.qle Qn * P.T
          - 2 * (Family.sizeR Family.qle Qn * (P.T / (400 * π))) := by
    unfold traceRowSlack; field_simp; ring
  rw [← hconst]
  calc _ ≤ _ := h1
    _ ≤ (1 / 100 - 1 / (200 * π))
          * ((18 / π ^ 4) * (Qn:ℝ) ^ 2 - 6 * Qn * (1 + Real.log Qn) ^ 2) * P.T := hrow
    _ ≤ (1 / 100 - 1 / (200 * π)) * Family.sizeR Family.qle Qn * P.T := by gcongr

/-- **Row 2 for `dyadic`, eventually**: `row2_error_eventually_gen` at `c = 1/4000`, monotonicity
in `L` (`λ*_dyad < λ*`), and the dyadic size floor `|𝔉_Q| ≥ Q²/10`. -/
theorem row2_dyadic_eventually (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      (P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2))
        ≤ traceRowSlack Family.dyadic * Family.sizeR Family.dyadic Qn * P.T
          - 2 * (Family.sizeR Family.dyadic Qn * (P.T / (400 * π))) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Row2Numeric.row2_error_eventually_gen r ε (1 / 4000) hr hε (by norm_num)),
    sizeR_dyadic_floor_eventually, eventually_ge_atTop 2] with Qn hrow hsz hQn2
  intro P hdes
  have hP : P.Valid := hdes.1
  have hLL := LL_of_design hdes
  have hLB : P.LB = 1.1931581210 * P.LL := by rw [LB_of_design hdes]; rfl
  have hT := T_of_design hdes
  dsimp only at hrow
  rw [← hLL, ← hT] at hrow
  have hLL0 : 0 ≤ P.LL :=
    le_trans (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Qn by omega)))
      (LL_ge_log_of_design hdes (by omega))
  have hLB0 : 0 ≤ P.LB := (EFChi.LB_pos_of_valid hP).le
  set Lq := 1.2507321515 * P.LL with hLq
  have hLq0 : 0 ≤ Lq := by rw [hLq]; exact mul_nonneg (by norm_num) hLL0
  have hLBle : P.LB ≤ Lq := by rw [hLB, hLq]; nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hQ0 : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  have hmono : 2 * P.LB * Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2)
        / Real.log 2
      ≤ 2 * Lq * Real.sqrt (Real.exp Lq) * (3 * (Qn : ℝ) * (1 + Lq) + 2) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    have hs : Real.sqrt (Real.exp P.LB) ≤ Real.sqrt (Real.exp Lq) :=
      Real.sqrt_le_sqrt (Real.exp_le_exp.mpr hLBle)
    have hb : 3 * (Qn : ℝ) * (1 + P.LB) + 2 ≤ 3 * (Qn : ℝ) * (1 + Lq) + 2 := by nlinarith
    apply mul_le_mul (mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by linarith)) hb
      (by positivity) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  have h1 := row2_term_le P hP Qn
  have hT0 : 0 ≤ P.T := (T_posQ hP).le
  have hS : 0 ≤ Family.sizeR Family.dyadic Qn := by unfold Family.sizeR; positivity
  have hpi : 3 < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  have hc : 1 / 300 ≤ 1 / 200 - 1 / (200 * π) := by
    have : 1 / (200 * π) ≤ 1 / 600 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hconst : traceRowSlack Family.dyadic * Family.sizeR Family.dyadic Qn * P.T
        - 2 * (Family.sizeR Family.dyadic Qn * (P.T / (400 * π)))
      = (1 / 200 - 1 / (200 * π)) * Family.sizeR Family.dyadic Qn * P.T := by
    unfold traceRowSlack; field_simp; ring
  rw [hconst]
  calc _ ≤ _ := h1
    _ ≤ 2 * Lq * Real.sqrt (Real.exp Lq) * (3 * (Qn : ℝ) * (1 + Lq) + 2) / Real.log 2 := hmono
    _ ≤ 1 / 4000 * (Qn:ℝ) ^ 2 * P.T := hrow
    _ ≤ 1 / 300 * Family.sizeR Family.dyadic Qn * P.T := by
        have : 1 / 4000 * (Qn:ℝ) ^ 2 ≤ 1 / 300 * Family.sizeR Family.dyadic Qn := by
          nlinarith
        exact mul_le_mul_of_nonneg_right this hT0
    _ ≤ (1 / 200 - 1 / (200 * π)) * Family.sizeR Family.dyadic Qn * P.T := by
        gcongr

/-- **Row 2 for ANY family, eventually** — the route of `row2_dyadic_eventually`, run at
the common size floor `|𝔉_Q| ≥ Q²/25` (`sizeR_floor_eventually`) and the common slack floor
`traceRowSlack F ≥ 1/200`, with the numeric input taken at `c = 1/10000` instead of `1/4000`.

The two ingredients that used to be family-specific are now uniform: every family's `λ*` is at
most `Family.qle`'s (`lamStar = 1.2507321515`, against `1.1931581210` dyadic, `1.1329788821`
even/odd `qle`, `1.1015998422` even/odd dyadic), so `Row2Numeric`'s bound at `Family.qle`'s
`L` dominates in all six branches; and `1/10000 ≤ (1/200 − 1/(200π))·(1/25)` with room
(`0.0001` against `0.000133`). `row2_qle_eventually` and `row2_dyadic_eventually` keep the
sharper family-specific constants and are still what `row2_eventually` uses for the two full
families. -/
theorem row2_generic_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2))
        ≤ traceRowSlack F * Family.sizeR F Qn * P.T
          - 2 * (Family.sizeR F Qn * (P.T / (400 * π))) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Row2Numeric.row2_error_eventually_gen r ε (1 / 10000) hr hε (by norm_num)),
    sizeR_floor_eventually F, eventually_ge_atTop 2] with Qn hrow hsz hQn2
  intro P hdes
  have hP : P.Valid := hdes.1
  have hLL := LL_of_design hdes
  have hT := T_of_design hdes
  dsimp only at hrow
  rw [← hLL, ← hT] at hrow
  have hLL0 : 0 ≤ P.LL :=
    le_trans (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Qn by omega)))
      (LL_ge_log_of_design hdes (by omega))
  have hLB0 : 0 ≤ P.LB := (EFChi.LB_pos_of_valid hP).le
  set Lq := 1.2507321515 * P.LL with hLq
  have hLq0 : 0 ≤ Lq := by rw [hLq]; exact mul_nonneg (by norm_num) hLL0
  have hlamF : F.lamStar ≤ 1.2507321515 := by
    cases F <;>
      simp only [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10, lamStarEvenDyad12] <;>
      norm_num
  have hLBle : P.LB ≤ Lq := by
    rw [LB_of_design hdes, hLq]
    exact mul_le_mul_of_nonneg_right hlamF hLL0
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hQ0 : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  have hmono : 2 * P.LB * Real.sqrt (Real.exp P.LB) * (3 * (Qn : ℝ) * (1 + P.LB) + 2)
        / Real.log 2
      ≤ 2 * Lq * Real.sqrt (Real.exp Lq) * (3 * (Qn : ℝ) * (1 + Lq) + 2) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    have hs : Real.sqrt (Real.exp P.LB) ≤ Real.sqrt (Real.exp Lq) :=
      Real.sqrt_le_sqrt (Real.exp_le_exp.mpr hLBle)
    have hb : 3 * (Qn : ℝ) * (1 + P.LB) + 2 ≤ 3 * (Qn : ℝ) * (1 + Lq) + 2 := by nlinarith
    apply mul_le_mul (mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by linarith)) hb
      (by positivity) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  have h1 := row2_term_le P hP Qn
  have hT0 : 0 ≤ P.T := (T_posQ hP).le
  have hS : 0 ≤ Family.sizeR F Qn := by unfold Family.sizeR; positivity
  have hpi : 3 < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  have hslack : (1:ℝ) / 200 ≤ traceRowSlack F := by
    cases F <;> norm_num [traceRowSlack]
  have hc : 1 / 300 ≤ traceRowSlack F - 1 / (200 * π) := by
    have : 1 / (200 * π) ≤ 1 / 600 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hconst : traceRowSlack F * Family.sizeR F Qn * P.T
        - 2 * (Family.sizeR F Qn * (P.T / (400 * π)))
      = (traceRowSlack F - 1 / (200 * π)) * Family.sizeR F Qn * P.T := by
    field_simp; ring
  rw [hconst]
  calc _ ≤ _ := h1
    _ ≤ 2 * Lq * Real.sqrt (Real.exp Lq) * (3 * (Qn : ℝ) * (1 + Lq) + 2) / Real.log 2 := hmono
    _ ≤ 1 / 10000 * (Qn:ℝ) ^ 2 * P.T := hrow
    _ ≤ 1 / 300 * Family.sizeR F Qn * P.T := by
        have hstep : 1 / 10000 * (Qn:ℝ) ^ 2 ≤ 1 / 300 * Family.sizeR F Qn := by
          linarith [hsz]
        exact mul_le_mul_of_nonneg_right hstep hT0
    _ ≤ (traceRowSlack F - 1 / (200 * π)) * Family.sizeR F Qn * P.T := by
        gcongr

/-- **⚠ SORRY for Corollary 3's four parity families.** `row2_qle_eventually` /
`row2_dyadic_eventually` are the two instances; each is an eventual comparison of §5's
Ramanujan prime-part budget against `traceRowSlack F · |𝔉| · T`, and each is proved from the
family's own §12.2 size asymptotic (`FamSizeLower` at `Qn²/C`, `Σ_q φ*(q) ≍ (18/π⁴)Q²`).
For a parity family `|𝔉|` is halved and `C` doubled, so the SHAPE of the argument survives
unchanged — what is missing is the §12.2 count `Σ_{q ≤ Q} evenPrimCount q ~ (9/π⁴)Q²` on this
import path, and the `traceRowSlack` value for the parity families (currently set equal to
the parent's, which is provisional). Needs: numerics + the §12.3 count.

**PROVED IN ALL SIX BRANCHES; the `sorry` is closed.** `row2_qle_eventually` /
`row2_dyadic_eventually` remain the two sharp instances; the four parity branches go through
`row2_generic_eventually`, which runs the dyadic route at the common size floor
`|𝔉_Q| ≥ Q²/25` (`sizeR_floor_eventually`, from §12.3's count) and the common slack floor
`traceRowSlack F ≥ 1/200`, taking `Row2Numeric`'s input at `c = 1/10000`. The `traceRowSlack`
values for the parity families are still set equal to their parents' (`1/100` for
`evenQle`/`oddQle`, `1/200` for the dyadic pair) and remain provisional in the sense that no
parity-specific analysis has been done — but nothing here depends on their being anything
better than `≥ 1/200`, which is all `row2_generic_eventually` asks for. -/
theorem row2_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (P.aQ * P.LB ^ 2)⁻¹
          * (P.LB ^ 3 * Real.sqrt P.XQ / Real.log 2 * (3 * (Qn : ℝ) * (1 + P.LB) + 2))
        ≤ traceRowSlack F * Family.sizeR F Qn * P.T
          - 2 * (Family.sizeR F Qn * (P.T / (400 * π))) := by
  cases F with
  | qle => exact row2_qle_eventually r ε hr hε
  | dyadic => exact row2_dyadic_eventually r ε hr hε
  -- the four parity branches, via the uniform route `row2_generic_eventually`.
  | evenQle => exact row2_generic_eventually Family.evenQle r ε hr hε
  | oddQle => exact row2_generic_eventually Family.oddQle r ε hr hε
  | evenDyadic => exact row2_generic_eventually Family.evenDyadic r ε hr hε
  | oddDyadic => exact row2_generic_eventually Family.oddDyadic r ε hr hε
  | evenQleR => exact row2_generic_eventually Family.evenQleR r ε hr hε
  | oddQleR => exact row2_generic_eventually Family.oddQleR r ε hr hε
  | evenDyadicR => exact row2_generic_eventually Family.evenDyadicR r ε hr hε
  | oddDyadicR => exact row2_generic_eventually Family.oddDyadicR r ε hr hε

/-! ### (E-a) packaged eventually -/

/-- **⚠ SORRY for Corollary 3's four parity families.** The `qle` branch runs on
`famRvMLower_of_design` (§12.2's exact conductor average) and the `dyadic` branch on
`EFChi.rvmChi_main_uniform` plus the crude `log q ≥ log(Q/2)` average. Neither input exists
for a parity family: both are statements about `Σ_q φ*(q)·⟨log q⟩` over the FULL character
set. The parity versions need §12.3's `Σ_q evenPrimCount q · log q` — the same `S(q)`
bookkeeping flagged at `sizeR_eq_sum_phiStar`. Needs: new mathematics (§12.3 conductor
average), then tedium.

**PROVED IN ALL SIX BRANCHES; the `sorry` is closed.** The two `Icc 2 Qn` parity families
run on `famRvMLower_parity_of_design` — §12.2's exact conductor average (`famLogCond_qle_bound`)
transported across §12.3's count (`ParityCount.abs_two_sum_weight_log_sub_le` and
`two_sizeR_parity_qle`), which raises the §12.2 residue from `19Q(1+log Q)³` to `21Q(1+log Q)³`
and changes nothing else, `Family.conductorShift` being `1/2` on `evenQle`/`oddQle` as well.
The two dyadic parity families run on the crude `log q ≥ log(Q/2)` average, which is a
per-modulus statement and therefore needs no counting input at all
(`rowR1_NfamQ_lower_parity_dyadic`). -/
theorem rowR1_NfamQ_lower_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      traceRowSlack F * Family.sizeR F Qn * P.T ≤ rowR1 F P * NfamQ P F Qn := by
  have hLL30 : ∀ᶠ Qn : ℕ in atTop, (30:ℝ) ≤ Real.log Qn :=
    tendsto_log_nat_atTop.eventually_ge_atTop 30
  cases F with
  | qle =>
    filter_upwards [famRvMLower_of_design r ε hr hε, hLL30, eventually_ge_atTop 1]
      with Qn hrvm h30 hQn1
    intro P hdes
    exact rowR1_NfamQ_lower_qle P hdes.1 Qn (hrvm P hdes)
      (le_trans h30 (LL_ge_log_of_design hdes hQn1))
  | dyadic =>
    obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
    have hre : (0:ℝ) < r + ε := by linarith
    have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
      (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
    filter_upwards [rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀, hLL30,
      eventually_ge_atTop 2] with Qn herr hT0 h30 hQn2
    intro P hdes
    have hP := hdes.1
    have hQ := hdes.2.1
    have hT := hdes.2.2.1
    have hpi0 : 0 < π := Real.pi_pos
    have herr' : A * Real.log ((Qn:ℝ) * (P.T + 2)) ≤ P.T / (400 * π) := by
      rw [hT, le_div_iff₀ (by positivity)]; linarith [herr]
    exact rowR1_NfamQ_lower_dyadic P hP Qn hQn2 hQ hA.le hrvm (by rw [hT]; exact hT0) herr'
      (le_trans h30 (LL_ge_log_of_design hdes (by omega)))
  -- the two `Icc 2 Qn` parity families run on `famRvMLower_parity_of_design`
  -- (§12.2's exact conductor average transported by §12.3's count); the two dyadic parity
  -- families run on the crude `log q ≥ log(Q/2)` average, which is per-modulus and so needs
  -- no counting input at all.
  | evenQle =>
    filter_upwards [famRvMLower_parity_of_design not_isFull_evenQle rfl (fun _ => rfl) r ε hr hε,
      hLL30, eventually_ge_atTop 1] with Qn hrvm h30 hQn1
    intro P hdes
    exact rowR1_NfamQ_lower_parity_qle P hdes.1 rfl rfl Qn (hrvm P hdes)
      (le_trans h30 (LL_ge_log_of_design hdes hQn1))
  | oddQle =>
    filter_upwards [famRvMLower_parity_of_design not_isFull_oddQle rfl (fun _ => rfl) r ε hr hε,
      hLL30, eventually_ge_atTop 1] with Qn hrvm h30 hQn1
    intro P hdes
    exact rowR1_NfamQ_lower_parity_qle P hdes.1 rfl rfl Qn (hrvm P hdes)
      (le_trans h30 (LL_ge_log_of_design hdes hQn1))
  | evenDyadic =>
    obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
    have hre : (0:ℝ) < r + ε := by linarith
    have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
      (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
    filter_upwards [rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀, hLL30,
      eventually_ge_atTop 2] with Qn herr hT0 h30 hQn2
    intro P hdes
    have hP := hdes.1
    have hQ := hdes.2.1
    have hT := hdes.2.2.1
    have hpi0 : 0 < π := Real.pi_pos
    have herr' : A * Real.log ((Qn:ℝ) * (P.T + 2)) ≤ P.T / (400 * π) := by
      rw [hT, le_div_iff₀ (by positivity)]; linarith [herr]
    exact rowR1_NfamQ_lower_parity_dyadic (F := Family.evenDyadic) P hP rfl rfl Qn hQn2 rfl hQ
      hA.le hrvm (by rw [hT]; exact hT0) herr'
      (le_trans h30 (LL_ge_log_of_design hdes (by omega)))
  | oddDyadic =>
    obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
    have hre : (0:ℝ) < r + ε := by linarith
    have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
      (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
    filter_upwards [rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀, hLL30,
      eventually_ge_atTop 2] with Qn herr hT0 h30 hQn2
    intro P hdes
    have hP := hdes.1
    have hQ := hdes.2.1
    have hT := hdes.2.2.1
    have hpi0 : 0 < π := Real.pi_pos
    have herr' : A * Real.log ((Qn:ℝ) * (P.T + 2)) ≤ P.T / (400 * π) := by
      rw [hT, le_div_iff₀ (by positivity)]; linarith [herr]
    exact rowR1_NfamQ_lower_parity_dyadic (F := Family.oddDyadic) P hP rfl rfl Qn hQn2 rfl hQ
      hA.le hrvm (by rw [hT]; exact hT0) herr'
      (le_trans h30 (LL_ge_log_of_design hdes (by omega)))
  | evenQleR =>
    filter_upwards [famRvMLower_parity_of_design not_isFull_evenQleR rfl (fun _ => rfl) r ε hr hε,
      hLL30, eventually_ge_atTop 1] with Qn hrvm h30 hQn1
    intro P hdes
    exact rowR1_NfamQ_lower_parity_qle P hdes.1 rfl rfl Qn (hrvm P hdes)
      (le_trans h30 (LL_ge_log_of_design hdes hQn1))
  | oddQleR =>
    filter_upwards [famRvMLower_parity_of_design not_isFull_oddQleR rfl (fun _ => rfl) r ε hr hε,
      hLL30, eventually_ge_atTop 1] with Qn hrvm h30 hQn1
    intro P hdes
    exact rowR1_NfamQ_lower_parity_qle P hdes.1 rfl rfl Qn (hrvm P hdes)
      (le_trans h30 (LL_ge_log_of_design hdes hQn1))
  | evenDyadicR =>
    obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
    have hre : (0:ℝ) < r + ε := by linarith
    have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
      (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
    filter_upwards [rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀, hLL30,
      eventually_ge_atTop 2] with Qn herr hT0 h30 hQn2
    intro P hdes
    have hP := hdes.1
    have hQ := hdes.2.1
    have hT := hdes.2.2.1
    have hpi0 : 0 < π := Real.pi_pos
    have herr' : A * Real.log ((Qn:ℝ) * (P.T + 2)) ≤ P.T / (400 * π) := by
      rw [hT, le_div_iff₀ (by positivity)]; linarith [herr]
    exact rowR1_NfamQ_lower_parity_dyadic (F := Family.evenDyadicR) P hP rfl rfl Qn hQn2 rfl hQ
      hA.le hrvm (by rw [hT]; exact hT0) herr'
      (le_trans h30 (LL_ge_log_of_design hdes (by omega)))
  | oddDyadicR =>
    obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
    have hre : (0:ℝ) < r + ε := by linarith
    have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
      (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
    filter_upwards [rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀, hLL30,
      eventually_ge_atTop 2] with Qn herr hT0 h30 hQn2
    intro P hdes
    have hP := hdes.1
    have hQ := hdes.2.1
    have hT := hdes.2.2.1
    have hpi0 : 0 < π := Real.pi_pos
    have herr' : A * Real.log ((Qn:ℝ) * (P.T + 2)) ≤ P.T / (400 * π) := by
      rw [hT, le_div_iff₀ (by positivity)]; linarith [herr]
    exact rowR1_NfamQ_lower_parity_dyadic (F := Family.oddDyadicR) P hP rfl rfl Qn hQn2 rfl hQ
      hA.le hrvm (by rw [hT]; exact hT0) herr'
      (le_trans h30 (LL_ge_log_of_design hdes (by omega)))

/-! ### (F) assembly

**`trace_row_eventually_aux` and `trace_row_eventually` now live in `ZetaQ/FrobRow9.lean`**,
at the foot of the file, under the same names and the same `ZetaQ` namespace.

They were moved DOWN one level, and here is why. Their `¬ F.IsFull` branch — the μ-part
lower bound at the parity weight — is discharged by `ZetaQ.trace_row_eventually_notFull`,
whose only genuinely new input is `ZetaQ.FamRows.abs_trGhatFam_sub_muPartChars_le`
(`ZetaQ/FrobRow9.lean`), and `FrobRow9` IMPORTS this file, so that lemma cannot be cited
here. Of the three ways out — move the theorems down, give them an explicit hypothesis
supplying the parity row-2 bound, or move the `FamRows` chain up into this file — the first
is by far the least invasive: no statement changes, no signature changes, nothing is threaded
through the four call sites, and the `FamRows` chain (which sits at the END of `FrobRow9` and
depends on most of it) stays where it is. The only other edit the move costs is one added
`import ZetaQ.FrobRow9` in `ZetaQ/JoinCert.lean`; `JoinProved` and `Margin` already see
`FrobRow9` transitively through `HFrob → FrobAssembly`.

The same question for `FrobAssembly.A1_eventually` has a different answer: it already lives
in a file that imports `FrobRow8`/`FrobRow9`, so its parity branch (`A1_eventually_gen`) is
proved in place with no move at all. -/

end TraceRow

end ZetaQ
