# Simple zeros

Two papers by Oliver D'Souza (2026) with their Lean 4 / Mathlib formalisation:

- **On the proportions of simple and of distinct zeros of the Riemann zeta function**: [PDF](papers/zeta/main.pdf),
  sources in [`papers/zeta/`](papers/zeta/); Lean library `ZetaS` and the kernel replay `ZetaSReplay`.
- **Simple zeros on the critical line of primitive Dirichlet L-functions on average over moduli q ≤ Q: the killed kernel
  and the Shell kernel**: [PDF](papers/family/main.pdf), sources in [`papers/family/`](papers/family/); Lean library
  `ZetaShell`.

Status: preprints, not independently refereed; the Lean development has not been rebuilt outside this project. The
papers and the formalisation were produced substantially by a generative AI system, Claude (Anthropic), working under
the direction of the author, who takes full responsibility for their contents. The exact status of each result (Lean
theorem, and with which displayed hypotheses) is in the tables below; what is in the release and what is not claimed is
in [`RELEASE_NOTES.md`](RELEASE_NOTES.md). Release `v1.0` (version 1.0.0) of <https://github.com/Oliverds321/simple-zeros>.
This repository is a single-commit snapshot of the release: the commits named in these files and in the papers (for
example `4874cc0`, whose Lean sources the release has) are commits of the development history, which is not published.

The repository is a modified copy of the Lean artifact Zeta23 (<https://github.com/anthropics/zeta-23-lean>), whose
README follows under [Upstream: Zeta23](#upstream-zeta23); what was added and changed is in [`NOTICE`](NOTICE).

## What is proved

**ζ** (library `ZetaS`, paper `papers/zeta/`). Each statement has the ε-form used throughout this README: for every
ε > 0 there is T₀ with (c − ε)·N(T, 2T) ≤ X(T, 2T) for all T ≥ T₀, where N(T, 2T) counts the zeros ρ of `riemannZeta`
with 0 < Re ρ < 1 and T < Im ρ ≤ 2T with multiplicity, and X is the count named in the first column (for "simple or on
the critical line": the zeros on the line counted with multiplicity plus the simple zeros off it).

| result | c | Lean name | module | trust level | hypotheses |
|---|---|---|---|---|---|
| simple zeros, K = 5 | 0.675158622 | `ZetaS.Top.zeta_simple_K5_uncond` | `ZetaSReplay/ReplayHeadlines.lean` | Lean theorem, three standard axioms | none |
| distinct zeros, K = 5 | 0.837579311 | `ZetaS.Top.zeta_distinct_K5_uncond` | `ZetaSReplay/ReplayHeadlines.lean` | Lean theorem, three standard axioms | none |
| simple zeros, K = 7 | 0.676102666 | `ZetaS.Top.zeta_simple_K7_final` | `ZetaS/Top/TopFinal.lean` | Lean theorem, three standard axioms | `CertAM7`, displayed (a finite numerical certificate, verified outside Lean) |
| distinct zeros, K = 7 | 0.838051333 | `ZetaS.Top.zeta_distinct_K7_final` | `ZetaS/Top/TopFinal.lean` | Lean theorem, three standard axioms | `CertAM7`, displayed |
| simple and on the critical line | 0.6733736895 | `ZetaS.Top.zeta_simple_on_line` | `ZetaS/Top/TopSSC.lean` | Lean theorem, three standard axioms | `CertS8`, displayed |
| simple or on the critical line | 0.8879195 | `ZetaS.Top.zeta_simple_or_critical` | `ZetaS/Top/TopSSC.lean` | Lean theorem, three standard axioms | `CertS8`, displayed |
| the fourteen comparator statements: the six rows with the certificates as displayed hypotheses (the K = 5 rows with `CertAM5`), their cumulative forms, and two non-vacuity companions | | `zeta_simple_K5`, …, `zeta_tendsto_Ncount` | `comparator/Challenge/FollowUpZeta.lean` (proofs: `comparator/Solution/FollowUpZeta.lean`) | Lean theorems, three standard axioms | as stated there |

The value 0.6733736895 is not a record: six larger public values exist. The K = 5 rows rest on the kernel replay of
the certificate `CertAM5` in the library `ZetaSReplay` ([`ZetaSReplay/README.md`](ZetaSReplay/README.md)); the same
statements with `CertAM5` as a displayed hypothesis are `ZetaS.Top.zeta_simple_K5_final` and `zeta_distinct_K5_final`
(`ZetaS/Top/TopFinal.lean`). The certificates' data, certifiers and logs are in
[`supplementary/`](supplementary/README.md); the comparator topic is described in
[`comparator/README_followup.md`](comparator/README_followup.md).

**Families of Dirichlet L-functions** (library `ZetaShell`, paper `papers/family/`; [`ZetaShell/README.md`](ZetaShell/README.md)).

| result | Lean name | module | trust level | hypotheses |
|---|---|---|---|---|
| Theorem 1′: for the primitive characters of conductor q ≤ Q, at height T = (log Q)^{r+ε} with r ≥ 3, at least the proportion 0.7235 − c·log log Q / log Q of the family's zeros with T < γ ≤ 2T (counted with multiplicity) are simple and on the critical line, for some c > 0 and all large Q | `ZetaShell.LemmaK.theorem_one_prime_design` | `ZetaShell/LemmaK/LK_KT_Headline.lean` | Lean theorem, three standard axioms | none (only 3 ≤ r, 0 < ε) |
| the certificate B(S53-L75) ≤ 2 − 0.9059137927 | `ZetaShell.certS53` | `ZetaShell/Cert/R4_CertS53.lean` | Lean theorem, three standard axioms | none |
| the main theorem (the Shell theorem): for the same family and height, at least the proportion 0.9059137927 − c·(log Q)^{−θ} (0 < θ < 503/1994) of the family's zeros with T < γ ≤ 2T are simple and on the critical line | `ZetaShell.shell_S53_qle_reduced` | `ZetaShell/Top/HeadlineReduced.lean` | Lean theorem, three standard axioms | `ZeroDensityInput`, displayed: the zero-density estimates (J) of Jutila and (M) of Montgomery, as quoted in the paper |
| the comparator statements of the two family theorems over a Mathlib-only file: `family_simple_on_line_killed` (0.7235, no hypothesis) and `family_simple_on_line_shell` (0.9059137927, `ZeroDensityInput`) | `family_simple_on_line_killed`, `family_simple_on_line_shell` | `comparator/Solution/FollowUpFamily.lean` | Lean theorems, three standard axioms | as stated |

## How to verify

Install [`elan`](https://github.com/leanprover/elan); then, from the repository root:

```bash
lake exe cache get                                         # optional: prebuilt Mathlib
lake build ZetaS ZetaShell                                 # also builds Zeta23 and ZetaQ, which they import
lake build Solution.FollowUpZeta
lake env lean comparator/PrintAxioms/FollowUpZeta.lean     # 14 lines
lake env lean comparator/PrintAxioms/FollowUpShell.lean    # 2 lines
lake build Challenge.FollowUpFamily Solution.FollowUpFamily
lake env lean comparator/PrintAxioms/FollowUpFamily.lean   # 2 lines
lake build ZetaSReplay                                     # about 20 Lean-hours of CPU time, about 7 GB of build products
lake env lean comparator/PrintAxioms/FollowUpReplay.lean   # 3 lines
```

Expected: every line printed by the four `lake env lean` commands reads
`'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`. The build of `ZetaS ZetaShell` prints
`declaration uses 'sorry'` warnings for the open statements listed in `RELEASE_NOTES.md` (and the four of `ZetaQ`, see
below); none of them is used by a theorem in the tables above. The numerical certificates are checked by the commands of
[`supplementary/VERIFY.md`](supplementary/VERIFY.md); the full comparator run is described in
[`comparator/README_followup.md`](comparator/README_followup.md).

**Trust model.** Every theorem in the two tables is checked by the Lean kernel and depends only on Lean's three
standard axioms `propext`, `Classical.choice` and `Quot.sound`; none uses `sorry`, `native_decide` or a declared
`axiom`. A displayed hypothesis (`CertAM7`, `CertS8`, and `CertAM5` in the comparator statements) is an explicit
hypothesis of the theorem: a Prop asserting a finite inequality between explicit numbers, checked outside Lean by
interval arithmetic (data, certifiers and logs in `supplementary/`), which the theorem assumes and does not prove.
`ZeroDensityInput`, the one hypothesis of the family main theorem, is of another kind: it states the two zero-density
estimates (J) and (M) from the literature, as quoted in the family paper, for the actual zeros of the family's
L-functions; the theorem assumes them and does not prove them (`comparator/ChallengeDeps/FollowUpFamily.lean` states
them over Mathlib's definitions alone, and shows that they follow from the generalized Riemann hypothesis). The
libraries as a whole are not `sorry`-free: `ZetaShell` still contains open `sorry` statements, in its `Skeleton/`
modules and its statement files, and `ZetaS` in one module; which theorems are affected is in `RELEASE_NOTES.md`.
(The count of `sorry`s in "Building and checking" below covers the upstream library, `comparator/` and `ZetaQ` only.)

## Layout

```
ZetaS/, ZetaS.lean           the ζ follow-up library (imports Zeta23)
ZetaSCertShims/              bare-name forwarders for the frozen certificate checker in ZetaS/Cert/
ZetaSReplay/                 the kernel replay of the K = 5 certificate CertAM5: 1,478 generated modules (README.md)
ZetaShell/, ZetaShell.lean   the family follow-up library (imports ZetaQ; README.md)
comparator/                  topic FollowUpZeta (ChallengeDeps/, Challenge/, Solution/, PrintAxioms/FollowUpZeta.lean,
                             config-followup.json, README_followup.md); topic FollowUpFamily (the same layout,
                             config-followup-family.json, README_followup_family.md); PrintAxioms/FollowUpShell.lean,
                             FollowUpReplay.lean
supplementary/               certificate data, certifiers, logs and the replay generator of the ζ paper (VERIFY.md)
papers/zeta/, papers/family/ the two papers: sources and PDF
audit/followup/              build logs and axiom censuses of the release commit
CITATION.cff, .zenodo.json   citation metadata; RELEASE_NOTES.md: contents, evidence and limits of the release
```

## Licence

Apache License, Version 2.0, as the upstream work: see [`LICENSE`](LICENSE), and [`NOTICE`](NOTICE) for what was added
and changed. The text of the two papers in `papers/` is licensed under CC BY 4.0 (`NOTICE`).

## Upstream: Zeta23

The rest of this file is the README of the upstream artifact, with the notice of the modifications. Its statements
(for example "sorry-free") concern the library `Zeta23` and, where said, `ZetaQ`; the follow-up libraries are
described above.

**Zeta23 — a Lean 4 formalization of "More than two thirds of the zeros of the Riemann zeta function lie on the critical line"**

> Research artifact. Not maintained and not accepting contributions.
> A Lean 4 formalization released as a static companion artifact to the paper.

Upstream repository: <https://github.com/anthropics/zeta-23-lean>.

> **This is a modified copy of that repository**, modified by Oliver D'Souza (2026, Apache 2.0).
> Added: the library `ZetaQ/` and its root module `ZetaQ.lean`, the scripts under `audit/`, the
> `ZetaQ` entries in `lakefile.toml`, and three modules inside `Zeta23/` (`WindowD.lean`,
> `Tail/GevreyTail.lean`, `Taper/GevreyProduct.lean`); and, for the follow-up of October 2026, the
> libraries `ZetaS/`, `ZetaSCertShims/`, `ZetaShell/` and `ZetaSReplay/` with their root modules and
> `lakefile.toml` entries, the comparator topics `FollowUpZeta` and `FollowUpFamily` and the files `FollowUpShell` and
> `FollowUpReplay` under `comparator/`, `supplementary/`, `papers/`, `audit/followup/`,
> `CITATION.cff`, `.zenodo.json` and `RELEASE_NOTES.md` (see
> [Simple zeros](#simple-zeros) above). Changed inside `Zeta23/`: a weakened
> standing-assumption class `Params.ValidQ` (`Params.Valid` without the bandwidth cap
> `lam_le_one`), and twenty-one modules whose `P.Valid` hypotheses were replaced by the weaker
> `P.ValidQ` — generalisations; no conclusion was altered and nothing was removed. The upstream files
> under `comparator/` and `LICENSE` are untouched, and the results recorded in [`AUDIT.md`](AUDIT.md) were obtained on
> the pristine upstream tree. Full statement in [`NOTICE`](NOTICE); see
> [ZetaQ — the conductor aspect](#zetaq--the-conductor-aspect) below.

This repository accompanies the paper "More than two thirds of the zeros of the Riemann zeta function lie on the critical line" (Claude; Anthropic, San Francisco, 2026).
It contains a complete, `sorry`-free Lean 4 / Mathlib formalization of Theorems A–E of that paper, including proofs
of every analytic input the argument uses (Weil's explicit formula for ζ and for primitive Dirichlet L-functions,
the Riemann–von Mangoldt zero-counting formulas, Stirling-type estimates for Γ′/Γ on vertical lines,
Chebyshev–Mertens prime-sum estimates, and the Montgomery–Vaughan generalized Hilbert inequality). Nothing is
assumed: the top-level theorems have no hypotheses, the repository declares no axioms, and `#print axioms` on each
headline theorem reports only Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound`.

Toolchain: Lean `v4.33.0-rc2`, Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (Mathlib's tag `v4.33.0-rc2`; pinned in `lake-manifest.json`).

### What is proved

Write N(T₁,T₂) for the number of zeros ρ of ζ with 0 < Re ρ < 1 and T₁ < Im ρ ≤ T₂, counted with
multiplicity; N₀*(T₁,T₂) for the number of *distinct* such zeros on the critical line Re ρ = 1/2;
N₀ˢ for those that are on the line and *simple*; N_d for the number of distinct zeros; N(T) := N(0,T) etc.
All of these are defined directly from Mathlib's `riemannZeta` and `analyticOrderAt`
([`comparator/ChallengeDeps.lean`](comparator/ChallengeDeps.lean), ≈60 lines, is the complete list of
definitions the statements depend on). "liminf_{T→∞} X(T)/N(T) ≥ c" is formalized in the ε-form
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`. Here c₁* = √2·tan ϑ/(1+ϑ·tan ϑ), ϑ = 1/√2 (= 0.75329…) is the
Montgomery–Taylor constant of Theorem D.

| | statement (as in the paper) | Lean name (modules `Solution` / `Solution.Multiplicity` under [`comparator/`](comparator/)) | underlying Zeta23 theorem |
|---|---|---|---|
| **A** | liminf N₀*(T,2T)/N(T,2T) ≥ 2/3, and liminf N₀*(T)/N(T) ≥ 2/3 | `two_thirds_on_critical_line`(`_cumulative`) | `Zeta23.thmA₀`(`_cumulative`) (`Zeta23/Final.lean`) |
| **B** | liminf N₀ˢ/N ≥ 2/3: at least two thirds of the zeros are simple and on the critical line (dyadic and cumulative) | `two_thirds_simple_on_critical_line`(`_cumulative`) | `Zeta23.thmB₀_mult`(`_cumulative`) (`Zeta23/FinalMult.lean`) |
| **C** | liminf N_d/N ≥ 5/6 (dyadic and cumulative) | `five_sixths_distinct`(`_cumulative`) | `Zeta23.thmC₀_mult`(`_cumulative`) |
| **D** | with the optimal (Montgomery–Taylor) window: liminf N₀*(T,2T)/N(T,2T) ≥ 2 − 1/c₁* (= 0.67250…), the same for N₀ˢ, and N_d: ≥ (3 − 1/c₁*)/2 (= 0.83625…) | `montgomery_taylor_on_critical_line`, `montgomery_taylor_simple_on_critical_line_mult`, `montgomery_taylor_distinct_mult` | `Zeta23.ThmD.thmD₀` (`Zeta23/ThmD/Final.lean`), `Zeta23.ThmD.thmD₀_simple_mult`, `thmD₀_dist_mult` (`Zeta23/ThmD/Mult.lean`) |
| **E** | for every primitive Dirichlet character χ mod q > 1, the analogues of A, B, C and D for the zeros of L(s,χ) (Mathlib's `DirichletCharacter.LFunction χ`) | `dirichlet_two_thirds_on_critical_line`, `dirichlet_two_thirds_simple_on_critical_line`, `dirichlet_five_sixths_distinct`, `dirichlet_montgomery_taylor_on_critical_line`, `dirichlet_montgomery_taylor_*_mult` | `Zeta23.ThmE.thmE_A₀`, `thmE_B₀_mult`, `thmE_C₀_mult`; `Zeta23.ThmDE.thmE_D₀`, `thmE_D₀_simple_mult`, `thmE_D₀_dist_mult` |

Note on Theorem C: in this repository the constant 5/6 is obtained from the rank–trace inequality of §3 applied with
parameter c = 3 (`Zeta23.ZeroSide.ZeroBlockData.mult_three`, `Zeta23/ZeroSide/Mult.lean`); the paper's text derives the
same 5/6 from Proposition 4.5(iii) with c = 2.

Also proved here, beyond the statements of Theorems A–E: the rank–trace certificate ("Lemma R") is TIGHT — for on-line
atoms with integer multiplicities m_j ≤ c on orthonormal vectors together with b pair-blocks of eigenvalue c,
2c·tr(P+Q) − ‖P+Q‖_F² = Σ_j k_c(m_j) + c²·b, i.e. the inequality cannot be improved using only these quantities
(`Zeta23.ZeroSide.TightMult.lemmaR_tight`, `Zeta23/ZeroSide/TightMult.lean`; cited in the paper's appendix).

Also included, beyond Theorems A–E (each group has its own trusted statement file under [`comparator/`](comparator/) or, where noted, is checked with `#print axioms` only):

* **The zeros of ξ′** (`Zeta23/XiPrime/`, comparator topic `XiPrime`, six statements): unconditionally, at least 0.85838 of the zeros of ξ′ (the derivative of the completed zeta function) with ordinates in (T, 2T] are simple and on the critical line and at least 0.92919 are distinct (flat window; 0.86864 / 0.93432 with the quartic window), all zeros of ξ′ lie in the open critical strip, and Re ξ′/ξ > 0 on Re s ≥ 1 — `Zeta23.XiPrime.xiDeriv_simple_on_line`(`_cumulative`, `_quartic_std`) in `Zeta23/XiPrime/Final.lean`. The argument is the one of Theorem B with ξ′ in place of ζ (the rank–trace device applied to the Farmer–Gonek(–Lee)/Montgomery argument for ξ′; Farmer–Gonek, arXiv:0803.0425 = Farmer–Gonek–Lee, J. London Math. Soc. (2) 90 (2014)). In the docstrings under `Zeta23/XiPrime/`, labels of the form `[XF′ Lemma 6.1]`, `[XF′ Thm 8.2]`, `[XF′ (Z3)]` refer to the authors' technical supplement on the explicit formula for ξ′/ξ and the two-trace transfer, which is not included in this repository; these labels record provenance only — what is relied upon is in each case the Lean statement that the docstring introduces. (The counting functions in `comparator/ChallengeDeps/XiPrime.lean` are finite sums / cardinalities over the set of zeros of ξ′ in a height window; that set is finite because every zero of ξ′ lies in the open critical strip — the first of the six statements — and the zeros of an entire function are isolated.)

* **The bandwidth-one ceiling** (`Zeta23/PairCeiling/`, no comparator topic; `#print axioms` audit below): the stability inequality behind the paper's remark on the optimality of the method — for every certificate (c₀, r) of the type used in Theorem B (r ∈ C¹[0,1], r′ differentiable off a countable set with integrable derivative) that is valid against a configuration whose form-factor measure has grid masses s_j and simple-point fraction p, one has c₀ + ∫₀¹ r(x)·x dx ≤ p + |r(1)|·|D(1)| + |r′(1)|·|E(1)| + (sup|E|)·∫₀¹|r″| (`Zeta23.PairCeiling.ceiling_stability`, `Zeta23/PairCeiling/Stability.lean`, two integrations by parts) — and its instance at an explicit 256-periodic law (`Zeta23.PairCeiling.ceiling_law256`, `ceiling_law256_decimal`, `ceiling_nearCUE_signed`, `ceiling_law256_signed`; files `NearCUE.lean`, `RowCert.lean`, `LawN256.lean`, `CeilingLaw256.lean`, `Signed.lean`): every bandwidth-one certificate certifies a proportion of simple zeros at most 0.6818287 + 2.55·10⁻⁶·(|r′(1)| + ∫|r″|). The ONE displayed hypothesis of these theorems is `EnclOK`: that the law's form factor S(j), j = 1…256, lies in the 256 integer enclosures recorded in `LawN256.lean` (obtained outside Lean by interval arithmetic from an exact-rational certificate, sha256 `cc3de9917db4d14d844630a4e97dda8387fd6e257e52b6967f430b8914584eb8`, available from the authors); everything downstream of the enclosures — the 255 near-CUE row inequalities |256·S(j) − j| ≤ 3·10⁻⁴⁰ (0 < j < 256), the edge bound |D(1)| ≤ 0.82395317, the sign of the edge term — is checked in the kernel by `decide` (`LawN256_check`, `LawN256_edge`), and the analytic inequality is proved in Lean.

How the two comparator configurations cover this: [`comparator/config.json`](comparator/config.json) (fifteen statements,
[`comparator/Challenge.lean`](comparator/Challenge.lean)) contains Theorem A together with the *Cauchy–Schwarz forms* of
B–E — N₀ˢ/N ≥ 1/2, N_d/N ≥ 3/4, and with the optimal window 2c₁* − 1 (= 0.50659…) and c₁*, for ζ and for L(s,χ)
(`Zeta23.thmB₀`, `Zeta23.thmC₀`, `Zeta23.ThmD.thmD₀_simple`, … in `Zeta23/Final.lean`, `Zeta23/ThmD/Final.lean`,
`Zeta23/ThmE/Final.lean`, `Zeta23/ThmDE/Final.lean`). [`comparator/config-multiplicity.json`](comparator/config-multiplicity.json)
(twelve statements, [`comparator/Challenge/Multiplicity.lean`](comparator/Challenge/Multiplicity.lean)) contains B–E with the
constants stated in the paper. In this formalization the latter are obtained from the same analytic inputs by the
rank–trace inequality of §3 applied with parameter c = 2 (simple zeros) and c = 3 (distinct zeros) to the
multiplicity-aware zero side (`Zeta23/ZeroSide/Mult.lean`, `Zeta23/Assembly/SeamMult.lean`, `Zeta23/FinalMult.lean`).
The same A–C statements in the Cauchy–Schwarz form, with the same names inside namespace `Zeta23`, are in
[`Zeta23/Unconditional.lean`](Zeta23/Unconditional.lean).

### Layout

```
comparator/          trusted statements (ChallengeDeps, Challenge), untrusted Solution, comparator config — START HERE
Zeta23/Statement.lean  nontrivial zeros, multiplicity, the counting functions, against Mathlib's riemannZeta
Zeta23/Unconditional.lean, Zeta23/Final.lean, Zeta23/FinalMult.lean      Theorems A, B, C (ζ)
Zeta23/ThmD/           Theorem D (the optimal Montgomery–Taylor window; variational problem in ThmD/Functional.lean; ThmD/Mult.lean)
Zeta23/ThmE/           Theorem E (primitive Dirichlet L-functions); Zeta23/ThmDE/: Theorem D for L(s,χ)
Zeta23/LinAlg/         §3 of the paper: Sylvester inertia, rank–trace inequality (via von Neumann), Cauchy–Schwarz count, Weyl
Zeta23/WeilEF/, Zeta23/ExplicitFormula*   Weil's explicit formula (contour integration, Landau's lemma, zero-sum limits)
Zeta23/RvM/            Riemann–von Mangoldt formula (argument principle, Backlund's bound via Jensen, local zero counts)
Zeta23/GammaFacts/, Zeta23/Analytic/   Γ′/Γ estimates on vertical lines (Stirling) and other analysis
Zeta23/Chebyshev.lean, Zeta23/FromPNTPlus/     Chebyshev–Mertens estimates; files ported (with attribution headers) from PrimeNumberTheoremAnd
Zeta23/MV/             Montgomery–Vaughan generalized Hilbert inequality
Zeta23/PrimeSideA/, PrimeSideB/, Poisson.lean, Taper/   the prime side: traces of the Gram matrix (paper §§4–5)
Zeta23/ZeroSide/, Tail/                the zero side: block structure, tail bounds (paper §§2, 6)
Zeta23/Assembly/, Main.lean            assembly of the certificate (paper §6)
Zeta23/XiPrime/         zeros of ξ′: explicit formula for ξ′/ξ, coefficient system, certificates, headline theorems (XiPrime/Final.lean)
Zeta23/PairCeiling/     the bandwidth-one ceiling: definitions, stability inequality (Stability.lean), near-CUE constants, integer row certificates, the N = 256 law instance
ZetaQ/, ZetaQ.lean, audit/   the conductor-aspect library added by Oliver D'Souza — see below; not built by `lake build`
```

Throughout the docstrings of `Zeta23/`, bracketed labels such as `[prop:PP]`, `[eq:tr2]`, `[thm:E]`, `[lem:R]` are the LaTeX labels of the corresponding statements and equations in the paper's source; they identify which step of the paper a declaration formalizes.

### Building and checking

Install [`elan`](https://github.com/leanprover/elan); the right Lean toolchain is selected automatically
from `lean-toolchain`.

```bash
lake exe cache get        # fetch prebuilt Mathlib for the pinned commit (a few GB). If this fails (no cache
                          # for your platform / offline), just proceed: the next step builds Mathlib from
                          # source, which takes several hours of CPU time but needs nothing else.
lake build                # builds library Zeta23 (the default target imports exactly the headline modules)
lake build Solution Solution.Multiplicity Solution.XiPrime
lake env lean comparator/PrintAxioms.lean; lake env lean comparator/PrintAxioms/Multiplicity.lean; lake env lean comparator/PrintAxioms/XiPrime.lean   # axiom audit of the 15 + 12 + 6 theorems
lake env lean comparator/PrintAxioms/PairCeiling.lean   # axiom audit of the ceiling theorems (no trusted statement file; see AUDIT.md)
```

Expected: no errors, no `sorry` warnings from `Zeta23/` or `Solution`, and 33 lines of the
form `'two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
The `sorry`s in this repository are the 33 deliberate ones in the trusted challenge statement files
under `comparator/` (15 + 12 + 6), plus four in `ZetaQ/` — the separate library described in the next
section, which `lake build` does not build and which nothing under `Zeta23/`, `comparator/` or
`Solution` depends on. Repository-wide total: 37.
For the strongest independent check — statement equality against the trusted challenge plus kernel replay —
run comparator as described in [`comparator/README.md`](comparator/README.md).


### ZetaQ — the conductor aspect

`ZetaQ/` is a **separate library added to this repository by Oliver D'Souza (2026)**, not part of the
Anthropic artifact described above; it is released under the same Apache 2.0 licence (see
[`NOTICE`](NOTICE)). It builds on `Zeta23` and proves a conductor-aspect ("q-aspect") analogue of
Theorems B and E: for a FAMILY of primitive Dirichlet characters of conductor up to `Q`, a positive
proportion of the zeros of `L(s, χ)` in a height window are simple and on the critical line — the
proportion being measured against the family's own total zero count, and the gain over B/E coming
from averaging over the family rather than over height.

The conductor-aspect paper itself is **not** part of this repository. The `§n` references
throughout `ZetaQ/` identify which step of that argument a declaration formalizes, in the same way
the `[prop:PP]`-style labels do under `Zeta23/`; what is relied upon is in every case the Lean
statement the docstring introduces, and nothing in the build depends on an unshipped file.

Start at the module docstring of [`ZetaQ.lean`](ZetaQ.lean) and at [`ZetaQ/README.md`](ZetaQ/README.md).

**What is proved.** Ten theorems, all in namespace `ZetaQ.JoinProved`: six stated in
[`ZetaQ/Margin.lean`](ZetaQ/Margin.lean) and the four Corollary 3″ rows in
[`ZetaQ/Cor3Full.lean`](ZetaQ/Cor3Full.lean). Each takes only `(hr : 3 ≤ r) (hε : 0 < ε)` and no other
hypothesis. With `T = (log Q)^{r+ε}`, `𝒩 = Σ_χ N_χ(T, 2T)` the family zero count and `Σ_χ N⁰ˢ_χ(T, 2T)`
the count of family zeros that are simple and on the critical line, each states
`∃ Q₀ c, 0 < c ∧ ∀ Q ≥ Q₀, (P − c·log log Q / log Q)·𝒩 ≤ Σ_χ N⁰ˢ_χ` over the family in its row:

| Lean name (`ZetaQ.JoinProved`) | `P` | family |
|---|---|---|
| `theorem_one_generic_proved'` | 0.7212 | `q ≤ Q` (`Family.qle`) |
| `corollary_two_dyadic_proved'` | 0.7098 | `Q/2 < q ≤ Q` (`Family.dyadic`) |
| `corollary_three_even_qQ_proved'` | 0.698 | `q ≤ Q`, χ even |
| `corollary_three_odd_qQ_proved'` | 0.698 | `q ≤ Q`, χ odd |
| `corollary_three_even_dyadic_proved'` | 0.6919 | `Q/2 < q ≤ Q`, χ even |
| `corollary_three_odd_dyadic_proved'` | 0.6919 | `Q/2 < q ≤ Q`, χ odd |
| `corollary_three_even_qQ_full_proved'` | **0.7212** | `q ≤ Q`, χ even |
| `corollary_three_odd_qQ_full_proved'` | **0.7212** | `q ≤ Q`, χ odd |
| `corollary_three_even_dyadic_full_proved'` | **0.7098** | `Q/2 < q ≤ Q`, χ even |
| `corollary_three_odd_dyadic_full_proved'` | **0.7098** | `Q/2 < q ≤ Q`, χ odd |

**Corollary 3″ (branch `reflected-sieve`).** The last four rows are about the SAME parity
families' zero counts (`Family.evenQle`, …) as the four rows above them, at the FULL families'
constants: the reflected large sieve ([`ZetaQ/ReflectedSieve.lean`](ZetaQ/ReflectedSieve.lean))
charges one parity class `Q²/2 + π(N + ½)`, so a parity family's out-zone constant is the full
family's `C`, and Theorem 1's / Corollary 2's certificates apply. They are stated in
[`ZetaQ/Cor3Full.lean`](ZetaQ/Cor3Full.lean) (same namespace) and proved through the four
reflected-sieve families `Family.evenQleR`/`oddQleR`/`evenDyadicR`/`oddDyadicR` (parity
characters, full-family design), whose zero counts are the parity families' by `rfl`. The
0.698 / 0.6919 rows are kept unchanged.

The counting functions `ZetaQ.NcountQ` / `ZetaQ.N0sQ` ([`ZetaQ/Certificate.lean`](ZetaQ/Certificate.lean))
wrap `Zeta23.ThmE.NcountL` / `N0simpleL`, which are defined against Mathlib's
`DirichletCharacter.LFunction`. The constants are four-digit *feasibility* constants, deliberately
weaker than the paper's ten-digit variational optima; the two are kept as distinct symbols
(`ZetaQ.Payoff.Pcert_*_smooth` versus `ZetaQ.Pconst`, see [`ZetaQ/Payoff.lean`](ZetaQ/Payoff.lean)).

**What is assumed.** Nothing: `#print axioms` on each of the ten reports
`[propext, Classical.choice, Quot.sound]`, and `#print sorries` on each returns nothing. Lemma 6.1,
the multiplicative large sieve, is consumed at Gallagher's elementary budget `Q² + πN`
([`ZetaQ/Gallagher.lean`](ZetaQ/Gallagher.lean); Gallagher 1967, Montgomery, Bull. AMS 84 (1978),
Thm 1), whose `Q²` — the only term that reaches the family constant — is that of the sharp budget
`N + Q² − 1`, so no certified constant moved. The sharp chain is kept in
[`ZetaQ/Sieve.lean`](ZetaQ/Sieve.lean) as a record; its one gap,
`ZetaQ.l2_concentration_exists` — the `L²` concentration statement behind the sharp sieve, i.e.
Selberg's extremal problem, proved there for the band `(N−1)δ ≤ 1` and for `δ = 1` — is still a
`sorry`, but no headline theorem consumes it. No `axiom` is declared anywhere in `ZetaQ/`.

`ZetaQ/` contains three further `sorry`s, all in [`ZetaQ/Budget.lean`](ZetaQ/Budget.lean):
`trace_row`, `frobenius_row` and `assembly_at_lamStar`. These are superseded statements, frozen
together with the record of why the method does not reach them as stated and replaced by proved
eventual / certified-constant forms elsewhere in the tree. **No proved theorem consumes them**;
`audit/RevDepZetaQ.lean` is the reverse-dependency check.

**Building and checking.**

```bash
lake build ZetaQ                        # ZetaQ is deliberately outside defaultTargets
lake env lean audit/final_check.lean    # `#print sorries` on the six theorems
lake env lean audit/final_axioms.lean   # `#print axioms` on the headline route
```

Expected: build completes with exactly four `declaration uses 'sorry'` warnings, one for each
declaration named above (none consumed by a headline); `final_check.lean` prints no sorries for
any of the six, and `final_axioms.lean` prints `[propext, Classical.choice, Quot.sound]` for each
of the six headlines (and `sorryAx` only for the unconsumed sharp `multiplicative_large_sieve`).

The rest of [`audit/`](audit/) is the receipts behind the claims above: `AxiomAuditZetaQ.lean`
partitions every `ZetaQ` declaration by whether `sorryAx` is in its proof-term closure (which the
build's warning count does *not* measure, since the warning does not propagate);
`RevDepZetaQ.lean` and `DepAuditProofTerm.lean` are the reverse-dependency and λ ≤ 1 / `D₀ = √T`
gate audits; `audit_axioms.lean` is the axiom gate for the `Zeta23`-side layers `ZetaQ` builds on;
`FlatTaperAudit.lean` measures the reach of the flat-taper facade; the `*_REPORT.md` files and the
small Python scripts are the numerical receipts for the constants, each named from the docstring
that quotes it.

### Provenance and attribution

Files under `Zeta23/FromPNTPlus/` are ported from the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project (Apache 2.0); each
carries a header naming the upstream file and commit, the upstream copyright and license, and the local
modifications; the upstream text (including its informal comments) is otherwise unedited. `Zeta23/LinAlg/` (the
linear-algebra core of §3: von Neumann's trace inequality for Hermitian matrices, both directions of Sylvester's law
of inertia, the rank–trace inequality and Weyl's bound) was written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the
paper, by the paper's authors, and is incorporated here unchanged; it has no upstream outside this project. Everything builds on [Mathlib](https://github.com/leanprover-community/mathlib4).

Released under the Apache License, Version 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
