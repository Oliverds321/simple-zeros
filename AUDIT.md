# Audit record

**Scope.** Everything in this file up to and including "Amendment: the zeros of ξ′ and the bandwidth-one ceiling" is the upstream audit record. It was obtained on the **pristine upstream tree**, and it covers `Zeta23/`, `comparator/` and the `Solution` files **only**. `Zeta23/` has since been modified — three modules added, and `Params.Valid` hypotheses weakened to `Params.ValidQ` in twenty-one modules; `comparator/` is untouched. The changes are hypothesis weakenings and additions, so every statement recorded below still holds and the trusted challenge files are byte-identical, but the job counts and timings below are those of the pristine tree. `NOTICE` states the modifications in full. It says nothing about `ZetaQ/`, the conductor-aspect library added to this repository later (see the top-level `README.md` and `ZetaQ/README.md`); in particular, the two `sorry` censuses below — 27, then 33 — are counts over `Zeta23/` + `comparator/` at those revisions, not repository-wide counts today. The repository-wide count now is **37**; the closing section "Amendment 2" restates it with the ZetaQ figures and records the ZetaQ checks. Nothing under `Zeta23/`, `comparator/` or `Solution` imports or depends on `ZetaQ/`, so none of the results below is affected by its presence.

This file records the checks that were run on exactly the sources in this repository and how to reproduce them. Nothing here is part of the trusted base: a reader can re-run everything below, and can run the [comparator](https://github.com/leanprover/comparator) tool against the trusted statement files in `comparator/` (see `comparator/README.md`).

Toolchain: Lean `leanprover/lean4:v4.33.0-rc2`; Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (the commit Mathlib's tag `v4.33.0-rc2` points to, read from the tag archive; pinned in `lake-manifest.json`). Library name: `Zeta23`. Repository: <https://github.com/anthropics/zeta-23-lean>.

## How to reproduce

```bash
lake exe cache get            # optional: prebuilt Mathlib for the pinned commit; otherwise Mathlib builds from source
lake build                    # the Zeta23 library (default target: the headline modules imported by Zeta23.lean)
lake build Solution && lake env lean comparator/PrintAxioms.lean
lake build Solution.Multiplicity && lake env lean comparator/PrintAxioms/Multiplicity.lean
lake build Solution.XiPrime && lake env lean comparator/PrintAxioms/XiPrime.lean
lake env lean comparator/PrintAxioms/PairCeiling.lean
lake build Challenge          # the trusted statement files; expect only the deliberate sorry placeholders
```

## Recorded results at this commit

* `lake build`: completed successfully (8890 jobs, counting the Mathlib dependency closure); no errors and no `sorry` warnings.
* `lake build Solution` and `lake build Solution.Multiplicity`: completed successfully; no errors and no `sorry` warnings.
* `lake build Challenge` and the topic challenge files: complete with `declaration uses 'sorry'` warnings **only** in the trusted statement files, which state each theorem with a placeholder proof by design (`comparator/Challenge.lean`: 15, `comparator/Challenge/Multiplicity.lean`: 12), and with no other warnings or errors.
* Declarations of new axioms (`axiom ...`) anywhere in the repository, counted on the sources with comments and docstrings stripped: **0**.
* Occurrences of the `sorry` token outside comments, over `Zeta23/` + `comparator/` + `Solution` (see the scope note at the head of this file; `ZetaQ/` did not exist at this revision): **27**, all in the trusted challenge statement files (`comparator/Challenge.lean`: 15, `comparator/Challenge/Multiplicity.lean`: 12); none under `Zeta23/` and none in any `Solution` file.
* Axiom audit: every line printed by the `#print axioms` commands below is exactly `[propext, Classical.choice, Quot.sound]`, Lean's three standard axioms; in particular no `sorryAx` and no project-specific axiom.

### `#print axioms` for the 27 comparator statements (`comparator/PrintAxioms*.lean`), verbatim

```
'two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_thirds_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'half_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'half_simple_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'three_quarters_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'three_quarters_distinct_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_two_thirds_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_half_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_three_quarters_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_thirds_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'two_thirds_simple_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'five_sixths_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'five_sixths_distinct_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_simple_on_critical_line_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_simple_on_critical_line_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_distinct_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'montgomery_taylor_distinct_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_two_thirds_simple_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_five_sixths_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_simple_on_critical_line_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichlet_montgomery_taylor_distinct_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `#print axioms` for the 28 `Zeta23` library theorems behind them (the theorems the comparator statements delegate to, plus the further results listed in README), verbatim

Each `Solution` theorem is a short delegation to the corresponding `Zeta23` theorem, so the two lists necessarily agree; the library names are the ones a reader of the library (or of the paper's appendix) will look for.

```
'Zeta23.thmA₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmA₀_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_simple' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_A₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_B₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_C₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀_simple' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmB₀_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.thmC₀_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_simple_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_simple_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_dist_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmD.thmD₀_dist_mult_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_B₀_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmE.thmE_C₀_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀_simple_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ThmDE.thmE_D₀_dist_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.ZeroSide.TightMult.lemmaR_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Comparator

The trusted statement files and configurations for the comparator tool are in `comparator/`: `config-multiplicity.json` (12 statements), `config.json` (15 statements), `config-xiprime.json` (6 statements). `comparator/README.md` explains what is trusted (`ChallengeDeps*.lean`, `Challenge*.lean`: Mathlib-only definitions and the statements) and what is not (`Solution*.lean` and the whole library), and how to run the tool, which independently re-checks that every `Solution` theorem has exactly the statement of its `Challenge` namesake and re-verifies the proofs in an external kernel.

## Amendment: the zeros of ξ′ and the bandwidth-one ceiling

This revision adds `Zeta23/XiPrime/` (comparator topic `XiPrime`, six statements) and `Zeta23/PairCeiling/` (no comparator topic), and replaces 69 shared modules by later versions with the same public statements (the trusted files `comparator/ChallengeDeps.lean`, `Challenge.lean`, `Challenge/Multiplicity.lean` are unchanged byte for byte). The checks above were re-run on exactly these sources:

* `lake build` (default target): completed successfully (9010 jobs); no errors and no `sorry` warnings.
* `lake build Solution Solution.Multiplicity Solution.XiPrime Challenge Challenge.Multiplicity Challenge.XiPrime ChallengeDeps ChallengeDeps.XiPrime`: complete, with `declaration uses 'sorry'` warnings **only** in the trusted statement files (`comparator/Challenge.lean`: 15, `comparator/Challenge/Multiplicity.lean`: 12, `comparator/Challenge/XiPrime.lean`: 6) and no other warnings or errors.
* Occurrences of the `sorry` token outside comments, over `Zeta23/` + `comparator/` + `Solution` (scope note at the head of this file): **33**, all in the three trusted challenge files; none under `Zeta23/` and none in any `Solution` file. No `axiom` declarations anywhere in the repository outside the trusted challenge files' deliberate `sorry`s (the word `axiom` occurs in `Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean` only inside a commented-out upstream test block, unchanged from upstream and from the previous revision; it declares nothing).
* `#print axioms`, 15 + 12 + 6 comparator statements (`comparator/PrintAxioms.lean`, `PrintAxioms/Multiplicity.lean`, `PrintAxioms/XiPrime.lean`): every line `[propext, Classical.choice, Quot.sound]`. The six ξ′ lines:

```
'xiPrime_zeros_in_open_critical_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_over_xi_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_quartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'xiPrime_simple_zeros_on_critical_line_quartic_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `#print axioms`, the ceiling theorems (`comparator/PrintAxioms/PairCeiling.lean`). All of these except the two kernel checks carry the displayed hypothesis `EnclOK` described in the README:

```
'Zeta23.PairCeiling.ceiling_stability' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_nearCUE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.lawN256_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_law256' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_law256_decimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_nearCUE_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.ceiling_law256_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.D1_nonneg_of_edgeNonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zeta23.PairCeiling.LawN256_check' depends on axioms: [propext]
'Zeta23.PairCeiling.LawN256_edge' does not depend on any axioms
```

* Comparator (statement equality against the trusted files + kernel replay, with the independent `nanoda` kernel enabled): `config.json` — "Your solution is okay!" (343 s); `config-multiplicity.json` — okay (335 s); `config-xiprime.json` — okay (345 s).

## Amendment 2: ZetaQ — the conductor-aspect library

*As to the headline `sorry`, this amendment is superseded by Amendment 3 (the Gallagher rethread) below: the six headline theorems no longer depend on `ZetaQ.l2_concentration_exists`.*

This section covers `ZetaQ/`, `ZetaQ.lean` and `audit/`, added to the repository by Oliver D'Souza (see `NOTICE` and the ZetaQ section of `README.md`). Nothing under `Zeta23/`, `comparator/` or `Solution` depends on any of it.

### Reproduce

```bash
lake build ZetaQ                        # ZetaQ is deliberately outside defaultTargets
lake env lean audit/final_check.lean    # `#print sorries` on the six headline theorems
lake env lean audit/final_axioms.lean   # `#print axioms` on the headline route
```

### Recorded results

* `lake build ZetaQ`: `Build completed successfully (9051 jobs)`, counting the Mathlib dependency closure and the `Zeta23` library; no errors.
* Exactly **four** `declaration uses 'sorry'` warnings, and no others:

```
warning: ZetaQ/Sieve.lean:2102:8: declaration uses `sorry`
warning: ZetaQ/Budget.lean:1688:8: declaration uses `sorry`
warning: ZetaQ/Budget.lean:1739:8: declaration uses `sorry`
warning: ZetaQ/Budget.lean:6312:8: declaration uses `sorry`
```

  These are `ZetaQ.l2_concentration_exists` and the three frozen, superseded statements `ZetaQ.trace_row`, `ZetaQ.frobenius_row`, `ZetaQ.assembly_at_lamStar`. No theorem the library proves consumes any of the latter three; `audit/RevDepZetaQ.lean` is the proof-term reverse-dependency check.
* Declarations of new axioms (`axiom ...`) under `ZetaQ/` or `audit/`: **0**.
* Occurrences of the `sorry` token outside comments, repository-wide: **37** = 15 (`comparator/Challenge.lean`) + 12 (`comparator/Challenge/Multiplicity.lean`) + 6 (`comparator/Challenge/XiPrime.lean`) + 4 (`ZetaQ/`: `Sieve.lean` 1, `Budget.lean` 3). None under `Zeta23/`, none in any `Solution` file.
* `lake env lean audit/final_check.lean`: `#check` on each of the six headline theorems, then `#print sorries` on each. The six `#print sorries` outputs are identical and name **one** declaration, `ZetaQ.l2_concentration_exists`, six times and nothing else:

```
ZetaQ.l2_concentration_exists has sorry of type
  ∃ ψ,
    MeasureTheory.MemLp ψ 2 MeasureTheory.volume ∧
      (∀ t ∉ Set.Ioc 0 δ, ψ t = 0) ∧
        ∫ (t : ℝ) in 0..δ, ‖ψ t‖ ^ 2 = ↑N - 1 + δ⁻¹ ∧
          ∀ (n : ℤ), 1 ≤ n → n ≤ ↑N → 1 ≤ ‖∫ (t : ℝ) in 0..δ, ψ t * ZetaQ.e (-(↑n * t))‖
```

* `lake env lean audit/final_axioms.lean`, verbatim:

```
'ZetaQ.JoinProved.theorem_one_generic_proved'' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'ZetaQ.JoinProved.corollary_two_dyadic_proved'' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'ZetaQ.HFrob.hfrob_qle_of_sep' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'ZetaQ.exists_designOfRecordM' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Cor3.EvenFamInstance.admissible_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Cor3.EvenFamInstance.admissible_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Cor3.EvenFamInstance.corollary3_even_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

  The `sorryAx` in the first three is exactly the one `#print sorries` localises to `ZetaQ.l2_concentration_exists`; `#print axioms` cannot say *which* `sorry` it came from, which is why `final_check.lean` exists.

### What that means

`ZetaQ` is **not** sorry-free, and does not claim to be. Its six headline theorems (`ZetaQ/Margin.lean`, namespace `ZetaQ.JoinProved`; listed in `README.md`) are proved from Mathlib, `Zeta23`, and exactly one unproved statement — `ZetaQ.l2_concentration_exists`, the `L²` concentration input to Lemma 6.1's sharp multiplicative large sieve, which the paper cites from the literature. Statements the library declines to prove are, wherever practical, carried as named `Prop`s rather than as `sorry`-ed theorems, so that a consumer must name them in its own signature; `ZetaQ/Payoff.lean`'s header states that policy and `ZetaQ/Zones.lean`'s STATUS block lists that file's four.

### Editorial revision of the `ZetaQ/` prose, and the check that it changed no code

Before release the prose under `ZetaQ/` was revised for a reader outside the authoring project. Removed: the session dates and per-pass changelogs, the per-declaration work-brief fields (`Track:`, `Difficulty:`), the `SORRY_LEDGER` tags, and every pointer to a working document that is not part of this repository. Kept, and in most places restated by subject rather than by finding number: the recorded false routes and the counterexamples that closed them, which are the reason much of this prose exists. Corrected: eleven declaration names cited under a namespace they do not live in, or (twice) under a name never declared at all, in 25 places; eight false import-graph claims, of the form "nothing imports X" or "X imports only Y"; and every file:line citation `ZetaQ/` made into one of its own files — every one of them pointing at the wrong line — which now gives the declaration or the file instead.

**No statement, definition or proof was touched**, and that was checked mechanically rather than asserted. Lean comments — nested `/- -/`, `--`, with string literals respected — were stripped from every `.lean` file under `ZetaQ/` at the pre-revision commit and at the released one, the remaining whitespace normalised, and the two compared file by file: **34 files compared, 0 added, 0 removed, 0 differing.**

## Amendment 3: the Gallagher rethread — the six headlines no longer depend on any `sorry`

Branch `gallagher-rethread` (from `phase2-skeleton` at `2c2a8a5`). Lemma 6.1 is now consumed at **Gallagher's budget** `Q² + πN` instead of the sharp `N + Q² − 1`:

* `ZetaQ/Gallagher.lean` (new; imports `ZetaQ.Sieve` only) proves, sorry-free, Gallagher's additive large sieve `Σ_i|S(θ_i)|² ≤ (δ⁻¹ + πN)Σ|a_n|²` for `δ`-separated points mod 1 (`gallagher_additive_large_sieve`, in the binder shape of `SharpAdditiveLargeSieve`), and from it, by `Sieve.lean`'s own Farey / Gauss-sum deduction with the `φ(q)/q ≤ 1` drop, `multiplicative_large_sieve_gallagher` at budget `Q² + πN` (plus subfamily and family forms).
* `Ends.LargeSieveHyp`, `Zones.LargeSieveFamily` and `Zones.sieveBudgetQ` (now `Q² + πX`) are stated at that budget, and `Ends.largeSieve_holds` / `largeSieveFamily_holds` are discharged from `Gallagher.lean` as bare terms.
* The only consumer-visible constant that moved is the `2` of `Zones.lemma43_budget_is_Qsq` (`|B/Q² − 1| ≤ 2Q^{−δ}` → `4Q^{−δ}`), because `B/Q² − 1 = πX/Q²` and `π > 2`. It propagates into `lemma43_family_le_C_diagonal` (inside its explicit `η`), the statement of `lemma43_family_le_C_diagonal_pointwise`, `FrobAssembly.famPP_le_sieve` and `FrobAssembly.PPsieve` (`1 + 2Q^{−δ}` → `1 + 4Q^{−δ}`), and `FrobAssembly.A4_eventually`, whose local `K` takes `8/η` in place of `4/η`. `FrobAssembly.design_regime` is untouched; InZone's `hBQ` still closes from its unchanged `2Q^{−1/2} ≤ 1/max 1 (3/δ)`. Ends' `Bfam_le_sep` uses the new `pi_mul_X_le_of_sieve_eff` (`πX ≤ 10⁻⁴Q²` at `Q ≥ 10⁹`, `δ ≥ 1/2`; margin 0.4 %), so its `1.0001`/`1.00005` arithmetic and its statement are unchanged.
* No certified constant moved: `Q²` — the only term of the budget that reaches `C = Q²/|𝔉_Q|` — is identical. `ZetaQ/Budget.lean` is byte-identical to `phase2-skeleton` (`git diff phase2-skeleton -- ZetaQ/Budget.lean` is empty), so its five frozen statements are untouched.
* The sharp chain of `Sieve.lean` — `l2_concentration_exists`, the Selberg majorant, `sharp_additive_large_sieve`, `multiplicative_large_sieve`, and the refutation `sharpAdditiveLargeSieveUnrestricted_false` — is kept unchanged as the record of the sharp statement; nothing on the headline route consumes it.

### Recorded results (26 Sep 2026)

* `lake build ZetaQ`: `Build completed successfully (9052 jobs)`; no errors. Exactly four `declaration uses 'sorry'` warnings, as before: `ZetaQ/Sieve.lean:2125:8` (`l2_concentration_exists`; the line moved because of a header note) and `ZetaQ/Budget.lean:1688:8`, `:1739:8`, `:6312:8`.
* `lake env lean audit/final_check.lean`: `Declarations are sorry-free!` for each of the six headline theorems.
* `lake env lean audit/final_axioms.lean` (extended to all six headlines and to the sieve), verbatim:

```
'ZetaQ.JoinProved.theorem_one_generic_proved'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.JoinProved.corollary_two_dyadic_proved'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.JoinProved.corollary_three_even_qQ_proved'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.JoinProved.corollary_three_odd_qQ_proved'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.JoinProved.corollary_three_even_dyadic_proved'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.JoinProved.corollary_three_odd_dyadic_proved'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.HFrob.hfrob_qle_of_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.exists_designOfRecordM' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Cor3.EvenFamInstance.admissible_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Cor3.EvenFamInstance.admissible_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Cor3.EvenFamInstance.corollary3_even_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Gallagher.gallagher_additive_large_sieve' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Gallagher.multiplicative_large_sieve_gallagher' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.Ends.largeSieve_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.largeSieveFamily_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaQ.multiplicative_large_sieve' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The last line is the sharp sieve, kept and unconsumed. **The six headline theorems are proved from Mathlib and `Zeta23` alone, with Lean's three standard axioms and no `sorry`.** The four remaining `sorry`s in `ZetaQ/` (`l2_concentration_exists` and the three frozen `Budget.lean` statements) are consumed by no headline.
