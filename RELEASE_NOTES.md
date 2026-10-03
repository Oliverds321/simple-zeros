# Release notes: v1.0

- Version: 1.0.0
- Tag: `v1.0`
- Date: 3 October 2026 (prepared on 2 October; the proof of the family main theorem and its comparator topic added on 3 October)
- Repository: <https://github.com/Oliverds321/simple-zeros>, a single-commit snapshot of the release. The commits named
  in these notes and in the papers (`4874cc0`, `b9f9c91`, `dcd371e`, `bb7223b`, ...) are commits of the development
  history, which is not published; the `git diff` checks below were run there.
- Toolchain: Lean `v4.33.0-rc2`, Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129` (pinned in `lake-manifest.json`)
- Licence: Apache License, Version 2.0 (`LICENSE`, `NOTICE`); the text of the two papers in `papers/`: CC BY 4.0 (`NOTICE`)

## What is in the release

This repository is a modified copy of the Lean artifact `zeta-23-lean` (upstream library `Zeta23`, and the
conductor-aspect library `ZetaQ` added earlier; both unchanged in this release). The release adds the follow-up work
of September and October 2026:

| part | where | what |
|---|---|---|
| the ζ paper | `papers/zeta/` | sources and PDF |
| the family paper | `papers/family/` | sources and PDF |
| library `ZetaS` | `ZetaS/`, `ZetaS.lean`, `ZetaSCertShims/` | the ζ follow-up: simple and distinct zeros, simple zeros on the critical line, zeros that are simple or on the line; the certificate checker v3 and its soundness chain |
| library `ZetaShell` | `ZetaShell/`, `ZetaShell.lean` | the family follow-up: Theorem 1′ (0.7235) and the main theorem (0.9059137927, under the zero-density estimates), with its certificate (`ZetaShell/README.md`) |
| library `ZetaSReplay` | `ZetaSReplay/` | the kernel replay of the K = 5 certificate `CertAM5`: 1,478 generated modules, run on 28 September 2026 (1,478 of 1,478, no failure, 20.4 Lean-hours); with it the K = 5 theorems need no hypothesis (`ZetaSReplay/README.md`) |
| comparator topic `FollowUpZeta` | `comparator/` | the fourteen trusted statements of the ζ paper, their proofs, the comparator configuration, and `#print axioms` files (also `FollowUpShell.lean`, `FollowUpReplay.lean`) |
| comparator topic `FollowUpFamily` | `comparator/` | the two trusted statements of the family paper over a file of definitions that imports Mathlib only, their proofs, the comparator configuration, and `PrintAxioms/FollowUpFamily.lean` (`comparator/README_followup_family.md`) |
| supplementary data | `supplementary/` | the certificates' exact-rational data, certifier scripts and logs, the generator of the replay, the tested Python versions (`requirements.txt`) and tests of the scripts' failure handling (`tests/`; `supplementary/VERIFY.md`) |
| evidence | `audit/followup/` | the build logs and axiom censuses of the release commit |

The results, with their Lean names, modules, trust level and hypotheses, are tabulated in `README.md`, section
"What is proved"; the commands to check them are in its section "How to verify".

## Corrections after an external review

A review of the first snapshot of this repository (commit `83b8cb0`, 3 October 2026) by another AI system, ChatGPT
(OpenAI), reported the errors below, and a follow-up review of the corrected snapshot (`12eb6a7`) the last two rows.
Each was checked before it was corrected, and each correction was read again before this release; nothing had been
published. No theorem statement, constant or Lean file changed.

| where | correction |
|---|---|
| ζ paper, §2 | the ramp is χ_w(t) = χ(t/w) for one fixed smooth χ: a general monotone ramp of width w does not give the derivative bound used |
| ζ paper, §3 | the proof of the two-parameter rank-trace inequality misidentified the difference of the two sides (the inequality is unchanged); the pinching lemma is stated for real symmetric G |
| ζ paper, §4 | the positive zeros of the kernel satisfy the tangent equation (the converse fails at x = α/2π); sinc 0 = 1 |
| ζ paper, §5 | the removal margins: the entry of a simple off-line pair is exactly 0, the others are at least 0.97 |
| ζ paper, §7 | M₃ = (1747823/7775424)π³ < 6.969843 (the printed 6.96984 was below it; the certifier used the exact value) |
| ζ paper, §8 | the bandwidth-one ceiling: what is proved (Alpöge and Furman §7.2, `Zeta23.PairCeiling.ceiling_law256` with its hypothesis `EnclOK`), not a bound for every such certificate |
| family paper, §2 | the density v in the scale-free variable, with the dictionary g(αℒ) = (aλ)²ℒψ(α); ‖v − v_p‖₁ = O(w/ℒ) instead of "they differ only on the ramp"; the range of the pointwise diagonal asymptotic |
| family paper, §4 | Lemma 4 at the design width K = ℒ(log ℒ)²; Lemma 5c(3) without its false clause for arbitrary W (unused); Lemma F1 with the support endpoint, as in Lean |
| family paper, §1, §7, bibliography | the descriptions of Sono's work and of Theorem 2 of Chandee, Lee, Liu and Radziwiłł, from the sources; the cited preprint [DSouza] identified by repository and commit; a sentence that the formal Frobenius row absorbs its eventual errors into the certificate's slack, so its intermediate rates are not checked in Lean |
| `supplementary/` | the CertS8 folder lacked two helper files (`localK.py`, `shard_ckpt.py`), now shipped; several scripts exited with status 0 after a failed, incomplete or empty run (the sharded S8 driver could report success with no shard checked), now nonzero; scalar multiprocessing with weights, whose workers ignored the weights, is refused; tested Python versions pinned; tests added |
| `supplementary/` (follow-up) | the sharded S8 loop re-sharded whatever checkpoint files were left, so lost shards vanished and a run could end with "ALL SHARDS OK" after losing its work; a run manifest now records the objective (with the sha256 of the weights and window files) and every shard of every round, and the drivers refuse missing, extra, changed or unexplained shards and a changed objective; checkpoints and logs carry the objective's sha256; the light K = 5/7 log checker checks alpha; the sharder checks without asserts; tests extended (63 negative and 21 positive controls) |
| both papers (follow-up) | Montgomery, Invent. Math. 8 (1969), pages 346 to 354; the weighting in the description of Chandee, Lee, Liu and Radziwiłł; the comparisons with earlier bounds and the first publication of the shared mechanism qualified as those we located; a short paragraph on the scope of the verification |

After the script corrections the three certificates were run again in full with the scripts of this release
(`supplementary/reruns-2026-10-03/`): `CertAM5` (20 of 20 classes), `CertAM7` (72 of 72 classes) and `CertS8` (the
sharded route with its run manifest, "ALL SHARDS OK", re-checked as COMPLETE) are certified, and the exact checkers
reproduce p and D; the results agree with the original logs, which are unchanged. The majorant check, the Python mirror
of the replay (46,047 leaves) and the regeneration of the 1,478 replay sources were repeated as well. The Lean kernel
replay of K = 5 (about 20 Lean-hours) was not repeated. Independently of the review, the papers no longer describe which
agent did what and when.

## Verification evidence

### A fresh build of the released Lean sources (3 October 2026, evening)

After the corrections, which changed no Lean file, the project's build products were deleted and every module of
`Zeta23`, `ZetaQ`, `ZetaS`, `ZetaSCertShims`, `ZetaShell` and the comparator files was compiled again from the sources
in this repository (Mathlib and the other dependencies from their official prebuilt cache; Lean `v4.33.0-rc2`, cloud
container, 4 CPUs, 15 GB). Files in `audit/followup/`:

| file | what | result |
|---|---|---|
| `build_fresh_2026-10-03_1924.log` | `lake build Zeta23 ZetaQ ZetaS ZetaSCertShims ZetaShell ChallengeDeps Challenge Solution Solution.FollowUpZeta Challenge.FollowUpFamily Solution.FollowUpFamily` | exit 0, 0 errors, 70 min; 53 `declaration uses 'sorry'` warnings, the same as in the build of the release commit below (open statements and trusted challenge statements) |
| `printaxioms_FollowUpZeta_2026-10-03_2035.out` | `lake env lean comparator/PrintAxioms/FollowUpZeta.lean` | fourteen lines, all `[propext, Classical.choice, Quot.sound]` |
| `printaxioms_FollowUpFamily_2026-10-03_2035.out` | `lake env lean comparator/PrintAxioms/FollowUpFamily.lean` | two lines, the same |
| `printaxioms_FollowUpShell_2026-10-03_2035.out` | `lake env lean comparator/PrintAxioms/FollowUpShell.lean` | two lines, the same |

The kernel replay `ZetaSReplay` (about 20 Lean-hours) was not rebuilt; its run is described under the evidence of
2 October below.

### The release commit (3 October 2026)

The Lean sources of the release are those of commit `4874cc0` on branch `release-v1`: the merge of `followup-trunk` at
`996b203` (the family library after the work of 3 October, which completes the proof of the family main theorem:
Lemma 2(a), Theorem S, Theorem K, the frame without `PNTErrorTerm`; and the comparator topic `FollowUpFamily`) into the
release branch at `b9f9c91` (the release as prepared on 2 October). The commits after `4874cc0` change no Lean file
and no build file (`git diff --stat 4874cc0 <release> -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain ':!audit/followup'`
is empty); they change `papers/`, `audit/followup/`, this file, `README.md`, `ZetaShell/README.md`, `papers/README.md`,
`NOTICE`, `CITATION.cff`, `.zenodo.json` and, after the external review, the scripts, documents and tests of
`supplementary/` (see "Corrections after an external review"; no certificate data, log or replay source changed). Between
`b9f9c91` and `4874cc0` no file of `ZetaS`, `ZetaSCertShims`, `Zeta23`, `ZetaQ`, `ZetaSReplay` or `supplementary/`
changed (`git diff --stat b9f9c91 4874cc0 -- ZetaS ZetaS.lean ZetaSCertShims Zeta23 ZetaQ ZetaSReplay supplementary` is
empty), so the evidence of 2 October below still holds for the Lean files and the certificate data, in particular the
kernel replay of the K = 5 certificate. The certificate logs in `supplementary/` are those of the original runs; the
reruns with the corrected scripts are listed in the corrections section. Evidence of 3 October, in `audit/followup/` (times are Australian Eastern Standard Time; machine: a cloud
container, 4 CPUs, 15 GB; Mathlib from its prebuilt cache; every module of `Zeta23`, `ZetaQ`, `ZetaS` and `ZetaShell`
was compiled from source by `lake` in that container on 2 and 3 October, the changed ones again in the build below):

| file | what | result |
|---|---|---|
| `build_release_2026-10-03_1519.log` | `lake build Zeta23 ZetaQ ZetaS ZetaSCertShims ZetaShell ChallengeDeps Challenge Solution Solution.FollowUpZeta Challenge.FollowUpFamily Solution.FollowUpFamily` at `4874cc0` | exit 0, 0 errors; the `declaration uses 'sorry'` warnings are those of the open statements listed below and of the trusted challenge statements |
| `printaxioms_FollowUpZeta_2026-10-03_1527.out` | `lake env lean comparator/PrintAxioms/FollowUpZeta.lean` | fourteen lines, all `[propext, Classical.choice, Quot.sound]` |
| `printaxioms_FollowUpFamily_2026-10-03_1527.out` | `lake env lean comparator/PrintAxioms/FollowUpFamily.lean` | two lines, the same |
| `printaxioms_FollowUpShell_2026-10-03_1527.out` | `lake env lean comparator/PrintAxioms/FollowUpShell.lean` | two lines, the same |
| `census_2026-10-03_1557.tsv`, `census_2026-10-03_1557.out` | census of every public theorem of `ZetaS`, `ZetaSCertShims` and `ZetaShell` at `4874cc0` (`Census_release.lean`, extended by the statement of record, the nodes of 3 October and the parts of the main theorem that the family paper quotes) | 3,680 public theorems, 3,632 at the three standard axioms; no definition uses `sorry`; `ZetaShell.shell_S53_qle_reduced` has no open leaf |

The two family statements (`printaxioms_FollowUpFamily_2026-10-03_1527.out`, verbatim):

```
'family_simple_on_line_killed' depends on axioms: [propext, Classical.choice, Quot.sound]
'family_simple_on_line_shell' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The statement of record and the nodes completed on 3 October in the census of `4874cc0`
(`census_2026-10-03_1557.out`, the lines concerned, verbatim):

```
'ZetaShell.Design.shell_frame_qle_of_K_noP' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.ShellK.K2_shellZone' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.ShellS.AS_pointwise_corr' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.ShellS.S2_zero_side' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.TrackF.ring_le_primitive_corr' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.shell_S53_qle_reduced' depends on axioms: [propext, Classical.choice, Quot.sound]
SORRY-LEAVES ZetaShell.Design.shell_frame_qle_of_K (0): []
SORRY-LEAVES ZetaShell.Design.shell_frame_qle_of_K_noP (0): []
SORRY-LEAVES ZetaShell.ShellK.F1c.K3b_integrated (0): []
SORRY-LEAVES ZetaShell.ShellK.K2_shellZone (0): []
SORRY-LEAVES ZetaShell.ShellK.thmK (0): []
SORRY-LEAVES ZetaShell.ShellS.AS_pointwise_corr (0): []
SORRY-LEAVES ZetaShell.ShellS.S1_ring_to_zeros (0): []
SORRY-LEAVES ZetaShell.ShellS.S2_zero_side (0): []
SORRY-LEAVES ZetaShell.ShellS.Z6a_zero_sums (0): []
SORRY-LEAVES ZetaShell.ShellS.Z6d_counts_corr (0): []
SORRY-LEAVES ZetaShell.ShellS.shell_S (0): []
SORRY-LEAVES ZetaShell.TrackF.lemma2a (0): []
SORRY-LEAVES ZetaShell.TrackF.ring_le_primitive_corr (0): []
SORRY-LEAVES ZetaShell.shell_S53_qle_reduced (0): []
```

Two internal statements were corrected on 3 October; each correction adds one hypothesis, the first form stays in the
library, open and used by no proof, and no headline statement changed: Lemma 6d (`Z6d_counts` → `Z6d_counts_corr`, the
near clause under 5·X₀ ≤ s₀, as the paper proves it) and the pointwise assembly (`AS_pointwise` → `AS_pointwise_corr`,
under α″ < λ). The transfer node `KT_transfer` is proved too but is not used by the proof of the main theorem.

### Evidence of 2 October 2026 (the release preparation)

On 2 October the Lean sources of the release were those of commit `dcd371e` on branch `release-v1`: the merge of `followup-trunk` at
`1d7f91a` (the family library after the integration shift of 1 October) into the release branch at `2b810aa` (the
tree after the release preparation). Up to `b9f9c91` the commits after `dcd371e` changed only `papers/`, `audit/followup/`, this
file and, for the repository's name and tag, `README.md`, `CITATION.cff`, `.zenodo.json` and `.gitattributes`:
`git diff --stat dcd371e b9f9c91 -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain ':!audit/followup'` is
empty, so no library file, no comparator Lean file and no lakefile entry changed after it until the merge of 3 October. Logs and censuses are in `audit/followup/`
(times are Australian Eastern Standard Time; machine: 24 cores,
32 GB; three Lean processes in parallel; the upstream build products of `Zeta23` and `ZetaQ` were reused, everything
of the follow-up libraries was built from source by `lake` in this tree):

| file | what | result |
|---|---|---|
| `build_libs_2026-10-01_2324.log` | `lake build ZetaS ZetaShell ZetaSCertShims ChallengeDeps Challenge Solution` at `dcd371e`, from an empty `.lake/build` for these libraries (every follow-up module compiled from source) | exit 0, 0 errors, 496 modules built, 38 min wall (23:25 to 00:03); 62 `declaration uses 'sorry'` warnings (the open statements of the section below) |
| `build_solution_2026-10-02_0002.log` | `lake build Solution.FollowUpZeta` (the `Solution` root does not import this module, so it is built by name) | exit 0 |
| `printaxioms_FollowUpZeta_2026-10-02_0003.out` | `lake env lean comparator/PrintAxioms/FollowUpZeta.lean` at `dcd371e`, after that build | fourteen lines, all `[propext, Classical.choice, Quot.sound]` |
| `printaxioms_FollowUpShell_2026-10-02_0003.out` | `lake env lean comparator/PrintAxioms/FollowUpShell.lean` | two lines, the same |
| `census_2026-10-02_0003.tsv`, `census_2026-10-02_0003.out` | census of every public theorem of `ZetaS`, `ZetaSCertShims` and `ZetaShell` at `dcd371e` after that build (`Census_release.lean`: module, name, level, axioms, number and list of `sorry` leaves) | 3,268 theorems: 3,196 at the three standard axioms, 72 depending on `sorryAx`, none on any other axiom |
| `build_libs_2026-10-01_2135.log`, `build_libs_2026-10-01_2301.log`, `census_2026-10-01_2216.*`, `census_2026-10-01_2315.*`, `printaxioms_*_2026-10-01_*.out` | the earlier runs of the same checks: a from-scratch build at `2b810aa` (before the merge of the family library's last shift) and the incremental rebuild at `dcd371e` | the same results; the census of `dcd371e` before and after the from-scratch build is identical row for row |
| `build_replay_2026-10-01_2222.log`, `build_replay_2026-10-01_2318.log`, `build_replay_2026-10-02_0006.log`, `build_replay_2026-10-02_0108.log` | `lake build ZetaSReplay`: started 22:22 on 1 October at three threads, paused for the library builds above (23:01, 23:24) and once more to go to four threads (01:08); lake keeps the shards built between runs | exit 0 at 03:52:14 on 2 October, 0 errors, 0 `sorry` warnings; all 1,478 modules built (81 + 11 + 164 + 1,222 across the four logs); the last run took 2 h 43 min at four threads, about 4 h 40 min of build time in all; `lake build ZetaSReplay --no-build` afterwards: "All targets up-to-date (10466 jobs)" |
| `printaxioms_FollowUpReplay_2026-10-02_0352.out` (and `…FollowUpZeta…`, `…FollowUpShell…` of the same time, re-run) | `lake env lean comparator/PrintAxioms/FollowUpReplay.lean` after the replay build | three lines, all `[propext, Classical.choice, Quot.sound]`: `ZetaS.Top.zeta_simple_K5_uncond`, `ZetaS.Top.zeta_distinct_K5_uncond`, `ZetaS.CertV2.certAM5_replayed` |

The fourteen comparator statements of the ζ paper (`printaxioms_FollowUpZeta_2026-10-02_0003.out`, verbatim):

```
'zeta_simple_K5' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_simple_K5_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_distinct_K5' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_distinct_K5_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_simple_K7' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_simple_K7_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_distinct_K7' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_distinct_K7_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_simple_on_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_simple_on_line_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_simple_or_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_simple_or_critical_cumulative' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_zerosIn_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'zeta_tendsto_Ncount' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The family headlines (`printaxioms_FollowUpShell_2026-10-02_0003.out`, verbatim):

```
'ZetaShell.LemmaK.theorem_one_prime_design' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.certS53' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The headline declarations in the census of `dcd371e` (`census_2026-10-02_0003.out`, verbatim; `SORRY-LEAVES x (n)`
lists the n declarations in the dependency closure of `x`, outside Mathlib and `Zeta23`, whose own statement or proof
uses `sorry`):

```
SORRY-LEAVES ZetaS.Top.zeta_simple_K5_final (0): []
SORRY-LEAVES ZetaS.Top.zeta_distinct_K5_final (0): []
SORRY-LEAVES ZetaS.Top.zeta_simple_K7_final (0): []
SORRY-LEAVES ZetaS.Top.zeta_distinct_K7_final (0): []
SORRY-LEAVES ZetaS.Top.zeta_simple_on_line (0): []
SORRY-LEAVES ZetaS.Top.zeta_simple_or_critical (0): []
'ZetaS.Top.zeta_simple_K5_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaS.Top.zeta_distinct_K5_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaS.Top.zeta_simple_K7_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaS.Top.zeta_distinct_K7_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaS.Top.zeta_simple_on_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaS.Top.zeta_simple_or_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
SORRY-LEAVES ZetaShell.LemmaK.theorem_one_prime_design (0): []
SORRY-LEAVES ZetaShell.certS53 (0): []
SORRY-LEAVES ZetaShell.certD53 (0): []
SORRY-LEAVES ZetaShell.PropZ.propZ_W (0): []
SORRY-LEAVES ZetaShell.TrackF.lemma2a (3): [ZetaShell.TrackF.line_sum_asymp [ZetaShell.Skeleton.A2P_LineProfile], ZetaShell.TrackF.s3_tail_plain_pt [ZetaShell.Skeleton.A2a_S3e_TailParts], ZetaShell.TrackF.s3_tail_sum [ZetaShell.Skeleton.A2a_S3e_TailParts]]
SORRY-LEAVES ZetaShell.Design.shell_frame_qle_of_nodes (1): [ZetaShell.Design.frob_row_shell [ZetaShell.Skeleton.SD_F1c_FrobRow]]
SORRY-LEAVES ZetaShell.LemmaK.theorem_one_prime (1): [ZetaShell.LemmaK.killed_frame_lamStar8 [ZetaShell.Skeleton.LK_K9_Frame]]
SORRY-LEAVES ZetaShell.PropZ.Z5R_W (0): []
SORRY-LEAVES ZetaShell.ShellK.F1c_chain (0): []
SORRY-LEAVES ZetaShell.Design.shell_frame_qle_of_K (2): [ZetaShell.ShellK.K2_shellZone [ZetaShell.Skeleton.L10_K2_ShellZone], ZetaShell.ShellK.F1c.K3b_integrated [ZetaShell.Skeleton.LF_K3Split]]
SORRY-LEAVES ZetaShell.ShellK.frob_row_shell' (2): [ZetaShell.ShellK.K2_shellZone [ZetaShell.Skeleton.L10_K2_ShellZone], ZetaShell.ShellK.F1c.K3b_integrated [ZetaShell.Skeleton.LF_K3Split]]
SORRY-LEAVES ZetaShell.ShellS.shell_S (2): [ZetaShell.ShellS.S2_zero_side [ZetaShell.Skeleton.L10_S2], ZetaShell.ShellS.S1_ring_to_zeros [ZetaShell.Skeleton.L10_S1]]
SORRY-LEAVES ZetaShell.ShellK.thmK (2): [ZetaShell.ShellK.K2_shellZone [ZetaShell.Skeleton.L10_K2_ShellZone], ZetaShell.ShellK.F1c.K3b_integrated [ZetaShell.Skeleton.LF_K3Split]]
'ZetaShell.LemmaK.theorem_one_prime_design' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.certS53' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.certD53' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.PropZ.propZ_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.TrackF.lemma2a' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'ZetaShell.ShellK.F1c_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaShell.Design.shell_frame_qle_of_K' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'ZetaShell.ShellS.shell_S' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'ZetaShell.ShellK.thmK' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Checks made on 1 October 2026, before the clean build:

- `ZetaSReplay/MANIFEST.sha256`: 1,478 of 1,478 files match;
- regeneration of the 1,478 replay files from `supplementary/replay-K5/`: 1,478 of 1,478 byte-identical;
- `supplementary/CHECKSUMS.sha256`: every file matches; the seven sha256 values printed in the ζ paper and in
  `comparator/ChallengeDeps/FollowUpZeta.lean`: seven of seven match;
- the exact-rational side conditions of `CertAM5` and `CertAM7` (`supplementary/VERIFY.md`, step 2): 20 of 20 and
  72 of 72 classes, both checks pass;
- `comparator/PrintAxioms/FollowUpReplay.lean` and `FollowUpShell.lean`: outputs in `audit/followup/` (the three
  standard axioms on all five lines).

## What is not claimed

- The zero-density estimates are not proved: the main theorem of the family paper (0.9059137927) is a Lean theorem under
  one displayed hypothesis, `ZeroDensityInput`, which states the estimates (J) of Jutila and (M) of Montgomery as
  quoted in the paper; the theorem assumes them.
- The constant for the dyadic family (Q/2 < q ≤ Q) and the bounded-height forms of the main theorem are not claimed;
  their statements of record are open. Of the dyadic case only the certificate exists in Lean (`ZetaShell.certD53`).
- `CertAM7` and `CertS8` are hypotheses: finite numerical inequalities checked outside Lean by interval arithmetic and
  displayed in the statements of the theorems that use them. In the fourteen comparator statements `CertAM5` is a
  displayed hypothesis too; its kernel proof is in `ZetaSReplay`, outside the comparator topic.
- The value 0.6733736895 (simple zeros on the critical line) is not a record: six larger public values exist.
- `ZetaShell.LemmaK.theorem_one_prime` (0.7237) is in the library but rests on an open statement
  (`killed_frame_lamStar8`); only the 0.7235 form `theorem_one_prime_design` is claimed.
- Nothing in this release claims priority or novelty over other work.

## Open statements in the libraries

The theorems named in `README.md` use no `sorry`. The libraries as a whole contain open statements (closed by `sorry`),
which `lake build` reports as `declaration uses 'sorry'`:

- `ZetaQ`: four, described in the `ZetaQ` section of `README.md`; no headline theorem uses them.
- `ZetaS`: one module, `ZetaS/Skeleton/A8g_SigmaDistGeneral.lean` (three statements: the general-K forms A7g and A8g);
  no named theorem uses them.
- `ZetaShell`: the modules under `ZetaShell/Skeleton/` other than the four proved in place on 3 October (`L10_S1`,
  `Astar_Corr`, `A2P_LineProfile`, `A2a_S3e_TailParts`), the statement files `ZetaShell/Challenge.lean` and
  `ZetaShell/Interfaces.lean` (the original headline statements, kept unchanged), and the three statements of record
  in `ZetaShell/Top/HeadlineReduced.lean` that are not claimed (the dyadic and the two bounded-height forms). At
  `4874cc0` the census counts 1,744 public theorems in `ZetaShell`, 1,708 of them at the three standard axioms and 36
  resting on `sorry` (29 open statements and 7 derived from them); no definition uses `sorry`, and none of the 36 is
  used by a theorem named in `README.md`. In `ZetaS` and `ZetaSCertShims` the census counted 1,936 public theorems, 1,924 at the three standard
  axioms and 12 resting on `sorry`, all of them derived from the open statements of the module named above (the
  general-K forms A7g and A8g); none of the theorems named in `README.md` is among them. The 12:
  `ZetaS.A8K.a7g_holds`, `ZetaS.OLL_gen`, `ZetaS.Top.a8g_dist_holds`, `ZetaS.Top.a8g_simple_holds`, `ZetaS.Top.zeta_distinct_K5_of_majorant`, `ZetaS.Top.zeta_distinct_K7_of_majorant`, `ZetaS.Top.zeta_simple_K5_of_majorant`, `ZetaS.Top.zeta_simple_K7_of_majorant`, `ZetaS.dist_abstract_gen`, `ZetaS.dist_abstract_of_gen`, `ZetaS.sigma_abstract_gen`, `ZetaS.sigma_abstract_of_gen`.

## Status of the family formalisation

The statement of record of the main theorem is `ZetaShell.shell_S53_qle_reduced` (`ZetaShell/Top/HeadlineReduced.lean`):
for the family q ≤ Q, at height T = (log Q)^{r+ε} with r ≥ 3, under the hypothesis `ZeroDensityInput` and for
0 < θ < 503/1994, a proportion at least 0.9059137927 − c·(log Q)^{−θ} of the family's zeros with T < γ ≤ 2T are simple
and on the critical line. At `4874cc0` it is a Lean theorem: three standard axioms, no open leaf.

| part | Lean declaration | open leaves at `dcd371e` (2 Oct) | at `4874cc0` (3 Oct) |
|---|---|---|---|
| the main theorem | `ZetaShell.shell_S53_qle_reduced` | its own `sorry` | **none** |
| the frame without `PNTErrorTerm` | `ZetaShell.Design.shell_frame_qle_of_K_noP` | (not stated) | **none** |
| the frame with `PNTErrorTerm` and the certificate as hypotheses | `ZetaShell.Design.shell_frame_qle_of_K` | two | **none** |
| Theorem K | `ZetaShell.ShellK.thmK` | two: `K2_shellZone`, `K3b_integrated` | **none** |
| Theorem S | `ZetaShell.ShellS.shell_S` | two: `S1_ring_to_zeros`, `S2_zero_side` | **none** |
| Lemma 2(a) | `ZetaShell.TrackF.lemma2a` | three | **none** |
| A⋆, the corrected primitive reduction | `ZetaShell.TrackF.ring_le_primitive_corr` | open | **none** |
| the pointwise assembly | `ZetaShell.ShellS.AS_pointwise_corr` (corrected form) | open (first form) | **none** |
| Proposition Z, the Frobenius row, the certificate | `PropZ.propZ_W`, `ShellK.F1c_chain`, `certS53` | none | none |

The route of the proof: the counts of the statement are those of `ZetaQ` (node B1, by `rfl`); ZetaQ's Proposition 3.1
turns a frame into the headline (node F2); the frame at λ = 191/100 is derived from Theorem K, the Frobenius-row chain
and the rows of the design layer, without the strong prime number theorem `PNTErrorTerm`, which no proved declaration
uses (the medium prime number theorem, a theorem of the tree, enters below Theorem K); the Shell-zone part of Theorem K
is derived from the pointwise assembly and Theorem S; Theorem S from its steps S1 (through A⋆, with the Gauss sums of
imprimitive characters, which Mathlib lacks, in `ZetaShell/Farey/Astar_Gauss.lean`), S2 (Lemmas 6a and 6d), S3 and S4.
The original headline statements of `ZetaShell/Challenge.lean`, with `PNTErrorTerm` and the certificate as hypotheses,
follow from the reduced ones by proved implications.

Statements found false, or not derivable from the inputs as stated, by formalising them: twelve in September (eight on
the ζ side, four on the family side: the far part of Lemma 1′, the first form of K2, the first form of Lemma 2(a), and
A⋆), and on 3 October the first forms of Lemma 6d's near clause and of the pointwise assembly. Each was replaced by a
corrected statement under a new name, and the first form was frozen or kept open and unused; no headline statement
changed. The dyadic family's constant and the bounded-height forms are not claimed; their statements of record are open
in `ZetaShell/Top/HeadlineReduced.lean`.
