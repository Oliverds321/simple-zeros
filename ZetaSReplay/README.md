# ZetaSReplay: the kernel replay of the K = 5 certificate

This library turns the finite numerical certificate `ZetaS.CertAM5` (the all-marks local inequality for K = 5,
defined in `ZetaS/Top/TopDefs.lean` and stated for comparator in `comparator/ChallengeDeps/FollowUpZeta.lean`) from a
displayed hypothesis into a theorem checked by the Lean kernel. With it, the two K = 5 theorems of the ζ paper hold
with no hypothesis at all.

## What is in this folder

| file(s) | what it is |
|---|---|
| `R<class>_Data.lean` | the instance of the local inequality for one reversal class of mark patterns (20 classes, `11111` to `22222`) |
| `R<class>_Pts<k>.lean`, `R<class>_Cells.lean` | exact-rational enclosures of the kernel and its derivatives at the points and on the cells the certificate uses |
| `R<class>_Leaves<k>.lean` | the leaves of the class's bisection tree, each checked by `decide +kernel` |
| `R<class>_Assembly.lean` | the inner nodes of the tree, up to `T0_ok : Node.check D_R<class> T0 root = true` |
| `R<class>_Cert.lean` | the class certificate, `cert_ok : Cert.check cert = true`, and `holds` through the soundness chain |
| `ReplayCommon.lean` | three small lemmas shared by the 20 class files |
| `ReplayAM5.lean` | `ZetaS.CertV2.certAM5_replayed : ZetaS.CertAM5`, from the 20 class certificates and `ZetaS.CertV2.ChainV3.certAM5_of_checks` (module `ZetaS.Cert.ChainV3`) |
| `ReplayHeadlines.lean` | the two hypothesis-free theorems (below) |
| `MANIFEST.sha256` | one sha256 per `.lean` file of this folder (1,478 lines) |
| `MANIFEST.orig.sha256` | the same hashes as recorded at generation, with the generator's paths (`./<class>/…`, `./common/…`) |

1,478 modules in all: 1,475 class files (between 56 and 89 per class) and the three common files. The module names
are bare (`R11111_Data`, `ReplayAM5`, …), because the generated files import each other by these names; the shards
also import the frozen checker through the bare-name forwarders of `ZetaSCertShims/` (`CheckerCoreV3`). The library's
`lakefile.toml` entry therefore lists every module in `globs`.

The files are mechanically generated and stored byte for byte (`.gitattributes`: no line-ending conversion; the files
have CRLF line endings). Check them with

```bash
cd ZetaSReplay && sha256sum -c MANIFEST.sha256      # 1,478 lines, each ending in OK
```

## How the files are generated

From the certificate data in `supplementary/replay-K5/` (one JSON file `v2_K5_<class>.json` per class, in the format
of the checker v3), by `supplementary/replay-K5/gen_replay.py`, which calls `gen_v2_lean.py` for each class and then
writes the `R<class>_Cert.lean` files and the three common files. Regeneration takes about two minutes with Python 3,
`numpy` and `scipy`; the commands are in `supplementary/VERIFY.md`. The output is written to class folders
`supplementary/replay-K5/<class>/` and `supplementary/replay-K5/common/`, and `supplementary/replay-K5/MANIFEST.sha256`
(identical to `MANIFEST.orig.sha256` here) checks it. On 1 October 2026 a regeneration on Windows reproduced all 1,478
files byte for byte. On Linux or macOS the generator writes LF line endings; convert them to CRLF before comparing
hashes (the command is in `supplementary/VERIFY.md`).

## How to build

```bash
lake build ZetaSReplay                                    # about 20 Lean-hours of CPU time, about 7 GB of build products
lake env lean comparator/PrintAxioms/FollowUpReplay.lean  # #print axioms on the three declarations below
```

The library is not in `defaultTargets`. Expected output of the second command: three lines, each ending
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

## The two theorems (verbatim from `ReplayHeadlines.lean`)

```lean
/-- **Simple zeros, K = 5, hypothesis-free** (thm:sigd-Sigma with the K = 5 certificate). -/
theorem zeta_simple_K5_uncond :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  zeta_simple_K5_final ZetaS.CertV2.certAM5_replayed

/-- **Distinct zeros, K = 5, hypothesis-free** (thm:sigd-D with the K = 5 certificate). -/
theorem zeta_distinct_K5_uncond :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  zeta_distinct_K5_final ZetaS.CertV2.certAM5_replayed
```

Both are in namespace `ZetaS.Top`. `Ncount`, `Nsimple` and `Ndist` are the counting functions of the upstream library
(`Zeta23/Statement.lean`: zeros of Mathlib's `riemannZeta` with 0 < Re ρ < 1 and T < Im ρ ≤ 2T, counted with multiplicity,
simple, distinct). In words: at least 0.675158622 of the zeros with T < γ ≤ 2T are simple, and at least 0.837579311
are distinct, as T → ∞. `zeta_simple_K5_final` and `zeta_distinct_K5_final` (`ZetaS/Top/TopFinal.lean`) are the same
statements with the hypothesis `CertAM5`.

## The run of 28 September 2026

The replay was run module by module (with `lean`, through the project's own job runner, not through `lake`) against
commit bb7223b. The `ZetaS/` and `ZetaSCertShims/` of this release differ from bb7223b's only in two doc-strings of
`ZetaS/ChallengeZetaS.lean` (no declaration changed).

- 1,478 of 1,478 files checked, no failure;
- 2 h 50 min wall time (10,207 s), 20.4 Lean-hours of CPU time (73,529 s);
- census afterwards (`#print axioms`, and a scan of the proof terms for declarations that use `sorry`), verbatim:

```
SORRY-LEAVES ZetaS.Top.zeta_simple_K5_uncond (0): []
SORRY-LEAVES ZetaS.Top.zeta_distinct_K5_uncond (0): []
SORRY-LEAVES ZetaS.CertV2.certAM5_replayed (0): []
'ZetaS.Top.zeta_simple_K5_uncond' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaS.Top.zeta_distinct_K5_uncond' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaS.CertV2.certAM5_replayed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No open leaf: none of the three declarations rests on a `sorry`. The census of the release commit, from a clean build
of this library, is in `audit/followup/`.

## What the replay relies on

The kernel checks every leaf with `decide +kernel` (kernel reduction; no `native_decide`, no extra axiom). Soundness of
the checker, that is, that `Cert.check C = true` implies the local inequality on the whole orthant, is the theorem
`ZetaS.CertV2.ChainV3.cert_check_sound` (module `ZetaS.Cert.ChainV3`), and `certAM5_of_checks` applies it to the 20 classes;
both use only the three standard axioms. The checker modules `ZetaS/Cert/CheckerBase.lean`, `CheckerLeaves.lean`,
`CheckerCoreV3.lean` are frozen and stored byte for byte; a change to any file under `ZetaS/Cert/` would make a
previous build of this library stale.
