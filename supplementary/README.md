# Supplementary data of the ζ paper

This folder holds the numerical supplementary material of the ζ paper (`papers/zeta/`): the finite certificates that
the paper's theorems use, the scripts that checked them, and the logs of those checks. The Lean side lives in the same
repository: the library `ZetaS/`, the comparator statements `comparator/*/FollowUpZeta.lean`, and the K = 5 kernel
replay `ZetaSReplay/`. How to check everything, in order: `VERIFY.md`.

## What is in this folder

Three finite numerical inequalities ("certificates") are displayed hypotheses of the paper's Lean theorems; one of
them, `CertAM5`, is also proved in the Lean kernel by the replay library `ZetaSReplay/`. A fourth certificate, the
majorant, is a theorem of the library `ZetaS` (614 cells replayed by the kernel). For each one, this folder has the
exact-rational data, the certifier script that checked it, and the log of that check.

| folder | certificate | data | certifier | log(s) |
|---|---|---|---|---|
| `certificates/CertS8/` | `CertS8`: the local inequality (LI') for the polynomial window, K = 8, hypothesis of the theorems on zeros that are simple and on the critical line, and simple or on the line | `w_poly8A_K8_mu1700.json` (weights), `win_poly8A.json` (window) | `bnb_lb3.py` (needs `polywin.py` and `localK.py` alongside it); the sharded route of the logs also `shard_ckpt.py`, `mkinit.sh`, `round_lb3.sh`, `run_lb3_loop.sh`, and since 3 October 2026 `s8_manifest.py` (the run manifest) | `logs/DRIVER_P8.log`, `logs/DRIVER_P8b.log` (independent re-run) |
| `certificates/CertAM5/` | `CertAM5`: the all-marks local inequality (LI_m) for K = 5, hypothesis of the K = 5 theorems on simple and distinct zeros, and proved in the kernel by `ZetaSReplay/` | `claims_d15e6_a1.6_K5_mu500.json` plus the 20 `xpat_K5_*.json` reversal-class files | `bnb_interval_w.py` (needs `localK.py` alongside it) | `logs/cert_K5_w_a16_mu500_d15e6.txt`, `..._b.txt` |
| `certificates/CertAM7/` | `CertAM7`: the same inequality for K = 7, hypothesis of the K = 7 theorems | `claims_a1.6_K7_mu500_L1e5.json` plus the 72 `xpat_K7_*.json` reversal-class files (the complete, passing run) | `bnb_lb3_w.py` (needs `localK.py` alongside it); `pexact2.py` is a standalone completeness check that imports `bnb_lb3_w.py` | `logs/cert_lb3_rerun.txt` (72/72 classes), `logs/k7_verify_pexact2.txt` (completeness) |
| `certificates/CertMajV2/` | the majorant of the lemma "separated sites have room"; in the Lean library a proved theorem, not a hypothesis | `majorant_delta1_beta.npy` (60 float64 coefficients) | `r4_majorant_arb.py` (Arb interval arithmetic, 106 bits) | none; the script prints its own pass or fail |
| `certificates/common/` | exact-rational checkers of the side conditions (weights nonnegative, spans sum to 2, claims equal the stated sums, every pattern covered) for the all-marks certificates | — | `verify_inputs.py`, `d819_exact.py` | — |
| `replay-K5/` | the source of the K = 5 kernel replay: the certificate JSON in the format of the checker v3 (`v2_K5_<class>.json`, one per reversal class, and `v2common_K5_4.json`), the generator that writes the Lean shards (`gen_replay.py`, which calls `gen_v2_lean.py`; both import `proto_v2.py` and `proto_cert.py`), a Python mirror of the checker (`replay_v3.py`), and `MANIFEST.sha256` (one sha256 per generated file) | `v2_K5_*.json` (20 files), `v2common_K5_4.json` | the Lean kernel, through `ZetaSReplay/` | `ZetaSReplay/README.md` (the run of 28 September 2026) |
| `replay-K5/drivers/` | the job drivers of the run of 28 September 2026 (`run_replay.sh`; `run_pools.sh` with `run_pools.py`, a memory-aware two-pool variant), kept for provenance | — | — | — |
| `reruns-2026-10-03/` | full reruns of `CertAM5`, `CertAM7` and `CertS8` with the corrected scripts of this release (3 October 2026, Linux): all certified, in agreement with the original logs (`reruns-2026-10-03/README.md`) | | | the rerun logs, the checker outputs and the complete S8 run folder with its run manifest |

The 1,478 Lean files that `gen_replay.py` writes are in `ZetaSReplay/`, byte for byte, with the same hashes as
`replay-K5/MANIFEST.sha256`. Regenerating them (about two minutes, Python only) is optional; `VERIFY.md` step 6 shows
how, and how to check the result against the manifest.

## The printed sha256 values

The paper (Table 3) and the doc-strings of `comparator/ChallengeDeps/FollowUpZeta.lean` identify each certificate's data
by its sha256. All seven printed values match the files here:

| certificate | file(s) | sha256 |
|---|---|---|
| `CertS8` | `certificates/CertS8/w_poly8A_K8_mu1700.json` | `257b340d9da4f343600a21589f16d8915f3e082499d475e153c5453980671e78` |
| `CertS8` (window) | `certificates/CertS8/win_poly8A.json` | `c4005f57a7920f78aa2df33b093c9c5030efac2b8e39fc6cf7371b0c0f32dc14` |
| `CertAM5` | `certificates/CertAM5/claims_d15e6_a1.6_K5_mu500.json` (printed elsewhere under its original name `claims_a1.6_K5_mu500.json`; the bytes are the same) | `cf055dd2ee9a9e469b6510fe70b5fbc416b8a40515cc6746bc390d40d88777f2` |
| `CertAM5` | the 20 `certificates/CertAM5/xpat_K5_*.json`, concatenated in sorted file-name order | `a5947c01d34ddcbc7366861b35e83942099fcbf7ac71e13fcd432796882dd34e` |
| `CertAM7` | `certificates/CertAM7/claims_a1.6_K7_mu500_L1e5.json` | `d2cf393019407bdc797c73147ec8e3dc66ec41fe745600c84173f74ac66bfc5c` |
| `CertAM7` | the 72 `certificates/CertAM7/xpat_K7_*.json`, concatenated in sorted file-name order | `33c4c8c5762bcebdf8f544ab34a137a6a7ba4065d08f5caee0a51188e1a67514` |
| `CertMajV2` | `certificates/CertMajV2/majorant_delta1_beta.npy` | `fd909f79669e2fc1ba5fd4e44d01d6007ccf5303b7ce62d4c5ee08f7ef024845` |

`CHECKSUMS.sha256` gives the hash of every file in this folder. The folder is stored without line-ending conversion
(`.gitattributes`), so these hashes hold in every checkout. A few scripts were edited for portability when the folder
was assembled, and on 3 October 2026, after an audit, for their exit status and failure checks; three missing helper
files were added to `certificates/CertS8/`. Later the same day, after a review of the corrected release, the sharded
CertS8 route got a run manifest (`certificates/CertS8/s8_manifest.py`, new) that binds coverage and inputs, and a few
scripts got further checks. The certificate data (`.json`, `.npy`) and the logs were not changed. `CHANGES.txt` lists
every edit.

## Map from the development's paths

The doc-strings of `comparator/ChallengeDeps/FollowUpZeta.lean` and `ZetaS/ChallengeZetaS.lean`, and Table 3 of the ζ
paper, name the files by their paths in the development's project folder. This table gives, for each of them, its
place in this folder. Every pair was compared by sha256 on 1 October 2026: "same" means byte-identical; "edited" means
changed for portability (1 October 2026) or for exit status and failure checks (3 October 2026), with the change
listed in `CHANGES.txt`. The three files added to `certificates/CertS8/` on 3 October 2026 were compared by sha256 with
the copies of the working folder of the recorded runs (two of them were edited afterwards, the same day). Also new on
3 October 2026, with no development path: `requirements.txt`, the regression tests `tests/run_negative_controls.sh`,
`tests/run_positive_smoke.sh`, and `certificates/CertS8/s8_manifest.py`.

| development path | here | |
|---|---|---|
| `round2/d6_5_numerics/w_poly8A_K8_mu1700.json` | `certificates/CertS8/w_poly8A_K8_mu1700.json` | same |
| `round2/d6_5_numerics/win_poly8A.json` | `certificates/CertS8/win_poly8A.json` | same |
| `round2/d6_5_numerics/bnb_lb3.py` | `certificates/CertS8/bnb_lb3.py` | edited (exit status; scalar multiprocessing guard; objective identity in checkpoints and logs) |
| `round2/d6_5_numerics/polywin.py` | `certificates/CertS8/polywin.py` | same |
| `round2/d6_5_numerics/mkinit.sh`, `round_lb3.sh` | `certificates/CertS8/` (same names) | edited (failure checks, exit status; run manifest) |
| `round2/d6_5_numerics/localK.py` | `certificates/CertS8/localK.py` | same (added 3 October 2026) |
| `round2/d6_5_numerics/shard_ckpt.py`, `run_lb3_loop.sh` | `certificates/CertS8/` (same names) | added 3 October 2026, then edited (explicit checks, objective identity; run manifest) |
| `round2/d6_5_numerics/runs/P8/DRIVER.log` | `certificates/CertS8/logs/DRIVER_P8.log` | same |
| `round2/d6_5_numerics/runs/P8b/DRIVER.log` | `certificates/CertS8/logs/DRIVER_P8b.log` | same |
| `round1/X2_numerics/claims_a1.6_K5_mu500.json` (also `claims_d15e6_a1.6_K5_mu500.json` there) | `certificates/CertAM5/claims_d15e6_a1.6_K5_mu500.json` | same |
| `round1/X2_numerics/xpat_K5_*.json` (20 files) | `certificates/CertAM5/xpat_K5_*.json` | same, 20 of 20 |
| `round1/X2_numerics/bnb_interval_w.py` | `certificates/CertAM5/bnb_interval_w.py` | edited (exit status; scalar multiprocessing guard) |
| `round1/X2_numerics/localK.py` | `certificates/CertAM5/localK.py` | same |
| `round1/X2_numerics/runcert.sh` | `certificates/CertAM5/runcert.sh` | edited (failure checks, exit status) |
| `round1/X2_numerics/cert_K5_w_a16_mu500_d15e6.txt`, `cert_K5_w_a16_mu500_d15e6_b.txt` | `certificates/CertAM5/logs/` (same names) | same |
| `round2/d8_9_numerics/k7m500/rerun/claims_a1.6_K7_mu500_L1e5.json` (the copy in `k7m500/d5/` is identical) | `certificates/CertAM7/claims_a1.6_K7_mu500_L1e5.json` | same |
| `round2/d8_9_numerics/k7m500/rerun/xpat_K7_*.json` (72 files; those in `k7m500/d5/` are identical) | `certificates/CertAM7/xpat_K7_*.json` | same, 72 of 72 |
| `round2/d8_9_numerics/bnb_lb3_w.py` | `certificates/CertAM7/bnb_lb3_w.py` | edited (exit status; scalar multiprocessing guard) |
| `round2/d8_9_numerics/localK.py` | `certificates/CertAM7/localK.py` | same |
| `round2/d8_9_numerics/runlb3.sh` | `certificates/CertAM7/runlb3.sh` | edited (failure checks, exit status) |
| `round2/d8_9_numerics/pexact2.py` | `certificates/CertAM7/pexact2.py` | edited (exit status) |
| `round2/d8_9_numerics/k7m500/rerun/cert_lb3_rerun.txt` | `certificates/CertAM7/logs/cert_lb3_rerun.txt` | same |
| `round2/d8_21_numerics/k7_verify_pexact2.txt` | `certificates/CertAM7/logs/k7_verify_pexact2.txt` | same |
| `round2/d6_6b_numerics/majorant_delta1_beta.npy` | `certificates/CertMajV2/majorant_delta1_beta.npy` | same |
| `round2/d7_6_numerics/r4_majorant_arb.py` | `certificates/CertMajV2/r4_majorant_arb.py` | edited (input path; exit status; report of a failed check) |
| `round2/d8_9_numerics/verify_inputs.py` | `certificates/common/verify_inputs.py` | edited (exit status; alpha and weight-check pattern checked) |
| `round2/d8_19_numerics/d819_exact.py` | `certificates/common/d819_exact.py` | edited (exit status) |
| `lean_work/L1_1/v2_K5_*.json` (20 files), `v2common_K5_4.json` | `replay-K5/` (same names) | same, 21 of 21 |
| `lean_work/L1_1/gen_v2_lean.py`, `proto_v2.py` | `replay-K5/` (same names) | same |
| `lean_work/L1_1/replay_v3.py` | `replay-K5/replay_v3.py` | edited (exit status) |
| `lean_work/L1_1/proto_cert.py` | `replay-K5/proto_cert.py` | edited (two paths) |
| `lean_work/L1_1/replay/gen_replay.py` | `replay-K5/gen_replay.py` | edited (one path; subprocess status) |
| `lean_work/L1_1/replay/MANIFEST.sha256` | `replay-K5/MANIFEST.sha256`, and `ZetaSReplay/MANIFEST.orig.sha256` | same |
| `lean_work/L1_1/replay/run_replay.sh`, `run_pools.py` | `replay-K5/drivers/` (same names) | edited (checkout path) |
| `lean_work/L1_1/replay/run_pools.sh` | `replay-K5/drivers/run_pools.sh` | same |
| `lean_work/L1_1/replay/<class>/*.lean`, `lean_work/L1_1/replay/common/*.lean` (1,478 files) | `ZetaSReplay/` (flat, same file names) | same, 1,478 of 1,478 |

## What is not in this folder

- The Lean library and the comparator files: they are the rest of this repository (`ZetaS/`, `ZetaSCertShims/`,
  `comparator/`, `ZetaSReplay/`).
- The paper's sources and PDF: `papers/zeta/`.
- `.olean` build products: `lake build` produces them.
- Superseded data and exploration scripts of the development (earlier certificate formats, solver checkpoints,
  parameter searches that were not certified): they are not part of the evidence.

## Licence

Apache License, Version 2.0, as the rest of the repository: see `LICENSE` and `NOTICE` at the repository root, and
`PROVENANCE.md` here.
