# How to verify: exact commands, in order

Run every command from the repository root unless a step says otherwise. Steps 1 to 3 need only Python 3 and the
packages of `requirements.txt` (the versions tested on 3 October 2026: `python -m pip install -r
supplementary/requirements.txt`); steps 4 and 5 need the Lean toolchain of the repository (`elan` picks it from
`lean-toolchain`); step 6 is optional. Times and memory figures are those of the runs recorded in the logs; other
hardware will differ.

Every script and driver of steps 2, 3 and 6 exits with status 0 only on success: a missing input, a failed or
incomplete check, a budget stop or a timeout gives a nonzero exit status. Check the exit status as well as the
expected line. Do not run the Python scripts with `python -O` or with `PYTHONOPTIMIZE` set: several of their checks are
`assert` statements (the entry points that rely on them refuse to run under `-O`; `shard_ckpt.py` and `s8_manifest.py`
use explicit checks, which hold either way). Step 7 runs regression tests of these exit statuses.

## 1. Checksums (seconds; any `sha256sum`)

```bash
cd supplementary && sha256sum -c CHECKSUMS.sha256 && cd ..
cd ZetaSReplay && sha256sum -c MANIFEST.sha256 && cd ..
```

Every line must end in `OK`. The seven sha256 values printed in the paper and in the doc-strings of
`comparator/ChallengeDeps/FollowUpZeta.lean` are listed, with their files, in `README.md` of this folder; the two that
are hashes of concatenations are checked by

```bash
cat $(ls supplementary/certificates/CertAM5/xpat_K5_*.json | sort) | sha256sum   # a5947c01…
cat $(ls supplementary/certificates/CertAM7/xpat_K7_*.json | sort) | sha256sum   # 33c4c8c5…
```

## 2. Exact-rational side conditions (seconds; Python 3, and for `d819_exact.py` also `sympy` and `python-flint`)

These check, without interval arithmetic, that the weights are nonnegative and reversal-symmetric, that every span's
weights sum to 2, that `a1`, `a2`, `nu` are the stated values, that every claim equals the sum the definition requires,
that the reversal classes cover every mark pattern, and that the certificate log records `ok: True` for every class at
exactly its claim; `d819_exact.py` also recomputes the proportions from the definitions.

```bash
python -X utf8 supplementary/certificates/common/verify_inputs.py 5 500 \
  supplementary/certificates/CertAM5/claims_d15e6_a1.6_K5_mu500.json supplementary/certificates/CertAM5 \
  supplementary/certificates/CertAM5/logs/cert_K5_w_a16_mu500_d15e6.txt \
  supplementary/certificates/CertAM5/logs/cert_K5_w_a16_mu500_d15e6_b.txt
# expected: "K=5 mu=1/500: 20 canonical patterns (cover all 32); certified ok at a claim >= the required claim: 20/20"

python -X utf8 supplementary/certificates/common/verify_inputs.py 7 500 \
  supplementary/certificates/CertAM7/claims_a1.6_K7_mu500_L1e5.json supplementary/certificates/CertAM7 \
  supplementary/certificates/CertAM7/logs/cert_lb3_rerun.txt
# expected: "K=7 mu=1/500: 72 canonical patterns (cover all 128); certified ok at a claim >= the required claim: 72/72"

python -X utf8 supplementary/certificates/common/d819_exact.py 5 500 \
  supplementary/certificates/CertAM5/claims_d15e6_a1.6_K5_mu500.json supplementary/certificates/CertAM5 \
  supplementary/certificates/CertAM5/logs/cert_K5_w_a16_mu500_d15e6.txt \
  supplementary/certificates/CertAM5/logs/cert_K5_w_a16_mu500_d15e6_b.txt
# expected, among others: "p   = [0.6751586221992…", "D   = [0.8375793110996…",
#                         "ALL STRUCTURE + ROBUSTNESS CHECKS PASS: True"

python -X utf8 supplementary/certificates/common/d819_exact.py 7 500 \
  supplementary/certificates/CertAM7/claims_a1.6_K7_mu500_L1e5.json supplementary/certificates/CertAM7 \
  supplementary/certificates/CertAM7/logs/cert_lb3_rerun.txt
# expected, among others: "p   = [0.6761026669641…", "D   = [0.8380513334820…",
#                         "ALL STRUCTURE + ROBUSTNESS CHECKS PASS: True"
```

These four commands were run on 1 October 2026 with the outputs shown (a few seconds each), and again on 3 October
2026 (same outputs; exit status 0). `verify_inputs.py` exits with status 1 unless every canonical pattern (20 for
K = 5, 72 for K = 7) is certified in the given logs; a log entry counts only if its alpha is the claims file's (`a=1.6`;
a log with `a=999` certifies nothing), the weight check it prints names its own class, and `--sym` appears only for a
palindromic class. `d819_exact.py` exits with status 1 unless the last line reads `True`.

## 3. Re-run the interval-arithmetic certifiers (minutes to hours; Python 3, `numpy`, `scipy`, `sympy`, `mpmath`, `python-flint`)

Full reruns of the three certificates with these scripts (3 October 2026, Linux) are in `reruns-2026-10-03/` (its README
gives the commands, durations and results).

`scipy` is needed because `localK.py` imports it; `sympy` because `polywin.py` (CertS8) uses it. Each block below runs
in the folder it names, and every file it needs ships in that folder.

**CertS8**, in `supplementary/certificates/CertS8` (needs `bnb_lb3.py`, `localK.py`, `polywin.py` and the two JSON
files; the sharded route also `shard_ckpt.py`, `s8_manifest.py`, `mkinit.sh`, `round_lb3.sh` and `run_lb3_loop.sh`). About 4e8 boxes in
all (4.4e8 and 3.9e8 in the two recorded runs, at about 1.1e4 boxes per second per process). Two routes:

```bash
cd supplementary/certificates/CertS8

# (a) unsharded: one process, on the order of 10 hours.
python -u bnb_lb3.py poly8A 8 1700 0.00796 --weights w_poly8A_K8_mu1700.json --window win_poly8A.json \
  --lb3 --sym --qp-sweeps 6
# must end with a line that begins "{'ok': True," and exit with status 0 (any other result: status 1).

# (b) sharded, the route of logs/DRIVER_P8b.log (8 shard processes in parallel; about 1 h 15 min of wall time there).
bash mkinit.sh P8b 8 poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6'
bash run_lb3_loop.sh P8b 0 8 1200 poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json \
  '--window win_poly8A.json --lb3 --sym --qp-sweeps 6'
# mkinit.sh must exit with status 0 (it runs the first 20,000 boxes, then writes the 8 shards runs/P8b/r0_*.ckpt
# and the run manifest runs/P8b/run_manifest.json).
# run_lb3_loop.sh repeats round_lb3.sh (each round runs every shard for at most 1200 s) until a round ends with all
# shards ok; it must print "round R -> ALLOK" and exit with status 0, and runs/P8b/DRIVER.log must end with the lines
#   <date> objective sha256=<64 hex digits> (K=8 alpha=poly8A mu=1/1700 claim=199/25000 weights sha256=257b340d...
#          window sha256=c4005f57...): coverage accounted for from the initial checkpoint ... through round R: ...
#   <date> ALL SHARDS OK: certificate claim=0.00796 holds (K=8 alpha=poly8A mu=1/1700 w_poly8A_K8_mu1700.json ...)
# DRIVER.log records every round: each shard of a round ends with 'ok': True or is re-sharded into the next round, and
# shard_ckpt.py checks by a sha256 that the new shards partition the leftover boxes exactly. Any failure stops the
# loop with exit status 1. N (here 8) is the number of shard processes run in parallel; choose it for your cores.
# A finished run can be checked again at any time (exit status 0 only for a complete run of exactly this objective):
python s8_manifest.py verify P8b -- poly8A 8 1700 0.00796 --weights w_poly8A_K8_mu1700.json --window win_poly8A.json \
  --lb3 --sym --qp-sweeps 6
cd ..
```

`logs/DRIVER_P8.log` is an earlier run of route (b) that started with 5 shards and was re-sharded to 8 in round 3 (with
the scripts of then, the re-shard kept the round number; now a change of N opens a new round, see below).

**The run manifest of route (b)** (added after the review of the corrected release, 3 October 2026; a reviewer showed
that the loop re-sharded whatever checkpoint files were left, so that lost shards vanished and a run could end with
"ALL SHARDS OK" after losing all its unresolved boxes). `mkinit.sh` now writes `runs/<TAG>/run_manifest.json`
(`s8_manifest.py`), and every round updates it. It records:

- the objective of the run: K, alpha (a label when a window is given), mu, the claim, the sha256 of the weights file
  and of the window file, the window coefficients, and the options `--sym`, `--lb3`, `--engine`, `--pure`, `--backend`,
  `--prec`; its sha256 is the "objective sha256" above. Options that only steer or stop the search (`--qp-sweeps`,
  `--axis`, `--min-width`, budgets, checkpointing) are not part of it (the recorded run P8 changed `--qp-sweeps` after
  round 0);
- the root: `init.log` (a fresh start that stopped at its box budget) and the initial checkpoint (sha256, boxes);
- for every round: N, each shard as written (name, sha256, boxes), its parents and the sha256 of the sorted rows of
  their union; once the round is closed, each shard's outcome: certified (its log, sha256) or left (the checkpoint it
  left, sha256, boxes). The parents of round R+1 are exactly the checkpoints left in round R. A copy of the manifest as
  it stood when each round opened stays in `runs/<TAG>/manifests/`.

The same objective sha256 is stored in every checkpoint (`bnb_lb3.py` refuses to resume a checkpoint of another
objective, so changed weights or window are refused, not resumed) and printed in the second line of every
`bnb_lb3.py` log; a shard counts as certified only if its process exited 0, its log ends with `{'ok': True,` and names
the run's objective and the sha256 of the shard it resumed, and its checkpoint is gone.

Before any round or re-shard, `round_lb3.sh` and `run_lb3_loop.sh` refuse (exit status nonzero, no ALLOK, no "ALL SHARDS
OK"): a folder without a manifest; a command whose objective differs from the run's (a missing or changed weights or
window file included); a failed run (a shard that ended `'ok': False` fails the run for good: start a new run with a new
TAG) or a complete one; a round R other than the current round; a missing shard, or one whose sha256 differs from the
recorded one (corrupt, replaced); any other shard-like file in the folder (an extra, duplicate or stale `*.ckpt`, a
`r<R>_<i>.log` of no recorded round, a text manifest of no round); a missing or changed log of a closed round. A new N
is accepted by `run_lb3_loop.sh` only when every shard of the current round is present with its recorded sha256: that
complete round is then re-sharded into the next round, and its record stays in the manifest. `round_lb3.sh` keeps a
start copy of each shard (`runs/<TAG>/start/`) while the round runs: a round stopped by a signal or a crash restarts
from these copies when it is run again (the logs of the stopped attempt move to `runs/<TAG>/attempts/`). To resume a
stopped loop, `python s8_manifest.py status <TAG>` names the current round R; then run `run_lb3_loop.sh <TAG> R ...`
with the same arguments. Checkpoints of the tooling before this change carry no objective and are refused.

**CertAM5**, in `supplementary/certificates/CertAM5`: about 1.18e7 boxes (LB1-2) + 3.7e5 (LB3) over 20 classes; 1 to 6
s per class; 53 s for all 20 on 3 October 2026.

```bash
cd CertAM5
bash runcert.sh 1.6 5 500 claims_d15e6_a1.6_K5_mu500.json <new logfile> 11111 11112 11121 11122 11211 11212 \
  11221 11222 12112 12121 12122 12212 12221 12222 21112 21122 21212 21222 22122 22222
# must print "runcert.sh: 20 of 20 patterns certified (ok: True)" and exit with status 0. Then check coverage:
python -X utf8 ../common/verify_inputs.py 5 500 claims_d15e6_a1.6_K5_mu500.json . <new logfile>
# expected: "... certified ok at a claim >= the required claim: 20/20", exit status 0
cd ..
```

**CertAM7**, in `supplementary/certificates/CertAM7`: about 4.8e8 boxes over 72 classes; between about 146 s and about
610 s per class in the rerun log (class 1111111: 50 s on 3 October 2026). `runlb3.sh` runs the classes one after
another in one process: budget 5 to 10 hours. To use several cores, start several `runlb3.sh` with disjoint pattern
lists and separate log files, and give all the logs to `verify_inputs.py`.

```bash
cd CertAM7
bash runlb3.sh 1.6 7 500 claims_a1.6_K7_mu500_L1e5.json . <new logfile> <timeout per class, s, e.g. 1800> \
  $(ls xpat_K7_*.json | sed 's/xpat_K7_//; s/\.json//')
# must print "runlb3.sh: 72 of 72 patterns certified (ok: True)" and exit with status 0. Then check coverage:
python -X utf8 ../common/verify_inputs.py 7 500 claims_a1.6_K7_mu500_L1e5.json . <new logfile>
# expected: "... certified ok at a claim >= the required claim: 72/72", exit status 0
python pexact2.py claims_a1.6_K7_mu500_L1e5.json    # p, D and the robustness conditions; exit status 0 if both hold
cd ..

# CertMajV2: Arb at 106 bits, seconds. Exit status 0 only if 2I' < s, (a) and (b) are certified and both negative
# controls fail.
cd CertMajV2
python -u r4_majorant_arb.py
cd ../../..
```

On 3 October 2026 (Linux) the 20 K = 5 classes and K = 7 class 1111111 gave the box counts and minima of the logs
exactly. The first CertS8 shard set from `mkinit.sh` had the counts of the logs (824 boxes, 19,164 processed) but a
different sha256 of its rows than `logs/DRIVER_P8b.log` (Windows). Not investigated; that sha256 checks the partition
within one run, and the float screen, which only picks bisection axes, may round differently across platforms.

**The optional engine `--engine scalar` with `--workers` > 1** is refused (exit status 1) when weights or a window are
given: its worker processes would check the default weights instead (audit of 3 October 2026, R3). The documented runs
use the default `--engine numpy`, which does not use worker processes.

## 4. The Lean statements, without the K = 5 replay (hours the first time: Mathlib and the libraries are built)

```bash
lake exe cache get                                   # optional: prebuilt Mathlib
lake build ZetaS ZetaShell
lake build Solution.FollowUpZeta
lake env lean comparator/PrintAxioms/FollowUpZeta.lean
```

Every line of the last command must read `'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`
(fourteen lines: six headlines, their six cumulative forms, two non-vacuity companions). This checks that the
statements of `comparator/Challenge/FollowUpZeta.lean` are proved from the three certificates as displayed
hypotheses and Lean's three standard axioms. It does not check the certificates themselves: step 3 does, outside Lean,
and step 5 does, in the kernel, for `CertAM5`. For the strongest check (statement equality and kernel replay by
comparator) see `comparator/README_followup.md`.

## 5. The kernel replay of the K = 5 certificate (about 20 Lean-hours of CPU time)

```bash
lake build ZetaSReplay
lake env lean comparator/PrintAxioms/FollowUpReplay.lean
```

Expected: three lines, for `ZetaS.Top.zeta_simple_K5_uncond`, `ZetaS.Top.zeta_distinct_K5_uncond` and
`ZetaS.CertV2.certAM5_replayed`, each `depends on axioms: [propext, Classical.choice, Quot.sound]`. The build has 1,478
modules and leaves about 7 GB of build products. In the run of 28 September 2026 a single file needed at most 3.6 GB of
memory (the two final files 4.6 and 4.7 GB), and the whole replay took 20.4 Lean-hours of CPU time and 2 h 50 min of wall time
with several files checked in parallel; `lake` checks as many files in parallel as the import graph allows, so allow
for several times the per-file memory. Details: `ZetaSReplay/README.md`.

## 6. Optional: regenerate the 1,478 replay files (about two minutes; Python 3, `numpy`, `scipy`)

```bash
cd supplementary/replay-K5
python -X utf8 gen_replay.py          # all 20 classes; or name classes, e.g. gen_replay.py 11111
```

The generator writes the class folders `11111/` … `22222/` and `common/` next to itself. On Windows its output has
CRLF line endings, as the recorded files do, and `sha256sum -c MANIFEST.sha256` checks it directly (run on 1 October
2026: 1,478 of 1,478 OK). On Linux or macOS the generator writes LF line endings; convert them first (tested the
same day: on LF copies of the files, 0 OK; after this conversion, 1,478 OK):

```bash
python -c "import glob, pathlib; [pathlib.Path(f).write_bytes(pathlib.Path(f).read_bytes().replace(b'\r\n', b'\n').replace(b'\n', b'\r\n')) for f in glob.glob('*/*.lean')]"
sha256sum -c MANIFEST.sha256
```

The generated files are those of `ZetaSReplay/` (same names, flat there). `replay_v3.py` is a Python mirror of the
Lean checker, used as a differential test during development (about 10 s per class:
`python -X utf8 replay_v3.py 11111,11112`); soundness rests on the Lean kernel, not on this mirror.

`gen_replay.py` stops with exit status 1 if its generator subprocess `gen_v2_lean.py` fails for a class, and
`replay_v3.py` exits with status 1 if any leaf fails. On 3 October 2026 (Linux): regeneration in 122 s, 1,478 of 1,478
OK after the conversion above; `replay_v3.py` on all 20 classes, 46,047 leaves, 0 failed, exit status 0.

The job drivers of the 28 September run are kept in `replay-K5/drivers/` for provenance only: they need the
project's internal job runner, which is not part of this repository; `lake build ZetaSReplay` is the supported route.

## 7. Regression tests of the exit statuses (minutes; Python 3 and `requirements.txt`)

```bash
bash supplementary/tests/run_negative_controls.sh   # about 1 minute
bash supplementary/tests/run_positive_smoke.sh      # about 3 minutes
```

Both work on a temporary copy of this folder and leave the folder unchanged. `run_negative_controls.sh` gives the
scripts empty, incomplete, false or missing inputs (among them the six negative tests of the audit of 3 October 2026,
the refused scalar multiprocessing configuration, and the cases of the review of the corrected release: the CertS8 loop
with a missing shard, with 825 shards of which the 824 nonempty ones are lost, with a duplicate, extra, corrupt or
replaced shard, with a change of N while a shard is missing, after a shard ended `'ok': False`, with a missing or
changed log of a closed round, with changed, other or missing weights or window files, on a complete run with other
inputs; `python -O shard_ckpt.py` on mismatched parents; `verify_inputs.py` with `a=999` in the logs; the majorant's
failure report) and requires a nonzero exit status, and from the CertS8 drivers no ALLOK and no new "ALL SHARDS OK".
`run_positive_smoke.sh` runs steps 1 to 3 from the clean copy: the checksums, the four input checks, all 20 K = 5
classes with `verify_inputs.py` on the fresh log, K = 7 class 1111111, `pexact2.py`, the majorant, `replay_v3.py` on
one class, the start of both CertS8 routes (a box budget or a 20 s round stops them), a CertS8 loop stopped by a time
limit and resumed, and two complete CertS8 loops on the small claim 0.005 (seconds), one with a change of N after its
complete first round. Each script prints one line per control and exits with status 0 only if every control behaves
as required.
