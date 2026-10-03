# Reruns of the three numerical certificates with the corrected scripts (3 October 2026)

After the corrections of the external review (`RELEASE_NOTES.md`, "Corrections after an external review"), the three
interval-arithmetic certificates were run again in full with the scripts of this release, on Linux (cloud container,
4 CPUs; Python 3.11.15 and the versions of `../requirements.txt`). The logs under `../certificates/*/logs/` are those of
the original runs (Windows, September 2026) and are unchanged. Every result below agrees with them.

| certificate | run | result | files here |
|---|---|---|---|
| `CertAM5` (K = 5) | `runcert.sh` on all 20 classes, one process, 53 s | 20 of 20 certified; box counts and minima equal those of the original logs; `verify_inputs.py` 20/20 and `d819_exact.py` "ALL STRUCTURE + ROBUSTNESS CHECKS PASS: True", p = 0.675158622199…, D = 0.837579311099… | `CertAM5/` |
| `CertAM7` (K = 7) | `runlb3.sh` on all 72 classes, two processes of 36 classes (95 and 136 min) | 72 of 72 certified at the required claims; `verify_inputs.py` 72/72; `d819_exact.py` "ALL STRUCTURE + ROBUSTNESS CHECKS PASS: True", p = 0.676102666964…, D = 0.838051333482…; `pexact2.py` exit status 0 | `CertAM7/` |
| `CertS8` | route (b) of `../VERIFY.md` step 3 with N = 4 shards: `mkinit.sh`, then `run_lb3_loop.sh` (rounds 0 to 4, 20 min per round) | `round 4 done: 4 shards ok, 0 left`, the coverage line and "ALL SHARDS OK: certificate claim=0.00796 holds"; `s8_manifest.py verify` prints COMPLETE (exit status 0); the run's weights and window sha256 are the printed values 257b340d… and c4005f57… | `CertS8/` |

Notes.

- K = 7: the 59 classes that are not palindromes have exactly the box counts of the original log; the 13 palindromic
  classes that differ (run with `--sym`) differ by at most 0.09% (`rerun_K7_all72.log` against
  `../certificates/CertAM7/logs/cert_lb3_rerun.txt`). The floating-point screen that picks bisection axes rounds
  differently across platforms; every accepted box is checked in interval arithmetic, so the verdicts do not depend on it.
- CertS8: the first attempt of round 4 ended with its four shards `'ok': True` (their logs are kept in
  `R1003/attempts/r4_attempt1/`), but the loop stopped with exit status 1: the run-manifest check then required the
  result on the last line of the log, while in a full run the result record wraps over two lines. The check was
  corrected (`../CHANGES.txt`, entry of 3 October 2026, night; tests in `../tests/`), and round 4 was run again from its
  recorded start copies (17 min), with the same outcome. `R1003/` is the complete run folder without its checkpoints
  (none is left at the end): `run_manifest.json`, `DRIVER.log`, every shard log, the per-round manifests. To check it
  again, copy `R1003/` to `../certificates/CertS8/runs/R1003/` and run, in `../certificates/CertS8/`:
  `python s8_manifest.py verify R1003 -- poly8A 8 1700 0.00796 --weights w_poly8A_K8_mu1700.json --window win_poly8A.json --lb3 --sym --qp-sweeps 6`.
- The Lean kernel replay of K = 5 (`ZetaSReplay`, about 20 Lean-hours) was not repeated.
