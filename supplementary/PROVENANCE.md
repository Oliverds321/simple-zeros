# Provenance and licence

## Who wrote what

Every file in this folder is new numerical work written for the ζ paper by its author: the certificate data (`.json`,
`.npy`), the certifier scripts (`bnb_lb3.py`, `bnb_interval_w.py`, `bnb_lb3_w.py`, `r4_majorant_arb.py`, `polywin.py`,
`localK.py`, `shard_ckpt.py`, `s8_manifest.py`, `pexact2.py`, `verify_inputs.py`, `d819_exact.py`), the K = 5 replay generators and their
helpers (`gen_replay.py`, `gen_v2_lean.py`, `proto_v2.py`, `proto_cert.py`), the Python mirror `replay_v3.py`, the
replay's certificate JSON (`v2_K5_*.json`, `v2common_K5_4.json`), the driver scripts (`mkinit.sh`, `round_lb3.sh`,
`run_lb3_loop.sh`, `runcert.sh`, `runlb3.sh`, and `replay-K5/drivers/`), the regression tests (`tests/`), and the run
logs. None of it is copied or adapted from a third party.

## Third-party material

None is included in this folder. The scripts depend only on Python and the general-purpose libraries `numpy`,
`scipy`, `sympy`, `mpmath` and `python-flint` (an interface to the Arb/FLINT libraries), which a user installs
separately (`requirements.txt` names the versions tested); none of their code is redistributed here.

The repository around this folder is a modified copy of the Lean artifact released at
`github.com/anthropics/zeta-23-lean` (Copyright 2026 Anthropic, PBC, Apache License 2.0). That address now leads to
`github.com/anthropics/formal-math`, folder `zeta23/`, whose README names the paper as Alpöge–Furman, arXiv:2608.13637.
What the repository adds and changes is listed in `NOTICE` at the repository root.

## Licence

The files in this folder are released under the Apache License, Version 2.0, as the rest of the follow-up work in the
repository: see `LICENSE` and `NOTICE` at the repository root. The edits made to scripts when the folder was assembled,
and on 3 October 2026 after an audit, are listed in `CHANGES.txt`.

## What is intentionally not described here

This file names only the upstream artifact the repository builds on and its licence, in the words of that artifact's
own README and `NOTICE`. It does not describe or assess any other author's work.
