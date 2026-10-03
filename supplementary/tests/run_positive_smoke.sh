#!/bin/bash
# Positive smoke test (audit of 3 October 2026): the documented commands of VERIFY.md, steps 1 to 3, run from a clean
# temporary copy of this folder and succeed with exit status 0; the CertS8 routes start (a box budget or a short time
# limit stops them; the full CertS8 run takes hours, see VERIFY.md). Since the review of the corrected release, the
# documented loop run_lb3_loop.sh also runs to its end on a small claim (0.005, seconds), with and without a change of
# N after a complete round, and an interrupted loop resumes. The folder itself is left unchanged.
# Usage: bash supplementary/tests/run_positive_smoke.sh   (from any folder; `python` with requirements.txt; ~4 min)
# Exit status 0 only if every check succeeds.
set -u -o pipefail
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
T=$(mktemp -d) || exit 1
trap 'rm -rf "$T"' EXIT
cp -a "$HERE" "$T/s" || exit 1
C=$T/s/certificates
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
n=0; nbad=0
check() {   # check NAME DIR COMMAND...: passes if COMMAND, run in DIR, exits 0
  local name=$1 dir=$2; shift 2; n=$((n+1)); local t0=$SECONDS
  (cd "$dir" && "$@") > "$T/out.$n" 2>&1; local rc=$?
  if [ $rc -eq 0 ]; then echo "ok    [$n] $name ($((SECONDS - t0)) s)"
  else echo "WRONG [$n] $name: exit status $rc"; tail -n 4 "$T/out.$n" | cut -c1-200 | sed 's/^/        | /'; nbad=$((nbad+1)); fi
}
K5A=(5 500 certificates/CertAM5/claims_d15e6_a1.6_K5_mu500.json certificates/CertAM5)
K5LOGS=(certificates/CertAM5/logs/cert_K5_w_a16_mu500_d15e6.txt certificates/CertAM5/logs/cert_K5_w_a16_mu500_d15e6_b.txt)
K7A=(7 500 certificates/CertAM7/claims_a1.6_K7_mu500_L1e5.json certificates/CertAM7 certificates/CertAM7/logs/cert_lb3_rerun.txt)
K5P=(11111 11112 11121 11122 11211 11212 11221 11222 12112 12121 12122 12212 12221 12222 21112 21122 21212 21222 22122 22222)

check "step 1: sha256sum -c CHECKSUMS.sha256" "$T/s" sha256sum --quiet -c CHECKSUMS.sha256
check "step 2: verify_inputs.py K=5 on the shipped logs" "$T/s" python -X utf8 certificates/common/verify_inputs.py "${K5A[@]}" "${K5LOGS[@]}"
check "step 2: verify_inputs.py K=7 on the shipped log" "$T/s" python -X utf8 certificates/common/verify_inputs.py "${K7A[@]}"
check "step 2: d819_exact.py K=5" "$T/s" python -X utf8 certificates/common/d819_exact.py "${K5A[@]}" "${K5LOGS[@]}"
check "step 2: d819_exact.py K=7" "$T/s" python -X utf8 certificates/common/d819_exact.py "${K7A[@]}"
check "step 3: CertAM5, runcert.sh on all 20 classes" "$C/CertAM5" bash runcert.sh 1.6 5 500 claims_d15e6_a1.6_K5_mu500.json "$T/k5.log" "${K5P[@]}"
check "step 3: verify_inputs.py K=5 on the fresh log (20/20)" "$T/s" python -X utf8 certificates/common/verify_inputs.py "${K5A[@]}" "$T/k5.log"
check "step 3: CertAM7, runlb3.sh on class 1111111" "$C/CertAM7" bash runlb3.sh 1.6 7 500 claims_a1.6_K7_mu500_L1e5.json . "$T/k7.log" 600 1111111
check "step 3: CertAM7, pexact2.py" "$C/CertAM7" python pexact2.py claims_a1.6_K7_mu500_L1e5.json
check "step 3: CertMajV2, r4_majorant_arb.py" "$C/CertMajV2" python -u r4_majorant_arb.py
check "step 6: replay_v3.py on class 12221" "$T/s/replay-K5" python -X utf8 replay_v3.py 12221
# CertS8: both routes start from the clean copy. The unsharded run stops at a budget of 20,000 boxes (exit status 1,
# reason 'budget', as required for an incomplete run); mkinit.sh shards; one round of round_lb3.sh leaves checkpoints.
n=$((n+1)); (cd "$C/CertS8" && python -u bnb_lb3.py poly8A 8 1700 0.00796 --weights w_poly8A_K8_mu1700.json \
  --window win_poly8A.json --lb3 --sym --qp-sweeps 6 --max-boxes 20000) > "$T/out.$n" 2>&1; rc=$?
if [ $rc -eq 1 ] && grep -q "'reason': 'budget'" "$T/out.$n"; then echo "ok    [$n] step 3: CertS8 unsharded command starts (budget stop, exit status 1)"
else echo "WRONG [$n] CertS8 unsharded command: exit status $rc"; tail -n 4 "$T/out.$n" | cut -c1-200 | sed 's/^/        | /'; nbad=$((nbad+1)); fi
check "step 3: CertS8 sharded route, mkinit.sh (2 shards)" "$C/CertS8" bash mkinit.sh SMOKE 2 poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6'
n=$((n+1)); (cd "$C/CertS8" && bash round_lb3.sh SMOKE 0 2 20 poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6') > "$T/out.$n" 2>&1; rc=$?
if [ $rc -eq 0 ] && [ "$(tail -n 1 "$T/out.$n")" = "CONTINUE 1" ]; then echo "ok    [$n] step 3: CertS8 sharded route, one round of round_lb3.sh (CONTINUE 1)"
else echo "WRONG [$n] CertS8 round_lb3.sh: exit status $rc"; tail -n 4 "$T/out.$n" | cut -c1-200 | sed 's/^/        | /'; nbad=$((nbad+1)); fi
# (review of the corrected release) the documented loop, interrupted and resumed, then to its end on a small claim
S8=$C/CertS8
LA=(poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6')
QA=(poly8A 8 1700 0.005 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6')
QCA=(poly8A 8 1700 0.005 --weights w_poly8A_K8_mu1700.json --window win_poly8A.json --lb3 --sym --qp-sweeps 6)
verdict() {   # verdict NAME OK(0/1)
  if [ "$2" -eq 0 ]; then echo "ok    [$n] $1"
  else echo "WRONG [$n] $1"; tail -n 4 "$T/out.$n" | cut -c1-200 | sed 's/^/        | /'; nbad=$((nbad+1)); fi
}
n=$((n+1)); t0=$SECONDS; (cd "$S8" && timeout 8 bash run_lb3_loop.sh SMOKE 1 2 5 "${LA[@]}") > "$T/out.$n" 2>&1; rc=$?
sleep 2   # let the interrupted round driver stop its shard processes
R=$(cd "$S8" && python s8_manifest.py status SMOKE | sed -n 's/.*current round \([0-9]*\) .*/\1/p')
(cd "$S8" && bash round_lb3.sh SMOKE "$R" 2 5 "${LA[@]}") >> "$T/out.$n" 2>&1; rc2=$?
[ $rc -eq 124 ] && [ $rc2 -eq 0 ] && [ -n "$R" ] && [ "$(tail -n 1 "$T/out.$n")" = "CONTINUE $((R + 1))" ]
verdict "CertS8 run_lb3_loop.sh stopped by a time limit in round $R, then that round resumed (CONTINUE $((R + 1))) ($((SECONDS - t0)) s)" $?
check "CertS8 mkinit.sh QUICK 2 (claim 0.005)" "$S8" bash mkinit.sh QUICK 2 "${QA[@]}"
n=$((n+1)); t0=$SECONDS; (cd "$S8" && bash run_lb3_loop.sh QUICK 0 2 60 "${QA[@]}") > "$T/out.$n" 2>&1; rc=$?
L=$S8/runs/QUICK/DRIVER.log
[ $rc -eq 0 ] && tail -n 1 "$T/out.$n" | grep -q ' round 0 -> ALLOK$' && tail -n 1 "$L" | grep -q ' ALL SHARDS OK: certificate claim=0.005 holds (K=8' \
  && tail -n 2 "$L" | head -n 1 | grep -q ' objective sha256=[0-9a-f]\{64\} (K=8 alpha=poly8A mu=1/1700 claim=1/200 weights sha256=257b340d'
verdict "CertS8 run_lb3_loop.sh QUICK 0 2 60: exit status 0, ALLOK, DRIVER.log ends with the objective and ALL SHARDS OK ($((SECONDS - t0)) s)" $?
check "CertS8 s8_manifest.py verify QUICK (the receipt checked again)" "$S8" python s8_manifest.py verify QUICK -- "${QCA[@]}"
check "CertS8 mkinit.sh NCH 2 (claim 0.005)" "$S8" bash mkinit.sh NCH 2 "${QA[@]}"
n=$((n+1)); t0=$SECONDS; (cd "$S8" && bash run_lb3_loop.sh NCH 0 3 60 "${QA[@]}") > "$T/out.$n" 2>&1; rc=$?
[ $rc -eq 0 ] && tail -n 1 "$T/out.$n" | grep -q ' round 1 -> ALLOK$' && tail -n 1 "$S8/runs/NCH/DRIVER.log" | grep -q ' ALL SHARDS OK: ' \
  && (cd "$S8" && python -c "
import json, sys
m = json.load(open('runs/NCH/run_manifest.json')); r = m['rounds']
sys.exit(0 if m['status'] == 'complete' and [(x['N'], x['state']) for x in r] == [(2, 'resharded'), (3, 'done')] else 1)")
verdict "CertS8 run_lb3_loop.sh NCH 0 3 60: N 2 -> 3 after the complete round 0, round 1 ends ALLOK, lineage kept ($((SECONDS - t0)) s)" $?

printf '%s\n' "objective: sha256=0" "{'ok': True, 'processed': 26357567, 'worst': (0.0080121, array([1.046875  , 2.921875  , 1.0390625 , 1.03515625, 1.0390625 ," \
  "       2.921875  , 1.046875  ])), 'time': 957.9, 'lb3': True}" > "$T/wrapped_ok.log"
check "CertS8 s8_manifest.result_ok: a result record that wraps over two lines (as in a full S8 run) counts as ok" "$S8" \
  python -c "import sys; sys.path.insert(0, '.'); import s8_manifest as m; sys.exit(0 if m.result_ok(open(sys.argv[1]).read().split(chr(10))) else 1)" "$T/wrapped_ok.log"

echo "== $((n - nbad)) of $n checks succeed"
[ $nbad -eq 0 ]
