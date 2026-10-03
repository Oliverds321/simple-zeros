#!/bin/bash
# Negative controls for the exit status of the scripts in this folder (audit of 3 October 2026, findings R2 and R3,
# and the review of the corrected release, same day: the documented CertS8 loop, input binding, -O, diagnostics).
# Each control gives a script a missing, empty, incomplete, failing or refused input; it passes only if the script
# exits nonzero (and, for the CertS8 drivers, prints no ALLOK and writes no new "ALL SHARDS OK"). A "setup" line is a
# step that must succeed for the controls after it to mean anything; it counts as a control. The controls run on a
# temporary copy of this folder, which is left unchanged.
# Usage: bash supplementary/tests/run_negative_controls.sh   (from any folder; `python` with requirements.txt; ~3 min)
# Exit status 0 only if every control behaves as required.
set -u -o pipefail
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
T=$(mktemp -d) || exit 1
trap 'rm -rf "$T"' EXIT
cp -a "$HERE" "$T/s" || exit 1
C=$T/s/certificates
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
: > "$T/empty.log"
n=0; nbad=0
report() {   # report NAME OK(0/1) OUTFILE
  if [ "$2" -eq 0 ]; then echo "ok    [$n] $1"
  else echo "WRONG [$n] $1"; tail -n 4 "$3" | cut -c1-200 | sed 's/^/        | /'; nbad=$((nbad+1)); fi
}
must_fail() {   # must_fail NAME DIR COMMAND...: passes if COMMAND, run in DIR, exits nonzero
  local name=$1 dir=$2; shift 2; n=$((n+1))
  (cd "$dir" && "$@") > "$T/out.$n" 2>&1; local rc=$?
  [ $rc -ne 0 ]; report "$name (exit status $rc)" $? "$T/out.$n"
}
S8ARGS=(poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6')
round_must_fail() {   # round_must_fail NAME TAG N CHUNK: round 0 of round_lb3.sh must fail and claim nothing
  local name=$1 tag=$2 nn=$3 ch=$4; n=$((n+1))
  (cd "$C/CertS8" && bash round_lb3.sh "$tag" 0 "$nn" "$ch" "${S8ARGS[@]}") > "$T/out.$n" 2>&1; local rc=$?
  local bad=0 claim="no certificate claim"
  [ $rc -ne 0 ] || bad=1
  grep -q '^ALLOK' "$T/out.$n" && { bad=1; claim="printed ALLOK"; }
  grep -q 'ALL SHARDS OK' "$C/CertS8/runs/$tag/DRIVER.log" 2>/dev/null && { bad=1; claim="$claim, wrote ALL SHARDS OK"; }
  report "$name (exit status $rc, $claim)" $bad "$T/out.$n"
}
K5A=(5 500 certificates/CertAM5/claims_d15e6_a1.6_K5_mu500.json certificates/CertAM5)
K5LOGS=(certificates/CertAM5/logs/cert_K5_w_a16_mu500_d15e6.txt certificates/CertAM5/logs/cert_K5_w_a16_mu500_d15e6_b.txt)
cat "${K5LOGS[@]/#/$T/s/}" | grep -v ' 22222 ' > "$T/k5_without_22222.log"

echo "== the six negative tests of the audit (R2)"
must_fail "verify_inputs.py, empty log" "$T/s" python -X utf8 certificates/common/verify_inputs.py "${K5A[@]}" "$T/empty.log"
must_fail "d819_exact.py, empty log" "$T/s" python -X utf8 certificates/common/d819_exact.py "${K5A[@]}" "$T/empty.log"
must_fail "bnb_interval_w.py limited to one box (budget stop)" "$C/CertAM5" python bnb_interval_w.py 1.6 5 500 0.01280197 --weights xpat_K5_11111.json --max-boxes 1
must_fail "runlb3.sh with a 0.001 s timeout" "$C/CertAM7" bash runlb3.sh 1.6 7 500 claims_a1.6_K7_mu500_L1e5.json . "$T/k7.log" 0.001 1111111
must_fail "runcert.sh with a nonexistent claims file" "$C/CertAM5" bash runcert.sh 1.6 5 500 "$T/nonexistent.json" "$T/k5.log" 11111
mkdir -p "$C/CertS8/runs/EMPTY"
round_must_fail "round_lb3.sh on an empty shard folder" EMPTY 8 1

echo "== further R2 controls: incomplete or false results"
must_fail "verify_inputs.py, K5 logs without class 22222" "$T/s" python -X utf8 certificates/common/verify_inputs.py "${K5A[@]}" "$T/k5_without_22222.log"
must_fail "d819_exact.py, K5 logs without class 22222" "$T/s" python -X utf8 certificates/common/d819_exact.py "${K5A[@]}" "$T/k5_without_22222.log"
must_fail "verify_inputs.py run with python -O" "$T/s" python -O -X utf8 certificates/common/verify_inputs.py "${K5A[@]}" "${K5LOGS[@]}"
python -c "import json, sys; j = json.load(open(sys.argv[1])); j['claims']['11111'] = '1/10'; json.dump(j, open(sys.argv[2], 'w'))" \
  "$C/CertAM5/claims_d15e6_a1.6_K5_mu500.json" "$T/claims_false.json"
must_fail "runcert.sh, false claim 1/10 for class 11111 (ok: False)" "$C/CertAM5" bash runcert.sh 1.6 5 500 "$T/claims_false.json" "$T/k5b.log" 11111
must_fail "runcert.sh, pattern absent from the claims" "$C/CertAM5" bash runcert.sh 1.6 5 500 claims_d15e6_a1.6_K5_mu500.json "$T/k5c.log" 33333
python -c "import json, sys; j = json.load(open(sys.argv[1])); j['a1'] = '3/10'; json.dump(j, open(sys.argv[2], 'w'))" \
  "$C/CertAM7/claims_a1.6_K7_mu500_L1e5.json" "$T/claims_a1.json"
must_fail "pexact2.py, a1 = 3/10 (c = 2 - 2a1 fails)" "$C/CertAM7" python pexact2.py "$T/claims_a1.json" 1.6
mkdir -p "$T/maj" && cp "$C/CertMajV2/r4_majorant_arb.py" "$T/maj/" && python -c "import numpy as np, sys; b = np.load(sys.argv[1]); b[0] += 1e-2; np.save(sys.argv[2], b)" \
  "$C/CertMajV2/majorant_delta1_beta.npy" "$T/maj/majorant_delta1_beta.npy"
must_fail "r4_majorant_arb.py, beta_0 + 1e-2 (its negative controls pass)" "$T/maj" python -u r4_majorant_arb.py
must_fail "mkinit.sh with a nonexistent weights file" "$C/CertS8" bash mkinit.sh NOW 2 poly8A 8 1700 0.00796 nonexistent.json '--window win_poly8A.json --lb3 --sym'
(cd "$C/CertS8" && bash mkinit.sh MISS 2 poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym' > /dev/null 2>&1) || echo "(mkinit.sh failed; the next three controls are then vacuous)"
cp -a "$C/CertS8/runs/MISS" "$C/CertS8/runs/EXTRA"; cp -a "$C/CertS8/runs/MISS" "$C/CertS8/runs/CRASH"
rm -f "$C/CertS8/runs/MISS/r0_1.ckpt"
round_must_fail "round_lb3.sh with shard 1 of 2 missing" MISS 2 5
cp "$C/CertS8/runs/EXTRA/r0_0.ckpt" "$C/CertS8/runs/EXTRA/r0_2.ckpt"
round_must_fail "round_lb3.sh with an unrecognised third shard (N=2)" EXTRA 2 5
echo garbage > "$C/CertS8/runs/CRASH/r0_1.ckpt"
round_must_fail "round_lb3.sh with a corrupt shard checkpoint (refused before any shard runs)" CRASH 2 5
round_must_fail "round_lb3.sh with N=0" CRASH 0 5
cp -a "$T/s/replay-K5" "$T/rgen" && printf 'import sys\nsys.exit(3)\n' > "$T/rgen/gen_v2_lean.py"
must_fail "gen_replay.py with a failing generator subprocess" "$T/rgen" python -X utf8 gen_replay.py 12221
python -c "import json, sys; j = json.load(open(sys.argv[1])); j['claims']['12221'] = '1/10'; json.dump(j, open(sys.argv[1], 'w'))" \
  "$C/CertAM5/claims_d15e6_a1.6_K5_mu500.json"
must_fail "replay_v3.py, claim of class 12221 raised to 1/10 (failed leaves)" "$T/s/replay-K5" python -X utf8 replay_v3.py 12221

echo "== R3: weighted or windowed scalar multiprocessing is refused"
must_fail "bnb_interval_w.py --engine scalar --workers 2 --weights" "$C/CertAM5" python bnb_interval_w.py 1.6 5 500 1280197/100000000 --weights xpat_K5_11111.json --engine scalar --workers 2 --max-boxes 3000
must_fail "bnb_lb3_w.py --engine scalar --workers 2 --weights" "$C/CertAM7" python bnb_lb3_w.py 1.6 7 500 1824837/100000000 --weights xpat_K7_1111111.json --engine scalar --workers 2 --max-boxes 3000
must_fail "bnb_lb3.py --engine scalar --workers 2 --window" "$C/CertS8" python bnb_lb3.py poly8A 8 1700 0.00796 --window win_poly8A.json --engine scalar --workers 2 --max-boxes 3000
n=$((n+1)); (cd "$C/CertAM5" && python bnb_interval_w.py 1.6 5 500 1280197/100000000 --weights xpat_K5_11111.json --engine scalar --workers 2 --max-boxes 3000) > "$T/out.$n" 2>&1
grep -q 'does not support --weights' "$T/out.$n"; report "the refusal names the reason" $? "$T/out.$n"

echo "== the documented loop run_lb3_loop.sh (review of the corrected release): lost, extra or changed work is refused"
S8=$C/CertS8
LA=(poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6')
QA=(poly8A 8 1700 0.005 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6')
LCA=(poly8A 8 1700 0.00796 --weights w_poly8A_K8_mu1700.json --window win_poly8A.json --lb3 --sym --qp-sweeps 6)
QCA=(poly8A 8 1700 0.005 --weights w_poly8A_K8_mu1700.json --window win_poly8A.json --lb3 --sym --qp-sweeps 6)
setup() {   # setup NAME COMMAND...: a step (in CertS8) that must succeed; counted as a control
  local name=$1; shift; n=$((n+1))
  (cd "$S8" && "$@") > "$T/out.$n" 2>&1; local rc=$?
  [ $rc -eq 0 ]; report "setup: $name (exit status $rc)" $? "$T/out.$n"
}
s8_must_fail() {   # s8_must_fail NAME TAG COMMAND...: COMMAND, run in CertS8, must exit nonzero (a time limit, 124, is
  # not enough), print no ALLOK and add no "ALL SHARDS OK" to runs/TAG/DRIVER.log
  local name=$1 tag=$2; shift 2; n=$((n+1))
  local before after bad=0 claim="no certificate claim"
  before=$(grep -c 'ALL SHARDS OK' "$S8/runs/$tag/DRIVER.log" 2> /dev/null)
  (cd "$S8" && timeout 120 "$@") > "$T/out.$n" 2>&1; local rc=$?
  after=$(grep -c 'ALL SHARDS OK' "$S8/runs/$tag/DRIVER.log" 2> /dev/null)
  { [ $rc -eq 0 ] || [ $rc -eq 124 ]; } && bad=1
  grep -qE '(^|-> )ALLOK' "$T/out.$n" && { bad=1; claim="printed ALLOK"; }
  [ "${before:-0}" = "${after:-0}" ] || { bad=1; claim="$claim, wrote ALL SHARDS OK"; }
  report "$name (exit status $rc, $claim)" $bad "$T/out.$n"
}
must_fail_with() {   # must_fail_with NAME REGEX DIR COMMAND...: exits nonzero, and the output matches REGEX
  local name=$1 re=$2 dir=$3; shift 3; n=$((n+1))
  (cd "$dir" && "$@") > "$T/out.$n" 2>&1; local rc=$?
  [ $rc -ne 0 ] && grep -qE "$re" "$T/out.$n"; report "$name (exit status $rc)" $? "$T/out.$n"
}
python - "$S8" "$T" <<'EOF'
import json, sys
from fractions import Fraction
S8, T = sys.argv[1], sys.argv[2]
j = json.load(open(f'{S8}/w_poly8A_K8_mu1700.json'))      # the reviewer's change: positive, symmetric, span sums 2
g = list(map(Fraction, j['gam'])); g[0] += Fraction(1, 100); g[6] += Fraction(1, 100); g[3] -= Fraction(2, 100)
j['gam'] = list(map(str, g)); json.dump(j, open(f'{T}/changed_weights.json', 'w'))
w = json.load(open(f'{S8}/win_poly8A.json'))
json.dump(dict(w, coeffs_u=w['coeffs_u'][:4] + ['25/10000']), open(f'{T}/changed_window.json', 'w'))
json.dump(dict(w, note='same coefficients, other bytes'), open(f'{T}/same_coeffs_window.json', 'w'))
EOF
setup "mkinit.sh SEED 2 (claim 0.00796)" bash mkinit.sh SEED 2 "${LA[@]}"
setup "mkinit.sh DONE 2 (claim 0.005)" bash mkinit.sh DONE 2 "${QA[@]}"
setup "run_lb3_loop.sh DONE 0 2 30 (claim 0.005) ends ALLOK" bash run_lb3_loop.sh DONE 0 2 30 "${QA[@]}"
setup "mkinit.sh S825 825 (824 shards of one box, one naturally empty)" bash mkinit.sh S825 825 "${LA[@]}"
for v in L_MISS L_NMISS L_DUP L_EXTRA L_GARB L_SWAP L_FAIL L_ROUND L_CW L_CV L_NOW L_NOV; do cp -a "$S8/runs/SEED" "$S8/runs/$v"; done
rm -f "$S8/runs/L_MISS/r0_1.ckpt"
s8_must_fail "loop, shard 1 of 2 missing" L_MISS bash run_lb3_loop.sh L_MISS 0 2 5 "${LA[@]}"
(cd "$S8" && python -c "
import pickle, pathlib
for p in pathlib.Path('runs/S825').glob('r0_*.ckpt'):
    if sum(len(C) for C, H in pickle.load(open(p, 'rb'))['stack']): p.unlink()")
s8_must_fail "loop, 825 shards: the 824 nonempty ones lost, the naturally empty one kept" S825 bash run_lb3_loop.sh S825 0 2 10 "${LA[@]}"
mkdir -p "$S8/runs/LOST" && (cd "$S8" && python shard_ckpt.py 825 runs/LOST/r0 runs/SEED/r0_0.ckpt runs/SEED/r0_1.ckpt > /dev/null && python -c "
import pickle, pathlib
for p in pathlib.Path('runs/LOST').glob('r0_*.ckpt'):
    if sum(len(C) for C, H in pickle.load(open(p, 'rb'))['stack']): p.unlink()")
s8_must_fail "loop on 825 shards made by shard_ckpt.py without a run manifest, nonempty ones lost (the reviewer's reproducer)" LOST bash run_lb3_loop.sh LOST 0 2 10 "${LA[@]}"
cp "$S8/runs/L_DUP/r0_1.ckpt" "$S8/runs/L_DUP/r0_01.ckpt"
s8_must_fail "loop, a duplicate of shard 1 (r0_01.ckpt)" L_DUP bash run_lb3_loop.sh L_DUP 0 2 5 "${LA[@]}"
cp "$S8/runs/L_EXTRA/r0_0.ckpt" "$S8/runs/L_EXTRA/r0_2.ckpt"
s8_must_fail "loop, an extra shard r0_2.ckpt (N=2)" L_EXTRA bash run_lb3_loop.sh L_EXTRA 0 2 5 "${LA[@]}"
echo garbage > "$S8/runs/L_GARB/r0_1.ckpt"
s8_must_fail "loop, a corrupt shard checkpoint" L_GARB bash run_lb3_loop.sh L_GARB 0 2 5 "${LA[@]}"
cp "$S8/runs/L_SWAP/r0_0.ckpt" "$S8/runs/L_SWAP/r0_1.ckpt"
s8_must_fail "loop, shard 1 replaced by a valid checkpoint (a copy of shard 0)" L_SWAP bash run_lb3_loop.sh L_SWAP 0 2 5 "${LA[@]}"
rm -f "$S8/runs/L_NMISS/r0_1.ckpt"
s8_must_fail "loop, N changed to 3 while shard 1 of round 0 is missing" L_NMISS bash run_lb3_loop.sh L_NMISS 0 3 5 "${LA[@]}"
s8_must_fail "round_lb3.sh, a shard ends 'ok': False (--min-width 4)" L_FAIL bash round_lb3.sh L_FAIL 0 2 20 poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6 --min-width 4'
rm -f "$S8"/runs/L_FAIL/r0_*.log
s8_must_fail "loop after a shard ended 'ok': False, its logs deleted (the run stays failed)" L_FAIL bash run_lb3_loop.sh L_FAIL 0 2 5 "${LA[@]}"
setup "round_lb3.sh L_ROUND 0 2 3 (one round; CONTINUE 1)" bash round_lb3.sh L_ROUND 0 2 3 "${LA[@]}"
cp -a "$S8/runs/L_ROUND" "$S8/runs/L_LOGGONE"; cp -a "$S8/runs/L_ROUND" "$S8/runs/L_LOGEDIT"
rm -f "$S8/runs/L_LOGGONE/r0_1.log"; echo x >> "$S8/runs/L_LOGEDIT/r0_0.log"
s8_must_fail "loop, the log of shard 1 of the closed round 0 missing" L_LOGGONE bash run_lb3_loop.sh L_LOGGONE 1 2 5 "${LA[@]}"
s8_must_fail "loop, the log of shard 0 of the closed round 0 changed" L_LOGEDIT bash run_lb3_loop.sh L_LOGEDIT 1 2 5 "${LA[@]}"
s8_must_fail "loop, round 0 run again after it closed" L_ROUND bash run_lb3_loop.sh L_ROUND 0 2 5 "${LA[@]}"
s8_must_fail "loop, changed weights file (resume)" L_CW bash run_lb3_loop.sh L_CW 0 2 5 poly8A 8 1700 0.00796 "$T/changed_weights.json" '--window win_poly8A.json --lb3 --sym --qp-sweeps 6'
s8_must_fail "loop, changed window file (resume)" L_CV bash run_lb3_loop.sh L_CV 0 2 5 poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json "--window $T/changed_window.json --lb3 --sym --qp-sweeps 6"
s8_must_fail "loop, nonexistent weights file" L_NOW bash run_lb3_loop.sh L_NOW 0 2 5 poly8A 8 1700 0.00796 NONEXISTENT_WEIGHTS.json '--window win_poly8A.json --lb3 --sym --qp-sweeps 6'
s8_must_fail "loop, nonexistent window file" L_NOV bash run_lb3_loop.sh L_NOV 0 2 5 poly8A 8 1700 0.00796 w_poly8A_K8_mu1700.json '--window NONEXISTENT_WINDOW.json --lb3 --sym --qp-sweeps 6'
cp "$S8/runs/SEED/r0_0.ckpt" "$T/resume.ckpt"
must_fail_with "bnb_lb3.py --resume with changed weights (refused, not a budget stop)" 'refusing to resume' "$S8" python bnb_lb3.py poly8A 8 1700 0.00796 --weights "$T/changed_weights.json" --window win_poly8A.json --lb3 --sym --qp-sweeps 6 --checkpoint "$T/resume.ckpt" --resume --max-boxes 1
must_fail_with "bnb_lb3.py --resume with a window file of the same coefficients, other bytes" 'refusing to resume' "$S8" python bnb_lb3.py poly8A 8 1700 0.00796 --weights w_poly8A_K8_mu1700.json --window "$T/same_coeffs_window.json" --lb3 --sym --qp-sweeps 6 --checkpoint "$T/resume.ckpt" --resume --max-boxes 1
s8_must_fail "round_lb3.sh on a complete run, nonexistent weights and window (the reviewer's case)" DONE bash round_lb3.sh DONE 0 2 10 poly8A 8 1700 0.005 NONEXISTENT_WEIGHTS.json '--window NONEXISTENT_WINDOW.json --lb3 --sym'
s8_must_fail "round_lb3.sh on a complete run, changed weights" DONE bash round_lb3.sh DONE 0 2 10 poly8A 8 1700 0.005 "$T/changed_weights.json" '--window win_poly8A.json --lb3 --sym --qp-sweeps 6'
s8_must_fail "s8_manifest.py verify of a complete run, changed window" DONE python s8_manifest.py verify DONE -- poly8A 8 1700 0.005 --weights w_poly8A_K8_mu1700.json --window "$T/changed_window.json" --lb3 --sym --qp-sweeps 6
rm -f "$S8/runs/DONE/r0_1.log"
s8_must_fail "s8_manifest.py verify of a complete run whose shard log is missing" DONE python s8_manifest.py verify DONE -- "${QCA[@]}"
s8_must_fail "python -O s8_manifest.py begin, shard 1 of 2 missing" L_MISS python -O s8_manifest.py begin L_MISS 0 2 -- "${LCA[@]}"

echo "== python -O, the light checker's alpha, the majorant diagnostic"
mkdir -p "$S8/runs/OPT" && (cd "$S8" && python -c "
import pickle
ck = pickle.load(open('runs/SEED/r0_1.ckpt', 'rb')); a = ck['args']; ck['args'] = a[:3] + ('0.02',) + a[4:]
pickle.dump(ck, open('runs/OPT/different.ckpt', 'wb'))")
must_fail_with "python -O shard_ckpt.py, parents with different checkpoint args" 'args differ' "$S8" python -O shard_ckpt.py 2 runs/OPT/optimized runs/SEED/r0_0.ckpt runs/OPT/different.ckpt
must_fail_with "python -O shard_ckpt.py, a parent missing" 'cannot read' "$S8" python -O shard_ckpt.py 2 runs/OPT/missing runs/SEED/r0_0.ckpt runs/OPT/nonexistent.ckpt
must_fail_with "python -O shard_ckpt.py, N = 0" 'positive integer' "$S8" python -O shard_ckpt.py 0 runs/OPT/zero runs/SEED/r0_0.ckpt
cp "$HERE/certificates/CertAM5/claims_d15e6_a1.6_K5_mu500.json" "$C/CertAM5/"   # undo the change of the replay control
n=$((n+1)); (cd "$T/s" && python -X utf8 certificates/common/verify_inputs.py "${K5A[@]}" "${K5LOGS[@]}") > "$T/out.$n" 2>&1
report "setup: verify_inputs.py on the shipped K5 logs (20/20, exit status 0)" $? "$T/out.$n"
cat "${K5LOGS[@]/#/$T/s/}" | sed 's/a=1\.6 /a=999 /' > "$T/k5_alpha999.log"
must_fail "verify_inputs.py, K5 logs with a=999 in place of a=1.6" "$T/s" python -X utf8 certificates/common/verify_inputs.py "${K5A[@]}" "$T/k5_alpha999.log"
must_fail "d819_exact.py, K5 logs with a=999 in place of a=1.6" "$T/s" python -X utf8 certificates/common/d819_exact.py "${K5A[@]}" "$T/k5_alpha999.log"
cat "${K5LOGS[@]/#/$T/s/}" | sed 's/weight check passed: pattern [12]*/weight check passed: pattern 11111/' > "$T/k5_wrongpat.log"
must_fail "verify_inputs.py, K5 logs whose weight check names class 11111 on every line" "$T/s" python -X utf8 certificates/common/verify_inputs.py "${K5A[@]}" "$T/k5_wrongpat.log"
mkdir -p "$T/maj2" && cp "$C/CertMajV2/r4_majorant_arb.py" "$T/maj2/" && python -c "import numpy as np, sys; b = np.load(sys.argv[1]); b[0] -= 1e-2; np.save(sys.argv[2], b)" \
  "$C/CertMajV2/majorant_delta1_beta.npy" "$T/maj2/majorant_delta1_beta.npy"
n=$((n+1)); (cd "$T/maj2" && python -u r4_majorant_arb.py) > "$T/out.$n" 2>&1; rc=$?
[ $rc -eq 1 ] && grep -q "^(b) B' - f > 0 on \[0,1/2\]: FAIL" "$T/out.$n" && ! grep -q Traceback "$T/out.$n"
report "r4_majorant_arb.py, beta_0 - 1e-2: (b) reported as FAIL, no traceback (exit status $rc)" $? "$T/out.$n"

printf '%s\n' "{'ok': True, 'processed': 5, 'worst': (0.008, array([1.0,"  "       2.0]))}" "Traceback (most recent call last):" > "$T/ok_then_tb.log"
must_fail "s8_manifest.result_ok: 'ok': True followed by a traceback is not a result" "$S8" python -c "import sys; sys.path.insert(0, '.'); import s8_manifest as m; sys.exit(0 if m.result_ok(open(sys.argv[1]).read().split(chr(10))) else 1)" "$T/ok_then_tb.log"
printf '%s\n' "objective: sha256=0" "{'ok': False, 'reason': 'budget'}" > "$T/ok_false.log"
must_fail "s8_manifest.result_ok: 'ok': False is not a result" "$S8" python -c "import sys; sys.path.insert(0, '.'); import s8_manifest as m; sys.exit(0 if m.result_ok(open(sys.argv[1]).read().split(chr(10))) else 1)" "$T/ok_false.log"

echo "== $((n - nbad)) of $n controls behave as required"
[ $nbad -eq 0 ]
