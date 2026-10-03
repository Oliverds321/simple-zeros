#!/bin/bash
# usage: runcert.sh alpha K muinv claimsjson logfile pattern1 pattern2 ...
# (Oct 2026) Run from this folder. Exit status 0 only if every pattern given ends with {'ok': True}: a missing claims
# file or claim, a timeout or a failed run is a failure. The log lines are unchanged. Coverage of all 20 classes is
# checked by ../common/verify_inputs.py on the log (VERIFY.md, step 3).
set -u -o pipefail
a=$1; K=$2; mu=$3; cj=$4; log=$5; shift 5
[ -f "$cj" ] || { echo "runcert.sh: claims file not found: $cj" >&2; exit 1; }
[ $# -gt 0 ] || { echo "runcert.sh: no pattern given" >&2; exit 1; }
nok=0
for p in "$@"; do
  C=$(python -c "import json;print(json.load(open('$cj'))['claims']['$p'])") || { echo "runcert.sh: no claim for $p in $cj" >&2; continue; }
  r=$(timeout 140 python -u bnb_interval_w.py $a $K $mu $C --weights xpat_K${K}_$p.json --log-every 10000000 2>&1 | grep -E "^\{|weight check" | tr '\n' ' ')
  rc=$?
  echo "K$K a=$a mu=1/$mu $p claim=$C -> ${r:0:260}" >> $log || exit 1
  if [[ "$r" == *"{'ok': True"* ]] && [ $rc -eq 0 ]; then nok=$((nok+1)); else echo "runcert.sh: $p: not certified (exit status $rc)" >&2; fi
done
echo "runcert.sh: $nok of $# patterns certified (ok: True)"
[ $nok -eq $# ]
