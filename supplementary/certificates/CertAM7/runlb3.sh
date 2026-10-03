#!/bin/bash
# d8_9: usage: runlb3.sh alpha K muinv claimsjson xpatdir logfile tlimit pattern1 pattern2 ...
# LB3 certifier (bnb_lb3_w.py) per pattern; --sym only for palindromic patterns (weights then exactly symmetric, asserted).
# (Oct 2026) Run from this folder. The patterns run one after another (no parallelism). Exit status 0 only if every
# pattern given ends with {'ok': True}: a missing file or claim, a timeout or a failed run is a failure. The log lines are
# unchanged. Coverage of all 72 classes is checked by ../common/verify_inputs.py on the log (VERIFY.md, step 3).
set -u -o pipefail
a=$1; K=$2; mu=$3; cj=$4; xd=$5; log=$6; tl=$7; shift 7
[ -f "$cj" ] || { echo "runlb3.sh: claims file not found: $cj" >&2; exit 1; }
[ -d "$xd" ] || { echo "runlb3.sh: pattern folder not found: $xd" >&2; exit 1; }
[ $# -gt 0 ] || { echo "runlb3.sh: no pattern given" >&2; exit 1; }
nok=0
for p in "$@"; do
  C=$(python -c "import json;print(json.load(open('$cj'))['claims']['$p'])") || { echo "runlb3.sh: no claim for $p in $cj" >&2; continue; }
  rev=$(python -c "print('$p'[::-1])"); sym=""; [ "$p" == "$rev" ] && sym="--sym"
  r=$(timeout $tl python -u bnb_lb3_w.py $a $K $mu $C --weights $xd/xpat_K${K}_$p.json --lb3 $sym --log-every 100000000 2>&1 | grep -E "^\{|weight check|Error|assert" | tr '\n' ' ')
  rc=$?
  echo "K$K a=$a mu=1/$mu $p $sym claim=$C -> ${r:0:330}" >> $log || exit 1
  if [[ "$r" == *"{'ok': True"* ]] && [ $rc -eq 0 ]; then nok=$((nok+1)); else echo "runlb3.sh: $p: not certified (exit status $rc)" >&2; fi
done
echo "runlb3.sh: $nok of $# patterns certified (ok: True)"
[ $nok -eq $# ]
