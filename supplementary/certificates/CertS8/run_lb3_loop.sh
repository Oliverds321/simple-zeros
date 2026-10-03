#!/bin/bash
# d6_5: loop round_lb3.sh until ALL SHARDS OK (exit 0) or FAIL (exit 1).  First re-shards the start round's
# checkpoints into N shards if their number differs from N (sha256-checked by shard_ckpt.py).
# Usage (cwd = d6_5_numerics): bash run_lb3_loop.sh TAG R0 N CHUNK alpha K muinv claim weights.json "EXTRA FLAGS"
# (Oct 2026) The re-shard no longer starts from the checkpoint files that happen to be in the folder (lost shards
# vanished that way). s8_manifest.py prepare checks the run against its manifest first (mkinit.sh writes it): the
# objective of this command must be the run's, R0 its current round, every shard of R0 present with its recorded
# sha256 (or restorable from its start copy after an interruption), the logs of the earlier rounds unchanged, and no
# other shard-like file in the folder. A new N is accepted only then: the complete round R0 is re-sharded into round
# R0+1 (its record and logs are kept), and the loop starts there. Then the loop runs as before.
set -u
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
TAG=$1; R=$2; N=$3; CHUNK=$4; AL=$5; K=$6; MI=$7; CL=$8; WF=$9; EXTRA=${10}
D=runs/$TAG
[ -d $D ] || { echo "run_lb3_loop.sh: FAIL: no run directory $D" >&2; echo FAIL; exit 1; }
out=$(python s8_manifest.py prepare "$TAG" "$R" "$N" -- $AL $K $MI $CL --weights $WF $EXTRA 2>&1)
last=$(printf '%s\n' "$out" | tail -n 1)
case "$last" in
  "ROUND "[0-9]*) R=${last#ROUND };;
  *) echo "$(date '+%F %T') FAIL run_lb3_loop.sh before round $R: $last" >> $D/DRIVER.log
     echo "run_lb3_loop.sh: FAIL: $last" >&2; echo FAIL; exit 1;;
esac
while true; do
  out=$(bash round_lb3.sh $TAG $R $N $CHUNK $AL $K $MI $CL $WF "$EXTRA" | tail -n 1)
  echo "$(date '+%F %T') round $R -> $out"
  case "$out" in
    ALLOK) exit 0;;
    CONTINUE*) R=${out#CONTINUE };;
    *) exit 1;;
  esac
done
