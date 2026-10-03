#!/bin/bash
# d6_5: ONE round of the sharded LB3 certifier (adapted from d3_1's run_sharded.sh so that every call ends inside the
# 10-minute tool limit).  Runs every shard runs/TAG/r<R>_<i>.ckpt for <= CHUNK s (in parallel), stops with FAIL on
# any 'ok': False, and merges + re-shards the leftovers into runs/TAG/r<R+1>_*.ckpt (sha256-checked by shard_ckpt.py).
# Usage (cwd = d6_5_numerics):  bash round_lb3.sh TAG R N CHUNK alpha K muinv claim weights.json "EXTRA FLAGS"
# (Oct 2026) Fail-closed checks, against the run manifest runs/TAG/run_manifest.json of mkinit.sh (s8_manifest.py).
# Before the round (s8_manifest.py begin): the objective of this command (K, alpha or window, mu, claim, sha256 of the
# weights and window files, options) must be the run's, and the run neither failed nor complete; R must be its current
# round and N its number of shards; every shard r<R>_<i>.ckpt must be present with the sha256 recorded when it was
# written, the logs of the earlier rounds present unchanged, and no other shard-like file in the folder. A start copy
# of each shard is kept (start/), so that an interrupted round restarts from it. After the round (s8_manifest.py end):
# a shard counts as certified only if its process exited 0, its log ends with 'ok': True and names this objective and
# the shard's sha256, and its checkpoint is gone; as left only if it stopped at the time limit (exit 124) with a
# checkpoint of this objective. 'ok': False fails the run for good (exit 2); any other outcome fails the round (exit 3
# or 5; run it again). ALLOK and "ALL SHARDS OK" are written only when all N shards are certified and the chain from
# the initial checkpoint is accounted for; the line before "ALL SHARDS OK" names the objective and the manifest.
set -u
set -o pipefail
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
TAG=$1; R=$2; N=$3; CHUNK=$4; AL=$5; K=$6; MI=$7; CL=$8; WF=$9; EXTRA=${10}
D=runs/$TAG; LOG=$D/DRIVER.log
[ -d $D ] || { echo "round_lb3.sh: FAIL: no run directory $D" >&2; echo FAIL; exit 4; }
fail() { echo "$(date '+%F %T') FAIL round $R: $1" >> $LOG; echo "round_lb3.sh: FAIL round $R: $1" >&2; echo FAIL; exit $2; }
echo "$(date '+%F %T') round $R start N=$N CHUNK=$CHUNK alpha=$AL K=$K mu=1/$MI claim=$CL weights=$WF extra=$EXTRA" >> $LOG
case "$N" in ''|*[!0-9]*|0*) fail "N must be a positive integer (got '$N')" 4;; esac
case "$R" in ''|*[!0-9]*|0?*) fail "R must be a nonnegative integer (got '$R')" 4;; esac
BNB=($AL $K $MI $CL --weights $WF $EXTRA)
out=$(python s8_manifest.py begin "$TAG" $R $N -- "${BNB[@]}" 2>&1); rc=$?
[ $rc -eq 0 ] || fail "$(printf '%s\n' "$out" | tail -n 1)" 4
pids=(); rcs=()
stop() {   # an interrupted round: stop the shard processes; the next run of this round restarts from the start copies
  for p in ${pids[@]+"${pids[@]}"}; do kill $p 2> /dev/null; done
  wait
  fail "interrupted by signal $1; run the round again (its shards restart from their start copies)" $((128 + $1))
}
trap 'stop 2' INT; trap 'stop 15' TERM; trap 'stop 1' HUP
for ((i = 0; i < N; i++)); do
  f=$D/r${R}_$i.ckpt
  timeout $CHUNK python -u bnb_lb3.py "${BNB[@]}" --checkpoint $f --resume \
      --ckpt-every 40 --log-every 40 --max-boxes 1e13 > ${f%.ckpt}.log 2>&1 &
  pids+=($!)
done
for j in ${pids[@]+"${!pids[@]}"}; do
  wait ${pids[$j]}; rcs+=($?)
done
trap - INT TERM HUP
out=$(python s8_manifest.py end "$TAG" $R $N ${rcs[@]+"${rcs[@]}"} -- "${BNB[@]}" 2>&1); rc=$?
[ $rc -eq 0 ] || fail "$(printf '%s\n' "$out" | tail -n 1)" $rc
st=$(printf '%s\n' "$out" | tail -n 1)
case "$st" in
  ALLOK) echo "$(date '+%F %T') ALL SHARDS OK: certificate claim=$CL holds (K=$K alpha=$AL mu=1/$MI $WF $EXTRA)" >> $LOG; echo ALLOK; exit 0;;
  "CONTINUE $((R + 1))") echo "$st"; exit 0;;
  *) fail "unexpected answer of s8_manifest.py end: $st" 5;;
esac
