#!/bin/bash
# d6_5: initial checkpoint (first chunk processed) + N shards.  Usage: bash mkinit.sh TAG N alpha K muinv claim weights "EXTRA"
# (Oct 2026) Run from this folder (needs bnb_lb3.py, localK.py, polywin.py, shard_ckpt.py, s8_manifest.py). Exit status 0
# only if the initial run stopped at its box budget with a checkpoint and s8_manifest.py init wrote the N shards
# runs/TAG/r0_<i>.ckpt (with shard_ckpt.py) and the run manifest runs/TAG/run_manifest.json: the objective (K, alpha or
# window, mu, claim, sha256 of the weights and window files, options), the initial log and checkpoint, and the sha256
# and box count of each shard. round_lb3.sh and run_lb3_loop.sh continue only a run with this manifest. A folder that
# holds a run manifest or checkpoints already is refused: use a new TAG.
set -u
set -o pipefail
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
TAG=$1; N=$2; AL=$3; K=$4; MI=$5; CL=$6; WF=$7; EXTRA=$8
case "$N" in ''|*[!0-9]*|0*) echo "mkinit.sh: N must be a positive integer (got '$N')" >&2; exit 1;; esac
D=runs/$TAG
if [ -e $D/run_manifest.json ] || ls $D/*.ckpt > /dev/null 2>&1; then
  echo "mkinit.sh: FAIL: $D holds a run already (run_manifest.json or checkpoints); use a new TAG" >&2; exit 1
fi
mkdir -p $D || exit 1
python -u bnb_lb3.py $AL $K $MI $CL --weights $WF $EXTRA --checkpoint $D/init.ckpt --ckpt-every 3 --max-boxes 20000 > $D/init.log 2>&1
tail -n 1 $D/init.log | cut -c1-300
# the initial run is meant to stop at its box budget ('reason': 'budget', exit status 1) and to leave init.ckpt
if [ ! -f $D/init.ckpt ] || ! grep -q "'reason': 'budget'" $D/init.log; then
  echo "mkinit.sh: FAIL: the initial run did not stop at its box budget with a checkpoint (see $D/init.log)" >&2; exit 1
fi
python s8_manifest.py init $TAG $N -- $AL $K $MI $CL --weights $WF $EXTRA > $D/DRIVER.log && rm -f $D/init.ckpt || { echo "mkinit.sh: FAIL: s8_manifest.py init (see $D/DRIVER.log)" >&2; exit 1; }
for ((i = 0; i < N; i++)); do [ -f $D/r0_$i.ckpt ] || { echo "mkinit.sh: FAIL: shard $D/r0_$i.ckpt missing" >&2; exit 1; }; done
head -n 3 $D/DRIVER.log
