#!/usr/bin/env bash
# run_replay.sh — kernel replay of the K = 5 all-marks certificate against the GREEN library (L1_1e, 28 Sep 2026).
#
# Usage: run_replay.sh [--class <c>]... [--jobs N] [--allow-4] [--budget SECONDS] [--top] [--olean DIR] [--reset]
#   --class <c>   replay only class <c> (repeatable). Default: all 20 classes, then the top files.
#   --jobs N      files compiled at the same time (default 2). N > 2 needs --allow-4 (max 4); every leaf file peaks at
#                 about 3.3 GB, so 4 jobs need about 14 GB free and occupy all 4 leanrun slots (provers then wait).
#   --budget S    launch no new file after S seconds; exit code 3 (budget reached). Call again to resume.
#   --top         also compile common/ReplayAM5.lean and common/ReplayHeadlines.lean (needs all 20 classes).
#   --olean DIR   olean directory of the replay's OWN modules (default replay/olean_lib). It must hold nothing else:
#                 the checker, the specification, the C-nodes and the chain come from the green tree only
#                 (ZetaS.Cert.*; the shards' `import CheckerCoreV3` resolves to green's forwarder module).
#   --reset       delete every .olean in DIR and start afresh (needed after green or the replay sources changed).
#
# Guard against stale oleans: DIR/REPLAY_STAMP records green's commit (git HEAD of the green tree) and the sha256 of the
# manifest of all replay sources (replay/MANIFEST.sha256, format of `sha256sum -b`). The driver REFUSES to resume
# (exit 4) when DIR holds oleans and the stamp differs from the current state; use --reset then. It also stops (exit 5)
# when green's commit changes during a run (an integrator flip); the next start then refuses until --reset.
# Order: ReplayCommon; per class: Data + Pts* (parallel) -> Cells -> Leaves* (parallel) -> Assembly -> Cert.
# Within one stamp, a file is skipped when its olean exists and is newer than its source. Each file is compiled to
# <module>.olean.part and renamed on success, so an interrupted run leaves no stale olean (the .part is deleted at start).
# Log: replay/replay.log, one line per compiled file (time, module, exit code, elapsed, peak memory).
# Stops on the first failure (lean's output in replay/errors_<module>.txt). Per-class summary: replay/<c>/SUMMARY.txt.
# Exit codes: 0 done; 1 a file failed; 2 usage/setup error; 3 budget reached; 4 stale oleans (use --reset);
#             5 green changed during the run.
# The driver runs in the foreground of its caller; its only children are leanrun.sh processes, which it waits for.
set -u
R="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOOLS="$(cd "$R/../../../lean_tools" && pwd)"
GREEN="${LEANRUN_TREE:?set LEANRUN_TREE to your zeta-23-lean checkout path (e.g. export LEANRUN_TREE=/path/to/zeta-23-lean)}"
LOG="$R/replay.log"
ALL=(11111 11112 11121 11122 11211 11212 11221 11222 12112 12121 12122 12212 12221 12222 21112 21122 21212 21222 22122 22222)
CLASSES=(); JOBS=2; ALLOW4=0; BUDGET=0; TOP=0; O="$R/olean_lib"; RESET=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --class) CLASSES+=("$2"); shift 2 ;;
    --jobs) JOBS="$2"; shift 2 ;;
    --allow-4) ALLOW4=1; shift ;;
    --budget) BUDGET="$2"; shift 2 ;;
    --top) TOP=1; shift ;;
    --olean) O="$2"; shift 2 ;;
    --reset) RESET=1; shift ;;
    *) echo "unknown option $1"; exit 2 ;;
  esac
done
if (( ALLOW4 )); then (( JOBS > 4 )) && JOBS=4; else (( JOBS > 2 )) && JOBS=2; fi
(( JOBS < 1 )) && JOBS=1
if [[ ${#CLASSES[@]} -eq 0 ]]; then CLASSES=("${ALL[@]}"); TOP=1; fi
mkdir -p "$O"

# ---- guard: green commit + manifest of the replay sources
green_head() { git -C "$GREEN" rev-parse HEAD 2>/dev/null; }
make_manifest() {
  ( cd "$R" && find ./[12]* ./common -name '*.lean' | LC_ALL=C sort | xargs sha256sum -b ) > "$R/MANIFEST.sha256"
}
HEAD0="$(green_head)"; [[ -n "$HEAD0" ]] || { echo "cannot read green's commit in $GREEN"; exit 2; }
make_manifest
MSHA="$(sha256sum "$R/MANIFEST.sha256" | cut -c1-64)"
STAMP="green=$HEAD0 manifest=$MSHA"
for bad in CheckerBase CheckerLeaves CheckerCoreV3 CertSpecAM5 NodeDefs ChainV3 ChallengeZetaS Interfaces; do
  [[ -f "$O/$bad.olean" ]] && { echo "refusing: $O/$bad.olean is a private copy of a library module; delete it"; exit 2; }
done
rm -f "$O"/*.olean.part          # leftovers of an interrupted run
if (( RESET )); then rm -f "$O"/*.olean "$O"/*.ilean "$O/REPLAY_STAMP"; echo "reset: $O emptied"; fi
if ls "$O"/*.olean >/dev/null 2>&1; then
  if [[ "$(cat "$O/REPLAY_STAMP" 2>/dev/null)" != "$STAMP" ]]; then
    echo "refusing to resume: $O holds oleans built under a different state"
    echo "  stamp in dir : $(cat "$O/REPLAY_STAMP" 2>/dev/null || echo none)"
    echo "  current      : $STAMP"
    echo "  -> run again with --reset (deletes the oleans of this directory)"
    exit 4
  fi
else
  echo "$STAMP" > "$O/REPLAY_STAMP"
fi
echo "$(date +%H:%M:%S) START jobs=$JOBS classes=${CLASSES[*]} top=$TOP $STAMP" >> "$LOG"
T0=$(date +%s); STOP=0

compile() {  # $1 = source file
  local f="$1" m ol out ec line el pm
  m="$(basename "$f" .lean)"; ol="$O/$m.olean"
  if [[ -f "$ol" && "$ol" -nt "$f" ]]; then return 0; fi
  # compile to <module>.olean.part and rename only on success: an interrupted file never leaves a newer-looking olean
  out="$(LEANRUN_OWNER=L1_1-replay LEANRUN_TIMEOUT=540 bash "$TOOLS/leanrun.sh" "$f" "$O" -- -o "$ol.part" 2>&1)"; ec=$?
  if [[ $ec -eq 0 ]]; then mv -f "$ol.part" "$ol" || ec=1; else rm -f "$ol.part"; fi
  line="$(echo "$out" | grep 'leanrun:' | tail -1)"
  el="$(echo "$line" | grep -o 'elapsed=[0-9.]*s')"; pm="$(echo "$line" | grep -o 'peak_mem=[0-9]*MB')"
  if [[ $ec -ne 0 ]]; then rm -f "$ol" "${ol%.olean}.ilean"; echo "$out" | grep -v 'declaration uses' > "$R/errors_$m.txt"; fi
  printf '%s %s exit=%s %s %s\n' "$(date +%H:%M:%S)" "$m" "$ec" "$el" "$pm" >> "$LOG"
  return $ec
}

wave() {  # at most JOBS at a time; returns 1 on a failure, 3 if the budget stopped it, 5 if green changed
  local f failed=0
  for f in "$@"; do
    if (( BUDGET > 0 && $(date +%s) - T0 >= BUDGET )); then STOP=1; break; fi
    while (( $(jobs -rp | wc -l) >= JOBS )); do wait -n || failed=1; done
    (( failed )) && break
    compile "$f" &
  done
  while (( $(jobs -rp | wc -l) > 0 )); do wait -n || failed=1; done
  (( failed )) && return 1
  [[ "$(green_head)" == "$HEAD0" ]] || return 5
  (( STOP )) && return 3
  return 0
}

summary() {  # $1 = class
  local c="$1" k
  awk -v p="R${c}_" '$2 ~ "^"p { last[$2]=$0 } END { n=0; t=0; mx=0; bad=0;
      for (k in last) { split(last[k], a, " "); n++; e=a[4]; sub("elapsed=","",e); sub("s","",e); t+=e;
        pmv=a[5]; sub("peak_mem=","",pmv); sub("MB","",pmv); if (pmv+0>mx) mx=pmv+0; if (a[3]!="exit=0") bad++ }
      printf "class %s: files compiled %d, failed %d, total leanrun time %.0f s, max peak %d MB\n", p, n, bad, t, mx }' \
      "$LOG" > "$R/$c/SUMMARY.txt"
  for k in Data Pts Cells Leaves Assembly Cert; do
    awk -v p="R${c}_${k}" '$2 ~ "^"p { last[$2]=$0 } END { n=0; t=0; mx=0; for (x in last) { split(last[x], a, " "); n++;
        e=a[4]; sub("elapsed=","",e); sub("s","",e); t+=e; pmv=a[5]; sub("peak_mem=","",pmv); sub("MB","",pmv); if (pmv+0>mx) mx=pmv+0 }
        if (n) printf "  %-9s files %3d  time %7.1f s  mean %6.1f s  max peak %5d MB\n", substr(p, 8), n, t, t/n, mx }' "$LOG" >> "$R/$c/SUMMARY.txt"
  done
  cat "$R/$c/SUMMARY.txt"
}

finish() {
  echo "$(date +%H:%M:%S) STOP code=$1 after $(( $(date +%s) - T0 )) s" >> "$LOG"
  echo "replay: stopped with code $1 after $(( $(date +%s) - T0 )) s (log: $LOG)"; exit "$1"; }

JOBS_SAVE=$JOBS; JOBS=1
wave "$R/common/ReplayCommon.lean"; rc=$?; (( rc )) && finish $rc
JOBS=$JOBS_SAVE

for c in "${CLASSES[@]}"; do
  D="$R/$c"; [[ -d "$D" ]] || { echo "no directory $D"; finish 2; }
  wave "$D/R${c}_Data.lean" $(ls "$D"/R${c}_Pts*.lean | sort -V); rc=$?; (( rc )) && { summary "$c"; finish $rc; }
  wave "$D/R${c}_Cells.lean"; rc=$?; (( rc )) && { summary "$c"; finish $rc; }
  wave $(ls "$D"/R${c}_Leaves*.lean | sort -V); rc=$?; (( rc )) && { summary "$c"; finish $rc; }
  wave "$D/R${c}_Assembly.lean"; rc=$?; (( rc )) && { summary "$c"; finish $rc; }
  wave "$D/R${c}_Cert.lean"; rc=$?; (( rc )) && { summary "$c"; finish $rc; }
  summary "$c"
done
if (( TOP )); then
  JOBS=1
  wave "$R/common/ReplayAM5.lean" "$R/common/ReplayHeadlines.lean"; rc=$?; (( rc )) && finish $rc
fi
finish 0
