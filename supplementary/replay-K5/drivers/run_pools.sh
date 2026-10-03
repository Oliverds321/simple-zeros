#!/usr/bin/env bash
# run_pools.sh — wrapper: runs the memory-aware two-pool replay driver run_pools.py in the foreground (L1_1e).
# All options are passed through; see the docstring of run_pools.py (python run_pools.py --help).
R="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python "$R/run_pools.py" --bash "$(cygpath -w "$(command -v bash)")" "$@"
