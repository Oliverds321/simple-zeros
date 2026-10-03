"""Merge one or more bnb_interval(_w).py checkpoints (same args) and split the union of their stacks into N shard
checkpoints (round-robin over boxes), so the remaining branch-and-bound runs as N independent processes, each resumed with
  bnb_interval_w.py ... --checkpoint <shard>.ckpt --resume
Soundness: the boxes on the parents' stacks, with the boxes already accepted/pruned, cover the domain; the shards
partition the union of the parents' stacks exactly (checked: sha256 of the sorted row multiset).  The certificate holds
iff every process ever launched on a shard returns ok=True or leaves a checkpoint that is merged again.
Stats: parents' stats are summed into shard 0 (others start at 0) so 'processed' adds up; worst = min over parents.
Usage: python shard_ckpt.py N out_prefix parent1.ckpt [parent2.ckpt ...]  -> out_prefix_r.ckpt (r < N), out_prefix.manifest.txt
(Oct 2026) Every check is an explicit test with exit status 1 (they hold under python -O as well): N a positive integer;
at least one parent; every parent present, readable, a checkpoint with the same args and the same objective identity
(bnb_lb3.py, objective_identity), and not given twice; no output file may exist already; the partition check. The
lines printed are those of before, plus a last line with the objective identity. This proves only that the shards
partition the parents given: that the parents are the complete set of a round is checked by s8_manifest.py (the run
manifest of mkinit.sh, round_lb3.sh and run_lb3_loop.sh), which calls shard() below."""
import sys, os, pickle, hashlib, numpy as np


class ShardError(Exception):
    """(Oct 2026) a refused input; the command line prints it and exits with status 1"""


def digest(st):
    if not st:
        return 'empty', 0
    rows = np.concatenate([np.hstack([C, H]) for C, H in st])
    rows = rows[np.lexsort(rows.T[::-1])]
    return hashlib.sha256(rows.tobytes()).hexdigest(), len(rows)


def load_checkpoint(fn):
    """(Oct 2026) read one checkpoint; returns (dict, sha256 of the file); ShardError if it is not a checkpoint"""
    try:
        with open(fn, 'rb') as f:
            raw = f.read()
    except OSError as e:
        raise ShardError(f"cannot read checkpoint {fn}: {e}")
    try:
        ck = pickle.loads(raw)
    except Exception as e:
        raise ShardError(f"{fn} is not a readable checkpoint ({type(e).__name__}: {e})")
    if not isinstance(ck, dict) or any(k not in ck for k in ('args', 'stack', 'stats', 'worst', 'time')):
        raise ShardError(f"{fn} is not a checkpoint (keys args, stack, stats, worst, time expected)")
    try:
        for C, H in ck['stack']:
            if not (isinstance(C, np.ndarray) and isinstance(H, np.ndarray) and C.ndim == 2 and C.shape == H.shape):
                raise ShardError(f"{fn}: malformed stack entry")
    except (TypeError, ValueError):
        raise ShardError(f"{fn}: malformed stack")
    return ck, hashlib.sha256(raw).hexdigest()


def boxes(ck):
    return sum(len(C) for C, H in ck['stack'])


def shard(N, pre, srcs):
    """(Oct 2026) Split the parents srcs into N shards pre_<r>.ckpt and write pre.manifest.txt; returns the printed
    lines and a summary. Raises ShardError, with nothing written, on a refused input."""
    if not isinstance(N, int) or isinstance(N, bool) or N < 1:
        raise ShardError(f"N must be a positive integer (got {N!r})")
    if not srcs:
        raise ShardError("no parent checkpoint given")
    real = [os.path.realpath(s) for s in srcs]
    if len(set(real)) != len(real):
        raise ShardError(f"a parent checkpoint is given twice: {srcs}")
    outs = [f"{pre}_{r}.ckpt" for r in range(N)] + [pre + '.manifest.txt']
    for fn in outs:
        if os.path.lexists(fn) or os.path.lexists(fn + '.tmp'):
            raise ShardError(f"output file {fn} exists already (refusing to overwrite)")
    loaded = [load_checkpoint(s) for s in srcs]
    cks = [c for c, h in loaded]
    seen = {}
    for s, (c, h) in zip(srcs, loaded):
        if boxes(c) and h in seen:
            raise ShardError(f"parents {seen[h]} and {s} are the same checkpoint (sha256 {h})")
        seen[h] = s
    args = cks[0]['args']
    for s, c in zip(srcs, cks):
        if c['args'] != args:
            raise ShardError(f"checkpoint args differ: {srcs[0]} has {args}, {s} has {c['args']}")
    ident = cks[0].get('identity')
    if ident is None:
        raise ShardError(f"{srcs[0]} has no objective identity (written by an older bnb_lb3.py?)")
    for s, c in zip(srcs, cks):
        if c.get('identity') != ident:
            raise ShardError(f"checkpoint objectives differ: {srcs[0]} has {ident}, {s} has {c.get('identity')}")
    stack = [b for c in cks for b in c['stack']]
    tot = sum(len(C) for C, H in stack)
    stats = {}
    for c in cks:
        for k, v in c['stats'].items():
            stats[k] = stats.get(k, 0) + v
    worst = min((c['worst'] for c in cks), key=lambda w: w[0])
    tsum = sum(c['time'] for c in cks)
    shards = [[] for _ in range(N)]
    off = 0
    for C, H in stack:
        idx = (np.arange(len(C)) + off) % N
        for r in range(N):
            sel = idx == r
            if sel.any():
                shards[r].append((C[sel].copy(), H[sel].copy()))
        off += len(C)
    dpar, dall = digest(stack), digest([b for s in shards for b in s])
    if dpar != dall:
        raise ShardError(f"shards do not partition the parents' stacks ({dpar} != {dall})")
    lines = [f"parents {srcs}: args={args} stack_boxes={tot} processed(sum)={stats.get('processed', 0):.4e} "
             f"cpu_time(sum)={tsum:.0f}s worst={worst[0]:.7f}",
             f"sha256(sorted rows): union of parents = union of shards = {dpar[0]} ({dpar[1]} rows)"]
    zero = {k: (0.0 if isinstance(v, float) else 0) for k, v in stats.items()}
    nbox = []
    for r in range(N):
        out = dict(args=args, identity=ident, stack=shards[r], stats=dict(stats) if r == 0 else dict(zero),
                   worst=worst, time=tsum if r == 0 else 0.0)
        fn = f"{pre}_{r}.ckpt"
        with open(fn + '.tmp', 'wb') as f:
            pickle.dump(out, f, protocol=4)
        os.replace(fn + '.tmp', fn)
        nbox.append(sum(len(C) for C, H in shards[r]))
        lines.append(f"shard {r}: {fn} boxes={nbox[-1]}")
    lines.append(f"objective: sha256={ident}")
    with open(pre + '.manifest.txt', 'w') as f:
        f.write('\n'.join(lines) + '\n')
    return lines, dict(args=args, identity=ident, rows_sha256=dpar[0], rows=dpar[1], files=outs[:-1], boxes=nbox,
                       parents=[dict(path=s, sha256=h, boxes=boxes(c)) for s, (c, h) in zip(srcs, loaded)],
                       text_manifest=outs[-1])


def main(argv):
    if len(argv) < 3:
        sys.exit("shard_ckpt.py: error: usage: python shard_ckpt.py N out_prefix parent1.ckpt [parent2.ckpt ...]")
    if not (argv[0].isascii() and argv[0].isdigit()):
        sys.exit(f"shard_ckpt.py: error: N must be a positive integer (got {argv[0]!r})")
    try:
        lines, _ = shard(int(argv[0]), argv[1], argv[2:])
    except ShardError as e:
        sys.exit(f"shard_ckpt.py: error: {e}")
    print('\n'.join(lines))


if __name__ == '__main__':
    main(sys.argv[1:])
