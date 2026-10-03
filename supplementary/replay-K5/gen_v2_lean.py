"""Emit Lean shard files for a v2 certificate (CheckerV2.lean format).

  python gen_v2_lean.py PATTERN SUBTREE_NODES_MIN SUBTREE_NODES_MAX TAG      -> one subtree (measurement)
  python gen_v2_lean.py PATTERN all 0 TAG [--leaves-per-shard N]              -> full shard layout (not run)

Output (in ./shards/<TAG>/):
  <TAG>_Pts<k>.lean   KPt records (`def P<i> : KPt := ⟨x, k0, k1, k2, by decide +kernel⟩`), <= RECS per file
  <TAG>_Cells.lean    Cell records (each refers to the KPt at the cell centre)
  <TAG>_Tree<k>.lean  subtree definitions + `theorem ... : Node.check D T box = true := by decide +kernel`
  <TAG>_Data.lean     the instance D (LIQ) of the class
"""
import sys, os, json
from fractions import Fraction as Fr
sys.argv_save = list(sys.argv); sys.argv = ['x']
import proto_v2 as v2
import proto_cert as pc
sys.argv = sys.argv_save
v2.setup(5)
pat = sys.argv[1]; mode = sys.argv[2]; TAG = sys.argv[4]
LPS = int(sys.argv[sys.argv.index('--leaves-per-shard') + 1]) if '--leaves-per-shard' in sys.argv else 400
RECS = 400
js = json.load(open(f'v2_K5_{pat}.json'))
tree = js['tree']; root = [(Fr(a), Fr(b)) for a, b in js['root']]
gam, mu, claim = pc.load(pat)

boxes = []; pos = 0; stack = [([a for a, _ in root], [b for _, b in root])]
while stack:
    lo, hi = stack.pop(); n = tree[pos]; boxes.append((lo, hi)); pos += 1
    if n[0] == 'S':
        ax = n[1]; m = (lo[ax] + hi[ax])/2; hi1 = hi[:]; hi1[ax] = m; lo2 = lo[:]; lo2[ax] = m
        stack.append((lo2, hi)); stack.append((lo, hi1))
end = [0]*len(tree)
sys.setrecursionlimit(1000000)
def sub_end(i):
    if tree[i][0] != 'S': end[i] = i + 1; return i + 1
    j = sub_end(i + 1); k = sub_end(j); end[i] = k; return k
sub_end(0)

def q(x):
    x = Fr(x); return f'({x.numerator}/{x.denominator})' if x.denominator != 1 else f'({x.numerator})'
def qi(I): return f'⟨{q(I.lo)},{q(I.hi)}⟩'
def lst(v): return '[' + ','.join(q(t) for t in v) + ']'

pts = {}; cells = {}
def P(x):
    if x not in pts: pts[x] = len(pts)
    return f'P{pts[x]}'
def Cn(n):
    if n not in cells: cells[n] = True; P((n + Fr(1, 2))*v2.CW)
    return f'C{n}'.replace('-', 'm')

DUMMY = Fr(0)
def spand(lo, hi, gh, i, sl, need_ab, yy=None):
    c = [(a + b)/2 for a, b in zip(lo, hi)]; h = [(b - a)/2 for a, b in zip(lo, hi)]
    x0 = sum(c[i:i+sl]); r = sum(h[i:i+sl]); xh = sum(gh[i:i+sl])
    if yy is not None and not any(yy[1:]):          # LP span with no active line: dummy records, no cells
        d = P(DUMMY); return f'⟨{d},{d},{d},{d},[]⟩'
    cr = v2.cell_range(x0, r)
    cl = '[' + ','.join(Cn(n) for n in range(*cr)) + ']' if cr else '[]'
    ph = P(xh) if (yy is None or yy[3]) else P(x0)
    use_ab = need_ab and (yy is None or yy[4])
    pa = P(x0 - r) if use_ab else P(x0); pb = P(x0 + r) if use_ab else P(x0)
    return f'⟨{P(x0)},{ph},{pa},{pb},{cl}⟩'

def leaf_term(i):
    n = tree[i]; lo, hi = boxes[i]
    if n[0] == 'A': return 'Leaf.cap'
    gh = [Fr(v, 1 << 40) for v in n[1]]
    ys = [Fr(v, 1 << 30) for v in n[2]] if n[0] == 'M' else None
    sds = '[' + ','.join(spand(lo, hi, gh, a, s, n[0] == 'M', ys[5*j:5*j+5] if ys else None) for j, (a, s) in enumerate(v2.SP)) + ']'
    if n[0] == 'C': return f'Leaf.convex {lst(gh)} {sds}'
    return f'Leaf.lp {lst(gh)} {lst([Fr(v, 1 << 30) for v in n[2]])} {sds}'

def node_term(i):
    n = tree[i]
    if n[0] != 'S': return f'(Node.leaf ({leaf_term(i)}))'
    j = i + 1; return f'(Node.split {n[1]} {node_term(j)} {node_term(end[j])})'

def box_term(i):
    lo, hi = boxes[i]; return '[' + ','.join(f'({q(a)},{q(b)})' for a, b in zip(lo, hi)) + ']'

# choose subtrees
if mode == 'all':
    # greedy frontier: descend until subtrees have <= LPS leaves
    def nleaves(i): return sum(1 for t in tree[i:end[i]] if t[0] != 'S')
    front = []; st = [0]
    while st:
        i = st.pop()
        if nleaves(i) <= LPS or tree[i][0] != 'S': front.append(i)
        else: st.append(end[i + 1]); st.append(i + 1)
    roots = sorted(front)
else:
    lo_n, hi_n = int(mode), int(sys.argv[3])
    roots = [next(i for i in range(len(tree)) if tree[i][0] == 'S' and lo_n <= end[i] - i <= hi_n)]

outdir = os.environ.get('OUTDIR') or f'shards/{TAG}'; os.makedirs(outdir, exist_ok=True)
NSWRAP = os.environ.get('NSWRAP') == '1'
def wr(path, text):
    # NSWRAP=1: every declaration of a class lives in namespace ZetaS.CertV2.<TAG> (unique names across classes)
    if NSWRAP:
        NL1 = chr(10)
        text = text.replace('namespace ZetaS.CertV2' + NL1, 'namespace ZetaS.CertV2' + NL1 + f'namespace {TAG}' + NL1, 1)
        k = text.rindex('end ZetaS.CertV2'); text = text[:k] + f'end {TAG}' + NL1 + text[k:]
    open(path, 'w', encoding='utf-8').write(text)
hdr = 'import CheckerCoreV3\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace ZetaS.CertV2\n\n'
trees = []
for k, i in enumerate(roots):
    t = node_term(i)
    trees.append((k, i, t))
# data file
spans = ','.join(f'({a},{s},{q(gam[j])})' for j, (a, s) in enumerate(v2.SP))
wr(f'{outdir}/{TAG}_Data.lean', 
    hdr + f'def D_{TAG} : LIQ := ⟨4, [{spans}], {lst(mu)}, {q(claim)}⟩\n\nend ZetaS.CertV2\n')
# point records
items = sorted(pts.items(), key=lambda t: t[1])
npf = 0
for s0 in range(0, len(items), RECS):
    body = hdr
    for x, idx in items[s0:s0 + RECS]:
        k0, k1, k2 = v2.kpt(x)
        body += f'def P{idx} : KPt := ⟨{q(x)},{qi(k0)},{qi(k1)},{qi(k2)},by decide +kernel⟩\n'
    wr(f'{outdir}/{TAG}_Pts{npf}.lean', body + '\nend ZetaS.CertV2\n'); npf += 1
# cells (import all point files)
imp = ''.join(f'import {TAG}_Pts{k}\n' for k in range(npf))
body = hdr.replace('import CheckerCoreV3\n', imp)
for n in sorted(cells):
    plo, phi, wlo = v2.cell(n)
    body += f'def {Cn(n)} : Cell := ⟨{n},P{pts[(n + Fr(1, 2))*v2.CW]},{q(plo)},{q(phi)},{q(wlo)},by decide +kernel⟩\n'
wr(f'{outdir}/{TAG}_Cells.lean', body + '\nend ZetaS.CertV2\n')
# trees: one theorem per leaf (kernel caches are per declaration, so memory is bounded by one leaf),
# leaves split into files of <= LEAFFILE leaves; assembly file proves the split nodes by Node.check_split_of.
LEAFFILE = int(os.environ.get('LEAFFILE', '150'))
NL = chr(10)
leafs = []; splits = []
def walk(i):
    if tree[i][0] != 'S': leafs.append(i); return
    walk(i + 1); walk(end[i + 1]); splits.append(i)
for k, i, t in trees: walk(i)
nlf = 0
for s0 in range(0, len(leafs), LEAFFILE):
    body = hdr.replace('import CheckerCoreV3' + NL, f'import {TAG}_Data' + NL + f'import {TAG}_Cells' + NL)
    for i in leafs[s0:s0 + LEAFFILE]:
        body += f'def L{i} : Leaf := {leaf_term(i)}' + NL
        body += f'theorem L{i}_ok : Leaf.check D_{TAG} {box_term(i)} L{i} = true := by decide +kernel' + NL + NL
    wr(f'{outdir}/{TAG}_Leaves{nlf}.lean', body + 'end ZetaS.CertV2' + NL); nlf += 1
body = hdr.replace('import CheckerCoreV3' + NL, ''.join(f'import {TAG}_Leaves{k}' + NL for k in range(nlf)))
for i in sorted(set(leafs) | set(splits), reverse=True):
    if tree[i][0] != 'S':
        body += f'def T{i} : Node := Node.leaf L{i}' + NL
        body += f'theorem T{i}_ok : Node.check D_{TAG} T{i} {box_term(i)} = true := Node.check_leaf_of _ _ _ L{i}_ok' + NL
    else:
        j = i + 1; k2 = end[j]
        body += f'def T{i} : Node := Node.split {tree[i][1]} T{j} T{k2}' + NL
        body += (f'theorem T{i}_ok : Node.check D_{TAG} T{i} {box_term(i)} = true :=' + NL + '  Node.check_split_of _ _ _ _ _ _ _ '
                 f'(by decide +kernel) (by decide +kernel) T{j}_ok T{k2}_ok' + NL)
wr(f'{outdir}/{TAG}_Assembly.lean', body + NL + 'end ZetaS.CertV2' + NL)
print(f'{TAG}: leaf files {nlf}; subtrees {len(trees)} (roots {roots[:5]}...), leaves {sum(1 for i in roots for tt in tree[i:end[i]] if tt[0] != "S")}, '
      f'points {len(pts)} in {npf} files, cells {len(cells)}; sizes:',
      {f: os.path.getsize(f'{outdir}/{f}') for f in sorted(os.listdir(outdir))} if len(os.listdir(outdir)) < 12 else
      sum(os.path.getsize(f'{outdir}/{f}') for f in os.listdir(outdir)))
