#!/usr/bin/env python3
"""
Phase 1.1 (textual layer) — ParamsQ dependency-closure audit for H1–H6.

For each imported hypothesis H1–H6 (paper §2.1), compute the transitive
IMPORT closure of the file containing its proof, and produce the file:line
table of every textual use of the gated names:

    lam_le_one   (field of Params.Valid, Defs.lean)   — the λ ≤ 1 gate
    hlam1        (the hypothesis-name alias used at consumption sites)
    one_le_w     (field of Params.Valid)              — the w ≥ 1 gate (KEPT by ParamsQ)
    D0           (def D0 (T : ℝ) : ℝ := Real.sqrt T)  — the hard-coded buffer

This is the textual/import-graph layer of the receipt. It OVERSTATES
dependence (a file-level import pulls in a whole file, not the single lemma
used); the proof-term layer (Lean environment closure over compiled
oleans, script: DepAuditProofTerm.lean) refines it.

Usage: python3 depaudit_textual.py <path-to-zeta-23-lean> <out-dir>
"""
import os, re, sys, collections, json

_HERE = os.path.dirname(os.path.abspath(__file__))
TREE = sys.argv[1] if len(sys.argv) > 1 else os.path.join(_HERE, os.pardir)
OUT = sys.argv[2] if len(sys.argv) > 2 else os.path.join(_HERE, "depaudit_out")
os.makedirs(OUT, exist_ok=True)

# ---------------------------------------------------------------- H anchors
H = {
    "H1": {"desc": "rank-trace certificate (#simple-online >= 4trG - |G|F^2 - 2N - 3NII - loss)",
           "decls": ["ZeroConfig.count_certificate", "ZeroConfig.N0star_lower_moment",
                      "four_tr_sub_frobSq_perturb"],
           "files": ["Zeta23/Assembly/Certificate.lean", "Zeta23/Assembly.lean"]},
    "H2": {"desc": "Weil-form grid Gram identity Gz = Gp per primitive chi, no pole term",
           "decls": ["ZeroConfig.Gz_eq_GpChi", "ZeroConfig.summable_Gsummand_chi"],
           "files": ["Zeta23/ThmE/GzGpChi.lean"]},
    "H3": {"desc": "pointwise positivity g = phi^2 * phi^2 >= 0",
           "decls": ["AdmWindow.gv_nonneg"],
           "files": ["Zeta23/ThmD/WindowCore.lean"]},
    "H4": {"desc": "Gevrey-2 profile rho2, (A,B) = (36/e, 2e^8), + ramp lemma",
           "decls": ["gevreyProfile_rhoTwo", "integral_abs_iteratedDeriv_phi_le"],
           "files": ["Zeta23/Taper/Gevrey.lean", "Zeta23/Taper/GevreyRamps.lean"]},
    "H5": {"desc": "nu-generic ends majorants, cap-free _L forms with explicit constants",
           "decls": ["calE1_maj_bound_L", "calE2_maj_bound_L"],
           "files": ["Zeta23/PrimeSideA/EndsE1.lean", "Zeta23/PrimeSideA/EndsE2.lean"]},
    "H6": {"desc": "q-uniform local count N_chi(t,t+1] <= A0 log(q(|t|+3))",
           "decls": ["localCountChi_uniform_proof"],
           "files": ["Zeta23/ThmE/LocalCountChi.lean"]},
}

# ---------------------------------------------------------------- imports
imp_re = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([\w.«»]+)', re.M)

def mod_to_path(mod):
    if not mod.startswith("Zeta23"):
        return None  # externals (Mathlib etc.) carry no Params; out of scope here
    p = os.path.join(TREE, mod.replace(".", "/") + ".lean")
    return p if os.path.exists(p) else None

def path_to_mod(path):
    rel = os.path.relpath(path, TREE)
    return rel[:-5].replace("/", ".")

def imports_of(path):
    try:
        return imp_re.findall(open(path, encoding="utf-8").read())
    except Exception:
        return []

def closure_of_file(relfile):
    root = path_to_mod(os.path.join(TREE, relfile))
    seen, stack = set(), [root]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        p = mod_to_path(m)
        if p:
            stack.extend(x for x in imports_of(p) if x not in seen)
    return {m for m in seen if m.startswith("Zeta23")}

# ---------------------------------------------------------------- site scan
PATTERNS = {
    "lam_le_one": re.compile(r'lam_le_one'),
    "hlam1":      re.compile(r'\bhlam1\b'),
    "one_le_w":   re.compile(r'one_le_w'),
    "D0":         re.compile(r'\bD0\b|D₀'),
    "sqrt_T_inline": re.compile(r'Real\.sqrt\s+T\b'),
}

def classify(name, text):
    """Rough per-line classification for the Valid-field patterns."""
    t = text.strip()
    if re.match(rf'^{name}\s*:', t):
        return "field-decl"
    if re.match(rf'^{name}\s*:=', t):
        return "construction"
    if re.search(rf'\.{name}\b', t):
        return "projection-use"
    if t.startswith("--") or t.startswith("/-") or t.startswith("*"):
        return "comment"
    return "other"

sites = collections.defaultdict(list)   # pattern -> [(relfile, lineno, linetext)]
all_lean = []
for dirpath, _, files in os.walk(os.path.join(TREE, "Zeta23")):
    for f in sorted(files):
        if f.endswith(".lean"):
            all_lean.append(os.path.join(dirpath, f))
for extra in ["Zeta23.lean"]:
    p = os.path.join(TREE, extra)
    if os.path.exists(p):
        all_lean.append(p)

for path in sorted(all_lean):
    rel = os.path.relpath(path, TREE)
    for i, line in enumerate(open(path, encoding="utf-8"), 1):
        for name, rx in PATTERNS.items():
            if rx.search(line):
                sites[name].append((rel, i, line.rstrip()))

def module_bucket(relfile):
    parts = relfile.split("/")
    if len(parts) == 1:
        return parts[0].replace(".lean", "")
    if len(parts) == 2:
        return parts[1].replace(".lean", "")
    return parts[1]

# ---------------------------------------------------------------- report
md = []
md.append("# ParamsQ audit, Phase 1.1 — textual layer (machine-generated)")
md.append("")
md.append(f"Tree: `zeta-23-lean` as shipped in the handover kit (commit `3635e74` per README_KIT).")
md.append(f"Generator: `depaudit_textual.py` (this file's sibling); rerun to regenerate.")
md.append("Layer: TEXTUAL (grep + file-level import closure). The proof-term layer")
md.append("(compiled-environment closure) refines this after the M0 build and is the")
md.append("half that certifies; this half is the independently regenerable receipt of")
md.append("the site inventory. File-level closure OVERSTATES dependence.")
md.append("")

md.append("## A. Site inventory (whole tree)")
md.append("")
for name in ["lam_le_one", "hlam1", "one_le_w", "D0", "sqrt_T_inline"]:
    rows = sites[name]
    files = sorted({r[0] for r in rows})
    md.append(f"### `{name}` — {len(rows)} sites in {len(files)} files")
    md.append("")
    bucket = collections.Counter(module_bucket(r[0]) for r in rows)
    md.append("Per module: " + ", ".join(f"{k} {v}" for k, v in bucket.most_common()))
    md.append("")
    if name in ("lam_le_one", "one_le_w"):
        kinds = collections.Counter(classify(name, t) for _, _, t in rows)
        md.append("Per kind: " + ", ".join(f"{k} {v}" for k, v in kinds.most_common()))
        md.append("")
    md.append("| file | line | kind | text |")
    md.append("|---|---|---|---|")
    for rel, i, txt in rows:
        t = txt.strip().replace("|", "\\|")
        if len(t) > 100:
            t = t[:97] + "..."
        k = classify(name, txt) if name in ("lam_le_one", "one_le_w") else ""
        md.append(f"| {rel} | {i} | {k} | `{t}` |")
    md.append("")

md.append("## B. H1–H6: anchors and import closures")
md.append("")
closure_cache = {}
summary_rows = []
for h in ["H1", "H2", "H3", "H4", "H5", "H6"]:
    info = H[h]
    clo = set()
    for f in info["files"]:
        if f not in closure_cache:
            closure_cache[f] = closure_of_file(f)
        clo |= closure_cache[f]
    clo_files = sorted(m.replace(".", "/") + ".lean" for m in clo)
    md.append(f"### {h} — {info['desc']}")
    md.append("")
    md.append("Anchor declarations: " + ", ".join(f"`{d}`" for d in info["decls"]))
    md.append("")
    md.append("Anchor files: " + ", ".join(f"`{f}`" for f in info["files"]))
    md.append("")
    md.append(f"Import closure within Zeta23: {len(clo_files)} files.")
    hits = {}
    for name in ["lam_le_one", "hlam1", "one_le_w", "D0"]:
        hs = [(rel, i, t) for (rel, i, t) in sites[name] if rel in clo_files]
        hits[name] = hs
    md.append("")
    md.append("| gated name | sites inside closure | files |")
    md.append("|---|---|---|")
    for name in ["lam_le_one", "hlam1", "one_le_w", "D0"]:
        fs = sorted({r[0] for r in hits[name]})
        md.append(f"| `{name}` | {len(hits[name])} | {', '.join(fs) if fs else '—'} |")
    md.append("")
    summary_rows.append((h, {n: len(hits[n]) for n in hits}, len(clo_files)))

md.append("## C. Summary matrix (textual closure level)")
md.append("")
md.append("| H | closure size (files) | lam_le_one | hlam1 | one_le_w | D0 |")
md.append("|---|---|---|---|---|---|")
for h, hh, n in summary_rows:
    md.append(f"| {h} | {n} | {hh['lam_le_one']} | {hh['hlam1']} | {hh['one_le_w']} | {hh['D0']} |")
md.append("")

open(os.path.join(OUT, "PARAMSQ_AUDIT_TEXTUAL.md"), "w").write("\n".join(md))

# JSON sidecar for the proof-term pass to diff against
json.dump({
    "sites": {k: [(a, b) for a, b, _ in v] for k, v in sites.items()},
    "closures": {h: sorted(closure_cache_f for f in H[h]["files"] for closure_cache_f in
                           sorted(m for m in closure_cache[f])) for h in H},
    "anchors": {h: H[h]["decls"] for h in H},
}, open(os.path.join(OUT, "paramsq_audit_textual.json"), "w"), indent=1)

print("sites:", {k: len(v) for k, v in sites.items()})
print("closures:", [(h, n) for h, _, n in summary_rows])
print("written:", os.path.join(OUT, "PARAMSQ_AUDIT_TEXTUAL.md"))
