/-
AxiomAuditZetaQ.lean — the HONEST completion measure for the ZetaQ skeleton.

WHY THIS EXISTS
---------------
`lake build` emits one `declaration uses 'sorry'` warning per declaration whose OWN body
contains a `sorry`. That warning does **not** propagate: a theorem proved cleanly but citing
a still-`sorry` lemma produces no warning at all. So counting warnings UNDERSTATES the debt,
sometimes badly — in `ZetaQ/CharSums.lean` at the time of writing, 6 declarations warn while
a further 17 are conditional on them.

The kernel does not have that blind spot. A declaration is genuinely complete iff `sorryAx`
is absent from the transitive closure of its proof term. That is also exactly the standard
[R]'s own artifact is held to (`comparator/PrintAxioms/`), and the standard this one must
meet at M8: sorry-free plus `#print axioms` reporting only
`propext, Classical.choice, Quot.sound`.

This file walks every declaration in the `ZetaQ` namespace and partitions them:

  CLEAN       — closure has no `sorryAx`: genuinely proved, at [R]'s axiom profile.
  SORRY_OWN   — the declaration's own body has a `sorry`.
  SORRY_DEP   — body is sorry-free, but the closure reaches a `sorry` elsewhere.
                THIS is the population the warning count misses.

Run (from `zeta-23-lean/`, AFTER `lake build ZetaQ`):
    lake env lean audit/AxiomAuditZetaQ.lean
-/
import ZetaQ
import Lean

open Lean Elab Command


/-- Does this declaration's OWN body mention `sorryAx`? -/
def ownSorry (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci =>
    match ci.value? with
    | some v => v.getUsedConstants.any (· == ``sorryAx)
    | none => false
  | none => false

/-- The file a declaration came from, as a short tag like `CharSums`. -/
def fileTag (env : Environment) (n : Name) : String :=
  match env.getModuleFor? n with
  | some m =>
    let s := m.toString
    if "ZetaQ.".isPrefixOf s then (s.drop 6).toString else s
  | none => "?"

def isInteresting (env : Environment) (n : Name) : Bool :=
  Name.isPrefixOf `ZetaQ n && !n.isInternal &&
    (match env.find? n with
     | some (.thmInfo _) | some (.defnInfo _) => true
     | _ => false)

/-- Uses `Lean.collectAxioms` — the very function `#print axioms` runs — rather than a
hand-rolled closure walk. An earlier version of this file reimplemented the walk and
UNDER-reported badly (2 sorries against a true ~100), which is exactly the failure mode
this audit exists to catch. Trust the kernel's own implementation. -/
def auditMain : CommandElabM Unit := do
  let env ← getEnv
  let mut clean := 0
  let mut ownS := 0
  let mut depS := 0
  let mut perFile : Std.HashMap String (Nat × Nat × Nat) := {}
  let mut depList : Array Name := #[]
  for (n, _) in env.constants.toList do
    if !isInteresting env n then continue
    let ax ← liftCoreM <| collectAxioms n
    let hasSorry := ax.any (· == ``sorryAx)
    let own := ownSorry env n
    let tag := fileTag env n
    let (a, b, c) := perFile.getD tag (0, 0, 0)
    if !hasSorry then
      clean := clean + 1
      perFile := perFile.insert tag (a + 1, b, c)
    else if own then
      ownS := ownS + 1
      perFile := perFile.insert tag (a, b + 1, c)
    else
      depS := depS + 1
      depList := depList.push n
      perFile := perFile.insert tag (a, b, c + 1)
  logInfo m!"== ZetaQ axiom audit (via Lean.collectAxioms) =="
  logInfo m!"CLEAN      (no sorryAx in closure) : {clean}"
  logInfo m!"SORRY_OWN  (own body has a sorry)  : {ownS}"
  logInfo m!"SORRY_DEP  (cites one, no warning) : {depS}"
  logInfo m!"TOTAL ZetaQ declarations           : {clean + ownS + depS}"
  logInfo m!""
  logInfo m!"per file  CLEAN / SORRY_OWN / SORRY_DEP"
  for (k, (a, b, c)) in perFile.toList do
    logInfo m!"  {k}: {a} / {b} / {c}"

#eval auditMain
