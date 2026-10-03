/-
DepAuditProofTerm.lean — Phase 1.1 (proof-term layer) — ParamsQ dependency-closure
audit for H1–H6.

For each anchor declaration of H1–H6 (paper §2.1), walk the TRANSITIVE closure of
constants reachable from its type AND value (proof term), and report:

  1. whether the gated projections `Zeta23.Params.Valid.lam_le_one` /
     `Zeta23.Params.Valid.one_le_w` are in the closure;
  2. whether the hard-coded buffer `Zeta23.D0` (:= Real.sqrt T) is in the closure;
  3. whether `Zeta23.Params.Valid` itself (or its recursor/casesOn — which would
     let a proof consume ALL fields by destructuring, invisible to projection
     search) is in the closure;
  4. every OTHER structure in the closure that carries its own λ ≤ 1 field
     (the local-hypothesis structures of PrimeSideA/Basic, ThmD/Traces,
     ThmDE/Traces, ThmE/TracesChi, PrimeSideB) — flagged by name;
  5. the closure size, as a sanity statistic.

This is decisive where grep is not: a proof that destructures `hP : P.Valid` never
mentions `lam_le_one` textually, but its closure then contains Valid's recursor;
conversely a file-level import closure flags whole files whose gated lemmas the
anchor never touches. This walker sees exactly what the kernel sees.

Run (from the zeta-23-lean project root, AFTER `lake build` is green):
  lake env lean audit/DepAuditProofTerm.lean
(or any path to this file; it only needs the Zeta23 oleans on LEAN_PATH).
-/
import Zeta23
import Lean

open Lean

/-- Names whose presence in a closure we report. -/
def gatedTargets : List Name := [
  `Zeta23.Params.Valid.lam_le_one,
  `Zeta23.Params.Valid.one_le_w,
  `Zeta23.D0,
  `Zeta23.Params.Valid,
  `Zeta23.Params.Valid.rec,
  `Zeta23.Params.Valid.casesOn,
  `Zeta23.Params.Valid.mk
]

/-- Substrings that mark OTHER λ-gate carriers (local hypothesis structures). -/
def lamFieldCarriers : List Name := [] -- filled dynamically: any constant whose
                                        -- name ends in `.lam_le_one` other than Params.Valid's

/-- Proof terms, actually. `ConstantInfo.value?` is `none` on `thmInfo` at this toolchain;
reading the structure field is what gives the proof term. -/
def realValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  while h : stack ≠ [] do
    let n := stack.head h
    stack := stack.tail
    if visited.contains n then
      continue
    visited := visited.insert n
    match env.find? n with
    | none => continue
    | some ci =>
      let mut used : NameSet := {}
      used := ci.type.getUsedConstants.foldl (·.insert ·) used
      -- ⚠ `ConstantInfo.value?` returns `none` for `thmInfo` at this Lean version, so the
      -- obvious spelling walks TYPES ONLY for theorems — which is exactly the case this
      -- audit exists to cover.  Read the field directly.
      if let some v := realValue? ci then
        used := v.getUsedConstants.foldl (·.insert ·) used
      for u in used.toList do
        if !visited.contains u then
          stack := u :: stack
  return visited

def anchors : List (String × List Name) := [
  ("H1 rank-trace certificate",
    [`Zeta23.Assembly.count_certificate,
     `Zeta23.Assembly.N0star_lower_moment,
     `Zeta23.Assembly.four_tr_sub_frobSq_perturb]),
  ("H2 Gz = Gp per primitive chi",
    [`Zeta23.ZeroConfig.Gz_eq_GpChi,
     `Zeta23.ZeroConfig.summable_Gsummand_chi]),
  ("H3 g >= 0",
    [`Zeta23.AdmWindow.gv_nonneg]),
  ("H4 Gevrey profile + ramp lemma",
    [`Zeta23.Taper.gevreyProfile_rhoTwo,
     `Zeta23.Taper.integral_abs_iteratedDeriv_phi_le]),
  ("H5 cap-free ends majorants",
    [`Zeta23.PrimeSide.calE1_maj_bound_L,
     `Zeta23.PrimeSide.calE2_maj_bound_L]),
  ("H6 q-uniform local count",
    [`Zeta23.ThmE.localCountChi_uniform_proof])
]

def nameQualifies (env : Environment) (n : Name) : Bool :=
  -- any `.lam_le_one` / `.one_le_w` projection from a structure OTHER than Params.Valid
  (n.toString.endsWith ".lam_le_one" || n.toString.endsWith ".one_le_w")
  && n != `Zeta23.Params.Valid.lam_le_one && n != `Zeta23.Params.Valid.one_le_w
  && (env.find? n).isSome

def resolveName (env : Environment) (n : Name) : Except String Name :=
  if (env.find? n).isSome then .ok n
  else .error s!"UNRESOLVED ANCHOR {n}"

unsafe def main : IO Unit := do
  -- load the Zeta23 environment via the import below (this file is #eval-driven instead)
  pure ()

-- We drive everything with #eval so `lake env lean` on this file both elaborates the
-- imports and prints the report.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  IO.println "== ParamsQ proof-term dependency audit =="
  for (label, decls) in anchors do
    for d in decls do
      match resolveName env d with
      | .error e => IO.println s!"!! {label}: {e}"
      | .ok n =>
        let clo := closureOf env n
        let hits := gatedTargets.filter clo.contains
        let others := clo.toList.filter (nameQualifies env)
        IO.println s!"{label} :: {n}"
        IO.println s!"  closure size: {clo.size}"
        IO.println s!"  gated hits  : {if hits.isEmpty then "NONE" else toString hits}"
        IO.println s!"  other λ/w-field structures in closure: {if others.isEmpty then "NONE" else toString others}"
  IO.println "== end audit =="
