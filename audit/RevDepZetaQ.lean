/-
RevDepZetaQ.lean — Rule-17 / reverse-dependency audit of the ZetaQ tree (proof-term walker).

The `sorries` list is the four sorry-carrying declarations (`l2_concentration_exists`, `trace_row`,
`frobenius_row`, `assembly_at_lamStar`); `newDecls` are the headline theorems and the declarations
whose independence of the frozen three is the thing being checked. Imports the whole `ZetaQ` library.

Run (from `zeta-23-lean/`, AFTER `lake build ZetaQ`):
    lake env lean audit/RevDepZetaQ.lean
-/
import ZetaQ
import Lean

open Lean

/-- **The fix.** `ConstantInfo.value?` returns `none` for `thmInfo` at this Lean version, so
any audit built on it walks TYPES ONLY for theorems. Reading the field directly works. -/
def realValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def directDeps (env : Environment) (n : Name) : NameSet := Id.run do
  let mut used : NameSet := {}
  match env.find? n with
  | none => return used
  | some ci =>
    used := ci.type.getUsedConstants.foldl (·.insert ·) used
    if let some v := realValue? ci then
      used := v.getUsedConstants.foldl (·.insert ·) used
    return used

partial def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  while h : stack ≠ [] do
    let n := stack.head h
    stack := stack.tail
    if visited.contains n then continue
    visited := visited.insert n
    for u in (directDeps env n).toList do
      if !visited.contains u then stack := u :: stack
  return visited

def gatedTargets : List Name := [
  `Zeta23.Params.Valid.lam_le_one, `Zeta23.Params.Valid.one_le_w, `Zeta23.D0,
  `Zeta23.Params.Valid.rec, `Zeta23.Params.Valid.casesOn ]

def nameQualifies (env : Environment) (n : Name) : Bool :=
  (n.toString.endsWith ".lam_le_one" || n.toString.endsWith ".one_le_w")
  && n != `Zeta23.Params.Valid.lam_le_one && n != `Zeta23.Params.Valid.one_le_w
  && (env.find? n).isSome

/-- the four sorry-carrying declarations of the current tree -/
def sorries : List Name := [
  `ZetaQ.l2_concentration_exists,
  `ZetaQ.trace_row, `ZetaQ.frobenius_row, `ZetaQ.assembly_at_lamStar ]

/-- the headline theorems, and the declarations whose independence of the frozen three matters -/
def newDecls : List Name := [
  `ZetaQ.JoinProved.theorem_one_generic_proved', `ZetaQ.JoinProved.corollary_two_dyadic_proved',
  `ZetaQ.JoinProved.theorem_one_generic_proved, `ZetaQ.JoinProved.corollary_two_dyadic_proved,
  `ZetaQ.HFrob.hfrob_qle_of_sep, `ZetaQ.HFrob.hfrob_dyadic_of_sep,
  `ZetaQ.HFrob.hsep_of_design, `ZetaQ.HFrob.hsep_of_design_dyadic,
  `ZetaQ.JoinProved.hfrob_dyadic_of_design, `ZetaQ.Margin.hfrob_dyadic_of_designM,
  `ZetaQ.FrobAssembly.zone_compare_eventually_of_data, `ZetaQ.ZoneData.zoneLipschitzData_dyadic,
  `ZetaQ.rowR2_nonneg, `ZetaQ.HPre.rowR2_le_of_facts, `ZetaQ.budgetTotal_isBigO,
  `ZetaQ.Ends.ends_relative_le, `ZetaQ.Ends.endsRowConstC_four_le,
  `ZetaQ.rowR1_NfamQ_lower_dyadic, `ZetaQ.conductorShift_dyadic_bounds,
  `ZetaQ.conductorShift_dyadic_err, `ZetaQ.famRvMLower_dyadic_of_design,
  `ZetaQ.trace_row_eventually ]

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  -- sanity: the fix actually changes what we see
  let probe := directDeps env `ZetaQ.Ends.largeSieve_holds
  IO.println s!"SANITY (proof-only dep visible): {probe.contains `ZetaQ.multiplicative_large_sieve}"
  let mut zq : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (`ZetaQ).isPrefixOf n && !n.isInternal then zq := zq.push n
  IO.println s!"ZetaQ declarations scanned: {zq.size}"
  IO.println "\n== REVERSE DEPENDENCIES OF EVERY SORRIED STATEMENT (direct consumers) =="
  for t in sorries do
    if (env.find? t).isNone then IO.println s!"!! MISSING {t}" else
    let mut cons : Array Name := #[]
    for d in zq do
      if d == t then continue
      if (directDeps env d).contains t then cons := cons.push d
    IO.println s!"{t}  -->  {if cons.isEmpty then "NO CONSUMERS" else toString cons.toList}"
  IO.println "\n== RULE 17 (proof-term closure, FIXED WALKER) + which sorries each closure reaches =="
  for d in newDecls do
    if (env.find? d).isNone then IO.println s!"!! MISSING {d}" else
    let clo := closureOf env d
    let hits := gatedTargets.filter clo.contains
    let others := clo.toList.filter (nameQualifies env)
    let reached := sorries.filter clo.contains
    IO.println s!"{d}: closure {clo.size}, gated {if hits.isEmpty then "NONE" else toString hits}, other λ/w {if others.isEmpty then "NONE" else toString others}, sorries reached {if reached.isEmpty then "NONE" else toString reached}"
