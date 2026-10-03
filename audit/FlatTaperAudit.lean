import ZetaQ.Budget
import Lean
open Lean

/-! FlatTaperAudit — how much of `ZetaQ` cites flat-taper-specific facts of [R]?
Direct-dependency scan over every ZetaQ declaration (types + proof terms, via `realValue?`),
grouped by module, plus proof-closure intersections for the key theorems on Theorem 1's path. -/

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

/-- classification of an external name -/
def group (n : Name) : Option String :=
  let s := n.toString
  if s.startsWith "Zeta23.TaperProfile" || s.startsWith "Zeta23.Taper.GevreyProfile" || s.startsWith "Zeta23.GevreyProfile" then some "G2:profile-structure"
  else if s.startsWith "Zeta23.Taper." then some "G1:taper-facade"
  else if s == "Zeta23.Params.phi" || s == "Zeta23.Params.a" || s == "Zeta23.Params.b" || s == "Zeta23.Params.g"
       || s == "Zeta23.Params.Phi" || s == "Zeta23.Params.PhiR" || s == "Zeta23.Params.phiHat" || s == "Zeta23.Params.phiHatR"
       || s == "Zeta23.Params.Aphi" || s == "Zeta23.Params.crho" || s == "Zeta23.Params.psi" || s == "Zeta23.Params.autocorr"
       || s.startsWith "Zeta23.Params.GevreyPhiBound" then some "G3:params-window-objects"
  else if s.startsWith "Zeta23.Tail." then some "G4:tail"
  else if s.startsWith "Zeta23.AdmWindow" || s.startsWith "Zeta23.ThmD." then some "G5:admwindow/ThmD"
  else if s == "ZetaQ.ParamsQ.Valid.taper" then some "G6:ZetaQ.Valid.taper"
  else if s == "ZetaQ.ParamsQ.phiQ" || s == "ZetaQ.ParamsQ.PhiQ" || s == "ZetaQ.ParamsQ.gQ" || s == "ZetaQ.ParamsQ.aQ"
       || s == "ZetaQ.ParamsQ.phiHatQ" || s == "ZetaQ.ParamsQ.toParams" then some "G7:ZetaQ-window-objects"
  else none

def keyThms : List Name := [
  `ZetaQ.assembly_clauses_at_design, `ZetaQ.exists_designOfRecord, `ZetaQ.payoff_rate_of_assembly,
  `ZetaQ.trace_row_of_muPart, `ZetaQ.trGhatFam_eq_split, `ZetaQ.abs_trGhatFam_sub_muPart_le,
  `ZetaQ.lemma43_family_le_C_diagonal, `ZetaQ.lemma44_zone_boundary, `ZetaQ.lemma44_P_main, `ZetaQ.lemma44_R_bound,
  `ZetaQ.Zones.frobSq_gridGram_sub_Mform_le, `ZetaQ.frobSq_gridGram_sub_Mform_le,
  `ZetaQ.Mform_mu_PX_le, `ZetaQ.Mform_muDensity_eval_exists,
  `ZetaQ.Ends.ends_relative_le, `ZetaQ.Ends.S2_localHypsCoreW,
  `ZetaQ.EFChi.prop31_fam, `ZetaQ.exists_famTailInputsD, `ZetaQ.famRvMLower_of_design,
  `ZetaQ.theta0Fam_le_of_design, `ZetaQ.pair_absorbed_of_theta_small,
  `ZetaQ.multiplicative_large_sieve, `ZetaQ.theta0Q_le_theta0Fam, `ZetaQ.theta0Q_le_of_closing ]

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut zq : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (`ZetaQ).isPrefixOf n && !n.isInternal then zq := zq.push n
  IO.println s!"ZetaQ declarations scanned: {zq.size}"
  -- per-module, per-group counts of declarations DIRECTLY citing the group; global name frequency
  let mut perMod : Std.HashMap String (Std.HashMap String Nat) := {}
  let mut modTotal : Std.HashMap String Nat := {}
  let mut freq : Std.HashMap Name Nat := {}
  let mut eqOneUsers : Array Name := #[]
  for d in zq do
    let m := match env.getModuleFor? d with | some m => m.toString | none => "?"
    modTotal := modTotal.insert m (modTotal.getD m 0 + 1)
    let deps := directDeps env d
    let mut groupsHit : Std.HashSet String := {}
    for u in deps.toList do
      if let some g := group u then
        groupsHit := groupsHit.insert g
        freq := freq.insert u (freq.getD u 0 + 1)
      if u == `Zeta23.TaperProfile.eq_one || u == `Zeta23.TaperProfile.monotone || u == `Zeta23.TaperProfile.eq_zero then
        eqOneUsers := eqOneUsers.push d
    let row := perMod.getD m {}
    let mut row' := row
    for g in groupsHit.toList do
      row' := row'.insert g (row'.getD g 0 + 1)
    if !groupsHit.isEmpty then row' := row'.insert "ANY" (row'.getD "ANY" 0 + 1)
    perMod := perMod.insert m row'
  IO.println "\n== DIRECT CITATIONS, per module (declarations citing at least one name of the group) =="
  let groups := ["ANY","G1:taper-facade","G2:profile-structure","G3:params-window-objects","G4:tail","G5:admwindow/ThmD","G6:ZetaQ.Valid.taper","G7:ZetaQ-window-objects"]
  for (m, tot) in modTotal.toList do
    let row := perMod.getD m {}
    let cells := groups.map fun g => s!"{g}={row.getD g 0}"
    IO.println s!"{m}: total={tot} | {String.intercalate " " cells}"
  IO.println "\n== MOST-CITED EXTERNAL NAMES (G1/G2/G3/G4/G5), by number of ZetaQ declarations citing them directly =="
  let arr := freq.toArray.qsort (fun a b => a.2 > b.2)
  for (n, c) in arr[:70] do
    IO.println s!"{c}\t{n}"
  IO.println s!"\n== declarations directly using TaperProfile.eq_one/monotone/eq_zero: {eqOneUsers.size} =="
  for d in eqOneUsers[:40] do IO.println s!"  {d}"
  IO.println "\n== PROOF-CLOSURE intersections for key theorems (G1..G5 names in closure) =="
  for t in keyThms do
    if (env.find? t).isNone then IO.println s!"!! MISSING {t}" else
    let clo := closureOf env t
    let mut g1 : Nat := 0; let mut g2 : Nat := 0; let mut g3 : Nat := 0; let mut g4 : Nat := 0; let mut g5 : Nat := 0
    let mut g2names : Array Name := #[]
    for n in clo.toList do
      match group n with
      | some "G1:taper-facade" => g1 := g1 + 1
      | some "G2:profile-structure" => g2 := g2 + 1; g2names := g2names.push n
      | some "G3:params-window-objects" => g3 := g3 + 1
      | some "G4:tail" => g4 := g4 + 1
      | some "G5:admwindow/ThmD" => g5 := g5 + 1
      | _ => pure ()
    IO.println s!"{t}: closure={clo.size} taper-facade={g1} profile-structure={g2} params-window={g3} tail={g4} admwindow/ThmD={g5} | profile-structure names: {g2names.toList}"
