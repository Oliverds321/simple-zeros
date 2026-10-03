-- Census_release.lean (lead, 1-2 Oct 2026): census of every public theorem of the libraries `ZetaS` and `ZetaShell` in
-- the RELEASE tree (one line per theorem: module, declaration, level, axioms, number of sorry leaves, the leaves), then
-- `#sorry_leaves` and `#print axioms` of the headline declarations. The census code is L0_6's `CensusCmd.lean` with the
-- root filter widened to both libraries. Run by release_build.sh census (`lake env lean` in the release tree).
import ZetaS
import ZetaShell
import Lean
open Lean Elab Command

namespace Census

def skipRoots : List Name :=
  [`Init, `Lean, `Std, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible, `ImportGraph,
   `LeanSearchClient, `Zeta23, `Cli]

def ourRoots : List Name := [`ZetaS, `ZetaShell, `ZetaSCertShims]

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `_current

structure CState where
  ax : Std.HashMap Name (Array Name) := {}
  lv : Std.HashMap Name (Array Name) := {}

partial def axOf (env : Environment) (n : Name) : StateM CState (Array Name) := do
  if let some r := (← get).ax[n]? then return r
  modify fun s => { s with ax := s.ax.insert n #[] }
  let some ci := env.find? n | return #[]
  let mut acc : Array Name := #[]
  if let .axiomInfo _ := ci then acc := acc.push n
  for c in ci.getUsedConstantsAsSet.toList do
    for a in (← axOf env c) do
      unless acc.contains a do acc := acc.push a
  modify fun s => { s with ax := s.ax.insert n acc }
  return acc

partial def lvOf (env : Environment) (n : Name) : StateM CState (Array Name) := do
  if let some r := (← get).lv[n]? then return r
  modify fun s => { s with lv := s.lv.insert n #[] }
  if skipRoots.contains (modOf env n).getRoot then return #[]
  let some ci := env.find? n | return #[]
  let cs := ci.getUsedConstantsAsSet
  let mut acc : Array Name := if cs.contains ``sorryAx then #[n] else #[]
  for c in cs.toList do
    for a in (← lvOf env c) do
      unless acc.contains a do acc := acc.push a
  modify fun s => { s with lv := s.lv.insert n acc }
  return acc

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#zs_census " f:str : command => do
  let env ← getEnv
  let mut st : CState := {}
  let mut lines : Array String := #[]
  let mut nThm := 0
  for (n, ci) in env.constants.map₁.toList do
    let m := modOf env n
    unless ourRoots.contains m.getRoot do continue
    if n.isInternal then continue
    match ci with
    | .thmInfo _ =>
      let (ax, st1) := (axOf env n).run st
      let (lv, st2) := (lvOf env n).run st1
      st := st2
      nThm := nThm + 1
      let axs := (ax.map toString).qsort (fun a b => a < b)
      let level := if ax.contains ``sorryAx then "SORRY"
        else if ax.all (fun a => std3.contains a) then "A" else "OTHER"
      let lvs := lv.toList.map fun a => s!"{a} [{modOf env a}]"
      lines := lines.push s!"{m}\t{n}\t{level}\t{axs.toList}\t{lv.size}\t{lvs}"
    | _ =>
      if ci.getUsedConstantsAsSet.contains ``sorryAx then
        lines := lines.push s!"{m}\t{n}\tDEFSORRY\t-\t-\t-"
  let sorted := lines.qsort (fun a b => a < b)
  IO.FS.writeFile f.getString (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"census: {nThm} public theorems, {lines.size} lines written to {f.getString}"

def sorryLeaves (env : Environment) (root : Name) : Array (Name × Name) := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut out : Array (Name × Name) := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    let m := modOf env n
    if skipRoots.contains m.getRoot then continue
    match env.find? n with
    | none => pure ()
    | some ci =>
      let cs := ci.getUsedConstantsAsSet
      if cs.contains ``sorryAx then out := out.push (n, m)
      for c in cs.toList do
        unless visited.contains c do stack := stack.push c
  return out

elab "#sorry_leaves " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let n := id.getId
    unless env.contains n do
      logError m!"unknown constant {n}"
      continue
    let leaves := sorryLeaves env n
    let s := leaves.toList.map fun (a, b) => s!"{a} [{b}]"
    logInfo m!"SORRY-LEAVES {n} ({leaves.size}): {s}"

end Census

open Census

#zs_census "CENSUS_TSV"

-- ζ headlines (library ZetaS; the K = 5 pair's hypothesis-free forms live in ZetaSReplay and are censused separately)
#sorry_leaves ZetaS.Top.zeta_simple_K5_final ZetaS.Top.zeta_distinct_K5_final ZetaS.Top.zeta_simple_K7_final ZetaS.Top.zeta_distinct_K7_final ZetaS.Top.zeta_simple_on_line ZetaS.Top.zeta_simple_or_critical
#print axioms ZetaS.Top.zeta_simple_K5_final
#print axioms ZetaS.Top.zeta_distinct_K5_final
#print axioms ZetaS.Top.zeta_simple_K7_final
#print axioms ZetaS.Top.zeta_distinct_K7_final
#print axioms ZetaS.Top.zeta_simple_on_line
#print axioms ZetaS.Top.zeta_simple_or_critical

-- family (library ZetaShell)
#sorry_leaves ZetaShell.LemmaK.theorem_one_prime_design ZetaShell.certS53 ZetaShell.certD53 ZetaShell.PropZ.propZ_W ZetaShell.TrackF.lemma2a ZetaShell.Design.shell_frame_qle_of_nodes ZetaShell.LemmaK.theorem_one_prime ZetaShell.PropZ.Z5R_W ZetaShell.ShellK.F1c_chain ZetaShell.Design.shell_frame_qle_of_K ZetaShell.ShellK.frob_row_shell' ZetaShell.ShellS.shell_S ZetaShell.ShellK.thmK
#print axioms ZetaShell.LemmaK.theorem_one_prime_design
#print axioms ZetaShell.certS53
#print axioms ZetaShell.certD53
#print axioms ZetaShell.PropZ.propZ_W
#print axioms ZetaShell.TrackF.lemma2a
#print axioms ZetaShell.ShellK.F1c_chain
#print axioms ZetaShell.Design.shell_frame_qle_of_K
#print axioms ZetaShell.ShellS.shell_S
#print axioms ZetaShell.ShellK.thmK
-- the statement of record of the family main theorem and the nodes proved on 3 Oct 2026 (followup-trunk 49/n to 56/n)
#sorry_leaves ZetaShell.shell_S53_qle_reduced ZetaShell.Design.shell_frame_qle_of_K_noP ZetaShell.ShellK.K2_shellZone ZetaShell.ShellS.AS_pointwise_corr ZetaShell.ShellK.F1c.K3b_integrated ZetaShell.ShellS.S2_zero_side ZetaShell.ShellS.Z6a_zero_sums ZetaShell.ShellS.Z6d_counts_corr ZetaShell.TrackF.ring_le_primitive_corr ZetaShell.ShellS.S1_ring_to_zeros
#print axioms ZetaShell.shell_S53_qle_reduced
#print axioms ZetaShell.Design.shell_frame_qle_of_K_noP
#print axioms ZetaShell.ShellK.K2_shellZone
#print axioms ZetaShell.ShellS.AS_pointwise_corr
#print axioms ZetaShell.ShellS.S2_zero_side
#print axioms ZetaShell.TrackF.ring_le_primitive_corr
#print axioms ZetaShell.ShellK.F1c.K3b_integrated
#print axioms ZetaShell.ShellS.S1_ring_to_zeros
#print axioms ZetaShell.ShellS.Z6a_zero_sums
#print axioms ZetaShell.ShellS.Z6d_counts_corr
-- the remaining parts of the main theorem quoted in Appendix A.6 of the family paper
#sorry_leaves ZetaShell.ShellK.KT_transfer ZetaShell.TrackF.lemmaP ZetaShell.TrackF.signed_gallagher ZetaShell.ShellS.S3_family_errors
#print axioms ZetaShell.ShellK.KT_transfer
#print axioms ZetaShell.TrackF.lemmaP
#print axioms ZetaShell.TrackF.signed_gallagher
#print axioms ZetaShell.ShellS.S3_family_errors
#check @ZetaShell.shell_S53_qle_reduced
#check @ZetaShell.LemmaK.theorem_one_prime_design
