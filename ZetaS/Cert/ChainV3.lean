/-
lean_work/L5_2/v3chain/ChainV3.lean — L5_2, 28 Sep 2026. **The track-C soundness chain, end to end, against the
fixed checker `CheckerCoreV3`** (L1_1c, 11:23; CheckerCoreV3.lean sha256 02f8dab9…, CheckerLeaves.lean 0041178c…,
CheckerBase.lean 6bddd64d…). Olean folder `lean_work/L5_2/olean6`, every module compiled from source against V3:
  spec      CertSpecAM5 = L6_1's CertSpecAM5_patched (C23–C26 proved inside) with `import CheckerCoreV3`
  L5_1      C01–C09 (C07b = the corrected C07b_SincEncl_fix), C14–C17, C19a (corrected: C19a_PsdLDL_symm),
            C19b (C19b_CvxLeaf_proof, compiled as module C19b_CvxLeaf), C20, C21
  L6_1      C10 (C23 through the one-line shim C23_KPsiCos: the patched spec already proves C23)
  L5_2      C11, C12, C13, C18 (v3/C18_LPLeaf.lean, against the V3 guard)
Only imports were changed; no proof needed repair.
Integrated as ZetaS/Cert/ChainV3.lean by L0_5 (round 12): imports renamed to the library's modules, and the
module names in the final `#eval` likewise (ZetaS.Cert.CheckerBase/CheckerLeaves/CertSpecAM5).
The spec's own `Cert.check_sound` stays `sorry` inside CertSpecAM5 (it cannot be proved there: its proof imports
modules that import CertSpecAM5), so the level-A theorems are restated here, downstream.
-/
import ZetaS.Cert.C21_CertSound

namespace ZetaS.CertV2.ChainV3

open ZetaS.CertV2

/-- **The certificate theorem** (node C21, L5_1's proof), against the V3 checker, all dependencies proved. -/
theorem cert_check_sound (C : Cert) (h : C.check = true) : C.data.Holds := Cert.check_sound' C h

/-- **Twenty checked certificates, one per canonical class, give `CertAM5`** (V3 checker, level A). -/
theorem certAM5_of_checks (C : List Cert) (hdata : C.map Cert.data = classes5.map classData)
    (hchk : ∀ c ∈ C, c.check = true) : CertAM5 :=
  certAM5_of_checks_of_sound cert_check_sound C hdata hchk

end ZetaS.CertV2.ChainV3

/- the definitions of the V3 checker modules that `Cert.check` unfolds to (transitively). -/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let modIdxs := #[`ZetaS.Cert.CheckerBase, `ZetaS.Cert.CheckerLeaves].filterMap fun m => env.getModuleIdx? m
  let specIdx := env.getModuleIdx? `ZetaS.Cert.CertSpecAM5
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`ZetaS.CertV2.Cert.check, `ZetaS.CertV2.classData, `ZetaS.CertV2.classes5]
  let mut out : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let idx := env.getModuleIdxFor? n
      let inV3 := match idx with | some i => modIdxs.contains i | none => false
      let inSpec := idx.isSome && idx == specIdx
      if inV3 then out := out.push n
      if inV3 || inSpec then
        for c in ci.type.getUsedConstants ++ ((ci.value?.map Expr.getUsedConstants).getD #[]) do
          todo := todo.push c
        if let .inductInfo ii := ci then
          for c in ii.ctors do todo := todo.push c
  let sorted := out.qsort (fun a b => a.toString < b.toString)
  let main := sorted.filter fun n => !(n.toString.splitOn "match_").length > 1 &&
    !(n.toString.splitOn "._").length > 1 && !(n.toString.splitOn "brecOn").length > 1 &&
    !(n.toString.splitOn ".below").length > 1 && !(n.toString.splitOn ".rec").length > 1 &&
    !(n.toString.splitOn "casesOn").length > 1
  IO.println s!"{sorted.size} V3 constants ({main.size} without auxiliary matchers/recursors): {main.toList}"
