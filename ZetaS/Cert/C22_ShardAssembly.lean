/-
nodes/C22_ShardAssembly.lean — track C node C22 (L1_1b, 28 Sep 2026).
Depends on: none — PROVED in the checker (v3: CheckerLeaves) (`Node.check_split_of`, `Node.check_leaf_of`).
Expected proof size: ≤ 0 lines.
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

example (D : LIQ) (a : ℕ) (L R : Node) (B B1 B2 : Box) (hs : B.splitAt a = (B1, B2))
    (ha : decide (a < D.d) = true) (hL : L.check D B1 = true) (hR : R.check D B2 = true) :
    (Node.split a L R).check D B = true := Node.check_split_of D a L R B B1 B2 hs ha hL hR

end ZetaS.CertV2
