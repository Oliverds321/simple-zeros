/- replay: common lemmas (L1_1d/e). Library modules only (green: ZetaS.Cert.*). -/
import ZetaS.Cert.CertSpecAM5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2

theorem LIQ.ext' {a b : LIQ} (h0 : a.d = b.d) (h1 : a.spans = b.spans) (h2 : a.mu = b.mu)
    (h3 : a.claim = b.claim) : a = b := by
  cases a; cases b; simp_all

/-- the root conditions of `Cert.check` (everything except the tree). -/
def rootOK (C : Cert) : Bool :=
  C.data.wf && decide (C.root.length = C.data.d) &&
    (List.range C.data.d).all (fun l => decide ((C.root.getD l (0, 0)).1 = 0) &&
      decide (C.data.claim ≤ C.data.mu.getD l 0 * (C.root.getD l (0, 0)).2))

theorem Cert.check_of_parts (C : Cert) (h1 : rootOK C = true) (h2 : C.tree.check C.data C.root = true) :
    C.check = true := by
  show (rootOK C && C.tree.check C.data C.root) = true
  rw [h1, h2]; rfl

end ZetaS.CertV2
