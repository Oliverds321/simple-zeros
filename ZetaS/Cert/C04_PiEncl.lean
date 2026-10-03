/-
nodes/C04_PiEncl.lean — track C node C04 (L1_1b, 28 Sep 2026).
Depends on: none (Mathlib pi_gt_d20, pi_lt_d20).
Expected proof size: ≤ 10 lines.
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

theorem piQ_contains : piQ.Contains Real.pi := by
  unfold QI.Contains piQ
  constructor
  · have := Real.pi_gt_d20; push_cast; norm_num at this ⊢; linarith
  · have := Real.pi_lt_d20; push_cast; norm_num at this ⊢; linarith

end ZetaS.CertV2
