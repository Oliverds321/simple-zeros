/-
L7_5 (28 Sep 2026), Track R: the exact moment inequalities of R5Q, restated as separate kernel facts (core Lean only,
`decide +kernel`, no `native_decide`) so that the analytic R5 can use them directly. Same computations as inside
`CertQ.l75Check` (its conjuncts 4 and 5): `a = Z/2 ≥ 3/4`, `b = Z₂/2 ≥ 1/2`, `Z = ∫_{-1}^{1} P̂`, `Z₂ = ∫_{-1}^{1} P̂²`.
-/
import ZetaShell.Cert.ShellCertQ

namespace ZetaShell.CertQ

theorem a_S53 : (3 : Rat) / 4 ≤ pdefint (pmul (spread dS53) (spread dS53)) (-1) 1 / 2 := by decide +kernel

theorem b_S53 : (1 : Rat) / 2 ≤
    pdefint (pmul (pmul (spread dS53) (spread dS53)) (pmul (spread dS53) (spread dS53))) (-1) 1 / 2 := by
  decide +kernel

theorem a_D53 : (3 : Rat) / 4 ≤ pdefint (pmul (spread dD53) (spread dD53)) (-1) 1 / 2 := by decide +kernel

theorem b_D53 : (1 : Rat) / 2 ≤
    pdefint (pmul (pmul (spread dD53) (spread dD53)) (pmul (spread dD53) (spread dD53))) (-1) 1 / 2 := by
  decide +kernel

/-- negative control: the S53 moment `a = 0.7500002…` does NOT reach `0.7500003`. -/
theorem a_S53_control : ¬ ((7500003 : Rat) / 10000000 ≤ pdefint (pmul (spread dS53) (spread dS53)) (-1) 1 / 2) := by
  decide +kernel

end ZetaShell.CertQ
