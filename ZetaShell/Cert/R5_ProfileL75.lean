/-
Node R5 (L7_1): the two headline profiles meet the Lean side conditions L75 (ssec:shell-cert "Lean side conditions",
l.1080–1082; table of ssec:shell-cert-53: S53-L75 `a = 0.7500002`, `b = 0.6240`, `p(λ/2) = 0.1968`; D53-L75
`a = 0.7577`, `b = 0.6305`, `p(λ/2) = 0.16666687`, margin 2·10⁻⁷ over 1/6) and `0 < p ≤ 1`, `p` decreasing.
Method of the draft: Sturm sequences over ℚ in `s = (2t/λ)²` for `p`, `(1−p)/s`, `−p′(s)` on `[0,1]`, exact moments.
Dependencies: none new. Difficulty: M (Sturm or Bernstein positivity by `decide +kernel`; `a`, `b` exact rationals).
-/
import ZetaShell.Interfaces
import ZetaShell.Cert.R5_S53
import ZetaShell.Cert.R5_D53

/-! PROVED by L7_5 (28 Sep 2026). Route: `TR_L75.L75_of_cert` reduces `L75` to (i) `q = Σ d_i s^i` strictly
decreasing on `[0,1]`, from `-q' = Σ e_k s^k (1-s)^{N-k}` with all `e_k > 0` (Bernstein form, degree 5 for S53-L75,
degree 15 = 5 + 10 elevations for D53-L75; identity by `ring`), (ii) `q(0) = 1`, `q(1) ≥ 1/6` (`norm_num`), and
(iii) the exact moments `3/4 ≤ Z/2`, `1/2 ≤ Z₂/2` (kernel, `TR_Q.lean`), with `mass = (λ/2)·Z` and
`∫p⁴ = (λ/2)·Z₂` proved from the soundness of `pmul`/`pint`/`spread` (`TR_Poly.lean`). -/

namespace ZetaShell

theorem S53L75_L75 : S53L75.L75 := TR.S53L75_L75'

theorem D53L75_L75 : D53L75.L75 := TR.D53L75_L75'

end ZetaShell
