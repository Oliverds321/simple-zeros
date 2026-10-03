/-
Node Z3 (L7_1): the rate exponent of Theorem S(5/3) at `α′ = 2497/1500`, `c₀ = 2`, `ε″ = 0`:
`κ′ = 3988/2497`, `θ(α′) = (2 − κ′)/κ′ = 503/1994` (thm:shell-S53, sec_shell.tex l.123–124: "θ = 503/1994 = 0.2522… at
α′ = 2497/1500"). Dependencies: none. Difficulty: E.
-/
import ZetaShell.Interfaces

namespace ZetaShell

theorem kappaPrime_S53 : kappaPrime 2 (2497 / 1500) 0 = 3988 / 2497 := by
  unfold kappaPrime; norm_num

theorem thetaRate_S53 : thetaRate (kappaPrime 2 (2497 / 1500) 0) = 503 / 1994 := by
  rw [kappaPrime_S53]; unfold thetaRate; norm_num [min_def]

end ZetaShell
