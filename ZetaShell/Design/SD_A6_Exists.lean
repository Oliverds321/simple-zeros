/-
Node SD-A6 (L7_7, F1a): the Shell design exists for all large `Q` — `ShellFrame.exists_design`.
Round 2: immediate from SD-A5's eventual form (`Filter.eventually_atTop`). Statement unchanged. Deps: SD-A5.
Difficulty E.
-/
import ZetaShell.Design.SD_A5_ExistsAt

namespace ZetaShell.Design

open ZetaQ Filter

theorem exists_shellDesignM (hL : S53L75.L75) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∃ P : ParamsQ, ShellDesignM S53L75 r ε Q P :=
  eventually_atTop.mp (exists_shellDesignM_eventually hL r ε hr hε)

end ZetaShell.Design
