/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaS/Basic.lean — placeholder module of the ζ follow-up library `ZetaS` (Phase 0 of
`mathsrh/rh72/LEAN_PLAN.md`). It only checks that the library is wired to the trunk: it imports
the root `Zeta23` and states one trivial fact about a trunk definition. The shared definitions
(`ZetaS/Defs/`) and the node statements (`ZetaS/Skeleton/`) are added in Phase 1.
-/
import Zeta23

namespace ZetaS

/-- Wiring check: the trunk's `D₀(T)` (`Zeta23/Defs.lean`) is `√T`, by definition. -/
theorem D0_eq_sqrt (T : ℝ) : Zeta23.D0 T = Real.sqrt T := rfl

end ZetaS
