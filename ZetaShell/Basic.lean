/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaShell/Basic.lean — placeholder module of the family follow-up library `ZetaShell` (Phase 0 of
`mathsrh/rh72/LEAN_PLAN.md`). It only checks that the library is wired to `ZetaQ`: it imports the
root `ZetaQ` and states one trivial fact about a `ZetaQ` definition. The shell deduction, the
`ZeroDensityInput` interface and the node statements are added in Phase 1.
-/
import ZetaQ

namespace ZetaShell

/-- Wiring check: the family zero count `ZetaQ.NcountQ` (`ZetaQ/Certificate.lean`) is `0` at the
degenerate modulus `q = 0`, by its definition. -/
theorem NcountQ_modulus_zero (χ : DirichletCharacter ℂ 0) (T₁ T₂ : ℝ) :
    ZetaQ.NcountQ 0 χ T₁ T₂ = 0 := by
  simp [ZetaQ.NcountQ]

end ZetaShell
