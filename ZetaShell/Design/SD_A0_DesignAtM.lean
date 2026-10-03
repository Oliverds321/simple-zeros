/-
Node SD-A0 (L7_7, F1a): ZetaQ's design of record with margin IS the generic `DesignAtM` at `(λ*_F, p_F)`.
Draft: rem:shell-lean ("the design layer at the new λ"); paper §10.3. Deps: none. Difficulty E. Proof: `rfl`.
Consequence: every ZetaQ lemma about `DesignOfRecordM F r ε Q P` is a lemma about `DesignAtM F.lamStar F.designProfile`,
so the Shell design differs from ZetaQ's only in the two parameters.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

open ZetaQ

theorem designOfRecordM_eq_designAtM (F : Family) (r ε Q : ℝ) (P : ParamsQ) :
    DesignOfRecordM F r ε Q P = DesignAtM F.lamStar F.designProfile r ε Q P := rfl

end ZetaShell.Design
