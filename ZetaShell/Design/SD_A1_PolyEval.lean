/-
Node SD-A1 (L7_7, F1a): the polynomial `S.poly` evaluates to the Shell profile `S.p`.
Needed for `ShellFrame.prof_eq` (`P.prof.eval t = S.p t`). Draft: ssec:shell-cert-53 (profile data). Deps: none.
Difficulty E.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell

theorem ShellProfile.poly_eval (S : ShellProfile) (t : ℝ) : S.poly.eval t = S.p t := by
  unfold ShellProfile.poly ShellProfile.p
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

end ZetaShell
