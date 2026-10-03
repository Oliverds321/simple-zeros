/-
Node K4b (L7_3): "`Σ_{r≤R} μ²(r)/φ(r) ≥ log R` for `R ≥ 1` [MV (3.18)]" (sec_lemmaK, after lem:K-R); used in eq:K-hole.
Lean form at integer `R` (the draft applies it at real `R₀ ≥ 1`; `Σ_{r ≤ R₀} = Σ_{r ≤ ⌊R₀⌋}` and
`log R₀ < log(⌊R₀⌋ + 1)`, so the consumer needs the sharper `log(R+1)` form — stated here).
Proof route: `μ²(r)/φ(r) = Σ_{n : rad n = r} 1/n`, `rad n ≤ n`, `Σ_{n≤R} 1/n ≥ log(R+1)`.
Numerics: `numerics/ktests.py` (`R < 3000`: min of `Σ − log R` is 1.0000, at `R = 1`). Difficulty: M.
-/
import ZetaShell.Defs.LK_Defs
import ZetaShell.LemmaK.LK9_K4b_Aux

noncomputable section

namespace ZetaShell
namespace LemmaK

/-- **K4b.** -/
theorem log_succ_le_sum_moebius_sq_div_totient (R : ℕ) :
    Real.log ((R : ℝ) + 1) ≤
      ∑ r ∈ Finset.Icc 1 R, ((ArithmeticFunction.moebius r : ℝ)) ^ 2 / (Nat.totient r : ℝ) := by
  exact K4bAux.log_succ_le_sum_aux R

end LemmaK
end ZetaShell
