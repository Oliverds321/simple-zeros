/-
Node K4 (L7_3): Lemma K.4 (lem:K-R), the principal Gauss sum. Draft: "Let `(a′_n)` be supported on integers coprime to
`r` and `S′(θ) = Σ a′_n e(nθ)`. For every `β ∈ ℝ`, `Σ*_{a mod r} |S′(a/r + β)|² = φ(r)⁻¹ Σ_χ |τ(χ)|² |S′_χ̄(β)|²
≥ μ²(r)/φ(r) |S′(β)|²`." Lean form: the inequality only (the identity is the proof), `a` read on `(0, N]`.
Numerics: `numerics/ktests.py` (400 trials, `r ≤ 30`: max (LHS − RHS)/‖a‖² = 7·10⁻¹⁵; the control WITHOUT the
coprimality hypothesis fails by 2.57‖a‖², so the hypothesis is load-bearing).
Dependencies: `τ(χ₀) = μ(r)` (MV Thm 9.10 at `d = 1`; Mathlib: Ramanujan sum / `gaussSum` of the trivial character),
orthogonality on `(ℤ/r)^×` (as in trunk `ZetaQ.primitive_decomposition`). Difficulty: M.
-/
import ZetaShell.Defs.LK_Defs
import ZetaShell.LemmaK.LK9_K4_Aux

noncomputable section

namespace ZetaShell
namespace LemmaK

/-- **K4 (Lemma K.4).** -/
theorem principal_gauss_hole (r N : ℕ) (hr : 0 < r) (a : ℕ → ℂ)
    (hcop : ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → Nat.Coprime n r) (β : ℝ) :
    ((ArithmeticFunction.moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * ‖ZetaQ.expSum N a β‖ ^ 2
      ≤ ∑ b ∈ ZetaQ.reducedResidues r, ‖ZetaQ.expSum N a ((b : ℝ) / (r : ℝ) + β)‖ ^ 2 := by
  exact K4Aux.principal_gauss_hole_aux r N hr a hcop β

end LemmaK
end ZetaShell
