/-
Node L2 (track L) — lem:oll-Ast, sec_zeta.tex l.640–662 (two-parameter rank–trace, used by cor:oll-SC at
(s,t) = (1, 2+√2)): for 0 ≤ s ≤ t, "s² r + t² b ≥ 2s tr P + 2t tr Q − ‖P+Q‖² + tr Ψ_{s,t}(M)".
(s,t) = (1,2) is L1 (since PsiST 1 2 = Psi). Proof: as L1 with s² − 2sp + (p−n)² + 2tn = (p−n−s)² + 2(t−s)n.
Deps: Interfaces (PsiST, trFun); trunk RHLinalg.

Proof (L2_1): `LinAlgHelpers.sum_eig_transfer` with `f = Ψ_{s,t} − s²` (`Ψ_{s,t}(0) = s²` as `0 ≤ t`) and
`LinAlgHelpers.stab_core_two` (the template `rank_trace_ineq` at `c = t`, step 5 replaced by
`Ψ_{s,t}(p) ≤ (p − m − s)² + 2(t − s)m`, `m ≥ 0`).
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.Helpers

open Matrix RHLinalg
open scoped ComplexOrder

namespace ZetaS

theorem stab_rank_trace_two {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (V : Matrix n r 𝕜) {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    2 * s * rtrace (V * Vᴴ) + 2 * t * rtrace Q - frobSq (V * Vᴴ + Q)
        + trFun (Matrix.isHermitian_conjTranspose_mul_self V) (PsiST s t)
      ≤ s ^ 2 * (Fintype.card r : ℝ) + t ^ 2 * (b : ℝ) := by
  have hP : (V * Vᴴ).PosSemidef := posSemidef_self_mul_conjTranspose V
  have hcore := stab_core_two hP hQ hb (s := s) (t := t)
  have h0 : PsiST s t 0 - s ^ 2 = 0 := by
    unfold PsiST; rw [if_pos (hs.trans hst)]; ring
  have htr := sum_eig_transfer V (fun x => PsiST s t x - s ^ 2) h0
  have hsplit : trFun (Matrix.isHermitian_conjTranspose_mul_self V) (PsiST s t)
      = ∑ i, (PsiST s t ((Matrix.isHermitian_conjTranspose_mul_self V).eigenvalues i) - s ^ 2)
        + s ^ 2 * (Fintype.card r : ℝ) := by
    unfold trFun
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  rw [hsplit, htr]
  linarith

end ZetaS
