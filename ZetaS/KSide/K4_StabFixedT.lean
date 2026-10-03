/-
Node K4 (track K) — cor:zeta-stab, first display (l.271–275, proof l.282–287), at one height:
"s₁ ≥ 4 tr Ĝ − 2N(I′) − ‖Ĝ‖² + tr Ψ(M°)".
Deps: L1 (with 𝕜 = ℝ, V = D.V, Q = D.Qp, b = s₂ + p), GramData fields tr_P1, nplus_Qp, count, P1_eq.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L1_StabRankTrace

open Matrix RHLinalg

namespace ZetaS

theorem stab_fixedT (D : GramData) :
    4 * rtrace D.Gt - 2 * (D.Nw : ℝ) - frobSq D.Gt
        + trFun (Matrix.isHermitian_conjTranspose_mul_self D.V) Psi
      ≤ (D.s1 : ℝ) := by
  have h := stab_rank_trace D.V D.Qp_herm D.nplus_Qp
  have hP : D.V * D.Vᴴ = D.P1 := by rw [D.P1_eq, conjTranspose_eq_transpose_of_trivial]
  rw [hP, Fintype.card_fin] at h
  have htr : rtrace D.Gt = rtrace D.P1 + rtrace D.Qp := by
    simp only [GramData.Gt, rtrace, Matrix.trace_add, map_add]
  have h1 := D.tr_P1
  have h2 : (D.s1 : ℝ) + 2 * ((D.s2 + D.p : ℕ) : ℝ) ≤ D.Nw := by
    have := D.count; exact_mod_cast (by omega : D.s1 + 2 * (D.s2 + D.p) ≤ D.Nw)
  have hG : frobSq D.Gt = frobSq (D.P1 + D.Qp) := rfl
  rw [htr, hG]
  linarith

end ZetaS
