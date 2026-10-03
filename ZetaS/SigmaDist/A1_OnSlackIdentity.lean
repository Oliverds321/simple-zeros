/-
Node A1 (track K, all-marks) — lem:sigd-onslack, identity part (sec_zeta.tex l.1123–1135): for vectors u_ρ (columns of
U) and multiplicities m_ρ, with C := UᵀU (so C_ρρ = d_ρ, C_ρρ′ = ⟨u_ρ,u_ρ′⟩) and G := Σ m_ρ u_ρu_ρᵀ,
"Slack(𝒪) = s₁(𝒪) − 2 tr G + ‖G‖² = Σ_ρ β_ρ + E(𝒪), β_ρ = 1_{m_ρ=1} − 2m_ρd_ρ + m_ρ²d_ρ², E = Σ_{ρ≠ρ′} m m′ C²".
Pure algebra (tr G = Σ m C_ρρ, ‖G‖² = Σ m m′ C_ρρ′²).

Proof (L2_2): `tr(U D Uᵀ) = tr(Uᵀ U D)`, `‖U D Uᵀ‖² = tr(U D Uᵀ U D Uᵀ) = tr(D C D C) = Σ_{ij} m_i m_j C_ij²`
(C symmetric), then split the diagonal off the double sum.
-/
import ZetaS.Interfaces

open Matrix RHLinalg Finset

namespace ZetaS

theorem onslack_identity {d n : ℕ} (U : Matrix (Fin d) (Fin n) ℝ) (m : Fin n → ℕ) :
    (#(univ.filter fun i => m i = 1) : ℝ)
        - 2 * rtrace (U * diagonal (fun i => (m i : ℝ)) * Uᵀ)
        + frobSq (U * diagonal (fun i => (m i : ℝ)) * Uᵀ)
      = (∑ i, ((if m i = 1 then (1 : ℝ) else 0) - 2 * m i * (Uᵀ * U) i i
            + (m i : ℝ) ^ 2 * ((Uᵀ * U) i i) ^ 2))
        + ∑ i, ∑ j, if i = j then (0 : ℝ) else (m i : ℝ) * m j * ((Uᵀ * U) i j) ^ 2 := by
  set D : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => (m i : ℝ)) with hD
  set C : Matrix (Fin n) (Fin n) ℝ := Uᵀ * U with hC
  have hCsymm : ∀ i j, C j i = C i j := by
    intro i j
    simp only [hC, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- the trace
  have htr : rtrace (U * D * Uᵀ) = ∑ i, (m i : ℝ) * C i i := by
    unfold rtrace
    rw [RCLike.re_to_real, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, hD, Matrix.mul_diagonal, hC]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- the Frobenius norm
  have hDT : Dᵀ = D := by simp [hD]
  have hT : (U * D * Uᵀ)ᵀ = U * D * Uᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hDT, Matrix.mul_assoc]
  have hentry : ∀ i, (D * C * D * C) i i = ∑ j, (m i : ℝ) * m j * C i j ^ 2 := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_diagonal, hD, Matrix.diagonal_mul, hCsymm i j]
    ring
  have hfr : frobSq (U * D * Uᵀ) = ∑ i, ∑ j, (m i : ℝ) * m j * C i j ^ 2 := by
    unfold frobSq
    rw [RCLike.re_to_real, Matrix.conjTranspose_eq_transpose_of_trivial, hT]
    have h1 : (U * D * Uᵀ) * (U * D * Uᵀ) = U * (D * C * D * Uᵀ) := by
      simp only [hC, Matrix.mul_assoc]
    have h2 : D * C * D * Uᵀ * U = D * C * D * C := by
      simp only [hC, Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm, h2]
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.sum_congr rfl fun i _ => hentry i
  -- split the diagonal off the double sum
  have hsplit : ∀ i, ∑ j, (m i : ℝ) * m j * C i j ^ 2
      = (m i : ℝ) ^ 2 * C i i ^ 2 + ∑ j, if i = j then (0 : ℝ) else (m i : ℝ) * m j * C i j ^ 2 := by
    intro i
    have : ∀ j, (m i : ℝ) * m j * C i j ^ 2
        = (if i = j then (m i : ℝ) * m j * C i j ^ 2 else 0)
          + (if i = j then (0 : ℝ) else (m i : ℝ) * m j * C i j ^ 2) := by
      intro j; split_ifs <;> simp
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    ring
  rw [htr, hfr, Finset.natCast_card_filter]
  simp only [hsplit, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_sub_distrib]
  ring_nf

end ZetaS
