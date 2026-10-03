/-
Sub-node Z9a5 (agent L3_1) — the frame of Z9a4 satisfies `FrameSpec`: kernel and span by definition; trace and
Frobenius norm through toC Ĝ = hat(Az) (Z9a3, `uC_ofReal`, reindexing by Z9a1); the weighted defect by reindexing;
the counts from Z9a6.
-/
import ZetaS.ZeroSide.Z9a6_Counts

noncomputable section

open Matrix RHLinalg

namespace ZetaS
namespace Z9

open Zeta23

variable (Z : ZeroConfig) {P : Params} (ψ : ℝ → ℝ) (T : ℝ) (hP : P.Valid) (heven : ∀ s, ψ (-s) = ψ s) {c : ℝ}
  (hW : AdmWindow (P.phiV ψ T) (P.L T) P.w c) (hv : (∫ u, P.phiV ψ T u ^ 2) ≠ 0) (hT : 0 < T)

omit hP heven in
lemma rtrace_toC {n : Type*} [Fintype n] (A : Matrix n n ℝ) : rtrace (toC A) = rtrace A := by
  simp [RHLinalg.rtrace, toC, Matrix.trace, Complex.re_sum]

omit hP heven in
lemma frobSq_toC {n : Type*} [Fintype n] (A : Matrix n n ℝ) : frobSq (toC A) = frobSq A := by
  rw [Assembly.frobSq_eq_sum_norm_sq, Assembly.frobSq_eq_sum_norm_sq]; simp [toC, Complex.norm_real]

/-- `toC Ĝ = hat(Az)`. -/
theorem frameAt_toC : toC (frameAt Z ψ T hP heven hW hv hT).Gt = (P.atV ψ T).hat T (Z.Az (P.atV ψ T) T) := by
  have hu : ∀ (i : Fin (Son Z T).card) (j : Fin (P.d T)), uvec P ψ T (eOn Z T i) j
      = (uR (P.phiV ψ T) (P.L T) T (gOn Z T i) ((j : ℕ) : ℤ) : ℂ) := by
    intro i j
    simp only [uvec]
    rw [ZeroSide.gammaOf_of_re_eq_half (Son_re Z T _ (eOn Z T i).2), eOn_im, ZeroSide.uC_ofReal hW]
  refine Matrix.ext fun (k : Fin (P.d T)) (l : Fin (P.d T)) => ?_
  have hR := congrFun (congrFun (hatAz_decomp Z hP heven hW) k) l
  refine Eq.trans ?_ hR.symm
  show ((((Matrix.of fun (k : Fin (P.d T)) (i : Fin (Son Z T).card) =>
          uR (P.phiV ψ T) (P.L T) T (gOn Z T i) (k : ℕ)) * diagonal (fun i => (Z.mult (eOn Z T i) : ℝ))
        * (Matrix.of fun (k : Fin (P.d T)) (i : Fin (Son Z T).card) =>
          uR (P.phiV ψ T) (P.L T) T (gOn Z T i) (k : ℕ))ᵀ
        + offBlock (Aoff Z T) (fun ρ => 2 * (Z.mult ρ : ℝ))
            (fun ρ k => (uvec P ψ T ρ k).re) (fun ρ k => (uvec P ψ T ρ k).im)) k l : ℝ) : ℂ) = _
  rw [Matrix.add_apply, Complex.ofReal_add, Matrix.add_apply]
  congr 1
  · rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Complex.ofReal_sum]
    rw [← Finset.sum_coe_sort (Son Z T), ← Equiv.sum_comp (eOn Z T)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu, hu]
    push_cast; ring

/-- trace and Frobenius norm of the frame's Ĝ are those of hat(Az). -/
theorem frameAt_trfrob :
    rtrace (frameAt Z ψ T hP heven hW hv hT).Gt = rtrace ((P.atV ψ T).hat T (Z.Az (P.atV ψ T) T)) ∧
    frobSq (frameAt Z ψ T hP heven hW hv hT).Gt = frobSq ((P.atV ψ T).hat T (Z.Az (P.atV ψ T) T)) := by
  have h := frameAt_toC Z ψ T hP heven hW hv hT
  exact ⟨(rtrace_toC _).symm.trans (congrArg rtrace h), (frobSq_toC _).symm.trans (congrArg frobSq h)⟩

/-- the weighted defect of the frame is the one of node Z6. -/
theorem frameAt_defect :
    ∑ i, ((frameAt Z ψ T hP heven hW hv hT).m i : ℝ) * (frameAt Z ψ T hP heven hW hv hT).delta i
      = ∑ᶠ ρ ∈ Z.window (lo T) (hi T) ∩ {ρ : ℂ | ρ.re = 1 / 2},
          (Z.mult ρ : ℝ) * deltaW (P.phiV ψ T) (P.L T) T (P.d T) ρ.im := by
  have hset : Z.window (lo T) (hi T) ∩ {ρ : ℂ | ρ.re = 1 / 2} = ↑(Son Z T) := by
    rw [window_eq_ZI]; ext ρ; simp
  rw [hset, finsum_mem_coe_finset, sum_Son]
  refine Finset.sum_congr rfl fun (i : Fin (Son Z T).card) _ => ?_
  show (Z.mult (eOn Z T i) : ℝ) * (∑' k : offGrid (P.d T),
      uR (P.phiV ψ T) (P.L T) T (gOn Z T i) k.1 * uR (P.phiV ψ T) (P.L T) T (gOn Z T i) k.1)
    = (Z.mult (eOn Z T i) : ℝ) * deltaW (P.phiV ψ T) (P.L T) T (P.d T) (eOn Z T i : ℂ).im
  rw [ZeroSide.offGrid_diag]
  exact congrArg (fun t => (Z.mult (eOn Z T i) : ℝ) * deltaW (P.phiV ψ T) (P.L T) T (P.d T) t)
    (eOn_im Z T i).symm

theorem frameAt_spec : FrameSpec Z P ψ T (frameAt Z ψ T hP heven hW hv hT) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := frameAt_counts Z ψ T hP heven hW hv hT
  exact { k_eq := rfl
          tr_eq := (frameAt_trfrob Z ψ T hP heven hW hv hT).1
          frob_eq := (frameAt_trfrob Z ψ T hP heven hW hv hT).2
          Nw_eq := h1
          Λ_eq := rfl
          defect_eq := frameAt_defect Z ψ T hP heven hW hv hT
          NsW_eq := h2
          sEq1_eq := h3
          NdW_eq := h4
          NscW_eq := h5 }

end Z9
end ZetaS
