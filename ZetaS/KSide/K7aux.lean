/-
K7aux (L4_1, 28 Sep 2026) — the pieces of cor:oll-SC (sec_zeta.tex l.675–709) used by node K7 (`sc_abstract`).
  * `psiST_nonneg`, `psiST_convexOn`, `psi_le_psiST` : Ψ_{1,t} ≥ 0, convex, and ≥ Ψ on [0,∞) for t ≥ 2 (l.664).
  * `sc_height` : at one height, for the GramData D of K0 (simple columns e of U):
        2t·tr Ĝ − ‖Ĝ‖² − (t²/4)N(I′) + tr Ψ(M°) ≤ (t²/4)·N^sc(I′),   t = 2 + √2,
    from L2 at (s,t) = (1, 2+√2) with P = U diag(m) Uᵀ = VVᵀ, V = U diag(√m), Q = Qoff (n₊ ≤ p), then pinching
    VᵀV onto the simple block (L4) and Ψ_{1,t} ≥ Ψ; counts n ≤ N_on, 4p ≤ N_off + 2p₁.
  * `gramFamily_of_frame` : a FrameFamily yields a GramFamily through K0 (per height), same N, R, k_ψ.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L2_StabRankTraceTwo
import ZetaS.SigmaDist.A8_SigmaDistAbstract
import ZetaS.KSide.K0_FrameToGram
import ZetaS.KSide.KHelpers

open Matrix RHLinalg Finset Filter Asymptotics

namespace ZetaS
namespace K7aux

lemma psiST_nonneg {t : ℝ} (ht : 1 ≤ t) (p : ℝ) : 0 ≤ PsiST 1 t p := by
  unfold PsiST; split_ifs with h
  · exact sq_nonneg _
  · push_neg at h; nlinarith

lemma psiST_tangent_le {t s : ℝ} (hs : s ≤ t) (p : ℝ) :
    (s - 1) ^ 2 + 2 * (s - 1) * (p - s) ≤ PsiST 1 t p := by
  unfold PsiST; split_ifs with h
  · nlinarith [sq_nonneg (p - s)]
  · push_neg at h
    nlinarith [mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 h.le), sq_nonneg (s - t)]

lemma psiST_eq_tangent (t z : ℝ) :
    PsiST 1 t z = (min z t - 1) ^ 2 + 2 * (min z t - 1) * (z - min z t) := by
  unfold PsiST; split_ifs with h
  · rw [min_eq_left h]; ring
  · push_neg at h; rw [min_eq_right h.le]

lemma psiST_convexOn (t : ℝ) : ConvexOn ℝ (Set.Ici 0) (PsiST 1 t) := by
  refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y
  set s := min z t with hs
  have hst : s ≤ t := min_le_right _ _
  rw [psiST_eq_tangent t z]
  have hx := psiST_tangent_le hst x
  have hy := psiST_tangent_le hst y
  have hlin : (s - 1) ^ 2 + 2 * (s - 1) * (z - s)
      = a * ((s - 1) ^ 2 + 2 * (s - 1) * (x - s)) + b * ((s - 1) ^ 2 + 2 * (s - 1) * (y - s)) := by
    have hb' : b = 1 - a := by linarith
    simp only [z, hb']; ring
  rw [← hs, hlin]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma psi_le_psiST {t : ℝ} (ht : 2 ≤ t) (p : ℝ) : Psi p ≤ PsiST 1 t p := by
  unfold Psi PsiST
  split_ifs with h1 h2 h2
  · exact le_rfl
  · linarith
  · nlinarith [sq_nonneg (p - 2)]
  · push_neg at h1 h2
    nlinarith [mul_nonneg (sub_nonneg.2 ht) (sub_nonneg.2 h2.le), sq_nonneg (t - 2)]

/-- the constant t = 2 + √2 and its identity t² = 4t − 2. -/
lemma t_sq : (2 + Real.sqrt 2) ^ 2 = 4 * (2 + Real.sqrt 2) - 2 := by
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

lemma t_ge : (2 : ℝ) ≤ 2 + Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]

/-- one height: L2 at (1, 2 + √2), pinching to the simple block, and the counts. -/
theorem sc_height (F : ZeroFrame) (D : GramData) (h : F.d = D.d) (e : Fin D.s1 → Fin F.n)
    (he : StrictMono e) (he1 : ∀ j, F.m (e j) = 1)
    (hV : D.V = Matrix.reindex (finCongr h) (Equiv.refl _) (F.U.submatrix id e)) :
    2 * (2 + Real.sqrt 2) * rtrace F.Gt - frobSq F.Gt - (2 + Real.sqrt 2) ^ 2 / 4 * (F.Nw : ℝ)
        + trFun (Matrix.isHermitian_conjTranspose_mul_self D.V) Psi
      ≤ (2 + Real.sqrt 2) ^ 2 / 4 * (F.NscW : ℝ) := by
  classical
  set t := 2 + Real.sqrt 2 with htdef
  have ht2 : t ^ 2 = 4 * t - 2 := t_sq
  have ht : 2 ≤ t := t_ge
  set V : Matrix (Fin F.d) (Fin F.n) ℝ := F.U * diagonal (fun i => Real.sqrt (F.m i)) with hVdef
  have hL2 := stab_rank_trace_two V F.Qoff_herm F.nplus_off (s := 1) (t := t) (by norm_num) (by linarith)
  -- V Vᵀ = U diag(m) Uᵀ
  have hVV : V * Vᴴ = F.U * diagonal (fun i => (F.m i : ℝ)) * F.Uᵀ := by
    rw [conjTranspose_eq_transpose_of_trivial, hVdef, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), Matrix.diagonal_mul_diagonal, ← Matrix.mul_assoc]
    rw [show (fun i => Real.sqrt (F.m i : ℝ) * Real.sqrt (F.m i)) = fun i => (F.m i : ℝ) from
      funext fun i => Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hGt : V * Vᴴ + F.Qoff = F.Gt := by rw [hVV]; rfl
  rw [hGt, Fintype.card_fin] at hL2
  have htrGt : rtrace F.Gt = rtrace (V * Vᴴ) + rtrace F.Qoff := by
    rw [← hGt]; exact A8b.rtrace_add _ _
  -- tr P ≤ N_on
  have htrP : rtrace (V * Vᴴ) ≤ ∑ i, (F.m i : ℝ) := by
    rw [hVV, A8b.rtrace_UDUt]
    apply Finset.sum_le_sum; intro i _
    have hC : (F.Uᵀ * F.U) i i = 1 - F.Etr i i := K0aux.Cg_diag F i
    have := F.Etr_psd.diag_nonneg (i := i)
    have : (0 : ℝ) ≤ F.m i := Nat.cast_nonneg _
    rw [hC]; nlinarith
  -- pinching VᵀV onto the simple block, then Ψ ≤ Ψ_{1,t}
  have hMpsd : (Vᴴ * V).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self V
  have hpinch := KHelp.pinch_blocks hMpsd {0} (fun _ => e) (fun _ _ => he.injective)
    (fun a ha b hb _ _ _ => by rw [Finset.mem_singleton] at ha hb; rw [ha, hb])
    (psiST_convexOn t) (fun x _ => psiST_nonneg (by linarith) x)
  rw [Finset.sum_singleton] at hpinch
  have hVe : ∀ l k, V l k = F.U l k * Real.sqrt (F.m k) := fun l k => by
    rw [hVdef, Matrix.mul_diagonal]
  have hsub : (Vᴴ * V).submatrix e e = D.Vᴴ * D.V := by
    rw [hV]; ext i j
    rw [submatrix_apply, mul_apply, mul_apply]
    simp only [conjTranspose_apply, star_trivial, hVe, he1, Nat.cast_one, Real.sqrt_one, mul_one,
      reindex_apply, submatrix_apply, Equiv.refl_symm, Equiv.coe_refl, id]
    exact (Equiv.sum_comp (finCongr h).symm (fun l => F.U l (e i) * F.U l (e j))).symm
  have hsubH : ((Vᴴ * V).submatrix e e).IsHermitian := (hMpsd.submatrix e).isHermitian
  have hpsi : trFun (Matrix.isHermitian_conjTranspose_mul_self D.V) Psi
      ≤ trFun (hMpsd.submatrix e).isHermitian (PsiST 1 t) := by
    rw [← KHelp.trFun_congr hsub hsubH (Matrix.isHermitian_conjTranspose_mul_self D.V) Psi]
    unfold trFun
    exact Finset.sum_le_sum fun i _ => psi_le_psiST ht _
  have hMdef : trFun (Matrix.isHermitian_conjTranspose_mul_self V) (PsiST 1 t)
      = trFun hMpsd.isHermitian (PsiST 1 t) := rfl
  rw [hMdef] at hL2
  -- counts
  have hn : (F.n : ℝ) ≤ ∑ i, (F.m i : ℝ) := by
    have : ((F.n : ℕ) : ℝ) = ∑ _i : Fin F.n, (1 : ℝ) := by simp
    rw [this]; exact Finset.sum_le_sum fun i _ => by exact_mod_cast F.one_le_m i
  have hp : 4 * (F.p : ℝ) ≤ F.Noff + 2 * F.p1 := by
    have := F.Noff_ge; have := F.p1_le
    exact_mod_cast (by omega : 4 * F.p ≤ F.Noff + 2 * F.p1)
  have hNw : (F.Nw : ℝ) = ∑ i, (F.m i : ℝ) + F.Noff := by unfold ZeroFrame.Nw; push_cast; ring
  have hNsc : (F.NscW : ℝ) = ∑ i, (F.m i : ℝ) + 2 * F.p1 := by unfold ZeroFrame.NscW; push_cast; ring
  -- products
  have f1 : (2 * t - 2) * rtrace (V * Vᴴ) ≤ (2 * t - 2) * ∑ i, (F.m i : ℝ) :=
    mul_le_mul_of_nonneg_left htrP (by linarith)
  have f2 : t ^ 2 * (F.p : ℝ) ≤ t ^ 2 * ((F.Noff + 2 * F.p1) / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg t)
  rw [htrGt, hNw, hNsc]
  rw [ht2] at f2 ⊢
  rw [ht2] at hL2
  nlinarith [hpinch, hpsi, f1, f2, hL2, hn]


/-! ### a FrameFamily yields a GramFamily through K0 -/

noncomputable def gramOf (F : ZeroFrame) : GramData := Classical.choose (frame_to_gram_fix F)

lemma gramOf_spec (F : ZeroFrame) :
    ∃ h : F.d = (gramOf F).d,
      (gramOf F).Gt = Matrix.reindex (finCongr h) (finCongr h) F.Gt ∧ (gramOf F).Nw = F.Nw ∧
      (gramOf F).s1 = #(univ.filter fun i => F.m i = 1) ∧ (gramOf F).k = F.k ∧ (gramOf F).Λ = F.Λ ∧
      RHLinalg.rtrace (gramOf F).Etr ≤ RHLinalg.rtrace F.Etr ∧
      ∃ e : Fin (gramOf F).s1 → Fin F.n, StrictMono e ∧ (∀ j, F.m (e j) = 1) ∧
        (gramOf F).V = Matrix.reindex (finCongr h) (Equiv.refl _) (F.U.submatrix id e) :=
  Classical.choose_spec (frame_to_gram_fix F)

lemma rtrace_reindex {n n' : Type*} [Fintype n] [Fintype n'] (σ : n ≃ n') (A : Matrix n n ℝ) :
    rtrace (Matrix.reindex σ σ A) = rtrace A := by
  unfold rtrace
  simp only [RCLike.re_to_real, Matrix.trace, Matrix.diag, reindex_apply, submatrix_apply]
  exact Equiv.sum_comp σ.symm (fun i => A i i)

lemma frobSq_reindex {n n' : Type*} [Fintype n] [Fintype n'] (σ : n ≃ n') (A : Matrix n n ℝ) :
    frobSq (Matrix.reindex σ σ A) = frobSq A := by
  rw [KHelp.frobSq_eq_sum, KHelp.frobSq_eq_sum]
  simp only [reindex_apply, submatrix_apply]
  rw [Equiv.sum_comp σ.symm (fun i => ∑ j, A i (σ.symm j) ^ 2)]
  exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ.symm (fun j => A i j ^ 2)

lemma gram_tr (F : ZeroFrame) : rtrace (gramOf F).Gt = rtrace F.Gt := by
  obtain ⟨h, hG, -⟩ := gramOf_spec F; rw [hG, rtrace_reindex]
lemma gram_frob (F : ZeroFrame) : frobSq (gramOf F).Gt = frobSq F.Gt := by
  obtain ⟨h, hG, -⟩ := gramOf_spec F; rw [hG, frobSq_reindex]
lemma gram_Nw (F : ZeroFrame) : (gramOf F).Nw = F.Nw := (gramOf_spec F).choose_spec.2.1
lemma gram_k (F : ZeroFrame) : (gramOf F).k = F.k := (gramOf_spec F).choose_spec.2.2.2.1
lemma gram_Λ (F : ZeroFrame) : (gramOf F).Λ = F.Λ := (gramOf_spec F).choose_spec.2.2.2.2.1
lemma gram_Etr (F : ZeroFrame) : rtrace (gramOf F).Etr ≤ ∑ i, (F.m i : ℝ) * F.delta i := by
  refine ((gramOf_spec F).choose_spec.2.2.2.2.2.1).trans ?_
  unfold rtrace
  simp only [RCLike.re_to_real, Matrix.trace, Matrix.diag]
  apply Finset.sum_le_sum; intro i _
  have := F.Etr_psd.diag_nonneg (i := i)
  have : (1 : ℝ) ≤ F.m i := by exact_mod_cast F.one_le_m i
  show F.Etr i i ≤ (F.m i : ℝ) * F.Etr i i
  nlinarith
lemma gram_Etr_nonneg (F : ZeroFrame) : 0 ≤ rtrace (gramOf F).Etr := by
  unfold rtrace
  simp only [RCLike.re_to_real, Matrix.trace, Matrix.diag]
  exact Finset.sum_nonneg fun i _ => (gramOf F).Etr_psd.diag_nonneg

noncomputable def gramFamily_of_frame {N : ℝ → ℝ} {R : ℝ} {kψ : ℝ → ℝ} (Fm : FrameFamily N R kψ) :
    GramFamily N R kψ where
  G T := gramOf (Fm.F T)
  N_nonneg := Fm.N_nonneg
  N_tendsto := Fm.N_tendsto
  trace := by simpa only [gram_tr] using Fm.trace
  frob := by simpa only [gram_frob] using Fm.frob
  window := by simpa only [gram_Nw] using Fm.window
  span := by simpa only [gram_Λ] using Fm.span
  trunc := by
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun T => ?_)).trans_isLittleO Fm.defect
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (gram_Etr_nonneg _)]
    exact (gram_Etr _).trans (le_abs_self _)
  kernel := by simpa only [gram_k] using Fm.kernel

end K7aux
end ZetaS
