/-
Node K0 (track K) — every ZeroFrame yields a GramData with the same Ĝ, N(I′), Λ, kernel and s₁ = #{m = 1}
(ssec:zeta-setting "The split"), CORRECTED STATEMENT (L4_1, 28 Sep 2026; lead ruling: replace `HEq` by a reindexing).

Statement change: the skeleton's `HEq D.Gt F.Gt` is replaced by `D.Gt = reindex (finCongr h) (finCongr h) F.Gt` with
`h : F.d = D.d`; and the construction is exposed (what cor:oll-SC, node K7, needs to pinch M = VᵀV onto the simple
block): the columns of `D.V` are the columns of `F.U` at the simple sites, in increasing order (`e` strictly monotone,
`F.m (e j) = 1`). All other conjuncts are the skeleton's.

Construction: V = the columns of U at the simple sites (order embedding e), P1 = VVᵀ, Qp = Ĝ − P1 = U diag(m·1_{m≥2}) Uᵀ
+ Qoff, s₂ = #{m ≥ 2}, p = F.p, x = F.x ∘ e, Etr = F.Etr on the simple sites. Facts: (AF1) tr P1 = Σ_simple (1 − δ) ≤ s₁;
rank P1 ≤ s₁; (AF2) n₊(Qp) ≤ rank(U diag(m·1_{m≥2}) Uᵀ) + n₊(Qoff) ≤ s₂ + p (trunk `posIndex_add_le`);
count s₁ + 2s₂ + 2p ≤ Σ m + Noff. Level A.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.SpecHelpers
import ZetaS.SigmaDist.A8_SigmaDistAbstract
import Zeta23.LinAlg.Inertia

open Matrix RHLinalg Finset

namespace ZetaS

namespace K0aux

variable (F : ZeroFrame)

def Ssim : Finset (Fin F.n) := univ.filter fun i => F.m i = 1
def eS : Fin (Ssim F).card ↪o Fin F.n := (Ssim F).orderEmbOfFin rfl
def Vs : Matrix (Fin F.d) (Fin (Ssim F).card) ℝ := F.U.submatrix id (eS F)
def w1 (i : Fin F.n) : ℝ := if F.m i = 1 then 1 else 0
def wN (i : Fin F.n) : ℝ := if F.m i = 1 then 0 else (F.m i : ℝ)

lemma sum_eS (g : Fin F.n → ℝ) : ∑ j, g (eS F j) = ∑ i ∈ Ssim F, g i := by
  have hmap : (univ : Finset (Fin (Ssim F).card)).map (eS F).toEmbedding = Ssim F := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact (Ssim F).orderEmbOfFin_mem rfl i
    · intro hx
      have : x ∈ Set.range (eS F) := by rw [eS, Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hi⟩
  conv_rhs => rw [← hmap]
  rw [Finset.sum_map]
  rfl

lemma eS_simple (j : Fin (Ssim F).card) : F.m (eS F j) = 1 := by
  have h := (Ssim F).orderEmbOfFin_mem rfl j
  exact (Finset.mem_filter.1 h).2

lemma Vs_mul : Vs F * (Vs F)ᵀ = F.U * diagonal (w1 F) * F.Uᵀ := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Vs, submatrix_apply, transpose_apply, id]
  rw [sum_eS F (fun i => F.U a i * F.U b i)]
  simp only [Ssim, Finset.sum_filter, w1]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

lemma Gt_split : F.Gt = Vs F * (Vs F)ᵀ + (F.U * diagonal (wN F) * F.Uᵀ + F.Qoff) := by
  have : diagonal (fun i => (F.m i : ℝ)) = diagonal (w1 F) + diagonal (wN F) := by
    rw [Matrix.diagonal_add]; congr 1; ext i; unfold w1 wN; split_ifs with h <;> simp [h]
  rw [Vs_mul]
  unfold ZeroFrame.Gt
  rw [this, Matrix.mul_add, Matrix.add_mul, add_assoc]

lemma wN_nonneg (i : Fin F.n) : 0 ≤ wN F i := by unfold wN; split_ifs <;> positivity

lemma GN_psd : (F.U * diagonal (wN F) * F.Uᵀ).PosSemidef := A8b.psd_UDUt F _ (wN_nonneg F)

lemma rank_GN : (F.U * diagonal (wN F) * F.Uᵀ).rank ≤ #(univ.filter fun i => 2 ≤ F.m i) := by
  calc (F.U * diagonal (wN F) * F.Uᵀ).rank ≤ (F.U * diagonal (wN F)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (diagonal (wN F)).rank := Matrix.rank_mul_le_right _ _
    _ = Fintype.card {i // wN F i ≠ 0} := Matrix.rank_diagonal _
    _ = #(univ.filter fun i => wN F i ≠ 0) := Fintype.card_subtype _
    _ ≤ _ := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      unfold wN at hi
      split_ifs at hi with h
      · exact absurd rfl hi
      · have := F.one_le_m i; omega

lemma Cg_diag (i : Fin F.n) : (F.Uᵀ * F.U) i i = 1 - F.Etr i i := by
  rw [F.gram_eq]; simp [kerMat, F.k_zero]

end K0aux

open K0aux in
theorem frame_to_gram_fix (F : ZeroFrame) :
    ∃ D : GramData, ∃ h : F.d = D.d,
      D.Gt = Matrix.reindex (finCongr h) (finCongr h) F.Gt ∧ D.Nw = F.Nw ∧
      D.s1 = #(univ.filter fun i => F.m i = 1) ∧ D.k = F.k ∧ D.Λ = F.Λ ∧
      RHLinalg.rtrace D.Etr ≤ RHLinalg.rtrace F.Etr ∧
      ∃ e : Fin D.s1 → Fin F.n, StrictMono e ∧ (∀ j, F.m (e j) = 1) ∧
        D.V = Matrix.reindex (finCongr h) (Equiv.refl _) (F.U.submatrix id e) := by
  classical
  -- the pieces
  have hP1psd : (Vs F * (Vs F)ᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose (Vs F)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hGtH : F.Gt.IsHermitian := by
    have h1 := (A8b.psd_UDUt F (fun i => (F.m i : ℝ)) (fun i => Nat.cast_nonneg _)).isHermitian
    exact h1.add F.Qoff_herm
  have hQpH : (F.Gt - Vs F * (Vs F)ᵀ).IsHermitian := hGtH.sub hP1psd.isHermitian
  have hQp_eq : F.Gt - Vs F * (Vs F)ᵀ = F.U * diagonal (wN F) * F.Uᵀ + F.Qoff := by
    rw [Gt_split F]; abel
  have hnplus : posIndex hQpH ≤ #(univ.filter fun i => 2 ≤ F.m i) + F.p := by
    rw [posIndex_congr hQp_eq hQpH ((GN_psd F).isHermitian.add F.Qoff_herm)]
    refine (posIndex_add_le (GN_psd F).isHermitian F.Qoff_herm).trans (add_le_add ?_ F.nplus_off)
    rw [posIndex_eq_rank_of_posSemidef (GN_psd F)]; exact rank_GN F
  have hrank : (Vs F * (Vs F)ᵀ).rank ≤ (Ssim F).card :=
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  have hdelta : ∀ i, 0 ≤ F.Etr i i := fun i => F.Etr_psd.diag_nonneg
  have htr : rtrace (Vs F * (Vs F)ᵀ) ≤ (Ssim F).card := by
    unfold rtrace
    rw [RCLike.re_to_real, Matrix.trace_mul_comm]
    have : ((Vs F)ᵀ * Vs F).trace = ∑ j, (1 - F.Etr (eS F j) (eS F j)) := by
      simp only [Matrix.trace, Matrix.diag]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Cg_diag F]; simp [Vs, mul_apply]
    rw [this, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : 0 ≤ ∑ j, F.Etr (eS F j) (eS F j) := Finset.sum_nonneg fun j _ => hdelta _
    linarith
  have hcount : (Ssim F).card + 2 * #(univ.filter fun i => 2 ≤ F.m i) + 2 * F.p ≤ F.Nw := by
    have h1 : ∑ i, (if F.m i = 1 then 1 else 2) ≤ ∑ i, F.m i :=
      Finset.sum_le_sum fun i _ => by have := F.one_le_m i; split_ifs <;> omega
    have h2 : ∑ i, (if F.m i = 1 then 1 else 2) = (Ssim F).card + 2 * #(univ.filter fun i => 2 ≤ F.m i) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one]
      have : (univ.filter fun i => ¬ F.m i = 1) = univ.filter fun i => 2 ≤ F.m i := by
        apply Finset.filter_congr; intro i _; have := F.one_le_m i; omega
      rw [this]; unfold Ssim; ring
    have h3 := F.Noff_ge; have h4 := F.p1_le
    unfold ZeroFrame.Nw
    omega
  have hgram : (Vs F)ᵀ * Vs F = kerMat F.k (fun j => F.x (eS F j)) - F.Etr.submatrix (eS F) (eS F) := by
    have : (Vs F)ᵀ * Vs F = (F.Uᵀ * F.U).submatrix (eS F) (eS F) := by
      ext a b; simp [Vs, mul_apply]
    rw [this, F.gram_eq]; ext a b; simp [kerMat]
  let D : GramData :=
    { d := F.d
      P1 := Vs F * (Vs F)ᵀ
      Qp := F.Gt - Vs F * (Vs F)ᵀ
      s1 := (Ssim F).card
      s2 := #(univ.filter fun i => 2 ≤ F.m i)
      p := F.p
      Nw := F.Nw
      P1_psd := hP1psd
      Qp_herm := hQpH
      rank_P1 := hrank
      tr_P1 := htr
      nplus_Qp := hnplus
      count := hcount
      V := Vs F
      P1_eq := rfl
      x := fun j => F.x (eS F j)
      x_mono := F.x_mono.comp (eS F).strictMono
      k := F.k
      k_zero := F.k_zero
      k_even := F.k_even
      k_posDef := F.k_posDef
      Etr := F.Etr.submatrix (eS F) (eS F)
      Etr_psd := F.Etr_psd.submatrix _
      gram_eq := hgram
      Λ := F.Λ
      Λ_nonneg := F.Λ_nonneg
      x_span := fun i j => F.x_span _ _ }
  refine ⟨D, rfl, ?_, rfl, rfl, rfl, rfl, ?_, eS F, (eS F).strictMono, eS_simple F, ?_⟩
  · show Vs F * (Vs F)ᵀ + (F.Gt - Vs F * (Vs F)ᵀ) = _
    simp <;> rfl
  · show rtrace (F.Etr.submatrix (eS F) (eS F)) ≤ rtrace F.Etr
    unfold rtrace
    simp only [RCLike.re_to_real, Matrix.trace, Matrix.diag, submatrix_apply]
    rw [sum_eS F (fun i => F.Etr i i)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hdelta i
  · show Vs F = _
    simp [Vs] <;> rfl

end ZetaS

namespace ZetaS

/-- **Node K0** under the node's original name `frame_to_gram`, with the statement change ACCEPTED by the lead (28 Sep 2026):
the statement of `frame_to_gram_fix` (the reindexing and the exposed column map in place of `HEq`); the skeleton statement is withdrawn. Integrated by L0_1. -/
alias frame_to_gram := frame_to_gram_fix

end ZetaS
