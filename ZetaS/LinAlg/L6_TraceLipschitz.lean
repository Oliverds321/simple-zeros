/-
Node L6 (track L) — the Lidskii step of lem:zeta-transfer (l.478–480) in the form it is used (Ê ⪰ 0, so
A = K_int ⪰ B = M°_int): for A, B ⪰ 0 with A − B ⪰ 0 and f L_f-Lipschitz on [0,∞),
"|tr f(A) − tr f(B)| ≤ L_f · tr(A − B)" (Weyl monotonicity of sorted eigenvalues; no full Lidskii needed).

Proof (L2_1).
  (1) `posIndexAbove_mono`: `A ⪰ B` ⇒ `n₊^θ(B) ≤ n₊^θ(A)` for every θ: on `W = range (B − θ)₊` (dim `n₊^θ(B)`,
      trunk `finrank_range_truncPos`) the form of `B`, hence of `A`, exceeds `θ‖x‖²`, so `A − θI` is positive definite
      on `W` and `dim W ≤ n₊(A − θI) = n₊^θ(A)` (trunk Sylvester `finrank_le_posIndex_of_posDefOn`; the eigenvalues of
      `A − θI` are `λᵢ − θ` by `SpecHelpers.eigenvalues_map_eq_of_conj`).
  (2) `weyl_mono`: sorted eigenvalues `bₖ ≤ aₖ` (if `aₖ < bₖ`, θ = aₖ gives `n₊^θ(B) ≥ k+1 > k ≥ n₊^θ(A)`).
  (3) `|Σ f(aₖ) − Σ f(bₖ)| ≤ Σ L|aₖ − bₖ| = L Σ(aₖ − bₖ) = L tr(A − B)`.
-/
import ZetaS.Interfaces
import Zeta23.LinAlg.Sylvester
import ZetaS.LinAlg.SpecHelpers

open Matrix RHLinalg Finset

namespace ZetaS

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma posIndexAbove_eq_posIndex_sub {A : Matrix n n ℝ} (hA : A.IsHermitian) (θ : ℝ)
    (hA' : (A - θ • (1 : Matrix n n ℝ)).IsHermitian) :
    posIndex hA' = posIndexAbove hA θ := by
  set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hD : diagonal (fun i => ((hA.eigenvalues i - θ : ℝ) : ℝ))
      = diagonal (RCLike.ofReal ∘ hA.eigenvalues) - θ • (1 : Matrix n n ℝ) := by
    rw [smul_one_eq_diagonal, diagonal_sub]; congr 1
  have hAeq : A - θ • (1 : Matrix n n ℝ)
      = U * diagonal (fun i => ((hA.eigenvalues i - θ : ℝ) : ℝ)) * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [hD, mul_sub, sub_mul, Matrix.mul_smul, mul_one, Matrix.smul_mul, hUU]
  have hmap := eigenvalues_map_eq_of_conj hA' hU _ hAeq
  unfold posIndex posIndexAbove
  rw [card_filter_eq_of_map_eq hmap (fun x => 0 < x)]
  congr 1; ext i; simp only [mem_filter, mem_univ, true_and]; exact sub_pos

private lemma posIndexAbove_mono {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A - B).PosSemidef) (θ : ℝ) :
    posIndexAbove hB θ ≤ posIndexAbove hA θ := by
  have h1 : (θ • (1 : Matrix n n ℝ)).IsHermitian := by
    simp [IsHermitian]
  have hA' : (A - θ • (1 : Matrix n n ℝ)).IsHermitian := hA.sub h1
  set W := LinearMap.range (specMap hB (fun t => (t - θ)⁺)).mulVecLin
  have hdimW : Module.finrank ℝ W = posIndexAbove hB θ := finrank_range_truncPos hB θ
  have hgt := hermForm_gt_on_range_truncPos hB θ
  have hform1 : ∀ x : n → ℝ, hermForm (θ • (1 : Matrix n n ℝ)) x = θ * ∑ i, ‖x i‖ ^ 2 := by
    intro x
    rw [← hermForm_one x]
    unfold hermForm
    simp [smul_mulVec, dotProduct_smul]
  have hpos : PosDefOn (A - θ • (1 : Matrix n n ℝ)) W := by
    intro x hxW hne
    have h2 := hgt x hxW hne
    have h3 := hermForm_nonneg_of_posSemidef hAB x
    rw [hermForm_sub] at h3 ⊢
    rw [hform1]
    linarith
  calc posIndexAbove hB θ = Module.finrank ℝ W := hdimW.symm
    _ ≤ posIndex hA' := finrank_le_posIndex_of_posDefOn hA' hpos
    _ = posIndexAbove hA θ := posIndexAbove_eq_posIndex_sub hA θ hA'

/-- Weyl monotonicity: `A − B ⪰ 0` ⇒ `λₖ↓(B) ≤ λₖ↓(A)` for every `k`. -/
private lemma weyl_mono {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A - B).PosSemidef) (k : Fin (Fintype.card n)) :
    hB.eigenvalues₀ k ≤ hA.eigenvalues₀ k := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  set θ := hA.eigenvalues₀ k
  have hmono := posIndexAbove_mono hA hB hAB θ
  unfold posIndexAbove at hmono
  rw [card_eigenvalues_reindex hB (θ < ·), card_eigenvalues_reindex hA (θ < ·)] at hmono
  have hBbig : Finset.Iic k ⊆ ({l | θ < hB.eigenvalues₀ l} : Finset _) := by
    intro l hl
    rw [Finset.mem_Iic] at hl
    simp only [mem_filter, mem_univ, true_and]
    exact lt_of_lt_of_le hlt (hB.eigenvalues₀_antitone hl)
  have hAsmall : ({l | θ < hA.eigenvalues₀ l} : Finset _) ⊆ Finset.Iio k := by
    intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl
    rw [Finset.mem_Iio]
    by_contra hkl
    rw [not_lt] at hkl
    exact absurd (hA.eigenvalues₀_antitone hkl) (not_le.mpr hl)
  have c1 := card_le_card hBbig
  have c2 := card_le_card hAsmall
  rw [Fin.card_Iic] at c1
  rw [Fin.card_Iio] at c2
  omega

theorem trFun_sub_le_of_psd_le {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : (A - B).PosSemidef) {f : ℝ → ℝ} {Lf : ℝ}
    (hLf : 0 ≤ Lf) (hf : ∀ x y, 0 ≤ x → 0 ≤ y → |f x - f y| ≤ Lf * |x - y|) :
    |trFun hA.isHermitian f - trFun hB.isHermitian f| ≤ Lf * rtrace (A - B) := by
  set a := hA.isHermitian.eigenvalues₀
  set b := hB.isHermitian.eigenvalues₀
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    rw [show a k = hA.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hA.isHermitian k).symm]
    exact hA.eigenvalues_nonneg _
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    rw [show b k = hB.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hB.isHermitian k).symm]
    exact hB.eigenvalues_nonneg _
  have hba : ∀ k, b k ≤ a k := weyl_mono hA.isHermitian hB.isHermitian hAB
  have hfA : trFun hA.isHermitian f = ∑ k, f (a k) := sum_eigenvalues_reindex hA.isHermitian f
  have hfB : trFun hB.isHermitian f = ∑ k, f (b k) := sum_eigenvalues_reindex hB.isHermitian f
  have htr : rtrace (A - B) = ∑ k, a k - ∑ k, b k := by
    have hsa : ∑ i, hA.isHermitian.eigenvalues i = ∑ k, a k := sum_eigenvalues_reindex hA.isHermitian id
    have hsb : ∑ i, hB.isHermitian.eigenvalues i = ∑ k, b k := sum_eigenvalues_reindex hB.isHermitian id
    rw [rtrace_sub, rtrace_eq_sum_eigenvalues hA.isHermitian, rtrace_eq_sum_eigenvalues hB.isHermitian,
      hsa, hsb]
  rw [hfA, hfB, htr, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have := hf (a k) (b k) (ha0 k) (hb0 k)
  rwa [abs_of_nonneg (sub_nonneg.mpr (hba k))] at this

end ZetaS
