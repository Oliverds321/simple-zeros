/-
lean_work/L2_1/SpecHelpers.lean — spectral bookkeeping helpers (L2_1, 28 Sep 2026). Namespace `ZetaS`, public.

  * `eigenvalues_map_eq_of_conj` : if `A = U·diag(g)·U*` with `U*U = 1`, the eigenvalue multiset of `A` is that of `g`.
  * `card_filter_eq_of_map_eq`   : equal multisets ⇒ equal counts `#{i | q (f i)} = #{i | q (g i)}`.
  * `negIndex_eq_posIndex_neg`   : `n₋(A) = n₊(−A)`.
  * `posIndex_congr`             : `posIndex` only depends on the matrix.
-/
import ZetaS.Interfaces

open Matrix RHLinalg Finset

namespace ZetaS

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

open Polynomial in
lemma eigenvalues_map_eq_of_conj {A : Matrix n n 𝕜} (hA : A.IsHermitian) {U : Matrix n n 𝕜}
    (hU : star U * U = 1) (g : n → ℝ) (hAeq : A = U * diagonal (fun i => (g i : 𝕜)) * star U) :
    Multiset.map hA.eigenvalues univ.val = Multiset.map g univ.val := by
  have hchar : A.charpoly = (diagonal (fun i => (g i : 𝕜))).charpoly := by
    rw [hAeq, charpoly_mul_comm, ← mul_assoc, hU, one_mul]
  have h1 := hA.roots_charpoly_eq_eigenvalues
  rw [hchar, charpoly_diagonal, Polynomial.roots_prod _ _
    (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [roots_X_sub_C, Multiset.bind_singleton] at h1
  have h2 := congrArg (Multiset.map RCLike.re) h1
  simp only [Multiset.map_map, Function.comp_def, RCLike.ofReal_re] at h2
  exact h2.symm

omit [DecidableEq n] in
lemma card_filter_eq_of_map_eq {f g : n → ℝ}
    (h : Multiset.map f univ.val = Multiset.map g univ.val) (q : ℝ → Prop) [DecidablePred q] :
    #{i | q (f i)} = #{i | q (g i)} := by
  have key : ∀ φ : n → ℝ, #{i | q (φ i)} = Multiset.card ((Multiset.map φ univ.val).filter q) := by
    intro φ; rw [Multiset.filter_map, Multiset.card_map]; rfl
  rw [key f, key g, h]

lemma posIndex_congr {A B : Matrix n n 𝕜} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    posIndex hA = posIndex hB := by
  subst h; rfl

lemma negIndex_eq_posIndex_neg {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    negIndex hA = posIndex hA.neg := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hD : diagonal (fun i => ((-hA.eigenvalues i : ℝ) : 𝕜))
      = -diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [diagonal_neg]; congr 1; funext i; simp
  have hAeq : -A = U * diagonal (fun i => ((-hA.eigenvalues i : ℝ) : 𝕜)) * star U := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [hD, mul_neg, neg_mul]
  have hmap := eigenvalues_map_eq_of_conj hA.neg hU _ hAeq
  unfold negIndex posIndex
  rw [card_filter_eq_of_map_eq hmap (fun x => 0 < x)]
  congr 1; ext i; simp

end ZetaS
