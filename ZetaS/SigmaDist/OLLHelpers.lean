/-
OLLHelpers (L4_1, 28 Sep 2026) — linear-algebra and bookkeeping helpers for node A7 (thm:sigd-OLL).
  * `trFun_congr`, `trFun_reindex`  : tr f depends only on the matrix, and is invariant under reindexing.
  * `eig_le_of_form`                : a quadratic-form bound `yᵀAy ≤ c‖y‖²` bounds every eigenvalue.
  * `frobSq_eq_sum`                 : `‖X‖² = Σ X_ij²` over ℝ.
  * `psd_entry_sq_le`               : `A ⪰ 0` ⇒ `A_ij² ≤ A_ii A_jj`.
  * `sum_orderEmb`                  : sums over `Fin #S` through `S.orderEmbOfFin` are sums over `S`.
-/
import ZetaS.Interfaces

open Matrix RHLinalg Finset

namespace ZetaS
namespace OLL

lemma trFun_congr {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ} (h : A = B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) : trFun hA f = trFun hB f := by
  subst h; rfl

lemma trFun_reindex {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) {A : Matrix n n ℝ} (hA : A.IsHermitian) (hB : (reindex e e A).IsHermitian) (f : ℝ → ℝ) :
    trFun hB f = trFun hA f := by
  have h1 := hA.roots_charpoly_eq_eigenvalues
  have h2 := hB.roots_charpoly_eq_eigenvalues
  rw [charpoly_reindex] at h2
  have h3 : Multiset.map hB.eigenvalues univ.val = Multiset.map hA.eigenvalues univ.val := by
    have := congrArg (Multiset.map RCLike.re) (h2.symm.trans h1)
    simpa [Multiset.map_map, Function.comp_def] using this
  unfold trFun
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  change (Multiset.map (f ∘ hB.eigenvalues) univ.val).sum = (Multiset.map (f ∘ hA.eigenvalues) univ.val).sum
  rw [← Multiset.map_map, ← Multiset.map_map, h3]

lemma eig_le_of_form {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ y : n → ℝ, y ⬝ᵥ (A *ᵥ y) ≤ c * ∑ i, y i ^ 2) (i : n) : hA.eigenvalues i ≤ c := by
  rw [hA.eigenvalues_eq i]
  have hn : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hs : ∑ j, (hA.eigenvectorBasis i) j ^ 2 = 1 := by
    have := EuclideanSpace.norm_eq (hA.eigenvectorBasis i)
    rw [hn] at this
    have h2 : (1 : ℝ) = ∑ j, ‖(hA.eigenvectorBasis i) j‖ ^ 2 := by
      have h0 : 0 ≤ ∑ j, ‖(hA.eigenvectorBasis i) j‖ ^ 2 := by positivity
      have e1 := Real.sq_sqrt h0
      rw [← this, one_pow] at e1
      exact e1
    rw [h2]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  have := h (hA.eigenvectorBasis i)
  simp only [star_trivial, RCLike.re_to_real]
  rw [hs, mul_one] at this
  exact this

lemma frobSq_eq_sum {n : Type*} [Fintype n] (X : Matrix n n ℝ) :
    frobSq X = ∑ i, ∑ j, X i j ^ 2 := by
  unfold frobSq
  simp only [RCLike.re_to_real, Matrix.trace, diag_apply, mul_apply, conjTranspose_apply, star_trivial]
  rw [Finset.sum_comm]
  simp [sq]

lemma psd_entry_sq_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) (i j : n) :
    A i j ^ 2 ≤ A i i * A j j := by
  have hsub := hA.submatrix ![i, j]
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have hsym : A j i = A i j := by
    have := hA.1.apply i j
    simpa using this
  rw [hsym] at hdet
  nlinarith

lemma sum_orderEmb {n : ℕ} (S : Finset (Fin n)) (g : Fin n → ℝ) :
    ∑ i : Fin S.card, g (S.orderEmbOfFin rfl i) = ∑ i ∈ S, g i := by
  have hmap : (univ : Finset (Fin S.card)).map (S.orderEmbOfFin rfl).toEmbedding = S := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact S.orderEmbOfFin_mem rfl i
    · intro hx
      have : x ∈ Set.range (S.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hi⟩
  conv_rhs => rw [← hmap]
  rw [Finset.sum_map]
  rfl

end OLL
end ZetaS
