/-
KHelpers (L4_1, 28 Sep 2026) — shared helpers for the K-side nodes (K2, K5, K7). Namespace `ZetaS.KHelp`.
  * `trFun_congr`, `trFun_reindex`   : tr f depends only on the matrix, and is invariant under reindexing.
  * `psi_nonneg`, `psi_tangent_le`, `psi_convexOn` : Ψ ≥ 0 and Ψ convex (supremum of its tangents at s ≤ 2).
  * `trFun_nonneg`                   : tr f(X) ≥ 0 for X ⪰ 0 and f ≥ 0 on [0,∞).
  * `pinch_blocks`                   : pinching (L4) for a family of disjoint blocks given by injective maps
                                        `Fin m → Fin S`; the rest of the index set is discarded (f ≥ 0).
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L4_Pinching

open Matrix RHLinalg Finset

namespace ZetaS
namespace KHelp

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

/-- a positive-definite kernel with `k(0) = 1` is bounded by 1. -/
lemma kernel_abs_le_one {k : ℝ → ℝ} (hpd : IsPosDefKernel k) (hk0 : k 0 = 1) (t : ℝ) : |k t| ≤ 1 := by
  have h := psd_entry_sq_le (hpd 2 ![0, -t]) 0 1
  simp only [kerMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, sub_neg_eq_add,
    zero_add, hk0, mul_one] at h
  exact (sq_le_one_iff_abs_le_one _).mp h

/-- Ψ is 2-Lipschitz on [0, ∞). -/
lemma psi_lipschitz (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : |Psi x - Psi y| ≤ 2 * |x - y| := by
  unfold Psi
  rw [abs_le]
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonpos (by linarith)]
    split_ifs with h1 h2 h2 <;> constructor <;> nlinarith
  · rw [abs_of_nonneg (by linarith)]
    split_ifs with h1 h2 h2 <;> constructor <;> nlinarith

lemma localCert_mono {K : ℕ} {W : LocalWeights K} {k : ℝ → ℝ} {c c' : ℝ} (h : LocalCert k W c) (hc : c' ≤ c) :
    LocalCert k W c' := fun g hg => le_trans hc (h g hg)

lemma psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
  unfold Psi; split_ifs with h
  · exact sq_nonneg _
  · linarith

lemma psi_tangent_le {s : ℝ} (hs : s ≤ 2) (t : ℝ) : (s - 1) ^ 2 + 2 * (s - 1) * (t - s) ≤ Psi t := by
  unfold Psi; split_ifs with h
  · nlinarith [sq_nonneg (t - s)]
  · push_neg at h
    nlinarith [mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 h.le), sq_nonneg (s - 2)]

lemma psi_eq_tangent (z : ℝ) :
    Psi z = (min z 2 - 1) ^ 2 + 2 * (min z 2 - 1) * (z - min z 2) := by
  unfold Psi; split_ifs with h
  · rw [min_eq_left h]; ring
  · push_neg at h; rw [min_eq_right h.le]; ring

lemma psi_convexOn : ConvexOn ℝ (Set.Ici 0) Psi := by
  refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a * x + b * y
  set s := min z 2 with hs
  have hs2 : s ≤ 2 := min_le_right _ _
  rw [psi_eq_tangent z]
  have hx := psi_tangent_le hs2 x
  have hy := psi_tangent_le hs2 y
  have hlin : (s - 1) ^ 2 + 2 * (s - 1) * (z - s)
      = a * ((s - 1) ^ 2 + 2 * (s - 1) * (x - s)) + b * ((s - 1) ^ 2 + 2 * (s - 1) * (y - s)) := by
    have hb' : b = 1 - a := by linarith
    simp only [z, hb']; ring
  rw [← hs, hlin]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma trFun_nonneg {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℝ} (hX : X.PosSemidef)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ x → 0 ≤ f x) : 0 ≤ trFun hX.isHermitian f := by
  unfold trFun
  exact Finset.sum_nonneg fun i _ => hf0 _ (hX.eigenvalues_nonneg i)

/-- pinching onto disjoint blocks `e a : Fin m → Fin S` (`a ∈ J`), the rest discarded. -/
lemma pinch_blocks {S m : ℕ} {G : Matrix (Fin S) (Fin S) ℝ} (hG : G.PosSemidef) (J : Finset ℕ)
    (e : ℕ → Fin m → Fin S) (hinj : ∀ a ∈ J, Function.Injective (e a))
    (hdisj : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, e a i = e b j → a = b)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) (hf0 : ∀ x, 0 ≤ x → 0 ≤ f x) :
    ∑ a ∈ J, trFun (hG.submatrix (e a)).isHermitian f ≤ trFun hG.isHermitian f := by
  classical
  let blk : Fin S → Option J := fun i =>
    if h : ∃ a ∈ J, ∃ j, e a j = i then some ⟨h.choose, h.choose_spec.1⟩ else none
  have hp := trFun_pinch hG blk hf
  rw [Fintype.sum_option] at hp
  have hnone := trFun_nonneg (hG.submatrix (fun i : {i // blk i = none} => (i : Fin S))) hf0
  have hsome : ∀ b : J, trFun ((hG.submatrix (fun i : {i // blk i = some b} => (i : Fin S)))).isHermitian f
      = trFun (hG.submatrix (e b)).isHermitian f := by
    intro b
    have hblk : ∀ j, blk (e b j) = some b := by
      intro j
      have hex : ∃ a ∈ J, ∃ j', e a j' = e b j := ⟨b, b.2, j, rfl⟩
      simp only [blk, dif_pos hex]
      congr 1; apply Subtype.ext
      obtain ⟨j', hj'⟩ := hex.choose_spec.2
      exact hdisj _ hex.choose_spec.1 _ b.2 _ _ hj'
    let σ : Fin m → {i // blk i = some b} := fun j => ⟨e b j, hblk j⟩
    have hσ : Function.Bijective σ := by
      constructor
      · intro j j' h; exact hinj b b.2 (congrArg Subtype.val h)
      · rintro ⟨i, hi⟩
        have hi' := hi
        simp only [blk] at hi'
        split_ifs at hi' with h
        · have hb : h.choose = (b : ℕ) := congrArg Subtype.val (Option.some_injective _ hi')
          obtain ⟨j, hj⟩ := h.choose_spec.2
          refine ⟨j, Subtype.ext ?_⟩
          show e b j = i
          rw [← hb]; exact hj
    let E := Equiv.ofBijective σ hσ
    have hre : reindex E.symm E.symm (G.submatrix (fun i : {i // blk i = some b} => (i : Fin S)) (fun i : {i // blk i = some b} => (i : Fin S)))
        = G.submatrix (e b) (e b) := by
      ext j j'; rfl
    have hB : (reindex E.symm E.symm (G.submatrix (fun i : {i // blk i = some b} => (i : Fin S)) (fun i : {i // blk i = some b} => (i : Fin S)))).IsHermitian := by
      rw [hre]; exact (hG.submatrix (e b)).isHermitian
    rw [← trFun_reindex E.symm _ hB f, trFun_congr hre hB (hG.submatrix (e b)).isHermitian f]
  have hsum : ∑ b : J, trFun ((hG.submatrix (fun i : {i // blk i = some b} => (i : Fin S)))).isHermitian f
      = ∑ a ∈ J, trFun (hG.submatrix (e a)).isHermitian f := by
    rw [Finset.sum_congr rfl fun b _ => hsome b]
    exact Finset.sum_coe_sort J (fun a => trFun (hG.submatrix (e a)).isHermitian f)
  linarith

end KHelp
end ZetaS
