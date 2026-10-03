/-
Node R1 (track L, scalars, M4) — the tree's matrices are `Matrix … ℂ` with real entries; GramData/ZeroFrame are real.
Trace, Frobenius norm and the inertia indices agree under `toC` (L1–L8 are over `RCLike 𝕜` and need no conversion).
-/
import ZetaS.InterfacesV2

open RHLinalg Matrix

namespace ZetaS

namespace R1aux

lemma rtrace_toC {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : rtrace (toC A) = rtrace A := by
  simp [rtrace, toC, Matrix.trace]

lemma conjTranspose_toC {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : (toC A)ᴴ = toC Aᴴ := by
  ext i j
  simp [toC, Matrix.conjTranspose_apply]

lemma toC_mul {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) : toC (A * B) = toC A * toC B := by
  unfold toC
  exact Matrix.map_mul (f := Complex.ofRealHom)

lemma frobSq_toC {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : frobSq (toC A) = frobSq A := by
  unfold frobSq
  rw [conjTranspose_toC, ← toC_mul]
  exact rtrace_toC (Aᴴ * A)

/-- the sorted eigenvalues of `toC A` are those of `A`. -/
lemma eigenvalues₀_toC {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hA' : (toC A).IsHermitian) : hA'.eigenvalues₀ = hA.eigenvalues₀ := by
  have hmap : (toC A).charpoly = A.charpoly.map Complex.ofRealHom := by
    rw [← Matrix.charpoly_map]; rfl
  have hcard : Multiset.card A.charpoly.roots = A.charpoly.natDegree := by
    rw [hA.roots_charpoly_eq_eigenvalues, Matrix.charpoly_natDegree_eq_dim]; simp
  have hroots : (toC A).charpoly.roots = A.charpoly.roots.map Complex.ofRealHom := by
    rw [hmap, Polynomial.roots_map_of_injective_of_card_eq_natDegree Complex.ofReal_injective hcard]
  have h1 := hA'.sort_roots_charpoly_eq_eigenvalues₀
  have h2 := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots, Multiset.map_map] at h1
  have e : (RCLike.re ∘ Complex.ofRealHom : ℝ → ℝ) = RCLike.re := by
    funext r; simp
  rw [e] at h1
  exact List.ofFn_injective (h1.symm.trans h2)

end R1aux

open R1aux

theorem realify {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hA' : (toC A).IsHermitian) :
    rtrace (toC A) = rtrace A ∧ frobSq (toC A) = frobSq A ∧ posIndex hA' = posIndex hA ∧
      negIndex hA' = negIndex hA := by
  refine ⟨rtrace_toC A, frobSq_toC A, ?_, ?_⟩
  · unfold posIndex
    rw [card_eigenvalues_reindex hA' (fun t => 0 < t), card_eigenvalues_reindex hA (fun t => 0 < t),
      eigenvalues₀_toC hA hA']
  · unfold negIndex
    rw [card_eigenvalues_reindex hA' (fun t => t < 0), card_eigenvalues_reindex hA (fun t => t < 0),
      eigenvalues₀_toC hA hA']

end ZetaS
