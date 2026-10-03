/-
Node L4 (track L) — lem:zeta-pinch, sec_zeta.tex l.367–377 ("For G ⪰ 0 and any partition of the index set into
blocks, tr Ψ(G) ≥ Σ_b tr Ψ(G_bb)"), stated for any f convex on [0,∞): it is also the pinching step of cor:oll-SC
(l.697, f = Ψ_{1,t}) and of lem:sigd-tight (l.1309, f = (2 − x)₊², Ky Fan).
Proof (l.375–376): ⊕_b G_bb is the average of DGD over block-constant sign matrices D; X ↦ tr f(X) is convex and
unitarily invariant on PSD matrices. [Mathlib gap: convexity of the trace function — likely the hard part.]
Deps: Interfaces (trFun).

Proof formalised (L2_1) — no trace convexity needed, Jensen for the spectral measure instead:
  (J) `jensen_trace`: for `X ⪰ 0`, `f` convex on `[0,∞)`, and unit vectors `(w_p)` forming a Parseval frame
      (`Σ_p ⟨y, w_p⟩² = ‖y‖²`), `Σ_p f(⟨w_p, X w_p⟩) ≤ tr f(X)`: with `c_{pk} = ⟨u_k, w_p⟩` (`u_k` eigenvectors),
      `⟨w_p, X w_p⟩ = Σ_k c_{pk}² λ_k` is a convex combination (`Σ_k c_{pk}² = 1`), so Jensen (`ConvexOn.map_sum_le`)
      gives `f(⟨w_p, X w_p⟩) ≤ Σ_k c_{pk}² f(λ_k)`, and `Σ_p c_{pk}² = ‖u_k‖² = 1`.
  (P) the family `w_{b,j}` = the `j`-th eigenvector of `G_bb`, extended by zero, is an orthonormal basis of `ℝⁿ`
      with `⟨w_{b,j}, G w_{b,j}⟩ = λ_j(G_bb)`; so `Σ_b tr f(G_bb) = Σ_{b,j} f(⟨w_{b,j}, G w_{b,j}⟩) ≤ tr f(G)`.
-/
import ZetaS.Interfaces
import Zeta23.LinAlg.Sylvester
import ZetaS.LinAlg.CountHelpers

open Matrix RHLinalg Finset

namespace ZetaS

section Jensen

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma hermForm_eigen {X : Matrix n n ℝ} (hX : X.IsHermitian) (x : n → ℝ) :
    hermForm X x = ∑ k, hX.eigenvalues k * ((star (hX.eigenvectorUnitary : Matrix n n ℝ) *ᵥ x) k) ^ 2 := by
  have h := hermForm_specMap hX id x
  rw [specMap_id] at h
  unfold hermForm
  rw [h]
  simp [Real.norm_eq_abs, sq_abs]

private lemma parseval_U {X : Matrix n n ℝ} (hX : X.IsHermitian) (x : n → ℝ) :
    ∑ k, ((star (hX.eigenvectorUnitary : Matrix n n ℝ) *ᵥ x) k) ^ 2 = ∑ i, x i ^ 2 := by
  have h := sum_normSq_unitary_mulVec hX x
  simpa [Real.norm_eq_abs, sq_abs] using h

private lemma unitary_apply {X : Matrix n n ℝ} (hX : X.IsHermitian) (k j : n) :
    ∑ s, (hX.eigenvectorUnitary : Matrix n n ℝ) s k * (hX.eigenvectorUnitary : Matrix n n ℝ) s j
      = if k = j then 1 else 0 := by
  have hU : star (hX.eigenvectorUnitary : Matrix n n ℝ) * (hX.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have := congrFun (congrFun hU k) j
  simpa [mul_apply, star_apply, one_apply] using this

private lemma col_sq_sum {X : Matrix n n ℝ} (hX : X.IsHermitian) (k : n) :
    ∑ i, ((hX.eigenvectorUnitary : Matrix n n ℝ) i k) ^ 2 = 1 := by
  have := unitary_apply hX k k
  simpa [sq] using this

private lemma coord_eq_dot {X : Matrix n n ℝ} (hX : X.IsHermitian) (x : n → ℝ) (k : n) :
    (star (hX.eigenvectorUnitary : Matrix n n ℝ) *ᵥ x) k
      = (fun i => (hX.eigenvectorUnitary : Matrix n n ℝ) i k) ⬝ᵥ x := by
  simp [mulVec, dotProduct, star_apply]

/-- **Jensen trace inequality** for a Parseval frame of unit vectors. -/
private lemma jensen_trace {P : Type*} [Fintype P] {X : Matrix n n ℝ} (hX : X.PosSemidef)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f) (w : P → n → ℝ)
    (hunit : ∀ p, ∑ i, w p i ^ 2 = 1)
    (hpars : ∀ y : n → ℝ, ∑ p, (y ⬝ᵥ w p) ^ 2 = ∑ i, y i ^ 2) :
    ∑ p, f (hermForm X (w p)) ≤ trFun hX.isHermitian f := by
  set hXh := hX.isHermitian
  set U : Matrix n n ℝ := (hXh.eigenvectorUnitary : Matrix n n ℝ) with hU
  set c : P → n → ℝ := fun p k => (star U *ᵥ w p) k with hc
  have hsum1 : ∀ p, ∑ k, c p k ^ 2 = 1 := fun p => by
    rw [← hunit p]; exact parseval_U hXh (w p)
  have hjen : ∀ p, f (hermForm X (w p)) ≤ ∑ k, c p k ^ 2 * f (hXh.eigenvalues k) := by
    intro p
    have := hf.map_sum_le (t := univ) (w := fun k => c p k ^ 2) (p := hXh.eigenvalues)
      (fun k _ => sq_nonneg _) (hsum1 p) (fun k _ => Set.mem_Ici.mpr (hX.eigenvalues_nonneg k))
    simp only [smul_eq_mul] at this
    rw [hermForm_eigen hXh]
    have e : ∑ k, hXh.eigenvalues k * c p k ^ 2 = ∑ k, c p k ^ 2 * hXh.eigenvalues k :=
      sum_congr rfl fun k _ => mul_comm _ _
    rw [e]; exact this
  have hcol : ∀ k, ∑ p, c p k ^ 2 = 1 := by
    intro k
    have h1 := hpars (fun i => U i k)
    have h2 : ∀ p, c p k = (fun i => U i k) ⬝ᵥ w p := fun p => coord_eq_dot hXh (w p) k
    simp only [h2]
    rw [h1]; exact col_sq_sum hXh k
  calc ∑ p, f (hermForm X (w p)) ≤ ∑ p, ∑ k, c p k ^ 2 * f (hXh.eigenvalues k) :=
        sum_le_sum fun p _ => hjen p
    _ = ∑ k, (∑ p, c p k ^ 2) * f (hXh.eigenvalues k) := by
        rw [Finset.sum_comm]; simp [Finset.sum_mul]
    _ = trFun hXh f := by simp [hcol, trFun]

end Jensen

theorem trFun_pinch {n β : Type*} [Fintype n] [DecidableEq n] [Fintype β] [DecidableEq β]
    {G : Matrix n n ℝ} (hG : G.PosSemidef) (blk : n → β) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Set.Ici 0) f) :
    ∑ b, trFun ((hG.submatrix (fun i : {i // blk i = b} => (i : n))).isHermitian) f
      ≤ trFun hG.isHermitian f := by
  classical
  set hB := fun b : β => (hG.submatrix (fun i : {i // blk i = b} => (i : n))).isHermitian with hBdef
  set Ub : ∀ b : β, Matrix {i // blk i = b} {i // blk i = b} ℝ :=
    fun b => ((hB b).eigenvectorUnitary : Matrix _ _ ℝ) with hUb
  set w : (Σ b : β, {i // blk i = b}) → n → ℝ :=
    fun p i => if h : blk i = p.1 then Ub p.1 ⟨i, h⟩ p.2 else 0 with hw
  -- sums of functions supported on a block
  have hsumblk : ∀ (b : β) (g : {i // blk i = b} → ℝ),
      ∑ i, (if h : blk i = b then g ⟨i, h⟩ else 0) = ∑ s, g s := by
    intro b g
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => blk i = b)]
    have h2 : ∑ i : {i // ¬ blk i = b}, (if h : blk (i : n) = b then g ⟨i, h⟩ else 0) = 0 :=
      sum_eq_zero fun i _ => dif_neg i.2
    rw [h2, add_zero]
    exact sum_congr rfl fun s _ => by rw [dif_pos s.2]
  have hunit : ∀ p, ∑ i, w p i ^ 2 = 1 := by
    rintro ⟨b, j⟩
    have e : ∀ i, w ⟨b, j⟩ i ^ 2 = if h : blk i = b then (Ub b ⟨i, h⟩ j) ^ 2 else 0 := fun i => by
      simp only [hw]; split_ifs <;> simp
    rw [sum_congr rfl (fun i _ => e i), hsumblk b (fun s => (Ub b s j) ^ 2)]
    exact col_sq_sum (hB b) j
  have hdot : ∀ (y : n → ℝ) (b : β) (j : {i // blk i = b}),
      y ⬝ᵥ w ⟨b, j⟩ = (star (Ub b) *ᵥ (fun s : {i // blk i = b} => y s)) j := by
    intro y b j
    rw [coord_eq_dot (hB b)]
    simp only [dotProduct]
    have e : ∀ i, y i * w ⟨b, j⟩ i = if h : blk i = b then Ub b ⟨i, h⟩ j * y i else 0 := fun i => by
      simp only [hw]; split_ifs <;> simp [mul_comm]
    rw [sum_congr rfl (fun i _ => e i), hsumblk b (fun s => Ub b s j * y s)]
  have hpars : ∀ y : n → ℝ, ∑ p, (y ⬝ᵥ w p) ^ 2 = ∑ i, y i ^ 2 := by
    intro y
    rw [Fintype.sum_sigma]
    simp only [hdot]
    have e : ∀ b, ∑ j : {i // blk i = b}, ((star (Ub b) *ᵥ (fun s : {i // blk i = b} => y s)) j) ^ 2
        = ∑ s : {i // blk i = b}, y s ^ 2 := fun b => parseval_U (hB b) _
    simp only [e]
    exact Fintype.sum_fiberwise blk (fun i => y i ^ 2)
  have hform : ∀ (b : β) (j : {i // blk i = b}), hermForm G (w ⟨b, j⟩) = (hB b).eigenvalues j := by
    intro b j
    set v : {i // blk i = b} → ℝ := fun s => Ub b s j with hv
    have hGw : ∀ i, (G *ᵥ w ⟨b, j⟩) i = ∑ s : {i // blk i = b}, G i s * v s := by
      intro i
      simp only [mulVec, dotProduct]
      have e : ∀ i', G i i' * w ⟨b, j⟩ i' = if h : blk i' = b then G i i' * Ub b ⟨i', h⟩ j else 0 :=
        fun i' => by simp only [hw]; split_ifs <;> simp
      rw [sum_congr rfl (fun i' _ => e i'), hsumblk b (fun s => G i s * Ub b s j)]
    have h1 : hermForm G (w ⟨b, j⟩)
        = hermForm (G.submatrix (fun i : {i // blk i = b} => (i : n)) (fun i => (i : n))) v := by
      rw [hermForm_real, hermForm_real]
      simp only [dotProduct]
      have e : ∀ i, w ⟨b, j⟩ i * (G *ᵥ w ⟨b, j⟩) i
          = if h : blk i = b then Ub b ⟨i, h⟩ j * ∑ s : {i // blk i = b}, G i s * v s else 0 := fun i => by
        rw [hGw]; simp only [hw]; split_ifs <;> simp
      rw [sum_congr rfl (fun i _ => e i), hsumblk b (fun s => Ub b s j * ∑ s' : {i // blk i = b}, G s s' * v s')]
      simp [mulVec, dotProduct, hv]
    rw [h1, hermForm_eigen (hB b)]
    have h2 : ∀ k, (star ((hB b).eigenvectorUnitary : Matrix {i // blk i = b} {i // blk i = b} ℝ) *ᵥ v) k
        = if k = j then 1 else 0 := by
      intro k
      rw [← unitary_apply (hB b) k j]
      simp [mulVec, dotProduct, star_apply, hv, hUb]
    simp only [h2]
    simp
  have hlhs : ∑ b, trFun (hB b) f = ∑ p, f (hermForm G (w p)) := by
    rw [Fintype.sum_sigma]
    refine sum_congr rfl fun b _ => ?_
    unfold trFun
    exact sum_congr rfl fun j _ => by rw [hform]
  have := jensen_trace hG hf w hunit hpars
  rw [← hlhs] at this
  exact this

end ZetaS
