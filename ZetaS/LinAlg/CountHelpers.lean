/-
lean_work/L2_1/CountHelpers.lean — eigenvalue counting over ℝ via the trunk's Sylvester tools (L2_1, 28 Sep 2026).
Namespace `ZetaS`, public. `n₊^θ(X) = posIndexAbove hX θ = #{λᵢ(X) > θ}`.

  * `hermForm_real`, `hermForm_smul_one`, `sum_norm_sq_real`
  * `posIndex_sub_smul_eq`      : `n₊(A − θI) = n₊^θ(A)`.
  * `finrank_le_posIndexAbove`  : a subspace on which `xᵀAx > θ‖x‖²` has dimension `≤ n₊^θ(A)`.
  * `posIndexAbove_mono_of_form`: `xᵀBx ≤ xᵀAx ∀x` ⇒ `n₊^θ(B) ≤ n₊^θ(A)`.
  * `weyl_mono_of_form`         : same hypothesis ⇒ sorted eigenvalues `λₖ↓(B) ≤ λₖ↓(A)` (Weyl monotonicity).
  * `le_eigenvalues₀_of_count`, `eigenvalues₀_le_of_count` : count bounds ⇒ bounds on sorted eigenvalues.
  * `hermForm_fromBlocks`, `posIndexAbove_fromBlocks_le` (`n₊^θ([[A,B],[C,D]]) ≤ n₊^θ(A) + |D|`, Cauchy interlacing,
    count form), `le_posIndexAbove_fromBlocks_smul` (`n₊^θ([[A,B],[C,ρI]]) ≥ |D|` for `θ < ρ`).
-/
import ZetaS.Interfaces
import Zeta23.LinAlg.Sylvester
import ZetaS.LinAlg.SpecHelpers

open Matrix RHLinalg Finset

namespace ZetaS

section Basic

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma hermForm_real (A : Matrix n n ℝ) (x : n → ℝ) : hermForm A x = x ⬝ᵥ (A *ᵥ x) := by
  simp [hermForm]

omit [DecidableEq n] in
lemma sum_norm_sq_real (x : n → ℝ) : ∑ i, ‖x i‖ ^ 2 = ∑ i, x i ^ 2 := by
  simp [Real.norm_eq_abs, sq_abs]

lemma hermForm_smul_one (θ : ℝ) (x : n → ℝ) :
    hermForm (θ • (1 : Matrix n n ℝ)) x = θ * ∑ i, ‖x i‖ ^ 2 := by
  rw [← hermForm_one x]
  unfold hermForm
  simp [smul_mulVec, dotProduct_smul]

lemma isHermitian_smul_one (θ : ℝ) : (θ • (1 : Matrix n n ℝ)).IsHermitian := by
  simp [IsHermitian]

lemma posIndex_sub_smul_eq {A : Matrix n n ℝ} (hA : A.IsHermitian) (θ : ℝ)
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

lemma finrank_le_posIndexAbove {A : Matrix n n ℝ} (hA : A.IsHermitian) (θ : ℝ)
    {W : Submodule ℝ (n → ℝ)} (hW : ∀ x ∈ W, x ≠ 0 → θ * ∑ i, ‖x i‖ ^ 2 < hermForm A x) :
    Module.finrank ℝ W ≤ posIndexAbove hA θ := by
  have hA' : (A - θ • (1 : Matrix n n ℝ)).IsHermitian := hA.sub (isHermitian_smul_one θ)
  have hpos : PosDefOn (A - θ • (1 : Matrix n n ℝ)) W := by
    intro x hx hne
    rw [hermForm_sub, hermForm_smul_one]
    linarith [hW x hx hne]
  exact (finrank_le_posIndex_of_posDefOn hA' hpos).trans_eq (posIndex_sub_smul_eq hA θ hA')

lemma posIndexAbove_mono_of_form {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hle : ∀ x, hermForm B x ≤ hermForm A x) (θ : ℝ) :
    posIndexAbove hB θ ≤ posIndexAbove hA θ := by
  rw [← finrank_range_truncPos hB θ]
  exact finrank_le_posIndexAbove hA θ fun x hx hne =>
    (hermForm_gt_on_range_truncPos hB θ x hx hne).trans_le (hle x)

/-- Count bounds ⇒ lower bound on sorted eigenvalues: if `n₊^θ(X) ≥ r` for all `θ < ρ`, then `λₗ↓(X) ≥ ρ` for `l < r`. -/
lemma le_eigenvalues₀_of_count {X : Matrix n n ℝ} (hX : X.IsHermitian) {ρ : ℝ} {r : ℕ}
    (hcount : ∀ θ < ρ, r ≤ posIndexAbove hX θ) (l : Fin (Fintype.card n)) (hl : (l : ℕ) < r) :
    ρ ≤ hX.eigenvalues₀ l := by
  by_contra hlt
  rw [not_le] at hlt
  have h := hcount _ hlt
  unfold posIndexAbove at h
  rw [card_eigenvalues_reindex hX (hX.eigenvalues₀ l < ·)] at h
  have hsub : ({k | hX.eigenvalues₀ l < hX.eigenvalues₀ k} : Finset _) ⊆ Finset.Iio l := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    rw [Finset.mem_Iio]
    by_contra hkl
    rw [not_lt] at hkl
    exact absurd (hX.eigenvalues₀_antitone hkl) (not_le.mpr hk)
  have := (h.trans (card_le_card hsub))
  rw [Fin.card_Iio] at this
  omega

/-- Count bounds ⇒ upper bound on sorted eigenvalues: if `n₊^θ(X) ≤ r + n₊^θ(A)` for all `θ`, then
`λ_{r+j}↓(X) ≤ λⱼ↓(A)`. -/
lemma eigenvalues₀_le_of_count {m : Type*} [Fintype m] [DecidableEq m] {X : Matrix n n ℝ} {A : Matrix m m ℝ}
    (hX : X.IsHermitian) (hA : A.IsHermitian) {r : ℕ}
    (hcount : ∀ θ, posIndexAbove hX θ ≤ r + posIndexAbove hA θ)
    (l : Fin (Fintype.card n)) (j : Fin (Fintype.card m)) (hlj : (l : ℕ) = r + j) :
    hX.eigenvalues₀ l ≤ hA.eigenvalues₀ j := by
  by_contra hlt
  rw [not_le] at hlt
  have h := hcount (hA.eigenvalues₀ j)
  unfold posIndexAbove at h
  rw [card_eigenvalues_reindex hX (hA.eigenvalues₀ j < ·),
    card_eigenvalues_reindex hA (hA.eigenvalues₀ j < ·)] at h
  have hbig : Finset.Iic l ⊆ ({k | hA.eigenvalues₀ j < hX.eigenvalues₀ k} : Finset _) := by
    intro k hk
    rw [Finset.mem_Iic] at hk
    simp only [mem_filter, mem_univ, true_and]
    exact lt_of_lt_of_le hlt (hX.eigenvalues₀_antitone hk)
  have hsmall : ({k | hA.eigenvalues₀ j < hA.eigenvalues₀ k} : Finset _) ⊆ Finset.Iio j := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    rw [Finset.mem_Iio]
    by_contra hkl
    rw [not_lt] at hkl
    exact absurd (hA.eigenvalues₀_antitone hkl) (not_le.mpr hk)
  have c1 := card_le_card hbig
  have c2 := card_le_card hsmall
  rw [Fin.card_Iic] at c1
  rw [Fin.card_Iio] at c2
  omega

/-- Weyl monotonicity: `xᵀBx ≤ xᵀAx` for all `x` ⇒ `λₖ↓(B) ≤ λₖ↓(A)`. -/
lemma weyl_mono_of_form {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hle : ∀ x, hermForm B x ≤ hermForm A x) (k : Fin (Fintype.card n)) :
    hB.eigenvalues₀ k ≤ hA.eigenvalues₀ k := by
  have h := eigenvalues₀_le_of_count (r := 0) hB hA
    (fun θ => by rw [zero_add]; exact posIndexAbove_mono_of_form hA hB hle θ) k k (by simp)
  exact h

end Basic

section Blocks

variable {m o : Type*} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

lemma hermForm_fromBlocks (A : Matrix m m ℝ) (B : Matrix m o ℝ) (C : Matrix o m ℝ) (D : Matrix o o ℝ)
    (x : m ⊕ o → ℝ) :
    hermForm (fromBlocks A B C D) x
      = hermForm A (x ∘ Sum.inl) + (x ∘ Sum.inl) ⬝ᵥ (B *ᵥ (x ∘ Sum.inr))
        + (x ∘ Sum.inr) ⬝ᵥ (C *ᵥ (x ∘ Sum.inl)) + hermForm D (x ∘ Sum.inr) := by
  rw [hermForm_real, hermForm_real, hermForm_real, fromBlocks_mulVec]
  conv_lhs => rw [← Sum.elim_comp_inl_inr x]
  rw [sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_add]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  ring

omit [DecidableEq m] [DecidableEq o] in
lemma sum_norm_sq_sum (x : m ⊕ o → ℝ) :
    ∑ i, ‖x i‖ ^ 2 = ∑ i, ‖(x ∘ Sum.inl) i‖ ^ 2 + ∑ i, ‖(x ∘ Sum.inr) i‖ ^ 2 := by
  rw [Fintype.sum_sum_type]; rfl

/-- Cauchy interlacing, count form: `n₊^θ([[A,B],[C,D]]) ≤ n₊^θ(A) + |o|`. -/
lemma posIndexAbove_fromBlocks_le {A : Matrix m m ℝ} {B : Matrix m o ℝ} {C : Matrix o m ℝ}
    {D : Matrix o o ℝ} (hX : (fromBlocks A B C D).IsHermitian) (hA : A.IsHermitian) (θ : ℝ) :
    posIndexAbove hX θ ≤ Fintype.card o + posIndexAbove hA θ := by
  set X := fromBlocks A B C D
  set V := LinearMap.range (specMap hX (fun t => (t - θ)⁺)).mulVecLin
  have hdimV : Module.finrank ℝ V = posIndexAbove hX θ := finrank_range_truncPos hX θ
  have hgt := hermForm_gt_on_range_truncPos hX θ
  let π₂ : (m ⊕ o → ℝ) →ₗ[ℝ] (o → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inr
  let π₁ : (m ⊕ o → ℝ) →ₗ[ℝ] (m → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inl
  let p : V →ₗ[ℝ] (o → ℝ) := π₂.domRestrict V
  have h1 := LinearMap.finrank_range_add_finrank_ker p
  have h2 : Module.finrank ℝ (LinearMap.range p) ≤ Fintype.card o :=
    (Submodule.finrank_le _).trans_eq (Module.finrank_fintype_fun_eq_card ℝ)
  let q : (LinearMap.ker p) →ₗ[ℝ] (m → ℝ) := π₁ ∘ₗ V.subtype ∘ₗ (LinearMap.ker p).subtype
  have hker : ∀ y : LinearMap.ker p, ((y : V) : m ⊕ o → ℝ) ∘ Sum.inr = 0 := by
    intro y
    have := y.2
    rw [LinearMap.mem_ker] at this
    exact this
  have hq0 : ∀ y, q y = 0 → y = 0 := by
    intro y hy
    have h1' : ((y : V) : m ⊕ o → ℝ) ∘ Sum.inl = 0 := hy
    have h2' := hker y
    apply Subtype.ext; apply Subtype.ext
    funext i
    cases i with
    | inl i => exact congrFun h1' i
    | inr i => exact congrFun h2' i
  have hq_inj : Function.Injective q := fun y₁ y₂ h => by
    have := hq0 (y₁ - y₂) ((q.map_sub y₁ y₂).trans (by rw [h, sub_self]))
    exact sub_eq_zero.mp this
  have h3 : Module.finrank ℝ (LinearMap.range q) = Module.finrank ℝ (LinearMap.ker p) :=
    LinearMap.finrank_range_of_inj hq_inj
  have h4 : Module.finrank ℝ (LinearMap.range q) ≤ posIndexAbove hA θ := by
    refine finrank_le_posIndexAbove hA θ ?_
    rintro _ ⟨y, rfl⟩ hne
    set x : m ⊕ o → ℝ := ((y : V) : m ⊕ o → ℝ) with hx
    have hxV : x ∈ V := (y : V).2
    have hqy : q y = x ∘ Sum.inl := rfl
    have hx0 : x ≠ 0 := by
      intro h; apply hne; rw [hqy, h]; rfl
    have hg := hgt x hxV hx0
    rw [hermForm_fromBlocks, hker y, sum_norm_sq_sum, hker y] at hg
    rw [hqy]
    simpa [hermForm] using hg
  have hV : Module.finrank ℝ V = posIndexAbove hX θ := hdimV
  omega

/-- `n₊^θ([[A,B],[C,ρI]]) ≥ |o|` for `θ < ρ` (the subspace `0 ⊕ ℝ^o`). -/
lemma le_posIndexAbove_fromBlocks_smul {A : Matrix m m ℝ} {B : Matrix m o ℝ} {C : Matrix o m ℝ} {ρ θ : ℝ}
    (hX : (fromBlocks A B C (ρ • (1 : Matrix o o ℝ))).IsHermitian) (hθ : θ < ρ) :
    Fintype.card o ≤ posIndexAbove hX θ := by
  let ι : (o → ℝ) →ₗ[ℝ] (m ⊕ o → ℝ) :=
    { toFun := fun z => Sum.elim 0 z
      map_add' := fun z w => by funext i; cases i <;> simp
      map_smul' := fun c z => by funext i; cases i <;> simp }
  have hinj : Function.Injective ι := by
    intro z w h
    funext i
    exact congrFun h (Sum.inr i)
  have hdim : Module.finrank ℝ (LinearMap.range ι) = Fintype.card o := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  rw [← hdim]
  refine finrank_le_posIndexAbove hX θ ?_
  rintro _ ⟨z, rfl⟩ hne
  have hz : z ≠ 0 := by rintro rfl; apply hne; funext i; cases i <;> rfl
  have hl : (ι z) ∘ Sum.inl = 0 := rfl
  have hr : (ι z) ∘ Sum.inr = z := rfl
  rw [hermForm_fromBlocks, hl, hr, sum_norm_sq_sum, hl, hr, hermForm_smul_one]
  have hpos : 0 < ∑ i, ‖z i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i))
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sum_const_zero, zero_add, mulVec_zero, dotProduct_zero, add_zero, zero_dotProduct]
  have : hermForm A 0 = 0 := by simp [hermForm]
  rw [this, zero_add]
  nlinarith

end Blocks

end ZetaS
