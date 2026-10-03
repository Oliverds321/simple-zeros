/-
Node L7 (track L) — thm:sigd-schur (l.1240–1269), second (used) inequality: M = [[A, Y], [Yᵀ, R]] real symmetric
with λ_max(R) ≤ λ_c = 2 + √c*; charge κ(λ) = [(λ − 2)₊² − c*]₊, ch(X) = Σ κ(λ_i(X)):
"ch(M) ≤ ‖A − 2I‖² + 2‖Y‖² − tr(2I − A)₊²".
Proof: layer-cake ch(X) = ∫_{λ_c}^∞ 2(t − 2) n_>(X;t) dt; Haynsworth/Sylvester (trunk `Sylvester.lean`) for the Schur
complement; Weyl; Cauchy interlacing for the dilation [[A, W^{1/2}],[W^{1/2}, ρ_R I]]. No positivity used.

Proof formalised (L2_1, a shortcut of the draft's route with the same final accounting; no Schur complement, no
layer-cake integral, no W^{1/2}):
  (1) `M̃ := [[A, Y],[Yᵀ, λ_c I_r]]` dominates `M` (`M̃ − M = 0 ⊕ (λ_c I − R) ⪰ 0` as `λ_max(R) ≤ λ_c`), so by Weyl
      monotonicity the sorted eigenvalues satisfy `μₗ(M) ≤ μ̃ₗ` and, `κ` being nondecreasing, `ch(M) ≤ ch(M̃)`.
  (2) Interlacing (count form, from the trunk's Sylvester tools, `CountHelpers`): `μ̃ₗ ≥ λ_c` for `l < r`
      (subspace `0 ⊕ ℝ^r`), and `μ̃_{r+j} ≤ αⱼ` (`n₊^θ(M̃) ≤ n₊^θ(A) + r`).
  (3) Accounting: with `h(μ) := (μ − 2)² − κ(μ)`, `h(μ̃ₗ) ≥ c*` for `l < r`, `h(μ̃_{r+j}) ≥ (2 − αⱼ)₊²`, and
      `Σ(μ̃ₗ − 2)² = ‖M̃ − 2I‖² = ‖A − 2I‖² + 2‖Y‖² + r·c*`; so
      `ch(M̃) = Σ(μ̃ − 2)² − Σh(μ̃) ≤ ‖A − 2I‖² + 2‖Y‖² − Σⱼ(2 − αⱼ)₊²`.
  (This is the draft's final computation for its dilation `M̃` with `ρ_R` replaced by `λ_c`; the draft's sharper first
  inequality with the `q`-term is not formalised — the skeleton states only the second one.)
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.CountHelpers

open Matrix RHLinalg Finset

namespace ZetaS

-- `kappaCh` lives in `ZetaS.Interfaces` (lead's ruling, 28 Sep 2026).

private lemma kappaCh_mono (c : ℝ) : Monotone (kappaCh c) := by
  intro x y hxy
  unfold kappaCh
  have h1 : max (x - 2) 0 ≤ max (y - 2) 0 := max_le_max (by linarith) le_rfl
  have h2 : (max (x - 2) 0) ^ 2 ≤ (max (y - 2) 0) ^ 2 := pow_le_pow_left₀ (le_max_right _ _) h1 2
  exact max_le_max (by linarith) le_rfl

private lemma kappa_top {c μ : ℝ} (hc : 0 ≤ c) (hμ : 2 + Real.sqrt c ≤ μ) :
    c ≤ (μ - 2) ^ 2 - kappaCh c μ := by
  unfold kappaCh
  have hs := Real.sqrt_nonneg c
  have hsq := Real.sq_sqrt hc
  rw [max_eq_left (by linarith : 0 ≤ μ - 2)]
  have : c ≤ (μ - 2) ^ 2 := by nlinarith
  rw [max_eq_left (by linarith)]; linarith

private lemma kappa_bot {c μ α : ℝ} (hc : 0 ≤ c) (hμα : μ ≤ α) :
    (max (2 - α) 0) ^ 2 ≤ (μ - 2) ^ 2 - kappaCh c μ := by
  unfold kappaCh
  rcases le_total 2 α with h | h
  · rw [max_eq_right (by linarith : 2 - α ≤ 0)]
    have hk : max ((max (μ - 2) 0) ^ 2 - c) 0 ≤ (μ - 2) ^ 2 := by
      refine max_le ?_ (sq_nonneg _)
      rcases le_total (μ - 2) 0 with h' | h'
      · rw [max_eq_right h']; nlinarith [sq_nonneg (μ - 2)]
      · rw [max_eq_left h']; linarith
    nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ 2 - α), max_eq_right (by linarith : μ - 2 ≤ 0)]
    rw [show ((0 : ℝ) ^ 2 - c) = -c by ring, max_eq_right (by linarith : -c ≤ 0)]
    nlinarith

private lemma frobSq_real {n : Type*} [Fintype n] (X : Matrix n n ℝ) :
    frobSq X = ∑ i, ∑ j, X i j ^ 2 := by
  unfold frobSq
  simp only [RCLike.re_to_real, Matrix.trace, diag_apply, mul_apply, conjTranspose_apply, star_trivial]
  rw [Finset.sum_comm]
  simp [sq]

private lemma frobSq_sub_smul_one {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℝ}
    (hX : X.IsHermitian) (θ : ℝ) :
    frobSq (X - θ • (1 : Matrix n n ℝ))
      = frobSq X - 2 * θ * rtrace X + θ ^ 2 * Fintype.card n := by
  rw [sub_eq_add_neg, frobSq_add_hermitian hX (isHermitian_smul_one θ).neg]
  have h1 : RCLike.re (X * -(θ • (1 : Matrix n n ℝ))).trace = -θ * rtrace X := by
    simp [rtrace, trace_smul]
  have h2 : frobSq (-(θ • (1 : Matrix n n ℝ))) = θ ^ 2 * Fintype.card n := by
    simp [frobSq, trace_smul, sq]; ring
  rw [h1, h2]; ring

private lemma sum_eig_sub_sq {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℝ}
    (hX : X.IsHermitian) (θ : ℝ) :
    ∑ i, (hX.eigenvalues i - θ) ^ 2 = frobSq X - 2 * θ * rtrace X + θ ^ 2 * Fintype.card n := by
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hX, rtrace_eq_sum_eigenvalues hX]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const,
    card_univ, nsmul_eq_mul]
  ring_nf
  simp [mul_comm, mul_left_comm]

theorem schur_localisation {a r : ℕ} {A : Matrix (Fin a) (Fin a) ℝ} (Y : Matrix (Fin a) (Fin r) ℝ)
    {R : Matrix (Fin r) (Fin r) ℝ} (hA : A.IsHermitian) (hR : R.IsHermitian) {cstar : ℝ}
    (hc : 0 ≤ cstar) (hRmax : ∀ i, hR.eigenvalues i ≤ 2 + Real.sqrt cstar) :
    trFun (hA.fromBlocks (B := Y) (C := Yᴴ) rfl hR) (kappaCh cstar)
      ≤ frobSq (A - 2) + 2 * (∑ i, ∑ j, (Y i j) ^ 2) - trFun hA (fun t => (max (2 - t) 0) ^ 2) := by
  classical
  set lc := 2 + Real.sqrt cstar with hlc
  have hlc2 : (lc - 2) ^ 2 = cstar := by rw [hlc]; simp [Real.sq_sqrt hc]
  set hM := hA.fromBlocks (B := Y) (C := Yᴴ) rfl hR with hMdef
  have h1 : (lc • (1 : Matrix (Fin r) (Fin r) ℝ)).IsHermitian := isHermitian_smul_one lc
  have hMt : (fromBlocks A Y Yᴴ (lc • (1 : Matrix (Fin r) (Fin r) ℝ))).IsHermitian :=
    hA.fromBlocks rfl h1
  -- (1) Weyl: `M ⪯ M̃`.
  have hle : ∀ x, hermForm (fromBlocks A Y Yᴴ R) x
      ≤ hermForm (fromBlocks A Y Yᴴ (lc • (1 : Matrix (Fin r) (Fin r) ℝ))) x := by
    intro x
    rw [hermForm_fromBlocks, hermForm_fromBlocks, hermForm_smul_one]
    have := hermForm_le_of_eigenvalues_le hR hRmax (x ∘ Sum.inr)
    linarith
  have hweyl := weyl_mono_of_form hMt hM hle
  set N := Fintype.card (Fin a ⊕ Fin r) with hNdef
  set μ := hM.eigenvalues₀ with hμ
  set μt := hMt.eigenvalues₀ with hμt
  set α := hA.eigenvalues₀ with hα
  have hch : trFun hM (kappaCh cstar) = ∑ l, kappaCh cstar (μ l) :=
    sum_eigenvalues_reindex hM _
  have hstep1 : ∑ l, kappaCh cstar (μ l) ≤ ∑ l, kappaCh cstar (μt l) :=
    sum_le_sum fun l _ => kappaCh_mono cstar (hweyl l)
  -- (2) interlacing.
  have hI1 : ∀ l : Fin N, (l : ℕ) < r → lc ≤ μt l := by
    intro l hl
    refine le_eigenvalues₀_of_count hMt (r := r) (fun θ hθ => ?_) l hl
    have := le_posIndexAbove_fromBlocks_smul hMt hθ
    simpa using this
  have hI2 : ∀ (l : Fin N) (j : Fin (Fintype.card (Fin a))), (l : ℕ) = r + j → μt l ≤ α j := by
    intro l j hlj
    refine eigenvalues₀_le_of_count hMt hA (r := r) (fun θ => ?_) l j hlj
    have := posIndexAbove_fromBlocks_le hMt hA θ
    simpa using this
  -- (3) accounting.
  set hfun : ℝ → ℝ := fun x => (x - 2) ^ 2 - kappaCh cstar x with hhfun
  have hsplitk : ∑ l, kappaCh cstar (μt l) = ∑ l, (μt l - 2) ^ 2 - ∑ l, hfun (μt l) := by
    rw [← Finset.sum_sub_distrib]; refine sum_congr rfl fun l _ => ?_; simp [hhfun]
  -- `Σ(μ̃ − 2)² = ‖A − 2‖² + 2‖Y‖² + r c*`.
  have hsq : ∑ l, (μt l - 2) ^ 2 = frobSq (A - 2) + 2 * (∑ i, ∑ j, (Y i j) ^ 2) + r * cstar := by
    have e1 : ∑ l, (μt l - 2) ^ 2 = ∑ i, (hMt.eigenvalues i - 2) ^ 2 :=
      (sum_eigenvalues_reindex hMt (fun x => (x - 2) ^ 2)).symm
    rw [e1, sum_eig_sub_sq hMt 2]
    have e2 : (A - 2) = A - (2 : ℝ) • (1 : Matrix (Fin a) (Fin a) ℝ) := by
      rw [two_smul, one_add_one_eq_two]
    rw [e2, frobSq_sub_smul_one hA 2]
    have e3 : frobSq (fromBlocks A Y Yᴴ (lc • (1 : Matrix (Fin r) (Fin r) ℝ)))
        = frobSq A + 2 * (∑ i, ∑ j, (Y i j) ^ 2) + r * lc ^ 2 := by
      rw [frobSq_real, frobSq_real]
      simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, conjTranspose_apply, star_trivial, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => Y j i ^ 2)]
      simp [one_apply, sq]
      ring
    have e4 : rtrace (fromBlocks A Y Yᴴ (lc • (1 : Matrix (Fin r) (Fin r) ℝ))) = rtrace A + r * lc := by
      simp [rtrace, Matrix.trace, Fintype.sum_sum_type, one_apply]
    rw [e3, e4]
    simp only [Fintype.card_sum, Fintype.card_fin]
    push_cast
    rw [← hlc2]; ring
  -- `Σ h(μ̃) ≥ r c* + Σⱼ (2 − αⱼ)₊²`, by the range trick.
  have hN : N = r + Fintype.card (Fin a) := by
    simp only [hNdef, Fintype.card_sum, Fintype.card_fin]; ring
  have hhsum : (r : ℝ) * cstar + ∑ j, (max (2 - α j) 0) ^ 2 ≤ ∑ l, hfun (μt l) := by
    set F : ℕ → ℝ := fun l => if hl : l < N then hfun (μt ⟨l, hl⟩) else 0 with hF
    set Gf : ℕ → ℝ := fun j => if hj : j < Fintype.card (Fin a) then (max (2 - α ⟨j, hj⟩) 0) ^ 2 else 0
      with hG
    have eF : ∑ l, hfun (μt l) = ∑ l ∈ range N, F l := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun l _ => ?_
      simp only [hF, Fin.eta]
      split_ifs with h
      · rfl
      · exfalso; exact h (by simp only [hNdef]; exact l.2)
    have eG : ∑ j, (max (2 - α j) 0) ^ 2 = ∑ j ∈ range (Fintype.card (Fin a)), Gf j := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun j _ => ?_
      simp only [hG, dif_pos j.2, Fin.eta]
    rw [eF, eG, hN, Finset.sum_range_add]
    have p1 : (r : ℝ) * cstar ≤ ∑ l ∈ range r, F l := by
      have : ∑ l ∈ range r, (cstar : ℝ) = r * cstar := by simp
      rw [← this]
      refine sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      have hlN : l < N := by omega
      simp only [hF, dif_pos hlN]
      exact kappa_top hc (hI1 ⟨l, hlN⟩ hl)
    have p2 : ∑ j ∈ range (Fintype.card (Fin a)), Gf j
        ≤ ∑ j ∈ range (Fintype.card (Fin a)), F (r + j) := by
      refine sum_le_sum fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hjN : r + j < N := by omega
      simp only [hF, hG, dif_pos hjN, dif_pos hj]
      exact kappa_bot hc (hI2 ⟨r + j, hjN⟩ ⟨j, hj⟩ rfl)
    linarith
  have htrA : trFun hA (fun t => (max (2 - t) 0) ^ 2) = ∑ j, (max (2 - α j) 0) ^ 2 := by
    unfold trFun; exact sum_eigenvalues_reindex hA (fun t => (max (2 - t) 0) ^ 2)
  rw [hch, htrA]
  linarith [hstep1, hsplitk, hsq, hhsum]

end ZetaS
