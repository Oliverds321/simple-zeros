/-
lean_work/L2_1/LinAlgHelpers.lean — shared helpers of the linear-algebra track (L2_1, 28 Sep 2026).
Namespace `ZetaS`, all public. Compiled into `lean_work/L2_1/olean/LinAlgHelpers.olean`.

  * `sum_eig_transfer`  : `∑_{i:r} f(λᵢ(VᴴV)) = ∑_{j:n} f(λⱼ(VVᴴ))` for `f 0 = 0` (nonzero spectra agree).
  * `stab_core`         : `2trP + 4trQ − 4b − ‖P+Q‖² + ∑ⱼ(Ψ(pⱼ) − 1) ≤ 0` for `P ⪰ 0`, `n₊(Q) ≤ b` (L1's core).
  * `stab_core_two`     : `2s trP + 2t trQ − ‖P+Q‖² + ∑ⱼ(Ψ_{s,t}(pⱼ) − s²) ≤ t²b`, `0 ≤ s ≤ t` (L2's core).
-/
import ZetaS.Interfaces

open Matrix RHLinalg Finset
open scoped ComplexOrder

namespace ZetaS

/-- `Ψ(p) ≤ (p − m − 1)² + 2m` for `m ≥ 0` (every real `p`). -/
lemma psi_le_min (p m : ℝ) (hm : 0 ≤ m) : Psi p ≤ (p - m - 1) ^ 2 + 2 * m := by
  unfold Psi
  split_ifs with h
  · nlinarith [mul_nonneg hm (show 0 ≤ m - 2 * p + 4 by linarith)]
  · nlinarith [sq_nonneg (p - m - 2)]

/-- `Ψ_{s,t}(p) ≤ (p − m − s)² + 2(t − s)m` for `m ≥ 0` (every real `p`). -/
lemma psiST_le_min {s t : ℝ} (p m : ℝ) (hm : 0 ≤ m) :
    PsiST s t p ≤ (p - m - s) ^ 2 + 2 * (t - s) * m := by
  unfold PsiST
  split_ifs with h
  · nlinarith [mul_nonneg hm (show 0 ≤ m + 2 * (t - p) by linarith)]
  · nlinarith [sq_nonneg (p - m - t)]

lemma psiST_one_two : PsiST 1 2 = Psi := by
  funext p; unfold PsiST Psi; split_ifs <;> ring

section Transfer

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

open Polynomial in
/-- Nonzero eigenvalues of `VᴴV` and `VVᴴ` agree with multiplicity: for `f 0 = 0`,
`∑_{i:r} f(λᵢ(VᴴV)) = ∑_{j:n} f(λⱼ(VVᴴ))`. -/
lemma sum_eig_transfer (V : Matrix n r 𝕜) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ i, f ((isHermitian_conjTranspose_mul_self V).eigenvalues i)
      = ∑ j, f ((isHermitian_mul_conjTranspose_self V).eigenvalues j) := by
  set hM := isHermitian_conjTranspose_mul_self V
  set hP := isHermitian_mul_conjTranspose_self V
  have key := charpoly_mul_comm' Vᴴ V
  have hne1 : (X ^ Fintype.card n * (Vᴴ * V).charpoly : 𝕜[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (charpoly_monic _).ne_zero
  have hne2 : (X ^ Fintype.card r * (V * Vᴴ).charpoly : 𝕜[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (charpoly_monic _).ne_zero
  have hroots := congrArg Polynomial.roots key
  rw [roots_mul hne1, roots_mul hne2, roots_X_pow, roots_X_pow,
    hM.roots_charpoly_eq_eigenvalues, hP.roots_charpoly_eq_eigenvalues] at hroots
  have hsum := congrArg (fun s : Multiset 𝕜 => (s.map (fun z => f (RCLike.re z))).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, map_zero, hf, smul_zero, zero_add,
    Multiset.map_map, Function.comp_apply, RCLike.ofReal_re] at hsum
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact hsum

end Transfer

section Core

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Two-parameter stability core** (lem:oll-Ast in eigenvalue form on `P`, no rank hypothesis):
for `P ⪰ 0`, `n₊(Q) ≤ b`, `0 ≤ s ≤ t`:
`2s tr P + 2t tr Q − ‖P+Q‖² + ∑ⱼ (Ψ_{s,t}(pⱼ) − s²) ≤ t² b`.
The template `rank_trace_ineq` with its step 5 replaced by `psiST_le_min`. -/
lemma stab_core_two {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) {s t : ℝ} :
    2 * s * rtrace P + 2 * t * rtrace Q - frobSq (P + Q)
      + ∑ j, (PsiST s t (hP.isHermitian.eigenvalues j) - s ^ 2) ≤ t ^ 2 * (b : ℝ) := by
  classical
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set p : Fin (Fintype.card n) → ℝ := hP.isHermitian.eigenvalues₀
  set m : Fin (Fintype.card n) → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  have hpsiP : ∑ j, (PsiST s t (hP.isHermitian.eigenvalues j) - s ^ 2)
      = ∑ k, (PsiST s t (p k) - s ^ 2) :=
    sum_eigenvalues_reindex hP.isHermitian (fun x => PsiST s t x - s ^ 2)
  -- Step 1: Frobenius expansion.
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]; simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  -- Step 2: `tr(PQ₊) ≥ 0`.
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace := trace_mul_nonneg_of_posSemidef hP hQp_psd
  -- Step 3: von Neumann.
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  -- Step 4.
  have hstep4 : ∑ k, (p k - m k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2
        = ∑ k, (p k)^2 - 2 * ∑ k, p k * m k + ∑ k, (m k)^2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]; linarith
  -- Step 5 (new): termwise minimum over `mₖ ≥ 0`.
  have hstep5 : ∑ k, (PsiST s t (p k) - s ^ 2) + 2 * s * rtrace P - 2 * t * rtrace Qm
      ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := psiST_le_min (s := s) (t := t) (p k) (m k) (hm_nn k)
    nlinarith
  -- Step 6 (template, `c = t`).
  have hstep6 : 2 * t * rtrace Qp - t ^ 2 * (b : ℝ) ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ t
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0}
        = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : rtrace Q = rtrace Qp - rtrace Qm := by rw [hQdec, rtrace_sub]
  rw [hpsiP]
  have h2t : 2 * t * rtrace Q = 2 * t * rtrace Qp - 2 * t * rtrace Qm := by rw [htraceQ]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, h2t]

/-- **Stability core** (L1): `2 tr P + 4 tr Q − 4b − ‖P+Q‖² + ∑ⱼ (Ψ(pⱼ) − 1) ≤ 0` for `P ⪰ 0`, `n₊(Q) ≤ b`. -/
lemma stab_core {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * (b : ℝ) - frobSq (P + Q)
      + ∑ j, (Psi (hP.isHermitian.eigenvalues j) - 1) ≤ 0 := by
  have h := stab_core_two hP hQ hb (s := 1) (t := 2)
  rw [psiST_one_two] at h
  norm_num at h ⊢
  linarith

end Core

end ZetaS
