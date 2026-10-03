/-
Node L1 (track L) — lem:zeta-stab, sec_zeta.tex l.231–236:
"Let P,Q be Hermitian d×d matrices with P = VV*, V ∈ ℂ^{d×r}, and put M := V*V. If n₊(Q) ≤ b, then
 r ≥ 2 tr P + 4 tr Q − 4b − ‖P+Q‖² + tr Ψ(M)."
Template: `RHLinalg.rank_trace_ineq` (Zeta23/LinAlg/RankTrace.lean:163), keeping the Σ Ψ(p_i) term instead of dropping it
(proof l.242–265: identity 1 − 2p + 4n + (p − n)² = (p − n − 1)² + 2n, then min over n ≥ 0).
Deps: Interfaces (Psi, trFun); trunk RHLinalg (hermPosPart, vonNeumann_trace_ineq, sum_eigenvalues_reindex).

Proof (L2_1, 28 Sep 2026). Two steps.
  (1) `sum_eig_transfer`: for `f` with `f 0 = 0`, `∑_{i:r} f(λᵢ(VᴴV)) = ∑_{j:n} f(λⱼ(VVᴴ))`, from Mathlib's
      `charpoly_mul_comm'` (`X^|n| χ(VᴴV) = X^|r| χ(VVᴴ)`) and `roots_charpoly_eq_eigenvalues`. Applied to
      `f = Ψ − 1` (`Ψ 0 = 1`) it turns `tr Ψ(M) − r` into `∑_{j:n} (Ψ(pⱼ) − 1)`, `pⱼ` the eigenvalues of `P = VVᴴ`;
      no rank bookkeeping and no case `r ≤ d` is needed.
  (2) `stab_core`: for `P ⪰ 0`, `2 tr P + 4 tr Q − 4b − ‖P+Q‖² + ∑ⱼ (Ψ(pⱼ) − 1) ≤ 0`. This is the template's proof
      at `c = 2` verbatim (steps 1–4, 6, 7), with its step 5 (`sum_sq_diff_lower`) replaced by the pointwise bound
      `psi_le_min`: `Ψ(p) ≤ (p − m − 1)² + 2m` for `m ≥ 0`.
-/
import ZetaS.Interfaces

open Matrix RHLinalg Finset
open scoped ComplexOrder

namespace ZetaS

/-- `Ψ(p) = min_{m ≥ 0} [(p − m − 1)² + 2m]`, the "≤" half (proof of lem:zeta-stab, sec_zeta.tex l.258–262).
Holds for every real `p`. -/
private lemma psi_le_min (p m : ℝ) (hm : 0 ≤ m) : Psi p ≤ (p - m - 1) ^ 2 + 2 * m := by
  unfold Psi
  split_ifs with h
  · -- `(p − m − 1)² + 2m − (p − 1)² = m (m − 2p + 4) ≥ 0` since `p ≤ 2`.
    nlinarith [mul_nonneg hm (show 0 ≤ m - 2 * p + 4 by linarith)]
  · -- `(p − m − 1)² + 2m − (2p − 3) = (p − m − 2)²`.
    nlinarith [sq_nonneg (p - m - 2)]

/-- The pointwise step replacing `sum_sq_diff_lower` of the template:
`(Ψ(p) − 1) + 2p − 4m ≤ (p − m)²` for `m ≥ 0` (identity `1 − 2p + 4m + (p − m)² = (p − m − 1)² + 2m`). -/
private lemma psi_step (p m : ℝ) (hm : 0 ≤ m) : (Psi p - 1) + 2 * p - 4 * m ≤ (p - m) ^ 2 := by
  have := psi_le_min p m hm
  nlinarith

section Transfer

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]

open Polynomial in
/-- Nonzero eigenvalues of `VᴴV` and `VVᴴ` agree with multiplicity: for `f 0 = 0`,
`∑_{i:r} f(λᵢ(VᴴV)) = ∑_{j:n} f(λⱼ(VVᴴ))`. -/
private lemma sum_eig_transfer (V : Matrix n r 𝕜) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ i, f ((isHermitian_conjTranspose_mul_self V).eigenvalues i)
      = ∑ j, f ((isHermitian_mul_conjTranspose_self V).eigenvalues j) := by
  set hM := isHermitian_conjTranspose_mul_self V
  set hP := isHermitian_mul_conjTranspose_self V
  have key := charpoly_mul_comm' Vᴴ V
  -- `X^|n| χ(VᴴV) = X^|r| χ(VVᴴ)`; take roots.
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

/-- The stability rank–trace inequality in eigenvalue form on `P` (no rank hypothesis):
`2 tr P + 4 tr Q − 4b − ‖P+Q‖² + ∑ⱼ (Ψ(pⱼ) − 1) ≤ 0` for `P ⪰ 0`, `n₊(Q) ≤ b`.
The template `rank_trace_ineq` at `c = 2`, keeping `∑ Ψ`. -/
private lemma stab_core {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * (b : ℝ) - frobSq (P + Q)
      + ∑ j, (Psi (hP.isHermitian.eigenvalues j) - 1) ≤ 0 := by
  classical
  -- Positive/negative parts of `Q`.
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  -- Sorted eigenvalues on `Fin d`.
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
  have hpsiP : ∑ j, (Psi (hP.isHermitian.eigenvalues j) - 1) = ∑ k, (Psi (p k) - 1) :=
    sum_eigenvalues_reindex hP.isHermitian (fun x => Psi x - 1)
  -- Step 1 (template): Frobenius expansion.
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
  -- Step 2 (template): drop `tr(PQ₊) ≥ 0`.
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace := trace_mul_nonneg_of_posSemidef hP hQp_psd
  -- Step 3 (template): von Neumann on `P, Q₋`.
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  -- Step 4 (template): `‖P‖² − 2 tr(PQ₋) + ‖Q₋‖² ≥ ∑(pₖ − mₖ)²`.
  have hstep4 : ∑ k, (p k - m k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2
        = ∑ k, (p k)^2 - 2 * ∑ k, p k * m k + ∑ k, (m k)^2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]; linarith
  -- Step 5 (new): termwise `(Ψ(pₖ) − 1) + 2pₖ − 4mₖ ≤ (pₖ − mₖ)²`, i.e. the minimum over `mₖ ≥ 0`.
  have hstep5 : ∑ k, (Psi (p k) - 1) + 2 * rtrace P - 4 * rtrace Qm ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun k _ => psi_step (p k) (m k) (hm_nn k)
  -- Step 6 (template, `c = 2`): `4 tr Q₊ − 4b ≤ ‖Q₊‖²`.
  have hstep6 : 2 * 2 * rtrace Qp - 2 ^ 2 * (b : ℝ) ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ 2
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0}
        = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  -- Step 7: combine.
  have htraceQ : rtrace Q = rtrace Qp - rtrace Qm := by rw [hQdec, rtrace_sub]
  rw [hpsiP]
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

end Core

/-- **Stability rank–trace lemma** (lem:zeta-stab, sec_zeta.tex l.231–236).
For `V ∈ 𝕜^{n×r}`, `P = VVᴴ`, `M = VᴴV` and Hermitian `Q` with `n₊(Q) ≤ b`:
`r ≥ 2 tr P + 4 tr Q − 4b − ‖P+Q‖²_F + tr Ψ(M)`. No relation between `|n|` and `|r|` is assumed. -/
theorem stab_rank_trace {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (V : Matrix n r 𝕜) {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (V * Vᴴ) + 4 * rtrace Q - 4 * (b : ℝ) - frobSq (V * Vᴴ + Q)
        + trFun (Matrix.isHermitian_conjTranspose_mul_self V) Psi
      ≤ (Fintype.card r : ℝ) := by
  have hP : (V * Vᴴ).PosSemidef := posSemidef_self_mul_conjTranspose V
  have hcore := stab_core hP hQ hb
  -- `tr Ψ(M) − r = ∑_{i:r} (Ψ(μᵢ) − 1) = ∑_{j:n} (Ψ(pⱼ) − 1)`, since `(Ψ − 1)(0) = 0`.
  have htr := sum_eig_transfer V (fun x => Psi x - 1) (by norm_num [Psi])
  have hsplit : trFun (Matrix.isHermitian_conjTranspose_mul_self V) Psi
      = ∑ i, (Psi ((Matrix.isHermitian_conjTranspose_mul_self V).eigenvalues i) - 1)
        + (Fintype.card r : ℝ) := by
    unfold trFun
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsplit, htr]
  linarith

end ZetaS
