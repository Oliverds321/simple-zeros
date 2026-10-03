/-
Node L5 (track L/P) — lem:sigd-removal (a), sec_zeta.tex l.1192–1196: "Let G ⪰ 0 and Q be real symmetric with
n₊(Q) ≤ b and n₋(Q) ≤ p, and let λ₁ ≥ λ₂ ≥ ⋯ be the eigenvalues of G. Then
‖G+Q‖² − ‖G‖² − 2 tr Q ≥ 2(tr Q − 2b) − Σ_{i≤p} (λ_i − 2)₊²."
The sum over the p largest eigenvalues is written with Mathlib's sorted eigenvalues `eigenvalues₀` (antitone,
indexed by Fin (card n)); indices i < p.
Deps: Interfaces; trunk RHLinalg (hermPosPart, vonNeumann_trace_ineq, negIndex).

Proof (L2_1): the template `rank_trace_ineq` (c = 2) with `P := G`: `‖G+Q‖² ≥ ‖G‖² + 2tr(GQ₊) − 2tr(GQ₋) + ‖Q₊‖² + ‖Q₋‖²`,
`tr(GQ₊) ≥ 0`, von Neumann `tr(GQ₋) ≤ Σₖ gₖmₖ` (sorted), `‖Q₊‖² ≥ 4trQ₊ − 4b`; then termwise
`mₖ² − 2gₖmₖ + 4mₖ ≥ −((gₖ − 2)₊)²` (`= (mₖ − (gₖ−2))² − (gₖ−2)²`, and `≥ 0` if `gₖ ≤ 2`), and `mₖ = 0` for `k ≥ p`
because `m` is antitone, nonnegative, with `#{mₖ ≠ 0} = rank Q₋ = n₋(Q) ≤ p`.
-/
import ZetaS.Interfaces

open Matrix RHLinalg Finset

namespace ZetaS

theorem pair_removal {n : Type*} [Fintype n] [DecidableEq n]
    {G Q : Matrix n n ℝ} (hG : G.PosSemidef) (hQ : Q.IsHermitian) {b p : ℕ}
    (hb : posIndex hQ ≤ b) (hp : negIndex hQ ≤ p) :
    2 * (rtrace Q - 2 * b)
        - ∑ i : Fin (Fintype.card n), (if (i : ℕ) < p then (max (hG.isHermitian.eigenvalues₀ i - 2) 0) ^ 2 else 0)
      ≤ frobSq (G + Q) - frobSq G - 2 * rtrace Q := by
  classical
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set g : Fin (Fintype.card n) → ℝ := hG.isHermitian.eigenvalues₀ with hg
  set m : Fin (Fintype.card n) → ℝ := hQm_psd.isHermitian.eigenvalues₀ with hm
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  -- `#{mₖ ≠ 0} = n₋(Q) ≤ p`, hence `mₖ = 0` for `k ≥ p` (`m` antitone).
  have hm_card : #{k | m k ≠ 0} ≤ p := by
    calc #{k | m k ≠ 0}
        = #{i | hQm_psd.isHermitian.eigenvalues i ≠ 0} :=
          (card_eigenvalues_reindex hQm_psd.isHermitian (· ≠ 0)).symm
      _ = Qm.rank := by
          rw [hQm_psd.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
      _ = #{i | (hQ.eigenvalues i)⁻ ≠ 0} := by
          rw [hQm_def, hermNegPart, rank_specMap]
      _ = #{i | hQ.eigenvalues i < 0} := by
          congr 1; ext i; simp [negPart_eq_zero, not_le]
      _ ≤ p := hp
  have hm_zero : ∀ k : Fin (Fintype.card n), p ≤ (k : ℕ) → m k = 0 := by
    intro k hk
    by_contra hne
    have hpos : 0 < m k := (hm_nn k).lt_of_ne' hne
    have hsub : Finset.Iic k ⊆ ({l | m l ≠ 0} : Finset _) := by
      intro l hl
      rw [Finset.mem_Iic] at hl
      have := hQm_psd.isHermitian.eigenvalues₀_antitone hl
      simp only [mem_filter, mem_univ, true_and]
      exact (lt_of_lt_of_le hpos this).ne'
    have := (card_le_card hsub).trans hm_card
    rw [Fin.card_Iic] at this
    omega
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  -- Frobenius expansion.
  have hexpand : frobSq (G + Q)
      = frobSq G + 2 * RCLike.re (G * Qp).trace - 2 * RCLike.re (G * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]; simp
    rw [hQdec, frobSq_add_hermitian hG.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  have hGQp : 0 ≤ RCLike.re (G * Qp).trace := trace_mul_nonneg_of_posSemidef hG hQp_psd
  have hvN : RCLike.re (G * Qm).trace ≤ ∑ k, g k * m k :=
    vonNeumann_trace_ineq hG.isHermitian hQm_psd.isHermitian
  have hstep6 : 2 * 2 * rtrace Qp - 2 ^ 2 * (b : ℝ) ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ 2
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0}
        = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  -- Termwise: `mₖ² − 2gₖmₖ + 4mₖ ≥ −[k < p]((gₖ − 2)₊)²`.
  have hterm : ∀ k : Fin (Fintype.card n),
      -(if (k : ℕ) < p then (max (g k - 2) 0) ^ 2 else 0) ≤ (m k) ^ 2 - 2 * (g k * m k) + 4 * m k := by
    intro k
    split_ifs with hk
    · rcases le_total (g k) 2 with h2 | h2
      · rw [max_eq_right (by linarith)]
        nlinarith [mul_nonneg (hm_nn k) (show 0 ≤ 2 - g k by linarith), sq_nonneg (m k)]
      · rw [max_eq_left (by linarith)]
        nlinarith [sq_nonneg (m k - (g k - 2))]
    · rw [hm_zero k (not_lt.mp hk)]; simp
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ univ) => hterm k
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hsum
  have htraceQ : rtrace Q = rtrace Qp - rtrace Qm := by rw [hQdec, rtrace_sub]
  linarith [hexpand, hGQp, hvN, hstep6, htraceQm, hfrobQm, hsum, htraceQ]

end ZetaS
