/-
Node Z7 (track L) — inertia of an off-line pair block (draft l.201–203, lem:sigd-removal (b)): for u = x + iy,
u uᵀ + ū ūᵀ = 2(xxᵀ − yyᵀ), and xxᵀ − yyᵀ has n₊ ≤ 1 and n₋ ≤ 1.

Proof (L3_2): `n₊(xxᵀ − yyᵀ) ≤ n₊(xxᵀ) + n₊(−yyᵀ)` (trunk `posIndex_add_le`), `n₊(xxᵀ) = rank(xxᵀ) ≤ 1`
(PSD, `posIndex_eq_rank_of_posSemidef`, Mathlib `rank_vecMulVec_le`), `n₊(−yyᵀ) = n₋(yyᵀ) = 0` (eigenvalues of a PSD
matrix are ≥ 0). `n₋` the same way through L2_1's `negIndex_add_le` (L8) and `negIndex_eq_posIndex_neg`.
-/
import ZetaS.InterfacesV2
import Zeta23.LinAlg.Inertia
import ZetaS.LinAlg.SpecHelpers
import ZetaS.LinAlg.L8_NegIndexAdd

open RHLinalg

namespace ZetaS

private lemma negIndex_psd_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : negIndex hA.isHermitian = 0 := by
  unfold negIndex
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact not_lt.mpr (hA.eigenvalues_nonneg i)

theorem pairBlock_inertia {n : Type*} [Fintype n] [DecidableEq n] (x y : n → ℝ)
    (h : (Matrix.vecMulVec x x - Matrix.vecMulVec y y).IsHermitian) :
    posIndex h ≤ 1 ∧ negIndex h ≤ 1 := by
  have hx : (Matrix.vecMulVec x x).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star x
  have hy : (Matrix.vecMulVec y y).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star y
  have hsum : Matrix.vecMulVec x x - Matrix.vecMulVec y y
      = Matrix.vecMulVec x x + -Matrix.vecMulVec y y := sub_eq_add_neg _ _
  have hxy := hx.isHermitian.add hy.isHermitian.neg
  -- positive index
  have hp : posIndex h ≤ 1 := by
    rw [posIndex_congr hsum h hxy]
    refine (posIndex_add_le hx.isHermitian hy.isHermitian.neg).trans ?_
    have h1 : posIndex hx.isHermitian ≤ 1 := by
      rw [posIndex_eq_rank_of_posSemidef hx]; exact Matrix.rank_vecMulVec_le _ _
    have h2 : posIndex hy.isHermitian.neg = 0 := by
      rw [← negIndex_eq_posIndex_neg hy.isHermitian]; exact negIndex_psd_eq_zero hy
    omega
  -- negative index
  have hn : negIndex h ≤ 1 := by
    rw [negIndex_eq_posIndex_neg, posIndex_congr (congrArg Neg.neg hsum) h.neg hxy.neg,
      ← negIndex_eq_posIndex_neg hxy]
    refine (negIndex_add_le hx.isHermitian hy.isHermitian.neg).trans ?_
    have h1 : negIndex hx.isHermitian = 0 := negIndex_psd_eq_zero hx
    have h2 : negIndex hy.isHermitian.neg ≤ 1 := by
      rw [negIndex_eq_posIndex_neg, posIndex_congr (neg_neg _) _ hy.isHermitian,
        posIndex_eq_rank_of_posSemidef hy]
      exact Matrix.rank_vecMulVec_le _ _
    omega
  exact ⟨hp, hn⟩

end ZetaS
