/-
Node K8d (L7_3): the bridge between Lemma K's objects (K5–K7, stated with `acoef`, `Xlam`, `charSum`, `l2sq`) and the
objects of ZetaQ's out-zone step (`Zones.acoefS`, `P.XQ`, `Zones.AchiC`, `Zones.normA2`), which K8a consumes:
ZetaQ's PP block bounds the out-zone by the pointwise sieve `2·sieveBudgetQ·∫_{inZoneᶜ} gQ·normA2`
(`InZone.famPP_total_le`); K8a replaces the pointwise sieve there by K7. The two coefficient conventions agree:
`a_n(s) = −(2π)⁻¹Λ(n)n^{−1/2}D_T(s − log n)` on `n ≤ ⌊𝒳⌋`, `𝒳 = e^{λℒ}`, `ℒ = log(QT/2π)`.
Difficulty: E. PROVED.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Zones

theorem DT_eq (P : ParamsQ) (v : ℝ) : DT P.T v = P.DT v := by
  unfold DT ParamsQ.DT
  congr 1
  funext τ
  ring_nf

theorem acoef_eq_acoefS (P : ParamsQ) (n : ℕ) (s : ℝ) : acoef P.T s n = acoefS P n s := by
  unfold acoef acoefS
  rw [DT_eq]
  congr 1
  have h : ((n : ℝ) ^ (-(1 / 2 : ℝ))) = 1 / Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n)]
    exact (one_div _).symm
  rw [h]
  push_cast
  ring

theorem Xlam_eq_XQ (P : ParamsQ) : Xlam P.lam P.Q P.T = P.XQ := by
  unfold Xlam Lc ParamsQ.XQ ParamsQ.LB ParamsQ.LL
  rfl

theorem l2sq_eq_normA2 (P : ParamsQ) (s : ℝ) :
    ZetaQ.l2sq ⌊Xlam P.lam P.Q P.T⌋₊ (acoef P.T s) = normA2 P s := by
  unfold ZetaQ.l2sq normA2 primeRangeQ
  rw [Xlam_eq_XQ]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [acoef_eq_acoefS]

theorem charSum_eq_AchiC (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℝ) :
    ZetaQ.charSum q ⌊Xlam P.lam P.Q P.T⌋₊ (acoef P.T s) χ = AchiC P (fun n s => acoefS P n s) χ s := by
  unfold ZetaQ.charSum AchiC primeRangeQ
  rw [Xlam_eq_XQ]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [acoef_eq_acoefS]

end LemmaK
end ZetaShell
