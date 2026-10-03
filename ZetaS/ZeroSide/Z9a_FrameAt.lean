/-
Sub-node Z9a (agent L3_1) — the frame at ONE height: for every T with 8w ≤ L, T > 0 and ∫φ_T² ≠ 0 there is a
`ZeroFrame` satisfying `FrameSpec` (on-line zeros of I′ sorted by ordinate with their multiplicities, columns
u_γ (Z1: `ZeroSide.gram_eq_matrix`), kernel kWin (Z2 fix), off-grid Etr (Z3), off-line block
Qoff = Σ_{β>½} 2m(xxᵀ − yyᵀ) with x + iy = u_ρ (Z8), n₊, n₋ ≤ p (Z7 + tree `posIndex_add_le`), and
toC Ĝ = hat(Az) (tree `ZeroSide.ZeroBlockData.blockA_decomp`)). At other heights any frame will do.
-/
import ZetaS.ZeroSide.Z9s_Spec
import ZetaS.ZeroSide.Z9a5_FrameSpec

noncomputable section

namespace ZetaS
namespace Z9

open Zeta23

theorem frameAt_exists (Z : ZeroConfig) {P : Params} (hP : P.Valid) {ψ : ℝ → ℝ}
    (heven : ∀ s, ψ (-s) = ψ s) {c : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV ψ T) (P.L T) P.w c) (T : ℝ) :
    ∃ F : ZeroFrame, 8 * P.w ≤ P.L T → 0 < T → (∫ u, P.phiV ψ T u ^ 2) ≠ 0 → FrameSpec Z P ψ T F := by
  by_cases hg : 8 * P.w ≤ P.L T ∧ 0 < T ∧ (∫ u, P.phiV ψ T u ^ 2) ≠ 0
  · obtain ⟨h8, hT, hv⟩ := hg
    exact ⟨frameAt Z ψ T hP heven (hadm T h8) hv hT, fun _ _ _ => frameAt_spec Z ψ T hP heven (hadm T h8) hv hT⟩
  · exact ⟨dummyFrame, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hg⟩

end Z9
end ZetaS
