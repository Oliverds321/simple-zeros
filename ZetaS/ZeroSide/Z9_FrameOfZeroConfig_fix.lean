/-
Node Z9, corrected form (agent L3_1, 28 Sep 2026) — STATEMENT-CHANGE REQUEST: the skeleton Z9 (and W2L-poly) give the
seams for Nˢ, N^d, N^sc only; W1L needs s₁ = #{simple on-line zeros of I′} ≤ N₀ˢ(T,2T) + o(N), which is NOT a
consequence of them (s₁ ≤ Nˢ(I′) points the wrong way: Nˢ ≥ N₀ˢ). This file adds the fourth seam
`(Fm.F T).sEq 1 ≤ Z.N0s T (2T) + r T`; the skeleton statement is its corollary (Z9_FrameOfZeroConfig.lean).
Assembly of the sub-nodes Z9a–Z9e with Z4, Z5, Z6 (L3_2).
-/
import ZetaS.InterfacesV2
import Zeta23.Hypotheses
import ZetaS.ZeroSide.Z9a_FrameAt
import ZetaS.ZeroSide.Z9b_TailTransfer
import ZetaS.ZeroSide.Z9c_JIdentity
import ZetaS.ZeroSide.Z9d_Span
import ZetaS.ZeroSide.Z9e_Seams
import ZetaS.ZeroSide.Z4_KWinClose
import ZetaS.ZeroSide.Z5_KWinDominated
import ZetaS.ZeroSide.Z6_Defect

open Filter Asymptotics

namespace ZetaS

theorem frameFamily_of_zeroConfig_fix (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z) {P : Zeta23.Params}
    (hP : P.Valid) (hlam : P.lam < 1) {ψ : ℝ → ℝ} (heven : ∀ s, ψ (-s) = ψ s) (hcont : Continuous ψ)
    (hcore : ∀ s, |s| ≤ 1 / 2 → 0 ≤ ψ s ∧ ψ s ≤ 1) {c : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → Zeta23.AdmWindow (P.phiV ψ T) (P.L T) P.w c)
    (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s) (hb : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s ^ 2) :
    ∃ Fm : FrameFamilyL P.lam (fun T => (Z.N T (2 * T) : ℝ)) (Rlam P.lam ψ) (kPsi ψ),
      ∃ r : ℝ → ℝ, r =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧ ∀ᶠ T in atTop,
        ((Fm.F T).NsW : ℝ) ≤ Z.Ns T (2 * T) + r T ∧
        ((Fm.F T).NdW : ℝ) ≤ Z.Nd T (2 * T) + r T ∧
        ((Fm.F T).NscW : ℝ) ≤ (Z.N0 T (2 * T) : ℝ) + Z.Ns T (2 * T) - Z.N0s T (2 * T) + r T ∧
        ((Fm.F T).sEq 1 : ℝ) ≤ Z.N0s T (2 * T) + r T := by
  classical
  choose F hF using fun T => Z9.frameAt_exists Z hP heven hadm T
  have h8 : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := Zeta23.Params.eventually_w8 hP
  have hI := Z9.eventually_int_sq_ne_zero hP heven hcont hcore hadm hb
  have hspec : ∀ᶠ T in atTop, Z9.FrameSpec Z P ψ T (F T) := by
    filter_upwards [h8, eventually_gt_atTop 0, hI] with T h1 h2 h3
    exact hF T h1 h2 h3
  have hJ := Z9.jWin_nonneg hcore hP.lam_pos.le
  obtain ⟨htr, hfr, hwin⟩ := Z9.hatAz_asymptotics Z H hP hlam heven hcont hcore hadm ha hb hJ
  rw [Z9.cWin_inv_eq_Rlam hcont] at hfr
  obtain ⟨rs, hrs, hspan⟩ := Z9.span_bound Z H hP
  obtain ⟨e4, he4, hk4⟩ := kWin_close hP hcont hcore ha
  obtain ⟨e5, he5, hk5⟩ := kWin_dominated hP hcont hcore ha
  have hdef := defect_littleO Z H hP hlam hadm
  have hN0 : ∀ᶠ T in atTop, (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Eventually.of_forall fun T => Nat.cast_nonneg _
  have hspanL : ∀ᶠ T in atTop, (F T).Λ ≤ P.lam * (Z.N T (2 * T) : ℝ) + rs T := by
    filter_upwards [hspec, hspan] with T hs h
    rw [hs.Λ_eq]; exact h
  refine ⟨{ F := F
            N_nonneg := hN0
            N_tendsto := Zeta23.Assembly.tendsto_N_atTop Z H.RvM
            trace := htr.congr' (hspec.mono fun T hs => by simp only [hs.tr_eq]) EventuallyEq.rfl
            frob := hfr.congr' (hspec.mono fun T hs => by simp only [hs.frob_eq]) EventuallyEq.rfl
            window := hwin.congr' (hspec.mono fun T hs => by simp only [hs.Nw_eq]) EventuallyEq.rfl
            span := ⟨rs, hrs, by
              filter_upwards [hspanL] with T h
              have h1 : P.lam * (Z.N T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) :=
                mul_le_of_le_one_left (Nat.cast_nonneg _) hlam.le
              linarith⟩
            defect := hdef.congr' (hspec.mono fun T hs => hs.defect_eq.symm) EventuallyEq.rfl
            kernel := ⟨e4, he4, by
              filter_upwards [hk4, hspec] with T h hs t
              rw [hs.k_eq]; exact h t⟩
            dominate := ⟨e5, he5, by
              filter_upwards [hk5, hspec] with T h hs
              rw [hs.k_eq]; exact h⟩
            lam_pos := hP.lam_pos
            lam_le_one := hlam.le
            span_lam := ⟨rs, hrs, hspanL⟩ },
    fun T => (Z.NIprime T : ℝ) - Z.N T (2 * T), hwin, ?_⟩
  filter_upwards [hspec] with T hs
  obtain ⟨h1, h2, h3, h4⟩ := Z9.count_seams Z T
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs.NsW_eq]; exact h1
  · rw [hs.NdW_eq]; exact h2
  · rw [hs.NscW_eq]; exact h3
  · rw [hs.sEq1_eq]; exact h4

end ZetaS
