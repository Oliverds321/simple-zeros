/-
lean_work/L3_2/top/TopSSC.lean — the architect's headlines `zeta_simple_on_line` (S, thm:zeta-mainw2) and
`zeta_simple_or_critical` (SC, cor:oll-SC), assembled from the named nodes (L3_2, 28 Sep 2026):
  W1L (`zeta_gramFamily_poly`, L3_1) / W2L-poly (`zeta_frameFamily_poly_fix`, L3_1) at every λ < 1,
  K6 `thmG_abstract` / K7 `sc_abstract` (skeleton statements here; proved by L4_1 in the tree's `ZetaS.KSide`),
  `eps_seam`, KL2 + KL3 (λ → 1⁻), N1 `num_stab` / `num_sc` (proved).
The statements are the architect's (`ChallengeZetaS` §5); identity is checked in `TopCheckSSC.lean`.
-/
import ZetaS.Top.TopSolution
import ZetaS.KSide.K6_ThmG
import ZetaS.KSide.K7_SCAbstract
import ZetaS.Window.W1L_ZetaGramPoly
import ZetaS.Top.PolyMoments

open Filter Topology Asymptotics

namespace ZetaS
namespace Top

lemma psiPoly8A_cont : ContinuousOn psiPoly8A (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
  (by unfold psiPoly8A; fun_prop : Continuous psiPoly8A).continuousOn

lemma psiPoly8A_pos : ∀ s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), 0 < psiPoly8A s := by
  intro s hs
  unfold psiPoly8A
  have h1 := hs.1; have h2 := hs.2
  set u := (2 * s) ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg _
  have hu1 : u ≤ 1 := by rw [hu]; nlinarith
  have hu2 : u ^ 2 ≤ 1 := by nlinarith
  apply mul_pos (by norm_num)
  nlinarith [pow_nonneg hu0 3, pow_nonneg hu0 4]

lemma int_psiPoly8A_ne : (∫ s in (-(1 / 2 : ℝ))..(1 / 2), psiPoly8A s) ≠ 0 := by
  rw [PolyMom.int_psi]; norm_num

/-- `stabConst` at the S data is affine in `H`. -/
lemma stab_affine (H : ℝ) : stabConst H 8 (7 / 1700) (199 / 25000) 147
    = (H - PhiM 147 (199 / 25000 * ((147 : ℕ) - (8 : ℕ) + 1)) / (199 / 25000 * ((147 : ℕ) - (8 : ℕ) + 1))
        * (7 / 1700 * ((147 : ℕ) - (8 : ℕ) + 1) / (147 : ℕ)))
      / (1 - PhiM 147 (199 / 25000 * ((147 : ℕ) - (8 : ℕ) + 1)) / (147 : ℕ)) := rfl

theorem stab_lim :
    Tendsto (fun lam => stabConst (2 - Rlam lam psiPoly8A) 8 (7 / 1700) (199 / 25000) 147) (𝓝[<] 1)
      (𝓝 (stabConst (Hpsi psiPoly8A) 8 (7 / 1700) (199 / 25000) 147)) := by
  have h := tendsto_Rlam_one psiPoly8A int_psiPoly8A_ne
  simp only [stab_affine]
  unfold Hpsi
  exact ((tendsto_const_nhds.sub h).sub tendsto_const_nhds).div_const _

theorem sc_lim :
    Tendsto (fun lam => scConst (stabConst (2 - Rlam lam psiPoly8A) 8 (7 / 1700) (199 / 25000) 147)) (𝓝[<] 1)
      (𝓝 (scConst (stabConst (Hpsi psiPoly8A) 8 (7 / 1700) (199 / 25000) 147))) := by
  unfold scConst
  exact ((tendsto_const_nhds.add (stab_lim.const_mul 2))).div_const _

lemma hBm : PhiM 147 (199 / 25000 * (((147 : ℕ) : ℝ) - (8 : ℕ) + 1)) < (147 : ℕ) := by
  have hPhiLe : ∀ E : ℝ, PhiM 147 E ≤ E := by
    intro E; unfold PhiM; split_ifs
    · exact le_rfl
    · exact sub_le_self _ (sq_nonneg _)
  have h140 : ((147 : ℕ) : ℝ) - ((8 : ℕ) : ℝ) + 1 = 140 := by norm_num
  rw [h140]
  have := hPhiLe (199 / 25000 * 140)
  norm_num at this ⊢
  linarith

/-- **S — simple zeros on the critical line** (the architect's `zeta_simple_on_line`, thm:zeta-mainw2). -/
theorem zeta_simple_on_line (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6733736895 : ℝ) / 10 ^ 10 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  obtain ⟨W, hnu, hLI⟩ := hcert
  have hk1 : ∀ t, |kPsi psiPoly8A t| ≤ 1 := SigmaHelpers.kPsi_abs_le_one psiPoly8A_cont psiPoly8A_pos
  refine eps_form_of_lam_limit (lam₀ := 0)
    (f := fun lam => stabConst (2 - Rlam lam psiPoly8A) 8 (7 / 1700) (199 / 25000) 147) (by norm_num)
    (Eventually.of_forall fun T => Nat.cast_nonneg _) ?_ stab_lim num_stab.le
  intro lam hl
  obtain ⟨Fm, r, hr, hseam⟩ := zeta_gramFamily_poly hl.1 hl.2
  have hA := thmG_abstract Fm.toGramFamily hk1 W (by norm_num) hLI (by norm_num) hBm
  rw [hnu] at hA
  exact eps_seam (fun T => Nat.cast_nonneg _) hA hr hseam

/-- **SC — simple or critical zeros** (the architect's `zeta_simple_or_critical`, cor:oll-SC). -/
theorem zeta_simple_or_critical (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((8879195 : ℝ) / 10 ^ 7 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsc T (2 * T) := by
  refine eps_form_of_lam_limit (lam₀ := 0)
    (f := fun lam => scConst (stabConst (2 - Rlam lam psiPoly8A) 8 (7 / 1700) (199 / 25000) 147)) (by norm_num)
    (Eventually.of_forall fun T => Nat.cast_nonneg _) ?_ sc_lim num_sc.le
  intro lam hl
  obtain ⟨Fm, r, hr, hseam⟩ := zeta_frameFamily_poly_fix hl.1 hl.2
  exact eps_seam (fun T => Nat.cast_nonneg _) (sc_abstract Fm.toFrameFamily hcert) hr
    (hseam.mono fun T h => h.2.2.1)

end Top
end ZetaS
