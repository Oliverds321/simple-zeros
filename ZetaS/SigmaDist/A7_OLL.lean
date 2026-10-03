/-
Node A7 (track K/P, all-marks) — thm:sigd-OLL (l.1320–1345): (OL_L) holds, "ch(M_L) ≤ mg_L + o(N)" with
ch = Σ κ(λ_i), κ(λ) = [(λ − 2)₊² − c*]₊, c* = 2 − 2a₁, mg_L = Slack(𝒪_L) − a₁s₁ − a₂s₂ + νΛ (def:sigd-charge), for the
FrameFamily of ψ = cos 1.6s and the data of CertAM7. The Hermitian proof of M_L is taken as an argument (it is a fact,
not a hypothesis on ζ).
Deps: L7, A5, M1, A6, A1, A1b, A2, N2, N3.

Proof (L4_1, 28 Sep 2026). Statement byte-identical to `lean_work/L0_4/skeleton/A7_OLL.lean` (kept as `A7_OLL_orig.lean`).
  * Per height (`OLL.oll_height`, file `OLLHeight.lean`): the draft's route with 𝒯 = light sites having another light site
    closer than 3/4 and ℛ = the rest: A5 ⇒ λ_max(M_ℛ) ≤ (1 + e′)β < 2 + √c* for any CertMaj threshold β ≤ 33/10; L7 after reindexing
    M_L ≅ [[M_𝒯, M_𝒯ℛ],[M_ℛ𝒯, M_ℛ]]; A6 (new node `tight_chains`) with k* = 1/4 − ε (N2 new node, N3); corrected A2
    (`agg_true_window_of_symm`, C = UᵀU symmetric) on ℛ; A1 on 𝒪_L; A1b on ℛ; exact accounting. Error term
    788·Σ m_ρδ_ρ + 784·ε_T·n + 14·Σ_i(|b_i(1)| + |b_i(2)|).
  * Asymptotics: ε_T (FrameFamily.kernel) and e′_T (FrameFamily.dominate) → 0, so eventually ε ≤ 1/20, e′ ≤ 1/40 (the draft's
    T ≥ T₀); e′_T ≥ 0 is forced by the domination at a single point; Σ mδ = o(N) (defect); n ≤ N(I′) = O(N) (window);
    the boundary constant is o(N) as N → ∞.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L7_SchurLocalisation
import ZetaS.SigmaDist.OLLHeight

open Filter Asymptotics Finset

namespace ZetaS

/-- `e′ ≥ 0` is forced by the domination hypothesis at one point (`k(0) = k_ψ(0) = 1`). -/
lemma OLL.dom_nonneg (F : ZeroFrame) {e' : ℝ} (hdom : IsPosDefKernel (fun t => (1 + e') * kPsi psiCos16 t - F.k t)) :
    0 ≤ e' := by
  have h := (hdom 1 ![0]).diag_nonneg (i := 0)
  simp only [kerMat, Matrix.of_apply, sub_self, F.k_zero,
    SigmaHelpers.kPsi_zero OLL.psi_cont OLL.psi_pos] at h
  linarith

lemma OLL.n_le_Nw (F : ZeroFrame) : (F.n : ℝ) ≤ (F.Nw : ℝ) := by
  have h : F.n ≤ F.Nw := by
    calc F.n = ∑ _i : Fin F.n, 1 := by simp
      _ ≤ ∑ i, F.m i := Finset.sum_le_sum fun i _ => F.one_le_m i
      _ ≤ F.Nw := Nat.le_add_right _ _
  exact_mod_cast h

theorem OLL {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) (hcert : CertAM7) (hmaj : CertMaj)
    (hML : ∀ T, ((Fm.F T).ML).IsHermitian) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      trFun (hML T) (kappaCh (2 - 2 * (1824837 / 10 ^ 8)))
        ≤ (Fm.F T).slackOn (Fm.F T).light ((Fm.F T).sEq 1)
          - 1824837 / 10 ^ 8 * ((Fm.F T).sEq 1 : ℝ) - 1168069 / (5 * 10 ^ 7) * ((Fm.F T).sEq 2 : ℝ)
          + 3 / 250 * (Fm.F T).Λ + r T := by
  obtain ⟨W, ha1, ha2, hnu, hcertW⟩ := hcert
  obtain ⟨e, he, hke⟩ := Fm.kernel
  obtain ⟨e', he', hdom⟩ := Fm.dominate
  set B : ℝ := (∑ i, |W.b i 0|) + ∑ i, |W.b i 1| with hB
  refine ⟨fun T => 788 * (∑ i, ((Fm.F T).m i : ℝ) * (Fm.F T).delta i) + 784 * (e T * ((Fm.F T).Nw : ℝ)) + 14 * B,
    ?_, ?_⟩
  · -- r = o(N)
    have hNw : (fun T => ((Fm.F T).Nw : ℝ)) =O[atTop] N := by
      have h := Fm.window.isBigO.add (isBigO_refl N atTop)
      simpa using h
    have he_o : e =o[atTop] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).mpr he
    have h2 : (fun T => e T * ((Fm.F T).Nw : ℝ)) =o[atTop] N := by
      have := he_o.mul_isBigO hNw
      simpa only [one_mul] using this
    have h3 : (fun _ : ℝ => 14 * B) =o[atTop] N :=
      isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp Fm.N_tendsto))
    exact ((Fm.defect.const_mul_left 788).add (h2.const_mul_left 784)).add h3
  · have hsmall : ∀ᶠ T in atTop, e T < 1 / 20 := he (Iio_mem_nhds (by norm_num))
    have hsmall' : ∀ᶠ T in atTop, e' T < 1 / 40 := he' (Iio_mem_nhds (by norm_num))
    filter_upwards [hke, hdom, hsmall, hsmall'] with T hkT hdT hsT hs'T
    have he0 : 0 ≤ e T := (abs_nonneg _).trans (hkT 0)
    have he'0 : 0 ≤ e' T := OLL.dom_nonneg (Fm.F T) hdT
    unfold CertMaj at hmaj
    have h := OLL.oll_height (Fm.F T) hcertW hmaj (by norm_num) ha1 ha2 hnu he0 hsT.le hkT he'0 hs'T.le hdT (hML T)
    have hn : e T * ((Fm.F T).n : ℝ) ≤ e T * ((Fm.F T).Nw : ℝ) :=
      mul_le_mul_of_nonneg_left (OLL.n_le_Nw (Fm.F T)) he0
    rw [← hB] at h
    linarith

end ZetaS
