/-
Node K7 (track K) — proof of cor:oll-SC (l.675–709), abstract: FrameFamily for ψ̃ and the S8 certificate give
"(scConst(S) − ε)N ≤ N^sc(I′)" with S = stabConst(2 − R, 8, 7/1700, 0.00796, 147).
Deps: L2 at (s,t) = (1, 2+√2), L4 (pinch to the simple block, f = Ψ_{1,t}, and Ψ_{1,t} ≥ Ψ), K5, K6 (fixed-point
identity β′S − τ″ = S − H), K0.
-/
import ZetaS.Interfaces
import ZetaS.SigmaDist.SigmaHelpers
import Zeta23.Assembly
import ZetaS.KSide.K5_TransferMcirc
import ZetaS.KSide.K6_ThmG
import ZetaS.KSide.K6a_StabConstCont
import ZetaS.KSide.K7aux

open Filter Topology Asymptotics RHLinalg

namespace ZetaS

theorem sc_abstract {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiPoly8A)) (hcert : CertS8) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (scConst (stabConst (2 - R) 8 (7 / 1700) (199 / 25000) 147) - ε) * N T
        ≤ ((Fm.F T).NscW : ℝ) := by
  intro ε hε
  obtain ⟨W, hnu, hLI⟩ := hcert
  set Gm := K7aux.gramFamily_of_frame Fm with hGm
  -- the window ψ̃ = psiPoly8A: continuous and positive on [−1/2, 1/2], so |k_ψ̃| ≤ 1
  have hcont : ContinuousOn psiPoly8A (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    (by unfold psiPoly8A; fun_prop : Continuous psiPoly8A).continuousOn
  have hpos : ∀ s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), 0 < psiPoly8A s := by
    intro s hs
    unfold psiPoly8A
    have h1 := hs.1; have h2 := hs.2
    set u := (2 * s) ^ 2 with hu
    have hu0 : 0 ≤ u := sq_nonneg _
    have hu1 : u ≤ 1 := by rw [hu]; nlinarith
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    apply mul_pos (by norm_num)
    nlinarith [pow_nonneg hu0 3, pow_nonneg hu0 4]
  have hk1 : ∀ t, |kPsi psiPoly8A t| ≤ 1 := SigmaHelpers.kPsi_abs_le_one hcont hpos
  -- Φ_m(E) ≤ E
  have hPhiLe : ∀ E : ℝ, PhiM 147 E ≤ E := by
    intro E; unfold PhiM; split_ifs
    · exact le_rfl
    · exact sub_le_self _ (sq_nonneg _)
  have h140 : ((147 : ℕ) : ℝ) - ((8 : ℕ) : ℝ) + 1 = 140 := by norm_num
  have hBm : PhiM 147 ((199 / 25000 : ℝ) * (((147 : ℕ) : ℝ) - ((8 : ℕ) : ℝ) + 1)) < 147 := by
    refine lt_of_le_of_lt (hPhiLe _) ?_; rw [h140]; norm_num
  -- (1) choose c′ < c with scConst(S(c′)) > scConst(S(c)) − ε/3
  have hsc_cont : Continuous scConst := by unfold scConst; fun_prop
  have hcontS : ContinuousAt (fun c => scConst (stabConst (2 - R) 8 (7 / 1700) c 147)) (199 / 25000) :=
    hsc_cont.continuousAt.comp (stabConst_continuousAt (by norm_num) (by norm_num) (by norm_num) hBm)
  have h1 : ∀ᶠ c' in 𝓝 (199 / 25000 : ℝ),
      scConst (stabConst (2 - R) 8 (7 / 1700) (199 / 25000) 147) - ε / 3
        < scConst (stabConst (2 - R) 8 (7 / 1700) c' 147) :=
    hcontS.eventually (lt_mem_nhds (by linarith))
  have h3 : ∀ᶠ c' in 𝓝 (199 / 25000 : ℝ), 0 < c' := lt_mem_nhds (by norm_num)
  have hev : ∀ᶠ c' in 𝓝[<] (199 / 25000 : ℝ),
      (scConst (stabConst (2 - R) 8 (7 / 1700) (199 / 25000) 147) - ε / 3
        < scConst (stabConst (2 - R) 8 (7 / 1700) c' 147) ∧ 0 < c') ∧ c' ∈ Set.Iio (199 / 25000) :=
    ((h1.and h3).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨c', ⟨hc1, hc3⟩, hc4⟩ := hev.exists
  rw [Set.mem_Iio] at hc4
  -- (2) K6 and K5 at c′ on the GramFamily of the frames (K0)
  have hLI' : LocalCert (kPsi psiPoly8A) W c' := KHelp.localCert_mono hLI hc4.le
  have hA'lt : c' * (((147 : ℕ) : ℝ) - ((8 : ℕ) : ℝ) + 1) < 147 := by rw [h140]; linarith
  have hBm' : PhiM 147 (c' * (((147 : ℕ) : ℝ) - ((8 : ℕ) : ℝ) + 1)) < 147 :=
    lt_of_le_of_lt (hPhiLe _) hA'lt
  have hK6 := thmG_abstract Gm hk1 W hc3 hLI' (m := 147) (by norm_num) hBm' (ε / 3) (by linarith)
  obtain ⟨T₁, hT₁⟩ := hK6
  obtain ⟨r1, hr1, hK5⟩ := transfer_Mcirc Gm hk1 W hLI hc3 hc4 (m := 147) (by norm_num)
  -- constants at c′
  set A' := c' * (((147 : ℕ) : ℝ) - ((8 : ℕ) : ℝ) + 1) with hA'
  set B' := PhiM 147 A' with hB'
  have hA'0 : 0 < A' := by rw [hA', h140]; linarith
  have hB'0 : 0 ≤ B' := K2aux.PhiM_nonneg (by norm_num) hA'0.le
  set β := B' / ((147 : ℕ) : ℝ) with hβ
  set C := B' / A' * (W.nu * (((147 : ℕ) : ℝ) - ((8 : ℕ) : ℝ) + 1) / ((147 : ℕ) : ℝ)) with hC
  set S' := stabConst (2 - R) 8 (7 / 1700) c' 147 with hS'
  have hβ0 : 0 ≤ β := div_nonneg hB'0 (by norm_num)
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one (by norm_num)]; have := hPhiLe A'; push_cast; linarith
  have hβ1' : 0 < 1 - β := by
    have : β < 1 := by rw [hβ, div_lt_one (by norm_num)]; exact hBm'
    linarith
  -- fixed point: β S′ − C = S′ − (2 − R)
  have hSdef : S' = ((2 - R) - C) / (1 - β) := by rw [hS', hC, hβ, hB', hA', hnu]; rfl
  have hfix : β * S' - C = S' - (2 - R) := by
    rw [hSdef]; field_simp; ring
  -- t = 2 + √2
  set t := 2 + Real.sqrt 2 with ht
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : t ^ 2 / 4 = (3 + 2 * Real.sqrt 2) / 2 := by rw [ht, add_sq, hs2]; ring
  have hq1 : 1 ≤ t ^ 2 / 4 := by rw [hq]; linarith [Real.sqrt_nonneg 2]
  have hsc : ∀ S, t ^ 2 / 4 * scConst S = 1 / 2 + Real.sqrt 2 + S := by
    intro S; rw [hq]; unfold scConst
    have : (3 + 2 * Real.sqrt 2) ≠ 0 := by positivity
    field_simp
  have hlin : 2 * t - 2 - t ^ 2 / 4 = 1 / 2 + Real.sqrt 2 := by rw [hq, ht]; ring
  -- (3) the per-height inequality
  set err0 : ℝ → ℝ := fun T => -(2 * t) * (rtrace (Fm.F T).Gt - N T) + (frobSq (Fm.F T).Gt - R * N T)
    + t ^ 2 / 4 * (((Fm.F T).Nw : ℝ) - N T) + r1 T with herr0
  have herr0o : err0 =o[atTop] N :=
    (((Fm.trace.const_mul_left (-(2 * t))).add Fm.frob).add (Fm.window.const_mul_left (t ^ 2 / 4))).add hr1
  have hmain : ∀ᶠ T in atTop, (scConst S' - ε / 3) * N T - err0 T / (t ^ 2 / 4) ≤ ((Fm.F T).NscW : ℝ) := by
    filter_upwards [hK5, Fm.N_nonneg, Filter.eventually_ge_atTop T₁] with T hT5 hN hT
    have h6 := hT₁ T hT
    obtain ⟨h, -, -, -, -, -, -, e, he, he1, hV⟩ := K7aux.gramOf_spec (Fm.F T)
    have hsh := K7aux.sc_height (Fm.F T) (K7aux.gramOf (Fm.F T)) h e he he1 hV
    rw [← ht] at hsh
    have hdef : trFun (Matrix.isHermitian_conjTranspose_mul_self (Gm.G T).V) Psi
        = trFun (Matrix.isHermitian_conjTranspose_mul_self (K7aux.gramOf (Fm.F T)).V) Psi := rfl
    rw [hdef] at hT5
    rw [hnu] at h6
    have hs1 : β * (S' - ε / 3) * N T ≤ β * ((Gm.G T).s1 : ℝ) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h6 hβ0
    have hηN : β * (ε / 3) * N T ≤ t ^ 2 / 4 * (ε / 3) * N T := by
      apply mul_le_mul_of_nonneg_right _ hN
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    have hscN : t ^ 2 / 4 * (scConst S' * N T) = (1 / 2 + Real.sqrt 2 + S') * N T := by
      rw [← mul_assoc, hsc]
    have hfixN : β * S' * N T - C * N T = S' * N T - (2 - R) * N T := by
      rw [show β * S' * N T - C * N T = (β * S' - C) * N T by ring, hfix]; ring
    have hlinN : (2 * t - 2 - t ^ 2 / 4) * N T = (1 / 2 + Real.sqrt 2) * N T := by rw [hlin]
    have hq0 : 0 < t ^ 2 / 4 := by linarith
    have key : (scConst S' - ε / 3) * N T * (t ^ 2 / 4) - err0 T ≤ ((Fm.F T).NscW : ℝ) * (t ^ 2 / 4) := by
      simp only [herr0]
      linarith [hsh, hT5, hs1, hηN, hscN, hfixN, hlinN]
    have hre : (scConst S' - ε / 3) * N T - err0 T / (t ^ 2 / 4)
        = ((scConst S' - ε / 3) * N T * (t ^ 2 / 4) - err0 T) / (t ^ 2 / 4) := by
      rw [sub_div, mul_div_cancel_right₀ _ hq0.ne']
    rw [hre, div_le_iff₀ hq0]
    exact key
  have herr : (fun T => err0 T / (t ^ 2 / 4)) =o[atTop] N :=
    (herr0o.const_mul_left (t ^ 2 / 4)⁻¹).congr_left (fun T => by ring)
  obtain ⟨T₀, hT₀⟩ := Zeta23.Assembly.eps_form_of_isLittleO hmain Fm.N_nonneg herr (ε / 3) (by linarith)
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp Fm.N_nonneg
  refine ⟨max T₀ T₂, fun T hT => ?_⟩
  have hN := hT₂ T (le_trans (le_max_right _ _) hT)
  have h := hT₀ T (le_trans (le_max_left _ _) hT)
  have hmono : (scConst (stabConst (2 - R) 8 (7 / 1700) (199 / 25000) 147) - ε) * N T
      ≤ (scConst S' - ε / 3 - ε / 3) * N T := mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

end ZetaS
