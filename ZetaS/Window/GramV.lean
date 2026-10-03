/-
rh72/lean_work/L0_2/GramV.lean — node W9.8: the Gram-level asymptotics that the architect's `GramFamily` asks for
(Interfaces.lean: fields `trace`, `frob`, `window`), for the window family `P.atV ψ` of any admissible profile, at fixed
bandwidth λ < 1, in the tree's little-o idiom:
  tr Ĝ − N = o(N),   ‖Ĝ‖²_F − R_λ(ψ)·N = o(N)  (TWO-sided),   N(I′) − N = o(N),
with Ĝ = (P.atV ψ T).hat T (Z.Gz (P.atV ψ T) T) (all zeros, hat units (aL²)⁻¹) and R_λ(ψ) = 1/c_λ(ψ).
The upper half of the Frobenius asymptotics is the tree's `frhat`; the lower half comes from `ratio`
(tr G̃)²/tr G̃² = c_T N(1 + O(E_T)) and the trace (`frob_two_sided_alg`).  No `sorry`.
-/
import ZetaS.Window.HeadlineV

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace ZetaS
namespace GramV

open Zeta23 Zeta23.ThmD Zeta23.Assembly ZetaS.ProfileMoments ZetaS.ProfileAutocorr ZetaS.TracesV

/-- the hat-units Gram matrix of the family at height `T` (all zeros). -/
def Ghat (Z : ZeroConfig) (P : Params) (v : ℝ → ℝ) (T : ℝ) :=
  (P.atV v T).hat T (Z.Gz (P.atV v T) T)

/-- the algebra of the two-sided Frobenius bound: from the trace (|x − N| ≤ R), the upper bound
y − N/c ≤ E₂·N/c and the ratio bound |x²/y − cN| ≤ E₃·cN (E₃ < 1): |y − N/c| ≤ ((E₂ + E₃)N + 2R)/c. -/
theorem frob_two_sided_alg {x y N cT R E₂ E₃ : ℝ} (hN : 0 < N) (hc : 0 < cT) (hy : 0 ≤ y) (hR0 : 0 ≤ R)
    (hR2 : 2 * R ≤ N) (hx : |x - N| ≤ R) (hE2 : 0 ≤ E₂) (hE3 : 0 ≤ E₃) (hE31 : E₃ < 1)
    (hup : y - N / cT ≤ E₂ * (N / cT)) (hratio : |x ^ 2 / y - cT * N| ≤ E₃ * (cT * N)) :
    |y - N / cT| ≤ ((E₂ + E₃) * N + 2 * R) / cT := by
  have hcN : 0 < cT * N := mul_pos hc hN
  have hy0 : 0 < y := by
    rcases hy.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, div_zero, zero_sub, abs_neg, abs_of_pos hcN] at hratio
      nlinarith
  have hq : x ^ 2 / y ≤ (1 + E₃) * (cT * N) := by
    have := (abs_le.mp hratio).2; linarith
  have hx2 : x ^ 2 ≤ (1 + E₃) * (cT * N) * y := by rwa [div_le_iff₀ hy0] at hq
  have hxlow : N - R ≤ x := by have := (abs_le.mp hx).1; linarith
  have hx0 : 0 ≤ N - R := by linarith
  have hsq : (N - R) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hx0 hxlow 2
  have key : N - 2 * R ≤ (1 + E₃) * (cT * y) := by
    have h1 : N * (N - 2 * R) ≤ N * ((1 + E₃) * (cT * y)) := by nlinarith
    exact le_of_mul_le_mul_left h1 hN
  have hcy : 0 ≤ cT * y := (mul_pos hc hy0).le
  have hlow : N - cT * y ≤ E₃ * N + 2 * R := by
    rcases le_or_gt (cT * y) N with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h hE3]
    · nlinarith
  have hlow' : N / cT - y ≤ (E₃ * N + 2 * R) / cT := by
    rw [show N / cT - y = (N - cT * y) / cT by field_simp]
    exact div_le_div_of_nonneg_right hlow hc.le
  have hup' : y - N / cT ≤ ((E₂ + E₃) * N + 2 * R) / cT := by
    have : E₂ * (N / cT) ≤ ((E₂ + E₃) * N + 2 * R) / cT := by
      rw [mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hc.le
      nlinarith [mul_nonneg hE3 hN.le]
    linarith
  rw [abs_le]
  constructor
  · have : (E₃ * N + 2 * R) / cT ≤ ((E₂ + E₃) * N + 2 * R) / cT := by
      apply div_le_div_of_nonneg_right _ hc.le
      nlinarith [mul_nonneg hE2 hN.le]
    linarith
  · exact hup'

/-- **W9.8: two-sided trace and Frobenius asymptotics and the window count, for the family `P.atV ψ`** (hypotheses as
`HeadlineV.simple_V_lam_abstract`). -/
theorem gram_asymptotics_V (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    {v : ℝ → ℝ} (hv : CoreProfile v) (heven : ∀ s, v (-s) = v s) {cW : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w cW)
    (ha : 1 / 2 < ∫ s in (-(1:ℝ)/2)..(1/2), v s) (hb : 1 / 2 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)
    (hJ : 0 ≤ XiPrime.jWin id P.lam v) :
    (fun T => rtrace (Ghat Z P v T) - (Z.N T (2 * T) : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧
    (fun T => frobSq (Ghat Z P v T) - (XiPrime.cWin id P.lam v)⁻¹ * (Z.N T (2 * T) : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧
    (fun T => (Z.NIprime T : ℝ) - (Z.N T (2 * T) : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  have hLoc : LocalHypsCoreVEventually P v cW := localHypsCore_eventually hP hv (K := 8) le_rfl hadm hb
  have hTr := tracesBoundsV (Z := Z) hP H hadm hLoc
  have hLJ : 0 ≤ P.lam * XiPrime.jWin id P.lam v := mul_nonneg hP.lam_pos.le hJ
  have hden : 0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + P.lam * XiPrime.jWin id P.lam v := by linarith
  have hc := tendsto_cRatioV hP hv hadm hden
  set c := XiPrime.cWin id P.lam v with hcdef
  have hc0 : 0 < c := by
    rw [hcdef]; unfold XiPrime.cWin
    exact div_pos (mul_pos hP.lam_pos (pow_pos (by linarith) 2)) hden
  have hab := (concreteFactsV hP H hadm hLoc).ab_range
  have h8 : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := Params.eventually_w8 hP
  have hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atV v T) T = (P.atV v T).Gp T := by
    filter_upwards [h8] with T hT
    exact XiPrime.GzGpV_of' hP heven hadm Z H.EF hT
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨C₃, hC₃, T₃, hra⟩ := hTr.ratio
  set D := concreteDataV P v Z with hD
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cT : ℝ → ℝ := fun T => cRatio (P.lam1 T) (D.aT T) (D.bT T) (D.JT T) with hcTdef
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / D.aT T with hR₁
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have hcT : Tendsto cT atTop (𝓝 c) := hc
  have hcinv : Tendsto (fun T => (cT T)⁻¹) atTop (𝓝 c⁻¹) := hcT.inv₀ hc0.ne'
  have hcalE := calE_tendsto_zero P hlam0 hlam1 (zero_le_one.trans hP.one_le_w)
  -- R₁ = o(N)  (as in ThmD.thmD_mult2_abstract)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / D.aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hab] with T ha2
      have ha1 : 1 / 2 ≤ D.aT T := ha2.1.trans ha2.2.1
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith))]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  -- the hat-unit identities
  have hxy : ∀ᶠ T in atTop, rtrace (Ghat Z P v T) = (D.aT T * P.L T)⁻¹ * D.trG T ∧
      frobSq (Ghat Z P v T) = ((D.aT T * P.L T)⁻¹) ^ 2 * D.trG2 T := by
    filter_upwards [hGzGp] with T hGG
    have hida : (P.atV v T).a T = D.aT T := Params.atV_a T hP heven
    constructor
    · unfold Ghat
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, Params.atV_trGtilde T hP heven, hida]; rfl
    · unfold Ghat
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, Params.atV_trGtildeSq T hP heven, hida]; rfl
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ D.aT T := hab.mono fun T h => h.1.trans h.2.1
  have hLpos : ∀ᶠ T in atTop, 0 < P.L T := (tendsto_L_atTop P hlam0).eventually_gt_atTop 0
  -- (1) the trace
  have htrb : ∀ᶠ T in atTop, |rtrace (Ghat Z P v T) - N T| ≤ R₁ T := by
    filter_upwards [hxy, hapos, hLpos, eventually_ge_atTop T₁] with T hT haT hL hT1
    rw [hT.1]
    exact trGhat_sub_N_le (by linarith) hL (htr1 T hT1)
  have otr : (fun T => rtrace (Ghat Z P v T) - N T) =o[atTop] N := by
    refine IsBigO.trans_isLittleO ?_ o1
    refine IsBigO.of_bound 1 ?_
    filter_upwards [htrb] with T h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    exact h.trans (le_abs_self _)
  refine ⟨otr, ?_, ?_⟩
  · -- (2) the Frobenius norm
    have hR2 : ∀ᶠ T in atTop, 2 * R₁ T ≤ N T := by
      have := o1.bound (show (0:ℝ) < 1 / 2 by norm_num)
      filter_upwards [this, hNtop.eventually_ge_atTop 0] with T h hN0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at h
      linarith [le_abs_self (R₁ T)]
    have hR0 : ∀ᶠ T in atTop, 0 ≤ R₁ T := by
      filter_upwards [hapos] with T haT
      exact div_nonneg (mul_nonneg hC₁.le (Real.sqrt_nonneg _)) (by linarith)
    have hE3 : ∀ᶠ T in atTop, C₃ * P.calE T < 1 := by
      have : Tendsto (fun T => C₃ * P.calE T) atTop (𝓝 0) := by simpa using hcalE.const_mul C₃
      exact this.eventually (gt_mem_nhds (by norm_num))
    have hEnn : ∀ᶠ T in atTop, 0 ≤ P.calE T := eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w)
    have hcTpos : ∀ᶠ T in atTop, 0 < cT T := hcT.eventually (lt_mem_nhds hc0)
    have hNpos : ∀ᶠ T in atTop, 0 < N T := hNtop.eventually_gt_atTop 0
    set err : ℝ → ℝ := fun T => ((C₂ + C₃) * P.calE T * N T + 2 * R₁ T) * (cT T)⁻¹
      + |(cT T)⁻¹ - c⁻¹| * N T with herr
    have hbound : ∀ᶠ T in atTop, |frobSq (Ghat Z P v T) - c⁻¹ * N T| ≤ err T := by
      filter_upwards [hxy, hapos, hLpos, htrb, hR2, hR0, hE3, hEnn, hcTpos, hNpos,
        eventually_ge_atTop T₂, eventually_ge_atTop T₃] with T hT haT hL htb hR2T hR0T hE3T hEnnT hcTT hNT hT2 hT3
      have haL : 0 < D.aT T * P.L T := mul_pos (by linarith) hL
      set x := rtrace (Ghat Z P v T)
      set y := frobSq (Ghat Z P v T)
      have hy0 : 0 ≤ y := frobSq_nonneg _
      -- the upper bound (frhat)
      have hup : y - N T / cT T ≤ (C₂ * P.calE T) * (N T / cT T) := by
        have h := hfr2 T hT2
        simp only at h
        have h1 : D.trG2 T / (D.aT T * P.L T) ^ 2 - (cT T)⁻¹ * N T
            ≤ C₂ * (P.calE T * ((cT T)⁻¹ * N T)) :=
          le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
        have e1 : y = D.trG2 T / (D.aT T * P.L T) ^ 2 := by
          rw [hT.2, inv_pow, div_eq_inv_mul]
        rw [e1, div_eq_inv_mul (N T)]
        calc D.trG2 T / (D.aT T * P.L T) ^ 2 - (cT T)⁻¹ * N T ≤ C₂ * (P.calE T * ((cT T)⁻¹ * N T)) := h1
          _ = C₂ * P.calE T * ((cT T)⁻¹ * N T) := by ring
      -- the ratio bound
      have hrat : |x ^ 2 / y - cT T * N T| ≤ (C₃ * P.calE T) * (cT T * N T) := by
        have h := hra T hT3
        simp only at h
        have e2 : x ^ 2 / y = D.trG T ^ 2 / D.trG2 T := by
          rw [hT.1, hT.2, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero haL.ne'))]
        rw [e2]
        calc |D.trG T ^ 2 / D.trG2 T - cT T * N T| ≤ C₃ * (P.calE T * (cT T * N T)) := h
          _ = C₃ * P.calE T * (cT T * N T) := by ring
      have hmain := frob_two_sided_alg hNT hcTT hy0 hR0T hR2T htb
        (mul_nonneg hC₂.le hEnnT) (mul_nonneg hC₃.le hEnnT) hE3T hup hrat
      have hdrift : |N T / cT T - c⁻¹ * N T| = |(cT T)⁻¹ - c⁻¹| * N T := by
        rw [div_eq_inv_mul, ← sub_mul, abs_mul, abs_of_pos hNT]
      calc |y - c⁻¹ * N T| ≤ |y - N T / cT T| + |N T / cT T - c⁻¹ * N T| := abs_sub_le _ _ _
        _ ≤ ((C₂ * P.calE T + C₃ * P.calE T) * N T + 2 * R₁ T) / cT T + |(cT T)⁻¹ - c⁻¹| * N T := by
          rw [hdrift]; linarith
        _ = err T := by rw [herr]; simp only; rw [div_eq_mul_inv]; ring
    -- err = o(N)
    have hcinvO : (fun T => (cT T)⁻¹) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
      have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
      filter_upwards [hcinv.eventually (eventually_ge_nhds hcpos),
        hcinv.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have oa : (fun T => (C₂ + C₃) * P.calE T * N T * (cT T)⁻¹) =o[atTop] N := by
      have hE0 : Tendsto (fun T => (C₂ + C₃) * P.calE T) atTop (𝓝 0) := by
        simpa using hcalE.const_mul (C₂ + C₃)
      have := isLittleO_of_bdd_mul hcinvO (isLittleO_of_tendsto_zero_mul (g := N) hE0)
      exact this.congr_left fun T => by ring
    have ob : (fun T => 2 * R₁ T * (cT T)⁻¹) =o[atTop] N := by
      have := isLittleO_of_bdd_mul hcinvO (o1.const_mul_left 2)
      exact this.congr_left fun T => by ring
    have oc : (fun T => |(cT T)⁻¹ - c⁻¹| * N T) =o[atTop] N := by
      refine isLittleO_of_tendsto_zero_mul ?_
      have : Tendsto (fun T => (cT T)⁻¹ - c⁻¹) atTop (𝓝 0) := by simpa using hcinv.sub_const c⁻¹
      simpa using this.abs
    have oerr : err =o[atTop] N := by
      have := (oa.add ob).add oc
      exact this.congr_left fun T => by rw [herr]; simp only; ring
    refine IsBigO.trans_isLittleO ?_ oerr
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hbound] with T h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    exact h.trans (le_abs_self _)
  · -- (3) the window count N(I′) = N + N(I′∖I), N(I′∖I) = o(N)
    obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
    obtain ⟨CII, hII⟩ := Tail.eventually_NII_le Z hA₀ hloc
    have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
      have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
        refine IsBigO.of_bound CII ?_
        filter_upwards [hII, eventually_l_pos] with T h hl
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_nonneg (by positivity)]
        simpa [mul_assoc] using h
      exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
    refine o3.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    rw [NIprime_eq Z hT]
    push_cast
    ring

/-! ## ζ instances (fixed λ ∈ (0,1)) -/

/-- **W9.8 for ζ, poly8A (ψ♮ = (4/5)v), at fixed λ ∈ (0,1)**, UNCONDITIONAL. -/
theorem zeta_gram_poly8A_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    let P := paramsOf stdProfile lam
    let N := fun T => (zetaZeroConfig.N T (2 * T) : ℝ)
    (fun T => rtrace (Ghat zetaZeroConfig P PolyWindow.psiN T) - N T) =o[atTop] N ∧
    (fun T => frobSq (Ghat zetaZeroConfig P PolyWindow.psiN T)
        - (ThmD.cRatio lam (40497 / 43750) (16536677606497 / 19144125000000)
            (166041852098299 / 606230625000000))⁻¹ * N T) =o[atTop] N ∧
    (fun T => (zetaZeroConfig.NIprime T : ℝ) - N T) =o[atTop] N := by
  intro P N
  have hP : P.Valid := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have heven : ∀ s, PolyWindow.psiN (-s) = PolyWindow.psiN s := fun s => by
    unfold PolyWindow.psiN; rw [PolyWindow.vP8_even]
  have h := gram_asymptotics_V zetaZeroConfig paperInputs_zeta P hP h1
    WindowInstances.coreProfile_psiN heven
    (fun T hT => by
      rw [PolyWindow.phiV_eq_phiP8]; exact PolyWindow.admWindow_phiP8 hP.taper hP.one_le_w hT)
    (by rw [PolyWindow.integral_psiN]; norm_num) (by rw [PolyWindow.integral_psiN_sq]; norm_num)
    (by rw [WindowLimits.jWin_psiN]; have := hP.lam_pos; positivity)
  rw [WindowLimits.cWin_psiN hP.lam_pos] at h
  exact h

/-- **W9.8 for ζ, window cos(8/5·s), at fixed λ ∈ (0,1)**, UNCONDITIONAL. -/
theorem zeta_gram_cos85_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    let P := paramsOf stdProfile lam
    let N := fun T => (zetaZeroConfig.N T (2 * T) : ℝ)
    (fun T => rtrace (Ghat zetaZeroConfig P (CosWindow.cosW (8 / 5)) T) - N T) =o[atTop] N ∧
    (fun T => frobSq (Ghat zetaZeroConfig P (CosWindow.cosW (8 / 5)) T)
        - (ThmD.cRatio lam (CosWindow.aC (8 / 5)) (CosWindow.bC (8 / 5)) (CosWindow.jC (8 / 5)))⁻¹ * N T)
        =o[atTop] N ∧
    (fun T => (zetaZeroConfig.NIprime T : ℝ) - N T) =o[atTop] N := by
  intro P N
  have hP : P.Valid := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have hα0 : (0:ℝ) < 8 / 5 := by norm_num
  have h := gram_asymptotics_V zetaZeroConfig paperInputs_zeta P hP h1
    (WindowInstances.coreProfile_cosW hα0 le_rfl) (CosWindow.cosW_even (8 / 5))
    (fun T hT => CosWindow.admWindow_phiV_cos hP hα0 le_rfl hT)
    (by rw [WindowInstances.half_interval, CosWindow.integral_cosW hα0.ne']; exact HeadlineV.aC_eight_fifths)
    (by rw [WindowInstances.half_interval, CosWindow.integral_cosW_sq hα0.ne']
        exact WindowInstances.half_lt_bC hα0 le_rfl)
    (by rw [HeadlineV.jWin_cosW _ _ hα0.ne']; exact mul_nonneg hP.lam_pos.le (HeadlineV.jC_nonneg hα0 le_rfl))
  rw [WindowLimits.cWin_cosW hα0.ne' hP.lam_pos] at h
  exact h

end GramV
end ZetaS

end

#print axioms ZetaS.GramV.frob_two_sided_alg
#print axioms ZetaS.GramV.gram_asymptotics_V
#print axioms ZetaS.GramV.zeta_gram_poly8A_lam
#print axioms ZetaS.GramV.zeta_gram_cos85_lam
