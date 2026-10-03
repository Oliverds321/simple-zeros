/-
L7_5 (28 Sep 2026), round 8: reduction of `ZO_nsp` to a single-frequency non-stationary phase lemma.
  `𝓕H̃(η) = ∫_{T}^{2T} J_β(γ−τ, 2πη) dτ`,  `J_β(λ, c) = ∫ Ξ(u/κ) e^{(β−1/2)u} e^{i(λu − c e^u)} du`
(substitution `t = e^u` and Fubini), and `∫_T^{2T} |γ−τ|^{−m} dτ ≤ D^{1−m}` (`tau_bound`).
Leaf `nsp_single`: `|J_β(λ, c)| ≤ C |λ|^{−m}` when `4|c|e^κ ≤ |λ|`, uniformly in `β ∈ [0,1]`.
-/
import ZetaShell.PropZ.ZZ2e_Fourier
import ZetaShell.PropZ.ZZ2h_NspCore

open MeasureTheory FourierTransform Complex

namespace ZetaShell.PropZ

theorem tau_bound (γ T : ℝ) (hT : 0 ≤ T) (n : ℕ) (hD : 1 ≤ |γ| - 2 * T) :
    (∫ τ in Set.Ioc T (2 * T), 1 / |γ - τ| ^ (n + 2)) ≤ 1 / (|γ| - 2 * T) ^ (n + 1) := by
  set D := |γ| - 2 * T with hDdef
  have hD0 : 0 < D := by linarith
  have hT2 : T ≤ 2 * T := by linarith
  -- pointwise: `|γ − τ| ≥ D + dist`, in the two sign cases
  rcases le_or_gt 0 γ with hg | hg
  · have habs : |γ| = γ := abs_of_nonneg hg
    have hpt : ∀ τ ∈ Set.Icc T (2 * T), 1 / |γ - τ| ^ (n + 2) = 1 / (D + 2 * T - τ) ^ (n + 2) := fun τ hτ => by
      rw [abs_of_nonneg (by linarith [hτ.2])]; congr 2; rw [hDdef, habs]; ring
    have hF : ∀ τ ∈ Set.uIcc T (2 * T), HasDerivAt (fun τ => ((D + 2 * T - τ) ^ (n + 1))⁻¹ / ((n + 1 : ℕ) : ℝ))
        (1 / (D + 2 * T - τ) ^ (n + 2)) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le hT2] at hτ
      have hy : 0 < D + 2 * T - τ := by linarith [hτ.2]
      have h1 : HasDerivAt (fun τ => D + 2 * T - τ) (-1) τ := (hasDerivAt_id τ).const_sub _ |>.congr_deriv (by simp)
      have h2 := ((h1.pow (n + 1)).inv (pow_ne_zero _ hy.ne')).div_const (((n + 1 : ℕ) : ℝ))
      refine h2.congr_deriv ?_
      have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      simp only [Nat.add_sub_cancel, Pi.pow_apply]
      field_simp
      ring
    have hcont : ContinuousOn (fun τ => 1 / (D + 2 * T - τ) ^ (n + 2)) (Set.uIcc T (2 * T)) := by
      rw [Set.uIcc_of_le hT2]
      refine ContinuousOn.div continuousOn_const ((continuous_const.sub continuous_id).pow (n + 2)).continuousOn ?_
      intro τ hτ; exact pow_ne_zero _ (by linarith [hτ.2])
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable)
    rw [← intervalIntegral.integral_of_le hT2]
    rw [intervalIntegral.integral_congr (g := fun τ => 1 / (D + 2 * T - τ) ^ (n + 2)) (fun τ hτ => by
      rw [Set.uIcc_of_le hT2] at hτ; exact hpt τ hτ), hFTC]
    simp only [show D + 2 * T - 2 * T = D by ring, show D + 2 * T - T = D + T by ring]
    have hm1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hA : 0 ≤ ((D + T) ^ (n + 1))⁻¹ / ((n + 1 : ℕ) : ℝ) := by positivity
    have hB : ((D ^ (n + 1))⁻¹) / ((n + 1 : ℕ) : ℝ) ≤ (D ^ (n + 1))⁻¹ :=
      div_le_self (by positivity) hm1
    rw [one_div]
    linarith
  · -- `γ < 0`: `|γ − τ| ≥ D + T` on `[T, 2T]`
    have habs : |γ| = -γ := abs_of_neg hg
    have hb : ∀ τ ∈ Set.Ioc T (2 * T), 1 / |γ - τ| ^ (n + 2) ≤ 1 / (D + T) ^ (n + 2) := fun τ hτ => by
      apply one_div_le_one_div_of_le (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      rw [abs_of_neg (by linarith [hτ.1])]
      rw [hDdef, habs]; linarith [hτ.1, hτ.2]
    calc (∫ τ in Set.Ioc T (2 * T), 1 / |γ - τ| ^ (n + 2)) ≤ ∫ τ in Set.Ioc T (2 * T), 1 / (D + T) ^ (n + 2) := by
          apply setIntegral_mono_on _ (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc hb
          refine (ContinuousOn.integrableOn_Icc (a := T) (b := 2 * T) ?_).mono_set Set.Ioc_subset_Icc_self
          refine ContinuousOn.div continuousOn_const ((continuous_const.sub continuous_id).abs.pow (n + 2)).continuousOn ?_
          intro τ hτ; exact pow_ne_zero _ (by rw [abs_ne_zero]; linarith [hτ.1])
      _ = T * (1 / (D + T) ^ (n + 2)) := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hT2]; ring
      _ ≤ 1 / D ^ (n + 1) := by
          rw [pow_succ]
          rw [show T * (1 / ((D + T) ^ (n + 1) * (D + T))) = (T / (D + T)) * (1 / (D + T) ^ (n + 1)) by
            field_simp]
          have h1 : T / (D + T) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          have h2 : 1 / (D + T) ^ (n + 1) ≤ 1 / D ^ (n + 1) :=
            one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hD0.le (by linarith) _)
          calc T / (D + T) * (1 / (D + T) ^ (n + 1)) ≤ 1 * (1 / (D + T) ^ (n + 1)) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ 1 / D ^ (n + 1) := by rw [one_mul]; exact h2


/-- the amplitude in the variable `u = log t`. -/
noncomputable def bamp (κ : ℝ) (Ξ : ℝ → ℝ) (β u : ℝ) : ℝ := Ξ (u / κ) * Real.exp ((β - 1 / 2) * u)

/-- the single-frequency oscillatory integral. -/
noncomputable def Jfun (κ : ℝ) (Ξ : ℝ → ℝ) (β lam c : ℝ) : ℂ :=
  ∫ u : ℝ, ((bamp κ Ξ β u : ℝ) : ℂ) * Complex.exp (I * ((lam : ℂ) * u - (c : ℂ) * (Real.exp u : ℂ)))

/-- non-stationary phase (PROVED in round 9 via `ZetaShell.NSP.nsp_core`, ZZ2h_NspCore.lean) for `λu − c e^u` (`4|c|e^κ ≤ |λ|`), uniformly in `β ∈ [0,1]`. -/
theorem nsp_single (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 → ∀ lam c : ℝ, lam ≠ 0 → 4 * |c| * Real.exp κ ≤ |lam| →
      ‖Jfun κ Ξ β lam c‖ ≤ C / |lam| ^ m := by
  obtain ⟨C, hC0, hC⟩ := ZetaShell.NSP.nsp_core κ hκ hκ1 Ξ hΞ m
  exact ⟨C, hC0, fun β h0 h1 lam c hl hc => by unfold Jfun bamp; exact hC β h0 h1 lam c hl hc⟩

theorem bamp_integrable (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (β : ℝ) :
    Integrable (fun u => bamp κ Ξ β u) := by
  have hc : Continuous (fun u => bamp κ Ξ β u) := by
    unfold bamp; exact (hΞ.smooth.continuous.comp (by fun_prop)).mul (by fun_prop)
  refine hc.integrable_of_hasCompactSupport ?_
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := -κ) (b := κ)) (isClosed_tsupport _) ?_
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra hc'
  apply hu
  have : u / κ ∉ tsupport Ξ := by
    intro h
    have h' := hΞ.supp h
    apply hc'
    have h1 := h'.1; have h2 := h'.2
    rw [lt_div_iff₀ hκ] at h1; rw [div_lt_iff₀ hκ] at h2
    exact ⟨by linarith, by linarith⟩
  show Ξ (u / κ) * Real.exp ((β - 1 / 2) * u) = 0
  rw [image_eq_zero_of_notMem_tsupport this, zero_mul]

theorem fourier_Htil_eq (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (T : ℝ) (hT : 0 ≤ T)
    (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (η : ℝ) :
    𝓕 (Htil T κ Ξ ρ) η
      = ∫ τ in Set.Ioc T (2 * T), Jfun κ Ξ ρ.re (ρ.im - τ) (2 * Real.pi * η) := by
  have hT2 : T ≤ 2 * T := by linarith
  set G : ℝ → ℂ := fun t => Complex.exp ((((-2 * Real.pi * (t * η) : ℝ)) : ℂ) * I) * Htil T κ Ξ ρ t with hG
  have hA1 : 𝓕 (Htil T κ Ξ ρ) η = ∫ t, G t := by
    rw [Real.fourier_eq']
    congr 1; funext t
    rw [smul_eq_mul, Real.inner_apply]
  have hGz : ∀ t, t < Real.exp (-κ) → G t = 0 := fun t ht => by
    simp only [hG]
    rw [Htil_zero_off κ hκ Ξ hΞ T ρ hρ0 hρ1 t (fun h => absurd h.1 (not_le.mpr ht)), mul_zero]
  have hlt : Real.exp (-κ - 1) < Real.exp (-κ) := Real.exp_lt_exp.mpr (by linarith)
  have hA2 : (∫ t, G t) = ∫ x, Real.exp x • G (Real.exp x) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi (Real.exp (-κ - 1)))
      (fun t ht => hGz t (lt_of_le_of_lt (not_lt.mp ht) hlt)), ← integral_comp_exp_Ioi G (-κ - 1)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    have : Real.exp x < Real.exp (-κ) :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr (not_lt.mp hx)) hlt
    rw [hGz _ this, smul_zero]
  set F : ℝ → ℝ → ℂ := fun x τ => ((bamp κ Ξ ρ.re x : ℝ) : ℂ)
      * Complex.exp (I * (((ρ.im - τ : ℝ) : ℂ) * x - ((2 * Real.pi * η : ℝ) : ℂ) * (Real.exp x : ℂ))) with hF
  have hA3 : ∀ x, Real.exp x • G (Real.exp x) = ∫ τ in Set.Ioc T (2 * T), F x τ := by
    intro x
    have hHt : Htil T κ Ξ ρ (Real.exp x) = ZetaShell.DTFacts.DTf T (-x) * ((Ξ (x / κ) : ℝ) : ℂ)
        * Complex.exp ((x : ℂ) * (ρ - 3 / 2)) := by
      unfold Htil Hrho
      rw [Set.indicator_of_mem (show Real.exp x ∈ Set.Ioi (0 : ℝ) from Real.exp_pos x), DT_eq_DTf,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
        ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
    have hDT : ZetaShell.DTFacts.DTf T (-x) = ∫ τ in Set.Ioc T (2 * T), Complex.exp (I * τ * (-x : ℝ)) := by
      unfold ZetaShell.DTFacts.DTf; rw [intervalIntegral.integral_of_le hT2]
    simp only [hG]
    rw [hHt, hDT, real_smul]
    rw [show (Real.exp x : ℂ) * (Complex.exp (((-2 * Real.pi * (Real.exp x * η) : ℝ) : ℂ) * I)
        * ((∫ τ in Set.Ioc T (2 * T), Complex.exp (I * τ * (-x : ℝ))) * ((Ξ (x / κ) : ℝ) : ℂ)
          * Complex.exp ((x : ℂ) * (ρ - 3 / 2))))
        = ((Real.exp x : ℂ) * Complex.exp (((-2 * Real.pi * (Real.exp x * η) : ℝ) : ℂ) * I)
          * ((Ξ (x / κ) : ℝ) : ℂ) * Complex.exp ((x : ℂ) * (ρ - 3 / 2)))
          * ∫ τ in Set.Ioc T (2 * T), Complex.exp (I * τ * (-x : ℝ)) by ring]
    rw [← integral_const_mul]
    congr 1; funext τ
    simp only [hF, bamp]
    rw [← Complex.re_add_im ρ]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, add_zero]
    push_cast
    rw [show ∀ a b c d : ℂ, Complex.exp a * Complex.exp b * ((Ξ (x / κ) : ℝ) : ℂ) * Complex.exp c
        * Complex.exp d = ((Ξ (x / κ) : ℝ) : ℂ) * Complex.exp (a + b + c + d) from fun a b c d => by
          rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]; ring]
    rw [mul_assoc (((Ξ (x / κ) : ℝ) : ℂ)), ← Complex.exp_add]
    congr 2
    ring
  have hFint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Set.Ioc T (2 * T)))) := by
    have hb := (bamp_integrable κ hκ Ξ hΞ ρ.re).norm
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc T (2 * T))) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    refine Integrable.mono' (hb.mul_prod h1) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have hc : Continuous (Function.uncurry F) := by
        simp only [hF, bamp]
        have hΞc := hΞ.smooth.continuous
        fun_prop
      exact hc.aestronglyMeasurable
    · simp only [Function.uncurry, hF, mul_one]
      rw [norm_mul, Complex.norm_real]
      have : ‖Complex.exp (I * (((ρ.im - p.2 : ℝ) : ℂ) * p.1 - ((2 * Real.pi * η : ℝ) : ℂ) * (Real.exp p.1 : ℂ)))‖ = 1 := by
        rw [show I * (((ρ.im - p.2 : ℝ) : ℂ) * p.1 - ((2 * Real.pi * η : ℝ) : ℂ) * (Real.exp p.1 : ℂ))
          = (((ρ.im - p.2) * p.1 - 2 * Real.pi * η * Real.exp p.1 : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      rw [this, mul_one]
  rw [hA1, hA2]
  simp only [hA3]
  rw [integral_integral_swap hFint]
  rfl

theorem ZO_nsp' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 → 1 ≤ |ρ.im| - 2 * T →
      ∀ η : ℝ, |η| ≤ (|ρ.im| - 2 * T) / (8 * Real.pi * Real.exp 1) →
      ‖𝓕 (Htil T κ Ξ ρ) η‖ ≤ C₃ / (|ρ.im| - 2 * T) ^ (k + 1) := by
  obtain ⟨C, hC0, hC⟩ := nsp_single κ hκ hκ1 Ξ hΞ (k + 2)
  refine ⟨C, hC0, fun T hT ρ hρ0 hρ1 hD η hη => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hT2 : T ≤ 2 * T := by linarith
  set D := |ρ.im| - 2 * T with hDdef
  have hD0 : 0 < D := by linarith
  rw [fourier_Htil_eq κ hκ Ξ hΞ T hT0 ρ hρ0 hρ1 η]
  have hne : ∀ τ ∈ Set.Icc T (2 * T), ρ.im - τ ≠ 0 := fun τ hτ h => by
    have : |ρ.im| ≤ 2 * T := by
      have e : ρ.im = τ := by linarith
      rw [e, abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.2]
    linarith
  have hge : ∀ τ ∈ Set.Icc T (2 * T), D ≤ |ρ.im - τ| := fun τ hτ => by
    have := abs_sub_abs_le_abs_sub ρ.im τ
    rw [abs_of_nonneg (by linarith [hτ.1] : (0 : ℝ) ≤ τ)] at this
    linarith [hτ.2]
  have hcond : ∀ τ ∈ Set.Icc T (2 * T), 4 * |2 * Real.pi * η| * Real.exp κ ≤ |ρ.im - τ| := fun τ hτ => by
    have he : Real.exp κ ≤ Real.exp 1 := Real.exp_le_exp.mpr hκ1
    have h1 : |2 * Real.pi * η| = 2 * Real.pi * |η| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    rw [h1]
    have h2 : 8 * Real.pi * Real.exp 1 * |η| ≤ D := by
      rw [le_div_iff₀ (by positivity)] at hη; linarith
    have h3 : 4 * (2 * Real.pi * |η|) * Real.exp κ ≤ 8 * Real.pi * Real.exp 1 * |η| := by
      have := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 8 * Real.pi * |η|)
      nlinarith
    linarith [hge τ hτ]
  have hbound : ∀ τ ∈ Set.Ioc T (2 * T),
      ‖Jfun κ Ξ ρ.re (ρ.im - τ) (2 * Real.pi * η)‖ ≤ C * (1 / |ρ.im - τ| ^ (k + 2)) := fun τ hτ => by
    have hτ' : τ ∈ Set.Icc T (2 * T) := Set.Ioc_subset_Icc_self hτ
    rw [← div_eq_mul_one_div]
    exact hC ρ.re hρ0.le hρ1.le (ρ.im - τ) (2 * Real.pi * η) (hne τ hτ') (hcond τ hτ')
  have hint : IntegrableOn (fun τ => C * (1 / |ρ.im - τ| ^ (k + 2))) (Set.Ioc T (2 * T)) := by
    refine (ContinuousOn.integrableOn_Icc (a := T) (b := 2 * T) ?_).mono_set Set.Ioc_subset_Icc_self
    refine continuousOn_const.mul (ContinuousOn.div continuousOn_const
      ((continuous_const.sub continuous_id).abs.pow (k + 2)).continuousOn ?_)
    intro τ hτ; exact pow_ne_zero _ (abs_ne_zero.mpr (hne τ hτ))
  calc ‖∫ τ in Set.Ioc T (2 * T), Jfun κ Ξ ρ.re (ρ.im - τ) (2 * Real.pi * η)‖
      ≤ ∫ τ in Set.Ioc T (2 * T), C * (1 / |ρ.im - τ| ^ (k + 2)) :=
        norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall hbound))
    _ = C * ∫ τ in Set.Ioc T (2 * T), 1 / |ρ.im - τ| ^ (k + 2) := integral_const_mul _ _
    _ ≤ C * (1 / D ^ (k + 1)) := mul_le_mul_of_nonneg_left (tau_bound ρ.im T hT0 k hD) hC0
    _ = C / D ^ (k + 1) := by ring


end ZetaShell.PropZ
