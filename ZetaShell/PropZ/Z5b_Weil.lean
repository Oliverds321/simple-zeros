/-
L7_5 (28 Sep 2026): Z5b in Weil form for r > 1, derived from `Zeta23.ThmE.EF_lit_chi_L` (level A).
Test function `k(u) = e^{u/2} V(e^u)`; then `paperFT k z = Ṽ(iz + 1/2)`, the prime leg is `Σ Λ(n)χ(n)V(n)`, and the
conjugate leg vanishes because `V = 0` on `(0, 1]`.
-/
import ZetaShell.PropZ.ZDefs
import Zeta23.ThmE.MainChi

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- `k(u) = e^{u/2} V(e^u)`. -/
noncomputable def kOfV (V : ℝ → ℂ) (u : ℝ) : ℂ := ((Real.exp (u / 2) : ℝ) : ℂ) * V (Real.exp u)

theorem kOfV_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) : ContDiff ℝ 2 (kOfV V) := by
  unfold kOfV
  have h1 : ContDiff ℝ 2 (fun u : ℝ => ((Real.exp (u / 2) : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.div_const 2))
  have hV2 : ContDiff ℝ 2 V := by exact_mod_cast contDiff_infty.1 hV 2
  exact h1.mul (hV2.comp Real.contDiff_exp)

theorem V_eq_zero_of_le_one (V : ℝ → ℂ) (hVpos : tsupport V ⊆ Set.Ioi 1) {y : ℝ} (hy : y ≤ 1) : V y = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => by have := hVpos h; simp only [Set.mem_Ioi] at this; linarith

theorem kOfV_hasCompactSupport (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVpos : tsupport V ⊆ Set.Ioi 1) :
    HasCompactSupport (kOfV V) := by
  refine HasCompactSupport.intro (K := Real.log '' tsupport V) ?_ ?_
  · refine hVc.isCompact.image_of_continuousOn (Real.continuousOn_log.mono fun x hx => ?_)
    have := hVpos hx; simp only [Set.mem_Ioi] at this
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
  · intro u hu
    unfold kOfV
    have : V (Real.exp u) = 0 := by
      by_contra h
      exact hu ⟨Real.exp u, subset_tsupport _ h, Real.log_exp u⟩
    rw [this, mul_zero]

theorem ofReal_exp_cpow (u : ℝ) (s : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ s = Complex.exp (s * u) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), mul_comm]

/-- `∫ V(e^u) e^{su} du = Ṽ(s)` (substitution `y = e^u`). -/
theorem integral_eq_mellin (V : ℝ → ℂ) (hVpos : tsupport V ⊆ Set.Ioi 1) (s : ℂ) :
    ∫ u : ℝ, V (Real.exp u) * Complex.exp (s * u) = mellin V s := by
  have h1 : ∫ u : ℝ, V (Real.exp u) * Complex.exp (s * u)
      = ∫ u in Set.Ioi 0, V (Real.exp u) * Complex.exp (s * u) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    simp only [Set.mem_Ioi, not_lt] at hu
    rw [V_eq_zero_of_le_one V hVpos (by simpa using Real.exp_le_one_iff.mpr hu), zero_mul]
  have h2 : ∫ u in Set.Ioi 0, V (Real.exp u) * Complex.exp (s * u)
      = ∫ u in Set.Ioi 0, Real.exp u • ((((Real.exp u : ℝ) : ℂ) ^ (s - 1)) • V (Real.exp u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [smul_eq_mul, Complex.real_smul, ofReal_exp_cpow]
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    rw [mul_comm]; congr 2; ring
  rw [h1, h2, integral_comp_exp_Ioi (fun y : ℝ => ((y : ℂ) ^ (s - 1)) • V y) 0, Real.exp_zero, mellin]
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ioi_subset_Ioi zero_le_one) fun y hy => ?_
  simp only [Set.mem_sdiff, Set.mem_Ioi, not_lt] at hy
  rw [V_eq_zero_of_le_one V hVpos hy.2, smul_zero]

theorem paperFT_kOfV (V : ℝ → ℂ) (hVpos : tsupport V ⊆ Set.Ioi 1) (z : ℂ) :
    Zeta23.paperFT (kOfV V) z = mellin V (I * z + 1 / 2) := by
  rw [Zeta23.paperFT, ← integral_eq_mellin V hVpos]
  congr 1; funext u
  simp only [kOfV]
  rw [show ((Real.exp (u / 2) : ℝ) : ℂ) = Complex.exp ((1 / 2 : ℂ) * u) by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring]
  rw [mul_comm (Complex.exp _) (V _), mul_assoc, ← Complex.exp_add]
  congr 2; ring

open scoped Classical in
/-- **Z5b-W for r > 1** (proved from `EF_lit_chi_L`). -/
theorem smooth_explicit_formula_weil_gt1 {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hr : 1 < r)
    (hχ : χ.IsPrimitive) (V : ℝ → ℂ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (hVpos : tsupport V ⊆ Set.Ioi 1) :
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℂ) * mellin V ρ.1) ∧
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * V n
      = - ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin V ρ.1
        + (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, mellin V (1 / 2 + t * I)
            * (((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
                + Real.log (r / Real.pi) : ℝ) : ℂ) := by
  obtain ⟨hsum, heq⟩ := Zeta23.ThmE.EF_lit_chi_L hr hχ (kOfV V) (kOfV_contDiff V hV)
    (kOfV_hasCompactSupport V hVc hVpos)
  have hIg : ∀ ρ : ℂ, I * Zeta23.gammaOf ρ + 1 / 2 = ρ := by
    intro ρ; rw [Zeta23.gammaOf, mul_div_cancel₀ _ Complex.I_ne_zero]; ring
  simp only [paperFT_kOfV V hVpos, hIg] at hsum heq
  refine ⟨hsum, ?_⟩
  -- the prime side
  have hprime : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (Zeta23.ThmE.coeff χ n * kOfV V (Real.log n)
        + (starRingEnd ℂ) (Zeta23.ThmE.coeff χ n) * kOfV V (-Real.log n))
      = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * V n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
      have hk1 : kOfV V (Real.log n) = ((Real.sqrt n : ℝ) : ℂ) * V n := by
        simp only [kOfV]
        rw [Real.exp_log hn, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]; congr 3; ring
      have hk2 : kOfV V (-Real.log n) = 0 := by
        simp only [kOfV]
        rw [V_eq_zero_of_le_one V hVpos, mul_zero]
        rw [Real.exp_neg, Real.exp_log hn]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
      rw [hk1, hk2, mul_zero, add_zero]
      have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
      have hs' : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
      simp only [Zeta23.ThmE.coeff]
      push_cast
      field_simp
  rw [Zeta23.ThmE.literatureRHSchi] at heq
  simp only [hprime, paperFT_kOfV V hVpos] at heq
  have harch : ∀ t : ℝ, mellin V (I * (t : ℂ) + 1 / 2) = mellin V (1 / 2 + t * I) := by
    intro t; congr 1; ring
  simp only [harch] at heq
  have hpar : Zeta23.ThmE.parity χ = (if χ.Even then 0 else 1 : ℕ) := rfl
  rw [hpar] at heq
  have hZ : ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin V ρ.1
      = ∑' ρ : ↥(Zeta23.ThmE.LZeros (Zeta23.ThmE.LSeam_of hr hχ)).carrier,
          ((Zeta23.ThmE.LZeros (Zeta23.ThmE.LSeam_of hr hχ)).mult ρ : ℂ) * mellin V ρ := rfl
  rw [hZ]
  linear_combination heq

end ZetaShell.PropZ
