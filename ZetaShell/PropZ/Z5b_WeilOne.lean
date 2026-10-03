/-
L7_5 (28 Sep 2026): Z5b in Weil form for r = 1 (ζ), derived from `Zeta23.WeilEF.EF_lit_zetaZeroConfig` (level A)
and Mathlib's `DirichletCharacter.LFunction_modOne_eq`. Pole terms: `h(−i/2) = Ṽ(1)`, `h(i/2) = Ṽ(0)`.
-/
import ZetaShell.PropZ.ZDefs
import ZetaShell.PropZ.Z5b_Weil
import Zeta23.WeilEF.Main

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem smooth_explicit_formula_weil_mod1 (χ : DirichletCharacter ℂ 1) (V : ℝ → ℂ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V) (hVpos : tsupport V ⊆ Set.Ioi 1) :
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℂ) * mellin V ρ.1) ∧
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * V n
      = (mellin V 1 + mellin V 0) - ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin V ρ.1
        + (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, mellin V (1 / 2 + t * I) * ((Zeta23.EF.gammaBracket t : ℝ) : ℂ) := by
  obtain ⟨hsum, heq⟩ := Zeta23.WeilEF.EF_lit_zetaZeroConfig (kOfV V) (kOfV_contDiff V hV)
    (kOfV_hasCompactSupport V hVc hVpos)
  have hIg : ∀ ρ : ℂ, I * Zeta23.gammaOf ρ + 1 / 2 = ρ := by
    intro ρ; rw [Zeta23.gammaOf, mul_div_cancel₀ _ Complex.I_ne_zero]; ring
  simp only [paperFT_kOfV V hVpos, hIg] at hsum heq
  -- the zero sets agree
  have hL : χ.LFunction = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hP : ∀ ρ : ℂ, IsNtZero χ ρ ↔ ρ ∈ Zeta23.zetaZeroConfig.carrier := by
    intro ρ
    show (χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ↔ (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
    rw [hL]
  let e : {ρ : ℂ // IsNtZero χ ρ} ≃ Zeta23.zetaZeroConfig.carrier := Equiv.subtypeEquivRight hP
  have hm : ∀ ρ : {ρ : ℂ // IsNtZero χ ρ},
      (zmult χ ρ.1 : ℂ) * mellin V ρ.1 = (Zeta23.zetaZeroConfig.mult (e ρ) : ℂ) * mellin V (e ρ) := by
    intro ρ
    show ((analyticOrderAt χ.LFunction ρ.1).toNat : ℂ) * mellin V ρ.1
      = ((analyticOrderAt riemannZeta ρ.1).toNat : ℂ) * mellin V ρ.1
    rw [hL]
  have hZ : ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin V ρ.1
      = ∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zetaZeroConfig.mult ρ : ℂ) * mellin V ρ := by
    simp_rw [hm]
    exact e.tsum_eq (fun ρ : Zeta23.zetaZeroConfig.carrier => (Zeta23.zetaZeroConfig.mult ρ : ℂ) * mellin V ρ)
  have hS : Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℂ) * mellin V ρ.1) := by
    simp_rw [hm]
    exact (e.summable_iff (f := fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : ℂ) * mellin V ρ)).mpr hsum
  refine ⟨hS, ?_⟩
  -- the prime side
  have hχn : ∀ n : ℕ, χ n = 1 := fun n => by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  have hprime : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (kOfV V (Real.log n) + kOfV V (-Real.log n))
      = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * V n := by
    intro n
    rw [hχn, mul_one]
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
      rw [hk1, hk2, add_zero]
      have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
      have hs' : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
      push_cast
      field_simp
  rw [Zeta23.EF.literatureRHS] at heq
  simp only [hprime, paperFT_kOfV V hVpos] at heq
  have h0 : I * (I / 2) + 1 / 2 = (0 : ℂ) := by
    rw [show I * (I / 2) = I * I / 2 by ring, Complex.I_mul_I]; ring
  have h1 : I * (-I / 2) + 1 / 2 = (1 : ℂ) := by
    rw [show I * (-I / 2) = -(I * I) / 2 by ring, Complex.I_mul_I]; ring
  have harch : ∀ t : ℝ, mellin V (I * (t : ℂ) + 1 / 2) = mellin V (1 / 2 + t * I) := by
    intro t; congr 1; ring
  simp only [h0, h1, harch] at heq
  rw [hZ]
  linear_combination heq

end ZetaShell.PropZ
