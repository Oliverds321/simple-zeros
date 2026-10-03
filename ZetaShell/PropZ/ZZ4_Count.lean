/-
Sub-node Z5Z-4 (L7_5, rounds 2–3): convergence of the double zero sum of prop:shell-Z ("the sums converge absolutely by
Step 4 and #{|γ| ≤ t} ≪ t log(rt)").
Proof (round 3): `pairTerm ≤ (m_ρϖ_ρ)(m_ρ′ϖ_ρ′)` (as `N₀^{β+β′−2} ≤ 1`, `(1+|γ−γ′|)^A ≥ 1`); `ϖ_ρ ≤ C/(1+|γ_ρ|²)` for
`k ≥ 2`; and `Σ_ρ m_ρ/(1+|γ_ρ|²) < ∞` from the tree: `Zeta23.WeilEF.zero_sum_inv_sq_gen` with the unit-window counts
`Zeta23.ThmE.localCountChi_uniform_proof` (primitive χ mod r > 1) and `Zeta23.RvM.zetaZeroConfig_local_count` (ζ).
-/
import ZetaShell.Skeleton.Z5_PropZ
import Zeta23.WeilEF.ZeroSummability
import Zeta23.RvM.LocalCount
import Zeta23.ThmE.LocalCountChi
import Zeta23.ThmE.SeamL
import Zeta23.Statement.SeamClosed

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem varpi_nonneg0 (T μ : ℝ) (k : ℕ) (ρ : ℂ) (hμ : 0 ≤ μ) : 0 ≤ varpi T μ k ρ := by
  unfold varpi
  apply Real.rpow_nonneg
  have : 0 ≤ max (|ρ.im| - 2 * T) 0 := le_max_right _ _
  positivity

theorem pairTerm_nonneg0 {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T μ s₀ : ℝ) (A k : ℕ) (hμ : 0 ≤ μ)
    (p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) : 0 ≤ pairTerm χ T μ s₀ A k p := by
  unfold pairTerm
  have h1 := varpi_nonneg0 T μ k p.1.1 hμ
  have h2 := varpi_nonneg0 T μ k p.2.1 hμ
  have h3 : 0 ≤ Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2) := Real.rpow_nonneg (Real.exp_pos s₀).le _
  positivity

/-- `Σ_ρ m_ρ/(1+|γ_ρ|²) < ∞` for every primitive character (ζ included). -/
theorem zero_sum_inv_sq (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} =>
      (zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) := by
  rcases Nat.lt_or_ge 1 r with hr | hr
  · obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.ThmE.localCountChi_uniform_proof
    set Z := Zeta23.ThmE.LZeros (Zeta23.ThmE.LSeam_of hr hχ) with hZ
    have hr0 : (1 : ℝ) < r := by exact_mod_cast hr
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr0.le
    have hloc' : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ (A₀ * (1 + Real.log r)) * Real.log (|t| + 3) := by
      intro t
      have h1 := hloc r χ hr hχ t
      rw [hZ, Zeta23.ThmE.LZeros_N]
      have hl3 : 1 ≤ Real.log (|t| + 3) := by
        have he : Real.exp 1 ≤ |t| + 3 := by linarith [Real.exp_one_lt_d9, abs_nonneg t]
        have := Real.log_le_log (Real.exp_pos 1) he
        rwa [Real.log_exp] at this
      have hsplit : Real.log (r * (|t| + 3)) = Real.log r + Real.log (|t| + 3) :=
        Real.log_mul (by positivity) (by positivity)
      rw [hsplit] at h1
      have hx : Real.log r + Real.log (|t| + 3) ≤ (1 + Real.log r) * Real.log (|t| + 3) := by
        nlinarith [mul_le_mul_of_nonneg_left hl3 hlogr]
      calc _ ≤ A₀ * (Real.log r + Real.log (|t| + 3)) := h1
        _ ≤ A₀ * ((1 + Real.log r) * Real.log (|t| + 3)) := mul_le_mul_of_nonneg_left hx (by linarith)
        _ = A₀ * (1 + Real.log r) * Real.log (|t| + 3) := by ring
    have hA : 1 ≤ A₀ * (1 + Real.log r) := by nlinarith
    exact Zeta23.WeilEF.zero_sum_inv_sq_gen Z hA hloc'
  · have h1 : r = 1 := le_antisymm hr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
    subst h1
    obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
    have hS := Zeta23.WeilEF.zero_sum_inv_sq_gen Zeta23.zetaZeroConfig hA₀ hloc
    have hL : χ.LFunction = riemannZeta := DirichletCharacter.LFunction_modOne_eq
    have hP : ∀ ρ : ℂ, IsNtZero χ ρ ↔ ρ ∈ Zeta23.zetaZeroConfig.carrier := by
      intro ρ
      show (χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ↔ (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
      rw [hL]
    let e : {ρ : ℂ // IsNtZero χ ρ} ≃ Zeta23.zetaZeroConfig.carrier := Equiv.subtypeEquivRight hP
    have hm : ∀ ρ : {ρ : ℂ // IsNtZero χ ρ},
        (zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))
          = (Zeta23.zetaZeroConfig.mult (e ρ) : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf (e ρ))) := by
      intro ρ
      show ((analyticOrderAt χ.LFunction ρ.1).toNat : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))
        = ((analyticOrderAt riemannZeta ρ.1).toNat : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))
      rw [hL]
    simp_rw [hm]
    exact (e.summable_iff (f := fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ)))).mpr hS

/-- `ϖ_ρ(μ) ≤ (5/4)(1+2T)²(μ+1)²/(1+|γ_ρ|²)` for `k ≥ 2`, `ρ` in the strip. -/
theorem varpi_le_inv_sq (T μ : ℝ) (k : ℕ) (hk : 2 ≤ k) (hT : 0 ≤ T) (hμ : 0 ≤ μ) (ρ : ℂ)
    (hρ : 0 < ρ.re ∧ ρ.re < 1) :
    varpi T μ k ρ ≤ (5 / 4 * (1 + 2 * T) ^ 2 * (μ + 1) ^ 2) / (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by
  set D := max (|ρ.im| - 2 * T) 0 with hD
  set a := μ + 1 with ha
  have ha1 : 1 ≤ a := by linarith
  have hD0 : 0 ≤ D := le_max_right _ _
  set B := 1 + D / a with hB
  have hB1 : 1 ≤ B := by have : 0 ≤ D / a := by positivity
                         linarith
  have hvar : varpi T μ k ρ ≤ B ^ (-(2 : ℝ)) := by
    unfold varpi
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                                                   linarith)
  have hB2 : B ^ (-(2 : ℝ)) = 1 / B ^ 2 := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]
  have hns : Complex.normSq (Zeta23.gammaOf ρ) ≤ ρ.im ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    nlinarith [hρ.1, hρ.2]
  have hγ : |ρ.im| ≤ D + 2 * T := by have := le_max_left (|ρ.im| - 2 * T) 0; linarith
  have hsq : ρ.im ^ 2 ≤ (D + 2 * T) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hγ 2
  have haB : a * B = a + D := by rw [hB]; field_simp
  have hkey : 1 + Complex.normSq (Zeta23.gammaOf ρ) ≤ 5 / 4 * (1 + 2 * T) ^ 2 * a ^ 2 * B ^ 2 := by
    have hY : 1 + (D + 2 * T) ≤ (1 + 2 * T) * (a + D) := by nlinarith [mul_nonneg hT hD0]
    have hX0 : 0 ≤ D + 2 * T := by linarith
    have h1 : 1 + (D + 2 * T) ^ 2 ≤ ((1 + 2 * T) * (a + D)) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) hY 2
      nlinarith
    have h2 : ((1 + 2 * T) * (a + D)) ^ 2 = (1 + 2 * T) ^ 2 * a ^ 2 * B ^ 2 := by rw [← haB]; ring
    nlinarith
  have hpos : 0 < 1 + Complex.normSq (Zeta23.gammaOf ρ) := by
    have := Complex.normSq_nonneg (Zeta23.gammaOf ρ); linarith
  rw [hB2] at hvar
  refine hvar.trans ?_
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith

theorem Z5Z_summable (A k : ℕ) (hk : 2 ≤ k) :
    ∀ (s₀ T μ : ℝ), 0 ≤ s₀ → 2 ≤ T → 0 ≤ μ →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → Summable (pairTerm χ T μ s₀ A k) := by
  intro s₀ T μ hs₀ hT hμ r _ χ hχ
  set C₁ := 5 / 4 * (1 + 2 * T) ^ 2 * (μ + 1) ^ 2 with hC₁
  set g : {ρ : ℂ // IsNtZero χ ρ} → ℝ := fun ρ => (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 with hg
  have hg0 : 0 ≤ g := fun ρ => mul_nonneg (Nat.cast_nonneg _) (varpi_nonneg0 T μ k ρ.1 hμ)
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun ρ => ?_) ((zero_sum_inv_sq r χ hχ).mul_left C₁)
    have h := varpi_le_inv_sq T μ k hk (by linarith) hμ ρ.1 ⟨ρ.2.2.1, ρ.2.2.2⟩
    have hm : (0 : ℝ) ≤ zmult χ ρ.1 := Nat.cast_nonneg _
    calc g ρ = (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 := rfl
      _ ≤ (zmult χ ρ.1 : ℝ) * (C₁ / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) := mul_le_mul_of_nonneg_left h hm
      _ = C₁ * ((zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) := by ring
  have hprod := hgs.mul_of_nonneg hgs hg0 hg0
  refine Summable.of_nonneg_of_le (fun p => pairTerm_nonneg0 χ T μ s₀ A k hμ p) (fun p => ?_) hprod
  have h1 := p.1.2
  have h2 := p.2.2
  have hexp : Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_exp hs₀) (by linarith [h1.2.2, h2.2.2])
  have hden : 1 ≤ (1 + |p.1.1.im - p.2.1.im|) ^ A := one_le_pow₀ (by linarith [abs_nonneg (p.1.1.im - p.2.1.im)])
  have hv1 := varpi_nonneg0 T μ k p.1.1 hμ
  have hv2 := varpi_nonneg0 T μ k p.2.1 hμ
  have hm1 : (0 : ℝ) ≤ zmult χ p.1.1 := Nat.cast_nonneg _
  have hm2 : (0 : ℝ) ≤ zmult χ p.2.1 := Nat.cast_nonneg _
  have he0 : 0 ≤ Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2) := Real.rpow_nonneg (Real.exp_pos s₀).le _
  unfold pairTerm
  simp only [hg]
  calc (zmult χ p.1.1 : ℝ) * zmult χ p.2.1 * Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2)
        * varpi T μ k p.1.1 * varpi T μ k p.2.1 / (1 + |p.1.1.im - p.2.1.im|) ^ A
      ≤ (zmult χ p.1.1 : ℝ) * zmult χ p.2.1 * Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2)
        * varpi T μ k p.1.1 * varpi T μ k p.2.1 := div_le_self (by positivity) hden
    _ ≤ (zmult χ p.1.1 : ℝ) * zmult χ p.2.1 * 1 * varpi T μ k p.1.1 * varpi T μ k p.2.1 := by gcongr
    _ = (zmult χ p.1.1 : ℝ) * varpi T μ k p.1.1 * ((zmult χ p.2.1 : ℝ) * varpi T μ k p.2.1) := by ring

end ZetaShell.PropZ
