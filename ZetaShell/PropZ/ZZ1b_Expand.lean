/-
L7_5 (28 Sep 2026), round 9: `Z5Z_expand_S4'` (the statement of the leaf `Z5Z_expand_S4`), Step 3.
For `|s − s₀| ≤ 1`, `a_ρ(x) = m_ρ Ṽ_{x,s}(ρ)` has the `x`-uniform majorant `K u_ρ` (`u_ρ = m_ρ/(1+|γ_ρ|²)`, summable)
and vanishes for `x ∉ [−1/(8Δ), e^{s₀+2} + 1/(8Δ)]`; so
  `‖Σ_ρ a_ρ(x)‖² = Σ_{ρ,ρ′} a_ρ(x) conj a_{ρ′}(x)`, `∫_x Σ = Σ ∫_x` (norm-summable), and by the scaling identity
  `Δ² ∫ a_ρ conj a_{ρ′} dx = m_ρ m_{ρ′} e^{is(γ−γ′)} Ψ_{ρρ′}(s)`;
then `∫_s W(s−s₀) Σ_{pairs} = Σ_{pairs} ∫_s` (norm-summable).
The zero set is countable because `u_ρ > 0` (`zmult ≥ 1`, tree's `LSeam_of`, `ZetaSeam.one_le_mult_holds`).
-/
import ZetaShell.PropZ.ZZ1a_Scaling
import ZetaShell.PropZ.ZZ4_Count
import ZetaShell.PropZ.ZR_Mellin
import ZetaShell.PropZ.ZP_Bridge
import ZetaShell.PropZ.ZB_Meas
import ZetaShell.PropZ.ZZ3c_Q
import ZetaShell.PropZ.ZZ2a_OneZeroSplit

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem zmult_pos (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (ρ : {ρ : ℂ // IsNtZero χ ρ}) : 1 ≤ zmult χ ρ.1 := by
  rcases Nat.lt_or_ge 1 r with hr | hr
  · exact (Zeta23.ThmE.LSeam_of hr hχ).one_le_mult ρ.1 ρ.2
  · have h1 : r = 1 := le_antisymm hr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
    subst h1
    have hL : χ.LFunction = riemannZeta := DirichletCharacter.LFunction_modOne_eq
    have hz : Zeta23.IsNontrivialZero ρ.1 := by
      have h := ρ.2
      show riemannZeta ρ.1 = 0 ∧ 0 < ρ.1.re ∧ ρ.1.re < 1
      rw [← hL]; exact h
    have := Zeta23.ZetaSeam.one_le_mult_holds ρ.1 hz
    show 1 ≤ (analyticOrderAt χ.LFunction ρ.1).toNat
    rw [hL]; exact this

theorem zeros_countable (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    Countable {ρ : ℂ // IsNtZero χ ρ} := by
  have hS := zero_sum_inv_sq r χ hχ
  have hsupp := hS.countable_support
  have huniv : Function.support (fun ρ : {ρ : ℂ // IsNtZero χ ρ} =>
      (zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) = Set.univ := by
    ext ρ
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    have h1 : (1 : ℝ) ≤ zmult χ ρ.1 := by exact_mod_cast zmult_pos r χ hχ ρ
    have h2 : 0 < 1 + Complex.normSq (Zeta23.gammaOf ρ.1) := by
      have := Complex.normSq_nonneg (Zeta23.gammaOf ρ.1); linarith
    exact (div_pos (by linarith) h2).ne'
  rw [huniv] at hsupp
  exact Set.countable_univ_iff.mp hsupp

/-- `Δ² N^{ρ−1/2} conj(N^{ρ′−1/2}) N = e^{is(γ−γ′)} (ΔN)² N^{β+β′−2}`, `N = e^s`. -/
theorem cpow_combo (s Δ : ℝ) (ρ ρ' : ℂ) :
    ((Δ ^ 2 : ℝ) : ℂ) * ((((Real.exp s : ℝ) : ℂ) ^ (ρ - 1 / 2))
      * (starRingEnd ℂ) (((Real.exp s : ℝ) : ℂ) ^ (ρ' - 1 / 2)) * ((Real.exp s : ℝ) : ℂ))
      = Complex.exp (I * s * (ρ.im - ρ'.im))
        * ((((Δ * Real.exp s) ^ 2 * Real.exp (s * (ρ.re + ρ'.re - 2)) : ℝ)) : ℂ) := by
  have hN : ((Real.exp s : ℝ) : ℂ) = Complex.exp (s : ℂ) := Complex.ofReal_exp s
  have hlog : Complex.log (Complex.exp (s : ℂ)) = (s : ℂ) :=
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])
  have hreal : (Δ * Real.exp s) ^ 2 * Real.exp (s * (ρ.re + ρ'.re - 2)) = Δ ^ 2 * Real.exp (s * (ρ.re + ρ'.re)) := by
    rw [mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]; congr 2; push_cast; ring
  calc _ = ((Δ ^ 2 : ℝ) : ℂ) * Complex.exp ((s : ℂ) * (ρ - 1 / 2) + (starRingEnd ℂ) ((s : ℂ) * (ρ' - 1 / 2)) + (s : ℂ)) := by
        rw [hN, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
          hlog, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
    _ = ((Δ ^ 2 : ℝ) : ℂ) * Complex.exp (((s * (ρ.re + ρ'.re) : ℝ) : ℂ) + I * s * (ρ.im - ρ'.im)) := by
        congr 2
        apply Complex.ext <;> simp <;> ring
    _ = Complex.exp (I * s * (ρ.im - ρ'.im)) * (((Δ ^ 2 * Real.exp (s * (ρ.re + ρ'.re)) : ℝ)) : ℂ) := by
        rw [Complex.exp_add, ← Complex.ofReal_exp]; push_cast; ring
    _ = Complex.exp (I * s * (ρ.im - ρ'.im)) * ((((Δ * Real.exp s) ^ 2 * Real.exp (s * (ρ.re + ρ'.re - 2)) : ℝ)) : ℂ) := by
        rw [hreal]


/-- the `x`- and `s`-uniform majorant `K u_ρ` for `|s − s₀| ≤ 1`. -/
theorem expand_bound (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (s₀ T Δ : ℝ) (hs₀ : 3 ≤ s₀) (hT : 2 ≤ T) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, |s - s₀| ≤ 1 → ∀ (x : ℝ) (ρ : {ρ : ℂ // IsNtZero χ ρ}),
      ‖(zmult χ ρ.1 : ℂ) * mellin (VxsW T κ Ξ f Δ s x) ρ.1‖
        ≤ K * ((zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) := by
  obtain ⟨C, hC0, hC⟩ := mellin_Vxs_bounds κ hκ hκ1 Ξ hΞ f hf
  have hT0 : 0 ≤ T := by linarith
  obtain ⟨K₀, hK₀⟩ : ∃ K : ℝ, K = C * T * Real.exp ((s₀ + 1) / 2) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K : ℝ, K = C * (T + Real.exp (s₀ + 1) + 1) ^ 2 * T * Real.exp ((s₀ + 1) / 2) := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  refine ⟨5 / 2 * (K₀ + K₂), by positivity, fun s hs x ρ => ?_⟩
  have hs1 := (abs_le.mp hs).1
  have hs2 := (abs_le.mp hs).2
  have hN0 : 0 < Real.exp s := Real.exp_pos s
  have hm0 : 0 ≤ min (1 / Δ) (Real.exp s) := le_min (by positivity) hN0.le
  have hmN : min (1 / Δ) (Real.exp s) / Real.exp s ≤ 1 := (div_le_one hN0).mpr (min_le_right _ _)
  have hpow : ∀ y : ℝ, y ≤ 1 / 2 → Real.exp s ^ y ≤ Real.exp ((s₀ + 1) / 2) := fun y hy => by
    rw [Real.rpow_def_of_pos hN0, Real.log_exp]
    apply Real.exp_le_exp.mpr
    have hsp : 0 < s := by linarith
    rcases le_total y 0 with h | h
    · have : s * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsp.le h
      linarith
    · have : s * y ≤ s * (1 / 2) := mul_le_mul_of_nonneg_left hy hsp.le
      linarith
  have hX : (T + Δ * Real.exp s + 1) ^ 2 ≤ (T + Real.exp (s₀ + 1) + 1) ^ 2 := by
    have h1 : Δ * Real.exp s ≤ Real.exp (s₀ + 1) := by
      calc Δ * Real.exp s ≤ 1 * Real.exp s := mul_le_mul_of_nonneg_right hΔ1 hN0.le
        _ ≤ Real.exp (s₀ + 1) := by rw [one_mul]; exact Real.exp_le_exp.mpr (by linarith)
    have h0 : 0 ≤ T + Δ * Real.exp s + 1 := by positivity
    exact pow_le_pow_left₀ h0 (by linarith) 2
  have hb0 : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖mellin (VxsW T κ Ξ f Δ s x) w‖ ≤ K₀ := by
    intro w h0 h1
    refine (hC s₀ T Δ s hs₀ hT hΔ hΔ1 hs x w h0 h1).1.trans ?_
    rw [hK₀]
    have hp := hpow (w.re - 1 / 2) (by linarith)
    have hp0 : 0 ≤ Real.exp s ^ (w.re - 1 / 2) := by positivity
    calc C * T * Real.exp s ^ (w.re - 1 / 2) * min (1 / Δ) (Real.exp s) / Real.exp s
        = C * T * Real.exp s ^ (w.re - 1 / 2) * (min (1 / Δ) (Real.exp s) / Real.exp s) := by ring
      _ ≤ C * T * Real.exp ((s₀ + 1) / 2) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hmN (by positivity) (by positivity)
      _ = C * T * Real.exp ((s₀ + 1) / 2) := by ring
  have hb2 : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → w ≠ 0 → ‖mellin (VxsW T κ Ξ f Δ s x) w‖ ≤ K₂ / ‖w‖ ^ 2 := by
    intro w h0 h1 hw
    refine ((hC s₀ T Δ s hs₀ hT hΔ hΔ1 hs x w h0 h1).2 hw).trans ?_
    rw [div_eq_mul_one_div K₂, mul_comm K₂, hK₂]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hp := hpow (w.re - 1 / 2) (by linarith)
    have hp0 : 0 ≤ Real.exp s ^ (w.re - 1 / 2) := by positivity
    calc C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp s ^ (w.re - 1 / 2) * min (1 / Δ) (Real.exp s) / Real.exp s
        = C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp s ^ (w.re - 1 / 2)
          * (min (1 / Δ) (Real.exp s) / Real.exp s) := by ring
      _ ≤ C * (T + Real.exp (s₀ + 1) + 1) ^ 2 * T * Real.exp ((s₀ + 1) / 2) * 1 := by
          apply mul_le_mul _ hmN (by positivity) (by positivity)
          apply mul_le_mul _ hp hp0 (by positivity)
          apply mul_le_mul_of_nonneg_right _ hT0
          exact mul_le_mul_of_nonneg_left hX hC0
      _ = C * (T + Real.exp (s₀ + 1) + 1) ^ 2 * T * Real.exp ((s₀ + 1) / 2) := by ring
  -- the zero bound (as in `ZB_Meas`)
  have hρ := ρ.2
  have hre0 : 0 ≤ ρ.1.re := hρ.2.1.le
  have hre1 : ρ.1.re ≤ 1 := hρ.2.2.le
  have hρ0 : ρ.1 ≠ 0 := fun h => by
    have := hρ.2.1; rw [h] at this; simp at this
  have hns : Complex.normSq (Zeta23.gammaOf ρ.1) ≤ ρ.1.im ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    nlinarith [hρ.2.1, hρ.2.2]
  have hnρ : ρ.1.im ^ 2 ≤ ‖ρ.1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [sq_nonneg ρ.1.re]
  have hpos : 0 < 1 + Complex.normSq (Zeta23.gammaOf ρ.1) := by
    have := Complex.normSq_nonneg (Zeta23.gammaOf ρ.1); linarith
  have hV : ‖mellin (VxsW T κ Ξ f Δ s x) ρ.1‖
      ≤ 5 / 2 * (K₀ + K₂) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1)) := by
    rw [le_div_iff₀ hpos]
    rcases le_or_gt 1 (ρ.1.im ^ 2) with hg | hg
    · have h2 := hb2 ρ.1 hre0 hre1 hρ0
      have hn2 : 0 < ‖ρ.1‖ ^ 2 := by positivity
      have : ‖mellin (VxsW T κ Ξ f Δ s x) ρ.1‖ * ‖ρ.1‖ ^ 2 ≤ K₂ := by
        rw [le_div_iff₀ hn2] at h2; exact h2
      have hmn := norm_nonneg (mellin (VxsW T κ Ξ f Δ s x) ρ.1)
      nlinarith
    · have h0 := hb0 ρ.1 hre0 hre1
      have hmn := norm_nonneg (mellin (VxsW T κ Ξ f Δ s x) ρ.1)
      nlinarith
  rw [norm_mul, Complex.norm_natCast]
  calc (zmult χ ρ.1 : ℝ) * ‖mellin (VxsW T κ Ξ f Δ s x) ρ.1‖
      ≤ (zmult χ ρ.1 : ℝ) * (5 / 2 * (K₀ + K₂) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) :=
        mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)
    _ = _ := by ring


/-- the pair summand of Step 3 at a fixed `s` (without the weight). -/
noncomputable def Gp {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T κ : ℝ) (Ξ f : ℝ → ℝ) (Δ s : ℝ)
    (p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) : ℂ :=
  ((zmult χ p.1.1 * zmult χ p.2.1 : ℕ) : ℂ) * (Complex.exp (I * s * (p.1.1.im - p.2.1.im)) * PsiP T κ Ξ f p.1.1 p.2.1 Δ s)

theorem expand_s (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (s₀ T Δ : ℝ) (hs₀ : 3 ≤ s₀) (hT : 2 ≤ T) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ s : ℝ, |s - s₀| ≤ 1 → ∀ (x : ℝ) (ρ : {ρ : ℂ // IsNtZero χ ρ}),
      ‖(zmult χ ρ.1 : ℂ) * mellin (VxsW T κ Ξ f Δ s x) ρ.1‖
        ≤ K * ((zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))))
    (s : ℝ) (hs : |s - s₀| ≤ 1) :
    (∀ p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ},
      ‖Gp χ T κ Ξ f Δ s p‖ ≤ Δ ^ 2 * (K ^ 2 * (Real.exp (s₀ + 2) + 1 / (4 * Δ)))
        * (((zmult χ p.1.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf p.1.1)))
          * ((zmult χ p.2.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf p.2.1))))) ∧
    (((Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2) : ℝ) : ℂ) = ∑' p, Gp χ T κ Ξ f Δ s p) := by
  haveI := zeros_countable r χ hχ
  set u : {ρ : ℂ // IsNtZero χ ρ} → ℝ := fun ρ => (zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))
    with hu
  have hSs : Summable u := zero_sum_inv_sq r χ hχ
  have hu0 : ∀ ρ, 0 ≤ u ρ := fun ρ => by
    simp only [hu]
    exact div_nonneg (Nat.cast_nonneg _) (by have := Complex.normSq_nonneg (Zeta23.gammaOf ρ.1); linarith)
  set a : {ρ : ℂ // IsNtZero χ ρ} → ℝ → ℂ := fun ρ x => (zmult χ ρ.1 : ℂ) * mellin (VxsW T κ Ξ f Δ s x) ρ.1
    with ha
  have haK : ∀ ρ x, ‖a ρ x‖ ≤ K * u ρ := fun ρ x => hK s hs x ρ
  set Kx := Set.Icc (-(1 / (8 * Δ))) (Real.exp (s₀ + 2) + 1 / (8 * Δ)) with hKx
  have hs1 := (abs_le.mp hs).1
  have hs2 := (abs_le.mp hs).2
  have hsupp : ∀ ρ x, x ∉ Kx → a ρ x = 0 := by
    intro ρ x hx
    have hx' : x ∉ Set.Icc (Real.exp (s - κ) - 1 / (8 * Δ)) (Real.exp (s + κ) + 1 / (8 * Δ)) := by
      intro h; apply hx
      have e1 := (Real.exp_pos (s - κ)).le
      have e2 : Real.exp (s + κ) ≤ Real.exp (s₀ + 2) := Real.exp_le_exp.mpr (by linarith)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    simp only [ha, VxsW_eq_zero_of_far T κ hκ Ξ hΞ f hf Δ hΔ s x hx', mellin, smul_zero,
      MeasureTheory.integral_zero, mul_zero]
  have hacont : ∀ ρ, Continuous (a ρ) := fun ρ =>
    continuous_const.mul (mellin_Vxs_cont_x κ hκ hκ1 Ξ hΞ f hf T Δ s₀ s hs₀ hs ρ.1)
  set F : ({ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) → ℝ → ℂ :=
    fun p x => a p.1 x * (starRingEnd ℂ) (a p.2 x) with hF
  set Lx := Real.exp (s₀ + 2) + 1 / (4 * Δ) with hLx
  have hvol : volume.real Kx = Lx := by
    have h8 : 0 ≤ 1 / (8 * Δ) := by positivity
    have he := Real.exp_pos (s₀ + 2)
    rw [hKx, Real.volume_real_Icc_of_le (by linarith), hLx]; field_simp; ring
  have hFb : ∀ p x, ‖F p x‖ ≤ Kx.indicator (fun _ => K ^ 2 * (u p.1 * u p.2)) x := by
    intro p x
    by_cases hx : x ∈ Kx
    · rw [Set.indicator_of_mem hx]
      simp only [hF]
      rw [norm_mul, Complex.norm_conj]
      calc ‖a p.1 x‖ * ‖a p.2 x‖ ≤ (K * u p.1) * (K * u p.2) :=
            mul_le_mul (haK _ _) (haK _ _) (norm_nonneg _) (mul_nonneg hK0 (hu0 _))
        _ = K ^ 2 * (u p.1 * u p.2) := by ring
    · rw [Set.indicator_of_notMem hx]
      simp only [hF, hsupp p.1 x hx, zero_mul, norm_zero, le_refl]
  have hFint : ∀ p, Integrable (F p) := fun p => by
    have hIi : Integrable (Kx.indicator (fun _ => K ^ 2 * (u p.1 * u p.2))) :=
      (integrableOn_const (s := Kx) (C := K ^ 2 * (u p.1 * u p.2)) (hs := measure_Icc_lt_top.ne)).integrable_indicator
        measurableSet_Icc
    refine Integrable.mono' hIi ((hacont p.1).mul (Complex.continuous_conj.comp (hacont p.2))).aestronglyMeasurable
      (Filter.Eventually.of_forall (hFb p))
  have hFnorm : ∀ p, (∫ x, ‖F p x‖) ≤ K ^ 2 * Lx * (u p.1 * u p.2) := by
    intro p
    have hIi : Integrable (Kx.indicator (fun _ => K ^ 2 * (u p.1 * u p.2))) :=
      (integrableOn_const (s := Kx) (C := K ^ 2 * (u p.1 * u p.2)) (hs := measure_Icc_lt_top.ne)).integrable_indicator
        measurableSet_Icc
    calc (∫ x, ‖F p x‖) ≤ ∫ x, Kx.indicator (fun _ => K ^ 2 * (u p.1 * u p.2)) x :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by
            simp only [Pi.zero_apply]; exact norm_nonneg _) hIi (Filter.Eventually.of_forall (hFb p))
      _ = K ^ 2 * Lx * (u p.1 * u p.2) := by
          rw [integral_indicator_const _ measurableSet_Icc, hvol, smul_eq_mul]; ring
  have hsumU : Summable (fun p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ} => u p.1 * u p.2) :=
    hSs.mul_of_nonneg hSs hu0 hu0
  have hFsum : Summable (fun p => ∫ x, ‖F p x‖) :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun x => norm_nonneg _) hFnorm (hsumU.mul_left _)
  -- (E): the value of each pair integral
  have hE : ∀ p, ((Δ ^ 2 : ℝ) : ℂ) * (∫ x, F p x) = Gp χ T κ Ξ f Δ s p := by
    intro p
    set N := Real.exp s with hN
    have hN0 : 0 < N := Real.exp_pos s
    set g : ℝ → ℂ := fun ξ => Irho T κ Ξ f 0 p.1.1 (Δ * N) ξ * (starRingEnd ℂ) (Irho T κ Ξ f 0 p.2.1 (Δ * N) ξ)
      with hg
    have hFx : ∀ x, F p x = ((zmult χ p.1.1 : ℂ) * (zmult χ p.2.1 : ℂ))
        * ((((N : ℝ) : ℂ) ^ (p.1.1 - 1 / 2)) * (starRingEnd ℂ) (((N : ℝ) : ℂ) ^ (p.2.1 - 1 / 2))) * g (x / N) := by
      intro x
      simp only [hF, ha, hg, mellin_VxsW_scaling, map_mul, Complex.conj_natCast]
      ring
    have hint : (∫ x, F p x) = ((zmult χ p.1.1 : ℂ) * (zmult χ p.2.1 : ℂ))
        * ((((N : ℝ) : ℂ) ^ (p.1.1 - 1 / 2)) * (starRingEnd ℂ) (((N : ℝ) : ℂ) ^ (p.2.1 - 1 / 2)))
        * (((N : ℝ) : ℂ) * Qab T κ Ξ f p.1.1 p.2.1 Δ 0 0 s) := by
      simp only [hFx]
      rw [integral_const_mul, MeasureTheory.Measure.integral_comp_div g N, abs_of_pos hN0, Complex.real_smul]
      rfl
    rw [hint]
    have hc := cpow_combo s Δ p.1.1 p.2.1
    simp only [Gp, PsiP]
    rw [← hN] at hc
    calc ((Δ ^ 2 : ℝ) : ℂ) * (((zmult χ p.1.1 : ℂ) * (zmult χ p.2.1 : ℂ))
          * ((((N : ℝ) : ℂ) ^ (p.1.1 - 1 / 2)) * (starRingEnd ℂ) (((N : ℝ) : ℂ) ^ (p.2.1 - 1 / 2)))
          * (((N : ℝ) : ℂ) * Qab T κ Ξ f p.1.1 p.2.1 Δ 0 0 s))
        = ((zmult χ p.1.1 : ℂ) * (zmult χ p.2.1 : ℂ))
          * (((Δ ^ 2 : ℝ) : ℂ) * ((((N : ℝ) : ℂ) ^ (p.1.1 - 1 / 2))
            * (starRingEnd ℂ) (((N : ℝ) : ℂ) ^ (p.2.1 - 1 / 2)) * ((N : ℝ) : ℂ)))
          * Qab T κ Ξ f p.1.1 p.2.1 Δ 0 0 s := by ring
      _ = _ := by
          rw [hc]; unfold Qab; simp only [hN]; push_cast; ring
  -- assemble the two claims
  refine ⟨fun p => ?_, ?_⟩
  · rw [← hE p, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg Δ)]
    calc Δ ^ 2 * ‖∫ x, F p x‖ ≤ Δ ^ 2 * (∫ x, ‖F p x‖) :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (sq_nonneg Δ)
      _ ≤ Δ ^ 2 * (K ^ 2 * Lx * (u p.1 * u p.2)) := mul_le_mul_of_nonneg_left (hFnorm p) (sq_nonneg Δ)
      _ = _ := by rw [hLx]; ring
  · have hpt : ∀ x, (((‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2 : ℝ)) : ℂ) = ∑' p, F p x := by
      intro x
      have hs1 : Summable (fun ρ => ‖a ρ x‖) :=
        Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) (fun ρ => haK ρ x) (hSs.mul_left K)
      have hs2 : Summable (fun ρ => ‖(starRingEnd ℂ) (a ρ x)‖) := by
        simpa only [Complex.norm_conj] using hs1
      have hz : zeroPartW χ T κ Ξ f Δ s x = ∑' ρ, a ρ x := rfl
      have hconj : (starRingEnd ℂ) (∑' ρ, a ρ x) = ∑' ρ, (starRingEnd ℂ) (a ρ x) :=
        Complex.conj_tsum (fun ρ => a ρ x)
      rw [hz, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hconj, tsum_mul_tsum_of_summable_norm hs1 hs2]
    have hI : (((∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2 : ℝ)) : ℂ) = ∑' p, ∫ x, F p x := by
      rw [← integral_complex_ofReal]
      simp only [hpt]
      exact (integral_tsum_of_summable_integral_norm hFint hFsum).symm
    push_cast
    rw [hI, ← tsum_mul_left]
    congr 1; funext p
    rw [← hE p]; push_cast; ring


set_option maxHeartbeats 4000000 in
theorem Z5Z_expand_S4' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hk : 2 ≤ k) (hone : ∃ C : ℝ, OneZeroBound κ Ξ f A k C) :
    ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      Integrable (fun s => W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))) ∧
      Summable (pairInt χ T κ Ξ f W Δ s₀) ∧
      (((∫ s, W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))) : ℝ) : ℂ)
        = ∑' p, pairInt χ T κ Ξ f W Δ s₀ p := by
  intro W hW s₀ T Δ hs₀ hT hΔ hΔ1 r _ χ hχ hr
  haveI := zeros_countable r χ hχ
  obtain ⟨K, hK0, hK⟩ := expand_bound κ hκ hκ1 Ξ hΞ f hf s₀ T Δ hs₀ hT hΔ hΔ1 r χ
  set u : {ρ : ℂ // IsNtZero χ ρ} → ℝ := fun ρ => (zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))
    with hu
  have hSs : Summable u := zero_sum_inv_sq r χ hχ
  have hu0 : ∀ ρ, 0 ≤ u ρ := fun ρ => by
    simp only [hu]
    exact div_nonneg (Nat.cast_nonneg _) (by have := Complex.normSq_nonneg (Zeta23.gammaOf ρ.1); linarith)
  have hsumU : Summable (fun p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ} => u p.1 * u p.2) :=
    hSs.mul_of_nonneg hSs hu0 hu0
  -- the weight
  have hWc : HasCompactSupport W :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport W) (hW.supp.trans Set.Ioo_subset_Icc_self)
  obtain ⟨Wb0, hWb0⟩ := hW.smooth.continuous.bounded_above_of_compact_support hWc
  set Wb := max Wb0 0 with hWbdef
  have hWb : ∀ z, |W z| ≤ Wb := fun z => by
    have := hWb0 z; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hWb0' : 0 ≤ Wb := le_max_right _ _
  have hWz : ∀ s : ℝ, ¬ |s - s₀| ≤ 1 → W (s - s₀) = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => hs (by
      have h' := hW.supp h; rw [abs_le]; exact ⟨h'.1.le, h'.2.le⟩)
  set Bc := Δ ^ 2 * (K ^ 2 * (Real.exp (s₀ + 2) + 1 / (4 * Δ))) with hBc
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  set H : ({ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) → ℝ → ℂ :=
    fun p s => ((W (s - s₀) : ℝ) : ℂ) * Gp χ T κ Ξ f Δ s p with hH
  have hHb : ∀ p s, ‖H p s‖ ≤ (Set.Icc (s₀ - 1) (s₀ + 1)).indicator (fun _ => Wb * Bc * (u p.1 * u p.2)) s := by
    intro p s
    by_cases hs : |s - s₀| ≤ 1
    · have hm : s ∈ Set.Icc (s₀ - 1) (s₀ + 1) := by
        have := abs_le.mp hs; exact ⟨by linarith [this.1], by linarith [this.2]⟩
      rw [Set.indicator_of_mem hm]
      simp only [hH]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hG := (expand_s κ hκ hκ1 Ξ hΞ f hf s₀ T Δ hs₀ hT hΔ hΔ1 r χ hχ K hK0 hK s hs).1 p
      calc |W (s - s₀)| * ‖Gp χ T κ Ξ f Δ s p‖ ≤ Wb * (Bc * (u p.1 * u p.2)) :=
            mul_le_mul (hWb _) hG (norm_nonneg _) hWb0'
        _ = Wb * Bc * (u p.1 * u p.2) := by ring
    · have hm : s ∉ Set.Icc (s₀ - 1) (s₀ + 1) := fun h => hs (by
        rw [abs_le]; exact ⟨by linarith [h.1], by linarith [h.2]⟩)
      rw [Set.indicator_of_notMem hm]
      simp only [hH, hWz s hs, Complex.ofReal_zero, zero_mul, norm_zero, le_refl]
  have hHb' : ∀ p s, ‖H p s‖ ≤ Wb * Bc * (u p.1 * u p.2) := fun p s => by
    refine (hHb p s).trans ?_
    by_cases hm : s ∈ Set.Icc (s₀ - 1) (s₀ + 1)
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]; exact mul_nonneg (mul_nonneg hWb0' hBc0) (mul_nonneg (hu0 _) (hu0 _))
  -- continuity of each `H p`
  have hHc : ∀ p, Continuous (H p) := by
    intro p
    have hρ1 := p.1.2
    have hρ2 := p.2.2
    have hQ : Continuous (fun s => Qab T κ Ξ f p.1.1 p.2.1 Δ 0 0 s) :=
      continuous_iff_continuousAt.mpr fun s =>
        (Qab_hasDerivAt κ hκ Ξ hΞ f hf T p.1.1 p.2.1 hρ1.2.1 hρ1.2.2 hρ2.2.1 hρ2.2.2 Δ hΔ 0 0 s).continuousAt
    have hPsi : (fun s => PsiP T κ Ξ f p.1.1 p.2.1 Δ s)
        = fun s => ((((Δ * Real.exp s) ^ 2 * Real.exp (s * (p.1.1.re + p.2.1.re - 2)) : ℝ)) : ℂ)
          * Qab T κ Ξ f p.1.1 p.2.1 Δ 0 0 s := rfl
    have hPc : Continuous (fun s => PsiP T κ Ξ f p.1.1 p.2.1 Δ s) := by
      rw [hPsi]; exact (Complex.continuous_ofReal.comp (by fun_prop)).mul hQ
    have hEc : Continuous (fun s : ℝ => Complex.exp (I * s * (p.1.1.im - p.2.1.im))) := by fun_prop
    simp only [hH, Gp]
    exact (Complex.continuous_ofReal.comp (hW.smooth.continuous.comp (by fun_prop))).mul
      (continuous_const.mul (hEc.mul hPc))
  have hIi : ∀ c : ℝ, Integrable ((Set.Icc (s₀ - 1) (s₀ + 1)).indicator (fun _ => c)) := fun c =>
    (integrableOn_const (s := Set.Icc (s₀ - 1) (s₀ + 1)) (C := c) (hs := measure_Icc_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  have hHint : ∀ p, Integrable (H p) := fun p =>
    Integrable.mono' (hIi _) (hHc p).aestronglyMeasurable (Filter.Eventually.of_forall (hHb p))
  have hHnorm : ∀ p, (∫ s, ‖H p s‖) ≤ 2 * (Wb * Bc * (u p.1 * u p.2)) := by
    intro p
    calc (∫ s, ‖H p s‖) ≤ ∫ s, (Set.Icc (s₀ - 1) (s₀ + 1)).indicator (fun _ => Wb * Bc * (u p.1 * u p.2)) s :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => by
            simp only [Pi.zero_apply]; exact norm_nonneg _) (hIi _) (Filter.Eventually.of_forall (hHb p))
      _ = 2 * (Wb * Bc * (u p.1 * u p.2)) := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
          ring
  have hHsum : Summable (fun p => ∫ s, ‖H p s‖) :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun s => norm_nonneg _) hHnorm
      ((hsumU.mul_left (2 * (Wb * Bc))).congr fun p => by ring)
  -- the pointwise identity in `s`
  have hpt : ∀ s, (((W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)) : ℝ)) : ℂ) = ∑' p, H p s := by
    intro s
    by_cases hs : |s - s₀| ≤ 1
    · have hE := (expand_s κ hκ hκ1 Ξ hΞ f hf s₀ T Δ hs₀ hT hΔ hΔ1 r χ hχ K hK0 hK s hs).2
      rw [Complex.ofReal_mul, hE, ← tsum_mul_left]
    · simp only [hH, hWz s hs, Complex.ofReal_zero, zero_mul, tsum_zero]
  -- pair integrals
  have hpair : ∀ p, pairInt χ T κ Ξ f W Δ s₀ p = ∫ s, H p s := by
    intro p
    simp only [pairInt, hH, Gp]
    rw [← integral_const_mul]
    congr 1; funext s; ring
  -- continuity and support of the real function
  have hScont : Continuous (fun s => ∑' p, H p s) := continuous_tsum hHc (hsumU.mul_left (Wb * Bc)) hHb'
  have hReq : (fun s => W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
      = fun s => (∑' p, H p s).re := by
    funext s; rw [← hpt s, Complex.ofReal_re]
  refine ⟨?_, ?_, ?_⟩
  · rw [hReq]
    refine (Complex.continuous_re.comp hScont).integrable_of_hasCompactSupport ?_
    refine IsCompact.of_isClosed_subset (isCompact_Icc (a := s₀ - 1) (b := s₀ + 1)) (isClosed_tsupport _) ?_
    apply closure_minimal _ isClosed_Icc
    intro s hs
    by_contra hc
    apply hs
    have hs' : ¬ |s - s₀| ≤ 1 := fun h => hc (by
      have := abs_le.mp h; exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    show (∑' p, H p s).re = 0
    simp only [hH, hWz s hs', Complex.ofReal_zero, zero_mul, tsum_zero, Complex.zero_re]
  · refine Summable.of_norm_bounded hHsum (fun p => ?_)
    rw [hpair p]; exact norm_integral_le_integral_norm _
  · rw [← integral_complex_ofReal]
    simp only [hpt]
    rw [← integral_tsum_of_summable_integral_norm hHint hHsum]
    congr 1; funext p; exact (hpair p).symm

end ZetaShell.PropZ
