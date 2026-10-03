/-
F1c-3b split (L7_3, round 6). `shell_mertens` (the step after the smearing) is derived here from
* F1c-3b′ `mertens_hsup` (OPEN): the Abel/Mertens step with the kernel identity, for the bounded-variation weight
  `hsupP` (unit-ball supremum of `g·wOut`):  `Σ_{n≤X} (Λ(n)²/n)·hsupP(log n) ≤ (ℒ(aL)²/2)·(KoutShell(a) + η)`.
  (Model: `Σ Λ²/n·f(log n) ≈ ∫ f(y) y dy` (Mertens), `g(αℒ) = (aL)²ℒ⁻¹ψ_{v_d}(α)` (`gQ_eq_psi_vDesign`), and
  `α·ℒ·shellWt(αℒ)/ℒ` is the Shell kernel `C|α|`, `1`, `C`; the unit-ball smoothing costs `O(1/ℒ)`.)
* the tail `(2H_P/π²)Σ_{n≤X}Λ(n)²/n` (`sumA2Q_le`, `H_P = aL(C + ℒ)`): `o(1)` against `Tℒ(aL)²` since `T ≥ Kℒ²` (A7);
* `|𝔉|(T/2π)ℒ ≤ (1+δ)𝒩` (`sizeR_LL_le_NfamQ_shell`) and `0 ≤ KoutShell ≤ 4C + 2` (`KoutShell_bounds`).
-/
import ZetaShell.ShellK.LF_OutDiag
import ZetaShell.ShellK.LF_Majorant

noncomputable section
open scoped BigOperators
open scoped ArithmeticFunction
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

/-- `0 ≤ KoutShell C α′ a v ≤ 4C + 2` for admissible `v` with `λ ≤ 2`, `C ≥ 0`. -/
theorem KoutShell_bounds {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (h2 : lam ≤ 2) {C αp a : ℝ}
    (hC : 0 ≤ C) (hαp : 1 ≤ αp) : 0 ≤ KoutShell C αp a v ∧ KoutShell C αp a v ≤ 4 * C + 2 := by
  have hpsi0 : ∀ α, 0 ≤ psi v α := psi_nonneg hv
  have hint : Integrable (fun α => |α| * psi v α) := absPsi_integrable hv
  have hpint : Integrable (psi v) := psi_integrable hv
  have htot : (∫ α, |α| * psi v α) ≤ 2 := by
    have := K0_add_K1_le_two hv h2
    rw [K0_add_K1 hv] at this
    exact this
  have hnn : ∀ α, 0 ≤ |α| * psi v α := fun α => mul_nonneg (abs_nonneg α) (hpsi0 α)
  -- each piece
  have hJ0 : 0 ≤ Jzone a v := Jzone_nonneg hv a
  have hJ : Jzone a v ≤ 2 := by
    unfold Jzone
    exact le_trans (setIntegral_le_integral hint (ae_of_all _ hnn)) htot
  have hm1 : MeasurableSet {α : ℝ | 1 < |α| ∧ |α| ≤ αp} :=
    (measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hm2 : MeasurableSet {α : ℝ | αp < |α|} := measurableSet_lt measurable_const continuous_abs.measurable
  have hmid0 : 0 ≤ ∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ αp}, psi v α := setIntegral_nonneg hm1 (fun α _ => hpsi0 α)
  have hmid : (∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ αp}, psi v α) ≤ 2 := by
    have h1 : (∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ αp}, psi v α)
        ≤ ∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ αp}, |α| * psi v α := by
      apply setIntegral_mono_on hpint.integrableOn hint.integrableOn hm1
      intro α hα
      have : 1 ≤ |α| := hα.1.le
      nlinarith [hpsi0 α]
    exact le_trans h1 (le_trans (setIntegral_le_integral hint (ae_of_all _ hnn)) htot)
  have htop0 : 0 ≤ ∫ α in {α : ℝ | αp < |α|}, psi v α := setIntegral_nonneg hm2 (fun α _ => hpsi0 α)
  have htop : (∫ α in {α : ℝ | αp < |α|}, psi v α) ≤ 2 := by
    have h1 : (∫ α in {α : ℝ | αp < |α|}, psi v α) ≤ ∫ α in {α : ℝ | αp < |α|}, |α| * psi v α := by
      apply setIntegral_mono_on hpint.integrableOn hint.integrableOn hm2
      intro α hα
      have : 1 ≤ |α| := le_trans hαp (le_of_lt hα)
      nlinarith [hpsi0 α]
    exact le_trans h1 (le_trans (setIntegral_le_integral hint (ae_of_all _ hnn)) htot)
  unfold KoutShell
  constructor
  · have := mul_nonneg hC hJ0
    have := mul_nonneg hC htop0
    linarith
  · have e1 := mul_le_mul_of_nonneg_left hJ hC
    have e2 := mul_le_mul_of_nonneg_left htop hC
    linarith

/-- **F1c-3c (OPEN).** A smooth majorant of the smoothed weight: a `C¹` function `F ≥ hsupP` on `[0, L]`, vanishing
beyond `L + 2`, with `|F′| ≤ 2M`, whose window integral plus the Abel error `M·Cab·(L+2)²` stays within
`(ℒ(aL)²/2)(KoutShell + η)`. (Ramps of width `ℒ^{1/2}` at the jumps of `wOut`: `M ≍ (aL)²ℒ^{−3/2}`, so the Abel error is
`O((aL)²ℒ^{1/2})`, and the ramps cost `O(ℒ^{−1/2})` relative; the kernel identity `g(αℒ) = (aL)²ℒ⁻¹ψ_{v_d}(α)` turns
`∫ g·wOut·y dy` into `(ℒ(aL)²/2)·∫_{|α|>a}(Shell kernel)ψ ≤ (ℒ(aL)²/2)·KoutShell(a)`.) Pure real analysis: no primes. -/
theorem smooth_majorant (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (Cab : ℝ) (hCab : 0 ≤ Cab) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∃ F : ℝ → ℝ, ∃ M : ℝ, 0 < M ∧ Differentiable ℝ F ∧ Continuous (deriv F) ∧
        (∀ y, |deriv F y| ≤ 2 * M) ∧ (∀ y, P.LB + 2 ≤ y → F y = 0) ∧ (∀ y, 0 ≤ F y) ∧
        (∀ y, 0 ≤ y → y ≤ P.LB → hsupP P y ≤ F y) ∧
        (∫ y in (0 : ℝ)..(P.LB + 2), F y * y) + M * (Cab * (P.LB + 2) ^ 2)
          ≤ P.LL * (P.aQ * P.LB) ^ 2 / 2
              * (KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) + η) := by
  -- round 7: DERIVED from the kernel identity (`kernel_window`, proved) and `majorant_excess` (`LF_Majorant`)
  filter_upwards [majorant_excess r ε hr hε Cab hCab η hη, kernel_window r ε hr hε] with Qn hE hK
  intro P hdes
  obtain ⟨F, M, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hE P hdes
  refine ⟨F, M, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  have h9 := hK P hdes
  nlinarith

/-- **F1c-3b′.** The Abel/Mertens step with the kernel identity, DERIVED from `smooth_majorant` and [R]'s weight-generic
Abel summation `Zeta23.ThmD.abel_sum_close` with the Chebyshev–Mertens estimate `Zeta23.Cheb.chebyshevMertens.cheb2a`
(`Σ_{n≤x}Λ(n)²/n = (log x)²/2 + O(log x)`), applied to `F/M` on `[0, L + 2]`. -/
theorem mertens_hsup (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * hsupP P (Real.log (n : ℝ))
        ≤ P.LL * (P.aQ * P.LB) ^ 2 / 2
            * (KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) + η) := by
  obtain ⟨C₀, hC₀⟩ := Zeta23.Cheb.chebyshevMertens.cheb2a
  filter_upwards [smooth_majorant r ε hr hε (2 * |C₀| + 10) (by positivity) η hη,
    design_basic_shell r ε hr hε] with Qn hSM hbas
  intro P hdes
  obtain ⟨F, M, hM0, hFd, hFc, hFb, hF0L, hF0, hdom, hint⟩ := hSM P hdes
  obtain ⟨-, hL8, -, -, -⟩ := hbas P hdes
  have hL' : (8 : ℝ) ≤ P.LB + 2 := by linarith
  have hderiv : deriv (fun y => F y / M) = fun y => deriv F y / M := by
    funext y; exact deriv_div_const M
  have hgd : Differentiable ℝ (fun y => F y / M) := hFd.div_const M
  have hgc : Continuous (deriv (fun y => F y / M)) := by rw [hderiv]; exact hFc.div_const M
  have hgb : ∀ y, |deriv (fun y => F y / M) y| ≤ 2 := by
    intro y
    rw [hderiv]
    show |deriv F y / M| ≤ 2
    rw [abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
    linarith [hFb y]
  have hgs : ∀ y, P.LB + 2 ≤ y → F y / M = 0 := fun y hy => by rw [hF0L y hy, zero_div]
  have hab := Zeta23.ThmD.abel_sum_close (c := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n)
    (by simp) (by simp [ArithmeticFunction.vonMangoldt_apply_one]) hC₀ (P.LB + 2) (Real.exp (P.LB + 2))
    (fun y => F y / M) hL' rfl hgd hgc hgb hgs
  -- unscale
  have e1 : (∑ n ∈ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)),
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n) n * (fun y => F y / M) (Real.log n))
      = (∑ n ∈ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)),
          (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ))) / M := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only
    ring
  have e2 : (∫ y in (0 : ℝ)..(P.LB + 2), (fun y => F y / M) y * y)
      = (∫ y in (0 : ℝ)..(P.LB + 2), F y * y) / M := by
    rw [← intervalIntegral.integral_div]
    congr 1
    funext y
    simp only
    ring
  rw [e1, e2] at hab
  have hab2 : (∑ n ∈ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)),
        (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ)))
      ≤ (∫ y in (0 : ℝ)..(P.LB + 2), F y * y) + M * ((2 * |C₀| + 10) * (P.LB + 2) ^ 2) := by
    have h := (abs_le.mp hab).2
    rw [← sub_div, div_le_iff₀ hM0] at h
    linarith
  -- `hsupP ≤ F` termwise on `primeRangeQ P`, then enlarge the range
  have hterm : ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * hsupP P (Real.log (n : ℝ))
      ≤ ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊ := hn
    rw [Finset.mem_Ioc] at hn'
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'.1
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hnX : (n : ℝ) ≤ P.XQ := le_trans (by exact_mod_cast hn'.2) (Nat.floor_le (Real.exp_pos _).le)
    have hlogL : Real.log (n : ℝ) ≤ P.LB := by
      have := Real.log_le_log (by linarith) hnX
      rwa [show P.XQ = Real.exp P.LB from rfl, Real.log_exp] at this
    exact mul_le_mul_of_nonneg_left (hdom _ hlog0 hlogL) (by positivity)
  have hsub : primeRangeQ P ⊆ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)) := by
    intro n hn
    have hn' : n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊ := hn
    show n ∈ Finset.Ioc 0 ⌊Real.exp (P.LB + 2)⌋₊
    rw [Finset.mem_Ioc] at hn' ⊢
    refine ⟨hn'.1, le_trans hn'.2 (Nat.floor_le_floor ?_)⟩
    show Real.exp P.LB ≤ Real.exp (P.LB + 2)
    exact Real.exp_le_exp.mpr (by linarith)
  have henl : ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ))
      ≤ ∑ n ∈ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)),
          (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg (by positivity) (hF0 _))
  linarith

end F1c
end ShellK
end ZetaShell
