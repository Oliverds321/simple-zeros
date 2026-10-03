/-
L7_9 round 2: `principal_arc_mass` (K6, lem:K-P) derived from the four sub-nodes K6a `model_mass`,
K6b′ `sbp_L2` (summation by parts, proved), K6c′ `pnt_step`, K6d `tails` (proved).
Decomposition `S′ = M̃ + G₁ + G₂` (`M̃` the model, `G₁ = S^ϱ − M̃`, `G₂ = S′ − S^ϱ`) and the pointwise inequality
`|M̃ + G|² ≥ (1 − t)|M̃|² − t⁻¹|G|²`, `|G₁ + G₂|² ≤ 2|G₁|² + 2|G₂|²`, integrated over `[−Δ, Δ]` with `t = 1/log Q`
(this replaces the draft's `L²`-triangle inequality and avoids square roots).
-/
import ZetaShell.LemmaK.LK9_K6a_ModelMass
import ZetaShell.LemmaK.LK9_K6b_SBP
import ZetaShell.LemmaK.LK9_K6c_PNTStep
import ZetaShell.LemmaK.LK9_K6d_Tails

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK
namespace K6

lemma expSum_add (N : ℕ) (a b : ℕ → ℂ) (β : ℝ) :
    ZetaQ.expSum N (fun n => a n + b n) β = ZetaQ.expSum N a β + ZetaQ.expSum N b β := by
  unfold ZetaQ.expSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- `|M + G₁ + G₂|² ≥ (1 − t)|M|² − (2/t)(|G₁|² + |G₂|²)` for `0 < t ≤ 1`. -/
lemma pt_ineq (M G1 G2 : ℂ) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 - t) * ‖M‖ ^ 2 - (2 / t) * (‖G1‖ ^ 2 + ‖G2‖ ^ 2) ≤ ‖M + G1 + G2‖ ^ 2 := by
  have hG : ‖G1 + G2‖ ^ 2 ≤ 2 * (‖G1‖ ^ 2 + ‖G2‖ ^ 2) := by
    have h := norm_add_le G1 G2
    have h0 := norm_nonneg (G1 + G2)
    nlinarith [sq_nonneg (‖G1‖ - ‖G2‖), norm_nonneg G1, norm_nonneg G2]
  have hM : ‖M‖ ≤ ‖M + (G1 + G2)‖ + ‖G1 + G2‖ := by
    have := norm_sub_le (M + (G1 + G2)) (G1 + G2)
    simpa using this
  rw [add_assoc]
  set a := ‖M‖ with ha_def
  set b := ‖G1 + G2‖ with hb_def
  set c := ‖M + (G1 + G2)‖ with hc_def
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have h1 : (1 - t) * a ^ 2 ≤ (1 - t) * (b + c) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha (by linarith) 2) (by linarith)
  have h3 : (1 - t) * (b + c) ^ 2 ≤ (t * c ^ 2 + b ^ 2) / t := by
    rw [le_div_iff₀ ht0]
    nlinarith [sq_nonneg (t * c - (1 - t) * b)]
  have e3 : (t * c ^ 2 + b ^ 2) / t = c ^ 2 + b ^ 2 / t := by
    field_simp
  have h4 : b ^ 2 / t ≤ (2 / t) * (‖G1‖ ^ 2 + ‖G2‖ ^ 2) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hG ht0.le
  linarith

/-- the integrated form over `[−Δ, Δ]`. -/
lemma arc_lower (N : ℕ) (a m g1 g2 : ℕ → ℂ) (hdec : ∀ n, a n = m n + g1 n + g2 n) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 - t) * (∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N m β‖ ^ 2)
      - (2 / t) * ((∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N g1 β‖ ^ 2)
          + ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N g2 β‖ ^ 2)
      ≤ ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N a β‖ ^ 2 := by
  have hc : ∀ b : ℕ → ℂ, Continuous (fun β => ‖ZetaQ.expSum N b β‖ ^ 2) :=
    fun b => (ZetaQ.Gallagher.continuous_trig _ b).norm.pow 2
  have hi : ∀ b : ℕ → ℂ,
      IntervalIntegrable (fun β => ‖ZetaQ.expSum N b β‖ ^ 2) MeasureTheory.volume (-Δ) Δ :=
    fun b => (hc b).intervalIntegrable _ _
  have hS : ∀ β, ZetaQ.expSum N a β
      = ZetaQ.expSum N m β + ZetaQ.expSum N g1 β + ZetaQ.expSum N g2 β := by
    intro β
    have : a = fun n => (fun n => m n + g1 n) n + g2 n := funext fun n => by rw [hdec n]
    rw [this, expSum_add, expSum_add]
  have hmono := intervalIntegral.integral_mono_on (by linarith : -Δ ≤ Δ)
    (((hi m).const_mul (1 - t)).sub (((hi g1).add (hi g2)).const_mul (2 / t))) (hi a)
    (fun β _ => by
      show (1 - t) * ‖ZetaQ.expSum N m β‖ ^ 2
          - (2 / t) * (‖ZetaQ.expSum N g1 β‖ ^ 2 + ‖ZetaQ.expSum N g2 β‖ ^ 2)
        ≤ ‖ZetaQ.expSum N a β‖ ^ 2
      rw [hS β]
      exact pt_ineq _ _ _ t ht0 ht1)
  rw [intervalIntegral.integral_sub ((hi m).const_mul _) (((hi g1).add (hi g2)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi g1) (hi g2)] at hmono
  exact hmono

lemma rho6_eq_zero {u : ℝ} (hu : 1 < u) : rho6 u = 0 := by
  unfold rho6
  rw [abs_of_pos (by linarith), min_eq_right (by linarith), max_eq_left (by linarith)]

lemma c_support (T s R : ℝ) (n : ℕ) (hn : Real.exp (s + 1) < n) :
    asmooth T s R n - wmod T s n = 0 := by
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn
  have hlog : s + 1 < Real.log n := by
    rw [← Real.exp_lt_exp, Real.exp_log hn0]; exact hn
  have hr : rho6 (Real.log n - s) = 0 := rho6_eq_zero (by linarith)
  unfold asmooth wmod
  rw [hr]
  simp

lemma expSum_reduce (N M : ℕ) (hMN : M ≤ N) (c : ℕ → ℂ) (hc : ∀ n, M < n → c n = 0) (β : ℝ) :
    ZetaQ.expSum N c β = ZetaQ.expSum M c β := by
  unfold ZetaQ.expSum
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN]
  have : ∑ n ∈ Finset.Ioc M N, c n * ZetaQ.e ((n : ℝ) * β) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    rw [hc n hn.1, zero_mul]
  rw [this, add_zero]

/-- **K6 from its four sub-nodes.** Same statement as `principal_arc_mass`. -/
theorem principal_arc_mass_of_nodes (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      (1 - C / Real.log (Qn : ℝ)) * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi))
        ≤ ∫ β in (-(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))..
              (ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)),
            ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
              (aPrime (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)) β‖ ^ 2 := by
  obtain ⟨Ca, hCa0, hA⟩ := model_mass lam r ε hlam1 hlam2 hr hε
  obtain ⟨Cc, hC⟩ := pnt_step lam r ε hlam1 hlam2 hr hε
  obtain ⟨Cd, hD⟩ := tails lam r ε hlam1 hlam2 hr hε
  refine ⟨1 + Ca + 2 * Cc + 2 * Cd, ?_⟩
  have E1 : ∀ᶠ Qn : ℕ in atTop, (100 : ℝ) ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 100)
  have E2 : ∀ᶠ Qn : ℕ in atTop, (1 : ℝ) ≤ Real.log (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  filter_upwards [hA, hC, hD, E1, E2] with Qn hAQ hCQ hDQ h100 hlog s hs1 hs2
  have hA' := hAQ s hs1 hs2
  have hC' := hCQ s hs1 hs2
  have hD' := hDQ s hs1 hs2
  set x := Real.log (Qn : ℝ) with hx
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  set U := T / (2 * Real.pi) with hUdef
  set Δ := T * Lc (Qn : ℝ) T / (2 * Real.exp s) with hΔdef
  have hT1 : 1 ≤ T := Real.one_le_rpow hlog (by linarith)
  have hpi := Real.pi_lt_d2
  have hL0 : 0 < Lc (Qn : ℝ) T := by
    unfold Lc
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hΔ : 0 < Δ := by positivity
  have hU : 0 ≤ U := by positivity
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < 1 / x := by positivity
  have ht1 : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hlog
  have hmain := arc_lower ⌊Xlam lam (Qn : ℝ) T⌋₊ (aPrime T s (R0 (Qn : ℝ) T s)) (wmod T s)
    (fun n => asmooth T s (R0 (Qn : ℝ) T s) n - wmod T s n)
    (fun n => aPrime T s (R0 (Qn : ℝ) T s) n - asmooth T s (R0 (Qn : ℝ) T s) n)
    (fun n => by ring) Δ hΔ.le (1 / x) ht0 ht1
  have hB := sbp_L2 ⌊Real.exp (s + 1)⌋₊
    (fun n => asmooth T s (R0 (Qn : ℝ) T s) n - wmod T s n) Δ hΔ.le
  have hMX : ⌊Real.exp (s + 1)⌋₊ ≤ ⌊Xlam lam (Qn : ℝ) T⌋₊ := by
    apply Nat.floor_le_floor
    rw [Xlam]
    apply Real.exp_le_exp.mpr
    have h := hs2
    rw [Xlam, Real.log_exp] at h
    linarith
  have hred : ∀ β, ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) T⌋₊
      (fun n => asmooth T s (R0 (Qn : ℝ) T s) n - wmod T s n) β
      = ZetaQ.expSum ⌊Real.exp (s + 1)⌋₊
      (fun n => asmooth T s (R0 (Qn : ℝ) T s) n - wmod T s n) β := by
    intro β
    refine expSum_reduce _ _ hMX _ (fun n hn => ?_) β
    exact c_support T s _ n ((Nat.floor_lt (Real.exp_pos _).le).mp hn)
  set IM := ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) T⌋₊ (wmod T s) β‖ ^ 2 with hIM
  set I1 := ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) T⌋₊
    (fun n => asmooth T s (R0 (Qn : ℝ) T s) n - wmod T s n) β‖ ^ 2 with hI1
  set I2 := ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) T⌋₊
    (fun n => aPrime T s (R0 (Qn : ℝ) T s) n - asmooth T s (R0 (Qn : ℝ) T s) n) β‖ ^ 2 with hI2
  set J := ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) T⌋₊
    (aPrime T s (R0 (Qn : ℝ) T s)) β‖ ^ 2 with hJ
  have hI1eq : I1 = ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum ⌊Real.exp (s + 1)⌋₊
      (fun n => asmooth T s (R0 (Qn : ℝ) T s) n - wmod T s n) β‖ ^ 2 := by
    rw [hI1]
    exact intervalIntegral.integral_congr (fun β _ => by simp only [hred β])
  have hI1le : I1 ≤ Cc * U / x ^ 2 := by
    rw [hI1eq]
    exact hB.trans hC'
  have e1 : 2 / (1 / x) = 2 * x := by field_simp
  rw [e1] at hmain
  have hsub : 0 ≤ 1 - 1 / x := by linarith
  have s1 : (1 - 1 / x) * ((1 - Ca / x) * U) ≤ (1 - 1 / x) * IM := mul_le_mul_of_nonneg_left hA' hsub
  have s2 : 2 * x * (I1 + I2) ≤ 2 * x * (Cc * U / x ^ 2 + Cd * U / x ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add hI1le hD') (by positivity)
  have s3 : 2 * x * (Cc * U / x ^ 2 + Cd * U / x ^ 2) = 2 * (Cc + Cd) * U / x := by
    field_simp
    try ring
  have s4 : (1 - 1 / x) * ((1 - Ca / x) * U) - 2 * (Cc + Cd) * U / x
      - (1 - (1 + Ca + 2 * Cc + 2 * Cd) / x) * U = Ca * U / x ^ 2 := by
    field_simp
    try ring
  have s5 : 0 ≤ Ca * U / x ^ 2 := by positivity
  linarith

end K6
end LemmaK
end ZetaShell
