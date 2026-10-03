/-
L7_9 round 4: ingredients of (a1) `model_l2_lower`.
* `DT_core_mass`: `∫_{−1/2}^{1/2}|D_T|² ≥ 2πT − 8 − 32/T`, from the tree's `ZetaQ.DT_sq_integral`
  (`∫_ℝ|D_T|² = 2πT`) and `ZetaQ.DT_tail_mass_sharp` (`∫_{|v|≥y}|D_T|² ≤ 4/y + 8/(Ty²)`).
* `gfun y = y⁻¹|D_T(s − log y)|²`: `∫_{e^a}^{e^b} gfun = ∫_a^b |D_T(s − u)|² du` (substitution `y = e^u`), and
  `|gfun y − gfun n| ≤ 4T³/n²` on `[n, n+1]`.
-/
import ZetaShell.LemmaK.LK9_K6_Defs
import ZetaShell.LemmaK.LK9_DT_Facts
import ZetaShell.PropZ.DT_Facts

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace LemmaK
namespace K6

/-- a `ParamsQ` carrying only `T` (the tree's `D_T` facts depend on `P.T` alone). -/
def PT (T : ℝ) : ZetaQ.ParamsQ :=
  { Q := 1, T := T, lam := 1, w := 1, D0 := 1, ϱ := fun _ => 0, prof := 0 }

lemma DT_eq_PT (T v : ℝ) : DT T v = (PT T).DT v := by
  unfold DT ZetaQ.ParamsQ.DT PT
  congr 1
  funext τ
  ring_nf

theorem DT_core_mass (T : ℝ) (hT : 1 ≤ T) :
    2 * Real.pi * T - 8 - 32 / T ≤ ∫ v in (-(1 / 2 : ℝ))..(1 / 2), ‖DT T v‖ ^ 2 := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hfull := ZetaQ.DT_sq_integral (PT T) hT0
  have htail := ZetaQ.DT_tail_mass_sharp (PT T) (by show (0 : ℝ) < T; linarith)
    (y := 1 / 2) (by norm_num)
  have hint := ZetaQ.DT_normSq_integrable (PT T) hT0
  have hfun : (fun v => ‖DT T v‖ ^ 2) = fun v => ‖(PT T).DT v‖ ^ 2 := by
    funext v; rw [DT_eq_PT]
  have hPT : (PT T).T = T := rfl
  rw [hPT] at hfull htail
  set S := Set.Icc (-(1 / 2 : ℝ)) (1 / 2) with hS
  have hsplit := integral_add_compl (s := S) measurableSet_Icc hint
  have hcompl : ∫ v in Sᶜ, ‖(PT T).DT v‖ ^ 2 ≤ ∫ v in {v : ℝ | 1 / 2 ≤ |v|}, ‖(PT T).DT v‖ ^ 2 := by
    apply setIntegral_mono_set hint.integrableOn
    · exact Filter.Eventually.of_forall fun v => sq_nonneg _
    · refine Filter.Eventually.of_forall fun v hv => ?_
      have hv' : v ∉ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := hv
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv'
      show 1 / 2 ≤ |v|
      rcases hv' with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have hII : ∫ v in (-(1 / 2 : ℝ))..(1 / 2), ‖DT T v‖ ^ 2 = ∫ v in S, ‖(PT T).DT v‖ ^ 2 := by
    rw [hfun, intervalIntegral.integral_of_le (by norm_num), hS, integral_Icc_eq_integral_Ioc]
  rw [hII]
  have e : 4 / (1 / 2 : ℝ) + 8 / (T * (1 / 2) ^ 2) = 8 + 32 / T := by field_simp; ring
  rw [e] at htail
  linarith

/-- `y⁻¹|D_T(s − log y)|²`. -/
def gfun (T s y : ℝ) : ℝ := y⁻¹ * ‖DT T (s - Real.log y)‖ ^ 2

lemma DT_cont (T : ℝ) : Continuous (fun v => DT T v) := by
  show Continuous (ZetaShell.DTFacts.DTf T)
  exact ZetaShell.DTFacts.DTf_continuous T

lemma gfun_contOn (T s a b : ℝ) (ha : 0 < a) : ContinuousOn (gfun T s) (Set.Icc a b) := by
  unfold gfun
  apply ContinuousOn.mul
  · exact continuousOn_inv₀.mono fun y hy => (ne_of_gt (lt_of_lt_of_le ha hy.1))
  · apply ContinuousOn.pow
    apply ContinuousOn.norm
    refine (DT_cont T).comp_continuousOn ?_
    exact continuousOn_const.sub (Real.continuousOn_log.mono fun y hy =>
      (ne_of_gt (lt_of_lt_of_le ha hy.1)))

theorem gfun_subst (T s a b : ℝ) (hab : a ≤ b) :
    ∫ y in Real.exp a..Real.exp b, gfun T s y = ∫ u in a..b, ‖DT T (s - u)‖ ^ 2 := by
  have h := intervalIntegral.integral_comp_mul_deriv'' (a := a) (b := b) (f := Real.exp)
    (f' := Real.exp) (g := gfun T s) Real.continuous_exp.continuousOn
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.continuous_exp.continuousOn
    (by
      apply (gfun_contOn T s (Real.exp a) (Real.exp b) (Real.exp_pos a)).mono
      rintro y ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact ⟨Real.exp_le_exp.mpr hu.1, Real.exp_le_exp.mpr hu.2⟩)
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [Function.comp, gfun, Real.log_exp]
  field_simp

lemma gfun_step (T s : ℝ) (hT : 1 ≤ T) (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy1 : (n : ℝ) ≤ y)
    (hy2 : y ≤ n + 1) : gfun T s n ≤ gfun T s y + 4 * T ^ 3 / (n : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < y := by linarith
  have hT0 : 0 ≤ T := by linarith
  set Dn := ‖DT T (s - Real.log n)‖ with hDn
  set Dy := ‖DT T (s - Real.log y)‖ with hDy
  have hDn0 : 0 ≤ Dn := norm_nonneg _
  have hDy0 : 0 ≤ Dy := norm_nonneg _
  have hDnT : Dn ≤ T := DTFacts.DT_norm_le T _ hT0
  have hDyT : Dy ≤ T := DTFacts.DT_norm_le T _ hT0
  have hlog : Real.log y - Real.log n ≤ 1 / n := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / n by positivity)
    rw [Real.log_div hy0.ne' hn0.ne'] at h
    have e : y / n - 1 = (y - n) / n := by field_simp
    rw [e] at h
    have : (y - n) / (n : ℝ) ≤ 1 / n := div_le_div_of_nonneg_right (by linarith) hn0.le
    linarith
  have hlog0 : 0 ≤ Real.log y - Real.log n := sub_nonneg.mpr (Real.log_le_log hn0 hy1)
  have hDdiff : |Dn - Dy| ≤ (3 / 2) * T ^ 2 * (1 / n) := by
    have h1 := DTFacts.DT_lipschitz T (s - Real.log n) (s - Real.log y) hT0
    have h2 : |Dn - Dy| ≤ ‖DT T (s - Real.log n) - DT T (s - Real.log y)‖ := abs_norm_sub_norm_le _ _
    rw [show s - Real.log n - (s - Real.log y) = Real.log y - Real.log n by ring,
      abs_of_nonneg hlog0] at h1
    calc |Dn - Dy| ≤ (3 / 2) * T ^ 2 * (Real.log y - Real.log n) := h2.trans h1
      _ ≤ (3 / 2) * T ^ 2 * (1 / n) := mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsq : Dn ^ 2 - Dy ^ 2 ≤ 3 * T ^ 3 / n := by
    have e : Dn ^ 2 - Dy ^ 2 = (Dn - Dy) * (Dn + Dy) := by ring
    rw [e]
    have h1 : Dn - Dy ≤ (3 / 2) * T ^ 2 * (1 / n) := (le_abs_self _).trans hDdiff
    have h2 : Dn + Dy ≤ 2 * T := by linarith
    rcases le_or_gt (Dn - Dy) 0 with h | h
    · have : (Dn - Dy) * (Dn + Dy) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
      have : 0 ≤ 3 * T ^ 3 / n := by positivity
      linarith
    · calc (Dn - Dy) * (Dn + Dy) ≤ ((3 / 2) * T ^ 2 * (1 / n)) * (2 * T) :=
            mul_le_mul h1 h2 (by linarith) (by positivity)
        _ = 3 * T ^ 3 / n := by field_simp; try ring
  have hinv : (n : ℝ)⁻¹ - y⁻¹ ≤ 1 / (n : ℝ) ^ 2 := by
    rw [inv_sub_inv hn0.ne' hy0.ne']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  unfold gfun
  rw [← hDn, ← hDy]
  have hyinv : y⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ hn0 hy1
  have hDn2 : Dn ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hDn0 hDnT 2
  -- `n⁻¹Dn² − y⁻¹Dy² = (n⁻¹ − y⁻¹)Dn² + y⁻¹(Dn² − Dy²)`
  have e : (n : ℝ)⁻¹ * Dn ^ 2 - y⁻¹ * Dy ^ 2 = ((n : ℝ)⁻¹ - y⁻¹) * Dn ^ 2 + y⁻¹ * (Dn ^ 2 - Dy ^ 2) := by ring
  have t1 : ((n : ℝ)⁻¹ - y⁻¹) * Dn ^ 2 ≤ 1 / (n : ℝ) ^ 2 * T ^ 2 :=
    mul_le_mul hinv hDn2 (sq_nonneg _) (by positivity)
  have t2 : y⁻¹ * (Dn ^ 2 - Dy ^ 2) ≤ (n : ℝ)⁻¹ * (3 * T ^ 3 / n) := by
    rcases le_or_gt (Dn ^ 2 - Dy ^ 2) 0 with h | h
    · have : y⁻¹ * (Dn ^ 2 - Dy ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      have : 0 ≤ (n : ℝ)⁻¹ * (3 * T ^ 3 / n) := by positivity
      linarith
    · exact mul_le_mul hyinv hsq h.le (by positivity)
  have hT23 : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT (by norm_num)
  have t3 : 1 / (n : ℝ) ^ 2 * T ^ 2 + (n : ℝ)⁻¹ * (3 * T ^ 3 / n) ≤ 4 * T ^ 3 / (n : ℝ) ^ 2 := by
    have e2 : 1 / (n : ℝ) ^ 2 * T ^ 2 + (n : ℝ)⁻¹ * (3 * T ^ 3 / n) = (T ^ 2 + 3 * T ^ 3) / (n : ℝ) ^ 2 := by
      field_simp
    rw [e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  linarith

end K6
end LemmaK
end ZetaShell
