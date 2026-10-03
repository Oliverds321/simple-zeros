/-
L7_9 round 3, sub-node (c2) of `pnt_step`: sup and total variation of the smooth weight `w̃ = wmod`,
`sup|w̃| + Σ_{m<e^{s+1}}|w̃(m+1) − w̃(m)| ≤ K T² e^{−s/2}` (`T ≥ 1`, `s ≥ 3`). Uses the shared `DT_lipschitz`.
-/
import ZetaShell.LemmaK.LK9_K6_Defs
import ZetaShell.LemmaK.LK9_DT_Facts
import ZetaShell.LemmaK.LK9_K6c2_Aux

noncomputable section

namespace ZetaShell
namespace LemmaK

theorem wmod_var : ∃ K : ℝ, 0 ≤ K ∧ ∀ T s : ℝ, 1 ≤ T → 3 ≤ s →
    (∀ n : ℕ, ‖K6.wmod T s n‖ ≤ K * T ^ 2 * Real.exp (-(s / 2))) ∧
    ∑ m ∈ Finset.range ⌊Real.exp (s + 1)⌋₊, ‖K6.wmod T s (m + 1) - K6.wmod T s m‖
      ≤ K * T ^ 2 * Real.exp (-(s / 2)) := by
  refine ⟨400, by norm_num, fun T s hT hs => ?_⟩
  have he1 := Real.exp_one_lt_d9
  have he1' := Real.exp_one_gt_d9
  have hpi3 := Real.pi_gt_three
  set y := Real.exp (s / 2) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hys : Real.exp (-(s / 2)) = y⁻¹ := by rw [hy, Real.exp_neg]
  have hy2 : y ^ 2 = Real.exp s := by rw [hy, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsm1 : Real.exp (s - 1) = y ^ 2 / Real.exp 1 := by rw [Real.exp_sub, hy2]
  have hsp1 : Real.exp (s + 1) = y ^ 2 * Real.exp 1 := by rw [Real.exp_add, hy2]
  have hes2 : 2 ≤ Real.exp (s - 1) := by
    have : (2 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    exact this.trans (Real.exp_le_exp.mpr (by linarith))
  have hlow : y ^ 2 / 9 ≤ Real.exp (s - 1) / 2 := by
    rw [hsm1, div_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [sq_nonneg y]
  -- support: `w̃(n) ≠ 0 → e^{s−1} < n`
  have hsupp : ∀ n : ℕ, K6.wmod T s n ≠ 0 → Real.exp (s - 1) < n := by
    intro n hn
    have hρ : K6.rho6 (Real.log n - s) ≠ 0 := by
      intro h; apply hn; unfold K6.wmod; rw [h]; simp
    have hlt : |Real.log n - s| < 1 := by
      by_contra hc
      rw [not_lt] at hc
      apply hρ
      unfold K6.rho6
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    have hn0 : n ≠ 0 := by
      intro h0; rw [h0] at hlt; simp at hlt; rw [abs_of_nonneg (by linarith)] at hlt; linarith
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [abs_lt] at hlt
    rw [← Real.exp_log hnR]; exact Real.exp_lt_exp.mpr (by linarith)
  -- `√m ≥ y/3` on the support
  have hsqrt : ∀ x : ℝ, y ^ 2 / 9 ≤ x → y / 3 ≤ Real.sqrt x := by
    intro x hx
    apply Real.le_sqrt_of_sq_le
    nlinarith
  constructor
  · intro n
    by_cases h : K6.wmod T s n = 0
    · rw [h, norm_zero]; positivity
    · have hn := hsupp n h
      have hnR : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn
      have hsq : y / 3 ≤ Real.sqrt n := hsqrt n (by linarith)
      have hsq0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
      have hinv : (Real.sqrt n)⁻¹ ≤ 3 / y := by
        rw [inv_le_comm₀ hsq0 (by positivity), inv_div]; linarith
      unfold K6.wmod
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, K6.rpow_neg_half_eq _ hnR.le]
      have hD := DTFacts.DT_norm_le T (s - Real.log n) (by linarith)
      have hρ0 := K6.rho6_nonneg (Real.log n - s)
      have hρ1 := K6.rho6_le_one (Real.log n - s)
      rw [abs_of_nonneg (by positivity)]
      rw [hys]
      have hpi : (2 * Real.pi)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by positivity)]; linarith
      calc (2 * Real.pi)⁻¹ * (Real.sqrt n)⁻¹ * K6.rho6 (Real.log n - s) * ‖DT T (s - Real.log n)‖
          ≤ 1 * (3 / y) * 1 * T := by
            apply mul_le_mul _ hD (norm_nonneg _) (by positivity)
            apply mul_le_mul _ hρ1 hρ0 (by positivity)
            exact mul_le_mul hpi hinv (by positivity) zero_le_one
        _ ≤ 400 * T ^ 2 * y⁻¹ := by
            rw [div_eq_mul_inv]
            have hyi : 0 < y⁻¹ := inv_pos.mpr hy0
            have hTT : T * y⁻¹ ≤ T ^ 2 * y⁻¹ := mul_le_mul_of_nonneg_right (by nlinarith) hyi.le
            have e1 : 1 * (3 * y⁻¹) * 1 * T = 3 * (T * y⁻¹) := by ring
            have e2 : 400 * T ^ 2 * y⁻¹ = 400 * (T ^ 2 * y⁻¹) := by ring
            rw [e1, e2]
            linarith [hTT, (by positivity : 0 ≤ T * y⁻¹)]
  · -- the variation
    have hterm : ∀ m ∈ Finset.range ⌊Real.exp (s + 1)⌋₊,
        ‖K6.wmod T s (m + 1) - K6.wmod T s m‖ ≤ (243 / 2) * T ^ 2 / y ^ 3 := by
      intro m _
      by_cases h : K6.wmod T s (m + 1) - K6.wmod T s m = 0
      · rw [h, norm_zero]; positivity
      · have hm : Real.exp (s - 1) - 1 < m := by
          by_cases h1 : K6.wmod T s (m + 1) = 0
          · have h2 : K6.wmod T s m ≠ 0 := by
              intro h2; apply h; rw [h1, h2, sub_zero]
            have := hsupp m h2; linarith
          · have := hsupp (m + 1) h1; push_cast at this; linarith
        have hmR : y ^ 2 / 9 ≤ (m : ℝ) := by linarith
        have hm1 : 1 ≤ m := by
          have : (1 : ℝ) < m := by linarith
          exact_mod_cast this.le
        have hstep := K6.wmod_step T s (by linarith) m hm1
        have hsq : y / 3 ≤ Real.sqrt m := hsqrt m hmR
        have hden : y ^ 3 / 27 ≤ (m : ℝ) * Real.sqrt m := by
          have h9 : y ^ 2 / 9 * (y / 3) ≤ (m : ℝ) * Real.sqrt m :=
            mul_le_mul hmR hsq (by positivity) (by positivity)
          nlinarith
        have hnum : (2 * Real.pi)⁻¹ * (3 * T + (3 / 2) * T ^ 2) ≤ (9 / 2) * T ^ 2 := by
          have hpi : (2 * Real.pi)⁻¹ ≤ 1 := by rw [inv_le_one₀ (by positivity)]; linarith
          have h0 : 0 ≤ 3 * T + (3 / 2) * T ^ 2 := by positivity
          calc (2 * Real.pi)⁻¹ * (3 * T + (3 / 2) * T ^ 2) ≤ 1 * (3 * T + (3 / 2) * T ^ 2) :=
                mul_le_mul_of_nonneg_right hpi h0
            _ ≤ (9 / 2) * T ^ 2 := by nlinarith
        refine hstep.trans ?_
        calc (2 * Real.pi)⁻¹ * (3 * T + (3 / 2) * T ^ 2) / ((m : ℝ) * Real.sqrt m)
            ≤ (9 / 2) * T ^ 2 / (y ^ 3 / 27) := by
              apply div_le_div₀ (by positivity) hnum (by positivity) hden
          _ = (243 / 2) * T ^ 2 / y ^ 3 := by field_simp; ring
    have hM : ((⌊Real.exp (s + 1)⌋₊ : ℕ) : ℝ) ≤ y ^ 2 * Real.exp 1 := by
      rw [← hsp1]; exact Nat.floor_le (Real.exp_pos _).le
    calc ∑ m ∈ Finset.range ⌊Real.exp (s + 1)⌋₊, ‖K6.wmod T s (m + 1) - K6.wmod T s m‖
        ≤ ∑ m ∈ Finset.range ⌊Real.exp (s + 1)⌋₊, (243 / 2) * T ^ 2 / y ^ 3 := Finset.sum_le_sum hterm
      _ = (⌊Real.exp (s + 1)⌋₊ : ℝ) * ((243 / 2) * T ^ 2 / y ^ 3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (y ^ 2 * Real.exp 1) * ((243 / 2) * T ^ 2 / y ^ 3) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
      _ ≤ 400 * T ^ 2 * Real.exp (-(s / 2)) := by
          rw [hys]
          have e : (y ^ 2 * Real.exp 1) * ((243 / 2) * T ^ 2 / y ^ 3)
              = ((243 / 2) * Real.exp 1) * (T ^ 2 * y⁻¹) := by
            field_simp
          rw [e]
          have h0 : 0 ≤ T ^ 2 * y⁻¹ := by positivity
          have hc : (243 / 2) * Real.exp 1 ≤ 400 := by linarith
          calc ((243 / 2) * Real.exp 1) * (T ^ 2 * y⁻¹) ≤ 400 * (T ^ 2 * y⁻¹) :=
                mul_le_mul_of_nonneg_right hc h0
            _ = 400 * T ^ 2 * y⁻¹ := by ring

end LemmaK
end ZetaShell
