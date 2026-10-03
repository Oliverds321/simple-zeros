/-
L7_5 (28 Sep 2026), round 7: groundwork for `Z5Z_pair` (Step 5): repeated integration by parts against `e^{iλs}`.
  `∫ g e^{wu} = (−1/w)^n ∫ g^{(n)} e^{wu}`  (`g ∈ C_c^∞`, `w ≠ 0`),
  `|∫ g(u) e^{iλu} du| (1+|λ|)^n ≤ 2^n (∫|g| + ∫|g^{(n)}|)`.
Not yet wired into `Z5Z_pair`: what remains there is the smoothness of `s ↦ W(s−s₀)Ψ_{ρρ′}(s)` and the bounds on its
`s`-derivatives from Step 4 (`∂_s I_ρ[f_a](ξ; Δe^s) = I_ρ[f_{a+1}]`).
-/
import ZetaShell.PropZ.MellinDecay

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem iterDeriv_props (g : ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n g) ∧ HasCompactSupport (iteratedDeriv n g)
  | 0 => by simp only [iteratedDeriv_zero]; exact ⟨hg, hgc⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := iterDeriv_props g hg hgc n
    rw [iteratedDeriv_succ]
    exact ⟨(contDiff_infty_iff_deriv.mp h1).2, h2.deriv⟩

theorem integral_cexp_ibp_iter (g : ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (w : ℂ) (hw : w ≠ 0) : ∀ n : ℕ,
    ∫ u : ℝ, g u * Complex.exp (w * u) = (-(1 / w)) ^ n * ∫ u : ℝ, iteratedDeriv n g u * Complex.exp (w * u)
  | 0 => by simp
  | n + 1 => by
    obtain ⟨h1, h2⟩ := iterDeriv_props g hg hgc n
    rw [integral_cexp_ibp_iter g hg hgc w hw n, integral_cexp_ibp (iteratedDeriv n g)
      (h1.of_le (by exact_mod_cast le_top)) h2 w hw, iteratedDeriv_succ, pow_succ]
    ring

theorem norm_cexp_I_mul (lam u : ℝ) : ‖Complex.exp ((lam : ℂ) * I * u)‖ = 1 := by
  rw [show (lam : ℂ) * I * u = ((lam * u : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem norm_integral_cexp_I_le (g : ℝ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (lam : ℝ) (n : ℕ) :
    ‖∫ u : ℝ, g u * Complex.exp ((lam : ℂ) * I * u)‖ * (1 + |lam|) ^ n
      ≤ 2 ^ n * ((∫ u : ℝ, ‖g u‖) + ∫ u : ℝ, ‖iteratedDeriv n g u‖) := by
  have ha0 : 0 ≤ ∫ u : ℝ, ‖g u‖ := integral_nonneg fun u => norm_nonneg _
  have hb0 : 0 ≤ ∫ u : ℝ, ‖iteratedDeriv n g u‖ := integral_nonneg fun u => norm_nonneg _
  have hA : ‖∫ u : ℝ, g u * Complex.exp ((lam : ℂ) * I * u)‖ ≤ ∫ u : ℝ, ‖g u‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext u; rw [norm_mul, norm_cexp_I_mul, mul_one]
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  rcases le_or_gt |lam| 1 with hl | hl
  · have h1 : (1 + |lam|) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    calc ‖∫ u : ℝ, g u * Complex.exp ((lam : ℂ) * I * u)‖ * (1 + |lam|) ^ n
        ≤ (∫ u : ℝ, ‖g u‖) * 2 ^ n := mul_le_mul hA h1 (by positivity) ha0
      _ ≤ 2 ^ n * ((∫ u : ℝ, ‖g u‖) + ∫ u : ℝ, ‖iteratedDeriv n g u‖) := by nlinarith
  · have hlam0 : (lam : ℂ) * I ≠ 0 := by
      have : (lam : ℂ) ≠ 0 := by
        have : lam ≠ 0 := fun h => by rw [h, abs_zero] at hl; linarith
        exact_mod_cast this
      exact mul_ne_zero this I_ne_zero
    have hlp : 0 < |lam| := by linarith
    rw [integral_cexp_ibp_iter g hg hgc _ hlam0 n, norm_mul, norm_pow, norm_neg, norm_div, norm_one,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hB : ‖∫ u : ℝ, iteratedDeriv n g u * Complex.exp ((lam : ℂ) * I * u)‖
        ≤ ∫ u : ℝ, ‖iteratedDeriv n g u‖ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      congr 1; funext u; rw [norm_mul, norm_cexp_I_mul, mul_one]
    have h1 : (1 + |lam|) ^ n ≤ 2 ^ n * |lam| ^ n := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) n
    have hpow : (1 / |lam|) ^ n * |lam| ^ n = 1 := by
      rw [← mul_pow, one_div, inv_mul_cancel₀ hlp.ne', one_pow]
    have hq : 0 ≤ (1 / |lam|) ^ n := by positivity
    calc (1 / |lam|) ^ n * ‖∫ u : ℝ, iteratedDeriv n g u * Complex.exp ((lam : ℂ) * I * u)‖ * (1 + |lam|) ^ n
        ≤ (1 / |lam|) ^ n * (∫ u : ℝ, ‖iteratedDeriv n g u‖) * (2 ^ n * |lam| ^ n) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hB hq) h1 (by positivity) (mul_nonneg hq hb0)
      _ = 2 ^ n * (∫ u : ℝ, ‖iteratedDeriv n g u‖) * ((1 / |lam|) ^ n * |lam| ^ n) := by ring
      _ = 2 ^ n * (∫ u : ℝ, ‖iteratedDeriv n g u‖) := by rw [hpow, mul_one]
      _ ≤ 2 ^ n * ((∫ u : ℝ, ‖g u‖) + ∫ u : ℝ, ‖iteratedDeriv n g u‖) := by nlinarith

end ZetaShell.PropZ
