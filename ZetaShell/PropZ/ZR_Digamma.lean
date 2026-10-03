/-
L7_5 (28 Sep 2026), round 5: `ZR_digamma'` (the statement of the shared leaf `ZR_digamma`), PROVED from the tree's
`GammaFactsChi` toolkit (Zeta23/ThmE/GammaFactsChiProof.lean): with `μ_χ = muq e r`,
  `Re ψ(1/4 + e/2 + it/2) + log(r/π) = 2π μ_χ(t)`;
  `|t| ≥ 1`: Stirling `|2πμ_χ(t) − log(r|t|/2π)| ≤ 20/t²` (`muq_stirling_const`, conductor-free constant);
  `|t| < 1`: `μ_χ(0) ≤ μ_χ(t) ≤ μ_χ(1)` (evenness and monotonicity), `μ_χ(0) > −1`, and Stirling at `τ = 1`.
Constant `C₁ = 50`, using `log(r(|t|+2)) ≥ log 2 + log r`.
-/
import ZetaShell.PropZ.ZDefsW
import Zeta23.ThmE.GammaFactsChiProof

open Complex

namespace ZetaShell.PropZ

theorem ZR_digamma' : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (e : ℕ), e ≤ 1 → ∀ t : ℝ,
    |(Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi)|
      ≤ C₁ * Real.log (r * (|t| + 2)) := by
  refine ⟨50, by norm_num, fun r hr e he t => ?_⟩
  have hπ := Real.pi_pos
  have hπ3 : Real.pi < 3.15 := Real.pi_lt_d2
  have hπ3' : 3 < Real.pi := Real.pi_gt_three
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h2π : 2 * Real.pi * (1 / (2 * Real.pi)) = 1 := by field_simp
  have hmu : (Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi)
      = 2 * Real.pi * Zeta23.ThmE.muq e r t := by
    unfold Zeta23.ThmE.muq
    calc (Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re + Real.log (r / Real.pi)
        = (2 * Real.pi * (1 / (2 * Real.pi))) * (Real.log (r / Real.pi)
            + (Complex.digamma (1 / 4 + (e : ℂ) / 2 + I * t / 2)).re) := by rw [h2π]; ring
      _ = _ := by ring
  rw [hmu]
  have hlog2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlr : 0 ≤ Real.log r := Real.log_nonneg hrr
  have hL : Real.log 2 + Real.log r ≤ Real.log (r * (|t| + 2)) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    apply Real.log_le_log (by linarith)
    nlinarith [abs_nonneg t]
  have hlog2π : Real.log (2 * Real.pi) ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity); linarith
  have hlog2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  set m := Zeta23.ThmE.muq e r t with hm
  rcases le_or_gt 1 |t| with ht | ht
  · -- Stirling
    have h := Zeta23.ThmE.GammaChi.muq_stirling_const he hr t ht
    rw [← hm] at h
    set ℓ := Real.log (r * |t| / (2 * Real.pi)) with hℓ
    have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    have h20 : (20 / (2 * Real.pi)) / t ^ 2 ≤ 20 / (2 * Real.pi) := div_le_self (by positivity) ht2
    have e1 : 2 * Real.pi * m - ℓ = 2 * Real.pi * (m - (1 / (2 * Real.pi)) * ℓ) := by
      calc 2 * Real.pi * m - ℓ = 2 * Real.pi * m - (2 * Real.pi * (1 / (2 * Real.pi))) * ℓ := by
            rw [h2π, one_mul]
        _ = 2 * Real.pi * (m - (1 / (2 * Real.pi)) * ℓ) := by ring
    have hA : |2 * Real.pi * m - ℓ| ≤ 20 := by
      rw [e1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      calc 2 * Real.pi * |m - 1 / (2 * Real.pi) * ℓ| ≤ 2 * Real.pi * (20 / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left (h.trans h20) (by positivity)
        _ = 20 := by field_simp
    have hrt : 1 ≤ (r : ℝ) * |t| := one_le_mul_of_one_le_of_one_le hrr ht
    have hℓe : ℓ = Real.log (r * |t|) - Real.log (2 * Real.pi) := by
      rw [hℓ, Real.log_div (by linarith) (by positivity)]
    have hl1 : 0 ≤ Real.log (r * |t|) := Real.log_nonneg hrt
    have hl2 : Real.log (r * |t|) ≤ Real.log (r * (|t| + 2)) :=
      Real.log_le_log (by linarith) (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    have hℓb : |ℓ| ≤ Real.log (r * |t|) + Real.log (2 * Real.pi) := by
      rw [hℓe, abs_le]; constructor <;> linarith
    have := abs_sub_abs_le_abs_sub (2 * Real.pi * m) ℓ
    linarith
  · -- |t| < 1: monotonicity between 0 and 1
    have hlo : Zeta23.ThmE.muq e r 0 ≤ m := Zeta23.ThmE.GammaChi.muq_zero_le (q := r) he t
    have hup : m ≤ Zeta23.ThmE.muq e r 1 := by
      rcases le_total 0 t with h0 | h0
      · exact Zeta23.ThmE.GammaChi.muq_monotoneOn (q := r) he (Set.mem_Ici.mpr h0)
          (Set.mem_Ici.mpr zero_le_one) (by linarith [le_abs_self t])
      · rw [hm, ← Zeta23.ThmE.GammaChi.muq_even (q := r) he t]
        exact Zeta23.ThmE.GammaChi.muq_monotoneOn (q := r) he (Set.mem_Ici.mpr (by linarith))
          (Set.mem_Ici.mpr zero_le_one) (by linarith [neg_abs_le t])
    have h0 := Zeta23.ThmE.GammaChi.neg_one_lt_muq_zero he hr
    have h1 := Zeta23.ThmE.GammaChi.muq_stirling_const he hr 1 (by norm_num)
    rw [abs_one, mul_one, one_pow, div_one] at h1
    have hlr1 : Real.log (r / (2 * Real.pi)) ≤ Real.log r := by
      rw [Real.log_div (by linarith) (by positivity)]; linarith
    have hup2 : 2 * Real.pi * Zeta23.ThmE.muq e r 1 ≤ Real.log r + 20 := by
      have hh := (abs_le.mp h1).2
      have e2 : 2 * Real.pi * Zeta23.ThmE.muq e r 1
          = 2 * Real.pi * (Zeta23.ThmE.muq e r 1 - 1 / (2 * Real.pi) * Real.log (r / (2 * Real.pi)))
            + (2 * Real.pi * (1 / (2 * Real.pi))) * Real.log (r / (2 * Real.pi)) := by ring
      rw [e2, h2π, one_mul]
      have : 2 * Real.pi * (Zeta23.ThmE.muq e r 1 - 1 / (2 * Real.pi) * Real.log (r / (2 * Real.pi)))
          ≤ 2 * Real.pi * (20 / (2 * Real.pi)) := mul_le_mul_of_nonneg_left hh (by positivity)
      have h20 : 2 * Real.pi * (20 / (2 * Real.pi)) = 20 := by field_simp
      linarith
    have hm1 : 2 * Real.pi * m ≤ Real.log r + 20 := by
      have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ 2 * Real.pi); linarith
    have hm0 : -(2 * Real.pi) < 2 * Real.pi * m := by
      have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      have h3 : 2 * Real.pi * (-1) < 2 * Real.pi * Zeta23.ThmE.muq e r 0 :=
        mul_lt_mul_of_pos_left h0 (by positivity)
      linarith
    rw [abs_le]; constructor <;> nlinarith

end ZetaShell.PropZ
