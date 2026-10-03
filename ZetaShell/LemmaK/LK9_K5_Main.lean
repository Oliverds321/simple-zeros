/-
L7_9 helper for node K5 (`small_primes_l2`, Lemma K.5 on `ℓ_K ≤ s ≤ log 𝒳`): the deterministic bound.
For `T ≥ 0`, `s ≥ 2`, `R < e^{s/2}`, and any cut-off `X`,
`‖a − a′‖² ≤ (4π²)⁻¹(8/s)(s/2 + log 4 + 4) + (4π²)⁻¹T²·C₂e^{−s/8}`:
* `n ≤ e^{s/2}`: `|s − log n| ≥ s/2`, so `|D_T| ≤ 4/s`; then `Λ(n)² ≤ (s/2)Λ(n)` and Mertens
  (`Mertens.sum_mangoldt_div_eq_log`, `|Σ_{n≤y}Λ(n)/n − log y| ≤ log 4 + 4`);
* `n > e^{s/2}`: `n` is a prime power with `minFac n ≤ R < e^{s/2} < n`, so a proper prime power;
  `|D_T| ≤ T` and the tail `Σ_{n > y, proper} Λ(n)²/n ≤ C₂ y^{−1/4}` (`LK9_K5_Tail`).
-/
import ZetaShell.Defs.LK_Defs
import ZetaShell.LemmaK.LK9_K5_Tail

noncomputable section
open Finset

namespace ZetaShell
namespace LemmaK
namespace K5Aux

lemma norm_exp_I_mul (τ v : ℝ) : ‖Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ))‖ = 1 := by
  rw [show Complex.I * (τ : ℂ) * (v : ℂ) = ((τ * v : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma DT_le_T (T v : ℝ) (hT : 0 ≤ T) : ‖DT T v‖ ≤ T := by
  unfold DT
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T) (C := 1)
    (f := fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ)))
    (fun τ _ => (norm_exp_I_mul τ v).le)
  rw [show |2 * T - T| = T by rw [abs_of_nonneg (by linarith)]; ring, one_mul] at h
  exact h

lemma DT_le_two_div (T v : ℝ) (hv : v ≠ 0) : ‖DT T v‖ ≤ 2 / |v| := by
  unfold DT
  have hc : Complex.I * (v : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hv)
  have e : (fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ)))
      = fun τ : ℝ => Complex.exp (Complex.I * (v : ℂ) * τ) := by
    funext τ; ring_nf
  rw [e, integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have h1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (v : ℂ) * (x : ℂ))‖ = 1 := by
    intro x
    rw [show Complex.I * (v : ℂ) * (x : ℂ) = (x : ℂ) * (v : ℂ) * Complex.I by ring]
    have := norm_exp_I_mul x v
    rw [show Complex.I * (x : ℂ) * (v : ℂ) = (x : ℂ) * (v : ℂ) * Complex.I by ring] at this
    exact this
  have hnum : ‖Complex.exp (Complex.I * (v : ℂ) * ((2 * T : ℝ) : ℂ))
      - Complex.exp (Complex.I * (v : ℂ) * (T : ℂ))‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (Complex.I * (v : ℂ) * ((2 * T : ℝ) : ℂ))‖
          + ‖Complex.exp (Complex.I * (v : ℂ) * (T : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h1]; norm_num
  have hv' : 0 < |v| := abs_pos.mpr hv
  exact div_le_div_of_nonneg_right hnum hv'.le

lemma norm_acoef_sq (T s : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖acoef T s n‖ ^ 2 = (4 * Real.pi ^ 2)⁻¹ * (ArithmeticFunction.vonMangoldt n ^ 2 / n)
      * ‖DT T (s - Real.log n)‖ ^ 2 := by
  unfold acoef
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
    exact Real.rpow_neg_one _
  rw [mul_pow, mul_pow, hr]
  field_simp
  ring

/-- **The deterministic bound for K5.** -/
theorem l2_bound (T s R : ℝ) (X : ℕ) (hT : 0 ≤ T) (hs : 2 ≤ s) (hR : R < Real.exp (s / 2)) :
    ZetaQ.l2sq X (fun n => acoef T s n - aPrime T s R n)
      ≤ (4 * Real.pi ^ 2)⁻¹ * (8 / s) * (s / 2 + (Real.log 4 + 4))
        + (4 * Real.pi ^ 2)⁻¹ * T ^ 2 * (C2 * (Real.exp (s / 2)) ^ (-(1 / 4 : ℝ))) := by
  classical
  set y := Real.exp (s / 2) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : 1 ≤ y := Real.one_le_exp (by linarith)
  have hlogy : Real.log y = s / 2 := Real.log_exp _
  set c : ℝ := (4 * Real.pi ^ 2)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  set S := (ppp X).filter (fun n : ℕ => y < (n : ℝ)) with hS
  set FA : ℕ → ℝ := fun n =>
    if (n : ℝ) ≤ y then c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * (4 / s) ^ 2 else 0 with hFA
  set FB : ℕ → ℝ := fun n =>
    if n ∈ S then c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * T ^ 2 else 0 with hFB
  have hFA0 : ∀ n, 0 ≤ FA n := fun n => by
    simp only [hFA]; split_ifs
    · positivity
    · exact le_refl 0
  have hFB0 : ∀ n, 0 ≤ FB n := fun n => by
    simp only [hFB]; split_ifs
    · positivity
    · exact le_refl 0
  -- pointwise
  have hpt : ∀ n ∈ Finset.Ioc 0 X, ‖acoef T s n - aPrime T s R n‖ ^ 2 ≤ FA n + FB n := by
    intro n hn
    have hnIoc := hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    unfold aPrime
    split_ifs with hA
    · rw [sub_self, norm_zero]
      have := hFA0 n; have := hFB0 n
      norm_num; linarith
    · rw [sub_zero, norm_acoef_sq T s n hn.1]
      by_cases hny : (n : ℝ) ≤ y
      · have hFAn : FA n = c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * (4 / s) ^ 2 := by
          simp only [hFA, if_pos hny]
        have hlogn : Real.log n ≤ s / 2 := by
          rw [← hlogy]; exact Real.log_le_log hn0 hny
        have hv : s / 2 ≤ s - Real.log n := by linarith
        have hvpos : 0 < s - Real.log n := by linarith
        have hD := DT_le_two_div T (s - Real.log n) hvpos.ne'
        rw [abs_of_pos hvpos] at hD
        have hD' : ‖DT T (s - Real.log n)‖ ≤ 4 / s := by
          refine hD.trans ?_
          rw [div_le_div_iff₀ hvpos (by linarith)]
          linarith
        have hD2 : ‖DT T (s - Real.log n)‖ ^ 2 ≤ (4 / s) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hD' 2
        have hco : 0 ≤ c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) := by positivity
        have := mul_le_mul_of_nonneg_left hD2 hco
        have := hFB0 n
        linarith
      · rw [not_le] at hny
        by_cases hpp : IsPrimePow n
        · by_cases hprime : n.Prime
          · exfalso
            apply hA
            refine ⟨hpp, ?_⟩
            rw [Nat.Prime.minFac_eq hprime]
            linarith
          · have hmem : n ∈ S := by
              rw [hS, Finset.mem_filter]
              refine ⟨?_, hny⟩
              simp only [ppp, Finset.mem_filter]
              exact ⟨hnIoc, hpp, hprime⟩
            have hFBn : FB n = c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * T ^ 2 := by
              simp only [hFB, if_pos hmem]
            have hD2 : ‖DT T (s - Real.log n)‖ ^ 2 ≤ T ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (DT_le_T T _ hT) 2
            have hco : 0 ≤ c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) := by positivity
            have := mul_le_mul_of_nonneg_left hD2 hco
            have := hFA0 n
            linarith
        · have hL : ArithmeticFunction.vonMangoldt n = 0 :=
            ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
          rw [hL]
          have := hFA0 n; have := hFB0 n
          norm_num; linarith
  -- sum
  have hsum : ZetaQ.l2sq X (fun n => acoef T s n - aPrime T s R n)
      ≤ ∑ n ∈ Finset.Ioc 0 X, FA n + ∑ n ∈ Finset.Ioc 0 X, FB n := by
    unfold ZetaQ.l2sq
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  -- part A
  have hA : ∑ n ∈ Finset.Ioc 0 X, FA n ≤ c * (8 / s) * (s / 2 + (Real.log 4 + 4)) := by
    have e1 : ∑ n ∈ Finset.Ioc 0 X, FA n
        = ∑ n ∈ (Finset.Ioc 0 X).filter (fun n : ℕ => (n : ℝ) ≤ y),
            c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * (4 / s) ^ 2 := by
      rw [Finset.sum_filter]
    have hsub : (Finset.Ioc 0 X).filter (fun n : ℕ => (n : ℝ) ≤ y) ⊆ Finset.Ioc 0 ⌊y⌋₊ := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Ioc] at hn
      rw [Finset.mem_Ioc]
      exact ⟨hn.1.1, Nat.le_floor hn.2⟩
    have hterm : ∀ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * (4 / s) ^ 2
          ≤ c * (4 / s) ^ 2 * (s / 2) * (ArithmeticFunction.vonMangoldt n / n) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff hy0.le).mp hn.2
      have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have hΛ : ArithmeticFunction.vonMangoldt n ≤ s / 2 := by
        have := ArithmeticFunction.vonMangoldt_le_log (n := n)
        have := Real.log_le_log hn0 hny
        linarith
      have hsq : ArithmeticFunction.vonMangoldt n ^ 2 ≤ (s / 2) * ArithmeticFunction.vonMangoldt n := by
        nlinarith
      have hk : 0 ≤ c * (4 / s) ^ 2 / n := by positivity
      have := mul_le_mul_of_nonneg_left hsq hk
      calc c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * (4 / s) ^ 2
          = c * (4 / s) ^ 2 / n * ArithmeticFunction.vonMangoldt n ^ 2 := by ring
        _ ≤ c * (4 / s) ^ 2 / n * ((s / 2) * ArithmeticFunction.vonMangoldt n) := this
        _ = c * (4 / s) ^ 2 * (s / 2) * (ArithmeticFunction.vonMangoldt n / n) := by ring
    have hmert := Mertens.sum_mangoldt_div_eq_log hy1
    have hmert' : ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
        ≤ s / 2 + (Real.log 4 + 4) := by
      have := (abs_le.mp hmert).2
      rw [hlogy] at this
      linarith
    have hk0 : 0 ≤ c * (4 / s) ^ 2 * (s / 2) := by
      have : 0 < s := by linarith
      positivity
    calc ∑ n ∈ Finset.Ioc 0 X, FA n
        = ∑ n ∈ (Finset.Ioc 0 X).filter (fun n : ℕ => (n : ℝ) ≤ y),
            c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * (4 / s) ^ 2 := e1
      _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * (4 / s) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, c * (4 / s) ^ 2 * (s / 2) * (ArithmeticFunction.vonMangoldt n / n) :=
          Finset.sum_le_sum hterm
      _ = c * (4 / s) ^ 2 * (s / 2) * ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n / n := by
          rw [Finset.mul_sum]
      _ ≤ c * (4 / s) ^ 2 * (s / 2) * (s / 2 + (Real.log 4 + 4)) :=
          mul_le_mul_of_nonneg_left hmert' hk0
      _ = c * (8 / s) * (s / 2 + (Real.log 4 + 4)) := by
          have : s ≠ 0 := by linarith
          field_simp
          ring
  -- part B
  have hB : ∑ n ∈ Finset.Ioc 0 X, FB n ≤ c * T ^ 2 * (C2 * y ^ (-(1 / 4 : ℝ))) := by
    have hSsub : S ⊆ Finset.Ioc 0 X := by
      intro n hn
      rw [hS, Finset.mem_filter] at hn
      simp only [ppp, Finset.mem_filter] at hn
      exact hn.1.1
    have e1 : ∑ n ∈ Finset.Ioc 0 X, FB n
        = ∑ n ∈ S, c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * T ^ 2 := by
      simp only [hFB]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSsub]
    rw [e1]
    have ht := tail_ppp X y hy0
    have hk : 0 ≤ c * T ^ 2 := by positivity
    calc ∑ n ∈ S, c * (ArithmeticFunction.vonMangoldt n ^ 2 / n) * T ^ 2
        = c * T ^ 2 * ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ^ 2 / n := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by ring
      _ ≤ c * T ^ 2 * (C2 * y ^ (-(1 / 4 : ℝ))) := mul_le_mul_of_nonneg_left ht hk
  linarith

end K5Aux
end LemmaK
end ZetaShell
