/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Abel summation of `log q` and `(log q)²` against an explicit counting function

Abstract partial-summation lemma for ledger row 8 (family averages `⟨log q⟩`, `⟨(log q)²⟩`
and the conductor-spread variance `⟨(log q)²⟩ − ⟨log q⟩² = 1/4 + O(·)`).

**Hypothesis shape (matches `ZetaQ.Normalisation.N2.Astar_bound` exactly, with `m = 2`, `K = 5`,
`c = 18/π⁴`, `a q = (phiStar q : ℝ)`):**
`hF : ∀ N : ℕ, 1 ≤ N → |(∑ q ∈ Icc 1 N, a q) - c * N ^ 2| ≤ K * N * (1 + log N) ^ m`.

**Conclusions (all for real `x ≥ 1`, index sets `Finset.Icc 1 ⌊x⌋₊`; integer versions `_nat`):**
* `sum_log_bound`   : `|Σ a q log q − c x² (log x − 1/2)| ≤ (K + 3c) x (1 + log x)^(m+1)`
* `sum_logsq_bound` : `|Σ a q (log q)² − c x² ((log x)² − log x + 1/2)| ≤ (2K + 5c) x (1 + log x)^(m+2)`
* `avg_bounds` / `avg_bounds_Icc2` : the averages and the variance, given a lower bound
  `c₀ x² ≤ Σ a q` (over `Icc 1`, resp. `Icc 2` — the tree's family excludes `q = 1`):
  `|⟨log q⟩ − (log x − 1/2)| ≤ (2K+5c)/c₀ · (1+log x)^(m+1)/x`,
  `|⟨(log q)²⟩ − ((log x)² − log x + 1/2)| ≤ (3K+7c)/c₀ · (1+log x)^(m+2)/x`,
  `|⟨(log q)²⟩ − ⟨log q⟩² − 1/4| ≤ (7K+17c)/c₀ · (1+log x)^(m+2)/x`
  (for `Icc 2` the constants pick up `+ a 1`, `+ a 1`, `+ 3 a 1`).
* `cnt_lower_of`, `cnt_lower_explicit_m2`, `cnt2_lower_explicit_m2` : explicit `c₀ = c/2`
  (resp. `c/4`) and explicit threshold `x₀' = (32 (K + 2c)/c)²` for `m = 2`.

Note the exponents: with a count error `x (1 + log x)^m`, the boundary term `E(x) log x`
forces `(1 + log x)^(m+1)` for the first moment and `(1 + log x)^(m+2)` for the second —
for the tree's `m = 2` these are `(1 + log x)³` and `(1 + log x)⁴`, exactly the shapes of
`ZetaQ.Normalisation.N2.Alog_bound` / `ZetaQ.Normalisation.N2.Alog2_bound` (with smaller constants here).

Mathlib engine: `sum_mul_eq_sub_integral_mul₀` (Abel summation, `Mathlib/NumberTheory/AbelSummation`),
`integrableOn_mul_sum_Icc`, `norm_setIntegral_le_of_norm_le_const`, `integral_id`,
`intervalIntegral.integral_eq_sub_of_hasDerivAt`.
-/

open MeasureTheory Finset

namespace ZetaQ.AbelLogPow

lemma sum_Icc_zero_eq_sum_Icc_one (g : ℕ → ℝ) (N : ℕ) (h0 : g 0 = 0) :
    ∑ k ∈ Icc 0 N, g k = ∑ k ∈ Icc 1 N, g k := by
  have hI : Icc 0 N = insert 0 (Icc 1 N) := by
    ext k; simp only [mem_Icc, mem_insert]; omega
  rw [hI, sum_insert (by simp), h0, zero_add]

noncomputable def cnt (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ q ∈ Icc 1 ⌊x⌋₊, a q

lemma cnt_real_bound (a : ℕ → ℝ) (c K : ℝ) (m : ℕ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ m)
    (t : ℝ) (ht : 1 ≤ t) :
    |cnt a t - c * t ^ 2| ≤ (K + 2 * c) * t * (1 + Real.log t) ^ m := by
  have hn : 1 ≤ ⌊t⌋₊ := Nat.floor_pos.mpr ht
  have hnR : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hn
  have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hfl2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hlog : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t := Real.log_le_log (by linarith) hfl
  have hlog0 : 0 ≤ Real.log (⌊t⌋₊ : ℝ) := Real.log_nonneg hnR
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hpow : (1 + Real.log (⌊t⌋₊ : ℝ)) ^ m ≤ (1 + Real.log t) ^ m :=
    pow_le_pow_left₀ (by linarith) (by linarith) m
  have hpow1 : 1 ≤ (1 + Real.log t) ^ m := one_le_pow₀ (by linarith)
  have hP0 : 0 ≤ (1 + Real.log (⌊t⌋₊ : ℝ)) ^ m := by positivity
  have h1 := hF ⌊t⌋₊ hn
  have h2 : K * (⌊t⌋₊ : ℝ) * (1 + Real.log (⌊t⌋₊ : ℝ)) ^ m
      ≤ K * t * (1 + Real.log t) ^ m := by
    apply mul_le_mul _ hpow hP0 (by positivity)
    exact mul_le_mul_of_nonneg_left hfl hK
  have h3 : c * (t ^ 2 - (⌊t⌋₊ : ℝ) ^ 2) ≤ 2 * c * t := by
    have : t ^ 2 - (⌊t⌋₊ : ℝ) ^ 2 ≤ 2 * t := by nlinarith
    nlinarith
  have h4 : 0 ≤ c * (t ^ 2 - (⌊t⌋₊ : ℝ) ^ 2) := by
    apply mul_nonneg hc; nlinarith
  have h5 : 2 * c * t ≤ 2 * c * t * (1 + Real.log t) ^ m := by
    have : 0 ≤ 2 * c * t := by positivity
    nlinarith
  have hcnt : cnt a t - c * t ^ 2
      = ((∑ q ∈ Icc 1 ⌊t⌋₊, a q) - c * (⌊t⌋₊ : ℝ) ^ 2) - c * (t ^ 2 - (⌊t⌋₊ : ℝ) ^ 2) := by
    unfold cnt; ring
  rw [hcnt]
  calc |((∑ q ∈ Icc 1 ⌊t⌋₊, a q) - c * (⌊t⌋₊ : ℝ) ^ 2) - c * (t ^ 2 - (⌊t⌋₊ : ℝ) ^ 2)|
      ≤ |(∑ q ∈ Icc 1 ⌊t⌋₊, a q) - c * (⌊t⌋₊ : ℝ) ^ 2| + |c * (t ^ 2 - (⌊t⌋₊ : ℝ) ^ 2)| :=
        abs_sub _ _
    _ ≤ K * t * (1 + Real.log t) ^ m + 2 * c * t * (1 + Real.log t) ^ m := by
        rw [abs_of_nonneg h4]; linarith
    _ = (K + 2 * c) * t * (1 + Real.log t) ^ m := by ring

lemma abel_sum (a : ℕ → ℝ) (f : ℝ → ℝ) (x : ℝ)
    (hf_diff : ∀ t ∈ Set.Icc 1 x, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 1 x)) :
    ∑ k ∈ Icc 1 ⌊x⌋₊, a k * f k
      = f x * cnt a x - ∫ t in Set.Ioc 1 x, deriv f t * cnt a t := by
  set a' : ℕ → ℝ := fun k => if k = 0 then 0 else a k with ha'
  have h0 : a' 0 = 0 := by simp [ha']
  have hS : ∀ N, ∑ k ∈ Icc 0 N, a' k = ∑ k ∈ Icc 1 N, a k := by
    intro N
    rw [sum_Icc_zero_eq_sum_Icc_one a' N h0]
    refine sum_congr rfl fun k hk => ?_
    have : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    simp [ha', this]
  have key := sum_mul_eq_sub_integral_mul₀ a' h0 x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, f k * a' k = ∑ k ∈ Icc 1 ⌊x⌋₊, a k * f k := by
    rw [sum_Icc_zero_eq_sum_Icc_one _ _ (by simp [h0])]
    refine sum_congr rfl fun k hk => ?_
    have : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    simp [ha', this, mul_comm]
  rw [hL] at key
  simp only [hS] at key
  unfold cnt
  exact key

lemma hasDerivAt_log_sq (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.log s ^ 2) (2 * Real.log t * t⁻¹) t := by
  have h : HasDerivAt (fun s : ℝ => Real.log s ^ 2)
      (((2 : ℕ) : ℝ) * Real.log t ^ (2 - 1) * t⁻¹) t := (Real.hasDerivAt_log ht).pow 2
  exact h.congr_deriv (by norm_num)

lemma deriv_log_sq (t : ℝ) (ht : t ≠ 0) :
    deriv (fun s : ℝ => Real.log s ^ 2) t = 2 * Real.log t * t⁻¹ :=
  (hasDerivAt_log_sq t ht).deriv

lemma integral_main1 (c x : ℝ) (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ * (c * t ^ 2) = c * (x ^ 2 - 1) / 2 := by
  rw [← intervalIntegral.integral_of_le hx]
  have : (fun t : ℝ => t⁻¹ * (c * t ^ 2)) = fun t => c * t := by
    funext t
    rcases eq_or_ne t 0 with h | h
    · simp [h]
    · field_simp
  rw [this, intervalIntegral.integral_const_mul, integral_id]; ring

lemma integral_main2 (c x : ℝ) (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, 2 * Real.log t * t⁻¹ * (c * t ^ 2)
      = c * (x ^ 2 * Real.log x - x ^ 2 / 2 + 1 / 2) := by
  rw [← intervalIntegral.integral_of_le hx]
  have : (fun t : ℝ => 2 * Real.log t * t⁻¹ * (c * t ^ 2))
      = fun t => c * (2 * t * Real.log t) := by
    funext t
    rcases eq_or_ne t 0 with h | h
    · simp [h]
    · field_simp
  rw [this, intervalIntegral.integral_const_mul]
  have hFTC : ∫ t in (1:ℝ)..x, 2 * t * Real.log t
      = (x ^ 2 * Real.log x - x ^ 2 / 2) - (1 ^ 2 * Real.log 1 - 1 ^ 2 / 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => t ^ 2 * Real.log t - t ^ 2 / 2)
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have h := ((hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log ht0)).sub
        ((hasDerivAt_pow 2 t).div_const 2)
      exact h.congr_deriv (by field_simp; ring)
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx]
      apply ContinuousOn.mul (by fun_prop)
      exact Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (by linarith [ht.1] : (0:ℝ) < t).ne')
  rw [hFTC]
  simp only [one_pow, Real.log_one, mul_zero, zero_sub]
  ring

/-- **Abel summation for `log`, explicit.**  If `|Σ_{q≤N} a q − c N²| ≤ K N (1+log N)^m` for all
integers `N ≥ 1`, then for every real `x ≥ 1`
`|Σ_{q≤⌊x⌋} a q log q − c x² (log x − 1/2)| ≤ (K + 3c) x (1 + log x)^{m+1}`. -/
theorem sum_log_bound (a : ℕ → ℝ) (c K : ℝ) (m : ℕ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ m)
    (x : ℝ) (hx : 1 ≤ x) :
    |(∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q) - c * x ^ 2 * (Real.log x - 1 / 2)|
      ≤ (K + 3 * c) * x * (1 + Real.log x) ^ (m + 1) := by
  have hE : ∀ t, 1 ≤ t → |cnt a t - c * t ^ 2| ≤ (K + 2 * c) * t * (1 + Real.log t) ^ m :=
    fun t ht => cnt_real_bound a c K m hc hK hF t ht
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hP1 : 1 ≤ (1 + Real.log x) ^ m := one_le_pow₀ (by linarith)
  have hK' : 0 ≤ K + 2 * c := by positivity
  -- Abel summation with `f = log`
  have hdiff : ∀ t ∈ Set.Icc (1:ℝ) x, DifferentiableAt ℝ Real.log t :=
    fun t ht => Real.differentiableAt_log (by linarith [ht.1])
  have hderiv : deriv Real.log = fun t : ℝ => t⁻¹ := funext Real.deriv_log
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Icc (1:ℝ) x) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_inv₀.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (by linarith [ht.1] : (0:ℝ) < t).ne')
  have hint : IntegrableOn (deriv Real.log) (Set.Icc (1:ℝ) x) := by rw [hderiv]; exact hinv
  have habel := abel_sum a Real.log x hdiff hint
  simp only [Real.deriv_log] at habel
  -- integrability of the pieces
  have hint1 : IntegrableOn (fun t : ℝ => t⁻¹ * cnt a t) (Set.Ioc 1 x) := by
    have := integrableOn_mul_sum_Icc a (m := 1) (by norm_num : (0:ℝ) ≤ 1) hinv
    exact this.mono_set Set.Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun t : ℝ => t⁻¹ * (c * t ^ 2)) (Set.Ioc 1 x) := by
    apply IntegrableOn.mono_set _ (Set.Ioc_subset_Icc_self (a := (1:ℝ)) (b := x))
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.mul
    · exact continuousOn_inv₀.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (by linarith [ht.1] : (0:ℝ) < t).ne')
    · fun_prop
  have hint3 : IntegrableOn (fun t : ℝ => t⁻¹ * (cnt a t - c * t ^ 2)) (Set.Ioc 1 x) :=
    (hint1.sub hint2).congr (ae_of_all _ (fun t => by simp only [Pi.sub_apply]; ring))
  have hsplit : ∫ t in Set.Ioc 1 x, t⁻¹ * cnt a t
      = (∫ t in Set.Ioc 1 x, t⁻¹ * (c * t ^ 2))
        + ∫ t in Set.Ioc 1 x, t⁻¹ * (cnt a t - c * t ^ 2) := by
    rw [← integral_add hint2 hint3]
    congr 1; funext t; ring
  have hmain := integral_main1 c x hx
  have herr : |∫ t in Set.Ioc 1 x, t⁻¹ * (cnt a t - c * t ^ 2)|
      ≤ (K + 2 * c) * (1 + Real.log x) ^ m * (x - 1) := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (1:ℝ) x)
      (f := fun t => t⁻¹ * (cnt a t - c * t ^ 2)) (C := (K + 2 * c) * (1 + Real.log x) ^ m)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_
    · rw [Real.volume_real_Ioc, Real.norm_eq_abs, max_eq_left (by linarith)] at hb
      exact hb
    · intro t ht
      have ht1 : 1 < t := ht.1
      have htx : t ≤ x := ht.2
      have ht0 : t ≠ 0 := (by linarith : (0:ℝ) < t).ne'
      have hlogt : Real.log t ≤ Real.log x := Real.log_le_log (by linarith) htx
      have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hpow : (1 + Real.log t) ^ m ≤ (1 + Real.log x) ^ m :=
        pow_le_pow_left₀ (by linarith) (by linarith) m
      rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (by linarith : (0:ℝ) < t)]
      calc t⁻¹ * |cnt a t - c * t ^ 2|
          ≤ t⁻¹ * ((K + 2 * c) * t * (1 + Real.log t) ^ m) := by
            gcongr; exact hE t ht1.le
        _ = (K + 2 * c) * (1 + Real.log t) ^ m := by field_simp
        _ ≤ (K + 2 * c) * (1 + Real.log x) ^ m := by gcongr
  -- assemble
  have hid : (∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q) - c * x ^ 2 * (Real.log x - 1 / 2)
      = Real.log x * (cnt a x - c * x ^ 2) + c / 2
        - ∫ t in Set.Ioc 1 x, t⁻¹ * (cnt a t - c * t ^ 2) := by
    rw [habel, hsplit, hmain]; ring
  rw [hid]
  have hEx := abs_le.mp (hE x hx)
  have hI := abs_le.mp herr
  have e1 := mul_le_mul_of_nonneg_left hEx.2 hL0
  have e1' := mul_le_mul_of_nonneg_left hEx.1 hL0
  have hT1 : 1 ≤ x * (1 + Real.log x) ^ m := by nlinarith
  have e3 : c ≤ c * (x * (1 + Real.log x) ^ m * (1 + Real.log x)) := by
    apply le_mul_of_one_le_right hc
    nlinarith
  have e4 : 0 ≤ (K + 2 * c) * (1 + Real.log x) ^ m := by positivity
  rw [pow_succ (1 + Real.log x) m, abs_le]
  constructor <;> nlinarith

/-- **Abel summation for `log²`, explicit.**  Under the same hypothesis, for real `x ≥ 1`
`|Σ_{q≤⌊x⌋} a q (log q)² − c x² ((log x)² − log x + 1/2)| ≤ (2K + 5c) x (1 + log x)^{m+2}`. -/
theorem sum_logsq_bound (a : ℕ → ℝ) (c K : ℝ) (m : ℕ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ m)
    (x : ℝ) (hx : 1 ≤ x) :
    |(∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q ^ 2)
        - c * x ^ 2 * (Real.log x ^ 2 - Real.log x + 1 / 2)|
      ≤ (2 * K + 5 * c) * x * (1 + Real.log x) ^ (m + 2) := by
  have hE : ∀ t, 1 ≤ t → |cnt a t - c * t ^ 2| ≤ (K + 2 * c) * t * (1 + Real.log t) ^ m :=
    fun t ht => cnt_real_bound a c K m hc hK hF t ht
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hP1 : 1 ≤ (1 + Real.log x) ^ m := one_le_pow₀ (by linarith)
  have hK' : 0 ≤ K + 2 * c := by positivity
  have hne : ∀ t ∈ Set.Icc (1:ℝ) x, t ≠ 0 := fun t ht => (by linarith [ht.1] : (0:ℝ) < t).ne'
  -- Abel summation with `f = log²`
  have hdiff : ∀ t ∈ Set.Icc (1:ℝ) x, DifferentiableAt ℝ (fun s : ℝ => Real.log s ^ 2) t :=
    fun t ht => (hasDerivAt_log_sq t (hne t ht)).differentiableAt
  have hderivOn : Set.EqOn (deriv (fun s : ℝ => Real.log s ^ 2))
      (fun t => 2 * Real.log t * t⁻¹) (Set.Icc 1 x) :=
    fun t ht => deriv_log_sq t (hne t ht)
  have hcontOn : ContinuousOn (fun t : ℝ => 2 * Real.log t * t⁻¹) (Set.Icc 1 x) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul continuousOn_const
      exact Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hne t ht)
    · exact continuousOn_inv₀.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hne t ht)
  have hg : IntegrableOn (fun t : ℝ => 2 * Real.log t * t⁻¹) (Set.Icc (1:ℝ) x) :=
    ContinuousOn.integrableOn_Icc hcontOn
  have hint : IntegrableOn (deriv (fun s : ℝ => Real.log s ^ 2)) (Set.Icc (1:ℝ) x) :=
    ContinuousOn.integrableOn_Icc (hcontOn.congr hderivOn)
  have habel := abel_sum a (fun s : ℝ => Real.log s ^ 2) x hdiff hint
  have hcongr : ∫ t in Set.Ioc 1 x, deriv (fun s : ℝ => Real.log s ^ 2) t * cnt a t
      = ∫ t in Set.Ioc 1 x, 2 * Real.log t * t⁻¹ * cnt a t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    beta_reduce
    rw [deriv_log_sq t (by linarith [ht.1] : (0:ℝ) < t).ne']
  rw [hcongr] at habel
  have hint1 : IntegrableOn (fun t : ℝ => 2 * Real.log t * t⁻¹ * cnt a t) (Set.Ioc 1 x) := by
    have := integrableOn_mul_sum_Icc a (m := 1) (by norm_num : (0:ℝ) ≤ 1) hg
    exact this.mono_set Set.Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun t : ℝ => 2 * Real.log t * t⁻¹ * (c * t ^ 2)) (Set.Ioc 1 x) := by
    apply IntegrableOn.mono_set _ (Set.Ioc_subset_Icc_self (a := (1:ℝ)) (b := x))
    apply ContinuousOn.integrableOn_Icc
    exact hcontOn.mul (by fun_prop)
  have hint3 : IntegrableOn (fun t : ℝ => 2 * Real.log t * t⁻¹ * (cnt a t - c * t ^ 2))
      (Set.Ioc 1 x) :=
    (hint1.sub hint2).congr (ae_of_all _ (fun t => by simp only [Pi.sub_apply]; ring))
  have hsplit : ∫ t in Set.Ioc 1 x, 2 * Real.log t * t⁻¹ * cnt a t
      = (∫ t in Set.Ioc 1 x, 2 * Real.log t * t⁻¹ * (c * t ^ 2))
        + ∫ t in Set.Ioc 1 x, 2 * Real.log t * t⁻¹ * (cnt a t - c * t ^ 2) := by
    rw [← integral_add hint2 hint3]
    congr 1; funext t; ring
  have hmain := integral_main2 c x hx
  have herr : |∫ t in Set.Ioc 1 x, 2 * Real.log t * t⁻¹ * (cnt a t - c * t ^ 2)|
      ≤ 2 * (K + 2 * c) * (1 + Real.log x) ^ (m + 1) * (x - 1) := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (1:ℝ) x)
      (f := fun t => 2 * Real.log t * t⁻¹ * (cnt a t - c * t ^ 2))
      (C := 2 * (K + 2 * c) * (1 + Real.log x) ^ (m + 1))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_
    · rw [Real.volume_real_Ioc, Real.norm_eq_abs, max_eq_left (by linarith)] at hb
      exact hb
    · intro t ht
      have ht1 : 1 < t := ht.1
      have htx : t ≤ x := ht.2
      have ht0 : t ≠ 0 := (by linarith : (0:ℝ) < t).ne'
      have hlogt : Real.log t ≤ Real.log x := Real.log_le_log (by linarith) htx
      have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hpow : (1 + Real.log t) ^ (m + 1) ≤ (1 + Real.log x) ^ (m + 1) :=
        pow_le_pow_left₀ (by linarith) (by linarith) (m + 1)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_inv,
        abs_of_pos (by linarith : (0:ℝ) < t), abs_of_nonneg hlogt0,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      calc 2 * Real.log t * t⁻¹ * |cnt a t - c * t ^ 2|
          ≤ 2 * Real.log t * t⁻¹ * ((K + 2 * c) * t * (1 + Real.log t) ^ m) := by
            gcongr; exact hE t ht1.le
        _ = 2 * (K + 2 * c) * (Real.log t * (1 + Real.log t) ^ m) := by
            field_simp
        _ ≤ 2 * (K + 2 * c) * (1 + Real.log t) ^ (m + 1) := by
            rw [pow_succ]
            have : Real.log t * (1 + Real.log t) ^ m
                ≤ (1 + Real.log t) ^ m * (1 + Real.log t) := by
              nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 + Real.log t) m]
            gcongr
        _ ≤ 2 * (K + 2 * c) * (1 + Real.log x) ^ (m + 1) := by gcongr
  -- assemble
  have hid : (∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q ^ 2)
        - c * x ^ 2 * (Real.log x ^ 2 - Real.log x + 1 / 2)
      = Real.log x ^ 2 * (cnt a x - c * x ^ 2) - c / 2
        - ∫ t in Set.Ioc 1 x, 2 * Real.log t * t⁻¹ * (cnt a t - c * t ^ 2) := by
    rw [habel, hsplit, hmain]; ring
  rw [hid]
  have hEx := abs_le.mp (hE x hx)
  have hI := abs_le.mp herr
  have hL2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hEx.2 hL2
  have e1' := mul_le_mul_of_nonneg_left hEx.1 hL2
  have hT1 : 1 ≤ x * (1 + Real.log x) ^ m := by nlinarith
  have hQ1 : 1 ≤ (1 + Real.log x) ^ 2 := one_le_pow₀ (by linarith)
  have e3 : c ≤ c * (x * (1 + Real.log x) ^ m * (1 + Real.log x) ^ 2) := by
    apply le_mul_of_one_le_right hc
    nlinarith
  have e4 : 0 ≤ (K + 2 * c) * (1 + Real.log x) ^ m := by positivity
  have e5 : 0 ≤ (K + 2 * c) * (1 + Real.log x) ^ m * Real.log x := by positivity
  have e6 : 0 ≤ (K + 2 * c) * (1 + Real.log x) ^ m * Real.log x * x := by positivity
  have e7 : 0 ≤ (K + 2 * c) * (1 + Real.log x) ^ m * Real.log x ^ 2 * x := by positivity
  rw [pow_succ (1 + Real.log x) m] at hI
  rw [pow_add (1 + Real.log x) m 2, abs_le]
  constructor <;> nlinarith


/-! ## Integer-argument corollaries -/

/-- `sum_log_bound` at integer argument `N ≥ 1`. -/
theorem sum_log_bound_nat (a : ℕ → ℝ) (c K : ℝ) (m : ℕ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ m)
    (N : ℕ) (hN : 1 ≤ N) :
    |(∑ q ∈ Icc 1 N, a q * Real.log q) - c * (N : ℝ) ^ 2 * (Real.log N - 1 / 2)|
      ≤ (K + 3 * c) * N * (1 + Real.log N) ^ (m + 1) := by
  have h := sum_log_bound a c K m hc hK hF (N : ℝ) (by exact_mod_cast hN)
  rwa [Nat.floor_natCast] at h

/-- `sum_logsq_bound` at integer argument `N ≥ 1`. -/
theorem sum_logsq_bound_nat (a : ℕ → ℝ) (c K : ℝ) (m : ℕ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ m)
    (N : ℕ) (hN : 1 ≤ N) :
    |(∑ q ∈ Icc 1 N, a q * Real.log q ^ 2)
        - c * (N : ℝ) ^ 2 * (Real.log N ^ 2 - Real.log N + 1 / 2)|
      ≤ (2 * K + 5 * c) * N * (1 + Real.log N) ^ (m + 2) := by
  have h := sum_logsq_bound a c K m hc hK hF (N : ℝ) (by exact_mod_cast hN)
  rwa [Nat.floor_natCast] at h

/-! ## One-term corrections (`Icc 1` versus `Icc 2`) -/

/-- `Σ_{Icc 1 N} g = g 1 + Σ_{Icc 2 N} g` for `N ≥ 1`. -/
lemma sum_Icc_one_eq_add_sum_Icc_two (g : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Icc 1 N, g k = g 1 + ∑ k ∈ Icc 2 N, g k := by
  have hI : Icc 1 N = insert 1 (Icc 2 N) := by
    ext k; simp only [mem_Icc, mem_insert]; omega
  rw [hI, sum_insert (by simp)]

/-- The weighted log-sum does not see `q = 1` (`log 1 = 0`). -/
lemma sum_mul_log_Icc_one_eq_Icc_two (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Icc 1 N, a q * Real.log q = ∑ q ∈ Icc 2 N, a q * Real.log q := by
  rw [sum_Icc_one_eq_add_sum_Icc_two _ N hN]; simp

/-- The weighted log²-sum does not see `q = 1`. -/
lemma sum_mul_logsq_Icc_one_eq_Icc_two (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Icc 1 N, a q * Real.log q ^ 2 = ∑ q ∈ Icc 2 N, a q * Real.log q ^ 2 := by
  rw [sum_Icc_one_eq_add_sum_Icc_two _ N hN]; simp

/-! ## Averages -/

/-- Nonnegativity of the first moment over `Icc k N`, `k ≥ 1`, for nonnegative weights. -/
lemma sum_mul_log_nonneg (a : ℕ → ℝ) (ha : ∀ q, 0 ≤ a q) (k N : ℕ) (hk : 1 ≤ k) :
    0 ≤ ∑ q ∈ Icc k N, a q * Real.log q := by
  apply sum_nonneg
  intro q hq
  have h1 : 1 ≤ q := le_trans hk (mem_Icc.mp hq).1
  exact mul_nonneg (ha q) (Real.log_nonneg (by exact_mod_cast h1))

/-- The trivial bound `Σ a q log q ≤ log x · Σ a q` over `Icc k ⌊x⌋₊`, `k ≥ 1`. -/
lemma sum_mul_log_le (a : ℕ → ℝ) (ha : ∀ q, 0 ≤ a q) (k : ℕ) (hk : 1 ≤ k) (x : ℝ)
    (hx : 0 ≤ x) :
    ∑ q ∈ Icc k ⌊x⌋₊, a q * Real.log q ≤ Real.log x * ∑ q ∈ Icc k ⌊x⌋₊, a q := by
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  have h1 : 1 ≤ q := le_trans hk (mem_Icc.mp hq).1
  have h2 : q ≤ ⌊x⌋₊ := (mem_Icc.mp hq).2
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast h1
  have hqx : (q:ℝ) ≤ x := le_trans (by exact_mod_cast h2) (Nat.floor_le hx)
  rw [mul_comm (Real.log x)]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hqx) (ha q)

/-- **Algebraic core for the averages.** `D` is any denominator (family size) with
`c₀ x² ≤ D` and `|D − c x²| ≤ A₀ x P`; `S₁, S₂` are the two weighted moments with their
main-term bounds; `P` plays the role of `(1 + log x)^m`, `L` of `log x`. Conclusions:
`⟨log q⟩ = L − 1/2 + O(P(1+L)/x)`, `⟨(log q)²⟩ = L² − L + 1/2 + O(P(1+L)²/x)`, and (given
`0 ≤ S₁ ≤ L D`) the variance `⟨(log q)²⟩ − ⟨log q⟩² = 1/4 + O(P(1+L)²/x)`. -/
theorem avg_core (c c₀ A₀ A₁ A₂ D S₁ S₂ L x P : ℝ) (hx : 0 < x) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (hc₀ : 0 < c₀) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hD : c₀ * x ^ 2 ≤ D)
    (h0 : |D - c * x ^ 2| ≤ A₀ * x * P)
    (h1 : |S₁ - c * x ^ 2 * (L - 1 / 2)| ≤ A₁ * x * (P * (1 + L)))
    (h2 : |S₂ - c * x ^ 2 * (L ^ 2 - L + 1 / 2)| ≤ A₂ * x * (P * (1 + L) ^ 2)) :
    |S₁ / D - (L - 1 / 2)| ≤ (A₁ + A₀) / c₀ * (P * (1 + L)) / x ∧
    |S₂ / D - (L ^ 2 - L + 1 / 2)| ≤ (A₂ + A₀) / c₀ * (P * (1 + L) ^ 2) / x ∧
    (0 ≤ S₁ → S₁ ≤ L * D →
      |S₂ / D - (S₁ / D) ^ 2 - 1 / 4|
        ≤ (A₂ + 2 * A₁ + 3 * A₀) / c₀ * (P * (1 + L) ^ 2) / x) := by
  have hx2 : 0 < x ^ 2 := by positivity
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hD0 : D ≠ 0 := hDpos.ne'
  have hc0 : c₀ ≠ 0 := hc₀.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hL1 : |L - 1 / 2| ≤ 1 + L := by rw [abs_le]; constructor <;> linarith
  have hL2 : |L ^ 2 - L + 1 / 2| ≤ (1 + L) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hA0x : 0 ≤ A₀ * x * P := by positivity
  -- numerators
  have k1 : |S₁ - D * (L - 1 / 2)| ≤ (A₁ + A₀) * x * (P * (1 + L)) := by
    have e : S₁ - D * (L - 1 / 2)
        = (S₁ - c * x ^ 2 * (L - 1 / 2)) - (D - c * x ^ 2) * (L - 1 / 2) := by ring
    rw [e]
    calc |(S₁ - c * x ^ 2 * (L - 1 / 2)) - (D - c * x ^ 2) * (L - 1 / 2)|
        ≤ |S₁ - c * x ^ 2 * (L - 1 / 2)| + |(D - c * x ^ 2) * (L - 1 / 2)| := abs_sub _ _
      _ = |S₁ - c * x ^ 2 * (L - 1 / 2)| + |D - c * x ^ 2| * |L - 1 / 2| := by rw [abs_mul]
      _ ≤ A₁ * x * (P * (1 + L)) + (A₀ * x * P) * (1 + L) := by
          have := mul_le_mul h0 hL1 (abs_nonneg _) hA0x
          linarith
      _ = (A₁ + A₀) * x * (P * (1 + L)) := by ring
  have k2 : |S₂ - D * (L ^ 2 - L + 1 / 2)| ≤ (A₂ + A₀) * x * (P * (1 + L) ^ 2) := by
    have e : S₂ - D * (L ^ 2 - L + 1 / 2)
        = (S₂ - c * x ^ 2 * (L ^ 2 - L + 1 / 2)) - (D - c * x ^ 2) * (L ^ 2 - L + 1 / 2) := by
      ring
    rw [e]
    calc |(S₂ - c * x ^ 2 * (L ^ 2 - L + 1 / 2)) - (D - c * x ^ 2) * (L ^ 2 - L + 1 / 2)|
        ≤ |S₂ - c * x ^ 2 * (L ^ 2 - L + 1 / 2)| + |(D - c * x ^ 2) * (L ^ 2 - L + 1 / 2)| :=
          abs_sub _ _
      _ = |S₂ - c * x ^ 2 * (L ^ 2 - L + 1 / 2)| + |D - c * x ^ 2| * |L ^ 2 - L + 1 / 2| := by
          rw [abs_mul]
      _ ≤ A₂ * x * (P * (1 + L) ^ 2) + (A₀ * x * P) * (1 + L) ^ 2 := by
          have := mul_le_mul h0 hL2 (abs_nonneg _) hA0x
          linarith
      _ = (A₂ + A₀) * x * (P * (1 + L) ^ 2) := by ring
  -- divide by `D ≥ c₀ x²`
  have hB1 : 0 ≤ (A₁ + A₀) / c₀ * (P * (1 + L)) / x := by positivity
  have hB2 : 0 ≤ (A₂ + A₀) / c₀ * (P * (1 + L) ^ 2) / x := by positivity
  have d1 : |S₁ / D - (L - 1 / 2)| ≤ (A₁ + A₀) / c₀ * (P * (1 + L)) / x := by
    have e : S₁ / D - (L - 1 / 2) = (S₁ - D * (L - 1 / 2)) / D := by field_simp
    rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    calc |S₁ - D * (L - 1 / 2)| ≤ (A₁ + A₀) * x * (P * (1 + L)) := k1
      _ = (A₁ + A₀) / c₀ * (P * (1 + L)) / x * (c₀ * x ^ 2) := by field_simp
      _ ≤ (A₁ + A₀) / c₀ * (P * (1 + L)) / x * D := mul_le_mul_of_nonneg_left hD hB1
  have d2 : |S₂ / D - (L ^ 2 - L + 1 / 2)| ≤ (A₂ + A₀) / c₀ * (P * (1 + L) ^ 2) / x := by
    have e : S₂ / D - (L ^ 2 - L + 1 / 2) = (S₂ - D * (L ^ 2 - L + 1 / 2)) / D := by field_simp
    rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    calc |S₂ - D * (L ^ 2 - L + 1 / 2)| ≤ (A₂ + A₀) * x * (P * (1 + L) ^ 2) := k2
      _ = (A₂ + A₀) / c₀ * (P * (1 + L) ^ 2) / x * (c₀ * x ^ 2) := by field_simp
      _ ≤ (A₂ + A₀) / c₀ * (P * (1 + L) ^ 2) / x * D := mul_le_mul_of_nonneg_left hD hB2
  refine ⟨d1, d2, fun hS0 hSL => ?_⟩
  -- variance
  have hq0 : 0 ≤ S₁ / D := div_nonneg hS0 hDpos.le
  have hqL : S₁ / D ≤ L := by rw [div_le_iff₀ hDpos]; linarith
  have hw : |S₁ / D + L - 1 / 2| ≤ 2 * (1 + L) := by rw [abs_le]; constructor <;> linarith
  have e : S₂ / D - (S₁ / D) ^ 2 - 1 / 4
      = (S₂ / D - (L ^ 2 - L + 1 / 2)) - (S₁ / D - (L - 1 / 2)) * (S₁ / D + L - 1 / 2) := by
    ring
  rw [e]
  calc |(S₂ / D - (L ^ 2 - L + 1 / 2)) - (S₁ / D - (L - 1 / 2)) * (S₁ / D + L - 1 / 2)|
      ≤ |S₂ / D - (L ^ 2 - L + 1 / 2)| + |(S₁ / D - (L - 1 / 2)) * (S₁ / D + L - 1 / 2)| :=
        abs_sub _ _
    _ = |S₂ / D - (L ^ 2 - L + 1 / 2)| + |S₁ / D - (L - 1 / 2)| * |S₁ / D + L - 1 / 2| := by
        rw [abs_mul]
    _ ≤ (A₂ + A₀) / c₀ * (P * (1 + L) ^ 2) / x
        + ((A₁ + A₀) / c₀ * (P * (1 + L)) / x) * (2 * (1 + L)) := by
        have := mul_le_mul d1 hw (abs_nonneg _) hB1
        linarith
    _ = (A₂ + 2 * A₁ + 3 * A₀) / c₀ * (P * (1 + L) ^ 2) / x := by ring

/-- **The averages over `Icc 1 ⌊x⌋₊`.**  With `F = Σ_{q≤⌊x⌋} a q ≥ c₀ x²`:
`|S₁/F − (log x − 1/2)| ≤ (2K+5c)/c₀ · (1+log x)^{m+1}/x`,
`|S₂/F − ((log x)² − log x + 1/2)| ≤ (3K+7c)/c₀ · (1+log x)^{m+2}/x`, and for nonnegative
weights the variance `|S₂/F − (S₁/F)² − 1/4| ≤ (7K+17c)/c₀ · (1+log x)^{m+2}/x`. -/
theorem avg_bounds (a : ℕ → ℝ) (c K : ℝ) (m : ℕ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ m)
    (x : ℝ) (hx : 1 ≤ x) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hlow : c₀ * x ^ 2 ≤ ∑ q ∈ Icc 1 ⌊x⌋₊, a q) :
    |(∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q) / (∑ q ∈ Icc 1 ⌊x⌋₊, a q) - (Real.log x - 1 / 2)|
        ≤ (2 * K + 5 * c) / c₀ * (1 + Real.log x) ^ (m + 1) / x ∧
    |(∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q ^ 2) / (∑ q ∈ Icc 1 ⌊x⌋₊, a q)
        - (Real.log x ^ 2 - Real.log x + 1 / 2)|
        ≤ (3 * K + 7 * c) / c₀ * (1 + Real.log x) ^ (m + 2) / x ∧
    ((∀ q, 0 ≤ a q) →
      |(∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q ^ 2) / (∑ q ∈ Icc 1 ⌊x⌋₊, a q)
        - ((∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q) / (∑ q ∈ Icc 1 ⌊x⌋₊, a q)) ^ 2 - 1 / 4|
        ≤ (7 * K + 17 * c) / c₀ * (1 + Real.log x) ^ (m + 2) / x) := by
  have h0 : |(∑ q ∈ Icc 1 ⌊x⌋₊, a q) - c * x ^ 2| ≤ (K + 2 * c) * x * (1 + Real.log x) ^ m :=
    cnt_real_bound a c K m hc hK hF x hx
  have h1 := sum_log_bound a c K m hc hK hF x hx
  have h2 := sum_logsq_bound a c K m hc hK hF x hx
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hP0 : 0 ≤ (1 + Real.log x) ^ m := by positivity
  rw [pow_succ (1 + Real.log x) m] at h1
  rw [pow_add (1 + Real.log x) m 2] at h2
  obtain ⟨d1, d2, d3⟩ := avg_core c c₀ (K + 2 * c) (K + 3 * c) (2 * K + 5 * c)
    (∑ q ∈ Icc 1 ⌊x⌋₊, a q) (∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q)
    (∑ q ∈ Icc 1 ⌊x⌋₊, a q * Real.log q ^ 2) (Real.log x) x ((1 + Real.log x) ^ m)
    (by linarith) hL0 hP0 hc₀ (by linarith) (by linarith) (by linarith) hlow h0 h1 h2
  rw [pow_succ (1 + Real.log x) m, pow_add (1 + Real.log x) m 2]
  refine ⟨?_, ?_, fun ha => ?_⟩
  · have e : (2 * K + 5 * c) = (K + 3 * c) + (K + 2 * c) := by ring
    rw [e]; exact d1
  · have e : (3 * K + 7 * c) = (2 * K + 5 * c) + (K + 2 * c) := by ring
    rw [e]; exact d2
  · have d3' := d3 (sum_mul_log_nonneg a ha 1 _ le_rfl)
      (sum_mul_log_le a ha 1 le_rfl x (by linarith))
    have e : (7 * K + 17 * c) = (2 * K + 5 * c) + 2 * (K + 3 * c) + 3 * (K + 2 * c) := by ring
    rw [e]; exact d3'

/-- **The averages over `Icc 2 ⌊x⌋₊`** (the tree's family excludes `q = 1`).  Same shape, with
the one-term correction `a 1` entering the constants. -/
theorem avg_bounds_Icc2 (a : ℕ → ℝ) (c K : ℝ) (m : ℕ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ m)
    (ha : ∀ q, 0 ≤ a q)
    (x : ℝ) (hx : 1 ≤ x) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hlow : c₀ * x ^ 2 ≤ ∑ q ∈ Icc 2 ⌊x⌋₊, a q) :
    |(∑ q ∈ Icc 2 ⌊x⌋₊, a q * Real.log q) / (∑ q ∈ Icc 2 ⌊x⌋₊, a q) - (Real.log x - 1 / 2)|
        ≤ (2 * K + 5 * c + a 1) / c₀ * (1 + Real.log x) ^ (m + 1) / x ∧
    |(∑ q ∈ Icc 2 ⌊x⌋₊, a q * Real.log q ^ 2) / (∑ q ∈ Icc 2 ⌊x⌋₊, a q)
        - (Real.log x ^ 2 - Real.log x + 1 / 2)|
        ≤ (3 * K + 7 * c + a 1) / c₀ * (1 + Real.log x) ^ (m + 2) / x ∧
    |(∑ q ∈ Icc 2 ⌊x⌋₊, a q * Real.log q ^ 2) / (∑ q ∈ Icc 2 ⌊x⌋₊, a q)
        - ((∑ q ∈ Icc 2 ⌊x⌋₊, a q * Real.log q) / (∑ q ∈ Icc 2 ⌊x⌋₊, a q)) ^ 2 - 1 / 4|
        ≤ (7 * K + 17 * c + 3 * a 1) / c₀ * (1 + Real.log x) ^ (m + 2) / x := by
  have hn : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.mpr hx
  have h0 : |(∑ q ∈ Icc 1 ⌊x⌋₊, a q) - c * x ^ 2| ≤ (K + 2 * c) * x * (1 + Real.log x) ^ m :=
    cnt_real_bound a c K m hc hK hF x hx
  have h1 := sum_log_bound a c K m hc hK hF x hx
  have h2 := sum_logsq_bound a c K m hc hK hF x hx
  rw [sum_mul_log_Icc_one_eq_Icc_two a _ hn] at h1
  rw [sum_mul_logsq_Icc_one_eq_Icc_two a _ hn] at h2
  have hD : ∑ q ∈ Icc 1 ⌊x⌋₊, a q = a 1 + ∑ q ∈ Icc 2 ⌊x⌋₊, a q :=
    sum_Icc_one_eq_add_sum_Icc_two a _ hn
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hP0 : 0 ≤ (1 + Real.log x) ^ m := by positivity
  have hP1 : 1 ≤ (1 + Real.log x) ^ m := one_le_pow₀ (by linarith)
  have ha1 := ha 1
  have h0' : |(∑ q ∈ Icc 2 ⌊x⌋₊, a q) - c * x ^ 2|
      ≤ (K + 2 * c + a 1) * x * (1 + Real.log x) ^ m := by
    have hxP : 1 ≤ x * (1 + Real.log x) ^ m := by nlinarith
    have e : (∑ q ∈ Icc 2 ⌊x⌋₊, a q) - c * x ^ 2
        = ((∑ q ∈ Icc 1 ⌊x⌋₊, a q) - c * x ^ 2) - a 1 := by rw [hD]; ring
    rw [e]
    calc |((∑ q ∈ Icc 1 ⌊x⌋₊, a q) - c * x ^ 2) - a 1|
        ≤ |(∑ q ∈ Icc 1 ⌊x⌋₊, a q) - c * x ^ 2| + |a 1| := abs_sub _ _
      _ ≤ (K + 2 * c) * x * (1 + Real.log x) ^ m + a 1 * (x * (1 + Real.log x) ^ m) := by
          rw [abs_of_nonneg ha1]
          have : a 1 ≤ a 1 * (x * (1 + Real.log x) ^ m) := le_mul_of_one_le_right ha1 hxP
          linarith
      _ = (K + 2 * c + a 1) * x * (1 + Real.log x) ^ m := by ring
  rw [pow_succ (1 + Real.log x) m] at h1
  rw [pow_add (1 + Real.log x) m 2] at h2
  obtain ⟨d1, d2, d3⟩ := avg_core c c₀ (K + 2 * c + a 1) (K + 3 * c) (2 * K + 5 * c)
    (∑ q ∈ Icc 2 ⌊x⌋₊, a q) (∑ q ∈ Icc 2 ⌊x⌋₊, a q * Real.log q)
    (∑ q ∈ Icc 2 ⌊x⌋₊, a q * Real.log q ^ 2) (Real.log x) x ((1 + Real.log x) ^ m)
    (by linarith) hL0 hP0 hc₀ (by linarith) (by linarith) (by linarith) hlow h0' h1 h2
  have d3' := d3 (sum_mul_log_nonneg a ha 2 _ (by norm_num))
    (sum_mul_log_le a ha 2 (by norm_num) x (by linarith))
  rw [pow_succ (1 + Real.log x) m, pow_add (1 + Real.log x) m 2]
  refine ⟨?_, ?_, ?_⟩
  · have e : (2 * K + 5 * c + a 1) = (K + 3 * c) + (K + 2 * c + a 1) := by ring
    rw [e]; exact d1
  · have e : (3 * K + 7 * c + a 1) = (2 * K + 5 * c) + (K + 2 * c + a 1) := by ring
    rw [e]; exact d2
  · have e : (7 * K + 17 * c + 3 * a 1)
        = (2 * K + 5 * c) + 2 * (K + 3 * c) + 3 * (K + 2 * c + a 1) := by ring
    rw [e]; exact d3'

/-! ## Explicit lower bounds for the count (so that `c₀` and `x₀'` are explicit) -/

/-- From the two-sided bound: as soon as `2(K + 2c)(1 + log x)^m ≤ c x`, the count is at least
`(c/2) x²`. -/
lemma cnt_lower_of (a : ℕ → ℝ) (c K : ℝ) (m : ℕ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ m)
    (x : ℝ) (hx : 1 ≤ x) (hbig : 2 * (K + 2 * c) * (1 + Real.log x) ^ m ≤ c * x) :
    c / 2 * x ^ 2 ≤ ∑ q ∈ Icc 1 ⌊x⌋₊, a q := by
  have h0 : |(∑ q ∈ Icc 1 ⌊x⌋₊, a q) - c * x ^ 2| ≤ (K + 2 * c) * x * (1 + Real.log x) ^ m :=
    cnt_real_bound a c K m hc hK hF x hx
  have h := (abs_le.mp h0).1
  have : (K + 2 * c) * x * (1 + Real.log x) ^ m ≤ c / 2 * x ^ 2 := by
    have hx0 : 0 ≤ x := by linarith
    nlinarith
  linarith

/-- `(1 + log x)² ≤ 16 √x` for `x ≥ 1` (via `log x = 4 log x^{1/4} ≤ 4 (x^{1/4} − 1)`). -/
lemma one_add_log_sq_le_sqrt (x : ℝ) (hx : 1 ≤ x) : (1 + Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
  set y := Real.sqrt (Real.sqrt x) with hy
  have hsx : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr hsx
  have hy2 : y ^ 2 = Real.sqrt x := Real.sq_sqrt (by linarith)
  have hy4 : (y ^ 2) ^ 2 = x := by rw [hy2]; exact Real.sq_sqrt (by linarith)
  have hlog : Real.log x = 4 * Real.log y := by
    rw [← hy4, Real.log_pow, Real.log_pow]; push_cast; ring
  have hly : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : 1 + Real.log x ≤ 4 * y := by rw [hlog]; linarith
  have h2 : (1 + Real.log x) ^ 2 ≤ (4 * y) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  calc (1 + Real.log x) ^ 2 ≤ (4 * y) ^ 2 := h2
    _ = 16 * y ^ 2 := by ring
    _ = 16 * Real.sqrt x := by rw [hy2]

/-- **Explicit threshold for `m = 2`.** If `(32 (K + 2c)/c)² ≤ x` then `(c/2) x² ≤ Σ_{q≤⌊x⌋} a q`.
(For the tree's `c = 18/π⁴`, `K = 5` this is `x ≥ 8.7·10⁵`; the true threshold is near `5.5·10³`.) -/
lemma cnt_lower_explicit_m2 (a : ℕ → ℝ) (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ 2)
    (x : ℝ) (hx0 : (32 * (K + 2 * c) / c) ^ 2 ≤ x) :
    c / 2 * x ^ 2 ≤ ∑ q ∈ Icc 1 ⌊x⌋₊, a q := by
  have hr : 2 ≤ (K + 2 * c) / c := by
    rw [le_div_iff₀ hc]; linarith
  have hr' : 64 ≤ 32 * (K + 2 * c) / c := by
    rw [mul_div_assoc]; linarith
  have hx : 1 ≤ x := by nlinarith
  apply cnt_lower_of a c K 2 hc.le hK hF x hx
  have hs : 32 * (K + 2 * c) / c ≤ Real.sqrt x :=
    Real.le_sqrt (by linarith) (by linarith) |>.mpr hx0
  have hs' : 32 * (K + 2 * c) ≤ c * Real.sqrt x := by
    rw [div_le_iff₀ hc] at hs; linarith
  have hsq := one_add_log_sq_le_sqrt x hx
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hK2 : 0 ≤ K + 2 * c := by linarith
  calc 2 * (K + 2 * c) * (1 + Real.log x) ^ 2
      ≤ 2 * (K + 2 * c) * (16 * Real.sqrt x) := by gcongr
    _ = (32 * (K + 2 * c)) * Real.sqrt x := by ring
    _ ≤ (c * Real.sqrt x) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs' (Real.sqrt_nonneg x)
    _ = c * x := by rw [mul_assoc, ← sq, hsx]

/-- The `Icc 2` count from below, explicit (`m = 2`): `(c/4) x² ≤ Σ_{2≤q≤⌊x⌋} a q` once
`(32(K+2c)/c)² ≤ x` and `4 a 1 ≤ c x²`. -/
lemma cnt2_lower_explicit_m2 (a : ℕ → ℝ) (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (hF : ∀ N : ℕ, 1 ≤ N →
      |(∑ q ∈ Icc 1 N, a q) - c * (N : ℝ) ^ 2| ≤ K * N * (1 + Real.log N) ^ 2)
    (x : ℝ) (hx0 : (32 * (K + 2 * c) / c) ^ 2 ≤ x) (ha1 : 4 * a 1 ≤ c * x ^ 2) :
    c / 4 * x ^ 2 ≤ ∑ q ∈ Icc 2 ⌊x⌋₊, a q := by
  have h := cnt_lower_explicit_m2 a c K hc hK hF x hx0
  have hr : 2 ≤ (K + 2 * c) / c := by
    rw [le_div_iff₀ hc]; linarith
  have hr' : 64 ≤ 32 * (K + 2 * c) / c := by
    rw [mul_div_assoc]; linarith
  have hx : 1 ≤ x := by nlinarith
  have hn : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.mpr hx
  rw [sum_Icc_one_eq_add_sum_Icc_two a _ hn] at h
  linarith

end ZetaQ.AbelLogPow
