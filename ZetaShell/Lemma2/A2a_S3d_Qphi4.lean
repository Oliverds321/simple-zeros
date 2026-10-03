/-
A2a_S3d_Qphi4 (L7_8, round 5): the weighted-family divisor sum with the exponent 4 (route (b) of the lead's
round-5 message): `Σ_{1≤e≤y} |c_e| τ(e) ≤ (1 + log y)⁴` for both kinds (`ce_tau_le4`).
q/φ kind: `|c_e| ≤ 1/φ(e) ≤ 2^{ω(e)}/e ≤ τ(e)/e`, `τ(e)² ≤ Σ_{d|e} τ(d)τ(e/d)` (`τ(ab) ≤ τ(a)τ(b)`), and
`Σ_{e≤N} Σ_{d|e} τ(d)τ(e/d)/e ≤ (Σ_{d≤N} τ(d)/d)² ≤ (1 + log N)⁴`.
-/
import ZetaShell.Skeleton.A2a_S3d_CeTau

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem tau_mul_le (a b : ℕ) : ((a * b).divisors.card : ℝ) ≤ (a.divisors.card : ℝ) * (b.divisors.card : ℝ) := by
  rw [Nat.divisors_mul]
  exact_mod_cast Finset.card_mul_le

theorem e_le_two_pow_mul_totient (e : ℕ) (he : e ≠ 0) :
    (e : ℝ) ≤ (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors e) * (Nat.totient e : ℝ) := by
  rw [omega_eq_card_primeFactors]
  have h := Nat.totient_mul_prod_primeFactors e
  have hle : ∏ p ∈ e.primeFactors, p ≤ ∏ p ∈ e.primeFactors, (2 * (p - 1)) := by
    apply Finset.prod_le_prod'
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hle
  have hpos : 0 < ∏ p ∈ e.primeFactors, (p - 1) := Finset.prod_pos (fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
  have hkey : e * ∏ p ∈ e.primeFactors, (p - 1) ≤ (2 ^ e.primeFactors.card * Nat.totient e) *
      ∏ p ∈ e.primeFactors, (p - 1) := by
    rw [← h]
    calc Nat.totient e * ∏ p ∈ e.primeFactors, p
        ≤ Nat.totient e * (2 ^ e.primeFactors.card * ∏ p ∈ e.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ hle
      _ = (2 ^ e.primeFactors.card * Nat.totient e) * ∏ p ∈ e.primeFactors, (p - 1) := by ring
  have := Nat.le_of_mul_le_mul_right hkey hpos
  exact_mod_cast this

theorem tau_sq_le_conv (e : ℕ) (he : 1 ≤ e) :
    (e.divisors.card : ℝ) ^ 2 ≤ ∑ d ∈ e.divisors, (d.divisors.card : ℝ) * ((e / d).divisors.card : ℝ) := by
  have h : ∀ d ∈ e.divisors, (e.divisors.card : ℝ) ≤ (d.divisors.card : ℝ) * ((e / d).divisors.card : ℝ) := by
    intro d hd
    have hde : d * (e / d) = e := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have := tau_mul_le d (e / d)
    rwa [hde] at this
  have := Finset.card_nsmul_le_sum _ _ _ h
  rw [nsmul_eq_mul] at this
  nlinarith [this]

theorem sum_tau_div_le (N : ℕ) : ∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ) / e ≤ (1 + Real.log N) ^ 2 := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have e1 : ∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ) / e = ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ e.divisors, 1 / (e : ℝ) := by
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [e1, divisor_swap (fun _ e => 1 / (e : ℝ)) N]
  calc ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), 1 / ((d * m : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 N, (1 / (d : ℝ)) * (1 + Real.log N) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have e2 : ∑ m ∈ Finset.Icc 1 (N / d), 1 / ((d * m : ℕ) : ℝ)
            = (1 / (d : ℝ)) * ∑ m ∈ Finset.Icc 1 (N / d), 1 / (m : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
          push_cast; rw [one_div_mul_one_div]
        rw [e2]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine le_trans (sum_harmonic_le (N / d)) ?_
        have hNd : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
        rcases Nat.eq_zero_or_pos (N / d) with h0 | hpos
        · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
        · have := Real.log_le_log (by exact_mod_cast hpos) hNd; linarith
    _ = (∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ)) * (1 + Real.log N) := by rw [Finset.sum_mul]
    _ ≤ (1 + Real.log N) * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_right (sum_harmonic_le N) (by linarith)
    _ = (1 + Real.log N) ^ 2 := by ring

theorem ce_tau_le_qphi4 (y : ℝ) (hy : 1 ≤ y) :
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |cE FKind.qphi e| * (e.divisors.card : ℝ) ≤ (1 + Real.log y) ^ 4 := by
  set N := ⌊y⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hy)
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hlogN : Real.log N ≤ Real.log y := Real.log_le_log (by exact_mod_cast hN1) hNy
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  -- termwise bound
  have hterm : ∀ e ∈ Finset.Icc 1 N, |cE FKind.qphi e| * (e.divisors.card : ℝ)
      ≤ (∑ d ∈ e.divisors, (d.divisors.card : ℝ) * ((e / d).divisors.card : ℝ)) / e := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heR : (0 : ℝ) < e := by exact_mod_cast he1
    have hphi : (0 : ℝ) < Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hτ : (0 : ℝ) ≤ (e.divisors.card : ℝ) := by positivity
    simp only [cE]
    rw [abs_div, abs_of_pos hphi]
    have hmu : |((ArithmeticFunction.moebius e : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h1 : 1 / (Nat.totient e : ℝ) ≤ (e.divisors.card : ℝ) / e := by
      rw [div_le_div_iff₀ hphi heR, one_mul]
      calc (e : ℝ) ≤ (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors e) * (Nat.totient e : ℝ) :=
            e_le_two_pow_mul_totient e (by omega)
        _ ≤ (e.divisors.card : ℝ) * (Nat.totient e : ℝ) :=
            mul_le_mul_of_nonneg_right (two_pow_omega_le_tau e (by omega)) hphi.le
    calc |((ArithmeticFunction.moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) * (e.divisors.card : ℝ)
        ≤ (1 / (Nat.totient e : ℝ)) * (e.divisors.card : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hτ
          exact div_le_div_of_nonneg_right hmu hphi.le
      _ ≤ ((e.divisors.card : ℝ) / e) * (e.divisors.card : ℝ) := mul_le_mul_of_nonneg_right h1 hτ
      _ = (e.divisors.card : ℝ) ^ 2 / e := by ring
      _ ≤ (∑ d ∈ e.divisors, (d.divisors.card : ℝ) * ((e / d).divisors.card : ℝ)) / e :=
          div_le_div_of_nonneg_right (tau_sq_le_conv e he1) heR.le
  calc ∑ e ∈ Finset.Icc 1 N, |cE FKind.qphi e| * (e.divisors.card : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1 N, (∑ d ∈ e.divisors, (d.divisors.card : ℝ) * ((e / d).divisors.card : ℝ)) / e :=
        Finset.sum_le_sum hterm
    _ = ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ e.divisors,
          (d.divisors.card : ℝ) * ((e / d).divisors.card : ℝ) / e := by
        apply Finset.sum_congr rfl; intro e _; rw [Finset.sum_div]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
          (d.divisors.card : ℝ) * (((d * m) / d).divisors.card : ℝ) / ((d * m : ℕ) : ℝ) :=
        divisor_swap (fun d e => (d.divisors.card : ℝ) * ((e / d).divisors.card : ℝ) / e) N
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ((d.divisors.card : ℝ) / d) * (1 + Real.log N) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
        have e2 : ∑ m ∈ Finset.Icc 1 (N / d), (d.divisors.card : ℝ) * (((d * m) / d).divisors.card : ℝ) /
              ((d * m : ℕ) : ℝ)
            = ((d.divisors.card : ℝ) / d) * ∑ m ∈ Finset.Icc 1 (N / d), (m.divisors.card : ℝ) / m := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
          rw [Nat.mul_div_cancel_left m (by omega)]
          push_cast
          field_simp
        rw [e2]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine le_trans (sum_tau_div_le (N / d)) ?_
        have hNd : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
        rcases Nat.eq_zero_or_pos (N / d) with h0 | hpos
        · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; nlinarith
        · have := Real.log_le_log (by exact_mod_cast hpos) hNd
          have h0' : 0 ≤ Real.log ((N / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hpos)
          nlinarith
    _ = (∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) / d) * (1 + Real.log N) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (1 + Real.log N) ^ 2 * (1 + Real.log N) ^ 2 :=
        mul_le_mul_of_nonneg_right (sum_tau_div_le N) (by positivity)
    _ ≤ (1 + Real.log y) ^ 4 := by
        have h1 : (1 + Real.log N) ^ 2 ≤ (1 + Real.log y) ^ 2 := by nlinarith
        nlinarith [sq_nonneg (1 + Real.log N)]

theorem ce_tau_le4 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : FKind) (y : ℝ), 1 ≤ y →
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |cE k e| * (e.divisors.card : ℝ) ≤ C * (1 + Real.log y) ^ 4 := by
  refine ⟨1, zero_le_one, ?_⟩
  intro k y hy
  have hl : 1 ≤ 1 + Real.log y := by have := Real.log_nonneg hy; linarith
  cases k
  · refine le_trans (ce_tau_le_plain y hy) ?_
    have : (1 + Real.log y) ^ 2 ≤ (1 + Real.log y) ^ 4 := pow_le_pow_right₀ hl (by norm_num)
    linarith
  · rw [one_mul]; exact ce_tau_le_qphi4 y hy

end TrackF
end ZetaShell
