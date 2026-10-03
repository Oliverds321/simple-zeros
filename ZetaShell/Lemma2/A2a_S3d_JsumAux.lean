/-
A2a_S3d_JsumAux (L7_8, round 4): elementary estimates for `s3_arith_jsum`.
* `sum_inv_sqrt_le`: `Σ_{1≤m≤N} 1/√m ≤ 2√N`;
* `one_add_log_sq_le`: `(1 + log t)² ≤ 25√t` for `t ≥ 1`;
* `divisor_swap`: `Σ_{n≤N} Σ_{d|n} G(d,n) = Σ_{d≤N} Σ_{m≤N/d} G(d, dm)`;
* `sum_harmonic_le`: `Σ_{1≤d≤N} 1/d ≤ 1 + log N`;
* `sum_tau_inv_sqrt_le`: `Σ_{n≤N} τ(n)/√n ≤ 2√N(1 + log N)`.
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem sum_inv_sqrt_le (N : ℕ) : ∑ m ∈ Finset.Icc 1 N, 1 / Real.sqrt m ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha := Real.sqrt_nonneg (n : ℝ)
    have hb : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have ha2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    push_cast at hb2 ⊢
    have key : 1 / Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt ((n : ℝ) + 1) - 2 * Real.sqrt n := by
      rw [div_le_iff₀ (by simpa using hb)]
      have : 2 * Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (n : ℝ) ^ 2 + Real.sqrt ((n : ℝ) + 1) ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - Real.sqrt ((n : ℝ) + 1))]
      nlinarith
    linarith

theorem one_add_log_sq_le (t : ℝ) (ht : 1 ≤ t) : (1 + Real.log t) ^ 2 ≤ 25 * Real.sqrt t := by
  have ht0 : 0 ≤ t := by linarith
  have hlog := Real.log_le_rpow_div ht0 (show (0 : ℝ) < 1 / 4 by norm_num)
  set u := t ^ (1 / 4 : ℝ) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow ht (by norm_num)
  have hsq : Real.sqrt t = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0, Real.sqrt_eq_rpow]; norm_num
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 : 1 + Real.log t ≤ 5 * u := by
    have : Real.log t ≤ 4 * u := by rw [div_eq_mul_inv] at hlog; norm_num at hlog; linarith
    linarith
  rw [hsq]
  nlinarith

theorem divisor_swap (G : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, G d n = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), G d (d * m) := by
  rw [Finset.sum_comm' (t' := Finset.Icc 1 N) (s' := fun d => (Finset.Icc 1 N).filter (fun n => d ∣ n))]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    symm
    apply Finset.sum_nbij' (fun m => d * m) (fun n => n / d)
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith [hm.1], ?_⟩, dvd_mul_right d m⟩
      have := Nat.mul_le_of_le_div d m N hm.2
      linarith [this, Nat.mul_comm m d]
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      obtain ⟨⟨hn1, hnN⟩, hdn⟩ := hn
      obtain ⟨c, rfl⟩ := hdn
      rw [Nat.mul_div_cancel_left c (by omega)]
      constructor
      · rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at hn1
        · exact h
      · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hnN)
    · intro m _
      exact Nat.mul_div_cancel_left m (by omega)
    · intro n hn
      rw [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      rfl
  · intro n d
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdn, _⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
      have hdN : d ≤ N := le_trans (Nat.le_of_dvd (by omega) hdn) hnN
      exact ⟨⟨⟨hn1, hnN⟩, hdn⟩, hd1, hdN⟩
    · rintro ⟨⟨⟨hn1, hnN⟩, hdn⟩, _, _⟩
      exact ⟨⟨hn1, hnN⟩, hdn, by omega⟩

theorem sum_harmonic_le (N : ℕ) : ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  have : ((∑ i ∈ Finset.Icc 1 N, ((i : ℚ))⁻¹ : ℚ) : ℝ) = ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
    push_cast; apply Finset.sum_congr rfl; intro d _; rw [one_div]
  rw [← this]; exact h

theorem sum_tau_inv_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) / Real.sqrt n ≤ 2 * Real.sqrt N * (1 + Real.log N) := by
  have e1 : ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) / Real.sqrt n
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, 1 / Real.sqrt n := by
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [e1, divisor_swap (fun d n => 1 / Real.sqrt n) N]
  have hterm : ∀ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt ((d * m : ℕ) : ℝ)
      ≤ 2 * Real.sqrt N * (1 / (d : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
    have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
    have e2 : ∑ m ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt ((d * m : ℕ) : ℝ)
        = (1 / Real.sqrt d) * ∑ m ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt m := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
      push_cast; rw [Real.sqrt_mul hdR.le]; field_simp
    rw [e2]
    have h1 := sum_inv_sqrt_le (N / d)
    have h2 : Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt d := by
      rw [← Real.sqrt_div' _ hdR.le] ; apply Real.sqrt_le_sqrt
      rw [le_div_iff₀ hdR]
      have : (N / d) * d ≤ N := Nat.div_mul_le_self N d
      exact_mod_cast this
    calc (1 / Real.sqrt d) * ∑ m ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt m
        ≤ (1 / Real.sqrt d) * (2 * (Real.sqrt N / Real.sqrt d)) := by
          apply mul_le_mul_of_nonneg_left (le_trans h1 (by linarith)) (by positivity)
      _ = 2 * Real.sqrt N * (1 / (d : ℝ)) := by
          have hdd : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt hdR.le
          have e3 : (1 / Real.sqrt d) * (2 * (Real.sqrt N / Real.sqrt d))
              = 2 * Real.sqrt N / (Real.sqrt d * Real.sqrt d) := by
            field_simp
          rw [e3, hdd]
          ring
  calc ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt ((d * m : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 N, 2 * Real.sqrt N * (1 / (d : ℝ)) := Finset.sum_le_sum hterm
    _ = 2 * Real.sqrt N * ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.sqrt N * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left (sum_harmonic_le N) (by positivity)

end TrackF
end ZetaShell
