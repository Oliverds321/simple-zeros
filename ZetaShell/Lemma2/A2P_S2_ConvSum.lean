/-
A2P_S2_ConvSum (L7_8, 28 Sep 2026): the algebraic backbone of **step (ii) of the proof of Lemma P**
(sec_shell.tex l.368–369), sorry-free: "From `Σ_{m≤x} m = x²/2 + ϑx`, `Σ_{j≤y} j b(j) = (y²/2)Σ_f ν_e(f)/f + O(…)`"
with `b = 1 * ν_e`.

Proved:
* `sum_mul_divisors_swap`: `Σ_{j≤N} j Σ_{f|j} ν(f) = Σ_{f≤N} ν(f) f Σ_{m≤N/f} m` (exact, any `ν`);
* `triangular_bound`: `|Σ_{1≤m≤⌊x⌋} m − x²/2| ≤ x` for real `x ≥ 0` (the draft's `ϑx`).
Together: `Σ_{j≤N} j b(j) = (N²/2)Σ_{f≤N} ν(f)/f + ϑ N Σ_{f≤N}|ν(f)|`, `|ϑ| ≤ 1` (`sum_mul_conv_approx`).
What remains of step (ii) is analytic: `Σ_{f≤y}|ν_e(f)| ≪ 2^{ω(e)}(1+log y)²` and the tail `Σ_{f>y}|ν_e(f)|/f`.
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem sum_mul_divisors_swap (ν : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∑ f ∈ j.divisors, ν f
      = ∑ f ∈ Finset.Icc 1 N, ν f * (f : ℝ) * ∑ m ∈ Finset.Icc 1 (N / f), (m : ℝ) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 N) (s' := fun f => (Finset.Icc 1 N).filter (fun j => f ∣ j))]
  · apply Finset.sum_congr rfl
    intro f hf
    have hf1 : 1 ≤ f := (Finset.mem_Icc.mp hf).1
    -- Σ_{j ≤ N, f | j} j ν f = Σ_{m ≤ N/f} ν f f m
    symm
    apply Finset.sum_nbij' (fun m => f * m) (fun j => j / f)
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith [hm.1], ?_⟩, dvd_mul_right f m⟩
      have := Nat.mul_le_of_le_div f m N hm.2
      linarith [this, Nat.mul_comm m f]
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]
      obtain ⟨⟨hj1, hjN⟩, hfj⟩ := hj
      obtain ⟨c, rfl⟩ := hfj
      rw [Nat.mul_div_cancel_left c (by omega)]
      constructor
      · rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at hj1
        · exact h
      · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hjN)
    · intro m _
      exact Nat.mul_div_cancel_left m (by omega)
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact Nat.mul_div_cancel' hj.2
    · intro m _
      push_cast
      ring
  · intro j f
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hj1, hjN⟩, hfj, _⟩
      have hf1 : 1 ≤ f := Nat.pos_of_dvd_of_pos hfj (by omega)
      have hfN : f ≤ N := le_trans (Nat.le_of_dvd (by omega) hfj) hjN
      exact ⟨⟨⟨hj1, hjN⟩, hfj⟩, hf1, hfN⟩
    · rintro ⟨⟨⟨hj1, hjN⟩, hfj⟩, _, _⟩
      exact ⟨⟨hj1, hjN⟩, hfj, by omega⟩

theorem triangular_bound (x : ℝ) (hx : 0 ≤ x) :
    |∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (m : ℝ) - x ^ 2 / 2| ≤ x := by
  set n := ⌊x⌋₊ with hn
  have hsum : ∑ m ∈ Finset.Icc 1 n, (m : ℝ) = (n : ℝ) * (n + 1) / 2 := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  rw [hsum]
  have h1 : (n : ℝ) ≤ x := Nat.floor_le hx
  have h2 : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_le]
  constructor <;> nlinarith

/-- **Step (ii) of Lemma P, exact form.** `|Σ_{j≤N} j (1*ν)(j) − (N²/2) Σ_{f≤N} ν(f)/f| ≤ N Σ_{f≤N} |ν(f)|`. -/
theorem sum_mul_conv_approx (ν : ℕ → ℝ) (N : ℕ) :
    |∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∑ f ∈ j.divisors, ν f
        - (N : ℝ) ^ 2 / 2 * ∑ f ∈ Finset.Icc 1 N, ν f / f|
      ≤ (N : ℝ) * ∑ f ∈ Finset.Icc 1 N, |ν f| := by
  rw [sum_mul_divisors_swap, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun f hf => ?_))
  have hf1 : 1 ≤ f := (Finset.mem_Icc.mp hf).1
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf1
  have hx : (0 : ℝ) ≤ (N : ℝ) / f := by positivity
  have hT := triangular_bound ((N : ℝ) / f) hx
  rw [Nat.floor_div_eq_div] at hT
  have e : ν f * (f : ℝ) * ∑ m ∈ Finset.Icc 1 (N / f), (m : ℝ) - (N : ℝ) ^ 2 / 2 * (ν f / f)
      = ν f * (f : ℝ) * (∑ m ∈ Finset.Icc 1 (N / f), (m : ℝ) - ((N : ℝ) / f) ^ 2 / 2) := by
    field_simp
  rw [e, abs_mul, abs_mul, abs_of_pos hfR]
  calc |ν f| * f * |∑ m ∈ Finset.Icc 1 (N / f), (m : ℝ) - ((N : ℝ) / f) ^ 2 / 2|
      ≤ |ν f| * f * ((N : ℝ) / f) := by
        apply mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (N : ℝ) * |ν f| := by field_simp

end TrackF
end ZetaShell
