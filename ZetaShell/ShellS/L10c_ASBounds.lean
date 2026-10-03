/-
L10c_ASBounds (L7_10c, 3 Oct 2026): the size bounds of the AS assembly at one point `(Q, s)`, every asymptotic input a
hypothesis: the bracket of Lemma 2(a) at `K = ℒ(log ℒ)²`, `ε = 1/ℒ` (`≤ 67 log ℒ/ℒ`), `‖b‖² ≤ U(s + 2)` (PNT on
the window), the complements `‖a − b‖², ‖aPrime − b‖² ≤ (C_f + 1)y`, and the hole (`‖b‖² − Hole ≤ U(ℒ + log K + C₁)`).
-/
import ZetaShell.ShellS.L10c_ASSupp

noncomputable section
open scoped BigOperators Chebyshev

namespace ZetaShell
namespace ShellS
namespace ASc

/-- **the bracket of Lemma 2(a)** at the shell width of record. -/
theorem bracket_bound (Q : ℕ) (s y L Hw : ℝ) (hy : y = Real.log Q) (hy16 : 16 ≤ y) (hyL : y ≤ L)
    (hL2 : L ≤ 2 * y) (hlogL : 1 ≤ Real.log L) (hHw : (Q : ℝ) ^ 2 / 6 ≤ Hw)
    (hsmall : 32 * Real.exp s * y ^ 14 ≤ (Q : ℝ) ^ 2) :
    TrackF.bracket2a Q (Real.exp s) (1 / L) (L * Real.log L ^ 2) 1 Hw ≤ 67 * (Real.log L / L) := by
  have hL0 : 0 < L := by linarith
  have hQ0 : (0 : ℝ) < Q := by
    have : (1 : ℝ) < Q := by
      rw [hy] at hy16
      by_contra h; push Not at h
      have : Real.log Q ≤ 0 := Real.log_nonpos (Nat.cast_nonneg Q) h
      linarith
    linarith
  have hQ2 : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  have hHw0 : 0 < Hw := lt_of_lt_of_le (by positivity) hHw
  have hes : 0 < Real.exp s := Real.exp_pos s
  have hlogL0 : 0 < Real.log L := by linarith
  set lm := Real.log L / L with hlmd
  have hlm0 : 0 < lm := by positivity
  have hLlm : 1 ≤ L * lm := by rw [hlmd, mul_div_cancel₀ _ hL0.ne']; exact hlogL
  have hy0 : 0 < y := by linarith
  unfold TrackF.bracket2a TrackF.R1shell
  rw [← hy]
  -- term 1: `(1 + log K)³/K ≤ 64 log ℒ/ℒ`
  have t1 : (1 + Real.log (L * Real.log L ^ 2)) ^ 3 / (L * Real.log L ^ 2) ≤ 64 * lm := by
    have hK : Real.log (L * Real.log L ^ 2) ≤ 3 * Real.log L := by
      rw [Real.log_mul hL0.ne' (by positivity), Real.log_pow]
      have := Real.log_le_sub_one_of_pos hlogL0
      push_cast; linarith
    have hK0 : 0 ≤ Real.log (L * Real.log L ^ 2) := by
      apply Real.log_nonneg
      have : 1 ≤ Real.log L ^ 2 := one_le_pow₀ hlogL
      nlinarith
    have h1 : (1 + Real.log (L * Real.log L ^ 2)) ^ 3 ≤ (4 * Real.log L) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    rw [div_le_iff₀ (by positivity), hlmd]
    have e : 64 * (Real.log L / L) * (L * Real.log L ^ 2) = (4 * Real.log L) ^ 3 := by field_simp; ring
    rw [e]; exact h1
  -- term 2: `N y²/(εQR₁) = y⁻⁴`
  have t2 : Real.exp s * y ^ 2 / (1 / L * Q * (Real.exp s * y ^ 6 / (1 / L * Q))) ≤ lm := by
    have e : Real.exp s * y ^ 2 / (1 / L * Q * (Real.exp s * y ^ 6 / (1 / L * Q))) = 1 / y ^ 4 := by
      field_simp
    rw [e, hlmd, div_le_div_iff₀ (by positivity) hL0]
    have hy3 : (16:ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy16 3
    have h4 : y * 2 ≤ y * y ^ 3 := mul_le_mul_of_nonneg_left (by linarith) hy0.le
    have h4' : y ^ 4 = y * y ^ 3 := by ring
    have h5 : y ^ 4 ≤ Real.log L * y ^ 4 := le_mul_of_one_le_left (by positivity) hlogL
    linarith
  -- term 3
  have t3 : Real.exp s * y ^ 8 / (1 / L * (Q : ℝ) ^ 2) ≤ lm := by
    rw [div_le_iff₀ (by positivity)]
    have e : lm * (1 / L * (Q : ℝ) ^ 2) = Real.log L * (Q : ℝ) ^ 2 / L ^ 2 := by rw [hlmd]; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hL4 : L ^ 2 ≤ 4 * y ^ 2 := by
      have := pow_le_pow_left₀ hL0.le hL2 2
      have e2 : (2 * y) ^ 2 = 4 * y ^ 2 := by ring
      linarith
    have h1 : Real.exp s * y ^ 8 * L ^ 2 ≤ Real.exp s * y ^ 8 * (4 * y ^ 2) :=
      mul_le_mul_of_nonneg_left hL4 (by positivity)
    have h2 : Real.exp s * y ^ 8 * (4 * y ^ 2) ≤ 32 * Real.exp s * y ^ 14 := by
      have h10 : y ^ 10 ≤ y ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have e1 : Real.exp s * y ^ 8 * (4 * y ^ 2) = 4 * (Real.exp s * y ^ 10) := by ring
      have e2 : 32 * Real.exp s * y ^ 14 = 32 * (Real.exp s * y ^ 14) := by ring
      have h11 : Real.exp s * y ^ 10 ≤ Real.exp s * y ^ 14 := mul_le_mul_of_nonneg_left h10 hes.le
      have h12 : 0 ≤ Real.exp s * y ^ 14 := by positivity
      rw [e1, e2]; linarith
    have h3 : (Q : ℝ) ^ 2 ≤ Real.log L * (Q : ℝ) ^ 2 := le_mul_of_one_le_left hQ2.le hlogL
    linarith
  -- term 4
  have t4 : 1 * Real.exp s / (1 / L * Hw) ≤ lm := by
    rw [div_le_iff₀ (by positivity)]
    have e : lm * (1 / L * Hw) = Real.log L * Hw / L ^ 2 := by rw [hlmd]; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hL4 : L ^ 2 ≤ 4 * y ^ 2 := by
      have := pow_le_pow_left₀ hL0.le hL2 2
      have e2 : (2 * y) ^ 2 = 4 * y ^ 2 := by ring
      linarith
    have h1 : 1 * Real.exp s * L ^ 2 ≤ Real.exp s * (4 * y ^ 2) := by
      rw [one_mul]; exact mul_le_mul_of_nonneg_left hL4 hes.le
    have h2 : Real.exp s * (4 * y ^ 2) * 6 ≤ 32 * Real.exp s * y ^ 14 := by
      have h10 : y ^ 2 ≤ y ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have e1 : Real.exp s * (4 * y ^ 2) * 6 = 24 * (Real.exp s * y ^ 2) := by ring
      have e2 : 32 * Real.exp s * y ^ 14 = 32 * (Real.exp s * y ^ 14) := by ring
      have h11 : Real.exp s * y ^ 2 ≤ Real.exp s * y ^ 14 := mul_le_mul_of_nonneg_left h10 hes.le
      have h12 : 0 ≤ Real.exp s * y ^ 2 := by positivity
      rw [e1, e2]; linarith
    have h3 : Hw ≤ Real.log L * Hw := le_mul_of_one_le_left hHw0.le hlogL
    linarith
  linarith

/-- the ring factor: `Q² + N/ε ≤ Q²(1 + log ℒ/ℒ)`. -/
theorem Bm_bound (Q : ℕ) (s y L : ℝ) (hy16 : 16 ≤ y) (hyL : y ≤ L) (hL2 : L ≤ 2 * y)
    (hlogL : 1 ≤ Real.log L) (hsmall : 32 * Real.exp s * y ^ 14 ≤ (Q : ℝ) ^ 2) :
    (Q : ℝ) ^ 2 + Real.exp s / (1 / L) ≤ (Q : ℝ) ^ 2 * (1 + Real.log L / L) := by
  have hL0 : 0 < L := by linarith
  have hes : 0 < Real.exp s := Real.exp_pos s
  have e1 : Real.exp s / (1 / L) = Real.exp s * L := by field_simp
  have e2 : (Q : ℝ) ^ 2 * (1 + Real.log L / L) = (Q : ℝ) ^ 2 + (Q : ℝ) ^ 2 * Real.log L / L := by
    field_simp
  rw [e1, e2]
  have h : Real.exp s * L ≤ (Q : ℝ) ^ 2 * Real.log L / L := by
    rw [le_div_iff₀ hL0]
    have hL4 : L * L ≤ 4 * y ^ 2 := by nlinarith
    have h1 : Real.exp s * L * L ≤ Real.exp s * (4 * y ^ 2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hL4 hes.le
    have h10 : y ^ 2 ≤ y ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h11 : Real.exp s * y ^ 2 ≤ Real.exp s * y ^ 14 := mul_le_mul_of_nonneg_left h10 hes.le
    have h12 : 0 ≤ Real.exp s * y ^ 2 := by positivity
    have h3 : (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 * Real.log L := le_mul_of_one_le_right (by positivity) hlogL
    have e3 : Real.exp s * (4 * y ^ 2) = 4 * (Real.exp s * y ^ 2) := by ring
    have e4 : 32 * Real.exp s * y ^ 14 = 32 * (Real.exp s * y ^ 14) := by ring
    linarith
  linarith

/-- the coefficient of the edge term (AF1): `3(ε/N)(2R₁² + πN′) ≤ 27/y`. -/
theorem edge_coef (Q R1n Nn s y L : ℝ) (hQ : 0 < Q) (hy16 : 16 ≤ y) (hyL : y ≤ L) (hL2 : L ≤ 2 * y)
    (hR0 : 0 ≤ R1n) (hR : R1n * Q ≤ Real.exp s * y ^ 6 * L) (hNn : Nn ≤ Real.exp (s + 1))
    (hsmall : 32 * Real.exp s * y ^ 14 ≤ Q ^ 2) :
    3 * (1 / L / Real.exp s) * (2 * R1n ^ 2 + Real.pi * Nn) ≤ 27 / y := by
  have hL0 : 0 < L := by linarith
  have hy0 : 0 < y := by linarith
  have hes : 0 < Real.exp s := Real.exp_pos s
  have e : 3 * (1 / L / Real.exp s) * (2 * R1n ^ 2 + Real.pi * Nn)
      = 3 * (2 * R1n ^ 2 + Real.pi * Nn) / (L * Real.exp s) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) hy0]
  -- the ring part
  have hA : 6 * y * R1n ^ 2 ≤ L * Real.exp s := by
    have hR2 : (R1n * Q) ^ 2 ≤ (Real.exp s * y ^ 6 * L) ^ 2 := pow_le_pow_left₀ (by positivity) hR 2
    have hQ2 : 0 < Q ^ 2 := by positivity
    have key : 6 * y * R1n ^ 2 * Q ^ 2 ≤ L * Real.exp s * Q ^ 2 := by
      have s1 : 6 * y * R1n ^ 2 * Q ^ 2 = 6 * y * (R1n * Q) ^ 2 := by ring
      have s2 : 6 * y * (R1n * Q) ^ 2 ≤ 6 * y * (Real.exp s * y ^ 6 * L) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 (by positivity)
      have s3 : 6 * y * (Real.exp s * y ^ 6 * L) ^ 2 = (L * Real.exp s) * (6 * Real.exp s * y ^ 13 * L) := by
        ring
      have s4 : 6 * Real.exp s * y ^ 13 * L ≤ 12 * Real.exp s * y ^ 14 := by
        have : 6 * Real.exp s * y ^ 13 * L ≤ 6 * Real.exp s * y ^ 13 * (2 * y) :=
          mul_le_mul_of_nonneg_left hL2 (by positivity)
        have e' : 6 * Real.exp s * y ^ 13 * (2 * y) = 12 * Real.exp s * y ^ 14 := by ring
        linarith
      have s5 : 12 * Real.exp s * y ^ 14 ≤ Q ^ 2 := by
        have : 0 ≤ Real.exp s * y ^ 14 := by positivity
        have e' : 32 * Real.exp s * y ^ 14 = 32 * (Real.exp s * y ^ 14) := by ring
        have e'' : 12 * Real.exp s * y ^ 14 = 12 * (Real.exp s * y ^ 14) := by ring
        linarith
      have s6 : (L * Real.exp s) * (6 * Real.exp s * y ^ 13 * L) ≤ (L * Real.exp s) * Q ^ 2 :=
        mul_le_mul_of_nonneg_left (le_trans s4 s5) (by positivity)
      rw [s1]; linarith
    exact le_of_mul_le_mul_right key hQ2
  -- the `N` part
  have hB : 3 * y * (Real.pi * Nn) ≤ 26 * L * Real.exp s := by
    have he : Real.exp (s + 1) = Real.exp s * Real.exp 1 := Real.exp_add s 1
    have he1 := Real.exp_one_lt_d9
    have hpi := Real.pi_lt_d2
    have h1 : Real.pi * Nn ≤ Real.pi * (Real.exp s * Real.exp 1) := by
      rw [← he]; exact mul_le_mul_of_nonneg_left hNn Real.pi_pos.le
    have h2 : Real.pi * Real.exp 1 ≤ 3.15 * 2.7182818286 := by
      have := Real.exp_pos 1
      nlinarith [Real.pi_pos]
    have h3 : Real.pi * (Real.exp s * Real.exp 1) ≤ 8.6 * Real.exp s := by
      have e' : Real.pi * (Real.exp s * Real.exp 1) = (Real.pi * Real.exp 1) * Real.exp s := by ring
      rw [e']; exact mul_le_mul_of_nonneg_right (by linarith) hes.le
    have h4 : 3 * y * (Real.pi * Nn) ≤ 3 * y * (8.6 * Real.exp s) :=
      mul_le_mul_of_nonneg_left (le_trans h1 h3) (by positivity)
    have h5 : y * Real.exp s ≤ L * Real.exp s := mul_le_mul_of_nonneg_right hyL hes.le
    have e' : 3 * y * (8.6 * Real.exp s) = 25.8 * (y * Real.exp s) := by ring
    have e'' : 26 * L * Real.exp s = 26 * (L * Real.exp s) := by ring
    have : 0 ≤ y * Real.exp s := by positivity
    linarith
  have e2 : 3 * (2 * R1n ^ 2 + Real.pi * Nn) * y = 6 * y * R1n ^ 2 + 3 * y * (Real.pi * Nn) := by ring
  have e3 : 27 * (L * Real.exp s) = L * Real.exp s + 26 * L * Real.exp s := by ring
  rw [e2, e3]; linarith

/-- the edge term `Ed ≤ 1080 H U`. -/
theorem Ed_bound (Q : ℕ) (R1n Nn s y L U Hw l2b : ℝ) (hQ : 0 < (Q : ℝ)) (hy16 : 16 ≤ y) (hyL : y ≤ L)
    (hL2 : L ≤ 2 * y) (hs2 : s ≤ 2 * y) (hR0 : 0 ≤ R1n) (hR : R1n * Q ≤ Real.exp s * y ^ 6 * L)
    (hNn : Nn ≤ Real.exp (s + 1)) (hNn0 : 0 ≤ Nn) (hsmall : 32 * Real.exp s * y ^ 14 ≤ (Q : ℝ) ^ 2)
    (hHw : (Q : ℝ) ^ 2 / 6 ≤ Hw) (hU : 0 ≤ U) (hl2b0 : 0 ≤ l2b) (hl2b : l2b ≤ U * (s + 2)) :
    ((Q : ℝ) ^ 2 + Real.exp s / (1 / L)) * (3 * (1 / L / Real.exp s) * (2 * R1n ^ 2 + Real.pi * Nn)) * l2b
      ≤ 1080 * Hw * U := by
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < L := by linarith
  have hes : 0 < Real.exp s := Real.exp_pos s
  have hA : (Q : ℝ) ^ 2 + Real.exp s / (1 / L) ≤ 2 * (Q : ℝ) ^ 2 := by
    have e1 : Real.exp s / (1 / L) = Real.exp s * L := by field_simp
    rw [e1]
    have h1 : Real.exp s * L ≤ Real.exp s * (2 * y) := mul_le_mul_of_nonneg_left hL2 hes.le
    have h10 : y ≤ y ^ 14 := by
      calc y = y ^ 1 := (pow_one y).symm
        _ ≤ y ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h11 : Real.exp s * y ≤ Real.exp s * y ^ 14 := mul_le_mul_of_nonneg_left h10 hes.le
    have h12 : 0 ≤ Real.exp s * y := by positivity
    have e3 : Real.exp s * (2 * y) = 2 * (Real.exp s * y) := by ring
    have e4 : 32 * Real.exp s * y ^ 14 = 32 * (Real.exp s * y ^ 14) := by ring
    linarith
  have hA0 : 0 ≤ (Q : ℝ) ^ 2 + Real.exp s / (1 / L) := by positivity
  have hB := edge_coef Q R1n Nn s y L hQ hy16 hyL hL2 hR0 hR hNn hsmall
  have hB0 : 0 ≤ 3 * (1 / L / Real.exp s) * (2 * R1n ^ 2 + Real.pi * Nn) := by
    have : 0 ≤ Real.pi * Nn := mul_nonneg Real.pi_pos.le hNn0
    positivity
  have hl2 : l2b ≤ U * (3 * y) := le_trans hl2b (mul_le_mul_of_nonneg_left (by linarith) hU)
  calc ((Q : ℝ) ^ 2 + Real.exp s / (1 / L)) * (3 * (1 / L / Real.exp s) * (2 * R1n ^ 2 + Real.pi * Nn)) * l2b
      ≤ (2 * (Q : ℝ) ^ 2) * (27 / y) * (U * (3 * y)) := by
        apply mul_le_mul (mul_le_mul hA hB hB0 (by positivity)) hl2 hl2b0 (by positivity)
    _ = 162 * (Q : ℝ) ^ 2 * U := by field_simp; ring
    _ ≤ 1080 * Hw * U := by
        have : 162 * (Q : ℝ) ^ 2 ≤ 1080 * Hw := by linarith
        exact mul_le_mul_of_nonneg_right this hU

/-- the Lemma 3 term `2π sinh κ (εQ² + N)‖b‖² ≤ 300 H U`. -/
theorem Ga_bound (Q : ℕ) (κ s y L U Hw l2b : ℝ) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hy16 : 16 ≤ y) (hyL : y ≤ L)
    (hs2 : s ≤ 2 * y) (hsmall : 32 * Real.exp s * y ^ 14 ≤ (Q : ℝ) ^ 2)
    (hHw : (Q : ℝ) ^ 2 / 6 ≤ Hw) (hU : 0 ≤ U) (hl2b0 : 0 ≤ l2b) (hl2b : l2b ≤ U * (s + 2)) :
    2 * Real.pi * Real.sinh κ * (1 / L * (Q : ℝ) ^ 2 + Real.exp s) * l2b ≤ 300 * Hw * U := by
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < L := by linarith
  have hes : 0 < Real.exp s := Real.exp_pos s
  have hsh0 : 0 ≤ Real.sinh κ := Real.sinh_nonneg_iff.mpr hκ
  have hsh1 : Real.sinh κ ≤ 1.36 := by
    have h1 : Real.sinh κ ≤ Real.sinh 1 := Real.sinh_le_sinh.mpr hκ1
    have h2 : Real.sinh 1 = (Real.exp 1 - Real.exp (-1)) / 2 := Real.sinh_eq 1
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos (-1)
    linarith
  have hpi := Real.pi_lt_d2
  have hl2 : l2b ≤ U * (3 * y) := le_trans hl2b (mul_le_mul_of_nonneg_left (by linarith) hU)
  have hB : (1 / L * (Q : ℝ) ^ 2 + Real.exp s) * l2b ≤ 4 * (Q : ℝ) ^ 2 * U := by
    have hB0 : 0 ≤ 1 / L * (Q : ℝ) ^ 2 + Real.exp s := by positivity
    have h1 : (1 / L * (Q : ℝ) ^ 2 + Real.exp s) * l2b ≤ (1 / L * (Q : ℝ) ^ 2 + Real.exp s) * (U * (3 * y)) :=
      mul_le_mul_of_nonneg_left hl2 hB0
    have e : (1 / L * (Q : ℝ) ^ 2 + Real.exp s) * (U * (3 * y))
        = 3 * (y / L) * ((Q : ℝ) ^ 2 * U) + 3 * (Real.exp s * y) * U := by field_simp
    have h2 : y / L ≤ 1 := by rw [div_le_one hL0]; exact hyL
    have h3 : 3 * (Real.exp s * y) ≤ (Q : ℝ) ^ 2 := by
      have h10 : y ≤ y ^ 14 := by
        calc y = y ^ 1 := (pow_one y).symm
          _ ≤ y ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have h11 : Real.exp s * y ≤ Real.exp s * y ^ 14 := mul_le_mul_of_nonneg_left h10 hes.le
      have h12 : 0 ≤ Real.exp s * y := by positivity
      have e4 : 32 * Real.exp s * y ^ 14 = 32 * (Real.exp s * y ^ 14) := by ring
      linarith
    have hQU : 0 ≤ (Q : ℝ) ^ 2 * U := by positivity
    have h4 : 3 * (y / L) * ((Q : ℝ) ^ 2 * U) ≤ 3 * ((Q : ℝ) ^ 2 * U) := by
      have := mul_le_mul_of_nonneg_right h2 hQU
      linarith
    have h5 : 3 * (Real.exp s * y) * U ≤ (Q : ℝ) ^ 2 * U := mul_le_mul_of_nonneg_right h3 hU
    rw [e] at h1; linarith
  have hc : 2 * Real.pi * Real.sinh κ ≤ 2 * 3.15 * 1.36 := by
    have := mul_le_mul hpi.le hsh1 hsh0 (by norm_num)
    linarith
  have hc0 : 0 ≤ 2 * Real.pi * Real.sinh κ := by positivity
  have hB0 : 0 ≤ (1 / L * (Q : ℝ) ^ 2 + Real.exp s) * l2b := by positivity
  have e : 2 * Real.pi * Real.sinh κ * (1 / L * (Q : ℝ) ^ 2 + Real.exp s) * l2b
      = (2 * Real.pi * Real.sinh κ) * ((1 / L * (Q : ℝ) ^ 2 + Real.exp s) * l2b) := by ring
  rw [e]
  have h1 := mul_le_mul hc hB hB0 (by norm_num)
  have hQU : 0 ≤ (Q : ℝ) ^ 2 * U := by positivity
  have h2 : (2 * 3.15 * 1.36 : ℝ) * (4 * (Q : ℝ) ^ 2 * U) ≤ 300 * Hw * U := by
    have : (2 * 3.15 * 1.36 : ℝ) * (4 * (Q : ℝ) ^ 2 * U) = 34.272 * ((Q : ℝ) ^ 2 * U) := by ring
    rw [this]
    have h3 : (Q : ℝ) ^ 2 * U ≤ 6 * Hw * U := by
      have : (Q : ℝ) ^ 2 ≤ 6 * Hw := by linarith
      exact mul_le_mul_of_nonneg_right this hU
    have h4 : 0 ≤ Hw * U := mul_nonneg (by linarith [sq_nonneg (Q : ℝ)]) hU
    nlinarith
  linarith

/-- the Gallagher cost of the replacement `a ↦ b`: `(Q² + πX)‖a − b‖² ≤ H U/ℒ`. -/
theorem GE_bound (Q : ℕ) (Nx Cf y L U Hw l2c : ℝ) (hy16 : 16 ≤ y) (hyL : y ≤ L) (hL2 : L ≤ 2 * y)
    (hNx : Real.pi * Nx ≤ (Q : ℝ) ^ 2) (hCf : 0 ≤ Cf) (hl2c0 : 0 ≤ l2c) (hl2c : l2c ≤ (Cf + 1) * y)
    (hUbig : 2 * (Cf + 1) * y ^ 3 ≤ U) (hHw : (Q : ℝ) ^ 2 / 6 ≤ Hw) :
    ((Q : ℝ) ^ 2 + Real.pi * Nx) * l2c ≤ 1 * Hw * U / L := by
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < L := by linarith
  rw [le_div_iff₀ hL0]
  have hQ2 : 0 ≤ (Q : ℝ) ^ 2 := by positivity
  have h1 : ((Q : ℝ) ^ 2 + Real.pi * Nx) * l2c ≤ (2 * (Q : ℝ) ^ 2) * ((Cf + 1) * y) :=
    mul_le_mul (by linarith) hl2c hl2c0 (by positivity)
  have h2 : ((Q : ℝ) ^ 2 + Real.pi * Nx) * l2c * L ≤ (2 * (Q : ℝ) ^ 2) * ((Cf + 1) * y) * (2 * y) :=
    mul_le_mul h1 hL2 hL0.le (by positivity)
  have h3 : (2 * (Q : ℝ) ^ 2) * ((Cf + 1) * y) * (2 * y) = (Q : ℝ) ^ 2 * (4 * (Cf + 1) * y ^ 2) := by ring
  have h4 : 4 * (Cf + 1) * y ^ 2 ≤ U / 6 := by
    have : 4 * (Cf + 1) * y ^ 2 * 6 ≤ 2 * (Cf + 1) * y ^ 3 := by
      have e : 2 * (Cf + 1) * y ^ 3 = 2 * (Cf + 1) * y ^ 2 * y := by ring
      rw [e]
      have : 0 ≤ (Cf + 1) * y ^ 2 := by positivity
      nlinarith
    have : 0 ≤ (Cf + 1) * y ^ 2 := by positivity
    linarith
  have hU0 : 0 ≤ U := le_trans (by positivity) hUbig
  have h5 : (Q : ℝ) ^ 2 * (4 * (Cf + 1) * y ^ 2) ≤ (Q : ℝ) ^ 2 * (U / 6) := mul_le_mul_of_nonneg_left h4 hQ2
  have h6 : (Q : ℝ) ^ 2 * (U / 6) ≤ 1 * Hw * U := by
    have e : (Q : ℝ) ^ 2 * (U / 6) = (Q : ℝ) ^ 2 / 6 * U := by ring
    rw [e, one_mul]; exact mul_le_mul_of_nonneg_right hHw hU0
  linarith

/-- **PNT upper bound for the near sum**: `‖b‖² ≤ U(s + 2)`. -/
theorem l2b_upper (Q T κ : ℝ) (Ξ : ℝ → ℝ) (hΞ : ZetaShell.PropZ.NearCutoff Ξ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (s : ℝ) (hs : 3 ≤ s) (Nn : ℕ) (hT1 : 1 ≤ T) (hbig : 100 * T ^ 3 ≤ Real.exp s) (εθ : ℝ) (hε0 : 0 ≤ εθ)
    (hθ : ∀ k : ℕ, Real.exp (s - 1) - 1 ≤ k → (k : ℝ) ≤ Real.exp (s + 1) → |θ (k : ℝ) - k| ≤ εθ * k)
    (h34 : 34 * εθ * T ^ 3 ≤ 1) (hsT : s + 1 ≤ Real.pi * T) :
    ZetaQ.l2sq Nn (aNearP Q T κ Ξ s) ≤ T / (2 * Real.pi) * (s + 2) := by
  have h1 := nearP_l2_le Q T κ Ξ hΞ hκ hκ1 s (by linarith) Nn
  have h2 := prime_window_upper T s εθ hT1 hs hbig hε0 hθ
  have hpi := Real.pi_pos
  have hc : 0 ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hc
  have h4 : (4 * Real.pi ^ 2)⁻¹ * (s + 1) * (2 * Real.pi * T + 1 + 34 * εθ * T ^ 3)
      ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) * (2 * Real.pi * T + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  have h5 : (4 * Real.pi ^ 2)⁻¹ * (s + 1) * (2 * Real.pi * T + 2) ≤ T / (2 * Real.pi) * (s + 2) := by
    have e : (4 * Real.pi ^ 2)⁻¹ * (s + 1) * (2 * Real.pi * T + 2)
        = T / (2 * Real.pi) * (s + 1) + (s + 1) / (2 * Real.pi ^ 2) := by field_simp; ring
    have e2 : T / (2 * Real.pi) * (s + 2) = T / (2 * Real.pi) * (s + 1) + T / (2 * Real.pi) := by ring
    rw [e, e2]
    have : (s + 1) / (2 * Real.pi ^ 2) ≤ T / (2 * Real.pi) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (s + 1) * (2 * Real.pi) ≤ Real.pi * T * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hsT (by positivity)
      nlinarith
    linarith
  linarith

/-- the tail term of `l2_far_le` is at most `1`. -/
theorem tiny_le (s y T : ℝ) (hy16 : 16 ≤ y) (hs1 : y + 4 ≤ s) (hs2 : s ≤ 2 * y) (hT : 0 ≤ T)
    (hyT : y ^ 4 * T ^ 4 ≤ Real.exp y) :
    (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s) * (2 * Real.exp ((s + 1) / 2) * (s + 1)) ≤ 1 := by
  have hy0 : 0 < y := by linarith
  have hpi := Real.pi_gt_three
  have e : (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s) * (2 * Real.exp ((s + 1) / 2) * (s + 1))
      = (2 * (4 * Real.pi ^ 2)⁻¹) * ((s + 1) ^ 2 * T ^ 2 * Real.exp ((3 - s) / 2)) := by
    have : Real.exp (1 - s) * Real.exp ((s + 1) / 2) = Real.exp ((3 - s) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← this]; ring
  rw [e]
  have hc : 2 * (4 * Real.pi ^ 2)⁻¹ ≤ 1 / 9 := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hs3 : (s + 1) ^ 2 ≤ 9 * y ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) (show s + 1 ≤ 3 * y by linarith) 2
    nlinarith
  have hex : Real.exp ((3 - s) / 2) ≤ Real.exp (-(y / 2)) := Real.exp_le_exp.mpr (by linarith)
  have hyT2 : y ^ 2 * T ^ 2 ≤ Real.exp (y / 2) := by
    have h1 : (y ^ 2 * T ^ 2) ^ 2 ≤ Real.exp (y / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast
      have : (2 : ℝ) * (y / 2) = y := by ring
      rw [this]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (Real.exp_pos _).le (by norm_num)).mp h1
  have hA : (s + 1) ^ 2 * T ^ 2 * Real.exp ((3 - s) / 2) ≤ 9 * (y ^ 2 * T ^ 2) * Real.exp (-(y / 2)) := by
    have h1 : (s + 1) ^ 2 * T ^ 2 ≤ 9 * (y ^ 2 * T ^ 2) := by nlinarith [sq_nonneg T]
    exact mul_le_mul h1 hex (Real.exp_pos _).le (by positivity)
  have hB : 9 * (y ^ 2 * T ^ 2) * Real.exp (-(y / 2)) ≤ 9 := by
    have h1 : (y ^ 2 * T ^ 2) * Real.exp (-(y / 2)) ≤ Real.exp (y / 2) * Real.exp (-(y / 2)) :=
      mul_le_mul_of_nonneg_right hyT2 (Real.exp_pos _).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h1
    linarith
  have hA0 : 0 ≤ (s + 1) ^ 2 * T ^ 2 * Real.exp ((3 - s) / 2) := by positivity
  have := mul_le_mul hc (le_trans hA hB) hA0 (by norm_num)
  linarith

/-- the far coefficients: `‖v‖² ≤ (C_f + 1)y` for `v` dominated by `a(s)` and vanishing on the near primes. -/
def Cf (d : ℝ) : ℝ := 12 * C0ch * (1 / d ^ 2 + 2) / Real.pi ^ 2

theorem Cf_nonneg (d : ℝ) : 0 ≤ Cf d := by
  unfold Cf; have := C0ch_pos; positivity

theorem compl_bound (M : ℕ) (T s d y : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) (hM : Real.log M ≤ 4 * y) (hy : 1 ≤ y)
    (hT : 0 ≤ T) (hs : 1 ≤ s) (v : ℕ → ℂ) (hv : ∀ n, ‖v n‖ ≤ ‖TrackF.acoefS T s n‖)
    (hv0 : ∀ n : ℕ, n.Prime → |Real.log n - s| ≤ d → v n = 0)
    (htiny : (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s) * (2 * Real.exp ((s + 1) / 2) * (s + 1)) ≤ 1) :
    ZetaQ.l2sq M v ≤ (Cf d + 1) * y := by
  have h := l2_far_le M T s d (4 * y) hd hd1 hM (by linarith) hT hs v hv hv0
  have e : (1 / Real.pi ^ 2) * (3 * C0ch * (4 * y) * (1 / d ^ 2 + 2)) = Cf d * y := by
    unfold Cf; field_simp; ring
  rw [e] at h
  linarith

/-- `‖b‖² ≤ ‖a‖²` (truncations `N′ ≤ 𝒳`). -/
theorem l2b_le_l2a (Nn Nx : ℕ) (h : Nn ≤ Nx) (T s : ℝ) (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ ‖TrackF.acoefS T s n‖) :
    ZetaQ.l2sq Nn b ≤ l2S Nx T s := by
  unfold ZetaQ.l2sq l2S
  calc ∑ n ∈ Finset.Ioc 0 Nn, ‖b n‖ ^ 2 ≤ ∑ n ∈ Finset.Ioc 0 Nn, ‖TrackF.acoefS T s n‖ ^ 2 :=
        Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hb n) 2
    _ ≤ ∑ n ∈ Finset.Ioc 0 Nx, ‖TrackF.acoefS T s n‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right h) fun _ _ _ => by positivity

/-- `ℓ_K = log(QTℒ) ≤ ℒ + log K + 2`. -/
theorem ell_le (Q T : ℝ) (hQ : 0 < Q) (hT : 0 < T) (hL1 : 0 < Real.log (Q * T / (2 * Real.pi)))
    (hlogL : 1 ≤ Real.log (Real.log (Q * T / (2 * Real.pi)))) :
    Real.log (Q * T * Real.log (Q * T / (2 * Real.pi)))
      ≤ Real.log (Q * T / (2 * Real.pi))
        + Real.log (Real.log (Q * T / (2 * Real.pi)) * Real.log (Real.log (Q * T / (2 * Real.pi))) ^ 2) + 2 := by
  set L := Real.log (Q * T / (2 * Real.pi)) with hL
  have hpi := Real.pi_pos
  have hL0 : 0 < L := hL1
  have e : Q * T * L = (Q * T / (2 * Real.pi)) * (2 * Real.pi) * L := by field_simp
  rw [e, Real.log_mul (by positivity) hL0.ne', Real.log_mul (by positivity) (by positivity), ← hL]
  have h2pi : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 := Real.pi_lt_d2
    have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hK : Real.log L ≤ Real.log (L * Real.log L ^ 2) := by
    apply Real.log_le_log hL0
    have : 1 ≤ Real.log L ^ 2 := one_le_pow₀ hlogL
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **the hole of `b`** (Lemma 4 via K6/K7), case `ℓ_K ≤ s`: `‖b‖² − Hole ≤ U(ℓ_K + 6 + 2|C₆|)`. -/
theorem hole_case2 (Q Nx Nn : ℕ) (b a' : ℕ → ℂ) (s y T L U C₆ Cf : ℝ)
    (hy16 : 16 ≤ y) (hQ1 : 1 ≤ (Q : ℝ)) (hT1 : 1 ≤ T) (hL1 : 1 ≤ L) (hU0 : 0 ≤ U)
    (hℓ : Real.log ((Q : ℝ) * T * L) ≤ s) (hs2 : s ≤ 2 * y) (hsQ : Real.exp s < (Q : ℝ) ^ 2)
    (hbP : ∀ n, b n ≠ 0 → n.Prime ∧ Q < n) (hNn : Nn ≤ Nx) (hbz : ∀ n, Nn < n → b n = 0)
    (hA : (1 - C₆ / y) * U ≤ ∫ β in (-(T * L / (2 * Real.exp s)))..(T * L / (2 * Real.exp s)),
        ‖ZetaQ.expSum Nx a' β‖ ^ 2)
    (hE : ZetaQ.l2sq Nx (fun n => a' n - b n) ≤ (Cf + 1) * y) (hCf : 0 ≤ Cf)
    (hUbig : 2 * (Cf + 1) * y ^ 3 ≤ U) (hl2 : ZetaQ.l2sq Nn b ≤ U * (s + 2)) :
    ZetaQ.l2sq Nn b - LemmaK.holeInt Nn b (Real.exp s / ((Q : ℝ) * T * L)) (T * L / (2 * Real.exp s))
      ≤ U * (Real.log ((Q : ℝ) * T * L) + 6 + 2 * |C₆|) := by
  have hy0 : 0 < y := by linarith
  have hes : 0 < Real.exp s := Real.exp_pos s
  have hTL1 : 1 ≤ T * L := one_le_mul_of_one_le_of_one_le hT1 hL1
  have hQTL1 : 1 ≤ (Q : ℝ) * T * L := by
    rw [mul_assoc]; exact one_le_mul_of_one_le_of_one_le hQ1 hTL1
  have hQTL : 0 < (Q : ℝ) * T * L := by linarith
  have hle : (Q : ℝ) * T * L ≤ Real.exp s := (Real.log_le_iff_le_exp hQTL).mp hℓ
  set R := Real.exp s / ((Q : ℝ) * T * L) with hRdef
  set Δ := T * L / (2 * Real.exp s) with hΔdef
  have hR1 : 1 ≤ R := by rw [hRdef, le_div_iff₀ hQTL]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hRQ : R < Q := by
    rw [hRdef, div_lt_iff₀ hQTL]
    have : (Q : ℝ) ^ 2 ≤ (Q : ℝ) * ((Q : ℝ) * T * L) := by
      have e : (Q : ℝ) * ((Q : ℝ) * T * L) = (Q : ℝ) ^ 2 * (T * L) := by ring
      rw [e]; exact le_mul_of_one_le_right (by positivity) hTL1
    linarith
  have hΔ0 : 0 < Δ := by rw [hΔdef]; have : 0 < T * L := by linarith
                         positivity
  have hΔh : Δ ≤ 1 / 2 := by
    rw [hΔdef, div_le_iff₀ (by positivity)]
    have : T * L ≤ (Q : ℝ) * T * L := by
      rw [mul_assoc]; exact le_mul_of_one_le_left (by linarith) hQ1
    linarith
  have hkey : 2 * Δ * (R * R) ≤ 1 := by
    have e : 2 * Δ * (R * R) = Real.exp s / ((Q : ℝ) ^ 2 * (T * L)) := by
      rw [hΔdef, hRdef]; field_simp
    rw [e, div_le_one (by positivity)]
    have : (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 * (T * L) := le_mul_of_one_le_right (by positivity) hTL1
    linarith
  have hrR : ∀ r : ℕ, r ≤ ⌊R⌋₊ → (r : ℝ) ≤ R := fun r h =>
    le_trans (Nat.cast_le.mpr h) (Nat.floor_le hR0)
  have hsepΔ : ∀ r r' : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → 1 ≤ r' → r' ≤ ⌊R⌋₊ → 2 * Δ ≤ 1 / ((r : ℝ) * r') := by
    intro r r' hr hrR' hr' hr'R
    have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have h1' : (1 : ℝ) ≤ r' := by exact_mod_cast hr'
    rw [le_div_iff₀ (by positivity)]
    have : (r : ℝ) * r' ≤ R * R := mul_le_mul (hrR r hrR') (hrR r' hr'R) (by linarith) hR0
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 2 * Δ)
    linarith
  have hcop : ∀ r : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → ∀ n ∈ Finset.Ioc 0 Nx, b n ≠ 0 → Nat.Coprime n r := by
    intro r hr hrR' n _ hbn
    obtain ⟨hp, hQn⟩ := hbP n hbn
    have hrQ : (r : ℝ) < Q := lt_of_le_of_lt (hrR r hrR') hRQ
    have hrQ' : r < Q := by exact_mod_cast hrQ
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hh := hole_lower_det Nx b a' R Δ (1 / y) ((1 - C₆ / y) * U) ((Cf + 1) * y) hΔ0 hΔh hsepΔ hR1 hcop
    (by positivity) (by rw [div_le_one hy0]; linarith) hA hE
  rw [holeInt_trunc Nn Nx hNn b hbz, l2sq_trunc Nn Nx hNn b hbz] at hh
  have hlogR : Real.log R = s - Real.log ((Q : ℝ) * T * L) := by
    rw [hRdef, Real.log_div hes.ne' hQTL.ne', Real.log_exp]
  rw [hlogR] at hh
  set ℓ := Real.log ((Q : ℝ) * T * L) with hℓdef
  set l2b := ZetaQ.l2sq Nn b with hl2bdef
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hQTL1
  set D := s - ℓ with hD
  have hD0 : 0 ≤ D := by linarith
  have hD2 : D ≤ 2 * y := by linarith
  have hl2b0 : 0 ≤ l2b := Finset.sum_nonneg fun _ _ => by positivity
  -- `2√‖b‖² ≤ U`
  have h12 : 12 * y ≤ U := by
    have : 12 * y ≤ 2 * (Cf + 1) * y ^ 3 := by
      have hy2 : 6 ≤ y ^ 2 := by
        have := mul_le_mul hy16 hy16 (by norm_num) hy0.le
        rw [sq]; linarith
      have e : 2 * (Cf + 1) * y ^ 3 = 2 * (Cf + 1) * y ^ 2 * y := by ring
      rw [e]
      have h3 : y ^ 2 ≤ (Cf + 1) * y ^ 2 := le_mul_of_one_le_left (by positivity) (by linarith)
      have : 12 ≤ 2 * (Cf + 1) * y ^ 2 := by linarith
      exact mul_le_mul_of_nonneg_right this hy0.le
    linarith
  have hsq : 2 * Real.sqrt l2b ≤ U := by
    have h1 : l2b ≤ (U / 2) ^ 2 := by
      have : U * (s + 2) ≤ U * (3 * y) := mul_le_mul_of_nonneg_left (by linarith) hU0
      have : U * (3 * y) ≤ U * (U / 4) := mul_le_mul_of_nonneg_left (by linarith) hU0
      have e : (U / 2) ^ 2 = U * (U / 4) := by ring
      linarith
    have h2 : Real.sqrt l2b ≤ U / 2 := by
      calc Real.sqrt l2b ≤ Real.sqrt ((U / 2) ^ 2) := Real.sqrt_le_sqrt h1
        _ = U / 2 := Real.sqrt_sq (by linarith)
    linarith
  -- `(1 − 1/y)(1 − C₆/y) ≥ 1 − (1 + |C₆|)/y`
  have hprod : (1 - (1 + |C₆|) / y) * U ≤ (1 - 1 / y) * ((1 - C₆ / y) * U) := by
    have e : (1 - 1 / y) * ((1 - C₆ / y) * U) = ((1 - 1 / y) * (1 - C₆ / y)) * U := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hU0
    have ha0 : 0 < 1 / y := by positivity
    have ha1 : 1 / y ≤ 1 := by rw [div_le_one hy0]; linarith
    have e2 : (1 - 1 / y) * (1 - C₆ / y) = 1 - 1 / y - C₆ * (1 / y) * (1 - 1 / y) := by ring
    have e3 : (1 + |C₆|) / y = 1 / y + |C₆| * (1 / y) := by ring
    rw [e2, e3]
    have h1 : C₆ * (1 - 1 / y) ≤ |C₆| := by
      have : C₆ * (1 - 1 / y) ≤ |C₆| * (1 - 1 / y) :=
        mul_le_mul_of_nonneg_right (le_abs_self C₆) (by linarith)
      have : |C₆| * (1 - 1 / y) ≤ |C₆| := mul_le_of_le_one_right (abs_nonneg C₆) (by linarith)
      linarith
    have h2 : C₆ * (1 / y) * (1 - 1 / y) ≤ |C₆| * (1 / y) := by
      have e4 : C₆ * (1 / y) * (1 - 1 / y) = (C₆ * (1 - 1 / y)) * (1 / y) := by ring
      rw [e4]; exact mul_le_mul_of_nonneg_right h1 ha0.le
    linarith
  have hD1 : D * U - 2 * (1 + |C₆|) * U ≤ D * ((1 - 1 / y) * ((1 - C₆ / y) * U)) := by
    have h1 := mul_le_mul_of_nonneg_left hprod hD0
    have e : D * ((1 - (1 + |C₆|) / y) * U) = D * U - (D / y) * ((1 + |C₆|) * U) := by
      field_simp
    have h2 : (D / y) * ((1 + |C₆|) * U) ≤ 2 * ((1 + |C₆|) * U) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [div_le_iff₀ hy0]; linarith
    linarith
  have hDE : D * ((Cf + 1) * y / (1 / y)) ≤ U := by
    have e : (Cf + 1) * y / (1 / y) = (Cf + 1) * y ^ 2 := by field_simp
    rw [e]
    have : D * ((Cf + 1) * y ^ 2) ≤ 2 * y * ((Cf + 1) * y ^ 2) :=
      mul_le_mul_of_nonneg_right hD2 (by positivity)
    have e2 : 2 * y * ((Cf + 1) * y ^ 2) = 2 * (Cf + 1) * y ^ 3 := by ring
    linarith
  have e : D * ((1 - 1 / y) * ((1 - C₆ / y) * U) - (Cf + 1) * y / (1 / y))
      = D * ((1 - 1 / y) * ((1 - C₆ / y) * U)) - D * ((Cf + 1) * y / (1 / y)) := by ring
  rw [e] at hh
  have e2 : U * (ℓ + 6 + 2 * |C₆|) = U * (s + 2) - (D * U - 2 * (1 + |C₆|) * U) + U + U := by
    rw [hD]; ring
  rw [e2]
  linarith

end ASc
end ShellS
end ZetaShell
