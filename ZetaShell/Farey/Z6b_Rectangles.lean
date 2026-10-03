/-
Node Z6b (L7_6): **Lemma 6b, rectangles** (lem:shell-6b, sec_shell.tex l.679–689).

Draft: "If `R ≤ R₁` and `H ≤ 2^j(2T+1+K N₀^{1+ε'}/(RQ))`, then `R² H^h ≤ 4^j 𝒵 N₀^{2ε'}` for every
`h ∈ [0,2]`", with `𝒵 := 9[R₁²(2T+1)² + (K N₀/Q)²]` (eq:shell-Zsize, l.676).

Hypotheses added (all implicit in the draft's context, l.672–696: `R ≥ 1`, `T ≥ 2`, `N₀ = e^{s₀}`, `s₀ ≥ 3`,
`K, Q > 0`, `ε' > 0`, `j ≥ 1` indexes height shells):
* `0 ≤ R`, `0 ≤ H`: real powers `H^h` of a negative `H` are Mathlib junk (`Real.rpow` of a negative base);
* `0 ≤ T`: gives `2T+1 ≥ 1`, needed for `x^h ≤ x²` at `h ≤ 2`;
* `0 ≤ K`, `0 < Q`: the second summand of the height bound is `≥ 0`;
* `1 ≤ N₀`, `0 ≤ ε'`: the case `x ≥ y` of the proof uses `𝒵 ≤ 𝒵 N₀^{2ε'}`;
* `j : ℕ`: for `j < 0` and `h < 2` the step `2^{jh} ≤ 4^j` fails.
Dependencies: none (Mathlib real powers). Difficulty: E.
-/
import Mathlib

noncomputable section

namespace ZetaShell

/-- `𝒵 := 9[R₁²(2T+1)² + (K N₀/Q)²]` (eq:shell-Zsize, sec_shell.tex l.676). -/
def Zsize (R1 T K N0 Q : ℝ) : ℝ := 9 * (R1 ^ 2 * (2 * T + 1) ^ 2 + (K * N0 / Q) ^ 2)

/-- **Lemma 6b (rectangles)**, lem:shell-6b: if `R ≤ R₁` and `H ≤ 2^j(2T+1+K N₀^{1+ε'}/(RQ))`, then
`R² H^h ≤ 4^j 𝒵 N₀^{2ε'}` for every `h ∈ [0,2]`. -/
theorem shell_rectangles (R R1 H T K N0 Q ε' h : ℝ) (j : ℕ)
    (hR : 0 ≤ R) (hRR1 : R ≤ R1) (hT : 0 ≤ T) (hK : 0 ≤ K) (hN0 : 1 ≤ N0) (hQ : 0 < Q)
    (hε : 0 ≤ ε') (hH0 : 0 ≤ H)
    (hH : H ≤ 2 ^ j * (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q)))
    (hh0 : 0 ≤ h) (hh2 : h ≤ 2) :
    R ^ 2 * H ^ h ≤ 4 ^ j * Zsize R1 T K N0 Q * N0 ^ (2 * ε') := by
  have hN0pos : 0 < N0 := by linarith
  have hx1 : (1 : ℝ) ≤ 2 * T + 1 := by linarith
  have hy0 : 0 ≤ K * N0 ^ (1 + ε') / (R * Q) :=
    div_nonneg (mul_nonneg hK (Real.rpow_nonneg hN0pos.le _)) (mul_nonneg hR hQ.le)
  have hNe : 1 ≤ N0 ^ (2 * ε') := Real.one_le_rpow hN0 (by linarith)
  have hNe0 : 0 ≤ N0 ^ (2 * ε') := by linarith
  have h4 : (0 : ℝ) ≤ 4 ^ j := by positivity
  -- `(2^j)^h ≤ 4^j`
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hpow2j : ((2 : ℝ) ^ j) ^ h ≤ 4 ^ j := by
    calc ((2 : ℝ) ^ j) ^ h ≤ ((2 : ℝ) ^ j) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2j hh2
      _ = 4 ^ j := by rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]; norm_num
  -- `H^h ≤ 4^j (x+y)^h`
  have hHh : H ^ h ≤ 4 ^ j * (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q)) ^ h := by
    calc H ^ h ≤ (2 ^ j * (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q))) ^ h :=
          Real.rpow_le_rpow hH0 hH hh0
      _ = ((2 : ℝ) ^ j) ^ h * (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q)) ^ h :=
          Real.mul_rpow (by positivity) (by linarith)
      _ ≤ 4 ^ j * (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q)) ^ h :=
          mul_le_mul_of_nonneg_right hpow2j (Real.rpow_nonneg (by linarith) _)
  rcases le_or_gt (K * N0 ^ (1 + ε') / (R * Q)) (2 * T + 1) with hxy | hxy
  · -- case `y ≤ x`: `R²(x+y)^h ≤ R₁²(2x)² = 4R₁²x² ≤ 𝒵`
    have h1 : (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q)) ^ h ≤ 4 * (2 * T + 1) ^ 2 := by
      calc (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q)) ^ h ≤ (2 * (2 * T + 1)) ^ h :=
            Real.rpow_le_rpow (by linarith) (by linarith) hh0
        _ ≤ (2 * (2 * T + 1)) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hh2
        _ = 4 * (2 * T + 1) ^ 2 := by rw [Real.rpow_two]; ring
    have hR2 : R ^ 2 ≤ R1 ^ 2 := by nlinarith
    have hA : 0 ≤ 4 ^ j * (4 * (2 * T + 1) ^ 2) := by positivity
    calc R ^ 2 * H ^ h ≤ R ^ 2 * (4 ^ j * (4 * (2 * T + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hHh.trans (mul_le_mul_of_nonneg_left h1 h4)) (sq_nonneg R)
      _ ≤ R1 ^ 2 * (4 ^ j * (4 * (2 * T + 1) ^ 2)) := mul_le_mul_of_nonneg_right hR2 hA
      _ ≤ 4 ^ j * Zsize R1 T K N0 Q := by
          unfold Zsize
          have hB : 0 ≤ (K * N0 / Q) ^ 2 := sq_nonneg _
          have hC : 0 ≤ R1 ^ 2 * (2 * T + 1) ^ 2 := by positivity
          nlinarith [mul_nonneg h4 hB, mul_nonneg h4 hC]
      _ ≤ 4 ^ j * Zsize R1 T K N0 Q * N0 ^ (2 * ε') := by
          have hZ0 : 0 ≤ 4 ^ j * Zsize R1 T K N0 Q := by unfold Zsize; positivity
          nlinarith
  · -- case `x < y`: then `R > 0`, `Y := R y = K N₀^{1+ε'}/Q ≥ R`, and `R² y^h = R^{2-h} Y^h ≤ Y²`
    have hRpos : 0 < R := by
      rcases hR.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        rw [← heq, zero_mul, div_zero] at hxy
        linarith
    have hRy : R * (K * N0 ^ (1 + ε') / (R * Q)) = K * N0 ^ (1 + ε') / Q := by
      field_simp
    have hRY : R ≤ K * N0 ^ (1 + ε') / Q := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ K * N0 ^ (1 + ε') / (R * Q) by linarith) hR
      linarith
    have hYpos : 0 < K * N0 ^ (1 + ε') / Q := lt_of_lt_of_le hRpos hRY
    have h1 : (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q)) ^ h
        ≤ 4 * (K * N0 ^ (1 + ε') / (R * Q)) ^ h := by
      calc (2 * T + 1 + K * N0 ^ (1 + ε') / (R * Q)) ^ h
            ≤ (2 * (K * N0 ^ (1 + ε') / (R * Q))) ^ h :=
            Real.rpow_le_rpow (by linarith) (by linarith) hh0
        _ = (2 : ℝ) ^ h * (K * N0 ^ (1 + ε') / (R * Q)) ^ h := Real.mul_rpow (by norm_num) hy0
        _ ≤ 4 * (K * N0 ^ (1 + ε') / (R * Q)) ^ h := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy0 _)
            calc (2 : ℝ) ^ h ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hh2
              _ = 4 := by rw [Real.rpow_two]; norm_num
    have h2 : R ^ 2 * (K * N0 ^ (1 + ε') / (R * Q)) ^ h ≤ (K * N0 ^ (1 + ε') / Q) ^ 2 := by
      have e1 : R ^ 2 = R ^ (2 - h) * R ^ h := by
        rw [← Real.rpow_add hRpos, sub_add_cancel, Real.rpow_two]
      calc R ^ 2 * (K * N0 ^ (1 + ε') / (R * Q)) ^ h
            = R ^ (2 - h) * (R * (K * N0 ^ (1 + ε') / (R * Q))) ^ h := by
            rw [e1, Real.mul_rpow hR hy0]; ring
        _ = R ^ (2 - h) * (K * N0 ^ (1 + ε') / Q) ^ h := by rw [hRy]
        _ ≤ (K * N0 ^ (1 + ε') / Q) ^ (2 - h) * (K * N0 ^ (1 + ε') / Q) ^ h :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hR hRY (by linarith))
              (Real.rpow_nonneg hYpos.le _)
        _ = (K * N0 ^ (1 + ε') / Q) ^ 2 := by
            rw [← Real.rpow_add hYpos, sub_add_cancel, Real.rpow_two]
    have hY2 : (K * N0 ^ (1 + ε') / Q) ^ 2 = (K * N0 / Q) ^ 2 * N0 ^ (2 * ε') := by
      have e2 : N0 ^ (2 * ε') = (N0 ^ ε') ^ 2 := by
        rw [mul_comm, Real.rpow_mul hN0pos.le, Real.rpow_two]
      rw [e2, Real.rpow_add hN0pos, Real.rpow_one]
      ring
    calc R ^ 2 * H ^ h ≤ R ^ 2 * (4 ^ j * (4 * (K * N0 ^ (1 + ε') / (R * Q)) ^ h)) :=
          mul_le_mul_of_nonneg_left (hHh.trans (mul_le_mul_of_nonneg_left h1 h4)) (sq_nonneg R)
      _ = 4 ^ j * 4 * (R ^ 2 * (K * N0 ^ (1 + ε') / (R * Q)) ^ h) := by ring
      _ ≤ 4 ^ j * 4 * (K * N0 ^ (1 + ε') / Q) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 4 ^ j * Zsize R1 T K N0 Q * N0 ^ (2 * ε') := by
          rw [hY2]
          unfold Zsize
          have hA : 0 ≤ R1 ^ 2 * (2 * T + 1) ^ 2 * N0 ^ (2 * ε') :=
            mul_nonneg (by positivity) hNe0
          have hB : 0 ≤ (K * N0 / Q) ^ 2 * N0 ^ (2 * ε') := mul_nonneg (sq_nonneg _) hNe0
          nlinarith [mul_nonneg h4 hA, mul_nonneg h4 hB]

end ZetaShell
