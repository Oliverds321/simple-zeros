/-
Node L3b (track L) — the regularity part of lem:zeta-Phi (l.336): "Φ_m is increasing, concave and C¹ on [0,∞),
with Φ_m(0) = 0", in the form prop:zeta-pack uses it (l.410–413): for 0 < A and 0 ≤ E,
Φ_m(E) ≥ (Φ_m(A)/A)·min(E, A), for m ≥ 2.
Deps: Interfaces (PhiM).

Proof (L2_1): write `Φ_m(E) = E − ((u_E − 1)₊)²` with `u_E = √(kE)`, `k = (m−1)/m ∈ (0,1]` (`PhiMHelpers.PhiM_eq`).
  E ≥ A: monotonicity, `Φ(E) − Φ(A) = (E − A) − [((u_E−1)₊)² − ((u_A−1)₊)²] ≥ (u_E² − u_A²) − [...] ≥ 0`.
  E < A: `Φ(A)E ≤ Φ(E)A ⟺ ((u_E−1)₊)²A ≤ ((u_A−1)₊)²E ⟺ (u_E−1)₊ u_A ≤ (u_A−1)₊ u_E` (as `A = u_A²/k`, `E = u_E²/k`),
  true since `u_E ≤ u_A` (if `u_E > 1`: `(u_E − 1)u_A ≤ (u_A − 1)u_E ⟺ u_E ≤ u_A`). No concavity theory needed.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.PhiMHelpers

namespace ZetaS

theorem PhiM_ge_chord {m : ℕ} (hm : 2 ≤ m) {A E : ℝ} (hA : 0 < A) (hE : 0 ≤ E) :
    PhiM m A / A * min E A ≤ PhiM m E := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hk0 : 0 < ((m : ℝ) - 1) / m := div_pos (by linarith) hm0
  have hk1 : ((m : ℝ) - 1) / m ≤ 1 := by rw [div_le_one hm0]; linarith
  rw [PhiM_eq hm A, PhiM_eq hm E]
  have hu2 : Real.sqrt (((m : ℝ) - 1) * A / m) ^ 2 = ((m : ℝ) - 1) / m * A := by
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by linarith) hA.le) hm0.le)]; ring
  have hv2 : Real.sqrt (((m : ℝ) - 1) * E / m) ^ 2 = ((m : ℝ) - 1) / m * E := by
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by linarith) hE) hm0.le)]; ring
  have hu0 := Real.sqrt_nonneg (((m : ℝ) - 1) * A / m)
  have hv0 := Real.sqrt_nonneg (((m : ℝ) - 1) * E / m)
  generalize Real.sqrt (((m : ℝ) - 1) * A / m) = u at hu2 hu0 ⊢
  generalize Real.sqrt (((m : ℝ) - 1) * E / m) = v at hv2 hv0 ⊢
  generalize ((m : ℝ) - 1) / m = k at hk0 hk1 hu2 hv2
  rcases le_total E A with hEA | hAE
  · -- `min = E`: the chord from `0`.
    rw [min_eq_left hEA]
    have hvu : v ≤ u := by
      by_contra h; rw [not_le] at h
      nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hEA), mul_pos (sub_pos.mpr h) (sub_pos.mpr h),
        mul_nonneg (sub_pos.mpr h).le hu0]
    have key : max (v - 1) 0 * u ≤ max (u - 1) 0 * v := by
      rcases le_total v 1 with hv1 | hv1
      · rw [max_eq_right (by linarith : v - 1 ≤ 0), zero_mul]
        exact mul_nonneg (le_max_right _ _) hv0
      · rw [max_eq_left (by linarith : 0 ≤ v - 1), max_eq_left (by linarith : 0 ≤ u - 1)]
        nlinarith
    have key2 : (max (v - 1) 0 * u) * (max (v - 1) 0 * u) ≤ (max (u - 1) 0 * v) * (max (u - 1) 0 * v) :=
      mul_self_le_mul_self (mul_nonneg (le_max_right _ _) hu0) key
    have key3 : k * ((max (v - 1) 0) ^ 2 * A) ≤ k * ((max (u - 1) 0) ^ 2 * E) := by
      have e1 : (max (v - 1) 0 * u) * (max (v - 1) 0 * u) = k * ((max (v - 1) 0) ^ 2 * A) := by
        rw [show k * ((max (v - 1) 0) ^ 2 * A) = (max (v - 1) 0) ^ 2 * (k * A) by ring, ← hu2]; ring
      have e2 : (max (u - 1) 0 * v) * (max (u - 1) 0 * v) = k * ((max (u - 1) 0) ^ 2 * E) := by
        rw [show k * ((max (u - 1) 0) ^ 2 * E) = (max (u - 1) 0) ^ 2 * (k * E) by ring, ← hv2]; ring
      rw [← e1, ← e2]; exact key2
    have key4 := le_of_mul_le_mul_left key3 hk0
    rw [div_mul_eq_mul_div, div_le_iff₀ hA]
    nlinarith [key4]
  · -- `min = A`: monotonicity.
    rw [min_eq_right hAE, div_mul_cancel₀ _ hA.ne']
    have huv : u ≤ v := by
      by_contra h; rw [not_le] at h
      nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hAE), mul_pos (sub_pos.mpr h) (sub_pos.mpr h),
        mul_nonneg (sub_pos.mpr h).le hv0]
    have hdiff := sq_posPart_sub_le hu0 huv
    have hkE : v ^ 2 - u ^ 2 ≤ E - A := by
      rw [hu2, hv2]; nlinarith [mul_le_mul_of_nonneg_right hk1 (sub_nonneg.mpr hAE)]
    linarith

end ZetaS
