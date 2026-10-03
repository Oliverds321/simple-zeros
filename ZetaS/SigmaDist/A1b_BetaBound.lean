/-
Node A1b (track K, all-marks) — lem:sigd-onslack, bound part (l.1130, proof l.1135–1136): for m ≥ 1 and
d = 1 − δ with 0 ≤ δ ≤ 1, "β = 1_{m=1} − 2md + m²d² ≥ m(m−2)1_{m≥3} − 2m(m−1)δ". Scalar.

Proof (L2_2): the difference RHS − LHS equals δ² for m = 1 and m²δ² for m ≥ 2 (exact algebra; the
hypothesis δ ≤ 1 is not needed).
-/
import ZetaS.Interfaces

namespace ZetaS

theorem beta_bound {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (if 3 ≤ m then (m : ℝ) * (m - 2) else 0) - 2 * m * (m - 1) * δ
      ≤ (if m = 1 then (1 : ℝ) else 0) - 2 * m * (1 - δ) + (m : ℝ) ^ 2 * (1 - δ) ^ 2 := by
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · -- m = 1 or m = 2
    interval_cases m
    · norm_num
      nlinarith [sq_nonneg δ]
    · norm_num
      nlinarith [sq_nonneg δ]
  · have hne : m ≠ 1 := by omega
    rw [if_pos h3, if_neg hne]
    nlinarith [sq_nonneg ((m : ℝ) * δ)]

end ZetaS
