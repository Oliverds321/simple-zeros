/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaQ.Budget

/-!
# `hpre` — §7's tail prefactor at the design of record

Receipt: `audit/HPre_REPORT.md`.

The two prefactors:

* `prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 Qn`
    `= Cenv² · 2A₀ · (1 + log Qn/log(2T+4)) · sideW L (w/A) (4/e) (2T+4) D₀ / L`
  (`ZetaQ/Tail.lean`, the UNCOLLECTED [R] window weight), and
* `exp (logPrefactorGev P) = Cenv² · 2(ℒ + log 4T) · S(D₀)² / L`
  (`ZetaQ/Budget.lean`, §QT.b(5)'s COLLECTED form).

`Cenv` and `L` cancel, so `hpre` is exactly

    A₀ · (1 + log Qn/log(2T+4)) · sideW L (1/A) (4/e) (2T+4) D₀  ≤  (ℒ + log 4T) · S(D₀)².

Asymptotically `sideW ≈ log(2T+4) · (L/2π)(2A)² t²/c²` and `S² ≈ (L/2π)²(2A)² t²/c²`
(`t = √(D₀/A)`), so the inequality reads `A₀ · log(Qn(2T+4)) ≲ (ℒ + log 4T) · L/(2π)`,
i.e. **`A₀ ≲ L/(2π)`** — it holds for all large `Q`, but with the tree's local-count
constant `A₀ = EFChi.A0 = 81.26` it needs `L ≳ 511`, which FAILS at `Q = 10¹⁰⁰`
(`L/2π ≈ 47`).  The `A₀`-free form (`A₀ := 1`, i.e. `η = A₀` in the closing condition — the
normalisation the `logPrefactorGev` docstring itself describes) holds at every design point
with `ℒ ≥ 100`.  Both are proved below.
-/

open ZetaQ Real

namespace ZetaQ.HPre

/-! ## 0. Unfolding `monoW` at the four indices -/

theorem mW0 (b c D : ℝ) : Zeta23.Tail.monoW b c D 0
    = 3 + 2 / b * ((Real.sqrt (b * D) + Real.sqrt b) / c + 1 / c * (1 / c)) := by
  simp [Zeta23.Tail.monoW, Zeta23.Tail.gammaPoly]

theorem mW1 (b c D : ℝ) : Zeta23.Tail.monoW b c D 1
    = ((1 / c) ^ 2 / b + 3) * (Real.sqrt (b * D) + 1 / c + Real.sqrt b)
      + 2 / b * ((Real.sqrt (b * D) + 1 / c + Real.sqrt b) ^ 2 / c
        + 2 / c * ((Real.sqrt (b * D) + 1 / c + Real.sqrt b) / c + 1 / c * (1 / c))) := by
  simp [Zeta23.Tail.monoW, Zeta23.Tail.gammaPoly]

theorem mW2 (b c D : ℝ) : Zeta23.Tail.monoW b c D 2
    = ((2 / c) ^ 2 / b + 3) * (Real.sqrt (b * D) + 2 / c + Real.sqrt b) ^ 2
      + 2 / b * ((Real.sqrt (b * D) + 2 / c + Real.sqrt b) ^ 3 / c
        + 3 / c * ((Real.sqrt (b * D) + 2 / c + Real.sqrt b) ^ 2 / c
          + 2 / c * ((Real.sqrt (b * D) + 2 / c + Real.sqrt b) / c + 1 / c * (1 / c)))) := by
  simp [Zeta23.Tail.monoW, Zeta23.Tail.gammaPoly]

theorem mW3 (b c D : ℝ) : Zeta23.Tail.monoW b c D 3
    = ((3 / c) ^ 2 / b + 3) * (Real.sqrt (b * D) + 3 / c + Real.sqrt b) ^ 3
      + 2 / b * ((Real.sqrt (b * D) + 3 / c + Real.sqrt b) ^ 4 / c
        + 4 / c * ((Real.sqrt (b * D) + 3 / c + Real.sqrt b) ^ 3 / c
          + 3 / c * ((Real.sqrt (b * D) + 3 / c + Real.sqrt b) ^ 2 / c
            + 2 / c * ((Real.sqrt (b * D) + 3 / c + Real.sqrt b) / c + 1 / c * (1 / c))))) := by
  simp [Zeta23.Tail.monoW, Zeta23.Tail.gammaPoly]

/-! ## 1. The four monomial-window bounds, in the regime `t ≥ 33`, `b = 1/A ∈ [1/14, 1/13]`,
`c = 4/e ∈ [1.4, 1.5]`.  Throughout `κ = 2/b`, `t = √(bD)`, `s = √b`. -/

/-- `c·m₀ ≤ κ(t + 1.2)`. -/
theorem m0_bound {t s c κ : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 0.278)
    (hc : 1.4 ≤ c) (hc' : c ≤ 1.5) (hκ : 26 ≤ κ) :
    c * (3 + κ * ((t + s) / c + 1 / c * (1 / c))) ≤ κ * (t + 1.2) := by
  have hc0 : 0 < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hκ0 : 0 ≤ κ := by linarith
  have hic : 1 / c ≤ 0.7143 := by rw [div_le_iff₀ hc0]; linarith
  have e : c * (3 + κ * ((t + s) / c + 1 / c * (1 / c)))
      = 3 * c + κ * (t + s) + κ * (1 / c) := by
    field_simp
    ring
  have f1 := mul_le_mul_of_nonneg_left hic hκ0
  have f2 := mul_le_mul_of_nonneg_left hs hκ0
  linarith [e, f1, f2]

/-- `c·m₁ ≤ κ(t + 2)²`. -/
theorem m1_bound {t s c b κ : ℝ} (ht : 33 ≤ t) (hs0 : 0 ≤ s) (hs : s ≤ 0.278)
    (hc : 1.4 ≤ c) (hc' : c ≤ 1.5) (hκ : 26 ≤ κ) (hb : 0 < b) (hκb : κ * b = 2) :
    c * (((1 / c) ^ 2 / b + 3) * (t + 1 / c + s)
      + κ * ((t + 1 / c + s) ^ 2 / c + 2 / c * ((t + 1 / c + s) / c + 1 / c * (1 / c))))
    ≤ κ * (t + 2) ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hκ0 : 0 ≤ κ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hic : 1 / c ≤ 0.7143 := by rw [div_le_iff₀ hc0]; linarith
  have hic0 : 0 ≤ 1 / c := by positivity
  have hic2 : (1 / c) ^ 2 ≤ 0.5103 := by
    have := mul_le_mul hic hic hic0 (by norm_num)
    nlinarith [this]
  have hinvb : 1 / b = κ / 2 := by
    rw [div_eq_iff (ne_of_gt hb)]; linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = t + 1 / c + s := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hudef]; linarith
  have hu1 : u ≤ t + 1 := by rw [hudef]; linarith
  have e : c * (((1 / c) ^ 2 / b + 3) * u
        + κ * (u ^ 2 / c + 2 / c * (u / c + 1 / c * (1 / c))))
      = κ * u * (1 / c) / 2 + 3 * c * u + κ * u ^ 2 + 2 * κ * u * (1 / c)
        + 2 * κ * (1 / c) ^ 2 := by
    rw [show (1 / c) ^ 2 / b = (1 / c) ^ 2 * (κ / 2) by rw [div_eq_mul_one_div, hinvb]]
    field_simp
    ring
  rw [← hudef]
  have f1 : κ * u ^ 2 ≤ κ * (t + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hu1 2) hκ0
  have f2 : κ * u * (1 / c) ≤ κ * u * 0.7143 := mul_le_mul_of_nonneg_left hic (by positivity)
  have f3 : c * u ≤ 1.5 * u := mul_le_mul_of_nonneg_right hc' hu0
  have f4 : 4.5 * u ≤ 0.1731 * (κ * u) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 0.1731 * κ - 4.5) hu0
    linarith
  have f5 : κ * (1 / c) ^ 2 ≤ κ * 0.5103 := mul_le_mul_of_nonneg_left hic2 hκ0
  have f6 : κ * u ≤ κ * (t + 1) := mul_le_mul_of_nonneg_left hu1 hκ0
  have f7 : 0 ≤ κ * t := mul_nonneg hκ0 ht0
  linarith [e, f1, f2, f3, f4, f5, f6, f7]

/-- `c·m₂ ≤ 2κ t³`. -/
theorem m2_bound {t s c b κ : ℝ} (ht : 33 ≤ t) (hs0 : 0 ≤ s) (hs : s ≤ 0.278)
    (hc : 1.4 ≤ c) (hc' : c ≤ 1.5) (hκ : 26 ≤ κ) (hb : 0 < b) (hκb : κ * b = 2) :
    c * (((2 / c) ^ 2 / b + 3) * (t + 2 / c + s) ^ 2
      + κ * ((t + 2 / c + s) ^ 3 / c
        + 3 / c * ((t + 2 / c + s) ^ 2 / c
          + 2 / c * ((t + 2 / c + s) / c + 1 / c * (1 / c)))))
    ≤ κ * (2 * t ^ 3) := by
  have hc0 : 0 < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hκ0 : 0 ≤ κ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hic : 1 / c ≤ 0.7143 := by rw [div_le_iff₀ hc0]; linarith
  have hic0 : 0 ≤ 1 / c := by positivity
  have hic2 : (1 / c) ^ 2 ≤ 0.5103 := by
    have := mul_le_mul hic hic hic0 (by norm_num)
    nlinarith [this]
  have hic3 : (1 / c) ^ 3 ≤ 0.3646 := by
    have := mul_le_mul hic2 hic hic0 (by norm_num)
    nlinarith [this]
  have h2c : 2 / c ≤ 1.4286 := by rw [div_le_iff₀ hc0]; linarith
  have hinvb : 1 / b = κ / 2 := by
    rw [div_eq_iff (ne_of_gt hb)]; linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = t + 2 / c + s := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have hu1 : u ≤ 1.1 * t := by rw [hudef]; linarith
  have e : c * (((2 / c) ^ 2 / b + 3) * u ^ 2
        + κ * (u ^ 3 / c + 3 / c * (u ^ 2 / c + 2 / c * (u / c + 1 / c * (1 / c)))))
      = 2 * κ * (1 / c) * u ^ 2 + 3 * c * u ^ 2 + κ * u ^ 3 + 3 * κ * (1 / c) * u ^ 2
        + 6 * κ * (1 / c) ^ 2 * u + 6 * κ * (1 / c) ^ 3 := by
    rw [show (2 / c) ^ 2 / b = (2 / c) ^ 2 * (κ / 2) by rw [div_eq_mul_one_div, hinvb]]
    field_simp
    ring
  rw [← hudef]
  have g3 : u ^ 3 ≤ (1.1 * t) ^ 3 := pow_le_pow_left₀ hu0 hu1 3
  have g2 : u ^ 2 ≤ (1.1 * t) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
  have f1 : κ * u ^ 3 ≤ κ * (1.1 * t) ^ 3 := mul_le_mul_of_nonneg_left g3 hκ0
  have f2 : κ * (1 / c) * u ^ 2 ≤ κ * 0.7143 * (1.1 * t) ^ 2 := by
    have : κ * (1 / c) ≤ κ * 0.7143 := mul_le_mul_of_nonneg_left hic hκ0
    exact mul_le_mul this g2 (by positivity) (by positivity)
  have f3 : c * u ^ 2 ≤ 1.5 * (1.1 * t) ^ 2 :=
    mul_le_mul hc' g2 (by positivity) (by positivity)
  have f4 : κ * (1 / c) ^ 2 * u ≤ κ * 0.5103 * (1.1 * t) := by
    have : κ * (1 / c) ^ 2 ≤ κ * 0.5103 := mul_le_mul_of_nonneg_left hic2 hκ0
    exact mul_le_mul this hu1 hu0 (by positivity)
  have f5 : κ * (1 / c) ^ 3 ≤ κ * 0.3646 := mul_le_mul_of_nonneg_left hic3 hκ0
  have p2 : t ^ 2 * 33 ≤ t ^ 2 * t := mul_le_mul_of_nonneg_left ht (pow_nonneg ht0 2)
  have p1 : t * 33 ^ 2 ≤ t * t ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) ht 2) ht0
  have p0 : (33 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht 3
  have q2 := mul_le_mul_of_nonneg_left p2 hκ0
  have q1 := mul_le_mul_of_nonneg_left p1 hκ0
  have q0 := mul_le_mul_of_nonneg_left p0 hκ0
  have r2 : 4.5 * t ^ 2 ≤ 0.1731 * (κ * t ^ 2) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 0.1731 * κ - 4.5) (pow_nonneg ht0 2)
    linarith
  linarith [e, f1, f2, f3, f4, f5, q2, q1, q0, r2]

/-- `c·m₃ ≤ 2κ t⁴`. -/
theorem m3_bound {t s c b κ : ℝ} (ht : 33 ≤ t) (hs0 : 0 ≤ s) (hs : s ≤ 0.278)
    (hc : 1.4 ≤ c) (hc' : c ≤ 1.5) (hκ : 26 ≤ κ) (hb : 0 < b) (hκb : κ * b = 2) :
    c * (((3 / c) ^ 2 / b + 3) * (t + 3 / c + s) ^ 3
      + κ * ((t + 3 / c + s) ^ 4 / c
        + 4 / c * ((t + 3 / c + s) ^ 3 / c
          + 3 / c * ((t + 3 / c + s) ^ 2 / c
            + 2 / c * ((t + 3 / c + s) / c + 1 / c * (1 / c))))))
    ≤ κ * (2 * t ^ 4) := by
  have hc0 : 0 < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hκ0 : 0 ≤ κ := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hic : 1 / c ≤ 0.7143 := by rw [div_le_iff₀ hc0]; linarith
  have hic0 : 0 ≤ 1 / c := by positivity
  have hic2 : (1 / c) ^ 2 ≤ 0.5103 := by
    have := mul_le_mul hic hic hic0 (by norm_num)
    nlinarith [this]
  have hic3 : (1 / c) ^ 3 ≤ 0.3646 := by
    have := mul_le_mul hic2 hic hic0 (by norm_num)
    nlinarith [this]
  have hic4 : (1 / c) ^ 4 ≤ 0.2605 := by
    have := mul_le_mul hic2 hic2 (by positivity) (by norm_num)
    nlinarith [this]
  have h3c : 3 / c ≤ 2.1429 := by rw [div_le_iff₀ hc0]; linarith
  have hinvb : 1 / b = κ / 2 := by
    rw [div_eq_iff (ne_of_gt hb)]; linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = t + 3 / c + s := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have hu1 : u ≤ 1.1 * t := by rw [hudef]; linarith
  have e : c * (((3 / c) ^ 2 / b + 3) * u ^ 3
        + κ * (u ^ 4 / c + 4 / c * (u ^ 3 / c + 3 / c * (u ^ 2 / c
          + 2 / c * (u / c + 1 / c * (1 / c))))))
      = 4.5 * κ * (1 / c) * u ^ 3 + 3 * c * u ^ 3 + κ * u ^ 4 + 4 * κ * (1 / c) * u ^ 3
        + 12 * κ * (1 / c) ^ 2 * u ^ 2 + 24 * κ * (1 / c) ^ 3 * u + 24 * κ * (1 / c) ^ 4 := by
    rw [show (3 / c) ^ 2 / b = (3 / c) ^ 2 * (κ / 2) by rw [div_eq_mul_one_div, hinvb]]
    field_simp
    ring
  rw [← hudef]
  have g4 : u ^ 4 ≤ (1.1 * t) ^ 4 := pow_le_pow_left₀ hu0 hu1 4
  have g3 : u ^ 3 ≤ (1.1 * t) ^ 3 := pow_le_pow_left₀ hu0 hu1 3
  have g2 : u ^ 2 ≤ (1.1 * t) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
  have f1 : κ * u ^ 4 ≤ κ * (1.1 * t) ^ 4 := mul_le_mul_of_nonneg_left g4 hκ0
  have f2 : κ * (1 / c) * u ^ 3 ≤ κ * 0.7143 * (1.1 * t) ^ 3 := by
    have : κ * (1 / c) ≤ κ * 0.7143 := mul_le_mul_of_nonneg_left hic hκ0
    exact mul_le_mul this g3 (by positivity) (by positivity)
  have f3 : c * u ^ 3 ≤ 1.5 * (1.1 * t) ^ 3 :=
    mul_le_mul hc' g3 (by positivity) (by positivity)
  have f4 : κ * (1 / c) ^ 2 * u ^ 2 ≤ κ * 0.5103 * (1.1 * t) ^ 2 := by
    have : κ * (1 / c) ^ 2 ≤ κ * 0.5103 := mul_le_mul_of_nonneg_left hic2 hκ0
    exact mul_le_mul this g2 (by positivity) (by positivity)
  have f5 : κ * (1 / c) ^ 3 * u ≤ κ * 0.3646 * (1.1 * t) := by
    have : κ * (1 / c) ^ 3 ≤ κ * 0.3646 := mul_le_mul_of_nonneg_left hic3 hκ0
    exact mul_le_mul this hu1 hu0 (by positivity)
  have f6 : κ * (1 / c) ^ 4 ≤ κ * 0.2605 := mul_le_mul_of_nonneg_left hic4 hκ0
  have p3 : t ^ 3 * 33 ≤ t ^ 3 * t := mul_le_mul_of_nonneg_left ht (pow_nonneg ht0 3)
  have p2 : t ^ 2 * 33 ^ 2 ≤ t ^ 2 * t ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) ht 2) (pow_nonneg ht0 2)
  have p1 : t * 33 ^ 3 ≤ t * t ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) ht 3) ht0
  have p0 : (33 : ℝ) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ (by norm_num) ht 4
  have q3 := mul_le_mul_of_nonneg_left p3 hκ0
  have q2 := mul_le_mul_of_nonneg_left p2 hκ0
  have q1 := mul_le_mul_of_nonneg_left p1 hκ0
  have q0 := mul_le_mul_of_nonneg_left p0 hκ0
  have r3 : 4.5 * t ^ 3 ≤ 0.1731 * (κ * t ^ 3) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 0.1731 * κ - 4.5) (pow_nonneg ht0 3)
    linarith
  linarith [e, f1, f2, f3, f4, f5, f6, q3, q2, q1, q0, r3]

/-! ## 2. The collected bound on `sideW` -/

set_option maxHeartbeats 2000000 in
/-- **`sideW` at the design regime.**  With `K = (L/2π)(2/b)`, `κ = 2/b`, `t = √(bD)`:
`sideW L b c B D ≤ (Kκ/c²)·(t + 2.5)²·(log B + 2.1·D/B)`. -/
theorem sideW_le_design {L b c B D : ℝ} (hL : 100 ≤ L)
    (hb : 1 / 14 ≤ b) (hb' : b ≤ 1 / 13) (hc : 1.4 ≤ c) (hc' : c ≤ 1.5)
    (hD : 0 ≤ D) (hB : 1 < B) (ht : 33 ≤ Real.sqrt (b * D)) :
    Zeta23.Tail.sideW L b c B D
      ≤ L / (2 * Real.pi) * (2 / b) * (2 / b) / c ^ 2 * (Real.sqrt (b * D) + 2.5) ^ 2
          * (Real.log B + 2.1 * (D / B)) := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hb0 : 0 < b := by linarith
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hc0 : 0 < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hB0 : 0 < B := by linarith
  have hBne : B ≠ 0 := ne_of_gt hB0
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB.le
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.sqrt (b * D) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt b := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 2 / b := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = L / (2 * Real.pi) * κ := ⟨_, rfl⟩
  rw [← htdef] at ht ⊢
  have ht2 : t ^ 2 = b * D := by rw [htdef]; exact Real.sq_sqrt (by positivity)
  have hs2 : s ^ 2 = b := by rw [hsdef]; exact Real.sq_sqrt hb0.le
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have hs : s ≤ 0.278 := by
    by_contra h
    push Not at h
    have h2 : (0.278 : ℝ) * 0.278 < s * s := mul_lt_mul'' h h (by norm_num) (by norm_num)
    nlinarith [hs2, hb', h2]
  have ht0 : 0 ≤ t := by linarith
  have hκb : κ * b = 2 := by rw [hκdef]; field_simp
  have hκ : 26 ≤ κ := by rw [hκdef, le_div_iff₀ hb0]; linarith
  have hκ' : κ ≤ 28 := by rw [hκdef, div_le_iff₀ hb0]; linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hK : 400 ≤ K := by
    rw [hKdef]
    have h1 : 100 / (2 * Real.pi) ≤ L / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hL (by positivity)
    have h2 : (15.8 : ℝ) ≤ 100 / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h3 := mul_le_mul (le_trans h2 h1) hκ (by norm_num) (by positivity)
    linarith
  have hK0 : 0 ≤ K := by linarith
  have hic : 1 / c ≤ 0.7143 := by rw [div_le_iff₀ hc0]; linarith
  have hic0 : 0 ≤ 1 / c := by positivity
  have hKc : 266 ≤ K / c := by
    rw [le_div_iff₀ hc0]; linarith
  have hKc0 : 0 ≤ K / c := by positivity
  -- the four monomial bounds
  have hm0 := m0_bound (t := t) hs0 hs hc hc' hκ
  have hm1 := m1_bound ht hs0 hs hc hc' hκ hb0 hκb
  have hm2 := m2_bound ht hs0 hs hc hc' hκ hb0 hκb
  have hm3 := m3_bound ht hs0 hs hc hc' hκ hb0 hκb
  -- name the four monomial weights
  obtain ⟨m0, hm0def⟩ : ∃ m : ℝ, m = 3 + κ * ((t + s) / c + 1 / c * (1 / c)) := ⟨_, rfl⟩
  obtain ⟨m1, hm1def⟩ : ∃ m : ℝ, m = ((1 / c) ^ 2 / b + 3) * (t + 1 / c + s)
      + κ * ((t + 1 / c + s) ^ 2 / c + 2 / c * ((t + 1 / c + s) / c + 1 / c * (1 / c))) :=
    ⟨_, rfl⟩
  obtain ⟨m2, hm2def⟩ : ∃ m : ℝ, m = ((2 / c) ^ 2 / b + 3) * (t + 2 / c + s) ^ 2
      + κ * ((t + 2 / c + s) ^ 3 / c + 3 / c * ((t + 2 / c + s) ^ 2 / c
          + 2 / c * ((t + 2 / c + s) / c + 1 / c * (1 / c)))) := ⟨_, rfl⟩
  obtain ⟨m3, hm3def⟩ : ∃ m : ℝ, m = ((3 / c) ^ 2 / b + 3) * (t + 3 / c + s) ^ 3
      + κ * ((t + 3 / c + s) ^ 4 / c + 4 / c * ((t + 3 / c + s) ^ 3 / c
          + 3 / c * ((t + 3 / c + s) ^ 2 / c
            + 2 / c * ((t + 3 / c + s) / c + 1 / c * (1 / c))))) := ⟨_, rfl⟩
  rw [← hm0def] at hm0
  rw [← hm1def] at hm1
  rw [← hm2def] at hm2
  rw [← hm3def] at hm3
  -- `sideW` in these names
  have hW : Zeta23.Tail.sideW L b c B D
      = (1 + K * (s / c + 1 / c ^ 2)) * Real.log B * m0 + K / c * Real.log B * m1
        + (1 + K * (s / c + 1 / c ^ 2)) / (b * B) * m2 + K / c / (b * B) * m3 := by
    rw [hm0def, hm1def, hm2def, hm3def, hKdef, hκdef, htdef, hsdef]
    unfold Zeta23.Tail.sideW
    rw [mW0, mW1, mW2, mW3]
  rw [hW]
  -- nonnegativity of the pieces
  have hα0 : 0 ≤ 1 + K * (s / c + 1 / c ^ 2) := by positivity
  have hm0nn : 0 ≤ m0 := by rw [hm0def]; positivity
  have hm1nn : 0 ≤ m1 := by rw [hm1def]; positivity
  have hm2nn : 0 ≤ m2 := by rw [hm2def]; positivity
  have hm3nn : 0 ≤ m3 := by rw [hm3def]; positivity
  -- replace `mᵢ` by `(1/c)·(c·mᵢ)`
  have em : ∀ m : ℝ, m = 1 / c * (c * m) := fun m => by field_simp
  -- `α ≤ 0.9965 (K/c)`
  have hα : 1 + K * (s / c + 1 / c ^ 2) ≤ 0.9965 * (K / c) := by
    have h1 : K * (s / c) ≤ 0.278 * (K / c) := by
      have e : K * (s / c) = K / c * s := by ring
      rw [e]
      linarith [mul_le_mul_of_nonneg_left hs hKc0]
    have h2 : K * (1 / c ^ 2) ≤ 0.7143 * (K / c) := by
      have e : K * (1 / c ^ 2) = K / c * (1 / c) := by ring
      rw [e]
      linarith [mul_le_mul_of_nonneg_left hic hKc0]
    have h3 : 1 ≤ 0.004 * (K / c) := by linarith
    linarith
  -- the bracket `α(t+1.2) + (K/c)(t+2)² ≤ (K/c)(t+2.5)²`
  have hmain_core : (1 + K * (s / c + 1 / c ^ 2)) * (t + 1.2) + K / c * (t + 2) ^ 2
      ≤ K / c * (t + 2.5) ^ 2 := by
    have h5 : (1 + K * (s / c + 1 / c ^ 2)) * (t + 1.2) ≤ 0.9965 * (K / c) * (t + 1.2) :=
      mul_le_mul_of_nonneg_right hα (by linarith)
    have h6 : 0 ≤ K / c * t := by positivity
    linarith
  -- MAIN: `α log B m₀ + (K/c) log B m₁ ≤ Kκ/c² (t+2.5)² log B`
  have hmainB : (1 + K * (s / c + 1 / c ^ 2)) * Real.log B * m0 + K / c * Real.log B * m1
      ≤ K * κ / c ^ 2 * (t + 2.5) ^ 2 * Real.log B := by
    have a1 : (1 + K * (s / c + 1 / c ^ 2)) * Real.log B * m0
        ≤ (1 + K * (s / c + 1 / c ^ 2)) * Real.log B * (1 / c * (κ * (t + 1.2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [em m0]
      exact mul_le_mul_of_nonneg_left hm0 hic0
    have a2 : K / c * Real.log B * m1
        ≤ K / c * Real.log B * (1 / c * (κ * (t + 2) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [em m1]
      exact mul_le_mul_of_nonneg_left hm1 hic0
    have a3 : (1 + K * (s / c + 1 / c ^ 2)) * Real.log B * (1 / c * (κ * (t + 1.2)))
        + K / c * Real.log B * (1 / c * (κ * (t + 2) ^ 2))
        = Real.log B * κ * (1 / c) * ((1 + K * (s / c + 1 / c ^ 2)) * (t + 1.2)
            + K / c * (t + 2) ^ 2) := by ring
    have a4 : Real.log B * κ * (1 / c) * ((1 + K * (s / c + 1 / c ^ 2)) * (t + 1.2)
            + K / c * (t + 2) ^ 2)
        ≤ Real.log B * κ * (1 / c) * (K / c * (t + 2.5) ^ 2) :=
      mul_le_mul_of_nonneg_left hmain_core (by positivity)
    have a5 : Real.log B * κ * (1 / c) * (K / c * (t + 2.5) ^ 2)
        = K * κ / c ^ 2 * (t + 2.5) ^ 2 * Real.log B := by ring
    linarith
  -- REMAINDER: `α/(bB) m₂ + (K/c)/(bB) m₃ ≤ Kκ/c² (t+2.5)² · 2.1 D/B`
  have hremB : (1 + K * (s / c + 1 / c ^ 2)) / (b * B) * m2 + K / c / (b * B) * m3
      ≤ K * κ / c ^ 2 * (t + 2.5) ^ 2 * (2.1 * (D / B)) := by
    have hbB : 0 < b * B := by positivity
    have b1 : (1 + K * (s / c + 1 / c ^ 2)) / (b * B) * m2
        ≤ (1 + K * (s / c + 1 / c ^ 2)) / (b * B) * (1 / c * (κ * (2 * t ^ 3))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [em m2]
      exact mul_le_mul_of_nonneg_left hm2 hic0
    have b2 : K / c / (b * B) * m3 ≤ K / c / (b * B) * (1 / c * (κ * (2 * t ^ 4))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [em m3]
      exact mul_le_mul_of_nonneg_left hm3 hic0
    -- the bracket: `α·2t³ + (K/c)·2t⁴ ≤ 2.1 (K/c) t⁴`
    have b3 : (1 + K * (s / c + 1 / c ^ 2)) * (2 * t ^ 3) + K / c * (2 * t ^ 4)
        ≤ 2.1 * (K / c) * t ^ 4 := by
      have h5 : (1 + K * (s / c + 1 / c ^ 2)) * (2 * t ^ 3)
          ≤ 0.9965 * (K / c) * (2 * t ^ 3) :=
        mul_le_mul_of_nonneg_right hα (by positivity)
      have h6 : t ^ 3 * 33 ≤ t ^ 3 * t := mul_le_mul_of_nonneg_left ht (pow_nonneg ht0 3)
      have h7 := mul_le_mul_of_nonneg_left h6 hKc0
      have h8 : 0 ≤ K / c * t ^ 4 := by positivity
      linarith
    have b4 : (1 + K * (s / c + 1 / c ^ 2)) / (b * B) * (1 / c * (κ * (2 * t ^ 3)))
        + K / c / (b * B) * (1 / c * (κ * (2 * t ^ 4)))
        = κ * (1 / c) / (b * B) * ((1 + K * (s / c + 1 / c ^ 2)) * (2 * t ^ 3)
            + K / c * (2 * t ^ 4)) := by ring
    have b5 : κ * (1 / c) / (b * B) * ((1 + K * (s / c + 1 / c ^ 2)) * (2 * t ^ 3)
            + K / c * (2 * t ^ 4))
        ≤ κ * (1 / c) / (b * B) * (2.1 * (K / c) * t ^ 4) :=
      mul_le_mul_of_nonneg_left b3 (by positivity)
    -- `t⁴/(bB) = t²·D/B`
    have b6 : κ * (1 / c) / (b * B) * (2.1 * (K / c) * t ^ 4)
        = K * κ / c ^ 2 * t ^ 2 * (2.1 * (D / B)) := by
      have : t ^ 4 = t ^ 2 * (b * D) := by rw [← ht2]; ring
      rw [this]
      field_simp
      try ring
    have b7 : K * κ / c ^ 2 * t ^ 2 * (2.1 * (D / B))
        ≤ K * κ / c ^ 2 * (t + 2.5) ^ 2 * (2.1 * (D / B)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have e : (t + 2.5) ^ 2 = t ^ 2 + 5 * t + 6.25 := by ring
      linarith [e, ht0]
    linarith
  have hKκ : L / (2 * Real.pi) * (2 / b) * (2 / b) / c ^ 2 = K * κ / c ^ 2 := by
    rw [hKdef, hκdef]
  rw [hKκ]
  linarith [hmainB, hremB]

/-! ## 3. The final arithmetic: `A₀·(1 + log q/log B)·sideW ≤ (ℒ + log 4T)·S²` -/

set_option maxHeartbeats 2000000 in
theorem final_arith {A₀ L t lB lq Λ D B K κ ic S sW : ℝ}
    (hA₀ : 0 < A₀) (hA₀L : 8 * A₀ ≤ L) (ht : 33 ≤ t)
    (hlB : 6 ≤ lB) (hlq : 0 ≤ lq) (hΛ : lB + lq ≤ Λ)
    (hDB0 : 0 ≤ D / B) (hDB : D / B ≤ 1 / 6)
    (hK : K = L / (2 * Real.pi) * κ) (hκ0 : 0 ≤ κ) (hic0 : 0 ≤ ic)
    (hsW : sW ≤ K * κ * ic ^ 2 * (t + 2.5) ^ 2 * (lB + 2.1 * (D / B)))
    (hS : K * t * ic ≤ S) :
    A₀ * (1 + lq / lB) * sW ≤ Λ * S ^ 2 := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hL0 : 0 < L := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have ht0 : 0 ≤ t := by linarith
  have hlB0 : 0 < lB := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hKt : 0 ≤ K * t * ic := by positivity
  have hS0 : 0 ≤ S := le_trans hKt hS
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ,
      W = K * κ * ic ^ 2 * (t + 2.5) ^ 2 * (lB + 2.1 * (D / B)) := ⟨_, rfl⟩
  rw [← hWdef] at hsW
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hfrac : 0 ≤ 1 + lq / lB := by positivity
  -- step 1: replace `sW` by `W`
  have s1 : A₀ * (1 + lq / lB) * sW ≤ A₀ * (1 + lq / lB) * W :=
    mul_le_mul_of_nonneg_left hsW (by positivity)
  -- step 2: `1 + lq/lB ≤ Λ/lB`
  have s2 : 1 + lq / lB ≤ Λ / lB := by
    rw [show (1 : ℝ) + lq / lB = (lB + lq) / lB by
      rw [add_div, div_self (ne_of_gt hlB0)]]
    exact div_le_div_of_nonneg_right hΛ hlB0.le
  have s3 : A₀ * (1 + lq / lB) * W ≤ A₀ * (Λ / lB) * W :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s2 hA₀.le) hW0
  -- step 4: `Λ S² ≥ Λ (K t ic)²`
  have s4 : Λ * (K * t * ic) ^ 2 ≤ Λ * S ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKt hS 2) hΛ0
  -- step 5: the core numeric inequality `2π A₀ (t+2.5)² (lB + 2.1 D/B) ≤ L t² lB`
  have n1 : (t + 2.5) ^ 2 ≤ 1.16 * t ^ 2 := by
    have := mul_nonneg (sub_nonneg.2 ht) (sub_nonneg.2 ht)
    nlinarith [this, ht]
  have n2 : lB + 2.1 * (D / B) ≤ 1.0584 * lB := by linarith
  have n3 : 2 * Real.pi * A₀ ≤ 0.7875 * L := by
    have := mul_le_mul_of_nonneg_right hpi'.le hA₀.le
    linarith
  have n4 : 2 * Real.pi * A₀ * ((t + 2.5) ^ 2 * (lB + 2.1 * (D / B))) ≤ L * t ^ 2 * lB := by
    have h1 : (t + 2.5) ^ 2 * (lB + 2.1 * (D / B)) ≤ 1.16 * t ^ 2 * (1.0584 * lB) :=
      mul_le_mul n1 n2 (by positivity) (by positivity)
    have h2 : 0 ≤ (t + 2.5) ^ 2 * (lB + 2.1 * (D / B)) := by positivity
    have h3 : 2 * Real.pi * A₀ * ((t + 2.5) ^ 2 * (lB + 2.1 * (D / B)))
        ≤ 0.7875 * L * (1.16 * t ^ 2 * (1.0584 * lB)) :=
      mul_le_mul n3 h1 h2 (by positivity)
    have h4 : 0 ≤ L * t ^ 2 * lB := by positivity
    linarith
  -- step 6: assemble `A₀ (Λ/lB) W ≤ Λ (K t ic)²`
  have s6 : A₀ * (Λ / lB) * W ≤ Λ * (K * t * ic) ^ 2 := by
    rw [hWdef, hK]
    have hKκ0 : 0 ≤ L / (2 * Real.pi) * κ * κ * ic ^ 2 := by positivity
    have e1 : A₀ * (Λ / lB) * (L / (2 * Real.pi) * κ * κ * ic ^ 2 * (t + 2.5) ^ 2
          * (lB + 2.1 * (D / B)))
        = Λ * (L / (2 * Real.pi) * κ * κ * ic ^ 2)
            * (A₀ * ((t + 2.5) ^ 2 * (lB + 2.1 * (D / B))) / lB) := by
      ring
    have e2 : Λ * (L / (2 * Real.pi) * κ * t * ic) ^ 2
        = Λ * (L / (2 * Real.pi) * κ * κ * ic ^ 2) * (L / (2 * Real.pi) * t ^ 2) := by
      ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hΛ0 hKκ0)
    rw [div_le_iff₀ hlB0]
    have : L / (2 * Real.pi) * t ^ 2 * lB = L * t ^ 2 * lB / (2 * Real.pi) := by ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith [n4]
  linarith

/-! ## 4. `hpre` at the design of record -/

/-- `2(2/e) = c₄ ∈ [1.4, 1.5]`. -/
theorem cgev_bounds : (1.4 : ℝ) ≤ 2 * (2 / Real.exp 1) ∧ 2 * (2 / Real.exp 1) ≤ 1.5 := by
  have hlo : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hhi : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  constructor
  · rw [show (2 : ℝ) * (2 / Real.exp 1) = 4 / Real.exp 1 by ring, le_div_iff₀ he]; linarith
  · rw [show (2 : ℝ) * (2 / Real.exp 1) = 4 / Real.exp 1 by ring, div_le_iff₀ he]; linarith

theorem cgev_eq_c4 : (2 : ℝ) * (2 / Real.exp 1) = c4 := by unfold c4; ring

theorem gevA_bounds : (13 : ℝ) ≤ gevreyA ∧ gevreyA ≤ 14 := by
  have hlo : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hhi : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  unfold gevreyA
  exact ⟨by rw [le_div_iff₀ he]; linarith, by rw [div_le_iff₀ he]; linarith⟩

theorem exp_six_le : Real.exp 6 ≤ 604 := by
  have h := Real.exp_one_lt_d9
  have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h6]
  have : Real.exp 1 ^ 6 ≤ 2.7182818286 ^ 6 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 6
  linarith

theorem lamStar_ge_one (F : Family) : 1 ≤ F.lamStar := by
  cases F <;>
    norm_num [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10, lamStarEvenDyad12]

/-- `w = 1` at the design for `r ≥ 3`. -/
theorem w_eq_one_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hLL1 : 1 ≤ P.LL) : P.w = 1 := by
  have hw : P.w = wDesign P.LL r := hdes.2.2.2.2.1
  rw [hw]
  unfold wDesign wStar
  exact max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))

/-- `L ≥ ℒ` at the design (`λ* ≥ 1`). -/
theorem LB_ge_LL_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hLL0 : 0 ≤ P.LL) : P.LL ≤ P.LB := by
  have hlam1 : (1 : ℝ) ≤ P.lam := by rw [hdes.2.2.2.1]; exact lamStar_ge_one F
  unfold ParamsQ.LB; nlinarith

set_option maxHeartbeats 2000000 in
/-- **`hpre` (and `hpre0`) from the closing condition's LOWER half**, over the facts it reads
(`Valid`, `Q`, `SideCondD0range`, `w = 1`, `ℒ, L ≥ 100`, and `hcc : needed ≤ c₄ t_{D₀}` — the
only use of the closing clause is `t_{D₀} ≥ 33` from `c₄ t ≥ L/2 ≥ 50`), under `8·A₀ ≤ L`.
Factored out of `hpre_of_design` so that it serves the margin design too
(`ClosingAtDesignM`'s lower half implies `hcc` since `m ≥ 0`; `Margin.hpre_of_designM`). -/
theorem hpre_of_closing (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hP : P.Valid) (hQ : P.Q = (Qn : ℝ)) (hD0r : SideCondD0range P) (hwe : P.w = 1)
    (hLL : 100 ≤ P.LL) (hLB : (100 : ℝ) ≤ P.LB)
    (hcc : P.LB / 2 + logPrefactorGev P + Real.log (P.LB / 1)
      ≤ c4 * Real.sqrt (P.w * P.D0 / gevreyA))
    (hA₀ : 1 ≤ A₀) (hA₀L : 8 * A₀ ≤ P.LB) :
    0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) ∧
    Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        ≤ logPrefactorGev P := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  obtain ⟨hA13, hA14⟩ := gevA_bounds
  obtain ⟨hc14, hc15⟩ := cgev_bounds
  have hA0 : (0 : ℝ) < gevreyA := by linarith
  have hAne : gevreyA ≠ 0 := ne_of_gt hA0
  -- regime facts
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hTne : P.T ≠ 0 := ne_of_gt hT0
  have hLL1 : (1 : ℝ) ≤ P.LL := by linarith
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hww : P.toParams.w = P.w := rfl
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hq1 : (1 : ℝ) ≤ (Qn : ℝ) := by rw [← hQ]; linarith
  have hq0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hlq : 0 ≤ Real.log (Qn : ℝ) := Real.log_nonneg hq1
  -- the buffer
  have hD10 : 10 * P.LB ≤ P.D0 := hD0r.1
  have hDT : P.D0 ≤ P.T / 3 := hD0r.2
  have hD0 : (0 : ℝ) < P.D0 := by linarith
  -- the window base
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 * P.T + 4 := ⟨_, rfl⟩
  have hB1 : (1 : ℝ) < B := by rw [hBdef]; linarith
  have hB0 : (0 : ℝ) < B := by linarith
  have hlB : (6 : ℝ) ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0, hBdef]; linarith [exp_six_le]
  have hlB0 : (0 : ℝ) < Real.log B := by linarith
  have hDB : P.D0 / B ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hB0 (by norm_num), hBdef]; linarith
  have hDB0 : 0 ≤ P.D0 / B := by positivity
  -- `b = 1/A`, `t = √(D₀/A)`, and `t ≥ L/3` from the closing condition
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = P.w / gevreyA := ⟨_, rfl⟩
  have hbe : b = 1 / gevreyA := by rw [hbdef, hwe]
  have hb14 : 1 / 14 ≤ b := by rw [hbe, div_le_div_iff₀ (by norm_num) hA0]; linarith
  have hb13 : b ≤ 1 / 13 := by rw [hbe, div_le_div_iff₀ hA0 (by norm_num)]; linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.sqrt (b * P.D0) := ⟨_, rfl⟩
  have htB : tBuffer P = t := by
    unfold tBuffer; rw [htdef, hbe, hwe]; congr 1; ring
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (2 : ℝ) * (2 / Real.exp 1) := ⟨_, rfl⟩
  have hc14' : 1.4 ≤ c := by rw [hcdef]; exact hc14
  have hc15' : c ≤ 1.5 := by rw [hcdef]; exact hc15
  have hc0 : 0 < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hc4c : c4 = c := by rw [hcdef, cgev_eq_c4]
  have hc40 : 0 < c4 := by rw [hc4c]; exact hc0
  have hc4le : c4 ≤ 1.5 := by rw [hc4c]; exact hc15'
  -- the needed side of the closing condition is ≥ L/2
  have hS1 : 1 ≤ rowSumFactor P := by
    unfold rowSumFactor tBuffer
    have hw0 : 0 < P.w := by rw [hwe]; norm_num
    have : 0 ≤ P.LB / (2 * Real.pi) * (2 * gevreyA / P.w)
        * (Real.sqrt (P.w * P.D0 / gevreyA) / c4 + 1 / c4 ^ 2) := by positivity
    linarith
  have hCenv1 : 1 ≤ CenvDesign P := by
    unfold CenvDesign
    have h1 : P.LB ≤ max (2 * P.gevreyBprod gevreyA gevreyB * P.w) P.LB := le_max_right _ _
    have h2 : (1 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h3 := mul_le_mul h2 (le_trans hLB h1) (by norm_num) (by positivity)
    linarith
  have hCenv0 : 0 < CenvDesign P := by linarith
  have hlog4T : 0 ≤ Real.log (4 * P.T) := Real.log_nonneg (by linarith)
  have hneed : 0 ≤ logPrefactorGev P + Real.log (P.LB / 1) := by
    unfold logPrefactorGev
    have h1 : 0 ≤ Real.log (CenvDesign P) := Real.log_nonneg hCenv1
    have h2 : 0 ≤ Real.log (2 * (P.LL + Real.log (4 * P.T))) :=
      Real.log_nonneg (by linarith)
    have h3 : 0 ≤ Real.log (rowSumFactor P) := Real.log_nonneg hS1
    rw [div_one]
    linarith
  have ht0 : 0 ≤ t := by rw [htdef]; exact Real.sqrt_nonneg _
  have ht33 : 33 ≤ t := by
    rw [show Real.sqrt (P.w * P.D0 / gevreyA) = tBuffer P from rfl, htB] at hcc
    have h1 : c4 * t ≤ 1.5 * t := mul_le_mul_of_nonneg_right hc4le ht0
    linarith
  -- `S ≥ K t/c` with `K = (L/2π)(2/b)`, `c = 2(2/e) = c₄`
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = P.LB / (2 * Real.pi) * (2 / b) := ⟨_, rfl⟩
  have hS : K * t * (1 / c) ≤ rowSumFactor P := by
    unfold rowSumFactor
    rw [htB, hwe, hc4c, hKdef, hbe, div_div_eq_mul_div, div_one]
    have h1 : 0 ≤ P.LB / (2 * Real.pi) * (2 * gevreyA) * (1 / c ^ 2) := by positivity
    have e : P.LB / (2 * Real.pi) * (2 * gevreyA) * (t / c + 1 / c ^ 2)
        = P.LB / (2 * Real.pi) * (2 * gevreyA) * t * (1 / c)
          + P.LB / (2 * Real.pi) * (2 * gevreyA) * (1 / c ^ 2) := by ring
    linarith [e, h1]
  -- the `sideW` bound
  have hside := sideW_le_design (L := P.LB) (b := b) (c := c) (B := B) (D := P.D0)
    hLB hb14 hb13 hc14' hc15' hD0.le hB1 (by rw [← htdef]; exact ht33)
  rw [← htdef] at hside
  -- `log B + log q ≤ ℒ + log 4T`
  have hΛ : Real.log B + Real.log (Qn : ℝ) ≤ P.LL + Real.log (4 * P.T) := by
    have e1 : P.LL = Real.log (Qn : ℝ) + Real.log P.T - Real.log (2 * Real.pi) := by
      unfold ParamsQ.LL
      rw [hQ, Real.log_div (mul_pos hq0 hT0).ne' (by positivity),
        Real.log_mul hq0.ne' hTne]
    have e2 : Real.log (4 * P.T) = Real.log 4 + Real.log P.T :=
      Real.log_mul (by norm_num) hTne
    have e3 : Real.log B ≤ Real.log 3 + Real.log P.T := by
      rw [← Real.log_mul (by norm_num) hTne]
      exact Real.log_le_log hB0 (by rw [hBdef]; linarith)
    have e4 : Real.log 3 + Real.log (2 * Real.pi) ≤ Real.log 4 + Real.log P.T := by
      rw [← Real.log_mul (by norm_num) (by positivity), ← Real.log_mul (by norm_num) hTne]
      exact Real.log_le_log (by positivity) (by linarith)
    linarith
  -- `sideW > 0`
  have hsideWpos : 0 < Zeta23.Tail.sideW P.LB b c B P.D0 := by
    unfold Zeta23.Tail.sideW
    rw [mW0]
    have hm1 := Zeta23.Tail.monoW_nonneg hb0 hc0 hD0.le 1
    have hm2 := Zeta23.Tail.monoW_nonneg hb0 hc0 hD0.le 2
    have hm3 := Zeta23.Tail.monoW_nonneg hb0 hc0 hD0.le 3
    have hα : 1 ≤ 1 + P.LB / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2) := by
      have : 0 ≤ P.LB / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2) := by
        positivity
      linarith
    have hm0 : 3 ≤ 3 + 2 / b * ((Real.sqrt (b * P.D0) + Real.sqrt b) / c + 1 / c * (1 / c)) := by
      have : 0 ≤ 2 / b * ((Real.sqrt (b * P.D0) + Real.sqrt b) / c + 1 / c * (1 / c)) := by
        positivity
      linarith
    have t1 : 3 * Real.log B
        ≤ (1 + P.LB / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2)) * Real.log B
          * (3 + 2 / b * ((Real.sqrt (b * P.D0) + Real.sqrt b) / c + 1 / c * (1 / c))) := by
      have h := mul_le_mul hα hm0 (by norm_num) (by linarith)
      have h' := mul_le_mul_of_nonneg_right h hlB0.le
      linarith
    have t2 : 0 ≤ P.LB / (2 * Real.pi) * (2 / b) / c * Real.log B
        * Zeta23.Tail.monoW b c P.D0 1 := by positivity
    have t3 : 0 ≤ (1 + P.LB / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2)) / (b * B)
        * Zeta23.Tail.monoW b c P.D0 2 := by positivity
    have t4 : 0 ≤ P.LB / (2 * Real.pi) * (2 / b) / c / (b * B)
        * Zeta23.Tail.monoW b c P.D0 3 := by positivity
    linarith
  have hA₀0 : 0 < A₀ := by linarith
  -- the collected inequality
  have hmain : A₀ * (1 + Real.log (Qn : ℝ) / Real.log B) * Zeta23.Tail.sideW P.LB b c B P.D0
      ≤ (P.LL + Real.log (4 * P.T)) * rowSumFactor P ^ 2 := by
    refine final_arith (L := P.LB) (t := t) (lB := Real.log B) (lq := Real.log (Qn : ℝ))
      (Λ := P.LL + Real.log (4 * P.T)) (D := P.D0) (B := B) (K := K) (κ := 2 / b)
      (ic := 1 / c) (S := rowSumFactor P) hA₀0 hA₀L ht33 hlB hlq hΛ hDB0 hDB hKdef
      (by positivity) (by positivity) ?_ hS
    have e : K * (2 / b) * (1 / c) ^ 2 = P.LB / (2 * Real.pi) * (2 / b) * (2 / b) / c ^ 2 := by
      rw [hKdef]; ring
    rw [e]
    exact hside
  -- unfold `prefactorQ` and finish
  have hfrac : 0 < 1 + Real.log (Qn : ℝ) / Real.log B := by
    have : 0 ≤ Real.log (Qn : ℝ) / Real.log B := div_nonneg hlq hlB0.le
    linarith
  have hX0 : 0 < 2 * A₀ * ((1 + Real.log (Qn : ℝ) / Real.log B)
      * Zeta23.Tail.sideW P.LB b c B P.D0) := by positivity
  have hpre_eq : prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
      = CenvDesign P ^ 2 * (2 * A₀ * ((1 + Real.log (Qn : ℝ) / Real.log B)
          * Zeta23.Tail.sideW P.LB b c B P.D0)) / P.LB := by
    unfold prefactorQ sideWQ
    rw [hLb, hww, ← hbdef, ← hcdef, ← hBdef]
  constructor
  · rw [hpre_eq]; positivity
  · rw [hpre_eq, Real.log_div (mul_pos (pow_pos hCenv0 2) hX0).ne' (ne_of_gt hLB0),
      Real.log_mul (pow_pos hCenv0 2).ne' hX0.ne', Real.log_pow]
    unfold logPrefactorGev
    have hS0 : 0 < rowSumFactor P := by linarith
    have hΛ0 : 0 < P.LL + Real.log (4 * P.T) := by linarith
    have h2 : 2 * Real.log (rowSumFactor P) = Real.log (rowSumFactor P ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    have key : Real.log (2 * A₀ * ((1 + Real.log (Qn : ℝ) / Real.log B)
          * Zeta23.Tail.sideW P.LB b c B P.D0))
        ≤ Real.log (2 * (P.LL + Real.log (4 * P.T))) + 2 * Real.log (rowSumFactor P) := by
      rw [h2, ← Real.log_mul (mul_pos two_pos hΛ0).ne' (pow_pos hS0 2).ne']
      apply Real.log_le_log hX0
      linarith [hmain]
    push_cast
    linarith

/-- **`hpre` (and `hpre0`) at the design of record**, in exactly the shape
`theta0Fam_le_of_design` / `tail_clauses_at_design_of_closing` consume, under
`r ≥ 3`, `ℒ ≥ 100` and the one genuinely necessary regime hypothesis `8·A₀ ≤ L`
(asymptotically `2π·A₀ ≲ L` is what the inequality says; see the header). -/
theorem hpre_of_design (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hA₀ : 1 ≤ A₀) (hA₀L : 8 * A₀ ≤ P.LB) :
    0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) ∧
    Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        ≤ logPrefactorGev P :=
  hpre_of_closing Qn P A₀ hdes.1 hdes.2.1 hdes.2.2.2.2.2.2.2.1
    (w_eq_one_of_design hdes hr (by linarith)) hLL
    (le_trans hLL (LB_ge_LL_of_design hdes (by linarith)))
    hdes.2.2.2.2.2.2.2.2.2.1.1 hA₀ hA₀L

/-- **The `A₀`-free form** (`η = A₀` in the closing condition): at every design point with
`r ≥ 3`, `ℒ ≥ 100`, `log(prefactorQ … A₀ …) ≤ logPrefactorGev P + log A₀`. -/
theorem hpre_of_design_A0 (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hA₀ : 1 ≤ A₀) :
    0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) ∧
    Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        ≤ logPrefactorGev P + Real.log A₀ := by
  have hLB : (100 : ℝ) ≤ P.LB := le_trans hLL (LB_ge_LL_of_design hdes (by linarith))
  obtain ⟨h0, h1⟩ := hpre_of_design F r ε Qn P 1 hdes hr hLL le_rfl (by linarith)
  have e : prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
      = A₀ * prefactorQ P.toParams P.T 1 gevreyA (CenvDesign P) P.D0 (Qn : ℝ) := by
    unfold prefactorQ; ring
  have hA₀0 : 0 < A₀ := by linarith
  refine ⟨by rw [e]; positivity, ?_⟩
  rw [e, Real.log_mul (ne_of_gt hA₀0) (ne_of_gt h0)]
  linarith

/-! ## 5. Consequences: `θ₀_fam ≤ A₀/L`, and the two §7 clauses with `hpre` DISCHARGED -/

/-- `ClosingAtDesign ⟹ θ₀_fam ≤ A₀/L` (the `η = A₀` reading), with no `hpre` hypothesis. -/
theorem theta0Fam_le_of_design_A0 (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hA₀ : 1 ≤ A₀) :
    theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) ≤ A₀ / P.LB := by
  obtain ⟨hpre0, hpre⟩ := hpre_of_design_A0 F r ε Qn P A₀ hdes hr hLL hA₀
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hcl : ClosingAtDesign P := hdes.2.2.2.2.2.2.2.2.2.1
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hww : P.toParams.w = P.w := rfl
  have hw : (0 : ℝ) < P.w := EFChi.w_pos_of_valid hP
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hL0 : (0 : ℝ) < P.toParams.L P.T := by rw [hLb]; exact hLB0
  have hA : (0 : ℝ) < gevreyA := by unfold gevreyA; positivity
  have hD0 : (0 : ℝ) ≤ P.D0 := by linarith [one_le_D0Q hP]
  have hA₀0 : (0 : ℝ) < A₀ := by linarith
  have hcc : P.LB / 2 + logPrefactorGev P + Real.log (P.LB / 1)
      ≤ c4 * Real.sqrt (P.w * P.D0 / gevreyA) := hcl.1
  have hc4 : c4 = 4 / Real.exp 1 := rfl
  rw [hc4, div_one] at hcc
  have hlogdiv : Real.log (P.LB / A₀) = Real.log P.LB - Real.log A₀ :=
    Real.log_div (ne_of_gt hLB0) (ne_of_gt hA₀0)
  have hclose : P.toParams.L P.T / 2
        + Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        + Real.log (P.toParams.L P.T / A₀)
      ≤ (4 / Real.exp 1) * Real.sqrt (P.toParams.w * P.D0 / gevreyA) := by
    rw [hLb, hww, hlogdiv]
    linarith
  have h := theta0Q_le_of_closing (η := A₀) hL0 hA₀0 hw hA hD0 hpre0 hclose
  rw [hLb] at h
  exact h

/-- `L₅ + L₉ ≤ 1` from `Valid` and `SideCondTfloor` (`T ≥ 300`, `T ≥ 10ℒ log ℒ`). -/
theorem L5_add_L9_le_one_of {P : ParamsQ} (hP : P.Valid)
    (hTf : 10 * P.LL * Real.log P.LL ≤ P.T) : L₅ P + L₉ P ≤ 1 := by
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have h5 : L₅ P ≤ 0.6 := by
    unfold L₅ cEnds
    rw [div_le_iff₀ hT0]; linarith
  have hd : dPdlogC ≤ 1 := by
    unfold dPdlogC
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]
  have hd0 : 0 ≤ dPdlogC := by
    unfold dPdlogC
    exact div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have h9 : L₉ P ≤ 0.001 := by
    unfold L₉
    rw [div_le_iff₀ hT0]; linarith
  linarith

/-- `L₅ + L₉ ≤ 1` at the design (`SideCondTfloor`, `T ≥ 300`). -/
theorem L5_add_L9_le_one {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) : L₅ P + L₉ P ≤ 1 :=
  L5_add_L9_le_one_of hdes.1 hdes.2.2.2.2.2.2.2.2.1

/-- **§7's two clauses from the design's own closing condition, `hpre` DISCHARGED.**
The only remaining input is the regime inequality `hregime`, now carrying the local-count
constant `A₀` on the left (the price of `θ₀ ≤ A₀/L` in place of `1/L`). -/
theorem tail_clauses_at_design_of_closing_A0 (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (A₀ : ℝ) (hQn : 2 ≤ Qn) (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hregime : A₀ * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P))
        ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P)) :
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
      (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) ∧
      (∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
        Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hA₀0 : (0 : ℝ) < A₀ := by linarith
  have hθle := theta0Fam_le_of_design_A0 F r ε Qn P A₀ hdes hr hLL hA₀
  have hk : (0 : ℝ) ≤ Real.sqrt (F.kappaC + rowR2 F P) := Real.sqrt_nonneg _
  have hL59 := L5_add_L9_le_one hdes
  have ha0 : (0 : ℝ) ≤ P.aQ := by linarith [hP.a_ge]
  have hpos : 0 ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) :=
    mul_nonneg (mul_nonneg ha0 (sq_nonneg _)) (Real.sqrt_nonneg _)
  -- `hsmall`
  have hsmall : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
        * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P))
      ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
        * (L₅ P + L₉ P) := by
    have hstep : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
          * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P))
        ≤ A₀ / P.LB * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P)) :=
      mul_le_mul_of_nonneg_right hθle (by linarith)
    refine le_trans hstep ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hLB0]
    have e : P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) * P.LB
        = P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) := by ring
    rw [e]; exact hregime
  -- `hone`: `A₀/L ≤ aL√(…)` ⟸ `A₀ ≤ aL²√(…)` ⟸ `hregime` and `L₅ + L₉ ≤ 1`
  have hone : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
      ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) := by
    refine le_trans hθle ?_
    rw [div_le_iff₀ hLB0]
    have h5 : 5 * A₀ ≤ A₀ * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P)) := by
      linarith [mul_nonneg hA₀0.le hk]
    have h6 := mul_le_mul_of_nonneg_left hL59 hpos
    linarith
  exact tail_clauses_at_design F r ε Qn P A₀ hQn hdes hϱ hA₀ hloc hone hsmall

/-! ## 6. TASK 2 — the regime inequality `hregime`, eventually in `Q`, for `r + ε ≤ 7`

`hregime : A₀·(5 + 2√(κ_C + r₂)) ≤ a·L²·√(T/(2π)·⟨ℒ⟩_low)·(L₅ + L₉)`.  At the design
`L = λ*ℒ`, `a ≥ 3/4`, `⟨ℒ⟩_low ≥ 0.9ℒ`, `L₅ = 6ℒ log ℒ/T`, so the right side is
`≳ 1.5·ℒ^{7/2 − (r+ε)/2}·log ℒ` once `T = (log Q)^{r+ε} ≤ ℒ^{r+ε}` is used, while the left
side is `O(A₀)` (crudely `≤ 23 A₀`, from `r₂ ≤ 79`).  Hence the inequality holds for all
large `Q` iff `r + ε ≤ 7` — and at `r + ε = 7` only through the `log ℒ`. -/

theorem kappaC_le_two (F : Family) : F.kappaC ≤ 2 := by
  cases F <;>
    norm_num [Family.kappaC, kappaCof, Family.payoff, Pconst, PconstDyadic, PconstEven,
      PconstEvenDyadic]

theorem Cconst_bounds' (F : Family) : 0 ≤ F.Cconst ∧ F.Cconst ≤ 19 := by
  have hpi0 := Real.pi_pos
  have h4 : Real.pi ^ 4 ≤ 98.5 := by
    have h := pow_le_pow_left₀ hpi0.le Real.pi_lt_d4.le 4
    nlinarith [h]
  have h0 : 0 ≤ Real.pi ^ 4 := by positivity
  cases F
  · show 0 ≤ Cfam ∧ Cfam ≤ 19
    unfold Cfam
    constructor
    · positivity
    · rw [div_le_iff₀ (by norm_num)]; linarith
  · show 0 ≤ CfamDyadic ∧ CfamDyadic ≤ 19
    unfold CfamDyadic
    constructor
    · positivity
    · rw [div_le_iff₀ (by norm_num)]; linarith
  · show 0 ≤ CfamEven ∧ CfamEven ≤ 19
    unfold CfamEven
    exact ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
  · show 0 ≤ CfamEven ∧ CfamEven ≤ 19
    unfold CfamEven
    exact ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
  · show 0 ≤ CfamEvenDyadic ∧ CfamEvenDyadic ≤ 19
    unfold CfamEvenDyadic
    exact ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
  · show 0 ≤ CfamEvenDyadic ∧ CfamEvenDyadic ≤ 19
    unfold CfamEvenDyadic
    exact ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
  · show 0 ≤ CfamEven ∧ CfamEven ≤ 19
    unfold CfamEven
    exact ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
  · show 0 ≤ CfamEven ∧ CfamEven ≤ 19
    unfold CfamEven
    exact ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
  · show 0 ≤ CfamEvenDyadic ∧ CfamEvenDyadic ≤ 19
    unfold CfamEvenDyadic
    exact ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
  · show 0 ≤ CfamEvenDyadic ∧ CfamEvenDyadic ≤ 19
    unfold CfamEvenDyadic
    exact ⟨by positivity, by rw [div_le_iff₀ (by norm_num)]; linarith⟩

theorem dPdlogC_bounds' : 0 ≤ dPdlogC ∧ dPdlogC ≤ 1 := by
  constructor
  · unfold dPdlogC
    exact div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  · unfold dPdlogC
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]

theorem cCross_le_three : cCross ≤ 3 := by
  unfold cCross
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have h : 24 / Real.pi ≤ 3 ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (by norm_num)] at this

/-- The crude bound `r₂ ≤ 79` over the facts it reads (`Valid`, `Q`, `log Q ≤ ℒ ≤ L`, `w = 1`)
at `log Q ≥ 200`. Factored out of `rowR2_le_design` so that it serves the margin design
too (`Margin.rowR2_le_designM`). -/
theorem rowR2_le_of_facts {F : Family} {Qn : ℕ} {P : ParamsQ}
    (hP : P.Valid) (hQ : P.Q = (Qn : ℝ)) (hLLu : Real.log (Qn : ℝ) ≤ P.LL)
    (hLB : P.LL ≤ P.LB) (hwe : P.w = 1) (hu : 200 ≤ Real.log (Qn : ℝ)) :
    rowR2 F P ≤ 79 := by
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hLL : 200 ≤ P.LL := le_trans hu hLLu
  have hLL0 : 0 < P.LL := by linarith
  have hLB0 : 0 < P.LB := by linarith
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : 0 < P.T := by linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  obtain ⟨hd0, hd1⟩ := dPdlogC_bounds'
  obtain ⟨hC0, hC19⟩ := Cconst_bounds' F
  have hcc0 : 0 ≤ cCross := Real.sqrt_nonneg _
  have hcc3 : cCross ≤ 3 := cCross_le_three
  have hlogQ : (200 : ℝ) ≤ Real.log P.Q := by rw [hQ]; exact hu
  have hlogQ0 : 0 < Real.log P.Q := by linarith
  have hlogLL0 : 0 ≤ Real.log P.LL := Real.log_nonneg (by linarith)
  have hlogLL : Real.log P.LL ≤ P.LL := by linarith [Real.log_le_sub_one_of_pos hLL0]
  have hlogLB0 : 0 ≤ Real.log P.LB := Real.log_nonneg (by linarith)
  have hlogLB : Real.log P.LB ≤ P.LB := by linarith [Real.log_le_sub_one_of_pos hLB0]
  -- the square root `√(log L/(TL)) ≤ 1`
  have hsqLB : Real.sqrt (Real.log P.LB / (P.T * P.LB)) ≤ 1 := by
    have h : Real.log P.LB / (P.T * P.LB) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ P.T by linarith) hLB0.le
      linarith
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_one] at this
  have hsqLB0 : 0 ≤ Real.sqrt (Real.log P.LB / (P.T * P.LB)) := Real.sqrt_nonneg _
  -- zone row ≤ 2.2 (`s_F ≤ 0.55` for both families, `1 − a ≤ δ′ + l/ℒ ≤ 4`)
  have hzone : zoneRowLinear F P ≤ 2.48 := by
    have hl0 : 0 < Zeta23.l P.T := EFChi.l_pos_of_valid hP
    have hlLL : Zeta23.l P.T ≤ P.LL := by
      show Real.log (P.T / (2 * Real.pi)) ≤ Real.log (P.Q * P.T / (2 * Real.pi))
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_div_iff_of_pos_right (by positivity)]
      linarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ P.Q by linarith) hT0.le]
    have hy1 : Zeta23.l P.T / P.LL ≤ 1 := by rw [div_le_one hLL0]; exact hlLL
    have hyy : 0 ≤ Zeta23.l P.T / P.LL := by positivity
    have hdp0 : 0 ≤ P.deltaPrime := by
      unfold ParamsQ.deltaPrime
      have : 0 ≤ Real.log (Real.log P.Q) := Real.log_nonneg (by linarith)
      positivity
    have hdp3 : P.deltaPrime ≤ 3 := by
      unfold ParamsQ.deltaPrime
      rw [div_le_iff₀ hlogQ0]
      have := Real.log_le_sub_one_of_pos hlogQ0
      linarith
    have hprod := mul_nonneg hdp0 hyy
    have hX : 1 - zoneFactor P ≤ 4 := by
      unfold zoneFactor; nlinarith [hprod, hy1, hdp3, hyy, hdp0]
    have hX0 : 0 ≤ 1 - zoneFactor P := by
      unfold zoneFactor; nlinarith [hprod, hy1, hdp3, hyy, hdp0, mul_nonneg hdp0 (sub_nonneg.2 hy1)]
    calc zoneRowLinear F P ≤ 62 / 100 * (1 - zoneFactor P) := zoneRowLinear_le F P hX0
      _ ≤ 62 / 100 * 4 := by linarith
      _ ≤ 2.48 := by norm_num
  -- L₃ ≤ 1
  have hL3 : L₃ P ≤ 1 := by
    unfold L₃ cRamp
    rw [hwe, div_le_iff₀ hLB0]; linarith
  -- L₇ ≤ 45
  have hL7 : L₇ F P ≤ 45 := by
    unfold L₇
    have hx0 : 0 < P.T * P.LL := by positivity
    have hlogx : Real.log (P.T * P.LL) ≤ P.T * P.LL := by
      linarith [Real.log_le_sub_one_of_pos hx0]
    have hin : F.Cconst * Real.log (P.T * P.LL) / (P.T * P.LL) ≤ 4.4 ^ 2 := by
      rw [div_le_iff₀ hx0]
      have h1 := mul_le_mul_of_nonneg_left hlogx hC0
      have h2 := mul_le_mul_of_nonneg_right hC19 hx0.le
      linarith
    have hsq : Real.sqrt (F.Cconst * Real.log (P.T * P.LL) / (P.T * P.LL)) ≤ 4.4 := by
      have := Real.sqrt_le_sqrt hin
      rwa [Real.sqrt_sq (by norm_num)] at this
    have := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 1.3 * 7.7)
    linarith
  -- L₈ ≤ 3
  have hL8 : L₈ P ≤ 3 := by
    unfold L₈
    have h1 : dPdlogC * cCross ≤ 1 * 3 := mul_le_mul hd1 hcc3 hcc0 (by norm_num)
    have := mul_le_mul h1 hsqLB hsqLB0 (by norm_num)
    linarith
  -- L₁₀ ≤ 3
  have hL10 : L₁₀ P ≤ 3 := by
    unfold L₁₀
    rw [div_le_iff₀ (pow_pos hLB0 2)]
    have h1 : Real.log P.LL ≤ P.LB := le_trans hlogLL hLB
    have h2 : Real.log P.LL ^ 2 ≤ P.LB ^ 2 := pow_le_pow_left₀ hlogLL0 h1 2
    linarith
  -- L₁₁ ≤ 1
  have hL11 : L₁₁ P ≤ 1 := by
    unfold L₁₁
    have hneg : (P.lam - 2) * Real.log P.Q ≤ 0 := by
      have := mul_le_mul_of_nonneg_right (show P.lam - 2 ≤ 0 by linarith [hP.lam_lt_two])
        hlogQ0.le
      linarith
    have hexp : Real.exp ((P.lam - 2) * Real.log P.Q) ≤ 1 := Real.exp_le_one_iff.mpr hneg
    have := mul_le_mul hd1 hexp (Real.exp_pos _).le (by norm_num)
    linarith
  -- L₁₂ ≤ 20
  have hL12 : L₁₂ F P ≤ 20 := by
    unfold L₁₂ sensInzone
    have h1 : 0.35 * F.Cconst ≤ 0.35 * 19 := mul_le_mul_of_nonneg_left hC19 (by norm_num)
    have h2 : 0.35 * F.Cconst * cCross ≤ 0.35 * 19 * 3 :=
      mul_le_mul h1 hcc3 hcc0 (by norm_num)
    have h3 := mul_le_mul h2 hsqLB hsqLB0 (by norm_num)
    linarith
  unfold rowR2
  linarith

/-- The crude bound `r₂ ≤ 79` at any design point with `log Q ≥ 200`. -/
theorem rowR2_le_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hu : 200 ≤ Real.log (Qn : ℝ)) :
    rowR2 F P ≤ 79 := by
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hQn1 : 1 ≤ Qn := by
    have : (1 : ℝ) ≤ (Qn : ℝ) := by rw [← hQ]; linarith
    exact_mod_cast this
  have hLLu : Real.log (Qn : ℝ) ≤ P.LL := LL_ge_log_of_design hdes hQn1
  have hLL0 : 0 < P.LL := by linarith
  exact rowR2_le_of_facts hP hQ hLLu (LB_ge_LL_of_design hdes hLL0.le)
    (w_eq_one_of_design hdes hr (by linarith)) hu

set_option maxHeartbeats 1000000 in
/-- The right side of `hregime` at the design: `≥ 1.5·u^{7/2−(r+ε)/2}·log u`, `u = log Q`. -/
theorem rhs_lower_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hε : 0 ≤ ε) (hre : r + ε ≤ 7)
    (hu : 200 ≤ Real.log (Qn : ℝ)) :
    1.5 * Real.log (Qn : ℝ) ^ (7 / 2 - (r + ε) / 2) * Real.log (Real.log (Qn : ℝ))
      ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) := by
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hQn1 : 1 ≤ Qn := by
    have : (1 : ℝ) ≤ (Qn : ℝ) := by rw [← hQ]; linarith
    exact_mod_cast this
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Real.log (Qn : ℝ) := ⟨_, rfl⟩
  rw [← hudef] at hu ⊢
  have hu0 : 0 < u := by linarith
  have hLLu : u ≤ P.LL := by rw [hudef]; exact LL_ge_log_of_design hdes hQn1
  have hLL : 200 ≤ P.LL := le_trans hu hLLu
  have hLL0 : 0 < P.LL := by linarith
  have hLB : P.LL ≤ P.LB := LB_ge_LL_of_design hdes hLL0.le
  have hLB0 : 0 < P.LB := by linarith
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : 0 < P.T := by linarith
  have hTne : P.T ≠ 0 := ne_of_gt hT0
  have hTeq : P.T = u ^ (r + ε) := by rw [hudef]; exact T_of_design hdes
  have hre0 : 0 ≤ r + ε := by linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have ha : 3 / 4 ≤ P.aQ := hP.a_ge
  have ha0 : 0 ≤ P.aQ := by linarith
  -- `⟨ℒ⟩_low ≥ 0.9ℒ`
  have hfam : 0.9 * P.LL ≤ famAvgLlow F P := by
    unfold famAvgLlow famAvgL rvmSlack
    have := conductorShift_le_half F
    have := Real.log_two_gt_d9
    linarith
  have hfam0 : 0 ≤ famAvgLlow F P := by linarith
  -- `Y ≥ T·Z`, `Z = √(ℒ/(7T))`
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = Real.sqrt (P.LL / (7 * P.T)) := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact Real.sqrt_nonneg _
  have hYZ : P.T * Z ≤ Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) := by
    have e : P.T * Z = Real.sqrt (P.T ^ 2 * (P.LL / (7 * P.T))) := by
      rw [hZdef, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hT0.le]
    rw [e]
    apply Real.sqrt_le_sqrt
    have e2 : P.T ^ 2 * (P.LL / (7 * P.T)) = P.T * (P.LL / 7) := by
      field_simp
      try ring
    rw [e2]
    have h1 : P.LL / 7 ≤ famAvgLlow F P / (2 * Real.pi) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have := mul_le_mul_of_nonneg_left hpi'.le hLL0.le
      linarith
    have := mul_le_mul_of_nonneg_left h1 hT0.le
    calc P.T * (P.LL / 7) ≤ P.T * (famAvgLlow F P / (2 * Real.pi)) := this
      _ = P.T / (2 * Real.pi) * famAvgLlow F P := by ring
  -- `L₅ + L₉ ≥ 6ℒ log ℒ/T`
  have hL59 : 6 * P.LL * Real.log P.LL / P.T ≤ L₅ P + L₉ P := by
    have h9 : 0 ≤ L₉ P := by
      unfold L₉
      obtain ⟨hd0, -⟩ := dPdlogC_bounds'
      positivity
    have h5 : L₅ P = 6 * P.LL * Real.log P.LL / P.T := rfl
    linarith
  have hlogLL0 : 0 ≤ Real.log P.LL := Real.log_nonneg (by linarith)
  have hL59' : 0 ≤ 6 * P.LL * Real.log P.LL / P.T := by positivity
  -- RHS ≥ 4.5 ℒ³ log ℒ Z
  have hLB2 : P.LL ^ 2 ≤ P.LB ^ 2 := pow_le_pow_left₀ hLL0.le hLB 2
  have hstep : 3 / 4 * P.LL ^ 2 * (P.T * Z) * (6 * P.LL * Real.log P.LL / P.T)
      ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) := by
    have h1 : 3 / 4 * P.LL ^ 2 ≤ P.aQ * P.LB ^ 2 :=
      mul_le_mul ha hLB2 (by positivity) ha0
    have h2 : 3 / 4 * P.LL ^ 2 * (P.T * Z)
        ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) :=
      mul_le_mul h1 hYZ (by positivity) (by positivity)
    exact mul_le_mul h2 hL59 hL59' (by positivity)
  have hstep2 : 3 / 4 * P.LL ^ 2 * (P.T * Z) * (6 * P.LL * Real.log P.LL / P.T)
      = 4.5 * P.LL ^ 3 * Real.log P.LL * Z := by
    field_simp
    try ring
  -- `Z ≥ ℒ^{(1−(r+ε))/2}/3`
  have hTle : P.T ≤ P.LL ^ (r + ε) := by
    rw [hTeq]; exact Real.rpow_le_rpow hu0.le hLLu hre0
  have hrp0 : 0 < P.LL ^ (r + ε) := Real.rpow_pos_of_pos hLL0 _
  have hZge : P.LL ^ ((1 - (r + ε)) * (1 / 2)) / 3 ≤ Z := by
    rw [hZdef]
    have h1 : P.LL ^ (1 - (r + ε)) / 7 ≤ P.LL / (7 * P.T) := by
      rw [Real.rpow_sub hLL0, Real.rpow_one, div_div]
      exact div_le_div_of_nonneg_left hLL0.le (by positivity) (by linarith)
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_div (Real.rpow_nonneg hLL0.le _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hLL0.le] at h2
    have h7 : Real.sqrt 7 ≤ 3 := by
      have := Real.sqrt_le_sqrt (show (7 : ℝ) ≤ 3 ^ 2 by norm_num)
      rwa [Real.sqrt_sq (by norm_num)] at this
    have h70 : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : P.LL ^ ((1 - (r + ε)) * (1 / 2)) / 3
        ≤ P.LL ^ ((1 - (r + ε)) * (1 / 2)) / Real.sqrt 7 :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hLL0.le _) h70 h7
    linarith
  -- `ℒ³ · ℒ^{(1−(r+ε))/2} = ℒ^{7/2 − (r+ε)/2}`
  have hpow : P.LL ^ 3 * P.LL ^ ((1 - (r + ε)) * (1 / 2)) = P.LL ^ (7 / 2 - (r + ε) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLL0]
    congr 1
    push_cast
    ring
  have hδ0 : 0 ≤ 7 / 2 - (r + ε) / 2 := by linarith
  have hLLδ : u ^ (7 / 2 - (r + ε) / 2) ≤ P.LL ^ (7 / 2 - (r + ε) / 2) :=
    Real.rpow_le_rpow hu0.le hLLu hδ0
  have hlog : Real.log u ≤ Real.log P.LL := Real.log_le_log hu0 hLLu
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have c1 : 4.5 * P.LL ^ 3 * Real.log P.LL * (P.LL ^ ((1 - (r + ε)) * (1 / 2)) / 3)
      ≤ 4.5 * P.LL ^ 3 * Real.log P.LL * Z :=
    mul_le_mul_of_nonneg_left hZge (by positivity)
  have c2 : 4.5 * P.LL ^ 3 * Real.log P.LL * (P.LL ^ ((1 - (r + ε)) * (1 / 2)) / 3)
      = 1.5 * P.LL ^ (7 / 2 - (r + ε) / 2) * Real.log P.LL := by
    rw [← hpow]; ring
  have c3 : 1.5 * u ^ (7 / 2 - (r + ε) / 2) * Real.log u
      ≤ 1.5 * P.LL ^ (7 / 2 - (r + ε) / 2) * Real.log P.LL := by
    have := mul_le_mul hLLδ hlog hlogu0 (Real.rpow_nonneg hLL0.le _)
    linarith
  linarith [hstep, hstep2, c1, c2, c3]

/-- **`hregime`, eventually in `Q`, for every `r + ε ≤ 7`** (with the local-count constant
`A₀` on the left, as `tail_clauses_at_design_of_closing_A0` needs it; the `A₀`-free form of
`tail_clauses_at_design_of_closing` is the case `A₀ = 1`). -/
theorem hregime_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 ≤ ε) (hre : r + ε ≤ 7)
    (A₀ : ℝ) (hA₀ : 1 ≤ A₀) :
    ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      A₀ * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P))
        ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) := by
  have h1 : ∀ᶠ Qn : ℕ in Filter.atTop, (200 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 200
  have h2 : ∀ᶠ Qn : ℕ in Filter.atTop, 16 * A₀ ≤ Real.log (Real.log (Qn : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (16 * A₀)
  filter_upwards [h1, h2] with Qn hu hlu
  intro P hdes
  have hrow := rowR2_le_design hdes hr hu
  have hrhs := rhs_lower_design hdes hr hε hre hu
  have hκ := kappaC_le_two F
  have hr2 : 0 ≤ rowR2 F P := rowR2_nonneg F P hdes.1
  have hsq : Real.sqrt (F.kappaC + rowR2 F P) ≤ 9 := by
    have := Real.sqrt_le_sqrt (show F.kappaC + rowR2 F P ≤ 9 ^ 2 by linarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hA₀0 : 0 < A₀ := by linarith
  have hlhs : A₀ * (5 + 2 * Real.sqrt (F.kappaC + rowR2 F P)) ≤ 23 * A₀ := by
    have := mul_le_mul_of_nonneg_left hsq hA₀0.le
    linarith
  have hpow1 : 1 ≤ Real.log (Qn : ℝ) ^ (7 / 2 - (r + ε) / 2) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hprod : 16 * A₀ ≤ Real.log (Qn : ℝ) ^ (7 / 2 - (r + ε) / 2)
      * Real.log (Real.log (Qn : ℝ)) := by
    have h0 : 0 ≤ Real.log (Real.log (Qn : ℝ)) := by linarith
    have := mul_le_mul_of_nonneg_right hpow1 h0
    linarith
  linarith

/-- **Everything together, eventually in `Q`:** §7's two clauses at the design of record
from `DesignOfRecord` alone (plus the Gevrey ramp, the local count with its constant `A₀`),
for every `r + ε ≤ 7` — `hpre` and `hregime` both discharged. -/
theorem tail_clauses_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 ≤ ε)
    (hre : r + ε ≤ 7) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ →
      ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
        (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaC + rowR2 F P)
          + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) ∧
        (∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
          Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have h1 : ∀ᶠ Qn : ℕ in Filter.atTop, (200 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 200
  filter_upwards [h1, hregime_eventually F r ε hr hε hre A₀ hA₀,
    Filter.eventually_ge_atTop 2] with Qn hu hreg hQn
  intro P hdes hϱ
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : 100 ≤ P.LL := le_trans (by linarith) (LL_ge_log_of_design hdes hQn1)
  exact tail_clauses_at_design_of_closing_A0 F r ε Qn P A₀ hQn hdes hr hLL hϱ hA₀ hloc
    (hreg P hdes)

end ZetaQ.HPre
