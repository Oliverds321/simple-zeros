/-
L7_5 (28 Sep 2026), round 4: split of Step 4 (`Z5Z_oneZero`) into the draft's two regimes, with the derivation
COMPILED (`Z5Z_oneZero'`). `D = (|γ| − 2T)_+`, `ϖ = (1 + D/(μ+1))^{−k}`.
  * `ZO_trivial` (draft (i)): `μ² ‖I_ρ(·;μ,f_j)‖₂² ≤ C T` for all `ρ` in the strip (Young: `‖H_ρ‖₂ ‖f_j‖₁`, and
    `‖H_ρ‖₂² ≤ 2πe^{2κ}T`).  Used where `D ≤ μ+1`, where `ϖ ≥ 2^{−k}`.
  * `ZO_ibp` (draft (ii)): `μ² ‖I_ρ‖₂² ≤ C T ((μ+1)/D)^{2k}` when `D > μ+1` (`k+2` integrations by parts in `t`).
    Used where `D > μ+1`, where `ϖ ≥ 2^{−k}((μ+1)/D)^k`.
Each leaf is exactly Step 4 restricted to its range (up to the factor `4^k`), so the split adds no new claim.
Status: both leaves OPEN (sorry); `Z5Z_oneZero'` proved from them.
The definition `OneZeroBound` is moved here verbatim from ZZ2_OneZero.lean (which now imports this file).
-/
import ZetaShell.PropZ.ZZ0_Defs
import ZetaShell.PropZ.ZZ2b_Trivial
import ZetaShell.PropZ.ZZ2f_Ibp

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- the conclusion of Step 4, as a named Prop (consumed by `Z5Z_pair`). -/
def OneZeroBound (κ : ℝ) (Ξ f : ℝ → ℝ) (A k : ℕ) (C : ℝ) : Prop :=
  ∀ (T : ℝ), 2 ≤ T → ∀ (μ : ℝ), 0 < μ → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 → ∀ j ≤ A,
    μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ C * T * varpi T μ k ρ ^ 2


theorem ZO_trivial (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (μ : ℝ), 0 < μ → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 → ∀ j ≤ A,
      μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ C * T :=
  ZO_trivial' κ hκ hκ1 Ξ hΞ f hf A

theorem ZO_ibp (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (μ : ℝ), 0 < μ → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 →
      μ + 1 < |ρ.im| - 2 * T → ∀ j ≤ A,
      μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ C * T * ((μ + 1) / (|ρ.im| - 2 * T)) ^ (2 * k) :=
  ZO_ibp' κ hκ hκ1 Ξ hΞ f hf A k hk

theorem Z5Z_oneZero' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, OneZeroBound κ Ξ f A k C := by
  obtain ⟨C₁, hC₁0, h1⟩ := ZO_trivial κ hκ hκ1 Ξ hΞ f hf A
  obtain ⟨C₂, hC₂0, h2⟩ := ZO_ibp κ hκ hκ1 Ξ hΞ f hf A k hk
  refine ⟨4 ^ k * (C₁ + C₂), ?_⟩
  intro T hT μ hμ ρ hρ0 hρ1 j hj
  have hT0 : 0 ≤ T := by linarith
  have hμ1 : 0 < μ + 1 := by linarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = max (|ρ.im| - 2 * T) 0 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; exact le_max_right _ _
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (1 + D / (μ + 1)) ^ k := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hP]; positivity
  have hvp : varpi T μ k ρ = P⁻¹ := by
    unfold varpi
    rw [← hD, Real.rpow_neg (by positivity), Real.rpow_natCast, hP]
  have h4 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h4k : (0 : ℝ) < 4 ^ k := by positivity
  have hS : 0 ≤ C₁ + C₂ := by linarith
  -- target: it suffices that the bound is `≤ K T` with `K ≤ 4^k (C₁+C₂) ϖ²`
  rw [hvp]
  rcases le_or_gt D (μ + 1) with hle | hgt
  · have hq : 1 + D / (μ + 1) ≤ 2 := by
      have : D / (μ + 1) ≤ 1 := (div_le_one hμ1).mpr hle
      linarith
    have hpk : P ≤ 2 ^ k := by rw [hP]; exact pow_le_pow_left₀ (by positivity) hq k
    have hP2 : P ^ 2 ≤ 4 ^ k := by
      calc P ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ hP0.le hpk 2
        _ = 4 ^ k := h4
    have hv : 1 ≤ 4 ^ k * P⁻¹ ^ 2 := by
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]; exact hP2
    calc μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ C₁ * T := h1 T hT μ hμ ρ hρ0 hρ1 j hj
      _ ≤ (C₁ + C₂) * T := by nlinarith
      _ = (C₁ + C₂) * T * 1 := by ring
      _ ≤ (C₁ + C₂) * T * (4 ^ k * P⁻¹ ^ 2) := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = 4 ^ k * (C₁ + C₂) * T * P⁻¹ ^ 2 := by ring
  · have hDpos : 0 < D := by linarith
    have hDe : D = |ρ.im| - 2 * T := by
      rw [hD] at hgt ⊢
      rcases le_total (|ρ.im| - 2 * T) 0 with h | h
      · rw [max_eq_right h] at hgt; linarith
      · exact max_eq_left h
    have hgt' : μ + 1 < |ρ.im| - 2 * T := by rw [← hDe]; exact hgt
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (μ + 1) / D := ⟨_, rfl⟩
    have hq0 : 0 < q := by rw [hq]; positivity
    have hq1 : q < 1 := by rw [hq, div_lt_one hDpos]; exact hgt
    have hPq : P * q ^ k = (q + 1) ^ k := by
      rw [hP, ← mul_pow]
      congr 1
      rw [hq]; field_simp
    have hPq2 : P ^ 2 * q ^ (2 * k) ≤ 4 ^ k := by
      have e : P ^ 2 * q ^ (2 * k) = (P * q ^ k) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm k 2]
      rw [e, hPq, ← h4, ← pow_mul, ← pow_mul]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hv : q ^ (2 * k) ≤ 4 ^ k * P⁻¹ ^ 2 := by
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]; exact hPq2
    have hb := h2 T hT μ hμ ρ hρ0 hρ1 hgt' j hj
    rw [← hDe, ← hq] at hb
    have hq2k : 0 ≤ q ^ (2 * k) := by positivity
    calc μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ C₂ * T * q ^ (2 * k) := hb
      _ ≤ (C₁ + C₂) * T * q ^ (2 * k) := by
          apply mul_le_mul_of_nonneg_right _ hq2k; nlinarith
      _ ≤ (C₁ + C₂) * T * (4 ^ k * P⁻¹ ^ 2) := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = 4 ^ k * (C₁ + C₂) * T * P⁻¹ ^ 2 := by ring

end ZetaShell.PropZ
