/-
L7_9 round 4: generic part of (a2) `model_outer`: for `w` with `w 0 = 0 = w (N+1)` and `0 < Δ ≤ 1/2`,
`Σ_{n≤N}|w(n)|² − ∫_{−Δ}^{Δ}|Σ w(n)e(nβ)|² ≤ (16Δ²)⁻¹ Σ_{n≤N+1}|w(n) − w(n−1)|²`
(Parseval on one period; `(1 − e(β))M(β) = Σ(w(n) − w(n−1))e(nβ)`; `|1 − e(β)| ≥ 4|β|` for `|β| ≤ 1/2`).
-/
import ZetaShell.Defs.LK_Defs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace LemmaK
namespace K6

lemma parseval_half (N : ℕ) (c : ℕ → ℂ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖ZetaQ.expSum N c β‖ ^ 2 = ZetaQ.l2sq N c := by
  have hper : Function.Periodic (fun β => ‖ZetaQ.expSum N c β‖ ^ 2) 1 := by
    intro β
    show ‖ZetaQ.expSum N c (β + 1)‖ ^ 2 = ‖ZetaQ.expSum N c β‖ ^ 2
    rw [show ZetaQ.expSum N c (β + 1) = ZetaQ.expSum N c β from
      ZetaQ.Gallagher.trig_periodic _ _ β]
  have h := hper.intervalIntegral_add_eq (-(1 / 2)) 0
  rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num, zero_add] at h
  rw [h, ZetaQ.Gallagher.integral_normSq_expSum]

/-- summation by parts: `Σ_{n≤N+1}(w(n) − w(n−1))e(nβ) = (1 − e(β))M(β) + w(N+1)e((N+1)β) − e(β)w(0)`. -/
lemma sbp_identity (w : ℕ → ℂ) (β : ℝ) (N : ℕ) :
    ZetaQ.expSum (N + 1) (fun n => w n - w (n - 1)) β
      = (1 - ZetaQ.e β) * ZetaQ.expSum N w β + w (N + 1) * ZetaQ.e (((N + 1 : ℕ) : ℝ) * β)
        - ZetaQ.e β * w 0 := by
  induction N with
  | zero =>
    unfold ZetaQ.expSum
    simp
    ring
  | succ N ih =>
    have h1 : ZetaQ.expSum (N + 1 + 1) (fun n => w n - w (n - 1)) β
        = ZetaQ.expSum (N + 1) (fun n => w n - w (n - 1)) β
          + (w (N + 2) - w (N + 1)) * ZetaQ.e (((N + 2 : ℕ) : ℝ) * β) := by
      unfold ZetaQ.expSum
      rw [Finset.sum_Ioc_succ_top (by omega)]
      simp only [Nat.add_sub_cancel]
    have h2 : ZetaQ.expSum (N + 1) w β = ZetaQ.expSum N w β + w (N + 1) * ZetaQ.e (((N + 1 : ℕ) : ℝ) * β) := by
      unfold ZetaQ.expSum
      rw [Finset.sum_Ioc_succ_top (by omega)]
    have h3 : ZetaQ.e β * ZetaQ.e (((N + 1 : ℕ) : ℝ) * β) = ZetaQ.e (((N + 2 : ℕ) : ℝ) * β) := by
      rw [← ZetaQ.e_add]; congr 1; push_cast; ring
    rw [h1, ih, h2]
    rw [show (N + 1 + 1 : ℕ) = N + 2 by ring]
    rw [← h3]
    ring

lemma jordan_e (β : ℝ) (hβ : |β| ≤ 1 / 2) : 4 * |β| ≤ ‖1 - ZetaQ.e β‖ := by
  rw [norm_sub_rev, ZetaQ.norm_e_sub_one]
  have hpi := Real.pi_pos
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → 2 * x ≤ Real.sin (Real.pi * x) := by
    intro x hx0 hx1
    have h := Real.mul_le_sin (x := Real.pi * x) (by positivity) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    linarith
  rcases le_or_gt 0 β with h | h
  · rw [abs_of_nonneg h] at hβ ⊢
    have := key β h hβ
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_neg h] at hβ ⊢
    have := key (-β) (by linarith) hβ
    rw [show Real.pi * β = -(Real.pi * -β) by ring, Real.sin_neg, abs_neg,
      abs_of_nonneg (by linarith)]
    linarith

/-- **the generic outer bound.** -/
theorem outer_le (N : ℕ) (w : ℕ → ℂ) (hw0 : w 0 = 0) (hwN : w (N + 1) = 0) (Δ : ℝ) (hΔ : 0 < Δ)
    (hΔ1 : Δ ≤ 1 / 2) :
    ZetaQ.l2sq N w - ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N w β‖ ^ 2
      ≤ (16 * Δ ^ 2)⁻¹ * ZetaQ.l2sq (N + 1) (fun n => w n - w (n - 1)) := by
  set f : ℝ → ℝ := fun β => ‖ZetaQ.expSum N w β‖ ^ 2 with hf
  set g : ℝ → ℝ := fun β => ‖ZetaQ.expSum (N + 1) (fun n => w n - w (n - 1)) β‖ ^ 2 with hg
  have hfc : Continuous f := (ZetaQ.Gallagher.continuous_trig _ _).norm.pow 2
  have hgc : Continuous g := (ZetaQ.Gallagher.continuous_trig _ _).norm.pow 2
  have hi : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hfc.intervalIntegrable _ _
  have hig : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hgc.intervalIntegrable _ _
  -- pointwise on the outer set
  have hpt : ∀ β, Δ ≤ |β| → |β| ≤ 1 / 2 → f β ≤ (16 * Δ ^ 2)⁻¹ * g β := by
    intro β h1 h2
    have hid := sbp_identity w β N
    rw [hw0, hwN, zero_mul, mul_zero, add_zero, sub_zero] at hid
    have hj := jordan_e β h2
    have hG : ‖ZetaQ.expSum (N + 1) (fun n => w n - w (n - 1)) β‖
        = ‖1 - ZetaQ.e β‖ * ‖ZetaQ.expSum N w β‖ := by rw [hid, norm_mul]
    have hM0 := norm_nonneg (ZetaQ.expSum N w β)
    have h4 : 4 * Δ * ‖ZetaQ.expSum N w β‖ ≤ ‖ZetaQ.expSum (N + 1) (fun n => w n - w (n - 1)) β‖ := by
      rw [hG]; nlinarith
    have h5 := pow_le_pow_left₀ (by positivity) h4 2
    simp only [hf, hg]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  -- split the period
  have hP := parseval_half N w
  have hPg := parseval_half (N + 1) (fun n => w n - w (n - 1))
  have hsplit : ∀ h : ℝ → ℝ, (∀ a b : ℝ, IntervalIntegrable h volume a b) →
      ∫ β in (-(1 / 2 : ℝ))..(1 / 2), h β
        = (∫ β in (-(1 / 2 : ℝ))..(-Δ), h β) + (∫ β in (-Δ)..Δ, h β) + ∫ β in Δ..(1 / 2), h β := by
    intro h hh
    rw [intervalIntegral.integral_add_adjacent_intervals (hh _ _) (hh _ _),
      intervalIntegral.integral_add_adjacent_intervals (hh _ _) (hh _ _)]
  have hL : ∫ β in (-(1 / 2 : ℝ))..(-Δ), f β ≤ (16 * Δ ^ 2)⁻¹ * ∫ β in (-(1 / 2 : ℝ))..(-Δ), g β := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith) (hi _ _) ((hig _ _).const_mul _)
    intro β hβ
    apply hpt β
    · rw [abs_of_neg (by linarith [hβ.2])]; linarith [hβ.2]
    · rw [abs_of_neg (by linarith [hβ.2])]; linarith [hβ.1]
  have hR : ∫ β in Δ..(1 / 2), f β ≤ (16 * Δ ^ 2)⁻¹ * ∫ β in Δ..(1 / 2), g β := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hΔ1 (hi _ _) ((hig _ _).const_mul _)
    intro β hβ
    apply hpt β
    · rw [abs_of_pos (by linarith [hβ.1])]; exact hβ.1
    · rw [abs_of_pos (by linarith [hβ.1])]; exact hβ.2
  have hmid : 0 ≤ ∫ β in (-Δ)..Δ, g β :=
    intervalIntegral.integral_nonneg (by linarith) (fun β _ => sq_nonneg _)
  have e1 := hsplit f hi
  have e2 := hsplit g hig
  rw [hP] at e1
  rw [hPg] at e2
  have hc : 0 ≤ (16 * Δ ^ 2)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left hmid hc
  simp only [hf] at e1 hL hR
  simp only [hg] at e2 hL hR this
  rw [e1, e2]
  nlinarith

end K6
end LemmaK
end ZetaShell
