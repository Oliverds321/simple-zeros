/-
L10c_ASH (L7_10c, 3 Oct 2026): **the hole of the near-P vector** (Lemma 4 for `b = a^{near,P}`):
`Hole(b) ≥ log R₀ · ((1 − t)A₀ − E/t) − 2‖b‖`, where `A₀ ≤ ∫_{|β|≤Δ}|S_{a′}|²` is the arc mass of any comparison
vector `a′` (Lemma K's `aPrime`, whose arc mass is K6) and `E ≥ ‖a′ − b‖²`; from `hole_lower_generic` (K7, with
`a = a′ = b`) and the pointwise `|x − y|² ≥ (1 − t)|x|² − |y|²/t`.
-/
import ZetaShell.ShellS.L10c_ASP
import ZetaShell.LemmaK.LK_K7_HoleGeneric
import ZetaShell.LemmaK.LK_K6_ArcMass

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace ShellS
namespace ASc

theorem normSq_sub_ge (x y : ℂ) (t : ℝ) (ht : 0 < t) :
    (1 - t) * ‖x‖ ^ 2 - ‖y‖ ^ 2 / t ≤ ‖x - y‖ ^ 2 := by
  have h1 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have h2 : (‖x‖ - ‖y‖) ^ 2 ≤ ‖x - y‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hamgm : 2 * ‖x‖ * ‖y‖ ≤ t * ‖x‖ ^ 2 + ‖y‖ ^ 2 / t := by
    have := sq_nonneg (t * ‖x‖ - ‖y‖)
    rw [div_eq_mul_inv]
    have ht' : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    nlinarith [mul_pos ht ht, inv_pos.mpr ht]
  have e : (‖x‖ - ‖y‖) ^ 2 = ‖x‖ ^ 2 - 2 * ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by ring
  have e2 : (1 - t) * ‖x‖ ^ 2 = ‖x‖ ^ 2 - t * ‖x‖ ^ 2 := by ring
  linarith [sq_nonneg ‖y‖]

/-- the arc mass of a difference is at most the `ℓ²` norm (Parseval, `Δ ≤ 1/2`). -/
theorem arc_le_l2 (N : ℕ) (c : ℕ → ℂ) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 1 / 2) :
    (∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N c β‖ ^ 2) ≤ ZetaQ.l2sq N c := by
  have hg := LemmaK.expSum_normSq_continuous N c
  have hp := LemmaK.expSum_normSq_periodic N c
  have h1 : (∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N c β‖ ^ 2) ≤ ∫ β in (-(1 / 2) : ℝ)..(1 / 2), ‖ZetaQ.expSum N c β‖ ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) hΔ
      (ae_of_all _ fun β => sq_nonneg _) (hg.intervalIntegrable _ _)
  have h2 : (∫ β in (-(1 / 2) : ℝ)..(1 / 2), ‖ZetaQ.expSum N c β‖ ^ 2)
      = ∫ β in (0 : ℝ)..1, ‖ZetaQ.expSum N c β‖ ^ 2 := by
    have := hp.intervalIntegral_add_eq (-(1 / 2)) 0
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at this
    exact this
  rw [h2, ZetaQ.Gallagher.integral_normSq_expSum] at h1
  exact h1

/-- **the hole of `b`, from the arc mass of a comparison vector `a′`.** -/
theorem hole_lower_det (N : ℕ) (b a' : ℕ → ℂ) (R Δ t A₀ E : ℝ) (hΔ : 0 < Δ) (hΔh : Δ ≤ 1 / 2)
    (hsepΔ : ∀ r r' : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → 1 ≤ r' → r' ≤ ⌊R⌋₊ → 2 * Δ ≤ 1 / ((r : ℝ) * r'))
    (hR1 : 1 ≤ R)
    (hcop : ∀ r : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → ∀ n ∈ Finset.Ioc 0 N, b n ≠ 0 → Nat.Coprime n r)
    (ht : 0 < t) (ht1 : t ≤ 1) (hA : A₀ ≤ ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N a' β‖ ^ 2)
    (hE : ZetaQ.l2sq N (fun n => a' n - b n) ≤ E) :
    Real.log R * ((1 - t) * A₀ - E / t) - 2 * Real.sqrt (ZetaQ.l2sq N b) ≤ LemmaK.holeInt N b R Δ := by
  have h0 := LemmaK.hole_lower_generic N b b R Δ hΔ (by linarith) hsepΔ hR1 hcop le_rfl
    (by
      have : ZetaQ.l2sq N (fun n => b n - b n) = 0 := by unfold ZetaQ.l2sq; simp
      rw [this]; norm_num)
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR1
  -- the arc comparison
  have harc : (1 - t) * A₀ - E / t ≤ ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N b β‖ ^ 2 := by
    have hcont : ∀ c : ℕ → ℂ, Continuous (fun β => ‖ZetaQ.expSum N c β‖ ^ 2) :=
      fun c => LemmaK.expSum_normSq_continuous N c
    have hpt : ∀ β, (1 - t) * ‖ZetaQ.expSum N a' β‖ ^ 2 - ‖ZetaQ.expSum N (fun n => a' n - b n) β‖ ^ 2 / t
        ≤ ‖ZetaQ.expSum N b β‖ ^ 2 := by
      intro β
      have e : ZetaQ.expSum N b β = ZetaQ.expSum N a' β - ZetaQ.expSum N (fun n => a' n - b n) β := by
        have := LemmaK.expSum_split N a' b β
        rw [this]; ring
      rw [e]
      exact normSq_sub_ge _ _ t ht
    set f : ℝ → ℝ := fun β => ‖ZetaQ.expSum N a' β‖ ^ 2 with hf
    set g : ℝ → ℝ := fun β => ‖ZetaQ.expSum N (fun n => a' n - b n) β‖ ^ 2 with hg
    have hfi : IntervalIntegrable (fun β => (1 - t) * f β) volume (-Δ) Δ :=
      (continuous_const.mul (hcont a')).intervalIntegrable _ _
    have hgi : IntervalIntegrable (fun β => g β / t) volume (-Δ) Δ :=
      ((hcont _).div_const t).intervalIntegrable _ _
    have hint1 : IntervalIntegrable (fun β => (1 - t) * f β - g β / t) volume (-Δ) Δ := hfi.sub hgi
    have hmono := intervalIntegral.integral_mono_on (by linarith) hint1 ((hcont b).intervalIntegrable _ _)
      (fun β _ => hpt β)
    have hL : (∫ β in (-Δ)..Δ, ((1 - t) * f β - g β / t))
        = (1 - t) * (∫ β in (-Δ)..Δ, f β) - (∫ β in (-Δ)..Δ, g β) / t := by
      rw [intervalIntegral.integral_sub hfi hgi, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_div]
    rw [hL] at hmono
    have hE' := le_trans (arc_le_l2 N (fun n => a' n - b n) Δ hΔ.le hΔh) hE
    have h1 : (1 - t) * A₀ ≤ (1 - t) * ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N a' β‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have h2 : (∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N (fun n => a' n - b n) β‖ ^ 2) / t ≤ E / t :=
      div_le_div_of_nonneg_right hE' ht.le
    linarith
  have := mul_le_mul_of_nonneg_left harc hlog
  linarith

end ASc
end ShellS
end ZetaShell
