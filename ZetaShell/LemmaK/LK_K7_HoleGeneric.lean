/-
lean_work/L7_3/skeleton/LK_K7_HoleGeneric.lean (L7_3, round 3): the hole lower bound eq:K-hole in generic form —
for `a = a′ + a″` with `a′` supported on integers coprime to every `r ≤ R`, `‖a′‖² ≤ ‖a‖²`, `‖a″‖² ≤ 1`, and `Δ`-balls
`2Δ`-separated: `log R · ∫_{−Δ}^{Δ}|S′|² − 2‖a‖ ≤ Hole(S)`.
Proof: K4 (`principal_gauss_hole`) integrated and K4b (`Σμ²/φ ≥ log(⌊R⌋+1)`) give `Hole(S′) ≥ log R·J′`;
`Hole(S′) ≤ ‖a‖²`, `Hole(S″) ≤ 1` (`holeInt_le_l2sq`); pointwise `|S|² ≥ |S′|² − 2|S′||S″|` and
`2|S′||S″| ≤ t|S′|² + |S″|²/t`, optimised at `t = ‖a‖⁻¹`. PROVED (modulo nothing; uses L7_9's K4, K4b).
-/
import ZetaShell.LemmaK.LK_K7_HoleLe
import ZetaShell.LemmaK.LK_K4_PrincipalGaussHole
import ZetaShell.LemmaK.LK_K4b_MuSqTotient

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace LemmaK

/-- the ball functional `Σ_{r ≤ R} Σ*_b ∫_{−Δ}^{Δ} f(b/r + β) dβ`. -/
def ballSum (R Δ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 ⌊R⌋₊, ∑ b ∈ ZetaQ.reducedResidues r, ∫ β in (-Δ)..Δ, f ((b : ℝ) / r + β)

theorem holeInt_eq_ballSum (N : ℕ) (a : ℕ → ℂ) (R Δ : ℝ) :
    holeInt N a R Δ = ballSum R Δ (fun θ => ‖ZetaQ.expSum N a θ‖ ^ 2) := rfl

theorem ballSum_mono {R Δ : ℝ} (hΔ : 0 ≤ Δ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ θ, f θ ≤ g θ) : ballSum R Δ f ≤ ballSum R Δ g := by
  unfold ballSum
  refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun b _ => ?_
  apply intervalIntegral.integral_mono_on (by linarith)
    ((hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
    ((hg.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
  intro β _; exact h _

theorem ballSum_lin {R Δ : ℝ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (c d : ℝ) :
    ballSum R Δ (fun θ => c * f θ + d * g θ) = c * ballSum R Δ f + d * ballSum R Δ g := by
  unfold ballSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hf' : IntervalIntegrable (fun β => f ((b : ℝ) / r + β)) volume (-Δ) Δ :=
    (hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hg' : IntervalIntegrable (fun β => g ((b : ℝ) / r + β)) volume (-Δ) Δ :=
    (hg.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hf'.const_mul c) (hg'.const_mul d),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem expSum_cont (N : ℕ) (a : ℕ → ℂ) : Continuous (ZetaQ.expSum N a) := by
  rw [show ZetaQ.expSum N a = ZetaQ.Gallagher.trig (Finset.Ioc 0 N) a from rfl]
  exact ZetaQ.Gallagher.continuous_trig _ _

theorem expSum_split (N : ℕ) (a a' : ℕ → ℂ) (θ : ℝ) :
    ZetaQ.expSum N a θ = ZetaQ.expSum N a' θ + ZetaQ.expSum N (fun n => a n - a' n) θ := by
  unfold ZetaQ.expSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Generic eq:K-hole.** -/
theorem hole_lower_generic (N : ℕ) (a a' : ℕ → ℂ) (R Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : 2 * Δ ≤ 1)
    (hsepΔ : ∀ r r' : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → 1 ≤ r' → r' ≤ ⌊R⌋₊ → 2 * Δ ≤ 1 / ((r : ℝ) * r'))
    (hR1 : 1 ≤ R)
    (hcop : ∀ r : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → ∀ n ∈ Finset.Ioc 0 N, a' n ≠ 0 → Nat.Coprime n r)
    (hA : ZetaQ.l2sq N a' ≤ ZetaQ.l2sq N a) (hB : ZetaQ.l2sq N (fun n => a n - a' n) ≤ 1) :
    Real.log R * (∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N a' β‖ ^ 2) - 2 * Real.sqrt (ZetaQ.l2sq N a)
      ≤ holeInt N a R Δ := by
  set a'' : ℕ → ℂ := fun n => a n - a' n with ha''
  set u : ℝ → ℝ := fun θ => ‖ZetaQ.expSum N a' θ‖ with hu
  set v : ℝ → ℝ := fun θ => ‖ZetaQ.expSum N a'' θ‖ with hv
  have hu_c : Continuous u := (expSum_cont N a').norm
  have hv_c : Continuous v := (expSum_cont N a'').norm
  set L : ℝ := ZetaQ.l2sq N a with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set H' := holeInt N a' R Δ with hH'
  set H'' := holeInt N a'' R Δ with hH''
  set Y := ballSum R Δ (fun θ => u θ * v θ) with hY
  -- (a) `H′ ≥ (Σμ²/φ)·J′`
  set J : ℝ := ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N a' β‖ ^ 2 with hJ
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg (by linarith) (fun β _ => sq_nonneg _)
  have hcont : ∀ c : ℝ, Continuous (fun β : ℝ => ‖ZetaQ.expSum N a' (c + β)‖ ^ 2) := fun c =>
    ((expSum_cont N a').comp (continuous_const.add continuous_id)).norm.pow 2
  have hHa : (∑ r ∈ Finset.Icc 1 ⌊R⌋₊, ((ArithmeticFunction.moebius r : ℝ)) ^ 2 / (Nat.totient r : ℝ)) * J ≤ H' := by
    rw [hH', holeInt, Finset.sum_mul]
    refine Finset.sum_le_sum fun r hr => ?_
    obtain ⟨hr1, hrR⟩ := Finset.mem_Icc.mp hr
    rw [← intervalIntegral.integral_finset_sum (fun b _ => (hcont _).intervalIntegrable _ _), hJ,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      (((expSum_cont N a').norm.pow 2).const_mul _ |>.intervalIntegrable _ _)
      ((continuous_finset_sum _ fun b _ => hcont _).intervalIntegrable _ _)
    intro β _
    have h4 := principal_gauss_hole r N (by omega) a' (hcop r hr1 hrR) β
    simpa [add_comm] using h4
  have hK4b := log_succ_le_sum_moebius_sq_div_totient ⌊R⌋₊
  have hlogR : Real.log R ≤ Real.log ((⌊R⌋₊ : ℝ) + 1) :=
    Real.log_le_log (by linarith) (Nat.lt_floor_add_one R).le
  have hH'low : Real.log R * J ≤ H' := by
    have := mul_le_mul_of_nonneg_right (hlogR.trans hK4b) hJ0
    linarith
  -- (b) `H′ ≤ L`, `H″ ≤ 1`
  have hH'le : H' ≤ L := (holeInt_le_l2sq N a' R Δ hΔ hΔ1 hsepΔ).trans hA
  have hH''le : H'' ≤ 1 := (holeInt_le_l2sq N a'' R Δ hΔ hΔ1 hsepΔ).trans hB
  -- (c) `Hole(S) ≥ H′ − 2Y`
  have hsplit : H' - 2 * Y ≤ holeInt N a R Δ := by
    have hm := ballSum_mono (R := R) hΔ.le
      (f := fun θ => u θ ^ 2 + -2 * (u θ * v θ)) (g := fun θ => ‖ZetaQ.expSum N a θ‖ ^ 2)
      (by exact (hu_c.pow 2).add ((hu_c.mul hv_c).const_mul (-2)))
      (by exact (expSum_cont N a).norm.pow 2) (fun θ => by
        have hs := expSum_split N a a' θ
        have htri := norm_sub_norm_le (ZetaQ.expSum N a' θ) (-(ZetaQ.expSum N a'' θ))
        rw [norm_neg, sub_neg_eq_add, ← hs] at htri
        have h0 : 0 ≤ ‖ZetaQ.expSum N a θ‖ := norm_nonneg _
        have hu0 : 0 ≤ u θ := norm_nonneg _
        have hv0 : 0 ≤ v θ := norm_nonneg _
        show u θ ^ 2 + -2 * (u θ * v θ) ≤ ‖ZetaQ.expSum N a θ‖ ^ 2
        rcases le_total (v θ) (u θ) with h | h
        · have h1 : 0 ≤ u θ - v θ := by linarith
          have h2 : (u θ - v θ) ^ 2 ≤ ‖ZetaQ.expSum N a θ‖ ^ 2 := pow_le_pow_left₀ h1 htri 2
          nlinarith
        · nlinarith)
    have e := ballSum_lin (R := R) (Δ := Δ) (f := fun θ => u θ ^ 2) (g := fun θ => u θ * v θ)
      (by exact hu_c.pow 2) (by exact hu_c.mul hv_c) 1 (-2)
    simp only [one_mul] at e
    rw [e] at hm
    rw [hH', holeInt_eq_ballSum, holeInt_eq_ballSum]
    have : ballSum R Δ (fun θ => u θ ^ 2) = ballSum R Δ (fun θ => ‖ZetaQ.expSum N a' θ‖ ^ 2) := rfl
    linarith
  -- (d) `2Y ≤ tH′ + H″/t`
  have hY_t : ∀ t : ℝ, 0 < t → 2 * Y ≤ t * H' + H'' / t := by
    intro t ht
    have hm := ballSum_mono (R := R) hΔ.le
      (f := fun θ => 2 * (u θ * v θ) + 0 * (u θ * v θ))
      (g := fun θ => t * u θ ^ 2 + 1 / t * v θ ^ 2)
      (by exact ((hu_c.mul hv_c).const_mul 2).add ((hu_c.mul hv_c).const_mul 0))
      (by exact ((hu_c.pow 2).const_mul t).add ((hv_c.pow 2).const_mul (1 / t))) (fun θ => by
        have h : 0 ≤ (t * u θ - v θ) ^ 2 := sq_nonneg _
        have e : t * u θ ^ 2 + 1 / t * v θ ^ 2 - 2 * (u θ * v θ) = (t * u θ - v θ) ^ 2 / t := by
          field_simp; ring
        have := div_nonneg h ht.le
        show 2 * (u θ * v θ) + 0 * (u θ * v θ) ≤ t * u θ ^ 2 + 1 / t * v θ ^ 2
        linarith)
    have e1 := ballSum_lin (R := R) (Δ := Δ) (f := fun θ => u θ * v θ) (g := fun θ => u θ * v θ)
      (by exact hu_c.mul hv_c) (by exact hu_c.mul hv_c) 2 0
    have e2 := ballSum_lin (R := R) (Δ := Δ) (f := fun θ => u θ ^ 2) (g := fun θ => v θ ^ 2)
      (by exact hu_c.pow 2) (by exact hv_c.pow 2) t (1 / t)
    simp only [zero_mul, add_zero] at e1 e2 hm
    rw [e1, e2] at hm
    have hA' : ballSum R Δ (fun θ => u θ ^ 2) = H' := rfl
    have hB' : ballSum R Δ (fun θ => v θ ^ 2) = H'' := rfl
    rw [hA', hB'] at hm
    have : 1 / t * H'' = H'' / t := by ring
    have hY' : ballSum R Δ (fun θ => u θ * v θ) = Y := rfl
    rw [hY'] at hm
    linarith
  -- (e) `Y ≤ √L`
  have hH''0 : 0 ≤ H'' := by
    rw [hH'', holeInt]
    exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun b _ =>
      intervalIntegral.integral_nonneg (by linarith) (fun β _ => sq_nonneg _)
  have hYle : Y ≤ Real.sqrt L := by
    rcases eq_or_lt_of_le hL0 with hL00 | hLpos
    · -- `L = 0`
      by_contra hcon
      push_neg at hcon
      have hYpos : 0 < Y := lt_of_le_of_lt (Real.sqrt_nonneg _) hcon
      have h := hY_t (1 / Y) (by positivity)
      have hH'0 : H' ≤ 0 := by rw [← hL00] at hH'le; exact hH'le
      have e : H'' / (1 / Y) = H'' * Y := by field_simp
      rw [e] at h
      have : 1 / Y * H' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hH'0
      nlinarith
    · have hs := Real.sqrt_pos.mpr hLpos
      have h := hY_t (1 / Real.sqrt L) (by positivity)
      have h1 : 1 / Real.sqrt L * H' ≤ Real.sqrt L := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs, Real.mul_self_sqrt hL0]; exact hH'le
      have h2 : H'' / (1 / Real.sqrt L) ≤ Real.sqrt L := by
        rw [div_div_eq_mul_div, div_one]
        have := mul_le_mul_of_nonneg_right hH''le hs.le
        linarith
      linarith
  linarith

end LemmaK
end ZetaShell
