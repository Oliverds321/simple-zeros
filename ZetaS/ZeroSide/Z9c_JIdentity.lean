/-
Sub-node Z9c (agent L3_1; the Fubini identity proved by L6_1, see lean_work/L6_1/Z9c_Fubini.lean) — the Frobenius constant: the tree's W9.8 constant (c_λ(ψ))⁻¹ = `(XiPrime.cWin id λ ψ)⁻¹`
(𝒥 in the one-integral form 2∫₀¹ λr (ψ⋆ψ)(r) dr) equals the interface's `Rlam λ ψ` (J in the double-integral form
∬|u − v|ψ(u)ψ(v), eq:zeta-R). Needs the Fubini identity 2∫₀¹ r (ψ⋆ψ)(r) dr = ∬_{[−½,½]²} |u − v| ψ(u)ψ(v) du dv.
-/
import ZetaS.ZeroSide.Z9s_Spec

noncomputable section

namespace ZetaS
namespace Z9

open Zeta23

section Fubini
open MeasureTheory Set

/-- Step (1): Fubini on the triangle. -/
theorem int_r_vConv_eq_iter {ψ : ℝ → ℝ} (hcont : Continuous ψ) :
    ∫ r in (0 : ℝ)..1, r * XiPrime.vConv ψ r
      = ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ∫ r in (0 : ℝ)..(1 / 2 - s), r * (ψ s * ψ (s + r)) := by
  let f : ℝ → ℝ → ℝ := fun r s => if s + r ≤ 1 / 2 then r * (ψ s * ψ (s + r)) else 0
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 + p.1 ≤ 1 / 2} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hg : Continuous fun p : ℝ × ℝ => p.1 * (ψ p.2 * ψ (p.2 + p.1)) := by fun_prop
  have hfu : Function.uncurry f
      = {p : ℝ × ℝ | p.2 + p.1 ≤ 1 / 2}.indicator (fun p : ℝ × ℝ => p.1 * (ψ p.2 * ψ (p.2 + p.1))) := by
    funext p
    obtain ⟨r, s⟩ := p
    simp only [Function.uncurry_apply_pair, f, Set.indicator_apply, mem_ofPred_eq]
  have hf_int : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2)))) := by
    rw [Measure.prod_restrict, hfu]
    have h1 : IntegrableOn (fun p : ℝ × ℝ => p.1 * (ψ p.2 * ψ (p.2 + p.1)))
        (Icc (0 : ℝ) 1 ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) (volume.prod volume) :=
      hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have h2 := h1.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    exact h2.indicator hS
  have hswap := integral_integral_swap hf_int
  -- the r-slices
  have hL : EqOn (fun r => r * XiPrime.vConv ψ r)
      (fun r => ∫ s in Ioc (-(1 / 2 : ℝ)) (1 / 2), f r s) (Ioc (0 : ℝ) 1) := by
    intro r hr
    simp only
    unfold XiPrime.vConv
    rw [← intervalIntegral.integral_const_mul]
    have hm : (-(1 : ℝ) / 2) = -(1 / 2) := by norm_num
    have hle : -(1 / 2 : ℝ) ≤ 1 / 2 - r := by linarith [hr.2]
    rw [hm, intervalIntegral.integral_of_le hle]
    have hfi : ∀ s, f r s = (Iic (1 / 2 - r)).indicator (fun s => r * (ψ s * ψ (s + r))) s := by
      intro s
      simp only [f, Set.indicator_apply, mem_Iic]
      split_ifs <;> first | rfl | (exfalso; linarith)
    simp_rw [hfi]
    rw [setIntegral_indicator measurableSet_Iic]
    have hset : Ioc (-(1 / 2 : ℝ)) (1 / 2) ∩ Iic (1 / 2 - r) = Ioc (-(1 / 2 : ℝ)) (1 / 2 - r) := by
      ext s
      simp only [mem_Ioc, mem_inter_iff, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by linarith [hr.1]⟩, h2⟩
    rw [hset]
  -- the s-slices
  have hR : EqOn (fun s => ∫ r in Ioc (0 : ℝ) 1, f r s)
      (fun s => ∫ r in (0 : ℝ)..(1 / 2 - s), r * (ψ s * ψ (s + r))) (Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro s hs
    simp only
    have hle : (0 : ℝ) ≤ 1 / 2 - s := by linarith [hs.2]
    rw [intervalIntegral.integral_of_le hle]
    have hfi : ∀ r, f r s = (Iic (1 / 2 - s)).indicator (fun r => r * (ψ s * ψ (s + r))) r := by
      intro r
      simp only [f, Set.indicator_apply, mem_Iic]
      split_ifs <;> first | rfl | (exfalso; linarith)
    simp_rw [hfi]
    rw [setIntegral_indicator measurableSet_Iic]
    have hset : Ioc (0 : ℝ) 1 ∩ Iic (1 / 2 - s) = Ioc (0 : ℝ) (1 / 2 - s) := by
      ext r
      simp only [mem_Ioc, mem_inter_iff, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by linarith [hs.1]⟩, h2⟩
    rw [hset]
  calc ∫ r in (0 : ℝ)..1, r * XiPrime.vConv ψ r
      = ∫ r in Ioc (0 : ℝ) 1, r * XiPrime.vConv ψ r := intervalIntegral.integral_of_le zero_le_one
    _ = ∫ r in Ioc (0 : ℝ) 1, ∫ s in Ioc (-(1 / 2 : ℝ)) (1 / 2), f r s :=
        setIntegral_congr_fun measurableSet_Ioc hL
    _ = ∫ s in Ioc (-(1 / 2 : ℝ)) (1 / 2), ∫ r in Ioc (0 : ℝ) 1, f r s := hswap
    _ = ∫ s in Ioc (-(1 / 2 : ℝ)) (1 / 2), ∫ r in (0 : ℝ)..(1 / 2 - s), r * (ψ s * ψ (s + r)) :=
        setIntegral_congr_fun measurableSet_Ioc hR
    _ = ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ∫ r in (0 : ℝ)..(1 / 2 - s), r * (ψ s * ψ (s + r)) :=
        (intervalIntegral.integral_of_le (by norm_num)).symm

/-- Step (2): the substitution v = u + r. -/
theorem int_r_slice_eq_max {ψ : ℝ → ℝ} (hcont : Continuous ψ) {u : ℝ}
    (hu1 : -(1 / 2 : ℝ) ≤ u) (hu2 : u ≤ 1 / 2) :
    ∫ r in (0 : ℝ)..(1 / 2 - u), r * (ψ u * ψ (u + r))
      = ∫ v in (-(1 / 2 : ℝ))..(1 / 2), max (v - u) 0 * ψ u * ψ v := by
  have hc : Continuous fun v => max (v - u) 0 * ψ u * ψ v := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h0 : ∫ v in (-(1 / 2 : ℝ))..u, max (v - u) 0 * ψ u * ψ v = 0 := by
    have hz : EqOn (fun v => max (v - u) 0 * ψ u * ψ v) (fun _ => (0 : ℝ)) (uIcc (-(1 / 2 : ℝ)) u) := by
      intro v hv
      rw [uIcc_of_le hu1] at hv
      show max (v - u) 0 * ψ u * ψ v = 0
      rw [max_eq_right (by linarith [hv.2])]
      ring
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
  have h1 : ∫ v in u..(1 / 2), max (v - u) 0 * ψ u * ψ v = ∫ v in u..(1 / 2), (v - u) * ψ u * ψ v := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hu2] at hv
    rw [max_eq_left (by linarith [hv.1])]
  rw [h0, zero_add, h1]
  have hsub := intervalIntegral.integral_comp_add_right (fun v => (v - u) * ψ u * ψ v) u
    (a := 0) (b := 1 / 2 - u)
  rw [zero_add, sub_add_cancel] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [add_sub_cancel_right, add_comm r u]
  ring

/-- Step (3a): the antisymmetric part vanishes. -/
theorem int_int_sub_eq_zero {ψ : ℝ → ℝ} (hcont : Continuous ψ) :
    ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), (u - v) * ψ u * ψ v = 0 := by
  have hin : ∀ u, ∫ v in (-(1 / 2 : ℝ))..(1 / 2), (u - v) * ψ u * ψ v
      = (u * ψ u) * (∫ v in (-(1 / 2 : ℝ))..(1 / 2), ψ v)
        - ψ u * (∫ v in (-(1 / 2 : ℝ))..(1 / 2), v * ψ v) := by
    intro u
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun v _ => ?_
      ring
    · exact (by fun_prop : Continuous fun v => u * ψ u * ψ v).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun v => ψ u * (v * ψ v)).intervalIntegrable _ _
  simp_rw [hin]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const]
  · ring
  · exact (by fun_prop : Continuous fun u => u * ψ u * ∫ v in (-(1 / 2 : ℝ))..(1 / 2), ψ v).intervalIntegrable _ _
  · exact (by fun_prop :
      Continuous fun u => ψ u * ∫ v in (-(1 / 2 : ℝ))..(1 / 2), v * ψ v).intervalIntegrable _ _

/-- The Fubini identity (J in both forms), for continuous ψ. -/
theorem two_int_r_vConv_eq_Jpsi {ψ : ℝ → ℝ} (hcont : Continuous ψ) :
    2 * ∫ r in (0 : ℝ)..1, r * XiPrime.vConv ψ r = Jpsi ψ := by
  have habs : ∀ u v : ℝ, |u - v| = (u - v) + 2 * max (v - u) 0 := by
    intro u v
    rcases le_total u v with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      ring
  have hin : ∀ u, ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * ψ u * ψ v
      = (∫ v in (-(1 / 2 : ℝ))..(1 / 2), (u - v) * ψ u * ψ v)
        + 2 * ∫ v in (-(1 / 2 : ℝ))..(1 / 2), max (v - u) 0 * ψ u * ψ v := by
    intro u
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun v _ => ?_
      rw [habs]
      ring
    · exact (by fun_prop : Continuous fun v => (u - v) * ψ u * ψ v).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun v => 2 * (max (v - u) 0 * ψ u * ψ v)).intervalIntegrable _ _
  have hA : Continuous fun u => ∫ v in (-(1 / 2 : ℝ))..(1 / 2), (u - v) * ψ u * ψ v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 - p.2) * ψ p.1 * ψ p.2) _ _
  have hB : Continuous fun u => ∫ v in (-(1 / 2 : ℝ))..(1 / 2), max (v - u) 0 * ψ u * ψ v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop : Continuous fun p : ℝ × ℝ => max (p.2 - p.1) 0 * ψ p.1 * ψ p.2) _ _
  unfold Jpsi
  simp_rw [hin]
  rw [intervalIntegral.integral_add (hA.intervalIntegrable _ _)
      ((show Continuous fun u => 2 * ∫ v in (-(1 / 2 : ℝ))..(1 / 2), max (v - u) 0 * ψ u * ψ v from
        continuous_const.mul hB).intervalIntegrable _ _),
    int_int_sub_eq_zero hcont, zero_add, intervalIntegral.integral_const_mul,
    int_r_vConv_eq_iter hcont]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (by norm_num)] at hu
  exact int_r_slice_eq_max hcont hu.1 hu.2

end Fubini

theorem jWin_id_eq (ψ : ℝ → ℝ) (lam : ℝ) :
    XiPrime.jWin id lam ψ = lam * (2 * ∫ r in (0 : ℝ)..1, r * XiPrime.vConv ψ r) := by
  unfold XiPrime.jWin
  simp only [id, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem jWin_nonneg {ψ : ℝ → ℝ} (hcore : ∀ s, |s| ≤ 1 / 2 → 0 ≤ ψ s ∧ ψ s ≤ 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ XiPrime.jWin id lam ψ := by
  rw [jWin_id_eq]
  refine mul_nonneg hlam (mul_nonneg zero_le_two (intervalIntegral.integral_nonneg zero_le_one fun r hr => ?_))
  refine mul_nonneg hr.1 (intervalIntegral.integral_nonneg (by linarith [hr.2]) fun s hs => ?_)
  have h1 : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2, hr.1]⟩
  have h2 : |s + r| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1, hr.1], by linarith [hs.2]⟩
  exact mul_nonneg (hcore s h1).1 (hcore (s + r) h2).1

theorem cWin_inv_eq_Rlam {ψ : ℝ → ℝ} (hcont : Continuous ψ) (lam : ℝ) :
    (XiPrime.cWin id lam ψ)⁻¹ = Rlam lam ψ := by
  unfold XiPrime.cWin Rlam
  rw [inv_div, jWin_id_eq, two_int_r_vConv_eq_Jpsi hcont, show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by norm_num]
  ring

end Z9
end ZetaS
