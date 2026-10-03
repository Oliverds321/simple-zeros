/-
S1L_Model (L7_5b, 1 Oct 2026): leaf `Mmod_props` of S1 — the model `M_s(β) = −(2π)⁻¹ ∫_0^∞ A_s(y) e(yβ) dy` is
continuous and `∫_{−1/2}^{1/2} |M_s|² ≤ CU·T`.
Route: `M_s(β) = −(2π)⁻¹ 𝓕A_s(−β)` (`A_s = 0` on `y ≤ 0`), Plancherel for `C_c^∞` (`FourierLink.plancherel_cc`), and
`∫ |A_s|² ≤ 36 c₁ T` (`c₁ = ∫ (1+x²)⁻¹`): on the support `y = e^{s+L}`, `|L| < κ ≤ 1`,
`|A_s(y)|² ≤ y⁻¹ |D_T(−L)|² ≤ 3e^{−s} · 2T²/(1 + (TL/2)²)` and `(y − e^s)² ≤ 4e^{2s}L²` give the Lorentzian majorant
`6T²e^{−s} (1 + ((y − e^s)/(b e^s))²)⁻¹`, `b = 6/T`, whose integral is `36 c₁ T`.
-/
import ZetaShell.ShellS.S1_Defs
import ZetaShell.PropZ.FourierLink
import ZetaShell.PropZ.ZZ2c_HL2

noncomputable section
open MeasureTheory FourierTransform

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem As_L2 (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → ∀ s : ℝ, (∫ y, ‖As T κ Ξ s y‖ ^ 2) ≤ C * T := by
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = ∫ x : ℝ, (1 + x ^ 2)⁻¹ := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; exact integral_nonneg fun x => by positivity
  refine ⟨36 * c₁, by positivity, fun T hT s => ?_⟩
  have hTp : 0 < T := by linarith
  set N := Real.exp s with hNdef
  have hN : 0 < N := Real.exp_pos s
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 6 / T := ⟨_, rfl⟩
  have hbp : 0 < b := by rw [hb]; positivity
  have hbN : 0 < b * N := mul_pos hbp hN
  have hGi : Integrable (fun y : ℝ => 6 * T ^ 2 * N⁻¹ * (1 + ((y - N) / (b * N)) ^ 2)⁻¹) :=
    ((integrable_inv_one_add_sq.comp_div hbN.ne').comp_sub_right N).const_mul _
  have hGint : (∫ y : ℝ, 6 * T ^ 2 * N⁻¹ * (1 + ((y - N) / (b * N)) ^ 2)⁻¹) = 36 * c₁ * T := by
    rw [integral_const_mul]
    have h1 := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => (1 + (y / (b * N)) ^ 2)⁻¹) N
    have h2 := MeasureTheory.Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) (b * N)
    beta_reduce at h1 h2
    rw [h1, h2, abs_of_pos hbN, smul_eq_mul, ← hc₁, hb]
    field_simp
    ring
  have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hpw : ∀ y : ℝ, ‖As T κ Ξ s y‖ ^ 2 ≤ 6 * T ^ 2 * N⁻¹ * (1 + ((y - N) / (b * N)) ^ 2)⁻¹ := by
    intro y
    have hG0 : 0 ≤ 6 * T ^ 2 * N⁻¹ * (1 + ((y - N) / (b * N)) ^ 2)⁻¹ := by positivity
    by_cases hy : y ≤ 0
    · rw [As_eq_zero_of_nonpos T κ Ξ s hy, norm_zero]
      simpa using hG0
    rw [not_le] at hy
    by_cases hz : Ξ ((Real.log y - s) / κ) = 0
    · have h0 : As T κ Ξ s y = 0 := by unfold As; rw [hz]; simp
      rw [h0, norm_zero]
      simpa using hG0
    have hmem : (Real.log y - s) / κ ∈ Set.Ioo (-1 : ℝ) 1 := hΞ.supp (subset_tsupport _ hz)
    set L := Real.log y - s with hL
    have hLk : |L| < κ := by
      have h := abs_lt.mpr ⟨hmem.1, hmem.2⟩
      rw [abs_div, abs_of_pos hκ, div_lt_one hκ] at h; exact h
    have hL1 : |L| ≤ 1 := by linarith
    have hyN : y = N * Real.exp L := by
      rw [hNdef, ← Real.exp_add, hL, show s + (Real.log y - s) = Real.log y by ring, Real.exp_log hy]
    have hyinv : y⁻¹ ≤ 3 * N⁻¹ := by
      rw [hyN, mul_inv, mul_comm]
      have h3 : (Real.exp L)⁻¹ ≤ 3 := by
        rw [← Real.exp_neg]
        refine (Real.exp_le_exp.mpr ?_).trans he1
        have := neg_abs_le L
        linarith
      exact mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hN.le)
    have hAs : ‖As T κ Ξ s y‖ ^ 2 ≤ y⁻¹ * ‖ZetaShell.DTFacts.DTf T (-L)‖ ^ 2 := by
      unfold As
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, DT_eq_DTf]
      have hsl : s - Real.log y = -L := by rw [hL]; ring
      rw [hsl, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _), Real.norm_of_nonneg (hΞ.nonneg _)]
      have hrp : (y ^ (-(1 / 2 : ℝ))) ^ 2 = y⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
        norm_num
        exact Real.rpow_neg_one y
      have hΞ1 := hΞ.le_one ((Real.log y - s) / κ)
      have hΞ0 := hΞ.nonneg ((Real.log y - s) / κ)
      have hΞsq : (Ξ ((Real.log y - s) / κ)) ^ 2 ≤ 1 := by nlinarith
      calc (y ^ (-(1 / 2 : ℝ)) * ‖ZetaShell.DTFacts.DTf T (-L)‖ * Ξ ((Real.log y - s) / κ)) ^ 2
          = (y ^ (-(1 / 2 : ℝ))) ^ 2 * ‖ZetaShell.DTFacts.DTf T (-L)‖ ^ 2
              * (Ξ ((Real.log y - s) / κ)) ^ 2 := by ring
        _ ≤ (y ^ (-(1 / 2 : ℝ))) ^ 2 * ‖ZetaShell.DTFacts.DTf T (-L)‖ ^ 2 * 1 := by gcongr
        _ = y⁻¹ * ‖ZetaShell.DTFacts.DTf T (-L)‖ ^ 2 := by rw [hrp, mul_one]
    have hyL : (y - N) ^ 2 ≤ 4 * N ^ 2 * L ^ 2 := by
      have hexp := Real.abs_exp_sub_one_le hL1
      have h1 : y - N = N * (Real.exp L - 1) := by rw [hyN]; ring
      rw [h1, mul_pow]
      have h2 : (Real.exp L - 1) ^ 2 ≤ 4 * L ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hexp 2
        rw [sq_abs, mul_pow, sq_abs] at this
        linarith
      nlinarith [sq_nonneg N]
    have hsq := DTf_sq_le T (-L) hTp.le
    have hden : ((y - N) / (b * N)) ^ 2 ≤ (T * -L / 2) ^ 2 := by
      rw [div_pow, div_le_iff₀ (by positivity), hb]
      have e2 : (T * -L / 2) ^ 2 * ((6 / T) * N) ^ 2 = 9 * N ^ 2 * L ^ 2 := by
        field_simp; ring
      rw [e2]
      nlinarith [sq_nonneg N, sq_nonneg L]
    have hq : 0 < 1 + ((y - N) / (b * N)) ^ 2 := by positivity
    have hD : ‖ZetaShell.DTFacts.DTf T (-L)‖ ^ 2 ≤ 2 * T ^ 2 * (1 + ((y - N) / (b * N)) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hq]
      have := mul_le_mul_of_nonneg_left (show 1 + ((y - N) / (b * N)) ^ 2 ≤ 1 + (T * -L / 2) ^ 2 by linarith)
        (sq_nonneg ‖ZetaShell.DTFacts.DTf T (-L)‖)
      linarith
    calc ‖As T κ Ξ s y‖ ^ 2 ≤ y⁻¹ * ‖ZetaShell.DTFacts.DTf T (-L)‖ ^ 2 := hAs
      _ ≤ (3 * N⁻¹) * (2 * T ^ 2 * (1 + ((y - N) / (b * N)) ^ 2)⁻¹) :=
          mul_le_mul hyinv hD (sq_nonneg _) (by positivity)
      _ = 6 * T ^ 2 * N⁻¹ * (1 + ((y - N) / (b * N)) ^ 2)⁻¹ := by ring
  calc (∫ y, ‖As T κ Ξ s y‖ ^ 2) ≤ ∫ y : ℝ, 6 * T ^ 2 * N⁻¹ * (1 + ((y - N) / (b * N)) ^ 2)⁻¹ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _) hGi
          (Filter.Eventually.of_forall hpw)
    _ = 36 * c₁ * T := hGint

theorem Mmod_props' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) :
    ∃ CU : ℝ, 0 ≤ CU ∧ ∀ T : ℝ, 2 ≤ T → ∀ s : ℝ,
      Continuous (Mmod T κ Ξ s) ∧ (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖Mmod T κ Ξ s β‖ ^ 2) ≤ CU * T := by
  obtain ⟨C, hC0, hC⟩ := As_L2 κ hκ hκ1 Ξ hΞ
  refine ⟨((2 * Real.pi)⁻¹) ^ 2 * C, by positivity, fun T hT s => ?_⟩
  have hAc : ContDiff ℝ (⊤ : ℕ∞) (As T κ Ξ s) := As_contDiff T κ hκ Ξ hΞ s
  have hAcs : HasCompactSupport (As T κ Ξ s) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (As_tsupport T κ hκ Ξ hΞ s)
  have hIoi : ∀ β, (∫ y in Set.Ioi (0 : ℝ), As T κ Ξ s y * eA (y * β)) = ∫ y, As T κ Ξ s y * eA (y * β) := by
    intro β
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [As_eq_zero_of_nonpos T κ Ξ s (not_lt.mp hy), zero_mul]
  have hM : ∀ β, Mmod T κ Ξ s β = -(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * 𝓕 (As T κ Ξ s) (-β) := by
    intro β
    unfold Mmod
    rw [hIoi, Real.fourier_real_eq]
    congr 1
    congr 1; funext y
    rw [Circle.smul_def, smul_eq_mul, ← eA_eq_fourierChar, mul_comm]
    congr 2; ring
  constructor
  · have h := continuous_S ∅ (fun _ => 0) (As T κ Ξ s) hAc.continuous hAcs
    simp only [Finset.sum_empty, zero_add] at h
    have hfun : Mmod T κ Ξ s = fun β => -(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ y, As T κ Ξ s y * eA (y * β) := by
      funext β; unfold Mmod; rw [hIoi]
    rw [hfun]
    exact continuous_const.mul h
  · set h := 𝓕 (hAcs.toSchwartzMap hAc) with hh
    have hhG : ∀ β, h β = 𝓕 (As T κ Ξ s) β := fun β => rfl
    have hint : Integrable (fun β => ‖h β‖ ^ 2) := by
      refine (h.integrable.norm.const_mul ‖h.toBoundedContinuousFunction‖).mono'
        (h.continuous.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      have hb : ‖h x‖ ≤ ‖h.toBoundedContinuousFunction‖ := h.toBoundedContinuousFunction.norm_coe_le_norm x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    have hint' : Integrable (fun β => ‖𝓕 (As T κ Ξ s) (-β)‖ ^ 2) := by
      simp_rw [← hhG]; exact hint.comp_neg
    have hPl := ZetaShell.FourierLink.plancherel_cc (As T κ Ξ s) hAc hAcs
    have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
    have hMsq : ∀ β, ‖Mmod T κ Ξ s β‖ ^ 2 = ((2 * Real.pi)⁻¹) ^ 2 * ‖𝓕 (As T κ Ξ s) (-β)‖ ^ 2 := by
      intro β
      rw [hM, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hpi, mul_pow]
    have hMint : Integrable (fun β => ‖Mmod T κ Ξ s β‖ ^ 2) := by
      simp_rw [hMsq]; exact hint'.const_mul _
    rw [intervalIntegral.integral_of_le (by norm_num)]
    calc (∫ β in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), ‖Mmod T κ Ξ s β‖ ^ 2) ≤ ∫ β, ‖Mmod T κ Ξ s β‖ ^ 2 :=
          setIntegral_le_integral hMint (Filter.Eventually.of_forall fun β => sq_nonneg _)
      _ = ((2 * Real.pi)⁻¹) ^ 2 * ∫ y, ‖As T κ Ξ s y‖ ^ 2 := by
          simp_rw [hMsq]
          rw [integral_const_mul, integral_neg_eq_self (fun β => ‖𝓕 (As T κ Ξ s) β‖ ^ 2) volume, hPl]
      _ ≤ ((2 * Real.pi)⁻¹) ^ 2 * (C * T) := by gcongr; exact hC T hT s
      _ = ((2 * Real.pi)⁻¹) ^ 2 * C * T := by ring

end ShellS
end ZetaShell
