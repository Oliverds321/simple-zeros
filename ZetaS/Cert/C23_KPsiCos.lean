/-
lean_work/L6_1/C23_KPsiCos.lean — track C node C23 (agent L6_1, 28 Sep 2026; statement from
lean_work/L1_1/nodes/C23_KPsiCos.lean, unchanged).
k_ψ for ψ = cos(1.6 s) (ChallengeZetaS `kPsi`, sec_zeta.tex l.107: k_ψ(x) = ∫ψ(s)cos(2πxs)ds/∫ψ) equals the closed
form `kCos x = (sinc(πx − 4/5) + sinc(πx + 4/5))/(2 sinc(4/5))`.
Proof: ∫_{−1/2}^{1/2} cos(a s) ds = sinc(a/2) for every a (Mathlib `integral_cos`; as L0_2's `CosWindow.integral_cosW`), and
cos(8s/5)cos(2πxs) = (cos((2πx − 8/5)s) + cos((2πx + 8/5)s))/2.
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

/-- ∫_{−1/2}^{1/2} cos(a s) ds = sinc(a/2), for every real a. -/
theorem integral_cos_mul_half (a : ℝ) :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (a * s) = Real.sinc (a / 2) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one, zero_div,
      Real.sinc_zero]
    norm_num
  · rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) ha, integral_cos, smul_eq_mul,
      show a * -(1 / 2) = -(a / 2) by ring, show a * (1 / 2) = a / 2 by ring, Real.sin_neg,
      Real.sinc_of_ne_zero (div_ne_zero ha two_ne_zero), div_div_eq_mul_div]
    ring

/-- = `kPsi_psiCos16_eq` of CertSpecAM5. -/
theorem kPsi_psiCos16_eq' (x : ℝ) : kPsi psiCos16 x = kCos x := by
  unfold kPsi psiCos16 kCos
  have hpt : ∀ s, Real.cos (8 / 5 * s) * Real.cos (2 * Real.pi * x * s)
      = (Real.cos ((2 * Real.pi * x - 8 / 5) * s) + Real.cos ((2 * Real.pi * x + 8 / 5) * s)) / 2 := by
    intro s
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  have hc1 : Continuous fun s : ℝ => Real.cos ((2 * Real.pi * x - 8 / 5) * s) := by fun_prop
  have hc2 : Continuous fun s : ℝ => Real.cos ((2 * Real.pi * x + 8 / 5) * s) := by fun_prop
  have hnum : ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (8 / 5 * s) * Real.cos (2 * Real.pi * x * s)
      = (Real.sinc (Real.pi * x - 4 / 5) + Real.sinc (Real.pi * x + 4 / 5)) / 2 := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _), integral_cos_mul_half, integral_cos_mul_half,
      show (2 * Real.pi * x - 8 / 5) / 2 = Real.pi * x - 4 / 5 by ring,
      show (2 * Real.pi * x + 8 / 5) / 2 = Real.pi * x + 4 / 5 by ring]
  have hden : ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (8 / 5 * s) = Real.sinc (4 / 5) := by
    rw [integral_cos_mul_half]
    norm_num
  rw [hnum, hden]
  ring

end ZetaS.CertV2
