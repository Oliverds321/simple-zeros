/-
Node Hom (track W/T) — degree-0 homogeneity of k_ψ and R_λ in ψ (rem:zeta-P8: "every quantity … is homogeneous of degree
0 in ψ"): for κ > 0, k_{κψ} = k_ψ and R_λ(κψ) = R_λ(ψ). Used to pass from the tree's ψ♮ = (4/5)v to the draft's ψ̃.
-/
import ZetaS.InterfacesV2

namespace ZetaS

theorem kPsi_Rlam_smul (ψ : ℝ → ℝ) {κ : ℝ} (hκ : 0 < κ) (lam : ℝ) :
    kPsi (fun s => κ * ψ s) = kPsi ψ ∧ Rlam lam (fun s => κ * ψ s) = Rlam lam ψ := by
  have hκ0 : κ ≠ 0 := hκ.ne'
  constructor
  · funext x
    unfold kPsi
    have e1 : (∫ s in (-(1 / 2 : ℝ))..(1 / 2), κ * ψ s * Real.cos (2 * Real.pi * x * s))
        = κ * ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s * Real.cos (2 * Real.pi * x * s) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun s _ => by ring
    rw [e1, intervalIntegral.integral_const_mul, mul_div_mul_left _ _ hκ0]
  · unfold Rlam Jpsi
    have e2 : (∫ u in (-(1 / 2 : ℝ))..(1 / 2), (κ * ψ u) ^ 2) = κ ^ 2 * ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun s _ => by ring
    have e3 : (∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * (κ * ψ u) * (κ * ψ v))
        = κ ^ 2 * ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * ψ u * ψ v := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun v _ => by ring
    rw [e2, e3, intervalIntegral.integral_const_mul]
    have hk2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ0
    rw [show κ ^ 2 * (∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u ^ 2)
          + lam ^ 2 * (κ ^ 2 * ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * ψ u * ψ v)
        = κ ^ 2 * ((∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u ^ 2)
          + lam ^ 2 * ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * ψ u * ψ v) by ring,
      show lam * (κ * ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u) ^ 2
        = κ ^ 2 * (lam * (∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u) ^ 2) by ring,
      mul_div_mul_left _ _ hk2]

end ZetaS
