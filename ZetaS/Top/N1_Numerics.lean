/-
Node N1 (track T, numerics) — the four closing numerical inequalities (values [C] by L0_4 in mpmath, 30 digits:
S = 0.673373689541190838…, SC = 0.887919569562077…, Σ = 0.676102666964137…, D = 0.838051333482068…).
Needs exact/interval evaluation of H(ψ̃) = 26957030199857/40103091391077 (rem:zeta-P8; polynomial autocorrelation,
upstream pattern `Zeta23/XiPrime/Certificate/Poly.lean`) and of H(cos 1.6s) = 0.6719815510003707… (closed form in
sin 0.8, cos 0.8; Taylor bounds as upstream `D1.lean`). Four declarations, one per headline.

L3_2 (28 Sep 2026): all four proved. `num_stab`, `num_sc`: H(ψ̃) = 26957030199857/40103091391077 exactly
(`PolyMoments.Hpsi_poly8A`: ∫ψ̃, ∫ψ̃², ∬|u − v|ψ̃ψ̃ by the tree's polynomial-list device), Φ_147 with
√(14527/13125) enclosed to 10⁻¹⁸ (S margin 4.1·10⁻¹¹), √2 ≥ 1.41421356. `num_sigma`, `num_dist` proved from L0_2's `CosWindow` (`Rquot_cosW`: R(cos α·) = (b + J)/a² in
closed form; `HC_eight_fifths`: H(8/5) ∈ [0.6719815510003707, 0.6719815510003708], alternating Taylor series; the
final arithmetic `sigma_K7`, `dist_K7`). The bridge is `Hpsi_cos16 : Hpsi psiCos16 = CosWindow.HC (8/5)`.
Statements unchanged; the import of `CosWindow` is added.
-/
import ZetaS.Interfaces
import ZetaS.Window.CosWindow
import ZetaS.Top.PolyMoments

namespace ZetaS

/-- `H(cos 1.6s)` of the interface is L0_2's closed form `HC (8/5)`. -/
theorem Hpsi_cos16 : Hpsi psiCos16 = CosWindow.HC (8 / 5) := by
  have h := CosWindow.Rquot_cosW (α := 8 / 5) (by norm_num)
  unfold Hpsi Rpsi CosWindow.HC
  congr 1

theorem sigmaConst_eq_cos : sigmaConst = CosWindow.sigmaConst := rfl
theorem distConst_eq_cos : distConst = CosWindow.distConst := rfl

theorem num_sigma :
    (676102666 : ℝ) / 10 ^ 9 < sigmaConst (Hpsi psiCos16) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) := by
  rw [Hpsi_cos16, sigmaConst_eq_cos]
  convert CosWindow.sigma_K7 using 1
  norm_num

theorem num_dist :
    (838051333 : ℝ) / 10 ^ 9 < distConst (Hpsi psiCos16) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) := by
  rw [Hpsi_cos16, distConst_eq_cos]
  convert CosWindow.dist_K7 using 1
  norm_num

theorem num_stab :
    (6733736895 : ℝ) / 10 ^ 10 < stabConst (Hpsi psiPoly8A) 8 (7 / 1700) (199 / 25000) 147 := by
  rw [Hpsi_poly8A]
  norm_num [stabConst, PhiM]
  rw [← Real.sqrt_div' 14527 (by norm_num : (0:ℝ) ≤ 13125)]
  have hy1 : (65753417437893711 / 62500000000000000 : ℝ) ≤ Real.sqrt (14527 / 13125) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hy2 : Real.sqrt (14527 / 13125) ≤ 1052054679006299377 / 1000000000000000000 := by
    rw [show (1052054679006299377 / 1000000000000000000 : ℝ)
        = Real.sqrt ((1052054679006299377 / 1000000000000000000) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  generalize Real.sqrt (14527 / 13125) = y at hy1 hy2 ⊢
  have hq : (y - 1) ^ 2 ≤ (1052054679006299377 / 1000000000000000000 - 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hq0 : 0 ≤ (y - 1) ^ 2 := sq_nonneg _
  rw [lt_div_iff₀ (by nlinarith)]
  nlinarith

theorem num_sc :
    (8879195 : ℝ) / 10 ^ 7 < scConst (stabConst (Hpsi psiPoly8A) 8 (7 / 1700) (199 / 25000) 147) := by
  have hS := num_stab
  generalize stabConst (Hpsi psiPoly8A) 8 (7 / 1700) (199 / 25000) 147 = S at hS ⊢
  have hr : (141421356 / 100000000 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  unfold scConst
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-! ### The K = 5 row (thm:zeta-allmarks, rem:sigd-cert; new declarations, same pattern) -/

theorem num_sigma_K5 :
    (675158622 : ℝ) / 10 ^ 9 < sigmaConst (Hpsi psiCos16) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) := by
  rw [Hpsi_cos16, sigmaConst_eq_cos]
  convert CosWindow.sigma_K5 using 1
  norm_num

theorem num_dist_K5 :
    (837579311 : ℝ) / 10 ^ 9 < distConst (Hpsi psiCos16) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) := by
  rw [Hpsi_cos16, distConst_eq_cos]
  convert CosWindow.dist_K5 using 1
  norm_num

end ZetaS
