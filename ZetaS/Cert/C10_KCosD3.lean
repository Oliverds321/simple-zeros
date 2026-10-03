/-
lean_work/L6_1/C10_KCosD3.lean — track C node C10 (agent L6_1, 28 Sep 2026; statements from
lean_work/L1_1/nodes/C10_KCosD3.lean, unchanged): |k‴| ≤ π³/4 for the cosine-window kernel, via the integral
representation k(x) = ∫_{−1/2}^{1/2} v(s) cos(2πxs) ds, v = cos(8s/5)/sinc(4/5).

Proof.
  * `IK n x = ∫ v(s)(2πs)ⁿ cos(2πxs + nπ/2) ds`; differentiation under the integral sign (compact interval,
    continuous integrand) gives `HasDerivAt (IK n) (IK (n+1) x) x`.
  * `kCos = IK 0` (node C23); uniqueness of derivatives with node C08 (`hasDerivAt_kCos`, `hasDerivAt_kCos1`, L5_1)
    gives `kCos1 = IK 1`, `kCos2 = IK 2`; hence `HasDerivAt kCos2 (IK 3 x) x`.
  * |IK 3 x| ≤ 8π³/sinc(4/5) · ∫cos(8s/5)|s|³ ≤ π³/4 by the Chebyshev-type bound
    ∫cos(8s/5)|s|³ ≤ (1/32)∫cos(8s/5): with s₀³ = 1/32, (cos(8s/5) − cos(8s₀/5))(1/32 − |s|³) ≥ 0 pointwise and
    ∫(1/32 − |s|³) = 0.
Imports C08 (L5_1, `lean_work/L5_1/C08_KCosDerivs.lean`) and C23 (L6_1).
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C08_KCosDerivs
import ZetaS.Cert.C23_KPsiCos

noncomputable section

open Set MeasureTheory

namespace ZetaS.CertV2

/-- the weights of the integral representation: v(s)(2πs)ⁿ. -/
def gK (n : ℕ) (s : ℝ) : ℝ := Real.cos (8 / 5 * s) / Real.sinc (4 / 5) * (2 * Real.pi * s) ^ n

/-- the n-th derivative of k in integral form. -/
def IK (n : ℕ) (x : ℝ) : ℝ :=
  ∫ s in (-(1 / 2 : ℝ))..(1 / 2), gK n s * Real.cos (2 * Real.pi * x * s + n * (Real.pi / 2))

theorem continuous_gK (n : ℕ) : Continuous (gK n) := by
  unfold gK
  fun_prop

/-- differentiation under the integral sign. -/
theorem hasDerivAt_intCos {g : ℝ → ℝ} (hg : Continuous g) (θ x₀ : ℝ) :
    HasDerivAt (fun x => ∫ s in (-(1 / 2 : ℝ))..(1 / 2), g s * Real.cos (2 * Real.pi * x * s + θ))
      (∫ s in (-(1 / 2 : ℝ))..(1 / 2),
        g s * (2 * Real.pi * s) * Real.cos (2 * Real.pi * x₀ * s + (θ + Real.pi / 2))) x₀ := by
  have hF : ∀ x, Continuous fun s => g s * Real.cos (2 * Real.pi * x * s + θ) := fun x => by fun_prop
  have hF' : ∀ x, Continuous fun s =>
      g s * (2 * Real.pi * s) * Real.cos (2 * Real.pi * x * s + (θ + Real.pi / 2)) := fun x => by fun_prop
  have hb : Continuous fun s => |g s * (2 * Real.pi * s)| := by fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (F := fun x s => g s * Real.cos (2 * Real.pi * x * s + θ))
    (F' := fun x s => g s * (2 * Real.pi * s) * Real.cos (2 * Real.pi * x * s + (θ + Real.pi / 2)))
    (x₀ := x₀) (s := Set.univ) (bound := fun s => |g s * (2 * Real.pi * s)|)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (hF x).aestronglyMeasurable)
    ((hF x₀).intervalIntegrable _ _)
    ((hF' x₀).aestronglyMeasurable)
    (ae_of_all _ fun t _ x _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    (hb.intervalIntegrable _ _)
    (ae_of_all _ fun t _ x _ => by
      have h := ((((hasDerivAt_id' x).const_mul (2 * Real.pi)).mul_const t).add_const θ).cos.const_mul (g t)
      have e : g t * (-Real.sin (2 * Real.pi * x * t + θ) * (2 * Real.pi * 1 * t))
          = g t * (2 * Real.pi * t) * Real.cos (2 * Real.pi * x * t + (θ + Real.pi / 2)) := by
        rw [← add_assoc, Real.cos_add_pi_div_two]
        ring
      rw [e] at h
      exact h)
  exact key.2

theorem hasDerivAt_IK (n : ℕ) (x : ℝ) : HasDerivAt (IK n) (IK (n + 1) x) x := by
  have h := hasDerivAt_intCos (continuous_gK n) (n * (Real.pi / 2)) x
  unfold IK
  convert h using 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [gK]
  push_cast
  rw [show ((n : ℝ) + 1) * (Real.pi / 2) = n * (Real.pi / 2) + Real.pi / 2 by ring, pow_succ]
  ring

theorem kCos_eq_IK0 : kCos = IK 0 := by
  funext x
  rw [← kPsi_psiCos16_eq' x]
  unfold kPsi psiCos16 IK gK
  rw [integral_cos_mul_half, show (8 / 5 : ℝ) / 2 = 4 / 5 by norm_num, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]
  ring

theorem kCos1_eq_IK1 : kCos1 = IK 1 := by
  funext x
  have h := hasDerivAt_kCos x
  rw [kCos_eq_IK0] at h
  exact h.unique (hasDerivAt_IK 0 x)

theorem kCos2_eq_IK2 : kCos2 = IK 2 := by
  funext x
  have h := hasDerivAt_kCos1 x
  rw [kCos1_eq_IK1] at h
  exact h.unique (hasDerivAt_IK 1 x)

theorem hasDerivAt_kCos2_IK3 (x : ℝ) : HasDerivAt kCos2 (IK 3 x) x := by
  rw [kCos2_eq_IK2]
  exact hasDerivAt_IK 2 x

theorem hasDerivAt_kCos2 (x : ℝ) : HasDerivAt kCos2 (deriv kCos2 x) x := by
  rw [(hasDerivAt_kCos2_IK3 x).deriv]
  exact hasDerivAt_kCos2_IK3 x

/-! ### The moment bound -/

theorem integral_abs_cube : ∫ s in (-(1 / 2 : ℝ))..(1 / 2), |s| ^ 3 = 1 / 32 := by
  have hc : Continuous fun s : ℝ => |s| ^ 3 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h1 : ∫ s in (-(1 / 2 : ℝ))..0, |s| ^ 3 = ∫ s in (-(1 / 2 : ℝ))..0, -(s ^ 3) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    show |s| ^ 3 = -(s ^ 3)
    rw [abs_of_nonpos hs.2]
    ring
  have h2 : ∫ s in (0 : ℝ)..(1 / 2), |s| ^ 3 = ∫ s in (0 : ℝ)..(1 / 2), s ^ 3 := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    show |s| ^ 3 = s ^ 3
    rw [abs_of_nonneg hs.1]
  rw [h1, h2, intervalIntegral.integral_neg, integral_pow, integral_pow]
  norm_num

theorem cos_cube_moment :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (8 / 5 * s) * |s| ^ 3
      ≤ 1 / 32 * ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (8 / 5 * s) := by
  set s0 : ℝ := (1 / 32 : ℝ) ^ ((3 : ℕ)⁻¹ : ℝ) with hs0_def
  have hs0 : s0 ^ 3 = 1 / 32 := Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  have hs00 : 0 ≤ s0 := Real.rpow_nonneg (by norm_num) _
  have hs01 : s0 ≤ 1 / 2 := by
    by_contra h
    rw [not_le] at h
    have : (1 / 2 : ℝ) ^ 3 ≤ s0 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
    rw [hs0] at this
    norm_num at this
  have hpi : (4 / 5 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  set C := Real.cos (8 / 5 * s0) with hC
  have hpt : ∀ s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), 0 ≤ (Real.cos (8 / 5 * s) - C) * (1 / 32 - |s| ^ 3) := by
    intro s hs
    have habs : |s| ≤ 1 / 2 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hcs : Real.cos (8 / 5 * s) = Real.cos (8 / 5 * |s|) := by
      rw [← Real.cos_abs (8 / 5 * s), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)]
    rw [hcs]
    rcases le_total |s| s0 with h | h
    · have e1 : |s| ^ 3 ≤ s0 ^ 3 := pow_le_pow_left₀ (abs_nonneg s) h 3
      have e2 : C ≤ Real.cos (8 / 5 * |s|) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
      rw [hs0] at e1
      exact mul_nonneg (by linarith) (by linarith)
    · have e1 : s0 ^ 3 ≤ |s| ^ 3 := pow_le_pow_left₀ hs00 h 3
      have e2 : Real.cos (8 / 5 * |s|) ≤ C :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
      rw [hs0] at e1
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hint := intervalIntegral.integral_nonneg (μ := volume) (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2) hpt
  have hc1 : Continuous fun s : ℝ => 1 / 32 * Real.cos (8 / 5 * s) := by fun_prop
  have hc2 : Continuous fun s : ℝ => Real.cos (8 / 5 * s) * |s| ^ 3 := by fun_prop
  have hc3 : Continuous fun s : ℝ => C * (1 / 32 - |s| ^ 3) := by fun_prop
  have hexp : ∀ s : ℝ, (Real.cos (8 / 5 * s) - C) * (1 / 32 - |s| ^ 3)
      = (1 / 32 * Real.cos (8 / 5 * s) - Real.cos (8 / 5 * s) * |s| ^ 3) - C * (1 / 32 - |s| ^ 3) := by
    intro s; ring
  simp_rw [hexp] at hint
  have hc12 : Continuous fun s : ℝ => 1 / 32 * Real.cos (8 / 5 * s) - Real.cos (8 / 5 * s) * |s| ^ 3 := by
    fun_prop
  rw [intervalIntegral.integral_sub (hc12.intervalIntegrable _ _) (hc3.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s : ℝ => |s| ^ 3).intervalIntegrable _ _),
    integral_abs_cube, intervalIntegral.integral_const] at hint
  have hz : ((1 / 2 : ℝ) - -(1 / 2)) * (1 / 32 : ℝ) - 1 / 32 = 0 := by norm_num
  simp only [smul_eq_mul, hz, mul_zero, sub_zero] at hint
  linarith

theorem sinc_four_fifths_pos : 0 < Real.sinc (4 / 5) := by
  rw [Real.sinc_of_ne_zero (by norm_num)]
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])) (by norm_num)

theorem abs_IK3_le (x : ℝ) : |IK 3 x| ≤ Real.pi ^ 3 / 4 := by
  have hA := sinc_four_fifths_pos
  set A := Real.sinc (4 / 5) with hA_def
  unfold IK
  have hab : -(1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  have hmono : ∫ s in (-(1 / 2 : ℝ))..(1 / 2), |gK 3 s * Real.cos (2 * Real.pi * x * s + ((3 : ℕ) : ℝ) * (Real.pi / 2))|
      ≤ ∫ s in (-(1 / 2 : ℝ))..(1 / 2), 8 * Real.pi ^ 3 / A * (Real.cos (8 / 5 * s) * |s| ^ 3) := by
    refine intervalIntegral.integral_mono_on hab
      ((by unfold gK; fun_prop : Continuous fun s =>
        |gK 3 s * Real.cos (2 * Real.pi * x * s + ((3 : ℕ) : ℝ) * (Real.pi / 2))|).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s : ℝ =>
        8 * Real.pi ^ 3 / A * (Real.cos (8 / 5 * s) * |s| ^ 3)).intervalIntegrable _ _) fun s hs => ?_
    have hcos : 0 ≤ Real.cos (8 / 5 * s) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> nlinarith [Real.pi_gt_three, hs.1, hs.2]
    rw [abs_mul]
    calc |gK 3 s| * |Real.cos (2 * Real.pi * x * s + ((3 : ℕ) : ℝ) * (Real.pi / 2))|
        ≤ |gK 3 s| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = 8 * Real.pi ^ 3 / A * (Real.cos (8 / 5 * s) * |s| ^ 3) := by
        unfold gK
        rw [mul_one, abs_mul, abs_div, abs_of_nonneg hcos, abs_of_pos hA, abs_pow, abs_mul, abs_mul,
          abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have hm := cos_cube_moment
  rw [integral_cos_mul_half, show (8 / 5 : ℝ) / 2 = 4 / 5 by norm_num, ← hA_def] at hm
  calc 8 * Real.pi ^ 3 / A * ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (8 / 5 * s) * |s| ^ 3
      ≤ 8 * Real.pi ^ 3 / A * (1 / 32 * A) :=
        mul_le_mul_of_nonneg_left hm (div_nonneg (by positivity) hA.le)
    _ = Real.pi ^ 3 / 4 := by
        field_simp
        ring

/-- |k‴| ≤ π³/4 (k = E_v cos(2πxs), |s| ≤ 1/2, E_v|s|³ ≤ 1/32 for v = cos(1.6 s)/∫cos(1.6 s)). -/
theorem kCos_d3_bound (x : ℝ) : |deriv kCos2 x| ≤ Real.pi ^ 3 / 4 := by
  rw [(hasDerivAt_kCos2_IK3 x).deriv]
  exact abs_IK3_le x

end ZetaS.CertV2
