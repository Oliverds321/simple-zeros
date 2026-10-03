/-
L7_5 (28 Sep 2026), round 3: SHARED facts about `D_T(v) = ∫_T^{2T} e^{iτv} dτ` (macros.tex `\DT`), Mathlib only.
Any definition that unfolds to `∫ τ in T..(2 * T), Complex.exp (Complex.I * τ * v)` (L7_5's `ZetaShell.PropZ.DT`,
L7_3/L7_9's `LK_Defs.DT`, L7_6/L7_8's `DTk`) can use these by `show`/`rfl`.
  * `DTf_eq_closed`: `D_T(v) = T e^{iTv} g(iTv)` with `g = dslope exp 0` (`g(z) = (e^z−1)/z`, `g(0) = 1`), entire;
  * `DTf_contDiff`: `D_T` is `C^∞` in `v` (every order);
  * `DTf_zero`: `D_T(0) = T`;  `norm_DTf_le`: `‖D_T(v)‖ ≤ T` for `T ≥ 0`;
  * `hasDerivAt_DTf`, `norm_deriv_DTf_le`: `D_T′(v) = ∫_T^{2T} iτ e^{iτv} dτ`, `‖D_T′(v)‖ ≤ 2T²` for `T ≥ 0`;
  * `deriv_DTf_eq_ibp`, `norm_deriv_DTf_le_div`: for `v ≠ 0`, `D_T′(v) = (2Te^{2iTv} − Te^{iTv} − D_T(v))/v` and
    `‖D_T′(v)‖ ≤ 4T/|v|` (`T ≥ 0`).
-/
import Mathlib

open MeasureTheory Complex

namespace ZetaShell.DTFacts

/-- `D_T(v) = ∫_T^{2T} e^{iτv} dτ`. -/
noncomputable def DTf (T v : ℝ) : ℂ := ∫ τ in T..(2 * T), Complex.exp (Complex.I * τ * v)

/-- `g(z) = (e^z − 1)/z`, `g(0) = 1`: an entire function. -/
noncomputable def gexp : ℂ → ℂ := dslope Complex.exp 0

theorem gexp_differentiable : Differentiable ℂ gexp := by
  intro z
  have h : DifferentiableOn ℂ (dslope Complex.exp 0) Set.univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr Complex.differentiable_exp.differentiableOn
  exact (h z (Set.mem_univ z)).differentiableAt Filter.univ_mem

theorem gexp_contDiff {n : WithTop ℕ∞} : ContDiff ℂ n gexp := gexp_differentiable.contDiff

theorem gexp_zero : gexp 0 = 1 := by
  simp [gexp, dslope_same, Complex.deriv_exp]

theorem gexp_of_ne {z : ℂ} (hz : z ≠ 0) : gexp z = (Complex.exp z - 1) / z := by
  simp [gexp, dslope_of_ne _ hz, slope_def_field]

/-- closed form: `D_T(v) = T e^{iTv} g(iTv)`. -/
theorem DTf_eq_closed (T v : ℝ) :
    DTf T v = (T : ℂ) * Complex.exp (Complex.I * T * v) * gexp (Complex.I * T * v) := by
  unfold DTf
  by_cases hv : v = 0
  · subst hv; simp [gexp_zero]; ring
  by_cases hT : T = 0
  · subst hT; simp
  have hc : Complex.I * (v : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hv)
  have hz : Complex.I * T * v ≠ 0 := by
    have : (T : ℂ) ≠ 0 := by exact_mod_cast hT
    have : (v : ℂ) ≠ 0 := by exact_mod_cast hv
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero ‹(T : ℂ) ≠ 0›) this
  have e : (fun τ : ℝ => Complex.exp (Complex.I * τ * v)) = fun τ : ℝ => Complex.exp ((Complex.I * v) * τ) := by
    funext τ; ring_nf
  rw [e, integral_exp_mul_complex hc, gexp_of_ne hz]
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  rw [show Complex.I * v * ((2 * T : ℝ) : ℂ) = Complex.I * T * v + Complex.I * T * v by push_cast; ring,
    Complex.exp_add]
  field_simp

theorem DTf_contDiff (T : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (DTf T) := by
  have e : DTf T = fun v : ℝ => (T : ℂ) * Complex.exp (Complex.I * T * v) * gexp (Complex.I * T * v) :=
    funext (DTf_eq_closed T)
  rw [e]
  have hof : ContDiff ℝ n (fun v : ℝ => (v : ℂ)) := Complex.ofRealCLM.contDiff
  have hlin : ContDiff ℝ n (fun v : ℝ => Complex.I * T * (v : ℂ)) := contDiff_const.mul hof
  have hg : ContDiff ℝ n gexp := (gexp_contDiff (n := n)).restrict_scalars ℝ
  have hexp : ContDiff ℝ n (fun v : ℝ => Complex.exp (Complex.I * T * v)) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := n)).comp hlin
  exact (contDiff_const.mul hexp).mul (hg.comp hlin)

theorem DTf_continuous (T : ℝ) : Continuous (DTf T) := (DTf_contDiff T (n := 0)).continuous

theorem DTf_zero (T : ℝ) : DTf T 0 = T := by
  unfold DTf; simp; ring

theorem norm_DTf_le {T : ℝ} (hT : 0 ≤ T) (v : ℝ) : ‖DTf T v‖ ≤ T := by
  unfold DTf
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T) (C := 1)
    (f := fun τ : ℝ => Complex.exp (Complex.I * τ * v)) (fun τ _ => by
      rw [show Complex.I * (τ : ℂ) * v = ((τ * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])
  rw [abs_of_nonneg (by linarith)] at h
  linarith

/-- `D_T′(v) = ∫_T^{2T} iτ e^{iτv} dτ` (differentiation under the integral on a compact interval). -/
theorem hasDerivAt_DTf (T v : ℝ) :
    HasDerivAt (DTf T) (∫ τ in T..(2 * T), Complex.I * τ * Complex.exp (Complex.I * τ * v)) v := by
  have key : ∀ τ w : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (Complex.I * τ * w))
      (Complex.I * τ * Complex.exp (Complex.I * τ * w)) w := by
    intro τ w
    have h1 : HasDerivAt (fun w : ℝ => Complex.I * τ * (w : ℂ)) (Complex.I * τ * 1) w :=
      (Complex.ofRealCLM.hasDerivAt (x := w)).const_mul (Complex.I * τ)
    have := (Complex.hasDerivAt_exp (Complex.I * τ * w)).comp w h1
    refine this.congr_deriv ?_
    ring
  have hb : ∀ τ w : ℝ, ‖Complex.I * τ * Complex.exp (Complex.I * τ * w)‖ = |τ| := by
    intro τ w
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      show Complex.I * (τ : ℂ) * w = ((τ * w : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := T)
    (b := 2 * T) (F := fun (w : ℝ) (τ : ℝ) => Complex.exp (Complex.I * τ * w))
    (F' := fun (w : ℝ) (τ : ℝ) => Complex.I * τ * Complex.exp (Complex.I * τ * w)) (x₀ := v) (s := Set.univ)
    (bound := fun τ => |τ|) Filter.univ_mem
    (Filter.Eventually.of_forall fun w => (by fun_prop : Continuous fun τ : ℝ =>
      Complex.exp (Complex.I * τ * w)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun τ : ℝ => Complex.exp (Complex.I * τ * v)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun τ : ℝ =>
      Complex.I * τ * Complex.exp (Complex.I * τ * v)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun τ _ w _ => (hb τ w).le)
    (continuous_abs.intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun τ _ w _ => key τ w)
  exact this.2

theorem norm_deriv_DTf_le {T : ℝ} (hT : 0 ≤ T) (v : ℝ) : ‖deriv (DTf T) v‖ ≤ 2 * T ^ 2 := by
  rw [(hasDerivAt_DTf T v).deriv]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T) (C := 2 * T)
    (f := fun τ : ℝ => Complex.I * τ * Complex.exp (Complex.I * τ * v)) (fun τ hτ => by
      rw [Set.uIoc_of_le (by linarith)] at hτ
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        show Complex.I * (τ : ℂ) * v = ((τ * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos (by linarith [hτ.1])]
      linarith [hτ.2])
  rw [abs_of_nonneg (by linarith)] at h
  nlinarith

/-- integration by parts: `D_T′(v) = (2T e^{2iTv} − T e^{iTv} − D_T(v))/v` for `v ≠ 0`. -/
theorem deriv_DTf_eq_ibp (T v : ℝ) (hv : v ≠ 0) :
    deriv (DTf T) v = ((2 * T : ℝ) * Complex.exp (Complex.I * (2 * T : ℝ) * v)
      - (T : ℂ) * Complex.exp (Complex.I * T * v) - DTf T v) / v := by
  rw [(hasDerivAt_DTf T v).deriv]
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  have hu : ∀ τ ∈ Set.uIcc T (2 * T), HasDerivAt (fun τ : ℝ => (τ : ℂ)) 1 τ :=
    fun τ _ => Complex.ofRealCLM.hasDerivAt
  have hw : ∀ τ ∈ Set.uIcc T (2 * T), HasDerivAt (fun τ : ℝ => Complex.exp (Complex.I * τ * v) / v)
      (Complex.I * Complex.exp (Complex.I * τ * v)) τ := by
    intro τ _
    have h1 : HasDerivAt (fun τ : ℝ => Complex.I * (τ : ℂ) * v) (Complex.I * 1 * v) τ :=
      ((Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul Complex.I).mul_const (v : ℂ)
    have := ((Complex.hasDerivAt_exp (Complex.I * τ * v)).comp τ h1).div_const (v : ℂ)
    refine this.congr_deriv ?_
    field_simp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hw
    (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun τ : ℝ => Complex.I * Complex.exp (Complex.I * τ * v)).intervalIntegrable _ _)
  have e1 : (∫ τ in T..(2 * T), Complex.I * τ * Complex.exp (Complex.I * τ * v))
      = ∫ τ in T..(2 * T), (τ : ℂ) * (Complex.I * Complex.exp (Complex.I * τ * v)) := by
    congr 1; funext τ; ring
  have e2 : (∫ τ in T..(2 * T), (1 : ℂ) * (Complex.exp (Complex.I * τ * v) / v)) = DTf T v / v := by
    unfold DTf
    simp only [one_mul]
    rw [intervalIntegral.integral_div]
  rw [e1, hibp, e2]
  push_cast
  field_simp

theorem norm_deriv_DTf_le_div {T : ℝ} (hT : 0 ≤ T) {v : ℝ} (hv : v ≠ 0) :
    ‖deriv (DTf T) v‖ ≤ 4 * T / |v| := by
  rw [deriv_DTf_eq_ibp T v hv, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hva : 0 < |v| := abs_pos.mpr hv
  rw [div_le_div_iff_of_pos_right hva]
  have hn : ∀ x : ℝ, ‖Complex.exp (Complex.I * x * v)‖ = 1 := fun x => by
    rw [show Complex.I * (x : ℂ) * v = ((x * v : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have h1 : ‖((2 * T : ℝ) : ℂ) * Complex.exp (Complex.I * (2 * T : ℝ) * v)‖ = 2 * T := by
    rw [norm_mul, hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), mul_one]
  have h2 : ‖(T : ℂ) * Complex.exp (Complex.I * T * v)‖ = T := by
    rw [norm_mul, hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT, mul_one]
  have h3 := norm_DTf_le hT v
  calc ‖((2 * T : ℝ) : ℂ) * Complex.exp (Complex.I * (2 * T : ℝ) * v) - (T : ℂ) * Complex.exp (Complex.I * T * v)
        - DTf T v‖
      ≤ ‖((2 * T : ℝ) : ℂ) * Complex.exp (Complex.I * (2 * T : ℝ) * v)‖
        + ‖(T : ℂ) * Complex.exp (Complex.I * T * v)‖ + ‖DTf T v‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 4 * T := by rw [h1, h2]; linarith

end ZetaShell.DTFacts
