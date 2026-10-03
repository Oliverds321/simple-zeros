/-
L7_5 (28 Sep 2026), round 4: the Mellin decay estimate, SHARED by `Z5R_W` and `ZB_parts_bounded` (report R2.1 (a4)).
For `V` of class `C²` with compact support in `(1,∞)` and `φ(u) = V(e^u)`:
  `Ṽ(w) = ∫ φ(u) e^{wu} du`                                   (`mellin_eq_integral_phi`, from `integral_eq_mellin`),
  `Ṽ(w) = w^{−2} ∫ φ″(u) e^{wu} du`  for `w ≠ 0`              (`mellin_eq_ibp2`, two integrations by parts),
  `‖Ṽ(w)‖ ≤ ∫ ‖φ(u)‖ e^{u Re w} du`                          (`norm_mellin_le_trivial`),
  `‖Ṽ(w)‖ ≤ ‖w‖^{−2} ∫ ‖φ″(u)‖ e^{u Re w} du`  for `w ≠ 0`   (`norm_mellin_le_ibp2`).
-/
import ZetaShell.PropZ.Z5b_Weil

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem hasDerivAt_cexp_div (w : ℂ) (hw : w ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (w * t) / w) (Complex.exp (w * t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => w * (t : ℂ)) (w * 1) t :=
    (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul w
  have := ((Complex.hasDerivAt_exp (w * t)).comp t h1).div_const w
  refine this.congr_deriv ?_
  field_simp

/-- one integration by parts on `ℝ` against `e^{wu}`, for `φ ∈ C¹_c`. -/
theorem integral_cexp_ibp (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (w : ℂ) (hw : w ≠ 0) :
    ∫ u : ℝ, φ u * Complex.exp (w * u) = -(1 / w) * ∫ u : ℝ, deriv φ u * Complex.exp (w * u) := by
  have hu : ∀ t : ℝ, HasDerivAt φ (deriv φ t) t := fun t => (hφ.differentiable one_ne_zero t).hasDerivAt
  have hc : Continuous (fun t : ℝ => Complex.exp (w * t)) := by fun_prop
  have hdc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have i1 : Integrable (φ * fun t : ℝ => Complex.exp (w * t)) :=
    (hφ.continuous.mul hc).integrable_of_hasCompactSupport (hφc.mul_right)
  have i2 : Integrable (deriv φ * fun t : ℝ => Complex.exp (w * t) / w) :=
    (hdc.mul (hc.div_const w)).integrable_of_hasCompactSupport (hφc.deriv.mul_right)
  have i3 : Integrable (φ * fun t : ℝ => Complex.exp (w * t) / w) :=
    (hφ.continuous.mul (hc.div_const w)).integrable_of_hasCompactSupport (hφc.mul_right)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := φ) (u' := deriv φ)
    (v := fun t : ℝ => Complex.exp (w * t) / w) (v' := fun t : ℝ => Complex.exp (w * t))
    (fun t _ => hu t) (fun t _ => hasDerivAt_cexp_div w hw t) i1 i2 i3
  rw [key]
  have e : (fun t : ℝ => deriv φ t * (Complex.exp (w * t) / w)) = fun t => (1 / w) * (deriv φ t * Complex.exp (w * t)) := by
    funext t; field_simp
  rw [e, integral_const_mul]; ring

theorem phi_hasCompactSupport (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVpos : tsupport V ⊆ Set.Ioi 1) :
    HasCompactSupport (fun u : ℝ => V (Real.exp u)) := by
  refine HasCompactSupport.intro (K := Real.log '' tsupport V) ?_ ?_
  · refine hVc.isCompact.image_of_continuousOn (Real.continuousOn_log.mono fun x hx => ?_)
    have := hVpos hx; simp only [Set.mem_Ioi] at this
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
  · intro u hu
    by_contra h
    exact hu ⟨Real.exp u, subset_tsupport _ h, Real.log_exp u⟩

theorem mellin_eq_integral_phi (V : ℝ → ℂ) (hVpos : tsupport V ⊆ Set.Ioi 1) (w : ℂ) :
    mellin V w = ∫ u : ℝ, V (Real.exp u) * Complex.exp (w * u) := (integral_eq_mellin V hVpos w).symm

/-- two integrations by parts: `Ṽ(w) = w^{−2} ∫ φ″ e^{wu}`. -/
theorem mellin_eq_ibp2 (V : ℝ → ℂ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (hVpos : tsupport V ⊆ Set.Ioi 1) (w : ℂ) (hw : w ≠ 0) :
    mellin V w = (1 / w ^ 2) * ∫ u : ℝ, deriv (deriv (fun u : ℝ => V (Real.exp u))) u * Complex.exp (w * u) := by
  set φ : ℝ → ℂ := fun u => V (Real.exp u) with hφdef
  have hφ2 : ContDiff ℝ (⊤ : ℕ∞) φ := hV.comp Real.contDiff_exp
  have hφc : HasCompactSupport φ := phi_hasCompactSupport V hVc hVpos
  have hφ1 : ContDiff ℝ 1 φ := hφ2.of_le (by exact_mod_cast le_top)
  have hd1 : ContDiff ℝ 1 (deriv φ) := (contDiff_infty_iff_deriv.mp hφ2).2.of_le (by exact_mod_cast le_top)
  rw [mellin_eq_integral_phi V hVpos w]
  rw [show (fun u : ℝ => V (Real.exp u) * Complex.exp (w * u)) = fun u => φ u * Complex.exp (w * u) from rfl]
  rw [integral_cexp_ibp φ hφ1 hφc w hw, integral_cexp_ibp (deriv φ) hd1 hφc.deriv w hw]
  field_simp

theorem norm_cexp_mul_ofReal (w : ℂ) (u : ℝ) : ‖Complex.exp (w * u)‖ = Real.exp (w.re * u) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem norm_mellin_le_trivial (V : ℝ → ℂ) (hVpos : tsupport V ⊆ Set.Ioi 1) (w : ℂ) :
    ‖mellin V w‖ ≤ ∫ u : ℝ, ‖V (Real.exp u)‖ * Real.exp (w.re * u) := by
  rw [mellin_eq_integral_phi V hVpos w]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u; rw [norm_mul, norm_cexp_mul_ofReal]

theorem norm_mellin_le_ibp2 (V : ℝ → ℂ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (hVpos : tsupport V ⊆ Set.Ioi 1) (w : ℂ) (hw : w ≠ 0) :
    ‖mellin V w‖ ≤ (1 / ‖w‖ ^ 2) *
      ∫ u : ℝ, ‖deriv (deriv (fun u : ℝ => V (Real.exp u))) u‖ * Real.exp (w.re * u) := by
  rw [mellin_eq_ibp2 V hV hVc hVpos w hw, norm_mul]
  have h1 : ‖(1 / w ^ 2 : ℂ)‖ = 1 / ‖w‖ ^ 2 := by rw [norm_div, norm_one, norm_pow]
  rw [h1]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u; rw [norm_mul, norm_cexp_mul_ofReal]

end ZetaShell.PropZ
