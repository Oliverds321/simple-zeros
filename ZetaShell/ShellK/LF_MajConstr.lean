/-
F1c-3c2, construction (L7_3, round 8): **a C¹ majorant built from Mathlib's `Real.smoothTransition`**, generic in the
data, so that `majorant_excess` (and later K3's weight `1 − ℒ/s`) can use it.
* `rampF a w y = smoothTransition((y − a)/w)`: `0` for `y ≤ a`, `1` for `y ≥ a + w`, `|ramp′| ≤ S/w`
  (`S = sup|smoothTransition′|`, finite: continuous, `0` off `[0,1]`).
* `vF c m y = c(y − 1)/((y − 1)² + m²)`: smooth everywhere, `|vF| ≤ c/(2m)`, `|vF′| ≤ c/m²`, and
  `vF ≥ ℒ/(y − 1)` once `c = (1+κ)ℒ` and `κ(y − 1)² ≥ m²` (a smooth stand-in for `ℒ/(y − 1)`).
* `WF`: the weight majorant `C·A(1 − B) + vF·B·(1 + (C − 1)D)` with three ramps `A, B, D` (rise to `C` before `s₀`,
  fall to `ℒ/s` after `log Q + 4`, rise to `Cℒ/s` before `α′ℒ`).
* `FF = (g + 2(1 − smoothTransition(y − L)))·WF`: `C¹`, with an explicit bound on `|FF′|`.
-/
import ZetaShell.ShellK.LF_OutDiag
import ZetaShell.Design.SD_A7_Regime

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

/-! ### The smooth step -/

theorem st_contDiff : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff

theorem st_hasDerivAt (t : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
  ((st_contDiff.differentiable one_ne_zero) t).hasDerivAt

theorem st_deriv_zero_of_lt {x : ℝ} (hx : x < 0) : deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq]; simp

theorem st_deriv_zero_of_gt {x : ℝ} (hx : 1 < x) : deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [h.deriv_eq]; simp

theorem st_deriv_bound : ∃ S : ℝ, 0 ≤ S ∧ ∀ x, |deriv Real.smoothTransition x| ≤ S := by
  have hc : Continuous (deriv Real.smoothTransition) := st_contDiff.continuous_deriv le_rfl
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max S 0, le_max_right _ _, fun x => ?_⟩
  by_cases h0 : x < 0
  · rw [st_deriv_zero_of_lt h0, abs_zero]; exact le_max_right _ _
  by_cases h1 : 1 < x
  · rw [st_deriv_zero_of_gt h1, abs_zero]; exact le_max_right _ _
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt h0, le_of_not_gt h1⟩
  have := hS x hx
  rw [Real.norm_eq_abs] at this
  exact le_trans this (le_max_left _ _)

/-! ### Ramps -/

/-- the ramp `0 → 1` on `[a, a + w]`. -/
def rampF (a w y : ℝ) : ℝ := Real.smoothTransition ((y - a) / w)

theorem rampF_zero {a w y : ℝ} (hw : 0 < w) (hy : y ≤ a) : rampF a w y = 0 := by
  unfold rampF
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le

theorem rampF_one {a w y : ℝ} (hw : 0 < w) (hy : a + w ≤ y) : rampF a w y = 1 := by
  unfold rampF
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hw]; linarith

theorem rampF_nonneg (a w y : ℝ) : 0 ≤ rampF a w y := Real.smoothTransition.nonneg _
theorem rampF_le_one (a w y : ℝ) : rampF a w y ≤ 1 := Real.smoothTransition.le_one _

theorem rampF_contDiff (a w : ℝ) : ContDiff ℝ 1 (rampF a w) :=
  st_contDiff.comp ((contDiff_id.sub contDiff_const).div_const w)

theorem rampF_hasDerivAt (a w y : ℝ) :
    HasDerivAt (rampF a w) (deriv Real.smoothTransition ((y - a) / w) * (1 / w)) y := by
  have h1 : HasDerivAt (fun y : ℝ => (y - a) / w) (1 / w) y := ((hasDerivAt_id y).sub_const a).div_const w
  exact (st_hasDerivAt ((y - a) / w)).comp y h1

/-! ### The smooth stand-in for `ℒ/(y − 1)` -/

/-- `c(y − 1)/((y − 1)² + m²)`. -/
def vF (c m y : ℝ) : ℝ := c * (y - 1) / ((y - 1) ^ 2 + m ^ 2)

theorem vF_den_pos {m : ℝ} (hm : 0 < m) (y : ℝ) : 0 < (y - 1) ^ 2 + m ^ 2 := by positivity

theorem vF_contDiff {c m : ℝ} (hm : 0 < m) : ContDiff ℝ 1 (vF c m) := by
  unfold vF
  refine (contDiff_const.mul (contDiff_id.sub contDiff_const)).div
    (((contDiff_id.sub contDiff_const).pow 2).add contDiff_const) fun y => (vF_den_pos hm y).ne'

theorem vF_hasDerivAt {c m : ℝ} (hm : 0 < m) (y : ℝ) :
    HasDerivAt (vF c m) (c * (m ^ 2 - (y - 1) ^ 2) / ((y - 1) ^ 2 + m ^ 2) ^ 2) y := by
  have hf : HasDerivAt (fun y : ℝ => c * (y - 1)) c y :=
    (((hasDerivAt_id' y).sub_const 1).const_mul c).congr_deriv (by ring)
  have hg : HasDerivAt (fun y : ℝ => (y - 1) ^ 2 + m ^ 2) (2 * (y - 1)) y :=
    ((((hasDerivAt_id' y).sub_const 1).pow 2).add_const (m ^ 2)).congr_deriv (by norm_num)
  have h := hf.div hg (vF_den_pos hm y).ne'
  have e : (c * ((y - 1) ^ 2 + m ^ 2) - c * (y - 1) * (2 * (y - 1))) / ((y - 1) ^ 2 + m ^ 2) ^ 2
      = c * (m ^ 2 - (y - 1) ^ 2) / ((y - 1) ^ 2 + m ^ 2) ^ 2 := by ring
  rw [e] at h
  exact h

theorem vF_abs_le {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (y : ℝ) : |vF c m y| ≤ c / (2 * m) := by
  unfold vF
  have hd := vF_den_pos hm y
  rw [abs_div, abs_mul, abs_of_nonneg hc, abs_of_pos hd, div_le_div_iff₀ hd (by positivity)]
  have : 2 * m * |y - 1| ≤ (y - 1) ^ 2 + m ^ 2 := by
    nlinarith [sq_nonneg (|y - 1| - m), sq_abs (y - 1)]
  nlinarith [abs_nonneg (y - 1)]

theorem vF_deriv_abs_le {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (y : ℝ) :
    |c * (m ^ 2 - (y - 1) ^ 2) / ((y - 1) ^ 2 + m ^ 2) ^ 2| ≤ c / m ^ 2 := by
  have hd := vF_den_pos hm y
  rw [abs_div, abs_mul, abs_of_nonneg hc, abs_of_pos (by positivity : (0:ℝ) < ((y - 1) ^ 2 + m ^ 2) ^ 2),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |m ^ 2 - (y - 1) ^ 2| ≤ (y - 1) ^ 2 + m ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg m]
  have h2 : m ^ 2 ≤ (y - 1) ^ 2 + m ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have := mul_le_mul h1 h2 (by positivity) (by positivity)
  have := mul_le_mul_of_nonneg_left this hc
  nlinarith

theorem vF_le {c m y : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (hy : 1 < y) : vF c m y ≤ c / (y - 1) := by
  unfold vF
  have hd := vF_den_pos hm y
  rw [div_le_div_iff₀ hd (by linarith)]
  have := mul_nonneg hc (sq_nonneg m)
  nlinarith

theorem vF_nonneg {c m y : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (hy : 1 ≤ y) : 0 ≤ vF c m y := by
  unfold vF
  exact div_nonneg (mul_nonneg hc (by linarith)) (vF_den_pos hm y).le

/-- `vF ≥ ℒ/(y−1)` when `c = (1+κ)ℒ` and `κ(y−1)² ≥ m²`. -/
theorem vF_ge {LL κ m y : ℝ} (hL : 0 ≤ LL) (hm : 0 < m) (hy : 1 < y) (hκ : m ^ 2 ≤ κ * (y - 1) ^ 2) :
    LL / (y - 1) ≤ vF ((1 + κ) * LL) m y := by
  unfold vF
  have hd := vF_den_pos hm y
  rw [div_le_div_iff₀ (by linarith) hd]
  have := mul_le_mul_of_nonneg_left hκ hL
  nlinarith

end F1c
end ShellK
end ZetaShell
