/-
F1c-3c2, construction part 2 (L7_3, round 8): the weight majorant `WF`, the product `FF`, `C¹`-ness and the explicit
derivative bound `|FF′| ≤ (2 + 2S)(C + Cc/(2m)) + (ĝ + 2)(2CS/ρ + Cc/m² + 2C(c/(2m))S/ρ)`, generic in the data
(`g` any `C¹` function with `|g′| ≤ 2`, `0 ≤ g ≤ ĝ`).
-/
import ZetaShell.ShellK.LF_MajConstr

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

/-- the weight majorant: `C·A(1 − B) + vF·B·(1 + (C − 1)D)`. -/
def WF (C c m ρ a₁ a₂ a₃ : ℝ) (y : ℝ) : ℝ :=
  C * rampF a₁ ρ y * (1 - rampF a₂ ρ y) + vF c m y * rampF a₂ ρ y * (1 + (C - 1) * rampF a₃ ρ y)

/-- the window majorant `g + 2(1 − smoothTransition(y − L))` times the weight majorant. -/
def FF (g : ℝ → ℝ) (L C c m ρ a₁ a₂ a₃ : ℝ) (y : ℝ) : ℝ :=
  (g y + 2 * (1 - Real.smoothTransition (y - L))) * WF C c m ρ a₁ a₂ a₃ y

theorem WF_contDiff {C c m ρ a₁ a₂ a₃ : ℝ} (hm : 0 < m) : ContDiff ℝ 1 (WF C c m ρ a₁ a₂ a₃) := by
  have hA := rampF_contDiff a₁ ρ
  have hB := rampF_contDiff a₂ ρ
  have hD := rampF_contDiff a₃ ρ
  have hv := vF_contDiff (c := c) hm
  exact ((contDiff_const.mul hA).mul (contDiff_const.sub hB)).add
    ((hv.mul hB).mul (contDiff_const.add (contDiff_const.mul hD)))

theorem FF_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {L C c m ρ a₁ a₂ a₃ : ℝ} (hm : 0 < m) :
    ContDiff ℝ 1 (FF g L C c m ρ a₁ a₂ a₃) := by
  have hE : ContDiff ℝ 1 (fun y => Real.smoothTransition (y - L)) := st_contDiff.comp (contDiff_id.sub contDiff_const)
  exact (hg.add (contDiff_const.mul (contDiff_const.sub hE))).mul (WF_contDiff hm)

theorem WF_abs_le {C c m ρ a₁ a₂ a₃ : ℝ} (hC : 1 ≤ C) (hc : 0 ≤ c) (hm : 0 < m) (y : ℝ) :
    |WF C c m ρ a₁ a₂ a₃ y| ≤ C + C * (c / (2 * m)) := by
  unfold WF
  have hA0 := rampF_nonneg a₁ ρ y
  have hA1 := rampF_le_one a₁ ρ y
  have hB0 := rampF_nonneg a₂ ρ y
  have hB1 := rampF_le_one a₂ ρ y
  have hD0 := rampF_nonneg a₃ ρ y
  have hD1 := rampF_le_one a₃ ρ y
  have hv := vF_abs_le hc hm y
  have h1 : |C * rampF a₁ ρ y * (1 - rampF a₂ ρ y)| ≤ C := by
    rw [abs_of_nonneg (by have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ C) hA0) (by linarith : (0:ℝ) ≤ 1 - rampF a₂ ρ y); linarith)]
    have : rampF a₁ ρ y * (1 - rampF a₂ ρ y) ≤ 1 := by nlinarith
    nlinarith
  have hE1 : 0 ≤ 1 + (C - 1) * rampF a₃ ρ y := by nlinarith
  have hE2 : 1 + (C - 1) * rampF a₃ ρ y ≤ C := by nlinarith
  have h2 : |vF c m y * rampF a₂ ρ y * (1 + (C - 1) * rampF a₃ ρ y)| ≤ c / (2 * m) * C := by
    rw [abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg hE1]
    have h3 : |vF c m y| * rampF a₂ ρ y ≤ c / (2 * m) := by
      have := mul_le_mul_of_nonneg_left hB1 (abs_nonneg (vF c m y))
      linarith
    have h4 := mul_le_mul h3 hE2 hE1 (by positivity)
    linarith
  calc |C * rampF a₁ ρ y * (1 - rampF a₂ ρ y) + vF c m y * rampF a₂ ρ y * (1 + (C - 1) * rampF a₃ ρ y)|
      ≤ |C * rampF a₁ ρ y * (1 - rampF a₂ ρ y)| + |vF c m y * rampF a₂ ρ y * (1 + (C - 1) * rampF a₃ ρ y)| :=
        abs_add_le _ _
    _ ≤ C + c / (2 * m) * C := by linarith
    _ = C + C * (c / (2 * m)) := by ring

/-- the derivative of `WF`, as a `HasDerivAt`. -/
theorem WF_hasDerivAt {C c m ρ a₁ a₂ a₃ : ℝ} (hm : 0 < m) (y : ℝ) :
    HasDerivAt (WF C c m ρ a₁ a₂ a₃)
      (C * (deriv Real.smoothTransition ((y - a₁) / ρ) * (1 / ρ)) * (1 - rampF a₂ ρ y)
        + C * rampF a₁ ρ y * -(deriv Real.smoothTransition ((y - a₂) / ρ) * (1 / ρ))
        + ((c * (m ^ 2 - (y - 1) ^ 2) / ((y - 1) ^ 2 + m ^ 2) ^ 2 * rampF a₂ ρ y
            + vF c m y * (deriv Real.smoothTransition ((y - a₂) / ρ) * (1 / ρ)))
            * (1 + (C - 1) * rampF a₃ ρ y)
          + vF c m y * rampF a₂ ρ y * ((C - 1) * (deriv Real.smoothTransition ((y - a₃) / ρ) * (1 / ρ))))) y := by
  have hA := rampF_hasDerivAt a₁ ρ y
  have hB := rampF_hasDerivAt a₂ ρ y
  have hD := rampF_hasDerivAt a₃ ρ y
  have hv := vF_hasDerivAt (c := c) hm y
  have t1 := (hA.const_mul C).mul (hB.const_sub 1)
  have t2 := (hv.mul hB).mul ((hD.const_mul (C - 1)).const_add 1)
  exact t1.add t2

theorem WF_deriv_abs_le {C c m ρ a₁ a₂ a₃ S : ℝ} (hC : 1 ≤ C) (hc : 0 ≤ c) (hm : 0 < m) (hρ : 0 < ρ)
    (hS : ∀ x, |deriv Real.smoothTransition x| ≤ S) (y : ℝ) :
    |deriv (WF C c m ρ a₁ a₂ a₃) y| ≤ 2 * C * S / ρ + C * (c / m ^ 2) + 2 * C * (c / (2 * m)) * S / ρ := by
  rw [(WF_hasDerivAt hm y).deriv]
  have hA0 := rampF_nonneg a₁ ρ y
  have hA1 := rampF_le_one a₁ ρ y
  have hB0 := rampF_nonneg a₂ ρ y
  have hB1 := rampF_le_one a₂ ρ y
  have hD0 := rampF_nonneg a₃ ρ y
  have hD1 := rampF_le_one a₃ ρ y
  have hv := vF_abs_le hc hm y
  have hv' := vF_deriv_abs_le hc hm y
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  set sA := deriv Real.smoothTransition ((y - a₁) / ρ) * (1 / ρ)
  set sB := deriv Real.smoothTransition ((y - a₂) / ρ) * (1 / ρ)
  set sD := deriv Real.smoothTransition ((y - a₃) / ρ) * (1 / ρ)
  have hsX : ∀ t, |deriv Real.smoothTransition t * (1 / ρ)| ≤ S / ρ := by
    intro t
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / ρ)]
    have := mul_le_mul_of_nonneg_right (hS t) (by positivity : (0:ℝ) ≤ 1 / ρ)
    calc |deriv Real.smoothTransition t| * (1 / ρ) ≤ S * (1 / ρ) := this
      _ = S / ρ := by ring
  have hsA : |sA| ≤ S / ρ := hsX _
  have hsB : |sB| ≤ S / ρ := hsX _
  have hsD : |sD| ≤ S / ρ := hsX _
  have hE1 : 0 ≤ 1 + (C - 1) * rampF a₃ ρ y := by nlinarith
  have hE2 : 1 + (C - 1) * rampF a₃ ρ y ≤ C := by nlinarith
  set v := vF c m y
  set v' := c * (m ^ 2 - (y - 1) ^ 2) / ((y - 1) ^ 2 + m ^ 2) ^ 2
  have e1 : |C * sA * (1 - rampF a₂ ρ y)| ≤ C * (S / ρ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ C), abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - rampF a₂ ρ y)]
    have := mul_le_mul hsA (by linarith : 1 - rampF a₂ ρ y ≤ 1) (by linarith) (by positivity)
    nlinarith
  have e2 : |C * rampF a₁ ρ y * -sB| ≤ C * (S / ρ) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ C), abs_of_nonneg hA0]
    have := mul_le_mul hA1 hsB (abs_nonneg _) (by norm_num)
    nlinarith
  have e3 : |(v' * rampF a₂ ρ y + v * sB) * (1 + (C - 1) * rampF a₃ ρ y)|
      ≤ (c / m ^ 2 + c / (2 * m) * (S / ρ)) * C := by
    rw [abs_mul, abs_of_nonneg hE1]
    have h1 : |v' * rampF a₂ ρ y + v * sB| ≤ c / m ^ 2 + c / (2 * m) * (S / ρ) := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hB0]
      have h2 := mul_le_mul hv' hB1 hB0 (by positivity)
      have h3 := mul_le_mul hv hsB (abs_nonneg _) (by positivity)
      linarith
    exact mul_le_mul h1 hE2 hE1 (by positivity)
  have e4 : |v * rampF a₂ ρ y * ((C - 1) * sD)| ≤ c / (2 * m) * C * (S / ρ) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg (by linarith : (0:ℝ) ≤ C - 1)]
    have h1 : |v| * rampF a₂ ρ y ≤ c / (2 * m) := by
      have := mul_le_mul_of_nonneg_left hB1 (abs_nonneg v); linarith
    have h2 : (C - 1) * |sD| ≤ C * (S / ρ) := by
      have := mul_le_mul (by linarith : C - 1 ≤ C) hsD (abs_nonneg _) (by linarith)
      linarith
    have := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith
  have htot := le_trans (abs_add_le _ _) (add_le_add (le_trans (abs_add_le _ _) (add_le_add e1 e2))
    (le_trans (abs_add_le _ _) (add_le_add e3 e4)))
  refine le_trans htot (le_of_eq ?_)
  field_simp
  ring

/-- **The derivative bound for `FF`.** -/
theorem FF_deriv_abs_le {g : ℝ → ℝ} (hgd : Differentiable ℝ g) (hg' : ∀ y, |deriv g y| ≤ 2)
    {ĝ : ℝ} (hg0 : ∀ y, 0 ≤ g y) (hgle : ∀ y, g y ≤ ĝ)
    {L C c m ρ a₁ a₂ a₃ S : ℝ} (hC : 1 ≤ C) (hc : 0 ≤ c) (hm : 0 < m) (hρ : 0 < ρ)
    (hS : ∀ x, |deriv Real.smoothTransition x| ≤ S) (y : ℝ) :
    |deriv (FF g L C c m ρ a₁ a₂ a₃) y|
      ≤ (2 + 2 * S) * (C + C * (c / (2 * m)))
        + (ĝ + 2) * (2 * C * S / ρ + C * (c / m ^ 2) + 2 * C * (c / (2 * m)) * S / ρ) := by
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  have h1 := (st_hasDerivAt (y - L)).comp y ((hasDerivAt_id' y).sub_const L)
  have hE := (hgd y).hasDerivAt.add ((h1.const_sub 1).const_mul 2)
  have hWd' : HasDerivAt (WF C c m ρ a₁ a₂ a₃) (deriv (WF C c m ρ a₁ a₂ a₃) y) y :=
    (((WF_contDiff (C := C) (c := c) (ρ := ρ) (a₁ := a₁) (a₂ := a₂) (a₃ := a₃) hm).differentiable
      one_ne_zero) y).hasDerivAt
  have hFd : HasDerivAt (FF g L C c m ρ a₁ a₂ a₃)
      ((deriv g y + 2 * -(deriv Real.smoothTransition (y - L) * 1)) * WF C c m ρ a₁ a₂ a₃ y
        + (g y + 2 * (1 - Real.smoothTransition (y - L))) * deriv (WF C c m ρ a₁ a₂ a₃) y) y :=
    hE.mul hWd'
  rw [hFd.deriv]
  have hWa := WF_abs_le (ρ := ρ) (a₁ := a₁) (a₂ := a₂) (a₃ := a₃) hC hc hm y
  have hWd := WF_deriv_abs_le (a₁ := a₁) (a₂ := a₂) (a₃ := a₃) hC hc hm hρ hS y
  have hG' : |deriv g y + 2 * -(deriv Real.smoothTransition (y - L) * 1)| ≤ 2 + 2 * S := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_neg, mul_one, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have := hS (y - L)
    linarith [hg' y]
  have hG : |g y + 2 * (1 - Real.smoothTransition (y - L))| ≤ ĝ + 2 := by
    have h0 := Real.smoothTransition.nonneg (y - L)
    have h1 := Real.smoothTransition.le_one (y - L)
    rw [abs_of_nonneg (by linarith [hg0 y])]
    linarith [hgle y]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul]
  have hW0 : 0 ≤ C + C * (c / (2 * m)) := by positivity
  exact add_le_add (mul_le_mul hG' hWa (abs_nonneg _) (by positivity))
    (mul_le_mul hG hWd (abs_nonneg _) (by linarith [hg0 y, hgle y]))

end F1c
end ShellK
end ZetaShell
