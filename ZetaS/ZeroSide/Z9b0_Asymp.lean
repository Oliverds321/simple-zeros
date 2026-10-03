/-
Sub-node Z9b0 (agent L3_1) — two generic asymptotic facts for the tail transfer Z9b: √N = o(N) when N → ∞, and
|‖G − E‖²_F − ‖G‖²_F| ≤ 2‖G‖_F + 1 when ‖E‖²_F ≤ 1.
-/
import Zeta23.Assembly

noncomputable section

open Filter Asymptotics Topology RHLinalg

namespace ZetaS
namespace Z9

open Zeta23

/-- `√N = o(N)` when `N → ∞`. -/
lemma sqrt_isLittleO {N : ℝ → ℝ} (hN : Tendsto N atTop atTop) :
    (fun T => Real.sqrt (N T)) =o[atTop] N := by
  refine IsLittleO.of_bound fun ε hε => ?_
  filter_upwards [hN.eventually_ge_atTop (1 / ε ^ 2), hN.eventually_ge_atTop 0] with T h h0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h0]
  have hs := Real.sqrt_nonneg (N T)
  have hsq := Real.mul_self_sqrt h0
  have h2 : 1 / ε ≤ Real.sqrt (N T) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / ε)]
    exact Real.sqrt_le_sqrt (by rw [div_pow, one_pow]; exact h)
  have h1 : 1 ≤ ε * Real.sqrt (N T) := by
    rw [div_le_iff₀ hε] at h2; linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hs]

/-- `|‖G − E‖² − ‖G‖²| ≤ 2‖G‖ + 1` (Frobenius) when `‖E‖²_F ≤ 1`. -/
lemma frobSq_close {n : Type*} [Fintype n] (G E : Matrix n n ℂ) (hE : frobSq E ≤ 1) :
    |frobSq (G - E) - frobSq G| ≤ 2 * Real.sqrt (frobSq G) + 1 := by
  have h1 := Assembly.frobSq_sub_le G E
  have h2 := Assembly.frobSq_sub_le (G - E) (-E)
  rw [sub_neg_eq_add, sub_add_cancel] at h2
  have hnE : frobSq (-E) = frobSq E := by simp [Assembly.frobSq_eq_sum_norm_sq]
  rw [hnE] at h2
  have hsE : Real.sqrt (frobSq E) ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hE
  set a := Real.sqrt (frobSq (G - E)) with hadef
  set g := Real.sqrt (frobSq G) with hgdef
  set e := Real.sqrt (frobSq E) with hedef
  have ha : frobSq (G - E) = a ^ 2 := (Real.sq_sqrt (Assembly.frobSq_nonneg _)).symm
  have hg : frobSq G = g ^ 2 := (Real.sq_sqrt (Assembly.frobSq_nonneg _)).symm
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have hag : a ≤ g + e := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ g + e)]; exact Real.sqrt_le_sqrt h1
  have hga : g ≤ a + e := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ a + e)]; exact Real.sqrt_le_sqrt h2
  rw [ha, hg, abs_le]
  have hu : a - g ≤ 1 := by linarith
  have hl : g - a ≤ 1 := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hl (add_nonneg ha0 hg0)]
  · nlinarith [mul_le_mul_of_nonneg_right hu (add_nonneg ha0 hg0)]

end Z9
end ZetaS
