/-
lean_work/L2_1/PhiMHelpers.lean — helpers on `Φ_m` (lem:zeta-Phi) for nodes L3, L3b (L2_1, 28 Sep 2026).
Namespace `ZetaS`, public.

  * `PhiM_eq`          : for `m ≥ 2`, `Φ_m(E) = E − ((√((m−1)E/m) − 1)₊)²` (both branches in one formula).
  * `sq_posPart_sub_le`: `((v−1)₊)² − ((u−1)₊)² ≤ v² − u²` for `0 ≤ u ≤ v`.
-/
import ZetaS.Interfaces

namespace ZetaS

lemma PhiM_eq {m : ℕ} (hm : 2 ≤ m) (E : ℝ) :
    PhiM m E = E - (max (Real.sqrt (((m : ℝ) - 1) * E / m) - 1) 0) ^ 2 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  unfold PhiM
  split_ifs with h
  · have h1 : E * ((m : ℝ) - 1) ≤ m := (le_div_iff₀ hm1).mp h
    have h2 : ((m : ℝ) - 1) * E / m ≤ 1 := by
      rw [div_le_one hm0]; linarith
    have h3 : Real.sqrt (((m : ℝ) - 1) * E / m) ≤ 1 :=
      (Real.sqrt_le_sqrt h2).trans_eq Real.sqrt_one
    rw [max_eq_right (by linarith)]; ring
  · rw [not_le] at h
    have h1 : (m : ℝ) < E * ((m : ℝ) - 1) := (div_lt_iff₀ hm1).mp h
    have h2 : 1 < ((m : ℝ) - 1) * E / m := by
      rw [lt_div_iff₀ hm0]; linarith
    have h3 : 1 < Real.sqrt (((m : ℝ) - 1) * E / m) := by
      have := Real.sqrt_lt_sqrt (x := 1) (by norm_num) h2
      rwa [Real.sqrt_one] at this
    rw [max_eq_left (by linarith)]

lemma sq_posPart_sub_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (max (v - 1) 0) ^ 2 - (max (u - 1) 0) ^ 2 ≤ v ^ 2 - u ^ 2 := by
  rcases le_total u 1 with hu1 | hu1 <;> rcases le_total v 1 with hv1 | hv1
  · rw [max_eq_right (by linarith : u - 1 ≤ 0), max_eq_right (by linarith : v - 1 ≤ 0)]; nlinarith
  · rw [max_eq_right (by linarith : u - 1 ≤ 0), max_eq_left (by linarith : 0 ≤ v - 1)]; nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ u - 1), max_eq_right (by linarith : v - 1 ≤ 0)]; nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ u - 1), max_eq_left (by linarith : 0 ≤ v - 1)]; nlinarith

end ZetaS
