/-
Node K6a (track K) — the last step of thm:zeta-G (l.501: "let c′ ↑ c; the right-hand side is continuous in c"):
c ↦ stabConst H K ν c m is continuous at c₀ > 0 when 2 ≤ K ≤ m and Φ_m(A) < m (Φ_m is continuous: both branches
agree at E = m/(m−1)).
-/
import ZetaS.Interfaces

open Filter Topology

namespace ZetaS

namespace K6aux

/-- `Φ_m(E) = E − ((√((m−1)E/m) − 1)₊)²` for every `E` (m ≥ 2): the two branches of `PhiM` in one continuous formula. -/
lemma PhiM_eq_max {m : ℕ} (hm : 2 ≤ m) (E : ℝ) :
    PhiM m E = E - (max (Real.sqrt (((m : ℝ) - 1) * E / m) - 1) 0) ^ 2 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  unfold PhiM
  split_ifs with h
  · have hx : ((m : ℝ) - 1) * E / m ≤ 1 := by
      rw [div_le_one hm0]; rw [le_div_iff₀ hm1] at h; linarith
    rw [max_eq_right (by linarith [Real.sqrt_le_one.mpr hx])]; ring
  · push_neg at h
    have hx : 1 < ((m : ℝ) - 1) * E / m := by
      rw [lt_div_iff₀ hm0]; rw [div_lt_iff₀ hm1] at h; linarith
    have hs : 1 < Real.sqrt (((m : ℝ) - 1) * E / m) := by rw [Real.lt_sqrt (by norm_num)]; linarith
    rw [max_eq_left (by linarith)]

lemma PhiM_continuous {m : ℕ} (hm : 2 ≤ m) : Continuous (PhiM m) := by
  have : PhiM m = fun E => E - (max (Real.sqrt (((m : ℝ) - 1) * E / m) - 1) 0) ^ 2 :=
    funext (PhiM_eq_max hm)
  rw [this]; fun_prop

end K6aux

open K6aux in

theorem stabConst_continuousAt {H ν c₀ : ℝ} {K m : ℕ} (hK : 2 ≤ K) (hKm : K ≤ m) (hc₀ : 0 < c₀)
    (hBm : PhiM m (c₀ * ((m : ℝ) - K + 1)) < m) :
    ContinuousAt (fun c => stabConst H K ν c m) c₀ := by
  have hm : 2 ≤ m := le_trans hK hKm
  have hKmR : (K : ℝ) ≤ m := by exact_mod_cast hKm
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hPc := PhiM_continuous hm
  have hA : ContinuousAt (fun c : ℝ => c * ((m : ℝ) - K + 1)) c₀ := by fun_prop
  have hB : ContinuousAt (fun c : ℝ => PhiM m (c * ((m : ℝ) - K + 1))) c₀ :=
    hPc.continuousAt.comp hA
  have hA0 : c₀ * ((m : ℝ) - K + 1) ≠ 0 := (mul_pos hc₀ (by linarith)).ne'
  have hden : 1 - PhiM m (c₀ * ((m : ℝ) - K + 1)) / m ≠ 0 := by
    have : PhiM m (c₀ * ((m : ℝ) - K + 1)) / m < 1 := by rw [div_lt_one hm0]; exact hBm
    linarith
  show ContinuousAt (fun c => (H - PhiM m (c * ((m : ℝ) - K + 1)) / (c * ((m : ℝ) - K + 1))
      * (ν * ((m : ℝ) - K + 1) / m)) / (1 - PhiM m (c * ((m : ℝ) - K + 1)) / m)) c₀
  exact ((continuousAt_const.sub ((hB.div hA hA0).mul continuousAt_const)).div
    (continuousAt_const.sub (hB.div continuousAt_const hm0.ne')) hden)

end ZetaS
