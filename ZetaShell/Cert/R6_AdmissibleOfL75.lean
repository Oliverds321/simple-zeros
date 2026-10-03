/-
Node R6 (L7_1): an L75 profile gives an admissible `v_p = p²/∫p²` on `[−λ/2, λ/2]` (paper §11's class: `v ≥ 0`,
integrable, `∫v = 1`, support). Dependencies: none new. Difficulty: E–M (`mass > 0` from `p > 0`; the full-line
integral of the restricted `v` is the interval integral).
-/
import ZetaShell.Interfaces

namespace ZetaShell

theorem p_continuous (S : ShellProfile) : Continuous S.p := by
  unfold ShellProfile.p
  fun_prop

theorem mass_pos_of_L75 (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) (h : S.L75) : 0 < S.mass := by
  unfold ShellProfile.mass
  have hc : Continuous (fun t => S.p t ^ 2) := (p_continuous S).pow 2
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) ?_ (by linarith)
  intro x hx
  have hx' : |x| ≤ (S.lam : ℝ) / 2 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  exact pow_pos (h.pos x hx') 2

theorem v_eq_indicator (S : ShellProfile) :
    S.v = Set.indicator (Set.Icc (-((S.lam : ℝ) / 2)) ((S.lam : ℝ) / 2)) (fun t => S.p t ^ 2 / S.mass) := by
  funext t
  simp only [ShellProfile.v, Set.indicator, Set.mem_Icc, abs_le]

theorem admissible_of_L75 (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) (h : S.L75) :
    AdmissibleS S.lam S.v := by
  have hm := mass_pos_of_L75 S hl h
  have hc : Continuous (fun t => S.p t ^ 2 / S.mass) := ((p_continuous S).pow 2).div_const _
  refine ⟨fun t => ?_, ?_, ?_, fun t ht => ?_⟩
  · unfold ShellProfile.v
    split_ifs
    · exact div_nonneg (sq_nonneg _) hm.le
    · exact le_refl _
  · rw [v_eq_indicator]
    exact (hc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  · rw [v_eq_indicator, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_div]
    exact div_self hm.ne'
  · by_contra hne
    apply ht
    unfold ShellProfile.v
    rw [if_neg hne]

end ZetaShell
