/-
Node SD-C3 (L7_7, constants; consumed by F1c's ends row): **Lemma 8.1's constant at λ = 1.91 by the Minkowski
split** (L7_4 correction 4, D4): `c₁ ≥ 3/(√2π³) + λ√(1 + X/Q²)/(√2π)`, and `c₁ = 0.52` suffices while `X/Q² ≤ 1/10`
(L7_4: `≤ 0.103419`). Replaces `c1Ends = 0.41` (`Defs.lean:394`), the λ* value of the `(a+b)² ≤ 2a²+2b²` route
(`Ends.lean:1299`), which at 1.91 gives 0.6156. Sanity: LHS = 0.519298 at `x = 1/10`, 0.498317 at `x = 0`.
Deps: none. Difficulty E.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

theorem c1Ends_shell_minkowski (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 10) :
    3 / (Real.sqrt 2 * Real.pi ^ 3) + (191 / 100) * Real.sqrt (1 + x) / (Real.sqrt 2 * Real.pi)
      ≤ c1EndsShell := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hs2 : (1.4142 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs1 : Real.sqrt (1 + x) ≤ 1.0489 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hpi3 : (3.1415 : ℝ) ^ 3 ≤ Real.pi ^ 3 := by
    apply pow_le_pow_left₀ (by norm_num) hpi.le
  have hd1 : (1.4142 : ℝ) * 3.1415 ^ 3 ≤ Real.sqrt 2 * Real.pi ^ 3 :=
    mul_le_mul hs2 hpi3 (by norm_num) (by positivity)
  have hd2 : (1.4142 : ℝ) * 3.1415 ≤ Real.sqrt 2 * Real.pi :=
    mul_le_mul hs2 hpi.le (by norm_num) (by positivity)
  have ht1 : 3 / (Real.sqrt 2 * Real.pi ^ 3) ≤ 3 / ((1.4142 : ℝ) * 3.1415 ^ 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd1
  have hnum : (191 / 100 : ℝ) * Real.sqrt (1 + x) ≤ 191 / 100 * 1.0489 := by
    nlinarith [Real.sqrt_nonneg (1 + x)]
  have ht2 : (191 / 100) * Real.sqrt (1 + x) / (Real.sqrt 2 * Real.pi)
      ≤ (191 / 100 * 1.0489) / ((1.4142 : ℝ) * 3.1415) := by
    calc (191 / 100) * Real.sqrt (1 + x) / (Real.sqrt 2 * Real.pi)
        ≤ (191 / 100 * 1.0489) / (Real.sqrt 2 * Real.pi) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (191 / 100 * 1.0489) / ((1.4142 : ℝ) * 3.1415) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd2
  unfold c1EndsShell
  have hfin : 3 / ((1.4142 : ℝ) * 3.1415 ^ 3) + (191 / 100 * 1.0489) / ((1.4142 : ℝ) * 3.1415)
      ≤ 0.52 := by norm_num
  linarith

end ZetaShell.Design
