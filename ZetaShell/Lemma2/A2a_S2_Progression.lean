/-
A2a_S2_Progression (L7_8, 28 Sep 2026): the counting core of **Step 2 of the proof of Lemma 2(a)**
(sec_shell.tex l.323–331): "for each `g` the admissible `k` form one class modulo `lcm(g, f_(r))`, or the empty set,
and the `q` run through one progression. A function of variation `≤ V*` summed over a progression differs from the
scaled integral by `≤ V*`."

Proved here (sorry-free), for the indicator weights of the sharp and dyadic families (`w = 1_I`, so `N_j(e, f)` is a
lattice-point count): the number of integers `x ∈ (a, b]` in one residue class mod `r ≥ 1` differs from `(b − a)/r` by
at most `1` (`progression_count`), from Mathlib's `Int.Ioc_filter_modEq_card`.
Remark on the draft: for a general `w` of bounded variation the per-class discrepancy is `≤ Var(w·1_{I_j}) ≤
Var(w) + 2‖w‖_∞` (restricting `w(qe/Q)` to the interval `I_j` adds up to two jumps), i.e. `≤ 2V*`, not `≤ V*`;
constant only.
-/
import Mathlib

noncomputable section

namespace ZetaShell
namespace TrackF

/-- **Step 2, one residue class.** `|#{x ∈ (a, b] : x ≡ v (mod r)} − (b − a)/r| ≤ 1` for `r ≥ 1`, `a ≤ b`. -/
theorem progression_count (a b v r : ℤ) (hr : 0 < r) (hab : a ≤ b) :
    |((((Finset.Ioc a b).filter (fun x => x ≡ v [ZMOD r])).card : ℤ) : ℚ) - ((b : ℚ) - a) / r| ≤ 1 := by
  rw [Int.Ioc_filter_modEq_card a b hr v]
  set y : ℚ := ((b : ℚ) - v) / r with hy
  set x : ℚ := ((a : ℚ) - v) / r with hx
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hyx : y - x = ((b : ℚ) - a) / r := by rw [hy, hx]; field_simp; ring
  have hyx0 : 0 ≤ y - x := by
    rw [hyx]; apply div_nonneg _ hrQ.le
    have : (a : ℚ) ≤ b := by exact_mod_cast hab
    linarith
  have f1 := Int.floor_le y
  have f2 := Int.lt_floor_add_one y
  have f3 := Int.floor_le x
  have f4 := Int.lt_floor_add_one x
  rw [← hyx]
  rcases le_total (⌊y⌋ - ⌊x⌋) 0 with h | h
  · rw [max_eq_right h]
    have h' : ((⌊y⌋ : ℚ) - ⌊x⌋) ≤ 0 := by exact_mod_cast h
    push_cast
    rw [abs_le]
    constructor <;> linarith
  · rw [max_eq_left h]
    push_cast
    rw [abs_le]
    constructor <;> linarith

end TrackF
end ZetaShell
