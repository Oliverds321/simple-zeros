/-
L7_5 (28 Sep 2026), round 3: the scaling identity of Step 3 of prop:shell-Z (first half of `Z5Z_expand`):
  Ṽ_{x,s}(ρ) = N^{ρ−1/2} I_ρ(x/N; ΔN),   N = e^s,
from `y = Nt`, `log(Nt) = s + log t`, `(Nt)^{−1/2} = N^{−1/2}t^{−1/2}`, `t^{ρ−1}t^{−1/2} = t^{ρ−3/2}`.
-/
import ZetaShell.PropZ.ZZ0_Defs

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem mellin_VxsW_scaling (T κ : ℝ) (Ξ f : ℝ → ℝ) (Δ s x : ℝ) (ρ : ℂ) :
    mellin (VxsW T κ Ξ f Δ s x) ρ
      = ((Real.exp s : ℝ) : ℂ) ^ (ρ - 1 / 2) * Irho T κ Ξ f 0 ρ (Δ * Real.exp s) (x / Real.exp s) := by
  set N := Real.exp s with hNdef
  have hN : 0 < N := Real.exp_pos s
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  -- mellin V ρ = N^ρ • mellin (V ∘ (N ·)) ρ
  have hsc := mellin_comp_mul_left (VxsW T κ Ξ f Δ s x) ρ hN
  have hV : mellin (VxsW T κ Ξ f Δ s x) ρ = (N : ℂ) ^ ρ * mellin (fun t => VxsW T κ Ξ f Δ s x (N * t)) ρ := by
    rw [hsc, smul_eq_mul, ← mul_assoc, ← Complex.cpow_add _ _ hNc]
    simp
  rw [hV]
  -- the rescaled Mellin transform
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), (t : ℂ) ^ (ρ - 1) • VxsW T κ Ξ f Δ s x (N * t)
      = ((N ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Hrho T κ Ξ ρ t * ((fj f 0 (Δ * N * (t - x / N)) : ℝ) : ℂ)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hlog : Real.log (N * t) = s + Real.log t := by
      rw [Real.log_mul hN.ne' ht0.ne', hNdef, Real.log_exp]
    have hrp : (N * t) ^ (-(1 / 2 : ℝ)) = N ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) :=
      Real.mul_rpow hN.le ht0.le
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hcp : ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (t : ℂ) ^ (ρ - 1) = (t : ℂ) ^ (ρ - 3 / 2) := by
      rw [Complex.ofReal_cpow ht0.le, ← Complex.cpow_add _ _ htc]
      congr 1; push_cast; ring
    have hf : Δ * (N * t - x) = Δ * N * (t - x / N) := by field_simp
    simp only [VxsW, As, Hrho, fj, smul_eq_mul, hlog, hrp, hf]
    rw [show s - (s + Real.log t) = -Real.log t by ring, show (s + Real.log t - s) / κ = Real.log t / κ by ring]
    rw [← hcp]
    push_cast
    ring
  have hint : mellin (fun t => VxsW T κ Ξ f Δ s x (N * t)) ρ
      = ((N ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Irho T κ Ξ f 0 ρ (Δ * N) (x / N) := by
    rw [mellin, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
    rfl
  rw [hint, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_cpow hN.le, ← Complex.cpow_add _ _ hNc]
  congr 1; push_cast; ring

end ZetaShell.PropZ
