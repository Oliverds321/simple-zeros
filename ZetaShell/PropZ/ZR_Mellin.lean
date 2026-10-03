/-
L7_5 (28 Sep 2026), round 4: Mellin bounds for `V_{x,s}`, uniform in `x`, from the shared decay estimate
(`MellinDecay`, proved) and the shared leaf `ZR_phi_bounds`:
  `‖Ṽ_{x,s}(w)‖ ≤ C T N^{Re w − 1/2} m/N`  and, for `w ≠ 0`, `‖Ṽ_{x,s}(w)‖ ≤ ‖w‖^{−2} C X² T N^{Re w − 1/2} m/N`.
-/
import ZetaShell.PropZ.MellinDecay
import ZetaShell.PropZ.ZR_Leaves
import ZetaShell.PropZ.ZB_As

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem VxsW_tsupport_Ioi (T κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ)
    (Δ s₀ s x : ℝ) (hs₀ : 3 ≤ s₀) (hs : |s - s₀| ≤ 1) : tsupport (VxsW T κ Ξ f Δ s x) ⊆ Set.Ioi 1 := by
  refine (VxsW_tsupport T κ hκ Ξ hΞ f Δ s x).trans ?_
  have hs1 : 0 < s - κ := by have := (abs_le.mp hs).1; linarith
  intro y hy
  have := Real.add_one_lt_exp (ne_of_gt hs1)
  exact lt_of_lt_of_le (by linarith) hy.1

theorem VxsW_hasCompactSupport (T κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (Δ s x : ℝ) :
    HasCompactSupport (VxsW T κ Ξ f Δ s x) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (VxsW_tsupport T κ hκ Ξ hΞ f Δ s x)

theorem mellin_Vxs_bounds (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (x : ℝ) (w : ℂ), 0 ≤ w.re → w.re ≤ 1 →
      ‖mellin (VxsW T κ Ξ f Δ s x) w‖
          ≤ C * T * Real.exp s ^ (w.re - 1 / 2) * min (1 / Δ) (Real.exp s) / Real.exp s ∧
      (w ≠ 0 → ‖mellin (VxsW T κ Ξ f Δ s x) w‖
          ≤ (1 / ‖w‖ ^ 2) * (C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp s ^ (w.re - 1 / 2)
            * min (1 / Δ) (Real.exp s) / Real.exp s)) := by
  obtain ⟨C, hC0, hC⟩ := ZR_phi_bounds κ hκ hκ1 Ξ hΞ f hf
  refine ⟨C, hC0, fun s₀ T Δ s hs₀ hT hΔ hΔ1 hs x w hw0 hw1 => ?_⟩
  have hsupp := VxsW_tsupport_Ioi T κ hκ hκ1 Ξ hΞ f Δ s₀ s x hs₀ hs
  obtain ⟨h1, h2⟩ := hC s₀ T Δ s hs₀ hT hΔ hΔ1 hs x w.re hw0 hw1
  refine ⟨(norm_mellin_le_trivial _ hsupp w).trans h1, fun hw => ?_⟩
  refine (norm_mellin_le_ibp2 _ (VxsW_contDiff T κ hκ Ξ hΞ f hf Δ s x)
    (VxsW_hasCompactSupport T κ hκ Ξ hΞ f Δ s x) hsupp w hw).trans ?_
  gcongr

end ZetaShell.PropZ
