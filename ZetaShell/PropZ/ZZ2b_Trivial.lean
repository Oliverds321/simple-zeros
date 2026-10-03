/-
L7_5 (28 Sep 2026), round 6: split of `ZO_trivial` (Step 4, regime `D ≤ μ+1`) into
  * `ZO_young` (PROVED in round 7 via `ZO_young'`, ZZ2d_Young.lean): Young's inequality for `I_ρ(ξ) = ∫_{t>0} H_ρ(t) f_j(μ(t−ξ)) dt`:
      `μ² ∫|I_ρ|² ≤ (∫_{t>0} |H_ρ|²) (∫|f_j|)²`   (pointwise Cauchy–Schwarz with weight `|f_j(μ(t−ξ))|`, then Tonelli);
  * `ZO_H_L2` (PROVED in round 7 via `ZO_H_L2'`, ZZ2c_HL2.lean): `∫_{t>0} |H_ρ|² ≤ C T` for `ρ` in the strip (`t = e^{−v}`, `|t^{ρ−3/2}| ≤ e^{3κ}` on the
      support, and `∫_{−κ}^{κ} |D_T|² ≤ 2πT`, or `|D_T(v)| ≤ min(T, 2/|v|)`);
and the derivation `ZO_trivial'` (PROVED), with `C = C_H Σ_{j ≤ A} (∫|f_j|)²`.
-/
import ZetaShell.PropZ.ZZ0_Defs
import ZetaShell.PropZ.ZZ2c_HL2
import ZetaShell.PropZ.ZZ2d_Young

open MeasureTheory

namespace ZetaShell.PropZ

theorem ZO_young (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T : ℝ) (j : ℕ) (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (μ : ℝ) (hμ : 0 < μ) :
    μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2)
      ≤ (∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖ ^ 2) * (∫ z, |fj f j z|) ^ 2 :=
  ZO_young' κ hκ Ξ hΞ f hf T j ρ hρ0 hρ1 μ hμ

theorem ZO_H_L2 (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 →
      (∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖ ^ 2) ≤ C * T :=
  ZO_H_L2' κ hκ hκ1 Ξ hΞ

theorem ZO_trivial' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (μ : ℝ), 0 < μ → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 → ∀ j ≤ A,
      μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ C * T := by
  obtain ⟨CH, hCH, hH⟩ := ZO_H_L2 κ hκ hκ1 Ξ hΞ
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i ∈ Finset.range (A + 1), (∫ z, |fj f i z|) ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨CH * S, mul_nonneg hCH hS0, fun T hT μ hμ ρ hρ0 hρ1 j hj => ?_⟩
  have hjS : (∫ z, |fj f j z|) ^ 2 ≤ S := by
    rw [hS]
    exact Finset.single_le_sum (f := fun i => (∫ z, |fj f i z|) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have hHT := hH T hT ρ hρ0 hρ1
  have hCT : 0 ≤ CH * T := mul_nonneg hCH (by linarith)
  calc μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2)
      ≤ (∫ t in Set.Ioi (0 : ℝ), ‖Hrho T κ Ξ ρ t‖ ^ 2) * (∫ z, |fj f j z|) ^ 2 :=
        ZO_young κ hκ Ξ hΞ f hf T j ρ hρ0 hρ1 μ hμ
    _ ≤ (CH * T) * S := mul_le_mul hHT hjS (sq_nonneg _) hCT
    _ = CH * S * T := by ring

end ZetaShell.PropZ
