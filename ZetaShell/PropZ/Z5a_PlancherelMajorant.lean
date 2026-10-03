/-
Node Z5a (L7_5, 28 Sep 2026): Lemma 5a, Plancherel majorant (sec_shell.tex, lem:shell-5a):
"Let ν be a finite compactly supported complex measure on (0,∞), S(β) = ∫ e(yβ) dν(y), and Δ > 0. Then
 ∫_{|β|≤Δ} |S|² ≤ ∫_ℝ |S(β)|² Φ(β/Δ) dβ = (Δ²/c_f) ∫_ℝ |∫ f(Δ(y−x)) dν(y)|² dx."
Formalised for ν = (finitely many point masses `a y` at `y ∈ F`) + (a continuous compactly supported density `g`),
which is the only shape Proposition Z uses (Step 1: `Σ Λχ(n)A_s(n)δ_n − δ_{r=1} A_s(y)dy`). The support condition
"ν on (0,∞)" is not needed. `c` is any `0 < c ≤ min_{[-1,1]} f̂²` (the draft's `c_f` is the largest such).
-/
import ZetaShell.PropZ.ZDefs
import ZetaShell.PropZ.Z5a_Plancherel

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- **Z5a, majorant half** (`Φ ≥ 1` on `[-1,1]`, `Φ ≥ 0`), for any continuous `S`. -/
theorem majorant_half (f : ℝ → ℝ) (c : ℝ) (hc0 : 0 < c)
    (hc : ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2) (S : ℝ → ℂ) (hS : Continuous S)
    (Δ : ℝ) (hΔ : 0 < Δ) (hint : Integrable (fun β => ‖S β‖ ^ 2 * Phi f c (β / Δ))) :
    ∫ β in Set.Icc (-Δ) Δ, ‖S β‖ ^ 2 ≤ ∫ β, ‖S β‖ ^ 2 * Phi f c (β / Δ) := by
  have hPhi : ∀ η, 0 ≤ Phi f c η := fun η => div_nonneg (sq_nonneg _) hc0.le
  have h1 : ∫ β in Set.Icc (-Δ) Δ, ‖S β‖ ^ 2
      ≤ ∫ β in Set.Icc (-Δ) Δ, ‖S β‖ ^ 2 * Phi f c (β / Δ) := by
    refine setIntegral_mono_on ((hS.norm.pow 2).integrableOn_Icc) hint.integrableOn measurableSet_Icc ?_
    intro β hβ
    have hmem : β / Δ ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ hΔ]; linarith [hβ.1]
      · rw [div_le_one hΔ]; exact hβ.2
    have h1Phi : 1 ≤ Phi f c (β / Δ) := by
      rw [Phi, le_div_iff₀ hc0, one_mul]; exact hc _ hmem
    have := sq_nonneg ‖S β‖
    nlinarith
  exact h1.trans (setIntegral_le_integral hint (Filter.Eventually.of_forall fun β =>
    mul_nonneg (sq_nonneg _) (hPhi _)))

/-- **Z5a, Plancherel half** (`Ĝ(β) = Δ⁻¹ f̂(β/Δ) S(−β)`, then Plancherel for the Schwartz function `G`). -/
theorem plancherel_identity (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c)
    (F : Finset ℝ) (a : ℝ → ℂ) (g : ℝ → ℂ) (hg : Continuous g) (hgs : HasCompactSupport g)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∫ β, ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2 * Phi f c (β / Δ)
      = Δ ^ 2 / c * ∫ x, ‖∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)‖ ^ 2 :=
  plancherel_identity' f hf c hc0 F a g hg hgs Δ hΔ

theorem continuous_S (F : Finset ℝ) (a : ℝ → ℂ) (g : ℝ → ℂ) (hg : Continuous g) (hgs : HasCompactSupport g) :
    Continuous (fun β : ℝ => ∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)) := by
  have hcA : ∀ y : ℝ, Continuous (fun β : ℝ => eA (y * β)) := fun y => by unfold eA; fun_prop
  refine (continuous_finsetSum _ fun y _ => continuous_const.mul (hcA y)).add ?_
  refine continuous_of_dominated (bound := fun y => ‖g y‖) (fun β => ?_) (fun β => ?_)
    (hg.integrable_of_hasCompactSupport hgs).norm (Filter.Eventually.of_forall fun y => ?_)
  · exact (hg.mul (by unfold eA; fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by rw [norm_mul, norm_eA, mul_one]
  · exact continuous_const.mul (hcA y)

/-- **Z5a** (lem:shell-5a), both halves, with integrability of the majorant. -/
theorem plancherel_majorant (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c)
    (hc : ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2)
    (F : Finset ℝ) (a : ℝ → ℂ) (g : ℝ → ℂ) (hg : Continuous g) (hgs : HasCompactSupport g)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    Integrable (fun β => ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2 * Phi f c (β / Δ)) ∧
    (∫ β in Set.Icc (-Δ) Δ, ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2)
      ≤ ∫ β, ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2 * Phi f c (β / Δ) ∧
    ∫ β, ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2 * Phi f c (β / Δ)
      = Δ ^ 2 / c * ∫ x, ‖∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)‖ ^ 2 :=
  ⟨plancherel_integrable f hf c hc0 F a g hg hgs Δ hΔ,
    majorant_half f c hc0 hc _ (continuous_S F a g hg hgs) Δ hΔ (plancherel_integrable f hf c hc0 F a g hg hgs Δ hΔ),
    plancherel_identity' f hf c hc0 F a g hg hgs Δ hΔ⟩

end ZetaShell.PropZ
