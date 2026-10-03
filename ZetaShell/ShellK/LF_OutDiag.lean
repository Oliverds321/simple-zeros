/-
F1c-3 (L7_3, round 6): **the weighted diagonal evaluation of Theorem K's right side**, `shell_outDiag`, DERIVED from
* F1c-3a `smear_upper` (PROVED, generic): the weighted smearing. For a measurable weight `0 ≤ h ≤ H` and any `h⁺`
  dominating `h` on unit balls (`|s − y| < 1 → h s ≤ h⁺ y`),
    `∫ h·‖a‖² ≤ (1/4π²) Σ_{n≤X} (Λ(n)²/n)·(2πT·h⁺(log n) + 8H)`
  (`normA2_eq`, `∫|D_T|² = 2πT` (`DT_sq_integral`), `∫_{|v|≥1}|D_T|² ≤ 8` (`DT_tail_mass`)). This is
  `lemma43_diagonal`'s smearing for a weight with jumps, upper bound only.
* F1c-3b `shell_mertens` (OPEN): the Abel/Mertens step for the bounded-variation weight
  `h⁺ = hsupP` (the unit-ball supremum of `g·wOut`, `wOut = shellWt` off the in-zone, `0` on it), with the kernel
  identity `g(αℒ) = (aL)²ℒ⁻¹ψ_{v_d}(α)` and `|𝔉|(T/2π)ℒ ≤ (1+δ)𝒩`:
    `2|𝔉|·(1/4π²) Σ_{n≤X}(Λ(n)²/n)(2πT·hsupP(log n) + 8H_P) ≤ (aL)²(KoutShell(a) + η)𝒩`.
Also PROVED here: `outShell_eq` (the out-zone integral as a whole-line integral of `g·wOut·‖a‖²`), the bounds
`0 ≤ g·wOut ≤ H_P = aL·(C + ℒ)`, its measurability, and the domination by `hsupP` (`le_csSup`).
-/
import ZetaShell.ShellK.LF_InZone

noncomputable section
open scoped BigOperators
open scoped ArithmeticFunction
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

/-- **F1c-3a.** The weighted smearing, upper bound. -/
theorem smear_upper (P : ParamsQ) (hT : 0 ≤ P.T) (h hp : ℝ → ℝ) (H : ℝ) (hm : Measurable h)
    (h0 : ∀ s, 0 ≤ h s) (hH : ∀ s, h s ≤ H) (hdom : ∀ s y, |s - y| < 1 → h s ≤ hp y) :
    (∫ s, h s * normA2 P s)
      ≤ 1 / (4 * Real.pi ^ 2) * ∑ n ∈ primeRangeQ P,
          (Λ n : ℝ) ^ 2 / (n : ℝ) * (2 * Real.pi * P.T * hp (Real.log (n : ℝ)) + 8 * H) := by
  set K : ℝ → ℝ := fun v => ‖P.DT v‖ ^ 2 with hKdef
  have hKint : Integrable K := DT_normSq_integrable P hT
  have hKc : Continuous K := DT_normSq_continuous P hT
  have hK0 : ∀ v, 0 ≤ K v := fun v => sq_nonneg _
  have hH0 : 0 ≤ H := le_trans (h0 0) (hH 0)
  -- one term: `∫ h(s) K(s − y) ds ≤ 2πT·hp(y) + 8H`
  have hterm : ∀ y : ℝ, Integrable (fun s => h s * K (s - y)) ∧
      (∫ s, h s * K (s - y)) ≤ 2 * Real.pi * P.T * hp y + 8 * H := by
    intro y
    have hKy : Integrable (fun s => K (s - y)) := hKint.comp_sub_right y
    have hint : Integrable (fun s => h s * K (s - y)) := by
      refine Integrable.bdd_mul (c := H) hKy hm.aestronglyMeasurable (ae_of_all _ (fun s => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 s)]
      exact hH s
    refine ⟨hint, ?_⟩
    have hsub : (∫ s, h s * K (s - y)) = ∫ v, h (y + v) * K v := by
      have := (integral_add_left_eq_self (μ := (volume : Measure ℝ)) (fun s => h s * K (s - y)) y).symm
      rw [this]
      congr 1
      ext v
      simp
    rw [hsub]
    have hp0 : 0 ≤ hp y := le_trans (h0 y) (hdom y y (by simp))
    set S : Set ℝ := {v : ℝ | 1 ≤ |v|} with hSdef
    have hSm : MeasurableSet S := measurableSet_le measurable_const continuous_abs.measurable
    have hpt : ∀ v, h (y + v) * K v ≤ hp y * K v + H * S.indicator K v := by
      intro v
      by_cases hv : 1 ≤ |v|
      · have h1 : S.indicator K v = K v := Set.indicator_of_mem (show v ∈ S from hv) K
        rw [h1]
        have := mul_le_mul_of_nonneg_right (hH (y + v)) (hK0 v)
        have := mul_nonneg hp0 (hK0 v)
        linarith
      · have h1 : S.indicator K v = 0 := Set.indicator_of_notMem (show v ∉ S from hv) K
        rw [h1, mul_zero, add_zero]
        have hlt : |(y + v) - y| < 1 := by simp only [add_sub_cancel_left]; exact lt_of_not_ge hv
        exact mul_le_mul_of_nonneg_right (hdom (y + v) y hlt) (hK0 v)
    have hint2 : Integrable (fun v => h (y + v) * K v) := by
      refine Integrable.bdd_mul (c := H) hKint (hm.comp (measurable_const_add y)).aestronglyMeasurable
        (ae_of_all _ (fun v => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
      exact hH _
    have hint3 : Integrable (fun v => hp y * K v + H * S.indicator K v) :=
      (hKint.const_mul _).add ((hKint.indicator hSm).const_mul _)
    calc (∫ v, h (y + v) * K v) ≤ ∫ v, (hp y * K v + H * S.indicator K v) := integral_mono hint2 hint3 hpt
      _ = hp y * (∫ v, K v) + H * (∫ v in S, K v) := by
          rw [integral_add (hKint.const_mul _) ((hKint.indicator hSm).const_mul _), integral_const_mul,
            integral_const_mul, integral_indicator hSm]
      _ ≤ hp y * (2 * Real.pi * P.T) + H * 8 := by
          have e1 : (∫ v, K v) = 2 * Real.pi * P.T := DT_sq_integral P hT
          have e2 : (∫ v in S, K v) ≤ 8 / 1 := DT_tail_mass P (y := 1) one_pos
          rw [e1]
          have := mul_le_mul_of_nonneg_left e2 hH0
          linarith
      _ = 2 * Real.pi * P.T * hp y + 8 * H := by ring
  -- sum over `n`
  have hexp : (fun s => h s * normA2 P s)
      = fun s => 1 / (4 * Real.pi ^ 2) * ∑ n ∈ primeRangeQ P,
          (Λ n : ℝ) ^ 2 / (n : ℝ) * (h s * K (s - Real.log (n : ℝ))) := by
    funext s
    rw [normA2_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hKdef]
    ring
  have hswap : (∫ a, ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * (h a * K (a - Real.log (n : ℝ))))
      = ∑ n ∈ primeRangeQ P, ∫ a, (Λ n : ℝ) ^ 2 / (n : ℝ) * (h a * K (a - Real.log (n : ℝ))) :=
    integral_finset_sum _ (fun n _ => (hterm (Real.log (n : ℝ))).1.const_mul _)
  rw [hexp, integral_const_mul, hswap]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro n _
  rw [integral_const_mul]
  have hc : 0 ≤ (Λ n : ℝ) ^ 2 / (n : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left (hterm (Real.log (n : ℝ))).2 hc

/-- the out-zone weight: Theorem K's `shellWt` off the in-zone, `0` on it. -/
def wOut (P : ParamsQ) (s : ℝ) : ℝ := if |s| ≤ P.s0 then 0 else shellWt P (2497 / 1500) s

/-- the bound `H_P = aL·(C + ℒ)` of `g·wOut`. -/
def HP (P : ParamsQ) : ℝ := P.aQ * P.LB * (Cfam + P.LL)

/-- the unit-ball supremum of `g·wOut`. -/
def hsupP (P : ParamsQ) (y : ℝ) : ℝ := sSup ((fun s => P.gQ s * wOut P s) '' Metric.ball y 1)

theorem wOut_nonneg_le {P : ParamsQ} (hP : P.Valid) (s : ℝ) : 0 ≤ wOut P s ∧ wOut P s ≤ Cfam + P.LL := by
  have hC0 : 0 < Cfam := by unfold Cfam; positivity
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hlogQ : 1 ≤ Real.log P.Q + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ P.Q by linarith)
    linarith
  unfold wOut shellWt
  split_ifs with h1 h2 h3
  · exact ⟨le_rfl, by linarith⟩
  · exact ⟨hC0.le, by linarith⟩
  · have hs : Real.log P.Q + 4 < s := lt_of_not_ge h2
    have hs0 : 0 < s := by linarith
    refine ⟨div_nonneg hLL0.le hs0.le, ?_⟩
    have : P.LL / s ≤ P.LL := by
      rw [div_le_iff₀ hs0]; nlinarith
    linarith
  · have hs : Real.log P.Q + 4 < s := lt_of_not_ge h2
    have hs0 : 0 < s := by linarith
    have hs2 : 2497 / 1500 * P.LL < s := lt_of_not_ge h3
    refine ⟨div_nonneg (mul_nonneg hC0.le hLL0.le) hs0.le, ?_⟩
    have : Cfam * P.LL / s ≤ Cfam := by
      rw [div_le_iff₀ hs0]; nlinarith
    linarith

theorem wOut_measurable (P : ParamsQ) : Measurable (wOut P) := by
  unfold wOut shellWt
  refine Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · exact measurable_const.div measurable_id
  · exact measurable_const.div measurable_id

theorem outShell_eq (P : ParamsQ) :
    outShell P = ∫ s, (P.gQ s * wOut P s) * normA2 P s := by
  unfold outShell
  rw [← integral_indicator (measurableSet_inZone P).compl]
  congr 1
  funext s
  by_cases hs : s ∈ (inZone P)ᶜ
  · rw [Set.indicator_of_mem hs]
    have hs' : ¬ |s| ≤ P.s0 := hs
    simp only [wOut, hs', if_false]
    ring
  · rw [Set.indicator_of_notMem hs]
    have hs' : |s| ≤ P.s0 := not_not.mp hs
    simp [wOut, hs']

end F1c
end ShellK
end ZetaShell
