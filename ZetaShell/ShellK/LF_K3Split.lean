/-
K3 split (L7_3, round 8; K3b PROVED by L7_3c, round 10, 3 Oct). `K3_killed` (L7_10's statement, verbatim, as
`K3_killed_of_split`) is DERIVED from
* K3a `killed_pointwise_shell` (PROVED, level A, `LF_K3a.lean`): K7 at `λ = 191/100` in ZetaQ's objects,
  `F(s) ≤ sieveBudgetQ·‖a‖² − Q²·savWeight C₁ + errWeight` for every `s`;
* K3b `K3b_integrated` (PROVED, round 10): the integrated comparison on `S = inZoneᶜ ∩ (α′ℒ, ∞)`, together with the
  integrability of its left side:
    `∫_S g·(sieveBudgetQ‖a‖² − Q²·savWeight C₁ + errWeight) ≤ (1 + c(log Q)^{−θ})|𝔉_Q| ∫_S g‖a‖²·Cℒ/s`
  for every fixed `C₁`, with `c = 1`. Pure analysis on `‖a‖²`, with no characters.
  Proof (`LF_K3bM.K3b_main`, at `θ′ = max(θ, 1/2)`, then monotonicity in `θ`): `S = (α′ℒ, ∞)` (`s₀ ≤ α′ℒ`);
  pointwise `g(B‖a‖² − Q²sav + err) ≤ Q²g((1 + δ₁)‖a‖² + ℒ) − Q²g·sav` (AM–GM, `R₀ ≤ 𝒳/Q`); `∫_S g‖a‖²` from
  above by the whole line (`smear_upper` + Abel with the jump-free weight `g + 2(1 − st(y − L))`, relative error
  `O(1/ℒ)`) minus the pointwise PNT lower bound `‖a(s)‖² ≥ (T/2π)(s − 1)` (`normA2_lower`, `√(log Q) ≤ s ≤ L − 1`)
  on `(√(log Q), α′ℒ]`; `∫_S g·sav` and the right side from below by the same pointwise bound; `∫_S g ≥ ℒ²/3240000`
  (`gQ_ge_bulk`); `Q² ≤ C|𝔉_Q|(1 + O(log³Q/Q))` (`sizeR_qle_lower'`); `𝒳 ≤ Q^{2−9/200}`; `ℓ_K = ℒ + log(2πℒ)`;
  then the real-number lemma `final_arith_K3b`.
-/
import ZetaShell.ShellK.LF_K3bM

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaShell.LemmaK

/-- **K3b (PROVED, L7_3c round 10).** The integrated killed comparison beyond `α′ℒ`, with integrability. -/
theorem K3b_integrated (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : θ < 1) (C₁ : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      IntegrableOn
          (fun s => P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
          ((inZone P)ᶜ ∩ Set.Ioi (αp * P.LL)) ∧
        (∫ s in (inZone P)ᶜ ∩ Set.Ioi (αp * P.LL),
            P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
          ≤ (1 + c * Real.log Qn ^ (-θ)) * Family.qle.sizeR Qn
              * ∫ s in (inZone P)ᶜ ∩ Set.Ioi (αp * P.LL), P.gQ s * (normA2 P s * shellWt P αp s) := by
  refine ⟨1, zero_le_one, ?_⟩
  have hθ' : max θ (1 / 2) < 1 := max_lt hθ (by norm_num)
  have hθ'0 : 0 < max θ (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  filter_upwards [K3b_main αp hα1 hα2 r ε (max θ (1 / 2)) hr hε hθ'0 hθ' C₁] with Qn h
  intro P hdes
  obtain ⟨hI, -, hle, hs0, ha0, hy1⟩ := h P hdes
  rw [outZone_inter_Ioi P hs0 ha0]
  refine ⟨hI, le_trans hle ?_⟩
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hLL0 : 0 < P.LL := hdes.1.LL_pos
  have hC0 : 0 < Cfam := by unfold Cfam; positivity
  have hsR0 : 0 ≤ Family.qle.sizeR Qn := by unfold Family.sizeR; positivity
  have hB0 : 0 ≤ ∫ s in Set.Ioi (αp * P.LL), P.gQ s * (normA2 P s * shellWt P αp s) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro s hs
    have hs' : αp * P.LL < s := hs
    have hspos : 0 < s := lt_of_le_of_lt ha0 hs'
    have hsw : 0 ≤ shellWt P αp s := by
      unfold shellWt
      split_ifs
      · exact hC0.le
      · exact div_nonneg hLL0.le hspos.le
      · exact div_nonneg (mul_nonneg hC0.le hLL0.le) hspos.le
    exact mul_nonneg (hdes.1.gQ_nonneg hw s) (mul_nonneg (normA2_nonneg P s) hsw)
  have hpow : Real.log Qn ^ (-max θ (1 / 2)) ≤ 1 * Real.log Qn ^ (-θ) := by
    rw [one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hy1 (neg_le_neg (le_max_left _ _))
  have h1 : 1 + Real.log Qn ^ (-max θ (1 / 2)) ≤ 1 + 1 * Real.log Qn ^ (-θ) := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hsR0) hB0

/-- **K3, derived** (L7_10's `K3_killed` statement, verbatim) from K3a (proved) and K3b. -/
theorem K3_killed_of_split (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : θ < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (∫ s in (inZone P)ᶜ ∩ Set.Ioi (αp * P.LL), P.gQ s * FfamZ P Qn s)
        ≤ (1 + c * Real.log Qn ^ (-θ)) * Family.qle.sizeR Qn
            * ∫ s in (inZone P)ᶜ ∩ Set.Ioi (αp * P.LL), P.gQ s * (normA2 P s * shellWt P αp s) := by
  obtain ⟨C₁, hK3a⟩ := killed_pointwise_shell r ε hr hε
  obtain ⟨c, hc0, hK3b⟩ := K3b_integrated αp hα1 hα2 r ε θ hr hε hθ C₁
  refine ⟨c, hc0, ?_⟩
  filter_upwards [hK3a, hK3b] with Qn ha hb
  intro P hdes
  obtain ⟨hInt, hle⟩ := hb P hdes
  refine le_trans ?_ hle
  have hP : P.Valid := hdes.1
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hF0 : ∀ s, 0 ≤ FfamZ P Qn s := fun s => by
    show 0 ≤ ∑ q ∈ Finset.Icc 2 Qn, ∑ χ ∈ ZetaQ.primitiveChars q, ‖Achi P χ s‖ ^ 2
    exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun χ _ => sq_nonneg _
  apply integral_mono_of_nonneg
  · exact ae_of_all _ fun s => mul_nonneg (hP.gQ_nonneg hw s) (hF0 s)
  · exact hInt
  · exact ae_of_all _ fun s => mul_le_mul_of_nonneg_left (ha P hdes s) (hP.gQ_nonneg hw s)

end F1c
end ShellK
end ZetaShell
