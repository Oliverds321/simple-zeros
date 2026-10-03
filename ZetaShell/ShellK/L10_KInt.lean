/-
Node KInt (L7_10's statement, VERBATIM; proof by L7_3, round 7). Drop-in for `lean_work/L7_10/L10_KInt.lean`: same
module name, namespace and statement; only the proof is new.

Original docstring (L7_10): **integrability and signs for Theorem K** (implicit in the draft): on a Shell design, `g F`
and `g ‖a‖² k̃/|α|` are integrable on the out-zone, `g ≥ 0`, `‖a‖²·weight ≥ 0` there, and `log Q ≥ 0`.

PROOF (L7_3). `g·F`: `F` is a finite sum of `|A_χ|²` (continuous, `Achi_continuous`), and `g·(continuous)` is
integrable (`gQ_mul_integrable`). `g·(‖a‖²·shellWt)`: `g‖a‖²` is integrable and `shellWt` is measurable and bounded by
`C + ℒ + Cℒ` (`s > log Q + 4 ≥ 1` on its last two branches), so `Integrable.bdd_mul`. Signs: `Valid.gQ_nonneg`,
`normA2 ≥ 0`, `shellWt ≥ 0` (its last two branches have `s > log Q + 4 > 0`). Only `P.Valid` and `8w ≤ L` are used.
-/
import ZetaShell.ShellK.L10_KDefs

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ MeasureTheory

theorem K_int (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      IntegrableOn (fun s => P.gQ s * FfamZ P Qn s) (inZone P)ᶜ ∧
      IntegrableOn (fun s => P.gQ s * (normA2 P s * shellWt P αp s)) (inZone P)ᶜ ∧
      (∀ s, 0 ≤ P.gQ s) ∧ (∀ s ∈ (inZone P)ᶜ, 0 ≤ normA2 P s * shellWt P αp s) ∧ 0 ≤ Real.log (Qn : ℝ) := by
  refine Filter.Eventually.of_forall fun Qn P hdes => ?_
  have hP : P.Valid := hdes.1
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hT : (0 : ℝ) ≤ P.T := hP.T_pos.le
  have hLL := hP.LL_pos
  have hC0 : (0 : ℝ) < Cfam := by unfold Cfam; positivity
  have hQ1 : (1 : ℝ) ≤ P.Q := by linarith [hP.Q_ge]
  have hlogQ : 0 ≤ Real.log P.Q := Real.log_nonneg hQ1
  have hαp0 : 0 < αp := by linarith
  -- `shellWt` is nonnegative and bounded
  have hW : ∀ s, 0 ≤ shellWt P αp s ∧ shellWt P αp s ≤ Cfam + P.LL + Cfam * P.LL := by
    intro s
    unfold shellWt
    split_ifs with h1 h2
    · exact ⟨hC0.le, by linarith [mul_nonneg hC0.le hLL.le]⟩
    · have hs : Real.log P.Q + 4 < s := lt_of_not_ge h1
      have hs1 : 1 ≤ s := by linarith
      have hs0 : 0 < s := by linarith
      refine ⟨div_nonneg hLL.le hs0.le, ?_⟩
      have : P.LL / s ≤ P.LL := by
        rw [div_le_iff₀ hs0]
        have := mul_le_mul_of_nonneg_left hs1 hLL.le
        linarith
      linarith [mul_nonneg hC0.le hLL.le]
    · have hs : Real.log P.Q + 4 < s := lt_of_not_ge h1
      have hs1 : 1 ≤ s := by linarith
      have hs0 : 0 < s := by linarith
      refine ⟨div_nonneg (mul_nonneg hC0.le hLL.le) hs0.le, ?_⟩
      have : Cfam * P.LL / s ≤ Cfam * P.LL := by
        rw [div_le_iff₀ hs0]
        have := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hC0.le hLL.le)
        linarith
      linarith
  have hWm : Measurable (shellWt P αp) := by
    unfold shellWt
    refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
    refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
    · exact measurable_const.div measurable_id
    · exact measurable_const.div measurable_id
  have hnA : ∀ s, 0 ≤ normA2 P s := fun s => Finset.sum_nonneg fun n _ => by positivity
  refine ⟨?_, ?_, fun s => hP.gQ_nonneg hw s, fun s _ => mul_nonneg (hnA s) (hW s).1,
    Real.log_natCast_nonneg Qn⟩
  · -- `g·F`
    have hFc : Continuous (FfamZ P Qn) := by
      unfold FfamZ familySum
      exact continuous_finset_sum _ fun q _ => continuous_finset_sum _ fun χ _ =>
        (InZone.Achi_continuous P χ).norm.pow 2
    exact (gQ_mul_integrable P hP hw hFc).integrableOn
  · -- `g·(‖a‖²·shellWt)`
    have hgn : Integrable (fun s => P.gQ s * normA2 P s) :=
      gQ_mul_integrable P hP hw (normA2_continuous P hT)
    have hb : Integrable (fun s => shellWt P αp s * (P.gQ s * normA2 P s)) :=
      Integrable.bdd_mul (c := Cfam + P.LL + Cfam * P.LL) hgn hWm.aestronglyMeasurable
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hW s).1]; exact (hW s).2)
    refine (hb.congr (ae_of_all _ fun s => ?_)).integrableOn
    ring
