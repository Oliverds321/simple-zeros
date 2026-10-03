/-
Node KT (L7_10): **the transfer from unit windows to `g`** (proof of thm:shell-K, "Transfer from unit windows to
`g`": "Write `1 = Σ_j W₀(s−j)` and put `W_j := W₀(·−j)g`. […] `‖g^{(A)}‖_∞ ≪ 1`, while `g(αℒ) ≍ ℒ(v⋆v)(α) > 0` for
`|α| ≤ α′ < λ`. Hence `‖W_j‖_{C^A} ≪ g(j)` and `∫W_j‖a‖² ≍ g(j)Ts₀` uniformly in `j`").
Abstract form: for ANY nonnegative continuous `R` whose unit-window averages obey Theorem S's bound
`∫W(s−s₀)R(s)ds ≤ η‖W‖_{C^A} T s₀` for all admissible `W` and all `log Q + 3 ≤ s₀ ≤ α″ log Q`, the `g`-average over
the Shell zone obeys `∫_{zone} gR ≤ Cη ∫_{zone} g T s`. Here `α′ < α″ < 2` and the design is S53-L75 (`λ = 1.91 > α″`).
It is used with `R(s) = Ring(s; R₁(s))` (`R1S (s−1)`), which is below the window's `Ring(s; R1S s₀)` for
`s ≤ s₀ + 1` by `ringMass_mono` and `R1S_mono` (proved).
Dependencies: ZetaQ `Window` (derivative bounds of `g`, `Valid.gQ_nonneg`), the lower bound `g(s) ≫ ℒ` on
`|s| ≤ α″ℒ` (from `p ≥ 1/6` and the ramp), a smooth partition of unity. Difficulty: M.

PROVED (L7_10c, 3 Oct 2026; statement unchanged, moved from `Skeleton/`): `K2c.KT_point` with the single window
`W₀ = K2c.bumpW` (`= 1` on `[−1/2, 1/2]`) at the centres `log Q + 4 + k`, `C = 279936·‖W₀‖_{C^A}`; no derivative of
`g` is needed (`g ≤ L` and `g ≥ (L − 2 − α′ℒ)/1296` on the zone). Note: the K2 derivation does not use this node,
since `RingS … (s − 1) s` is not continuous in `s`; it uses the same window domination with `Theorem S`'s own
integrability (`K2c.K2_point`).
-/
import ZetaShell.ShellK.L10c_KT

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ MeasureTheory ZetaShell.PropZ

theorem KT_transfer (αp αpp : ℝ) (hα1 : 1 < αp) (hαα : αp < αpp) (hαpp : αpp < 5 / 3) (r ε : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (A : ℕ) (hA : 2 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∀ (R : ℝ → ℝ) (η : ℝ), 0 ≤ η → (∀ s, 0 ≤ R s) → Continuous R →
        (∀ W : ℝ → ℝ, AvgWeight W → ∀ s₀ : ℝ, Real.log Qn + 3 ≤ s₀ → s₀ ≤ αpp * Real.log Qn →
            (∫ s, W (s - s₀) * R s) ≤ η * normCA W A * (P.T * s₀)) →
        (∫ s in shellZone P αp, P.gQ s * R s) ≤ C * η * ∫ s in shellZone P αp, P.gQ s * (P.T * s) := by
  have hre : 0 < r + ε := by linarith
  refine ⟨279936 * normCA K2c.bumpW A, mul_nonneg (by norm_num) (ShellS.normCA_nonneg' _ _), ?_⟩
  filter_upwards [K2c.design_facts r ε hr hε, K2c.scalars_KT αp αpp r ε hα1 hαα hre] with Qn hfac hsc
  intro P hdes R η hη hR0 hRc hW
  obtain ⟨hP, hw8, hw1, hQ, hT, -, hLB, hyLL, hLL2, hLLu, hy1⟩ := hfac P hdes
  obtain ⟨h16, h5, hll⟩ := hsc
  have hlogQ : Real.log P.Q = Real.log Qn := by rw [hQ]
  have hTpos : 0 < P.T := by rw [hT]; exact Real.rpow_pos_of_pos (by linarith) _
  have hLL16 : 16 ≤ P.LL := by linarith
  have hα53 : αp < 5 / 3 := by linarith
  have hloglog : 0 ≤ Real.log (Real.log Qn) := Real.log_nonneg (by linarith)
  refine K2c.KT_point P hP hw8 hw1 αp A hTpos ?_ ?_ ?_ ?_ ?_ R η hη hR0 hRc ?_
  · rw [hlogQ]; nlinarith
  · rw [hLB]; nlinarith
  · nlinarith
  · rw [hLB]; nlinarith
  · rw [hlogQ]; linarith
  · intro s₀ h1 h2
    refine hW K2c.bumpW K2c.bumpW_avg s₀ (by rw [hlogQ] at h1; linarith) ?_
    have : αp * P.LL ≤ αp * (Real.log Qn + (r + ε) * Real.log (Real.log Qn)) :=
      mul_le_mul_of_nonneg_left hLLu (by linarith)
    nlinarith

end ShellK
end ZetaShell
