/-
L10c_K2Aux (L7_10c, 3 Oct 2026): the pieces of the K2 assembly that are not analysis:
* `exists_alpha2`: Theorem S is applied at some `α″ ∈ (α′, 5/3)` with `θ₁ < thetaD1p α″` (continuity of `thetaD1p`);
* `scalars_K2`: the eventual scalar facts in `y = log Q`;
* the bridges between AS's objects (`TrackF.famF`, `famSize`, `l2S`, `LcS`, `XlamS`, `twin`) and Theorem K's
  (`FfamZ`, `Family.qle.sizeR`, `normA2`, `P.LL`, `P.XQ`, `P.T`) on a Shell design.
-/
import ZetaShell.ShellK.L10c_K2Point
import ZetaShell.LemmaK.LK_K8d_Bridge

noncomputable section
open MeasureTheory Filter

namespace ZetaShell
namespace ShellK
namespace K2c

open ZetaQ ZetaShell.PropZ

theorem thetaD1p_continuousAt (αp : ℝ) (hα1 : 1 < αp) : ContinuousAt ShellS.thetaD1p αp := by
  have h0 : αp ≠ 0 := by linarith
  have hden : (4 - 4 / αp) ≠ 0 := by
    have : 4 / αp < 4 := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  show ContinuousAt (fun x => min 1 ((2 - (4 - 4 / x)) / (4 - 4 / x))) αp
  have hg : ContinuousAt (fun x : ℝ => (2 - (4 - 4 / x)) / (4 - 4 / x)) αp := by
    have h1 : ContinuousAt (fun x : ℝ => 2 - (4 - 4 / x)) αp :=
      continuousAt_const.sub (continuousAt_const.sub (continuousAt_const.div continuousAt_id h0))
    have h2 : ContinuousAt (fun x : ℝ => 4 - 4 / x) αp :=
      continuousAt_const.sub (continuousAt_const.div continuousAt_id h0)
    exact h1.div h2 hden
  exact Filter.Tendsto.min tendsto_const_nhds hg

theorem exists_alpha2 (αp θ₁ : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (hθ : θ₁ < ShellS.thetaD1p αp) :
    ∃ α₂ : ℝ, αp < α₂ ∧ α₂ < 5 / 3 ∧ θ₁ < ShellS.thetaD1p α₂ := by
  have hev : ∀ᶠ x in nhds αp, θ₁ < ShellS.thetaD1p x :=
    (thetaD1p_continuousAt αp hα1).eventually (lt_mem_nhds hθ)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hd : 0 < (5 / 3 - αp) / 2 := by linarith
  refine ⟨αp + min (δ / 2) ((5 / 3 - αp) / 2), ?_, ?_, hball ?_⟩
  · have : 0 < min (δ / 2) ((5 / 3 - αp) / 2) := lt_min (by linarith) hd
    linarith
  · have := min_le_right (δ / 2) ((5 / 3 - αp) / 2)
    linarith
  · have h1 : 0 < min (δ / 2) ((5 / 3 - αp) / 2) := lt_min (by linarith) hd
    have h2 := min_le_left (δ / 2) ((5 / 3 - αp) / 2)
    rw [Real.dist_eq, show αp + min (δ / 2) ((5 / 3 - αp) / 2) - αp = min (δ / 2) ((5 / 3 - αp) / 2) by ring,
      abs_of_pos h1]
    linarith

/-- the eventual scalar facts of K2. -/
theorem scalars_K2 (αp α₂ r ε CA θ₁ : ℝ) (hα1 : 1 < αp) (hαα : αp < α₂) (hre : 0 < r + ε) (hθ1 : θ₁ < 1)
    (hCA : 0 ≤ CA) :
    ∀ᶠ Qn : ℕ in atTop, (16 ≤ Real.log Qn ∧ 5 ≤ (αp - 1) * Real.log Qn ∧
      αp * (r + ε) * Real.log (Real.log Qn) + 1 ≤ (α₂ - αp) * Real.log Qn) ∧
      3 * Real.log (2 * Real.log Qn) + CA + 2 ≤ Real.log Qn ^ (1 - θ₁) / 2 ∧
      Real.log (2 * Real.log Qn) ≤ Real.log Qn ^ (1 - θ₁) ∧
      CA * Real.log (2 * Real.log Qn) ≤ Real.log Qn ∧
      2 * Real.log (2 * Real.log Qn) ^ 2 ≤ Real.log Qn ∧
      6 * (1 + Real.log Qn) ^ 2 ≤ (18 / Real.pi ^ 4 - 1 / 6) * Qn := by
  have hβ : 0 < 1 - θ₁ := by linarith
  have hpi4 : 0 < 18 / Real.pi ^ 4 - 1 / 6 := by
    have h1 : Real.pi ^ 4 < 3.15 ^ 4 := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
    have h2 : 0 < Real.pi ^ 4 := by positivity
    rw [sub_pos, lt_div_iff₀ h2]; nlinarith
  -- facts in `y`
  have hy : ∀ᶠ y : ℝ in atTop,
      3 * Real.log (2 * y) + CA + 2 ≤ y ^ (1 - θ₁) / 2 ∧ Real.log (2 * y) ≤ y ^ (1 - θ₁) ∧
      CA * Real.log (2 * y) ≤ y ∧ 2 * Real.log (2 * y) ^ 2 ≤ y := by
    have hlo := (isLittleO_log_rpow_atTop hβ).def (by norm_num : (0 : ℝ) < 1 / 12)
    have hpow : Tendsto (fun y : ℝ => y ^ (1 - θ₁)) atTop atTop := tendsto_rpow_atTop hβ
    have hsq := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (by norm_num : (0 : ℝ) < 1 / 8)
    have hK : 0 < 2 * CA + 1 := by linarith
    filter_upwards [hlo, hpow.eventually_ge_atTop (4 * (3 * Real.log 2 + CA + 2)),
      FrobAssembly.loglog_le_eventually _ hK, hsq, eventually_ge_atTop (2 : ℝ),
      eventually_ge_atTop (2 * CA * Real.log 2 + 1)] with y h1 h2 h3 h4 h5 h6
    have hy0 : 0 < y := by linarith
    have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
    have hly : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) h5
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpos : 0 ≤ y ^ (1 - θ₁) := Real.rpow_nonneg hy0.le _
    have hlog0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have h1' : Real.log y ≤ 1 / 12 * y ^ (1 - θ₁) := by
      have e1 : ‖Real.log y‖ = Real.log y := by rw [Real.norm_eq_abs, abs_of_nonneg hlog0]
      have e2 : ‖y ^ (1 - θ₁)‖ = y ^ (1 - θ₁) := by rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      rw [e1, e2] at h1; exact h1
    have h4' : Real.log y ^ 2 ≤ 1 / 8 * y := by
      have e1 : ‖Real.log y ^ 2‖ = Real.log y ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 2)]
      have e2 : ‖id y‖ = y := by rw [id, Real.norm_eq_abs, abs_of_nonneg hy0.le]
      rw [e1, e2] at h4; exact h4
    have hA : 3 * Real.log (2 * y) + CA + 2 ≤ y ^ (1 - θ₁) / 2 := by rw [hlog2y]; linarith [h1']
    refine ⟨hA, ?_, ?_, ?_⟩
    · have : 0 ≤ Real.log (2 * y) := by rw [hlog2y]; linarith
      linarith
    · rw [hlog2y]
      have e1 : CA * Real.log y ≤ (2 * CA + 1) * Real.log y := by nlinarith
      nlinarith
    · rw [hlog2y]
      have e : (Real.log 2 + Real.log y) ^ 2 ≤ 4 * Real.log y ^ 2 := by nlinarith
      linarith [h4']
  have hQ : ∀ᶠ x : ℝ in atTop, 6 * (1 + Real.log x) ^ 2 ≤ (18 / Real.pi ^ 4 - 1 / 6) * x := by
    have hsq := (Real.isLittleO_pow_log_id_atTop (n := 2)).def
      (by positivity : (0 : ℝ) < (18 / Real.pi ^ 4 - 1 / 6) / 24)
    filter_upwards [hsq, eventually_ge_atTop (Real.exp 1)] with x h1 h2
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) h2
    have hl1 : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact h2
    have h1' : Real.log x ^ 2 ≤ (18 / Real.pi ^ 4 - 1 / 6) / 24 * x := by
      have e1 : ‖Real.log x ^ 2‖ = Real.log x ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) 2)]
      have e2 : ‖id x‖ = x := by rw [id, Real.norm_eq_abs, abs_of_nonneg hx0.le]
      rw [e1, e2] at h1; exact h1
    have e : (1 + Real.log x) ^ 2 ≤ 4 * Real.log x ^ 2 := by nlinarith
    have : 6 * (4 * Real.log x ^ 2) ≤ (18 / Real.pi ^ 4 - 1 / 6) * x := by
      have := mul_le_mul_of_nonneg_left h1' (by norm_num : (0 : ℝ) ≤ 24)
      have e2 : 24 * ((18 / Real.pi ^ 4 - 1 / 6) / 24 * x) = (18 / Real.pi ^ 4 - 1 / 6) * x := by ring
      linarith
    linarith
  filter_upwards [scalars_KT αp α₂ r ε hα1 hαα hre, tendsto_log_nat_atTop.eventually hy,
    tendsto_natCast_atTop_atTop.eventually hQ] with Qn h1 h2 h3
  exact ⟨h1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, h3⟩

/-! ### Bridges on a Shell design -/

theorem LcS_eq (P : ParamsQ) (Qn : ℕ) (T : ℝ) (hQ : P.Q = Qn) (hT : P.T = T) :
    ShellS.LcS Qn T = P.LL := by
  unfold ShellS.LcS ParamsQ.LL; rw [hQ, hT]

theorem bridge_F (P : ParamsQ) (Qn : ℕ) (T : ℝ) (hQ : P.Q = Qn) (hT : P.T = T) (hlam : P.lam = 191 / 100)
    (s : ℝ) :
    TrackF.famF (Finset.Icc 2 Qn) ⌊ShellS.XlamS (191 / 100) Qn T⌋₊ (TrackF.acoefS T s) = FfamZ P Qn s := by
  have hX : ShellS.XlamS (191 / 100) (Qn : ℝ) T = LemmaK.Xlam P.lam P.Q P.T := by
    rw [hlam, hQ, hT]; rfl
  unfold TrackF.famF FfamZ familySum
  rw [hX, ← hT]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
  have h := LemmaK.charSum_eq_AchiC P χ s
  show ‖ZetaQ.charSum q ⌊LemmaK.Xlam P.lam P.Q P.T⌋₊ (LemmaK.acoef P.T s) χ‖ ^ 2 = ‖Achi P χ s‖ ^ 2
  rw [h]; rfl

theorem bridge_size (Qn : ℕ) : ShellS.famSize Qn = Family.qle.sizeR Qn := by
  unfold ShellS.famSize Family.sizeR Family.size
  push_cast
  rfl

theorem bridge_l2 (P : ParamsQ) (Qn : ℕ) (T : ℝ) (hQ : P.Q = Qn) (hT : P.T = T) (hlam : P.lam = 191 / 100)
    (s : ℝ) : ShellS.l2S ⌊ShellS.XlamS (191 / 100) Qn T⌋₊ T s = normA2 P s := by
  have hX : ShellS.XlamS (191 / 100) (Qn : ℝ) T = LemmaK.Xlam P.lam P.Q P.T := by
    rw [hlam, hQ, hT]; rfl
  rw [hX, ← hT, ← LemmaK.l2sq_eq_normA2]
  rfl

end K2c
end ShellK
end ZetaShell
