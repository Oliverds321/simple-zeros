/-
Node K1 (L7_10's statement, VERBATIM; proof by L7_3, round 7). Drop-in for `lean_work/L7_10/L10_K1_Strip.lean`: same
module name, namespace and statement; only the imports and the proof are new.

Original docstring (L7_10, abridged): **Theorem K on the strip** — pointwise, for `s` in the out-zone with
`s ≤ log Q + 4` (this includes every `s < −s₀`): `F(s) ≤ (1 + c(log Q)^{−θ})·|𝔉_Q|·‖a(s)‖²·C`, `C = π⁴/18`.

PROOF (L7_3). `F(s) ≤ famSum ≤ (Q² + π𝒳)‖a(s)‖²` (the tree's pointwise large sieve `lemma43_sieve_half_A`,
`familySum_le_famSum`); `Q² ≤ C|𝔉_Q| + 6CQ(1 + log Q)²` (`sizeR_qle_lower'`); `π𝒳 ≤ πQ²Q^{−9/200}` (A7) with
`Q^{9/200} ≥ 4π log Q` and `48C(log Q)³ ≤ Q` eventually (`Real.isLittleO_log_rpow_atTop`,
`Real.isLittleO_pow_log_id_atTop`). Hence `Q² + π𝒳 ≤ C|𝔉_Q|(1 + 2/log Q) ≤ C|𝔉_Q|(1 + 2(log Q)^{−θ})` for `θ < 1`:
`c = 2`. Numerical check of the family-size step: `py/k1_test.py → .out` (`Q²/(C|𝔉_Q|) − 1 = 6·10⁻⁶` at `Q = 10⁵`).
-/
import ZetaShell.ShellK.L10_KDefs
import ZetaShell.Design.SD_A7_Regime

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ

theorem K1_strip (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hθ : θ < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∀ s ∈ (inZone P)ᶜ, s ≤ Real.log P.Q + 4 →
        FfamZ P Qn s ≤ (1 + c * Real.log Qn ^ (-θ)) * Family.qle.sizeR Qn * (normA2 P s * shellWt P αp s) := by
  refine ⟨2, by norm_num, ?_⟩
  have hpi := Real.pi_pos
  have hC0 : (0 : ℝ) < Cfam := by unfold Cfam; positivity
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  -- the two growth facts, in the real variable
  have hE1 : ∀ᶠ y : ℝ in Filter.atTop, Real.log y ^ 3 ≤ 1 / (48 * Cfam) * y := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 3)).def (show (0 : ℝ) < 1 / (48 * Cfam) by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have h0 : 0 ≤ Real.log y := Real.log_nonneg hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), id, abs_of_nonneg (by linarith)] at hy
    exact hy
  have hE2 : ∀ᶠ y : ℝ in Filter.atTop, Real.log y ≤ 1 / (4 * Real.pi) * y ^ ((9 : ℝ) / 200) := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 9 / 200 by norm_num)).def
      (show (0 : ℝ) < 1 / (4 * Real.pi) by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have h0 : 0 ≤ Real.log y := Real.log_nonneg hy1
    have h1 : 0 ≤ y ^ ((9 : ℝ) / 200) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg h1] at hy
    exact hy
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hE1, tendsto_natCast_atTop_atTop.eventually hE2,
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)),
    Design.shellDesign_regime S53L75 hS2 r ε hr hε 1 le_rfl, Filter.eventually_ge_atTop 2]
    with Qn h1 h2 h3 hreg hQn2
  intro P hdes s hs hs4
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  obtain ⟨-, -, -, -, -, hX, -, -⟩ := hreg P hdes
  set x := Real.log (Qn : ℝ) with hxdef
  set Q := (Qn : ℝ) with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast (show 1 ≤ Qn by omega)
  have hQ0 : 0 < Q := by linarith
  have hx1 : 1 ≤ x := h3
  have hx0 : 0 < x := by linarith
  -- the sieve, pointwise
  have hQn : Qn ≤ ⌊P.Q⌋₊ := by rw [hQ, Nat.floor_natCast]
  have hF : FfamZ P Qn s ≤ Zones.sieveBudgetQ P * normA2 P s := by
    have h1' : familySum Family.qle Qn (fun _ χ => ‖Achi P χ s‖ ^ 2)
        ≤ Zones.famSum P (fun _ χ => ‖Achi P χ s‖ ^ 2) :=
      familySum_le_famSum P Family.qle Qn hQn _ fun _ _ => sq_nonneg _
    exact h1'.trans (lemma43_sieve_half_A P hP largeSieveFamily_holds s)
  have hnA : 0 ≤ normA2 P s := Finset.sum_nonneg fun n _ => by positivity
  -- the weight on the strip is `C`
  have hW : shellWt P αp s = Cfam := by unfold shellWt; rw [if_pos hs4]
  -- family size
  have hS := sizeR_qle_lower' Qn (by omega)
  set S := Family.qle.sizeR Qn with hSdef
  have hCS : Q ^ 2 - 6 * Cfam * Q * (1 + x) ^ 2 ≤ Cfam * S := by
    have e : Cfam * ((18 / Real.pi ^ 4) * Q ^ 2 - 6 * Q * (1 + x) ^ 2)
        = Q ^ 2 - 6 * Cfam * Q * (1 + x) ^ 2 := by
      unfold Cfam; field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left hS hC0.le
  -- `6CQ(1+x)² ≤ Q²/(2x)`
  have hA : 6 * Cfam * Q * (1 + x) ^ 2 * (2 * x) ≤ Q ^ 2 := by
    have hx3 : x ^ 3 ≤ 1 / (48 * Cfam) * Q := h1
    have hb : (1 + x) ^ 2 * (2 * x) ≤ 8 * x ^ 3 := by
      have h1x : 1 + x ≤ 2 * x := by linarith
      have hsq : (1 + x) ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ (by linarith) h1x 2
      have := mul_le_mul_of_nonneg_right hsq (by linarith : (0 : ℝ) ≤ 2 * x)
      nlinarith
    have hc : 6 * Cfam * (8 * x ^ 3) ≤ Q := by
      have := mul_le_mul_of_nonneg_left hx3 (by positivity : (0 : ℝ) ≤ 48 * Cfam)
      rw [show 48 * Cfam * (1 / (48 * Cfam) * Q) = Q by field_simp] at this
      linarith
    have hd : 6 * Cfam * Q * (1 + x) ^ 2 * (2 * x) ≤ 6 * Cfam * Q * (8 * x ^ 3) := by
      have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 6 * Cfam * Q)
      linarith
    have := mul_le_mul_of_nonneg_left hc hQ0.le
    linarith
  -- `π𝒳 ≤ Q²/(4x)`
  have hB : Real.pi * P.XQ * (4 * x) ≤ Q ^ 2 := by
    have hQd : x ≤ 1 / (4 * Real.pi) * Q ^ ((9 : ℝ) / 200) := h2
    have hδ : Design.deltaShell = 9 / 200 := rfl
    rw [hδ, hQ] at hX
    have hsplit : Real.rpow Q (2 - 9 / 200) = Q ^ 2 / Q ^ ((9 : ℝ) / 200) := by
      show Q ^ ((2 : ℝ) - 9 / 200) = Q ^ 2 / Q ^ ((9 : ℝ) / 200)
      rw [Real.rpow_sub hQ0, Real.rpow_two]
    rw [hsplit] at hX
    have hQd0 : 0 < Q ^ ((9 : ℝ) / 200) := Real.rpow_pos_of_pos hQ0 _
    have h4 : 4 * Real.pi * x ≤ Q ^ ((9 : ℝ) / 200) := by
      have := mul_le_mul_of_nonneg_left hQd (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
      rw [show 4 * Real.pi * (1 / (4 * Real.pi) * Q ^ ((9 : ℝ) / 200)) = Q ^ ((9 : ℝ) / 200) by field_simp]
        at this
      linarith
    have hX' : P.XQ * Q ^ ((9 : ℝ) / 200) ≤ Q ^ 2 := by
      rw [le_div_iff₀ hQd0] at hX; exact hX
    have hX0 : 0 ≤ P.XQ := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left h4 hX0
    linarith
  -- `Q² + π𝒳 ≤ C·S·(1 + 2/x)`, as `x·(Q² + π𝒳) ≤ C·S·(x + 2)`
  have hbud : x * (Q ^ 2 + Real.pi * P.XQ) ≤ Cfam * S * (x + 2) := by
    have hA0 : 0 ≤ 6 * Cfam * Q * (1 + x) ^ 2 := by positivity
    have hCS' : Q ^ 2 ≤ Cfam * S + 6 * Cfam * Q * (1 + x) ^ 2 := by linarith
    have hxA : x * (6 * Cfam * Q * (1 + x) ^ 2) ≤ Q ^ 2 / 2 := by linarith
    have hxB : x * (Real.pi * P.XQ) ≤ Q ^ 2 / 4 := by linarith
    have hA1 : 6 * Cfam * Q * (1 + x) ^ 2 ≤ 6 * Cfam * Q * (1 + x) ^ 2 * x := le_mul_of_one_le_right hA0 hx1
    have hQ2 : Q ^ 2 ≤ 2 * (Cfam * S) := by linarith
    have hxQ : x * Q ^ 2 ≤ x * (Cfam * S + 6 * Cfam * Q * (1 + x) ^ 2) := mul_le_mul_of_nonneg_left hCS' hx0.le
    linarith
  -- the rate
  have hr1 : x⁻¹ ≤ x ^ (-θ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (show (-1 : ℝ) ≤ -θ by linarith)
    rwa [Real.rpow_neg_one] at this
  have hfac : Zones.sieveBudgetQ P ≤ (1 + 2 * x ^ (-θ)) * S * Cfam := by
    unfold Zones.sieveBudgetQ
    rw [hQ]
    have h5 : Q ^ 2 + Real.pi * P.XQ ≤ Cfam * S * (1 + 2 * x⁻¹) := by
      have e : Cfam * S * (1 + 2 * x⁻¹) = Cfam * S * (x + 2) / x := by field_simp
      rw [e, le_div_iff₀ hx0]
      linarith
    have hS0 : 0 ≤ S := by rw [hSdef]; unfold Family.sizeR; positivity
    have h6 : Cfam * S * (1 + 2 * x⁻¹) ≤ Cfam * S * (1 + 2 * x ^ (-θ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0.le hS0)
    linarith
  rw [hW]
  calc FfamZ P Qn s ≤ Zones.sieveBudgetQ P * normA2 P s := hF
    _ ≤ ((1 + 2 * x ^ (-θ)) * S * Cfam) * normA2 P s := mul_le_mul_of_nonneg_right hfac hnA
    _ = (1 + 2 * x ^ (-θ)) * S * (normA2 P s * Cfam) := by ring

end ShellK
end ZetaShell
