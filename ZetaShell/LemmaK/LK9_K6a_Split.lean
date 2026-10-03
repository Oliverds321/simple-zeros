/-
L7_9 round 3: split of the open sub-node K6a (`model_mass`) into two leaves, both open:
(a1) `model_l2_lower`: the full model mass, `Σ|w̃(n)|² ≥ U − C` (sum vs integral, `∫_ℝ|D_T|² = 2πT`);
(a2) `model_outer`: the mass outside the arc, `Σ|w̃(n)|² − ∫_{−Δ}^{Δ}|M̃|² ≤ C·U/ℒ²` (Parseval on one period,
     summation by parts with `|1 − e(β)| ≥ 4‖β‖`, and `Σ|w̃(n+1) − w̃(n)|² = O(T³e^{−2s})` from an `L²` bound on
     `D_T′`, e.g. `‖D_T′(v)‖ ≤ min(2T², 4T/|v|)` in L7_5's shared `DT_Facts`).
`model_mass_of_split` derives K6a's statement from them (`U ≥ log Q`, `ℒ ≥ (log Q)/2`).
-/
import ZetaShell.LemmaK.LK9_K6_Defs
import ZetaShell.LemmaK.LK9_K6a_Outer
import ZetaShell.LemmaK.LK9_K6a_L2Final

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

/-- (a1) the full model mass (proved in `LK9_K6a_L2Final.lean`, round 4). -/
theorem model_l2_lower (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi) - C
        ≤ ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s) := by
  exact K6.model_l2_lower_aux lam r ε hlam1 hlam2 hr hε

/-- (a2) the model mass outside the arc (proved in `LK9_K6a_Outer.lean`, round 4). -/
theorem model_outer (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s)
        - ∫ β in (-(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))..(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)), ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s) β‖ ^ 2
        ≤ C * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi)) / Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ^ 2 := by
  exact K6.model_outer_aux lam r ε hlam1 hlam2 hr hε

/-- K6a's statement from (a1) and (a2). -/
theorem model_mass_of_split (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      (1 - C / Real.log (Qn : ℝ)) * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi))
        ≤ ∫ β in (-(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))..(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)), ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s) β‖ ^ 2 := by
  obtain ⟨C₁, h1⟩ := model_l2_lower lam r ε hlam1 hlam2 hr hε
  obtain ⟨C₂, h2⟩ := model_outer lam r ε hlam1 hlam2 hr hε
  refine ⟨|C₁| + 4 * |C₂|, by positivity, ?_⟩
  have E2 : ∀ᶠ Qn : ℕ in atTop, (4 : ℝ) ≤ Real.log (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 4)
  filter_upwards [h1, h2, E2] with Qn hA hB hlog s hs1 hs2
  have hA' := hA s hs1 hs2
  have hB' := hB s hs1 hs2
  set x := Real.log (Qn : ℝ) with hx
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  set L := Lc (Qn : ℝ) T with hL
  set U := T / (2 * Real.pi) with hU
  have hx0 : 0 < x := by linarith
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  have hQ1 : (1 : ℝ) ≤ Qn := by
    by_contra h; rw [not_le] at h
    have : Real.log (Qn : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hQ0 : (0 : ℝ) < Qn := by linarith
  have hT3 : x ^ 3 ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) (by linarith : (3 : ℝ) ≤ r + ε)
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h
  have h64 : (64 : ℝ) ≤ x ^ 3 := by
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hlog 3
    norm_num at h4; linarith
  have hT1 : 1 ≤ T := by linarith
  have hUx : x ≤ U := by
    rw [hU, le_div_iff₀ (by positivity)]
    have h16 : x * (2 * Real.pi) ≤ x * 16 := mul_le_mul_of_nonneg_left (by linarith) hx0.le
    have hx2 : 16 ≤ x ^ 2 := by nlinarith
    have h3 : x * 16 ≤ x ^ 3 := by
      calc x * 16 ≤ x * x ^ 2 := mul_le_mul_of_nonneg_left hx2 hx0.le
        _ = x ^ 3 := by ring
    linarith
  -- ℒ ≥ x/2
  have hL2 : x / 2 ≤ L := by
    rw [hL, Lc]
    have h1 : Real.log ((Qn : ℝ) / (2 * Real.pi)) ≤ Real.log ((Qn : ℝ) * T / (2 * Real.pi)) :=
      Real.log_le_log (by positivity) (by
        apply div_le_div_of_nonneg_right _ (by positivity); nlinarith)
    rw [Real.log_div hQ0.ne' (by positivity)] at h1
    have h2 : Real.log (2 * Real.pi) ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have := Real.add_one_le_exp (2 : ℝ)
      have h3 : (7 : ℝ) ≤ Real.exp 2 := by
        have he := Real.exp_one_gt_d9
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
      linarith
    linarith
  have hL0 : 0 < L := by linarith
  have hU0 : 0 ≤ U := by positivity
  -- combine
  have hC1 : -C₁ ≥ -(|C₁| * U / x) := by
    have : |C₁| ≤ |C₁| * U / x := by
      rw [le_div_iff₀ hx0]; exact mul_le_mul_of_nonneg_left hUx (abs_nonneg _)
    linarith [le_abs_self C₁]
  have hC2 : C₂ * U / L ^ 2 ≤ 4 * |C₂| * U / x := by
    have hLsq : x ^ 2 / 4 ≤ L ^ 2 := by nlinarith
    have hxx : x ≤ x ^ 2 / 4 := by nlinarith
    calc C₂ * U / L ^ 2 ≤ |C₂| * U / L ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hU0) (by positivity)
      _ ≤ |C₂| * U / x :=
          div_le_div_of_nonneg_left (by positivity) hx0 (by linarith)
      _ ≤ 4 * |C₂| * U / x := by
          apply div_le_div_of_nonneg_right _ hx0.le
          nlinarith [abs_nonneg C₂]
  have e : (1 - (|C₁| + 4 * |C₂|) / x) * U = U - |C₁| * U / x - 4 * |C₂| * U / x := by
    field_simp
    ring
  rw [e]
  linarith

end LemmaK
end ZetaShell
