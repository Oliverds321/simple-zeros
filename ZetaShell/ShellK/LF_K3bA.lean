/-
K3b-A (L7_3c, round 10): the generic pieces of the K3b assembly, at one design point.
* `outZone_inter_Ioi`: `inZoneᶜ ∩ (a, ∞) = (a, ∞)` once `s₀ ≤ a`.
* `integrand_le`: pointwise, `g(B‖a‖² − Q²sav + err) ≤ Q²g((1 + δ₁)‖a‖² + ℒ) − Q²g·sav` (AM–GM for `2Q²‖a‖`,
  `R₀ ≤ 𝒳/Q` on the support of `g`).
* `sav_lower_pt`: `g·sav ≥ κU(g(s − ℓ_K) − L·1_{(L−1, L]})`.
* `shell_lower_pt`: on `s > α′ℒ`, `g‖a‖²·shellWt ≥ CℒU(1 − 1/ℒ)(g − 1_{(L−1, L]})` from `‖a‖² ≥ U(s − 1)`.
* `G_lower`: `∫_{(a,∞)} g ≥ (L − 2 − a)²/5184` (`w = 1`, `gQ_ge_bulk`).
* `Y_le`: `∫_{(a,∞)} g·s ≤ L∫_{(a,∞)} g`.
* `AS_upper`: `∫_{(a,∞)} g‖a‖² ≤ U(∫_{(a,∞)} g·s + L s₁² + ∫ g + K) + V` from a whole-line upper bound
  `∫ g‖a‖² ≤ U(∫_{(0,L+2]} g·s + K) + V` and the pointwise lower bound on `(s₁, a]`.
* `wholeLine_le`: `wholeLine_upper` in that form.
-/
import ZetaShell.ShellK.LF_K3bU
import ZetaShell.ShellK.LF_K3bP
import ZetaShell.ShellK.LF_K3a
import ZetaShell.LemmaK.LK_K8a3_Errors

noncomputable section
open scoped BigOperators ArithmeticFunction
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaShell.LemmaK

/-- `S = (a, ∞)` once `s₀ ≤ a`. -/
theorem outZone_inter_Ioi (P : ParamsQ) {a : ℝ} (ha : P.s0 ≤ a) (ha0 : 0 ≤ a) :
    (inZone P)ᶜ ∩ Ioi a = Ioi a := by
  ext s
  simp only [mem_inter_iff, mem_compl_iff, inZone, mem_setOf_eq, mem_Ioi, not_le]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [abs_of_pos (by linarith)]
    linarith

theorem normA2_nonneg (P : ParamsQ) (s : ℝ) : 0 ≤ normA2 P s :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem Lc_eq_LL (P : ParamsQ) : Lc P.Q P.T = P.LL := rfl

/-- **Pointwise integrand bound** (with `δ₁Q² ≥ 2π𝒳 + 4 + (𝒳/Q)² + Q²/ℒ`). -/
theorem integrand_le (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (C₁ : ℝ) (Qn : ℕ)
    (hTL : 1 ≤ P.T * P.LL) (δ₁ : ℝ)
    (hδ : 2 * Real.pi * P.XQ + 4 + (P.XQ / P.Q) ^ 2 + P.Q ^ 2 / P.LL ≤ δ₁ * P.Q ^ 2) (s : ℝ) :
    P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s)
      ≤ P.Q ^ 2 * (P.gQ s * ((1 + δ₁) * normA2 P s + P.LL))
        - P.Q ^ 2 * (P.gQ s * savWeight C₁ Qn P s) := by
  have hg0 := hP.gQ_nonneg hw s
  by_cases hs : P.LB ≤ |s|
  · rw [hP.gQ_eq_zero hw hs]; simp
  push Not at hs
  have hLL : 0 < P.LL := hP.LL_pos
  have hQ0 : 0 < P.Q := by linarith [hP.Q_ge]
  set nA := normA2 P s with hnAdef
  have hnA : 0 ≤ nA := normA2_nonneg P s
  have hR00 : 0 ≤ R0 P.Q P.T s := by
    unfold R0
    rw [Lc_eq_LL]
    have : 0 < P.Q * P.T * P.LL := by
      have := hP.T_pos
      positivity
    positivity
  have hR0 : R0 P.Q P.T s ≤ P.XQ / P.Q := by
    unfold R0
    rw [Lc_eq_LL]
    have hes : Real.exp s ≤ P.XQ := by
      unfold ParamsQ.XQ
      exact Real.exp_le_exp.mpr (le_trans (le_abs_self s) hs.le)
    have hden : P.Q ≤ P.Q * P.T * P.LL := by
      rw [mul_assoc]; exact le_mul_of_one_le_right hQ0.le hTL
    calc Real.exp s / (P.Q * P.T * P.LL) ≤ P.XQ / (P.Q * P.T * P.LL) :=
          div_le_div_of_nonneg_right hes (by linarith)
      _ ≤ P.XQ / P.Q := div_le_div_of_nonneg_left (Real.exp_pos _).le hQ0 hden
  have hR : (max 2 (R0 P.Q P.T s)) ^ 2 ≤ 4 + (P.XQ / P.Q) ^ 2 := by
    rcases le_total 2 (R0 P.Q P.T s) with h | h
    · rw [max_eq_right h]
      have := pow_le_pow_left₀ hR00 hR0 2
      linarith
    · rw [max_eq_left h]
      have := sq_nonneg (P.XQ / P.Q)
      linarith
  have hamgm : 2 * P.Q ^ 2 * Real.sqrt nA ≤ P.Q ^ 2 / P.LL * nA + P.Q ^ 2 * P.LL := by
    have hs2 := Real.sq_sqrt hnA
    have h1 : 2 * Real.sqrt nA * P.LL ≤ nA + P.LL ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt nA - P.LL)]
    have h2 : 2 * Real.sqrt nA ≤ nA / P.LL + P.LL := by
      rw [div_add' _ _ _ hLL.ne', le_div_iff₀ hLL]
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg P.Q)
    have e : P.Q ^ 2 * (nA / P.LL + P.LL) = P.Q ^ 2 / P.LL * nA + P.Q ^ 2 * P.LL := by ring
    linarith
  have hX0 : 0 ≤ P.XQ := (Real.exp_pos _).le
  have key : sieveBudgetQ P * nA - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s
      ≤ P.Q ^ 2 * ((1 + δ₁) * nA + P.LL) - P.Q ^ 2 * savWeight C₁ Qn P s := by
    unfold sieveBudgetQ errWeight
    rw [← hnAdef]
    have h1 : (max 2 (R0 P.Q P.T s)) ^ 2 * nA ≤ (4 + (P.XQ / P.Q) ^ 2) * nA :=
      mul_le_mul_of_nonneg_right hR hnA
    have h2 : (2 * Real.pi * P.XQ + 4 + (P.XQ / P.Q) ^ 2 + P.Q ^ 2 / P.LL) * nA ≤ δ₁ * P.Q ^ 2 * nA :=
      mul_le_mul_of_nonneg_right hδ hnA
    nlinarith
  have := mul_le_mul_of_nonneg_left key hg0
  nlinarith

/-- `g·sav ≥ κU(g(s − ℓ_K) − L·1_{(L−1, L]})`. -/
theorem sav_lower_pt (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (C₁ : ℝ) (Qn : ℕ)
    (hκ : 0 ≤ 1 - C₁ / Real.log Qn) (hℓ0 : 0 ≤ ellK P.Q P.T) (hL1 : 1 ≤ P.LB) (s : ℝ) :
    (1 - C₁ / Real.log Qn) * (P.T / (2 * Real.pi))
        * (P.gQ s * (s - ellK P.Q P.T) - P.LB * (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s)
      ≤ P.gQ s * savWeight C₁ Qn P s := by
  have hg0 := hP.gQ_nonneg hw s
  have hU0 : 0 ≤ P.T / (2 * Real.pi) := by have := hP.T_pos; positivity
  have hκU : 0 ≤ (1 - C₁ / Real.log Qn) * (P.T / (2 * Real.pi)) := mul_nonneg hκ hU0
  have hlogX : Real.log P.XQ = P.LB := by unfold ParamsQ.XQ; exact Real.log_exp _
  unfold savWeight
  rw [hlogX]
  by_cases h1 : s ≤ P.LB - 1
  · have hind : (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s = 0 :=
      Set.indicator_of_notMem (fun h => by linarith [h.1]) _
    rw [hind, if_pos h1]
    have hm : P.gQ s * (s - ellK P.Q P.T) ≤ P.gQ s * max (s - ellK P.Q P.T) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hg0
    have e : P.gQ s * ((1 - C₁ / Real.log Qn) * (P.T / (2 * Real.pi)) * max (s - ellK P.Q P.T) 0 * 1)
        = (1 - C₁ / Real.log Qn) * (P.T / (2 * Real.pi)) * (P.gQ s * max (s - ellK P.Q P.T) 0) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hm hκU
    linarith
  · push Not at h1
    rw [if_neg (by linarith)]
    simp only [mul_zero]
    by_cases h2 : s ≤ P.LB
    · have hind : (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s = 1 :=
        Set.indicator_of_mem (show s ∈ Ioc (P.LB - 1) P.LB from ⟨h1, h2⟩) _
      rw [hind]
      have hg1 : P.gQ s ≤ 1 := by
        have h := hP.gQ_le_env hw s
        rw [abs_of_pos (by linarith)] at h
        have : max (P.LB - s) 0 ≤ 1 := max_le (by linarith) (by norm_num)
        linarith
      have hgs : P.gQ s * (s - ellK P.Q P.T) ≤ P.LB := by
        rcases le_total 0 (s - ellK P.Q P.T) with h | h
        · calc P.gQ s * (s - ellK P.Q P.T) ≤ 1 * (s - ellK P.Q P.T) := mul_le_mul_of_nonneg_right hg1 h
            _ ≤ P.LB := by linarith
        · have := mul_nonpos_of_nonneg_of_nonpos hg0 h
          linarith
      have : P.gQ s * (s - ellK P.Q P.T) - P.LB * 1 ≤ 0 := by linarith
      nlinarith
    · push Not at h2
      have hind : (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s = 0 :=
        Set.indicator_of_notMem (fun h => by linarith [h.2]) _
      rw [hind, hP.gQ_eq_zero hw (by rw [abs_of_pos (by linarith)]; exact h2.le)]
      simp

/-- On `s > α′ℒ`: `g‖a‖²·shellWt ≥ CℒU(1 − 1/ℒ)(g − 1_{(L−1, L]})`. -/
theorem shell_lower_pt (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (αp : ℝ) (hLL1 : 1 ≤ P.LL)
    (ha1 : Real.log P.Q + 4 ≤ αp * P.LL) (haL : P.LL ≤ αp * P.LL)
    (hlow : ∀ s, αp * P.LL < s → s ≤ P.LB - 1 → P.T / (2 * Real.pi) * (s - 1) ≤ normA2 P s)
    (s : ℝ) (hs : αp * P.LL < s) :
    Cfam * P.LL * (P.T / (2 * Real.pi)) * (1 - 1 / P.LL)
        * (P.gQ s - (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s)
      ≤ P.gQ s * (normA2 P s * shellWt P αp s) := by
  have hg0 := hP.gQ_nonneg hw s
  have hU0 : 0 < P.T / (2 * Real.pi) := by have := hP.T_pos; positivity
  have hC0 : 0 < Cfam := by unfold Cfam; positivity
  have hs0 : 0 < s := by linarith
  have hsL : P.LL ≤ s := by linarith
  have hnA := normA2_nonneg P s
  have hsw : shellWt P αp s = Cfam * P.LL / s := by
    unfold shellWt
    rw [if_neg (by linarith), if_neg (by linarith)]
  have hc0 : 0 ≤ Cfam * P.LL * (P.T / (2 * Real.pi)) * (1 - 1 / P.LL) := by
    have : 0 ≤ 1 - 1 / P.LL := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hLL1
    positivity
  have hR0 : 0 ≤ P.gQ s * (normA2 P s * shellWt P αp s) := by
    rw [hsw]; positivity
  by_cases h1 : s ≤ P.LB - 1
  · have hind : (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s = 0 :=
      Set.indicator_of_notMem (fun h => by linarith [h.1]) _
    rw [hind, sub_zero, hsw]
    have hl := hlow s hs h1
    have h2 : 1 - 1 / P.LL ≤ (s - 1) / s := by
      rw [sub_div, div_self hs0.ne']
      have : 1 / s ≤ 1 / P.LL := one_div_le_one_div_of_le (by linarith) hsL
      linarith
    have h3 : Cfam * P.LL * (P.T / (2 * Real.pi)) * ((s - 1) / s)
        = P.T / (2 * Real.pi) * (s - 1) * (Cfam * P.LL / s) := by
      field_simp
    calc Cfam * P.LL * (P.T / (2 * Real.pi)) * (1 - 1 / P.LL) * P.gQ s
        ≤ Cfam * P.LL * (P.T / (2 * Real.pi)) * ((s - 1) / s) * P.gQ s := by
          apply mul_le_mul_of_nonneg_right _ hg0
          apply mul_le_mul_of_nonneg_left h2
          positivity
      _ = P.T / (2 * Real.pi) * (s - 1) * (Cfam * P.LL / s) * P.gQ s := by rw [h3]
      _ ≤ normA2 P s * (Cfam * P.LL / s) * P.gQ s := by
          apply mul_le_mul_of_nonneg_right _ hg0
          exact mul_le_mul_of_nonneg_right hl (by positivity)
      _ = P.gQ s * (normA2 P s * (Cfam * P.LL / s)) := by ring
  · push Not at h1
    by_cases h2 : s ≤ P.LB
    · have hind : (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s = 1 :=
        Set.indicator_of_mem (show s ∈ Ioc (P.LB - 1) P.LB from ⟨h1, h2⟩) _
      rw [hind]
      have hg1 : P.gQ s ≤ 1 := by
        have h := hP.gQ_le_env hw s
        rw [abs_of_pos hs0] at h
        have : max (P.LB - s) 0 ≤ 1 := max_le (by linarith) (by norm_num)
        linarith
      have : Cfam * P.LL * (P.T / (2 * Real.pi)) * (1 - 1 / P.LL) * (P.gQ s - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
      linarith
    · push Not at h2
      have hind : (Ioc (P.LB - 1) P.LB).indicator (fun _ => (1 : ℝ)) s = 0 :=
        Set.indicator_of_notMem (fun h => by linarith [h.2]) _
      rw [hind, hP.gQ_eq_zero hw (by rw [abs_of_pos hs0]; exact h2.le)]
      simp only [sub_zero, mul_zero, zero_mul]
      exact le_refl 0

/-- `∫_{(a,∞)} g ≥ (L − 2 − a)²/5184` at `w = 1`. -/
theorem G_lower (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (hw1 : P.w = 1) (a : ℝ) (ha : 0 ≤ a)
    (haL : a + 2 ≤ P.LB) :
    (P.LB - 2 - a) ^ 2 / 5184 ≤ ∫ s in Ioi a, P.gQ s := by
  set m := (a + (P.LB - 2)) / 2 with hm
  have ham : a ≤ m := by rw [hm]; linarith
  have hgint := hP.gQ_integrable hw
  have h1 : ∫ s in Ioc a m, P.gQ s ≤ ∫ s in Ioi a, P.gQ s :=
    setIntegral_mono_set hgint.integrableOn (ae_of_all _ fun s => hP.gQ_nonneg hw s)
      (Ioc_subset_Ioi_self.eventuallyLE)
  have h2 : ∫ s in Ioc a m, (P.LB - 2 - a) / 2592 ≤ ∫ s in Ioc a m, P.gQ s := by
    apply setIntegral_mono_on (integrableOn_const (by simp)) hgint.integrableOn measurableSet_Ioc
    intro s hs
    have hb := hP.gQ_ge_bulk hw s
    rw [hw1, abs_of_pos (by linarith [hs.1])] at hb
    have hpos : 0 ≤ P.LB - 2 * 1 - s := by linarith [hs.2]
    rw [max_eq_left hpos] at hb
    have : (P.LB - 2 - a) / 2592 ≤ 1 / 1296 * (P.LB - 2 * 1 - s) := by
      rw [hm] at hs
      linarith [hs.2]
    linarith
  have h3 : ∫ s in Ioc a m, (P.LB - 2 - a) / 2592 = (P.LB - 2 - a) ^ 2 / 5184 := by
    rw [← intervalIntegral.integral_of_le ham, intervalIntegral.integral_const, smul_eq_mul, hm]
    ring
  linarith

/-- `∫_{(a,∞)} g·s ≤ L∫_{(a,∞)} g`. -/
theorem Y_le (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (a : ℝ) :
    ∫ s in Ioi a, P.gQ s * s ≤ P.LB * ∫ s in Ioi a, P.gQ s := by
  have hgy : Integrable (fun s : ℝ => P.gQ s * s) := gQ_mul_integrable P hP hw continuous_id
  have hgint := hP.gQ_integrable hw
  rw [← integral_const_mul]
  apply setIntegral_mono_on hgy.integrableOn (hgint.const_mul _).integrableOn measurableSet_Ioi
  intro s _
  have hg0 := hP.gQ_nonneg hw s
  by_cases h : P.LB ≤ |s|
  · rw [hP.gQ_eq_zero hw h]; simp
  · push Not at h
    have : s ≤ P.LB := le_trans (le_abs_self s) h.le
    nlinarith

/-- **`A_S` from above**: whole line minus the pointwise lower bound on `(s₁, a]`. -/
theorem AS_upper (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (s₁ a K V : ℝ) (hs₁ : 0 ≤ s₁)
    (hs₁a : s₁ ≤ a) (haL : a ≤ P.LB + 2)
    (hlow : ∀ y, s₁ < y → y ≤ a → P.T / (2 * Real.pi) * (y - 1) ≤ normA2 P y)
    (hwhole : ∫ s, P.gQ s * normA2 P s
      ≤ P.T / (2 * Real.pi) * ((∫ s in Ioc 0 (P.LB + 2), P.gQ s * s) + K) + V) :
    ∫ s in Ioi a, P.gQ s * normA2 P s
      ≤ P.T / (2 * Real.pi) * ((∫ s in Ioi a, P.gQ s * s) + P.LB * s₁ ^ 2 + (∫ s, P.gQ s) + K) + V := by
  have hT := hP.T_pos
  set U := P.T / (2 * Real.pi) with hU
  have hU0 : 0 < U := by positivity
  have hLB := hP.LB_pos
  have hnA := gQ_mul_integrable P hP hw (normA2_continuous P hT.le)
  have hgy : Integrable (fun s : ℝ => P.gQ s * s) := gQ_mul_integrable P hP hw continuous_id
  have hgy1 : Integrable (fun s : ℝ => P.gQ s * (s - 1)) :=
    gQ_mul_integrable P hP hw (continuous_id.sub continuous_const)
  have hgint := hP.gQ_integrable hw
  have hnn : ∀ s, 0 ≤ P.gQ s * normA2 P s := fun s => mul_nonneg (hP.gQ_nonneg hw s) (normA2_nonneg P s)
  -- (i) the two disjoint pieces
  have hi : (∫ s in Ioc s₁ a, P.gQ s * normA2 P s) + ∫ s in Ioi a, P.gQ s * normA2 P s
      ≤ ∫ s, P.gQ s * normA2 P s := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hnA.integrableOn hnA.integrableOn,
      Ioc_union_Ioi_eq_Ioi hs₁a]
    exact setIntegral_le_integral hnA (ae_of_all _ hnn)
  -- (ii) the pointwise lower bound on `(s₁, a]`
  have hii : ∫ s in Ioc s₁ a, U * (P.gQ s * (s - 1)) ≤ ∫ s in Ioc s₁ a, P.gQ s * normA2 P s := by
    apply setIntegral_mono_on (hgy1.const_mul U).integrableOn hnA.integrableOn measurableSet_Ioc
    intro y hy
    have := mul_le_mul_of_nonneg_left (hlow y hy.1 hy.2) (hP.gQ_nonneg hw y)
    calc U * (P.gQ y * (y - 1)) = P.gQ y * (U * (y - 1)) := by ring
      _ ≤ P.gQ y * normA2 P y := this
  have hii' : ∫ s in Ioc s₁ a, U * (P.gQ s * (s - 1))
      = U * ((∫ s in Ioc s₁ a, P.gQ s * s) - ∫ s in Ioc s₁ a, P.gQ s) := by
    rw [integral_const_mul, ← integral_sub hgy.integrableOn hgint.integrableOn]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    ring
  -- (iii) the split of `(0, L + 2]`
  have hiii : ∫ s in Ioc 0 (P.LB + 2), P.gQ s * s
      = (∫ s in Ioc 0 s₁, P.gQ s * s) + (∫ s in Ioc s₁ a, P.gQ s * s) + ∫ s in Ioc a (P.LB + 2), P.gQ s * s := by
    rw [← Ioc_union_Ioc_eq_Ioc (le_trans hs₁ hs₁a) haL, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc hgy.integrableOn hgy.integrableOn, ← Ioc_union_Ioc_eq_Ioc hs₁ hs₁a,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hgy.integrableOn hgy.integrableOn]
  -- (iv) the top piece
  have hiv : ∫ s in Ioc a (P.LB + 2), P.gQ s * s ≤ ∫ s in Ioi a, P.gQ s * s := by
    apply setIntegral_mono_set hgy.integrableOn
    · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
      exact ae_of_all _ fun s hs => by
        simp only [Pi.zero_apply]
        exact mul_nonneg (hP.gQ_nonneg hw s) (by linarith [mem_Ioi.mp hs])
    · exact Ioc_subset_Ioi_self.eventuallyLE
  -- (v) the bottom piece
  have hv : ∫ s in Ioc 0 s₁, P.gQ s * s ≤ P.LB * s₁ ^ 2 := by
    have h := setIntegral_mono_on (s := Ioc 0 s₁) hgy.integrableOn
      (integrableOn_const (C := P.LB * s₁) (by simp)) measurableSet_Ioc (fun y hy => by
        have hg := hP.gQ_le_env hw y
        have hg0 := hP.gQ_nonneg hw y
        have hgL : P.gQ y ≤ P.LB := le_trans hg (max_le (by linarith [abs_nonneg y]) hLB.le)
        exact mul_le_mul hgL hy.2 (by linarith [hy.1]) hLB.le)
    have hc : ∫ s in Ioc 0 s₁, P.LB * s₁ = P.LB * s₁ ^ 2 := by
      rw [← intervalIntegral.integral_of_le hs₁, intervalIntegral.integral_const, smul_eq_mul]
      ring
    linarith
  -- (vi) `∫_{(s₁,a]} g ≤ ∫ g`
  have hvi : ∫ s in Ioc s₁ a, P.gQ s ≤ ∫ s, P.gQ s :=
    setIntegral_le_integral hgint (ae_of_all _ fun s => hP.gQ_nonneg hw s)
  have hg0' : 0 ≤ ∫ s in Ioc s₁ a, P.gQ s := setIntegral_nonneg measurableSet_Ioc fun s _ => hP.gQ_nonneg hw s
  have hU1 := mul_le_mul_of_nonneg_left hiv hU0.le
  have hU2 := mul_le_mul_of_nonneg_left hv hU0.le
  have hU3 := mul_le_mul_of_nonneg_left hvi hU0.le
  rw [hiii] at hwhole
  rw [hii'] at hii
  nlinarith

/-- **The whole line, from above** (`wholeLine_upper` with `∫₀^{L+2} GW·y ≤ ∫_{(0,L+2]} g·y + (L+2)²` and the
Chebyshev–Mertens bound `Σ_{n≤𝒳} Λ(n)²/n ≤ L²/2 + C₀L`). -/
theorem wholeLine_le (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {C₀ : ℝ}
    (hC₀ : ∀ t : ℝ, 2 ≤ t → |(∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n) k)
      - Real.log t ^ 2 / 2| ≤ C₀ * Real.log t)
    (hL' : (8 : ℝ) ≤ P.LB + 2) {S : ℝ} (hS : ∀ x, |deriv Real.smoothTransition x| ≤ S) :
    ∫ s, P.gQ s * normA2 P s
      ≤ P.T / (2 * Real.pi) * ((∫ s in Ioc 0 (P.LB + 2), P.gQ s * s)
          + (1 + (1 + S) * (2 * |C₀| + 10)) * (P.LB + 2) ^ 2)
        + 2 * P.aQ * P.LB / Real.pi ^ 2 * (P.LB ^ 2 / 2 + C₀ * P.LB) := by
  have h := wholeLine_upper P hP hw hC₀ hL' hS
  have hLB0 : 0 ≤ P.LB + 2 := by linarith
  have hLB := hP.LB_pos
  have hT := hP.T_pos
  have ha0 := hP.aQ_pos
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  have hGW : (∫ y in (0 : ℝ)..(P.LB + 2), GW P.gQ P.LB y * y)
      ≤ (∫ s in Ioc 0 (P.LB + 2), P.gQ s * s) + (P.LB + 2) ^ 2 := by
    have hgc := hP.gQ_continuous hw
    have hstc : Continuous (fun y => Real.smoothTransition (y - P.LB)) :=
      Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)
    have hi1 : IntervalIntegrable (fun y => P.gQ y * y) volume 0 (P.LB + 2) :=
      (hgc.mul continuous_id).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun y => 2 * (1 - Real.smoothTransition (y - P.LB)) * y) volume 0
        (P.LB + 2) := ((continuous_const.mul (continuous_const.sub hstc)).mul continuous_id).intervalIntegrable _ _
    have hi3 : IntervalIntegrable (fun y : ℝ => 2 * y) volume 0 (P.LB + 2) :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    have e1 : (fun y => GW P.gQ P.LB y * y)
        = fun y => P.gQ y * y + 2 * (1 - Real.smoothTransition (y - P.LB)) * y := by
      funext y; unfold GW; ring
    rw [e1, intervalIntegral.integral_add hi1 hi2]
    rw [intervalIntegral.integral_of_le hLB0]
    have hle : (∫ y in (0 : ℝ)..(P.LB + 2), 2 * (1 - Real.smoothTransition (y - P.LB)) * y)
        ≤ ∫ y in (0 : ℝ)..(P.LB + 2), 2 * y := by
      apply intervalIntegral.integral_mono_on hLB0 hi2 hi3
      intro y hy
      have := Real.smoothTransition.nonneg (y - P.LB)
      have hy0 : 0 ≤ y := hy.1
      nlinarith
    have hval : (∫ y in (0 : ℝ)..(P.LB + 2), 2 * y) = (P.LB + 2) ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    linarith
  have hsum : ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) ≤ P.LB ^ 2 / 2 + C₀ * P.LB := by
    have hX2 : (2 : ℝ) ≤ P.XQ := by
      unfold ParamsQ.XQ
      have := Real.add_one_le_exp P.LB
      linarith
    have h1 := (abs_le.mp (hC₀ P.XQ hX2)).2
    have hlog : Real.log P.XQ = P.LB := by unfold ParamsQ.XQ; exact Real.log_exp _
    rw [hlog] at h1
    have e : ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ)
        = ∑ k ∈ Finset.Ioc 0 ⌊P.XQ⌋₊, (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n) k := rfl
    rw [e]
    linarith
  set U := P.T / (2 * Real.pi) with hU
  have hU0 : 0 < U := by positivity
  have e : 1 / (4 * Real.pi ^ 2) * (2 * Real.pi * P.T
          * ((∫ y in (0 : ℝ)..(P.LB + 2), GW P.gQ P.LB y * y) + (1 + S) * ((2 * |C₀| + 10) * (P.LB + 2) ^ 2))
        + 8 * (P.aQ * P.LB) * ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ))
      = U * ((∫ y in (0 : ℝ)..(P.LB + 2), GW P.gQ P.LB y * y) + (1 + S) * ((2 * |C₀| + 10) * (P.LB + 2) ^ 2))
        + 2 * P.aQ * P.LB / Real.pi ^ 2 * ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) := by
    rw [hU]; field_simp; ring
  rw [e] at h
  have h1 := mul_le_mul_of_nonneg_left hGW hU0.le
  have h2 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * P.aQ * P.LB / Real.pi ^ 2)
  nlinarith

end F1c
end ShellK
end ZetaShell
