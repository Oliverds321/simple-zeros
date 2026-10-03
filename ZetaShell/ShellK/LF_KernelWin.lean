/-
F1c-3c1 (L7_3, round 7): **the kernel identity for the Shell weight** (the main term of `smooth_majorant`):
  `∫_{s₀}^{L} g(y)·wOut(y)·y dy ≤ (ℒ(aL)²/2)·KoutShell(C, α′, a, v_d)`,   `a = zoneFactor = s₀/ℒ`.
Proof: `y = αℒ` (`intervalIntegral.integral_comp_mul_right`), `g(αℒ) = (aλ)²ℒ·ψ_{v_d}(α)` (`gQ_eq_psi_vDesign`), and
pointwise `(αℒ)·wOut(αℒ)/ℒ` is the Shell kernel `k(α)` = `Cα` / `1` / `C`, bounded by `kout(α)` = `Cα` on `(a,1]`,
`1` on `(1,α′]`, `C` beyond (on `(b,1]`, `b = (log Q+4)/ℒ`: `1 ≤ Cα` since `Cb ≥ 1`); then
`∫_a^λ kout·ψ = (C/2)Jzone(a) + ½∫_{1<|α|≤α′}ψ + C∫_{α′}^{λ}ψ ≤ ½·KoutShell` (`Jzone_eq_two_interval`, `sym_strip`).
Hypotheses of `kernel_window_at`: `0 ≤ a ≤ 1`, `log Q + 4 ≤ ℒ ≤ C(log Q + 4)`, `α′ ≤ λ`.
-/
import ZetaShell.ShellK.LF_OutDiag

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

/-- `∫_{p<|α|≤q} f = 2∫_p^q f` for even integrable `f` (`Jzone_eq_two_interval`'s proof, generic). -/
theorem sym_strip {f : ℝ → ℝ} (hf : Integrable f) (heven : ∀ α, f (-α) = f α) {p q : ℝ} (hp : 0 ≤ p)
    (hpq : p ≤ q) : (∫ α in {α : ℝ | p < |α| ∧ |α| ≤ q}, f α) = 2 * ∫ α in p..q, f α := by
  have hS : {α : ℝ | p < |α| ∧ |α| ≤ q} = Ioc p q ∪ Ico (-q) (-p) := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Ioc, mem_Ico]
    rcases abs_cases x with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [e]
    · constructor
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h2⟩
        · exact absurd (lt_of_le_of_lt he (by linarith)) (lt_irrefl _)
    · constructor
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨by linarith, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · linarith
        · exact ⟨by linarith, by linarith⟩
  have hdisj : Disjoint (Ioc p q) (Ico (-q) (-p)) := by
    rw [Set.disjoint_left]
    rintro x ⟨h1, _⟩ ⟨_, h2⟩
    linarith
  rw [hS, setIntegral_union hdisj measurableSet_Ico hf.integrableOn hf.integrableOn]
  have hpos : ∫ α in Ioc p q, f α = ∫ α in p..q, f α := by
    rw [intervalIntegral.integral_of_le hpq]
  have hneg : ∫ α in Ico (-q) (-p), f α = ∫ α in p..q, f α := by
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : (-q:ℝ) ≤ -p),
      ← intervalIntegral.integral_comp_neg (fun α => f α)]
    rw [intervalIntegral.integral_of_le hpq, intervalIntegral.integral_of_le hpq]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only [heven]
  rw [hpos, hneg]
  ring

/-- `s₀ = zoneFactor·ℒ`. -/
theorem s0_eq_zoneFactor (P : ParamsQ) (hP : P.Valid) : P.s0 = zoneFactor P * P.LL := by
  have hQ : 0 < P.Q := by linarith [hP.Q_ge]
  have hT : 0 < P.T := hP.T_pos
  have hLL : 0 < P.LL := hP.LL_pos
  have hsplit : P.LL = Real.log P.Q + Zeta23.l P.T := by
    unfold ParamsQ.LL Zeta23.l
    rw [mul_div_assoc, Real.log_mul hQ.ne' (by positivity)]
  unfold zoneFactor ParamsQ.s0
  have : (1 - Zeta23.l P.T / P.LL) * P.LL = Real.log P.Q := by
    field_simp
    linarith
  calc (1 - P.deltaPrime) * Real.log P.Q = (1 - P.deltaPrime) * ((1 - Zeta23.l P.T / P.LL) * P.LL) := by
        rw [this]
    _ = (1 - P.deltaPrime) * (1 - Zeta23.l P.T / P.LL) * P.LL := by ring

/-- the comparison kernel `kout`: `Cα` on `α ≤ 1`, `1` on `(1, α′]`, `C` beyond. -/
def koutK (α : ℝ) : ℝ := if α ≤ 1 then Cfam * α else if α ≤ 2497 / 1500 then 1 else Cfam

theorem koutK_measurable : Measurable koutK := by
  unfold koutK
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) (measurable_const.mul measurable_id) ?_
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const

/-- **The pointwise kernel bound.** For `α ≥ a`:
`g(αℒ)·wOut(αℒ)·(αℒ) ≤ (aλ)²ℒ²·(kout(α)·ψ_{v_d}(α))`. -/
theorem pointwise_kernel (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (ha0 : 0 ≤ zoneFactor P)
    (hb1 : Real.log P.Q + 4 ≤ P.LL) (hbC : P.LL ≤ Cfam * (Real.log P.Q + 4)) (α : ℝ)
    (hα : zoneFactor P ≤ α) :
    P.gQ (α * P.LL) * wOut P (α * P.LL) * (α * P.LL)
      ≤ (P.aQ * P.lam) ^ 2 * P.LL ^ 2 * (koutK α * psi (vDesign P) α) := by
  have hLL := hP.LL_pos
  have hC0 : (0 : ℝ) < Cfam := by unfold Cfam; positivity
  have hpsi0 : 0 ≤ psi (vDesign P) α := psi_nonneg (vDesign_admissible hP) α
  have hg := gQ_eq_psi_vDesign hP hw α
  have hα0 : 0 ≤ α := le_trans ha0 hα
  have hK0 : 0 ≤ (P.aQ * P.lam) ^ 2 * P.LL ^ 2 := by positivity
  have hQ1 : (1 : ℝ) ≤ P.Q := by linarith [hP.Q_ge]
  have hlogQ : 0 ≤ Real.log P.Q := Real.log_nonneg hQ1
  rw [hg]
  by_cases hin : |α * P.LL| ≤ P.s0
  · have e0 : wOut P (α * P.LL) = 0 := by unfold wOut; rw [if_pos hin]
    rw [e0, mul_zero, zero_mul]
    apply mul_nonneg hK0 (mul_nonneg _ hpsi0)
    unfold koutK
    split_ifs
    · exact mul_nonneg hC0.le hα0
    · exact zero_le_one
    · exact hC0.le
  · have hw' : wOut P (α * P.LL) = shellWt P (2497 / 1500) (α * P.LL) := by unfold wOut; rw [if_neg hin]
    rw [hw']
    unfold shellWt koutK
    by_cases h1 : α * P.LL ≤ Real.log P.Q + 4
    · have hα1 : α ≤ 1 := by
        by_contra hc
        have hc' : 1 < α := lt_of_not_ge hc
        have : P.LL < α * P.LL := by nlinarith
        linarith
      rw [if_pos h1, if_pos hα1]
      apply le_of_eq
      ring
    · have hs0 : 0 < α * P.LL := by linarith
      rw [if_neg h1]
      by_cases h2 : α * P.LL ≤ 2497 / 1500 * P.LL
      · rw [if_pos h2]
        have hα' : α ≤ 2497 / 1500 := le_of_mul_le_mul_right h2 hLL
        have e1 : P.LL / (α * P.LL) * (α * P.LL) = P.LL := div_mul_cancel₀ _ hs0.ne'
        by_cases h3 : α ≤ 1
        · rw [if_pos h3]
          have hCa : 1 ≤ Cfam * α := by
            have h5 : Real.log P.Q + 4 < α * P.LL := lt_of_not_ge h1
            have h6 : P.LL < Cfam * (α * P.LL) := by nlinarith
            have h4 : P.LL * 1 < P.LL * (Cfam * α) := by nlinarith
            exact (lt_of_mul_lt_mul_left h4 hLL.le).le
          have e2 : (P.aQ * P.lam) ^ 2 * P.LL * psi (vDesign P) α * (P.LL / (α * P.LL)) * (α * P.LL)
              = (P.aQ * P.lam) ^ 2 * P.LL ^ 2 * (1 * psi (vDesign P) α) := by
            rw [mul_assoc _ (P.LL / (α * P.LL)), e1]; ring
          rw [e2]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCa hpsi0) hK0
        · rw [if_neg h3, if_pos hα']
          apply le_of_eq
          rw [mul_assoc _ (P.LL / (α * P.LL)), e1]; ring
      · rw [if_neg h2]
        have hα' : ¬ α ≤ 2497 / 1500 := by
          intro hc
          exact h2 (mul_le_mul_of_nonneg_right hc hLL.le)
        have h3 : ¬ α ≤ 1 := by intro hc; exact hα' (by linarith)
        rw [if_neg h3, if_neg hα']
        have e1 : Cfam * P.LL / (α * P.LL) * (α * P.LL) = Cfam * P.LL := div_mul_cancel₀ _ hs0.ne'
        apply le_of_eq
        rw [mul_assoc _ (Cfam * P.LL / (α * P.LL)), e1]; ring

set_option maxHeartbeats 1000000 in
/-- **F1c-3c1.** The kernel identity for the Shell weight, at a design point. -/
theorem kernel_window_at (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (ha0 : 0 ≤ zoneFactor P)
    (ha1 : zoneFactor P ≤ 1) (hb1 : Real.log P.Q + 4 ≤ P.LL) (hbC : P.LL ≤ Cfam * (Real.log P.Q + 4))
    (hlam : 2497 / 1500 ≤ P.lam) :
    (∫ y in P.s0..P.LB, P.gQ y * wOut P y * y)
      ≤ P.LL * (P.aQ * P.LB) ^ 2 / 2 * KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) := by
  have hLL := hP.LL_pos
  have hC0 : (0 : ℝ) < Cfam := by unfold Cfam; positivity
  have hadm := vDesign_admissible hP
  have hpsiI : Integrable (psi (vDesign P)) := psi_integrable hadm
  have hpsi0 : ∀ α, 0 ≤ psi (vDesign P) α := psi_nonneg hadm
  have hal : zoneFactor P ≤ P.lam := by linarith
  have hK20 : 0 ≤ (P.aQ * P.lam) ^ 2 * P.LL ^ 2 := by positivity
  -- change of variables `y = αℒ`
  have hcv : (∫ y in P.s0..P.LB, P.gQ y * wOut P y * y)
      = P.LL * ∫ α in (zoneFactor P)..(P.lam), P.gQ (α * P.LL) * wOut P (α * P.LL) * (α * P.LL) := by
    have h := intervalIntegral.integral_comp_mul_right (fun y => P.gQ y * wOut P y * y) (c := P.LL)
      hLL.ne' (a := zoneFactor P) (b := P.lam)
    rw [h, smul_eq_mul, ← s0_eq_zoneFactor P hP]
    have hLB : P.lam * P.LL = P.LB := rfl
    rw [hLB]
    field_simp
  -- the kernel `kout·ψ` is integrable on `Ioc a λ`
  have hkb : ∀ α ∈ Ioc (zoneFactor P) P.lam, ‖koutK α‖ ≤ Cfam := by
    intro α hα
    have hα0 : 0 ≤ α := le_trans ha0 hα.1.le
    have hC1 : (1 : ℝ) ≤ Cfam := by
      have : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) this.le 4
      unfold Cfam; rw [le_div_iff₀ (by norm_num)]; linarith
    unfold koutK
    split_ifs with h1 h2
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; nlinarith
    · rw [Real.norm_eq_abs, abs_one]; exact hC1
    · rw [Real.norm_eq_abs, abs_of_pos hC0]
  have hkI : IntegrableOn (fun α => koutK α * psi (vDesign P) α) (Ioc (zoneFactor P) P.lam) := by
    refine Integrable.bdd_mul (c := Cfam) hpsiI.integrableOn koutK_measurable.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hkb)
  -- pointwise, then integrate (no integrability of the left side needed)
  have hmono : (∫ α in (zoneFactor P)..(P.lam), P.gQ (α * P.LL) * wOut P (α * P.LL) * (α * P.LL))
      ≤ ∫ α in (zoneFactor P)..(P.lam), (P.aQ * P.lam) ^ 2 * P.LL ^ 2 * (koutK α * psi (vDesign P) α) := by
    rw [intervalIntegral.integral_of_le hal, intervalIntegral.integral_of_le hal]
    apply integral_mono_of_nonneg
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun α hα => ?_)
      have hα0 : 0 ≤ α := le_trans ha0 hα.1.le
      exact mul_nonneg (mul_nonneg (hP.gQ_nonneg hw _) (wOut_nonneg_le hP _).1) (mul_nonneg hα0 hLL.le)
    · exact hkI.const_mul _
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun α hα => ?_)
      exact pointwise_kernel P hP hw ha0 hb1 hbC α hα.1.le
  -- `∫_a^λ kout·ψ ≤ ½ KoutShell`
  have hII : ∀ p q, zoneFactor P ≤ p → p ≤ q → q ≤ P.lam →
      IntervalIntegrable (fun α => koutK α * psi (vDesign P) α) volume p q := by
    intro p q hp hpq hq
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
    exact hkI.mono_set (Ioc_subset_Ioc hp hq)
  have h1l : (1 : ℝ) ≤ 2497 / 1500 := by norm_num
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hII (zoneFactor P) 1 le_rfl ha1 (by linarith)) (hII 1 P.lam ha1 (by linarith) le_rfl)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hII 1 (2497 / 1500) ha1 h1l hlam)
    (hII (2497 / 1500) P.lam (by linarith) hlam le_rfl)
  have hp1 : (∫ α in (zoneFactor P)..1, koutK α * psi (vDesign P) α)
      = Cfam * ∫ α in (zoneFactor P)..1, α * psi (vDesign P) α := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun α hα => ?_
    rw [Set.uIcc_of_le ha1] at hα
    simp only [koutK, if_pos hα.2]
    ring
  have hp2 : (∫ α in (1 : ℝ)..(2497 / 1500), koutK α * psi (vDesign P) α)
      = ∫ α in (1 : ℝ)..(2497 / 1500), psi (vDesign P) α := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun α hα => ?_)
    rw [Set.uIoc_of_le h1l] at hα
    have h3 : ¬ α ≤ 1 := not_le.mpr hα.1
    simp only [koutK, if_neg h3, if_pos hα.2, one_mul]
  have hp3 : (∫ α in (2497 / 1500 : ℝ)..P.lam, koutK α * psi (vDesign P) α)
      = Cfam * ∫ α in (2497 / 1500 : ℝ)..P.lam, psi (vDesign P) α := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun α hα => ?_)
    rw [Set.uIoc_of_le hlam] at hα
    have h4 : ¬ α ≤ 2497 / 1500 := not_le.mpr hα.1
    have h3 : ¬ α ≤ 1 := fun hc => h4 (by linarith)
    simp only [koutK, if_neg h3, if_neg h4]
  have hJ := Jzone_eq_two_interval hadm (psi_even (vDesign P)) ha0 ha1
  have hmid := sym_strip hpsiI (psi_even (vDesign P)) (p := 1) (q := 2497 / 1500) zero_le_one h1l
  have htop := sym_strip hpsiI (psi_even (vDesign P)) (p := 2497 / 1500) (q := P.lam) (by norm_num) hlam
  have htop2 : (∫ α in {α : ℝ | 2497 / 1500 < |α| ∧ |α| ≤ P.lam}, psi (vDesign P) α)
      ≤ ∫ α in {α : ℝ | 2497 / 1500 < |α|}, psi (vDesign P) α := by
    apply setIntegral_mono_set hpsiI.integrableOn
    · exact ae_of_all _ fun α => hpsi0 α
    · exact ae_of_all _ fun α hα => hα.1
  have hkint : (∫ α in (zoneFactor P)..(P.lam), koutK α * psi (vDesign P) α)
      ≤ KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) / 2 := by
    unfold KoutShell
    rw [← hsplit1, ← hsplit2, hp1, hp2, hp3]
    have e1 : (∫ α in (zoneFactor P)..1, α * psi (vDesign P) α) = Jzone (zoneFactor P) (vDesign P) / 2 := by
      rw [hJ]; ring
    have e2 : (∫ α in (1 : ℝ)..(2497 / 1500), psi (vDesign P) α)
        = (∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ 2497 / 1500}, psi (vDesign P) α) / 2 := by rw [hmid]; ring
    have e3 : (∫ α in (2497 / 1500 : ℝ)..P.lam, psi (vDesign P) α)
        = (∫ α in {α : ℝ | 2497 / 1500 < |α| ∧ |α| ≤ P.lam}, psi (vDesign P) α) / 2 := by
      rw [htop]; ring
    rw [e1, e2, e3]
    have := mul_le_mul_of_nonneg_left htop2 hC0.le
    linarith
  have hfin : (∫ α in (zoneFactor P)..(P.lam), (P.aQ * P.lam) ^ 2 * P.LL ^ 2 * (koutK α * psi (vDesign P) α))
      = (P.aQ * P.lam) ^ 2 * P.LL ^ 2 * ∫ α in (zoneFactor P)..(P.lam), koutK α * psi (vDesign P) α :=
    intervalIntegral.integral_const_mul _ _
  rw [hcv]
  have hLBe : P.LB = P.lam * P.LL := rfl
  calc P.LL * (∫ α in (zoneFactor P)..(P.lam), P.gQ (α * P.LL) * wOut P (α * P.LL) * (α * P.LL))
      ≤ P.LL * ((P.aQ * P.lam) ^ 2 * P.LL ^ 2
          * ∫ α in (zoneFactor P)..(P.lam), koutK α * psi (vDesign P) α) := by
        rw [← hfin]; exact mul_le_mul_of_nonneg_left hmono hLL.le
    _ ≤ P.LL * ((P.aQ * P.lam) ^ 2 * P.LL ^ 2
          * (KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hLL.le
        exact mul_le_mul_of_nonneg_left hkint hK20
    _ = P.LL * (P.aQ * P.LB) ^ 2 / 2 * KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) := by
        rw [hLBe]; ring

end F1c
end ShellK
end ZetaShell
