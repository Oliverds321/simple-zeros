/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaQ.Budget
import ZetaQ.RampLink
import ZetaQ.AbelLogPow
import ZetaQ.FrobRow8
import ZetaQ.FrobRow9
import ZetaQ.Row9Numeric

/-! # The Frobenius assembly (`frobenius_row`): parts (A) dictionary, (B′) PP block, (D1) master
inequality with family ends, (D2a) explicit assembly, (D2b) eventual form, (C) zone comparison.

This module is sorry-free. Receipt: `audit/frob_assembly/FrobAssembly_REPORT.md`.
The Frobenius rows 8–9 it consumes live in `ZetaQ/FrobRow8.lean`, `ZetaQ/FrobRow9.lean` and
`ZetaQ/Row9Numeric.lean` (namespaces `ZetaQ.FamRows`, `ZetaQ.Row9Numeric`) and are imported, not
restated here.

Deliverables: `gQ_eq_psi_vDesign`, `B_eq_zoneSplit`, `frobSqGhatFam_le_Mform_add_ends`,
`frobenius_sieve_eventually` (sorry-free since `largeSieveFamily_holds` is discharged from
`ZetaQ/Gallagher.lean`; it inherited `sorryAx` through it before the Gallagher rethread),
`ZoneLipschitzData`, `zone_compare_eventually_of_data` (certified for `Family.qle` in
`ZetaQ/ZoneData.lean`). -/

noncomputable section

open MeasureTheory Set Real
open ZetaQ.Payoff ZetaQ.Zones

namespace ZetaQ
namespace FrobAssembly

variable {P : ParamsQ}

/-! ## A.1 `gQ` as an integral, and its evenness -/

theorem gQ_eq_integral (P : ParamsQ) (y : ℝ) :
    P.gQ y = ∫ u, P.phiQ u ^ 2 * P.phiQ (u + y) ^ 2 := rfl

/-- `psi (vDesign P) α = g(αℒ) / ((λa)² ℒ)`. -/
theorem psi_vDesign_eq_gQ (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (α : ℝ) :
    psi (vDesign P) α = P.gQ (α * P.LL) / ((P.lam * P.aQ) ^ 2 * P.LL) := by
  have hLL : 0 < P.LL := hP.LL_pos
  have hN : 0 < P.lam * P.aQ := mul_pos hP.lam_pos hP.aQ_pos
  have e : ∀ t : ℝ, vDesign P t * vDesign P (t - α)
      = (1 / (P.lam * P.aQ) ^ 2) * (P.phiQ (t * P.LL) ^ 2 * P.phiQ (t * P.LL + (-(α * P.LL))) ^ 2) := by
    intro t
    rw [vDesign_eq hP, vDesign_eq hP]
    have : (t - α) * P.LL = t * P.LL + -(α * P.LL) := by ring
    rw [this]
    field_simp
  unfold psi
  simp_rw [e]
  rw [integral_const_mul]
  have hcomp := MeasureTheory.Measure.integral_comp_mul_right
    (fun u => P.phiQ u ^ 2 * P.phiQ (u + -(α * P.LL)) ^ 2) P.LL

  rw [hcomp, smul_eq_mul, abs_of_pos (inv_pos.mpr hLL)]
  have hg : (∫ u, P.phiQ u ^ 2 * P.phiQ (u + -(α * P.LL)) ^ 2) = P.gQ (α * P.LL) := by
    rw [← hP.gQ_even hw (α * P.LL)]
    rfl
  rw [hg]
  field_simp

/-- **THE DICTIONARY**: `g(αℒ) = (aλ)² ℒ · ψ_{v_design}(α)`. -/
theorem gQ_eq_psi_vDesign (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (α : ℝ) :
    P.gQ (α * P.LL) = (P.aQ * P.lam) ^ 2 * P.LL * psi (vDesign P) α := by
  rw [psi_vDesign_eq_gQ hP hw α]
  have hLL : 0 < P.LL := hP.LL_pos
  have ha : P.aQ ≠ 0 := hP.aQ_pos.ne'
  have hl : P.lam ≠ 0 := hP.lam_pos.ne'
  field_simp

/-! ## A.2 the first-moment integrals -/

/-- `∫ |u| g(u) du = ℒ (aL)² ∫ |α| ψ(α) dα`. -/
theorem integral_abs_gQ_eq (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    ∫ u, |u| * P.gQ u = P.LL * (P.aQ * P.LB) ^ 2 * ∫ α, |α| * psi (vDesign P) α := by
  have hLL : 0 < P.LL := hP.LL_pos
  have hcomp := MeasureTheory.Measure.integral_comp_mul_right (fun u => |u| * P.gQ u) P.LL

  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hLL)] at hcomp
  -- `∫ |αℒ| g(αℒ) dα = ℒ⁻¹ ∫ |u| g(u) du`
  have e : ∀ α : ℝ, |α * P.LL| * P.gQ (α * P.LL)
      = (P.LL * ((P.aQ * P.lam) ^ 2 * P.LL)) * (|α| * psi (vDesign P) α) := by
    intro α
    rw [abs_mul, abs_of_pos hLL, gQ_eq_psi_vDesign hP hw α]
    ring
  simp_rw [e] at hcomp
  rw [integral_const_mul] at hcomp
  have hLB : P.LB = P.lam * P.LL := rfl
  rw [hLB]
  have h2 : (∫ u, |u| * P.gQ u)
      = P.LL * (P.LL * ((P.aQ * P.lam) ^ 2 * P.LL) * ∫ α, |α| * psi (vDesign P) α) := by
    rw [hcomp]; field_simp
  rw [h2]; ring

/-- the zone-restricted version: `∫_{|u|≤s} |u| g = ℒ (aL)² ∫_{|α|≤s/ℒ} |α| ψ`. -/
theorem integral_abs_gQ_Icc_eq (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (s : ℝ) :
    ∫ u in Icc (-s) s, |u| * P.gQ u
      = P.LL * (P.aQ * P.LB) ^ 2 * ∫ α in Icc (-(s / P.LL)) (s / P.LL), |α| * psi (vDesign P) α := by
  have hLL : 0 < P.LL := hP.LL_pos
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
  have hcomp := MeasureTheory.Measure.integral_comp_mul_right
    ((Icc (-s) s).indicator (fun u => |u| * P.gQ u)) P.LL

  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hLL)] at hcomp
  have e : ∀ α : ℝ, (Icc (-s) s).indicator (fun u => |u| * P.gQ u) (α * P.LL)
      = (P.LL * ((P.aQ * P.lam) ^ 2 * P.LL))
          * (Icc (-(s / P.LL)) (s / P.LL)).indicator (fun α => |α| * psi (vDesign P) α) α := by
    intro α
    have hmem : α * P.LL ∈ Icc (-s) s ↔ α ∈ Icc (-(s / P.LL)) (s / P.LL) := by
      simp only [mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← neg_div, div_le_iff₀ hLL]; linarith, by rw [le_div_iff₀ hLL]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← neg_div, div_le_iff₀ hLL] at h1; linarith, by rwa [le_div_iff₀ hLL] at h2⟩
    by_cases h : α ∈ Icc (-(s / P.LL)) (s / P.LL)
    · rw [indicator_of_mem h, indicator_of_mem (hmem.mpr h)]
      rw [abs_mul, abs_of_pos hLL, gQ_eq_psi_vDesign hP hw α]
      ring
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.mp h'))]
      ring
  simp_rw [e] at hcomp
  rw [integral_const_mul] at hcomp
  have hLB : P.LB = P.lam * P.LL := rfl
  rw [hLB]
  have h2 : (∫ u, (Icc (-s) s).indicator (fun u => |u| * P.gQ u) u)
      = P.LL * (P.LL * ((P.aQ * P.lam) ^ 2 * P.LL)
          * ∫ α, (Icc (-(s / P.LL)) (s / P.LL)).indicator (fun α => |α| * psi (vDesign P) α) α) := by
    rw [hcomp]; field_simp
  rw [h2]; ring

/-- `∫ |u| g(u) du = 2 ∫_0^L g(y) y dy` (evenness and the support `|y| ≤ L`). -/
theorem integral_abs_gQ_eq_two_interval (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    ∫ u, |u| * P.gQ u = 2 * ∫ y in (0:ℝ)..P.LB, P.gQ y * y := by
  have hgcont : Continuous P.gQ := hP.gQ_continuous hw
  have hLB : 0 < P.LB := hP.LB_pos
  have hint : Integrable (fun u => |u| * P.gQ u) := by
    have hcs : HasCompactSupport P.gQ := hP.gQ_hasCompactSupport hw
    exact (continuous_abs.mul hgcont).integrable_of_hasCompactSupport (hcs.mul_left)
  have heven : ∀ u, |(-u)| * P.gQ (-u) = |u| * P.gQ u := by
    intro u; rw [abs_neg, hP.gQ_even hw]
  -- split at 0
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Ioi (a := (0 : ℝ))) hint
  rw [Set.compl_Ioi] at hsplit
  have hneg : ∫ u in Iic (0 : ℝ), |u| * P.gQ u = ∫ u in Ioi (0 : ℝ), |u| * P.gQ u := by
    rw [show (0 : ℝ) = -0 by ring, ← integral_comp_neg_Ioi]
    simp only [neg_zero]
    congr 1; funext u; exact heven u
  have hIoi : ∫ u in Ioi (0 : ℝ), |u| * P.gQ u = ∫ y in (0:ℝ)..P.LB, P.gQ y * y := by
    rw [← integral_Ici_eq_integral_Ioi]
    have hgz : ∀ y : ℝ, P.LB ≤ y → P.gQ y = 0 := by
      intro y hy
      have hy0 : (0 : ℝ) ≤ y := le_trans hLB.le hy
      exact hP.gQ_eq_zero hw (by rw [abs_of_nonneg hy0]; exact hy)
    have h1 : ∫ u in Ici (0 : ℝ), |u| * P.gQ u = ∫ u in Ici (0 : ℝ), u * P.gQ u := by
      refine setIntegral_congr_fun measurableSet_Ici fun u hu => ?_
      simp only [mem_Ici] at hu
      simp only [abs_of_nonneg hu]
    have hint2 : Integrable (fun u : ℝ => u * P.gQ u) := by
      have hcs : HasCompactSupport P.gQ := hP.gQ_hasCompactSupport hw
      exact (continuous_id.mul hgcont).integrable_of_hasCompactSupport (hcs.mul_left)
    have hsplit2 : Ici (0:ℝ) = Icc 0 P.LB ∪ Ioi P.LB := by
      ext y
      simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
      constructor
      · intro h
        rcases le_or_gt y P.LB with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'
      · rintro (⟨h, _⟩ | h)
        · exact h
        · linarith
    have hdisj : Disjoint (Icc (0:ℝ) P.LB) (Ioi P.LB) := by
      rw [Set.disjoint_left]
      rintro x ⟨_, h1⟩ h2
      simp only [mem_Ioi] at h2
      linarith
    rw [h1, hsplit2, setIntegral_union hdisj measurableSet_Ioi hint2.integrableOn hint2.integrableOn]
    have h0 : ∫ u in Ioi P.LB, u * P.gQ u = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      simp only [mem_Ioi] at hu
      rw [hgz u hu.le, mul_zero]
    rw [h0, add_zero, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hLB.le]
    exact intervalIntegral.integral_congr (fun y _ => mul_comm y (P.gQ y))
  linarith

/-- **`∫_0^L g(y) y dy = ½ ℒ (aL)² (K0 + K1)(v_design)`** — the Mertens main term of
`sumA2gQ` (`Zones.sumA2gQ_close`) in §11's vocabulary. -/
theorem intervalIntegral_gQ_mul_eq (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    ∫ y in (0:ℝ)..P.LB, P.gQ y * y
      = P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2 := by
  rw [K0_add_K1 (vDesign_admissible hP), ← integral_abs_gQ_eq hP hw,
    integral_abs_gQ_eq_two_interval hP hw]
  ring

/-! ## A.3 the kernel split at an arbitrary zone edge `a` -/

/-- `∫_{|α| ≤ a} |α| ψ`. -/
def K0a (a : ℝ) (v : ℝ → ℝ) : ℝ := ∫ α in Icc (-a) a, |α| * psi v α

/-- `∫_{|α| > a} |α| ψ`. -/
def K1a (a : ℝ) (v : ℝ → ℝ) : ℝ := ∫ α in {α : ℝ | a < |α|}, |α| * psi v α

/-- the strip `a < |α| ≤ 1`. -/
def Jzone (a : ℝ) (v : ℝ → ℝ) : ℝ := ∫ α in {α : ℝ | a < |α| ∧ |α| ≤ 1}, |α| * psi v α

theorem compl_Icc_eq (a : ℝ) : (Icc (-a) a)ᶜ = {α : ℝ | a < |α|} := by
  ext x
  simp only [mem_compl_iff, mem_Icc, mem_setOf_eq, not_and_or, not_le]
  rcases abs_cases x with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [e]
  · exact ⟨fun h => by rcases h with h | h <;> linarith, fun h => Or.inr (by linarith)⟩
  · exact ⟨fun h => by rcases h with h | h <;> linarith, fun h => Or.inl (by linarith)⟩

theorem measurableSet_gt_abs (a : ℝ) : MeasurableSet {α : ℝ | a < |α|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

theorem measurableSet_strip (a : ℝ) : MeasurableSet {α : ℝ | a < |α| ∧ |α| ≤ 1} :=
  (measurableSet_gt_abs a).inter (measurableSet_le continuous_abs.measurable measurable_const)

theorem K0_eq_K0a_one (v : ℝ → ℝ) : K0 v = K0a 1 v := rfl
theorem K1_eq_K1a_one (v : ℝ → ℝ) : K1 v = K1a 1 v := rfl

theorem K0a_add_K1a {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (a : ℝ) :
    K0a a v + K1a a v = ∫ α, |α| * psi v α := by
  have hsplit := integral_add_compl (measurableSet_Icc (a := (-a)) (b := a))
    (absPsi_integrable hv)
  rw [K0a, K1a, ← compl_Icc_eq]
  exact hsplit

/-- `K1a a = Jzone a + K1` for `a ≤ 1`. -/
theorem K1a_eq_Jzone_add_K1 {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) {a : ℝ}
    (ha : a ≤ 1) : K1a a v = Jzone a v + K1 v := by
  have hint := absPsi_integrable hv
  have hU : {α : ℝ | a < |α|} = {α : ℝ | a < |α| ∧ |α| ≤ 1} ∪ {α : ℝ | 1 < |α|} := by
    ext x
    simp only [mem_setOf_eq, mem_union]
    constructor
    · intro h
      rcases le_or_gt |x| 1 with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr h1
    · rintro (⟨h, _⟩ | h)
      · exact h
      · linarith
  have hdisj : Disjoint {α : ℝ | a < |α| ∧ |α| ≤ 1} {α : ℝ | 1 < |α|} := by
    rw [Set.disjoint_left]
    rintro x ⟨_, h1⟩ h2
    simp only [mem_setOf_eq] at h2
    linarith
  rw [K1a, hU, setIntegral_union hdisj (measurableSet_gt_abs 1) hint.integrableOn hint.integrableOn]
  rfl

/-- `K0 = K0a a + Jzone a` for `0 ≤ a ≤ 1`. -/
theorem K0_eq_K0a_add_Jzone {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ 1) : K0 v = K0a a v + Jzone a v := by
  have h1 := K0a_add_K1a hv a
  have h2 := K0a_add_K1a hv 1
  rw [K1a_eq_Jzone_add_K1 hv ha] at h1
  rw [← K0_eq_K0a_one, ← K1_eq_K1a_one] at h2
  linarith

/-- **THE ZONE SPLIT OF `B`**: for `0 ≤ a ≤ 1`,
`K0a a + C·K1a a = K0 + C·K1 + (C − 1)·∫_{a<|α|≤1}|α|ψ`, hence
`B C v = ψ(0) + K0a a v + C·K1a a v − (C − 1)·Jzone a v`. -/
theorem K0a_add_mul_K1a {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (C : ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ 1) :
    K0a a v + C * K1a a v = K0 v + C * K1 v + (C - 1) * Jzone a v := by
  rw [K1a_eq_Jzone_add_K1 hv ha, K0_eq_K0a_add_Jzone hv ha0 ha]
  ring

theorem B_eq_zoneSplit {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (C : ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a ≤ 1) :
    B C v = psi v 0 + K0a a v + C * K1a a v - (C - 1) * Jzone a v := by
  rw [B_eq_Bgen C hv, Bgen]
  have h := K0a_add_mul_K1a hv C ha0 ha
  linarith

/-- `Jzone a v ≥ 0`, `K1a ≥ 0`, `K0a ≥ 0` for admissible `v`. -/
theorem Jzone_nonneg {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (a : ℝ) : 0 ≤ Jzone a v :=
  setIntegral_nonneg (measurableSet_strip a) fun x _ => mul_nonneg (abs_nonneg x) (psi_nonneg hv x)

theorem K1a_nonneg {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (a : ℝ) : 0 ≤ K1a a v :=
  setIntegral_nonneg (measurableSet_gt_abs a) fun x _ => mul_nonneg (abs_nonneg x) (psi_nonneg hv x)

theorem K0a_nonneg {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (a : ℝ) : 0 ≤ K0a a v :=
  setIntegral_nonneg measurableSet_Icc fun x _ => mul_nonneg (abs_nonneg x) (psi_nonneg hv x)

/-- `Jzone a v = 2 ∫_a^1 α ψ(α) dα` for EVEN `v` (hence even `ψ`) — the form in which the
zone comparison of part (C) is stated. Proved for `vProfile`/`vDesign` via evenness below. -/
theorem Jzone_eq_two_interval {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v)
    (heven : ∀ α, psi v (-α) = psi v α) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1) :
    Jzone a v = 2 * ∫ α in a..1, α * psi v α := by
  have hint := absPsi_integrable hv
  have hS : {α : ℝ | a < |α| ∧ |α| ≤ 1} = Ioc a 1 ∪ Ico (-1) (-a) := by
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
  have hdisj : Disjoint (Ioc a 1) (Ico (-1) (-a)) := by
    rw [Set.disjoint_left]
    rintro x ⟨h1, _⟩ ⟨_, h2⟩
    linarith
  rw [Jzone, hS, setIntegral_union hdisj measurableSet_Ico hint.integrableOn hint.integrableOn]
  have hpos : ∫ α in Ioc a 1, |α| * psi v α = ∫ α in a..1, α * psi v α := by
    rw [intervalIntegral.integral_of_le ha]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [mem_Ioc] at hx
    simp only [abs_of_pos (lt_of_le_of_lt ha0 hx.1)]
  have hneg : ∫ α in Ico (-1) (-a), |α| * psi v α = ∫ α in a..1, α * psi v α := by
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : (-1:ℝ) ≤ -a),
      ← intervalIntegral.integral_comp_neg (fun α => |α| * psi v α)]
    rw [intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le ha]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [mem_Ioc] at hx
    simp only [abs_neg, heven, abs_of_pos (lt_of_le_of_lt ha0 hx.1)]
  rw [hpos, hneg]
  ring


/-! ###################### PART B ###################### -/
/-! ## B.1 side conditions -/

theorem IwinQ_eq (P : ParamsQ) : P.IwinQ = Icc P.T (2 * P.T) := rfl

/-- `Fwin P u` is continuous for continuous `u` (dominated convergence on the compact window). -/
theorem Fwin_continuous (P : ParamsQ) {u : ℝ → ℝ} (hu : Continuous u) :
    Continuous (Fwin P u) := by
  unfold Fwin
  have hbound : Integrable (fun τ => |u τ|) (volume.restrict P.IwinQ) := by
    rw [IwinQ_eq]
    exact (hu.abs.integrableOn_Icc)
  refine continuous_of_dominated (bound := fun τ => |u τ|) ?_ ?_ hbound ?_
  · intro s
    apply Continuous.aestronglyMeasurable
    fun_prop
  · intro s
    refine Filter.Eventually.of_forall fun τ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖Complex.exp (Complex.I * (τ : ℂ) * (s : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [this, mul_one]
  · refine Filter.Eventually.of_forall fun τ => ?_
    fun_prop

theorem PXchi_continuous (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (PXchi P χ) :=
  Zeta23.ThmE.PXc_continuous _ (Real.exp_pos _)

theorem PXchi_integrableOn (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    IntegrableOn (PXchi P χ) P.IwinQ := by
  rw [IwinQ_eq]; exact (PXchi_continuous P χ).integrableOn_Icc

theorem PXchi_sq_integrableOn (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    IntegrableOn (fun τ => PXchi P χ τ ^ 2) P.IwinQ := by
  rw [IwinQ_eq]; exact ((PXchi_continuous P χ).pow 2).integrableOn_Icc

theorem gQ_Fwin_PXchi_integrableOn (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    IntegrableOn (fun s => P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) Set.univ :=
  (gQ_mul_integrable P hP hw ((Fwin_continuous P (PXchi_continuous P χ)).norm.pow 2)).integrableOn

theorem regimeQ_of (hP : P.Valid) (hL : (8 : ℝ) ≤ P.LB) : RegimeQ P :=
  ⟨hL, hP.one_le_w, hP.T_pos, hP.Q_ge⟩

/-! ## B.2 the POINTWISE `ρ_ℝ` bound (the family-free form of `Zones.rhoU_univ_le_family`) -/

/-- `ρ_ℝ ≤ √(48/π)·√(2/T)` at every design point with `L ≥ max 8 (342C)`, `T ≥ T_ρ(c₀)`. -/
theorem rhoU_univ_le_pointwise (c₀ : ℝ) :
    ∃ Lρ Tρ : ℝ, ∀ P : ParamsQ, P.Valid → 8 * P.w ≤ P.LB → P.cWin ≤ c₀ →
      Lρ ≤ P.LB → Tρ ≤ P.T →
      rhoU P Set.univ ≤ rhoConstConservative * Real.sqrt (2 / P.T) := by
  obtain ⟨Cs, hCs0, hdiag⟩ := lemma43_diagonal c₀
  obtain ⟨C, hC0, hmom⟩ := sumA2gQ_ge_first_moment_margin
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  obtain ⟨C₃, hC₃def⟩ : ∃ x : ℝ, x = 1 / 2 + (2 * (Real.log 4 + 4) + 1537 / Real.log 2) / 8 :=
    ⟨_, rfl⟩
  have hC₃0 : (0 : ℝ) < C₃ := by
    have h1 : (0 : ℝ) < 1537 / Real.log 2 := div_pos (by norm_num) hlog2
    rw [hC₃def]; linarith
  refine ⟨max 8 (342 * C), 57 * (30 * C₃ + 5 * C + 6 * Cs * C₃), ?_⟩
  intro P hv hw hcr hLbig hTbig
  have hL8 : (8 : ℝ) ≤ P.LB := le_trans (le_max_left _ _) hLbig
  have hreg : RegimeQ P := regimeQ_of hv hL8
  have hLC : 342 * C ≤ P.LB := le_trans (le_max_right _ _) hLbig
  have hTpos : (0 : ℝ) < P.T := hv.T_pos
  have hLpos : (0 : ℝ) < P.LB := by linarith
  obtain ⟨Esm, hEsm, hdg⟩ := hdiag P hv hreg hw hcr
  have hSpos : (0:ℝ) < sumA2gQ P := by
    have h := sumA2gQ_lower_const P hv hreg hw
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have h6 : (0:ℝ) < 6 - Real.log 2 := by linarith
    have hpos : (0:ℝ) < Real.log 2 ^ 2 / 2 * (6 - Real.log 2) / 1296 := by positivity
    linarith
  have hlow : P.T * P.LB * (∫ s in Set.Ici (0:ℝ), P.gQ s)
      ≤ 12 * Real.pi * ∫ s in Set.Ici (0:ℝ), P.gQ s * normA2 P s := by
    refine halfline_low_arith (C := C) (C₃ := C₃) (Cs := Cs)
      (Bp := ∫ s in Set.Ici (0:ℝ), P.gQ s * normB2 P s)
      hC0 hC₃0 hCs0 hL8 hLC hTpos hTbig ?_ hSpos ?_ ?_ ?_ hEsm ?_
    · exact setIntegral_nonneg measurableSet_Ici fun s _ => lemma42_g_nonneg P s
    · exact hmom P hv hw hL8
    · rw [hC₃def]; exact sumA2gQ_le_cubic P hv hw hL8
    · exact halfline_normB2_le P hv hw (by linarith)
    · exact (diagonal_halfline_split P hv hw).symm.trans hdg
  obtain ⟨hintA, hintB, hintK, hintJ, hintg, -⟩ := rho_integrability P hv hw
  have h := rhoU_univ_le_conservative_of_halfline P hTpos hLpos hintA hintB hintK
    hintJ.integrableOn hintg.integrableOn hlow
  have hS := supNormBSum_le P hLpos.le
  have hTL : (0:ℝ) < P.T * P.LB := mul_pos hTpos hLpos
  have harg : supNormBSum P / (P.T * P.LB) ≤ 2 / P.T := by
    rw [div_le_div_iff₀ hTL hTpos]
    nlinarith [mul_le_mul_of_nonneg_right (show supNormBSum P ≤ 2 * P.LB by linarith) hTpos.le]
  have hcc : (0:ℝ) ≤ rhoConstConservative := Real.sqrt_nonneg _
  calc rhoU P Set.univ ≤ rhoConstConservative * Real.sqrt (supNormBSum P / (P.T * P.LB)) := h
    _ ≤ rhoConstConservative * Real.sqrt (2 / P.T) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg) hcc

/-! ## B.3 the PP block, sieve on both zones, in §11's vocabulary -/

/-- **The PP block, pointwise, with `C` on both zones.**
`Σ_{χ∈𝔉_Q} 𝓜[P_χ,P_χ] ≤ Q²(T/π)·(½ℒ(aL)²(K0+K1)(v_design) + C_M L²)·(1+4Q^{−δ})(1+ρ_ℝ)(1+Cs/T)`
at every valid design point with `8w ≤ L`, `8 ≤ L`, `c_W ≤ c₀`, `X ≤ Q^{2−δ}` (`0 < δ ≤ 2`),
`T > Cs`, `Qn ≤ ⌊Q⌋₊`. `Cs = Cs(c₀)` is `lemma43_diagonal`'s smearing constant, `C_M` the
Mertens constant of `Zones.sumA2gQ_close`. -/
theorem famPP_le_sieve (c₀ : ℝ) :
    ∃ Cs CM : ℝ, 0 < Cs ∧ 0 < CM ∧
      ∀ (P : ParamsQ) (δ : ℝ) (F : Family) (Qn : ℕ), P.Valid → 8 * P.w ≤ P.LB →
        (8 : ℝ) ≤ P.LB → P.cWin ≤ c₀ → 0 < δ → δ ≤ 2 → P.XQ ≤ Real.rpow P.Q (2 - δ) →
        Cs < P.T → Qn ≤ ⌊P.Q⌋₊ →
        familySum F Qn (fun _q χ => Mform P (PXchi P χ) (PXchi P χ))
          ≤ P.Q ^ 2 * (P.T / Real.pi)
              * (P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2
                  + CM * P.LB ^ 2)
              * ((1 + 4 * Real.rpow P.Q (-δ)) * (1 + rhoU P Set.univ) * (1 + Cs / P.T)) := by
  obtain ⟨Cs, hCs0, hpt⟩ := lemma43_family_le_C_diagonal_pointwise c₀
  obtain ⟨CM, hCM0, hclose⟩ := sumA2gQ_close
  refine ⟨Cs, CM, hCs0, hCM0, ?_⟩
  intro P δ F Qn hP hw hL8 hcr hδ0 hδ2 hXQ hTCs hQn
  have hreg : RegimeQ P := regimeQ_of hP hL8
  have hphi := phiQ_sq_integrable P hP hw
  obtain ⟨-, -, hintK, -, -, hintAB⟩ := rho_integrability P hP hw
  have h1 := familySum_Mform_PP_le_famSum P F Qn hQn hphi (fun q χ => PXchi_integrableOn P χ)
    (fun q χ => PXchi_sq_integrableOn P χ)
  have h2 := hpt P δ hP hreg hw hcr largeSieveFamily_holds hδ0 hδ2 hXQ hTCs
    (fun q χ => PXchi_integrableOn P χ) (fun q χ => PXchi_sq_integrableOn P χ)
    hintAB.integrableOn (fun q χ => gQ_Fwin_PXchi_integrableOn hP hw χ) hintK.integrableOn
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  rw [famConstQ_mul_famDiagonal P hQ3] at h2
  have hsum := hclose P hP hw hL8
  have hsum' : sumA2gQ P ≤ (∫ y in (0:ℝ)..P.LB, P.gQ y * y) + CM * P.LB ^ 2 := by
    linarith [(abs_le.mp hsum).2]
  rw [FrobAssembly.intervalIntegral_gQ_mul_eq hP hw] at hsum'
  have hfac : (0 : ℝ) ≤ (1 + 4 * Real.rpow P.Q (-δ)) * (1 + rhoU P Set.univ) * (1 + Cs / P.T) := by
    have hrp0 : (0:ℝ) ≤ Real.rpow P.Q (-δ) := Real.rpow_nonneg (by linarith) _
    have hrho0 : (0:ℝ) ≤ rhoU P Set.univ := rhoU_nonneg P Set.univ MeasurableSet.univ
    have hT0 : (0:ℝ) < P.T := hP.T_pos
    have : (0:ℝ) ≤ Cs / P.T := div_nonneg hCs0.le hT0.le
    positivity
  have hQT : (0 : ℝ) ≤ P.Q ^ 2 * (P.T / Real.pi) := by
    have hT0 : (0:ℝ) < P.T := hP.T_pos
    positivity
  calc familySum F Qn (fun _q χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ famSum P (fun _q χ => Mform P (PXchi P χ) (PXchi P χ)) := h1
    _ ≤ P.Q ^ 2 * (P.T / Real.pi) * sumA2gQ P
          * ((1 + 4 * Real.rpow P.Q (-δ)) * (1 + rhoU P Set.univ) * (1 + Cs / P.T)) := h2
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hfac
        exact mul_le_mul_of_nonneg_left hsum' hQT

/-! ###################### SHARED DEFINITIONS (D) ###################### -/

section SharedDefs
open Zeta23.PrimeSide Zeta23.ThmE ZetaQ.Ends

/-- the family ends majorant (Lemma 8.2 at the family constant), in hat units. -/
def endsMaj (P : ParamsQ) : ℝ :=
  ((P.aQ * P.LB ^ 2)⁻¹) ^ 2
    * ((c1Ends * P.Q) ^ 2 * (P.LB ^ 3 * (P.LB + Zeta23.l P.T) * (P.LL + C0Ends) ^ 2
        * (C1ends P.cWin + C2ends P.cWin * (1 + Real.log P.LB))))

/-- the closed-form row-9 majorant as a function of `(Q, l, L)`.

**The leading `3`** is `FamRows.famMform_muP_le`'s parity factor. `ROW9par ≤ ROW9` is
false for large `Q` (the parity `log q`-weighted coefficient carries a `τ(n+1)` kernel that
`ROW9` has not budgeted), so row 9 is proved at `3·ROW9` in all six branches and the constant
is absorbed HERE, in the majorant's definition, rather than propagated through
`frobSq_le_explicit` / `A3_eventually`: those statements mention only `R9closed` and are
therefore unchanged. The only proof that notices is `R9fun_eventually`, which now applies
`Row9Numeric.row9_closed_eventually` at `c/3`. -/
def R9fun (Q l L : ℝ) : ℝ :=
  3 * (24 / Real.pi * Q * L * Real.sqrt (Real.exp L) * (1 + Real.log Q) * (1 + L)
    + 8 / Real.pi * (44 * l + 24) * L * Real.sqrt (Real.exp L) * (3 / 4 * Q * (10 + 6 * L) + 2))

/-- the closed-form row-9 majorant (`FamRows.famMform_muP_le_closed`'s right-hand side). -/
def R9closed (P : ParamsQ) (Qn : ℕ) : ℝ := R9fun (Qn : ℝ) (Zeta23.l P.T) P.LB

/-- the sieve-on-both-zones PP majorant (`famPP_le_sieve`'s right-hand side). -/
def PPsieve (Cs CM δ : ℝ) (P : ParamsQ) : ℝ :=
  P.Q ^ 2 * (P.T / Real.pi)
    * (P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2 + CM * P.LB ^ 2)
    * ((1 + 4 * Real.rpow P.Q (-δ)) * (1 + rhoU P Set.univ) * (1 + Cs / P.T))

theorem T_ge_two_pi {P : ParamsQ} (hP : P.Valid) : 2 * Real.pi ≤ P.T := by
  linarith [hP.T_ge300, Real.pi_lt_four]

/-- the ends constant of a window constant `c`: `endsMaj ≤ Kends c · Q² ℒ³`. -/
def Kends (c : ℝ) : ℝ := 0.861 * (C1ends c + 3 * C2ends c)

end SharedDefs
/-! ###################### PART D1 ######################
The per-character `NuBound` for `ν_χ = μ_χ + P_{X,χ}` (crude `B`, for INTEGRABILITY only), the
exact decomposition `a²L⁴‖Ĝ(χ)‖²_F = L²𝓜[ν_χ,ν_χ] + 𝓔₁(χ) + 𝓔₂(χ)` (`Zeta23.PrimeSide.decomp`),
and the family master inequality with the ends error at the FAMILY constant of
`Ends.ends_family_bound` (Lemma 8.1′ `hsep` threaded, D18 pattern). -/

section PartD1

open Zeta23.PrimeSide Zeta23.ThmE ZetaQ.Ends

/-- the crude sup of `|P_{X,χ}|`: `(1/π)·Σ_{n≤X} Λ(n)/√n`. -/
def PXsup (P : ParamsQ) : ℝ :=
  (1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n

theorem PXsup_nonneg (P : ParamsQ) : 0 ≤ PXsup P := by
  unfold PXsup
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => ?_)
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- `|P_{X,c}(τ)| ≤ (1/π) Σ_{n≤X} Λ(n)/√n` for `‖c n‖ ≤ 1`. -/
theorem abs_PXc_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (X τ : ℝ) :
    |PXc c X τ| ≤ (1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n := by
  unfold PXc
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    Complex.norm_natCast_cpow_of_pos hn0]
  have hre : (-(1 / 2 : ℂ) - Complex.I * (τ : ℂ)).re = -(1 / 2 : ℝ) := by simp
  rw [hre, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  have h1 := hc n
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  calc (ArithmeticFunction.vonMangoldt n : ℝ) * ‖c n‖ * (Real.sqrt (n : ℝ))⁻¹
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * (Real.sqrt (n : ℝ))⁻¹ := by gcongr
    _ = (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n := by ring

/-- `log(|τ|+1) ≤ log(4T+1) + log⁺(|τ|/4T)` for `T > 0`. -/
theorem log_abs_add_one_le (T τ : ℝ) (hT : 0 < T) :
    Real.log (|τ| + 1) ≤ Real.log (4 * T + 1) + max (Real.log (|τ| / (4 * T))) 0 := by
  have h4 : (0:ℝ) < 4 * T := by positivity
  have hmax : (0:ℝ) ≤ max (Real.log (|τ| / (4 * T))) 0 := le_max_right _ _
  rcases le_or_gt |τ| (4 * T) with h | h
  · have : Real.log (|τ| + 1) ≤ Real.log (4 * T + 1) :=
      Real.log_le_log (by linarith [abs_nonneg τ]) (by linarith)
    linarith
  · have hτ0 : 0 < |τ| := by linarith
    have hq : 1 ≤ |τ| / (4 * T) := by rw [le_div_iff₀ h4]; linarith
    have hle : |τ| + 1 ≤ |τ| / (4 * T) * (4 * T + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h4]; nlinarith
    calc Real.log (|τ| + 1) ≤ Real.log (|τ| / (4 * T) * (4 * T + 1)) :=
          Real.log_le_log (by linarith) hle
      _ = Real.log (|τ| / (4 * T)) + Real.log (4 * T + 1) :=
          Real.log_mul (by positivity) (by positivity)
      _ ≤ _ := by linarith [le_max_left (Real.log (|τ| / (4 * T))) 0]

/-- the crude per-character `NuBound` constant for `ν_χ`. -/
def Bnu (P : ParamsQ) (q : ℕ) : ℝ :=
  (Real.log q + Real.log (4 * P.T + 1)) / (2 * Real.pi) + (10 / Real.pi + 1) + PXsup P

theorem Bnu_nonneg (hP : P.Valid) {q : ℕ} (hq : 1 ≤ q) : 0 ≤ Bnu P q := by
  unfold Bnu
  have h1 : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have h2 : 0 ≤ Real.log (4 * P.T + 1) := Real.log_nonneg (by linarith [hP.T_pos])
  have h3 := PXsup_nonneg P
  positivity

/-- **`NuBound` for `ν_χ` at the crude constant** (integrability-grade; NOT a quantitative
input — the quantitative ends bound is Lemma 8.1′'s family envelope). -/
theorem nuQ_nuBound (hP : P.Valid) {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    NuBound (toSetting P) (Bnu P q) (nuQ P q χ) := by
  intro τ
  have hT : 0 < P.T := hP.T_pos
  have hTs : (toSetting P).T = P.T := rfl
  rw [hTs]
  have hμ := MuqUniform.muq_abs_le_global (parity_le_one χ) hq τ
  have hPX := abs_PXc_le (fun n => χ (n : ZMod q)) (fun n => χ.norm_le_one _) P.XQ τ
  have hlog := log_abs_add_one_le P.T τ hT
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmax : (0:ℝ) ≤ max (Real.log (|τ| / (4 * P.T))) 0 := le_max_right _ _
  have hinv : (1:ℝ) / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have hsplit : nuQ P q χ τ = muq (parity χ) q τ + PXc (fun n => χ (n : ZMod q)) P.XQ τ := rfl
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  unfold Bnu PXsup
  have hmono : (Real.log q + Real.log (|τ| + 1)) / (2 * Real.pi)
      ≤ (Real.log q + Real.log (4 * P.T + 1)) / (2 * Real.pi)
        + max (Real.log (|τ| / (4 * P.T))) 0 := by
    rw [add_div, add_div]
    have : Real.log (|τ| + 1) / (2 * Real.pi)
        ≤ Real.log (4 * P.T + 1) / (2 * Real.pi) + max (Real.log (|τ| / (4 * P.T))) 0 := by
      rw [div_le_iff₀ (by positivity)]
      have h2π : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      nlinarith [Real.log_le_log (by positivity : (0:ℝ) < 1) (le_refl (1:ℝ)),
        div_mul_cancel₀ (Real.log (4 * P.T + 1)) (by positivity : (2 * Real.pi) ≠ 0)]
    linarith
  linarith

/-! ### the per-character decomposition -/

theorem muq_continuous (κ : ℕ) (hκ : κ ≤ 1) (q : ℕ) : Continuous (muq κ q) := by
  have h1 : Continuous (muq κ 1) :=
    (Zeta23.ThmE.GammaChi.gammaFactsChi hκ le_rfl).smooth.continuous
  have he : muq κ q = fun τ => muq κ 1 τ + (muq κ q 0 - muq κ 1 0) := by
    funext τ
    have := MuqUniform.muq_sub_eq κ q τ 0
    linarith
  rw [he]
  exact h1.add continuous_const

theorem muDensity_continuous (q : ℕ) {r : ℕ} (χ : DirichletCharacter ℂ r) :
    Continuous (muDensity q χ) :=
  muq_continuous (parity χ) (parity_le_one χ) q

theorem nuQ_continuous (P : ParamsQ) (q : ℕ) (χ : DirichletCharacter ℂ q) :
    Continuous (nuQ P q χ) := by
  have : nuQ P q χ = fun τ => muDensity q χ τ + PXchi P χ τ := by
    funext τ; exact nuQ_eq_muDensity_add_PXchi P q χ τ
  rw [this]
  exact (muDensity_continuous q χ).add (PXchi_continuous P χ)

theorem nuFam_continuous (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (nuFam P.XQ χ) := by
  have : nuFam P.XQ χ = nuQ P q χ := by funext τ; exact nuFam_eq_nuQ P q χ τ
  rw [this]; exact nuQ_continuous P q χ

/-- **the per-character decomposition, in certificate vocabulary**:
`a²L⁴·‖Ĝ(χ)‖²_F = L²·𝓜[ν_χ,ν_χ] + 𝓔₁(χ) + 𝓔₂(χ)`. -/
theorem frobSq_char_decomp (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (hl : 1 ≤ Zeta23.l P.T)
    (hX : 1 ≤ P.XQ) {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    P.aQ ^ 2 * P.LB ^ 4 * RHLinalg.frobSq (hatQ P (gridGram P χ))
      = P.LB ^ 2 * Mform P (nuQ P q χ) (nuQ P q χ)
        + calE1 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)
        + calE2 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ) := by
  have hlne : Zeta23.l P.T ≠ 0 := by intro h0; rw [h0] at hl; linarith
  have hF := S2_localHypsCoreW P hP (by linarith) hl hX
  have hdec := decomp (nuQ_continuous P q χ) hF (nuQ_nuBound hP hq χ) (Bnu_nonneg hP hq)
    (by show 2 * Real.pi ≤ P.T; exact T_ge_two_pi hP)
  rw [sum_GentryNu_sq_eq P hlne χ, MtotalNu_eq_Mform P χ, S1_toSetting_L P hlne] at hdec
  rw [frobSq_hatQ_gridGram_entrywise P χ]
  have ha : P.aQ ≠ 0 := hP.aQ_pos.ne'
  have hL : P.LB ≠ 0 := hP.LB_pos.ne'
  have e : P.aQ ^ 2 * P.LB ^ 4 * (((P.aQ * P.LB ^ 2)⁻¹) ^ 2
      * ∑ k : Fin P.dQ, ∑ l : Fin P.dQ, gridGramEntry P χ (k : ℕ) (l : ℕ) ^ 2)
      = ∑ k : Fin P.dQ, ∑ l : Fin P.dQ, gridGramEntry P χ (k : ℕ) (l : ℕ) ^ 2 := by
    field_simp
  rw [e]
  linarith [hdec]

theorem moduli_subset_Icc (F : Family) (Qn : ℕ) : F.moduli Qn ⊆ Finset.Icc 1 Qn := by
  cases F <;>
    · intro q hq
      simp only [Family.moduli, Finset.mem_Ioc, Finset.mem_Icc] at hq ⊢
      omega

/-- **THE MASTER INEQUALITY, family ends constant** (the analogue of
`Zones.frobSqGhatFam_le_master` with the per-character `NuBound·B²` error replaced by Lemma
8.2's family bound, `hsep` = Lemma 8.1′ threaded):
`‖Ĝ_fam‖²_F ≤ (a²L²)⁻¹·Σ_χ 𝓜[ν_χ,ν_χ] + endsMaj`. -/
theorem frobSqGhatFam_le_Mform_add_ends (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    (hl : 1 ≤ Zeta23.l P.T) (hX : 1 ≤ P.XQ) (F : Family) (Qn : ℕ)
    (hT1 : (2 * Real.pi) ^ 2 ≤ P.T) (hT2 : 2 * Real.pi * Real.exp 8 ≤ P.T)
    (hsep : ∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) :
    frobSqGhatFam P F Qn
      ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * familySum F Qn (fun q χ => Mform P (nuQ P q χ) (nuQ P q χ))
        + endsMaj P := by
  classical
  have hlne : Zeta23.l P.T ≠ 0 := by intro h0; rw [h0] at hl; linarith
  have hF := S2_localHypsCoreW P hP (by linarith) hl hX
  have hends := ends_family_bound P Qn P.cWin P.XQ (P.toParams.localFun P.T) hP hlne hT1 hT2 hF
    (fun q χ => nuFam_continuous P χ) hsep
  have ha : 0 < P.aQ := hP.aQ_pos
  have hL : 0 < P.LB := hP.LB_pos
  set c := ((P.aQ * P.LB ^ 2)⁻¹) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  -- per character: `‖Ĝ(χ)‖² = c·(L²𝓜 + 𝓔₁ + 𝓔₂)`
  have hchar : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      RHLinalg.frobSq (hatQ P (gridGram P χ))
        = c * (P.LB ^ 2 * Mform P (nuQ P q χ) (nuQ P q χ)
          + calE1 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)
          + calE2 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)) := by
    intro q hq χ _
    have h := frobSq_char_decomp hP hw hl hX (one_le_of_mem_moduli hq) χ
    rw [← h, hc]
    field_simp
  unfold frobSqGhatFam familySum
  rw [Finset.sum_congr rfl fun q hq =>
    Finset.sum_congr rfl fun χ hχ => hchar q hq χ (F.chars_subset q hχ)]
  -- bound the `𝓔` part by the family sum of absolute values over `Icc 1 Qn`
  have hE : ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
        (calE1 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)
          + calE2 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ))
      ≤ ZetaQ.Ends.famSum Qn (fun _ χ => |calE1 (toSetting P) (P.toParams.localFun P.T) (nuFam P.XQ χ)|)
        + ZetaQ.Ends.famSum Qn (fun _ χ => |calE2 (toSetting P) (P.toParams.localFun P.T) (nuFam P.XQ χ)|) := by
    have hR : ZetaQ.Ends.famSum Qn (fun _ χ => |calE1 (toSetting P) (P.toParams.localFun P.T) (nuFam P.XQ χ)|)
        + ZetaQ.Ends.famSum Qn (fun _ χ => |calE2 (toSetting P) (P.toParams.localFun P.T) (nuFam P.XQ χ)|)
        = ∑ q ∈ Finset.Icc 1 Qn, ∑ χ ∈ primitiveChars q,
            (|calE1 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)|
              + |calE2 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)|) := by
      unfold ZetaQ.Ends.famSum
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.sum_add_distrib]
      rfl
    rw [hR]
    refine le_trans (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun χ _ =>
      add_le_add (le_abs_self _) (le_abs_self _)) ?_
    refine le_trans (Finset.sum_le_sum fun q _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (F.chars_subset q)
        (fun χ _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (moduli_subset_Icc F Qn) ?_
    intro q _ _
    exact Finset.sum_nonneg fun χ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hM : ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
        c * (P.LB ^ 2 * Mform P (nuQ P q χ) (nuQ P q χ)
          + calE1 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)
          + calE2 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ))
      = (P.aQ ^ 2 * P.LB ^ 2)⁻¹
          * ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, Mform P (nuQ P q χ) (nuQ P q χ)
        + c * ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q,
            (calE1 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)
              + calE2 (toSetting P) (P.toParams.localFun P.T) (nuQ P q χ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hc]
    field_simp
    ring
  rw [hM]
  unfold endsMaj
  rw [← hc]
  have := mul_le_mul_of_nonneg_left (hE.trans hends) hc0.le
  linarith

end PartD1
/-! ###################### PART D2a ######################
The explicit (non-asymptotic) assembly at a single design point: rows 8, 9, 9′, the PP block
(sieve on both zones) and the family ends majorant, in §11's vocabulary. -/

section PartD2a

open Zeta23.PrimeSide Zeta23.ThmE ZetaQ.Ends ZetaQ.FamRows

/-- `MformKer P u v` is integrable on the window square for continuous densities. -/
theorem MformKer_integrableOn (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) :
    IntegrableOn (MformKer P u v) (P.IwinQ ×ˢ P.IwinQ) := by
  have hΦ : Continuous P.PhiQ := hP.PhiQ_continuous hw
  have hc : Continuous (MformKer P u v) := by
    unfold MformKer
    fun_prop
  rw [IwinQ_eq]
  exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- **The family split of `Σ_χ 𝓜[ν_χ,ν_χ]` into rows 8, 9 (twice) and 10–12.** -/
theorem familySum_Mform_nuQ_split (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (F : Family) (Qn : ℕ) :
    familySum F Qn (fun q χ => Mform P (nuQ P q χ) (nuQ P q χ))
      = familySum F Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
        + 2 * familySum F Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ))
        + familySum F Qn (fun q χ => Mform P (PXchi P χ) (PXchi P χ)) := by
  classical
  have hpt : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      Mform P (nuQ P q χ) (nuQ P q χ)
        = Mform P (muDensity q χ) (muDensity q χ)
          + 2 * Mform P (muDensity q χ) (PXchi P χ)
          + Mform P (PXchi P χ) (PXchi P χ) := by
    intro q χ
    have hμ := muDensity_continuous q χ
    have hPc := PXchi_continuous P χ
    have hν := nuQ_continuous P q χ
    have h := Mform_nuQ_split P q χ (MformKer_integrableOn hP hw hμ hν)
      (MformKer_integrableOn hP hw hPc hν) (MformKer_integrableOn hP hw hμ hμ)
      (MformKer_integrableOn hP hw hμ hPc) (MformKer_integrableOn hP hw hPc hμ)
      (MformKer_integrableOn hP hw hPc hPc)
    rw [h, MformQ_comm P (PXchi P χ) (muDensity q χ)]
    ring
  unfold familySum
  simp only [hpt, Finset.sum_add_distrib, Finset.mul_sum]

/-- **THE EXPLICIT ASSEMBLY AT A DESIGN POINT** (no asymptotics):
`‖Ĝ_fam‖²_F ≤ (a²L²)⁻¹·( MAIN8chars + |𝔉|·err8 + 2·R9closed + PPsieve ) + endsMaj`,
with `MAIN8chars = b(TL/2π)Σ_q |F.chars q|·ℓ_{1,q}²` (the family's OWN per-modulus
weight; `= MAIN8 = a²L²·ψ_{v_design}(0)·(T/2π)·Σφ*ℓ²/ℒ` whenever `F.IsFull`). Hypotheses: `Valid`,
`8w ≤ L`, `8 ≤ L`, `c_W ≤ c₀`, the sieve range `X ≤ Q^{2−δ}`, `T > Cs`, the two ends
T-floors, `Qn ≤ ⌊Q⌋₊`, and Lemma 8.1′ (`hsep`). -/
theorem frobSq_le_explicit (c₀ : ℝ) :
    ∃ Cs CM : ℝ, 0 < Cs ∧ 0 < CM ∧
      ∀ (P : ParamsQ) (δ : ℝ) (F : Family) (Qn : ℕ), P.Valid → 8 * P.w ≤ P.LB →
        (8 : ℝ) ≤ P.LB → P.cWin ≤ c₀ → 0 < δ → δ ≤ 2 → P.XQ ≤ Real.rpow P.Q (2 - δ) →
        Cs < P.T → Qn ≤ ⌊P.Q⌋₊ →
        (2 * Real.pi) ^ 2 ≤ P.T → 2 * Real.pi * Real.exp 8 ≤ P.T →
        (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
        frobSqGhatFam P F Qn
          ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹
              * (MAIN8chars F P Qn + F.sizeR Qn * err8 P Qn + 2 * R9closed P Qn + PPsieve Cs CM δ P)
            + endsMaj P := by
  obtain ⟨Cs, CM, hCs0, hCM0, hPP⟩ := famPP_le_sieve c₀
  refine ⟨Cs, CM, hCs0, hCM0, ?_⟩
  intro P δ F Qn hP hw hL8 hcr hδ0 hδ2 hXQ hTCs hQn hT1 hT2 hsep
  have hl : 1 ≤ Zeta23.l P.T := one_le_l_of_valid hP
  have hX : 1 ≤ P.XQ := one_le_XQ_of_valid hP
  have h0 := frobSqGhatFam_le_Mform_add_ends hP hw hl hX F Qn hT1 hT2 hsep
  rw [familySum_Mform_nuQ_split hP hw F Qn] at h0
  have h8 := famMform_mumu_eval P hP hw F Qn
  have h9 := famMform_muP_le_closed P hP hw F Qn
  have hpp := hPP P δ F Qn hP hw hL8 hcr hδ0 hδ2 hXQ hTCs hQn
  have hc0 : 0 ≤ (P.aQ ^ 2 * P.LB ^ 2)⁻¹ := by
    have := hP.aQ_pos; have := hP.LB_pos; positivity
  have h8' : familySum F Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
      ≤ MAIN8chars F P Qn + F.sizeR Qn * err8 P Qn := by linarith [(abs_le.mp h8).2]
  have h9' : familySum F Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ)) ≤ R9closed P Qn := by
    unfold R9closed R9fun; exact (le_abs_self _).trans h9
  have hsum : familySum F Qn (fun q χ => Mform P (muDensity q χ) (muDensity q χ))
        + 2 * familySum F Qn (fun q χ => Mform P (muDensity q χ) (PXchi P χ))
        + familySum F Qn (fun q χ => Mform P (PXchi P χ) (PXchi P χ))
      ≤ MAIN8chars F P Qn + F.sizeR Qn * err8 P Qn + 2 * R9closed P Qn + PPsieve Cs CM δ P := by
    unfold PPsieve
    linarith
  calc frobSqGhatFam P F Qn ≤ _ := h0
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hsum hc0
        linarith

end PartD2a
/-! ###################### PART D2b-pre ######################
Regime / arithmetic lemmas for the eventual assembly (no `FamRows` dependency). -/

section PartD2bPre

open Zeta23.PrimeSide Zeta23.ThmE ZetaQ.Ends Filter

/-- `K0 + K1 = ∫|α|ψ ≤ 2` for profiles of bandwidth `≤ 2`. -/
theorem K0_add_K1_le_two {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (h2 : lam ≤ 2) :
    K0 v + K1 v ≤ 2 := by
  rw [K0_add_K1 hv]
  have hpsi := psi_integrable hv
  have hbound : ∀ α, |α| * psi v α ≤ 2 * psi v α := by
    intro α
    by_cases hα : lam < |α|
    · simp [psi_supp' hv hα]
    · push_neg at hα
      nlinarith [psi_nonneg' hv α, abs_nonneg α]
  calc ∫ α, |α| * psi v α ≤ ∫ α, 2 * psi v α :=
        integral_mono (absPsi_integrable hv) (hpsi.const_mul 2) hbound
    _ = 2 := by rw [integral_const_mul, psi_total hv]; ring

theorem K0_add_K1_nonneg {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) : 0 ≤ K0 v + K1 v := by
  rw [K0_add_K1 hv]
  exact integral_nonneg fun α => mul_nonneg (abs_nonneg α) (psi_nonneg' hv α)

/-- `ℓ_{1,q}(T) ≤ ℒ + 2log2 − 1` for `1 ≤ q ≤ Q`. -/
theorem ell1q_le_LL (P : ParamsQ) (hT : 0 < P.T) {q : ℕ} (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ P.Q) :
    ell1q q P.T ≤ P.LL + (2 * Real.log 2 - 1) := by
  unfold ell1q ParamsQ.LL
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have : Real.log ((q : ℝ) * P.T / (2 * Real.pi)) ≤ Real.log (P.Q * P.T / (2 * Real.pi)) :=
    Real.log_le_log (by positivity) (by gcongr)
  linarith

theorem ell1q_nonneg {T : ℝ} (hT : 2 * Real.pi ≤ T) {q : ℕ} (hq : 1 ≤ q) : 0 ≤ ell1q q T := by
  unfold ell1q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 1 ≤ (q : ℝ) * T / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have := Real.log_nonneg h1
  have := Real.log_two_gt_d9
  linarith

/-- `ℓ_{1,q}(T) ≥ ℒ + log 2 − 1` for `Q/2 < q` (the dyadic family). -/
theorem ell1q_ge_dyadic (P : ParamsQ) (hT : 0 < P.T) {Qn q : ℕ} (hQn : 1 ≤ Qn) (hQ : P.Q = Qn)
    (hq : Qn / 2 < q) : P.LL + (Real.log 2 - 1) ≤ ell1q q P.T := by
  unfold ell1q ParamsQ.LL
  have h5 : Qn ≤ 2 * q := by omega
  have hq2 : (Qn : ℝ) ≤ 2 * q := by exact_mod_cast h5
  have hq0 : (0 : ℝ) < q := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hQn0 : (0 : ℝ) < Qn := by exact_mod_cast hQn
  rw [hQ]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog : Real.log ((Qn : ℝ) * P.T / (2 * Real.pi))
      ≤ Real.log ((q : ℝ) * P.T / (2 * Real.pi)) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    refine Real.log_le_log (by positivity) ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  linarith

/-- `|𝔉| ≤ |𝔉'|` whenever `F` and `G` share a modulus range and `G` is FULL — i.e. a parity
subfamily is no larger than its parent. Rule 17: no parameter occurs. -/
theorem sizeR_le_of_isFull (F G : Family) (Qn : ℕ) (hm : F.moduli Qn = G.moduli Qn)
    (hG : G.IsFull) : F.sizeR Qn ≤ G.sizeR Qn := by
  rw [sizeR_eq_sum_weight, sizeR_eq_sum_weight, hm]
  refine Finset.sum_le_sum fun q _ => ?_
  have hsub : F.chars q ⊆ G.chars q := by
    rw [G.chars_eq_of_isFull hG]; exact F.chars_subset q
  exact_mod_cast Finset.card_le_card hsub

/-- `|𝔉_Q| ≤ (18/π⁴)Q² + 5Q(1+log Q)²` for ALL SIX families: Corollary 3's four are
subfamilies of `qle` / `dyadic` on the same modulus range, so `sizeR_le_of_isFull` reduces
them to the two proved cases (and in fact they are about half the size). -/
theorem sizeR_le (F : Family) (Qn : ℕ) (hQn : 1 ≤ Qn) :
    F.sizeR Qn ≤ (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2 + 5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
  have hA := abs_le.mp (Normalisation.N2.Astar_bound Qn hQn)
  have hA0 : 0 ≤ Normalisation.N2.Astar (Qn / 2) := by
    unfold Normalisation.N2.Astar; positivity
  have hqle : Family.qle.sizeR Qn
      ≤ (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2 + 5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
    rw [sizeR_qle_eq_Astar_sub_one Qn hQn]; linarith [hA.2]
  have hdya : Family.dyadic.sizeR Qn
      ≤ (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2 + 5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by
    rw [sizeR_dyadic_eq]; linarith [hA.2]
  cases F with
  | qle => exact hqle
  | dyadic => exact hdya
  | evenQle =>
      exact le_trans (sizeR_le_of_isFull _ Family.qle Qn rfl Family.isFull_qle) hqle
  | oddQle =>
      exact le_trans (sizeR_le_of_isFull _ Family.qle Qn rfl Family.isFull_qle) hqle
  | evenDyadic =>
      exact le_trans (sizeR_le_of_isFull _ Family.dyadic Qn rfl Family.isFull_dyadic) hdya
  | oddDyadic =>
      exact le_trans (sizeR_le_of_isFull _ Family.dyadic Qn rfl Family.isFull_dyadic) hdya
  | evenQleR =>
      exact le_trans (sizeR_le_of_isFull _ Family.qle Qn rfl Family.isFull_qle) hqle
  | oddQleR =>
      exact le_trans (sizeR_le_of_isFull _ Family.qle Qn rfl Family.isFull_qle) hqle
  | evenDyadicR =>
      exact le_trans (sizeR_le_of_isFull _ Family.dyadic Qn rfl Family.isFull_dyadic) hdya
  | oddDyadicR =>
      exact le_trans (sizeR_le_of_isFull _ Family.dyadic Qn rfl Family.isFull_dyadic) hdya

theorem C1ends_nonneg (c : ℝ) : 0 ≤ C1ends c := by unfold C1ends; positivity

theorem C2ends_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ C2ends c := by
  unfold C2ends Zeta23.PrimeSide.CN2
  have h1 : 0 ≤ max 0 (Real.log c) := le_max_left _ _
  positivity

theorem Kends_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ Kends c := by
  unfold Kends; have := C1ends_nonneg c; have := C2ends_nonneg hc; positivity

/-- `l(T) ≤ ℒ` (`Q ≥ 1`). -/
theorem l_le_LL (hP : P.Valid) : Zeta23.l P.T ≤ P.LL := by
  unfold Zeta23.l ParamsQ.LL
  have hQ := hP.Q_ge
  have hT := hP.T_pos
  have hpi := Real.pi_pos
  refine Real.log_le_log (by positivity) ?_
  rw [div_le_div_iff_of_pos_right (by positivity)]
  nlinarith

theorem l_nonneg (hP : P.Valid) : 0 ≤ Zeta23.l P.T := by
  unfold Zeta23.l
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  linarith [hP.T_ge300, Real.pi_lt_four]

theorem LL_le_LB (hP : P.Valid) (hlam : 1 ≤ P.lam) : P.LL ≤ P.LB := by
  show P.LL ≤ P.lam * P.LL
  nlinarith [hP.LL_pos]

theorem LB_le_two_LL (hP : P.Valid) : P.LB ≤ 2 * P.LL := by
  show P.lam * P.LL ≤ 2 * P.LL
  nlinarith [hP.LL_pos, hP.lam_lt_two]

/-- `endsMaj ≤ Kends(c_W)·Q²·ℒ³` at `ℒ ≥ 30`, `λ ≥ 1`, `8 ≤ L`. -/
theorem endsMaj_le (hP : P.Valid) (hLL : 30 ≤ P.LL) (hlam : 1 ≤ P.lam) (hL8 : 8 ≤ P.LB) :
    endsMaj P ≤ Kends P.cWin * P.Q ^ 2 * P.LL ^ 3 := by
  unfold endsMaj Kends
  have hLL0 : 0 < P.LL := by linarith
  have hL0 : 0 < P.LB := by linarith
  have ha : 3 / 4 ≤ P.aQ := hP.a_ge
  have ha0 : 0 < P.aQ := by linarith
  have hc0 : 0 ≤ P.cWin := hP.cWin_pos.le
  have hC1 := C1ends_nonneg P.cWin
  have hC2 := C2ends_nonneg hc0
  have hl0 := l_nonneg hP
  have hl := (l_le_LL hP).trans (LL_le_LB hP hlam)
  have hL2 := LB_le_two_LL hP
  have hlogL : Real.log P.LB ≤ P.LB := by linarith [Real.log_le_sub_one_of_pos hL0]
  have hQ0 : 0 ≤ P.Q := by linarith [hP.Q_ge]
  -- the five factor bounds
  have f1 : ((P.aQ * P.LB ^ 2)⁻¹) ^ 2 ≤ (16 / 9) * (P.LB ^ 4)⁻¹ := by
    have h1 : ((P.aQ * P.LB ^ 2)⁻¹) ^ 2 = (P.aQ ^ 2)⁻¹ * (P.LB ^ 4)⁻¹ := by
      field_simp
    rw [h1]
    have h2 : (P.aQ ^ 2)⁻¹ ≤ 16 / 9 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have f2 : (c1Ends * P.Q) ^ 2 = 0.1681 * P.Q ^ 2 := by unfold c1Ends; ring
  have f3 : P.LB ^ 3 * (P.LB + Zeta23.l P.T) ≤ 2 * P.LB ^ 4 := by nlinarith [pow_pos hL0 3]
  have f4 : (P.LL + C0Ends) ^ 2 ≤ 1.44 * P.LL ^ 2 := by unfold C0Ends; nlinarith
  have f5 : C1ends P.cWin + C2ends P.cWin * (1 + Real.log P.LB)
      ≤ (C1ends P.cWin + 3 * C2ends P.cWin) * P.LL := by nlinarith
  have hA : 0 ≤ (c1Ends * P.Q) ^ 2 := sq_nonneg _
  have hB : 0 ≤ P.LB ^ 3 * (P.LB + Zeta23.l P.T) := by positivity
  have hC : 0 ≤ (P.LL + C0Ends) ^ 2 := sq_nonneg _
  have hD : 0 ≤ C1ends P.cWin + C2ends P.cWin * (1 + Real.log P.LB) := by
    have : 0 ≤ 1 + Real.log P.LB := by
      have := Real.log_nonneg (show (1:ℝ) ≤ P.LB by linarith); linarith
    positivity
  have hE : 0 ≤ ((P.aQ * P.LB ^ 2)⁻¹) ^ 2 := sq_nonneg _
  have key : ((P.aQ * P.LB ^ 2)⁻¹) ^ 2 * ((c1Ends * P.Q) ^ 2 * (P.LB ^ 3 * (P.LB + Zeta23.l P.T)
        * (P.LL + C0Ends) ^ 2 * (C1ends P.cWin + C2ends P.cWin * (1 + Real.log P.LB))))
      ≤ ((16 / 9) * (P.LB ^ 4)⁻¹) * ((0.1681 * P.Q ^ 2) * ((2 * P.LB ^ 4) * (1.44 * P.LL ^ 2)
        * ((C1ends P.cWin + 3 * C2ends P.cWin) * P.LL))) := by
    rw [f2]
    have h34 : P.LB ^ 3 * (P.LB + Zeta23.l P.T) * (P.LL + C0Ends) ^ 2
        ≤ (2 * P.LB ^ 4) * (1.44 * P.LL ^ 2) := mul_le_mul f3 f4 hC (by positivity)
    have h345 : P.LB ^ 3 * (P.LB + Zeta23.l P.T) * (P.LL + C0Ends) ^ 2
          * (C1ends P.cWin + C2ends P.cWin * (1 + Real.log P.LB))
        ≤ (2 * P.LB ^ 4) * (1.44 * P.LL ^ 2) * ((C1ends P.cWin + 3 * C2ends P.cWin) * P.LL) :=
      mul_le_mul h34 f5 hD (by positivity)
    have h2345 : 0.1681 * P.Q ^ 2 * (P.LB ^ 3 * (P.LB + Zeta23.l P.T) * (P.LL + C0Ends) ^ 2
          * (C1ends P.cWin + C2ends P.cWin * (1 + Real.log P.LB)))
        ≤ 0.1681 * P.Q ^ 2 * ((2 * P.LB ^ 4) * (1.44 * P.LL ^ 2)
          * ((C1ends P.cWin + 3 * C2ends P.cWin) * P.LL)) :=
      mul_le_mul_of_nonneg_left h345 (by positivity)
    exact mul_le_mul f1 h2345 (by positivity) (by positivity)
  refine key.trans ?_
  have e : (16 / 9) * (P.LB ^ 4)⁻¹ * ((0.1681 * P.Q ^ 2) * ((2 * P.LB ^ 4) * (1.44 * P.LL ^ 2)
        * ((C1ends P.cWin + 3 * C2ends P.cWin) * P.LL)))
      = (16 / 9 * 0.1681 * 2 * 1.44) * ((C1ends P.cWin + 3 * C2ends P.cWin) * P.Q ^ 2 * P.LL ^ 3) := by
    first | (field_simp; ring) | field_simp
  rw [e]
  have hnn : 0 ≤ (C1ends P.cWin + 3 * C2ends P.cWin) * P.Q ^ 2 * P.LL ^ 3 := by positivity
  have hc : (16 / 9 * 0.1681 * 2 * 1.44 : ℝ) ≤ 0.861 := by norm_num
  calc _ ≤ 0.861 * ((C1ends P.cWin + 3 * C2ends P.cWin) * P.Q ^ 2 * P.LL ^ 3) :=
        mul_le_mul_of_nonneg_right hc hnn
    _ = _ := by ring

/-! ### the row-9 closed form: monotone in `L`, and small eventually -/

theorem R9fun_mono {Q l L L' : ℝ} (hQ : 1 ≤ Q) (hl : 0 ≤ l) (hL : 0 ≤ L) (hLL' : L ≤ L') :
    R9fun Q l L ≤ R9fun Q l L' := by
  unfold R9fun
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hs : Real.sqrt (Real.exp L) ≤ Real.sqrt (Real.exp L') :=
    Real.sqrt_le_sqrt (Real.exp_le_exp.mpr hLL')
  have hpi : 0 < Real.pi := Real.pi_pos
  have hL' : 0 ≤ L' := hL.trans hLL'
  have hQ0 : 0 ≤ Q := by linarith
  have h1Q : 0 ≤ 1 + Real.log Q := by linarith
  have hl24 : 0 ≤ 44 * l + 24 := by linarith
  gcongr

/-- the row-9 closed form at `L = 1.2507321515·ℒ` is `≤ c·Q²·T` eventually (from
`Row9Numeric.row9_closed_eventually`, copied). -/
theorem R9fun_eventually (r ε c : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ Q : ℝ in atTop,
      R9fun Q (Real.log (Real.log Q ^ (r + ε) / (2 * Real.pi)))
          (1.2507321515 * Real.log (Q * Real.log Q ^ (r + ε) / (2 * Real.pi)))
        ≤ c * Q ^ 2 * Real.log Q ^ (r + ε) := by
  filter_upwards [Row9Numeric.row9_closed_eventually r ε (c / 3) hr hε (by positivity)] with Q hQ
  have h3 : (3:ℝ) * (c / 3 * Q ^ 2 * Real.log Q ^ (r + ε)) = c * Q ^ 2 * Real.log Q ^ (r + ε) := by
    ring
  unfold R9fun
  linarith [mul_le_mul_of_nonneg_left hQ (by norm_num : (0:ℝ) ≤ 3)]

/-! ### the thresholds along the design, as eventual facts in `Qn : ℕ` -/

theorem loglog_le_eventually (K : ℝ) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ≤ x := by
  have h := Real.isLittleO_log_id_atTop.def (one_div_pos.mpr hK)
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with x hx hx1
  simp only [Real.norm_eq_abs, id_eq] at hx
  rw [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (by linarith : (0:ℝ) ≤ x)] at hx
  calc K * Real.log x ≤ K * (1 / K * x) := by gcongr
    _ = x := by field_simp

/-- the design's `ℒ` and `T` in `Qn`: `ℒ = log Qn + log T − log 2π`, `T = (log Qn)^{r+ε}`. -/
theorem LL_eq_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ} (hQn : 1 ≤ Qn)
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) :
    P.LL = Real.log Qn + Real.log P.T - Real.log (2 * Real.pi) := by
  obtain ⟨hP, hQ, -⟩ := hdes
  unfold ParamsQ.LL
  have hQ0 : (0:ℝ) < Qn := by exact_mod_cast hQn
  have hT := hP.T_pos
  rw [hQ, Real.log_div (by positivity) (by positivity), Real.log_mul hQ0.ne' hT.ne']

end PartD2bPre
/-! ###################### PART D2b-1 ######################
The design's scales as eventual facts in `Qn`, and the sharp family lower bound
`Q²(T/2π)ℒ ≤ C_F(1+η)·𝒩` along the design of record (both families). -/

section PartD2b1

open Zeta23.PrimeSide Zeta23.ThmE ZetaQ.Ends Filter

/-! ### the design's scales -/

theorem lam_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) : P.lam = F.lamStar := hdes.2.2.2.1

theorem one_le_lam_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) : 1 ≤ P.lam := by
  rw [lam_of_design hdes]; exact one_le_lamStar_of_family F

theorem lam_le_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) : P.lam ≤ 1.2507321515 := by
  rw [lam_of_design hdes]
  cases F <;>
    simp [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10, lamStarEvenDyad12] <;> norm_num

theorem wrange_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1

theorem Q_of_design {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecord F r ε (Qn : ℝ) P) : P.Q = Qn := hdes.2.1

/-- the eventual regime facts in `Qn` along the design: for any `K > 0`,
`ℒ ≥ 30 ∨ …` — packaged: `log Qn ≥ K`, `T ≥ K`, `T ≥ K·ℒ²`, `ℒ ≤ 2 log Qn`, `K·(1+log Qn)² ≤ Qn`,
`X ≤ Qn^{3/2}`, `2·Qn^{-1/2} ≤ 1/K`, `log(Qn(T+2)) ≤ 3 log Qn`. -/
theorem design_regime (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      K ≤ Real.log Qn ∧ K ≤ P.T ∧ K * P.LL ^ 2 ≤ P.T ∧ P.LL ≤ 2 * Real.log Qn ∧
      K * (1 + Real.log Qn) ^ 2 ≤ Qn ∧ P.XQ ≤ Real.rpow P.Q (2 - 1 / 2) ∧
      2 * Real.rpow P.Q (-(1 / 2)) ≤ 1 / K ∧
      Real.log ((Qn : ℝ) * (P.T + 2)) ≤ 3 * Real.log Qn := by
  have hre : (3 : ℝ) ≤ r + ε := by linarith
  have hre0 : (0 : ℝ) < r + ε := by linarith
  have hK0 : 0 < K := by linarith
  -- facts in `x = log Qn`
  have hx1 : ∀ᶠ x : ℝ in atTop, (r + ε) * Real.log x ≤ x := loglog_le_eventually _ hre0
  have hx2 : ∀ᶠ x : ℝ in atTop, ((r + ε) / 0.19) * Real.log x ≤ x :=
    loglog_le_eventually _ (by positivity)
  have hx3 : ∀ᶠ x : ℝ in atTop, K ≤ x := eventually_ge_atTop K
  have hx4 : ∀ᶠ x : ℝ in atTop, 4 * K ≤ x := eventually_ge_atTop (4 * K)
  have hx5 : ∀ᶠ x : ℝ in atTop, 4 * K * x ^ 2 ≤ Real.exp x := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2 (b := (1:ℝ)) (by norm_num)).def
      (by positivity : (0:ℝ) < 1 / (4 * K))
    filter_upwards [h, eventually_ge_atTop (0:ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs, one_mul] at hx
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2), Real.abs_exp] at hx
    calc 4 * K * x ^ 2 ≤ 4 * K * (1 / (4 * K) * Real.exp x) := by gcongr
      _ = Real.exp x := by field_simp
  have hx6 : ∀ᶠ x : ℝ in atTop, 4 * K ^ 2 ≤ Real.exp x := by
    have h := Real.tendsto_exp_atTop.eventually_ge_atTop (4 * K ^ 2)
    exact h
  have hx7 : ∀ᶠ x : ℝ in atTop, Real.log (2 * Real.pi) ≤ x := eventually_ge_atTop _
  have hlogx : ∀ᶠ x : ℝ in atTop, Real.log 2 + (r + ε) * Real.log x ≤ x := by
    have h := loglog_le_eventually (2 * (r + ε)) (by positivity)
    filter_upwards [h, eventually_ge_atTop (2 * Real.log 2)] with x hx hx2
    nlinarith [Real.log_nonneg (show (1:ℝ) ≤ x by
      linarith [Real.log_two_gt_d9])]
  filter_upwards [tendsto_log_nat_atTop.eventually hx1, tendsto_log_nat_atTop.eventually hx2,
    tendsto_log_nat_atTop.eventually hx3, tendsto_log_nat_atTop.eventually hx4,
    tendsto_log_nat_atTop.eventually hx5, tendsto_log_nat_atTop.eventually hx6,
    tendsto_log_nat_atTop.eventually hx7, tendsto_log_nat_atTop.eventually hlogx,
    eventually_ge_atTop 3] with Qn h1 h2 h3 h4 h5 h6 h7 h8 hQn3
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  have hT := T_of_design hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (3 : ℝ) ≤ Qn := by exact_mod_cast hQn3
  have hQn0 : (0 : ℝ) < Qn := by linarith
  set x := Real.log (Qn : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hxe : Real.exp x = Qn := Real.exp_log hQn0
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog2pi3 : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.exp_one_gt_d9, Real.pi_lt_d2]
  -- `T = x^{r+ε}`, `log T = (r+ε) log x`
  have hTx : P.T = x ^ (r + ε) := by rw [hT]
  have hTpos : 0 < P.T := hP.T_pos
  have hlogT : Real.log P.T = (r + ε) * Real.log x := by
    rw [hTx, Real.log_rpow hx0]
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  -- `ℒ = x + log T − log 2π`
  have hLL := LL_eq_of_design hQn1 hdes
  rw [hlogT] at hLL
  have hLLx : P.LL ≤ 2 * x := by rw [hLL]; linarith
  have hLLge : x ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hLLpos : 0 < P.LL := by linarith
  -- `x³ ≤ T`
  have hx3T : x ^ 3 ≤ P.T := by
    rw [hTx]
    have : x ^ (3:ℝ) ≤ x ^ (r + ε) := Real.rpow_le_rpow_of_exponent_le (by linarith) hre
    rw [show (x:ℝ) ^ (3:ℝ) = x ^ (3:ℕ) by norm_cast] at this
    exact this
  refine ⟨h3, ?_, ?_, hLLx, ?_, ?_, ?_, ?_⟩
  · -- K ≤ T
    calc K ≤ x := h3
      _ ≤ x ^ 3 := by nlinarith
      _ ≤ P.T := hx3T
  · -- K ℒ² ≤ T
    calc K * P.LL ^ 2 ≤ K * (2 * x) ^ 2 := by gcongr
      _ = 4 * K * x ^ 2 := by ring
      _ ≤ x * x ^ 2 := by nlinarith
      _ = x ^ 3 := by ring
      _ ≤ P.T := hx3T
  · -- K (1 + log Qn)² ≤ Qn
    rw [← hxe]
    calc K * (1 + x) ^ 2 ≤ 4 * K * x ^ 2 := by nlinarith
      _ ≤ Real.exp x := h5
  · -- X ≤ Q^{3/2}
    have hLB : P.LB = P.lam * P.LL := rfl
    have hlam := lam_le_of_design hdes
    have hlam0 := hP.lam_pos
    show Real.exp P.LB ≤ P.Q ^ (2 - 1 / 2 : ℝ)
    rw [hQ, Real.rpow_def_of_pos hQn0, ← hxdef]
    apply Real.exp_le_exp.mpr
    rw [hLB]
    have hLL19 : P.LL ≤ 1.19 * x := by
      rw [hLL]
      have : (r + ε) * Real.log x ≤ 0.19 * x := by
        have := h2
        rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)] at this
        linarith
      linarith
    nlinarith
  · -- 2 Q^{-1/2} ≤ 1/K
    show 2 * P.Q ^ (-(1 / 2) : ℝ) ≤ 1 / K
    rw [hQ, Real.rpow_neg hQn0.le, ← Real.sqrt_eq_rpow,
      show (2:ℝ) * (Real.sqrt Qn)⁻¹ = 2 / Real.sqrt Qn by ring]
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hQn0) hK0]
    have : (2 * K) ^ 2 ≤ (Qn : ℝ) := by
      rw [← hxe]; nlinarith [h6]
    have hs : 2 * K ≤ Real.sqrt Qn := by
      rw [show (2 * K) = Real.sqrt ((2 * K) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt this
    linarith
  · -- log(Qn (T+2)) ≤ 3 log Qn
    have hT2 : P.T + 2 ≤ 2 * P.T := by linarith [hP.T_ge300]
    calc Real.log ((Qn : ℝ) * (P.T + 2)) ≤ Real.log ((Qn : ℝ) * (2 * P.T)) :=
          Real.log_le_log (by positivity) (by gcongr)
      _ = x + (Real.log 2 + Real.log P.T) := by
          rw [Real.log_mul hQn0.ne' (by positivity), Real.log_mul (by norm_num) hTpos.ne']
      _ ≤ 3 * x := by rw [hlogT]; linarith

/-! ### the sharp family lower bound on `𝒩` -/

/-- `(T/2π)·famEll1 ≤ 𝒩 + |𝔉|·A·log(Qn(T+2))` (RvM lower half, summed).

**`F.IsFull` is now CARRIED.** `FamRows.famEll1` prices each modulus at the FULL `φ*(q)`
(`ZetaQ/FrobRow8.lean`), while `NfamQ` and `F.sizeR` are `F.chars` objects, so for a parity
family the left-hand side is the full first moment and the right-hand side is roughly half of
it: the inequality is FALSE there, not merely unproved. An earlier form of this declaration consumed
the then-`sorry`ing `Budget.sizeR_eq_sum_phiStar` while generic in `F` and so reached
`sorryAx` silently. The parity route is to re-spell `famEll1` at `((F.chars q).card : ℝ)`,
against which `Budget.famRvM_lower_weight` is proved in all six branches; the obligation is
recorded at `A1_eventually`, the one `F`-generic consumer. -/
theorem famEll1_le (P : ParamsQ) {F : Family} (hF : F.IsFull) (Qn : ℕ) (hQn : 2 ≤ Qn)
    {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) (hT0 : 0 < P.T) :
    (P.T / (2 * Real.pi)) * FamRows.famEll1 F P Qn
      ≤ NfamQ P F Qn + F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2))) := by
  have h := famRvM_lower_raw P hF Qn hQn hrvm hT
  unfold FamRows.famEll1
  rw [Finset.mul_sum]
  have hS : F.sizeR Qn = ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) := sizeR_eq_sum_phiStar hF Qn
  rw [hS, Finset.sum_mul]
  have hterm : ∀ q ∈ F.moduli Qn,
      (phiStar q : ℝ) * (A * Real.log ((q : ℝ) * (P.T + 2)))
        ≤ (phiStar q : ℝ) * (A * Real.log ((Qn : ℝ) * (P.T + 2))) := by
    intro q hq
    have hq1 := one_le_of_mem_moduli hq
    have hqQ := le_Qn_of_mem_moduli hq
    have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
    have hqQ' : (q:ℝ) ≤ Qn := by exact_mod_cast hqQ
    gcongr
  have hsum := Finset.sum_le_sum hterm
  have e : ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T - A * Real.log ((q : ℝ) * (P.T + 2)))
      = ∑ q ∈ F.moduli Qn, P.T / (2 * Real.pi) * ((phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T)
        - ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * (A * Real.log ((q : ℝ) * (P.T + 2))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e] at h
  linarith

/-- **The sharp family lower bound, `qle`**: `Qn²(T/2π)ℒ ≤ Cfam(1+η)𝒩` from `FamRvMLower` and
`|𝔉| ≥ (18/π⁴)Qn² − 6Qn(1+log Qn)²`, once `(π⁴/3)(1+log Qn)² ≤ (η/4)Qn` and `0.124 ≤ (η/4)ℒ`. -/
theorem NfamQ_sharp_qle (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 1 ≤ Qn) (hQ : P.Q = Qn)
    (hrvm : FamRvMLower Family.qle Qn P) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsz : Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 ≤ 3 * (η / 4) * Qn)
    (hLL : 0.124 ≤ η / 4 * P.LL) :
    (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL
      ≤ Family.Cconst Family.qle * (1 + η) * NfamQ P Family.qle Qn := by
  have hT0 : 0 < P.T := hP.T_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsize := sizeR_qle_lower' Qn hQn
  have hpi4 : (97.408 : ℝ) < Real.pi ^ 4 := Ends.pi_four_gt
  have hlog2 := Real.log_two_gt_d9
  have hfA : P.LL - 0.124 ≤ famAvgLlow Family.qle P := by
    unfold famAvgLlow famAvgL rvmSlack Family.conductorShift; linarith
  have hQn0 : (0:ℝ) < Qn := by exact_mod_cast hQn
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hC : Family.Cconst Family.qle = Real.pi ^ 4 / 18 := rfl
  -- `|𝔉|·(ℒ − 0.124) ≥ (18/π⁴)(1−η/4)Qn²·(1−η/4)ℒ`
  have hsz' : (18 / Real.pi ^ 4) * (1 - η / 4) * (Qn : ℝ) ^ 2 ≤ Family.sizeR Family.qle Qn := by
    have : 6 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 ≤ (18 / Real.pi ^ 4) * (η / 4) * (Qn : ℝ) ^ 2 := by
      have h1 : (1 + Real.log Qn) ^ 2 ≤ (3 / Real.pi ^ 4) * (η / 4 * Qn) := by
        rw [show (3 / Real.pi ^ 4) * (η / 4 * Qn) = (3 * (η / 4) * Qn) / Real.pi ^ 4 by ring,
          le_div_iff₀ (by positivity)]
        linarith
      calc 6 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 ≤ 6 * Qn * ((3 / Real.pi ^ 4) * (η / 4 * Qn)) := by
            gcongr
        _ = (18 / Real.pi ^ 4) * (η / 4) * (Qn : ℝ) ^ 2 := by ring
    linarith
  have hLL' : (1 - η / 4) * P.LL ≤ famAvgLlow Family.qle P := by linarith
  have hS0 : 0 ≤ Family.sizeR Family.qle Qn := by unfold Family.sizeR; positivity
  have hfA0 : 0 ≤ famAvgLlow Family.qle P := by nlinarith
  have hN : Family.sizeR Family.qle Qn * (P.T / (2 * Real.pi) * famAvgLlow Family.qle P)
      ≤ NfamQ P Family.qle Qn := hrvm
  have h1η : 0 ≤ 1 - η / 4 := by linarith
  have hprod : (18 / Real.pi ^ 4) * (1 - η / 4) * (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))
      ≤ Family.sizeR Family.qle Qn * (P.T / (2 * Real.pi) * famAvgLlow Family.qle P) := by
    apply mul_le_mul hsz' (mul_le_mul_of_nonneg_left hLL' (by positivity))
      (mul_nonneg (by positivity) (mul_nonneg h1η hLL0.le)) hS0
  rw [hC]
  have hkey : (1 : ℝ) ≤ (1 - η / 4) * (1 - η / 4) * (1 + η) := by
    have : 0 ≤ η * (8 - 7 * η + η ^ 2) := mul_nonneg hη.le (by nlinarith)
    nlinarith
  have hbase : 0 ≤ (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL := by positivity
  calc (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL
      ≤ (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * ((1 - η / 4) * (1 - η / 4) * (1 + η)) :=
        le_mul_of_one_le_right hbase hkey
    _ = Real.pi ^ 4 / 18 * (1 + η) * ((18 / Real.pi ^ 4) * (1 - η / 4) * (Qn : ℝ) ^ 2
          * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))) := by
          first | (field_simp; ring) | field_simp
    _ ≤ Real.pi ^ 4 / 18 * (1 + η) * NfamQ P Family.qle Qn := by
        gcongr
        exact hprod.trans hN

/-- **The sharp family lower bound, `dyadic`**: from RvM (lower half) and
`|𝔉_d| ≥ (3/4)(18/π⁴)Qn² − 8Qn(1+log Qn)²`. -/
theorem NfamQ_sharp_dyadic (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn) (hQ : P.Q = Qn)
    {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsz : 16 * Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 ≤ 27 * (η / 4) * Qn)
    (hLL : 0.307 ≤ η / 8 * P.LL)
    (herr : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL)) :
    (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL
      ≤ Family.Cconst Family.dyadic * (1 + η) * NfamQ P Family.dyadic Qn := by
  have hT0 : 0 < P.T := hP.T_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQn1 : 1 ≤ Qn := by omega
  have hQn0 : (0:ℝ) < Qn := by exact_mod_cast hQn1
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hlog2 := Real.log_two_gt_d9
  have hC : Family.Cconst Family.dyadic = 2 * Real.pi ^ 4 / 27 := rfl
  have hlow := famRvM_lower_raw P Family.isFull_dyadic Qn hQn hrvm hT
  -- termwise: `φ*(q)((T/2π)ℓ_q − A log(q(T+2))) ≥ φ*(q)·((T/2π)(ℒ − 0.307) − A log(Qn(T+2)))`
  have hterm : ∀ q ∈ Family.moduli Family.dyadic Qn,
      (phiStar q : ℝ) * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))
        ≤ (phiStar q : ℝ) * (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            - A * Real.log ((q : ℝ) * (P.T + 2))) := by
    intro q hq
    have hq' : Qn / 2 < q := (Finset.mem_Ioc.mp hq).1
    have hqQ : q ≤ Qn := (Finset.mem_Ioc.mp hq).2
    have hq1 : 1 ≤ q := by omega
    have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
    have hqQ' : (q:ℝ) ≤ Qn := by exact_mod_cast hqQ
    have hell := ell1q_ge_dyadic P hT0 hQn1 hQ hq'
    have hlogq : Real.log ((q : ℝ) * (P.T + 2)) ≤ Real.log ((Qn : ℝ) * (P.T + 2)) :=
      Real.log_le_log (by positivity) (by gcongr)
    have hA' : A * Real.log ((q : ℝ) * (P.T + 2)) ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL) :=
      (mul_le_mul_of_nonneg_left hlogq hA).trans herr
    have h1 : P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL)
        ≤ P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T - A * Real.log ((q : ℝ) * (P.T + 2)) := by
      have h2 : P.T / (2 * Real.pi) * (P.LL - 0.307) ≤ P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have h3 : P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL)
          = P.T / (2 * Real.pi) * (P.LL - 0.307) - (P.T / (2 * Real.pi) * (η / 4 * P.LL - 0.307)) := by ring
      have h4 : η / 8 * (P.T / (2 * Real.pi) * P.LL) ≤ P.T / (2 * Real.pi) * (η / 4 * P.LL - 0.307) := by
        have : η / 8 * P.LL ≤ η / 4 * P.LL - 0.307 := by linarith
        have := mul_le_mul_of_nonneg_left this (show 0 ≤ P.T / (2 * Real.pi) by positivity)
        linarith
      linarith
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hS : ∑ q ∈ Family.moduli Family.dyadic Qn, (phiStar q : ℝ) = Family.sizeR Family.dyadic Qn :=
    (sizeR_eq_sum_phiStar Family.isFull_dyadic Qn).symm
  rw [hS] at hsum
  have hN : Family.sizeR Family.dyadic Qn * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))
      ≤ NfamQ P Family.dyadic Qn := hsum.trans hlow
  -- the size
  have hsize := sizeR_dyadic_lower Qn hQn
  have hsz' : (27 / (2 * Real.pi ^ 4)) * (1 - η / 4) * (Qn : ℝ) ^ 2
      ≤ Family.sizeR Family.dyadic Qn := by
    have h1 : 8 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 ≤ (27 / (2 * Real.pi ^ 4)) * (η / 4) * (Qn : ℝ) ^ 2 := by
      have h2 : (1 + Real.log Qn) ^ 2 ≤ (27 / (16 * Real.pi ^ 4)) * (η / 4 * Qn) := by
        rw [show (27 / (16 * Real.pi ^ 4)) * (η / 4 * Qn) = (27 * (η / 4) * Qn) / (16 * Real.pi ^ 4) by ring,
          le_div_iff₀ (by positivity)]
        linarith
      calc 8 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2
          ≤ 8 * Qn * ((27 / (16 * Real.pi ^ 4)) * (η / 4 * Qn)) := by gcongr
        _ = (27 / (2 * Real.pi ^ 4)) * (η / 4) * (Qn : ℝ) ^ 2 := by field_simp; ring
    have h3 : 3 / 4 * (18 / Real.pi ^ 4) = 27 / (2 * Real.pi ^ 4) := by field_simp; ring
    rw [h3] at hsize
    linarith
  have hS0 : 0 ≤ Family.sizeR Family.dyadic Qn := by unfold Family.sizeR; positivity
  have h1η : 0 ≤ 1 - η / 4 := by linarith
  have hprod : (27 / (2 * Real.pi ^ 4)) * (1 - η / 4) * (Qn : ℝ) ^ 2
        * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))
      ≤ Family.sizeR Family.dyadic Qn * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL)) :=
    mul_le_mul_of_nonneg_right hsz' (mul_nonneg (by positivity) (mul_nonneg h1η hLL0.le))
  rw [hC]
  have hkey : (1 : ℝ) ≤ (1 - η / 4) * (1 - η / 4) * (1 + η) := by
    have : 0 ≤ η * (8 - 7 * η + η ^ 2) := mul_nonneg hη.le (by nlinarith)
    nlinarith
  have hbase : 0 ≤ (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL := by positivity
  calc (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL
      ≤ (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * ((1 - η / 4) * (1 - η / 4) * (1 + η)) :=
        le_mul_of_one_le_right hbase hkey
    _ = 2 * Real.pi ^ 4 / 27 * (1 + η) * ((27 / (2 * Real.pi ^ 4)) * (1 - η / 4) * (Qn : ℝ) ^ 2
          * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))) := by
          first | (field_simp; ring) | field_simp
    _ ≤ 2 * Real.pi ^ 4 / 27 * (1 + η) * NfamQ P Family.dyadic Qn := by
        gcongr
        exact hprod.trans hN

/-- **The sharp family lower bound for the two `Icc 2 Qn` PARITY families**.

`NfamQ_sharp_qle` with `Family.qle` generalised: it reads `F` only through `F.conductorShift`
(inside `famAvgLlow`) and `F.Cconst`, and the size input is §12.3's halving

    |𝔉_Q| ≥ ½(|𝔉^full_Q| − Q) ≥ (9/π⁴)Q² − 3Q(1+log Q)² − Q/2

(`Budget.two_sizeR_parity_qle` against `Budget.sizeR_qle_lower'`). The `Q/2` that the count
costs is why the size threshold is `4π⁴(1+log Q)² ≤ 3(η/4)Q` rather than `NfamQ_sharp_qle`'s
`π⁴(1+log Q)² ≤ 3(η/4)Q`; the margin used is `2.625` of the available `9`. -/
theorem NfamQ_sharp_parity_qle (P : ParamsQ) (hP : P.Valid) {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = 1 / 2) (hC : F.Cconst = Real.pi ^ 4 / 9)
    (Qn : ℕ) (hQn : 1 ≤ Qn) (hmod : F.moduli Qn = Family.qle.moduli Qn)
    (hrvm : FamRvMLower F Qn P) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsz : 4 * Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 ≤ 3 * (η / 4) * Qn)
    (hLL : 0.124 ≤ η / 4 * P.LL) :
    (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL
      ≤ F.Cconst * (1 + η) * NfamQ P F Qn := by
  have hT0 : 0 < P.T := hP.T_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi4 : (97.408 : ℝ) < Real.pi ^ 4 := Ends.pi_four_gt
  have hpi40 : (0 : ℝ) < Real.pi ^ 4 := by positivity
  have hlog2 := Real.log_two_gt_d9
  have hQn0 : (0:ℝ) < Qn := by exact_mod_cast hQn
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hlogQ0 : (0:ℝ) ≤ Real.log (Qn : ℝ) := Real.log_natCast_nonneg Qn
  have hL2 : (1:ℝ) ≤ (1 + Real.log (Qn : ℝ)) ^ 2 := by nlinarith
  have hη4 : (0:ℝ) ≤ η / 4 := by linarith
  have hfA : P.LL - 0.124 ≤ famAvgLlow F P := by
    unfold famAvgLlow famAvgL rvmSlack
    rw [hsh]; linarith
  -- §12.3's size floor, sharp
  have hkey : 3 * (Qn:ℝ) * (1 + Real.log Qn) ^ 2 + (Qn:ℝ) / 2
      ≤ (9 / Real.pi ^ 4) * (η / 4) * (Qn:ℝ) ^ 2 := by
    rw [show (9 / Real.pi ^ 4) * (η / 4) * (Qn:ℝ) ^ 2
        = (9 * (η / 4) * (Qn:ℝ) ^ 2) / Real.pi ^ 4 by ring, le_div_iff₀ hpi40]
    linarith [mul_le_mul_of_nonneg_right hsz hQn0.le,
      mul_nonneg (mul_nonneg hpi40.le hQn0.le) (sub_nonneg.2 hL2),
      mul_nonneg hη4 (sq_nonneg (Qn:ℝ))]
  have hsz' : (9 / Real.pi ^ 4) * (1 - η / 4) * (Qn : ℝ) ^ 2 ≤ Family.sizeR F Qn := by
    have hpar := (abs_le.mp (two_sizeR_parity_qle hF Qn hQn hmod)).1
    have hqeq := sizeR_qle_eq_Astar_sub_one Qn hQn
    have hqlow := sizeR_qle_lower' Qn hQn
    -- put every `π⁴`-division on the SAME atom `9/π⁴` (`linarith` keeps `a / b` opaque
    -- when `b` is not a numeral, so `18/π⁴` and `9/π⁴` are unrelated to it otherwise)
    rw [show (18 : ℝ) / Real.pi ^ 4 = 2 * (9 / Real.pi ^ 4) by ring] at hqlow
    linarith [hpar, hqeq, hqlow, hkey]
  have hLL' : (1 - η / 4) * P.LL ≤ famAvgLlow F P := by linarith
  have hS0 : 0 ≤ Family.sizeR F Qn := by unfold Family.sizeR; positivity
  have hfA0 : 0 ≤ famAvgLlow F P := by nlinarith
  have hN : Family.sizeR F Qn * (P.T / (2 * Real.pi) * famAvgLlow F P) ≤ NfamQ P F Qn := hrvm
  have h1η : 0 ≤ 1 - η / 4 := by linarith
  have hprod : (9 / Real.pi ^ 4) * (1 - η / 4) * (Qn : ℝ) ^ 2
        * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))
      ≤ Family.sizeR F Qn * (P.T / (2 * Real.pi) * famAvgLlow F P) := by
    apply mul_le_mul hsz' (mul_le_mul_of_nonneg_left hLL' (by positivity))
      (mul_nonneg (by positivity) (mul_nonneg h1η hLL0.le)) hS0
  rw [hC]
  have hkey2 : (1 : ℝ) ≤ (1 - η / 4) * (1 - η / 4) * (1 + η) := by
    have : 0 ≤ η * (8 - 7 * η + η ^ 2) := mul_nonneg hη.le (by nlinarith)
    nlinarith
  have hbase : 0 ≤ (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL := by positivity
  calc (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL
      ≤ (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * ((1 - η / 4) * (1 - η / 4) * (1 + η)) :=
        le_mul_of_one_le_right hbase hkey2
    _ = Real.pi ^ 4 / 9 * (1 + η) * ((9 / Real.pi ^ 4) * (1 - η / 4) * (Qn : ℝ) ^ 2
          * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))) := by
          first | (field_simp; ring) | field_simp
    _ ≤ Real.pi ^ 4 / 9 * (1 + η) * NfamQ P F Qn := by
        gcongr
        exact hprod.trans hN

/-- **The sharp family lower bound for the two DYADIC PARITY families**.

`NfamQ_sharp_dyadic` with the per-modulus weight moved from `φ*(q)` to `|F.chars q|`
(`Budget.famRvM_lower_weight`, `Budget.sizeR_eq_sum_weight`). The conductor input
`ℓ_{1,q}(T) ≥ ℒ + log 2 − 1` for `q > Q/2` is per-modulus and so is unaffected; the only §12.3
input is the size floor
`|𝔉_Q| ≥ (27/4π⁴)Q² − 4Q(1+log Q)² − Q/2` (`Budget.two_sizeR_parity_dyadic` against
`Budget.sizeR_dyadic_lower`), which is why the size threshold is `20π⁴(1+log Q)² ≤ 27(η/4)Q`
rather than `16π⁴(1+log Q)² ≤ 27(η/4)Q`. -/
theorem NfamQ_sharp_parity_dyadic (P : ParamsQ) (hP : P.Valid) {F : Family} (hF : ¬ F.IsFull)
    (hC : F.Cconst = 4 * Real.pi ^ 4 / 27) (Qn : ℕ) (hQn : 2 ≤ Qn) (hQ : P.Q = Qn)
    (hmod : F.moduli Qn = Family.dyadic.moduli Qn)
    {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsz : 20 * Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 ≤ 27 * (η / 4) * Qn)
    (hLL : 0.307 ≤ η / 8 * P.LL)
    (herr : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL)) :
    (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL
      ≤ F.Cconst * (1 + η) * NfamQ P F Qn := by
  have hT0 : 0 < P.T := hP.T_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi40 : (0 : ℝ) < Real.pi ^ 4 := by positivity
  have hQn1 : 1 ≤ Qn := by omega
  have hQn0 : (0:ℝ) < Qn := by exact_mod_cast hQn1
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hlog2 := Real.log_two_gt_d9
  have hlogQ0 : (0:ℝ) ≤ Real.log (Qn : ℝ) := Real.log_natCast_nonneg Qn
  have hL2 : (1:ℝ) ≤ (1 + Real.log (Qn : ℝ)) ^ 2 := by nlinarith
  have hη4 : (0:ℝ) ≤ η / 4 := by linarith
  have hlow := famRvM_lower_weight P F Qn hQn hrvm hT
  have hterm : ∀ q ∈ F.moduli Qn,
      (((F.chars q).card : ℕ) : ℝ) * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))
        ≤ (((F.chars q).card : ℕ) : ℝ) * (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
            - A * Real.log ((q : ℝ) * (P.T + 2))) := by
    intro q hq
    rw [hmod] at hq
    have hq' : Qn / 2 < q := (Finset.mem_Ioc.mp hq).1
    have hqQ : q ≤ Qn := (Finset.mem_Ioc.mp hq).2
    have hq1 : 1 ≤ q := by omega
    have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
    have hqQ' : (q:ℝ) ≤ Qn := by exact_mod_cast hqQ
    have hell := ell1q_ge_dyadic P hT0 hQn1 hQ hq'
    have hlogq : Real.log ((q : ℝ) * (P.T + 2)) ≤ Real.log ((Qn : ℝ) * (P.T + 2)) :=
      Real.log_le_log (by positivity) (by gcongr)
    have hA' : A * Real.log ((q : ℝ) * (P.T + 2)) ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL) :=
      (mul_le_mul_of_nonneg_left hlogq hA).trans herr
    have h1 : P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL)
        ≤ P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T - A * Real.log ((q : ℝ) * (P.T + 2)) := by
      have h2 : P.T / (2 * Real.pi) * (P.LL - 0.307)
          ≤ P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have h3 : P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL)
          = P.T / (2 * Real.pi) * (P.LL - 0.307)
            - (P.T / (2 * Real.pi) * (η / 4 * P.LL - 0.307)) := by ring
      have h4 : η / 8 * (P.T / (2 * Real.pi) * P.LL)
          ≤ P.T / (2 * Real.pi) * (η / 4 * P.LL - 0.307) := by
        have hstep : η / 8 * P.LL ≤ η / 4 * P.LL - 0.307 := by linarith
        have := mul_le_mul_of_nonneg_left hstep (show 0 ≤ P.T / (2 * Real.pi) by positivity)
        linarith
      linarith
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hS : ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) = Family.sizeR F Qn :=
    (sizeR_eq_sum_weight F Qn).symm
  rw [hS] at hsum
  have hN : Family.sizeR F Qn * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))
      ≤ NfamQ P F Qn := hsum.trans hlow
  -- §12.3's size floor, sharp
  have hkey : 4 * (Qn:ℝ) * (1 + Real.log Qn) ^ 2 + (Qn:ℝ) / 2
      ≤ (27 / (4 * Real.pi ^ 4)) * (η / 4) * (Qn:ℝ) ^ 2 := by
    rw [show (27 / (4 * Real.pi ^ 4)) * (η / 4) * (Qn:ℝ) ^ 2
        = (27 * (η / 4) * (Qn:ℝ) ^ 2) / (4 * Real.pi ^ 4) by ring,
      le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hsz hQn0.le,
      mul_nonneg (mul_nonneg hpi40.le hQn0.le) (sub_nonneg.2 hL2),
      mul_nonneg hη4 (sq_nonneg (Qn:ℝ))]
  have hsz' : (27 / (4 * Real.pi ^ 4)) * (1 - η / 4) * (Qn : ℝ) ^ 2 ≤ Family.sizeR F Qn := by
    have hpar := (abs_le.mp (two_sizeR_parity_dyadic hF Qn hmod)).1
    have hdeq := sizeR_dyadic_eq Qn
    have hdlow := sizeR_dyadic_lower Qn hQn
    -- same normalisation as in `NfamQ_sharp_parity_qle`: one `π⁴`-division atom only
    have h34 : 3 / 4 * (18 / Real.pi ^ 4) = 2 * (27 / (4 * Real.pi ^ 4)) := by
      field_simp; ring
    rw [h34] at hdlow
    linarith [hpar, hdeq, hdlow, hkey]
  have hS0 : 0 ≤ Family.sizeR F Qn := by unfold Family.sizeR; positivity
  have h1η : 0 ≤ 1 - η / 4 := by linarith
  have hprod : (27 / (4 * Real.pi ^ 4)) * (1 - η / 4) * (Qn : ℝ) ^ 2
        * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))
      ≤ Family.sizeR F Qn * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL)) :=
    mul_le_mul_of_nonneg_right hsz' (mul_nonneg (by positivity) (mul_nonneg h1η hLL0.le))
  rw [hC]
  have hkey2 : (1 : ℝ) ≤ (1 - η / 4) * (1 - η / 4) * (1 + η) := by
    have : 0 ≤ η * (8 - 7 * η + η ^ 2) := mul_nonneg hη.le (by nlinarith)
    nlinarith
  have hbase : 0 ≤ (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL := by positivity
  calc (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL
      ≤ (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * ((1 - η / 4) * (1 - η / 4) * (1 + η)) :=
        le_mul_of_one_le_right hbase hkey2
    _ = 4 * Real.pi ^ 4 / 27 * (1 + η) * ((27 / (4 * Real.pi ^ 4)) * (1 - η / 4) * (Qn : ℝ) ^ 2
          * (P.T / (2 * Real.pi) * ((1 - η / 4) * P.LL))) := by
          first | (field_simp; ring) | field_simp
    _ ≤ 4 * Real.pi ^ 4 / 27 * (1 + η) * NfamQ P F Qn := by
        gcongr
        exact hprod.trans hN

set_option maxHeartbeats 1600000 in
/-- **The sharp family lower bound, eventually, ALL SIX families**. -/
theorem NfamQ_sharp_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL ≤ F.Cconst * (1 + η) * NfamQ P F Qn := by
  have hre : (0:ℝ) < r + ε := by linarith
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
    (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hpi4 : (97.408 : ℝ) < Real.pi ^ 4 := Ends.pi_four_gt
  -- thresholds: `K·(1+log Qn)² ≤ Qn` with `K = 4·(16π⁴/27)/η ≥ 4(π⁴/3)/η`, `ℒ ≥ 8·0.307/η`,
  -- `A·3·log Qn ≤ (η/8)(T/2π)·log Qn` i.e. `48πA/η ≤ T`.
  -- the threshold is raised from `4(16π⁴/27)/η = 2.37π⁴/η` to `6π⁴/η`, which is what
  -- the parity branches need (the `Q/2` that §12.3's count costs); the two full branches only
  -- get a stronger hypothesis.
  have hK1 : (1:ℝ) ≤ 6 * Real.pi ^ 4 / η := by
    rw [le_div_iff₀ hη]; nlinarith
  filter_upwards [design_regime F r ε hr hε (6 * Real.pi ^ 4 / η) hK1,
    design_regime F r ε hr hε (max 1 (max (8 * 0.307 / η) (48 * Real.pi * A / η))) (le_max_left _ _),
    famRvMLower_of_design r ε hr hε,
    famRvMLower_parity_of_design not_isFull_evenQle rfl (fun _ => rfl) r ε hr hε,
    famRvMLower_parity_of_design not_isFull_oddQle rfl (fun _ => rfl) r ε hr hε,
    famRvMLower_parity_of_design not_isFull_evenQleR rfl (fun _ => rfl) r ε hr hε,
    famRvMLower_parity_of_design not_isFull_oddQleR rfl (fun _ => rfl) r ε hr hε,
    hTtop.eventually_ge_atTop T₀, eventually_ge_atTop 2]
    with Qn hreg1 hreg2 hrvmq hrvmqE hrvmqO hrvmqER hrvmqOR hT0 hQn2
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  have hT := T_of_design hdes
  obtain ⟨hlogQ1, -, -, -, hsz1, -, -, -⟩ := hreg1 P hdes
  obtain ⟨hlogQ2, hT2, -, -, -, -, -, hlog3⟩ := hreg2 P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hLLge : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hmax1 : 8 * 0.307 / η ≤ P.LL :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hlogQ2.trans hLLge)
  have hmax2 : 48 * Real.pi * A / η ≤ P.T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT2
  have hT0' : T₀ ≤ P.T := by rw [hT]; exact hT0
  have hTpos : 0 < P.T := hP.T_pos
  have hlogQ0 : 0 ≤ Real.log Qn := Real.log_natCast_nonneg Qn
  cases F with
  | qle =>
    apply NfamQ_sharp_qle P hP Qn hQn1 hQ (hrvmq P hdes) hη hη1
    · -- π⁴(1+log Qn)² ≤ 3(η/4) Qn
      have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
  | dyadic =>
    apply NfamQ_sharp_dyadic P hP Qn hQn2 hQ hA.le hrvm hT0' hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
    · -- A log(Qn(T+2)) ≤ (η/8)(T/2π)ℒ
      have h1 : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ A * (3 * Real.log Qn) :=
        mul_le_mul_of_nonneg_left hlog3 hA.le
      have h2 : 48 * Real.pi * A ≤ η * P.T := by rw [div_le_iff₀ hη] at hmax2; linarith
      have h3 : A * (3 * Real.log Qn) ≤ η / 8 * (P.T / (2 * Real.pi) * Real.log Qn) := by
        have hpi := Real.pi_pos
        rw [show η / 8 * (P.T / (2 * Real.pi) * Real.log Qn) = (η * P.T) * Real.log Qn / (16 * Real.pi) by ring]
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right h2 hlogQ0]
      have h4 : η / 8 * (P.T / (2 * Real.pi) * Real.log Qn) ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL) := by
        gcongr
      linarith
  -- the two `Icc 2 Qn` parity families run on `famRvMLower_parity_of_design`; the two
  -- dyadic ones on the per-modulus `ℓ_{1,q} ≥ ℒ + log 2 − 1`, which needs no counting input.
  | evenQle =>
    apply NfamQ_sharp_parity_qle (F := Family.evenQle) P hP not_isFull_evenQle rfl rfl Qn hQn1
      rfl (hrvmqE P hdes) hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
  | oddQle =>
    apply NfamQ_sharp_parity_qle (F := Family.oddQle) P hP not_isFull_oddQle rfl rfl Qn hQn1
      rfl (hrvmqO P hdes) hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
  | evenDyadic =>
    apply NfamQ_sharp_parity_dyadic (F := Family.evenDyadic) P hP not_isFull_evenDyadic rfl Qn
      hQn2 hQ rfl hA.le hrvm hT0' hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
    · have h1 : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ A * (3 * Real.log Qn) :=
        mul_le_mul_of_nonneg_left hlog3 hA.le
      have h2 : 48 * Real.pi * A ≤ η * P.T := by rw [div_le_iff₀ hη] at hmax2; linarith
      have h3 : A * (3 * Real.log Qn) ≤ η / 8 * (P.T / (2 * Real.pi) * Real.log Qn) := by
        have hpi := Real.pi_pos
        rw [show η / 8 * (P.T / (2 * Real.pi) * Real.log Qn)
            = (η * P.T) * Real.log Qn / (16 * Real.pi) by ring]
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right h2 hlogQ0]
      have h4 : η / 8 * (P.T / (2 * Real.pi) * Real.log Qn)
          ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL) := by gcongr
      linarith
  | oddDyadic =>
    apply NfamQ_sharp_parity_dyadic (F := Family.oddDyadic) P hP not_isFull_oddDyadic rfl Qn
      hQn2 hQ rfl hA.le hrvm hT0' hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
    · have h1 : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ A * (3 * Real.log Qn) :=
        mul_le_mul_of_nonneg_left hlog3 hA.le
      have h2 : 48 * Real.pi * A ≤ η * P.T := by rw [div_le_iff₀ hη] at hmax2; linarith
      have h3 : A * (3 * Real.log Qn) ≤ η / 8 * (P.T / (2 * Real.pi) * Real.log Qn) := by
        have hpi := Real.pi_pos
        rw [show η / 8 * (P.T / (2 * Real.pi) * Real.log Qn)
            = (η * P.T) * Real.log Qn / (16 * Real.pi) by ring]
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right h2 hlogQ0]
      have h4 : η / 8 * (P.T / (2 * Real.pi) * Real.log Qn)
          ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL) := by gcongr
      linarith
  | evenQleR =>
    apply NfamQ_sharp_parity_qle (F := Family.evenQleR) P hP not_isFull_evenQleR rfl rfl Qn hQn1
      rfl (hrvmqER P hdes) hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
  | oddQleR =>
    apply NfamQ_sharp_parity_qle (F := Family.oddQleR) P hP not_isFull_oddQleR rfl rfl Qn hQn1
      rfl (hrvmqOR P hdes) hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
  | evenDyadicR =>
    apply NfamQ_sharp_parity_dyadic (F := Family.evenDyadicR) P hP not_isFull_evenDyadicR rfl Qn
      hQn2 hQ rfl hA.le hrvm hT0' hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
    · have h1 : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ A * (3 * Real.log Qn) :=
        mul_le_mul_of_nonneg_left hlog3 hA.le
      have h2 : 48 * Real.pi * A ≤ η * P.T := by rw [div_le_iff₀ hη] at hmax2; linarith
      have h3 : A * (3 * Real.log Qn) ≤ η / 8 * (P.T / (2 * Real.pi) * Real.log Qn) := by
        have hpi := Real.pi_pos
        rw [show η / 8 * (P.T / (2 * Real.pi) * Real.log Qn)
            = (η * P.T) * Real.log Qn / (16 * Real.pi) by ring]
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right h2 hlogQ0]
      have h4 : η / 8 * (P.T / (2 * Real.pi) * Real.log Qn)
          ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL) := by gcongr
      linarith
  | oddDyadicR =>
    apply NfamQ_sharp_parity_dyadic (F := Family.oddDyadicR) P hP not_isFull_oddDyadicR rfl Qn
      hQn2 hQ rfl hA.le hrvm hT0' hη hη1
    · have h2 := hsz1
      rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h2
      have hpos : 0 ≤ Real.pi ^ 4 * (1 + Real.log Qn) ^ 2 := by positivity
      nlinarith
    · rw [div_le_iff₀ hη] at hmax1; nlinarith
    · have h1 : A * Real.log ((Qn : ℝ) * (P.T + 2)) ≤ A * (3 * Real.log Qn) :=
        mul_le_mul_of_nonneg_left hlog3 hA.le
      have h2 : 48 * Real.pi * A ≤ η * P.T := by rw [div_le_iff₀ hη] at hmax2; linarith
      have h3 : A * (3 * Real.log Qn) ≤ η / 8 * (P.T / (2 * Real.pi) * Real.log Qn) := by
        have hpi := Real.pi_pos
        rw [show η / 8 * (P.T / (2 * Real.pi) * Real.log Qn)
            = (η * P.T) * Real.log Qn / (16 * Real.pi) by ring]
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right h2 hlogQ0]
      have h4 : η / 8 * (P.T / (2 * Real.pi) * Real.log Qn)
          ≤ η / 8 * (P.T / (2 * Real.pi) * P.LL) := by gcongr
      linarith

/-- the crude form: `Qn²·T·ℒ/(4π·C_F) ≤ 𝒩` eventually. -/
theorem NfamQ_crude_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst) ≤ NfamQ P F Qn := by
  filter_upwards [NfamQ_sharp_eventually F r ε hr hε (η := 1) one_pos le_rfl] with Qn h
  intro P hdes
  have h1 := h P hdes
  have hC : 0 < F.Cconst := by
    cases F <;>
      simp [Family.Cconst, Cfam, CfamDyadic, CfamEven, CfamEvenDyadic] <;> positivity
  have hpi := Real.pi_pos
  calc (Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)
      = ((Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL) / (2 * F.Cconst) := by
        field_simp; ring
    _ ≤ (F.Cconst * (1 + 1) * NfamQ P F Qn) / (2 * F.Cconst) := by gcongr
    _ = NfamQ P F Qn := by field_simp; ring

end PartD2b1
/-! ###################### PART D2b-2 ######################
The relative bounds for rows 8 and the row-8 error, EVENTUALLY along the design. -/

section PartD2b2

open Zeta23.PrimeSide Zeta23.ThmE ZetaQ.Ends ZetaQ.FamRows Filter

theorem bQ_le_one' (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) : P.bQ ≤ 1 := by
  have hl := one_le_l_of_valid hP
  have hX := one_le_XQ_of_valid hP
  have hF := S2_localHypsCoreW P hP (by linarith) hl hX
  exact le_trans hF.b_le_a hF.a_le_one

/-- `ψ_{v_design}(0) = b/(λa²) ≤ 16/9` at `λ ≥ 1`. -/
theorem psi0_le (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (hlam : 1 ≤ P.lam) :
    psi (vDesign P) 0 ≤ 16 / 9 := by
  rw [psi_vDesign_zero P hP]
  have hb := bQ_le_one' hP hw
  have ha := hP.a_ge
  have ha0 := hP.aQ_pos
  rw [div_le_iff₀ (by positivity)]
  have h1 : (3 / 4 : ℝ) * (3 / 4) ≤ P.aQ * P.aQ := mul_le_mul ha ha (by norm_num) ha0.le
  nlinarith

theorem psi0_nonneg (hP : P.Valid) : 0 ≤ psi (vDesign P) 0 :=
  psi_nonneg' (vDesign_admissible hP) 0

/-- `famEll1Sq ≤ (ℒ + 2log2 − 1)·famEll1`. -/
theorem famEll1Sq_le (hP : P.Valid) (F : Family) (Qn : ℕ) (hQ : P.Q = Qn) :
    famEll1Sq F P Qn ≤ (P.LL + (2 * Real.log 2 - 1)) * famEll1 F P Qn := by
  unfold famEll1Sq famEll1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq1 := one_le_of_mem_moduli hq
  have hqQ : (q:ℝ) ≤ P.Q := by rw [hQ]; exact_mod_cast le_Qn_of_mem_moduli hq
  have h1 := ell1q_le_LL P hP.T_pos hq1 hqQ
  have h0 := ell1q_nonneg (T_ge_two_pi hP) hq1
  have hφ : (0:ℝ) ≤ phiStar q := Nat.cast_nonneg _
  calc (phiStar q : ℝ) * ell1q q P.T ^ 2 = ((phiStar q : ℝ) * ell1q q P.T) * ell1q q P.T := by ring
    _ ≤ ((phiStar q : ℝ) * ell1q q P.T) * (P.LL + (2 * Real.log 2 - 1)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hφ h0)
    _ = _ := by ring

theorem famEll1_nonneg (hP : P.Valid) (F : Family) (Qn : ℕ) : 0 ≤ famEll1 F P Qn := by
  unfold famEll1
  exact Finset.sum_nonneg fun q hq => mul_nonneg (Nat.cast_nonneg _)
    (ell1q_nonneg (T_ge_two_pi hP) (one_le_of_mem_moduli hq))

/-- the error constant of row 8 as a function of the window constant. -/
def Kerr (c : ℝ) : ℝ := 1 + 87 * c + 384 * (8 + 2 * c ^ 2)

theorem Kerr_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ Kerr c := by unfold Kerr; positivity

set_option maxHeartbeats 4000000 in
/-- **the row-8 error, crudely**: `err8 ≤ 0.0071·L·T + Kerr(c_W)·L·ℒ²` at `ℒ ≥ 14`, `8 ≤ L`. -/
theorem err8_le (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (Qn : ℕ) (hQ : P.Q = Qn) (hQn : 1 ≤ Qn)
    (hLL : 14 ≤ P.LL) (hL8 : 8 ≤ P.LB) :
    err8 P Qn ≤ 0.0071 * P.LB * P.T + Kerr P.cWin * P.LB * P.LL ^ 2 := by
  have hT300 : 300 ≤ P.T := hP.T_ge300
  have hT0 : 0 < P.T := by linarith
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi4 : Real.pi < 3.1416 := Real.pi_lt_d4
  have hb1 := bQ_le_one' hP hw
  have hb0 : 0 ≤ P.bQ := hP.bQ_pos.le
  have hw1 : 1 ≤ P.w := hP.one_le_w
  have hc4 : 4 ≤ P.cWin := hP.four_le_cWin
  have hc0 : 0 ≤ P.cWin := by linarith
  have hL0 : 0 < P.LB := by linarith
  have hLL0 : 0 < P.LL := by linarith
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn hQ).1
  have hlogQ0 : 0 ≤ Real.log (Qn:ℝ) := Real.log_natCast_nonneg Qn
  have hl := l_le_LL hP
  have hl0 := l_nonneg hP
  have hℓ := ell1q_le_LL P hT0 hQn (by rw [hQ])
  have hℓ0 := ell1q_nonneg (T_ge_two_pi hP) hQn
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hℓ' : ell1q Qn P.T ≤ P.LL + 0.3863 := by linarith
  -- `A_q ≤ 4ℒ`
  have hA : Aq Qn P.T ≤ 4 * P.LL := by
    unfold Aq
    have h1 : Real.log Qn / (2 * Real.pi) ≤ P.LL / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : 11 / Real.pi * Zeta23.l P.T ≤ 11 / 3 * P.LL := by
      have : 11 / Real.pi ≤ 11 / 3 := by
        rw [div_le_div_iff₀ hpi (by norm_num)]; nlinarith
      calc 11 / Real.pi * Zeta23.l P.T ≤ 11 / 3 * Zeta23.l P.T :=
            mul_le_mul_of_nonneg_right this hl0
        _ ≤ 11 / 3 * P.LL := by gcongr
    linarith
  have hA0 : 0 ≤ Aq Qn P.T := by unfold Aq; positivity
  have hK : Kinc ≤ 96 := by
    unfold Kinc
    have : 180 / Real.pi ≤ 60 := by rw [div_le_iff₀ hpi]; linarith
    linarith
  have hK0 : 0 ≤ Kinc := by unfold Kinc; positivity
  -- `Cm8 ≤ 0.00112 T + 1.24 ℒ/T`
  have hCm : Cm8 Qn P.T ≤ 0.00112 * P.T + 1.24 * P.LL / P.T := by
    unfold Cm8
    have h1 : 1 - 2 * Real.log 2 ^ 2 ≤ 0.04 := by nlinarith
    have h2 : 36 ≤ 4 * Real.pi ^ 2 := by nlinarith
    have hfirst : P.T * (1 - 2 * Real.log 2 ^ 2) / (4 * Real.pi ^ 2) ≤ 0.00112 * P.T := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : P.T * (1 - 2 * Real.log 2 ^ 2) ≤ P.T * 0.04 := mul_le_mul_of_nonneg_left h1 hT0.le
      nlinarith
    have hsec : (10 / Real.pi) / P.T * ((ell1q Qn P.T + 1) / Real.pi + (10 / Real.pi) / P.T ^ 2)
        ≤ 1.24 * P.LL / P.T := by
      have hT2 : 90000 ≤ P.T ^ 2 := by nlinarith
      have hinv : 1 / P.T ^ 2 ≤ 1 / 90000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have hb1' : (ell1q Qn P.T + 1) / Real.pi ≤ (P.LL + 1.3863) / 3 := by
        rw [div_le_div_iff₀ hpi (by norm_num)]; nlinarith
      have h10 : 10 / Real.pi ≤ 10 / 3 := by rw [div_le_div_iff₀ hpi (by norm_num)]; nlinarith
      have hb2 : (10 / Real.pi) / P.T ^ 2 ≤ 0.00004 := by
        have : (10 / Real.pi) / P.T ^ 2 = (10 / Real.pi) * (1 / P.T ^ 2) := by ring
        rw [this]
        calc 10 / Real.pi * (1 / P.T ^ 2) ≤ 10 / 3 * (1 / 90000) := by
              exact mul_le_mul h10 hinv (by positivity) (by norm_num)
          _ ≤ 0.00004 := by norm_num
      have hsum : (ell1q Qn P.T + 1) / Real.pi + (10 / Real.pi) / P.T ^ 2
          ≤ (P.LL + 1.3863) / 3 + 0.00004 := add_le_add hb1' hb2
      have hsum' : (P.LL + 1.3863) / 3 + 0.00004 ≤ 0.372 * P.LL := by linarith
      calc (10 / Real.pi) / P.T * ((ell1q Qn P.T + 1) / Real.pi + (10 / Real.pi) / P.T ^ 2)
          ≤ (10 / 3) / P.T * (0.372 * P.LL) := by
            apply mul_le_mul _ (hsum.trans hsum') (by positivity) (by positivity)
            exact div_le_div_of_nonneg_right h10 hT0.le
        _ = 1.24 * P.LL / P.T := by ring
    linarith
  have hCm0 : 0 ≤ Cm8 Qn P.T := by
    unfold Cm8
    have h1' : 0 ≤ 1 - 2 * Real.log 2 ^ 2 := one_sub_two_logsq_nonneg
    positivity
  -- piece 1
  have hpiece1 : 2 * Real.pi * P.bQ * P.LB * Cm8 Qn P.T ≤ 0.0071 * P.LB * P.T + P.LB * P.LL ^ 2 := by
    have h2 : 1.24 * P.LL / P.T ≤ P.LL ^ 2 / 7 := by
      rw [div_le_div_iff₀ hT0 (by norm_num)]; nlinarith
    have hCm' : Cm8 Qn P.T ≤ 0.00112 * P.T + P.LL ^ 2 / 7 := hCm.trans (by linarith)
    have h1 : 2 * Real.pi * P.bQ * P.LB * Cm8 Qn P.T
        ≤ (2 * 3.1416) * (P.LB * (0.00112 * P.T + P.LL ^ 2 / 7)) := by
      have e1 : 2 * Real.pi * P.bQ * P.LB * Cm8 Qn P.T
          = (2 * Real.pi * P.bQ) * (P.LB * Cm8 Qn P.T) := by ring
      rw [e1]
      apply mul_le_mul _ (mul_le_mul_of_nonneg_left hCm' hL0.le) (by positivity) (by norm_num)
      nlinarith
    have e2 : (2 * 3.1416) * (P.LB * (0.00112 * P.T + P.LL ^ 2 / 7))
        = 0.007037184 * (P.LB * P.T) + 0.8976 * (P.LB * P.LL ^ 2) := by ring
    rw [e2] at h1
    have hpos : 0 ≤ P.LB * P.LL ^ 2 := by positivity
    have hpos2 : 0 ≤ P.LB * P.T := by positivity
    have e3 : 0.0071 * P.LB * P.T + P.LB * P.LL ^ 2 = 0.0071 * (P.LB * P.T) + 1 * (P.LB * P.LL ^ 2) := by ring
    rw [e3]
    linarith
  have hlogfac : 8 + 8 * Real.log (P.cWin * P.LB / (4 * P.w)) ≤ 2 * P.cWin * P.LB := by
    have hpos : 0 < P.cWin * P.LB / (4 * P.w) := by positivity
    have h1 := Real.log_le_sub_one_of_pos hpos
    have h2 : P.cWin * P.LB / (4 * P.w) ≤ P.cWin * P.LB / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    linarith
  -- piece 2
  have hpiece2 : (Aq Qn P.T ^ 2 + Aq Qn P.T * Kinc) * (8 + 8 * Real.log (P.cWin * P.LB / (4 * P.w)))
      ≤ 87 * P.cWin * P.LB * P.LL ^ 2 := by
    have hA2 : Aq Qn P.T ^ 2 ≤ (4 * P.LL) ^ 2 := pow_le_pow_left₀ hA0 hA 2
    have hAK1 : Aq Qn P.T * Kinc ≤ (4 * P.LL) * 96 := mul_le_mul hA hK hK0 (by positivity)
    have hAK : Aq Qn P.T ^ 2 + Aq Qn P.T * Kinc ≤ 16 * P.LL ^ 2 + 384 * P.LL := by nlinarith
    have hAK0 : 0 ≤ Aq Qn P.T ^ 2 + Aq Qn P.T * Kinc := by positivity
    have h384 : 384 * P.LL ≤ 27.5 * P.LL ^ 2 := by nlinarith
    calc (Aq Qn P.T ^ 2 + Aq Qn P.T * Kinc) * (8 + 8 * Real.log (P.cWin * P.LB / (4 * P.w)))
        ≤ (Aq Qn P.T ^ 2 + Aq Qn P.T * Kinc) * (2 * P.cWin * P.LB) :=
          mul_le_mul_of_nonneg_left hlogfac hAK0
      _ ≤ (16 * P.LL ^ 2 + 384 * P.LL) * (2 * P.cWin * P.LB) :=
          mul_le_mul_of_nonneg_right hAK (by positivity)
      _ ≤ (43.5 * P.LL ^ 2) * (2 * P.cWin * P.LB) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      _ = 87 * P.cWin * P.LB * P.LL ^ 2 := by ring
  -- piece 3
  have hpiece3 : Aq Qn P.T * Kinc * (8 + 2 * (P.cWin / P.w) ^ 2)
      ≤ 384 * (8 + 2 * P.cWin ^ 2) * P.LB * P.LL ^ 2 := by
    have hcw : (P.cWin / P.w) ^ 2 ≤ P.cWin ^ 2 := by
      have : P.cWin / P.w ≤ P.cWin := div_le_self hc0 hw1
      have h0 : 0 ≤ P.cWin / P.w := by positivity
      exact pow_le_pow_left₀ h0 this 2
    have hAK' : Aq Qn P.T * Kinc ≤ 384 * P.LL := by
      have := mul_le_mul hA hK hK0 (by positivity : (0:ℝ) ≤ 4 * P.LL)
      linarith
    have hf : 8 + 2 * (P.cWin / P.w) ^ 2 ≤ 8 + 2 * P.cWin ^ 2 := by linarith
    have hf0 : 0 ≤ 8 + 2 * (P.cWin / P.w) ^ 2 := by positivity
    have hLL2 : P.LL ≤ P.LB * P.LL ^ 2 := by nlinarith
    calc Aq Qn P.T * Kinc * (8 + 2 * (P.cWin / P.w) ^ 2)
        ≤ (384 * P.LL) * (8 + 2 * P.cWin ^ 2) :=
          mul_le_mul hAK' hf hf0 (by positivity)
      _ = 384 * (8 + 2 * P.cWin ^ 2) * P.LL := by ring
      _ ≤ 384 * (8 + 2 * P.cWin ^ 2) * (P.LB * P.LL ^ 2) := by gcongr
      _ = 384 * (8 + 2 * P.cWin ^ 2) * P.LB * P.LL ^ 2 := by ring
  unfold err8 Kerr
  linarith [hpiece1, hpiece2, hpiece3]

/-! ### the relative bounds, eventually -/

theorem Cconst_pos (F : Family) : 0 < F.Cconst := by
  cases F <;>
    simp [Family.Cconst, Cfam, CfamDyadic, CfamEven, CfamEvenDyadic] <;> try positivity

/-- `|𝔉| ≤ 0.2 Qn²` once `500(1+log Qn)² ≤ Qn`. -/
theorem sizeR_le_point (F : Family) (Qn : ℕ) (hQn : 1 ≤ Qn)
    (hsz : 500 * (1 + Real.log Qn) ^ 2 ≤ Qn) : F.sizeR Qn ≤ 0.2 * (Qn : ℝ) ^ 2 := by
  have h1 := sizeR_le F Qn hQn
  have h2 : 18 / Real.pi ^ 4 ≤ 0.19 := by
    have := Ends.pi_four_gt; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hQn0 : (0:ℝ) ≤ Qn := Nat.cast_nonneg _
  have h3 : (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2 ≤ 0.19 * (Qn : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have h4 : 5 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 ≤ 0.01 * (Qn : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsz (by positivity : (0:ℝ) ≤ Qn / 100)
    nlinarith
  linarith

/-- the common regime facts along the design: `ℒ ≥ 30`, `8 ≤ L`, `λ ≥ 1`, `8w ≤ L`, `Qn ≥ 2`. -/
theorem design_basic (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      30 ≤ P.LL ∧ 8 ≤ P.LB ∧ 1 ≤ P.lam ∧ 8 * P.w ≤ P.LB ∧ 2 ≤ Qn := by
  filter_upwards [design_regime F r ε hr hε 30 (by norm_num), eventually_ge_atTop 2]
    with Qn hreg hQn2
  intro P hdes
  obtain ⟨h30, -⟩ := hreg P hdes
  have hP := hdes.1
  have hLL : 30 ≤ P.LL := h30.trans (log_Qn_le_LL hP (by omega) (Q_of_design hdes)).1
  have hlam := one_le_lam_of_design hdes
  refine ⟨hLL, ?_, hlam, wrange_of_design hdes, hQn2⟩
  have := LL_le_LB hP hlam
  linarith

/-! ### the row-8 first moment at the family's OWN per-modulus weight

`FamRows.famEll1` prices each modulus at the FULL `phiStar q`, while `NfamQ` is an `F.chars`
sum; on a parity family the two differ by nearly a factor of two, which is what used to block
`A1_eventually`'s `¬ F.IsFull` branch. `famEll1Chars` is the same first moment at
`|F.chars q|`; against it `Budget.famRvM_lower_weight` and `Budget.sizeR_eq_sum_weight` are
available with no `F.IsFull` hypothesis, and the whole of `A1_eventually` goes through in all
six branches (`A1_eventually_gen`).

**A finding worth recording.** The `sorry` comment this replaces predicted that §12.3's count
`ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn` would be needed to convert
`∑_q |F.chars q|·ℓ₁,q` back to `½·∑_q phiStar q·ℓ₁,q + O(Q log Q)`. It is NOT needed. Once
the re-spelling is done consistently, every other object in the argument (`NfamQ`,
`Family.sizeR`, `MAIN8chars`, `famEll1SqChars`) is ALREADY an `F.chars` object proved in all
six branches, so the two sides match with no counting bridge at all. The `ParityCount` layer
is what makes those downstream lemmas true; it is not spent a second time here. -/

/-- `∑_{q ∈ 𝔉} |F.chars q| · ℓ_{1,q}` — `FamRows.famEll1` at the family's own weight. -/
def famEll1Chars (F : Family) (P : ParamsQ) (Qn : ℕ) : ℝ :=
  ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * ell1q q P.T

/-- On a FULL family the re-spelling changes nothing. -/
theorem famEll1Chars_eq_of_isFull {F : Family} (h : F.IsFull) (P : ParamsQ) (Qn : ℕ) :
    famEll1Chars F P Qn = famEll1 F P Qn :=
  Finset.sum_congr rfl fun q _ => by rw [F.card_chars_of_isFull h]

theorem famEll1Chars_nonneg (hP : P.Valid) (F : Family) (Qn : ℕ) : 0 ≤ famEll1Chars F P Qn := by
  unfold famEll1Chars
  exact Finset.sum_nonneg fun q hq => mul_nonneg (Nat.cast_nonneg _)
    (ell1q_nonneg (T_ge_two_pi hP) (one_le_of_mem_moduli hq))

/-- `famEll1SqChars ≤ (ℒ + 2log2 − 1)·famEll1Chars` — `famEll1Sq_le` at the family's own
weight (the proof is per modulus, so the weight is inert). -/
theorem famEll1SqChars_le (hP : P.Valid) (F : Family) (Qn : ℕ) (hQ : P.Q = Qn) :
    famEll1SqChars F P Qn ≤ (P.LL + (2 * Real.log 2 - 1)) * famEll1Chars F P Qn := by
  unfold famEll1SqChars famEll1Chars
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hq1 := one_le_of_mem_moduli hq
  have hqQ : (q:ℝ) ≤ P.Q := by rw [hQ]; exact_mod_cast le_Qn_of_mem_moduli hq
  have h1 := ell1q_le_LL P hP.T_pos hq1 hqQ
  have h0 := ell1q_nonneg (T_ge_two_pi hP) hq1
  have hφ : (0:ℝ) ≤ ((F.chars q).card : ℝ) := Nat.cast_nonneg _
  calc ((F.chars q).card : ℝ) * ell1q q P.T ^ 2
      = (((F.chars q).card : ℝ) * ell1q q P.T) * ell1q q P.T := by ring
    _ ≤ (((F.chars q).card : ℝ) * ell1q q P.T) * (P.LL + (2 * Real.log 2 - 1)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hφ h0)
    _ = _ := by ring

/-- **`famEll1_le` WITHOUT `F.IsFull`, at the family's own weight**:
`(T/2π)·famEll1Chars ≤ 𝒩 + |𝔉|·A·log(Qn(T+2))`.

The inputs are `Budget.famRvM_lower_weight` (all six branches) and `Budget.sizeR_eq_sum_weight`
(the true, `IsFull`-free count) in place of `famRvM_lower_raw` / `sizeR_eq_sum_phiStar`. -/
theorem famEll1Chars_le (P : ParamsQ) (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn)
    {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) (hT0 : 0 < P.T) :
    (P.T / (2 * Real.pi)) * famEll1Chars F P Qn
      ≤ NfamQ P F Qn + F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2))) := by
  have h := famRvM_lower_weight P F Qn hQn hrvm hT
  unfold famEll1Chars
  rw [Finset.mul_sum]
  have hS : F.sizeR Qn = ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) := sizeR_eq_sum_weight F Qn
  rw [hS, Finset.sum_mul]
  have hterm : ∀ q ∈ F.moduli Qn,
      ((F.chars q).card : ℝ) * (A * Real.log ((q : ℝ) * (P.T + 2)))
        ≤ ((F.chars q).card : ℝ) * (A * Real.log ((Qn : ℝ) * (P.T + 2))) := by
    intro q hq
    have hq1 := one_le_of_mem_moduli hq
    have hqQ := le_Qn_of_mem_moduli hq
    have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
    have hqQ' : (q:ℝ) ≤ Qn := by exact_mod_cast hqQ
    gcongr
  have hsum := Finset.sum_le_sum hterm
  have e : ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T - A * Real.log ((q : ℝ) * (P.T + 2)))
      = ∑ q ∈ F.moduli Qn, P.T / (2 * Real.pi) * (((F.chars q).card : ℝ) * Zeta23.ThmE.ell1q q P.T)
        - ∑ q ∈ F.moduli Qn, ((F.chars q).card : ℝ) * (A * Real.log ((q : ℝ) * (P.T + 2))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e] at h
  linarith

/-- `MAIN8chars` in `ψ(0)`-units — `FamRows.MAIN8_eq_psi` at the family's own weight. -/
theorem MAIN8chars_eq_psi (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) :
    MAIN8chars F P Qn
      = P.aQ ^ 2 * P.LB ^ 2 * Payoff.psi (Payoff.vDesign P) 0
          * (P.T / (2 * Real.pi)) * (famEll1SqChars F P Qn / P.LL) := by
  rw [psi_vDesign_zero P hP]
  unfold MAIN8chars
  have hLL : 0 < P.LL := hP.LL_pos
  have ha : 0 < P.aQ := hP.aQ_pos
  have hlam : 0 < P.lam := hP.lam_pos
  have hLBdef : P.LB = P.lam * P.LL := rfl
  rw [hLBdef]
  field_simp

set_option maxHeartbeats 4000000 in
/-- **(A1) row 8, relative — ALL SIX FAMILIES, no `F.IsFull`.**
`(a²L²)⁻¹·MAIN8chars ≤ (ψ₀ + ε′/8)·𝒩` eventually.

The `F.IsFull` route's two consumers are replaced by their own-weight versions:
`MAIN8chars_eq_of_isFull hF ▸ MAIN8_eq_psi` becomes `MAIN8chars_eq_psi`, and `famEll1_le`
becomes `famEll1Chars_le`. Every other step is verbatim and `F`-generic. -/
theorem A1_eventually_gen (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ)
    (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars F P Qn
        ≤ (psi (vDesign P) 0 + ε' / 8) * NfamQ P F Qn := by
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hre : (0:ℝ) < r + ε := by linarith
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
    (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  have hC := Cconst_pos F
  set K : ℝ := max 1 (max (12 / ε') (max (96 * Real.pi * A * F.Cconst / ε') 500)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  filter_upwards [design_regime F r ε hr hε K hK1, design_basic F r ε hr hε,
    NfamQ_crude_eventually F r ε hr hε, hTtop.eventually_ge_atTop T₀] with Qn hreg hbas hcrude hT0
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  have hT := T_of_design hdes
  obtain ⟨hlogK, hTK, -, -, hszK, -, -, hlog3⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hN := hcrude P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := by linarith
  have hpi := Real.pi_pos
  have ha0 := hP.aQ_pos
  have hL0 := hP.LB_pos
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hlogQ0 : 0 ≤ Real.log (Qn:ℝ) := Real.log_natCast_nonneg Qn
  have hK12 : 12 / ε' ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKA : 96 * Real.pi * A * F.Cconst / ε' ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hK500 : (500:ℝ) ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hLL12 : 12 / ε' ≤ P.LL := hK12.trans (hlogK.trans hlogQ)
  have hTA : 96 * Real.pi * A * F.Cconst / ε' ≤ P.T := hKA.trans hTK
  have hsz500 : 500 * (1 + Real.log Qn) ^ 2 ≤ Qn := by
    have h := hszK
    have hsq : 0 ≤ (1 + Real.log Qn) ^ 2 := sq_nonneg _
    nlinarith
  have hS := sizeR_le_point F Qn hQn1 hsz500
  have hS0 : 0 ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hpsi := psi0_le hP hw hlam
  have hpsi0 := psi0_nonneg hP
  have hE := famEll1SqChars_le hP F Qn hQ
  have hell := famEll1Chars_le P F Qn hQn2 hA.le hrvm (by rw [hT]; exact hT0) hTpos
  have hfam0 := famEll1Chars_nonneg hP F Qn
  have hM8 : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars F P Qn
      = psi (vDesign P) 0 * (P.T / (2 * Real.pi)) * (famEll1SqChars F P Qn / P.LL) := by
    rw [MAIN8chars_eq_psi P hP F Qn]; field_simp
  rw [hM8]
  have hlog2 := Real.log_two_lt_d9
  have hc : 2 * Real.log 2 - 1 ≤ 0.3863 := by linarith
  have hE' : famEll1SqChars F P Qn / P.LL ≤ (1 + 0.3863 / P.LL) * famEll1Chars F P Qn := by
    rw [div_le_iff₀ hLL0]
    have h1 : (P.LL + (2 * Real.log 2 - 1)) * famEll1Chars F P Qn
        ≤ (P.LL + 0.3863) * famEll1Chars F P Qn :=
      mul_le_mul_of_nonneg_right (by linarith) hfam0
    have e : (1 + 0.3863 / P.LL) * famEll1Chars F P Qn * P.LL
        = (P.LL + 0.3863) * famEll1Chars F P Qn := by field_simp
    rw [e]; linarith
  have hrat : 0.3863 / P.LL ≤ 0.033 * ε' := by
    rw [div_le_iff₀ hLL0]
    have := hLL12; rw [div_le_iff₀ hε'] at this
    nlinarith
  have h14 : 1 + 0.3863 / P.LL ≤ 1.4 := by
    have : 0.3863 / P.LL ≤ 0.4 := by rw [div_le_iff₀ hLL0]; linarith
    linarith
  have h14' : 0 ≤ 1 + 0.3863 / P.LL := by positivity
  have hmain : psi (vDesign P) 0 * (P.T / (2 * Real.pi)) * (famEll1SqChars F P Qn / P.LL)
      ≤ psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
          * (NfamQ P F Qn + F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)))) := by
    calc psi (vDesign P) 0 * (P.T / (2 * Real.pi)) * (famEll1SqChars F P Qn / P.LL)
        ≤ psi (vDesign P) 0 * (P.T / (2 * Real.pi))
            * ((1 + 0.3863 / P.LL) * famEll1Chars F P Qn) := by gcongr
      _ = psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
            * ((P.T / (2 * Real.pi)) * famEll1Chars F P Qn) := by ring
      _ ≤ _ := by gcongr
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hsmall1 : psi (vDesign P) 0 * (0.3863 / P.LL) * NfamQ P F Qn
      ≤ ε' / 16 * NfamQ P F Qn := by
    apply mul_le_mul_of_nonneg_right _ hN0
    calc psi (vDesign P) 0 * (0.3863 / P.LL) ≤ (16 / 9) * (0.033 * ε') :=
          mul_le_mul hpsi hrat (by positivity) (by norm_num)
      _ ≤ ε' / 16 := by linarith
  have hsmall2 : psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
        * (F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)))) ≤ ε' / 16 * NfamQ P F Qn := by
    have h1 : psi (vDesign P) 0 * (1 + 0.3863 / P.LL) ≤ 2.5 := by
      calc psi (vDesign P) 0 * (1 + 0.3863 / P.LL) ≤ (16 / 9) * 1.4 :=
            mul_le_mul hpsi h14 h14' (by norm_num)
        _ ≤ 2.5 := by norm_num
    have hlogQT0 : 0 ≤ Real.log ((Qn : ℝ) * (P.T + 2)) := by
      apply Real.log_nonneg
      have : (1:ℝ) ≤ Qn := by exact_mod_cast hQn1
      nlinarith
    have hAlog0 : 0 ≤ A * Real.log ((Qn : ℝ) * (P.T + 2)) := mul_nonneg hA.le hlogQT0
    have h2 : F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)))
        ≤ 0.2 * (Qn:ℝ) ^ 2 * (A * (3 * P.LL)) := by
      apply mul_le_mul hS _ hAlog0 (by positivity)
      apply mul_le_mul_of_nonneg_left _ hA.le
      linarith
    have key : 96 * Real.pi * A * F.Cconst ≤ ε' * P.T := by
      rw [div_le_iff₀ hε'] at hTA; linarith
    have h3 : 2.5 * (0.2 * (Qn:ℝ) ^ 2 * (A * (3 * P.LL)))
        ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := by
      rw [show 2.5 * (0.2 * (Qn:ℝ) ^ 2 * (A * (3 * P.LL)))
          = (96 * Real.pi * A * F.Cconst) * ((Qn:ℝ) ^ 2 * P.LL) / (64 * Real.pi * F.Cconst) by
            field_simp; ring,
        show ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst))
          = (ε' * P.T) * ((Qn:ℝ) ^ 2 * P.LL) / (64 * Real.pi * F.Cconst) by ring]
      gcongr
    calc psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
          * (F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2))))
        ≤ 2.5 * (0.2 * (Qn:ℝ) ^ 2 * (A * (3 * P.LL))) :=
          mul_le_mul h1 h2 (mul_nonneg hS0 hAlog0) (by norm_num)
      _ ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := h3
      _ ≤ ε' / 16 * NfamQ P F Qn := by gcongr
  have hfinal : psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
        * (NfamQ P F Qn + F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2))))
      = psi (vDesign P) 0 * NfamQ P F Qn + psi (vDesign P) 0 * (0.3863 / P.LL) * NfamQ P F Qn
        + psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
            * (F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)))) := by ring
  linarith [hmain, hfinal, hsmall1, hsmall2]

set_option maxHeartbeats 4000000 in
/-- **(A1) row 8, relative**: `(a²L²)⁻¹·MAIN8chars ≤ (ψ₀ + ε′/8)·𝒩` eventually.

**PROVED IN ALL SIX BRANCHES.** The `F.IsFull` branch keeps the original `famEll1_le` route;
the four Corollary 3 parity families go through `A1_eventually_gen`, which runs the identical
argument at the family's own per-modulus weight `|F.chars q|`. -/
theorem A1_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars F P Qn ≤ (psi (vDesign P) 0 + ε' / 8) * NfamQ P F Qn := by
  by_cases hF : F.IsFull
  case neg =>
    -- Corollary 3: the row-8 obligation at the family's own weight (`A1_eventually_gen`,
    -- which needs no `F.IsFull` at all — `hF` is not used).
    exact A1_eventually_gen F r ε hr hε ε' hε'
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hre : (0:ℝ) < r + ε := by linarith
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop :=
    (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  have hC := Cconst_pos F
  set K : ℝ := max 1 (max (12 / ε') (max (96 * Real.pi * A * F.Cconst / ε') 500)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  filter_upwards [design_regime F r ε hr hε K hK1, design_basic F r ε hr hε,
    NfamQ_crude_eventually F r ε hr hε, hTtop.eventually_ge_atTop T₀] with Qn hreg hbas hcrude hT0
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  have hT := T_of_design hdes
  obtain ⟨hlogK, hTK, -, -, hszK, -, -, hlog3⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hN := hcrude P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := by linarith
  have hpi := Real.pi_pos
  have ha0 := hP.aQ_pos
  have hL0 := hP.LB_pos
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hlogQ0 : 0 ≤ Real.log (Qn:ℝ) := Real.log_natCast_nonneg Qn
  have hK12 : 12 / ε' ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKA : 96 * Real.pi * A * F.Cconst / ε' ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hK500 : (500:ℝ) ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hLL12 : 12 / ε' ≤ P.LL := hK12.trans (hlogK.trans hlogQ)
  have hTA : 96 * Real.pi * A * F.Cconst / ε' ≤ P.T := hKA.trans hTK
  have hsz500 : 500 * (1 + Real.log Qn) ^ 2 ≤ Qn := by
    have h := hszK
    have hsq : 0 ≤ (1 + Real.log Qn) ^ 2 := sq_nonneg _
    nlinarith
  have hS := sizeR_le_point F Qn hQn1 hsz500
  have hS0 : 0 ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hψ := psi0_le hP hw hlam
  have hψ0 := psi0_nonneg hP
  have hE := famEll1Sq_le hP F Qn hQ
  have hell := famEll1_le P hF Qn hQn2 hA.le hrvm (by rw [hT]; exact hT0) hTpos
  have hfam0 := famEll1_nonneg hP F Qn
  have hM8 : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars F P Qn
      = psi (vDesign P) 0 * (P.T / (2 * Real.pi)) * (famEll1Sq F P Qn / P.LL) := by
    rw [MAIN8chars_eq_of_isFull hF, MAIN8_eq_psi P hP F Qn]; field_simp
  rw [hM8]
  have hlog2 := Real.log_two_lt_d9
  have hc : 2 * Real.log 2 - 1 ≤ 0.3863 := by linarith
  have hE' : famEll1Sq F P Qn / P.LL ≤ (1 + 0.3863 / P.LL) * famEll1 F P Qn := by
    rw [div_le_iff₀ hLL0]
    have h1 : (P.LL + (2 * Real.log 2 - 1)) * famEll1 F P Qn ≤ (P.LL + 0.3863) * famEll1 F P Qn :=
      mul_le_mul_of_nonneg_right (by linarith) hfam0
    have e : (1 + 0.3863 / P.LL) * famEll1 F P Qn * P.LL = (P.LL + 0.3863) * famEll1 F P Qn := by
      field_simp
    rw [e]; linarith
  have hrat : 0.3863 / P.LL ≤ 0.033 * ε' := by
    rw [div_le_iff₀ hLL0]
    have := hLL12; rw [div_le_iff₀ hε'] at this
    nlinarith
  have h14 : 1 + 0.3863 / P.LL ≤ 1.4 := by
    have : 0.3863 / P.LL ≤ 0.4 := by rw [div_le_iff₀ hLL0]; linarith
    linarith
  have h14' : 0 ≤ 1 + 0.3863 / P.LL := by positivity
  have hmain : psi (vDesign P) 0 * (P.T / (2 * Real.pi)) * (famEll1Sq F P Qn / P.LL)
      ≤ psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
          * (NfamQ P F Qn + F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)))) := by
    calc psi (vDesign P) 0 * (P.T / (2 * Real.pi)) * (famEll1Sq F P Qn / P.LL)
        ≤ psi (vDesign P) 0 * (P.T / (2 * Real.pi)) * ((1 + 0.3863 / P.LL) * famEll1 F P Qn) := by
          gcongr
      _ = psi (vDesign P) 0 * (1 + 0.3863 / P.LL) * ((P.T / (2 * Real.pi)) * famEll1 F P Qn) := by ring
      _ ≤ _ := by gcongr
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hsmall1 : psi (vDesign P) 0 * (0.3863 / P.LL) * NfamQ P F Qn ≤ ε' / 16 * NfamQ P F Qn := by
    apply mul_le_mul_of_nonneg_right _ hN0
    calc psi (vDesign P) 0 * (0.3863 / P.LL) ≤ (16 / 9) * (0.033 * ε') :=
          mul_le_mul hψ hrat (by positivity) (by norm_num)
      _ ≤ ε' / 16 := by linarith
  have hsmall2 : psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
        * (F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)))) ≤ ε' / 16 * NfamQ P F Qn := by
    have h1 : psi (vDesign P) 0 * (1 + 0.3863 / P.LL) ≤ 2.5 := by
      calc psi (vDesign P) 0 * (1 + 0.3863 / P.LL) ≤ (16 / 9) * 1.4 :=
            mul_le_mul hψ h14 h14' (by norm_num)
        _ ≤ 2.5 := by norm_num
    have hlogQT0 : 0 ≤ Real.log ((Qn : ℝ) * (P.T + 2)) := by
      apply Real.log_nonneg
      have : (1:ℝ) ≤ Qn := by exact_mod_cast hQn1
      nlinarith
    have hAlog0 : 0 ≤ A * Real.log ((Qn : ℝ) * (P.T + 2)) := mul_nonneg hA.le hlogQT0
    have h2 : F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)))
        ≤ 0.2 * (Qn:ℝ) ^ 2 * (A * (3 * P.LL)) := by
      apply mul_le_mul hS _ hAlog0 (by positivity)
      apply mul_le_mul_of_nonneg_left _ hA.le
      linarith
    have key : 96 * Real.pi * A * F.Cconst ≤ ε' * P.T := by
      rw [div_le_iff₀ hε'] at hTA; linarith
    have h3 : 2.5 * (0.2 * (Qn:ℝ) ^ 2 * (A * (3 * P.LL)))
        ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := by
      rw [show 2.5 * (0.2 * (Qn:ℝ) ^ 2 * (A * (3 * P.LL)))
          = (96 * Real.pi * A * F.Cconst) * ((Qn:ℝ) ^ 2 * P.LL) / (64 * Real.pi * F.Cconst) by
            first | (field_simp; ring) | field_simp,
        show ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst))
          = (ε' * P.T) * ((Qn:ℝ) ^ 2 * P.LL) / (64 * Real.pi * F.Cconst) by ring]
      gcongr
    calc psi (vDesign P) 0 * (1 + 0.3863 / P.LL) * (F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2))))
        ≤ 2.5 * (0.2 * (Qn:ℝ) ^ 2 * (A * (3 * P.LL))) :=
          mul_le_mul h1 h2 (mul_nonneg hS0 hAlog0) (by norm_num)
      _ ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := h3
      _ ≤ ε' / 16 * NfamQ P F Qn := by gcongr
  have hfinal : psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
        * (NfamQ P F Qn + F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2))))
      = psi (vDesign P) 0 * NfamQ P F Qn + psi (vDesign P) 0 * (0.3863 / P.LL) * NfamQ P F Qn
        + psi (vDesign P) 0 * (1 + 0.3863 / P.LL)
            * (F.sizeR Qn * (A * Real.log ((Qn : ℝ) * (P.T + 2)))) := by ring
  linarith [hmain, hfinal, hsmall1, hsmall2]

set_option maxHeartbeats 4000000 in
/-- **(A2) the row-8 error, relative**: `(a²L²)⁻¹·|𝔉|·err8 ≤ (ε′/8)·𝒩` eventually. -/
theorem A2_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (F.sizeR Qn * err8 P Qn) ≤ ε' / 8 * NfamQ P F Qn := by
  have hC := Cconst_pos F
  set Kc : ℝ := Kerr (cWinDesign F) with hKc
  set K : ℝ := max 1 (max (0.51 * F.Cconst / ε') (max (72 * Kc * F.Cconst / ε') 500)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  filter_upwards [design_regime F r ε hr hε K hK1, design_basic F r ε hr hε,
    NfamQ_crude_eventually F r ε hr hε] with Qn hreg hbas hcrude
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  obtain ⟨hlogK, hTK, -, -, hszK, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hN := hcrude P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := by linarith
  have hpi := Real.pi_pos
  have hpi4 : Real.pi ≤ 3.1416 := Real.pi_lt_d4.le
  have ha0 := hP.aQ_pos
  have ha := hP.a_ge
  have hL0 := hP.LB_pos
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hcW : P.cWin = cWinDesign F := cWin_of_design hdes
  have hc0 : 0 ≤ cWinDesign F := by rw [← hcW]; exact hP.cWin_pos.le
  have hKc0 : 0 ≤ Kc := Kerr_nonneg hc0
  have hK1' : 0.51 * F.Cconst / ε' ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK2' : 72 * Kc * F.Cconst / ε' ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hK500 : (500:ℝ) ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hLL1 : 0.51 * F.Cconst ≤ ε' * P.LL := by
    have := hK1'.trans (hlogK.trans hlogQ); rw [div_le_iff₀ hε'] at this; linarith
  have hT2 : 72 * Kc * F.Cconst ≤ ε' * P.T := by
    have := hK2'.trans hTK; rw [div_le_iff₀ hε'] at this; linarith
  have hsz500 : 500 * (1 + Real.log Qn) ^ 2 ≤ Qn := by
    have h := hszK
    have hsq : 0 ≤ (1 + Real.log Qn) ^ 2 := sq_nonneg _
    nlinarith
  have hS := sizeR_le_point F Qn hQn1 hsz500
  have hS0 : 0 ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have herr := err8_le hP hw Qn hQ hQn1 (by linarith) hL8
  rw [hcW] at herr
  have herr0 : 0 ≤ err8 P Qn := by
    unfold err8 Cm8 Aq Kinc
    have h1' : 0 ≤ 1 - 2 * Real.log 2 ^ 2 := one_sub_two_logsq_nonneg
    have hl0 := l_nonneg hP
    have hlogQ0 : 0 ≤ Real.log (Qn:ℝ) := Real.log_natCast_nonneg Qn
    have hℓ0 := ell1q_nonneg (T_ge_two_pi hP) hQn1
    have hb0 := hP.bQ_pos.le
    have hw1 := hP.one_le_w
    have hlogf : 0 ≤ Real.log (P.cWin * P.LB / (4 * P.w)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      have hc4 := hP.four_le_cWin
      nlinarith
    positivity
  -- `(a²L²)⁻¹ ≤ (16/9)/(L·ℒ)`
  have hinv : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ ≤ (16 / 9) / (P.LB * P.LL) := by
    have hLLle : P.LL ≤ P.LB := LL_le_LB hP hlam
    have h1 : (9 / 16) * (P.LB * P.LL) ≤ P.aQ ^ 2 * P.LB ^ 2 := by
      have ha2 : (9 / 16 : ℝ) ≤ P.aQ ^ 2 := by nlinarith
      have hL2 : P.LB * P.LL ≤ P.LB ^ 2 := by nlinarith
      calc (9 / 16) * (P.LB * P.LL) ≤ P.aQ ^ 2 * (P.LB * P.LL) :=
            mul_le_mul_of_nonneg_right ha2 (by positivity)
        _ ≤ P.aQ ^ 2 * P.LB ^ 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
    calc (P.aQ ^ 2 * P.LB ^ 2)⁻¹ ≤ ((9 / 16) * (P.LB * P.LL))⁻¹ :=
          inv_anti₀ (by positivity) h1
      _ = (16 / 9) / (P.LB * P.LL) := by field_simp
  have hmain : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (F.sizeR Qn * err8 P Qn)
      ≤ (16 / 9) / (P.LB * P.LL)
          * (0.2 * (Qn : ℝ) ^ 2 * (0.0071 * P.LB * P.T + Kc * P.LB * P.LL ^ 2)) := by
    apply mul_le_mul hinv (mul_le_mul hS herr herr0 (by positivity)) (by positivity) (by positivity)
  have hsimp : (16 / 9) / (P.LB * P.LL)
        * (0.2 * (Qn : ℝ) ^ 2 * (0.0071 * P.LB * P.T + Kc * P.LB * P.LL ^ 2))
      = (16 / 9 * 0.2 * 0.0071) * ((Qn : ℝ) ^ 2 * P.T / P.LL)
        + (16 / 9 * 0.2 * Kc) * ((Qn : ℝ) ^ 2 * P.LL) := by
    first | (field_simp; ring) | field_simp
  rw [hsimp] at hmain
  have hpc1 : (16 / 9 * 0.2 * 0.0071) * ((Qn : ℝ) ^ 2 * P.T / P.LL)
      ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := by
    have key : (16 / 9 * 0.2 * 0.0071) * (64 * Real.pi * F.Cconst) ≤ ε' * P.LL ^ 2 := by
      have h1 : (16 / 9 * 0.2 * 0.0071) * (64 * Real.pi * F.Cconst) ≤ 0.51 * F.Cconst := by
        have := mul_le_mul_of_nonneg_right hpi4 hC.le
        linarith
      have hLL2 : P.LL ≤ P.LL ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hLL2 hε'.le]
    rw [show (16 / 9 * 0.2 * 0.0071) * ((Qn : ℝ) ^ 2 * P.T / P.LL)
        = ((16 / 9 * 0.2 * 0.0071) * (64 * Real.pi * F.Cconst)) * ((Qn : ℝ) ^ 2 * P.T * P.LL)
          / (64 * Real.pi * F.Cconst * P.LL ^ 2) by first | (field_simp; ring) | field_simp,
      show ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst))
        = (ε' * P.LL ^ 2) * ((Qn : ℝ) ^ 2 * P.T * P.LL) / (64 * Real.pi * F.Cconst * P.LL ^ 2) by
          first | (field_simp; ring) | field_simp]
    gcongr
  have hpc2 : (16 / 9 * 0.2 * Kc) * ((Qn : ℝ) ^ 2 * P.LL)
      ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := by
    have key : (16 / 9 * 0.2 * Kc) * (64 * Real.pi * F.Cconst) ≤ ε' * P.T := by
      have h1 : (16 / 9 * 0.2 * Kc) * (64 * Real.pi * F.Cconst) ≤ 72 * Kc * F.Cconst := by
        have h0 : 0 ≤ Kc * F.Cconst := mul_nonneg hKc0 hC.le
        have hpc : Kc * (Real.pi * F.Cconst) ≤ Kc * (3.1416 * F.Cconst) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpi4 hC.le) hKc0
        calc (16 / 9 * 0.2 * Kc) * (64 * Real.pi * F.Cconst)
            = (16 / 9 * 0.2 * 64) * (Kc * (Real.pi * F.Cconst)) := by ring
          _ ≤ (16 / 9 * 0.2 * 64) * (Kc * (3.1416 * F.Cconst)) := by gcongr
          _ = (16 / 9 * 0.2 * 64 * 3.1416) * (Kc * F.Cconst) := by ring
          _ ≤ 72 * (Kc * F.Cconst) := by gcongr; norm_num
          _ = 72 * Kc * F.Cconst := by ring
      linarith
    rw [show (16 / 9 * 0.2 * Kc) * ((Qn : ℝ) ^ 2 * P.LL)
        = ((16 / 9 * 0.2 * Kc) * (64 * Real.pi * F.Cconst)) * ((Qn : ℝ) ^ 2 * P.LL)
          / (64 * Real.pi * F.Cconst) by first | (field_simp; ring) | field_simp,
      show ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst))
        = (ε' * P.T) * ((Qn : ℝ) ^ 2 * P.LL) / (64 * Real.pi * F.Cconst) by ring]
    gcongr
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  calc (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (F.sizeR Qn * err8 P Qn)
      ≤ (16 / 9 * 0.2 * 0.0071) * ((Qn : ℝ) ^ 2 * P.T / P.LL)
        + (16 / 9 * 0.2 * Kc) * ((Qn : ℝ) ^ 2 * P.LL) := hmain
    _ ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst))
        + ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := add_le_add hpc1 hpc2
    _ = ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := by ring
    _ ≤ ε' / 8 * NfamQ P F Qn := by gcongr

end PartD2b2
/-! ###################### PART D2b-3 ######################
The relative bounds for row 9, the PP block and the ends, EVENTUALLY along the design, and the
assembled eventual theorem with the sieve-on-both-zones constant
`κ_sieve(P) = ψ_{v_design}(0) + C_F·(K0 + K1)(v_design)`. -/

section PartD2b3

open Zeta23.PrimeSide Zeta23.ThmE ZetaQ.Ends ZetaQ.FamRows Filter

/-- `(a²L²)⁻¹ ≤ (16/9)/ℒ²` (`a ≥ 3/4`, `L ≥ ℒ`). -/
theorem inv_aL_le (hP : P.Valid) (hlam : 1 ≤ P.lam) :
    (P.aQ ^ 2 * P.LB ^ 2)⁻¹ ≤ (16 / 9) / P.LL ^ 2 := by
  have ha := hP.a_ge
  have ha0 := hP.aQ_pos
  have hLL0 := hP.LL_pos
  have hLLle : P.LL ≤ P.LB := LL_le_LB hP hlam
  have h1 : (9 / 16) * P.LL ^ 2 ≤ P.aQ ^ 2 * P.LB ^ 2 := by
    have ha2 : (9 / 16 : ℝ) ≤ P.aQ ^ 2 := by nlinarith
    have hL2 : P.LL ^ 2 ≤ P.LB ^ 2 := pow_le_pow_left₀ hLL0.le hLLle 2
    calc (9 / 16) * P.LL ^ 2 ≤ P.aQ ^ 2 * P.LL ^ 2 := mul_le_mul_of_nonneg_right ha2 (by positivity)
      _ ≤ P.aQ ^ 2 * P.LB ^ 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
  calc (P.aQ ^ 2 * P.LB ^ 2)⁻¹ ≤ ((9 / 16) * P.LL ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
    _ = (16 / 9) / P.LL ^ 2 := by field_simp

set_option maxHeartbeats 4000000 in
/-- **(A3) row 9, relative**: `(a²L²)⁻¹·2·R9closed ≤ (ε′/8)·𝒩` eventually. -/
theorem A3_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn) ≤ ε' / 8 * NfamQ P F Qn := by
  have hC := Cconst_pos F
  have hR9 := tendsto_natCast_atTop_atTop.eventually (R9fun_eventually r ε 1 hr hε one_pos)
  set K : ℝ := max 1 (358 * F.Cconst / ε') with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  filter_upwards [design_regime F r ε hr hε K hK1, design_basic F r ε hr hε,
    NfamQ_crude_eventually F r ε hr hε, hR9, eventually_ge_atTop 1] with Qn hreg hbas hcrude hR9' hQn1
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  have hT := T_of_design hdes
  obtain ⟨hlogK, -, -, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hN := hcrude P hdes
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := by linarith
  have hpi := Real.pi_pos
  have hpi4 : Real.pi ≤ 3.1416 := Real.pi_lt_d4.le
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hK' : 358 * F.Cconst ≤ ε' * P.LL := by
    have := (le_max_right _ _ : 358 * F.Cconst / ε' ≤ K).trans (hlogK.trans hlogQ)
    rw [div_le_iff₀ hε'] at this; linarith
  -- `R9closed ≤ Qn² T`
  have hLLeq := LL_of_design hdes
  have hl : Zeta23.l P.T = Real.log (Real.log Qn ^ (r + ε) / (2 * Real.pi)) := by
    unfold Zeta23.l; rw [hT]
  have hR9'' : R9fun (Qn : ℝ) (Zeta23.l P.T) (1.2507321515 * P.LL) ≤ 1 * (Qn : ℝ) ^ 2 * P.T := by
    rw [hl, hLLeq, hT]; exact hR9'
  have hQn1R : (1:ℝ) ≤ Qn := by exact_mod_cast hQn1
  have hLB1 : P.LB ≤ 1.2507321515 * P.LL := by
    have := lam_le_of_design hdes
    show P.lam * P.LL ≤ _
    nlinarith
  have hR9c : R9closed P Qn ≤ (Qn : ℝ) ^ 2 * P.T := by
    unfold R9closed
    refine (R9fun_mono hQn1R (l_nonneg hP) hP.LB_pos.le hLB1).trans ?_
    linarith
  have hR9c0 : 0 ≤ R9closed P Qn := by
    unfold R9closed R9fun
    have := l_nonneg hP
    have := hP.LB_pos
    have hlogQ0 : 0 ≤ Real.log (Qn:ℝ) := Real.log_natCast_nonneg Qn
    positivity
  have hinv := inv_aL_le hP hlam
  have hmain : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
      ≤ (16 / 9) / P.LL ^ 2 * (2 * ((Qn : ℝ) ^ 2 * P.T)) := by
    apply mul_le_mul hinv (by linarith) (by positivity) (by positivity)
  have hkey : (32 / 9 : ℝ) * (32 * Real.pi * F.Cconst) ≤ ε' * P.LL ^ 3 := by
    have h1 : (32 / 9 : ℝ) * (32 * Real.pi * F.Cconst) ≤ 358 * F.Cconst := by
      have := mul_le_mul_of_nonneg_right hpi4 hC.le
      linarith
    have hLL3 : P.LL ≤ P.LL ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hLL3 hε'.le]
  have hfin : (16 / 9) / P.LL ^ 2 * (2 * ((Qn : ℝ) ^ 2 * P.T))
      ≤ ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := by
    rw [show (16 / 9) / P.LL ^ 2 * (2 * ((Qn : ℝ) ^ 2 * P.T))
        = ((32 / 9) * (32 * Real.pi * F.Cconst)) * ((Qn : ℝ) ^ 2 * P.T * P.LL)
          / (32 * Real.pi * F.Cconst * P.LL ^ 3) by first | (field_simp; ring) | field_simp,
      show ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst))
        = (ε' * P.LL ^ 3) * ((Qn : ℝ) ^ 2 * P.T * P.LL) / (32 * Real.pi * F.Cconst * P.LL ^ 3) by
          first | (field_simp; ring) | field_simp]
    gcongr
  calc (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
      ≤ (16 / 9) / P.LL ^ 2 * (2 * ((Qn : ℝ) ^ 2 * P.T)) := hmain
    _ ≤ ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := hfin
    _ ≤ ε' / 8 * NfamQ P F Qn := by gcongr

set_option maxHeartbeats 4000000 in
/-- **(A5) the ends, relative**: `endsMaj ≤ (ε′/8)·𝒩` eventually. -/
theorem A5_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      endsMaj P ≤ ε' / 8 * NfamQ P F Qn := by
  have hC := Cconst_pos F
  set Ke : ℝ := Kends (cWinDesign F) with hKe
  set K : ℝ := max 1 (32 * Real.pi * F.Cconst * Ke / ε') with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  filter_upwards [design_regime F r ε hr hε K hK1, design_basic F r ε hr hε,
    NfamQ_crude_eventually F r ε hr hε] with Qn hreg hbas hcrude
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  obtain ⟨-, -, hTK, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hN := hcrude P hdes
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := by linarith
  have hpi := Real.pi_pos
  have hcW : P.cWin = cWinDesign F := cWin_of_design hdes
  have hc0 : 0 ≤ cWinDesign F := by rw [← hcW]; exact hP.cWin_pos.le
  have hKe0 : 0 ≤ Ke := Kends_nonneg hc0
  have hends := endsMaj_le hP hLL30 hlam hL8
  rw [hcW, hQ] at hends
  have hK' : 32 * Real.pi * F.Cconst * Ke * P.LL ^ 2 ≤ ε' * P.T := by
    have h1 : 32 * Real.pi * F.Cconst * Ke / ε' ≤ K := le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg P.LL)
    rw [div_mul_eq_mul_div, div_le_iff₀ hε'] at h2
    have h3 := mul_le_mul_of_nonneg_right hTK hε'.le
    linarith
  have hfin : Ke * (Qn : ℝ) ^ 2 * P.LL ^ 3 ≤ ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := by
    rw [show Ke * (Qn : ℝ) ^ 2 * P.LL ^ 3
        = (32 * Real.pi * F.Cconst * Ke * P.LL ^ 2) * ((Qn : ℝ) ^ 2 * P.LL) / (32 * Real.pi * F.Cconst) by
          first | (field_simp; ring) | field_simp,
      show ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst))
        = (ε' * P.T) * ((Qn : ℝ) ^ 2 * P.LL) / (32 * Real.pi * F.Cconst) by ring]
    gcongr
  calc endsMaj P ≤ Ke * (Qn : ℝ) ^ 2 * P.LL ^ 3 := hends
    _ ≤ ε' / 8 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := hfin
    _ ≤ ε' / 8 * NfamQ P F Qn := by gcongr

/-- the three small factors of the sieve bound multiply to `≤ 1 + η` once each is `≤ η/4 ≤ 1/4`. -/
theorem three_factor_le {a b c η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (ha' : a ≤ η / 4) (hb' : b ≤ η / 4) (hc' : c ≤ η / 4) :
    (1 + a) * (1 + b) * (1 + c) ≤ 1 + η := by
  have h1 : (1 + a) * (1 + b) * (1 + c) ≤ (1 + η / 4) ^ 3 := by
    have : (1 + a) * (1 + b) * (1 + c) ≤ (1 + η / 4) * (1 + η / 4) * (1 + η / 4) := by
      apply mul_le_mul (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
        (by linarith) (by linarith) (by positivity)
    linarith [this]
  have h2 : (1 + η / 4) ^ 3 ≤ 1 + η := by
    nlinarith [mul_nonneg hη0 hη0, mul_nonneg (mul_nonneg hη0 hη0) hη0]
  linarith

set_option maxHeartbeats 4000000 in
/-- **(A4) the PP block, relative**:
`(a²L²)⁻¹·PPsieve ≤ (C_F(K0+K1) + ε′/8)·𝒩` eventually (sieve on both zones). -/
theorem A4_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (Cs CM Lρ Tρ : ℝ)
    (hCs : 0 < Cs) (hCM : 0 < CM)
    (hρ : ∀ P : ParamsQ, P.Valid → 8 * P.w ≤ P.LB → P.cWin ≤ cWinDesign F →
      Lρ ≤ P.LB → Tρ ≤ P.T → rhoU P Set.univ ≤ rhoConstConservative * Real.sqrt (2 / P.T))
    (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * PPsieve Cs CM (1 / 2) P
        ≤ (F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) + ε' / 8) * NfamQ P F Qn := by
  have hC := Cconst_pos F
  set η : ℝ := min 1 (ε' / (96 * F.Cconst)) with hηdef
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ ε' / (96 * F.Cconst) := min_le_right _ _
  have hpi := Real.pi_pos
  set K : ℝ := max 1 (max (8 / η) (max (1536 / (Real.pi * η ^ 2))
    (max (4 * Cs / η) (max (240 * F.Cconst * CM / ε') (max Lρ Tρ))))) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  filter_upwards [design_regime F r ε hr hε K hK1, design_basic F r ε hr hε,
    NfamQ_crude_eventually F r ε hr hε, NfamQ_sharp_eventually F r ε hr hε hη0 hη1]
    with Qn hreg hbas hcrude hsharp
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  obtain ⟨hlogK, hTK, -, -, -, -, hQhalf, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hN := hcrude P hdes
  have hNs := hsharp P hdes
  have hQn1 : 1 ≤ Qn := by omega
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := by linarith
  have ha0 := hP.aQ_pos
  have ha := hP.a_ge
  have hL0 := hP.LB_pos
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hcW : P.cWin = cWinDesign F := cWin_of_design hdes
  -- unpack the thresholds
  have hK4 : 8 / η ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK1536 : 1536 / (Real.pi * η ^ 2) ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hKCs : 4 * Cs / η ≤ K :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hKCM : 240 * F.Cconst * CM / ε' ≤ K :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)
  have hKL : Lρ ≤ K :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hKT : Tρ ≤ K :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  -- the three small factors
  -- Gallagher budget: the factor is `1 + 4Q^{−1/2}` (was `1 + 2Q^{−1/2}` at the sharp budget);
  -- `design_regime`'s unchanged `2Q^{−1/2} ≤ 1/K` with `K ≥ 8/η` gives `4Q^{−1/2} ≤ η/4`.
  have hf1 : 4 * Real.rpow P.Q (-(1 / 2)) ≤ η / 4 := by
    have h1 : 1 / K ≤ η / 8 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      have := hK4; rw [div_le_iff₀ hη0] at this; linarith
    linarith [hQhalf]
  have hf1' : 0 ≤ 4 * Real.rpow P.Q (-(1 / 2)) := by
    have h0 : (0:ℝ) ≤ P.Q := by linarith [hP.Q_ge]
    have h1 : 0 ≤ Real.rpow P.Q (-(1 / 2)) := Real.rpow_nonneg h0 _
    linarith
  have hf2 : rhoU P Set.univ ≤ η / 4 := by
    have hLρ : Lρ ≤ P.LB := hKL.trans (hlogK.trans (hlogQ.trans (LL_le_LB hP hlam)))
    have hTρ : Tρ ≤ P.T := hKT.trans hTK
    have h := hρ P hP hw (by rw [hcW]) hLρ hTρ
    have hT1536 : 1536 / (Real.pi * η ^ 2) ≤ P.T := hK1536.trans hTK
    have h2 : rhoConstConservative * Real.sqrt (2 / P.T) ≤ η / 4 := by
      unfold rhoConstConservative
      rw [← Real.sqrt_mul (by positivity)]
      have : 48 / Real.pi * (2 / P.T) ≤ (η / 4) ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at hT1536
        rw [show 48 / Real.pi * (2 / P.T) = 96 / (Real.pi * P.T) by rw [div_mul_div_comm]; norm_num,
          div_le_iff₀ (by positivity)]
        nlinarith
      calc Real.sqrt (48 / Real.pi * (2 / P.T)) ≤ Real.sqrt ((η / 4) ^ 2) := Real.sqrt_le_sqrt this
        _ = η / 4 := Real.sqrt_sq (by positivity)
    exact h.trans h2
  have hf2' : 0 ≤ rhoU P Set.univ := rhoU_nonneg P Set.univ MeasurableSet.univ
  have hf3 : Cs / P.T ≤ η / 4 := by
    have hT4 : 4 * Cs / η ≤ P.T := hKCs.trans hTK
    rw [div_le_iff₀ hTpos]
    rw [div_le_iff₀ hη0] at hT4
    linarith
  have hf3' : 0 ≤ Cs / P.T := by positivity
  have hfac := three_factor_le hf1' hf2' hf3' hη0.le hη1 hf1 hf2 hf3
  have hfac0 : 0 ≤ (1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T) := by
    positivity
  -- the algebra
  have hKK := K0_add_K1_le_two (vDesign_admissible hP) hP.lam_lt_two.le
  have hKK0 := K0_add_K1_nonneg (vDesign_admissible hP)
  have hsimp : (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * PPsieve Cs CM (1 / 2) P
      = ((Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * (K0 (vDesign P) + K1 (vDesign P))
          + (Qn : ℝ) ^ 2 * (P.T / Real.pi) * (CM / P.aQ ^ 2))
        * ((1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T)) := by
    unfold PPsieve
    rw [hQ]
    first | (field_simp; ring) | field_simp
  rw [hsimp]
  -- main part
  have hmain : (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * (K0 (vDesign P) + K1 (vDesign P))
        * ((1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T))
      ≤ (F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) + ε' / 16) * NfamQ P F Qn := by
    have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
    calc (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * (K0 (vDesign P) + K1 (vDesign P))
          * ((1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T))
        ≤ (F.Cconst * (1 + η) * NfamQ P F Qn) * (K0 (vDesign P) + K1 (vDesign P)) * (1 + η) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hNs hKK0) hfac hfac0 (by positivity)
      _ = F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) * NfamQ P F Qn
          + F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) * ((1 + η) ^ 2 - 1) * NfamQ P F Qn := by ring
      _ ≤ F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) * NfamQ P F Qn + ε' / 16 * NfamQ P F Qn := by
          gcongr
          have h1 : (1 + η) ^ 2 - 1 ≤ 3 * η := by nlinarith
          have h2 : F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) ≤ 2 * F.Cconst := by nlinarith
          have h3 : 6 * F.Cconst * η ≤ ε' / 16 := by
            have := hη2; rw [le_div_iff₀ (by positivity)] at this; linarith
          calc F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) * ((1 + η) ^ 2 - 1)
              ≤ (2 * F.Cconst) * (3 * η) := by
                apply mul_le_mul h2 h1 (by nlinarith) (by positivity)
            _ ≤ ε' / 16 := by linarith
      _ = _ := by ring
  -- the `C_M` part
  have hCM' : (Qn : ℝ) ^ 2 * (P.T / Real.pi) * (CM / P.aQ ^ 2)
        * ((1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T))
      ≤ ε' / 16 * NfamQ P F Qn := by
    have hKCM' : 240 * F.Cconst * CM ≤ ε' * P.LL := by
      have := hKCM.trans (hlogK.trans hlogQ); rw [div_le_iff₀ hε'] at this; linarith
    have ha2 : CM / P.aQ ^ 2 ≤ 16 / 9 * CM := by
      rw [div_le_iff₀ (by positivity)]
      have : (9 / 16 : ℝ) ≤ P.aQ ^ 2 := by nlinarith
      nlinarith
    have hpi3 : 1 / Real.pi ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hpi (by norm_num)]; linarith [Real.pi_gt_three]
    have h1 : (Qn : ℝ) ^ 2 * (P.T / Real.pi) * (CM / P.aQ ^ 2)
          * ((1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T))
        ≤ (Qn : ℝ) ^ 2 * (P.T / 3) * (16 / 9 * CM) * 2 := by
      have hT3 : P.T / Real.pi ≤ P.T / 3 := by
        rw [div_le_div_iff₀ hpi (by norm_num)]; nlinarith [Real.pi_gt_three]
      apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hT3 (by positivity)) ha2
        (by positivity) (by positivity)) (by linarith) hfac0 (by positivity)
    have hpi4 : Real.pi ≤ 3.1416 := Real.pi_lt_d4.le
    have key2 : (32 / 27 * CM) * (64 * Real.pi * F.Cconst) ≤ ε' * P.LL := by
      have hCMC : CM * (Real.pi * F.Cconst) ≤ CM * (3.1416 * F.Cconst) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpi4 hC.le) hCM.le
      have h0 : 0 ≤ CM * F.Cconst := mul_nonneg hCM.le hC.le
      calc (32 / 27 * CM) * (64 * Real.pi * F.Cconst) = (32 / 27 * 64) * (CM * (Real.pi * F.Cconst)) := by ring
        _ ≤ (32 / 27 * 64) * (CM * (3.1416 * F.Cconst)) := by gcongr
        _ = (32 / 27 * 64 * 3.1416) * (CM * F.Cconst) := by ring
        _ ≤ 240 * (CM * F.Cconst) := by gcongr; norm_num
        _ = 240 * F.Cconst * CM := by ring
        _ ≤ ε' * P.LL := hKCM'
    have h2 : (Qn : ℝ) ^ 2 * (P.T / 3) * (16 / 9 * CM) * 2
        ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := by
      rw [show (Qn : ℝ) ^ 2 * (P.T / 3) * (16 / 9 * CM) * 2
          = ((32 / 27 * CM) * (64 * Real.pi * F.Cconst)) * ((Qn : ℝ) ^ 2 * P.T) / (64 * Real.pi * F.Cconst) by
            first | (field_simp; ring) | field_simp,
        show ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst))
          = (ε' * P.LL) * ((Qn : ℝ) ^ 2 * P.T) / (64 * Real.pi * F.Cconst) by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right key2 (by positivity)) (by positivity)
    calc _ ≤ (Qn : ℝ) ^ 2 * (P.T / 3) * (16 / 9 * CM) * 2 := h1
      _ ≤ ε' / 16 * ((Qn : ℝ) ^ 2 * P.T * P.LL / (4 * Real.pi * F.Cconst)) := h2
      _ ≤ ε' / 16 * NfamQ P F Qn := by gcongr
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  calc ((Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * (K0 (vDesign P) + K1 (vDesign P))
          + (Qn : ℝ) ^ 2 * (P.T / Real.pi) * (CM / P.aQ ^ 2))
        * ((1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T))
      = (Qn : ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL * (K0 (vDesign P) + K1 (vDesign P))
          * ((1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T))
        + (Qn : ℝ) ^ 2 * (P.T / Real.pi) * (CM / P.aQ ^ 2)
          * ((1 + 4 * Real.rpow P.Q (-(1 / 2))) * (1 + rhoU P Set.univ) * (1 + Cs / P.T)) := by ring
    _ ≤ (F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) + ε' / 16) * NfamQ P F Qn
        + ε' / 16 * NfamQ P F Qn := add_le_add hmain hCM'
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **THE EVENTUAL FROBENIUS BOUND WITH THE SIEVE ON BOTH ZONES.**
Along the design of record, for every `ε′ > 0` and all large `Qn`, for every design point `P`
and under Lemma 8.1′ (`hsep`, the family envelope of §8 — threaded, D18 pattern):

  `‖Ĝ_fam‖²_F ≤ ( ψ_{v_design}(0) + C_F·(K0 + K1)(v_design) + ε′ ) · 𝒩`.

`ψ(0) + C_F(K0 + K1)` is `B_{C_F,C_F}(v_design)` = `Bgen C_F C_F` — the §11 functional with the
sieve constant on BOTH zones. The paper's `κ_C = B_{1,C}` (in-zone coefficient 1) needs §5's
in-zone orthogonality for the in-zone form, which is not in the tree. -/
theorem frobenius_sieve_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (∀ τ : ℝ, Bfam Qn P.XQ τ ≤ cMu * P.Q * envSep P τ) →
      frobSqGhatFam P F Qn
        ≤ (psi (vDesign P) 0 + F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) + ε')
            * NfamQ P F Qn := by
  obtain ⟨Cs, CM, hCs, hCM, hexp⟩ := frobSq_le_explicit (cWinDesign F)
  obtain ⟨Lρ, Tρ, hρ⟩ := rhoU_univ_le_pointwise (cWinDesign F)
  set K : ℝ := max 1 (max (Cs + 1) (max ((2 * Real.pi) ^ 2) (2 * Real.pi * Real.exp 8))) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  filter_upwards [A1_eventually F r ε hr hε ε' hε', A2_eventually F r ε hr hε ε' hε',
    A3_eventually F r ε hr hε ε' hε', A4_eventually F r ε hr hε Cs CM Lρ Tρ hCs hCM hρ ε' hε',
    A5_eventually F r ε hr hε ε' hε', design_basic F r ε hr hε,
    design_regime F r ε hr hε K hK1] with Qn h1 h2 h3 h4 h5 hbas hreg
  intro P hdes hsep
  have hP := hdes.1
  have hQ := Q_of_design hdes
  obtain ⟨-, hTK, -, -, -, hX, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hCsT : Cs < P.T := by
    have : Cs + 1 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hT1 : (2 * Real.pi) ^ 2 ≤ P.T :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hTK
  have hT2 : 2 * Real.pi * Real.exp 8 ≤ P.T :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hTK
  have hQnfloor : Qn ≤ ⌊P.Q⌋₊ := by rw [hQ, Nat.floor_natCast]
  have hE := hexp P (1 / 2) F Qn hP hw hL8 (by rw [cWin_of_design hdes]) (by norm_num) (by norm_num)
    hX hCsT hQnfloor hT1 hT2 hsep
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hdist : (P.aQ ^ 2 * P.LB ^ 2)⁻¹
        * (MAIN8chars F P Qn + F.sizeR Qn * err8 P Qn + 2 * R9closed P Qn + PPsieve Cs CM (1 / 2) P)
        + endsMaj P
      = (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * MAIN8chars F P Qn
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (F.sizeR Qn * err8 P Qn)
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * (2 * R9closed P Qn)
        + (P.aQ ^ 2 * P.LB ^ 2)⁻¹ * PPsieve Cs CM (1 / 2) P
        + endsMaj P := by ring
  rw [hdist] at hE
  have ha1 := h1 P hdes
  have ha2 := h2 P hdes
  have ha3 := h3 P hdes
  have ha4 := h4 P hdes
  have ha5 := h5 P hdes
  have hsum : (psi (vDesign P) 0 + ε' / 8) * NfamQ P F Qn + ε' / 8 * NfamQ P F Qn
        + ε' / 8 * NfamQ P F Qn
        + (F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) + ε' / 8) * NfamQ P F Qn
        + ε' / 8 * NfamQ P F Qn
      ≤ (psi (vDesign P) 0 + F.Cconst * (K0 (vDesign P) + K1 (vDesign P)) + ε') * NfamQ P F Qn := by
    nlinarith
  linarith

end PartD2b3
/-! ###################### PART C ######################
The zone comparison `(C−1)·Jzone a v ≤ zoneRowLinear F` for the CONCRETE profile, reduced to a
local Lipschitz bound `ψ_{v_profile}(α) ≤ ψ₁ + c(1−α)` near `α = 1` with margin
`2(C−1)ψ₁ < s_F`, and the eventual comparison along the design (`1 − zoneFactor → 0`).
The secant is the FAMILY's (`Family.sZoneF`: `sZone` for `q ≤ Q`,
`sZoneDyadic` for the dyadic family), so `ZoneLipschitzData` and `zone_compare_eventually_of_data`
serve both families (`ZoneData.zoneLipschitzData_qle`, `ZoneData.zoneLipschitzData_dyadic`).
The numeric certification of `ψ₁ = ψ_{v_profile}(1) ≈ 0.05724` and `c` for
`designProfileQle` is NOT done here (the margin is `0.5073 − 0.5050 = 0.0023`). -/

section PartC

open Filter

/-- the autocorrelation is even, for every `v`. -/
theorem psi_even (v : ℝ → ℝ) (α : ℝ) : psi v (-α) = psi v α := by
  unfold psi
  have h := integral_sub_right_eq_self (μ := volume) (fun t : ℝ => v t * v (t + α)) α
  simp only [sub_add_cancel] at h
  simp only [sub_neg_eq_add]
  rw [← h]
  congr 1; funext s; ring

/-- `∫_a^1 α ψ(α) dα ≤ ψ₁(1−a) + c(1−a)²/2` from `ψ ≤ ψ₁ + c(1−α)` on `[a,1]`. -/
theorem integral_alpha_psi_le {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) {a ψ₁ c : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc : 0 ≤ c)
    (hlip : ∀ α, a ≤ α → α ≤ 1 → psi v α ≤ ψ₁ + c * (1 - α)) :
    ∫ α in a..1, α * psi v α ≤ ψ₁ * (1 - a) + c * (1 - a) ^ 2 / 2 := by
  have hint : IntervalIntegrable (fun α => α * psi v α) volume a 1 := by
    have h := (absPsi_integrable hv).intervalIntegrable (a := a) (b := 1)
    refine h.congr fun x hx => ?_
    rw [Set.uIoc_of_le ha1] at hx
    simp only [abs_of_pos (lt_of_le_of_lt ha0 hx.1)]
  have hbound : ∀ α ∈ Set.Icc a 1, α * psi v α ≤ ψ₁ + c * (1 - α) := by
    intro α hα
    have hψ := psi_nonneg' hv α
    have h1 : α * psi v α ≤ psi v α := by nlinarith [hα.2]
    exact h1.trans (hlip α hα.1 hα.2)
  have hint2 : IntervalIntegrable (fun α : ℝ => ψ₁ + c * (1 - α)) volume a 1 :=
    (by fun_prop : Continuous fun α : ℝ => ψ₁ + c * (1 - α)).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on ha1 hint hint2 hbound
  refine hmono.trans (le_of_eq ?_)
  have hderiv : ∀ x ∈ Set.uIcc a 1,
      HasDerivAt (fun α => ψ₁ * α - c * (1 - α) ^ 2 / 2) (ψ₁ + c * (1 - x)) x := by
    intro x _
    have h1 : HasDerivAt (fun α : ℝ => ψ₁ * α) ψ₁ x := by
      simpa using (hasDerivAt_id x).const_mul ψ₁
    have h2 : HasDerivAt (fun α : ℝ => (1 - α) ^ 2) (2 * (1 - x) * (-1)) x := by
      have h := ((hasDerivAt_id' x).const_sub 1).mul ((hasDerivAt_id' x).const_sub 1)
      have e : (fun α : ℝ => (1 - α) ^ 2) = fun y : ℝ => (1 - y) * (1 - y) := by funext α; ring
      rw [e]
      exact h.congr_deriv (by ring)
    have h3 := h1.sub ((h2.const_mul c).div_const 2)
    refine h3.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
  ring

/-- **The zone comparison from a local Lipschitz bound with margin**: if
`ψ_v(α) ≤ ψ₁ + c(1−α)` on `[a,1]`, `2(C−1)ψ₁ ≤ s − (C−1)c(1−a)` and `0 ≤ a ≤ 1`, then
`(C−1)·Jzone a v ≤ s·(1−a)` (for any secant `s` — `sZone` or `sZoneDyadic`). -/
theorem zone_compare_of_lipschitz {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v)
    {a ψ₁ c C s : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc : 0 ≤ c) (hC : 1 ≤ C)
    (hlip : ∀ α, a ≤ α → α ≤ 1 → psi v α ≤ ψ₁ + c * (1 - α))
    (hmargin : 2 * (C - 1) * ψ₁ + (C - 1) * c * (1 - a) ≤ s) :
    (C - 1) * Jzone a v ≤ s * (1 - a) := by
  rw [Jzone_eq_two_interval hv (psi_even v) ha0 ha1]
  have h := integral_alpha_psi_le hv ha0 ha1 hc hlip
  have hC1 : 0 ≤ C - 1 := by linarith
  have h1a : 0 ≤ 1 - a := by linarith
  calc (C - 1) * (2 * ∫ α in a..1, α * psi v α)
      ≤ (C - 1) * (2 * (ψ₁ * (1 - a) + c * (1 - a) ^ 2 / 2)) := by gcongr
    _ = (2 * (C - 1) * ψ₁ + (C - 1) * c * (1 - a)) * (1 - a) := by ring
    _ ≤ s * (1 - a) := mul_le_mul_of_nonneg_right hmargin h1a

/-- `1 − zoneFactor P ≤ θ` eventually along the design, for every `θ > 0`
(`1 − a = δ′ + (l/ℒ)(1 − δ′)`, `δ′ = 3 log log Q/log Q`, `l/ℒ ≤ (r+ε) log log Q/log Q`). -/
theorem one_sub_zoneFactor_le_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      0 ≤ zoneFactor P ∧ 0 ≤ 1 - zoneFactor P ∧ 1 - zoneFactor P ≤ θ := by
  have hre : (0:ℝ) < r + ε := by linarith
  have h1 : ∀ᶠ x : ℝ in atTop, (2 * (r + ε) / θ) * Real.log x ≤ x :=
    loglog_le_eventually _ (by positivity)
  have h2 : ∀ᶠ x : ℝ in atTop, (6 / θ) * Real.log x ≤ x := loglog_le_eventually _ (by positivity)
  have h3 : ∀ᶠ x : ℝ in atTop, (3:ℝ) * Real.log x ≤ x := loglog_le_eventually 3 (by norm_num)
  filter_upwards [tendsto_log_nat_atTop.eventually h1, tendsto_log_nat_atTop.eventually h2,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (3:ℝ)), design_basic F r ε hr hε,
    tendsto_log_nat_atTop.eventually h3]
    with Qn hx1 hx2 hx3 hbas hx4
  intro P hdes
  have hP := hdes.1
  have hQ := Q_of_design hdes
  have hT := T_of_design hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  have hQn1 : 1 ≤ Qn := by omega
  set x := Real.log (Qn : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hLL0 : 0 < P.LL := by linarith
  have hLLge : x ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  -- δ′ = 3 log x / x ≤ θ/2
  have hδ : P.deltaPrime = 3 * Real.log x / x := by
    unfold ParamsQ.deltaPrime; rw [hQ]
  have hδ0 : 0 ≤ P.deltaPrime := by rw [hδ]; positivity
  have hδθ : P.deltaPrime ≤ θ / 2 := by
    rw [hδ, div_le_iff₀ hx0]
    have := hx2; rw [div_mul_eq_mul_div, div_le_iff₀ hθ] at this
    linarith
  -- l/ℒ ≤ (r+ε) log x / x ≤ θ/2
  have hl0 := l_nonneg hP
  have hl : Zeta23.l P.T ≤ (r + ε) * Real.log x := by
    unfold Zeta23.l
    rw [hT]
    have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc Real.log (x ^ (r + ε) / (2 * Real.pi)) ≤ Real.log (x ^ (r + ε)) :=
          Real.log_le_log (by positivity) (by
            rw [div_le_iff₀ (by positivity)]
            have : 0 ≤ x ^ (r + ε) := by positivity
            nlinarith)
      _ = (r + ε) * Real.log x := Real.log_rpow hx0 _
  have hlL : Zeta23.l P.T / P.LL ≤ θ / 2 := by
    rw [div_le_iff₀ hLL0]
    have := hx1; rw [div_mul_eq_mul_div, div_le_iff₀ hθ] at this
    calc Zeta23.l P.T ≤ (r + ε) * Real.log x := hl
      _ ≤ θ / 2 * x := by linarith
      _ ≤ θ / 2 * P.LL := by gcongr
  have hlL0 : 0 ≤ Zeta23.l P.T / P.LL := by positivity
  have hδ1 : P.deltaPrime ≤ 1 := by
    rw [hδ, div_le_one hx0]; linarith
  have hlL1 : Zeta23.l P.T / P.LL ≤ 1 := by
    rw [div_le_one hLL0]; exact l_le_LL hP
  unfold zoneFactor
  refine ⟨?_, ?_, ?_⟩
  · exact mul_nonneg (by linarith) (by linarith)
  · nlinarith
  · nlinarith

/-- **The eventual zone comparison for a profile family with Lipschitz data.** If every design
point's certified profile satisfies `ψ_{v_profile}(α) ≤ ψ₁ + c(1−α)` on `[0,1]` and the margin
`2(C−1)ψ₁ < s` holds, then eventually along the design
`(C−1)·Jzone (zoneFactor P) (vProfile P) ≤ s·(1 − zoneFactor P)` (any secant `s`; at
`s = F.sZoneF` the right side is `zoneRowLinear F P`). -/
theorem zone_compare_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (C s ψ₁ c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (hmargin : 2 * (C - 1) * ψ₁ < s)
    (hlip : ∀ (Qn : ℕ) (P : ParamsQ), DesignOfRecord F r ε (Qn : ℝ) P →
      ∀ α, 0 ≤ α → α ≤ 1 → psi (vProfile P) α ≤ ψ₁ + c * (1 - α)) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (C - 1) * Jzone (zoneFactor P) (vProfile P) ≤ s * (1 - zoneFactor P) := by
  set θ : ℝ := (s - 2 * (C - 1) * ψ₁) / ((C - 1) * c + 1) with hθdef
  have hC1 : 0 ≤ C - 1 := by linarith
  have hden : 0 < (C - 1) * c + 1 := by positivity
  have hθ : 0 < θ := div_pos (by linarith) hden
  filter_upwards [one_sub_zoneFactor_le_eventually F r ε hr hε θ hθ] with Qn hz
  intro P hdes
  have hP := hdes.1
  obtain ⟨ha0, h0, hθ'⟩ := hz P hdes
  have hv := vProfile_admissible hP
  apply zone_compare_of_lipschitz hv ha0 (by linarith) hc hC
    (fun α ha hα1 => hlip Qn P hdes α (by linarith) hα1)
  -- `2(C−1)ψ₁ + (C−1)c(1−a) ≤ 2(C−1)ψ₁ + (C−1)c·θ ≤ s`
  have h1 : (C - 1) * c * (1 - zoneFactor P) ≤ (C - 1) * c * θ :=
    mul_le_mul_of_nonneg_left hθ' (by positivity)
  have h2 : (C - 1) * c * θ ≤ s - 2 * (C - 1) * ψ₁ := by
    rw [hθdef]
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith [mul_nonneg hC1 hc]
  linarith

/-- **What the concrete profile must satisfy (stated here, certified in `ZetaQ/ZoneData.lean`).**
For `Family.qle` (`C = π⁴/18`): `ψ_{v_profile}(1) ≈ 0.05724` and the margin
`sZone − 2(C−1)ψ(1) ≈ 0.0022`; the local Lipschitz constant near `α = 1` is `c = 1.84`. The
eventual zone comparison then needs `1 − zoneFactor ≲ 2.7·10⁻⁴`.
The margin clause is against the FAMILY's secant `F.sZoneF` (`sZone` for
`q ≤ Q`, `sZoneDyadic` for the dyadic family): against `sZone` the dyadic data is FALSE
(`ZoneData.dyadic_margin_fails`), against `sZoneDyadic` it holds with margin `0.0028`
(`ZoneData.zoneLipschitzData_dyadic`). -/
def ZoneLipschitzData (F : Family) (r ε : ℝ) : Prop :=
  ∃ ψ₁ c : ℝ, 0 ≤ c ∧ 2 * (F.Cconst - 1) * ψ₁ < F.sZoneF ∧
    ∀ (Qn : ℕ) (P : ParamsQ), DesignOfRecord F r ε (Qn : ℝ) P →
      ∀ α, 0 ≤ α → α ≤ 1 → psi (vProfile P) α ≤ ψ₁ + c * (1 - α)

theorem one_le_Cconst (F : Family) : 1 ≤ F.Cconst := by
  have := Ends.pi_four_gt
  cases F <;>
    simp [Family.Cconst, Cfam, CfamDyadic, CfamEven, CfamEvenDyadic] <;> nlinarith

/-- the eventual zone comparison, from `ZoneLipschitzData`, at the family's zone row
`zoneRowLinear F P = F.sZoneF·(1 − zoneFactor P)`. -/
theorem zone_compare_eventually_of_data (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hdata : ZoneLipschitzData F r ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      (F.Cconst - 1) * Jzone (zoneFactor P) (vProfile P) ≤ zoneRowLinear F P := by
  obtain ⟨ψ₁, c, hc, hmargin, hlip⟩ := hdata
  filter_upwards [zone_compare_eventually F r ε hr hε F.Cconst F.sZoneF ψ₁ c (one_le_Cconst F)
    hc hmargin hlip] with Qn h
  intro P hdes
  unfold zoneRowLinear
  exact h P hdes

end PartC

end FrobAssembly
end ZetaQ
