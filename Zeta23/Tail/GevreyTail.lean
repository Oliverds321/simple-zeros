/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/GevreyTail.lean — the Gevrey-2 transform envelope (companion notes, Lemma QT.a)
and the tail chain at a FREE buffer D₀ (QT.b) — the ParamsQ replacement for the record's
inverse-square tail at D₀ = √T.

Part A (this file's first section): **the Gevrey-2 envelope.** For a taper φ with the
`GevreyPhiBound`-interface bounds ‖φ^{(k)}‖₁ ≤ 2Bw·(A/w)^k·k^{2k} (k ≥ 1), support in
[−Λ, Λ] and ‖φ‖₁ ≤ 2Λ, every z ∈ ℂ satisfies

    ‖h_φ(z)‖ ≤ e² · max (2Bw) (2Λ) · e^{|Im z|·Λ} · exp(−(2/e)·√(w‖z‖/A)).

Route (all inputs in tree): k-fold `paperFT_deriv` gives h_{φ^{(k)}}(z) = (−iz)^k h_φ(z);
the zeroth-order bound `norm_paperFT_le` applied to φ^{(k)} gives, for z ≠ 0 and k ≥ 1,
‖h_φ(z)‖ ≤ e^{|Im z|Λ}·2Bw·(k²/r)^k with r := w‖z‖/A; optimize at k = ⌊√r/e⌋ when r ≥ e²
(then (k²/r)^k ≤ e^{−2k} ≤ e²·e^{−(2/e)√r}); for r < e² the zeroth-order bound closes with
the 2Λ branch of the constant since e^{−(2/e)√r} ≥ e^{−2} there. No factor-2 fudge: the
integer floor is absorbed by the r < e² branch and the e² prefactor.
-/
import Zeta23.Tail
import Zeta23.Taper.GevreyPhi
import Zeta23.Taper.GevreyRamps
import Zeta23.WindowD

open Filter Complex MeasureTheory Finset Real
open scoped Topology

noncomputable section

namespace Zeta23
namespace Taper

/-! ### k-fold integration by parts for paperFT -/

/-- Iterated derivatives of a smooth compactly-supported function have compact support. -/
lemma hasCompactSupport_iteratedDeriv {f : ℝ → ℂ} (hsupp : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using hsupp
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- Iterated derivatives of a smooth function are smooth. -/
lemma contDiff_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedDeriv k f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv k hf

/-- k-fold integration by parts: `h_{f^{(k)}}(z) = (−iz)^k · h_f(z)` for smooth
compactly-supported `f` (k-th order form of `paperFT_deriv`). -/
theorem paperFT_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hsupp : HasCompactSupport f) (k : ℕ) (z : ℂ) :
    paperFT (iteratedDeriv k f) z = (-(I * z)) ^ k * paperFT f z := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,
      paperFT_deriv ((contDiff_iteratedDeriv hf n).of_le (mod_cast le_top))
        (hasCompactSupport_iteratedDeriv hsupp n) z, ih]
    ring

/-! ### the Gevrey-2 envelope (Lemma QT.a) -/

/-- **Gevrey-2 transform envelope** (companion notes, Lemma QT.a). `Λ` is the half-support
(`Λ = L/2` for the concrete taper, so `2Λ = L` and the constant is the notes'
`C_env = e²·max(2Bw, L)`). -/
theorem norm_paperFT_le_gevrey {φ : ℝ → ℂ} {Λ A B w : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hw : 0 < w) (hΛ : 0 < Λ)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ Λ)
    (hL1 : ∫ u, ‖φ u‖ ≤ 2 * Λ)
    (hbound : ∀ k : ℕ, 1 ≤ k →
      ∫ u, ‖iteratedDeriv k φ u‖ ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ ((2 : ℝ) * k))
    (z : ℂ) :
    ‖paperFT φ z‖ ≤ Real.exp 2 * max (2 * B * w) (2 * Λ) * Real.exp (|z.im| * Λ)
      * Real.exp (-(2 / Real.exp 1) * Real.sqrt (w * ‖z‖ / A)) := by
  have hcs : HasCompactSupport φ := hasCompactSupport_of_support_subset_abs hsupp
  have hint : Integrable φ := hsm.continuous.integrable_of_hasCompactSupport hcs
  set r : ℝ := w * ‖z‖ / A with hr
  have hr0 : 0 ≤ r := by positivity
  have he1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  by_cases hcase : r < Real.exp 1 ^ 2
  · -- small-r branch: zeroth order, envelope ≥ e^{−2}
    have h0 : ‖paperFT φ z‖ ≤ Real.exp (|z.im| * Λ) * (2 * Λ) := by
      calc ‖paperFT φ z‖ ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖φ u‖ :=
            norm_paperFT_le hint hsupp z
        _ ≤ Real.exp (|z.im| * Λ) * (2 * Λ) := by
            gcongr
    have henv : Real.exp (-(2:ℝ)) ≤ Real.exp (-(2 / Real.exp 1) * Real.sqrt r) := by
      rw [Real.exp_le_exp]
      have hsq : Real.sqrt r ≤ Real.exp 1 := by
        rw [show Real.exp 1 = Real.sqrt (Real.exp 1 ^ 2) by
          rw [Real.sqrt_sq he1.le]]
        exact Real.sqrt_le_sqrt hcase.le
      have h2e : 0 < 2 / Real.exp 1 := by positivity
      calc -(2:ℝ) = -(2 / Real.exp 1) * Real.exp 1 := by field_simp
        _ ≤ -(2 / Real.exp 1) * Real.sqrt r := by
            rw [neg_mul, neg_mul, neg_le_neg_iff]
            exact mul_le_mul_of_nonneg_left hsq h2e.le
    have hone : (1:ℝ) ≤ Real.exp 2 * Real.exp (-(2 / Real.exp 1) * Real.sqrt r) := by
      calc (1:ℝ) = Real.exp 2 * Real.exp (-(2:ℝ)) := by
            rw [← Real.exp_add]; norm_num
        _ ≤ Real.exp 2 * Real.exp (-(2 / Real.exp 1) * Real.sqrt r) :=
            mul_le_mul_of_nonneg_left henv (Real.exp_pos 2).le
    calc ‖paperFT φ z‖ ≤ Real.exp (|z.im| * Λ) * (2 * Λ) := h0
      _ ≤ Real.exp (|z.im| * Λ) * (2 * Λ)
            * (Real.exp 2 * Real.exp (-(2 / Real.exp 1) * Real.sqrt r)) :=
          le_mul_of_one_le_right (by positivity) hone
      _ ≤ Real.exp (|z.im| * Λ) * max (2 * B * w) (2 * Λ)
            * (Real.exp 2 * Real.exp (-(2 / Real.exp 1) * Real.sqrt r)) := by
          gcongr
          exact le_max_right _ _
      _ = Real.exp 2 * max (2 * B * w) (2 * Λ) * Real.exp (|z.im| * Λ)
            * Real.exp (-(2 / Real.exp 1) * Real.sqrt r) := by ring
  · -- large-r branch: optimize k = ⌊√r/e⌋
    push_neg at hcase
    have hz : z ≠ 0 := by
      intro h
      rw [h] at hr
      simp only [norm_zero, mul_zero, zero_div] at hr
      rw [hr] at hcase
      nlinarith [Real.exp_pos 1]
    have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hsqr : Real.exp 1 ≤ Real.sqrt r := by
      rw [show Real.exp 1 = Real.sqrt (Real.exp 1 ^ 2) by rw [Real.sqrt_sq he1.le]]
      exact Real.sqrt_le_sqrt hcase
    set k : ℕ := ⌊Real.sqrt r / Real.exp 1⌋₊ with hkdef
    have hk1 : 1 ≤ k := by
      rw [hkdef, Nat.one_le_floor_iff]
      rw [le_div_iff₀ he1]; linarith [hsqr]
    have hkle : (k : ℝ) ≤ Real.sqrt r / Real.exp 1 :=
      Nat.floor_le (by positivity)
    have hkge : Real.sqrt r / Real.exp 1 - 1 ≤ (k : ℝ) := by
      have := Nat.lt_floor_add_one (Real.sqrt r / Real.exp 1)
      linarith
    -- the k-th order bound
    have hkth : ‖z‖ ^ k * ‖paperFT φ z‖
        ≤ Real.exp (|z.im| * Λ) * (2 * B * w * (A / w) ^ k * (k : ℝ) ^ ((2:ℝ) * k)) := by
      have hid := paperFT_iteratedDeriv hsm hcs k z
      have hsupp' : ∀ u, iteratedDeriv k φ u ≠ 0 → |u| ≤ Λ := by
        intro u hu
        have hmem : u ∈ tsupport (iteratedDeriv k φ) := subset_tsupport _ hu
        have h1 : tsupport (iteratedDeriv k φ) ⊆ tsupport φ := by
          induction k with
          | zero => simp [iteratedDeriv_zero]
          | succ n ih =>
            rw [iteratedDeriv_succ]
            exact Set.Subset.trans (tsupport_deriv_subset) ih
        have h2 : tsupport φ ⊆ Set.Icc (-Λ) Λ :=
          tsupport_subset_of_support_subset_abs hsupp
        have := h2 (h1 hmem)
        rw [Set.mem_Icc] at this
        rw [abs_le]; exact this
      have hint' : Integrable (iteratedDeriv k φ) :=
        (contDiff_iteratedDeriv hsm k).continuous.integrable_of_hasCompactSupport
          (hasCompactSupport_iteratedDeriv hcs k)
      have hb := norm_paperFT_le hint' hsupp' z
      rw [hid, norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul] at hb
      exact hb.trans (by gcongr; exact hbound k hk1)
    have hAwz : (A / (w * ‖z‖)) ^ k * (k : ℝ) ^ ((2:ℝ) * k) ≤ Real.exp 2 *
        Real.exp (-(2 / Real.exp 1) * Real.sqrt r) := by
      -- (k²/r)^k ≤ e^{−2k} ≤ e²·e^{−(2/e)√r}
      have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hcase
      have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
      have hpow : (k : ℝ) ^ ((2:ℝ) * k) = ((k : ℝ) ^ 2) ^ k := by
        rw [show ((2:ℝ) * k) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast, pow_mul]
      have hcomb : (A / (w * ‖z‖)) ^ k * ((k : ℝ) ^ 2) ^ k = ((k : ℝ) ^ 2 / r) ^ k := by
        rw [← mul_pow]
        congr 1
        rw [hr]
        field_simp
      have hk2r : (k : ℝ) ^ 2 / r ≤ (Real.exp 1 ^ 2)⁻¹ := by
        rw [div_le_iff₀ hrpos]
        have h1 : (k : ℝ) ≤ Real.sqrt r / Real.exp 1 := hkle
        have h2 : (k : ℝ) ^ 2 ≤ (Real.sqrt r / Real.exp 1) ^ 2 := by
          apply pow_le_pow_left₀ hk0.le h1
        calc (k : ℝ) ^ 2 ≤ (Real.sqrt r / Real.exp 1) ^ 2 := h2
          _ = r / Real.exp 1 ^ 2 := by
              rw [div_pow, Real.sq_sqrt hrpos.le]
          _ = (Real.exp 1 ^ 2)⁻¹ * r := by ring
      have hstep : ((k : ℝ) ^ 2 / r) ^ k ≤ ((Real.exp 1 ^ 2)⁻¹) ^ k := by
        apply pow_le_pow_left₀ (by positivity) hk2r
      have hexp : ((Real.exp 1 ^ 2)⁻¹) ^ k = Real.exp (-(2 * (k:ℝ))) := by
        have h1 : (Real.exp 1 ^ 2 : ℝ) = Real.exp 2 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [h1, ← Real.exp_neg, ← Real.exp_nat_mul]
        congr 1
        ring
      have hfinal : Real.exp (-(2 * (k:ℝ))) ≤ Real.exp 2 *
          Real.exp (-(2 / Real.exp 1) * Real.sqrt r) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        have : 2 / Real.exp 1 * Real.sqrt r ≤ 2 * ((k:ℝ) + 1) := by
          have h1 : Real.sqrt r / Real.exp 1 ≤ (k:ℝ) + 1 := by linarith [hkge]
          calc 2 / Real.exp 1 * Real.sqrt r = 2 * (Real.sqrt r / Real.exp 1) := by ring
            _ ≤ 2 * ((k:ℝ) + 1) := by linarith [h1]
        linarith
      calc (A / (w * ‖z‖)) ^ k * (k : ℝ) ^ ((2:ℝ) * k)
          = ((k : ℝ) ^ 2 / r) ^ k := by rw [hpow, hcomb]
        _ ≤ ((Real.exp 1 ^ 2)⁻¹) ^ k := hstep
        _ = Real.exp (-(2 * (k:ℝ))) := hexp
        _ ≤ Real.exp 2 * Real.exp (-(2 / Real.exp 1) * Real.sqrt r) := hfinal
    -- assemble
    have hzk : 0 < ‖z‖ ^ k := by positivity
    rw [← le_div_iff₀' hzk] at hkth
    calc ‖paperFT φ z‖
        ≤ Real.exp (|z.im| * Λ) * (2 * B * w * (A / w) ^ k * (k : ℝ) ^ ((2:ℝ) * k)) / ‖z‖ ^ k :=
          hkth
      _ = Real.exp (|z.im| * Λ) * (2 * B * w) *
            ((A / (w * ‖z‖)) ^ k * (k : ℝ) ^ ((2:ℝ) * k)) := by
          have hsplit : (A / w) ^ k / ‖z‖ ^ k = (A / (w * ‖z‖)) ^ k := by
            rw [← div_pow, div_div]
          rw [← hsplit]
          ring
      _ ≤ Real.exp (|z.im| * Λ) * (2 * B * w) *
            (Real.exp 2 * Real.exp (-(2 / Real.exp 1) * Real.sqrt r)) := by
          have : (0:ℝ) ≤ Real.exp (|z.im| * Λ) * (2 * B * w) := by positivity
          exact mul_le_mul_of_nonneg_left hAwz this
      _ ≤ Real.exp (|z.im| * Λ) * max (2 * B * w) (2 * Λ) *
            (Real.exp 2 * Real.exp (-(2 / Real.exp 1) * Real.sqrt r)) := by
          gcongr
          exact le_max_left _ _
      _ = Real.exp 2 * max (2 * B * w) (2 * Λ) * Real.exp (|z.im| * Λ)
            * Real.exp (-(2 / Real.exp 1) * Real.sqrt r) := by ring

end Taper

/-! ### the envelope for the concrete taper `P.phi T` -/

namespace Params

variable {P : Params} {T : ℝ}

/-- ‖φ‖₁ ≤ L for the concrete taper (0 ≤ φ ≤ 1, support in [−L/2, L/2]). -/
lemma integral_norm_phi_le (hP : P.ValidQ) (hwL : 8 * P.w ≤ P.L T) (hL : 0 < P.L T) :
    ∫ u, ‖(P.phi T u : ℂ)‖ ≤ P.L T := by
  have hcont : Continuous (P.phi T) := phi_continuous hP hwL
  have hcs : HasCompactSupport (P.phi T) := phi_hasCompactSupport hP
  have hint : Integrable (fun u => ‖(P.phi T u : ℂ)‖) := by
    simpa using (hcont.norm.integrable_of_hasCompactSupport hcs.norm)
  have hind : Integrable ((Set.Icc (-(P.L T / 2)) (P.L T / 2)).indicator fun _ => (1:ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hmono : ∀ u, ‖(P.phi T u : ℂ)‖
      ≤ (Set.Icc (-(P.L T / 2)) (P.L T / 2)).indicator (fun _ => (1:ℝ)) u := by
    intro u
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (phi_nonneg hP u)]
    by_cases hu : u ∈ Set.Icc (-(P.L T / 2)) (P.L T / 2)
    · rw [Set.indicator_of_mem hu]
      exact phi_le_one hP u
    · rw [Set.indicator_of_notMem hu]
      by_contra h
      push_neg at h
      exact hu (phi_support_subset hP (by simp only [Function.mem_support]; positivity))
  calc ∫ u, ‖(P.phi T u : ℂ)‖
      ≤ ∫ u, (Set.Icc (-(P.L T / 2)) (P.L T / 2)).indicator (fun _ => (1:ℝ)) u :=
        integral_mono hint hind hmono
    _ = P.L T := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
          Real.volume_real_Icc_of_le (by linarith)]
        ring

/-- **QT.a for the concrete taper**: with a Gevrey-2 profile at constants (A, B),
`‖φ̂(z)‖ ≤ e²·max(2Bw, L)·e^{|Im z|·L/2}·exp(−(2/e)√(w‖z‖/A))` for every `z ∈ ℂ`. -/
theorem norm_phiHat_le_gevrey {A B : ℝ} (hϱ : Taper.GevreyProfile 2 A B P.ϱ)
    (hP : P.ValidQ) (hwL : 8 * P.w ≤ P.L T) (hL : 0 < P.L T) (z : ℂ) :
    ‖P.phiHat T z‖ ≤ Real.exp 2 * max (2 * B * P.w) (P.L T)
      * Real.exp (|z.im| * (P.L T / 2))
      * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A)) := by
  have hw : 0 < P.w := w_pos hP
  have h2w : 2 * P.w ≤ P.L T := two_w_le hwL hP
  have hG : P.GevreyPhiBound T 2 A B := P.gevreyPhiBound_of_profile T hϱ hw h2w
  have hsupp : ∀ u, (fun u : ℝ => (P.phi T u : ℂ)) u ≠ 0 → |u| ≤ P.L T / 2 := by
    intro u hu
    have : P.phi T u ≠ 0 := by
      intro h; apply hu; simp [h]
    have hmem := phi_support_subset hP (Function.mem_support.mpr this)
    rw [Set.mem_Icc] at hmem
    rw [abs_le]; exact hmem
  have hbound : ∀ k : ℕ, 1 ≤ k →
      ∫ u, ‖iteratedDeriv k (fun u : ℝ => (P.phi T u : ℂ)) u‖
        ≤ 2 * B * P.w * (A / P.w) ^ k * (k : ℝ) ^ ((2:ℝ) * k) := by
    intro k hk
    exact hG.bound k hk
  have hL1' : ∫ u, ‖(P.phi T u : ℂ)‖ ≤ 2 * (P.L T / 2) := by
    rw [show 2 * (P.L T / 2) = P.L T by ring]
    exact integral_norm_phi_le hP hwL hL
  have h := Taper.norm_paperFT_le_gevrey (Λ := P.L T / 2) hϱ.A_pos hϱ.B_pos hw
    (by linarith) hG.smooth hsupp hL1' hbound z
  calc ‖P.phiHat T z‖
      = ‖paperFT (fun u : ℝ => (P.phi T u : ℂ)) z‖ := rfl
    _ ≤ Real.exp 2 * max (2 * B * P.w) (2 * (P.L T / 2)) * Real.exp (|z.im| * (P.L T / 2))
          * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A)) := h
    _ = _ := by rw [show 2 * (P.L T / 2) = P.L T by ring]

end Params

namespace Tail

/-! ### the exponential-√ sum toolbox (for QT.b(3)–(4))

All grid/window sums below have the shape `∑_k g(x₀ + k·step)` with
`g x = exp(−c·√(b·x))`, `g` antitone. The comparison is the record's own
telescoping-vs-integral style (`Tail/Grid.lean`), with the fourth-power
antiderivative replaced by the explicit primitive
`F x = −(2/b)·e^{−c√(bx)}·(√(bx)/c + 1/c²)`, `F′ = g`, `F ≤ 0`:
`∑_{k<d} g(x₀+k·step) ≤ g x₀ + step⁻¹·(−F x₀)`. -/

section ExpSqrtSums

variable {b c : ℝ}

/-- The primitive: `F x = −(2/b)·e^{−c√(bx)}·(√(bx)/c + 1/c²)` has derivative
`e^{−c√(bx)}` at every `x > 0`. -/
lemma hasDerivAt_expSqrtPrimitive (hb : 0 < b) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(2 / b) * Real.exp (-c * Real.sqrt (b * y))
        * (Real.sqrt (b * y) / c + 1 / c ^ 2))
      (Real.exp (-c * Real.sqrt (b * x))) x := by
  have hbx : 0 < b * x := by positivity
  have hsq : 0 < Real.sqrt (b * x) := Real.sqrt_pos.mpr hbx
  have hu : HasDerivAt (fun y : ℝ => Real.sqrt (b * y)) (b / (2 * Real.sqrt (b * x))) x := by
    have h1 : HasDerivAt (fun y : ℝ => b * y) b x := by
      simpa using (hasDerivAt_id x).const_mul b
    have h2 := (Real.hasDerivAt_sqrt hbx.ne').comp x h1
    have h4 : HasDerivAt (fun y : ℝ => Real.sqrt (b * y))
        (1 / (2 * Real.sqrt (b * x)) * b) x := h2
    exact h4.congr_deriv (by ring)
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-c * Real.sqrt (b * y)))
      (-c * (b / (2 * Real.sqrt (b * x))) * Real.exp (-c * Real.sqrt (b * x))) x := by
    have h3 : HasDerivAt (fun y : ℝ => -c * Real.sqrt (b * y))
        (-c * (b / (2 * Real.sqrt (b * x)))) x := hu.const_mul (-c)
    simpa [mul_comm] using h3.exp
  have hlin : HasDerivAt (fun y : ℝ => Real.sqrt (b * y) / c + 1 / c ^ 2)
      (b / (2 * Real.sqrt (b * x)) / c) x := by
    simpa using (hu.div_const c).add_const (1 / c ^ 2)
  have hmul := (hexp.mul hlin).const_mul (-(2 / b))
  have hfun : (fun y : ℝ => -(2 / b) * Real.exp (-c * Real.sqrt (b * y))
      * (Real.sqrt (b * y) / c + 1 / c ^ 2))
      = (fun y : ℝ => -(2 / b) * (Real.exp (-c * Real.sqrt (b * y))
        * (Real.sqrt (b * y) / c + 1 / c ^ 2))) := by
    funext y; ring
  rw [hfun]
  have hs : Real.sqrt (b * x) ≠ 0 := hsq.ne'
  exact hmul.congr_deriv (by field_simp; ring)

/-- `g x = e^{−c√(bx)}` is antitone on `[x₀, ∞)` for `x₀ ≥ 0`. -/
lemma antitoneOn_expSqrt (hb : 0 < b) (hc : 0 < c) {x₀ : ℝ} (hx₀ : 0 ≤ x₀) :
    AntitoneOn (fun x : ℝ => Real.exp (-c * Real.sqrt (b * x))) (Set.Ici x₀) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  apply Real.exp_le_exp.mpr
  have h1 : Real.sqrt (b * x) ≤ Real.sqrt (b * y) :=
    Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

/-- **Step-sum comparison** (the record's telescoping style, abstract form): for `g`
with primitive `F ≤ 0` on `[x₀, ∞)`, `g` antitone there, `step > 0`:
`∑_{k<d} g(x₀ + k·step) ≤ g x₀ + step⁻¹·(−F x₀)`. -/
lemma sum_step_le_of_primitive {F g : ℝ → ℝ} {x₀ step : ℝ} (hstep : 0 < step)
    (hx₀g : 0 ≤ g x₀) (d : ℕ)
    (hF : ∀ x ∈ Set.Ici x₀, HasDerivAt F (g x) x)
    (hanti : AntitoneOn g (Set.Ici x₀))
    (hFle : ∀ x ∈ Set.Ici x₀, F x ≤ 0) :
    ∑ k ∈ Finset.range d, g (x₀ + k * step) ≤ g x₀ + step⁻¹ * (-(F x₀)) := by
  have hF0 : F x₀ ≤ 0 := hFle x₀ (Set.mem_Ici.mpr le_rfl)
  have htail : 0 ≤ step⁻¹ * (-(F x₀)) := mul_nonneg (by positivity) (by linarith)
  rcases d with - | n
  · simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  set f : ℕ → ℝ := fun i => F (x₀ + i * step) with hfdef
  have key : ∀ i : ℕ, g (x₀ + (i + 1 : ℕ) * step) ≤ step⁻¹ * (f (i + 1) - f i) := by
    intro i
    set a : ℝ := x₀ + i * step with ha
    set b' : ℝ := x₀ + (i + 1 : ℕ) * step with hb'
    have hab : a < b' := by
      rw [ha, hb']
      push_cast
      nlinarith
    have ha0 : x₀ ≤ a := by
      rw [ha]; have : (0:ℝ) ≤ i * step := by positivity
      linarith
    have hb0 : x₀ ≤ b' := ha0.trans hab.le
    have hcont : ContinuousOn F (Set.Icc a b') := fun x hx =>
      ((hF x (Set.mem_Ici.mpr (ha0.trans hx.1))).continuousAt).continuousWithinAt
    have hderiv : ∀ x ∈ Set.Ioo a b', HasDerivAt F (g x) x := fun x hx =>
      hF x (Set.mem_Ici.mpr (ha0.trans hx.1.le))
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope F g hab hcont hderiv
    have hgb : g b' ≤ g ξ :=
      hanti (Set.mem_Ici.mpr (ha0.trans hξ.1.le)) (Set.mem_Ici.mpr hb0) hξ.2.le
    have hba : b' - a = step := by rw [ha, hb']; push_cast; ring
    have hΔ : f (i + 1) - f i = g ξ * step := by
      have h1 : f (i + 1) - f i = F b' - F a := by rw [hfdef, ha, hb']
      rw [h1]
      have h2 : F b' - F a = g ξ * (b' - a) := by
        field_simp [show b' - a ≠ 0 by rw [hba]; exact hstep.ne'] at hslope
        linarith
      rw [h2, hba]
    rw [hΔ]
    calc g (x₀ + (i + 1 : ℕ) * step) = g b' := by rw [hb']
      _ ≤ g ξ := hgb
      _ = step⁻¹ * (g ξ * step) := by field_simp
  calc ∑ k ∈ Finset.range (n + 1), g (x₀ + k * step)
      = (∑ i ∈ Finset.range n, g (x₀ + (i + 1 : ℕ) * step)) + g (x₀ + (0 : ℕ) * step) :=
        Finset.sum_range_succ' _ n
    _ = (∑ i ∈ Finset.range n, g (x₀ + (i + 1 : ℕ) * step)) + g x₀ := by norm_num
    _ ≤ (∑ i ∈ Finset.range n, step⁻¹ * (f (i + 1) - f i)) + g x₀ := by
        gcongr with i hi
        exact key i
    _ = step⁻¹ * (f n - f 0) + g x₀ := by
        rw [← Finset.mul_sum, Finset.sum_range_sub f]
    _ ≤ step⁻¹ * (-(F x₀)) + g x₀ := by
        have hfn : f n ≤ 0 := hFle (x₀ + n * step)
          (Set.mem_Ici.mpr (le_add_of_nonneg_right (by positivity)))
        have hf0 : f 0 = F x₀ := by
          show F (x₀ + (0 : ℕ) * step) = F x₀
          norm_num
        have : f n - f 0 ≤ -(F x₀) := by rw [hf0]; linarith
        gcongr
    _ = g x₀ + step⁻¹ * (-(F x₀)) := by ring

/-- **The exponential-√ step sum, explicit** (all pieces assembled): for `b, c > 0`,
`x₀ > 0`, `step > 0`:
`∑_{k<d} e^{−c√(b(x₀+k·step))} ≤ e^{−c√(bx₀)}·(1 + step⁻¹·(2/b)·(√(bx₀)/c + 1/c²))`. -/
theorem sum_exp_sqrt_le (hb : 0 < b) (hc : 0 < c) {x₀ step : ℝ} (hx₀ : 0 < x₀)
    (hstep : 0 < step) (d : ℕ) :
    ∑ k ∈ Finset.range d, Real.exp (-c * Real.sqrt (b * (x₀ + k * step)))
      ≤ Real.exp (-c * Real.sqrt (b * x₀))
        * (1 + step⁻¹ * (2 / b) * (Real.sqrt (b * x₀) / c + 1 / c ^ 2)) := by
  have h := sum_step_le_of_primitive (F := fun y : ℝ => -(2 / b)
      * Real.exp (-c * Real.sqrt (b * y)) * (Real.sqrt (b * y) / c + 1 / c ^ 2))
    (g := fun y : ℝ => Real.exp (-c * Real.sqrt (b * y))) hstep (Real.exp_pos _).le d
    (fun x hx => hasDerivAt_expSqrtPrimitive hb hc (lt_of_lt_of_le hx₀ hx))
    (antitoneOn_expSqrt hb hc hx₀.le)
    (fun x hx => by
      have h1 : 0 ≤ Real.sqrt (b * x) / c + 1 / c ^ 2 := by positivity
      have h2 : 0 ≤ Real.exp (-c * Real.sqrt (b * x)) := (Real.exp_pos _).le
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 / b) h2) h1])
  calc ∑ k ∈ Finset.range d, Real.exp (-c * Real.sqrt (b * (x₀ + k * step)))
      ≤ Real.exp (-c * Real.sqrt (b * x₀))
        + step⁻¹ * (-(-(2 / b) * Real.exp (-c * Real.sqrt (b * x₀))
            * (Real.sqrt (b * x₀) / c + 1 / c ^ 2))) := h
    _ = Real.exp (-c * Real.sqrt (b * x₀))
        * (1 + step⁻¹ * (2 / b) * (Real.sqrt (b * x₀) / c + 1 / c ^ 2)) := by ring

end ExpSqrtSums

/-! ### the exponential grid row lemma (QT.b(3), mirror of `Tail/Grid.lean grid_sum_le`) -/

section GridExp

open Finset

/-- The row weight `S(D) := 1 + (L/2π)·(2/b)·(√(bD)/c + 1/c²)` of the companion notes'
QT.b(3) (with `b = w/A` at the call sites). -/
def rowS (L b c D : ℝ) : ℝ :=
  1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt (b * D) / c + 1 / c ^ 2)

lemma rowS_nonneg {L b c D : ℝ} (hL : 0 ≤ L) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ rowS L b c D := by
  unfold rowS
  have hπ := Real.pi_pos
  have h1 : 0 ≤ Real.sqrt (b * D) / c + 1 / c ^ 2 := by positivity
  positivity

/-- **Exponential grid estimate** (QT.b(3); mirror of `grid_sum_le` with the exponential
in place of the fourth power): with τ_k := T + k·h, h = 2π/L, d·h ≤ T, L ≥ 2 and
D := dist(γ, I) ≥ 1:  `∑_{k<d} e^{−c√(b|γ−τ_k|)} ≤ e^{−c√(bD)}·S(D)`. -/
theorem grid_sum_exp_le {T L γ b c : ℝ} {d : ℕ} (hL : 2 ≤ L) (hT : 0 < T)
    (hd : (d : ℝ) * (2 * Real.pi / L) ≤ T) (hD : 1 ≤ distI T γ)
    (hb : 0 < b) (hc : 0 < c) :
    ∑ k ∈ range d, Real.exp (-c * Real.sqrt (b * |γ - (T + k * (2 * Real.pi / L))|))
      ≤ Real.exp (-c * Real.sqrt (b * distI T γ)) * rowS L b c (distI T γ) := by
  set h : ℝ := 2 * Real.pi / L with hh_def
  have hLpos : 0 < L := by linarith
  have hπ := Real.pi_pos
  have hh : 0 < h := by rw [hh_def]; positivity
  have hinv : h⁻¹ = L / (2 * Real.pi) := by
    rw [hh_def, inv_div]
  have hbound : ∀ D : ℝ, 1 ≤ D →
      ∑ k ∈ range d, Real.exp (-c * Real.sqrt (b * (D + k * h)))
        ≤ Real.exp (-c * Real.sqrt (b * D)) * rowS L b c D := by
    intro D hD1
    have hD0 : 0 < D := by linarith
    have hs := sum_exp_sqrt_le hb hc hD0 hh d
    calc ∑ k ∈ range d, Real.exp (-c * Real.sqrt (b * (D + k * h)))
        ≤ Real.exp (-c * Real.sqrt (b * D))
          * (1 + h⁻¹ * (2 / b) * (Real.sqrt (b * D) / c + 1 / c ^ 2)) := hs
      _ = Real.exp (-c * Real.sqrt (b * D)) * rowS L b c D := by
          rw [hinv]; rfl
  have hside : 1 ≤ T - γ ∨ 1 ≤ γ - 2 * T := by
    unfold distI at hD
    rcases le_max_iff.mp hD with h0 | h1
    · exact absurd h0 (by norm_num)
    · exact le_max_iff.mp h1
  rcases hside with hlt | hgt
  · have hDeq : distI T γ = T - γ := distI_of_le hT.le (by linarith)
    rw [hDeq] at hD ⊢
    have hterm : ∀ k ∈ range d,
        Real.exp (-c * Real.sqrt (b * |γ - (T + k * h)|))
          = Real.exp (-c * Real.sqrt (b * (T - γ + k * h))) := by
      intro k _
      have hk : 0 ≤ (k : ℝ) * h := by positivity
      congr 3
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [sum_congr rfl hterm]
    exact hbound (T - γ) hD
  · have hDeq : distI T γ = γ - 2 * T := distI_of_ge hT.le (by linarith)
    rw [hDeq] at hD ⊢
    have hD0 : 0 < γ - 2 * T := by linarith
    rw [← sum_range_reflect]
    have hterm : ∀ k ∈ range d,
        Real.exp (-c * Real.sqrt (b * |γ - (T + ((d - 1 - k : ℕ) : ℝ) * h)|))
          ≤ Real.exp (-c * Real.sqrt (b * (γ - 2 * T + k * h))) := by
      intro k hk
      have hkd : k < d := mem_range.mp hk
      have hcast : ((d - 1 - k : ℕ) : ℝ) = d - 1 - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
      rw [hcast]
      have hk0 : 0 ≤ (k : ℝ) * h := by positivity
      have hle : T + ((d : ℝ) - 1 - k) * h ≤ 2 * T - h - k * h := by nlinarith
      have hpos : γ - 2 * T + k * h ≤ γ - (T + ((d : ℝ) - 1 - k) * h) := by linarith
      have hpos2 : 0 < γ - 2 * T + k * h := by linarith
      rw [Real.exp_le_exp, abs_of_pos (by linarith)]
      have hsq : Real.sqrt (b * (γ - 2 * T + k * h))
          ≤ Real.sqrt (b * (γ - (T + ((d : ℝ) - 1 - k) * h))) :=
        Real.sqrt_le_sqrt (by nlinarith)
      nlinarith
    exact (sum_le_sum hterm).trans (hbound (γ - 2 * T) hD)

end GridExp


/-! ### QT.b(1)–(2): entry decay for tail zeros at a free buffer, Gevrey shape -/

section EntryG

open Finset

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- The tail predicate at a FREE buffer `D` (mirror of `InTail`, which fixes `D = √T`).
`InTailD T (Real.sqrt T) = InTail T`. -/
def InTailD (T D γ : ℝ) : Prop := γ ≤ T - D ∨ 2 * T + D < γ

lemma inTailD_sqrtT (T γ : ℝ) : InTailD T (Real.sqrt T) γ ↔ InTail T γ := Iff.rfl

/-- `D ≤ dist(γ, I)` for a tail zero at buffer `D` (mirror of `sqrt_le_distI_of_InTail`). -/
lemma le_distI_of_InTailD {T D γ : ℝ} (hT : 0 ≤ T) (hD : 0 ≤ D) (h : InTailD T D γ) :
    D ≤ distI T γ := by
  rcases h with h | h
  · rw [distI_of_le hT (by linarith)]; linarith
  · rw [distI_of_ge hT (by linarith)]; linarith

/-- **QT.b(1), entry bound**: with the Gevrey-shape decay hypothesis
`‖φ̂(r − iy)‖ ≤ Kg·e^{−c√(b|r|)}` (|y| ≤ 1/2), every entry of `u_ρ` for a zero in the
strip satisfies `‖u_ρ(k)‖ ≤ Kg·e^{−c√(b|γ−τ_k|)}`. (No `r ≠ 0` side condition: the
Gevrey envelope holds in the full plane.) -/
lemma norm_uvec_le_gevrey {Kg b c : ℝ}
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 →
        ‖P.phiHat T ((r : ℂ) - Complex.I * (y : ℂ))‖
          ≤ Kg * Real.exp (-c * Real.sqrt (b * |r|)))
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (k : Fin (P.d T)) :
    ‖uvec P T ρ k‖
      ≤ Kg * Real.exp (-c * Real.sqrt (b * |ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))|)) := by
  set r : ℝ := ρ.im - P.tau T k with hr
  set y : ℝ := ρ.re - 1 / 2 with hy
  have hstrip := Z.strip ρ hρ
  have hyab : |y| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have heq : uvec P T ρ k = P.phiHat T ((r : ℂ) - Complex.I * (y : ℂ)) := by
    unfold uvec; rw [gammaOf_sub_ofReal]
  rw [heq, ← tau_fin, ← hr]
  exact hdecay r y hyab

/-- **QT.b(2)+(3), the row bound, two-factor**: `∑_k ‖u_ρ(k)‖² ≤ Kg²·e^{−2c√(bD)}·S(D)`
at `D := dist(γ, I) ≥ 1`, where `S = rowS L b (2c)`. Mirror of `norm_sq_uvec_le` with the
exponential row lemma in place of the fourth-power grid estimate; the squared entries
carry BOTH taper factors (the record's own two-factor convention, `Tail.lean:229`). -/
lemma norm_sq_uvec_le_gevrey (hT : T₀ ≤ T) (hL : 2 ≤ P.L T) {Kg b c : ℝ}
    (hKg : 0 ≤ Kg) (hb : 0 < b) (hc : 0 < c)
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 →
        ‖P.phiHat T ((r : ℂ) - Complex.I * (y : ℂ))‖
          ≤ Kg * Real.exp (-c * Real.sqrt (b * |r|)))
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hdist : 1 ≤ distI T ρ.im) :
    ∑ k, ‖uvec P T ρ k‖ ^ 2
      ≤ Kg ^ 2 * Real.exp (-(2 * c) * Real.sqrt (b * distI T ρ.im))
          * rowS (P.L T) b (2 * c) (distI T ρ.im) := by
  have hT' : (300 : ℝ) ≤ T := hT
  have hL0 : 0 < P.L T := by linarith
  calc ∑ k, ‖uvec P T ρ k‖ ^ 2
      ≤ ∑ k : Fin (P.d T), Kg ^ 2
          * Real.exp (-(2 * c) * Real.sqrt (b * |ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))|)) := by
        refine sum_le_sum fun k _ => ?_
        have h := norm_uvec_le_gevrey (Z := Z) hdecay hρ k
        set S : ℝ := Real.sqrt (b * |ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))|) with hS
        have h2 : ‖uvec P T ρ k‖ ^ 2 ≤ (Kg * Real.exp (-c * S)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
        have h3 : (Kg * Real.exp (-c * S)) ^ 2 = Kg ^ 2 * Real.exp (-(2 * c) * S) := by
          rw [mul_pow, sq (Real.exp (-c * S)), ← Real.exp_add]
          congr 2
          ring
        exact h2.trans_eq h3
    _ = Kg ^ 2 * ∑ k ∈ range (P.d T),
          Real.exp (-(2 * c) * Real.sqrt (b * |ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))|)) := by
        rw [mul_sum, Fin.sum_univ_eq_sum_range
          (fun k : ℕ => Kg ^ 2 * Real.exp (-(2 * c)
            * Real.sqrt (b * |ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))|)))]
    _ ≤ Kg ^ 2 * (Real.exp (-(2 * c) * Real.sqrt (b * distI T ρ.im))
          * rowS (P.L T) b (2 * c) (distI T ρ.im)) :=
        mul_le_mul_of_nonneg_left
          (grid_sum_exp_le hL (by linarith) (d_mul_hgrid_le hL0 (by linarith)) hdist hb
            (by positivity)) (by positivity)
    _ = _ := by ring

end EntryG

/-! ### monomial exponential sums (QT.b(4) toolbox): `∑ (√(bx))^k e^{−c√(bx)}`

`gammaPoly c u k` is the incomplete-Γ antiderivative polynomial:
`d/du (−e^{−cu}·gammaPoly c u k) = u^k e^{−cu}`. Pulled back through `u = √(bx)`
(and scaled by `2/b`) it is the primitive of `(√(bx))^k·e^{−c√(bx)}`. -/

section GammaPoly

variable {b c : ℝ}

/-- The antiderivative polynomial: `∫ u^k e^{−cu} du = −e^{−cu}·gammaPoly c u k`. -/
def gammaPoly (c u : ℝ) : ℕ → ℝ
  | 0 => 1 / c
  | k + 1 => u ^ (k + 1) / c + ((k + 1 : ℕ) : ℝ) / c * gammaPoly c u k

lemma gammaPoly_nonneg (hc : 0 < c) {u : ℝ} (hu : 0 ≤ u) : ∀ k, 0 ≤ gammaPoly c u k
  | 0 => by unfold gammaPoly; positivity
  | (k + 1) => by
      unfold gammaPoly
      have h1 : (0:ℝ) ≤ u ^ (k + 1) / c := by positivity
      have h2 : (0:ℝ) ≤ ((k + 1 : ℕ) : ℝ) / c := by positivity
      have h3 := gammaPoly_nonneg hc hu k
      nlinarith

lemma gammaPoly_mono (hc : 0 < c) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∀ k, gammaPoly c u k ≤ gammaPoly c v k
  | 0 => le_rfl
  | (k + 1) => by
      unfold gammaPoly
      have h1 : u ^ (k + 1) ≤ v ^ (k + 1) := pow_le_pow_left₀ hu huv _
      have h2 : (0:ℝ) ≤ ((k + 1 : ℕ) : ℝ) / c := by positivity
      have h3 := mul_le_mul_of_nonneg_left (gammaPoly_mono hc hu huv k) h2
      have h4 : u ^ (k + 1) / c ≤ v ^ (k + 1) / c := by
        gcongr
      linarith

/-- `d/du (−e^{−cu}·gammaPoly c u k) = u^k·e^{−cu}`. -/
lemma hasDerivAt_gammaPrimitive (hc : 0 < c) : ∀ (k : ℕ) (u : ℝ),
    HasDerivAt (fun v : ℝ => -Real.exp (-c * v) * gammaPoly c v k)
      (u ^ k * Real.exp (-c * u)) u
  | 0, u => by
      have h1 : HasDerivAt (fun v : ℝ => Real.exp (-c * v)) (-c * Real.exp (-c * u)) u := by
        simpa [mul_comm] using ((hasDerivAt_id u).const_mul (-c)).exp
      have h2 := h1.const_mul (-(1/c) : ℝ)
      have he : (fun v : ℝ => -Real.exp (-c * v) * gammaPoly c v 0)
          = fun v : ℝ => -(1/c) * Real.exp (-c * v) := by
        funext v; show -Real.exp (-c * v) * (1 / c) = _; ring
      rw [he]
      exact h2.congr_deriv (by field_simp)
  | (k + 1), u => by
      have hpow : HasDerivAt (fun v : ℝ => v ^ (k + 1))
          (((k + 1 : ℕ) : ℝ) * u ^ k) u := by
        simpa using hasDerivAt_pow (k + 1) u
      have h1 : HasDerivAt (fun v : ℝ => Real.exp (-c * v)) (-c * Real.exp (-c * u)) u := by
        simpa [mul_comm] using ((hasDerivAt_id u).const_mul (-c)).exp
      have hp1 : HasDerivAt (fun v : ℝ => -(1/c) * (Real.exp (-c * v) * v ^ (k + 1)))
          (-(1/c) * ((-c * Real.exp (-c * u)) * u ^ (k + 1)
            + Real.exp (-c * u) * (((k + 1 : ℕ) : ℝ) * u ^ k))) u :=
        (h1.mul hpow).const_mul (-(1/c))
      have hp2 : HasDerivAt (fun v : ℝ => ((k + 1 : ℕ) : ℝ) / c
            * (-Real.exp (-c * v) * gammaPoly c v k))
          (((k + 1 : ℕ) : ℝ) / c * (u ^ k * Real.exp (-c * u))) u :=
        (hasDerivAt_gammaPrimitive hc k u).const_mul _
      have hsum := hp1.add hp2
      have he : (fun v : ℝ => -(1/c) * (Real.exp (-c * v) * v ^ (k + 1))
            + ((k + 1 : ℕ) : ℝ) / c * (-Real.exp (-c * v) * gammaPoly c v k))
          = fun v : ℝ => -Real.exp (-c * v) * gammaPoly c v (k + 1) := by
        funext v
        show _ = -Real.exp (-c * v) * (v ^ (k + 1) / c + ((k + 1 : ℕ) : ℝ) / c * gammaPoly c v k)
        ring
      rw [← he]
      exact hsum.congr_deriv (by field_simp; ring)

/-- Pullback: `d/dx [(2/b)·(−e^{−c√(bx)}·gammaPoly c (√(bx)) (k+1))] = (√(bx))^k·e^{−c√(bx)}`
for `x > 0`. -/
lemma hasDerivAt_monoPrimitive (hb : 0 < b) (hc : 0 < c) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (2 / b)
        * (-Real.exp (-c * Real.sqrt (b * y)) * gammaPoly c (Real.sqrt (b * y)) (k + 1)))
      ((Real.sqrt (b * x)) ^ k * Real.exp (-c * Real.sqrt (b * x))) x := by
  have hbx : 0 < b * x := by positivity
  have hsq : 0 < Real.sqrt (b * x) := Real.sqrt_pos.mpr hbx
  have hu : HasDerivAt (fun y : ℝ => Real.sqrt (b * y)) (b / (2 * Real.sqrt (b * x))) x := by
    have h1 : HasDerivAt (fun y : ℝ => b * y) b x := by
      simpa using (hasDerivAt_id x).const_mul b
    have h2 := (Real.hasDerivAt_sqrt hbx.ne').comp x h1
    have h4 : HasDerivAt (fun y : ℝ => Real.sqrt (b * y))
        (1 / (2 * Real.sqrt (b * x)) * b) x := h2
    exact h4.congr_deriv (by ring)
  have hcomp := (hasDerivAt_gammaPrimitive hc (k + 1) (Real.sqrt (b * x))).comp x hu
  have := hcomp.const_mul (2 / b)
  refine this.congr_deriv ?_
  rw [pow_succ]
  field_simp
  all_goals ring

/-- Antitonicity of `x ↦ (√(bx))^k·e^{−c√(bx)}` past the peak `√(bx₀) ≥ k/c`
(via `log(v/u) ≤ (v−u)/u`). -/
lemma antitoneOn_monoExpSqrt (hb : 0 < b) (hc : 0 < c) (k : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hpeak : (k : ℝ) / c ≤ Real.sqrt (b * x₀)) :
    AntitoneOn (fun x : ℝ => (Real.sqrt (b * x)) ^ k * Real.exp (-c * Real.sqrt (b * x)))
      (Set.Ici x₀) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  set u : ℝ := Real.sqrt (b * x) with hudef
  have hxpos : 0 < x := hx₀.trans_le hx
  set v : ℝ := Real.sqrt (b * y) with hvdef
  have hu0 : 0 < u := Real.sqrt_pos.mpr (mul_pos hb hxpos)
  have huv : u ≤ v := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxy hb.le)
  have hupeak : (k : ℝ) / c ≤ u :=
    hpeak.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hx hb.le))
  -- v^k ≤ u^k · e^{c(v−u)}
  have hlog : Real.log (v / u) ≤ (v - u) / u := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hu0.trans_le huv) hu0)
    have h2 : v / u - 1 = (v - u) / u := by field_simp
    linarith
  have hkey : (k : ℝ) * Real.log (v / u) ≤ c * (v - u) := by
    have h3 : (k : ℝ) * Real.log (v / u) ≤ (k : ℝ) * ((v - u) / u) :=
      mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
    have hku : (k : ℝ) ≤ c * u := by
      rw [div_le_iff₀ hc] at hupeak
      linarith
    have h4 : (k : ℝ) * ((v - u) / u) ≤ c * (v - u) := by
      have hvu : 0 ≤ v - u := by linarith
      have expand : (k : ℝ) * ((v - u) / u) = ((k : ℝ) * (v - u)) / u := by ring
      rw [expand, div_le_iff₀ hu0]
      nlinarith [mul_le_mul_of_nonneg_right hku hvu]
    linarith
  have hvk : v ^ k ≤ u ^ k * Real.exp (c * (v - u)) := by
    have hvu0 : 0 < v / u := div_pos (hu0.trans_le huv) hu0
    have h5 : v ^ k = u ^ k * (v / u) ^ k := by
      rw [div_pow]; field_simp
    rw [h5]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (v / u) ^ k = Real.exp ((k : ℝ) * Real.log (v / u)) := by
          rw [← Real.log_rpow hvu0, Real.exp_log (by positivity)]
          rw [← Real.rpow_natCast (v / u) k]
      _ ≤ Real.exp (c * (v - u)) := Real.exp_le_exp.mpr hkey
  calc v ^ k * Real.exp (-c * v)
      ≤ (u ^ k * Real.exp (c * (v - u))) * Real.exp (-c * v) :=
        mul_le_mul_of_nonneg_right hvk (Real.exp_pos _).le
    _ = u ^ k * Real.exp (-c * u) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

end GammaPoly

/-! ### the monomial window sum (QT.b(4) core) -/

section MonoWindow

open Finset

variable {b c : ℝ}

/-- `√(x+y+z) ≤ √x + √y + √z` for nonnegative arguments. -/
lemma sqrt_add_le3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hsz := Real.sq_sqrt hz
  have h1 : x + y + z ≤ (Real.sqrt x + Real.sqrt y + Real.sqrt z) ^ 2 := by
    have h2 : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
    have h3 : 0 ≤ Real.sqrt x * Real.sqrt z := by positivity
    have h4 : 0 ≤ Real.sqrt y * Real.sqrt z := by positivity
    nlinarith
  calc Real.sqrt (x + y + z) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y + Real.sqrt z) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt x + Real.sqrt y + Real.sqrt z := Real.sqrt_sq (by positivity)

/-- The collected monomial window weight: everything explicit, full rate. -/
def monoW (b c D : ℝ) (k : ℕ) : ℝ :=
  (((k : ℝ) / c) ^ 2 / b + 3)
      * (Real.sqrt (b * D) + (k : ℝ) / c + Real.sqrt b) ^ k
    + (2 / b) * gammaPoly c (Real.sqrt (b * D) + (k : ℝ) / c + Real.sqrt b) (k + 1)

lemma monoW_nonneg (hb : 0 < b) (hc : 0 < c) {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    0 ≤ monoW b c D k := by
  unfold monoW
  have h1 : (0:ℝ) ≤ Real.sqrt (b * D) + (k : ℝ) / c + Real.sqrt b := by positivity
  have h2 := gammaPoly_nonneg hc h1 (k + 1)
  have h3 : (0:ℝ) ≤ (((k : ℝ) / c) ^ 2 / b + 3) := by positivity
  have h4 : (0:ℝ) ≤ (Real.sqrt (b * D) + (k : ℝ) / c + Real.sqrt b) ^ k := by positivity
  have h5 : (0:ℝ) ≤ 2 / b := by positivity
  nlinarith [mul_nonneg h3 h4, mul_nonneg h5 h2]

/-- **Monomial window-sum bound** (full rate): for window keys `j` with `D ≤ j + 1`
(`D ≥ 1`), `∑_j (√(b·max(D,j)))^k·e^{−c√(b·max(D,j))} ≤ e^{−c√(bD)}·monoW b c D k`. -/
theorem sum_mono_window_le (hb : 0 < b) (hc : 0 < c) {D : ℝ} (hD : 1 ≤ D) (k : ℕ)
    (F : Finset ℕ) (hF : ∀ j ∈ F, D ≤ (j : ℝ) + 1) :
    ∑ j ∈ F, (Real.sqrt (b * max D (j : ℝ))) ^ k
        * Real.exp (-c * Real.sqrt (b * max D (j : ℝ)))
      ≤ Real.exp (-c * Real.sqrt (b * D)) * monoW b c D k := by
  classical
  set tD : ℝ := Real.sqrt (b * D) with htD
  set M : ℝ := tD + (k : ℝ) / c + Real.sqrt b with hM
  have hD0 : 0 < D := by linarith
  have htD0 : 0 ≤ tD := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  -- generic per-term facts
  have hu_ge : ∀ j : ℕ, tD ≤ Real.sqrt (b * max D (j : ℝ)) := fun j =>
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_max_left _ _) hb.le)
  have hexp_le : ∀ j : ℕ, Real.exp (-c * Real.sqrt (b * max D (j : ℝ)))
      ≤ Real.exp (-c * tD) := fun j => by
    rw [Real.exp_le_exp]
    nlinarith [hu_ge j]
  -- the split point
  set peak2 : ℝ := ((k : ℝ) / c) ^ 2 / b with hpeak2
  have hpeak2_0 : 0 ≤ peak2 := by rw [hpeak2]; positivity
  set jstar : ℕ := ⌈max D peak2⌉₊ with hjstar
  have hjstar_ge : max D peak2 ≤ (jstar : ℝ) := Nat.le_ceil _
  have hjstar_le : (jstar : ℝ) ≤ max D peak2 + 1 :=
    (Nat.ceil_lt_add_one (le_trans hD0.le (le_max_left _ _))).le
  have hjstarD : D ≤ (jstar : ℝ) := (le_max_left _ _).trans hjstar_ge
  have hjstar_pos : 0 < (jstar : ℝ) := lt_of_lt_of_le hD0 hjstarD
  -- bound b * (anything ≤ max D peak2 + 1) inside √ by M
  have hsqrt_M : ∀ x : ℝ, 0 ≤ x → x ≤ max D peak2 + 1 → Real.sqrt (b * x) ≤ M := by
    intro x hx hxle
    have h1 : b * x ≤ b * D + ((k : ℝ) / c) ^ 2 + b := by
      have h2 : max D peak2 ≤ D + peak2 := max_le (by linarith) (by linarith)
      have h3 : b * x ≤ b * (D + peak2 + 1) := by nlinarith
      have h4 : b * peak2 = ((k : ℝ) / c) ^ 2 := by
        rw [hpeak2]; field_simp
      nlinarith
    calc Real.sqrt (b * x) ≤ Real.sqrt (b * D + ((k : ℝ) / c) ^ 2 + b) :=
          Real.sqrt_le_sqrt h1
      _ ≤ Real.sqrt (b * D) + Real.sqrt (((k : ℝ) / c) ^ 2) + Real.sqrt b :=
          sqrt_add_le3 (by positivity) (by positivity) hb.le
      _ = M := by
          rw [hM, htD, Real.sqrt_sq (by positivity)]
  -- split F
  set Fpre := F.filter (fun j => j < jstar) with hFpre
  set Fpost := F.filter (fun j => ¬ j < jstar) with hFpost
  have hsplit : ∑ j ∈ F, (Real.sqrt (b * max D (j : ℝ))) ^ k
        * Real.exp (-c * Real.sqrt (b * max D (j : ℝ)))
      = (∑ j ∈ Fpre, (Real.sqrt (b * max D (j : ℝ))) ^ k
          * Real.exp (-c * Real.sqrt (b * max D (j : ℝ))))
        + ∑ j ∈ Fpost, (Real.sqrt (b * max D (j : ℝ))) ^ k
          * Real.exp (-c * Real.sqrt (b * max D (j : ℝ))) :=
    (sum_filter_add_sum_filter_not F _ _).symm
  -- ── pre-peak: each term ≤ M^k·e^{−c·tD}, count ≤ peak2 + 2
  have hpre : ∑ j ∈ Fpre, (Real.sqrt (b * max D (j : ℝ))) ^ k
        * Real.exp (-c * Real.sqrt (b * max D (j : ℝ)))
      ≤ (peak2 + 2) * (M ^ k * Real.exp (-c * tD)) := by
    have hterm : ∀ j ∈ Fpre, (Real.sqrt (b * max D (j : ℝ))) ^ k
        * Real.exp (-c * Real.sqrt (b * max D (j : ℝ))) ≤ M ^ k * Real.exp (-c * tD) := by
      intro j hj
      rw [hFpre, mem_filter] at hj
      have hjlt : (j : ℝ) < jstar := by exact_mod_cast hj.2
      have hmaxle : max D (j : ℝ) ≤ max D peak2 + 1 := by
        rcases le_total (j : ℝ) D with h | h
        · rw [max_eq_left h]; linarith [le_max_left D peak2]
        · rw [max_eq_right h]
          linarith [hjstar_le]
      have h1 : Real.sqrt (b * max D (j : ℝ)) ≤ M :=
        hsqrt_M _ (le_trans hD0.le (le_max_left _ _)) hmaxle
      have h2 := hexp_le j
      have h3 : (Real.sqrt (b * max D (j : ℝ))) ^ k ≤ M ^ k :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 k
      have h4 : (0:ℝ) ≤ (Real.sqrt (b * max D (j : ℝ))) ^ k := by positivity
      nlinarith [Real.exp_pos (-c * Real.sqrt (b * max D (j : ℝ)))]
    have hcard : (Fpre.card : ℝ) ≤ peak2 + 2 := by
      set jlo : ℕ := ⌈D⌉₊ - 1 with hjlo
      have hsub : Fpre ⊆ Finset.Ico jlo jstar := by
        intro j hj
        rw [hFpre, mem_filter] at hj
        rw [Finset.mem_Ico]
        constructor
        · have := hF j hj.1
          have hceil : ⌈D⌉₊ ≤ j + 1 := Nat.ceil_le.mpr (by push_cast; linarith)
          omega
        · exact hj.2
      have h5 : Fpre.card ≤ jstar - jlo := by
        have := Finset.card_le_card hsub
        rwa [Nat.card_Ico] at this
      by_cases hle : jlo ≤ jstar
      · have h6 : ((jstar - jlo : ℕ) : ℝ) = (jstar : ℝ) - jlo := by
          rw [Nat.cast_sub hle]
        have h7 : (Fpre.card : ℝ) ≤ (jstar : ℝ) - jlo := by
          rw [← h6]; exact_mod_cast h5
        have h8 : D - 1 ≤ (jlo : ℝ) := by
          rw [hjlo]
          have hceil1 : 1 ≤ ⌈D⌉₊ := Nat.one_le_ceil_iff.mpr hD0
          rw [Nat.cast_sub hceil1]
          have := Nat.le_ceil D
          push_cast
          linarith
        have h9 : (jstar : ℝ) ≤ max D peak2 + 1 := hjstar_le
        have h10 : max D peak2 ≤ D + peak2 := max_le (by linarith) (by linarith)
        linarith
      · push_neg at hle
        have h0 : jstar - jlo = 0 := by omega
        rw [h0] at h5
        have h00 : Fpre.card = 0 := by omega
        rw [h00]
        push_cast
        linarith
    calc ∑ j ∈ Fpre, (Real.sqrt (b * max D (j : ℝ))) ^ k
          * Real.exp (-c * Real.sqrt (b * max D (j : ℝ)))
        ≤ ∑ _j ∈ Fpre, M ^ k * Real.exp (-c * tD) := sum_le_sum hterm
      _ = (Fpre.card : ℝ) * (M ^ k * Real.exp (-c * tD)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (peak2 + 2) * (M ^ k * Real.exp (-c * tD)) := by
          apply mul_le_mul_of_nonneg_right hcard (by positivity)
  -- ── post-peak: consecutive comparison with the pulled-back primitive
  have hpost : ∑ j ∈ Fpost, (Real.sqrt (b * max D (j : ℝ))) ^ k
        * Real.exp (-c * Real.sqrt (b * max D (j : ℝ)))
      ≤ M ^ k * Real.exp (-c * tD)
        + (2 / b) * (Real.exp (-c * tD) * gammaPoly c M (k + 1)) := by
    -- on Fpost, max D j = j
    have hmax_eq : ∀ j ∈ Fpost, max D (j : ℝ) = (j : ℝ) := by
      intro j hj
      rw [hFpost, mem_filter] at hj
      have : jstar ≤ j := by omega
      have : (jstar : ℝ) ≤ j := by exact_mod_cast this
      exact max_eq_right (by linarith [hjstarD])
    set g : ℝ → ℝ := fun x => (Real.sqrt (b * x)) ^ k * Real.exp (-c * Real.sqrt (b * x))
      with hg
    have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hg]; positivity
    set N : ℕ := F.sup id with hN
    have hsubI : Fpost ⊆ Finset.Ico jstar (N + 1) := by
      intro j hj
      rw [hFpost, mem_filter] at hj
      rw [Finset.mem_Ico]
      exact ⟨by omega, Nat.lt_succ_of_le (Finset.le_sup (f := id) hj.1)⟩
    have hstep1 : ∑ j ∈ Fpost, g (j : ℝ) ≤ ∑ j ∈ Finset.Ico jstar (N + 1), g (j : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsubI (fun j _ _ => hg0 _)
    have hstep2 : ∑ j ∈ Finset.Ico jstar (N + 1), g (j : ℝ)
        = ∑ i ∈ range (N + 1 - jstar), g ((jstar : ℝ) + i * 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    have hpeak_j : (k : ℝ) / c ≤ Real.sqrt (b * (jstar : ℝ)) := by
      have h1 : peak2 ≤ (jstar : ℝ) := (le_max_right D peak2).trans hjstar_ge
      have h2 : ((k : ℝ) / c) ^ 2 ≤ b * (jstar : ℝ) := by
        rw [hpeak2] at h1
        calc ((k : ℝ) / c) ^ 2 = b * (((k : ℝ) / c) ^ 2 / b) := by field_simp
          _ ≤ b * (jstar : ℝ) := by nlinarith
      calc (k : ℝ) / c = Real.sqrt (((k : ℝ) / c) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (b * (jstar : ℝ)) := Real.sqrt_le_sqrt h2
    have hprim := sum_step_le_of_primitive
      (F := fun y : ℝ => (2 / b)
        * (-Real.exp (-c * Real.sqrt (b * y)) * gammaPoly c (Real.sqrt (b * y)) (k + 1)))
      (g := g) one_pos (hg0 _) (N + 1 - jstar)
      (fun x hx => hasDerivAt_monoPrimitive hb hc k (lt_of_lt_of_le hjstar_pos hx))
      (by
        have := antitoneOn_monoExpSqrt hb hc k hjstar_pos hpeak_j
        exact this)
      (fun x hx => by
        have h1 : 0 ≤ gammaPoly c (Real.sqrt (b * x)) (k + 1) :=
          gammaPoly_nonneg hc (Real.sqrt_nonneg _) (k + 1)
        have h2 : (0:ℝ) ≤ Real.exp (-c * Real.sqrt (b * x)) := (Real.exp_pos _).le
        have h3 : (0:ℝ) ≤ 2 / b := by positivity
        nlinarith [mul_nonneg h2 h1, mul_nonneg h3 (mul_nonneg h2 h1)])
    have hustar_le : Real.sqrt (b * (jstar : ℝ)) ≤ M :=
      hsqrt_M _ hjstar_pos.le hjstar_le
    have hustar_ge : tD ≤ Real.sqrt (b * (jstar : ℝ)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hjstarD hb.le)
    have hgj : g (jstar : ℝ) ≤ M ^ k * Real.exp (-c * tD) := by
      rw [hg]
      have h1 : (Real.sqrt (b * (jstar : ℝ))) ^ k ≤ M ^ k :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hustar_le k
      have h2 : Real.exp (-c * Real.sqrt (b * (jstar : ℝ))) ≤ Real.exp (-c * tD) := by
        rw [Real.exp_le_exp]; nlinarith
      nlinarith [Real.exp_pos (-c * Real.sqrt (b * (jstar : ℝ))),
        pow_nonneg (Real.sqrt_nonneg (b * (jstar : ℝ))) k]
    have hFj : (1 : ℝ)⁻¹ * (-((2 / b)
          * (-Real.exp (-c * Real.sqrt (b * (jstar : ℝ)))
            * gammaPoly c (Real.sqrt (b * (jstar : ℝ))) (k + 1))))
        ≤ (2 / b) * (Real.exp (-c * tD) * gammaPoly c M (k + 1)) := by
      rw [inv_one, one_mul]
      have h1 : -((2 / b) * (-Real.exp (-c * Real.sqrt (b * (jstar : ℝ)))
            * gammaPoly c (Real.sqrt (b * (jstar : ℝ))) (k + 1)))
          = (2 / b) * (Real.exp (-c * Real.sqrt (b * (jstar : ℝ)))
            * gammaPoly c (Real.sqrt (b * (jstar : ℝ))) (k + 1)) := by ring
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 2 / b)
      have h2 : Real.exp (-c * Real.sqrt (b * (jstar : ℝ))) ≤ Real.exp (-c * tD) := by
        rw [Real.exp_le_exp]; nlinarith
      have h3 : gammaPoly c (Real.sqrt (b * (jstar : ℝ))) (k + 1) ≤ gammaPoly c M (k + 1) :=
        gammaPoly_mono hc (Real.sqrt_nonneg _) hustar_le (k + 1)
      have h4 := gammaPoly_nonneg hc (Real.sqrt_nonneg (b * (jstar : ℝ))) (k + 1)
      nlinarith [Real.exp_pos (-c * Real.sqrt (b * (jstar : ℝ))), Real.exp_pos (-c * tD)]
    calc ∑ j ∈ Fpost, (Real.sqrt (b * max D (j : ℝ))) ^ k
          * Real.exp (-c * Real.sqrt (b * max D (j : ℝ)))
        = ∑ j ∈ Fpost, g (j : ℝ) := by
          apply sum_congr rfl
          intro j hj
          rw [hg, hmax_eq j hj]
      _ ≤ ∑ i ∈ range (N + 1 - jstar), g ((jstar : ℝ) + i * 1) := hstep2 ▸ hstep1
      _ ≤ g (jstar : ℝ) + (1 : ℝ)⁻¹ * (-((2 / b)
            * (-Real.exp (-c * Real.sqrt (b * (jstar : ℝ)))
              * gammaPoly c (Real.sqrt (b * (jstar : ℝ))) (k + 1)))) := hprim
      _ ≤ M ^ k * Real.exp (-c * tD)
            + (2 / b) * (Real.exp (-c * tD) * gammaPoly c M (k + 1)) :=
          add_le_add hgj hFj
  -- ── combine
  rw [hsplit]
  have := add_le_add hpre hpost
  calc _ ≤ (peak2 + 2) * (M ^ k * Real.exp (-c * tD))
        + (M ^ k * Real.exp (-c * tD)
          + (2 / b) * (Real.exp (-c * tD) * gammaPoly c M (k + 1))) := this
    _ = Real.exp (-c * tD) * ((peak2 + 3) * M ^ k + (2 / b) * gammaPoly c M (k + 1)) := by
        ring
    _ = Real.exp (-c * Real.sqrt (b * D)) * monoW b c D k := by
        rw [htD, hM, hpeak2]
        rfl

end MonoWindow

/-! ### the collected tail row-sum (QT.b(4)) -/

section SideW

open Finset

variable {b c : ℝ}

/-- `√(x+y) ≤ √x + √y`. -/
lemma sqrt_add_le2 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h1 : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h2 : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-- The one-side collected weight (`rowS ≤ α + β·u` on each unit window,
`log(B+j) ≤ log B + u²/(bB)`; the four monomial sums collected by `monoW`). -/
def sideW (L b c B D : ℝ) : ℝ :=
  (1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2)) * Real.log B
      * monoW b c D 0
    + (L / (2 * Real.pi) * (2 / b) / c) * Real.log B * monoW b c D 1
    + (1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2)) / (b * B)
      * monoW b c D 2
    + (L / (2 * Real.pi) * (2 / b) / c) / (b * B) * monoW b c D 3

lemma sideW_nonneg {L : ℝ} (hL : 0 ≤ L) (hb : 0 < b) (hc : 0 < c) {B D : ℝ} (hB : 1 ≤ B)
    (hD : 0 ≤ D) : 0 ≤ sideW L b c B D := by
  unfold sideW
  have hπ := Real.pi_pos
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have h0 := monoW_nonneg hb hc hD 0
  have h1 := monoW_nonneg hb hc hD 1
  have h2 := monoW_nonneg hb hc hD 2
  have h3 := monoW_nonneg hb hc hD 3
  have hα : (0:ℝ) ≤ 1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2) := by
    positivity
  have hβ : (0:ℝ) ≤ L / (2 * Real.pi) * (2 / b) / c := by positivity
  have hbB : (0:ℝ) < b * B := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hα hlogB) h0, mul_nonneg (mul_nonneg hβ hlogB) h1,
    mul_nonneg (div_nonneg hα hbB.le) h2, mul_nonneg (div_nonneg hβ hbB.le) h3]

/-- **One side of the tail, exponential weights** (mirror of `one_side_sum_le`): zeros at
distance `x_ρ ≥ D` beyond an endpoint of I, grouped by an integer key with
`key ≤ x ≤ key + 1`, each group counted by `A₀·log(B + key)`:
`∑ m_ρ·e^{−c√(b·x_ρ)}·rowS(x_ρ) ≤ A₀·e^{−c√(bD)}·sideW`. -/
lemma one_side_exp_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (m : ι → ℕ) (key : ι → ℕ)
    {A₀ B D L : ℝ} (hA₀ : 0 ≤ A₀) (hB : 1 ≤ B) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hb : 0 < b) (hc : 0 < c)
    (hx : ∀ ρ ∈ s, D ≤ x ρ) (hkey_le : ∀ ρ ∈ s, (key ρ : ℝ) ≤ x ρ)
    (hkey_ge : ∀ ρ ∈ s, x ρ ≤ key ρ + 1)
    (hcount : ∀ j : ℕ, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ A₀ * Real.log (B + j)) :
    ∑ ρ ∈ s, (m ρ : ℝ) * (Real.exp (-c * Real.sqrt (b * x ρ)) * rowS L b c (x ρ))
      ≤ A₀ * (Real.exp (-c * Real.sqrt (b * D)) * sideW L b c B D) := by
  classical
  have hπ := Real.pi_pos
  have hB0 : (0:ℝ) < B := by linarith
  have hD0 : (0:ℝ) < D := by linarith
  set α : ℝ := 1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2) with hα
  set β : ℝ := L / (2 * Real.pi) * (2 / b) / c with hβ
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  -- the per-key envelope value
  have envkey : ∀ j : ℕ,
      (0:ℝ) ≤ Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
        * (α + β * Real.sqrt (b * max D (j:ℝ))) := by
    intro j
    have := Real.sqrt_nonneg (b * max D (j:ℝ))
    have h1 : 0 ≤ α + β * Real.sqrt (b * max D (j:ℝ)) := by nlinarith
    nlinarith [Real.exp_pos (-c * Real.sqrt (b * max D (j:ℝ)))]
  -- fiberwise
  rw [← sum_fiberwise_of_maps_to (g := key) (t := s.image key)
    (fun ρ hρ => mem_image_of_mem key hρ)]
  have hfiber : ∀ j ∈ s.image key,
      ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * x ρ)) * rowS L b c (x ρ))
        ≤ A₀ * Real.log (B + j)
            * (Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
              * (α + β * Real.sqrt (b * max D (j:ℝ)))) := by
    intro j _
    have henv : ∀ ρ ∈ s.filter (fun ρ => key ρ = j),
        Real.exp (-c * Real.sqrt (b * x ρ)) * rowS L b c (x ρ)
          ≤ Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
            * (α + β * Real.sqrt (b * max D (j:ℝ))) := by
      intro ρ hρ
      rw [mem_filter] at hρ
      obtain ⟨hρs, hρj⟩ := hρ
      have hxρD : D ≤ x ρ := hx ρ hρs
      have hxρ0 : (0:ℝ) ≤ x ρ := by linarith
      have hxmax : max D (j : ℝ) ≤ x ρ := by
        refine max_le hxρD ?_
        have := hkey_le ρ hρs
        rw [hρj] at this
        exact this
      have hxup : x ρ ≤ (j : ℝ) + 1 := by
        have := hkey_ge ρ hρs
        rw [hρj] at this
        exact this
      have hexp : Real.exp (-c * Real.sqrt (b * x ρ))
          ≤ Real.exp (-c * Real.sqrt (b * max D (j:ℝ))) := by
        rw [Real.exp_le_exp]
        have h1 := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxmax hb.le)
        nlinarith
      have hrow : rowS L b c (x ρ) ≤ α + β * Real.sqrt (b * max D (j:ℝ)) := by
        have hsq : Real.sqrt (b * x ρ) ≤ Real.sqrt (b * max D (j:ℝ)) + Real.sqrt b := by
          have h1 : b * x ρ ≤ b * max D (j:ℝ) + b := by
            have h2 : x ρ ≤ max D (j:ℝ) + 1 := by
              rcases le_total (x ρ) ((j:ℝ)) with h | h
              · linarith [le_max_right D (j:ℝ)]
              · linarith [le_max_right D (j:ℝ)]
            nlinarith
          calc Real.sqrt (b * x ρ) ≤ Real.sqrt (b * max D (j:ℝ) + b) :=
                Real.sqrt_le_sqrt h1
            _ ≤ Real.sqrt (b * max D (j:ℝ)) + Real.sqrt b :=
                sqrt_add_le2 (by positivity) hb.le
        have hgoal : rowS L b c (x ρ)
            ≤ 1 + L / (2 * Real.pi) * (2 / b)
              * ((Real.sqrt (b * max D (j:ℝ)) + Real.sqrt b) / c + 1 / c ^ 2) := by
          unfold rowS
          gcongr
        refine hgoal.trans (le_of_eq ?_)
        rw [hα, hβ]
        ring
      have hrow0 : 0 ≤ rowS L b c (x ρ) := rowS_nonneg hL hb hc
      exact mul_le_mul hexp hrow hrow0 (Real.exp_pos _).le
    calc ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * x ρ)) * rowS L b c (x ρ))
        ≤ ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
            * (α + β * Real.sqrt (b * max D (j:ℝ)))) := by
          apply sum_le_sum
          intro ρ hρ
          exact mul_le_mul_of_nonneg_left (henv ρ hρ) (Nat.cast_nonneg _)
      _ = (∑ ρ ∈ s with key ρ = j, (m ρ : ℝ))
          * (Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
            * (α + β * Real.sqrt (b * max D (j:ℝ)))) := by
          rw [← sum_mul]
      _ ≤ A₀ * Real.log (B + j)
          * (Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
            * (α + β * Real.sqrt (b * max D (j:ℝ)))) :=
          mul_le_mul_of_nonneg_right (hcount j) (envkey j)
  refine (sum_le_sum hfiber).trans ?_
  -- keys satisfy D ≤ j + 1
  have hkeysF : ∀ j ∈ s.image key, D ≤ (j : ℝ) + 1 := by
    intro j hj
    obtain ⟨ρ, hρ, rfl⟩ := mem_image.mp hj
    exact (hx ρ hρ).trans (hkey_ge ρ hρ)
  -- per-key: log(B+j)·env ≤ (log B + u²/(bB))·env, then expand into the four monomials
  have hperkey : ∀ j ∈ s.image key,
      A₀ * Real.log (B + j)
          * (Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
            * (α + β * Real.sqrt (b * max D (j:ℝ))))
        ≤ A₀ * (α * Real.log B
              * ((Real.sqrt (b * max D (j:ℝ))) ^ 0
                * Real.exp (-c * Real.sqrt (b * max D (j:ℝ))))
            + β * Real.log B
              * ((Real.sqrt (b * max D (j:ℝ))) ^ 1
                * Real.exp (-c * Real.sqrt (b * max D (j:ℝ))))
            + α / (b * B)
              * ((Real.sqrt (b * max D (j:ℝ))) ^ 2
                * Real.exp (-c * Real.sqrt (b * max D (j:ℝ))))
            + β / (b * B)
              * ((Real.sqrt (b * max D (j:ℝ))) ^ 3
                * Real.exp (-c * Real.sqrt (b * max D (j:ℝ))))) := by
    intro j _
    have hu0 : (0:ℝ) ≤ Real.sqrt (b * max D (j:ℝ)) := Real.sqrt_nonneg _
    have husq : (j : ℝ) ≤ (Real.sqrt (b * max D (j:ℝ))) ^ 2 / b := by
      rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ b * max D (j:ℝ))]
      rw [mul_comm, mul_div_assoc, div_self hb.ne', mul_one]
      exact le_max_right _ _
    have hlog : Real.log (B + j) ≤ Real.log B
        + (Real.sqrt (b * max D (j:ℝ))) ^ 2 / (b * B) := by
      calc Real.log (B + j) ≤ Real.log B + (j : ℝ) / B :=
            log_add_le_log_add_div hB0 (Nat.cast_nonneg j)
        _ ≤ Real.log B + (Real.sqrt (b * max D (j:ℝ))) ^ 2 / (b * B) := by
            have h1 : (j : ℝ) / B ≤ (Real.sqrt (b * max D (j:ℝ))) ^ 2 / b / B := by
              gcongr
            have h2 : (Real.sqrt (b * max D (j:ℝ))) ^ 2 / b / B
                = (Real.sqrt (b * max D (j:ℝ))) ^ 2 / (b * B) := by ring
            linarith
    have hstep : A₀ * Real.log (B + j)
        * (Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
          * (α + β * Real.sqrt (b * max D (j:ℝ))))
        ≤ A₀ * ((Real.log B + (Real.sqrt (b * max D (j:ℝ))) ^ 2 / (b * B))
          * (Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
            * (α + β * Real.sqrt (b * max D (j:ℝ))))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hlog (envkey j)) hA₀
    refine hstep.trans (le_of_eq ?_)
    ring
  refine (sum_le_sum hperkey).trans ?_
  -- distribute and apply the four monomial window sums
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hbB : (0:ℝ) < b * B := by nlinarith
  have hm0 := sum_mono_window_le hb hc hD 0 (s.image key) hkeysF
  have hm1 := sum_mono_window_le hb hc hD 1 (s.image key) hkeysF
  have hm2 := sum_mono_window_le hb hc hD 2 (s.image key) hkeysF
  have hm3 := sum_mono_window_le hb hc hD 3 (s.image key) hkeysF
  have c0 : (0:ℝ) ≤ α * Real.log B := mul_nonneg hα0 hlogB
  have c1 : (0:ℝ) ≤ β * Real.log B := mul_nonneg hβ0 hlogB
  have c2 : (0:ℝ) ≤ α / (b * B) := div_nonneg hα0 hbB.le
  have c3 : (0:ℝ) ≤ β / (b * B) := div_nonneg hβ0 hbB.le
  have hdistrib : ∑ j ∈ s.image key, A₀ * (α * Real.log B
          * ((Real.sqrt (b * max D (j:ℝ))) ^ 0
            * Real.exp (-c * Real.sqrt (b * max D (j:ℝ))))
        + β * Real.log B
          * ((Real.sqrt (b * max D (j:ℝ))) ^ 1
            * Real.exp (-c * Real.sqrt (b * max D (j:ℝ))))
        + α / (b * B)
          * ((Real.sqrt (b * max D (j:ℝ))) ^ 2
            * Real.exp (-c * Real.sqrt (b * max D (j:ℝ))))
        + β / (b * B)
          * ((Real.sqrt (b * max D (j:ℝ))) ^ 3
            * Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))))
      = A₀ * (α * Real.log B * ∑ j ∈ s.image key, (Real.sqrt (b * max D (j:ℝ))) ^ 0
            * Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
        + β * Real.log B * ∑ j ∈ s.image key, (Real.sqrt (b * max D (j:ℝ))) ^ 1
            * Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
        + α / (b * B) * ∑ j ∈ s.image key, (Real.sqrt (b * max D (j:ℝ))) ^ 2
            * Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))
        + β / (b * B) * ∑ j ∈ s.image key, (Real.sqrt (b * max D (j:ℝ))) ^ 3
            * Real.exp (-c * Real.sqrt (b * max D (j:ℝ)))) := by
    rw [← mul_sum]
    congr 1
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib,
      ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
  rw [hdistrib]
  have t0 := mul_le_mul_of_nonneg_left hm0 c0
  have t1 := mul_le_mul_of_nonneg_left hm1 c1
  have t2 := mul_le_mul_of_nonneg_left hm2 c2
  have t3 := mul_le_mul_of_nonneg_left hm3 c3
  have hsum4 := add_le_add (add_le_add (add_le_add t0 t1) t2) t3
  refine (mul_le_mul_of_nonneg_left hsum4 hA₀).trans (le_of_eq ?_)
  unfold sideW
  rw [hα, hβ]
  ring

end SideW

/-! ### the two-sided tail row-sum (QT.b(4), collected) -/

section TwoSided

open Finset

variable {b c : ℝ}

/-- **Zero-count row-sum at a free buffer** (mirror of `tail_count_sum_le`): for `T ≥ T₀`,
`1 ≤ D`, and every finite set of tail-at-`D` zeros,
`∑ m_ρ·e^{−c√(b·dist(γ_ρ,I))}·rowS(dist(γ_ρ,I)) ≤ 2·A₀·e^{−c√(bD)}·sideW(L,b,c,2T+4,D)`. -/
theorem tail_rowsum_exp_le {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T D L : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hb : 0 < b) (hc : 0 < c)
    (s : Finset ι) (hs : ∀ ρ ∈ s, InTailD T D (γ ρ)) :
    ∑ ρ ∈ s, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * distI T (γ ρ))) * rowS L b c (distI T (γ ρ)))
      ≤ 2 * A₀ * (Real.exp (-c * Real.sqrt (b * D)) * sideW L b c (2 * T + 4) D) := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA₀ : 0 ≤ A₀ := hN.A₀_pos.le
  set B : ℝ := 2 * T + 4 with hBdef
  have hB : (1 : ℝ) ≤ B := by rw [hBdef]; linarith
  -- split s into the lower side (γ ≤ T − D, includes all γ ≤ 0) and the upper side
  set slo := s.filter (fun ρ => γ ρ ≤ T - D) with hslo
  set shi := s.filter (fun ρ => ¬ γ ρ ≤ T - D) with hshi
  have hshi_mem : ∀ ρ ∈ shi, 2 * T + D < γ ρ := by
    intro ρ hρ
    rw [hshi, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact absurd h hρ.2
    · exact h
  have hsplit : ∑ ρ ∈ s, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * distI T (γ ρ))) * rowS L b c (distI T (γ ρ)))
      = (∑ ρ ∈ slo, (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * distI T (γ ρ))) * rowS L b c (distI T (γ ρ))))
        + ∑ ρ ∈ shi, (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * distI T (γ ρ))) * rowS L b c (distI T (γ ρ))) :=
    (sum_filter_add_sum_filter_not s _ _).symm
  have hlogmono : ∀ (t : ℝ) (j : ℕ), |t| + 3 ≤ B + j →
      A₀ * Real.log (|t| + 3) ≤ A₀ * Real.log (B + j) := fun t j h =>
    mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) h) hA₀
  ---------------- lower side: x = T − γ, key = ⌊T − γ⌋₊ ----------------
  have hlo : ∑ ρ ∈ slo, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * distI T (γ ρ))) * rowS L b c (distI T (γ ρ)))
      ≤ A₀ * (Real.exp (-c * Real.sqrt (b * D)) * sideW L b c B D) := by
    have hmem : ∀ ρ ∈ slo, γ ρ ≤ T - D := fun ρ hρ => (mem_filter.mp hρ).2
    have e : ∀ ρ ∈ slo, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * distI T (γ ρ))) * rowS L b c (distI T (γ ρ)))
        = (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * (T - γ ρ))) * rowS L b c (T - γ ρ)) := by
      intro ρ hρ
      rw [distI_of_le hT0 (by linarith [hmem ρ hρ, hD])]
    rw [sum_congr rfl e]
    apply one_side_exp_sum_le slo (fun ρ => T - γ ρ) m (fun ρ => ⌊T - γ ρ⌋₊)
      hA₀ hB hD hL hb hc
    · intro ρ hρ; linarith [hmem ρ hρ]
    · intro ρ hρ; exact Nat.floor_le (by linarith [hmem ρ hρ, hD])
    · intro ρ hρ; exact (Nat.lt_floor_add_one _).le
    · intro j
      refine (hN.window (T - j - 1) _ ?_).trans (hlogmono _ _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hnn : 0 ≤ T - γ ρ := by linarith [hmem ρ hρs, hD]
        have := (Nat.floor_eq_iff hnn).mp hρj
        constructor <;> linarith [this.1, this.2]
      · have : |T - j - 1| ≤ T + j + 1 := by
          rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
        rw [hBdef]; linarith
  ---------------- upper side: x = γ − 2T, key = ⌈γ − 2T⌉₊ − 1 ----------------
  have hhi : ∑ ρ ∈ shi, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * distI T (γ ρ))) * rowS L b c (distI T (γ ρ)))
      ≤ A₀ * (Real.exp (-c * Real.sqrt (b * D)) * sideW L b c B D) := by
    have hmem := hshi_mem
    have e : ∀ ρ ∈ shi, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * distI T (γ ρ))) * rowS L b c (distI T (γ ρ)))
        = (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * (γ ρ - 2 * T))) * rowS L b c (γ ρ - 2 * T)) := by
      intro ρ hρ
      rw [distI_of_ge hT0 (by linarith [hmem ρ hρ, hD])]
    rw [sum_congr rfl e]
    have hceil1 : ∀ ρ ∈ shi, 1 ≤ ⌈γ ρ - 2 * T⌉₊ := fun ρ hρ =>
      Nat.one_le_ceil_iff.mpr (by linarith [hmem ρ hρ, hD])
    have hcast : ∀ ρ ∈ shi, (((⌈γ ρ - 2 * T⌉₊ - 1 : ℕ) : ℝ)) = ⌈γ ρ - 2 * T⌉₊ - 1 :=
      fun ρ hρ => by rw [Nat.cast_sub (hceil1 ρ hρ)]; simp
    apply one_side_exp_sum_le shi (fun ρ => γ ρ - 2 * T) m (fun ρ => ⌈γ ρ - 2 * T⌉₊ - 1)
      hA₀ hB hD hL hb hc
    · intro ρ hρ; linarith [hmem ρ hρ]
    · intro ρ hρ
      rw [hcast ρ hρ]
      have := Nat.ceil_lt_add_one (show 0 ≤ γ ρ - 2 * T by linarith [hmem ρ hρ, hD])
      linarith
    · intro ρ hρ
      rw [hcast ρ hρ]
      have := Nat.le_ceil (γ ρ - 2 * T)
      linarith
    · intro j
      refine (hN.window (2 * T + j) _ ?_).trans (hlogmono _ _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hc1 : ⌈γ ρ - 2 * T⌉₊ = j + 1 := by have := hceil1 ρ hρs; omega
        have := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc1
        push_cast at this
        constructor <;> linarith [this.1, this.2]
      · rw [abs_of_nonneg (by positivity), hBdef]; linarith
  ---------------- combine ----------------
  rw [hsplit]
  calc _ ≤ A₀ * (Real.exp (-c * Real.sqrt (b * D)) * sideW L b c B D)
        + A₀ * (Real.exp (-c * Real.sqrt (b * D)) * sideW L b c B D) := add_le_add hlo hhi
    _ = 2 * A₀ * (Real.exp (-c * Real.sqrt (b * D)) * sideW L b c B D) := by ring

end TwoSided

/-! ### the free-buffer tail split and the Gevrey tail hypotheses (QT.b packaging) -/

section TailHypG

open Finset

/-- `InTailD` is the complement of the `ZIprimeD` window. -/
lemma InTailD_iff_not_mem_Ioc (T D γ : ℝ) :
    InTailD T D γ ↔ γ ∉ Set.Ioc (T - D) (2 * T + D) := by
  simp only [InTailD, Set.mem_Ioc, not_and_or, not_lt, not_le]

/-- The non-tail set at a free buffer is finite (mirror of `finite_notTail`). -/
lemma finite_notTailD (Z : ZeroConfig) (T D : ℝ) :
    {ρ : Z.carrier | ¬ InTailD T D (ρ : ℂ).im}.Finite := by
  have hfin : (Z.ZIprimeD T D).Finite := Z.finite_window _ _
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro ρ hρ
  simp only [Set.mem_setOf_eq, InTailD, not_or, not_le, not_lt] at hρ
  exact ⟨ρ.2, hρ.1, hρ.2⟩

end TailHypG

end Tail

/-! ### the matrix split at a free buffer: `AzD`, `EzD` -/

namespace ZeroConfig

variable (Z : ZeroConfig) (P : Params) (T D : ℝ)

/-- `A(D)_{kl}` — the finite part of the Gram series over `𝒵(I′(D))` (mirror of `Az`). -/
noncomputable def AzD : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  fun k l => ∑ᶠ ρ ∈ Z.ZIprimeD T D, Z.Gsummand P T k l ρ

lemma AzD_sqrtT : Z.AzD P T (D0 T) = Z.Az P T := rfl

/-- `E(D) := G − A(D)` — the tail matrix at a free buffer (mirror of `Ez`). -/
noncomputable def EzD : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  Z.Gz P T - Z.AzD P T D

lemma EzD_sqrtT : Z.EzD P T (D0 T) = Z.Ez P T := rfl

end ZeroConfig

namespace Tail

/-- **Standing hypotheses of the Gevrey tail at a free buffer** (mirror of `TailHyp`;
`hdecay` carries the QT.a Gevrey envelope in place of the record's inverse square,
and the buffer `D` is free with only `1 ≤ D` as regime fact). `A, Cenv` are the
Gevrey profile constants (`A = 36/e`, `Cenv = e²·max(2Bw, L)` at the design profile). -/
structure TailHypG (Z : ZeroConfig) (P : Params) (T A₀ A Cenv D : ℝ) : Prop where
  hT : T₀ ≤ T
  hL : 2 ≤ P.L T
  hA₀ : 1 ≤ A₀
  /-- PaperInputs.RvM.local (two-sided unit-window local count). -/
  hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
  hA : 0 < A
  hCenv : 0 ≤ Cenv
  hw : 0 < P.w
  hD : 1 ≤ D
  /-- the QT.a envelope for φ̂ on the strip, in terms of the real distance `|r|`. -/
  hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 →
    ‖P.phiHat T ((r : ℂ) - Complex.I * (y : ℂ))‖
      ≤ (Real.exp (P.L T / 4) * Cenv)
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w / A * |r|))

/-- The collected tail bound at a free buffer, in the record's `θ₀`-slot normalisation
(`∑_tail m_ρ‖u_ρ‖² ≤ L·θ₀G`): explicit, full rate `e^{−(4/e)√(wD/A)}`. -/
noncomputable def theta0G (P : Params) (T A₀ A Cenv D : ℝ) : ℝ :=
  (Real.exp (P.L T / 4) * Cenv) ^ 2 * (2 * A₀
      * (Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w / A * D))
        * sideW (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D))
    / P.L T

namespace TailHypG

open Finset

variable {Z : ZeroConfig} {P : Params} {T A₀ A Cenv D : ℝ}
variable (H : TailHypG Z P T A₀ A Cenv D)
include H

lemma T_pos : 0 < T := by have h : (300:ℝ) ≤ T := H.hT; linarith
lemma L_pos : 0 < P.L T := by linarith [H.hL]
lemma A₀_nonneg : 0 ≤ A₀ := by linarith [H.hA₀]
lemma b_pos : 0 < P.w / A := div_pos H.hw H.hA
lemma c2_pos : (0:ℝ) < 2 / Real.exp 1 := by positivity

/-- the zeros of `𝒵(I′(D))` as a Finset of the carrier subtype. -/
noncomputable def sAD (_ : TailHypG Z P T A₀ A Cenv D) : Finset Z.carrier :=
  (finite_notTailD Z T D).toFinset

lemma not_mem_sAD_iff (ρ : Z.carrier) : ρ ∉ H.sAD ↔ InTailD T D (ρ : ℂ).im := by
  rw [sAD, Set.Finite.mem_toFinset]; simp

/-- `K_G := e^{L/4}·C_env` (the Gevrey analogue of the record's `K = e^{L/4}C₁`). -/
def K (_ : TailHypG Z P T A₀ A Cenv D) : ℝ := Real.exp (P.L T / 4) * Cenv

lemma K_nonneg : 0 ≤ H.K := by unfold K; have := H.hCenv; positivity

/-- **QT.b(1)–(4) combined** (mirror of `partial_sum_le`): finite partial sums over
tail-at-`D` zeros satisfy `∑ m_ρ ‖u_ρ‖₂² ≤ L·θ₀G`. -/
lemma partial_sum_leG (u : Finset {ρ : Z.carrier // ρ ∉ H.sAD}) :
    ∑ x ∈ u, (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ P.L T * theta0G P T A₀ A Cenv D := by
  classical
  have hLC := LocalCount.ofWindowCount Z H.hA₀ H.hloc
  have hb := H.b_pos
  have hc := H.c2_pos
  have hL0 := H.L_pos
  -- push u forward to a Finset of the carrier; all its elements are tail zeros
  set s : Finset Z.carrier := u.map (Function.Embedding.subtype _) with hs
  have hs_tail : ∀ ρ ∈ s, InTailD T D ((fun ρ : Z.carrier => (ρ : ℂ).im) ρ) := by
    intro ρ hρ
    rw [hs, Finset.mem_map] at hρ
    obtain ⟨x, _, rfl⟩ := hρ
    exact (H.not_mem_sAD_iff _).mp x.2
  have hcount := tail_rowsum_exp_le (L := P.L T) (c := 2 * (2 / Real.exp 1)) hLC H.hT H.hD
    (by linarith [H.hL]) hb (by positivity) s hs_tail
  have hterm : ∀ x ∈ u,
      (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
        ≤ H.K ^ 2 * ((Z.mult (x : Z.carrier) : ℝ)
            * (Real.exp (-(2 * (2 / Real.exp 1))
                * Real.sqrt (P.w / A * distI T ((x : Z.carrier) : ℂ).im))
              * rowS (P.L T) (P.w / A) (2 * (2 / Real.exp 1))
                (distI T ((x : Z.carrier) : ℂ).im))) := by
    intro x _
    have hx : InTailD T D ((x : Z.carrier) : ℂ).im := (H.not_mem_sAD_iff _).mp x.2
    have hdist : 1 ≤ distI T ((x : Z.carrier) : ℂ).im :=
      H.hD.trans (le_distI_of_InTailD H.T_pos.le (by linarith [H.hD]) hx)
    have h := norm_sq_uvec_le_gevrey (Z := Z) H.hT H.hL H.K_nonneg hb hc
      H.hdecay (x : Z.carrier).2 hdist
    have hm : (0:ℝ) ≤ Z.mult (x : Z.carrier) := Nat.cast_nonneg _
    calc _ ≤ (Z.mult (x : Z.carrier) : ℝ)
          * (H.K ^ 2 * Real.exp (-(2 * (2 / Real.exp 1))
              * Real.sqrt (P.w / A * distI T ((x : Z.carrier) : ℂ).im))
            * rowS (P.L T) (P.w / A) (2 * (2 / Real.exp 1))
              (distI T ((x : Z.carrier) : ℂ).im)) :=
          mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring
  calc ∑ x ∈ u, (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ ∑ x ∈ u, H.K ^ 2 * ((Z.mult (x : Z.carrier) : ℝ)
          * (Real.exp (-(2 * (2 / Real.exp 1))
              * Real.sqrt (P.w / A * distI T ((x : Z.carrier) : ℂ).im))
            * rowS (P.L T) (P.w / A) (2 * (2 / Real.exp 1))
              (distI T ((x : Z.carrier) : ℂ).im))) := sum_le_sum hterm
    _ = H.K ^ 2 * ∑ ρ ∈ s, (Z.mult ρ : ℝ)
          * (Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w / A * distI T (ρ : ℂ).im))
            * rowS (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (distI T (ρ : ℂ).im)) := by
        rw [← mul_sum, hs, Finset.sum_map]; rfl
    _ ≤ H.K ^ 2 * (2 * A₀
          * (Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w / A * D))
            * sideW (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D)) := by
        apply mul_le_mul_of_nonneg_left hcount
        have := H.K_nonneg; positivity
    _ = P.L T * theta0G P T A₀ A Cenv D := by
        unfold theta0G K
        field_simp

end TailHypG

/-! ### the tail matrix chain at a free buffer (mirror of the record's `TailHyp` series
section, `prop_tail`, and the `Assembly.TailInputs` export — QT.b(5)) -/

end Tail

namespace Assembly

open RHLinalg Matrix

/-- **Inputs from the tail at a free buffer** (mirror of `Assembly.TailInputs` with the
split `E(D) := G − A(D)` at `I′(D)`; `TailInputsD Z P T (√T) θ₀ = TailInputs Z P T θ₀`
definitionally). -/
structure TailInputsD (Z : ZeroConfig) (P : Params) (T D θ₀ : ℝ) : Prop where
  theta_nonneg : 0 ≤ θ₀
  tilde : ∃ hEt : (P.tilde T (Z.EzD P T D)).IsHermitian, ∀ i, |hEt.eigenvalues i| ≤ θ₀
  hat : ∃ B : ℝ, 0 ≤ B ∧ |rtrace (P.hat T (Z.EzD P T D))| ≤ B ∧
      frobSq (P.hat T (Z.EzD P T D)) ≤ B ^ 2 ∧ B ≤ θ₀ / (P.a T * P.L T)

/-- At `D = √T` the free-buffer tail inputs are the record's. -/
lemma tailInputsD_sqrtT (Z : ZeroConfig) (P : Params) (T θ₀ : ℝ) :
    TailInputsD Z P T (D0 T) θ₀ ↔ TailInputs Z P T θ₀ :=
  ⟨fun h => ⟨h.theta_nonneg, h.tilde, h.hat⟩, fun h => ⟨h.theta_nonneg, h.tilde, h.hat⟩⟩

end Assembly

namespace Tail

namespace TailHypG

open Finset RHLinalg Matrix

variable {Z : ZeroConfig} {P : Params} {T A₀ A Cenv D : ℝ}
variable (H : TailHypG Z P T A₀ A Cenv D)
include H

/-- ∑_{γ∉I′(D)} m_ρ ‖u_ρ‖₂² is summable … (mirror of `summable_tail`). -/
lemma summable_tailG :
    Summable (fun x : {ρ : Z.carrier // ρ ∉ H.sAD} =>
      (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2) :=
  summable_of_sum_le (fun x => by positivity) H.partial_sum_leG

/-- … with sum ≤ L·θ₀G (mirror of `tsum_tail_le`). -/
lemma tsum_tail_leG :
    ∑' x : {ρ : Z.carrier // ρ ∉ H.sAD},
      (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ P.L T * theta0G P T A₀ A Cenv D :=
  Real.tsum_le_of_sum_le (fun x => by positivity) H.partial_sum_leG

/-- Absolute convergence of the entry series (mirror of `summable_Gsummand`). -/
lemma summable_GsummandG (k l : Fin (P.d T)) :
    Summable (fun ρ : Z.carrier => Z.Gsummand P T k l ρ) := by
  apply (Finset.summable_compl_iff H.sAD).mp
  refine Summable.of_norm_bounded H.summable_tailG (fun x => ?_)
  rw [Gsummand_eq, norm_mul, norm_mul, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h1 : ‖uvec P T (x : Z.carrier) k‖ ^ 2 ≤ ∑ j, ‖uvec P T (x : Z.carrier) j‖ ^ 2 :=
    single_le_sum (f := fun j => ‖uvec P T (x : Z.carrier) j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ k)
  have h2 : ‖uvec P T (x : Z.carrier) l‖ ^ 2 ≤ ∑ j, ‖uvec P T (x : Z.carrier) j‖ ^ 2 :=
    single_le_sum (f := fun j => ‖uvec P T (x : Z.carrier) j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ l)
  nlinarith [sq_nonneg (‖uvec P T (x : Z.carrier) k‖ - ‖uvec P T (x : Z.carrier) l‖),
    norm_nonneg (uvec P T (x : Z.carrier) k), norm_nonneg (uvec P T (x : Z.carrier) l)]

/-- `A(D)_{kl}` is the finite part of the series (mirror of `Az_eq_sum`). -/
lemma AzD_eq_sum (k l : Fin (P.d T)) :
    Z.AzD P T D k l = ∑ x ∈ H.sAD, Z.Gsummand P T k l (x : ℂ) := by
  classical
  have hfin : (Z.ZIprimeD T D).Finite := Z.finite_window _ _
  show (∑ᶠ ρ ∈ Z.ZIprimeD T D, Z.Gsummand P T k l ρ) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hmap : H.sAD.map (Function.Embedding.subtype _) = hfin.toFinset := by
    ext y
    rw [Finset.mem_map, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : ¬ InTailD T D ((x : Z.carrier) : ℂ).im := by
        rw [sAD, Set.Finite.mem_toFinset] at hx; exact hx
      simp only [InTailD, not_or, not_le, not_lt] at hx'
      exact ⟨x.2, hx'.1, hx'.2⟩
    · rintro ⟨hy, h1, h2⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [sAD, Set.Finite.mem_toFinset]
      simp only [Set.mem_setOf_eq, InTailD, not_or, not_le, not_lt]
      exact ⟨h1, h2⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- **E(D) = ∑_{γ∉I′(D)} m_ρ u_ρ u_ρᵀ** (mirror of `hasSum_Ez`). -/
theorem hasSum_EzD :
    HasSum (fun x : {ρ : Z.carrier // ρ ∉ H.sAD} =>
      ((Z.mult (x : Z.carrier) : ℝ) : ℂ)
        • vecMulVec (uvec P T (x : Z.carrier)) (uvec P T (x : Z.carrier)))
      (Z.EzD P T D) := by
  refine Pi.hasSum.mpr fun k => Pi.hasSum.mpr fun l => ?_
  have hG : HasSum (fun ρ : Z.carrier => Z.Gsummand P T k l ρ) (Z.Gz P T k l) :=
    (H.summable_GsummandG k l).hasSum
  have hE : HasSum (fun x : {ρ : Z.carrier // ρ ∉ H.sAD} => Z.Gsummand P T k l (x : Z.carrier))
      (Z.EzD P T D k l) := by
    apply (Finset.hasSum_compl_iff (f := fun ρ : Z.carrier => Z.Gsummand P T k l ρ) H.sAD).mpr
    have : Z.EzD P T D k l + ∑ x ∈ H.sAD, Z.Gsummand P T k l (x : ℂ) = Z.Gz P T k l := by
      rw [← H.AzD_eq_sum]; show (Z.Gz P T - Z.AzD P T D) k l + _ = _; simp
    rw [this]; exact hG
  simpa only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Complex.ofReal_natCast,
    Gsummand_eq] using hE

/-- traceNorm (κ•E(D)) ≤ κ·L·θ₀G for κ ≥ 0 (mirror of `traceNorm_smul_Ez_le`). -/
theorem traceNorm_smul_EzD_le {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : (((κ : ℝ) : ℂ) • Z.EzD P T D).IsHermitian) :
    traceNorm hM ≤ κ * (P.L T * theta0G P T A₀ A Cenv D) := by
  have hsum := H.hasSum_EzD
  have hS := H.summable_tailG.hasSum
  refine le_trans ?_ (mul_le_mul_of_nonneg_left H.tsum_tail_leG hκ)
  apply traceNorm_le_of_hasSum_vecMulVec hM
    (fun x : {ρ : Z.carrier // ρ ∉ H.sAD} => κ * (Z.mult (x : Z.carrier) : ℝ))
    (fun x => by positivity)
    (fun x : {ρ : Z.carrier // ρ ∉ H.sAD} => uvec P T (x : Z.carrier))
  · have := hS.mul_left κ
    simpa only [mul_assoc] using this
  · have := hsum.const_smul ((κ : ℝ) : ℂ)
    simpa only [smul_smul, Complex.ofReal_mul] using this

/-- E(D) is Hermitian (mirror of `TailHyp.Ez_isHermitian`; `I′(D)` is invariant under
ρ ↦ 1 − ρ̄ since reflection preserves the ordinate). -/
theorem EzD_isHermitian
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (Z.EzD P T D).IsHermitian := by
  classical
  have hrefl : ∀ x : {ρ : Z.carrier // ρ ∉ H.sAD},
      (⟨reflect ((x : Z.carrier) : ℂ), Z.reflect_mem _ (x : Z.carrier).2⟩ : Z.carrier)
        ∉ H.sAD := by
    intro x
    rw [H.not_mem_sAD_iff]
    simp only [reflect_im]
    exact (H.not_mem_sAD_iff _).mp x.2
  set σ : {ρ : Z.carrier // ρ ∉ H.sAD} → {ρ : Z.carrier // ρ ∉ H.sAD} :=
    fun x => ⟨⟨reflect ((x : Z.carrier) : ℂ), Z.reflect_mem _ (x : Z.carrier).2⟩, hrefl x⟩
    with hσdef
  have hσ : Function.Involutive σ := fun x => by
    apply Subtype.ext; apply Subtype.ext
    simp only [hσdef, reflect_reflect]
  set f : {ρ : Z.carrier // ρ ∉ H.sAD} → Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
    fun x => ((Z.mult (x : Z.carrier) : ℝ) : ℂ) •
      vecMulVec (uvec P T (x : Z.carrier)) (uvec P T (x : Z.carrier)) with hfdef
  have hf : HasSum f (Z.EzD P T D) := H.hasSum_EzD
  have hfH : HasSum (fun x => (f x)ᴴ) (Z.EzD P T D)ᴴ := hf.matrix_conjTranspose
  have hfσ : ∀ x, (f x)ᴴ = f (σ x) := by
    intro x
    ext k l
    have hm : Z.mult (reflect ((x : Z.carrier) : ℂ)) = Z.mult ((x : Z.carrier) : ℂ) :=
      Z.mult_reflect _ (x : Z.carrier).2
    simp only [hfdef, hσdef, conjTranspose_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, uvec_reflect hconj, hm]
    ring
  have h2 : HasSum (f ∘ (hσ.toPerm σ)) (Z.EzD P T D)ᴴ := by
    have : (f ∘ (hσ.toPerm σ)) = fun x => (f x)ᴴ := by
      funext x; simp [Function.comp, hfσ]
    rw [this]; exact hfH
  rw [Equiv.hasSum_iff] at h2
  exact h2.unique hf

lemma tilde_EzD_isHermitian
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (P.tilde T (Z.EzD P T D)).IsHermitian := by
  have h := isHermitian_real_smul (H.EzD_isHermitian hconj) (P.L T)⁻¹
  unfold Params.tilde; rw [← Complex.ofReal_inv]; exact h

lemma hat_EzD_isHermitian
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (P.hat T (Z.EzD P T D)).IsHermitian := by
  have h := isHermitian_real_smul (H.EzD_isHermitian hconj) (P.a T * P.L T ^ 2)⁻¹
  unfold Params.hat
  have e : ((P.a T * P.L T ^ 2)⁻¹ : ℂ) = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e]; exact h

lemma theta0G_nonneg : 0 ≤ theta0G P T A₀ A Cenv D := by
  unfold theta0G
  have hL0 := H.L_pos
  have hA₀ := H.A₀_nonneg
  have hK : (0:ℝ) ≤ Real.exp (P.L T / 4) * Cenv := by
    have := H.hCenv; positivity
  have hside : 0 ≤ sideW (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D := by
    apply sideW_nonneg (by linarith [H.hL]) H.b_pos (by positivity)
    · have := H.T_pos; linarith
    · linarith [H.hD]
  have hexp : (0:ℝ) ≤ Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w / A * D)) :=
    (Real.exp_pos _).le
  positivity

/-- **[prop:tail] at a free buffer, Gevrey decay** (mirror of `prop_tail`):
(T1) every eigenvalue of Ẽ(D) has |λ| ≤ θ₀G, and ‖Ẽ(D)‖₁ ≤ θ₀G;
(T2) ‖Ê(D)‖₁ ≤ θ₀G/(aL). -/
theorem prop_tailG (ha : 0 < P.a T)
    (hEt : (P.tilde T (Z.EzD P T D)).IsHermitian)
    (hEh : (P.hat T (Z.EzD P T D)).IsHermitian) :
    (∀ i, |hEt.eigenvalues i| ≤ theta0G P T A₀ A Cenv D) ∧
    traceNorm hEt ≤ theta0G P T A₀ A Cenv D ∧
    traceNorm hEh ≤ theta0G P T A₀ A Cenv D / (P.a T * P.L T) := by
  have hL := H.L_pos
  have htilde : P.tilde T (Z.EzD P T D) = (((P.L T)⁻¹ : ℝ) : ℂ) • Z.EzD P T D := by
    unfold Params.tilde; rw [Complex.ofReal_inv]
  have hEt' : ((((P.L T)⁻¹ : ℝ) : ℂ) • Z.EzD P T D).IsHermitian := htilde ▸ hEt
  have h1 : traceNorm hEt ≤ theta0G P T A₀ A Cenv D := by
    have h := H.traceNorm_smul_EzD_le (κ := (P.L T)⁻¹) (by positivity) hEt'
    have e : (P.L T)⁻¹ * (P.L T * theta0G P T A₀ A Cenv D) = theta0G P T A₀ A Cenv D := by
      field_simp
    rw [e] at h
    convert h using 2
  have hhat : P.hat T (Z.EzD P T D) = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • Z.EzD P T D := by
    unfold Params.hat; push_cast; rfl
  have hEh' : ((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • Z.EzD P T D).IsHermitian := hhat ▸ hEh
  have h2 : traceNorm hEh ≤ theta0G P T A₀ A Cenv D / (P.a T * P.L T) := by
    have h := H.traceNorm_smul_EzD_le (κ := (P.a T * P.L T ^ 2)⁻¹) (by positivity) hEh'
    have e : (P.a T * P.L T ^ 2)⁻¹ * (P.L T * theta0G P T A₀ A Cenv D)
        = theta0G P T A₀ A Cenv D / (P.a T * P.L T) := by
      field_simp
    rw [e] at h
    convert h using 2
  exact ⟨fun i => (abs_eigenvalues_le_traceNorm hEt i).trans h1, h1, h2⟩

/-- **QT.b(5): the free-buffer tail package** (mirror of `TailHyp.tailInputs`):
`Assembly.TailInputsD` holds at `θ₀G` — the Gevrey tail feeds the θ₀-generic
assembly interface with the buffer FREE. -/
theorem tailInputsD (ha : 0 < P.a T)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    Assembly.TailInputsD Z P T D (theta0G P T A₀ A Cenv D) := by
  have hEt := H.tilde_EzD_isHermitian hconj
  have hEh := H.hat_EzD_isHermitian hconj
  have hp := H.prop_tailG ha hEt hEh
  exact
    { theta_nonneg := H.theta0G_nonneg
      tilde := ⟨hEt, hp.1⟩
      hat := ⟨traceNorm hEh, traceNorm_nonneg _, abs_rtrace_le_traceNorm _,
        frobSq_le_traceNorm_sq _, hp.2.2⟩ }

end TailHypG

/-! ### the boundary count at a free buffer (QT.b(5) NII mirror) and the profile bridge -/

open Finset

/-- **Boundary count at a free buffer** (mirror of `boundary_count_le`): for zeros in
`(T−D, T] ∪ (2T, 2T+D]` with `2 ≤ D`, `D + 4 ≤ T`:  `∑ m_ρ ≤ 3·A₀·D·log(4T)`. -/
theorem boundary_countD_le {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T D : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (hD2 : 2 ≤ D) (hDT : D + 4 ≤ T) (s : Finset ι)
    (hs : ∀ ρ ∈ s, (T - D < γ ρ ∧ γ ρ ≤ T) ∨ (2 * T < γ ρ ∧ γ ρ ≤ 2 * T + D)) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ 3 * A₀ * D * Real.log (4 * T) := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA₀ : 0 ≤ A₀ := hN.A₀_pos.le
  set K : ℕ := ⌈D⌉₊ with hK
  have hKlt : (K : ℝ) < D + 1 := Nat.ceil_lt_add_one (by linarith)
  have hKge : D ≤ K := Nat.le_ceil D
  set C : ℝ := A₀ * Real.log (4 * T) with hCdef
  have hlog1 : 1 ≤ Real.log (4 * T) := one_le_log_four_mul hT
  have hC : 0 ≤ C := by positivity
  have hlogmono : ∀ (t : ℝ), |t| + 3 ≤ 4 * T →
      A₀ * Real.log (|t| + 3) ≤ C := fun t h =>
    mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) h) hA₀
  set slo := s.filter (fun ρ => γ ρ ≤ T) with hslo
  set shi := s.filter (fun ρ => ¬ γ ρ ≤ T) with hshi
  have hlo_mem : ∀ ρ ∈ slo, T - D < γ ρ ∧ γ ρ ≤ T := by
    intro ρ hρ
    rw [hslo, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact h
    · exact absurd hρ.2 (by linarith [h.1])
  have hhi_mem : ∀ ρ ∈ shi, 2 * T < γ ρ ∧ γ ρ ≤ 2 * T + D := by
    intro ρ hρ
    rw [hshi, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact absurd h.2 hρ.2
    · exact h
  have hlo : ∑ ρ ∈ slo, (m ρ : ℝ) ≤ K * C := by
    apply sum_mult_le_of_windows slo m (fun ρ => ⌊T - γ ρ⌋₊) K
    · intro ρ hρ
      have h := hlo_mem ρ hρ
      have : (⌊T - γ ρ⌋₊ : ℝ) < K :=
        lt_of_le_of_lt (Nat.floor_le (by linarith [h.2])) (by linarith [h.1, hKge])
      exact_mod_cast this
    · intro j hj
      refine (hN.window (T - j - 1) _ ?_).trans (hlogmono _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hnn : 0 ≤ T - γ ρ := by linarith [(hlo_mem ρ hρs).2]
        have := (Nat.floor_eq_iff hnn).mp hρj
        constructor <;> linarith [this.1, this.2]
      · have hj' : (j : ℝ) < D + 1 := lt_of_lt_of_le (by exact_mod_cast hj) hKlt.le
        rw [abs_of_nonneg (by linarith)]
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hhi : ∑ ρ ∈ shi, (m ρ : ℝ) ≤ K * C := by
    have hceil1 : ∀ ρ ∈ shi, 1 ≤ ⌈γ ρ - 2 * T⌉₊ := fun ρ hρ =>
      Nat.one_le_ceil_iff.mpr (by linarith [(hhi_mem ρ hρ).1])
    apply sum_mult_le_of_windows shi m (fun ρ => ⌈γ ρ - 2 * T⌉₊ - 1) K
    · intro ρ hρ
      have h := hhi_mem ρ hρ
      have : ⌈γ ρ - 2 * T⌉₊ ≤ K := by rw [hK]; exact Nat.ceil_mono (by linarith [h.2])
      have := hceil1 ρ hρ
      omega
    · intro j hj
      refine (hN.window (2 * T + j) _ ?_).trans (hlogmono _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hc : ⌈γ ρ - 2 * T⌉₊ = j + 1 := by have := hceil1 ρ hρs; omega
        have := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
        push_cast at this
        constructor <;> linarith [this.1, this.2]
      · have hj' : (j : ℝ) < D + 1 := lt_of_lt_of_le (by exact_mod_cast hj) hKlt.le
        rw [abs_of_nonneg (by positivity)]
        linarith
  rw [← sum_filter_add_sum_filter_not s (fun ρ => γ ρ ≤ T)]
  have hK' : (K : ℝ) * C ≤ (D + 1) * C := mul_le_mul_of_nonneg_right hKlt.le hC
  have hfin : (2 : ℝ) * ((D + 1) * C) ≤ 3 * A₀ * D * Real.log (4 * T) := by
    rw [hCdef]
    have h23 : 2 * (D + 1) ≤ 3 * D := by linarith
    have hAl : 0 ≤ A₀ * Real.log (4 * T) := hC
    nlinarith
  linarith

/-- **N(I′(D)∖I) ≤ 3·A₀·D·log(4T)** (mirror of `NII_le`; QT.b(5)'s buffer count at a
free buffer). -/
theorem NIID_le (Z : ZeroConfig) {A₀ T D : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hT : T₀ ≤ T) (hD2 : 2 ≤ D) (hDT : D + 4 ≤ T) :
    (Assembly.NIID Z T D : ℝ) ≤ 3 * A₀ * D * Real.log (4 * T) := by
  classical
  have hT' : (300:ℝ) ≤ T := hT
  have hLC := LocalCount.ofWindowCount Z hA₀ hloc
  have hfin1 : (Z.window (T - D) T).Finite := Z.finite_window _ _
  have hfin2 : (Z.window (2 * T) (2 * T + D)).Finite := Z.finite_window _ _
  set s1 : Finset Z.carrier := hfin1.toFinset.subtype (· ∈ Z.carrier) with hs1
  set s2 : Finset Z.carrier := hfin2.toFinset.subtype (· ∈ Z.carrier) with hs2
  have hN1 : (Z.N (T - D) T : ℝ) = ∑ ρ ∈ s1, (Z.mult (ρ : ℂ) : ℝ) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin1, hs1,
      Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (Z.mult ρ : ℝ))]
    · push_cast; rfl
    · intro x hx; exact ((Set.Finite.mem_toFinset _).mp hx).1
  have hN2 : (Z.N (2 * T) (2 * T + D) : ℝ) = ∑ ρ ∈ s2, (Z.mult (ρ : ℂ) : ℝ) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin2, hs2,
      Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (Z.mult ρ : ℝ))]
    · push_cast; rfl
    · intro x hx; exact ((Set.Finite.mem_toFinset _).mp hx).1
  have hmem1 : ∀ ρ ∈ s1, T - D < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T := by
    intro ρ hρ
    rw [hs1, Finset.mem_subtype, Set.Finite.mem_toFinset] at hρ
    exact hρ.2
  have hmem2 : ∀ ρ ∈ s2, 2 * T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T + D := by
    intro ρ hρ
    rw [hs2, Finset.mem_subtype, Set.Finite.mem_toFinset] at hρ
    exact hρ.2
  have hdisj : Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have := (hmem1 ρ h1).2; have := (hmem2 ρ h2).1; linarith
  have hunion : ∀ ρ ∈ s1 ∪ s2, (T - D < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T)
      ∨ (2 * T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T + D) := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · exact Or.inl (hmem1 ρ h)
    · exact Or.inr (hmem2 ρ h)
  have h := boundary_countD_le hLC hT hD2 hDT (s1 ∪ s2) hunion
  rw [Finset.sum_union hdisj] at h
  unfold Assembly.NIID
  push_cast
  rw [hN1, hN2]
  exact h

/-- **The profile bridge**: a Gevrey-2 profile at constants `(A, B)` (the design has
`GevreyProfile 2 (36/e) (2e⁸) ϱ₂`, `Taper/Gevrey.lean gevreyProfile_rhoTwo`) yields the
`TailHypG` hypotheses at `Cenv = e²·max(2Bw, L)` — QT.a feeding QT.b, all regime facts
explicit. -/
theorem TailHypG.of_profile {Z : ZeroConfig} {P : Params} {T A₀ A B D : ℝ}
    (hϱ : Taper.GevreyProfile 2 A B P.ϱ) (hP : P.ValidQ) (hwL : 8 * P.w ≤ P.L T)
    (hT : T₀ ≤ T) (hL : 2 ≤ P.L T) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (hD : 1 ≤ D) :
    TailHypG Z P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) D where
  hT := hT
  hL := hL
  hA₀ := hA₀
  hloc := hloc
  hA := hϱ.A_pos
  hCenv := by
    have hL0 : 0 < P.L T := by linarith
    have hB := hϱ.B_pos
    have hw := Params.w_pos hP
    positivity
  hw := Params.w_pos hP
  hD := hD
  hdecay := by
    intro r y hy
    have hL0 : 0 < P.L T := by linarith
    have h := P.norm_phiHat_le_gevrey hϱ hP hwL hL0 ((r : ℂ) - Complex.I * (y : ℂ))
    have him : ((r : ℂ) - Complex.I * (y : ℂ)).im = -y := by simp
    have hre : ((r : ℂ) - Complex.I * (y : ℂ)).re = r := by simp
    have hnorm : |r| ≤ ‖(r : ℂ) - Complex.I * (y : ℂ)‖ := by
      calc |r| = |((r : ℂ) - Complex.I * (y : ℂ)).re| := by rw [hre]
        _ ≤ ‖(r : ℂ) - Complex.I * (y : ℂ)‖ := Complex.abs_re_le_norm _
    have hw0 : 0 < P.w := Params.w_pos hP
    have hexp1 : Real.exp (|((r : ℂ) - Complex.I * (y : ℂ)).im| * (P.L T / 2))
        ≤ Real.exp (P.L T / 4) := by
      rw [Real.exp_le_exp, him, abs_neg]
      nlinarith [abs_nonneg y]
    have hexp2 : Real.exp (-(2 / Real.exp 1)
          * Real.sqrt (P.w * ‖(r : ℂ) - Complex.I * (y : ℂ)‖ / A))
        ≤ Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w / A * |r|)) := by
      rw [Real.exp_le_exp]
      have hA0 := hϱ.A_pos
      have h1 : P.w / A * |r| ≤ P.w * ‖(r : ℂ) - Complex.I * (y : ℂ)‖ / A := by
        have e1 : P.w / A * |r| = P.w * |r| / A := by ring
        rw [e1]
        gcongr
      have h2 : Real.sqrt (P.w / A * |r|)
          ≤ Real.sqrt (P.w * ‖(r : ℂ) - Complex.I * (y : ℂ)‖ / A) :=
        Real.sqrt_le_sqrt h1
      have h3 : 0 < 2 / Real.exp 1 := by positivity
      nlinarith
    calc ‖P.phiHat T ((r : ℂ) - Complex.I * (y : ℂ))‖
        ≤ Real.exp 2 * max (2 * B * P.w) (P.L T)
            * Real.exp (|((r : ℂ) - Complex.I * (y : ℂ)).im| * (P.L T / 2))
            * Real.exp (-(2 / Real.exp 1)
              * Real.sqrt (P.w * ‖(r : ℂ) - Complex.I * (y : ℂ)‖ / A)) := h
      _ ≤ Real.exp 2 * max (2 * B * P.w) (P.L T) * Real.exp (P.L T / 4)
            * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w / A * |r|)) := by
          have hc0 : (0:ℝ) ≤ Real.exp 2 * max (2 * B * P.w) (P.L T) := by
            have hB := hϱ.B_pos
            positivity
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hexp1 hc0
          · exact hexp2
          · positivity
          · positivity
      _ = Real.exp (P.L T / 4) * (Real.exp 2 * max (2 * B * P.w) (P.L T))
            * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w / A * |r|)) := by ring

end Tail
end Zeta23
