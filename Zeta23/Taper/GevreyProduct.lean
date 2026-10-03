/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper/GevreyProduct.lean — the PRODUCT window  φ_q(u) := q(u)·φ(u),  φ = Zeta23.Taper.phi ϱ L w.

This is the analytic half of the flat-taper repair: the design window of the q-aspect paper is
`p(u/ℒ)·ϱ₂((L/2 − |u|)/w)` with `p` an even polynomial, and this file supplies

  §A  the Gevrey ramp lemma for q·φ:  ‖(q·φ)^{(k)}‖₁ ≤ 2·B'·w·(A/w)^k·k^{sk}  with explicit B'
      (`integral_abs_iteratedDeriv_mul_phi_le_sum` — k-explicit;
       `integral_abs_iteratedDeriv_mul_phi_le_of_bounds` — general (S,T) constants;
       `integral_abs_iteratedDeriv_mul_phi_le` — B' = (B + L/(2w))·Σ_{i≤m} Mq i (w/A)^i);
  §B  the AdmWindow instance for q·φ under support-LOCAL hypotheses `ProfileFactor`
      (`admWindow_mul_phi`, c' = cMod ϱ A B — the tree's `XiPrime.admWindow_phiM` with its GLOBAL
      `nonneg` weakened to the core);
  §P  the polynomial application q u = pp.eval (u/ℒ): C^∞, q^{(j)}(u) = ℒ^{−j} pp^{(j)}(u/ℒ),
      explicit M_j (coefficient sums `Mpoly`), `gevrey_polyQ_mul_phi` (§A) and
      `admWindow_polyQ_mul_phi` (§B).
Consumed by `ZetaQ/Window.lean` (the `ParamsQ` instance). Imports only `Zeta23.Taper.GevreyRamps`
and `Zeta23.XiPrime.QuarticWindow.ModWindow`; nothing in `Zeta23` imports this file.
Everything is sorry-free (`[propext, Classical.choice, Quot.sound]`, checked at the foot of the
prototype).
-/
import Zeta23.Taper.GevreyRamps
import Zeta23.XiPrime.QuarticWindow.ModWindow

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Zeta23
namespace ProductWindow

open Taper XiPrime

/-! ## §A  Gevrey ramp lemma for the product window -/

variable {s A B : ℝ} {ϱ : ℝ → ℝ} {L w : ℝ}


/-- φ is C^∞ for a Gevrey profile (product of the two smooth ramps `fP`, `fM`). -/
lemma phi_contDiff_top (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phi ϱ L w) := by
  have hprod : phi ϱ L w = fP ϱ L w * fM ϱ L w := by
    funext u; exact phi_eq_mul hϱ.taper hw hwL u
  rw [hprod]; exact (fP_contDiff hϱ).mul (fM_contDiff hϱ)

/-- all derivatives of φ vanish for |u| > L/2 (φ ≡ 0 on that open set). -/
lemma iteratedDeriv_phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) (j : ℕ) {u : ℝ}
    (hu : L / 2 < |u|) : iteratedDeriv j (phi ϱ L w) u = 0 := by
  have hopen : IsOpen {v : ℝ | L / 2 < |v|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
  have hev : phi ϱ L w =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
    filter_upwards [hopen.mem_nhds hu] with v hv
    exact phi_eq_zero hϱ hw (le_of_lt hv)
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
  split_ifs <;> rfl

lemma hasCompactSupport_iteratedDeriv_phi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (j : ℕ) : HasCompactSupport (iteratedDeriv j (phi ϱ L w)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(L / 2)) (b := L / 2))
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hmem
  apply hu
  apply iteratedDeriv_phi_eq_zero hϱ hw
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  rcases hmem with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma integrable_abs_iteratedDeriv_phi (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) (j : ℕ) : Integrable (fun u => |iteratedDeriv j (phi ϱ L w) u|) := by
  have hc : Continuous (iteratedDeriv j (phi ϱ L w)) :=
    (phi_contDiff_top hϱ hw hwL).continuous_iteratedDeriv j (WithTop.coe_le_coe.mpr le_top)
  exact (hc.abs).integrable_of_hasCompactSupport
    ((hasCompactSupport_iteratedDeriv_phi hϱ.taper hw hwL j).comp_left (g := fun t => |t|) abs_zero)

/-- the combinatorial/Gevrey arithmetic: for `i < k`,
`C(k,i)·(A/w)^{k−i}·(k−i)^{s(k−i)} ≤ (A/w)^k·k^{sk}·(w/A)^i`  (uses `s > 1`, `k ≥ 1`). -/
lemma choose_ramp_le (hs : 1 < s) (hA : 0 < A) (hw : 0 < w) {i k : ℕ} (hik : i < k) :
    (k.choose i : ℝ) * (A / w) ^ (k - i) * ((k - i : ℕ) : ℝ) ^ (s * ((k - i : ℕ) : ℝ))
      ≤ (A / w) ^ k * (k : ℝ) ^ (s * k) * (w / A) ^ i := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hk0 : (0:ℝ) < k := by linarith
  have hAw : (0:ℝ) < A / w := by positivity
  have hik' : i ≤ k := hik.le
  have hs0 : (0:ℝ) ≤ s := by linarith
  have e1 : (A / w) ^ (k - i) = (A / w) ^ k * (w / A) ^ i := by
    rw [pow_sub₀ _ hAw.ne' hik', ← inv_pow, inv_div]
  have h1 : (k.choose i : ℝ) ≤ (k : ℝ) ^ i := by exact_mod_cast Nat.choose_le_pow k i
  have h2 : ((k - i : ℕ) : ℝ) ^ (s * ((k - i : ℕ) : ℝ)) ≤ (k : ℝ) ^ (s * ((k - i : ℕ) : ℝ)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le k i) (by positivity)
  have h3 : (k : ℝ) ^ i * (k : ℝ) ^ (s * ((k - i : ℕ) : ℝ)) ≤ (k : ℝ) ^ (s * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hk0]
    have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := by push_cast [Nat.cast_sub hik']; ring
    rw [hcast]
    have e : (i : ℝ) + s * ((k:ℝ) - i) = s * k + (i : ℝ) * (1 - s) := by ring
    rw [e, Real.rpow_add hk0]
    have h4 : (k : ℝ) ^ ((i : ℝ) * (1 - s)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk1 (by nlinarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])
    have h5 : (0:ℝ) ≤ (k : ℝ) ^ (s * k) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  calc (k.choose i : ℝ) * (A / w) ^ (k - i) * ((k - i : ℕ) : ℝ) ^ (s * ((k - i : ℕ) : ℝ))
      ≤ (k : ℝ) ^ i * ((A / w) ^ k * (w / A) ^ i) * (k : ℝ) ^ (s * ((k - i : ℕ) : ℝ)) := by
        rw [e1]; gcongr
    _ = (A / w) ^ k * (w / A) ^ i * ((k : ℝ) ^ i * (k : ℝ) ^ (s * ((k - i : ℕ) : ℝ))) := by ring
    _ ≤ (A / w) ^ k * (w / A) ^ i * (k : ℝ) ^ (s * k) := by gcongr
    _ = _ := by ring

/-- **Gevrey ramp lemma for a product window, k-explicit form.**
For `q ∈ C^k` with `|q^{(i)}| ≤ Mq i` on `[−L/2, L/2]` (`i ≤ k`):
`‖(q·φ)^{(k)}‖₁ ≤ 2Bw(A/w)^k k^{sk} · Σ_{i<k} Mq i (w/A)^i  +  Mq k · L`. -/
theorem integral_abs_iteratedDeriv_mul_phi_le_sum (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) {q : ℝ → ℝ} {Mq : ℕ → ℝ} {k : ℕ} (hq : ContDiff ℝ k q)
    (hMq : ∀ i ≤ k, ∀ u, |u| ≤ L / 2 → |iteratedDeriv i q u| ≤ Mq i) :
    ∫ u, |iteratedDeriv k (fun u => q u * phi ϱ L w u) u|
      ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k)
          * (∑ i ∈ Finset.range k, Mq i * (w / A) ^ i) + Mq k * L := by
  have hL2 : (0:ℝ) ≤ L / 2 := by linarith
  have hMq0 : ∀ i ≤ k, 0 ≤ Mq i := fun i hi =>
    (abs_nonneg _).trans (hMq i hi 0 (by rw [abs_zero]; exact hL2))
  have hA := hϱ.A_pos
  have hB := hϱ.B_pos
  have hφsm := phi_contDiff_top hϱ hw hwL
  -- Leibniz
  have hleib : ∀ u, iteratedDeriv k (fun u => q u * phi ϱ L w u) u
      = ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * iteratedDeriv i q u * iteratedDeriv (k - i) (phi ϱ L w) u := by
    intro u
    exact iteratedDeriv_mul (n := k) (x := u) hq.contDiffAt
      ((hφsm.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
  -- pointwise majorant
  set maj : ℝ → ℝ := fun u => ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * Mq i * |iteratedDeriv (k - i) (phi ϱ L w) u| with hmaj
  have hterm : ∀ i ≤ k, ∀ u, |iteratedDeriv i q u| * |iteratedDeriv (k - i) (phi ϱ L w) u|
      ≤ Mq i * |iteratedDeriv (k - i) (phi ϱ L w) u| := by
    intro i hi u
    rcases le_or_gt |u| (L / 2) with hu | hu
    · exact mul_le_mul_of_nonneg_right (hMq i hi u hu) (abs_nonneg _)
    · rw [iteratedDeriv_phi_eq_zero hϱ.taper hw _ hu, abs_zero, mul_zero, mul_zero]
  have hpt : ∀ u, |iteratedDeriv k (fun u => q u * phi ϱ L w u) u| ≤ maj u := by
    intro u
    rw [hleib u]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hterm i hik u) (Nat.cast_nonneg _)
  -- integrability of the majorant
  have hint : ∀ i ∈ Finset.range (k + 1),
      Integrable (fun u => (k.choose i : ℝ) * Mq i * |iteratedDeriv (k - i) (phi ϱ L w) u|) :=
    fun i _ => (integrable_abs_iteratedDeriv_phi hϱ hw hwL (k - i)).const_mul _
  have hmajint : Integrable maj := by
    rw [hmaj]; exact integrable_finsetSum _ hint
  -- the i = k term and the i < k terms
  have hlast : Mq k * ∫ u, |phi ϱ L w u| ≤ Mq k * L :=
    mul_le_mul_of_nonneg_left (XiPrime.integral_abs_phi_le hϱ.taper hw hwL) (hMq0 k le_rfl)
  have hmid : ∀ i ∈ Finset.range k,
      (k.choose i : ℝ) * Mq i * ∫ u, |iteratedDeriv (k - i) (phi ϱ L w) u|
        ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) * (Mq i * (w / A) ^ i) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hramp := integral_abs_iteratedDeriv_phi_le hϱ hw hwL (k := k - i) (by omega)
    have hMi := hMq0 i hik.le
    calc (k.choose i : ℝ) * Mq i * ∫ u, |iteratedDeriv (k - i) (phi ϱ L w) u|
        ≤ (k.choose i : ℝ) * Mq i
            * (2 * B * w * (A / w) ^ (k - i) * ((k - i : ℕ) : ℝ) ^ (s * ((k - i : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hramp (by positivity)
      _ = 2 * B * w * Mq i
            * ((k.choose i : ℝ) * (A / w) ^ (k - i) * ((k - i : ℕ) : ℝ) ^ (s * ((k - i : ℕ) : ℝ))) := by
          ring
      _ ≤ 2 * B * w * Mq i * ((A / w) ^ k * (k : ℝ) ^ (s * k) * (w / A) ^ i) :=
          mul_le_mul_of_nonneg_left (choose_ramp_le hϱ.one_lt hA hw hik) (by positivity)
      _ = _ := by ring
  -- integrate
  calc ∫ u, |iteratedDeriv k (fun u => q u * phi ϱ L w u) u|
      ≤ ∫ u, maj u :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _) hmajint
          (Eventually.of_forall hpt)
    _ = ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * Mq i * ∫ u, |iteratedDeriv (k - i) (phi ϱ L w) u| := by
        rw [hmaj, integral_finsetSum _ hint]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul]
    _ = (∑ i ∈ Finset.range k, (k.choose i : ℝ) * Mq i * ∫ u, |iteratedDeriv (k - i) (phi ϱ L w) u|)
          + Mq k * ∫ u, |phi ϱ L w u| := by
        rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
          iteratedDeriv_zero]
    _ ≤ (∑ i ∈ Finset.range k, 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) * (Mq i * (w / A) ^ i))
          + Mq k * L := add_le_add (Finset.sum_le_sum hmid) hlast
    _ = _ := by rw [← Finset.mul_sum]

/-- **Gevrey ramp lemma for a product window, with a k-independent constant.**
If moreover `Mq i = 0` for `i > m` (e.g. `q` a polynomial of degree `≤ m` in `u`), then with
`S := Σ_{i=0}^{m} Mq i (w/A)^i` and `B' := (B + L/(2w))·S`,
`‖(q·φ)^{(k)}‖₁ ≤ 2·B'·w·(A/w)^k·k^{sk}` for every `k ≥ 1`. -/
theorem integral_abs_iteratedDeriv_mul_phi_le (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) {q : ℝ → ℝ} {Mq : ℕ → ℝ} {m : ℕ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q)
    (hMq : ∀ i u, |u| ≤ L / 2 → |iteratedDeriv i q u| ≤ Mq i)
    (hm : ∀ i, m < i → Mq i = 0) {k : ℕ} (hk : 1 ≤ k) :
    ∫ u, |iteratedDeriv k (fun u => q u * phi ϱ L w u) u|
      ≤ 2 * ((B + L / (2 * w)) * ∑ i ∈ Finset.range (m + 1), Mq i * (w / A) ^ i)
          * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
  have hL2 : (0:ℝ) ≤ L / 2 := by linarith
  have hL : (0:ℝ) ≤ L := by linarith
  have hMq0 : ∀ i, 0 ≤ Mq i := fun i =>
    (abs_nonneg _).trans (hMq i 0 (by rw [abs_zero]; exact hL2))
  have hA := hϱ.A_pos
  have hB := hϱ.B_pos
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hmain := integral_abs_iteratedDeriv_mul_phi_le_sum hϱ hw hwL (k := k)
    (hq.of_le (WithTop.coe_le_coe.mpr le_top)) (fun i _ u hu => hMq i u hu)
  set f : ℕ → ℝ := fun i => Mq i * (w / A) ^ i with hf
  set S : ℝ := ∑ i ∈ Finset.range (m + 1), f i with hS
  have hf0 : ∀ i, 0 ≤ f i := fun i => mul_nonneg (hMq0 i) (by positivity)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hf0 i
  have hfS : ∀ i, f i ≤ S := by
    intro i
    rcases le_or_gt i m with him | him
    · exact Finset.single_le_sum (fun j _ => hf0 j) (Finset.mem_range.mpr (by omega))
    · have : f i = 0 := by rw [hf]; simp only; rw [hm i him, zero_mul]
      rw [this]; exact hS0
  have hsum : ∑ i ∈ Finset.range k, f i ≤ S := by
    have h1 : ∑ i ∈ Finset.range k, f i ≤ ∑ i ∈ Finset.range (k + m + 1), f i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : k ≤ k + m + 1))
        (fun i _ _ => hf0 i)
    have h2 : ∑ i ∈ Finset.range (m + 1), f i = ∑ i ∈ Finset.range (k + m + 1), f i := by
      apply Finset.sum_subset (Finset.range_mono (by omega : m + 1 ≤ k + m + 1))
      intro i _ hi
      rw [Finset.mem_range, not_lt] at hi
      rw [hf]; simp only; rw [hm i (by omega), zero_mul]
    rw [hS, h2]; exact h1
  -- Mq k ≤ S·(A/w)^k·k^{sk}
  have hMk : Mq k ≤ S * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
    have hfk : Mq k * (w / A) ^ k ≤ S := hfS k
    have hkpow : (1:ℝ) ≤ (k : ℝ) ^ (s * k) :=
      Real.one_le_rpow hk1 (by have := hϱ.one_lt; positivity)
    have hwA : (w / A) ^ k * (A / w) ^ k = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm w A, div_self (by positivity), one_pow]
    calc Mq k = Mq k * (w / A) ^ k * (A / w) ^ k := by rw [mul_assoc, hwA, mul_one]
      _ ≤ S * (A / w) ^ k := mul_le_mul_of_nonneg_right hfk (by positivity)
      _ = S * (A / w) ^ k * 1 := (mul_one _).symm
      _ ≤ S * (A / w) ^ k * (k : ℝ) ^ (s * k) :=
          mul_le_mul_of_nonneg_left hkpow (by positivity)
  have hpos : (0:ℝ) ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by positivity
  have hpos2 : (0:ℝ) ≤ (A / w) ^ k * (k : ℝ) ^ (s * k) := by positivity
  calc ∫ u, |iteratedDeriv k (fun u => q u * phi ϱ L w u) u|
      ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) * (∑ i ∈ Finset.range k, f i) + Mq k * L :=
        hmain
    _ ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) * S
          + (S * (A / w) ^ k * (k : ℝ) ^ (s * k)) * L :=
        add_le_add (mul_le_mul_of_nonneg_left hsum hpos) (mul_le_mul_of_nonneg_right hMk hL)
    _ = 2 * ((B + L / (2 * w)) * S) * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
        field_simp


/-- **Gevrey ramp lemma for a product window, general constants.**
`S ≥ Σ_{i<n} Mq i (w/A)^i` for all `n`, and `T ≥ Mq n·L·(w/A)^n` for all `n ≥ 1`; then
`‖(q·φ)^{(k)}‖₁ ≤ 2·(B·S + T/(2w))·w·(A/w)^k·k^{sk}`  (`k ≥ 1`). -/
theorem integral_abs_iteratedDeriv_mul_phi_le_of_bounds (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) {q : ℝ → ℝ} {Mq : ℕ → ℝ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q)
    (hMq : ∀ i u, |u| ≤ L / 2 → |iteratedDeriv i q u| ≤ Mq i)
    {S T : ℝ} (hS : ∀ n, ∑ i ∈ Finset.range n, Mq i * (w / A) ^ i ≤ S)
    (hT : ∀ n, 1 ≤ n → Mq n * L * (w / A) ^ n ≤ T) {k : ℕ} (hk : 1 ≤ k) :
    ∫ u, |iteratedDeriv k (fun u => q u * phi ϱ L w u) u|
      ≤ 2 * (B * S + T / (2 * w)) * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
  have hA := hϱ.A_pos
  have hB := hϱ.B_pos
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hmain := integral_abs_iteratedDeriv_mul_phi_le_sum hϱ hw hwL (k := k)
    (hq.of_le (WithTop.coe_le_coe.mpr le_top)) (fun i _ u hu => hMq i u hu)
  have hkpow : (1:ℝ) ≤ (k : ℝ) ^ (s * k) :=
    Real.one_le_rpow hk1 (by have := hϱ.one_lt; positivity)
  have hwA : (w / A) ^ k * (A / w) ^ k = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm w A, div_self (by positivity), one_pow]
  have hMk : Mq k * L ≤ T * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
    calc Mq k * L = Mq k * L * (w / A) ^ k * (A / w) ^ k := by rw [mul_assoc, hwA, mul_one]
      _ ≤ T * (A / w) ^ k := mul_le_mul_of_nonneg_right (hT k hk) (by positivity)
      _ = T * (A / w) ^ k * 1 := (mul_one _).symm
      _ ≤ T * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
          apply mul_le_mul_of_nonneg_left hkpow
          have hT0 : 0 ≤ T := by
            have h1 := hT 1 le_rfl
            have hL2 : (0:ℝ) ≤ L / 2 := by linarith
            have hMq1 : 0 ≤ Mq 1 := (abs_nonneg _).trans (hMq 1 0 (by rw [abs_zero]; exact hL2))
            have : 0 ≤ Mq 1 * L * (w / A) ^ 1 :=
              mul_nonneg (mul_nonneg hMq1 (by linarith)) (by positivity)
            linarith
          positivity
  have hpos : (0:ℝ) ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by positivity
  calc ∫ u, |iteratedDeriv k (fun u => q u * phi ϱ L w u) u|
      ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k)
          * (∑ i ∈ Finset.range k, Mq i * (w / A) ^ i) + Mq k * L := hmain
    _ ≤ 2 * B * w * (A / w) ^ k * (k : ℝ) ^ (s * k) * S
          + T * (A / w) ^ k * (k : ℝ) ^ (s * k) :=
        add_le_add (mul_le_mul_of_nonneg_left (hS k) hpos) hMk
    _ = 2 * (B * S + T / (2 * w)) * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
        field_simp

/-! ## §B  AdmWindow instance for the product window -/

/-- hypotheses on the profile factor `q`, all LOCAL to the support `[−L/2, L/2]`. -/
structure ProfileFactor (f : ℝ → ℝ) (L A B : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  even : ∀ u, f (-u) = f u
  nonneg : ∀ u, |u| ≤ L / 2 → 0 ≤ f u
  le_one : ∀ u, |u| ≤ L / 2 → f u ≤ 1
  antitone : AntitoneOn f (Icc 0 (L / 2))
  smooth : ∃ δ : ℝ, 0 < δ ∧ ContDiffOn ℝ 2 f (Ioo (-(L / 2 + δ)) (L / 2 + δ))
  deriv_le : ∀ u, |u| ≤ L / 2 → |deriv f u| ≤ A / L
  deriv2_le : ∀ u, |u| ≤ L / 2 → |deriv (deriv f) u| ≤ B / L ^ 2

variable {f q : ℝ → ℝ} {ϱ : ℝ → ℝ} {L w A B : ℝ}

theorem ModFactor.toProfileFactor (hf : ModFactor f L A B) : ProfileFactor f L A B :=
  { hf with nonneg := fun u _ => hf.nonneg u }

/-- (1) the tree's theorem, restated for the product window. -/
theorem admWindow_mul_phi_of_modFactor (hf : ModFactor q L A B) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) : AdmWindow (fun u => q u * Taper.phi ϱ L w u) L w (cMod ϱ A B) :=
  admWindow_phiM hf hϱ hw hwL

/-! ### (2) the local-hypothesis version -/

theorem phiM_even' (hf : ProfileFactor f L A B) (u : ℝ) : phiM f ϱ L w (-u) = phiM f ϱ L w u := by
  simp only [phiM, hf.even, Taper.phi_even]

theorem phiM_nonneg' (hf : ProfileFactor f L A B) (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ) :
    0 ≤ phiM f ϱ L w u := by
  rcases le_or_gt |u| (L / 2) with hu | hu
  · exact mul_nonneg (hf.nonneg u hu) (Taper.phi_nonneg hϱ u)
  · rw [phiM_eq_zero hϱ hw hu.le]

theorem phiM_le_one' (hf : ProfileFactor f L A B) (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ) :
    phiM f ϱ L w u ≤ 1 := by
  rcases le_or_gt (L / 2) |u| with hu | hu
  · rw [phiM_eq_zero hϱ hw hu]; exact zero_le_one
  · calc phiM f ϱ L w u ≤ 1 * 1 :=
          mul_le_mul (hf.le_one u hu.le) (Taper.phi_le_one hϱ u) (Taper.phi_nonneg hϱ u) zero_le_one
      _ = 1 := mul_one 1

theorem phiM_contDiff' (hf : ProfileFactor f L A B) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) : ContDiff ℝ 2 (phiM f ϱ L w) := by
  obtain ⟨δ, hδ, hsm⟩ := hf.smooth
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge |u| (L / 2 + δ) with hu | hu
  · have hmem : u ∈ Ioo (-(L / 2 + δ)) (L / 2 + δ) := by
      constructor <;> linarith [neg_abs_le u, le_abs_self u]
    have hfu : ContDiffAt ℝ 2 f u := hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)
    exact hfu.mul ((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)).contDiffAt
  · have hopen : IsOpen {v : ℝ | L / 2 < |v|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
    have hmem : u ∈ {v : ℝ | L / 2 < |v|} := by
      show L / 2 < |u|; linarith
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := 0)) ?_
    filter_upwards [hopen.mem_nhds hmem] with v hv
    exact phiM_eq_zero hϱ hw hv.le

theorem phiM_antitoneOn' (hf : ProfileFactor f L A B) (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    AntitoneOn (phiM f ϱ L w) (Ici 0) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  rcases le_or_gt (L / 2) y with hyL | hyL
  · rw [phiM_eq_zero hϱ hw (by rwa [abs_of_nonneg hy])]
    exact phiM_nonneg' hf hϱ hw x
  · unfold phiM
    refine mul_le_mul (hf.antitone ⟨hx, by linarith⟩ ⟨hy, hyL.le⟩ hxy)
      (phi_antitoneOn hϱ hw hx hy hxy) (Taper.phi_nonneg hϱ y) (hf.nonneg x ?_)
    rw [abs_of_nonneg hx]; linarith

theorem integral_abs_deriv_phiM_le' (hf : ProfileFactor f L A B) (hϱ : TaperProfile ϱ) (hw : 0 < w)
    (hwL : 2 * w ≤ L) : ∫ u, |deriv (phiM f ϱ L w) u| ≤ 2 := by
  have hL : 0 < L := by linarith
  exact integral_abs_deriv_le_two (by positivity : (0:ℝ) < L / 2)
    ((phiM_contDiff' hf hϱ hw hwL).of_le (by norm_num)) (phiM_even' hf)
    (phiM_antitoneOn' hf hϱ hw) (phiM_le_one' hf hϱ hw) (fun x hx => phiM_eq_zero hϱ hw hx)

theorem integral_abs_deriv_phiM_sq_le' (hf : ProfileFactor f L A B) (hϱ : TaperProfile ϱ)
    (hw : 0 < w) (hwL : 2 * w ≤ L) : ∫ u, |deriv (fun u => phiM f ϱ L w u ^ 2) u| ≤ 2 := by
  have hL : 0 < L := by linarith
  refine integral_abs_deriv_le_two (by positivity : (0:ℝ) < L / 2)
    (((phiM_contDiff' hf hϱ hw hwL).pow 2).of_le (by norm_num)) ?_ ?_ ?_ ?_
  · intro x; rw [phiM_even' hf]
  · intro x hx y hy hxy
    exact pow_le_pow_left₀ (phiM_nonneg' hf hϱ hw y) (phiM_antitoneOn' hf hϱ hw hx hy hxy) 2
  · intro x
    calc phiM f ϱ L w x ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (phiM_nonneg' hf hϱ hw x) (phiM_le_one' hf hϱ hw x) 2
      _ = 1 := one_pow 2
  · intro x hx
    rw [phiM_eq_zero hϱ hw hx, zero_pow two_ne_zero]

theorem ProfileFactor.abs_le_one (hf : ProfileFactor f L A B) (u : ℝ) (hu : |u| ≤ L / 2) :
    |f u| ≤ 1 := by
  rw [abs_of_nonneg (hf.nonneg u hu)]; exact hf.le_one u hu

/-- ‖φ_f″‖₁ ≤ cMod/w (verbatim the tree's proof, with the local hypotheses). -/
theorem integral_abs_deriv2_phiM_le' (hf : ProfileFactor f L A B) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) : ∫ u, |deriv (deriv (phiM f ϱ L w)) u| ≤ cMod ϱ A B / w := by
  have hw0 : 0 < w := by linarith
  have h2wL : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  obtain ⟨δ, hδ, hsm⟩ := hf.smooth
  have hmain := integral_abs_deriv2_mul_le (F := f) (G := Taper.phi ϱ L w) (L := L) hδ
    (div_nonneg hf.A_nonneg hL.le) (div_nonneg hf.B_nonneg (sq_nonneg L)) hsm hf.abs_le_one hf.deriv_le
    hf.deriv2_le ((Taper.phi_contDiff hϱ hw0 h2wL).of_le (by norm_num)) (Taper.phi_hasCompactSupport hϱ hw0)
    (fun u hu => Taper.phi_eq_zero hϱ hw0 hu.le) (phiM_contDiff' hf hϱ hw0 h2wL)
    (phiM_hasCompactSupport hϱ hw0)
  have hI0 := integral_abs_phi_le hϱ hw0 h2wL
  have hI1 : ∫ u, |deriv (Taper.phi ϱ L w) u| = 2 := Taper.integral_abs_deriv_phi hϱ hw0 h2wL
  have hI2 : ∫ u, |deriv (deriv (Taper.phi ϱ L w)) u| = 2 * Taper.l1Deriv2 ϱ / w :=
    Taper.integral_abs_deriv2_phi hϱ hw0 h2wL
  rw [hI1, hI2] at hmain
  have hc := Taper.two_mul_l1Deriv2_le_cRho hϱ
  have hl1 := l1Deriv2_nonneg' ϱ
  have hA := hf.A_nonneg; have hB := hf.B_nonneg
  refine hmain.trans ?_
  have e1 : B / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ B / w := by
    calc B / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ B / L ^ 2 * L := by gcongr
      _ = B / L := by field_simp
      _ ≤ B / w := div_le_div_of_nonneg_left hB hw0 (by linarith)
  have e2 : 2 * (A / L) * 2 ≤ A / w := by
    rw [show 2 * (A / L) * 2 = 4 * A / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
  have e3 : 2 * Taper.l1Deriv2 ϱ / w ≤ Taper.cRho ϱ / w := div_le_div_of_nonneg_right hc hw0.le
  have e4 : 0 ≤ A ^ 2 / w := by positivity
  calc B / L ^ 2 * (∫ u, |Taper.phi ϱ L w u|) + 2 * (A / L) * 2 + 2 * Taper.l1Deriv2 ϱ / w
      ≤ B / w + A / w + Taper.cRho ϱ / w + A ^ 2 / w := by linarith
    _ = cMod ϱ A B / w := by simp only [cMod]; ring

/-- ‖(φ_f²)″‖₁ ≤ cMod/w (verbatim the tree's proof, with the local hypotheses). -/
theorem integral_abs_deriv2_phiM_sq_le' (hf : ProfileFactor f L A B) (hϱ : TaperProfile ϱ)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (deriv (fun u => phiM f ϱ L w u ^ 2)) u| ≤ cMod ϱ A B / w := by
  have hw0 : 0 < w := by linarith
  have h2wL : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  obtain ⟨δ, hδ, hsm⟩ := hf.smooth
  set U : Set ℝ := Ioo (-(L / 2 + δ)) (L / 2 + δ) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have hcore : ∀ u, |u| ≤ L / 2 → u ∈ U := fun u hu => by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have hsm2 : ContDiffOn ℝ 2 (fun u => f u * f u) U := hsm.mul hsm
  have hA := hf.A_nonneg; have hB := hf.B_nonneg
  have hF0 : ∀ u, |u| ≤ L / 2 → |f u * f u| ≤ 1 := fun u hu => by
    rw [abs_mul]; have := hf.abs_le_one u hu; nlinarith [abs_nonneg (f u)]
  have hF1 : ∀ u, |u| ≤ L / 2 → |deriv (fun u => f u * f u) u| ≤ 2 * A / L := fun u hu => by
    rw [deriv_mul_eq hU hsm hsm (hcore u hu)]
    have h0 := hf.abs_le_one u hu; have h1 := hf.deriv_le u hu
    calc |deriv f u * f u + f u * deriv f u| = 2 * (|f u| * |deriv f u|) := by
          rw [show deriv f u * f u + f u * deriv f u = 2 * (f u * deriv f u) by ring, abs_mul, abs_mul,
            abs_two]
      _ ≤ 2 * (1 * (A / L)) := by gcongr
      _ = 2 * A / L := by ring
  have hF2 : ∀ u, |u| ≤ L / 2 → |deriv (deriv (fun u => f u * f u)) u| ≤ (2 * B + 2 * A ^ 2) / L ^ 2 :=
    fun u hu => by
    rw [deriv2_mul_eq hU hsm hsm (hcore u hu)]
    have h0 := hf.abs_le_one u hu; have h1 := hf.deriv_le u hu; have h2 := hf.deriv2_le u hu
    have hd0 := abs_nonneg (deriv f u)
    calc |deriv (deriv f) u * f u + 2 * (deriv f u * deriv f u) + f u * deriv (deriv f) u|
        ≤ |deriv (deriv f) u * f u| + |2 * (deriv f u * deriv f u)| + |f u * deriv (deriv f) u| :=
          abs_add_three _ _ _
      _ = 2 * (|deriv (deriv f) u| * |f u|) + 2 * (|deriv f u| * |deriv f u|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
      _ ≤ 2 * (B / L ^ 2 * 1) + 2 * (A / L * (A / L)) := by gcongr
      _ = (2 * B + 2 * A ^ 2) / L ^ 2 := by field_simp
  have hφ := Taper.phi_contDiff hϱ hw0 h2wL
  have hG : ContDiff ℝ 2 (fun u => Taper.phi ϱ L w u ^ 2) := (hφ.pow 2).of_le (by norm_num)
  have hGcs : HasCompactSupport (fun u => Taper.phi ϱ L w u ^ 2) :=
    (Taper.phi_hasCompactSupport hϱ (L := L) hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hGzero : ∀ u, L / 2 < |u| → Taper.phi ϱ L w u ^ 2 = 0 := fun u hu => by
    rw [Taper.phi_eq_zero hϱ hw0 hu.le, zero_pow two_ne_zero]
  have hH : ContDiff ℝ 2 (fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2)) := by
    rw [← phiM_sq_eq]; exact (phiM_contDiff' hf hϱ hw0 h2wL).pow 2
  have hHcs : HasCompactSupport (fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2)) := by
    rw [← phiM_sq_eq]; exact (phiM_hasCompactSupport hϱ hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hmain := integral_abs_deriv2_mul_le (F := fun u => f u * f u) (G := fun u => Taper.phi ϱ L w u ^ 2)
    (L := L) hδ (by positivity : (0:ℝ) ≤ 2 * A / L) (by positivity : (0:ℝ) ≤ (2 * B + 2 * A ^ 2) / L ^ 2)
    hsm2 hF0 hF1 hF2 hG hGcs hGzero hH hHcs
  rw [phiM_sq_eq]
  have hI0 := integral_abs_phi_sq_le hϱ hw0 h2wL
  have hI1 : ∫ u, |deriv (fun u => Taper.phi ϱ L w u ^ 2) u| = 2 := Taper.integral_abs_deriv_phi_sq hϱ hw0 h2wL
  have hI2 : ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u| ≤ Taper.cRho ϱ / w :=
    Taper.integral_abs_deriv2_phi_sq_le hϱ hw h2wL
  rw [hI1] at hmain
  refine hmain.trans ?_
  have e1 : (2 * B + 2 * A ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2| ≤ (B + A ^ 2) / w := by
    calc (2 * B + 2 * A ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2|
        ≤ (2 * B + 2 * A ^ 2) / L ^ 2 * L := by gcongr
      _ = (2 * B + 2 * A ^ 2) / L := by field_simp
      _ ≤ (B + A ^ 2) / w := by rw [div_le_div_iff₀ hL hw0]; nlinarith
  have e2 : 2 * (2 * A / L) * 2 ≤ A / w := by
    rw [show 2 * (2 * A / L) * 2 = 8 * A / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
  calc (2 * B + 2 * A ^ 2) / L ^ 2 * (∫ u, |Taper.phi ϱ L w u ^ 2|) + 2 * (2 * A / L) * 2
        + ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u|
      ≤ (B + A ^ 2) / w + A / w + Taper.cRho ϱ / w := by linarith
    _ = cMod ϱ A B / w := by simp only [cMod]; ring

/-- **(2) the product window `q·φ` is an admissible window** under the LOCAL hypotheses
`ProfileFactor q L A B`, with constant `c' = cMod ϱ A B = cRho ϱ + A + A² + B`. -/
theorem admWindow_mul_phi (hf : ProfileFactor q L A B) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) : AdmWindow (fun u => q u * Taper.phi ϱ L w u) L w (cMod ϱ A B) where
  one_le_w := hw
  w8 := hwL
  four_le_c := four_le_cMod hϱ hf.A_nonneg hf.B_nonneg
  even := phiM_even' hf
  nonneg := phiM_nonneg' hf hϱ (by linarith)
  le_one := phiM_le_one' hf hϱ (by linarith)
  contDiff := phiM_contDiff' hf hϱ (by linarith) (by linarith)
  support := fun _ hu => phiM_eq_zero hϱ (by linarith) hu
  l1_deriv := integral_abs_deriv_phiM_le' hf hϱ (by linarith) (by linarith)
  l1_deriv_sq := integral_abs_deriv_phiM_sq_le' hf hϱ (by linarith) (by linarith)
  l1_deriv2 := integral_abs_deriv2_phiM_le' hf hϱ hw hwL
  l1_deriv2_sq := integral_abs_deriv2_phiM_sq_le' hf hϱ hw hwL

/-! ## §P  the polynomial application  q(u) = pp.eval (u/ℒ) -/

section Poly
open Polynomial

/-- the polynomial profile factor in the `u`-variable. -/
def polyQ (pp : ℝ[X]) (ℒ : ℝ) (u : ℝ) : ℝ := pp.eval (u / ℒ)

lemma contDiff_eval_poly (pp : ℝ[X]) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : ℝ => pp.eval x) := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) pp n
  simpa [Polynomial.coe_aeval_eq_eval] using this

lemma polyQ_contDiff (pp : ℝ[X]) (ℒ : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (polyQ pp ℒ) :=
  (contDiff_eval_poly pp n).comp (contDiff_id.div_const ℒ)

lemma iteratedDeriv_eval_poly (pp : ℝ[X]) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => pp.eval x) = fun x => (derivative^[j] pp).eval x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [Polynomial.deriv, Function.iterate_succ_apply']

/-- `q^{(j)}(u) = ℒ^{−j}·pp^{(j)}(u/ℒ)`. -/
lemma iteratedDeriv_polyQ (pp : ℝ[X]) (ℒ : ℝ) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (polyQ pp ℒ) u = (ℒ⁻¹) ^ j * (derivative^[j] pp).eval (u / ℒ) := by
  have e : polyQ pp ℒ = fun u => (fun x : ℝ => pp.eval x) (ℒ⁻¹ * u) := by
    funext u; simp only [polyQ, div_eq_inv_mul]
  rw [e, iteratedDeriv_comp_const_mul (contDiff_eval_poly pp j) ℒ⁻¹, iteratedDeriv_eval_poly]
  simp only [div_eq_inv_mul]

/-- the derivative bounds for Task A: `Mq j := M j / ℒ^j` for `j ≤ deg pp`, `0` beyond. -/
def polyMq (pp : ℝ[X]) (ℒ : ℝ) (M : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ pp.natDegree then M j / ℒ ^ j else 0

lemma polyMq_eq_zero (pp : ℝ[X]) (ℒ : ℝ) (M : ℕ → ℝ) {j : ℕ} (hj : pp.natDegree < j) :
    polyMq pp ℒ M j = 0 := by
  simp [polyMq, not_le.mpr hj]

/-- if `|pp^{(j)}(t)| ≤ M j` for `|t| ≤ L/(2ℒ)` then `|q^{(j)}(u)| ≤ polyMq j` for `|u| ≤ L/2`. -/
lemma abs_iteratedDeriv_polyQ_le (pp : ℝ[X]) {ℒ L : ℝ} (hℒ : 0 < ℒ) (M : ℕ → ℝ)
    (hM : ∀ j t, |t| ≤ L / (2 * ℒ) → |(derivative^[j] pp).eval t| ≤ M j)
    (j : ℕ) (u : ℝ) (hu : |u| ≤ L / 2) :
    |iteratedDeriv j (polyQ pp ℒ) u| ≤ polyMq pp ℒ M j := by
  rw [iteratedDeriv_polyQ]
  have ht : |u / ℒ| ≤ L / (2 * ℒ) := by
    rw [abs_div, abs_of_pos hℒ, div_le_div_iff₀ hℒ (by positivity)]
    nlinarith
  rcases le_or_gt j pp.natDegree with hj | hj
  · rw [polyMq, if_pos hj, abs_mul, abs_pow, abs_inv, abs_of_pos hℒ]
    calc ℒ⁻¹ ^ j * |(derivative^[j] pp).eval (u / ℒ)| ≤ ℒ⁻¹ ^ j * M j :=
          mul_le_mul_of_nonneg_left (hM j _ ht) (by positivity)
      _ = M j / ℒ ^ j := by rw [inv_pow]; ring
  · rw [polyMq, if_neg (not_le.mpr hj), Polynomial.iterate_derivative_eq_zero hj, eval_zero,
      mul_zero, abs_zero]

/-- the profile factor hypotheses for `q u = pp.eval (u/ℒ)`, with `λ := L/ℒ`:
`A = M₁·λ`, `B = M₂·λ²` (so `A/L = M₁/ℒ`, `B/L² = M₂/ℒ²`). -/
theorem profileFactor_polyQ (pp : ℝ[X]) {ℒ L : ℝ} (hℒ : 0 < ℒ) (hL : 0 < L) {M1 M2 : ℝ}
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (heven : ∀ t, pp.eval (-t) = pp.eval t)
    (hnonneg : ∀ t, |t| ≤ L / (2 * ℒ) → 0 ≤ pp.eval t)
    (hle_one : ∀ t, |t| ≤ L / (2 * ℒ) → pp.eval t ≤ 1)
    (hanti : AntitoneOn (fun t => pp.eval t) (Icc 0 (L / (2 * ℒ))))
    (hd1 : ∀ t, |t| ≤ L / (2 * ℒ) → |(derivative pp).eval t| ≤ M1)
    (hd2 : ∀ t, |t| ≤ L / (2 * ℒ) → |(derivative (derivative pp)).eval t| ≤ M2) :
    ProfileFactor (polyQ pp ℒ) L (M1 * (L / ℒ)) (M2 * (L / ℒ) ^ 2) where
  A_nonneg := by positivity
  B_nonneg := by positivity
  even := fun u => by simp only [polyQ, neg_div, heven]
  nonneg := fun u hu => hnonneg _ (by
    rw [abs_div, abs_of_pos hℒ, div_le_div_iff₀ hℒ (by positivity)]; nlinarith)
  le_one := fun u hu => hle_one _ (by
    rw [abs_div, abs_of_pos hℒ, div_le_div_iff₀ hℒ (by positivity)]; nlinarith)
  antitone := by
    intro x hx y hy hxy
    simp only [polyQ]
    apply hanti
    · exact ⟨by have := hx.1; positivity, by rw [div_le_div_iff₀ hℒ (by positivity)]; nlinarith [hx.2]⟩
    · exact ⟨by have := hy.1; positivity, by rw [div_le_div_iff₀ hℒ (by positivity)]; nlinarith [hy.2]⟩
    · exact div_le_div_of_nonneg_right hxy hℒ.le
  smooth := ⟨1, one_pos, (polyQ_contDiff pp ℒ 2).contDiffOn⟩
  deriv_le := fun u hu => by
    have h := iteratedDeriv_polyQ pp ℒ 1 u
    rw [iteratedDeriv_one] at h
    rw [h, abs_mul, abs_pow, abs_inv, abs_of_pos hℒ, pow_one, Function.iterate_one]
    have ht : |u / ℒ| ≤ L / (2 * ℒ) := by
      rw [abs_div, abs_of_pos hℒ, div_le_div_iff₀ hℒ (by positivity)]; nlinarith
    calc ℒ⁻¹ * |(derivative pp).eval (u / ℒ)| ≤ ℒ⁻¹ * M1 :=
          mul_le_mul_of_nonneg_left (hd1 _ ht) (by positivity)
      _ = M1 * (L / ℒ) / L := by field_simp
  deriv2_le := fun u hu => by
    have h := iteratedDeriv_polyQ pp ℒ 2 u
    rw [iteratedDeriv_succ, iteratedDeriv_one] at h
    rw [h, abs_mul, abs_pow, abs_inv, abs_of_pos hℒ]
    have ht : |u / ℒ| ≤ L / (2 * ℒ) := by
      rw [abs_div, abs_of_pos hℒ, div_le_div_iff₀ hℒ (by positivity)]; nlinarith
    have e : (derivative^[2] pp) = derivative (derivative pp) := by
      rw [Function.iterate_succ_apply', Function.iterate_one]
    rw [e]
    calc ℒ⁻¹ ^ 2 * |(derivative (derivative pp)).eval (u / ℒ)| ≤ ℒ⁻¹ ^ 2 * M2 :=
          mul_le_mul_of_nonneg_left (hd2 _ ht) (by positivity)
      _ = M2 * (L / ℒ) ^ 2 / L ^ 2 := by field_simp

/-- the polynomial product window is admissible, with
`c' = cRho ϱ + M₁λ + M₁²λ² + M₂λ²`, `λ = L/ℒ`. -/
theorem admWindow_polyQ_mul_phi (pp : ℝ[X]) {ℒ : ℝ} (hℒ : 0 < ℒ) {M1 M2 : ℝ}
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (heven : ∀ t, pp.eval (-t) = pp.eval t)
    (hnonneg : ∀ t, |t| ≤ L / (2 * ℒ) → 0 ≤ pp.eval t)
    (hle_one : ∀ t, |t| ≤ L / (2 * ℒ) → pp.eval t ≤ 1)
    (hanti : AntitoneOn (fun t => pp.eval t) (Icc 0 (L / (2 * ℒ))))
    (hd1 : ∀ t, |t| ≤ L / (2 * ℒ) → |(derivative pp).eval t| ≤ M1)
    (hd2 : ∀ t, |t| ≤ L / (2 * ℒ) → |(derivative (derivative pp)).eval t| ≤ M2)
    (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    AdmWindow (fun u => pp.eval (u / ℒ) * Taper.phi ϱ L w u) L w
      (cMod ϱ (M1 * (L / ℒ)) (M2 * (L / ℒ) ^ 2)) :=
  admWindow_mul_phi (profileFactor_polyQ pp hℒ (by linarith) hM1 hM2 heven hnonneg hle_one hanti hd1 hd2)
    hϱ hw hwL

/-- explicit coefficient-sum bound for `|pp^{(j)}|` on `[−R, R]`:
`M_j := Σ_i |coeff_i(pp^{(j)})|·R^i`. -/
def Mpoly (pp : ℝ[X]) (R : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((derivative^[j] pp).natDegree + 1), |(derivative^[j] pp).coeff i| * R ^ i

lemma abs_eval_le_Mpoly (pp : ℝ[X]) {R : ℝ} (j : ℕ) {t : ℝ} (ht : |t| ≤ R) :
    |(derivative^[j] pp).eval t| ≤ Mpoly pp R j := by
  unfold Mpoly
  rw [Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ht i) (abs_nonneg _)

/-- **Task A for the polynomial window** `pp.eval (u/ℒ) · φ(u)`: with `λ := L/ℒ` and `M j` any
bounds `|pp^{(j)}(t)| ≤ M j` on `|t| ≤ λ/2` (e.g. `Mpoly pp (λ/2)`),
`‖(q·φ)^{(k)}‖₁ ≤ 2·B'·w·(A/w)^k·k^{sk}` with
`B' = B·Σ_{j≤deg} M j (w/(ℒA))^j + (1/2)·Σ_{j≤deg} M j (λ/A)^j`. -/
theorem gevrey_polyQ_mul_phi (hϱ : GevreyProfile s A B ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (pp : ℝ[X]) {ℒ : ℝ} (hℒ : 0 < ℒ) (M : ℕ → ℝ)
    (hM : ∀ j t, |t| ≤ L / (2 * ℒ) → |(derivative^[j] pp).eval t| ≤ M j) {k : ℕ} (hk : 1 ≤ k) :
    ∫ u, |iteratedDeriv k (fun u => pp.eval (u / ℒ) * phi ϱ L w u) u|
      ≤ 2 * (B * (∑ j ∈ Finset.range (pp.natDegree + 1), M j * (w / (ℒ * A)) ^ j)
            + (∑ j ∈ Finset.range (pp.natDegree + 1), M j * (L / ℒ / A) ^ j) / 2)
          * w * (A / w) ^ k * (k : ℝ) ^ (s * k) := by
  have hA := hϱ.A_pos
  have hL : 0 < L := by linarith
  have hwL' : w ≤ L := by linarith
  have hM0 : ∀ j, 0 ≤ M j := fun j =>
    (abs_nonneg _).trans (hM j 0 (by rw [abs_zero]; positivity))
  set Mq := polyMq pp ℒ M with hMqdef
  have hMq : ∀ i u, |u| ≤ L / 2 → |iteratedDeriv i (polyQ pp ℒ) u| ≤ Mq i :=
    fun i u hu => abs_iteratedDeriv_polyQ_le pp hℒ M hM i u hu
  have hMq0 : ∀ i, 0 ≤ Mq i := fun i => by
    rw [hMqdef, polyMq]; split_ifs
    · exact div_nonneg (hM0 i) (by positivity)
    · exact le_rfl
  -- S
  set S : ℝ := ∑ j ∈ Finset.range (pp.natDegree + 1), M j * (w / (ℒ * A)) ^ j with hS
  have hSeq : S = ∑ j ∈ Finset.range (pp.natDegree + 1), Mq j * (w / A) ^ j := by
    rw [hS]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ pp.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [hMqdef, polyMq, if_pos hj', div_pow, div_pow, mul_pow]
    field_simp
  have hf0 : ∀ i, 0 ≤ Mq i * (w / A) ^ i := fun i => mul_nonneg (hMq0 i) (by positivity)
  have hSbound : ∀ n, ∑ i ∈ Finset.range n, Mq i * (w / A) ^ i ≤ S := by
    intro n
    rw [hSeq]
    have h1 : ∑ i ∈ Finset.range n, Mq i * (w / A) ^ i
        ≤ ∑ i ∈ Finset.range (n + pp.natDegree + 1), Mq i * (w / A) ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega : n ≤ n + pp.natDegree + 1)) (fun i _ _ => hf0 i)
    have h2 : ∑ i ∈ Finset.range (pp.natDegree + 1), Mq i * (w / A) ^ i
        = ∑ i ∈ Finset.range (n + pp.natDegree + 1), Mq i * (w / A) ^ i := by
      apply Finset.sum_subset
        (Finset.range_mono (by omega : pp.natDegree + 1 ≤ n + pp.natDegree + 1))
      intro i _ hi
      rw [Finset.mem_range, not_lt] at hi
      rw [hMqdef, polyMq_eq_zero pp ℒ M (by omega), zero_mul]
    rw [h2]; exact h1
  -- T
  set T : ℝ := w * ∑ j ∈ Finset.range (pp.natDegree + 1), M j * (L / ℒ / A) ^ j with hT
  have hTbound : ∀ n, 1 ≤ n → Mq n * L * (w / A) ^ n ≤ T := by
    intro n hn
    rcases le_or_gt n pp.natDegree with hnd | hnd
    · have hterm : M n * (L / ℒ / A) ^ n
          ≤ ∑ j ∈ Finset.range (pp.natDegree + 1), M j * (L / ℒ / A) ^ j :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hM0 j) (by positivity))
          (Finset.mem_range.mpr (by omega))
      -- L·w^n ≤ w·L^n  (n ≥ 1, w ≤ L)
      have hpow : L * w ^ n ≤ w * L ^ n := by
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have : w ^ n' ≤ L ^ n' := pow_le_pow_left₀ hw.le hwL' n'
        rw [pow_succ, pow_succ]
        nlinarith [mul_nonneg hL.le hw.le, mul_le_mul_of_nonneg_left this (mul_nonneg hL.le hw.le)]
      have e1 : Mq n * L * (w / A) ^ n = M n * (L * w ^ n) / (ℒ ^ n * A ^ n) := by
        rw [hMqdef, polyMq, if_pos hnd, div_pow]; field_simp
      have e2 : w * (M n * (L / ℒ / A) ^ n) = M n * (w * L ^ n) / (ℒ ^ n * A ^ n) := by
        rw [div_pow, div_pow]; field_simp
      calc Mq n * L * (w / A) ^ n = M n * (L * w ^ n) / (ℒ ^ n * A ^ n) := e1
        _ ≤ M n * (w * L ^ n) / (ℒ ^ n * A ^ n) := by
            gcongr; exact hM0 n
        _ = w * (M n * (L / ℒ / A) ^ n) := e2.symm
        _ ≤ T := by rw [hT]; exact mul_le_mul_of_nonneg_left hterm hw.le
    · rw [hMqdef, polyMq_eq_zero pp ℒ M hnd, zero_mul, zero_mul, hT]
      apply mul_nonneg hw.le
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hM0 j) (by positivity)
  have h := integral_abs_iteratedDeriv_mul_phi_le_of_bounds hϱ hw hwL
    (polyQ_contDiff pp ℒ _) hMq hSbound hTbound hk
  have e : T / (2 * w) = (∑ j ∈ Finset.range (pp.natDegree + 1), M j * (L / ℒ / A) ^ j) / 2 := by
    rw [hT]; field_simp
  rw [e] at h
  exact h

end Poly


end ProductWindow
end Zeta23

end
