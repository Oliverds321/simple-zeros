/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/DesignProfile.lean — **the two DESIGN PROFILES `p` of the profile-weighted window, and
everything the design of record needs to know about them.**

The q-aspect paper's design window is `φ(u) = p(u/ℒ)·ϱ₂((L/2 − |u|)/w)` (`ZetaQ/Defs.lean` §3–4;
the module header of `ZetaQ/Budget.lean` records why the window has to carry a profile factor at
all — a flat taper cannot reach the constant the payoff functional is minimised at), with `p` an
even polynomial of degree 6 whose square is
§11's profile `v = p²` on the design support `[−λ*/2, λ*/2]`. This file ships, for each family:

  * the polynomial (`designProfileQle`, `designProfileDyadic`) — coefficients from
    the authoring project's `profile_design.py`, which is not shipped (degree 6 in the MONOMIAL basis,
    support FIXED at `b = λ*/2` so that the certificate's support is the design's, coefficients
    rationalised to denominator `10⁶`);
  * its `ProfileQ` class at `λ*` (even, `1/6 ≤ p ≤ 1` on the core, nonincreasing on `[0, λ*/2]`);
  * the core integrals `∫_{−c}^{c} p²`, `∫_{−c}^{c} p⁴` below which the window moments `a`, `b`
    cannot fall (`aQ_ge_core`, `bQ_ge_core`), evaluated at the design's core, giving the two
    `Valid` floors `a ≥ 3/4`, `b ≥ 1/2`;
  * the derivative-bound sums behind the product-window Gevrey constant `gevreyBprod`
    (`Mpoly` bounds), giving `gevreyBprod gevreyA gevreyB ≤ 30000` at the design.

Numerics (`profile_design.py`, exact ℚ): q ≤ Q — `B = 1.2787464`, `P = 0.7212536 ≥ 0.7212`,
`p(λ*/2) = 0.1772`, `a_core = 0.7832`, `b_core = 0.6838`, `M_j = 2.88, 14.7, 102, 590, 2666,
8262, 13212`, `Σ_j M_j (λ/A)^j = 5.96`; dyadic — `B = 1.2901591`, `P = 0.7098409` (so the dyadic
smooth certificate ships `0.7098`, below the paper's `0.7099`: a degree-6 `p` at the FIXED support
`λ*_dyad/2` does not reach the fourth digit — recorded, see `ZetaQ/Payoff.lean`), `p(λ*/2) = 0.2066`,
`a_core = 0.8017`, `b_core = 0.7031`.

Imports `ZetaQ.Window`, `ZetaQ.Certificate` (for `Family`), `ZetaQ.Payoff`. Imported by
`ZetaQ.Budget`.

RULE 17: nothing here mentions `X`, `T`, `D₀`; `λ` enters only as the literal `λ* > 1`.
-/
import ZetaQ.Window
import ZetaQ.Certificate
import ZetaQ.Payoff

noncomputable section

open Polynomial Real MeasureTheory Set

namespace ZetaQ

/-! ## 1. The two polynomials -/

/-- **The design profile for `q ≤ Q`** (`C = π⁴/18`, support `λ*/2 = 0.62536607575`):
`p(t) = 1 − 0.650056 t² + 3.458583 t⁴ − 18.349255 t⁶`. -/
def designProfileQle : ℝ[X] :=
  C 1 + C (-81257 / 125000 : ℝ) * X ^ 2 + C (3458583 / 1000000 : ℝ) * X ^ 4
    + C (-3669851 / 200000 : ℝ) * X ^ 6

/-- **The design profile for the dyadic family** (`C = 2π⁴/27`, support `λ*_dyad/2 =
0.5965790605`): `p(t) = 1 − 1.014099 t² + 8.34917 t⁴ − 33.051334 t⁶`. -/
def designProfileDyadic : ℝ[X] :=
  C 1 + C (-1014099 / 1000000 : ℝ) * X ^ 2 + C (834917 / 100000 : ℝ) * X ^ 4
    + C (-16525667 / 500000 : ℝ) * X ^ 6

/-! **Corollary 3's two smooth design profiles** (degree 10 for the even/odd dyadic family at
`C = 4π⁴/27`, degree 8 for even/odd over `q ≤ Q` at `C = π⁴/9`). These were written in
`ZetaQ/Cor3Smooth.lean` and MOVED here when `ZetaQ.Family` gained its four parity
constructors: `Family.designProfile` is defined in this file and `Cor3Smooth.lean` imports it
(through `PayoffSmooth.lean`), so leaving them below would have been an import cycle. The
proofs are unchanged — self-contained Bernstein `linarith`/`nlinarith` calls with no
`PayoffSmooth` dependency. -/

/-- the even design profile: `p(t) = 1 + (-306129 / 500000) t^2 + (387781 / 62500) t^4 + (-28365317 / 250000) t^6 + (397141241 / 500000) t^8 + (-46455797 / 25000) t^10`. -/
def designProfileEvenDyad : ℝ[X] :=
  C 1
    + C (-306129 / 500000 : ℝ) * X ^ 2
    + C (387781 / 62500 : ℝ) * X ^ 4
    + C (-28365317 / 250000 : ℝ) * X ^ 6
    + C (397141241 / 500000 : ℝ) * X ^ 8
    + C (-46455797 / 25000 : ℝ) * X ^ 10

theorem designProfileEvenDyad_eval (t : ℝ) :
    designProfileEvenDyad.eval t = 1 + (-306129 / 500000) * t ^ 2 + (387781 / 62500) * t ^ 4 + (-28365317 / 250000) * t ^ 6 + (397141241 / 500000) * t ^ 8 + (-46455797 / 25000) * t ^ 10 := by
  simp [designProfileEvenDyad]

theorem designProfileEvenDyad_natDegree_le : designProfileEvenDyad.natDegree ≤ 10 := by
  unfold designProfileEvenDyad; compute_degree

theorem designProfileEvenDyad_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => designProfileEvenDyad.eval s) ((-306129 / 250000) * t ^ 1 + (387781 / 15625) * t ^ 3 + (-85095951 / 125000) * t ^ 5 + (397141241 / 62500) * t ^ 7 + (-46455797 / 2500) * t ^ 9) t := by
  have e : (fun s : ℝ => designProfileEvenDyad.eval s) = fun s : ℝ => 1 + (-306129 / 500000) * s ^ 2 + (387781 / 62500) * s ^ 4 + (-28365317 / 250000) * s ^ 6 + (397141241 / 500000) * s ^ 8 + (-46455797 / 25000) * s ^ 10 := by
    funext s; exact designProfileEvenDyad_eval s
  rw [e]
  have h0 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have h1 := (hasDerivAt_pow 2 t).const_mul ((-306129 / 500000 : ℝ))
  have h2 := (hasDerivAt_pow 4 t).const_mul ((387781 / 62500 : ℝ))
  have h3 := (hasDerivAt_pow 6 t).const_mul ((-28365317 / 250000 : ℝ))
  have h4 := (hasDerivAt_pow 8 t).const_mul ((397141241 / 500000 : ℝ))
  have h5 := (hasDerivAt_pow 10 t).const_mul ((-46455797 / 25000 : ℝ))
  have h := (((((h0.add h1).add h2).add h3).add h4).add h5)
  refine h.congr_deriv ?_
  push_cast; ring

/-- `q'(x) ≤ 0` on `[0, 1517 / 5000]` where `p(t) = q(t²)` (Bernstein certificate, degree 16). -/
theorem designProfileEvenDyad_qderiv_nonpos (x : ℝ) (hx0 : 0 ≤ x) (hxB : x ≤ 1517 / 5000) :
    (-306129 / 500000) * x ^ 0 + (387781 / 31250) * x ^ 1 + (-85095951 / 250000) * x ^ 2 + (397141241 / 125000) * x ^ 3 + (-46455797 / 5000) * x ^ 4 ≤ 0 := by
  have hB : 0 ≤ 1517 / 5000 - x := by linarith
  linarith [mul_nonneg (pow_nonneg hx0 0) (pow_nonneg hB 16), mul_nonneg (pow_nonneg hx0 1) (pow_nonneg hB 15), mul_nonneg (pow_nonneg hx0 2) (pow_nonneg hB 14), mul_nonneg (pow_nonneg hx0 3) (pow_nonneg hB 13), mul_nonneg (pow_nonneg hx0 4) (pow_nonneg hB 12), mul_nonneg (pow_nonneg hx0 5) (pow_nonneg hB 11), mul_nonneg (pow_nonneg hx0 6) (pow_nonneg hB 10), mul_nonneg (pow_nonneg hx0 7) (pow_nonneg hB 9), mul_nonneg (pow_nonneg hx0 8) (pow_nonneg hB 8), mul_nonneg (pow_nonneg hx0 9) (pow_nonneg hB 7), mul_nonneg (pow_nonneg hx0 10) (pow_nonneg hB 6), mul_nonneg (pow_nonneg hx0 11) (pow_nonneg hB 5), mul_nonneg (pow_nonneg hx0 12) (pow_nonneg hB 4), mul_nonneg (pow_nonneg hx0 13) (pow_nonneg hB 3), mul_nonneg (pow_nonneg hx0 14) (pow_nonneg hB 2), mul_nonneg (pow_nonneg hx0 15) (pow_nonneg hB 1), mul_nonneg (pow_nonneg hx0 16) (pow_nonneg hB 0)]

/-- **`designProfileEvenDyad ∈ ProfileQ` at `lamStarEvenDyad`**: even; `p' = 2t·q'(t²) ≤ 0` on `[0, λ/2]` so `p` is
antitone there; `p ≤ p(0) = 1`; `p ≥ p(λ/2) = 0.1700 ≥ 1/6`. -/
theorem profileQ_evendyad : ParamsQ.ProfileQ designProfileEvenDyad lamStarEvenDyad := by
  have heven : ∀ t : ℝ, designProfileEvenDyad.eval (-t) = designProfileEvenDyad.eval t := by
    intro t; rw [designProfileEvenDyad_eval, designProfileEvenDyad_eval]; ring
  have hlam : lamStarEvenDyad = 5507999211 / 5000000000 := by norm_num [lamStarEvenDyad]
  have hanti : AntitoneOn (fun t : ℝ => designProfileEvenDyad.eval t) (Set.Icc 0 (lamStarEvenDyad / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact (designProfileEvenDyad.continuous).continuousOn
    · exact (designProfileEvenDyad.differentiable).differentiableOn
    · intro t ht
      rw [interior_Icc] at ht
      rw [(designProfileEvenDyad_hasDerivAt t).deriv]
      have ht0 : 0 ≤ t := ht.1.le
      have ht2 : t ^ 2 ≤ 1517 / 5000 := by
        have : t ≤ lamStarEvenDyad / 2 := ht.2.le
        rw [hlam] at this
        nlinarith
      have hq := designProfileEvenDyad_qderiv_nonpos (t ^ 2) (sq_nonneg t) ht2
      have e : (-306129 / 250000) * t ^ 1 + (387781 / 15625) * t ^ 3 + (-85095951 / 125000) * t ^ 5 + (397141241 / 62500) * t ^ 7 + (-46455797 / 2500) * t ^ 9
          = 2 * t * ((-306129 / 500000) * (t ^ 2) ^ 0 + (387781 / 31250) * (t ^ 2) ^ 1 + (-85095951 / 250000) * (t ^ 2) ^ 2 + (397141241 / 125000) * (t ^ 2) ^ 3 + (-46455797 / 5000) * (t ^ 2) ^ 4) := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hq
  have habs : ∀ t : ℝ, designProfileEvenDyad.eval t = designProfileEvenDyad.eval |t| := by
    intro t
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, heven]
  have hlam0 : (0 : ℝ) ≤ lamStarEvenDyad / 2 := by rw [hlam]; norm_num
  refine ⟨heven, ?_, ?_, hanti⟩
  · intro t ht
    rw [habs]
    have h1 : designProfileEvenDyad.eval (lamStarEvenDyad / 2) ≤ designProfileEvenDyad.eval |t| :=
      hanti ⟨abs_nonneg t, ht⟩ ⟨hlam0, le_refl _⟩ ht
    have h2 : (1 : ℝ) / 6 ≤ designProfileEvenDyad.eval (lamStarEvenDyad / 2) := by
      rw [designProfileEvenDyad_eval, hlam]; norm_num
    linarith
  · intro t ht
    rw [habs]
    have h1 : designProfileEvenDyad.eval |t| ≤ designProfileEvenDyad.eval 0 :=
      hanti ⟨le_refl _, hlam0⟩ ⟨abs_nonneg t, ht⟩ (abs_nonneg t)
    have h2 : designProfileEvenDyad.eval 0 = 1 := by rw [designProfileEvenDyad_eval]; norm_num
    linarith

/-- the even design profile: `p(t) = 1 + (-66999 / 500000) t^2 + (-5495941 / 500000) t^4 + (100475221 / 1000000) t^6 + (-3503919 / 12500) t^8`. -/
def designProfileEvenQ : ℝ[X] :=
  C 1
    + C (-66999 / 500000 : ℝ) * X ^ 2
    + C (-5495941 / 500000 : ℝ) * X ^ 4
    + C (100475221 / 1000000 : ℝ) * X ^ 6
    + C (-3503919 / 12500 : ℝ) * X ^ 8

theorem designProfileEvenQ_eval (t : ℝ) :
    designProfileEvenQ.eval t = 1 + (-66999 / 500000) * t ^ 2 + (-5495941 / 500000) * t ^ 4 + (100475221 / 1000000) * t ^ 6 + (-3503919 / 12500) * t ^ 8 := by
  simp [designProfileEvenQ]

theorem designProfileEvenQ_natDegree_le : designProfileEvenQ.natDegree ≤ 8 := by
  unfold designProfileEvenQ; compute_degree

theorem designProfileEvenQ_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => designProfileEvenQ.eval s) ((-66999 / 250000) * t ^ 1 + (-5495941 / 125000) * t ^ 3 + (301425663 / 500000) * t ^ 5 + (-7007838 / 3125) * t ^ 7) t := by
  have e : (fun s : ℝ => designProfileEvenQ.eval s) = fun s : ℝ => 1 + (-66999 / 500000) * s ^ 2 + (-5495941 / 500000) * s ^ 4 + (100475221 / 1000000) * s ^ 6 + (-3503919 / 12500) * s ^ 8 := by
    funext s; exact designProfileEvenQ_eval s
  rw [e]
  have h0 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have h1 := (hasDerivAt_pow 2 t).const_mul ((-66999 / 500000 : ℝ))
  have h2 := (hasDerivAt_pow 4 t).const_mul ((-5495941 / 500000 : ℝ))
  have h3 := (hasDerivAt_pow 6 t).const_mul ((100475221 / 1000000 : ℝ))
  have h4 := (hasDerivAt_pow 8 t).const_mul ((-3503919 / 12500 : ℝ))
  have h := ((((h0.add h1).add h2).add h3).add h4)
  refine h.congr_deriv ?_
  push_cast; ring

/-- `q'(x) ≤ 0` on `[0, 321 / 1000]` where `p(t) = q(t²)` (Bernstein certificate, degree 13). -/
theorem designProfileEvenQ_qderiv_nonpos (x : ℝ) (hx0 : 0 ≤ x) (hxB : x ≤ 321 / 1000) :
    (-66999 / 500000) * x ^ 0 + (-5495941 / 250000) * x ^ 1 + (301425663 / 1000000) * x ^ 2 + (-3503919 / 3125) * x ^ 3 ≤ 0 := by
  have hB : 0 ≤ 321 / 1000 - x := by linarith
  linarith [mul_nonneg (pow_nonneg hx0 0) (pow_nonneg hB 13), mul_nonneg (pow_nonneg hx0 1) (pow_nonneg hB 12), mul_nonneg (pow_nonneg hx0 2) (pow_nonneg hB 11), mul_nonneg (pow_nonneg hx0 3) (pow_nonneg hB 10), mul_nonneg (pow_nonneg hx0 4) (pow_nonneg hB 9), mul_nonneg (pow_nonneg hx0 5) (pow_nonneg hB 8), mul_nonneg (pow_nonneg hx0 6) (pow_nonneg hB 7), mul_nonneg (pow_nonneg hx0 7) (pow_nonneg hB 6), mul_nonneg (pow_nonneg hx0 8) (pow_nonneg hB 5), mul_nonneg (pow_nonneg hx0 9) (pow_nonneg hB 4), mul_nonneg (pow_nonneg hx0 10) (pow_nonneg hB 3), mul_nonneg (pow_nonneg hx0 11) (pow_nonneg hB 2), mul_nonneg (pow_nonneg hx0 12) (pow_nonneg hB 1), mul_nonneg (pow_nonneg hx0 13) (pow_nonneg hB 0)]

/-- **`designProfileEvenQ ∈ ProfileQ` at `lamStarEvenQ`**: even; `p' = 2t·q'(t²) ≤ 0` on `[0, λ/2]` so `p` is
antitone there; `p ≤ p(0) = 1`; `p ≥ p(λ/2) = 0.1727 ≥ 1/6`. -/
theorem profileQ_evenq : ParamsQ.ProfileQ designProfileEvenQ lamStarEvenQ := by
  have heven : ∀ t : ℝ, designProfileEvenQ.eval (-t) = designProfileEvenQ.eval t := by
    intro t; rw [designProfileEvenQ_eval, designProfileEvenQ_eval]; ring
  have hlam : lamStarEvenQ = 11329788821 / 10000000000 := by norm_num [lamStarEvenQ]
  have hanti : AntitoneOn (fun t : ℝ => designProfileEvenQ.eval t) (Set.Icc 0 (lamStarEvenQ / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact (designProfileEvenQ.continuous).continuousOn
    · exact (designProfileEvenQ.differentiable).differentiableOn
    · intro t ht
      rw [interior_Icc] at ht
      rw [(designProfileEvenQ_hasDerivAt t).deriv]
      have ht0 : 0 ≤ t := ht.1.le
      have ht2 : t ^ 2 ≤ 321 / 1000 := by
        have : t ≤ lamStarEvenQ / 2 := ht.2.le
        rw [hlam] at this
        nlinarith
      have hq := designProfileEvenQ_qderiv_nonpos (t ^ 2) (sq_nonneg t) ht2
      have e : (-66999 / 250000) * t ^ 1 + (-5495941 / 125000) * t ^ 3 + (301425663 / 500000) * t ^ 5 + (-7007838 / 3125) * t ^ 7
          = 2 * t * ((-66999 / 500000) * (t ^ 2) ^ 0 + (-5495941 / 250000) * (t ^ 2) ^ 1 + (301425663 / 1000000) * (t ^ 2) ^ 2 + (-3503919 / 3125) * (t ^ 2) ^ 3) := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hq
  have habs : ∀ t : ℝ, designProfileEvenQ.eval t = designProfileEvenQ.eval |t| := by
    intro t
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, heven]
  have hlam0 : (0 : ℝ) ≤ lamStarEvenQ / 2 := by rw [hlam]; norm_num
  refine ⟨heven, ?_, ?_, hanti⟩
  · intro t ht
    rw [habs]
    have h1 : designProfileEvenQ.eval (lamStarEvenQ / 2) ≤ designProfileEvenQ.eval |t| :=
      hanti ⟨abs_nonneg t, ht⟩ ⟨hlam0, le_refl _⟩ ht
    have h2 : (1 : ℝ) / 6 ≤ designProfileEvenQ.eval (lamStarEvenQ / 2) := by
      rw [designProfileEvenQ_eval, hlam]; norm_num
    linarith
  · intro t ht
    rw [habs]
    have h1 : designProfileEvenQ.eval |t| ≤ designProfileEvenQ.eval 0 :=
      hanti ⟨le_refl _, hlam0⟩ ⟨abs_nonneg t, ht⟩ (abs_nonneg t)
    have h2 : designProfileEvenQ.eval 0 = 1 := by rw [designProfileEvenQ_eval]; norm_num
    linarith

/-! **The two REFIT parity design profiles, and why they replace the two above.**

`designProfileEvenDyad` (degree 10, at `lamStarEvenDyad = 1.1015998422`) and
`designProfileEvenQ` (degree 8, at `lamStarEvenQ = 1.1329788821`) are `ProfileQ` and carry
their moment floors, but their derivative-bound sums do NOT fit the product-window Gevrey
budget `gevreyBprod ≤ 40000`: that is exactly what `design_gevreyBprod_le_cor3` recorded as a
`sorry`. The refit trades `0.006` (resp. `0.004`) of `λ` for that budget —

  * `designProfileEvenDyad12`, degree 12, at `lamStarEvenDyad12 = 1.0955998422`;
    `M₀ = 4.734257…`, `min p on the core = p(λ'/2) = 0.2157286… ≥ 1/6`,
    `6000·Σ M_j 52^{-j} + ½Σ M_j 10^{-j} = 39000.0132…` (`39005.877…` with the rounded `M_j`);
  * `designProfileEvenQ10`, degree 10, at `lamStarEvenQ10 = 1.1289788821`;
    `M₀ = 5.230462…`, `min p = 0.1927273… ≥ 1/6`, surrogate `39000.0064…` (`39005.278…`) —

and `Family.designProfile` / `Family.lamStar` route the four parity constructors here.

**The two profiles above are NOT edited in place**: `ZetaQ/Cor3Smooth.lean` states
their admissibility certificates at `lamStarEvenDyad` / `lamStarEvenQ` exactly, and the
payoffs the refit realises (`P = 0.6919144470` / `0.6980487914`) are below the frozen
`PconstEvenDyadic` / `PconstEven` that `Family.payoff` returns — but ABOVE the shipped
certificates `Payoff.Pcert_even_dyad_smooth = 6919/10000` / `Payoff.Pcert_evenQ_smooth =
349/500`, and `ZetaQ.kappaC_le_kappaCert` consumes only `payoffCert ≤ payoff`. So
`Family.payoff` is unchanged and the proved chain is unaffected. -/

/-- **the degree-12 REFIT even/odd dyadic design profile**, at `λ' = lamStarEvenDyad12`:
`p(t) = 1 − 0.402449 t² − 1.139336 t⁴ − 16.037751 t⁶ + 181.892252 t⁸ − 2194.509137 t¹²`. -/
def designProfileEvenDyad12 : ℝ[X] :=
  C 1
    + C (-402449 / 1000000 : ℝ) * X ^ 2
    + C (-142417 / 125000 : ℝ) * X ^ 4
    + C (-16037751 / 1000000 : ℝ) * X ^ 6
    + C (45473063 / 250000 : ℝ) * X ^ 8
    + C (-2194509137 / 1000000 : ℝ) * X ^ 12

theorem designProfileEvenDyad12_eval (t : ℝ) :
    designProfileEvenDyad12.eval t = 1 + (-402449 / 1000000) * t ^ 2 + (-142417 / 125000) * t ^ 4 + (-16037751 / 1000000) * t ^ 6 + (45473063 / 250000) * t ^ 8 + (-2194509137 / 1000000) * t ^ 12 := by
  simp [designProfileEvenDyad12]

theorem designProfileEvenDyad12_natDegree_le : designProfileEvenDyad12.natDegree ≤ 12 := by
  unfold designProfileEvenDyad12; compute_degree

theorem designProfileEvenDyad12_coeff (k : ℕ) :
    designProfileEvenDyad12.coeff k
      = (if k = 0 then (1 : ℝ) else 0) + (if k = 2 then (-402449 / 1000000 : ℝ) else 0) + (if k = 4 then (-142417 / 125000 : ℝ) else 0) + (if k = 6 then (-16037751 / 1000000 : ℝ) else 0) + (if k = 8 then (45473063 / 250000 : ℝ) else 0) + (if k = 12 then (-2194509137 / 1000000 : ℝ) else 0) := by
  simp [designProfileEvenDyad12, coeff_add, Polynomial.coeff_one]

theorem designProfileEvenDyad12_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => designProfileEvenDyad12.eval s)
      ((-402449 / 500000) * t ^ 1 + (-142417 / 31250) * t ^ 3 + (-48113253 / 500000) * t ^ 5 + (45473063 / 31250) * t ^ 7 + (-6583527411 / 250000) * t ^ 11) t := by
  have e : (fun s : ℝ => designProfileEvenDyad12.eval s) = fun s : ℝ => 1 + (-402449 / 1000000) * s ^ 2 + (-142417 / 125000) * s ^ 4 + (-16037751 / 1000000) * s ^ 6 + (45473063 / 250000) * s ^ 8 + (-2194509137 / 1000000) * s ^ 12 := by
    funext s; exact designProfileEvenDyad12_eval s
  rw [e]
  have h0 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have h1 := (hasDerivAt_pow 2 t).const_mul ((-402449 / 1000000 : ℝ))
  have h2 := (hasDerivAt_pow 4 t).const_mul ((-142417 / 125000 : ℝ))
  have h3 := (hasDerivAt_pow 6 t).const_mul ((-16037751 / 1000000 : ℝ))
  have h4 := (hasDerivAt_pow 8 t).const_mul ((45473063 / 250000 : ℝ))
  have h5 := (hasDerivAt_pow 12 t).const_mul ((-2194509137 / 1000000 : ℝ))
  have h := (((((h0.add h1).add h2).add h3).add h4).add h5)
  refine h.congr_deriv ?_
  push_cast; ring

/-- `q'(x) ≤ 0` on `[0, 30009 / 100000]` where `p(t) = q(t²)` (Bernstein certificate, degree 15). -/
theorem designProfileEvenDyad12_qderiv_nonpos (x : ℝ) (hx0 : 0 ≤ x) (hxB : x ≤ 30009 / 100000) :
    (-402449 / 1000000) * x ^ 0 + (-142417 / 62500) * x ^ 1 + (-48113253 / 1000000) * x ^ 2 + (45473063 / 62500) * x ^ 3 + (-6583527411 / 500000) * x ^ 5 ≤ 0 := by
  have hB : 0 ≤ 30009 / 100000 - x := by linarith
  linarith [mul_nonneg (pow_nonneg hx0 0) (pow_nonneg hB 15), mul_nonneg (pow_nonneg hx0 1) (pow_nonneg hB 14), mul_nonneg (pow_nonneg hx0 2) (pow_nonneg hB 13), mul_nonneg (pow_nonneg hx0 3) (pow_nonneg hB 12), mul_nonneg (pow_nonneg hx0 4) (pow_nonneg hB 11), mul_nonneg (pow_nonneg hx0 5) (pow_nonneg hB 10), mul_nonneg (pow_nonneg hx0 6) (pow_nonneg hB 9), mul_nonneg (pow_nonneg hx0 7) (pow_nonneg hB 8), mul_nonneg (pow_nonneg hx0 8) (pow_nonneg hB 7), mul_nonneg (pow_nonneg hx0 9) (pow_nonneg hB 6), mul_nonneg (pow_nonneg hx0 10) (pow_nonneg hB 5), mul_nonneg (pow_nonneg hx0 11) (pow_nonneg hB 4), mul_nonneg (pow_nonneg hx0 12) (pow_nonneg hB 3), mul_nonneg (pow_nonneg hx0 13) (pow_nonneg hB 2), mul_nonneg (pow_nonneg hx0 14) (pow_nonneg hB 1), mul_nonneg (pow_nonneg hx0 15) (pow_nonneg hB 0)]

/-- **`designProfileEvenDyad12 ∈ ProfileQ` at `lamStarEvenDyad12`**: even; `p' = 2t·q'(t²) ≤ 0` on
`[0, λ'/2]`; `p ≤ p(0) = 1`; `p ≥ p(λ'/2) = 0.215729 ≥ 1/6`. -/
theorem profileQ_evendyad12 : ParamsQ.ProfileQ designProfileEvenDyad12 lamStarEvenDyad12 := by
  have heven : ∀ t : ℝ, designProfileEvenDyad12.eval (-t) = designProfileEvenDyad12.eval t := by
    intro t; rw [designProfileEvenDyad12_eval, designProfileEvenDyad12_eval]; ring
  have hlam : lamStarEvenDyad12 = 5477999211 / 5000000000 := by norm_num [lamStarEvenDyad12]
  have hanti : AntitoneOn (fun t : ℝ => designProfileEvenDyad12.eval t)
      (Set.Icc 0 (lamStarEvenDyad12 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact (designProfileEvenDyad12.continuous).continuousOn
    · exact (designProfileEvenDyad12.differentiable).differentiableOn
    · intro t ht
      rw [interior_Icc] at ht
      rw [(designProfileEvenDyad12_hasDerivAt t).deriv]
      have ht0 : 0 ≤ t := ht.1.le
      have ht2 : t ^ 2 ≤ 30009 / 100000 := by
        have : t ≤ lamStarEvenDyad12 / 2 := ht.2.le
        rw [hlam] at this
        nlinarith
      have hq := designProfileEvenDyad12_qderiv_nonpos (t ^ 2) (sq_nonneg t) ht2
      have e : (-402449 / 500000) * t ^ 1 + (-142417 / 31250) * t ^ 3 + (-48113253 / 500000) * t ^ 5 + (45473063 / 31250) * t ^ 7 + (-6583527411 / 250000) * t ^ 11
          = 2 * t * ((-402449 / 1000000) * (t ^ 2) ^ 0 + (-142417 / 62500) * (t ^ 2) ^ 1 + (-48113253 / 1000000) * (t ^ 2) ^ 2 + (45473063 / 62500) * (t ^ 2) ^ 3 + (-6583527411 / 500000) * (t ^ 2) ^ 5) := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hq
  have habs : ∀ t : ℝ, designProfileEvenDyad12.eval t = designProfileEvenDyad12.eval |t| := by
    intro t
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, heven]
  have hlam0 : (0 : ℝ) ≤ lamStarEvenDyad12 / 2 := by rw [hlam]; norm_num
  refine ⟨heven, ?_, ?_, hanti⟩
  · intro t ht
    rw [habs]
    have h1 : designProfileEvenDyad12.eval (lamStarEvenDyad12 / 2) ≤ designProfileEvenDyad12.eval |t| :=
      hanti ⟨abs_nonneg t, ht⟩ ⟨hlam0, le_refl _⟩ ht
    have h2 : (1 : ℝ) / 6 ≤ designProfileEvenDyad12.eval (lamStarEvenDyad12 / 2) := by
      rw [designProfileEvenDyad12_eval, hlam]; norm_num
    linarith
  · intro t ht
    rw [habs]
    have h1 : designProfileEvenDyad12.eval |t| ≤ designProfileEvenDyad12.eval 0 :=
      hanti ⟨le_refl _, hlam0⟩ ⟨abs_nonneg t, ht⟩ (abs_nonneg t)
    have h2 : designProfileEvenDyad12.eval 0 = 1 := by rw [designProfileEvenDyad12_eval]; norm_num
    linarith

/-- **the degree-10 REFIT even/odd `q ≤ Q` design profile**, at `λ' = lamStarEvenQ10`:
`p(t) = 1 − 0.305071 t² − 6.14528 t⁴ + 52.901255 t⁶ − 90.80634 t⁸ − 262.238203 t¹⁰`. -/
def designProfileEvenQ10 : ℝ[X] :=
  C 1
    + C (-305071 / 1000000 : ℝ) * X ^ 2
    + C (-19204 / 3125 : ℝ) * X ^ 4
    + C (10580251 / 200000 : ℝ) * X ^ 6
    + C (-4540317 / 50000 : ℝ) * X ^ 8
    + C (-262238203 / 1000000 : ℝ) * X ^ 10

theorem designProfileEvenQ10_eval (t : ℝ) :
    designProfileEvenQ10.eval t = 1 + (-305071 / 1000000) * t ^ 2 + (-19204 / 3125) * t ^ 4 + (10580251 / 200000) * t ^ 6 + (-4540317 / 50000) * t ^ 8 + (-262238203 / 1000000) * t ^ 10 := by
  simp [designProfileEvenQ10]

theorem designProfileEvenQ10_natDegree_le : designProfileEvenQ10.natDegree ≤ 10 := by
  unfold designProfileEvenQ10; compute_degree

theorem designProfileEvenQ10_coeff (k : ℕ) :
    designProfileEvenQ10.coeff k
      = (if k = 0 then (1 : ℝ) else 0) + (if k = 2 then (-305071 / 1000000 : ℝ) else 0) + (if k = 4 then (-19204 / 3125 : ℝ) else 0) + (if k = 6 then (10580251 / 200000 : ℝ) else 0) + (if k = 8 then (-4540317 / 50000 : ℝ) else 0) + (if k = 10 then (-262238203 / 1000000 : ℝ) else 0) := by
  simp [designProfileEvenQ10, coeff_add, Polynomial.coeff_one]

theorem designProfileEvenQ10_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => designProfileEvenQ10.eval s)
      ((-305071 / 500000) * t ^ 1 + (-76816 / 3125) * t ^ 3 + (31740753 / 100000) * t ^ 5 + (-4540317 / 6250) * t ^ 7 + (-262238203 / 100000) * t ^ 9) t := by
  have e : (fun s : ℝ => designProfileEvenQ10.eval s) = fun s : ℝ => 1 + (-305071 / 1000000) * s ^ 2 + (-19204 / 3125) * s ^ 4 + (10580251 / 200000) * s ^ 6 + (-4540317 / 50000) * s ^ 8 + (-262238203 / 1000000) * s ^ 10 := by
    funext s; exact designProfileEvenQ10_eval s
  rw [e]
  have h0 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have h1 := (hasDerivAt_pow 2 t).const_mul ((-305071 / 1000000 : ℝ))
  have h2 := (hasDerivAt_pow 4 t).const_mul ((-19204 / 3125 : ℝ))
  have h3 := (hasDerivAt_pow 6 t).const_mul ((10580251 / 200000 : ℝ))
  have h4 := (hasDerivAt_pow 8 t).const_mul ((-4540317 / 50000 : ℝ))
  have h5 := (hasDerivAt_pow 10 t).const_mul ((-262238203 / 1000000 : ℝ))
  have h := (((((h0.add h1).add h2).add h3).add h4).add h5)
  refine h.congr_deriv ?_
  push_cast; ring

/-- `q'(x) ≤ 0` on `[0, 6373 / 20000]` where `p(t) = q(t²)` (Bernstein certificate, degree 11). -/
theorem designProfileEvenQ10_qderiv_nonpos (x : ℝ) (hx0 : 0 ≤ x) (hxB : x ≤ 6373 / 20000) :
    (-305071 / 1000000) * x ^ 0 + (-38408 / 3125) * x ^ 1 + (31740753 / 200000) * x ^ 2 + (-4540317 / 12500) * x ^ 3 + (-262238203 / 200000) * x ^ 4 ≤ 0 := by
  have hB : 0 ≤ 6373 / 20000 - x := by linarith
  linarith [mul_nonneg (pow_nonneg hx0 0) (pow_nonneg hB 11), mul_nonneg (pow_nonneg hx0 1) (pow_nonneg hB 10), mul_nonneg (pow_nonneg hx0 2) (pow_nonneg hB 9), mul_nonneg (pow_nonneg hx0 3) (pow_nonneg hB 8), mul_nonneg (pow_nonneg hx0 4) (pow_nonneg hB 7), mul_nonneg (pow_nonneg hx0 5) (pow_nonneg hB 6), mul_nonneg (pow_nonneg hx0 6) (pow_nonneg hB 5), mul_nonneg (pow_nonneg hx0 7) (pow_nonneg hB 4), mul_nonneg (pow_nonneg hx0 8) (pow_nonneg hB 3), mul_nonneg (pow_nonneg hx0 9) (pow_nonneg hB 2), mul_nonneg (pow_nonneg hx0 10) (pow_nonneg hB 1), mul_nonneg (pow_nonneg hx0 11) (pow_nonneg hB 0)]

/-- **`designProfileEvenQ10 ∈ ProfileQ` at `lamStarEvenQ10`**: even; `p' = 2t·q'(t²) ≤ 0` on
`[0, λ'/2]`; `p ≤ p(0) = 1`; `p ≥ p(λ'/2) = 0.192727 ≥ 1/6`. -/
theorem profileQ_evenq10 : ParamsQ.ProfileQ designProfileEvenQ10 lamStarEvenQ10 := by
  have heven : ∀ t : ℝ, designProfileEvenQ10.eval (-t) = designProfileEvenQ10.eval t := by
    intro t; rw [designProfileEvenQ10_eval, designProfileEvenQ10_eval]; ring
  have hlam : lamStarEvenQ10 = 11289788821 / 10000000000 := by norm_num [lamStarEvenQ10]
  have hanti : AntitoneOn (fun t : ℝ => designProfileEvenQ10.eval t)
      (Set.Icc 0 (lamStarEvenQ10 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact (designProfileEvenQ10.continuous).continuousOn
    · exact (designProfileEvenQ10.differentiable).differentiableOn
    · intro t ht
      rw [interior_Icc] at ht
      rw [(designProfileEvenQ10_hasDerivAt t).deriv]
      have ht0 : 0 ≤ t := ht.1.le
      have ht2 : t ^ 2 ≤ 6373 / 20000 := by
        have : t ≤ lamStarEvenQ10 / 2 := ht.2.le
        rw [hlam] at this
        nlinarith
      have hq := designProfileEvenQ10_qderiv_nonpos (t ^ 2) (sq_nonneg t) ht2
      have e : (-305071 / 500000) * t ^ 1 + (-76816 / 3125) * t ^ 3 + (31740753 / 100000) * t ^ 5 + (-4540317 / 6250) * t ^ 7 + (-262238203 / 100000) * t ^ 9
          = 2 * t * ((-305071 / 1000000) * (t ^ 2) ^ 0 + (-38408 / 3125) * (t ^ 2) ^ 1 + (31740753 / 200000) * (t ^ 2) ^ 2 + (-4540317 / 12500) * (t ^ 2) ^ 3 + (-262238203 / 200000) * (t ^ 2) ^ 4) := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hq
  have habs : ∀ t : ℝ, designProfileEvenQ10.eval t = designProfileEvenQ10.eval |t| := by
    intro t
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, heven]
  have hlam0 : (0 : ℝ) ≤ lamStarEvenQ10 / 2 := by rw [hlam]; norm_num
  refine ⟨heven, ?_, ?_, hanti⟩
  · intro t ht
    rw [habs]
    have h1 : designProfileEvenQ10.eval (lamStarEvenQ10 / 2) ≤ designProfileEvenQ10.eval |t| :=
      hanti ⟨abs_nonneg t, ht⟩ ⟨hlam0, le_refl _⟩ ht
    have h2 : (1 : ℝ) / 6 ≤ designProfileEvenQ10.eval (lamStarEvenQ10 / 2) := by
      rw [designProfileEvenQ10_eval, hlam]; norm_num
    linarith
  · intro t ht
    rw [habs]
    have h1 : designProfileEvenQ10.eval |t| ≤ designProfileEvenQ10.eval 0 :=
      hanti ⟨le_refl _, hlam0⟩ ⟨abs_nonneg t, ht⟩ (abs_nonneg t)
    have h2 : designProfileEvenQ10.eval 0 = 1 := by rw [designProfileEvenQ10_eval]; norm_num
    linarith

/-- the profile of a family. The four Corollary 3 families share their partner's profile:
even and odd are the SAME variational problem (`C` and `λ*` agree), so they carry the same
design. **The parity branches are the two REFIT profiles** (see just above), matching
`Family.lamStar`'s refit bandwidths. -/
def Family.designProfile : Family → ℝ[X]
  | Family.qle => designProfileQle
  | Family.dyadic => designProfileDyadic
  | Family.evenQle => designProfileEvenQ10
  | Family.oddQle => designProfileEvenQ10
  | Family.evenDyadic => designProfileEvenDyad12
  | Family.oddDyadic => designProfileEvenDyad12
  | Family.evenQleR => designProfileQle
  | Family.oddQleR => designProfileQle
  | Family.evenDyadicR => designProfileDyadic
  | Family.oddDyadicR => designProfileDyadic

/-- `ZetaQ.PconstEven` (`Certificate.lean` §3.0b, where `Family.payoff` needs it) and
`ZetaQ.Payoff.PconstEvenQ` are the same number. This file is the first
that imports both. -/
theorem PconstEvenQ_eq_PconstEven : Payoff.PconstEvenQ = PconstEven := by
  rw [Payoff.PconstEvenQ, PconstEven]

theorem designProfileQle_eval (t : ℝ) :
    designProfileQle.eval t
      = 1 + (-81257 / 125000) * t ^ 2 + (3458583 / 1000000) * t ^ 4
          + (-3669851 / 200000) * t ^ 6 := by
  simp [designProfileQle]

theorem designProfileDyadic_eval (t : ℝ) :
    designProfileDyadic.eval t
      = 1 + (-1014099 / 1000000) * t ^ 2 + (834917 / 100000) * t ^ 4
          + (-16525667 / 500000) * t ^ 6 := by
  simp [designProfileDyadic]

theorem designProfileQle_natDegree_le : designProfileQle.natDegree ≤ 6 := by
  unfold designProfileQle; compute_degree

theorem designProfileDyadic_natDegree_le : designProfileDyadic.natDegree ≤ 6 := by
  unfold designProfileDyadic; compute_degree

/-! ## 2. The profile class at `λ*` -/

/-- **`designProfileQle ∈ ProfileQ` at `λ* = 1.2507321515`.** Core: `t² ≤ 0.3911`. The three
inequalities are the polynomial facts `q(x) := p(√x)`: `q` is decreasing on `[0, ∞)`
(`q′ < 0`: discriminant `47.8 − 143 < 0`), `q(0.3911) = 0.1771 ≥ 1/6`, `q ≤ q(0) = 1`. -/
theorem profileQ_qle : ParamsQ.ProfileQ designProfileQle lamStar := by
  have hcore : ∀ t : ℝ, |t| ≤ lamStar / 2 → t ^ 2 ≤ 3911 / 10000 := by
    intro t ht
    have h1 : |t| ^ 2 ≤ (lamStar / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
    rw [sq_abs] at h1
    unfold lamStar at h1
    norm_num at h1
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t; rw [designProfileQle_eval, designProfileQle_eval]; ring
  · intro t ht
    rw [designProfileQle_eval]
    have hx := hcore t ht
    have h0 : 0 ≤ t ^ 2 := sq_nonneg t
    -- q(x) − q(x₀) = (x₀ − x)·r(x), r(x) = 18.349x² + 3.72x + 2.10 > 0
    have hr : (0 : ℝ) ≤ 81257 / 125000 - 3458583 / 1000000 * (t ^ 2 + 3911 / 10000)
        + 3669851 / 200000 * ((t ^ 2) ^ 2 + t ^ 2 * (3911 / 10000) + (3911 / 10000) ^ 2) := by
      nlinarith [sq_nonneg (t ^ 2)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) hr]
  · intro t ht
    rw [designProfileQle_eval]
    have hx := hcore t ht
    have h0 : 0 ≤ t ^ 2 := sq_nonneg t
    -- q(x) ≤ 1 ⟺ x·(18.349x² − 3.4586x + 0.650) ≥ 0
    have hq : (0 : ℝ) ≤ 81257 / 125000 - 3458583 / 1000000 * t ^ 2
        + 3669851 / 200000 * (t ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (t ^ 2 - 942 / 10000)]
    nlinarith [mul_nonneg h0 hq]
  · intro x hx y hy hxy
    simp only
    rw [designProfileQle_eval, designProfileQle_eval]
    have hx0 : 0 ≤ x := hx.1
    have hy0 : 0 ≤ y := hy.1
    have hXY : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0 hxy 2
    have hX0 : 0 ≤ x ^ 2 := sq_nonneg x
    have hY0 : 0 ≤ y ^ 2 := sq_nonneg y
    -- q(X) − q(Y) = (Y − X)·r(X,Y), r ≥ 13.76 s² − 3.46 s + 0.65 > 0
    have hr : (0 : ℝ) ≤ 81257 / 125000 - 3458583 / 1000000 * (x ^ 2 + y ^ 2)
        + 3669851 / 200000 * ((x ^ 2) ^ 2 + x ^ 2 * y ^ 2 + (y ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2 - 1257 / 10000)]
    nlinarith [mul_nonneg (sub_nonneg.2 hXY) hr]

/-- **`designProfileDyadic ∈ ProfileQ` at `λ*_dyad = 1.1931581210`.** Core: `t² ≤ 0.356`;
`q(0.356) = 0.2064 ≥ 1/6`. -/
theorem profileQ_dyadic : ParamsQ.ProfileQ designProfileDyadic lamStarDyadic := by
  have hcore : ∀ t : ℝ, |t| ≤ lamStarDyadic / 2 → t ^ 2 ≤ 356 / 1000 := by
    intro t ht
    have h1 : |t| ^ 2 ≤ (lamStarDyadic / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
    rw [sq_abs] at h1
    unfold lamStarDyadic at h1
    norm_num at h1
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t; rw [designProfileDyadic_eval, designProfileDyadic_eval]; ring
  · intro t ht
    rw [designProfileDyadic_eval]
    have hx := hcore t ht
    have h0 : 0 ≤ t ^ 2 := sq_nonneg t
    have hr : (0 : ℝ) ≤ 1014099 / 1000000 - 834917 / 100000 * (t ^ 2 + 356 / 1000)
        + 16525667 / 500000 * ((t ^ 2) ^ 2 + t ^ 2 * (356 / 1000) + (356 / 1000) ^ 2) := by
      nlinarith [sq_nonneg (t ^ 2)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) hr]
  · intro t ht
    rw [designProfileDyadic_eval]
    have hx := hcore t ht
    have h0 : 0 ≤ t ^ 2 := sq_nonneg t
    have hq : (0 : ℝ) ≤ 1014099 / 1000000 - 834917 / 100000 * t ^ 2
        + 16525667 / 500000 * (t ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (t ^ 2 - 1263 / 10000)]
    nlinarith [mul_nonneg h0 hq]
  · intro x hx y hy hxy
    simp only
    rw [designProfileDyadic_eval, designProfileDyadic_eval]
    have hx0 : 0 ≤ x := hx.1
    have hy0 : 0 ≤ y := hy.1
    have hXY : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0 hxy 2
    have hX0 : 0 ≤ x ^ 2 := sq_nonneg x
    have hY0 : 0 ≤ y ^ 2 := sq_nonneg y
    have hr : (0 : ℝ) ≤ 1014099 / 1000000 - 834917 / 100000 * (x ^ 2 + y ^ 2)
        + 16525667 / 500000 * ((x ^ 2) ^ 2 + x ^ 2 * y ^ 2 + (y ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2 - 1684 / 10000)]
    nlinarith [mul_nonneg (sub_nonneg.2 hXY) hr]

theorem profileQ_design (F : Family) : ParamsQ.ProfileQ F.designProfile F.lamStar := by
  cases F
  · exact profileQ_qle
  · exact profileQ_dyadic
  · exact profileQ_evenq10
  · exact profileQ_evenq10
  · exact profileQ_evendyad12
  · exact profileQ_evendyad12
  · exact profileQ_qle
  · exact profileQ_qle
  · exact profileQ_dyadic
  · exact profileQ_dyadic

/-! ## 3. The window moments are at least the core integrals of the profile -/

namespace ParamsQ

variable {P : ParamsQ}

/-- `φ = p(u/ℒ)` on the plateau `|u| ≤ L/2 − w` (no `Valid` needed). -/
theorem phiQ_eq_prof_on_plateau (hϱ : Zeta23.TaperProfile P.ϱ) (hl : Zeta23.l P.T ≠ 0)
    (hw : 0 < P.w) (heven : ∀ t, P.prof.eval (-t) = P.prof.eval t) {u : ℝ}
    (hu : |u| ≤ P.LB / 2 - P.w) : P.phiQ u = P.prof.eval (u / P.LL) := by
  rw [P.phiQ_eq_prof_mul hl hw.ne', Zeta23.Taper.phi_eq_one hϱ hw hu, mul_one]
  rcases le_or_gt 0 u with h0 | h0
  · rw [abs_of_nonneg h0]
  · rw [abs_of_neg h0, neg_div, heven]

theorem phiQ_continuous_of (hϱ : Zeta23.TaperProfile P.ϱ) (hl : Zeta23.l P.T ≠ 0)
    (hw : 0 < P.w) (hwL : 2 * P.w ≤ P.LB) : Continuous P.phiQ := by
  have e : P.phiQ = fun u => P.prof.eval (|u| / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u :=
    funext (P.phiQ_eq_prof_mul hl hw.ne')
  rw [e]
  exact ((Zeta23.ProductWindow.contDiff_eval_poly P.prof 0).continuous.comp
    (continuous_abs.div_const _)).mul (Zeta23.Taper.phi_continuous hϱ hw hwL)

theorem phiQ_hasCompactSupport_of (hϱ : Zeta23.TaperProfile P.ϱ) (hl : Zeta23.l P.T ≠ 0)
    (hw : 0 < P.w) : HasCompactSupport P.phiQ := by
  have e : P.phiQ = fun u => P.prof.eval (|u| / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u :=
    funext (P.phiQ_eq_prof_mul hl hw.ne')
  rw [e]
  exact (Zeta23.Taper.phi_hasCompactSupport hϱ hw).mul_left

/-- **`∫ φ^{2m} ≥ ∫_{−c}^{c} p(u/ℒ)^{2m} du`, `c = L/2 − w`**: on the plateau `ϱ₂ = 1` so
`φ = p(u/ℒ)`, and `φ^{2m} ≥ 0` elsewhere. -/
theorem core_integral_le (hϱ : Zeta23.TaperProfile P.ϱ) (hl : Zeta23.l P.T ≠ 0)
    (hw : 0 < P.w) (hwL : 2 * P.w ≤ P.LB) (heven : ∀ t, P.prof.eval (-t) = P.prof.eval t)
    (m : ℕ) (hm : 0 < m) :
    (∫ u in -(P.LB / 2 - P.w)..(P.LB / 2 - P.w), (P.prof.eval (u / P.LL)) ^ (2 * m))
      ≤ ∫ u, P.phiQ u ^ (2 * m) := by
  have hc0 : 0 ≤ P.LB / 2 - P.w := by linarith
  have hcont := phiQ_continuous_of hϱ hl hw hwL
  have hcs := phiQ_hasCompactSupport_of hϱ hl hw
  have hint : Integrable (fun u => P.phiQ u ^ (2 * m)) :=
    (hcont.pow _).integrable_of_hasCompactSupport
      (hcs.comp_left (g := fun x : ℝ => x ^ (2 * m)) (zero_pow (by omega)))
  have hnn : ∀ u, 0 ≤ P.phiQ u ^ (2 * m) := fun u => (even_two_mul m).pow_nonneg _
  calc (∫ u in -(P.LB / 2 - P.w)..(P.LB / 2 - P.w), (P.prof.eval (u / P.LL)) ^ (2 * m))
      = ∫ u in Icc (-(P.LB / 2 - P.w)) (P.LB / 2 - P.w), (P.prof.eval (u / P.LL)) ^ (2 * m) := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
    _ = ∫ u in Icc (-(P.LB / 2 - P.w)) (P.LB / 2 - P.w), P.phiQ u ^ (2 * m) := by
        refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
        rw [phiQ_eq_prof_on_plateau hϱ hl hw heven (abs_le.mpr ⟨by linarith [hu.1], hu.2⟩)]
    _ ≤ ∫ u, P.phiQ u ^ (2 * m) := setIntegral_le_integral hint (ae_of_all _ hnn)

theorem LB_mul_aQ (hl : Zeta23.l P.T ≠ 0) (hLB : P.LB ≠ 0) :
    P.LB * P.aQ = ∫ u, P.phiQ u ^ 2 := by
  unfold aQ Zeta23.Params.a
  rw [P.toParams_L hl, ← mul_assoc, mul_inv_cancel₀ hLB, one_mul]
  rfl

theorem LB_mul_bQ (hl : Zeta23.l P.T ≠ 0) (hLB : P.LB ≠ 0) :
    P.LB * P.bQ = ∫ u, P.phiQ u ^ 4 := by
  unfold bQ Zeta23.Params.b
  rw [P.toParams_L hl, ← mul_assoc, mul_inv_cancel₀ hLB, one_mul]
  rfl

end ParamsQ

/-! ## 4. The core integrals, evaluated -/

/-- the antiderivative of `(1 + d₁x² + d₂x⁴ + d₃x⁶)²`. -/
def sqPrim (d1 d2 d3 x : ℝ) : ℝ :=
  x + 2 * d1 * x ^ 3 / 3 + (d1 ^ 2 + 2 * d2) * x ^ 5 / 5 + (2 * d3 + 2 * d1 * d2) * x ^ 7 / 7
    + (d2 ^ 2 + 2 * d1 * d3) * x ^ 9 / 9 + 2 * d2 * d3 * x ^ 11 / 11 + d3 ^ 2 * x ^ 13 / 13

theorem hasDerivAt_sqPrim (d1 d2 d3 x : ℝ) :
    HasDerivAt (sqPrim d1 d2 d3) ((1 + d1 * x ^ 2 + d2 * x ^ 4 + d3 * x ^ 6) ^ 2) x := by
  unfold sqPrim
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h3 := ((hasDerivAt_pow 3 x).const_mul (2 * d1)).div_const 3
  have h5 := ((hasDerivAt_pow 5 x).const_mul (d1 ^ 2 + 2 * d2)).div_const 5
  have h7 := ((hasDerivAt_pow 7 x).const_mul (2 * d3 + 2 * d1 * d2)).div_const 7
  have h9 := ((hasDerivAt_pow 9 x).const_mul (d2 ^ 2 + 2 * d1 * d3)).div_const 9
  have h11 := ((hasDerivAt_pow 11 x).const_mul (2 * d2 * d3)).div_const 11
  have h13 := ((hasDerivAt_pow 13 x).const_mul (d3 ^ 2)).div_const 13
  have h := (((((h1.add h3).add h5).add h7).add h9).add h11).add h13
  exact h.congr_deriv (by push_cast; ring)

theorem integral_sq_poly (d1 d2 d3 a b : ℝ) :
    ∫ x in a..b, (1 + d1 * x ^ 2 + d2 * x ^ 4 + d3 * x ^ 6) ^ 2
      = sqPrim d1 d2 d3 b - sqPrim d1 d2 d3 a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_sqPrim d1 d2 d3 x)
    ((by fun_prop : Continuous fun x : ℝ => (1 + d1 * x ^ 2 + d2 * x ^ 4 + d3 * x ^ 6) ^ 2)
      |>.intervalIntegrable _ _)

/-- the two moment floors from the core integrals, GENERIC in the coefficients: with
`p(t) = 1 + d₁t² + d₂t⁴ + d₃t⁶`, `w = 1`, `κ ≤ L/(2ℒ) − 1/ℒ`, and the two numeric inputs
`2∫₀^κ p² ≥ (3/4)λ`, `4∫₀^κ p² − 2κ ≥ λ/2` (the second uses `p⁴ ≥ 2p² − 1`). -/
theorem design_moments_of (P : ParamsQ) {d1 d2 d3 κ : ℝ}
    (hprof : ∀ t, P.prof.eval t = 1 + d1 * t ^ 2 + d2 * t ^ 4 + d3 * t ^ 6)
    (hϱ : Zeta23.TaperProfile P.ϱ) (hl : Zeta23.l P.T ≠ 0) (hw : P.w = 1)
    (hLL : 0 < P.LL) (hLB : 2 ≤ P.LB) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ (P.LB / 2 - 1) / P.LL)
    (hnum1 : 3 / 4 * P.lam ≤ sqPrim d1 d2 d3 κ - sqPrim d1 d2 d3 (-κ))
    (hnum2 : P.lam / 2 ≤ 2 * (sqPrim d1 d2 d3 κ - sqPrim d1 d2 d3 (-κ)) - 2 * κ) :
    3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hLB0 : 0 < P.LB := by linarith
  have hw0 : (0 : ℝ) < P.w := by rw [hw]; norm_num
  have hwL : 2 * P.w ≤ P.LB := by rw [hw]; linarith
  have heven : ∀ t, P.prof.eval (-t) = P.prof.eval t := by
    intro t; rw [hprof, hprof]; ring
  set c : ℝ := P.LB / 2 - P.w with hc
  have hcw : c = P.LB / 2 - 1 := by rw [hc, hw]
  have hcLL : κ ≤ c / P.LL := by rw [hcw]; exact hκ
  have hcLL' : -c / P.LL ≤ -κ := by rw [neg_div]; linarith
  have hLBeq : P.LB = P.lam * P.LL := rfl
  have hcont : Continuous fun t : ℝ => P.prof.eval t :=
    (Zeta23.ProductWindow.contDiff_eval_poly P.prof 0).continuous
  have hval : ∫ t in (-κ)..κ, (P.prof.eval t) ^ 2
      = sqPrim d1 d2 d3 κ - sqPrim d1 d2 d3 (-κ) := by
    simp_rw [hprof]; exact integral_sq_poly d1 d2 d3 _ _
  have hsub : ∀ m : ℕ, ∫ u in (-c)..c, (P.prof.eval (u / P.LL)) ^ m
      = P.LL * ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ m := by
    intro m
    have := intervalIntegral.integral_comp_div (f := fun t => (P.prof.eval t) ^ m) (a := -c)
      (b := c) hLL.ne'
    simpa [smul_eq_mul] using this
  have hmono2 : ∫ t in (-κ)..κ, (P.prof.eval t) ^ 2
      ≤ ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ 2 :=
    intervalIntegral.integral_mono_interval hcLL' (by linarith) hcLL
      (ae_of_all _ fun t => sq_nonneg _) ((hcont.pow 2).intervalIntegrable _ _)
  have hmono4 : ∫ t in (-κ)..κ, (P.prof.eval t) ^ 4
      ≤ ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ 4 :=
    intervalIntegral.integral_mono_interval hcLL' (by linarith) hcLL
      (ae_of_all _ fun t => (even_two_mul 2).pow_nonneg _) ((hcont.pow 4).intervalIntegrable _ _)
  have h4 : ∫ t in (-κ)..κ, (2 * (P.prof.eval t) ^ 2 - 1)
      ≤ ∫ t in (-κ)..κ, (P.prof.eval t) ^ 4 := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((((hcont.pow 2).const_mul 2).sub continuous_const).intervalIntegrable _ _)
      ((hcont.pow 4).intervalIntegrable _ _) fun t _ => ?_
    nlinarith [sq_nonneg ((P.prof.eval t) ^ 2 - 1)]
  have h4val : ∫ t in (-κ)..κ, (2 * (P.prof.eval t) ^ 2 - 1)
      = 2 * (sqPrim d1 d2 d3 κ - sqPrim d1 d2 d3 (-κ)) - 2 * κ := by
    rw [intervalIntegral.integral_sub (f := fun t => 2 * (P.prof.eval t) ^ 2) (g := fun _ => (1 : ℝ))
      ((by fun_prop : Continuous fun t : ℝ => 2 * (P.prof.eval t) ^ 2).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hval, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
    ring
  have hcore2 := ParamsQ.core_integral_le hϱ hl hw0 hwL heven 1 one_pos
  have hcore4 := ParamsQ.core_integral_le hϱ hl hw0 hwL heven 2 two_pos
  simp only [mul_one] at hcore2
  rw [show (2 * 2 : ℕ) = 4 by norm_num] at hcore4
  rw [hsub 2] at hcore2
  rw [hsub 4] at hcore4
  have hA := ParamsQ.LB_mul_aQ hl hLB0.ne'
  have hB := ParamsQ.LB_mul_bQ hl hLB0.ne'
  constructor
  · have h1 : P.LL * (3 / 4 * P.lam) ≤ P.LB * P.aQ := by
      rw [hA]
      calc P.LL * (3 / 4 * P.lam) ≤ P.LL * (sqPrim d1 d2 d3 κ - sqPrim d1 d2 d3 (-κ)) :=
            mul_le_mul_of_nonneg_left hnum1 hLL.le
        _ = P.LL * ∫ t in (-κ)..κ, (P.prof.eval t) ^ 2 := by rw [hval]
        _ ≤ P.LL * ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ 2 :=
            mul_le_mul_of_nonneg_left hmono2 hLL.le
        _ ≤ ∫ u, P.phiQ u ^ 2 := hcore2
    have h2 : P.LL * (3 / 4 * P.lam) = 3 / 4 * P.LB := by rw [hLBeq]; ring
    rw [h2] at h1
    exact le_of_mul_le_mul_left (by linarith) hLB0
  · have h1 : P.LL * (P.lam / 2) ≤ P.LB * P.bQ := by
      rw [hB]
      calc P.LL * (P.lam / 2)
          ≤ P.LL * (2 * (sqPrim d1 d2 d3 κ - sqPrim d1 d2 d3 (-κ)) - 2 * κ) :=
            mul_le_mul_of_nonneg_left hnum2 hLL.le
        _ = P.LL * ∫ t in (-κ)..κ, (2 * (P.prof.eval t) ^ 2 - 1) := by rw [h4val]
        _ ≤ P.LL * ∫ t in (-κ)..κ, (P.prof.eval t) ^ 4 := mul_le_mul_of_nonneg_left h4 hLL.le
        _ ≤ P.LL * ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ 4 :=
            mul_le_mul_of_nonneg_left hmono4 hLL.le
        _ ≤ ∫ u, P.phiQ u ^ 4 := hcore4
    have h2 : P.LL * (P.lam / 2) = 1 / 2 * P.LB := by rw [hLBeq]; ring
    rw [h2] at h1
    exact le_of_mul_le_mul_left (by linarith) hLB0

/-! **Corollary 3's moment floors**, moved here with the profiles (see §1). `design_moments_of'`
is `design_moments_of` with the profile abstract: only evenness and the VALUE of
`∫_{−κ}^{κ} p²` are consumed, which is what lets the degree-8 and degree-10 profiles reuse the
degree-6 route. -/

/-- `design_moments_of` with the profile abstract: only evenness and the VALUE of
`∫_{−κ}^{κ} p²` are consumed (the degree-6 `sqPrim` route of `DesignProfile.lean` is
the special case `I2 = sqPrim d1 d2 d3 κ − sqPrim d1 d2 d3 (−κ)`). -/
theorem design_moments_of' (P : ParamsQ) {κ I2 : ℝ}
    (heven : ∀ t, P.prof.eval (-t) = P.prof.eval t)
    (hval : ∫ t in (-κ)..κ, (P.prof.eval t) ^ 2 = I2)
    (hϱ : Zeta23.TaperProfile P.ϱ) (hl : Zeta23.l P.T ≠ 0) (hw : P.w = 1)
    (hLL : 0 < P.LL) (hLB : 2 ≤ P.LB) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ (P.LB / 2 - 1) / P.LL)
    (hnum1 : 3 / 4 * P.lam ≤ I2)
    (hnum2 : P.lam / 2 ≤ 2 * I2 - 2 * κ) :
    3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hLB0 : 0 < P.LB := by linarith
  have hw0 : (0 : ℝ) < P.w := by rw [hw]; norm_num
  have hwL : 2 * P.w ≤ P.LB := by rw [hw]; linarith
  set c : ℝ := P.LB / 2 - P.w with hc
  have hcw : c = P.LB / 2 - 1 := by rw [hc, hw]
  have hcLL : κ ≤ c / P.LL := by rw [hcw]; exact hκ
  have hcLL' : -c / P.LL ≤ -κ := by rw [neg_div]; linarith
  have hLBeq : P.LB = P.lam * P.LL := rfl
  have hcont : Continuous fun t : ℝ => P.prof.eval t :=
    (Zeta23.ProductWindow.contDiff_eval_poly P.prof 0).continuous
  have hsub : ∀ m : ℕ, ∫ u in (-c)..c, (P.prof.eval (u / P.LL)) ^ m
      = P.LL * ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ m := by
    intro m
    have := intervalIntegral.integral_comp_div (f := fun t => (P.prof.eval t) ^ m) (a := -c)
      (b := c) hLL.ne'
    simpa [smul_eq_mul] using this
  have hmono2 : ∫ t in (-κ)..κ, (P.prof.eval t) ^ 2
      ≤ ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ 2 :=
    intervalIntegral.integral_mono_interval hcLL' (by linarith) hcLL
      (ae_of_all _ fun t => sq_nonneg _) ((hcont.pow 2).intervalIntegrable _ _)
  have hmono4 : ∫ t in (-κ)..κ, (P.prof.eval t) ^ 4
      ≤ ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ 4 :=
    intervalIntegral.integral_mono_interval hcLL' (by linarith) hcLL
      (ae_of_all _ fun t => (even_two_mul 2).pow_nonneg _) ((hcont.pow 4).intervalIntegrable _ _)
  have h4 : ∫ t in (-κ)..κ, (2 * (P.prof.eval t) ^ 2 - 1)
      ≤ ∫ t in (-κ)..κ, (P.prof.eval t) ^ 4 := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((((hcont.pow 2).const_mul 2).sub continuous_const).intervalIntegrable _ _)
      ((hcont.pow 4).intervalIntegrable _ _) fun t _ => ?_
    nlinarith [sq_nonneg ((P.prof.eval t) ^ 2 - 1)]
  have h4val : ∫ t in (-κ)..κ, (2 * (P.prof.eval t) ^ 2 - 1)
      = 2 * I2 - 2 * κ := by
    rw [intervalIntegral.integral_sub (f := fun t => 2 * (P.prof.eval t) ^ 2) (g := fun _ => (1 : ℝ))
      ((by fun_prop : Continuous fun t : ℝ => 2 * (P.prof.eval t) ^ 2).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hval, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
    ring
  have hcore2 := ParamsQ.core_integral_le hϱ hl hw0 hwL heven 1 one_pos
  have hcore4 := ParamsQ.core_integral_le hϱ hl hw0 hwL heven 2 two_pos
  simp only [mul_one] at hcore2
  rw [show (2 * 2 : ℕ) = 4 by norm_num] at hcore4
  rw [hsub 2] at hcore2
  rw [hsub 4] at hcore4
  have hA := ParamsQ.LB_mul_aQ hl hLB0.ne'
  have hB := ParamsQ.LB_mul_bQ hl hLB0.ne'
  constructor
  · have h1 : P.LL * (3 / 4 * P.lam) ≤ P.LB * P.aQ := by
      rw [hA]
      calc P.LL * (3 / 4 * P.lam) ≤ P.LL * I2 := mul_le_mul_of_nonneg_left hnum1 hLL.le
        _ = P.LL * ∫ t in (-κ)..κ, (P.prof.eval t) ^ 2 := by rw [hval]
        _ ≤ P.LL * ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ 2 :=
            mul_le_mul_of_nonneg_left hmono2 hLL.le
        _ ≤ ∫ u, P.phiQ u ^ 2 := hcore2
    have h2 : P.LL * (3 / 4 * P.lam) = 3 / 4 * P.LB := by rw [hLBeq]; ring
    rw [h2] at h1
    exact le_of_mul_le_mul_left (by linarith) hLB0
  · have h1 : P.LL * (P.lam / 2) ≤ P.LB * P.bQ := by
      rw [hB]
      calc P.LL * (P.lam / 2)
          ≤ P.LL * (2 * I2 - 2 * κ) := mul_le_mul_of_nonneg_left hnum2 hLL.le
        _ = P.LL * ∫ t in (-κ)..κ, (2 * (P.prof.eval t) ^ 2 - 1) := by rw [h4val]
        _ ≤ P.LL * ∫ t in (-κ)..κ, (P.prof.eval t) ^ 4 := mul_le_mul_of_nonneg_left h4 hLL.le
        _ ≤ P.LL * ∫ t in (-c / P.LL)..(c / P.LL), (P.prof.eval t) ^ 4 :=
            mul_le_mul_of_nonneg_left hmono4 hLL.le
        _ ≤ ∫ u, P.phiQ u ^ 4 := hcore4
    have h2 : P.LL * (P.lam / 2) = 1 / 2 * P.LB := by rw [hLBeq]; ring
    rw [h2] at h1
    exact le_of_mul_le_mul_left (by linarith) hLB0

/-- the antiderivative of `designProfileEvenDyad²`. -/
def sqPrimEvenDyad (x : ℝ) : ℝ :=
  (1) * x ^ 1 + (-102043 / 250000) * x ^ 3 + (3195962964641 / 1250000000000) * x ^ 5 + (-3664375634749 / 109375000000) * x ^ 7 + (36791580680423 / 187500000000) * x ^ 9 + (-762126916831321 / 1375000000000) * x ^ 11 + (1562821185613503 / 812500000000) * x ^ 13 + (-12706211228054957 / 937500000000) * x ^ 15 + (263139837974432001 / 4250000000000) * x ^ 17 + (-18449512872224077 / 118750000000) * x ^ 19 + (2158141074905209 / 13125000000) * x ^ 21

theorem hasDerivAt_sqPrimEvenDyad (x : ℝ) :
    HasDerivAt sqPrimEvenDyad ((1 + (-306129 / 500000) * x ^ 2 + (387781 / 62500) * x ^ 4 + (-28365317 / 250000) * x ^ 6 + (397141241 / 500000) * x ^ 8 + (-46455797 / 25000) * x ^ 10) ^ 2) x := by
  unfold sqPrimEvenDyad
  have g0 := (hasDerivAt_pow 1 x).const_mul ((1 : ℝ))
  have g1 := (hasDerivAt_pow 3 x).const_mul ((-102043 / 250000 : ℝ))
  have g2 := (hasDerivAt_pow 5 x).const_mul ((3195962964641 / 1250000000000 : ℝ))
  have g3 := (hasDerivAt_pow 7 x).const_mul ((-3664375634749 / 109375000000 : ℝ))
  have g4 := (hasDerivAt_pow 9 x).const_mul ((36791580680423 / 187500000000 : ℝ))
  have g5 := (hasDerivAt_pow 11 x).const_mul ((-762126916831321 / 1375000000000 : ℝ))
  have g6 := (hasDerivAt_pow 13 x).const_mul ((1562821185613503 / 812500000000 : ℝ))
  have g7 := (hasDerivAt_pow 15 x).const_mul ((-12706211228054957 / 937500000000 : ℝ))
  have g8 := (hasDerivAt_pow 17 x).const_mul ((263139837974432001 / 4250000000000 : ℝ))
  have g9 := (hasDerivAt_pow 19 x).const_mul ((-18449512872224077 / 118750000000 : ℝ))
  have g10 := (hasDerivAt_pow 21 x).const_mul ((2158141074905209 / 13125000000 : ℝ))
  have h := ((((((((((g0.add g1).add g2).add g3).add g4).add g5).add g6).add g7).add g8).add g9).add g10)
  exact h.congr_deriv (by push_cast; ring)

theorem integral_sq_designProfileEvenDyad (a c : ℝ) :
    ∫ x in a..c, (1 + (-306129 / 500000) * x ^ 2 + (387781 / 62500) * x ^ 4 + (-28365317 / 250000) * x ^ 6 + (397141241 / 500000) * x ^ 8 + (-46455797 / 25000) * x ^ 10) ^ 2 = sqPrimEvenDyad c - sqPrimEvenDyad a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_sqPrimEvenDyad x)
    ((by fun_prop : Continuous fun x : ℝ => (1 + (-306129 / 500000) * x ^ 2 + (387781 / 62500) * x ^ 4 + (-28365317 / 250000) * x ^ 6 + (397141241 / 500000) * x ^ 8 + (-46455797 / 25000) * x ^ 10) ^ 2)
      |>.intervalIntegrable _ _)

/-- **the `Valid` moment floors at the EvenDyad design**: `prof = designProfileEvenDyad`, `λ = lamStarEvenDyad`, `w = 1`, `ℒ ≥ 100`
(`a_core = 0.8543`, `b_core = 0.7711`; the floors are checked at `κ = 2703 / 5000`). -/
theorem design_moments_evendyad (P : ParamsQ) (hprof : P.prof = designProfileEvenDyad)
    (hϱ : Zeta23.TaperProfile P.ϱ) (hlam : P.lam = lamStarEvenDyad) (hw : P.w = 1)
    (hLL : 100 ≤ P.LL) (hl : Zeta23.l P.T ≠ 0) : 3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hLL0 : 0 < P.LL := by linarith
  have hLBeq : P.LB = P.lam * P.LL := rfl
  have hlam' : P.lam = 5507999211 / 5000000000 := by rw [hlam]; norm_num [lamStarEvenDyad]
  refine design_moments_of' P (κ := 2703 / 5000) (I2 := sqPrimEvenDyad (2703 / 5000) - sqPrimEvenDyad (-(2703 / 5000)))
    (fun t => by rw [hprof, designProfileEvenDyad_eval, designProfileEvenDyad_eval]; ring) ?_ hϱ hl hw hLL0 ?_ (by norm_num) ?_ ?_ ?_
  · simp_rw [hprof, designProfileEvenDyad_eval]; exact integral_sq_designProfileEvenDyad _ _
  · rw [hLBeq, hlam']; nlinarith
  · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
  · rw [hlam']; unfold sqPrimEvenDyad; norm_num
  · rw [hlam']; unfold sqPrimEvenDyad; norm_num

/-- the antiderivative of `designProfileEvenQ²`. -/
def sqPrimEvenQ (x : ℝ) : ℝ :=
  (1) * x ^ 1 + (-22333 / 250000) * x ^ 3 + (-5491452133999 / 1250000000000) * x ^ 5 + (25487027801059 / 875000000000) * x ^ 7 + (-58341565928149 / 1125000000000) * x ^ 9 + (-533425161051481 / 2750000000000) * x ^ 11 + (16257616304688121 / 13000000000000) * x ^ 13 + (-117352345297033 / 31250000000) * x ^ 15 + (12277448358561 / 2656250000) * x ^ 17

theorem hasDerivAt_sqPrimEvenQ (x : ℝ) :
    HasDerivAt sqPrimEvenQ ((1 + (-66999 / 500000) * x ^ 2 + (-5495941 / 500000) * x ^ 4 + (100475221 / 1000000) * x ^ 6 + (-3503919 / 12500) * x ^ 8) ^ 2) x := by
  unfold sqPrimEvenQ
  have g0 := (hasDerivAt_pow 1 x).const_mul ((1 : ℝ))
  have g1 := (hasDerivAt_pow 3 x).const_mul ((-22333 / 250000 : ℝ))
  have g2 := (hasDerivAt_pow 5 x).const_mul ((-5491452133999 / 1250000000000 : ℝ))
  have g3 := (hasDerivAt_pow 7 x).const_mul ((25487027801059 / 875000000000 : ℝ))
  have g4 := (hasDerivAt_pow 9 x).const_mul ((-58341565928149 / 1125000000000 : ℝ))
  have g5 := (hasDerivAt_pow 11 x).const_mul ((-533425161051481 / 2750000000000 : ℝ))
  have g6 := (hasDerivAt_pow 13 x).const_mul ((16257616304688121 / 13000000000000 : ℝ))
  have g7 := (hasDerivAt_pow 15 x).const_mul ((-117352345297033 / 31250000000 : ℝ))
  have g8 := (hasDerivAt_pow 17 x).const_mul ((12277448358561 / 2656250000 : ℝ))
  have h := ((((((((g0.add g1).add g2).add g3).add g4).add g5).add g6).add g7).add g8)
  exact h.congr_deriv (by push_cast; ring)

theorem integral_sq_designProfileEvenQ (a c : ℝ) :
    ∫ x in a..c, (1 + (-66999 / 500000) * x ^ 2 + (-5495941 / 500000) * x ^ 4 + (100475221 / 1000000) * x ^ 6 + (-3503919 / 12500) * x ^ 8) ^ 2 = sqPrimEvenQ c - sqPrimEvenQ a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_sqPrimEvenQ x)
    ((by fun_prop : Continuous fun x : ℝ => (1 + (-66999 / 500000) * x ^ 2 + (-5495941 / 500000) * x ^ 4 + (100475221 / 1000000) * x ^ 6 + (-3503919 / 12500) * x ^ 8) ^ 2)
      |>.intervalIntegrable _ _)

/-- **the `Valid` moment floors at the EvenQ design**: `prof = designProfileEvenQ`, `λ = lamStarEvenQ`, `w = 1`, `ℒ ≥ 100`
(`a_core = 0.8409`, `b_core = 0.7571`; the floors are checked at `κ = 5563 / 10000`). -/
theorem design_moments_evenq (P : ParamsQ) (hprof : P.prof = designProfileEvenQ)
    (hϱ : Zeta23.TaperProfile P.ϱ) (hlam : P.lam = lamStarEvenQ) (hw : P.w = 1)
    (hLL : 100 ≤ P.LL) (hl : Zeta23.l P.T ≠ 0) : 3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hLL0 : 0 < P.LL := by linarith
  have hLBeq : P.LB = P.lam * P.LL := rfl
  have hlam' : P.lam = 11329788821 / 10000000000 := by rw [hlam]; norm_num [lamStarEvenQ]
  refine design_moments_of' P (κ := 5563 / 10000) (I2 := sqPrimEvenQ (5563 / 10000) - sqPrimEvenQ (-(5563 / 10000)))
    (fun t => by rw [hprof, designProfileEvenQ_eval, designProfileEvenQ_eval]; ring) ?_ hϱ hl hw hLL0 ?_ (by norm_num) ?_ ?_ ?_
  · simp_rw [hprof, designProfileEvenQ_eval]; exact integral_sq_designProfileEvenQ _ _
  · rw [hLBeq, hlam']; nlinarith
  · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
  · rw [hlam']; unfold sqPrimEvenQ; norm_num
  · rw [hlam']; unfold sqPrimEvenQ; norm_num

/-! **The moment floors at the two REFIT parity profiles.** Same route as
`design_moments_evendyad` / `design_moments_evenq`: an explicit antiderivative of `p²`, the
fundamental theorem of calculus, and `design_moments_of'` at a core `κ` inside `λ'/2`. -/

/-- the antiderivative of `designProfileEvenDyad12²`. -/
def sqPrimEvenDyad12 (x : ℝ) : ℝ :=
  (1) * x ^ 1 + (-402449 / 1500000) * x ^ 3 + (-2116706802399 / 5000000000000) * x ^ 5 + (-1947403295767 / 437500000000) * x ^ 7 + (188995672112647 / 4500000000000) * x ^ 9 + (-13732491962953 / 1375000000000) * x ^ 11 + (-4546281598511343 / 13000000000000) * x ^ 13 + (-2033964638728739 / 7500000000000) * x ^ 15 + (1190167433183049 / 531250000000) * x ^ 17 + (35194991106430887 / 9500000000000) * x ^ 19 + (-99791052240876631 / 2625000000000) * x ^ 21 + (4815870352376484769 / 25000000000000) * x ^ 25

theorem hasDerivAt_sqPrimEvenDyad12 (x : ℝ) :
    HasDerivAt sqPrimEvenDyad12 ((1 + (-402449 / 1000000) * x ^ 2 + (-142417 / 125000) * x ^ 4 + (-16037751 / 1000000) * x ^ 6 + (45473063 / 250000) * x ^ 8 + (-2194509137 / 1000000) * x ^ 12) ^ 2) x := by
  unfold sqPrimEvenDyad12
  have g0 := (hasDerivAt_pow 1 x).const_mul ((1 : ℝ))
  have g1 := (hasDerivAt_pow 3 x).const_mul ((-402449 / 1500000 : ℝ))
  have g2 := (hasDerivAt_pow 5 x).const_mul ((-2116706802399 / 5000000000000 : ℝ))
  have g3 := (hasDerivAt_pow 7 x).const_mul ((-1947403295767 / 437500000000 : ℝ))
  have g4 := (hasDerivAt_pow 9 x).const_mul ((188995672112647 / 4500000000000 : ℝ))
  have g5 := (hasDerivAt_pow 11 x).const_mul ((-13732491962953 / 1375000000000 : ℝ))
  have g6 := (hasDerivAt_pow 13 x).const_mul ((-4546281598511343 / 13000000000000 : ℝ))
  have g7 := (hasDerivAt_pow 15 x).const_mul ((-2033964638728739 / 7500000000000 : ℝ))
  have g8 := (hasDerivAt_pow 17 x).const_mul ((1190167433183049 / 531250000000 : ℝ))
  have g9 := (hasDerivAt_pow 19 x).const_mul ((35194991106430887 / 9500000000000 : ℝ))
  have g10 := (hasDerivAt_pow 21 x).const_mul ((-99791052240876631 / 2625000000000 : ℝ))
  have g11 := (hasDerivAt_pow 25 x).const_mul ((4815870352376484769 / 25000000000000 : ℝ))
  have h := (((((((((((g0.add g1).add g2).add g3).add g4).add g5).add g6).add g7).add g8).add g9).add g10).add g11)
  exact h.congr_deriv (by push_cast; ring)

theorem integral_sq_designProfileEvenDyad12 (a c : ℝ) :
    ∫ x in a..c, (1 + (-402449 / 1000000) * x ^ 2 + (-142417 / 125000) * x ^ 4 + (-16037751 / 1000000) * x ^ 6 + (45473063 / 250000) * x ^ 8 + (-2194509137 / 1000000) * x ^ 12) ^ 2 = sqPrimEvenDyad12 c - sqPrimEvenDyad12 a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_sqPrimEvenDyad12 x)
    ((by fun_prop : Continuous fun x : ℝ => (1 + (-402449 / 1000000) * x ^ 2 + (-142417 / 125000) * x ^ 4 + (-16037751 / 1000000) * x ^ 6 + (45473063 / 250000) * x ^ 8 + (-2194509137 / 1000000) * x ^ 12) ^ 2)
      |>.intervalIntegrable _ _)

set_option maxHeartbeats 0 in
/-- **the `Valid` moment floors at the evendyad12 REFIT design**: `prof = designProfileEvenDyad12`,
`λ = lamStarEvenDyad12`, `w = 1`, `ℒ ≥ 100` (floors checked at `κ = 336 / 625`;
`∫_{-κ}^{κ} p² = 0.940879`). -/
theorem design_moments_evendyad12 (P : ParamsQ) (hprof : P.prof = designProfileEvenDyad12)
    (hϱ : Zeta23.TaperProfile P.ϱ) (hlam : P.lam = lamStarEvenDyad12) (hw : P.w = 1)
    (hLL : 100 ≤ P.LL) (hl : Zeta23.l P.T ≠ 0) : 3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hLL0 : 0 < P.LL := by linarith
  have hLBeq : P.LB = P.lam * P.LL := rfl
  have hlam' : P.lam = 5477999211 / 5000000000 := by rw [hlam]; norm_num [lamStarEvenDyad12]
  refine design_moments_of' P (κ := 336 / 625)
    (I2 := sqPrimEvenDyad12 (336 / 625) - sqPrimEvenDyad12 (-(336 / 625)))
    (fun t => by rw [hprof, designProfileEvenDyad12_eval, designProfileEvenDyad12_eval]; ring) ?_ hϱ hl hw
    hLL0 ?_ (by norm_num) ?_ ?_ ?_
  · simp_rw [hprof, designProfileEvenDyad12_eval]; exact integral_sq_designProfileEvenDyad12 _ _
  · rw [hLBeq, hlam']; nlinarith
  · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
  · rw [hlam']; unfold sqPrimEvenDyad12; norm_num
  · rw [hlam']; unfold sqPrimEvenDyad12; norm_num

/-- the antiderivative of `designProfileEvenQ10²`. -/
def sqPrimEvenQ10 (x : ℝ) : ℝ :=
  (1) * x ^ 1 + (-305071 / 1500000) * x ^ 3 + (-12197491684959 / 5000000000000) * x ^ 5 + (171175005359 / 10937500000) * x ^ 7 + (-5870849708327 / 300000000000) * x ^ 9 + (-27981442318813 / 275000000000) * x ^ 11 + (4074606092380251 / 13000000000000) * x ^ 13 + (-159612108191243 / 375000000000) * x ^ 15 + (-1949966871109393 / 1700000000000) * x ^ 17 + (1190644571130351 / 475000000000) * x ^ 19 + (68768875112669209 / 21000000000000) * x ^ 21

theorem hasDerivAt_sqPrimEvenQ10 (x : ℝ) :
    HasDerivAt sqPrimEvenQ10 ((1 + (-305071 / 1000000) * x ^ 2 + (-19204 / 3125) * x ^ 4 + (10580251 / 200000) * x ^ 6 + (-4540317 / 50000) * x ^ 8 + (-262238203 / 1000000) * x ^ 10) ^ 2) x := by
  unfold sqPrimEvenQ10
  have g0 := (hasDerivAt_pow 1 x).const_mul ((1 : ℝ))
  have g1 := (hasDerivAt_pow 3 x).const_mul ((-305071 / 1500000 : ℝ))
  have g2 := (hasDerivAt_pow 5 x).const_mul ((-12197491684959 / 5000000000000 : ℝ))
  have g3 := (hasDerivAt_pow 7 x).const_mul ((171175005359 / 10937500000 : ℝ))
  have g4 := (hasDerivAt_pow 9 x).const_mul ((-5870849708327 / 300000000000 : ℝ))
  have g5 := (hasDerivAt_pow 11 x).const_mul ((-27981442318813 / 275000000000 : ℝ))
  have g6 := (hasDerivAt_pow 13 x).const_mul ((4074606092380251 / 13000000000000 : ℝ))
  have g7 := (hasDerivAt_pow 15 x).const_mul ((-159612108191243 / 375000000000 : ℝ))
  have g8 := (hasDerivAt_pow 17 x).const_mul ((-1949966871109393 / 1700000000000 : ℝ))
  have g9 := (hasDerivAt_pow 19 x).const_mul ((1190644571130351 / 475000000000 : ℝ))
  have g10 := (hasDerivAt_pow 21 x).const_mul ((68768875112669209 / 21000000000000 : ℝ))
  have h := ((((((((((g0.add g1).add g2).add g3).add g4).add g5).add g6).add g7).add g8).add g9).add g10)
  exact h.congr_deriv (by push_cast; ring)

theorem integral_sq_designProfileEvenQ10 (a c : ℝ) :
    ∫ x in a..c, (1 + (-305071 / 1000000) * x ^ 2 + (-19204 / 3125) * x ^ 4 + (10580251 / 200000) * x ^ 6 + (-4540317 / 50000) * x ^ 8 + (-262238203 / 1000000) * x ^ 10) ^ 2 = sqPrimEvenQ10 c - sqPrimEvenQ10 a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_sqPrimEvenQ10 x)
    ((by fun_prop : Continuous fun x : ℝ => (1 + (-305071 / 1000000) * x ^ 2 + (-19204 / 3125) * x ^ 4 + (10580251 / 200000) * x ^ 6 + (-4540317 / 50000) * x ^ 8 + (-262238203 / 1000000) * x ^ 10) ^ 2)
      |>.intervalIntegrable _ _)

set_option maxHeartbeats 0 in
/-- **the `Valid` moment floors at the evenq10 REFIT design**: `prof = designProfileEvenQ10`,
`λ = lamStarEvenQ10`, `w = 1`, `ℒ ≥ 100` (floors checked at `κ = 5543 / 10000`;
`∫_{-κ}^{κ} p² = 0.949445`). -/
theorem design_moments_evenq10 (P : ParamsQ) (hprof : P.prof = designProfileEvenQ10)
    (hϱ : Zeta23.TaperProfile P.ϱ) (hlam : P.lam = lamStarEvenQ10) (hw : P.w = 1)
    (hLL : 100 ≤ P.LL) (hl : Zeta23.l P.T ≠ 0) : 3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hLL0 : 0 < P.LL := by linarith
  have hLBeq : P.LB = P.lam * P.LL := rfl
  have hlam' : P.lam = 11289788821 / 10000000000 := by rw [hlam]; norm_num [lamStarEvenQ10]
  refine design_moments_of' P (κ := 5543 / 10000)
    (I2 := sqPrimEvenQ10 (5543 / 10000) - sqPrimEvenQ10 (-(5543 / 10000)))
    (fun t => by rw [hprof, designProfileEvenQ10_eval, designProfileEvenQ10_eval]; ring) ?_ hϱ hl hw
    hLL0 ?_ (by norm_num) ?_ ?_ ?_
  · simp_rw [hprof, designProfileEvenQ10_eval]; exact integral_sq_designProfileEvenQ10 _ _
  · rw [hLBeq, hlam']; nlinarith
  · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
  · rw [hlam']; unfold sqPrimEvenQ10; norm_num
  · rw [hlam']; unfold sqPrimEvenQ10; norm_num

/-- **the `Valid` floors at the design of record** (all six families): `prof = designProfile F`,
`ϱ` a taper profile, `λ = λ*`, `w = 1`, `ℒ ≥ 100`. -/
theorem design_moments (F : Family) (P : ParamsQ) (hprof : P.prof = F.designProfile)
    (hϱ : Zeta23.TaperProfile P.ϱ) (hlam : P.lam = F.lamStar) (hw : P.w = 1)
    (hLL : 100 ≤ P.LL) (hl : Zeta23.l P.T ≠ 0) : 3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hLL0 : 0 < P.LL := by linarith
  have hLBeq : P.LB = P.lam * P.LL := rfl
  cases F with
  | qle =>
    have hlam' : P.lam = 1.2507321515 := hlam
    refine design_moments_of P (d1 := -81257 / 125000) (d2 := 3458583 / 1000000)
      (d3 := -3669851 / 200000) (κ := 6153 / 10000)
      (fun t => by rw [hprof]; exact designProfileQle_eval t) hϱ hl hw hLL0 ?_ (by norm_num)
      ?_ ?_ ?_
    · rw [hLBeq, hlam']; nlinarith
    · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
    · rw [hlam']; unfold sqPrim; norm_num
    · rw [hlam']; unfold sqPrim; norm_num
  | dyadic =>
    have hlam' : P.lam = 1.1931581210 := hlam
    refine design_moments_of P (d1 := -1014099 / 1000000) (d2 := 834917 / 100000)
      (d3 := -16525667 / 500000) (κ := 5865 / 10000)
      (fun t => by rw [hprof]; exact designProfileDyadic_eval t) hϱ hl hw hLL0 ?_ (by norm_num)
      ?_ ?_ ?_
    · rw [hLBeq, hlam']; nlinarith
    · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
    · rw [hlam']; unfold sqPrim; norm_num
    · rw [hlam']; unfold sqPrim; norm_num
  | evenQle => exact design_moments_evenq10 P hprof hϱ hlam hw hLL hl
  | oddQle => exact design_moments_evenq10 P hprof hϱ hlam hw hLL hl
  | evenDyadic => exact design_moments_evendyad12 P hprof hϱ hlam hw hLL hl
  | oddDyadic => exact design_moments_evendyad12 P hprof hϱ hlam hw hLL hl
  | evenQleR =>
    have hlam' : P.lam = 1.2507321515 := hlam
    refine design_moments_of P (d1 := -81257 / 125000) (d2 := 3458583 / 1000000)
      (d3 := -3669851 / 200000) (κ := 6153 / 10000)
      (fun t => by rw [hprof]; exact designProfileQle_eval t) hϱ hl hw hLL0 ?_ (by norm_num)
      ?_ ?_ ?_
    · rw [hLBeq, hlam']; nlinarith
    · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
    · rw [hlam']; unfold sqPrim; norm_num
    · rw [hlam']; unfold sqPrim; norm_num
  | oddQleR =>
    have hlam' : P.lam = 1.2507321515 := hlam
    refine design_moments_of P (d1 := -81257 / 125000) (d2 := 3458583 / 1000000)
      (d3 := -3669851 / 200000) (κ := 6153 / 10000)
      (fun t => by rw [hprof]; exact designProfileQle_eval t) hϱ hl hw hLL0 ?_ (by norm_num)
      ?_ ?_ ?_
    · rw [hLBeq, hlam']; nlinarith
    · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
    · rw [hlam']; unfold sqPrim; norm_num
    · rw [hlam']; unfold sqPrim; norm_num
  | evenDyadicR =>
    have hlam' : P.lam = 1.1931581210 := hlam
    refine design_moments_of P (d1 := -1014099 / 1000000) (d2 := 834917 / 100000)
      (d3 := -16525667 / 500000) (κ := 5865 / 10000)
      (fun t => by rw [hprof]; exact designProfileDyadic_eval t) hϱ hl hw hLL0 ?_ (by norm_num)
      ?_ ?_ ?_
    · rw [hLBeq, hlam']; nlinarith
    · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
    · rw [hlam']; unfold sqPrim; norm_num
    · rw [hlam']; unfold sqPrim; norm_num
  | oddDyadicR =>
    have hlam' : P.lam = 1.1931581210 := hlam
    refine design_moments_of P (d1 := -1014099 / 1000000) (d2 := 834917 / 100000)
      (d3 := -16525667 / 500000) (κ := 5865 / 10000)
      (fun t => by rw [hprof]; exact designProfileDyadic_eval t) hϱ hl hw hLL0 ?_ (by norm_num)
      ?_ ?_ ?_
    · rw [hLBeq, hlam']; nlinarith
    · rw [hLBeq, hlam', le_div_iff₀ hLL0]; nlinarith
    · rw [hlam']; unfold sqPrim; norm_num
    · rw [hlam']; unfold sqPrim; norm_num

/-! ## 5. The derivative-bound sums of the design profiles: `gevreyBprod ≤ 40000` -/

theorem Mpoly_le_sum_range {pp : ℝ[X]} {R : ℝ} (hR : 0 ≤ R) {j N : ℕ}
    (hN : (derivative^[j] pp).natDegree ≤ N) :
    ParamsQ.Mpoly pp R j
      ≤ ∑ i ∈ Finset.range (N + 1), |(derivative^[j] pp).coeff i| * R ^ i := by
  unfold ParamsQ.Mpoly
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro i _ _
  exact mul_nonneg (abs_nonneg _) (pow_nonneg hR i)

theorem designProfileQle_coeff (k : ℕ) :
    designProfileQle.coeff k
      = (if k = 0 then (1 : ℝ) else 0) + (if k = 2 then (-81257 / 125000 : ℝ) else 0)
        + (if k = 4 then (3458583 / 1000000 : ℝ) else 0)
        + (if k = 6 then (-3669851 / 200000 : ℝ) else 0) := by
  simp [designProfileQle, coeff_add, coeff_C_mul_X_pow, coeff_C, Polynomial.coeff_one]

theorem designProfileDyadic_coeff (k : ℕ) :
    designProfileDyadic.coeff k
      = (if k = 0 then (1 : ℝ) else 0) + (if k = 2 then (-1014099 / 1000000 : ℝ) else 0)
        + (if k = 4 then (834917 / 100000 : ℝ) else 0)
        + (if k = 6 then (-16525667 / 500000 : ℝ) else 0) := by
  simp [designProfileDyadic, coeff_add, coeff_C_mul_X_pow, coeff_C, Polynomial.coeff_one]

/-- `M_j(designProfileQle, λ*/2) ≤ [3, 15, 102, 591, 2667, 8263, 13212]`. -/
theorem profM_qle_le (P : ParamsQ) (hprof : P.prof = designProfileQle) (hlam : P.lam = lamStar) :
    P.profM 0 ≤ 3 ∧ P.profM 1 ≤ 15 ∧ P.profM 2 ≤ 102 ∧ P.profM 3 ≤ 591 ∧ P.profM 4 ≤ 2667
      ∧ P.profM 5 ≤ 8263 ∧ P.profM 6 ≤ 13212 ∧ ∀ j, 7 ≤ j → P.profM j = 0 := by
  have hR : P.lam / 2 = 1.2507321515 / 2 := by rw [hlam]; rfl
  have hR0 : (0 : ℝ) ≤ P.lam / 2 := by rw [hR]; norm_num
  have hdeg : ∀ j, (derivative^[j] designProfileQle).natDegree ≤ 6 :=
    fun j => (natDegree_iterate_derivative _ j).trans
      (Nat.sub_le_of_le_add (by linarith [designProfileQle_natDegree_le]))
  have hM : ∀ j, P.profM j ≤ ∑ i ∈ Finset.range 7, |(derivative^[j] designProfileQle).coeff i|
      * (P.lam / 2) ^ i := by
    intro j
    unfold ParamsQ.profM
    rw [hprof]
    exact Mpoly_le_sum_range hR0 (hdeg j)
  have hz : ∀ j, 7 ≤ j → P.profM j = 0 := by
    intro j hj
    unfold ParamsQ.profM ParamsQ.Mpoly
    rw [hprof, iterate_derivative_eq_zero (by linarith [designProfileQle_natDegree_le])]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hz⟩ <;>
  · refine le_trans (hM _) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_iterate_derivative,
      designProfileQle_coeff, hR]
    norm_num [Nat.descFactorial]

/-- `M_j(designProfileDyadic, λ*_dyad/2) ≤ [4, 24, 164, 962, 4436, 14197, 23797]`. -/
theorem profM_dyadic_le (P : ParamsQ) (hprof : P.prof = designProfileDyadic)
    (hlam : P.lam = lamStarDyadic) :
    P.profM 0 ≤ 4 ∧ P.profM 1 ≤ 24 ∧ P.profM 2 ≤ 164 ∧ P.profM 3 ≤ 962 ∧ P.profM 4 ≤ 4436
      ∧ P.profM 5 ≤ 14197 ∧ P.profM 6 ≤ 23797 ∧ ∀ j, 7 ≤ j → P.profM j = 0 := by
  have hR : P.lam / 2 = 1.1931581210 / 2 := by rw [hlam]; rfl
  have hR0 : (0 : ℝ) ≤ P.lam / 2 := by rw [hR]; norm_num
  have hdeg : ∀ j, (derivative^[j] designProfileDyadic).natDegree ≤ 6 :=
    fun j => (natDegree_iterate_derivative _ j).trans
      (Nat.sub_le_of_le_add (by linarith [designProfileDyadic_natDegree_le]))
  have hM : ∀ j, P.profM j ≤ ∑ i ∈ Finset.range 7, |(derivative^[j] designProfileDyadic).coeff i|
      * (P.lam / 2) ^ i := by
    intro j
    unfold ParamsQ.profM
    rw [hprof]
    exact Mpoly_le_sum_range hR0 (hdeg j)
  have hz : ∀ j, 7 ≤ j → P.profM j = 0 := by
    intro j hj
    unfold ParamsQ.profM ParamsQ.Mpoly
    rw [hprof, iterate_derivative_eq_zero (by linarith [designProfileDyadic_natDegree_le])]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hz⟩ <;>
  · refine le_trans (hM _) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_iterate_derivative,
      designProfileDyadic_coeff, hR]
    norm_num [Nat.descFactorial]

/-- `13 ≤ A = 36/e` and `B = 2e⁸ ≤ 6000`. -/
theorem gevreyA_ge_13 : (13 : ℝ) ≤ gevreyA := by
  unfold gevreyA
  rw [le_div_iff₀ (Real.exp_pos 1)]
  have := Real.exp_one_lt_d9
  linarith

theorem gevreyB_le_6000 : gevreyB ≤ 6000 := by
  unfold gevreyB
  have h := Real.exp_one_lt_d9
  have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h8]
  have : Real.exp 1 ^ 8 ≤ 2.7182818286 ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 8
  nlinarith

/-- the generic arithmetic core of `design_gevreyBprod_le`: seven bounded `M_j`, two ratios
`x₁ ≤ 1/52`, `x₂ ≤ 1/10`, and `B ≤ 6000` give `B·ΣM_j x₁^j + ½ΣM_j x₂^j ≤ 40000` whenever the
rounded sums do. -/
theorem gevreyBprod_arith {B x1 x2 M0 M1 M2 M3 M4 M5 M6 : ℝ}
    (hB0 : 0 ≤ B) (hB : B ≤ 6000) (hx1_0 : 0 ≤ x1) (hx1 : x1 ≤ 1 / 52) (hx2_0 : 0 ≤ x2)
    (hx2 : x2 ≤ 1 / 10) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hM4 : 0 ≤ M4) (hM5 : 0 ≤ M5) (hM6 : 0 ≤ M6)
    (hS : 6000 * (M0 + M1 / 52 + M2 / 52 ^ 2 + M3 / 52 ^ 3 + M4 / 52 ^ 4 + M5 / 52 ^ 5
        + M6 / 52 ^ 6)
      + (M0 + M1 / 10 + M2 / 10 ^ 2 + M3 / 10 ^ 3 + M4 / 10 ^ 4 + M5 / 10 ^ 5 + M6 / 10 ^ 6) / 2
        ≤ 40000) :
    B * (M0 * x1 ^ 0 + M1 * x1 ^ 1 + M2 * x1 ^ 2 + M3 * x1 ^ 3 + M4 * x1 ^ 4 + M5 * x1 ^ 5
          + M6 * x1 ^ 6)
      + (M0 * x2 ^ 0 + M1 * x2 ^ 1 + M2 * x2 ^ 2 + M3 * x2 ^ 3 + M4 * x2 ^ 4 + M5 * x2 ^ 5
          + M6 * x2 ^ 6) / 2 ≤ 40000 := by
  have hp1 : ∀ n : ℕ, x1 ^ n ≤ (1 / 52) ^ n := fun n => pow_le_pow_left₀ hx1_0 hx1 n
  have hp2 : ∀ n : ℕ, x2 ^ n ≤ (1 / 10) ^ n := fun n => pow_le_pow_left₀ hx2_0 hx2 n
  have hS1 : M0 * x1 ^ 0 + M1 * x1 ^ 1 + M2 * x1 ^ 2 + M3 * x1 ^ 3 + M4 * x1 ^ 4 + M5 * x1 ^ 5
      + M6 * x1 ^ 6 ≤ M0 + M1 / 52 + M2 / 52 ^ 2 + M3 / 52 ^ 3 + M4 / 52 ^ 4 + M5 / 52 ^ 5
        + M6 / 52 ^ 6 := by
    have := mul_le_mul_of_nonneg_left (hp1 1) hM1
    have := mul_le_mul_of_nonneg_left (hp1 2) hM2
    have := mul_le_mul_of_nonneg_left (hp1 3) hM3
    have := mul_le_mul_of_nonneg_left (hp1 4) hM4
    have := mul_le_mul_of_nonneg_left (hp1 5) hM5
    have := mul_le_mul_of_nonneg_left (hp1 6) hM6
    norm_num at *
    linarith
  have hS2 : M0 * x2 ^ 0 + M1 * x2 ^ 1 + M2 * x2 ^ 2 + M3 * x2 ^ 3 + M4 * x2 ^ 4 + M5 * x2 ^ 5
      + M6 * x2 ^ 6 ≤ M0 + M1 / 10 + M2 / 10 ^ 2 + M3 / 10 ^ 3 + M4 / 10 ^ 4 + M5 / 10 ^ 5
        + M6 / 10 ^ 6 := by
    have := mul_le_mul_of_nonneg_left (hp2 1) hM1
    have := mul_le_mul_of_nonneg_left (hp2 2) hM2
    have := mul_le_mul_of_nonneg_left (hp2 3) hM3
    have := mul_le_mul_of_nonneg_left (hp2 4) hM4
    have := mul_le_mul_of_nonneg_left (hp2 5) hM5
    have := mul_le_mul_of_nonneg_left (hp2 6) hM6
    norm_num at *
    linarith
  have hS1nn : 0 ≤ M0 * x1 ^ 0 + M1 * x1 ^ 1 + M2 * x1 ^ 2 + M3 * x1 ^ 3 + M4 * x1 ^ 4
      + M5 * x1 ^ 5 + M6 * x1 ^ 6 := by positivity
  nlinarith [mul_le_mul hB hS1 hS1nn (by norm_num)]

/-! **The degree-generic arithmetic core and the two REFIT parity `M_j` ledgers.**

`gevreyBprod_arith` above is the `N = 7` case with the seven sums written out; the parity
profiles need `N = 13` / `N = 11`, and the proof uses nothing about the length. -/

set_option maxHeartbeats 0 in
/-- `M_j(designProfileEvenDyad12, λ'/2) ≤ [4.735, 62.582, 1029.000, …]`
(exact values `4.7343, 62.5818, 1028.3939, …`). -/
theorem profM_evenDyad12_le (P : ParamsQ) (hprof : P.prof = designProfileEvenDyad12)
    (hlam : P.lam = lamStarEvenDyad12) :
    P.profM 0 ≤ 947 / 200 ∧ P.profM 1 ≤ 31291 / 500 ∧ P.profM 2 ≤ 1029 ∧ P.profM 3 ≤ 16215 ∧
     P.profM 4 ≤ 240690 ∧ P.profM 5 ≤ 3294691 ∧ P.profM 6 ≤ 40564363 ∧ P.profM 7 ≤ 436136086 ∧
     P.profM 8 ≤ 3951461682 ∧ P.profM 9 ≤ 28799768925 ∧ P.profM 10 ≤ 157720553518 ∧
     P.profM 11 ≤ 575832698920 ∧ P.profM 12 ≤ 1051173387838 ∧
      ∀ j, 13 ≤ j → P.profM j = 0 := by
  have hR : P.lam / 2 = 1.0955998422 / 2 := by rw [hlam]; rfl
  have hR0 : (0 : ℝ) ≤ P.lam / 2 := by rw [hR]; norm_num
  have hdeg : ∀ j, (derivative^[j] designProfileEvenDyad12).natDegree ≤ 12 :=
    fun j => (natDegree_iterate_derivative _ j).trans
      (Nat.sub_le_of_le_add (by linarith [designProfileEvenDyad12_natDegree_le]))
  have hM : ∀ j, P.profM j ≤ ∑ i ∈ Finset.range 13,
      |(derivative^[j] designProfileEvenDyad12).coeff i| * (P.lam / 2) ^ i := by
    intro j
    unfold ParamsQ.profM
    rw [hprof]
    exact Mpoly_le_sum_range hR0 (hdeg j)
  have hz : ∀ j, 13 ≤ j → P.profM j = 0 := by
    intro j hj
    unfold ParamsQ.profM ParamsQ.Mpoly
    rw [hprof, iterate_derivative_eq_zero (by linarith [designProfileEvenDyad12_natDegree_le])]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hz⟩ <;>
  · refine le_trans (hM _) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_iterate_derivative,
      designProfileEvenDyad12_coeff, hR]
    norm_num [Nat.descFactorial]

set_option maxHeartbeats 0 in
/-- `M_j(designProfileEvenQ10, λ'/2) ≤ [5.231, 51.488, 594.000, …]`
(exact values `5.2305, 51.4879, 593.1028, …`). -/
theorem profM_evenQ10_le (P : ParamsQ) (hprof : P.prof = designProfileEvenQ10)
    (hlam : P.lam = lamStarEvenQ10) :
    P.profM 0 ≤ 5231 / 1000 ∧ P.profM 1 ≤ 6436 / 125 ∧ P.profM 2 ≤ 594 ∧ P.profM 3 ≤ 6423 ∧
     P.profM 4 ≤ 64469 ∧ P.profM 5 ≤ 585788 ∧ P.profM 6 ≤ 4647400 ∧ P.profM 7 ≤ 30595027 ∧
     P.profM 8 ≤ 155275779 ∧ P.profM 9 ≤ 537173792 ∧ P.profM 10 ≤ 951609992 ∧
      ∀ j, 11 ≤ j → P.profM j = 0 := by
  have hR : P.lam / 2 = 1.1289788821 / 2 := by rw [hlam]; rfl
  have hR0 : (0 : ℝ) ≤ P.lam / 2 := by rw [hR]; norm_num
  have hdeg : ∀ j, (derivative^[j] designProfileEvenQ10).natDegree ≤ 10 :=
    fun j => (natDegree_iterate_derivative _ j).trans
      (Nat.sub_le_of_le_add (by linarith [designProfileEvenQ10_natDegree_le]))
  have hM : ∀ j, P.profM j ≤ ∑ i ∈ Finset.range 11,
      |(derivative^[j] designProfileEvenQ10).coeff i| * (P.lam / 2) ^ i := by
    intro j
    unfold ParamsQ.profM
    rw [hprof]
    exact Mpoly_le_sum_range hR0 (hdeg j)
  have hz : ∀ j, 11 ≤ j → P.profM j = 0 := by
    intro j hj
    unfold ParamsQ.profM ParamsQ.Mpoly
    rw [hprof, iterate_derivative_eq_zero (by linarith [designProfileEvenQ10_natDegree_le])]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hz⟩ <;>
  · refine le_trans (hM _) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_iterate_derivative,
      designProfileEvenQ10_coeff, hR]
    norm_num [Nat.descFactorial]

/-- **degree-generic replacement for `gevreyBprod_arith`.** `B ≤ 6000`, `x₁ ≤ 1/52`,
`x₂ ≤ 1/10`, nonnegative `M_j`: the rounded sums control the real ones at ANY truncation
length `N`. -/
theorem gevreyBprod_arith_gen {B x1 x2 : ℝ} {N : ℕ} {M : ℕ → ℝ}
    (hB : B ≤ 6000) (hx1_0 : 0 ≤ x1) (hx1 : x1 ≤ 1 / 52)
    (hx2_0 : 0 ≤ x2) (hx2 : x2 ≤ 1 / 10) (hM : ∀ j, 0 ≤ M j)
    (hS : 6000 * (∑ j ∈ Finset.range N, M j * (1 / 52 : ℝ) ^ j)
        + (∑ j ∈ Finset.range N, M j * (1 / 10 : ℝ) ^ j) / 2 ≤ 40000) :
    B * (∑ j ∈ Finset.range N, M j * x1 ^ j)
      + (∑ j ∈ Finset.range N, M j * x2 ^ j) / 2 ≤ 40000 := by
  have h1 : ∑ j ∈ Finset.range N, M j * x1 ^ j
      ≤ ∑ j ∈ Finset.range N, M j * (1 / 52 : ℝ) ^ j :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx1_0 hx1 j) (hM j)
  have h2 : ∑ j ∈ Finset.range N, M j * x2 ^ j
      ≤ ∑ j ∈ Finset.range N, M j * (1 / 10 : ℝ) ^ j :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx2_0 hx2 j) (hM j)
  have h0 : 0 ≤ ∑ j ∈ Finset.range N, M j * x1 ^ j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hM j) (pow_nonneg hx1_0 j)
  have hmul : B * (∑ j ∈ Finset.range N, M j * x1 ^ j)
      ≤ 6000 * (∑ j ∈ Finset.range N, M j * (1 / 52 : ℝ) ^ j) :=
    mul_le_mul hB h1 h0 (by norm_num)
  linarith

set_option maxHeartbeats 0 in
/-- **`B′ ≤ 40000` at the degree-12 even/odd dyadic REFIT design** (`A ≥ 13`, `B ≤ 6000`,
`w = 1`, `ℒ ≥ 4`). -/
theorem design_gevreyBprod_evenDyad12 (P : ParamsQ)
    (hprof : P.prof = designProfileEvenDyad12) (hlam : P.lam = lamStarEvenDyad12) (hw : P.w = 1)
    (hLL : 4 ≤ P.LL) :
    P.gevreyBprod gevreyA gevreyB ≤ 40000 := by
  have hA13 := gevreyA_ge_13
  have hB := gevreyB_le_6000
  have hB0 : 0 ≤ gevreyB := by unfold gevreyB; positivity
  have hA0 : 0 < gevreyA := by linarith
  have hLL0 : 0 < P.LL := by linarith
  have hx1 : P.w / (P.LL * gevreyA) ≤ 1 / 52 := by
    rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hx1_0 : 0 ≤ P.w / (P.LL * gevreyA) := by rw [hw]; positivity
  have hlam2 : P.lam ≤ 1.3 := by rw [hlam]; norm_num [lamStarEvenDyad12]
  have hlam0 : 0 ≤ P.lam := by rw [hlam]; norm_num [lamStarEvenDyad12]
  have hx2 : P.lam / gevreyA ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hA0 (by norm_num)]; nlinarith
  have hx2_0 : 0 ≤ P.lam / gevreyA := div_nonneg hlam0 hA0.le
  have hM0 : ∀ j, 0 ≤ P.profM j := fun j => by
    unfold ParamsQ.profM ParamsQ.Mpoly
    exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by linarith) i)
  have hdeg : P.prof.natDegree + 1 ≤ 13 := by
    rw [hprof]; linarith [designProfileEvenDyad12_natDegree_le]
  have hS : ∀ x : ℝ, 0 ≤ x →
      ∑ j ∈ Finset.range (P.prof.natDegree + 1), P.profM j * x ^ j
        ≤ ∑ j ∈ Finset.range 13, P.profM j * x ^ j := fun x hx =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hdeg)
      (fun j _ _ => mul_nonneg (hM0 j) (pow_nonneg hx j))
  have hmain : gevreyB * (∑ j ∈ Finset.range 13, P.profM j * (P.w / (P.LL * gevreyA)) ^ j)
      + (∑ j ∈ Finset.range 13, P.profM j * (P.lam / gevreyA) ^ j) / 2 ≤ 40000 := by
    refine gevreyBprod_arith_gen hB hx1_0 hx1 hx2_0 hx2 hM0 ?_
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ :=
      profM_evenDyad12_le P hprof hlam
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    linarith
  unfold ParamsQ.gevreyBprod
  have hS1 := mul_le_mul_of_nonneg_left (hS _ hx1_0) hB0
  linarith [hS _ hx2_0, hS1, hmain]

set_option maxHeartbeats 0 in
/-- **`B′ ≤ 40000` at the degree-10 even/odd `q ≤ Q` REFIT design** (`A ≥ 13`, `B ≤ 6000`,
`w = 1`, `ℒ ≥ 4`). -/
theorem design_gevreyBprod_evenQ10 (P : ParamsQ)
    (hprof : P.prof = designProfileEvenQ10) (hlam : P.lam = lamStarEvenQ10) (hw : P.w = 1)
    (hLL : 4 ≤ P.LL) :
    P.gevreyBprod gevreyA gevreyB ≤ 40000 := by
  have hA13 := gevreyA_ge_13
  have hB := gevreyB_le_6000
  have hB0 : 0 ≤ gevreyB := by unfold gevreyB; positivity
  have hA0 : 0 < gevreyA := by linarith
  have hLL0 : 0 < P.LL := by linarith
  have hx1 : P.w / (P.LL * gevreyA) ≤ 1 / 52 := by
    rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hx1_0 : 0 ≤ P.w / (P.LL * gevreyA) := by rw [hw]; positivity
  have hlam2 : P.lam ≤ 1.3 := by rw [hlam]; norm_num [lamStarEvenQ10]
  have hlam0 : 0 ≤ P.lam := by rw [hlam]; norm_num [lamStarEvenQ10]
  have hx2 : P.lam / gevreyA ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hA0 (by norm_num)]; nlinarith
  have hx2_0 : 0 ≤ P.lam / gevreyA := div_nonneg hlam0 hA0.le
  have hM0 : ∀ j, 0 ≤ P.profM j := fun j => by
    unfold ParamsQ.profM ParamsQ.Mpoly
    exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by linarith) i)
  have hdeg : P.prof.natDegree + 1 ≤ 11 := by
    rw [hprof]; linarith [designProfileEvenQ10_natDegree_le]
  have hS : ∀ x : ℝ, 0 ≤ x →
      ∑ j ∈ Finset.range (P.prof.natDegree + 1), P.profM j * x ^ j
        ≤ ∑ j ∈ Finset.range 11, P.profM j * x ^ j := fun x hx =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hdeg)
      (fun j _ _ => mul_nonneg (hM0 j) (pow_nonneg hx j))
  have hmain : gevreyB * (∑ j ∈ Finset.range 11, P.profM j * (P.w / (P.LL * gevreyA)) ^ j)
      + (∑ j ∈ Finset.range 11, P.profM j * (P.lam / gevreyA) ^ j) / 2 ≤ 40000 := by
    refine gevreyBprod_arith_gen hB hx1_0 hx1 hx2_0 hx2 hM0 ?_
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := profM_evenQ10_le P hprof hlam
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    linarith
  unfold ParamsQ.gevreyBprod
  have hS1 := mul_le_mul_of_nonneg_left (hS _ hx1_0) hB0
  linarith [hS _ hx2_0, hS1, hmain]

/-- **`B′ ≤ 40000` at the two FULL designs, by the degree-6 route** (split out of
`design_gevreyBprod_le` so that `design_gevreyBprod_le_cor3` can cite it for the four
reflected-sieve families `evenQleR`/`oddQleR`/`evenDyadicR`/`oddDyadicR`, which carry the
full families' profile and bandwidth). The proof is `design_gevreyBprod_le`'s former
`IsFull` branch, verbatim. -/
theorem design_gevreyBprod_le_full (F : Family) (P : ParamsQ)
    (hprof : P.prof = F.designProfile) (hlam : P.lam = F.lamStar) (hw : P.w = 1)
    (hLL : 4 ≤ P.LL) (hF : F = Family.qle ∨ F = Family.dyadic) :
    P.gevreyBprod gevreyA gevreyB ≤ 40000 := by
  have hA13 := gevreyA_ge_13
  have hB := gevreyB_le_6000
  have hB0 : 0 ≤ gevreyB := by unfold gevreyB; positivity
  have hA0 : 0 < gevreyA := by linarith
  have hLL0 : 0 < P.LL := by linarith
  have hx1 : P.w / (P.LL * gevreyA) ≤ 1 / 52 := by
    rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hx1_0 : 0 ≤ P.w / (P.LL * gevreyA) := by rw [hw]; positivity
  have hlam2 : P.lam ≤ 1.3 := by
    rw [hlam]; cases F <;>
      simp [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10, lamStarEvenDyad12] <;> norm_num
  have hlam0 : 0 ≤ P.lam := by
    rw [hlam]; cases F <;>
      simp [Family.lamStar, lamStar, lamStarDyadic, lamStarEvenQ10, lamStarEvenDyad12] <;> norm_num
  have hx2 : P.lam / gevreyA ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hA0 (by norm_num)]; nlinarith
  have hx2_0 : 0 ≤ P.lam / gevreyA := div_nonneg hlam0 hA0.le
  have hdeg : F.designProfile.natDegree + 1 ≤ 7 := by
    cases F
    · show designProfileQle.natDegree + 1 ≤ 7; linarith [designProfileQle_natDegree_le]
    · show designProfileDyadic.natDegree + 1 ≤ 7; linarith [designProfileDyadic_natDegree_le]
    all_goals simp at hF
  have hM0 : ∀ j, 0 ≤ P.profM j := fun j => by
    unfold ParamsQ.profM ParamsQ.Mpoly
    exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by linarith) i)
  have hS : ∀ x : ℝ, 0 ≤ x →
      ∑ j ∈ Finset.range (P.prof.natDegree + 1), P.profM j * x ^ j
        ≤ P.profM 0 * x ^ 0 + P.profM 1 * x ^ 1 + P.profM 2 * x ^ 2 + P.profM 3 * x ^ 3
          + P.profM 4 * x ^ 4 + P.profM 5 * x ^ 5 + P.profM 6 * x ^ 6 := fun x hx => by
    have h7 : ∑ j ∈ Finset.range 7, P.profM j * x ^ j
        = P.profM 0 * x ^ 0 + P.profM 1 * x ^ 1 + P.profM 2 * x ^ 2 + P.profM 3 * x ^ 3
          + P.profM 4 * x ^ 4 + P.profM 5 * x ^ 5 + P.profM 6 * x ^ 6 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← h7]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ?_)
      (fun j _ _ => mul_nonneg (hM0 j) (pow_nonneg hx j))
    rw [hprof]; exact hdeg
  have hS1 := hS _ hx1_0
  have hS2 := hS _ hx2_0
  unfold ParamsQ.gevreyBprod
  have hmain : gevreyB * (P.profM 0 * (P.w / (P.LL * gevreyA)) ^ 0
        + P.profM 1 * (P.w / (P.LL * gevreyA)) ^ 1 + P.profM 2 * (P.w / (P.LL * gevreyA)) ^ 2
        + P.profM 3 * (P.w / (P.LL * gevreyA)) ^ 3 + P.profM 4 * (P.w / (P.LL * gevreyA)) ^ 4
        + P.profM 5 * (P.w / (P.LL * gevreyA)) ^ 5 + P.profM 6 * (P.w / (P.LL * gevreyA)) ^ 6)
      + (P.profM 0 * (P.lam / gevreyA) ^ 0 + P.profM 1 * (P.lam / gevreyA) ^ 1
        + P.profM 2 * (P.lam / gevreyA) ^ 2 + P.profM 3 * (P.lam / gevreyA) ^ 3
        + P.profM 4 * (P.lam / gevreyA) ^ 4 + P.profM 5 * (P.lam / gevreyA) ^ 5
        + P.profM 6 * (P.lam / gevreyA) ^ 6) / 2 ≤ 40000 := by
    cases F with
    | qle =>
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := profM_qle_le P hprof hlam
      refine gevreyBprod_arith hB0 hB hx1_0 hx1 hx2_0 hx2 (hM0 0) (hM0 1) (hM0 2) (hM0 3)
        (hM0 4) (hM0 5) (hM0 6) ?_
      nlinarith [h0, h1, h2, h3, h4, h5, h6]
    | dyadic =>
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := profM_dyadic_le P hprof hlam
      refine gevreyBprod_arith hB0 hB hx1_0 hx1 hx2_0 hx2 (hM0 0) (hM0 1) (hM0 2) (hM0 3)
        (hM0 4) (hM0 5) (hM0 6) ?_
      nlinarith [h0, h1, h2, h3, h4, h5, h6]
    | evenQle => simp at hF
    | oddQle => simp at hF
    | evenDyadic => simp at hF
    | oddDyadic => simp at hF
    | evenQleR => simp at hF
    | oddQleR => simp at hF
    | evenDyadicR => simp at hF
    | oddDyadicR => simp at hF
  have hS1' := mul_le_mul_of_nonneg_left hS1 hB0
  linarith [hS1', hS2, hmain]

/-- **PROVED — Corollary 3's four parity families: `B′ ≤ 40000`.**

This used to be a `sorry`, and the reason was not plumbing: `design_gevreyBprod_le`'s
degree-6 route below truncates `Σ_j M_j x^j` at `j ≤ 6`, which is FALSE for a profile of
degree 8 or 10, and no `M_j` ledger existed at those degrees. The repair is threefold and all
of it is above: `gevreyBprod_arith_gen` (the same arithmetic at ANY truncation length),
`profM_evenDyad12_le` / `profM_evenQ10_le` (the two ledgers, via `Mpoly_le_sum_range` and the
`_coeff` lemmas), and — the substantive part — a REFIT of the two parity designs, since the
original degree-8 / degree-10 profiles at `lamStarEvenQ` / `lamStarEvenDyad` do NOT fit under
`40000`. `Family.designProfile` / `Family.lamStar` now route the four parity constructors at
`designProfileEvenQ10` / `lamStarEvenQ10` and `designProfileEvenDyad12` / `lamStarEvenDyad12`;
the threshold `40000` is unchanged, and so is `Family.payoff`. -/
theorem design_gevreyBprod_le_cor3 (F : Family) (P : ParamsQ)
    (hprof : P.prof = F.designProfile) (hlam : P.lam = F.lamStar) (hw : P.w = 1)
    (hLL : 4 ≤ P.LL) (hF : ¬ (F = Family.qle ∨ F = Family.dyadic)) :
    P.gevreyBprod gevreyA gevreyB ≤ 40000 := by
  cases F with
  | qle => exact absurd (Or.inl rfl) hF
  | dyadic => exact absurd (Or.inr rfl) hF
  | evenQle => exact design_gevreyBprod_evenQ10 P hprof hlam hw hLL
  | oddQle => exact design_gevreyBprod_evenQ10 P hprof hlam hw hLL
  | evenDyadic => exact design_gevreyBprod_evenDyad12 P hprof hlam hw hLL
  | oddDyadic => exact design_gevreyBprod_evenDyad12 P hprof hlam hw hLL
  -- the reflected-sieve families carry the FULL designs
  | evenQleR => exact design_gevreyBprod_le_full Family.qle P hprof hlam hw hLL (Or.inl rfl)
  | oddQleR => exact design_gevreyBprod_le_full Family.qle P hprof hlam hw hLL (Or.inl rfl)
  | evenDyadicR =>
    exact design_gevreyBprod_le_full Family.dyadic P hprof hlam hw hLL (Or.inr rfl)
  | oddDyadicR =>
    exact design_gevreyBprod_le_full Family.dyadic P hprof hlam hw hLL (Or.inr rfl)

/-- **`B′ ≤ 40000` at the design** (`A ≥ 13`, `B ≤ 6000`, `w = 1`, `ℒ ≥ 4`):
`B′ = B·Σ_j M_j (w/(ℒA))^j + ½Σ_j M_j (λ/A)^j`, with `w/(ℒA) ≤ 1/52`, `λ/A ≤ 1/10`.

For `Family.qle` / `Family.dyadic` this is PROVED by the degree-6 route below. For Corollary 3's
four parity families it is delegated to `design_gevreyBprod_le_cor3`, which is PROVED
at the two REFIT designs; see there. **This theorem is sorry-free in all six branches.** -/
theorem design_gevreyBprod_le (F : Family) (P : ParamsQ) (hprof : P.prof = F.designProfile)
    (hlam : P.lam = F.lamStar) (hw : P.w = 1) (hLL : 4 ≤ P.LL) :
    P.gevreyBprod gevreyA gevreyB ≤ 40000 := by
  by_cases hF : F = Family.qle ∨ F = Family.dyadic
  case neg => exact design_gevreyBprod_le_cor3 F P hprof hlam hw hLL hF
  exact design_gevreyBprod_le_full F P hprof hlam hw hLL hF

end ZetaQ

end
