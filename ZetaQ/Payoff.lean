/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Payoff.lean — paper §11: the variational / payoff layer.

Self-contained: it imports `ZetaQ.Defs` only.

Statement source of truth: paper §11, plus the two corollary constants at §1.1 and the
interface at §3 Prop. 3.1.

=============================================================================================
THE DESIGN DECISION, STATED ONCE
=============================================================================================
We do NOT mirror §11's closed-form variational build. The paper's §11 solves an
Euler–Lagrange problem (bulk `cos(√2 t)`, an edge zone from the quartic
`(ρ² + 2)² = (C−1)²(1 − ρ²)` with the reflection collapse `β(ρ)β(−ρ) = 1`, free boundary
`v(b*) = 0`) and reports `P = 2 − min B` to ten digits. None of that is needed to PROVE
Theorem 1, and none of it is transcribed into a theorem statement here.

Why the weaker form suffices: §3 Prop. 3.1 consumes only
`‖Ĝ_fam‖²_F ≤ (κ_C + r₂)𝒩` and reports the constant `2 − κ_C`, where `κ_C = B(v)` for the
profile the construction actually chooses. So Theorem 1 consumes an UPPER bound on `B`, i.e.
**feasibility**. Exhibiting one admissible `v_cert` with `B(v_cert) ≤ 2 − Pcert` gives
`min B ≤ 2 − Pcert`, hence `P ≥ Pcert`. The inequality runs the right way with no minimality
input. The MINIMALITY half of §11 (`min B = 1.278716…`, hence `P = 0.7212835668` exactly) is
what makes the paper's constant SHARP; it is stated below as `PconstEqTwoSubMinB` and is
OUT OF SCOPE — the named `Prop` that records the gap (this file declares no `sorry`;
see the Prop-ification block below).

=============================================================================================
F58 — THE CERTIFICATES THE CONSTRUCTION ACTUALLY USES ARE IN `ZetaQ/PayoffSmooth.lean`
=============================================================================================
The four certificates below (`certQQ`, `certDyad`, `certEvenDyad`, `certEvenQ`) are feasibility
statements about piecewise-polynomial profiles that the CONSTRUCTION never realised: until F58 the
tree's window was [R]'s flat taper. The repaired construction (`ZetaQ/Defs.lean` `ParamsQ.prof`,
`ZetaQ/DesignProfile.lean`) realises `v = p²` with `p` an even degree-6 polynomial on the design
support `[−λ*/2, λ*/2]`, and `ZetaQ/PayoffSmooth.lean` ships the SAME engine's certificates for
THOSE profiles: `certQQsmooth` (`B ≤ 2 − 0.7212`, degree 12, `b = λ*/2` exactly) and
`certDyadSmooth` (`B ≤ 2 − 0.7098`; the paper's `0.7099` is not reached by degree 6 at the fixed
dyadic support), plus the §11 link `ProfileRampLink` (stated). Nothing in this file changed.

=============================================================================================
R-A5 — THE SHIPPED CONSTANT IS WEAKER THAN THE PAPER'S. THIS IS NOT BURIED.
=============================================================================================
Two symbols, deliberately distinct, both present:
  * `ZetaQ.Pconst = 0.7212835668`  (frozen in `ZetaQ/Defs.lean`) — the PAPER's constant,
    the value of §11's variational problem. NOT what the Lean route proves.
  * `ZetaQ.Payoff.Pcert  = 0.7212`  (defined here) — the CERTIFIED lower bound, at the
    profile's digit count. This is what every Lean statement downstream may use.
`Pcert < Pconst` (`Pcert_lt_Pconst`). Any Lean artifact's abstract must say `≥ 0.7212`, never
`= 0.7212835668`. The weakening is deliberate and is recorded at `Pcert_qQ`.

=============================================================================================
CLOSED DEFECT (D25) — `Cert` GAINED `hdeg`, AND `Cert.admissible` IS NOW PROVED
=============================================================================================
`Cert.nonnegCheck` inspects only the coefficients `coeff[i][0 .. deg]`, but `evalPoly` (hence
`toFun`) uses every entry of every block, and the original `Cert` bounded only the NUMBER of
blocks, never a block's LENGTH. A certificate with an over-long block therefore passed
`NonnegOK` and `MassOK` while `toFun` went negative (failing instance in the `Cert.hdeg` and
`Cert.admissible` docstrings). Per RESOLUTIONS D25 the STRUCTURE was repaired, not the
statement: `Cert` now carries `hdeg : ∀ p ∈ coeff, p.length ≤ deg + 1`, which all four shipped
certificates satisfy with equality (`certQQ_degBound`, `certDyad_degBound`,
`certEvenDyad_degBound`, `certEvenQ_degBound` now just read the field off), so NO SHIPPED DATUM
CHANGED. `Cert.admissible` is `admissible_of_degBound c h1 h2 c.hdeg` and is sorry-free.

=============================================================================================
D24 — THE ENGINE IS TO BE VERIFIED PER CERTIFICATE, NOT IN GENERAL
=============================================================================================
`Cert.B0Eq` / `B1Eq` — "the exact-ℚ convolution engine agrees with the real-valued `B`, for
EVERY certificate" — are **OPTIONAL**. Proving them in general needs full semantics for
`padd/pmul/pcomp/pint/p2*`, `convPair` as a parametric interval integral with affine
endpoints, branch-constancy on `pairCells`, and cell-by-cell assembly; that was scoped at
multi-week size and is over-engineering, because only four fixed certificates are ever needed.
D24's replacement is direct evaluation at those four. **§3b is the analytic half of that
replacement, and it is proved sorry-free**: `B0_add_B1_half` and `B1_half` carry `B0 + B1` and
`B1` from the parametric-integral definition of `ψ` down to elementary double integrals over
the quarter plane, after which nothing analytic is left.

**STATUS: D24's replacement route is COMPLETE.** §3c cuts §3b's quarter-plane integrals at the
mesh nodes and does the exact-ℚ arithmetic, generically for a TWO-CELL certificate
(`two_cell_payoff` / `two_cell_payoff'`) — and all four shipped certificates are two-cell,
because `hmesh` forces `1 − b ∈ xs` and their meshes have exactly that one interior node. The
four per-certificate evaluations `B0B1_certQQ`, `B0B1_certDyad`, `B0B1_certEvenDyad`,
`B0B1_certEvenQ` are `sorry`-free, and `payoff_of_cert_num` routes the five feasibility
theorems (`payoff_feasible_qQ`, `_qQ_sharp`, `_dyadic`, `_even_dyadic`, `_even_qQ`) through them.
**None of those five depends on a `sorry` any more.**

`Cert.B0Eq` / `Cert.B1Eq` — the GENERAL, every-certificate engine-correctness statements — are
NOT proved, as D24 says they need not be: they assert that the §3a SYMBOLIC-CONVOLUTION engine is
correct for arbitrary data, which is the multi-week object D24 declined. `payoff_of_cert` (the
generic soundness wrapper) takes them as explicit HYPOTHESES; nothing in the tree discharges them,
and nothing consumes that wrapper.

=============================================================================================
THIS FILE HAS NO `sorry`. WHAT IT DOES NOT PROVE IS CARRIED AS EIGHT NAMED `Prop`s
=============================================================================================
That is the file's policy and the reason `lake build ZetaQ` reports no warning from here. A
`def Foo : Prop := …` is still elaborated and type-checked on every build, it is visibly not a
fact, and it cannot be cited as one — whereas a `sorry`-ed *theorem* of the same statement is
indistinguishable from a proved one at every use site, and `#print axioms` on a consumer reports
`sorryAx` only after the fact. Turning each of the eight into a `Prop` forces every would-be
consumer to name it in its own signature. The eight, each with a docstring recording precisely
why it is out of scope:

  * `Cert.B0Eq`, `Cert.B1Eq`  — general engine correctness; OPTIONAL under D24, replaced for the
    four shipped certificates by §3c's exact-ℚ evaluation. Hypotheses of `payoff_of_cert`.
  * `PconstEqTwoSubMinB`      — §11's MINIMALITY half, `P = 2 − min B`. The feasibility route
    proves only `≥`, which is the direction Theorem 1 consumes.
  * `GateMTUpper`, `GateMTAttained`, `GateSo16` — [MT]'s and [So16]'s own theorems, the λ = 1
    and Sono calibration gates. Mentioned in docstrings only (`ZetaQ/Normalisation.lean` §12);
    no declaration takes them as a hypothesis.
  * `RampCostThetaCubic`, `RampCostAtLeastSecondOrder` — §10.3's ramp cost. NOT consumed by
    Theorem 1; the link the construction actually uses is `ZetaQ/RampLink.lean` /
    `RampLinkSharp.lean`, which is proved.

All eight are out of scope by design, and none is reachable from any theorem this
library proves. `Gates.MTconst_digits` is PROVED (see its section note: `x = 1/√2` gives
`x² = 1/2`, so both Taylor series have rational terms and the twelve digits are exact rational
arithmetic — no order-14 error control needed, which is what had blocked it).

**Independence of the numbers.** §3c is a Gram-block computation; §3a is symbolic convolution.
They are different algorithms and they land on the same eight rationals inside Lean
(`B0B1_certQQ` vs `certQQ_parts`, and likewise for the other three). That is a Lean-internal
cross-check on top of the external ones (the off-line certificate generator, the paper's
high-precision solver, a 24-digit mpmath double integral, and the two flat-profile
calibration gates).

=============================================================================================
RULE 17 — λ ≤ 1 IS A SILENT KILLER HERE. READ THIS BEFORE EDITING ANY STATEMENT.
=============================================================================================
**At λ ≤ 1 the C-penalised zone `1 < |α| ≤ λ` is EMPTY.** Then `supp ψ ⊆ [−λ, λ] ⊆ [−1, 1]`,
`B` collapses to the Montgomery–Taylor functional, and every §11 value collapses to
`0.672500703679412` (`Gates.MTconst`). A hypothesis `lam ≤ 1` smuggled into `Admissible`, into
`Cert`, or into any feasibility statement would COMPILE, would be provable, and would silently
destroy the theorem. Consequently:
  * every statement that needs the gain carries `1 < lam` explicitly, or the literal `5/4`;
  * `Cert.hb_lo : 1/2 < b` is the certificate's OWN data condition delivering `λ = 2b > 1`
    (a property of the data, not a hypothesis on the theorem);
  * `Zeta23.ThmD.cFun_vStar` (`Zeta23/ThmD/Functional.lean:432`) carries `h1 : lam ≤ 1`. It is
    reusable **for the MT gate ONLY**, where λ = 1 holds with EQUALITY. Do not generalise it,
    and do not cite it anywhere else in `ZetaQ`.
`X ≤ T` and `D₀ = √T`: §11 has no `X`, no `T`, no `D₀`. Nothing here can smuggle them.

=============================================================================================
SOLVER TRAPS, recorded so that nobody re-steps on them
=============================================================================================
(1) **The kernel jump at `|α| = 1`.** `W_C` is discontinuous there by `C − 1`. In the Lean
    route this is handled STRUCTURALLY by `Cert.hmesh : (1 − b) ∈ xs`, which forces
    `1 = b + (1 − b)` into the sumset of `v`'s breakpoints, i.e. onto a ψ-cell boundary. The
    trap cannot recur. Do NOT re-import a Nyström discretisation with an averaged
    `(1+C)/2` kernel value on the diagonal `|tᵢ − t_j| = 1`.
(2) **The constrained-window junction.** `v'` jumps by `−(C−1)v(b)` unless one is at the free
    boundary. Irrelevant here: the Lean route never solves an EL equation.
-/
import ZetaQ.Defs

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace ZetaQ.Payoff

/-! ## 1. The §11 objects

`minimize B(v) = ψ(0) + ∫_{|α|≤1}|α|ψ + C∫_{1<|α|≤λ}|α|ψ, ψ = v⋆v, over v ≥ 0, ∫v = 1,
supp ⊆ [−λ/2, λ/2]; P = 2 − min B.` -/

/-- `ψ = v ⋆ v` of paper §11, read as the **AUTOCORRELATION**
`ψ(α) = ∫ v(t) v(t − α) dt`.

Paper §11. Resolution: The paper writes `ψ = v⋆v` at L678 but
writes `ψ(0) = ∫v²` at L700; for non-even `v` the convolution gives `ψ(0) = ∫v(t)v(−t)dt ≠ ∫v²`,
so **the paper's own L700 fixes the reading as the autocorrelation**, i.e.
`∫|α|ψ(α)dα = ∬|t−s|v(t)v(s)`. This matches `scripts/payoff_hp2.py`, `payoff_final2.py`,
`fb.py`, `gate3_so16.py` (all `|t − s|`); `qg_check.py` uses `|t + s|` (true convolution) and
agrees on even `v` — the bridge is `psi_conv_eq_of_even` below.
Depends on: nothing.
Rule 17: no `lam` occurs; vacuously clean. -/
def psi (v : ℝ → ℝ) (α : ℝ) : ℝ := ∫ t, v t * v (t - α)

/-- The C-penalised kernel `W_C(α) = |α|` on `|α| ≤ 1`, `C|α|` on `|α| > 1`.

Paper §11. **DISCONTINUOUS at `|α| = 1` by `C − 1`** — solver trap (1) of.
Depends on: nothing.
Rule 17: the upper cut at `λ` of the paper's `C∫_{1<|α|≤λ}` is left implicit because
`supp ψ ⊆ [−λ, λ]` makes it automatic — this is NOT a bandwidth hypothesis and imposes no
relation between `λ` and 1. -/
def W (C : ℝ) (α : ℝ) : ℝ := if |α| ≤ 1 then |α| else C * |α|

/-- Admissible profiles of paper §11: `v ≥ 0`, `∫v = 1`,
`supp v ⊆ [−λ/2, λ/2]`.

Paper §11. Note what is NOT imposed: the paper's admissible class requires no
evenness, no continuity, no C¹ matching. `integrable` is added because
Mathlib's `∫` is junk-valued off the integrable class — it is a well-definedness condition,
not a restriction the paper omits.
Depends on: nothing.
**Rule 17: `lam` is FREE here and MUST stay free.** The headline runs at `lam = 5/4 > 1`.
Adding `lam ≤ 1` to this structure would empty the C-zone of `B` and silently collapse every
§11 value to `Gates.MTconst`. Callers that need the gain carry `1 < lam` themselves. -/
structure Admissible (lam : ℝ) (v : ℝ → ℝ) : Prop where
  /-- `v ≥ 0`. -/
  nonneg : ∀ t, 0 ≤ v t
  /-- well-definedness of every integral below. -/
  integrable : Integrable v
  /-- `∫v = 1`. Exact, not asymptotic — see -/
  mass : ∫ t, v t = 1
  /-- `supp v ⊆ [−λ/2, λ/2]`. -/
  supp : ∀ t, v t ≠ 0 → |t| ≤ lam / 2

/-- The IN-ZONE kernel integral `∫_{|α| ≤ 1} |α| ψ(α) dα`.

Paper §11. Split out from `B` so that §12.3's subfamily mechanism can talk about the in-zone
coefficient separately from the out-zone one (`Bgen` below) — that separation is exactly what
distinguishes Corollary 3 (in-zone coefficient UNCHANGED) from the 0.3693 trap (in-zone
coefficient doubled).
Depends on: `psi`.
Rule 17: `lam`-free. -/
def K0 (v : ℝ → ℝ) : ℝ := ∫ α in Set.Icc (-1 : ℝ) 1, |α| * psi v α

/-- The OUT-ZONE kernel integral `∫_{1 < |α|} |α| ψ(α) dα`.

Paper §11. The paper's upper cut `|α| ≤ λ` is automatic: `supp ψ ⊆ [−λ, λ]` for
`v` admissible at `lam`.
Depends on: `psi`.
Rule 17: `lam`-free by construction — the `λ`-cut is a CONSEQUENCE of admissibility, never a
hypothesis. At `lam ≤ 1` this integral is 0, which is precisely the collapse Rule 17 forbids
anybody to assume. -/
def K1 (v : ℝ → ℝ) : ℝ := ∫ α in {α : ℝ | 1 < |α|}, |α| * psi v α

/-- `B(v) = ψ(0) + ∫_{|α|≤1}|α|ψ + C∫_{1<|α|≤λ}|α|ψ`.

Paper §11. Written as `ψ(0) + ∫ W_C·ψ`; equal to `Bgen 1 C v` (`B_eq_Bgen`).
Depends on: `psi`, `W`.
Rule 17: no `lam` argument at all — the bandwidth enters only through the admissible class of
the profile `B` is evaluated at. -/
def B (C : ℝ) (v : ℝ → ℝ) : ℝ := psi v 0 + ∫ α, W C α * psi v α

/-- The C-free part `B0(v) = ψ(0) + ∫_{|α|≤1}|α|ψ`.

Paper §11 (the decomposition is the pivot of the exact-rational route: `B` is AFFINE in `C`).
Depends on: `psi`, `K0`.
Rule 17: `lam`-free. -/
def B0 (v : ℝ → ℝ) : ℝ := psi v 0 + K0 v

/-- The C-carried part `B1(v) = ∫_{1<|α|≤λ}|α|ψ`. Nonnegative
(`B1_nonneg`), which is what lets a RATIONAL upper bound for the irrational `C` discharge the
irrationality.

Paper §11. Depends on: `K1`.
Rule 17: `lam`-free; identically 0 at `lam ≤ 1`, which is the collapse Rule 17 forbids. -/
def B1 (v : ℝ → ℝ) : ℝ := K1 v

/-- The two-zone functional with INDEPENDENT in-zone weight `c₁` and out-zone weight `c₂`:
`B_{c₁,c₂}(v) = ψ(0) + c₁∫_{|α|≤1}|α|ψ + c₂∫_{1<|α|}|α|ψ`. §11's `B C` is `B_{1,C}`.

Paper §11 generalised exactly as §12.3 and Corollary 3
use it: Corollary 3 proves `B_{1, 2C}` (in-zone coefficient UNCHANGED by the parity projector,
out-zone constant DOUBLED by sieve positivity), whereas positivity in BOTH zones would give
`B_{2, 2C}` — "the 0.3693 trap" of. Keeping the two weights separate is what
makes that distinction expressible; `ZetaQ.Normalisation` consumes this.
Depends on: `psi`, `K0`, `K1`.
Rule 17: `lam`-free. -/
def Bgen (c₁ c₂ : ℝ) (v : ℝ → ℝ) : ℝ := psi v 0 + c₁ * K0 v + c₂ * K1 v

/-! ### 1a. Integrability toolkit

Everything in §1 that splits an integral needs to know that `α ↦ W_C(α)·ψ(α)` is integrable.
That is not free: `ψ` is a parametric integral. The route is Mathlib's convolution API —
`ψ = v ⋆ v̌` with `v̌ t = v (−t)` (`psi_eq_conv`) — which gives integrability of `ψ`
(`Integrable.integrable_convolution`) and `∫ψ = (∫v)² = 1` (`integral_convolution`) in one go.
The kernel factor is then dominated using `psi_supp'` and `psi_nonneg'`.

`psi_nonneg'` and `psi_supp'` duplicate `psi_nonneg` / `psi_supp` below; they are stated here
only because the frozen statement order puts those two AFTER the theorems that need them. The
public forms are one-liners citing these.
Rule 17: `lam`-free throughout — `psi_supp'` compares `|α|` with `lam`, never `lam`
with `1`. -/

theorem psi_nonneg' {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (α : ℝ) : 0 ≤ psi v α :=
  integral_nonneg fun t => mul_nonneg (hv.nonneg t) (hv.nonneg _)

theorem psi_supp' {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) {α : ℝ} (h : lam < |α|) :
    psi v α = 0 := by
  have hz : ∀ t : ℝ, v t * v (t - α) = 0 := by
    intro t
    by_cases h1 : v t = 0
    · simp [h1]
    by_cases h2 : v (t - α) = 0
    · simp [h2]
    exfalso
    have a1 := hv.supp t h1
    have a2 := hv.supp (t - α) h2
    have hb : |α| ≤ |t| + |t - α| := by
      rcases abs_cases α with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases abs_cases t with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
          rcases abs_cases (t - α) with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
            rw [e1, e2, e3] <;> linarith
    linarith
  simp only [psi, hz, integral_zero]

/-- `ψ = v ⋆ v̌` for `v̌ t = v (−t)`: the autocorrelation IS a convolution, with the reflection
absorbed into the second factor. This is the bridge to Mathlib's `Analysis.Convolution`. -/
theorem psi_eq_conv (v : ℝ → ℝ) :
    psi v = convolution v (fun u => v (-u)) (ContinuousLinearMap.mul ℝ ℝ) := by
  funext α
  simp only [psi, convolution_mul]
  congr 1
  funext t
  rw [neg_sub]

/-- `ψ` is integrable — the convolution of two integrable functions. -/
theorem psi_integrable {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) : Integrable (psi v) := by
  rw [psi_eq_conv]
  exact hv.integrable.integrable_convolution _ hv.integrable.comp_neg

/-- `∫ψ = (∫v)² = 1`. Used only to bound `B1` from above, which is what makes
`feasibleValues` bounded below at NEGATIVE `C` (the `minB_le_of_feasible` obligation). -/
theorem psi_total {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) : ∫ α, psi v α = 1 := by
  rw [psi_eq_conv,
    integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hv.integrable hv.integrable.comp_neg]
  simp only [ContinuousLinearMap.mul_apply']
  rw [integral_neg_eq_self, hv.mass]
  ring

/-- `W_C` is measurable (it is a two-branch step, discontinuous at `|α| = 1`). -/
theorem W_meas (C : ℝ) : Measurable (W C) := by
  unfold W
  refine Measurable.ite ?_ measurable_abs (measurable_const.mul measurable_abs)
  exact measurableSet_le measurable_abs measurable_const

/-- `α ↦ W_C(α)·ψ(α)` is integrable: it is dominated by `K·ψ` with
`K = (1 + |C|)(|lam| + 1)`, because `ψ` VANISHES off `[−lam, lam]` (`psi_supp'`) and is
nonnegative there. -/
theorem Wpsi_integrable {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (C : ℝ) :
    Integrable (fun α => W C α * psi v α) := by
  set K : ℝ := (1 + |C|) * (|lam| + 1) with hK
  have hKpos : 0 ≤ K := by positivity
  refine Integrable.mono' (g := fun α => K * psi v α)
    ((psi_integrable hv).const_mul K)
    (((W_meas C).aestronglyMeasurable).mul (psi_integrable hv).aestronglyMeasurable) ?_
  filter_upwards with α
  by_cases hα : lam < |α|
  · simp [psi_supp' hv hα]
  · rw [not_lt] at hα
    have hp := psi_nonneg' hv α
    have hW : |W C α| ≤ (1 + |C|) * (|lam| + 1) := by
      have h1 : |α| ≤ |lam| + 1 := by linarith [le_abs_self lam]
      unfold W
      split
      · rw [abs_abs]
        nlinarith [abs_nonneg C, abs_nonneg α, abs_nonneg lam]
      · rw [abs_mul, abs_abs]
        nlinarith [abs_nonneg C, abs_nonneg α, abs_nonneg lam]
    calc ‖W C α * psi v α‖ = |W C α| * psi v α := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
      _ ≤ K * psi v α := by nlinarith

/-- `W 1 = |·|`. -/
theorem W_one (α : ℝ) : W 1 α = |α| := by simp [W]

/-- `α ↦ |α|·ψ(α)` is integrable. -/
theorem absPsi_integrable {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) :
    Integrable (fun α => |α| * psi v α) := by
  simpa [W_one] using Wpsi_integrable hv 1

/-- `K1 ≤ 2` for a profile of bandwidth `lam < 2`: on `supp ψ ⊆ [−lam, lam]` the kernel
weight `|α|` is at most `2`, and `∫ψ = 1`.

**Rule 17: `lam < 2` is §2.2's own sieve range, NOT a cap of the forbidden kind, and nothing
here compares `lam` with `1`.** -/
theorem K1_le_two {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (h2 : lam < 2) : K1 v ≤ 2 := by
  have hT : MeasurableSet {α : ℝ | 1 < |α|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hpsi := psi_integrable hv
  have hbound : ∀ α : ℝ, |α| * psi v α ≤ 2 * psi v α := by
    intro α
    by_cases hα : lam < |α|
    · simp [psi_supp' hv hα]
    · rw [not_lt] at hα
      nlinarith [psi_nonneg' hv α]
  calc K1 v ≤ ∫ α in {α : ℝ | 1 < |α|}, 2 * psi v α :=
        setIntegral_mono_on ((absPsi_integrable hv).integrableOn)
          ((hpsi.const_mul 2).integrableOn) hT (fun x _ => hbound x)
    _ ≤ ∫ α, 2 * psi v α := setIntegral_le_integral (hpsi.const_mul 2)
        (Filter.Eventually.of_forall (fun x => by
          have := psi_nonneg' hv x; simp only [Pi.zero_apply]; linarith))
    _ = 2 := by rw [integral_const_mul, psi_total hv]; ring

/-- `B C = Bgen 1 C` — §11's functional is the two-zone functional at in-zone weight 1.

Paper §11. Requires the kernel split at `|α| = 1` and
`supp ψ ⊆ [−λ, λ]` for the `∫ W_C ψ` over all of ℝ to equal `K0 + C·K1`.
Depends on: `Admissible`, `psi`, `W`, `K0`, `K1`.
Rule 17: `1 < lam` is NOT assumed — the identity holds at every `lam`; it is the VALUE that
degenerates at `lam ≤ 1`, not the identity. -/
theorem B_eq_Bgen (C : ℝ) {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) :
    B C v = Bgen 1 C v := by
  have hS : MeasurableSet (Set.Icc (-1 : ℝ) 1) := measurableSet_Icc
  have hsplit := integral_add_compl hS (Wpsi_integrable hv C)
  have h0 : ∫ α in Set.Icc (-1 : ℝ) 1, W C α * psi v α = K0 v := by
    refine setIntegral_congr_fun hS ?_
    intro x hx
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    simp [W, hx1]
  have hcompl : (Set.Icc (-1 : ℝ) 1)ᶜ = {α : ℝ | 1 < |α|} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, not_and_or, not_le]
    rcases abs_cases x with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [e]
    · exact ⟨fun h => by rcases h with h | h <;> linarith, fun h => Or.inr (by linarith)⟩
    · exact ⟨fun h => by rcases h with h | h <;> linarith, fun h => Or.inl (by linarith)⟩
  have h1 : ∫ α in (Set.Icc (-1 : ℝ) 1)ᶜ, W C α * psi v α = C * K1 v := by
    rw [hcompl, K1, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_lt measurable_const continuous_abs.measurable) ?_
    intro x hx
    have hx1 : ¬ (|x| ≤ 1) := not_le.mpr hx
    simp [W, hx1]
    ring
  rw [B, Bgen, ← hsplit, h0, h1]
  ring

/-- `B` is affine in `C`: `B C v = B0 v + C · B1 v`. **The pivot of the exact-rational route.**

Paper §11. Only `C` is irrational in the whole certificate, and this
identity plus `B1_nonneg` reduces the irrationality to a single rational upper bound `Cbar ≥ C`.
Depends on: `B_eq_Bgen`.
Rule 17: no bandwidth hypothesis. -/
theorem B_eq_B0_add_C_mul_B1 (C : ℝ) {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) :
    B C v = B0 v + C * B1 v := by
  rw [B_eq_Bgen C hv, Bgen, B0, B1]
  ring

/-- `ψ ≥ 0` for `v ≥ 0` — the autocorrelation of a nonnegative function.

Paper §11 (implicit). Depends on: `Admissible`.
Rule 17: `lam`-free. -/
theorem psi_nonneg {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (α : ℝ) : 0 ≤ psi v α :=
  psi_nonneg' hv α

/-- `supp ψ ⊆ [−λ, λ]` — the sumset of the support with itself. This is what makes the paper's
upper cut `|α| ≤ λ` in `C∫_{1<|α|≤λ}` redundant.

Paper §11. Depends on: `Admissible`.
Rule 17: this is the ONLY place where `lam` and `1` could be compared, and they deliberately
are not: the statement is `|α| > lam → ψ α = 0`, valid at every `lam`. -/
theorem psi_supp {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) {α : ℝ} (h : lam < |α|) :
    psi v α = 0 := psi_supp' hv h

/-- `B1 ≥ 0` (since `ψ ≥ 0` for nonnegative `v`).

Paper §11.3 ("`B1q ≥ 0` automatically").
Depends on: `psi_nonneg`. Rule 17: no bandwidth hypothesis. -/
theorem B1_nonneg {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) : 0 ≤ B1 v := by
  have hmeas : MeasurableSet {α : ℝ | 1 < |α|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  exact setIntegral_nonneg hmeas fun x _ => mul_nonneg (abs_nonneg x) (psi_nonneg hv x)

/-- `B` is monotone in `C`. **This is what lets a RATIONAL upper bound for `π⁴/18` discharge
the irrationality of `C`** without any transcendental evaluation.

Paper §11. Depends on: `B_eq_B0_add_C_mul_B1`, `B1_nonneg`.
Rule 17: no bandwidth hypothesis. -/
theorem B_mono_C {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) {C C' : ℝ} (h : C ≤ C') :
    B C v ≤ B C' v := by
  rw [B_eq_B0_add_C_mul_B1 C hv, B_eq_B0_add_C_mul_B1 C' hv]
  nlinarith [B1_nonneg hv]

/-- **Convention bridge.** For EVEN `v` the autocorrelation and the
convolution agree, so the `|t − s|` form of `payoff_hp2.py` / `payoff_final2.py` / `fb.py` /
`gate3_so16.py` and the `|t + s|` form of `qg_check.py` define the SAME `B`. The optimum is
even, so no shipped number is affected; the bridge is stated so the discrepancy is visible
rather than silently assumed away.

Paper §11 (L678 vs L700). Depends on: `psi`.
Rule 17: `lam`-free. -/
theorem psi_conv_eq_of_even {v : ℝ → ℝ} (hv : ∀ t, v (-t) = v t) (α : ℝ) :
    psi v α = ∫ t, v t * v (α - t) := by
  simp only [psi]
  congr 1
  funext t
  rw [show t - α = -(α - t) by ring, hv]

/-! ## 2. `min B`, `P = 2 − min B`, and the R-A5 gap

Paper §11: "`P = 2 − min B`" — a DEFINITION of `P`, not a theorem. The Tier
C.4 route reaches `min B` only from ABOVE. Everything in this section that requires the lower
half is flagged. -/

/-- The set of achievable values of `B C` over admissible profiles at bandwidths in `(1, 2)`.

Paper §11; `λ ∈ (0,2)` is §2.2's standing range, and `1 < λ` is the
regime §11's gain lives in.
Depends on: `Admissible`, `B`.
**Rule 17: `1 < lam` is IN the set's definition and must stay.** Dropping it to `0 < lam`
would let the MT minimiser at `λ = 1` into the set and pull `minB` down to the MT value,
turning every §11 statement into the collapse. -/
def feasibleValues (C : ℝ) : Set ℝ :=
  {x : ℝ | ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Admissible lam v ∧ B C v = x}

/-- `min B` at penalty `C`, as an infimum over `λ ∈ (1,2)`.

Paper §11. Depends on: `feasibleValues`.
Rule 17: inherits `1 < lam` from `feasibleValues`. -/
def minB (C : ℝ) : ℝ := sInf (feasibleValues C)

/-- `min B_{c₁,c₂}` — the two-zone version, needed to state the 0.3693 trap (§12.3, Cor. 3
O20) as the negative claim it is.

Paper §11 + §12.3.
Depends on: `Bgen`. Rule 17: `1 < lam` retained. -/
def minBgen (c₁ c₂ : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Admissible lam v ∧ Bgen c₁ c₂ v = x}

/-- Feasibility bounds the minimum from ABOVE — the only direction this route needs,
and the only one it can supply.

Paper §11.1 ("Direction"). Depends on: `minB`, `Admissible`.
Rule 17: `1 < lam` is an explicit hypothesis, as it must be. -/
theorem minB_le_of_feasible (C : ℝ) {lam : ℝ} (h1 : 1 < lam) (h2 : lam < 2) {v : ℝ → ℝ}
    (hv : Admissible lam v) : minB C ≤ B C v := by
  refine csInf_le ⟨min 0 (2 * C), ?_⟩ ⟨lam, v, h1, h2, hv, rfl⟩
  rintro x ⟨l, u, hl1, hl2, hu, rfl⟩
  rw [B_eq_B0_add_C_mul_B1 C hu]
  have hB0 : 0 ≤ B0 u := by
    have hp := psi_nonneg hu 0
    have hK0 : 0 ≤ K0 u := setIntegral_nonneg measurableSet_Icc
      (fun x _ => mul_nonneg (abs_nonneg x) (psi_nonneg hu x))
    simp only [B0]
    linarith
  have hB1 : 0 ≤ B1 u := B1_nonneg hu
  have hB1' : B1 u ≤ 2 := K1_le_two hu hl2
  rcases le_or_gt 0 C with hC | hC
  · have hm : min 0 (2 * C) ≤ 0 := min_le_left _ _
    nlinarith
  · have hm : min 0 (2 * C) ≤ 2 * C := min_le_right _ _
    nlinarith

/-- **R-A5, THE GAP, STATED SO IT CANNOT BE OVERLOOKED.** The paper's constant
`P = 0.7212835668` (`ZetaQ.Pconst`) is `2 − min B` at `C = π⁴/18`. The feasibility
route proves only `min B ≤ 2 − Pcert`; the reverse inequality needs the MINIMALITY half of §11
(the Euler–Lagrange solve, the free-boundary condition, and a certified lower bound on
`min B`), which this route does not supply.

Paper §11 (L689).
Depends on: `minB`, `ZetaQ.Pconst`.
Rule 17: `1 < lam` lives inside `minB`'s `feasibleValues`; nothing here caps the bandwidth.
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: this is §11's MINIMALITY half.  The feasibility route deliberately proves
only `≥`, which is the direction Theorem 1 consumes and the direction the paper's headline
states.  Establishing equality needs the lower bound on `min B` that the chosen route
structurally cannot supply. -/
def PconstEqTwoSubMinB : Prop := ZetaQ.Pconst = 2 - minB (Real.pi ^ 4 / 18)

/-! ## 3. The certificate data structure

An EVEN piecewise-polynomial profile with EXACT RATIONAL data. Everything Lean must check is a
finite `ℚ` computation: per-cell Bernstein-coefficient nonnegativity (`NonnegOK`), the exact
mass identity (`MassOK`), and support by construction of the evaluator. -/

/-- Horner evaluation of `Σⱼ cⱼ uʲ` at a real `u`, from rational coefficients.

Depends on: nothing.
Rule 17: no parameters. -/
def evalPoly (cs : List ℚ) (u : ℝ) : ℝ := cs.foldr (fun a acc => (a : ℝ) + u * acc) 0

/-- `evalPoly [] = 0`. -/
theorem evalPoly_nil (u : ℝ) : evalPoly [] u = 0 := rfl

/-- One Horner step. -/
theorem evalPoly_cons (a : ℚ) (as : List ℚ) (u : ℝ) :
    evalPoly (a :: as) u = (a : ℝ) + u * evalPoly as u := rfl

/-- Horner form as an explicit `Finset` sum, for any index bound past the coefficient list.
This is the bridge from the `List`-recursive evaluator to the binomial algebra of
`Cert.bernsteinCoeff`. -/
theorem evalPoly_eq_sum : ∀ (cs : List ℚ) (m : ℕ), cs.length ≤ m → ∀ u : ℝ,
    evalPoly cs u = ∑ j ∈ Finset.range m, ((cs.getD j 0 : ℚ) : ℝ) * u ^ j := by
  intro cs
  induction cs with
  | nil => intro m _ u; simp [evalPoly_nil]
  | cons a as ih =>
    intro m hm u
    cases m with
    | zero => simp at hm
    | succ m =>
      have hm' : as.length ≤ m := by simpa using hm
      rw [evalPoly_cons, ih m hm' u,
        Finset.sum_range_succ' (fun j => (((a :: as).getD j 0 : ℚ) : ℝ) * u ^ j) m]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ,
        Finset.mul_sum]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring

/-- `C(k,j)/C(n,j) · C(n,k) = C(n−j, k−j)` for `j ≤ k ≤ n` — the subset-of-a-subset identity
(`Nat.choose_mul`) in the divided form `bernsteinCoeff` uses. -/
theorem choose_div_mul (n k j : ℕ) (hjk : j ≤ k) (hkn : k ≤ n) :
    (k.choose j : ℚ) / (n.choose j : ℚ) * (n.choose k : ℚ) = ((n - j).choose (k - j) : ℚ) := by
  have hjn : j ≤ n := hjk.trans hkn
  have hcn : ((n.choose j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hjn).ne'
  have hid : (n.choose k : ℚ) * (k.choose j : ℚ)
      = (n.choose j : ℚ) * ((n - j).choose (k - j) : ℚ) := by
    exact_mod_cast Nat.choose_mul (n := n) hjk
  field_simp
  linear_combination hid

/-- `evalPoly cs` is continuous (it is a polynomial). -/
theorem evalPoly_continuous : ∀ cs : List ℚ, Continuous (evalPoly cs) := by
  intro cs
  induction cs with
  | nil =>
    have : evalPoly [] = fun _ : ℝ => (0 : ℝ) := funext evalPoly_nil
    rw [this]; exact continuous_const
  | cons a as ih =>
    have : evalPoly (a :: as) = fun u : ℝ => (a : ℝ) + u * evalPoly as u :=
      funext (evalPoly_cons a as)
    rw [this]
    exact continuous_const.add (continuous_id.mul ih)

/-! ### 3a. The exact-ℚ symbolic convolution engine

`Cert.B0q` / `Cert.B1q` need `ψ = v ⋆ v` as an EXACT piecewise-rational-polynomial object.
This block is the Lean transcription of the certificate generator §1–§4 (`padd`…`pmul`,
`conv`, `pw_integral`, `payoff_parts`), validated against it: on the certificate's data the
Lean engine returns `ψ(0)`, `K0`, `K1` equal *as rationals* to the Python engine's output
(`certQQ_parts` below), and on the two flat-`v` calibration profiles it reproduces the closed
forms `ψ(α) = (λ − |α|)/λ²` exactly (`flat_gate_one`, `flat_gate_five_quarters`).

Everything here is plain rational arithmetic on `List ℚ`; **the file is inside
`noncomputable section`, so `decide` is unavailable** (`Rat` arithmetic does not reduce in the
kernel — `Rat.normalize` goes through `Nat.gcd`). All evaluation is therefore by `norm_num`,
which is why the engine is written to keep the term count small: per-PAIR α-cells rather than
a global refinement, and only the half-line `α ≥ 0` (ψ is even, so
`B0 = ψ(0) + 2∫₀¹ αψ` and `B1 = 2∫₁^{2b} αψ` — exactly the form the `B0_certQQ` /
`B1_certQQ` docstrings record).

Convention: a polynomial is a `List ℚ` of coefficients in ASCENDING powers, matching
`evalPoly`'s `foldr` Horner order. Trailing zeros are harmless throughout.
Rule 17: pure data. -/

/-- Coefficientwise sum of two ascending-coefficient polynomials. -/
def padd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Scalar multiple `a · p`. -/
def pscal (a : ℚ) (p : List ℚ) : List ℚ := p.map (fun c => a * c)

/-- Difference `p − q`. -/
def psub (p q : List ℚ) : List ℚ := padd p (pscal (-1) q)

/-- Product of two polynomials. -/
def pmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => padd (pscal a q) (0 :: pmul p q)

/-- Horner evaluation at a rational point (the ℚ-valued twin of `evalPoly`). -/
def pevalQ (p : List ℚ) (x : ℚ) : ℚ := p.foldr (fun a acc => a + x * acc) 0

/-- Composition `p ∘ q`, i.e. `t ↦ p (q t)`. Used only with `q` affine, for the Taylor
shifts `p(t − x₀)` and the reflections `p(−t − x₀)`. -/
def pcomp (p q : List ℚ) : List ℚ := p.foldr (fun a acc => padd [a] (pmul q acc)) []

/-- Auxiliary for `pint`: divide the coefficient of `uʲ` by `j + 1`, starting the count at
the given index. -/
def pintAux : ℕ → List ℚ → List ℚ
  | _, [] => []
  | j, a :: as => (a / ((j : ℚ) + 1)) :: pintAux (j + 1) as

/-- Antiderivative with zero constant term. -/
def pint (p : List ℚ) : List ℚ := 0 :: pintAux 0 p

/-- Definite integral `∫_lo^hi p`. -/
def pdefint (p : List ℚ) (lo hi : ℚ) : ℚ := pevalQ (pint p) hi - pevalQ (pint p) lo

/-! A BIVARIATE polynomial `A(t, α)` is a `List (List ℚ)` indexed by the power of `α`, whose
entries are polynomials in `t`: `A = Σⱼ αʲ · A[j](t)`. -/

/-- Sum of bivariate polynomials. -/
def p2add : List (List ℚ) → List (List ℚ) → List (List ℚ)
  | [], B => B
  | A, [] => A
  | a :: A, b :: B => padd a b :: p2add A B

/-- Product of bivariate polynomials. -/
def p2mul : List (List ℚ) → List (List ℚ) → List (List ℚ)
  | [], _ => []
  | a :: A, B => p2add (B.map (fun q => pmul a q)) ([] :: p2mul A B)

/-- `q(t − α)` as a bivariate polynomial (Horner in the bivariate atom `t − α`, whose
representation is `[[0,1],[-1]]`). -/
def p2sub (q : List ℚ) : List (List ℚ) :=
  q.foldr (fun a acc => p2add [[a]] (p2mul [[0, 1], [-1]] acc)) []

/-- Substitute `t := a₀ + a₁·α` into a bivariate polynomial, yielding a polynomial in `α`.
The `a₁ = 0` branch is the same formula specialised (it is the common case, and keeping it
cheap is what makes the certificate's evaluation tractable). -/
def p2evalT (A : List (List ℚ)) (a0 a1 : ℚ) : List ℚ :=
  if a1 = 0 then A.map (fun p => pevalQ p a0)
  else A.foldr (fun p acc => padd (pcomp p [a0, a1]) (0 :: acc)) []

/-- A piece `(lo, hi, p)` of a piecewise polynomial: `p` in the GLOBAL variable, on `[lo, hi)`. -/
abbrev Piece : Type := ℚ × ℚ × List ℚ

/-- The contribution of the piece pair `(F, G)` to `ψ(α) = ∫ f(t) g(t − α) dt`, as a
polynomial in `α`, valid on any α-cell whose midpoint is `am`.

The integrand is supported where `t ∈ [A₀, A₁]` and `t − α ∈ [B₀, B₁]`, i.e.
`max(A₀, B₀+α) ≤ t ≤ min(A₁, B₁+α)`; both bounds are AFFINE in `α` and their branches change
only at `α = A₀ − B₀` and `α = A₁ − B₁`. On a cell free of those two values the branch is
constant, so `ψ` is a polynomial there — that is the whole algorithm
(`payoff_cert_gen.py:conv`). -/
def convPair (F G : Piece) (am : ℚ) : List ℚ :=
  let Lc : ℚ × ℚ := if G.1 + am ≤ F.1 then (F.1, 0) else (G.1, 1)
  let Uc : ℚ × ℚ := if F.2.1 ≤ G.2.1 + am then (F.2.1, 0) else (G.2.1, 1)
  if Uc.1 + Uc.2 * am ≤ Lc.1 + Lc.2 * am then []
  else
    let Q := (p2mul [F.2.2] (p2sub G.2.2)).map pint
    psub (p2evalT Q Uc.1 Uc.2) (p2evalT Q Lc.1 Lc.2)

/-- Insert into a sorted list, dropping duplicates. -/
def sortedIns (x : ℚ) : List ℚ → List ℚ
  | [] => [x]
  | a :: l => if x < a then x :: a :: l else if x = a then a :: l else a :: sortedIns x l

/-- Sort and deduplicate. -/
def sortedNub (l : List ℚ) : List ℚ := l.foldr sortedIns []

/-- Adjacent pairs of a list: the cells cut out by a sorted list of nodes. -/
def pairsAdj : List ℚ → List (ℚ × ℚ)
  | [] => []
  | [_] => []
  | a :: b :: t => (a, b) :: pairsAdj (b :: t)

/-- The α-cells on which the pair `(F, G)` contributes a single polynomial, restricted to
`α ≥ 0`. The branch-change points `A₀ − B₀`, `A₁ − B₁` are cut, AND SO IS `α = 1`: that is
what makes the kernel's jump at `|α| = 1` land on a cell boundary (solver trap (1)).

For the certificate this is where `hmesh` pays off: with `t₀ = 1 − b` a mesh point, `1` is
already one of the branch-change values for the pair `([t₀,b], [−b,−t₀])`, so the forced cut
adds nothing and no polynomial piece is split. -/
def pairCells (F G : Piece) : List (ℚ × ℚ) :=
  let lo := max 0 (F.1 - G.2.1)
  let hi := F.2.1 - G.1
  if hi ≤ lo then []
  else
    pairsAdj (sortedNub (lo :: hi ::
      (List.filter (fun x => decide (lo < x) && decide (x < hi))
        [F.1 - G.1, F.2.1 - G.2.1, 1])))

/-- The pair's contribution to `ψ` on `α ≥ 0`, cell by cell. -/
def pairPsi (F G : Piece) : List Piece :=
  (pairCells F G).map (fun z => (z.1, z.2, convPair F G ((z.1 + z.2) / 2)))

/-- `ψ` on `α ≥ 0` as an UNORDERED list of cell contributions whose SUM is `ψ`: one block per
ordered pair of pieces. (No global refinement is formed; the cells of different pairs overlap
freely, which is harmless because every consumer below is additive.) -/
def allPsi (vps : List Piece) : List Piece :=
  vps.flatMap (fun F => vps.flatMap (fun G => pairPsi F G))

/-- `ψ(0) = ∫ v²`, read off the cell blocks containing `0`. -/
def psiAtZero (ps : List Piece) : ℚ :=
  ps.foldr (fun z acc => (if z.1 ≤ 0 ∧ 0 < z.2.1 then pevalQ z.2.2 0 else 0) + acc) 0

/-- `∫ α·p` over `[lo, hi] ∩ [z.lo, z.hi]` for one cell block (`α ≥ 0`, so the kernel weight
`|α|` is just `α`, whose representation is the prefix `0 :: ·`). -/
def intCell (z : Piece) (lo hi : ℚ) : ℚ :=
  if min z.2.1 hi ≤ max z.1 lo then 0
  else pdefint (0 :: z.2.2) (max z.1 lo) (min z.2.1 hi)

/-- `∫_lo^hi α·ψ(α) dα`, summed over the cell blocks. -/
def sumInt (ps : List Piece) (lo hi : ℚ) : ℚ := ps.foldr (fun z acc => intCell z lo hi + acc) 0

/-- **Engine calibration gate at `λ = 1`** (`payoff_cert_gen.py:gate_flat`).
The flat profile `v ≡ 1` on `[−1/2, 1/2]` has `ψ(α) = 1 − |α|`, so `ψ(0) = 1`,
`2∫₀¹ αψ = 1/3` and the out-zone integral is `0` — i.e. `B = 4/3` for EVERY `C`, hit on the
nose in ℚ. This is the paper's second calibration gate applied to the ENGINE (the flat profile
is not expressible as a `Cert`: it needs `b = 1/2`, which `hb_lo` forbids).

Rule 17: `λ = 1` is this gate's own content and
must never leak — cf. `Gates.gate_flat`. -/
theorem flat_gate_one :
    psiAtZero (allPsi [((-1 : ℚ) / 2, (1 : ℚ) / 2, [1])]) = 1 ∧
      2 * sumInt (allPsi [((-1 : ℚ) / 2, (1 : ℚ) / 2, [1])]) 0 1 = 1 / 3 ∧
      2 * sumInt (allPsi [((-1 : ℚ) / 2, (1 : ℚ) / 2, [1])]) 1 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num (maxSteps := 10000000) [allPsi, pairPsi, pairCells, convPair, psiAtZero, sumInt,
      intCell, p2mul, p2add, p2sub, p2evalT, pcomp, pmul, padd, pscal, psub, pint, pintAux,
      pevalQ, pdefint, sortedNub, sortedIns, pairsAdj, List.replicate]

/-- **Engine calibration gate at `λ = 5/4`** — the certificate's own bandwidth, where the
C-penalised zone is LIVE (`K1 > 0`). For `v ≡ 1/λ` on `[−λ/2, λ/2]` the closed form is
`ψ(α) = (λ − |α|)/λ²`, giving `ψ(0) = 4/5`, `K0 = 28/75`, `K1 = 13/300`; the engine returns
exactly those. This is the gate that exercises the `α = 1` cell split.

**Rule 17: `λ = 5/4 > 1` here; `K1 = 13/300 ≠ 0` is the C-zone being nonempty.** -/
theorem flat_gate_five_quarters :
    psiAtZero (allPsi [((-5 : ℚ) / 8, (5 : ℚ) / 8, [4 / 5])]) = 4 / 5 ∧
      2 * sumInt (allPsi [((-5 : ℚ) / 8, (5 : ℚ) / 8, [4 / 5])]) 0 1 = 28 / 75 ∧
      2 * sumInt (allPsi [((-5 : ℚ) / 8, (5 : ℚ) / 8, [4 / 5])]) 1 (5 / 4) = 13 / 300 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num (maxSteps := 10000000) [allPsi, pairPsi, pairCells, convPair, psiAtZero, sumInt,
      intCell, p2mul, p2add, p2sub, p2evalT, pcomp, pmul, padd, pscal, psub, pint, pintAux,
      pevalQ, pdefint, sortedNub, sortedIns, pairsAdj, List.replicate]

/-! ### 3b. THE D24 PER-CERTIFICATE ROUTE — the analytic bridge, proved

**Status (RESOLUTIONS D24).** `Cert.B0Eq` / `B1Eq` — engine correctness *for every
certificate* — are declared OPTIONAL. What Theorem 1 actually needs is the value of `B0` and
`B1` at four FIXED certificates, and for a specific `psi` with a known mesh those are finite
explicit polynomial integrals. This section is the ANALYTIC HALF of that replacement route,
and it is complete and sorry-free: it carries `B0 + B1` and `B1` all the way down from the
parametric-integral definition of `psi` to **elementary double integrals over the quarter
plane** (`B0_add_B1_half`, `B1_half`). What remains for a specific certificate is bookkeeping
(cutting the quarter plane at the mesh nodes) plus exact ℚ arithmetic — no analysis.

**That remaining step is now done too — see §3c below**, which consumes `B0_add_B1_half` and
`B1_half` and produces exact rationals for `B0` and `B1` of any two-cell certificate. The five
`payoff_feasible_*` theorems go through §3c (via `payoff_of_cert_num`) and no longer touch
`B0Eq`/`B1Eq`.

**The reduction.** With `psi = v ⋆ v̌` the kernel integrals are Gram forms in `v`:
`∫ g(α) psi(α) dα = ∬ g(t − s) v(t) v(s)` (`kernel_psi_eq_double`, the one genuinely analytic
step — Fubini on `ℝ²` plus the shear `(α, s) ↦ (α + s, s)`, which is measure preserving). For
an EVEN `v` and an EVEN `g` the four quadrants collapse onto the first
(`kernel_psi_eq_half`), and the two kernels §11 needs become elementary there:
  * in+out zone: `|s − t| + (s + t) = 2·max(s, t)` — the absolute value disappears;
  * out zone alone: `|s − t| > 1` is impossible for `s, t ∈ (0, b]` with `b < 1` (`hb_hi`), so
    only the corner `s + t > 1` survives — and `s + t > 1` is impossible unless BOTH `s` and
    `t` are in the top cell, because `2(1 − b) < 1` exactly when `b > 1/2` (`hb_lo`).
So the certificate's own two data conditions are precisely what makes the out-zone integral a
single corner triangle on one cell. The `|α| = 1` kernel jump never has to be tracked: it has
been traded for the constraint `s + t > 1` on the quarter plane, whose cut `s = 1 − t` is an
INTERIOR cut of the top cell exactly because `1 − b ∈ xs` (`hmesh`).

**Validated.** Carrying the remaining bookkeeping out in exact ℚ (per-cell moments
`∫_I v`, `∫_I t·v`, `∫_I v²`, the diagonal blocks `2∫_I v(t)(t·F_I(t) − G_I(t))dt`, the
off-diagonal products `2(A_J B_I − A_I B_J)`, and the one corner triangle) reproduces
`B0_certQQ`, `B1_certQQ`, `B0_certDyad`, `B1_certDyad`, `B0_certEvenDyad`, `B1_certEvenDyad`,
`B0_certEvenQ`, `B1_certEvenQ` **exactly, as rationals, for all four shipped certificates**.
That is a FIFTH independent check on the engine's numbers (after the two flat-profile gates,
the `payoff_cert_gen.py` reference and the 24-digit mpmath double integral), obtained by a
completely different algorithm — Gram blocks rather than symbolic convolution.

Rule 17: `lam` is free throughout; `half_kernel_out` uses `lam < 2`, which is §2.2's
own sieve range and is delivered by `Cert.hb_hi` — nothing anywhere compares `lam` with 1.

#### The scalar polynomial calculus

`evalPoly` is a `List ℚ` Horner evaluator; §3a's `padd`/`pscal`/`psub`/`pmul`/`pcomp`/`pint`
are its ℚ-level algebra. These are the SCALAR semantics only — nothing here touches the
bivariate `p2*`/`convPair`/`pairCells` layer that `B0Eq`/`B1Eq` would need. -/

/-- `evalPoly` is additive: the ℚ-level `padd` really is polynomial addition. -/
theorem evalPoly_padd : ∀ (p q : List ℚ) (u : ℝ),
    evalPoly (padd p q) u = evalPoly p u + evalPoly q u := by
  intro p
  induction p with
  | nil => intro q u; simp [padd, evalPoly_nil]
  | cons a p ih =>
    intro q u
    cases q with
    | nil => simp [padd, evalPoly_nil]
    | cons b q =>
      simp only [padd, evalPoly_cons, ih q u]
      push_cast
      ring

/-- `pscal` really is scalar multiplication. -/
theorem evalPoly_pscal : ∀ (a : ℚ) (p : List ℚ) (u : ℝ),
    evalPoly (pscal a p) u = (a : ℝ) * evalPoly p u := by
  intro a p
  induction p with
  | nil => intro u; simp [pscal, evalPoly_nil]
  | cons b p ih =>
    intro u
    simp only [pscal, List.map_cons, evalPoly_cons] at *
    rw [ih u]
    push_cast
    ring

/-- `psub` really is polynomial subtraction. -/
theorem evalPoly_psub (p q : List ℚ) (u : ℝ) :
    evalPoly (psub p q) u = evalPoly p u - evalPoly q u := by
  simp only [psub, evalPoly_padd, evalPoly_pscal]
  push_cast
  ring

/-- `pmul` really is polynomial multiplication. -/
theorem evalPoly_pmul : ∀ (p q : List ℚ) (u : ℝ),
    evalPoly (pmul p q) u = evalPoly p u * evalPoly q u := by
  intro p
  induction p with
  | nil => intro q u; simp [pmul, evalPoly_nil]
  | cons a p ih =>
    intro q u
    simp only [pmul, evalPoly_padd, evalPoly_pscal, evalPoly_cons, ih q u]
    push_cast
    ring

/-- `pcomp p q` really is `p` composed with `q`. Used only with `q` affine. -/
theorem evalPoly_pcomp : ∀ (p q : List ℚ) (u : ℝ),
    evalPoly (pcomp p q) u = evalPoly p (evalPoly q u) := by
  intro p
  induction p with
  | nil => intro q u; simp [pcomp, evalPoly_nil]
  | cons a p ih =>
    intro q u
    simp only [pcomp, List.foldr_cons] at *
    rw [evalPoly_padd, evalPoly_pmul, ih q u, evalPoly_cons, evalPoly_cons, evalPoly_nil]
    ring

/-- `pevalQ` is `evalPoly` at a rational point: the ℚ-valued twin agrees after casting. -/
theorem pevalQ_cast : ∀ (p : List ℚ) (x : ℚ),
    ((pevalQ p x : ℚ) : ℝ) = evalPoly p ((x : ℚ) : ℝ) := by
  intro p
  induction p with
  | nil => intro x; simp [pevalQ, evalPoly_nil]
  | cons a p ih =>
    intro x
    simp only [pevalQ, List.foldr_cons] at *
    rw [evalPoly_cons, ← ih x]
    push_cast
    ring

/-- The induction behind `hasDerivAt_pint`: the derivative of `x^(j+1)·A_j(x)` is `x^j·p(x)`,
where `A_j = evalPoly (pintAux j p)` is the series with coefficients `a_i/(j+i+1)`. -/
theorem hasDerivAt_pintAux : ∀ (p : List ℚ) (j : ℕ) (x : ℝ),
    HasDerivAt (fun y : ℝ => y ^ (j + 1) * evalPoly (pintAux j p) y)
      (x ^ j * evalPoly p x) x := by
  intro p
  induction p with
  | nil =>
    intro j x
    have h : (fun y : ℝ => y ^ (j + 1) * evalPoly (pintAux j []) y) = fun _ : ℝ => (0 : ℝ) := by
      funext y; simp [pintAux, evalPoly_nil]
    rw [h, evalPoly_nil, mul_zero]
    exact hasDerivAt_const _ _
  | cons a p ih =>
    intro j x
    have hfun : (fun y : ℝ => y ^ (j + 1) * evalPoly (pintAux j (a :: p)) y)
        = fun y : ℝ => ((a : ℝ) / ((j : ℝ) + 1)) * y ^ (j + 1)
            + y ^ (j + 1 + 1) * evalPoly (pintAux (j + 1) p) y := by
      funext y
      simp only [pintAux, evalPoly_cons]
      push_cast
      ring
    have h1 : HasDerivAt (fun y : ℝ => ((a : ℝ) / ((j : ℝ) + 1)) * y ^ (j + 1))
        (((a : ℝ) / ((j : ℝ) + 1)) * ((j + 1 : ℕ) * x ^ j)) x :=
      (hasDerivAt_pow (j + 1) x).const_mul _
    have h2 := ih (j + 1) x
    have h3 := h1.add h2
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have heq : ((a : ℝ) / ((j : ℝ) + 1)) * (((j + 1 : ℕ) : ℝ) * x ^ j)
          + x ^ (j + 1) * evalPoly p x
        = x ^ j * evalPoly (a :: p) x := by
      rw [evalPoly_cons]
      push_cast
      field_simp
      ring
    rw [hfun, ← heq]
    exact h3

/-- `pint` really is the antiderivative with zero constant term. -/
theorem hasDerivAt_pint (p : List ℚ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => evalPoly (pint p) y) (evalPoly p x) x := by
  have h := hasDerivAt_pintAux p 0 x
  have hfun : (fun y : ℝ => evalPoly (pint p) y)
      = fun y : ℝ => y ^ (0 + 1) * evalPoly (pintAux 0 p) y := by
    funext y
    simp only [pint, evalPoly_cons, pow_one, zero_add]
    push_cast
    ring
  rw [hfun]
  simpa using h

/-- **The polynomial fundamental theorem of calculus, in engine form.** Every per-cell integral
of the certificate route is one application of this. -/
theorem integral_evalPoly_interval (p : List ℚ) (a b : ℝ) :
    ∫ x in a..b, evalPoly p x = evalPoly (pint p) b - evalPoly (pint p) a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_pint p x)
    ((evalPoly_continuous p).intervalIntegrable _ _)]

/-! #### The Fubini bridge

`∫ g(α) psi(α) dα = ∫ v(t) (∫ g(s − t) v(s) ds) dt`. The shear `(α, s) ↦ (α + s, s)` preserves
`volume.prod volume`, which is what makes the product integrand integrable; the kernel is only
ever evaluated where `v(t)v(s) ≠ 0`, i.e. on `|s − t| ≤ lam`, so a bound there suffices. -/

/-- `psi(α) = ∫ v(s + α) v(s) ds` — the autocorrelation with the shift moved onto the first
factor, by translation invariance of Lebesgue measure. -/
theorem psi_shift {v : ℝ → ℝ} (α : ℝ) : psi v α = ∫ s, v (s + α) * v s := by
  have h := integral_add_right_eq_self (μ := volume) (fun t : ℝ => v t * v (t - α)) α
  simp only [add_sub_cancel_right] at h
  simp only [psi]
  exact h.symm

/-- `(α, s) ↦ v(s + α)·v(s)` is integrable on `ℝ²`: it is `(x, y) ↦ v(x)v(y)` composed with the
measure-preserving shear `(α, s) ↦ (α + s, s)`. -/
theorem integrable_vv {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) :
    Integrable (fun z : ℝ × ℝ => v (z.2 + z.1) * v z.2) (volume.prod volume) := by
  have h0 : Integrable (fun z : ℝ × ℝ => v z.1 * v z.2) (volume.prod volume) :=
    hv.integrable.mul_prod hv.integrable
  have hmp : MeasurePreserving (fun z : ℝ × ℝ => (z.1 + z.2, z.2))
      (volume.prod volume) (volume.prod volume) := measurePreserving_add_prod volume volume
  have h1 := hmp.integrable_comp_of_integrable h0
  have heq : (fun z : ℝ × ℝ => v (z.2 + z.1) * v z.2)
      = (fun z : ℝ × ℝ => v z.1 * v z.2) ∘ (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) := by
    funext z
    simp only [Function.comp_apply]
    rw [add_comm]
  rw [heq]
  exact h1

/-- **THE FUBINI BRIDGE (D24).** A kernel integral against `psi` is the Gram form of `v`:
`∫ g(α) psi(α) dα = ∫ v(t) (∫ g(s − t) v(s) ds) dt`. The only genuinely analytic step of the
per-certificate route; everything after it is bookkeeping and exact arithmetic.

`g` need only be bounded on `[−lam, lam]`: off that range `v(t)v(s) = 0`. -/
theorem kernel_psi_eq_double {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v)
    {g : ℝ → ℝ} (hg : Measurable g) {Mb : ℝ} (hgb : ∀ α : ℝ, |α| ≤ lam → |g α| ≤ Mb) :
    ∫ α, g α * psi v α = ∫ t, v t * ∫ s, g (s - t) * v s := by
  have hprod := integrable_vv hv
  have hF : Integrable (Function.uncurry fun α s : ℝ => g α * (v (s + α) * v s))
      (volume.prod volume) := by
    have hmeas : AEStronglyMeasurable
        (fun z : ℝ × ℝ => g z.1 * (v (z.2 + z.1) * v z.2)) (volume.prod volume) :=
      ((hg.comp measurable_fst).aestronglyMeasurable).mul hprod.aestronglyMeasurable
    have hb : ∀ z : ℝ × ℝ, ‖g z.1 * (v (z.2 + z.1) * v z.2)‖
        ≤ Mb * (v (z.2 + z.1) * v z.2) := by
      intro z
      have hnn : 0 ≤ v (z.2 + z.1) * v z.2 := mul_nonneg (hv.nonneg _) (hv.nonneg _)
      by_cases h : v z.2 = 0
      · simp [h]
      by_cases h2 : v (z.2 + z.1) = 0
      · simp [h2]
      have a1 := hv.supp _ h2
      have a2 := hv.supp _ h
      have habs : |z.1| ≤ lam := by
        rcases abs_cases z.1 with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
          rcases abs_cases (z.2 + z.1) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
            rcases abs_cases z.2 with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
              rw [e1] <;> rw [e2] at a1 <;> rw [e3] at a2 <;> linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right (hgb z.1 habs) hnn
    exact Integrable.mono' (hprod.const_mul Mb) hmeas (Filter.Eventually.of_forall hb)
  have step1 : ∀ α : ℝ, ∫ s, g α * (v (s + α) * v s) = g α * psi v α := by
    intro α
    rw [integral_const_mul, ← psi_shift]
  have step2 : ∀ t : ℝ, ∫ α, g α * (v (t + α) * v t) = v t * ∫ s, g (s - t) * v s := by
    intro t
    have h1 : ∀ α : ℝ, g α * (v (t + α) * v t) = v t * (g α * v (t + α)) := by
      intro α; ring
    simp_rw [h1]
    rw [integral_const_mul]
    congr 1
    have h2 := integral_sub_right_eq_self (μ := volume) (fun α : ℝ => g α * v (t + α)) t
    simp only [add_sub_cancel] at h2
    exact h2.symm
  calc ∫ α, g α * psi v α = ∫ α, ∫ s, g α * (v (s + α) * v s) := by simp_rw [step1]
    _ = ∫ s, ∫ α, g α * (v (s + α) * v s) := integral_integral_swap hF
    _ = ∫ t, v t * ∫ s, g (s - t) * v s := by simp_rw [step2]

/-! #### Reduction to the quarter plane

For EVEN `v` and EVEN `g` the four sign quadrants of `ℝ²` collapse onto `(0,∞)²` with kernel
`g(s − t) + g(s + t)`. Note `integral_comp_abs` needs no integrability hypothesis, which is why
the OUTER split is done by evenness and only the INNER one by `integral_split_half`. -/

/-- `∫ over ℝ` equals `∫ over (0, ∞)` of `F(s) + F(−s)`. -/
theorem integral_split_half {F : ℝ → ℝ} (hF : Integrable F) :
    ∫ s, F s = ∫ s in Set.Ioi (0 : ℝ), (F s + F (-s)) := by
  have h1 := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hF
  have hc : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic 0 := by
    ext x; simp
  have h2 : ∫ s in Set.Iic (0 : ℝ), F s = ∫ s in Set.Ioi (0 : ℝ), F (-s) := by
    simp
  rw [← h1, hc, h2, ← integral_add hF.integrableOn (hF.comp_neg).integrableOn]

/-- **Reduction to the quarter plane.** For EVEN `v` and EVEN `g`,
`∫ g(α) psi(α) dα = 2∫_{t>0} v(t) ∫_{s>0} (g(s − t) + g(s + t)) v(s)`. -/
theorem kernel_psi_eq_half {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v)
    (heven : ∀ t, v (-t) = v t)
    {g : ℝ → ℝ} (hg : Measurable g) {Mb : ℝ} (hgb : ∀ α : ℝ, |g α| ≤ Mb)
    (hgeven : ∀ α : ℝ, g (-α) = g α) :
    ∫ α, g α * psi v α
      = 2 * ∫ t in Set.Ioi (0 : ℝ), v t * ∫ s in Set.Ioi (0 : ℝ), (g (s - t) + g (s + t)) * v s := by
  have key := kernel_psi_eq_double hv hg (fun α _ => hgb α)
  have hint : ∀ t : ℝ, Integrable (fun s => g (s - t) * v s) := by
    intro t
    refine Integrable.mono' (hv.integrable.norm.const_mul Mb)
      ((hg.comp (measurable_id.sub_const t)).aestronglyMeasurable.mul
        hv.integrable.aestronglyMeasurable) ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)
  have hinner : ∀ t : ℝ, ∫ s, g (s - t) * v s
      = ∫ s in Set.Ioi (0 : ℝ), (g (s - t) + g (s + t)) * v s := by
    intro t
    rw [integral_split_half (hint t)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    have e1 : g (-s - t) = g (s + t) := by
      have : (-s - t : ℝ) = -(s + t) := by ring
      rw [this, hgeven]
    rw [heven s, e1]
    ring
  set H : ℝ → ℝ := fun t => v t * ∫ s in Set.Ioi (0 : ℝ), (g (s - t) + g (s + t)) * v s with hH
  have hHeven : ∀ t : ℝ, H (-t) = H t := by
    intro t
    simp only [hH, heven t]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    have e1 : (s - -t : ℝ) = s + t := by ring
    have e2 : (s + -t : ℝ) = s - t := by ring
    rw [e1, e2]
    ring
  have hLHS : ∫ α, g α * psi v α = ∫ t, H t := by
    rw [key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hH]
    rw [hinner t]
  have h3 : ∫ t, H t = ∫ t, H |t| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show H t = H |t|
    rcases abs_choice t with h | h <;> rw [h]
    exact (hHeven t).symm
  rw [hLHS, h3, integral_comp_abs]

/-! #### The two truncated kernels, and the terminal statements

`wAll L` and `wOut L` are `|·|` and `1_{|·|>1}|·|` cut off outside `[−L, L]`. Truncating is
harmless (`psi` vanishes off `[−lam, lam]`) and makes both kernels BOUNDED, which is what the
bridge wants. `B0_add_B1_half` and `B1_half` are the terminal statements of this section. -/

/-- `|α|`, truncated to `[−L, L]`. Bounded, even and measurable — the bridge needs all three,
and the truncation is invisible to `psi` (`intAbsPsi_wAll`). -/
def wAll (L : ℝ) : ℝ → ℝ := fun α => if |α| ≤ L then |α| else 0

/-- The out-zone kernel, truncated to `[−L, L]`. Same role for the C-penalised zone. -/
def wOut (L : ℝ) : ℝ → ℝ := fun α => if |α| ≤ L then (if 1 < |α| then |α| else 0) else 0

/-- `wAll L` is measurable. -/
theorem wAll_meas (L : ℝ) : Measurable (wAll L) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_abs measurable_const

/-- `wOut L` is measurable. -/
theorem wOut_meas (L : ℝ) : Measurable (wOut L) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const)
    (Measurable.ite (measurableSet_lt measurable_const measurable_abs) measurable_abs
      measurable_const) measurable_const

/-- `wAll L` is even. -/
theorem wAll_even (L : ℝ) (α : ℝ) : wAll L (-α) = wAll L α := by simp [wAll]

/-- `wOut L` is even. -/
theorem wOut_even (L : ℝ) (α : ℝ) : wOut L (-α) = wOut L α := by simp [wOut]

/-- `wAll L` is bounded by `L`. -/
theorem wAll_bdd {L : ℝ} (hL : 0 ≤ L) (α : ℝ) : |wAll L α| ≤ L := by
  unfold wAll
  split
  · rwa [abs_abs]
  · rwa [abs_zero]

/-- `wOut L` is bounded by `L`. -/
theorem wOut_bdd {L : ℝ} (hL : 0 ≤ L) (α : ℝ) : |wOut L α| ≤ L := by
  unfold wOut
  split
  · rename_i h; split
    · rwa [abs_abs]
    · rwa [abs_zero]
  · rwa [abs_zero]

/-- The in-zone and out-zone sets partition `ℝ`. (Same computation as inside `B_eq_Bgen`,
extracted so both users share it.) -/
theorem compl_Icc_one : (Set.Icc (-1 : ℝ) 1)ᶜ = {α : ℝ | 1 < |α|} := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, not_and_or, not_le]
  rcases abs_cases x with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [e]
  · exact ⟨fun h => by rcases h with h | h <;> linarith, fun h => Or.inr (by linarith)⟩
  · exact ⟨fun h => by rcases h with h | h <;> linarith, fun h => Or.inl (by linarith)⟩

/-- `K0 + K1 = ∫ |α| psi(α) dα` over all of `ℝ` — the two zones reassembled. -/
theorem K0_add_K1 {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) :
    K0 v + K1 v = ∫ α, |α| * psi v α := by
  have hsplit := integral_add_compl (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))
    (absPsi_integrable hv)
  rw [K0, K1, ← compl_Icc_one]
  exact hsplit

/-- Truncating the kernel at any `L ≥ lam` does not change `∫ |α| psi`, since `psi` vanishes off
`[−lam, lam]`. -/
theorem intAbsPsi_wAll {lam L : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (hL : lam ≤ L) :
    ∫ α, wAll L α * psi v α = ∫ α, |α| * psi v α := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  simp only []
  by_cases h : |α| ≤ L
  · rw [show wAll L α = |α| from if_pos h]
  · rw [show wAll L α = 0 from if_neg h, psi_supp' hv (by linarith [not_le.mp h])]
    ring

/-- `K1` is the truncated out-zone kernel integrated against `psi`. -/
theorem K1_wOut {lam L : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (hL : lam ≤ L) :
    ∫ α, wOut L α * psi v α = K1 v := by
  rw [K1, ← integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  simp only []
  by_cases h1 : (1 : ℝ) < |α|
  · rw [Set.indicator_of_mem (s := {a : ℝ | 1 < |a|}) h1]
    by_cases h2 : |α| ≤ L
    · rw [show wOut L α = |α| from by
        show (if |α| ≤ L then (if 1 < |α| then |α| else 0) else 0) = |α|
        rw [if_pos h2, if_pos h1]]
    · rw [show wOut L α = 0 from by
        show (if |α| ≤ L then (if 1 < |α| then |α| else 0) else 0) = 0
        rw [if_neg h2], psi_supp' hv (by linarith [not_le.mp h2])]
      ring
  · rw [Set.indicator_of_notMem (s := {a : ℝ | 1 < |a|}) h1,
      show wOut L α = 0 from by simp [wOut, h1]]
    ring

/-- **`|s − t| + (s + t) = 2·max(s, t)`** on the support, at `L = lam`. The absolute value — the
thing that makes `∫ |α| psi` piecewise — disappears on the quarter plane. -/
theorem half_kernel_max {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v)
    {t : ℝ} (htv : v t ≠ 0) (ht : 0 < t) {s : ℝ} (hs : 0 < s) :
    (wAll lam (s - t) + wAll lam (s + t)) * v s = 2 * (max s t * v s) := by
  by_cases hsv : v s = 0
  · simp [hsv]
  have a1 := hv.supp t htv
  have a2 := hv.supp s hsv
  have ht' : t ≤ lam / 2 := le_trans (le_abs_self t) a1
  have hs' : s ≤ lam / 2 := le_trans (le_abs_self s) a2
  have c1 : |s - t| ≤ lam := by
    rcases abs_cases (s - t) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith
  have hst : (0 : ℝ) ≤ s + t := by linarith
  have c2 : |s + t| ≤ lam := by rw [abs_of_nonneg hst]; linarith
  rw [show wAll lam (s - t) = |s - t| from if_pos c1,
    show wAll lam (s + t) = |s + t| from if_pos c2, abs_of_nonneg hst]
  rcases le_total s t with h | h
  · rw [abs_of_nonpos (by linarith : s - t ≤ 0), max_eq_right h]; ring
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t), max_eq_left h]; ring

/-- **On the quarter plane the out-zone kernel is just the corner `s + t > 1`.** The `|s − t| > 1`
branch is empty because `s, t ≤ lam/2 < 1`; this is the ONLY place `lam < 2` is used, and it
is §2.2 own sieve range (delivered by `Cert.hb_hi`), never a comparison of `lam` with 1. -/
theorem half_kernel_out {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (h2 : lam < 2)
    {t : ℝ} (htv : v t ≠ 0) (ht : 0 < t) {s : ℝ} (hs : 0 < s) :
    (wOut lam (s - t) + wOut lam (s + t)) * v s = (if 1 < s + t then s + t else 0) * v s := by
  by_cases hsv : v s = 0
  · simp [hsv]
  have a1 := hv.supp t htv
  have a2 := hv.supp s hsv
  have ht' : t ≤ lam / 2 := le_trans (le_abs_self t) a1
  have hs' : s ≤ lam / 2 := le_trans (le_abs_self s) a2
  have hlam : (0 : ℝ) ≤ lam := by linarith
  have c1 : |s - t| ≤ lam := by
    rcases abs_cases (s - t) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith
  have c1'' : |s - t| ≤ 1 := by
    rcases abs_cases (s - t) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith
  have c1' : ¬ (1 < |s - t|) := not_lt.mpr c1''
  have hst : (0 : ℝ) ≤ s + t := by linarith
  have c2 : |s + t| ≤ lam := by rw [abs_of_nonneg hst]; linarith
  have e1 : wOut lam (s - t) = 0 := by
    show (if |s - t| ≤ lam then (if 1 < |s - t| then |s - t| else 0) else 0) = 0
    rw [if_pos c1, if_neg c1']
  have e2 : wOut lam (s + t) = if 1 < s + t then s + t else 0 := by
    show (if |s + t| ≤ lam then (if 1 < |s + t| then |s + t| else 0) else 0) = _
    rw [if_pos c2, abs_of_nonneg hst]
  rw [e1, e2]
  ring

/-- **TERMINAL STATEMENT 1 of the D24 route.**
`B0 + B1 = ∫v² + 4∫_{t>0} v(t) ∫_{s>0} max(s, t) v(s)`.
For a certificate profile the right-hand side is a finite sum of explicit polynomial integrals
over the mesh cells: `∫_I v`, `∫_I t·v`, `∫_I v²`, and one diagonal term per cell. -/
theorem B0_add_B1_half {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (h0 : 0 ≤ lam)
    (heven : ∀ t, v (-t) = v t) :
    B0 v + B1 v = (∫ t, v t * v t)
      + 4 * ∫ t in Set.Ioi (0 : ℝ), v t * ∫ s in Set.Ioi (0 : ℝ), max s t * v s := by
  have hz : psi v 0 = ∫ t, v t * v t := by simp [psi]
  have hK := K0_add_K1 hv
  have hW := intAbsPsi_wAll hv (le_refl lam)
  have hhalf := kernel_psi_eq_half hv heven (wAll_meas lam) (wAll_bdd h0) (wAll_even lam)
  have hin : ∫ t in Set.Ioi (0 : ℝ), v t
        * ∫ s in Set.Ioi (0 : ℝ), (wAll lam (s - t) + wAll lam (s + t)) * v s
      = 2 * ∫ t in Set.Ioi (0 : ℝ), v t * ∫ s in Set.Ioi (0 : ℝ), max s t * v s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    by_cases htv : v t = 0
    · rw [htv]; ring
    have h1 : ∫ s in Set.Ioi (0 : ℝ), (wAll lam (s - t) + wAll lam (s + t)) * v s
        = ∫ s in Set.Ioi (0 : ℝ), 2 * (max s t * v s) :=
      setIntegral_congr_fun measurableSet_Ioi fun s hs =>
        half_kernel_max hv htv (Set.mem_Ioi.mp ht) (Set.mem_Ioi.mp hs)
    rw [h1, integral_const_mul]
    ring
  have hmain : K0 v + K1 v
      = 4 * ∫ t in Set.Ioi (0 : ℝ), v t * ∫ s in Set.Ioi (0 : ℝ), max s t * v s := by
    rw [hK, ← hW, hhalf, hin]
    ring
  rw [B0, B1, hz]
  linarith [hmain]

/-- **TERMINAL STATEMENT 2 of the D24 route.**
`B1 = 2∫_{t>0} v(t) ∫_{s>0} 1_{s+t>1}(s + t) v(s)`.
For a certificate profile only the TOP cell contributes (`2(1 − b) < 1` iff `b > 1/2`, i.e.
`Cert.hb_lo`), and there the region is a single corner triangle cut by `s = 1 − t` — an
interior cut of that cell exactly because `1 − b` is a mesh point (`Cert.hmesh`). -/
theorem B1_half {lam : ℝ} {v : ℝ → ℝ} (hv : Admissible lam v) (h0 : 0 ≤ lam) (h2 : lam < 2)
    (heven : ∀ t, v (-t) = v t) :
    B1 v = 2 * ∫ t in Set.Ioi (0 : ℝ), v t
        * ∫ s in Set.Ioi (0 : ℝ), (if 1 < s + t then s + t else 0) * v s := by
  have hhalf := kernel_psi_eq_half hv heven (wOut_meas lam) (wOut_bdd h0) (wOut_even lam)
  have hK := K1_wOut hv (le_refl lam)
  have hin : ∫ t in Set.Ioi (0 : ℝ), v t
        * ∫ s in Set.Ioi (0 : ℝ), (wOut lam (s - t) + wOut lam (s + t)) * v s
      = ∫ t in Set.Ioi (0 : ℝ), v t
        * ∫ s in Set.Ioi (0 : ℝ), (if 1 < s + t then s + t else 0) * v s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    by_cases htv : v t = 0
    · rw [htv]; ring
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
      half_kernel_out hv h2 htv (Set.mem_Ioi.mp ht) (Set.mem_Ioi.mp hs)
  rw [B1, ← hK, hhalf, hin]

/-- **The feasibility certificate.** An EVEN piecewise-polynomial profile with exact rational
data: support half-width `b`, interior breakpoints `xs ⊆ (0, b)`, degree `deg`, and per-cell
coefficient blocks `coeff`. Piece `i` on `[xᵢ, xᵢ₊₁]` is `t ↦ Σⱼ coeff[i][j]·(t − xᵢ)ʲ`;
the profile is extended evenly to `[−b, b]` and by `0` outside.

**Provenance of the coefficients (this is the whole of §11's closed-form
build, kept as documentation and OUT of every theorem statement).** The numbers are generated
by the paper's own high-precision payoff script at `mp.dps = 40`: bulk `cos(√2 t)` on
`|t| ≤ t₀ = 1−b`;
edge zone on `t₀ ≤ |t| ≤ b` built from the quartic `(ρ² + 2)² = (C−1)²(1 − ρ²)`, i.e.
`z² + (4+D²)z + (4−D²) = 0` with `D = C−1`, `ρ = √z`, and the reflection collapse
`β = −(z+2)/(D(1+ρ))`, `β(ρ)β(−ρ) = 1`, each z-root giving ONE real solution
`w_z(s) = Re[e^{ρs} + β e^{−ρs}]`; matched at `t₀` with the jump condition
`v'(t₀⁺) = v'(t₀⁻) − (C−1)v(b)`; free boundary `v(b*) = 0` by root-finding on `b ↦ v(b)`.
Lean is the CHECKER, the scripts are the GENERATOR. No EL equation, no quartic, no free
boundary appears in any statement below.

**Why `1 − b ∈ xs` is the whole trick (solver trap (1)).** `ψ = v ⋆ v` is
piecewise polynomial on the partition generated by the SUMSET of `v`'s breakpoints. `W_C`
jumps at `|α| = 1`, so `∫|α|ψ` splits exactly only if `α = 1` is a ψ-cell boundary. With
`t₀ := 1 − b` in the mesh, `1 = b + t₀` is in the sumset automatically. `t₀` is also the true
profile's bulk/edge junction, so no polynomial piece straddles the C¹ kink.

**Practical note.** Write the LAST piece as `(b − t)·p(t)` with `p`'s
Bernstein coefficients `≥ 0`, so `v(b) = 0` exactly and no near-edge sign dip is possible.
This is why the exact sign certificate is required rather than a sampled one — cf. paper §1.6
 and `logs/log_ext_checks.txt`.

**§11's ramp remark, carried verbatim.** "The taper's ramp
does not disturb the optimum, and provably: v* vanishes linearly at the free boundary, so a
ramp of relative width ρ gives ‖δv‖₁ = O(ρ²) and ‖δv‖₂² = O(ρ³); B is stationary at v* for
mass-preserving perturbations, and of the second variation the kernel part pairs two ℓ¹-masses
(O(ρ⁴)) while ψ(0) = ∫v² is an L²-norm — so ΔP = Θ(ρ³), with the ∫v² term as the reason
(stable across three ramp shapes and three grids; measured exponent 3.03–3.09). The
free-boundary condition itself protects the profile." In the certificate route this is MOOT:
the profile is not `v*`-plus-a-ramp, and any ramp cost is already inside `B0q`, `B1q`. See
§7 below for the statements, and note §10.3's "Distinct objects" — the budget's `r₂ = 6w/L`
row and §11's ramp cost are DIFFERENT quantities; nothing consumes §7.

Paper §11.
**Rule 17: `hb_lo` and `hb_hi` are the certificate's OWN DATA conditions**,
not hypotheses on any theorem: `1/2 < b ⟺ λ = 2b > 1` makes the C-zone NONEMPTY (the entire
point of §11), and `b < 1 ⟺ λ < 2` is §2.2's own sieve range. A reviewer must not read
`hb_hi` as a smuggled convenience, and nobody may ever add `b ≤ 1/2`. -/
structure Cert where
  /-- support half-width; `λ_cert = 2b`. -/
  b : ℚ
  /-- interior breakpoints on `(0, b)`, strictly increasing. -/
  xs : List ℚ
  /-- the declared per-cell polynomial degree. -/
  deg : ℕ
  /-- coefficient blocks, one per cell, in ascending powers of `t − xᵢ`. -/
  coeff : List (List ℚ)
  /-- `λ = 2b > 1`: the C-penalised zone is NONEMPTY. **Rule 17's positive form.** -/
  hb_lo : (1 : ℚ) / 2 < b
  /-- `λ = 2b < 2`: §2.2's sieve range `λ ∈ (0,2)`. -/
  hb_hi : b < 1
  /-- **the trick**: `t₀ = 1 − b` is a mesh point, so `α = 1` is a ψ-cell boundary. -/
  hmesh : (1 - b) ∈ xs
  /-- the interior breakpoints really are interior. -/
  hxs_mem : ∀ x ∈ xs, 0 < x ∧ x < b
  /-- strictly increasing. -/
  hxs_sorted : xs.Pairwise (· < ·)
  /-- one coefficient block per cell. -/
  hcoeff_len : coeff.length = xs.length + 1
  /-- **each block really has degree `≤ deg`** (D25). Without this field `Cert.admissible` is
  FALSE: `nonnegCheck` ranges `k` over `range (deg+1)` and `bernsteinCoeff … deg k` sums `j`
  over `range (k+1)`, so only `coeff[i][0..deg]` is ever inspected, while `evalPoly` (hence
  `toFunNonneg`, hence `toFun`) consumes EVERY entry of every block. `hcoeff_len` constrains
  the NUMBER of blocks, never a block's LENGTH, so an over-long block carries entirely
  unchecked coefficients. Machine-checked failing instance for the field-less structure:
  `b = 5/8, xs = [3/8], deg = 0, coeff = [[17/6, -8], [0]]` satisfies every other field and
  both checks (`massHalf = (17/6)(3/8) − 8(3/8)²/2 = 1/2`; the only inspected Bernstein
  coefficients are `17/6 ≥ 0` and `0 ≥ 0`), yet `toFun (37/100) = 17/6 − 8·(37/100) = −19/150`.

  This is what the structure always meant: the certificate generator assumes it
  (shorter coefficient blocks are zero-padded by `getD`) and all four
  shipped certificates satisfy it **with equality**, so no shipped datum changed when the
  field was added. -/
  hdeg : ∀ p ∈ coeff, p.length ≤ deg + 1

namespace Cert

variable (c : Cert)

/-- The full node list `0 < x₁ < … < x_N < b` on `[0, b]`. Length `xs.length + 2`.

Depends on: `Cert`. Rule 17: data only. -/
def nodes : List ℚ := (0 : ℚ) :: (c.xs ++ [c.b])

/-- The `i`-th node, clamped to `b` out of range (so out-of-range cells are empty).

Depends on: `nodes`. Rule 17: data only. -/
def node (i : ℕ) : ℚ := c.nodes.getD i c.b

/-- `λ_cert := 2b`. Strictly between 1 and 2 by `hb_lo`, `hb_hi`.

Paper §11.1(1). Depends on: `Cert`.
Rule 17: this is where `λ > 1` is DELIVERED, not assumed. -/
def lam : ℚ := 2 * c.b

/-- The evaluator on `u ≥ 0`: the piece whose cell `[xᵢ, xᵢ₊₁)` contains `u`, and `0` beyond
`b`. Support `⊆ [0, b]` holds by construction.

Depends on: `evalPoly`, `node`.
Rule 17: data only. -/
def toFunNonneg (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (c.xs.length + 1),
    Set.indicator (Set.Ico ((c.node i : ℚ) : ℝ) ((c.node (i + 1) : ℚ) : ℝ))
      (fun t => evalPoly (c.coeff.getD i []) (t - ((c.node i : ℚ) : ℝ))) u

/-- The real-valued profile the certificate denotes: even, supported in `[−b, b]`.

Evenness is not required by the paper's admissible class but IS imposed here, because it
halves the data and because it makes the two ψ-conventions coincide.
Depends on: `toFunNonneg`.
Rule 17: data only. -/
def toFun : ℝ → ℝ := fun t => c.toFunNonneg |t|

/-- Bernstein coefficient `β_k` of the degree-`n` polynomial `Σⱼ aⱼ uʲ` on the cell `[0, h]`:
`β_k = Σ_{j≤k} (C(k,j)/C(n,j)) aⱼ hʲ`. All-nonneg `β` ⇒ the polynomial is `≥ 0` on the cell.

**Bernstein is preferred over Sturm** —
a cheap sufficient condition, decidable in `ℚ`, complete after subdivision, and far cheaper in
the kernel than exact root counting. Sturm remains the complete fallback if a future mesh
needs it.
Depends on: nothing.
Rule 17: no parameters. -/
def bernsteinCoeff (cs : List ℚ) (h : ℚ) (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1),
    ((Nat.choose k j : ℚ) / (Nat.choose n j : ℚ)) * cs.getD j 0 * h ^ j

/-- The decidable `ℚ`-check behind `NonnegOK`, as a `Bool` so that no instance search is
needed anywhere.

Depends on: `bernsteinCoeff`.
Rule 17: data only. -/
def nonnegCheck : Bool :=
  (List.range (c.xs.length + 1)).all fun i =>
    (List.range (c.deg + 1)).all fun k =>
      decide (0 ≤ bernsteinCoeff (c.coeff.getD i []) (c.node (i + 1) - c.node i) c.deg k)

/-- **Sign certificate**: every Bernstein coefficient of every cell is `≥ 0`, hence `v ≥ 0`.
Decidable by construction (`nonnegCheck` is a `Bool`).

Depends on: `nonnegCheck`. Rule 17: data only. -/
def NonnegOK : Prop := c.nonnegCheck = true

instance : Decidable c.NonnegOK := inferInstanceAs (Decidable (c.nonnegCheck = true))

/-- Exact rational mass of one cell: `∫₀ʰ Σⱼ aⱼ uʲ du = Σⱼ aⱼ hʲ⁺¹/(j+1)`, with `j` the
running index.

Depends on: nothing. Rule 17: no parameters. -/
def massPiece : List ℚ → ℚ → ℕ → ℚ
  | [], _, _ => 0
  | a :: as, h, j => a * h ^ (j + 1) / ((j : ℚ) + 1) + massPiece as h (j + 1)

/-- `∫₀^b v` as an exact rational. The full mass is twice this, by evenness.

Depends on: `massPiece`, `node`.
Rule 17: data only. -/
def massHalf : ℚ :=
  ∑ i ∈ Finset.range (c.xs.length + 1),
    massPiece (c.coeff.getD i []) (c.node (i + 1) - c.node i) 0

/-- **Exact mass identity** `∫v = 1`, as a decidable `ℚ` equation `2·massHalf = 1`.
Trivially arranged by the generator: rescale all coefficients by the reciprocal of the
computed (rational) mass —

Depends on: `massHalf`. Rule 17: data only. -/
def MassOK : Prop := 2 * c.massHalf = 1

instance : Decidable c.MassOK := inferInstanceAs (Decidable (2 * c.massHalf = 1))

/-- `λ_cert > 1` — the C-zone is nonempty. Delivered by the certificate's own `hb_lo`.

**Rule 17: this is the positive statement Rule 17 exists to protect.** Anyone tempted to add
`lam ≤ 1` anywhere in §11 should read this lemma first.
Depends on: `Cert`. -/
theorem one_lt_lam : (1 : ℝ) < (c.lam : ℝ) := by
  have h : (1 : ℚ) < c.lam := by
    have hb := c.hb_lo
    simp only [Cert.lam]
    linarith
  exact_mod_cast h

/-- `λ_cert < 2` — §2.2's sieve range. Delivered by the certificate's own `hb_hi`.

Depends on: `Cert`.
Rule 17: an upper bound on λ, which is the paper's own range and NOT a bandwidth cap of the
forbidden kind. -/
theorem lam_lt_two : (c.lam : ℝ) < 2 := by
  have h : c.lam < (2 : ℚ) := by
    have hb := c.hb_hi
    simp only [Cert.lam]
    linarith
  exact_mod_cast h

/-- The certificate's profile is even.

Depends on: `toFun`.
Rule 17: `lam`-free. -/
theorem toFun_even (t : ℝ) : c.toFun (-t) = c.toFun t := by
  simp only [Cert.toFun, abs_neg]

/-- Support by construction: `v = 0` off `[−b, b]`.

Depends on: `toFun`, `toFunNonneg`. Rule 17: `lam`-free. -/
theorem node_le_b (i : ℕ) : c.node i ≤ c.b := by
  have hall : ∀ x ∈ c.nodes, x ≤ c.b := by
    intro x hx
    simp only [Cert.nodes] at hx
    simp at hx
    rcases hx with rfl | hx | rfl
    · linarith [c.hb_lo]
    · exact (c.hxs_mem x hx).2.le
    · exact le_rfl
  simp only [Cert.node]
  by_cases hlt : i < c.nodes.length
  · rw [List.getD_eq_getElem _ _ hlt]
    exact hall _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ (not_lt.mp hlt)]

theorem toFun_supp {t : ℝ} (h : (c.b : ℝ) < |t|) : c.toFun t = 0 := by
  simp only [Cert.toFun, Cert.toFunNonneg]
  refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem ?_ _
  intro hmem
  have h2 : |t| < ((c.node (i + 1) : ℚ) : ℝ) := hmem.2
  have h3 : ((c.node (i + 1) : ℚ) : ℝ) ≤ ((c.b : ℚ) : ℝ) := by
    exact_mod_cast c.node_le_b (i + 1)
  linarith

/-! ### The piecewise-integration toolkit for the `mass` and `integrable` halves of
`admissible`. `massPiece` and `evalPoly` are put in a common `Finset.range` form and
matched term by term against the interval integral of a polynomial. -/

theorem massPiece_eq_sum : ∀ (cs : List ℚ) (m : ℕ), cs.length ≤ m → ∀ (H : ℚ) (j0 : ℕ),
    Cert.massPiece cs H j0
      = ∑ j ∈ Finset.range m, cs.getD j 0 * H ^ (j0 + j + 1) / (((j0 + j : ℕ) : ℚ) + 1) := by
  intro cs
  induction cs with
  | nil => intro m _ H j0; simp [Cert.massPiece]
  | cons a as ih =>
    intro m hm H j0
    cases m with
    | zero => simp at hm
    | succ m =>
      have hm' : as.length ≤ m := by simpa using hm
      rw [Cert.massPiece, ih m hm' H (j0 + 1),
        Finset.sum_range_succ'
          (fun j => (a :: as).getD j 0 * H ^ (j0 + j + 1) / (((j0 + j : ℕ) : ℚ) + 1)) m]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have e : j0 + 1 + j = j0 + (j + 1) := by omega
      rw [e]

theorem integral_evalPoly (cs : List ℚ) (H : ℝ) :
    ∫ x in (0 : ℝ)..H, evalPoly cs x
      = ∑ j ∈ Finset.range cs.length,
          ((cs.getD j 0 : ℚ) : ℝ) * H ^ (j + 1) / ((j : ℝ) + 1) := by
  have h1 : ∀ x : ℝ,
      evalPoly cs x = ∑ j ∈ Finset.range cs.length, ((cs.getD j 0 : ℚ) : ℝ) * x ^ j :=
    fun x => evalPoly_eq_sum cs cs.length le_rfl x
  simp only [h1]
  have hii : ∀ j ∈ Finset.range cs.length,
      IntervalIntegrable (fun x : ℝ => ((cs.getD j 0 : ℚ) : ℝ) * x ^ j) volume 0 H :=
    fun j _ => (Continuous.mul continuous_const (continuous_pow j)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hii]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero j), sub_zero]
  have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem integral_cell (cs : List ℚ) (a b : ℚ) (hab : a ≤ b) :
    ∫ u in Set.Ico ((a : ℚ) : ℝ) ((b : ℚ) : ℝ), evalPoly cs (u - ((a : ℚ) : ℝ))
      = ((Cert.massPiece cs (b - a) 0 : ℚ) : ℝ) := by
  have habR : ((a : ℚ) : ℝ) ≤ ((b : ℚ) : ℝ) := by exact_mod_cast hab
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le habR,
    intervalIntegral.integral_comp_sub_right (fun x => evalPoly cs x) ((a : ℚ) : ℝ),
    sub_self, integral_evalPoly, massPiece_eq_sum cs cs.length le_rfl (b - a) 0]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem node_nonneg (c : Cert) (i : ℕ) : 0 ≤ c.node i := by
  have hall : ∀ x ∈ c.nodes, (0 : ℚ) ≤ x := by
    intro x hx
    simp only [Cert.nodes] at hx
    simp at hx
    rcases hx with rfl | hx | rfl
    · exact le_rfl
    · exact (c.hxs_mem x hx).1.le
    · linarith [c.hb_lo]
  simp only [Cert.node]
  by_cases hlt : i < c.nodes.length
  · rw [List.getD_eq_getElem _ _ hlt]
    exact hall _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ (not_lt.mp hlt)]
    linarith [c.hb_lo]

theorem nodes_pairwise (c : Cert) : c.nodes.Pairwise (· ≤ ·) := by
  simp only [Cert.nodes]
  rw [List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact (c.hxs_mem y h).1.le
    · simp at h
      rw [h]
      linarith [c.hb_lo]
  · rw [List.pairwise_append]
    refine ⟨c.hxs_sorted.imp le_of_lt, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    simp at hy
    rw [hy]
    exact (c.hxs_mem x hx).2.le

theorem node_le_succ (c : Cert) (i : ℕ) : c.node i ≤ c.node (i + 1) := by
  by_cases h : i + 1 < c.nodes.length
  · have hi : i < c.nodes.length := by omega
    simp only [Cert.node]
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ h]
    exact List.pairwise_iff_getElem.mp (nodes_pairwise c) i (i + 1) hi h (by omega)
  · have : c.node (i + 1) = c.b := by
      simp only [Cert.node]
      exact List.getD_eq_default _ _ (by omega)
    rw [this]
    exact c.node_le_b i

theorem toFunNonneg_integrable (c : Cert) : Integrable c.toFunNonneg := by
  have hrw : c.toFunNonneg = fun u : ℝ => ∑ i ∈ Finset.range (c.xs.length + 1),
      Set.indicator (Set.Ico ((c.node i : ℚ) : ℝ) ((c.node (i + 1) : ℚ) : ℝ))
        (fun t => evalPoly (c.coeff.getD i []) (t - ((c.node i : ℚ) : ℝ))) u := rfl
  rw [hrw]
  refine integrable_finsetSum _ fun i _ => ?_
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Ico
  exact IntegrableOn.mono_set
    (((evalPoly_continuous _).comp (continuous_id.sub continuous_const)).integrableOn_Icc)
    Set.Ico_subset_Icc_self

theorem toFun_integrable (c : Cert) : Integrable c.toFun := by
  have hF := c.toFunNonneg_integrable
  have hdec : c.toFun = fun t => Set.indicator (Set.Ici (0 : ℝ)) c.toFunNonneg t
      + Set.indicator (Set.Iio (0 : ℝ)) (fun s => c.toFunNonneg (-s)) t := by
    funext t
    rcases le_or_gt 0 t with h | h
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr h),
        Set.indicator_of_notMem (fun hc => absurd (Set.mem_Iio.mp hc) (not_lt.mpr h))]
      simp only [Cert.toFun, abs_of_nonneg h, add_zero]
    · rw [Set.indicator_of_notMem (fun hc => absurd (Set.mem_Ici.mp hc) (not_le.mpr h)),
        Set.indicator_of_mem (Set.mem_Iio.mpr h)]
      simp only [Cert.toFun, abs_of_neg h, zero_add]
  rw [hdec]
  exact Integrable.add (hF.integrableOn.integrable_indicator measurableSet_Ici)
    (hF.comp_neg.integrableOn.integrable_indicator measurableSet_Iio)

theorem toFunNonneg_integral (c : Cert) :
    ∫ x, c.toFunNonneg x = ((c.massHalf : ℚ) : ℝ) := by
  have hint : ∀ i ∈ Finset.range (c.xs.length + 1),
      Integrable (Set.indicator (Set.Ico ((c.node i : ℚ) : ℝ) ((c.node (i + 1) : ℚ) : ℝ))
        (fun t => evalPoly (c.coeff.getD i []) (t - ((c.node i : ℚ) : ℝ)))) := by
    intro i _
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ico
    exact IntegrableOn.mono_set
      (((evalPoly_continuous _).comp (continuous_id.sub continuous_const)).integrableOn_Icc)
      Set.Ico_subset_Icc_self
  simp only [Cert.toFunNonneg]
  rw [MeasureTheory.integral_finsetSum _ hint, Cert.massHalf]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_indicator measurableSet_Ico]
  have hc := integral_cell (c.coeff.getD i []) (c.node i) (c.node (i + 1)) (c.node_le_succ i)
  rw [hc]

theorem toFun_mass (c : Cert) (h2 : c.MassOK) : ∫ t, c.toFun t = 1 := by
  have habs : ∫ t, c.toFun t = 2 * ∫ x in Set.Ioi (0 : ℝ), c.toFunNonneg x := by
    simp only [Cert.toFun]
    exact integral_comp_abs
  have hIci : ∫ x in Set.Ioi (0 : ℝ), c.toFunNonneg x = ∫ x, c.toFunNonneg x := by
    rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    have hx' : x < 0 := by simpa using hx
    simp only [Cert.toFunNonneg]
    refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem ?_ _
    intro hmem
    have h0 : (0 : ℝ) ≤ ((c.node i : ℚ) : ℝ) := by exact_mod_cast c.node_nonneg i
    linarith [hmem.1]
  rw [habs, hIci, c.toFunNonneg_integral]
  have : ((2 * c.massHalf : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by rw [h2]
  push_cast at this
  linarith

/-- The power-basis-to-Bernstein-basis identity, in the exact form `bernsteinCoeff` produces:
`Σⱼ aⱼ hʲ sʲ = Σₖ βₖ C(n,k) sᵏ (1−s)ⁿ⁻ᵏ`.

The proof is the classical one: substitute `C(k,j)·C(n,k)/C(n,j) = C(n−j, k−j)`
(`choose_div_mul`), swap the triangular double sum (`Finset.sum_Ico_Ico_comm`), reindex
`k = j + i`, and collapse the inner sum by the binomial theorem `(s + (1−s))ⁿ⁻ʲ = 1`. -/
theorem bernstein_sum_eq (cs : List ℚ) (h : ℚ) (n : ℕ) (s : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        ((bernsteinCoeff cs h n k : ℚ) : ℝ) * (n.choose k : ℝ) * s ^ k * (1 - s) ^ (n - k)
      = ∑ j ∈ Finset.range (n + 1), ((cs.getD j 0 : ℚ) : ℝ) * (h : ℝ) ^ j * s ^ j := by
  have key : ∀ k ∈ Finset.range (n + 1),
      ((bernsteinCoeff cs h n k : ℚ) : ℝ) * (n.choose k : ℝ) * s ^ k * (1 - s) ^ (n - k)
        = ∑ j ∈ Finset.range (k + 1),
            (((cs.getD j 0 : ℚ) : ℝ) * (h : ℝ) ^ j) *
              (((n - j).choose (k - j) : ℝ) * s ^ k * (1 - s) ^ (n - k)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hB : bernsteinCoeff cs h n k * (n.choose k : ℚ)
        = ∑ j ∈ Finset.range (k + 1), cs.getD j 0 * h ^ j * ((n - j).choose (k - j) : ℚ) := by
      rw [bernsteinCoeff, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [← choose_div_mul n k j hjk hkn]
      ring
    calc ((bernsteinCoeff cs h n k : ℚ) : ℝ) * (n.choose k : ℝ) * s ^ k * (1 - s) ^ (n - k)
        = ((bernsteinCoeff cs h n k * (n.choose k : ℚ) : ℚ) : ℝ)
            * (s ^ k * (1 - s) ^ (n - k)) := by push_cast; ring
      _ = ((∑ j ∈ Finset.range (k + 1),
              cs.getD j 0 * h ^ j * ((n - j).choose (k - j) : ℚ) : ℚ) : ℝ)
            * (s ^ k * (1 - s) ^ (n - k)) := by rw [hB]
      _ = ∑ j ∈ Finset.range (k + 1),
            (((cs.getD j 0 : ℚ) : ℝ) * (h : ℝ) ^ j) *
              (((n - j).choose (k - j) : ℝ) * s ^ k * (1 - s) ^ (n - k)) := by
          push_cast
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl key]
  simp only [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_Ico_comm 0 (n + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hj).2
  rw [← Finset.mul_sum]
  have hinner : ∑ k ∈ Finset.Ico j (n + 1),
      (((n - j).choose (k - j) : ℕ) : ℝ) * s ^ k * (1 - s) ^ (n - k) = s ^ j := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : n + 1 - j = (n - j) + 1 := by omega
    rw [hlen]
    have hterm : ∀ i ∈ Finset.range ((n - j) + 1),
        (((n - j).choose (j + i - j) : ℕ) : ℝ) * s ^ (j + i) * (1 - s) ^ (n - (j + i))
          = s ^ j * (s ^ i * (1 - s) ^ ((n - j) - i) * (((n - j).choose i : ℕ) : ℝ)) := by
      intro i hi
      have hi' : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have e1 : j + i - j = i := by omega
      have e2 : n - (j + i) = (n - j) - i := by omega
      rw [e1, e2, pow_add]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
    norm_num
  rw [hinner]

/-- **THE BERNSTEIN TRANSFER**, proved: a polynomial of degree
`≤ n` whose degree-`n` Bernstein coefficients on `[0, h]` are all `≥ 0` is itself `≥ 0` on
`[0, h]`. Each Bernstein basis function `C(n,k) sᵏ (1−s)ⁿ⁻ᵏ` is nonnegative for `s ∈ [0,1]`,
so `bernstein_sum_eq` turns the coefficient check into pointwise nonnegativity.

**`hlen` is essential and is exactly what `Cert` fails to record** — see the note on
`admissible` below. Without it the coefficients of index `> n` are invisible to
`bernsteinCoeff` and the conclusion is false. -/
theorem evalPoly_nonneg_of_bernstein {cs : List ℚ} {h : ℚ} {n : ℕ} (hh : 0 < h)
    (hlen : cs.length ≤ n + 1) (hb : ∀ k ≤ n, 0 ≤ bernsteinCoeff cs h n k)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ (h : ℝ)) : 0 ≤ evalPoly cs u := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  obtain ⟨s, hs0, hs1, hus⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ u = s * (h : ℝ) :=
    ⟨u / (h : ℝ), div_nonneg hu0 hhR.le, (div_le_one hhR).mpr hu1, by field_simp⟩
  rw [evalPoly_eq_sum cs (n + 1) hlen u]
  have hrw : ∑ j ∈ Finset.range (n + 1), ((cs.getD j 0 : ℚ) : ℝ) * u ^ j
      = ∑ j ∈ Finset.range (n + 1), ((cs.getD j 0 : ℚ) : ℝ) * (h : ℝ) ^ j * s ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hus, mul_pow]
    ring
  rw [hrw, ← bernstein_sum_eq]
  refine Finset.sum_nonneg fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : (0 : ℝ) ≤ ((bernsteinCoeff cs h n k : ℚ) : ℝ) := by exact_mod_cast hb k hkn
  have h2 : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) (pow_nonneg hs0 k))
    (pow_nonneg (by linarith) _)

/-- The `Bool` sign certificate, unpacked: `NonnegOK` really does give every Bernstein
coefficient of every cell. -/
theorem bernstein_nonneg (h1 : c.NonnegOK) {i : ℕ} (hi : i < c.xs.length + 1)
    {k : ℕ} (hk : k ≤ c.deg) :
    0 ≤ bernsteinCoeff (c.coeff.getD i []) (c.node (i + 1) - c.node i) c.deg k := by
  simp only [Cert.NonnegOK, Cert.nonnegCheck] at h1
  have h2 := List.all_eq_true.mp h1 i (List.mem_range.mpr hi)
  have h3 := List.all_eq_true.mp h2 k (List.mem_range.mpr (Nat.lt_succ_of_le hk))
  exact of_decide_eq_true h3

/-- **`v ≥ 0` — the Bernstein half of `admissible`, proved, under the one hypothesis `Cert`
does not carry**: that each coefficient block really has degree `≤ deg`.

Note that the cell width `h = node(i+1) − node i` is positive *for free* here: it is extracted
from the `Set.Ico` membership, not from `hxs_sorted`. -/
theorem toFun_nonneg (h1 : c.NonnegOK) (hdeg : ∀ p ∈ c.coeff, p.length ≤ c.deg + 1) (t : ℝ) :
    0 ≤ c.toFun t := by
  simp only [Cert.toFun, Cert.toFunNonneg]
  refine Finset.sum_nonneg fun i hi => ?_
  by_cases hmem : |t| ∈ Set.Ico ((c.node i : ℚ) : ℝ) ((c.node (i + 1) : ℚ) : ℝ)
  · rw [Set.indicator_of_mem hmem]
    have hlt : ((c.node i : ℚ) : ℝ) < ((c.node (i + 1) : ℚ) : ℝ) := lt_of_le_of_lt hmem.1 hmem.2
    have hltQ : c.node i < c.node (i + 1) := by exact_mod_cast hlt
    have hpos : 0 < c.node (i + 1) - c.node i := by linarith
    have hlen : (c.coeff.getD i []).length ≤ c.deg + 1 := by
      by_cases hi' : i < c.coeff.length
      · rw [List.getD_eq_getElem _ _ hi']
        exact hdeg _ (List.getElem_mem hi')
      · rw [List.getD_eq_default _ _ (not_lt.mp hi')]
        simp
    refine evalPoly_nonneg_of_bernstein hpos hlen
      (fun k hk => c.bernstein_nonneg h1 (Finset.mem_range.mp hi) hk) (by linarith [hmem.1]) ?_
    have hcast : ((c.node (i + 1) - c.node i : ℚ) : ℝ)
        = ((c.node (i + 1) : ℚ) : ℝ) - ((c.node i : ℚ) : ℝ) := by push_cast; ring
    rw [hcast]
    linarith [hmem.2]
  · rw [Set.indicator_of_notMem hmem]

/-- **The repaired `admissible`**: exactly `Cert.admissible`, plus the degree bound that `Cert`
fails to record. -/
theorem admissible_of_degBound (c : Cert) (h1 : c.NonnegOK) (h2 : c.MassOK)
    (hdeg : ∀ p ∈ c.coeff, p.length ≤ c.deg + 1) :
    Admissible ((c.lam : ℚ) : ℝ) c.toFun where
  nonneg := c.toFun_nonneg h1 hdeg
  integrable := c.toFun_integrable
  mass := c.toFun_mass h2
  supp := by
    intro t ht
    by_contra hc
    rw [not_le] at hc
    have hl : ((c.lam : ℚ) : ℝ) / 2 = ((c.b : ℚ) : ℝ) := by
      simp only [Cert.lam]; push_cast; ring
    rw [hl] at hc
    exact ht (c.toFun_supp hc)

/-- **The certificate is admissible.** `v ≥ 0` from the Bernstein check, `∫v = 1` from the
mass check, `supp v ⊆ [−λ/2, λ/2] = [−b, b]` by construction.

=============================================================================================
**HISTORY: this statement was FALSE until `Cert` gained `hdeg` (D25).** Now proved.
=============================================================================================
The defect: `nonnegCheck` ranges `k` over `List.range (c.deg + 1)` and
`bernsteinCoeff … c.deg k` sums `j` over `range (k + 1)`, so **only the coefficients
`coeff[i][0 .. deg]` are ever inspected**, whereas `evalPoly` (hence `toFunNonneg`, hence
`toFun`) uses every entry — and the old `Cert` constrained the NUMBER of blocks
(`hcoeff_len`) but never the LENGTH of a block. Machine-checked failing instance:
`b = 5/8, xs = [3/8], deg = 0, coeff = [[17/6, -8], [0]]` passed every field and both checks
yet had `toFun (37/100) = −19/150 < 0`.

D25 repaired the structure rather than the statement: `Cert.hdeg` is the invariant the
structure always meant (see its own docstring), all four shipped certificates satisfy it with
equality, and no shipped datum changed. The proof is then one application of
`admissible_of_degBound`, which is the same theorem with the bound supplied by hand.

Paper §11; RESOLUTIONS D25.
Depends on: `admissible_of_degBound`, `NonnegOK`, `MassOK`, `Cert.hdeg`.
**Rule 17: the conclusion is at `lam = c.lam = 2b > 1` — see `one_lt_lam`.** -/
theorem admissible (h1 : c.NonnegOK) (h2 : c.MassOK) :
    Admissible ((c.lam : ℚ) : ℝ) c.toFun :=
  admissible_of_degBound c h1 h2 c.hdeg

/-- The certificate's profile as a list of pieces in the GLOBAL variable `t`: cell `i` on
`[xᵢ, xᵢ₊₁)` carries `coeffᵢ(t − xᵢ)` and its even reflection `coeffᵢ(−t − xᵢ)` on
`[−xᵢ₊₁, −xᵢ)`.

Depends on: `pcomp`, `nodes`.
Rule 17: data only. -/
def piecesFrom : List ℚ → List (List ℚ) → List Piece
  | x0 :: x1 :: xs, cs :: css =>
      (x0, x1, pcomp cs [-x0, 1]) :: (-x1, -x0, pcomp cs [-x0, -1]) :: piecesFrom (x1 :: xs) css
  | _, _ => []

/-- The pieces of `c.toFun`. -/
def certPieces (cert : Cert) : List Piece := piecesFrom cert.nodes cert.coeff

/-- **The engine's output: `(B0q, B1q)` in one pass.**

`ψ` is an autocorrelation, hence EVEN unconditionally, so
`∫_{|α|≤1}|α|ψ = 2∫₀¹ αψ` and `∫_{|α|>1}|α|ψ = 2∫₁^{2b} αψ` (the upper cut is automatic:
`supp ψ ⊆ [−2b, 2b] = [−λ, λ]`). Both halves are computed from the same cell blocks, which is
why they are produced together rather than by two independent traversals.

Depends on: `allPsi`, `certPieces`.
Rule 17: data only — `2 * cert.b` is `λ_cert`, never compared with 1. -/
def payoffPartsQ (cert : Cert) : ℚ × ℚ :=
  (psiAtZero (allPsi (certPieces cert)) + 2 * sumInt (allPsi (certPieces cert)) 0 1,
    2 * sumInt (allPsi (certPieces cert)) 1 (2 * cert.b))

/-- The exact rational `B0 = ψ(0) + ∫_{|α|≤1}|α|ψ` of the certificate's profile.

**Implemented** by the symbolic piecewise-polynomial convolution engine of §3a above
(`ψ` has degree `≤ 2·deg + 1` on the `≤ (2N)²` sumset cells), the one genuinely missing object
of §11. `payoff_hp2.py` is the generator to
mirror.
Paper §11.
Depends on: `Cert`. Rule 17: data only.
(The `Cert` argument is bound EXPLICITLY rather than via `variable`; the binder is named
`cert` so it does not shadow the section variable `c`.) -/
def B0q (cert : Cert) : ℚ := (payoffPartsQ cert).1

/-- The exact rational `B1 = ∫_{1<|α|≤λ}|α|ψ`. Nonnegative automatically.

Same status as `B0q`: the second component of `payoffPartsQ`.
Paper §11. Depends on: `Cert`.
Rule 17: data only — this is the quantity that is identically 0 when `λ ≤ 1`, which is why
`hb_lo` is a field of the structure. Explicit `Cert` binder for the same reason as `B0q`. -/
def B1q (cert : Cert) : ℚ := (payoffPartsQ cert).2

/-- **OPTIONAL BY RESOLUTIONS D24, AND NO LONGER LOAD-BEARING.** `B0` of the certificate's
profile is the exact rational the §3a ℚ engine returns, **for every certificate**.

**Nothing Theorem 1 needs goes through this any more.** §3c (`two_cell_payoff'`) evaluates `B0`
and `B1` for the four shipped certificates outright, and `payoff_of_cert_num` carries all five
`payoff_feasible_*` theorems. Only the generic wrapper `payoff_of_cert` still cites this lemma,
and nothing consumes `payoff_of_cert`.

This is full engine-correctness: it needs semantics for `padd`/`pmul`/`pcomp`/`pint`/`p2add`/
`p2mul`/`p2sub`/`p2evalT`, `convPair` as a parametric interval integral with affine endpoints,
branch-constancy of those endpoints on every cell of `pairCells`, and the cell-by-cell
reassembly of `allPsi` into `ψ`. That was scoped at multi-week size. D24 records
the decision not to pay it: only four fixed certificates are ever needed, and for a specific
ψ with a known mesh and known rational coefficients `B0` is a finite explicit polynomial
integral. §3b proves the ANALYTIC half of that replacement route (`B0_add_B1_half`,
`B1_half`) and §3c does the remaining bookkeeping and exact-ℚ arithmetic, so the replacement is
complete and this statement is no longer load-bearing.

The engine's remaining role is as GENERATOR and as CROSS-CHECK on the ℚ literals, and in that
role it is already validated three ways: `flat_gate_one` / `flat_gate_five_quarters`
(closed-form calibration at λ = 1 and λ = 5/4), `certQQ_parts` and its three siblings
(agreement with the generator's reference values *as exact rationals*), and an
independent mpmath double integral agreeing to 24 digits.

Kept, stated as a named `Prop`, for anyone who wants the stronger result.
Paper §11; RESOLUTIONS D24.
Depends on: `B0q`, `admissible`, `psi`. Rule 17: no bandwidth hypothesis.

**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than a
`sorry`-ed theorem: still elaborated and type-checked on every build, visibly not a fact,
and impossible to cite as one.  `payoff_of_cert` now takes it as an explicit HYPOTHESIS
(the `hsieve : LargeSieveHyp` idiom of §8), so that wrapper is `sorry`-free too.
-/
def B0Eq (c : Cert) : Prop :=
  c.NonnegOK → c.MassOK → B0 c.toFun = ((c.B0q : ℚ) : ℝ)

/-- **OPTIONAL BY RESOLUTIONS D24, AND NO LONGER LOAD-BEARING.** `B1` of the certificate's
profile is the exact rational the §3a ℚ engine returns, **for every certificate**. Same status,
same reasons, same replacement as `B0Eq` — read its docstring. `B0B1_certQQ` and its three
siblings supply what the feasibility theorems actually need.

Paper §11; RESOLUTIONS D24.
Depends on: `B1q`, `admissible`, `psi`.
Rule 17: the ψ-cell boundary at `α = 1` is supplied by `hmesh`, not by any relation between
`lam` and 1.

**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than a
`sorry`-ed theorem: still elaborated and type-checked on every build, visibly not a fact,
and impossible to cite as one.  `payoff_of_cert` now takes it as an explicit HYPOTHESIS
(the `hsieve : LargeSieveHyp` idiom of §8), so that wrapper is `sorry`-free too.
-/
def B1Eq (c : Cert) : Prop :=
  c.NonnegOK → c.MassOK → B1 c.toFun = ((c.B1q : ℚ) : ℝ)

end Cert

/-! ### 3c. THE D24 REPLACEMENT, CARRIED OUT: the two-cell Gram engine in exact ℚ

§3b left `B0 + B1` and `B1` as quarter-plane double integrals. All four shipped certificates
have exactly TWO cells (`xs = [1 − b]`, forced: `hmesh` puts `1 − b` in `xs`, and a two-cell
mesh has only that one interior node), so those double integrals are finite explicit
polynomial integrals over `[0, 1−b]` and `[1−b, b]`. This block does that bookkeeping once,
generically in the cell data, and the result is `two_cell_payoff`: an exact ℚ value for `B0`
and `B1`. Nothing here is analysis — every step is `∫ evalPoly = evalPoly ∘ pint`
(`integral_evalPoly_interval`) plus indicator bookkeeping.

The three shapes that occur, all read off §3b:
  * `∫_{s>0} max(s,t) v(s) ds = t·A(t) + (S(b) − S(t))` with `A = ∫₀ᵗ v`, `S = ∫₀ᵗ s v(s) ds`
    — `gramPhi0` on the bottom cell, `gramPhi1` on the top cell;
  * `∫_{s>0} 1_{s+t>1}(s+t) v(s) ds` is `0` for `t ≤ 1 − b` and, for `t ≥ 1 − b`, the single
    corner integral `∫_{1−t}^{b}(s+t)v(s)ds` — `gramInner`. This is exactly §3b's "one corner
    triangle on the top cell", and `1 − t` stays inside that cell because `1 − b` is a mesh
    point (`hmesh`);
  * `∫v² = 2(∫₀^{1−b} v² + ∫_{1−b}^{b} v²)`.
Then `B1 = 2N` and `B0 = ∫v² + 4M − 2N`.

Rule 17: `lam` never meets 1 here; `hb_lo`/`hb_hi` enter only through
`Cert.one_lt_lam` / `Cert.lam_lt_two`, which are what `B1_half` consumes. -/

/-- `evalPoly (pint p) 0 = 0`: the antiderivative `pint` has zero constant term. -/
theorem evalPoly_pint_zero (p : List ℚ) : evalPoly (pint p) 0 = 0 := by
  simp [pint, evalPoly_cons]

/-- The polynomial FTC with RATIONAL endpoints, landing in `pdefint`. -/
theorem integral_evalPoly_Q (p : List ℚ) (a b : ℚ) :
    ∫ x in ((a : ℚ) : ℝ)..((b : ℚ) : ℝ), evalPoly p x = ((pdefint p a b : ℚ) : ℝ) := by
  rw [integral_evalPoly_interval, pdefint, Rat.cast_sub, pevalQ_cast, pevalQ_cast]

/-- The same with lower endpoint the literal `0 : ℝ`. -/
theorem integral_evalPoly_Q0 (p : List ℚ) (b : ℚ) :
    ∫ x in (0 : ℝ)..((b : ℚ) : ℝ), evalPoly p x = ((pdefint p 0 b : ℚ) : ℝ) := by
  rw [integral_evalPoly_interval, pdefint, Rat.cast_sub, pevalQ_cast, pevalQ_cast, Rat.cast_zero]

/-- The reflection `t ↦ 1 − t` in engine form: this is what turns the corner cut `s = 1 − t`
into a polynomial in `t`. -/
theorem evalPoly_comp_one_sub (p : List ℚ) (t : ℝ) :
    evalPoly (pcomp p [1, -1]) t = evalPoly p (1 - t) := by
  rw [evalPoly_pcomp]
  congr 1
  simp only [evalPoly_cons, evalPoly_nil]
  push_cast
  ring

/-- **Cutting a half-line integral at three interior nodes.** If `F` agrees on `[0, ∞)` with a
sum of three interval-supported continuous pieces, its `Ioi 0` integral is the sum of the three
interval integrals. Every reduction in §3c is one call to this (or its two/one-piece forms). -/
theorem intIoi_split3 {F G1 G2 G3 : ℝ → ℝ} {p0 p1 p2 p3 : ℝ}
    (hp0 : 0 ≤ p0) (h01 : p0 ≤ p1) (h12 : p1 ≤ p2) (h23 : p2 ≤ p3)
    (hG1 : Continuous G1) (hG2 : Continuous G2) (hG3 : Continuous G3)
    (hF : ∀ x : ℝ, 0 ≤ x → F x = Set.indicator (Set.Ico p0 p1) G1 x
        + Set.indicator (Set.Ico p1 p2) G2 x + Set.indicator (Set.Ico p2 p3) G3 x) :
    ∫ x in Set.Ioi (0 : ℝ), F x
      = (∫ x in p0..p1, G1 x) + (∫ x in p1..p2, G2 x) + ∫ x in p2..p3, G3 x := by
  have hi : ∀ (G : ℝ → ℝ), Continuous G → ∀ a b : ℝ,
      Integrable (Set.indicator (Set.Ico a b) G) := by
    intro G hG a b
    exact (hG.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self).integrable_indicator
      measurableSet_Ico
  have hi1 := hi G1 hG1 p0 p1
  have hi2 := hi G2 hG2 p1 p2
  have hi3 := hi G3 hG3 p2 p3
  have hi12 : Integrable (fun x : ℝ => Set.indicator (Set.Ico p0 p1) G1 x
      + Set.indicator (Set.Ico p1 p2) G2 x) := hi1.add hi2
  calc ∫ x in Set.Ioi (0 : ℝ), F x
      = ∫ x in Set.Ici (0 : ℝ), F x := (integral_Ici_eq_integral_Ioi).symm
    _ = ∫ x in Set.Ici (0 : ℝ), (Set.indicator (Set.Ico p0 p1) G1 x
          + Set.indicator (Set.Ico p1 p2) G2 x + Set.indicator (Set.Ico p2 p3) G3 x) :=
        setIntegral_congr_fun measurableSet_Ici fun x hx => hF x (Set.mem_Ici.mp hx)
    _ = ∫ x, (Set.indicator (Set.Ico p0 p1) G1 x
          + Set.indicator (Set.Ico p1 p2) G2 x + Set.indicator (Set.Ico p2 p3) G3 x) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro x hx
        have hx' : x < 0 := by simpa using hx
        have e1 : x ∉ Set.Ico p0 p1 := fun h => by have := h.1; linarith
        have e2 : x ∉ Set.Ico p1 p2 := fun h => by have := h.1; linarith
        have e3 : x ∉ Set.Ico p2 p3 := fun h => by have := h.1; linarith
        rw [Set.indicator_of_notMem e1, Set.indicator_of_notMem e2, Set.indicator_of_notMem e3]
        ring
    _ = (∫ x, Set.indicator (Set.Ico p0 p1) G1 x) + (∫ x, Set.indicator (Set.Ico p1 p2) G2 x)
          + ∫ x, Set.indicator (Set.Ico p2 p3) G3 x := by
        rw [integral_add hi12 hi3, integral_add hi1 hi2]
    _ = (∫ x in p0..p1, G1 x) + (∫ x in p1..p2, G2 x) + ∫ x in p2..p3, G3 x := by
        rw [integral_indicator measurableSet_Ico, integral_indicator measurableSet_Ico,
          integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
          integral_Ico_eq_integral_Ioc, integral_Ico_eq_integral_Ioc,
          intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h12,
          intervalIntegral.integral_of_le h23]

/-- Two-piece form of `intIoi_split3`. -/
theorem intIoi_split2 {F G1 G2 : ℝ → ℝ} {p0 p1 p2 : ℝ}
    (hp0 : 0 ≤ p0) (h01 : p0 ≤ p1) (h12 : p1 ≤ p2)
    (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hF : ∀ x : ℝ, 0 ≤ x → F x = Set.indicator (Set.Ico p0 p1) G1 x
        + Set.indicator (Set.Ico p1 p2) G2 x) :
    ∫ x in Set.Ioi (0 : ℝ), F x = (∫ x in p0..p1, G1 x) + ∫ x in p1..p2, G2 x := by
  have h := intIoi_split3 (F := F) (G3 := fun _ : ℝ => (0 : ℝ)) (p3 := p2) hp0 h01 h12 le_rfl
    hG1 hG2 continuous_const (fun x hx => by rw [hF x hx]; simp)
  simpa using h

/-- One-piece form over an OPEN cell — needed for the out-zone corner, whose lower cut
`s = 1 − t` is a point where the kernel is `0` but the polynomial is not. -/
theorem intIoi_Ioo {F G : ℝ → ℝ} {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hG : Continuous G)
    (hF : ∀ x : ℝ, 0 ≤ x → F x = Set.indicator (Set.Ioo p q) G x) :
    ∫ x in Set.Ioi (0 : ℝ), F x = ∫ x in p..q, G x := by
  have hi : Integrable (Set.indicator (Set.Ioo p q) G) :=
    (hG.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  calc ∫ x in Set.Ioi (0 : ℝ), F x
      = ∫ x in Set.Ici (0 : ℝ), F x := (integral_Ici_eq_integral_Ioi).symm
    _ = ∫ x in Set.Ici (0 : ℝ), Set.indicator (Set.Ioo p q) G x :=
        setIntegral_congr_fun measurableSet_Ici fun x hx => hF x (Set.mem_Ici.mp hx)
    _ = ∫ x, Set.indicator (Set.Ioo p q) G x := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
        intro x hx
        have hx' : x < 0 := by simpa using hx
        exact Set.indicator_of_notMem (fun h => by have := h.1; linarith) _
    _ = ∫ x in p..q, G x := by
        rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
          intervalIntegral.integral_of_le hpq]

/-- The top cell's polynomial in the GLOBAL variable `t` (the data is stored in `t − (1−b)`). -/
def gramTop (b : ℚ) (c1 : List ℚ) : List ℚ := pcomp c1 [b - 1, 1]

/-- `∫_{s>0} max(s,t) v(s) ds` as a polynomial in `t`, valid for `t` in the BOTTOM cell. -/
def gramPhi0 (b : ℚ) (g0 g1 : List ℚ) : List ℚ :=
  padd (psub (0 :: pint g0) (pint (0 :: g0)))
    [pevalQ (pint (0 :: g0)) (1 - b) + pevalQ (pint (0 :: g1)) b
      - pevalQ (pint (0 :: g1)) (1 - b)]

/-- The same, valid for `t` in the TOP cell. -/
def gramPhi1 (b : ℚ) (g0 g1 : List ℚ) : List ℚ :=
  padd (psub (padd (0 :: pint g1) [0, pevalQ (pint g0) (1 - b) - pevalQ (pint g1) (1 - b)])
      (pint (0 :: g1)))
    [pevalQ (pint (0 :: g1)) b]

/-- The out-zone corner `∫_{1−t}^{b}(s+t)v(s)ds` as a polynomial in `t`, valid on the top cell. -/
def gramInner (b : ℚ) (g1 : List ℚ) : List ℚ :=
  padd (psub [pevalQ (pint (0 :: g1)) b] (pcomp (pint (0 :: g1)) [1, -1]))
    (0 :: psub [pevalQ (pint g1) b] (pcomp (pint g1) [1, -1]))

/-- `∫_{t>0} v(t)∫_{s>0} 1_{s+t>1}(s+t)v(s)` — half of `B1`. -/
def gramN (b : ℚ) (g1 : List ℚ) : ℚ := pdefint (pmul g1 (gramInner b g1)) (1 - b) b

/-- `∫_{t>0} v(t)∫_{s>0} max(s,t)v(s)` — a quarter of `K0 + K1`. -/
def gramM (b : ℚ) (g0 g1 : List ℚ) : ℚ :=
  pdefint (pmul g0 (gramPhi0 b g0 g1)) 0 (1 - b)
    + pdefint (pmul g1 (gramPhi1 b g0 g1)) (1 - b) b

/-- `ψ(0) = ∫v²`. -/
def gramI2 (b : ℚ) (g0 g1 : List ℚ) : ℚ :=
  2 * (pdefint (pmul g0 g0) 0 (1 - b) + pdefint (pmul g1 g1) (1 - b) b)

/-- `B1` of a two-cell certificate, in exact ℚ. -/
def gramB1 (b : ℚ) (g1 : List ℚ) : ℚ := 2 * gramN b g1

/-- `B0` of a two-cell certificate, in exact ℚ. -/
def gramB0 (b : ℚ) (g0 g1 : List ℚ) : ℚ :=
  gramI2 b g0 g1 + 4 * gramM b g0 g1 - gramB1 b g1

/-- `gramTop` really is the cell polynomial re-expressed in the global variable. -/
theorem gramTop_eval (b : ℚ) (c1 : List ℚ) (u : ℝ) :
    evalPoly (gramTop b c1) u = evalPoly c1 (u - ((1 - b : ℚ) : ℝ)) := by
  rw [gramTop, evalPoly_pcomp]
  congr 1
  simp only [evalPoly_cons, evalPoly_nil]
  push_cast
  ring

/-- **THE D24 REPLACEMENT, PROVED.** For a TWO-CELL certificate, `B0` and `B1` of its profile
are the exact rationals `gramB0` / `gramB1` computed by §3c's Gram engine.

Everything analytic is inherited from §3b (`B0_add_B1_half`, `B1_half`); what is added here is
the cut at the mesh node and the polynomial FTC. `hxs : xs = [1 − b]` is not a restriction on
the shipped data: `hmesh` forces `1 − b ∈ xs`, and all four shipped certificates have a single
interior node.

Paper §11; RESOLUTIONS D24.
**Rule 17: `1 < lam` and `lam < 2` are supplied by `Cert.one_lt_lam` / `Cert.lam_lt_two`,
i.e. by the certificate's own `hb_lo`/`hb_hi`; no hypothesis compares `lam` with 1.** -/
theorem two_cell_payoff (c : Cert) (hpos : c.NonnegOK) (hmass : c.MassOK)
    (g0 c1 g1 : List ℚ) (hxs : c.xs = [1 - c.b]) (hcoeff : c.coeff = [g0, c1])
    (hg1 : ∀ u : ℝ, evalPoly g1 u = evalPoly c1 (u - ((1 - c.b : ℚ) : ℝ))) :
    B0 c.toFun = ((gramB0 c.b g0 g1 : ℚ) : ℝ) ∧ B1 c.toFun = ((gramB1 c.b g1 : ℚ) : ℝ) := by
  have hblo : (1 : ℝ) < 2 * ((c.b : ℚ) : ℝ) := by
    have h : (1 : ℚ) < 2 * c.b := by linarith [c.hb_lo]
    exact_mod_cast h
  have hbhi : ((c.b : ℚ) : ℝ) < 1 := by exact_mod_cast c.hb_hi
  have ht0 : ((1 - c.b : ℚ) : ℝ) = 1 - ((c.b : ℚ) : ℝ) := by push_cast; ring
  have ht0pos : (0 : ℝ) < ((1 - c.b : ℚ) : ℝ) := by rw [ht0]; linarith
  have ht0b : ((1 - c.b : ℚ) : ℝ) < ((c.b : ℚ) : ℝ) := by rw [ht0]; linarith
  -- the piecewise description of the profile
  have hn0 : c.node 0 = 0 := by simp [Cert.node, Cert.nodes]
  have hn1 : c.node 1 = 1 - c.b := by simp [Cert.node, Cert.nodes, hxs]
  have hn2 : c.node 2 = c.b := by simp [Cert.node, Cert.nodes, hxs]
  have hlen : c.xs.length = 1 := by rw [hxs]; rfl
  have hdec : ∀ u : ℝ, c.toFunNonneg u
      = Set.indicator (Set.Ico (0 : ℝ) ((1 - c.b : ℚ) : ℝ)) (fun x : ℝ => evalPoly g0 x) u
        + Set.indicator (Set.Ico ((1 - c.b : ℚ) : ℝ) ((c.b : ℚ) : ℝ))
            (fun x : ℝ => evalPoly g1 x) u := by
    have e1 : Set.indicator (Set.Ico ((c.node 0 : ℚ) : ℝ) ((c.node 1 : ℚ) : ℝ))
          (fun t : ℝ => evalPoly (c.coeff.getD 0 []) (t - ((c.node 0 : ℚ) : ℝ)))
        = Set.indicator (Set.Ico (0 : ℝ) ((1 - c.b : ℚ) : ℝ)) (fun x : ℝ => evalPoly g0 x) := by
      rw [hn0, hn1, hcoeff]
      simp only [Rat.cast_zero, sub_zero, List.getD_cons_zero]
    have e2 : Set.indicator (Set.Ico ((c.node 1 : ℚ) : ℝ) ((c.node 2 : ℚ) : ℝ))
          (fun t : ℝ => evalPoly (c.coeff.getD 1 []) (t - ((c.node 1 : ℚ) : ℝ)))
        = Set.indicator (Set.Ico ((1 - c.b : ℚ) : ℝ) ((c.b : ℚ) : ℝ))
            (fun x : ℝ => evalPoly g1 x) := by
      rw [hn1, hn2, hcoeff]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      have hfun : (fun t : ℝ => evalPoly c1 (t - ((1 - c.b : ℚ) : ℝ)))
          = fun x : ℝ => evalPoly g1 x := funext fun x => (hg1 x).symm
      rw [hfun]
    intro u
    simp only [Cert.toFunNonneg, hlen, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [e1, e2]
  have hv0 : ∀ u : ℝ, 0 ≤ u → u < ((1 - c.b : ℚ) : ℝ) → c.toFun u = evalPoly g0 u := by
    intro u hu0 hu1
    have hxu : c.toFun u = c.toFunNonneg u := by simp [Cert.toFun, abs_of_nonneg hu0]
    rw [hxu, hdec u, Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hu0, hu1⟩),
      Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hu1))]
    ring
  have hv1 : ∀ u : ℝ, ((1 - c.b : ℚ) : ℝ) ≤ u → u < ((c.b : ℚ) : ℝ) →
      c.toFun u = evalPoly g1 u := by
    intro u hu0 hu1
    have hu0' : (0 : ℝ) ≤ u := le_trans ht0pos.le hu0
    have hxu : c.toFun u = c.toFunNonneg u := by simp [Cert.toFun, abs_of_nonneg hu0']
    rw [hxu, hdec u, Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hu0, hu1⟩),
      Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hu0))]
    ring
  have hv2 : ∀ u : ℝ, ((c.b : ℚ) : ℝ) ≤ u → c.toFun u = 0 := by
    intro u hu
    have hu0' : (0 : ℝ) ≤ u := le_trans (le_of_lt (lt_trans ht0pos ht0b)) hu
    have hxu : c.toFun u = c.toFunNonneg u := by simp [Cert.toFun, abs_of_nonneg hu0']
    rw [hxu, hdec u, Set.indicator_of_notMem (fun h => absurd (h.2.trans ht0b) (not_lt.mpr hu)),
      Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hu))]
    ring
  -- the inner max-kernel integral, bottom cell
  have hPhi0 : ∀ t : ℝ, 0 ≤ t → t ≤ ((1 - c.b : ℚ) : ℝ) →
      ∫ s in Set.Ioi (0 : ℝ), max s t * c.toFun s = evalPoly (gramPhi0 c.b g0 g1) t := by
    intro t hta htb
    have hpt : ∀ x : ℝ, 0 ≤ x → max x t * c.toFun x
        = Set.indicator (Set.Ico (0 : ℝ) t) (fun s : ℝ => t * evalPoly g0 s) x
          + Set.indicator (Set.Ico t ((1 - c.b : ℚ) : ℝ))
              (fun s : ℝ => evalPoly (0 :: g0) s) x
          + Set.indicator (Set.Ico ((1 - c.b : ℚ) : ℝ) ((c.b : ℚ) : ℝ))
              (fun s : ℝ => evalPoly (0 :: g1) s) x := by
      intro x hx
      by_cases hA : x < t
      · rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hx, hA⟩),
          Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hA)),
          Set.indicator_of_notMem
            (fun h => absurd h.1 (not_le.mpr (lt_of_lt_of_le hA htb))),
          hv0 x hx (lt_of_lt_of_le hA htb), max_eq_right hA.le]
        ring
      · rw [not_lt] at hA
        by_cases hB : x < ((1 - c.b : ℚ) : ℝ)
        · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
            Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hA, hB⟩),
            Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hB)),
            hv0 x hx hB, max_eq_left hA, evalPoly_cons]
          push_cast; ring
        · rw [not_lt] at hB
          by_cases hC : x < ((c.b : ℚ) : ℝ)
          · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
              Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hB)),
              Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hB, hC⟩),
              hv1 x hB hC, max_eq_left hA, evalPoly_cons]
            push_cast; ring
          · rw [not_lt] at hC
            rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
              Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hB)),
              Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hC)),
              hv2 x hC]
            ring
    rw [intIoi_split3 (G1 := fun s : ℝ => t * evalPoly g0 s)
        (G2 := fun s : ℝ => evalPoly (0 :: g0) s) (G3 := fun s : ℝ => evalPoly (0 :: g1) s)
        le_rfl hta htb ht0b.le
        (show Continuous fun s : ℝ => t * evalPoly g0 s from
          continuous_const.mul (evalPoly_continuous _))
        (evalPoly_continuous _) (evalPoly_continuous _) hpt,
      intervalIntegral.integral_const_mul, integral_evalPoly_interval,
      integral_evalPoly_interval, integral_evalPoly_interval, evalPoly_pint_zero]
    simp only [gramPhi0, evalPoly_padd, evalPoly_psub, evalPoly_cons, evalPoly_nil]
    push_cast [pevalQ_cast]
    ring
  -- the inner max-kernel integral, top cell
  have hPhi1 : ∀ t : ℝ, ((1 - c.b : ℚ) : ℝ) ≤ t → t ≤ ((c.b : ℚ) : ℝ) →
      ∫ s in Set.Ioi (0 : ℝ), max s t * c.toFun s = evalPoly (gramPhi1 c.b g0 g1) t := by
    intro t hta htb
    have hpt : ∀ x : ℝ, 0 ≤ x → max x t * c.toFun x
        = Set.indicator (Set.Ico (0 : ℝ) ((1 - c.b : ℚ) : ℝ))
              (fun s : ℝ => t * evalPoly g0 s) x
          + Set.indicator (Set.Ico ((1 - c.b : ℚ) : ℝ) t) (fun s : ℝ => t * evalPoly g1 s) x
          + Set.indicator (Set.Ico t ((c.b : ℚ) : ℝ)) (fun s : ℝ => evalPoly (0 :: g1) s) x := by
      intro x hx
      by_cases hA : x < ((1 - c.b : ℚ) : ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hx, hA⟩),
          Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hA)),
          Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr (lt_of_lt_of_le hA hta))),
          hv0 x hx hA, max_eq_right (le_of_lt (lt_of_lt_of_le hA hta))]
        ring
      · rw [not_lt] at hA
        by_cases hB : x < t
        · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
            Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hA, hB⟩),
            Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hB)),
            hv1 x hA (lt_of_lt_of_le hB htb), max_eq_right hB.le]
          ring
        · rw [not_lt] at hB
          by_cases hC : x < ((c.b : ℚ) : ℝ)
          · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
              Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hB)),
              Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hB, hC⟩),
              hv1 x hA hC, max_eq_left hB, evalPoly_cons]
            push_cast; ring
          · rw [not_lt] at hC
            rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
              Set.indicator_of_notMem (fun h => absurd (h.2.trans_le htb) (not_lt.mpr hC)),
              Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hC)),
              hv2 x hC]
            ring
    rw [intIoi_split3 (G1 := fun s : ℝ => t * evalPoly g0 s)
        (G2 := fun s : ℝ => t * evalPoly g1 s) (G3 := fun s : ℝ => evalPoly (0 :: g1) s)
        le_rfl ht0pos.le hta htb
        (show Continuous fun s : ℝ => t * evalPoly g0 s from
          continuous_const.mul (evalPoly_continuous _))
        (show Continuous fun s : ℝ => t * evalPoly g1 s from
          continuous_const.mul (evalPoly_continuous _))
        (evalPoly_continuous _) hpt,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_evalPoly_interval, integral_evalPoly_interval, integral_evalPoly_interval,
      evalPoly_pint_zero]
    simp only [gramPhi1, evalPoly_padd, evalPoly_psub, evalPoly_cons, evalPoly_nil]
    push_cast [pevalQ_cast]
    ring
  -- the outer max-kernel integral
  have hM : ∫ t in Set.Ioi (0 : ℝ), c.toFun t * ∫ s in Set.Ioi (0 : ℝ), max s t * c.toFun s
      = ((gramM c.b g0 g1 : ℚ) : ℝ) := by
    have hpt : ∀ x : ℝ, 0 ≤ x →
        c.toFun x * (∫ s in Set.Ioi (0 : ℝ), max s x * c.toFun s)
        = Set.indicator (Set.Ico (0 : ℝ) ((1 - c.b : ℚ) : ℝ))
            (fun t : ℝ => evalPoly (pmul g0 (gramPhi0 c.b g0 g1)) t) x
          + Set.indicator (Set.Ico ((1 - c.b : ℚ) : ℝ) ((c.b : ℚ) : ℝ))
            (fun t : ℝ => evalPoly (pmul g1 (gramPhi1 c.b g0 g1)) t) x := by
      intro x hx
      by_cases hA : x < ((1 - c.b : ℚ) : ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hx, hA⟩),
          Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hA)),
          hv0 x hx hA, hPhi0 x hx hA.le, evalPoly_pmul]
        ring
      · rw [not_lt] at hA
        by_cases hB : x < ((c.b : ℚ) : ℝ)
        · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
            Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hA, hB⟩),
            hv1 x hA hB, hPhi1 x hA hB.le, evalPoly_pmul]
          ring
        · rw [not_lt] at hB
          rw [Set.indicator_of_notMem
              (fun h => absurd h.2 (not_lt.mpr (le_trans ht0b.le hB))),
            Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hB)), hv2 x hB]
          ring
    rw [intIoi_split2 (G1 := fun t : ℝ => evalPoly (pmul g0 (gramPhi0 c.b g0 g1)) t)
        (G2 := fun t : ℝ => evalPoly (pmul g1 (gramPhi1 c.b g0 g1)) t)
        le_rfl ht0pos.le ht0b.le (evalPoly_continuous _) (evalPoly_continuous _)
        hpt, integral_evalPoly_Q0, integral_evalPoly_Q]
    simp only [gramM]
    push_cast
    ring
  -- the L² term
  have hI2 : ∫ t, c.toFun t * c.toFun t = ((gramI2 c.b g0 g1 : ℚ) : ℝ) := by
    have hpt : ∀ x : ℝ, 0 ≤ x → c.toFunNonneg x * c.toFunNonneg x
        = Set.indicator (Set.Ico (0 : ℝ) ((1 - c.b : ℚ) : ℝ))
            (fun t : ℝ => evalPoly (pmul g0 g0) t) x
          + Set.indicator (Set.Ico ((1 - c.b : ℚ) : ℝ) ((c.b : ℚ) : ℝ))
            (fun t : ℝ => evalPoly (pmul g1 g1) t) x := by
      intro x hx
      have hxx : c.toFunNonneg x = c.toFun x := by simp [Cert.toFun, abs_of_nonneg hx]
      rw [hxx]
      by_cases hA : x < ((1 - c.b : ℚ) : ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hx, hA⟩),
          Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hA)),
          hv0 x hx hA, evalPoly_pmul]
        ring
      · rw [not_lt] at hA
        by_cases hB : x < ((c.b : ℚ) : ℝ)
        · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
            Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hA, hB⟩), hv1 x hA hB, evalPoly_pmul]
          ring
        · rw [not_lt] at hB
          rw [Set.indicator_of_notMem
              (fun h => absurd h.2 (not_lt.mpr (le_trans ht0b.le hB))),
            Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hB)), hv2 x hB]
          ring
    calc ∫ t, c.toFun t * c.toFun t
        = ∫ t : ℝ, (fun u : ℝ => c.toFunNonneg u * c.toFunNonneg u) |t| := rfl
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), c.toFunNonneg x * c.toFunNonneg x :=
          integral_comp_abs (f := fun u : ℝ => c.toFunNonneg u * c.toFunNonneg u)
      _ = ((gramI2 c.b g0 g1 : ℚ) : ℝ) := by
          rw [intIoi_split2 (G1 := fun t : ℝ => evalPoly (pmul g0 g0) t)
              (G2 := fun t : ℝ => evalPoly (pmul g1 g1) t)
              le_rfl ht0pos.le ht0b.le (evalPoly_continuous _)
              (evalPoly_continuous _) hpt, integral_evalPoly_Q0, integral_evalPoly_Q]
          simp only [gramI2]
          push_cast
          ring
  -- the out-zone inner integral
  have hOut0 : ∀ t : ℝ, 0 ≤ t → t ≤ ((1 - c.b : ℚ) : ℝ) →
      ∫ s in Set.Ioi (0 : ℝ), (if 1 < s + t then s + t else 0) * c.toFun s = 0 := by
    intro t hta htb
    rw [ht0] at htb
    have hz : ∀ s ∈ Set.Ioi (0 : ℝ), (if 1 < s + t then s + t else 0) * c.toFun s = 0 := by
      intro s _
      by_cases h : 1 < s + t
      · have hbs : ((c.b : ℚ) : ℝ) ≤ s := by linarith
        rw [if_pos h, hv2 s hbs, mul_zero]
      · rw [if_neg h, zero_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hz, integral_zero]
  have hOut1 : ∀ t : ℝ, ((1 - c.b : ℚ) : ℝ) ≤ t → t ≤ ((c.b : ℚ) : ℝ) →
      ∫ s in Set.Ioi (0 : ℝ), (if 1 < s + t then s + t else 0) * c.toFun s
        = evalPoly (gramInner c.b g1) t := by
    intro t hta htb
    rw [ht0] at hta
    have hp : (0 : ℝ) ≤ 1 - t := by linarith
    have hpq : 1 - t ≤ ((c.b : ℚ) : ℝ) := by linarith
    have hpt : ∀ x : ℝ, 0 ≤ x → (if 1 < x + t then x + t else 0) * c.toFun x
        = Set.indicator (Set.Ioo (1 - t) ((c.b : ℚ) : ℝ))
            (fun s : ℝ => evalPoly (0 :: g1) s + t * evalPoly g1 s) x := by
      intro x hx
      by_cases hA : 1 - t < x ∧ x < ((c.b : ℚ) : ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr hA), if_pos (by linarith [hA.1]),
          hv1 x (by rw [ht0]; linarith [hA.1]) hA.2, evalPoly_cons]
        push_cast; ring
      · rw [Set.indicator_of_notMem (fun h => hA (Set.mem_Ioo.mp h))]
        rcases not_and_or.mp hA with h | h
        · rw [not_lt] at h
          rw [if_neg (by linarith), zero_mul]
        · rw [not_lt] at h
          rw [hv2 x h, mul_zero]
    rw [intIoi_Ioo (G := fun s : ℝ => evalPoly (0 :: g1) s + t * evalPoly g1 s) hp hpq
        (show Continuous fun s : ℝ => evalPoly (0 :: g1) s + t * evalPoly g1 s from
          (evalPoly_continuous _).add (continuous_const.mul (evalPoly_continuous _))) hpt,
      intervalIntegral.integral_add ((evalPoly_continuous _).intervalIntegrable _ _)
        (show IntervalIntegrable (fun s : ℝ => t * evalPoly g1 s) _ _ _ from
          (continuous_const.mul (evalPoly_continuous _)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_evalPoly_interval,
      integral_evalPoly_interval]
    simp only [gramInner, evalPoly_padd, evalPoly_psub, evalPoly_cons, evalPoly_nil,
      evalPoly_comp_one_sub]
    push_cast [pevalQ_cast]
    ring
  -- the out-zone outer integral
  have hN : ∫ t in Set.Ioi (0 : ℝ), c.toFun t
        * ∫ s in Set.Ioi (0 : ℝ), (if 1 < s + t then s + t else 0) * c.toFun s
      = ((gramN c.b g1 : ℚ) : ℝ) := by
    have hpt : ∀ x : ℝ, 0 ≤ x →
        c.toFun x * (∫ s in Set.Ioi (0 : ℝ), (if 1 < s + x then s + x else 0) * c.toFun s)
        = Set.indicator (Set.Ico (0 : ℝ) ((1 - c.b : ℚ) : ℝ)) (fun _ : ℝ => (0 : ℝ)) x
          + Set.indicator (Set.Ico ((1 - c.b : ℚ) : ℝ) ((c.b : ℚ) : ℝ))
            (fun t : ℝ => evalPoly (pmul g1 (gramInner c.b g1)) t) x := by
      intro x hx
      by_cases hA : x < ((1 - c.b : ℚ) : ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hx, hA⟩),
          Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hA)),
          hOut0 x hx hA.le]
        ring
      · rw [not_lt] at hA
        by_cases hB : x < ((c.b : ℚ) : ℝ)
        · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hA)),
            Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hA, hB⟩),
            hv1 x hA hB, hOut1 x hA hB.le, evalPoly_pmul]
          ring
        · rw [not_lt] at hB
          rw [Set.indicator_of_notMem
              (fun h => absurd h.2 (not_lt.mpr (le_trans ht0b.le hB))),
            Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hB)), hv2 x hB]
          ring
    rw [intIoi_split2 (G1 := fun _ : ℝ => (0 : ℝ))
        (G2 := fun t : ℝ => evalPoly (pmul g1 (gramInner c.b g1)) t)
        le_rfl ht0pos.le ht0b.le continuous_const (evalPoly_continuous _) hpt,
      integral_evalPoly_Q]
    simp [gramN]
  -- assembly
  have hadm := c.admissible hpos hmass
  have hlam0 : (0 : ℝ) ≤ ((c.lam : ℚ) : ℝ) := by linarith [c.one_lt_lam]
  have hB1 : B1 c.toFun = ((gramB1 c.b g1 : ℚ) : ℝ) := by
    rw [B1_half hadm hlam0 c.lam_lt_two c.toFun_even, hN]
    simp only [gramB1]
    push_cast
    ring
  refine ⟨?_, hB1⟩
  have hsum := B0_add_B1_half hadm hlam0 c.toFun_even
  rw [hI2, hM, hB1] at hsum
  have hfin : B0 c.toFun = ((gramI2 c.b g0 g1 : ℚ) : ℝ) + 4 * ((gramM c.b g0 g1 : ℚ) : ℝ)
      - ((gramB1 c.b g1 : ℚ) : ℝ) := by linarith
  rw [hfin]
  simp only [gramB0]
  push_cast
  ring

/-- `two_cell_payoff` with the top-cell polynomial supplied by `gramTop`: the form every shipped
certificate is instantiated at. -/
theorem two_cell_payoff' (c : Cert) (hpos : c.NonnegOK) (hmass : c.MassOK)
    (g0 c1 : List ℚ) (hxs : c.xs = [1 - c.b]) (hcoeff : c.coeff = [g0, c1]) :
    B0 c.toFun = ((gramB0 c.b g0 (gramTop c.b c1) : ℚ) : ℝ) ∧
      B1 c.toFun = ((gramB1 c.b (gramTop c.b c1) : ℚ) : ℝ) :=
  two_cell_payoff c hpos hmass g0 c1 (gramTop c.b c1) hxs hcoeff (gramTop_eval c.b c1)

/-- **The soundness theorem of the payoff route.** Everything downstream is one application of
this with a concrete `Cert`, a rational `Cbar ≥ C` (from Mathlib's π bounds), and a single
rational comparison `hnum`.

Paper §11 + §3 Prop. 3.1.
Depends on: `Cert.admissible`, `Cert.B0Eq`, `Cert.B1Eq`, `B_eq_B0_add_C_mul_B1`,
`B1_nonneg`.
**Rule 17: the conclusion asserts `Admissible (c.lam) …` with `1 < c.lam` available from
`Cert.one_lt_lam`. No `lam ≤ 1` hypothesis exists or may be added.** -/
theorem payoff_of_cert (c : Cert) (hpos : c.NonnegOK) (hmass : c.MassOK)
    (hB0 : Cert.B0Eq c) (hB1eq : Cert.B1Eq c)
    (C : ℝ) (Cbar Pc : ℚ) (hCbar : 0 ≤ Cbar) (hC : C ≤ ((Cbar : ℚ) : ℝ))
    (hnum : c.B0q + Cbar * c.B1q ≤ 2 - Pc) :
    Admissible ((c.lam : ℚ) : ℝ) c.toFun ∧ B C c.toFun ≤ 2 - ((Pc : ℚ) : ℝ) := by
  have hadm := c.admissible hpos hmass
  refine ⟨hadm, ?_⟩
  have hB1 : 0 ≤ B1 c.toFun := B1_nonneg hadm
  calc B C c.toFun = B0 c.toFun + C * B1 c.toFun := B_eq_B0_add_C_mul_B1 C hadm
    _ ≤ B0 c.toFun + ((Cbar : ℚ) : ℝ) * B1 c.toFun := by
        nlinarith [mul_le_mul_of_nonneg_right hC hB1]
    _ = ((c.B0q + Cbar * c.B1q : ℚ) : ℝ) := by
        rw [hB0 hpos hmass, hB1eq hpos hmass]; push_cast; ring
    _ ≤ ((2 - Pc : ℚ) : ℝ) := by exact_mod_cast hnum
    _ = 2 - ((Pc : ℚ) : ℝ) := by push_cast; ring

/-- **The soundness theorem in the form the four shipped certificates actually use.** Identical
to `payoff_of_cert` except that the exact-ℚ values of `B0` and `B1` are supplied as HYPOTHESES
rather than read off the symbolic engine. §3c's `two_cell_payoff'` discharges those hypotheses
for every two-cell certificate, so this route needs no such hypothesis, where `payoff_of_cert` takes
`Cert.B0Eq` / `Cert.B1Eq` as ones. Both are kept: `payoff_of_cert` is the general statement,
this is the one Theorem 1's four constants are proved through.

Paper §11 + §3 Prop. 3.1; RESOLUTIONS D24.
Depends on: `Cert.admissible`, `B_eq_B0_add_C_mul_B1`, `B1_nonneg`.
**Rule 17: unchanged from `payoff_of_cert` — the conclusion is at `lam = c.lam > 1`
(`Cert.one_lt_lam`); no hypothesis compares `lam` with 1.** -/
theorem payoff_of_cert_num (c : Cert) (hpos : c.NonnegOK) (hmass : c.MassOK) (b0 b1 : ℚ)
    (hb0 : B0 c.toFun = ((b0 : ℚ) : ℝ)) (hb1 : B1 c.toFun = ((b1 : ℚ) : ℝ))
    (C : ℝ) (Cbar Pc : ℚ) (hCbar : 0 ≤ Cbar) (hC : C ≤ ((Cbar : ℚ) : ℝ))
    (hnum : b0 + Cbar * b1 ≤ 2 - Pc) :
    Admissible ((c.lam : ℚ) : ℝ) c.toFun ∧ B C c.toFun ≤ 2 - ((Pc : ℚ) : ℝ) := by
  have hadm := c.admissible hpos hmass
  refine ⟨hadm, ?_⟩
  have hB1 : 0 ≤ B1 c.toFun := B1_nonneg hadm
  calc B C c.toFun = B0 c.toFun + C * B1 c.toFun := B_eq_B0_add_C_mul_B1 C hadm
    _ ≤ B0 c.toFun + ((Cbar : ℚ) : ℝ) * B1 c.toFun := by
        nlinarith [mul_le_mul_of_nonneg_right hC hB1]
    _ = ((b0 + Cbar * b1 : ℚ) : ℝ) := by rw [hb0, hb1]; push_cast; ring
    _ ≤ ((2 - Pc : ℚ) : ℝ) := by exact_mod_cast hnum
    _ = 2 - ((Pc : ℚ) : ℝ) := by push_cast; ring

/-! ## 4. The shipped constants (R-A5): `Pcert` here, `ZetaQ.Pconst` in `Defs` -/

/-- The digit count the certificate ships at `C = π⁴/18`: `Pcert_qQ = 0.7212`.
HANDOVER §5: "the payoff route ships ≥ 0.7212 at the profile's digit count".

**This is NOT the paper's `P = 0.7212835668`** (`ZetaQ.Pconst`, L689). The
headroom is `8.4×10⁻⁵`.

**Correction, see §5a below.** This docstring used to say that
"the binding cost is the RATIONAL SUPPORT WIDTH (`b = 5/8` against `b* = 0.6253660758`, a
second-order loss `≲ 10⁻⁶`), not the polynomial approximation". That is WRONG, and
`payoff_feasible_qQ_sharp` shows it in Lean: the width loss is `+9.8·10⁻¹⁰` and the degree-4
truncation `+1.7·10⁻¹⁰`, while the π-bound slack from `Real.pi_lt_d6` is `+2.0·10⁻⁸`. Sharpening
`Cbar` ALONE — same `certQQ`, same `B0q`, same `B1q` — takes the certified constant from
`0.7212` to `0.7212835656`.
Paper §11. Rule 17: no parameters. -/
def Pcert_qQ : ℚ := 7212 / 10000

/-- Corollary 2's certified constant, `C = 2π⁴/27`. Paper's value `0.7099167448`
(`ZetaQ.PconstDyadic`). Rule 17: no parameters. -/
def Pcert_dyad : ℚ := 7099 / 10000

/-- Corollary 3's certified constant (even, resp. odd, DYADIC), `C = 4π⁴/27`. Paper's value
`0.6919434301` (`ZetaQ.PconstEvenDyadic`, `λ* = 1.1015998422`).
This value has NO shipped script anchor; it was re-verified off-line as
`0.691943430126`. Rule 17: no parameters. -/
def Pcert_even : ℚ := 6919 / 10000

/-- Corollary 3's certified constant (even, resp. odd) over `q ≤ Q`, `C = π⁴/9`. Paper's value
`0.6980745436`.
Rule 17: no parameters. -/
def Pcert_evenQ : ℚ := 6980 / 10000

/-- `Pcert = 0.7212` as a real — the constant every downstream `ZetaQ` statement may use.
**Read the R-A5 block in this file's header before using `ZetaQ.Pconst` instead.**

Paper §11. Rule 17: no parameters. -/
def Pcert : ℝ := ((Pcert_qQ : ℚ) : ℝ)

/-- The paper's value `0.6980745436` for the even/odd family over `q ≤ Q` at `C = π⁴/9`.
The three siblings (`Pconst`, `PconstDyadic`, `PconstEvenDyadic`) are frozen
in `ZetaQ/Defs.lean`; this fourth one is not, so it is defined here.
It belongs in `Defs.lean` at the next freeze.
Paper §1.1. Rule 17: no parameters. -/
def PconstEvenQ : ℝ := 0.6980745436

/-- **The weakening, made checkable.** `Pcert < ZetaQ.Pconst`: what Lean ships is strictly
weaker than what the paper states.

Paper §11 (L689).
Depends on: `Pcert`, `ZetaQ.Pconst`. Rule 17: no parameters. -/
theorem Pcert_lt_Pconst : Pcert < ZetaQ.Pconst := by
  simp only [Pcert, Pcert_qQ, ZetaQ.Pconst]
  norm_num

/-! ## 5. The shipped certificate instance and the four feasibility statements

The recommended headline instantiation: 3 cells, `b = 5/8`, `λ_cert = 5/4`,
`t₀ = 1 − b = 3/8`. Sumset `{0, ±1/4, ±3/4, ±1, ±5/4}` — 8 ψ-cells with `α = 1` a boundary. -/

/-- The certificate data at `C = π⁴/18`. `b = 5/8`, so `λ_cert = 5/4 ∈ (1,2)` and
`t₀ = 1 − b = 3/8` is BOTH a mesh point and the true bulk/edge junction of `v*` — so no
polynomial piece straddles the C¹ kink, and `α = 1` is automatically a ψ-cell boundary
(`hmesh` is what delivers that, structurally).

GENERATED off-line by an exact-rational certificate generator, which is not shipped; the
loss budget and the eight validation gates it applies are described below. The profile was
fitted to the shipped
high-precision solution, rationalised, then rescaled by the reciprocal of its exact rational
mass so that `MassOK` holds exactly rather than approximately.

**Two cells at degree 4, not the three cells at degree 12/8 first anticipated.** The
reason is worth recording: `B` is *stationary* at the optimum, so a profile agreeing with
`v*` only to `sup|v_cert − v*| ≈ 6.3·10⁻⁵` still reproduces `B` to `1.7·10⁻¹⁰`. A degree
sweep (deg 4/6/8/10 × 2/4/5 cells) moved the certified value only in the 10th decimal — see
so the smallest data that clears the target is shipped.

Paper §11.
Rule 17: `b = 5/8 > 1/2`, i.e. `λ = 5/4 > 1` — the C-zone is nonempty. It is a `Cert` FIELD
(`hb_lo`), i.e. certificate data, not a hypothesis anyone can weaken. -/
def certQQ : Cert where
  b     := (5 / 8 : ℚ)
  xs    := [(3 / 8 : ℚ)]
  deg   := 4
  coeff :=
    [[ (18785766097 / 18432000000 : ℚ), (3 / 100000 : ℚ), (-20393 / 20000 : ℚ),
       (287 / 100000 : ℚ), (16341 / 100000 : ℚ) ],
     [ (43957 / 50000 : ℚ), (-36551 / 50000 : ℚ), (-164309 / 12500 : ℚ),
       (40159 / 12500 : ℚ), (1971979 / 100000 : ℚ) ]]
  hb_lo      := by norm_num
  hb_hi      := by norm_num
  hmesh      := by norm_num
  hxs_mem    := by norm_num
  hxs_sorted := by norm_num
  hcoeff_len := by rfl
  hdeg       := by norm_num

/-- **Gate 6: the exact mass identity `2·∫₀^b v = 1` holds in ℚ.**
Arranged by the generator: the coefficients are rounded to the grid `1/10⁵` and then `c[0][0]`
alone is adjusted by `(1 − m)/(2h₀)`, so the identity closes EXACTLY, not approximately.

(`by decide` is NOT available: the file is `noncomputable` and, more to the point, `Rat`
arithmetic does not reduce in the kernel — `Rat.normalize` goes through `Nat.gcd`.)
Rule 17: no parameters. -/
theorem certQQ_MassOK : certQQ.MassOK := by
  norm_num [Cert.MassOK, Cert.massHalf, Cert.massPiece, Cert.node, Cert.nodes, certQQ,
    Finset.sum_range_succ]

/-- **Gate 5: the Bernstein sign certificate.** All ten Bernstein
coefficients of the two cells are `≥ 0` (in fact strictly positive; the worst is
`β₄` of cell 1 `= v(b⁻) = 52971/25600000 ≈ +2.07·10⁻³`), hence `v ≥ 0` on `[0, b]` and, by
evenness, everywhere. No subdivision was required.

Note `v(b⁻) > 0`: the free boundary sits at `b* = 0.62536608 > 5/8`, so at `b = 5/8` the
optimal profile has NOT yet decayed to zero, and the `(b − t)·p(t)` trick
is inapplicable here (it would force `v(b) = 0`) and was not used.
Rule 17: no parameters. -/
theorem certQQ_NonnegOK : certQQ.NonnegOK := by
  norm_num [Cert.NonnegOK, Cert.nonnegCheck, Cert.node, Cert.nodes, certQQ]
  have hc2 : Nat.choose 4 2 = 6 := by decide
  intro i hi k hk
  interval_cases i <;> interval_cases k <;>
    norm_num [Cert.bernsteinCoeff, Finset.sum_range_succ, hc2]

/-- The exact `B₀` of `certQQ`, computed in ℚ by the certificate generator.
`B₀ = ψ(0) + 2∫₀¹ α ψ(α) dα`. Recorded as a literal so the feasibility check is a decidable
ℚ inequality; `Cert.B0q certQQ = B0_certQQ` is the engine's obligation. -/
def B0_certQQ : ℚ := 11478597963771543793577 / 9301288550400000000000

/-- The exact `B₁` of `certQQ`: `B₁ = 2∫₁^{2b} α ψ(α) dα`, the C-penalised zone. Nonnegative,
which is what makes replacing `C` by a rational UPPER bound sound. -/
def B1_certQQ : ℚ := 35956728892014883151 / 4359979008000000000000

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- **THE ENGINE, RUN ON THE SHIPPED CERTIFICATE.** The symbolic ℚ convolution engine of §3a
returns exactly the two rationals the generator computed — this is the Lean side
of the generator's own check, and it is what turns `B0_certQQ` / `B1_certQQ` from recorded literals
into computed values.

The intermediate quantities agree too (checked while developing, and recoverable by splitting
this statement): `ψ(0) = 282672272551404238591/317089382400000000000`,
`K0 = 9560633906791058384723/27903865651200000000000`,
`K1 = 35956728892014883151/4359979008000000000000`.

Stated as ONE equation of pairs on purpose: `B0q` and `B1q` share the cell blocks, and a
single `norm_num` call shares its cache across both components, halving the cost.

Paper §11.
Rule 17: `2 * certQQ.b = 5/4 > 1`; no comparison with 1 occurs. -/
theorem certQQ_parts : Cert.payoffPartsQ certQQ = (B0_certQQ, B1_certQQ) := by
  norm_num (maxSteps := 100000000) [Cert.payoffPartsQ, Cert.certPieces, Cert.piecesFrom,
    Cert.nodes, certQQ, B0_certQQ, B1_certQQ, allPsi, pairPsi, pairCells, convPair, psiAtZero,
    sumInt, intCell, p2mul, p2add, p2sub, p2evalT, pcomp, pmul, padd, pscal, psub, pint,
    pintAux, pevalQ, pdefint, sortedNub, sortedIns, pairsAdj, List.replicate]

/-- `Cert.B0q certQQ = B0_certQQ` — the engine's obligation, discharged. -/
theorem B0q_certQQ : Cert.B0q certQQ = B0_certQQ := by
  simp only [Cert.B0q, certQQ_parts]

/-- `Cert.B1q certQQ = B1_certQQ` — the engine's obligation, discharged. -/
theorem B1q_certQQ : Cert.B1q certQQ = B1_certQQ := by
  simp only [Cert.B1q, certQQ_parts]

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- **THE REAL-VALUED `B0` AND `B1` OF `certQQ`, EVALUATED — this is what replaces
`Cert.B0Eq` / `Cert.B1Eq` for the headline certificate.** §3c's `two_cell_payoff'` carries the
analytic reduction of §3b down to the two mesh cells; what is left is the exact-ℚ arithmetic,
done here by `norm_num`.

Note what this is NOT: it is not the symbolic-convolution engine of §3a. It is an independent
Gram-block computation, and it lands on the SAME two rationals `certQQ_parts` computes — a
Lean-internal cross-check of the engine against a different algorithm, on top of the four
external ones recorded in `certQQ_parts`.

Paper §11; RESOLUTIONS D24.
Depends on: `two_cell_payoff'`, `certQQ_NonnegOK`, `certQQ_MassOK`.
Rule 17: `2 * certQQ.b = 5/4 > 1`; no comparison with 1 occurs. -/
theorem B0B1_certQQ :
    B0 certQQ.toFun = ((B0_certQQ : ℚ) : ℝ) ∧ B1 certQQ.toFun = ((B1_certQQ : ℚ) : ℝ) := by
  obtain ⟨h0, h1⟩ := two_cell_payoff' certQQ certQQ_NonnegOK certQQ_MassOK
    (certQQ.coeff.getD 0 []) (certQQ.coeff.getD 1 []) (by norm_num [certQQ]) (by rfl)
  refine ⟨h0.trans ?_, h1.trans ?_⟩ <;>
  · norm_num (maxSteps := 100000000) [certQQ, B0_certQQ, B1_certQQ, gramB0, gramB1, gramI2,
      gramM, gramN, gramTop, gramPhi0, gramPhi1, gramInner, pdefint, pevalQ, pint, pintAux,
      pmul, padd, pscal, psub, pcomp]

/-- The single rational comparison the whole payoff route reduces to:
`B0q + Cbar·B1q ≤ 2 − Pcert` at the crude Lean-provable `Cbar = 5412/1000 ≥ π⁴/18` of
`C_qQ_le`. Slack `+8.04·10⁻⁵`. -/
theorem certQQ_num :
    Cert.B0q certQQ + (5412 / 1000 : ℚ) * Cert.B1q certQQ ≤ 2 - Pcert_qQ := by
  rw [B0q_certQQ, B1q_certQQ]
  norm_num [B0_certQQ, B1_certQQ, Pcert_qQ]

/-- The rational π-bound the route needs: `π⁴/18 ≤ 5.412`, from Mathlib's `Real.pi_lt_3141593`
raised to the fourth power. (`π⁴/18 = 5.4116161686…`.)

Paper §2.2 (`C = π⁴/18`).1(6). Depends on: Mathlib `Real.pi_lt_3141593`. Rule 17: no bandwidth. -/
theorem C_qQ_le : Real.pi ^ 4 / 18 ≤ ((5412 / 1000 : ℚ) : ℝ) := by
  have h4 : Real.pi ^ 4 ≤ (3.141593 : ℝ) ^ 4 := by
    gcongr
    exact Real.pi_lt_d6.le
  have h5 : (3.141593 : ℝ) ^ 4 ≤ 97.40914 := by norm_num
  push_cast
  linarith

/-- `1 < 5/4` — the Rule-17 audit point for the headline statement, stated so the audit does
not have to trust a numeral.

Rule 17: **this IS the Rule-17 content of `payoff_feasible_qQ`.** -/
theorem one_lt_lamCert : (1 : ℝ) < 5 / 4 := by norm_num

/-- **§11 AT `C = π⁴/18`, IN FEASIBILITY FORM — THE HEADLINE STATEMENT THEOREM 1 CONSUMES.**

There is an admissible profile at bandwidth `λ = 5/4 ∈ (1,2)` whose payoff functional is at
most `2 − 0.7212`; equivalently `κ_C ≤ 2 − Pcert`, hence Theorem 1's constant
`2 − κ_C ≥ 0.7212`.

Paper §11 (L689) via §3 Prop. 3.1.
Depends on: `payoff_of_cert`, `certQQ`, `C_qQ_le`.
**Rule 17: the bandwidth is the LITERAL `5/4 > 1` (see `one_lt_lamCert`).** At `λ ≤ 1` the
C-zone `1 < |α| ≤ λ` is empty, `B` collapses to Montgomery–Taylor, and this statement would
still compile while asserting nothing about §11's gain. `π⁴/18 = ZetaQ.Cfam`. -/
theorem payoff_feasible_qQ :
    ∃ v : ℝ → ℝ, Admissible ((5 : ℝ) / 4) v ∧
      B (Real.pi ^ 4 / 18) v ≤ 2 - ((Pcert_qQ : ℚ) : ℝ) := by
  obtain ⟨hadm, hB⟩ :=
    payoff_of_cert_num certQQ certQQ_NonnegOK certQQ_MassOK B0_certQQ B1_certQQ
      B0B1_certQQ.1 B0B1_certQQ.2 (Real.pi ^ 4 / 18) (5412 / 1000)
      Pcert_qQ (by norm_num) C_qQ_le (by norm_num [B0_certQQ, B1_certQQ, Pcert_qQ])
  refine ⟨certQQ.toFun, ?_, hB⟩
  have hl : ((certQQ.lam : ℚ) : ℝ) = (5 : ℝ) / 4 := by
    norm_num [Cert.lam, certQQ]
  rwa [hl] at hadm

/-! ### 5a. How far this certificate actually reaches

The binding cost on the certified digit count is the RATIONAL
UPPER BOUND ON `π⁴/18`, not the support width `b = 5/8` and not the polynomial degree —
contradicting the `Pcert_qQ` docstring above, which names the width. That
is confirmed here IN LEAN: replacing `Real.pi_lt_d6` by Mathlib's own `Real.pi_lt_d20` in the
one rational comparison, and changing NOTHING else — same `certQQ`, same `B0q`, same `B1q` —
moves the certified constant from `0.7212` to `0.7212835656`, i.e. from 4 digits to 10, at
the cost of one longer numeral. The π bound then stops binding altogether: what remains is
`+1.2·10⁻⁹`, the `b = 5/8` width loss plus the degree-4 truncation, exactly the two terms
the loss budget predicts.

`Pcert_qQ` is nevertheless left at `7212/10000`: it is the paper's shipped digit count and is
frozen. This section records what is available, it does not change what is shipped. -/

/-- `π⁴/18 ≤ 3.14159265358979323847⁴/18`, from Mathlib's 20-digit bound `Real.pi_lt_d20`. -/
theorem C_qQ_le_sharp :
    Real.pi ^ 4 / 18 ≤ ((314159265358979323847 ^ 4 / (18 * 10 ^ 80) : ℚ) : ℝ) := by
  have h4 : Real.pi ^ 4 ≤ (3.14159265358979323847 : ℝ) ^ 4 := by
    gcongr
    exact Real.pi_lt_d20.le
  have h5 : ((314159265358979323847 ^ 4 / (18 * 10 ^ 80) : ℚ) : ℝ)
      = (3.14159265358979323847 : ℝ) ^ 4 / 18 := by
    push_cast
    norm_num
  rw [h5]
  linarith

/-- The same comparison as `certQQ_num`, at ten digits. -/
theorem certQQ_num_sharp :
    Cert.B0q certQQ + (314159265358979323847 ^ 4 / (18 * 10 ^ 80) : ℚ) * Cert.B1q certQQ
      ≤ 2 - 7212835656 / 10 ^ 10 := by
  rw [B0q_certQQ, B1q_certQQ]
  norm_num [B0_certQQ, B1_certQQ]

/-- **The same certificate, at ten digits: `P ≥ 0.7212835656`.** Compare the paper's
(unformalised, minimality-dependent) `0.7212835668`: the gap is `1.2·10⁻⁹`, which is the
width-plus-truncation loss and NOT the π bound. Recorded, not shipped — every downstream
`ZetaQ` statement uses `Pcert_qQ = 0.7212`. -/
theorem payoff_feasible_qQ_sharp :
    ∃ v : ℝ → ℝ, Admissible ((5 : ℝ) / 4) v ∧
      B (Real.pi ^ 4 / 18) v ≤ 2 - ((7212835656 / 10 ^ 10 : ℚ) : ℝ) := by
  obtain ⟨hadm, hB⟩ :=
    payoff_of_cert_num certQQ certQQ_NonnegOK certQQ_MassOK B0_certQQ B1_certQQ
      B0B1_certQQ.1 B0B1_certQQ.2 (Real.pi ^ 4 / 18)
      (314159265358979323847 ^ 4 / (18 * 10 ^ 80)) (7212835656 / 10 ^ 10)
      (by norm_num) C_qQ_le_sharp (by norm_num [B0_certQQ, B1_certQQ])
  refine ⟨certQQ.toFun, ?_, hB⟩
  have hl : ((certQQ.lam : ℚ) : ℝ) = (5 : ℝ) / 4 := by
    norm_num [Cert.lam, certQQ]
  rwa [hl] at hadm

/-- **The certificate data for Corollary 2**, `C = 2π⁴/27`. `b = 59/100`, so
`λ_cert = 59/50 ∈ (1,2)` and `t₀ = 1 − b = 41/100` is the mesh point that puts `α = 1` on a
ψ-cell boundary. Two cells, degree 2.

GENERATED the same way as `certQQ` (the generator's exact-ℚ Gram/convolution
engine, solved in ℚ, rounded to the grid `1/10⁵`, mass repaired exactly), then re-verified by
the Lean engine (`certDyad_parts`).

**Why `b` sits BELOW the paper's free boundary `b* = 0.5965790605` and not above it.** At
`b > b*` the finite-dimensional optimum dips NEGATIVE near the edge and the Bernstein check
fails — the natural first try `b = 3/5` does exactly that (worst `β = −2.4·10⁻²`), and the
`B` it reports is below the true CONSTRAINED minimum, i.e. it is not a feasible point at all.
`b = 59/100 < b*` keeps `v ≥ 0` with margin (worst `β = +3.7·10⁻²`). This is the certificate
route's own guard rail doing its job.
Rule 17: `b = 59/100 > 1/2`, i.e. `λ > 1` — the C-zone is nonempty. -/
def certDyad : Cert where
  b     := (59 / 100 : ℚ)
  xs    := [(41 / 100 : ℚ)]
  deg   := 2
  coeff :=
    [[ (32395943 / 31250000 : ℚ), (-1073 / 100000 : ℚ), (-49353 / 50000 : ℚ) ],
     [ (87593 / 100000 : ℚ), (-40729 / 25000 : ℚ), (-1683721 / 100000 : ℚ) ]]
  hb_lo      := by norm_num
  hb_hi      := by norm_num
  hmesh      := by norm_num
  hxs_mem    := by norm_num
  hxs_sorted := by norm_num
  hcoeff_len := by rfl
  hdeg       := by norm_num

/-- Exact mass identity for `certDyad`. -/
theorem certDyad_MassOK : certDyad.MassOK := by
  norm_num [Cert.MassOK, Cert.massHalf, Cert.massPiece, Cert.node, Cert.nodes, certDyad,
    Finset.sum_range_succ]

/-- Bernstein sign certificate for `certDyad` (worst coefficient `+3.7·10⁻²`). -/
theorem certDyad_NonnegOK : certDyad.NonnegOK := by
  norm_num [Cert.NonnegOK, Cert.nonnegCheck, Cert.node, Cert.nodes, certDyad]
  intro i hi k hk
  interval_cases i <;> interval_cases k <;>
    norm_num [Cert.bernsteinCoeff, Finset.sum_range_succ]

/-- `B₀` of `certDyad`. -/
def B0_certDyad : ℚ := 8240318666139222431280719 / 6562500000000000000000000

/-- `B₁` of `certDyad`. -/
def B1_certDyad : ℚ := 2609482595936963580801 / 546875000000000000000000

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- The engine, run on `certDyad`. -/
theorem certDyad_parts : Cert.payoffPartsQ certDyad = (B0_certDyad, B1_certDyad) := by
  norm_num (maxSteps := 100000000) [Cert.payoffPartsQ, Cert.certPieces, Cert.piecesFrom,
    Cert.nodes, certDyad, B0_certDyad, B1_certDyad, allPsi, pairPsi, pairCells, convPair, psiAtZero,
    sumInt, intCell, p2mul, p2add, p2sub, p2evalT, pcomp, pmul, padd, pscal, psub, pint,
    pintAux, pevalQ, pdefint, sortedNub, sortedIns, pairsAdj, List.replicate]

/-- `2π⁴/27 ≤ 2·3.141593⁴/27`, from `Real.pi_lt_d6`. -/
theorem C_dyad_le :
    2 * Real.pi ^ 4 / 27 ≤ ((2 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) := by
  have h4 : Real.pi ^ 4 ≤ (3.141593 : ℝ) ^ 4 := by
    gcongr
    exact Real.pi_lt_d6.le
  have h5 : ((2 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) = 2 * (3.141593 : ℝ) ^ 4 / 27 := by
    push_cast
    norm_num
  rw [h5]
  linarith

/-- The rational comparison for Corollary 2; slack `+2.77·10⁻⁶`. -/
theorem certDyad_num :
    Cert.B0q certDyad + (2 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) * Cert.B1q certDyad
      ≤ 2 - Pcert_dyad := by
  have h0 : Cert.B0q certDyad = B0_certDyad := by simp only [Cert.B0q, certDyad_parts]
  have h1 : Cert.B1q certDyad = B1_certDyad := by simp only [Cert.B1q, certDyad_parts]
  rw [h0, h1]
  norm_num [B0_certDyad, B1_certDyad, Pcert_dyad]

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- The real-valued `B0`, `B1` of `certDyad`, from §3c. Replaces `Cert.B0Eq`/`B1Eq` here. -/
theorem B0B1_certDyad :
    B0 certDyad.toFun = ((B0_certDyad : ℚ) : ℝ)
      ∧ B1 certDyad.toFun = ((B1_certDyad : ℚ) : ℝ) := by
  obtain ⟨h0, h1⟩ := two_cell_payoff' certDyad certDyad_NonnegOK certDyad_MassOK
    (certDyad.coeff.getD 0 []) (certDyad.coeff.getD 1 []) (by norm_num [certDyad]) (by rfl)
  refine ⟨h0.trans ?_, h1.trans ?_⟩ <;>
  · norm_num (maxSteps := 100000000) [certDyad, B0_certDyad, B1_certDyad, gramB0, gramB1,
      gramI2, gramM, gramN, gramTop, gramPhi0, gramPhi1, gramInner, pdefint, pevalQ, pint,
      pintAux, pmul, padd, pscal, psub, pcomp]

/-- **Corollary 2's payoff**, `C = 2π⁴/27 = ZetaQ.CfamDyadic`, at `Pcert_dyad = 0.7099`
(paper's `0.7099167448` at `λ* = 1.1931581210`, `b* = 0.5965790605`).

The mesh for this `C` has not been chosen, so the bandwidth is existential-with-bounds
; the recipe of A.5.2 applies with `b = 5966/10000`.
Paper §11, Corollary 2.
Depends on: `payoff_of_cert`. **Rule 17: `1 < lam ∧ lam < 2` explicit; never `lam ≤ 1`.** -/
theorem payoff_feasible_dyadic :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Admissible lam v ∧
      B (2 * Real.pi ^ 4 / 27) v ≤ 2 - ((Pcert_dyad : ℚ) : ℝ) := by
  obtain ⟨hadm, hB⟩ :=
    payoff_of_cert_num certDyad certDyad_NonnegOK certDyad_MassOK B0_certDyad B1_certDyad
      B0B1_certDyad.1 B0B1_certDyad.2 (2 * Real.pi ^ 4 / 27)
      (2 * 3141593 ^ 4 / (27 * 10 ^ 24)) Pcert_dyad (by norm_num) C_dyad_le
      (by norm_num [B0_certDyad, B1_certDyad, Pcert_dyad])
  exact ⟨((certDyad.lam : ℚ) : ℝ), certDyad.toFun, certDyad.one_lt_lam, certDyad.lam_lt_two,
    hadm, hB⟩

/-- **The certificate data for Corollary 3 (even/odd dyadic)**, `C = 4π⁴/27`.
`b = 11/20`, so `λ_cert = 11/10 ∈ (1,2)` and `t₀ = 9/20`. Two cells, degree 3.
`b < b* = 0.5507999211`, so the Bernstein check passes (worst `β = +9.4·10⁻³`).
Rule 17: `λ = 11/10 > 1`. -/
def certEvenDyad : Cert where
  b     := (11 / 20 : ℚ)
  xs    := [(9 / 20 : ℚ)]
  deg   := 3
  coeff :=
    [[ (229391807 / 216000000 : ℚ), (1 / 250 : ℚ), (-1107 / 1000 : ℚ), (39 / 250 : ℚ) ],
     [ (853 / 1000 : ℚ), (-737 / 1000 : ℚ), (-51883 / 500 : ℚ), (133899 / 500 : ℚ) ]]
  hb_lo      := by norm_num
  hb_hi      := by norm_num
  hmesh      := by norm_num
  hxs_mem    := by norm_num
  hxs_sorted := by norm_num
  hcoeff_len := by rfl
  hdeg       := by norm_num

/-- Exact mass identity for `certEvenDyad`. -/
theorem certEvenDyad_MassOK : certEvenDyad.MassOK := by
  norm_num [Cert.MassOK, Cert.massHalf, Cert.massPiece, Cert.node, Cert.nodes, certEvenDyad,
    Finset.sum_range_succ]

/-- Bernstein sign certificate for `certEvenDyad`. -/
theorem certEvenDyad_NonnegOK : certEvenDyad.NonnegOK := by
  norm_num [Cert.NonnegOK, Cert.nonnegCheck, Cert.node, Cert.nodes, certEvenDyad]
  intro i hi k hk
  interval_cases i <;> interval_cases k <;>
    norm_num [Cert.bernsteinCoeff, Finset.sum_range_succ]

/-- `B₀` of `certEvenDyad`. -/
def B0_certEvenDyad : ℚ := 46790081051145410281 / 36288000000000000000

/-- `B₁` of `certEvenDyad`. -/
def B1_certEvenDyad : ℚ := 1628154448871089 / 1260000000000000000

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- The engine, run on `certEvenDyad`. -/
theorem certEvenDyad_parts :
    Cert.payoffPartsQ certEvenDyad = (B0_certEvenDyad, B1_certEvenDyad) := by
  norm_num (maxSteps := 100000000) [Cert.payoffPartsQ, Cert.certPieces, Cert.piecesFrom,
    Cert.nodes, certEvenDyad, B0_certEvenDyad, B1_certEvenDyad, allPsi, pairPsi, pairCells, convPair, psiAtZero,
    sumInt, intCell, p2mul, p2add, p2sub, p2evalT, pcomp, pmul, padd, pscal, psub, pint,
    pintAux, pevalQ, pdefint, sortedNub, sortedIns, pairsAdj, List.replicate]

/-- `4π⁴/27 ≤ 4·3.141593⁴/27`, from `Real.pi_lt_d6`. -/
theorem C_even_dyad_le :
    4 * Real.pi ^ 4 / 27 ≤ ((4 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) := by
  have h4 : Real.pi ^ 4 ≤ (3.141593 : ℝ) ^ 4 := by
    gcongr
    exact Real.pi_lt_d6.le
  have h5 : ((4 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) : ℝ) = 4 * (3.141593 : ℝ) ^ 4 / 27 := by
    push_cast
    norm_num
  rw [h5]
  linarith

/-- The rational comparison for Corollary 3 (dyadic); slack `+4.33·10⁻⁵`. -/
theorem certEvenDyad_num :
    Cert.B0q certEvenDyad + (4 * 3141593 ^ 4 / (27 * 10 ^ 24) : ℚ) * Cert.B1q certEvenDyad
      ≤ 2 - Pcert_even := by
  have h0 : Cert.B0q certEvenDyad = B0_certEvenDyad := by
    simp only [Cert.B0q, certEvenDyad_parts]
  have h1 : Cert.B1q certEvenDyad = B1_certEvenDyad := by
    simp only [Cert.B1q, certEvenDyad_parts]
  rw [h0, h1]
  norm_num [B0_certEvenDyad, B1_certEvenDyad, Pcert_even]

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- The real-valued `B0`, `B1` of `certEvenDyad`, from §3c. -/
theorem B0B1_certEvenDyad :
    B0 certEvenDyad.toFun = ((B0_certEvenDyad : ℚ) : ℝ)
      ∧ B1 certEvenDyad.toFun = ((B1_certEvenDyad : ℚ) : ℝ) := by
  obtain ⟨h0, h1⟩ := two_cell_payoff' certEvenDyad certEvenDyad_NonnegOK certEvenDyad_MassOK
    (certEvenDyad.coeff.getD 0 []) (certEvenDyad.coeff.getD 1 [])
    (by norm_num [certEvenDyad]) (by rfl)
  refine ⟨h0.trans ?_, h1.trans ?_⟩ <;>
  · norm_num (maxSteps := 100000000) [certEvenDyad, B0_certEvenDyad, B1_certEvenDyad, gramB0,
      gramB1, gramI2, gramM, gramN, gramTop, gramPhi0, gramPhi1, gramInner, pdefint, pevalQ,
      pint, pintAux, pmul, padd, pscal, psub, pcomp]

/-- **Corollary 3's payoff (even, resp. odd, dyadic)** — the SAME functional at the DOUBLED
out-zone constant `2·C_dyad = 4π⁴/27 = ZetaQ.CfamEvenDyadic`, at `Pcert_even = 0.6919`
(paper's `0.6919434301` at `λ* = 1.1015998422`, `b* = 0.5507999211`).

The doubling is Corollary 3's O13 (sieve positivity out-zone, halved denominator); the in-zone
coefficient is UNCHANGED (O8–O12) — i.e. the functional is `Bgen 1 (2C)`, NOT `Bgen 2 (2C)`.
This constant has NO shipped script anchor (it is absent from `payoff_hp2.py`'s target list and
from every log of the authoring project); it was re-verified off-line as
`0.691943430126`.
Paper §1.1, §12.3.
Depends on: `payoff_of_cert`. **Rule 17: `1 < lam ∧ lam < 2` explicit.** -/
theorem payoff_feasible_even_dyadic :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Admissible lam v ∧
      B (4 * Real.pi ^ 4 / 27) v ≤ 2 - ((Pcert_even : ℚ) : ℝ) := by
  obtain ⟨hadm, hB⟩ :=
    payoff_of_cert_num certEvenDyad certEvenDyad_NonnegOK certEvenDyad_MassOK
      B0_certEvenDyad B1_certEvenDyad B0B1_certEvenDyad.1 B0B1_certEvenDyad.2
      (4 * Real.pi ^ 4 / 27) (4 * 3141593 ^ 4 / (27 * 10 ^ 24)) Pcert_even (by norm_num)
      C_even_dyad_le (by norm_num [B0_certEvenDyad, B1_certEvenDyad, Pcert_even])
  exact ⟨((certEvenDyad.lam : ℚ) : ℝ), certEvenDyad.toFun, certEvenDyad.one_lt_lam,
    certEvenDyad.lam_lt_two, hadm, hB⟩

/-- **The certificate data for Corollary 3 (even/odd over `q ≤ Q`)**, `C = π⁴/9`.
`b = 14/25`, so `λ_cert = 28/25 ∈ (1,2)` and `t₀ = 11/25`. Two cells, degree 2.
`b < b* = 0.5664894411`, so the Bernstein check passes (worst `β = +5.6·10⁻²`).
Rule 17: `λ = 28/25 > 1`. -/
def certEvenQ : Cert where
  b     := (14 / 25 : ℚ)
  xs    := [(11 / 25 : ℚ)]
  deg   := 2
  coeff :=
    [[ (7246337 / 6875000 : ℚ), (-13 / 1000 : ℚ), (-249 / 250 : ℚ) ],
     [ (173 / 200 : ℚ), (-2361 / 1000 : ℚ), (-7301 / 200 : ℚ) ]]
  hb_lo      := by norm_num
  hb_hi      := by norm_num
  hmesh      := by norm_num
  hxs_mem    := by norm_num
  hxs_sorted := by norm_num
  hcoeff_len := by rfl
  hdeg       := by norm_num

/-- Exact mass identity for `certEvenQ`. -/
theorem certEvenQ_MassOK : certEvenQ.MassOK := by
  norm_num [Cert.MassOK, Cert.massHalf, Cert.massPiece, Cert.node, Cert.nodes, certEvenQ,
    Finset.sum_range_succ]

/-- Bernstein sign certificate for `certEvenQ`. -/
theorem certEvenQ_NonnegOK : certEvenQ.NonnegOK := by
  norm_num [Cert.NonnegOK, Cert.nonnegCheck, Cert.node, Cert.nodes, certEvenQ]
  intro i hi k hk
  interval_cases i <;> interval_cases k <;>
    norm_num [Cert.bernsteinCoeff, Finset.sum_range_succ]

/-! ### The degree bound, now a `Cert` FIELD (D25), read off for the four shipped certificates

`Cert.admissible` was FALSE before `hdeg` existed — see the `Cert.hdeg` docstring for the
counterexample. D25 added the field rather than weakening the statement; the four lemmas below
are kept and are now just the field,
satisfied **with equality** by every shipped certificate, so no shipped datum changed. -/

/-- `certQQ`'s coefficient blocks really have degree `≤ deg = 4`. -/
theorem certQQ_degBound : ∀ p ∈ certQQ.coeff, p.length ≤ certQQ.deg + 1 := certQQ.hdeg

/-- `certDyad`'s coefficient blocks really have degree `≤ deg = 2`. -/
theorem certDyad_degBound : ∀ p ∈ certDyad.coeff, p.length ≤ certDyad.deg + 1 := certDyad.hdeg

/-- `certEvenDyad`'s coefficient blocks really have degree `≤ deg = 3`. -/
theorem certEvenDyad_degBound : ∀ p ∈ certEvenDyad.coeff, p.length ≤ certEvenDyad.deg + 1 :=
  certEvenDyad.hdeg

/-- `certEvenQ`'s coefficient blocks really have degree `≤ deg = 2`. -/
theorem certEvenQ_degBound : ∀ p ∈ certEvenQ.coeff, p.length ≤ certEvenQ.deg + 1 :=
  certEvenQ.hdeg

/-- `B₀` of `certEvenQ`. -/
def B0_certEvenQ : ℚ := 2252798830925654203 / 1762390136718750000

/-- `B₁` of `certEvenQ`. -/
def B1_certEvenQ : ℚ := 2671235932167 / 1220703125000000

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- The engine, run on `certEvenQ`. -/
theorem certEvenQ_parts : Cert.payoffPartsQ certEvenQ = (B0_certEvenQ, B1_certEvenQ) := by
  norm_num (maxSteps := 100000000) [Cert.payoffPartsQ, Cert.certPieces, Cert.piecesFrom,
    Cert.nodes, certEvenQ, B0_certEvenQ, B1_certEvenQ, allPsi, pairPsi, pairCells, convPair, psiAtZero,
    sumInt, intCell, p2mul, p2add, p2sub, p2evalT, pcomp, pmul, padd, pscal, psub, pint,
    pintAux, pevalQ, pdefint, sortedNub, sortedIns, pairsAdj, List.replicate]

/-- `π⁴/9 ≤ 3.141593⁴/9`, from `Real.pi_lt_d6`. -/
theorem C_even_qQ_le : Real.pi ^ 4 / 9 ≤ ((3141593 ^ 4 / (9 * 10 ^ 24) : ℚ) : ℝ) := by
  have h4 : Real.pi ^ 4 ≤ (3.141593 : ℝ) ^ 4 := by
    gcongr
    exact Real.pi_lt_d6.le
  have h5 : ((3141593 ^ 4 / (9 * 10 ^ 24) : ℚ) : ℝ) = (3.141593 : ℝ) ^ 4 / 9 := by
    push_cast
    norm_num
  rw [h5]
  linarith

/-- The rational comparison for Corollary 3 over `q ≤ Q`; slack `+5.24·10⁻⁵`. -/
theorem certEvenQ_num :
    Cert.B0q certEvenQ + (3141593 ^ 4 / (9 * 10 ^ 24) : ℚ) * Cert.B1q certEvenQ
      ≤ 2 - Pcert_evenQ := by
  have h0 : Cert.B0q certEvenQ = B0_certEvenQ := by simp only [Cert.B0q, certEvenQ_parts]
  have h1 : Cert.B1q certEvenQ = B1_certEvenQ := by simp only [Cert.B1q, certEvenQ_parts]
  rw [h0, h1]
  norm_num [B0_certEvenQ, B1_certEvenQ, Pcert_evenQ]

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- The real-valued `B0`, `B1` of `certEvenQ`, from §3c. -/
theorem B0B1_certEvenQ :
    B0 certEvenQ.toFun = ((B0_certEvenQ : ℚ) : ℝ)
      ∧ B1 certEvenQ.toFun = ((B1_certEvenQ : ℚ) : ℝ) := by
  obtain ⟨h0, h1⟩ := two_cell_payoff' certEvenQ certEvenQ_NonnegOK certEvenQ_MassOK
    (certEvenQ.coeff.getD 0 []) (certEvenQ.coeff.getD 1 []) (by norm_num [certEvenQ]) (by rfl)
  refine ⟨h0.trans ?_, h1.trans ?_⟩ <;>
  · norm_num (maxSteps := 100000000) [certEvenQ, B0_certEvenQ, B1_certEvenQ, gramB0, gramB1,
      gramI2, gramM, gramN, gramTop, gramPhi0, gramPhi1, gramInner, pdefint, pevalQ, pint,
      pintAux, pmul, padd, pscal, psub, pcomp]

/-- **Corollary 3's payoff (even, resp. odd) over `q ≤ Q`**, `C = π⁴/9 = ZetaQ.CfamEven`, at
`Pcert_evenQ = 0.6980` (paper's `0.6980745436` at `λ* = 1.1329788821`, `b* = 0.5664894411`).

Paper §1.1. Depends on: `payoff_of_cert`.
**Rule 17: `1 < lam ∧ lam < 2` explicit.** -/
theorem payoff_feasible_even_qQ :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Admissible lam v ∧
      B (Real.pi ^ 4 / 9) v ≤ 2 - ((Pcert_evenQ : ℚ) : ℝ) := by
  obtain ⟨hadm, hB⟩ :=
    payoff_of_cert_num certEvenQ certEvenQ_NonnegOK certEvenQ_MassOK B0_certEvenQ B1_certEvenQ
      B0B1_certEvenQ.1 B0B1_certEvenQ.2 (Real.pi ^ 4 / 9)
      (3141593 ^ 4 / (9 * 10 ^ 24)) Pcert_evenQ (by norm_num) C_even_qQ_le
      (by norm_num [B0_certEvenQ, B1_certEvenQ, Pcert_evenQ])
  exact ⟨((certEvenQ.lam : ℚ) : ℝ), certEvenQ.toFun, certEvenQ.one_lt_lam,
    certEvenQ.lam_lt_two, hadm, hB⟩

/-! ## 6. The three calibration gates

**The paper's own caveat, carried verbatim, because a referee will notice it (L684–688):**
"One honest caveat, stated because a referee will notice it: all three gates are special cases
— fixed kernel or a C-limit — so they certify the SOLVER against outside ground truth; the
finite-C free-boundary regime the headline uses is checked separately, by the closed-form/
Nyström agreement to twelve digits and the strict KKT complementarity of payoff_hp2.py".

**Consequence for this skeleton, stated plainly: there is NO Lean gate for the headline regime
other than the certificate itself.** Gates 1 and 2 are C-limits or fixed profiles; gate 3 is a
different kernel at λ = 2. None of them touches the finite-C free-boundary regime.

A correction to the paper's description: `log_payoff.txt:6–8` shows
closed-form-vs-Nyström agreement of 9–11 digits (Richardson at FIXED `b`), and the
free-boundary Nyström scan agrees to ≈ 6 digits; the "twelve digits" figure is the
EL-vs-direct-quadrature check of `payoff_final2.py`, not a Nyström comparison — and
D2 notes that check reuses the EL solve's own normalisation. -/

namespace Gates

/-- The Montgomery–Taylor constant in closed form,
`3/2 − (1/√2)·cot(1/√2) = 0.672500703679412`.

Paper §11. Equals `Zeta23.ThmD.HD 1` (`Zeta23/ThmD/Functional.lean:53, :464`).
Rule 17: this is the value at `λ = 1` EXACTLY. -/
def MTconst : ℝ := 3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)

/-- The paper's decimal for the MT anchor, `0.672500703679412` (re-verified in
off-line as `0.6725007036794116`).

Rule 17: value at `λ = 1`. -/
def MTdigits : ℝ := 0.672500703679412

/-- `MTconst = Zeta23.ThmD.HD 1` — the MT anchor IS the reference tree's Theorem-D constant.

This is the one place `ZetaQ` may reach into `Zeta23.ThmD`. Under `v(t) = u(t/λ)/λ` one has
`B(v) = 1/cFun λ u` at `∫u = 1`, so `2 − B = 2 − 1/cStar λ = HD λ`; `HD_one`
(`Zeta23/ThmD/Functional.lean:464`) is sorry-free.
Paper §11.
Depends on: `Zeta23.ThmD.HD_one`.
**Rule 17: `Zeta23.ThmD.cFun_vStar` (`ThmD/Functional.lean:432`) carries `h1 : lam ≤ 1` and is
reusable HERE ONLY, at `λ = 1` with EQUALITY. `Zeta23.ThmD.HD_one` (`:464`) is at `λ = 1` and
is safe. Do NOT cite either anywhere else in `ZetaQ`.** -/
theorem MTconst_eq_HD_one : MTconst = Zeta23.ThmD.HD 1 := by
  unfold MTconst
  exact Zeta23.ThmD.HD_one.symm

/-! ### The twelve digits of the MT anchor

**Why this is not an interval-arithmetic exercise.** `Real.cos_bound` in this Mathlib pin is the
order-4 Taylor bound, error `≈ 1.3·10⁻²` at `1/√2` — nowhere near twelve digits, and there is no
order-14 error control to reach for. The route taken instead is exact:

`x = 1/√2` satisfies `x² = 1/2`, so **both Taylor series have RATIONAL terms**,
`cos x = Σ (−1)ⁿ 2⁻ⁿ/(2n)!` and `sin x = x·Σ (−1)ⁿ 2⁻ⁿ/(2n+1)!`. The factor `x` in the sine
series cancels the `1/√2` in front of the cotangent, so
`MTconst = 3/2 − cos x / (sin x / x)` with BOTH arguments limits of rational series — no
irrational number survives into the arithmetic. Nine terms of each, with the crude geometric
tail majorant `|term(i+9)| ≤ (2⁻⁹/18!)·2⁻ⁱ` (from `18! ≤ (2i+18)!`), give `10⁻¹⁵` accuracy, and
the final comparison is a rational inequality with `9.2·10⁻¹³` of slack.

Rule 17: `λ = 1` here with EQUALITY, and nothing in this block mentions `λ` at all. -/

/-- Geometric tail bound: a real series whose terms past `k` are dominated by `M·2⁻ⁱ` has tail
at most `2M`. No summability hypothesis is needed — the domination supplies it. -/
theorem geom_tail_abs_le {h : ℕ → ℝ} {k : ℕ} {M : ℝ}
    (hb : ∀ i : ℕ, |h (i + k)| ≤ M * (1 / 2 : ℝ) ^ i) :
    |∑' i : ℕ, h (i + k)| ≤ 2 * M := by
  have hgeo : Summable (fun i : ℕ => M * (1 / 2 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left M
  have habs : Summable (fun i : ℕ => |h (i + k)|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) hb hgeo
  have h1 : |∑' i : ℕ, h (i + k)| ≤ ∑' i : ℕ, |h (i + k)| := by
    have hn := norm_tsum_le_tsum_norm (f := fun i : ℕ => h (i + k))
      (by simpa [Real.norm_eq_abs] using habs)
    simpa [Real.norm_eq_abs] using hn
  have h2 : ∑' i : ℕ, |h (i + k)| ≤ ∑' i : ℕ, M * (1 / 2 : ℝ) ^ i :=
    Summable.tsum_le_tsum hb habs hgeo
  have h3 : ∑' i : ℕ, M * (1 / 2 : ℝ) ^ i = M * 2 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- Truncating a `HasSum` at index `k` costs at most twice the geometric tail majorant. -/
theorem hasSum_trunc_bound {f : ℕ → ℝ} {L : ℝ} (hf : HasSum f L) (k : ℕ) {M : ℝ}
    (hb : ∀ i : ℕ, |f (i + k)| ≤ M * (1 / 2 : ℝ) ^ i) :
    |L - ∑ i ∈ Finset.range k, f i| ≤ 2 * M := by
  have hsplit := hf.summable.sum_add_tsum_nat_add k
  rw [hf.tsum_eq] at hsplit
  have hrw : L - ∑ i ∈ Finset.range k, f i = ∑' i : ℕ, f (i + k) := by linarith
  rw [hrw]
  exact geom_tail_abs_le hb

/-- **The whole trick**: `(1/√2)² = 1/2`, so every even power of the MT argument is rational. -/
theorem inv_sqrt_two_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `cos(1/√2)` to fifteen digits, from nine terms of its (rational-term) Taylor series. -/
theorem cos_inv_sqrt_two_bound :
    |Real.cos (Real.sqrt 2)⁻¹ - 4072048119833761 / 5356234211328000| ≤ 1 / 10 ^ 15 := by
  have hCs : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n) : ℝ))
      (Real.cos (Real.sqrt 2)⁻¹) := by
    have hfun : (fun n : ℕ =>
          (-1 : ℝ) ^ n * ((Real.sqrt 2)⁻¹) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ))
        = fun n : ℕ => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n) : ℝ) := by
      funext n
      rw [pow_mul, inv_sqrt_two_sq]
    rw [← hfun]
    exact Real.hasSum_cos _
  have hb : ∀ i : ℕ,
      |(fun n : ℕ => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n) : ℝ)) (i + 9)|
        ≤ ((1 / 2 : ℝ) ^ 9 / 6402373705728000) * (1 / 2 : ℝ) ^ i := by
    intro i
    have hf18 : Nat.factorial 18 = 6402373705728000 := by norm_num [Nat.factorial]
    have hfac : (6402373705728000 : ℝ) ≤ (Nat.factorial (2 * (i + 9)) : ℝ) := by
      have h : Nat.factorial 18 ≤ Nat.factorial (2 * (i + 9)) := Nat.factorial_le (by omega)
      rw [hf18] at h
      exact_mod_cast h
    have habs : |(-1 : ℝ) ^ (i + 9) * (1 / 2 : ℝ) ^ (i + 9) / (Nat.factorial (2 * (i + 9)) : ℝ)|
        = (1 / 2 : ℝ) ^ (i + 9) / (Nat.factorial (2 * (i + 9)) : ℝ) := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), Nat.abs_cast]
    simp only [habs]
    calc (1 / 2 : ℝ) ^ (i + 9) / (Nat.factorial (2 * (i + 9)) : ℝ)
        ≤ (1 / 2 : ℝ) ^ (i + 9) / 6402373705728000 := by gcongr
      _ = ((1 / 2 : ℝ) ^ 9 / 6402373705728000) * (1 / 2 : ℝ) ^ i := by rw [pow_add]; ring
  have hmain := hasSum_trunc_bound hCs 9 hb
  have hsum : (∑ i ∈ Finset.range 9,
        (-1 : ℝ) ^ i * (1 / 2 : ℝ) ^ i / (Nat.factorial (2 * i) : ℝ))
      = 4072048119833761 / 5356234211328000 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hmain
  refine hmain.trans ?_
  norm_num

/-- `sin(1/√2)/(1/√2)` to fifteen digits. Dividing the sine series by its argument is what
removes the `1/√2` prefactor from `MTconst` — see the section note. -/
theorem sinc_inv_sqrt_two_bound :
    |Real.sin (Real.sqrt 2)⁻¹ / (Real.sqrt 2)⁻¹
        - 27885146789037259 / 30351993864192000| ≤ 1 / 10 ^ 15 := by
  have hxpos : (0 : ℝ) < (Real.sqrt 2)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have hx0 : ((Real.sqrt 2)⁻¹ : ℝ) ≠ 0 := ne_of_gt hxpos
  have hSs0 : HasSum (fun n : ℕ => (Real.sqrt 2)⁻¹
      * ((-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ)))
      (Real.sin (Real.sqrt 2)⁻¹) := by
    have hfun : (fun n : ℕ =>
          (-1 : ℝ) ^ n * ((Real.sqrt 2)⁻¹) ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ))
        = fun n : ℕ => (Real.sqrt 2)⁻¹
            * ((-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ)) := by
      funext n
      rw [pow_succ, pow_mul, inv_sqrt_two_sq]
      ring
    rw [← hfun]
    exact Real.hasSum_sin _
  have hSs : HasSum
      (fun n : ℕ => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ))
      (Real.sin (Real.sqrt 2)⁻¹ / (Real.sqrt 2)⁻¹) := by
    have hfun2 : (fun n : ℕ => (Real.sqrt 2)⁻¹
          * ((-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ)) / (Real.sqrt 2)⁻¹)
        = fun n : ℕ => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ) := by
      funext n
      field_simp
    rw [← hfun2]
    exact hSs0.div_const _
  have hb : ∀ i : ℕ,
      |(fun n : ℕ => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n / (Nat.factorial (2 * n + 1) : ℝ)) (i + 9)|
        ≤ ((1 / 2 : ℝ) ^ 9 / 121645100408832000) * (1 / 2 : ℝ) ^ i := by
    intro i
    have hf19 : Nat.factorial 19 = 121645100408832000 := by norm_num [Nat.factorial]
    have hfac : (121645100408832000 : ℝ) ≤ (Nat.factorial (2 * (i + 9) + 1) : ℝ) := by
      have h : Nat.factorial 19 ≤ Nat.factorial (2 * (i + 9) + 1) := Nat.factorial_le (by omega)
      rw [hf19] at h
      exact_mod_cast h
    have habs :
        |(-1 : ℝ) ^ (i + 9) * (1 / 2 : ℝ) ^ (i + 9) / (Nat.factorial (2 * (i + 9) + 1) : ℝ)|
        = (1 / 2 : ℝ) ^ (i + 9) / (Nat.factorial (2 * (i + 9) + 1) : ℝ) := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), Nat.abs_cast]
    simp only [habs]
    calc (1 / 2 : ℝ) ^ (i + 9) / (Nat.factorial (2 * (i + 9) + 1) : ℝ)
        ≤ (1 / 2 : ℝ) ^ (i + 9) / 121645100408832000 := by gcongr
      _ = ((1 / 2 : ℝ) ^ 9 / 121645100408832000) * (1 / 2 : ℝ) ^ i := by rw [pow_add]; ring
  have hmain := hasSum_trunc_bound hSs 9 hb
  have hsum : (∑ i ∈ Finset.range 9,
        (-1 : ℝ) ^ i * (1 / 2 : ℝ) ^ i / (Nat.factorial (2 * i + 1) : ℝ))
      = 27885146789037259 / 30351993864192000 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hmain
  refine hmain.trans ?_
  norm_num

/-- The MT anchor's decimal, to the twelve digits the paper prints. **Proved**, by the
rational-series route described in the section note above.

Paper §11.
Depends on: `MTconst`, `cos_inv_sqrt_two_bound`, `sinc_inv_sqrt_two_bound`.
Rule 17: value at `λ = 1`. -/
theorem MTconst_digits : |MTconst - MTdigits| ≤ (1 : ℝ) / 10 ^ 12 := by
  have hxpos : (0 : ℝ) < (Real.sqrt 2)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have hx0 : ((Real.sqrt 2)⁻¹ : ℝ) ≠ 0 := ne_of_gt hxpos
  have hC := abs_le.mp cos_inv_sqrt_two_bound
  have hS := abs_le.mp sinc_inv_sqrt_two_bound
  have hSpos : (0 : ℝ) < Real.sin (Real.sqrt 2)⁻¹ / (Real.sqrt 2)⁻¹ := by linarith [hS.1]
  have hsin0 : Real.sin (Real.sqrt 2)⁻¹ ≠ 0 := by
    intro h
    rw [h] at hSpos
    simp at hSpos
  have hMT : MTconst = 3 / 2
      - Real.cos (Real.sqrt 2)⁻¹ / (Real.sin (Real.sqrt 2)⁻¹ / (Real.sqrt 2)⁻¹) := by
    rw [MTconst]
    field_simp
  rw [hMT, abs_le]
  constructor
  · have hub : Real.cos (Real.sqrt 2)⁻¹ / (Real.sin (Real.sqrt 2)⁻¹ / (Real.sqrt 2)⁻¹)
        ≤ 3 / 2 - MTdigits + 1 / 10 ^ 12 := by
      rw [div_le_iff₀ hSpos]
      simp only [MTdigits]
      linarith [hC.2, hS.1]
    simp only [MTdigits] at hub ⊢
    linarith
  · have hlb : 3 / 2 - MTdigits - 1 / 10 ^ 12
        ≤ Real.cos (Real.sqrt 2)⁻¹ / (Real.sin (Real.sqrt 2)⁻¹ / (Real.sqrt 2)⁻¹) := by
      rw [le_div_iff₀ hSpos]
      simp only [MTdigits]
      linarith [hC.1, hS.2]
    simp only [MTdigits] at hlb ⊢
    linarith

/-- **GATE 1 (Montgomery–Taylor), the C-LIMIT gate.** At `λ = 1` the C-penalised zone
`1 < |α| ≤ λ` is EMPTY, `B` collapses to the Montgomery–Taylor functional for every `C`, and
`2 − B ≤ 0.672500703679412`.

Paper §11.
Depends on: `Admissible`, `B`, `MTconst`, and — at `λ = 1` only — `Zeta23.ThmD`.
**Rule 17, and read it carefully: `Admissible 1 v` here is NOT a smuggled bandwidth cap; it is
the DEFINING feature of the gate. This theorem is precisely the statement that §11's problem
DEGENERATES at λ = 1. It is the reason a `lam ≤ 1` hypothesis anywhere else would be fatal —
it would make every §11 statement a restatement of this one.** Never generalise this to
`λ > 1`, and never let `Admissible 1` propagate out of this namespace.
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: a `λ = 1` degeneracy gate.  It supports `Normalisation.gain_positive_all_C`, which is
itself out of scope; Theorem 1 runs at `λ* = 1.2507 > 1` and never consumes it. -/
def GateMTUpper : Prop := ∀ (C : ℝ) (v : ℝ → ℝ), Admissible 1 v → 2 - B C v ≤ MTconst

/-- **GATE 1, attainment.** The MT value is achieved at `v* = cos(√2 t)` on `[−1/2, 1/2]`
(normalised), for every `C` — because the C-zone is empty at `λ = 1`.

Paper §11; the profile is `Zeta23.ThmD.vStar 1` up to normalisation.
Depends on: `gate_MT_upper`, `Zeta23.ThmD.HD_one`.
**Rule 17: same as `gate_MT_upper` — `λ = 1` is the gate's content, not a hypothesis on §11.**
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: the attainment half of `GateMTUpper`; same scope note. -/
def GateMTAttained : Prop := ∀ C : ℝ, ∃ v : ℝ → ℝ, Admissible 1 v ∧ 2 - B C v = MTconst

/-- Helper for `gate_flat`: the triangular autocorrelation of the flat profile,
`ψ(α) = max(1 − |α|, 0)`. The product `v(t)·v(t−α)` is the indicator of
`[−1/2, 1/2] ∩ ([−1/2, 1/2] + α) = [max(−1/2, α−1/2), min(1/2, α+1/2)]`, whose length is
`1 − |α|` when that is nonnegative. **Rule 17: `λ = 1` here is `gate_flat`'s own content.** -/
private theorem psi_flat (α : ℝ) :
    psi (Set.indicator (Set.Icc (-(1 : ℝ) / 2) (1 / 2)) (fun _ => (1 : ℝ))) α
      = max (1 - |α|) 0 := by
  have hmem : ∀ t : ℝ,
      t ∈ Set.Icc (max (-(1 : ℝ) / 2) (α - 1 / 2)) (min ((1 : ℝ) / 2) (α + 1 / 2))
        ↔ (t ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
            ∧ t - α ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) := by
    intro t
    simp only [Set.mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, by constructor <;> linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
  have hfun : (fun t : ℝ =>
      Set.indicator (Set.Icc (-(1 : ℝ) / 2) (1 / 2)) (fun _ => (1 : ℝ)) t *
        Set.indicator (Set.Icc (-(1 : ℝ) / 2) (1 / 2)) (fun _ => (1 : ℝ)) (t - α))
      = Set.indicator (Set.Icc (max (-(1 : ℝ) / 2) (α - 1 / 2)) (min ((1 : ℝ) / 2) (α + 1 / 2)))
          (fun _ => (1 : ℝ)) := by
    funext t
    by_cases h : t ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
        ∧ t - α ∈ Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)
    · rw [Set.indicator_of_mem h.1, Set.indicator_of_mem h.2,
        Set.indicator_of_mem ((hmem t).mpr h)]
      norm_num
    · rw [Set.indicator_of_notMem (fun hc => h ((hmem t).mp hc))]
      rcases not_and_or.mp h with h' | h'
      · rw [Set.indicator_of_notMem h', zero_mul]
      · rw [Set.indicator_of_notMem h', mul_zero]
  have hlen : min ((1 : ℝ) / 2) (α + 1 / 2) - max (-(1 : ℝ) / 2) (α - 1 / 2) = 1 - |α| := by
    rcases le_or_gt 0 α with hα | hα
    · rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg hα]; ring
    · rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_neg hα]; ring
  simp only [psi]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
    Real.volume_real_Icc, smul_eq_mul, mul_one, hlen]

/-- Helper for `gate_flat`: `∫_{-1}^{1} (|α| − α²) dα = 1/3`, the in-zone kernel integral of the
triangular autocorrelation. -/
private theorem flat_kernel_integral : ∫ x in (-(1 : ℝ))..1, (|x| - x ^ 2) = 1 / 3 := by
  have hcont : Continuous (fun x : ℝ => |x| - x ^ 2) := continuous_abs.sub (continuous_pow 2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := -(1 : ℝ)) (b := 0) (c := 1) (μ := volume) (f := fun x : ℝ => |x| - x ^ 2)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hc1 : Set.EqOn (fun x : ℝ => |x| - x ^ 2) (fun x : ℝ => -x - x ^ 2)
      (Set.uIcc (-(1 : ℝ)) 0) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-(1 : ℝ)) ≤ 0)] at hx
    simp only
    rw [abs_of_nonpos hx.2]
  have h1 : ∫ x in (-(1 : ℝ))..0, (|x| - x ^ 2) = 1 / 6 := by
    rw [intervalIntegral.integral_congr hc1]
    have hd : ∀ x ∈ Set.uIcc (-(1 : ℝ)) 0,
        HasDerivAt (fun y : ℝ => -(y ^ 2) / 2 - y ^ 3 / 3) (-x - x ^ 2) x := by
      intro x _
      have h2 : (-x - x ^ 2 : ℝ) = -(2 * x ^ 1) / 2 - 3 * x ^ 2 / 3 := by ring
      rw [h2]
      exact ((hasDerivAt_pow 2 x).neg.div_const 2).sub ((hasDerivAt_pow 3 x).div_const 3)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun x : ℝ => -x - x ^ 2).intervalIntegrable _ _)]
    norm_num
  have hc2 : Set.EqOn (fun x : ℝ => |x| - x ^ 2) (fun x : ℝ => x - x ^ 2)
      (Set.uIcc (0 : ℝ) 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    simp only
    rw [abs_of_nonneg hx.1]
  have h2 : ∫ x in (0 : ℝ)..1, (|x| - x ^ 2) = 1 / 6 := by
    rw [intervalIntegral.integral_congr hc2]
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => y ^ 2 / 2 - y ^ 3 / 3) (x - x ^ 2) x := by
      intro x _
      have h3 : (x - x ^ 2 : ℝ) = 2 * x ^ 1 / 2 - 3 * x ^ 2 / 3 := by ring
      rw [h3]
      exact ((hasDerivAt_pow 2 x).div_const 2).sub ((hasDerivAt_pow 3 x).div_const 3)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun x : ℝ => x - x ^ 2).intervalIntegrable _ _)]
    norm_num
  linarith [hsplit, h1, h2]

/-- **GATE 2 (flat `v`), the FIXED-PROFILE gate.** `v = 1` on `[−1/2, 1/2]` gives
`ψ(α) = 1 − |α|` on `[−1,1]`, hence `B = 1 + 1/3 = 4/3` for EVERY `C`.

Fully exact: this gate is provable outright, not a `sorry` in principle — it is listed here so
the calibration suite is complete and so a future implementation must pass it.
Paper §11; `fb.gates`, `qg_check.py` (which measures `1.333000`).
Depends on: `B`, `psi`.
**Rule 17: the profile is supported in `[−1/2, 1/2]`, i.e. `λ = 1` — again a C-limit, and
again the reason this gate says nothing about the λ > 1 regime the headline uses.** -/
theorem gate_flat (C : ℝ) :
    B C (Set.indicator (Set.Icc (-(1 : ℝ) / 2) (1 / 2)) (fun _ => (1 : ℝ))) = 4 / 3 := by
  have hW : (fun α : ℝ =>
      W C α * psi (Set.indicator (Set.Icc (-(1 : ℝ) / 2) (1 / 2)) (fun _ => (1 : ℝ))) α)
      = Set.indicator (Set.Ioc (-(1 : ℝ)) 1) (fun α => |α| - α ^ 2) := by
    funext α
    rw [psi_flat]
    by_cases h : α ∈ Set.Ioc (-(1 : ℝ)) 1
    · have h1 : |α| ≤ 1 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
      rw [Set.indicator_of_mem h]
      simp only [W]
      rw [if_pos h1, max_eq_left (by linarith : (0 : ℝ) ≤ 1 - |α|), mul_sub, mul_one,
        abs_mul_abs_self]
      ring
    · rw [Set.indicator_of_notMem h]
      have h0 : (1 : ℝ) - |α| ≤ 0 := by
        simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at h
        rcases h with h | h
        · have : (1 : ℝ) ≤ |α| := by rw [abs_of_nonpos (by linarith)]; linarith
          linarith
        · have : (1 : ℝ) ≤ |α| := le_trans (by linarith) (le_abs_self α)
          linarith
      rw [max_eq_right h0, mul_zero]
  simp only [B]
  rw [hW, psi_flat, MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ)) ≤ 1), flat_kernel_integral]
  norm_num

/-- The [So16] functional: kernel `F(α) = min(|α|, 1)` (NOT `W_C`), support `[−1, 1]`
(`λ = 2`). A DIFFERENT functional from §11's.

Paper §11; `scripts/gate3_so16.py`.
Depends on: `psi`.
Rule 17: `λ = 2` is [So16]'s setting, not this paper's design point; nothing here constrains
`ParamsQ.lam`. -/
def Bso (v : ℝ → ℝ) : ℝ := psi v 0 + ∫ α, min |α| 1 * psi v α

/-- **GATE 3 ([So16]), the FIXED-KERNEL gate — the one that lands on someone else's published
number.** On the strictly better kernel `F = min(|α|, 1)` at `λ = 2`, the payoff is at least
`0.9322` — against Sono's published GRH benchmark `0.93228262`; `gate3_so16.py` reproduces
`0.9322826239` (`logs/log_gate3.txt`, `delta = 3.94e-09`).

Stated in FEASIBILITY form, which is faithful: `gate3_so16.py` solves WITHOUT the sign
constraint and verifies positivity a posteriori (`min v/max v = +4.59e-01`), so an ADMISSIBLE
optimiser genuinely exists. Do not restate this as a claim about the
sign-unconstrained infimum.
Paper §11.
Depends on: `Bso`, `Admissible`.
**Rule 17: `Admissible 2 v` — bandwidth 2, the [So16] window, strictly ABOVE 1. This gate
carries no `lam ≤ 1`; note also that `λ = 2` is [So16]'s, and is the endpoint of (not inside)
§2.2's open range `λ ∈ (0,2)`.**
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: a comparison anchor against [So16] at bandwidth 2, recorded for orientation.  It is
not one of the five feasibility certificates Theorem 1 and its corollaries consume. -/
def GateSo16 : Prop := ∃ v : ℝ → ℝ, Admissible 2 v ∧ ((9322 / 10000 : ℚ) : ℝ) ≤ 2 - Bso v

end Gates

/-! ## 7. The ramp perturbation, `ΔP = Θ(ρ³)`

**Status, stated up front.** Nothing consumes these statements:
§10.3 says explicitly that the budget's ramp row `r₂ = 6w/L` and §11's ramp cost are
"Distinct objects", and the certificate route makes the question moot (the Lean profile is not
`v*`-plus-a-ramp; any ramp cost is already inside `B0q`, `B1q`). The paper (source of truth)
states the clean power `Θ(ρ³)`; the SHIPPED evidence is one ramp shape (`sin²`) at one grid
(`n = 4001`) with measured exponent `3.09` (`qg_check.py`, `logs/log_qg.txt`) — the paper's
"three ramp shapes and three grids; measured exponent 3.03–3.09" is not reproducible from the
shipped evidence, and `NOTE_QG`'s own attack surface (item 4) says the draft should claim
"≥ second order, measured ≈ third" rather than a clean power. Both forms are
therefore stated: the paper's `Θ(ρ³)` and the weaker `O(ρ²)` the evidence supports.

`ΔP = −ΔB` since `P = 2 − B`, so the statements below are about `B(v_ρ) − B(v) ≥ 0`. -/

/-- A ramp shape of relative width `ρ`: identically `1` on `[0, 1−ρ]`, taking values in
`[0,1]`, and vanishing at the edge. `qg_check.py` uses `sin²` on the outer `ρ`-fraction.

Paper §11.
Rule 17: `ρ` is the ramp's RELATIVE width, unrelated to `λ`; no bandwidth constraint. -/
structure RampShape (r : ℝ → ℝ → ℝ) : Prop where
  /-- `r ρ = 1` on the inner `1 − ρ` fraction. -/
  unit : ∀ ρ s : ℝ, 0 < ρ → ρ < 1 → 0 ≤ s → s ≤ 1 - ρ → r ρ s = 1
  /-- nonnegative. -/
  nonneg : ∀ ρ s : ℝ, 0 ≤ r ρ s
  /-- bounded by 1. -/
  le_one : ∀ ρ s : ℝ, r ρ s ≤ 1
  /-- vanishes at the edge. -/
  edge : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → r ρ 1 = 0

/-- The ramped profile at relative width `ρ`: `v` multiplied by the ramp in the rescaled
variable `|t|/(λ/2)`, renormalised to unit mass.

Paper §11; `scripts/qg_check.py`'s ramp study.
Depends on: `RampShape`.
Rule 17: `lam` free; the ramp lives inside the SAME support `[−λ/2, λ/2]`, so admissibility is
preserved at every `lam` and no bandwidth relation is introduced. -/
def ramped (r : ℝ → ℝ → ℝ) (lam : ℝ) (v : ℝ → ℝ) (ρ : ℝ) : ℝ → ℝ :=
  fun t => v t * r ρ (|t| / (lam / 2)) / (∫ s, v s * r ρ (|s| / (lam / 2)))

/-- **§11's ramp result, the PAPER's form: `ΔP = Θ(ρ³)`**.

`v*` vanishes linearly at the free boundary (hypothesis `hedge`), so a ramp of relative width
`ρ` gives `‖δv‖₁ = O(ρ²)` and `‖δv‖₂² = O(ρ³)`; `B` is stationary at `v*` for mass-preserving
perturbations (hypothesis `hmin`, i.e. `v` IS the minimiser), and of the second variation the
kernel part pairs two ℓ¹-masses (`O(ρ⁴)`) while `ψ(0) = ∫v²` is an L²-norm — hence `Θ(ρ³)`,
**with the `∫v²` term as the reason**.

Paper §11.
`hmin` (minimality) is exactly what the feasibility route does not supply, so it is taken as
an explicit HYPOTHESIS here rather than derived. Even then the lower half of `Θ` is measured,
not proved.
Depends on: `ramped`, `RampShape`, `Admissible`.
**Rule 17: `1 < lam ∧ lam < 2` explicit. The result is about the λ > 1 free-boundary profile;
at `λ ≤ 1` there is no free boundary in the C-zone and the statement is vacuous.**
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: needs §11 minimality (see `PconstEqTwoSubMinB`).  §10.3 records that this ramp cost
and the budget's ramp row are DIFFERENT quantities, so Theorem 1 does not consume it. -/
def RampCostThetaCubic : Prop :=
  ∀ (r : ℝ → ℝ → ℝ), RampShape r → ∀ (C lam : ℝ), 0 < C → 1 < lam → lam < 2 →
    ∀ v : ℝ → ℝ, Admissible lam v →
      (∀ u : ℝ → ℝ, Admissible lam u → B C v ≤ B C u) →
      (∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ ∀ t : ℝ, |t| ≤ lam / 2 →
        κ₁ * (lam / 2 - |t|) ≤ v t ∧ v t ≤ κ₂ * (lam / 2 - |t|)) →
      ∃ K₁ K₂ ρ₀ : ℝ, 0 < K₁ ∧ K₁ ≤ K₂ ∧ 0 < ρ₀ ∧ ρ₀ < 1 ∧
        ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
          K₁ * ρ ^ 3 ≤ B C (ramped r lam v ρ) - B C v ∧
          B C (ramped r lam v ρ) - B C v ≤ K₂ * ρ ^ 3

/-- **§11's ramp result, in the weakest form the SHIPPED evidence supports**: the ramp cost is
at least SECOND order in `ρ` — in particular NOT first order in `w/L`, which is all the design
needs ("anything ≥ 2 beats the budget", `NOTE_QG.md` attack surface item 4).

Measured exponent `3.09` (`qg_check.py`, `logs/log_qg.txt`); the paper states `Θ(ρ³)`
 — see `ramp_cost_theta_cubic`. **NOT consumed by Theorem 1** — §10.3:
"Distinct objects: this ramp row … and §11's ramp cost … are different quantities".

Paper §11.
No minimality is needed: only stationarity is used, and here even that is replaced by the
weaker one-sided hypothesis `hmin`.
Depends on: `ramped`, `RampShape`, `Admissible`.
**Rule 17: `1 < lam ∧ lam < 2` explicit.**
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: as `RampCostThetaCubic`, of which this is the weaker half. -/
def RampCostAtLeastSecondOrder : Prop :=
  ∀ (r : ℝ → ℝ → ℝ), RampShape r → ∀ (C lam : ℝ), 0 < C → 1 < lam → lam < 2 →
    ∀ v : ℝ → ℝ, Admissible lam v →
      (∀ u : ℝ → ℝ, Admissible lam u → B C v ≤ B C u) →
      (∃ κ₂ : ℝ, ∀ t : ℝ, |t| ≤ lam / 2 → v t ≤ κ₂ * (lam / 2 - |t|)) →
      ∃ K ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
        ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → |B C (ramped r lam v ρ) - B C v| ≤ K * ρ ^ 2

end ZetaQ.Payoff
