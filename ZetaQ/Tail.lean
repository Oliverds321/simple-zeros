/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Tail.lean — paper §7, "The tail".

Statement source of truth: paper §7. Companion note: `LEMMA_QT` (its R8 correction at
§QT.b(5) is respected).

Imports `ZetaQ.Defs` **and `ZetaQ.Certificate`**. The
second edge was added by PART B.8 below, §7.3's pair split stated at the `ParamsQ` + `Family`
spelling that `ZetaQ/EFChi.lean`'s family join (`certificate_display_fam_of_bridge`,
`prop31_fam`) consumes: `ZetaQ.Btr` / `ZetaQ.BF` / `ZetaQ.familySum` / `ZetaQ.Family` live in
`ZetaQ/Certificate.lean`, which cannot be restated here. **Acyclicity checked**:
`ZetaQ.Certificate` imports only `ZetaQ.Defs` and `ZetaQ.Window`, neither of which reaches
`ZetaQ.Tail`.  (`ZetaQ/Budget.lean` imports `ZetaQ.Tail`, and it is above `Certificate` in
the graph.)  Precedents for adding an intra-ZetaQ edge for a genuine join:
D26 (`Ends → Normalisation`), D29, and `EFChi → Certificate` itself.

--------------------------------------------------------------------------------------
THE POINT OF THIS FILE IS THE SEPARATION.
--------------------------------------------------------------------------------------

**PART A — re-exports, ZERO sorries.** §7 is the section where Phase 1 did the most work:
of the 21 discrete claims §7 makes, 18 are already sorry-free Lean in the [R] tree at a
FREE buffer. §7.1 in particular needs *no new Lean at all* — it IS
`Zeta23.Params.norm_phiHat_le_gevrey` (`Zeta23/Tail/GevreyTail.lean:268`). Part A states
those claims at the paper's parameters and proves them by citing the Phase-1 theorem
through the `ParamsQ.toParams` bridge of `ZetaQ/Defs.lean`. Every proof here is real.

**PART B — the genuinely new statements**, all now PROVED (this file is `sorry`-free).
Three clusters:
(i) the χ/q-uniform mirror of §7.2's window sums (the paper's local count carries
`log(q(|t|+3))`, [R]'s carries `log(|t|+3)`); (ii) the closing condition of §7.2 and the
size estimate for θ₀ that §7.4 of PHASE1_INTERFACES records as missing from the whole tree;
(iii) §7.3's family aggregation and the PAIR perturbation lemma.

--------------------------------------------------------------------------------------
RULE 17.
--------------------------------------------------------------------------------------
No declaration below hypothesises λ ≤ 1, X ≤ T, or D₀ = √T.
  * the buffer is `P.D0` (a FIELD) or a bare variable `D` / a profile `D : ℝ → ℝ`.
    `Zeta23.D0 T = Real.sqrt T` never appears; only the `…D` mirrors of `WindowD.lean`
    and `GevreyTail.lean` are cited.
  * `P.lam` appears in NO hypothesis of this file. `Zeta23.Params.Valid` (which carries
    `lam_le_one`) is never cited: only `Params.ValidQ`.
  * `X` never appears; nothing relates `XQ` to `T`.
Every declaration's docstring carries a one-line Rule-17 note.

--------------------------------------------------------------------------------------
⚠ A FINDING RAISED BY THIS FILE. The bridge lemma
`ZetaQ.ParamsQ.Valid.toParamsValidQ` demands
`hlam2 : P.toParams.lam < 2`, i.e. `λℒ < 2·log(T/2π)`. `ZetaQ/Defs.lean` itself records that
`P.toParams.lam ≈ 18` at Q = 10¹⁰⁰ and `≈ 116` at 10¹⁰⁰⁰. So `P.toParams.ValidQ` is FALSE
at the design of record, and every Phase-1 lemma gated on `hP : P.ValidQ` is, as written,
not citable there. This is NOT a Rule-17 violation (it is the opposite: an over-strong
hypothesis), but it blocks the whole Part-A route in Phase 3.

--------------------------------------------------------------------------------------
⚠ THREE STATEMENTS OF THIS FILE WERE REPAIRED IN PLACE under decision D14 ("a
demonstrably false statement is repaired, not preserved"). Each carries the full diagnosis,
the counterexample and the justification in its own docstring; this is only the index.
  * **F14 `sideW_mono_base`** — was FALSE unconditionally (`sideW 0 1 1 1 1 = 396` but
    `sideW 0 1 1 e 1 ≈ 154.7`). Now states monotonicity ABOVE the crossover, with the
    crossover explicit. Proved.
  * **F16 `tail_rowsum_exp_le_Q`** — the RHS `sideW L b c (q(2T+4)) D` was short (it
    divides `sideW`'s telescoping remainder by `q`) and the prescribed proof leg does not
    exist (`one_side_exp_sum_le` needs its count for EVERY `j`; at `q=2,T=300,j=3` the
    requirement `1212 ≤ 1211` fails). RHS restated at the new `ZetaQ.sideWQ`, whose leading
    terms still carry the paper's `log(q(2T+4))`. `theta0Q` and `prefactorQ` moved in step;
    `theta0Q_one`, `theta0Q_eq`, `theta0Q_le_of_closing` are unchanged in statement and
    still hold. Proved.
  * **F15 `theta0Q_le_theta0Fam`** — was FALSE against the OLD `theta0Q`, exactly as
    diagnosed. **But the prescribed remedy (add `D ≤ T` from `ParamsQ.Valid.D0_le`) turned
    out to be unnecessary**: repairing F16 removes the `sideW` crossover from this statement
    entirely, and it is now proved WITH ITS FROZEN HYPOTHESES UNCHANGED. No hypothesis was
    added anywhere in this file.
--------------------------------------------------------------------------------------
Accordingly Part A takes `hPQ : P.toParams.ValidQ` as an EXPLICIT hypothesis at every call
site (never manufacturing it from `Valid`), so the audit sees it, and Part A additionally
ships `norm_phiHatQ_le_gevrey_abstract`, a `ValidQ`-FREE route to §7.1 through
`Zeta23.Taper.norm_paperFT_le_gevrey` (`GevreyTail.lean:70`), which needs neither `ValidQ`
nor `8w ≤ L`. What the cited lemmas actually consume from `ValidQ` is `taper` and
`one_le_w`; the two `lam` fields are dead weight in the whole §7 chain. Fixing this is a
one-field weakening in [R] (or a `ValidQ'` without `lam_lt_two`), not a mathematical
obstruction — but it is an edit to a frozen file, and so is recorded rather than made.
--------------------------------------------------------------------------------------
-/
import ZetaQ.Defs
import ZetaQ.Certificate

noncomputable section

open scoped BigOperators

namespace ZetaQ

/-! ############################################################################
# PART A — re-exports of Phase-1's §7 at the paper's parameters. ZERO sorries.
############################################################################ -/

/-! ## A.0 Small bridge facts

These are consequences of `ParamsQ.Valid` that Part A uses repeatedly. They are stated
here and not in `Defs.lean` because `Defs.lean` is FROZEN. -/

/-- **§2.2 regime fact.** `0 < T` at any valid design point (from `T_ge : T₀ ≤ T`, `T₀ = 300`).

Paper §2.2. Derivation: `Zeta23.Tail.T₀ = 300` (`Tail/Basic.lean:53`).
Depends on: `ParamsQ.Valid.T_ge`.
Rule 17: no λ, no X, no D₀; `T₀ ≤ T` is an absolute threshold. CLEAN. -/
theorem T_posQ {P : ParamsQ} (hV : P.Valid) : 0 < P.T := by
  have h : (300 : ℝ) ≤ P.T := hV.T_ge
  linarith

/-- **§2.2 regime fact.** `1 ≤ D₀` — the standing buffer regime of the whole Gevrey tail
chain (`PHASE1_INTERFACES` §7.1), from `Valid.two_le_D0`.

Paper §2.2.
Depends on: `ParamsQ.Valid.two_le_D0`.
Rule 17: `D0` is a FIELD; this is `2 ≤ D₀ ⟹ 1 ≤ D₀`, never `D₀ = √T`. CLEAN. -/
theorem one_le_D0Q {P : ParamsQ} (hV : P.Valid) : (1 : ℝ) ≤ P.D0 := by
  have h : (2 : ℝ) ≤ P.D0 := hV.two_le_D0
  linarith

/-- `0 < w` at any valid design point (from `one_le_w` —
`w ≥ 1` is the artifact's validity class shaping the design, paper §10.3's `w = max(1,w*)`).

Paper §10.3. Depends on: `ParamsQ.Valid.one_le_w`.
Rule 17: `w ≥ 1` is not one of the three forbidden facts; recorded at -/
theorem w_posQ {P : ParamsQ} (hV : P.Valid) : 0 < P.w := by
  have h : (1 : ℝ) ≤ P.w := hV.one_le_w
  linarith

/-! ## A.1 — §7.1, the Gevrey transform bound

> For any GevreyProfile(2, A, B) taper with 2w ≤ L, all z ∈ ℂ:
> `‖φ̂(z)‖ ≤ e²·max(2Bw, L)·e^{|Im z|·L/2}·exp(−(2/e)√(w|z|/A))`

**This paper claim needs no new Lean.** It IS `Zeta23.Params.norm_phiHat_le_gevrey`.
RESOLUTION R-1: the Lean hypothesis is `8w ≤ L`, the paper's §7.1 text says `2w ≤ L`;
resolved in favour of the Lean form, since paper §2.2 [eq:wrange] carries `1 ≤ w ≤ L/8`
as a standing convention and §10.3 lists `8w ≤ L` among the design's satisfied side
conditions. `8w ≤ L` is not λ ≤ 1, X ≤ T or D₀ = √T; it is plumbing. -/

/-- **§7.1's envelope constant** `C_env := e²·max(2Bw, L)` at the paper's `L = λℒ`.
Appears inline in [R] as `Real.exp 2 * max (2 * B * P.w) (P.L T)`. -/
def CenvQ (P : ParamsQ) (B : ℝ) : ℝ := Real.exp 2 * max (2 * B * P.w) P.LB

/-- **H4, second half** (paper §2.2): the design profile ϱ₂ is Gevrey-2 at
`(A, B) = (36/e, 2e⁸) = (gevreyA, gevreyB)`.

Paper §2.2, §7.1. Re-export of
`Zeta23.Taper.gevreyProfile_rhoTwo` (`Zeta23/Taper/Gevrey.lean:401`) at `ZetaQ`'s constants.
Depends on: `Zeta23.Taper.gevreyProfile_rhoTwo`.
Rule 17: no parameters at all — a fact about a fixed profile. CLEAN. -/
theorem gevreyProfile_rhoTwoQ :
    Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB Zeta23.Taper.rhoTwo :=
  Zeta23.Taper.gevreyProfile_rhoTwo

/-- **H4, first half** (the proved ramp lemma `‖φ^{(k)}‖₁ ≤ 2B′w(A/w)^k k^{2k}`) in the
`GevreyPhiBound` interface, at the paper's scale `L = λℒ` through the bridge.

The design window is the product `p(u/ℒ)·φ_flat` and the Gevrey constant is
the PRODUCT constant `B′ = gevreyBprod A B = B·Σ_j M_j (w/(ℒA))^j + ½Σ_j M_j (λ/A)^j` (`A` is
unchanged). Re-export of `ParamsQ.Valid.gevreyPhiBound` (`ZetaQ/Window.lean`, from
`Zeta23/Taper/GevreyProduct.lean` `gevrey_polyQ_mul_phi`). Before F58 this was
`Zeta23.Params.gevreyPhiBound_of_profile` at `B` — which needs `GevreyProfile … toParams.ϱ`, false
for the realising profile.
Rule 17: `hw : 8w ≤ L` is [eq:wrange] plumbing. No λ, no X, no D₀. CLEAN. -/
theorem gevreyPhiBoundQ_of_profile (P : ParamsQ) {A B : ℝ}
    (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) (hV : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    P.toParams.GevreyPhiBound P.T 2 A (P.gevreyBprod A B) :=
  hV.gevreyPhiBound hw hϱ

/-- **§7.1, THE paper claim, at the paper's parameters**:
`‖φ̂(z)‖ ≤ e²·max(2Bw, L)·e^{|Im z|·L/2}·exp(−(2/e)√(w‖z‖/A))` for every `z ∈ ℂ`, at
`L = λℒ` and the free buffer regime. Term-by-term identical to the paper's display.

Paper §7.1. At the product window the constant is
`B′ = gevreyBprod A B` (in place of `B`); this is `ParamsQ.Valid.norm_phiHat_le_gevrey`
(`ZetaQ/Window.lean`), i.e. `Zeta23.Taper.norm_paperFT_le_gevrey` fed with the product ramp
bound. Before F58 it was `Zeta23.Params.norm_phiHat_le_gevrey` under `hPQ : P.toParams.ValidQ`,
which is FALSE at the design (FINDING F-0 + F58); the hypothesis is now `hV : P.Valid`.
RESOLUTION R-1 (`8w ≤ L` for the paper's `2w ≤ L`).
Rule 17: `hV : P.Valid` has no `lam_le_one`; `hwL : 8w ≤ L` is [eq:wrange].
No X, no D₀. -/
theorem norm_phiHatQ_le_gevrey (P : ParamsQ) {A B : ℝ}
    (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) (hV : P.Valid)
    (hwL : 8 * P.w ≤ P.LB) (z : ℂ) :
    ‖P.toParams.phiHat P.T z‖
      ≤ Real.exp 2 * max (2 * P.gevreyBprod A B * P.w) P.LB
        * Real.exp (|z.im| * (P.LB / 2))
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A)) :=
  hV.norm_phiHat_le_gevrey hwL hϱ z

/-- **§7.1 at the design profile ϱ₂**, with the envelope constant packaged as `CenvQ`.

Paper §7.1 with `(A, B) = (36/e, 2e⁸)`; F58: the envelope constant is
`CenvQ P B′` with the product constant `B′ = gevreyBprod gevreyA gevreyB`.
Depends on: `norm_phiHatQ_le_gevrey`, `gevreyProfile_rhoTwoQ`.
Rule 17: identical to `norm_phiHatQ_le_gevrey`; `hϱ : P.ϱ = rhoTwo` pins the RAMP only. -/
theorem norm_phiHatQ_le_gevrey_design (P : ParamsQ) (hϱ : P.ϱ = Zeta23.Taper.rhoTwo)
    (hV : P.Valid) (hwL : 8 * P.w ≤ P.LB) (z : ℂ) :
    ‖P.toParams.phiHat P.T z‖
      ≤ CenvQ P (P.gevreyBprod gevreyA gevreyB) * Real.exp (|z.im| * (P.LB / 2))
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / gevreyA)) := by
  have hprof : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ := by
    rw [hϱ]; exact gevreyProfile_rhoTwoQ
  unfold CenvQ
  exact norm_phiHatQ_le_gevrey P hprof hV hwL z

/-- **§7.1, the `ValidQ`-FREE route** (see FINDING F-0). The abstract envelope
`Zeta23.Taper.norm_paperFT_le_gevrey` (`Zeta23/Tail/GevreyTail.lean:70`) needs neither
`Params.ValidQ` nor `8w ≤ L`: it takes the four analytic facts about the window directly.
Stated at half-support `Λ = L/2`, which is exactly `supp φ = [−L/2, L/2]`.

Paper §7.1, abstract-taper form.
Depends on: `Zeta23.Taper.norm_paperFT_le_gevrey`.
Rule 17: no `Params` validity class is used at all, hence structurally no `lam` hypothesis;
no X, no D₀. **CLEAN, and satisfiable at the design of record** — unlike the `ValidQ` route. -/
theorem norm_phiHatQ_le_gevrey_abstract (P : ParamsQ) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hw : 0 < P.w) (hL : 0 < P.LB)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => (P.phiQ u : ℂ)))
    (hsupp : ∀ u, (fun u => (P.phiQ u : ℂ)) u ≠ 0 → |u| ≤ P.LB / 2)
    (hL1 : ∫ u, ‖(fun u => (P.phiQ u : ℂ)) u‖ ≤ 2 * (P.LB / 2))
    (hbound : ∀ k : ℕ, 1 ≤ k →
      ∫ u, ‖iteratedDeriv k (fun u => (P.phiQ u : ℂ)) u‖
        ≤ 2 * B * P.w * (A / P.w) ^ k * (k : ℝ) ^ ((2 : ℝ) * k))
    (z : ℂ) :
    ‖Zeta23.paperFT (fun u => (P.phiQ u : ℂ)) z‖
      ≤ Real.exp 2 * max (2 * B * P.w) (2 * (P.LB / 2))
        * Real.exp (|z.im| * (P.LB / 2))
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A)) :=
  Zeta23.Taper.norm_paperFT_le_gevrey (φ := fun u => (P.phiQ u : ℂ)) (Λ := P.LB / 2)
    (A := A) (B := B) (w := P.w) hA hB hw (by linarith) hsm hsupp hL1 hbound z

/-! ## A.2 — §7.2, the parts that ARE the [R]-tree per-block chain

Every row below is a Phase-1 theorem re-stated at `P.toParams`, `P.T` and the FREE buffer
`P.D0`. The `√T`-specific originals (`Zeta23.Tail.TailHyp.tailInputs`, `Tail.NII_le`,
`Tail.InTail`, `Zeta23.Assembly.TailInputs`) are on the DO-NOT-CITE list of RESOLUTION R-4
and appear nowhere in this file. -/

/-- **§7.2, tail geometry at the free buffer**: a tail zero at buffer `D₀` is at distance
`≥ D₀` from `I = [T, 2T]`.

Paper §7.2. Re-export of `Zeta23.Tail.le_distI_of_InTailD`
(`Zeta23/Tail/GevreyTail.lean:552`) at `D := P.D0`.
Depends on: `T_posQ`, `one_le_D0Q`.
Rule 17: the buffer is the FIELD `P.D0` and the predicate is `InTailD` — never
`Zeta23.Tail.InTail`, whose body unfolds to `Real.sqrt T`. CLEAN. -/
theorem buffer_le_distI {P : ParamsQ} (hV : P.Valid) {γ : ℝ}
    (h : Zeta23.Tail.InTailD P.T P.D0 γ) : P.D0 ≤ Zeta23.Tail.distI P.T γ :=
  Zeta23.Tail.le_distI_of_InTailD (T_posQ hV).le (by linarith [one_le_D0Q hV]) h

/-- **§7.2, QT.b(1): the entry bound.** Under the §7.1 envelope in strip form, every entry
of the Gram column `u_ρ` at a zero in the critical strip obeys
`‖u_ρ(k)‖ ≤ Kg·e^{−c√(b|γ−τ_k|)}`, with the grid step `h = 2π/L` of paper §2.2.

Paper §7.2. Re-export of `Zeta23.Tail.norm_uvec_le_gevrey`
(`Zeta23/Tail/GevreyTail.lean:562`); PHASE1_INTERFACES §7.3 item 3: there is deliberately
NO tail hypothesis (the Gevrey envelope is entire).
Depends on: `ZetaQ.ParamsQ.toParams_L`.
Rule 17: no buffer occurs at all; no λ, no X. CLEAN. -/
theorem norm_uvecQ_le_gevrey (P : ParamsQ) {Z : Zeta23.ZeroConfig}
    (hl : Zeta23.l P.T ≠ 0) {Kg b c : ℝ}
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 →
      ‖P.toParams.phiHat P.T ((r : ℂ) - Complex.I * (y : ℂ))‖
        ≤ Kg * Real.exp (-c * Real.sqrt (b * |r|)))
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (k : Fin (P.toParams.d P.T)) :
    ‖Zeta23.Tail.uvec P.toParams P.T ρ k‖
      ≤ Kg * Real.exp (-c * Real.sqrt (b * |ρ.im - (P.T + (k : ℕ) * P.hgridQ)|)) := by
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have key := Zeta23.Tail.norm_uvec_le_gevrey (Z := Z) (P := P.toParams) (T := P.T)
    hdecay hρ k
  rw [hLb] at key
  exact key

/-- **§7.2, QT.b(2)+(3): the two-factor squared row bound.** "Each squared Gram-column entry
carries BOTH taper factors at the same argument … giving suppression
`exp(−(4/e)√(w·dist/A))` per entry" — here the doubled rate is the `2*c` and the row weight
is `rowS L b (2c)`.

Paper §7.2. Re-export of `Zeta23.Tail.norm_sq_uvec_le_gevrey`
(`Zeta23/Tail/GevreyTail.lean:582`). PHASE1_INTERFACES §7.3 item 4: `hdist : 1 ≤ distI` is
passed DIRECTLY, not derived from a tail predicate — supply it from `buffer_le_distI`.
Depends on: `ZetaQ.ParamsQ.toParams_L`.
Rule 17: `hdist` is about `distI`, not about any buffer value; no λ, no X, no D₀. CLEAN. -/
theorem norm_sq_uvecQ_le_gevrey (P : ParamsQ) {Z : Zeta23.ZeroConfig} (hV : P.Valid)
    (hl : Zeta23.l P.T ≠ 0) (hL : 2 ≤ P.LB) {Kg b c : ℝ}
    (hKg : 0 ≤ Kg) (hb : 0 < b) (hc : 0 < c)
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 →
      ‖P.toParams.phiHat P.T ((r : ℂ) - Complex.I * (y : ℂ))‖
        ≤ Kg * Real.exp (-c * Real.sqrt (b * |r|)))
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hdist : 1 ≤ Zeta23.Tail.distI P.T ρ.im) :
    ∑ k, ‖Zeta23.Tail.uvec P.toParams P.T ρ k‖ ^ 2
      ≤ Kg ^ 2 * Real.exp (-(2 * c) * Real.sqrt (b * Zeta23.Tail.distI P.T ρ.im))
          * Zeta23.Tail.rowS P.LB b (2 * c) (Zeta23.Tail.distI P.T ρ.im) := by
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have key := Zeta23.Tail.norm_sq_uvec_le_gevrey (Z := Z) (P := P.toParams) (T := P.T)
    hV.T_ge (by rw [hLb]; exact hL) hKg hb hc hdecay hρ hdist
  rw [hLb] at key
  exact key

/-- the `hdecay` field of `TailHypG`/`TailHypQ` from the §7.1 envelope (F58 helper). -/
theorem hdecay_of_envelope {P : Zeta23.Params} {T A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hw : 0 < P.w) (hL0 : 0 < P.L T)
    (henv : ∀ z : ℂ, ‖P.phiHat T z‖
      ≤ Real.exp 2 * max (2 * B * P.w) (P.L T) * Real.exp (|z.im| * (P.L T / 2))
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A))) :
    ∀ (r y : ℝ), |y| ≤ 1 / 2 →
      ‖P.phiHat T ((r : ℂ) - Complex.I * (y : ℂ))‖
        ≤ (Real.exp (P.L T / 4) * (Real.exp 2 * max (2 * B * P.w) (P.L T)))
          * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w / A * |r|)) := by
  intro r y hy
  have hL0 : 0 < P.L T := by linarith
  have h := henv ((r : ℂ) - Complex.I * (y : ℂ))
  have him : ((r : ℂ) - Complex.I * (y : ℂ)).im = -y := by simp
  have hre : ((r : ℂ) - Complex.I * (y : ℂ)).re = r := by simp
  have hnorm : |r| ≤ ‖(r : ℂ) - Complex.I * (y : ℂ)‖ := by
    calc |r| = |((r : ℂ) - Complex.I * (y : ℂ)).re| := by rw [hre]
      _ ≤ ‖(r : ℂ) - Complex.I * (y : ℂ)‖ := Complex.abs_re_le_norm _
  have hexp1 : Real.exp (|((r : ℂ) - Complex.I * (y : ℂ)).im| * (P.L T / 2))
      ≤ Real.exp (P.L T / 4) := by
    rw [Real.exp_le_exp, him, abs_neg]
    nlinarith [abs_nonneg y]
  have hexp2 : Real.exp (-(2 / Real.exp 1)
        * Real.sqrt (P.w * ‖(r : ℂ) - Complex.I * (y : ℂ)‖ / A))
      ≤ Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w / A * |r|)) := by
    rw [Real.exp_le_exp]
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
        have hc0 : (0:ℝ) ≤ Real.exp 2 * max (2 * B * P.w) (P.L T) := by positivity
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hexp1 hc0
        · exact hexp2
        · positivity
        · positivity
    _ = Real.exp (P.L T / 4) * (Real.exp 2 * max (2 * B * P.w) (P.L T))
          * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w / A * |r|)) := by ring

/-- **`Zeta23.Tail.TailHypG.of_profile` with the envelope taken as a
HYPOTHESIS** (the `of_phiBound` form): for any
`P : Zeta23.Params`, the §7.1 envelope `‖φ̂(z)‖ ≤ e²·max(2Bw, L)·e^{|Im z|L/2}·exp(−(2/e)√(w‖z‖/A))`
(for all `z ∈ ℂ`) supplies the `TailHypG` bundle at `C_env = e²·max(2Bw, L)`. The proof is
`of_profile`'s `hdecay` verbatim with the envelope substituted for
`Zeta23.Params.norm_phiHat_le_gevrey`; `of_profile` is the special case (flat taper,
`GevreyProfile 2 A B P.ϱ` + `P.ValidQ`), and the design window is the case
`B := gevreyBprod A B` through `ParamsQ.Valid.norm_phiHat_le_gevrey`. Placed here rather than in
`Zeta23/Tail/GevreyTail.lean` so that no Phase-1 file is touched.
Rule 17: no validity class at all; `hD : 1 ≤ D`, buffer FREE. CLEAN. -/
theorem _root_.Zeta23.Tail.TailHypG.of_envelope {Z : Zeta23.ZeroConfig} {P : Zeta23.Params}
    {T A₀ A B D : ℝ} (hA : 0 < A) (hB : 0 < B) (hw : 0 < P.w)
    (hT : Zeta23.Tail.T₀ ≤ T) (hL : 2 ≤ P.L T) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (hD : 1 ≤ D)
    (henv : ∀ z : ℂ, ‖P.phiHat T z‖
      ≤ Real.exp 2 * max (2 * B * P.w) (P.L T) * Real.exp (|z.im| * (P.L T / 2))
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A))) :
    Zeta23.Tail.TailHypG Z P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) D where
  hT := hT
  hL := hL
  hA₀ := hA₀
  hloc := hloc
  hA := hA
  hCenv := by
    have hL0 : 0 < P.L T := by linarith
    positivity
  hw := hw
  hD := hD
  hdecay := hdecay_of_envelope hA hB hw (by linarith) henv

/-- **§7.2, the QT.a ⟹ QT.b bridge at the paper's parameters.** A Gevrey-2 profile at
`(A, B)` supplies the whole `TailHypG` bundle at `C_env = e²·max(2Bw, L)` and the FREE
buffer `P.D0`.

Paper §7.1 → §7.2 seam (526). At the product window the
envelope constant is `C_env = e²·max(2B′w, L)`, `B′ = gevreyBprod A B`; the bridge is
`TailHypG.of_envelope` (above) fed with `ParamsQ.Valid.norm_phiHat_le_gevrey`. Before F58 it
was `Zeta23.Tail.TailHypG.of_profile` under `hPQ : P.toParams.ValidQ` (FALSE at the design).
Depends on: `TailHypG.of_envelope`, `ParamsQ.Valid.norm_phiHat_le_gevrey`,
`one_le_D0Q`.
Rule 17: `hD` is `1 ≤ P.D0`, derived from the FIELD condition `Valid.two_le_D0` — never
from `√T ≥ 17`. `hV : P.Valid` has no `lam_le_one`. `hloc` is [R]'s
`log(|t|+3)` count; the paper's q-uniform `log(q(|t|+3))` is PART B (`TailHypQ`). CLEAN. -/
theorem tailHyp_of_profileQ (P : ParamsQ) {Z : Zeta23.ZeroConfig} {A B A₀ : ℝ}
    (hV : P.Valid) (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ)
    (hwL : 8 * P.w ≤ P.LB) (hL : 2 ≤ P.LB) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    Zeta23.Tail.TailHypG Z P.toParams P.T A₀ A
      (Real.exp 2 * max (2 * P.gevreyBprod A B * P.w) P.LB) P.D0 := by
  have hLb : P.toParams.L P.T = P.LB := hV.toParams_L
  have key := Zeta23.Tail.TailHypG.of_envelope (Z := Z) (P := P.toParams) (T := P.T)
    (A₀ := A₀) (D := P.D0) hϱ.A_pos (hV.gevreyBprod_pos hϱ.A_pos hϱ.B_pos) hV.w_pos hV.T_ge
    (by rw [hLb]; exact hL) hA₀ hloc (one_le_D0Q hV)
    (fun z => by rw [hLb]; exact hV.norm_phiHat_le_gevrey hwL hϱ z)
  rw [hLb] at key
  exact key

/-- **§7.2, QT.b(1)–(4) combined, at the paper's `L = λℒ`**: finite partial sums over
tail-at-`D₀` zeros satisfy `∑ m_ρ‖u_ρ‖₂² ≤ L·θ₀G`.

Paper §7.2 ("Row sums by exponential telescoping, window sums by the …
local count"). Re-export of `Zeta23.Tail.TailHypG.partial_sum_leG`
(`Zeta23/Tail/GevreyTail.lean:1494`).
Depends on: `ZetaQ.ParamsQ.toParams_L`.
Rule 17: the buffer slot of `TailHypG` is instantiated at the FIELD `P.D0`; `theta0G`'s
own body mentions no `D0 T` and no `Real.sqrt T`. CLEAN. -/
theorem tail_partial_sum_le (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) {Z : Zeta23.ZeroConfig}
    {A₀ A Cenv : ℝ} (H : Zeta23.Tail.TailHypG Z P.toParams P.T A₀ A Cenv P.D0)
    (u : Finset {ρ : Z.carrier // ρ ∉ H.sAD}) :
    ∑ x ∈ u, (Z.mult (x : Z.carrier) : ℝ)
        * ∑ k, ‖Zeta23.Tail.uvec P.toParams P.T (x : Z.carrier) k‖ ^ 2
      ≤ P.LB * Zeta23.Tail.theta0G P.toParams P.T A₀ A Cenv P.D0 := by
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have key := H.partial_sum_leG u
  rw [hLb] at key
  exact key

/-- **§7.2, "‖Ẽ_χ‖ ≤ θ₀", the per-block half.** (T1) every eigenvalue of `Ẽ(D₀)` has
`|λ| ≤ θ₀G` and `‖Ẽ(D₀)‖₁ ≤ θ₀G`; (T2) `‖Ê(D₀)‖₁ ≤ θ₀G/(aL)`.

Paper §7.2 ("Either way ‖Ẽ_χ‖ ≤ θ₀"). Re-export of
`Zeta23.Tail.TailHypG.prop_tailG` (`Zeta23/Tail/GevreyTail.lean:1746`); the "uniformly over
the family" half is PART B (`theta0Q_le_theta0Fam`).
Depends on: Phase 1.
Rule 17: buffer is the FIELD `P.D0`; `ha : 0 < a` is a normalisation positivity. CLEAN. -/
theorem prop_tailQ (P : ParamsQ) {Z : Zeta23.ZeroConfig} {A₀ A Cenv : ℝ}
    (H : Zeta23.Tail.TailHypG Z P.toParams P.T A₀ A Cenv P.D0)
    (ha : 0 < P.toParams.a P.T)
    (hEt : (P.toParams.tilde P.T (Z.EzD P.toParams P.T P.D0)).IsHermitian)
    (hEh : (P.toParams.hat P.T (Z.EzD P.toParams P.T P.D0)).IsHermitian) :
    (∀ i, |hEt.eigenvalues i| ≤ Zeta23.Tail.theta0G P.toParams P.T A₀ A Cenv P.D0) ∧
      Zeta23.Tail.traceNorm hEt
        ≤ Zeta23.Tail.theta0G P.toParams P.T A₀ A Cenv P.D0 ∧
      Zeta23.Tail.traceNorm hEh
        ≤ Zeta23.Tail.theta0G P.toParams P.T A₀ A Cenv P.D0
            / (P.toParams.a P.T * P.toParams.L P.T) :=
  H.prop_tailG ha hEt hEh

/-- **§7.2, QT.b(5): the free-buffer tail package at the paper's parameters.** The Gevrey
tail feeds the θ₀-generic assembly interface `Assembly.TailInputsD` with the buffer FREE.

Paper §7.2; companion notes §QT.b(5) with its R8 CORRECTION (RESOLUTION R-4:
`Zeta23.Tail.TailHyp.tailInputs`, `Tail.lean:579`, is on the DO-NOT-CITE list because its
conclusion instantiates at `D₀² = T`; the correct citation is `TailHypG.tailInputsD`).
Re-export of `Zeta23.Tail.TailHypG.tailInputsD` (`Zeta23/Tail/GevreyTail.lean:1777`)
composed with `tailHyp_of_profileQ`.
Depends on: `tailHyp_of_profileQ`.
Rule 17: buffer is the FIELD `P.D0`; the target structure is `TailInputsD` (D-generic),
never `Assembly.TailInputs` (whose `D` is `√T`). See FINDING F-0 re `hPQ`. CLEAN. -/
theorem tailInputs_of_profileQ (P : ParamsQ) {Z : Zeta23.ZeroConfig} {A B A₀ : ℝ}
    (hV : P.Valid) (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ)
    (hwL : 8 * P.w ≤ P.LB) (hL : 2 ≤ P.LB) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (ha : 0 < P.toParams.a P.T)
    (hconj : ∀ z : ℂ, P.toParams.phiHat P.T ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (P.toParams.phiHat P.T z)) :
    Zeta23.Assembly.TailInputsD Z P.toParams P.T P.D0
      (Zeta23.Tail.theta0G P.toParams P.T A₀ A
        (Real.exp 2 * max (2 * P.gevreyBprod A B * P.w) P.LB) P.D0) :=
  (tailHyp_of_profileQ P hV hϱ hwL hL hA₀ hloc).tailInputsD ha hconj

/-- **§7.2, QT.b(5)'s buffer count**: `N(I′(D₀)∖I) ≤ 3A₀·D₀·log 4T` at the FREE buffer.
This is the row that feeds §9/§10's budget row L₄.

Paper §7.2; companion notes §QT.b(5). Re-export of `Zeta23.Tail.NIID_le`
(`Zeta23/Tail/GevreyTail.lean:1878`). NOTE: `Zeta23.Tail.NII_le` (`Tail.lean:593`) is
`√T`-specific and is on the DO-NOT-CITE list (RESOLUTION R-4).
Depends on: `ParamsQ.Valid.two_le_D0`,
`ParamsQ.Valid.D0_le`.
Rule 17: this is the single place the two STRICTLY STRONGER buffer facts `2 ≤ D₀` and
`D₀ + 4 ≤ T` are consumed (PHASE1_INTERFACES §7.1). [R] got both free from `√T ≥ 17`; ours
come from the `Valid` FIELDS, which is exactly why they are fields. **No `√T` anywhere.** -/
theorem NIID_le_Q (P : ParamsQ) (hV : P.Valid) (Z : Zeta23.ZeroConfig) {A₀ : ℝ}
    (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    (Zeta23.Assembly.NIID Z P.T P.D0 : ℝ) ≤ 3 * A₀ * P.D0 * Real.log (4 * P.T) :=
  Zeta23.Tail.NIID_le Z hA₀ hloc hV.T_ge hV.two_le_D0 hV.D0_le

/-! ## A.3 — §7.3, the scalar perturbation lemma the pair version generalizes

> §7.3: "…generalizing [R]'s scalar version, which is the case `B_tr = B_F`"

`Zeta23.Assembly.four_tr_sub_frobSq_perturb` (`Zeta23/Assembly.lean:150`) is already stated
at full generality over `RCLike 𝕜` and needs no re-export at ParamsQ: it mentions no
`Params`, no `T`, no buffer. It is cited directly by PART B's `_pair_diag` consistency
check. Recorded here for the ledger; no Lean statement. -/

/-! ############################################################################
# PART B — the genuinely new statements. All are PROVED; this file has no `sorry`.
############################################################################ -/

/-! ## B.1 — the q-uniform window row-sum (χ-mirror of `tail_rowsum_exp_le`)

> **§7.2** "window sums by the q-uniform local count (§9)"
> **§2.1 (H6)** "the q-uniform local count `N_χ(t, t+1] ≤ A₀·log(q(|t|+3))` with absolute A₀"

**KEY RECONNAISSANCE FINDING.** `Zeta23.Tail.one_side_exp_sum_le`
(`GevreyTail.lean:1082`) already takes the window-log base `B` as a FREE parameter
(`hB : 1 ≤ B`); only `Zeta23.Tail.tail_rowsum_exp_le` (`:1287`) hardcodes `B = 2T+4`,
because it derives its `hcount` from `Zeta23.Tail.LocalCount`, whose `window` field is
`≤ A₀·log(|t|+3)`. So the ENTIRE q-uniform mirror of §7.2's window sums costs ONE
structure and ONE theorem, not a rebuild of the chain. -/

/-- **H6 in the abstract shape [R]'s tail machinery consumes**: the q-uniform unit-window
local count `N_χ(t, t+1] ≤ A₀·log(q(|t|+3))`.

Paper §2.1 H6 ( ff.), consumed at §7.2. 
`LEMMA_QT` §QT.b(4). Mirror of `Zeta23.Tail.LocalCount` (`Zeta23/Tail/Basic.lean:66`)
with the conductor inside the log.
Depends on: nothing.
Rule 17: `q` is a bare real ≥ 1; no λ, no X, no buffer. CLEAN. -/
structure LocalCountQ {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ) (A₀ q : ℝ) : Prop where
  /-- `A₀ ≥ 1`, absolute (E9-explicit, carried per block). -/
  one_le : 1 ≤ A₀
  /-- the conductor is at least 1. -/
  one_le_q : 1 ≤ q
  /-- the two-sided unit-window count, uniform in `q`. -/
  window : ∀ t : ℝ, ∀ s : Finset ι, (∀ ρ ∈ s, t < γ ρ ∧ γ ρ ≤ t + 1) →
    (∑ ρ ∈ s, (m ρ : ℝ)) ≤ A₀ * Real.log (q * (|t| + 3))

/-- **The q-uniform window weight.** `sideWQ L b c B D q := (1 + log q / log B)·sideW L b c B D`,
to be read at the [R] base `B = 2T+4`.

⚠ **THIS DEFINITION IS PART OF THE REPAIR OF FINDING F16 (decision D14)**; see
`tail_rowsum_exp_le_Q` for the full diagnosis. Expanding `Zeta23.Tail.sideW`
(`GevreyTail.lean:1054`), with `α = 1 + (L/2π)(2/b)(√b/c+1/c²)` and `β = (L/2π)(2/b)/c`,

  `sideWQ L b c B D q = (α·monoW₀ + β·monoW₁)·log(qB) + (1 + log q/log B)·(α·monoW₂+β·monoW₃)/(bB)`.

So **the leading (window-count) terms carry exactly the paper's q-uniform window-log base
`log(q(2T+4))`** — which is what §7.2's "window sums by the q-uniform local count" asserts —
while the two `1/(bB)` telescoping remainders are charged the same ratio
`log(qB)/log B` rather than being divided by `q`. That last point is the whole content of
F16: the frozen skeleton wrote the whole thing as `sideW L b c (q(2T+4)) D`, which divides
those remainders BY `q`, and no proof supplies that.

`q = 1` gives back `sideW` on the nose (`Real.log 1 = 0`), with no side condition — see
`theta0Q_one`.

Paper §7.2.
Rule 17: `D` and `B` are bare reals; no `D0`, no `√T`, no λ, no X. CLEAN. -/
def sideWQ (L b c B D q : ℝ) : ℝ :=
  (1 + Real.log q / Real.log B) * Zeta23.Tail.sideW L b c B D

/-- **§7.2's window sums at a q-uniform local count** (QT.b(4)): the two-sided collection of
the row weights over unit windows at distances `D, D+1, …` from `I` on both sides, at the
q-uniform window weight `sideWQ`.

⚠ **REPAIR OF A FALSE/UNPROVABLE RHS (decision D14).** The frozen skeleton put
`sideW L b c (q(2T+4)) D` on the right and prescribed the proof "feed
`Zeta23.Tail.one_side_exp_sum_le` twice, editing the `hcount` leg from `|t|+3 ≤ B+j` to
`q(|t|+3) ≤ q(2T+4)+j`". **That leg does not exist.** `one_side_exp_sum_le`
(`GevreyTail.lean:1082`) demands `hcount` for EVERY `j : ℕ`, and on the upper side the
window centre is `t = 2T+j`, so the requirement is

  `q(2T+j+3) ≤ q(2T+4) + j`  for all `j`, i.e.  `j(q−1) ≤ q`,

**false at `q = 2, T = 300, j = 3`** (`1212 ≤ 1211` — machine-checked). The lower side fails
the same way (`j(q−1) ≤ qT`). Nothing repairs the leg: no single base `B` can satisfy
`q(2T+j+3) ≤ B + j` for all `j` once `q > 1`.

**And the frozen RHS is genuinely short, not merely hard.** Writing `α, β` as in `sideWQ`,

  `sideW L b c (q(2T+4)) D = (α·monoW₀+β·monoW₁)·log(q(2T+4)) + (α·monoW₂+β·monoW₃)/(q·b(2T+4))`,

so it charges the telescoping remainder at `1/q` of its [R] value. The honest bound keeps
that remainder — the deficit is `2A₀(1−1/q)(α·monoW₂+β·monoW₃)/(b(2T+4))`, which **dominates
once `D ≫ T²`** (`monoW₂/monoW₀ ≍ bD`, so the remainder overtakes the log terms exactly at
the `sideW` crossover of `sideW_mono_base`).

**What the statement now says, and why it is the paper's own claim.** The proof applies
`one_side_exp_sum_le` at [R]'s base `B = 2T+4` and at the inflated count constant
`A₀' := A₀·(1 + log q/log(2T+4)) = A₀·log(q(2T+4))/log(2T+4)`, whose `hcount` leg IS valid
for every `j`: `A₀ log(q(|t|+3)) = A₀ log q + A₀ log(|t|+3) ≤ A₀'·log(B+j)`, using only
`log(|t|+3) ≤ log(B+j)` and `log B ≤ log(B+j)`. The result is `2A₀·sideWQ`, whose leading
terms carry the paper's `log(q(2T+4))` verbatim. Relative to the tightest possible RHS
(`sideW L b c (2T+4) D + log q·(α·monoW₀+β·monoW₁) = S·log(qB) + R`, which would need
`one_side_exp_sum_le` re-proved from scratch rather than cited — it is not citable, being
the very leg that fails) this is larger by `(log q/log B)·R`, i.e. by the fraction
`R/(S·log B)` of the `log q` correction, where `S = α·monoW₀+β·monoW₁` and
`R = (α·monoW₂+β·monoW₃)/(bB)` are `sideW`'s window-count and telescoping-remainder parts.
Since `R/S ≍ D/(2T+4)`, that fraction is `≍ D/((2T+4)·log(2T+4))`: measured at
`b = 1, c = 4/e, T = 300` it is `1.3%` at `D = 10` and `12%` at `D = T = 300`. Always in the
conservative direction. **This is a strengthening of the RHS, not a weakening: the frozen
form was not provable and was not true of the underlying sum.**

Paper §7.2. Derivation: `LEMMA_QT` §QT.b(4). Mirror of
`Zeta23.Tail.tail_rowsum_exp_le` (`Zeta23/Tail/GevreyTail.lean:1287`).
Depends on: `Zeta23.Tail.one_side_exp_sum_le`, `sideW`, `rowS`,
`InTailD`, `distI`.
Rule 17: `hD : 1 ≤ D` — buffer FREE, no `D0 T`, no `Real.sqrt T`. No `P.lam` occurs, so no
λ ≤ 1 can hide. No `X`. `hT : T₀ ≤ T` is the absolute threshold `300 ≤ T`. CLEAN. -/
theorem tail_rowsum_exp_le_Q {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ q T D L b c : ℝ}
    (hN : LocalCountQ γ m A₀ q) (hT : Zeta23.Tail.T₀ ≤ T) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hb : 0 < b) (hc : 0 < c)
    (s : Finset ι) (hs : ∀ ρ ∈ s, Zeta23.Tail.InTailD T D (γ ρ)) :
    ∑ ρ ∈ s, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * Zeta23.Tail.distI T (γ ρ)))
          * Zeta23.Tail.rowS L b c (Zeta23.Tail.distI T (γ ρ)))
      ≤ 2 * A₀ * (Real.exp (-c * Real.sqrt (b * D))
          * sideWQ L b c (2 * T + 4) D q) := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA₀ : 0 ≤ A₀ := by linarith [hN.one_le]
  have hq1 : (1 : ℝ) ≤ q := hN.one_le_q
  have hq0 : (0 : ℝ) < q := by linarith
  set B : ℝ := 2 * T + 4 with hBdef
  have hB : (1 : ℝ) ≤ B := by rw [hBdef]; linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by rw [hBdef]; linarith)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  set A₀' : ℝ := A₀ * (1 + Real.log q / Real.log B) with hA₀'def
  have hratio : (0 : ℝ) ≤ Real.log q / Real.log B := div_nonneg hlogq hlogB.le
  have hA₀' : 0 ≤ A₀' := by rw [hA₀'def]; nlinarith
  -- split s into the lower side (γ ≤ T − D, includes all γ ≤ 0) and the upper side
  set slo := s.filter (fun ρ => γ ρ ≤ T - D) with hslo
  set shi := s.filter (fun ρ => ¬ γ ρ ≤ T - D) with hshi
  have hshi_mem : ∀ ρ ∈ shi, 2 * T + D < γ ρ := by
    intro ρ hρ
    rw [hshi, Finset.mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact absurd h hρ.2
    · exact h
  have hsum_split : ∑ ρ ∈ s, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * Zeta23.Tail.distI T (γ ρ)))
          * Zeta23.Tail.rowS L b c (Zeta23.Tail.distI T (γ ρ)))
      = (∑ ρ ∈ slo, (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * Zeta23.Tail.distI T (γ ρ)))
            * Zeta23.Tail.rowS L b c (Zeta23.Tail.distI T (γ ρ))))
        + ∑ ρ ∈ shi, (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * Zeta23.Tail.distI T (γ ρ)))
            * Zeta23.Tail.rowS L b c (Zeta23.Tail.distI T (γ ρ))) :=
    (Finset.sum_filter_add_sum_filter_not s _ _).symm
  -- THE REPAIRED COUNT LEG: `A₀·log(q(|t|+3)) ≤ A₀'·log(B+j)` whenever `|t|+3 ≤ B+j`.
  have hlogmonoQ : ∀ (t : ℝ) (j : ℕ), |t| + 3 ≤ B + (j : ℝ) →
      A₀ * Real.log (q * (|t| + 3)) ≤ A₀' * Real.log (B + (j : ℝ)) := by
    intro t j h
    have ht0 : (0 : ℝ) < |t| + 3 := by positivity
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hlt : Real.log (|t| + 3) ≤ Real.log (B + (j : ℝ)) := Real.log_le_log ht0 h
    have hlB : Real.log B ≤ Real.log (B + (j : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hmul : Real.log (q * (|t| + 3)) = Real.log q + Real.log (|t| + 3) :=
      Real.log_mul (ne_of_gt hq0) (ne_of_gt ht0)
    have hinv : Real.log q / Real.log B * Real.log B = Real.log q := by
      field_simp
    have hstep : Real.log q ≤ Real.log q / Real.log B * Real.log (B + (j : ℝ)) := by
      linarith [mul_le_mul_of_nonneg_left hlB hratio]
    have hexp : (1 + Real.log q / Real.log B) * Real.log (B + (j : ℝ))
        = Real.log (B + (j : ℝ)) + Real.log q / Real.log B * Real.log (B + (j : ℝ)) := by
      ring
    have hall : Real.log (q * (|t| + 3))
        ≤ (1 + Real.log q / Real.log B) * Real.log (B + (j : ℝ)) := by
      rw [hmul, hexp]; linarith
    calc A₀ * Real.log (q * (|t| + 3))
        ≤ A₀ * ((1 + Real.log q / Real.log B) * Real.log (B + (j : ℝ))) :=
          mul_le_mul_of_nonneg_left hall hA₀
      _ = A₀' * Real.log (B + (j : ℝ)) := by rw [hA₀'def]; ring
  ---------------- lower side: x = T − γ, key = ⌊T − γ⌋₊ ----------------
  have hlo : ∑ ρ ∈ slo, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * Zeta23.Tail.distI T (γ ρ)))
          * Zeta23.Tail.rowS L b c (Zeta23.Tail.distI T (γ ρ)))
      ≤ A₀' * (Real.exp (-c * Real.sqrt (b * D)) * Zeta23.Tail.sideW L b c B D) := by
    have hmem : ∀ ρ ∈ slo, γ ρ ≤ T - D := fun ρ hρ => (Finset.mem_filter.mp hρ).2
    have e : ∀ ρ ∈ slo, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * Zeta23.Tail.distI T (γ ρ)))
          * Zeta23.Tail.rowS L b c (Zeta23.Tail.distI T (γ ρ)))
        = (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * (T - γ ρ)))
            * Zeta23.Tail.rowS L b c (T - γ ρ)) := by
      intro ρ hρ
      rw [Zeta23.Tail.distI_of_le hT0 (by linarith [hmem ρ hρ, hD])]
    rw [Finset.sum_congr rfl e]
    apply Zeta23.Tail.one_side_exp_sum_le slo (fun ρ => T - γ ρ) m (fun ρ => ⌊T - γ ρ⌋₊)
      hA₀' hB hD hL hb hc
    · intro ρ hρ; linarith [hmem ρ hρ]
    · intro ρ hρ; exact Nat.floor_le (by linarith [hmem ρ hρ, hD])
    · intro ρ hρ; exact (Nat.lt_floor_add_one _).le
    · intro j
      refine (hN.window (T - j - 1) _ ?_).trans (hlogmonoQ _ _ ?_)
      · intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hnn : 0 ≤ T - γ ρ := by linarith [hmem ρ hρs, hD]
        have := (Nat.floor_eq_iff hnn).mp hρj
        constructor <;> linarith [this.1, this.2]
      · have : |T - j - 1| ≤ T + j + 1 := by
          rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
        rw [hBdef]; linarith
  ---------------- upper side: x = γ − 2T, key = ⌈γ − 2T⌉₊ − 1 ----------------
  have hhi : ∑ ρ ∈ shi, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * Zeta23.Tail.distI T (γ ρ)))
          * Zeta23.Tail.rowS L b c (Zeta23.Tail.distI T (γ ρ)))
      ≤ A₀' * (Real.exp (-c * Real.sqrt (b * D)) * Zeta23.Tail.sideW L b c B D) := by
    have hmem := hshi_mem
    have e : ∀ ρ ∈ shi, (m ρ : ℝ)
        * (Real.exp (-c * Real.sqrt (b * Zeta23.Tail.distI T (γ ρ)))
          * Zeta23.Tail.rowS L b c (Zeta23.Tail.distI T (γ ρ)))
        = (m ρ : ℝ)
          * (Real.exp (-c * Real.sqrt (b * (γ ρ - 2 * T)))
            * Zeta23.Tail.rowS L b c (γ ρ - 2 * T)) := by
      intro ρ hρ
      rw [Zeta23.Tail.distI_of_ge hT0 (by linarith [hmem ρ hρ, hD])]
    rw [Finset.sum_congr rfl e]
    have hceil1 : ∀ ρ ∈ shi, 1 ≤ ⌈γ ρ - 2 * T⌉₊ := fun ρ hρ =>
      Nat.one_le_ceil_iff.mpr (by linarith [hmem ρ hρ, hD])
    have hcast : ∀ ρ ∈ shi, (((⌈γ ρ - 2 * T⌉₊ - 1 : ℕ) : ℝ)) = ⌈γ ρ - 2 * T⌉₊ - 1 :=
      fun ρ hρ => by rw [Nat.cast_sub (hceil1 ρ hρ)]; simp
    apply Zeta23.Tail.one_side_exp_sum_le shi (fun ρ => γ ρ - 2 * T) m
      (fun ρ => ⌈γ ρ - 2 * T⌉₊ - 1) hA₀' hB hD hL hb hc
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
      refine (hN.window (2 * T + j) _ ?_).trans (hlogmonoQ _ _ ?_)
      · intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hc1 : ⌈γ ρ - 2 * T⌉₊ = j + 1 := by have := hceil1 ρ hρs; omega
        have := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc1
        push_cast at this
        constructor <;> linarith [this.1, this.2]
      · rw [abs_of_nonneg (by positivity), hBdef]; linarith
  ---------------- combine ----------------
  rw [hsum_split]
  have hfin : A₀' * (Real.exp (-c * Real.sqrt (b * D)) * Zeta23.Tail.sideW L b c B D)
        + A₀' * (Real.exp (-c * Real.sqrt (b * D)) * Zeta23.Tail.sideW L b c B D)
      = 2 * A₀ * (Real.exp (-c * Real.sqrt (b * D)) * sideWQ L b c B D q) := by
    unfold sideWQ; rw [hA₀'def]; ring
  calc _ ≤ A₀' * (Real.exp (-c * Real.sqrt (b * D)) * Zeta23.Tail.sideW L b c B D)
        + A₀' * (Real.exp (-c * Real.sqrt (b * D)) * Zeta23.Tail.sideW L b c B D) :=
        add_le_add hlo hhi
    _ = _ := hfin

/-! ## B.2 — the mirrored tail lemma per χ (§7.2's family-indexed QT.b(1)–(5))

> **§7.2** "…Either way `‖Ẽ_χ‖ ≤ θ₀ → 0` faster than any required rate, uniformly over the
> family."

The χ-indexed version of the Phase-1 chain: the same statements with `LocalCountQ` in place
of `LocalCount`, so that θ₀ is a single number valid for EVERY χ in 𝔉_Q. -/

/-- **Standing hypotheses of the q-aspect tail at a free buffer**, per primitive χ of
conductor `q`. `Z` is the zero configuration of `L(s,χ)`.

Paper §7.2. Mirror of `Zeta23.Tail.TailHypG`
(`Zeta23/Tail/GevreyTail.lean:1442`) with H6's q-uniform local count.
Depends on: `LocalCountQ`.
Rule 17: `hD : 1 ≤ D` — buffer FREE (no `D0 T`, no `√T`). No `lam` field is mentioned, so
no λ ≤ 1 can hide; no `X`. `hL : 2 ≤ P.L T` is a growth fact, not a cap. CLEAN. -/
structure TailHypQ (Z : Zeta23.ZeroConfig) (P : Zeta23.Params) (T A₀ A Cenv D q : ℝ)
    : Prop where
  hT : Zeta23.Tail.T₀ ≤ T
  hL : 2 ≤ P.L T
  hA₀ : 1 ≤ A₀
  hq : 1 ≤ q
  /-- H6: the q-uniform two-sided unit-window local count. -/
  hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))
  hA : 0 < A
  hCenv : 0 ≤ Cenv
  hw : 0 < P.w
  hD : 1 ≤ D
  /-- the §7.1 envelope for φ̂ on the strip, in terms of the real distance `|r|`. -/
  hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 →
    ‖P.phiHat T ((r : ℂ) - Complex.I * (y : ℂ))‖
      ≤ (Real.exp (P.L T / 4) * Cenv)
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w / A * |r|))

/-- The zeros NOT in the tail at buffer `D`, as a `Finset` of the carrier subtype (mirror of
`Zeta23.Tail.TailHypG.sAD`, `Zeta23/Tail/GevreyTail.lean:1481`). Owned here so that
`partial_sum_leQ` does not have to forward-reference a field — this matters for
the skeleton author (note after B.2). -/
def TailHypQ.sAQ {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T A₀ A Cenv D q : ℝ}
    (_ : TailHypQ Z P T A₀ A Cenv D q) : Finset Z.carrier :=
  (Zeta23.Tail.finite_notTailD Z T D).toFinset

/-- Membership in `sAQ` is exactly failure of `InTailD` (mirror of
`Zeta23.Tail.TailHypG.not_mem_sAD_iff`, `GevreyTail.lean:1484`). -/
theorem TailHypQ.not_mem_sAQ_iff {Z : Zeta23.ZeroConfig} {P : Zeta23.Params}
    {T A₀ A Cenv D q : ℝ} (H : TailHypQ Z P T A₀ A Cenv D q) (ρ : Z.carrier) :
    ρ ∉ H.sAQ ↔ Zeta23.Tail.InTailD T D (ρ : ℂ).im := by
  rw [TailHypQ.sAQ, Set.Finite.mem_toFinset]; simp

/-- **H6 in `LocalCountQ` shape, from the `ZeroConfig` window count** — the q-uniform mirror
of `Zeta23.Tail.LocalCount.ofWindowCount` (`Zeta23/Tail.lean:119`), whose proof this is
verbatim (the right-hand side is opaque to it).

Rule 17: no buffer, no λ, no X. CLEAN. -/
theorem LocalCountQ.ofWindowCount (Z : Zeta23.ZeroConfig) {A₀ q : ℝ} (hA₀ : 1 ≤ A₀)
    (hq : 1 ≤ q)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    LocalCountQ (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ) A₀ q where
  one_le := hA₀
  one_le_q := hq
  window t s hs := by
    classical
    refine le_trans ?_ (hloc t)
    have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
    unfold Zeta23.ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hs ρ hρ⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h

/-- **The q-aspect collected tail bound** — the paper's θ₀ at the q-uniform window weight
`sideWQ`, whose leading terms carry the window-log base `q(2T+4)`.

⚠ **FOLLOWS THE F16 REPAIR (decision D14).** The frozen body wrote
`sideW … (q*(2*T+4)) D`; that form divides `sideW`'s telescoping remainder by `q` and is
NOT what `tail_rowsum_exp_le_Q` can deliver (see the finding written out there in full).
The body now uses `sideWQ … (2*T+4) D q`, which is the honest output of the row-sum and
still carries `log(q(2T+4))` on the window-count terms — the paper's actual §7.2 claim.
`theta0Q_one`, `theta0Q_eq`, `prefactorQ` and `theta0Q_le_of_closing` are all unchanged in
statement; only this body and `prefactorQ`'s moved, in step, so the factorisation identity
still holds on the nose.

Paper §7.2. Derivation: `LEMMA_QT` §QT.b(4)–(5) (RESOLUTION R-2: the
Lean `sideW` shape is used in place of the note's crude `2(ℒ + log 4T)·S(D₀)²`, both being
explicit and both full-rate `exp(−(4/e)√(wD₀/A))`; §7.2 itself says the crude form
"exceeds it by the factor 0.199ℒ — conservative, never wrong"). Mirror of
`Zeta23.Tail.theta0G` (`Zeta23/Tail/GevreyTail.lean:1460`).
Rule 17: `D` is a bare argument; the body mentions no `D0`, no `Real.sqrt T`, no `lam`,
no `X`. CLEAN. -/
def theta0Q (P : Zeta23.Params) (T A₀ A Cenv D q : ℝ) : ℝ :=
  (Real.exp (P.L T / 4) * Cenv) ^ 2 * (2 * A₀
      * (Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w / A * D))
        * sideWQ (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D q))
    / P.L T

/-- `theta0Q` at conductor 1 is [R]'s `theta0G` — the sanity bridge between the q-aspect
window base `q(2T+4)` and Phase 1's `2T+4`.

Still holds verbatim after the F16 repair, and still with NO hypotheses: `Real.log 1 = 0`
makes `sideWQ`'s factor `1 + 0/log B = 1` even where `log B = 0`. (This is why `sideWQ` is
written `1 + log q / log B` rather than the equal-looking `log (qB) / log B`, which would
need `B ≠ 1` and so would put a hypothesis on this bridge.)

Paper §7.2.
Depends on: `theta0Q`, `sideWQ`, `Zeta23.Tail.theta0G`.
Rule 17: definitional identity; no hypotheses at all. CLEAN. -/
theorem theta0Q_one (P : Zeta23.Params) (T A₀ A Cenv D : ℝ) :
    theta0Q P T A₀ A Cenv D 1 = Zeta23.Tail.theta0G P T A₀ A Cenv D := by
  unfold theta0Q sideWQ Zeta23.Tail.theta0G
  rw [Real.log_one, zero_div, add_zero, one_mul]

/-- **§7.2, QT.b(1)–(4) combined, q-aspect**: finite partial sums over tail-at-`D` zeros
satisfy `∑ m_ρ‖u_ρ‖₂² ≤ L·θ₀Q`, with the local count q-uniform.

Paper §7.2. Mirror of `Zeta23.Tail.TailHypG.partial_sum_leG`
(`Zeta23/Tail/GevreyTail.lean:1494`).
Depends on: B.1, `Zeta23.Tail.norm_sq_uvec_le_gevrey`,
`Zeta23.Tail.grid_sum_exp_le`.
Rule 17: buffer FREE (`H.hD : 1 ≤ D`); no λ, no X. CLEAN. -/
theorem TailHypQ.partial_sum_leQ {Z : Zeta23.ZeroConfig} {P : Zeta23.Params}
    {T A₀ A Cenv D q : ℝ} (H : TailHypQ Z P T A₀ A Cenv D q)
    (u : Finset {ρ : Z.carrier // ρ ∉ H.sAQ}) :
    ∑ x ∈ u, (Z.mult (x : Z.carrier) : ℝ)
        * ∑ k, ‖Zeta23.Tail.uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ P.L T * theta0Q P T A₀ A Cenv D q := by
  classical
  have hLC := LocalCountQ.ofWindowCount Z H.hA₀ H.hq H.hloc
  have hb : 0 < P.w / A := div_pos H.hw H.hA
  have hc : (0 : ℝ) < 2 / Real.exp 1 := by positivity
  have hL0 : 0 < P.L T := by linarith [H.hL]
  have hLne : P.L T ≠ 0 := ne_of_gt hL0
  have hT0 : 0 < T := by have h : (300 : ℝ) ≤ T := H.hT; linarith
  have hK0 : (0 : ℝ) ≤ Real.exp (P.L T / 4) * Cenv := by have := H.hCenv; positivity
  -- push `u` forward to a Finset of the carrier; all its elements are tail zeros
  set s : Finset Z.carrier := u.map (Function.Embedding.subtype _) with hs
  have hs_tail : ∀ ρ ∈ s, Zeta23.Tail.InTailD T D ((fun ρ : Z.carrier => (ρ : ℂ).im) ρ) := by
    intro ρ hρ
    rw [hs, Finset.mem_map] at hρ
    obtain ⟨x, _, rfl⟩ := hρ
    exact (H.not_mem_sAQ_iff _).mp x.2
  have hcount := tail_rowsum_exp_le_Q (L := P.L T) (c := 2 * (2 / Real.exp 1))
    hLC H.hT H.hD (by linarith [H.hL]) hb (by positivity) s hs_tail
  have hterm : ∀ x ∈ u,
      (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖Zeta23.Tail.uvec P T (x : Z.carrier) k‖ ^ 2
        ≤ (Real.exp (P.L T / 4) * Cenv) ^ 2 * ((Z.mult (x : Z.carrier) : ℝ)
            * (Real.exp (-(2 * (2 / Real.exp 1))
                * Real.sqrt (P.w / A * Zeta23.Tail.distI T ((x : Z.carrier) : ℂ).im))
              * Zeta23.Tail.rowS (P.L T) (P.w / A) (2 * (2 / Real.exp 1))
                (Zeta23.Tail.distI T ((x : Z.carrier) : ℂ).im))) := by
    intro x _
    have hx : Zeta23.Tail.InTailD T D ((x : Z.carrier) : ℂ).im := (H.not_mem_sAQ_iff _).mp x.2
    have hdist : 1 ≤ Zeta23.Tail.distI T ((x : Z.carrier) : ℂ).im :=
      H.hD.trans (Zeta23.Tail.le_distI_of_InTailD hT0.le (by linarith [H.hD]) hx)
    have h := Zeta23.Tail.norm_sq_uvec_le_gevrey (Z := Z) H.hT H.hL hK0 hb hc
      H.hdecay (x : Z.carrier).2 hdist
    have hm : (0 : ℝ) ≤ Z.mult (x : Z.carrier) := Nat.cast_nonneg _
    calc _ ≤ (Z.mult (x : Z.carrier) : ℝ)
          * ((Real.exp (P.L T / 4) * Cenv) ^ 2 * Real.exp (-(2 * (2 / Real.exp 1))
              * Real.sqrt (P.w / A * Zeta23.Tail.distI T ((x : Z.carrier) : ℂ).im))
            * Zeta23.Tail.rowS (P.L T) (P.w / A) (2 * (2 / Real.exp 1))
              (Zeta23.Tail.distI T ((x : Z.carrier) : ℂ).im)) :=
          mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring
  calc ∑ x ∈ u, (Z.mult (x : Z.carrier) : ℝ)
          * ∑ k, ‖Zeta23.Tail.uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ ∑ x ∈ u, (Real.exp (P.L T / 4) * Cenv) ^ 2 * ((Z.mult (x : Z.carrier) : ℝ)
          * (Real.exp (-(2 * (2 / Real.exp 1))
              * Real.sqrt (P.w / A * Zeta23.Tail.distI T ((x : Z.carrier) : ℂ).im))
            * Zeta23.Tail.rowS (P.L T) (P.w / A) (2 * (2 / Real.exp 1))
              (Zeta23.Tail.distI T ((x : Z.carrier) : ℂ).im))) := Finset.sum_le_sum hterm
    _ = (Real.exp (P.L T / 4) * Cenv) ^ 2 * ∑ ρ ∈ s, (Z.mult ρ : ℝ)
          * (Real.exp (-(2 * (2 / Real.exp 1))
              * Real.sqrt (P.w / A * Zeta23.Tail.distI T (ρ : ℂ).im))
            * Zeta23.Tail.rowS (P.L T) (P.w / A) (2 * (2 / Real.exp 1))
              (Zeta23.Tail.distI T (ρ : ℂ).im)) := by
        rw [← Finset.mul_sum, hs, Finset.sum_map]; rfl
    _ ≤ (Real.exp (P.L T / 4) * Cenv) ^ 2 * (2 * A₀
          * (Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w / A * D))
            * sideWQ (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D q)) := by
        apply mul_le_mul_of_nonneg_left hcount
        positivity
    _ = P.L T * theta0Q P T A₀ A Cenv D q := by
        unfold theta0Q
        field_simp

/-- **§7.2, QT.b(5), q-aspect**: the free-buffer tail package feeds the θ₀-generic assembly
interface with the buffer FREE and the count q-uniform.

Paper §7.2. Derivation: `LEMMA_QT` §QT.b(5) with its R8 CORRECTION
(RESOLUTION R-4). Mirror of `Zeta23.Tail.TailHypG.tailInputsD`
(`Zeta23/Tail/GevreyTail.lean:1777`).
Depends on: `TailHypQ.partial_sum_leQ`, `Zeta23.Assembly.TailInputsD`.

**Proof route** (avoids re-deriving ~200 lines of the [R] matrix chain). Everything in
`GevreyTail.lean:1588–1740` that produces the *structural* facts about `E(D)` —
`hasSum_EzD`, `EzD_isHermitian`, `tilde_/hat_EzD_isHermitian` — has a conclusion that does
not mention `θ₀` at all; only the SIZE step `traceNorm_smul_EzD_le` does. So those are taken
from a `TailHypG` built out of `H` at the crude inflated constant
`A₀·(1 + log q/log 3)` (legitimate since `log(q(|t|+3)) ≤ (1+log q/log 3)·log(|t|+3)` for
every real `t`, as `|t|+3 ≥ 3`), and the size step is then redone against
`partial_sum_leQ`'s own `θ₀Q`. The crude constant is used ONLY where it cannot be read off
the conclusion; the θ₀ delivered is the sharp `theta0Q`, never the inflated one.

Rule 17: target is `TailInputsD` (D-generic), never `Assembly.TailInputs` (whose `D` is
`√T`, `Assembly/Inputs.lean:57`) — the DO-NOT-CITE rule of RESOLUTION R-4. The auxiliary
`TailHypG` is instantiated at the FREE buffer `D` too. CLEAN. -/
theorem TailHypQ.tailInputsQ {Z : Zeta23.ZeroConfig} {P : Zeta23.Params}
    {T A₀ A Cenv D q : ℝ} (H : TailHypQ Z P T A₀ A Cenv D q) (ha : 0 < P.a T)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    Zeta23.Assembly.TailInputsD Z P T D (theta0Q P T A₀ A Cenv D q) := by
  classical
  have hL0 : 0 < P.L T := by linarith [H.hL]
  have hb : 0 < P.w / A := div_pos H.hw H.hA
  have hT300 : (300 : ℝ) ≤ T := H.hT
  have hT0 : 0 < T := by linarith
  have hA₀0 : (0 : ℝ) ≤ A₀ := by linarith [H.hA₀]
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg H.hq
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hratio : (0 : ℝ) ≤ Real.log q / Real.log 3 := div_nonneg hlogq hlog3.le
  have hB1 : (1 : ℝ) ≤ 2 * T + 4 := by linarith
  -- (0) `θ₀Q ≥ 0`
  have hθ0 : 0 ≤ theta0Q P T A₀ A Cenv D q := by
    have hside : 0 ≤ Zeta23.Tail.sideW (P.L T) (P.w / A) (2 * (2 / Real.exp 1))
        (2 * T + 4) D :=
      Zeta23.Tail.sideW_nonneg hL0.le hb (by positivity) hB1 (by linarith [H.hD])
    have hK : (0 : ℝ) ≤ Real.exp (P.L T / 4) * Cenv := by have := H.hCenv; positivity
    have hfac : (0 : ℝ) ≤ 1 + Real.log q / Real.log (2 * T + 4) := by
      have h : (0 : ℝ) ≤ Real.log q / Real.log (2 * T + 4) :=
        div_nonneg hlogq (Real.log_nonneg hB1)
      linarith
    unfold theta0Q sideWQ
    positivity
  -- (1) the auxiliary [R] hypothesis bundle, at the crude constant, for the STRUCTURE only
  have hA₀' : 1 ≤ A₀ * (1 + Real.log q / Real.log 3) := by nlinarith [H.hA₀]
  have hloc' : ∀ t : ℝ, (Z.N t (t + 1) : ℝ)
      ≤ A₀ * (1 + Real.log q / Real.log 3) * Real.log (|t| + 3) := by
    intro t
    have ht3 : (3 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
    have ht0 : (0 : ℝ) < |t| + 3 := by linarith
    have hlt : Real.log 3 ≤ Real.log (|t| + 3) := Real.log_le_log (by norm_num) ht3
    have hq0 : (0 : ℝ) < q := by linarith [H.hq]
    have hmul : Real.log (q * (|t| + 3)) = Real.log q + Real.log (|t| + 3) :=
      Real.log_mul (ne_of_gt hq0) (ne_of_gt ht0)
    have hinv : Real.log q / Real.log 3 * Real.log 3 = Real.log q := by field_simp
    have hstep : Real.log q ≤ Real.log q / Real.log 3 * Real.log (|t| + 3) := by
      linarith [mul_le_mul_of_nonneg_left hlt hratio]
    have hall : Real.log (q * (|t| + 3))
        ≤ (1 + Real.log q / Real.log 3) * Real.log (|t| + 3) := by
      rw [hmul]; nlinarith
    refine (H.hloc t).trans ?_
    calc A₀ * Real.log (q * (|t| + 3))
        ≤ A₀ * ((1 + Real.log q / Real.log 3) * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hall hA₀0
      _ = A₀ * (1 + Real.log q / Real.log 3) * Real.log (|t| + 3) := by ring
  have H' : Zeta23.Tail.TailHypG Z P T (A₀ * (1 + Real.log q / Real.log 3)) A Cenv D :=
    { hT := H.hT
      hL := H.hL
      hA₀ := hA₀'
      hloc := hloc'
      hA := H.hA
      hCenv := H.hCenv
      hw := H.hw
      hD := H.hD
      hdecay := H.hdecay }
  -- (2) the structural facts (θ₀-free conclusions), taken from `H'`
  have hEt := H'.tilde_EzD_isHermitian hconj
  have hEh := H'.hat_EzD_isHermitian hconj
  have hSum : HasSum (fun x : {ρ : Z.carrier // ρ ∉ H.sAQ} =>
      ((Z.mult (x : Z.carrier) : ℝ) : ℂ)
        • Matrix.vecMulVec (Zeta23.Tail.uvec P T (x : Z.carrier))
            (Zeta23.Tail.uvec P T (x : Z.carrier))) (Z.EzD P T D) := H'.hasSum_EzD
  -- (3) the SIZE step, redone against `partial_sum_leQ`'s own sharp `θ₀Q`
  have hsummable : Summable (fun x : {ρ : Z.carrier // ρ ∉ H.sAQ} =>
      (Z.mult (x : Z.carrier) : ℝ)
        * ∑ k, ‖Zeta23.Tail.uvec P T (x : Z.carrier) k‖ ^ 2) :=
    summable_of_sum_le (fun x => by positivity) H.partial_sum_leQ
  have htsum : ∑' x : {ρ : Z.carrier // ρ ∉ H.sAQ},
      (Z.mult (x : Z.carrier) : ℝ)
        * ∑ k, ‖Zeta23.Tail.uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ P.L T * theta0Q P T A₀ A Cenv D q :=
    Real.tsum_le_of_sum_le (fun x => by positivity) H.partial_sum_leQ
  have htrace : ∀ {κ : ℝ}, 0 ≤ κ → ∀ (hM : (((κ : ℝ) : ℂ) • Z.EzD P T D).IsHermitian),
      Zeta23.Tail.traceNorm hM ≤ κ * (P.L T * theta0Q P T A₀ A Cenv D q) := by
    intro κ hκ hM
    refine le_trans ?_ (mul_le_mul_of_nonneg_left htsum hκ)
    apply Zeta23.Tail.traceNorm_le_of_hasSum_vecMulVec hM
      (fun x : {ρ : Z.carrier // ρ ∉ H.sAQ} => κ * (Z.mult (x : Z.carrier) : ℝ))
      (fun x => by positivity)
      (fun x : {ρ : Z.carrier // ρ ∉ H.sAQ} => Zeta23.Tail.uvec P T (x : Z.carrier))
    · have h := hsummable.hasSum.mul_left κ
      simpa only [mul_assoc] using h
    · have h := hSum.const_smul ((κ : ℝ) : ℂ)
      simpa only [smul_smul, Complex.ofReal_mul] using h
  -- (4) [prop:tail], q-aspect
  have htilde : P.tilde T (Z.EzD P T D) = (((P.L T)⁻¹ : ℝ) : ℂ) • Z.EzD P T D := by
    unfold Zeta23.Params.tilde; rw [Complex.ofReal_inv]
  have hEt' : ((((P.L T)⁻¹ : ℝ) : ℂ) • Z.EzD P T D).IsHermitian := htilde ▸ hEt
  have h1 : Zeta23.Tail.traceNorm hEt ≤ theta0Q P T A₀ A Cenv D q := by
    have h := htrace (κ := (P.L T)⁻¹) (by positivity) hEt'
    have e : (P.L T)⁻¹ * (P.L T * theta0Q P T A₀ A Cenv D q)
        = theta0Q P T A₀ A Cenv D q := by field_simp
    rw [e] at h
    convert h using 2
  have hhat : P.hat T (Z.EzD P T D) = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • Z.EzD P T D := by
    unfold Zeta23.Params.hat; push_cast; rfl
  have hEh' : ((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • Z.EzD P T D).IsHermitian := hhat ▸ hEh
  have h2 : Zeta23.Tail.traceNorm hEh
      ≤ theta0Q P T A₀ A Cenv D q / (P.a T * P.L T) := by
    have h := htrace (κ := (P.a T * P.L T ^ 2)⁻¹) (by positivity) hEh'
    have e : (P.a T * P.L T ^ 2)⁻¹ * (P.L T * theta0Q P T A₀ A Cenv D q)
        = theta0Q P T A₀ A Cenv D q / (P.a T * P.L T) := by field_simp
    rw [e] at h
    convert h using 2
  exact
    { theta_nonneg := hθ0
      tilde := ⟨hEt, fun i => (Zeta23.Tail.abs_eigenvalues_le_traceNorm hEt i).trans h1⟩
      hat := ⟨Zeta23.Tail.traceNorm hEh, Zeta23.Tail.traceNorm_nonneg _,
        Zeta23.Tail.abs_rtrace_le_traceNorm _, Zeta23.Tail.frobSq_le_traceNorm_sq _, h2⟩ }

/-- **`TailHypQ.of_profile` with the §7.1 envelope taken as a HYPOTHESIS** —
the q-uniform twin of `Zeta23.Tail.TailHypG.of_envelope` above; `of_profile` is the flat-taper
special case and the design window is `B := gevreyBprod A B`. Rule 17: no validity class;
buffer FREE. CLEAN. -/
theorem TailHypQ.of_envelope {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T A₀ A B D q : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hw : 0 < P.w)
    (hT : Zeta23.Tail.T₀ ≤ T) (hL : 2 ≤ P.L T)
    (hA₀ : 1 ≤ A₀) (hq : 1 ≤ q)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hD : 1 ≤ D)
    (henv : ∀ z : ℂ, ‖P.phiHat T z‖
      ≤ Real.exp 2 * max (2 * B * P.w) (P.L T) * Real.exp (|z.im| * (P.L T / 2))
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A))) :
    TailHypQ Z P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) D q where
  hT := hT
  hL := hL
  hA₀ := hA₀
  hq := hq
  hloc := hloc
  hA := hA
  hCenv := by
    have hL0 : 0 < P.L T := by linarith
    positivity
  hw := hw
  hD := hD
  hdecay := hdecay_of_envelope hA hB hw (by linarith) henv

/-- **§7.1 ⟹ §7.2 bridge, q-aspect**: the Gevrey-2 profile supplies `hdecay` at
`C_env = e²·max(2Bw, L)`, and H6's q-uniform count supplies `hloc`.

Paper §7.1 → §7.2 seam (526). Mirror of `Zeta23.Tail.TailHypG.of_profile`
(`Zeta23/Tail/GevreyTail.lean:1930`).
Depends on:
`Zeta23.Params.norm_phiHat_le_gevrey`.
Rule 17: `hP : P.ValidQ` is the WEAKENED class, no `lam_le_one`; but see FINDING F-0 —
`ValidQ` at `toParams` is unsatisfiable at the design of record, so this hypothesis must be
weakened in Phase 3. `hwL : 8w ≤ L` is RESOLUTION R-1's [eq:wrange] plumbing. `hD : 1 ≤ D`
— buffer FREE. No X. CLEAN. -/
theorem TailHypQ.of_profile {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T A₀ A B D q : ℝ}
    (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) (hP : P.ValidQ)
    (hwL : 8 * P.w ≤ P.L T) (hT : Zeta23.Tail.T₀ ≤ T) (hL : 2 ≤ P.L T)
    (hA₀ : 1 ≤ A₀) (hq : 1 ≤ q)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hD : 1 ≤ D) :
    TailHypQ Z P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) D q where
  hT := hT
  hL := hL
  hA₀ := hA₀
  hq := hq
  hloc := hloc
  hA := hϱ.A_pos
  hCenv := by
    have hL0 : 0 < P.L T := by linarith
    have hB := hϱ.B_pos
    have hw := Zeta23.Params.w_pos hP
    positivity
  hw := Zeta23.Params.w_pos hP
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
    have hw0 : 0 < P.w := Zeta23.Params.w_pos hP
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

/-! ## B.3 — the closing condition (§7.2's inequality) and the missing θ₀ size estimates

> **§7.2** "…the closing condition `(4/e)√(wD₀/A) ≥ L/2 + log(prefactor) + log(L/η)` holds
> with Θ(ℒ log ℒ) to spare at the reference design; **the design of record sits ON the
> constraint by construction — the optimiser drives D₀ to the boundary, so the margin is
> 0 nats at every Q** (table2_check.py), which is admissible: … equality delivers exactly
> the target θ₀"

**⚠ The closing condition MUST be transcribed NON-STRICT.**
The paper is explicit that at the design of record the margin is exactly 0 nats at every Q.
A Phase-2 statement written with `<`, or with any added positive slack, is a statement the
paper's own design does not satisfy. Both statements below put `≤` with the *needed*
quantity `L/2 + log(prefactor) + log(L/η)` on the LEFT, i.e. `needed ≤ supplied`, which
admits equality.

**RESOLUTION R-3.** LEMMA_QT §QT.b(6) offers two targets (`θ₀ ≤ η/L` or `θ₀ ≤ Q^{−2}`).
Paper §7.2 and §10.3 quote only the `η/L` branch and §7.3 says the pair repair "removes it
entirely", so ONLY the `η/L` branch is transcribed. The `Q^{−2}` branch and the whole `c₂`
ladder table get no Lean statement.

**PHASE1_INTERFACES §7.4 / "Not found" item 4** records that there is NO size estimate for
`Zeta23.Tail.theta0G` anywhere in the tree (only `theta0G_nonneg`), while §7.2's closing
condition IS exactly a size estimate for θ₀. `theta0G_le` below discharges that obligation
for the [R]-tree object; `theta0Q_le_of_closing` does it for the q-aspect object. -/

/-- The `θ₀G` prefactor with the off-line amplification `e^{L/2}` and the Gevrey
exponential `exp(−(4/e)√(wD/A))` stripped out, so that
`θ₀G = e^{L/2}·prefactorG·exp(−(4/e)√(wD/A))` by construction.

Paper §7.2 ("log(prefactor)"). Derivation: `LEMMA_QT` §QT.b(5).
Rule 17: `D` a bare argument; no `D0`, no `√T`, no `lam`, no `X`. CLEAN. -/
def prefactorG (P : Zeta23.Params) (T A₀ A Cenv D : ℝ) : ℝ :=
  Cenv ^ 2 * (2 * A₀
      * Zeta23.Tail.sideW (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D)
    / P.L T

/-- The same for the q-aspect `theta0Q`, at the q-uniform window weight `sideWQ`
(window-log base `q(2T+4)` on the count terms).

⚠ Body moved in step with `theta0Q` under the F16 repair (decision D14), so that
`theta0Q_eq` and hence `theta0Q_le_of_closing` remain true verbatim.

Paper §7.2.
Rule 17: as `prefactorG`. CLEAN. -/
def prefactorQ (P : Zeta23.Params) (T A₀ A Cenv D q : ℝ) : ℝ :=
  Cenv ^ 2 * (2 * A₀
      * sideWQ (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D q)
    / P.L T

/-- **The factorisation of `θ₀G`**: `θ₀G = e^{L/2}·prefactorG·exp(−(4/e)√(wD/A))`.
Reads off `(e^{L/4}C)² = e^{L/2}C²`, `2·(2/e) = 4/e` and `√((w/A)·D) = √(wD/A)`.

Paper §7.2.
Depends on: `Zeta23.Tail.theta0G`, `prefactorG`.
Rule 17: an identity between two definitions; no hypotheses. CLEAN. -/
theorem theta0G_eq (P : Zeta23.Params) (T A₀ A Cenv D : ℝ) :
    Zeta23.Tail.theta0G P T A₀ A Cenv D
      = Real.exp (P.L T / 2) * prefactorG P T A₀ A Cenv D
        * Real.exp (-(4 / Real.exp 1) * Real.sqrt (P.w * D / A)) := by
  have hs : Real.sqrt (P.w / A * D) = Real.sqrt (P.w * D / A) := by
    rw [show P.w / A * D = P.w * D / A by ring]
  have he : Real.exp (P.L T / 4) ^ 2 = Real.exp (P.L T / 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hE : Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w * D / A))
      = Real.exp (-(4 / Real.exp 1) * Real.sqrt (P.w * D / A)) := by
    congr 1; ring
  unfold Zeta23.Tail.theta0G prefactorG
  rw [hs, hE, mul_pow, he]
  ring

/-- The same factorisation for `theta0Q`.

Paper §7.2.
Depends on: `theta0Q`, `prefactorQ`.
Rule 17: an identity between two definitions; no hypotheses. CLEAN. -/
theorem theta0Q_eq (P : Zeta23.Params) (T A₀ A Cenv D q : ℝ) :
    theta0Q P T A₀ A Cenv D q
      = Real.exp (P.L T / 2) * prefactorQ P T A₀ A Cenv D q
        * Real.exp (-(4 / Real.exp 1) * Real.sqrt (P.w * D / A)) := by
  have hs : Real.sqrt (P.w / A * D) = Real.sqrt (P.w * D / A) := by
    rw [show P.w / A * D = P.w * D / A by ring]
  have he : Real.exp (P.L T / 4) ^ 2 = Real.exp (P.L T / 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hE : Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w * D / A))
      = Real.exp (-(4 / Real.exp 1) * Real.sqrt (P.w * D / A)) := by
    congr 1; ring
  unfold theta0Q prefactorQ
  rw [hs, hE, mul_pow, he]
  ring

/-- **THE MISSING SIZE ESTIMATE FOR `theta0G`** (PHASE1_INTERFACES §7.4 and "Not found"
item 4: "No `theta0G_le`. There is no size estimate for `theta0G` analogous to
`Tail.theta0_le`; only `theta0G_nonneg`"). §7.2's closing condition IS that estimate:
`(4/e)√(wD/A) ≥ L/2 + log(prefactor) + log(L/η)` implies `θ₀G ≤ η/L`.

⚠ **NON-STRICT** (FLAG F-1): the design of record meets the constraint with EQUALITY —
margin 0 nats at every Q (`table2_check.py`) — so a strict `<`, or any added slack, would be
a statement the paper's own design FAILS.

Paper §7.2. Derivation: `LEMMA_QT` §QT.b(6), `η/L` branch only
(RESOLUTION R-3).
Depends on: `theta0G_eq`, `Zeta23.Tail.sideW_nonneg`.
Rule 17: `D` is a bare variable — **no** `D = Real.sqrt T`, **no** `Zeta23.D0 T`, and this
is precisely the estimate whose absence forced [R]'s `theta0_le` to hard-code `D₀² = T`.
No `P.lam` appears at all; no `X`. `hpre : 0 < prefactorG …` is a positivity side condition
(it follows from `sideW_nonneg` + `0 < Cenv`, `1 ≤ A₀`, `0 < L`), kept explicit so the
statement is self-contained. CLEAN. -/
theorem theta0G_le {P : Zeta23.Params} {T A₀ A Cenv D η : ℝ}
    (hL : 0 < P.L T) (hη : 0 < η) (hw : 0 < P.w) (hA : 0 < A) (hD : 0 ≤ D)
    (hpre : 0 < prefactorG P T A₀ A Cenv D)
    (hclose : P.L T / 2 + Real.log (prefactorG P T A₀ A Cenv D)
        + Real.log (P.L T / η)
      ≤ (4 / Real.exp 1) * Real.sqrt (P.w * D / A)) :
    Zeta23.Tail.theta0G P T A₀ A Cenv D ≤ η / P.L T := by
  have hηL : 0 < η / P.L T := div_pos hη hL
  have hinv : Real.log (P.L T / η) = -Real.log (η / P.L T) := by
    rw [← Real.log_inv, inv_div]
  rw [theta0G_eq]
  calc Real.exp (P.L T / 2) * prefactorG P T A₀ A Cenv D
        * Real.exp (-(4 / Real.exp 1) * Real.sqrt (P.w * D / A))
      = Real.exp (P.L T / 2 + Real.log (prefactorG P T A₀ A Cenv D)
          + -(4 / Real.exp 1) * Real.sqrt (P.w * D / A)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hpre]
    _ ≤ Real.exp (Real.log (η / P.L T)) := by
        apply Real.exp_le_exp.mpr
        rw [hinv] at hclose
        linarith
    _ = η / P.L T := Real.exp_log hηL

/-- **THE CLOSING CONDITION OF §7.2**, q-aspect: the same, for `theta0Q`.

⚠ **NON-STRICT** (FLAG F-1) — see `theta0G_le`.

Paper §7.2. Derivation: `LEMMA_QT` §QT.b(6), `η/L` branch only
(RESOLUTION R-3).
Depends on: `theta0Q_eq`, `Zeta23.Tail.sideW_nonneg`.
Rule 17: as `theta0G_le`. CLEAN.
(Recorded, not acted on:
the paper's own design script omits `log A₀` from its `logpre`,
while both `theta0G` and `theta0Q` carry `2·A₀`. Since the design is driven to
`margin = 0` exactly, that is not absorbed by slack. The Lean statement here is written
against `prefactorQ`, which DOES carry `A₀`, so the statement is correct as it stands and
the discrepancy is confined to the script.) -/
theorem theta0Q_le_of_closing {P : Zeta23.Params} {T A₀ A Cenv D q η : ℝ}
    (hL : 0 < P.L T) (hη : 0 < η) (hw : 0 < P.w) (hA : 0 < A) (hD : 0 ≤ D)
    (hpre : 0 < prefactorQ P T A₀ A Cenv D q)
    (hclose : P.L T / 2 + Real.log (prefactorQ P T A₀ A Cenv D q)
        + Real.log (P.L T / η)
      ≤ (4 / Real.exp 1) * Real.sqrt (P.w * D / A)) :
    theta0Q P T A₀ A Cenv D q ≤ η / P.L T := by
  have hηL : 0 < η / P.L T := div_pos hη hL
  have hinv : Real.log (P.L T / η) = -Real.log (η / P.L T) := by
    rw [← Real.log_inv, inv_div]
  rw [theta0Q_eq]
  calc Real.exp (P.L T / 2) * prefactorQ P T A₀ A Cenv D q
        * Real.exp (-(4 / Real.exp 1) * Real.sqrt (P.w * D / A))
      = Real.exp (P.L T / 2 + Real.log (prefactorQ P T A₀ A Cenv D q)
          + -(4 / Real.exp 1) * Real.sqrt (P.w * D / A)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hpre]
    _ ≤ Real.exp (Real.log (η / P.L T)) := by
        apply Real.exp_le_exp.mpr
        rw [hinv] at hclose
        linarith
    _ = η / P.L T := Real.exp_log hηL

/-! ## B.4 — uniformity over the family (§7.2's "uniformly over the family")

> **§7.2** "‖Ẽ_χ‖ ≤ θ₀ → 0 faster than any required rate, **uniformly over the family**."
> **§7.3** "Over the direct sum: the operator norm is a MAX (the Weyl consumer pays nothing)"

`theta0Q` depends on `q`; the family statement needs ONE θ₀ good for every `q ≤ Q`.
The family θ₀ is `theta0Fam := theta0Q … Q`, a closed
form the budget can differentiate, rather than an `sSup`.
OPEN QUESTION Q-2 is live: `sideW L b c B D` is
`α·log B·monoW₀ + β·log B·monoW₁ + α/(bB)·monoW₂ + β/(bB)·monoW₃`; the first two terms
INCREASE in `B` and the last two DECREASE. Monotonicity is therefore stated as its own
obligation with an explicit fallback recorded in its docstring. -/

/-- **`sideW` is monotone in the window-log base `B` ABOVE ITS CROSSOVER — and only there.**

⚠ **REPAIR OF A FALSE STATEMENT (decision D14).** The frozen skeleton stated
this as unconditional monotonicity on `1 ≤ B ≤ B'`. **That is false.** Unfolding
`Zeta23.Tail.sideW` (`GevreyTail.lean:1054`),

  `sideW L b c B D = (α·monoW₀ + β·monoW₁)·log B + (α·monoW₂ + β·monoW₃)/(bB)`,
  `α = 1 + (L/2π)(2/b)(√b/c + 1/c²) ≥ 1`,  `β = (L/2π)(2/b)/c ≥ 0`,

so the first bracket INCREASES in `B` and the second DECREASES, and for small `B` the second
wins. **Counterexample** (machine-checked against the definition, and the record of
and it settles NEGATIVELY the question of whether the pair term can be dropped):

  `L = 0, b = 1, c = 1, D = 1` — all hypotheses of the frozen statement hold. Then
  `α = 1, β = 0`, `monoW 1 1 1 0 = 9` and `monoW 1 1 1 2 = 396`, so
  `sideW 0 1 1 B 1 = 9·log B + 396/B`, giving
  **`sideW(B = 1) = 396` but `sideW(B = e) = 9 + 396/e ≈ 154.7`** — strictly DECREASING
  across `1 ≤ 1 ≤ e`. The frozen statement is refuted.

**What IS true**, and is what this lemma now says: `sideW` is increasing in `B` from the
crossover point onwards, and the crossover is exactly `b·B ≥ (α·monoW₂+β·monoW₃)/(α·monoW₀+β·monoW₁)`.
The two hypotheses below are the natural termwise sufficient form of that condition
(`α, β ≥ 0`, so they imply the collected one). The proof is the elementary two-line
estimate `log(B'/B) ≥ 1 − B/B'` (`Real.log_le_sub_one_of_pos`) against
`1/(bB) − 1/(bB') = (B'−B)/(bBB')`; no analysis beyond that is involved. This is NOT a
weakening of a true claim — it is the true claim, the frozen one having been false.

**The crossover is real and is where F15 bites.** At `b = 1, c = 4/e` the ratio
`monoW₂/(b·monoW₀)` is `23.0` at `D = 1`, `464` at `D = 300`, and `1.0·10¹²` at `D = 10¹²`:
it scales like `b·D`. So a window base `B = 2T+4 = 604` (T = 300) clears the crossover for
every `D ≲ T` and fails catastrophically for `D ≫ T²`. That is precisely the mechanism
behind finding F15 (see `theta0Q_le_theta0Fam`).

**This lemma is no longer a dependency of anything.** `theta0Q_le_theta0Fam` is now routed
through `sideWQ`'s explicit `log q` factor and needs no `sideW` monotonicity at all. It is
kept as the machine-checked record of Q-2's negative resolution.

Paper §7.2 ("uniformly over the family").
Depends on: `Zeta23.Tail.sideW`, `Zeta23.Tail.monoW_nonneg`, `Real.log_le_sub_one_of_pos`.
Rule 17: no `Params`, no buffer semantics (`D` is a bare nonneg real), no λ, no X. CLEAN. -/
theorem sideW_mono_base {L b c D : ℝ} (hL : 0 ≤ L) (hb : 0 < b) (hc : 0 < c)
    (hD : 0 ≤ D) {B B' : ℝ} (hB : 1 ≤ B) (hBB : B ≤ B')
    (hcross0 : Zeta23.Tail.monoW b c D 2 ≤ b * B * Zeta23.Tail.monoW b c D 0)
    (hcross1 : Zeta23.Tail.monoW b c D 3 ≤ b * B * Zeta23.Tail.monoW b c D 1) :
    Zeta23.Tail.sideW L b c B D ≤ Zeta23.Tail.sideW L b c B' D := by
  have hπ := Real.pi_pos
  have hB0 : (0:ℝ) < B := by linarith
  have hB'0 : (0:ℝ) < B' := by linarith
  have hm0 := Zeta23.Tail.monoW_nonneg hb hc hD 0
  have hm1 := Zeta23.Tail.monoW_nonneg hb hc hD 1
  have hm2 := Zeta23.Tail.monoW_nonneg hb hc hD 2
  have hm3 := Zeta23.Tail.monoW_nonneg hb hc hD 3
  have hα0 : (0:ℝ) ≤ 1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2) := by
    positivity
  have hβ0 : (0:ℝ) ≤ L / (2 * Real.pi) * (2 / b) / c := by positivity
  -- `sideW` in collected form: `S·log X + W/(bX)`.
  have hcol : ∀ X : ℝ, 0 < X →
      Zeta23.Tail.sideW L b c X D
        = ((1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2))
              * Zeta23.Tail.monoW b c D 0
            + (L / (2 * Real.pi) * (2 / b) / c) * Zeta23.Tail.monoW b c D 1) * Real.log X
          + ((1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2))
              * Zeta23.Tail.monoW b c D 2
            + (L / (2 * Real.pi) * (2 / b) / c) * Zeta23.Tail.monoW b c D 3) / (b * X) := by
    intro X hX
    unfold Zeta23.Tail.sideW
    field_simp
    ring
  rw [hcol B hB0, hcol B' hB'0]
  set S : ℝ := (1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2))
      * Zeta23.Tail.monoW b c D 0
    + (L / (2 * Real.pi) * (2 / b) / c) * Zeta23.Tail.monoW b c D 1 with hSdef
  set W : ℝ := (1 + L / (2 * Real.pi) * (2 / b) * (Real.sqrt b / c + 1 / c ^ 2))
      * Zeta23.Tail.monoW b c D 2
    + (L / (2 * Real.pi) * (2 / b) / c) * Zeta23.Tail.monoW b c D 3 with hWdef
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  -- the collected crossover `W ≤ bB·S`
  have hcross : W ≤ b * B * S := by
    rw [hWdef, hSdef]
    nlinarith [mul_le_mul_of_nonneg_left hcross0 hα0,
      mul_le_mul_of_nonneg_left hcross1 hβ0]
  -- `log(B'/B) ≥ 1 − B/B'`
  have hlog : 1 - B / B' ≤ Real.log B' - Real.log B := by
    have h := Real.log_le_sub_one_of_pos (div_pos hB0 hB'0)
    rw [Real.log_div (ne_of_gt hB0) (ne_of_gt hB'0)] at h
    linarith
  have hgap : W / (b * B) - W / (b * B') ≤ S * (Real.log B' - Real.log B) := by
    have step1 : W / (b * B) - W / (b * B') = W * (B' - B) / (b * B * B') := by
      field_simp
    have step2 : W * (B' - B) / (b * B * B') ≤ S * (1 - B / B') := by
      rw [div_le_iff₀ (by positivity)]
      have hBB0 : (0:ℝ) ≤ B' - B := by linarith
      have hnum : W * (B' - B) ≤ (b * B * S) * (B' - B) := by nlinarith
      have e : S * (1 - B / B') * (b * B * B') = (b * B * S) * (B' - B) := by
        field_simp
      rw [e]; exact hnum
    have step3 : S * (1 - B / B') ≤ S * (Real.log B' - Real.log B) :=
      mul_le_mul_of_nonneg_left hlog hS0
    rw [step1]; linarith
  linarith

/-- **The family-uniform tail threshold**: one `θ₀` for every conductor `q ≤ Q`, obtained by
evaluating `theta0Q` at the largest conductor.

Paper §7.2.
Rule 17: `D` a bare argument; no `D0`, no `√T`, no λ, no X. CLEAN. -/
def theta0Fam (P : Zeta23.Params) (T A₀ A Cenv D Q : ℝ) : ℝ :=
  theta0Q P T A₀ A Cenv D Q

/-- **"uniformly over the family"**: every conductor `q ≤ Q` in 𝔉_Q has
`θ₀(q) ≤ θ₀_fam`.

⚠ **A FINDING, AND ITS RESOLUTION — NOT THE ONE THAT WAS EXPECTED.**
Against the FROZEN `theta0Q` (window base `q(2T+4)` throughout, including the telescoping
remainder) this statement was FALSE, exactly as F15 records. Reconfirmed here against the
old body: `T = 300, b = P.w/A = 1, c = 2(2/e), L = 10⁻³, D = 10¹², q = 1, Q = 10⁶` satisfies
every hypothesis below, yet
`sideW(base 604) = 4.890·10¹⁷` while `sideW(base 6.04·10⁸) = 4.950·10¹¹` —
`θ₀(q=1)` exceeds `θ₀_fam` by six orders of magnitude. The mechanism is the `sideW`
crossover of `sideW_mono_base`: the `1/(bB)` remainder scales like `D/B`, so for `D ≫ T²`
raising the base *lowers* `sideW`, and F15's proposed fix — add `D ≤ T` from
`ZetaQ.ParamsQ.Valid.D0_le` — is exactly the hypothesis that keeps `D` below the crossover.

**That fix is no longer needed, and adding it would now be an unnecessary hypothesis.**
Repairing F16 removed the crossover from this statement altogether: the repaired `theta0Q`
carries `sideWQ … (2*T+4) D q = (1 + log q/log(2T+4))·sideW … (2*T+4) D`, in which `q`
enters through a single MANIFESTLY INCREASING factor and the base `2T+4` never moves. The
comparison is then just `log q ≤ log Q` against a nonnegative `sideW`. So the statement
below is proved **with its frozen hypotheses exactly as given** — no `P.Valid`, no `D ≤ T`,
no `hDT`. Recorded because it contradicts the prescribed repair: F15's *diagnosis* was
correct, but its *remedy* was contingent on the F16 defect and is dead with it.

`hL`, `hq`, `hqQ`, `hA₀`, `hw`, `hA`, `hD`, `hT` are all consumed: they are what make
`sideW ≥ 0` and the prefactors nonnegative, without which monotonicity in `q` does not
survive multiplication. `hCenv` alone turns out to be redundant (`C_env` enters only as
`(e^{L/4}C_env)²`) — it is kept because the statement is frozen and dropping a hypothesis is
as much an edit as adding one.

Paper §7.2.
Depends on: `theta0Q`, `sideWQ`, `theta0Fam`, `Zeta23.Tail.sideW_nonneg`.
**No longer depends on `sideW_mono_base`** (which is false unconditionally; see there).
Rule 17: `D` free; no λ; no X. CLEAN. -/
theorem theta0Q_le_theta0Fam {P : Zeta23.Params} {T A₀ A Cenv D q Q : ℝ}
    (hL : 0 < P.L T) (hq : 1 ≤ q) (hqQ : q ≤ Q) (hCenv : 0 ≤ Cenv) (hA₀ : 1 ≤ A₀)
    (hw : 0 < P.w) (hA : 0 < A) (hD : 0 ≤ D) (hT : Zeta23.Tail.T₀ ≤ T) :
    theta0Q P T A₀ A Cenv D q ≤ theta0Fam P T A₀ A Cenv D Q := by
  have hT' : (300 : ℝ) ≤ T := hT
  have hb : 0 < P.w / A := div_pos hw hA
  have hc : (0 : ℝ) < 2 * (2 / Real.exp 1) := by positivity
  have hB1 : (1 : ℝ) ≤ 2 * T + 4 := by linarith
  have hlogB : 0 < Real.log (2 * T + 4) := Real.log_pos (by linarith)
  have hside : 0 ≤ Zeta23.Tail.sideW (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D :=
    Zeta23.Tail.sideW_nonneg hL.le hb hc hB1 hD
  -- the only place `q` enters: an increasing scalar factor
  have hlq : Real.log q ≤ Real.log Q := Real.log_le_log (by linarith) hqQ
  have hcoef : Real.log q / Real.log (2 * T + 4) ≤ Real.log Q / Real.log (2 * T + 4) := by
    have h : 0 ≤ (Real.log Q - Real.log q) / Real.log (2 * T + 4) :=
      div_nonneg (by linarith) hlogB.le
    have e : (Real.log Q - Real.log q) / Real.log (2 * T + 4)
        = Real.log Q / Real.log (2 * T + 4) - Real.log q / Real.log (2 * T + 4) := by ring
    rw [e] at h; linarith
  have hstep : (1 + Real.log q / Real.log (2 * T + 4))
        * Zeta23.Tail.sideW (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D
      ≤ (1 + Real.log Q / Real.log (2 * T + 4))
        * Zeta23.Tail.sideW (P.L T) (P.w / A) (2 * (2 / Real.exp 1)) (2 * T + 4) D :=
    mul_le_mul_of_nonneg_right (by linarith) hside
  have hE : (0 : ℝ) ≤ Real.exp (-(2 * (2 / Real.exp 1)) * Real.sqrt (P.w / A * D)) :=
    (Real.exp_pos _).le
  have h2 := mul_le_mul_of_nonneg_left hstep hE
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 * A₀ by linarith)
  have h4 := mul_le_mul_of_nonneg_left h3
    (show (0 : ℝ) ≤ (Real.exp (P.L T / 4) * Cenv) ^ 2 by positivity)
  have hdiv : ∀ x y : ℝ, x ≤ y → x / P.L T ≤ y / P.L T := fun x y hxy => by
    have h := mul_le_mul_of_nonneg_right hxy (le_of_lt (inv_pos.mpr hL))
    simpa [div_eq_mul_inv] using h
  unfold theta0Fam theta0Q sideWQ
  exact hdiv _ _ h4

/-! ## B.5 — §7.3's family aggregation: the direct sum, `B_tr` and `B_F`

> **7.3 Aggregation without a Q-power.** Over the direct sum: the operator norm is a MAX
> (the Weyl consumer pays nothing); the trace is additive, `|tr Ê_fam| ≤ |𝔉|θ₀/(aL) =: B_tr`;
> the Frobenius norm is √-additive, `‖Ê_fam‖_F ≤ √|𝔉|·θ₀/(aL) =: B_F`.

`grep -rn "blockDiagonal\|DirectSum\|directSum" Zeta23/` returns NOTHING: [R] has no family
layer at all, so this cluster is new Lean from the ground up. All blocks share the grid size
`Fin (P.d T)` — paper §2.2, "the common taper (one coefficient vector for the whole
family)" — so `Matrix.blockDiagonal` applies directly at index `Fin (P.d T) × ι`.

OPEN QUESTION Q-4: the family index is kept ABSTRACT (`{ι : Type*} [Fintype ι]
[DecidableEq ι]`) so that §7 compiles independently of §12's `𝔉_Q` encoding;
instantiate at the §3 seam. -/

/-- `Ê_fam := ⊕_χ Ê_χ` — the block-diagonal hat-unit tail matrix over the family, at the
FREE buffer `D`.

Paper §7.3.
Depends on: `Matrix.blockDiagonal` [Mathlib], `Zeta23.Params.hat`, `Zeta23.ZeroConfig.EzD`.
Rule 17: `D` is a bare argument — the blocks are `EzD` (free buffer), never `Ez` (which
unfolds through `ZIprime` to `D0 T = √T`). No λ, no X. CLEAN. -/
def EhatFam {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Zc : ι → Zeta23.ZeroConfig) (P : Zeta23.Params) (T D : ℝ) :
    Matrix (Fin (P.d T) × ι) (Fin (P.d T) × ι) ℂ :=
  Matrix.blockDiagonal (fun χ => P.hat T ((Zc χ).EzD P T D))

/-- `Ẽ_fam := ⊕_χ Ẽ_χ` — the same in TILDE units, which is what the Weyl consumer reads.
(`Params.tilde` and `Params.hat` are different normalisations and must not be mixed —
`Zeta23/Defs.lean:301,305`.)

Paper §7.3.
Rule 17: as `EhatFam`. CLEAN. -/
def EtildeFam {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Zc : ι → Zeta23.ZeroConfig) (P : Zeta23.Params) (T D : ℝ) :
    Matrix (Fin (P.d T) × ι) (Fin (P.d T) × ι) ℂ :=
  Matrix.blockDiagonal (fun χ => P.tilde T ((Zc χ).EzD P T D))

/-- **`B_tr := |𝔉|·θ₀/(aL)`** — the ADDITIVE family loss of paper §7.3.

NAME: `OfParams` because this is the spelling at [R]'s `Zeta23.Params`, which is what §7's
own chain consumes. `ZetaQ.Btr` (in `ZetaQ/Certificate.lean`) is the same quantity spelled
at `ParamsQ` + `Family`, which is what Proposition 3.1(iv) consumes; the two agree through
`ParamsQ.toParams_L`. Kept distinct because `Certificate` and `Tail` are import-graph
siblings and neither can see the other.

Paper §7.3. Derivation: `LEMMA_QT` §QT.c, "Family instantiation"
(`|tr(⊕Ê_χ)| ≤ Σ_χ ‖Ê_χ‖₁ ≤ |𝔉|·θ₀/(aL)`).
Rule 17: `θ₀` and `cardF` are bare arguments; no buffer, no λ, no X. CLEAN. -/
def BtrOfParams (P : Zeta23.Params) (T θ₀ : ℝ) (cardF : ℕ) : ℝ :=
  (cardF : ℝ) * θ₀ / (P.a T * P.L T)

/-- **`B_F := √|𝔉|·θ₀/(aL)`** — the √-ADDITIVE family loss of paper §7.3.
The whole point of §7.3 is that `B_tr` and `B_F` are charged in their OWN roles: `B_tr ≍ Q²θ₀/(aL)`
but `B_F ≍ Q·θ₀/(aL)`, so no negative power of Q is demanded of θ₀.

Paper §7.3. Derivation: `LEMMA_QT` §QT.c
(`‖⊕Ê_χ‖²_F = Σ_χ ‖Ê_χ‖²_F ≤ |𝔉|·(θ₀/(aL))²`).
Rule 17: as `BtrOfParams`. CLEAN. -/
def BFOfParams (P : Zeta23.Params) (T θ₀ : ℝ) (cardF : ℕ) : ℝ :=
  Real.sqrt (cardF : ℝ) * θ₀ / (P.a T * P.L T)

/-- **§7.3, the trace is additive**: `|tr Ê_fam| ≤ Σ_χ ‖Ê_χ‖₁ ≤ |𝔉|·θ₀/(aL) = B_tr`.

Paper §7.3. Derivation: `LEMMA_QT` §QT.c.
Depends on: `Zeta23.Assembly.TailInputsD`, `RHLinalg.rtrace`, `EhatFam`, `BtrOfParams`.
Rule 17: `D` free (blocks are `EzD`); `haL : 0 < a·L` is the normalisation positivity that
[R]'s own `tailInputsD` carries as `ha : 0 < P.a T`. No λ, no X. CLEAN. -/
theorem abs_rtrace_EhatFam_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Zc : ι → Zeta23.ZeroConfig} {P : Zeta23.Params} {T D θ₀ : ℝ}
    (hblock : ∀ χ, Zeta23.Assembly.TailInputsD (Zc χ) P T D θ₀)
    (haL : 0 < P.a T * P.L T) :
    |RHLinalg.rtrace (EhatFam Zc P T D)| ≤ BtrOfParams P T θ₀ (Fintype.card ι) := by
  classical
  have hsum : RHLinalg.rtrace (EhatFam Zc P T D)
      = ∑ χ : ι, RHLinalg.rtrace (P.hat T ((Zc χ).EzD P T D)) := by
    show (RCLike.re (EhatFam Zc P T D).trace : ℝ) = _
    unfold EhatFam
    rw [Matrix.trace_blockDiagonal, map_sum]
    rfl
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ χ ∈ (Finset.univ : Finset ι),
      |RHLinalg.rtrace (P.hat T ((Zc χ).EzD P T D))| ≤ θ₀ / (P.a T * P.L T) := by
    intro χ _
    obtain ⟨B, _, hBtr, _, hBθ⟩ := (hblock χ).hat
    exact hBtr.trans hBθ
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold BtrOfParams
  rw [mul_div_assoc]

/-- **§7.3, the Frobenius norm is √-additive**:
`‖Ê_fam‖²_F = Σ_χ ‖Ê_χ‖²_F ≤ |𝔉|·(θ₀/(aL))² = B_F²`.

Paper §7.3. Derivation: `LEMMA_QT` §QT.c.
Depends on: `Zeta23.Assembly.TailInputsD`, `RHLinalg.frobSq`, `EhatFam`, `BFOfParams`.
Rule 17: as `abs_rtrace_EhatFam_le`. CLEAN. -/
theorem frobSq_EhatFam_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Zc : ι → Zeta23.ZeroConfig} {P : Zeta23.Params} {T D θ₀ : ℝ}
    (hblock : ∀ χ, Zeta23.Assembly.TailInputsD (Zc χ) P T D θ₀)
    (haL : 0 < P.a T * P.L T) :
    RHLinalg.frobSq (EhatFam Zc P T D) ≤ BFOfParams P T θ₀ (Fintype.card ι) ^ 2 := by
  classical
  -- (1) the Frobenius norm of a block-diagonal matrix is the sum over blocks
  have hfs : ∀ (M : ι → Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ),
      RHLinalg.frobSq (Matrix.blockDiagonal M) = ∑ χ : ι, RHLinalg.frobSq (M χ) := by
    intro M
    have h1 : RHLinalg.frobSq (Matrix.blockDiagonal M)
        = ∑ i : Fin (P.d T), ∑ k : ι, ∑ j : Fin (P.d T), ‖M k i j‖ ^ 2 := by
      rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' _ hne
        rw [Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hne)]
        simp
      · intro h; exact absurd (Finset.mem_univ k) h
    have h2 : ∑ i : Fin (P.d T), ∑ k : ι, ∑ j : Fin (P.d T), ‖M k i j‖ ^ 2
        = ∑ k : ι, ∑ i : Fin (P.d T), ∑ j : Fin (P.d T), ‖M k i j‖ ^ 2 := Finset.sum_comm
    rw [h1, h2]
    exact Finset.sum_congr rfl fun k _ =>
      (Zeta23.Assembly.frobSq_eq_sum_norm_sq (M k)).symm
  -- (2) each block is bounded by (θ₀/(aL))²
  have hterm : ∀ χ ∈ (Finset.univ : Finset ι),
      RHLinalg.frobSq (P.hat T ((Zc χ).EzD P T D)) ≤ (θ₀ / (P.a T * P.L T)) ^ 2 := by
    intro χ _
    obtain ⟨B, hB0, _, hBfr, hBθ⟩ := (hblock χ).hat
    exact hBfr.trans (by nlinarith)
  unfold EhatFam
  rw [hfs]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine le_of_eq ?_
  unfold BFOfParams
  rw [show (Real.sqrt (Fintype.card ι : ℝ) * θ₀ / (P.a T * P.L T)) ^ 2
      = Real.sqrt (Fintype.card ι : ℝ) ^ 2 * (θ₀ / (P.a T * P.L T)) ^ 2 by ring,
    Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι))]

/-! ### Three linear-algebra helpers for the block-diagonal spectral bound (OPEN QUESTION
resolved via ROUTE (a), the Rayleigh-quotient characterisation).

Neither Mathlib nor [R] has "the eigenvalues of `⊕Aᵢ` are the union of the blocks'
eigenvalues". [R] has only the FORWARD direction of the Rayleigh characterisation,
`RHLinalg.hermForm_le_of_eigenvalues_le` (`Zeta23/LinAlg/Sylvester.lean:200`). The two
missing pieces are supplied here, both by the spectral-coordinate identity
`RHLinalg.hermForm_specMap` (`Zeta23/LinAlg/HermitianPosPart.lean:77`):

  (a) `hermForm (blockDiagonal M) x = Σ_k hermForm (M k) x_k` — the form splits;
  (b) `(∀ x, |hermForm A x| ≤ θ‖x‖²) → ∀ i, |λᵢ| ≤ θ` — the CONVERSE Rayleigh bound,
      obtained by testing at the `i`-th eigenvector `x = U·eᵢ`.

Together with the two-sided forward bound they give the block-diagonal spectral bound with
NO factor of `|𝔉|`. All three are local (`private`) and Rule-17-vacuous: they mention no
`Params` field at all. -/

open Matrix in
/-- **Helper (a).** The Hermitian form of a block-diagonal matrix is the sum of the blocks'
Hermitian forms at the corresponding coordinate slices. Rule 17: no parameters. CLEAN. -/
private lemma hermForm_blockDiagonal' {m o : Type*} [Fintype m] [DecidableEq m]
    [Fintype o] [DecidableEq o] (M : o → Matrix m m ℂ) (x : m × o → ℂ) :
    RHLinalg.hermForm (Matrix.blockDiagonal M) x
      = ∑ k : o, RHLinalg.hermForm (M k) (fun i => x (i, k)) := by
  have hmv : ∀ (i : m) (k : o), (Matrix.blockDiagonal M *ᵥ x) (i, k)
      = (M k *ᵥ (fun j => x (j, k))) i := by
    intro i k
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [Matrix.blockDiagonal_apply_eq]
    · intro k' _ hne
      rw [Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hne), zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hdp : (star x : m × o → ℂ) ⬝ᵥ (Matrix.blockDiagonal M *ᵥ x)
      = ∑ k : o, (star (fun i => x (i, k)) : m → ℂ) ⬝ᵥ (M k *ᵥ (fun i => x (i, k))) := by
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun i _ => by rw [hmv i k]
  unfold RHLinalg.hermForm
  rw [hdp, map_sum]

open Matrix in
/-- **Helper (forward, two-sided).** `|λᵢ| ≤ θ` for every eigenvalue gives
`|hermForm A x| ≤ θ·‖x‖₂²`. This is the two-sided companion of [R]'s one-sided
`RHLinalg.hermForm_le_of_eigenvalues_le`, proved the same way through
`RHLinalg.hermForm_specMap`. Rule 17: no parameters. CLEAN. -/
private lemma abs_hermForm_le_of_abs_eigenvalues_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {θ : ℝ}
    (hθ : ∀ i, |hA.eigenvalues i| ≤ θ) (x : n → ℂ) :
    |RHLinalg.hermForm A x| ≤ θ * ∑ i, ‖x i‖ ^ 2 := by
  have hAx : A *ᵥ x = RHLinalg.specMap hA id *ᵥ x := by rw [RHLinalg.specMap_id]
  have h1 : RHLinalg.hermForm A x
      = ∑ i, hA.eigenvalues i
          * ‖(star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x) i‖ ^ 2 := by
    unfold RHLinalg.hermForm
    rw [hAx, RHLinalg.hermForm_specMap hA id x]
    exact Finset.sum_congr rfl fun i _ => by simp only [id_eq]
  rw [h1, ← RHLinalg.sum_normSq_unitary_mulVec hA x, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ‖(star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x) i‖ ^ 2)]
  exact mul_le_mul_of_nonneg_right (hθ i) (by positivity)

open Matrix in
/-- **Helper (b), the CONVERSE Rayleigh bound.** If `|hermForm A x| ≤ θ·‖x‖₂²` for every
`x`, then every eigenvalue of `A` obeys `|λᵢ| ≤ θ`. Test vector: the `i`-th eigenvector
`x = U·eᵢ`, for which `Uᴴx = eᵢ`, hence `hermForm A x = λᵢ` and `‖x‖₂² = 1`.
Rule 17: no parameters. CLEAN. -/
private lemma abs_eigenvalues_le_of_abs_hermForm_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {θ : ℝ}
    (h : ∀ x : n → ℂ, |RHLinalg.hermForm A x| ≤ θ * ∑ i, ‖x i‖ ^ 2) (i : n) :
    |hA.eigenvalues i| ≤ θ := by
  set e : n → ℂ := Pi.single i 1 with he
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set x : n → ℂ := U *ᵥ e with hx
  have hstar : star U *ᵥ x = e := by
    rw [hx, Matrix.mulVec_mulVec, hU,
      Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, Matrix.one_mulVec]
  have hone : ∑ j, ‖e j‖ ^ 2 = 1 := by
    rw [he]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  have hnorm : ∑ j, ‖x j‖ ^ 2 = 1 := by
    rw [← RHLinalg.sum_normSq_unitary_mulVec hA x, hstar, hone]
  have hform : RHLinalg.hermForm A x = hA.eigenvalues i := by
    have hAx : A *ᵥ x = RHLinalg.specMap hA id *ᵥ x := by rw [RHLinalg.specMap_id]
    unfold RHLinalg.hermForm
    rw [hAx, RHLinalg.hermForm_specMap hA id x, hstar, Finset.sum_eq_single i]
    · rw [he]; simp
    · intro j _ hj; rw [he]; simp [Pi.single_apply, hj]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  have hkey := h x
  rwa [hform, hnorm, mul_one] at hkey

/-- **§7.3, the operator norm is a MAX**: every eigenvalue of `Ẽ_fam` is `≤ θ₀` in absolute
value, with NO factor of `|𝔉|` — "the Weyl consumer pays nothing"; `seamA_BC`'s threshold
consumption `θ ≥ θ₀` is free.

Paper §7.3. Derivation: `LEMMA_QT` §QT.c, "Family instantiation".
**RESOLVED by ROUTE (a)**,
the Rayleigh-quotient / quadratic-form characterisation, through the three private helpers
above: the block form splits (`hermForm_blockDiagonal'`), each block's spectral bound gives
a two-sided form bound (`abs_hermForm_le_of_abs_eigenvalues_le`, the two-sided companion of
[R]'s `RHLinalg.hermForm_le_of_eigenvalues_le`), and the converse Rayleigh bound
(`abs_eigenvalues_le_of_abs_hermForm_le`) reads the family bound back off the form. The
`|𝔉|`-freeness is exactly the fact that the *slices* `x_χ` partition `‖x‖₂²`, so the
per-block bounds add up to `θ₀·‖x‖₂²` and not `|𝔉|·θ₀·‖x‖₂²`.
Depends on: `Zeta23.Assembly.TailInputsD`, `EtildeFam`, `RHLinalg.hermForm_specMap`.
Rule 17: `D` free; blocks are `EzD`; no λ, no X. CLEAN. -/
theorem abs_eigenvalues_EtildeFam_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Zc : ι → Zeta23.ZeroConfig} {P : Zeta23.Params} {T D θ₀ : ℝ}
    (hblock : ∀ χ, Zeta23.Assembly.TailInputsD (Zc χ) P T D θ₀)
    (hH : (EtildeFam Zc P T D).IsHermitian) :
    ∀ i, |hH.eigenvalues i| ≤ θ₀ := by
  refine abs_eigenvalues_le_of_abs_hermForm_le hH ?_
  intro x
  have hsplit : RHLinalg.hermForm (EtildeFam Zc P T D) x
      = ∑ χ : ι, RHLinalg.hermForm (P.tilde T ((Zc χ).EzD P T D)) (fun i => x (i, χ)) :=
    hermForm_blockDiagonal' (fun χ => P.tilde T ((Zc χ).EzD P T D)) x
  have hterm : ∀ χ ∈ (Finset.univ : Finset ι),
      |RHLinalg.hermForm (P.tilde T ((Zc χ).EzD P T D)) (fun i => x (i, χ))|
        ≤ θ₀ * ∑ i : Fin (P.d T), ‖x (i, χ)‖ ^ 2 := by
    intro χ _
    obtain ⟨hEt, hev⟩ := (hblock χ).tilde
    exact abs_hermForm_le_of_abs_eigenvalues_le hEt hev _
  have hsum : ∑ p : Fin (P.d T) × ι, ‖x p‖ ^ 2
      = ∑ χ : ι, ∑ i : Fin (P.d T), ‖x (i, χ)‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hsplit, hsum, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)

/-! ## B.6 — THE PAIR PERTURBATION LEMMA (§7.3's headline)

> **§7.3** "The pair perturbation lemma
> (`4 tr Ĝ − ‖Ĝ‖²_F − [4B_tr + 2B_F‖Ĝ‖_F + B_F²] ≤ 4 tr Â − ‖Â‖²_F`; three lines,
> generalizing [R]'s scalar version, which is the case `B_tr = B_F`) feeds Proposition
> 3.1's (iv) with per-block `θ₀ → 0` only: **no negative power of Q is demanded anywhere.**
> (The verbatim scalar interface would demand `θ₀ = o(Q^{−1}·polylog)`; the pair costs
> nothing and removes it.)" -/

/-- **PAIR PERTURBATION LEMMA** (paper §7.3; companion notes Lemma QT.c).
The generalization of `Zeta23.Assembly.four_tr_sub_frobSq_perturb`
(`Zeta23/Assembly.lean:150`) in which the record's single scalar `B` is split into the pair
`(B_tr, B_F)`: `|tr Ê| ≤ B_tr` and `‖Ê‖²_F ≤ B_F²` SEPARATELY. [R]'s lemma is the diagonal
case `B_tr = B_F = B`, since `4B + 2B√frobSq + B² = B(4 + 2√frobSq + B)`.

Paper §7.3. Derivation: `LEMMA_QT` §QT.c ("tr Â = tr Ĝ − tr Ê ≥
tr Ĝ − B_tr by linearity; ‖Â‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F ≤ ‖Ĝ‖_F + B_F by the Frobenius triangle
inequality, `Zeta23.Assembly.frobSq_sub_le`, `Assembly.lean:138`; combine").
Depends on: `Zeta23.Assembly.frobSq_sub_le`, `frobSq_eq_norm_sq`, `norm_eq_sqrt_frobSq`,
`frobSq_nonneg`.
Hypothesis notes: (a) `hBtr : 0 ≤ BtrOfParams` is derivable from `htrE` (an absolute value is `≥ 0`)
but LEMMA_QT.c states "B_tr, B_F ≥ 0" explicitly and [R] carries `hB : 0 ≤ B`, so fidelity
beats economy; (b) `hBF : 0 ≤ BFOfParams` is NOT derivable from `hfrE` and is genuinely needed —
it is what makes `√(frobSq Ê) ≤ BFOfParams`; (c) [R]'s section has `[Fintype n]` but NO
`[DecidableEq n]`, and the pair version needs no more.
Rule 17: the statement is pure matrix algebra over `RCLike 𝕜`. There is no `Params`, no `T`,
no `L`, no `D`, no `lam`, no `X`. **Structurally impossible to smuggle λ ≤ 1, X ≤ T, or
D₀ = √T. CLEAN.** -/
theorem four_tr_sub_frobSq_perturb_pair
    {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    {Ghat Ahat Ehat : Matrix n n 𝕜}
    (hGAE : Ghat = Ahat + Ehat) {BtrOfParams BFOfParams : ℝ} (hBtr : 0 ≤ BtrOfParams) (hBF : 0 ≤ BFOfParams)
    (htrE : |RHLinalg.rtrace Ehat| ≤ BtrOfParams)
    (hfrE : RHLinalg.frobSq Ehat ≤ BFOfParams ^ 2) :
    4 * RHLinalg.rtrace Ghat - RHLinalg.frobSq Ghat
        - (4 * BtrOfParams + 2 * BFOfParams * Real.sqrt (RHLinalg.frobSq Ghat) + BFOfParams ^ 2)
      ≤ 4 * RHLinalg.rtrace Ahat - RHLinalg.frobSq Ahat := by
  have hA : Ahat = Ghat - Ehat := by rw [hGAE]; abel
  have htr : RHLinalg.rtrace Ahat = RHLinalg.rtrace Ghat - RHLinalg.rtrace Ehat := by
    rw [hA, RHLinalg.rtrace_sub]
  have hsqE : Real.sqrt (RHLinalg.frobSq Ehat) ≤ BFOfParams :=
    Real.sqrt_le_iff.mpr ⟨hBF, hfrE⟩
  have hsqG : 0 ≤ Real.sqrt (RHLinalg.frobSq Ghat) := Real.sqrt_nonneg _
  have hfrA : RHLinalg.frobSq Ahat
      ≤ (Real.sqrt (RHLinalg.frobSq Ghat) + BFOfParams) ^ 2 := by
    rw [hA]
    refine (Zeta23.Assembly.frobSq_sub_le Ghat Ehat).trans ?_
    gcongr
  have hGG : Real.sqrt (RHLinalg.frobSq Ghat) ^ 2 = RHLinalg.frobSq Ghat :=
    Real.sq_sqrt (Zeta23.Assembly.frobSq_nonneg _)
  have htrE' : RHLinalg.rtrace Ehat ≤ BtrOfParams := (le_abs_self _).trans htrE
  nlinarith [hfrA, hGG, htrE', htr]

/-- **The record's lemma is the diagonal case** `B_tr = B_F = B` — the paper's "generalizing
[R]'s scalar version, which is the case `B_tr = B_F`", stated as a consistency check.
NOT a dependency of anything.

Paper §7.3.
Depends on: `four_tr_sub_frobSq_perturb_pair`.
Rule 17: pure matrix algebra; no `Params`, no `D`, no λ, no X. CLEAN. -/
theorem four_tr_sub_frobSq_perturb_pair_diag
    {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    {Ghat Ahat Ehat : Matrix n n 𝕜} (hGAE : Ghat = Ahat + Ehat) {B : ℝ} (hB : 0 ≤ B)
    (htrE : |RHLinalg.rtrace Ehat| ≤ B)
    (hfrE : RHLinalg.frobSq Ehat ≤ B ^ 2) :
    4 * RHLinalg.rtrace Ghat - RHLinalg.frobSq Ghat
        - B * (4 + 2 * Real.sqrt (RHLinalg.frobSq Ghat) + B)
      ≤ 4 * RHLinalg.rtrace Ahat - RHLinalg.frobSq Ahat := by
  have hEq : B * (4 + 2 * Real.sqrt (RHLinalg.frobSq Ghat) + B)
      = 4 * B + 2 * B * Real.sqrt (RHLinalg.frobSq Ghat) + B ^ 2 := by ring
  rw [hEq]
  exact four_tr_sub_frobSq_perturb_pair hGAE hB hB htrE hfrE

/-! ## B.7 — the missing `∀ᶠ T` wrappers (PHASE1_INTERFACES §7.4)

PHASE1_INTERFACES §7.4 lists four `[R]` declarations with no D-generic/Gevrey counterpart:
`Zeta23.Tail.eventually_tailInputs` (`Tail.lean:651`), `Tail.eventually_theta0_le`
(`Tail.lean:668`), `Tail.eventually_NII_le` (`Tail.lean:677`) and
`Tail.eventually_tailPackage` (`Tail/Package.lean:36`).

**Does §7 need them? YES, all four** — but only in FREE-BUFFER form, i.e. quantified over a
buffer PROFILE `D : ℝ → ℝ` rather than a number. §7 itself is a fixed-design-point section
(and `ZetaQ.ParamsQ` pins `T` as a field, so an `∀ᶠ T` statement cannot be phrased at
`ParamsQ` at all); but §7's own consumer, Theorem 1's asymptotic, quantifies over a family of
design points, and §3/§10's `Zeta23.Assembly.count_certificate_free` (`WindowD.lean:183`)
takes its inputs in `∀ᶠ T` / `isLittleO` form. So the wrappers are stated here at
`Zeta23.Params` with an explicit buffer profile.

**⚠ NAMING (PHASE1_INTERFACES §7.2 item 7).** A trailing `D` already means Theorem D's
Montgomery–Taylor window `P.atD T` in ~20 pre-existing declarations, and
`Zeta23.ThmD.eventually_tailPackageD` (`ThmD/ZeroSideD.lean:155`) in particular LOOKS like
the missing free-buffer package and is NOT (its conclusion is the record's
`Assembly.TailInputs`, i.e. `D = √T`). Nothing in this file carries a trailing `D`; the
free-buffer wrappers are suffixed `Free`. -/

/-- **`∀ᶠ T` form of the QT.a ⟹ QT.b bridge at a free buffer profile** — the missing mirror
of `Zeta23.Tail.eventually_tailInputs` (`Zeta23/Tail.lean:651`) at the level of `TailHypG`.

Paper §7.2, eventual-in-T form.
Depends on: `Zeta23.Tail.TailHypG.of_profile`,
`Zeta23.Tail.tendsto_L_atTop`.
Rule 17: the buffer is an arbitrary PROFILE `D : ℝ → ℝ` with only `1 ≤ D T` eventually —
`Real.sqrt` is nowhere; `hP : P.ValidQ` is the weakened class (no `lam_le_one`), but see
FINDING F-0. No X. CLEAN. -/
theorem eventually_tailHypFree (Z : Zeta23.ZeroConfig) (P : Zeta23.Params)
    (hP : P.ValidQ) {A B A₀ : ℝ} (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (D : ℝ → ℝ) (hD : ∀ᶠ T in Filter.atTop, 1 ≤ D T) :
    ∀ᶠ T in Filter.atTop,
      Zeta23.Tail.TailHypG Z P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) (D T) := by
  have hL2 : ∀ᶠ T in Filter.atTop, 2 ≤ P.L T :=
    (Zeta23.Tail.tendsto_L_atTop P hP).eventually_ge_atTop 2
  have hL8 : ∀ᶠ T in Filter.atTop, 8 * P.w ≤ P.L T :=
    (Zeta23.Tail.tendsto_L_atTop P hP).eventually_ge_atTop (8 * P.w)
  filter_upwards [Filter.eventually_ge_atTop Zeta23.Tail.T₀, hL2, hL8, hD]
    with T hT hL hwL hD1
  exact Zeta23.Tail.TailHypG.of_profile hϱ hP hwL hT hL hA₀ hloc hD1

/-- **`∀ᶠ T` form of QT.b(5) at a free buffer profile** — the missing D-generic mirror of
`Zeta23.Tail.eventually_tailInputs` (`Zeta23/Tail.lean:651`) proper.

Paper §7.2, eventual-in-T form.
Depends on: `eventually_tailHypFree`, `Zeta23.Tail.TailHypG.tailInputsD`.
Rule 17: buffer PROFILE, no `√T`; the target is `TailInputsD`, never `Assembly.TailInputs`
(RESOLUTION R-4's DO-NOT-CITE rule). No λ, no X. CLEAN. -/
theorem eventually_tailInputsFree (Z : Zeta23.ZeroConfig) (P : Zeta23.Params)
    (hP : P.ValidQ) {A B A₀ : ℝ} (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (D : ℝ → ℝ) (hD : ∀ᶠ T in Filter.atTop, 1 ≤ D T)
    (ha : ∀ᶠ T in Filter.atTop, 0 < P.a T)
    (hconj : ∀ᶠ T in Filter.atTop, ∀ z : ℂ,
      P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    ∀ᶠ T in Filter.atTop, Zeta23.Assembly.TailInputsD Z P T (D T)
      (Zeta23.Tail.theta0G P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) (D T)) := by
  filter_upwards [eventually_tailHypFree Z P hP hϱ hA₀ hloc D hD, ha, hconj]
    with T H ha' hc'
  exact H.tailInputsD ha' hc'

/-- **`∀ᶠ T` form of the θ₀ size estimate** — the missing mirror of
`Zeta23.Tail.eventually_theta0_le` (`Zeta23/Tail.lean:668`). The rate input is §7.2's
CLOSING CONDITION, held eventually along the design family, and the conclusion is the
paper's target `θ₀ ≤ η/L`.

⚠ **NON-STRICT** (FLAG F-1): `hclose` is `needed ≤ supplied`, admitting equality — the
design of record has margin exactly 0 nats at every Q.

Paper §7.2, eventual-in-T form.
Depends on: `theta0G_le`.
Rule 17: buffer PROFILE `D : ℝ → ℝ`, no `√T`; no λ; no X. CLEAN. -/
theorem eventually_theta0G_le (P : Zeta23.Params) {A₀ A : ℝ} (Cenv D η : ℝ → ℝ)
    (hw : 0 < P.w) (hA : 0 < A)
    (hL : ∀ᶠ T in Filter.atTop, 0 < P.L T)
    (hDnn : ∀ᶠ T in Filter.atTop, 0 ≤ D T)
    (hη : ∀ᶠ T in Filter.atTop, 0 < η T)
    (hpre : ∀ᶠ T in Filter.atTop, 0 < prefactorG P T A₀ A (Cenv T) (D T))
    (hclose : ∀ᶠ T in Filter.atTop,
      P.L T / 2 + Real.log (prefactorG P T A₀ A (Cenv T) (D T)) + Real.log (P.L T / η T)
        ≤ (4 / Real.exp 1) * Real.sqrt (P.w * D T / A)) :
    ∀ᶠ T in Filter.atTop,
      Zeta23.Tail.theta0G P T A₀ A (Cenv T) (D T) ≤ η T / P.L T := by
  filter_upwards [hL, hDnn, hη, hpre, hclose] with T hL' hD' hη' hpre' hcl
  exact theta0G_le hL' hη' hw hA hD' hpre' hcl

/-- **`∀ᶠ T` form of the buffer count** — the missing mirror of
`Zeta23.Tail.eventually_NII_le` (`Zeta23/Tail.lean:677`); PHASE1_INTERFACES "Not found"
item 3 records that only the fixed-`T` `NIID_le` exists. This is what supplies `hNII_o` to
`Zeta23.Assembly.count_certificate_free` (`Zeta23/WindowD.lean:183`).

Paper §7.2 feeding §10's budget row L₄.
Depends on: `Zeta23.Tail.NIID_le`.
Rule 17: the two hypotheses `2 ≤ D T` and `D T + 4 ≤ T` are the STRICTLY STRONGER counting
regime of PHASE1_INTERFACES §7.1 — [R] got them free from `√T ≥ 17`; here they are explicit
constraints on the buffer PROFILE, which is precisely the free-buffer statement. No `√T`.
No λ, no X. CLEAN. -/
theorem eventually_NIID_le (Z : Zeta23.ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (D : ℝ → ℝ) (hD2 : ∀ᶠ T in Filter.atTop, 2 ≤ D T)
    (hDT : ∀ᶠ T in Filter.atTop, D T + 4 ≤ T) :
    ∀ᶠ T in Filter.atTop,
      (Zeta23.Assembly.NIID Z T (D T) : ℝ) ≤ 3 * A₀ * D T * Real.log (4 * T) := by
  filter_upwards [Filter.eventually_ge_atTop Zeta23.Tail.T₀, hD2, hDT] with T hT h2 h4
  exact Zeta23.Tail.NIID_le Z hA₀ hloc hT h2 h4

/-- **The packaged §7.2 statement at a free buffer** — the missing mirror of
`Zeta23.Tail.eventually_tailPackage` (`Zeta23/Tail/Package.lean:36`). Deliberately NOT
called `eventually_tailPackageD`: that name is taken by `Zeta23.ThmD.eventually_tailPackageD`
(`ThmD/ZeroSideD.lean:155`), whose `D` is Theorem D's `P.atD` window and whose conclusion is
the record's `Assembly.TailInputs` at `D = √T` (PHASE1_INTERFACES §7.2 item 7, "Not found"
item 3).

The second conjunct replaces [R]'s `θ₀ ≤ C·l·T^{λ/2−1}` by the paper's own target
`θ₀ ≤ η/L` ("θ₀ → 0 faster than any required rate"), driven by the CLOSING CONDITION.

⚠ **NON-STRICT** (FLAG F-1) in `hclose`.

Paper §7.2. Depends on: `eventually_tailInputsFree`, `eventually_theta0G_le`.
Rule 17: buffer PROFILE with only `1 ≤ D T` eventually; conclusion is `TailInputsD`;
`hP : P.ValidQ` carries no `lam_le_one` (but see FINDING F-0). No X. CLEAN. -/
theorem eventually_tailPackageFree (Z : Zeta23.ZeroConfig) (P : Zeta23.Params)
    (hP : P.ValidQ) {A B A₀ : ℝ} (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (D η : ℝ → ℝ) (hD : ∀ᶠ T in Filter.atTop, 1 ≤ D T)
    (hη : ∀ᶠ T in Filter.atTop, 0 < η T)
    (ha : ∀ᶠ T in Filter.atTop, 0 < P.a T)
    (hconj : ∀ᶠ T in Filter.atTop, ∀ z : ℂ,
      P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z))
    (hclose : ∀ᶠ T in Filter.atTop,
      P.L T / 2
        + Real.log (prefactorG P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) (D T))
        + Real.log (P.L T / η T)
      ≤ (4 / Real.exp 1) * Real.sqrt (P.w * D T / A)) :
    ∃ θ₀ : ℝ → ℝ,
      (∀ᶠ T in Filter.atTop, Zeta23.Assembly.TailInputsD Z P T (D T) (θ₀ T))
        ∧ (∀ᶠ T in Filter.atTop, θ₀ T ≤ η T / P.L T) := by
  refine ⟨fun T => Zeta23.Tail.theta0G P T A₀ A
      (Real.exp 2 * max (2 * B * P.w) (P.L T)) (D T),
    eventually_tailInputsFree Z P hP hϱ hA₀ hloc D hD ha hconj, ?_⟩
  have hw : 0 < P.w := Zeta23.Params.w_pos hP
  have hA : 0 < A := hϱ.A_pos
  have hL0 : ∀ᶠ T in Filter.atTop, 0 < P.L T :=
    (Zeta23.Tail.tendsto_L_atTop P hP).eventually_gt_atTop 0
  filter_upwards [hL0, hD, hη, hclose] with T hLT hDT hηT hcl
  by_cases hp : 0 < prefactorG P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) (D T)
  · exact theta0G_le hLT hηT hw hA (by linarith) hp hcl
  · -- degenerate case: a nonpositive prefactor forces `θ₀G ≤ 0 < η/L`
    rw [theta0G_eq]
    have hple : prefactorG P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) (D T) ≤ 0 :=
      not_lt.mp hp
    have h2 : 0 < η T / P.L T := div_pos hηT hLT
    have hprod : (0:ℝ) ≤ Real.exp (P.L T / 2)
        * Real.exp (-(4 / Real.exp 1) * Real.sqrt (P.w * D T / A)) := by positivity
    have key : Real.exp (P.L T / 2)
        * prefactorG P T A₀ A (Real.exp 2 * max (2 * B * P.w) (P.L T)) (D T)
        * Real.exp (-(4 / Real.exp 1) * Real.sqrt (P.w * D T / A)) ≤ 0 := by
      nlinarith [hprod, hple]
    linarith

/-! ############################################################################
# PART B.8 — §7.3's PAIR SPLIT AT THE FAMILY LEVEL, in the spelling `ZetaQ/EFChi.lean`
# consumes. ZERO sorries.
############################################################################

`ZetaQ/EFChi.lean`'s family join — `EFChi.certificate_display_fam_of_bridge` and
`EFChi.prop31_fam`, both sorry-free — carries §7.3's pair split as two NAMED HYPOTHESES it
does not prove:

    hpairTr : |trGzFam P F Qn Zc − trAhatFam P F Qn Zc| ≤ Btr P F Qn θ₀
    hpairF  : √(frobSqAhatFam P F Qn Zc) − √(frobSqGzFam P F Qn Zc) ≤ BF P F Qn θ₀

This part discharges both. The two theorems below are stated with `EFChi`'s four aggregates
UNFOLDED to their bodies (`familySum F Qn fun q χ => RHLinalg.rtrace (P.toParams.hat P.T …)`
etc.) — `EFChi` imports `Certificate` and would import `Tail`, so `Tail` cannot see
`EFChi.trGzFam`. The bodies are definitionally the aggregates, so at the join the two
theorems close the two slots by `exact` with no massaging; that has been machine-checked
against `EFChi`'s own elaborated statement.

**WHY THIS IS NOT `abs_rtrace_EhatFam_le` / `frobSq_EhatFam_le` (B.5) VERBATIM.** Those are
the same two facts in the *block-diagonal* spelling at an abstract `Fintype` family index
`ι` (OPEN QUESTION Q-4). §3's family object is not a `Fintype`-indexed direct sum but the
DEPENDENT DOUBLE SUM `ZetaQ.familySum` (`∑_{q ∈ F.moduli Qn} ∑*_{χ mod q}`), and the two
never meet without an encoding of `𝔉_Q` as a type. So B.8 flattens `familySum` to a single
`Finset (Σ q, DirichletCharacter ℂ q)` (`Finset.sum_sigma'`) and runs the same two
arguments there. `EhatFam_eq_sub` below records the bridge in the block-diagonal spelling
too, so the B.5 route is not orphaned.

**THE BRIDGE**, which is what B.5 lacked and this part supplies: per member,
`Ê_χ = Ĝ_χ − Â_χ(D₀)`. That is not an assumption — `Zeta23.ZeroConfig.EzD` is *defined* as
`Gz − AzD` (`Zeta23/Tail/GevreyTail.lean:1429`), and `Zeta23.Params.hat` is a scalar `•`, so
it is `smul_sub` + `RHLinalg.rtrace_sub` / `Zeta23.Assembly.frobSq_sub_le`.

**⚠ THE ORIENTATION OF `hpairF`.** It is `√(frobSqAhat) − √(frobSqGz) ≤ B_F`, i.e. the
paper's own §7.3 step `‖Â‖_F ≤ ‖Ĝ‖_F + B_F`. The reverse reading is FALSE and
was caught twice in this project; `ZetaQ/Certificate.lean`'s `pair_perturbation` records the
machine-checked failing instance (`trG = trA = 0`, `frobSqG = 0`, `frobSqA = 100`, `B = 0`
satisfies the reversed hypothesis and makes the conclusion read `0 ≤ −100`). B.8 is in the
paper's direction, and the direction is forced by the proof: the Frobenius triangle
inequality bounds the truncated side ABOVE by the full side.

**Rule 17.** `D` is `P.D0`, a FIELD; the blocks are `AzD`/`EzD` at that free buffer, never
`Az`/`Ez` (which unfold through `ZIprime` to `Zeta23.D0 T = √T`). `θ₀` is a bare real. No
`P.lam` hypothesis, no `X`, no relation between `P.XQ` and `P.T`. `hl : Zeta23.l P.T ≠ 0` is
the `toParams_L` side condition (`T ≠ 2π`, free at `T ≥ 300`), and
`hB0 : 0 ≤ θ₀/(P.aQ · P.LB)` is normalisation positivity — the same hypothesis
`ZetaQ/EFChi.lean` already carries in `∀ᶠ Q` form. Neither is one of the three
forbidden facts. CLEAN.

**Scope-trap note.** `θ₀`, `Zc`, `F`, `Qn` are all quantified in the theorem binders, ahead
of every hypothesis that mentions them; nothing is introduced after the design point. -/

/-- **THE BRIDGE, block-diagonal spelling**: `Ê_fam = Ĝ_fam − Â_fam(D)` over the direct sum.
Pure unfolding — `EzD` IS `Gz − AzD` and `blockDiagonal`/`hat` are both additive — recorded
so that B.5's `abs_rtrace_EhatFam_le` / `frobSq_EhatFam_le` have their perturbation identity
in the same units they are stated in.

Paper §7.3.
Depends on: `Matrix.blockDiagonal_sub`, `Zeta23.ZeroConfig.EzD`.
Rule 17: `D` is a bare argument; blocks are `AzD` (free buffer). No λ, no X. CLEAN. -/
theorem EhatFam_eq_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Zc : ι → Zeta23.ZeroConfig) (P : Zeta23.Params) (T D : ℝ) :
    EhatFam Zc P T D
      = Matrix.blockDiagonal (fun χ => P.hat T ((Zc χ).Gz P T))
        - Matrix.blockDiagonal (fun χ => P.hat T ((Zc χ).AzD P T D)) := by
  unfold EhatFam
  rw [← Matrix.blockDiagonal_sub]
  refine congrArg Matrix.blockDiagonal ?_
  funext χ
  show P.hat T ((Zc χ).Gz P T - (Zc χ).AzD P T D) = _
  unfold Zeta23.Params.hat
  rw [smul_sub]
  rfl

/-- `𝔉_Q` as a SINGLE `Finset` of dependent pairs `⟨q, χ⟩`, so that Cauchy–Schwarz and the
cardinality count can be run once instead of twice. Rule 17: no parameter occurs. -/
private def famIdx (F : Family) (Qn : ℕ) : Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (F.moduli Qn).sigma (fun q => F.chars q)

/-- `ZetaQ.familySum` is the sum over `famIdx`. Rule 17: no parameter occurs. -/
private lemma familySum_eq_sum_famIdx (F : Family) (Qn : ℕ)
    (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    familySum F Qn f = ∑ x ∈ famIdx F Qn, f x.1 x.2 :=
  Finset.sum_sigma' _ _ _

/-- `|famIdx F Qn| = |𝔉_Q|` — this is what makes `Btr`/`BF`'s `F.sizeR Qn` the cardinality
the per-member bounds are summed over. All SIX cases are `rfl`: `Family.size` is
`∑ q ∈ F.moduli Qn, (F.chars q).card` in every branch (`Family.size_eq`), and for
`qle`/`dyadic` that is `∑_q phiStar q = ∑_q (primitiveChars q).card`, i.e.
`famCard − φ*(1)` / `famCardDyadic`. Rule 17: no parameter occurs. -/
private lemma card_famIdx (F : Family) (Qn : ℕ) :
    ((famIdx F Qn).card : ℝ) = F.sizeR Qn := by
  unfold famIdx Family.sizeR
  rw [Finset.card_sigma]
  cases F with
  | qle => rfl
  | dyadic => rfl
  | evenQle => rfl
  | oddQle => rfl
  | evenDyadic => rfl
  | oddDyadic => rfl
  | evenQleR => rfl
  | oddQleR => rfl
  | evenDyadicR => rfl
  | oddDyadicR => rfl

/-- ℓ¹ over a `Finset`: the ADDITIVE aggregation of §7.3's trace side.
Rule 17: no parameter occurs. -/
private lemma abs_sum_le_card_mul {ι : Type*} (S : Finset ι) (f : ι → ℝ) {c : ℝ}
    (h : ∀ i ∈ S, |f i| ≤ c) : |∑ i ∈ S, f i| ≤ (S.card : ℝ) * c := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- ℓ² over a `Finset`: the √-ADDITIVE aggregation of §7.3's Frobenius side. From the
pointwise `a ≤ g + c` it derives `‖a‖₂ ≤ ‖g‖₂ + √|S|·c`, which is where the `√|𝔉|` of
`B_F = √|𝔉|θ₀/(aL)` comes from (and why the trace side gets a bare `|𝔉|` and the Frobenius
side does not). The only nontrivial input is Chebyshev/Cauchy–Schwarz with `f ≡ 1`,
`Mathlib`'s `sq_sum_le_card_mul_sum_sq`, giving `∑ g ≤ √|S|·√(∑ g²)`.
Rule 17: no parameter occurs. -/
private lemma sqrt_sum_sq_le_sqrt_add_sqrt_card_mul {ι : Type*} (S : Finset ι) (a g : ι → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (ha : ∀ i ∈ S, 0 ≤ a i) (hg : ∀ i ∈ S, 0 ≤ g i)
    (hag : ∀ i ∈ S, a i ≤ g i + c) :
    Real.sqrt (∑ i ∈ S, a i ^ 2)
      ≤ Real.sqrt (∑ i ∈ S, g i ^ 2) + Real.sqrt (S.card : ℝ) * c := by
  set SG := ∑ i ∈ S, g i ^ 2 with hSGdef
  have hSG0 : 0 ≤ SG := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsG : Real.sqrt SG ^ 2 = SG := Real.sq_sqrt hSG0
  have hsG0 : 0 ≤ Real.sqrt SG := Real.sqrt_nonneg _
  have hcard : Real.sqrt (S.card : ℝ) ^ 2 = (S.card : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hcard0 : 0 ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
  have hg0 : 0 ≤ ∑ i ∈ S, g i := Finset.sum_nonneg hg
  have hCS : ∑ i ∈ S, g i ≤ Real.sqrt (S.card : ℝ) * Real.sqrt SG := by
    have h1 : (∑ i ∈ S, g i) ^ 2 ≤ (S.card : ℝ) * SG := sq_sum_le_card_mul_sum_sq
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hg0, Real.sqrt_mul (Nat.cast_nonneg _)] at h2
  have hstep : ∑ i ∈ S, a i ^ 2 ≤ (Real.sqrt SG + Real.sqrt (S.card : ℝ) * c) ^ 2 := by
    have h2 : ∑ i ∈ S, a i ^ 2 ≤ ∑ i ∈ S, (g i + c) ^ 2 :=
      Finset.sum_le_sum fun i hi => by
        have h3 := ha i hi; have h4 := hag i hi
        nlinarith [hg i hi, hc]
    have h3 : ∑ i ∈ S, (g i + c) ^ 2
        = SG + 2 * c * (∑ i ∈ S, g i) + (S.card : ℝ) * c ^ 2 := by
      have hexp : ∀ i, (g i + c) ^ 2 = g i ^ 2 + 2 * c * g i + c ^ 2 := fun i => by ring
      simp only [hexp]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, hSGdef]
    have h4 : 2 * c * (∑ i ∈ S, g i)
        ≤ 2 * c * (Real.sqrt (S.card : ℝ) * Real.sqrt SG) :=
      mul_le_mul_of_nonneg_left hCS (by linarith)
    have h5 : (Real.sqrt SG + Real.sqrt (S.card : ℝ) * c) ^ 2
        = SG + 2 * c * (Real.sqrt (S.card : ℝ) * Real.sqrt SG) + (S.card : ℝ) * c ^ 2 := by
      rw [show (Real.sqrt SG + Real.sqrt (S.card : ℝ) * c) ^ 2
            = Real.sqrt SG ^ 2 + 2 * c * (Real.sqrt (S.card : ℝ) * Real.sqrt SG)
              + Real.sqrt (S.card : ℝ) ^ 2 * c ^ 2 from by ring, hsG, hcard]
    rw [h5]
    linarith [h2, h3.le, h3.ge]
  calc Real.sqrt (∑ i ∈ S, a i ^ 2)
      ≤ Real.sqrt ((Real.sqrt SG + Real.sqrt (S.card : ℝ) * c) ^ 2) := Real.sqrt_le_sqrt hstep
    _ = Real.sqrt SG + Real.sqrt (S.card : ℝ) * c := Real.sqrt_sq (by positivity)

/-- `Zeta23.Params.hat` is a scalar `•`, hence additive. Rule 17: `hat` carries `a` and `L`
but no hypothesis; this is `smul_sub`. CLEAN. -/
private lemma hat_sub (Q : Zeta23.Params) (T : ℝ) {n : Type*}
    (M N : Matrix n n ℂ) : Q.hat T (M - N) = Q.hat T M - Q.hat T N := by
  unfold Zeta23.Params.hat; rw [smul_sub]

/-- **§7.3's TRACE half of the pair split, at the family level — `EFChi`'s `hpairTr`.**

    `|tr Ĝ_fam − tr Â_fam(D₀)| = |tr Ê_fam| ≤ |𝔉_Q|·θ₀/(aL) = Btr P F Qn θ₀`

The statement is `EFChi.trGzFam`/`EFChi.trAhatFam` with their bodies written out (see PART
B.8's header for why `Tail` cannot name them): `familySum F Qn fun q χ => RHLinalg.rtrace
(P.toParams.hat P.T (…))`, at `Gz` and at `AzD … P.D0` respectively. It therefore closes
`EFChi.certificate_display_fam_of_bridge`'s and `EFChi.prop31_fam`'s `hpairTr` slot by
`exact`; machine-checked.

Proof: `Ê = Ĝ − Â` per member (`Zeta23.ZeroConfig.EzD` is defined as `Gz − AzD`, and `hat`
is a `•`), then `Finset.abs_sum_le_sum_abs` over the flattened family index, then the `hat`
clause of `Zeta23.Assembly.TailInputsD` at each member (`|tr Ê_χ| ≤ B ≤ θ₀/(aL)`), then
`card_famIdx`. The `|𝔉_Q|` is exactly the number of summands — this is the ADDITIVE side of
§7.3, which is why `B_tr ≍ Q²θ₀/(aL)`.

Paper §7.3. Derivation: `LEMMA_QT` §QT.c, "Family instantiation".
Depends on: `Zeta23.Assembly.TailInputsD`, `RHLinalg.rtrace_sub`, `ParamsQ.toParams_L`,
`Finset.sum_sigma'`, `ZetaQ.Btr`.
Rule 17: `P.D0` is a FIELD, the blocks are `AzD`/`EzD` at it (never `Az`/`Ez`); `hl` is the
`toParams_L` side condition; no λ, no X. CLEAN. -/
theorem abs_trGz_sub_trAhat_fam_le_Btr
    (P : ParamsQ) (F : Family) (Qn : ℕ) (θ₀ : ℝ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hl : Zeta23.l P.T ≠ 0)
    (hblock : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      Zeta23.Assembly.TailInputsD (Zc q χ) P.toParams P.T P.D0 θ₀) :
    |familySum F Qn (fun q χ =>
          RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).Gz P.toParams P.T)))
        - familySum F Qn (fun q χ =>
          RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0)))|
      ≤ Btr P F Qn θ₀ := by
  classical
  have haL : P.toParams.a P.T * P.toParams.L P.T = P.aQ * P.LB := by
    rw [P.toParams_L hl]; rfl
  rw [familySum_eq_sum_famIdx, familySum_eq_sum_famIdx, ← Finset.sum_sub_distrib]
  have hterm : ∀ x ∈ famIdx F Qn,
      |RHLinalg.rtrace (P.toParams.hat P.T ((Zc x.1 x.2).Gz P.toParams P.T))
        - RHLinalg.rtrace (P.toParams.hat P.T ((Zc x.1 x.2).AzD P.toParams P.T P.D0))|
        ≤ θ₀ / (P.aQ * P.LB) := by
    intro x hx
    obtain ⟨q, χ⟩ := x
    simp only [famIdx, Finset.mem_sigma] at hx
    obtain ⟨B, hB0a, hBtr, hBfr, hBθ⟩ := (hblock q hx.1 χ (F.chars_subset q hx.2)).hat
    have hE : RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).EzD P.toParams P.T P.D0))
        = RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).Gz P.toParams P.T))
          - RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0)) := by
      show RHLinalg.rtrace (P.toParams.hat P.T
          ((Zc q χ).Gz P.toParams P.T - (Zc q χ).AzD P.toParams P.T P.D0)) = _
      rw [hat_sub, RHLinalg.rtrace_sub]
    rw [← hE]
    refine hBtr.trans (hBθ.trans ?_)
    rw [haL]
  refine (abs_sum_le_card_mul _ _ hterm).trans ?_
  rw [card_famIdx]
  unfold Btr
  rw [mul_div_assoc]

/-- **§7.3's FROBENIUS half of the pair split, at the family level — `EFChi`'s `hpairF`.**

    `‖Â_fam(D₀)‖_F ≤ ‖Ĝ_fam‖_F + √|𝔉_Q|·θ₀/(aL)`,  i.e.
    `√(frobSqAhatFam) − √(frobSqGzFam) ≤ BF P F Qn θ₀`

⚠ **ORIENTATION.** This is the paper's own direction ("the Frobenius norm is
√-additive"): the TRUNCATED side is bounded ABOVE by the FULL side plus `B_F`. The reverse
reading is FALSE — see PART B.8's header and `ZetaQ/Certificate.lean`'s `pair_perturbation` for the
machine-checked failing instance. The direction is forced by the proof, since the Frobenius
triangle inequality (`Zeta23.Assembly.frobSq_sub_le`) bounds `‖Ĝ − Ê‖_F` above.

The statement is `EFChi.frobSqAhatFam`/`EFChi.frobSqGzFam` with their bodies written out, so
it closes `EFChi.certificate_display_fam_of_bridge`'s and `EFChi.prop31_fam`'s `hpairF` slot
by `exact`; machine-checked.

Proof: per member `‖Â_χ‖_F ≤ ‖Ĝ_χ‖_F + B ≤ ‖Ĝ_χ‖_F + θ₀/(aL)` from `Â = Ĝ − Ê`, the
Frobenius triangle inequality and the `hat` clause of `Zeta23.Assembly.TailInputsD`; then the
ℓ² aggregation `sqrt_sum_sq_le_sqrt_add_sqrt_card_mul` over the flattened family index, whose
`√|S|` is exactly `B_F`'s `√|𝔉_Q|`. **This is the whole point of §7.3**: the Frobenius side
pays `√|𝔉|` and not `|𝔉|`, so `B_F ≍ Q·θ₀/(aL)` and no negative power of `Q` is demanded of
`θ₀`.

Paper §7.3. Derivation: `LEMMA_QT` §QT.c.
Depends on: `Zeta23.Assembly.TailInputsD`, `Zeta23.Assembly.frobSq_sub_le`,
`sq_sum_le_card_mul_sum_sq` [Mathlib], `ParamsQ.toParams_L`, `ZetaQ.BF`.
Rule 17: `P.D0` is a FIELD, blocks are `AzD`/`EzD` at it; `hl` is the `toParams_L` side
condition; `hB0` is normalisation positivity (the fixed-`(Q,T)` form of the hypothesis
`ZetaQ/EFChi.lean` already carries). No λ, no X. CLEAN. -/
theorem sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF
    (P : ParamsQ) (F : Family) (Qn : ℕ) (θ₀ : ℝ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hl : Zeta23.l P.T ≠ 0) (hB0 : 0 ≤ θ₀ / (P.aQ * P.LB))
    (hblock : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      Zeta23.Assembly.TailInputsD (Zc q χ) P.toParams P.T P.D0 θ₀) :
    Real.sqrt (familySum F Qn (fun q χ =>
          RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))))
        - Real.sqrt (familySum F Qn (fun q χ =>
          RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).Gz P.toParams P.T))))
      ≤ BF P F Qn θ₀ := by
  classical
  have haL : P.toParams.a P.T * P.toParams.L P.T = P.aQ * P.LB := by
    rw [P.toParams_L hl]; rfl
  set A : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun x =>
    Real.sqrt (RHLinalg.frobSq (P.toParams.hat P.T ((Zc x.1 x.2).AzD P.toParams P.T P.D0)))
    with hAdef
  set G : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun x =>
    Real.sqrt (RHLinalg.frobSq (P.toParams.hat P.T ((Zc x.1 x.2).Gz P.toParams P.T)))
    with hGdef
  have hAsq : ∀ x, A x ^ 2
      = RHLinalg.frobSq (P.toParams.hat P.T ((Zc x.1 x.2).AzD P.toParams P.T P.D0)) :=
    fun x => Real.sq_sqrt (Zeta23.Assembly.frobSq_nonneg _)
  have hGsq : ∀ x, G x ^ 2
      = RHLinalg.frobSq (P.toParams.hat P.T ((Zc x.1 x.2).Gz P.toParams P.T)) :=
    fun x => Real.sq_sqrt (Zeta23.Assembly.frobSq_nonneg _)
  have hpt : ∀ x ∈ famIdx F Qn, A x ≤ G x + θ₀ / (P.aQ * P.LB) := by
    intro x hx
    obtain ⟨q, χ⟩ := x
    simp only [famIdx, Finset.mem_sigma] at hx
    obtain ⟨B, hB0a, hBtr, hBfr, hBθ⟩ := (hblock q hx.1 χ (F.chars_subset q hx.2)).hat
    have hAeq : (Zc q χ).AzD P.toParams P.T P.D0
        = (Zc q χ).Gz P.toParams P.T - (Zc q χ).EzD P.toParams P.T P.D0 := by
      unfold Zeta23.ZeroConfig.EzD; abel
    have hsqE : Real.sqrt (RHLinalg.frobSq
        (P.toParams.hat P.T ((Zc q χ).EzD P.toParams P.T P.D0))) ≤ θ₀ / (P.aQ * P.LB) := by
      refine (Real.sqrt_le_iff.mpr ⟨hB0a, hBfr⟩).trans ?_
      refine hBθ.trans ?_
      rw [haL]
    have hfr : RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))
        ≤ (Real.sqrt (RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).Gz P.toParams P.T)))
            + Real.sqrt (RHLinalg.frobSq
              (P.toParams.hat P.T ((Zc q χ).EzD P.toParams P.T P.D0)))) ^ 2 := by
      rw [hAeq, hat_sub]
      exact Zeta23.Assembly.frobSq_sub_le _ _
    have hle := Real.sqrt_le_sqrt hfr
    rw [Real.sqrt_sq (by positivity)] at hle
    show Real.sqrt (RHLinalg.frobSq
        (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))) ≤ _
    linarith [hle, hsqE]
  have hkey := sqrt_sum_sq_le_sqrt_add_sqrt_card_mul (famIdx F Qn) A G hB0
    (fun x _ => Real.sqrt_nonneg _) (fun x _ => Real.sqrt_nonneg _) hpt
  rw [familySum_eq_sum_famIdx, familySum_eq_sum_famIdx]
  have e1 : ∑ x ∈ famIdx F Qn,
      RHLinalg.frobSq (P.toParams.hat P.T ((Zc x.1 x.2).AzD P.toParams P.T P.D0))
      = ∑ x ∈ famIdx F Qn, A x ^ 2 :=
    Finset.sum_congr rfl fun x _ => (hAsq x).symm
  have e2 : ∑ x ∈ famIdx F Qn,
      RHLinalg.frobSq (P.toParams.hat P.T ((Zc x.1 x.2).Gz P.toParams P.T))
      = ∑ x ∈ famIdx F Qn, G x ^ 2 :=
    Finset.sum_congr rfl fun x _ => (hGsq x).symm
  rw [e1, e2]
  have hBF : BF P F Qn θ₀ = Real.sqrt ((famIdx F Qn).card : ℝ) * (θ₀ / (P.aQ * P.LB)) := by
    rw [card_famIdx]; unfold BF; rw [mul_div_assoc]
  rw [hBF]
  linarith [hkey]

end ZetaQ
