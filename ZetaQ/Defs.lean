/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Defs.lean — the frozen shared layer: paper §2.2's notation.

Every other file in the library imports this one and adds nothing to it: the definitions and
the standing-assumption class below are fixed here once, so that the rest of the tree cannot
drift apart on notation.

Statement source of truth: paper §2.2.

RULE 17 lives here. The three forbidden hypotheses are λ ≤ 1, X ≤ T, and D₀ = √T. None of
them appears in this file, and each absence is deliberate:
  * `ParamsQ.lam` is free in (0,2) — the paper runs λ* = 1.2507321515 > 1;
  * `ParamsQ.D0` is a FIELD — [R]'s `Zeta23.D0 T = √T` (`Defs.lean:61`) is never used;
  * no hypothesis anywhere relates `XQ` to `T`. In this paper X = (QT/2π)^λ ≫ T always.

**THE DESIGN TAPER CARRIES A PROFILE** (the module header of `ZetaQ/Budget.lean` records why: a
flat taper cannot reach the constant §11 minimises `B` at). The design window is
the PROFILE-WEIGHTED `φ(u) = p(u/ℒ)·ϱ₂((L/2 − |u|)/w)`, realised with [R]'s `atD`
idiom (`Zeta23/ThmD/ParamsD.lean`): `ParamsQ` gained the even polynomial profile field `prof`,
`toParams` carries the REALISING profile `x ↦ p((L/2 − w·x)/ℒ)·ϱ(x)`, and every derived object
(`phiQ`, `PhiQ`, `gQ`, `aQ`, `phiHatQ`, …) keeps its definition through `toParams`, so the
generic call sites are untouched. `Valid.taper` still says the RAMP `ϱ` is a `TaperProfile`;
the new `Valid.profile` is the profile class (`ProfileQ`), and `Valid.a_ge`, `Valid.b_ge` are
the two window-moment floors that [R]'s generic-window route (`AdmWindow.localHypsCore`) takes
as inputs. `Valid.toParamsValidQ` is GONE: the realising profile is not a `TaperProfile`, and
every former consumer now goes through `ZetaQ/Window.lean`'s `AdmWindow` instance.
-/
import Zeta23

noncomputable section

open scoped BigOperators
open Finset

namespace ZetaQ

/-! ## 1. The parameter record

Paper §2.2. `Q` and `T` are FIELDS rather than separate arguments (contrast [R], where `T`
is threaded explicitly): every lemma of this paper is a statement at one design point
`(Q, T, λ, w, D₀)`, and the asymptotics of Theorem 1 are expressed by quantifying over a
family of design points. Keeping the design point finite is what makes each hypothesis
individually Rule-17 auditable. -/

/-- The paper's parameter bundle at one design point (§2.2). `ϱ` is the Gevrey-2 RAMP
profile ϱ₂ of [R] (H4, derivative constants `(A, B) = (36/e, 2e⁸)`); `prof` is the even
POLYNOMIAL profile factor `p` of §11 in the scale-free variable `t = u/ℒ` (the design
window is `p(u/ℒ)·ϱ₂((L/2 − |u|)/w)`; the flat taper is `prof = 1`); `lam` is the bandwidth
λ; `w` the ramp width; `D0` **the free buffer** — a field, never `Real.sqrt T`. -/
structure ParamsQ where
  /-- the conductor bound: the family is the primitive χ of modulus q ≤ Q. -/
  Q : ℝ
  /-- the window height: `I = [T, 2T]`, `T = (log Q)^{r+ε}`. -/
  T : ℝ
  /-- bandwidth λ ∈ (0,2). Free above 1: the design of record is λ* = 1.2507321515. -/
  lam : ℝ
  /-- ramp width w; the design sets `w = max(1, w*)` (§10.3). -/
  w : ℝ
  /-- the buffer D₀. A FREE field — this is the whole point of the ParamsQ layer. -/
  D0 : ℝ
  /-- the ramp profile (the ϱ₂ of [R]). -/
  ϱ : ℝ → ℝ
  /-- The even polynomial profile factor `p` (§11's `v = p²`), in the variable
  `t = u/ℒ`. The flat taper of [R] is `prof = 1`. -/
  prof : Polynomial ℝ

namespace ParamsQ

variable (P : ParamsQ)

/-! ## 2. Scales

**The scale is the q-aspect one and it is NOT [R]'s.** [R] has
`Zeta23.l T = log(T/2π)` (`Defs.lean:49`); the paper has `ℒ = log(QT/2π)`. Silently
reusing `Zeta23.l` would reimpose `X ≤ T ⟺ λ ≤ 1`, which Rule 17 forbids. -/

/-- `ℒ := log(QT/2π)`  (§2.2). The common scale of the whole paper. -/
def LL : ℝ := Real.log (P.Q * P.T / (2 * Real.pi))

/-- `L := λℒ`  (§2.2). -/
def LB : ℝ := P.lam * P.LL

/-- `X := e^L = (QT/2π)^λ`  (§2.2). At λ* > 1 this is ≫ T; no hypothesis may say otherwise. -/
def XQ : ℝ := Real.exp P.LB

/-- `h := 2π/L`  (§2.2). -/
def hgridQ : ℝ := 2 * Real.pi / P.LB

/-- `d := ⌊LT/2π⌋`  (§2.2). -/
def dQ : ℕ := ⌊P.LB * P.T / (2 * Real.pi)⌋₊

/-- `τ_k := T + kh`  (§2.2). -/
def tauQ (k : ℤ) : ℝ := P.T + k * P.hgridQ

/-- `δ′ := 3 log log Q / log Q`  (§2.2, the zone edge; K = 3 is the design's conservative
choice, K ≥ 2 being what §5 proves). -/
def deltaPrime : ℝ := 3 * Real.log (Real.log P.Q) / Real.log P.Q

/-- `s₀ := (1 − δ′)·log Q` — the in-zone breakpoint. Paper §4: "The in-zone breakpoint is
`|s| ≤ (1 − δ′)·log Q`, **not** `(1 − δ′)ℒ` (the difference is budget row L₁)." -/
def s0 : ℝ := (1 - P.deltaPrime) * Real.log P.Q

/-- `Y := e^{s₀} = Q^{1−δ′}` — the zone cutoff of §5's low–low zone. -/
def zoneY : ℝ := Real.exp P.s0

/-! ## 3. The bridge to [R]'s `Params`

[R]'s taper machinery (`Taper/`, the Gevrey ramp lemma, `Tail/GevreyTail.lean`) is stated
for `Zeta23.Params` and is scale-generic: every derived object is built from `Params.L`.
So instead of re-deriving φ, Φ, g, a at our scale we INSTANTIATE [R]'s record at the
bandwidth that makes its `L` equal ours:

    toParams.lam := L / l T = λℒ / log(T/2π)

Then `Params.L toParams P.T = λℒ = LB P`, and `phi`, `Phi`, `g`, `a`, `X`, `hgrid`, `d`,
`tau` at argument `P.T` all coincide with paper §2.2 term for term.

**The REALISING profile.** `toParams.ϱ` is NOT `P.ϱ` but `x ↦ p((L/2 − w·x)/ℒ)·ϱ(x)`,
exactly [R]'s `Params.atD` idiom (`Zeta23/ThmD/ParamsD.lean:39`, where the Montgomery–Taylor
window `φ_D` is realised as `⟨x ↦ φ_D(L/2 − w·x), λ, w⟩`). Since `Params.phi` only ever
evaluates the profile at `x = (L/2 − |u|)/w`, one gets `toParams.phi T u = p(|u|/ℒ)·ϱ((L/2 −
|u|)/w)` (`phiQ_eq_prof_mul`), i.e. the profile-weighted window of §11 with the Gevrey ramp of
§2.2 — and every derived object below keeps its definition. The values of the realising
profile at `x > L/(2w)` are never consulted; in particular `toParams.crho` (which would see
them) is NOT a meaningful constant any more, and the window constant is `cWin` below.

Rule-17 note: `toParams.lam` is ≈ 18 at Q = 10¹⁰⁰ and ≈ 116 at 10¹⁰⁰⁰ — it is emphatically
NOT λ*, and no `lam ≤ 1` is derivable from it. The bridge is the reason the reuse is
legitimate; it is also the reason nobody may "simplify" `toParams.lam` to `P.lam`. -/

/-- [R]'s parameter record instantiated so that its `L` is the paper's `L = λℒ`, with the
REALISING profile `x ↦ p((L/2 − w·x)/ℒ)·ϱ(x)` ([R]'s `atD` idiom). -/
def toParams : Zeta23.Params where
  ϱ := fun x => P.prof.eval ((P.LB / 2 - P.w * x) / P.LL) * P.ϱ x
  lam := P.LB / Zeta23.l P.T
  w := P.w

/-- The bridge equation: [R]'s `L` at `toParams` IS the paper's `L`, provided `l T ≠ 0`
(i.e. `T ≠ 2π`, free in the regime `T ≥ 300`). -/
theorem toParams_L (h : Zeta23.l P.T ≠ 0) : P.toParams.L P.T = P.LB := by
  simp only [Zeta23.Params.L, toParams]
  field_simp

/-- Consequently [R]'s `X` at `toParams` is the paper's `X = (QT/2π)^λ`. -/
theorem toParams_X (h : Zeta23.l P.T ≠ 0) : P.toParams.X P.T = P.XQ := by
  simp only [Zeta23.Params.X, XQ, toParams_L P h]

/-! ## 4. Taper, kernels, windows (§2.2), via the bridge -/

/-- `φ(u) := p(u/ℒ)·ϱ₂((L/2 − |u|)/w)`  (§2.2 ramp × §11 profile; F58).

Until the repair this was [R]'s FLAT taper `ϱ((L/2 − |u|)/w)` (paper
§2.2 verbatim), for which `B(v_flat) = 1.4086 ≠ κ_C = 1.2787` at `λ*` — the headline constant
is §11's optimum over profiles `v = φ²`, which the flat window does not attain. [R] realises
such a profile with `ThmD.phiD = √(v*(u/L))·φ_flat` (`Zeta23/ThmD/Window.lean:38`, packaged
as `Params.atD`); the notes' intended design is the profile-weighted window (E6 §2 D2, NOTE_QG
§g.5). The repair keeps THIS definition verbatim and changes `toParams`'s profile, so that
`phiQ u = P.prof.eval (|u|/ℒ) · ϱ((L/2 − |u|)/w)` (`phiQ_eq_prof_mul`) with `prof` an even
polynomial. Record: "the design window must carry a profile", in the module header of
`ZetaQ/Budget.lean`. -/
def phiQ (u : ℝ) : ℝ := P.toParams.phi P.T u

/-- `Φ := h_{φ²}` on the real line  (§2.2). -/
def PhiQ (r : ℝ) : ℝ := P.toParams.PhiR P.T r

/-- `g := φ²⋆φ² ≥ 0`  (§2.2); nonnegativity is H3 (`Zeta23.AdmWindow.gv_nonneg`). -/
def gQ (y : ℝ) : ℝ := P.toParams.g P.T y

/-- `a := L⁻¹∫φ²`  (§3, the hat normalisation `Ĝ := G/(aL²)`). -/
def aQ : ℝ := P.toParams.a P.T

/-- `b := L⁻¹∫φ⁴`  (§2.2, [eq:abdef]; F58: the second window moment, `≥ 1/2` is the
generic-window positivity input of [R]'s `AdmWindow.localHypsCore`). -/
def bQ : ℝ := P.toParams.b P.T

/-- `I := [T, 2T]`  (§2.2). -/
def IwinQ : Set ℝ := Zeta23.Iwin P.T

/-- `I′ := (T − D₀, 2T + D₀]`  (§2.2), at the FREE buffer — Phase 1's `IprimeD`, never
[R]'s `Iprime` (whose body substitutes `D0 T = √T`). -/
def IprimeQ : Set ℝ := Zeta23.IprimeD P.T P.D0

/-- `D_T(v) := ∫_I e^{iτv} dτ`  (§2.2). -/
def DT (v : ℝ) : ℂ := ∫ τ in P.T..(2 * P.T), Complex.exp (Complex.I * v * τ)

/-- **The window is the product of the profile and the ramp taper** — the `ParamsQ`
mirror of `Zeta23.Params.atD_phi` (`Zeta23/ThmD/ParamsD.lean:55`):
`φ(u) = p(|u|/ℒ)·φ_flat(u)`, `φ_flat = Zeta23.Taper.phi ϱ L w`. Needs only `l T ≠ 0` (the
scale identity) and `w ≠ 0`. -/
theorem phiQ_eq_prof_mul (h : Zeta23.l P.T ≠ 0) (hw : P.w ≠ 0) (u : ℝ) :
    P.phiQ u = P.prof.eval (|u| / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u := by
  show P.prof.eval ((P.LB / 2 - P.w * ((P.toParams.L P.T / 2 - |u|) / P.w)) / P.LL)
      * P.ϱ ((P.toParams.L P.T / 2 - |u|) / P.w)
    = P.prof.eval (|u| / P.LL) * P.ϱ ((P.LB / 2 - |u|) / P.w)
  rw [toParams_L P h]
  have e : P.LB / 2 - P.w * ((P.LB / 2 - |u|) / P.w) = |u| := by
    field_simp
    ring
  rw [e]

/-! ## 4a. The profile class and the window constants

The profile factor `p = P.prof` is an even polynomial, `1/6 ≤ p ≤ 1` on the core
`[−λ/2, λ/2]` and nonincreasing on `[0, λ/2]`. These four facts are exactly what the
generic admissible-window instance (`ZetaQ/Window.lean`, built on [R]'s
`XiPrime.admWindow_phiM`) consumes, plus the derivative bounds below, which for a polynomial
are EXPLICIT coefficient sums and need no hypothesis. The bulk floor `1/6` replaces the flat
plateau's `φ = 1` in every lower-envelope lemma of §4 (`g ≥ (L − 2w − |y|)₊` becomes
`g ≥ (1/6)⁴·(L − 2w − |y|)₊`); the design profiles have `p(λ/2) ≈ 0.18` (q ≤ Q) and `≈ 0.21`
(dyadic) — see `ZetaQ/Payoff.lean` `designProfile`. -/

/-- **The profile class**. `even`, the bulk floor `1/6 ≤ p` and `p ≤ 1` on the core,
and `p` nonincreasing on `[0, λ/2]`. Rule 17: constrains only the free field `prof` and the
core `[−λ/2, λ/2]`; caps no λ, names no `X`, `T`, `D₀`. -/
structure ProfileQ (pp : Polynomial ℝ) (lam : ℝ) : Prop where
  /-- `p(−t) = p(t)`. -/
  even : ∀ t : ℝ, pp.eval (-t) = pp.eval t
  /-- the bulk floor: `1/6 ≤ p` on the core. -/
  bulk : ∀ t : ℝ, |t| ≤ lam / 2 → 1 / 6 ≤ pp.eval t
  /-- `p ≤ 1` on the core. -/
  le_one : ∀ t : ℝ, |t| ≤ lam / 2 → pp.eval t ≤ 1
  /-- `p` is nonincreasing on `[0, λ/2]`. -/
  antitone : AntitoneOn (fun t : ℝ => pp.eval t) (Set.Icc 0 (lam / 2))

/-- explicit coefficient-sum bound for `|pp^{(j)}|` on `[−R, R]`:
`Mpoly pp R j := Σ_i |coeff_i(pp^{(j)})|·R^i` (proved in `ZetaQ/Window.lean`,
`abs_eval_le_Mpoly`). -/
def Mpoly (pp : Polynomial ℝ) (R : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((Polynomial.derivative^[j] pp).natDegree + 1),
    |(Polynomial.derivative^[j] pp).coeff i| * R ^ i

/-- `M_j := Mpoly p (λ/2) j` — the derivative bounds of the profile on its core. -/
def profM (j : ℕ) : ℝ := Mpoly P.prof (P.lam / 2) j

/-- **The admissible-window constant of the design window**:
`c_W := c_ϱ + M₁λ + (M₁λ)² + M₂λ²` — [R]'s `XiPrime.cMod ϱ A B = cRho ϱ + A + A² + B` at
`A = M₁λ`, `B = M₂λ²` (`|q′| ≤ A/L`, `|q″| ≤ B/L²` for `q(u) = p(u/ℒ)`, `λ = L/ℒ`). Replaces
`P.toParams.crho`, which is meaningless for the realising profile (it sees `p` beyond the core,
where the polynomial is unbounded). `4 ≤ c_W` (`Window.four_le_cWin`). -/
def cWin : ℝ :=
  Zeta23.Taper.cRho P.ϱ + P.profM 1 * P.lam + (P.profM 1 * P.lam) ^ 2 + P.profM 2 * P.lam ^ 2

/-- **The Gevrey constant of the product window** (`Zeta23/Taper/GevreyProduct.lean`
`gevrey_polyQ_mul_phi`, report `audit/ProductWindow_REPORT.md`): if the ramp is `GevreyProfile 2 A B`, then
`‖φ^{(k)}‖₁ ≤ 2·B′·w·(A/w)^k·k^{2k}` with
`B′ = B·Σ_{j≤deg p} M_j (w/(ℒA))^j + ½·Σ_{j≤deg p} M_j (λ/A)^j`. At the flat profile
`p = 1` this is `B + 1/2` (`M₀ = 1`, `M_j = 0` for `j ≥ 1`). -/
def gevreyBprod (A B : ℝ) : ℝ :=
  B * (∑ j ∈ Finset.range (P.prof.natDegree + 1), P.profM j * (P.w / (P.LL * A)) ^ j)
    + (∑ j ∈ Finset.range (P.prof.natDegree + 1), P.profM j * (P.lam / A) ^ j) / 2

/-! ## 5. Validity

Mirrors `Zeta23.Params.ValidQ` (`Defs.lean:204`) and adds the buffer regime. The side
conditions that are consumed only locally (`8w ≤ L`, `wD₀ ≫ e²A`, the Gevrey closing
condition) are deliberately NOT bundled here: bundling them would hide them from the
call sites the Rule-17 audit has to inspect.

Three fields were added: `profile` (the profile class), and the two window-moment
floors `a_ge : 3/4 ≤ a`, `b_ge : 1/2 ≤ b`. For the flat taper both floors were THEOREMS
(`Zeta23.Params.three_quarters_le_b`, `b_le_a`); for a profile-weighted window they are
properties of the design point (they need `L ≫ w`: at `8w = L` the design profile has
`a ≈ 0.69`), exactly as [R]'s `AdmWindow.localHypsCore` takes `b ≥ 1/2` as an input ("it is a
property of the particular window"). They are used ONLY for positivity/normalisation
(`a > 0`, `9/16 ≤ a²`, `1/2 ≤ b`), never quantitatively beyond that, and the design of record
satisfies them with room (`a ≈ 0.783`, `b ≈ 0.684` for q ≤ Q at `w = 1`, `ℒ ≥ 100`). -/

/-- Standing assumptions at a design point. Note what is absent: no `lam_le_one`, no
`X ≤ T`, no `D0 = Real.sqrt T`. -/
structure Valid (P : ParamsQ) : Prop where
  /-- The RAMP profile is [R]'s `TaperProfile` (H4). (this is about `ϱ`, the ramp, and
  is still true; the realising profile `toParams.ϱ` is NOT a `TaperProfile`.) -/
  taper : Zeta23.TaperProfile P.ϱ
  /-- The profile factor is in the profile class (even polynomial, `1/6 ≤ p ≤ 1` on the
  core, nonincreasing on `[0, λ/2]`). -/
  profile : ProfileQ P.prof P.lam
  /-- 0 < λ. -/
  lam_pos : 0 < P.lam
  /-- λ < 2 — §2.2's standing convention, and the sieve's own range. NOT λ ≤ 1. -/
  lam_lt_two : P.lam < 2
  /-- 1 ≤ w — KEPT deliberately: it is a genuine hypothesis of the reused cap-free ends
  lemmas, and it costs `6/(λℒ)` in the budget rather than being free. The design satisfies it
  by the clamp
  `w = max(1, w*)` (§10.3). -/
  one_le_w : 1 ≤ P.w
  /-- the buffer regime required by the free-buffer counting layer. Phase 1's
  `Zeta23.Tail.NIID_le` needs `2 ≤ D` AND `D + 4 ≤ T` (strictly stronger than the tail
  chain's `1 ≤ D`); [R]'s version got both free from `√T ≥ 17`, ours must state them.
  -/
  two_le_D0 : 2 ≤ P.D0
  /-- the buffer must fit inside the window. -/
  D0_le : P.D0 + 4 ≤ P.T
  /-- the window regime. -/
  T_ge : Zeta23.Tail.T₀ ≤ P.T
  /-- `Q ≥ 3` so that `log log Q > 0` and `δ′` is well defined. -/
  Q_ge : 3 ≤ P.Q
  /-- The hat-normalisation floor `3/4 ≤ a = L⁻¹∫φ²` (was `three_quarters_le_b ∘
  b_le_a` for the flat taper). Used for `a > 0` and `9/16 ≤ a²` only. -/
  a_ge : 3 / 4 ≤ P.aQ
  /-- The second-moment floor `1/2 ≤ b = L⁻¹∫φ⁴` — the generic-window positivity input
  of [R]'s `AdmWindow.localHypsCore` (`LocalHypsCore.b_ge_half`). -/
  b_ge : 1 / 2 ≤ P.bQ

/-! `Valid.toParamsValidQ` (the old bridge `P.Valid → P.toParams.ValidQ`) is GONE:
`toParams.ϱ` is the realising profile `x ↦ p((L/2 − w·x)/ℒ)·ϱ(x)`, which is not a
`TaperProfile`, so `P.toParams.ValidQ` is FALSE at every design point with `prof ≠ 1`. Every
former consumer now goes through `ZetaQ/Window.lean` (`Valid.admWindow`, the `AdmWindow`
instance of the product window, with constant `cWin`), which is what [R]'s own Theorem D
route does for its profile-weighted window. -/

end ParamsQ

/-! ## 6. The family (§1.1, §2.2, §12)

[R] is per-character throughout — `grep` over all 328 files finds no family character sum —
so everything here is new. -/

open DirichletCharacter in
/-- `Σ*_{χ mod q}` — the primitive Dirichlet characters mod `q`. Mathlib has no notion of
"the Finset of primitive characters"; `IsPrimitive` is not decidable (`conductor` is an
`sInf`), hence the classical instance. -/
def primitiveChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  Finset.univ.filter (fun χ => χ.IsPrimitive)

/-- `φ*(q)` — the number of primitive characters mod `q`. -/
def phiStar (q : ℕ) : ℕ := (primitiveChars q).card

/-- `|𝔉_Q|` — the family size, `= (18/π⁴)Q²(1 + o(1))` (§2.2, proved in §12.2). -/
def famCard (Q : ℕ) : ℕ := ∑ q ∈ Finset.Icc 1 Q, phiStar q

/-- The dyadic family of Corollary 2, `q ∈ (Q/2, Q]`. -/
def famCardDyadic (Q : ℕ) : ℕ := ∑ q ∈ Finset.Ioc (Q / 2) Q, phiStar q

/-- `κ(χ) ∈ {0,1}` — the PARITY of §2.2. Deliberately not named `κ`: paper §3 warns that
`κ_C`, the Frobenius main-term constant, is a different object. -/
def parity {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ :=
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.Even)
  if χ.Even then 0 else 1

/-- `μ_q(τ) := (1/2π)[log(q/π) + Re ψ(¼ + κ/2 + iτ/2)]` (§2.2) — [R]'s, reused verbatim. -/
def muDensity (q : ℕ) {r : ℕ} (χ : DirichletCharacter ℂ r) (τ : ℝ) : ℝ :=
  Zeta23.ThmE.muq (parity χ) q τ

/-- `ν_{X,χ} := μ_q + P_{X,χ}`, **no pole term** (§2.2; the no-pole fact is H2) — [R]'s
`nuXc`, reused verbatim at the coefficient sequence `n ↦ χ(n)`. -/
def nuQ (P : ParamsQ) (q : ℕ) (χ : DirichletCharacter ℂ q) (τ : ℝ) : ℝ :=
  Zeta23.ThmE.nuXc (parity χ) q (fun n => χ (n : ZMod q)) P.XQ τ

/-! ## 7. Constants, as `def`s with provenance -/

/-- `C := Q²/|𝔉_Q| → π⁴/18` — the family constant of the q ≤ Q family (§2.2). -/
def Cfam : ℝ := Real.pi ^ 4 / 18

/-- `C_dyad = 2π⁴/27` (Corollary 2). -/
def CfamDyadic : ℝ := 2 * Real.pi ^ 4 / 27

/-- `C_even,dyad = 4π⁴/27` (Corollary 3, out-zone `C → 2C`). -/
def CfamEvenDyadic : ℝ := 4 * Real.pi ^ 4 / 27

/-- `C_even = π⁴/9` over q ≤ Q (Corollary 3). -/
def CfamEven : ℝ := Real.pi ^ 4 / 9

/-- `P = 0.7212835668…` — Theorem 1's constant, the value of §10–11's variational problem
at `C = π⁴/18`. Shipped by `ZetaQ/Payoff.lean` as a FEASIBILITY certificate at this digit
count, not as an equality. -/
def Pconst : ℝ := 0.7212835668

/-- `P_dyad = 0.7099167448…` (Corollary 2). -/
def PconstDyadic : ℝ := 0.7099167448

/-- `P_even,dyad = P_odd,dyad = 0.6919434301…` (Corollary 3). -/
def PconstEvenDyadic : ℝ := 0.6919434301

/-- `λ* = 1.2507321515` at `C = π⁴/18` (§11). **Greater than 1** — the fact the whole
ParamsQ layer exists to permit. -/
def lamStar : ℝ := 1.2507321515

/-- `λ*_dyad = 1.1931581210` (§11). -/
def lamStarDyadic : ℝ := 1.1931581210

/-- `(A, B) = (36/e, 2e⁸)` — [R]'s Gevrey-2 derivative constants (H4, §2.2). -/
def gevreyA : ℝ := 36 / Real.exp 1

/-- see `gevreyA`. -/
def gevreyB : ℝ := 2 * Real.exp 8

/-- `c₁ = 0.41` — the explicit absolute constant of Lemma 8.1 (§8). -/
def c1Ends : ℝ := 0.41

/-- `C₀ = 6` — the explicit absolute constant of Lemma 8.1 (§8). -/
def C0Ends : ℝ := 6

end ZetaQ
