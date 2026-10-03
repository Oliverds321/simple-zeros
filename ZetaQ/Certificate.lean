/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Certificate.lean — paper §3: the grid Gram, the hat units, the family aggregates,
the displayed certificate (H1) and **Proposition 3.1**.

Imports `ZetaQ.Defs` and nothing else. Consumed by `ZetaQ/Budget.lean` (§10) and re-exported by
the library root `ZetaQ.lean`.

Statement source of truth: paper §3 and §7.3.

**This file is sorry-free.** `kappaC_value`, `kappaCDyadic_value`,
`NIIfree_eq`, **`prop_3_1_pair_moment_certificate`** (Proposition 3.1, the file's
centrepiece), **`pair_perturbation`** (§7.3), **`certificate_display_of_H1`** and
**`h1_block_fixed_free`** (now `@[deprecated h1_block_free]`) are all proved.

**THE FREE-BUFFER RANK–TRACE / INERTIA BOUND IS PROVED (§3.8).** The bound **`hatAzD_mult2`** is proved — it is [R]'s own `ZeroBlockData.mult_two` instantiated at
`𝒵(I′(D))` rather than `𝒵(I′(√T))` — and **`h1_block_free`** is the per-block H1 display at
fixed `(Q,T)` and free `D` with NO rank–trace hypothesis. Nothing had to be added to `Zeta23/`
for it. See the §3.8 block below, and the 🚩 finding recorded there and at
`h1_block_free`: the frozen hypothesis `hrt` of `h1_block_fixed_free` is itself a
mis-transcription (it drops `−2 N(I′(D))` and doubles `s₁`), so it is strictly stronger than
anything §4 proves; the conclusion is unaffected.

Two of them were found FALSE as first transcribed, with machine-checked counterexamples, and
have been REPAIRED in place — the standing policy of this library is that a demonstrably false
statement is repaired, not preserved. In both,
the Frobenius hypothesis was oriented backwards against the paper's own §7.3 step
`‖Â‖_F ≤ ‖Ĝ‖_F + B_F`, and `pair_perturbation` additionally dropped `0 ≤ frobSqG`. The
paper is NOT wrong here; only our transcription was. The counterexamples are retained in the
docstrings as the record. `pair_perturbation'` / `certificate_display_of_H1'` survive as
deprecated aliases so nothing that already cites them breaks.

--------------------------------------------------------------------------------------
## RULE 17 — the loud flag for this file

The three forbidden hypotheses are **λ ≤ 1**, **X ≤ T**, **D₀ = √T**. This file's specific
exposure is the third, and it is *the* interface decision of §3:

  * **`Zeta23.Assembly.count_certificate` (`Zeta23/Assembly/Certificate.lean:39`) SMUGGLES
    D₀ = √T.** Its hypotheses `h0` and `hNII_o` both mention `(NII Z T : ℝ)`, and
    `Zeta23.Assembly.NII` (`Zeta23/Assembly/Inputs.lean:33`) is *definitionally*
    `Z.N (T − D0 T) T + Z.N (2T) (2T + D0 T)` with `Zeta23.D0 T = Real.sqrt T`
    (`Zeta23/Defs.lean:61`). **Phase 2 must NOT cite `count_certificate`.**
  * **Phase 2 consumes `Zeta23.Assembly.count_certificate_free`
    (`Zeta23/WindowD.lean:183`)** instead, which abstracts the buffer count into a free
    parameter `NIIf : ℝ → ℝ`; `D0` does not occur in its statement, which is exactly what it
    was added to `Zeta23/WindowD.lean` for.
  * Every buffer object below is at the FREE field `ParamsQ.D0` (`NIIFam`, `NIIFamQ`,
    `h1_block_fixed_free`), mirroring `Zeta23.Assembly.NIID` (`WindowD.lean:100`) and
    never `Zeta23.Assembly.NII`.
  * Also forbidden here: `Zeta23.Params.Valid` (`Zeta23/Defs.lean:193`) carries
    `lam_le_one`. Use `ZetaQ.ParamsQ.Valid` / `Zeta23.Params.ValidQ` only.
  * The scale is the q-aspect one throughout: `P.LL = log(QT/2π)`, `P.LB = λℒ`,
    `P.XQ = (QT/2π)^λ` from the frozen `ZetaQ/Defs.lean`. `Zeta23.Params.L`/`X`/`d` at
    argument `P.T` are the T-aspect scale and are reached ONLY through the bridge
    `ParamsQ.toParams`, whose `toParams_L` makes them coincide with the
    paper's. Never `Zeta23.l P.T` in the *scale* slot.

--------------------------------------------------------------------------------------
## OPEN QUESTION Q2 — RECORDED, NOT RESOLVED

`count_certificate_free` ends in the **ε-filter form** `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, …`, and its
hypotheses are `∀ᶠ T in atTop`. Paper §10.5 is explicit that **no ε-limit is taken**: the
rate is carried by the budget rows, so `ZetaQ`'s Proposition 3.1 mirrors the *fixed-(Q,T)*
`Zeta23.Assembly.N0star_lower_moment` (`Assembly/Certificate.lean:24–31`), not
`count_certificate`'s filter shape.

That leaves a **residual gap**: the per-block H1 *display* at a fixed `(Q, T)` and at the
free buffer `D₀`. Phase 1 ships the window bookkeeping at free `D` (`s1D_le`,
`s1D_add_s2D_le`, `card_ZIprimeD_le`, `WindowD.lean:140–174`) but has **not** assembled it
into a fixed-`T` producer of `h0`; and the free-`D` *truncated* zero-side matrix does not
exist at all — `Zeta23.ZeroConfig.Az` (`Zeta23/Defs.lean:325`) is built on `ZIprime`, i.e.
at `D₀ = √T`. The obligation is stated below as `h1_block_fixed_free`, with the genuinely
missing ingredient isolated as its hypothesis `hrt`.

**RESOLUTION OF THE LEAN SIDE (this fill).** `h1_block_fixed_free` is now **PROVED**: given
`hrt`, the rest is exactly `Zeta23.Assembly.s1D_le` (free `D`) plus `N₀ˢ ≤ N` from
`ZeroConfig.trivial_chain`, and it is six lines. So the *window bookkeeping* half of Q2 is
NOT a gap: Phase 1 shipped everything needed for it.

**What IS the gap, stated precisely.** It is the discharge of `hrt` — the rank–trace /
inertia inequality `4 tr Â − ‖Â‖²_F ≤ 2 s₁(T, D)` on the truncated block **at a free `D`**.

CORRECTION, recorded because an earlier draft of this docstring got it wrong
and the wrong version is the more alarming one: **the free-buffer matrix DOES exist.** Phase
1 built `Zeta23.ZeroConfig.AzD` (`Zeta23/Tail/GevreyTail.lean:1423`), summing `Gsummand`
over `ZIprimeD T D` at a free `D`, with the `rfl` bridge `AzD_sqrtT : Z.AzD P T (D0 T) =
Z.Az P T` (`:1426`) and the tail split `EzD := Gz − AzD` (`:1429`). So the claim that "the
only truncated zero-side matrix in the tree is `ZeroConfig.Az`" is FALSE — that search
missed `GevreyTail.lean`, which is exactly where Phase 1 put the matrix layer.

The residual obligation is therefore narrower and is ordinary Phase-2 work, not a Phase-1
completeness gap: apply `RHLinalg`'s rank–trace/inertia bound to `AzD` at free `D` — i.e.
mirror [R]'s own zero-side rank argument over `ZIprimeD` in place of `ZIprime`. Nothing has
to be added to `Zeta23/`.

### ✅ Q2 IS NOW CLOSED (§3.8 below). No Phase-1 gap.

That mirror is built in §3.8 and the whole of Q2 is discharged:
  * **`hatAzD_mult2`** — the free-buffer rank–trace / inertia bound
    `4 tr Â(D) − ‖Â(D)‖²_F − 2 N(I′(D)) ≤ s₁(T,D)` on `Zeta23.ZeroConfig.AzD`, obtained by
    instantiating [R]'s abstract `Zeta23.ZeroSide.ZeroBlockData.mult_two`
    (`ZeroSide/Mult.lean:128`) at `𝒵(I′(D))` instead of `𝒵(I′(√T))`. Nothing was added to
    `Zeta23/`: the rank–trace engine is already index-type-generic, and only [R]'s
    *instantiation* layer (`ZeroSide.lean:573–950`) was `√T`-specific.
  * **`h1_block_free`** — `h1_block_fixed_free` with NO rank–trace hypothesis, at the free
    buffer. This is the object §10.5 should consume.

**🚩 And the frozen hypothesis `hrt` is itself a mis-transcription**, recorded in full at
`h1_block_free`: `hrt : 4 tr Â − ‖Â‖²_F ≤ 2 s₁` drops the `−2 N(I′(D))` term and doubles
`s₁`, which makes it *strictly stronger* than anything §4 proves (the true right-hand side
`s₁ + 2N(I′)` is never below `3s₁`, by `[eq:Ncount]`). It fails already at the sharpest
single-zero instance. `h1_block_fixed_free` is nevertheless TRUE and is left exactly as
frozen — the defect is that its hypothesis is unsatisfiable in general, not that its
conclusion is wrong, and the conclusion is what `h1_block_free` now proves outright.
**Decision D28: `h1_block_fixed_free` is therefore marked
`@[deprecated h1_block_free]`** (the attribute is attached just after `h1_block_free`, since
that is where the replacement comes into scope), with the unsatisfiability recorded in its
own docstring, so that no effort is spent trying to instantiate `hrt`.
It is NOT deleted; nothing cites it at term level, and the two `Depends on:` docstrings that
named it now name `h1_block_free`.

--------------------------------------------------------------------------------------
## 🚩 The family excludes `q = 1` (this pass, one line, decided)

`Family.moduli Family.qle Qn` was `Finset.Icc 1 Qn`; it is now **`Finset.Icc 2 Qn`**. The
trivial character mod 1 *is* primitive (`DirichletCharacter.isPrimitive_one_level_one`, so
`primitiveChars 1 = {1}`), so that member's `L`-function is `ζ`, with a pole at `s = 1` —
exactly what paper §2.2's no-pole hypothesis (H2, encoded in `ZetaQ.nuQ` by the *absence* of a
pole term) and [R]'s Theorem E (stated for `q > 1`) exclude. §2.2 and [R] already excluded it;
only §1.1's printed family definition omitted the bound. Cost: one character out of
`|𝔉_Q| ≍ (18/π⁴)Q²`, relative `O(Q^{-2})`. Full reasoning at `Family.moduli`, and the exact
companion change it forces in `Family.size` — which is written out over `Icc 2 Qn` rather than
citing the frozen `ZetaQ.famCard`, so that `sizeR` stays *exactly* `|𝔉_Q|` and
`ZetaQ/Tail.lean`'s `card_famIdx` stays an identity — at `Family.size`. Nothing else in this file
mentions the index set, and no proof here used `1 ∈ moduli`.

**What it unlocks elsewhere:** `ZetaQ/EFChi.lean` carries
`rtrace_hatQ_gridGram_eq_Gz`, `frobSq_hatQ_gridGram_eq_Gz`, `ZChi_N`, `ZChi_N0s` under a
`1 < q` hypothesis *precisely because* of the `q = 1` member; those hypotheses are now
discharged from `Finset.mem_Icc` on `Family.moduli Family.qle`, which is what
`ZetaQ.assembly_clauses_at_design`'s `hZc`/`hB` were blocked on.

--------------------------------------------------------------------------------------
## κ_C vs κ(χ) — the collision the paper flags explicitly

`ZetaQ.parity χ ∈ {0,1}` (frozen in `ZetaQ/Defs.lean`) is the **parity** of the character, an
argument of the digamma density μ_q. `ZetaQ.kappaC` below is the **Frobenius main-term
constant** of §§4–6 (= `min B` of §11's C-penalised variational problem, `P = 2 − κ_C`).
They are different objects and are kept textually distinct. [R]'s tree spells the *second*
one `κ` (`Assembly/Certificate.lean:39`) and has no parity object of that name, so `κ` in
[R] = our `κ_C`; recorded so the mirror does not silently invert the meaning.

--------------------------------------------------------------------------------------
## DEFINED HERE RATHER THAN IN `Defs.lean`, which is frozen

`ParamsQ.phiHatQ` (φ̂ at the paper's scale), `Family` + `Family.moduli/size/Cconst/payoff/
kappaC/lamStar`, `familySum`, `NcountQ`, `N0sQ`, `NfamCount`, `N0sFamCount`, `NIIFam`,
`gridGram`, `hatQ`, `trGhatFam`, `frobSqGhatFam`, `Btr`, `BF`, `kappaCof`.
-/
import ZetaQ.Defs
import ZetaQ.Window

noncomputable section

open scoped BigOperators

namespace ZetaQ

/-! ## 3.0 φ̂ at the paper's scale, via the bridge

Paper §2.2's `h_f(z) := ∫ f(u)e^{izu}du`; [R]'s `Zeta23.paperFT` (`Zeta23/Defs.lean:44`) is
the same transform, and `Zeta23.Params.phiHatR` (`Defs.lean:250`) its real part at real
argument. Through `ParamsQ.toParams` (whose `L` IS the paper's `L = λℒ`, `toParams_L`) this
is the paper's φ̂ term for term. -/

namespace ParamsQ

/-- `φ̂(r) := Re h_φ(r)` at the paper's scale (§2.2, §3), through the bridge.

Paper §2.2; mirrors `Zeta23.Params.phiHatR` (`Zeta23/Defs.lean:250`).
Rule 17: reached through `toParams`, whose `lam` is `LB / Zeta23.l T` and NOT `P.lam`; the
resulting `L` is `λℒ`, the q-aspect scale. No λ ≤ 1, no X ≤ T, no D₀. -/
def phiHatQ (P : ParamsQ) (r : ℝ) : ℝ := P.toParams.phiHatR P.T r

end ParamsQ

/-! ## 3.0b Corollary 3's constants that are NOT in `Defs.lean`

`Defs.lean` freezes `CfamEven`, `CfamEvenDyadic` and `PconstEvenDyadic`; the remaining three
Corollary 3 constants were first written further down the import order — `PconstEvenQ` in
`ZetaQ/Payoff.lean`, `lamStarEvenDyad`/`lamStarEvenQ` in `ZetaQ/Cor3Smooth.lean` — and
`Family.payoff` / `Family.lamStar` need them HERE. `lamStarEvenDyad` and `lamStarEvenQ` were
MOVED up (they are gone from `Cor3Smooth.lean`, which still sees them by import, so there is
one definition of each); `PconstEven` is a second name for `Payoff.PconstEvenQ`'s literal,
because `ZetaQ/Payoff.lean` does not import `ZetaQ/Certificate.lean` and vice versa.
All three belong in `Defs.lean` at the next freeze. -/

/-- `P_even = P_odd = 0.6980745436…` — Corollary 3's constant over `q ≤ Q`, at `C = π⁴/9`.
Numerically identical to `ZetaQ.Payoff.PconstEvenQ`;
the two are kept in step by `ZetaQ.PconstEvenQ_eq_PconstEven` (`ZetaQ/DesignProfile.lean`,
the first file that imports both `Certificate` and `Payoff`). -/
def PconstEven : ℝ := 0.6980745436

/-- `λ*_even,dyad = 1.1015998422` (`C = 4π⁴/27`). **Greater than 1.** -/
def lamStarEvenDyad : ℝ := 1.1015998422

/-- `λ*_even = 1.1329788821` (`C = π⁴/9`; `Payoff.lean` `payoff_feasible_even_qQ`
docstring). **Greater than 1.** -/
def lamStarEvenQ : ℝ := 1.1329788821

/-! ### The REFIT bandwidths of record for the four parity families

`Family.lamStar` routes the four Corollary 3 constructors at the two constants below, NOT at
`lamStarEvenDyad` / `lamStarEvenQ` above. The refit trades `0.006` (resp. `0.004`) of `λ` for
the product-window Gevrey budget: at the two original bandwidths the design profile has to be
degree 10 (resp. 8) and `gevreyBprod ≤ 40000` was not available, which is what
`ZetaQ.design_gevreyBprod_le_cor3` used to record as a `sorry`. At the two refit bandwidths a
degree-12 (resp. degree-10) profile realises `P = 0.6919144470` / `0.6980487914` — still above
the shipped certificates `Payoff.Pcert_even_dyad_smooth = 6919/10000` and
`Payoff.Pcert_evenQ_smooth = 349/500`, which is all `ZetaQ.kappaC_le_kappaCert` consumes — and
`ZetaQ.design_gevreyBprod_evenDyad12` / `_evenQ10` close the budget.

**The two constants above are NOT edited in place**: `ZetaQ/Cor3Smooth.lean` states
`payoff_feasible_even_dyadic_smooth` / `payoff_feasible_even_qQ_smooth` at those exact
literals, and editing them would silently break those admissibility certificates. -/

/-- `λ'_even,dyad = 1.0955998422` — the REFIT even/odd dyadic bandwidth of record
(`Family.lamStar` on `evenDyadic` / `oddDyadic`). **Greater than 1.** -/
def lamStarEvenDyad12 : ℝ := 1.0955998422

/-- `λ'_even = 1.1289788821` — the REFIT even/odd `q ≤ Q` bandwidth of record
(`Family.lamStar` on `evenQle` / `oddQle`). **Greater than 1.** -/
def lamStarEvenQ10 : ℝ := 1.1289788821

/-! ## 3.1 The family index

Paper §1.1, §2.2: 𝔉_Q is the set of primitive χ mod `1 < q ≤ Q` (Corollary 2: q ∈ (Q/2, Q]).
`ZetaQ.primitiveChars`, `phiStar`, `famCard`, `famCardDyadic` are frozen in `Defs.lean`;
this layer only selects between the two modulus ranges so that Theorem 1 and Corollary 2
are one statement schema.

**F32 (decided): the `q ≤ Q` range is `1 < q ≤ Q`.** §1.1's printed definition
omitted the lower bound that §2.2 (no pole term) and [R]'s Theorem E (`q > 1`) both assume;
`Family.moduli` now carries it. Full reasoning and the `+1` in `Family.size` at the two
docstrings below. -/

/-- The families of §1.1 and §12.3: `qle` = all primitive χ of modulus q ≤ Q (Theorem 1);
`dyadic` = q ∈ (Q/2, Q] (Corollary 2); and the four parity-restricted subfamilies of
Corollary 3 (§12.3), which keep the same modulus ranges but halve the character set.

**Spine invariant (added with the Corollary 3 constructors).** A family is now a pair
"modulus range × character selector": `Family.moduli` gives the first and `Family.chars` the
second, and *every* aggregate — `Family.size`, `familySum`, `Tail.famIdx` — is built from
those two. `qle`/`dyadic` have `Family.chars = ZetaQ.primitiveChars`, so their bodies are
unchanged up to `rfl` and the two headline theorems are untouched. -/
inductive Family
  /-- q ≤ Q — Theorem 1's family, `C = π⁴/18`. -/
  | qle
  /-- Q/2 < q ≤ Q — Corollary 2's family, `C = 2π⁴/27`. -/
  | dyadic
  /-- q ≤ Q, χ EVEN — Corollary 3's family, `C = π⁴/9`. -/
  | evenQle
  /-- q ≤ Q, χ ODD — Corollary 3's family, `C = π⁴/9` (same count as the even class up to
  the `S(q)` correction of §12.3; the paper uses the same `C`). -/
  | oddQle
  /-- Q/2 < q ≤ Q, χ EVEN — Corollary 3's dyadic family, `C = 4π⁴/27`. -/
  | evenDyadic
  /-- Q/2 < q ≤ Q, χ ODD — Corollary 3's dyadic family, `C = 4π⁴/27`. -/
  | oddDyadic
  /-- q ≤ Q, χ EVEN, run at THEOREM 1's design — Corollary 3″'s reflected-sieve family.
  Same moduli, characters, size and `Cconst = π⁴/9` as `evenQle` (so its zero counts ARE
  `evenQle`'s, by `rfl`), but the bandwidth, profile, zone secant, payoff and `κ_cert` of `qle`:
  the reflected large sieve (`ZetaQ/ReflectedSieve.lean`) charges a parity class `Q²/2`, so the
  out-zone constant is `Cconst/2 = π⁴/18` and Theorem 1's certificate applies
  (`ZetaQ/Cor3Frob.lean`, `ZetaQ/Cor3Full.lean`). -/
  | evenQleR
  /-- q ≤ Q, χ ODD, at Theorem 1's design — see `evenQleR`. -/
  | oddQleR
  /-- Q/2 < q ≤ Q, χ EVEN, at Corollary 2's design (`Cconst = 4π⁴/27`, out-zone `2π⁴/27`). -/
  | evenDyadicR
  /-- Q/2 < q ≤ Q, χ ODD, at Corollary 2's design — see `evenDyadicR`. -/
  | oddDyadicR

/-- The modulus range of a family.

### 🚩 **F32: `q = 1` IS EXCLUDED — `Icc 2 Qn`, not `Icc 1 Qn`.**

`ZetaQ.primitiveChars 1 = {1}`: the trivial character mod 1 **is** primitive
(`DirichletCharacter.isPrimitive_one_level_one`), so at `q = 1` the family member's
`L`-function is `ζ` itself, which has a pole at `s = 1`. That single member is exactly where

  * paper §2.2's no-pole hypothesis — "`L(s,χ)` entire for primitive `χ ≠ χ₀`", which is H2
    and which `ZetaQ.nuQ` encodes by carrying **no** pole term — fails; and
  * [R]'s Theorem E, whose statement is for `q > 1`
    (`Zeta23.ThmE.*`, and hence `ZetaQ.EFChi.rtrace_hatQ_gridGram_eq_Gz` /
    `frobSq_hatQ_gridGram_eq_Gz`), does not apply.

**Paper §2.2 and [R] both already exclude it; only §1.1's family definition omitted the
bound**, and this line is where that omission lived. The exclusion is therefore a
transcription repair, not a change of theorem: it makes `Family.qle` the family the rest of
the paper argues about. Cost: one character out of `|𝔉_Q| ≍ (18/π⁴)Q²`, i.e. relative
`O(Q^{-2})`; `|𝔉_Q|` itself is `ZetaQ.famCard Qn − 1`, see `Family.size`.

`Family.dyadic`'s `Finset.Ioc (Qn/2) Qn` already excludes `q = 1` for every `Qn ≥ 2`
(`Qn/2 ≥ 1`), so it is left exactly as it was.

**The one companion change, in the next declaration:** `Family.size` must run over the SAME
index set, or it stops being `|𝔉_Q|`. It is therefore spelled out over `Finset.Icc 2 Qn`
instead of citing the frozen `ZetaQ.famCard` (whose index set is `Finset.Icc 1 Qn`). See there
for why that is the conservative choice and what it costs. -/
def Family.moduli : Family → ℕ → Finset ℕ
  | Family.qle, Qn => Finset.Icc 2 Qn
  | Family.dyadic, Qn => Finset.Ioc (Qn / 2) Qn
  | Family.evenQle, Qn => Finset.Icc 2 Qn
  | Family.oddQle, Qn => Finset.Icc 2 Qn
  | Family.evenDyadic, Qn => Finset.Ioc (Qn / 2) Qn
  | Family.oddDyadic, Qn => Finset.Ioc (Qn / 2) Qn
  | Family.evenQleR, Qn => Finset.Icc 2 Qn
  | Family.oddQleR, Qn => Finset.Icc 2 Qn
  | Family.evenDyadicR, Qn => Finset.Ioc (Qn / 2) Qn
  | Family.oddDyadicR, Qn => Finset.Ioc (Qn / 2) Qn

/-- **The character selector of a family** — the second half of the "modulus range ×
character set" pair a `Family` denotes.

`qle`/`dyadic` take *all* primitive characters of the modulus, so `Family.chars` is the
frozen `ZetaQ.primitiveChars` and every `qle`/`dyadic` fact is unchanged **by `rfl`**.
Corollary 3's four families filter on the frozen `ZetaQ.parity`
(`parity χ = 0 ↔ χ.Even`).

**Why `ZetaQ.parity` and not `DirichletCharacter.Even`:** only ℕ-equality decidability is
needed, so no `Classical.decPred` instance leaks into the `Finset.filter`, and — decisive
here — `ZetaQ.CharSums` (which owns `primitiveCharsEven`) is *not* on `Certificate.lean`'s
import path. `ZetaQ.Cor3.evenPrimitiveChars` is the same
`Finset` spelled the same way, and `ZetaQ.Cor3.primitiveCharsEven_eq` (`Normalisation.lean`
§12.3) is the ONE canonical bridge to the `CharSums` spelling; `ZetaQ.chars_evenQle_eq` and
friends (`Zones.lean`) compose it with the `rfl` below and are what the spine cites.

Paper §1.1, §12.3.
Rule 17: no λ, X or D₀ occurs. -/
def Family.chars : Family → (q : ℕ) → Finset (DirichletCharacter ℂ q)
  | Family.qle, q => primitiveChars q
  | Family.dyadic, q => primitiveChars q
  | Family.evenQle, q => (primitiveChars q).filter (fun χ => parity χ = 0)
  | Family.oddQle, q => (primitiveChars q).filter (fun χ => parity χ = 1)
  | Family.evenDyadic, q => (primitiveChars q).filter (fun χ => parity χ = 0)
  | Family.oddDyadic, q => (primitiveChars q).filter (fun χ => parity χ = 1)
  | Family.evenQleR, q => (primitiveChars q).filter (fun χ => parity χ = 0)
  | Family.oddQleR, q => (primitiveChars q).filter (fun χ => parity χ = 1)
  | Family.evenDyadicR, q => (primitiveChars q).filter (fun χ => parity χ = 0)
  | Family.oddDyadicR, q => (primitiveChars q).filter (fun χ => parity χ = 1)

/-- **The one lemma the whole parity fan-out runs on:** a family's characters are primitive.
Companion to `ZetaQ.EFChi.isPrimitive_of_mem_primitiveChars`: every per-character hypothesis
in §§7–10 is stated `∀ χ ∈ primitiveChars q`, and this is what lets those hypotheses be used
under `∑ χ ∈ F.chars q`. Rule 17: no parameter occurs. -/
theorem Family.chars_subset (F : Family) (q : ℕ) : F.chars q ⊆ primitiveChars q := by
  cases F <;>
    first
      | exact Finset.Subset.refl _
      | exact Finset.filter_subset _ _

@[simp] theorem Family.chars_qle (q : ℕ) : Family.qle.chars q = primitiveChars q := rfl

@[simp] theorem Family.chars_dyadic (q : ℕ) : Family.dyadic.chars q = primitiveChars q := rfl

/-- **`F` is one of the two FULL families of §1.1** — `qle` (Theorem 1) or `dyadic`
(Corollary 2) — as opposed to one of Corollary 3's four parity-restricted ones.

This is the side condition that separates the two regimes throughout §§7–10. Everything in
the tree that prices a modulus at `φ*(q)` — every `∑ q, phiStar q · (…)` row of §10, the
§12.2 family count, the RvM lower bound — is a statement about the FULL character set, and is
simply false by a factor of about two for the parity families. Rather than weaken those
statements, the proofs that need them carry `hF : F.IsFull`, and the parity branch was
originally left as a marked `sorry` in `ZetaQ/Budget.lean`. **Those branches are all closed**
: the parity families are priced at the full `φ*(q)`, which costs a second factor
of two and which every `A₀`-generic consumer absorbs — see `Budget.NIIFam_avg_le` and
`Margin.famNIIUpper_parity_of_valid`. `IsFull` survives as the hypothesis of the statements
that genuinely need the full character set. -/
def Family.IsFull (F : Family) : Prop := F = Family.qle ∨ F = Family.dyadic

theorem Family.isFull_qle : Family.qle.IsFull := Or.inl rfl

theorem Family.isFull_dyadic : Family.dyadic.IsFull := Or.inr rfl

/-- On a full family the character set IS the frozen `ZetaQ.primitiveChars`. -/
theorem Family.chars_eq_of_isFull {F : Family} (h : F.IsFull) (q : ℕ) :
    F.chars q = primitiveChars q := by
  rcases h with rfl | rfl <;> rfl

/-- On a full family the per-modulus weight IS `φ*(q)`. -/
theorem Family.card_chars_of_isFull {F : Family} (h : F.IsFull) (q : ℕ) :
    (F.chars q).card = phiStar q := by
  rw [F.chars_eq_of_isFull h]; rfl

/-- `φ*_F(q) := |F.chars q|` — the per-modulus weight. `= phiStar q` for `qle`/`dyadic`
(by `rfl`), and the even/odd prim-count of §12.3 for the four Corollary 3 families. -/
def Family.weight (F : Family) (q : ℕ) : ℕ := (F.chars q).card

theorem Family.weight_le_phiStar (F : Family) (q : ℕ) : F.weight q ≤ phiStar q :=
  Finset.card_le_card (F.chars_subset q)

/-- `|𝔉_Q|` for the family — the number of characters `Family.moduli`/`familySum` actually
range over, in both cases.

**🚩 F32 bookkeeping — the ONE thing the `q = 1` exclusion changed besides `Family.moduli`.**
The dyadic body is the frozen `ZetaQ.famCardDyadic`, unchanged. The `qle` body was
`ZetaQ.famCard Qn = ∑_{q ∈ Icc 1 Qn} φ*(q)`, and `Defs.lean` is frozen, so
it is now written out over the same `Icc 2 Qn` that `Family.moduli` uses. Since
`φ*(1) = |primitiveChars 1| = 1` (the trivial character mod 1 is primitive), the relation to
the frozen constant is exactly

    Family.size Family.qle Qn  =  ZetaQ.famCard Qn − 1        (`Qn ≥ 1`)

— peeling the bottom index, `Finset.Icc 1 Qn = insert 1 (Finset.Icc 2 Qn)` for `Qn ≥ 1`
(`Finset.Icc_erase_left` / `Finset.sum_insert`).

**Why this and not "keep `famCard` and absorb a `+1`".** Every consumer of `sizeR` reads it as
`|𝔉_Q|`, on both sides of inequalities, and two of them are *identities*, not estimates:
`ZetaQ/Tail.lean`'s `card_famIdx` (`|famIdx F Qn| = F.sizeR Qn`, `rfl` in both cases, and what makes
`Btr`/`BF` the cardinality the per-member tail bounds are summed over) and, through it, §7.3's
two family exports `abs_trGz_sub_trAhat_fam_le_Btr` /
`sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF`. Keeping `famCard` here would have made that
identity FALSE by one character and broken `ZetaQ/Tail.lean` (checked: `card_famIdx`'s `qle`
case fails to be `rfl`), for no gain — while `ZetaQ.Btr`, `ZetaQ.BF`, `SharpZeroDensity`,
`FamRvMLower`, `FamNIIUpper` and `FamSizeLower` all keep their exact intended meanings under
the spelled-out body. Nothing outside `Certificate`/`Budget`/`Tail` mentions `Family.size` at
all (`Normalisation`, `Zones`, `Ends`, `Sieve` all use the frozen `famCard`/`phiStar`
directly), so this body is the whole of the change.

**What is owed, and it is `O(Q^{-2})`:** anything that wants §12.2's count for *this* size must
bridge `famCard − 1` to `famCard`. §12.2's own statements
(`ZetaQ.Normalisation.famCard_asymp`, `famConst_asymp`) are about `famCard`, and
`famCard Qn − 1 ~ (18/π⁴)Qn²` just as well, so the bridge is the display above plus
`phiStar 1 = 1` (`Finset.card_eq_one` on `primitiveChars 1 = {1}`; §N6 of
`ZetaQ/Normalisation.lean` already establishes that value inline). The only §10 `Prop` that
would feel it is `ZetaQ.FamSizeLower` (`Qn² ≤ Cconst·sizeR`), a hypothesis nothing in the tree
yet discharges.

**Corollary 3 (§12.3).** The four parity branches are `∑_q |F.chars q|` over the same two
modulus ranges — i.e. `∑_q evenPrimCount q` / `∑_q oddPrimCount q` in the spelling of
`ZetaQ.Normalisation`. `Family.size F Qn = ∑ q ∈ F.moduli Qn, (F.chars q).card` therefore
holds in EVERY branch, `qle`/`dyadic` included (`phiStar q := (primitiveChars q).card` is
`rfl`); that uniformity is what keeps `ZetaQ/Tail.lean`'s `card_famIdx` six `rfl`s. -/
def Family.size : Family → ℕ → ℕ
  | Family.qle, Qn => ∑ q ∈ Finset.Icc 2 Qn, phiStar q
  | Family.dyadic, Qn => famCardDyadic Qn
  | Family.evenQle, Qn => ∑ q ∈ Finset.Icc 2 Qn, (Family.evenQle.chars q).card
  | Family.oddQle, Qn => ∑ q ∈ Finset.Icc 2 Qn, (Family.oddQle.chars q).card
  | Family.evenDyadic, Qn => ∑ q ∈ Finset.Ioc (Qn / 2) Qn, (Family.evenDyadic.chars q).card
  | Family.oddDyadic, Qn => ∑ q ∈ Finset.Ioc (Qn / 2) Qn, (Family.oddDyadic.chars q).card
  | Family.evenQleR, Qn => ∑ q ∈ Finset.Icc 2 Qn, (Family.evenQleR.chars q).card
  | Family.oddQleR, Qn => ∑ q ∈ Finset.Icc 2 Qn, (Family.oddQleR.chars q).card
  | Family.evenDyadicR, Qn => ∑ q ∈ Finset.Ioc (Qn / 2) Qn, (Family.evenDyadicR.chars q).card
  | Family.oddDyadicR, Qn => ∑ q ∈ Finset.Ioc (Qn / 2) Qn, (Family.oddDyadicR.chars q).card

/-- `Family.size` is `∑_q |F.chars q|` in every branch — the uniform spelling.
Rule 17: no parameter occurs. -/
theorem Family.size_eq (F : Family) (Qn : ℕ) :
    F.size Qn = ∑ q ∈ F.moduli Qn, (F.chars q).card := by
  cases F <;> rfl

/-- `|𝔉_Q|` as a real. -/
def Family.sizeR (F : Family) (Qn : ℕ) : ℝ := (F.size Qn : ℝ)

/-- `C := Q²/|𝔉_Q|` — the family constant (§2.2). `π⁴/18` for `qle`, `2π⁴/27` for `dyadic`;
both frozen in `Defs.lean` as `Cfam`, `CfamDyadic`. -/
def Family.Cconst : Family → ℝ
  | Family.qle => Cfam
  | Family.dyadic => CfamDyadic
  | Family.evenQle => CfamEven
  | Family.oddQle => CfamEven
  | Family.evenDyadic => CfamEvenDyadic
  | Family.oddDyadic => CfamEvenDyadic
  | Family.evenQleR => CfamEven
  | Family.oddQleR => CfamEven
  | Family.evenDyadicR => CfamEvenDyadic
  | Family.oddDyadicR => CfamEvenDyadic

/-- `P` — the value of §11's C-penalised variational problem at the family's `C`.
`0.7212835668…` (Theorem 1) / `0.7099167448…` (Corollary 2); frozen as `Pconst`,
`PconstDyadic`. Shipped by `ZetaQ/Payoff.lean` as a FEASIBILITY certificate, not an equality
(the feasibility route; see `ZetaQ/Payoff.lean`). -/
def Family.payoff : Family → ℝ
  | Family.qle => Pconst
  | Family.dyadic => PconstDyadic
  | Family.evenQle => PconstEven
  | Family.oddQle => PconstEven
  | Family.evenDyadic => PconstEvenDyadic
  | Family.oddDyadic => PconstEvenDyadic
  | Family.evenQleR => Pconst
  | Family.oddQleR => Pconst
  | Family.evenDyadicR => PconstDyadic
  | Family.oddDyadicR => PconstDyadic

/-- `λ*` — the optimal bandwidth of §11. `1.2507321515` / `1.1931581210`, frozen as
`lamStar`, `lamStarDyadic`. **All six are > 1** — the fact the whole `ParamsQ` layer exists to
permit (Rule 17).

**The four parity branches are the REFIT bandwidths** `lamStarEvenQ10 = 1.1289788821` /
`lamStarEvenDyad12 = 1.0955998422` (§3.0b), not `lamStarEvenQ` / `lamStarEvenDyad`. See §3.0b
for why, and `ZetaQ.design_gevreyBprod_le_cor3` for what it bought. -/
def Family.lamStar : Family → ℝ
  | Family.qle => _root_.ZetaQ.lamStar
  | Family.dyadic => _root_.ZetaQ.lamStarDyadic
  | Family.evenQle => _root_.ZetaQ.lamStarEvenQ10
  | Family.oddQle => _root_.ZetaQ.lamStarEvenQ10
  | Family.evenDyadic => _root_.ZetaQ.lamStarEvenDyad12
  | Family.oddDyadic => _root_.ZetaQ.lamStarEvenDyad12
  | Family.evenQleR => _root_.ZetaQ.lamStar
  | Family.oddQleR => _root_.ZetaQ.lamStar
  | Family.evenDyadicR => _root_.ZetaQ.lamStarDyadic
  | Family.oddDyadicR => _root_.ZetaQ.lamStarDyadic

/-- `Σ_{χ ∈ 𝔉_Q}` — the family sum, a double sum over the family's moduli then over the
family's characters of that modulus. §3: "the direct sum over 𝔉_Q aggregates identically".

**Corollary 3 note.** The inner index set is `Family.chars`, not the frozen
`ZetaQ.primitiveChars`: that is the ONLY thing the four parity families change. For
`qle`/`dyadic` the two are the same `Finset` by `rfl` (`Family.chars_qle`,
`Family.chars_dyadic`), so §§3–10 are unchanged there.

Paper §2.2, §3.
Rule 17: no λ, X or D₀ occurs. -/
def familySum (F : Family) (Qn : ℕ) (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, f q χ

/-- On a FULL family (`Family.IsFull`) `familySum` is the frozen double sum over
`ZetaQ.primitiveChars` — the spelling every §§7–10 proof used before Corollary 3's families
existed. This is the one rewrite those proofs need. -/
theorem familySum_of_isFull {F : Family} (h : F.IsFull) (Qn : ℕ)
    (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    familySum F Qn f = ∑ q ∈ F.moduli Qn, ∑ χ ∈ primitiveChars q, f q χ :=
  Finset.sum_congr rfl fun q _ => by rw [F.chars_eq_of_isFull h]

/-! ## 3.2 The per-character and family zero counts

Paper §1.1: `N_χ(T,2T)` counts nontrivial zeros with multiplicity; `N^s_{0,χ}(T,2T)` counts
those that are **simple and on the critical line**. [R] already has both against Mathlib's
`DirichletCharacter.LFunction`: `Zeta23.ThmE.NcountL` and `Zeta23.ThmE.N0simpleL`
(`Zeta23/ThmE/Statement.lean:58`, `:67`). Those carry `[NeZero q]`; inside a `Finset.sum`
over `q` no such instance is available, so the wrappers below discharge it by a `dite` on
`q = 0` (a case the index sets `Finset.Icc 2 Qn` / `Finset.Ioc (Qn/2) Qn` never contain).
This is the robust encoding: no instance search inside the sum. -/

/-- `N_χ(T₁,T₂)` — nontrivial zeros of `L(s,χ)` with `T₁ < γ ≤ T₂`, with multiplicity, as a
real. Paper §1.1; wraps `Zeta23.ThmE.NcountL`.
Rule 17: the ordinate window is an explicit pair `(T₁,T₂)`; nothing ties it to X or D₀. -/
def NcountQ (q : ℕ) (χ : DirichletCharacter ℂ q) (T₁ T₂ : ℝ) : ℝ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    ((Zeta23.ThmE.NcountL χ T₁ T₂ : ℕ) : ℝ)

/-- `N^s_{0,χ}(T₁,T₂)` — zeros of `L(s,χ)` in the window that are **simple and on the
critical line**. Paper §1.1; wraps `Zeta23.ThmE.N0simpleL`
(`ThmE/Statement.lean:67`, `= (zerosInL ∩ {Re = 1/2} ∩ {mult = 1}).ncard`), which is [R]'s
`ZeroConfig.N0s` shape and NOT `N0star` (on-line but not necessarily simple).
Rule 17: clean. -/
def N0sQ (q : ℕ) (χ : DirichletCharacter ℂ q) (T₁ T₂ : ℝ) : ℝ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    ((Zeta23.ThmE.N0simpleL χ T₁ T₂ : ℕ) : ℝ)

/-- `𝒩 := Σ_{χ ∈ 𝔉_Q} N_χ(T₁,T₂)` (§2.2: `𝒩 ≍ Q²Tℒ`). -/
def NfamCount (F : Family) (Qn : ℕ) (T₁ T₂ : ℝ) : ℝ :=
  familySum F Qn (fun q χ => NcountQ q χ T₁ T₂)

/-- `Σ_{χ ∈ 𝔉_Q} N^s_{0,χ}(T₁,T₂)` — the left-hand side of Theorem 1 and of §3's display. -/
def N0sFamCount (F : Family) (Qn : ℕ) (T₁ T₂ : ℝ) : ℝ :=
  familySum F Qn (fun q χ => N0sQ q χ T₁ T₂)

/-- `N_{II,fam} := Σ_χ [N_χ(T−D, T) + N_χ(2T, 2T+D)]` — the buffer count at a **free** `D`.

Paper §2.2 (`I′ := (T − D₀, 2T + D₀]`), §7, §9. Mirrors `Zeta23.Assembly.NIID`
(`Zeta23/WindowD.lean:100`).
**Rule 17: `D` is a free real. This is deliberately NOT `Zeta23.Assembly.NII`
(`Assembly/Inputs.lean:33`), whose body substitutes `Zeta23.D0 T = Real.sqrt T`.** -/
def NIIFam (F : Family) (Qn : ℕ) (T D : ℝ) : ℝ :=
  familySum F Qn (fun q χ => NcountQ q χ (T - D) T + NcountQ q χ (2 * T) (2 * T + D))

/-- `𝒩` at the design point's own window `I = [T, 2T]`. -/
def NfamQ (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ := NfamCount F Qn P.T (2 * P.T)

/-- `Σ_χ N^s_{0,χ}(T,2T)` at the design point. -/
def N0sFamQ (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ := N0sFamCount F Qn P.T (2 * P.T)

/-- `N_{II,fam}` at the design point's **free** buffer `P.D0`.
Rule 17: `P.D0` is a `ParamsQ` FIELD; `Real.sqrt P.T` appears nowhere. -/
def NIIFamQ (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ := NIIFam F Qn P.T P.D0

/-- `N_χ ≥ 0` — it is the cast of a cardinality (or `0` at the excluded index `q = 0`).
Rule 17: n/a. -/
theorem NcountQ_nonneg (q : ℕ) (χ : DirichletCharacter ℂ q) (T₁ T₂ : ℝ) :
    0 ≤ NcountQ q χ T₁ T₂ := by
  unfold NcountQ
  split_ifs <;> positivity

/-- `𝒩 ≥ 0` — a double sum of the nonnegative `NcountQ`. This is the sign fact every
`mul_le_mul` against `𝒩` in §10 needs, and it is free.
Rule 17: n/a. -/
theorem NfamCount_nonneg (F : Family) (Qn : ℕ) (T₁ T₂ : ℝ) : 0 ≤ NfamCount F Qn T₁ T₂ := by
  unfold NfamCount familySum
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => NcountQ_nonneg _ _ _ _

/-- `𝒩 ≥ 0` at the design point. -/
theorem NfamQ_nonneg (P : ParamsQ) (F : Family) (Qn : ℕ) : 0 ≤ NfamQ P F Qn :=
  NfamCount_nonneg F Qn P.T (2 * P.T)

/-! ## 3.3 The grid Gram, the hat units, the family aggregates

Paper §3, verbatim:

> Per χ, the grid Gram `G(χ)_{kl} := ∫ φ̂(τ − τ_k)φ̂(τ − τ_l) ν_{X,χ}(τ)dτ`; by the
> q-uniform explicit formula (§9) this equals the zero-side matrix
> `Σ_ρ m_ρ h_φ(γ_ρ − τ_k)·conj(h_φ(…))`; hat units `Ĝ := G/(aL²)`, `a := L⁻¹∫φ²`.

The matrix type is **ℂ** (not ℝ) so that
`RHLinalg.rtrace` / `RHLinalg.frobSq` (`Zeta23/LinAlg/PosIndex.lean:70`, `:73`) apply
unchanged; the entries are real numbers coerced in, since ν is real and φ̂ is real at real
argument. -/

/-- The Gram entry `G(χ)_{kl} := ∫ φ̂(τ − τ_k) φ̂(τ − τ_l) ν_{X,χ}(τ) dτ` as a real.

Paper §3.
Rule 17: `ν_{X,χ}` is `ZetaQ.nuQ`, whose `X` is `P.XQ = (QT/2π)^λ` — the q-aspect X, which
is ≫ T at λ*. `τ_k` is `P.tauQ` at the q-aspect grid step `h = 2π/λℒ`. -/
def gridGramEntry (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) (k l : ℤ) : ℝ :=
  ∫ τ : ℝ, P.phiHatQ (τ - P.tauQ k) * P.phiHatQ (τ - P.tauQ l) * nuQ P q χ τ

/-- The grid Gram `G(χ)` of §3 as a `d × d` complex matrix, `d = ⌊LT/2π⌋ = P.dQ`.

Paper §3. Mirrors `Zeta23.ZeroConfig.Gz` / `Zeta23.Params.Gp`
(`Zeta23/Defs.lean:319`, `:291`) but is per-CHARACTER: [R] has no family object at all
It exists nowhere else in the tree.
Rule 17: as `gridGramEntry`. -/
def gridGram (P : ParamsQ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Matrix (Fin P.dQ) (Fin P.dQ) ℂ :=
  fun k l => ((gridGramEntry P χ ((k : ℕ) : ℤ) ((l : ℕ) : ℤ) : ℝ) : ℂ)

/-- Hat units `M ↦ M/(aL²)` (§3). Mirrors `Zeta23.Params.hat`
(`Zeta23/Defs.lean:305`) at the q-aspect `a = P.aQ` and `L = P.LB = λℒ`.

Rule 17: `P.LB` is `λℒ`, **not** `Zeta23.Params.L` at the T-aspect scale; `P.aQ` is
`P.toParams.a P.T`, which by `toParams_L` is `L⁻¹∫φ²` at the paper's `L`. -/
def hatQ (P : ParamsQ) {n : Type*} (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (((P.aQ * P.LB ^ 2)⁻¹ : ℝ) : ℂ) • M

/-- `tr Ĝ_fam := Σ_{χ ∈ 𝔉_Q} tr Ĝ(χ)`. §3: the trace is additive over the direct sum, which
is why "the family aggregates identically". -/
def trGhatFam (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ :=
  familySum F Qn (fun _q χ => RHLinalg.rtrace (hatQ P (gridGram P χ)))

/-- `‖Ĝ_fam‖²_F := Σ_{χ ∈ 𝔉_Q} ‖Ĝ(χ)‖²_F`. Same reason: `‖·‖²_F` is additive over the
direct sum. -/
def frobSqGhatFam (P : ParamsQ) (F : Family) (Qn : ℕ) : ℝ :=
  familySum F Qn (fun _q χ => RHLinalg.frobSq (hatQ P (gridGram P χ)))

/-! ## 3.4 The pair split (B_tr, B_F) of §7.3

Paper §7.3, verbatim:

> Over the direct sum: the operator norm is a MAX (the Weyl consumer pays nothing); the
> trace is additive, `|tr Ê_fam| ≤ |𝔉|θ₀/(aL) =: B_tr`; the Frobenius norm is √-additive,
> `‖Ê_fam‖_F ≤ √|𝔉|·θ₀/(aL) =: B_F`.

This is the **one exception** to "aggregates identically" (§3): the tail
perturbation aggregates by the pair mechanism, not the direct sum. [R] has only the scalar
case `B_tr = B_F = B`, folded into `N0star_lower_moment`'s hypothesis `h0`. -/

/-- `B_tr := |𝔉_Q|·θ₀/(aL)` — the trace-side tail budget (§7.3).
`θ₀` is §7's per-block operator-norm tail level, superexponentially small in `√(wD₀/A)`.

Rule 17: `θ₀` is a free real here; §7 bounds it by `exp(−(4/e)√(wD₀/A))·prefactor` at the
FREE `D₀`, never at `√T`. -/
def Btr (P : ParamsQ) (F : Family) (Qn : ℕ) (θ₀ : ℝ) : ℝ :=
  F.sizeR Qn * θ₀ / (P.aQ * P.LB)

/-- `B_F := √|𝔉_Q|·θ₀/(aL)` — the Frobenius-side tail budget (§7.3).
Rule 17: as `Btr`. -/
def BF (P : ParamsQ) (F : Family) (Qn : ℕ) (θ₀ : ℝ) : ℝ :=
  Real.sqrt (F.sizeR Qn) * θ₀ / (P.aQ * P.LB)

/-! ## 3.5 κ_C — the Frobenius main-term constant (NOT the parity κ(χ)) -/

/-- `κ_C := 2 − P` — the relation between §11's payoff value `P` and the Frobenius
main-term constant of §§4–6 (paper §3; §11; `fb.py:83`'s return dict
`dict(…, B=mu, P=2-mu)`, i.e. `B` *is* `min B`).

Paper §3, §11.
**Naming:** this is `κ_C`, *not* `ZetaQ.parity` (= `κ(χ) ∈ {0,1}`, the character parity of
§2.2, frozen in `ZetaQ/Defs.lean`). The paper flags the collision explicitly.
Rule 17: a pure real function; no λ, X or D₀. -/
def kappaCof (payoff : ℝ) : ℝ := 2 - payoff

/-- `κ_C(π⁴/18) = 2 − 0.7212835668 = 1.2787164332` — Theorem 1's Frobenius constant.

**⚠ F58.** This is `min B` over profiles `v = φ²` (§11, the `cos(√2 t)`-bulk
profile). `frobenius_row` asserts it for `frobSqGhatFam`, which `gridGramEntry` builds from the
FLAT taper (`phiHatQ = toParams.phiHatR`); for the flat taper at `λ*` the §§4–6 route gives
`B_flat = 1.4085520`. So `κ_C` here is the constant of a profile the tree's design does not use.
See "the design window must carry a profile" in `ZetaQ/Budget.lean`'s header. -/
def kappaC : ℝ := kappaCof Pconst

/-- `κ_C(2π⁴/27) = 2 − 0.7099167448 = 1.2900832552` — Corollary 2's. -/
def kappaCDyadic : ℝ := kappaCof PconstDyadic

/-- `κ_C` selected by family. -/
def Family.kappaC (F : Family) : ℝ := kappaCof F.payoff

/-- **`2 − κ_C = P`** — the identity that turns Proposition 3.1's conclusion into Theorem 1's
headline coefficient. `Pconst` for `Family.qle`, `PconstDyadic` for `Family.dyadic`
(paper §3; §11; `fb.py:83`'s `dict(…, B=mu, P=2-mu)`).
Rule 17: n/a. -/
theorem two_sub_kappaC (F : Family) : 2 - F.kappaC = F.payoff := by
  unfold Family.kappaC kappaCof
  ring

/-- `κ_C(π⁴/18) = 1.2787164332` — the numeral, i.e. `2 − Pconst` evaluated.
Rule 17: n/a (numeric). -/
theorem kappaC_value : kappaC = 1.2787164332 := by
  unfold kappaC kappaCof Pconst
  norm_num

/-- `κ_C(2π⁴/27) = 1.2900832552`. -/
theorem kappaCDyadic_value : kappaCDyadic = 1.2900832552 := by
  unfold kappaCDyadic kappaCof PconstDyadic
  norm_num

/-! ## 3.6 The certificate, displayed in full (H1) -/

/-- **§3's certificate display (H1), at family level**, verbatim:

> `Σ_χ N^s_{0,χ}(T, 2T) ≥ 4 tr Ĝ_fam − ‖Ĝ_fam‖²_F − 2𝒩 − 3·N_{II,fam}`
> `                       − [4B_tr + 2B_F·‖Ĝ_fam‖_F + B_F²]`

The paper is explicit that "the −2𝒩 and −3N_{II} window terms are **part of the
inequality, not corrections**". Stated as a `Prop` on bare reals so that
Proposition 3.1 is pure moment algebra, exactly as `Zeta23.Assembly.N0star_lower_moment`
is; the orientation is flipped to `… ≤ N0sFam` to match [R]'s.

Paper §3.
Rule 17: **CLEAN** — bare reals only; no λ, no X, no D₀ can occur in a `Prop` over reals.
The Rule-17 content sits in *what is substituted*: `NIIfam` must come from `NIIFamQ` at the
free `P.D0`, never from `Zeta23.Assembly.NII`. -/
def CertificateDisplay
    (N0sFam Nfam NIIfam trGhat frobSqGhat Btr BF : ℝ) : Prop :=
  4 * trGhat - frobSqGhat - 2 * Nfam - 3 * NIIfam
    - (4 * Btr + 2 * BF * Real.sqrt frobSqGhat + BF ^ 2) ≤ N0sFam

/-- **Proposition 3.1 (quantitative pair moment certificate)** — paper §3,
verbatim:

> Suppose for a given (Q, T): (i) the display above; (ii) `𝒩(1 − r₁) ≤ tr Ĝ_fam` and
> `‖Ĝ_fam‖²_F ≤ (κ_C + r₂)𝒩`, where κ_C is the Frobenius main-term constant of §§4–6 (NOT
> the parity κ(χ) of §2.2); (iii) `N_{II,fam} ≤ r₃𝒩`; (iv) `B_tr ≤ r₄𝒩` and `B_F ≤ r₅√𝒩`.
> Then `Σ_χ N^s_{0,χ} ≥ [2 − κ_C − (4r₁ + r₂ + 3r₃ + 4r₄ + 2r₅√(κ_C+r₂) + r₅²)]·𝒩`.

Proof (paper): "the moment algebra of [R]'s certificate with the scalar B split into
(B_tr, B_F) — trace linearity, the Frobenius triangle inequality, and `√frobSq(Ê) ≤ B_F`;
three displays."

Mirror of `Zeta23.Assembly.N0star_lower_moment` (`Zeta23/Assembly/Certificate.lean:24–31`),
whose `B * (4 + 2·√frGh + B)` is replaced by `4·B_tr + 2·B_F·√frGh + B_F²`; that theorem is
the case `B_tr = B_F = B`.

Fidelity resolutions: the paper's **relative** forms
`(1−r₁)𝒩 ≤ tr Ĝ` and `‖Ĝ‖²_F ≤ (κ_C+r₂)𝒩` are used, not [R]'s absolute `N − R₁ ≤ trGh`,
`frGh ≤ κN + R₂` — they agree at `Rᵢ = rᵢ𝒩`, and §10.3's rows are relative. The conclusion
is flipped to `[…]·𝒩 ≤ N0sFam`; same statement.

Paper §3. Derivation: [R] `Assembly/Certificate.lean:24–31` + §7.3.
Depends on: `CertificateDisplay`.
**Rule 17: CLEAN.** Pure real arithmetic in `(𝒩, tr, frobSq, N_II, B_tr, B_F, κ_C, r₁…r₅)`.
No λ, no X, no D₀ occurs — this is the whole point of stating it on bare reals, and it is
why it is the fixed-(Q,T) form and not `count_certificate`'s ε-filter form (R5, §10.5:
"no ε-limit is taken"). -/
theorem prop_3_1_pair_moment_certificate
    {N0sFam Nfam NIIfam trGhat frobSqGhat Btr BF κC r₁ r₂ r₃ r₄ r₅ : ℝ}
    (hN : 0 ≤ Nfam)
    (hBtr : 0 ≤ Btr) (hBF : 0 ≤ BF)
    (hκr₂ : 0 ≤ κC + r₂)
    -- (i) the display of §3
    (hdisp : CertificateDisplay N0sFam Nfam NIIfam trGhat frobSqGhat Btr BF)
    -- (ii) the two moment hypotheses, in the paper's relative form
    (htr : (1 - r₁) * Nfam ≤ trGhat)
    (hfrob : frobSqGhat ≤ (κC + r₂) * Nfam)
    -- (iii) the buffer count
    (hNII : NIIfam ≤ r₃ * Nfam)
    -- (iv) the pair perturbation (§7.3)
    (hBtr' : Btr ≤ r₄ * Nfam)
    (hBF' : BF ≤ r₅ * Real.sqrt Nfam) :
    (2 - κC - (4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
                 + 2 * r₅ * Real.sqrt (κC + r₂) + r₅ ^ 2)) * Nfam ≤ N0sFam := by
  unfold CertificateDisplay at hdisp
  have hsN : Real.sqrt Nfam ^ 2 = Nfam := Real.sq_sqrt hN
  have hsN0 : 0 ≤ Real.sqrt Nfam := Real.sqrt_nonneg _
  have hr₅N : 0 ≤ r₅ * Real.sqrt Nfam := hBF.trans hBF'
  -- Display 3: `√frobSq(Ĝ) ≤ √(κ_C + r₂)·√𝒩`.
  have hsq : Real.sqrt frobSqGhat ≤ Real.sqrt (κC + r₂) * Real.sqrt Nfam := by
    rw [← Real.sqrt_mul hκr₂]
    exact Real.sqrt_le_sqrt hfrob
  -- The Frobenius cross term: `B_F·√frobSq(Ĝ) ≤ r₅√(κ_C + r₂)·𝒩`.
  have hcross : BF * Real.sqrt frobSqGhat ≤ r₅ * Real.sqrt (κC + r₂) * Nfam := by
    have h1 : BF * Real.sqrt frobSqGhat
        ≤ (r₅ * Real.sqrt Nfam) * (Real.sqrt (κC + r₂) * Real.sqrt Nfam) :=
      mul_le_mul hBF' hsq (Real.sqrt_nonneg _) hr₅N
    have h2 : (r₅ * Real.sqrt Nfam) * (Real.sqrt (κC + r₂) * Real.sqrt Nfam)
        = r₅ * Real.sqrt (κC + r₂) * Nfam := by
      linear_combination (r₅ * Real.sqrt (κC + r₂)) * hsN
    linarith
  -- The Frobenius square term: `B_F² ≤ r₅²·𝒩`.
  have hBFsq : BF ^ 2 ≤ r₅ ^ 2 * Nfam := by
    have h := mul_self_le_mul_self hBF hBF'
    have e : (r₅ * Real.sqrt Nfam) * (r₅ * Real.sqrt Nfam) = r₅ ^ 2 * Nfam := by
      linear_combination (r₅ ^ 2) * hsN
    rw [e] at h
    calc BF ^ 2 = BF * BF := pow_two BF
      _ ≤ r₅ ^ 2 * Nfam := h
  linarith [hdisp, htr, hfrob, hNII, hBtr', hcross, hBFsq]

/-- **§7.3's pair perturbation lemma**, generalizing [R]'s scalar version (which is the case
`B_tr = B_F`):

> The pair perturbation lemma
> `(4 tr Ĝ − ‖Ĝ‖²_F − [4B_tr + 2B_F‖Ĝ‖_F + B_F²] ≤ 4 tr Â − ‖Â‖²_F`; three lines,
> generalizing [R]'s scalar version, which is the case `B_tr = B_F`) feeds Proposition
> 3.1's (iv) with per-block θ₀ → 0 only: **no negative power of Q is demanded anywhere.**

`Â` is the truncated (window) zero-side matrix, `Ĝ` the full one, `Ê = Ĝ − Â` the tail.

Paper §7.3.
Depends on: nothing.
**Rule 17: CLEAN** — bare reals; no λ, X or D₀. Note the paper's own emphasis: only
`θ₀ → 0` per block is demanded, i.e. no `Q^{−δ}` and hence no bandwidth cap.

**🚩🚩 THE STATEMENT AS FROZEN IS FALSE — DO NOT ATTEMPT TO PROVE IT. 🚩🚩**

Two independent defects, both in the Frobenius hypothesis `hF`, both machine-checked:

1. **`hF` is oriented backwards.** The paper's step is `‖Â‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F ≤ ‖Ĝ‖_F + B_F`
   (LEMMA_QT §QT.c; [R] `Assembly.lean:150–166` derives it from `frobSq_sub_le`), i.e.
   `√frobSqA − √frobSqG ≤ B_F`. What is written is `√frobSqG − √frobSqA ≤ B_F`, which is a
   LOWER bound on `frobSqA` — exactly the wrong direction, since the conclusion needs
   `frobSqA ≤ frobSqG + 2B_F√frobSqG + B_F²`.
   *Failing instance* (all quantities nonnegative, every hypothesis satisfied):
   `trG = trA = 0`, `frobSqG = 0`, `frobSqA = 100`, `B_tr = B_F = 0`.
   Then `hF : √0 − √100 = −10 ≤ 0` holds and the conclusion reads `0 ≤ −100`.
2. **`0 ≤ frobSqG` is missing.** Even after fixing (1) the statement fails at
   `frobSqG = −10`, everything else `0`, because `Real.sqrt` truncates at `0`
   (`√(−10) = 0`, so `(√frobSqG)² = 0 > frobSqG`). [R]'s version never needs the
   hypothesis because there `frobSqG` is literally `RHLinalg.frobSq Ĝ ≥ 0`; the bare-real
   abstraction has to state it. Note `hfrA : 0 ≤ frobSqA` IS present — only the `G` side
   was dropped.

**RESOLVED: the statement has been REPAIRED in
place.** The repair is exactly "swap the two `Real.sqrt`s in `hF`, and add `0 ≤ frobSqG`",
which restores the paper's own §7.3 display; nothing else about the lemma moves, and at the
intended instantiation both repairs are free (`frobSqG` is a `RHLinalg.frobSq`, and §7.3
supplies the triangle inequality in the paper's direction). "Statements are frozen" exists
to block edits of convenience, not to preserve a transcription error — a known-false
statement left in the skeleton is a trap for every later reader. The paper is NOT wrong
here; only our transcription was. The counterexample above is retained as the record of
why. -/
theorem pair_perturbation
    {trG frobSqG trA frobSqA Btr BF : ℝ}
    (hBtr : 0 ≤ Btr) (hBF : 0 ≤ BF)
    (hfrA : 0 ≤ frobSqA) (hfrG : 0 ≤ frobSqG)
    (htr : |trG - trA| ≤ Btr)
    (hF : Real.sqrt frobSqA - Real.sqrt frobSqG ≤ BF) :
    4 * trG - frobSqG - (4 * Btr + 2 * BF * Real.sqrt frobSqG + BF ^ 2)
      ≤ 4 * trA - frobSqA := by
  -- Display 1 (trace linearity): `tr Â ≥ tr Ĝ − B_tr`.
  have htr' : trG - trA ≤ Btr := (le_abs_self _).trans htr
  -- Displays 2–3 (Frobenius triangle inequality, squared).
  have hgG : Real.sqrt frobSqG ^ 2 = frobSqG := Real.sq_sqrt hfrG
  have hgA : Real.sqrt frobSqA ^ 2 = frobSqA := Real.sq_sqrt hfrA
  have hA0 : 0 ≤ Real.sqrt frobSqA := Real.sqrt_nonneg _
  have hG0 : 0 ≤ Real.sqrt frobSqG := Real.sqrt_nonneg _
  nlinarith [hgG, hgA, hA0, hG0, hF, htr', hBF]

/-- **§7.3's pair perturbation lemma, in the paper's own orientation — PROVED.**

This is `pair_perturbation` with the two defects listed in its docstring repaired: `hF` is
the paper's Frobenius triangle inequality `‖Â‖_F ≤ ‖Ĝ‖_F + B_F` (LEMMA_QT §QT.c), and
`0 ≤ frobSqG` is stated (it is free at every intended instantiation, where `frobSqG` is a
`RHLinalg.frobSq`). The conclusion is byte-identical to `pair_perturbation`'s.

It was recorded here, next to the frozen statement rather than in place of it, to show that
the whole content of the §7.3 lemma was present while `pair_perturbation` was still a `sorry`
— i.e. that what remained was a transcription question and nothing more. `pair_perturbation`
has since been proved, which is why this variant is `@[deprecated]`. It is the exact
bare-real shadow of `ZetaQ.four_tr_sub_frobSq_perturb_pair` (`ZetaQ/Tail.lean`), whose
matrix-level statement has both repairs built in for free.

Paper §7.3; [R] `Zeta23.Assembly.four_tr_sub_frobSq_perturb`
(`Zeta23/Assembly.lean:150`) is the diagonal case `B_tr = B_F`.
**Rule 17: CLEAN** — bare reals; no λ, X or D₀. -/
@[deprecated pair_perturbation (since := "2026-08-19")]
theorem pair_perturbation'
    {trG frobSqG trA frobSqA Btr BF : ℝ}
    (hBtr : 0 ≤ Btr) (hBF : 0 ≤ BF)
    (hfrA : 0 ≤ frobSqA) (hfrG : 0 ≤ frobSqG)
    (htr : |trG - trA| ≤ Btr)
    (hF : Real.sqrt frobSqA - Real.sqrt frobSqG ≤ BF) :
    4 * trG - frobSqG - (4 * Btr + 2 * BF * Real.sqrt frobSqG + BF ^ 2)
      ≤ 4 * trA - frobSqA :=
  pair_perturbation hBtr hBF hfrA hfrG htr hF

/-! ## 3.7 From per-block H1 to the family display

§3's display is [R]'s H1 aggregated over 𝔉_Q. The aggregation is: `tr` and `‖·‖²_F` add
(direct sum), `N` and `N_II` add, and the tail enters through the pair split of §7.3. -/

/-- `‖Ĝ_fam‖²_F ≥ 0` — the family Frobenius aggregate is a double sum of `RHLinalg.frobSq`
values, so its nonnegativity is free. This is the ingredient the bare-real
`pair_perturbation` has to take as a hypothesis and the family-level statement does not.
Rule 17: n/a. -/
theorem frobSqGhatFam_nonneg (P : ParamsQ) (F : Family) (Qn : ℕ) :
    0 ≤ frobSqGhatFam P F Qn := by
  unfold frobSqGhatFam familySum
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Zeta23.Assembly.frobSq_nonneg _

/-- **§3's family display from the per-block H1 and §7.3's pair aggregation.**

This is the obligation that would consume `Zeta23.Assembly.count_certificate_free`
(`Zeta23/WindowD.lean:183`) block by block — **NEVER
`Zeta23.Assembly.count_certificate`** (`Assembly/Certificate.lean:39`), whose `NII` is
definitionally at `D₀ = √T` (see the module header).

The hypothesis `hH1` is the *family-summed, fixed-(Q,T)* per-block display at the truncated
matrix `Â`, at the **free** buffer `P.D0`. `trAfam`/`frobSqAfam` are its two aggregated
moments, carried as free reals because the free-`D` truncated matrix does not exist in [R]'s
tree (`Zeta23.ZeroConfig.Az`, `Zeta23/Defs.lean:325`, is built on `ZIprime` = at `√T`).

Paper §3 + §7.3.
Depends on: `pair_perturbation`, `h1_block_free` (D28: **not** the deprecated
`h1_block_fixed_free`, whose `hrt` is unsatisfiable).
**Rule 17:** the buffer enters only as `NIIFamQ P F Qn = NIIFam F Qn P.T P.D0`, at the FREE
field `P.D0`; `hP : P.Valid` is `ZetaQ.ParamsQ.Valid`, which has `lam_pos`/`lam_lt_two` and
NO `lam_le_one`, and no hypothesis relates `P.XQ` to `P.T`.

**REPAIRED under decision D14** — `hpairF` had inherited `pair_perturbation`'s reversed
orientation and the statement was FALSE; it is now the paper's own direction and PROVED.
The record of why: §7.3 supplies `‖Â_fam‖_F ≤ ‖Ĝ_fam‖_F + B_F`, i.e.
`√frobSqAfam − √(frobSqGhatFam …) ≤ B_F`; what is written is the subtraction the other way
round, which bounds `frobSqAfam` from below and leaves the conclusion unreachable (take
`trAfam := trGhatFam P F Qn` and `frobSqAfam` arbitrarily large: every hypothesis holds and
the conclusion does not mention it, so a proof would give H1 unconditionally at `θ₀ = 0`).
`certificate_display_of_H1'` below survives as a deprecated alias. See `pair_perturbation`'s
docstring for the machine-checked failing instance of the underlying algebra. -/
theorem certificate_display_of_H1
    (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) (θ₀ : ℝ)
    (trAfam frobSqAfam : ℝ)
    (hfrA : 0 ≤ frobSqAfam)
    -- (a) H1 per block, at FIXED (Q,T) and at the FREE buffer D₀, summed over 𝔉_Q:
    (hH1 : 4 * trAfam - frobSqAfam - 2 * NfamQ P F Qn - 3 * NIIFamQ P F Qn
             ≤ N0sFamQ P F Qn)
    -- (b) §7.3: the tail is trace-additive and Frobenius-√-additive over the direct sum:
    (hpairTr : |trGhatFam P F Qn - trAfam| ≤ Btr P F Qn θ₀)
    (hpairF : Real.sqrt frobSqAfam - Real.sqrt (frobSqGhatFam P F Qn) ≤ BF P F Qn θ₀)
    (hBtr : 0 ≤ Btr P F Qn θ₀) (hBF : 0 ≤ BF P F Qn θ₀) :
    CertificateDisplay (N0sFamQ P F Qn) (NfamQ P F Qn) (NIIFamQ P F Qn)
      (trGhatFam P F Qn) (frobSqGhatFam P F Qn)
      (Btr P F Qn θ₀) (BF P F Qn θ₀) := by
  unfold CertificateDisplay
  have hpp := pair_perturbation hBtr hBF hfrA (frobSqGhatFam_nonneg P F Qn) hpairTr hpairF
  linarith


/-- **§3's family display from the per-block H1, in the paper's own orientation — PROVED.**

`certificate_display_of_H1` with its `hpairF` written the way §7.3 supplies it, namely the
Frobenius triangle inequality `‖Â_fam‖_F ≤ ‖Ĝ_fam‖_F + B_F` (: "the Frobenius
norm is √-additive, `‖Ê_fam‖_F ≤ √|𝔉|·θ₀/(aL) =: B_F`"). Everything else — the statement,
the other five hypotheses, the conclusion — is byte-identical.

The frozen `certificate_display_of_H1` has `√(frobSqGhatFam) − √frobSqAfam ≤ B_F`, i.e. the
subtraction the other way round; see `pair_perturbation`'s docstring for the machine-checked
failing instance. With that orientation the hypothesis bounds `frobSqAfam` from BELOW, and
the frozen statement is not provable: instantiating `trAfam := trGhatFam P F Qn` and
`frobSqAfam := M` for `M` large satisfies every hypothesis while the conclusion does not
mention `M`, so a proof would establish the H1 display unconditionally for every `ParamsQ`,
at `θ₀ = 0` (where `Btr = BF = 0`) — which is the whole of §§7 and 9, not an aggregation
step. **The defect is `hpairF`'s orientation and nothing else**, as this proof shows: with
the orientation fixed the obligation is `pair_perturbation'` plus `linarith`, and the second
repair `pair_perturbation` needs (`0 ≤ frobSqG`) is free here, by `frobSqGhatFam_nonneg`.

Paper §3 + §7.3.
Depends on: `pair_perturbation'`, `frobSqGhatFam_nonneg`.
**Rule 17:** unchanged from `certificate_display_of_H1` — the buffer enters only as
`NIIFamQ P F Qn = NIIFam F Qn P.T P.D0`, at the FREE field `P.D0`. -/
theorem certificate_display_of_H1'
    (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) (θ₀ : ℝ)
    (trAfam frobSqAfam : ℝ)
    (hfrA : 0 ≤ frobSqAfam)
    -- (a) H1 per block, at FIXED (Q,T) and at the FREE buffer D₀, summed over 𝔉_Q:
    (hH1 : 4 * trAfam - frobSqAfam - 2 * NfamQ P F Qn - 3 * NIIFamQ P F Qn
             ≤ N0sFamQ P F Qn)
    -- (b) §7.3: the tail is trace-additive and Frobenius-√-additive over the direct sum:
    (hpairTr : |trGhatFam P F Qn - trAfam| ≤ Btr P F Qn θ₀)
    (hpairF : Real.sqrt frobSqAfam - Real.sqrt (frobSqGhatFam P F Qn) ≤ BF P F Qn θ₀)
    (hBtr : 0 ≤ Btr P F Qn θ₀) (hBF : 0 ≤ BF P F Qn θ₀) :
    CertificateDisplay (N0sFamQ P F Qn) (NfamQ P F Qn) (NIIFamQ P F Qn)
      (trGhatFam P F Qn) (frobSqGhatFam P F Qn)
      (Btr P F Qn θ₀) (BF P F Qn θ₀) := by
  unfold CertificateDisplay
  have hpp := pair_perturbation' hBtr hBF hfrA (frobSqGhatFam_nonneg P F Qn) hpairTr hpairF
  linarith

/-- **⛔ DEPRECATED (decision D28) in favour of `h1_block_free`, whose conclusion is
identical and which carries NO rank–trace hypothesis. Do not instantiate this: `hrt` is
UNSATISFIABLE at the paper's designs.**

`hrt : 4 tr Â − ‖Â‖²_F ≤ 2·s₁(T,D)` is not merely stronger than anything §4 proves — it
cannot be met. At a configuration whose only zero in `I′(D)` is simple, on the line, and
sitting on the grid point `γ_ρ = τ₀ = T`, the matrix `Â(D) = (aL²)⁻¹ u uᵀ` is **rank one**,
so `‖Â(D)‖²_F = (tr Â(D))² = x²` exactly, with `x := tr Â(D)` the truncated fraction of the
Poisson mass, so `x → 1` by lem:poisson (the loss is the `L₅` ends row, `Θ(ℒ log ℒ/T)`).
There `hrt` reads `4x − x² ≤ 2`, i.e. `x ≤ 2 − √2 = 0.5858…`, which fails for every design
that captures more than 59 % of the mass — i.e. for every design. The honest bound, which is
what [R]'s engine gives and what `hatAzD_mult2` proves, is `4 tr Â − ‖Â‖²_F ≤ s₁ + 2N(I′)`,
tight (with equality as `x → 1`) at that same instance.

The declaration is TRUE and is kept, not deleted, so that anything citing it still resolves;
`h1_block_free` below supersedes it entirely (same conclusion, three lines from
`hatAzD_mult2'` + `Zeta23.Assembly.NIprimeD_eq` + `s1D_le`). Nothing in the tree cites this
at term level; the two `Depends on:` docstrings that named it now name `h1_block_free`.
Full write-up at `h1_block_free`.

**🚩 OPEN QUESTION Q2 (now CLOSED — see `h1_block_free`) — kept for the record.**

The per-block H1 display at a **fixed** `(Q, T)` and at the **free** buffer `D`. Phase 1's
`Zeta23.Assembly.count_certificate_free` (`WindowD.lean:183`) is the ε-filter form
(`∀ᶠ T in atTop` hypotheses, `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀` conclusion); paper §10.5 takes **no
ε-limit**, so §3 needs the fixed-parameter shape instead.

What Phase 1 *does* ship at free `D` is the window bookkeeping — `Zeta23.ZeroConfig.s1D`
(`WindowD.lean:65`), `Zeta23.Assembly.s1D_le` (`:150`), `s1D_add_s2D_le` (`:139`),
`card_ZIprimeD_le` (`:163`). Given the rank–trace/inertia step `hrt` on the truncated block,
the rest is exactly `s1D_le` plus `N0s ≤ N`. **The missing ingredient is `hrt` itself**: it
is the free-`D` analogue of [R]'s rank–trace inequality applied to `Zeta23.ZeroConfig.Az`,
and `Az` (`Zeta23/Defs.lean:325`) is built on `ZIprime`, i.e. **at `D₀ = √T`** — a Rule-17
smuggle. So `hrt` is taken as a hypothesis here and the free-`D` truncated matrix is
carried abstractly through its two hat-unit moments.

**This was flagged as a possible gap in the Phase-1
deliverable. There was none:** the free-`D` rank–trace step is proved outright below
(`hatAzD_mult2`), so `hrt` never had to be hypothesised — and, as recorded above, it could
not have been discharged in the shape frozen here.

Paper §3 (H1); [R] `Assembly/Certificate.lean`, `WindowD.lean:140–174`.
Depends on: `Zeta23.Assembly.s1D_le`, `Zeta23.ZeroConfig.N0s`.
Rule 17: `D` is a free real; `Zeta23.D0` does not occur. -/
theorem h1_block_fixed_free
    (Z : Zeta23.ZeroConfig) {T D trAhat frobSqAhat : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D)
    -- the rank–trace / inertia step on the TRUNCATED block at the free buffer `D`:
    (hrt : 4 * trAhat - frobSqAhat ≤ 2 * (Z.s1D T D : ℝ)) :
    4 * trAhat - frobSqAhat - 2 * (Z.N T (2 * T) : ℝ)
        - 3 * (Zeta23.Assembly.NIID Z T D : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) := by
  -- `s₁(D) ≤ N₀ˢ(T,2T) + N_II(D)` — Phase 1's free-buffer window bookkeeping.
  have hs1 : (Z.s1D T D : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) + (Zeta23.Assembly.NIID Z T D : ℝ) := by
    exact_mod_cast Zeta23.Assembly.s1D_le Z hT hD
  -- `N₀ˢ ≤ N` on the window — the trivial chain.
  have hchain := Z.trivial_chain T (2 * T)
  have hN0sN : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    exact_mod_cast hchain.1.trans (hchain.2.1.trans hchain.2.2.1)
  have hNnn : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hNIInn : (0 : ℝ) ≤ (Zeta23.Assembly.NIID Z T D : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## 3.8 OPEN QUESTION Q2, DISCHARGED — the free-buffer rank–trace / inertia bound

This section closes Q2. It mirrors [R]'s own zero-side rank–trace argument over
`Zeta23.ZeroConfig.ZIprimeD T D` (the window at a **free** buffer `D`, `WindowD.lean:45`) in
place of `ZIprime T` (the window at `D₀ = √T`), and applies it to Phase 1's free-buffer
truncated matrix `Zeta23.ZeroConfig.AzD` (`Zeta23/Tail/GevreyTail.lean:1423`).

**Nothing is added to `Zeta23/`.** The whole rank–trace development is already stated at the
abstract level — `Zeta23.ZeroSide.ZeroBlockData` (`ZeroSide.lean:161`) is generic in the
index type of the window, and `ZeroBlockData.mult_two` (`ZeroSide/Mult.lean:128`) is the
`c = 2` rank–trace/inertia inequality on that abstract data. What is `D₀ = √T`-specific in
[R] is only the *instantiation* section (`ZeroSide.lean:573–950`), which builds the block
data at `ZI Z T := 𝒵(I′(√T))`. The declarations below are that instantiation at a free `D`:
`ZID`/`blockDataD`/`pairRepsD`, the matrix bridge `AzD_eq_blockA`, the two counting bridges
`s1D_eq_mk`/`NIprimeD_eq_mk`, and the truncated Poisson bound
`sum_normSq_evalVecD_le`. Each is a line-for-line copy of its `√T` original with
`Z.ZIprime T` replaced by `Z.ZIprimeD T D`.

**Rule 17.** `D` is a free real throughout. `Zeta23.D0` and `Zeta23.ZeroConfig.Az` occur
nowhere below, and no cited lemma mentions either: `ZeroBlockData.mult_two`,
`ZeroSide.card_filter_coe`, `ZeroSide.phiHatConj/phiHatReal/poissonSq/aLsq_pos/hat_eq`,
`Zeta23.Assembly.s1D_le` and `Zeta23.Assembly.NIprimeD_eq` are all either abstract or
already free-`D`. `Zeta23.Params.ValidQ` is the `lam_le_one`-free class (`Defs.lean:218`);
`8w ≤ L` is [R]'s `[eq:wrange]`, which is §10.3's `SideCondWrange`, not a bandwidth cap. -/

section FreeBufferBlock

open Matrix Finset RHLinalg Classical
open Zeta23 (reflect gammaOf)
open scoped ComplexOrder

variable (Z : Zeta23.ZeroConfig) (T D : ℝ)

/-- `𝒵(I′(D))` is finite (local finiteness of the configuration in the ordinate). -/
lemma ZIprimeD_finite : (Z.ZIprimeD T D).Finite := Z.finite_window _ _

/-- `𝒵(I′(D))` as a `Finset` — the index type of the free-buffer block data.
Mirror of `Zeta23.ZeroSide.ZI` (`ZeroSide.lean:582`) at a free `D`. -/
def ZID : Finset ℂ := (ZIprimeD_finite Z T D).toFinset

lemma mem_ZID {ρ : ℂ} : ρ ∈ ZID Z T D ↔ ρ ∈ Z.ZIprimeD T D := Set.Finite.mem_toFinset _

lemma coe_ZID : ((ZID Z T D : Finset ℂ) : Set ℂ) = Z.ZIprimeD T D := Set.Finite.coe_toFinset _

/-- Membership in `𝒵(I′(D))` unfolded. Mirror of `ZeroSide.mem_ZIprime_iff`; note the window
is `(T − D, 2T + D]` at the FREE `D`, never at `√T`. -/
lemma mem_ZIprimeD_iff {ρ : ℂ} :
    ρ ∈ Z.ZIprimeD T D ↔ ρ ∈ Z.carrier ∧ T - D < ρ.im ∧ ρ.im ≤ 2 * T + D := by
  simp [Zeta23.ZeroConfig.ZIprimeD, Zeta23.ZeroConfig.window]

lemma mem_carrier_of_mem_ZID {ρ : ℂ} (h : ρ ∈ ZID Z T D) : ρ ∈ Z.carrier :=
  ((mem_ZIprimeD_iff Z T D).mp ((mem_ZID Z T D).mp h)).1

/-- `ρ ↦ 1 − ρ̄` preserves `𝒵(I′(D))` (it preserves the ordinate, and the carrier is
reflection-invariant). Mirror of `ZeroSide.reflect_mem_ZI`. -/
lemma reflect_mem_ZID {ρ : ℂ} (h : ρ ∈ ZID Z T D) : reflect ρ ∈ ZID Z T D := by
  rw [mem_ZID, mem_ZIprimeD_iff] at h ⊢
  exact ⟨Z.reflect_mem ρ h.1, by rw [Zeta23.ZeroSide.reflect_im]; exact h.2⟩

variable (P : Zeta23.Params)

/-- The evaluation vectors `u_ρ := (φ̂(γ_ρ − τ_k))_{0 ≤ k < d}` on `𝒵(I′(D))`.
Mirror of `Zeta23.ZeroSide.evalVec` (`ZeroSide.lean:808`). -/
def evalVecD : ZID Z T D → Fin (P.d T) → ℂ :=
  fun z k => P.phiHat T (gammaOf z - P.tau T k)

/-- `u_{1−ρ̄} = conj u_ρ` (from `γ_{1−ρ̄} = conj γ_ρ`, `τ_k ∈ ℝ` and `φ̂(conj w) = conj φ̂(w)`).
Mirror of `ZeroSide.evalVec_reflect`, with `hconj` discharged by `ZeroSide.phiHatConj`. -/
lemma evalVecD_reflect :
    ∀ z : ZID Z T D, evalVecD Z T D P ⟨reflect z, reflect_mem_ZID Z T D z.2⟩
      = star (evalVecD Z T D P z) := by
  intro z
  funext k
  simp only [evalVecD, Pi.star_apply, RCLike.star_def]
  rw [Zeta23.ZeroSide.gammaOf_reflect, ← Zeta23.ZeroSide.phiHatConj (T := T) (P := P),
    map_sub, Complex.conj_ofReal]

/-- **The §4 block data of `𝒵(I′(D))` at a FREE buffer** — the object [R] builds only at
`D₀ = √T` (`Zeta23.ZeroSide.blockData`, `ZeroSide.lean:823`). Multiplicities `m := Z.mult`,
evaluation vectors `u_ρ`, involution `σ := (ρ ↦ 1 − ρ̄)`. -/
def blockDataD : Zeta23.ZeroSide.ZeroBlockData (ZID Z T D) (Fin (P.d T)) where
  m z := Z.mult z
  one_le_m z := Z.one_le_mult _ (mem_carrier_of_mem_ZID Z T D z.2)
  v := evalVecD Z T D P
  σ z := ⟨reflect z, reflect_mem_ZID Z T D z.2⟩
  σ_invol _ := Subtype.ext (Zeta23.ZeroSide.reflect_reflect _)
  m_σ z := Z.mult_reflect _ (mem_carrier_of_mem_ZID Z T D z.2)
  v_σ := evalVecD_reflect Z T D P

@[simp] lemma blockDataD_m (z : ZID Z T D) : (blockDataD Z T D P).m z = Z.mult z := rfl

@[simp] lemma blockDataD_v : (blockDataD Z T D P).v = evalVecD Z T D P := rfl

@[simp] lemma blockDataD_σ (z : ZID Z T D) :
    (((blockDataD Z T D P).σ z : ZID Z T D) : ℂ) = reflect z := rfl

/-- Fixed points of `σ` are exactly the on-line points (`β = 1/2`). -/
lemma blockDataD_σ_eq_iff (z : ZID Z T D) :
    (blockDataD Z T D P).σ z = z ↔ (z : ℂ).re = 1 / 2 := by
  rw [Subtype.ext_iff, blockDataD_σ, Zeta23.ZeroSide.reflect_eq_self_iff]

/-- Canonical representatives of the off-line pairs `{ρ, 1−ρ̄}` of `𝒵(I′(D))`: the member with
`β > 1/2`. Mirror of `Zeta23.ZeroSide.mkPairReps` (`ZeroSide.lean:656`). -/
def pairRepsD : (blockDataD Z T D P).PairReps where
  R := {z | 1 / 2 < (z : ℂ).re}
  off z hz h := by
    rw [blockDataD_σ_eq_iff] at h
    simp only [mem_filter, mem_univ, true_and] at hz
    linarith
  σ_not_mem z hz h := by
    simp only [mem_filter, mem_univ, true_and, blockDataD_σ, Zeta23.ZeroSide.reflect_re] at hz h
    linarith
  cover z hz := by
    rw [ne_eq, blockDataD_σ_eq_iff] at hz
    simp only [mem_filter, mem_univ, true_and, blockDataD_σ, Zeta23.ZeroSide.reflect_re]
    rcases lt_or_gt_of_ne hz with h | h
    · right; linarith
    · left; exact h

/-- **The matrix bridge:** Phase 1's free-buffer truncated matrix
`Zeta23.ZeroConfig.AzD` (`Zeta23/Tail/GevreyTail.lean:1423`) IS the abstract `blockA` of the
free-buffer block data, i.e. `A(D) = Σ_{ρ ∈ 𝒵(I′(D))} m_ρ u_ρ u_ρᵀ`.
Mirror of `Zeta23.ZeroSide.Az_eq_blockA` (`ZeroSide.lean:827`). -/
theorem AzD_eq_blockA : Z.AzD P T D = (blockDataD Z T D P).blockA := by
  ext k l
  rw [Zeta23.ZeroSide.ZeroBlockData.blockA_apply]
  change ∑ᶠ ρ ∈ Z.ZIprimeD T D, Z.Gsummand P T k l ρ = _
  rw [finsum_mem_eq_finite_toFinset_sum _ (ZIprimeD_finite Z T D), ← Finset.sum_coe_sort]
  refine sum_congr rfl fun z _ => ?_
  simp only [Zeta23.ZeroConfig.Gsummand, blockDataD, evalVecD]
  ring

/-- `𝒮₁(D)` as a `Finset` filter. Mirror of `Zeta23.ZeroSide.S1_eq`. -/
lemma S1D_eq :
    Z.S1D T D = ↑((ZID Z T D).filter (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)) := by
  ext ρ
  simp only [Zeta23.ZeroConfig.S1D, Zeta23.ZeroConfig.onLine, Zeta23.ZeroConfig.simple,
    Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_filter, mem_ZID]
  tauto

/-- **Counting bridge 1:** Phase 1's `Zeta23.ZeroConfig.s1D` (`WindowD.lean:65`) is the
abstract `s₁` of the free-buffer block data. Mirror of `ZeroSide.s1_eq_mk`. -/
lemma s1D_eq_mk : Z.s1D T D = (blockDataD Z T D P).s₁ := by
  rw [Zeta23.ZeroConfig.s1D, S1D_eq, Set.ncard_coe_finset,
    Zeta23.ZeroSide.ZeroBlockData.s₁, Zeta23.ZeroSide.ZeroBlockData.S₁]
  convert (Zeta23.ZeroSide.card_filter_coe (ZID Z T D)
    (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)
    (fun z => (blockDataD Z T D P).σ z = z ∧ (blockDataD Z T D P).m z = 1)
    fun z => by rw [blockDataD_σ_eq_iff]; rfl).symm using 2
  all_goals
    first
      | exact Finset.filter_congr_decidable _ _ _
      | exact (Finset.filter_congr_decidable _ _ _).symm

/-- **Counting bridge 2:** `N(I′(D))` (`WindowD.lean:80`) is the abstract `Ncount`.
Mirror of `ZeroSide.NIprime_eq_mk`. -/
lemma NIprimeD_eq_mk : Z.NIprimeD T D = (blockDataD Z T D P).Ncount := by
  rw [Zeta23.ZeroConfig.NIprimeD, Zeta23.ZeroConfig.N,
    Zeta23.ZeroSide.ZeroBlockData.Ncount]
  change ∑ᶠ ρ ∈ Z.ZIprimeD T D, Z.mult ρ = _
  rw [finsum_mem_eq_finite_toFinset_sum _ (ZIprimeD_finite Z T D), ← Finset.sum_coe_sort]
  rfl

/-- The truncated Poisson bound at an on-line zero of `𝒵(I′(D))`:
`Σ_{0 ≤ k < d} |φ̂(γ_ρ − τ_k)|² ≤ aL²`, the finite partial sum of the nonnegative series whose
full sum over `k ∈ ℤ` is exactly `aL²` (lem:poisson). Mirror of
`Zeta23.ZeroSide.sum_normSq_v_le` (`ZeroSide.lean:909`). -/
lemma sum_normSq_evalVecD_le (hPois : Zeta23.ZeroSide.PoissonSq T P)
    (z : ZID Z T D) (hz : z ∈ (blockDataD Z T D P).onLine) :
    ∑ k, ‖(blockDataD Z T D P).v z k‖ ^ 2 ≤ P.a T * P.L T ^ 2 := by
  rw [Zeta23.ZeroSide.ZeroBlockData.mem_onLine] at hz
  have hz' : (z : ℂ).re = 1 / 2 := (blockDataD_σ_eq_iff Z T D P z).mp hz
  have hv : ∀ k : Fin (P.d T), ‖(blockDataD Z T D P).v z k‖ ^ 2
      = P.phiHatR T ((z : ℂ).im - P.tau T k) ^ 2 := by
    intro k
    simp only [blockDataD_v, evalVecD]
    rw [Zeta23.ZeroSide.gammaOf_of_re_eq_half hz', ← Complex.ofReal_sub,
      Zeta23.ZeroSide.phiHatReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hv]
  let e : Fin (P.d T) ↪ ℤ := ⟨fun k => ((k : ℕ) : ℤ), fun a b h => Fin.ext (by
    have h' : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := h
    exact_mod_cast h')⟩
  have := sum_le_hasSum (Finset.univ.map e) (fun i _ => sq_nonneg _) (hPois (z : ℂ).im)
  rwa [sum_map] at this

/-- **🟢 OPEN QUESTION Q2, THE MISSING INGREDIENT — the free-buffer rank–trace / inertia
bound. PROVED.**

  `4 tr Â(D) − ‖Â(D)‖²_F − 2·N(I′(D)) ≤ s₁(T, D)`

on the truncated block `Â(D) := Zeta23.ZeroConfig.AzD` in hat units, at a **free** buffer
`D`. This is [R]'s `Zeta23.ZeroSide.hatAz_mult2` (`ZeroSide/Mult.lean:185`, the `c = 2`
multiplicity-aware rank–trace step, `lem:ranktrace` + `prop:block`) with `𝒵(I′(√T))`
replaced by `𝒵(I′(D))` everywhere. The abstract engine `ZeroBlockData.mult_two` is reused
verbatim; only the instantiation is new, and it is the block above.

`hc : 0 < aL²` and `hPois` (lem:poisson) are the two analytic side conditions of [R]'s own
version; `hatAzD_mult2'` discharges them from the standing assumptions.

Paper §3 (H1) / §4 (`prop:block`, `prop:zeroside-rank`); [R] `ZeroSide/Mult.lean:128,185`.
**Rule 17: CLEAN — `D` is free; `Zeta23.D0` and `ZeroConfig.Az` occur nowhere.** -/
theorem hatAzD_mult2 (hc : 0 < P.a T * P.L T ^ 2)
    (hPois : Zeta23.ZeroSide.PoissonSq T P) :
    4 * rtrace (P.hat T (Z.AzD P T D)) - frobSq (P.hat T (Z.AzD P T D))
        - 2 * (Z.NIprimeD T D : ℝ)
      ≤ (Z.s1D T D : ℝ) := by
  have hsplit : P.hat T (Z.AzD P T D)
      = (blockDataD Z T D P).blockP (P.a T * P.L T ^ 2)
        + (blockDataD Z T D P).blockQ (P.a T * P.L T ^ 2) := by
    rw [Zeta23.ZeroSide.ZeroBlockData.blockP_add_blockQ, Zeta23.ZeroSide.hat_eq,
      AzD_eq_blockA]
  rw [hsplit, NIprimeD_eq_mk Z T D P, s1D_eq_mk Z T D P]
  exact Zeta23.ZeroSide.ZeroBlockData.mult_two _ (pairRepsD Z T D P) hc
    (sum_normSq_evalVecD_le Z T D P hPois)

/-- `hatAzD_mult2` with the two analytic side conditions discharged from the standing
assumptions, exactly as [R]'s `ZeroSide.blockInputs_of_hwL` (`ZeroSide/Final.lean:46`) does:
`P.ValidQ` (the `lam_le_one`-FREE class) plus `[eq:wrange]`'s `8w ≤ L`, which is §10.3's
`SideCondWrange`. **Rule 17: neither hypothesis is λ ≤ 1, X ≤ T or D₀ = √T.** -/
theorem hatAzD_mult2' (hP : P.ValidQ) (hwL : 8 * P.w ≤ P.L T) :
    4 * rtrace (P.hat T (Z.AzD P T D)) - frobSq (P.hat T (Z.AzD P T D))
        - 2 * (Z.NIprimeD T D : ℝ)
      ≤ (Z.s1D T D : ℝ) :=
  hatAzD_mult2 Z T D P (Zeta23.ZeroSide.aLsq_pos hP hwL) (Zeta23.ZeroSide.poissonSq hP hwL)

/-- **🟢 `h1_block_fixed_free` IN HYPOTHESIS-FREE FORM — the per-block H1 display at a fixed
`(Q, T)` and a FREE buffer `D`, with no rank–trace hypothesis. PROVED.**

The conclusion is `h1_block_fixed_free`'s, with the two abstract moments instantiated at the
free-buffer truncated matrix `Â(D) = P.hat T (Z.AzD P T D)`:

  `4 tr Â(D) − ‖Â(D)‖²_F − 2 N(T,2T) − 3 N_{II}(T,D) ≤ N₀ˢ(T,2T)`.

Proof: `hatAzD_mult2'` (the free-`D` rank–trace bound) plus the two pieces of Phase 1's
free-buffer window bookkeeping — `Zeta23.Assembly.NIprimeD_eq` (`WindowD.lean:107`,
`N(I′(D)) = N(T,2T) + N_{II}(D)`) and `Zeta23.Assembly.s1D_le` (`WindowD.lean:151`,
`s₁(D) ≤ N₀ˢ(T,2T) + N_{II}(D)`). Three lines. **This is the whole of Q2.**

### 🚩 FINDING — the frozen hypothesis `hrt` of `h1_block_fixed_free` is MIS-TRANSCRIBED

`h1_block_fixed_free` carries `hrt : 4 tr Â − ‖Â‖²_F ≤ 2·s₁(T,D)`. That is **not** the
rank–trace inequality, and it is **strictly stronger than anything §4 proves**. [R]'s
rank–trace step (`lem:ranktrace` at `c = 2`, via `ZeroBlockData.mult_two`) delivers

  `4 tr Â − ‖Â‖²_F ≤ s₁ + 2·N(I′)`,

and since `N(I′) ≥ s₁ + 2s₂ + 2p ≥ s₁` (that is `[eq:Ncount]`, and it is consumed inside
`mult_two`'s own proof) the bound `s₁ + 2N(I′)` is never smaller than `3s₁`; it cannot be
sharpened to `2s₁`. The `−2N(I′)` term is not a slack that can be dropped: it is what pays
for the `p` hyperbolic blocks and the multiple on-line zeros.

*Failing instance for `hrt` itself.* Take a configuration whose only zero in `I′(D)` is
simple, on the line, and sitting at a grid point, `γ_ρ = τ_0 = T`. Then `s₁(T,D) = 1`,
`m_ρ = 1`, and `Â(D) = (aL²)⁻¹ u u^T` with `u_k = φ̂(kh)`, so with
`x := tr Â(D) = (aL²)⁻¹ Σ_{0 ≤ k < d} φ̂(kh)²` one has `‖Â(D)‖²_F = x²` exactly (a rank-one
matrix), and lem:poisson makes `x` the truncated fraction of the full Poisson mass, i.e.
`x → 1`. `hrt` then reads `4x − x² ≤ 2`, i.e. `x ≤ 2 − √2 = 0.5858…`, which **fails** for
every design in which the grid captures more than 59% of the Poisson mass — which is every
design, since the truncation loss is the `L₅` ends row, `Θ(ℒ log ℒ / T)`. The honest bound
at the same instance reads `4x − x² − 2·1 ≤ 1`, which holds with equality in the limit
`x → 1`: the `−2N(I′)` term is exactly what makes the inequality tight.

**Nothing is lost.** `h1_block_fixed_free`'s *conclusion* — the display §3 needs — follows
from the honest bound with room to spare (`s₁(D) − N_{II}(D) ≤ N₀ˢ`, versus `hrt`'s route
`2N₀ˢ − 2N − N_{II} ≤ N₀ˢ`), which is what this theorem proves. `h1_block_fixed_free` is
therefore left exactly as frozen — it is true, and now redundant — and this declaration is
the form §10.5 should consume.

Paper §3 (H1); [R] `ZeroSide/Mult.lean:185`, `WindowD.lean:107,151`.
**Rule 17: CLEAN** — `D` free, `Zeta23.D0` absent, `P.ValidQ` has no
`lam_le_one`, and `8w ≤ L` is `[eq:wrange]`. -/
theorem h1_block_free (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hP : P.ValidQ) (hwL : 8 * P.w ≤ P.L T) :
    4 * rtrace (P.hat T (Z.AzD P T D)) - frobSq (P.hat T (Z.AzD P T D))
        - 2 * (Z.N T (2 * T) : ℝ) - 3 * (Zeta23.Assembly.NIID Z T D : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hrt := hatAzD_mult2' Z T D P hP hwL
  have hNI : (Z.NIprimeD T D : ℝ)
      = (Z.N T (2 * T) : ℝ) + (Zeta23.Assembly.NIID Z T D : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Zeta23.Assembly.NIprimeD_eq Z hT hD)
  have hs1 : (Z.s1D T D : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) + (Zeta23.Assembly.NIID Z T D : ℝ) := by
    exact_mod_cast Zeta23.Assembly.s1D_le Z hT hD
  rw [hNI] at hrt
  linarith

/-- **`h1_block_free` with its two analytic inputs taken DIRECTLY** — `aL² > 0`
and lem:poisson's `PoissonSq` — in place of `P.ValidQ`, so that it applies to the
profile-weighted design window (for which `P.toParams.ValidQ` is FALSE: the realising profile is
not a `TaperProfile`). `ZetaQ/Window.lean` supplies both inputs from `ParamsQ.Valid`
(`Valid.aLsq_pos`, `Valid.poissonSq`); `EFChi.h1_fam` consumes this form. Same conclusion, same
proof. Rule 17: CLEAN — no validity class at all. -/
theorem h1_block_free_of_poisson (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hc : 0 < P.a T * P.L T ^ 2) (hPois : Zeta23.ZeroSide.PoissonSq T P) :
    4 * rtrace (P.hat T (Z.AzD P T D)) - frobSq (P.hat T (Z.AzD P T D))
        - 2 * (Z.N T (2 * T) : ℝ) - 3 * (Zeta23.Assembly.NIID Z T D : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) := by
  have hrt := hatAzD_mult2 Z T D P hc hPois
  have hNI : (Z.NIprimeD T D : ℝ)
      = (Z.N T (2 * T) : ℝ) + (Zeta23.Assembly.NIID Z T D : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Zeta23.Assembly.NIprimeD_eq Z hT hD)
  have hs1 : (Z.s1D T D : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) + (Zeta23.Assembly.NIID Z T D : ℝ) := by
    exact_mod_cast Zeta23.Assembly.s1D_le Z hT hD
  rw [hNI] at hrt
  linarith

-- **Decision D28** — `h1_block_fixed_free` is retired in favour of `h1_block_free`.  The
-- attribute is attached here rather than at the declaration because `h1_block_free`, the
-- replacement, only comes into scope at this point.  See `h1_block_fixed_free`'s docstring
-- for the unsatisfiability of its `hrt` (rank-one `Â(D)` at a single on-line grid-point zero
-- forces `x ≤ 2 − √2`, against `x → 1`).
attribute [deprecated h1_block_free (since := "2026-08-19")] h1_block_fixed_free

end FreeBufferBlock

/-- The `NIIf`-instantiation Phase 2 is entitled to make, recorded so the mirror does not
drift: `count_certificate_free`'s free buffer parameter is instantiated at
`NIIf T := (Zeta23.Assembly.NIID Z T (D T) : ℝ)` for the design's buffer profile `D`, never
at `NIIf T := (Zeta23.Assembly.NII Z T : ℝ)`.

Stated as a definitional identity so that a later fill can `rfl`-bridge the two layers.
Paper §7, §10.3.
**Rule 17: this declaration IS the Rule-17 boundary of the file.** -/
theorem NIIfree_eq (Z : Zeta23.ZeroConfig) (T D : ℝ) :
    (Zeta23.Assembly.NIID Z T D : ℝ)
      = ((Z.N (T - D) T : ℝ) + (Z.N (2 * T) (2 * T + D) : ℝ)) := by
  unfold Zeta23.Assembly.NIID
  push_cast
  ring

end ZetaQ
