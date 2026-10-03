/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/EFChi.lean — paper §9 (the archimedean and explicit-formula layer, uniformly in q)
TOGETHER WITH paper §2.1's H1–H6 import surface.

Imports `ZetaQ.Defs` **and `ZetaQ.Certificate`** — the second edge was
added by the §9 → §3 family join of PART C below, after checking acyclicity: `ZetaQ.Certificate`
imports only `ZetaQ.Defs` and `ZetaQ.Window`, neither of which reaches this file.
(⚠ The clause "and no module imports `ZetaQ.EFChi`" that stood here is STALE:
`ZetaQ/Budget.lean` imports it. Acyclicity is unaffected — `Budget` is above `EFChi` in the
graph.) Precedents for
adding an intra-ZetaQ edge for a genuine join: D26 (`Ends → Normalisation`), D29
(`Zones → Normalisation`). See PART C's header for the full check.

Statement source of truth: paper §2.1 and §9. PART A below is the H1–H6 import map, with the
verbatim [R] signature and the citation strategy for each; PART B is §9's own statements;
PART C is the λ ≤ 1 audit cross-check.

## What this file is for

Paper §2.1 isolates six statements imported from [R]. This file NAMES them at ZetaQ's parameters,
so that the rest of ZetaQ cites `ZetaQ.H3_positivity` rather than reaching into `Zeta23.*` ad hoc.
Five of the six are re-exports with a real proof; only H1 is a mirror.

**PART C (added, sorry-free) is the §9 → §3 FAMILY JOIN** — the one obligation
`ZetaQ.assembly_at_lamStar`'s checklist calls item 3, which both that statement's own
docstring and `ZetaQ/Certificate.lean` §3.8 locate in THIS file. It carries the per-block H1 display
`ZetaQ.h1_block_free` over `𝔉_Q` and identifies §3's prime-side `ZetaQ.gridGram` aggregates with
the zero-side blocks through H2 (`H2_Gz_eq_GpChi`), producing `ZetaQ.CertificateDisplay` at
`trGhatFam`/`frobSqGhatFam`/`NfamQ`/`N0sFamQ`/`NIIFamQ`. The export is
`ZetaQ.EFChi.certificate_display_fam_of_bridge`; `prop31_fam` composes it with §10.3's four rows
to give `assembly_at_lamStar`'s last conclusion clause. The ONLY input PART C does not prove is
§7's pair split (`hpairTr`/`hpairF`), which is `ZetaQ/Tail.lean`'s.

* **H2–H5 are citable.** They are FIXED-T statements — `T` is an
  explicit argument, not a filter variable — so instantiating [R]'s record at
  `lam := λℒ / l T` makes its derived `L` equal the paper's `L = λℒ` on the nose. That is exactly
  what `ParamsQ.toParams` does, and `ParamsQ.toParams_L` / `toParams_X` are the bridge equations.
  The reparameterised `lam` is LARGE (≈ 24 at Q = 10¹⁰⁰); nobody may "simplify" it to `P.lam`.
* **H1 needs a mirror.** `Zeta23.Assembly.count_certificate_free` (`WindowD.lean:183`) quantifies
  `∀ᶠ T in atTop` with `P : Params` fixed OUTSIDE the filter, and the paper's asymptotic variable
  is `Q` with `L = λℒ(Q,T)` — not of the form `lam · l T` for a T-constant `lam`. R-1 is
  unavailable; the mirror is mechanical (the [R] proof touches `P` only through `P.hat`, `P.a`,
  `P.L`, `Z.Gz` as opaque symbols).

## RULE 17 — three flags, all honoured here

1. **Only the cap-free `_L` ends majorants are cited** (`calE1_maj_bound_L`, `EndsE1.lean:727`;
   `calE2_maj_bound_L`, `EndsE2.lean:353`). Their capped siblings `calE1_maj_bound`
   (`EndsE1.lean:616`) and `calE2_maj_bound` (`EndsE2.lean:266`) carry `p.L ≤ 2 * p.l`, which is
   the bandwidth cap in T-aspect disguise (there `L = λl`) and is FALSE here by a factor 10–60
   (paper §8.2). They are never mentioned below except as a warning.
2. **`Zeta23.Tail.NII_le` (`Tail.lean:595`) is NEVER cited.** It concludes `≤ 3A₀·√T·log 4T`,
   i.e. it has `D₀ = √T` baked in. The buffer chain here goes through
   `Zeta23.Tail.NIID_le` (`Tail/GevreyTail.lean:1878`), where `D` is a free real, and
   `Zeta23.D0` (`Zeta23/Defs.lean:61`, `:= Real.sqrt T`) is not reintroduced anywhere.
3. **H3's anchor is at `Zeta23/ThmD/WindowCore.lean:387`**, not `:386`, which is the
   docstring line above it.

No declaration below has a hypothesis asserting `λ ≤ 1`, `X ≤ T`, or `D₀ = √T`. The buffer regime
that IS assumed — `2 ≤ D₀` and `D₀ + 4 ≤ T`, threaded from `ParamsQ.Valid.two_le_D0` /
`Valid.D0_le` — is the honest regime `Zeta23.Tail.NIID_le` needs (it needs BOTH), and is satisfied
by the design of record and by the reference design `D₀ = ℒ² log ℒ`.

## PART C findings recorded here

* **(D1) §9's prose understates the tree.** Paper §9 asks for "LocalCountChi/MainTermChi re-runs
  with explicit constants", parenthesising only the local count as already uniform. In fact
  `Zeta23.ThmE.mainChi_uniform_aux` (`ThmE/MainTermChi.lean:260`) already delivers the RvM-χ MAIN
  TERM with absolute constants `A`, `T₀`, uniformly in q and χ, and BOTH of its hypotheses are
  proved q-uniform theorems in the same tree (`backlund_horizontalChi_uniform`,
  `ReZeroCountChi.lean:283`; `GammaChi.gammaFactsChi_uniform`, `GammaFactsChiProof.lean:380`).
  [R] composes them at `MainTermChi.lean:517` but only to DEGRADE to the per-χ `mainChi`, so the
  uniform composite has no top-level name there. §9 therefore owes a NAMING lemma, not a re-run:
  `ZetaQ.EFChi.rvmChi_main_uniform` below is a one-line `:=` with no sorry.
* **(D2) §2.1/§9's "LIVE obligation" language is stale.** Both sections still describe the ParamsQ
  re-parameterisation as an open risk ("until the ParamsQ re-parameterisation compiles"). Phase 1
  discharged it: `Params.ValidQ` exists (`Zeta23/Defs.lean:204`, `lam_le_one` dropped, `one_le_w`
  kept, `lam_lt_two` added), the reused modules were re-hypothesised to it, the free buffer was
  delivered structurally (`WindowD.lean`) and analytically (`Tail/GevreyTail.lean`), and the build
  is green and sorry-free at [R]'s own axiom profile. One residue survives and §9 should keep
  saying so: Phase 1 did NOT produce ZetaQ's own parameter class (ℒ = log(QT/2π), L = λℒ) — that
  is Phase-2 work, and it is precisely why H1 below is a mirror rather than a citation.

## Live sub-finding carried from H5 (it belongs to §8, NOT to §9)

`calE2_maj_bound_L` carries `p.L ≤ B`. At the paper's instantiation `B := ℒ + C₀` (C₀ = 6) that
reads `λ*ℒ ≤ ℒ + 6`, i.e. `ℒ ≲ 23.9` — FALSE at every headline scale. The repair is free
(`NuBound` is monotone in `B`: enlarge to `B := λ*ℒ`) but inflates the displayed 𝓔₂ family
constant by ≈ 1.48 at ℒ = 230. Recorded because the hypothesis is visible only in the verbatim
signature re-exported below.
-/
import ZetaQ.Defs
import ZetaQ.Certificate

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Topology Asymptotics

namespace ZetaQ

/-! # PART A — the H1–H6 import surface (paper §2.1)

Five of the six are proved re-exports. `H1_count_certificate_Q` is the single mirror. -/

/-! ## A.0 A bridge abbreviation used only by H1

`ZetaQ.GzQ` / `ZetaQ.hatQ` are owned by `ZetaQ/Certificate.lean` (§3), and
§9's file must not define them. The abbreviation below is deliberately given a name that cannot
collide with those; §3's own objects are `ZetaQ.gridGram` and `ZetaQ.hatQ`. -/

/-- `Ĝ = G/(aL²)` on the zero side, at ZetaQ's design point, through the `toParams` bridge.

Paper §3 (the hat normalisation `Ĝ := G/(aL²)`).
Depends on: `ParamsQ.toParams`.
Rule 17: contains no hypothesis at all; `P.toParams` is the R-1 instantiation, whose `lam` is
`λℒ / l T` and is NOT `P.lam`. NOT a replacement for §3's own `ZetaQ.gridGram`/`hatQ`. -/
def hatGzBridge (Z : Zeta23.ZeroConfig) (P : ParamsQ) :
    Matrix (Fin (P.toParams.d P.T)) (Fin (P.toParams.d P.T)) ℂ :=
  P.toParams.hat P.T (Z.Gz P.toParams P.T)

/-! ## A.1 H1 — the rank–trace certificate (MIRROR) -/

/-- **H1** (the rank–trace certificate, at the paper's asymptotic variable `Q`). Along a family of
design points `PQ : ℝ → ParamsQ` and zero configurations `Zc : ℝ → ZeroConfig` indexed by `Q`, the
moment inequality `#{simple, on-line} ≥ 4 tr Ĝ − ‖Ĝ‖²_F − 2𝒩 − 3N_II − (perturbation loss)`
upgrades to `(2 − κ − ε)·𝒩 ≤ lower` for every `ε > 0` and all large `Q`.

Paper §2.1 (H1) and §3 (the display in full, with the family split
`− [4B_tr + 2B_F‖Ĝ_fam‖_F + B_F²]`).
Depends on: template `Zeta23.Assembly.count_certificate_free` (`Zeta23/WindowD.lean:183`);
moment algebra `Zeta23.Assembly.N0star_lower_moment` (`Assembly/Certificate.lean:24`); perturbation
step `Zeta23.Assembly.four_tr_sub_frobSq_perturb` (`Assembly.lean:150`).
Why a mirror and not a citation: `count_certificate*` is the only H-anchor quantified
`∀ᶠ T in atTop` with `P : Params` fixed OUTSIDE the filter. The paper's asymptotic variable is `Q`
and its `L = λℒ(Q,T)` is not `lam · l T` for T-constant `lam`, so R-1's pointwise-λ trick does not
apply. The [R] proof body never touches `P` beyond `P.hat`, `P.a`, `P.L`, `Z.Gz` as opaque
symbols, so the transcription is mechanical.
Rule 17: CLEAN. No `Params.Valid` or `ValidQ` argument anywhere (the anchor takes a bare
`P : Params`); the buffer enters only through the ABSTRACT `NIIf`, which is what removed the last
`Zeta23.D0` from the anchor's kernel closure. No λ ≤ 1, no X ≤ T, no D₀ = √T. -/
theorem H1_count_certificate_Q
    (Zc : ℝ → Zeta23.ZeroConfig) (PQ : ℝ → ParamsQ) (κ : ℝ) (lower θ₀ NIIf : ℝ → ℝ)
    (h0 : ∀ᶠ Q in atTop,
      4 * RHLinalg.rtrace (hatGzBridge (Zc Q) (PQ Q))
          - RHLinalg.frobSq (hatGzBridge (Zc Q) (PQ Q))
          - 2 * ((Zc Q).N (PQ Q).T (2 * (PQ Q).T) : ℝ) - 3 * NIIf Q
          - θ₀ Q / ((PQ Q).aQ * (PQ Q).LB)
              * (4 + 2 * Real.sqrt (RHLinalg.frobSq (hatGzBridge (Zc Q) (PQ Q)))
                  + θ₀ Q / ((PQ Q).aQ * (PQ Q).LB))
        ≤ lower Q)
    (hB0 : ∀ᶠ Q in atTop, 0 ≤ θ₀ Q / ((PQ Q).aQ * (PQ Q).LB))
    (hBto : Tendsto (fun Q => θ₀ Q / ((PQ Q).aQ * (PQ Q).LB)) atTop (𝓝 0))
    (hNII_o : NIIf =o[atTop] (fun Q => ((Zc Q).N (PQ Q).T (2 * (PQ Q).T) : ℝ)))
    (hNtop : Tendsto (fun Q => ((Zc Q).N (PQ Q).T (2 * (PQ Q).T) : ℝ)) atTop atTop)
    (htrace : ∀ δ > (0 : ℝ), ∀ᶠ Q in atTop,
      (1 - δ) * ((Zc Q).N (PQ Q).T (2 * (PQ Q).T) : ℝ)
        ≤ RHLinalg.rtrace (hatGzBridge (Zc Q) (PQ Q)))
    (hfrob : ∀ δ > (0 : ℝ), ∀ᶠ Q in atTop,
      RHLinalg.frobSq (hatGzBridge (Zc Q) (PQ Q))
        ≤ (κ + δ) * ((Zc Q).N (PQ Q).T (2 * (PQ Q).T) : ℝ)) :
    ∀ ε > 0, ∃ Q₀ : ℝ, ∀ Q ≥ Q₀,
      (2 - κ - ε) * ((Zc Q).N (PQ Q).T (2 * (PQ Q).T) : ℝ) ≤ lower Q := by
  intro ε hε
  set N : ℝ → ℝ := fun Q => ((Zc Q).N (PQ Q).T (2 * (PQ Q).T) : ℝ) with hNdef
  set B : ℝ → ℝ := fun Q => θ₀ Q / ((PQ Q).aQ * (PQ Q).LB) with hBdef
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hκδ0 : 0 ≤ κ + δ := by
    by_contra h
    rw [not_le] at h
    obtain ⟨Q, hQ1, hQ2⟩ := ((hfrob δ hδ).and (hNtop.eventually_ge_atTop 1)).exists
    have hneg : RHLinalg.frobSq (hatGzBridge (Zc Q) (PQ Q)) < 0 :=
      lt_of_le_of_lt hQ1 (mul_neg_of_neg_of_pos h
        (by simp only [hNdef] at hQ2 ⊢; linarith))
    exact absurd (Zeta23.Assembly.frobSq_nonneg _) (not_le.mpr hneg)
  have hot := Zeta23.Assembly.err_isLittleO (N := N) (R₁ := fun _ => 0) (R₂ := fun _ => 0)
    (NII := NIIf) (B := B) (cl := fun _ => κ + δ) (K := κ + δ)
    hNtop (isLittleO_zero _ _) (isLittleO_zero _ _) hNII_o hBto
    (Eventually.of_forall fun _ => ⟨hκδ0, le_rfl⟩)
  have hsmall : ∀ᶠ Q in atTop,
      3 * NIIf Q + B Q * (4 + 2 * Real.sqrt ((κ + δ) * N Q) + B Q) ≤ δ * N Q := by
    filter_upwards [hot.def hδ, hNtop.eventually_ge_atTop 0] with Q h1 hN0
    simp only [Real.norm_eq_abs, mul_zero, zero_add, add_zero, abs_of_nonneg hN0] at h1
    exact (le_abs_self _).trans h1
  have hmain : ∀ᶠ Q in atTop, (2 - κ - ε) * N Q ≤ lower Q := by
    filter_upwards [h0, hB0, htrace δ hδ, hfrob δ hδ, hsmall,
      hNtop.eventually_ge_atTop 0] with Q hA hB₀ htr hfr hsm hN0
    have hlow := Zeta23.Assembly.N0star_lower_moment (κ := κ)
      (R₁ := δ * N Q) (R₂ := δ * N Q) hB₀ hA
      (by simp only [hNdef] at htr ⊢; linarith)
      (by simp only [hNdef] at hfr ⊢; linarith)
    rw [show κ * N Q + δ * N Q = (κ + δ) * N Q by ring] at hlow
    have hfin : (2 - κ - ε) * N Q
        = (2 - κ) * N Q - (4 * (δ * N Q) + δ * N Q + δ * N Q) := by
      simp only [hδdef]; ring
    rw [hfin]
    linarith [hsm, hlow]
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp hmain
  exact ⟨Q₀, fun Q hQ => hQ₀ Q hQ⟩

/-! ## A.2 H2 — the Weil-form grid Gram identity `Gz = Gp`, no pole term (CITED) -/

/-- **H2** (the Weil-form grid Gram identity, at ZetaQ's design point). Given the paper-form
explicit formula for `L(·,χ)`, the zero-side and prime-side grid Gram matrices agree at
`P.toParams`, i.e. at `L = λℒ` and `X = (QT/2π)^λ`.

Paper §2.1 (H2) and §2.2 (the density display `ν_{X,χ} = μ_q + P_{X,χ}`, **no pole term**).

Depends on: `Zeta23.ZeroConfig.Gz_eq_GpChi` (`Zeta23/ThmE/GzGpChi.lean:47`);
`ZetaQ.ParamsQ.toParams_L`.
Rule 17: CLEAN. `hL : 0 < P.LB` is POSITIVITY of the bandwidth scale, not a cap; `hl` says
`T ≠ 2π`, free in the regime `T ≥ 300`. No `Params.Valid`, no `X ≤ T` (and none is needed —
[R]'s hypotheses are exactly the four transcribed here), no buffer. -/
theorem H2_Gz_eq_GpChi (Z : Zeta23.ZeroConfig) (P : ParamsQ) (κ q : ℕ) (c : ℕ → ℂ)
    (hl : Zeta23.l P.T ≠ 0)
    (hEF : Zeta23.ThmE.ExplicitFormulaPaperChi κ q c Z)
    (hL : 0 < P.LB)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ)))
    (hφsupp : tsupport P.phiQ ⊆ Set.Icc (-(P.LB / 2)) (P.LB / 2)) :
    Z.Gz P.toParams P.T = Zeta23.ThmE.GpChi P.toParams κ q c P.T := by
  have hLB : P.toParams.L P.T = P.LB := P.toParams_L hl
  refine Z.Gz_eq_GpChi P.toParams κ q c P.T hEF ?_ hφC2 ?_
  · rw [hLB]; exact hL
  · rw [hLB]; exact hφsupp

/-- **H2, absolute-convergence half.** Under the same hypotheses the zero-side entries are
absolutely summable at ZetaQ's design point.

Paper §2.1 (H2).
Depends on:
`Zeta23.ZeroConfig.summable_Gsummand_chi`, `ZetaQ.ParamsQ.toParams_L`.
Rule 17: CLEAN — identical hypothesis set to `H2_Gz_eq_GpChi`. -/
theorem H2_summable_Gsummand (Z : Zeta23.ZeroConfig) (P : ParamsQ) (κ q : ℕ) (c : ℕ → ℂ)
    (hl : Zeta23.l P.T ≠ 0)
    (hEF : Zeta23.ThmE.ExplicitFormulaPaperChi κ q c Z)
    (hL : 0 < P.LB)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ)))
    (hφsupp : tsupport P.phiQ ⊆ Set.Icc (-(P.LB / 2)) (P.LB / 2))
    (k l : Fin (P.toParams.d P.T)) :
    Summable (fun ρ : Z.carrier => Z.Gsummand P.toParams P.T k l ρ) := by
  have hLB : P.toParams.L P.T = P.LB := P.toParams_L hl
  refine Z.summable_Gsummand_chi P.toParams κ q c P.T hEF ?_ hφC2 ?_ k l
  · rw [hLB]; exact hL
  · rw [hLB]; exact hφsupp

/-- **H2's hypothesis is DISCHARGED, not assumed.** For primitive `χ` mod `q > 1` the paper-form
explicit formula `ExplicitFormulaPaperChi` is a theorem of [R], not an axiom: [R]'s
literature-form EF for `L(s,χ)` composed with the χ-Γ facts.

Paper §2.1 (H2, "no pole term (Λ(s,χ) entire for primitive χ, q > 1)", `ThmE/EFLitChi.lean:14`).

Depends on:
`Zeta23.ThmE.explicitFormulaPaperChi_of_lit` (`ThmE/EFLitChi.lean:357`),
`Zeta23.ThmE.EF_lit_chi_L` (`ThmE/MainChi.lean:37`),
`Zeta23.ThmE.GammaChi.gammaFactsChi` (`ThmE/GammaFactsChiProof.lean:371`).
Modulus range: the tree says `1 < q` and the notes say `3 ≤ q`; resolved to the tree's `1 < q`
plus primitivity (no primitive character mod 2 exists, so the two agree in
content, and matching the tree lets this be a `:=`).
Rule 17: CLEAN — parameter-free (no `Params`, no λ, no X, no D₀). -/
theorem H2_EF_of_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) :
    Zeta23.ThmE.ExplicitFormulaPaperChi (Zeta23.ThmE.parity χ) q (Zeta23.ThmE.coeff χ)
      (Zeta23.ThmE.LZeros (Zeta23.ThmE.LSeam_of hq hprim)) :=
  Zeta23.ThmE.explicitFormulaPaperChi_of_lit (Zeta23.ThmE.EF_lit_chi_L hq hprim)
    (Zeta23.ThmE.GammaChi.gammaFactsChi Zeta23.ThmE.parity_le_one (by omega)) (by omega)
    (Zeta23.ThmE.coeffUnimodular_of_primitive hq hprim).toCoeffOK

/-! ## A.3 H3 — pointwise positivity `g = φ²⋆φ² ≥ 0` (CITED) -/

/-- **H3** (pointwise positivity). `g = φ²⋆φ² ≥ 0` at ZetaQ's taper.

Paper §2.1 (H3) and §2.2 (`gQ`'s docstring in `ZetaQ/Defs.lean`).

Depends on: `Zeta23.AdmWindow.gv_nonneg`,
**`Zeta23/ThmD/WindowCore.lean:387`** — both handover notes cite `:386` (the docstring line);
the corrected anchor is recorded here. The proof term below is [R]'s own,
verbatim; the anchor's ambient `hW : AdmWindow v L w c` is an auto-included section variable the
tree itself flags as unused (`set_option linter.unusedSectionVars false in`, with the comment that
`hW` is kept "so that call sites can write `hW.<name>`"), so there is nothing in it to cite
through. `H3_positivity_window` immediately below is the literal re-export for call sites that do
hold an `AdmWindow`.
Rule 17: CLEAN, vacuously — the statement mentions no bandwidth, no X and no buffer. -/
theorem H3_positivity (P : ParamsQ) (y : ℝ) : 0 ≤ P.gQ y :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **H3, literal re-export** at an abstract admissible window.

Paper §2.1 (H3).
Depends on: `Zeta23.AdmWindow.gv_nonneg`
(`Zeta23/ThmD/WindowCore.lean:387`).
Rule 17: CLEAN. NB the ambient `AdmWindow` structure does carry `one_le_w` and `w8 : 8w ≤ L`
(`WindowCore.lean:31–43`) — irrelevant to positivity, and neither is a forbidden hypothesis
(`one_le_w` is KEPT in `ParamsQ.Valid`; `8w ≤ L` is the paper's own side condition, §10.3). Do
NOT, however, cite `AdmWindow` itself as though it were hypothesis-free. -/
theorem H3_positivity_window {v : ℝ → ℝ} {L w c : ℝ} (hW : Zeta23.AdmWindow v L w c) (y : ℝ) :
    0 ≤ Zeta23.AdmWindow.gv v y :=
  hW.gv_nonneg y

/-! ## A.4 H4 — the Gevrey-2 profile ϱ₂ and the ramp lemma (CITED) -/

/-- The ZetaQ taper is the PROFILE FACTOR times [R]'s `Taper.phi` at the paper's scale `L = λℒ`.

Used to read `P.phiQ u = Taper.phi P.ϱ P.LB P.w u` (the flat taper, paper
§2.2 verbatim). The design window is now the profile-weighted product
`φ(u) = p(|u|/ℒ)·ϱ₂((L/2 − |u|)/w)` (`ZetaQ.ParamsQ.phiQ_eq_prof_mul`, the `atD` idiom of
`ZetaQ/Defs.lean` §3); this is that statement.
Depends on: `ParamsQ.phiQ_eq_prof_mul`.
Rule 17: CLEAN — `hl : Zeta23.l P.T ≠ 0` is `T ≠ 2π`, free at `T ≥ 300`; `hw : w ≠ 0`. -/
theorem phiQ_eq (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) (hw : P.w ≠ 0) (u : ℝ) :
    P.phiQ u = P.prof.eval (|u| / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u :=
  P.phiQ_eq_prof_mul hl hw u

/-- **H4a** (the Gevrey-2 profile with its explicit constants). `ϱ₂` is a Gevrey-2 taper profile
with derivative constants `(A, B) = (36/e, 2e⁸)` — literally `ZetaQ.gevreyA`, `ZetaQ.gevreyB`.

Paper §2.1 (H4) and §2.2.
Depends on: `Zeta23.Taper.gevreyProfile_rhoTwo`
(`Zeta23/Taper/Gevrey.lean:401`).
Rule 17: CLEAN, vacuously — no `Params`, no λ, no T. -/
theorem H4_gevreyProfile_rhoTwo :
    Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB Zeta23.Taper.rhoTwo :=
  Zeta23.Taper.gevreyProfile_rhoTwo

/-- **H4b** (the ramp lemma, at ZetaQ's taper). `‖φ^{(k)}‖₁ ≤ 2B′w(A/w)^k k^{2k}` for `k ≥ 1`,
with the PRODUCT-WINDOW constant `B′ = gevreyBprod A B`.

For the flat taper this was [R]'s ramp lemma verbatim at `B = gevreyB`;
the design window `p(u/ℒ)·φ_flat` satisfies the same Gevrey-2 shape by Leibniz over the finitely
many derivatives of the polynomial factor (`Zeta23/Taper/GevreyProduct.lean`
`gevrey_polyQ_mul_phi`; report `audit/ProductWindow_REPORT.md`), with
`B′ = B·Σ_j M_j (w/(ℒA))^j + ½Σ_j M_j (λ/A)^j` (`ZetaQ.ParamsQ.gevreyBprod`). The `(A, B)` of
§2.2 are unchanged; only the prefactor moves. Re-export of `ParamsQ.Valid.gevreyPhiBound`
(`ZetaQ/Window.lean`).
Rule 17: CLEAN — `hP : P.Valid` (no `lam_le_one`), `hw : 8w ≤ L` is [eq:wrange],
a bound on the RAMP WIDTH; no upper bound on `P.lam` anywhere in the chain. -/
theorem H4_ramp (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) {k : ℕ} (hk : 1 ≤ k) :
    ∫ u, |iteratedDeriv k P.phiQ u|
      ≤ 2 * P.gevreyBprod gevreyA gevreyB * P.w * (gevreyA / P.w) ^ k
          * (k : ℝ) ^ ((2 : ℝ) * (k : ℝ)) := by
  have hG := hP.gevreyPhiBound hw hϱ
  have hsm := hP.phiQ_smooth (by linarith [hP.w_pos]) hϱ
  have h := hG.bound k hk
  rw [Zeta23.Taper.iteratedDeriv_ofReal_comp (f := P.toParams.phi P.T) hsm k] at h
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-! ## A.5 H5 — the ν-generic ends majorants, CAP-FREE `_L` forms only (CITED)

**Rule-17 trap, stated once and loudly.** The capped siblings `Zeta23.PrimeSide.calE1_maj_bound`
(`EndsE1.lean:616`) and `calE2_maj_bound` (`EndsE2.lean:266`) carry the hypothesis
`p.L ≤ 2 * p.l`. In T-aspect (`L = λl`) that IS the bandwidth cap, and here it is false by a
factor 10–60 (paper §8.2). Only the `_L` variants below may be cited. -/

/-- ZetaQ's design point as one of [R]'s `Setting`s, via the same R-1 reparameterisation as
`ParamsQ.toParams`. `Setting = ⟨T, lam, w⟩` (`Zeta23/PrimeSideA/Defs.lean:65`) with
`L := lam * Zeta23.l T` (`:78`).

Paper §2.2 / §8.
Depends on: `ParamsQ.toParams`.
Rule 17: `toSetting.lam` is `λℒ / l T` — LARGE (≈ 24 at Q = 10¹⁰⁰), emphatically not `P.lam`,
and no `lam ≤ 1` is derivable from it. Never "simplify" it. -/
def ParamsQ.toSetting (P : ParamsQ) : Zeta23.PrimeSide.Setting :=
  ⟨P.T, P.toParams.lam, P.w⟩

/-- The `Setting` bridge equation: [R]'s prime-side `L` at `toSetting` IS the paper's `L = λℒ`.

Paper §2.2.
Depends on: `ParamsQ.toSetting`.
Rule 17: `h : Zeta23.l P.T ≠ 0` is `T ≠ 2π`. -/
theorem ParamsQ.toSetting_L (P : ParamsQ) (h : Zeta23.l P.T ≠ 0) : P.toSetting.L = P.LB := by
  simp only [Zeta23.PrimeSide.Setting.L, ParamsQ.toSetting, ParamsQ.toParams]
  field_simp

/-- Consequently [R]'s prime-side `X` at `toSetting` is the paper's `X = (QT/2π)^λ`.

Paper §2.2.
Depends on: `ParamsQ.toSetting_L`.
Rule 17: `X ≫ T` here at every λ; no hypothesis says otherwise. -/
theorem ParamsQ.toSetting_X (P : ParamsQ) (h : Zeta23.l P.T ≠ 0) : P.toSetting.X = P.XQ := by
  simp only [Zeta23.PrimeSide.Setting.X, ParamsQ.XQ, ParamsQ.toSetting_L P h]

/-- **H5a** (the 𝓔₁ ends majorant, cap-free L-intrinsic form). `∬_{I×I} majK1(ν) ≤ C·L³B²(L + l)`
with `C = 4(90 + 32c_ϱ²)` and `T₀ = (2π)²`, for every `Setting` — in particular at
`P.toSetting`, which is what R-1 buys.

Paper §2.1 (H5) and §8.2 (`|𝓔₁| ≤ 4(90 + 32c_ϱ²)·L³B²·(L + l)`).

Depends on:
`Zeta23.PrimeSide.calE1_maj_bound_L` (`Zeta23/PrimeSideA/EndsE1.lean:727`).
Rule 17: CLEAN, and this is the flagged trap. The CAPPED sibling `calE1_maj_bound`
(`EndsE1.lean:616`) carries `p.L ≤ 2 * p.l` — the λ-cap in disguise — and is NOT cited. The
`_L` variant drops it, and its conclusion is symmetric in `(p.L + p.l)`. `LocalHypsCoreW`
(`PrimeSideA/Basic.lean:559`) demands only `4 ≤ cϱ`, `lam_pos : 0 < p.lam` (its own doc comment
reads "no upper cap here"), `1 ≤ w`, `w ≤ L/8`, `1 ≤ l` and φ̂ facts. -/
theorem H5_calE1_maj_bound_L (cϱ : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Zeta23.PrimeSide.Setting) (F : Zeta23.PrimeSide.LocalFun) (B : ℝ)
        (ν : ℝ → ℝ), T₀ ≤ p.T →
      Zeta23.PrimeSide.LocalHypsCoreW cϱ p F → Continuous ν → Zeta23.PrimeSide.NuBound p B ν →
      ∫ z in Zeta23.PrimeSide.sqI p, Zeta23.PrimeSide.majK1 p F ν z
        ≤ C * (p.L ^ 3 * B ^ 2 * (p.L + p.l)) :=
  Zeta23.PrimeSide.calE1_maj_bound_L cϱ

/-- **H5b** (the 𝓔₂ ends majorant, cap-free L-intrinsic form).
`∬_{(I×I)ᶜ} majK2(ν) ≤ C·L³B²(1 + log L)(L + l)` with `C = 2(8 + 4 log⁺c_ϱ + 7c_ϱ)·CN2 c_ϱ`
(= the notes' `C₂′`) and `T₀ = 2πe⁸`.

Paper §2.1 (H5) and §8.2 (`|𝓔₂| ≤ C₂′·L³B²·(1 + log L)(L + l)`).

Depends on:
`Zeta23.PrimeSide.calE2_maj_bound_L` (`Zeta23/PrimeSideA/EndsE2.lean:353`).
Rule 17: CLEAN — the CAPPED sibling `calE2_maj_bound` (`EndsE2.lean:266`) carries
`p.L ≤ 2 * p.l` and is NOT cited.
LIVE SUB-FINDING (Q-1, §8-adjacent, routed to the §8 owner, NOT a §9 obligation): the surviving
hypothesis `p.L ≤ B` is FALSE at the paper's instantiation `B := ℒ + C₀` (`C₀ = 6`), since it
reads `λ*ℒ ≤ ℒ + 6`, i.e. `ℒ ≤ 6/(λ* − 1) ≈ 23.9`, whereas ℒ ≈ 230 at Q = 10¹⁰⁰. `NuBound` is
monotone in `B`, so the repair is free (`B := λ*ℒ`), at the cost of inflating the displayed 𝓔₂
family constant by ≈ 1.48. Expected downstream impact ≈ +0.2% of budget. -/
theorem H5_calE2_maj_bound_L (cϱ : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Zeta23.PrimeSide.Setting) (F : Zeta23.PrimeSide.LocalFun) (B : ℝ)
        (ν : ℝ → ℝ), T₀ ≤ p.T →
      Zeta23.PrimeSide.LocalHypsCoreW cϱ p F → Continuous ν → Zeta23.PrimeSide.NuBound p B ν →
      p.L ≤ B →
      ∫ z in (Zeta23.PrimeSide.sqI p)ᶜ, Zeta23.PrimeSide.majK2 cϱ p ν z
        ≤ C * (p.L ^ 3 * B ^ 2 * (1 + Real.log p.L) * (p.L + p.l)) :=
  Zeta23.PrimeSide.calE2_maj_bound_L cϱ

/-! ## A.6 H6 — the q-uniform local count with ABSOLUTE A₀ (CITED) -/

/-- **H6** (the q-uniform local count). ONE absolute `A₀ ≥ 1` with
`N_χ(t, t+1] ≤ A₀·log(q(|t| + 3))` for every primitive `χ` mod `q > 1` and every real `t`.

Paper §2.1 (H6) and §9 ("the local count is [R]'s own uniform theorem").

Depends on:
`Zeta23.ThmE.localCountChi_uniform_proof` (`Zeta23/ThmE/LocalCountChi.lean:69`; the docstring
opens at `:65`).
Do NOT confuse with the per-χ packaging `Zeta23.ThmE.localCountChi` (`LocalCountChi.lean:237`),
whose constant is `A₀·(1 + log q)` and is therefore q-DEPENDENT; that packaging is what the
`RvMChi` header's "constants depending on q" (`RvMChi.lean:11`) describes.
Rule 17: CLEAN, and the cleanest of the six — the statement is `Params`-free, `Setting`-free and
T-free, so it needs no reparameterisation at all. -/
theorem H6_localCountChi_uniform :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)) :=
  Zeta23.ThmE.localCountChi_uniform_proof

/-! # PART B — §9's own statements

Paper §9, verbatim:

> The Weil explicit formula Gz(χ) = Gp(χ) with density ν_{X,χ} and no pole term; RvM-χ with
> absolute constant; the local count N_χ(t, t+1] ≤ A₀·log(q(|t|+3)) with ABSOLUTE A₀. Every
> analytic constant in the chain is already explicit-and-linear in q in [R]'s own development
> (‖L(s,χ)‖ ≤ q‖s‖/Re s; ‖L(w,χ)‖ ≤ 8q(|w.im|+3)); the uniformity is re-packaging, not new
> analysis. The buffer count N_{II,χ} ≤ 3A₀D₀·log-scale gives the L₄ budget row. -/

/-! ## B.0 The per-χ zero configuration

Named `ZetaQ.ZChi` (not `ZetaQ.EFChi.ZChi`) because it is a shared object, and
lists it at the §3/§9 boundary with the note "propose §9 defines the thin wrapper, §3 consumes". -/

/-- The nontrivial zeros of `L(·,χ)` with multiplicities, as an abstract `ZeroConfig`, for
primitive `χ` mod `q > 1`.

Paper §2.2, §3.
Depends on: `Zeta23.ThmE.LZeros`,
`Zeta23.ThmE.LSeam_of` (`Zeta23/ThmE/SeamL.lean:367`).
Modulus range: `1 < q` + primitivity, matching the tree.
Rule 17: CLEAN — no parameters at all. -/
def ZChi {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hprim : χ.IsPrimitive) :
    Zeta23.ZeroConfig :=
  Zeta23.ThmE.LZeros (Zeta23.ThmE.LSeam_of hq hprim)

namespace EFChi

/-! ## B.1 EF-χ at the ZetaQ grid: `Gz(χ) = Gp(χ)`, density `ν_{X,χ}`, no pole term -/

/-- The density of §9 IS `ν_{X,χ}` at the paper's `X = (QT/2π)^λ`: `ZetaQ.nuQ` is [R]'s `nuXc`
evaluated at `P.toParams.X P.T`. This is the "at density `ν_{X,χ} = μ_q + P_{X,χ}`, **no pole
term**" clause made machine-checkable — `nuXc = muq + PXc` with `Π_X ≡ 0`
(`Zeta23/ThmE/Hypotheses.lean:41–60`), the primitivity ground being that `Λ(s,χ)` is entire for
primitive `χ`, `q > 1` (`ThmE/EFLitChi.lean:14`).

Paper §2.2 (the density display) and §9 sentence 1.

Depends on: `ParamsQ.toParams_X`, `ZetaQ.nuQ`.
Rule 17: CLEAN. `hl : Zeta23.l P.T ≠ 0` is `T ≠ 2π`; there is no relation between `X` and `T`
anywhere here, and none may be added. -/
theorem nuQ_eq_nuXc (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    nuQ P q χ τ
      = Zeta23.ThmE.nuXc (parity χ) q (fun n => χ (n : ZMod q)) (P.toParams.X P.T) τ := by
  rw [P.toParams_X hl]; rfl

/-- **§9, EF-χ at the ZetaQ grid.** The Weil/Guinand explicit formula `Gz(χ) = Gp(χ)` entrywise
for the zeros of `L(·,χ)`, at ZetaQ's grid `(L = λℒ, h = 2π/L, d = ⌊LT/2π⌋, τ_k = T + kh)`, with
density `ν_{X,χ} = μ_q + P_{X,χ}` (`nuQ_eq_nuXc`) and **NO pole term**.

Paper §9 sentence 1; paper §2.2 density display; consumed at paper §3 ("by the q-uniform explicit
formula (§9) this equals the zero-side matrix"). Working note: NOTE_QF §QF.i.

Depends on: `ZetaQ.H2_Gz_eq_GpChi`, `ZetaQ.EFChi.ZChi`,
`ZetaQ.EFChi.H_EF_chi`, `ZetaQ.EFChi.nuQ_eq_nuXc`.
Rule 17: CLEAN by construction. `hL : 0 < P.LB` is positivity. **No** `P.lam ≤ 1`, **no**
`P.XQ ≤ P.T`, **no** `D₀ = √T` (the buffer does not appear in this statement at all).
FLAG: do NOT add `hX : P.XQ ≤ P.T` for a summability step — [R] does not need
it; `Gz_eq_GpChi`'s hypotheses are exactly the four transcribed here. -/
theorem Gz_eq_GpChi_Q (P : ParamsQ) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive)
    (hl : Zeta23.l P.T ≠ 0) (hL : 0 < P.LB)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ)))
    (hφsupp : tsupport P.phiQ ⊆ Set.Icc (-(P.LB / 2)) (P.LB / 2)) :
    (ZChi hq hprim).Gz P.toParams P.T
      = Zeta23.ThmE.GpChi P.toParams (parity χ) q (fun n => χ (n : ZMod q)) P.T := by
  have hpar : parity χ = Zeta23.ThmE.parity χ := by
    simp only [parity, Zeta23.ThmE.parity]
  rw [hpar]
  exact H2_Gz_eq_GpChi (ZChi hq hprim) P (Zeta23.ThmE.parity χ) q
    (Zeta23.ThmE.coeff χ) hl (H2_EF_of_primitive hq hprim) hL hφC2 hφsupp

/-- **§9, EF-χ: the hypothesis is a theorem.** Restatement of `ZetaQ.H2_EF_of_primitive` at
`ZChi`, so that nothing downstream carries H-EF(χ) as an axiom.

Paper §2.1 (H2)
Depends on: `ZetaQ.H2_EF_of_primitive`.
Rule 17: CLEAN — parameter-free. -/
theorem H_EF_chi {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) :
    Zeta23.ThmE.ExplicitFormulaPaperChi (Zeta23.ThmE.parity χ) q (Zeta23.ThmE.coeff χ)
      (ZChi hq hprim) :=
  H2_EF_of_primitive hq hprim

/-! ## B.2 RvM-χ with absolute constant -/

/-- **§9, RvM-χ with ABSOLUTE constant.** `|N_χ(T,2T) − (T/2π)·ℓ_{1,χ}| ≤ A·log(q(T+2))` with `A`
and `T₀` absolute — independent of `q` and of `χ` — for every primitive `χ` mod `q > 1` and every
`T ≥ T₀`.

Paper §9 sentence 1 ("RvM-χ with absolute constant"); NOTE_QF §QF.i(a); NOTE_QR §QR.2.

**NOT a sorry** — this is [R]'s `mainChi_uniform_aux`
(`Zeta23/ThmE/MainTermChi.lean:260`) discharged at its two proved q-uniform inputs
`backlund_horizontalChi_uniform` (`ThmE/ReZeroCountChi.lean:283`) and
`GammaChi.gammaFactsChi_uniform` (`ThmE/GammaFactsChiProof.lean:380`). [R] performs exactly this
composition at `MainTermChi.lean:517` but only to DEGRADE to the per-χ `mainChi` (`:514`, constant
`A(log q + log 2 + 1)`), so the uniform composite has no top-level name there. **ZetaQ names it.**
That is discrepancy D1: §9's prose ("the LocalCountChi/MainTermChi re-runs with explicit
constants") understates the tree; the obligation is a naming lemma, not a re-run.
Log-scale note for §10's ledger: `log(q(T+2)) ≤ ℒ + O(1)` for `q ≤ Q`, `T ≥ 2π`, so the paper's
"C·log(qT)" and the tree's "A·log(q(T+2))" agree to an additive absolute constant.
Rule 17: CLEAN. No `Params` at all — no λ, no X, no D₀. `T₀ ≤ T` is a size threshold, and this
`T₀` is existential/absolute, NOT `Zeta23.Tail.T₀ = 300`. -/
theorem rvmChi_main_uniform :
    ∃ A T₀ : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)) :=
  Zeta23.ThmE.mainChi_uniform_aux
    Zeta23.ThmE.backlund_horizontalChi_uniform
    Zeta23.ThmE.GammaChi.gammaFactsChi_uniform

/-! ## B.3 The q-uniform local count and its constant -/

/-- The absolute local-count constant `A₀` of H6, as WITNESSED by [R]'s own proof
(`Zeta23/ThmE/LocalCountChi.lean:72–76`: `refine ⟨max 1 (2 * (1 / Real.log (R / r) * 5)), …⟩`
with the Jensen disc `r = 0.84`, `R = 0.95` centred at `c₀ = 2 + (t + ½)i`, growth input
`B := 24q(|t| + 6)`, lower bound `|L(2,χ)| ≥ 1/3`, and a factor 2 from halving). The `max 1` is
inactive, so `A₀ = 2·(1/log(0.95/0.84))·5 = 10/log(95/84) = 81.26111216028406…`
(`log(95/84) = 0.12306009275722721`).

Diagnostic anchor (NOTE_QF (2)): the MEASURED value on the 5230-zero dataset is ≈ 0.38, so the
proved constant carries ≈ 214× slack — consistent with the note's "enormous practical slack".
The value is QUOTED with provenance and never re-optimised (the Jensen radii
are not tuned here).

Paper §2.1 (H6), §9.
Rule 17: CLEAN — a numeral. -/
def A0 : ℝ := 10 / Real.log (95 / 84)

/-- **§9 / H6, the q-uniform local count.** `N_χ(t, t+1] ≤ A₀·log(q(|t| + 3))` with ONE absolute
`A₀` for every primitive `χ` mod `q > 1` and every real `t`.

Paper §2.1 (H6) and §9; NOTE_QR §QR.2 ("the local count needs NO re-run: it is in the tree";
NOTE_QF's ledger row "mechanical: re-run Jensen" is upgraded to [proved in tree]).

Depends on: `ZetaQ.H6_localCountChi_uniform`.
The witnessing constant is `ZetaQ.EFChi.A0 = 81.2611…`.
Rule 17: CLEAN — parameter-free. -/
theorem localCountChi_uniform :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)) :=
  H6_localCountChi_uniform

/-! ## B.4 The buffer count `N_{II,χ}` at a FREE buffer, and the L₄ budget row

**Why §9 owes a mirror here.** Phase 1's `Zeta23.Tail.NIID_le`
(`Tail/GevreyTail.lean:1878`) takes its local-count hypothesis in the PER-χ shape
`A₀·log(|t| + 3)`, i.e. at [R]'s `localCountChi`, whose constant is `A₀ᵘ·(1 + log q)`. Feeding H6
through that packaging gives `3A₀ᵘ(1 + log q)·D·log 4T` — a PRODUCT of `log q` and `log 4T` —
whereas the paper's L₄ budget row is the SUM `3A₀D₀(ℒ + log 4T)`. The shapes are genuinely
different and it is the sum-form that §10 prices. So §9 mirrors the boundary count with the
log-scale taken INSIDE, at `log(q·4T)`, which is what the q-uniform local count actually produces,
which implies the notes' `(ℒ + log 4T)` display for `q ≤ Q`, `T ≥ 2π`, and which keeps `A₀`
absolute — the whole point of §9's sentence.

**Rule-17 pressure point, named.** The buffer `D` is a FREE real in every statement below. There
is no `D = Real.sqrt T` hypothesis and none may be added. `2 ≤ D` and `D + 4 ≤ T` are the honest
regime facts inherited from `boundary_countD_le`; both are satisfied by the design of record and
by the reference design `D₀ = ℒ² log ℒ`, and both are threaded from `ParamsQ.Valid` below.
[R]'s original `Zeta23.Tail.NII_le` (`Tail.lean:595`) concludes `≤ 3A₀·√T·log 4T` and is NEVER
cited; `Zeta23.D0` (`Zeta23/Defs.lean:61`) is never reintroduced. -/

/-- **§9, the boundary count at a free buffer, q-uniformly.** For an abstract family of ordinates
`γ` with multiplicities `m` satisfying the q-UNIFORM unit-window count, the zeros in
`(T − D, T] ∪ (2T, 2T + D]` satisfy `∑ m_ρ ≤ 3·A₀·D·log(q·4T)`.

Paper §9 ("The buffer count N_{II,χ} ≤ 3A₀D₀·log-scale gives the L₄ budget row"); LEMMA_QT
§QT.b(5) displays `(ℒ + log 4T)`.
Mirror of `Zeta23.Tail.boundary_countD_le`
(`Zeta23/Tail/GevreyTail.lean:1797`) with `Real.log (|t| + 3) ⤳ Real.log (q * (|t| + 3))` carried
through the window/ceiling bookkeeping; the only real work is re-running the monotonicity step at
the q-scaled argument (`|t| + 3 ≤ 4T` becomes `q(|t| + 3) ≤ q·4T`, the same inequality scaled).
Depends on: `Zeta23.Tail.boundary_countD_le`, `Zeta23.Tail.T₀` (= 300, `Tail/Basic.lean:53`).
Rule 17: CLEAN. `D` is FREE — no `D = √T`. `hD2 : 2 ≤ D` and `hDT : D + 4 ≤ T` are the regime
facts the free-buffer count genuinely needs ([R] got both for free from `√T ≥ 17`; ours must state
them). Do NOT cite `Zeta23.Tail.NII_le`. -/
theorem boundary_countD_chi_le {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T D : ℝ} {q : ℕ}
    (hq : 1 < q) (hA₀ : 1 ≤ A₀)
    (hN : ∀ (t : ℝ) (s : Finset ι), (∀ ρ ∈ s, t < γ ρ ∧ γ ρ ≤ t + 1) →
      (∑ ρ ∈ s, (m ρ : ℝ)) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hT : Zeta23.Tail.T₀ ≤ T) (hD2 : 2 ≤ D) (hDT : D + 4 ≤ T) (s : Finset ι)
    (hs : ∀ ρ ∈ s, (T - D < γ ρ ∧ γ ρ ≤ T) ∨ (2 * T < γ ρ ∧ γ ρ ≤ 2 * T + D)) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ 3 * A₀ * D * Real.log (q * (4 * T)) := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA₀' : (0 : ℝ) ≤ A₀ := by linarith
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.le
  set K : ℕ := ⌈D⌉₊ with hK
  have hKlt : (K : ℝ) < D + 1 := Nat.ceil_lt_add_one (by linarith)
  have hKge : D ≤ K := Nat.le_ceil D
  set C : ℝ := A₀ * Real.log ((q : ℝ) * (4 * T)) with hCdef
  have hlog1 : 1 ≤ Real.log ((q : ℝ) * (4 * T)) := by
    refine le_trans (Zeta23.Tail.one_le_log_four_mul hT) ?_
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hC : 0 ≤ C := by rw [hCdef]; nlinarith
  have hlogmono : ∀ (t : ℝ), |t| + 3 ≤ 4 * T →
      A₀ * Real.log ((q : ℝ) * (|t| + 3)) ≤ C := by
    intro t h
    refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hA₀'
    · have := abs_nonneg t; nlinarith
    · exact mul_le_mul_of_nonneg_left h hq0
  set slo := s.filter (fun ρ => γ ρ ≤ T) with hslo
  set shi := s.filter (fun ρ => ¬ γ ρ ≤ T) with hshi
  have hlo_mem : ∀ ρ ∈ slo, T - D < γ ρ ∧ γ ρ ≤ T := by
    intro ρ hρ
    rw [hslo, Finset.mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact h
    · exact absurd hρ.2 (by linarith [h.1])
  have hhi_mem : ∀ ρ ∈ shi, 2 * T < γ ρ ∧ γ ρ ≤ 2 * T + D := by
    intro ρ hρ
    rw [hshi, Finset.mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact absurd h.2 hρ.2
    · exact h
  have hlo : ∑ ρ ∈ slo, (m ρ : ℝ) ≤ K * C := by
    apply Zeta23.Tail.sum_mult_le_of_windows slo m (fun ρ => ⌊T - γ ρ⌋₊) K
    · intro ρ hρ
      have h := hlo_mem ρ hρ
      have : (⌊T - γ ρ⌋₊ : ℝ) < K :=
        lt_of_le_of_lt (Nat.floor_le (by linarith [h.2])) (by linarith [h.1, hKge])
      exact_mod_cast this
    · intro j hj
      refine (hN (T - j - 1) _ ?_).trans (hlogmono _ ?_)
      · intro ρ hρ
        rw [Finset.mem_filter] at hρ
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
    apply Zeta23.Tail.sum_mult_le_of_windows shi m (fun ρ => ⌈γ ρ - 2 * T⌉₊ - 1) K
    · intro ρ hρ
      have h := hhi_mem ρ hρ
      have : ⌈γ ρ - 2 * T⌉₊ ≤ K := by rw [hK]; exact Nat.ceil_mono (by linarith [h.2])
      have := hceil1 ρ hρ
      omega
    · intro j hj
      refine (hN (2 * T + j) _ ?_).trans (hlogmono _ ?_)
      · intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hc : ⌈γ ρ - 2 * T⌉₊ = j + 1 := by have := hceil1 ρ hρs; omega
        have := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
        push_cast at this
        constructor <;> linarith [this.1, this.2]
      · have hj' : (j : ℝ) < D + 1 := lt_of_lt_of_le (by exact_mod_cast hj) hKlt.le
        rw [abs_of_nonneg (by positivity)]
        linarith
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => γ ρ ≤ T)]
  have hK' : (K : ℝ) * C ≤ (D + 1) * C := mul_le_mul_of_nonneg_right hKlt.le hC
  have hfin : (2 : ℝ) * ((D + 1) * C) ≤ 3 * A₀ * D * Real.log ((q : ℝ) * (4 * T)) := by
    rw [hCdef]
    have h23 : 2 * (D + 1) ≤ 3 * D := by linarith
    have hAl : 0 ≤ A₀ * Real.log ((q : ℝ) * (4 * T)) := hC
    nlinarith
  linarith

/-- **§9, the buffer count `N_{II,χ}(D) ≤ 3·A₀·D·log(4qT)` with `A₀` ABSOLUTE.**
`N(I′(D) ∖ I) = N(T−D, T) + N(2T, 2T+D)` at a FREE buffer `D`.

Paper §9 ("The buffer count N_{II,χ} ≤ 3A₀D₀·log-scale gives the L₄ budget row"); LEMMA_QT
§QT.b(5). The log scale is pinned to `Real.log (q * (4 * T))`, which implies the notes'
`3A₀D₀(ℒ + log 4T)` display for `q ≤ Q`, `T ≥ 2π`.
Mirror of `Zeta23.Tail.NIID_le`
(`Zeta23/Tail/GevreyTail.lean:1878`) at H6's uniform local count; follows the existing `NIID_le`
script verbatim once `boundary_countD_chi_le` is in place.
Depends on: `boundary_countD_chi_le`, `Zeta23.Assembly.NIID` (`Zeta23/WindowD.lean:100`),
`Zeta23.Tail.T₀`.
Rule 17: CLEAN and this is the pressure point. `D` is FREE. **Never cite `Zeta23.Tail.NII_le`**
(`Tail.lean:595`), whose conclusion `≤ 3A₀·√T·log 4T` has `D₀ = √T` baked in; and never
reintroduce `Zeta23.D0`. `2 ≤ D`, `D + 4 ≤ T` are honest regime facts, not a buffer identity. -/
theorem NIID_chi_le (Z : Zeta23.ZeroConfig) {A₀ T D : ℝ} {q : ℕ} (hq : 1 < q) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hT : Zeta23.Tail.T₀ ≤ T) (hD2 : 2 ≤ D) (hDT : D + 4 ≤ T) :
    (Zeta23.Assembly.NIID Z T D : ℝ) ≤ 3 * A₀ * D * Real.log (q * (4 * T)) := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  -- the q-uniform local count in the finite-sub-family shape (mirror of
  -- `Zeta23.Tail.LocalCount.ofWindowCount`)
  have hNw : ∀ (t : ℝ) (u : Finset Z.carrier),
      (∀ ρ ∈ u, t < ((ρ : ℂ).im) ∧ ((ρ : ℂ).im) ≤ t + 1) →
      (∑ ρ ∈ u, ((Z.mult (ρ : ℂ) : ℕ) : ℝ)) ≤ A₀ * Real.log (q * (|t| + 3)) := by
    intro t u hu
    refine le_trans ?_ (hloc t)
    have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
    unfold Zeta23.ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : u.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hu ρ hρ⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h
  have hfin1 : (Z.window (T - D) T).Finite := Z.finite_window _ _
  have hfin2 : (Z.window (2 * T) (2 * T + D)).Finite := Z.finite_window _ _
  set s1 : Finset Z.carrier := hfin1.toFinset.subtype (· ∈ Z.carrier) with hs1
  set s2 : Finset Z.carrier := hfin2.toFinset.subtype (· ∈ Z.carrier) with hs2
  have hN1 : (Z.N (T - D) T : ℝ) = ∑ ρ ∈ s1, (Z.mult (ρ : ℂ) : ℝ) := by
    unfold Zeta23.ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin1, hs1,
      Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (Z.mult ρ : ℝ))]
    · push_cast; rfl
    · intro x hx; exact ((Set.Finite.mem_toFinset _).mp hx).1
  have hN2 : (Z.N (2 * T) (2 * T + D) : ℝ) = ∑ ρ ∈ s2, (Z.mult (ρ : ℂ) : ℝ) := by
    unfold Zeta23.ZeroConfig.N
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
  have h := boundary_countD_chi_le (γ := fun ρ : Z.carrier => (ρ : ℂ).im)
    (m := fun ρ : Z.carrier => Z.mult (ρ : ℂ)) hq hA₀ hNw hT hD2 hDT (s1 ∪ s2) hunion
  rw [Finset.sum_union hdisj] at h
  unfold Zeta23.Assembly.NIID
  push_cast
  rw [hN1, hN2]
  exact h

/-- **§9, the free-buffer count at a ZetaQ design point.** `N_{II,χ}(D₀) ≤ 3A₀D₀·log(4qT)` at
`P.D0`, with the buffer regime read off `ParamsQ.Valid`.

Paper §9; §2.2 (`I′ = (T − D₀, 2T + D₀]` at the FREE buffer).
Depends on: `NIID_chi_le`, `ParamsQ.Valid.two_le_D0`, `Valid.D0_le`, `Valid.T_ge`.
Rule 17: CLEAN and this is exactly why `ParamsQ.D0` is a FIELD. The three regime facts consumed
are `Zeta23.Tail.T₀ ≤ P.T` (`Valid.T_ge`), `2 ≤ P.D0` (`Valid.two_le_D0`) and `P.D0 + 4 ≤ P.T`
(`Valid.D0_le`) — `Zeta23.Tail.NIID_le` needs BOTH buffer conditions, strictly more than the tail
chain's `1 ≤ D`, which is why `ParamsQ.Valid` carries both. NOTHING here says `P.D0 = √P.T`. -/
theorem NIID_chi_le_Q (P : ParamsQ) (hP : P.Valid) (Z : Zeta23.ZeroConfig) {A₀ : ℝ} {q : ℕ}
    (hq : 1 < q) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    (Zeta23.Assembly.NIID Z P.T P.D0 : ℝ) ≤ 3 * A₀ * P.D0 * Real.log (q * (4 * P.T)) :=
  NIID_chi_le Z hq hA₀ hloc hP.T_ge hP.two_le_D0 hP.D0_le

/-- **§9 → §3 Prop 3.1(iii), the family aggregate (the L₄ budget row).**
`N_{II,fam} := Σ_χ N_{II,χ}(D₀) ≤ 3A₀D₀(ℒ + log 4T)·|fam|` for a finite family of primitive
characters of moduli `≤ Q`, each satisfying the q-uniform local count with the SAME absolute `A₀`.

The family is indexed abstractly (`Zc` the per-χ `ZeroConfig`, `mod` the modulus) rather than by
`Σ q, DirichletCharacter ℂ q`, so that `1 < mod i`, `mod i ≤ Q` and the local count are auditable
per member and the statement does not presuppose §12's family bookkeeping.

Paper §3 Prop 3.1(iii) ("N_{II,fam} ≤ r₃𝒩") and §9; priced at §10.3.

Depends on: `NIID_chi_le_Q`, `ParamsQ.LL`, `Zeta23.Assembly.NIID`.
**R-5, flagged for the ledger:** this statement carries the PROVED absolute constant
`A₀ = 81.2611…`. Paper §10.3 prices the L₄ row at the SHARP zero density instead ("**not** at the
proved absolute A₀ of §9, which is larger") — the ONE budget row not at its proved constant. The
ratio is ≈ πA₀ ≈ 255×; §10's ledger must state it explicitly. §9 does not attempt
the sharp-density bound; that is not §9's claim.
Rule 17: CLEAN. `P.D0` is a FIELD throughout; the regime facts come from `hP : P.Valid`. No
`D₀ = √T`, no λ-cap, no `X ≤ T`. -/
theorem NII_fam_le (P : ParamsQ) (hP : P.Valid) {ι : Type*} (fam : Finset ι)
    (Zc : ι → Zeta23.ZeroConfig) (mod : ι → ℕ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hmod : ∀ i ∈ fam, 1 < mod i) (hmodQ : ∀ i ∈ fam, (mod i : ℝ) ≤ P.Q)
    (hloc : ∀ i ∈ fam, ∀ t : ℝ,
      ((Zc i).N t (t + 1) : ℝ) ≤ A₀ * Real.log (mod i * (|t| + 3))) :
    (∑ i ∈ fam, (Zeta23.Assembly.NIID (Zc i) P.T P.D0 : ℝ))
      ≤ 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) * (fam.card : ℝ) := by
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hQ : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hD0 : (2 : ℝ) ≤ P.D0 := hP.two_le_D0
  have hπ := Real.pi_pos
  -- `log q ≤ log Q ≤ ℒ`, the last step being `T ≥ 2π` (free at `T ≥ 300`)
  have hTpi : (1 : ℝ) ≤ P.T / (2 * Real.pi) :=
    (one_le_div (by positivity)).mpr (by nlinarith [Real.pi_le_four])
  have hle : P.Q ≤ P.Q * P.T / (2 * Real.pi) := by
    rw [show P.Q * P.T / (2 * Real.pi) = P.Q * (P.T / (2 * Real.pi)) by ring]
    nlinarith
  have hlogQ : Real.log P.Q ≤ P.LL :=
    Real.log_le_log (by linarith) hle
  have hterm : ∀ i ∈ fam, (Zeta23.Assembly.NIID (Zc i) P.T P.D0 : ℝ)
      ≤ 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) := by
    intro i hi
    refine (NIID_chi_le_Q P hP (Zc i) (hmod i hi) hA₀ (hloc i hi)).trans ?_
    have hmodpos : (0 : ℝ) < (mod i : ℝ) := by
      have h1 : 1 < mod i := hmod i hi
      have h2 : 0 < mod i := by omega
      exact_mod_cast h2
    have h4T : (0 : ℝ) < 4 * P.T := by linarith
    rw [Real.log_mul (ne_of_gt hmodpos) (ne_of_gt h4T)]
    have hlm : Real.log (mod i : ℝ) ≤ P.LL :=
      le_trans (Real.log_le_log hmodpos (hmodQ i hi)) hlogQ
    have hcoef : (0 : ℝ) ≤ 3 * A₀ * P.D0 := by nlinarith
    exact mul_le_mul_of_nonneg_left (by linarith) hcoef
  calc (∑ i ∈ fam, (Zeta23.Assembly.NIID (Zc i) P.T P.D0 : ℝ))
      ≤ fam.card • (3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T))) :=
        Finset.sum_le_card_nsmul fam _ _ hterm
    _ = 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) * (fam.card : ℝ) := by
        rw [nsmul_eq_mul]; ring

/-! ## B.5 The explicit-and-linear-in-q constant ledger

Paper §9: "Every analytic constant in the chain is already explicit-and-linear in q in [R]'s own
development (‖L(s,χ)‖ ≤ q‖s‖/Re s; ‖L(w,χ)‖ ≤ 8q(|w.im|+3)); the uniformity is re-packaging, not
new analysis." Both bounds are located and re-exported so that the ledger is machine-checkable;
neither generates a sorry.

Anchor corrections recorded: NOTE_QF §QF.ii cites the half-plane bound at
`ThmE/LGrowth.lean:210` — it is at `:209` (docstring `:208`); and it cites
`‖L(w,χ)‖ ≤ 8q(|w.im|+3)` at `ThmE/LandauChi.lean:72`, which is a PROOF STEP, not a theorem — the
theorem is `Zeta23.ThmE.LFunction_growth_right_uniform` at `ThmE/LGrowth.lean:334`. -/

/-- **§9 ledger, half-plane bound.** `‖L(s,χ)‖ ≤ q‖s‖/Re s` for `Re s > 0` — linear in `q`.

Paper §9.
Depends on:
`Zeta23.ThmE.norm_LFunction_le_of_re_pos` (`Zeta23/ThmE/LGrowth.lean:209`).
Rule 17: CLEAN. `0 < s.re` is a half-plane condition on the COMPLEX VARIABLE, not on the
bandwidth. No λ, no X, no D₀.
Deliberately NOT named `norm_LFunction_le_of_re_pos`: that is the [R] name, and a same-base-name
re-export would be ambiguous in any file that opens both namespaces. -/
theorem ledger_norm_LFunction_le_q {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ q * ‖s‖ / s.re :=
  Zeta23.ThmE.norm_LFunction_le_of_re_pos hχ1 hs

/-- **§9 ledger, q-uniform growth with absolute constants.** `‖L(s,χ)‖ ≤ 8q(|Im s| + 3)` for
`Re s ≥ 0.15` — this is the input that keeps `log B` ADDITIVE in `log q`, hence the absolute `A₀`
of H6.

Paper §9.
Depends on:
`Zeta23.ThmE.LFunction_growth_right_uniform` (`Zeta23/ThmE/LGrowth.lean:334`).
Rule 17: CLEAN. `0.15 ≤ s.re` is a half-plane condition on the complex variable. -/
theorem ledger_norm_LFunction_le_eight_q {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) {s : ℂ} (hσ : (0.15 : ℝ) ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 8 * q * (|s.im| + 3) :=
  Zeta23.ThmE.LFunction_growth_right_uniform hχ1 hσ

/-! # PART C — the §9 → §3 FAMILY JOIN (`Budget.assembly_at_lamStar`, checklist item 3)

`ZetaQ.h1_block_free` (`ZetaQ/Certificate.lean`, sorry-free) is the per-block
H1 display at a FIXED `(Q, T)` and a FREE buffer `D`:

  `4 tr Â(D) − ‖Â(D)‖²_F − 2 N(T,2T) − 3 N_{II}(T,D) ≤ N₀ˢ(T,2T)`

for one `Zeta23.ZeroConfig` at one `Zeta23.Params`, in the hat units
`RHLinalg.rtrace (P.hat T (Z.AzD P T D))`. `ZetaQ.assembly_at_lamStar`'s clauses are
instead FAMILY DOUBLE SUMS over `ZetaQ.gridGram` — `trGhatFam`, `frobSqGhatFam`, `NfamQ`,
`N0sFamQ`, `NIIFamQ`. Both `ZetaQ/Budget.lean` and `Certificate.lean`'s §3.8 identify the
missing step as a §9/§7 join and place it HERE. This PART builds it.

**Import note (recorded as the precedent lines D26/D29 ask).** This file now carries
`import ZetaQ.Certificate` in addition to `ZetaQ.Defs`. The edge is ACYCLIC and was checked
before it was added: `ZetaQ.Certificate` imports `ZetaQ.Defs` and nothing else, and no file
imports `ZetaQ.EFChi` (`ZetaQ/Budget.lean` imports `Defs` and `Certificate`; `Ends` imports
`Defs`, `Sieve`, `Normalisation`; `Zones` imports `Defs`, `Sieve`, `CharSums`,
`Normalisation`). Precedents: D26 `Ends → Normalisation`, D29 `Zones → Normalisation`.

**What lands, and what does NOT.** `certificate_display_fam_of_bridge` is the export: it
produces `ZetaQ.CertificateDisplay` at the family aggregates from
  * `h1_block_free` per member, summed over `𝔉_Q` (this PART; NO hypothesis),
  * the per-character seam `FamZeroConfig` (this PART; discharged at `ZChi` by `ZChi_N` /
    `ZChi_N0s` for `1 < q`),
  * the §9 hat-normalisation bridge `FamGramBridge` (this PART; discharged per member by
    `rtrace_hatQ_gridGram_eq_Gz` / `frobSq_hatQ_gridGram_eq_Gz`, which are H2 = the Weil
    explicit formula `Gz(χ) = Gp(χ)` at density `ν_{X,χ}` composed with the grid bridge
    equations `dQ_eq`/`tauQ_eq`/`hatQ_eq`),
  * and **§7's pair split** `hpairTr` / `hpairF`, which is NOT §9's to supply — it is
    4's `ZetaQ.Tail` deliverable (`prop_tailQ` / `theta0Q_le_of_closing`), aggregated by the
    §7.3 mechanism (trace-additive, Frobenius-√-additive). Those two remain hypotheses here,
    named exactly as `ZetaQ.certificate_display_of_H1` consumes them, and they are the only
    inputs to the display that this file does not prove.

**🚩 FINDING (q = 1 is in the family, and its EF has a pole).** `ZetaQ.Family.moduli
Family.qle Qn = Finset.Icc 1 Qn` CONTAINS `1`, and `primitiveChars 1 = {1}` — the trivial
character mod 1, whose `L(·,χ)` is `ζ`. Both facts are machine-checked. So `𝔉_Q` for
Theorem 1's family has exactly one member for which `ZetaQ.H2_EF_of_primitive`'s `1 < q` (and
hence "no pole term", `ThmE/EFLitChi.lean:14`) is unavailable. Consequences, and why the join
below is unaffected:
  * The H1 half — `h1_fam`, the summation of `h1_block_free` — is **EF-FREE**: it needs no
    primitivity, no `1 < q`, and no explicit formula. It goes through for `q = 1` verbatim,
    at whatever `ZeroConfig` is supplied for `ζ`.
  * Only `FamGramBridge` (the `Ĝ`-side identification `gridGram = Gz`) needs `1 < q`, and
    only for the two moments `rtrace`/`frobSq`.
  * Hence `Zc` is carried ABSTRACTLY below (a function of `(q, χ)`), rather than being fixed
    to `ZChi`: that is what lets the assembly hand `ζ`'s own configuration to the
    `q = 1` member and `ZChi` to the rest. Fixing `Zc := ZChi` in the statement would make it
    unusable at `Family.qle` — which is Theorem 1's family.
  * Size of the defect if one instead drops the member: one character out of
    `|𝔉_Q| ≍ (18/π⁴)Q²`, contributing `≍ T·log T` to `𝒩 ≍ Q²Tℒ`, i.e. a relative `O(Q^{−2})`
    — far inside every budget row. Recorded, not exploited: nothing below drops it.

**⚠ THE FINDING ABOVE IS SUPERSEDED BY F32 — retained as a record, not as a live warning.**
`Family.moduli Family.qle Qn` is now `Finset.Icc 2 Qn` (`ZetaQ/Certificate.lean`, F32, decided
this pass): the `q = 1` member was REMOVED, precisely because its `L` is `ζ` and the no-pole
hypothesis fails there. The last bullet's "`Icc 1 Qn`" reading is therefore historical. Two
consequences, both realised in C.4a/C.5a/C.7 below:
  * `1 < q` IS available at every member of `𝔉_Q`, from `Finset.mem_Icc` (`qle`) or
    `Finset.mem_Ioc` with `2 ≤ Qn` (`dyadic`) — see `one_lt_of_mem_moduli`.
  * `Zc` therefore has a canonical total choice, `famZc` (`ZChi` on the good branch, the empty
    configuration off it), at which `FamZeroConfig` and `FamGramBridge` are THEOREMS
    (`famZeroConfig_famZc`, `famGramBridge_famZc`) rather than hypotheses. The abstract `Zc`
    is kept in every statement below — it is strictly more general and nothing is lost — but
    it is no longer FORCED by a `q = 1` member.
The other residue the join used to have, that nothing supplied `hφC2`/`hφsupp` from `P.Valid`,
is closed by C.0a (`phiQ_contDiff_two`, `phiQ_tsupport_subset`).

**Rule 17.** CLEAN throughout. The buffer is `P.D0`, a FIELD, everywhere (`AzD`,
`Zeta23.Assembly.NIID`, `NIIFamQ`); `Zeta23.D0`, `Zeta23.Assembly.NII`,
`Zeta23.ZeroConfig.Az`, `Zeta23.Tail.NII_le` and `Zeta23.Params.Valid` occur nowhere. The
validity class is `ZetaQ.ParamsQ.Valid` (no `lam_le_one`) and, through `toParams_validQ`,
`Zeta23.Params.ValidQ`. `hwL : 8 * P.w ≤ P.LB` is [R]'s `[eq:wrange]` at the paper's own
scale `L = λℒ` (§10.3's `SideCondWrange`), not a bandwidth cap: it bounds `w` above, not `λ`.
No hypothesis relates `P.XQ` to `P.T`. -/

/-! ## C.0 The scale facts `ParamsQ.Valid` already implies

These are what turn `hP : P.Valid` into the bridge's side conditions. They are stated here
rather than cited because `ZetaQ.Ends.LL_pos` lives in `ZetaQ/Ends.lean`, which imports `Sieve` and
`Normalisation` and is not on this file's import path. -/

/-- `0 < l T = log(T/2π)` at the design regime (`T ≥ 300` ⟹ `T/2π ≥ 47`).
Rule 17: `T ≥ 300` is `Valid.T_ge`, a window regime
fact, not a cap. -/
theorem l_pos_of_valid {P : ParamsQ} (hP : P.Valid) : 0 < Zeta23.l P.T := by
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hπ := Real.pi_pos
  refine Real.log_pos ?_
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Real.pi_le_four]

/-- `T ≠ 2π` — the hypothesis every `toParams` bridge equation carries, discharged from
`Valid`. -/
theorem l_ne_zero_of_valid {P : ParamsQ} (hP : P.Valid) : Zeta23.l P.T ≠ 0 :=
  ne_of_gt (l_pos_of_valid hP)

/-- `0 < ℒ = log(QT/2π)` (`Q ≥ 3`, `T ≥ 300` ⟹ `QT/2π ≥ 143`).
Rule 17: this is the q-aspect scale, NOT `Zeta23.l`. -/
theorem LL_pos_of_valid {P : ParamsQ} (hP : P.Valid) : 0 < P.LL := by
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hQ : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hπ := Real.pi_pos
  refine Real.log_pos ?_
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Real.pi_le_four]

/-- `0 < L = λℒ`.
Rule 17: POSITIVITY of the bandwidth scale. There is no upper bound on `P.lam` here beyond
`Valid.lam_lt_two`, and `λ* = 1.2507… > 1`. -/
theorem LB_pos_of_valid {P : ParamsQ} (hP : P.Valid) : 0 < P.LB :=
  mul_pos hP.lam_pos (LL_pos_of_valid hP)

/-- `0 < toParams.lam = λℒ / l T` — the ONE argument `ParamsQ.Valid.toParamsValidQ` does not
carry as a field, because `toParams.lam` is NOT `P.lam` (it is ≈ 18 at `Q = 10¹⁰⁰`).
Rule 17: this is the R-1 reparameterised bandwidth. Never "simplify" it to `P.lam`, and note
that no `≤ 1` and no `< 2` is claimed for it. -/
theorem toParams_lam_pos {P : ParamsQ} (hP : P.Valid) : 0 < P.toParams.lam := by
  show 0 < P.LB / Zeta23.l P.T
  exact div_pos (LB_pos_of_valid hP) (l_pos_of_valid hP)

/-! `toParams_validQ` (`P.Valid → P.toParams.ValidQ`) is GONE: the realising
profile `toParams.ϱ = x ↦ p((L/2 − w·x)/ℒ)·ϱ(x)` is not a `TaperProfile`, so
`P.toParams.ValidQ` is FALSE at every design point with a non-flat profile. Every former consumer
goes through `ZetaQ/Window.lean` (`ParamsQ.Valid.admWindow`, `Valid.poissonSq`, `Valid.aLsq_pos`,
…), i.e. [R]'s generic `AdmWindow` layer. -/

/-! ## C.0a The taper regularity facts `ParamsQ.Valid` implies

**Why these exist (finding of that stage).** `H2_Gz_eq_GpChi`, `Gz_eq_GpChi_Q`,
`rtrace_hatQ_gridGram_eq_Gz` and `frobSq_hatQ_gridGram_eq_Gz` all carry two hypotheses that,
until now, NOTHING in `ZetaQ` supplied:

    `hφC2   : ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ))`
    `hφsupp : tsupport P.phiQ ⊆ Set.Icc (-(P.LB/2)) (P.LB/2)`

A grep found them only as hypotheses, never as a conclusion — so every consumer of H2 was
blocked on an undischargeable side condition. They are NOT new mathematics: [R]'s tree proves
both, one layer beneath the `Params` façade, for the GENERIC taper `Zeta23.Taper.phi ϱ L w` at
free reals `L, w` with no `Params` and hence no `λ ≤ 1` anywhere in sight:

  * `Zeta23.Taper.phiC_contDiff_two` (`Zeta23/Taper/Fourier.lean:293`), from
    `Taper.phiC_contDiff` (`Taper/Strip.lean:29`) and `Taper.phi_contDiff`
    (`Taper/Basic.lean:161`) — hypotheses `TaperProfile ϱ`, `0 < w`, `2w ≤ L`;
  * `Zeta23.Taper.phi_support_subset` (`Taper/Basic.lean:135`) — hypotheses `TaperProfile ϱ`,
    `0 < w` only.

`ZetaQ.phiQ_eq` (`:307`) is the bridge that turns `P.phiQ` into that generic taper at
`(L, w) = (P.LB, P.w)`. So both facts follow from `P.Valid` alone (plus `[eq:wrange]` for the
`C²` half, which every intended instantiation carries).

Rule 17 for the whole subsection: `hwL : 2 * P.w ≤ P.LB` is the ADMISSIBILITY FLOOR of the
ramp (it bounds `w` ABOVE, not `λ`) and is implied by [R]'s `[eq:wrange]` `8w ≤ L`, §10.3's
`SideCondWrange`; `hP.one_le_w` is `Valid.one_le_w`, KEPT by HANDOVER §3 correction 2. No
`λ ≤ 1`, no `X ≤ T`, no `D₀ = √T` occurs, and `P.lam` is not bounded above at all. -/

/-- The ZetaQ taper IS the profile factor times [R]'s generic `Taper.phi` at
`(L, w) = (P.LB, P.w)`, as an equality of FUNCTIONS (`ZetaQ.phiQ_eq` is the pointwise form,
`ParamsQ.Valid.phiQ_eq` the `Window.lean` original).
Depends on: `ParamsQ.Valid.phiQ_eq`.
Rule 17: CLEAN — `hP` is `ParamsQ.Valid`, which has no `lam_le_one`. -/
theorem phiQ_eq_taper {P : ParamsQ} (hP : P.Valid) :
    P.phiQ = fun u => P.prof.eval (u / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u :=
  hP.phiQ_eq

/-- `0 < w`, from `Valid.one_le_w`.
Rule 17: CLEAN — a positivity fact about the RAMP WIDTH. -/
theorem w_pos_of_valid {P : ParamsQ} (hP : P.Valid) : 0 < P.w :=
  lt_of_lt_of_le zero_lt_one hP.one_le_w

/-- `[eq:wrange]`'s `8w ≤ L` implies the ramp construction's own floor `2w ≤ L`.
Rule 17: CLEAN — both sides bound `w`, neither bounds `λ`. -/
theorem two_w_le_of_wrange {P : ParamsQ} (hP : P.Valid) (hwL : 8 * P.w ≤ P.LB) :
    2 * P.w ≤ P.LB := by
  have := w_pos_of_valid hP
  linarith

/-- **`φ ∈ C³`, at ZetaQ's scale.** Depends on: `Zeta23.Taper.phi_contDiff` (`Zeta23/Taper/Basic.lean:161`).
Rule 17: CLEAN — `hwL : 2w ≤ L` bounds the ramp width, not the bandwidth. -/
theorem phiQ_contDiff_three {P : ParamsQ} (hP : P.Valid) (hwL : 2 * P.w ≤ P.LB) :
    ContDiff ℝ 3 P.phiQ :=
  hP.phiQ_contDiff_three hwL

/-- **`hφC2` DERIVED.** `ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ))` from `P.Valid` and
`[eq:wrange]`'s floor — the first of the two hypotheses that H2 and its two moment corollaries
carry and that nothing in `ZetaQ` previously supplied.
Paper §2.2 ("`φ ∈ C_c³(ℝ)`", the sentence after [eq:phidef]).
Depends on: `Zeta23.Taper.phiC_contDiff_two`
(`Zeta23/Taper/Fourier.lean:293`), `phiQ_eq_taper`.
Rule 17: CLEAN. `hwL : 2 * P.w ≤ P.LB` bounds the RAMP WIDTH above; `P.lam` is unconstrained
here (in particular `λ* = 1.2507… > 1` is fine, and larger `λ` only makes `hwL` easier). -/
theorem phiQ_contDiff_two {P : ParamsQ} (hP : P.Valid) (hwL : 2 * P.w ≤ P.LB) :
    ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ)) :=
  hP.phiC_contDiff_two hwL

/-- **`hφsupp` DERIVED, and with NO side condition beyond `P.Valid`.**
`tsupport P.phiQ ⊆ [−L/2, L/2]` — the second hypothesis H2 carries. Note that `[eq:wrange]` is
NOT needed: `Zeta23.Taper.phi_support_subset` asks only for `0 < w`, because `φ(u) = ϱ((L/2 −
|u|)/w)` vanishes for `|u| ≥ L/2` by `TaperProfile.eq_zero` alone; `Set.Icc` is closed, so
`closure_minimal` upgrades `support ⊆ Icc` to `tsupport ⊆ Icc`.
Paper §2.2 ("`supp φ = [−L/2, L/2]`").
Depends on: `Zeta23.Taper.phi_support_subset` (`Zeta23/Taper/Basic.lean:135`), `phiQ_eq_taper`.
Rule 17: CLEAN — the only input is `Valid.taper` and `Valid.one_le_w`. -/
theorem phiQ_tsupport_subset {P : ParamsQ} (hP : P.Valid) :
    tsupport P.phiQ ⊆ Set.Icc (-(P.LB / 2)) (P.LB / 2) :=
  hP.phiQ_tsupport_subset

/-- `φ` has compact support at ZetaQ's scale — the companion of `phiQ_tsupport_subset`,
recorded because consumers of the Fourier layer ask for it in this shape.
Depends on: `Zeta23.Taper.phi_hasCompactSupport`.
Rule 17: CLEAN, as `phiQ_tsupport_subset`. -/
theorem phiQ_hasCompactSupport {P : ParamsQ} (hP : P.Valid) : HasCompactSupport P.phiQ :=
  hP.phiQ_hasCompactSupport

/-! ## C.1 The grid bridge equations

`ParamsQ.toParams` makes [R]'s derived scale equal the paper's; §2.2's grid objects therefore
agree object by object. These are the equations the §3 ↔ §9 identification runs on. -/

/-- `d = ⌊LT/2π⌋` agrees with [R]'s `Params.d` at the bridge.
Depends on: `ParamsQ.toParams_L`.
Rule 17: `hl` is `T ≠ 2π`. -/
theorem dQ_eq (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) : P.dQ = P.toParams.d P.T := by
  simp only [ParamsQ.dQ, Zeta23.Params.d, P.toParams_L hl]

/-- `h = 2π/L` agrees with [R]'s `Params.hgrid`. -/
theorem hgridQ_eq (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) :
    P.hgridQ = P.toParams.hgrid P.T := by
  simp only [ParamsQ.hgridQ, Zeta23.Params.hgrid, P.toParams_L hl]

/-- `τ_k = T + kh` agrees with [R]'s `Params.tau`. -/
theorem tauQ_eq (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) (k : ℤ) :
    P.tauQ k = P.toParams.tau P.T k := by
  simp only [ParamsQ.tauQ, Zeta23.Params.tau, hgridQ_eq P hl]

/-- **The hat-unit agreement.** §3's `ZetaQ.hatQ` (`M ↦ M/(aL²)` at `a = P.aQ`, `L = P.LB`)
IS [R]'s `Zeta23.Params.hat` at the bridge. This is the normalisation half of the §9 join:
without it `trGhatFam` and `rtrace (P.hat T (Z.Gz P T))` are in different units.
Depends on: `ParamsQ.toParams_L` (`P.aQ` is
DEFINITIONALLY `P.toParams.a P.T`, so only `L` has to be bridged).
Rule 17: `hl` is `T ≠ 2π`. -/
theorem hatQ_eq (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) {n : Type*} (M : Matrix n n ℂ) :
    hatQ P M = P.toParams.hat P.T M := by
  simp only [hatQ, Zeta23.Params.hat, ParamsQ.aQ, P.toParams_L hl]
  push_cast
  ring_nf

/-! ## C.2 §9's `Ĝ`-side identification: `gridGram(χ)` in hat units IS `Ĝ_χ`

`ZetaQ.gridGramEntry` is the paper's `G(χ)_{kl} = ∫ φ̂(τ−τ_k)φ̂(τ−τ_l) ν_{X,χ}(τ)dτ`; [R]'s
`Zeta23.ThmE.GentryChi` is the same integral at `toParams`. Composing with H2
(`Gz_eq_GpChi_Q`, the Weil explicit formula with density `ν_{X,χ}` and NO pole term) turns the
PRIME-side family object of §3 into the ZERO-side matrix of §4, which is what
`h1_block_free` is about.

The two matrices live at different index types (`Fin P.dQ` vs `Fin (P.toParams.d P.T)`), equal
only up to `dQ_eq`, so the identification is made at the level of the two moments
`RHLinalg.rtrace` / `RHLinalg.frobSq` through `rtrace_frobSq_cast`. That is exactly the level
§3 consumes them at. -/

/-- The Gram entry of §3 IS [R]'s `GentryChi` at the bridge, at every pair of INTEGER indices
(no `Fin` cast involved).
Paper §3 / §2.2 (the density display).
Depends on: `tauQ_eq`, `ZetaQ.EFChi.nuQ_eq_nuXc`, `ParamsQ.phiHatQ`.
Rule 17: CLEAN. `hl` is `T ≠ 2π`; nothing relates `P.XQ` to `P.T` (and `X ≫ T` at λ*). -/
theorem gridGramEntry_eq (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (k l : ℤ) :
    gridGramEntry P χ k l
      = Zeta23.ThmE.GentryChi P.toParams (parity χ) q (fun n => χ (n : ZMod q)) P.T k l := by
  simp only [gridGramEntry, Zeta23.ThmE.GentryChi, ParamsQ.phiHatQ,
    tauQ_eq P hl, nuQ_eq_nuXc P hl]

/-- **The index-recast lemma.** `RHLinalg.rtrace` and `RHLinalg.frobSq` are invariant under
the `Fin`-index recast supplied by `dQ_eq`. Stated as a conjunction so the two consumers share
one entrywise hypothesis.
Rule 17: vacuous — no parameters occur. -/
theorem rtrace_frobSq_cast {a b : ℕ} (h : a = b)
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (hAB : ∀ i j : Fin a, A i j = B (Fin.cast h i) (Fin.cast h j)) :
    RHLinalg.rtrace A = RHLinalg.rtrace B ∧ RHLinalg.frobSq A = RHLinalg.frobSq B := by
  refine ⟨?_, ?_⟩
  · unfold RHLinalg.rtrace
    congr 1
    show ∑ i : Fin a, A i i = ∑ i : Fin b, B i i
    calc ∑ i : Fin a, A i i
        = ∑ i : Fin a, (fun j : Fin b => B j j) (Fin.cast h i) :=
          Finset.sum_congr rfl fun i _ => hAB i i
      _ = ∑ j : Fin b, B j j := Fin.sum_congr' (fun j : Fin b => B j j) h
  · rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq, Zeta23.Assembly.frobSq_eq_sum_norm_sq]
    calc ∑ i : Fin a, ∑ j : Fin a, ‖A i j‖ ^ 2
        = ∑ i : Fin a, (fun i' : Fin b => ∑ j : Fin b, ‖B i' j‖ ^ 2) (Fin.cast h i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc ∑ j : Fin a, ‖A i j‖ ^ 2
              = ∑ j : Fin a, (fun j' : Fin b => ‖B (Fin.cast h i) j'‖ ^ 2) (Fin.cast h j) :=
                Finset.sum_congr rfl fun j _ => by rw [hAB i j]
            _ = ∑ j : Fin b, ‖B (Fin.cast h i) j‖ ^ 2 :=
                Fin.sum_congr' (fun j' : Fin b => ‖B (Fin.cast h i) j'‖ ^ 2) h
      _ = ∑ i : Fin b, ∑ j : Fin b, ‖B i j‖ ^ 2 :=
          Fin.sum_congr' (fun i' : Fin b => ∑ j : Fin b, ‖B i' j‖ ^ 2) h

/-- Entrywise: §3's `Ĝ(χ)` is [R]'s hatted `GpChi` at the recast index.
Depends on: `hatQ_eq`'s ingredients, `gridGramEntry_eq`,
`dQ_eq`. Rule 17: CLEAN. -/
theorem hatQ_gridGram_entry (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (i j : Fin P.dQ) :
    hatQ P (gridGram P χ) i j
      = P.toParams.hat P.T
          (Zeta23.ThmE.GpChi P.toParams (parity χ) q (fun n => χ (n : ZMod q)) P.T)
          (Fin.cast (dQ_eq P hl) i) (Fin.cast (dQ_eq P hl) j) := by
  simp only [hatQ, Zeta23.Params.hat, Matrix.smul_apply, smul_eq_mul, gridGram,
    Zeta23.ThmE.GpChi, Fin.val_cast, gridGramEntry_eq P hl, ParamsQ.aQ, P.toParams_L hl]
  push_cast
  ring

/-- `tr Ĝ(χ)` (§3, prime side) `= tr` of [R]'s hatted `GpChi`. -/
theorem rtrace_hatQ_gridGram (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    RHLinalg.rtrace (hatQ P (gridGram P χ))
      = RHLinalg.rtrace (P.toParams.hat P.T
          (Zeta23.ThmE.GpChi P.toParams (parity χ) q (fun n => χ (n : ZMod q)) P.T)) :=
  (rtrace_frobSq_cast (dQ_eq P hl) _ _ (hatQ_gridGram_entry P hl χ)).1

/-- `‖Ĝ(χ)‖²_F` (§3, prime side) `= ‖·‖²_F` of [R]'s hatted `GpChi`. -/
theorem frobSq_hatQ_gridGram (P : ParamsQ) (hl : Zeta23.l P.T ≠ 0) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    RHLinalg.frobSq (hatQ P (gridGram P χ))
      = RHLinalg.frobSq (P.toParams.hat P.T
          (Zeta23.ThmE.GpChi P.toParams (parity χ) q (fun n => χ (n : ZMod q)) P.T)) :=
  (rtrace_frobSq_cast (dQ_eq P hl) _ _ (hatQ_gridGram_entry P hl χ)).2

/-- **§9's `Ĝ`-side identification, trace half.** `tr Ĝ(χ)` computed from §3's PRIME-side grid
Gram equals `tr Ĝ_χ` computed from the ZERO side, for primitive `χ` mod `q > 1`. This is H2 —
the Weil/Guinand explicit formula at density `ν_{X,χ}` with NO pole term — in the exact shape
§3's family aggregate needs.
Paper §3 ("by the q-uniform explicit formula (§9) this equals the zero-side
matrix") and §9 sentence 1.
Depends on: `rtrace_hatQ_gridGram`, `ZetaQ.EFChi.Gz_eq_GpChi_Q` (hence
`ZetaQ.H2_Gz_eq_GpChi` and `ZetaQ.H2_EF_of_primitive`).
Rule 17: CLEAN. `hL : 0 < P.LB` is positivity; the four hypotheses are exactly
`Gz_eq_GpChi_Q`'s. Do NOT add `hX : P.XQ ≤ P.T` — see the FLAG at `Gz_eq_GpChi_Q`. -/
theorem rtrace_hatQ_gridGram_eq_Gz (P : ParamsQ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hprim : χ.IsPrimitive)
    (hl : Zeta23.l P.T ≠ 0) (hL : 0 < P.LB)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ)))
    (hφsupp : tsupport P.phiQ ⊆ Set.Icc (-(P.LB / 2)) (P.LB / 2)) :
    RHLinalg.rtrace (hatQ P (gridGram P χ))
      = RHLinalg.rtrace (P.toParams.hat P.T ((ZChi hq hprim).Gz P.toParams P.T)) := by
  rw [rtrace_hatQ_gridGram P hl χ, Gz_eq_GpChi_Q P hq hprim hl hL hφC2 hφsupp]

/-- **§9's `Ĝ`-side identification, Frobenius half.** As `rtrace_hatQ_gridGram_eq_Gz`.
Rule 17: CLEAN, identical hypothesis set. -/
theorem frobSq_hatQ_gridGram_eq_Gz (P : ParamsQ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hprim : χ.IsPrimitive)
    (hl : Zeta23.l P.T ≠ 0) (hL : 0 < P.LB)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ)))
    (hφsupp : tsupport P.phiQ ⊆ Set.Icc (-(P.LB / 2)) (P.LB / 2)) :
    RHLinalg.frobSq (hatQ P (gridGram P χ))
      = RHLinalg.frobSq (P.toParams.hat P.T ((ZChi hq hprim).Gz P.toParams P.T)) := by
  rw [frobSq_hatQ_gridGram P hl χ, Gz_eq_GpChi_Q P hq hprim hl hL hφC2 hφsupp]

/-! ## C.3 `familySum` algebra

§3: "the direct sum over 𝔉_Q aggregates identically". Machine-checkably, that
is monotonicity plus the ONE linear combination the H1 display uses. -/

/-- `Σ_{χ ∈ 𝔉_Q}` is monotone. -/
theorem familySum_mono (F : Family) (Qn : ℕ)
    (f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (h : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q, f q χ ≤ g q χ) :
    familySum F Qn f ≤ familySum F Qn g := by
  unfold familySum
  exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ =>
    h q hq χ (F.chars_subset q hχ)

/-- The H1 linear combination commutes with `Σ_{χ ∈ 𝔉_Q}`: this is exactly §3's "the trace is
additive, `‖·‖²_F` is additive, `N` and `N_II` are additive".
Rule 17: n/a. -/
theorem familySum_h1comb (F : Family) (Qn : ℕ)
    (a b c d : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    familySum F Qn (fun q χ => 4 * a q χ - b q χ - 2 * c q χ - 3 * d q χ)
      = 4 * familySum F Qn a - familySum F Qn b - 2 * familySum F Qn c
        - 3 * familySum F Qn d := by
  unfold familySum
  have inner : ∀ q : ℕ, ∑ χ ∈ F.chars q, (4 * a q χ - b q χ - 2 * c q χ - 3 * d q χ)
      = 4 * (∑ χ ∈ F.chars q, a q χ) - (∑ χ ∈ F.chars q, b q χ)
        - 2 * (∑ χ ∈ F.chars q, c q χ) - 3 * (∑ χ ∈ F.chars q, d q χ) := by
    intro q
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun q _ => inner q)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]

/-! ## C.4 The per-character seam

`h1_block_free` speaks of a `Zeta23.ZeroConfig`'s own `N` / `N0s`; §3's aggregates are built
from `ZetaQ.NcountQ` / `ZetaQ.N0sQ`, which wrap `Zeta23.ThmE.NcountL` / `N0simpleL` through a
`dite` on `q = 0`. `FamZeroConfig` is that identification, member by member. -/

/-- **The per-character seam of the family join.** `Zc q χ` is a zero configuration whose
counts ARE the zero counts of `L(·,χ)` used by §3's aggregates, for every member of `𝔉_Q`.

**⚠ SUPERSEDED.** This bundle is now DERIVED at the canonical `famZc`:
`famZeroConfig_famZc` (C.4a). It is kept as a `Prop` because the abstract `Zc` is strictly
more general. Original note follows. Carried as a hypothesis rather than fixed to `ZChi` for
the reason recorded in PART C's header: `Family.qle`'s modulus range includes `q = 1`, whose
unique primitive character is the trivial character mod 1 (`L = ζ`), and `ZChi` needs `1 < q`.
For `1 < q` the two clauses are theorems — `ZChi_N` and `ZChi_N0s` below. (F32 removed the
`q = 1` member, so `1 < q` now holds on all of `𝔉_Q`; see `one_lt_of_mem_moduli`.)
Paper §1.1, §3. Rule 17: no parameter occurs. -/
structure FamZeroConfig (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig) : Prop where
  /-- the configuration's zero count with multiplicity is `N_χ` on every ordinate window. -/
  count : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q, ∀ T₁ T₂ : ℝ,
    (((Zc q χ).N T₁ T₂ : ℕ) : ℝ) = NcountQ q χ T₁ T₂
  /-- its simple-and-on-line count is `N^s_{0,χ}`. -/
  count0s : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q, ∀ T₁ T₂ : ℝ,
    (((Zc q χ).N0s T₁ T₂ : ℕ) : ℝ) = N0sQ q χ T₁ T₂

/-- `ZChi`'s zero count IS `ZetaQ.NcountQ` — the `count` clause of `FamZeroConfig`, discharged
for `1 < q`.
Depends on: `Zeta23.ThmE.LZeros_N`. Rule 17: parameter-free. -/
theorem ZChi_N {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) (T₁ T₂ : ℝ) :
    (((ZChi hq hprim).N T₁ T₂ : ℕ) : ℝ) = NcountQ q χ T₁ T₂ := by
  have h : (ZChi hq hprim).N T₁ T₂ = Zeta23.ThmE.NcountL χ T₁ T₂ :=
    Zeta23.ThmE.LZeros_N (Zeta23.ThmE.LSeam_of hq hprim) T₁ T₂
  rw [h]
  unfold NcountQ
  rw [dif_neg (show ¬ q = 0 by omega)]

/-- `ZChi`'s simple-on-line count IS `ZetaQ.N0sQ` — the `count0s` clause of `FamZeroConfig`,
discharged for `1 < q`. Note `N0sQ` wraps `N0simpleL` (on-line AND simple), which is [R]'s
`ZeroConfig.N0s` shape, NOT `N0star`.
Depends on: `Zeta23.ThmE.LZeros_N0s`. -/
theorem ZChi_N0s {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) (T₁ T₂ : ℝ) :
    (((ZChi hq hprim).N0s T₁ T₂ : ℕ) : ℝ) = N0sQ q χ T₁ T₂ := by
  have h : (ZChi hq hprim).N0s T₁ T₂ = Zeta23.ThmE.N0simpleL χ T₁ T₂ :=
    Zeta23.ThmE.LZeros_N0s (Zeta23.ThmE.LSeam_of hq hprim) T₁ T₂
  rw [h]
  unfold N0sQ
  rw [dif_neg (show ¬ q = 0 by omega)]

/-! ## C.4a The CANONICAL family zero configuration, and `FamZeroConfig` DERIVED

**The `q = 1` obstruction recorded in PART C's header is GONE.** F32 (`ZetaQ/Certificate.lean`,
`Family.moduli`) excluded `q = 1` from Theorem 1's family: `Family.moduli Family.qle Qn` is
`Finset.Icc 2 Qn`, not `Finset.Icc 1 Qn`. So `1 < q` is available at every member of `𝔉_Q`
from `Finset.mem_Icc` (`Finset.mem_Ioc` for the dyadic family, where `Qn/2 ≥ 1` needs
`2 ≤ Qn`), and `ZChi` — which needs exactly `1 < q` and primitivity — is available member by
member. `FamZeroConfig` and `FamGramBridge` therefore no longer have to be ASSUMED: this
subsection and C.5a DERIVE them at one canonical `Zc`.

The canonical `Zc` has to be TOTAL in `(q, χ)` while `ZChi` is partial, so it is a `dite` with
a junk branch. `emptyZeroConfig` (carrier `∅`) is the junk value: every field of
`Zeta23.ZeroConfig` is a `∀ ρ ∈ carrier` clause except `finite_window`, which is
`Set.finite_empty` — so the empty configuration is legal, and it is never reached on `𝔉_Q`.

Rule 17 for the whole subsection: no bandwidth, no `X`, no buffer occurs. `hQn : 2 ≤ Qn` is a
size floor on the FAMILY index, not on `λ`. -/

/-- Membership in the frozen `ZetaQ.primitiveChars` gives primitivity. (`ZetaQ.Sieve` has the
`iff` form, but `ZetaQ/Sieve.lean` is not on this file's import path — this file imports
`ZetaQ.Defs` and `ZetaQ.Certificate` only, and the PART C header's acyclicity check must stay
true.)
Rule 17: no parameter occurs. -/
theorem isPrimitive_of_mem_primitiveChars {q : ℕ} {χ : DirichletCharacter ℂ q}
    (h : χ ∈ primitiveChars q) : χ.IsPrimitive := by
  classical
  simpa [primitiveChars] using h

/-- **`1 < q` at every member of `𝔉_Q`** — the fact F32 made available and the reason the two
bundles below are theorems rather than hypotheses. `qle`'s range is `Finset.Icc 2 Qn`;
`dyadic`'s is `Finset.Ioc (Qn/2) Qn`, which excludes `q = 1` as soon as `Qn ≥ 2`.
Depends on: `ZetaQ.Family.moduli`.
Rule 17: CLEAN — `hQn` bounds the family index below; nothing here mentions `λ`, `X` or `D₀`. -/
theorem one_lt_of_mem_moduli {F : Family} {Qn q : ℕ} (hQn : 2 ≤ Qn)
    (hq : q ∈ F.moduli Qn) : 1 < q := by
  cases F with
  | qle =>
      have h : q ∈ Finset.Icc 2 Qn := hq
      rw [Finset.mem_Icc] at h
      omega
  | dyadic =>
      have h : q ∈ Finset.Ioc (Qn / 2) Qn := hq
      rw [Finset.mem_Ioc] at h
      omega
  | evenQle =>
      have h : q ∈ Finset.Icc 2 Qn := hq
      rw [Finset.mem_Icc] at h
      omega
  | oddQle =>
      have h : q ∈ Finset.Icc 2 Qn := hq
      rw [Finset.mem_Icc] at h
      omega
  | evenDyadic =>
      have h : q ∈ Finset.Ioc (Qn / 2) Qn := hq
      rw [Finset.mem_Ioc] at h
      omega
  | oddDyadic =>
      have h : q ∈ Finset.Ioc (Qn / 2) Qn := hq
      rw [Finset.mem_Ioc] at h
      omega
  | evenQleR =>
      have h : q ∈ Finset.Icc 2 Qn := hq
      rw [Finset.mem_Icc] at h
      omega
  | oddQleR =>
      have h : q ∈ Finset.Icc 2 Qn := hq
      rw [Finset.mem_Icc] at h
      omega
  | evenDyadicR =>
      have h : q ∈ Finset.Ioc (Qn / 2) Qn := hq
      rw [Finset.mem_Ioc] at h
      omega
  | oddDyadicR =>
      have h : q ∈ Finset.Ioc (Qn / 2) Qn := hq
      rw [Finset.mem_Ioc] at h
      omega

/-- **`1 < q` on Theorem 1's family, with NO hypothesis on `Qn`** — `Finset.Icc 2 Qn` is empty
for `Qn ≤ 1`, so the `2 ≤ Qn` of `one_lt_of_mem_moduli` is not needed in the `qle` case.
Rule 17: CLEAN. -/
theorem one_lt_of_mem_moduli_qle {Qn q : ℕ} (hq : q ∈ Family.qle.moduli Qn) : 1 < q := by
  have h : q ∈ Finset.Icc 2 Qn := hq
  rw [Finset.mem_Icc] at h
  omega

/-- The junk branch of `famZc`: the EMPTY zero configuration. Every field of
`Zeta23.ZeroConfig` except `finite_window` is a `∀ ρ ∈ carrier` clause, hence vacuous at
`carrier = ∅`; `finite_window` is `Set.finite_empty`. It is never reached on `𝔉_Q`.
Rule 17: no parameter occurs. -/
def emptyZeroConfig : Zeta23.ZeroConfig where
  carrier := ∅
  mult := fun _ => 1
  one_le_mult := fun _ h => h.elim
  strip := fun _ h => h.elim
  reflect_mem := fun _ h => h.elim
  mult_reflect := fun _ h => h.elim
  finite_window := fun _ _ => by
    rw [Set.empty_inter]
    exact Set.finite_empty

open Classical in
/-- **The canonical family zero configuration.** `ZChi` where it is defined (`1 < q` and `χ`
primitive), `emptyZeroConfig` elsewhere. This is the `Zc` at which `FamZeroConfig` and
`FamGramBridge` are DERIVED (C.4a, C.5a), so that
`certificate_display_fam_of_bridge`/`prop31_fam` can be applied with those two bundles
discharged rather than assumed (`certificate_display_fam_derived`, `prop31_fam_derived`).

PART C's header carries `Zc` abstractly for the historical reason that `Family.qle` used to
contain `q = 1`; F32 removed that member, so a canonical total choice now exists. The abstract
form is kept — nothing below changes it — because it is strictly more general.
Depends on: `ZetaQ.ZChi`, `emptyZeroConfig`.
Rule 17: no parameter occurs (`Zeta23.ZeroConfig` is `Params`-free). -/
def famZc (q : ℕ) (χ : DirichletCharacter ℂ q) : Zeta23.ZeroConfig :=
  if h : 1 < q ∧ χ.IsPrimitive then
    haveI : NeZero q := ⟨by have := h.1; omega⟩
    ZChi h.1 h.2
  else emptyZeroConfig

/-- On the good branch `famZc` IS `ZChi`.
Rule 17: no parameter occurs. -/
theorem famZc_eq_ZChi {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) : famZc q χ = ZChi hq hprim := by
  classical
  unfold famZc
  rw [dif_pos (⟨hq, hprim⟩ : 1 < q ∧ χ.IsPrimitive)]

/-- **🟢 `FamZeroConfig` DERIVED, not assumed.** The per-character seam holds at the canonical
`famZc`, for either family, as soon as `2 ≤ Qn`.

This is `ZChi_N` / `ZChi_N0s` — both already proved and, until here, ORPHANS (nothing
in the project cited them) — applied member by member, with `1 < q` supplied by
`one_lt_of_mem_moduli` (i.e. by F32) and primitivity by `isPrimitive_of_mem_primitiveChars`.
Paper §1.1, §3.
Depends on: `ZChi_N`, `ZChi_N0s`, `famZc_eq_ZChi`, `one_lt_of_mem_moduli`.
Rule 17: CLEAN — no `Params` occurs at all, so no λ, no X, no D₀. -/
theorem famZeroConfig_famZc (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn) :
    FamZeroConfig F Qn famZc := by
  constructor
  · intro q hq χ hχ T₁ T₂
    have hq1 : 1 < q := one_lt_of_mem_moduli hQn hq
    have : NeZero q := ⟨by omega⟩
    have hp : χ.IsPrimitive := isPrimitive_of_mem_primitiveChars hχ
    rw [famZc_eq_ZChi hq1 hp]
    exact ZChi_N hq1 hp T₁ T₂
  · intro q hq χ hχ T₁ T₂
    have hq1 : 1 < q := one_lt_of_mem_moduli hQn hq
    have : NeZero q := ⟨by omega⟩
    have hp : χ.IsPrimitive := isPrimitive_of_mem_primitiveChars hχ
    rw [famZc_eq_ZChi hq1 hp]
    exact ZChi_N0s hq1 hp T₁ T₂

/-- **🟢 `FamZeroConfig` on Theorem 1's family, with no floor on `Qn`.**
Rule 17: CLEAN. -/
theorem famZeroConfig_famZc_qle (Qn : ℕ) : FamZeroConfig Family.qle Qn famZc := by
  constructor
  · intro q hq χ hχ T₁ T₂
    have hq1 : 1 < q := one_lt_of_mem_moduli_qle hq
    have : NeZero q := ⟨by omega⟩
    have hp : χ.IsPrimitive := isPrimitive_of_mem_primitiveChars hχ
    rw [famZc_eq_ZChi hq1 hp]
    exact ZChi_N hq1 hp T₁ T₂
  · intro q hq χ hχ T₁ T₂
    have hq1 : 1 < q := one_lt_of_mem_moduli_qle hq
    have : NeZero q := ⟨by omega⟩
    have hp : χ.IsPrimitive := isPrimitive_of_mem_primitiveChars hχ
    rw [famZc_eq_ZChi hq1 hp]
    exact ZChi_N0s hq1 hp T₁ T₂

/-! ## C.5 The family aggregates of the per-block matrices

Four family sums, in the units `h1_block_free` speaks: the truncated block `Â_χ(D₀)` at the
FREE buffer, and the full block `Ĝ_χ`. `Certificate.certificate_display_of_H1` carries
`trAfam`/`frobSqAfam` as free reals precisely so that these can be plugged in. -/

/-- `tr Â_fam(D₀) := Σ_{χ ∈ 𝔉_Q} tr Â_χ(D₀)` — the family trace of the TRUNCATED zero-side
blocks at the FREE buffer `P.D0`.
Paper §3, §7.3.
**Rule 17: `P.D0` is a FIELD.** `Zeta23.ZeroConfig.AzD` (`Tail/GevreyTail.lean:1423`) sums
over `ZIprimeD T D` at a free `D`; `Zeta23.ZeroConfig.Az` (at `√T`) is NOT used. -/
def trAhatFam (P : ParamsQ) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig) : ℝ :=
  familySum F Qn fun q χ =>
    RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))

/-- `‖Â_fam(D₀)‖²_F := Σ_{χ ∈ 𝔉_Q} ‖Â_χ(D₀)‖²_F`. Rule 17: as `trAhatFam`. -/
def frobSqAhatFam (P : ParamsQ) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig) : ℝ :=
  familySum F Qn fun q χ =>
    RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))

/-- `tr Ĝ_fam` computed on the ZERO side — the object §7's tail compares with `trAhatFam`.
Rule 17: no buffer occurs (`Gz` is the FULL matrix). -/
def trGzFam (P : ParamsQ) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig) : ℝ :=
  familySum F Qn fun q χ =>
    RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).Gz P.toParams P.T))

/-- `‖Ĝ_fam‖²_F` computed on the ZERO side. Rule 17: as `trGzFam`. -/
def frobSqGzFam (P : ParamsQ) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig) : ℝ :=
  familySum F Qn fun q χ =>
    RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).Gz P.toParams P.T))

/-- `‖Â_fam(D₀)‖²_F ≥ 0` — the sign fact `certificate_display_of_H1`'s `hfrA` needs, free
because the aggregate is a double sum of `RHLinalg.frobSq` values.
-/
theorem frobSqAhatFam_nonneg (P : ParamsQ) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig) :
    0 ≤ frobSqAhatFam P F Qn Zc := by
  unfold frobSqAhatFam familySum
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Zeta23.Assembly.frobSq_nonneg _

/-- **§9's `Ĝ`-side bridge at family level**, as a two-clause `Prop`: per member of `𝔉_Q`, §3's
prime-side grid Gram in hat units has the same trace and the same Frobenius square as the
zero-side block `Ĝ_χ` at the bridge.

Discharged member by member by `rtrace_hatQ_gridGram_eq_Gz` / `frobSq_hatQ_gridGram_eq_Gz`
once `Zc` is fixed — i.e. this Prop IS H2, aggregated.

**⚠ SUPERSEDED.** **The `q = 1` obstruction recorded below no longer exists.**  F32 changed
`Family.moduli Family.qle` to `Finset.Icc 2 Qn` (`Certificate.lean`), so `1 < q` is available at
every family member from `Finset.mem_Icc`, and the four clauses this bundles (`ZChi_N`,
`ZChi_N0s`, `rtrace_hatQ_gridGram_eq_Gz`, `frobSq_hatQ_gridGram_eq_Gz`) are all PROVED and
sorry-free.  **The residue that note recorded — that nothing in `ZetaQ` supplied
`ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ))` or `tsupport P.phiQ ⊆ Icc (-(LB/2)) (LB/2)` from
`P.Valid` — IS NOW CLOSED** by C.0a (`phiQ_contDiff_two`, `phiQ_tsupport_subset`), and this
bundle is consequently DERIVED at the canonical `famZc` by `famGramBridge_famZc` (C.5a). It is
kept as a `Prop` only because the abstract `Zc` is strictly more general.
Original note follows.  It is stated rather than derived
because the derivation needs `1 < q` and `Family.qle` contains `q = 1` (PART C header,
🚩 FINDING).
Paper §3, §9. Rule 17: no forbidden hypothesis;
`Zc` is abstract and the buffer does not occur. -/
structure FamGramBridge (P : ParamsQ) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig) : Prop where
  /-- `tr Ĝ(χ)` agrees on the two sides. -/
  tr : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
    RHLinalg.rtrace (hatQ P (gridGram P χ))
      = RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).Gz P.toParams P.T))
  /-- `‖Ĝ(χ)‖²_F` agrees on the two sides. -/
  frobSq : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
    RHLinalg.frobSq (hatQ P (gridGram P χ))
      = RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).Gz P.toParams P.T))

/-- `tr Ĝ_fam` of §3 (prime side, `gridGram`) `=` `tr Ĝ_fam` on the zero side.
-/
theorem trGhatFam_eq_trGzFam (P : ParamsQ) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hB : FamGramBridge P F Qn Zc) :
    trGhatFam P F Qn = trGzFam P F Qn Zc := by
  unfold trGhatFam trGzFam familySum
  exact Finset.sum_congr rfl fun q hq =>
    Finset.sum_congr rfl fun χ hχ => hB.tr q hq χ (F.chars_subset q hχ)

/-- `‖Ĝ_fam‖²_F` of §3 `=` `‖Ĝ_fam‖²_F` on the zero side.
-/
theorem frobSqGhatFam_eq_frobSqGzFam (P : ParamsQ) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hB : FamGramBridge P F Qn Zc) :
    frobSqGhatFam P F Qn = frobSqGzFam P F Qn Zc := by
  unfold frobSqGhatFam frobSqGzFam familySum
  exact Finset.sum_congr rfl fun q hq =>
    Finset.sum_congr rfl fun χ hχ => hB.frobSq q hq χ (F.chars_subset q hχ)

/-! ## C.5a `FamGramBridge` DERIVED

The last of the four ingredients. `rtrace_hatQ_gridGram_eq_Gz` / `frobSq_hatQ_gridGram_eq_Gz`
(both proved, both ORPHANS until here) each need six inputs; five of them are now
supplied from `P.Valid` alone — `hl` by `l_ne_zero_of_valid`, `hL` by `LB_pos_of_valid`,
`hφC2` by `phiQ_contDiff_two` (C.0a), `hφsupp` by `phiQ_tsupport_subset` (C.0a), `1 < q` by
`one_lt_of_mem_moduli` — and the sixth, primitivity, by membership in `primitiveChars`.

Rule 17: `hwL : 8 * P.w ≤ P.LB` is [R]'s `[eq:wrange]`, §10.3's `SideCondWrange`; it is used
only through `two_w_le_of_wrange` to feed the ramp's admissibility floor `2w ≤ L`, which bounds
the RAMP WIDTH, not the bandwidth. `hQn : 2 ≤ Qn` bounds the family index. Nothing here says
`λ ≤ 1`, `X ≤ T` or `D₀ = √T`, and the buffer does not occur at all. -/

/-- **🟢 `FamGramBridge` DERIVED, not assumed.** §9's `Ĝ`-side identification holds at the
canonical `famZc` for either family, from `P.Valid` and `[eq:wrange]`.

This is H2 — the Weil/Guinand explicit formula `Gz(χ) = Gp(χ)` at density `ν_{X,χ}` with no
pole term — aggregated over `𝔉_Q`. Its docstring's claim that it "is stated rather than derived
because the derivation needs `1 < q` and `Family.qle` contains `q = 1`" is stale twice over:
F32 removed `q = 1` from `Family.qle`, and C.0a now supplies the two taper hypotheses.
Paper §3 + §9 sentence 1.
Depends on: `rtrace_hatQ_gridGram_eq_Gz`, `frobSq_hatQ_gridGram_eq_Gz`, `phiQ_contDiff_two`,
`phiQ_tsupport_subset`, `famZc_eq_ZChi`, `one_lt_of_mem_moduli`, `LB_pos_of_valid`.
**Rule 17: CLEAN.** `hL : 0 < P.LB` is positivity; `hwL` bounds `w`; do NOT add
`hX : P.XQ ≤ P.T` (see the FLAG at `Gz_eq_GpChi_Q`). -/
theorem famGramBridge_famZc (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ)
    (hQn : 2 ≤ Qn) (hwL : 8 * P.w ≤ P.LB) :
    FamGramBridge P F Qn famZc := by
  have hl := l_ne_zero_of_valid hP
  have hL := LB_pos_of_valid hP
  have hC2 := phiQ_contDiff_two hP (two_w_le_of_wrange hP hwL)
  have hsupp := phiQ_tsupport_subset hP
  constructor
  · intro q hq χ hχ
    have hq1 : 1 < q := one_lt_of_mem_moduli hQn hq
    have : NeZero q := ⟨by omega⟩
    have hp : χ.IsPrimitive := isPrimitive_of_mem_primitiveChars hχ
    rw [famZc_eq_ZChi hq1 hp]
    exact rtrace_hatQ_gridGram_eq_Gz P hq1 hp hl hL hC2 hsupp
  · intro q hq χ hχ
    have hq1 : 1 < q := one_lt_of_mem_moduli hQn hq
    have : NeZero q := ⟨by omega⟩
    have hp : χ.IsPrimitive := isPrimitive_of_mem_primitiveChars hχ
    rw [famZc_eq_ZChi hq1 hp]
    exact frobSq_hatQ_gridGram_eq_Gz P hq1 hp hl hL hC2 hsupp

/-- **🟢 `FamGramBridge` on Theorem 1's family, with no floor on `Qn`.**
Rule 17: CLEAN, as `famGramBridge_famZc`. -/
theorem famGramBridge_famZc_qle (P : ParamsQ) (hP : P.Valid) (Qn : ℕ)
    (hwL : 8 * P.w ≤ P.LB) :
    FamGramBridge P Family.qle Qn famZc := by
  have hl := l_ne_zero_of_valid hP
  have hL := LB_pos_of_valid hP
  have hC2 := phiQ_contDiff_two hP (two_w_le_of_wrange hP hwL)
  have hsupp := phiQ_tsupport_subset hP
  constructor
  · intro q hq χ hχ
    have hq1 : 1 < q := one_lt_of_mem_moduli_qle hq
    have : NeZero q := ⟨by omega⟩
    have hp : χ.IsPrimitive := isPrimitive_of_mem_primitiveChars hχ
    rw [famZc_eq_ZChi hq1 hp]
    exact rtrace_hatQ_gridGram_eq_Gz P hq1 hp hl hL hC2 hsupp
  · intro q hq χ hχ
    have hq1 : 1 < q := one_lt_of_mem_moduli_qle hq
    have : NeZero q := ⟨by omega⟩
    have hp : χ.IsPrimitive := isPrimitive_of_mem_primitiveChars hχ
    rw [famZc_eq_ZChi hq1 hp]
    exact frobSq_hatQ_gridGram_eq_Gz P hq1 hp hl hL hC2 hsupp

/-! ## C.6 THE JOIN -/

/-- **🟢 §9 → §3, the H1 display SUMMED OVER `𝔉_Q`, at a FIXED `(Q,T)` and a FREE buffer.
PROVED, and with NO explicit-formula input.**

  `4 tr Â_fam(D₀) − ‖Â_fam(D₀)‖²_F − 2𝒩 − 3 N_{II,fam} ≤ Σ_χ N^s_{0,χ}(T,2T)`

This is `ZetaQ.h1_block_free` (per block, sorry-free, Q2 closed) applied at each member of
`𝔉_Q` and summed. The only per-member inputs are the seam `FamZeroConfig` and the two side
conditions of the rank–trace engine, both threaded from `hP : P.Valid` and `hwL : 8w ≤ L`;
**no primitivity, no `1 < q`, no explicit formula and no zero-density input appears**, which
is what makes the display valid for the `q = 1` member too (PART C header).

Paper §3 (H1).
Depends on: `ZetaQ.h1_block_free`, `ZetaQ.NIIfree_eq`, `familySum_h1comb`, `familySum_mono`,
`toParams_validQ`, `l_ne_zero_of_valid`.
**Rule 17: CLEAN, and this is the pressure point of the whole join.** The buffer is `P.D0`, a
FIELD, in all four places it occurs (`AzD`, `Zeta23.Assembly.NIID`, `NIIFamQ`, and the two
regime facts `2 ≤ P.D0`, `P.D0 + 4 ≤ P.T` from `Valid`). `Zeta23.D0`,
`Zeta23.Assembly.NII`, `Zeta23.ZeroConfig.Az` and `Zeta23.Tail.NII_le` occur NOWHERE.
`hwL : 8 * P.w ≤ P.LB` is [R]'s `[eq:wrange]` at the paper's scale — an upper bound on the
RAMP WIDTH, not on the bandwidth; `P.lam` is unbounded above here except by
`Valid.lam_lt_two`, and `λ* = 1.2507… > 1`. -/
theorem h1_fam (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hZc : FamZeroConfig F Qn Zc) (hwL : 8 * P.w ≤ P.LB) :
    4 * trAhatFam P F Qn Zc - frobSqAhatFam P F Qn Zc
        - 2 * NfamQ P F Qn - 3 * NIIFamQ P F Qn
      ≤ N0sFamQ P F Qn := by
  have hl := l_ne_zero_of_valid hP
  -- the two analytic inputs of `h1_block_free`, from the product window's `AdmWindow`
  -- instance (`ZetaQ/Window.lean`) instead of the flat facade's `P.toParams.ValidQ`.
  have haLsq := hP.aLsq_pos
  have hPois := hP.poissonSq hwL
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT : (0 : ℝ) ≤ P.T := by linarith
  have hD : (0 : ℝ) ≤ P.D0 := by have := hP.two_le_D0; linarith
  -- the per-member display, in the vocabulary of §3's aggregates
  have hstep : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      4 * RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))
        - RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))
        - 2 * NcountQ q χ P.T (2 * P.T)
        - 3 * (NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0))
        ≤ N0sQ q χ P.T (2 * P.T) := by
    intro q hq χ hχ
    have hb := h1_block_free_of_poisson (Zc q χ) P.T P.D0 P.toParams hT hD haLsq hPois
    rw [NIIfree_eq] at hb
    simp only [hZc.count q hq χ hχ, hZc.count0s q hq χ hχ] at hb
    linarith
  have hcomb := familySum_h1comb F Qn
    (fun q χ => RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0)))
    (fun q χ => RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0)))
    (fun q χ => NcountQ q χ P.T (2 * P.T))
    (fun q χ => NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0))
  have hle := familySum_mono F Qn
    (fun q χ =>
      4 * RHLinalg.rtrace (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))
        - RHLinalg.frobSq (P.toParams.hat P.T ((Zc q χ).AzD P.toParams P.T P.D0))
        - 2 * NcountQ q χ P.T (2 * P.T)
        - 3 * (NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0)))
    (fun q χ => N0sQ q χ P.T (2 * P.T)) hstep
  have h1 : NfamQ P F Qn = familySum F Qn (fun q χ => NcountQ q χ P.T (2 * P.T)) := rfl
  have h2 : NIIFamQ P F Qn
      = familySum F Qn (fun q χ =>
          NcountQ q χ (P.T - P.D0) P.T + NcountQ q χ (2 * P.T) (2 * P.T + P.D0)) := rfl
  have h3 : N0sFamQ P F Qn = familySum F Qn (fun q χ => N0sQ q χ P.T (2 * P.T)) := rfl
  unfold trAhatFam frobSqAhatFam
  rw [h1, h2, h3]
  linarith

/-- **🟢 §3's family certificate display (H1) from the per-block H1. PROVED.**

`ZetaQ.CertificateDisplay` at the family aggregates — i.e. exactly

  `4 tr Ĝ_fam − ‖Ĝ_fam‖²_F − 2𝒩 − 3N_{II,fam} − [4B_tr + 2B_F‖Ĝ_fam‖_F + B_F²] ≤ Σ_χ N^s_{0,χ}`

with `tr Ĝ_fam = ZetaQ.trGhatFam`, `‖Ĝ_fam‖²_F = ZetaQ.frobSqGhatFam` (both built from
`ZetaQ.gridGram`), `𝒩 = NfamQ`, `N_{II,fam} = NIIFamQ` at the FREE `P.D0`, and
`Σ_χ N^s_{0,χ} = N0sFamQ`.

Route: `h1_fam` (the summed per-block display) into `ZetaQ.certificate_display_of_H1` (§7.3's
pair perturbation at the family level).

The two remaining hypotheses `hpairTr`/`hpairF` are **§7's**, not §9's: they are the pair
split of paper §7.3 ("the trace is additive, `|tr Ê_fam| ≤ |𝔉|θ₀/(aL) =:
B_tr`; the Frobenius norm is √-additive, `‖Ê_fam‖_F ≤ √|𝔉|·θ₀/(aL) =: B_F`"), to be supplied
from `ZetaQ.Tail`'s per-character `θ₀`. They are stated here in the `gridGram` vocabulary;
`certificate_display_fam_of_bridge` below is the same statement with them in the ZERO-side
vocabulary §7 actually works in.

Paper §3 + §7.3.
Depends on: `h1_fam`, `frobSqAhatFam_nonneg`,
`ZetaQ.certificate_display_of_H1`.
**Rule 17: CLEAN.** `NIIFamQ P F Qn = NIIFam F Qn P.T P.D0` at the FREE field; `hP` is
`ZetaQ.ParamsQ.Valid` (no `lam_le_one`); `hwL` bounds `w`, not `λ`; nothing relates `P.XQ`
to `P.T`. -/
theorem certificate_display_fam (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) (θ₀ : ℝ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hZc : FamZeroConfig F Qn Zc) (hwL : 8 * P.w ≤ P.LB)
    (hpairTr : |trGhatFam P F Qn - trAhatFam P F Qn Zc| ≤ Btr P F Qn θ₀)
    (hpairF : Real.sqrt (frobSqAhatFam P F Qn Zc)
                - Real.sqrt (frobSqGhatFam P F Qn) ≤ BF P F Qn θ₀)
    (hBtr : 0 ≤ Btr P F Qn θ₀) (hBF : 0 ≤ BF P F Qn θ₀) :
    CertificateDisplay (N0sFamQ P F Qn) (NfamQ P F Qn) (NIIFamQ P F Qn)
      (trGhatFam P F Qn) (frobSqGhatFam P F Qn) (Btr P F Qn θ₀) (BF P F Qn θ₀) :=
  certificate_display_of_H1 P hP F Qn θ₀ (trAhatFam P F Qn Zc) (frobSqAhatFam P F Qn Zc)
    (frobSqAhatFam_nonneg P F Qn Zc) (h1_fam P hP F Qn Zc hZc hwL) hpairTr hpairF hBtr hBF

/-- **🟢🟢 THE EXPORT: §3's family certificate display, with the tail hypotheses in the
ZERO-SIDE vocabulary §7 works in. PROVED.**

This is the object `ZetaQ.assembly_at_lamStar`'s checklist item 3 asks for. It is
`certificate_display_fam` with `hpairTr`/`hpairF` written against `trGzFam`/`frobSqGzFam`
(the family aggregates of `Ĝ_χ = P.hat T (Z_χ.Gz P T)`) instead of against §3's
`trGhatFam`/`frobSqGhatFam`, the two being identified by `FamGramBridge` — i.e. by H2, the
Weil explicit formula. So the four inputs are, in order:

  1. `hZc : FamZeroConfig F Qn Zc` — the per-character seam. **§9, discharged here** for
     `1 < q` by `ZChi_N` / `ZChi_N0s`.
  2. `hB : FamGramBridge P F Qn Zc` — the `Ĝ`-side identification. **§9, discharged here**
     per member by `rtrace_hatQ_gridGram_eq_Gz` / `frobSq_hatQ_gridGram_eq_Gz`, whose content
     is `H2_Gz_eq_GpChi` + `H2_EF_of_primitive` + the grid bridge equations of C.1.
  3. `hwL : 8 * P.w ≤ P.LB` — [R]'s `[eq:wrange]`, §10.3's `SideCondWrange`.
  4. `hpairTr` / `hpairF` — **§7's pair split, the ONLY input this file does not prove.**
     `|tr Ĝ_fam − tr Â_fam| ≤ B_tr` and `‖Â_fam‖_F ≤ ‖Ĝ_fam‖_F + B_F` (paper §7.3), to come
     from `ZetaQ.Tail`'s per-character `θ₀` bound plus the direct-sum aggregation.

**How `Budget` should consume it.** `assembly_at_lamStar`'s LAST conclusion clause follows by
`prop31_fam` below (this display + the four §§4–6 row clauses), then the trivial monotonicity
step `bracket ≤ budgetTotal F P` against `0 ≤ NfamQ` (`ZetaQ.NfamQ_nonneg`). The other
clauses are §§4–6's rows and §10's design construction, untouched by this file.

Paper §3 + §7.3 + §9.
Depends on: `certificate_display_fam`, `trGhatFam_eq_trGzFam`,
`frobSqGhatFam_eq_frobSqGzFam`.
**Rule 17: CLEAN**, identically to `certificate_display_fam`. -/
theorem certificate_display_fam_of_bridge
    (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) (θ₀ : ℝ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hZc : FamZeroConfig F Qn Zc) (hB : FamGramBridge P F Qn Zc) (hwL : 8 * P.w ≤ P.LB)
    (hpairTr : |trGzFam P F Qn Zc - trAhatFam P F Qn Zc| ≤ Btr P F Qn θ₀)
    (hpairF : Real.sqrt (frobSqAhatFam P F Qn Zc)
                - Real.sqrt (frobSqGzFam P F Qn Zc) ≤ BF P F Qn θ₀)
    (hBtr : 0 ≤ Btr P F Qn θ₀) (hBF : 0 ≤ BF P F Qn θ₀) :
    CertificateDisplay (N0sFamQ P F Qn) (NfamQ P F Qn) (NIIFamQ P F Qn)
      (trGhatFam P F Qn) (frobSqGhatFam P F Qn) (Btr P F Qn θ₀) (BF P F Qn θ₀) := by
  have ht := trGhatFam_eq_trGzFam P F Qn Zc hB
  have hf := frobSqGhatFam_eq_frobSqGzFam P F Qn Zc hB
  refine certificate_display_fam P hP F Qn θ₀ Zc hZc hwL ?_ ?_ hBtr hBF
  · rw [ht]; exact hpairTr
  · rw [hf]; exact hpairF

/-- **🟢 Proposition 3.1 at the family aggregates — the LAST clause of
`ZetaQ.assembly_at_lamStar`, up to the `budgetTotal` monotonicity step. PROVED.**

  `[2 − κ_C − (4r₁ + r₂ + 3r₃ + 4r₄ + 2r₅√(κ_C+r₂) + r₅²)]·𝒩 ≤ Σ_χ N^s_{0,χ}(T,2T)`

from the display (`certificate_display_fam_of_bridge`, i.e. §9's join) together with the four
row clauses of §10.3, which are stated here in EXACTLY the form `assembly_at_lamStar`'s
conclusion states them (`trace_row`, `frobenius_row`, `buffer_row_proved`, `pair_rows`).
`Budget` then needs only `bracket ≤ budgetTotal F P` and `0 ≤ NfamQ P F Qn`
(`ZetaQ.NfamQ_nonneg`) to reach its own last clause.

Paper §3 Prop 3.1, §10.5.
Depends on: `certificate_display_fam_of_bridge`,
`ZetaQ.prop_3_1_pair_moment_certificate`, `ZetaQ.NfamQ_nonneg`.
**Rule 17: CLEAN.** `prop_3_1_pair_moment_certificate` is pure real arithmetic; every buffer
occurrence is `P.D0`; `κ_C` here is `Family.kappaC`, the FROBENIUS main-term constant of
§§4–6, **not** `ZetaQ.parity` (paper §3 flags the collision). -/
theorem prop31_fam
    (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) (θ₀ r₁ r₂ r₃ r₄ r₅ : ℝ)
    (Zc : ∀ q : ℕ, DirichletCharacter ℂ q → Zeta23.ZeroConfig)
    (hZc : FamZeroConfig F Qn Zc) (hB : FamGramBridge P F Qn Zc) (hwL : 8 * P.w ≤ P.LB)
    (hpairTr : |trGzFam P F Qn Zc - trAhatFam P F Qn Zc| ≤ Btr P F Qn θ₀)
    (hpairF : Real.sqrt (frobSqAhatFam P F Qn Zc)
                - Real.sqrt (frobSqGzFam P F Qn Zc) ≤ BF P F Qn θ₀)
    (hBtr : 0 ≤ Btr P F Qn θ₀) (hBF : 0 ≤ BF P F Qn θ₀)
    (hκr₂ : 0 ≤ F.kappaC + r₂)
    (htr : (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn)
    (hfrob : frobSqGhatFam P F Qn ≤ (F.kappaC + r₂) * NfamQ P F Qn)
    (hNII : NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn)
    (hBtr' : Btr P F Qn θ₀ ≤ r₄ * NfamQ P F Qn)
    (hBF' : BF P F Qn θ₀ ≤ r₅ * Real.sqrt (NfamQ P F Qn)) :
    (2 - F.kappaC - (4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
        + 2 * r₅ * Real.sqrt (F.kappaC + r₂) + r₅ ^ 2)) * NfamQ P F Qn
      ≤ N0sFamQ P F Qn :=
  prop_3_1_pair_moment_certificate (NfamQ_nonneg P F Qn) hBtr hBF hκr₂
    (certificate_display_fam_of_bridge P hP F Qn θ₀ Zc hZc hB hwL hpairTr hpairF hBtr hBF)
    htr hfrob hNII hBtr' hBF'

/-! ## C.7 The two exports with `FamZeroConfig` and `FamGramBridge` DISCHARGED

`certificate_display_fam_of_bridge` and `prop31_fam` above take the two §9 bundles as
hypotheses at an abstract `Zc`. C.4a and C.5a prove both at the canonical `famZc`, so the
same two exports are available with those hypotheses GONE. These are the forms
`ZetaQ.assembly_at_lamStar`'s checklist item 5 should consume: their only remaining
non-arithmetic inputs are `hP : P.Valid`, `[eq:wrange]`, `2 ≤ Qn`, and **§7's pair split**
`hpairTr`/`hpairF`, which is §7's and not §9's.

Rule 17: CLEAN, inherited verbatim from `certificate_display_fam_of_bridge` / `prop31_fam`;
the only new hypothesis is `hQn : 2 ≤ Qn`, a floor on the FAMILY index. -/

/-- **🟢🟢 THE EXPORT, with both §9 bundles discharged.** `certificate_display_fam_of_bridge`
at the canonical `famZc`, with `FamZeroConfig` and `FamGramBridge` supplied by
`famZeroConfig_famZc` / `famGramBridge_famZc` instead of assumed.
Depends on: `certificate_display_fam_of_bridge`, `famZeroConfig_famZc`, `famGramBridge_famZc`.
**Rule 17: CLEAN**, identically to `certificate_display_fam_of_bridge`. -/
theorem certificate_display_fam_derived
    (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn) (θ₀ : ℝ)
    (hwL : 8 * P.w ≤ P.LB)
    (hpairTr : |trGzFam P F Qn famZc - trAhatFam P F Qn famZc| ≤ Btr P F Qn θ₀)
    (hpairF : Real.sqrt (frobSqAhatFam P F Qn famZc)
                - Real.sqrt (frobSqGzFam P F Qn famZc) ≤ BF P F Qn θ₀)
    (hBtr : 0 ≤ Btr P F Qn θ₀) (hBF : 0 ≤ BF P F Qn θ₀) :
    CertificateDisplay (N0sFamQ P F Qn) (NfamQ P F Qn) (NIIFamQ P F Qn)
      (trGhatFam P F Qn) (frobSqGhatFam P F Qn) (Btr P F Qn θ₀) (BF P F Qn θ₀) :=
  certificate_display_fam_of_bridge P hP F Qn θ₀ famZc
    (famZeroConfig_famZc F Qn hQn) (famGramBridge_famZc P hP F Qn hQn hwL)
    hwL hpairTr hpairF hBtr hBF

/-- **🟢🟢 Proposition 3.1 at the family aggregates, with both §9 bundles discharged.**
`prop31_fam` at the canonical `famZc`. This is the shape
`ZetaQ.assembly_at_lamStar`'s last conclusion clause needs, modulo the trivial
`bracket ≤ budgetTotal F P` monotonicity step.
Depends on: `prop31_fam`, `famZeroConfig_famZc`, `famGramBridge_famZc`.
**Rule 17: CLEAN**, identically to `prop31_fam`. -/
theorem prop31_fam_derived
    (P : ParamsQ) (hP : P.Valid) (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (θ₀ r₁ r₂ r₃ r₄ r₅ : ℝ) (hwL : 8 * P.w ≤ P.LB)
    (hpairTr : |trGzFam P F Qn famZc - trAhatFam P F Qn famZc| ≤ Btr P F Qn θ₀)
    (hpairF : Real.sqrt (frobSqAhatFam P F Qn famZc)
                - Real.sqrt (frobSqGzFam P F Qn famZc) ≤ BF P F Qn θ₀)
    (hBtr : 0 ≤ Btr P F Qn θ₀) (hBF : 0 ≤ BF P F Qn θ₀)
    (hκr₂ : 0 ≤ F.kappaC + r₂)
    (htr : (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn)
    (hfrob : frobSqGhatFam P F Qn ≤ (F.kappaC + r₂) * NfamQ P F Qn)
    (hNII : NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn)
    (hBtr' : Btr P F Qn θ₀ ≤ r₄ * NfamQ P F Qn)
    (hBF' : BF P F Qn θ₀ ≤ r₅ * Real.sqrt (NfamQ P F Qn)) :
    (2 - F.kappaC - (4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
        + 2 * r₅ * Real.sqrt (F.kappaC + r₂) + r₅ ^ 2)) * NfamQ P F Qn
      ≤ N0sFamQ P F Qn :=
  prop31_fam P hP F Qn θ₀ r₁ r₂ r₃ r₄ r₅ famZc
    (famZeroConfig_famZc F Qn hQn) (famGramBridge_famZc P hP F Qn hQn hwL)
    hwL hpairTr hpairF hBtr hBF hκr₂ htr hfrob hNII hBtr' hBF'


end EFChi

end ZetaQ
