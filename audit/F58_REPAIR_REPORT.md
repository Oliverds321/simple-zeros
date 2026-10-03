# The flat-taper repair: what changed, and the acceptance checks

The design window was [R]'s flat plateau while `κ_C` is the optimal-profile constant; see "the design window
must carry a profile" in the module header of `ZetaQ/Budget.lean` for the finding itself. This is the record of
the repair. It added `ZetaQ/Window.lean`, `ZetaQ/DesignProfile.lean`, `ZetaQ/PayoffSmooth.lean` and
`Zeta23/Taper/GevreyProduct.lean`, and left the build green with exactly four sorries.

## Acceptance
* Frozen statements byte-identical to their pre-repair form: `theorem_one_generic`, `corollary_two_dyadic`,
  `assembly_at_lamStar`, `trace_row`, `frobenius_row`.
* `#print axioms` of 118 touched theorems: all `[propext, Classical.choice, Quot.sound]` except the sorry-carriers and
  `assembly_clauses_at_design(_tailfree)` (inherit `sorryAx` from `trace_row`/`frobenius_row`, as before).
* Rule-17 audits (`RevDepZetaQ`, `DepAuditProofTerm`): identical to pre-repair (all ZetaQ `gated NONE`; the known
  [R]-side `count_certificate`/`D0` and `LocalHypsCoreW.one_le_w` entries pre-existing).

## What changed
* **Defs**: `ParamsQ.prof : Polynomial ℝ` (new field); `toParams.ϱ := fun x => prof.eval((LB/2 − w x)/LL) * ϱ x`
  ([R]'s `atD` idiom) — `phiQ`, `PhiQ`, `gQ`, `aQ`, `phiHatQ` definitions unchanged; `bQ` added; `phiQ_eq_prof_mul`;
  `ProfileQ pp lam` (even, bulk floor `1/6 ≤ pp.eval t` on `|t| ≤ lam/2`, `≤ 1`, antitone on `[0, lam/2]`);
  `Mpoly`, `profM`, `cWin := cRho ϱ + M₁λ + (M₁λ)² + M₂λ²`, `gevreyBprod A B`; `Valid` keeps `taper`, adds
  `profile : ProfileQ prof lam`, `a_ge : 3/4 ≤ aQ`, `b_ge : 1/2 ≤ bQ`; `Valid.toParamsValidQ` deleted.
* **Zeta23/Taper/GevreyProduct.lean** (new; the prototype §A verbatim): `gevrey_polyQ_mul_phi`,
  `admWindow_polyQ_mul_phi`, … (only addition to the [R] tree).
* **ZetaQ/Window.lean** (new): `Valid.admWindow : AdmWindow phiQ LB w cWin`; rfl bridges to `AdmWindow`'s
  `gv/VPhiR/vHatR/av/bv/localFun`; `gQ_ge_bulk`, `gQ_le_aL`, `integral_gQ = (aQ·LB)²`, `poissonSq`,
  `gevreyPhiBound`, `norm_phiHat_le_gevrey`, §8 wrappers; `profileQ_one`, `toParams_flat`, `flat_moment_floors`.
* **Certificate**: `h1_block_free_of_poisson`. **EFChi**: `phiQ_eq`, `H4_ramp` (product), `phiQ_*` via Window,
  `h1_fam` via the Poisson form. **Tail**: `TailHypG.of_envelope` (the plan's `of_phiBound`), `TailHypQ.of_envelope`,
  `norm_phiHatQ_le_gevrey(_design)` with envelope `CenvQ P (gevreyBprod gevreyA gevreyB)`.
* **Ends**: `S2_localHypsCoreW : LocalHypsCoreW P.cWin (toSetting P) (localFun)` field-by-field from
  `Valid.admWindow` (no `lam ≤ 1`); `ends_relative_le` uses `a ≥ 3/4`.
* **Zones**: `crho → cWin`; `gQ_ge_env` (1/1296 envelope); `gQ_deriv_facts` via `ThmD.autocorr_deriv_facts`;
  `bathtub_first_moment` ⇒ `taper_first_moment_ge` (same statement); constants rescaled by 1296 (thresholds
  `log Q ≥ 7100`, 2⁴⁵, `zoneRP` 82944π/2654208); witnesses with `prof := 1`.
* **DesignProfile.lean** (new): `designProfileQle`, `designProfileDyadic`, `Family.designProfile`, `profileQ_*`,
  `design_moments : 3/4 ≤ aQ ∧ 1/2 ≤ bQ` (at `lam = lamStar`, `w = 1`, `LL ≥ 100`), `design_gevreyBprod_le ≤ 40000`.
* **Budget**: `DesignOfRecord … ∧ P.ϱ = rhoTwo ∧ P.prof = F.designProfile`; `CenvDesign` (gevreyBprod);
  `D0_le_of_design` (`80000 + 3 log Q`); `design_high_sign (hBp : Bp ≤ 40000)`; `exists_designOfRecord_at` witness
  `⟨Q, log Q^(r+ε), lamStar, 1, 2, rhoTwo, F.designProfile⟩`; frozen shapes untouched.
* **PayoffSmooth.lean** (new, root-imported): `Pcert_qQ_smooth = 7212/10000`, `Pcert_dyad_smooth = 7098/10000`;
  `certQQsmooth`, `certDyadSmooth` (two cells, degree 12, exact ℚ); `payoff_feasible_qQ_smooth :
  ∃ v, Admissible lamStar v ∧ B (π⁴/18) v ≤ 2 − 7212/10000`; `payoff_feasible_dyadic_smooth`; `vDesign`, `vProfile`,
  `rampCost`, `ProfileRampLink : Prop` (the §11 link, stated with the Gates banner, NOT proved).

## Design profiles (optimised ON the design support, b = λ*/2 — so the design runs at λ*)
`p(t) = 1 + d₂t² + d₄t⁴ + d₆t⁶`:
| family | λ* | d₂, d₄, d₆ (ℚ) | float B | a_core, b_core | Pcert |
|---|---|---|---|---|---|
| qle | 1.2507321515 | −81257/125000, 3458583/1000000, −3669851/200000 | 1.27874639 | 0.7832, 0.6838 | 0.7212 (slack 5.4e-5) |
| dyadic | 1.1931581210 | −1014099/1000000, 834917/100000, −16525667/500000 | 1.29015911 | 0.8017, 0.7031 | 0.7098 |
Gevrey: `B′ = gevreyBprod A B ≤ 40000` at the design (qle M_j ≈ 2.88, 14.7, 102, 590, 2666, 8262, 13212).

## Deviations from the route as first planned
* Profiles at `b = λ*/2` (certificate support = design support; a free b would break `Admissible lamStar`);
  dyadic tops out at 0.70984/0.70988 (deg 6/8) → ships 0.7098, not the paper's 0.7099.
* `prof : Polynomial ℝ` (for `compute_degree`, `Mpoly`, exact integrals).
* Bulk floor 1/6 replaces all plateau-quantitative flat facts (taint audits showed them reaching 20 Zones lemmas,
  `h1_block_free`, Budget/Ends `a ≥ 3/4`); hence the 1296 rescaling of Zones constants.
* Moment floors `a ≥ 3/4`, `b ≥ 1/2` are `Valid` fields discharged at the design by exact polynomial integrals.
* `TailHypG.of_envelope` lives in `ZetaQ/Tail.lean` (root namespace), not in the [R] tree.
* `ends_relative_le` had a vacuous `cϱ ≤ 4` hypothesis (now `cWin`-based).

## Remaining
`ProfileRampLink` (the §11 link: `B C (vDesign P) ≤ B C (vProfile P) + rampCost C P`, needs ramp L¹/L² control of
`φ_Q² − p²`, `aQ` vs `a_core`, continuity of `B`, `w/ℒ` smallness); the four sorries (statements unchanged).
