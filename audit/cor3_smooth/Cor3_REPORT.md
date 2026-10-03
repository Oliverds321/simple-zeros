# Corollary 3's smooth certificates at the DESIGN supports, and the wiring audit

Files: `cor3_fixedb.py/.out` (optimiser at fixed b = λ*/2 + exact-ℚ certification via `phase2/payoff_cert_gen.py`),
`row_*.json`, `gen_lean.py`, **`Cor3Smooth.lean`** (even-dyadic deg 10 con, even-q deg 8; `import ZetaQ.PayoffSmooth`,
sorry-free, all `[propext, Classical.choice, Quot.sound]`; needs `set_option maxHeartbeats 0` on `_MassOK/_NonnegOK`),
`Cor3Smooth_fallback8.lean` (even-dyadic deg 8 con, 0.6918).

## Certified constants at the design supports
Even/odd DYADIC, C = 4π⁴/27, λ* = 1.1015998422: deg 6 → 0.6908; deg 8 con → 0.6918; **deg 10 con (p ≥ 0.17) → 0.6919**
(certified 0.6919177625, slack 1.78e-5, Bernstein +3.1e-2 at n = 20, min p = 0.170, antitone, a_core 0.854, b_core 0.771).
Even/odd q ≤ Q, C = π⁴/9, λ* = 1.1329788821 (from `payoff_feasible_even_qQ`'s docstring; no `lamStarEvenQ` in the tree):
deg 6 → 0.6975; **deg 8 → 0.6980** (0.6980458533, slack 4.59e-5, Bernstein +3.1e-2 at n = 16, min p 0.173, a_core 0.841,
b_core 0.757). So the paper's 4 digits ARE reached at fixed design support. Unconstrained deg-10 optima violate the bulk
floor 1/6 (0.153/0.161) and unc deg-8 even-dy is non-monotone — constrained runs fix both at ≤ 3.4e-6 in P.
Chosen: even-dy deg 10 con `d = −306129/500000, 387781/62500, −28365317/250000, 397141241/500000, −46455797/25000`;
even-q deg 8 `d = −66999/500000, −5495941/500000, 100475221/1000000, −3503919/12500` (monomial basis, t², t⁴, …).

## Lean
`certEvenDyadSmooth` (deg 20), `certEvenQSmooth` (deg 16) + `_MassOK/_NonnegOK/B0B1_*`;
`payoff_feasible_even_dyadic_smooth : ∃ v, Admissible lamStarEvenDyad v ∧ B (4π⁴/27) v ≤ 2 − 6919/10000`;
`payoff_feasible_even_qQ_smooth : ∃ v, Admissible lamStarEvenQ v ∧ B (π⁴/9) v ≤ 2 − 349/500`;
`designProfileEvenDyad : ℝ[X]` (deg 10), `designProfileEvenQ` (deg 8), `profileQ_evendyad`, `profileQ_evenq`
(via `antitoneOn_of_deriv_nonpos`, degree-uniform), `design_moments_of'` (generic), `design_moments_evendyad/_evenq`
(3/4 ≤ aQ ∧ 1/2 ≤ bQ at lam = λ*_fam, w = 1, ℒ ≥ 100).

## Wiring audit (`Normalisation.lean` 4480/4517/4550 — all PROVED, conditionally)
`corollary3_even_dyadic (evenFam : Subfamily) (hdens : SubfamilyAdmissible evenFam (1/2)) (I : PassageInterface CfamDyadic) :
∃ lam v, 1 < lam ∧ lam < 2 ∧ Admissible lam v ∧ Pcert_even ≤ I.pay evenFam v` (odd/even-qQ analogous). Proof =
`payoff_feasible_even_*` (PIECEWISE certs at λ = 11/10, 28/25) + `subfamily_passage`. `PassageInterface C` has fields
`outSet, outWt, den, pay, sieve_budget (Lemma 6.1 posited), den_density, delivers : ∀ S α, SubfamilyAdmissible S α → ∀ lam v,
… → 2 − Bgen 1 (Σ_S/den S) v ≤ pay S v` — i.e. the whole §§3–10 chain on the subfamily is an ABSTRACT FIELD, universally
quantified over all admissible v; `SubfamilyAdmissible` = {pos, density, conductor_matches, in_zone_projector}. NOTHING in
the tree constructs an instance of either; no Corollary-3 zero-count statement exists in Budget.lean; `Family` is
`qle | dyadic` only (no parity selector).
Under the repaired construction: (a) swap to the smooth certificates — mechanical, constants 0.6919/0.6980 unchanged;
(b) `delivers` must be restricted to the design profile (+ rampCost) when built from the spine; (c) a parity-selecting
`Family`-like value (moduli + character selector), `Cconst`, `payoff`, `lamStar`, `designProfile` per even family;
(d) `Valid` at the even designs discharged by `profileQ_even*`/`design_moments_even*`.
Remaining to PROVE for an unconditional Corollary 3: a `PassageInterface` instance (sieve budget, `den_density` from
`famCardEven_asymp`/`zeroCountEven_asymp`, `delivers` = §§3–10 on the subfamily with in-zone coefficient 1), a
`SubfamilyAdmissible evenFam (1/2)` instance (`conductor_matches` proved nowhere; `InZoneProjector` needs CharSums 5.2′),
and a zero-count statement of `theorem_one_generic`'s shape. This is a separate project beyond Theorem 1.

## Findings contradicting the plan
1. Gevrey constant: `gevreyBprod` (with `Mpoly` coefficient sums) ≈ 1.33e5 (even-dy deg 10 con), 6.3e4 (even-q deg 8),
   7.9e4 (even-dy deg 8 con) — above the `40000` threshold of `design_gevreyBprod_le` / `design_high_sign` / `D0_le_of_design`;
   only degree-6 profiles stay under. A larger threshold or sup-norm `M_j` is needed for the even families.
2. `λ*_even,qQ = 1.1329788821` exists only in a docstring; the old certificates were at λ = 1.1/1.12, not λ*.
