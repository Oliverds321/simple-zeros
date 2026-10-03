# The `frobenius_row` assembly — receipt for `ZetaQ/FrobAssembly.lean` (imports ZetaQ.Budget, RampLink, AbelLogPow; no sorry of its own)

## Proved (all `[propext, Classical.choice, Quot.sound]` unless noted)
(A) The §11 dictionary + zone split: `gQ_eq_psi_vDesign : gQ (α·ℒ) = (aQ·λ)²·ℒ·psi (vDesign P) α`; `integral_abs_gQ_eq`,
`integral_abs_gQ_Icc_eq` (∫|u|gQ over |u| ≤ s = ℒ(aL)²∫|α|ψ over |α| ≤ s/ℒ); `intervalIntegral_gQ_mul_eq : ∫_0^L gQ(y)·y dy
= ½ℒ(aL)²(K0+K1)(vDesign)` (the Mertens main term in §11 vocabulary); `K0a a v`, `K1a a v`, `Jzone a v := ∫_{a<|α|≤1}|α|ψ`;
`K0a_add_mul_K1a`, `B_eq_zoneSplit : B C v = ψ(0) + K0a + C·K1a − (C−1)·Jzone`, `Jzone_eq_two_interval`, `psi_even`.
(B′) PP block pointwise (sorryAx inherited ONLY from `largeSieveFamily_holds` = the Sieve sorry): side conditions
`Fwin_continuous`, `PXchi_integrableOn`, `MformKer_integrableOn`, `nuQ_continuous`, `muq_continuous`;
`rhoU_univ_le_pointwise` (family-free ρ_U ≤ √(48/π)√(2/T)); `famPP_le_sieve : Σ_χ𝓜[P,P] ≤ Q²(T/π)(½ℒ(aL)²(K0+K1) + CM·L²)(1+2Q^{−δ})(1+ρ)(1+Cs/T)`.
(D1) `nuQ_nuBound` (crude B ≈ √X, integrability-grade only), `frobSq_char_decomp`, `frobSqGhatFam_le_Mform_add_ends (hsep :
∀ τ, Bfam ≤ cMu·Q·envSep P τ) : frobSqGhatFam ≤ (a²L²)⁻¹Σ_χ𝓜[ν,ν] + endsMaj P` (via `Ends.ends_family_bound` at cϱ = cWin).
(D2a) `familySum_Mform_nuQ_split`, `frobSq_le_explicit` (rows 8, 9).
(D2b) **`frobenius_sieve_eventually (F r ε) (hr) (hε) (ε′ > 0) : ∀ᶠ Qn, ∀ P, DesignOfRecord → (∀ τ, Bfam Qn X τ ≤ cMu·Q·envSep P τ)
→ frobSqGhatFam ≤ (psi (vDesign P) 0 + F.Cconst·(K0 + K1)(vDesign P) + ε′)·NfamQ`** (both families; ingredients A1–A5
eventually; `NfamQ_sharp_eventually`; `design_regime`).
(C) zone comparison abstractly: `zone_compare_of_lipschitz`, `one_sub_zoneFactor_le_eventually`, `ZoneLipschitzData`,
`zone_compare_eventually_of_data : ZoneLipschitzData → ∀ᶠ …, (C−1)·Jzone (zoneFactor P) (vProfile P) ≤ zoneRowLinear P`.

## THE FINDING — the in-zone §5 evaluation is ABSENT from Zones.lean
The reachable constant is `Bgen C C (vDesign)` (sieve constant on BOTH zones, ≈ 3 > 2, useless). `lemma43_family_le_C_diagonal_pointwise`
spends Lemma 6.1 on the whole line; the in-zone mean value `Σ_χ∫_U g|A′_χ|² ≈ |𝔉|·∫_U g‖a′‖²` exists ONLY as the hypothesis `hmv`
of `lemma44_zone_boundary`/`lemma45_conservative` (lower direction only). No theorem bounds `inZoneFormFam`/`inZoneSquares` above at
the |𝔉| scale; `CharSums.lemma5_3_zone_calibrated` is the ingredient, the assembly is nowhere. Hence the paper's `κ_C = B_{1,C}`
is not reachable from the tree; this is THE missing object between `frobenius_sieve_eventually` and `frobenius_row_eventually_of`
at κ = 2 − Pcert + rows. Estimate ≥ 1500 lines (Lemma 4.3 in-zone + 4.4 inflation + 4.5(i) cross; the 4.5(ii) branch is gated
by the named Props `Lemma45DivisorRoute`/`CrossDivisorAverage`).
Also: `Ends.Bfam_le_sep` (Lemma 8.1′) carries `hΓ : ∀ (q : ℕ) (χ), GammaFactsChi (parity χ) q` quantified over ALL q incl.
q = 0 where it is FALSE — unused in the proof, so the lemma is sound but inapplicable as stated (one-line repo fix: delete
`hΓ`/`hcoeff`); that is why `hsep` is threaded as a hypothesis.
`NuBound` for `nuQ`: only B ≈ √X is valid → `Zones.frobSqGhatFam_le_master`'s route is dead at λ* > 1; replaced by
`frobSqGhatFam_le_Mform_add_ends`.

## Margins
Zone: `2(C−1)ψ_profile(1) = 0.5050 < sZone = 0.5073`, margin 0.0023; needs `1 − zoneFactor ≲ 0.0009` eventually
(`ZoneLipschitzData` certification for the degree-6 profile not attempted). Small terms: ends `≈ Kends·Q²ℒ³` (needs T ≥ Kℒ²),
row 9 needs `ℒ³ ≥ 358C/ε′`, row-8 error `ℒ ≥ 0.51C/ε′`, PP `(1+2Q^{−1/2})(1+ρ)(1+Cs/T) ≤ 1+η`.

## What remained at the time of writing (all since supplied)
1. In-zone §5 evaluation + assembly — the real blocker; now `ZetaQ/InZone.lean`.
2. `ZoneLipschitzData` certification; now `ZetaQ/ZoneData.lean`.
3. `Bfam_le_sep` hΓ/hcoeff repo fix, then `hsep` from `largeSieve_holds`, `Qn ≤ Q`, `X ≤ Q^{3/2}`, `Q ≥ 10⁹` (design_regime).
4. Sieve sorry `multiplicative_large_sieve` (Lemma 6.1) = the only sorryAx in the chain.
