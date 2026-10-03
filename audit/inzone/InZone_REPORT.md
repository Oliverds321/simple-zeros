# The in-zone §5 evaluation — receipt for `ZetaQ/InZone.lean` (imports `ZetaQ.FrobAssembly`)

Axioms: every theorem `[propext, Classical.choice, Quot.sound]` EXCEPT the final `famPP_le_zone_split`, whose `sorryAx` is
inherited only through `largeSieveFamily_holds` (the Sieve sorry); intermediate lemmas take `hLS : LargeSieveFamily`.

## 1. The in-zone mean value, both directions (NEW — the object the tree lacked)
* `meanValue_generic`: for any coefficient vector supported on `n ≤ Y` and any set `S` of moduli with pairwise family
  character sums `‖Σ_{q∈S}Σ*_χ χ(n)χ̄(m)‖ ≤ cQ·τ(|n−m|)` (n ≠ m):
  `|Σ_{q∈S}Σ*_χ‖Σ_n c_n χ(n)‖² − Σ_n‖c_n‖²·famCountAt S n| ≤ cQ·2Y(1+log Y)·Σ_n‖c_n‖²` (`famCountAt S n ≤ |𝔉_S|`, the
  coprimality-weighted diagonal). Route: exact expansion, Lemma 5.2 crude termwise, Schur/AM–GM on τ.
* `pairSumS_family_le F Qn n m : ‖Σ_{q∈F.moduli Qn}Σ*_χ χ(n)χ̄(m)‖ ≤ 2·Qn·τ(|n−m|)` (both families).
* At `a′(s) = acoefLow P`: `inZone_meanValue_pointwise/_upper/_lower`; integrated: `inFormF_low_le : inFormF F Qn P (acoefLow P)
  ≤ (F.sizeR Qn + ERRin P Qn)·zoneP P`, `inFormF_low_two_sided`; `famSum` versions `inZoneFormFam_low_le`, `_two_sided`.
* `ERRin P Qn := 2·Qn·(2·Yn(1+log Yn))`, `Yn = ⌊Q^{1−δ′}⌋₊`; `ERRin_le_sizeR : ERRin ≤ 80·|𝔉_Q|/(log Qn)²`;
  `ERRin_small_eventually`.
## 2. The in-zone PP form
`famPP_inZone_le … : Σ_{χ∈𝔉_Q}∫_U g|F_χ|² ≤ 2[(1+ε)(|𝔉_Q|+ERRin)·zoneP + (1+1/ε)(X+Q²−1)·zoneR] + 2(X+Q²−1)∫_U g‖a‖‖b‖`
(Lemma 4.4's inflation and 4.5(i)'s cross term reproduced; `zone_diag_eq`, `inFormF_split`, `inFormF_high_le`, mirror lemmas,
`cross_pointwise_family`/`cross_integral_family`).
## 3. Out-zone + total
`famPP_total_le'` (pointwise master), dictionary `s0_div_LL_eq_zoneFactor`, `zoneMain_eq : 2(T/2π)∫_0^{s0}u g = (T/2π)ℒ(aL)²·K0a(zoneFactor)(vDesign)`,
transfer `DesignFamily → DesignOfRecord` (`designFamily_of_DoR`, `transfer_of_designFamily`, `zone_facts_eventually`, `reg_eventually`).
**`famPP_le_zone_split (F r ε) (hr) (hε) (ε′ > 0) : ∀ᶠ Qn, ∀ P, DesignOfRecord F r ε Qn P →
  familySum F Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ)) ≤ (aQ·LB)²·(K0a (zoneFactor P) (vDesign P) + F.Cconst·K1a (zoneFactor P) (vDesign P) + ε′)·NfamQ P F Qn`**
o(1) bookkeeping: one δ := min 1 (ε′/(70C+10)) absorbs smearing `Cs/T`, cross `ρ_ℝ ≤ √(48/π)√(2/T)`, budget `B ≤ Q²(1+δ)`,
zone edge `ERRin ≤ (δ/3)|𝔉|` (log Q ≥ 240/δ + 36), `a″` tails `zoneR ≤ δ²zoneP`, Mertens remainder (ℒ ≥ 128C·CM/(9δ)),
family floors (`NfamQ_sharp_eventually`, `sizeR_LL_le_NfamQ_eventually`).
## 4. FINDING — the `hmv` hypotheses are NOT discharged and are almost certainly FALSE at large Q
`lemma44_zone_boundary`'s / `lemma45_conservative`'s `hmv` assert a LOWER bound `family form ≥ |𝔉|(1 + (X−1)/Q²)·diagonal`,
strictly above the mean value; the true diagonal carries the coprimality-weighted count `N_𝔉(n) ≤ |𝔉|` (deficiency
`≍ Σ_p (log p)²/p²/L² > 0`), so the provable lower bound is `|𝔉|(1 − c/L² − o(1))·zoneP`. Not needed: the assembly uses
only the upper bound and reproduces 4.4/4.5(i)'s conclusions with `(1+o(1))` slack.
## 5. Remaining
Quantifying the lower direction at scale `|𝔉|(1 − o(1))` (a `Σ_{p|q}φ*(q)` density estimate) — not needed; `ρ_U(inZone) → 0` not proved (not needed).
