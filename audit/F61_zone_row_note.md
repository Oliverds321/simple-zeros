# The zone rows price the ENVELOPE; a fixed profile pays more at finite Q

Receipt: `audit/zone_secant_check.txt` (numpy, the landed degree-6 qle profile, C = π⁴/18).

`zoneRowLinear P = sZone·(1 − zoneFactor P)` with `sZone = 0.5073` = the secant of the OPTIMAL payoff
`P(C,1) − P(C,a)` (paper §10.3: "the measured small-δ payoff SECANT … the δ → 0 slope is 0.5042"), i.e. the
profile is re-optimised for each zone edge `a`. The Lean construction (and, after F58's §2.2, the paper's)
uses ONE fixed profile `v_C`, whose zone cost is `B_a(v_C) − B_1(v_C) = (C−1)·2∫_a^1 α ψ_{v_C}(α) dα`, which
by convexity exceeds the envelope secant:

| a | zone cost (fixed profile) | sZone·(1−a) | ratio |
|---|---|---|---|
| 0.99 | 0.00528 | 0.00507 | 1.04 |
| 0.95 | 0.03110 | 0.02537 | 1.23 |
| 0.90 | 0.07444 | 0.05073 | 1.47 |
| 0.858 (Q = 10¹⁰⁰ design) | 0.12046 | 0.07204 | 1.67 |

Limiting slope `(C−1)·2·ψ_{v_C}(1) = 0.505 < 0.5073`, so the frozen row covers the fixed profile only for
`1 − a ≲ 0.001` (δ′ + l/ℒ ≲ 0.001 ⇒ log Q ≳ 10⁵), with slack ≈ 0.0023·(1−a) thereafter.

Consequences:
* `frobenius_row` as stated (every design point) cannot hold with the fixed profile at practical Q; the
  provable form is EVENTUAL (same situation as `trace_row`), which `assembly_at_lamStar` accepts.
* The proved §11 ramp link constant (`≈ 77·w/ℒ`, `RampLink.lean`) exceeds the ramp row `L₃ = 6w/L` ≈ 16×;
  the true cost is ≈ 10⁻³·w/L (measured) — a sharper link (edge-density `p(λ/2)² ≈ 0.03` in the
  L¹ distance) would fit inside `L₃`; asymptotically both are `O(1/ℒ) = o(zone rows)` but the zone slack
  `0.0023(1−a)` absorbs `70/ℒ` only for `log log Q ≳ 5×10³` — so the eventual threshold is absurd unless the
  link is sharpened. Theorem 1 (eventual) is unaffected in kind; the explicit budget at finite Q is.
* PAPER: §10.3/§10.4 price the zone rows at the envelope secant; for the fixed profile the rows are larger
  (×1.67 at 10¹⁰⁰). Either re-run Table 2 with the fixed profile's `B_a − B_1` (and a sharpened ramp
  constant), or make the construction's profile depend on `a(Q)` (the envelope is then exact — but that is the
  degree/profile-growing route of B7). Decision for the author, alongside B7/B8.
