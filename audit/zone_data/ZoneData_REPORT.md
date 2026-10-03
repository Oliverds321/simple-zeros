# `ZoneLipschitzData`, certified — receipt for `ZetaQ/ZoneData.lean` (imports ZetaQ.Budget, RampLink; sorry-free, kernel-clean)
* `zoneLipschitzData_qle (r ε) : ZoneLipschitzData Family.qle r ε` with ψ₁ = 5724/100000, c = 184/100:
  `psi_one_le : psi (vProfile P) 1 ≤ 0.05724` (exact degree-24 expansion + antiderivative; exact ψ(1) = 0.0572395…),
  `psi_le_psi_one_add : psi α ≤ psi 1 + 1.84(1−α)` on [0,1] (MVT; `K = 5.7 ≥ sup|(p²)′|` via Bernstein certificates),
  `psi_vProfile_eq` (generic formula). Margin `sZone − 2(C−1)ψ₁ = 0.0022`; implied threshold `1 − zoneFactor ≤ 2.7e-4`
  (`FrobAssembly.zone_compare_eventually_of_data` takes it verbatim).
* **DYADIC:** `dyadic_margin_fails : sZone < 2(C_dyad − 1)·psi (vProfile P) 1` (0.5456 > 0.5073) — `ZoneLipschitzData
  Family.dyadic` against `sZone` is FALSE at every realised dyadic design point; against `sZoneDyadic = 0.5485` (which Budget
  defines) it holds (`zoneLipschitzDataDyadic`, ψ₁ = 0.0439, c = 1.83, margin 0.0028). But `zoneRowLinear P = sZone·(1 − zoneFactor)`
  and `rowR2` use `sZone` for BOTH families ⇒ the frozen dyadic budget row is too small: `frobenius_row`/`corollary_two_dyadic`
  cannot hold asymptotically for the dyadic family as written. Fix = family-aware zone row (`sZoneDyadic` for `Family.dyadic`),
  a frozen-def change — decision for the author.
