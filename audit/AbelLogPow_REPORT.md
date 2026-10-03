# Abel summation of log q and (log q)^2 against the family count (ledger row 8)

Receipt for `ZetaQ/AbelLogPow.lean` (imports Mathlib only; namespace `ZetaQ.AbelLogPow`; no warnings, no
sorry; every theorem `[propext, Classical.choice, Quot.sound]`).

## Two corrections, both verified
1. "Σ φ*(q)(log q)² is NOT in the tree" is FALSE: `ZetaQ/Normalisation.lean` has `Normalisation.N2.Alog2`,
   `N2.Alog2_bound` (l.1134: `|Alog2 N − (18/π⁴)N²((log N)² − log N + 1/2)| ≤ 30 N(1+log N)⁴`),
   `N2.avgLogSq_limit` (l.1385), `avgLogCondSq`, `N9_facts` (l.2260), `conductor_spread_bigO` (l.2494, IsBigO).
   What the tree LACKS for row 8 is explicit-constant bounds for the two AVERAGES and the explicit VARIANCE
   `⟨(log q)²⟩ − ⟨log q⟩² = 1/4 + O((1+log x)⁴/x)`; this file supplies them, with smaller constants than
   the tree's (K+3c = 5.55 vs 13; 2K+5c = 10.9 vs 30 at c = 18/π⁴, K = 5).
2. From a count error `K x(1+log x)²` the S₂ error is `(1+log x)⁴`, not `³` (the Abel boundary term alone
   is `x(1+log x)⁴`); delivered for general exponent m.

## Statements (hypothesis `hF : ∀ N ≥ 1, |Σ_{q∈Icc 1 N} a q − c N²| ≤ K N (1+log N)^m`, the exact shape of `N2.Astar_bound`)
- `sum_log_bound`: `|S₁(x) − c x²(log x − 1/2)| ≤ (K+3c) x (1+log x)^(m+1)` (x ≥ 1); `sum_logsq_bound`:
  `|S₂(x) − c x²((log x)² − log x + 1/2)| ≤ (2K+5c) x (1+log x)^(m+2)`; `_nat` versions at x = N.
- `abel_sum` (generic continuous Abel identity), `cnt_real_bound`.
- `avg_core` (denominator-agnostic algebraic core), `avg_bounds`, `avg_bounds_Icc2` (sums over `Icc 2 ⌊x⌋₊` =
  `Family.qle.moduli`; constants `(2K+5c+a 1)`, `(3K+7c+a 1)`, variance `(7K+17c+3a 1)`, all `/c0 · (1+log x)^(m+k)/x`).
- One-term Icc 1 ↔ Icc 2 corrections; `sum_mul_log_nonneg`, `sum_mul_log_le`; explicit count lower bounds
  `cnt_lower_explicit_m2` (c/2 · x² ≤ F(x) for x ≥ (32(K+2c)/c)²), `cnt2_lower_explicit_m2`.

## Instantiation in the tree (one line each; type-checked against a def-wrapped stand-in)
`hF := fun N hN => N2.Astar_bound N hN` (c = 18/π⁴, K = 5, m = 2, a q = (phiStar q : ℝ)); then
`sum_logsq_bound_nat (fun q => (phiStar q : ℝ)) (18/π⁴) 5 2 (by positivity) (by norm_num) hF Q hQ`, etc.;
`hlow` from `cnt2_lower_explicit_m2` or `sizeR_qle_lower'` (`Budget.lean:2326`) via `sizeR_eq_sum_phiStar`.
Tree numbers: ⟨log q⟩ error 10.92/c0·(1+log x)³/x; ⟨(log q)²⟩ 16.29/c0·(1+log x)⁴/x; variance 38.14/c0·(1+log x)⁴/x.

## Limitations
Nothing sorried. Explicit c0/x0' only for m = 2, and crude there (8.7e5 against a true ~5.5e3).
