# The row-2 numeric lemma (trace_row E(ii)) and Corollary 3's smooth profiles

## 1 — `ZetaQ/Row2Numeric.lean` (imports Mathlib only): sorry-free, `[propext, Classical.choice, Quot.sound]`
```
theorem Row2Numeric.row2_error_eventually (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in Filter.atTop,
      let T := Real.log Q ^ (r + ε); let ℒ := Real.log (Q * T / (2 * Real.pi)); let L := (1.2507321515 : ℝ) * ℒ
      2 * L * Real.sqrt (Real.exp L) * (3 * Q * (1 + L) + 2) / Real.log 2
        ≤ (1 / 100 - 1 / (200 * Real.pi)) * ((18 / Real.pi ^ 4) * Q ^ 2 - 6 * Q * (1 + Real.log Q) ^ 2) * T
```
Regime (eventual): log Q ≥ 10, (r+ε) log log Q ≤ log Q, 300(log Q)² ≤ Q, 200000(log Q)² ≤ Q^0.37 (binding: Q ≳ 10^24).
Route: T = exp((r+ε) log x), ℒ = x + (r+ε)log x − log 2π ∈ [0, 2x], L ≤ 2.52x, √exp L = exp(L/2) ≤ exp(0.63x)·exp(0.63(r+ε)log x);
bracket ≥ 0.1Q²; numerator ≤ 64Qx²; log 2 > 0.69; Mathlib: Real.isLittleO_log_id_atTop, isLittleO_pow_exp_pos_mul_atTop,
Real.rpow_def_of_pos, Real.exp_half, Real.pi_lt_d2, Real.log_two_gt_d9, … This is step E(ii) of `audit/MuqUniform_REPORT.md`.

## 2 — smooth certified profiles v = p² at all four family constants
Engine: `phase2/payoff_cert_gen.py` exact ℚ; Cbar = scale·3141593⁴/(18·10²⁴) (scale 1, 4/3, 2, 8/3); certified P = 2 − (B0q + Cbar·B1q);
mass = 1 exactly; Bernstein at native degree 2·deg p. Regression: qle deg 6 reproduces `audit/smooth_cert_probe.out` exactly.

| family | C | lam=2b | deg p | certified P | Pcert4 (slack) | Bernstein | min p | note |
|---|---|---|---|---|---|---|---|---|
| qle π⁴/18 | 5.41162 | 1.2428 | 6 | 0.7212579090 | 0.7212 (+5.8e-5) | ok | 0.211 | the Theorem-1 profile |
| qle | | 1.2424 | 10 | 0.7212588830 | 0.7212 (+5.9e-5) | ok | 0.216 | |
| dyadic 2π⁴/27 | 7.21549 | 1.1848 | 6 | 0.7098493241 | 0.7098 (+4.9e-5) | ok | 0.248 | paper optimum 0.7099167 |
| dyadic | | 1.1858 | 10 | 0.7098955752 | 0.7098 (+9.6e-5); 0.70984 | ok | 0.227 | |
| even-q π⁴/9 | 10.82323 | 1.1226 | 6 | 0.6976133915 | 0.6976 | ok | 0.351 | paper 0.6980745 |
| even-q | | 1.1298 | 10 | 0.6980490799 | 0.6980 (+4.9e-5) | ok | 0.189 | |
| even-dy 4π⁴/27 | 14.43098 | 1.0892 | 6 | 0.6909510883 | 0.6909 | ok | 0.437 | paper 0.6919434 |
| even-dy | | 1.0996 | 10 | 0.6919216597 | 0.6919 (+2.2e-5) | ok | 0.175 | |
Observation: a global polynomial approximates the true profile's C¹ kink at t = 1−b slowly — the gap to the optimum plateaus at
≈ 2.1–2.6e-5 for all four families at degree 10. So the artifact's 4-digit constants are 0.7212 / 0.7098 / 0.6980 / 0.6919
(Cor 2 one digit below the paper's 0.7099; 0.70984 at five digits). Caveats: unconstrained deg-8 at π⁴/9 has an interior root
(Bernstein fails) and at 4π⁴/27 is non-monotone (max p = 1.0013) — use the "con" rows or deg 10.
Exact rational data (b, c_k, the two cell coefficient lists, ready `Cert` blocks) for every row is not shipped;
the deg-6 profiles are:
- dyadic: b = 1481/2500, xs = [1019/2500], c = [1, −43967/125000, 1012373/1000000, −706337/500000]
- even-q: b = 5613/10000, xs = [4387/10000], c = [1, −229389/500000, 178703/125000, −1620341/1000000]
- even-dy: b = 2723/5000, xs = [2277/5000], c = [1, −7676/15625, 757059/500000, −1585743/1000000]
(qle: b = 6214/10000, c = [1, −0.24761978, 0.5028952, −1.04416763] at den 10⁶ — `audit/smooth_cert_probe.out`.)
