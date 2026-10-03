# q-uniform μ_q chain for `trace_row` row 1

Receipt for `ZetaQ/MuqUniform.lean` (namespace `ZetaQ.MuqUniform`; imports only
`Zeta23.ThmE.GammaFactsChiProof`, `Zeta23.ThmE.PrimeSideChi`). No errors, warnings or sorries; all 14
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## The two observations that made everything explicit
* On `[−1,1]` no compactness: `muq` is even and monotone on `[0,∞)` (`GammaChi.muq_even`,
  `muq_monotoneOn`, both need `κ ≤ 1`), so `μ_χ(0) ≤ μ_χ(τ) ≤ μ_χ(1)`; `μ_χ(0) > −1`
  (`neg_one_lt_muq_zero`), Stirling at τ = 1 (`muq_stirling_const`, q-free `10/π`) ⇒
  `|μ_χ| ≤ (log q)/2π + 10/π` on `[−1,1]` — handover item 1 with `M₀ = 10/π`.
* Increments are q-FREE: `muq κ q τ₁ − muq κ q τ₂ = muq κ 1 τ₁ − muq κ 1 τ₂` (`muq_sub_eq`), so
  item 2's constant is absolute for ALL q: `K = 180/π + 36`.
All statements carry `κ ≤ 1` (parity), as every lemma in `GammaFactsChiProof.lean` does.

## Statements proved (abridged; see the file)
* `muq_abs_le_of_abs_le_one`, `muq_abs_le_of_one_le`, `muq_abs_le_global`,
  `muq_linear_bound_uniform` (`|muq| ≤ (log q)/2π + (10/π + 1) + |τ|`), `muq_linear_bound_uniform'`,
  `muq_linear_bound_Icc_uniform` — item 1 (`PrimeSideChi.lean:240`) q-uniform.
* `muq_abs_le_Icc_uniform`, `muq_abs_le_uniform` (`C = 11/π`, `T₀ = 2πe`) — item 3a (`:50`).
* `muq_sub_eq`, `increment_of_bounds`, `muq_increment_bound_explicit` (`K = 180/π + 36`, all q),
  `muq_increment_bound_uniform` — item 2 (`:303`).
* `muq_nonneg_of_ge`, `muq_nonneg_eventually_uniform` (`τ₀ = 2πe`), `muq_nonneg_of_abs_ge` — item 3b (`:354`).
* BONUS, per character, over cap-free `LocalHypsCoreW`: `muPart_approx_core`, `muPart_approx_ell1`:
  `|Σ_{k<d} ∫ φ̂(r)² μ_q(τ_k + r) dr − aL²·T·ℓ_{1,q}(T)/2π| ≤ K(16+2cϱ+2cϱ²)L²/2π + 4πL((log q)/2π + (11/π)l) + (10/π)L²/T`
  — the μ-part of the trace is `aL²·Tℓ_{1,χ}/2π + O_{cϱ}(L²) + O(L log q) + O(L l)`, i.e. `Θ(1/T)` relative.

## Constants
| quantity | per-q original | uniform |
|---|---|---|
| `|μ_χ|` on `[−1,1]` | opaque compactness `M₁` | `(log q)/2π + 10/π` |
| linear `M` (:240) | `max M₁ (1 + log q + |C|)` | `(log q)/2π + (10/π + 1)` |
| `muq_abs_le` (:50) | `log q + log 2 + 1 + |Cs|`, `T₀ = 2πe` | `((log q)/2π + 11/π)·l(T)`, `T₀ = 2πe` |
| increment `K` (:303) | q-dependent | `180/π + 36 ≈ 93.3` |
| `τ₀` (:354) | `2π·exp(2π|C|)` | `2πe` |

## The aggregate chain for `trace_row_of_muPart`'s `hmu` (proposed `muPart_row1_of_design`)
A ✅ `muPart_approx_ell1` (per χ). B ⬜ bridge to `ParamsQ` via `Ends.S2_localHypsCoreW` (copy the
prelude of `sum_gridGramEntry_diag_eq`, `Budget.lean` TraceRungs) — NOTE: after the f58 repair the
window constant is `cMod`, not `crho`. C ⬜ per-χ RvM: `EFChi.rvmChi_main_uniform` (`EFChi.lean:555`).
D ⬜ family sum (`Finset.sum_le_sum`, `log q ≤ log Qn`, `sizeR_eq_sum_phiStar`). E ⬜ two eventual
inequalities: (i) per-χ error ≤ `T/(400π)` eventually (pattern `rvm_error_small`, `Budget ≈ :2430`;
needs the window constant as a numeral at the design); (ii) **the only genuinely new numeric lemma**:
the row-2 prime-part error `2·LB·√XQ·(3Qn(1+LB)+2)/log 2 ≤ (0.0101 − 1/200π)·sizeR·T` eventually
(`sizeR ≥ (18/π⁴)Qn² − 6Qn(1+log Qn)²` from `sizeR_qle_lower'`, `√XQ = (QT/2π)^{λ*/2}`, `λ* < 2`;
ratio ≈ `2360·ℒ²·(QT)^{−0.3746}`, crossover `Q ≈ 10¹⁰`). F ⬜ assembly.
Effort: B 1–2 h, C 0.5 h, D 1–2 h, E(i) 1–2 h, E(ii) 3–6 h (medium risk), F 0.5 h ≈ 1–2 sessions.

## Mechanics
`lake env lean` must run from the project root; parenthesise interval integrals before a `−`
(`∫ τ in a..b, f τ - g` parses as `∫ (f τ - g)`); `linear_combination (…) * (x * x⁻¹ = 1)` is a
deterministic substitute for `field_simp`.
