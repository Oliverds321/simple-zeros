# The product-window prototype behind `Zeta23/Taper/GevreyProduct.lean`

Receipt for the prototype the lifted product-window layer was built from: it imports only
`Zeta23.Taper.GevreyRamps` and `Zeta23.XiPrime.QuarticWindow.ModWindow`.
**Zero sorries, zero warnings; every theorem below is `[propext, Classical.choice, Quot.sound]`.**

## Structural finding

The tree ALREADY contains a generic "modulated ramp taper is an AdmWindow" theorem:
`Zeta23.XiPrime.admWindow_phiM` (`Zeta23/XiPrime/QuarticWindow/ModWindow.lean:485`) for
`phiM f ϱ L w u := f u * Taper.phi ϱ L w u` under `XiPrime.ModFactor f L A B` (`:32`), constant
`cMod ϱ A B = cRho ϱ + A + A² + B` (`:47`); `Quartic.lean` uses it for `f = √(max 0 (vQuartic(u/L)))`.
Its only hypothesis a polynomial factor cannot meet verbatim is `nonneg : ∀ u, 0 ≤ f u` (GLOBAL);
it is re-proved here with support-local `nonneg`/`le_one` (`ProfileFactor`), reusing the tree's
helpers. Cheapest integration: weaken `ModFactor.nonneg` to the support-local form in the tree
(every use in ModWindow.lean needs it only on the core) and cite `admWindow_phiM` itself.

## Task A — Gevrey ramp lemma for `q·φ` (new analysis, DONE)

Hypotheses on `q`: `ContDiff ℝ k q` (resp. `C^∞`) and derivative bounds ONLY on the support
`hMq : ∀ i u, |u| ≤ L/2 → |iteratedDeriv i q u| ≤ Mq i`.

(A1) k-explicit: `∫|(q·φ)^{(k)}| ≤ 2Bw(A/w)^k k^{sk}·(Σ_{i<k} Mq i (w/A)^i) + Mq k·L`.
(A2) k-free constants `S ≥ Σ_{i<n} Mq i (w/A)^i`, `T ≥ Mq n·L·(w/A)^n` (n ≥ 1):
  `∫|(q·φ)^{(k)}| ≤ 2(B·S + T/(2w))·w·(A/w)^k·k^{sk}` for k ≥ 1.
(A3) the requested shape: if `Mq i = 0` for `i > m`, `B′ := (B + L/(2w))·Σ_{i≤m} Mq i (w/A)^i`.
(A4) polynomial window `q u = pp.eval (u/ℒ)`, fully explicit (`gevrey_polyQ_mul_phi`):
  `B′ = B·Σ_{j≤deg} M_j (w/(ℒA))^j + ½·Σ_{j≤deg} M_j (λ/A)^j`, λ = L/ℒ — independent of L, w, k
  (with 8w ≤ L the first sum is ≤ Σ M_j (λ/8A)^j). `M_j` any bound for `|pp^{(j)}|` on `[−λ/2, λ/2]`,
  e.g. `Mpoly pp (λ/2) j = Σ_i |coeff_i(pp^{(j)})| (λ/2)^i` (`abs_eval_le_Mpoly`).

Route: Mathlib `iteratedDeriv_mul` (Leibniz; exists at this pin, already used in
GevreyRamps.lean:176); pointwise majorant `Σ_i C(k,i) Mq i |φ^{(k−i)}|` (for |u| > L/2 all
`φ^{(j)}` vanish); integrate termwise; ramp lemma `Taper.integral_abs_iteratedDeriv_phi_le` for
i < k, `∫|φ| ≤ L` for i = k; arithmetic `C(k,i)(A/w)^{k−i}(k−i)^{s(k−i)} ≤ (A/w)^k k^{sk}(w/A)^i`
(`Nat.choose_le_pow`, `rpow_le_rpow`, `rpow_add`, `rpow_le_one_of_one_le_of_nonpos`).
A ℂ-valued `GevreyPhiBound`-style wrapper is the same trick as
`Params.gevreyPhiBound_of_profile` (GevreyRamps.lean:237–258); ~10 lines.

## Task B — `AdmWindow` instance (DONE)

```
structure ProfileFactor (f : ℝ → ℝ) (L A B : ℝ) : Prop   -- even; 0 ≤ f ≤ 1 on the core;
  -- AntitoneOn f (Icc 0 (L/2)); C² on a neighbourhood of the core; |f'| ≤ A/L, |f''| ≤ B/L² on the core
theorem admWindow_mul_phi (hf : ProfileFactor q L A B) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) : AdmWindow (fun u => q u * Taper.phi ϱ L w u) L w (cMod ϱ A B)
theorem admWindow_polyQ_mul_phi (pp : ℝ[X]) … : AdmWindow (fun u => pp.eval (u / ℒ) * Taper.phi ϱ L w u)
    L w (cMod ϱ (M1 * (L / ℒ)) (M2 * (L / ℒ) ^ 2))          -- c′ = cRho ϱ + M₁λ + M₁²λ² + M₂λ²
```
Which hypotheses feed which field: `l1_deriv ≤ 2`, `l1_deriv_sq ≤ 2` ← even + 0 ≤ q ≤ 1 on the
core + antitone on [0, L/2] + C¹ near the core (tree's `integral_abs_deriv_le_two`, ModWindow:117;
`q(0) = 1` NOT needed); `l1_deriv2`, `l1_deriv2_sq ≤ c′/w` ← C², |q| ≤ 1, |q′| ≤ A/L, |q″| ≤ B/L²
on the core (tree's `integral_abs_deriv2_mul_le`, ModWindow:267, + Norms.lean:128/341/388/496).

## What is left (integration, not analysis)

1. Lift `ProductWindow.lean` into the tree (§A → e.g. `Zeta23/Taper/GevreyProduct.lean`; §B by
   weakening `XiPrime.ModFactor.nonneg` to support-local and citing `admWindow_phiM`). ~0.5 day.
2. ℂ `GevreyPhiBound`-style wrapper for the product window (window-generic, since
   `Params.GevreyPhiBound` is tied to `P.phi T`). ~1–2 h.
3. For the concrete degree-6 `pp` (data in `audit/smooth_cert_probe.out`): discharge `0 ≤ pp ≤ 1`,
   antitone on [0, λ/2], and `M₁, M₂` (and `M_j` for the Gevrey constant) by `nlinarith`/`Mpoly`,
   as `Quartic.lean` does for `vQuartic`. ~0.5–1 day.
No known obstruction remains.
