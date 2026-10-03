# `hpre` (LEMMA_QT QT.b(4)->(5)) and `hregime` — receipt for `ZetaQ/HPre.lean` (imports ZetaQ.Budget, 0 sorry)

## hpre — proved, with a finding
Verbatim slots (Budget.lean `theta0Fam_le_of_design`, `tail_clauses_at_design_of_closing`):
  hpre0 : 0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 Qn
  hpre  : log (prefactorQ …) ≤ logPrefactorGev P
  hregime : 5 + 2√(κ_C + rowR2) ≤ aQ·LB²·√(T/(2π)·famAvgLlow)·(L₅ + L₉)
Unfolded, hpre is `A₀(1 + log Qn/log(2T+4))·sideW L (1/A) (4/e) (2T+4) D₀ ≤ (ℒ + log 4T)·S(D₀)²` — Cenv and L
cancel (the F58 constant change is immaterial). Asymptotically it says `2π·A₀ ≲ L`. With the tree's local-count
constant `EFChi.A0 = 81.26` the LITERAL hpre needs `L ≳ 511` (Q ≳ 10^167) and FAILS at Q = 10¹⁰⁰ (L/2π ≈ 49).
Fix = the normalisation the `logPrefactorGev` docstring describes: η = A₀, i.e. θ₀ ≤ A₀/L.
Proved (namespace `ZetaQ.HPre`, all `[propext, Classical.choice, Quot.sound]`):
* `hpre_of_design … (hr : 3 ≤ r) (hLL : 100 ≤ LL) (hA₀ : 1 ≤ A₀) (hA₀L : 8·A₀ ≤ LB) : hpre0 ∧ hpre` (literal slots).
* `hpre_of_design_A0 … : hpre0 ∧ log(prefactorQ …) ≤ logPrefactorGev P + log A₀` (no extra hypothesis, ℒ ≥ 100).
* `theta0Fam_le_of_design_A0 : theta0Fam … ≤ A₀/LB`; `tail_clauses_at_design_of_closing_A0` (same statement as the
  tree's, WITHOUT hpre0/hpre; hregime carries `A₀·` on the left); core `sideW_le_design`.
## hregime
(a) After θ₀ ≤ A₀/L: `A₀(5 + 2√(κ_C + r₂)) ≤ aL²√(T⟨ℒ⟩/2π)(L₅ + L₉)` ⇔ at the design `√T ≤ 0.399·ℒ^{3.5}·log ℒ/A₀`
    ⇒ still `r + ε ≤ 7` (A₀ only shifts Q₀; at 10¹⁰⁰: √T = 1.36e4 vs 6.5e6).
(b) PROVED: `hregime_eventually (hr : 3 ≤ r) (hε : 0 ≤ ε) (hre : r + ε ≤ 7) (hA₀ : 1 ≤ A₀) : ∀ᶠ Qn, ∀ P, DesignOfRecord →
    A₀(5 + 2√(κ_C + rowR2)) ≤ aQ L² √(T/(2π)·famAvgLlow)(L₅+L₉)` and `tail_clauses_eventually` (§7's two clauses from
    DesignOfRecord + GevreyProfile 2 A B ϱ + hloc alone, for every r + ε ≤ 7).
(c) Margin m: `ClosingAtDesign` with `+ m` nats gives θ₀ ≤ A₀e^{−m}/L; m = k log ℒ ⇒ r + ε ≤ 7 + 2k; m = ½ log T makes it
    √T-free (every r ≥ 3); cost: IVT root Δt = m/c₄ (≈ 6.5 vs t ≈ 143 at 10¹⁰⁰), D₀ up ≈ 9 %, L₄ up ≈ 0.0008; the
    IVT sign lemmas survive. NOT edited (frozen).
## Remaining
Wire the `_A0` chain into `assembly_clauses_at_design_tailfree` (or keep the literal chain under `8A₀ ≤ L`, Q₀ ≳ 10²¹⁶);
`hloc` with explicit A₀ and `GevreyProfile 2 A B rhoTwo` left as hypotheses; F52 option (a) margin vs (b) `r+ε ≤ 7` = author.
