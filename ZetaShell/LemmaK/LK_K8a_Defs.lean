/-
lean_work/L7_3/skeleton/LK_K8a_Defs.lean — the objects of K8a's four sub-nodes (L7_3, round 2, 28 Sep 2026).

* `masterRHS F Qn P e` — the right side of ZetaQ's master inequality `InZone.famPP_total_le` (verbatim): the in-zone
  mean value, the zone remainder, the OUT-ZONE sieve term `2·sieveBudgetQ·∫_{inZoneᶜ} gQ·normA2`, and the cross term.
* `savWeight C₁ Qn P s = (1 − C₁/log Q)·U·(s − ℓ_K)₊·1{s ≤ log 𝒳 − 1}`, `U = T/2π` — Lemma K (i)'s subtracted term
  (K7 with `η_P ≤ C₁/log Q`), and `Sav = ∫_{inZoneᶜ} gQ·savWeight`.
* `errWeight P s = 2Q²‖a(s)‖ + (π𝒳 + R′²)‖a(s)‖²` — what K7's bound adds to ZetaQ's pointwise sieve
  `sieveBudgetQ·‖a‖² = (Q² + π𝒳)‖a‖²`, and `Err = ∫_{inZoneᶜ} gQ·errWeight`.
So K7 reads, pointwise: `Σ_χ|A_χ(s)|² ≤ sieveBudgetQ·normA2 − Q²·savWeight + errWeight`.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section
open MeasureTheory Set

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaQ.Payoff

/-- the right side of `ZetaQ.InZone.famPP_total_le` (the master inequality), at the Cauchy–Schwarz parameter `e`. -/
def masterRHS (F : Family) (Qn : ℕ) (P : ParamsQ) (e : ℝ) : ℝ :=
  2 * ((1 + e) * ((F.sizeR Qn + ERRin P Qn) * zoneP P) + (1 + 1 / e) * (sieveBudgetQ P * zoneR P))
    + 2 * (sieveBudgetQ P * ∫ s in (inZone P)ᶜ, P.gQ s * normA2 P s)
    + 2 * sieveBudgetQ P * ∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s)

/-- Lemma K (i)'s subtracted term at `η_P ≤ C₁/log Q`: `(1 − C₁/log Q)·(T/2π)·(s − ℓ_K)₊·1{s ≤ log 𝒳 − 1}`. -/
def savWeight (C₁ : ℝ) (Qn : ℕ) (P : ParamsQ) (s : ℝ) : ℝ :=
  (1 - C₁ / Real.log (Qn : ℝ)) * (P.T / (2 * Real.pi)) * max (s - ellK P.Q P.T) 0
    * (if s ≤ Real.log P.XQ - 1 then 1 else 0)

/-- the out-zone saving `∫_{inZoneᶜ} gQ·savWeight`. -/
def Sav (C₁ : ℝ) (Qn : ℕ) (P : ParamsQ) : ℝ := ∫ s in (inZone P)ᶜ, P.gQ s * savWeight C₁ Qn P s

/-- what Lemma K (i) adds to ZetaQ's pointwise sieve: `2Q²‖a‖ + (π𝒳 + R′²)‖a‖²`. -/
def errWeight (P : ParamsQ) (s : ℝ) : ℝ :=
  2 * P.Q ^ 2 * Real.sqrt (normA2 P s) + (Real.pi * P.XQ + (max 2 (R0 P.Q P.T s)) ^ 2) * normA2 P s

/-- the out-zone error `∫_{inZoneᶜ} gQ·errWeight`. -/
def Err (P : ParamsQ) : ℝ := ∫ s in (inZone P)ᶜ, P.gQ s * errWeight P s

end LemmaK
end ZetaShell
