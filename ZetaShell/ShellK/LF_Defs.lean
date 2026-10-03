/-
lean_work/L7_3/f1c/LF_Defs.lean — objects of the sub-nodes of F1c_chain (L7_3, round 4, 28 Sep 2026).
Namespace `ZetaShell.ShellK.F1c`. On L7_10's `L10_KDefs` (Theorem K's vocabulary: `FfamZ`, `shellWt`), L7_7's design
layer (`Design.ShellDesignM`) and ZetaQ's objects.

* `inCrossRHS Qn P e` — the in-zone and cross part of ZetaQ's master inequality `InZone.famPP_total_le` (verbatim, the
  out-zone sieve term removed): `2((1+e)(|𝔉| + ERR_in)·P_z + (1+1/e)·B·R_z) + 2B∫g‖a‖‖b‖`.
* `outShell P = ∫_{inZoneᶜ} g‖a‖²·shellWt` — Theorem K's right side at `α′ = 2497/1500`, without `(1+c₀r)|𝔉|`.
* `KoutShell C α′ a v = C·Jzone(a) + ∫_{1<|α|≤α′}ψ + C∫_{α′<|α|}ψ` — the out-zone kernel integral of the Shell
  (zone edge `C|α|`, Shell zone `1`, killed zone `C`); `ψ_v(0) + K0a(a) + KoutShell = B_{α′} + (C−1)·Jzone(a)`.
Every integral that is not the last term of its expression is parenthesised (lead's rule, 14:00).
-/
import ZetaShell.ShellK.L10_KDefs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaQ.Payoff ZetaQ.FrobAssembly

/-- the in-zone and cross part of `InZone.famPP_total_le`'s right side, at the Cauchy–Schwarz parameter `e`. -/
def inCrossRHS (Qn : ℕ) (P : ParamsQ) (e : ℝ) : ℝ :=
  2 * ((1 + e) * ((Family.qle.sizeR Qn + ERRin P Qn) * zoneP P) + (1 + 1 / e) * (sieveBudgetQ P * zoneR P))
    + 2 * sieveBudgetQ P * (∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))

/-- Theorem K's out-zone integral at `α′ = 2497/1500`: `∫_{inZoneᶜ} g‖a‖²·k̃_{α′}(s/ℒ)/|s/ℒ|`. -/
def outShell (P : ParamsQ) : ℝ :=
  ∫ s in (inZone P)ᶜ, P.gQ s * (normA2 P s * shellWt P (2497 / 1500) s)

/-- the Shell out-zone kernel integral: `C·Jzone(a) + ∫_{1<|α|≤α′} ψ + C·∫_{α′<|α|} ψ`. -/
def KoutShell (C αp a : ℝ) (v : ℝ → ℝ) : ℝ :=
  C * Jzone a v + (∫ α in {α : ℝ | 1 < |α| ∧ |α| ≤ αp}, psi v α)
    + C * (∫ α in {α : ℝ | αp < |α|}, psi v α)

/-- the ramp constant `c = profMass/(λa)` of `HFrob.psi_vDesign_le`. -/
def cRampS (P : ParamsQ) : ℝ := profMass P / (P.lam * P.aQ)

end F1c
end ShellK
end ZetaShell
