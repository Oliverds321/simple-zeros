/-
L10_KDefs (L7_10): vocabulary of Theorem K (thm:shell-K) in ZetaQ's objects (what F1c consumes): the family
functional `F(s) = Σ_χ |A_χ(s)|²` (`ZetaQ.familySum`, `ZetaQ.Achi`), the window `P.gQ`, `normA2`, the in-zone
`ZetaQ.inZone P = {|s| ≤ (1−δ′) log Q}`, and the Shell weight `k̃_{α′}(s/ℒ)/|s/ℒ|` in `s`-units.
Design vocabulary from L7_7's `ShellDesignDefs` (`Design.ShellDesignM`), certificate data from L7_1's
`ChallengeShell` (`S53L75`, `PcertS53`). Namespace `ZetaShell.ShellK`.
-/
import ZetaShell.ShellS.L10_Defs
import ZetaShell.Design.ShellDesignDefs

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ

/-- `F(s) = Σ_{χ ∈ 𝔉_Q} |A_χ(s)|²` (eq:shell-Fbold) in ZetaQ's objects. -/
def FfamZ (P : ParamsQ) (Qn : ℕ) (s : ℝ) : ℝ := familySum Family.qle Qn (fun _ χ => ‖Achi P χ s‖ ^ 2)

/-- **The Shell weight** `k̃_{α′}(s/ℒ)/(s/ℒ)` of eq:shell-thmK in `s`-units, with the constant `C = π⁴/18`:
`C` for `s ≤ log Q + 4` (the strip `Σ_Q`, kernel `C|α|`, and — for `s < −s₀` — the paper's sieve);
`ℒ/s` on `(log Q + 4, α′ℒ]` (kernel `1`; on `(log Q + 4, ℒ]` this is `≥ 1 = |α|/|α|`, i.e. WEAKER than the draft's
`k̃ = |α|` there by a factor `≤ 1 + O(log log Q/log Q)`, which the draft's proof actually delivers);
`Cℒ/s` beyond `α′ℒ` (the killed kernel `C·1`). -/
def shellWt (P : ParamsQ) (αp : ℝ) (s : ℝ) : ℝ :=
  if s ≤ Real.log P.Q + 4 then Cfam else if s ≤ αp * P.LL then P.LL / s else Cfam * P.LL / s

/-- the Shell zone `(log Q + 4, α′ℒ]`, where Theorem S acts. -/
def shellZone (P : ParamsQ) (αp : ℝ) : Set ℝ := Set.Ioc (Real.log P.Q + 4) (αp * P.LL)

theorem measurableSet_outZone (P : ParamsQ) : MeasurableSet (inZone P)ᶜ := by
  rw [inZone_eq_Icc]; exact measurableSet_Icc.compl

end ShellK
end ZetaShell
