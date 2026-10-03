/-
Node K3 (L7_10's statement, verbatim; drop-in by L7_3, round 8): **Theorem K beyond `α′`: the killed kernel**.
`∫_{out, s>α′ℒ} gF ≤ (1 + c(log Q)^{−θ})|𝔉_Q| ∫_{out, s>α′ℒ} g‖a‖²Cℒ/s`.
DERIVED (`F1c.K3_killed_of_split`, LF_K3Split) from
* K3a `F1c.killed_pointwise_shell` (PROVED, level A): L7_3's K7 (`LemmaK.killed_pointwise`, any `1 < λ < 2`, imported
  from green) at `λ = 191/100`, bridged by K8d to ZetaQ's objects;
* K3b `F1c.K3b_integrated` (OPEN): the integrated comparison on `inZoneᶜ ∩ (α′ℒ, ∞)`, pure analysis on `‖a‖²`.
L7_10's original file is `lean_work/L7_10/L10_K3_Killed.lean`, and its olean is kept in `orig/L10_K3_Killed_L7_10.olean`.
-/
import ZetaShell.ShellK.L10_KDefs
import ZetaShell.ShellK.LF_K3Split

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ

theorem K3_killed (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hθ : θ < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (∫ s in (inZone P)ᶜ ∩ Set.Ioi (αp * P.LL), P.gQ s * FfamZ P Qn s)
        ≤ (1 + c * Real.log Qn ^ (-θ)) * Family.qle.sizeR Qn
            * ∫ s in (inZone P)ᶜ ∩ Set.Ioi (αp * P.LL), P.gQ s * (normA2 P s * shellWt P αp s) :=
  F1c.K3_killed_of_split αp hα1 hα2 r ε θ hr hε hθ

end ShellK
end ZetaShell
