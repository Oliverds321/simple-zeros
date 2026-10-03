/-
lean_work/L7_1/ShellInterfaces.lean — interfaces of the FAMILY follow-up (`ZetaShell`), L7_1, 28 Sep 2026.
Intended home: `ZetaShell/Interfaces.lean`. Imports the Mathlib-only statement layer `ChallengeShell` (this folder)
and the trunk `ZetaQ` modules the Shell route reuses (`ZetaQ.Budget`: `Twin`, `Family`, `NfamCount`, `ParamsQ`,
the rows `trGhatFam`/`frobSqGhatFam`/`NIIFamQ`/`Btr`/`BF`; `ZetaQ.Payoff`: `psi`, `Admissible`).

Contents
  §1 the ABSTRACT density hypotheses (B) and (LF) of ssec:shell-density (sec_shell.tex l.707–717), with their
     parameters (`h_B`, `b₀`, `c(σ)`, `σ_LF`, `h_LF`, `c₀`) kept as parameters, and the threshold arithmetic
     `A*`, `M`, `α₀(𝒟)` (eq:shell-alpha0), `κ′`, `θ(α′)` (eq:shell-etaQ). `ZeroDensityInput` (ChallengeShell §2) is
     the instantiation (D1′); node Z1 derives (B) and (LF) from it.
  §2 `ShellFrame` — the family analogue of the ζ paper's `FrameFamily`: a design along `Q → ∞` at the Shell
     bandwidth `λ = S.lam` and profile `S.p`, carrying the display (H1) and the five rows that ZetaQ's Proposition 3.1
     (`ZetaQ.prop_3_1_pair_moment_certificate`) consumes (`ZetaQ.Margin.assembly_at_lamStar_provedM`'s bundle), with the Frobenius row at the Shell constant `κ` and
     every error row at the Shell rate.
  §3 the headline in the TREE form (against `ZetaQ.NfamCount`, `ZetaQ.N0sFamCount`, `ZetaQ.Twin`, exactly the shape of
     `ZetaQ.JoinProved.theorem_one_generic_proved'`), `sorry`; the Mathlib-only form is `ChallengeShell.shell_S53_qle`
     and node B1 identifies the two.
-/
import ZetaShell.Challenge
import ZetaQ.Budget
import ZetaQ.Payoff

noncomputable section
open scoped BigOperators
open Filter

namespace ZetaShell

/-! ## §1 The abstract density hypotheses and the threshold -/

/-- **(B) Bulk hybrid** (sec_shell.tex l.708–711): "There are `h_B ∈ [0,2]`, `b₀ ≥ 0` and `c(σ)` such that for every
`ε > 0`, uniformly in `R ≥ 1`, `H ≥ 2`, `½ + ε ≤ σ ≤ σ_LF`:
`Σ_{r≤R} Σ*_χ N(σ,H,χ) ≤ C_ε (R²H^{h_B})^{c(σ)(1−σ)+ε} (log RH)^{b₀}`." Parameters kept free. -/
def BulkHybrid (hB b0 σLF : ℝ) (c : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℕ, 1 ≤ R → ∀ H : ℝ, 2 ≤ H → ∀ σ : ℝ, 1 / 2 + ε ≤ σ → σ ≤ σLF →
    Nstar R σ H ≤ C * ((R : ℝ) ^ 2 * H ^ hB) ^ (c σ * (1 - σ) + ε) * Real.log (R * H) ^ b0

/-- **(LF) Log-free hybrid** (sec_shell.tex l.712–714): "There are `σ_LF < 1`, `h_LF ∈ [0,2]` and `c₀ > 0` such that
for every `ε > 0`, uniformly in `R ≥ 1`, `H ≥ 2`, `σ ≥ σ_LF`: `Σ_{r≤R} Σ*_χ N(σ,H,χ) ≤ C_ε (R²H^{h_LF})^{(c₀+ε)(1−σ)}`."
(`σ ≤ 1` added: there are no zeros with `β > 1`, so this is no restriction.) -/
def LogFreeHybrid (σLF hLF c0 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℕ, 1 ≤ R → ∀ H : ℝ, 2 ≤ H → ∀ σ : ℝ, σLF ≤ σ → σ ≤ 1 →
    Nstar R σ H ≤ C * ((R : ℝ) ^ 2 * H ^ hLF) ^ ((c0 + ε) * (1 - σ))

/-- `A* := sup_{[1/2, σ_LF]} c` (sec_shell.tex l.711). -/
def Astar (c : ℝ → ℝ) (σLF : ℝ) : ℝ := sSup (c '' Set.Icc (1 / 2) σLF)

/-- `M := max(A*, c₀)` (eq:shell-alpha0). -/
def Mexp (c : ℝ → ℝ) (σLF c0 : ℝ) : ℝ := max (Astar c σLF) c0

/-- `α₀(𝒟) := min(M/(M−1), 2)` (eq:shell-alpha0). -/
def alpha0 (M : ℝ) : ℝ := min (M / (M - 1)) 2

/-- `κ′ = c₀(2 − 2/α′) + ε″` (eq:shell-etaQ). -/
def kappaPrime (c0 αp ε'' : ℝ) : ℝ := c0 * (2 - 2 / αp) + ε''

/-- `θ(α′) = min(1, (2 − κ′)/κ′)` (eq:shell-etaQ). -/
def thetaRate (κ' : ℝ) : ℝ := min 1 ((2 - κ') / κ')

/-- Montgomery's exponent of (D1′): `c(σ) = 3/(2−σ)`. -/
def cMontgomery (σ : ℝ) : ℝ := 3 / (2 - σ)

/-! ## §2 The family frame -/

/-- **`ShellFrame F r ε S κ rate`** — the family-side analogue of the ζ paper's `FrameFamily`.
A design predicate `Des Q P` along `Q → ∞` at `T = (log Q)^{r+ε}`, bandwidth `λ = S.lam` and profile `p = S.p`
(so the certificate `ShellCert S` is about the design's own `v = p²`), together with the display (H1) of paper §3
(`ZetaQ.CertificateDisplay`, the rank–trace certificate summed over the family) and the rows of
`ZetaQ.Margin.assembly_at_lamStar_provedM`'s bundle, the Frobenius row at the Shell constant `κ` and every error row
`≤ c·rate(Q)`. `trace`/`NII`/`Btr`/`BF` are ZetaQ's rows re-run at the Shell bandwidth (remark rem:shell-interface:
"imported at the new λ ∈ [1.69, 1.995]" — [CHECK] in the draft); `frob` is the only row the Shell route changes
(thm:shell-K, thm:shell-1pp). -/
structure ShellFrame (F : ZetaQ.Family) (r ε : ℝ) (S : ShellProfile) (κ : ℝ) (rate : ℕ → ℝ) where
  Des : ℝ → ZetaQ.ParamsQ → Prop
  exists_design : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∃ P : ZetaQ.ParamsQ, Des Q P
  T_eq : ∀ Q P, Des Q P → P.T = ZetaQ.Twin Q r ε
  Q_eq : ∀ Q P, Des Q P → P.Q = Q
  lam_eq : ∀ Q P, Des Q P → P.lam = (S.lam : ℝ)
  valid : ∀ Q P, Des Q P → P.Valid
  prof_eq : ∀ Q P, Des Q P → ∀ t : ℝ, P.prof.eval t = S.p t
  rows : ∃ c : ℝ, 0 < c ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ZetaQ.ParamsQ, Des (Qn : ℝ) P →
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧ 0 ≤ ZetaQ.Btr P F Qn θ₀ ∧ 0 ≤ ZetaQ.BF P F Qn θ₀ ∧
      ZetaQ.CertificateDisplay (ZetaQ.N0sFamQ P F Qn) (ZetaQ.NfamQ P F Qn) (ZetaQ.NIIFamQ P F Qn)
        (ZetaQ.trGhatFam P F Qn) (ZetaQ.frobSqGhatFam P F Qn) (ZetaQ.Btr P F Qn θ₀) (ZetaQ.BF P F Qn θ₀) ∧
      (1 - c * rate Qn) * ZetaQ.NfamQ P F Qn ≤ ZetaQ.trGhatFam P F Qn ∧
      ZetaQ.frobSqGhatFam P F Qn ≤ (κ + c * rate Qn) * ZetaQ.NfamQ P F Qn ∧
      ZetaQ.NIIFamQ P F Qn ≤ c * rate Qn * ZetaQ.NfamQ P F Qn ∧
      ZetaQ.Btr P F Qn θ₀ ≤ c * rate Qn * ZetaQ.NfamQ P F Qn ∧
      ZetaQ.BF P F Qn θ₀ ≤ c * rate Qn * Real.sqrt (ZetaQ.NfamQ P F Qn)

/-- the Shell rate `(log Q)^{−θ}`. -/
def shellRate (θ : ℝ) (Qn : ℕ) : ℝ := Real.log (Qn : ℝ) ^ (-θ)

/-! ## §3 The headline, tree form -/

/-- **Theorem S(5/3), `1 < q ≤ Q`, tree form**: `ChallengeShell.shell_S53_qle` with the counts
`ZetaQ.NfamCount Family.qle` / `ZetaQ.N0sFamCount Family.qle` and `ZetaQ.Twin` — the exact shape of
`ZetaQ.JoinProved.theorem_one_generic_proved'` (`0.7212 ↦ 0.9059137927`, rate `log log Q/log Q ↦ (log Q)^{−θ}`),
plus the displayed hypotheses `ZeroDensityInput`, `PNTErrorTerm` and `CertS53`. -/
theorem shell_S53_qle_tree (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertS53) (r ε θ : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertS53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * ZetaQ.NfamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε)
            (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  sorry

/-- **Theorem S(5/3), dyadic, tree form** (constant `0.9031776196`, profile D53-L75). -/
theorem shell_S53_dyadic_tree (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertD53) (r ε θ : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertD53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * ZetaQ.NfamCount ZetaQ.Family.dyadic Qn (ZetaQ.Twin (Qn : ℝ) r ε)
              (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.dyadic Qn (ZetaQ.Twin (Qn : ℝ) r ε)
            (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  sorry

end ZetaShell
