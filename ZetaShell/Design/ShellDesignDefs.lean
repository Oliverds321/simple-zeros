/-
lean_work/L7_7/ShellDesignDefs.lean — the DESIGN LAYER of the family follow-up at a new bandwidth (L7_7, 28 Sep 2026).
Namespace `ZetaShell.Design`. NON-INVASIVE: imports `ZetaQ` (green, read-only) and L7_1's `ShellInterfaces`, edits
neither. Intended home: `ZetaShell/Design/Defs.lean`.

Design decision (report `lean_board/reports/L7_7_design_layer.md` §1):
  * `ZetaQ.ParamsQ` and `ZetaQ.ParamsQ.Valid` are REUSED unchanged. `ParamsQ.lam` is free in `(0,2)`, `prof` is an
    arbitrary `Polynomial ℝ`; `Valid` caps only `λ < 2`. Its one field that the degree-12 profile S53-L75 meets only
    eventually is `a_ge : 3/4 ≤ aQ` (⟨p²⟩ − 3/4 = 2.00001·10⁻⁷); it is met by taking `ℒ` large (eventual form),
    NOT by relaxing the floor (L7_4 correction 1: `Ends.lean:3089` needs a ≥ 0.7409 and `psi0_le` needs 3/4).
  * `ZetaQ.DesignOfRecordM` pins `P.lam = F.lamStar` and `P.prof = F.designProfile`; it cannot be reused. The
    replacement `DesignAtM lam prof` is `DesignOfRecordM`'s conjunction with the two pins made PARAMETERS, in the SAME
    order, so `DesignOfRecordM F r ε Q P` is DEFINITIONALLY `DesignAtM F.lamStar F.designProfile r ε Q P`
    (node A0) and every projection `hdes.1`, `hdes.2.1`, … reads the same field in both.
-/
import ZetaShell.Interfaces
import ZetaQ

noncomputable section

open Filter

namespace ZetaShell

namespace ShellProfile

/-- The Shell profile as a `Polynomial ℝ` in the scale-free variable `t = u/ℒ`:
`p(t) = Σᵢ dᵢ (2t/λ)^{2i}` (the data of `ShellProfile.p`, ChallengeShell §3). Degree `2·(len d − 1)`
(12 for S53-L75). -/
def poly (S : ShellProfile) : Polynomial ℝ :=
  ∑ i : Fin S.d.length, Polynomial.C (((S.d.get i : ℚ) : ℝ)) *
    (Polynomial.C (2 / (S.lam : ℝ)) * Polynomial.X) ^ (2 * (i : ℕ))

end ShellProfile

namespace Design

open ZetaQ

/-- **The design of record with margin, at a FREE bandwidth `lam` and a FREE profile `prof`.**
`ZetaQ.DesignOfRecordM` (`ZetaQ/Budget.lean:1186`) verbatim, with its two pins `P.lam = F.lamStar` and
`P.prof = F.designProfile` replaced by `P.lam = lam` and `P.prof = prof`, in the same positions. -/
def DesignAtM (lam : ℝ) (prof : Polynomial ℝ) (r ε Q : ℝ) (P : ParamsQ) : Prop :=
  P.Valid ∧ P.Q = Q ∧ P.T = Twin Q r ε ∧ P.lam = lam ∧ P.w = wDesign P.LL r ∧
    SideCondWrange P ∧ SideCondWD0 P ∧ SideCondD0range P ∧ SideCondTfloor P ∧
    ClosingAtDesignM P ∧ P.ϱ = Zeta23.Taper.rhoTwo ∧ P.prof = prof

/-- **The Shell design** at the certificate's own bandwidth `S.lam` and profile `S.poly`. -/
def ShellDesignM (S : ShellProfile) (r ε Q : ℝ) (P : ParamsQ) : Prop :=
  DesignAtM (S.lam : ℝ) S.poly r ε Q P

/-- The zone-row slope for S53-L75 with the Shell strip kernel: `2(C⁺−1)ψ_v(1) = 1.9455…` (L7_2 §0.4(iii),
`slopes.out`), rounded up. Replaces `ZetaQ.sZone = 0.5073` (`Budget.lean:622`) in the Shell's zone row. -/
def sZoneShell : ℝ := 1.95

/-- The ends constant of Lemma 8.1 at `λ = 1.91` by the Minkowski split (L7_4 D4): `0.4983 ≤ 0.52`.
Replaces `ZetaQ.c1Ends = 0.41` (`Defs.lean:394`). -/
def c1EndsShell : ℝ := 0.52

/-- The Gevrey gate for the product window at S53-L75: `B′ ≤ 5·10⁴` (L7_2 §3: 42 952 at `x₁ → 0`, 48 698 at
`x₁ = 1/52`). Replaces the literal `40000` of `Budget.lean:4542,5719,5847`. -/
def gevreyGateShell : ℝ := 50000

/-- The regime exponent `δ = (2 − λ)/2 = 9/200` at `λ = 191/100`: `X ≤ Q^{2−δ}` eventually. Replaces
`design_regime`'s `X ≤ Q^{3/2}` (`FrobAssembly.lean:1151`). -/
def deltaShell : ℝ := 9 / 200

end Design

end ZetaShell
