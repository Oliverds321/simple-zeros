/-
Node SD-C1 (L7_7, constants): the admissible-window constant is a CONSTANT along the Shell design,
`P.cWin = cWinShell S = c_ϱ₂ + M₁λ + (M₁λ)² + M₂λ²` (coefficient-sum majorants of `S.poly` on `[−λ/2, λ/2]`).
Replaces `ZetaQ.cWinDesign` / `cWin_of_design` (`Budget.lean:7608–7618`). The trace row (SD-B3) needs only that it
is a constant (`T ≥ 400π·cErr(cWin)` eventually); the ends row (F1c) needs its value.
Value (`sanity_L7_7.py`, exact Mpoly, `c_ϱ₂ ≈ 31.3` from paper §8): `M₁ = 43.9`, `M₂ = 289`,
`cWinShell S53L75 ≈ 8.2·10³` (L7_2: 8 183; design of record 548). Deps: none. Difficulty E.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

open ZetaQ

/-- `c_W` at the Shell design (`ZetaQ.cWinDesign` with `(λ*_F, p_F) ↦ (S.lam, S.poly)`). -/
noncomputable def cWinShell (S : ShellProfile) : ℝ :=
  Zeta23.Taper.cRho Zeta23.Taper.rhoTwo
    + ParamsQ.Mpoly S.poly ((S.lam : ℝ) / 2) 1 * (S.lam : ℝ)
    + (ParamsQ.Mpoly S.poly ((S.lam : ℝ) / 2) 1 * (S.lam : ℝ)) ^ 2
    + ParamsQ.Mpoly S.poly ((S.lam : ℝ) / 2) 2 * (S.lam : ℝ) ^ 2

theorem cWin_of_shellDesignM {S : ShellProfile} {r ε Q : ℝ} {P : ParamsQ}
    (hdes : ShellDesignM S r ε Q P) : P.cWin = cWinShell S := by
  obtain ⟨-, -, -, hlam, -, -, -, -, -, -, hϱ, hprof⟩ := hdes
  unfold ParamsQ.cWin ParamsQ.profM cWinShell
  rw [hlam, hϱ, hprof]

end ZetaShell.Design
