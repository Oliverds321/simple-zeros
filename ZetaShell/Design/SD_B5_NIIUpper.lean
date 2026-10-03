/-
Node SD-B5 (L7_7, F1b): the §9 family aggregate of H6, `FamNIIUpper qle … (2A₀)`, along the Shell design.
Verbatim copy of `ZetaQ.Margin.famNIIUpper_qle_of_designM` (`Margin.lean:199`), which reads only `Valid` and `P.Q`.
Paper §9 (H6, `A₀ = 81.26`). Deps: `residue_small_eventually`, `famNII_upper_of_residue_small`,
`JoinProved.famNIIUpper_double_of_eps`. Difficulty E.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

open ZetaQ ZetaQ.JoinCert ZetaQ.JoinProved Filter

theorem famNIIUpper_shell (S : ShellProfile) (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, ShellDesignM S r ε (Qn : ℝ) P →
      FamNIIUpper Family.qle Qn P (2 * A₀) := by
  filter_upwards [residue_small_eventually (ε := 1) one_pos, eventually_ge_atTop 2]
    with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  exact famNIIUpper_double_of_eps Family.qle Qn P hP hA₀
    (famNII_upper_of_residue_small P hP Qn hQn hQ hA₀ hloc hres)

end ZetaShell.Design
