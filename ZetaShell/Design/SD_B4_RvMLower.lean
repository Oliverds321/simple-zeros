/-
Node SD-B4 (L7_7, F1b): the family Riemann–von Mangoldt lower bound `FamRvMLower qle` along the Shell design.
Verbatim copy of `ZetaQ.famRvMLower_of_design` (`Budget.lean:2974`), whose proof reads only `Valid`, `P.Q`, `P.T`
from the design (no λ, no profile). Paper §9, §12.2. Deps: `famRvM_lower_from_tree`, `residue_small_eventually`,
`rvm_error_small`. Difficulty E.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

open ZetaQ Filter

theorem famRvMLower_shell (S : ShellProfile) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P : ParamsQ,
      ShellDesignM S r ε (n : ℝ) P → FamRvMLower Family.qle n P := by
  obtain ⟨A, T₀, hA, hlow⟩ := famRvM_lower_from_tree
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop := by
    have hre : (0 : ℝ) < r + ε := by linarith
    exact (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  filter_upwards [residue_small_eventually (ε := 1 / 200) (by norm_num),
    rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀,
    eventually_ge_atTop 2] with n hres herr hT0 hn2
  intro P hdes
  obtain ⟨hP, hQ, hT, -⟩ := hdes
  have hTpos : (0 : ℝ) < P.T := T_posQ hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey := hlow P hP (by rw [hT]; exact hT0) n hn2 hQ
  have hM0 : (0 : ℝ) < P.T / (2 * Real.pi) := by positivity
  have hS0 : (0 : ℝ) ≤ Family.sizeR Family.qle n := by
    unfold Family.sizeR; positivity
  have h1 : P.T / (2 * Real.pi) * (19 * (n : ℝ) * (1 + Real.log n) ^ 3)
      ≤ Family.sizeR Family.qle n * (P.T / (2 * Real.pi)) / 200 := by
    have h := mul_le_mul_of_nonneg_left hres hM0.le
    nlinarith [h]
  have hlogpos : (0 : ℝ) ≤ Real.log ((n : ℝ) * (P.T + 2)) := by
    apply Real.log_nonneg
    have hn : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    nlinarith
  have h2 : A * (Family.sizeR Family.qle n * Real.log ((n : ℝ) * (P.T + 2)))
      ≤ Family.sizeR Family.qle n * (P.T / (2 * Real.pi)) / 200 := by
    have herr' : 400 * Real.pi * A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T := by
      rw [hT]; exact herr
    have hstep : A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T / (2 * Real.pi) / 200 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith [herr']
    nlinarith [mul_le_mul_of_nonneg_left hstep hS0]
  unfold FamRvMLower famAvgLlow rvmSlack
  have hexp : Family.sizeR Family.qle n
        * (P.T / (2 * Real.pi) * (famAvgL Family.qle P - 1 / 100))
      = Family.sizeR Family.qle n * (P.T / (2 * Real.pi) * famAvgL Family.qle P)
        - Family.sizeR Family.qle n * (P.T / (2 * Real.pi)) / 200
        - Family.sizeR Family.qle n * (P.T / (2 * Real.pi)) / 200 := by ring
  rw [hexp]
  linarith [hkey, h1, h2]

end ZetaShell.Design
