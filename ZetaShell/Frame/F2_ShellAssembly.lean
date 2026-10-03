/-
Node F2 (L7_1): a Shell frame gives the family bound `(2 − κ − c·rate)·𝒩 ≤ Σ_χ N^s_{0,χ}` — ZetaQ's Proposition 3.1
(`ZetaQ.prop_3_1_pair_moment_certificate`) at each design point; the budget
`4r₁ + r₂ + 3r₃ + 4r₄ + 2r₅√(κ + r₂) + r₅²` is `≤ c′·rate` once `rate → 0`, `rate ≥ 0`.
Draft: thm:shell-1pp (the step "P ≥ 2 − B_{α′}(v_p) − O(…)"). Dependencies: trunk
`ZetaQ.prop_3_1_pair_moment_certificate`, `ZetaQ.NcountQ_nonneg`. Difficulty: M.
-/
import ZetaShell.Interfaces

namespace ZetaShell

open Filter Topology

theorem shell_assembly (F : ZetaQ.Family) (r ε : ℝ) (S : ShellProfile) (κ : ℝ) (rate : ℕ → ℝ)
    (hrate : Tendsto rate atTop (𝓝 0)) (hrate0 : ∀ᶠ Qn : ℕ in atTop, 0 ≤ rate Qn) (hκ : 0 ≤ κ)
    (Fr : ShellFrame F r ε S κ rate) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (2 - κ - c * rate Qn) * ZetaQ.NfamCount F Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount F Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₁, hQ₁⟩ := Fr.exists_design
  obtain ⟨c, hc, hrows⟩ := Fr.rows
  have hsmall : ∀ᶠ Qn : ℕ in atTop, rate Qn ≤ 1 / c :=
    hrate.eventually (ge_mem_nhds (by positivity))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hrows.and (hrate0.and hsmall))
  refine ⟨max Q₁ (N₀ : ℝ), c * (17 + 2 * κ), by positivity, fun Qn hQn => ?_⟩
  obtain ⟨P, hP⟩ := hQ₁ (Qn : ℝ) (le_trans (le_max_left _ _) hQn)
  have hNQ : N₀ ≤ Qn := by exact_mod_cast le_trans (le_max_right _ _) hQn
  obtain ⟨hrow, hr0, hr1⟩ := hN₀ Qn hNQ
  obtain ⟨θ₀, -, hBtr0, hBF0, hdisp, htr, hfrob, hNII, hBtr, hBF⟩ := hrow P hP
  set x := c * rate Qn with hx
  have hx0 : 0 ≤ x := mul_nonneg hc.le hr0
  have hx1 : x ≤ 1 := by
    rw [hx]
    calc c * rate Qn ≤ c * (1 / c) := by gcongr
      _ = 1 := by field_simp
  have hN : 0 ≤ ZetaQ.NfamQ P F Qn := ZetaQ.NfamQ_nonneg P F Qn
  have h31 := ZetaQ.prop_3_1_pair_moment_certificate (r₁ := x) (r₂ := x) (r₃ := x) (r₄ := x) (r₅ := x)
    hN hBtr0 hBF0 (by linarith) hdisp htr hfrob hNII hBtr hBF
  -- the budget is at most `(17 + 2κ)·x`
  have hsq : Real.sqrt (κ + x) ≤ κ + 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hbud : 4 * x + x + 3 * x + 4 * x + 2 * x * Real.sqrt (κ + x) + x ^ 2 ≤ (17 + 2 * κ) * x := by
    have h1 : 2 * x * Real.sqrt (κ + x) ≤ 2 * x * (κ + 2) := by gcongr
    have h2 : x ^ 2 ≤ x := by nlinarith
    nlinarith
  have hT := Fr.T_eq _ _ hP
  have key : (2 - κ - c * (17 + 2 * κ) * rate Qn) * ZetaQ.NfamQ P F Qn ≤ ZetaQ.N0sFamQ P F Qn := by
    calc (2 - κ - c * (17 + 2 * κ) * rate Qn) * ZetaQ.NfamQ P F Qn
        = (2 - κ - (17 + 2 * κ) * x) * ZetaQ.NfamQ P F Qn := by rw [hx]; ring
      _ ≤ (2 - κ - (4 * x + x + 3 * x + 4 * x + 2 * x * Real.sqrt (κ + x) + x ^ 2))
            * ZetaQ.NfamQ P F Qn := by gcongr
      _ ≤ ZetaQ.N0sFamQ P F Qn := h31
  simpa [ZetaQ.NfamQ, ZetaQ.N0sFamQ, hT] using key

end ZetaShell
