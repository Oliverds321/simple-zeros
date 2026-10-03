/-
Node KA (L7_3): a killed-kernel frame gives the family bound `(2 − κ − c·rate)·𝒩 ≤ Σ_χ N^s_{0,χ}` — ZetaQ's
Proposition 3.1 (`ZetaQ.prop_3_1_pair_moment_certificate`) at each design point, with the frame's bracket
`4r₁ + r₂ + 3r₃ + 4r₄ + 2r₅√(κ + r₂) + r₅² ≤ c·rate`.
Draft: thm:one-prime's proof ("Proposition 3.1 is applied with `κ_C := B^K_C(v_K)`"). Same shape as L7_1's F2
(`lean_work/L7_1/skeleton/F2_ShellAssembly.lean`), for the bracket-form frame.
Dependencies: trunk `ZetaQ.prop_3_1_pair_moment_certificate`, `ZetaQ.NfamQ_nonneg`. Difficulty: E. PROVED.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section
open Filter Topology

namespace ZetaShell
namespace LemmaK

/-- **KA.** -/
theorem k_assembly (F : ZetaQ.Family) (r ε : ℝ) (S : KProfile) (κ : ℝ) (rate : ℕ → ℝ)
    (Fr : KFrame F r ε S κ rate) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (2 - κ - c * rate Qn) * ZetaQ.NfamCount F Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount F Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₁, hQ₁⟩ := Fr.exists_design
  obtain ⟨c, hc, hrows⟩ := Fr.rows
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hrows
  refine ⟨max Q₁ (N₀ : ℝ), c, hc, fun Qn hQn => ?_⟩
  obtain ⟨P, hP⟩ := hQ₁ (Qn : ℝ) (le_trans (le_max_left _ _) hQn)
  have hNQ : N₀ ≤ Qn := by exact_mod_cast le_trans (le_max_right _ _) hQn
  obtain ⟨r₁, r₂, r₃, r₄, r₅, θ₀, -, hBtr0, hBF0, hκ, hdisp, htr, hfrob, hNII, hBtr, hBF, hbr⟩ :=
    hN₀ Qn hNQ P hP
  have hN : 0 ≤ ZetaQ.NfamQ P F Qn := ZetaQ.NfamQ_nonneg P F Qn
  have h31 := ZetaQ.prop_3_1_pair_moment_certificate hN hBtr0 hBF0 hκ hdisp htr hfrob hNII hBtr hBF
  have hT := Fr.T_eq _ _ hP
  have key : (2 - κ - c * rate Qn) * ZetaQ.NfamQ P F Qn ≤ ZetaQ.N0sFamQ P F Qn :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) hN) h31
  simpa [ZetaQ.NfamQ, ZetaQ.N0sFamQ, hT] using key

end LemmaK
end ZetaShell
