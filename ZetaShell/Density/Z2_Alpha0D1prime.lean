/-
Node Z2 (L7_1): the threshold of (D1′): `A* = sup_{[1/2,4/5]} 3/(2−σ) = 5/2`, `M = max(5/2, 2) = 5/2`,
`α₀ = min(M/(M−1), 2) = 5/3` (sec_shell.tex l.760–762, eq:shell-alpha0); at `α′ = 2497/1500` the two conditions of
the threshold paragraph (l.735–740) hold: bulk `A*(2 − 2/α′) < 2`, log-free `c₀(2 − 2/α′) < 2`.
Dependencies: none. Difficulty: E (sSup of the image of a monotone function on a compact interval).
-/
import ZetaShell.Interfaces

namespace ZetaShell

theorem Astar_montgomery : Astar cMontgomery (4 / 5) = 5 / 2 := by
  unfold Astar
  apply IsGreatest.csSup_eq
  refine ⟨⟨4 / 5, ⟨by norm_num, le_refl _⟩, by norm_num [cMontgomery]⟩, ?_⟩
  rintro y ⟨σ, ⟨h1, h2⟩, rfl⟩
  unfold cMontgomery
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem alpha0_D1prime : alpha0 (Mexp cMontgomery (4 / 5) 2) = 5 / 3 := by
  unfold alpha0 Mexp
  rw [Astar_montgomery]
  norm_num [max_def, min_def]

theorem conditions_S53 :
    (5 / 2 : ℝ) * (2 - 2 / (2497 / 1500)) < 2 ∧ (2 : ℝ) * (2 - 2 / (2497 / 1500)) < 2 := by
  constructor <;> norm_num

end ZetaShell
