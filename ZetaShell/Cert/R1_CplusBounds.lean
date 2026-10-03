/-
Node R1 (L7_1): the rational constants `C⁺` of the certificates dominate the family constants
(ssec:shell-cert "Kernel and constants", sec_shell.tex l.1019–1021: "`C⁺ = 541161617/10⁸ ≥ π⁴/18`;
`721548823/10⁸ ≥ 2π⁴/27`"). Margins (mpmath, `numerics_L7_1.py`): `1.44·10⁻⁹` and `5.26·10⁻⁹`. Dependencies: Mathlib `Real.pi_lt_d20`. Difficulty: E.
-/
import ZetaShell.Interfaces

namespace ZetaShell

theorem pi4_div18_le_Cplus : Real.pi ^ 4 / 18 ≤ ((S53L75.Cplus : ℚ) : ℝ) := by
  have h := Real.pi_lt_d20
  have h0 := Real.pi_pos
  have h4 : Real.pi ^ 4 ≤ (3.14159265358979323847 : ℝ) ^ 4 := by
    gcongr
  simp only [S53L75]
  push_cast
  nlinarith [h4]

theorem two_pi4_div27_le_Cplus : 2 * Real.pi ^ 4 / 27 ≤ ((D53L75.Cplus : ℚ) : ℝ) := by
  have h := Real.pi_lt_d20
  have h0 := Real.pi_pos
  have h4 : Real.pi ^ 4 ≤ (3.14159265358979323847 : ℝ) ^ 4 := by
    gcongr
  simp only [D53L75]
  push_cast
  nlinarith [h4]

end ZetaShell
