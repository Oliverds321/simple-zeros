/-
Node R4 (L7_1): **the certificate Props `CertS53`, `CertD53` at level A** — assembly of R3 (analytic formula), R5 (L75),
R6 (admissibility) and the kernel evaluations `CertQ.BS53_le`, `CertQ.BD53_le` (PROVED, level A, `ShellCertQ.lean`).
Difficulty: E. PROVED here modulo R3 and R5 (R6 and the kernel evaluations are proved; `S53L75.d` and `CertQ.dS53` are
the same literals, `rfl`).
-/
import ZetaShell.Cert.R3_ShellPayoffFormula
import ZetaShell.Cert.R5_ProfileL75
import ZetaShell.Cert.R6_AdmissibleOfL75

namespace ZetaShell

theorem shellBq_S53 :
    CertQ.shellBq S53L75.lam S53L75.alphaP S53L75.level S53L75.Cplus S53L75.d = CertQ.BS53 := rfl

theorem shellBq_D53 :
    CertQ.shellBq D53L75.lam D53L75.alphaP D53L75.level D53L75.Cplus D53L75.d = CertQ.BD53 := rfl

theorem certS53 : CertS53 := by
  have hL := S53L75_L75
  have hl : (0 : ℝ) < (S53L75.lam : ℝ) := by norm_num [S53L75]
  have hm := mass_pos_of_L75 S53L75 hl hL
  have hB := Bshell_eq_shellBq S53L75 (by norm_num [S53L75]) (by norm_num [S53L75]) (by norm_num [S53L75]) hm
  refine ⟨by norm_num [S53L75], by norm_num [S53L75], by norm_num [S53L75], admissible_of_L75 S53L75 hl hL,
    hL, ?_⟩
  rw [hB, shellBq_S53]
  have h := CertQ.BS53_le
  have h' : ((CertQ.BS53 : ℚ) : ℝ) ≤ ((2 - 9059137927 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast h
  simpa [PcertS53] using h'

theorem certD53 : CertD53 := by
  have hL := D53L75_L75
  have hl : (0 : ℝ) < (D53L75.lam : ℝ) := by norm_num [D53L75]
  have hm := mass_pos_of_L75 D53L75 hl hL
  have hB := Bshell_eq_shellBq D53L75 (by norm_num [D53L75]) (by norm_num [D53L75]) (by norm_num [D53L75]) hm
  refine ⟨by norm_num [D53L75], by norm_num [D53L75], by norm_num [D53L75], admissible_of_L75 D53L75 hl hL,
    hL, ?_⟩
  rw [hB, shellBq_D53]
  have h := CertQ.BD53_le
  have h' : ((CertQ.BD53 : ℚ) : ℝ) ≤ ((2 - 9031776196 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast h
  simpa [PcertD53] using h'

end ZetaShell
