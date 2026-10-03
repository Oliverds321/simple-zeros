/-
Node Z1 (L7_1): the named hypothesis gives the draft's abstract (B) and (LF) with the (D1′) parameters
(sec_shell.tex l.756–762: "`c₀ = 2`, `A* = sup_{[1/2,4/5]} 3/(2−σ) = 5/2` …"): (B) with `h_B = 1`, `b₀ = A`,
`c(σ) = 3/(2−σ)`, `σ_LF = 4/5`; (LF) with `σ_LF = 4/5`, `h_LF = 1`, `c₀ = 2`.
Dependencies: `ZeroDensityInput` only. Difficulty: E (rpow monotone in the exponent for base `R²H ≥ 1`;
`log(RH) > 0`; `C ↦ |C|`).
-/
import ZetaShell.Interfaces

namespace ZetaShell

theorem zdi_to_bulk_logfree (hD : ZeroDensityInput) :
    (∃ b0 : ℝ, BulkHybrid 1 b0 (4 / 5) cMontgomery) ∧ LogFreeHybrid (4 / 5) 1 2 := by
  constructor
  · obtain ⟨A, C, hC⟩ := hD.montgomery
    refine ⟨A, fun ε hε => ⟨|C|, fun R hR H hH σ hσ1 hσ2 => ?_⟩⟩
    have h := hC R hR H hH σ (by linarith) (by linarith)
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hx : (1 : ℝ) ≤ (R : ℝ) ^ 2 * H := by nlinarith
    have hL : 0 < Real.log ((R : ℝ) * H) := Real.log_pos (by nlinarith)
    have hLA : 0 < Real.log ((R : ℝ) * H) ^ A := Real.rpow_pos_of_pos hL A
    have he : cMontgomery σ * (1 - σ) = 3 * (1 - σ) / (2 - σ) := by
      unfold cMontgomery; field_simp
    rw [Real.rpow_one, he]
    have hTQ : H * (R : ℝ) ^ 2 = (R : ℝ) ^ 2 * H := by ring
    have hTQ' : H * (R : ℝ) = (R : ℝ) * H := by ring
    rw [hTQ, hTQ'] at h
    have hmono : ((R : ℝ) ^ 2 * H) ^ (3 * (1 - σ) / (2 - σ))
        ≤ ((R : ℝ) ^ 2 * H) ^ (3 * (1 - σ) / (2 - σ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hpos : 0 ≤ ((R : ℝ) ^ 2 * H) ^ (3 * (1 - σ) / (2 - σ)) := Real.rpow_nonneg (by linarith) _
    calc Nstar R σ H ≤ C * (((R : ℝ) ^ 2 * H) ^ (3 * (1 - σ) / (2 - σ)) * Real.log ((R : ℝ) * H) ^ A) := h
      _ ≤ |C| * (((R : ℝ) ^ 2 * H) ^ (3 * (1 - σ) / (2 - σ)) * Real.log ((R : ℝ) * H) ^ A) := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * (((R : ℝ) ^ 2 * H) ^ (3 * (1 - σ) / (2 - σ) + ε) * Real.log ((R : ℝ) * H) ^ A) := by
          gcongr
      _ = |C| * ((R : ℝ) ^ 2 * H) ^ (3 * (1 - σ) / (2 - σ) + ε) * Real.log ((R : ℝ) * H) ^ A := by ring
  · intro ε hε
    obtain ⟨C, hC⟩ := hD.jutila ε hε
    refine ⟨C, fun R hR H hH σ hσ1 hσ2 => ?_⟩
    rw [Real.rpow_one]
    exact hC R hR H (by linarith) σ hσ1 hσ2

end ZetaShell
