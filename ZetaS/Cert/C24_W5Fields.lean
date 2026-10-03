/-
lean_work/L6_1/C24_W5Fields.lean — track C node C24 (agent L6_1, 28 Sep 2026; statements from
lean_work/L1_1/nodes/C24_W5Fields.lean, unchanged): the three proof fields of the witness `W5`, its reversal
symmetry and its constants a₁ = Σ_i b_i(1), a₂ = Σ_i b_i(2), ν = Σ_l μ_l. Finite rational checks.
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

theorem gam5_nonneg (s i : ℕ) : (0 : ℚ) ≤ gam5 s i := by
  unfold gam5
  split <;> norm_num

theorem W5_gam_nonneg : ∀ s ∈ Finset.Icc 1 (5 - 1), ∀ i ∈ Finset.range (5 - s), (0 : ℝ) ≤ (gam5 s i : ℝ) := by
  intro s _ i _
  exact_mod_cast gam5_nonneg s i

theorem W5_gam_sum : ∀ s ∈ Finset.Icc 1 (5 - 1), ∑ i ∈ Finset.range (5 - s), (gam5 s i : ℝ) = 2 := by
  intro s hs
  rw [Finset.mem_Icc] at hs
  obtain ⟨h1, h2⟩ := hs
  interval_cases s <;> norm_num [Finset.sum_range_succ, gam5]

theorem W5_mu_nonneg : ∀ l : Fin (5 - 1), (0 : ℝ) ≤ ((mu5.getD l 0 : ℚ) : ℝ) := by
  intro l
  fin_cases l <;> norm_num [mu5]

theorem W5_revSymm' : W5.IsRevSymm := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs i hi
    rw [Finset.mem_Icc] at hs
    rw [Finset.mem_range] at hi
    obtain ⟨h1, h2⟩ := hs
    show (gam5 s i : ℝ) = (gam5 s (5 - s - 1 - i) : ℝ)
    interval_cases s <;> interval_cases i <;> norm_num [gam5]
  · intro l
    show ((mu5.getD l 0 : ℚ) : ℝ) = ((mu5.getD l.rev 0 : ℚ) : ℝ)
    fin_cases l <;> norm_num [mu5]
  · intro i j
    show (b5 i j : ℝ) = (b5 i.rev j : ℝ)
    fin_cases i <;> fin_cases j <;> rfl

theorem W5_consts' : W5.a 0 = 1280197 / 10 ^ 8 ∧ W5.a 1 = 48749 / 3125000 ∧ W5.nu = 1 / 125 := by
  have ha0 : ∑ i : Fin 5, b5 i 0 = 1280197 / 10 ^ 8 := by
    rw [Fin.sum_univ_five, show b5 0 0 = 64333 / 25000000 from rfl, show b5 1 0 = 64617 / 25000000 from rfl,
      show b5 2 0 = 248597 / 100000000 from rfl, show b5 3 0 = 64617 / 25000000 from rfl,
      show b5 4 0 = 64333 / 25000000 from rfl]
    norm_num
  have ha1 : ∑ i : Fin 5, b5 i 1 = 48749 / 3125000 := by
    rw [Fin.sum_univ_five, show b5 0 1 = 310701 / 100000000 from rfl, show b5 1 1 = 61913 / 20000000 from rfl,
      show b5 2 1 = 79859 / 25000000 from rfl, show b5 3 1 = 61913 / 20000000 from rfl,
      show b5 4 1 = 310701 / 100000000 from rfl]
    norm_num
  have hnu : ∑ l : Fin (5 - 1), mu5.getD l 0 = 1 / 125 := by
    rw [Fin.sum_univ_four, show mu5.getD ((0 : Fin (5 - 1)) : ℕ) 0 = 3833 / 2500000 from rfl,
      show mu5.getD ((1 : Fin (5 - 1)) : ℕ) 0 = 6167 / 2500000 from rfl,
      show mu5.getD ((2 : Fin (5 - 1)) : ℕ) 0 = 6167 / 2500000 from rfl,
      show mu5.getD ((3 : Fin (5 - 1)) : ℕ) 0 = 3833 / 2500000 from rfl]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · show ∑ i : Fin 5, (b5 i 0 : ℝ) = 1280197 / 10 ^ 8
    rw [← Rat.cast_sum, ha0]
    norm_num
  · show ∑ i : Fin 5, (b5 i 1 : ℝ) = 48749 / 3125000
    rw [← Rat.cast_sum, ha1]
    norm_num
  · show ∑ l : Fin (5 - 1), ((mu5.getD l 0 : ℚ) : ℝ) = 1 / 125
    rw [← Rat.cast_sum, hnu]
    norm_num

end ZetaS.CertV2
