/-
S1L_Twist (L7_5b, 1 Oct 2026): leaf `twist_sub_model` of S1 — the twisted near-prime sum minus the model is
`−(2π)⁻¹ (S_χ − P_χ)`.
-/
import ZetaShell.ShellS.S1_Defs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem DTk_eq_DT (T v : ℝ) : TrackF.DTk T v = DT T v := rfl

theorem e_eq_eA (x : ℝ) : ZetaQ.e x = eA x := rfl

theorem twist_sub_model' (Qn : ℕ) (T κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (s : ℝ)
    (hQ : (Qn : ℝ) ≤ Real.exp (s - 1)) (r : ℕ) (χ : DirichletCharacter ℂ r) (β : ℝ) :
    TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β - (if r = 1 then Mmod T κ Ξ s β else 0)
      = -(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (Schi χ T κ Ξ s β - PPart χ T κ Ξ s β) := by
  set N := Nnear s with hN
  set g : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * As T κ Ξ s n * eA (n * β)
    with hg
  -- the tsum of `Schi` is the finite sum over `0 < n ≤ N`
  have htsum : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * As T κ Ξ s n * eA (n * β))
      = ∑ n ∈ Finset.Ioc 0 N, g n := by
    apply tsum_eq_sum
    intro n hn
    rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hn
    rcases hn with h0 | hbig
    · have : n = 0 := by omega
      subst this; simp
    · have hAs : As T κ Ξ s n = 0 := by
        apply As_eq_zero_outside T κ hκ Ξ hΞ s
        intro hmem
        have h1 : Real.exp (s + 1) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : (N : ℝ) + 1 ≤ n := by exact_mod_cast hbig
        have h3 : Real.exp (s + κ) ≤ Real.exp (s + 1) := Real.exp_le_exp.mpr (by linarith)
        linarith [hmem.2]
      rw [hAs]; simp
  -- primes `n ≤ Q` carry nothing
  have hsmall : ∀ n : ℕ, (n : ℝ) ≤ Qn → As T κ Ξ s n = 0 := by
    intro n hn
    apply As_eq_zero_outside T κ hκ Ξ hΞ s
    intro hmem
    have h3 : Real.exp (s - 1) ≤ Real.exp (s - κ) := Real.exp_le_exp.mpr (by linarith)
    linarith [hmem.1]
  have hsplit : ∑ n ∈ Finset.Ioc 0 N, g n
      = (∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => n.Prime ∧ (Qn : ℝ) < n), g n) + PPart χ T κ Ξ s β := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 N) (fun n : ℕ => n.Prime ∧ (Qn : ℝ) < n)]
    congr 1
    unfold PPart
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · by_cases hq : (Qn : ℝ) < n
      · simp [hp, hq]
      · have hAs := hsmall n (le_of_not_gt hq)
        simp [hp, hq, hg, hAs]
    · simp [hp, hg]
  have htw : TrackF.twistSum N (aNearP Qn T κ Ξ s) χ β
      = -(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => n.Prime ∧ (Qn : ℝ) < n), g n := by
    unfold TrackF.twistSum
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    unfold aNearP
    split_ifs with h
    · rw [hg]
      simp only [TrackF.acoefS, As, DTk_eq_DT, e_eq_eA]
      push_cast
      ring
    · simp
  have hSchi : Schi χ T κ Ξ s β = (∑ n ∈ Finset.Ioc 0 N, g n)
      - (if r = 1 then ∫ y in Set.Ioi (0 : ℝ), As T κ Ξ s y * eA (y * β) else 0) := by
    unfold Schi; rw [htsum]
  rw [htw, hSchi, hsplit]
  unfold Mmod
  split_ifs <;> ring

end ShellS
end ZetaShell
