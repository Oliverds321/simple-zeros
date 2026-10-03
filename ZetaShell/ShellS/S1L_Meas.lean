/-
S1L_Meas (L7_5b, 1 Oct 2026): leaf `ringS_aesm` of S1 — `s ↦ W(s−s₀) Ring(s)` is a.e.-strongly measurable.
On `|s − s₀| < 1` the sum `Σ_{0<n≤N(s)}` of `Ring(s)` equals the sum up to the FIXED `M = ⌊e^{s₀+2}⌋`
(`a^{near,P}_n(s) = 0` for `n > e^{s+1}` when `κ ≤ 1`); with `M` fixed, the integrand is jointly continuous in
`(s, β)` and the `β`-integral is strongly measurable in `s` (`StronglyMeasurable.integral_prod_right'`).
-/
import ZetaShell.ShellS.S1L_Twist

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem aNearP_continuous (Qn : ℕ) (T κ : ℝ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (n : ℕ) :
    Continuous (fun s => aNearP Qn T κ Ξ s n) := by
  unfold aNearP
  split_ifs
  · unfold TrackF.acoefS
    have h1 : Continuous (fun s : ℝ => TrackF.DTk T (s - Real.log n)) := by
      simp only [DTk_eq_DT, DT_eq_DTf]
      exact (ZetaShell.DTFacts.DTf_continuous T).comp (continuous_id.sub continuous_const)
    have h2 : Continuous (fun s : ℝ => ((Ξ ((Real.log n - s) / κ) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hΞ.smooth.continuous.comp
        ((continuous_const.sub continuous_id).div_const κ))
    exact (continuous_const.mul h1).mul h2
  · exact continuous_const

theorem aNearP_eq_zero_big (Qn : ℕ) (T κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (s : ℝ) (n : ℕ) (hn : Real.exp (s + 1) < n) : aNearP Qn T κ Ξ s n = 0 := by
  unfold aNearP
  split_ifs
  · have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn
    have hlog : s + 1 < Real.log n := by rw [Real.lt_log_iff_exp_lt hn0]; exact hn
    have hΞ0 : Ξ ((Real.log n - s) / κ) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have h1 := (hΞ.supp hmem).2
      rw [div_lt_one hκ] at h1
      linarith
    rw [hΞ0]; simp
  · rfl

theorem ringS_aesm' (Qn : ℕ) (T κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (K ε s₀ : ℝ)
    (W : ℝ → ℝ) (hW : AvgWeight W) :
    AEStronglyMeasurable (fun s => W (s - s₀) * RingS Qn T κ Ξ K ε s₀ s) volume := by
  set M : ℕ := ⌊Real.exp (s₀ + 2)⌋₊ with hM
  set R1 := R1S Qn ε s₀
  have hfix : ∀ s, W (s - s₀) * RingS Qn T κ Ξ K ε s₀ s
      = W (s - s₀) * TrackF.ringMass Qn R1 M K (aNearP Qn T κ Ξ s) := by
    intro s
    by_cases h0 : W (s - s₀) = 0
    · rw [h0, zero_mul, zero_mul]
    have hs : s - s₀ < 1 := (hW.supp (subset_tsupport _ h0)).2
    congr 1
    unfold RingS TrackF.ringMass
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro b _
    congr 1; funext β
    congr 2
    unfold ZetaQ.expSum
    have hNM : Nnear s ≤ M := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hNM]
    have hz : ∑ n ∈ Finset.Ioc (Nnear s) M, aNearP Qn T κ Ξ s n * ZetaQ.e (n * ((b : ℝ) / r + β)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hn1 : Nnear s + 1 ≤ n := (Finset.mem_Ioc.mp hn).1
      have hlt : Real.exp (s + 1) < n := by
        have h1 : Real.exp (s + 1) < (Nnear s : ℝ) + 1 := Nat.lt_floor_add_one _
        have h2 : (Nnear s : ℝ) + 1 ≤ n := by exact_mod_cast hn1
        linarith
      rw [aNearP_eq_zero_big Qn T κ hκ hκ1 Ξ hΞ s n hlt, zero_mul]
    rw [hz, add_zero]
  simp_rw [hfix]
  have hWc : Continuous (fun s => W (s - s₀)) := hW.smooth.continuous.comp (continuous_id.sub continuous_const)
  refine hWc.aestronglyMeasurable.mul ?_
  apply StronglyMeasurable.aestronglyMeasurable
  unfold TrackF.ringMass
  apply Finset.stronglyMeasurable_fun_sum
  intro r _
  apply Finset.stronglyMeasurable_fun_sum
  intro b _
  have hcont : Continuous (fun p : ℝ × ℝ =>
      ‖ZetaQ.expSum M (aNearP Qn T κ Ξ p.1) ((b : ℝ) / r + p.2)‖ ^ 2) := by
    unfold ZetaQ.expSum
    have hterm : ∀ n : ℕ, Continuous (fun p : ℝ × ℝ =>
        aNearP Qn T κ Ξ p.1 n * ZetaQ.e ((n : ℝ) * ((b : ℝ) / r + p.2))) := by
      intro n
      refine ((aNearP_continuous Qn T κ Ξ hΞ n).comp continuous_fst).mul ?_
      unfold ZetaQ.e
      fun_prop
    have hsum : Continuous (fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ioc 0 M, aNearP Qn T κ Ξ p.1 n * ZetaQ.e ((n : ℝ) * ((b : ℝ) / r + p.2))) :=
      continuous_finset_sum _ fun n _ => hterm n
    exact hsum.norm.pow 2
  exact (hcont.stronglyMeasurable).integral_prod_right'

end ShellS
end ZetaShell
