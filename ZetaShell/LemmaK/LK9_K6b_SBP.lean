/-
L7_9 round 2, sub-node K6b′ of `principal_arc_mass` (K6): Step 2 of lem:K-P by DISCRETE SUMMATION BY PARTS, in
place of Gallagher's `L²` lemma (which needs Plancherel on `ℝ`). For `|β| ≤ Δ`,
`S(β) = C₀(N)e(Nβ) − Σ_{n<N} C₀(n)(e((n+1)β) − e(nβ))` and `|e(β) − 1| = 2|sin πβ| ≤ 2π|β|`, so
`|S(β)| ≤ |C₀(N)| + 2πΔ Σ_{n<N}|C₀(n)|` and `∫_{−Δ}^{Δ}|S|² ≤ 2Δ(|C₀(N)| + 2πΔΣ_{n<N}|C₀(n)|)²`.
Compared with Gallagher's lemma this loses a factor `≍ ℒT`, which the PNT input (`ψ(y) − y = O(y(log y)^{−A})`
for every `A`) absorbs in K6c.
-/
import ZetaShell.LemmaK.LK9_K6_Defs

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

/-- Abel summation for `expSum`. -/
theorem K6.expSum_abel (N : ℕ) (c : ℕ → ℂ) (β : ℝ) :
    ZetaQ.expSum N c β = K6.psum N c * ZetaQ.e ((N : ℝ) * β)
      - ∑ n ∈ Finset.range N, K6.psum n c * (ZetaQ.e (((n + 1 : ℕ) : ℝ) * β) - ZetaQ.e ((n : ℝ) * β)) := by
  induction N with
  | zero => simp [ZetaQ.expSum, K6.psum]
  | succ N ih =>
    have h1 : ZetaQ.expSum (N + 1) c β = ZetaQ.expSum N c β + c (N + 1) * ZetaQ.e (((N + 1 : ℕ) : ℝ) * β) := by
      unfold ZetaQ.expSum
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le N)]
    have h2 : K6.psum (N + 1) c = K6.psum N c + c (N + 1) := by
      unfold K6.psum
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le N)]
    rw [h1, ih, h2, Finset.sum_range_succ]
    ring

lemma K6.norm_e_step (n : ℕ) (β : ℝ) :
    ‖ZetaQ.e (((n + 1 : ℕ) : ℝ) * β) - ZetaQ.e ((n : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have e1 : ZetaQ.e (((n + 1 : ℕ) : ℝ) * β) - ZetaQ.e ((n : ℝ) * β)
      = ZetaQ.e ((n : ℝ) * β) * (ZetaQ.e β - 1) := by
    rw [show (((n + 1 : ℕ) : ℝ) * β) = (n : ℝ) * β + β by push_cast; ring, ZetaQ.e_add]
    ring
  rw [e1, norm_mul, ZetaQ.norm_e, one_mul, ZetaQ.norm_e_sub_one]
  have h := Real.abs_sin_le_abs (x := Real.pi * β)
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  linarith

/-- **K6b′ (summation by parts on `[−Δ, Δ]`).** -/
theorem sbp_L2 (N : ℕ) (c : ℕ → ℂ) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N c β‖ ^ 2
      ≤ 2 * Δ * (‖K6.psum N c‖ + 2 * Real.pi * Δ * ∑ n ∈ Finset.range N, ‖K6.psum n c‖) ^ 2 := by
  set B := ‖K6.psum N c‖ + 2 * Real.pi * Δ * ∑ n ∈ Finset.range N, ‖K6.psum n c‖ with hB
  have hpt : ∀ β ∈ Set.Icc (-Δ) Δ, ‖ZetaQ.expSum N c β‖ ^ 2 ≤ B ^ 2 := by
    intro β hβ
    have hβΔ : |β| ≤ Δ := abs_le.mpr ⟨hβ.1, hβ.2⟩
    have hle : ‖ZetaQ.expSum N c β‖ ≤ B := by
      rw [K6.expSum_abel]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, ZetaQ.norm_e, mul_one]
      have hs : ‖∑ n ∈ Finset.range N, K6.psum n c
            * (ZetaQ.e (((n + 1 : ℕ) : ℝ) * β) - ZetaQ.e ((n : ℝ) * β))‖
          ≤ 2 * Real.pi * Δ * ∑ n ∈ Finset.range N, ‖K6.psum n c‖ := by
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul]
        have h1 := K6.norm_e_step n β
        have h2 : 2 * Real.pi * |β| ≤ 2 * Real.pi * Δ :=
          mul_le_mul_of_nonneg_left hβΔ (by positivity)
        have h3 := norm_nonneg (K6.psum n c)
        nlinarith
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hint : IntervalIntegrable (fun β => ‖ZetaQ.expSum N c β‖ ^ 2) MeasureTheory.volume (-Δ) Δ :=
    ((ZetaQ.Gallagher.continuous_trig _ c).norm.pow 2).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith : -Δ ≤ Δ) hint
    (intervalIntegrable_const (c := B ^ 2)) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith

end LemmaK
end ZetaShell
