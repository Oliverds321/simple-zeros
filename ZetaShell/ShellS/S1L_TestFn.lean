/-
S1L_TestFn (L7_5b, 1 Oct 2026): leaf `exists_testFn` of S1 — an explicit test function
`f(z) = smoothTransition(1 − (16z)²)` (smooth, even, `0 ≤ f`, support `[−1/16, 1/16]`, `f(0) = 1`) with
`Re f̂(η) ≥ ½ ∫ f > 0` on `|η| ≤ 1` (there `|2πzη| ≤ π/8 < 1`, so `cos(2πzη) ≥ 1 − ½ = ½`).
-/
import ZetaShell.ShellS.S1_Defs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- the explicit test function. -/
def bumpF (z : ℝ) : ℝ := Real.smoothTransition (1 - (16 * z) ^ 2)

theorem bumpF_support : Function.support bumpF ⊆ Set.Icc (-(1 / 16 : ℝ)) (1 / 16) := by
  intro z hz
  by_contra h
  apply hz
  apply Real.smoothTransition.zero_of_nonpos
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h <;> nlinarith

theorem bumpF_testFn : TestFn bumpF where
  smooth := Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_const.mul contDiff_id).pow 2))
  supp := (closure_minimal bumpF_support isClosed_Icc).trans (Set.Icc_subset_Ioo (by norm_num) (by norm_num))
  even := fun z => by unfold bumpF; ring_nf
  nonneg := fun z => Real.smoothTransition.nonneg _
  ne_zero := ⟨0, by simp [bumpF]⟩

theorem eA_re (x : ℝ) : (eA x).re = Real.cos (2 * Real.pi * x) := by
  rw [eA, show (2 * Real.pi * Complex.I * x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

theorem exists_testFn' : ∃ (f : ℝ → ℝ) (c : ℝ), TestFn f ∧ 0 < c ∧
    ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2 := by
  have hf := bumpF_testFn
  have hcont : Continuous bumpF := hf.smooth.continuous
  have hcs : HasCompactSupport bumpF :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hf.supp.trans Set.Ioo_subset_Icc_self)
  set I := ∫ z, bumpF z with hI
  have h0 : bumpF 0 ≠ 0 := by simp [bumpF]
  have hIpos : 0 < I := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun z => hf.nonneg z) h0
  refine ⟨bumpF, (I / 2) ^ 2, hf, by positivity, fun η hη => ?_⟩
  have hη : |η| ≤ 1 := abs_le.mpr ⟨hη.1, hη.2⟩
  have hfi : Integrable bumpF := hcont.integrable_of_hasCompactSupport hcs
  have hcosc : Continuous (fun z : ℝ => bumpF z * Real.cos (2 * Real.pi * z * η)) := by fun_prop
  have hgi : Integrable (fun z : ℝ => bumpF z * Real.cos (2 * Real.pi * z * η)) :=
    hcosc.integrable_of_hasCompactSupport (hcs.mul_right)
  have hint : Integrable (fun z : ℝ => (bumpF z : ℂ) * eA (-(z * η))) := by
    have hc : Continuous (fun z : ℝ => (bumpF z : ℂ) * eA (-(z * η))) := by unfold eA; fun_prop
    have hcs' : HasCompactSupport (fun z : ℝ => (bumpF z : ℂ)) := hcs.comp_left Complex.ofReal_zero
    exact hc.integrable_of_hasCompactSupport hcs'.mul_right
  have hre : (fhat bumpF η).re = ∫ z, bumpF z * Real.cos (2 * Real.pi * z * η) := by
    unfold fhat
    rw [← RCLike.re_to_complex, ← integral_re hint]
    congr 1; funext z
    rw [RCLike.re_to_complex, Complex.re_ofReal_mul, eA_re, show 2 * Real.pi * -(z * η) = -(2 * Real.pi * z * η) by ring, Real.cos_neg]
  have hlow : I / 2 ≤ (fhat bumpF η).re := by
    rw [hre, hI, ← integral_div]
    apply integral_mono (hfi.div_const 2) hgi
    intro z
    by_cases hz : bumpF z = 0
    · simp [hz]
    · have hzs := bumpF_support hz
      have hza : |z| ≤ 1 / 16 := abs_le.mpr ⟨hzs.1, hzs.2⟩
      have hx : |2 * Real.pi * z * η| ≤ 1 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos]
        have := Real.pi_lt_four
        have h1 : |z| * |η| ≤ 1 / 16 := by
          calc |z| * |η| ≤ 1 / 16 * 1 := mul_le_mul hza hη (abs_nonneg _) (by norm_num)
            _ = 1 / 16 := by ring
        nlinarith [abs_nonneg z, abs_nonneg η, mul_nonneg (abs_nonneg z) (abs_nonneg η)]
      have hcos : 1 / 2 ≤ Real.cos (2 * Real.pi * z * η) := by
        have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * z * η)
        have h2 : (2 * Real.pi * z * η) ^ 2 ≤ 1 := by
          rw [← sq_abs]; nlinarith [abs_nonneg (2 * Real.pi * z * η)]
        linarith
      have hnn := hf.nonneg z
      show bumpF z / 2 ≤ bumpF z * Real.cos (2 * Real.pi * z * η)
      nlinarith
  have hnorm : (fhat bumpF η).re ≤ ‖fhat bumpF η‖ := Complex.re_le_norm _
  have hI2 : 0 ≤ I / 2 := by positivity
  exact pow_le_pow_left₀ hI2 (hlow.trans hnorm) 2

end ShellS
end ZetaShell
