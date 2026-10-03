/-
L7_5 (28 Sep 2026), round 3: regularity and support of `A_s(y) = y^{−1/2} D_T(s − log y) Ξ((log y − s)/κ)` (eq:shell-As)
and of `V_{x,s}(y) = A_s(y) f(Δ(y−x))`, via the shared `DT_Facts` (closed form of `D_T`).
  * `As_eq_zero_of_nonpos`: `A_s(y) = 0` for `y ≤ 0` (Mathlib's `y^{−1/2}` is `0` there);
  * `As_eq_zero_outside`: `A_s(y) = 0` unless `e^{s−κ} < y < e^{s+κ}`;
  * `As_contDiff`: `A_s` is `C^∞` on `ℝ`;  `VxsW_contDiff`, `VxsW_tsupport`.
-/
import ZetaShell.PropZ.ZDefsW
import ZetaShell.PropZ.DT_Facts

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem DT_eq_DTf (T v : ℝ) : DT T v = ZetaShell.DTFacts.DTf T v := rfl

theorem As_eq_zero_of_nonpos (T κ : ℝ) (Ξ : ℝ → ℝ) (s : ℝ) {y : ℝ} (hy : y ≤ 0) : As T κ Ξ s y = 0 := by
  unfold As
  have h : y ^ (-(1 / 2 : ℝ)) = 0 := by
    rcases hy.lt_or_eq with hlt | heq
    · rw [Real.rpow_def_of_neg hlt, show -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg,
        Real.cos_pi_div_two, mul_zero]
    · rw [heq, Real.zero_rpow (by norm_num)]
  rw [h]; simp

theorem As_eq_zero_outside (T κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (s : ℝ) {y : ℝ}
    (hy : y ∉ Set.Ioo (Real.exp (s - κ)) (Real.exp (s + κ))) : As T κ Ξ s y = 0 := by
  rcases le_or_gt y 0 with h0 | h0
  · exact As_eq_zero_of_nonpos T κ Ξ s h0
  have hΞ0 : Ξ ((Real.log y - s) / κ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hΞ.supp hmem
    rw [Set.mem_Ioo, lt_div_iff₀ hκ, div_lt_iff₀ hκ] at h1
    apply hy
    constructor
    · rw [← Real.exp_log h0]; exact Real.exp_lt_exp.mpr (by linarith [h1.1])
    · rw [← Real.exp_log h0]; exact Real.exp_lt_exp.mpr (by linarith [h1.2])
  unfold As; rw [hΞ0]; simp

theorem As_contDiff (T κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (As T κ Ξ s) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases le_or_gt y 0 with h0 | h0
  · -- `A_s` vanishes on `(−∞, e^{s−κ})`, a neighbourhood of `y`
    have hev : As T κ Ξ s =ᶠ[nhds y] fun _ => (0 : ℂ) := by
      have hmem : Set.Iio (Real.exp (s - κ)) ∈ nhds y :=
        Iio_mem_nhds (lt_of_le_of_lt h0 (Real.exp_pos _))
      filter_upwards [hmem] with z hz
      exact As_eq_zero_outside T κ hκ Ξ hΞ s (fun h => absurd h.1 (not_lt.mpr (le_of_lt hz)))
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hlog : ContDiffAt ℝ (⊤ : ℕ∞) Real.log y := Real.contDiffAt_log.mpr h0.ne'
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_rpow_const_of_ne h0.ne')
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => DT T (s - Real.log y)) y :=
      (ZetaShell.DTFacts.DTf_contDiff T).contDiffAt.comp y (contDiffAt_const.sub hlog)
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => ((Ξ ((Real.log y - s) / κ) : ℝ) : ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y
        (hΞ.smooth.contDiffAt.comp y ((hlog.sub contDiffAt_const).div_const κ))
    exact (h1.mul h2).mul h3

theorem VxsW_contDiff (T κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (Δ s x : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (VxsW T κ Ξ f Δ s x) := by
  have h4 : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ((f (Δ * (y - x)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf.smooth.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))
  exact (As_contDiff T κ hκ Ξ hΞ s).mul h4

theorem VxsW_eq_zero_outside (T κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ)
    (Δ s x : ℝ) {y : ℝ} (hy : y ∉ Set.Ioo (Real.exp (s - κ)) (Real.exp (s + κ))) :
    VxsW T κ Ξ f Δ s x y = 0 := by
  unfold VxsW; rw [As_eq_zero_outside T κ hκ Ξ hΞ s hy, zero_mul]

theorem VxsW_tsupport (T κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (Δ s x : ℝ) :
    tsupport (VxsW T κ Ξ f Δ s x) ⊆ Set.Icc (Real.exp (s - κ)) (Real.exp (s + κ)) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_contra h
  exact hy (VxsW_eq_zero_outside T κ hκ Ξ hΞ f Δ s x (fun h' => h (Set.Ioo_subset_Icc_self h')))

theorem As_tsupport (T κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (s : ℝ) :
    tsupport (As T κ Ξ s) ⊆ Set.Icc (Real.exp (s - κ)) (Real.exp (s + κ)) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_contra h
  exact hy (As_eq_zero_outside T κ hκ Ξ hΞ s (fun h' => h (Set.Ioo_subset_Icc_self h')))

end ZetaShell.PropZ
