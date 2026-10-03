/-
A2a_S3a_Reindex (L7_8, round 3): **re-indexing of the window sum by lines** (Steps 0–1, sec_shell.tex l.306–320).
Tested numerically (`numerics/step3_split_test.py`). Round 4: PROVED from `s3_window_lines_pf` (the core
bijection, A2a_S3a_WindowProof) and `line_collapse` (Step 1, A2a_S3a_Collapse, proved).
With `ar′ − a′r = 1`, the Farey points `b/q` (`q ≤ Q`) of the window `[a/r + η − δ/2, a/r + η + δ/2]` other than `a/r`
are the `q = rk − r′j`, `(k, j)` primitive, `j ≠ 0`, `q ∈ I_j = lineIv` (Step 0, `line_inverse`, `line_gcd`,
`line_offset`, `line_j_bound`); their weights expand as `Ω(q) = Σ_e c_e w(qe/Q) Σ_{f|q} λ_e(f)` (Step 1,
`omegaW_step1`). `δ < 1` makes the representative of each point in the window unique; `r ≤ Q` makes `a/r` a point.
-/
import ZetaShell.Lemma2.A2a_S3_Defs
import ZetaShell.Skeleton.A2a_S3a_Window
import ZetaShell.Lemma2.A2a_S3a_WindowProof

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem s3_reindex (F : Fam) (Q r : ℕ) (a a' r' : ℤ) (η δ : ℝ) (hQ : 2 ≤ Q) (hr : 1 ≤ r) (hrQ : r ≤ Q)
    (hdet : a * r' - a' * (r : ℤ) = 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    δ * Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) δ ((a : ℝ) / r + η)
      = spike F Q r η δ + ∑ j ∈ lineSet (lineM Q r η δ), ∑ e ∈ Finset.Icc 1 Q, cE F.kind e *
          ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f *
            lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2 := by
  have hwin : δ * Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) δ ((a : ℝ) / r + η)
      = ∑ x ∈ fareyWin Q ((a : ℝ) / r + η) δ, fareyWeight F Q x := by
    rw [Ddens_eq_win, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
  rw [hwin, s3_window_lines_pf F Q r a a' r' η δ hQ hr hrQ hdet hδ hδ1]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [line_collapse F Q (r : ℤ) r' j (lineIv Q r j η δ).1 (lineIv Q r j η δ).2 (lineK_bounds Q r hr r' j η δ)]

end TrackF
end ZetaShell
