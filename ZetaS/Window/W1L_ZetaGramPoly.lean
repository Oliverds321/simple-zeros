/-
Node W1L (track W; replaces v1's W1 for the S route) — ζ at bandwidth λ ∈ (0,1), polynomial window: a GramFamilyL with
R = R_λ(ψ̃), s₁ ≤ N₀ˢ(T,2T) + o(N). From W2L-poly by K0 (frame → GramData).
-/
import ZetaS.InterfacesV2
import ZetaS.Window.W2L_ZetaFramePoly_fix
import ZetaS.KSide.K0_FrameToGramHEq

open Filter Asymptotics

namespace ZetaS

/-- Traces and Frobenius norms agree across a heterogeneous equality of square matrices (for K0's `HEq`). -/
theorem W1L_heq_traces {d d' : ℕ} (h : d = d') {A : Matrix (Fin d) (Fin d) ℝ} {B : Matrix (Fin d') (Fin d') ℝ}
    (hAB : HEq A B) : RHLinalg.rtrace A = RHLinalg.rtrace B ∧ RHLinalg.frobSq A = RHLinalg.frobSq B := by
  subst h; rw [eq_of_heq hAB]; exact ⟨rfl, rfl⟩

/-- `0 ≤ tr Etr(D) ≤ tr Etr(F) = Σ δ ≤ Σ m δ`. -/
theorem W1L_trunc_le (F : ZeroFrame) (D : GramData) (h : RHLinalg.rtrace D.Etr ≤ RHLinalg.rtrace F.Etr) :
    |RHLinalg.rtrace D.Etr| ≤ ∑ i, (F.m i : ℝ) * F.delta i := by
  have hre : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), RHLinalg.rtrace A = ∑ i, A i i := by
    intro n A; simp [RHLinalg.rtrace, Matrix.trace]
  have h0 : 0 ≤ RHLinalg.rtrace D.Etr := by rw [hre]; exact Finset.sum_nonneg fun i _ => D.Etr_psd.diag_nonneg
  rw [abs_of_nonneg h0]
  refine h.trans ?_
  rw [hre]
  refine Finset.sum_le_sum fun i _ => ?_
  have hδ : 0 ≤ F.Etr i i := F.Etr_psd.diag_nonneg
  have hm : (1 : ℝ) ≤ F.m i := by exact_mod_cast F.one_le_m i
  show F.Etr i i ≤ (F.m i : ℝ) * F.Etr i i
  nlinarith

theorem zeta_gramFamily_poly {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    ∃ Fm : GramFamilyL lam (fun T => (Ncount T (2 * T) : ℝ)) (Rlam lam psiPoly8A) (kPsi psiPoly8A),
      ∃ r : ℝ → ℝ, r =o[atTop] (fun T => (Ncount T (2 * T) : ℝ)) ∧ ∀ᶠ T in atTop,
        ((Fm.G T).s1 : ℝ) ≤ N0simple T (2 * T) + r T := by
  obtain ⟨Fm, r, hr, hev⟩ := zeta_frameFamily_poly_fix hl0 hl1
  choose D hD using fun T => frame_to_gram_heq (Fm.F T)
  have hgt := fun T => W1L_heq_traces (hD T).1 (hD T).2.1
  refine ⟨{ G := D
            N_nonneg := Fm.N_nonneg
            N_tendsto := Fm.N_tendsto
            trace := Fm.trace.congr' (Eventually.of_forall fun T => by simp only [(hgt T).1])
              EventuallyEq.rfl
            frob := Fm.frob.congr' (Eventually.of_forall fun T => by simp only [(hgt T).2])
              EventuallyEq.rfl
            window := Fm.window.congr' (Eventually.of_forall fun T => by simp only [(hD T).2.2.1])
              EventuallyEq.rfl
            span := by
              obtain ⟨r', hr', h'⟩ := Fm.span
              exact ⟨r', hr', h'.mono fun T h => by rw [(hD T).2.2.2.2.2.1]; exact h⟩
            trunc := by
              refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun T => ?_)) Fm.defect
              rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
              exact (W1L_trunc_le _ _ (hD T).2.2.2.2.2.2).trans (le_abs_self _)
            kernel := by
              obtain ⟨e, he, h'⟩ := Fm.kernel
              exact ⟨e, he, h'.mono fun T h t => by rw [(hD T).2.2.2.2.1]; exact h t⟩
            lam_pos := Fm.lam_pos
            lam_le_one := Fm.lam_le_one
            span_lam := by
              obtain ⟨r', hr', h'⟩ := Fm.span_lam
              exact ⟨r', hr', h'.mono fun T h => by rw [(hD T).2.2.2.2.2.1]; exact h⟩ }, r, hr, ?_⟩
  filter_upwards [hev] with T h
  show ((D T).s1 : ℝ) ≤ _
  rw [(hD T).2.2.2.1]
  exact h.2.2.2

end ZetaS
