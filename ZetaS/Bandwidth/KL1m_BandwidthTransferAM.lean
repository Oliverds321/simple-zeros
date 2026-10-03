/-
Node KL1m (track K, bandwidth) — KL1 for the all-marks inequality: `LocalCertAM k W → LocalCertAM (k(λ·)) W` for
0 < λ ≤ 1 (claims C(m) = Σ b_i(m_i), hence a₁, a₂, unchanged; ν unchanged, or λν in the exact form).
-/
import ZetaS.InterfacesV2

namespace ZetaS

theorem localCertAM_rescale {K : ℕ} (W : MarkWeights K) {k : ℝ → ℝ} {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) (hLI : LocalCertAM k W) : LocalCertAM (fun t => k (lam * t)) W := by
  intro m h hh
  have h1 := hLI m (fun l => lam * h l) fun l => mul_nonneg hlam0.le (hh l)
  refine h1.trans ?_
  unfold localFm
  have hspan : ∀ i s, gapSpan (fun l => lam * h l) i s = lam * gapSpan h i s := by
    intro i s; unfold gapSpan; rw [Finset.mul_sum]
  simp only [hspan]
  have : ∑ l, W.μ l * (lam * h l) ≤ ∑ l, W.μ l * h l := by
    apply Finset.sum_le_sum; intro l _
    have := mul_nonneg (W.μ_nonneg l) (hh l)
    nlinarith
  linarith

end ZetaS
