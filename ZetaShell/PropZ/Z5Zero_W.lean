/-
Node Z5Zero (L7_5, round 2): Steps 3–5 of prop:shell-Z, the zero part s-averaged, ASSEMBLED from the sub-nodes
`Z5Z_expand` (Step 3), `Z5Z_oneZero` (Step 4), `Z5Z_pair` (Step 5, from Step 4), `Z5Z_summable` (zero count).
The proof below is complete; the open leaves are the four sub-nodes.
Round 5: uses `Z5Z_expand_S4` (Step 3 with Step 4 as hypothesis) in place of `Z5Z_expand`; statement unchanged.
-/
import ZetaShell.PropZ.ZZ1_Expand
import ZetaShell.PropZ.ZZ3_Pair
import ZetaShell.PropZ.ZZ4_Count

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem Z5ZeroW (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      Summable (pairTerm χ T (Δ * Real.exp s₀) s₀ A k) ∧
      Integrable (fun s => W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))) ∧
      (∫ s, W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
        ≤ C₀ * normCA W A * T * ∑' p, pairTerm χ T (Δ * Real.exp s₀) s₀ A k p := by
  have hone := Z5Z_oneZero κ hκ hκ1 Ξ hΞ f hf A k hk
  obtain ⟨C₁, hC₁0, hC₁⟩ := Z5Z_pair κ hκ hκ1 Ξ hΞ f hf A k hA hk hone
  refine ⟨C₁, hC₁0, fun W hW s₀ T Δ hs₀ hT hΔ hΔ1 r _ χ hχ hr => ?_⟩
  have hsum := Z5Z_summable A k hk s₀ T (Δ * Real.exp s₀) (by linarith) hT (by positivity) r χ hχ
  obtain ⟨hint, _, heq⟩ := Z5Z_expand_S4 κ hκ hκ1 Ξ hΞ f hf A k hk hone W hW s₀ T Δ hs₀ hT hΔ hΔ1 r χ hχ hr
  refine ⟨hsum, hint, ?_⟩
  set F := pairInt χ T κ Ξ f W Δ s₀ with hF
  set c₀ := C₁ * normCA W A * T with hc₀
  have hb : ∀ p, ‖F p‖ ≤ c₀ * pairTerm χ T (Δ * Real.exp s₀) s₀ A k p := by
    intro p
    have h1 := p.1.2
    have h2 := p.2.2
    have hp := hC₁ W hW s₀ T Δ hs₀ hT hΔ hΔ1 p.1.1 p.2.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2
    simp only [hF, pairInt, norm_mul, Complex.norm_natCast]
    calc ((zmult χ p.1.1 * zmult χ p.2.1 : ℕ) : ℝ) *
          ‖∫ s, ((W (s - s₀) : ℝ) : ℂ) * Complex.exp (I * s * (p.1.1.im - p.2.1.im))
            * PsiP T κ Ξ f p.1.1 p.2.1 Δ s‖
        ≤ ((zmult χ p.1.1 * zmult χ p.2.1 : ℕ) : ℝ) *
          (C₁ * normCA W A * T * (Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2)
            * varpi T (Δ * Real.exp s₀) k p.1.1 * varpi T (Δ * Real.exp s₀) k p.2.1
            / (1 + |p.1.1.im - p.2.1.im|) ^ A)) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = c₀ * pairTerm χ T (Δ * Real.exp s₀) s₀ A k p := by
        simp only [hc₀, pairTerm]; push_cast; ring
  have hsum' : Summable (fun p => c₀ * pairTerm χ T (Δ * Real.exp s₀) s₀ A k p) := hsum.mul_left c₀
  have hSn : Summable (fun p => ‖F p‖) := Summable.of_nonneg_of_le (fun p => norm_nonneg _) hb hsum'
  set L := ∫ s, W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)) with hL
  calc L ≤ ‖((L : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self L
    _ = ‖∑' p, F p‖ := by rw [heq]
    _ ≤ ∑' p, ‖F p‖ := norm_tsum_le_tsum_norm hSn
    _ ≤ ∑' p, c₀ * pairTerm χ T (Δ * Real.exp s₀) s₀ A k p := hSn.tsum_le_tsum hb hsum'
    _ = c₀ * ∑' p, pairTerm χ T (Δ * Real.exp s₀) s₀ A k p := tsum_mul_left

end ZetaShell.PropZ
