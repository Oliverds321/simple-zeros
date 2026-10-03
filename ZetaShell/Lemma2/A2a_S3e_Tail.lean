/-
A2a_S3e_Tail (L7_8, round 3): **the tail `f > Q` of the main term** (Step 3, sec_shell.tex l.338, with L7_8's bound).
`Σ_{sqfree f} λ_e(f)∏_{p|f}δ_p = ∏_p(1 + λ_e(p)δ_p) = 𝔈_{j,r}(e)` (Euler product; for the `q/φ` kind `λ_e` lives on
`f | e ≤ Q` and the tail is `0`); the tail `Σ_{f>Q}|λ_e(f)|∏δ_p ≤ 2^{ω(e)+1}σ(rad(r,j))/Q`, and
`Σ_{j≤J} jσ(rad(r,j)) ≤ J²Σ_{d|r}σ(d)/d` give `≪ δQτ(r) log log r ≤ δQr`.
Round 5: proved from the three nodes of `A2a_S3e_TailParts` (`s3_tail_qphi_pt`, `s3_tail_plain_pt`, `s3_tail_sum`).
-/
import ZetaShell.Lemma2.A2a_S3_Defs
import ZetaShell.Skeleton.A2a_S3e_TailParts

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem s3_tail (F : Fam) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q r : ℕ) (R1 η δ : ℝ), 2 ≤ Q → 1 ≤ r → (r : ℝ) ≤ R1 →
    2 * R1 ≤ Q → |η| ≤ 1 / (r * R1) → 0 < δ → δ < 1 →
    ∑ j ∈ lineSet (lineM Q r η δ), ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
      ∑ e ∈ Finset.Icc 1 Q, |cE F.kind e| *
        |∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)| *
        |∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * deltaProd r j f - Ecoef F.kind r j.natAbs e|
      ≤ C * (δ * Q * r * (1 + Real.log Q)) := by
  cases hk : F.kind with
  | plain =>
    obtain ⟨C, hC, h⟩ := s3_tail_sum F hk
    refine ⟨C, hC, ?_⟩
    intro Q r R1 η δ hQ hr hrR hRQ hη hδ hδ1
    refine le_trans ?_ (h Q r R1 η δ hQ hr hrR hRQ hη hδ hδ1)
    apply Finset.sum_le_sum
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact s3_tail_plain_pt Q r j e (by omega) hr hj0 he1
  | qphi =>
    refine ⟨0, le_rfl, ?_⟩
    intro Q r R1 η δ hQ hr hrR hRQ hη hδ hδ1
    rw [zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2
    rw [Finset.sum_eq_zero, mul_zero]
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heQ : e ≤ Q := (Finset.mem_Icc.mp he).2
    rw [s3_tail_qphi_pt Q r j e hr hj0 he1 heQ, sub_self, abs_zero, mul_zero]

end TrackF
end ZetaShell
