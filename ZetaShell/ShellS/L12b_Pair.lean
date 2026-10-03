/-
L7_12c (3 Oct 2026): the per-character pair bound of Lemma 6a (lem:shell-6a), abstract finite form.
For a finite family with weights `m ≥ 0`, split `b = b^N + b^R` (near / rest), a symmetric kernel `0 ≤ K ≤ 1`
with the two Schur bounds `Σ_ρ' m' K(ρ,ρ') ≤ cS ℓ(ρ)` and `Σ_ρ' m' K(ρ,ρ')/ℓ(ρ') ≤ cU` (`ℓ > 0`):
`Σ_{ρ,ρ'} m m' b b' K ≤ (1 + cU)(Σ m b^N)² + (1 + cS) Σ m (b^R)² ℓ`.
Proof: expand `b b'` in four terms; near-near `≤ 𝒩²` (`K ≤ 1`); the two cross terms equal `2Σ_ρ m b^R G(ρ)` with
`G(ρ) = Σ_ρ' m' b'^N K(ρ,ρ') ≤ 𝒩`, and `2 b^R G ≤ (b^R)² ℓ + G²/ℓ ≤ (b^R)² ℓ + 𝒩 G/ℓ`, `Σ_ρ m G/ℓ ≤ cU 𝒩`
(Tonelli on finite sums); rest-rest `≤ Σ m (b^R)² Σ' m' K ≤ cS Σ m (b^R)² ℓ` (`2xy ≤ x² + y²`, symmetry).
Mathlib only.
-/
import Mathlib

noncomputable section

namespace ZetaShell
namespace ShellS

open Finset

theorem L12b_pair {ι : Type*} (s : Finset ι) (m bN bR ℓ : ι → ℝ) (K : ι → ι → ℝ) (cS cU : ℝ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hbN : ∀ ρ ∈ s, 0 ≤ bN ρ) (hbR : ∀ ρ ∈ s, 0 ≤ bR ρ)
    (hℓ : ∀ ρ ∈ s, 0 < ℓ ρ)
    (hK0 : ∀ ρ ∈ s, ∀ ρ' ∈ s, 0 ≤ K ρ ρ') (hK1 : ∀ ρ ∈ s, ∀ ρ' ∈ s, K ρ ρ' ≤ 1)
    (hKs : ∀ ρ ρ', K ρ ρ' = K ρ' ρ)
    (hS : ∀ ρ ∈ s, ∑ ρ' ∈ s, m ρ' * K ρ ρ' ≤ cS * ℓ ρ)
    (hU : ∀ ρ ∈ s, ∑ ρ' ∈ s, m ρ' * K ρ ρ' / ℓ ρ' ≤ cU) :
    ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * m ρ' * (bN ρ + bR ρ) * (bN ρ' + bR ρ') * K ρ ρ'
      ≤ (1 + cU) * (∑ ρ ∈ s, m ρ * bN ρ) ^ 2 + (1 + cS) * ∑ ρ ∈ s, m ρ * bR ρ ^ 2 * ℓ ρ := by
  set N := ∑ ρ ∈ s, m ρ * bN ρ with hN
  set G : ι → ℝ := fun ρ => ∑ ρ' ∈ s, m ρ' * bN ρ' * K ρ ρ' with hG
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun ρ hρ => mul_nonneg (hm ρ hρ) (hbN ρ hρ)
  have hG0 : ∀ ρ ∈ s, 0 ≤ G ρ := fun ρ hρ => Finset.sum_nonneg fun ρ' hρ' =>
    mul_nonneg (mul_nonneg (hm ρ' hρ') (hbN ρ' hρ')) (hK0 ρ hρ ρ' hρ')
  have hG1 : ∀ ρ ∈ s, G ρ ≤ N := fun ρ hρ => Finset.sum_le_sum fun ρ' hρ' => by
    have h1 := hK1 ρ hρ ρ' hρ'
    have h2 := mul_nonneg (hm ρ' hρ') (hbN ρ' hρ')
    nlinarith
  -- the four terms
  have hexp : ∀ ρ ρ', m ρ * m ρ' * (bN ρ + bR ρ) * (bN ρ' + bR ρ') * K ρ ρ'
      = m ρ * m ρ' * bN ρ * bN ρ' * K ρ ρ' + m ρ * bR ρ * (m ρ' * bN ρ' * K ρ ρ')
        + m ρ' * bR ρ' * (m ρ * bN ρ * K ρ' ρ) + m ρ * m ρ' * bR ρ * bR ρ' * K ρ ρ' := by
    intro ρ ρ'; rw [hKs ρ' ρ]; ring
  have hsplit : ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * m ρ' * (bN ρ + bR ρ) * (bN ρ' + bR ρ') * K ρ ρ'
      = ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * m ρ' * bN ρ * bN ρ' * K ρ ρ'
        + ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * bR ρ * (m ρ' * bN ρ' * K ρ ρ')
        + ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ' * bR ρ' * (m ρ * bN ρ * K ρ' ρ)
        + ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * m ρ' * bR ρ * bR ρ' * K ρ ρ' := by
    simp only [hexp, Finset.sum_add_distrib]
  rw [hsplit]
  -- T1
  have hT1 : ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * m ρ' * bN ρ * bN ρ' * K ρ ρ' ≤ N ^ 2 := by
    calc ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * m ρ' * bN ρ * bN ρ' * K ρ ρ'
        ≤ ∑ ρ ∈ s, ∑ ρ' ∈ s, (m ρ * bN ρ) * (m ρ' * bN ρ') := by
          apply Finset.sum_le_sum; intro ρ hρ; apply Finset.sum_le_sum; intro ρ' hρ'
          have h1 := hK1 ρ hρ ρ' hρ'
          have h2 := mul_nonneg (mul_nonneg (hm ρ hρ) (hbN ρ hρ)) (mul_nonneg (hm ρ' hρ') (hbN ρ' hρ'))
          nlinarith
      _ = N ^ 2 := by rw [sq, hN, Finset.sum_mul_sum]
  -- T2 = T3 = Σ m bR G
  have hT2 : ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * bR ρ * (m ρ' * bN ρ' * K ρ ρ') = ∑ ρ ∈ s, m ρ * bR ρ * G ρ := by
    apply Finset.sum_congr rfl; intro ρ _; rw [hG, Finset.mul_sum]
  have hT3 : ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ' * bR ρ' * (m ρ * bN ρ * K ρ' ρ) = ∑ ρ ∈ s, m ρ * bR ρ * G ρ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ρ _; rw [hG, Finset.mul_sum]
  -- the cross bound
  have hGU : ∑ ρ ∈ s, m ρ * G ρ / ℓ ρ ≤ cU * N := by
    have e1 : ∑ ρ ∈ s, m ρ * G ρ / ℓ ρ = ∑ ρ' ∈ s, (m ρ' * bN ρ') * ∑ ρ ∈ s, m ρ * K ρ' ρ / ℓ ρ := by
      have e2 : ∀ ρ ∈ s, m ρ * G ρ / ℓ ρ = ∑ ρ' ∈ s, (m ρ' * bN ρ') * (m ρ * K ρ' ρ / ℓ ρ) := by
        intro ρ _
        rw [hG, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl; intro ρ' _; rw [hKs ρ ρ']; ring
      rw [Finset.sum_congr rfl e2, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro ρ' _; rw [Finset.mul_sum]
    rw [e1]
    calc ∑ ρ' ∈ s, (m ρ' * bN ρ') * ∑ ρ ∈ s, m ρ * K ρ' ρ / ℓ ρ ≤ ∑ ρ' ∈ s, (m ρ' * bN ρ') * cU :=
          Finset.sum_le_sum fun ρ' hρ' =>
            mul_le_mul_of_nonneg_left (hU ρ' hρ') (mul_nonneg (hm ρ' hρ') (hbN ρ' hρ'))
      _ = cU * N := by rw [hN, ← Finset.sum_mul, mul_comm]
  have hcross : 2 * ∑ ρ ∈ s, m ρ * bR ρ * G ρ ≤ ∑ ρ ∈ s, m ρ * bR ρ ^ 2 * ℓ ρ + cU * N ^ 2 := by
    have hpt : ∀ ρ ∈ s, 2 * (m ρ * bR ρ * G ρ) ≤ m ρ * bR ρ ^ 2 * ℓ ρ + N * (m ρ * G ρ / ℓ ρ) := by
      intro ρ hρ
      have hl := hℓ ρ hρ
      have hmρ := hm ρ hρ
      have hG0ρ := hG0 ρ hρ
      have hGN := hG1 ρ hρ
      have hamgm : 2 * (bR ρ * G ρ) ≤ bR ρ ^ 2 * ℓ ρ + G ρ ^ 2 / ℓ ρ := by
        rw [← sub_nonneg]
        have : bR ρ ^ 2 * ℓ ρ + G ρ ^ 2 / ℓ ρ - 2 * (bR ρ * G ρ) = (bR ρ * ℓ ρ - G ρ) ^ 2 / ℓ ρ := by
          field_simp; ring
        rw [this]; positivity
      have hGG : G ρ ^ 2 / ℓ ρ ≤ N * (G ρ / ℓ ρ) := by
        rw [sq, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hGN (div_nonneg hG0ρ hl.le)
      calc 2 * (m ρ * bR ρ * G ρ) = m ρ * (2 * (bR ρ * G ρ)) := by ring
        _ ≤ m ρ * (bR ρ ^ 2 * ℓ ρ + N * (G ρ / ℓ ρ)) :=
            mul_le_mul_of_nonneg_left (hamgm.trans (by linarith)) hmρ
        _ = m ρ * bR ρ ^ 2 * ℓ ρ + N * (m ρ * G ρ / ℓ ρ) := by ring
    calc 2 * ∑ ρ ∈ s, m ρ * bR ρ * G ρ = ∑ ρ ∈ s, 2 * (m ρ * bR ρ * G ρ) := by rw [Finset.mul_sum]
      _ ≤ ∑ ρ ∈ s, (m ρ * bR ρ ^ 2 * ℓ ρ + N * (m ρ * G ρ / ℓ ρ)) := Finset.sum_le_sum hpt
      _ = ∑ ρ ∈ s, m ρ * bR ρ ^ 2 * ℓ ρ + N * ∑ ρ ∈ s, m ρ * G ρ / ℓ ρ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ ρ ∈ s, m ρ * bR ρ ^ 2 * ℓ ρ + N * (cU * N) := by
          have := mul_le_mul_of_nonneg_left hGU hN0; linarith
      _ = ∑ ρ ∈ s, m ρ * bR ρ ^ 2 * ℓ ρ + cU * N ^ 2 := by ring
  -- T4
  have hT4 : ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * m ρ' * bR ρ * bR ρ' * K ρ ρ' ≤ cS * ∑ ρ ∈ s, m ρ * bR ρ ^ 2 * ℓ ρ := by
    have hpt : ∀ ρ ∈ s, ∀ ρ' ∈ s, m ρ * m ρ' * bR ρ * bR ρ' * K ρ ρ'
        ≤ (m ρ * bR ρ ^ 2) * (m ρ' * K ρ ρ') / 2 + (m ρ' * bR ρ' ^ 2) * (m ρ * K ρ' ρ) / 2 := by
      intro ρ hρ ρ' hρ'
      rw [hKs ρ' ρ]
      have h0 := mul_nonneg (mul_nonneg (hm ρ hρ) (hm ρ' hρ')) (hK0 ρ hρ ρ' hρ')
      have h1 : 2 * (bR ρ * bR ρ') ≤ bR ρ ^ 2 + bR ρ' ^ 2 := by nlinarith [sq_nonneg (bR ρ - bR ρ')]
      have h2 := mul_le_mul_of_nonneg_left h1 h0
      nlinarith
    have hsym : ∑ ρ ∈ s, ∑ ρ' ∈ s, (m ρ' * bR ρ' ^ 2) * (m ρ * K ρ' ρ) / 2
        = ∑ ρ ∈ s, ∑ ρ' ∈ s, (m ρ * bR ρ ^ 2) * (m ρ' * K ρ ρ') / 2 := Finset.sum_comm
    calc ∑ ρ ∈ s, ∑ ρ' ∈ s, m ρ * m ρ' * bR ρ * bR ρ' * K ρ ρ'
        ≤ ∑ ρ ∈ s, ∑ ρ' ∈ s, ((m ρ * bR ρ ^ 2) * (m ρ' * K ρ ρ') / 2
            + (m ρ' * bR ρ' ^ 2) * (m ρ * K ρ' ρ) / 2) :=
          Finset.sum_le_sum fun ρ hρ => Finset.sum_le_sum fun ρ' hρ' => hpt ρ hρ ρ' hρ'
      _ = ∑ ρ ∈ s, ∑ ρ' ∈ s, (m ρ * bR ρ ^ 2) * (m ρ' * K ρ ρ') / 2
            + ∑ ρ ∈ s, ∑ ρ' ∈ s, (m ρ' * bR ρ' ^ 2) * (m ρ * K ρ' ρ) / 2 := by
          simp only [Finset.sum_add_distrib]
      _ = ∑ ρ ∈ s, (m ρ * bR ρ ^ 2) * ∑ ρ' ∈ s, m ρ' * K ρ ρ' := by
          rw [hsym, ← two_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro ρ _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro ρ' _; ring
      _ ≤ ∑ ρ ∈ s, (m ρ * bR ρ ^ 2) * (cS * ℓ ρ) :=
          Finset.sum_le_sum fun ρ hρ =>
            mul_le_mul_of_nonneg_left (hS ρ hρ) (mul_nonneg (hm ρ hρ) (sq_nonneg _))
      _ = cS * ∑ ρ ∈ s, m ρ * bR ρ ^ 2 * ℓ ρ := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ρ _; ring
  rw [hT2, hT3]
  have hR0 : 0 ≤ ∑ ρ ∈ s, m ρ * bR ρ ^ 2 * ℓ ρ :=
    Finset.sum_nonneg fun ρ hρ => mul_nonneg (mul_nonneg (hm ρ hρ) (sq_nonneg _)) (hℓ ρ hρ).le
  nlinarith [hT1, hcross, hT4]

end ShellS
end ZetaShell
