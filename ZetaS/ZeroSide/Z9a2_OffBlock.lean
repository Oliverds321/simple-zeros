/-
Sub-node Z9a2 (agent L3_1) — inertia of the off-line block (draft l.198–203, AF2): for pair representatives
A (β > ½) with weights c_ρ = 2m_ρ > 0 and real/imaginary parts x_ρ, y_ρ of u_ρ,
  Qoff = Σ_{ρ∈A} c_ρ (x_ρx_ρᵀ − y_ρy_ρᵀ)  has  n₊(Qoff), n₋(Qoff) ≤ #A = p.
Each term is x′x′ᵀ − y′y′ᵀ with x′ = √c x, y′ = √c y (Z7, L3_2), then subadditivity (trunk `posIndex_add_le`,
L8 `negIndex_add_le`).
-/
import ZetaS.ZeroSide.Z7_PairBlockInertia
import ZetaS.LinAlg.L8_NegIndexAdd
import Zeta23.ZeroSide

noncomputable section

open RHLinalg Matrix

namespace ZetaS
namespace Z9

/-- the off-line block. -/
def offBlock {d : ℕ} (A : Finset ℂ) (c : ℂ → ℝ) (x y : ℂ → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ ρ ∈ A, c ρ • (vecMulVec (x ρ) (x ρ) - vecMulVec (y ρ) (y ρ))

lemma term_eq {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (x y : Fin d → ℝ) :
    c • (vecMulVec x x - vecMulVec y y)
      = vecMulVec (Real.sqrt c • x) (Real.sqrt c • x) - vecMulVec (Real.sqrt c • y) (Real.sqrt c • y) := by
  have hs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
  conv_lhs => rw [← hs]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma term_herm {d : ℕ} (x y : Fin d → ℝ) : (vecMulVec x x - vecMulVec y y).IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  simp [vecMulVec_apply, mul_comm]

lemma offBlock_herm {d : ℕ} (A : Finset ℂ) (c : ℂ → ℝ) (x y : ℂ → Fin d → ℝ) :
    (offBlock A c x y).IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  simp [offBlock, Matrix.sum_apply, vecMulVec_apply, mul_comm]

lemma idx_congr {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : posIndex hA = posIndex hB ∧ negIndex hA = negIndex hB := by
  subst h; exact ⟨rfl, rfl⟩

lemma zero_index {d : ℕ} (h : (0 : Matrix (Fin d) (Fin d) ℝ).IsHermitian) :
    posIndex h = 0 ∧ negIndex h = 0 := by
  constructor
  · exact Nat.le_zero.mp ((Zeta23.ZeroSide.posIndex_le_rank h).trans (Matrix.rank_zero).le)
  · rw [negIndex_eq_posIndex_neg]
    have hr : (-(0 : Matrix (Fin d) (Fin d) ℝ)).rank = 0 := by rw [neg_zero, Matrix.rank_zero]
    exact Nat.le_zero.mp ((Zeta23.ZeroSide.posIndex_le_rank _).trans hr.le)

/-- **Z9a2**: `n₊(Qoff), n₋(Qoff) ≤ #A`. -/
theorem offBlock_inertia {d : ℕ} (A : Finset ℂ) (c : ℂ → ℝ) (hc : ∀ ρ ∈ A, 0 ≤ c ρ) (x y : ℂ → Fin d → ℝ) :
    posIndex (offBlock_herm A c x y) ≤ A.card ∧ negIndex (offBlock_herm A c x y) ≤ A.card := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have h0 : offBlock (∅ : Finset ℂ) c x y = 0 := by simp [offBlock]
    have := zero_index (h0 ▸ offBlock_herm ∅ c x y)
    rw [Finset.card_empty]
    constructor
    · rw [(idx_congr h0 (offBlock_herm ∅ c x y) (h0 ▸ offBlock_herm ∅ c x y)).1]; omega
    · rw [(idx_congr h0 (offBlock_herm ∅ c x y) (h0 ▸ offBlock_herm ∅ c x y)).2]; omega
  | insert ρ A hρ ih =>
    have hcA : ∀ σ ∈ A, 0 ≤ c σ := fun σ hσ => hc σ (Finset.mem_insert_of_mem hσ)
    obtain ⟨ih1, ih2⟩ := ih hcA
    have hsplit : offBlock (insert ρ A) c x y
        = c ρ • (vecMulVec (x ρ) (x ρ) - vecMulVec (y ρ) (y ρ)) + offBlock A c x y := by
      simp [offBlock, Finset.sum_insert hρ]
    have ht := term_herm (Real.sqrt (c ρ) • x ρ) (Real.sqrt (c ρ) • y ρ)
    have hte : c ρ • (vecMulVec (x ρ) (x ρ) - vecMulVec (y ρ) (y ρ))
        = vecMulVec (Real.sqrt (c ρ) • x ρ) (Real.sqrt (c ρ) • x ρ)
          - vecMulVec (Real.sqrt (c ρ) • y ρ) (Real.sqrt (c ρ) • y ρ) :=
      term_eq (hc ρ (Finset.mem_insert_self ρ A)) (x ρ) (y ρ)
    obtain ⟨p1, n1⟩ := pairBlock_inertia (Real.sqrt (c ρ) • x ρ) (Real.sqrt (c ρ) • y ρ) ht
    have hsum : offBlock (insert ρ A) c x y
        = (vecMulVec (Real.sqrt (c ρ) • x ρ) (Real.sqrt (c ρ) • x ρ)
          - vecMulVec (Real.sqrt (c ρ) • y ρ) (Real.sqrt (c ρ) • y ρ)) + offBlock A c x y := by
      rw [hsplit, hte]
    have hH := ht.add (offBlock_herm A c x y)
    rw [Finset.card_insert_of_notMem hρ]
    constructor
    · rw [(idx_congr hsum (offBlock_herm _ c x y) hH).1]
      have := posIndex_add_le ht (offBlock_herm A c x y)
      omega
    · rw [(idx_congr hsum (offBlock_herm _ c x y) hH).2]
      have := negIndex_add_le ht (offBlock_herm A c x y)
      omega

end Z9
end ZetaS
