/-
Node A5 (track P/K, all-marks) — lem:sigd-env (l.1274–1297) in quadratic-form shape: if `MajorantCert ψ β`, the
true kernel is dominated, `(1 + e)k_ψ − k` positive definite (FrameFamily.dominate), and sites x have consecutive
gaps ≥ 3/4 with marks m ∈ {1, 2}, then for all y:
"Σ_{a,b} y_a y_b √(m_a m_b) k(x_a − x_b) ≤ (1 + e) β Σ y_a²" (i.e. λ_max(M_𝓡) ≤ (1 + e)β; Ê ⪰ 0 is dropped separately).
Proof: domination, then B ≥ v_ψ ⇒ B̂ − k_ψ positive definite (node M1), then Gershgorin with supp B̂ ⊂ [−1,1].

Proof (L2_2): z_a := y_a√m_a. Domination (hdom) gives Σ z z k ≤ (1+e) Σ z z k_ψ; M1 (`majorant_kernel_gen`) gives
Σ z z k_ψ ≤ Σ z z B̂; Gershgorin: each site has at most one separated neighbour on each side within distance < 1
(two on one side would be ≥ 3/2 away), B̂ = 0 beyond, |B̂| ≤ β* on [3/4, 1], so Σ z z B̂ ≤ (B̂(0) + 2β*) Σ z²,
and Σ z² ≤ 2 Σ y².
-/
import ZetaS.Interfaces
import ZetaS.SigmaDist.M1_MajorantKernel

open Finset

namespace ZetaS

namespace A5aux

/-- at most one close separated neighbour on the right. -/
lemma right_le_one {n : ℕ} (x : Fin n → ℝ) (hsep : ∀ i j : Fin n, i < j → x i + 3 / 4 ≤ x j) (a : Fin n) :
    #(univ.filter fun b => a < b ∧ |x a - x b| < 1) ≤ 1 := by
  rw [Finset.card_le_one]
  intro b1 hb1 b2 hb2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb1 hb2
  have h1 := hsep a b1 hb1.1
  have h2 := hsep a b2 hb2.1
  have c1 := (abs_lt.1 hb1.2).1
  have c2 := (abs_lt.1 hb2.2).1
  rcases lt_trichotomy b1 b2 with h | h | h
  · have := hsep b1 b2 h; linarith
  · exact h
  · have := hsep b2 b1 h; linarith

/-- at most one close separated neighbour on the left. -/
lemma left_le_one {n : ℕ} (x : Fin n → ℝ) (hsep : ∀ i j : Fin n, i < j → x i + 3 / 4 ≤ x j) (a : Fin n) :
    #(univ.filter fun b => b < a ∧ |x a - x b| < 1) ≤ 1 := by
  rw [Finset.card_le_one]
  intro b1 hb1 b2 hb2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb1 hb2
  have h1 := hsep b1 a hb1.1
  have h2 := hsep b2 a hb2.1
  have c1 := (abs_lt.1 hb1.2).2
  have c2 := (abs_lt.1 hb2.2).2
  rcases lt_trichotomy b1 b2 with h | h | h
  · have := hsep b1 b2 h; linarith
  · exact h
  · have := hsep b2 b1 h; linarith

lemma close_le_two {n : ℕ} (x : Fin n → ℝ) (hsep : ∀ i j : Fin n, i < j → x i + 3 / 4 ≤ x j) (a : Fin n) :
    #(univ.filter fun b => b ≠ a ∧ |x a - x b| < 1) ≤ 2 := by
  have hsub : univ.filter (fun b => b ≠ a ∧ |x a - x b| < 1)
      ⊆ univ.filter (fun b => b < a ∧ |x a - x b| < 1) ∪ univ.filter (fun b => a < b ∧ |x a - x b| < 1) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hb ⊢
    rcases lt_or_gt_of_ne hb.1 with h | h
    · exact Or.inl ⟨h, hb.2⟩
    · exact Or.inr ⟨h, hb.2⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 1 + 1 := add_le_add (left_le_one x hsep a) (right_le_one x hsep a)

lemma quad_of_posDef {f : ℝ → ℝ} (hf : IsPosDefKernel f) {n : ℕ} (x z : Fin n → ℝ) :
    0 ≤ ∑ a, ∑ b, z a * z b * f (x a - x b) := by
  have := (hf n x).dotProduct_mulVec_nonneg z
  rwa [M1aux.quad_kerMat] at this

end A5aux

open A5aux

theorem separated_room {ψ : ℝ → ℝ} {β e : ℝ} (hmaj : MajorantCert ψ β) (he : 0 ≤ e)
    {k : ℝ → ℝ} (hdom : IsPosDefKernel (fun t => (1 + e) * kPsi ψ t - k t))
    {n : ℕ} (x : Fin n → ℝ) (hsep : ∀ i j : Fin n, i < j → x i + 3 / 4 ≤ x j)
    (m : Fin n → ℕ) (hm : ∀ i, m i = 1 ∨ m i = 2) (y : Fin n → ℝ) :
    ∑ a, ∑ b, y a * y b * Real.sqrt ((m a : ℝ) * m b) * k (x a - x b)
      ≤ (1 + e) * β * ∑ a, y a ^ 2 := by
  obtain ⟨Bh, hPD, hBh_even, hBh_supp, hBh0, βstar, hβ1, hβ2⟩ := majorant_kernel_gen hmaj
  have hβs : 0 ≤ βstar := le_trans (abs_nonneg _) (hβ1 (3 / 4) ⟨le_rfl, by norm_num⟩)
  set z : Fin n → ℝ := fun a => y a * Real.sqrt (m a) with hz
  have hmv : ∀ a, (m a : ℝ) ≤ 2 ∧ 0 ≤ (m a : ℝ) := by
    intro a; rcases hm a with h | h <;> simp [h]
  have hLHS : ∑ a, ∑ b, y a * y b * Real.sqrt ((m a : ℝ) * m b) * k (x a - x b)
      = ∑ a, ∑ b, z a * z b * k (x a - x b) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hz]; rw [Real.sqrt_mul (hmv a).2]; ring
  -- domination
  have s1 : ∑ a, ∑ b, z a * z b * k (x a - x b) ≤ (1 + e) * ∑ a, ∑ b, z a * z b * kPsi ψ (x a - x b) := by
    have h := quad_of_posDef hdom x z
    have : ∑ a, ∑ b, z a * z b * ((1 + e) * kPsi ψ (x a - x b) - k (x a - x b))
        = (1 + e) * ∑ a, ∑ b, z a * z b * kPsi ψ (x a - x b) - ∑ a, ∑ b, z a * z b * k (x a - x b) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    linarith
  -- majorant
  have s2 : ∑ a, ∑ b, z a * z b * kPsi ψ (x a - x b) ≤ ∑ a, ∑ b, z a * z b * Bh (x a - x b) := by
    have h := quad_of_posDef hPD x z
    have : ∑ a, ∑ b, z a * z b * (Bh (x a - x b) - kPsi ψ (x a - x b))
        = ∑ a, ∑ b, z a * z b * Bh (x a - x b) - ∑ a, ∑ b, z a * z b * kPsi ψ (x a - x b) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    linarith
  -- Gershgorin
  let P : Fin n → Fin n → Prop := fun a b => b ≠ a ∧ |x a - x b| < 1
  have hPsymm : ∀ a b, P a b ↔ P b a := by
    intro a b; simp only [P]; rw [abs_sub_comm]
    exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
  have hterm : ∀ a b, z a * z b * Bh (x a - x b)
      ≤ (if a = b then z a ^ 2 * Bh 0 else 0)
        + (if P a b then βstar * (z a ^ 2 + z b ^ 2) / 2 else 0) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have : ¬ P a a := fun h => h.1 rfl
      rw [if_pos rfl, if_neg this, sub_self]
      nlinarith
    · rw [if_neg hab]
      have hsepab : 3 / 4 ≤ |x a - x b| := by
        rcases lt_or_gt_of_ne hab with h | h
        · have := hsep a b h; rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
        · have := hsep b a h; rw [abs_of_nonneg (by linarith)]; linarith
      by_cases hc : |x a - x b| < 1
      · have hP : P a b := ⟨Ne.symm hab, hc⟩
        rw [if_pos hP]
        have hB : |Bh (x a - x b)| ≤ βstar := by
          rcases le_or_gt 0 (x a - x b) with h | h
          · rw [abs_of_nonneg h] at hsepab hc
            exact hβ1 _ ⟨hsepab, hc.le⟩
          · rw [abs_of_neg h] at hsepab hc
            rw [← hBh_even]
            exact hβ1 _ ⟨hsepab, hc.le⟩
        have h1 : z a * z b * Bh (x a - x b) ≤ |z a * z b| * βstar := by
          calc z a * z b * Bh (x a - x b) ≤ |z a * z b * Bh (x a - x b)| := le_abs_self _
            _ = |z a * z b| * |Bh (x a - x b)| := abs_mul _ _
            _ ≤ |z a * z b| * βstar := mul_le_mul_of_nonneg_left hB (abs_nonneg _)
        have h2 : |z a * z b| ≤ (z a ^ 2 + z b ^ 2) / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|z a| - |z b|), sq_abs (z a), sq_abs (z b)]
        nlinarith
      · have hP : ¬ P a b := fun h => hc h.2
        rw [if_neg hP, hBh_supp _ (not_lt.1 hc)]
        simp
  have hcount : ∀ a, ∑ b, (if P a b then (1 : ℝ) else 0) ≤ 2 := by
    intro a
    rw [← Finset.natCast_card_filter]
    exact_mod_cast close_le_two x hsep a
  have hsum1 : ∑ a, ∑ b, (if a = b then z a ^ 2 * Bh 0 else 0) = Bh 0 * ∑ a, z a ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq]; simp [mul_comm]
  have hsum2 : ∑ a, ∑ b, (if P a b then βstar * (z a ^ 2 + z b ^ 2) / 2 else 0)
      = βstar * ∑ a, z a ^ 2 * ∑ b, (if P a b then (1 : ℝ) else 0) := by
    have e1 : ∀ a b, (if P a b then βstar * (z a ^ 2 + z b ^ 2) / 2 else 0)
        = βstar / 2 * (z a ^ 2 * (if P a b then 1 else 0))
          + βstar / 2 * (z b ^ 2 * (if P b a then 1 else 0)) := by
      intro a b
      by_cases h : P a b
      · have h' : P b a := (hPsymm a b).1 h
        rw [if_pos h, if_pos h, if_pos h']; ring
      · have h' : ¬ P b a := fun h' => h ((hPsymm a b).2 h')
        rw [if_neg h, if_neg h, if_neg h']; ring
    have e2 : ∑ a, ∑ b, βstar / 2 * (z b ^ 2 * (if P b a then (1 : ℝ) else 0))
        = ∑ a, ∑ b, βstar / 2 * (z a ^ 2 * (if P a b then (1 : ℝ) else 0)) := Finset.sum_comm
    simp only [e1, Finset.sum_add_distrib]
    rw [e2, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have s3 : ∑ a, ∑ b, z a * z b * Bh (x a - x b) ≤ (Bh 0 + 2 * βstar) * ∑ a, z a ^ 2 := by
    have hle : ∑ a, z a ^ 2 * ∑ b, (if P a b then (1 : ℝ) else 0) ≤ ∑ a, z a ^ 2 * 2 :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hcount a) (sq_nonneg _)
    calc ∑ a, ∑ b, z a * z b * Bh (x a - x b)
        ≤ ∑ a, ∑ b, ((if a = b then z a ^ 2 * Bh 0 else 0)
            + (if P a b then βstar * (z a ^ 2 + z b ^ 2) / 2 else 0)) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = Bh 0 * ∑ a, z a ^ 2 + βstar * ∑ a, z a ^ 2 * ∑ b, (if P a b then (1 : ℝ) else 0) := by
          rw [← hsum1, ← hsum2, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
      _ ≤ Bh 0 * ∑ a, z a ^ 2 + βstar * ∑ a, z a ^ 2 * 2 := by
          have := mul_le_mul_of_nonneg_left hle hβs; linarith
      _ = (Bh 0 + 2 * βstar) * ∑ a, z a ^ 2 := by rw [← Finset.sum_mul]; ring
  -- Σ z² ≤ 2 Σ y²
  have s4 : ∑ a, z a ^ 2 ≤ 2 * ∑ a, y a ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    simp only [hz]
    rw [mul_pow, Real.sq_sqrt (hmv a).2]
    have := (hmv a).1; have := sq_nonneg (y a)
    nlinarith
  have hc0 : 0 ≤ Bh 0 + 2 * βstar := by linarith
  have he1 : 0 ≤ 1 + e := by linarith
  have hy0 : 0 ≤ ∑ a, y a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [hLHS]
  calc ∑ a, ∑ b, z a * z b * k (x a - x b)
      ≤ (1 + e) * ∑ a, ∑ b, z a * z b * kPsi ψ (x a - x b) := s1
    _ ≤ (1 + e) * ((Bh 0 + 2 * βstar) * ∑ a, z a ^ 2) := mul_le_mul_of_nonneg_left (s2.trans s3) he1
    _ ≤ (1 + e) * ((Bh 0 + 2 * βstar) * (2 * ∑ a, y a ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s4 hc0) he1
    _ ≤ (1 + e) * β * ∑ a, y a ^ 2 := by
        have : (Bh 0 + 2 * βstar) * (2 * ∑ a, y a ^ 2) ≤ β * ∑ a, y a ^ 2 := by nlinarith
        nlinarith

end ZetaS
