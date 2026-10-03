/-
Node L3 (track L) — lem:zeta-Phi, sec_zeta.tex l.330–361: "Let G ⪰ 0 be m×m with unit diagonal, and let
E := ‖G − I‖². Then tr Ψ(G) ≥ Φ_m(E)." (Φ_m as `PhiM`; the regularity claims — increasing, concave, C¹,
Φ_m(0) = 0 — are node L3b.)
Deps: Interfaces (PhiM, Psi, trFun). Proof: eigenvalue bookkeeping (l.340–358), Cauchy–Schwarz on the complement.

Proof (L2_1). Eigenvalues `λᵢ`, `uᵢ = λᵢ − 1`: `∑uᵢ = 0` (unit diagonal), `∑uᵢ² = E`, `Ψ(λ) = u² − ((λ−2)₊)²`, so
`trΨ(G) = E − F`, `F = ∑((λᵢ−2)₊)²`, and `Φ_m(E) = E − ((√(kE) − 1)₊)²`, `k = (m−1)/m` (`PhiM_eq`). If `F > 0`, with
`J = {λ > 2}`, `j = |J| ≥ 1`, `σ = ∑_J(λᵢ − 2) ≥ w := √F`, `X = ∑_{Jᶜ}uᵢ²`, `D = |Jᶜ|`: `∑_J uᵢ² = F + 2σ + j`,
`∑_{Jᶜ}uᵢ = −(σ + j)`, Cauchy–Schwarz `D·X ≥ (σ+j)² ≥ (w+1)²`, and `m − 1 = D + j − 1 ≥ D`, so
`(m−1)E = (m−1)X + (m−1)(F+2σ+j) ≥ (w+1)² + (m−1)(w+1)² = m(w+1)²`, i.e. `1 + w ≤ √(kE)`, i.e. `F ≤ ((√(kE)−1)₊)²`.
(The paper's variable `V = 1 + √F_J`; positivity of `G` is not used beyond Hermitian-ness.)
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.PhiMHelpers

open Matrix RHLinalg Finset

namespace ZetaS

private lemma psi_eq_sq_sub (t : ℝ) : Psi t = (t - 1) ^ 2 - (max (t - 2) 0) ^ 2 := by
  unfold Psi
  split_ifs with h
  · rw [max_eq_right (by linarith)]; ring
  · rw [max_eq_left (by linarith)]; ring

/-- The real core of lem:zeta-Phi: for reals `λ₁,…,λ_m` (`m ≥ 2`) with `∑λᵢ = m`,
`Φ_m(∑(λᵢ − 1)²) ≤ ∑Ψ(λᵢ)`. -/
private lemma core_real {m : ℕ} (hm : 2 ≤ m) (lam : Fin m → ℝ) (hsum : ∑ i, lam i = m) :
    PhiM m (∑ i, (lam i - 1) ^ 2) ≤ ∑ i, Psi (lam i) := by
  classical
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set E := ∑ i, (lam i - 1) ^ 2 with hE
  set F := ∑ i, (max (lam i - 2) 0) ^ 2 with hF
  have hPsi : ∑ i, Psi (lam i) = E - F := by
    simp only [psi_eq_sq_sub, Finset.sum_sub_distrib, hE, hF]
  rw [hPsi, PhiM_eq hm]
  suffices h : F ≤ (max (Real.sqrt (((m : ℝ) - 1) * E / m) - 1) 0) ^ 2 by linarith
  have hF0 : 0 ≤ F := sum_nonneg fun i _ => sq_nonneg _
  rcases hF0.eq_or_lt with hF0 | hFpos
  · rw [← hF0]; positivity
  -- `J = {λ > 2}`, `Jc` its complement.
  set J := univ.filter (fun i => 2 < lam i) with hJ
  set Jc := univ.filter (fun i => ¬ 2 < lam i) with hJc
  set σ := ∑ i ∈ J, (lam i - 2) with hσ
  set X := ∑ i ∈ Jc, (lam i - 1) ^ 2 with hX
  have hFJ : F = ∑ i ∈ J, (lam i - 2) ^ 2 := by
    rw [hF, hJ, Finset.sum_filter]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [max_eq_left (by linarith)]
    · rw [max_eq_right (by linarith)]; ring
  have hJpos : ∀ i ∈ J, 0 ≤ lam i - 2 := fun i hi => by
    simp only [hJ, mem_filter, mem_univ, true_and] at hi; linarith
  have hJne : J.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hFJ, hne, sum_empty] at hFpos
    exact lt_irrefl _ hFpos
  have hj1 : (1 : ℝ) ≤ #J := by exact_mod_cast hJne.card_pos
  have hσ0 : 0 ≤ σ := sum_nonneg hJpos
  -- `w = √F ≤ σ`.
  set w := Real.sqrt F with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = F := Real.sq_sqrt hF0
  have hFσ : F ≤ σ ^ 2 := by
    rw [hFJ]
    calc ∑ i ∈ J, (lam i - 2) ^ 2 ≤ ∑ i ∈ J, (lam i - 2) * σ := by
          refine sum_le_sum fun i hi => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left
            (single_le_sum (f := fun i => lam i - 2) hJpos hi) (hJpos i hi)
      _ = σ ^ 2 := by rw [← Finset.sum_mul, sq]
  have hwσ : w ≤ σ := (Real.sqrt_le_sqrt hFσ).trans_eq (Real.sqrt_sq hσ0)
  -- Bookkeeping on `J` and `Jc`.
  have hcard : (#J : ℝ) + #Jc = m := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) (fun i => 2 < lam i)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have htot : ∑ i, (lam i - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]; simp
  have hsplit1 : ∑ i ∈ J, (lam i - 1) + ∑ i ∈ Jc, (lam i - 1) = 0 := by
    rw [hJ, hJc, sum_filter_add_sum_filter_not]; exact htot
  have hsumJ : ∑ i ∈ J, (lam i - 1) = σ + #J := by
    have e : ∀ i, lam i - 1 = (lam i - 2) + 1 := fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hσ]
  have hsqJ : ∑ i ∈ J, (lam i - 1) ^ 2 = F + 2 * σ + #J := by
    have e : ∀ i, (lam i - 1) ^ 2 = (lam i - 2) ^ 2 + 2 * (lam i - 2) + 1 := fun i => by ring
    rw [hFJ, hσ, Finset.mul_sum]
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hEsplit : E = ∑ i ∈ J, (lam i - 1) ^ 2 + X := by
    rw [hE, hX, hJ, hJc, sum_filter_add_sum_filter_not]
  have hCS : (∑ i ∈ Jc, (lam i - 1)) ^ 2 ≤ #Jc * X := sq_sum_le_card_mul_sum_sq
  have hX0 : 0 ≤ X := sum_nonneg fun i _ => sq_nonneg _
  -- The main estimate `m (1 + w)² ≤ (m − 1) E`.
  have h2 : (σ + #J) ^ 2 ≤ #Jc * X := by
    have : ∑ i ∈ Jc, (lam i - 1) = -(σ + #J) := by linarith
    rw [this, neg_sq] at hCS; exact hCS
  have h3 : (w + 1) ^ 2 ≤ (σ + #J) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h1 : (#Jc : ℝ) * X ≤ ((m : ℝ) - 1) * X :=
    mul_le_mul_of_nonneg_right (by linarith) hX0
  have h4 : ((m : ℝ) - 1) * (w + 1) ^ 2 ≤ ((m : ℝ) - 1) * (F + 2 * σ + #J) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have hmain : (1 + w) ^ 2 ≤ ((m : ℝ) - 1) * E / m := by
    rw [le_div_iff₀ hm0, hEsplit, hsqJ]
    nlinarith
  have hsq : 1 + w ≤ Real.sqrt (((m : ℝ) - 1) * E / m) :=
    (Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 + w)).symm.trans_le (Real.sqrt_le_sqrt hmain)
  have hmax : w ≤ max (Real.sqrt (((m : ℝ) - 1) * E / m) - 1) 0 := le_max_of_le_left (by linarith)
  rw [← hw2]
  exact pow_le_pow_left₀ hw0 hmax 2

theorem trPsi_ge_PhiM {m : ℕ} {G : Matrix (Fin m) (Fin m) ℝ} (hG : G.PosSemidef)
    (hdiag : ∀ i, G i i = 1) :
    PhiM m (frobSq (G - 1)) ≤ trFun hG.isHermitian Psi := by
  set lam := hG.isHermitian.eigenvalues with hlam
  -- `∑ λᵢ = tr G = m`.
  have htr : ∑ i, lam i = m := by
    rw [hlam, ← rtrace_eq_sum_eigenvalues hG.isHermitian]
    simp [rtrace, Matrix.trace, hdiag]
  -- `‖G − I‖² = ∑ (λᵢ − 1)²`.
  have hfrob : frobSq (G - 1) = ∑ i, (lam i - 1) ^ 2 := by
    have hneg : frobSq (-1 : Matrix (Fin m) (Fin m) ℝ) = m := by
      simp [frobSq]
    rw [sub_eq_add_neg, frobSq_add_hermitian hG.isHermitian (isHermitian_one.neg), hneg,
      frobSq_hermitian_eq_sum_sq_eigenvalues hG.isHermitian]
    have h1 : RCLike.re (G * -1).trace = -∑ i, lam i := by
      rw [mul_neg, mul_one, trace_neg, map_neg, hlam, ← rtrace_eq_sum_eigenvalues hG.isHermitian]
      rfl
    rw [h1]
    have h2 : ∑ i, (lam i - 1) ^ 2 = ∑ i, lam i ^ 2 - 2 * ∑ i, lam i + m := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      simp
    rw [h2]; ring
  rw [hfrob]
  unfold trFun
  rcases lt_or_ge m 2 with hm | hm
  · -- `m ≤ 1`: `G = (1)` or empty; `E = 0`, both sides `0`.
    interval_cases m
    · simp [PhiM]
    · have h0 : lam 0 = 1 := by simpa using htr
      show PhiM 1 (∑ i, (lam i - 1) ^ 2) ≤ ∑ i, Psi (lam i)
      rw [Fin.sum_univ_one, Fin.sum_univ_one, h0]
      norm_num [PhiM, Psi]
  · exact core_real hm lam htr

end ZetaS
