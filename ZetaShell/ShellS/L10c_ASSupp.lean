/-
L10c_ASSupp (L7_10c, 3 Oct 2026): bookkeeping for the AS assembly: truncation of sums beyond the support of the
near-P vector, `H_w = |𝔉_Q|` for the sharp family, and the two complement vectors `a − b`, `aPrime − b`.
-/
import ZetaShell.ShellS.L10c_ASArith

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace ShellS
namespace ASc

theorem sum_trunc {M : Type*} [AddCommMonoid M] (Nn Nx : ℕ) (h : Nn ≤ Nx) (f : ℕ → M)
    (hf : ∀ n, Nn < n → n ≤ Nx → f n = 0) :
    ∑ n ∈ Finset.Ioc 0 Nx, f n = ∑ n ∈ Finset.Ioc 0 Nn, f n := by
  symm
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc le_rfl h)
  intro n hn hnn
  rw [Finset.mem_Ioc] at hn hnn
  exact hf n (by omega) hn.2

theorem famF_trunc (M : Finset ℕ) (Nn Nx : ℕ) (h : Nn ≤ Nx) (b : ℕ → ℂ) (hb : ∀ n, Nn < n → b n = 0) :
    TrackF.famF M Nx b = TrackF.famF M Nn b := by
  unfold TrackF.famF ZetaQ.charSum
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
  rw [sum_trunc Nn Nx h _ (fun n hn _ => by rw [hb n hn, zero_mul])]

theorem expSum_trunc (Nn Nx : ℕ) (h : Nn ≤ Nx) (b : ℕ → ℂ) (hb : ∀ n, Nn < n → b n = 0) (θ : ℝ) :
    ZetaQ.expSum Nx b θ = ZetaQ.expSum Nn b θ := by
  unfold ZetaQ.expSum
  rw [sum_trunc Nn Nx h _ (fun n hn _ => by rw [hb n hn, zero_mul])]

theorem l2sq_trunc (Nn Nx : ℕ) (h : Nn ≤ Nx) (b : ℕ → ℂ) (hb : ∀ n, Nn < n → b n = 0) :
    ZetaQ.l2sq Nx b = ZetaQ.l2sq Nn b := by
  unfold ZetaQ.l2sq
  rw [sum_trunc Nn Nx h _ (fun n hn _ => by rw [hb n hn]; simp)]

theorem holeInt_trunc (Nn Nx : ℕ) (h : Nn ≤ Nx) (b : ℕ → ℂ) (hb : ∀ n, Nn < n → b n = 0) (R Δ : ℝ) :
    LemmaK.holeInt Nx b R Δ = LemmaK.holeInt Nn b R Δ := by
  unfold LemmaK.holeInt
  simp_rw [expSum_trunc Nn Nx h b hb]

theorem Hw_sharp_famSize (Q : ℕ) : TrackF.Hw .sharp Q = famSize Q := by
  unfold TrackF.Hw famSize
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [omega_sharp_eq_one Q q (Finset.mem_Icc.mp hq).2, one_mul]
  rfl

/-- `b` vanishes beyond `⌊e^{s+1}⌋`. -/
theorem aNearP_zero_beyond (Q T κ : ℝ) (Ξ : ℝ → ℝ) (hΞ : PropZ.NearCutoff Ξ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (s : ℝ) (n : ℕ) (hn : ⌊Real.exp (s + 1)⌋₊ < n) : aNearP Q T κ Ξ s n = 0 := by
  by_contra h
  obtain ⟨hp, -, hclose⟩ := aNearP_support Q T κ Ξ hΞ hκ s n h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hp.pos
  have h1 : Real.log n < s + 1 := by linarith [(abs_lt.mp hclose).2]
  have h2 : (n : ℝ) < Real.exp (s + 1) := by rw [← Real.exp_log hnR]; exact Real.exp_lt_exp.mpr h1
  have h3 : n ≤ ⌊Real.exp (s + 1)⌋₊ := Nat.le_floor h2.le
  omega

/-- on a near prime, `b = a`. -/
theorem aNearP_eq_near (Q T κ c : ℝ) (Ξ : ℝ → ℝ) (hκ : 0 < κ) (hΞc : ∀ z, |z| ≤ c → Ξ z = 1)
    (s : ℝ) (n : ℕ) (hp : n.Prime) (hQn : Q < (n : ℝ)) (hclose : |Real.log n - s| ≤ min c 1 * κ) :
    aNearP Q T κ Ξ s n = TrackF.acoefS T s n := by
  unfold aNearP
  rw [if_pos ⟨hp, hQn⟩]
  have h1 : |(Real.log n - s) / κ| ≤ c := by
    rw [abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
    exact le_trans hclose (mul_le_mul_of_nonneg_right (min_le_left _ _) hκ.le)
  rw [hΞc _ h1]; simp

/-- the complement `a − b`. -/
theorem diff_a_b (Q T κ c : ℝ) (Ξ : ℝ → ℝ) (hΞ : PropZ.NearCutoff Ξ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hΞc : ∀ z, |z| ≤ c → Ξ z = 1)
    (s : ℝ) (hsQ : Real.log Q + 1 < s) (hQ : 1 ≤ Q) :
    (∀ n, ‖TrackF.acoefS T s n - aNearP Q T κ Ξ s n‖ ≤ ‖TrackF.acoefS T s n‖) ∧
    (∀ n : ℕ, n.Prime → |Real.log n - s| ≤ min c 1 * κ → TrackF.acoefS T s n - aNearP Q T κ Ξ s n = 0) := by
  constructor
  · intro n
    unfold aNearP
    split_ifs with h
    · have e : TrackF.acoefS T s n - TrackF.acoefS T s n * ((Ξ ((Real.log n - s) / κ) : ℝ) : ℂ)
          = TrackF.acoefS T s n * ((1 - Ξ ((Real.log n - s) / κ) : ℝ) : ℂ) := by push_cast; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h0 := hΞ.nonneg ((Real.log n - s) / κ)
      have h1 := hΞ.le_one ((Real.log n - s) / κ)
      rw [abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_right (norm_nonneg _) (by linarith)
    · simp
  · intro n hp hclose
    have hnR : (0 : ℝ) < n := by exact_mod_cast hp.pos
    have hQn : Q < (n : ℝ) := by
      have hd : min c 1 * κ ≤ 1 * κ := mul_le_mul_of_nonneg_right (min_le_right _ _) hκ.le
      have h1 : s - 1 ≤ Real.log n := by
        have := (abs_le.mp hclose).1
        linarith
      have h2 : Real.log Q < Real.log n := by linarith
      exact (Real.log_lt_log_iff (by linarith) hnR).mp h2
    rw [aNearP_eq_near Q T κ c Ξ hκ hΞc s n hp hQn hclose, sub_self]

/-- the complement `aPrime − b` (Lemma K's comparison vector minus the near-P vector). -/
theorem diff_aP_b (Q T κ c R0 : ℝ) (Ξ : ℝ → ℝ) (hΞ : PropZ.NearCutoff Ξ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hΞc : ∀ z, |z| ≤ c → Ξ z = 1) (s : ℝ) (hsQ : Real.log Q + 1 < s) (hQ : 1 ≤ Q) (hR0Q : R0 < Q) :
    (∀ n, ‖LemmaK.aPrime T s R0 n - aNearP Q T κ Ξ s n‖ ≤ ‖TrackF.acoefS T s n‖) ∧
    (∀ n : ℕ, n.Prime → |Real.log n - s| ≤ min c 1 * κ → LemmaK.aPrime T s R0 n - aNearP Q T κ Ξ s n = 0) := by
  constructor
  · intro n
    have hA : LemmaK.aPrime T s R0 n = TrackF.acoefS T s n ∨ LemmaK.aPrime T s R0 n = 0 := by
      unfold LemmaK.aPrime
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hB : ∃ ξ : ℝ, 0 ≤ ξ ∧ ξ ≤ 1 ∧ aNearP Q T κ Ξ s n = TrackF.acoefS T s n * (ξ : ℂ) := by
      unfold aNearP
      split_ifs
      · exact ⟨_, hΞ.nonneg _, hΞ.le_one _, rfl⟩
      · exact ⟨0, le_rfl, zero_le_one, by simp⟩
    obtain ⟨ξ, hξ0, hξ1, hb⟩ := hB
    rw [hb]
    rcases hA with h | h
    · rw [h]
      have e : TrackF.acoefS T s n - TrackF.acoefS T s n * (ξ : ℂ) = TrackF.acoefS T s n * ((1 - ξ : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_right (norm_nonneg _) (by linarith)
    · rw [h, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hξ0]
      exact mul_le_of_le_one_right (norm_nonneg _) hξ1
  · intro n hp hclose
    have hnR : (0 : ℝ) < n := by exact_mod_cast hp.pos
    have hd : min c 1 * κ ≤ 1 * κ := mul_le_mul_of_nonneg_right (min_le_right _ _) hκ.le
    have h1 : s - 1 ≤ Real.log n := by
      have := (abs_le.mp hclose).1
      linarith
    have hQn : Q < (n : ℝ) := (Real.log_lt_log_iff (by linarith) hnR).mp (by linarith)
    have haP : LemmaK.aPrime T s R0 n = TrackF.acoefS T s n := by
      unfold LemmaK.aPrime
      rw [if_pos ⟨hp.isPrimePow, by rw [hp.minFac_eq]; linarith⟩]
      rfl
    rw [haP, aNearP_eq_near Q T κ c Ξ hκ hΞc s n hp hQn hclose, sub_self]

end ASc
end ShellS
end ZetaShell
