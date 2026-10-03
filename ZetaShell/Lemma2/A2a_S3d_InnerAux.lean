/-
A2a_S3d_InnerAux (L7_8, round 4): pieces of `s3_arith_inner`.
* `omega_eq_card_primeFactors`, `two_pow_omega_le_tau`: `2^{ω(n)} ≤ τ(n)`;
* `abs_lam_le`: `|λ_e(f)| ≤ Σ_{d|e, d|f} d/f`;
* `lam_sum_le`: `Σ_{1≤f≤Q} |λ_e(f)| ≤ τ(e)(1 + log Q)`.
-/
import ZetaShell.Lemma2.A2a_S3_Defs
import ZetaShell.Lemma2.A2a_S3d_JsumAux

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem omega_eq_card_primeFactors (n : ℕ) : ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  rfl

theorem two_pow_omega_le_tau (n : ℕ) (hn : n ≠ 0) :
    (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ (n.divisors.card : ℝ) := by
  rw [omega_eq_card_primeFactors]
  have h : (n.primeFactors.powerset).card ≤ n.divisors.card := by
    apply Finset.card_le_card_of_injOn (fun t => ∏ p ∈ t, p)
    · intro t ht
      have htP : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
      rw [Finset.mem_coe, Nat.mem_divisors]
      refine ⟨?_, hn⟩
      exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ htP) (Nat.prod_primeFactors_dvd n)
    · intro t ht t' ht' heq
      have htp : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
      have htp' : ∀ p ∈ t', p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht' hp)
      have := congrArg Nat.primeFactors heq
      simp only at this
      rwa [Nat.primeFactors_prod htp, Nat.primeFactors_prod htp'] at this
  rw [Finset.card_powerset] at h
  exact_mod_cast h

theorem abs_lam_le (k : FKind) (e f : ℕ) (he : 1 ≤ e) :
    |lam k e f| ≤ ∑ d ∈ e.divisors.filter (fun d => d ∣ f), (d : ℝ) / f := by
  classical
  unfold lam
  split_ifs with hsq
  · have hf0 : f ≠ 0 := hsq.ne_zero
    set P := f.primeFactors with hP
    set g := ∏ p ∈ P.filter (fun p => p ∣ e), p with hg
    have hgf : g ∣ f := by
      rw [hg]
      exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
        (Nat.prod_primeFactors_dvd f)
    have hge : g ∣ e := by
      rw [hg]
      apply Finset.prod_primes_dvd
      · intro p hp; exact Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      · intro p hp; exact (Finset.mem_filter.mp hp).2
    have hgmem : g ∈ e.divisors.filter (fun d => d ∣ f) :=
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hge, by omega⟩, hgf⟩
    -- |λ| ≤ g/f
    have hbound : |∏ p ∈ P, (hE k e p - 1)| ≤ (g : ℝ) / f := by
      rw [Finset.abs_prod]
      have hle : ∀ p ∈ P, |hE k e p - 1| ≤ (if p ∣ e then (1 : ℝ) else 1 / (p : ℝ)) := by
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        cases k <;> simp only [hE] <;> split_ifs <;> rw [abs_le] <;> constructor <;>
          first | norm_num | (have : 0 < 1 / (p : ℝ) := by positivity
                              have : 1 / (p : ℝ) ≤ 1 / 2 := by
                                rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
                              linarith)
      calc ∏ p ∈ P, |hE k e p - 1| ≤ ∏ p ∈ P, (if p ∣ e then (1 : ℝ) else 1 / (p : ℝ)) :=
            Finset.prod_le_prod (fun p _ => abs_nonneg _) hle
        _ = (g : ℝ) / f := by
            rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
            have hfprod : (f : ℝ) = ((∏ p ∈ P.filter (fun p => p ∣ e), p : ℕ) : ℝ) *
                ((∏ p ∈ P.filter (fun p => ¬ p ∣ e), p : ℕ) : ℝ) := by
              rw [← Nat.cast_mul, Finset.prod_filter_mul_prod_filter_not, hP, Nat.prod_primeFactors_of_squarefree hsq]
            rw [hfprod, hg]
            have hpos : (0 : ℝ) < ((∏ p ∈ P.filter (fun p => p ∣ e), p : ℕ) : ℝ) := by
              exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)
            push_cast
            rw [Finset.prod_div_distrib, Finset.prod_const_one]
            have hB : (∏ i ∈ P.filter (fun p => p ∣ e), (i : ℝ)) ≠ 0 :=
              Finset.prod_ne_zero_iff.mpr (fun i hi => by
                have := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hi).1).pos
                positivity)
            have hA : (∏ i ∈ P.filter (fun p => ¬ p ∣ e), (i : ℝ)) ≠ 0 :=
              Finset.prod_ne_zero_iff.mpr (fun i hi => by
                have := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hi).1).pos
                positivity)
            field_simp
    refine le_trans hbound ?_
    exact Finset.single_le_sum (f := fun d : ℕ => (d : ℝ) / (f : ℝ)) (fun d _ => div_nonneg (by positivity) (by positivity)) hgmem
  · rw [abs_zero]
    exact Finset.sum_nonneg (fun d _ => by positivity)

theorem lam_sum_le (k : FKind) (e Q : ℕ) (he : 1 ≤ e) (hQ : 1 ≤ Q) :
    ∑ f ∈ Finset.Icc 1 Q, |lam k e f| ≤ (e.divisors.card : ℝ) * (1 + Real.log Q) := by
  classical
  calc ∑ f ∈ Finset.Icc 1 Q, |lam k e f|
      ≤ ∑ f ∈ Finset.Icc 1 Q, ∑ d ∈ e.divisors.filter (fun d => d ∣ f), (d : ℝ) / f :=
        Finset.sum_le_sum (fun f _ => abs_lam_le k e f he)
    _ = ∑ d ∈ e.divisors, ∑ f ∈ (Finset.Icc 1 Q).filter (fun f => d ∣ f), (d : ℝ) / f := by
        rw [Finset.sum_comm' (t' := e.divisors) (s' := fun d => (Finset.Icc 1 Q).filter (fun f => d ∣ f))]
        intro f d
        simp only [Finset.mem_filter]
        tauto
    _ ≤ ∑ d ∈ e.divisors, (1 + Real.log Q) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
        have e1 : ∑ f ∈ (Finset.Icc 1 Q).filter (fun f => d ∣ f), (d : ℝ) / f
            = ∑ m ∈ Finset.Icc 1 (Q / d), 1 / (m : ℝ) := by
          symm
          apply Finset.sum_nbij' (fun m => d * m) (fun f => f / d)
          · intro m hm
            rw [Finset.mem_Icc] at hm
            rw [Finset.mem_filter, Finset.mem_Icc]
            refine ⟨⟨by nlinarith [hm.1], ?_⟩, dvd_mul_right d m⟩
            have := Nat.mul_le_of_le_div d m Q hm.2
            linarith [this, Nat.mul_comm m d]
          · intro f hf
            rw [Finset.mem_filter, Finset.mem_Icc] at hf
            rw [Finset.mem_Icc]
            obtain ⟨⟨hf1, hfQ⟩, c, rfl⟩ := hf
            rw [Nat.mul_div_cancel_left c (by omega)]
            constructor
            · rcases Nat.eq_zero_or_pos c with h | h
              · subst h; simp at hf1
              · exact h
            · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hfQ)
          · intro m _
            exact Nat.mul_div_cancel_left m (by omega)
          · intro f hf
            rw [Finset.mem_filter] at hf
            exact Nat.mul_div_cancel' hf.2
          · intro m hm
            rw [Finset.mem_Icc] at hm
            have hmR : (0 : ℝ) < m := by exact_mod_cast hm.1
            push_cast
            field_simp
        rw [e1]
        refine le_trans (sum_harmonic_le (Q / d)) ?_
        have hQd : ((Q / d : ℕ) : ℝ) ≤ Q := by exact_mod_cast Nat.div_le_self Q d
        rcases Nat.eq_zero_or_pos (Q / d) with h0 | hpos
        · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
          have := Real.log_nonneg (show (1 : ℝ) ≤ Q by exact_mod_cast hQ); linarith
        · have := Real.log_le_log (by exact_mod_cast hpos) hQd; linarith
    _ = (e.divisors.card : ℝ) * (1 + Real.log Q) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end TrackF
end ZetaShell
