/-
A2a_S2s_MainAux (L7_8, round 4): lemmas for `s2_main` (the Möbius main-term identity of Step 2).
* `mu_lcm_divisor_sum`: `Σ_{g|n} μ(g)/lcm(g,F) = (1/F)·∏_{p|n}(1 − gcd(p,F)/p)` (divisors → subsets of primes, then
  `mobius_lcm_sum`);
* `prod_one_sub_inv_primeFactors`: `∏_{p|n}(1 − 1/p) = φ(n)/n`;
* `deltaProd_eval`: under admissibility, `∏_{p|f}δ_p = [no prime of |j| divides f_(r)]/f_(r)`; `deltaProd_zero`
  otherwise.
-/
import ZetaShell.Lemma2.A2a_S2s_Defs
import ZetaShell.Lemma2.A2a_S2_Mobius

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem fOff_pos (f : ℕ) (r : ℤ) : 0 < fOff f r := by
  unfold fOff
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem normalizedFactors_toFinset (n : ℕ) :
    (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
  rw [Nat.factors_eq]
  rfl

theorem mu_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    ((ArithmeticFunction.moebius (∏ p ∈ t, p) : ℤ) : ℝ) = (-1 : ℝ) ^ t.card := by
  rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime ArithmeticFunction.isMultiplicative_moebius t ht]
  rw [Finset.prod_congr rfl (fun p hp => ArithmeticFunction.moebius_apply_prime (ht p hp))]
  simp

theorem inv_lcm_eq (g F : ℕ) (hg : 0 < g) (hF : 0 < F) :
    1 / ((Nat.lcm g F : ℕ) : ℝ) = ((Nat.gcd g F : ℕ) : ℝ) / ((g : ℝ) * F) := by
  have h := Nat.gcd_mul_lcm g F
  have hl : 0 < Nat.lcm g F := Nat.lcm_pos hg hF
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hFR : (0 : ℝ) < F := by exact_mod_cast hF
  have hlR : (0 : ℝ) < (Nat.lcm g F : ℝ) := by exact_mod_cast hl
  have hR : ((Nat.gcd g F : ℕ) : ℝ) * ((Nat.lcm g F : ℕ) : ℝ) = (g : ℝ) * F := by exact_mod_cast h
  rw [div_eq_div_iff hlR.ne' (by positivity)]
  linarith

theorem mu_lcm_divisor_sum (n F : ℕ) (hn : n ≠ 0) (hF : 0 < F) :
    ∑ g ∈ n.divisors, ((ArithmeticFunction.moebius g : ℤ) : ℝ) * (1 / ((Nat.lcm g F : ℕ) : ℝ))
      = (1 / (F : ℝ)) * ∏ p ∈ n.primeFactors, (1 - ((Nat.gcd p F : ℕ) : ℝ) / (p : ℝ)) := by
  classical
  have hsq : ∑ g ∈ n.divisors, ((ArithmeticFunction.moebius g : ℤ) : ℝ) * (1 / ((Nat.lcm g F : ℕ) : ℝ))
      = ∑ g ∈ n.divisors with Squarefree g,
          ((ArithmeticFunction.moebius g : ℤ) : ℝ) * (1 / ((Nat.lcm g F : ℕ) : ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro g _
    split_ifs with hs
    · rfl
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; simp
  rw [hsq, Nat.sum_divisors_filter_squarefree hn, normalizedFactors_toFinset,
    ← mobius_lcm_sum n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) F, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htP : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
  have htp : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (htP hp)
  have hval : t.val.prod = ∏ p ∈ t, p := by simpa using (Finset.prod_val t)
  rw [hval, mu_prod_primes t htp]
  have hpos : 0 < ∏ p ∈ t, p := Finset.prod_pos (fun p hp => (htp p hp).pos)
  rw [inv_lcm_eq _ F hpos hF]
  have hPR : (0 : ℝ) < ((∏ p ∈ t, p : ℕ) : ℝ) := by exact_mod_cast hpos
  have hFR : (0 : ℝ) < F := by exact_mod_cast hF
  field_simp

theorem prod_one_sub_inv_primeFactors (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) = (Nat.totient n : ℝ) / n := by
  have h := Nat.totient_eq_mul_prod_factors n
  have hR : (Nat.totient n : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - ((p : ℕ) : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at this
    exact this
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [hR]
  field_simp

theorem deltaProd_eval (r j : ℤ) (f : ℕ) (hj : j ≠ 0) (hadm : admissibleP r j f) :
    deltaProd r j f = if (∀ p ∈ j.natAbs.primeFactors, ¬ p ∣ fOff f r) then 1 / (fOff f r : ℝ) else 0 := by
  classical
  unfold deltaProd
  split_ifs with hc
  · -- every p | f with p ∤ r has p ∤ j
    have hD : ∀ p ∈ f.primeFactors,
        (if ¬ ((p : ℕ) : ℤ) ∣ r ∧ ¬ ((p : ℕ) : ℤ) ∣ j then 1 / (p : ℝ)
          else if ((p : ℕ) : ℤ) ∣ r ∧ ((p : ℕ) : ℤ) ∣ j then 1 else 0)
        = if ¬ ((p : ℕ) : ℤ) ∣ r then 1 / (p : ℝ) else 1 := by
      intro p hp
      by_cases hpr : ((p : ℕ) : ℤ) ∣ r
      · have hpj := hadm p hp hpr
        simp [hpr, hpj]
      · have hpj : ¬ ((p : ℕ) : ℤ) ∣ j := by
          intro hpj
          have hpP : p ∈ j.natAbs.primeFactors := by
            rw [Nat.mem_primeFactors]
            refine ⟨Nat.prime_of_mem_primeFactors hp, ?_, Int.natAbs_ne_zero.mpr hj⟩
            exact Int.natCast_dvd.mp hpj
          apply hc p hpP
          exact mem_fOff_dvd (Finset.mem_filter.mpr ⟨hp, hpr⟩)
        simp [hpr, hpj]
    rw [Finset.prod_congr rfl hD, Finset.prod_ite, Finset.prod_const_one, mul_one]
    unfold fOff
    push_cast
    rw [one_div, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rw [one_div]
  · push_neg at hc
    obtain ⟨p, hpP, hpF⟩ := hc
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpP
    -- p | fOff f r ⇒ p is one of its primes
    have hmem : p ∈ f.primeFactors.filter (fun p : ℕ => ¬ ((p : ℕ) : ℤ) ∣ r) := by
      unfold fOff at hpF
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpprime) _).mp hpF
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      rw [(Nat.prime_dvd_prime_iff_eq hpprime hqprime).mp hpq]
      exact hq
    have hmem' := Finset.mem_filter.mp hmem
    have hpj : ((p : ℕ) : ℤ) ∣ j := by
      have : p ∣ j.natAbs := Nat.dvd_of_mem_primeFactors hpP
      exact Int.natCast_dvd.mpr this
    apply Finset.prod_eq_zero hmem'.1
    simp [hmem'.2, hpj]

theorem deltaProd_zero (r j : ℤ) (f : ℕ) (hadm : ¬ admissibleP r j f) : deltaProd r j f = 0 := by
  classical
  unfold admissibleP at hadm
  push_neg at hadm
  obtain ⟨p, hp, hpr, hpj⟩ := hadm
  unfold deltaProd
  apply Finset.prod_eq_zero hp
  simp [hpr, hpj]

end TrackF
end ZetaShell
