/-
A2a_S2_CRTExist (L7_8, round 2, 28 Sep 2026): **Step 2, existence of an admissible `k`** (sec_shell.tex l.323–327):
"for each `g` the admissible `k` form one class modulo `lcm(g, f_(r))`, **or the empty set**". The set
`S_g = {k : g | k, f | rk − r′j}` is non-empty exactly when every prime `p | f` with `p | r` divides `j`
(for `g | j`). Proved here (sorry-free): the "if" direction, by an explicit CRT solution
`k = g·u·r′·j` with `u·(rg) + v·F₂ = 1`, `F₂ = ∏_{p|f, p∤r, p∤g} p`.
Together with `oneClass_closed`/`oneClass_unique` (A2a_S2_OneClass) this gives the full structure of `S_g`.
-/
import ZetaShell.Lemma2.A2a_S2_OneClass

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem admissible_exists (r r' j : ℤ) (g f : ℕ) (hf : Squarefree f) (hgj : (g : ℤ) ∣ j)
    (hcond : ∀ p ∈ f.primeFactors, ((p : ℕ) : ℤ) ∣ r → ((p : ℕ) : ℤ) ∣ j) :
    ∃ k : ℤ, (g : ℤ) ∣ k ∧ (f : ℤ) ∣ r * k - r' * j := by
  classical
  set P := f.primeFactors.filter (fun p : ℕ => ¬ ((p : ℕ) : ℤ) ∣ r ∧ ¬ ((p : ℕ) : ℤ) ∣ (g : ℤ)) with hP
  set F2 : ℤ := ∏ p ∈ P, ((p : ℕ) : ℤ) with hF2
  have hcop : IsCoprime (r * (g : ℤ)) F2 := by
    rw [hF2]
    apply IsCoprime.prod_right
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (Nat.prime_of_mem_primeFactors hp'.1)
    have hnd : ¬ ((p : ℕ) : ℤ) ∣ r * (g : ℤ) := by
      intro h
      rcases hprime.dvd_or_dvd h with h1 | h1
      · exact hp'.2.1 h1
      · exact hp'.2.2 h1
    exact ((Irreducible.coprime_iff_not_dvd hprime.irreducible).mpr hnd).symm
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨(g : ℤ) * (u * r' * j), dvd_mul_right _ _, ?_⟩
  have hkey : r * ((g : ℤ) * (u * r' * j)) - r' * j = -(r' * j * v) * F2 := by
    linear_combination (r' * j) * huv
  rw [Int.natCast_dvd, ← Nat.prod_primeFactors_of_squarefree hf]
  apply Finset.prod_primes_dvd
  · intro p hp; exact Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp)
  · intro p hp
    rw [← Int.natCast_dvd]
    by_cases hpr : ((p : ℕ) : ℤ) ∣ r
    · have hpj := hcond p hp hpr
      exact dvd_sub (dvd_mul_of_dvd_left hpr _) (dvd_mul_of_dvd_right hpj _)
    · by_cases hpg : ((p : ℕ) : ℤ) ∣ (g : ℤ)
      · have hpj : ((p : ℕ) : ℤ) ∣ j := dvd_trans hpg hgj
        have hpk : ((p : ℕ) : ℤ) ∣ (g : ℤ) * (u * r' * j) := dvd_mul_of_dvd_left hpg _
        exact dvd_sub (dvd_mul_of_dvd_right hpk _) (dvd_mul_of_dvd_right hpj _)
      · rw [hkey]
        apply dvd_mul_of_dvd_right
        rw [hF2]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hp, hpr, hpg⟩)

/-- the "only if" direction: if some `k` is admissible, every `p | f` with `p | r` divides `j` (needs `(r, r′) = 1`). -/
theorem admissible_necessary (r r' j : ℤ) (f : ℕ) (hrr' : IsCoprime r r') (k : ℤ)
    (hk : (f : ℤ) ∣ r * k - r' * j) : ∀ p ∈ f.primeFactors, ((p : ℕ) : ℤ) ∣ r → ((p : ℕ) : ℤ) ∣ j := by
  intro p hp hpr
  have hprime : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (Nat.prime_of_mem_primeFactors hp)
  have hpf : ((p : ℕ) : ℤ) ∣ (f : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
  have h1 : ((p : ℕ) : ℤ) ∣ r * k - r' * j := dvd_trans hpf hk
  have h2 : ((p : ℕ) : ℤ) ∣ r' * j := by
    have := dvd_sub (dvd_mul_of_dvd_left hpr k) h1
    rwa [show r * k - (r * k - r' * j) = r' * j by ring] at this
  rcases hprime.dvd_or_dvd h2 with h3 | h3
  · exfalso
    obtain ⟨a, b, hab⟩ := hrr'
    have : ((p : ℕ) : ℤ) ∣ a * r + b * r' := dvd_add (dvd_mul_of_dvd_right hpr a) (dvd_mul_of_dvd_right h3 b)
    rw [hab] at this
    exact hprime.not_isUnit (isUnit_of_dvd_one this)
  · exact h3

end TrackF
end ZetaShell
