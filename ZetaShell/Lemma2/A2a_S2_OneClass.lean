/-
A2a_S2_OneClass (L7_8, 28 Sep 2026): the structural claim of **Step 2 of the proof of Lemma 2(a)**
(sec_shell.tex l.323–327), sorry-free: "for each `g` the admissible `k` form one class modulo `lcm(g, f_(r))`, or the
empty set", with `f_(r) = ∏_{p | f, p ∤ r} p`.

For `f` squarefree, `g ∈ ℕ` and integers `r, r′, j`, put `S = {k ∈ ℤ : g ∣ k, f ∣ rk − r′j}` and `m = lcm(g, f_(r))`.
* `oneClass_closed`: `k ∈ S ⟹ k + t·m ∈ S` for every integer `t`;
* `oneClass_unique`: `k, k′ ∈ S ⟹ m ∣ k − k′`.
So `S` is empty or exactly one residue class mod `m`; with `progression_count` (A2a_S2_Progression) the number of
`k ∈ (X, Y]` in `S` is `(Y − X)/m + ϑ`, `|ϑ| ≤ 1`, when `S ≠ ∅`.
-/
import ZetaShell.Lemma2.A2a_S2_CRT

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- `f_(r) = ∏_{p | f, p ∤ r} p`. -/
def fOff (f : ℕ) (r : ℤ) : ℕ := ∏ p ∈ f.primeFactors.filter (fun p : ℕ => ¬ ((p : ℕ) : ℤ) ∣ r), p

theorem fOff_dvd_iff_prime {f : ℕ} {r : ℤ} (n : ℕ)
    (h : ∀ p ∈ f.primeFactors.filter (fun p : ℕ => ¬ ((p : ℕ) : ℤ) ∣ r), p ∣ n) : fOff f r ∣ n := by
  unfold fOff
  apply Finset.prod_primes_dvd n
  · intro p hp
    exact Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
  · exact h

theorem mem_fOff_dvd {f : ℕ} {r : ℤ} {p : ℕ} (hp : p ∈ f.primeFactors.filter (fun p : ℕ => ¬ ((p : ℕ) : ℤ) ∣ r)) :
    p ∣ fOff f r := by
  unfold fOff
  exact Finset.dvd_prod_of_mem _ hp

/-- closure of the admissible set under adding multiples of `m = lcm(g, f_(r))`. -/
theorem oneClass_closed (f g : ℕ) (hf : Squarefree f) (r r' j k t : ℤ)
    (hk : (g : ℤ) ∣ k ∧ (f : ℤ) ∣ r * k - r' * j) :
    (g : ℤ) ∣ k + t * (Nat.lcm g (fOff f r) : ℤ) ∧
      (f : ℤ) ∣ r * (k + t * (Nat.lcm g (fOff f r) : ℤ)) - r' * j := by
  set m : ℕ := Nat.lcm g (fOff f r) with hm
  constructor
  · have : (g : ℤ) ∣ (m : ℤ) := by exact_mod_cast Nat.dvd_lcm_left g (fOff f r)
    exact dvd_add hk.1 (dvd_mul_of_dvd_right this t)
  · have hfrm : (f : ℤ) ∣ r * (m : ℤ) := by
      rw [Int.natCast_dvd]
      rw [← Nat.prod_primeFactors_of_squarefree hf]
      apply Finset.prod_primes_dvd
      · intro p hp; exact Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp)
      · intro p hp
        rw [← Int.natCast_dvd]
        by_cases hpr : (p : ℤ) ∣ r
        · exact dvd_mul_of_dvd_left hpr _
        · have h1 : p ∣ fOff f r := mem_fOff_dvd (Finset.mem_filter.mpr ⟨hp, hpr⟩)
          have h2 : p ∣ m := dvd_trans h1 (Nat.dvd_lcm_right g (fOff f r))
          have h3 : (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast h2
          exact dvd_mul_of_dvd_right h3 r
    have e : r * (k + t * (m : ℤ)) - r' * j = (r * k - r' * j) + t * (r * (m : ℤ)) := by ring
    rw [e]
    exact dvd_add hk.2 (dvd_mul_of_dvd_right hfrm t)

/-- two admissible `k` differ by a multiple of `m = lcm(g, f_(r))`. -/
theorem oneClass_unique (f g : ℕ) (r r' j k k' : ℤ)
    (hk : (g : ℤ) ∣ k ∧ (f : ℤ) ∣ r * k - r' * j) (hk' : (g : ℤ) ∣ k' ∧ (f : ℤ) ∣ r * k' - r' * j) :
    (Nat.lcm g (fOff f r) : ℤ) ∣ k - k' := by
  rw [Int.natCast_dvd]
  apply Nat.lcm_dvd
  · rw [← Int.natCast_dvd]; exact dvd_sub hk.1 hk'.1
  · apply fOff_dvd_iff_prime
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Nat.prime_of_mem_primeFactors hp'.1)
    have hpf : (p : ℤ) ∣ (f : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp'.1
    rw [← Int.natCast_dvd]
    exact line_class_unique hprime hp'.2 j k k' (dvd_trans hpf hk.2) (dvd_trans hpf hk'.2)

end TrackF
end ZetaShell
