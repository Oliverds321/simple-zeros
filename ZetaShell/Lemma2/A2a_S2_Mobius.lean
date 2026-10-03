/-
A2a_S2_Mobius (L7_8, round 2, 28 Sep 2026): the **Möbius main-term identity of Step 2** (sec_shell.tex l.323–331),
in subset form, sorry-free.

For a finite set `P` of primes (the primes of `j`) and `F ≥ 1` (`F = f_(r)`), with `g = ∏ t` running over the squarefree
divisors of `rad j` (`μ(g) = (−1)^{|t|}`) and `1/lcm(g, F) = gcd(g, F)/(gF)`:
`Σ_{t ⊆ P} (−1)^{|t|} gcd(∏t, F)/∏t = ∏_{p∈P} (1 − gcd(p, F)/p)`,
which is `φ(j)/j` if no prime of `F` divides `j`, and `0` otherwise (`mobius_lcm_sum`, `mobius_lcm_sum_eval`).
Combined with `admissible_exists`/`admissible_necessary` (non-emptiness of `S_g` does not depend on `g | j`) this is the
draft's main term `(φ(j)/j)∏_{p|f}δ_p` (the `1/F` factor is `∏_{p|f, p∤rj} 1/p`).
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem gcd_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (F : ℕ) :
    Nat.gcd (∏ p ∈ t, p) F = ∏ p ∈ t, Nat.gcd p F := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hs : ∀ p ∈ s, p.Prime := fun p hp => ht p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      have hpa : p ≠ a := fun h => ha (h ▸ hp)
      exact (Nat.coprime_primes (ht a (Finset.mem_insert_self a s)) (hs p hp)).mpr hpa.symm
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul F hcop, Nat.gcd_comm F a, Nat.gcd_comm F (∏ p ∈ s, p), ih hs]

theorem mobius_lcm_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (F : ℕ) :
    ∑ t ∈ P.powerset, (-1 : ℝ) ^ t.card * ((Nat.gcd (∏ p ∈ t, p) F : ℕ) : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ)
      = ∏ p ∈ P, (1 - ((Nat.gcd p F : ℕ) : ℝ) / (p : ℝ)) := by
  classical
  have h1 : ∏ p ∈ P, (1 - ((Nat.gcd p F : ℕ) : ℝ) / (p : ℝ))
      = ∏ p ∈ P, (1 + (-(((Nat.gcd p F : ℕ) : ℝ) / (p : ℝ)))) := by
    apply Finset.prod_congr rfl; intro p _; ring
  rw [h1, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t ht
  have htP : t ⊆ P := Finset.mem_powerset.mp ht
  have htp : ∀ p ∈ t, p.Prime := fun p hp => hP p (htP hp)
  rw [gcd_prod_primes t htp F]
  push_cast
  rw [Finset.prod_neg, Finset.prod_div_distrib]
  ring

theorem mobius_lcm_sum_eval (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (F : ℕ) :
    ∏ p ∈ P, (1 - ((Nat.gcd p F : ℕ) : ℝ) / (p : ℝ))
      = if (∀ p ∈ P, ¬ p ∣ F) then ∏ p ∈ P, (1 - 1 / (p : ℝ)) else 0 := by
  classical
  split_ifs with h
  · apply Finset.prod_congr rfl
    intro p hp
    have : Nat.gcd p F = 1 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (hP p hp)).mpr (h p hp))).symm
    rw [this]; simp
  · push_neg at h
    obtain ⟨p, hp, hpF⟩ := h
    apply Finset.prod_eq_zero hp
    rw [Nat.gcd_eq_left hpF]
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    field_simp
    ring

end TrackF
end ZetaShell
