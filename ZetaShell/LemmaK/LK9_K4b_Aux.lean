/-
L7_9 helper for node K4b (`log_succ_le_sum_moebius_sq_div_totient`).
`Σ_{n ≤ R} 1/n ≤ Σ_{r ≤ R} μ²(r)/φ(r)`, by grouping `n` by its radical `rad n = ∏_{p | n} p`:
for squarefree `r`, `Σ_{n ∈ A, rad n = r} 1/n ≤ r⁻¹ Σ_{m r-factored} 1/m = r⁻¹ ∏_{p | r}(1 − 1/p)⁻¹ = 1/φ(r)`
(Mathlib's Euler product over `factoredNumbers`).
-/
import Mathlib

noncomputable section
open Finset

namespace ZetaShell
namespace LemmaK
namespace K4bAux

/-- the radical `∏_{p | n} p`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  unfold rad
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (Nat.prime_of_mem_primeFactors hp).squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq

lemma primeFactors_rad (n : ℕ) : (rad n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod_primeFactors n

/-- `n ↦ 1/n` as a monoid hom `ℕ →* ℝ`. -/
def invHom : ℕ →* ℝ where
  toFun n := ((n : ℕ) : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; exact mul_inv _ _

lemma hasSum_inv_factored (s : Finset ℕ) :
    HasSum (fun m : Nat.factoredNumbers s => (((m : ℕ) : ℝ))⁻¹)
      (∏ p ∈ s with p.Prime, (1 - ((p : ℕ) : ℝ)⁻¹)⁻¹) := by
  have h : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, Real.norm_natCast]
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact inv_lt_one_of_one_lt₀ this
  have := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := invHom) h s).2
  simpa [invHom] using this

/-- `r · ∏_{p | r}(1 − 1/p) = φ(r)`, in `ℝ`. -/
lemma totient_real (r : ℕ) :
    ((Nat.totient r : ℕ) : ℝ) = (r : ℝ) * ∏ p ∈ r.primeFactors, (1 - ((p : ℕ) : ℝ)⁻¹) := by
  have h := Nat.totient_eq_mul_prod_factors r
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simpa using h'

/-- **The fibre bound.** For squarefree `r` and a finite set `A` of positive `n` with `rad n = r`,
`Σ_{n ∈ A} 1/n ≤ 1/φ(r)`. -/
lemma fiber_bound (r : ℕ) (A : Finset ℕ) (hA : ∀ n ∈ A, n ≠ 0 ∧ rad n = r) :
    ∑ n ∈ A, ((n : ℕ) : ℝ)⁻¹ ≤ ((Nat.totient r : ℕ) : ℝ)⁻¹ := by
  classical
  rcases A.eq_empty_or_nonempty with hAe | ⟨n₀, hn₀⟩
  · simp [hAe]
  have hr0 : 0 < r := (hA n₀ hn₀).2 ▸ rad_pos n₀
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hdvd : ∀ n ∈ A, r ∣ n := fun n hn => (hA n hn).2 ▸ rad_dvd n
  -- the cofactor map `n ↦ n / r`
  set B : Finset ℕ := A.image (fun n => n / r) with hB
  have hinj : Set.InjOn (fun n => n / r) (A : Set ℕ) := by
    intro x hx y hy hxy
    simp only at hxy
    rw [← Nat.div_mul_cancel (hdvd x hx), ← Nat.div_mul_cancel (hdvd y hy), hxy]
  have hsumA : ∑ n ∈ A, ((n : ℕ) : ℝ)⁻¹ = (r : ℝ)⁻¹ * ∑ m ∈ B, ((m : ℕ) : ℝ)⁻¹ := by
    rw [hB, Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have h1 : n = r * (n / r) := (Nat.mul_div_cancel' (hdvd n hn)).symm
    conv_lhs => rw [h1]
    push_cast
    exact mul_inv _ _
  -- every cofactor is `r.primeFactors`-factored
  have hBf : ∀ m ∈ B, m ∈ Nat.factoredNumbers r.primeFactors := by
    intro m hm
    rw [hB, Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    have hn0 := (hA n hn).1
    have hr' := (hA n hn).2
    rw [Nat.mem_factoredNumbers']
    intro p hp hpd
    have hpn : p ∣ n := hpd.trans (Nat.div_dvd_of_dvd (hdvd n hn))
    rw [← hr', primeFactors_rad]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
  -- finite part of the Euler sum
  have hle : ∑ m ∈ B, ((m : ℕ) : ℝ)⁻¹ ≤ ∏ p ∈ r.primeFactors with p.Prime, (1 - ((p : ℕ) : ℝ)⁻¹)⁻¹ := by
    have hH := hasSum_inv_factored r.primeFactors
    have := sum_le_hasSum (B.subtype (· ∈ Nat.factoredNumbers r.primeFactors))
      (fun i _ => by positivity) hH
    rwa [Finset.sum_subtype_of_mem (fun m : ℕ => ((m : ℕ) : ℝ)⁻¹) hBf] at this
  have hfilt : (r.primeFactors.filter (fun p => p.Prime)) = r.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [hfilt, Finset.prod_inv_distrib] at hle
  rw [hsumA, totient_real, mul_inv]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- `Σ_{n ≤ R} 1/n ≤ Σ_{r ≤ R} μ²(r)/φ(r)`. -/
theorem harmonic_le_sum_moebius_sq_div_totient (R : ℕ) :
    ∑ n ∈ Finset.Icc 1 R, ((n : ℕ) : ℝ)⁻¹ ≤
      ∑ r ∈ Finset.Icc 1 R, ((ArithmeticFunction.moebius r : ℝ)) ^ 2 / (Nat.totient r : ℝ) := by
  classical
  have hmaps : ∀ n ∈ Finset.Icc 1 R, rad n ∈ Finset.Icc 1 R := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨rad_pos n, (Nat.le_of_dvd (by omega) (rad_dvd n)).trans hn.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun r hr => ?_
  set A := (Finset.Icc 1 R).filter (fun n => rad n = r) with hAdef
  rcases A.eq_empty_or_nonempty with hAe | ⟨n₀, hn₀⟩
  · rw [hAe, Finset.sum_empty]; positivity
  have hsq : Squarefree r := by
    rw [hAdef, Finset.mem_filter] at hn₀
    exact hn₀.2 ▸ rad_squarefree n₀
  have hmu : ((ArithmeticFunction.moebius r : ℝ)) ^ 2 = 1 := by
    have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    exact_mod_cast this
  rw [hmu, one_div]
  refine fiber_bound r A fun n hn => ?_
  rw [hAdef, Finset.mem_filter, Finset.mem_Icc] at hn
  exact ⟨by omega, hn.2⟩

theorem log_succ_le_sum_aux (R : ℕ) :
    Real.log ((R : ℝ) + 1) ≤
      ∑ r ∈ Finset.Icc 1 R, ((ArithmeticFunction.moebius r : ℝ)) ^ 2 / (Nat.totient r : ℝ) := by
  have h1 := log_add_one_le_harmonic R
  rw [harmonic_eq_sum_Icc] at h1
  push_cast at h1
  exact h1.trans (harmonic_le_sum_moebius_sq_div_totient R)

end K4bAux
end LemmaK
end ZetaShell
