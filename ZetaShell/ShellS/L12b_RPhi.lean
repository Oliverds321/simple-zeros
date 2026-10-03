/-
L7_12c (3 Oct 2026): `r/φ(r) ≪ log log r` in the form used by Lemma 6a (lem:shell-6a, last line of the proof:
"Finally `r/φ(r) ≪ log log r`"): for `1 ≤ r ≤ e^{s₀}`, `s₀ ≥ 3`, `r/φ(r) ≤ C log s₀`.
Route: Mertens' first theorem (green: `Mertens.sum_mangoldt_div_eq_log`, ported from PrimeNumberTheoremAnd, no
`sorry`) gives `A(N) = Σ_{p≤N} log p/p ≤ log N + c₁`; discrete partial summation (an induction with the potential
`A(N)/log N + c₁(1/log 2 − 1/log N) + log log N − log log 2`, using `1 − u/v ≤ log(v/u)`) gives
`Σ_{p≤N} 1/p ≤ log log N + B₀`; then `r/φ(r) = Π_{p|r}(1 + 1/(p−1)) ≤ exp Σ_{p|r} 1/(p−1)`, the primes `p ≤ s₀`
contribute `≤ Σ_{p≤s₀} 1/p + Σ_n 1/(n(n−1)) ≤ log log s₀ + B₀ + 1`, and the at most `s₀/log s₀` primes `p > s₀`
dividing `r` contribute `≤ 2`.
-/
import Zeta23.FromPNTPlus.Mertens
import Mathlib

noncomputable section
open Finset

namespace ZetaShell
namespace ShellS

/-- `A(N) = Σ_{p ≤ N} log p / p`. -/
def L12bA (N : ℕ) : ℝ := ∑ n ∈ Icc 2 N, if n.Prime then Real.log n / n else 0

/-- `P(N) = Σ_{p ≤ N} 1/p`. -/
def L12bP (N : ℕ) : ℝ := ∑ n ∈ Icc 2 N, if n.Prime then (1 : ℝ) / n else 0

/-- Mertens' constant in green's form: `log 4 + 4`. -/
def L12bc1 : ℝ := Real.log 4 + 4

lemma L12bA_le (N : ℕ) (hN : 1 ≤ N) : L12bA N ≤ Real.log N + L12bc1 := by
  have hM := Mertens.sum_mangoldt_div_eq_log (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at hM
  have h1 : L12bA N ≤ ∑ d ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
    unfold L12bA
    have hsub : Icc 2 N ⊆ Ioc 0 N := by
      intro x hx; simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx ⊢; omega
    calc ∑ n ∈ Icc 2 N, (if n.Prime then Real.log n / n else 0)
        ≤ ∑ n ∈ Icc 2 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
          apply Finset.sum_le_sum; intro n _
          split_ifs with hp
          · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
          · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
  have h2 := (abs_le.mp hM).2
  unfold L12bc1; linarith

lemma L12bA_succ (N : ℕ) (hN : 2 ≤ N + 1) :
    L12bA (N + 1) = L12bA N + (if (N + 1).Prime then Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) else 0) := by
  unfold L12bA; rw [Finset.sum_Icc_succ_top hN]

lemma L12bP_succ (N : ℕ) (hN : 2 ≤ N + 1) :
    L12bP (N + 1) = L12bP N + (if (N + 1).Prime then (1 : ℝ) / ((N + 1 : ℕ) : ℝ) else 0) := by
  unfold L12bP; rw [Finset.sum_Icc_succ_top hN]

/-- discrete partial summation. -/
lemma L12bP_le_pot (N : ℕ) (hN : 2 ≤ N) :
    L12bP N ≤ L12bA N / Real.log N + L12bc1 * (1 / Real.log 2 - 1 / Real.log N)
      + Real.log (Real.log N) - Real.log (Real.log 2) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    simp only [L12bP, L12bA, Finset.Icc_self, Finset.sum_singleton, if_pos Nat.prime_two]
    push_cast
    field_simp
    ring_nf; norm_num
  | succ N hN ih =>
    have hN1 : 2 ≤ N + 1 := by omega
    rw [L12bP_succ N hN1, L12bA_succ N hN1]
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hL : 0 < Real.log N := Real.log_pos (by linarith)
    have hL' : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) := Real.log_le_log (by linarith) (by push_cast; linarith)
    have hL'0 : 0 < Real.log ((N + 1 : ℕ) : ℝ) := lt_of_lt_of_le hL hL'
    have hA := L12bA_le N (by omega)
    set L := Real.log N with hLdef
    set L' := Real.log ((N + 1 : ℕ) : ℝ) with hL'def
    set A := L12bA N with hAdef
    -- the new term
    have hterm : (if (N + 1).Prime then (1 : ℝ) / ((N + 1 : ℕ) : ℝ) else 0)
        = (if (N + 1).Prime then Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) else 0) / L' := by
      split_ifs
      · field_simp
        try exact hL'def
      · simp
    rw [hterm]
    set a := (if (N + 1).Prime then Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) else 0) with hadef
    -- key: (A − c₁)(1/L − 1/L') ≤ log L' − log L
    have hdiff : 0 ≤ 1 / L - 1 / L' := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hL hL'
    have hkey1 : (A - L12bc1) * (1 / L - 1 / L') ≤ L * (1 / L - 1 / L') :=
      mul_le_mul_of_nonneg_right (by linarith) hdiff
    have hkey2 : L * (1 / L - 1 / L') ≤ Real.log L' - Real.log L := by
      have h := Real.one_sub_inv_le_log_of_pos (show 0 < L' / L by positivity)
      rw [Real.log_div hL'0.ne' hL.ne', inv_div] at h
      have : L * (1 / L - 1 / L') = 1 - L / L' := by field_simp
      rw [this]; exact h
    have e1 : (A + a) / L' = A / L' + a / L' := add_div _ _ _
    have e2 : (A - L12bc1) * (1 / L - 1 / L') = A / L - A / L' - L12bc1 / L + L12bc1 / L' := by ring
    have e3 : L12bc1 * (1 / Real.log 2 - 1 / L) = L12bc1 / Real.log 2 - L12bc1 / L := by ring
    have e4 : L12bc1 * (1 / Real.log 2 - 1 / L') = L12bc1 / Real.log 2 - L12bc1 / L' := by ring
    rw [e1, e4]
    rw [e3] at ih
    linarith [ih, hkey1, hkey2, e2]

/-- the constant of Mertens' second theorem (upper bound). -/
def L12bB0 : ℝ := (2 * L12bc1 + 1) / Real.log 2

lemma L12bP_le (N : ℕ) (hN : 2 ≤ N) : L12bP N ≤ Real.log (Real.log N) + L12bB0 := by
  have h := L12bP_le_pot N hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hL : 0 < Real.log N := lt_of_lt_of_le hl2 hL2
  have hA := L12bA_le N (by omega)
  have hc1 : 0 ≤ L12bc1 := by unfold L12bc1; have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have h1 : L12bA N / Real.log N ≤ 1 + L12bc1 / Real.log 2 := by
    rw [div_le_iff₀ hL]
    have : L12bc1 / Real.log 2 * Real.log N ≥ L12bc1 := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hl2]; exact mul_le_mul_of_nonneg_left hL2 hc1
    nlinarith
  have h2 : L12bc1 * (1 / Real.log 2 - 1 / Real.log N) ≤ L12bc1 / Real.log 2 := by
    have : 0 ≤ 1 / Real.log N := by positivity
    have := mul_le_mul_of_nonneg_left (show 1 / Real.log 2 - 1 / Real.log N ≤ 1 / Real.log 2 by linarith) hc1
    rw [mul_one_div] at this; exact this
  have h3 : -Real.log (Real.log 2) ≤ 1 / Real.log 2 - 1 := by
    rw [← Real.log_inv, ← one_div]
    exact Real.log_le_sub_one_of_pos (by positivity)
  unfold L12bB0
  have e : (2 * L12bc1 + 1) / Real.log 2 = L12bc1 / Real.log 2 + L12bc1 / Real.log 2 + 1 / Real.log 2 := by ring
  rw [e]; linarith

/-- `Σ_{n=2}^{N} 1/(n(n−1)) ≤ 1`. -/
lemma L12b_sum_recip_sq (N : ℕ) : ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
  have key : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 2 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (N : ℝ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hN0 : (N : ℝ) ≠ 0 := by linarith
      have hN1 : (N : ℝ) + 1 ≠ 0 := by linarith
      push_cast
      have h1 : (N : ℝ) + 1 - 1 = N := by ring
      rw [h1]
      field_simp
      ring
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [key N h]
    have : 0 ≤ 1 / (N : ℝ) := by positivity
    linarith

/-- **`r/φ(r) ≤ C log s₀`** for `1 ≤ r ≤ e^{s₀}`, `s₀ ≥ 3`. -/
theorem L12b_rphi : ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ) (s₀ : ℝ), 1 ≤ r → 3 ≤ s₀ → (r : ℝ) ≤ Real.exp s₀ →
    (r : ℝ) / (Nat.totient r : ℝ) ≤ C * Real.log s₀ := by
  refine ⟨Real.exp (L12bB0 + 3), (Real.exp_pos _).le, ?_⟩
  intro r s₀ hr hs hrs
  set P := r.primeFactors with hP
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hp2 : ∀ p ∈ P, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  -- Euler's product
  have hφ : (Nat.totient r : ℝ) = r * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
    have h := Nat.totient_eq_mul_prod_factors r
    have h' := congrArg (fun x : ℚ => (x : ℝ)) h
    simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv] at h'
    exact h'
  have hprod_pos : 0 < ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_pos; intro p hp
    have := hp2 p hp
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hrat : (r : ℝ) / (Nat.totient r : ℝ) = ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) := by
    rw [hφ, div_mul_cancel_left₀ hr0.ne', ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl; intro p hp
    have := hp2 p hp
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  -- ≤ exp Σ 1/(p−1)
  have hexp : (r : ℝ) / (Nat.totient r : ℝ) ≤ Real.exp (∑ p ∈ P, 1 / ((p : ℝ) - 1)) := by
    rw [hrat, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp; have := hp2 p hp; have : 0 ≤ 1 / ((p : ℝ) - 1) := by apply div_nonneg <;> linarith
      linarith
    · intro p _; linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1))]
  -- split at y = ⌊s₀⌋
  set y := ⌊s₀⌋₊ with hy
  have hy3 : 3 ≤ y := Nat.le_floor (by exact_mod_cast hs)
  have hyr : (y : ℝ) ≤ s₀ := Nat.floor_le (by linarith)
  have hys : s₀ < (y : ℝ) + 1 := Nat.lt_floor_add_one s₀
  have hy3r : (3 : ℝ) ≤ y := by exact_mod_cast hy3
  have hls : 1 ≤ Real.log s₀ := by
    have he : Real.exp 1 ≤ s₀ := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) he; rwa [Real.log_exp] at this
  -- small primes
  have hsmall : ∑ p ∈ P.filter (fun p => p ≤ y), 1 / ((p : ℝ) - 1) ≤ Real.log (Real.log s₀) + L12bB0 + 1 := by
    have hsub : P.filter (fun p => p ≤ y) ⊆ Icc 2 y := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_Icc]
      exact ⟨(Nat.prime_of_mem_primeFactors hp.1).two_le, hp.2⟩
    have hsplit : ∀ p ∈ P.filter (fun p => p ≤ y), 1 / ((p : ℝ) - 1)
        = (if p.Prime then (1 : ℝ) / p else 0) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [if_pos (Nat.prime_of_mem_primeFactors hp.1)]
      have := hp2 p hp.1
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℝ) ≠ 0 := by linarith
      field_simp; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hA : ∑ p ∈ P.filter (fun p => p ≤ y), (if p.Prime then (1 : ℝ) / p else 0) ≤ L12bP y := by
      unfold L12bP
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n _ _; split_ifs <;> positivity
    have hB : ∑ p ∈ P.filter (fun p => p ≤ y), 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
      refine le_trans ?_ (L12b_sum_recip_sq y)
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n hn _
      rw [Finset.mem_Icc] at hn
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
      apply div_nonneg zero_le_one; nlinarith
    have hPy := L12bP_le y (by omega)
    have hll : Real.log (Real.log y) ≤ Real.log (Real.log s₀) := by
      have h1 : 0 < Real.log y := Real.log_pos (by linarith)
      exact Real.log_le_log h1 (Real.log_le_log (by linarith) hyr)
    linarith
  -- large primes
  have hlarge : ∑ p ∈ P.filter (fun p => ¬ p ≤ y), 1 / ((p : ℝ) - 1) ≤ 2 := by
    set P₂ := P.filter (fun p => ¬ p ≤ y) with hP₂
    have hge : ∀ p ∈ P₂, (y : ℝ) + 1 ≤ p := by
      intro p hp; rw [Finset.mem_filter] at hp
      have : y + 1 ≤ p := by omega
      exact_mod_cast this
    have hterm : ∀ p ∈ P₂, 1 / ((p : ℝ) - 1) ≤ 1 / (y : ℝ) := by
      intro p hp
      have := hge p hp
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have hcard : (P₂.card : ℝ) * Real.log s₀ ≤ s₀ := by
      have h1 : (y + 1) ^ P₂.card ≤ ∏ p ∈ P₂, p := by
        apply Finset.pow_card_le_prod; intro p hp; rw [Finset.mem_filter] at hp; omega
      have h2 : ∏ p ∈ P₂, p ≤ ∏ p ∈ P, p := by
        apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        intro p hp _; exact (Nat.prime_of_mem_primeFactors hp).one_lt.le
      have h3 : ∏ p ∈ P, p ≤ r := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd r)
      have h4 : (((y + 1) ^ P₂.card : ℕ) : ℝ) ≤ r := by exact_mod_cast h1.trans (h2.trans h3)
      push_cast at h4
      have h5 : Real.log (((y : ℝ) + 1) ^ P₂.card) ≤ Real.log r := Real.log_le_log (by positivity) h4
      rw [Real.log_pow] at h5
      have h6 : Real.log r ≤ s₀ := by
        have := Real.log_le_log hr0 hrs; rwa [Real.log_exp] at this
      have h7 : Real.log s₀ ≤ Real.log ((y : ℝ) + 1) := Real.log_le_log (by linarith) hys.le
      have h8 : (P₂.card : ℝ) * Real.log s₀ ≤ (P₂.card : ℝ) * Real.log ((y : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left h7 (Nat.cast_nonneg _)
      linarith
    calc ∑ p ∈ P₂, 1 / ((p : ℝ) - 1) ≤ ∑ p ∈ P₂, 1 / (y : ℝ) := Finset.sum_le_sum hterm
      _ = (P₂.card : ℝ) / y := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]
          have hc : (P₂.card : ℝ) ≤ s₀ := by nlinarith [Nat.cast_nonneg (α := ℝ) P₂.card]
          have : (P₂.card : ℝ) ≤ s₀ / Real.log s₀ := by rw [le_div_iff₀ (by linarith)]; exact hcard
          have : s₀ / Real.log s₀ ≤ s₀ := div_le_self (by linarith) hls
          linarith
  have hsum : ∑ p ∈ P.filter (fun p => p ≤ y), 1 / ((p : ℝ) - 1)
      + ∑ p ∈ P.filter (fun p => ¬ p ≤ y), 1 / ((p : ℝ) - 1) ≤ Real.log (Real.log s₀) + (L12bB0 + 3) := by
    linarith
  refine hexp.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ y)]
  calc Real.exp (∑ p ∈ P.filter (fun p => p ≤ y), 1 / ((p : ℝ) - 1)
        + ∑ p ∈ P.filter (fun p => ¬ p ≤ y), 1 / ((p : ℝ) - 1))
      ≤ Real.exp (Real.log (Real.log s₀) + (L12bB0 + 3)) := Real.exp_le_exp.mpr hsum
    _ = Real.exp (L12bB0 + 3) * Real.log s₀ := by
        rw [Real.exp_add, Real.exp_log (by linarith)]; ring

end ShellS
end ZetaShell
