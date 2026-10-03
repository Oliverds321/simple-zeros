/-
L711_MuSqPhi (L7_11, 28 Sep 2026, round 2): SHARED lemma, imports only Mathlib. Namespace `ZetaShell.MuSqPhi`.

* `musq_phi_sum_le`: `∃ C ≥ 0, ∀ y ≥ 1, Σ_{1≤e≤⌊y⌋} |μ(e)|/φ(e) ≤ C (1 + log y)`.
* `musq_phi_tau_sum_le`: `∃ C ≥ 0, ∀ y ≥ 1, Σ_{1≤e≤⌊y⌋} |μ(e)|/φ(e) · τ(e) ≤ C (1 + log y)²` (τ = `e.divisors.card`).

Route (L8_8 second reader A, step 6): `n/φ(n) = Σ_{d|n} μ(d)²/φ(d)` (`sum_musq_div_totient`, both sides
multiplicative), so `1/φ(n) = Σ_{dm=n} (μ(d)²/(dφ(d)))·(1/m)` and the sum is at most
`(Σ_{d≤N} μ(d)²/(dφ(d)))·(Σ_{m≤N} 1/m)`; the first factor is at most `(Σ_n n⁻²)²` since `1/φ(d) ≤ τ(d)/d`
(`le_totient_mul_card_divisors`) and `Σ_{d≤N} τ(d)/d² ≤ (Σ n⁻²)²`. The τ-weighted form uses `τ(dm) ≤ τ(d)τ(m)`,
`Σ_{m≤N} τ(m)/m ≤ (1 + log N)²` and `Σ_{d≤N} τ(d)²/d² ≤ (Σ n⁻²)⁴`.
-/
import Mathlib

noncomputable section
open scoped BigOperators Pointwise
open ArithmeticFunction

namespace ZetaShell
namespace MuSqPhi

local notation "μR" => ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
local notation "ζR" => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
local notation "idR" => ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

/-! ### Divisor-sum swap -/

theorem divisor_sum_swap (F : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, F d (n / d)
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), F d m := by
  rw [Finset.sum_comm' (t' := Finset.Icc 1 N) (s' := fun d => (Finset.Icc 1 N).filter (fun n => d ∣ n))]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    symm
    apply Finset.sum_nbij' (fun m => d * m) (fun n => n / d)
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith [hm.1], ?_⟩, dvd_mul_right d m⟩
      have := Nat.mul_le_of_le_div d m N hm.2
      linarith [this, Nat.mul_comm m d]
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      obtain ⟨⟨hn1, hnN⟩, hdn⟩ := hn
      obtain ⟨c, rfl⟩ := hdn
      rw [Nat.mul_div_cancel_left c (by omega)]
      constructor
      · rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at hn1
        · exact h
      · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hnN)
    · intro m _
      exact Nat.mul_div_cancel_left m (by omega)
    · intro n hn
      rw [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      rw [Nat.mul_div_cancel_left m (by omega)]
  · intro n d
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdn, _⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
      have hdN : d ≤ N := le_trans (Nat.le_of_dvd (by omega) hdn) hnN
      exact ⟨⟨⟨hn1, hnN⟩, hdn⟩, hd1, hdN⟩
    · rintro ⟨⟨⟨hn1, hnN⟩, hdn⟩, _, _⟩
      exact ⟨⟨hn1, hnN⟩, hdn, by omega⟩

/-- the swap, bounded by a product of two partial sums. -/
theorem divisor_sum_le_mul (F : ℕ → ℕ → ℝ) (u v : ℕ → ℝ) (hu : ∀ a, 0 ≤ u a) (hv : ∀ b, 0 ≤ v b)
    (hF : ∀ a b, 1 ≤ a → 1 ≤ b → F a b ≤ u a * v b) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, F d (n / d)
      ≤ (∑ a ∈ Finset.Icc 1 N, u a) * ∑ b ∈ Finset.Icc 1 N, v b := by
  rw [divisor_sum_swap, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a ha
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  rw [Finset.mul_sum]
  calc ∑ m ∈ Finset.Icc 1 (N / a), F a m ≤ ∑ m ∈ Finset.Icc 1 (N / a), u a * v m :=
        Finset.sum_le_sum (fun m hm => hF a m ha1 (Finset.mem_Icc.mp hm).1)
    _ ≤ ∑ m ∈ Finset.Icc 1 N, u a * v m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          simp only [Finset.mem_Icc] at hb ⊢
          exact ⟨hb.1, le_trans hb.2 (Nat.div_le_self N a)⟩
        · intro b _ _; exact mul_nonneg (hu a) (hv b)

/-! ### Elementary bounds -/

theorem sum_inv_le (N : ℕ) : ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / a ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

theorem sum_inv_sq_le (N : ℕ) : ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / (a : ℝ) ^ 2 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
  (Real.summable_one_div_nat_pow.mpr one_lt_two).sum_le_tsum _ (fun i _ => by positivity)

theorem card_divisors_mul_le (m n : ℕ) :
    ((m * n).divisors.card : ℝ) ≤ (m.divisors.card : ℝ) * (n.divisors.card : ℝ) := by
  rw [Nat.divisors_mul]
  exact_mod_cast Finset.card_mul_le

/-- `n ≤ φ(n)·τ(n)` for `n ≥ 1`. -/
theorem le_totient_mul_card_divisors (n : ℕ) (hn : n ≠ 0) : n ≤ Nat.totient n * n.divisors.card := by
  rw [Nat.totient_eq_prod_factorization hn, Nat.card_divisors hn]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  unfold Finsupp.prod
  rw [Nat.support_factorization, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun p _ => Nat.zero_le _)
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hk : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
  obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [hk']
  show p ^ (k.succ) ≤ p ^ (k.succ - 1) * (p - 1) * (k.succ + 1)
  rw [Nat.succ_sub_one, pow_succ]
  have h2 := hpp.two_le
  have hpk : p ≤ (p - 1) * (k + 1 + 1) := by
    calc p ≤ (p - 1) * 2 := by omega
      _ ≤ (p - 1) * (k + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
  calc p ^ k * p ≤ p ^ k * ((p - 1) * (k + 1 + 1)) := Nat.mul_le_mul_left _ hpk
    _ = p ^ k * (p - 1) * (Nat.succ k + 1) := by rw [Nat.succ_eq_add_one]; ring

theorem inv_totient_le (n : ℕ) (hn : n ≠ 0) :
    1 / (Nat.totient n : ℝ) ≤ (n.divisors.card : ℝ) / n := by
  have h := le_totient_mul_card_divisors n hn
  have hφ : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [div_le_div_iff₀ hφ hn0, one_mul]
  have h' : n ≤ n.divisors.card * Nat.totient n := by rw [Nat.mul_comm]; exact h
  exact_mod_cast h'

/-- `Σ_{d≤N} τ(d)/d² ≤ (Σ n⁻²)²`. -/
theorem sum_tau_div_sq_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) / (d : ℝ) ^ 2 ≤ (∑' n : ℕ, 1 / (n : ℝ) ^ 2) ^ 2 := by
  set F : ℕ → ℕ → ℝ := fun a b => 1 / ((a : ℝ) * b) ^ 2 with hF
  have h1 : ∀ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) / (d : ℝ) ^ 2 = ∑ a ∈ d.divisors, F a (d / a) := by
    intro d _
    rw [show (d.divisors.card : ℝ) / (d : ℝ) ^ 2 = ∑ a ∈ d.divisors, 1 / (d : ℝ) ^ 2 by
      rw [Finset.sum_const, nsmul_eq_mul]; ring]
    apply Finset.sum_congr rfl
    intro a ha
    have hadvd := Nat.dvd_of_mem_divisors ha
    have hmul : (a : ℝ) * ((d / a : ℕ) : ℝ) = d := by exact_mod_cast Nat.mul_div_cancel' hadvd
    simp only [hF, hmul]
  rw [Finset.sum_congr rfl h1]
  refine (divisor_sum_le_mul F (fun n => 1 / (n : ℝ) ^ 2) (fun n => 1 / (n : ℝ) ^ 2)
    (fun a => by positivity) (fun b => by positivity) (fun a b _ _ => le_of_eq ?_) N).trans ?_
  · simp only [hF]; rw [mul_pow, one_div_mul_one_div]
  · rw [sq]
    have h := sum_inv_sq_le N
    have h0 : 0 ≤ ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / (a : ℝ) ^ 2 := Finset.sum_nonneg (fun a _ => by positivity)
    exact mul_le_mul h h h0 (h0.trans h)

/-- `Σ_{m≤N} τ(m)/m ≤ (1 + log N)²`. -/
theorem sum_tau_div_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (m.divisors.card : ℝ) / m ≤ (1 + Real.log N) ^ 2 := by
  set F : ℕ → ℕ → ℝ := fun a b => 1 / ((a : ℝ) * b) with hF
  have h1 : ∀ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) / d = ∑ a ∈ d.divisors, F a (d / a) := by
    intro d _
    rw [show (d.divisors.card : ℝ) / (d : ℝ) = ∑ a ∈ d.divisors, 1 / (d : ℝ) by
      rw [Finset.sum_const, nsmul_eq_mul]; ring]
    apply Finset.sum_congr rfl
    intro a ha
    have hadvd := Nat.dvd_of_mem_divisors ha
    have hmul : (a : ℝ) * ((d / a : ℕ) : ℝ) = d := by exact_mod_cast Nat.mul_div_cancel' hadvd
    simp only [hF, hmul]
  rw [Finset.sum_congr rfl h1]
  refine (divisor_sum_le_mul F (fun n => 1 / (n : ℝ)) (fun n => 1 / (n : ℝ))
    (fun a => by positivity) (fun b => by positivity) (fun a b _ _ => le_of_eq ?_) N).trans ?_
  · simp only [hF]; rw [one_div_mul_one_div]
  · rw [sq]
    have h := sum_inv_le N
    have h0 : 0 ≤ ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / a := Finset.sum_nonneg (fun a _ => by positivity)
    exact mul_le_mul h h h0 (h0.trans h)

/-- `Σ_{d≤N} τ(d)²/d² ≤ (Σ n⁻²)⁴`. -/
theorem sum_tau_sq_div_sq_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) ^ 2 / (d : ℝ) ^ 2 ≤ ((∑' n : ℕ, 1 / (n : ℝ) ^ 2) ^ 2) ^ 2 := by
  set F : ℕ → ℕ → ℝ := fun a b => (a.divisors.card : ℝ) * b.divisors.card / ((a : ℝ) * b) ^ 2 with hF
  have h1 : ∀ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) ^ 2 / (d : ℝ) ^ 2 ≤ ∑ a ∈ d.divisors, F a (d / a) := by
    intro d _
    rw [show (d.divisors.card : ℝ) ^ 2 / (d : ℝ) ^ 2
        = ∑ a ∈ d.divisors, (d.divisors.card : ℝ) / (d : ℝ) ^ 2 by
      rw [Finset.sum_const, nsmul_eq_mul]; ring]
    apply Finset.sum_le_sum
    intro a ha
    have hadvd := Nat.dvd_of_mem_divisors ha
    have hd : a * (d / a) = d := Nat.mul_div_cancel' hadvd
    have hmul : (a : ℝ) * ((d / a : ℕ) : ℝ) = d := by exact_mod_cast hd
    have hτ := card_divisors_mul_le a (d / a)
    rw [hd] at hτ
    simp only [hF, hmul]
    exact div_le_div_of_nonneg_right hτ (by positivity)
  refine (Finset.sum_le_sum h1).trans ?_
  refine (divisor_sum_le_mul F (fun n => (n.divisors.card : ℝ) / (n : ℝ) ^ 2)
    (fun n => (n.divisors.card : ℝ) / (n : ℝ) ^ 2)
    (fun a => by positivity) (fun b => by positivity) (fun a b _ _ => le_of_eq ?_) N).trans ?_
  · simp only [hF]; rw [mul_pow, mul_div_mul_comm]
  · rw [sq]
    have h := sum_tau_div_sq_le N
    have h0 : 0 ≤ ∑ a ∈ Finset.Icc 1 N, (a.divisors.card : ℝ) / (a : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun a _ => by positivity)
    exact mul_le_mul h h h0 (h0.trans h)

/-! ### The identity `n/φ(n) = Σ_{d|n} μ(d)²/φ(d)` -/

def totR : ArithmeticFunction ℝ := ⟨fun n => (Nat.totient n : ℝ), by simp⟩

theorem totR_apply (n : ℕ) : totR n = (Nat.totient n : ℝ) := rfl

theorem totR_mult : IsMultiplicative totR :=
  ⟨by simp [totR_apply], fun {m n} h => by simp only [totR_apply]; rw [Nat.totient_mul h]; push_cast; ring⟩

def gR : ArithmeticFunction ℝ := pdiv (pmul μR μR) totR

theorem gR_apply (n : ℕ) : gR n = ((moebius n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ) := by
  simp only [gR, pdiv_apply, pmul_apply, intCoe_apply, totR_apply, sq]

theorem gR_mult : IsMultiplicative gR :=
  (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pdiv totR_mult

theorem zeta_mul_gR : ζR * gR = pdiv idR totR := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_zeta.natCast.mul gR_mult) _
    (isMultiplicative_id.natCast.pdiv totR_mult)]
  intro p i hp
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp, pdiv_apply]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rcases i with _ | m
  · simp [gR_apply, totR_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ k ∈ Finset.range m, gR (p ^ (k + 1 + 1)) = 0 := by
    intro k _
    rw [gR_apply, moebius_apply_prime_pow hp (by omega)]
    simp
  rw [Finset.sum_eq_zero hz, gR_apply, gR_apply, pow_zero, moebius_apply_one, pow_one,
    moebius_apply_prime hp, natCoe_apply, totR_apply, id_apply, Nat.totient_prime hp,
    Nat.totient_prime_pow hp (by omega), Nat.totient_one]
  have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp.one_le]; simp
  push_cast [hsub]
  try simp only [Nat.add_sub_cancel]
  rw [pow_succ]
  have hpm : (p : ℝ) ^ m ≠ 0 := pow_ne_zero _ hp0
  field_simp
  ring

theorem sum_musq_div_totient (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ) = (n : ℝ) / (Nat.totient n : ℝ) := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n) zeta_mul_gR
  simp only [coe_zeta_mul_apply, pdiv_apply, natCoe_apply, id_apply, totR_apply] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro d _
  rw [gR_apply]

/-! ### The two shared statements -/

theorem abs_moebius_div_totient_le (n : ℕ) :
    |((moebius n : ℤ) : ℝ)| / (Nat.totient n : ℝ) ≤ 1 / (Nat.totient n : ℝ) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one

/-- `1/φ(n) = Σ_{d|n} (μ(d)²/(dφ(d)))·(1/(n/d))` for `n ≥ 1`. -/
theorem inv_totient_eq_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    1 / (Nat.totient n : ℝ)
      = ∑ d ∈ n.divisors, (fun a b : ℕ => ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a * (1 / (b : ℝ)))
          d (n / d) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h := sum_musq_div_totient n hn
  have e : 1 / (Nat.totient n : ℝ) = (1 / (n : ℝ)) * ((n : ℝ) / (Nat.totient n : ℝ)) := by
    field_simp
  rw [e, ← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by exact_mod_cast Nat.mul_div_cancel' hdvd
  have hd0 : (d : ℝ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hd; positivity
  have hm0 : ((n / d : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hn0 hmul.symm
  simp only
  rw [← hmul]
  field_simp

/-- **Shared statement 1.** `Σ_{1≤e≤⌊y⌋} |μ(e)|/φ(e) ≤ C (1 + log y)` for `y ≥ 1`, with `C = (Σ n⁻²)²`. -/
theorem musq_phi_sum_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |((moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) ≤ C * (1 + Real.log y) := by
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ 2 with hZ
  refine ⟨Z ^ 2, by positivity, fun y hy => ?_⟩
  set N := ⌊y⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hy)
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hlog : Real.log N ≤ Real.log y := Real.log_le_log (by exact_mod_cast hN1) hNy
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have h1 : ∑ e ∈ Finset.Icc 1 N, |((moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1 N, 1 / (Nat.totient e : ℝ) :=
    Finset.sum_le_sum (fun e _ => abs_moebius_div_totient_le e)
  have h2 : ∑ e ∈ Finset.Icc 1 N, 1 / (Nat.totient e : ℝ)
      = ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ e.divisors,
          (fun a b : ℕ => ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a * (1 / (b : ℝ))) d (e / d) := by
    apply Finset.sum_congr rfl
    intro e he
    exact inv_totient_eq_divisor_sum e (by rw [Finset.mem_Icc] at he; omega)
  have hg : ∀ a : ℕ, 0 ≤ ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a := fun a => by positivity
  have h3 := divisor_sum_le_mul
    (fun a b : ℕ => ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a * (1 / (b : ℝ)))
    (fun a => ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a) (fun b => 1 / (b : ℝ))
    hg (fun b => by positivity) (fun a b _ _ => le_refl _) N
  have h4 : ∑ a ∈ Finset.Icc 1 N, ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a ≤ Z ^ 2 := by
    refine le_trans (Finset.sum_le_sum (fun a ha => ?_)) (sum_tau_div_sq_le N)
    have ha0 : a ≠ 0 := by rw [Finset.mem_Icc] at ha; omega
    have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha0
    have hμ : ((moebius a : ℤ) : ℝ) ^ 2 ≤ 1 := by
      have : |((moebius a : ℤ) : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
      nlinarith [abs_nonneg ((moebius a : ℤ) : ℝ), sq_abs ((moebius a : ℤ) : ℝ)]
    have hφ := inv_totient_le a ha0
    calc ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a ≤ 1 / (Nat.totient a : ℝ) / a := by
          apply div_le_div_of_nonneg_right _ haR.le
          exact div_le_div_of_nonneg_right hμ (by positivity)
      _ ≤ (a.divisors.card : ℝ) / a / a := div_le_div_of_nonneg_right hφ haR.le
      _ = (a.divisors.card : ℝ) / (a : ℝ) ^ 2 := by field_simp
  have h5 := sum_inv_le N
  have h6 := mul_le_mul h4 h5 (Finset.sum_nonneg (fun b _ => by positivity)) (by positivity)
  rw [h2] at h1
  calc ∑ e ∈ Finset.Icc 1 N, |((moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) ≤ Z ^ 2 * (1 + Real.log N) :=
        h1.trans (h3.trans h6)
    _ ≤ Z ^ 2 * (1 + Real.log y) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

/-- **Shared statement 2.** `Σ_{1≤e≤⌊y⌋} |μ(e)|/φ(e)·τ(e) ≤ C (1 + log y)²` for `y ≥ 1`, with `C = (Σ n⁻²)⁴`. -/
theorem musq_phi_tau_sum_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |((moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) * (e.divisors.card : ℝ)
      ≤ C * (1 + Real.log y) ^ 2 := by
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ 2 with hZ
  refine ⟨(Z ^ 2) ^ 2, by positivity, fun y hy => ?_⟩
  set N := ⌊y⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hy)
  have hNy : (N : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hlog : Real.log N ≤ Real.log y := Real.log_le_log (by exact_mod_cast hN1) hNy
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have h1 : ∀ e ∈ Finset.Icc 1 N, |((moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) * (e.divisors.card : ℝ)
      ≤ ∑ d ∈ e.divisors, (fun a b : ℕ =>
          ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a * (a.divisors.card : ℝ)
            * ((b.divisors.card : ℝ) / b)) d (e / d) := by
    intro e he
    have he0 : e ≠ 0 := by rw [Finset.mem_Icc] at he; omega
    have hτ0 : (0 : ℝ) ≤ (e.divisors.card : ℝ) := by positivity
    calc |((moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) * (e.divisors.card : ℝ)
        ≤ 1 / (Nat.totient e : ℝ) * (e.divisors.card : ℝ) :=
          mul_le_mul_of_nonneg_right (abs_moebius_div_totient_le e) hτ0
      _ = ∑ d ∈ e.divisors, ((moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ) / d
            * (1 / ((e / d : ℕ) : ℝ)) * (e.divisors.card : ℝ) := by
          rw [inv_totient_eq_divisor_sum e he0, Finset.sum_mul]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro d hd
          have hdvd := Nat.dvd_of_mem_divisors hd
          have hde : d * (e / d) = e := Nat.mul_div_cancel' hdvd
          have hτ := card_divisors_mul_le d (e / d)
          rw [hde] at hτ
          calc ((moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ) / d * (1 / ((e / d : ℕ) : ℝ))
                * (e.divisors.card : ℝ)
              ≤ ((moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ) / d * (1 / ((e / d : ℕ) : ℝ))
                * ((d.divisors.card : ℝ) * ((e / d).divisors.card : ℝ)) :=
                mul_le_mul_of_nonneg_left hτ (by positivity)
            _ = ((moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ) / d * (d.divisors.card : ℝ)
                * (((e / d).divisors.card : ℝ) / ((e / d : ℕ) : ℝ)) := by ring
  refine (Finset.sum_le_sum h1).trans ?_
  have hu : ∀ a : ℕ, 0 ≤ ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a * (a.divisors.card : ℝ) :=
    fun a => by positivity
  refine (divisor_sum_le_mul _
    (fun a => ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a * (a.divisors.card : ℝ))
    (fun b => (b.divisors.card : ℝ) / b) hu (fun b => by positivity) (fun a b _ _ => le_refl _) N).trans ?_
  have h4 : ∑ a ∈ Finset.Icc 1 N, ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a * (a.divisors.card : ℝ)
      ≤ (Z ^ 2) ^ 2 := by
    refine le_trans (Finset.sum_le_sum (fun a ha => ?_)) (sum_tau_sq_div_sq_le N)
    have ha0 : a ≠ 0 := by rw [Finset.mem_Icc] at ha; omega
    have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha0
    have hμ : ((moebius a : ℤ) : ℝ) ^ 2 ≤ 1 := by
      have : |((moebius a : ℤ) : ℝ)| ≤ 1 := by rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
      nlinarith [abs_nonneg ((moebius a : ℤ) : ℝ), sq_abs ((moebius a : ℤ) : ℝ)]
    have hφ := inv_totient_le a ha0
    have hτ0 : (0 : ℝ) ≤ (a.divisors.card : ℝ) := by positivity
    calc ((moebius a : ℤ) : ℝ) ^ 2 / (Nat.totient a : ℝ) / a * (a.divisors.card : ℝ)
        ≤ 1 / (Nat.totient a : ℝ) / a * (a.divisors.card : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hτ0
          apply div_le_div_of_nonneg_right _ haR.le
          exact div_le_div_of_nonneg_right hμ (by positivity)
      _ ≤ (a.divisors.card : ℝ) / a / a * (a.divisors.card : ℝ) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hφ haR.le) hτ0
      _ = (a.divisors.card : ℝ) ^ 2 / (a : ℝ) ^ 2 := by field_simp
  have h5 := sum_tau_div_le N
  have h6 := mul_le_mul h4 h5 (Finset.sum_nonneg (fun b _ => by positivity)) (by positivity)
  refine h6.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : 1 + Real.log N ≤ 1 + Real.log y := by linarith
  exact pow_le_pow_left₀ (by linarith) this 2

end MuSqPhi
end ZetaShell
