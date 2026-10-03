/-
A2P_LineSumCore (L7_8c, cloud, 3 Oct 2026): the proof of the sub-node `line_sum_asymp` of Lemma P
(lem:shell-P, sec_shell.tex l.357–386), written against Mathlib alone (plus the Mathlib-only library modules
`L711_MuSqPhi`, `A2P_S2_ConvSum` and the trunk's `ZetaQ.Normalisation`), so that `A2P_LineProfile` can import it
without an import cycle. The coefficients are restated in closed form (`EcoefPl`, `EcoefQp`, `PiEPl`, `PiEQp`,
`Pi0X`, the weights `wSharp`, `wDyadic`, `wWeighted`); they are definitionally the library's
`Ecoef k`, `PiE k`, `Pi0plain`, `Fam.w` (checked by the three `exact`s in `A2P_LineProfile.line_sum_asymp`).

Route (L7_11's R2.4, items 1–5):
1. `φ(j) 𝔈_{j,r}(e) = K j ∏_{p|j} (1 + g(p))` with `K = 𝔈_{1,r}(e)` (`lsc_factor_pl`, `lsc_factor_qp`), so
   `φ(j)𝔈 = K j (1 ⋆ ν)(j)`, `ν(f) = μ²(f) ∏_{p|f} g(p)`, `|g(p)| ≤ 1` (`p | e`), `≤ 2/p` (`p ∤ e`).
2. `sum_mul_conv_approx`: `Σ_{j≤N} j(1⋆ν)(j) = (N²/2) Σ_{f≤N} ν(f)/f + O(N Σ_{f≤N}|ν(f)|)`.
3. `|ν(f)| ≤ Σ_{d|f, d|e} τ(f/d)/(f/d)`: `Σ_{f≤N}|ν(f)| ≤ τ(e)(1+log N)²`, `Σ_{f>N}|ν(f)|/f ≤ 8τ(e)(1+log N)/N`.
4. Euler product: `K Σ_f ν(f)/f = Π(e)` (`lsc_euler_pl`, `lsc_euler_qp`); `|K| ≤ e⁴`.
5. Partial summation against the three weights (L7_11's `L711_LineSumRed` draft, finished).
-/
import Mathlib
import ZetaShell.Lemma2.L711_MuSqPhi
import ZetaShell.Lemma2.A2P_S2_ConvSum
import ZetaQ.Normalisation

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-! ### Generic tools -/

theorem lsc_hasProd_sqfree (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsq : ∀ p k : ℕ, p.Prime → 2 ≤ k → f (p ^ k) = 0)
    (hsum : Summable (fun n => ‖f n‖)) :
    HasProd (fun p : Nat.Primes => 1 + f p) (∑' n, f n) := by
  have h := EulerProduct.eulerProduct_hasProd hf1 hmul hsum hf0
  have hloc : (fun p : Nat.Primes => ∑' e, f ((p : ℕ) ^ e)) = (fun p : Nat.Primes => 1 + f p) := by
    funext p
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ, hf1]
    · intro e he
      simp only [Finset.mem_range, not_lt] at he
      exact hsq p e p.2 he
  rwa [hloc] at h

theorem lsc_nf_toFinset (n : ℕ) :
    (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
  rw [Nat.factors_eq]
  rfl

/-- the finite Euler product over the squarefree divisors. -/
theorem lsc_divsum (g : ℕ → ℝ) (m : ℕ) (hm0 : m ≠ 0) :
    ∑ u ∈ m.divisors, (if Squarefree u then ∏ p ∈ u.primeFactors, g p else 0)
      = ∏ p ∈ m.primeFactors, (1 + g p) := by
  rw [← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hm0, lsc_nf_toFinset, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t ht
  have htP : t ⊆ m.primeFactors := Finset.mem_powerset.mp ht
  have htp : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (htP hp)
  have hval : t.val.prod = ∏ p ∈ t, p := by simp
  rw [hval, Nat.primeFactors_prod htp]

/-- a finite modification of an Euler product. -/
theorem lsc_hasProd_dvd (m : ℕ) (hm : m ≠ 0) (c : ℕ → ℝ) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ m then c p else 1) (∏ p ∈ m.primeFactors, c p) := by
  set c' : ℕ → ℝ := fun n => if n ∣ m then c n else 1 with hc'
  have h : HasProd (fun p : Nat.Primes => c' p)
      (∏ p ∈ (m.primeFactors.subtype Nat.Prime : Finset Nat.Primes), c' p) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    have hpn : ¬ (p : ℕ) ∣ m := fun hd =>
      hp (Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.2, hd, hm⟩))
    simp only [hc', if_neg hpn]
  rw [Finset.prod_subtype_eq_prod_filter (f := c'), Finset.filter_true_of_mem
    (fun p hp => Nat.prime_of_mem_primeFactors hp)] at h
  have e : ∏ p ∈ m.primeFactors, c' p = ∏ p ∈ m.primeFactors, c p := by
    apply Finset.prod_congr rfl
    intro p hp
    simp only [hc', if_pos (Nat.dvd_of_mem_primeFactors hp)]
  rw [e] at h
  exact h

theorem lsc_inv_sq_tail (L M : ℕ) (hL : 1 ≤ L) :
    ∑ b ∈ Finset.Ioc L M, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 1 / L := by
  have key : ∀ k : ℕ, ∑ b ∈ Finset.Ioc L (L + k), (1 : ℝ) / (b : ℝ) ^ 2 ≤ 1 / L - 1 / ((L + k : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show L + (k + 1) = (L + k) + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
      have hx : (1 : ℝ) ≤ ((L + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ L + k)
      set x : ℝ := ((L + k : ℕ) : ℝ) with hxdef
      have hc : (((L + k + 1 : ℕ)) : ℝ) = x + 1 := by rw [hxdef]; push_cast; ring
      rw [hc]
      have h2 : 1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
        have e : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by field_simp; ring
        rw [e]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      linarith
  by_cases hM : L ≤ M
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
    have h := key k
    have : (0 : ℝ) ≤ 1 / ((L + k : ℕ) : ℝ) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity

theorem lsc_inv_sq_le_two (X : ℕ) : ∑ b ∈ Finset.Icc 1 X, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  have e : Finset.Icc 1 X = insert 1 (Finset.Ioc 1 X) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [e, Finset.sum_insert (by simp)]
  have := lsc_inv_sq_tail 1 X le_rfl
  norm_num at this ⊢
  linarith

/-- generic tail: from uniform bounds on the finite tails to the bound on the full tail. -/
theorem lsc_tail (a : ℕ → ℝ) (A B : ℝ) (hA : HasSum a A) (ha0 : a 0 = 0) (N : ℕ)
    (hB : ∀ M, N ≤ M → ∑ e ∈ Finset.Ioc N M, |a e| ≤ B) :
    |∑ e ∈ Finset.Icc 1 N, a e - A| ≤ B := by
  have hS := hA.tendsto_sum_nat
  have key : ∀ M ≥ N, |∑ e ∈ Finset.range (M + 1), a e - ∑ e ∈ Finset.Icc 1 N, a e| ≤ B := by
    intro M hM
    have e2 := Finset.sum_Ioc_consecutive a (Nat.zero_le N) hM
    have i1 : Finset.range (M + 1) = insert 0 (Finset.Ioc 0 M) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
    have i2 : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e1 : ∑ e ∈ Finset.range (M + 1), a e = ∑ e ∈ Finset.Ioc 0 M, a e := by
      rw [i1, Finset.sum_insert (by simp), ha0, zero_add]
    rw [e1, i2, ← e2, add_sub_cancel_left]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (hB M hM)
  have hlim : Filter.Tendsto
      (fun M : ℕ => |∑ e ∈ Finset.range (M + 1), a e - ∑ e ∈ Finset.Icc 1 N, a e|)
      Filter.atTop (nhds |A - ∑ e ∈ Finset.Icc 1 N, a e|) :=
    ((hS.comp (Filter.tendsto_add_atTop_nat 1)).sub_const _).abs
  have := le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨N, key⟩)
  rw [abs_sub_comm]
  exact this

/-- `2^{ω(n)} ≤ τ(n)`, in the form `2^{#primeFactors}`. -/
theorem lsc_two_pow_card_le (n : ℕ) (hn : n ≠ 0) :
    (2 : ℝ) ^ n.primeFactors.card ≤ (n.divisors.card : ℝ) := by
  have h : (n.primeFactors.powerset).card ≤ n.divisors.card := by
    apply Finset.card_le_card_of_injOn (fun t => ∏ p ∈ t, p)
    · intro t ht
      have htP : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
      rw [Finset.mem_coe, Nat.mem_divisors]
      refine ⟨?_, hn⟩
      exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ htP) (Nat.prod_primeFactors_dvd n)
    · intro t ht t' ht' heq
      have htp : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
      have htp' : ∀ p ∈ t', p.Prime :=
        fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht' hp)
      have := congrArg Nat.primeFactors heq
      simp only at this
      rwa [Nat.primeFactors_prod htp, Nat.primeFactors_prod htp'] at this
  rw [Finset.card_powerset] at h
  exact_mod_cast h

theorem lsc_sum_Icc_one_eq_range (g : ℕ → ℝ) (n : ℕ) :
    ∑ q ∈ Finset.Icc 1 n, g q = ∑ q ∈ Finset.range (n + 1), g q - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (n + 1)]
    ring

theorem lsc_abel_range (f a : ℕ → ℝ) (n : ℕ) :
    ∑ q ∈ Finset.range n, f q * a q
      = f n * (∑ q ∈ Finset.range n, a q)
        - ∑ k ∈ Finset.range n, (f (k + 1) - f k) * ∑ q ∈ Finset.range (k + 1), a q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ]
    ring

theorem lsc_sum_range_sq (n : ℕ) :
    ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 = ((n : ℝ) - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem lsc_sum_range_cube (n : ℕ) :
    ∑ k ∈ Finset.range n, (k : ℝ) ^ 3 = (((n : ℝ) - 1) * n) ^ 2 / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `∏_p (1 − p⁻²) = 6/π²`. -/
theorem lsc_m2 : HasProd (fun p : Nat.Primes => 1 - 1 / ((p : ℕ) : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  set m2 : ℕ → ℝ := fun e => ((ArithmeticFunction.moebius e : ℤ) : ℝ) / (e : ℝ) ^ 2 with hm2
  have hb : ∀ e, |m2 e| ≤ 1 / (e : ℝ) ^ 2 := by
    intro e
    simp only [hm2]
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) ^ 2)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h := lsc_hasProd_sqfree m2 (by simp [hm2]) (by simp [hm2])
    (fun {m n} hmn => by
      simp only [hm2]
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
      push_cast; ring)
    (fun p k hp hk => by
      simp only [hm2]
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
      simp)
    (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hb n)
      (Real.summable_one_div_nat_pow.mpr one_lt_two))
  have hs : ∑' n, m2 n = 6 / Real.pi ^ 2 := ZetaQ.Normalisation.N2.hasSum_mu_sq.tsum_eq
  rw [hs] at h
  have hf : (fun p : Nat.Primes => 1 + m2 p) = (fun p : Nat.Primes => 1 - 1 / ((p : ℕ) : ℝ) ^ 2) := by
    funext p
    simp only [hm2]
    rw [ArithmeticFunction.moebius_apply_prime p.2]
    push_cast; ring
  rwa [hf] at h

/-- `Π₀ = ∏_p (1 − 2/p² + 1/p³)` (the body of the library's `Pi0plain`). -/
def Pi0X : ℝ := ∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3)

theorem lsc_Pi0 :
    HasProd (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3)) Pi0X := by
  have hs : Summable (fun n : ℕ => 3 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 3
  have hsP : Summable (fun p : Nat.Primes => 3 * (1 / ((p : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective Subtype.val_injective
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖(-(2 / ((p : ℕ) : ℝ) ^ 2) + 1 / ((p : ℕ) : ℝ) ^ 3)‖) := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hsP
    have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have h3 : 1 / ((p : ℕ) : ℝ) ^ 3 ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    have h3' : 0 ≤ 1 / ((p : ℕ) : ℝ) ^ 3 := by positivity
    have hq2 : 0 ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by positivity
    have e2 : 2 / ((p : ℕ) : ℝ) ^ 2 = 2 * (1 / ((p : ℕ) : ℝ) ^ 2) := by ring
    rw [Real.norm_eq_abs, abs_le, e2]
    constructor <;> linarith
  have hm := multipliable_one_add_of_summable hnorm
  have e : (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3))
      = (fun p : Nat.Primes => 1 + (-(2 / ((p : ℕ) : ℝ) ^ 2) + 1 / ((p : ℕ) : ℝ) ^ 3)) := by
    funext p; ring
  unfold Pi0X
  rw [e]
  exact hm.hasProd

/-! ### The multiplicative function `ν` and its sums -/

/-- `ν(f) = μ²(f) ∏_{p|f} g(p)`. -/
def lscNu (g : ℕ → ℝ) (f : ℕ) : ℝ := if Squarefree f then ∏ p ∈ f.primeFactors, g p else 0

/-- the local hypothesis: `|g(p)| ≤ 1` for `p | e`, `|g(p)| ≤ 2/p` for `p ∤ e`. -/
def lscGood (e : ℕ) (g : ℕ → ℝ) : Prop := ∀ p : ℕ, p.Prime → |g p| ≤ (if p ∣ e then 1 else 2 / (p : ℝ))

/-- the majorant `Σ_{d|f, d|e} τ(f/d)/(f/d)` of `|ν(f)|`. -/
def lscMaj (e f : ℕ) : ℝ :=
  ∑ d ∈ f.divisors, (if d ∣ e then ((f / d).divisors.card : ℝ) / ((f / d : ℕ) : ℝ) else 0)

theorem lscMaj_nonneg (e f : ℕ) : 0 ≤ lscMaj e f := by
  unfold lscMaj
  apply Finset.sum_nonneg
  intro d _
  split_ifs <;> positivity

theorem lscNu_zero (g : ℕ → ℝ) : lscNu g 0 = 0 := by
  unfold lscNu; simp

theorem lscNu_one (g : ℕ → ℝ) : lscNu g 1 = 1 := by
  unfold lscNu; simp

theorem lscNu_mul (g : ℕ → ℝ) {u v : ℕ} (h : Nat.Coprime u v) :
    lscNu g (u * v) = lscNu g u * lscNu g v := by
  unfold lscNu
  by_cases hu : Squarefree u
  · by_cases hv : Squarefree v
    · rw [if_pos (Nat.squarefree_mul_iff.mpr ⟨h, hu, hv⟩), if_pos hu, if_pos hv,
        Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]
    · rw [if_neg (fun hs => hv (Nat.squarefree_mul_iff.mp hs).2.2), if_neg hv, mul_zero]
  · rw [if_neg (fun hs => hu (Nat.squarefree_mul_iff.mp hs).2.1), if_neg hu, zero_mul]

theorem lscNu_prime_pow (g : ℕ → ℝ) (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) : lscNu g (p ^ k) = 0 := by
  unfold lscNu
  rw [if_neg]
  intro hs
  have := (Nat.squarefree_pow_iff hp.ne_one (by omega)).mp hs
  omega

theorem lscNu_abs_le (e : ℕ) (g : ℕ → ℝ) (hg : lscGood e g) (f : ℕ) (hf : f ≠ 0) :
    |lscNu g f| ≤ lscMaj e f := by
  have hmaj0 : ∀ d ∈ f.divisors,
      0 ≤ (if d ∣ e then ((f / d).divisors.card : ℝ) / ((f / d : ℕ) : ℝ) else 0) := by
    intro d _; split_ifs <;> positivity
  unfold lscNu
  split_ifs with hsq
  · have hd0f : Nat.gcd f e ∣ f := Nat.gcd_dvd_left f e
    have hd0e : Nat.gcd f e ∣ e := Nat.gcd_dvd_right f e
    have hfdh : f = Nat.gcd f e * (f / Nat.gcd f e) := (Nat.mul_div_cancel' hd0f).symm
    have hsq' : Squarefree (Nat.gcd f e * (f / Nat.gcd f e)) := by rw [← hfdh]; exact hsq
    obtain ⟨hcop, _, hsqh⟩ := Nat.squarefree_mul_iff.mp hsq'
    have hh0 : f / Nat.gcd f e ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hfdh; exact hf hfdh
    have hne : ∀ p ∈ (f / Nat.gcd f e).primeFactors, ¬ p ∣ e := by
      intro p hp hpe
      have hph : p ∣ f / Nat.gcd f e := Nat.dvd_of_mem_primeFactors hp
      have hpf : p ∣ f := dvd_trans hph (Nat.div_dvd_of_dvd hd0f)
      have hpd : p ∣ Nat.gcd f e := Nat.dvd_gcd hpf hpe
      exact (Nat.prime_of_mem_primeFactors hp).ne_one
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpd hcop) hph)
    have hpf : f.primeFactors = (Nat.gcd f e).primeFactors ∪ (f / Nat.gcd f e).primeFactors := by
      conv_lhs => rw [hfdh]
      exact Nat.Coprime.primeFactors_mul hcop
    have h1 : ∏ p ∈ (Nat.gcd f e).primeFactors, |g p| ≤ 1 := by
      apply Finset.prod_le_one (fun p _ => abs_nonneg _)
      intro p hp
      have := hg p (Nat.prime_of_mem_primeFactors hp)
      rwa [if_pos (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hd0e)] at this
    have h2 : ∏ p ∈ (f / Nat.gcd f e).primeFactors, |g p|
        ≤ ∏ p ∈ (f / Nat.gcd f e).primeFactors, (2 / (p : ℝ)) := by
      apply Finset.prod_le_prod (fun p _ => abs_nonneg _)
      intro p hp
      have := hg p (Nat.prime_of_mem_primeFactors hp)
      rwa [if_neg (hne p hp)] at this
    have hh : ∏ p ∈ (f / Nat.gcd f e).primeFactors, (p : ℝ) = ((f / Nat.gcd f e : ℕ) : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsqh]
    have h3 : ∏ p ∈ (f / Nat.gcd f e).primeFactors, (2 / (p : ℝ))
        ≤ ((f / Nat.gcd f e).divisors.card : ℝ) / ((f / Nat.gcd f e : ℕ) : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, hh]
      exact div_le_div_of_nonneg_right (lsc_two_pow_card_le _ hh0) (by positivity)
    rw [Finset.abs_prod, hpf, Finset.prod_union hcop.disjoint_primeFactors]
    calc (∏ p ∈ (Nat.gcd f e).primeFactors, |g p|) * ∏ p ∈ (f / Nat.gcd f e).primeFactors, |g p|
        ≤ 1 * (((f / Nat.gcd f e).divisors.card : ℝ) / ((f / Nat.gcd f e : ℕ) : ℝ)) :=
          mul_le_mul h1 (h2.trans h3) (Finset.prod_nonneg (fun p _ => abs_nonneg _)) zero_le_one
      _ = (if Nat.gcd f e ∣ e then ((f / Nat.gcd f e).divisors.card : ℝ) / ((f / Nat.gcd f e : ℕ) : ℝ)
            else 0) := by rw [one_mul, if_pos hd0e]
      _ ≤ lscMaj e f := Finset.single_le_sum hmaj0 (Nat.mem_divisors.mpr ⟨hd0f, hf⟩)
  · rw [abs_zero]; exact lscMaj_nonneg e f

theorem lsc_count_dvd_le (e : ℕ) (he : e ≠ 0) (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ d ∈ Finset.Icc 1 M, (if d ∣ e then c else 0) ≤ (e.divisors.card : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hc
  have : (Finset.Icc 1 M).filter (fun d => d ∣ e) ⊆ e.divisors := by
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, he⟩
  exact_mod_cast Finset.card_le_card this

theorem lscMaj_sum_le (e : ℕ) (he : e ≠ 0) (N : ℕ) :
    ∑ f ∈ Finset.Icc 1 N, lscMaj e f ≤ (e.divisors.card : ℝ) * (1 + Real.log N) ^ 2 := by
  unfold lscMaj
  have hsw := MuSqPhi.divisor_sum_swap
    (fun d m => if d ∣ e then ((m.divisors.card : ℝ) / (m : ℝ)) else 0) N
  rw [hsw]
  have hb : ∀ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d),
      (if d ∣ e then ((m.divisors.card : ℝ) / (m : ℝ)) else 0)
      ≤ (if d ∣ e then (1 + Real.log N) ^ 2 else 0) := by
    intro d _
    split_ifs
    · calc ∑ m ∈ Finset.Icc 1 (N / d), ((m.divisors.card : ℝ) / (m : ℝ))
          ≤ ∑ m ∈ Finset.Icc 1 N, ((m.divisors.card : ℝ) / (m : ℝ)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              rw [Finset.mem_Icc] at hm ⊢
              exact ⟨hm.1, le_trans hm.2 (Nat.div_le_self N d)⟩
            · intro m _ _; positivity
        _ ≤ (1 + Real.log N) ^ 2 := MuSqPhi.sum_tau_div_le N
    · simp
  exact (Finset.sum_le_sum hb).trans (lsc_count_dvd_le e he N _ (by positivity))

/-- `V(X) = Σ_{m≤X} τ(m)/m²`. -/
def lscV (X : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 X, (m.divisors.card : ℝ) / (m : ℝ) ^ 2

/-- `W(X) = Σ_{b≤X} 1/b²`. -/
def lscW (X : ℕ) : ℝ := ∑ b ∈ Finset.Icc 1 X, (1 : ℝ) / (b : ℝ) ^ 2

theorem lscV_le (X : ℕ) : lscV X ≤ 4 := by
  unfold lscV
  refine (MuSqPhi.sum_tau_div_sq_le X).trans ?_
  have h := hasSum_zeta_two.tsum_eq
  rw [h]
  have hp := Real.pi_lt_d2
  have hp0 := Real.pi_gt_three
  have h1 : Real.pi ^ 2 < 10 := by nlinarith
  have h2 : Real.pi ^ 2 / 6 < 2 := by linarith
  have h3 : 0 < Real.pi ^ 2 / 6 := by positivity
  nlinarith

theorem lscV_eq (X : ℕ) : lscV X = ∑ a ∈ Finset.Icc 1 X, (1 / (a : ℝ) ^ 2) * lscW (X / a) := by
  unfold lscV lscW
  have hsw := MuSqPhi.divisor_sum_swap (fun a b => (1 / (a : ℝ) ^ 2) * (1 / (b : ℝ) ^ 2)) X
  have h1 : ∀ m ∈ Finset.Icc 1 X, (m.divisors.card : ℝ) / (m : ℝ) ^ 2
      = ∑ a ∈ m.divisors, (1 / (a : ℝ) ^ 2) * (1 / ((m / a : ℕ) : ℝ) ^ 2) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    rw [div_eq_mul_one_div, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro a ha
    have had : a ∣ m := Nat.dvd_of_mem_divisors ha
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors ha).ne'
    have hcast : ((m / a : ℕ) : ℝ) = (m : ℝ) / a := Nat.cast_div had ha0
    rw [hcast]
    field_simp
  rw [Finset.sum_congr rfl h1, hsw]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

/-- the tail of `Σ τ(m)/m²`. -/
theorem lscV_tail (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    lscV B - lscV A ≤ 4 * (1 + Real.log A) / A := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  rw [lscV_eq, lscV_eq]
  have hsplit : Finset.Icc 1 B = Finset.Icc 1 A ∪ Finset.Ioc A B := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 A) (Finset.Ioc A B) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx; rw [Finset.mem_Ioc] at hx'; omega
  rw [hsplit, Finset.sum_union hdisj]
  -- first part
  have hfirst : ∑ a ∈ Finset.Icc 1 A, (1 / (a : ℝ) ^ 2) * lscW (B / a)
      - ∑ a ∈ Finset.Icc 1 A, (1 / (a : ℝ) ^ 2) * lscW (A / a) ≤ 2 * (1 + Real.log A) / A := by
    rw [← Finset.sum_sub_distrib]
    have hb : ∀ a ∈ Finset.Icc 1 A, (1 / (a : ℝ) ^ 2) * lscW (B / a) - (1 / (a : ℝ) ^ 2) * lscW (A / a)
        ≤ 2 / A * (1 / (a : ℝ)) := by
      intro a ha
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have haA : a ≤ A := (Finset.mem_Icc.mp ha).2
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha1
      have hAa : 1 ≤ A / a := (Nat.one_le_div_iff (by omega)).mpr haA
      have hAaB : A / a ≤ B / a := Nat.div_le_div_right hAB
      have hW : lscW (B / a) - lscW (A / a) ≤ 1 / ((A / a : ℕ) : ℝ) := by
        unfold lscW
        have e1 : Finset.Icc 1 (B / a) = Finset.Icc 1 (A / a) ∪ Finset.Ioc (A / a) (B / a) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
        have e2 : Disjoint (Finset.Icc 1 (A / a)) (Finset.Ioc (A / a) (B / a)) := by
          rw [Finset.disjoint_left]
          intro x hx hx'
          rw [Finset.mem_Icc] at hx; rw [Finset.mem_Ioc] at hx'; omega
        rw [e1, Finset.sum_union e2, add_sub_cancel_left]
        exact lsc_inv_sq_tail _ _ hAa
      have hAa' : (1 : ℝ) / ((A / a : ℕ) : ℝ) ≤ 2 * a / A := by
        have h1 : A < a * (A / a + 1) := Nat.lt_mul_div_succ A (by omega)
        have h2 : A ≤ 2 * (A / a) * a := by nlinarith
        have h3 : (A : ℝ) ≤ 2 * ((A / a : ℕ) : ℝ) * a := by exact_mod_cast h2
        have h4 : (0 : ℝ) < ((A / a : ℕ) : ℝ) := by exact_mod_cast hAa
        rw [div_le_div_iff₀ h4 hA']
        linarith
      rw [← mul_sub]
      calc (1 / (a : ℝ) ^ 2) * (lscW (B / a) - lscW (A / a)) ≤ (1 / (a : ℝ) ^ 2) * (2 * a / A) :=
            mul_le_mul_of_nonneg_left (hW.trans hAa') (by positivity)
        _ = 2 / A * (1 / (a : ℝ)) := by field_simp
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    calc 2 / (A : ℝ) * ∑ a ∈ Finset.Icc 1 A, 1 / (a : ℝ) ≤ 2 / A * (1 + Real.log A) :=
          mul_le_mul_of_nonneg_left (MuSqPhi.sum_inv_le A) (by positivity)
      _ = 2 * (1 + Real.log A) / A := by ring
  have hsecond : ∑ a ∈ Finset.Ioc A B, (1 / (a : ℝ) ^ 2) * lscW (B / a) ≤ (2 : ℝ) / A := by
    calc ∑ a ∈ Finset.Ioc A B, (1 / (a : ℝ) ^ 2) * lscW (B / a)
        ≤ ∑ a ∈ Finset.Ioc A B, (1 / (a : ℝ) ^ 2) * 2 := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_left (lsc_inv_sq_le_two _) (by positivity)
      _ = 2 * ∑ a ∈ Finset.Ioc A B, (1 / (a : ℝ) ^ 2) := by rw [Finset.mul_sum]; ring_nf
      _ ≤ 2 * (1 / A) := mul_le_mul_of_nonneg_left (lsc_inv_sq_tail A B hA) (by norm_num)
      _ = 2 / A := by ring
  have hlog : 0 ≤ Real.log A := Real.log_nonneg (by exact_mod_cast hA)
  have : 2 / (A : ℝ) ≤ 2 * (1 + Real.log A) / A := by
    apply div_le_div_of_nonneg_right _ hA'.le; linarith
  have e4 : 4 * (1 + Real.log A) / A = 2 * (1 + Real.log A) / A + 2 * (1 + Real.log A) / A := by ring
  linarith

theorem lscV_nonneg (X : ℕ) : 0 ≤ lscV X := by
  unfold lscV; apply Finset.sum_nonneg; intro m _; positivity

theorem lscMaj_div_eq (e M : ℕ) :
    ∑ f ∈ Finset.Icc 1 M, lscMaj e f / f
      = ∑ d ∈ Finset.Icc 1 M, (if d ∣ e then (1 / (d : ℝ)) * lscV (M / d) else 0) := by
  have hsw := MuSqPhi.divisor_sum_swap
    (fun d m => if d ∣ e then (1 / (d : ℝ)) * ((m.divisors.card : ℝ) / (m : ℝ) ^ 2) else 0) M
  have h1 : ∀ f ∈ Finset.Icc 1 M, lscMaj e f / f = ∑ d ∈ f.divisors,
      (if d ∣ e then (1 / (d : ℝ)) * (((f / d).divisors.card : ℝ) / ((f / d : ℕ) : ℝ) ^ 2) else 0) := by
    intro f hf
    unfold lscMaj
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    split_ifs
    · have had : d ∣ f := Nat.dvd_of_mem_divisors hd
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      have hf0 : (f : ℝ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hf).1; exact_mod_cast (show f ≠ 0 by omega)
      rw [Nat.cast_div had hd0]
      field_simp
    · simp
  rw [Finset.sum_congr rfl h1, hsw]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs
  · unfold lscV; rw [Finset.mul_sum]
  · simp

theorem lscMaj_div_le (e : ℕ) (he : e ≠ 0) (M : ℕ) :
    ∑ f ∈ Finset.Icc 1 M, lscMaj e f / f ≤ 4 * (e.divisors.card : ℝ) := by
  rw [lscMaj_div_eq]
  have hb : ∀ d ∈ Finset.Icc 1 M, (if d ∣ e then (1 / (d : ℝ)) * lscV (M / d) else 0)
      ≤ (if d ∣ e then (4 : ℝ) else 0) := by
    intro d hd
    split_ifs
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hV := lscV_le (M / d)
      have hV0 := lscV_nonneg (M / d)
      have h1 : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hd1
      have h2 : 0 ≤ 1 / (d : ℝ) := by positivity
      nlinarith
    · rfl
  refine (Finset.sum_le_sum hb).trans ?_
  have := lsc_count_dvd_le e he M 4 (by norm_num)
  linarith

theorem lscMaj_div_tail (e : ℕ) (he : e ≠ 0) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ f ∈ Finset.Ioc N M, lscMaj e f / f ≤ 8 * (e.divisors.card : ℝ) * (1 + Real.log N) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hsplit : ∑ f ∈ Finset.Ioc N M, lscMaj e f / f
      = ∑ f ∈ Finset.Icc 1 M, lscMaj e f / f - ∑ f ∈ Finset.Icc 1 N, lscMaj e f / f := by
    have e1 : Finset.Icc 1 M = Finset.Icc 1 N ∪ Finset.Ioc N M := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    have e2 : Disjoint (Finset.Icc 1 N) (Finset.Ioc N M) := by
      rw [Finset.disjoint_left]; intro x hx hx'
      rw [Finset.mem_Icc] at hx; rw [Finset.mem_Ioc] at hx'; omega
    rw [e1, Finset.sum_union e2]; ring
  rw [hsplit, lscMaj_div_eq, lscMaj_div_eq]
  have hext : ∑ d ∈ Finset.Icc 1 N, (if d ∣ e then (1 / (d : ℝ)) * lscV (N / d) else 0)
      = ∑ d ∈ Finset.Icc 1 M, (if d ∣ e then (1 / (d : ℝ)) * lscV (N / d) else 0) := by
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro d hd hdN
      rw [Finset.mem_Icc] at hd hdN
      have hNd : N / d = 0 := Nat.div_eq_of_lt (by omega)
      rw [hNd]; unfold lscV; simp
  rw [hext, ← Finset.sum_sub_distrib]
  have hb : ∀ d ∈ Finset.Icc 1 M, (if d ∣ e then (1 / (d : ℝ)) * lscV (M / d) else 0)
      - (if d ∣ e then (1 / (d : ℝ)) * lscV (N / d) else 0)
      ≤ (if d ∣ e then 8 * (1 + Real.log N) / N else 0) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd1
    split_ifs
    · rw [← mul_sub]
      by_cases hdN : d ≤ N
      · have hA : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr hdN
        have hAB : N / d ≤ M / d := Nat.div_le_div_right hNM
        have hT := lscV_tail (N / d) (M / d) hA hAB
        have hA' : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hA
        have hlogA : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N :=
          Real.log_le_log hA' (by exact_mod_cast Nat.div_le_self N d)
        have hlogA0 : 0 ≤ Real.log ((N / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hA)
        have hinv : 1 / ((N / d : ℕ) : ℝ) ≤ 2 * d / N := by
          have h1 : N < d * (N / d + 1) := Nat.lt_mul_div_succ N (by omega)
          have h2 : N ≤ 2 * (N / d) * d := by nlinarith
          have h3 : (N : ℝ) ≤ 2 * ((N / d : ℕ) : ℝ) * d := by exact_mod_cast h2
          rw [div_le_div_iff₀ hA' hN']
          linarith
        have e3 : 4 * (1 + Real.log ((N / d : ℕ) : ℝ)) / ((N / d : ℕ) : ℝ)
            = 4 * (1 + Real.log ((N / d : ℕ) : ℝ)) * (1 / ((N / d : ℕ) : ℝ)) := by ring
        calc 1 / (d : ℝ) * (lscV (M / d) - lscV (N / d))
            ≤ 1 / d * (4 * (1 + Real.log ((N / d : ℕ) : ℝ)) / ((N / d : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hT (by positivity)
          _ ≤ 1 / d * (4 * (1 + Real.log N) * (2 * d / N)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [e3]
              apply mul_le_mul (by linarith) hinv (by positivity) (by positivity)
          _ = 8 * (1 + Real.log N) / N := by field_simp; ring
      · have hNd : N / d = 0 := Nat.div_eq_of_lt (by omega)
        rw [hNd]
        have hV0 : lscV 0 = 0 := by unfold lscV; simp
        rw [hV0, sub_zero]
        have hV := lscV_le (M / d)
        have hdN' : (N : ℝ) < d := by exact_mod_cast (not_le.mp hdN)
        calc 1 / (d : ℝ) * lscV (M / d) ≤ 1 / d * 4 := mul_le_mul_of_nonneg_left hV (by positivity)
          _ = 4 / d := by ring
          _ ≤ 4 / N := div_le_div_of_nonneg_left (by norm_num) hN' hdN'.le
          _ ≤ 8 * (1 + Real.log N) / N := div_le_div_of_nonneg_right (by linarith) hN'.le
    · simp
  refine (Finset.sum_le_sum hb).trans ?_
  have := lsc_count_dvd_le e he M (8 * (1 + Real.log N) / N) (by positivity)
  calc _ ≤ (e.divisors.card : ℝ) * (8 * (1 + Real.log N) / N) := this
    _ = 8 * (e.divisors.card : ℝ) * (1 + Real.log N) / N := by ring

theorem lscNu_div_summable (e : ℕ) (he : e ≠ 0) (g : ℕ → ℝ) (hg : lscGood e g) :
    Summable (fun f => ‖lscNu g f / f‖) := by
  apply summable_of_sum_range_le (c := 4 * (e.divisors.card : ℝ)) (fun n => norm_nonneg _)
  intro n
  have hsub : Finset.range n ⊆ insert 0 (Finset.Icc 1 n) := by
    intro x hx; simp only [Finset.mem_range] at hx; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  calc ∑ i ∈ Finset.range n, ‖lscNu g i / i‖
      ≤ ∑ i ∈ insert 0 (Finset.Icc 1 n), ‖lscNu g i / i‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ = ∑ i ∈ Finset.Icc 1 n, ‖lscNu g i / i‖ := by
        rw [Finset.sum_insert (by simp)]; simp [lscNu_zero]
    _ ≤ ∑ i ∈ Finset.Icc 1 n, lscMaj e i / i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
        rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
        exact div_le_div_of_nonneg_right (lscNu_abs_le e g hg i hi0) (by positivity)
    _ ≤ 4 * (e.divisors.card : ℝ) := lscMaj_div_le e he n

theorem lscNu_div_tail (e : ℕ) (he : e ≠ 0) (g : ℕ → ℝ) (hg : lscGood e g) (N : ℕ) (hN : 1 ≤ N) :
    |∑ f ∈ Finset.Icc 1 N, lscNu g f / f - ∑' f, lscNu g f / f|
      ≤ 8 * (e.divisors.card : ℝ) * (1 + Real.log N) / N := by
  have hS := (lscNu_div_summable e he g hg).of_norm.hasSum
  refine lsc_tail (fun f => lscNu g f / f) _ _ hS (by simp [lscNu_zero]) N ?_
  intro M hM
  calc ∑ f ∈ Finset.Ioc N M, |lscNu g f / f| ≤ ∑ f ∈ Finset.Ioc N M, lscMaj e f / f := by
        apply Finset.sum_le_sum
        intro f hf
        have hf0 : f ≠ 0 := by have := (Finset.mem_Ioc.mp hf).1; omega
        rw [abs_div, Nat.abs_cast]
        exact div_le_div_of_nonneg_right (lscNu_abs_le e g hg f hf0) (by positivity)
    _ ≤ 8 * (e.divisors.card : ℝ) * (1 + Real.log N) / N := lscMaj_div_tail e he N M hN hM

/-- **the generic line count**: `Σ_{j≤N} j ∏_{p|j}(1 + g(p)) = (N²/2) Σ_f ν(f)/f + O(τ(e) N (1+log N)²)`. -/
theorem lsc_conv_count (e : ℕ) (he : e ≠ 0) (g : ℕ → ℝ) (hg : lscGood e g) (N : ℕ) (hN : 1 ≤ N) :
    |∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∏ p ∈ j.primeFactors, (1 + g p)
      - (N : ℝ) ^ 2 / 2 * ∑' f, lscNu g f / f|
      ≤ 5 * (e.divisors.card : ℝ) * ((N : ℝ) * (1 + Real.log N) ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hτ : 0 ≤ (e.divisors.card : ℝ) := by positivity
  have h1 : ∀ j ∈ Finset.Icc 1 N, (j : ℝ) * ∏ p ∈ j.primeFactors, (1 + g p)
      = (j : ℝ) * ∑ f ∈ j.divisors, lscNu g f := by
    intro j hj
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
    rw [← lsc_divsum g j hj0]; rfl
  rw [Finset.sum_congr rfl h1]
  have hA := sum_mul_conv_approx (lscNu g) N
  have hB := lscNu_div_tail e he g hg N hN
  have hC : ∑ f ∈ Finset.Icc 1 N, |lscNu g f| ≤ (e.divisors.card : ℝ) * (1 + Real.log N) ^ 2 :=
    (Finset.sum_le_sum (fun f hf => lscNu_abs_le e g hg f
      (by have := (Finset.mem_Icc.mp hf).1; omega))).trans (lscMaj_sum_le e he N)
  set S := ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∑ f ∈ j.divisors, lscNu g f with hS
  set T := ∑ f ∈ Finset.Icc 1 N, lscNu g f / f with hT
  set L := ∑' f, lscNu g f / f with hL
  have e1 : S - (N : ℝ) ^ 2 / 2 * L = (S - (N : ℝ) ^ 2 / 2 * T) + (N : ℝ) ^ 2 / 2 * (T - L) := by ring
  rw [e1]
  have h2 : |(N : ℝ) ^ 2 / 2 * (T - L)| ≤ 4 * (e.divisors.card : ℝ) * N * (1 + Real.log N) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (N : ℝ) ^ 2 / 2 * |T - L|
        ≤ (N : ℝ) ^ 2 / 2 * (8 * (e.divisors.card : ℝ) * (1 + Real.log N) / N) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 4 * (e.divisors.card : ℝ) * N * (1 + Real.log N) := by field_simp; ring
  have h3 : |S - (N : ℝ) ^ 2 / 2 * T| ≤ (N : ℝ) * ((e.divisors.card : ℝ) * (1 + Real.log N) ^ 2) :=
    hA.trans (mul_le_mul_of_nonneg_left hC hN'.le)
  have h4 : (1 + Real.log N) ≤ (1 + Real.log N) ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 4 * (e.divisors.card : ℝ) * N)
  calc _ ≤ |S - (N : ℝ) ^ 2 / 2 * T| + |(N : ℝ) ^ 2 / 2 * (T - L)| := abs_add_le _ _
    _ ≤ (N : ℝ) * ((e.divisors.card : ℝ) * (1 + Real.log N) ^ 2)
        + 4 * (e.divisors.card : ℝ) * N * (1 + Real.log N) := add_le_add h3 h2
    _ ≤ 5 * (e.divisors.card : ℝ) * ((N : ℝ) * (1 + Real.log N) ^ 2) := by nlinarith [h5]

/-- the Euler product of `ν(f)/f`. -/
theorem lscNu_hasProd (e : ℕ) (he : e ≠ 0) (g : ℕ → ℝ) (hg : lscGood e g) :
    HasProd (fun p : Nat.Primes => 1 + g p / (p : ℕ)) (∑' f, lscNu g f / f) := by
  have h := lsc_hasProd_sqfree (fun f => lscNu g f / f) (by simp [lscNu_zero]) (by simp [lscNu_one])
    (fun {m n} hmn => by
      rw [lscNu_mul g hmn]; push_cast
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [lscNu_zero]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [lscNu_zero]
      field_simp)
    (fun p k hp hk => by rw [lscNu_prime_pow g p k hp hk, zero_div])
    (lscNu_div_summable e he g hg)
  have hf : (fun p : Nat.Primes => 1 + lscNu g (p : ℕ) / ((p : ℕ) : ℝ))
      = (fun p : Nat.Primes => 1 + g p / (p : ℕ)) := by
    funext p
    unfold lscNu
    rw [if_pos p.2.prime.squarefree, Nat.Prime.primeFactors p.2, Finset.prod_singleton]
  rwa [hf] at h

/-! ### The coefficients in closed form -/

/-- `𝔈_{j,r}(e)`, plain kind (the body of the library's `Ecoef FKind.plain`). -/
def EcoefPl (r j e : ℕ) : ℝ :=
  ((6 / Real.pi ^ 2) * ∏ p ∈ (r * j * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹) *
  (∏ p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * j), (1 - 1 / (p : ℝ))) *
  ∏ p ∈ (Nat.gcd r j).primeFactors, (if p ∣ e then 0 else 1 - 1 / (p : ℝ))

/-- `𝔈_{j,r}(e)`, `q/φ` kind (the body of the library's `Ecoef FKind.qphi`). -/
def EcoefQp (r j e : ℕ) : ℝ :=
  1 * (∏ p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * j), (1 - 1 / (p : ℝ))) *
  ∏ p ∈ (Nat.gcd r j).primeFactors, (if p ∣ e then (0 : ℝ) else 1)

/-- `Π(e)`, plain kind. -/
def PiEPl (e : ℕ) : ℝ := Pi0X * ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)⁻¹

/-- `Π(e)`, `q/φ` kind. -/
def PiEQp (e : ℕ) : ℝ := (6 / Real.pi ^ 2) * ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ))⁻¹

/-- the local factor `ρ_p − 1` of `φ(j)𝔈_{j,r}(e)/(j 𝔈_{1,r}(e))`, plain kind. -/
def gPl (r e p : ℕ) : ℝ :=
  (if p ∣ e then (if p ∣ r then 0 else 1)
    else (if p ∣ r then (1 - 1 / (p : ℝ)) ^ 2 else (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ) ^ 2)⁻¹)) - 1

/-- the same, `q/φ` kind. -/
def gQp (r e p : ℕ) : ℝ := (if p ∣ e then (if p ∣ r then 0 else 1) else 1 - 1 / (p : ℝ)) - 1

theorem lsc_prod_ext (S U : Finset ℕ) (hSU : S ⊆ U) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ p ∈ U, (p ∈ S ↔ P p)) (c : ℕ → ℝ) :
    ∏ p ∈ S, c p = ∏ p ∈ U, (if P p then c p else 1) := by
  rw [← Finset.prod_filter]
  congr 1
  ext p
  rw [Finset.mem_filter]
  constructor
  · intro hp; exact ⟨hSU hp, (hP p (hSU hp)).mp hp⟩
  · rintro ⟨hpU, hpP⟩; exact (hP p hpU).mpr hpP

theorem lsc_totient (n : ℕ) : (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h2 : ((n.totient : ℚ) : ℝ) = ((n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by rw [h]
  push_cast at h2
  rw [h2]
  simp [one_div]

theorem lsc_p_facts (p : ℕ) (hp : p.Prime) :
    (2 : ℝ) ≤ p ∧ (1 - 1 / (p : ℝ)) ≠ 0 ∧ (1 - 1 / (p : ℝ) ^ 2) ≠ 0 ∧ (0 : ℝ) < 1 - 1 / (p : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h3 : 1 / (p : ℝ) ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  exact ⟨h2, by linarith, by linarith, by linarith⟩

/-- **the factorisation, plain kind**: `φ(j) 𝔈_{j,r}(e) = 𝔈_{1,r}(e) · j ∏_{p|j}(1 + g(p))`. -/
theorem lsc_factor_pl (r j e : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (he : 1 ≤ e) :
    (Nat.totient j : ℝ) * EcoefPl r j e
      = EcoefPl r 1 e * ((j : ℝ) * ∏ p ∈ j.primeFactors, (1 + gPl r e p)) := by
  have hm : r * j * e ≠ 0 := by positivity
  have he0 : e ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  have hr0 : r ≠ 0 := by omega
  set U := (r * j * e).primeFactors with hU
  have hdvd : ∀ p ∈ U, p.Prime ∧ (p ∣ r * j ↔ p ∣ r ∨ p ∣ j) ∧ (p ∣ r * 1 * e ↔ p ∣ r ∨ p ∣ e)
      ∧ (p ∣ r * 1 ↔ p ∣ r) ∧ (p ∣ r ∨ p ∣ j ∨ p ∣ e) := by
    intro p hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hpm := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpP, hpP.dvd_mul, ?_, by rw [mul_one], ?_⟩
    · rw [mul_one]; exact hpP.dvd_mul
    · rcases (hpP.dvd_mul).mp hpm with h | h
      · rcases (hpP.dvd_mul).mp h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
  have hjU : j.primeFactors ⊆ U := Nat.primeFactors_mono (Dvd.intro (r * e) (by ring)) hm
  have hj' : ∀ p ∈ U, (p ∈ j.primeFactors ↔ p ∣ j) := fun p hp => by
    rw [Nat.mem_primeFactors]; exact ⟨fun h => h.2.1, fun h => ⟨(hdvd p hp).1, h, hj0⟩⟩
  have h1U : (r * 1 * e).primeFactors ⊆ U :=
    Nat.primeFactors_mono (by rw [mul_one]; exact Nat.mul_dvd_mul_right (Dvd.intro _ rfl) e) hm
  have h1' : ∀ p ∈ U, (p ∈ (r * 1 * e).primeFactors ↔ p ∣ r * 1 * e) := fun p hp => by
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨(hdvd p hp).1, h, by rw [mul_one]; positivity⟩⟩
  have heU : e.primeFactors ⊆ U := Nat.primeFactors_mono (Dvd.intro_left _ rfl) hm
  have hBU : e.primeFactors.filter (fun p => ¬ p ∣ r * j) ⊆ U := (Finset.filter_subset _ _).trans heU
  have hB' : ∀ p ∈ U, (p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * j) ↔ (p ∣ e ∧ ¬ p ∣ r * j)) :=
    fun p hp => by
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨fun h => ⟨h.1.2.1, h.2⟩, fun h => ⟨⟨(hdvd p hp).1, h.1, he0⟩, h.2⟩⟩
  have hB1U : e.primeFactors.filter (fun p => ¬ p ∣ r * 1) ⊆ U := (Finset.filter_subset _ _).trans heU
  have hB1' : ∀ p ∈ U, (p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * 1) ↔ (p ∣ e ∧ ¬ p ∣ r * 1)) :=
    fun p hp => by
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨fun h => ⟨h.1.2.1, h.2⟩, fun h => ⟨⟨(hdvd p hp).1, h.1, he0⟩, h.2⟩⟩
  have hCU : (Nat.gcd r j).primeFactors ⊆ U :=
    Nat.primeFactors_mono (dvd_trans (Nat.gcd_dvd_left r j) (Dvd.intro (j * e) (by ring))) hm
  have hC' : ∀ p ∈ U, (p ∈ (Nat.gcd r j).primeFactors ↔ (p ∣ r ∧ p ∣ j)) := fun p hp => by
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => ⟨dvd_trans h.2.1 (Nat.gcd_dvd_left r j), dvd_trans h.2.1 (Nat.gcd_dvd_right r j)⟩,
      fun h => ⟨(hdvd p hp).1, Nat.dvd_gcd h.1 h.2, Nat.gcd_ne_zero_left hr0⟩⟩
  have hg1 : (Nat.gcd r 1).primeFactors = ∅ := by rw [Nat.gcd_one_right]; simp
  unfold EcoefPl
  rw [hg1, Finset.prod_empty, mul_one, lsc_totient,
    lsc_prod_ext _ U hjU (fun p => p ∣ j) hj' (fun p => 1 - 1 / (p : ℝ)),
    lsc_prod_ext _ U hjU (fun p => p ∣ j) hj' (fun p => 1 + gPl r e p),
    lsc_prod_ext _ U h1U (fun p => p ∣ r * 1 * e) h1' (fun p => (1 - 1 / (p : ℝ) ^ 2)⁻¹),
    lsc_prod_ext _ U hBU (fun p => p ∣ e ∧ ¬ p ∣ r * j) hB' (fun p => 1 - 1 / (p : ℝ)),
    lsc_prod_ext _ U hB1U (fun p => p ∣ e ∧ ¬ p ∣ r * 1) hB1' (fun p => 1 - 1 / (p : ℝ)),
    lsc_prod_ext _ U hCU (fun p => p ∣ r ∧ p ∣ j) hC' (fun p => if p ∣ e then 0 else 1 - 1 / (p : ℝ))]
  have key : ∀ p ∈ U, (if p ∣ j then 1 - 1 / (p : ℝ) else 1) * (1 - 1 / (p : ℝ) ^ 2)⁻¹
      * (if p ∣ e ∧ ¬ p ∣ r * j then 1 - 1 / (p : ℝ) else 1)
      * (if p ∣ r ∧ p ∣ j then (if p ∣ e then 0 else 1 - 1 / (p : ℝ)) else 1)
      = (if p ∣ r * 1 * e then (1 - 1 / (p : ℝ) ^ 2)⁻¹ else 1)
        * (if p ∣ e ∧ ¬ p ∣ r * 1 then 1 - 1 / (p : ℝ) else 1)
        * (if p ∣ j then 1 + gPl r e p else 1) := by
    intro p hp
    obtain ⟨hpP, hrj, hre, hr1, hcase⟩ := hdvd p hp
    obtain ⟨_, hq1, hq2, _⟩ := lsc_p_facts p hpP
    unfold gPl
    simp only [hrj, hre, hr1]
    by_cases h1 : p ∣ r <;> by_cases h2 : p ∣ j <;> by_cases h3 : p ∣ e <;>
      simp only [h1, h2, h3, if_true, if_false, and_true, or_true, not_true_eq_false,
        not_false_eq_true, and_false, or_false] <;>
      first | (exfalso; rcases hcase with h | h | h <;> contradiction) | ring
  have hprod := Finset.prod_congr rfl key
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
  rw [← hU]
  linear_combination (6 / Real.pi ^ 2 * (j : ℝ)) * hprod

/-- **the factorisation, `q/φ` kind**. -/
theorem lsc_factor_qp (r j e : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (he : 1 ≤ e) :
    (Nat.totient j : ℝ) * EcoefQp r j e
      = EcoefQp r 1 e * ((j : ℝ) * ∏ p ∈ j.primeFactors, (1 + gQp r e p)) := by
  have hm : r * j * e ≠ 0 := by positivity
  have he0 : e ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  have hr0 : r ≠ 0 := by omega
  set U := (r * j * e).primeFactors with hU
  have hdvd : ∀ p ∈ U, p.Prime ∧ (p ∣ r * j ↔ p ∣ r ∨ p ∣ j)
      ∧ (p ∣ r * 1 ↔ p ∣ r) ∧ (p ∣ r ∨ p ∣ j ∨ p ∣ e) := by
    intro p hp
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hpm := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpP, hpP.dvd_mul, by rw [mul_one], ?_⟩
    rcases (hpP.dvd_mul).mp hpm with h | h
    · rcases (hpP.dvd_mul).mp h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h)
  have hjU : j.primeFactors ⊆ U := Nat.primeFactors_mono (Dvd.intro (r * e) (by ring)) hm
  have hj' : ∀ p ∈ U, (p ∈ j.primeFactors ↔ p ∣ j) := fun p hp => by
    rw [Nat.mem_primeFactors]; exact ⟨fun h => h.2.1, fun h => ⟨(hdvd p hp).1, h, hj0⟩⟩
  have heU : e.primeFactors ⊆ U := Nat.primeFactors_mono (Dvd.intro_left _ rfl) hm
  have hBU : e.primeFactors.filter (fun p => ¬ p ∣ r * j) ⊆ U := (Finset.filter_subset _ _).trans heU
  have hB' : ∀ p ∈ U, (p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * j) ↔ (p ∣ e ∧ ¬ p ∣ r * j)) :=
    fun p hp => by
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨fun h => ⟨h.1.2.1, h.2⟩, fun h => ⟨⟨(hdvd p hp).1, h.1, he0⟩, h.2⟩⟩
  have hB1U : e.primeFactors.filter (fun p => ¬ p ∣ r * 1) ⊆ U := (Finset.filter_subset _ _).trans heU
  have hB1' : ∀ p ∈ U, (p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * 1) ↔ (p ∣ e ∧ ¬ p ∣ r * 1)) :=
    fun p hp => by
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨fun h => ⟨h.1.2.1, h.2⟩, fun h => ⟨⟨(hdvd p hp).1, h.1, he0⟩, h.2⟩⟩
  have hCU : (Nat.gcd r j).primeFactors ⊆ U :=
    Nat.primeFactors_mono (dvd_trans (Nat.gcd_dvd_left r j) (Dvd.intro (j * e) (by ring))) hm
  have hC' : ∀ p ∈ U, (p ∈ (Nat.gcd r j).primeFactors ↔ (p ∣ r ∧ p ∣ j)) := fun p hp => by
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => ⟨dvd_trans h.2.1 (Nat.gcd_dvd_left r j), dvd_trans h.2.1 (Nat.gcd_dvd_right r j)⟩,
      fun h => ⟨(hdvd p hp).1, Nat.dvd_gcd h.1 h.2, Nat.gcd_ne_zero_left hr0⟩⟩
  have hg1 : (Nat.gcd r 1).primeFactors = ∅ := by rw [Nat.gcd_one_right]; simp
  unfold EcoefQp
  rw [hg1, Finset.prod_empty, mul_one, lsc_totient,
    lsc_prod_ext _ U hjU (fun p => p ∣ j) hj' (fun p => 1 - 1 / (p : ℝ)),
    lsc_prod_ext _ U hjU (fun p => p ∣ j) hj' (fun p => 1 + gQp r e p),
    lsc_prod_ext _ U hBU (fun p => p ∣ e ∧ ¬ p ∣ r * j) hB' (fun p => 1 - 1 / (p : ℝ)),
    lsc_prod_ext _ U hB1U (fun p => p ∣ e ∧ ¬ p ∣ r * 1) hB1' (fun p => 1 - 1 / (p : ℝ)),
    lsc_prod_ext _ U hCU (fun p => p ∣ r ∧ p ∣ j) hC' (fun p => if p ∣ e then (0 : ℝ) else 1)]
  have key : ∀ p ∈ U, (if p ∣ j then 1 - 1 / (p : ℝ) else 1)
      * (if p ∣ e ∧ ¬ p ∣ r * j then 1 - 1 / (p : ℝ) else 1)
      * (if p ∣ r ∧ p ∣ j then (if p ∣ e then (0 : ℝ) else 1) else 1)
      = (if p ∣ e ∧ ¬ p ∣ r * 1 then 1 - 1 / (p : ℝ) else 1)
        * (if p ∣ j then 1 + gQp r e p else 1) := by
    intro p hp
    obtain ⟨hpP, hrj, hr1, hcase⟩ := hdvd p hp
    unfold gQp
    simp only [hrj, hr1]
    by_cases h1 : p ∣ r <;> by_cases h2 : p ∣ j <;> by_cases h3 : p ∣ e <;>
      simp only [h1, h2, h3, if_true, if_false, and_true, or_true, not_true_eq_false,
        not_false_eq_true, and_false, or_false] <;>
      first | (exfalso; rcases hcase with h | h | h <;> contradiction) | ring
  have hprod := Finset.prod_congr rfl key
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
  linear_combination (j : ℝ) * hprod

theorem lsc_prod_inv_le_exp (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (m : ℕ) (hSm : S ⊆ Finset.Icc 1 m) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2)⁻¹ ≤ Real.exp 4 := by
  have h1 : ∀ p ∈ S, (1 - 1 / (p : ℝ) ^ 2)⁻¹ ≤ Real.exp (2 * (1 / (p : ℝ) ^ 2)) := by
    intro p hp
    obtain ⟨h2, _, _, hpos⟩ := lsc_p_facts p (hS p hp)
    have hu0 : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
    have hu : 1 / (p : ℝ) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    calc (1 - 1 / (p : ℝ) ^ 2)⁻¹ ≤ 1 + 2 * (1 / (p : ℝ) ^ 2) := by
          rw [inv_eq_one_div, div_le_iff₀ hpos]
          nlinarith
      _ ≤ Real.exp (2 * (1 / (p : ℝ) ^ 2)) := by linarith [Real.add_one_le_exp (2 * (1 / (p : ℝ) ^ 2))]
  calc ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2)⁻¹ ≤ ∏ p ∈ S, Real.exp (2 * (1 / (p : ℝ) ^ 2)) :=
        Finset.prod_le_prod (fun p hp => (inv_pos.mpr (lsc_p_facts p (hS p hp)).2.2.2).le) h1
    _ = Real.exp (∑ p ∈ S, 2 * (1 / (p : ℝ) ^ 2)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 4 := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.mul_sum]
        have h3 : ∑ p ∈ S, (1 / (p : ℝ) ^ 2) ≤ ∑ b ∈ Finset.Icc 1 m, (1 : ℝ) / (b : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hSm (fun _ _ _ => by positivity)
        have := lsc_inv_sq_le_two m
        linarith

theorem lsc_prod_one_sub_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (P : ℕ → Prop) [DecidablePred P] :
    0 ≤ ∏ p ∈ S, (if P p then 1 - 1 / (p : ℝ) else 1) ∧ ∏ p ∈ S, (if P p then 1 - 1 / (p : ℝ) else 1) ≤ 1 := by
  have hb : ∀ p ∈ S, 0 ≤ (if P p then 1 - 1 / (p : ℝ) else 1) ∧ (if P p then 1 - 1 / (p : ℝ) else 1) ≤ 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := (lsc_p_facts p (hS p hp)).1
    have h3 : 0 ≤ 1 / (p : ℝ) := by positivity
    have h4 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    split_ifs <;> constructor <;> linarith
  exact ⟨Finset.prod_nonneg (fun p hp => (hb p hp).1),
    Finset.prod_le_one (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2)⟩

theorem lsc_K_pl_bound (r e : ℕ) (hr : 1 ≤ r) (he : 1 ≤ e) : |EcoefPl r 1 e| ≤ Real.exp 4 := by
  have hm : r * 1 * e ≠ 0 := by positivity
  unfold EcoefPl
  rw [Nat.gcd_one_right, Nat.primeFactors_one, Finset.prod_empty, mul_one, Finset.prod_filter]
  have hA := lsc_prod_inv_le_exp (r * 1 * e).primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (r * 1 * e) (fun p hp => by
      rw [Finset.mem_Icc]
      exact ⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le,
        Nat.le_of_dvd (by positivity) (Nat.dvd_of_mem_primeFactors hp)⟩)
  have hA0 : 0 ≤ ∏ p ∈ (r * 1 * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ :=
    Finset.prod_nonneg (fun p hp => (inv_pos.mpr (lsc_p_facts p (Nat.prime_of_mem_primeFactors hp)).2.2.2).le)
  obtain ⟨hB0, hB1⟩ := lsc_prod_one_sub_le e.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun p => ¬ p ∣ r * 1)
  have hpi : 0 < 6 / Real.pi ^ 2 := by positivity
  have hpi1 : 6 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  rw [abs_of_nonneg (by positivity)]
  calc _ ≤ 1 * Real.exp 4 * 1 := by
        apply mul_le_mul (mul_le_mul hpi1 hA hA0 (by norm_num)) hB1 hB0 (by positivity)
    _ = Real.exp 4 := by ring

theorem lsc_K_qp_bound (r e : ℕ) : |EcoefQp r 1 e| ≤ 1 := by
  unfold EcoefQp
  rw [Nat.gcd_one_right, Nat.primeFactors_one, Finset.prod_empty, mul_one, Finset.prod_filter, one_mul]
  obtain ⟨hB0, hB1⟩ := lsc_prod_one_sub_le e.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun p => ¬ p ∣ r * 1)
  rw [abs_of_nonneg hB0]
  exact hB1

theorem lsc_good_pl (r e : ℕ) : lscGood e (gPl r e) := by
  intro p hp
  obtain ⟨h2, hq1, hq2, hpos⟩ := lsc_p_facts p hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) + 1 ≠ 0 := by linarith
  have hpp : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hi : 0 ≤ 1 / (p : ℝ) := by positivity
  have hi2 : 1 / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  unfold gPl
  by_cases he : p ∣ e <;> by_cases hr : p ∣ r <;> simp only [he, hr, if_true, if_false]
  · norm_num
  · norm_num
  · have e1 : (1 - 1 / (p : ℝ)) ^ 2 - 1 = -(2 / p) + 1 / (p : ℝ) ^ 2 := by ring
    rw [e1, abs_le]
    have e2 : 2 / (p : ℝ) = 2 * (1 / p) := by ring
    constructor <;> nlinarith
  · have e1 : (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ) ^ 2)⁻¹ - 1 = -(1 / ((p : ℝ) + 1)) := by
      field_simp
      ring
    rw [e1, abs_neg, abs_of_nonneg (by positivity)]
    have : 1 / ((p : ℝ) + 1) ≤ 1 / p := one_div_le_one_div_of_le (by linarith) (by linarith)
    have e2 : 2 / (p : ℝ) = 2 * (1 / p) := by ring
    linarith

theorem lsc_good_qp (r e : ℕ) : lscGood e (gQp r e) := by
  intro p hp
  obtain ⟨h2, _, _, _⟩ := lsc_p_facts p hp
  have hi : 0 ≤ 1 / (p : ℝ) := by positivity
  unfold gQp
  by_cases he : p ∣ e <;> by_cases hr : p ∣ r <;> simp only [he, hr, if_true, if_false]
  · norm_num
  · norm_num
  · rw [show 1 - 1 / (p : ℝ) - 1 = -(1 / p) by ring, abs_neg, abs_of_nonneg hi]
    have e2 : 2 / (p : ℝ) = 2 * (1 / p) := by ring
    linarith
  · rw [show 1 - 1 / (p : ℝ) - 1 = -(1 / p) by ring, abs_neg, abs_of_nonneg hi]
    have e2 : 2 / (p : ℝ) = 2 * (1 / p) := by ring
    linarith

/-- **the Euler product, plain kind**: `𝔈_{1,r}(e) Σ_f ν(f)/f = Π(e)`. -/
theorem lsc_euler_pl (r e : ℕ) (hr : 1 ≤ r) (he : 1 ≤ e) :
    EcoefPl r 1 e * ∑' f, lscNu (gPl r e) f / f = PiEPl e := by
  have he0 : e ≠ 0 := by omega
  have hm : r * 1 * e ≠ 0 := by positivity
  have hF := lscNu_hasProd e he0 (gPl r e) (lsc_good_pl r e)
  have hc1 := lsc_hasProd_dvd (r * 1 * e) hm (fun p => (1 - 1 / (p : ℝ) ^ 2)⁻¹)
  have hc2 := lsc_hasProd_dvd e he0 (fun p => if ¬ p ∣ r * 1 then 1 - 1 / (p : ℝ) else 1)
  have hc3 := lsc_hasProd_dvd e he0 (fun p => (1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)⁻¹)
  have h1 := ((hF.mul lsc_m2).mul hc1).mul hc2
  have h2 := lsc_Pi0.mul hc3
  have h1' : HasProd (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3)
      * (if (p : ℕ) ∣ e then (1 + 1 / ((p : ℕ) : ℝ) - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ else 1))
      ((∑' f, lscNu (gPl r e) f / f) * (6 / Real.pi ^ 2)
        * (∏ p ∈ (r * 1 * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹)
        * (∏ p ∈ e.primeFactors, (if ¬ p ∣ r * 1 then 1 - 1 / (p : ℝ) else 1))) := by
    convert h1 using 1
    funext p
    obtain ⟨h2, hq1, hq2, hpos⟩ := lsc_p_facts p p.2
    have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by linarith
    have hpl : 1 + 1 / ((p : ℕ) : ℝ) - 1 / ((p : ℕ) : ℝ) ^ 2 ≠ 0 := by
      have : 1 / ((p : ℕ) : ℝ) ^ 2 ≤ 1 / ((p : ℕ) : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have : 0 < 1 / ((p : ℕ) : ℝ) := by positivity
      linarith
    have hre : (p : ℕ) ∣ r * e ↔ (p : ℕ) ∣ r ∨ (p : ℕ) ∣ e := p.2.dvd_mul
    have hA : (-1 + ((p : ℕ) : ℝ) + ((p : ℕ) : ℝ) ^ 2) ≠ 0 := by nlinarith
    have hB : (-1 + ((p : ℕ) : ℝ) ^ 2) ≠ 0 := by nlinarith
    have hA' : (((p : ℕ) : ℝ) ^ 2 + ((p : ℕ) : ℝ) - 1) ≠ 0 := by nlinarith
    have hB' : (((p : ℕ) : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith
    simp only [mul_one, hre]
    have hX : (1 + 1 / ((p : ℕ) : ℝ) - 1 / ((p : ℕ) : ℝ) ^ 2)
        * (1 + 1 / ((p : ℕ) : ℝ) - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hpl
    have hY : (1 - 1 / ((p : ℕ) : ℝ) ^ 2) * (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hq2
    have hH : (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3)
        = (1 - 1 / ((p : ℕ) : ℝ)) * (1 + 1 / ((p : ℕ) : ℝ) - 1 / ((p : ℕ) : ℝ) ^ 2) := by ring
    unfold gPl
    by_cases h3 : (p : ℕ) ∣ e <;> by_cases h4 : (p : ℕ) ∣ r <;>
      simp only [h3, h4, if_true, if_false, or_true, or_false, not_true_eq_false,
        not_false_eq_true]
    · linear_combination (1 + 1 / ((p : ℕ) : ℝ) - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ * hH
        + (1 - 1 / ((p : ℕ) : ℝ)) * hX - (1 - 1 / ((p : ℕ) : ℝ)) * hY
    · linear_combination (1 + 1 / ((p : ℕ) : ℝ) - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ * hH
        + (1 - 1 / ((p : ℕ) : ℝ)) * hX - (1 - 1 / ((p : ℕ) : ℝ)) * hY
    · field_simp; ring
    · field_simp; ring
  have h3 := h1'.unique h2
  unfold EcoefPl PiEPl
  rw [Nat.gcd_one_right, Nat.primeFactors_one, Finset.prod_empty, mul_one, Finset.prod_filter]
  linear_combination h3

/-- **the Euler product, `q/φ` kind**. -/
theorem lsc_euler_qp (r e : ℕ) (he : 1 ≤ e) :
    EcoefQp r 1 e * ∑' f, lscNu (gQp r e) f / f = PiEQp e := by
  have he0 : e ≠ 0 := by omega
  have hF := lscNu_hasProd e he0 (gQp r e) (lsc_good_qp r e)
  have hc2 := lsc_hasProd_dvd e he0 (fun p => if ¬ p ∣ r * 1 then 1 - 1 / (p : ℝ) else 1)
  have hc4 := lsc_hasProd_dvd e he0 (fun p => (1 + 1 / (p : ℝ))⁻¹)
  have h1 := hF.mul hc2
  have h2 := lsc_m2.mul hc4
  have h1' : HasProd (fun p : Nat.Primes => (1 - 1 / ((p : ℕ) : ℝ) ^ 2)
      * (if (p : ℕ) ∣ e then (1 + 1 / ((p : ℕ) : ℝ))⁻¹ else 1))
      ((∑' f, lscNu (gQp r e) f / f)
        * (∏ p ∈ e.primeFactors, (if ¬ p ∣ r * 1 then 1 - 1 / (p : ℝ) else 1))) := by
    convert h1 using 1
    funext p
    obtain ⟨h2, hq1, hq2, hpos⟩ := lsc_p_facts p p.2
    have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by linarith
    have hp1 : 1 + 1 / ((p : ℕ) : ℝ) ≠ 0 := by
      have : 0 < 1 / ((p : ℕ) : ℝ) := by positivity
      linarith
    have hB : (-1 + ((p : ℕ) : ℝ) ^ 2) ≠ 0 := by nlinarith
    have hB' : (((p : ℕ) : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith
    have hC : (((p : ℕ) : ℝ) + 1) ≠ 0 := by nlinarith
    have hC' : (1 + ((p : ℕ) : ℝ)) ≠ 0 := by nlinarith
    simp only [mul_one]
    unfold gQp
    by_cases h3 : (p : ℕ) ∣ e <;> by_cases h4 : (p : ℕ) ∣ r <;>
      simp only [h3, h4, if_true, if_false, not_true_eq_false, not_false_eq_true] <;> field_simp <;> ring
  have h3 := h1'.unique h2
  unfold EcoefQp PiEQp
  rw [Nat.gcd_one_right, Nat.primeFactors_one, Finset.prod_empty, mul_one, Finset.prod_filter]
  linear_combination h3

/-- **the unweighted line count, plain kind** (L7_11's `LineCountAsymp FKind.plain`). -/
theorem lsc_count_pl : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 1 ≤ r → ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N →
    |∑ j ∈ Finset.Icc 1 N, (Nat.totient j : ℝ) * EcoefPl r j e - (N : ℝ) ^ 2 / 2 * PiEPl e|
      ≤ C * (e.divisors.card : ℝ) * ((N : ℝ) * (1 + Real.log N) ^ 2) := by
  refine ⟨5 * Real.exp 4, by positivity, ?_⟩
  intro r hr e he N hN
  have he0 : e ≠ 0 := by omega
  have hfac : ∑ j ∈ Finset.Icc 1 N, (Nat.totient j : ℝ) * EcoefPl r j e
      = EcoefPl r 1 e * ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∏ p ∈ j.primeFactors, (1 + gPl r e p) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
    exact lsc_factor_pl r j e hr (Finset.mem_Icc.mp hj).1 he
  rw [hfac, ← lsc_euler_pl r e hr he]
  have hc := lsc_conv_count e he0 (gPl r e) (lsc_good_pl r e) N hN
  have hK := lsc_K_pl_bound r e hr he
  set S := ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∏ p ∈ j.primeFactors, (1 + gPl r e p)
  set L := ∑' f, lscNu (gPl r e) f / f
  rw [show EcoefPl r 1 e * S - (N : ℝ) ^ 2 / 2 * (EcoefPl r 1 e * L)
      = EcoefPl r 1 e * (S - (N : ℝ) ^ 2 / 2 * L) by ring, abs_mul]
  calc |EcoefPl r 1 e| * |S - (N : ℝ) ^ 2 / 2 * L|
      ≤ Real.exp 4 * (5 * (e.divisors.card : ℝ) * ((N : ℝ) * (1 + Real.log N) ^ 2)) :=
        mul_le_mul hK hc (abs_nonneg _) (by positivity)
    _ = 5 * Real.exp 4 * (e.divisors.card : ℝ) * ((N : ℝ) * (1 + Real.log N) ^ 2) := by ring

/-- **the unweighted line count, `q/φ` kind**. -/
theorem lsc_count_qp : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 1 ≤ r → ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N →
    |∑ j ∈ Finset.Icc 1 N, (Nat.totient j : ℝ) * EcoefQp r j e - (N : ℝ) ^ 2 / 2 * PiEQp e|
      ≤ C * (e.divisors.card : ℝ) * ((N : ℝ) * (1 + Real.log N) ^ 2) := by
  refine ⟨5, by norm_num, ?_⟩
  intro r hr e he N hN
  have he0 : e ≠ 0 := by omega
  have hfac : ∑ j ∈ Finset.Icc 1 N, (Nat.totient j : ℝ) * EcoefQp r j e
      = EcoefQp r 1 e * ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∏ p ∈ j.primeFactors, (1 + gQp r e p) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
    exact lsc_factor_qp r j e hr (Finset.mem_Icc.mp hj).1 he
  rw [hfac, ← lsc_euler_qp r e he]
  have hc := lsc_conv_count e he0 (gQp r e) (lsc_good_qp r e) N hN
  have hK := lsc_K_qp_bound r e
  set S := ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∏ p ∈ j.primeFactors, (1 + gQp r e p)
  set L := ∑' f, lscNu (gQp r e) f / f
  rw [show EcoefQp r 1 e * S - (N : ℝ) ^ 2 / 2 * (EcoefQp r 1 e * L)
      = EcoefQp r 1 e * (S - (N : ℝ) ^ 2 / 2 * L) by ring, abs_mul]
  calc |EcoefQp r 1 e| * |S - (N : ℝ) ^ 2 / 2 * L|
      ≤ 1 * (5 * (e.divisors.card : ℝ) * ((N : ℝ) * (1 + Real.log N) ^ 2)) :=
        mul_le_mul hK hc (abs_nonneg _) (by norm_num)
    _ = 5 * (e.divisors.card : ℝ) * ((N : ℝ) * (1 + Real.log N) ^ 2) := by ring

/-! ### Partial summation against the three weights (L7_11's `L711_LineSumRed` draft, finished) -/

/-- `w` of the sharp family (the body of the library's `Fam.w Fam.sharp`). -/
def wSharp : ℝ → ℝ := fun x => if 0 ≤ x ∧ x ≤ 1 then 1 else 0

/-- `w` of the dyadic family. -/
def wDyadic : ℝ → ℝ := fun x => if 1 / 2 < x ∧ x ≤ 1 then 1 else 0

/-- `w` of the weighted family. -/
def wWeighted : ℝ → ℝ := fun x => if 0 ≤ x ∧ x ≤ 1 then (1 - x) ^ 2 else 0

theorem lsc_nlog_le {n : ℕ} {y : ℝ} (hn : 1 ≤ n) (hny : (n : ℝ) ≤ y) :
    (n : ℝ) * (1 + Real.log n) ^ 2 ≤ y * (1 + Real.log y) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hl : Real.log n ≤ Real.log y := Real.log_le_log (by linarith) hny
  have hsq : (1 + Real.log n) ^ 2 ≤ (1 + Real.log y) ^ 2 := by nlinarith
  exact mul_le_mul hny hsq (by positivity) (by linarith)

/-- the count error at every `n ≤ y`. -/
theorem lsc_count_err (a : ℕ → ℝ) (P C τ : ℝ) (hC : 0 ≤ C) (hτ : 1 ≤ τ)
    (hcount : ∀ n : ℕ, 1 ≤ n → |∑ j ∈ Finset.Icc 1 n, a j - (n : ℝ) ^ 2 / 2 * P|
      ≤ C * τ * ((n : ℝ) * (1 + Real.log n) ^ 2))
    (y : ℝ) (hy : 1 ≤ y) (n : ℕ) (hn : (n : ℝ) ≤ y) :
    |∑ j ∈ Finset.Icc 1 n, a j - (n : ℝ) ^ 2 / 2 * P| ≤ C * τ * (y * (1 + Real.log y) ^ 2) := by
  have hL0 : 0 ≤ y * (1 + Real.log y) ^ 2 := by have := Real.log_nonneg hy; positivity
  have hCτ : 0 ≤ C * τ := mul_nonneg hC (by linarith)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty, Nat.cast_zero]
    norm_num; exact mul_nonneg hCτ hL0
  · exact (hcount n hpos).trans (mul_le_mul_of_nonneg_left (lsc_nlog_le hpos hn) hCτ)

theorem lsc_reduce_sharp (a : ℕ → ℝ) (P P0 C τ : ℝ) (hC : 0 ≤ C) (hP : |P| ≤ P0) (hτ : 1 ≤ τ)
    (hcount : ∀ n : ℕ, 1 ≤ n → |∑ j ∈ Finset.Icc 1 n, a j - (n : ℝ) ^ 2 / 2 * P|
      ≤ C * τ * ((n : ℝ) * (1 + Real.log n) ^ 2))
    (y : ℝ) (hy : 1 ≤ y) :
    |∑ j ∈ Finset.Icc 1 ⌊y⌋₊, a j * wSharp ((j : ℝ) / y) - y ^ 2 * (1 / 2) * P|
      ≤ (11 * C + 2 * P0) * τ * (y * (1 + Real.log y) ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  set L : ℝ := y * (1 + Real.log y) ^ 2 with hL
  have hyL : y ≤ L := by
    have : 1 ≤ (1 + Real.log y) ^ 2 := by nlinarith
    rw [hL]; nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hP00 : 0 ≤ P0 := le_trans (abs_nonneg _) hP
  have hCτL : 0 ≤ C * τ * L := mul_nonneg (mul_nonneg hC (by linarith)) hL0
  have hP0τL : 0 ≤ P0 * τ * L := mul_nonneg (mul_nonneg hP00 (by linarith)) hL0
  have hP0L : P0 * y ≤ P0 * τ * L := by
    have : y ≤ τ * L := by nlinarith
    nlinarith
  have hE := lsc_count_err a P C τ hC hτ hcount y hy
  set N := ⌊y⌋₊ with hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyN : y < N + 1 := Nat.lt_floor_add_one y
  have hS : ∑ j ∈ Finset.Icc 1 N, a j * wSharp ((j : ℝ) / y) = ∑ j ∈ Finset.Icc 1 N, a j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : (j : ℝ) ≤ y := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hj).2) hNy
    unfold wSharp
    rw [if_pos ⟨by positivity, (div_le_one hy0).mpr hjN⟩, mul_one]
  rw [hS]
  have hNN : |(N : ℝ) ^ 2 - y ^ 2| ≤ 2 * y := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [abs_le]; constructor <;> nlinarith
  set AN := ∑ j ∈ Finset.Icc 1 N, a j with hAN
  have e1 : AN - y ^ 2 * (1 / 2) * P = (AN - (N : ℝ) ^ 2 / 2 * P) + ((N : ℝ) ^ 2 - y ^ 2) / 2 * P := by ring
  rw [e1]
  have h1 := hE N hNy
  have h2 : |((N : ℝ) ^ 2 - y ^ 2) / 2 * P| ≤ P0 * y := by
    rw [abs_mul, abs_div, abs_two]
    calc |(N : ℝ) ^ 2 - y ^ 2| / 2 * |P| ≤ (2 * y) / 2 * P0 :=
          mul_le_mul (div_le_div_of_nonneg_right hNN (by norm_num)) hP (abs_nonneg _) (by positivity)
      _ = P0 * y := by ring
  calc _ ≤ |AN - (N : ℝ) ^ 2 / 2 * P| + |((N : ℝ) ^ 2 - y ^ 2) / 2 * P| := abs_add_le _ _
    _ ≤ C * τ * L + P0 * τ * L := by linarith
    _ ≤ (11 * C + 2 * P0) * τ * L := by nlinarith

theorem lsc_reduce_dyadic (a : ℕ → ℝ) (P P0 C τ : ℝ) (hC : 0 ≤ C) (hP : |P| ≤ P0) (hτ : 1 ≤ τ)
    (hcount : ∀ n : ℕ, 1 ≤ n → |∑ j ∈ Finset.Icc 1 n, a j - (n : ℝ) ^ 2 / 2 * P|
      ≤ C * τ * ((n : ℝ) * (1 + Real.log n) ^ 2))
    (y : ℝ) (hy : 1 ≤ y) :
    |∑ j ∈ Finset.Icc 1 ⌊y⌋₊, a j * wDyadic ((j : ℝ) / y) - y ^ 2 * (3 / 8) * P|
      ≤ (11 * C + 2 * P0) * τ * (y * (1 + Real.log y) ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  set L : ℝ := y * (1 + Real.log y) ^ 2 with hL
  have hyL : y ≤ L := by
    have : 1 ≤ (1 + Real.log y) ^ 2 := by nlinarith
    rw [hL]; nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hP00 : 0 ≤ P0 := le_trans (abs_nonneg _) hP
  have hCτL : 0 ≤ C * τ * L := mul_nonneg (mul_nonneg hC (by linarith)) hL0
  have hP0τL : 0 ≤ P0 * τ * L := mul_nonneg (mul_nonneg hP00 (by linarith)) hL0
  have hP0L : P0 * y ≤ P0 * τ * L := by
    have : y ≤ τ * L := by nlinarith
    nlinarith
  have hE := lsc_count_err a P C τ hC hτ hcount y hy
  set N := ⌊y⌋₊ with hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyN : y < N + 1 := Nat.lt_floor_add_one y
  set M := ⌊y / 2⌋₊ with hM
  have hMy : (M : ℝ) ≤ y / 2 := Nat.floor_le (by positivity)
  have hyM : y / 2 < M + 1 := Nat.lt_floor_add_one (y / 2)
  have hMN : M ≤ N := Nat.floor_le_floor (by linarith)
  have hS : ∑ j ∈ Finset.Icc 1 N, a j * wDyadic ((j : ℝ) / y)
      = ∑ j ∈ Finset.Icc 1 N, a j - ∑ j ∈ Finset.Icc 1 M, a j := by
    have h1 : ∀ j ∈ Finset.Icc 1 N, a j * wDyadic ((j : ℝ) / y) = if M < j then a j else 0 := by
      intro j hj
      have hjN : (j : ℝ) ≤ y := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hj).2) hNy
      unfold wDyadic
      by_cases hc : M < j
      · have hlt : (1 : ℝ) / 2 < (j : ℝ) / y := by
          rw [div_lt_div_iff₀ (by norm_num) hy0]
          have : y / 2 < j := (Nat.floor_lt (by positivity : (0 : ℝ) ≤ y / 2)).mp hc
          linarith
        rw [if_pos ⟨hlt, (div_le_one hy0).mpr hjN⟩, if_pos hc, mul_one]
      · have hnlt : ¬ ((1 : ℝ) / 2 < (j : ℝ) / y) := by
          rw [div_lt_div_iff₀ (by norm_num) hy0, not_lt]
          have hjM : j ≤ M := by omega
          have : (j : ℝ) ≤ y / 2 := le_trans (by exact_mod_cast hjM) hMy
          linarith
        rw [if_neg (fun h => hnlt h.1), if_neg hc, mul_zero]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    have hfilt : (Finset.Icc 1 N).filter (fun j => M < j) = Finset.Ioc M N := by
      ext x; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
    have hsplit : Finset.Icc 1 N = Finset.Icc 1 M ∪ Finset.Ioc M N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Ioc M N) := by
      rw [Finset.disjoint_left]; intro x hx hx'
      rw [Finset.mem_Icc] at hx; rw [Finset.mem_Ioc] at hx'; omega
    rw [hfilt]
    conv_rhs => rw [hsplit, Finset.sum_union hdisj]
    ring
  rw [hS]
  have hNN : |(N : ℝ) ^ 2 - y ^ 2| ≤ 2 * y := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [abs_le]; constructor <;> nlinarith
  have hMM : |(M : ℝ) ^ 2 - (y / 2) ^ 2| ≤ y := by
    have hM0 : (0 : ℝ) ≤ M := by positivity
    rw [abs_le]; constructor <;> nlinarith
  set AN := ∑ j ∈ Finset.Icc 1 N, a j with hAN
  set AM := ∑ j ∈ Finset.Icc 1 M, a j with hAM
  have e1 : AN - AM - y ^ 2 * (3 / 8) * P = (AN - (N : ℝ) ^ 2 / 2 * P) - (AM - (M : ℝ) ^ 2 / 2 * P)
      + (((N : ℝ) ^ 2 - y ^ 2) / 2 * P - ((M : ℝ) ^ 2 - (y / 2) ^ 2) / 2 * P) := by ring
  rw [e1]
  have h1 := hE N hNy
  have h2 := hE M (by linarith)
  have h3 : |((N : ℝ) ^ 2 - y ^ 2) / 2 * P| ≤ P0 * y := by
    rw [abs_mul, abs_div, abs_two]
    calc |(N : ℝ) ^ 2 - y ^ 2| / 2 * |P| ≤ (2 * y) / 2 * P0 :=
          mul_le_mul (div_le_div_of_nonneg_right hNN (by norm_num)) hP (abs_nonneg _) (by positivity)
      _ = P0 * y := by ring
  have h4 : |((M : ℝ) ^ 2 - (y / 2) ^ 2) / 2 * P| ≤ P0 * y := by
    rw [abs_mul, abs_div, abs_two]
    calc |(M : ℝ) ^ 2 - (y / 2) ^ 2| / 2 * |P| ≤ y / 2 * P0 :=
          mul_le_mul (div_le_div_of_nonneg_right hMM (by norm_num)) hP (abs_nonneg _) (by positivity)
      _ ≤ P0 * y := by have := mul_nonneg hP00 hy0.le; linarith
  have t1 := abs_add_le ((AN - (N : ℝ) ^ 2 / 2 * P) - (AM - (M : ℝ) ^ 2 / 2 * P))
    (((N : ℝ) ^ 2 - y ^ 2) / 2 * P - ((M : ℝ) ^ 2 - (y / 2) ^ 2) / 2 * P)
  have t2 := abs_sub (AN - (N : ℝ) ^ 2 / 2 * P) (AM - (M : ℝ) ^ 2 / 2 * P)
  have t3 := abs_sub (((N : ℝ) ^ 2 - y ^ 2) / 2 * P) (((M : ℝ) ^ 2 - (y / 2) ^ 2) / 2 * P)
  calc _ ≤ C * τ * L + C * τ * L + (P0 * y + P0 * y) := by linarith
    _ ≤ (11 * C + 2 * P0) * τ * L := by nlinarith

theorem lsc_poly_bound (y t Mv : ℝ) (hy : 1 ≤ y) (ht0 : t ≤ 0) (ht1 : -1 < t)
    (hD : (Mv - y ^ 2 / 6) * y ^ 2 = t ^ 4 / 2 + 2 * t ^ 3 / 3 - t / 6 - y ^ 3 / 3 + y ^ 2 / 3
        + y * (2 * t ^ 3 / 3 + t ^ 2 + t / 3 - 1 / 6)) :
    |Mv - y ^ 2 / 6| ≤ 3 * y := by
  have hy0 : 0 < y := by linarith
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ht3 : -1 ≤ t ^ 3 := by nlinarith
  have ht3' : t ^ 3 ≤ 0 := by nlinarith
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have ht4' : 0 ≤ t ^ 4 := by positivity
  have hy3 : -y ≤ y * t ^ 3 := by nlinarith
  have hy3' : y * t ^ 3 ≤ 0 := by nlinarith
  have hy2 : y * t ^ 2 ≤ y := by nlinarith
  have hy2' : 0 ≤ y * t ^ 2 := by positivity
  have hy1 : -y ≤ y * t := by nlinarith
  have hy1' : y * t ≤ 0 := by nlinarith
  have hyy : y ≤ y ^ 2 := by nlinarith
  have hyyy : y ^ 2 ≤ y ^ 3 := by nlinarith
  have hD' : |(Mv - y ^ 2 / 6) * y ^ 2| ≤ 3 * y ^ 3 := by
    rw [hD, abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ 2)] at hD'
  have hy2p : 0 < y ^ 2 := by positivity
  have : |Mv - y ^ 2 / 6| * y ^ 2 ≤ (3 * y) * y ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right this hy2p

theorem lsc_Mv_identity (N : ℕ) (y : ℝ) (hy0 : 0 < y) :
    ((1 - (((N + 1 : ℕ) : ℝ)) / y) ^ 2 * (N : ℝ) ^ 2
      - ∑ k ∈ Finset.range (N + 1), ((1 - (((k + 1 : ℕ) : ℝ)) / y) ^ 2 - (1 - (k : ℝ) / y) ^ 2) * (k : ℝ) ^ 2
      - y ^ 2 / 6) * y ^ 2
    = ((N : ℝ) - y) ^ 4 / 2 + 2 * ((N : ℝ) - y) ^ 3 / 3 - ((N : ℝ) - y) / 6 - y ^ 3 / 3 + y ^ 2 / 3
      + y * (2 * ((N : ℝ) - y) ^ 3 / 3 + ((N : ℝ) - y) ^ 2 + ((N : ℝ) - y) / 3 - 1 / 6) := by
  have h1 : ∀ k ∈ Finset.range (N + 1),
      ((1 - (((k + 1 : ℕ) : ℝ)) / y) ^ 2 - (1 - (k : ℝ) / y) ^ 2) * (k : ℝ) ^ 2
        = -(2 / y) * (k : ℝ) ^ 2 + 2 / y ^ 2 * (k : ℝ) ^ 3 + 1 / y ^ 2 * (k : ℝ) ^ 2 := by
    intro k _; push_cast; field_simp; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, lsc_sum_range_sq, lsc_sum_range_cube]
  push_cast
  field_simp
  ring

theorem lsc_reduce_weighted (a : ℕ → ℝ) (P P0 C τ : ℝ) (hC : 0 ≤ C) (hP : |P| ≤ P0) (hτ : 1 ≤ τ)
    (hcount : ∀ n : ℕ, 1 ≤ n → |∑ j ∈ Finset.Icc 1 n, a j - (n : ℝ) ^ 2 / 2 * P|
      ≤ C * τ * ((n : ℝ) * (1 + Real.log n) ^ 2))
    (y : ℝ) (hy : 1 ≤ y) :
    |∑ j ∈ Finset.Icc 1 ⌊y⌋₊, a j * wWeighted ((j : ℝ) / y) - y ^ 2 * (1 / 12) * P|
      ≤ (11 * C + 2 * P0) * τ * (y * (1 + Real.log y) ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  set L : ℝ := y * (1 + Real.log y) ^ 2 with hL
  have hyL : y ≤ L := by
    have : 1 ≤ (1 + Real.log y) ^ 2 := by nlinarith
    rw [hL]; nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hP00 : 0 ≤ P0 := le_trans (abs_nonneg _) hP
  have hCτL : 0 ≤ C * τ * L := mul_nonneg (mul_nonneg hC (by linarith)) hL0
  have hP0τL : 0 ≤ P0 * τ * L := mul_nonneg (mul_nonneg hP00 (by linarith)) hL0
  have hP0L : P0 * y ≤ P0 * τ * L := by
    have : y ≤ τ * L := by nlinarith
    nlinarith
  have hE := lsc_count_err a P C τ hC hτ hcount y hy
  set N := ⌊y⌋₊ with hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyN : y < N + 1 := Nat.lt_floor_add_one y
  set A : ℕ → ℝ := fun n => ∑ j ∈ Finset.Icc 1 n, a j with hAdef
  set a' : ℕ → ℝ := fun q => if q = 0 then 0 else a q with ha'
  set f : ℕ → ℝ := fun k => (1 - (k : ℝ) / y) ^ 2 with hf
  have hA_range : ∀ k : ℕ, ∑ q ∈ Finset.range (k + 1), a' q = A k := by
    intro k
    have h0 : a' 0 = 0 := by simp [ha']
    have hh := lsc_sum_Icc_one_eq_range a' k
    rw [h0, sub_zero] at hh
    rw [← hh]
    simp only [hAdef]
    apply Finset.sum_congr rfl
    intro q hq
    have : q ≠ 0 := by rw [Finset.mem_Icc] at hq; omega
    simp [ha', this]
  have hS : ∑ j ∈ Finset.Icc 1 N, a j * wWeighted ((j : ℝ) / y)
      = f (N + 1) * A N - ∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * A k := by
    have h1 : ∑ j ∈ Finset.Icc 1 N, a j * wWeighted ((j : ℝ) / y)
        = ∑ q ∈ Finset.range (N + 1), f q * a' q := by
      have hh := lsc_sum_Icc_one_eq_range (fun q => f q * a' q) N
      have h0 : f 0 * a' 0 = 0 := by simp [ha']
      rw [h0, sub_zero] at hh
      rw [← hh]
      apply Finset.sum_congr rfl
      intro j hj
      have hj0 : j ≠ 0 := by rw [Finset.mem_Icc] at hj; omega
      have hjN : (j : ℝ) ≤ y := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hj).2) hNy
      simp only [wWeighted, hf, ha', if_neg hj0]
      rw [if_pos ⟨by positivity, (div_le_one hy0).mpr hjN⟩]
      ring
    rw [h1, lsc_abel_range f a' (N + 1)]
    simp only [hA_range]
  rw [hS]
  set E : ℕ → ℝ := fun k => A k - (k : ℝ) ^ 2 / 2 * P with hEdef
  have hEb : ∀ k ∈ Finset.range (N + 1), |E k| ≤ C * τ * L := by
    intro k hk
    have hkN : (k : ℝ) ≤ y := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hNy
    exact hE k hkN
  have hdf : ∀ k : ℕ, f (k + 1) - f k = -(2 / y) + (2 * (k : ℝ) + 1) / y ^ 2 := by
    intro k; simp only [hf]; push_cast; field_simp; ring
  have hdf_abs : ∀ k ∈ Finset.range (N + 1), |f (k + 1) - f k| ≤ 5 / y := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hdf k]
    have h2 : (2 * (k : ℝ) + 1) / y ^ 2 ≤ 3 / y := by
      rw [div_le_div_iff₀ (by positivity) hy0]; nlinarith
    have h3 : 0 ≤ (2 * (k : ℝ) + 1) / y ^ 2 := by positivity
    have h4 : 0 ≤ 2 / y := by positivity
    have h5 : 2 / y + 3 / y = 5 / y := by ring
    rw [abs_le]; constructor <;> linarith
  have hfN : |f (N + 1)| ≤ 1 := by
    simp only [hf]
    rw [abs_of_nonneg (sq_nonneg _)]
    push_cast
    have h1 : 1 < ((N : ℝ) + 1) / y := by rw [lt_div_iff₀ hy0]; linarith
    have h2 : ((N : ℝ) + 1) / y ≤ 2 := by rw [div_le_iff₀ hy0]; linarith
    nlinarith
  set Mv : ℝ := f (N + 1) * (N : ℝ) ^ 2 - ∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * (k : ℝ) ^ 2
    with hMv
  set t : ℝ := (N : ℝ) - y with htdef
  have ht0 : t ≤ 0 := by linarith
  have ht1 : -1 < t := by linarith
  have hD : (Mv - y ^ 2 / 6) * y ^ 2
      = t ^ 4 / 2 + 2 * t ^ 3 / 3 - t / 6 - y ^ 3 / 3 + y ^ 2 / 3
        + y * (2 * t ^ 3 / 3 + t ^ 2 + t / 3 - 1 / 6) := lsc_Mv_identity N y hy0
  have hMvb : |Mv - y ^ 2 / 6| ≤ 3 * y := lsc_poly_bound y t Mv hy ht0 ht1 hD
  have hsplit : f (N + 1) * A N - ∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * A k - y ^ 2 * (1 / 12) * P
      = P / 2 * (Mv - y ^ 2 / 6)
        + (f (N + 1) * E N - ∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * E k) := by
    have hAE : ∀ k, A k = (k : ℝ) ^ 2 / 2 * P + E k := by intro k; simp only [hEdef]; ring
    rw [hMv]
    simp only [hAE, mul_add, Finset.sum_add_distrib]
    rw [show ∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * ((k : ℝ) ^ 2 / 2 * P)
        = P / 2 * ∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * (k : ℝ) ^ 2 by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
    ring
  rw [hsplit]
  have hErr : |f (N + 1) * E N - ∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * E k|
      ≤ 11 * (C * τ * L) := by
    have hEN : |E N| ≤ C * τ * L := hE N hNy
    have h1 : |f (N + 1) * E N| ≤ C * τ * L := by
      rw [abs_mul]
      calc |f (N + 1)| * |E N| ≤ 1 * (C * τ * L) := mul_le_mul hfN hEN (abs_nonneg _) (by norm_num)
        _ = C * τ * L := one_mul _
    have h2 : |∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * E k| ≤ 10 * (C * τ * L) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ k ∈ Finset.range (N + 1), |(f (k + 1) - f k) * E k| ≤ 5 / y * (C * τ * L) := by
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (hdf_abs k hk) (hEb k hk) (abs_nonneg _) (by positivity)
      refine (Finset.sum_le_sum hb).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hN2 : ((N + 1 : ℕ) : ℝ) ≤ 2 * y := by push_cast; linarith
      calc ((N + 1 : ℕ) : ℝ) * (5 / y * (C * τ * L)) ≤ (2 * y) * (5 / y * (C * τ * L)) :=
            mul_le_mul_of_nonneg_right hN2 (by positivity)
        _ = 10 * (C * τ * L) := by field_simp; ring
    have := abs_sub (f (N + 1) * E N) (∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * E k)
    linarith
  have hMain : |P / 2 * (Mv - y ^ 2 / 6)| ≤ 2 * P0 * y := by
    rw [abs_mul, abs_div, abs_two]
    calc |P| / 2 * |Mv - y ^ 2 / 6| ≤ P0 / 2 * (3 * y) :=
          mul_le_mul (div_le_div_of_nonneg_right hP (by norm_num)) hMvb (abs_nonneg _) (by positivity)
      _ ≤ 2 * P0 * y := by nlinarith
  calc _ ≤ |P / 2 * (Mv - y ^ 2 / 6)|
        + |f (N + 1) * E N - ∑ k ∈ Finset.range (N + 1), (f (k + 1) - f k) * E k| := abs_add_le _ _
    _ ≤ 2 * P0 * y + 11 * (C * τ * L) := add_le_add hMain hErr
    _ ≤ (11 * C + 2 * P0) * τ * L := by nlinarith

/-! ### `line_sum_asymp` for the three families, in closed form -/

theorem lsc_one_le_tau (e : ℕ) (he : 1 ≤ e) : (1 : ℝ) ≤ (e.divisors.card : ℝ) := by
  have : 1 ≤ e.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  exact_mod_cast this

theorem lsc_abs_PiEPl_le (e : ℕ) : |PiEPl e| ≤ |Pi0X| := by
  unfold PiEPl
  have hb : ∀ p ∈ e.primeFactors, 1 ≤ 1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := (lsc_p_facts p (Nat.prime_of_mem_primeFactors hp)).1
    have : 1 / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have h0 : 0 ≤ ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)⁻¹ :=
    Finset.prod_nonneg (fun p hp => inv_nonneg.mpr (by linarith [hb p hp]))
  have h1 : ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)⁻¹ ≤ 1 :=
    Finset.prod_le_one (fun p hp => inv_nonneg.mpr (by linarith [hb p hp]))
      (fun p hp => inv_le_one_of_one_le₀ (hb p hp))
  rw [abs_mul, abs_of_nonneg h0]
  calc |Pi0X| * ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)⁻¹ ≤ |Pi0X| * 1 :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |Pi0X| := mul_one _

theorem lsc_abs_PiEQp_le (e : ℕ) : |PiEQp e| ≤ 1 := by
  unfold PiEQp
  have hb : ∀ p ∈ e.primeFactors, 1 ≤ 1 + 1 / (p : ℝ) := by
    intro p _; have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith
  have h0 : 0 ≤ ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ))⁻¹ :=
    Finset.prod_nonneg (fun p hp => inv_nonneg.mpr (by linarith [hb p hp]))
  have h1 : ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ))⁻¹ ≤ 1 :=
    Finset.prod_le_one (fun p hp => inv_nonneg.mpr (by linarith [hb p hp]))
      (fun p hp => inv_le_one_of_one_le₀ (hb p hp))
  have hpi : 6 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have hpi0 : 0 < 6 / Real.pi ^ 2 := by positivity
  rw [abs_mul, abs_of_nonneg h0, abs_of_pos hpi0]
  calc 6 / Real.pi ^ 2 * ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ))⁻¹ ≤ 1 * 1 :=
        mul_le_mul hpi h1 h0 (by norm_num)
    _ = 1 := mul_one _

/-- `line_sum_asymp`, sharp family. -/
theorem lsc_line_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 1 ≤ r → ∀ e : ℕ, 1 ≤ e → ∀ y : ℝ, 1 ≤ y →
    |∑ j ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient j : ℝ) * EcoefPl r j e * wSharp ((j : ℝ) / y)
      - y ^ 2 * (1 / 2) * PiEPl e| ≤ C * (e.divisors.card : ℝ) * (y * (1 + Real.log y) ^ 2) := by
  obtain ⟨C, hC, hcount⟩ := lsc_count_pl
  refine ⟨11 * C + 2 * |Pi0X|, by positivity, ?_⟩
  intro r hr e he y hy
  exact lsc_reduce_sharp (fun j => (Nat.totient j : ℝ) * EcoefPl r j e) (PiEPl e) |Pi0X| C _ hC
    (lsc_abs_PiEPl_le e) (lsc_one_le_tau e he) (fun n hn => hcount r hr e he n hn) y hy

/-- `line_sum_asymp`, dyadic family. -/
theorem lsc_line_dyadic : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 1 ≤ r → ∀ e : ℕ, 1 ≤ e → ∀ y : ℝ, 1 ≤ y →
    |∑ j ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient j : ℝ) * EcoefPl r j e * wDyadic ((j : ℝ) / y)
      - y ^ 2 * (3 / 8) * PiEPl e| ≤ C * (e.divisors.card : ℝ) * (y * (1 + Real.log y) ^ 2) := by
  obtain ⟨C, hC, hcount⟩ := lsc_count_pl
  refine ⟨11 * C + 2 * |Pi0X|, by positivity, ?_⟩
  intro r hr e he y hy
  exact lsc_reduce_dyadic (fun j => (Nat.totient j : ℝ) * EcoefPl r j e) (PiEPl e) |Pi0X| C _ hC
    (lsc_abs_PiEPl_le e) (lsc_one_le_tau e he) (fun n hn => hcount r hr e he n hn) y hy

/-- `line_sum_asymp`, weighted family. -/
theorem lsc_line_weighted : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 1 ≤ r → ∀ e : ℕ, 1 ≤ e → ∀ y : ℝ, 1 ≤ y →
    |∑ j ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient j : ℝ) * EcoefQp r j e * wWeighted ((j : ℝ) / y)
      - y ^ 2 * (1 / 12) * PiEQp e| ≤ C * (e.divisors.card : ℝ) * (y * (1 + Real.log y) ^ 2) := by
  obtain ⟨C, hC, hcount⟩ := lsc_count_qp
  refine ⟨11 * C + 2 * 1, by positivity, ?_⟩
  intro r hr e he y hy
  exact lsc_reduce_weighted (fun j => (Nat.totient j : ℝ) * EcoefQp r j e) (PiEQp e) 1 C _ hC
    (lsc_abs_PiEQp_le e) (lsc_one_le_tau e he) (fun n hn => hcount r hr e he n hn) y hy

end TrackF
end ZetaShell
