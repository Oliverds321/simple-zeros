/-
L711_QphiSum (L7_11, 28 Sep 2026): inputs for `Hw_normalisation` (A2N), weighted family (`q/φ` kind).

* `qphiA N = Σ_{1≤q≤N} (q/φ(q)) φ*(q)` and `qphiA_bound`:
  `|qphiA N − (𝔖/2) N²| ≤ C N (1 + log N)²` for `N ≥ 1`. Paper proof: L8_8 second reader A, item 3
  (`q/φ` kind): `φ*(q)/φ(q) = (1 * h)(q)` with `h(p) = −1/(p−1)`, `h(p²) = 1/(p(p−1))`, `h(p^k) = 0` (`k ≥ 3`),
  `Σ_d h(d)/d = ∏_p (1 − p⁻² − p⁻³) = 𝔖`, `Σ_{d≤x}|h(d)| ≪ log x`; the error is even `O(N log N)`.
  ALL PROVED (L7_11, no sorry). `qphiA_bound` is derived from three sub-nodes about the explicit function `hq`:
  `hq_conv` (`1 * hq = φ*/φ`, PROVED here), `hq_abs_partial` (PROVED here) (`Σ_{f≤N}|hq f| ≤ C(1+log N)²`) and `hq_partial_Sconst` (derived from `hq_hasSum`, the Euler product via Mathlib's `EulerProduct.eulerProduct_hasProd`, and `hq_tail`)
  (`|Σ_{f≤N} hq(f)/f − 𝔖| ≤ C(1+log N)²/N`: the Euler product plus the tail), via L7_8's proved
  `sum_mul_conv_approx` (A2P_S2_ConvSum). All three tested: `numerics/hq_test.py`, `hq_test.out`.
* proved helpers (no sorry): summation by parts on `range` (`abel_range`), `Icc 1 n` vs `range (n+1)`
  (`sum_Icc_one_eq_range`), the power sums `Σ_{k<n} k²`, `Σ_{k<n} k³`, and two logarithm inequalities for `x ≥ 2`.
-/
import ZetaShell.Skeleton.A2P_LineProfile
import ZetaShell.Lemma2.A2P_S2_ConvSum
import ZetaQ.Normalisation

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- `Σ_{1≤q≤N} (q/φ(q)) φ*(q)`. -/
def qphiA (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 N, ((q : ℝ) / (Nat.totient q : ℝ)) * (ZetaQ.phiStar q : ℝ)

theorem sum_Icc_one_eq_range (g : ℕ → ℝ) (n : ℕ) :
    ∑ q ∈ Finset.Icc 1 n, g q = ∑ q ∈ Finset.range (n + 1), g q - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (n + 1)]
    ring

/-- local factor of `h = φ*/φ ∗ μ` at `p^k`. -/
def hloc (p k : ℕ) : ℝ :=
  if k = 1 then -1 / ((p : ℝ) - 1) else if k = 2 then 1 / ((p : ℝ) * ((p : ℝ) - 1)) else 0

/-- the multiplicative function `h` with `1 * h = φ*/φ`. -/
def hq (d : ℕ) : ℝ := if d = 0 then 0 else ∏ p ∈ d.primeFactors, hloc p (d.factorization p)

/-! ### Proof of the sub-node `hq_conv` (L7_11): both sides are multiplicative arithmetic functions (`h` by its
product formula; `φ* = μ ⋆ φ` by the trunk's `ZetaQ.Normalisation.phiStar_eq_moebius_sum`, `φ*/φ` by `pdiv`) and
they agree at prime powers (`φ*(p^{m+1}) = φ(p^{m+1}) − φ(p^m)`). -/

section HqConv
open ArithmeticFunction

local notation "μR" => ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
local notation "ζR" => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

theorem hq_zero : hq 0 = 0 := by simp [hq]

theorem hq_one : hq 1 = 1 := by simp [hq]

theorem hq_eq_prod (d : ℕ) (hd : d ≠ 0) : hq d = d.factorization.prod hloc := by
  simp only [hq, if_neg hd]
  rfl

theorem hq_mul (m n : ℕ) (hmn : m.Coprime n) : hq (m * n) = hq m * hq n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hq_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hq_zero]
  rw [hq_eq_prod _ (by positivity), hq_eq_prod _ hm.ne', hq_eq_prod _ hn.ne',
    Nat.factorization_mul hm.ne' hn.ne']
  apply Finsupp.prod_add_index_of_disjoint
  simpa using hmn.disjoint_primeFactors

theorem hq_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) : hq (p ^ k) = hloc p k := by
  have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [hq, if_neg hne]
  rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton, hp.factorization_pow,
    Finsupp.single_eq_same]

def hqAF : ArithmeticFunction ℝ := ⟨hq, hq_zero⟩

theorem hqAF_apply (n : ℕ) : hqAF n = hq n := rfl

theorem hqAF_mult : IsMultiplicative hqAF :=
  ⟨by rw [hqAF_apply, hq_one], fun {m n} h => by simp only [hqAF_apply]; exact hq_mul m n h⟩

def totR : ArithmeticFunction ℝ := ⟨fun n => (Nat.totient n : ℝ), by simp⟩

theorem totR_apply (n : ℕ) : totR n = (Nat.totient n : ℝ) := rfl

theorem totR_mult : IsMultiplicative totR :=
  ⟨by simp [totR_apply], fun {m n} h => by simp only [totR_apply]; rw [Nat.totient_mul h]; push_cast; ring⟩

def psR : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else (ZetaQ.phiStar n : ℝ), by simp⟩

theorem psR_apply (n : ℕ) : psR n = if n = 0 then 0 else (ZetaQ.phiStar n : ℝ) := rfl

theorem psR_eq : psR = μR * totR := by
  ext n
  by_cases hn : n = 0
  · subst hn; simp
  rw [psR_apply, if_neg hn, mul_apply]
  have h := ZetaQ.Normalisation.phiStar_eq_moebius_sum n (by omega)
  have h' : (ZetaQ.phiStar n : ℝ)
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ) * (Nat.totient d : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    simp only [Int.cast_natCast] at this
    rw [this]; push_cast; rfl
  rw [h', Nat.sum_divisorsAntidiagonal' (fun a b => μR a * totR b)]
  apply Finset.sum_congr rfl
  intro d _
  rw [intCoe_apply, totR_apply]

theorem psR_mult : IsMultiplicative psR := by
  rw [psR_eq]
  exact isMultiplicative_moebius.intCast.mul totR_mult

theorem psR_prime_pow_succ (p m : ℕ) (hp : p.Prime) :
    psR (p ^ (m + 1)) = (Nat.totient (p ^ (m + 1)) : ℝ) - (Nat.totient (p ^ m) : ℝ) := by
  rw [psR_eq, mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => μR a * totR b),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ k ∈ Finset.range m,
      μR (p ^ (k + 1 + 1)) * totR (p ^ (m + 1) / p ^ (k + 1 + 1)) = 0 := by
    intro k _
    rw [intCoe_apply, moebius_apply_prime_pow hp (by omega)]
    simp
  rw [Finset.sum_eq_zero hz, intCoe_apply, intCoe_apply, pow_zero, moebius_apply_one,
    moebius_apply_prime_pow hp (by omega : 0 + 1 ≠ 0)]
  simp only [totR_apply]
  rw [Nat.pow_div (by omega) hp.pos, Nat.div_one]
  have e : m + 1 - (0 + 1) = m := by omega
  rw [e]
  norm_num <;> ring

theorem hq_conv_AF : (ζR * hqAF) = pdiv psR totR := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_zeta.natCast.mul hqAF_mult) _
    (psR_mult.pdiv totR_mult)]
  intro p i hp
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp, pdiv_apply]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rcases i with _ | m
  · simp [hqAF_apply, hq_one, psR_mult.map_one, totR_mult.map_one]
  rw [psR_prime_pow_succ p m hp]
  rcases m with _ | m
  · -- i = 1
    have hq_p : hq p = -1 / ((p : ℝ) - 1) := by
      have := hq_prime_pow p 1 hp one_ne_zero
      rw [pow_one] at this
      rw [this]; simp [hloc]
    simp only [zero_add, pow_one, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
      pow_zero, hqAF_apply, hq_one, totR_apply, Nat.totient_prime hp, Nat.totient_one]
    rw [hq_p]
    push_cast [Nat.cast_sub hp.one_le]
    field_simp
    ring
  · -- i = m + 2
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : ∀ k ∈ Finset.range m, hqAF (p ^ (k + 1 + 1 + 1)) = 0 := by
      intro k _
      rw [hqAF_apply, hq_prime_pow p _ hp (by omega)]
      simp [hloc]
    rw [Finset.sum_eq_zero hz, hqAF_apply, hqAF_apply, hqAF_apply, pow_zero, hq_one,
      hq_prime_pow p _ hp (by omega), hq_prime_pow p _ hp (by omega), totR_apply,
      Nat.totient_prime_pow hp (by omega), Nat.totient_prime_pow hp (by omega)]
    simp only [hloc, zero_add, show (0 + 1 + 1 = 2) from rfl, if_true, show ((2 : ℕ) = 1) = False by decide,
      if_false]
    have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp.one_le]; simp
    push_cast [hsub]
    try simp only [Nat.add_sub_cancel]
    have hpm : (p : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [pow_succ]
    field_simp
    ring

end HqConv

/-- **Sub-node `hq_conv` (PROVED).** `Σ_{f|j} h(f) = φ*(j)/φ(j)` for `j ≥ 1`. -/
theorem hq_conv : ∀ j : ℕ, 1 ≤ j →
    ∑ f ∈ j.divisors, hq f = (ZetaQ.phiStar j : ℝ) / (Nat.totient j : ℝ) := by
  intro j hj
  have h := congrArg (fun F : ArithmeticFunction ℝ => F j) hq_conv_AF
  simp only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.pdiv_apply, hqAF_apply, psR_apply,
    totR_apply] at h
  rw [h, if_neg (by omega)]

/-! ### Proof of the sub-node `hq_abs_partial` (L7_11): `|h(d)| ≤ τ(d)/d`, `Σ_{d≤N} τ(d)/d ≤ H_N²`,
`H_N ≤ 1 + log N`. -/

theorem abs_hloc_le (p k : ℕ) (hp : p.Prime) :
    |hloc p k| ≤ ((k : ℝ) + 1) / (p : ℝ) ^ k := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  unfold hloc
  split_ifs with h1 h2
  · subst h1
    rw [abs_div, abs_neg, abs_one, abs_of_pos hp1, div_le_div_iff₀ hp1 (by positivity)]
    norm_num <;> nlinarith
  · subst h2
    rw [abs_div, abs_one, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num <;> nlinarith
  · rw [abs_zero]; positivity

theorem abs_hq_le (d : ℕ) (hd : d ≠ 0) : |hq d| ≤ (d.divisors.card : ℝ) / d := by
  rw [hq_eq_prod d hd]
  unfold Finsupp.prod
  rw [Nat.support_factorization, Finset.abs_prod]
  have hcard := Nat.card_divisors hd
  have hself := Nat.prod_factorization_pow_eq_self hd
  unfold Finsupp.prod at hself
  rw [Nat.support_factorization] at hself
  have hle : ∏ p ∈ d.primeFactors, |hloc p (d.factorization p)|
      ≤ ∏ p ∈ d.primeFactors, (((d.factorization p : ℝ) + 1) / (p : ℝ) ^ (d.factorization p)) :=
    Finset.prod_le_prod (fun p _ => abs_nonneg _)
      (fun p hp => abs_hloc_le p _ (Nat.prime_of_mem_primeFactors hp))
  refine hle.trans (le_of_eq ?_)
  rw [Finset.prod_div_distrib]
  have hnum : (∏ p ∈ d.primeFactors, ((d.factorization p : ℝ) + 1)) = (d.divisors.card : ℝ) := by
    rw [hcard]; push_cast; rfl
  have hden : (∏ p ∈ d.primeFactors, (p : ℝ) ^ (d.factorization p)) = (d : ℝ) := by
    conv_rhs => rw [← hself]
    push_cast; rfl
  rw [hnum, hden]

theorem sum_card_divisors_mul_le (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hwm : ∀ a m, w (a * m) = w a * w m)
    (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) * w d ≤ (∑ a ∈ Finset.Icc 1 N, w a) ^ 2 := by
  have h1 : ∀ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) * w d = ∑ a ∈ d.divisors, w d := by
    intro d _; rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 N) (s' := fun a => (Finset.Icc 1 N).filter (fun d => a ∣ d))]
  · rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hswap : ∑ d ∈ (Finset.Icc 1 N).filter (fun d => a ∣ d), w d
        = ∑ b ∈ Finset.Icc 1 (N / a), w a * w b := by
      symm
      apply Finset.sum_nbij' (fun m => a * m) (fun j => j / a)
      · intro m hm
        rw [Finset.mem_Icc] at hm
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by nlinarith [hm.1], ?_⟩, dvd_mul_right a m⟩
        have := Nat.mul_le_of_le_div a m N hm.2
        linarith [this, Nat.mul_comm m a]
      · intro j hj
        rw [Finset.mem_filter, Finset.mem_Icc] at hj
        rw [Finset.mem_Icc]
        obtain ⟨⟨hj1, hjN⟩, hfj⟩ := hj
        obtain ⟨c, rfl⟩ := hfj
        rw [Nat.mul_div_cancel_left c (by omega)]
        constructor
        · rcases Nat.eq_zero_or_pos c with h | h
          · subst h; simp at hj1
          · exact h
        · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hjN)
      · intro m _
        exact Nat.mul_div_cancel_left m (by omega)
      · intro j hj
        rw [Finset.mem_filter] at hj
        exact Nat.mul_div_cancel' hj.2
      · intro m _
        rw [hwm]
    rw [hswap]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      exact ⟨hb.1, le_trans hb.2 (Nat.div_le_self N a)⟩
    · intro b _ _; exact mul_nonneg (hw0 a) (hw0 b)
  · intro d a
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, had, _⟩
      have ha1 : 1 ≤ a := Nat.pos_of_dvd_of_pos had (by omega)
      have haN : a ≤ N := le_trans (Nat.le_of_dvd (by omega) had) hdN
      exact ⟨⟨⟨hd1, hdN⟩, had⟩, ha1, haN⟩
    · rintro ⟨⟨⟨hd1, hdN⟩, had⟩, _, _⟩
      exact ⟨⟨hd1, hdN⟩, had, by omega⟩

theorem sum_card_divisors_mul_eq (w : ℕ → ℝ) (hwm : ∀ a m, w (a * m) = w a * w m) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) * w d
      = ∑ a ∈ Finset.Icc 1 N, w a * ∑ b ∈ Finset.Icc 1 (N / a), w b := by
  have h1 : ∀ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) * w d = ∑ a ∈ d.divisors, w d := by
    intro d _; rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 N) (s' := fun a => (Finset.Icc 1 N).filter (fun d => a ∣ d))]
  · apply Finset.sum_congr rfl
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    rw [Finset.mul_sum]
    symm
    apply Finset.sum_nbij' (fun m => a * m) (fun j => j / a)
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith [hm.1], ?_⟩, dvd_mul_right a m⟩
      have := Nat.mul_le_of_le_div a m N hm.2
      linarith [this, Nat.mul_comm m a]
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]
      obtain ⟨⟨hj1, hjN⟩, hfj⟩ := hj
      obtain ⟨c, rfl⟩ := hfj
      rw [Nat.mul_div_cancel_left c (by omega)]
      constructor
      · rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at hj1
        · exact h
      · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hjN)
    · intro m _
      exact Nat.mul_div_cancel_left m (by omega)
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact Nat.mul_div_cancel' hj.2
    · intro m _
      rw [hwm]
  · intro d a
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, had, _⟩
      have ha1 : 1 ≤ a := Nat.pos_of_dvd_of_pos had (by omega)
      have haN : a ≤ N := le_trans (Nat.le_of_dvd (by omega) had) hdN
      exact ⟨⟨⟨hd1, hdN⟩, had⟩, ha1, haN⟩
    · rintro ⟨⟨⟨hd1, hdN⟩, had⟩, _, _⟩
      exact ⟨⟨hd1, hdN⟩, had, by omega⟩

/-- `Σ_{L<b≤M} b⁻² ≤ 1/L` (telescoping). -/
theorem inv_sq_tail (L M : ℕ) (hL : 1 ≤ L) : ∑ b ∈ Finset.Ioc L M, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 1 / L := by
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

theorem inv_sq_partial_le_two (X : ℕ) : ∑ b ∈ Finset.Icc 1 X, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  have hI : Finset.Icc 1 X = insert 1 (Finset.Ioc 1 X) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [hI, Finset.sum_insert (by simp)]
  have := inv_sq_tail 1 X le_rfl
  norm_num at this ⊢
  linarith

theorem sum_card_divisors_div_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) / d ≤ (∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / a) ^ 2 := by
  have h := sum_card_divisors_mul_le (fun d : ℕ => 1 / (d : ℝ)) (fun d => by positivity)
    (fun a m => by push_cast; rw [one_div_mul_one_div]) N
  have e : ∀ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) / d = (d.divisors.card : ℝ) * (1 / (d : ℝ)) := by
    intro d _; ring
  rw [Finset.sum_congr rfl e]
  exact h

theorem sum_inv_le_one_add_log (N : ℕ) :
    ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / a ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- **Sub-node `hq_abs_partial` (PROVED).** `Σ_{f≤N} |h(f)| ≤ (1 + log N)²` (constant 1). -/
theorem hq_abs_partial : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ f ∈ Finset.Icc 1 N, |hq f| ≤ C * (1 + Real.log N) ^ 2 := by
  refine ⟨1, by norm_num, ?_⟩
  intro N _
  have h1 : ∑ f ∈ Finset.Icc 1 N, |hq f| ≤ ∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) / d :=
    Finset.sum_le_sum (fun d hd => abs_hq_le d (by rw [Finset.mem_Icc] at hd; omega))
  have h2 := sum_card_divisors_div_le N
  have h3 := sum_inv_le_one_add_log N
  have h0 : 0 ≤ ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / a := Finset.sum_nonneg (fun a _ => by positivity)
  have h4 : (∑ a ∈ Finset.Icc 1 N, (1 : ℝ) / a) ^ 2 ≤ (1 + Real.log N) ^ 2 := pow_le_pow_left₀ h0 h3 2
  linarith

/-- **Sub-node (PROVED).** The Euler product: `Σ_{d≥1} h(d)/d = ∏_p (1 − p⁻² − p⁻³) = 𝔖` (local factor
`1 + h(p)/p + h(p²)/p² = 1 − p⁻² − p⁻³`; route: Mathlib's `EulerProduct.eulerProduct_tprod` for the multiplicative
`d ↦ h(d)/d`, summable since `|h(d)|/d ≤ τ(d)/d²`, `abs_hq_le`). -/
theorem hq_hasSum : HasSum (fun d : ℕ => hq d / (d : ℝ)) Sconst := by
  set f : ℕ → ℝ := fun d => hq d / (d : ℝ) with hf
  -- summability: `|h(d)/d| ≤ τ(d)/d²` and `Σ_{d≤N} τ(d)/d² ≤ (Σ_a a⁻²)²`
  have hz : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr one_lt_two
  set Z : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ 2 with hZ
  have hτ : Summable (fun d : ℕ => (d.divisors.card : ℝ) * (1 / (d : ℝ) ^ 2)) := by
    refine summable_of_sum_range_le (c := Z ^ 2) (fun d => by positivity) (fun n => ?_)
    have h1 := sum_Icc_one_eq_range (fun d : ℕ => (d.divisors.card : ℝ) * (1 / (d : ℝ) ^ 2)) (n - 1)
    have h2 := sum_card_divisors_mul_le (fun d : ℕ => 1 / (d : ℝ) ^ 2) (fun d => by positivity)
      (fun a m => by push_cast; rw [mul_pow, one_div_mul_one_div]) (n - 1)
    have h3 : ∑ a ∈ Finset.Icc 1 (n - 1), 1 / (a : ℝ) ^ 2 ≤ Z :=
      hz.sum_le_tsum _ (fun i _ => by positivity)
    have h4 : 0 ≤ ∑ a ∈ Finset.Icc 1 (n - 1), 1 / (a : ℝ) ^ 2 := Finset.sum_nonneg (fun a _ => by positivity)
    have h5 := pow_le_pow_left₀ h4 h3 2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; positivity
    · have e : n - 1 + 1 = n := by omega
      rw [e] at h1
      simp only [Nat.cast_zero, Finset.card_empty, Nat.divisors_zero, zero_mul] at h1
      linarith
  have hsum : Summable (fun d : ℕ => ‖f d‖) := by
    refine Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => ?_) hτ
    rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [hf]
    · simp only [hf]
      rw [abs_div, Nat.abs_cast]
      have := abs_hq_le d hd.ne'
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
      calc |hq d| / (d : ℝ) ≤ (d.divisors.card : ℝ) / d / d := by
            exact div_le_div_of_nonneg_right this hd0.le
        _ = (d.divisors.card : ℝ) * (1 / (d : ℝ) ^ 2) := by field_simp
  have hf1 : f 1 = 1 := by simp [hf, hq_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hf]
    rw [hq_mul m n hmn, Nat.cast_mul, mul_div_mul_comm]
  have hf0 : f 0 = 0 := by simp [hf]
  have hprod := EulerProduct.eulerProduct_hasProd hf1 hmul hsum hf0
  -- the local factors
  have hloc_eq : (fun p : Nat.Primes => ∑' e : ℕ, f ((p : ℕ) ^ e))
      = (fun p : Nat.Primes => 1 - 1 / ((p : ℕ) : ℝ) ^ 2 - 1 / ((p : ℕ) : ℝ) ^ 3) := by
    funext p
    have hp := p.2
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp.two_le
    have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by linarith
    have hp1 : ((p : ℕ) : ℝ) - 1 ≠ 0 := by linarith
    rw [tsum_eq_sum (s := Finset.range 3)]
    · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, hf,
        Nat.cast_one, hq_one, div_one, pow_one]
      have ha : hq (p : ℕ) = -1 / (((p : ℕ) : ℝ) - 1) := by
        have := hq_prime_pow (p : ℕ) 1 hp one_ne_zero
        rw [pow_one] at this
        rw [this]; simp [hloc]
      have hb : hq ((p : ℕ) ^ 2) = 1 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1)) := by
        rw [hq_prime_pow _ 2 hp two_ne_zero]; simp only [hloc]; norm_num
      rw [ha, hb]
      push_cast
      field_simp
      ring
    · intro e he
      simp only [Finset.mem_range, not_lt] at he
      simp only [hf]
      rw [hq_prime_pow _ e hp (by omega)]
      simp only [hloc]
      rw [if_neg (by omega), if_neg (by omega), zero_div]
  rw [hloc_eq] at hprod
  have hS : Sconst = ∑' n, f n := hprod.tprod_eq
  rw [hS]
  exact (hsum.of_norm).hasSum

/-- **Sub-node (PROVED).** The tail: `Σ_{N<f≤M} |h(f)|/f ≤ C (1 + log N)²/N` for all `M` (route: `|h(f)| ≤ τ(f)/f`,
`Σ_{ab>N} (ab)⁻² ≤ Σ_a a⁻² min(2, 2a/N) ≪ (1 + log N)/N`). -/
theorem hq_tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ,
    ∑ f ∈ Finset.Ioc N M, |hq f| / (f : ℝ) ≤ C * (1 + Real.log N) ^ 2 / N := by
  refine ⟨4, by norm_num, fun N hN M => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  set w : ℕ → ℝ := fun d => 1 / (d : ℝ) ^ 2 with hw
  have hwm : ∀ a m, w (a * m) = w a * w m := fun a m => by
    simp only [hw]; push_cast; rw [mul_pow, one_div_mul_one_div]
  have h1 : ∑ f ∈ Finset.Ioc N M, |hq f| / (f : ℝ) ≤ ∑ f ∈ Finset.Ioc N M, (f.divisors.card : ℝ) * w f := by
    apply Finset.sum_le_sum
    intro f hf
    have hf0 : f ≠ 0 := by rw [Finset.mem_Ioc] at hf; omega
    have hfR : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero hf0
    have := abs_hq_le f hf0
    calc |hq f| / (f : ℝ) ≤ (f.divisors.card : ℝ) / f / f := div_le_div_of_nonneg_right this hfR.le
      _ = (f.divisors.card : ℝ) * w f := by simp only [hw]; field_simp
  refine h1.trans ?_
  have hbound : 0 ≤ 4 * (1 + Real.log N) ^ 2 / N := by positivity
  by_cases hMN : M ≤ N
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; exact hbound
  push_neg at hMN
  set g : ℕ → ℝ := fun f => (f.divisors.card : ℝ) * w f with hg
  set S : ℕ → ℝ := fun X => ∑ b ∈ Finset.Icc 1 X, w b with hS
  have i1 : ∀ X : ℕ, Finset.Icc 1 X = Finset.Ioc 0 X := fun X => by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have htail : ∑ f ∈ Finset.Ioc N M, g f = ∑ f ∈ Finset.Icc 1 M, g f - ∑ f ∈ Finset.Icc 1 N, g f := by
    have hc := Finset.sum_Ioc_consecutive g (Nat.zero_le N) hMN.le
    rw [i1 M, i1 N]; linarith
  have eM : ∑ f ∈ Finset.Icc 1 M, g f = ∑ a ∈ Finset.Icc 1 M, w a * S (M / a) :=
    sum_card_divisors_mul_eq w hwm M
  have eN : ∑ f ∈ Finset.Icc 1 N, g f = ∑ a ∈ Finset.Icc 1 N, w a * S (N / a) :=
    sum_card_divisors_mul_eq w hwm N
  have hsplitM : ∑ a ∈ Finset.Icc 1 M, w a * S (M / a)
      = ∑ a ∈ Finset.Icc 1 N, w a * S (M / a) + ∑ a ∈ Finset.Ioc N M, w a * S (M / a) := by
    have hc := Finset.sum_Ioc_consecutive (fun a => w a * S (M / a)) (Nat.zero_le N) hMN.le
    rw [i1 M, i1 N]; linarith
  have hT : ∑ f ∈ Finset.Ioc N M, g f
      = ∑ a ∈ Finset.Icc 1 N, w a * (S (M / a) - S (N / a)) + ∑ a ∈ Finset.Ioc N M, w a * S (M / a) := by
    rw [htail, eM, eN, hsplitM]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hT]
  have hA : ∀ a ∈ Finset.Icc 1 N, w a * (S (M / a) - S (N / a)) ≤ 2 / N * (1 / (a : ℝ)) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.1
    have hNa : 1 ≤ N / a := (Nat.le_div_iff_mul_le ha.1).mpr (by omega)
    have hNaM : N / a ≤ M / a := Nat.div_le_div_right hMN.le
    have hdiff : S (M / a) - S (N / a) = ∑ b ∈ Finset.Ioc (N / a) (M / a), w b := by
      have hc := Finset.sum_Ioc_consecutive w (Nat.zero_le (N / a)) hNaM
      simp only [hS]; rw [i1 (M / a), i1 (N / a)]; linarith
    rw [hdiff]
    have ht := inv_sq_tail (N / a) (M / a) hNa
    have hfl : (N : ℝ) ≤ 2 * a * ((N / a : ℕ) : ℝ) := by
      have h := Nat.div_add_mod N a
      have hmod := Nat.mod_lt N ha.1
      have : N ≤ 2 * a * (N / a) := by nlinarith
      exact_mod_cast this
    have hNa0 : (0 : ℝ) < ((N / a : ℕ) : ℝ) := by exact_mod_cast hNa
    have hinv : 1 / ((N / a : ℕ) : ℝ) ≤ 2 * a / N := by
      rw [div_le_div_iff₀ hNa0 hN0]; linarith
    have hwa : 0 ≤ w a := by simp only [hw]; positivity
    calc w a * ∑ b ∈ Finset.Ioc (N / a) (M / a), w b ≤ w a * (2 * a / N) :=
          mul_le_mul_of_nonneg_left (ht.trans hinv) hwa
      _ = 2 / N * (1 / (a : ℝ)) := by simp only [hw]; field_simp
  have hB : ∀ a ∈ Finset.Ioc N M, w a * S (M / a) ≤ 2 * w a := by
    intro a _
    have hwa : 0 ≤ w a := by simp only [hw]; positivity
    have h2 : S (M / a) ≤ 2 := inv_sq_partial_le_two (M / a)
    nlinarith
  have hsA := Finset.sum_le_sum hA
  have hsB := Finset.sum_le_sum hB
  rw [← Finset.mul_sum] at hsA hsB
  have hH := sum_inv_le_one_add_log N
  have hwt : ∑ a ∈ Finset.Ioc N M, w a ≤ 1 / N := inv_sq_tail N M hN
  have hL1 : 1 + Real.log N ≤ (1 + Real.log N) ^ 2 := by nlinarith
  have hL2 : (1 : ℝ) ≤ (1 + Real.log N) ^ 2 := by nlinarith
  have hfin1 : 2 / (N : ℝ) * ∑ a ∈ Finset.Icc 1 N, 1 / (a : ℝ) ≤ 2 * (1 + Real.log N) ^ 2 / N := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hN0]; nlinarith
  have hfin2 : 2 * ∑ a ∈ Finset.Ioc N M, w a ≤ 2 * (1 + Real.log N) ^ 2 / N := by
    have : 2 * (1 / (N : ℝ)) ≤ 2 * (1 + Real.log N) ^ 2 / N := by
      rw [mul_one_div, div_le_div_iff_of_pos_right hN0]; linarith
    linarith
  have e4 : 4 * (1 + Real.log N) ^ 2 / N = 2 * (1 + Real.log N) ^ 2 / N + 2 * (1 + Real.log N) ^ 2 / N := by
    ring
  linarith

/-- `|Σ_{f≤N} h(f)/f − 𝔖| ≤ C (1 + log N)²/N`: derived from `hq_hasSum` and `hq_tail`. -/
theorem hq_partial_Sconst : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |∑ f ∈ Finset.Icc 1 N, hq f / f - Sconst| ≤ C * (1 + Real.log N) ^ 2 / N := by
  obtain ⟨C, hC, hT⟩ := hq_tail
  refine ⟨C, hC, fun N hN => ?_⟩
  have hS := hq_hasSum.tendsto_sum_nat
  have h0 : hq 0 / ((0 : ℕ) : ℝ) = 0 := by simp
  have key : ∀ M ≥ N, |∑ f ∈ Finset.range (M + 1), hq f / (f : ℝ) - ∑ f ∈ Finset.Icc 1 N, hq f / (f : ℝ)|
      ≤ C * (1 + Real.log N) ^ 2 / N := by
    intro M hM
    have e1 := sum_Icc_one_eq_range (fun f => hq f / (f : ℝ)) M
    rw [h0, sub_zero] at e1
    have e2 := Finset.sum_Ioc_consecutive (fun f => hq f / (f : ℝ)) (Nat.zero_le N) hM
    have i1 : Finset.Icc 1 M = Finset.Ioc 0 M := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have i2 : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e : ∑ f ∈ Finset.range (M + 1), hq f / (f : ℝ) - ∑ f ∈ Finset.Icc 1 N, hq f / (f : ℝ)
        = ∑ f ∈ Finset.Ioc N M, hq f / (f : ℝ) := by
      rw [← e1, i1, i2]; linarith
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_) (hT N hN M))
    apply Finset.sum_congr rfl
    intro f _
    rw [abs_div, Nat.abs_cast]
  have hlim : Filter.Tendsto
      (fun M : ℕ => |∑ f ∈ Finset.range (M + 1), hq f / (f : ℝ) - ∑ f ∈ Finset.Icc 1 N, hq f / (f : ℝ)|)
      Filter.atTop (nhds |Sconst - ∑ f ∈ Finset.Icc 1 N, hq f / (f : ℝ)|) :=
    ((hS.comp (Filter.tendsto_add_atTop_nat 1)).sub_const _).abs
  have := le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨N, key⟩)
  rw [abs_sub_comm]
  exact this

/-- `Σ_{q≤N} (q/φ(q)) φ*(q) = (𝔖/2) N² + O(N (1 + log N)²)`: derived from the three sub-nodes. -/
theorem qphiA_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |qphiA N - Sconst / 2 * (N : ℝ) ^ 2| ≤ C * N * (1 + Real.log N) ^ 2 := by
  obtain ⟨C2, hC2, h2⟩ := hq_abs_partial
  obtain ⟨C3, hC3, h3⟩ := hq_partial_Sconst
  refine ⟨C2 + C3, by positivity, ?_⟩
  intro N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hconv := sum_mul_conv_approx hq N
  have hq_eq : qphiA N = ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∑ f ∈ j.divisors, hq f := by
    unfold qphiA
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [hq_conv j hj1]
    ring
  rw [hq_eq]
  set T := ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ∑ f ∈ j.divisors, hq f with hT
  set U := ∑ f ∈ Finset.Icc 1 N, hq f / (f : ℝ) with hU
  set L := (1 + Real.log N) ^ 2 with hL
  have hL0 : 0 ≤ L := sq_nonneg _
  have e : T - Sconst / 2 * (N : ℝ) ^ 2 = (T - (N : ℝ) ^ 2 / 2 * U) + (N : ℝ) ^ 2 / 2 * (U - Sconst) := by
    ring
  rw [e]
  have hA : |T - (N : ℝ) ^ 2 / 2 * U| ≤ N * (C2 * L) :=
    hconv.trans (mul_le_mul_of_nonneg_left (h2 N hN) hN0.le)
  have hB : |(N : ℝ) ^ 2 / 2 * (U - Sconst)| ≤ (N : ℝ) ^ 2 / 2 * (C3 * L / N) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (h3 N hN) (by positivity)
  have hB' : (N : ℝ) ^ 2 / 2 * (C3 * L / N) = C3 / 2 * N * L := by field_simp
  have hsum := abs_add_le (T - (N : ℝ) ^ 2 / 2 * U) ((N : ℝ) ^ 2 / 2 * (U - Sconst))
  have hpos : 0 ≤ C3 / 2 * N * L := by positivity
  have e2 : (C2 + C3) * N * L - (N * (C2 * L) + C3 / 2 * N * L) = C3 / 2 * N * L := by ring
  linarith

/-- summation by parts on `range n`. -/
theorem abel_range (f a : ℕ → ℝ) (n : ℕ) :
    ∑ q ∈ Finset.range n, f q * a q
      = f n * (∑ q ∈ Finset.range n, a q)
        - ∑ k ∈ Finset.range n, (f (k + 1) - f k) * ∑ q ∈ Finset.range (k + 1), a q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ]
    ring


theorem sum_range_sq (n : ℕ) :
    ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 = ((n : ℝ) - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_range_cube (n : ℕ) :
    ∑ k ∈ Finset.range n, (k : ℝ) ^ 3 = (((n : ℝ) - 1) * n) ^ 2 / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem log_sq_ge_third {x : ℝ} (hx : 2 ≤ x) : 1 / 3 ≤ Real.log x ^ 2 := by
  have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have := Real.log_two_gt_d9
  nlinarith

theorem one_add_log_sq_le_eight {x : ℝ} (hx : 2 ≤ x) : (1 + Real.log x) ^ 2 ≤ 8 * Real.log x ^ 2 := by
  have h := log_sq_ge_third hx
  nlinarith [sq_nonneg (Real.log x - 1)]

end TrackF
end ZetaShell
