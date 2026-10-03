/-
L10c_Tao (L7_10c, 3 Oct 2026): **`‖Ω‖_∞ ≤ 1` for the sharp family** (rem:shell-Omega (iii), the case
`𝒫 = {p ∤ d}` of Tao's inequality, credited there to Granville–Soundararajan):
`|Σ_{m ≤ M, (m,d)=1} μ(m)/m| ≤ 1`, hence `|Ω(d)| ≤ φ(d)/d ≤ 1`.
Proof (elementary): `M·S = Σ_{m} μ(m)⌊M/m⌋ + Σ_{m ≥ 2} μ(m){M/m}`, and `Σ_m μ(m)⌊M/m⌋ = Σ_{n ≤ M} g(n)` with
`g(n) = Σ_{e ∣ n, (e,d)=1} μ(e) ∈ [0, 1]` (multiplicative, `g(p^k) = 1 − [p ∤ d]`), `g(1) = 1`, `g = 0` on the
`m ≥ 2` coprime to `d`; so `G + A ≤ M` with `A = #{2 ≤ m ≤ M : (m,d) = 1}`, `G ≥ 1`, and `−M ≤ 2G − M ≤ M·S ≤ G + A ≤ M`.
-/
import ZetaShell.Lemma2.A2a_OutsideShells

noncomputable section
open scoped BigOperators ArithmeticFunction

namespace ZetaShell
namespace ShellS
namespace ASc

open ArithmeticFunction

/-- the indicator of `(e, d) = 1` as an arithmetic function. -/
def coprInd (d : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun e => if e ≠ 0 ∧ Nat.Coprime e d then 1 else 0, by simp⟩

theorem coprInd_apply (d e : ℕ) (he : e ≠ 0) : coprInd d e = if Nat.Coprime e d then 1 else 0 := by
  show (if e ≠ 0 ∧ Nat.Coprime e d then (1 : ℤ) else 0) = _
  simp [he]

theorem coprInd_mult (d : ℕ) : IsMultiplicative (coprInd d) := by
  refine ⟨by rw [coprInd_apply d 1 one_ne_zero]; simp, fun {m n} hmn => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [coprInd]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coprInd]
  rw [coprInd_apply d _ (Nat.mul_ne_zero hm.ne' hn.ne'), coprInd_apply d _ hm.ne', coprInd_apply d _ hn.ne']
  by_cases h1 : Nat.Coprime m d <;> by_cases h2 : Nat.Coprime n d
  · rw [if_pos (Nat.Coprime.mul_left h1 h2), if_pos h1, if_pos h2, mul_one]
  · rw [if_neg (fun h => h2 (Nat.Coprime.coprime_mul_left h)), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (Nat.Coprime.coprime_mul_right h)), if_neg h1, zero_mul]
  · rw [if_neg (fun h => h1 (Nat.Coprime.coprime_mul_right h)), if_neg h1, zero_mul]

/-- `g = (μ·1_{(·,d)=1}) * ζ`. -/
def gTao (d : ℕ) : ArithmeticFunction ℤ := ((moebius : ArithmeticFunction ℤ).pmul (coprInd d)) * (zeta : ArithmeticFunction ℤ)

theorem gTao_mult (d : ℕ) : IsMultiplicative (gTao d) :=
  (isMultiplicative_moebius.intCast.pmul (coprInd_mult d)).mul isMultiplicative_zeta.natCast

theorem gTao_apply (d n : ℕ) :
    gTao d n = ∑ e ∈ n.divisors, (moebius e : ℤ) * coprInd d e := by
  unfold gTao
  rw [coe_mul_zeta_apply]
  rfl

theorem gTao_prime_pow (d p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    gTao d (p ^ k) = 1 - coprInd d p := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [gTao_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∑ i ∈ Finset.range j, ((moebius (p ^ (i + 1 + 1)) : ℤ) * coprInd d (p ^ (i + 1 + 1))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [moebius_apply_prime_pow hp (by omega)]
    simp
  rw [hrest]
  have h1 : (moebius (p ^ (0 + 1)) : ℤ) = -1 := by
    rw [zero_add, pow_one, moebius_apply_prime hp]
  rw [h1, pow_zero, moebius_apply_one, coprInd_apply d 1 one_ne_zero, zero_add, pow_one]
  simp; ring

theorem gTao_bounds (d n : ℕ) (hn : n ≠ 0) : 0 ≤ gTao d n ∧ gTao d n ≤ 1 := by
  rw [(gTao_mult d).multiplicative_factorization _ hn]
  unfold Finsupp.prod
  have hfac : ∀ p ∈ n.factorization.support, 0 ≤ gTao d (p ^ n.factorization p) ∧
      gTao d (p ^ n.factorization p) ≤ 1 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    rw [gTao_prime_pow d p _ hpp hk, coprInd_apply d p hpp.ne_zero]
    split_ifs <;> norm_num
  exact ⟨Finset.prod_nonneg fun p hp => (hfac p hp).1,
    Finset.prod_le_one (fun p hp => (hfac p hp).1) fun p hp => (hfac p hp).2⟩

theorem gTao_one (d : ℕ) : gTao d 1 = 1 := (gTao_mult d).map_one

theorem gTao_coprime (d n : ℕ) (hn : 2 ≤ n) (hcop : Nat.Coprime n d) : gTao d n = 0 := by
  rw [gTao_apply]
  have h : ∀ e ∈ n.divisors, (moebius e : ℤ) * coprInd d e = (moebius e : ℤ) := by
    intro e he
    have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
    rw [coprInd_apply d e he0, if_pos (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors he) hcop),
      mul_one]
  rw [Finset.sum_congr rfl h]
  have := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at this
  rw [this, if_neg (by omega)]

/-- `Σ_{m ∈ E} μ(m)⌊M/m⌋ = Σ_{n ≤ M} g(n)`, `E = {1 ≤ m ≤ M, (m,d) = 1}`. -/
theorem floor_sum_eq (M d : ℕ) :
    ∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m d), (moebius m : ℤ) * ((M / m : ℕ) : ℤ)
      = ∑ n ∈ Finset.Icc 1 M, gTao d n := by
  have h1 : ∀ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m d),
      (moebius m : ℤ) * ((M / m : ℕ) : ℤ) = ∑ n ∈ Finset.Icc 1 M, if m ∣ n then (moebius m : ℤ) else 0 := by
    intro m _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    rw [← Nat.Ioc_filter_dvd_card_eq_div M m]
    congr 1
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn0 : n ≠ 0 := by omega
  rw [gTao_apply]
  have L : (∑ m ∈ Finset.Icc 1 M, if Nat.Coprime m d then (if m ∣ n then (moebius m : ℤ) else 0) else 0)
      = ∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m d ∧ m ∣ n), (moebius m : ℤ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h1 : Nat.Coprime m d <;> by_cases h2 : m ∣ n <;> simp [h1, h2]
  have R : (∑ m ∈ n.divisors, (moebius m : ℤ) * coprInd d m)
      = ∑ m ∈ n.divisors.filter (fun m => Nat.Coprime m d), (moebius m : ℤ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [coprInd_apply d m (Nat.ne_of_gt (Nat.pos_of_mem_divisors hm))]
    split_ifs <;> simp
  have hsum : (∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m d),
      if m ∣ n then (moebius m : ℤ) else 0)
      = ∑ m ∈ Finset.Icc 1 M, if Nat.Coprime m d then (if m ∣ n then (moebius m : ℤ) else 0) else 0 := by
    rw [Finset.sum_filter]
  rw [hsum, L, R]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨-, hc, hd⟩
    exact ⟨⟨hd, hn0⟩, hc⟩
  · rintro ⟨⟨hd, -⟩, hc⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) hn.2⟩, hc, hd⟩

/-- **Tao's inequality, coprime form**: `|Σ_{m ≤ M, (m,d)=1} μ(m)/m| ≤ 1`. -/
theorem tao_ineq (M d : ℕ) :
    |∑ m ∈ (Finset.Icc 1 M).filter (fun m => Nat.Coprime m d), ((moebius m : ℤ) : ℝ) / m| ≤ 1 := by
  set E := (Finset.Icc 1 M).filter (fun m => Nat.Coprime m d) with hE
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [hE]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  -- the fractional parts
  set f : ℕ → ℝ := fun m => (M : ℝ) / m - ((M / m : ℕ) : ℝ) with hf
  have hf0 : ∀ m ∈ E, 0 ≤ f m ∧ f m < 1 := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    have h1 : ((M / m : ℕ) : ℝ) ≤ (M : ℝ) / m := Nat.cast_div_le
    have h2 : (M : ℝ) / m < ((M / m : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hmR]
      have e1 := Nat.div_add_mod M m
      have e2 := Nat.mod_lt M (by omega : m > 0)
      have e1' : ((m * (M / m) + M % m : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast e1
      have e2' : ((M % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast e2
      push_cast at e1'
      nlinarith
    exact ⟨by rw [hf]; linarith, by rw [hf]; linarith⟩
  have hf1 : f 1 = 0 := by rw [hf]; simp
  set G : ℝ := ∑ n ∈ Finset.Icc 1 M, ((gTao d n : ℤ) : ℝ) with hG
  set E2 := E.filter (fun m => 2 ≤ m) with hE2
  set A : ℝ := (E2.card : ℝ) with hA
  -- `M·S = G + F`
  have hsplit : (M : ℝ) * ∑ m ∈ E, ((moebius m : ℤ) : ℝ) / m
      = G + ∑ m ∈ E, ((moebius m : ℤ) : ℝ) * f m := by
    have hfl := congrArg (fun z : ℤ => (z : ℝ)) (floor_sum_eq M d)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hfl
    rw [hG, ← hfl, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hf]; ring
  -- `|F| ≤ A`
  have hF : |∑ m ∈ E, ((moebius m : ℤ) : ℝ) * f m| ≤ A := by
    have h1 : ∑ m ∈ E, ((moebius m : ℤ) : ℝ) * f m = ∑ m ∈ E2, ((moebius m : ℤ) : ℝ) * f m := by
      rw [hE2, Finset.sum_filter (s := E)]
      refine Finset.sum_congr rfl fun m hm => ?_
      split_ifs with h
      · rfl
      · have : m = 1 := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
          omega
        rw [this, hf1, mul_zero]
    rw [h1]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [hA, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmE : m ∈ E := (Finset.mem_filter.mp hm).1
    obtain ⟨h0, h1⟩ := hf0 m hmE
    rw [abs_mul, abs_of_nonneg h0]
    have hμ : |((moebius m : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    nlinarith [abs_nonneg ((moebius m : ℤ) : ℝ)]
  -- `G ≥ 1` and `G + A ≤ M`
  have hg : ∀ n ∈ Finset.Icc 1 M, 0 ≤ ((gTao d n : ℤ) : ℝ) ∧ ((gTao d n : ℤ) : ℝ) ≤ 1 := by
    intro n hn
    have := gTao_bounds d n (by have := (Finset.mem_Icc.mp hn).1; omega)
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have hG1 : 1 ≤ G := by
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨le_rfl, hM⟩
    have := Finset.single_le_sum (f := fun n => ((gTao d n : ℤ) : ℝ)) (fun n hn => (hg n hn).1) h1
    rw [gTao_one] at this
    simpa using this
  have hGA : G + A ≤ M := by
    have hsub : E2 ⊆ Finset.Icc 1 M := fun m hm => (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
    have h1 : G ≤ ∑ n ∈ Finset.Icc 1 M, (if n ∈ E2 then (0 : ℝ) else 1) := by
      refine Finset.sum_le_sum fun n hn => ?_
      split_ifs with h
      · have hn2 : 2 ≤ n := (Finset.mem_filter.mp h).2
        have hcop : Nat.Coprime n d := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
        rw [gTao_coprime d n hn2 hcop]; simp
      · exact (hg n hn).2
    have h2 : ∑ n ∈ Finset.Icc 1 M, (if n ∈ E2 then (0 : ℝ) else 1) = (M : ℝ) - A := by
      have e1 : ∀ n ∈ Finset.Icc 1 M, (if n ∈ E2 then (0 : ℝ) else 1) = 1 - (if n ∈ E2 then (1 : ℝ) else 0) :=
        fun n _ => by split_ifs <;> norm_num
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Nat.card_Icc,
        nsmul_eq_mul, mul_one, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub, hA]
      simp
    linarith
  have hMS := hsplit
  rw [abs_le]
  have hFle := abs_le.mp hF
  constructor
  · have : -(M : ℝ) ≤ (M : ℝ) * ∑ m ∈ E, ((moebius m : ℤ) : ℝ) / m := by linarith
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon hMR
    linarith
  · have : (M : ℝ) * ∑ m ∈ E, ((moebius m : ℤ) : ℝ) / m ≤ M := by linarith
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon hMR
    linarith

theorem omega_sharp_eq_one (Q q : ℕ) (hq : q ≤ Q) : TrackF.Fam.omega .sharp Q q = 1 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · have : q = 0 := by omega
    subst this
    simp [TrackF.Fam.omega, TrackF.Fam.kind, TrackF.Fam.w]
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hle : (q : ℝ) / Q ≤ 1 := by rw [div_le_one hQ0]; exact_mod_cast hq
  simp only [TrackF.Fam.omega, TrackF.Fam.kind, TrackF.Fam.w]
  rw [if_pos ⟨by positivity, hle⟩]

/-- **`|Ω(d)| ≤ 1` for the sharp family.** -/
theorem omega_sharp_abs_le (Q d : ℕ) : |ZetaShell.OmegaW Q (TrackF.Fam.omega .sharp Q) d| ≤ 1 := by
  unfold ZetaShell.OmegaW
  have h1 : ∑ e ∈ (Finset.Icc 1 (Q / d)).filter (fun e => Nat.Coprime e d),
      ((moebius e : ℤ) : ℝ) * TrackF.Fam.omega .sharp Q (d * e) / e
      = ∑ e ∈ (Finset.Icc 1 (Q / d)).filter (fun e => Nat.Coprime e d), ((moebius e : ℤ) : ℝ) / e := by
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).2
    have : d * e ≤ Q := by
      calc d * e ≤ d * (Q / d) := Nat.mul_le_mul_left d he'
        _ ≤ Q := Nat.mul_div_le Q d
    rw [omega_sharp_eq_one Q _ this, mul_one]
  rw [h1, abs_mul]
  have h2 : |(Nat.totient d : ℝ) / d| ≤ 1 := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    rw [abs_of_nonneg (by positivity), div_le_one hd0]
    exact_mod_cast Nat.totient_le d
  calc |(Nat.totient d : ℝ) / d| * |∑ e ∈ (Finset.Icc 1 (Q / d)).filter (fun e => Nat.Coprime e d),
        ((moebius e : ℤ) : ℝ) / e| ≤ 1 * 1 :=
        mul_le_mul h2 (tao_ineq (Q / d) d) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end ASc
end ShellS
end ZetaShell
