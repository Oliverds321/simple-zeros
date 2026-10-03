/-
Node A1 (L7_1 statement, L7_6 proof): **Lemma 1, the signed Farey identity** (lem:shell-1, sec_shell.tex
l.192–203): for `(a_n)` finitely supported with every prime factor of every `n` in the support exceeding `Q`,
and any `ω : {1,…,Q} → ℝ`,
`Σ_{1≤q≤Q} ω(q) Σ*_{χ mod q} |F_χ|² = Σ_{d≤Q} Ω_ω(d) Σ*_{b mod d} |S(b/d)|²`,
`Ω_ω(d) = (φ(d)/d) Σ_{e≤Q/d, (e,d)=1} μ(e) ω(de)/e`, `F_χ = Σ a_n χ(n)`, `S(θ) = Σ a_n e(nθ)`.

Route (L7_6; **sorry-free, axioms `[propext, Classical.choice, Quot.sound]`**). Both sides are expanded as
`Σ_{n,m∈s} a_n ā_m K(n,m)`:
* left: `Σ*_{χ mod q} χ(n)χ̄(m) = Σ_{f|q, f|(n−m)} μ(q/f)φ(f)` is ZetaQ's `lemma5_1` (needs `(nm,q)=1`, which is where
  the support hypothesis `hs` enters) — `lhs_expand`, `primPairSum_eq`;
* right: the Ramanujan sum `Σ_{b<d,(b,d)=1} e(bk/d) = Σ_{g|d, g|k} μ(d/g) g` (`ramanujan_sum`, from `μ * ζ = 1` and
  the geometric sum of a root of unity) — `rhs_expand`;
* the two kernels agree for every `k = n − m` (`farey_kernel_identity`): reindex both sides by the divisor `g`
  (`sum_Icc_divisors_reindex`), which reduces it to `φ(g) Σ_{j≤Q/g} μ(j)ω(gj) = g Σ_{i≤Q/g} μ(i)Ω_ω(gi)`
  (`coeff_identity`), and that to the local identity `Σ_{i|j, (j/i,gi)=1} μ(i)μ(j/i)φ(gi) = jφ(g)μ(j)`
  (`local_identity`, by induction over primes for squarefree `j`, `sqfree_sum`).
Numerics: `numerics_A1.py` (exact kernel identity T1 and coefficient identity T2 for `Q ≤ 40`; the full identity with
brute-force characters at 50 digits, edge cases `Q = 0, 1, 2`, prime, prime powers, `n = 0` at `Q = 1`, `n = 1`;
negative controls with `hs` violated fail).
Dependencies: ZetaQ `CharSums.lemma5_1`, `CharSums.cong_iff_dvd_sub` (trunk), Mathlib. Difficulty: M.
-/
import ZetaShell.Challenge
import ZetaQ.CharSums

noncomputable section

open scoped ComplexConjugate

namespace ZetaShell

open ArithmeticFunction in
/-- `Ω_ω(d)` (eq:shell-identity). -/
def OmegaW (Q : ℕ) (ω : ℕ → ℝ) (d : ℕ) : ℝ :=
  ((Nat.totient d : ℝ) / d) * ∑ e ∈ (Finset.Icc 1 (Q / d)).filter (fun e => Nat.Coprime e d),
    ((moebius e : ℤ) : ℝ) * ω (d * e) / e

/-- `S(θ) = Σ_n a_n e(nθ)`. -/
def expSum (s : Finset ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ s, a n * Complex.exp (2 * Real.pi * Complex.I * n * θ)

/-! ### Elementary pieces -/

/-- The support hypothesis makes every `n` of the support coprime to every modulus `1 ≤ q ≤ Q`. -/
theorem coprime_of_hs {Q : ℕ} {s : Finset ℕ} (hs : ∀ n ∈ s, ∀ p : ℕ, p.Prime → p ∣ n → Q < p)
    {n : ℕ} (hn : n ∈ s) {q : ℕ} (hq1 : 1 ≤ q) (hqQ : q ≤ Q) : Nat.Coprime n q := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpq
  have h1 := hs n hn p hp hpn
  have h2 := Nat.le_of_dvd (by omega) hpq
  omega

/-- `|Σ c_n|² = Σ_n Σ_m c_n c̄_m`, cast to `ℂ`. -/
theorem normSq_sum_expand (s : Finset ℕ) (c : ℕ → ℂ) :
    ((‖∑ n ∈ s, c n‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) := by
  have h := Complex.mul_conj' (∑ n ∈ s, c n)
  push_cast
  rw [← h, map_sum, Finset.sum_mul_sum]

/-- Left side, one modulus: `Σ*_{χ mod q} |F_χ|² = Σ_{n,m} a_n ā_m Σ*_χ χ(n)χ̄(m)`. -/
theorem lhs_expand (q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ χ ∈ primChars q, ((‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, a n * conj (a m) * ZetaQ.primPairSum q n m := by
  have hpc : primChars q = ZetaQ.primitiveChars q := rfl
  simp_rw [normSq_sum_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [ZetaQ.primPairSum, Finset.mul_sum, hpc]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [map_mul]
  ring

/-- `e(nθ)·conj(e(mθ)) = e((n−m)θ)`. -/
theorem exp_mul_conj_exp (n m : ℕ) (θ : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * n * θ) * conj (Complex.exp (2 * Real.pi * Complex.I * m * θ))
      = Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * θ) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast, map_ofNat]
  push_cast
  ring

/-- The additive sum over reduced residues `Σ_{b<d,(b,d)=1} e(bk/d)` (a Ramanujan sum). -/
def ramSum (d : ℕ) (k : ℤ) : ℂ :=
  ∑ b ∈ (Finset.range d).filter (fun b => Nat.Coprime b d),
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((b : ℝ) / d : ℝ))

/-- Right side, one denominator: `Σ*_{b mod d} |S(b/d)|² = Σ_{n,m} a_n ā_m c_d(n−m)`. -/
theorem rhs_expand (d : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ b ∈ (Finset.range d).filter (fun b => Nat.Coprime b d),
        ((‖expSum s a ((b : ℝ) / d)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, a n * conj (a m) * ramSum d ((n : ℤ) - (m : ℤ)) := by
  simp_rw [expSum, normSq_sum_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [ramSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← exp_mul_conj_exp n m ((b : ℝ) / d), map_mul]
  ring

/-! ### The Ramanujan sum -/

/-- Geometric sum of an `m`-th root of unity: `Σ_{j<m} e(kj/m) = m·[m | k]`. -/
theorem sum_exp_range (m : ℕ) (hm : 0 < m) (k : ℤ) :
    ∑ j ∈ Finset.range m, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / (m : ℂ))
      = if (m : ℤ) ∣ k then (m : ℂ) else 0 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) with hz
  have hpow : ∀ j : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (j : ℂ) / (m : ℂ)) = z ^ j := by
    intro j
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [hpow]
  split_ifs with hdvd
  · obtain ⟨t, ht⟩ := hdvd
    have hz1 : z = 1 := by
      rw [hz, Complex.exp_eq_one_iff]
      refine ⟨t, ?_⟩
      rw [ht, div_eq_iff hmC]
      push_cast
      ring
    simp [hz1]
  · have hz1 : z ≠ 1 := by
      intro h1
      rw [hz, Complex.exp_eq_one_iff] at h1
      obtain ⟨t, ht⟩ := h1
      rw [div_eq_iff hmC] at ht
      apply hdvd
      refine ⟨t, ?_⟩
      have h3 : (2 * Real.pi * Complex.I) * ((k : ℂ) - (m : ℂ) * (t : ℂ)) = 0 := by
        linear_combination ht
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hpi
      · have h5 : (k : ℂ) = ((m * t : ℤ) : ℂ) := by push_cast; linear_combination h4
        exact_mod_cast h5
    have hzm : z ^ m = 1 := by
      rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨k, ?_⟩
      field_simp
    rw [geom_sum_eq hz1, hzm, sub_self, zero_div]

/-- `[(b,d) = 1] = Σ_{e | (b,d)} μ(e)`. -/
theorem coprime_indicator (b d : ℕ) :
    (if Nat.Coprime b d then (1 : ℂ) else 0)
      = ∑ e ∈ (Nat.gcd b d).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd b d))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] at h
  rw [h]

/-- The multiples of `e ∣ d` below `d` are `e·j`, `j < d/e`. -/
theorem sum_filter_dvd_range {d e : ℕ} (he : e ∣ d) (hd : 0 < d) (F : ℕ → ℂ) :
    ∑ b ∈ (Finset.range d).filter (fun b => e ∣ b), F b = ∑ j ∈ Finset.range (d / e), F (e * j) := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hd
  obtain ⟨c, rfl⟩ := he
  have hc : e * c / e = c := Nat.mul_div_cancel_left c he0
  have himg : (Finset.range (e * c)).filter (fun b => e ∣ b)
      = (Finset.range c).image (fun j => e * j) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hb, j, rfl⟩
      exact ⟨j, Nat.lt_of_mul_lt_mul_left hb, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hj he0, dvd_mul_right e j⟩
  rw [hc, himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left he0 hxy

/-- **Ramanujan sum**: `Σ_{b<d,(b,d)=1} e(bk/d) = Σ_{g|d, g|k} μ(d/g) g`. -/
theorem ramanujan_sum (d : ℕ) (hd : 0 < d) (k : ℤ) :
    ramSum d k = ∑ g ∈ d.divisors,
      ((ArithmeticFunction.moebius (d / g) : ℤ) : ℂ) * (if (g : ℤ) ∣ k then (g : ℂ) else 0) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  -- step 1: Möbius for the coprimality condition, and swap
  have step1 : ramSum d k = ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
      ∑ b ∈ (Finset.range d).filter (fun b => e ∣ b),
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((b : ℝ) / d : ℝ)) := by
    rw [ramSum, Finset.sum_filter]
    have hind : ∀ b ∈ Finset.range d,
        (if Nat.Coprime b d then
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((b : ℝ) / d : ℝ)) else 0)
        = ∑ e ∈ (Nat.gcd b d).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((b : ℝ) / d : ℝ)) := by
      intro b _
      rw [← Finset.sum_mul, ← coprime_indicator]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hind]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_comm' (fun b e => ?_)
    simp only [Finset.mem_range, Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨hb, ⟨heb, hed⟩, _⟩
      exact ⟨⟨hb, heb⟩, hed, hd.ne'⟩
    · rintro ⟨⟨hb, heb⟩, hed, _⟩
      refine ⟨hb, ⟨heb, hed⟩, ?_⟩
      exact (Nat.gcd_pos_of_pos_right b hd).ne'
  -- step 2: each inner sum is a geometric sum at modulus `d/e`
  have step2 : ∀ e ∈ d.divisors,
      ∑ b ∈ (Finset.range d).filter (fun b => e ∣ b),
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((b : ℝ) / d : ℝ))
      = if ((d / e : ℕ) : ℤ) ∣ k then ((d / e : ℕ) : ℂ) else 0 := by
    intro e he
    have hed : e ∣ d := Nat.dvd_of_mem_divisors he
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hed hd
    have hde : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hd hed) he0
    rw [sum_filter_dvd_range hed hd, ← sum_exp_range (d / e) hde k]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    rw [Nat.cast_div hed heC]
    push_cast
    field_simp
  rw [step1, Finset.sum_congr rfl (fun e he => by rw [step2 e he])]
  rw [← Nat.sum_div_divisors d]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hg) hd.ne']

/-! ### The arithmetic kernel identity -/

/-- Divisor-pair reindexing: `Σ_{q≤Q} Σ_{f|q} F(q,f) = Σ_{f≤Q} Σ_{j≤Q/f} F(fj, f)`. -/
theorem sum_Icc_divisors_reindex (Q : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ f ∈ q.divisors, F q f
      = ∑ f ∈ Finset.Icc 1 Q, ∑ j ∈ Finset.Icc 1 (Q / f), F (f * j) f := by
  have hcomm : ∀ q f, q ∈ Finset.Icc 1 Q ∧ f ∈ q.divisors ↔
      q ∈ (Finset.Icc 1 Q).filter (fun q => f ∣ q) ∧ f ∈ Finset.Icc 1 Q := by
    intro q f
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq1, hqQ⟩, hfq, _⟩
      have h1 := Nat.le_of_dvd (by omega) hfq
      have h2 := Nat.pos_of_dvd_of_pos hfq (by omega)
      exact ⟨⟨⟨hq1, hqQ⟩, hfq⟩, by omega, by omega⟩
    · rintro ⟨⟨⟨hq1, hqQ⟩, hfq⟩, _, _⟩
      exact ⟨⟨hq1, hqQ⟩, hfq, by omega⟩
  rw [Finset.sum_comm' hcomm]
  refine Finset.sum_congr rfl (fun f hf => ?_)
  rw [Finset.mem_Icc] at hf
  have hf0 : 0 < f := by omega
  have himg : (Finset.Icc 1 Q).filter (fun q => f ∣ q)
      = (Finset.Icc 1 (Q / f)).image (fun j => f * j) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hq1, hqQ⟩, j, rfl⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with h | h
        · subst h; simp at hq1
        · exact h
      · rw [Nat.le_div_iff_mul_le hf0]; linarith [mul_comm f j]
    · rintro ⟨j, ⟨hj1, hjQ⟩, rfl⟩
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩,
        dvd_mul_right f j⟩
      calc f * j ≤ f * (Q / f) := Nat.mul_le_mul_left f hjQ
        _ ≤ Q := Nat.mul_div_le Q f
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hf0 hxy

/-- Divisors of `p·a` for a prime `p ∤ a`: `Σ_{d | pa} F(d) = Σ_{v | a} F(v) + Σ_{v | a} F(pv)`. -/
theorem sum_divisors_prime_mul {p a : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (F : ℕ → ℤ) :
    ∑ d ∈ (p * a).divisors, F d = ∑ v ∈ a.divisors, F v + ∑ v ∈ a.divisors, F (p * v) := by
  have ha0 : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
  have hset : (p * a).divisors = a.divisors ∪ a.divisors.image (fun v => p * v) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, -⟩
      by_cases hpd : p ∣ d
      · obtain ⟨v, rfl⟩ := hpd
        right
        refine ⟨v, ⟨?_, ha0⟩, rfl⟩
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos hd
      · left
        have hcd : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
        refine ⟨?_, ha0⟩
        exact Nat.Coprime.dvd_of_dvd_mul_left hcd hd
    · rintro (⟨hd, -⟩ | ⟨v, ⟨hv, -⟩, rfl⟩)
      · exact ⟨dvd_mul_of_dvd_right hd p, mul_ne_zero hp.ne_zero ha0⟩
      · exact ⟨mul_dvd_mul_left p hv, mul_ne_zero hp.ne_zero ha0⟩
  have hdisj : Disjoint a.divisors (a.divisors.image (fun v => p * v)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    rw [Finset.mem_image] at hd'
    obtain ⟨v, _, rfl⟩ := hd'
    exact hpa (dvd_trans (dvd_mul_right p v) (Nat.dvd_of_mem_divisors hd))
  rw [hset, Finset.sum_union hdisj, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hp.pos hxy

/-- For squarefree `j`: `Σ_{i | j, (j/i, g) = 1} φ(gi) = j φ(g)`. -/
theorem sqfree_sum (g : ℕ) : ∀ j : ℕ, Squarefree j →
    ∑ i ∈ j.divisors, (if Nat.Coprime (j / i) g then ((g * i).totient : ℤ) else 0)
      = (j : ℤ) * (g.totient : ℤ) := by
  intro j
  induction j using induction_on_primes with
  | zero => intro h; exact absurd h not_squarefree_zero
  | one => intro _; simp
  | prime_mul p a hp ih =>
    intro hsq
    rw [Nat.squarefree_mul_iff] at hsq
    obtain ⟨hcop, _, hsa⟩ := hsq
    have hpa : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
    rw [sum_divisors_prime_mul hp hpa]
    have e1 : ∀ v ∈ a.divisors, (if Nat.Coprime (p * a / v) g then ((g * v).totient : ℤ) else 0)
        = (if Nat.Coprime (p * (a / v)) g then ((g * v).totient : ℤ) else 0) := by
      intro v hv
      rw [Nat.mul_div_assoc p (Nat.dvd_of_mem_divisors hv)]
    have e2 : ∀ v ∈ a.divisors,
        (if Nat.Coprime (p * a / (p * v)) g then ((g * (p * v)).totient : ℤ) else 0)
        = (if Nat.Coprime (a / v) g then ((g * (p * v)).totient : ℤ) else 0) := by
      intro v _
      rw [Nat.mul_div_mul_left a v hp.pos]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
    by_cases hpg : p ∣ g
    · have hnc : ¬ Nat.Coprime p g := fun h => (Nat.Prime.coprime_iff_not_dvd hp).mp h hpg
      have h1 : ∀ v ∈ a.divisors,
          (if Nat.Coprime (p * (a / v)) g then ((g * v).totient : ℤ) else 0) = 0 := by
        intro v _
        rw [if_neg]
        rw [Nat.coprime_mul_iff_left]
        exact fun h => hnc h.1
      have h2 : ∀ v ∈ a.divisors,
          (if Nat.Coprime (a / v) g then ((g * (p * v)).totient : ℤ) else 0)
          = (p : ℤ) * (if Nat.Coprime (a / v) g then ((g * v).totient : ℤ) else 0) := by
        intro v _
        have : g * (p * v) = p * (g * v) := by ring
        rw [this, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_left hpg v)]
        split_ifs <;> push_cast <;> ring
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ih hsa,
        Finset.sum_const_zero, zero_add]
      push_cast
      ring
    · have hc : Nat.Coprime p g := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpg
      have h1 : ∀ v ∈ a.divisors,
          (if Nat.Coprime (p * (a / v)) g then ((g * v).totient : ℤ) else 0)
          = (if Nat.Coprime (a / v) g then ((g * v).totient : ℤ) else 0) := by
        intro v _
        by_cases h : Nat.Coprime (a / v) g
        · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hc, h⟩), if_pos h]
        · rw [if_neg (fun h' => h (Nat.coprime_mul_iff_left.mp h').2), if_neg h]
      have h2 : ∀ v ∈ a.divisors,
          (if Nat.Coprime (a / v) g then ((g * (p * v)).totient : ℤ) else 0)
          = ((p : ℤ) - 1) * (if Nat.Coprime (a / v) g then ((g * v).totient : ℤ) else 0) := by
        intro v hv
        have hpv : ¬ p ∣ g * v := by
          intro h
          rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
          · exact hpg h'
          · exact hpa (dvd_trans h' (Nat.dvd_of_mem_divisors hv))
        have : g * (p * v) = p * (g * v) := by ring
        rw [this, Nat.totient_mul_of_prime_of_not_dvd hp hpv]
        have hp1 : 1 ≤ p := hp.one_lt.le
        split_ifs <;> push_cast [Nat.cast_sub hp1] <;> ring
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ih hsa]
      push_cast
      ring

/-- **Local identity** (multiplicative-function identity in `ℤ`): for `g, j ≥ 1`,
`Σ_{i | j, (j/i, gi) = 1} μ(i) μ(j/i) φ(gi) = j φ(g) μ(j)`. -/
theorem local_identity (g j : ℕ) (_hg : 0 < g) (_hj : 0 < j) :
    ∑ i ∈ j.divisors, (if Nat.Coprime (j / i) (g * i) then
        ArithmeticFunction.moebius i * ArithmeticFunction.moebius (j / i) * ((g * i).totient : ℤ)
      else 0)
      = (j : ℤ) * (g.totient : ℤ) * ArithmeticFunction.moebius j := by
  by_cases hsq : Squarefree j
  · have key : ∀ i ∈ j.divisors, (if Nat.Coprime (j / i) (g * i) then
          ArithmeticFunction.moebius i * ArithmeticFunction.moebius (j / i) * ((g * i).totient : ℤ)
        else 0)
        = ArithmeticFunction.moebius j *
          (if Nat.Coprime (j / i) g then ((g * i).totient : ℤ) else 0) := by
      intro i hi
      have hij : i ∣ j := Nat.dvd_of_mem_divisors hi
      have hj' : j = i * (j / i) := (Nat.mul_div_cancel' hij).symm
      have hsq' : Squarefree (i * (j / i)) := by rw [← hj']; exact hsq
      rw [Nat.squarefree_mul_iff] at hsq'
      obtain ⟨hcop, _, _⟩ := hsq'
      have hmu : ArithmeticFunction.moebius i * ArithmeticFunction.moebius (j / i)
          = ArithmeticFunction.moebius j := by
        rw [← ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, ← hj']
      have hiff : Nat.Coprime (j / i) (g * i) ↔ Nat.Coprime (j / i) g := by
        rw [Nat.coprime_mul_iff_right]
        exact ⟨fun h => h.1, fun h => ⟨h, hcop.symm⟩⟩
      by_cases hc : Nat.Coprime (j / i) g
      · rw [if_pos (hiff.mpr hc), if_pos hc, hmu]
      · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc, mul_zero]
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, sqfree_sum g j hsq]
    ring
  · have hmu : ArithmeticFunction.moebius j = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    rw [hmu, mul_zero]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    split_ifs with hc
    · have hij : i ∣ j := Nat.dvd_of_mem_divisors hi
      have hj' : j = i * (j / i) := (Nat.mul_div_cancel' hij).symm
      have hcop : Nat.Coprime i (j / i) :=
        (Nat.Coprime.coprime_dvd_right (dvd_mul_left i g) hc).symm
      by_cases h1 : Squarefree i
      · by_cases h2 : Squarefree (j / i)
        · have : Squarefree j := by rw [hj']; exact Nat.squarefree_mul_iff.mpr ⟨hcop, h1, h2⟩
          exact absurd this hsq
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h2]; ring
      · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h1]; ring
    · rfl

/-- The per-`g` coefficient identity `φ(g) Σ_{j≤Q/g} μ(j) ω(gj) = g Σ_{i≤Q/g} μ(i) Ω_ω(gi)`
(`numerics_A1.py`, T2). -/
theorem coeff_identity (Q : ℕ) (ω : ℕ → ℝ) (g : ℕ) (hg : 0 < g) :
    (g.totient : ℂ) * ∑ j ∈ Finset.Icc 1 (Q / g),
        ((ArithmeticFunction.moebius j : ℤ) : ℂ) * (ω (g * j) : ℂ)
      = (g : ℂ) * ∑ i ∈ Finset.Icc 1 (Q / g),
          ((ArithmeticFunction.moebius i : ℤ) : ℂ) * (OmegaW Q ω (g * i) : ℂ) := by
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  set G : ℕ → ℕ → ℂ := fun i e => if Nat.Coprime e (g * i) then
      ((ArithmeticFunction.moebius i : ℤ) : ℂ) * ((ArithmeticFunction.moebius e : ℤ) : ℂ)
        * ((g * i).totient : ℂ) * (ω (g * (i * e)) : ℂ) / ((i : ℂ) * (e : ℂ)) else 0 with hG
  have hR : (g : ℂ) * ∑ i ∈ Finset.Icc 1 (Q / g),
      ((ArithmeticFunction.moebius i : ℤ) : ℂ) * (OmegaW Q ω (g * i) : ℂ)
      = ∑ i ∈ Finset.Icc 1 (Q / g), ∑ e ∈ Finset.Icc 1 (Q / g / i), G i e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    have hiC : (i : ℂ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    rw [OmegaW, Nat.div_div_eq_div_mul, Finset.sum_filter]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [Finset.mem_Icc] at he
    have heC : (e : ℂ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
    rw [hG]
    simp only
    split_ifs with hc
    · rw [show g * i * e = g * (i * e) by ring]
      push_cast
      field_simp
    · simp
  have hre := sum_Icc_divisors_reindex (Q / g) (fun j i => G i (j / i))
  have hre' : ∑ i ∈ Finset.Icc 1 (Q / g), ∑ e ∈ Finset.Icc 1 (Q / g / i), G i e
      = ∑ j ∈ Finset.Icc 1 (Q / g), ∑ i ∈ j.divisors, G i (j / i) := by
    rw [hre]
    refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun e _ => ?_))
    rw [Finset.mem_Icc] at hi
    rw [Nat.mul_div_cancel_left e (by omega)]
  rw [hR, hre', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hjC : (j : ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hloc := congrArg (Int.cast : ℤ → ℂ) (local_identity g j hg (by omega))
  push_cast at hloc
  have hG' : ∀ i ∈ j.divisors, G i (j / i) = (ω (g * j) : ℂ) / (j : ℂ) *
      (if Nat.Coprime (j / i) (g * i) then
        ((ArithmeticFunction.moebius i : ℤ) : ℂ) * ((ArithmeticFunction.moebius (j / i) : ℤ) : ℂ)
          * ((g * i).totient : ℂ) else 0) := by
    intro i hi
    have hij : i ∣ j := Nat.dvd_of_mem_divisors hi
    have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hij (by omega)
    have hiC : (i : ℂ) ≠ 0 := by exact_mod_cast hi0.ne'
    have hjiC : ((j / i : ℕ) : ℂ) = (j : ℂ) / (i : ℂ) := Nat.cast_div hij hiC
    rw [hG]
    simp only
    split_ifs with hc
    · rw [Nat.mul_div_cancel' hij, hjiC]
      field_simp
    · simp
  rw [Finset.sum_congr rfl hG', ← Finset.mul_sum]
  have hloc' : ∑ i ∈ j.divisors, (if Nat.Coprime (j / i) (g * i) then
        ((ArithmeticFunction.moebius i : ℤ) : ℂ) * ((ArithmeticFunction.moebius (j / i) : ℤ) : ℂ)
          * ((g * i).totient : ℂ) else 0)
      = (j : ℂ) * (g.totient : ℂ) * ((ArithmeticFunction.moebius j : ℤ) : ℂ) := by
    rw [← hloc]
  rw [hloc']
  field_simp

/-- **Kernel identity** (pure arithmetic; checked exactly in `numerics_A1.py`, T1, for `Q ≤ 40` and all
`|k| ≤ 60`): for every `k`,
`Σ_{q≤Q} ω(q) Σ_{f|q, f|k} μ(q/f)φ(f) = Σ_{d≤Q} Ω_ω(d) Σ_{g|d, g|k} μ(d/g) g`. -/
theorem farey_kernel_identity (Q : ℕ) (ω : ℕ → ℝ) (k : ℤ) :
    ∑ q ∈ Finset.Icc 1 Q, (ω q : ℂ) * ∑ f ∈ q.divisors,
        ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) * (if (f : ℤ) ∣ k then (Nat.totient f : ℂ) else 0)
      = ∑ d ∈ Finset.Icc 1 Q, (OmegaW Q ω d : ℂ) * ∑ g ∈ d.divisors,
        ((ArithmeticFunction.moebius (d / g) : ℤ) : ℂ) * (if (g : ℤ) ∣ k then (g : ℂ) else 0) := by
  simp_rw [Finset.mul_sum]
  rw [sum_Icc_divisors_reindex Q (fun q f => (ω q : ℂ) *
      (((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) * (if (f : ℤ) ∣ k then (Nat.totient f : ℂ) else 0))),
    sum_Icc_divisors_reindex Q (fun d g => (OmegaW Q ω d : ℂ) *
      (((ArithmeticFunction.moebius (d / g) : ℤ) : ℂ) * (if (g : ℤ) ∣ k then (g : ℂ) else 0)))]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [Finset.mem_Icc] at hg
  have hg0 : 0 < g := by omega
  have hc := coeff_identity Q ω g hg0
  simp only [Nat.mul_div_cancel_left _ hg0]
  by_cases hk : (g : ℤ) ∣ k
  · simp only [hk, if_true]
    have e1 : ∑ j ∈ Finset.Icc 1 (Q / g), (ω (g * j) : ℂ) *
        (((ArithmeticFunction.moebius j : ℤ) : ℂ) * (Nat.totient g : ℂ))
        = (g.totient : ℂ) * ∑ j ∈ Finset.Icc 1 (Q / g),
          ((ArithmeticFunction.moebius j : ℤ) : ℂ) * (ω (g * j) : ℂ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    have e2 : ∑ i ∈ Finset.Icc 1 (Q / g), (OmegaW Q ω (g * i) : ℂ) *
        (((ArithmeticFunction.moebius i : ℤ) : ℂ) * (g : ℂ))
        = (g : ℂ) * ∑ i ∈ Finset.Icc 1 (Q / g),
          ((ArithmeticFunction.moebius i : ℤ) : ℂ) * (OmegaW Q ω (g * i) : ℂ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1, e2, hc]
  · simp [hk]

/-! ### Assembly -/

/-- `Σ*_{χ mod q} χ(n)χ̄(m)` in the divisibility form, from ZetaQ's `lemma5_1`. -/
theorem primPairSum_eq (q : ℕ) (hq : 1 ≤ q) (n m : ℕ) (hnm : Nat.Coprime (n * m) q) :
    ZetaQ.primPairSum q n m = ∑ f ∈ q.divisors,
      ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ)
        * (if (f : ℤ) ∣ ((n : ℤ) - (m : ℤ)) then (Nat.totient f : ℂ) else 0) := by
  have : NeZero q := ⟨by omega⟩
  rw [ZetaQ.lemma5_1 n m hnm, ZetaQ.divisorsCong, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  by_cases h : (n : ZMod f) = (m : ZMod f)
  · rw [if_pos h, if_pos ((ZetaQ.cong_iff_dvd_sub n m f).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((ZetaQ.cong_iff_dvd_sub n m f).mpr h')), mul_zero]

theorem signed_farey_identity (Q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ) (ω : ℕ → ℝ)
    (hs : ∀ n ∈ s, ∀ p : ℕ, p.Prime → p ∣ n → Q < p) :
    ∑ q ∈ Finset.Icc 1 Q, ω q * ∑ χ ∈ primChars q, ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2
      = ∑ d ∈ Finset.Icc 1 Q, OmegaW Q ω d *
          ∑ b ∈ (Finset.range d).filter (fun b => Nat.Coprime b d), ‖expSum s a ((b : ℝ) / d)‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  -- left side
  have hL : ∑ q ∈ Finset.Icc 1 Q, (ω q : ℂ) *
        ∑ χ ∈ primChars q, ((‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, a n * conj (a m) * ∑ q ∈ Finset.Icc 1 Q, (ω q : ℂ) * ∑ f ∈ q.divisors,
        ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ)
          * (if (f : ℤ) ∣ ((n : ℤ) - (m : ℤ)) then (Nat.totient f : ℂ) else 0) := by
    have h1 : ∀ q ∈ Finset.Icc 1 Q, (ω q : ℂ) *
        ∑ χ ∈ primChars q, ((‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 : ℝ) : ℂ)
        = ∑ n ∈ s, ∑ m ∈ s, (ω q : ℂ) * (a n * conj (a m) * ∑ f ∈ q.divisors,
          ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ)
            * (if (f : ℤ) ∣ ((n : ℤ) - (m : ℤ)) then (Nat.totient f : ℂ) else 0)) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      rw [lhs_expand, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hc : Nat.Coprime (n * m) q :=
        Nat.Coprime.mul_left (coprime_of_hs hs hn hq.1 hq.2) (coprime_of_hs hs hm hq.1 hq.2)
      rw [primPairSum_eq q hq.1 n m hc]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  -- right side
  have hR : ∑ d ∈ Finset.Icc 1 Q, (OmegaW Q ω d : ℂ) *
        ∑ b ∈ (Finset.range d).filter (fun b => Nat.Coprime b d),
          ((‖expSum s a ((b : ℝ) / d)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, a n * conj (a m) * ∑ d ∈ Finset.Icc 1 Q, (OmegaW Q ω d : ℂ) *
        ∑ g ∈ d.divisors, ((ArithmeticFunction.moebius (d / g) : ℤ) : ℂ)
          * (if (g : ℤ) ∣ ((n : ℤ) - (m : ℤ)) then (g : ℂ) else 0) := by
    have h1 : ∀ d ∈ Finset.Icc 1 Q, (OmegaW Q ω d : ℂ) *
        ∑ b ∈ (Finset.range d).filter (fun b => Nat.Coprime b d),
          ((‖expSum s a ((b : ℝ) / d)‖ ^ 2 : ℝ) : ℂ)
        = ∑ n ∈ s, ∑ m ∈ s, (OmegaW Q ω d : ℂ) * (a n * conj (a m) *
          ∑ g ∈ d.divisors, ((ArithmeticFunction.moebius (d / g) : ℤ) : ℂ)
            * (if (g : ℤ) ∣ ((n : ℤ) - (m : ℤ)) then (g : ℂ) else 0)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      rw [rhs_expand, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [ramanujan_sum d (by omega)]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
  rw [farey_kernel_identity Q ω ((n : ℤ) - (m : ℤ))]

end ZetaShell
