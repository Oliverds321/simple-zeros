/-
Node A⋆ (L7_6, round 2): **statement-change request for `ring_le_primitive`** (lem:shell-star).

The frozen statement (`ZetaShell.Skeleton.Astar_PrimitiveReduction`, L7_6's own round-1 draft) ends with
`∫ β in R_r, ‖S_χ β − [r=1]𝓜 β‖ ^ 2 + 2 * (Real.log K + Cμ) * U`. An integral's body is parsed at precedence 60, so
Lean reads the model term INSIDE the last integral (and inside both sums): the right side is
`2(log K + Cμ) Σ_r (r/φ(r)) Σ*_χ ∫_{R_r} (‖S_χ − [r=1]𝓜‖² + 2(log K + Cμ)U)`, not the draft's
`2(log K + Cμ) Σ_r … ∫_{R_r} ‖S_χ − [r=1]𝓜‖² + 2(log K + Cμ)U`. `frozen_rhs_parse` below checks this by `rfl`.

As parsed the statement is FALSE (numerical counterexample `cex_Astar.py`): `R₁ = 1`, `K = 3`, `Cμ = 0`, `Q = 1000`,
`a_n = e(−2n/Q)` on the primes `Q < n ≤ 30000`, `𝓜 = S`, `U = ‖a‖² = 3077`: `Ring = 331.4` against the parsed right side
`4(log 3)² U · 4/Q = 59.4` (the intended right side is `6760.9`). All hypotheses hold (`hmult`: the only window sum is
`1 ≤ log 3`; `hU` with equality by Parseval).

Corrected statement (integral parenthesised; this is the draft's lem:shell-star and the form round 1 tested
numerically, N3): `ring_le_primitive_corr`.

PROOF (L7_6c, 3 Oct 2026; statement unchanged, only the `sorry` replaced). The arithmetic half is the module
`ZetaShell.Farey.Astar_Gauss` (imprimitive Gauss sum, eq:shell-gauss, `ring_point_bound`). Here, pointwise in `β`:
`Σ_r 1_{ring r}(β) Σ*_b |S(b/r+β)|² ≤ Σ_r 1_{ring r} Σ_{d|r} (d/φ(d))(μ(r/d)²/φ(r/d)) Σ*_ψ |S_ψ|²`, reindexed `r = dm`;
for fixed `d` the window sum `Σ_{m ≤ R₁/d} 1_{ring(dm)}(β) μ²(m)/φ(m)` is at most `(log K + Cμ)·1_{|β| ∈ [1/(R₁Q), K/(dQ)]}`
by `hmult` at `y = 1/(dQ|β|)` (`window_bound`); then `|S|² ≤ 2|S − 𝓜|² + 2|𝓜|²` at `d = 1` (one character mod 1) and
`∫_{|β| ≤ K/Q} |𝓜|² ≤ ∫_{−1/2}^{1/2} |𝓜|² ≤ U` (`K/Q ≤ 1/2`). Integrals: indicators of bounded measurable sets times
continuous functions, `integral_mono`. `R₁ = 0` is the trivial case (`U ≥ 0` from `hU`).
-/
import ZetaShell.Defs.TF_Defs
import ZetaShell.Farey.Astar_Gauss

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace TrackF

/-- The frozen right side, as Lean parses it: the model term sits inside the last integral. -/
theorem frozen_rhs_parse (Q R1 N : ℕ) (K Cμ U : ℝ) (a : ℕ → ℂ) (M : ℝ → ℂ) :
    (2 * (Real.log K + Cμ) * ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ χ ∈ ZetaQ.primitiveChars r,
            ∫ β in {β : ℝ | 1 / ((R1 : ℝ) * Q) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Q)},
              ‖twistSum N a χ β - (if r = 1 then M β else 0)‖ ^ 2
        + 2 * (Real.log K + Cμ) * U)
      = 2 * (Real.log K + Cμ) * ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ χ ∈ ZetaQ.primitiveChars r,
            ∫ β in {β : ℝ | 1 / ((R1 : ℝ) * Q) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Q)},
              (‖twistSum N a χ β - (if r = 1 then M β else 0)‖ ^ 2 + 2 * (Real.log K + Cμ) * U) :=
  rfl

namespace AstarAux

/-- Divisor-pair reindexing `Σ_{r≤R} Σ_{d|r} F(r,d) = Σ_{d≤R} Σ_{m≤R/d} F(dm, d)` (as A1's `sum_Icc_divisors_reindex`,
for any additive commutative monoid). -/
theorem sum_Icc_divisors_reindex' {β' : Type*} [AddCommMonoid β'] (R : ℕ) (F : ℕ → ℕ → β') :
    ∑ q ∈ Finset.Icc 1 R, ∑ f ∈ q.divisors, F q f
      = ∑ f ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 (R / f), F (f * j) f := by
  have hcomm : ∀ q f, q ∈ Finset.Icc 1 R ∧ f ∈ q.divisors ↔
      q ∈ (Finset.Icc 1 R).filter (fun q => f ∣ q) ∧ f ∈ Finset.Icc 1 R := by
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
  have himg : (Finset.Icc 1 R).filter (fun q => f ∣ q)
      = (Finset.Icc 1 (R / f)).image (fun j => f * j) := by
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
      calc f * j ≤ f * (R / f) := Nat.mul_le_mul_left f hjQ
        _ ≤ R := Nat.mul_div_le R f
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hf0 hxy

/-- The region of the right side: `1/(R₁Q) ≤ |β| ≤ K/(dQ)`. -/
def regSet (Q R1 : ℕ) (K : ℝ) (d : ℕ) : Set ℝ :=
  {β : ℝ | 1 / ((R1 : ℝ) * Q) ≤ |β| ∧ |β| ≤ K / ((d : ℝ) * Q)}

/-- The integrand of `ringMass`, summed (indicator form). -/
def lhsF (Q R1 N : ℕ) (K : ℝ) (a : ℕ → ℂ) (β : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R1, ∑ b ∈ ZetaQ.reducedResidues r,
    (ringSet Q K r).indicator (fun β => ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2) β

/-- The integrand of the right side (indicator form), with `L = log K + Cμ`. -/
def rhsF (Q R1 N : ℕ) (K L : ℝ) (a : ℕ → ℂ) (M : ℝ → ℂ) (β : ℝ) : ℝ :=
  2 * L * ∑ d ∈ Finset.Icc 1 R1, ((d : ℝ) / (Nat.totient d : ℝ)) *
      ∑ χ ∈ ZetaQ.primitiveChars d,
        (regSet Q R1 K d).indicator
          (fun β => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β
    + 2 * L * (regSet Q R1 K 1).indicator (fun β => ‖M β‖ ^ 2) β

/-- **The window bound**: for fixed `d ≥ 1`,
`Σ_{m ≤ R₁/d} 1_{ring(dm)}(β) μ(m)²/φ(m) ≤ L · 1_{reg d}(β)` (`hmult` at `y = 1/(dQ|β|)`). -/
theorem window_bound (Q R1 d : ℕ) (K L : ℝ) (hd : 0 < d) (hQ : 0 < Q) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hmult : ∀ y : ℝ, 0 < y →
      ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
        ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) ≤ L) (β : ℝ) :
    ∑ m ∈ Finset.Icc 1 (R1 / d), (ringSet Q K (d * m)).indicator (fun _ => (1 : ℝ)) β *
        (((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 / (Nat.totient m : ℝ))
      ≤ L * (regSet Q R1 K d).indicator (fun _ => (1 : ℝ)) β := by
  classical
  by_cases hex : ∃ m ∈ Finset.Icc 1 (R1 / d), β ∈ ringSet Q K (d * m)
  swap
  · simp only [not_exists, not_and] at hex
    rw [Finset.sum_eq_zero (fun m hm => by rw [Set.indicator_of_notMem (hex m hm), zero_mul])]
    exact mul_nonneg hL (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  obtain ⟨m0, hm0, hβ0⟩ := hex
  rw [Finset.mem_Icc] at hm0
  have hdm0 : d * m0 ≤ R1 := le_trans (Nat.mul_le_mul_left d hm0.2) (Nat.mul_div_le R1 d)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm0R : (1 : ℝ) ≤ m0 := by exact_mod_cast hm0.1
  obtain ⟨h1, h2⟩ := hβ0
  push_cast at h1 h2
  have hX : (0 : ℝ) < (d : ℝ) * m0 * Q := by positivity
  have hb : 0 < |β| := lt_of_lt_of_le (by positivity) h1
  have hreg : β ∈ regSet Q R1 K d := by
    refine ⟨le_trans ?_ h1, le_trans h2.le ?_⟩
    · apply one_div_le_one_div_of_le hX
      have h3 : ((d * m0 : ℕ) : ℝ) ≤ R1 := by exact_mod_cast hdm0
      push_cast at h3
      exact mul_le_mul_of_nonneg_right h3 hQR.le
    · apply div_le_div_of_nonneg_left hK (by positivity)
      nlinarith [mul_pos hdR hQR]
  rw [Set.indicator_of_mem hreg, mul_one]
  have hDb : (0 : ℝ) < (d : ℝ) * Q * |β| := by positivity
  set y : ℝ := 1 / ((d : ℝ) * Q * |β|) with hy
  have hy0 : 0 < y := by positivity
  calc ∑ m ∈ Finset.Icc 1 (R1 / d), (ringSet Q K (d * m)).indicator (fun _ => (1 : ℝ)) β *
          (((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 / (Nat.totient m : ℝ))
        = ∑ m ∈ (Finset.Icc 1 (R1 / d)).filter (fun m => β ∈ ringSet Q K (d * m)),
          (((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 / (Nat.totient m : ℝ)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        by_cases h : β ∈ ringSet Q K (d * m)
        · rw [Set.indicator_of_mem h, one_mul, if_pos h]
        · rw [Set.indicator_of_notMem h, zero_mul, if_neg h]
    _ ≤ ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
          ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
          obtain ⟨⟨hm1, hm2⟩, k1, k2⟩ := hm
          push_cast at k1 k2
          have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          have hXm : (0 : ℝ) < (d : ℝ) * m * Q := by positivity
          refine ⟨⟨hm1, le_trans hm2 (Nat.div_le_self R1 d)⟩, ?_, ?_⟩
          · rw [hy, div_le_iff₀ hDb]
            have h5 := (div_le_iff₀ hXm).mp k1
            have e : (m : ℝ) * ((d : ℝ) * Q * |β|) = |β| * ((d : ℝ) * m * Q) := by ring
            rw [e]
            exact h5
          · rw [hy, mul_one_div, lt_div_iff₀ hDb]
            have h5 := (lt_div_iff₀ hXm).mp k2
            have e : (m : ℝ) * ((d : ℝ) * Q * |β|) = |β| * ((d : ℝ) * m * Q) := by ring
            rw [e]
            exact h5
        · intro m _ _
          positivity
    _ ≤ L := hmult y hy0

/-- `‖x‖² ≤ 2‖x − y‖² + 2‖y‖²`. -/
theorem norm_sq_le_two (x y : ℂ) : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have h2 : ‖x‖ ^ 2 ≤ (‖x - y‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x - y‖ - ‖y‖)]

/-- The core at one conductor `d`: `(d/φ(d)) P_d 1_{reg d} ≤ 2(T_d + [d=1] 1_{reg 1}|𝓜|²)`. -/
theorem conductor_core (Q R1 N : ℕ) (K : ℝ) (a : ℕ → ℂ) (M : ℝ → ℂ) (d : ℕ) (β : ℝ) :
    ((d : ℝ) / Nat.totient d) * (∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2) *
        (regSet Q R1 K d).indicator (fun _ => (1 : ℝ)) β
      ≤ 2 * (((d : ℝ) / (Nat.totient d : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars d,
          (regSet Q R1 K d).indicator
            (fun β => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β)
        + 2 * (if d = 1 then (regSet Q R1 K 1).indicator (fun β => ‖M β‖ ^ 2) β else 0) := by
  have hc0 : (0 : ℝ) ≤ (d : ℝ) / Nat.totient d := by positivity
  have hP0 : (0 : ℝ) ≤ ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hβ : β ∈ regSet Q R1 K d
  · rw [Set.indicator_of_mem hβ, mul_one]
    simp only [Set.indicator_of_mem hβ]
    by_cases hd1 : d = 1
    · subst hd1
      rw [if_pos rfl, Set.indicator_of_mem hβ]
      simp only [if_true, Nat.totient_one, Nat.cast_one, div_one, one_mul]
      have hcard : (ZetaQ.primitiveChars 1).card ≤ 1 :=
        Finset.card_le_one.mpr fun x _ y _ => Subsingleton.elim x y
      have hsum : ∑ ψ ∈ ZetaQ.primitiveChars 1, ‖twistSum N a ψ β‖ ^ 2
          ≤ ∑ ψ ∈ ZetaQ.primitiveChars 1, (2 * ‖twistSum N a ψ β - M β‖ ^ 2 + 2 * ‖M β‖ ^ 2) :=
        Finset.sum_le_sum fun ψ _ => norm_sq_le_two _ _
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
      have hcardR : ((ZetaQ.primitiveChars 1).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      have hM0 : (0 : ℝ) ≤ 2 * ‖M β‖ ^ 2 := by positivity
      nlinarith
    · simp only [if_neg hd1, sub_zero, add_zero, mul_zero]
      nlinarith [mul_nonneg hc0 hP0]
  · rw [Set.indicator_of_notMem hβ, mul_zero]
    simp only [Set.indicator_of_notMem hβ, Finset.sum_const_zero, mul_zero, zero_add]
    by_cases hd1 : d = 1
    · subst hd1
      rw [if_pos rfl, Set.indicator_of_notMem hβ, mul_zero]
    · rw [if_neg hd1, mul_zero]

/-- **The pointwise bound** `lhsF ≤ rhsF` (all of A⋆ except the integration). -/
theorem pointwise_bound (Q R1 N : ℕ) (K L : ℝ) (a : ℕ → ℂ) (M : ℝ → ℂ)
    (hR1 : 1 ≤ R1) (hQ : 0 < Q) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hcop : ∀ r ∈ Finset.Icc 1 R1, ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → Nat.Coprime n r)
    (hmult : ∀ y : ℝ, 0 < y →
      ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
        ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) ≤ L) (β : ℝ) :
    lhsF Q R1 N K a β ≤ rhsF Q R1 N K L a M β := by
  have hind0 : ∀ s : Set ℝ, 0 ≤ s.indicator (fun _ => (1 : ℝ)) β :=
    fun s => Set.indicator_nonneg (fun _ _ => zero_le_one) β
  -- step 1: the per-modulus bound under the ring indicator
  have step1 : lhsF Q R1 N K a β ≤ ∑ r ∈ Finset.Icc 1 R1, ∑ d ∈ r.divisors,
      (ringSet Q K r).indicator (fun _ => (1 : ℝ)) β * ((((d : ℝ) / Nat.totient d) *
          (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 / Nat.totient (r / d))) *
          ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2) := by
    unfold lhsF
    refine Finset.sum_le_sum fun r hr => ?_
    have hr0 : 0 < r := (Finset.mem_Icc.mp hr).1
    have e1 : ∑ b ∈ ZetaQ.reducedResidues r,
          (ringSet Q K r).indicator (fun β => ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2) β
        = (ringSet Q K r).indicator (fun _ => (1 : ℝ)) β *
            ∑ b ∈ ZetaQ.reducedResidues r, ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2 := by
      by_cases h : β ∈ ringSet Q K r
      · simp only [Set.indicator_of_mem h, one_mul]
      · simp only [Set.indicator_of_notMem h, zero_mul, Finset.sum_const_zero]
    rw [e1, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ring_point_bound hr0 N a β (hcop r hr)) (hind0 _)
  -- step 2: reindex `r = dm`
  have step2 := sum_Icc_divisors_reindex' R1 (fun r d =>
    (ringSet Q K r).indicator (fun _ => (1 : ℝ)) β * ((((d : ℝ) / Nat.totient d) *
      (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 / Nat.totient (r / d))) *
      ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2))
  -- step 3: at each conductor, the window bound and the core
  have step3 : ∀ d ∈ Finset.Icc 1 R1, ∑ m ∈ Finset.Icc 1 (R1 / d),
        (ringSet Q K (d * m)).indicator (fun _ => (1 : ℝ)) β * ((((d : ℝ) / Nat.totient d) *
          (((ArithmeticFunction.moebius (d * m / d) : ℤ) : ℝ) ^ 2 / Nat.totient (d * m / d))) *
          ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2)
      ≤ 2 * L * (((d : ℝ) / (Nat.totient d : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars d,
          (regSet Q R1 K d).indicator
            (fun β => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β)
        + (if d = 1 then 2 * L * (regSet Q R1 K 1).indicator (fun β => ‖M β‖ ^ 2) β else 0) := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hc0 : (0 : ℝ) ≤ (d : ℝ) / Nat.totient d := by positivity
    have hP0 : (0 : ℝ) ≤ ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have e2 : ∑ m ∈ Finset.Icc 1 (R1 / d),
        (ringSet Q K (d * m)).indicator (fun _ => (1 : ℝ)) β * ((((d : ℝ) / Nat.totient d) *
          (((ArithmeticFunction.moebius (d * m / d) : ℤ) : ℝ) ^ 2 / Nat.totient (d * m / d))) *
          ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2)
        = (((d : ℝ) / Nat.totient d) * ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2) *
          ∑ m ∈ Finset.Icc 1 (R1 / d), (ringSet Q K (d * m)).indicator (fun _ => (1 : ℝ)) β *
            (((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 / (Nat.totient m : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.mul_div_cancel_left m hd0]
      ring
    rw [e2]
    have hcore := conductor_core Q R1 N K a M d β
    have hE : (if d = 1 then 2 * L * (regSet Q R1 K 1).indicator (fun β => ‖M β‖ ^ 2) β else 0)
        = L * (2 * (if d = 1 then (regSet Q R1 K 1).indicator (fun β => ‖M β‖ ^ 2) β else 0)) := by
      split_ifs <;> ring
    rw [hE]
    calc (((d : ℝ) / Nat.totient d) * ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2) *
          ∑ m ∈ Finset.Icc 1 (R1 / d), (ringSet Q K (d * m)).indicator (fun _ => (1 : ℝ)) β *
            (((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 / (Nat.totient m : ℝ))
        ≤ (((d : ℝ) / Nat.totient d) * ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2) *
            (L * (regSet Q R1 K d).indicator (fun _ => (1 : ℝ)) β) :=
          mul_le_mul_of_nonneg_left (window_bound Q R1 d K L hd0 hQ hK hL hmult β)
            (mul_nonneg hc0 hP0)
      _ = L * (((d : ℝ) / Nat.totient d) * (∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2) *
            (regSet Q R1 K d).indicator (fun _ => (1 : ℝ)) β) := by ring
      _ ≤ L * (2 * (((d : ℝ) / (Nat.totient d : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars d,
            (regSet Q R1 K d).indicator
              (fun β => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β)
          + 2 * (if d = 1 then (regSet Q R1 K 1).indicator (fun β => ‖M β‖ ^ 2) β else 0)) :=
          mul_le_mul_of_nonneg_left hcore hL
      _ = 2 * L * (((d : ℝ) / (Nat.totient d : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars d,
            (regSet Q R1 K d).indicator
              (fun β => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β)
          + L * (2 * (if d = 1 then (regSet Q R1 K 1).indicator (fun β => ‖M β‖ ^ 2) β else 0)) := by
          ring
  calc lhsF Q R1 N K a β ≤ _ := step1
    _ = _ := step2
    _ ≤ ∑ d ∈ Finset.Icc 1 R1, (2 * L * (((d : ℝ) / (Nat.totient d : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars d,
          (regSet Q R1 K d).indicator
            (fun β => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β)
        + (if d = 1 then 2 * L * (regSet Q R1 K 1).indicator (fun β => ‖M β‖ ^ 2) β else 0)) :=
        Finset.sum_le_sum step3
    _ = rhsF Q R1 N K L a M β := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' (Finset.Icc 1 R1) 1,
          if_pos (Finset.mem_Icc.mpr ⟨le_refl 1, hR1⟩)]
        rfl

end AstarAux

/-- **A⋆ (lem:shell-star), corrected statement**: the region integral is parenthesised. -/
theorem ring_le_primitive_corr (Q R1 N : ℕ) (K Cμ U : ℝ) (a : ℕ → ℂ) (M : ℝ → ℂ)
    (hK : 1 ≤ K) (hRQ : 2 * K * R1 ≤ Q) (hCμ : 0 ≤ Cμ)
    (hsupp : ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → ∀ p : ℕ, p.Prime → p ∣ n → Q < p)
    (hmult : ∀ y : ℝ, 0 < y →
      ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
        ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) ≤ Real.log K + Cμ)
    (hMc : Continuous M) (hU : (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖M β‖ ^ 2) ≤ U) :
    ringMass Q R1 N K a
      ≤ 2 * (Real.log K + Cμ) * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ χ ∈ ZetaQ.primitiveChars r,
            (∫ β in {β : ℝ | 1 / ((R1 : ℝ) * Q) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Q)},
              ‖twistSum N a χ β - (if r = 1 then M β else 0)‖ ^ 2))
        + 2 * (Real.log K + Cμ) * U := by
  classical
  have hL : 0 ≤ Real.log K + Cμ := add_nonneg (Real.log_nonneg hK) hCμ
  have hU0 : 0 ≤ U :=
    le_trans (intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)) hU
  rcases Nat.eq_zero_or_pos R1 with hR0 | hR1
  · -- `R₁ = 0`: both sums are empty
    subst hR0
    have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by norm_num)
    simp only [ringMass, h0, Finset.sum_empty, mul_zero, zero_add]
    exact mul_nonneg (mul_nonneg (by norm_num) hL) hU0
  have hR1R : (1 : ℝ) ≤ R1 := by exact_mod_cast hR1
  have hKR : (1 : ℝ) ≤ K * R1 := by nlinarith
  have hQpos : (0 : ℝ) < Q := by linarith
  have hQ : 0 < Q := by exact_mod_cast hQpos
  have hRQn : R1 ≤ Q := by
    have h : (R1 : ℝ) ≤ Q := by nlinarith
    exact_mod_cast h
  -- the support is coprime to every modulus `r ≤ R₁`
  have hcop : ∀ r ∈ Finset.Icc 1 R1, ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → Nat.Coprime n r := by
    intro r hr n hn han
    apply Nat.coprime_of_dvd
    intro p hp hpn hpr
    have h1 := hsupp n hn han p hp hpn
    have h2 := Nat.le_of_dvd (Finset.mem_Icc.mp hr).1 hpr
    have h3 := (Finset.mem_Icc.mp hr).2
    omega
  -- measurability, boundedness, continuity, integrability
  have hring_meas : ∀ r : ℕ, MeasurableSet (ringSet Q K r) := fun r =>
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hreg_meas : ∀ d : ℕ, MeasurableSet (AstarAux.regSet Q R1 K d) := fun d =>
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hring_sub : ∀ r : ℕ,
      ringSet Q K r ⊆ Set.Icc (-(K / ((r : ℝ) * Q))) (K / ((r : ℝ) * Q)) := by
    intro r β hβ
    exact abs_le.mp hβ.2.le
  have hreg_sub : ∀ d : ℕ,
      AstarAux.regSet Q R1 K d ⊆ Set.Icc (-(K / ((d : ℝ) * Q))) (K / ((d : ℝ) * Q)) := by
    intro d β hβ
    exact abs_le.mp hβ.2
  have hcont_exp : ∀ r b : ℕ,
      Continuous (fun β : ℝ => ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2) := by
    intro r b
    simp only [ZetaQ.expSum]
    exact (continuous_finsetSum _ fun n _ => continuous_const.mul
      (ZetaQ.continuous_e.comp (continuous_const.mul (continuous_const.add continuous_id)))).norm.pow 2
  have hcont_tw : ∀ (d : ℕ) (χ : DirichletCharacter ℂ d),
      Continuous (fun β : ℝ => twistSum N a χ β) := by
    intro d χ
    simp only [twistSum]
    exact continuous_finsetSum _ fun n _ => continuous_const.mul
      (ZetaQ.continuous_e.comp (continuous_const.mul continuous_id))
  have hcont_h : ∀ (d : ℕ) (χ : DirichletCharacter ℂ d),
      Continuous (fun β : ℝ => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) := by
    intro d χ
    have hite : Continuous (fun β : ℝ => if d = 1 then M β else 0) := by
      by_cases hd1 : d = 1
      · simp only [hd1, if_true]
        exact hMc
      · simp only [hd1, if_false]
        exact continuous_const
    exact ((hcont_tw d χ).sub hite).norm.pow 2
  have hint_ring : ∀ r b : ℕ,
      Integrable ((ringSet Q K r).indicator
        (fun β : ℝ => ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2)) := fun r b =>
    (integrable_indicator_iff (hring_meas r)).mpr
      (((hcont_exp r b).integrableOn_Icc).mono_set (hring_sub r))
  have hint_reg : ∀ (d : ℕ) (χ : DirichletCharacter ℂ d),
      Integrable ((AstarAux.regSet Q R1 K d).indicator
        (fun β : ℝ => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2)) := fun d χ =>
    (integrable_indicator_iff (hreg_meas d)).mpr
      (((hcont_h d χ).integrableOn_Icc).mono_set (hreg_sub d))
  have hint_M : Integrable ((AstarAux.regSet Q R1 K 1).indicator (fun β : ℝ => ‖M β‖ ^ 2)) :=
    (integrable_indicator_iff (hreg_meas 1)).mpr
      (((hMc.norm.pow 2).integrableOn_Icc).mono_set (hreg_sub 1))
  have hint_T : ∀ d : ℕ, Integrable (fun β : ℝ => ((d : ℝ) / (Nat.totient d : ℝ)) *
      ∑ χ ∈ ZetaQ.primitiveChars d, (AstarAux.regSet Q R1 K d).indicator
        (fun β : ℝ => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β) := fun d =>
    (integrable_finsetSum _ fun χ _ => hint_reg d χ).const_mul _
  have hint_X : Integrable (fun β : ℝ => 2 * (Real.log K + Cμ) *
      ∑ d ∈ Finset.Icc 1 R1, ((d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ χ ∈ ZetaQ.primitiveChars d, (AstarAux.regSet Q R1 K d).indicator
          (fun β : ℝ => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β) :=
    (integrable_finsetSum _ fun d _ => hint_T d).const_mul _
  have hint_Y : Integrable (fun β : ℝ => 2 * (Real.log K + Cμ) *
      (AstarAux.regSet Q R1 K 1).indicator (fun β : ℝ => ‖M β‖ ^ 2) β) :=
    hint_M.const_mul _
  have hLi : Integrable (AstarAux.lhsF Q R1 N K a) := by
    unfold AstarAux.lhsF
    exact integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun b _ => hint_ring r b
  have hRi : Integrable (AstarAux.rhsF Q R1 N K (Real.log K + Cμ) a M) := by
    unfold AstarAux.rhsF
    exact hint_X.add hint_Y
  -- (A) the ring mass is the integral of `lhsF`
  have hA : ringMass Q R1 N K a = ∫ β, AstarAux.lhsF Q R1 N K a β := by
    unfold AstarAux.lhsF ringMass
    rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun b _ => hint_ring r b]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_finsetSum _ fun b _ => hint_ring r b]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_indicator (hring_meas r)]
  -- (B) the integral of `rhsF`
  have hT : ∀ d : ℕ, ∫ β : ℝ, ((d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ χ ∈ ZetaQ.primitiveChars d, (AstarAux.regSet Q R1 K d).indicator
          (fun β : ℝ => ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) β
      = ((d : ℝ) / (Nat.totient d : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars d,
          (∫ β in AstarAux.regSet Q R1 K d,
            ‖twistSum N a χ β - (if d = 1 then M β else 0)‖ ^ 2) := by
    intro d
    rw [integral_const_mul, integral_finsetSum _ fun χ _ => hint_reg d χ]
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [integral_indicator (hreg_meas d)]
  have hB : ∫ β, AstarAux.rhsF Q R1 N K (Real.log K + Cμ) a M β
      = 2 * (Real.log K + Cμ) * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ χ ∈ ZetaQ.primitiveChars r,
            (∫ β in AstarAux.regSet Q R1 K r,
              ‖twistSum N a χ β - (if r = 1 then M β else 0)‖ ^ 2))
        + 2 * (Real.log K + Cμ) * ∫ β in AstarAux.regSet Q R1 K 1, ‖M β‖ ^ 2 := by
    unfold AstarAux.rhsF
    rw [integral_add hint_X hint_Y, integral_const_mul, integral_const_mul,
      integral_indicator (hreg_meas 1), integral_finsetSum _ fun d _ => hint_T d]
    simp only [hT]
  -- (E) the model term
  have hE : ∫ β in AstarAux.regSet Q R1 K 1, ‖M β‖ ^ 2 ≤ U := by
    have hKQ : K / (((1 : ℕ) : ℝ) * Q) ≤ 1 / 2 := by
      rw [Nat.cast_one, one_mul, div_le_iff₀ hQpos]
      nlinarith
    have hsub : AstarAux.regSet Q R1 K 1 ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      intro β hβ
      exact abs_le.mp (le_trans hβ.2 hKQ)
    calc ∫ β in AstarAux.regSet Q R1 K 1, ‖M β‖ ^ 2
        ≤ ∫ β in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖M β‖ ^ 2 :=
          setIntegral_mono_set ((hMc.norm.pow 2).integrableOn_Icc)
            (Filter.Eventually.of_forall fun β => by simp only [Pi.zero_apply]; positivity)
            hsub.eventuallyLE
      _ = ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖M β‖ ^ 2 := by
          rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
      _ ≤ U := hU
  have h2L : (0 : ℝ) ≤ 2 * (Real.log K + Cμ) := mul_nonneg (by norm_num) hL
  calc ringMass Q R1 N K a = ∫ β, AstarAux.lhsF Q R1 N K a β := hA
    _ ≤ ∫ β, AstarAux.rhsF Q R1 N K (Real.log K + Cμ) a M β :=
        integral_mono hLi hRi fun β => AstarAux.pointwise_bound Q R1 N K (Real.log K + Cμ) a M
          hR1 hQ (by linarith) hL hcop hmult β
    _ = _ := hB
    _ ≤ 2 * (Real.log K + Cμ) * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ χ ∈ ZetaQ.primitiveChars r,
            (∫ β in AstarAux.regSet Q R1 K r,
              ‖twistSum N a χ β - (if r = 1 then M β else 0)‖ ^ 2))
        + 2 * (Real.log K + Cμ) * U := by
        have := mul_le_mul_of_nonneg_left hE h2L
        linarith

end TrackF
end ZetaShell
