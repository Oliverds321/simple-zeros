/-
Astar_Gauss (L7_6c, 3 Oct 2026): the arithmetic half of A⋆ (lem:shell-star, `ring_le_primitive_corr`).

1. **Imprimitive Gauss sum** (`gaussSum_changeLevel`): for `d ∣ r` and ANY `ψ mod d` (primitivity is not needed),
   `τ(ψ↑r) = μ(r/d) ψ(r/d) τ(ψ)` with Mathlib's `τ(χ) = Σ_{a ∈ ZMod r} χ(a) stdAddChar(a)` (MV Thm 9.10).
   Route (L7_6 round 2 plan): `[(a,r)=1] = Σ_{e|(a,r)} μ(e)`, swap; the multiples `a = ej` give
   `ψ(e) Σ_{j<r/e} ψ(j) e(j/(r/e))`; when `ψ(e) ≠ 0`, `(e,d) = 1`, so `r/e = dk`, and the block sum
   `Σ_{j<dk} ψ(j) e(j/(dk)) = (Σ_{c<d} ψ(c) e(c/(dk))) (Σ_{i<k} e(i/k)) = [k=1] τ(ψ)`.
   Corollary `norm_gaussSum_changeLevel_sq_le`: `‖τ(ψ↑r)‖² ≤ μ(r/d)² d` for primitive `ψ` (ZetaQ's `‖τ(ψ)‖ = √d`).
2. **eq:shell-gauss, identity form** (`totient_mul_sum_ring_eq`): for coefficients supported on `n` coprime to `r`,
   `φ(r) Σ*_{b mod r} |S(b/r + β)|² = Σ_{χ mod r} |τ(χ⁻¹)|² |S_χ(β)|²` (template: ZetaQ `primitive_decomposition`).
3. **Per-modulus bound** (`ring_point_bound`): grouping by conductor (ZetaQ `sum_all_chars_eq_sum_divisors`) and
   `φ(d)φ(r/d) ≤ φ(r)`:
   `Σ*_{b mod r} |S(b/r + β)|² ≤ Σ_{d | r} (d/φ(d)) (μ(r/d)²/φ(r/d)) Σ*_{ψ mod d} |S_ψ(β)|²`.
Imports: ZetaQ (trunk) and `ZetaShell.Defs.TF_Defs` (for `twistSum`) only. Namespace `ZetaShell.TrackF.AstarAux`.
-/
import ZetaShell.Defs.TF_Defs
import ZetaQ.CharSums

noncomputable section

open scoped ComplexConjugate

namespace ZetaShell
namespace TrackF
namespace AstarAux

/-! ### Sums over `ZMod n` as sums over `range n` -/

theorem sum_zmod_eq_sum_range {n : ℕ} [NeZero n] (g : ZMod n → ℂ) :
    ∑ x : ZMod n, g x = ∑ a ∈ Finset.range n, g (a : ZMod n) := by
  refine Finset.sum_nbij' (fun x => x.val) (fun a => (a : ZMod n)) ?_ ?_ ?_ ?_ ?_
  · intro x _
    simp [ZMod.val_lt]
  · intro a _
    simp
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro a ha
    have ha' : a < n := by simpa using ha
    exact ZMod.val_natCast_of_lt ha'
  · intro x _
    rw [ZMod.natCast_zmod_val]

/-- `τ(χ) = Σ_{a<n} χ(a) e(a/n)`. -/
theorem gaussSum_eq_sum_range {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    gaussSum χ (ZMod.stdAddChar (N := n))
      = ∑ a ∈ Finset.range n, χ (a : ZMod n) * ZetaQ.e ((a : ℝ) / n) := by
  rw [gaussSum, sum_zmod_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ZetaQ.stdAddChar_eq_e]

/-- The induced character on naturals: `ψ↑r(a) = [(a,r)=1] ψ(a)`. -/
theorem changeLevel_natCast {d r : ℕ} (hdr : d ∣ r) (ψ : DirichletCharacter ℂ d) (a : ℕ) :
    DirichletCharacter.changeLevel hdr ψ (a : ZMod r)
      = if Nat.Coprime a r then ψ (a : ZMod d) else 0 := by
  split_ifs with h
  · have hc : IsCoprime (a : ℤ) ((r : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' (R := ℂ) (χ := ψ) hdr hc
    push_cast at h1
    exact h1
  · apply MulChar.map_nonunit
    rwa [ZMod.isUnit_iff_coprime]

/-! ### Elementary sums -/

/-- `[(b,d) = 1] = Σ_{e | (b,d)} μ(e)` (as in `ZetaShell.coprime_indicator`, A1). -/
theorem coprime_indicator' (b d : ℕ) :
    (if Nat.Coprime b d then (1 : ℂ) else 0)
      = ∑ e ∈ (Nat.gcd b d).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd b d))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] at h
  rw [h]

/-- The multiples of `e ∣ d` below `d` are `e·j`, `j < d/e` (as in `ZetaShell.sum_filter_dvd_range`, A1). -/
theorem sum_filter_dvd_range' {d e : ℕ} (he : e ∣ d) (hd : 0 < d) (F : ℕ → ℂ) :
    ∑ b ∈ (Finset.range d).filter (fun b => e ∣ b), F b
      = ∑ j ∈ Finset.range (d / e), F (e * j) := by
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

/-- Blocks of length `d`: `Σ_{j < dk} F(j) = Σ_{i<k} Σ_{c<d} F(c + d i)`. -/
theorem sum_range_mul_block (d k : ℕ) (F : ℕ → ℂ) :
    ∑ j ∈ Finset.range (d * k), F j
      = ∑ i ∈ Finset.range k, ∑ c ∈ Finset.range d, F (c + d * i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [add_comm]

/-- `Σ_{i<k} e(i/k) = [k = 1]` for `k ≥ 1`. -/
theorem sum_e_range (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, ZetaQ.e ((i : ℝ) / k) = if k = 1 then 1 else 0 := by
  split_ifs with h1
  · subst h1
    simp
  · have hk2 : 1 < k := by omega
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    set z : ℂ := ZetaQ.e (1 / (k : ℝ)) with hz
    have hpow : ∀ i : ℕ, ZetaQ.e ((i : ℝ) / k) = z ^ i := by
      intro i
      rw [hz, ZetaQ.e, ZetaQ.e, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hzk : z ^ k = 1 := by
      rw [← hpow k, div_self hkR]
      simpa using ZetaQ.e_intCast 1
    have hz1 : z ≠ 1 := by
      intro h
      rw [hz, ZetaQ.e, Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : (((1 / (k : ℝ)) : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
        apply mul_left_cancel₀ hpi
        rw [hn]
        push_cast
        ring
      have h3 : (1 / (k : ℝ)) = (n : ℝ) := by exact_mod_cast h2
      have h4 : (0 : ℝ) < 1 / (k : ℝ) := by positivity
      have h5 : 1 / (k : ℝ) < 1 := by
        rw [div_lt_one (by positivity)]
        exact_mod_cast hk2
      rw [h3] at h4 h5
      have h6 : (0 : ℤ) < n := by exact_mod_cast h4
      have h7 : n < 1 := by exact_mod_cast h5
      omega
    simp_rw [hpow]
    rw [geom_sum_eq hz1, hzk, sub_self, zero_div]

/-- The block sum: `Σ_{j<dk} ψ(j) e(j/(dk)) = [k = 1] τ(ψ)`. -/
theorem block_gauss {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d) (k : ℕ) (hk : 0 < k) :
    ∑ j ∈ Finset.range (d * k), ψ (j : ZMod d) * ZetaQ.e ((j : ℝ) / ((d * k : ℕ) : ℝ))
      = if k = 1 then gaussSum ψ (ZMod.stdAddChar (N := d)) else 0 := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [sum_range_mul_block d k (fun j => ψ (j : ZMod d) * ZetaQ.e ((j : ℝ) / ((d * k : ℕ) : ℝ)))]
  have hterm : ∀ i c : ℕ,
      ψ ((c + d * i : ℕ) : ZMod d) * ZetaQ.e (((c + d * i : ℕ) : ℝ) / ((d * k : ℕ) : ℝ))
        = (ψ (c : ZMod d) * ZetaQ.e ((c : ℝ) / ((d * k : ℕ) : ℝ))) * ZetaQ.e ((i : ℝ) / k) := by
    intro i c
    have h1 : ((c + d * i : ℕ) : ZMod d) = (c : ZMod d) := by
      push_cast
      rw [ZMod.natCast_self]
      ring
    have h2 : ((c + d * i : ℕ) : ℝ) / ((d * k : ℕ) : ℝ)
        = (c : ℝ) / ((d * k : ℕ) : ℝ) + (i : ℝ) / k := by
      push_cast
      field_simp
    rw [h1, h2, ZetaQ.e_add]
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => hterm i c]
  rw [Finset.sum_comm, ← Finset.sum_mul_sum, sum_e_range k hk]
  split_ifs with h1
  · subst h1
    simp only [mul_one]
    rw [gaussSum_eq_sum_range]
  · rw [mul_zero]

/-! ### The imprimitive Gauss sum -/

/-- **Imprimitive Gauss sum** (MV Thm 9.10, any `ψ`): `τ(ψ↑r) = μ(r/d) ψ(r/d) τ(ψ)` for `d ∣ r`. -/
theorem gaussSum_changeLevel {d r : ℕ} [NeZero d] [NeZero r] (hdr : d ∣ r)
    (ψ : DirichletCharacter ℂ d) :
    gaussSum (DirichletCharacter.changeLevel hdr ψ) (ZMod.stdAddChar (N := r))
      = ((ArithmeticFunction.moebius (r / d) : ℤ) : ℂ) * ψ ((r / d : ℕ) : ZMod d)
          * gaussSum ψ (ZMod.stdAddChar (N := d)) := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [gaussSum_eq_sum_range]
  simp_rw [changeLevel_natCast hdr ψ]
  -- step 1: Möbius for the coprimality condition, and swap
  have step1 : ∑ a ∈ Finset.range r,
        (if Nat.Coprime a r then ψ (a : ZMod d) else 0) * ZetaQ.e ((a : ℝ) / r)
      = ∑ e ∈ r.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          ∑ a ∈ (Finset.range r).filter (fun a => e ∣ a), ψ (a : ZMod d) * ZetaQ.e ((a : ℝ) / r) := by
    have hind : ∀ a ∈ Finset.range r,
        (if Nat.Coprime a r then ψ (a : ZMod d) else 0) * ZetaQ.e ((a : ℝ) / r)
          = ∑ e ∈ (Nat.gcd a r).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
              (ψ (a : ZMod d) * ZetaQ.e ((a : ℝ) / r)) := by
      intro a _
      rw [← Finset.sum_mul, ← coprime_indicator']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hind]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_comm' (fun a e => ?_)
    simp only [Finset.mem_range, Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨ha, ⟨hea, her⟩, _⟩
      exact ⟨⟨ha, hea⟩, her, hr.ne'⟩
    · rintro ⟨⟨ha, hea⟩, her, _⟩
      exact ⟨ha, ⟨hea, her⟩, (Nat.gcd_pos_of_pos_right a hr).ne'⟩
  -- step 2: only `e = r/d` survives
  have step2 : ∀ e ∈ r.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
        ∑ a ∈ (Finset.range r).filter (fun a => e ∣ a), ψ (a : ZMod d) * ZetaQ.e ((a : ℝ) / r)
      = if e = r / d then ((ArithmeticFunction.moebius (r / d) : ℤ) : ℂ) * ψ ((r / d : ℕ) : ZMod d)
          * gaussSum ψ (ZMod.stdAddChar (N := d)) else 0 := by
    intro e he
    have her : e ∣ r := Nat.dvd_of_mem_divisors he
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos her hr
    have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he0.ne'
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [sum_filter_dvd_range' her hr]
    have hj : ∀ j ∈ Finset.range (r / e),
        ψ ((e * j : ℕ) : ZMod d) * ZetaQ.e (((e * j : ℕ) : ℝ) / r)
          = ψ (e : ZMod d) * (ψ (j : ZMod d) * ZetaQ.e ((j : ℝ) / ((r / e : ℕ) : ℝ))) := by
      intro j _
      have h1 : ((e * j : ℕ) : ℝ) / r = (j : ℝ) / ((r / e : ℕ) : ℝ) := by
        rw [Nat.cast_div her heR]
        push_cast
        field_simp
      rw [h1, Nat.cast_mul, map_mul]
      ring
    rw [Finset.sum_congr rfl hj, ← Finset.mul_sum]
    by_cases hψe : ψ (e : ZMod d) = 0
    · rw [hψe, zero_mul, mul_zero]
      by_cases hed : e = r / d
      · rw [if_pos hed, ← hed, hψe]
        ring
      · rw [if_neg hed]
    · have hu : IsUnit (e : ZMod d) := by
        by_contra h
        exact hψe (MulChar.map_nonunit ψ h)
      have hcop : Nat.Coprime e d := (ZMod.isUnit_iff_coprime e d).mp hu
      have hdre : d ∣ r / e := by
        have h1 : d ∣ e * (r / e) := by
          rw [Nat.mul_div_cancel' her]
          exact hdr
        exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left h1
      obtain ⟨k, hk⟩ := hdre
      have hre0 : 0 < r / e := Nat.div_pos (Nat.le_of_dvd hr her) he0
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk
          omega
        · exact h
      rw [hk, block_gauss ψ k hk0]
      by_cases hk1 : k = 1
      · rw [if_pos hk1]
        have hed : e = r / d := by
          rw [hk1, mul_one] at hk
          rw [← hk, Nat.div_div_self her hr.ne']
        rw [if_pos hed, hed]
        ring
      · rw [if_neg hk1, mul_zero, mul_zero]
        have hed : e ≠ r / d := by
          intro h
          apply hk1
          rw [h, Nat.div_div_self hdr hr.ne'] at hk
          exact (Nat.eq_of_mul_eq_mul_left hd (by rw [mul_one]; exact hk)).symm
        rw [if_neg hed]
  rw [step1, Finset.sum_congr rfl step2, Finset.sum_ite_eq']
  rw [if_pos (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdr, hr.ne'⟩)]

/-- `‖τ(ψ↑r)‖² ≤ μ(r/d)² d` for primitive `ψ mod d`, `d ∣ r`. -/
theorem norm_gaussSum_changeLevel_sq_le {d r : ℕ} [NeZero d] [NeZero r] (hdr : d ∣ r)
    {ψ : DirichletCharacter ℂ d} (hψ : ψ.IsPrimitive) :
    ‖gaussSum (DirichletCharacter.changeLevel hdr ψ) (ZMod.stdAddChar (N := r))‖ ^ 2
      ≤ ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d := by
  rw [gaussSum_changeLevel hdr ψ, norm_mul, norm_mul, ZetaQ.norm_gaussSum_of_isPrimitive hψ,
    mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h1 : ‖ψ ((r / d : ℕ) : ZMod d)‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
  have h0 : 0 ≤ ‖ψ ((r / d : ℕ) : ZMod d)‖ := norm_nonneg _
  have h2 : ‖((ArithmeticFunction.moebius (r / d) : ℤ) : ℂ)‖ ^ 2
      = ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 := by
    rw [Complex.norm_intCast, sq_abs]
  rw [h2]
  have h3 : ‖ψ ((r / d : ℕ) : ZMod d)‖ ^ 2 ≤ 1 := by nlinarith
  have h4 : (0 : ℝ) ≤ ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 := sq_nonneg _
  have h5 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  calc ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * ‖ψ ((r / d : ℕ) : ZMod d)‖ ^ 2 * (d : ℝ)
      ≤ ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * 1 * (d : ℝ) := by gcongr
    _ = _ := by ring

/-! ### eq:shell-gauss in identity form -/

/-- For coefficients supported on `n` coprime to `r`, the twist by `ψ↑r` is the twist by `ψ`. -/
theorem twistSum_changeLevel {d r : ℕ} (hdr : d ∣ r) (ψ : DirichletCharacter ℂ d) (N : ℕ)
    (a : ℕ → ℂ) (β : ℝ) (hcop : ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → Nat.Coprime n r) :
    twistSum N a (DirichletCharacter.changeLevel hdr ψ) β = twistSum N a ψ β := by
  unfold twistSum
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases han : a n = 0
  · simp [han]
  · rw [changeLevel_natCast hdr ψ n, if_pos (hcop n hn han)]

/-- **eq:shell-gauss, identity form**: for `(a_n)` supported on `n` coprime to `r`,
`φ(r) Σ*_{b mod r} |S(b/r + β)|² = Σ_{χ mod r} |τ(χ⁻¹)|² |S_χ(β)|²`. -/
theorem totient_mul_sum_ring_eq {r : ℕ} [NeZero r] (N : ℕ) (a : ℕ → ℂ) (β : ℝ)
    (hcop : ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → Nat.Coprime n r) :
    (Nat.totient r : ℝ) * ∑ b ∈ ZetaQ.reducedResidues r, ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ r,
          ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := r))‖ ^ 2 * ‖twistSum N a χ β‖ ^ 2 := by
  classical
  have hval : ∀ b : ZMod r, ((b.val : ℕ) : ZMod r) = b := fun b => ZMod.natCast_zmod_val b
  set f : ZMod r → ℂ := fun x => ZetaQ.expSum N a ((x.val : ℝ) / r + β) with hfdef
  -- (1) the transfer, at every character (units only, by the support hypothesis)
  have transfer : ∀ χ : DirichletCharacter ℂ r,
      ∑ x : ZMod r, χ⁻¹ x * f x
        = gaussSum χ⁻¹ (ZMod.stdAddChar (N := r)) * twistSum N a χ β := by
    intro χ
    simp only [hfdef, ZetaQ.expSum, twistSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases han : a n = 0
    · simp [han]
    · have hu : IsUnit (n : ZMod r) := (ZMod.isUnit_iff_coprime n r).mpr (hcop n hn han)
      have hg := gaussSum_mulShift_eq χ⁻¹ (ZMod.stdAddChar (N := r)) hu.unit
      rw [inv_inv, IsUnit.unit_spec] at hg
      have hsum : ∑ x : ZMod r, χ⁻¹ x * (a n * ZetaQ.e ((n : ℝ) * ((x.val : ℝ) / r + β)))
          = a n * ZetaQ.e ((n : ℝ) * β)
              * gaussSum χ⁻¹ ((ZMod.stdAddChar (N := r)).mulShift (n : ZMod r)) := by
        rw [gaussSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [AddChar.mulShift_apply]
        have h1 : (n : ZMod r) * x = ((x.val * n : ℕ) : ZMod r) := by
          push_cast [hval x]
          ring
        have h2 : (n : ℝ) * ((x.val : ℝ) / r + β) = ((x.val * n : ℕ) : ℝ) / r + (n : ℝ) * β := by
          push_cast
          ring
        rw [h1, ZetaQ.stdAddChar_eq_e, h2, ZetaQ.e_add]
        ring
      rw [hsum, hg]
      ring
  -- (2) inversion is a bijection of the character group
  have reindex : ∑ χ : DirichletCharacter ℂ r, ‖∑ x : ZMod r, χ⁻¹ x * f x‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ r, ‖∑ x : ZMod r, χ x * f x‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ r)) _ _ (fun _ => rfl)
  -- (3) the units of `ZMod r` are the reduced residues
  have himg : (ZetaQ.unitResidues r).image (fun b : ZMod r => b.val) = ZetaQ.reducedResidues r := by
    ext c
    simp only [Finset.mem_image, ZetaQ.mem_unitResidues, ZetaQ.mem_reducedResidues]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨ZMod.val_lt b, (ZMod.isUnit_iff_coprime b.val r).mp (by rw [hval b]; exact hb)⟩
    · rintro ⟨hlt, hcop'⟩
      exact ⟨(c : ZMod r), (ZMod.isUnit_iff_coprime c r).mpr hcop', ZMod.val_natCast_of_lt hlt⟩
  have hsum5 : ∑ b ∈ ZetaQ.unitResidues r, ‖f b‖ ^ 2
      = ∑ c ∈ ZetaQ.reducedResidues r, ‖ZetaQ.expSum N a ((c : ℝ) / r + β)‖ ^ 2 := by
    rw [← himg, Finset.sum_image]
    intro b _ c _ h
    have h' : b.val = c.val := h
    rw [← hval b, ← hval c, h']
  rw [← hsum5, ← ZetaQ.sum_sq_over_all_chars f, ← reindex]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [transfer χ, norm_mul, mul_pow]

/-! ### The per-modulus bound -/

/-- `μ(m)² d / φ(dm) ≤ (d/φ(d)) (μ(m)²/φ(m))`, as `μ² d ≤ φ(r) · c(d, r/d)`. -/
theorem coef_le {d r : ℕ} (hr : 0 < r) (hd : d ∣ r) :
    ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d
      ≤ (Nat.totient r : ℝ) * (((d : ℝ) / Nat.totient d) *
          (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 / Nat.totient (r / d))) := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  have hm0 : 0 < r / d := Nat.div_pos (Nat.le_of_dvd hr hd) hd0
  have h1 : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
  have h2 : (0 : ℝ) < Nat.totient (r / d) := by exact_mod_cast Nat.totient_pos.mpr hm0
  have hle : (Nat.totient d : ℝ) * Nat.totient (r / d) ≤ Nat.totient r := by
    have h := Nat.totient_super_multiplicative d (r / d)
    rw [Nat.mul_div_cancel' hd] at h
    exact_mod_cast h
  have hμ : (0 : ℝ) ≤ ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d := by positivity
  have hone : (1 : ℝ) ≤ (Nat.totient r : ℝ) / ((Nat.totient d : ℝ) * Nat.totient (r / d)) := by
    rw [one_le_div (by positivity)]
    exact hle
  calc ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d
      = ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d * 1 := by ring
    _ ≤ ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d *
          ((Nat.totient r : ℝ) / ((Nat.totient d : ℝ) * Nat.totient (r / d))) :=
        mul_le_mul_of_nonneg_left hone hμ
    _ = (Nat.totient r : ℝ) * (((d : ℝ) / Nat.totient d) *
          (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 / Nat.totient (r / d))) := by
        field_simp

/-- **Per-modulus bound**: for `(a_n)` supported on `n` coprime to `r ≥ 1`,
`Σ*_{b mod r} |S(b/r + β)|² ≤ Σ_{d | r} (d/φ(d)) (μ(r/d)²/φ(r/d)) Σ*_{ψ mod d} |S_ψ(β)|²`. -/
theorem ring_point_bound {r : ℕ} (hr : 0 < r) (N : ℕ) (a : ℕ → ℂ) (β : ℝ)
    (hcop : ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → Nat.Coprime n r) :
    ∑ b ∈ ZetaQ.reducedResidues r, ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2
      ≤ ∑ d ∈ r.divisors, (((d : ℝ) / Nat.totient d) *
          (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 / Nat.totient (r / d))) *
          ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2 := by
  have : NeZero r := ⟨hr.ne'⟩
  have hφr : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr
  have hT := totient_mul_sum_ring_eq N a β hcop
  set F : DirichletCharacter ℂ r → ℝ := fun χ =>
    ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := r))‖ ^ 2 * ‖twistSum N a χ β‖ ^ 2 with hF
  let G : ∀ d : ℕ, DirichletCharacter ℂ d → ℂ := fun d ψ =>
    if h : d ∣ r then ((F (DirichletCharacter.changeLevel h ψ) : ℝ) : ℂ) else 0
  have hG : ∀ (d : ℕ) (hd : d ∣ r) (ψ : DirichletCharacter ℂ d),
      G r (DirichletCharacter.changeLevel hd ψ) = G d ψ := by
    intro d hd ψ
    simp only [G, dif_pos hd, dif_pos (dvd_refl r), DirichletCharacter.changeLevel_self]
  have hdec := ZetaQ.sum_all_chars_eq_sum_divisors G hG
  have hGr : ∀ χ : DirichletCharacter ℂ r, G r χ = ((F χ : ℝ) : ℂ) := by
    intro χ
    simp only [G, dif_pos (dvd_refl r), DirichletCharacter.changeLevel_self]
  have hdecR : ∑ χ : DirichletCharacter ℂ r, F χ
      = ∑ d ∈ r.divisors, ∑ ψ ∈ ZetaQ.primitiveChars d,
          (if h : d ∣ r then F (DirichletCharacter.changeLevel h ψ) else 0) := by
    apply Complex.ofReal_injective
    push_cast
    rw [← Finset.sum_congr rfl fun χ _ => hGr χ, hdec]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun ψ _ => ?_
    simp only [G]
    split_ifs <;> simp
  -- each primitive term
  have hterm : ∀ d ∈ r.divisors, ∀ ψ ∈ ZetaQ.primitiveChars d,
      (if h : d ∣ r then F (DirichletCharacter.changeLevel h ψ) else 0)
        ≤ ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d * ‖twistSum N a ψ β‖ ^ 2 := by
    intro d hd ψ hψ
    have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
    have : NeZero d := ⟨(Nat.pos_of_dvd_of_pos hdr hr).ne'⟩
    have hψp : ψ.IsPrimitive := ZetaQ.mem_primitiveChars.mp hψ
    rw [dif_pos hdr]
    simp only [hF]
    rw [← map_inv (DirichletCharacter.changeLevel hdr) ψ, twistSum_changeLevel hdr ψ N a β hcop]
    exact mul_le_mul_of_nonneg_right
      (norm_gaussSum_changeLevel_sq_le hdr (ZetaQ.isPrimitive_inv hψp)) (sq_nonneg _)
  have hmain : (Nat.totient r : ℝ) *
        ∑ b ∈ ZetaQ.reducedResidues r, ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2
      ≤ (Nat.totient r : ℝ) * ∑ d ∈ r.divisors, (((d : ℝ) / Nat.totient d) *
          (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 / Nat.totient (r / d))) *
          ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2 := by
    rw [hT, hdecR, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
    calc ∑ ψ ∈ ZetaQ.primitiveChars d,
          (if h : d ∣ r then F (DirichletCharacter.changeLevel h ψ) else 0)
        ≤ ∑ ψ ∈ ZetaQ.primitiveChars d,
            ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d * ‖twistSum N a ψ β‖ ^ 2 :=
          Finset.sum_le_sum fun ψ hψ => hterm d hd ψ hψ
      _ = (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 * d) *
            ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ((Nat.totient r : ℝ) * (((d : ℝ) / Nat.totient d) *
            (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 / Nat.totient (r / d)))) *
            ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (coef_le hr hdr)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = (Nat.totient r : ℝ) * ((((d : ℝ) / Nat.totient d) *
            (((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) ^ 2 / Nat.totient (r / d))) *
            ∑ ψ ∈ ZetaQ.primitiveChars d, ‖twistSum N a ψ β‖ ^ 2) := by ring
  exact le_of_mul_le_mul_left hmain hφr

end AstarAux
end TrackF
end ZetaShell
