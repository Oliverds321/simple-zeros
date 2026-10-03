/-
L7_9 helper for node K4 (`principal_gauss_hole`, Lemma K.4, lem:K-R).
Route (Cauchy–Schwarz form of the draft's identity): for `(n, r) = 1` the Ramanujan sum
`c_r(n) = Σ_{b ∈ (ℤ/r)^×} e(nb/r)` equals `μ(r)`, so for `a` supported on integers coprime to `r`,
`Σ_{b} S(b/r + β) = μ(r) S(β)`; Cauchy–Schwarz over the `φ(r)` reduced residues gives
`μ(r)² |S(β)|² ≤ φ(r) Σ_b |S(b/r + β)|²`.
`c_r(n) = Σ_{d | r} μ(d) Σ_{k < r/d} e(n k/(r/d))`, and the inner geometric sum is `0` unless `r/d = 1`.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section
open Finset

namespace ZetaShell
namespace LemmaK
namespace K4Aux

open ZetaQ

lemma sum_moebius_divisors (g : ℕ) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℂ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f g) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h' := congrArg (fun z : ℤ => (z : ℂ)) h
  simp only [Int.cast_sum] at h'
  rw [h']
  split_ifs <;> simp

lemma e_nat_mul (k : ℕ) (x : ℝ) : ZetaQ.e ((k : ℝ) * x) = ZetaQ.e x ^ k := by
  unfold ZetaQ.e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- the geometric sum `Σ_{k<m} e(n/m)^k` for `(n, m) = 1`. -/
lemma geom_e (n m : ℕ) (hm : 0 < m) (hcop : Nat.Coprime n m) :
    ∑ k ∈ range m, ZetaQ.e ((n : ℝ) / m) ^ k = if m = 1 then 1 else 0 := by
  split_ifs with h1
  · subst h1; simp
  · have hprim : IsPrimitiveRoot (ZetaQ.e ((n : ℝ) / m)) m := by
      have := Complex.isPrimitiveRoot_exp_of_coprime n m hm.ne' hcop
      convert this using 1
      unfold ZetaQ.e
      congr 1
      push_cast
      ring
    exact hprim.geom_sum_eq_zero (by omega)

/-- **Ramanujan sum at a coprime argument**: `Σ_{b ∈ (ℤ/r)^×} e(nb/r) = μ(r)` for `(n, r) = 1`. -/
theorem ramanujan_coprime (r n : ℕ) (hr : 0 < r) (hn : Nat.Coprime n r) :
    ∑ b ∈ reducedResidues r, ZetaQ.e ((n : ℝ) * (b : ℝ) / (r : ℝ))
      = (ArithmeticFunction.moebius r : ℂ) := by
  classical
  set f : ℕ → ℂ := fun b => ZetaQ.e ((n : ℝ) * (b : ℝ) / (r : ℝ)) with hf
  -- (1) the coprimality indicator as a Möbius sum
  have h1 : ∑ b ∈ reducedResidues r, f b
      = ∑ b ∈ range r, ∑ d ∈ (Nat.gcd b r).divisors, (ArithmeticFunction.moebius d : ℂ) * f b := by
    have hRR : reducedResidues r = (range r).filter (fun b => Nat.Coprime b r) := by
      ext b; rw [mem_reducedResidues, mem_filter, mem_range]
    rw [hRR, sum_filter]
    refine sum_congr rfl fun b _ => ?_
    rw [← sum_mul, sum_moebius_divisors]
    by_cases hc : Nat.Coprime b r
    · rw [if_pos hc, if_pos (Nat.Coprime.gcd_eq_one hc), one_mul]
    · rw [if_neg hc, if_neg (fun h => hc h), zero_mul]
  -- (2) swap the sums
  have h2 : ∑ b ∈ range r, ∑ d ∈ (Nat.gcd b r).divisors, (ArithmeticFunction.moebius d : ℂ) * f b
      = ∑ d ∈ r.divisors, ∑ b ∈ (range r).filter (fun b => d ∣ b),
          (ArithmeticFunction.moebius d : ℂ) * f b := by
    refine sum_comm' fun b d => ?_
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨hb, ⟨hdb, hdr⟩, _⟩
      exact ⟨⟨hb, hdb⟩, hdr, hr.ne'⟩
    · rintro ⟨⟨hb, hdb⟩, hdr, _⟩
      exact ⟨hb, ⟨hdb, hdr⟩, Nat.gcd_ne_zero_right hr.ne'⟩
  -- (3) each inner sum
  have h3 : ∀ d ∈ r.divisors, ∑ b ∈ (range r).filter (fun b => d ∣ b),
      (ArithmeticFunction.moebius d : ℂ) * f b
        = (ArithmeticFunction.moebius d : ℂ) * (if r / d = 1 then 1 else 0) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdr, _⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdr hr
    set m := r / d with hm
    have hrm : r = d * m := (Nat.mul_div_cancel' hdr).symm
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hrm; omega
      · exact h
    have himg : (range r).filter (fun b => d ∣ b) = (range m).image (fun k => d * k) := by
      ext b
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hb, k, rfl⟩
        refine ⟨k, ?_, rfl⟩
        rw [hrm] at hb
        exact Nat.lt_of_mul_lt_mul_left hb
      · rintro ⟨k, hk, rfl⟩
        refine ⟨?_, dvd_mul_right d k⟩
        rw [hrm]
        exact Nat.mul_lt_mul_of_pos_left hk hd0
    have hinj : Set.InjOn (fun k => d * k) (range m : Set ℕ) := by
      intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hd0 hxy
    rw [himg, sum_image hinj, ← mul_sum]
    congr 1
    have hterm : ∀ k ∈ range m, f (d * k) = ZetaQ.e ((n : ℝ) / m) ^ k := by
      intro k _
      simp only [hf]
      rw [← e_nat_mul]
      congr 1
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      rw [hrm]
      push_cast
      field_simp
    rw [sum_congr rfl hterm]
    have hcop : Nat.Coprime n m := Nat.Coprime.coprime_dvd_right (Dvd.intro_left d hrm.symm) hn
    exact geom_e n m hm0 hcop
  rw [h1, h2, sum_congr rfl h3]
  rw [sum_eq_single r]
  · rw [Nat.div_self hr, if_pos rfl, mul_one]
  · intro d hd hdr
    rw [Nat.mem_divisors] at hd
    have : r / d ≠ 1 := by
      intro h
      apply hdr
      have := Nat.mul_div_cancel' hd.1
      rw [h, mul_one] at this
      exact this
    rw [if_neg this, mul_zero]
  · intro h
    exact absurd (Nat.mem_divisors_self r hr.ne') h

theorem card_reducedResidues (r : ℕ) : (reducedResidues r).card = Nat.totient r := by
  classical
  rw [Nat.totient]
  congr 1
  ext b
  rw [mem_reducedResidues, mem_filter, mem_range, Nat.coprime_comm]

/-- `Σ_{b ∈ (ℤ/r)^×} S(b/r + β) = μ(r) S(β)` for `a` supported on integers coprime to `r`. -/
theorem sum_expSum_shift (r N : ℕ) (hr : 0 < r) (a : ℕ → ℂ)
    (hcop : ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → Nat.Coprime n r) (β : ℝ) :
    ∑ b ∈ reducedResidues r, expSum N a ((b : ℝ) / (r : ℝ) + β)
      = (ArithmeticFunction.moebius r : ℂ) * expSum N a β := by
  unfold expSum
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have hsplit : ∀ b ∈ reducedResidues r, a n * ZetaQ.e ((n : ℝ) * ((b : ℝ) / (r : ℝ) + β))
      = a n * ZetaQ.e ((n : ℝ) * β) * ZetaQ.e ((n : ℝ) * (b : ℝ) / (r : ℝ)) := by
    intro b _
    rw [show (n : ℝ) * ((b : ℝ) / (r : ℝ) + β) = (n : ℝ) * (b : ℝ) / (r : ℝ) + (n : ℝ) * β by ring,
      e_add]
    ring
  rw [sum_congr rfl hsplit, ← mul_sum]
  by_cases ha : a n = 0
  · simp [ha]
  · rw [ramanujan_coprime r n hr (hcop n hn ha)]
    ring

theorem principal_gauss_hole_aux (r N : ℕ) (hr : 0 < r) (a : ℕ → ℂ)
    (hcop : ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → Nat.Coprime n r) (β : ℝ) :
    ((ArithmeticFunction.moebius r : ℝ) ^ 2 / (Nat.totient r : ℝ)) * ‖ZetaQ.expSum N a β‖ ^ 2
      ≤ ∑ b ∈ ZetaQ.reducedResidues r, ‖ZetaQ.expSum N a ((b : ℝ) / (r : ℝ) + β)‖ ^ 2 := by
  have hphi : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr
  have hid := sum_expSum_shift r N hr a hcop β
  -- `‖μ(r) S(β)‖² = μ(r)² ‖S(β)‖²`
  have hnorm : ‖(ArithmeticFunction.moebius r : ℂ) * expSum N a β‖ ^ 2
      = (ArithmeticFunction.moebius r : ℝ) ^ 2 * ‖expSum N a β‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    congr 1
    rw [show ((ArithmeticFunction.moebius r : ℤ) : ℂ) = (((ArithmeticFunction.moebius r : ℤ) : ℝ) : ℂ)
      by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- Cauchy–Schwarz
  have hCS : ‖∑ b ∈ reducedResidues r, expSum N a ((b : ℝ) / (r : ℝ) + β)‖ ^ 2
      ≤ (Nat.totient r : ℝ) * ∑ b ∈ reducedResidues r, ‖expSum N a ((b : ℝ) / (r : ℝ) + β)‖ ^ 2 := by
    have h1 := norm_sum_le (reducedResidues r) (fun b => expSum N a ((b : ℝ) / (r : ℝ) + β))
    have h2 := sq_sum_le_card_mul_sum_sq (s := reducedResidues r)
      (f := fun b => ‖expSum N a ((b : ℝ) / (r : ℝ) + β)‖)
    rw [card_reducedResidues] at h2
    calc ‖∑ b ∈ reducedResidues r, expSum N a ((b : ℝ) / (r : ℝ) + β)‖ ^ 2
        ≤ (∑ b ∈ reducedResidues r, ‖expSum N a ((b : ℝ) / (r : ℝ) + β)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  rw [hid, hnorm] at hCS
  rw [div_mul_eq_mul_div, div_le_iff₀ hphi]
  linarith

end K4Aux
end LemmaK
end ZetaShell
