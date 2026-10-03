/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ZetaQ.Budget
import ZetaQ.AbelLogPow
import ZetaQ.FrobRow8
import ZetaQ.JoinCert

/-!
# The dyadic family `(Q/2, Q]`: differencing the N2 counts at `Q` and `⌊Q/2⌋`

* (a) `dyadic_count_diff` / `dyadic_log_diff` / `dyadic_logsq_diff` — the three family sums over
  `Finset.Ioc (Qn/2) Qn` are differences of `N2.Astar` / `N2.Alog` / `N2.Alog2` at `Qn` and `Qn/2`.
* (b) `famLogCond_dyadic_bound`, `famLogSqCond_dyadic_bound` — explicit two-sided bounds
  `|Σφ*(q) log q − |𝔉_dyad|·(log Q − (1/2 − log2/3))| ≤ 28 Q (1+log Q)³`,
  `|Σφ*(q) log²q − |𝔉_dyad|·h(Q)| ≤ 54 Q (1+log Q)⁴`, `h = (log Q + log2/3)² − (log Q + log2/3)
  + 1/2 − (4/9) log²2`; and `sizeR_dyadic_bound` (two-sided size).
* (c) `famRvMLower_dyadic_of_design` — `FamRvMLower Family.dyadic` along the design of record.
* (d) `famEll1Sq_dyadic_eq`, `famEll1Sq_dyadic_eval` — row 8's `Σφ*ℓ_{1,q}²` for the dyadic family.
* (e) `avg_log_dyadic` — `⟨log q⟩`, `⟨log²q⟩`, variance `1/4 − (4/9)log²2` for the dyadic family.
-/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace ZetaQ

open ZetaQ.Normalisation

/-! ## (a) Differencing identities -/

theorem sum_Ioc_half_eq_sub (f : ℕ → ℝ) (N : ℕ) :
    ∑ q ∈ Finset.Ioc (N / 2) N, f q
      = (∑ q ∈ Finset.Icc 1 N, f q) - ∑ q ∈ Finset.Icc 1 (N / 2), f q := by
  have hcons := Finset.sum_Ioc_consecutive f (Nat.zero_le (N / 2)) (Nat.div_le_self N 2)
  rw [Icc_one_eq_Ioc_zero', Icc_one_eq_Ioc_zero']
  linarith

/-- `Σ_{Q/2<q≤Q} φ*(q) = Astar Q − Astar ⌊Q/2⌋`. -/
theorem dyadic_count_diff (N : ℕ) :
    ∑ q ∈ Finset.Ioc (N / 2) N, (phiStar q : ℝ) = N2.Astar N - N2.Astar (N / 2) :=
  sum_Ioc_half_eq_sub (fun q => (phiStar q : ℝ)) N

/-- `Σ_{Q/2<q≤Q} φ*(q) log q = Alog Q − Alog ⌊Q/2⌋`. -/
theorem dyadic_log_diff (N : ℕ) :
    ∑ q ∈ Finset.Ioc (N / 2) N, (phiStar q : ℝ) * Real.log q
      = N2.Alog N - N2.Alog (N / 2) :=
  sum_Ioc_half_eq_sub (fun q => (phiStar q : ℝ) * Real.log q) N

/-- `Σ_{Q/2<q≤Q} φ*(q) (log q)² = Alog2 Q − Alog2 ⌊Q/2⌋`. -/
theorem dyadic_logsq_diff (N : ℕ) :
    ∑ q ∈ Finset.Ioc (N / 2) N, (phiStar q : ℝ) * Real.log q ^ 2
      = N2.Alog2 N - N2.Alog2 (N / 2) :=
  sum_Ioc_half_eq_sub (fun q => (phiStar q : ℝ) * Real.log q ^ 2) N

/-! ## (b) Explicit bounds by differencing `N2.Astar/Alog/Alog2_bound` at `N` and `N/2` -/

/-- The elementary facts about `n = ⌊N/2⌋`: `1 ≤ n`, `2n ≤ N ≤ 2n+1`, and
`δ := log N − log n − log 2 = log(N/2n) ∈ [0, 1/(2n)]`. -/
theorem half_facts (N : ℕ) (hN : 2 ≤ N) :
    (1 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) ∧ 2 * ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ)
      ∧ (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1
      ∧ 0 ≤ Real.log (N : ℝ) - Real.log ((N / 2 : ℕ) : ℝ) - Real.log 2
      ∧ (Real.log (N : ℝ) - Real.log ((N / 2 : ℕ) : ℝ) - Real.log 2)
          * (2 * ((N / 2 : ℕ) : ℝ)) ≤ 1 := by
  have h1 : 1 ≤ N / 2 := by omega
  have h2 : 2 * (N / 2) ≤ N := by omega
  have h3 : N ≤ 2 * (N / 2) + 1 := by omega
  have h1R : (1 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h1
  have h2R : 2 * ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
  have h3R : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h3
  have hb0 : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hδ : Real.log (N : ℝ) - Real.log ((N / 2 : ℕ) : ℝ) - Real.log 2
      = Real.log ((N : ℝ) / (2 * ((N / 2 : ℕ) : ℝ))) := by
    rw [Real.log_div (ne_of_gt hN0) (by positivity), Real.log_mul (by norm_num) (ne_of_gt hb0)]
    ring
  have hratio1 : 1 ≤ (N : ℝ) / (2 * ((N / 2 : ℕ) : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  refine ⟨h1R, h2R, h3R, ?_, ?_⟩
  · rw [hδ]; exact Real.log_nonneg hratio1
  · rw [hδ]
    have hle := Real.log_le_sub_one_of_pos
      (by positivity : (0:ℝ) < (N : ℝ) / (2 * ((N / 2 : ℕ) : ℝ)))
    have hpos : (0:ℝ) < 2 * ((N / 2 : ℕ) : ℝ) := by positivity
    calc Real.log ((N : ℝ) / (2 * ((N / 2 : ℕ) : ℝ))) * (2 * ((N / 2 : ℕ) : ℝ))
        ≤ ((N : ℝ) / (2 * ((N / 2 : ℕ) : ℝ)) - 1) * (2 * ((N / 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hle hpos.le
      _ = (N : ℝ) - 2 * ((N / 2 : ℕ) : ℝ) := by field_simp
      _ ≤ 1 := by linarith

theorem c18_le : (18 / Real.pi ^ 4 : ℝ) ≤ 0.19 := by
  have hpi : 3.14 < Real.pi := Real.pi_gt_d2
  have h4 : (3.14 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) hpi.le 4
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The dyadic conductor shift is the exact `1/2 − (log 2)/3 = 0.26895094…`** (it used to be
the literal `0.26895`, `9.4·10⁻⁷` BELOW the exact
value, and this lemma bounded the gap by `10⁻⁶` — it is now an identity, kept so that
`famRvMLower_dyadic_of_design`'s rounding absorption reads unchanged). -/
theorem conductorShift_dyadic_err :
    0 ≤ (1 / 2 - Real.log 2 / 3) - Family.dyadic.conductorShift ∧
    (1 / 2 - Real.log 2 / 3) - Family.dyadic.conductorShift ≤ 1 / 1000000 := by
  constructor <;> simp only [Family.conductorShift, sub_self] <;> norm_num

set_option maxHeartbeats 400000 in
/-- **The FAMILY step of §12.2 for `Family.dyadic`, with an EXPLICIT two-sided error.**
`|Σ_{Q/2<q≤Q} φ*(q) log q − |𝔉_dyad|·(log Q − (1/2 − log2/3))| ≤ 28·Q·(1 + log Q)³`.
The exact dyadic conductor shift is `1/2 − (log 2)/3 = 0.2689509…` (paper §12.2:
`⟨log q⟩ = log Q + (log 2)/3 − 1/2`), and it is `Family.dyadic.conductorShift`
(the literal `0.26895`, `9.4·10⁻⁷` below it, was the earlier value; `conductorShift_dyadic_err`). -/
theorem famLogCond_dyadic_bound (N : ℕ) (hN : 2 ≤ N) :
    |(∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q)
        - Family.sizeR Family.dyadic N * (Real.log N - (1 / 2 - Real.log 2 / 3))|
      ≤ 28 * (N : ℝ) * (1 + Real.log N) ^ 3 := by
  have hmod : Family.dyadic.moduli N = Finset.Ioc (N / 2) N := rfl
  rw [hmod, dyadic_log_diff, sizeR_dyadic_eq]
  obtain ⟨hb1, h2b, hb2, hδ0, hδ⟩ := half_facts N hN
  have hN1 : 1 ≤ N := by omega
  have hn1 : 1 ≤ N / 2 := by omega
  have hA1 := N2.Alog_bound N hN1
  have hA1' := N2.Alog_bound (N / 2) hn1
  have hA0 := N2.Astar_bound N hN1
  have hA0' := N2.Astar_bound (N / 2) hn1
  have hc19 := c18_le
  set a : ℝ := (N : ℝ) with hadef
  set b : ℝ := ((N / 2 : ℕ) : ℝ) with hbdef
  set L : ℝ := Real.log a with hLdef
  set L' : ℝ := Real.log b with hL'def
  set ℓ : ℝ := Real.log 2 with hℓdef
  set c : ℝ := 18 / Real.pi ^ 4 with hcdef
  set A1 := N2.Alog N with hA1def
  set A1' := N2.Alog (N / 2) with hA1'def
  set A0 := N2.Astar N with hA0def
  set A0' := N2.Astar (N / 2) with hA0'def
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hℓ1 : 0.6931471803 < ℓ := Real.log_two_gt_d9
  have hℓ2 : ℓ < 0.6931471808 := Real.log_two_lt_d9
  have ha2 : (2 : ℝ) ≤ a := by rw [hadef]; exact_mod_cast hN
  have ha0 : 0 ≤ a := by linarith
  have hL'0 : 0 ≤ L' := Real.log_nonneg hb1
  have hL'L : L' ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hℓL : ℓ ≤ L := Real.log_le_log (by norm_num) ha2
  have hL0 : 0 ≤ L := by linarith
  have hba : b ≤ a / 2 := by linarith
  have hP3 : (1 + L') ^ 3 ≤ (1 + L) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hP2 : (1 + L') ^ 2 ≤ (1 + L) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hP31 : 1 ≤ (1 + L) ^ 3 := one_le_pow₀ (by linarith)
  -- the four error pieces
  have he1' : |A1' - c * b ^ 2 * (L' - 1 / 2)| ≤ 13 / 2 * a * (1 + L) ^ 3 := by
    refine hA1'.trans ?_
    calc 13 * b * (1 + L') ^ 3 ≤ 13 * (a / 2) * (1 + L) ^ 3 := by
          apply mul_le_mul (by linarith) hP3 (by positivity) (by positivity)
      _ = 13 / 2 * a * (1 + L) ^ 3 := by ring
  have he0' : |A0' - c * b ^ 2| ≤ 5 / 2 * a * (1 + L) ^ 2 := by
    refine hA0'.trans ?_
    calc 5 * b * (1 + L') ^ 2 ≤ 5 * (a / 2) * (1 + L) ^ 2 := by
          apply mul_le_mul (by linarith) hP2 (by positivity) (by positivity)
      _ = 5 / 2 * a * (1 + L) ^ 2 := by ring
  have hm : |L - 1 / 2 + ℓ / 3| ≤ 1 + L := by
    rw [abs_le]; constructor <;> linarith
  have hprod : |((A0 - c * a ^ 2) - (A0' - c * b ^ 2)) * (L - 1 / 2 + ℓ / 3)|
      ≤ 15 / 2 * a * (1 + L) ^ 3 := by
    rw [abs_mul]
    have h1 : |(A0 - c * a ^ 2) - (A0' - c * b ^ 2)| ≤ 15 / 2 * a * (1 + L) ^ 2 := by
      refine (abs_sub _ _).trans ?_; linarith
    calc |(A0 - c * a ^ 2) - (A0' - c * b ^ 2)| * |L - 1 / 2 + ℓ / 3|
        ≤ (15 / 2 * a * (1 + L) ^ 2) * (1 + L) :=
          mul_le_mul h1 hm (abs_nonneg _) (by positivity)
      _ = 15 / 2 * a * (1 + L) ^ 3 := by ring
  -- the parity mismatch `M = cℓ/3·(4b² − a²) + c b² δ`, `|M| ≤ a`
  have hM : |c * ℓ / 3 * (4 * b ^ 2 - a ^ 2) + c * b ^ 2 * (L - L' - ℓ)| ≤ a * (1 + L) ^ 3 := by
    have e4 : 4 * b ^ 2 - a ^ 2 = (2 * b - a) * (2 * b + a) := by ring
    have h4 : -(2 * a) ≤ 4 * b ^ 2 - a ^ 2 := by
      rw [e4]
      have := mul_le_mul_of_nonneg_right (show (-1 : ℝ) ≤ 2 * b - a by linarith)
        (show (0 : ℝ) ≤ 2 * b + a by linarith)
      linarith
    have h4' : 4 * b ^ 2 - a ^ 2 ≤ 0 := by
      rw [e4]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have hbδ : b * (L - L' - ℓ) ≤ 1 / 2 := by linarith
    have hb2δ : b ^ 2 * (L - L' - ℓ) ≤ a / 4 := by
      have e : b ^ 2 * (L - L' - ℓ) = b * (b * (L - L' - ℓ)) := by ring
      rw [e]
      calc b * (b * (L - L' - ℓ)) ≤ b * (1 / 2) := mul_le_mul_of_nonneg_left hbδ (by linarith)
        _ ≤ a / 4 := by linarith
    have hb2δ0 : 0 ≤ b ^ 2 * (L - L' - ℓ) := mul_nonneg (sq_nonneg b) hδ0
    have hcl : 0 ≤ c * ℓ / 3 := by positivity
    have hcℓ1 : c * ℓ ≤ 1 := by
      calc c * ℓ ≤ 0.19 * ℓ := mul_le_mul_of_nonneg_right hc19 (by linarith)
        _ ≤ 1 := by linarith
    have hM1 : -(2 * a) * (c * ℓ / 3) ≤ c * ℓ / 3 * (4 * b ^ 2 - a ^ 2) := by
      have := mul_le_mul_of_nonneg_left h4 hcl
      linarith
    have hM1' : c * ℓ / 3 * (4 * b ^ 2 - a ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcl h4'
    have hM2 : c * b ^ 2 * (L - L' - ℓ) ≤ c * (a / 4) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb2δ hc0.le
    have hM20 : 0 ≤ c * b ^ 2 * (L - L' - ℓ) := by rw [mul_assoc]; exact mul_nonneg hc0.le hb2δ0
    have haP : a ≤ a * (1 + L) ^ 3 := le_mul_of_one_le_right ha0 hP31
    have hacl : a * (c * ℓ) ≤ a * 1 := mul_le_mul_of_nonneg_left hcℓ1 ha0
    have hca : c * a ≤ 0.19 * a := mul_le_mul_of_nonneg_right hc19 ha0
    have hlow : -a ≤ c * ℓ / 3 * (4 * b ^ 2 - a ^ 2) + c * b ^ 2 * (L - L' - ℓ) := by
      linarith
    have hup : c * ℓ / 3 * (4 * b ^ 2 - a ^ 2) + c * b ^ 2 * (L - L' - ℓ) ≤ a := by
      linarith
    rw [abs_le]; constructor <;> linarith
  -- the identity
  have hE : A1 - A1' - (A0 - A0') * (L - (1 / 2 - ℓ / 3))
      = (A1 - c * a ^ 2 * (L - 1 / 2)) - (A1' - c * b ^ 2 * (L' - 1 / 2))
        - ((A0 - c * a ^ 2) - (A0' - c * b ^ 2)) * (L - 1 / 2 + ℓ / 3)
        + (c * ℓ / 3 * (4 * b ^ 2 - a ^ 2) + c * b ^ 2 * (L - L' - ℓ)) := by ring
  rw [hE]
  set X := A1 - c * a ^ 2 * (L - 1 / 2) with hXdef
  set Y := A1' - c * b ^ 2 * (L' - 1 / 2) with hYdef
  set Z := ((A0 - c * a ^ 2) - (A0' - c * b ^ 2)) * (L - 1 / 2 + ℓ / 3) with hZdef
  set M := c * ℓ / 3 * (4 * b ^ 2 - a ^ 2) + c * b ^ 2 * (L - L' - ℓ) with hMdef
  clear_value X Y Z M
  have s1 := abs_add_le (X - Y - Z) M
  have s2 := abs_sub (X - Y) Z
  have s3 := abs_sub X Y
  linarith

set_option maxHeartbeats 400000 in
/-- **The SECOND log-moment of the dyadic family, EXPLICIT.**
`|Σ_{Q/2<q≤Q} φ*(q) (log q)² − |𝔉_dyad|·h(Q)| ≤ 54·Q·(1 + log Q)⁴`, with
`h(Q) = (log Q + log2/3)² − (log Q + log2/3) + 1/2 − (4/9)log²2`
(`= ⟨log q⟩² + Var`, `⟨log q⟩ = log Q + log2/3 − 1/2`, `Var = 1/4 − (4/9) log²2 = 0.0365`). -/
theorem famLogSqCond_dyadic_bound (N : ℕ) (hN : 2 ≤ N) :
    |(∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q ^ 2)
        - Family.sizeR Family.dyadic N
          * ((Real.log N + Real.log 2 / 3) ^ 2 - (Real.log N + Real.log 2 / 3) + 1 / 2
              - 4 / 9 * Real.log 2 ^ 2)|
      ≤ 54 * (N : ℝ) * (1 + Real.log N) ^ 4 := by
  have hmod : Family.dyadic.moduli N = Finset.Ioc (N / 2) N := rfl
  rw [hmod, dyadic_logsq_diff, sizeR_dyadic_eq]
  obtain ⟨hb1, h2b, hb2, hδ0, hδ⟩ := half_facts N hN
  have hN1 : 1 ≤ N := by omega
  have hn1 : 1 ≤ N / 2 := by omega
  have hA2 := N2.Alog2_bound N hN1
  have hA2' := N2.Alog2_bound (N / 2) hn1
  have hA0 := N2.Astar_bound N hN1
  have hA0' := N2.Astar_bound (N / 2) hn1
  have hc19 := c18_le
  set a : ℝ := (N : ℝ) with hadef
  set b : ℝ := ((N / 2 : ℕ) : ℝ) with hbdef
  set L : ℝ := Real.log a with hLdef
  set L' : ℝ := Real.log b with hL'def
  set ℓ : ℝ := Real.log 2 with hℓdef
  set c : ℝ := 18 / Real.pi ^ 4 with hcdef
  set A2 := N2.Alog2 N with hA2def
  set A2' := N2.Alog2 (N / 2) with hA2'def
  set A0 := N2.Astar N with hA0def
  set A0' := N2.Astar (N / 2) with hA0'def
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hℓ1 : 0.6931471803 < ℓ := Real.log_two_gt_d9
  have hℓ2 : ℓ < 0.6931471808 := Real.log_two_lt_d9
  have ha2 : (2 : ℝ) ≤ a := by rw [hadef]; exact_mod_cast hN
  have ha0 : 0 ≤ a := by linarith
  have hL'0 : 0 ≤ L' := Real.log_nonneg hb1
  have hL'L : L' ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hℓL : ℓ ≤ L := Real.log_le_log (by norm_num) ha2
  have hL0 : 0 ≤ L := by linarith
  have hba : b ≤ a / 2 := by linarith
  have hδ1 : L - L' - ℓ ≤ 1 / 2 := by
    have : (L - L' - ℓ) * 2 ≤ (L - L' - ℓ) * (2 * b) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0
    linarith
  have hP4 : (1 + L') ^ 4 ≤ (1 + L) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hP2 : (1 + L') ^ 2 ≤ (1 + L) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hP1le4 : (1 + L) ≤ (1 + L) ^ 4 := by
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + L) (by norm_num : 1 ≤ 4)
    simpa using this
  have hℓsq : ℓ ^ 2 ≤ 0.49 := by
    have := mul_le_mul hℓ2.le hℓ2.le (by linarith) (by norm_num)
    rw [sq]; linarith
  have hℓsq0 : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have hLℓ : L * ℓ ≤ L * 0.7 := mul_le_mul_of_nonneg_left (by linarith) hL0
  have hLℓ0 : 0 ≤ L * ℓ := mul_nonneg hL0 (by linarith)
  -- the error pieces
  have he2' : |A2' - c * b ^ 2 * (L' ^ 2 - L' + 1 / 2)| ≤ 15 * a * (1 + L) ^ 4 := by
    refine hA2'.trans ?_
    calc 30 * b * (1 + L') ^ 4 ≤ 30 * (a / 2) * (1 + L) ^ 4 := by
          apply mul_le_mul (by linarith) hP4 (by positivity) (by positivity)
      _ = 15 * a * (1 + L) ^ 4 := by ring
  have he0' : |A0' - c * b ^ 2| ≤ 5 / 2 * a * (1 + L) ^ 2 := by
    refine hA0'.trans ?_
    calc 5 * b * (1 + L') ^ 2 ≤ 5 * (a / 2) * (1 + L) ^ 2 := by
          apply mul_le_mul (by linarith) hP2 (by positivity) (by positivity)
      _ = 5 / 2 * a * (1 + L) ^ 2 := by ring
  have hh : |(L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2| ≤ (1 + L) ^ 2 := by
    have hL2 := sq_nonneg L
    rw [abs_le]; constructor <;> linarith
  have hprod : |((A0 - c * a ^ 2) - (A0' - c * b ^ 2))
        * ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2)|
      ≤ 15 / 2 * a * (1 + L) ^ 4 := by
    rw [abs_mul]
    have h1 : |(A0 - c * a ^ 2) - (A0' - c * b ^ 2)| ≤ 15 / 2 * a * (1 + L) ^ 2 := by
      refine (abs_sub _ _).trans ?_; linarith
    calc |(A0 - c * a ^ 2) - (A0' - c * b ^ 2)|
          * |(L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2|
        ≤ (15 / 2 * a * (1 + L) ^ 2) * (1 + L) ^ 2 :=
          mul_le_mul h1 hh (abs_nonneg _) (by positivity)
      _ = 15 / 2 * a * (1 + L) ^ 4 := by ring
  -- the parity mismatch
  have hM : |c * (ℓ / 3 * (1 + ℓ - 2 * L)) * (a ^ 2 - 4 * b ^ 2)
        + c * b ^ 2 * (L - L' - ℓ) * (2 * (L - ℓ) - (L - L' - ℓ) - 1)| ≤ a * (1 + L) ^ 4 := by
    have eq4 : a ^ 2 - 4 * b ^ 2 = (a - 2 * b) * (a + 2 * b) := by ring
    have hq0 : 0 ≤ a ^ 2 - 4 * b ^ 2 := by
      rw [eq4]; exact mul_nonneg (by linarith) (by linarith)
    have hq1 : a ^ 2 - 4 * b ^ 2 ≤ 2 * a := by
      rw [eq4]
      have := mul_le_mul_of_nonneg_right (show a - 2 * b ≤ 1 by linarith)
        (show (0 : ℝ) ≤ a + 2 * b by linarith)
      linarith
    have hg : |ℓ / 3 * (1 + ℓ - 2 * L)| ≤ 2 * ℓ / 3 * (1 + L) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < ℓ / 3)]
      have : |1 + ℓ - 2 * L| ≤ 2 * (1 + L) := by rw [abs_le]; constructor <;> linarith
      calc ℓ / 3 * |1 + ℓ - 2 * L| ≤ ℓ / 3 * (2 * (1 + L)) :=
            mul_le_mul_of_nonneg_left this (by linarith)
        _ = 2 * ℓ / 3 * (1 + L) := by ring
    have hf1 : |c * (ℓ / 3 * (1 + ℓ - 2 * L)) * (a ^ 2 - 4 * b ^ 2)|
        ≤ c * (2 * ℓ / 3 * (1 + L)) * (2 * a) := by
      rw [abs_mul, abs_mul, abs_of_pos hc0, abs_of_nonneg hq0]
      gcongr
    have hbδ : b * (L - L' - ℓ) ≤ 1 / 2 := by linarith
    have hb2δ : b ^ 2 * (L - L' - ℓ) ≤ a / 4 := by
      have e : b ^ 2 * (L - L' - ℓ) = b * (b * (L - L' - ℓ)) := by ring
      rw [e]
      calc b * (b * (L - L' - ℓ)) ≤ b * (1 / 2) := mul_le_mul_of_nonneg_left hbδ (by linarith)
        _ ≤ a / 4 := by linarith
    have hb2δ0 : 0 ≤ b ^ 2 * (L - L' - ℓ) := mul_nonneg (sq_nonneg b) hδ0
    have hcb : 0 ≤ c * b ^ 2 * (L - L' - ℓ) := by rw [mul_assoc]; exact mul_nonneg hc0.le hb2δ0
    have hcb' : c * b ^ 2 * (L - L' - ℓ) ≤ c * (a / 4) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb2δ hc0.le
    have hw : |2 * (L - ℓ) - (L - L' - ℓ) - 1| ≤ 2 * (1 + L) := by
      rw [abs_le]; constructor <;> linarith
    have hf2 : |c * b ^ 2 * (L - L' - ℓ) * (2 * (L - ℓ) - (L - L' - ℓ) - 1)|
        ≤ c * (a / 4) * (2 * (1 + L)) := by
      rw [abs_mul, abs_of_nonneg hcb]
      exact mul_le_mul hcb' hw (abs_nonneg _) (by positivity)
    have hcℓ : c * ℓ ≤ 0.14 := by
      calc c * ℓ ≤ 0.19 * ℓ := mul_le_mul_of_nonneg_right hc19 (by linarith)
        _ ≤ 0.14 := by linarith
    have hca : c * a ≤ 0.19 * a := mul_le_mul_of_nonneg_right hc19 ha0
    have hacl : a * (c * ℓ) ≤ a * 0.14 := mul_le_mul_of_nonneg_left hcℓ ha0
    have haL : a * (1 + L) ≤ a * (1 + L) ^ 4 := mul_le_mul_of_nonneg_left hP1le4 ha0
    have hcaL : c * a * (1 + L) ≤ 0.19 * a * (1 + L) :=
      mul_le_mul_of_nonneg_right hca (by linarith)
    have haclL : a * (c * ℓ) * (1 + L) ≤ a * 0.14 * (1 + L) :=
      mul_le_mul_of_nonneg_right hacl (by linarith)
    have haL0 : 0 ≤ a * (1 + L) := mul_nonneg ha0 (by linarith)
    calc |c * (ℓ / 3 * (1 + ℓ - 2 * L)) * (a ^ 2 - 4 * b ^ 2)
          + c * b ^ 2 * (L - L' - ℓ) * (2 * (L - ℓ) - (L - L' - ℓ) - 1)|
        ≤ |c * (ℓ / 3 * (1 + ℓ - 2 * L)) * (a ^ 2 - 4 * b ^ 2)|
          + |c * b ^ 2 * (L - L' - ℓ) * (2 * (L - ℓ) - (L - L' - ℓ) - 1)| := abs_add_le _ _
      _ ≤ c * (2 * ℓ / 3 * (1 + L)) * (2 * a) + c * (a / 4) * (2 * (1 + L)) :=
          add_le_add hf1 hf2
      _ ≤ a * (1 + L) := by linarith
      _ ≤ a * (1 + L) ^ 4 := haL
  -- the identity
  have hE : A2 - A2' - (A0 - A0') * ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2)
      = (A2 - c * a ^ 2 * (L ^ 2 - L + 1 / 2)) - (A2' - c * b ^ 2 * (L' ^ 2 - L' + 1 / 2))
        - ((A0 - c * a ^ 2) - (A0' - c * b ^ 2))
            * ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2)
        + (c * (ℓ / 3 * (1 + ℓ - 2 * L)) * (a ^ 2 - 4 * b ^ 2)
            + c * b ^ 2 * (L - L' - ℓ) * (2 * (L - ℓ) - (L - L' - ℓ) - 1)) := by ring
  rw [hE]
  set X := A2 - c * a ^ 2 * (L ^ 2 - L + 1 / 2) with hXdef
  set Y := A2' - c * b ^ 2 * (L' ^ 2 - L' + 1 / 2) with hYdef
  set Z := ((A0 - c * a ^ 2) - (A0' - c * b ^ 2))
      * ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2) with hZdef
  set M := c * (ℓ / 3 * (1 + ℓ - 2 * L)) * (a ^ 2 - 4 * b ^ 2)
      + c * b ^ 2 * (L - L' - ℓ) * (2 * (L - ℓ) - (L - L' - ℓ) - 1) with hMdef
  clear_value X Y Z M
  have s1 := abs_add_le (X - Y - Z) M
  have s2 := abs_sub (X - Y) Z
  have s3 := abs_sub X Y
  have s4 : 0 ≤ a * (1 + L) ^ 4 := mul_nonneg ha0 (by positivity)
  linarith

/-- The dyadic family size, TWO-SIDED: `||𝔉_dyad| − (3/4)(18/π⁴)Q²| ≤ 8Q(1 + log Q)²`. -/
theorem sizeR_dyadic_bound (N : ℕ) (hN : 2 ≤ N) :
    |Family.sizeR Family.dyadic N - 3 / 4 * (18 / Real.pi ^ 4) * (N : ℝ) ^ 2|
      ≤ 8 * (N : ℝ) * (1 + Real.log N) ^ 2 := by
  rw [sizeR_dyadic_eq]
  obtain ⟨hb1, h2b, hb2, -, -⟩ := half_facts N hN
  have hN1 : 1 ≤ N := by omega
  have hn1 : 1 ≤ N / 2 := by omega
  have hA0 := N2.Astar_bound N hN1
  have hA0' := N2.Astar_bound (N / 2) hn1
  have hc19 := c18_le
  set a : ℝ := (N : ℝ) with hadef
  set b : ℝ := ((N / 2 : ℕ) : ℝ) with hbdef
  set L : ℝ := Real.log a with hLdef
  set L' : ℝ := Real.log b with hL'def
  set c : ℝ := 18 / Real.pi ^ 4 with hcdef
  set A0 := N2.Astar N with hA0def
  set A0' := N2.Astar (N / 2) with hA0'def
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have ha2 : (2 : ℝ) ≤ a := by rw [hadef]; exact_mod_cast hN
  have ha0 : 0 ≤ a := by linarith
  have hL'0 : 0 ≤ L' := Real.log_nonneg hb1
  have hL'L : L' ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hL0 : 0 ≤ L := by linarith
  have hP2 : (1 + L') ^ 2 ≤ (1 + L) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hP21 : 1 ≤ (1 + L) ^ 2 := one_le_pow₀ (by linarith)
  have he0' : |A0' - c * b ^ 2| ≤ 5 / 2 * a * (1 + L) ^ 2 := by
    refine hA0'.trans ?_
    calc 5 * b * (1 + L') ^ 2 ≤ 5 * (a / 2) * (1 + L) ^ 2 := by
          apply mul_le_mul (by linarith) hP2 (by positivity) (by positivity)
      _ = 5 / 2 * a * (1 + L) ^ 2 := by ring
  have eq4 : a ^ 2 - 4 * b ^ 2 = (a - 2 * b) * (a + 2 * b) := by ring
  have hq0 : 0 ≤ a ^ 2 - 4 * b ^ 2 := by
    rw [eq4]; exact mul_nonneg (by linarith) (by linarith)
  have hq1 : a ^ 2 - 4 * b ^ 2 ≤ 2 * a := by
    rw [eq4]
    have := mul_le_mul_of_nonneg_right (show a - 2 * b ≤ 1 by linarith)
      (show (0 : ℝ) ≤ a + 2 * b by linarith)
    linarith
  have hca : c * a ≤ 0.19 * a := mul_le_mul_of_nonneg_right hc19 ha0
  have haP : a ≤ a * (1 + L) ^ 2 := le_mul_of_one_le_right ha0 hP21
  have hM : |c / 4 * (a ^ 2 - 4 * b ^ 2)| ≤ 1 / 2 * a * (1 + L) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have : c / 4 * (a ^ 2 - 4 * b ^ 2) ≤ c / 4 * (2 * a) :=
      mul_le_mul_of_nonneg_left hq1 (by positivity)
    linarith
  have hE : A0 - A0' - 3 / 4 * c * a ^ 2
      = (A0 - c * a ^ 2) - (A0' - c * b ^ 2) + c / 4 * (a ^ 2 - 4 * b ^ 2) := by ring
  rw [hE]
  set X := A0 - c * a ^ 2 with hXdef
  set Y := A0' - c * b ^ 2 with hYdef
  set M := c / 4 * (a ^ 2 - 4 * b ^ 2) with hMdef
  clear_value X Y M
  have s1 := abs_add_le (X - Y) M
  have s2 := abs_sub X Y
  linarith

/-! ## (c) `FamRvMLower Family.dyadic` along the design of record -/

section FamilyBridgeDyadic

/-- **`FamRvMLower` for `Family.dyadic`, with BOTH residues kept explicit** — the §12.2 conductor
residue `(T/2π)·(28Q(1+log Q)³ + 10⁻⁶|𝔉|)` (the `10⁻⁶|𝔉|` is the rounding of the frozen
`conductorShift = 0.26895` against the exact `1/2 − log2/3`) and the q-uniform RvM error
`A·|𝔉|·log(Q(T+2))`. Mirrors `famRvM_lower_with_residue` (`qle`). -/
theorem famRvM_lower_with_residue_dyadic (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hQ : P.Q = (Qn : ℝ)) {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    Family.sizeR Family.dyadic Qn * (P.T / (2 * Real.pi) * famAvgL Family.dyadic P)
        - P.T / (2 * Real.pi) * (28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
            + 1 / 1000000 * Family.sizeR Family.dyadic Qn)
        - A * (Family.sizeR Family.dyadic Qn * Real.log ((Qn : ℝ) * (P.T + 2)))
      ≤ NfamQ P Family.dyadic Qn := by
  have hbase := famRvM_lower_raw P Family.isFull_dyadic Qn hQn hrvm hT
  have hQnR : (2 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hM : (0 : ℝ) ≤ P.T / (2 * Real.pi) := by positivity
  have hdiv : (0 : ℝ) < P.T / (2 * Real.pi) := div_pos hT0 (by linarith)
  have hS0 : 0 ≤ Family.sizeR Family.dyadic Qn := by unfold Family.sizeR; positivity
  set G : ℝ := Real.log (P.T / (2 * Real.pi)) + 2 * Real.log 2 - 1 with hG
  have hLLsplit : P.LL = Real.log (Qn : ℝ) + Real.log (P.T / (2 * Real.pi)) := by
    unfold ParamsQ.LL
    rw [hQ, show (Qn : ℝ) * P.T / (2 * Real.pi) = (Qn : ℝ) * (P.T / (2 * Real.pi)) by ring]
    exact Real.log_mul (ne_of_gt hQ0) (ne_of_gt hdiv)
  have hell : ∀ q ∈ Family.dyadic.moduli Qn,
      Zeta23.ThmE.ell1q q P.T = Real.log (q : ℝ) + G := by
    intro q hq
    have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    unfold Zeta23.ThmE.ell1q
    rw [show (q : ℝ) * P.T / (2 * Real.pi) = (q : ℝ) * (P.T / (2 * Real.pi)) by ring,
      Real.log_mul (ne_of_gt hqR) (ne_of_gt hdiv), hG]
    ring
  have hsum1 : ∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T
      = (∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Real.log q)
        + Family.sizeR Family.dyadic Qn * G := by
    rw [sizeR_eq_sum_phiStar Family.isFull_dyadic, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [hell q hq]; ring
  have hsum2 : ∑ q ∈ Family.dyadic.moduli Qn,
        (phiStar q : ℝ) * Real.log ((q : ℝ) * (P.T + 2))
      ≤ Family.sizeR Family.dyadic Qn * Real.log ((Qn : ℝ) * (P.T + 2)) := by
    rw [sizeR_eq_sum_phiStar Family.isFull_dyadic, Finset.sum_mul]
    refine Finset.sum_le_sum (fun q hq => ?_)
    have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
    have hqle : (q : ℝ) ≤ (Qn : ℝ) := by
      have h : q ∈ Finset.Ioc (Qn / 2) Qn := hq
      rw [Finset.mem_Ioc] at h
      exact_mod_cast h.2
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    have hmono : Real.log ((q : ℝ) * (P.T + 2)) ≤ Real.log ((Qn : ℝ) * (P.T + 2)) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hsplitL : ∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
          - A * Real.log ((q : ℝ) * (P.T + 2)))
      = P.T / (2 * Real.pi)
          * (∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T)
        - A * (∑ q ∈ Family.dyadic.moduli Qn,
            (phiStar q : ℝ) * Real.log ((q : ℝ) * (P.T + 2))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  -- the dyadic conductor step, at the FROZEN shift (rounding ≤ 10⁻⁶ absorbed)
  have hshift := conductorShift_dyadic_err
  have hS : Family.sizeR Family.dyadic Qn * (Real.log (Qn : ℝ) - Family.dyadic.conductorShift)
        - (28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
            + 1 / 1000000 * Family.sizeR Family.dyadic Qn)
      ≤ ∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Real.log q := by
    have h := (abs_le.mp (famLogCond_dyadic_bound Qn hQn)).1
    have hsz : Family.sizeR Family.dyadic Qn
          * ((1 / 2 - Real.log 2 / 3) - Family.dyadic.conductorShift)
        ≤ Family.sizeR Family.dyadic Qn * (1 / 1000000) :=
      mul_le_mul_of_nonneg_left hshift.2 hS0
    linarith
  have hfa : famAvgL Family.dyadic P
      = (Real.log (Qn : ℝ) - Family.dyadic.conductorShift) + G := by
    unfold famAvgL
    rw [hLLsplit, hG]
    ring
  have step1 : P.T / (2 * Real.pi)
        * ((Family.sizeR Family.dyadic Qn * (Real.log (Qn : ℝ) - Family.dyadic.conductorShift)
              - (28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
                  + 1 / 1000000 * Family.sizeR Family.dyadic Qn))
            + Family.sizeR Family.dyadic Qn * G)
      ≤ P.T / (2 * Real.pi)
        * (∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Zeta23.ThmE.ell1q q P.T) := by
    rw [hsum1]
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  have step2 : A * (∑ q ∈ Family.dyadic.moduli Qn,
        (phiStar q : ℝ) * Real.log ((q : ℝ) * (P.T + 2)))
      ≤ A * (Family.sizeR Family.dyadic Qn * Real.log ((Qn : ℝ) * (P.T + 2))) :=
    mul_le_mul_of_nonneg_left hsum2 hA
  have heq : Family.sizeR Family.dyadic Qn * (P.T / (2 * Real.pi) * famAvgL Family.dyadic P)
        - P.T / (2 * Real.pi) * (28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
            + 1 / 1000000 * Family.sizeR Family.dyadic Qn)
      = P.T / (2 * Real.pi)
        * ((Family.sizeR Family.dyadic Qn * (Real.log (Qn : ℝ) - Family.dyadic.conductorShift)
              - (28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
                  + 1 / 1000000 * Family.sizeR Family.dyadic Qn))
            + Family.sizeR Family.dyadic Qn * G) := by
    rw [hfa]; ring
  refine le_trans ?_ hbase
  rw [hsplitL, heq]
  linarith

theorem one_add_log_cube_div_tendsto'' :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ 3 / x) atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ 0 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 0)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 1 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 1)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have h3 : Tendsto (fun x : ℝ => Real.log x ^ 3 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero
  have hcomb : Tendsto (fun x : ℝ =>
      Real.log x ^ 0 / x + 3 * (Real.log x ^ 1 / x) + 3 * (Real.log x ^ 2 / x)
        + Real.log x ^ 3 / x) atTop (nhds 0) := by
    simpa using ((h0.add (h1.const_mul 3)).add (h2.const_mul 3)).add h3
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [pow_zero, pow_one]
  field_simp
  ring

/-- **The dyadic §12.2 residue is eventually below any fixed multiple of `|𝔉_dyad|`.** -/
theorem residue_small_eventually_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      28 * (N : ℝ) * (1 + Real.log N) ^ 3 ≤ ε * Family.sizeR Family.dyadic N := by
  have hc : (0 : ℝ) < ε * (3 / 4 * (18 / Real.pi ^ 4)) := by
    have : (0 : ℝ) < 18 / Real.pi ^ 4 := by positivity
    positivity
  have hH : Tendsto (fun x : ℝ =>
      28 * ((1 + Real.log x) ^ 3 / x) + 8 * ε * ((1 + Real.log x) ^ 2 / x))
      atTop (nhds 0) := by
    simpa using (one_add_log_cube_div_tendsto''.const_mul 28).add
      (one_add_log_sq_div_tendsto'.const_mul (8 * ε))
  have hev : ∀ᶠ x : ℝ in atTop,
      28 * ((1 + Real.log x) ^ 3 / x) + 8 * ε * ((1 + Real.log x) ^ 2 / x)
        < ε * (3 / 4 * (18 / Real.pi ^ 4)) := hH.eventually_lt_const hc
  have hevN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  filter_upwards [hevN, eventually_ge_atTop 2] with N hN1 hN2
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hN1.le (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
  have hexpand : (28 * ((1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ))
        + 8 * ε * ((1 + Real.log (N : ℝ)) ^ 2 / (N : ℝ))) * (N : ℝ) ^ 2
      = 28 * (N : ℝ) * (1 + Real.log N) ^ 3
        + 8 * ε * (N : ℝ) * (1 + Real.log N) ^ 2 := by
    field_simp
  rw [hexpand] at hmul
  have hsz2 := mul_le_mul_of_nonneg_left (sizeR_dyadic_lower N hN2) hε.le
  linarith

/-- **`FamRvMLower Family.dyadic` HOLDS ALONG THE DESIGN OF RECORD.**
Mirrors `famRvMLower_of_design` (`qle`); the only change is the conductor-average input
(`famLogCond_dyadic_bound`, at the exact shift `1/2 − log2/3`, with the `≤ 10⁻⁶` rounding of the
frozen `0.26895` absorbed into the slack): the residues are split as `1/400 + 10⁻⁶ < 1/200`
(conductor side) and `1/200` (RvM side), against `rvmSlack = 1/100`. -/
theorem famRvMLower_dyadic_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord Family.dyadic r ε (n : ℝ) P → FamRvMLower Family.dyadic n P := by
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop := by
    have hre : (0 : ℝ) < r + ε := by linarith
    exact (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  filter_upwards [residue_small_eventually_dyadic (ε := 1 / 400) (by norm_num),
    rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀,
    eventually_ge_atTop 2] with n hres herr hT0 hn2
  intro P hdes
  obtain ⟨hP, hQ, hT, -⟩ := hdes
  have hTpos : (0 : ℝ) < P.T := T_posQ hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey := famRvM_lower_with_residue_dyadic P hP n hn2 hQ hA.le hrvm
    (by rw [hT]; exact hT0)
  have hM0 : (0 : ℝ) < P.T / (2 * Real.pi) := by positivity
  have hS0 : (0 : ℝ) ≤ Family.sizeR Family.dyadic n := by
    unfold Family.sizeR; positivity
  -- (i) the §12.2 residue plus the shift rounding, at half the slack
  have h1 : P.T / (2 * Real.pi) * (28 * (n : ℝ) * (1 + Real.log n) ^ 3
        + 1 / 1000000 * Family.sizeR Family.dyadic n)
      ≤ Family.sizeR Family.dyadic n * (P.T / (2 * Real.pi)) / 200 := by
    have h := mul_le_mul_of_nonneg_left hres hM0.le
    have h' := mul_nonneg hM0.le hS0
    nlinarith [h, h']
  -- (ii) RvM's own error, at the other half
  have hlogpos : (0 : ℝ) ≤ Real.log ((n : ℝ) * (P.T + 2)) := by
    apply Real.log_nonneg
    have hn : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    nlinarith
  have h2 : A * (Family.sizeR Family.dyadic n * Real.log ((n : ℝ) * (P.T + 2)))
      ≤ Family.sizeR Family.dyadic n * (P.T / (2 * Real.pi)) / 200 := by
    have herr' : 400 * Real.pi * A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T := by
      rw [hT]; exact herr
    have hstep : A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T / (2 * Real.pi) / 200 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith [herr']
    nlinarith [mul_le_mul_of_nonneg_left hstep hS0]
  -- assemble
  unfold FamRvMLower famAvgLlow rvmSlack
  have hexp : Family.sizeR Family.dyadic n
        * (P.T / (2 * Real.pi) * (famAvgL Family.dyadic P - 1 / 100))
      = Family.sizeR Family.dyadic n * (P.T / (2 * Real.pi) * famAvgL Family.dyadic P)
        - Family.sizeR Family.dyadic n * (P.T / (2 * Real.pi)) / 200
        - Family.sizeR Family.dyadic n * (P.T / (2 * Real.pi)) / 200 := by ring
  rw [hexp]
  linarith [hkey, h1, h2]

end FamilyBridgeDyadic

/-! ## (d) Row 8's `famEll1Sq` for the dyadic family -/

namespace FamRows

open Zeta23.ThmE

/-- `famEll1Sq dyadic = (Alog2 Q − Alog2 ⌊Q/2⌋) + 2e(Alog Q − Alog ⌊Q/2⌋) + e²(Astar Q − Astar ⌊Q/2⌋)`,
`e = ℓ₁(T) = l(T) + 2log2 − 1` — the dyadic twin of `famEll1Sq_qle_eq`, by differencing. -/
theorem famEll1Sq_dyadic_eq (P : ParamsQ) (hT : 0 < P.T) (Qn : ℕ) :
    famEll1Sq Family.dyadic P Qn
      = (N2.Alog2 Qn - N2.Alog2 (Qn / 2))
        + 2 * Zeta23.ell1 P.T * (N2.Alog Qn - N2.Alog (Qn / 2))
        + Zeta23.ell1 P.T ^ 2 * (N2.Astar Qn - N2.Astar (Qn / 2)) := by
  unfold famEll1Sq
  rw [← dyadic_logsq_diff, ← dyadic_log_diff, ← dyadic_count_diff]
  have hmod : Family.dyadic.moduli Qn = Finset.Ioc (Qn / 2) Qn := rfl
  rw [hmod]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := by
    have h := (Finset.mem_Ioc.mp hq).1; omega
  rw [Zeta23.ThmE.IntMuChi.ell1q_eq hq1 hT]
  ring

/-- **`⟨ℓ_{1,q}²⟩` over the DYADIC family, EXPLICIT (N2 differenced)**: with
`ℓ_d := ℓ_{1,Q}(T) + (log 2)/3`,
`|Σ_{Q/2<q≤Q} φ*(q)ℓ_{1,q}² − |𝔉_dyad|·(ℓ_d² − ℓ_d + 1/2 − (4/9)log²2)|
  ≤ 54Q(1+log Q)⁴ + 56ℓ₁(T)Q(1+log Q)³`.
Note `ℓ_d² − ℓ_d + 1/2 − (4/9)log²2 = (ℓ_d − 1/2)² + (1/4 − (4/9)log²2) = ⟨ℓ⟩² + Var`, with the
dyadic conductor average `⟨ℓ⟩ = ℓ_{1,Q} + log2/3 − 1/2` and variance `Var = 1/4 − (4/9)log²2
= 0.0365` (the `qle` variance is `1/4`). -/
theorem famEll1Sq_dyadic_eval (P : ParamsQ) (hT : 0 < P.T) (he : 0 ≤ Zeta23.ell1 P.T) (Qn : ℕ)
    (hQn : 2 ≤ Qn) :
    |famEll1Sq Family.dyadic P Qn
        - Family.sizeR Family.dyadic Qn
          * ((ell1q Qn P.T + Real.log 2 / 3) ^ 2 - (ell1q Qn P.T + Real.log 2 / 3) + 1 / 2
              - 4 / 9 * Real.log 2 ^ 2)|
      ≤ 54 * (Qn : ℝ) * (1 + Real.log Qn) ^ 4
        + 56 * Zeta23.ell1 P.T * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 := by
  have hQn1 : 1 ≤ Qn := by omega
  have h1 := famLogCond_dyadic_bound Qn hQn
  have h2 := famLogSqCond_dyadic_bound Qn hQn
  have hℓ : ell1q Qn P.T = Zeta23.ell1 P.T + Real.log Qn :=
    Zeta23.ThmE.IntMuChi.ell1q_eq hQn1 hT
  rw [hℓ, famEll1Sq_dyadic_eq P hT Qn]
  have hmod : Family.dyadic.moduli Qn = Finset.Ioc (Qn / 2) Qn := rfl
  rw [hmod, dyadic_log_diff] at h1
  rw [hmod, dyadic_logsq_diff] at h2
  rw [sizeR_dyadic_eq] at h1 h2 ⊢
  set e := Zeta23.ell1 P.T with hedef
  set D := N2.Astar Qn - N2.Astar (Qn / 2) with hDdef
  set S1 := N2.Alog Qn - N2.Alog (Qn / 2) with hS1def
  set S2 := N2.Alog2 Qn - N2.Alog2 (Qn / 2) with hS2def
  set L := Real.log (Qn : ℝ) with hLdef
  set ℓ := Real.log 2 with hℓdef
  have key : S2 + 2 * e * S1 + e ^ 2 * D
      - D * ((e + L + ℓ / 3) ^ 2 - (e + L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2)
      = (S2 - D * ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2))
        + 2 * e * (S1 - D * (L - (1 / 2 - ℓ / 3))) := by ring
  rw [key]
  calc |(S2 - D * ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2))
        + 2 * e * (S1 - D * (L - (1 / 2 - ℓ / 3)))|
      ≤ |S2 - D * ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2)|
        + |2 * e * (S1 - D * (L - (1 / 2 - ℓ / 3)))| := abs_add_le _ _
    _ ≤ 54 * (Qn : ℝ) * (1 + L) ^ 4 + 2 * e * (28 * (Qn : ℝ) * (1 + L) ^ 3) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * e)]
        gcongr
    _ = _ := by ring

/-- The main term of `famEll1Sq_dyadic_eval` in `(3/4)(18/π⁴)Q²` units (the twin of
`famEll1Sq_qle_eval`'s shape), paying `8Q(1+log Q)²·(1+ℓ_d)²` for `|𝔉_dyad| − (3/4)(18/π⁴)Q²`. -/
theorem famEll1Sq_dyadic_eval' (P : ParamsQ) (hT : 0 < P.T) (he : 0 ≤ Zeta23.ell1 P.T) (Qn : ℕ)
    (hQn : 2 ≤ Qn) :
    |famEll1Sq Family.dyadic P Qn
        - 3 / 4 * (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2
          * ((ell1q Qn P.T + Real.log 2 / 3) ^ 2 - (ell1q Qn P.T + Real.log 2 / 3) + 1 / 2
              - 4 / 9 * Real.log 2 ^ 2)|
      ≤ 54 * (Qn : ℝ) * (1 + Real.log Qn) ^ 4
        + 56 * Zeta23.ell1 P.T * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
        + 8 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 * (1 + (ell1q Qn P.T + Real.log 2 / 3)) ^ 2 := by
  have h := famEll1Sq_dyadic_eval P hT he Qn hQn
  have hs := sizeR_dyadic_bound Qn hQn
  have hQn1 : 1 ≤ Qn := by omega
  have hℓ : ell1q Qn P.T = Zeta23.ell1 P.T + Real.log Qn :=
    Zeta23.ThmE.IntMuChi.ell1q_eq hQn1 hT
  have hL0 : 0 ≤ Real.log (Qn : ℝ) := Real.log_natCast_nonneg Qn
  have hℓ2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hℓ2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  set x := ell1q Qn P.T + Real.log 2 / 3 with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef, hℓ]; linarith
  have hhx : |x ^ 2 - x + 1 / 2 - 4 / 9 * Real.log 2 ^ 2| ≤ (1 + x) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, sq_nonneg (Real.log 2)]
  set F := famEll1Sq Family.dyadic P Qn
  set D := Family.sizeR Family.dyadic Qn
  set hx := x ^ 2 - x + 1 / 2 - 4 / 9 * Real.log 2 ^ 2
  have e : F - 3 / 4 * (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2 * hx
      = (F - D * hx) + (D - 3 / 4 * (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2) * hx := by ring
  rw [e]
  calc |(F - D * hx) + (D - 3 / 4 * (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2) * hx|
      ≤ |F - D * hx| + |(D - 3 / 4 * (18 / Real.pi ^ 4) * (Qn : ℝ) ^ 2) * hx| := abs_add_le _ _
    _ ≤ (54 * (Qn : ℝ) * (1 + Real.log Qn) ^ 4
          + 56 * Zeta23.ell1 P.T * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
        + (8 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2) * (1 + x) ^ 2 := by
        rw [abs_mul]
        exact add_le_add h (mul_le_mul hs hhx (abs_nonneg _) (by positivity))
    _ = _ := by ring

end FamRows

/-! ## (e) The dyadic family averages `⟨log q⟩`, `⟨(log q)²⟩`, and the variance -/

/-- `Σ_{q∈𝔉_dyad} φ*(q) log q ≤ log N · |𝔉_dyad|` and `≥ 0`. -/
theorem sum_log_dyadic_bounds (N : ℕ) :
    0 ≤ ∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q ∧
    ∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q
      ≤ Real.log N * Family.sizeR Family.dyadic N := by
  constructor
  · exact Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg q)
  · rw [sizeR_eq_sum_phiStar Family.isFull_dyadic, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hqN : q ≤ N := (Finset.mem_Ioc.mp hq).2
    have hlog : Real.log (q : ℝ) ≤ Real.log (N : ℝ) := FamRows.log_natCast_mono' hqN
    nlinarith [Nat.cast_nonneg (α := ℝ) (phiStar q)]

/-- **The dyadic conductor averages with EXPLICIT constants**, given `c₀ N² ≤ |𝔉_dyad|`:
`|⟨log q⟩ − (log N + log2/3 − 1/2)| ≤ 28/c₀·(1+log N)³/N`,
`|⟨log²q⟩ − h(N)| ≤ 54/c₀·(1+log N)⁴/N`, and the VARIANCE
`|⟨log²q⟩ − ⟨log q⟩² − (1/4 − (4/9)log²2)| ≤ 110/c₀·(1+log N)⁴/N`
(`1/4 − (4/9) log²2 = 0.0365`; cf. `1/4` for `Family.qle`, `FamRows.avg_log_qle`). -/
theorem avg_log_dyadic (N : ℕ) (hN : 2 ≤ N) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hlow : c₀ * (N : ℝ) ^ 2 ≤ Family.sizeR Family.dyadic N) :
    |(∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q)
        / Family.sizeR Family.dyadic N - (Real.log N + Real.log 2 / 3 - 1 / 2)|
        ≤ 28 / c₀ * (1 + Real.log N) ^ 3 / N ∧
    |(∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q ^ 2)
        / Family.sizeR Family.dyadic N
        - ((Real.log N + Real.log 2 / 3) ^ 2 - (Real.log N + Real.log 2 / 3) + 1 / 2
            - 4 / 9 * Real.log 2 ^ 2)|
        ≤ 54 / c₀ * (1 + Real.log N) ^ 4 / N ∧
    |(∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q ^ 2)
        / Family.sizeR Family.dyadic N
        - ((∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q)
            / Family.sizeR Family.dyadic N) ^ 2
        - (1 / 4 - 4 / 9 * Real.log 2 ^ 2)|
        ≤ 110 / c₀ * (1 + Real.log N) ^ 4 / N := by
  have h1 := famLogCond_dyadic_bound N hN
  have h2 := famLogSqCond_dyadic_bound N hN
  obtain ⟨hS10, hS1L⟩ := sum_log_dyadic_bounds N
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hℓ1 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hℓ2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  set S1 := ∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q with hS1def
  set S2 := ∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q ^ 2 with hS2def
  set D := Family.sizeR Family.dyadic N with hDdef
  set L := Real.log (N : ℝ) with hLdef
  set ℓ := Real.log 2 with hℓdef
  set a : ℝ := (N : ℝ) with hadef
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hlow
  have hx2 : 0 < a ^ 2 := by positivity
  -- generic division step: `|S − D m| ≤ K a P` ⟹ `|S/D − m| ≤ K/c₀ · P / a`
  have hdiv : ∀ (S m K Pw : ℝ), 0 ≤ K → 0 ≤ Pw → |S - D * m| ≤ K * a * Pw →
      |S / D - m| ≤ K / c₀ * Pw / a := by
    intro S m K Pw hK hPw hb
    have e : S / D - m = (S - D * m) / D := by field_simp
    have hB : 0 ≤ K / c₀ * Pw / a := by positivity
    rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    calc |S - D * m| ≤ K * a * Pw := hb
      _ = K / c₀ * Pw / a * (c₀ * a ^ 2) := by field_simp
      _ ≤ K / c₀ * Pw / a * D := mul_le_mul_of_nonneg_left hlow hB
  have d1 : |S1 / D - (L + ℓ / 3 - 1 / 2)| ≤ 28 / c₀ * (1 + L) ^ 3 / a := by
    have := hdiv S1 (L - (1 / 2 - ℓ / 3)) 28 ((1 + L) ^ 3) (by norm_num) (by positivity) h1
    have e : L - (1 / 2 - ℓ / 3) = L + ℓ / 3 - 1 / 2 := by ring
    rw [e] at this; exact this
  have d2 : |S2 / D - ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2)|
      ≤ 54 / c₀ * (1 + L) ^ 4 / a :=
    hdiv S2 _ 54 ((1 + L) ^ 4) (by norm_num) (by positivity) h2
  refine ⟨d1, d2, ?_⟩
  -- variance
  have hq0 : 0 ≤ S1 / D := div_nonneg hS10 hDpos.le
  have hqL : S1 / D ≤ L := by rw [div_le_iff₀ hDpos]; linarith
  have hw : |S1 / D + (L + ℓ / 3 - 1 / 2)| ≤ 2 * (1 + L) := by
    rw [abs_le]; constructor <;> linarith
  have e : S2 / D - (S1 / D) ^ 2 - (1 / 4 - 4 / 9 * ℓ ^ 2)
      = (S2 / D - ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2))
        - (S1 / D - (L + ℓ / 3 - 1 / 2)) * (S1 / D + (L + ℓ / 3 - 1 / 2)) := by ring
  rw [e]
  have hB1 : 0 ≤ 28 / c₀ * (1 + L) ^ 3 / a := by positivity
  calc |(S2 / D - ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2))
        - (S1 / D - (L + ℓ / 3 - 1 / 2)) * (S1 / D + (L + ℓ / 3 - 1 / 2))|
      ≤ |S2 / D - ((L + ℓ / 3) ^ 2 - (L + ℓ / 3) + 1 / 2 - 4 / 9 * ℓ ^ 2)|
        + |S1 / D - (L + ℓ / 3 - 1 / 2)| * |S1 / D + (L + ℓ / 3 - 1 / 2)| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ 54 / c₀ * (1 + L) ^ 4 / a + (28 / c₀ * (1 + L) ^ 3 / a) * (2 * (1 + L)) := by
        have := mul_le_mul d1 hw (abs_nonneg _) hB1
        linarith
    _ = 110 / c₀ * (1 + L) ^ 4 / a := by field_simp; ring

/-- `avg_log_dyadic` with the explicit eventual floor `|𝔉_dyad| ≥ N²/10`
(`sizeR_dyadic_floor_eventually`): all three averages, eventually along `N`, with `c₀ = 1/10`. -/
theorem avg_log_dyadic_eventually :
    ∀ᶠ N : ℕ in atTop,
      |(∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q)
          / Family.sizeR Family.dyadic N - (Real.log N + Real.log 2 / 3 - 1 / 2)|
          ≤ 280 * (1 + Real.log N) ^ 3 / N ∧
      |(∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q ^ 2)
          / Family.sizeR Family.dyadic N
          - ((Real.log N + Real.log 2 / 3) ^ 2 - (Real.log N + Real.log 2 / 3) + 1 / 2
              - 4 / 9 * Real.log 2 ^ 2)|
          ≤ 540 * (1 + Real.log N) ^ 4 / N ∧
      |(∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q ^ 2)
          / Family.sizeR Family.dyadic N
          - ((∑ q ∈ Family.dyadic.moduli N, (phiStar q : ℝ) * Real.log q)
              / Family.sizeR Family.dyadic N) ^ 2
          - (1 / 4 - 4 / 9 * Real.log 2 ^ 2)|
          ≤ 1100 * (1 + Real.log N) ^ 4 / N := by
  filter_upwards [sizeR_dyadic_floor_eventually, eventually_ge_atTop 2] with N hfl hN2
  have hlow : (1 / 10 : ℝ) * (N : ℝ) ^ 2 ≤ Family.sizeR Family.dyadic N := by
    have : (N : ℝ) ^ 2 / 10 = 1 / 10 * (N : ℝ) ^ 2 := by ring
    rw [← this]; exact hfl
  obtain ⟨d1, d2, d3⟩ := avg_log_dyadic N hN2 (1 / 10) (by norm_num) hlow
  refine ⟨?_, ?_, ?_⟩
  · convert d1 using 2; ring
  · convert d2 using 2; ring
  · convert d3 using 2; ring

/-! ## The join: `corollary_two_dyadic_cert` with `hrvm` DISCHARGED by `famRvMLower_dyadic_of_design` -/

/-- `corollary_two_dyadic_cert` with the dyadic family RvM lower bound supplied by the tree
(`famRvMLower_dyadic_of_design`): only `hsharp` and `hfrob` remain named. -/
theorem corollary_two_dyadic_cert_rvm (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hre : r + ε ≤ 7)
    (hsharp : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord Family.dyadic r ε (Qn : ℝ) P → SharpZeroDensity Family.dyadic Qn P)
    (hfrob : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.dyadic Qn
        ≤ (Family.dyadic.kappaCert + rowR2 Family.dyadic P) * NfamQ P Family.dyadic Qn) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) :=
  JoinCert.corollary_two_dyadic_cert r ε hr hε hre hsharp hfrob
    (famRvMLower_dyadic_of_design r ε hr hε)

end ZetaQ

