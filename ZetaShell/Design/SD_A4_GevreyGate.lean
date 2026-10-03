/-
Node SD-A4 (L7_7, F1a): the Gevrey gate of the product window at S53-L75: `B′ = gevreyBprod A B ≤ 5·10⁴`.
Replaces `design_gevreyBprod_le` (`DesignProfile.lean:1417`, gate 40000). Paper §7.1 (Leibniz, any degree).
Numbers (`sanity_L7_7.py`, `gen_A4_lean.py`, exact): Lean's coefficient-sum majorants `M₀…M₁₂ = 7.20, 43.8, 289, 1740,
…, 4.51·10⁷`; with `B ≤ 6000`, `x₁ = w/(ℒA) ≤ 1/1300` (`ℒ ≥ 100`, `A ≥ 13`), `x₂ = λ/A ≤ 3/20`: `B′ ≤ 43 447`.
ROUND 2: PROVED, by the route of `DesignProfile.profM_evenDyad12_le` / `design_gevreyBprod_evenDyad12`, after
`S53L75.poly = p53X` (explicit `C c_k X^{2k}`, `c_k = d_k (200/191)^{2k}`, by `Polynomial.funext`).
No longer on F1's path (SD-A5 and SD-B7 use a `Q`-independent constant instead). Deps: SD-A3 (`S53_p_eq`).
-/
import ZetaShell.Design.SD_A3_Moments

namespace ZetaShell.Design

open ZetaQ Polynomial

/-- `S53L75.poly` with explicit coefficients in `t`. -/
noncomputable def p53X : ℝ[X] := C (1 : ℝ) + C (-873965128000 / 2305358680767 : ℝ) * X ^ 2 + C (-775375480000000000 / 1202930781287702251 : ℝ) * X ^ 4 + C (36046083680000000000000 / 12121963477656640606803 : ℝ) * X ^ 6 + C (-3186985891840000000000000000 / 841496434391642381512865461 : ℝ) * X ^ 8 + C (781666899968000000000000000000 / 1268072065097166435995216997827 : ℝ) * X ^ 10 + C (31009528217600000000000000000000000 / 329292145369481850020773995450086073 : ℝ) * X ^ 12

theorem p53X_eval (t : ℝ) : p53X.eval t = (1 : ℝ) + (-873965128000 / 2305358680767 : ℝ) * t ^ 2 + (-775375480000000000 / 1202930781287702251 : ℝ) * t ^ 4 + (36046083680000000000000 / 12121963477656640606803 : ℝ) * t ^ 6 + (-3186985891840000000000000000 / 841496434391642381512865461 : ℝ) * t ^ 8 + (781666899968000000000000000000 / 1268072065097166435995216997827 : ℝ) * t ^ 10 + (31009528217600000000000000000000000 / 329292145369481850020773995450086073 : ℝ) * t ^ 12 := by
  simp [p53X]

theorem S53_poly_eq : S53L75.poly = p53X := by
  apply Polynomial.funext
  intro t
  rw [S53L75.poly_eval, S53_p_eq, p53X_eval]
  unfold q53
  ring

theorem p53X_natDegree_le : p53X.natDegree ≤ 12 := by
  unfold p53X; compute_degree

theorem p53X_coeff (k : ℕ) : p53X.coeff k = (if k = 0 then (1 : ℝ) else 0) + (if k = 2 then (-873965128000 / 2305358680767 : ℝ) else 0) + (if k = 4 then (-775375480000000000 / 1202930781287702251 : ℝ) else 0) + (if k = 6 then (36046083680000000000000 / 12121963477656640606803 : ℝ) else 0) + (if k = 8 then (-3186985891840000000000000000 / 841496434391642381512865461 : ℝ) else 0) + (if k = 10 then (781666899968000000000000000000 / 1268072065097166435995216997827 : ℝ) else 0) + (if k = 12 then (31009528217600000000000000000000000 / 329292145369481850020773995450086073 : ℝ) else 0) := by
  simp [p53X, coeff_add, Polynomial.coeff_one]

set_option maxHeartbeats 0 in
theorem profM_S53_le (P : ParamsQ) (hprof : P.prof = S53L75.poly) (hlam : P.lam = 191 / 100) :
    P.profM 0 ≤ (7203 / 1000 : ℝ) ∧ P.profM 1 ≤ (45 : ℝ) ∧ P.profM 2 ≤ (291 : ℝ) ∧ P.profM 3 ≤ (1742 : ℝ) ∧ P.profM 4 ≤ (9417 : ℝ) ∧ P.profM 5 ≤ (45509 : ℝ) ∧ P.profM 6 ≤ (196849 : ℝ) ∧ P.profM 7 ≤ (769221 : ℝ) ∧ P.profM 8 ≤ (2736358 : ℝ) ∧ P.profM 9 ≤ (8685095 : ℝ) ∧ P.profM 10 ≤ (22808831 : ℝ) ∧ P.profM 11 ≤ (43082170 : ℝ) ∧ P.profM 12 ≤ (45112219 : ℝ) ∧ ∀ j, 13 ≤ j → P.profM j = 0 := by
  have hR : P.lam / 2 = 191 / 200 := by rw [hlam]; norm_num
  have hR0 : (0 : ℝ) ≤ P.lam / 2 := by rw [hR]; norm_num
  have hdeg : ∀ j, (derivative^[j] p53X).natDegree ≤ 12 :=
    fun j => (natDegree_iterate_derivative _ j).trans
      (Nat.sub_le_of_le_add (by linarith [p53X_natDegree_le]))
  have hM : ∀ j, P.profM j ≤ ∑ i ∈ Finset.range 13,
      |(derivative^[j] p53X).coeff i| * (P.lam / 2) ^ i := by
    intro j
    unfold ParamsQ.profM
    rw [hprof, S53_poly_eq]
    exact Mpoly_le_sum_range hR0 (hdeg j)
  have hz : ∀ j, 13 ≤ j → P.profM j = 0 := by
    intro j hj
    unfold ParamsQ.profM ParamsQ.Mpoly
    rw [hprof, S53_poly_eq, iterate_derivative_eq_zero (by linarith [p53X_natDegree_le])]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hz⟩ <;>
  · refine le_trans (hM _) ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_iterate_derivative,
      p53X_coeff, hR]
    norm_num [Nat.descFactorial]

set_option maxHeartbeats 0 in
theorem gevreyBprod_S53_le (P : ParamsQ) (hprof : P.prof = S53L75.poly)
    (hlam : P.lam = (S53L75.lam : ℝ)) (hw : P.w = 1) (hLL : 100 ≤ P.LL) :
    P.gevreyBprod gevreyA gevreyB ≤ gevreyGateShell := by
  have hlamR : P.lam = 191 / 100 := by rw [hlam]; norm_num [S53L75]
  have hA13 := gevreyA_ge_13
  have hB := gevreyB_le_6000
  have hB0 : 0 ≤ gevreyB := by unfold gevreyB; positivity
  have hA0 : 0 < gevreyA := by linarith
  have hLL0 : 0 < P.LL := by linarith
  set x1 := P.w / (P.LL * gevreyA) with hx1def
  set x2 := P.lam / gevreyA with hx2def
  have hx1 : x1 ≤ 1 / 1300 := by
    rw [hx1def, hw, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul hLL hA13 (by norm_num) (by linarith)
    linarith
  have hx1_0 : 0 ≤ x1 := by rw [hx1def, hw]; positivity
  have hx2 : x2 ≤ 3 / 20 := by
    rw [hx2def, hlamR, div_le_div_iff₀ hA0 (by norm_num)]; linarith
  have hx2_0 : 0 ≤ x2 := by rw [hx2def, hlamR]; positivity
  have hM0 : ∀ j, 0 ≤ P.profM j := fun j => by
    unfold ParamsQ.profM ParamsQ.Mpoly
    exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by rw [hlamR]; norm_num) i)
  have hdeg : P.prof.natDegree + 1 ≤ 13 := by
    rw [hprof, S53_poly_eq]; linarith [p53X_natDegree_le]
  have hS : ∀ x : ℝ, 0 ≤ x →
      ∑ j ∈ Finset.range (P.prof.natDegree + 1), P.profM j * x ^ j
        ≤ ∑ j ∈ Finset.range 13, P.profM j * x ^ j := fun x hx =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hdeg)
      (fun j _ _ => mul_nonneg (hM0 j) (pow_nonneg hx j))
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, -⟩ := profM_S53_le P hprof hlamR
  have a0 : P.profM 0 * x1 ^ 0 ≤ (7203 / 1000 : ℝ) * (1 / 1300 : ℝ) ^ 0 :=
    mul_le_mul m0 (pow_le_pow_left₀ hx1_0 hx1 0) (pow_nonneg hx1_0 0) (le_trans (hM0 0) m0)
  have a1 : P.profM 1 * x1 ^ 1 ≤ (45 : ℝ) * (1 / 1300 : ℝ) ^ 1 :=
    mul_le_mul m1 (pow_le_pow_left₀ hx1_0 hx1 1) (pow_nonneg hx1_0 1) (le_trans (hM0 1) m1)
  have a2 : P.profM 2 * x1 ^ 2 ≤ (291 : ℝ) * (1 / 1300 : ℝ) ^ 2 :=
    mul_le_mul m2 (pow_le_pow_left₀ hx1_0 hx1 2) (pow_nonneg hx1_0 2) (le_trans (hM0 2) m2)
  have a3 : P.profM 3 * x1 ^ 3 ≤ (1742 : ℝ) * (1 / 1300 : ℝ) ^ 3 :=
    mul_le_mul m3 (pow_le_pow_left₀ hx1_0 hx1 3) (pow_nonneg hx1_0 3) (le_trans (hM0 3) m3)
  have a4 : P.profM 4 * x1 ^ 4 ≤ (9417 : ℝ) * (1 / 1300 : ℝ) ^ 4 :=
    mul_le_mul m4 (pow_le_pow_left₀ hx1_0 hx1 4) (pow_nonneg hx1_0 4) (le_trans (hM0 4) m4)
  have a5 : P.profM 5 * x1 ^ 5 ≤ (45509 : ℝ) * (1 / 1300 : ℝ) ^ 5 :=
    mul_le_mul m5 (pow_le_pow_left₀ hx1_0 hx1 5) (pow_nonneg hx1_0 5) (le_trans (hM0 5) m5)
  have a6 : P.profM 6 * x1 ^ 6 ≤ (196849 : ℝ) * (1 / 1300 : ℝ) ^ 6 :=
    mul_le_mul m6 (pow_le_pow_left₀ hx1_0 hx1 6) (pow_nonneg hx1_0 6) (le_trans (hM0 6) m6)
  have a7 : P.profM 7 * x1 ^ 7 ≤ (769221 : ℝ) * (1 / 1300 : ℝ) ^ 7 :=
    mul_le_mul m7 (pow_le_pow_left₀ hx1_0 hx1 7) (pow_nonneg hx1_0 7) (le_trans (hM0 7) m7)
  have a8 : P.profM 8 * x1 ^ 8 ≤ (2736358 : ℝ) * (1 / 1300 : ℝ) ^ 8 :=
    mul_le_mul m8 (pow_le_pow_left₀ hx1_0 hx1 8) (pow_nonneg hx1_0 8) (le_trans (hM0 8) m8)
  have a9 : P.profM 9 * x1 ^ 9 ≤ (8685095 : ℝ) * (1 / 1300 : ℝ) ^ 9 :=
    mul_le_mul m9 (pow_le_pow_left₀ hx1_0 hx1 9) (pow_nonneg hx1_0 9) (le_trans (hM0 9) m9)
  have a10 : P.profM 10 * x1 ^ 10 ≤ (22808831 : ℝ) * (1 / 1300 : ℝ) ^ 10 :=
    mul_le_mul m10 (pow_le_pow_left₀ hx1_0 hx1 10) (pow_nonneg hx1_0 10) (le_trans (hM0 10) m10)
  have a11 : P.profM 11 * x1 ^ 11 ≤ (43082170 : ℝ) * (1 / 1300 : ℝ) ^ 11 :=
    mul_le_mul m11 (pow_le_pow_left₀ hx1_0 hx1 11) (pow_nonneg hx1_0 11) (le_trans (hM0 11) m11)
  have a12 : P.profM 12 * x1 ^ 12 ≤ (45112219 : ℝ) * (1 / 1300 : ℝ) ^ 12 :=
    mul_le_mul m12 (pow_le_pow_left₀ hx1_0 hx1 12) (pow_nonneg hx1_0 12) (le_trans (hM0 12) m12)
  have b0 : P.profM 0 * x2 ^ 0 ≤ (7203 / 1000 : ℝ) * (3 / 20 : ℝ) ^ 0 :=
    mul_le_mul m0 (pow_le_pow_left₀ hx2_0 hx2 0) (pow_nonneg hx2_0 0) (le_trans (hM0 0) m0)
  have b1 : P.profM 1 * x2 ^ 1 ≤ (45 : ℝ) * (3 / 20 : ℝ) ^ 1 :=
    mul_le_mul m1 (pow_le_pow_left₀ hx2_0 hx2 1) (pow_nonneg hx2_0 1) (le_trans (hM0 1) m1)
  have b2 : P.profM 2 * x2 ^ 2 ≤ (291 : ℝ) * (3 / 20 : ℝ) ^ 2 :=
    mul_le_mul m2 (pow_le_pow_left₀ hx2_0 hx2 2) (pow_nonneg hx2_0 2) (le_trans (hM0 2) m2)
  have b3 : P.profM 3 * x2 ^ 3 ≤ (1742 : ℝ) * (3 / 20 : ℝ) ^ 3 :=
    mul_le_mul m3 (pow_le_pow_left₀ hx2_0 hx2 3) (pow_nonneg hx2_0 3) (le_trans (hM0 3) m3)
  have b4 : P.profM 4 * x2 ^ 4 ≤ (9417 : ℝ) * (3 / 20 : ℝ) ^ 4 :=
    mul_le_mul m4 (pow_le_pow_left₀ hx2_0 hx2 4) (pow_nonneg hx2_0 4) (le_trans (hM0 4) m4)
  have b5 : P.profM 5 * x2 ^ 5 ≤ (45509 : ℝ) * (3 / 20 : ℝ) ^ 5 :=
    mul_le_mul m5 (pow_le_pow_left₀ hx2_0 hx2 5) (pow_nonneg hx2_0 5) (le_trans (hM0 5) m5)
  have b6 : P.profM 6 * x2 ^ 6 ≤ (196849 : ℝ) * (3 / 20 : ℝ) ^ 6 :=
    mul_le_mul m6 (pow_le_pow_left₀ hx2_0 hx2 6) (pow_nonneg hx2_0 6) (le_trans (hM0 6) m6)
  have b7 : P.profM 7 * x2 ^ 7 ≤ (769221 : ℝ) * (3 / 20 : ℝ) ^ 7 :=
    mul_le_mul m7 (pow_le_pow_left₀ hx2_0 hx2 7) (pow_nonneg hx2_0 7) (le_trans (hM0 7) m7)
  have b8 : P.profM 8 * x2 ^ 8 ≤ (2736358 : ℝ) * (3 / 20 : ℝ) ^ 8 :=
    mul_le_mul m8 (pow_le_pow_left₀ hx2_0 hx2 8) (pow_nonneg hx2_0 8) (le_trans (hM0 8) m8)
  have b9 : P.profM 9 * x2 ^ 9 ≤ (8685095 : ℝ) * (3 / 20 : ℝ) ^ 9 :=
    mul_le_mul m9 (pow_le_pow_left₀ hx2_0 hx2 9) (pow_nonneg hx2_0 9) (le_trans (hM0 9) m9)
  have b10 : P.profM 10 * x2 ^ 10 ≤ (22808831 : ℝ) * (3 / 20 : ℝ) ^ 10 :=
    mul_le_mul m10 (pow_le_pow_left₀ hx2_0 hx2 10) (pow_nonneg hx2_0 10) (le_trans (hM0 10) m10)
  have b11 : P.profM 11 * x2 ^ 11 ≤ (43082170 : ℝ) * (3 / 20 : ℝ) ^ 11 :=
    mul_le_mul m11 (pow_le_pow_left₀ hx2_0 hx2 11) (pow_nonneg hx2_0 11) (le_trans (hM0 11) m11)
  have b12 : P.profM 12 * x2 ^ 12 ≤ (45112219 : ℝ) * (3 / 20 : ℝ) ^ 12 :=
    mul_le_mul m12 (pow_le_pow_left₀ hx2_0 hx2 12) (pow_nonneg hx2_0 12) (le_trans (hM0 12) m12)
  have hS1 : ∑ j ∈ Finset.range 13, P.profM j * x1 ^ j ≤ (7203 / 1000 : ℝ) * (1 / 1300 : ℝ) ^ 0 + (45 : ℝ) * (1 / 1300 : ℝ) ^ 1 + (291 : ℝ) * (1 / 1300 : ℝ) ^ 2 + (1742 : ℝ) * (1 / 1300 : ℝ) ^ 3 + (9417 : ℝ) * (1 / 1300 : ℝ) ^ 4 + (45509 : ℝ) * (1 / 1300 : ℝ) ^ 5 + (196849 : ℝ) * (1 / 1300 : ℝ) ^ 6 + (769221 : ℝ) * (1 / 1300 : ℝ) ^ 7 + (2736358 : ℝ) * (1 / 1300 : ℝ) ^ 8 + (8685095 : ℝ) * (1 / 1300 : ℝ) ^ 9 + (22808831 : ℝ) * (1 / 1300 : ℝ) ^ 10 + (43082170 : ℝ) * (1 / 1300 : ℝ) ^ 11 + (45112219 : ℝ) * (1 / 1300 : ℝ) ^ 12 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    linarith [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
  have hS2 : ∑ j ∈ Finset.range 13, P.profM j * x2 ^ j ≤ (7203 / 1000 : ℝ) * (3 / 20 : ℝ) ^ 0 + (45 : ℝ) * (3 / 20 : ℝ) ^ 1 + (291 : ℝ) * (3 / 20 : ℝ) ^ 2 + (1742 : ℝ) * (3 / 20 : ℝ) ^ 3 + (9417 : ℝ) * (3 / 20 : ℝ) ^ 4 + (45509 : ℝ) * (3 / 20 : ℝ) ^ 5 + (196849 : ℝ) * (3 / 20 : ℝ) ^ 6 + (769221 : ℝ) * (3 / 20 : ℝ) ^ 7 + (2736358 : ℝ) * (3 / 20 : ℝ) ^ 8 + (8685095 : ℝ) * (3 / 20 : ℝ) ^ 9 + (22808831 : ℝ) * (3 / 20 : ℝ) ^ 10 + (43082170 : ℝ) * (3 / 20 : ℝ) ^ 11 + (45112219 : ℝ) * (3 / 20 : ℝ) ^ 12 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    linarith [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]
  have hS10 : 0 ≤ ∑ j ∈ Finset.range 13, P.profM j * x1 ^ j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hM0 j) (pow_nonneg hx1_0 j)
  have hmul : gevreyB * (∑ j ∈ Finset.range 13, P.profM j * x1 ^ j)
      ≤ 6000 * ((7203 / 1000 : ℝ) * (1 / 1300 : ℝ) ^ 0 + (45 : ℝ) * (1 / 1300 : ℝ) ^ 1 + (291 : ℝ) * (1 / 1300 : ℝ) ^ 2 + (1742 : ℝ) * (1 / 1300 : ℝ) ^ 3 + (9417 : ℝ) * (1 / 1300 : ℝ) ^ 4 + (45509 : ℝ) * (1 / 1300 : ℝ) ^ 5 + (196849 : ℝ) * (1 / 1300 : ℝ) ^ 6 + (769221 : ℝ) * (1 / 1300 : ℝ) ^ 7 + (2736358 : ℝ) * (1 / 1300 : ℝ) ^ 8 + (8685095 : ℝ) * (1 / 1300 : ℝ) ^ 9 + (22808831 : ℝ) * (1 / 1300 : ℝ) ^ 10 + (43082170 : ℝ) * (1 / 1300 : ℝ) ^ 11 + (45112219 : ℝ) * (1 / 1300 : ℝ) ^ 12) := mul_le_mul hB hS1 hS10 (by norm_num)
  have hnum : 6000 * ((7203 / 1000 : ℝ) * (1 / 1300 : ℝ) ^ 0 + (45 : ℝ) * (1 / 1300 : ℝ) ^ 1 + (291 : ℝ) * (1 / 1300 : ℝ) ^ 2 + (1742 : ℝ) * (1 / 1300 : ℝ) ^ 3 + (9417 : ℝ) * (1 / 1300 : ℝ) ^ 4 + (45509 : ℝ) * (1 / 1300 : ℝ) ^ 5 + (196849 : ℝ) * (1 / 1300 : ℝ) ^ 6 + (769221 : ℝ) * (1 / 1300 : ℝ) ^ 7 + (2736358 : ℝ) * (1 / 1300 : ℝ) ^ 8 + (8685095 : ℝ) * (1 / 1300 : ℝ) ^ 9 + (22808831 : ℝ) * (1 / 1300 : ℝ) ^ 10 + (43082170 : ℝ) * (1 / 1300 : ℝ) ^ 11 + (45112219 : ℝ) * (1 / 1300 : ℝ) ^ 12) + ((7203 / 1000 : ℝ) * (3 / 20 : ℝ) ^ 0 + (45 : ℝ) * (3 / 20 : ℝ) ^ 1 + (291 : ℝ) * (3 / 20 : ℝ) ^ 2 + (1742 : ℝ) * (3 / 20 : ℝ) ^ 3 + (9417 : ℝ) * (3 / 20 : ℝ) ^ 4 + (45509 : ℝ) * (3 / 20 : ℝ) ^ 5 + (196849 : ℝ) * (3 / 20 : ℝ) ^ 6 + (769221 : ℝ) * (3 / 20 : ℝ) ^ 7 + (2736358 : ℝ) * (3 / 20 : ℝ) ^ 8 + (8685095 : ℝ) * (3 / 20 : ℝ) ^ 9 + (22808831 : ℝ) * (3 / 20 : ℝ) ^ 10 + (43082170 : ℝ) * (3 / 20 : ℝ) ^ 11 + (45112219 : ℝ) * (3 / 20 : ℝ) ^ 12) / 2 ≤ 50000 := by norm_num
  unfold ParamsQ.gevreyBprod gevreyGateShell
  rw [← hx1def, ← hx2def]
  have hS1' := mul_le_mul_of_nonneg_left (hS _ hx1_0) hB0
  linarith [hS _ hx2_0, hS1', hmul, hS2, hnum]

end ZetaShell.Design
