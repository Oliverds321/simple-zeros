/-
Node Z5c (L7_5, 28 Sep 2026): Lemma 5c (2), family errors (sec_shell.tex, lem:shell-5c):
"Take Δ_r = K/(rQ) for r ≤ R₁ ≤ Q/(2K), s₀ ≥ log Q + 3 and N₀ ≤ Q^{2−η}. (2) Σ_{r≤R₁} r E(r,Δ_r) ≪
 T⁴K⁴(log N₀)³(N₀/Q⁴ + 1/Q² + R₁/(QN₀))."
ADDED HYPOTHESIS `T ≤ N₀` (the draft leaves it implicit; without it `log²(r N₀ T)` is not `≪ (log N₀)²`; Theorem S
has `T = (log Q)^{r+ε} ≤ Q ≤ N₀`). `N₀ ≥ e³ Q` is the draft's `s₀ ≥ log Q + 3`; `N₀ ≤ Q^{2−η}` is not needed for (2).
The constant is absolute: `C = 128`.
-/
import ZetaShell.PropZ.ZDefs

open MeasureTheory

namespace ZetaShell.PropZ

/-- the pointwise inequality, in the variables `u = 1/r`, `q = 1/Q`, `n = 1/N₀`. -/
theorem key_pt (T K L0 q n u N0 ℓ : ℝ) (hT : 2 ≤ T) (hK : 1 ≤ K) (hL : 1 ≤ L0) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hn0 : 0 < n) (hn1 : n ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1) (hnN : n * N0 = 1) (hℓ : ℓ ^ 2 ≤ 9 * L0 ^ 2) :
    T ^ 2 * (K ^ 2 * q ^ 2 * u + K * q * n)
        + T ^ 2 * (T + K * u * q * N0 + 1) ^ 2 * (K ^ 2 * q ^ 2 * u * n + K * q * n ^ 2) * ℓ ^ 2
      ≤ 64 * (T ^ 4 * K ^ 4 * L0 ^ 2) * u * (N0 * q ^ 4 + q ^ 2) + 46 * (T ^ 4 * K ^ 4 * L0 ^ 2) * q * n := by
  have hN0 : 0 < N0 := by
    by_contra h; push_neg at h; nlinarith
  have hT0 : 0 < T := by linarith
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L0 := by linarith
  have hx : (T + K * u * q * N0 + 1) ^ 2 ≤ 5 * T ^ 2 + 2 * (K * u * q * N0) ^ 2 := by
    nlinarith [sq_nonneg (T + 1 - K * u * q * N0)]
  have hP2 : T ^ 2 * (T + K * u * q * N0 + 1) ^ 2 * (K ^ 2 * q ^ 2 * u * n + K * q * n ^ 2) * ℓ ^ 2
      ≤ T ^ 2 * (5 * T ^ 2 + 2 * (K * u * q * N0) ^ 2) * (K ^ 2 * q ^ 2 * u * n + K * q * n ^ 2)
          * (9 * L0 ^ 2) := by
    gcongr
  have e : T ^ 2 * (5 * T ^ 2 + 2 * (K * u * q * N0) ^ 2) * (K ^ 2 * q ^ 2 * u * n + K * q * n ^ 2)
          * (9 * L0 ^ 2)
      = 9 * L0 ^ 2 * T ^ 2 * (5 * T ^ 2 * K ^ 2 * q ^ 2 * u * n + 5 * T ^ 2 * K * q * n ^ 2
          + 2 * K ^ 4 * u ^ 3 * q ^ 4 * N0 * (n * N0) + 2 * K ^ 3 * u ^ 2 * q ^ 3 * (n * N0) ^ 2) := by ring
  rw [e, hnN, one_pow, mul_one, mul_one] at hP2
  have hT24 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hK24 : K ^ 2 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hK14 : K ≤ K ^ 4 := by simpa using pow_le_pow_right₀ hK (show 1 ≤ 4 by norm_num)
  have hK34 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hL2 : 1 ≤ L0 ^ 2 := one_le_pow₀ hL
  have hu3 : u ^ 3 ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
  have hu2 : u ^ 2 ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
  have hq32 : q ^ 3 ≤ q ^ 2 := pow_le_pow_of_le_one hq0.le hq1 (by norm_num)
  have hn2 : n ^ 2 ≤ n := pow_le_of_le_one hn0.le hn1 (by norm_num)
  have m1 : T ^ 2 * (K ^ 2 * q ^ 2 * u) ≤ (T ^ 4 * K ^ 4 * L0 ^ 2) * u * q ^ 2 := by
    calc T ^ 2 * (K ^ 2 * q ^ 2 * u) = (T ^ 2 * K ^ 2) * (u * q ^ 2) * 1 := by ring
      _ ≤ (T ^ 4 * K ^ 4) * (u * q ^ 2) * L0 ^ 2 := by gcongr
      _ = _ := by ring
  have m2 : T ^ 2 * (K * q * n) ≤ (T ^ 4 * K ^ 4 * L0 ^ 2) * q * n := by
    calc T ^ 2 * (K * q * n) = (T ^ 2 * K) * (q * n) * 1 := by ring
      _ ≤ (T ^ 4 * K ^ 4) * (q * n) * L0 ^ 2 := by gcongr
      _ = _ := by ring
  have m3 : 9 * L0 ^ 2 * T ^ 2 * (5 * T ^ 2 * K ^ 2 * q ^ 2 * u * n)
      ≤ 45 * (T ^ 4 * K ^ 4 * L0 ^ 2) * u * q ^ 2 := by
    calc 9 * L0 ^ 2 * T ^ 2 * (5 * T ^ 2 * K ^ 2 * q ^ 2 * u * n)
        = 45 * (T ^ 2 * T ^ 2 * L0 ^ 2) * K ^ 2 * (u * q ^ 2) * n := by ring
      _ ≤ 45 * (T ^ 2 * T ^ 2 * L0 ^ 2) * K ^ 4 * (u * q ^ 2) * 1 := by gcongr
      _ = _ := by ring
  have m4 : 9 * L0 ^ 2 * T ^ 2 * (5 * T ^ 2 * K * q * n ^ 2) ≤ 45 * (T ^ 4 * K ^ 4 * L0 ^ 2) * q * n := by
    calc 9 * L0 ^ 2 * T ^ 2 * (5 * T ^ 2 * K * q * n ^ 2) = 45 * (T ^ 2 * T ^ 2 * L0 ^ 2) * K * q * n ^ 2 := by
          ring
      _ ≤ 45 * (T ^ 2 * T ^ 2 * L0 ^ 2) * K ^ 4 * q * n := by gcongr
      _ = _ := by ring
  have m5 : 9 * L0 ^ 2 * T ^ 2 * (2 * K ^ 4 * u ^ 3 * q ^ 4 * N0)
      ≤ 18 * (T ^ 4 * K ^ 4 * L0 ^ 2) * u * (N0 * q ^ 4) := by
    calc 9 * L0 ^ 2 * T ^ 2 * (2 * K ^ 4 * u ^ 3 * q ^ 4 * N0)
        = 18 * L0 ^ 2 * T ^ 2 * K ^ 4 * u ^ 3 * (N0 * q ^ 4) := by ring
      _ ≤ 18 * L0 ^ 2 * T ^ 4 * K ^ 4 * u * (N0 * q ^ 4) := by gcongr
      _ = _ := by ring
  have m6 : 9 * L0 ^ 2 * T ^ 2 * (2 * K ^ 3 * u ^ 2 * q ^ 3) ≤ 18 * (T ^ 4 * K ^ 4 * L0 ^ 2) * u * q ^ 2 := by
    calc 9 * L0 ^ 2 * T ^ 2 * (2 * K ^ 3 * u ^ 2 * q ^ 3) = 18 * L0 ^ 2 * T ^ 2 * K ^ 3 * u ^ 2 * q ^ 3 := by
          ring
      _ ≤ 18 * L0 ^ 2 * T ^ 4 * K ^ 4 * u * q ^ 2 := by gcongr
      _ = _ := by ring
  have hM : 0 ≤ T ^ 4 * K ^ 4 * L0 ^ 2 * u * (N0 * q ^ 4) := by positivity
  nlinarith [m1, m2, m3, m4, m5, m6, hP2, hM]

theorem family_E_sum : ∃ C : ℝ, ∀ (Q K T N0 : ℝ) (R1 : ℕ), 1 ≤ Q → 1 ≤ K → 2 ≤ T → T ≤ N0 →
    Real.exp 3 * Q ≤ N0 → (R1 : ℝ) ≤ Q / (2 * K) →
    ∑ r ∈ Finset.Icc 1 R1, (r : ℝ) * Eerr T N0 r (K / (r * Q))
      ≤ C * T ^ 4 * K ^ 4 * Real.log N0 ^ 3 * (N0 / Q ^ 4 + 1 / Q ^ 2 + R1 / (Q * N0)) := by
  refine ⟨128, fun Q K T N0 R1 hQ hK hT hTN hN hR => ?_⟩
  have hQ0 : 0 < Q := by linarith
  have hK0 : 0 < K := by linarith
  have he3 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hQN : Q ≤ N0 := le_trans (le_mul_of_one_le_left hQ0.le he3) hN
  have hN1 : 1 ≤ N0 := le_trans hQ hQN
  have hN0 : 0 < N0 := by linarith
  set L0 := Real.log N0 with hL0def
  have hL3 : 3 ≤ L0 := by
    have h := Real.log_le_log (Real.exp_pos 3) (le_trans (le_mul_of_one_le_right (Real.exp_pos 3).le hQ) hN)
    rwa [Real.log_exp] at h
  have hRQ : (R1 : ℝ) ≤ N0 := by
    refine le_trans hR (le_trans (div_le_self hQ0.le (by linarith)) hQN)
  set M := T ^ 4 * K ^ 4 * L0 ^ 2 with hM
  set B := N0 / Q ^ 4 + 1 / Q ^ 2 with hB
  have hpt : ∀ r ∈ Finset.Icc 1 R1, (r : ℝ) * Eerr T N0 r (K / (r * Q))
      ≤ 64 * M * B * (r : ℝ)⁻¹ + 46 * M / (Q * N0) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.1
    have hr0 : (0 : ℝ) < r := by linarith
    have hrN : (r : ℝ) ≤ N0 := le_trans (by exact_mod_cast hr.2) hRQ
    have hpos : 0 < (r : ℝ) * N0 * T := by positivity
    have hℓ0 : 0 ≤ Real.log (r * N0 * T) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr1 hN1) (by linarith))
    have hℓ3 : Real.log (r * N0 * T) ≤ 3 * L0 := by
      have h1 : Real.log (r * N0 * T) ≤ Real.log (N0 ^ 3) := by
        apply Real.log_le_log hpos
        have : (r : ℝ) * N0 * T ≤ N0 * N0 * N0 := by gcongr
        nlinarith
      rw [Real.log_pow] at h1; push_cast at h1; linarith
    have hℓ9 : Real.log (r * N0 * T) ^ 2 ≤ 9 * L0 ^ 2 := by nlinarith
    have hk := key_pt T K L0 (1 / Q) (1 / N0) (1 / (r : ℝ)) N0 (Real.log (r * N0 * T)) hT hK (by linarith)
      (by positivity) (by rw [div_le_one hQ0]; exact hQ) (by positivity) (by rw [div_le_one hN0]; exact hN1)
      (by positivity) (by rw [div_le_one hr0]; exact hr1) (by field_simp) hℓ9
    have e1 : (r : ℝ) * Eerr T N0 r (K / (r * Q))
        = T ^ 2 * (K ^ 2 * (1 / Q) ^ 2 * (1 / (r : ℝ)) + K * (1 / Q) * (1 / N0))
          + T ^ 2 * (T + K * (1 / (r : ℝ)) * (1 / Q) * N0 + 1) ^ 2
            * (K ^ 2 * (1 / Q) ^ 2 * (1 / (r : ℝ)) * (1 / N0) + K * (1 / Q) * (1 / N0) ^ 2)
            * Real.log (r * N0 * T) ^ 2 := by
      unfold Eerr; field_simp
    have e2 : 64 * (T ^ 4 * K ^ 4 * L0 ^ 2) * (1 / (r : ℝ)) * (N0 * (1 / Q) ^ 4 + (1 / Q) ^ 2)
          + 46 * (T ^ 4 * K ^ 4 * L0 ^ 2) * (1 / Q) * (1 / N0)
        = 64 * M * B * (r : ℝ)⁻¹ + 46 * M / (Q * N0) := by
      rw [hM, hB]; field_simp
    rw [e1, ← e2]; exact hk
  have hH : ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹ ≤ 1 + Real.log R1 := by
    have := harmonic_le_one_add_log R1
    simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using this
  have hlogR : Real.log R1 ≤ L0 := by
    rcases Nat.eq_zero_or_pos R1 with h0 | h0
    · simp [h0]; linarith
    · exact Real.log_le_log (by exact_mod_cast h0) hRQ
  have hsum : ∑ r ∈ Finset.Icc 1 R1, (64 * M * B * (r : ℝ)⁻¹ + 46 * M / (Q * N0))
      = 64 * M * B * ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹ + R1 * (46 * M / (Q * N0)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
  have hM0 : 0 ≤ M := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hQN0 : 0 < Q * N0 := by positivity
  calc ∑ r ∈ Finset.Icc 1 R1, (r : ℝ) * Eerr T N0 r (K / (r * Q))
      ≤ ∑ r ∈ Finset.Icc 1 R1, (64 * M * B * (r : ℝ)⁻¹ + 46 * M / (Q * N0)) := Finset.sum_le_sum hpt
    _ = 64 * M * B * ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹ + R1 * (46 * M / (Q * N0)) := hsum
    _ ≤ 64 * M * B * (2 * L0) + (R1 / (Q * N0)) * (128 * M * L0) := by
        have h1 : ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹ ≤ 2 * L0 := by linarith
        have h2 : R1 * (46 * M / (Q * N0)) ≤ (R1 / (Q * N0)) * (128 * M * L0) := by
          rw [mul_div_assoc', div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ hQN0.le
          have hR0 : (0 : ℝ) ≤ R1 := by positivity
          have h46 : 46 * M ≤ 128 * M * L0 := by nlinarith
          have := mul_le_mul_of_nonneg_left h46 hR0
          linarith
        gcongr
    _ = 128 * T ^ 4 * K ^ 4 * L0 ^ 3 * (N0 / Q ^ 4 + 1 / Q ^ 2 + R1 / (Q * N0)) := by
        rw [hM, hB]; ring

end ZetaShell.PropZ
