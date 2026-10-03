/-
Node Z5c(2′) (L7_5, 28 Sep 2026, round 2): Lemma 5c(2) restated for the Weil-form error term E′ (report §R2.1(b)):
  Σ_{r≤R₁} r E′(r, K/(rQ)) ≤ C T⁴K²(log N₀)³ (R₁²/N₀ + N₀/Q² + 1/Q² + R₁/(QN₀)),   C = 128 absolute,
under 1 ≤ Q, 1 ≤ K, 2 ≤ T ≤ N₀, e³Q ≤ N₀, R₁ ≤ Q/(2K) (the hypotheses of 5c(2), including the added T ≤ N₀).
-/
import ZetaShell.PropZ.ZDefsW

open MeasureTheory

namespace ZetaShell.PropZ

/-- the pointwise inequality, in the variables `u = 1/r`, `q = 1/Q`, `n = 1/N₀`. -/
theorem key_ptW (T K L0 q n u r N0 ℓ : ℝ) (hT : 2 ≤ T) (hK : 1 ≤ K) (hL : 1 ≤ L0) (hq0 : 0 < q)
    (hn0 : 0 < n) (hu0 : 0 < u) (hr : 1 ≤ r) (hru : r * u = 1) (hnN : n * N0 = 1)
    (hℓ : ℓ ^ 2 ≤ 9 * L0 ^ 2) :
    T ^ 2 * (K ^ 2 * q ^ 2 * u + K * q * n) + r * T ^ 2 * (T + K * u * q * N0 + 1) ^ 2 * ℓ ^ 2 * n
      ≤ 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * u * (q ^ 2 + N0 * q ^ 2) + 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * q * n
        + 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * r * n := by
  have hN0 : 0 < N0 := by
    by_contra h; push_neg at h; nlinarith
  have hT0 : 0 < T := by linarith
  have hK0 : 0 < K := by linarith
  have hr0 : 0 < r := by linarith
  have hx : (T + K * u * q * N0 + 1) ^ 2 ≤ 5 * T ^ 2 + 2 * (K * u * q * N0) ^ 2 := by
    nlinarith [sq_nonneg (T + 1 - K * u * q * N0)]
  have hP2 : r * T ^ 2 * (T + K * u * q * N0 + 1) ^ 2 * ℓ ^ 2 * n
      ≤ r * T ^ 2 * (5 * T ^ 2 + 2 * (K * u * q * N0) ^ 2) * (9 * L0 ^ 2) * n := by
    gcongr
  have e : r * T ^ 2 * (5 * T ^ 2 + 2 * (K * u * q * N0) ^ 2) * (9 * L0 ^ 2) * n
      = 45 * L0 ^ 2 * T ^ 4 * r * n + 18 * L0 ^ 2 * T ^ 2 * K ^ 2 * u * q ^ 2 * N0 * (r * u) * (n * N0) := by
    ring
  rw [e, hru, hnN, mul_one, mul_one] at hP2
  have hT24 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hK12 : K ≤ K ^ 2 := by simpa using pow_le_pow_right₀ hK (show 1 ≤ 2 by norm_num)
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hL2 : 1 ≤ L0 ^ 2 := one_le_pow₀ hL
  have m1 : T ^ 2 * (K ^ 2 * q ^ 2 * u) ≤ (T ^ 4 * K ^ 2 * L0 ^ 2) * u * q ^ 2 := by
    calc T ^ 2 * (K ^ 2 * q ^ 2 * u) = (T ^ 2 * K ^ 2) * (u * q ^ 2) * 1 := by ring
      _ ≤ (T ^ 4 * K ^ 2) * (u * q ^ 2) * L0 ^ 2 := by gcongr
      _ = _ := by ring
  have m2 : T ^ 2 * (K * q * n) ≤ (T ^ 4 * K ^ 2 * L0 ^ 2) * q * n := by
    calc T ^ 2 * (K * q * n) = (T ^ 2 * K) * (q * n) * 1 := by ring
      _ ≤ (T ^ 4 * K ^ 2) * (q * n) * L0 ^ 2 := by gcongr
      _ = _ := by ring
  have m3 : 45 * L0 ^ 2 * T ^ 4 * r * n ≤ 45 * (T ^ 4 * K ^ 2 * L0 ^ 2) * r * n := by
    calc 45 * L0 ^ 2 * T ^ 4 * r * n = 45 * (T ^ 4 * L0 ^ 2) * (r * n) * 1 := by ring
      _ ≤ 45 * (T ^ 4 * L0 ^ 2) * (r * n) * K ^ 2 := by gcongr
      _ = _ := by ring
  have m4 : 18 * L0 ^ 2 * T ^ 2 * K ^ 2 * u * q ^ 2 * N0
      ≤ 18 * (T ^ 4 * K ^ 2 * L0 ^ 2) * u * (N0 * q ^ 2) := by
    calc 18 * L0 ^ 2 * T ^ 2 * K ^ 2 * u * q ^ 2 * N0 = 18 * L0 ^ 2 * K ^ 2 * (u * (N0 * q ^ 2)) * T ^ 2 := by
          ring
      _ ≤ 18 * L0 ^ 2 * K ^ 2 * (u * (N0 * q ^ 2)) * T ^ 4 := by gcongr
      _ = _ := by ring
  have hM : 0 ≤ T ^ 4 * K ^ 2 * L0 ^ 2 := by positivity
  have hA : 0 ≤ (T ^ 4 * K ^ 2 * L0 ^ 2) * u * q ^ 2 := by positivity
  have hB : 0 ≤ (T ^ 4 * K ^ 2 * L0 ^ 2) * u * (N0 * q ^ 2) := by positivity
  have hC : 0 ≤ (T ^ 4 * K ^ 2 * L0 ^ 2) * q * n := by positivity
  have hD : 0 ≤ (T ^ 4 * K ^ 2 * L0 ^ 2) * r * n := by positivity
  nlinarith [m1, m2, m3, m4, hP2]

theorem family_EW_sum : ∃ C : ℝ, ∀ (Q K T N0 : ℝ) (R1 : ℕ), 1 ≤ Q → 1 ≤ K → 2 ≤ T → T ≤ N0 →
    Real.exp 3 * Q ≤ N0 → (R1 : ℝ) ≤ Q / (2 * K) →
    ∑ r ∈ Finset.Icc 1 R1, (r : ℝ) * EerrW T N0 r (K / (r * Q))
      ≤ C * T ^ 4 * K ^ 2 * Real.log N0 ^ 3 * ((R1 : ℝ) ^ 2 / N0 + N0 / Q ^ 2 + 1 / Q ^ 2 + R1 / (Q * N0)) := by
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
  have hRQ : (R1 : ℝ) ≤ N0 := le_trans hR (le_trans (div_le_self hQ0.le (by linarith)) hQN)
  set M := T ^ 4 * K ^ 2 * L0 ^ 2 with hM
  set B := N0 / Q ^ 2 + 1 / Q ^ 2 with hB
  have hpt : ∀ r ∈ Finset.Icc 1 R1, (r : ℝ) * EerrW T N0 r (K / (r * Q))
      ≤ 64 * M * B * (r : ℝ)⁻¹ + 64 * M / (Q * N0) + 64 * M * (r : ℝ) / N0 := by
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
    have hk := key_ptW T K L0 (1 / Q) (1 / N0) (1 / (r : ℝ)) r N0 (Real.log (r * N0 * T)) hT hK (by linarith)
      (by positivity) (by positivity) (by positivity) hr1 (by field_simp) (by field_simp) hℓ9
    have e1 : (r : ℝ) * EerrW T N0 r (K / (r * Q))
        = T ^ 2 * (K ^ 2 * (1 / Q) ^ 2 * (1 / (r : ℝ)) + K * (1 / Q) * (1 / N0))
          + r * T ^ 2 * (T + K * (1 / (r : ℝ)) * (1 / Q) * N0 + 1) ^ 2 * Real.log (r * N0 * T) ^ 2
            * (1 / N0) := by
      unfold EerrW; field_simp
    have e2 : 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * (1 / (r : ℝ)) * ((1 / Q) ^ 2 + N0 * (1 / Q) ^ 2)
          + 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * (1 / Q) * (1 / N0) + 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * r * (1 / N0)
        = 64 * M * B * (r : ℝ)⁻¹ + 64 * M / (Q * N0) + 64 * M * (r : ℝ) / N0 := by
      rw [hM, hB]; field_simp; ring
    rw [e1, ← e2]; exact hk
  have hH : ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹ ≤ 1 + Real.log R1 := by
    have := harmonic_le_one_add_log R1
    simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using this
  have hlogR : Real.log R1 ≤ L0 := by
    rcases Nat.eq_zero_or_pos R1 with h0 | h0
    · simp [h0]; linarith
    · exact Real.log_le_log (by exact_mod_cast h0) hRQ
  have hsumr : ∑ r ∈ Finset.Icc 1 R1, (r : ℝ) ≤ (R1 : ℝ) ^ 2 := by
    have := Finset.sum_le_card_nsmul (Finset.Icc 1 R1) (fun r : ℕ => (r : ℝ)) (R1 : ℝ) (fun r hr => by
      rw [Finset.mem_Icc] at hr; exact_mod_cast hr.2)
    simp only [Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at this
    nlinarith
  have hsum : ∑ r ∈ Finset.Icc 1 R1, (64 * M * B * (r : ℝ)⁻¹ + 64 * M / (Q * N0) + 64 * M * (r : ℝ) / N0)
      = 64 * M * B * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹) + R1 * (64 * M / (Q * N0))
        + 64 * M / N0 * (∑ r ∈ Finset.Icc 1 R1, (r : ℝ)) := by
    have e1 : ∑ r ∈ Finset.Icc 1 R1, 64 * M * B * (r : ℝ)⁻¹
        = 64 * M * B * ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹ := by rw [Finset.mul_sum]
    have e2 : ∑ _r ∈ Finset.Icc 1 R1, 64 * M / (Q * N0) = R1 * (64 * M / (Q * N0)) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    have e3 : ∑ r ∈ Finset.Icc 1 R1, 64 * M * (r : ℝ) / N0 = 64 * M / N0 * ∑ r ∈ Finset.Icc 1 R1, (r : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3]
  have hM0 : 0 ≤ M := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hQN0 : 0 < Q * N0 := by positivity
  have hR0 : (0 : ℝ) ≤ R1 := by positivity
  have h1 : ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹ ≤ 2 * L0 := by linarith
  have hMN : 0 ≤ 64 * M / N0 := by positivity
  calc ∑ r ∈ Finset.Icc 1 R1, (r : ℝ) * EerrW T N0 r (K / (r * Q))
      ≤ ∑ r ∈ Finset.Icc 1 R1, (64 * M * B * (r : ℝ)⁻¹ + 64 * M / (Q * N0) + 64 * M * (r : ℝ) / N0) :=
        Finset.sum_le_sum hpt
    _ = 64 * M * B * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ))⁻¹) + R1 * (64 * M / (Q * N0))
        + 64 * M / N0 * (∑ r ∈ Finset.Icc 1 R1, (r : ℝ)) := hsum
    _ ≤ 64 * M * B * (2 * L0) + R1 * (64 * M / (Q * N0)) + 64 * M / N0 * (R1 : ℝ) ^ 2 := by
        gcongr
    _ ≤ 128 * T ^ 4 * K ^ 2 * L0 ^ 3 * ((R1 : ℝ) ^ 2 / N0 + N0 / Q ^ 2 + 1 / Q ^ 2 + R1 / (Q * N0)) := by
        rw [hM, hB]
        have hL1 : 1 ≤ L0 := by linarith
        have hT4 : 0 ≤ T ^ 4 * K ^ 2 * L0 ^ 2 := by positivity
        have ha : 0 ≤ (R1 : ℝ) / (Q * N0) := by positivity
        have hb : 0 ≤ (R1 : ℝ) ^ 2 / N0 := by positivity
        have e3 : 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * (N0 / Q ^ 2 + 1 / Q ^ 2) * (2 * L0)
            + R1 * (64 * (T ^ 4 * K ^ 2 * L0 ^ 2) / (Q * N0))
            + 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) / N0 * (R1 : ℝ) ^ 2
            = 128 * T ^ 4 * K ^ 2 * L0 ^ 3 * (N0 / Q ^ 2 + 1 / Q ^ 2)
              + 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * ((R1 : ℝ) / (Q * N0) + (R1 : ℝ) ^ 2 / N0) := by
          field_simp; ring
        rw [e3]
        have h64 : 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) * ((R1 : ℝ) / (Q * N0) + (R1 : ℝ) ^ 2 / N0)
            ≤ 128 * T ^ 4 * K ^ 2 * L0 ^ 3 * ((R1 : ℝ) / (Q * N0) + (R1 : ℝ) ^ 2 / N0) := by
          have : 64 * (T ^ 4 * K ^ 2 * L0 ^ 2) ≤ 128 * T ^ 4 * K ^ 2 * L0 ^ 3 := by nlinarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
        nlinarith [h64]

end ZetaShell.PropZ
