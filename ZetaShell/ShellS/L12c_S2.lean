/-
L7_12c (3 Oct 2026): node S2 (L7_10's `L10_S2`, statement byte-identical) DERIVED from Z6a and the CORRECTED Z6d,
`Z6d_counts_corr` (statement-change request SCR-Z6d: the near clause on `5 X₀ ≤ s₀`). Same proof as `L12_S2.lean`
(which uses the frozen `Z6d_counts`), with one added step: the near clause is used at `X₀ = (log log Q)/κ′`, and
`5 X₀ ≤ s₀` holds eventually (`5 log log Q ≤ κ′ log Q ≤ κ′ s₀`, from `ℓ e^{−ℓ} ≤ κ′/5`).
Node S2 (L7_10): **Theorem S, step 2: the zero side at the rate** (proof of thm:shell-S, the choice
`e^{X₀} = (log Q)^{1/κ′}`).
Proof: WLOG `θ ≥ 0` (replace `θ` by `θ' = max θ 0`, still `< θ(α′)`). Choose `ε″ = (2/(1+θ') − κ₀)/2 > 0`,
`κ₀ = 4 − 4/α′`, so `κ′ = κ₀ + ε″ < 2/(1+θ')`, hence `γ := (2−κ′)/κ′ > θ'` and `g := 2(κ′−1)₊/κ′ < 1 − θ'`.
With `ℓ = log log Q` and `X₀ = ℓ/κ′`: Z6a gives `𝔷 ≤ C log s₀ (near² + s₀ rest) + C/N₀`; Z6d gives
`near ≤ C(1+X₀)e^{(κ′−1)₊X₀}`, `s₀ rest ≤ C(N₀^{−c} + s₀e^{−γℓ})`; then every term is `≤ const · e^{−θ'ℓ} s₀`
because `ℓ⁴e^{−(1−g−θ')ℓ} → 0` and `ℓ²e^{−(γ−θ')ℓ} → 0`.
Uses `Z6a_zero_sums` (`L12b_Z6a`) and `Z6d_counts_corr` (`L12c_Z6d`), both proved (level A, `ZeroDensityInput` as
hypothesis).
-/
import ZetaShell.ShellS.L12b_Z6a
import ZetaShell.ShellS.L12c_Z6d
import ZetaShell.ShellS.L12_Aux

noncomputable section

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

lemma L12_varpi_nonneg (T μ : ℝ) (k : ℕ) (ρ : ℂ) (hμ : 0 ≤ μ) : 0 ≤ varpi T μ k ρ := by
  unfold varpi
  apply Real.rpow_nonneg
  have : 0 ≤ max (|ρ.im| - 2 * T) 0 / (μ + 1) := div_nonneg (le_max_right _ _) (by linarith)
  linarith

lemma L12_nearSum_nonneg (Q T K ε s₀ : ℝ) (k : ℕ) (X₀ : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K) :
    0 ≤ nearSum Q T K ε s₀ k X₀ := by
  unfold nearSum famZeroSum
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro χ _
  split_ifs with h
  · exact le_rfl
  · apply tsum_nonneg
    intro ρ
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold gNear
    split_ifs
    · unfold bRho
      apply mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)
      apply L12_varpi_nonneg
      unfold muR
      apply div_nonneg (mul_nonneg hK (Real.exp_pos _).le) (mul_nonneg (Nat.cast_nonneg _) hQ)
    · exact le_rfl

lemma L12_restSq_nonneg (Q T K ε s₀ : ℝ) (k : ℕ) (X₀ : ℝ) :
    0 ≤ restSq Q T K ε s₀ k X₀ := by
  unfold restSq famZeroSum
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro χ _
  split_ifs with h
  · exact le_rfl
  · apply tsum_nonneg
    intro ρ
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold gRest
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

set_option maxHeartbeats 1000000 in
theorem S2_zero_side (hD : ZeroDensityInput) (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (A : ℕ) (hA : 2 ≤ A)
    (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (B θ : ℝ) (hB : 1 ≤ B) (hθ : θ < thetaD1p αp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      (Real.log K + 2) * (twin Qn r0 ε0 * zeroPairSum Qn (twin Qn r0 ε0) K ε s₀ A 3)
        ≤ C * Real.log Qn ^ (-θ) * (twin Qn r0 ε0 * s₀) := by
  -- the exponents
  set θ' := max θ 0 with hθ'def
  have hθθ' : θ ≤ θ' := le_max_left _ _
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  set κ₀ := 4 - 4 / αp with hκ₀def
  have hαpos : 0 < αp := by linarith
  have hκ₀pos : 0 < κ₀ := by
    rw [hκ₀def, sub_pos, div_lt_iff₀ hαpos]; linarith
  have hthD : thetaD1p αp = min 1 ((2 - κ₀) / κ₀) := rfl
  have hθ'1 : θ' < 1 := by
    rcases le_total θ 0 with h | h
    · rw [hθ'def, max_eq_right h]; norm_num
    · rw [hθ'def, max_eq_left h]; exact lt_of_lt_of_le hθ (by rw [hthD]; exact min_le_left _ _)
  have hθ'γ₀ : θ' < (2 - κ₀) / κ₀ := by
    have hγ0 : 0 < (2 - κ₀) / κ₀ := by
      apply div_pos _ hκ₀pos
      rw [hκ₀def]
      have : 4 / αp > 12 / 5 := by rw [gt_iff_lt, lt_div_iff₀ hαpos]; linarith
      linarith
    rcases le_total θ 0 with h | h
    · rw [hθ'def, max_eq_right h]; exact hγ0
    · rw [hθ'def, max_eq_left h]; exact lt_of_lt_of_le hθ (by rw [hthD]; exact min_le_right _ _)
  have h1θ : 0 < 1 + θ' := by linarith
  have hκ₀lt : κ₀ < 2 / (1 + θ') := by
    rw [lt_div_iff₀ h1θ]
    have := (lt_div_iff₀ hκ₀pos).mp hθ'γ₀
    nlinarith
  set e'' := (2 / (1 + θ') - κ₀) / 2 with he''def
  have he'' : 0 < e'' := by rw [he''def]; linarith
  set κ' := kappaD1p αp e'' with hκ'def
  have hκ' : κ' = κ₀ + e'' := by rw [hκ'def, hκ₀def]; unfold kappaD1p; ring
  have hκ'pos : 0 < κ' := by rw [hκ']; linarith
  have hκ'lt : κ' * (1 + θ') < 2 := by
    have : κ' < 2 / (1 + θ') := by rw [hκ', he''def]; linarith
    rwa [lt_div_iff₀ h1θ] at this
  set γ := (2 - κ') / κ' with hγdef
  have hγθ : θ' < γ := by
    rw [hγdef, lt_div_iff₀ hκ'pos]; nlinarith
  set g := 2 * max (κ' - 1) 0 / κ' with hgdef
  have hg0 : 0 ≤ g := by rw [hgdef]; positivity
  have hgθ : g < 1 - θ' := by
    rcases le_total (κ' - 1) 0 with h | h
    · rw [hgdef, max_eq_right h]; simp; linarith
    · rw [hgdef, max_eq_left h, div_lt_iff₀ hκ'pos]; nlinarith
  set c1 := (1 + 1 / κ') ^ 2 with hc1def
  have hc1 : 1 ≤ c1 := by
    rw [hc1def]; apply one_le_pow₀; have : 0 ≤ 1 / κ' := by positivity
    linarith
  -- the nodes
  obtain ⟨Ca, hCa, hZa⟩ := Z6a_zero_sums A 3 hA le_rfl
  obtain ⟨Cd, c, hCd, hc, hZd⟩ := Z6d_counts_corr hD αp hα1 hα2 r0 ε0 hr0 hε0 B hB e'' he'' 3 le_rfl
  refine ⟨(B + 2) * (2 * Ca * (Cd ^ 2 + 2 * Cd) + Ca), by positivity, ?_⟩
  have hb1 : 0 < 1 - g - θ' := by linarith
  have hb2 : 0 < γ - θ' := by linarith
  filter_upwards [hZd, L12_log_eventually_ge 3, L12_loglog_eventually_ge 1,
    L12_ev_rpow_exp (r0 + ε0) 1 1 one_pos one_pos, L12_ev_rpow_exp B 1 1 one_pos one_pos,
    L12_ev_rpow_exp (6 + B) 1 (1 / Real.exp 1) one_pos (by positivity),
    L12_ev_loglog 4 (1 - g - θ') (1 / c1) hb1 (by positivity),
    L12_ev_loglog 2 (γ - θ') 1 hb2 one_pos, L12_ev_loglog 1 1 (κ' / 5) one_pos (by linarith)]
    with Qn hd hL hℓ1 eT eK eR F1 F2 F3
  intro K ε s₀ hR
  have hRd := hd K ε s₀ hR
  obtain ⟨hK2, hKle, hεge, hεle, hsge, hsle⟩ := hR
  have hQpos : (0 : ℝ) < Qn := by
    rcases Nat.eq_zero_or_pos Qn with h | h
    · exfalso; rw [h, Nat.cast_zero, Real.log_zero] at hL; norm_num at hL
    · exact_mod_cast h
  set L := Real.log (Qn : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hQexp : Real.exp L = Qn := Real.exp_log hQpos
  set ℓ := Real.log L with hℓdef
  have hℓpos : 0 < ℓ := by linarith
  have hLℓ : Real.exp ℓ = L := Real.exp_log hLpos
  set P := L ^ B with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hLpos B
  have hεpos : 0 < ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hLpos _) hεge
  have hεinv : 1 / ε ≤ P := by
    rw [one_div_le hεpos hP, one_div, ← Real.rpow_neg hLpos.le]; exact hεge
  have hKpos : 0 < K := by linarith
  set T := L ^ (r0 + ε0) with hTdef
  have hTtw : twin (Qn : ℝ) r0 ε0 = T := rfl
  rw [hTtw]
  rw [hTtw] at hRd
  have ha1 : 1 ≤ r0 + ε0 := by linarith
  have hLT : L ≤ T := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le (by linarith) ha1
  have hT2 : 2 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hTq : T ≤ Real.exp L := by
    have := L12_le_of_mul_exp _ _ _ _ eT
    simpa using this
  have hsL : L ≤ s₀ := by linarith
  have hs0 : 0 < s₀ := by linarith
  have hs3 : 3 ≤ s₀ := by linarith
  have hαL : αp * L ≤ 2 * L := mul_le_mul_of_nonneg_right (by linarith) hLpos.le
  have hs2 : s₀ ≤ 2 * L := by linarith
  have hTN : T ≤ Real.exp s₀ := le_trans hTq (Real.exp_le_exp.mpr hsL)
  have hQ3 : (3 : ℝ) ≤ Qn := by
    rw [← hQexp]
    have : (3 : ℝ) ≤ 1 + L := by linarith
    exact le_trans this (by have := Real.add_one_le_exp L; linarith)
  have hPq : P ≤ Real.exp L := by
    have := L12_le_of_mul_exp _ _ _ _ eK
    simpa using this
  have hKQ : K ≤ Qn := by rw [← hQexp]; linarith
  -- R₁ ≤ N₀
  have hR1 : (R1S (Qn : ℝ) ε s₀ : ℝ) ≤ Real.exp s₀ := by
    have hU0 : 0 ≤ Real.exp (s₀ + 1) * L ^ 6 / (ε * Qn) := by positivity
    have hRU : (R1S (Qn : ℝ) ε s₀ : ℝ) ≤ Real.exp (s₀ + 1) * L ^ 6 / (ε * Qn) := Nat.floor_le hU0
    have hU : Real.exp (s₀ + 1) * L ^ 6 / (ε * Qn)
        = Real.exp 1 * L ^ 6 * (1 / ε) * Real.exp (-L) * Real.exp s₀ := by
      have e1 : Real.exp (s₀ + 1) = Real.exp 1 * Real.exp (-L) * Real.exp s₀ * Real.exp L := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [e1, ← hQexp]
      field_simp
    have hsplit : L ^ (6 + B) = L ^ 6 * P := by
      rw [Real.rpow_add hLpos, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have eR' := L12_le_of_mul_exp _ _ _ _ eR
    rw [hsplit] at eR'
    have hmul : Real.exp 1 * (L ^ 6 * P * Real.exp (-1 * L)) ≤ Real.exp 1 * (1 / Real.exp 1) := by
      gcongr
      have := mul_le_mul_of_nonneg_right eR' (Real.exp_pos (-1 * L)).le
      calc L ^ 6 * P * Real.exp (-1 * L) ≤ 1 / Real.exp 1 * Real.exp (1 * L) * Real.exp (-1 * L) := by
            gcongr
        _ = 1 / Real.exp 1 := by
            rw [mul_assoc, ← Real.exp_add, show 1 * L + -1 * L = 0 by ring, Real.exp_zero, mul_one]
    have hmul' : Real.exp 1 * L ^ 6 * (1 / ε) * Real.exp (-L) ≤ 1 := by
      have h1 : Real.exp 1 * (1 / Real.exp 1) = 1 := by field_simp
      calc Real.exp 1 * L ^ 6 * (1 / ε) * Real.exp (-L) ≤ Real.exp 1 * L ^ 6 * P * Real.exp (-L) := by
            gcongr
        _ = Real.exp 1 * (L ^ 6 * P * Real.exp (-1 * L)) := by ring_nf
        _ ≤ Real.exp 1 * (1 / Real.exp 1) := hmul
        _ = 1 := h1
    calc (R1S (Qn : ℝ) ε s₀ : ℝ) ≤ _ := hRU
      _ = Real.exp 1 * L ^ 6 * (1 / ε) * Real.exp (-L) * Real.exp s₀ := hU
      _ ≤ 1 * Real.exp s₀ := by gcongr
      _ = Real.exp s₀ := one_mul _
  -- X₀
  set X₀ := ℓ / κ' with hX₀def
  have hX₀ : 0 ≤ X₀ := by positivity
  obtain ⟨-, -, hz⟩ := hZa Qn T K ε s₀ X₀ hQ3 hT2 hTN (by linarith) hKQ hs3 hR1 hX₀
  have h5 : 5 * X₀ ≤ s₀ := by
    have F3' := L12_le_of_mul_exp _ _ _ _ F3
    rw [Real.rpow_one, one_mul, hLℓ] at F3'
    rw [hX₀def, show 5 * (ℓ / κ') = 5 * ℓ / κ' by ring, div_le_iff₀ hκ'pos]
    have := mul_le_mul_of_nonneg_left hsL hκ'pos.le
    linarith
  obtain ⟨hrest, hnear'⟩ := hRd X₀ hX₀
  have hnear := hnear' h5
  set Z := zeroPairSum Qn T K ε s₀ A 3 with hZdef
  set nr := nearSum Qn T K ε s₀ 3 X₀ with hnrdef
  set rs := restSq Qn T K ε s₀ 3 X₀ with hrsdef
  have hnr0 : 0 ≤ nr := L12_nearSum_nonneg _ _ _ _ _ _ _ hQpos.le hKpos.le
  -- the pieces
  have hγX : (2 - κ') * X₀ = γ * ℓ := by rw [hX₀def, hγdef]; field_simp
  have hgX : 2 * (max (κ' - 1) 0 * X₀) = g * ℓ := by rw [hX₀def, hgdef]; field_simp
  have h1X : 1 + X₀ ≤ (1 + 1 / κ') * ℓ := by
    rw [hX₀def]
    have : ℓ / κ' = 1 / κ' * ℓ := by ring
    rw [this]
    have h2 : (1 + 1 / κ') * ℓ = ℓ + 1 / κ' * ℓ := by ring
    rw [h2]; linarith
  have hnear2 : nr ^ 2 ≤ Cd ^ 2 * (c1 * ℓ ^ 2 * Real.exp (g * ℓ)) := by
    have h0 : 0 ≤ Cd * (1 + X₀) * Real.exp (max (κ' - 1) 0 * X₀) := by positivity
    calc nr ^ 2 ≤ (Cd * (1 + X₀) * Real.exp (max (κ' - 1) 0 * X₀)) ^ 2 := by gcongr
      _ = Cd ^ 2 * ((1 + X₀) ^ 2 * Real.exp (2 * (max (κ' - 1) 0 * X₀))) := by
          rw [show 2 * (max (κ' - 1) 0 * X₀) = ((2 : ℕ) : ℝ) * (max (κ' - 1) 0 * X₀) by norm_num,
            Real.exp_nat_mul]; ring
      _ ≤ Cd ^ 2 * (((1 + 1 / κ') * ℓ) ^ 2 * Real.exp (2 * (max (κ' - 1) 0 * X₀))) := by
          gcongr
      _ = Cd ^ 2 * (c1 * ℓ ^ 2 * Real.exp (g * ℓ)) := by rw [hgX, hc1def]; ring
  have hrest' : s₀ * rs ≤ Cd * (1 + s₀ * Real.exp (-(γ * ℓ))) := by
    have hpow : Real.exp s₀ ^ (-c) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_exp hs0.le) (by linarith)
    calc s₀ * rs ≤ Cd * (Real.exp s₀ ^ (-c) + s₀ * Real.exp (-((2 - κ') * X₀))) := hrest
      _ ≤ Cd * (1 + s₀ * Real.exp (-((2 - κ') * X₀))) := by gcongr
      _ = Cd * (1 + s₀ * Real.exp (-(γ * ℓ))) := by rw [hγX]
  have hlogs : Real.log s₀ ≤ 2 * ℓ := by
    have h1 : s₀ ≤ L ^ 2 := by
      have : 2 * L ≤ L * L := mul_le_mul_of_nonneg_right (by linarith) hLpos.le
      rw [sq]; linarith
    have h2 : Real.log s₀ ≤ Real.log (L ^ 2) := Real.log_le_log hs0 h1
    rw [Real.log_pow] at h2; push_cast at h2; linarith
  have hlogs0 : 0 ≤ Real.log s₀ := Real.log_nonneg (by linarith)
  have hZb : Z ≤ Ca * (2 * ℓ) * (Cd ^ 2 * (c1 * ℓ ^ 2 * Real.exp (g * ℓ)) + Cd * (1 + s₀ * Real.exp (-(γ * ℓ))))
      + Ca := by
    have hcs : Ca / Real.exp s₀ ≤ Ca := div_le_self hCa (Real.one_le_exp hs0.le)
    calc Z ≤ Ca * Real.log s₀ * (nr ^ 2 + s₀ * rs) + Ca / Real.exp s₀ := hz
      _ ≤ Ca * (2 * ℓ) * (Cd ^ 2 * (c1 * ℓ ^ 2 * Real.exp (g * ℓ)) + Cd * (1 + s₀ * Real.exp (-(γ * ℓ))))
          + Ca := by
        have hB0 : 0 ≤ Cd ^ 2 * (c1 * ℓ ^ 2 * Real.exp (g * ℓ)) + Cd * (1 + s₀ * Real.exp (-(γ * ℓ))) := by
          positivity
        have := add_le_add hnear2 hrest'
        have hX0 : 0 ≤ nr ^ 2 + s₀ * rs :=
          add_nonneg (sq_nonneg _) (mul_nonneg hs0.le (L12_restSq_nonneg _ _ _ _ _ _ _))
        gcongr
  -- the saving
  set W := Real.exp (-(θ' * ℓ)) * s₀ with hWdef
  have hP1 : c1 * ℓ ^ 4 * Real.exp (g * ℓ) ≤ W := by
    have F1' := L12_le_of_mul_exp _ _ _ _ F1
    have h4 : ℓ ^ (4 : ℝ) = ℓ ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h4] at F1'
    calc c1 * ℓ ^ 4 * Real.exp (g * ℓ) ≤ c1 * (1 / c1 * Real.exp ((1 - g - θ') * ℓ)) * Real.exp (g * ℓ) := by
          gcongr
      _ = Real.exp (-(θ' * ℓ)) * Real.exp ℓ := by
          rw [← Real.exp_add, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul, mul_comm,
            ← Real.exp_add]; ring_nf
      _ ≤ W := by rw [hWdef, hLℓ]; gcongr
  have hl2 : ℓ ^ 2 ≤ c1 * ℓ ^ 4 * Real.exp (g * ℓ) := by
    have e1 : 1 ≤ Real.exp (g * ℓ) := Real.one_le_exp (by positivity)
    have e2 : ℓ ^ 2 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
    calc ℓ ^ 2 = 1 * ℓ ^ 2 * 1 := by ring
      _ ≤ c1 * ℓ ^ 4 * Real.exp (g * ℓ) := by gcongr
  have hl1 : ℓ ≤ ℓ ^ 2 := le_self_pow₀ hℓ1 (by norm_num)
  have hP3 : ℓ ^ 2 * (s₀ * Real.exp (-(γ * ℓ))) ≤ W := by
    have F2' := L12_le_of_mul_exp _ _ _ _ F2
    have h2 : ℓ ^ (2 : ℝ) = ℓ ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2] at F2'
    calc ℓ ^ 2 * (s₀ * Real.exp (-(γ * ℓ))) ≤ (1 * Real.exp ((γ - θ') * ℓ)) * (s₀ * Real.exp (-(γ * ℓ))) := by
          gcongr
      _ = W := by
          rw [hWdef, one_mul, mul_comm s₀, ← mul_assoc, ← Real.exp_add]; ring_nf
  have hW0 : 0 ≤ W := by positivity
  -- log K + 2 ≤ (B + 2) ℓ
  have hlogK : Real.log K + 2 ≤ (B + 2) * ℓ := by
    have h1 : Real.log K ≤ Real.log P := Real.log_le_log hKpos hKle
    have h2 : Real.log P = B * ℓ := Real.log_rpow hLpos B
    have h6 : (B + 2) * ℓ = B * ℓ + 2 * ℓ := by ring
    linarith
  have hlogK0 : 0 ≤ Real.log K + 2 := by
    have : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    linarith
  have hmainZ : (Real.log K + 2) * Z ≤ (B + 2) * (2 * Ca * (Cd ^ 2 + 2 * Cd) + Ca) * W := by
    have hbd0 : 0 ≤ Ca * (2 * ℓ) * (Cd ^ 2 * (c1 * ℓ ^ 2 * Real.exp (g * ℓ))
        + Cd * (1 + s₀ * Real.exp (-(γ * ℓ)))) + Ca := by positivity
    calc (Real.log K + 2) * Z
        ≤ ((B + 2) * ℓ) * (Ca * (2 * ℓ) * (Cd ^ 2 * (c1 * ℓ ^ 2 * Real.exp (g * ℓ))
            + Cd * (1 + s₀ * Real.exp (-(γ * ℓ)))) + Ca) := by
          calc (Real.log K + 2) * Z ≤ (Real.log K + 2) * (Ca * (2 * ℓ) * (Cd ^ 2 * (c1 * ℓ ^ 2 * Real.exp (g * ℓ))
            + Cd * (1 + s₀ * Real.exp (-(γ * ℓ)))) + Ca) := mul_le_mul_of_nonneg_left hZb hlogK0
            _ ≤ _ := mul_le_mul_of_nonneg_right hlogK hbd0
      _ = (B + 2) * (2 * Ca * Cd ^ 2 * (c1 * ℓ ^ 4 * Real.exp (g * ℓ)) + 2 * Ca * Cd * ℓ ^ 2
            + 2 * Ca * Cd * (ℓ ^ 2 * (s₀ * Real.exp (-(γ * ℓ)))) + Ca * ℓ) := by ring
      _ ≤ (B + 2) * (2 * Ca * Cd ^ 2 * W + 2 * Ca * Cd * W + 2 * Ca * Cd * W + Ca * W) := by
          have hB2 : 0 ≤ B + 2 := by linarith
          have hCaCd2 : 0 ≤ 2 * Ca * Cd ^ 2 := by positivity
          have hCaCd : 0 ≤ 2 * Ca * Cd := by positivity
          refine mul_le_mul_of_nonneg_left ?_ hB2
          refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
          · exact mul_le_mul_of_nonneg_left hP1 hCaCd2
          · exact mul_le_mul_of_nonneg_left (hl2.trans hP1) hCaCd
          · exact mul_le_mul_of_nonneg_left hP3 hCaCd
          · exact mul_le_mul_of_nonneg_left (hl1.trans (hl2.trans hP1)) hCa
      _ = (B + 2) * (2 * Ca * (Cd ^ 2 + 2 * Cd) + Ca) * W := by ring
  have hrate : Real.exp (-(θ' * ℓ)) ≤ L ^ (-θ) := by
    rw [Real.rpow_def_of_pos hLpos]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hθθ' hℓpos.le
    linarith
  calc (Real.log K + 2) * (T * Z) = T * ((Real.log K + 2) * Z) := by ring
    _ ≤ T * ((B + 2) * (2 * Ca * (Cd ^ 2 + 2 * Cd) + Ca) * W) := by gcongr
    _ = (B + 2) * (2 * Ca * (Cd ^ 2 + 2 * Cd) + Ca) * Real.exp (-(θ' * ℓ)) * (T * s₀) := by
        rw [hWdef]; ring
    _ ≤ (B + 2) * (2 * Ca * (Cd ^ 2 + 2 * Cd) + Ca) * L ^ (-θ) * (T * s₀) := by gcongr

end ShellS
end ZetaShell
