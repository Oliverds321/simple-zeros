/-
L7_12 (28 Sep 2026): PROOF of node S3 (L7_10's `L10_S3`, statement byte-identical).
Node S3 (L7_10): **Lemma 5c(3) with the Weil-form error `E′`** (lem:shell-5c (3)), in the form Theorem S consumes.
Proof: L7_5's `family_EW_sum` (`Σ r E′ ≤ C₀ T⁴K²(log N₀)³(R₁²/N₀ + N₀/Q² + 1/Q² + R₁/(QN₀))`) with the actual
`R₁ ≤ e^{s₀+1}(log Q)⁶/(εQ)`, `1/ε ≤ (log Q)^B`, `K ≤ (log Q)^B`, `N₀ = e^{s₀} ≤ Q^{α′}`; every bracket term is
`≤ e²(log Q)^{12}P²·Q^{α′−2}` (`P = (log Q)^B`), and `(log Q)^M Q^{α′−2} → 0` for every fixed `M`.
-/
import ZetaShell.ShellS.L10_Defs
import ZetaShell.PropZ.Z5c_FamilyErrorsW
import ZetaShell.ShellS.L12_Aux

noncomputable section

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem S3_family_errors (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 2) (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0)
    (B θ : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      (Real.log K + 2) * famErrSum Qn (twin Qn r0 ε0) K ε s₀
        ≤ C * Real.log Qn ^ (-θ) * (twin Qn r0 ε0 * s₀) := by
  obtain ⟨C0, hC0⟩ := family_EW_sum
  have ha1 : 1 ≤ r0 + ε0 := by linarith
  have hb0 : 0 < 2 - αp := by linarith
  set C1 := max C0 1 with hC1
  have hC1pos : 0 < C1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨32 * Real.exp 1 ^ 2 * (B + 2) * C1, by positivity, ?_⟩
  filter_upwards [L12_log_eventually_ge 3, L12_ev_rpow_exp (r0 + ε0) 1 1 one_pos one_pos,
    L12_ev_rpow_exp (6 + 2 * B) (2 - αp) (1 / (2 * Real.exp 1)) hb0 (by positivity),
    L12_ev_rpow_exp (3 * (r0 + ε0) + 4 * B + 15 + θ) (2 - αp) 1 hb0 one_pos] with Qn hL e2 e3 e4
  intro K ε s₀ hR
  obtain ⟨hK2, hKle, hεge, hεle, hsge, hsle⟩ := hR
  have hQpos : (0 : ℝ) < Qn := by
    rcases Nat.eq_zero_or_pos Qn with h | h
    · exfalso; rw [h, Nat.cast_zero, Real.log_zero] at hL; norm_num at hL
    · exact_mod_cast h
  set L := Real.log (Qn : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hQexp : Real.exp L = Qn := Real.exp_log hQpos
  set P := L ^ B with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hLpos B
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) (by linarith)
  have hεpos : 0 < ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hLpos _) hεge
  have hεinv : 1 / ε ≤ P := by
    rw [one_div_le hεpos hP, one_div, ← Real.rpow_neg hLpos.le]; exact hεge
  have hKpos : 0 < K := by linarith
  set T := L ^ (r0 + ε0) with hTdef
  have hTtw : twin (Qn : ℝ) r0 ε0 = T := rfl
  rw [hTtw]
  have hLT : L ≤ T := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le (by linarith) ha1
  have hT2 : 2 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hTq : T ≤ Real.exp L := by
    have := L12_le_of_mul_exp _ _ _ _ e2
    simpa using this
  have hsL : L ≤ s₀ := by linarith
  have hs0 : 0 < s₀ := by linarith
  have hαL : αp * L ≤ 2 * L := mul_le_mul_of_nonneg_right hα2.le hLpos.le
  have hαL0 : 0 ≤ αp * L := by positivity
  have hs2 : s₀ ≤ 2 * L := by linarith
  have hTN : T ≤ Real.exp s₀ := le_trans hTq (Real.exp_le_exp.mpr hsL)
  have hN : Real.exp 3 * Qn ≤ Real.exp s₀ := by
    rw [← hQexp, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hQ1 : (1 : ℝ) ≤ Qn := by rw [← hQexp]; exact Real.one_le_exp (by linarith)
  -- the size of R₁
  set U := Real.exp (s₀ + 1) * L ^ 6 / (ε * Qn) with hUdef
  have hU0 : 0 ≤ U := by positivity
  set R := (R1S (Qn : ℝ) ε s₀ : ℝ) with hRdef
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hRU : R ≤ U := Nat.floor_le hU0
  have hU : U = Real.exp 1 * L ^ 6 * (1 / ε) * Real.exp (s₀ - L) := by
    have e1 : Real.exp (s₀ + 1) = Real.exp 1 * Real.exp (s₀ - L) * Real.exp L := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [hUdef, e1, ← hQexp]
    field_simp
  set x := Real.exp 1 * L ^ 6 * P with hxdef
  have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ (by linarith)
  have hx1 : 1 ≤ x := by
    have : 1 * 1 * 1 ≤ Real.exp 1 * L ^ 6 * P := by gcongr
    simpa using this
  have hU2 : U ≤ x * Real.exp (s₀ - L) := by
    rw [hU, hxdef]; gcongr
  set G := Real.exp (-(2 - αp) * L) with hGdef
  have hG0 : 0 < G := Real.exp_pos _
  have hsG : Real.exp (s₀ - 2 * L) ≤ G := Real.exp_le_exp.mpr (by ring_nf; linarith)
  have h2G : Real.exp (-2 * L) ≤ G := Real.exp_le_exp.mpr (by ring_nf; linarith)
  -- R₁ ≤ Q/(2K)
  have hRQ : R ≤ Qn / (2 * K) := by
    have e3' := L12_le_of_mul_exp _ _ _ _ e3
    -- L^(6+2B) = L^6 * P^2
    have hsplit : L ^ (6 + 2 * B) = L ^ 6 * P ^ 2 := by
      rw [Real.rpow_add hLpos, show (2 : ℝ) * B = B * ((2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul_natCast hLpos.le]
      norm_cast
    rw [hsplit] at e3'
    -- x * exp(s₀ - L) ≤ Q/(2P) ≤ Q/(2K)
    have key : x * Real.exp (s₀ - L) ≤ Qn / (2 * P) := by
      rw [le_div_iff₀ (by positivity), ← hQexp]
      have hexp : Real.exp (s₀ - L) * Real.exp ((2 - αp) * L) ≤ Real.exp L := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by ring_nf; linarith)
      calc x * Real.exp (s₀ - L) * (2 * P)
          = (2 * Real.exp 1) * (L ^ 6 * P ^ 2) * Real.exp (s₀ - L) := by rw [hxdef]; ring
        _ ≤ (2 * Real.exp 1) * (1 / (2 * Real.exp 1) * Real.exp ((2 - αp) * L)) * Real.exp (s₀ - L) := by
            gcongr
        _ = Real.exp (s₀ - L) * Real.exp ((2 - αp) * L) := by field_simp
        _ ≤ Real.exp L := hexp
    calc R ≤ U := hRU
      _ ≤ x * Real.exp (s₀ - L) := hU2
      _ ≤ Qn / (2 * P) := key
      _ ≤ Qn / (2 * K) := by gcongr
  have hmain := hC0 (Qn : ℝ) K T (Real.exp s₀) (R1S (Qn : ℝ) ε s₀) hQ1 (by linarith) hT2 hTN hN hRQ
  rw [Real.log_exp] at hmain
  -- the bracket
  set Br := R ^ 2 / Real.exp s₀ + Real.exp s₀ / (Qn : ℝ) ^ 2 + 1 / (Qn : ℝ) ^ 2 + R / (Qn * Real.exp s₀)
    with hBrdef
  have hBr0 : 0 ≤ Br := by positivity
  have hBr : Br ≤ 4 * x ^ 2 * G := by
    have t1 : R ^ 2 / Real.exp s₀ ≤ x ^ 2 * G := by
      rw [div_le_iff₀ (Real.exp_pos _)]
      calc R ^ 2 ≤ (x * Real.exp (s₀ - L)) ^ 2 := by gcongr; exact le_trans hRU hU2
        _ = x ^ 2 * Real.exp (s₀ - 2 * L) * Real.exp s₀ := by
            rw [mul_pow, mul_assoc, ← Real.exp_add, ← Real.exp_nat_mul]; ring_nf
        _ ≤ x ^ 2 * G * Real.exp s₀ := by gcongr
    have t2 : Real.exp s₀ / (Qn : ℝ) ^ 2 ≤ G := by
      rw [← hQexp, ← Real.exp_nat_mul, ← Real.exp_sub]
      calc Real.exp (s₀ - ((2 : ℕ) : ℝ) * L) = Real.exp (s₀ - 2 * L) := by norm_num
        _ ≤ G := hsG
    have t3 : 1 / (Qn : ℝ) ^ 2 ≤ G := by
      rw [← hQexp, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]
      calc Real.exp (-(((2 : ℕ) : ℝ) * L)) = Real.exp (-2 * L) := by ring_nf
        _ ≤ G := h2G
    have t4 : R / (Qn * Real.exp s₀) ≤ x * G := by
      rw [div_le_iff₀ (by positivity), ← hQexp]
      calc R ≤ x * Real.exp (s₀ - L) := le_trans hRU hU2
        _ = x * Real.exp (-2 * L) * (Real.exp L * Real.exp s₀) := by
            have hE : Real.exp (s₀ - L) = Real.exp (-2 * L) * (Real.exp L * Real.exp s₀) := by
              rw [← Real.exp_add, ← Real.exp_add]; ring_nf
            rw [hE]; ring
        _ ≤ x * G * (Real.exp L * Real.exp s₀) := by gcongr
    have hxx : x ≤ x ^ 2 := le_self_pow₀ hx1 (by norm_num)
    have h1x : 1 ≤ x ^ 2 := one_le_pow₀ hx1
    calc Br ≤ x ^ 2 * G + G + G + x * G := by rw [hBrdef]; linarith
      _ = (x ^ 2 + 1 + 1 + x) * G := by ring
      _ ≤ (x ^ 2 + x ^ 2 + x ^ 2 + x ^ 2) * G := by gcongr
      _ = 4 * x ^ 2 * G := by ring
  -- log K + 2 ≤ (B + 2) L
  have hlogK : Real.log K + 2 ≤ (B + 2) * L := by
    have h1 : Real.log K ≤ Real.log P := Real.log_le_log hKpos hKle
    have h2 : Real.log P = B * Real.log L := Real.log_rpow hLpos B
    have h3 : Real.log L ≤ L := le_trans (Real.log_le_sub_one_of_pos hLpos) (by linarith)
    have h4 : B * Real.log L ≤ B * L := mul_le_mul_of_nonneg_left h3 (by linarith)
    have h5 : 2 ≤ 2 * L := by linarith
    have h6 : (B + 2) * L = B * L + 2 * L := by ring
    linarith
  have hlogK0 : 0 ≤ Real.log K + 2 := by
    have : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    linarith
  -- the saving
  have hsave : T ^ 3 * P ^ 4 * L ^ 15 * G ≤ L ^ (-θ) := by
    have hsp : L ^ (3 * (r0 + ε0) + 4 * B + 15 + θ) = T ^ 3 * P ^ 4 * L ^ 15 * L ^ θ := by
      rw [Real.rpow_add hLpos, Real.rpow_add hLpos, Real.rpow_add hLpos,
        show 3 * (r0 + ε0) = (r0 + ε0) * ((3 : ℕ) : ℝ) by push_cast; ring,
        show 4 * B = B * ((4 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul_natCast hLpos.le, Real.rpow_mul_natCast hLpos.le,
        show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hsp] at e4
    rw [Real.rpow_neg hLpos.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hLpos θ)]
    calc T ^ 3 * P ^ 4 * L ^ 15 * G * L ^ θ = T ^ 3 * P ^ 4 * L ^ 15 * L ^ θ * Real.exp (-(2 - αp) * L) := by
          rw [hGdef]; ring
      _ ≤ 1 := e4
  -- assembly
  have hC0le : C0 ≤ C1 := le_max_left _ _
  have hX0 : 0 ≤ T ^ 4 * K ^ 2 * s₀ ^ 3 * Br := by positivity
  unfold famErrSum
  calc (Real.log K + 2) * ∑ r ∈ Finset.Icc 1 (R1S (Qn : ℝ) ε s₀), (r : ℝ) * EerrW T (Real.exp s₀) r (K / (r * Qn))
      ≤ (Real.log K + 2) * (C0 * T ^ 4 * K ^ 2 * s₀ ^ 3 * Br) := by
        gcongr
    _ = (Real.log K + 2) * (C0 * (T ^ 4 * K ^ 2 * s₀ ^ 3 * Br)) := by ring
    _ ≤ (Real.log K + 2) * (C1 * (T ^ 4 * K ^ 2 * s₀ ^ 3 * Br)) := by gcongr
    _ ≤ ((B + 2) * L) * (C1 * (T ^ 4 * P ^ 2 * (2 * L) ^ 3 * (4 * x ^ 2 * G))) := by
        gcongr
    _ = 32 * Real.exp 1 ^ 2 * (B + 2) * C1 * (T ^ 3 * P ^ 4 * L ^ 15 * G) * (T * L) := by
        rw [hxdef]; ring
    _ ≤ 32 * Real.exp 1 ^ 2 * (B + 2) * C1 * L ^ (-θ) * (T * s₀) := by
        gcongr

end ShellS
end ZetaShell
