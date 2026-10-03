/-
L7_9 round 2, sub-node K6c′ of `principal_arc_mass` (K6): the PNT step (lem:K-P Step 3), in the form that the
summation-by-parts Step 2′ (`sbp_L2`, sub-node K6b′) consumes.
With `c_n = (Λ′(n) − 1)w̃(n)` (supported in `[N/e, eN]`, `N = e^s`), `M = ⌊e^{s+1}⌋` and `C₀(n) = Σ_{m≤n} c_m`:
`2Δ(|C₀(M)| + 2πΔΣ_{n<M}|C₀(n)|)² ≤ C·U/(log Q)²`.
Route: Abel summation with `E(y) = Σ_{m≤y}(Λ′(m) − 1) = ψ(y) − ⌊y⌋ − Σ_{p^k≤y, p≤R₀} log p` gives
`|C₀(n)| ≤ E*(|w̃(n)| + Σ_m|w̃(m+1) − w̃(m)|) ≲ E*T²/√N` (`|D_T′| ≤ 1.5T²`), hence the left side is
`≲ ℒ³T⁷(E*/N)²`; `E*/N ≤ |ψ − id|/N + log(eN)/(QTℒ)` and `ψ(y) − y = o(y(log y)^{−A})` for a fixed `A`
(`A = 3 + 3(r+ε)` suffices; `L7_2.psi_sub_id_isLittleO_log_rpow`, imported) give `O(U/(log Q)²)`.
-/
import ZetaShell.LemmaK.LK9_K6_Defs
import ZetaShell.PNT.PNTMedium
import ZetaShell.LemmaK.LK9_K6c2_Var
import ZetaShell.LemmaK.LK9_K6c3_PNT
import ZetaShell.LemmaK.LK9_K6c4_Assembly

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

set_option maxHeartbeats 1000000 in
/-- **K6c′ (the PNT step).** -/
theorem pnt_step (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      2 * (ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)) * (‖K6.psum ⌊Real.exp (s + 1)⌋₊ (fun n => K6.asmooth (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s) n - K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s n)‖
          + 2 * Real.pi * (ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)) * ∑ n ∈ Finset.range ⌊Real.exp (s + 1)⌋₊, ‖K6.psum n (fun n => K6.asmooth (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s) n - K6.wmod (ZetaQ.Twin (Qn : ℝ) r ε) s n)‖) ^ 2
        ≤ C * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi)) / Real.log (Qn : ℝ) ^ 2 := by
  obtain ⟨K, hK0, hKv⟩ := wmod_var
  have hEv := E_bound lam r ε hlam1 hlam2 hr hε
  have hre : 3 ≤ r + ε := by linarith
  refine ⟨1024 * Real.pi ^ 3 * Real.exp 1 ^ 4 * K ^ 2, ?_⟩
  have E1 : ∀ᶠ Qn : ℕ in atTop, (100 : ℝ) ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 100)
  have E2 : ∀ᶠ Qn : ℕ in atTop, (4 : ℝ) ≤ Real.log (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 4)
  have E3 : ∀ᶠ Qn : ℕ in atTop, Real.log (Qn : ℝ) ^ (r + ε) ≤ (Qn : ℝ) := by
    have hO := (isLittleO_log_rpow_rpow_atTop (r + ε) (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1)
    have h' : ∀ᶠ y : ℝ in atTop, Real.log y ^ (r + ε) ≤ y := by
      filter_upwards [hO, eventually_ge_atTop (1 : ℝ)] with y hy hy1
      have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _), Real.rpow_one,
        Real.norm_of_nonneg (by linarith), one_mul] at hy
      exact hy
    exact tendsto_natCast_atTop_atTop.eventually h'
  filter_upwards [hEv, E1, E2, E3] with Qn hEQ h100 hlog hTQ s hs1 hs2
  set x := Real.log (Qn : ℝ) with hx
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  set L := Lc (Qn : ℝ) T with hL
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hT1 : 1 ≤ T := Real.one_le_rpow hx1 (by linarith)
  have hTQ' : T ≤ (Qn : ℝ) := hTQ
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  have he1 := Real.exp_one_lt_d9
  have he1' := Real.exp_one_gt_d9
  have hL1 : 1 ≤ L := by
    rw [hL, Lc]
    have hz0 : 0 < (Qn : ℝ) * T / (2 * Real.pi) := by positivity
    rw [Real.le_log_iff_exp_le hz0, le_div_iff₀ (by positivity)]
    nlinarith
  have hL2 : L ≤ 2 * x := by
    have h1 : (Qn : ℝ) * T / (2 * Real.pi) ≤ (Qn : ℝ) * (Qn : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hTQ' hQ0.le]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hQ0.ne' hQ0.ne'] at h2
    rw [hL, Lc]
    linarith
  have hQTL : 0 < (Qn : ℝ) * T * L := by positivity
  have hellx : x ≤ ellK (Qn : ℝ) T := by
    rw [ellK, ← hL]
    apply Real.log_le_log hQ0
    have hTL : 1 ≤ T * L := one_le_mul_of_one_le_of_one_le hT1 hL1
    calc (Qn : ℝ) = (Qn : ℝ) * 1 := (mul_one _).symm
      _ ≤ (Qn : ℝ) * (T * L) := mul_le_mul_of_nonneg_left hTL hQ0.le
      _ = (Qn : ℝ) * T * L := (mul_assoc _ _ _).symm
  have hs3 : 3 ≤ s := by linarith
  -- the three sub-nodes
  obtain ⟨hw, hv⟩ := hKv T s hT1 hs3
  set N := Real.exp s with hN
  set e₁ := Real.exp 1 with he₁
  have hN0 : 0 < N := Real.exp_pos _
  have hes1 : Real.exp (s + 1) = N * e₁ := by rw [hN, he₁, ← Real.exp_add]
  set E := x ^ (-(3 + 3 * (r + ε))) with hE
  have hE0 : 0 ≤ E := Real.rpow_nonneg (by linarith) _
  set Es := 2 * Real.exp (s + 1) * E with hEs
  set W := K * T ^ 2 * Real.exp (-(s / 2)) with hW
  have hEs0 : 0 ≤ Es := by positivity
  have hB := psum_c_bound T s (R0 (Qn : ℝ) T s) W Es (by linarith) hEs0 hw hv (hEQ s hs1 hs2)
  set M := ⌊Real.exp (s + 1)⌋₊ with hM
  set c : ℕ → ℂ := fun n => K6.asmooth T s (R0 (Qn : ℝ) T s) n - K6.wmod T s n with hc
  set Δ := T * L / (2 * N) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  set P := 2 * Es * W with hP
  have hW0 : 0 ≤ W := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hMle : (M : ℝ) ≤ N * e₁ := by rw [← hes1]; exact Nat.floor_le (Real.exp_pos _).le
  have hsum : ∑ n ∈ Finset.range M, ‖K6.psum n c‖ ≤ M * P := by
    calc ∑ n ∈ Finset.range M, ‖K6.psum n c‖ ≤ ∑ n ∈ Finset.range M, P :=
          Finset.sum_le_sum fun n hn => hB n (Finset.mem_range.mp hn).le
      _ = M * P := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hinner : ‖K6.psum M c‖ + 2 * Real.pi * Δ * ∑ n ∈ Finset.range M, ‖K6.psum n c‖
      ≤ P * (2 * Real.pi * e₁ * T * L) := by
    have h1 := hB M le_rfl
    have h2 : 2 * Real.pi * Δ * ∑ n ∈ Finset.range M, ‖K6.psum n c‖ ≤ 2 * Real.pi * Δ * (M * P) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h3 : 2 * Real.pi * Δ * (M : ℝ) ≤ Real.pi * e₁ * T * L := by
      have : 2 * Real.pi * Δ * (M : ℝ) ≤ 2 * Real.pi * Δ * (N * e₁) :=
        mul_le_mul_of_nonneg_left hMle (by positivity)
      have e : 2 * Real.pi * Δ * (N * e₁) = Real.pi * e₁ * T * L := by
        rw [hΔ]; field_simp
      linarith
    have h4 : 1 ≤ Real.pi * e₁ * T * L := by
      have hTL : 1 ≤ T * L := one_le_mul_of_one_le_of_one_le hT1 hL1
      have hpe : 1 ≤ Real.pi * e₁ := by nlinarith
      have e : Real.pi * e₁ * T * L = (Real.pi * e₁) * (T * L) := by ring
      rw [e]; exact one_le_mul_of_one_le_of_one_le hpe hTL
    have h5 : 2 * Real.pi * Δ * ((M : ℝ) * P) ≤ Real.pi * e₁ * T * L * P := by
      have := mul_le_mul_of_nonneg_right h3 hP0
      calc 2 * Real.pi * Δ * ((M : ℝ) * P) = 2 * Real.pi * Δ * (M : ℝ) * P := by ring
        _ ≤ _ := this
    have h6 : P ≤ Real.pi * e₁ * T * L * P := by
      have := mul_le_mul_of_nonneg_right h4 hP0
      linarith
    have e7 : P * (2 * Real.pi * e₁ * T * L) = 2 * (Real.pi * e₁ * T * L * P) := by ring
    rw [e7]
    linarith
  have hsq : (‖K6.psum M c‖ + 2 * Real.pi * Δ * ∑ n ∈ Finset.range M, ‖K6.psum n c‖) ^ 2
      ≤ (P * (2 * Real.pi * e₁ * T * L)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hinner 2
  -- 2ΔP² = 16K²e₁²T⁵LE²
  have hexp : Real.exp (-(s / 2)) ^ 2 * N = 1 := by
    rw [hN, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num; ring
  have h2DP : 2 * Δ * P ^ 2 = 16 * K ^ 2 * e₁ ^ 2 * T ^ 5 * L * E ^ 2 := by
    rw [hΔ, hP, hEs, hW, hes1]
    have : Real.exp (-(s / 2)) ^ 2 = 1 / N := by field_simp; linarith [hexp]
    field_simp
    rw [this]
    field_simp
    ring
  -- the key power count: T⁶L³E²x² ≤ 8
  have hkey : T ^ 6 * L ^ 3 * E ^ 2 * x ^ 2 ≤ 8 := by
    have hx0 : 0 < x := by linarith
    have hTE : T ^ 6 * E ^ 2 = (x ^ 6)⁻¹ := by
      rw [hT, ZetaQ.Twin, hE, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
        ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      rw [show (r + ε) * ((6 : ℕ) : ℝ) + -(3 + 3 * (r + ε)) * ((2 : ℕ) : ℝ) = -((6 : ℕ) : ℝ) by
        push_cast; ring, Real.rpow_neg hx0.le, Real.rpow_natCast]
    have hL3 : L ^ 3 ≤ 8 * x ^ 3 := by
      have := pow_le_pow_left₀ (by linarith) hL2 3
      nlinarith
    have hx6 : 0 < x ^ 6 := by positivity
    calc T ^ 6 * L ^ 3 * E ^ 2 * x ^ 2 = (T ^ 6 * E ^ 2) * L ^ 3 * x ^ 2 := by ring
      _ = L ^ 3 * x ^ 2 / x ^ 6 := by rw [hTE]; field_simp
      _ ≤ 8 * x ^ 3 * x ^ 2 / x ^ 6 := by
          apply div_le_div_of_nonneg_right _ hx6.le
          exact mul_le_mul_of_nonneg_right hL3 (by positivity)
      _ = 8 / x := by field_simp; try ring
      _ ≤ 8 := by rw [div_le_iff₀ hx0]; linarith
  have hx2 : 0 < x ^ 2 := by positivity
  calc 2 * Δ * (‖K6.psum M c‖ + 2 * Real.pi * Δ * ∑ n ∈ Finset.range M, ‖K6.psum n c‖) ^ 2
      ≤ 2 * Δ * (P * (2 * Real.pi * e₁ * T * L)) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (2 * Δ * P ^ 2) * (4 * Real.pi ^ 2 * e₁ ^ 2 * T ^ 2 * L ^ 2) := by ring
    _ = 64 * Real.pi ^ 2 * e₁ ^ 4 * K ^ 2 * T * (T ^ 6 * L ^ 3 * E ^ 2 * x ^ 2) / x ^ 2 := by
        rw [h2DP]; field_simp; ring
    _ ≤ 64 * Real.pi ^ 2 * e₁ ^ 4 * K ^ 2 * T * 8 / x ^ 2 := by
        apply div_le_div_of_nonneg_right _ hx2.le
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = 1024 * Real.pi ^ 3 * Real.exp 1 ^ 4 * K ^ 2 * (T / (2 * Real.pi)) / x ^ 2 := by
        rw [he₁]; field_simp; ring

end LemmaK
end ZetaShell
