/-
L7_12c (3 Oct 2026): Lemma 6d (lem:shell-6d), the size of the family on Theorem S's range:
`𝒵 = N₀^{2−2/α′+o(1)}` (sec_shell.tex l.676 and lem:shell-6d: "so `𝒵 = N₀^{2−2/α+o(1)}`"), in the form
`log 𝒵 ≤ (2 − 2/α′ + η) s₀` eventually, uniformly on `SRange α′ B`, with `T = (log Q)^{r₀+ε₀}`;
together with `1 ≤ R₁ ≤ N₀`, `T ≥ 1`.
Route: `R₁ ≤ e N₀ L⁶ P/Q`, `KN₀/Q ≤ P N₀/Q`, `N₀/Q ≤ N₀^{1−1/α′}` (`s₀ ≤ α′L`), `P = L^B ≥ 1/ε, K`, `L ≤ s₀`,
so `𝒵 ≤ 9(9e²+1) s₀^M N₀^{2−2/α′}` with `M = 12 + 2B + 2(r₀+ε₀)`.
-/
import ZetaShell.ShellS.L10_Defs
import ZetaShell.ShellS.L12_Aux

noncomputable section

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- `C x^M ≤ e^{ηx}` for large `x`. -/
lemma L12c_poly_le_exp (C M η : ℝ) (hC : 0 < C) (hη : 0 < η) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ x : ℝ, S ≤ x → C * x ^ M ≤ Real.exp (η * x) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero M η hη
  have h2 := h1.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / C by positivity))
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp h2
  refine ⟨max S 1, le_max_right _ _, fun x hx => ?_⟩
  have h3 : x ^ M * Real.exp (-η * x) ≤ 1 / C := hS x (le_trans (le_max_left _ _) hx)
  have h4 := L12_le_of_mul_exp _ _ _ _ h3
  calc C * x ^ M ≤ C * (1 / C * Real.exp (η * x)) := mul_le_mul_of_nonneg_left h4 hC.le
    _ = Real.exp (η * x) := by field_simp

set_option maxHeartbeats 400000 in
/-- **the family size on `SRange`**. -/
theorem L12c_Zsize_ev (αp : ℝ) (hα1 : 1 < αp) (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (B : ℝ)
    (hB : 1 ≤ B) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      0 < (Qn : ℝ) ∧ 1 ≤ twin Qn r0 ε0 ∧ 1 ≤ (R1S Qn ε s₀ : ℝ) ∧ (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀ ∧
      0 < Zsize (R1S Qn ε s₀) (twin Qn r0 ε0) K (Real.exp s₀) Qn ∧
      Real.log (Zsize (R1S Qn ε s₀) (twin Qn r0 ε0) K (Real.exp s₀) Qn) ≤ (2 - 2 / αp + η) * s₀ := by
  set M : ℝ := 12 + 2 * B + 2 * (r0 + ε0) with hMdef
  set C₁ : ℝ := 9 * (9 * Real.exp 1 ^ 2 + 1) with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  obtain ⟨S, hS1, hS⟩ := L12c_poly_le_exp C₁ M η hC₁pos hη
  filter_upwards [L12_log_eventually_ge (max S 3),
    L12_ev_rpow_exp (6 + B) 1 (1 / Real.exp 1) one_pos (by positivity)] with Qn hL eR
  intro K ε s₀ hR
  obtain ⟨hK2, hKle, hεge, hεle, hsge, hsle⟩ := hR
  have hL3 : 3 ≤ Real.log (Qn : ℝ) := le_trans (le_max_right _ _) hL
  have hLS : S ≤ Real.log (Qn : ℝ) := le_trans (le_max_left _ _) hL
  have hQpos : (0 : ℝ) < Qn := by
    rcases Nat.eq_zero_or_pos Qn with h | h
    · exfalso; rw [h, Nat.cast_zero, Real.log_zero] at hL3; norm_num at hL3
    · exact_mod_cast h
  set L := Real.log (Qn : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hQexp : Real.exp L = Qn := Real.exp_log hQpos
  set P := L ^ B with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hLpos B
  have hεpos : 0 < ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hLpos _) hεge
  have hεne : ε ≠ 0 := hεpos.ne'
  have hεinv : 1 / ε ≤ P := by
    rw [one_div_le hεpos hP, one_div, ← Real.rpow_neg hLpos.le]; exact hεge
  have hKpos : 0 < K := by linarith
  set T := L ^ (r0 + ε0) with hTdef
  have hTtw : twin (Qn : ℝ) r0 ε0 = T := rfl
  rw [hTtw]
  have hT1 : 1 ≤ T := Real.one_le_rpow (by linarith) (by linarith)
  have hsL : L ≤ s₀ := by linarith
  have hs0 : 0 < s₀ := by linarith
  set N₀ := Real.exp s₀ with hN₀
  -- `U = e N₀ L⁶ (1/ε) e^{−L}`
  set U := Real.exp (s₀ + 1) * L ^ 6 / (ε * Qn) with hUdef
  have hU : U = Real.exp 1 * L ^ 6 * (1 / ε) * (N₀ * Real.exp (-L)) := by
    rw [hUdef, hN₀, ← hQexp, Real.exp_add, Real.exp_neg]
    field_simp
  have hU0 : 0 ≤ U := by positivity
  have hRU : (R1S (Qn : ℝ) ε s₀ : ℝ) ≤ U := Nat.floor_le hU0
  have hNe0 : 0 < N₀ * Real.exp (-L) := by positivity
  have hUV : U ≤ Real.exp 1 * L ^ 6 * P * (N₀ * Real.exp (-L)) := by
    rw [hU]
    apply mul_le_mul_of_nonneg_right _ hNe0.le
    exact mul_le_mul_of_nonneg_left hεinv (by positivity)
  -- `R₁ ≥ 1`
  have hR1ge : 1 ≤ (R1S (Qn : ℝ) ε s₀ : ℝ) := by
    have hNL : Real.exp 3 ≤ N₀ * Real.exp (-L) := by
      rw [hN₀, ← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ (by linarith)
    have hε1 : 1 ≤ 1 / ε := by rw [le_div_iff₀ hεpos]; linarith
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have he3 : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
    have hU1 : 1 ≤ U := by
      rw [hU]
      have h1 : 1 ≤ Real.exp 1 * L ^ 6 := one_le_mul_of_one_le_of_one_le he1 hL6
      have h2 : 1 ≤ Real.exp 1 * L ^ 6 * (1 / ε) := one_le_mul_of_one_le_of_one_le h1 hε1
      exact one_le_mul_of_one_le_of_one_le h2 (he3.trans hNL)
    have : 1 ≤ R1S (Qn : ℝ) ε s₀ := Nat.le_floor (by exact_mod_cast hU1)
    exact_mod_cast this
  -- `R₁ ≤ N₀`
  have hR1le : (R1S (Qn : ℝ) ε s₀ : ℝ) ≤ N₀ := by
    have hsplit : L ^ (6 + B) = L ^ 6 * P := by
      rw [Real.rpow_add hLpos, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have eR' := L12_le_of_mul_exp _ _ _ _ eR
    rw [hsplit] at eR'
    have h1 : Real.exp 1 * L ^ 6 * P * Real.exp (-L) ≤ 1 := by
      have h2 : L ^ 6 * P * Real.exp (-L) ≤ 1 / Real.exp 1 := by
        have := mul_le_mul_of_nonneg_right eR' (Real.exp_pos (-L)).le
        calc L ^ 6 * P * Real.exp (-L) ≤ 1 / Real.exp 1 * Real.exp (1 * L) * Real.exp (-L) := this
          _ = 1 / Real.exp 1 := by
              rw [mul_assoc, ← Real.exp_add, show 1 * L + -L = 0 by ring, Real.exp_zero, mul_one]
      calc Real.exp 1 * L ^ 6 * P * Real.exp (-L) = Real.exp 1 * (L ^ 6 * P * Real.exp (-L)) := by ring
        _ ≤ Real.exp 1 * (1 / Real.exp 1) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
        _ = 1 := by field_simp
    calc (R1S (Qn : ℝ) ε s₀ : ℝ) ≤ Real.exp 1 * L ^ 6 * P * (N₀ * Real.exp (-L)) := hRU.trans hUV
      _ = (Real.exp 1 * L ^ 6 * P * Real.exp (-L)) * N₀ := by ring
      _ ≤ 1 * N₀ := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = N₀ := one_mul _
  -- `N₀ e^{−L} ≤ D := e^{s₀(1−1/α′)}`
  set D := Real.exp (s₀ * (1 - 1 / αp)) with hD
  have hαpos : 0 < αp := by linarith
  have hND : N₀ * Real.exp (-L) ≤ D := by
    rw [hN₀, ← Real.exp_add, hD]; apply Real.exp_le_exp.mpr
    have : s₀ / αp ≤ L := by rw [div_le_iff₀ hαpos]; linarith
    have e : s₀ * (1 - 1 / αp) = s₀ - s₀ / αp := by ring
    linarith
  have hD0 : 0 < D := Real.exp_pos _
  have hD2 : D ^ 2 = Real.exp ((2 - 2 / αp) * s₀) := by
    rw [hD, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- the bound
  have hR1D : (R1S (Qn : ℝ) ε s₀ : ℝ) ≤ Real.exp 1 * L ^ 6 * P * D :=
    (hRU.trans hUV).trans (mul_le_mul_of_nonneg_left hND (by positivity))
  have hKD : K * N₀ / Qn ≤ P * D := by
    have e : K * N₀ / Qn = K * (N₀ * Real.exp (-L)) := by
      rw [← hQexp, Real.exp_neg]; field_simp
    rw [e]
    exact mul_le_mul hKle hND hNe0.le hP.le
  have hKD0 : 0 ≤ K * N₀ / Qn := by positivity
  have hR0 : (0 : ℝ) ≤ R1S (Qn : ℝ) ε s₀ := Nat.cast_nonneg _
  have hT3 : 2 * T + 1 ≤ 3 * T := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hZle : Zsize (R1S (Qn : ℝ) ε s₀) T K N₀ Qn ≤ C₁ * (L ^ 12 * P ^ 2 * T ^ 2) * D ^ 2 := by
    unfold Zsize
    have h1 : (R1S (Qn : ℝ) ε s₀ : ℝ) ^ 2 * (2 * T + 1) ^ 2 ≤ (Real.exp 1 * L ^ 6 * P * D) ^ 2 * (3 * T) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ hR0 hR1D 2) (pow_le_pow_left₀ (by linarith) hT3 2) (by positivity)
        (by positivity)
    have h2 : (K * N₀ / Qn) ^ 2 ≤ (P * D) ^ 2 := pow_le_pow_left₀ hKD0 hKD 2
    have h3 : (P * D) ^ 2 ≤ L ^ 12 * P ^ 2 * T ^ 2 * D ^ 2 := by
      have hL12 : 1 ≤ L ^ 12 := one_le_pow₀ hL1
      have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT1
      have hLT : 1 ≤ L ^ 12 * T ^ 2 := one_le_mul_of_one_le_of_one_le hL12 hT2
      have e : L ^ 12 * P ^ 2 * T ^ 2 * D ^ 2 = (L ^ 12 * T ^ 2) * (P * D) ^ 2 := by ring
      rw [e]
      exact le_mul_of_one_le_left (sq_nonneg _) hLT
    have e2 : (Real.exp 1 * L ^ 6 * P * D) ^ 2 * (3 * T) ^ 2
        = 9 * Real.exp 1 ^ 2 * (L ^ 12 * P ^ 2 * T ^ 2 * D ^ 2) := by ring
    rw [e2] at h1
    rw [hC₁]
    linear_combination 9 * h1 + 9 * h2 + 9 * h3
  -- `L^12 P² T² = L^M ≤ s₀^M`
  have hLM : L ^ 12 * P ^ 2 * T ^ 2 = L ^ M := by
    have e1 : P ^ 2 = L ^ (2 * B) := by
      rw [hPdef, ← Real.rpow_natCast (L ^ B) 2, ← Real.rpow_mul hLpos.le]; congr 1; push_cast; ring
    have e2 : T ^ 2 = L ^ (2 * (r0 + ε0)) := by
      rw [hTdef, ← Real.rpow_natCast (L ^ (r0 + ε0)) 2, ← Real.rpow_mul hLpos.le]; congr 1; push_cast; ring
    have e3 : L ^ 12 = L ^ (12 : ℝ) := by
      rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e1, e2, e3, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
  have hM0 : 0 ≤ M := by rw [hMdef]; nlinarith
  have hLMs : L ^ M ≤ s₀ ^ M := Real.rpow_le_rpow hLpos.le hsL hM0
  have hsS : S ≤ s₀ := le_trans hLS hsL
  have hCs := hS s₀ hsS
  have hZpos : 0 < Zsize (R1S (Qn : ℝ) ε s₀) T K N₀ Qn := by
    unfold Zsize
    have : 0 < (R1S (Qn : ℝ) ε s₀ : ℝ) ^ 2 * (2 * T + 1) ^ 2 := by
      have : (0 : ℝ) < R1S (Qn : ℝ) ε s₀ := by linarith
      positivity
    have h2 : 0 ≤ (K * N₀ / Qn) ^ 2 := sq_nonneg _
    linarith
  refine ⟨hQpos, hT1, hR1ge, hR1le, hZpos, ?_⟩
  rw [Real.log_le_iff_le_exp hZpos]
  calc Zsize (R1S (Qn : ℝ) ε s₀) T K N₀ Qn ≤ C₁ * (L ^ 12 * P ^ 2 * T ^ 2) * D ^ 2 := hZle
    _ = C₁ * L ^ M * D ^ 2 := by rw [hLM]
    _ ≤ C₁ * s₀ ^ M * D ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hLMs hC₁pos.le
    _ ≤ Real.exp (η * s₀) * D ^ 2 := mul_le_mul_of_nonneg_right hCs (sq_nonneg _)
    _ = Real.exp ((2 - 2 / αp + η) * s₀) := by
        rw [hD2, ← Real.exp_add]; congr 1; ring

end ShellS
end ZetaShell
