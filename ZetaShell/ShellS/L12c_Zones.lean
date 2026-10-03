/-
L7_12c (3 Oct 2026): Lemma 6d (lem:shell-6d), the three zone counts of the family `𝔛` in power form
(`𝒵′ := 𝒵 N₀^{2ε′}`, `I := ⌈1/ε′⌉`):
* (LF, Jutila (1.8), `σ ≥ 4/5`): `W(β ≥ σ) ≤ (I+1)·9C·𝒵′^{(2+ε_J)(1−σ)}`;
* (bulk, Montgomery–Bombieri Th. 20, `1/2 ≤ σ ≤ 4/5`): `W(β ≥ σ) ≤ (I+1)·9C·𝒵′^{3(1−σ)/(2−σ)+ε_M}`;
* (all zeros, unit windows): `W(all) ≤ (I+1)·9C·𝒵′^{1+ε_L}`.
`ZeroDensityInput` enters only here (its two fields, in the sources' form).
-/
import ZetaShell.ShellS.L12c_Counts

noncomputable section
open Complex
open scoped ENNReal

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- `(log x)^A ≤ K x^ε` for `x ≥ 2`. -/
lemma L12c_log_rpow_le (A ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x →
    Real.log x ^ A ≤ K * x ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt A 0 with hA | hA
  · refine ⟨Real.log 2 ^ A, Real.rpow_nonneg hl2.le _, fun x hx => ?_⟩
    have h1 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h2 : Real.log x ^ A ≤ Real.log 2 ^ A := Real.rpow_le_rpow_of_nonpos hl2 h1 hA
    have h3 : 1 ≤ x ^ ε := Real.one_le_rpow (by linarith) hε.le
    have h4 : 0 ≤ Real.log 2 ^ A := Real.rpow_nonneg hl2.le _
    nlinarith
  · refine ⟨(A / ε) ^ A, Real.rpow_nonneg (by positivity) _, fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h1 : Real.log x ≤ x ^ (ε / A) / (ε / A) := Real.log_le_rpow_div hx0 (by positivity)
    have h2 : Real.log x ^ A ≤ (x ^ (ε / A) / (ε / A)) ^ A := Real.rpow_le_rpow hlx h1 hA.le
    refine h2.trans (le_of_eq ?_)
    rw [div_eq_mul_inv, Real.mul_rpow (Real.rpow_nonneg hx0 _) (by positivity), ← Real.rpow_mul hx0,
      div_mul_cancel₀ _ hA.ne', inv_div]
    ring

/-- **(LF) zone**: Jutila on the blocks. -/
theorem L12c_zone_LF (hD : ZeroDensityInput) (εJ : ℝ) (hεJ : 0 < εJ) (hεJ1 : εJ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Qn : ℕ) (T K ε s₀ ε' : ℝ) (k : ℕ), 3 ≤ k → 1 ≤ T → 0 ≤ K → 0 < (Qn : ℝ) →
      0 < s₀ → 1 ≤ (R1S Qn ε s₀ : ℝ) → (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀ → 0 < ε' → ε' ≤ 1 →
      ∀ σ : ℝ, 4 / 5 ≤ σ → σ ≤ 1 →
        L12cW Qn T K ε s₀ k (fun ρ => σ ≤ ρ.re) ≤ ENNReal.ofReal ((⌈1 / ε'⌉₊ + 1) * (9 * C *
          (Zsize (R1S Qn ε s₀) T K (Real.exp s₀) Qn * Real.exp s₀ ^ (2 * ε')) ^ ((2 + εJ) * (1 - σ)))) := by
  obtain ⟨C₀, hC₀⟩ := hD.jutila εJ hεJ
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro Qn T K ε s₀ ε' k hk hT hK hQ hs hR1 hR1N hε' hε1 σ hσ1 hσ2
  have hσ0 : 0 < σ := by linarith
  apply L12c_family_pow Qn T K ε s₀ ε' k hk (fun ρ => σ ≤ ρ.re) hT hK hQ hs hR1 hR1N hε' hε1
    (fun r χ Y => Nrect r χ σ Y) (fun r χ Y => L12c_Nrect_nonneg r χ σ Y)
    (fun r _ χ hχ h Y s hs => by
      have : NeZero r := ⟨h⟩
      have hprim : χ.IsPrimitive := by
        classical
        simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ; exact hχ
      exact L12c_rect_count χ hprim σ Y hσ0 s hs)
    (max C₀ 0) ((2 + εJ) * (1 - σ)) (le_max_right _ _) (by nlinarith) (by nlinarith)
  intro i _ hRi j
  set R := Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i with hR
  set Y := 2 ^ j * Hblk T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' i with hY
  have hN0' : 1 < Real.exp s₀ := by have := Real.add_one_le_exp s₀; linarith
  have hY1 : 1 ≤ Y := by
    have h1 := Z6c_Hge T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' hK hQ hN0' hR1 i
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [hY]; nlinarith
  have hfl : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hRi)
  have hJ := hC₀ ⌊R⌋₊ hfl Y hY1 σ hσ1 hσ2
  have hfle : ((⌊R⌋₊ : ℕ) : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hfl0 : (0 : ℝ) ≤ ⌊R⌋₊ := Nat.cast_nonneg _
  have ha : 0 ≤ (2 + εJ) * (1 - σ) := by nlinarith
  calc ∑ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r, Nrect r χ σ Y
      ≤ Nstar ⌊R⌋₊ σ Y := L12c_block_rect Qn T K ε s₀ ε' i σ Y
    _ ≤ C₀ * (((⌊R⌋₊ : ℕ) : ℝ) ^ 2 * Y) ^ ((2 + εJ) * (1 - σ)) := hJ
    _ ≤ max C₀ 0 * (((⌊R⌋₊ : ℕ) : ℝ) ^ 2 * Y) ^ ((2 + εJ) * (1 - σ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    _ ≤ max C₀ 0 * (R ^ 2 * Y) ^ ((2 + εJ) * (1 - σ)) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        apply Real.rpow_le_rpow (by positivity) _ ha
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact pow_le_pow_left₀ hfl0 hfle 2

/-- **bulk zone**: Montgomery–Bombieri on the blocks (`1/2 ≤ σ ≤ 4/5`). -/
theorem L12c_zone_bulk (hD : ZeroDensityInput) (εM : ℝ) (hεM : 0 < εM) (hεM1 : εM ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Qn : ℕ) (T K ε s₀ ε' : ℝ) (k : ℕ), 3 ≤ k → 1 ≤ T → 0 ≤ K → 0 < (Qn : ℝ) →
      0 < s₀ → 1 ≤ (R1S Qn ε s₀ : ℝ) → (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀ → 0 < ε' → ε' ≤ 1 →
      ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 4 / 5 →
        L12cW Qn T K ε s₀ k (fun ρ => σ ≤ ρ.re) ≤ ENNReal.ofReal ((⌈1 / ε'⌉₊ + 1) * (9 * C *
          (Zsize (R1S Qn ε s₀) T K (Real.exp s₀) Qn * Real.exp s₀ ^ (2 * ε')) ^
            (3 * (1 - σ) / (2 - σ) + εM))) := by
  obtain ⟨A, C₀, hC₀⟩ := hD.montgomery
  obtain ⟨KL, hKL, hKLb⟩ := L12c_log_rpow_le A εM hεM
  refine ⟨max C₀ 0 * KL, mul_nonneg (le_max_right _ _) hKL, ?_⟩
  intro Qn T K ε s₀ ε' k hk hT hK hQ hs hR1 hR1N hε' hε1 σ hσ1 hσ2
  have hσ0 : 0 < σ := by linarith
  have hb0 : 0 ≤ 3 * (1 - σ) / (2 - σ) := div_nonneg (by linarith) (by linarith)
  have hb1 : 3 * (1 - σ) / (2 - σ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  apply L12c_family_pow Qn T K ε s₀ ε' k hk (fun ρ => σ ≤ ρ.re) hT hK hQ hs hR1 hR1N hε' hε1
    (fun r χ Y => Nrect r χ σ Y) (fun r χ Y => L12c_Nrect_nonneg r χ σ Y)
    (fun r _ χ hχ h Y s hs => by
      have : NeZero r := ⟨h⟩
      have hprim : χ.IsPrimitive := by
        classical
        simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ; exact hχ
      exact L12c_rect_count χ hprim σ Y hσ0 s hs)
    (max C₀ 0 * KL) (3 * (1 - σ) / (2 - σ) + εM) (mul_nonneg (le_max_right _ _) hKL) (by linarith)
    (by linarith)
  intro i _ hRi j
  set R := Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i with hR
  set Y := 2 ^ j * Hblk T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' i with hY
  have hN0' : 1 < Real.exp s₀ := by have := Real.add_one_le_exp s₀; linarith
  have hY2 : 2 ≤ Y := by
    have h1 := Z6c_Hge T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' hK hQ hN0' hR1 i
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [hY]; nlinarith
  have hfl : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by exact_mod_cast hRi)
  have hM := hC₀ ⌊R⌋₊ hfl Y hY2 σ hσ1 (by linarith)
  set q : ℝ := ((⌊R⌋₊ : ℕ) : ℝ) with hq
  have hfle : q ≤ R := Nat.floor_le (by linarith)
  have hq1 : (1 : ℝ) ≤ q := by rw [hq]; exact_mod_cast hfl
  -- the log factor
  have hYq : Y * q ≤ q ^ 2 * Y := by
    have h0 : 0 ≤ Y * q * (q - 1) := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have hlog : Real.log (Y * q) ^ A ≤ KL * (q ^ 2 * Y) ^ εM := by
    have h1 := hKLb (Y * q) (by nlinarith)
    have h2 : (Y * q) ^ εM ≤ (q ^ 2 * Y) ^ εM :=
      Real.rpow_le_rpow (by positivity) hYq hεM.le
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hKL)
  have hx1 : 1 ≤ q ^ 2 * Y := by nlinarith
  have hpow : (Y * q ^ 2) ^ (3 * (1 - σ) / (2 - σ)) * (q ^ 2 * Y) ^ εM
      = (q ^ 2 * Y) ^ (3 * (1 - σ) / (2 - σ) + εM) := by
    rw [mul_comm Y, Real.rpow_add (by linarith)]
  have hlog0 : 0 ≤ Real.log (Y * q) ^ A := Real.rpow_nonneg (Real.log_nonneg (by nlinarith)) _
  calc ∑ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r, Nrect r χ σ Y
      ≤ Nstar ⌊R⌋₊ σ Y := L12c_block_rect Qn T K ε s₀ ε' i σ Y
    _ ≤ C₀ * ((Y * q ^ 2) ^ (3 * (1 - σ) / (2 - σ)) * Real.log (Y * q) ^ A) := hM
    _ ≤ max C₀ 0 * ((Y * q ^ 2) ^ (3 * (1 - σ) / (2 - σ)) * Real.log (Y * q) ^ A) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (Real.rpow_nonneg (by positivity) _) hlog0)
    _ ≤ max C₀ 0 * ((Y * q ^ 2) ^ (3 * (1 - σ) / (2 - σ)) * (KL * (q ^ 2 * Y) ^ εM)) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (by positivity) _)
    _ = max C₀ 0 * KL * (q ^ 2 * Y) ^ (3 * (1 - σ) / (2 - σ) + εM) := by rw [← hpow]; ring
    _ ≤ max C₀ 0 * KL * (R ^ 2 * Y) ^ (3 * (1 - σ) / (2 - σ) + εM) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_max_right _ _) hKL)
        apply Real.rpow_le_rpow (by positivity) _ (by linarith)
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact pow_le_pow_left₀ (by linarith) hfle 2

/-- **all zeros**: unit windows on the blocks. -/
theorem L12c_zone_all (εL : ℝ) (hεL : 0 < εL) (hεL1 : εL ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Qn : ℕ) (T K ε s₀ ε' : ℝ) (k : ℕ), 3 ≤ k → 1 ≤ T → 0 ≤ K → 0 < (Qn : ℝ) →
      0 < s₀ → 1 ≤ (R1S Qn ε s₀ : ℝ) → (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀ → 0 < ε' → ε' ≤ 1 →
        L12cW Qn T K ε s₀ k (fun _ => True) ≤ ENNReal.ofReal ((⌈1 / ε'⌉₊ + 1) * (9 * C *
          (Zsize (R1S Qn ε s₀) T K (Real.exp s₀) Qn * Real.exp s₀ ^ (2 * ε')) ^ (1 + εL))) := by
  obtain ⟨A₀, hA₀, hloc⟩ := L12b_local_count
  have hA₀0 : 0 ≤ A₀ := by linarith
  refine ⟨3 * A₀ * (2 / εL + 2), by positivity, ?_⟩
  intro Qn T K ε s₀ ε' k hk hT hK hQ hs hR1 hR1N hε' hε1
  set Nf : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℝ :=
    fun r _ Y => (2 * |Y| + 2) * (A₀ * (Real.log r + Real.log (|Y| + 4))) with hNf
  have hNf0 : ∀ r χ Y, 0 ≤ Nf r χ Y := by
    intro r χ Y
    simp only [hNf]
    have h1 : 0 ≤ Real.log (r : ℝ) := Real.log_natCast_nonneg r
    have h2 : 0 ≤ Real.log (|Y| + 4) := Real.log_nonneg (by linarith [abs_nonneg Y])
    positivity
  apply L12c_family_pow Qn T K ε s₀ ε' k hk (fun _ => True) hT hK hQ hs hR1 hR1N hε' hε1 Nf hNf0
    (fun r _ χ hχ h Y s hs => by
      have : NeZero r := ⟨h⟩
      have hprim : χ.IsPrimitive := by
        classical
        simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ; exact hχ
      exact L12c_all_count χ A₀ hA₀ (hloc r χ hprim) |Y| (abs_nonneg Y) s
        (fun ρ hρ => ((hs ρ hρ).2).trans (le_abs_self Y)))
    (3 * A₀ * (2 / εL + 2)) (1 + εL) (by positivity) (by linarith) (by linarith)
  intro i _ hRi j
  set R := Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i with hR
  set Y := 2 ^ j * Hblk T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' i with hY
  have hN0' : 1 < Real.exp s₀ := by have := Real.add_one_le_exp s₀; linarith
  have hY2 : 2 ≤ Y := by
    have h1 := Z6c_Hge T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' hK hQ hN0' hR1 i
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [hY]; nlinarith
  have habs : |Y| = Y := abs_of_nonneg (by linarith)
  have hblk := L12c_block_all Qn T K ε s₀ ε' i A₀ Y hA₀0 (by linarith) hRi
  simp only [hNf, habs]
  refine hblk.trans ?_
  set x := R ^ 2 * Y with hx
  have hx2 : 2 ≤ x := by rw [hx]; nlinarith
  have hlogx : Real.log x ≤ x ^ εL / εL := Real.log_le_rpow_div (by linarith) hεL
  have hxe : 1 ≤ x ^ εL := Real.one_le_rpow (by linarith) hεL.le
  have hlR : Real.log R ≤ Real.log x := Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
  have hR2 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hRi
  have hRY : Y ≤ R ^ 2 * Y := le_mul_of_one_le_left (by linarith) hR2
  have hlY : Real.log (Y + 4) ≤ Real.log 3 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by rw [hx]; linarith)
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hsum : Real.log R + Real.log (Y + 4) ≤ (2 / εL + 2) * x ^ εL := by
    have h1 : 2 * Real.log x ≤ 2 / εL * x ^ εL := by
      have := mul_le_mul_of_nonneg_left hlogx (show (0 : ℝ) ≤ 2 by norm_num)
      rw [mul_div_assoc'] at this
      calc 2 * Real.log x ≤ 2 * x ^ εL / εL := this
        _ = 2 / εL * x ^ εL := by ring
    nlinarith
  have hlR0 : 0 ≤ Real.log R := Real.log_nonneg hRi
  calc R ^ 2 * ((2 * Y + 2) * (A₀ * (Real.log R + Real.log (Y + 4))))
      ≤ R ^ 2 * ((3 * Y) * (A₀ * ((2 / εL + 2) * x ^ εL))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul (by linarith) _
          (mul_nonneg hA₀0 (add_nonneg hlR0 (Real.log_nonneg (by linarith)))) (by linarith)
        exact mul_le_mul_of_nonneg_left hsum hA₀0
    _ = 3 * A₀ * (2 / εL + 2) * (x * x ^ εL) := by rw [hx]; ring
    _ = 3 * A₀ * (2 / εL + 2) * x ^ (1 + εL) := by
        rw [Real.rpow_add (by linarith), Real.rpow_one]
    _ = 3 * A₀ * (2 / εL + 2) * (R ^ 2 * (2 ^ j * Hblk T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' i)) ^ (1 + εL) := rfl

end ShellS
end ZetaShell
