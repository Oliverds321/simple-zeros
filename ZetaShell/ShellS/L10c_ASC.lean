/-
L10c_ASC (L7_10c, 3 Oct 2026): **Chebyshev bounds for the complements of the near-P vector**:
`Σ_{n≤M, |log n − s| > d} Λ(n)²/(n(log n − s)²) ≤ 2C₀L(1/d² + 2)` (`C₀ = e(log 4 + 4)`, `log M ≤ L`), from
`ψ(x) ≤ (log 4 + 4)x` on unit `log`-blocks; and `Σ_{non-prime n ≤ x} Λ(n) = ψ − θ ≤ 2√x log x` for the prime powers
near `e^s`. Consequence (`l2_far_le`): every vector `v` with `|v_n| ≤ |a_n(s)|` that vanishes on the primes with
`|log n − s| ≤ d` has `‖v‖² ≤ (2C₀L/π²)(1/d² + 2) + (s+1)²T²·2e^{(s+1)/2}·e^{1−s}/(4π²)`.
-/
import ZetaShell.ShellS.L10c_ASCore
import ZetaShell.Farey.A1p_SmallPrimeNorm
import ZetaShell.LemmaK.LK9_K5_Main
import ZetaShell.LemmaK.LK9_DT_Facts

noncomputable section
open scoped BigOperators Chebyshev
open ArithmeticFunction

namespace ZetaShell
namespace ShellS
namespace ASc

/-- the Chebyshev constant of a unit `log`-block. -/
def C0ch : ℝ := Real.exp 1 * (Real.log 4 + 4)

theorem C0ch_pos : 0 < C0ch := by unfold C0ch; positivity

/-- **unit `log`-block**: `Σ_{a ≤ log n < a+1} Λ(n)/n ≤ e(log 4 + 4)`. -/
theorem block_cheb (M : ℕ) (a : ℝ) :
    ∑ n ∈ (Finset.Ioc 0 M).filter (fun n : ℕ => a ≤ Real.log n ∧ Real.log n < a + 1),
      vonMangoldt n / (n : ℝ) ≤ C0ch := by
  set S := (Finset.Ioc 0 M).filter (fun n : ℕ => a ≤ Real.log n ∧ Real.log n < a + 1) with hS
  have h1 : ∀ n ∈ S, vonMangoldt n / (n : ℝ) ≤ vonMangoldt n * Real.exp (-a) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn'.1).1
    have hexp : Real.exp a ≤ n := by
      rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr hn'.2.1
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos a) hexp
  have h2 : ∑ n ∈ S, vonMangoldt n ≤ ψ (Real.exp (a + 1)) := by
    unfold Chebyshev.psi
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn'.1).1
      rw [Finset.mem_Ioc]
      refine ⟨(Finset.mem_Ioc.mp hn'.1).1, Nat.le_floor ?_⟩
      rw [← Real.exp_log hn0]; exact (Real.exp_lt_exp.mpr hn'.2.2).le
    · intro n _ _; exact vonMangoldt_nonneg
  have h3 := Chebyshev.psi_le_const_mul_self (Real.exp_pos (a + 1)).le
  calc ∑ n ∈ S, vonMangoldt n / (n : ℝ) ≤ ∑ n ∈ S, vonMangoldt n * Real.exp (-a) := Finset.sum_le_sum h1
    _ = (∑ n ∈ S, vonMangoldt n) * Real.exp (-a) := by rw [Finset.sum_mul]
    _ ≤ ((Real.log 4 + 4) * Real.exp (a + 1)) * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right (h2.trans h3) (Real.exp_pos _).le
    _ = C0ch := by
        unfold C0ch
        rw [mul_assoc, ← Real.exp_add, show a + 1 + -a = 1 by ring]; ring

theorem sum_union_le' {s t : Finset ℕ} (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ s ∪ t, f n ≤ ∑ n ∈ s, f n + ∑ n ∈ t, f n := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h0 : 0 ≤ ∑ n ∈ s ∩ t, f n := Finset.sum_nonneg fun n _ => hf n
  linarith

theorem inv_sq_sum_le (K : ℕ) : ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) ^ 2) ≤ 2 := by
  have h : ∀ K : ℕ, 1 ≤ K → ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) ^ 2) ≤ 2 - 1 / (K : ℝ) := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have e : 1 / (((n + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · have := h K hK
    have : 0 ≤ 1 / (K : ℝ) := by positivity
    linarith

/-- **the far sum**: `Σ_{n≤M, |log n − s| > d} Λ(n)²/(n(log n − s)²) ≤ 2C₀L(1/d² + 2)`. -/
theorem far_sum_le (M : ℕ) (s d L : ℝ) (hd : 0 < d) (hL : Real.log M ≤ L) (hL0 : 0 ≤ L) :
    ∑ n ∈ (Finset.Ioc 0 M).filter (fun n : ℕ => d < |Real.log n - s|),
      vonMangoldt n ^ 2 / ((n : ℝ) * (Real.log n - s) ^ 2) ≤ 3 * C0ch * L * (1 / d ^ 2 + 2) := by
  set S := (Finset.Ioc 0 M).filter (fun n : ℕ => d < |Real.log n - s|) with hS
  set K := ⌊L + |s|⌋₊ with hK
  set kf : ℕ → ℕ := fun n => ⌊|Real.log n - s|⌋₊ with hkf
  set w : ℕ → ℝ := fun k => if k = 0 then 1 / d ^ 2 else 1 / ((k : ℝ) ^ 2) with hw
  have hmaps : ∀ n ∈ S, kf n ∈ Finset.range (K + 1) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn'.1).1
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Ioc.mp hn'.1).2
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn0
    have hlogM : Real.log n ≤ L := le_trans (Real.log_le_log (by linarith) hnM) hL
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    calc |Real.log n - s| ≤ |Real.log n| + |s| := abs_sub _ _
      _ = Real.log n + |s| := by rw [abs_of_nonneg hlog0]
      _ ≤ L + |s| := by linarith
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- each fiber
  have hfib : ∀ k ∈ Finset.range (K + 1),
      ∑ n ∈ S.filter (fun n => kf n = k), vonMangoldt n ^ 2 / ((n : ℝ) * (Real.log n - s) ^ 2)
        ≤ L * w k * (3 * C0ch) := by
    intro k _
    have hpt : ∀ n ∈ S.filter (fun n => kf n = k),
        vonMangoldt n ^ 2 / ((n : ℝ) * (Real.log n - s) ^ 2) ≤ L * w k * (vonMangoldt n / (n : ℝ)) := by
      intro n hn
      have hn1 := Finset.mem_filter.mp hn
      have hn' := Finset.mem_filter.mp hn1.1
      have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn'.1).1
      have hnM : (n : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Ioc.mp hn'.1).2
      have hlogM : Real.log n ≤ L := le_trans (Real.log_le_log (by linarith) hnM) hL
      have hΛ : vonMangoldt n ≤ L := le_trans vonMangoldt_le_log hlogM
      have hΛ0 : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
      have hu : d < |Real.log n - s| := hn'.2
      have hsq : 0 < (Real.log n - s) ^ 2 := by
        have : 0 < |Real.log n - s| := lt_trans hd hu
        rw [← sq_abs]; positivity
      have hwk : 1 / (Real.log n - s) ^ 2 ≤ w k := by
        have hk : kf n = k := hn1.2
        simp only [hw]
        split_ifs with h0
        · rw [← sq_abs]
          exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hd.le hu.le 2)
        · have hk1 : (k : ℝ) ≤ |Real.log n - s| := by
            rw [← hk]; exact Nat.floor_le (abs_nonneg _)
          have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero h0
          rw [← sq_abs]
          exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hk0.le hk1 2)
      have hn0' : (0 : ℝ) < n := by linarith
      calc vonMangoldt n ^ 2 / ((n : ℝ) * (Real.log n - s) ^ 2)
          = vonMangoldt n * (vonMangoldt n / (n : ℝ)) * (1 / (Real.log n - s) ^ 2) := by
            field_simp
        _ ≤ L * (vonMangoldt n / (n : ℝ)) * w k := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hΛ (by positivity)) hwk (by positivity)
            positivity
        _ = L * w k * (vonMangoldt n / (n : ℝ)) := by ring
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.mul_sum]
    have hw0 : 0 ≤ w k := by simp only [hw]; split_ifs <;> positivity
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL0 hw0)
    -- the fiber lies in two unit blocks
    set A := (Finset.Ioc 0 M).filter (fun n : ℕ => s + k ≤ Real.log n ∧ Real.log n < s + k + 1)
    set B := (Finset.Ioc 0 M).filter (fun n : ℕ => s - k - 1 ≤ Real.log n ∧ Real.log n < s - k - 1 + 1)
    set B' := (Finset.Ioc 0 M).filter (fun n : ℕ => s - k ≤ Real.log n ∧ Real.log n < s - k + 1)
    have hsub : S.filter (fun n => kf n = k) ⊆ A ∪ (B ∪ B') := by
      intro n hn
      have hn1 := Finset.mem_filter.mp hn
      have hn' := Finset.mem_filter.mp hn1.1
      have hk : ⌊|Real.log n - s|⌋₊ = k := hn1.2
      have h1 : (k : ℝ) ≤ |Real.log n - s| := by rw [← hk]; exact Nat.floor_le (abs_nonneg _)
      have h2 : |Real.log n - s| < k + 1 := by rw [← hk]; exact Nat.lt_floor_add_one _
      rcases le_or_gt 0 (Real.log n - s) with hpos | hneg
      · rw [abs_of_nonneg hpos] at h1 h2
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn'.1, by linarith, by linarith⟩)
      · rw [abs_of_neg hneg] at h1 h2
        rcases eq_or_lt_of_le h1 with heq | hlt
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hn'.1, by linarith, by linarith⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hn'.1, by linarith, by linarith⟩))
    have hnn : ∀ n, 0 ≤ vonMangoldt n / (n : ℝ) := fun n => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
    calc ∑ n ∈ S.filter (fun n => kf n = k), vonMangoldt n / (n : ℝ)
        ≤ ∑ n ∈ A ∪ (B ∪ B'), vonMangoldt n / (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hnn n
      _ ≤ ∑ n ∈ A, vonMangoldt n / (n : ℝ) + ∑ n ∈ B ∪ B', vonMangoldt n / (n : ℝ) :=
          sum_union_le' _ hnn
      _ ≤ ∑ n ∈ A, vonMangoldt n / (n : ℝ) + (∑ n ∈ B, vonMangoldt n / (n : ℝ) + ∑ n ∈ B', vonMangoldt n / (n : ℝ)) := by
          gcongr; exact sum_union_le' _ hnn
      _ ≤ C0ch + (C0ch + C0ch) := by
          gcongr
          · exact block_cheb M (s + k)
          · exact block_cheb M (s - k - 1)
          · exact block_cheb M (s - k)
      _ = 3 * C0ch := by ring
  refine le_trans (Finset.sum_le_sum hfib) ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsplit : ∑ k ∈ Finset.range (K + 1), w k = 1 / d ^ 2 + ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) ^ 2) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [hw, if_pos rfl]
    congr 1
    rw [show Finset.Icc 1 K = Finset.Ico 1 (K + 1) from rfl]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (by have := (Finset.mem_Ico.mp hk).1; omega)]
  rw [hsplit]
  have := inv_sq_sum_le K
  have hC := C0ch_pos
  have : L * (1 / d ^ 2 + ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) ^ 2)) ≤ L * (1 / d ^ 2 + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hL0
  nlinarith

theorem acoef_normSq_le_T (T s : ℝ) (hT : 0 ≤ T) (n : ℕ) (hn : 0 < n) :
    ‖TrackF.acoefS T s n‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * (vonMangoldt n ^ 2 / n) * T ^ 2 := by
  have h := LemmaK.K5Aux.norm_acoef_sq T s n hn
  have hD := LemmaK.DTFacts.DT_norm_le T (s - Real.log n) hT
  have hD2 : ‖LemmaK.DT T (s - Real.log n)‖ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  show ‖LemmaK.acoef T s n‖ ^ 2 ≤ _
  rw [h]
  apply mul_le_mul_of_nonneg_left hD2
  positivity

/-- **the complement bound**: a vector dominated by `a(s)` that vanishes on the near primes. -/
theorem l2_far_le (M : ℕ) (T s d L : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) (hL : Real.log M ≤ L) (hL0 : 0 ≤ L)
    (hT : 0 ≤ T) (hs : 1 ≤ s) (v : ℕ → ℂ) (hv : ∀ n, ‖v n‖ ≤ ‖TrackF.acoefS T s n‖)
    (hv0 : ∀ n : ℕ, n.Prime → |Real.log n - s| ≤ d → v n = 0) :
    ZetaQ.l2sq M v ≤ (1 / Real.pi ^ 2) * (3 * C0ch * L * (1 / d ^ 2 + 2))
      + (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s) * (2 * Real.exp ((s + 1) / 2) * (s + 1)) := by
  unfold ZetaQ.l2sq
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 M) (fun n : ℕ => d < |Real.log n - s|)]
  have hpi : 0 < Real.pi ^ 2 := by positivity
  -- far part
  have hfar : ∑ n ∈ (Finset.Ioc 0 M).filter (fun n : ℕ => d < |Real.log n - s|), ‖v n‖ ^ 2
      ≤ (1 / Real.pi ^ 2) * (3 * C0ch * L * (1 / d ^ 2 + 2)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (far_sum_le M s d L hd hL hL0) (by positivity))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := Finset.mem_filter.mp hn
    have hn0 := (Finset.mem_Ioc.mp hn'.1).1
    have hne : s - Real.log n ≠ 0 := by
      intro h
      have : |Real.log n - s| = 0 := by rw [abs_eq_zero]; linarith
      linarith [hn'.2]
    have h1 := TrackF.acoefS_normSq_le T s n hn0 hne
    have h2 : ‖v n‖ ^ 2 ≤ ‖TrackF.acoefS T s n‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hv n) 2
    refine le_trans h2 (le_trans h1 (le_of_eq ?_))
    have e : (s - Real.log n) ^ 2 = (Real.log n - s) ^ 2 := by ring
    rw [e]; field_simp
  -- near part: only non-primes survive
  have hnear : ∑ n ∈ (Finset.Ioc 0 M).filter (fun n : ℕ => ¬ d < |Real.log n - s|), ‖v n‖ ^ 2
      ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s) * (2 * Real.exp ((s + 1) / 2) * (s + 1)) := by
    set x := Real.exp (s + 1) with hx
    have hpt : ∀ n ∈ (Finset.Ioc 0 M).filter (fun n : ℕ => ¬ d < |Real.log n - s|),
        ‖v n‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s)
          * (if n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬ n.Prime) then vonMangoldt n else 0) := by
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hn0 := (Finset.mem_Ioc.mp hn'.1).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hclose : |Real.log n - s| ≤ d := not_lt.mp hn'.2
      have hlog1 : Real.log n ≤ s + 1 := by linarith [(abs_le.mp hclose).2]
      have hlog2 : s - 1 ≤ Real.log n := by linarith [(abs_le.mp hclose).1]
      by_cases hp : n.Prime
      · rw [hv0 n hp hclose, norm_zero]
        have : 0 ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s)
            * (if n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬ n.Prime) then vonMangoldt n else 0) := by
          have : 0 ≤ (if n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬ n.Prime) then vonMangoldt n else 0) := by
            split_ifs <;> simp [vonMangoldt_nonneg]
          have : (0 : ℝ) ≤ s + 1 := by linarith
          positivity
        simpa using this
      · have hmem : n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬ n.Prime) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn0, Nat.le_floor ?_⟩, hp⟩
          rw [hx, ← Real.exp_log hnR]; exact Real.exp_le_exp.mpr hlog1
        rw [if_pos hmem]
        have h1 : ‖v n‖ ^ 2 ≤ ‖TrackF.acoefS T s n‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hv n) 2
        have h2 := acoef_normSq_le_T T s hT n hn0
        have hΛ : vonMangoldt n ≤ s + 1 := le_trans vonMangoldt_le_log hlog1
        have hΛ0 : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
        have hninv : 1 / (n : ℝ) ≤ Real.exp (1 - s) := by
          rw [one_div, show 1 - s = -(s - 1) by ring, Real.exp_neg]
          apply inv_anti₀ (Real.exp_pos _)
          rw [← Real.exp_log hnR]; exact Real.exp_le_exp.mpr hlog2
        calc ‖v n‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * (vonMangoldt n ^ 2 / n) * T ^ 2 := h1.trans h2
          _ = (4 * Real.pi ^ 2)⁻¹ * vonMangoldt n * T ^ 2 * (1 / (n : ℝ)) * vonMangoldt n := by
              field_simp
          _ ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s) * vonMangoldt n := by
              gcongr
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ n ∈ (Finset.Ioc 0 M).filter (fun n : ℕ => ¬ d < |Real.log n - s|),
        (if n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬ n.Prime) then vonMangoldt n else 0)
        ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬ n.Prime), vonMangoldt n := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn; exact (Finset.mem_filter.mp hn).2
      · intro n _ _; exact vonMangoldt_nonneg
    have hψθ : ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬ n.Prime), vonMangoldt n
        ≤ 2 * Real.exp ((s + 1) / 2) * (s + 1) := by
      rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime]
      have h := Chebyshev.psi_sub_theta_le (x := x) (by rw [hx]; exact Real.one_le_exp (by linarith))
      rw [hx, Real.log_exp, Real.sqrt_eq_rpow, ← Real.exp_mul] at h
      convert h using 2; ring_nf
    have hc0 : 0 ≤ (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s) := by
      have : (0 : ℝ) ≤ s + 1 := by linarith
      positivity
    exact mul_le_mul_of_nonneg_left (hsum.trans hψθ) hc0
  linarith

end ASc
end ShellS
end ZetaShell
