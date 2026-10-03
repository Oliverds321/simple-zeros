/-
Sub-nodes ZB-1..3 (L7_5, round 2): the elementary bridging facts that `ZP_pointwise` needs besides Z5a and Z5b-W.
All three are OPEN (sorry); each is elementary (no number theory):
  ZB-1: S_χ(·;s) is Z5a's `S` for ν = Σ_{n≤Ne^κ} Λχ(n)A_s(n)δ_n − δ_{r=1}A_s dy, and Z5a's `G` is
        Σ_n Λχ(n)V_{x,s}(n) − δ_{r=1}Ṽ_{x,s}(1)   (uses `A_s(y) = 0` for `y ≤ 0` and `f` even);
  ZB-2: `V_{x,s}` is `C^∞`, compactly supported, with `tsupport ⊆ (1,∞)` (from `s ≥ s₀−1 ≥ 2`, `κ ≤ 1`);
  ZB-3: the zero part and the Weil remainder are square-integrable in `x`.
-/
import ZetaShell.PropZ.ZDefsW
import ZetaShell.PropZ.ZB_As
import ZetaShell.PropZ.ZB_Bounded
import ZetaShell.PropZ.ZB_Meas

open MeasureTheory Complex

namespace ZetaShell.PropZ

open scoped Classical in
theorem ZB_Schi_form (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∃ (F : Finset ℝ) (a g : ℝ → ℂ), Continuous g ∧ HasCompactSupport g ∧
        (∀ β, Schi χ T κ Ξ s β = ∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)) ∧
        (∀ x, ∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)
          = ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * VxsW T κ Ξ f Δ s x n
            - (if r = 1 then mellin (VxsW T κ Ξ f Δ s x) 1 else 0)) := by
  intro s₀ T Δ s hs₀ hT hΔ hΔ1 hs r _ χ hχ
  set M : ℕ := ⌈Real.exp (s + κ)⌉₊ + 1 with hM
  have hbig : ∀ n : ℕ, n ∉ Finset.range M → (n : ℝ) ∉ Set.Ioo (Real.exp (s - κ)) (Real.exp (s + κ)) := by
    intro n hn hmem
    rw [Finset.mem_range, not_lt] at hn
    have h1 : Real.exp (s + κ) ≤ ⌈Real.exp (s + κ)⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp (s + κ)⌉₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith [hmem.2]
  have hAz : ∀ n : ℕ, n ∉ Finset.range M → As T κ Ξ s n = 0 :=
    fun n hn => As_eq_zero_outside T κ hκ Ξ hΞ s (hbig n hn)
  have hinj : Set.InjOn (fun n : ℕ => (n : ℝ)) (Finset.range M : Set ℕ) :=
    (Nat.cast_injective (R := ℝ)).injOn
  have hAc : Continuous (As T κ Ξ s) := (As_contDiff T κ hκ Ξ hΞ s).continuous
  have hAs : HasCompactSupport (As T κ Ξ s) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (As_tsupport T κ hκ Ξ hΞ s)
  have hA0 : ∀ y ∉ Set.Ioi (0 : ℝ), As T κ Ξ s y = 0 :=
    fun y hy => As_eq_zero_of_nonpos T κ Ξ s (not_lt.mp hy)
  refine ⟨(Finset.range M).image (fun n : ℕ => (n : ℝ)),
    fun y => ((ArithmeticFunction.vonMangoldt ⌊y⌋₊ : ℝ) : ℂ) * χ ⌊y⌋₊ * As T κ Ξ s y,
    fun y => -(if r = 1 then As T κ Ξ s y else 0), ?_, ?_, ?_, ?_⟩
  · split_ifs
    · exact hAc.neg
    · exact continuous_const.neg
  · split_ifs
    · exact hAs.neg
    · exact (HasCompactSupport.zero : HasCompactSupport (fun _ : ℝ => (0 : ℂ))).neg
  · intro β
    rw [Finset.sum_image hinj]
    simp only [Schi, Nat.floor_natCast]
    rw [tsum_eq_sum (s := Finset.range M) (fun n hn => by rw [hAz n hn]; ring)]
    have hint : (∫ y, (-(if r = 1 then As T κ Ξ s y else 0)) * eA (y * β))
        = -(if r = 1 then ∫ y in Set.Ioi (0 : ℝ), As T κ Ξ s y * eA (y * β) else 0) := by
      split_ifs
      · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hA0 y hy]; ring),
          ← integral_neg]
        congr 1; funext y; ring
      · simp
    rw [hint, sub_eq_add_neg]
  · intro x
    rw [Finset.sum_image hinj]
    simp only [Nat.floor_natCast]
    rw [tsum_eq_sum (s := Finset.range M) (fun n hn => by
      simp only [VxsW]; rw [hAz n hn]; ring)]
    have hsum : ∑ n ∈ Finset.range M, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * As T κ Ξ s n
          * ((f (Δ * ((n : ℝ) - x)) : ℝ) : ℂ)
        = ∑ n ∈ Finset.range M, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * VxsW T κ Ξ f Δ s x n :=
      Finset.sum_congr rfl fun n _ => by simp only [VxsW]; ring
    have hint : (∫ y, (-(if r = 1 then As T κ Ξ s y else 0)) * ((f (Δ * (y - x)) : ℝ) : ℂ))
        = -(if r = 1 then mellin (VxsW T κ Ξ f Δ s x) 1 else 0) := by
      split_ifs
      · rw [mellin, setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
          simp only [VxsW]; rw [hA0 y hy]; simp), ← integral_neg]
        congr 1; funext y
        simp only [VxsW, sub_self, Complex.cpow_zero, one_smul]
        ring
      · simp
    rw [hsum, hint, sub_eq_add_neg]

theorem ZB_Vxs_props (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ (s₀ T Δ s x : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ContDiff ℝ (⊤ : ℕ∞) (VxsW T κ Ξ f Δ s x) ∧ HasCompactSupport (VxsW T κ Ξ f Δ s x) ∧
        tsupport (VxsW T κ Ξ f Δ s x) ⊆ Set.Ioi 1 := by
  intro s₀ T Δ s x hs₀ hT hΔ hΔ1 hs
  have hts := VxsW_tsupport T κ hκ Ξ hΞ f Δ s x
  refine ⟨VxsW_contDiff T κ hκ Ξ hΞ f hf Δ s x,
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hts, hts.trans ?_⟩
  have hs1 : 0 < s - κ := by have := (abs_le.mp hs).1; linarith
  intro y hy
  have := Real.add_one_lt_exp (ne_of_gt hs1)
  exact lt_of_lt_of_le (by linarith) hy.1

/-- ZB-3a: both parts are bounded in `x`. PROVED (round 4) in `ZB_Bounded.lean` from the shared estimates
(`MellinDecay`, proved) and the shared leaves `ZR_phi_bounds`, `ZR_digamma` (`ZR_Leaves.lean`). -/
theorem ZB_parts_bounded (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∃ C : ℝ, ∀ x : ℝ, ‖zeroPartW χ T κ Ξ f Δ s x‖ ≤ C ∧ ‖remPartW χ T κ Ξ f Δ s x‖ ≤ C :=
  ZB_parts_bounded' κ hκ hκ1 Ξ hΞ f hf

/-- ZB-3b (OPEN): both parts are measurable in `x` (continuity of the Mellin transforms in `x` by dominated
convergence, and of the zero sum by uniform convergence). -/
theorem ZB_parts_measurable (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      AEStronglyMeasurable (fun x => zeroPartW χ T κ Ξ f Δ s x) volume ∧
        AEStronglyMeasurable (fun x => remPartW χ T κ Ξ f Δ s x) volume :=
  ZB_parts_measurable' κ hκ hκ1 Ξ hΞ f hf

/-- `V_{x,s} ≡ 0` for `x` outside `[e^{s−κ} − 1/(8Δ), e^{s+κ} + 1/(8Δ)]`. -/
theorem VxsW_eq_zero_of_far (T κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (Δ : ℝ) (hΔ : 0 < Δ) (s x : ℝ)
    (hx : x ∉ Set.Icc (Real.exp (s - κ) - 1 / (8 * Δ)) (Real.exp (s + κ) + 1 / (8 * Δ))) :
    VxsW T κ Ξ f Δ s x = fun _ => 0 := by
  funext y
  by_cases hy : y ∈ Set.Ioo (Real.exp (s - κ)) (Real.exp (s + κ))
  · unfold VxsW
    have hf0 : f (Δ * (y - x)) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have h1 := hf.supp hmem
      rw [Set.mem_Ioo] at h1
      apply hx
      have e : 1 / (8 * Δ) = (1 / 8) / Δ := by field_simp
      have hl : -(1 / 8 : ℝ) / Δ < y - x := by rw [div_lt_iff₀ hΔ, mul_comm]; exact h1.1
      have hr : y - x < (1 / 8 : ℝ) / Δ := by rw [lt_div_iff₀ hΔ, mul_comm]; exact h1.2
      constructor
      · rw [e]; linarith [hy.1]
      · rw [e]; rw [neg_div] at hl; linarith [hy.2]
    rw [hf0]; simp
  · exact VxsW_eq_zero_outside T κ hκ Ξ hΞ f Δ s x hy

theorem ZB_sq_integrable (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      Integrable (fun x => ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2) ∧
        Integrable (fun x => ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2) := by
  intro s₀ T Δ s hs₀ hT hΔ hΔ1 hs r _ χ hχ
  obtain ⟨C, hC⟩ := ZB_parts_bounded κ hκ hκ1 Ξ hΞ f hf s₀ T Δ s hs₀ hT hΔ hΔ1 hs r χ hχ
  obtain ⟨hmZ, hmR⟩ := ZB_parts_measurable κ hκ hκ1 Ξ hΞ f hf s₀ T Δ s hs₀ hT hΔ hΔ1 hs r χ hχ
  set K := Set.Icc (Real.exp (s - κ) - 1 / (8 * Δ)) (Real.exp (s + κ) + 1 / (8 * Δ)) with hK
  have hKf : volume K ≠ ⊤ := measure_Icc_lt_top.ne
  have hZ0 : ∀ x, x ∉ K → zeroPartW χ T κ Ξ f Δ s x = 0 := by
    intro x hx
    simp only [zeroPartW, VxsW_eq_zero_of_far T κ hκ Ξ hΞ f hf Δ hΔ s x hx, mellin, smul_zero,
      MeasureTheory.integral_zero, mul_zero, tsum_zero]
  have hR0 : ∀ x, x ∉ K → remPartW χ T κ Ξ f Δ s x = 0 := by
    intro x hx
    simp only [remPartW, VxsW_eq_zero_of_far T κ hκ Ξ hΞ f hf Δ hΔ s x hx, mellin, smul_zero,
      MeasureTheory.integral_zero, zero_mul, mul_zero, ite_self, zero_add]
  constructor
  · refine (Measure.integrableOn_of_bounded (M := C ^ 2) hKf (hmZ.norm.pow 2)
      (Filter.Eventually.of_forall fun x => ?_)).integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC x).1 2
    · simp [hZ0 x hx]
  · refine (Measure.integrableOn_of_bounded (M := C ^ 2) hKf (hmR.norm.pow 2)
      (Filter.Eventually.of_forall fun x => ?_)).integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC x).2 2
    · simp [hR0 x hx]

end ZetaShell.PropZ
