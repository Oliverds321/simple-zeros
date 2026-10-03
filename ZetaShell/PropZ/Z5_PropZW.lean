/-
Node Z5 in the Weil form (L7_5, round 2): Proposition Z (prop:shell-Z) with the error term E′ of report §R2.1,
ASSEMBLED from Z5a (`plancherel_identity`, proved), Z5b-W (`smooth_explicit_formula_weil`, proved), `ZP_pointwise`
(Steps 1–2 bridging), `Z5R_W` (Step 2 remainder) and `Z5ZeroW` (Steps 3–5). The proof below is complete; the open
leaves are listed by `SL_Z5W.lean`. The draft-form `propZ` (Z5_PropZ.lean) is kept untouched.
-/
import ZetaShell.PropZ.Z5a_PlancherelMajorant
import ZetaShell.Skeleton.Z5b_SmoothEF
import ZetaShell.PropZ.ZP_Pointwise
import ZetaShell.PropZ.Z5R_W
import ZetaShell.PropZ.Z5Zero_W

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem normCA_nonneg (W : ℝ → ℝ) (A : ℕ) : 0 ≤ normCA W A :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => abs_nonneg _

theorem varpi_nonneg (T μ : ℝ) (k : ℕ) (ρ : ℂ) (hμ : 0 ≤ μ) : 0 ≤ varpi T μ k ρ := by
  unfold varpi
  apply Real.rpow_nonneg
  have : 0 ≤ max (|ρ.im| - 2 * T) 0 := le_max_right _ _
  positivity

theorem pairTerm_nonneg {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T μ s₀ : ℝ) (A k : ℕ) (hμ : 0 ≤ μ)
    (p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) : 0 ≤ pairTerm χ T μ s₀ A k p := by
  unfold pairTerm
  have h1 := varpi_nonneg T μ k p.1.1 hμ
  have h2 := varpi_nonneg T μ k p.2.1 hμ
  have h3 : 0 ≤ Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2) := Real.rpow_nonneg (Real.exp_pos s₀).le _
  positivity

theorem int_W_le (W : ℝ → ℝ) (hW : AvgWeight W) (A : ℕ) (s₀ : ℝ) :
    (∫ s, W (s - s₀)) ≤ 2 * normCA W A := by
  have hWc : HasCompactSupport W :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport W) (hW.supp.trans Set.Ioo_subset_Icc_self)
  have hcont : Continuous W := hW.smooth.continuous
  have hbdd : BddAbove (Set.range fun x => |W x|) :=
    hcont.abs.bddAbove_range_of_hasCompactSupport (hWc.comp_left (g := abs) abs_zero)
  set S := ⨆ x, |W x| with hS
  have hWS : ∀ x, W x ≤ S := fun x => (le_abs_self _).trans (le_ciSup hbdd x)
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun _ => abs_nonneg _
  have hSN : S ≤ normCA W A := by
    have := Finset.single_le_sum (f := fun j => ⨆ x, |iteratedDeriv j W x|)
      (fun j _ => Real.iSup_nonneg fun _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.succ_pos A))
    simpa [normCA, iteratedDeriv_zero] using this
  have hshift : (∫ s, W (s - s₀)) = ∫ s, W s := integral_sub_right_eq_self W s₀
  have hind : ∀ x, W x ≤ Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => S) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hx]; exact hWS x
    · rw [Set.indicator_of_notMem hx]
      have : W x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (Set.Ioo_subset_Icc_self (hW.supp h))
      rw [this]
  have hWi : Integrable W := hcont.integrable_of_hasCompactSupport hWc
  have hIi : Integrable (Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => S)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  rw [hshift]
  calc (∫ s, W s) ≤ ∫ s, Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => S) s := integral_mono hWi hIi hind
    _ = 2 * S := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
      ring
    _ ≤ 2 * normCA W A := by linarith

theorem propZ_W (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c) (hc : ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2)
    (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k) :
    ∃ C₀ : ℝ, ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      Summable (pairTerm χ T (Δ * Real.exp s₀) s₀ A k) ∧
      (∫ s, W (s - s₀) * (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)))
        ≤ C₀ * normCA W A * (T * ∑' p, pairTerm χ T (Δ * Real.exp s₀) s₀ A k p + EerrW T (Real.exp s₀) r Δ) := by
  obtain ⟨CZ, hCZ0, hZ⟩ := Z5ZeroW κ hκ hκ1 Ξ hΞ f hf A k hA hk
  obtain ⟨CR, hR⟩ := Z5R_W κ hκ hκ1 Ξ hΞ f hf
  have hpt := ZP_pointwise κ hκ hκ1 Ξ hΞ f hf c hc0 hc
    (fun F a g hg hgs Δ hΔ => plancherel_identity f hf c hc0 F a g hg hgs Δ hΔ)
    (fun r _ χ hχ V hV hVc hVpos => smooth_explicit_formula_weil χ hχ V hV hVc hVpos)
  refine ⟨2 / c * CZ + 2 / c * max CR 0 * 2, fun W hW s₀ T Δ hs₀ hT hΔ hΔ1 r _ χ hχ hr => ?_⟩
  obtain ⟨hsum, hint, hZb⟩ := hZ W hW s₀ T Δ hs₀ hT hΔ hΔ1 r χ hχ hr
  refine ⟨hsum, ?_⟩
  set E := EerrW T (Real.exp s₀) r Δ with hEdef
  set Sp := ∑' p, pairTerm χ T (Δ * Real.exp s₀) s₀ A k p with hSpdef
  set N := normCA W A with hN
  have hN0 : 0 ≤ N := normCA_nonneg W A
  have hSp0 : 0 ≤ Sp := tsum_nonneg fun p => pairTerm_nonneg χ T _ s₀ A k (by positivity) p
  have hE0 : 0 ≤ E := by
    have hN0' : 0 < Real.exp s₀ := Real.exp_pos s₀
    simp only [hEdef, EerrW]
    positivity
  have hM0 : 0 ≤ max CR 0 := le_max_right _ _
  have hc2 : 0 ≤ 2 / c := by positivity
  have hWsupp : ∀ s, W (s - s₀) ≠ 0 → |s - s₀| ≤ 1 := by
    intro s h0
    have h := hW.supp (subset_tsupport _ h0)
    rw [Set.mem_Ioo] at h
    exact abs_le.mpr ⟨h.1.le, h.2.le⟩
  have hbound : ∀ s, W (s - s₀) * (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ))
      ≤ 2 / c * (W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
        + 2 / c * max CR 0 * E * W (s - s₀) := by
    intro s
    by_cases h0 : W (s - s₀) = 0
    · rw [h0]; simp
    · have hs := hWsupp s h0
      have h1 := hpt s₀ T Δ s hs₀ hT hΔ hΔ1 hs r χ hχ
      have h2 := hR s₀ T Δ hs₀ hT hΔ hΔ1 r χ hχ hr s hs
      have hWn := hW.nonneg (s - s₀)
      have h3 : Δ ^ 2 * (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2) ≤ max CR 0 * E :=
        h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0)
      calc W (s - s₀) * (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ))
          ≤ W (s - s₀) * (2 / c * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))
              + 2 / c * (Δ ^ 2 * (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2))) :=
            mul_le_mul_of_nonneg_left h1 hWn
        _ ≤ W (s - s₀) * (2 / c * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2))
              + 2 / c * (max CR 0 * E)) := by gcongr
        _ = 2 / c * (W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
              + 2 / c * max CR 0 * E * W (s - s₀) := by ring
  have hWi : Integrable (fun s => W (s - s₀)) := by
    have hWc : HasCompactSupport W :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport W) (hW.supp.trans Set.Ioo_subset_Icc_self)
    exact (hW.smooth.continuous.integrable_of_hasCompactSupport hWc).comp_sub_right s₀
  have hg : Integrable (fun s => 2 / c * (W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
      + 2 / c * max CR 0 * E * W (s - s₀)) := (hint.const_mul _).add (hWi.const_mul _)
  have hnn : ∀ s, 0 ≤ W (s - s₀) * (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)) := fun s =>
    mul_nonneg (hW.nonneg _) (integral_nonneg fun β => mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hc0.le))
  have hWint := int_W_le W hW A s₀
  calc (∫ s, W (s - s₀) * (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)))
      ≤ ∫ s, (2 / c * (W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
          + 2 / c * max CR 0 * E * W (s - s₀)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hg (Filter.Eventually.of_forall hbound)
    _ = 2 / c * (∫ s, W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
          + 2 / c * max CR 0 * E * (∫ s, W (s - s₀)) := by
        rw [integral_add (hint.const_mul _) (hWi.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ 2 / c * (CZ * N * T * Sp) + 2 / c * max CR 0 * E * (2 * N) := by
        gcongr
    _ ≤ (2 / c * CZ + 2 / c * max CR 0 * 2) * N * (T * Sp + E) := by
        have hT0 : 0 ≤ T := by linarith
        have hx1 : 0 ≤ 2 / c * CZ * N * E := by positivity
        have hx2 : 0 ≤ 2 / c * max CR 0 * 2 * N * (T * Sp) := by positivity
        nlinarith [hx1, hx2]

end ZetaShell.PropZ
