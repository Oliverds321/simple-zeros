/-
Z5_PropZWdom (L7_5b, 1 Oct 2026): `propZ_W_dom`, Proposition Z (Weil form) with the s-integrand DOMINATED by an
explicit integrable function `H` whose integral obeys Proposition Z's bound. Same hypotheses and constant as `propZ_W`
(the proof is `propZ_W`'s proof, stopped before the last integration). Needed by S1 (Theorem S, step 1), which sums
Proposition Z over `r ≤ R₁` and `χ`: the sum of integrals needs integrable summands, and `propZ_W` does not assert
that `s ↦ W(s−s₀) ∫ ‖S_χ‖²Φ` is integrable (`H` is).
-/
import ZetaShell.PropZ.Z5_PropZW

open MeasureTheory Complex

namespace ZetaShell.PropZ

theorem propZ_W_dom (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c) (hc : ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2)
    (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      Summable (pairTerm χ T (Δ * Real.exp s₀) s₀ A k) ∧
      ∃ H : ℝ → ℝ, Integrable H ∧
        (∀ s, W (s - s₀) * (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)) ≤ H s) ∧
        (∫ s, H s)
          ≤ C₀ * normCA W A * (T * ∑' p, pairTerm χ T (Δ * Real.exp s₀) s₀ A k p + EerrW T (Real.exp s₀) r Δ) := by
  obtain ⟨CZ, hCZ0, hZ⟩ := Z5ZeroW κ hκ hκ1 Ξ hΞ f hf A k hA hk
  obtain ⟨CR, hR⟩ := Z5R_W κ hκ hκ1 Ξ hΞ f hf
  have hpt := ZP_pointwise κ hκ hκ1 Ξ hΞ f hf c hc0 hc
    (fun F a g hg hgs Δ hΔ => plancherel_identity f hf c hc0 F a g hg hgs Δ hΔ)
    (fun r _ χ hχ V hV hVc hVpos => smooth_explicit_formula_weil χ hχ V hV hVc hVpos)
  refine ⟨2 / c * CZ + 2 / c * max CR 0 * 2, by positivity, fun W hW s₀ T Δ hs₀ hT hΔ hΔ1 r _ χ hχ hr => ?_⟩
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
  refine ⟨fun s => 2 / c * (W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
      + 2 / c * max CR 0 * E * W (s - s₀), hg, hbound, ?_⟩
  have hWint := int_W_le W hW A s₀
  calc (∫ s, (2 / c * (W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
          + 2 / c * max CR 0 * E * W (s - s₀)))
      = 2 / c * (∫ s, W (s - s₀) * (Δ ^ 2 * (∫ x, ‖zeroPartW χ T κ Ξ f Δ s x‖ ^ 2)))
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
