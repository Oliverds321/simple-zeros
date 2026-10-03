/-
L7_5 (28 Sep 2026), round 8: `ZO_ibp'` (the statement of `ZO_ibp`), Step 4 in the regime `D = |γ|−2T > μ+1`,
by the Fourier route of the draft, from `ZO_nsp` (non-stationary phase for `𝓕H̃` on `|η| ≤ D/(8πe)`; round 8: proved from the single-frequency leaf
`nsp_single` in ZZ2g_Nsp.lean):
  `μ²∫|I|² = μ² ∫ |𝓕H̃|²|𝓕G_μ|² ≤ μ² L² ∫|𝓕G_μ|² + μ² Hb² ∫|𝓕H̃|²`,
  `L = C₃ D^{−k−1}` (low range, `ZO_nsp`),  `Hb = μ^{k−1} ∫|f_j^{(k)}| / (2πR)^k` (high range, `norm_fourier_mul_le`),
  `∫|𝓕G_μ|² = μ^{−1}∫|f_j|²`,  `∫|𝓕H̃|² = ∫_{t>0}|H_ρ|² ≤ C_H T` (`ZO_H_L2'`).
-/
import ZetaShell.PropZ.ZZ2e_Fourier
import ZetaShell.PropZ.ZZ2g_Nsp
import ZetaShell.PropZ.ZZ2c_HL2

open MeasureTheory FourierTransform Complex Convolution

namespace ZetaShell.PropZ

/-- the non-stationary phase bound (leaf): `|𝓕H̃(η)| ≤ C₃ D^{−k−1}` for `|η| ≤ D/(8πe)`. -/
theorem ZO_nsp (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 → 1 ≤ |ρ.im| - 2 * T →
      ∀ η : ℝ, |η| ≤ (|ρ.im| - 2 * T) / (8 * Real.pi * Real.exp 1) →
      ‖𝓕 (Htil T κ Ξ ρ) η‖ ≤ C₃ / (|ρ.im| - 2 * T) ^ (k + 1) :=
  ZO_nsp' κ hκ hκ1 Ξ hΞ k hk

theorem iD_ofReal (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ∀ n : ℕ, iteratedDeriv n (fun z => ((g z : ℝ) : ℂ)) = fun z => ((iteratedDeriv n g z : ℝ) : ℂ)
  | 0 => by simp only [iteratedDeriv_zero]
  | n + 1 => by
    rw [iteratedDeriv_succ, iD_ofReal g hg n, iteratedDeriv_succ]
    funext z
    have hs : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n g) := by
      rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv n hg
    have hd := ((hs.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 _).differentiable one_ne_zero z).hasDerivAt
    exact hd.ofReal_comp.deriv

theorem sq_fourier_integrable (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    Integrable (fun η => ‖𝓕 F η‖ ^ 2) := by
  have hS := (𝓕 (hFc.toSchwartzMap hF)).integrable (μ := MeasureTheory.volume)
  have hb : ∀ η, ‖𝓕 F η‖ ≤ ∫ x, ‖F x‖ := fun η => by
    have := ZetaShell.FourierLink.norm_fourier_mul_le F hF hFc 0 η
    simpa using this
  refine Integrable.mono' (hS.norm.const_mul (∫ x, ‖F x‖)) ?_ (Filter.Eventually.of_forall fun η => ?_)
  · exact (hS.1.norm.pow 2)
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (hb η) (norm_nonneg _)

set_option maxHeartbeats 1000000 in
theorem ZO_ibp' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (μ : ℝ), 0 < μ → ∀ (ρ : ℂ), 0 < ρ.re → ρ.re < 1 →
      μ + 1 < |ρ.im| - 2 * T → ∀ j ≤ A,
      μ ^ 2 * (∫ ξ, ‖Irho T κ Ξ f j ρ μ ξ‖ ^ 2) ≤ C * T * ((μ + 1) / (|ρ.im| - 2 * T)) ^ (2 * k) := by
  obtain ⟨C₃, hC₃, hN⟩ := ZO_nsp κ hκ hκ1 Ξ hΞ k hk
  obtain ⟨CH, hCH, hH⟩ := ZO_H_L2' κ hκ hκ1 Ξ hΞ
  obtain ⟨S2, hS2⟩ : ∃ S : ℝ, S = ∑ i ∈ Finset.range (A + 1), ∫ z, |fj f i z| ^ 2 := ⟨_, rfl⟩
  obtain ⟨SB, hSB⟩ : ∃ S : ℝ, S = ∑ i ∈ Finset.range (A + 1), (∫ z, |iteratedDeriv k (fj f i) z|) ^ 2 := ⟨_, rfl⟩
  have hS20 : 0 ≤ S2 := by rw [hS2]; exact Finset.sum_nonneg fun i _ => integral_nonneg fun z => sq_nonneg _
  have hSB0 : 0 ≤ SB := by rw [hSB]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨C₃ ^ 2 * S2 + CH * 12 ^ (2 * k) * SB, by positivity, ?_⟩
  intro T hT μ hμ ρ hρ0 hρ1 hD j hj
  have hT0 : 0 ≤ T := by linarith
  set D := |ρ.im| - 2 * T with hDdef
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 < D := by linarith
  set R := D / (8 * Real.pi * Real.exp 1) with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨hgs, hgc⟩ := fj_smooth f hf j
  -- the two Fourier factors
  have hHs := Htil_smooth κ hκ Ξ hΞ T ρ hρ0 hρ1
  have hHc := Htil_compact κ hκ Ξ hΞ T ρ hρ0 hρ1
  have hGs := Gmu_smooth f hf j μ
  have hGc := Gmu_compact f hf j μ hμ
  -- `∫|𝓕G_μ|² = μ^{−1} ∫|f_j|²`
  have hG2 : (∫ η, ‖𝓕 (Gmu f j μ) η‖ ^ 2) = μ⁻¹ * ∫ z, |fj f j z| ^ 2 := by
    rw [ZetaShell.FourierLink.plancherel_cc _ hGs hGc]
    unfold Gmu
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [MeasureTheory.Measure.integral_comp_mul_left (fun z => |fj f j z| ^ 2) (-μ), smul_eq_mul, abs_inv,
      abs_neg, abs_of_pos hμ]
  -- `∫|𝓕H̃|² ≤ C_H T`
  have hH2 : (∫ η, ‖𝓕 (Htil T κ Ξ ρ) η‖ ^ 2) ≤ CH * T := by
    rw [ZetaShell.FourierLink.plancherel_cc _ hHs hHc]
    refine le_trans (le_of_eq ?_) (hH T hT ρ hρ0 hρ1)
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext t
    unfold Htil
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem ht]
    · simp only [Set.indicator_of_notMem ht, norm_zero]; norm_num
  -- `∫|G_μ^{(k)}| = μ^{k−1} ∫|f_j^{(k)}|`
  have hGk : (∫ z, ‖iteratedDeriv k (Gmu f j μ) z‖) = μ ^ k * (μ⁻¹ * ∫ z, |iteratedDeriv k (fj f j) z|) := by
    have e1 : iteratedDeriv k (Gmu f j μ) = fun z => (((-μ) ^ k * iteratedDeriv k (fj f j) (-μ * z) : ℝ) : ℂ) := by
      unfold Gmu
      rw [iD_ofReal (fun z => fj f j (-μ * z)) (hgs.comp (contDiff_const.mul contDiff_id)) k,
        iteratedDeriv_comp_const_mul (hgs.of_le (by exact_mod_cast le_top)) (-μ)]
    rw [e1]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos hμ]
    rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left (fun z => |iteratedDeriv k (fj f j) z|) (-μ),
      smul_eq_mul, abs_inv, abs_neg, abs_of_pos hμ]
  set Bk := ∫ z, |iteratedDeriv k (fj f j) z| with hBk
  have hBk0 : 0 ≤ Bk := integral_nonneg fun z => abs_nonneg _
  set L := C₃ / D ^ (k + 1) with hL
  have hL0 : 0 ≤ L := by positivity
  set Hb := μ ^ k * (μ⁻¹ * Bk) / (2 * Real.pi * R) ^ k with hHb
  have hHb0 : 0 ≤ Hb := by positivity
  -- pointwise split
  have hpw : ∀ η, ‖𝓕 (Htil T κ Ξ ρ) η‖ ^ 2 * ‖𝓕 (Gmu f j μ) η‖ ^ 2
      ≤ L ^ 2 * ‖𝓕 (Gmu f j μ) η‖ ^ 2 + Hb ^ 2 * ‖𝓕 (Htil T κ Ξ ρ) η‖ ^ 2 := by
    intro η
    rcases le_or_gt |η| R with hη | hη
    · have h1 := hN T hT ρ hρ0 hρ1 hD1 η hη
      have h2 : ‖𝓕 (Htil T κ Ξ ρ) η‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖𝓕 (Gmu f j μ) η‖)
      nlinarith [sq_nonneg Hb, sq_nonneg ‖𝓕 (Htil T κ Ξ ρ) η‖]
    · have hdec := ZetaShell.FourierLink.norm_fourier_mul_le _ hGs hGc k η
      rw [hGk] at hdec
      have hge : (2 * Real.pi * R) ^ k ≤ |2 * Real.pi * η| ^ k := by
        apply pow_le_pow_left₀ (by positivity)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        exact mul_le_mul_of_nonneg_left hη.le (by positivity)
      have hG1 : ‖𝓕 (Gmu f j μ) η‖ ≤ Hb := by
        rw [hHb, le_div_iff₀ (by positivity)]
        calc ‖𝓕 (Gmu f j μ) η‖ * (2 * Real.pi * R) ^ k ≤ ‖𝓕 (Gmu f j μ) η‖ * |2 * Real.pi * η| ^ k :=
              mul_le_mul_of_nonneg_left hge (norm_nonneg _)
          _ ≤ μ ^ k * (μ⁻¹ * Bk) := hdec
      have h2 : ‖𝓕 (Gmu f j μ) η‖ ^ 2 ≤ Hb ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG1 2
      have := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖𝓕 (Htil T κ Ξ ρ) η‖)
      nlinarith [sq_nonneg L, sq_nonneg ‖𝓕 (Gmu f j μ) η‖]
  have i1 := (sq_fourier_integrable _ hGs hGc).const_mul (L ^ 2)
  have i2 := (sq_fourier_integrable _ hHs hHc).const_mul (Hb ^ 2)
  have hup : Integrable (fun η => L ^ 2 * ‖𝓕 (Gmu f j μ) η‖ ^ 2 + Hb ^ 2 * ‖𝓕 (Htil T κ Ξ ρ) η‖ ^ 2) := i1.add i2
  have hint := integral_mono_of_nonneg (Filter.Eventually.of_forall fun η => by
      simp only [Pi.zero_apply]; positivity) hup (Filter.Eventually.of_forall hpw)
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul, hG2] at hint
  rw [Irho_L2_fourier κ hκ Ξ hΞ f hf T j ρ hρ0 hρ1 μ hμ]
  -- the constants for this `j`
  have hjS2 : (∫ z, |fj f j z| ^ 2) ≤ S2 := by
    rw [hS2]
    exact Finset.single_le_sum (f := fun i => ∫ z, |fj f i z| ^ 2)
      (fun i _ => integral_nonneg fun z => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  have hjSB : Bk ^ 2 ≤ SB := by
    rw [hSB, hBk]
    exact Finset.single_le_sum (f := fun i => (∫ z, |iteratedDeriv k (fj f i) z|) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  set q := (μ + 1) / D with hq
  have hq0 : 0 ≤ q := by positivity
  -- low range: `μ² L² μ^{−1} ∫|f_j|² ≤ C₃² S2 T q^{2k}`
  have hlow : μ ^ 2 * (L ^ 2 * (μ⁻¹ * ∫ z, |fj f j z| ^ 2)) ≤ C₃ ^ 2 * S2 * T * q ^ (2 * k) := by
    have e : μ ^ 2 * (L ^ 2 * (μ⁻¹ * ∫ z, |fj f j z| ^ 2))
        = C₃ ^ 2 * (∫ z, |fj f j z| ^ 2) * (μ / D ^ (2 * k + 2)) := by
      rw [hL]; field_simp; ring
    rw [e]
    have hμD : μ / D ^ (2 * k + 2) ≤ q ^ (2 * k) := by
      rw [hq, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 1 ≤ (μ + 1) ^ (2 * k) := one_le_pow₀ (by linarith)
      have h2 : μ ≤ D ^ 2 := by nlinarith
      calc μ * D ^ (2 * k) ≤ D ^ 2 * D ^ (2 * k) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = 1 * D ^ (2 * k + 2) := by ring
        _ ≤ (μ + 1) ^ (2 * k) * D ^ (2 * k + 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
    have hI0 : 0 ≤ ∫ z, |fj f j z| ^ 2 := integral_nonneg fun z => sq_nonneg _
    calc C₃ ^ 2 * (∫ z, |fj f j z| ^ 2) * (μ / D ^ (2 * k + 2))
        ≤ C₃ ^ 2 * S2 * q ^ (2 * k) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hjS2 (sq_nonneg _)) hμD (by positivity) (by positivity)
      _ ≤ C₃ ^ 2 * S2 * T * q ^ (2 * k) := by
          have : 0 ≤ C₃ ^ 2 * S2 * q ^ (2 * k) := by positivity
          nlinarith
  -- high range: `μ² Hb² C_H T ≤ C_H 12^{2k} SB T q^{2k}`
  have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hhigh : μ ^ 2 * (Hb ^ 2 * (CH * T)) ≤ CH * 12 ^ (2 * k) * SB * T * q ^ (2 * k) := by
    have e2 : 2 * Real.pi * R = D / (4 * Real.exp 1) := by rw [hR]; field_simp; ring
    have hX : D / 12 ≤ 2 * Real.pi * R := by
      rw [e2]; exact div_le_div_of_nonneg_left hD0.le (by positivity) (by linarith)
    have hRp : 0 < 2 * Real.pi * R := by positivity
    have hμHb : μ * Hb = μ ^ k * Bk / (2 * Real.pi * R) ^ k := by
      rw [hHb]; field_simp
    have h12 : μ ^ k * Bk / (2 * Real.pi * R) ^ k ≤ Bk * (12 * q) ^ k := by
      calc μ ^ k * Bk / (2 * Real.pi * R) ^ k ≤ μ ^ k * Bk / (D / 12) ^ k :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ (by positivity) hX k)
        _ = Bk * (12 * μ / D) ^ k := by
            rw [div_pow, div_pow, mul_pow]; field_simp
        _ ≤ Bk * (12 * q) ^ k := by
            apply mul_le_mul_of_nonneg_left _ hBk0
            apply pow_le_pow_left₀ (by positivity)
            rw [hq, mul_div_assoc]
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact div_le_div_of_nonneg_right (by linarith) hD0.le
    have hsq : μ ^ 2 * Hb ^ 2 ≤ Bk ^ 2 * (12 ^ (2 * k) * q ^ (2 * k)) := by
      have h0 : 0 ≤ μ * Hb := by positivity
      calc μ ^ 2 * Hb ^ 2 = (μ * Hb) ^ 2 := by ring
        _ ≤ (Bk * (12 * q) ^ k) ^ 2 := pow_le_pow_left₀ h0 (hμHb ▸ h12) 2
        _ = Bk ^ 2 * (12 ^ (2 * k) * q ^ (2 * k)) := by
            rw [mul_pow, ← pow_mul, mul_pow, mul_comm k 2]
    calc μ ^ 2 * (Hb ^ 2 * (CH * T)) = (μ ^ 2 * Hb ^ 2) * (CH * T) := by ring
      _ ≤ Bk ^ 2 * (12 ^ (2 * k) * q ^ (2 * k)) * (CH * T) := mul_le_mul_of_nonneg_right hsq (by positivity)
      _ ≤ SB * (12 ^ (2 * k) * q ^ (2 * k)) * (CH * T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjSB (by positivity)) (by positivity)
      _ = CH * 12 ^ (2 * k) * SB * T * q ^ (2 * k) := by ring
  calc μ ^ 2 * (∫ η, ‖𝓕 (Htil T κ Ξ ρ) η‖ ^ 2 * ‖𝓕 (Gmu f j μ) η‖ ^ 2)
      ≤ μ ^ 2 * (L ^ 2 * (μ⁻¹ * ∫ z, |fj f j z| ^ 2) + Hb ^ 2 * ∫ η, ‖𝓕 (Htil T κ Ξ ρ) η‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hint (sq_nonneg μ)
    _ ≤ μ ^ 2 * (L ^ 2 * (μ⁻¹ * ∫ z, |fj f j z| ^ 2) + Hb ^ 2 * (CH * T)) := by
        gcongr
    _ = μ ^ 2 * (L ^ 2 * (μ⁻¹ * ∫ z, |fj f j z| ^ 2)) + μ ^ 2 * (Hb ^ 2 * (CH * T)) := by ring
    _ ≤ C₃ ^ 2 * S2 * T * q ^ (2 * k) + CH * 12 ^ (2 * k) * SB * T * q ^ (2 * k) := add_le_add hlow hhigh
    _ = (C₃ ^ 2 * S2 + CH * 12 ^ (2 * k) * SB) * T * q ^ (2 * k) := by ring

end ZetaShell.PropZ
