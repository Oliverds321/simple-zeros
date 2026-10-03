/-
Node M1 (track P/K) — the first display of the proof of lem:sigd-env (l.1286–1291) as a kernel statement: from
`MajorantCert ψ β` (B ≥ 0, B ≥ v_ψ on [−1/2,1/2], supp B̂ ⊂ [−1,1]) the transform B̂ satisfies: B̂ − k_ψ is a positive-
definite kernel (Fourier transform of the nonnegative B − v_ψ·1_{[−1/2,1/2]}), B̂ even, B̂ = 0 on |t| ≥ 1, and
2B̂(0) + 4 sup_{[3/4,1]}|B̂| < β.

Proof (L2_2): `B̂(t) := ∫ B(s) cos(2πts) ds`. For a finite point set and weights y, with
`Φ(s) = Σ y_i y_j cos(2π(x_i − x_j)s) = |Σ y_i e(x_i s)|² ≥ 0`, the quadratic forms are `∫_ℝ B Φ` and
`∫_{−1/2}^{1/2} v_ψ Φ ≤ ∫_{−1/2}^{1/2} B Φ ≤ ∫_ℝ B Φ`. The hypotheses `hcont`, `hpos` are NOT needed
(`majorant_kernel_gen`): if `∫ψ = 0`, `kPsi ψ ≡ 0`; otherwise ψ is interval-integrable.
-/
import ZetaS.Interfaces
import ZetaS.SigmaDist.SigmaHelpers

open Set MeasureTheory Matrix

namespace ZetaS

namespace M1aux

/-- `Φ(s) = Σ_ij y_i y_j cos(2π(x_i − x_j)s) = (Σ y_i cos 2πx_is)² + (Σ y_i sin 2πx_is)²`. -/
lemma phi_eq {n : ℕ} (x y : Fin n → ℝ) (s : ℝ) :
    ∑ i, ∑ j, y i * y j * Real.cos (2 * Real.pi * (x i - x j) * s)
      = (∑ i, y i * Real.cos (2 * Real.pi * x i * s)) ^ 2
        + (∑ i, y i * Real.sin (2 * Real.pi * x i * s)) ^ 2 := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * Real.pi * (x i - x j) * s = 2 * Real.pi * x i * s - 2 * Real.pi * x j * s by ring, Real.cos_sub]
  ring

lemma phi_nonneg {n : ℕ} (x y : Fin n → ℝ) (s : ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * Real.cos (2 * Real.pi * (x i - x j) * s) := by
  rw [phi_eq]; positivity

lemma quad_kerMat {n : ℕ} (f : ℝ → ℝ) (x y : Fin n → ℝ) :
    star y ⬝ᵥ (kerMat f x *ᵥ y) = ∑ i, ∑ j, y i * y j * f (x i - x j) := by
  simp only [dotProduct, mulVec, kerMat, Matrix.of_apply, star_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- an even `f` whose quadratic forms on finite point sets are `≥ 0` is a positive-definite kernel. -/
lemma isPosDefKernel_of {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t)
    (hq : ∀ (n : ℕ) (x y : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, y i * y j * f (x i - x j)) : IsPosDefKernel f := by
  intro n x
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun y => by rw [quad_kerMat]; exact hq n x y⟩
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [kerMat, Matrix.of_apply, star_trivial]
  rw [← heven (x i - x j), neg_sub]

end M1aux

open M1aux

/-- **M1, general form** (no hypothesis on ψ is needed): if `∫ψ = 0` then `kPsi ψ ≡ 0` (division by zero) and
`B̂` alone is positive definite; otherwise ψ is interval-integrable and `B̂ − k_ψ` is the transform of
`B − v_ψ 1_{[−1/2,1/2]} ≥ 0`. Also records `0 ≤ B̂(0)`. -/
theorem majorant_kernel_gen {ψ : ℝ → ℝ} {β : ℝ} (hmaj : MajorantCert ψ β) :
    ∃ Bh : ℝ → ℝ, IsPosDefKernel (fun t => Bh t - kPsi ψ t) ∧ (∀ t, Bh (-t) = Bh t) ∧
      (∀ t, 1 ≤ |t| → Bh t = 0) ∧ 0 ≤ Bh 0 ∧
      ∃ βstar : ℝ, (∀ t ∈ Icc (3 / 4 : ℝ) 1, |Bh t| ≤ βstar) ∧ 2 * Bh 0 + 4 * βstar < β := by
  obtain ⟨B, hBi, _hBeven, hB0, hBv, hBsupp, βstar, hβ1, hβ2⟩ := hmaj
  have hab : (-(1 / 2 : ℝ)) ≤ 1 / 2 := by norm_num
  set a := ∫ t in (-(1 / 2 : ℝ))..(1 / 2), ψ t with ha
  let Bh : ℝ → ℝ := fun t => ∫ s, B s * Real.cos (2 * Real.pi * t * s)
  have hBcos : ∀ t, Integrable (fun s => B s * Real.cos (2 * Real.pi * t * s)) := fun t =>
    hBi.mul_bdd (by fun_prop : Continuous fun s => Real.cos (2 * Real.pi * t * s)).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hBh_even : ∀ t, Bh (-t) = Bh t := by
    intro t
    simp only [Bh]
    congr 1
    funext s
    rw [show 2 * Real.pi * -t * s = -(2 * Real.pi * t * s) by ring, Real.cos_neg]
  have hBh0 : Bh 0 = ∫ s, B s := by
    simp only [Bh, mul_zero, zero_mul, Real.cos_zero, mul_one]
  -- the two quadratic forms
  have hQ : ∀ (n : ℕ) (x y : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, y i * y j * (Bh (x i - x j) - kPsi ψ (x i - x j)) := by
    intro n x y
    set Φ : ℝ → ℝ := fun s => ∑ i, ∑ j, y i * y j * Real.cos (2 * Real.pi * (x i - x j) * s) with hΦ
    have hΦ0 : ∀ s, 0 ≤ Φ s := fun s => phi_nonneg x y s
    have hΦc : Continuous Φ := by simp only [hΦ]; fun_prop
    -- ∫ B Φ as a double sum
    have hBΦ_eq : (fun s => B s * Φ s)
        = fun s => ∑ i, ∑ j, y i * y j * (B s * Real.cos (2 * Real.pi * (x i - x j) * s)) := by
      funext s; simp only [hΦ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
    have hBΦi : Integrable (fun s => B s * Φ s) := by
      rw [hBΦ_eq]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hBcos _).const_mul _
    have hQB : ∑ i, ∑ j, y i * y j * Bh (x i - x j) = ∫ s, B s * Φ s := by
      rw [hBΦ_eq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hBcos _).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hBcos _).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    have hBΦ0 : 0 ≤ ∫ s, B s * Φ s := integral_nonneg fun s => mul_nonneg (hB0 s) (hΦ0 s)
    have hsplit : ∑ i, ∑ j, y i * y j * (Bh (x i - x j) - kPsi ψ (x i - x j))
        = ∑ i, ∑ j, y i * y j * Bh (x i - x j) - ∑ i, ∑ j, y i * y j * kPsi ψ (x i - x j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit, hQB]
    by_cases ha0 : a = 0
    · -- `kPsi ψ ≡ 0`
      have hk0 : ∀ t, kPsi ψ t = 0 := fun t => by unfold kPsi; rw [← ha, ha0, div_zero]
      simp only [hk0, mul_zero, Finset.sum_const_zero, sub_zero]
      exact hBΦ0
    · have hψi : IntervalIntegrable ψ volume (-(1 / 2 : ℝ)) (1 / 2) := by
        by_contra h
        exact ha0 (by rw [ha]; exact intervalIntegral.integral_undef h)
      have hcosc : ∀ t, IntervalIntegrable (fun s => ψ s * Real.cos (2 * Real.pi * t * s) / a)
          volume (-(1 / 2 : ℝ)) (1 / 2) := fun t =>
        (hψi.mul_continuousOn (Continuous.continuousOn (by fun_prop))).div_const a
      have hQk : ∑ i, ∑ j, y i * y j * kPsi ψ (x i - x j)
          = ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s / a * Φ s := by
        have e : (fun s => ψ s / a * Φ s)
            = fun s => ∑ i, ∑ j, y i * y j * (ψ s * Real.cos (2 * Real.pi * (x i - x j) * s) / a) := by
          funext s; simp only [hΦ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
        have hij : ∀ i j, IntervalIntegrable
            (fun s => y i * y j * (ψ s * Real.cos (2 * Real.pi * (x i - x j) * s) / a))
            volume (-(1 / 2 : ℝ)) (1 / 2) := fun i j => (hcosc (x i - x j)).const_mul (y i * y j)
        have hi : ∀ i, IntervalIntegrable
            (fun s => ∑ j, y i * y j * (ψ s * Real.cos (2 * Real.pi * (x i - x j) * s) / a))
            volume (-(1 / 2 : ℝ)) (1 / 2) := fun i =>
          intervalIntegrable_iff.2 (integrable_finsetSum _ fun j _ => intervalIntegrable_iff.1 (hij i j))
        rw [e, intervalIntegral.integral_finsetSum
          (f := fun i s => ∑ j, y i * y j * (ψ s * Real.cos (2 * Real.pi * (x i - x j) * s) / a))
          (fun i _ => hi i)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_finsetSum
          (f := fun j s => y i * y j * (ψ s * Real.cos (2 * Real.pi * (x i - x j) * s) / a))
          (fun j _ => hij i j)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
        rfl
      -- comparison
      have h1 : (∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s / a * Φ s)
          ≤ ∫ s in (-(1 / 2 : ℝ))..(1 / 2), B s * Φ s := by
        apply intervalIntegral.integral_mono_on hab
        · exact (hψi.div_const a).mul_continuousOn hΦc.continuousOn
        · exact hBΦi.intervalIntegrable
        · intro s hs
          exact mul_le_mul_of_nonneg_right (hBv s hs) (hΦ0 s)
      have h2 : (∫ s in (-(1 / 2 : ℝ))..(1 / 2), B s * Φ s) ≤ ∫ s, B s * Φ s := by
        rw [intervalIntegral.integral_of_le hab]
        exact setIntegral_le_integral hBΦi (ae_of_all _ fun s => mul_nonneg (hB0 s) (hΦ0 s))
      rw [hQk]
      linarith
  refine ⟨Bh, isPosDefKernel_of (fun t => by simp only [hBh_even, SigmaHelpers.kPsi_neg]) hQ, hBh_even,
    fun t ht => hBsupp t ht, ?_, βstar, hβ1, ?_⟩
  · rw [hBh0]; exact integral_nonneg hB0
  · rw [hBh0]; exact hβ2

theorem majorant_kernel {ψ : ℝ → ℝ} {β : ℝ} (hmaj : MajorantCert ψ β)
    (hcont : ContinuousOn ψ (Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (hpos : ∀ s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), 0 < ψ s) :
    ∃ Bh : ℝ → ℝ, IsPosDefKernel (fun t => Bh t - kPsi ψ t) ∧ (∀ t, Bh (-t) = Bh t) ∧
      (∀ t, 1 ≤ |t| → Bh t = 0) ∧
      ∃ βstar : ℝ, (∀ t ∈ Icc (3 / 4 : ℝ) 1, |Bh t| ≤ βstar) ∧ 2 * Bh 0 + 4 * βstar < β := by
  obtain ⟨Bh, h1, h2, h3, _, h5⟩ := majorant_kernel_gen hmaj
  exact ⟨Bh, h1, h2, h3, h5⟩

end ZetaS
