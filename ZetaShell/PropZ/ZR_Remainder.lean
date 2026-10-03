/-
L7_5 (28 Sep 2026), round 4: `Z5R_W'` (node Z5R-W, same statement as `Z5R_W`), PROVED from the shared
estimates (`mellin_Vxs_bounds` <- `MellinDecay` + leaf `ZR_phi_bounds`) and the leaf `ZR_digamma` (report R2.1).
(a5) with `u = t/X`: `‖Ṽ(1/2+it)‖·|w_r(t)| ≤ 10 A C₁ (log(rX)+4)(1+|t/X|)^{−3/2}`; the `t`-integral is `X c₀` times that.
(a8) `R^W_{x,s} = 0` off an interval of length `≤ 3(N + 1/Δ)`, so `∫|R|² ≤ 3(N+1/Δ) B²`.
(a9) `Δ²m²(N+1/Δ) ≤ 2N`, `N₀ ≤ 3N`, `X ≤ 3(T+ΔN₀+1)`, `log(rX)+4 ≤ 3 log(rN₀T)` (pure algebra, `ZR_final_alg`).
-/
import ZetaShell.PropZ.ZB_Bounded
import ZetaShell.PropZ.ZP_Bridge

open MeasureTheory Complex

namespace ZetaShell.PropZ

/-- (a5), the `min` bound after rescaling `t = uX`. -/
theorem ZR_min_scaled (v A X t : ℝ) (hA : 0 ≤ A) (hX : 1 ≤ X) (hv0 : 0 ≤ v) (h0 : v ≤ A)
    (h2 : v ≤ A * X ^ 2 / (1 / 4 + t ^ 2)) :
    v * (1 / 4 + (t / X) ^ 2) ≤ 5 / 4 * A := by
  have hX0 : 0 < X := by linarith
  have hq : 0 < 1 / 4 + t ^ 2 := by positivity
  rw [le_div_iff₀ hq] at h2
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = t / X := ⟨_, rfl⟩
  have ht : t = u * X := by rw [hu]; field_simp
  rw [← hu]
  rcases le_or_gt (u ^ 2) 1 with hg | hg
  · nlinarith [mul_le_mul_of_nonneg_left hg hv0]
  · rw [ht] at h2
    have hX2 : 0 < X ^ 2 := by positivity
    have hux : X ^ 2 ≤ u ^ 2 * X ^ 2 := by nlinarith
    have e2 : X ^ 2 / 4 + (u * X) ^ 2 ≤ 5 / 4 * (1 / 4 + (u * X) ^ 2) := by nlinarith
    have key : v * (1 / 4 + u ^ 2) * X ^ 2 ≤ 5 / 4 * A * X ^ 2 := by
      calc v * (1 / 4 + u ^ 2) * X ^ 2 = v * (X ^ 2 / 4 + (u * X) ^ 2) := by ring
        _ ≤ v * (5 / 4 * (1 / 4 + (u * X) ^ 2)) := mul_le_mul_of_nonneg_left e2 hv0
        _ = 5 / 4 * (v * (1 / 4 + (u * X) ^ 2)) := by ring
        _ ≤ 5 / 4 * (A * X ^ 2) := by linarith
        _ = 5 / 4 * A * X ^ 2 := by ring
    exact le_of_mul_le_mul_right key hX2

/-- (a9), pure algebra. -/
theorem ZR_final_alg (C k₁ Δ N N₀ T m X L ℓ Y B len I : ℝ)
    (hC : 0 ≤ C) (hk : 0 ≤ k₁) (hΔ : 0 < Δ) (hN : 0 < N) (hN₀ : 0 < N₀) (hT : 0 ≤ T) (hm0 : 0 ≤ m)
    (hmΔ : m ≤ 1 / Δ) (hmN : m ≤ N) (hX : 0 ≤ X) (hL : 0 ≤ L + 4)
    (hB0 : 0 ≤ B) (hB : B ≤ C * T * m / N * ((L + 4) * X) * k₁)
    (hlen : len ≤ 3 * (N + 1 / Δ)) (hI : I ≤ len * B ^ 2)
    (hNN : N₀ ≤ 3 * N) (hXY : X ≤ 3 * Y) (hLℓ : L + 4 ≤ 3 * ℓ) :
    Δ ^ 2 * I ≤ 1458 * C ^ 2 * k₁ ^ 2 * (T ^ 2 * Y ^ 2 * ℓ ^ 2 / N₀) := by
  have hΔ1 : Δ * (1 / Δ) = 1 := mul_one_div_cancel hΔ.ne'
  have hp1 : Δ * m ≤ 1 := by
    calc Δ * m ≤ Δ * (1 / Δ) := mul_le_mul_of_nonneg_left hmΔ hΔ.le
      _ = 1 := hΔ1
  have hp0 : 0 ≤ Δ * m := mul_nonneg hΔ.le hm0
  have hΔm : Δ ^ 2 * m ^ 2 * (N + 1 / Δ) ≤ 2 * N := by
    have e : Δ ^ 2 * m ^ 2 * (N + 1 / Δ) = (Δ * m) ^ 2 * N + (Δ * m) * m := by
      calc Δ ^ 2 * m ^ 2 * (N + 1 / Δ) = (Δ * m) ^ 2 * N + (Δ * m) * m * (Δ * (1 / Δ)) := by ring
        _ = (Δ * m) ^ 2 * N + (Δ * m) * m := by rw [hΔ1, mul_one]
    have h1 : (Δ * m) ^ 2 * N ≤ N := mul_le_of_le_one_left hN.le (pow_le_one₀ hp0 hp1)
    have h2 : (Δ * m) * m ≤ m := mul_le_of_le_one_left hm0 hp1
    rw [e]; linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = C * T / N * ((L + 4) * X) * k₁ := ⟨_, rfl⟩
  have hBQ : B ≤ Q * m := by
    rw [hQ]
    calc B ≤ C * T * m / N * ((L + 4) * X) * k₁ := hB
      _ = C * T / N * ((L + 4) * X) * k₁ * m := by ring
  have hB2 : B ^ 2 ≤ Q ^ 2 * m ^ 2 := by
    calc B ^ 2 ≤ (Q * m) ^ 2 := pow_le_pow_left₀ hB0 hBQ 2
      _ = Q ^ 2 * m ^ 2 := by ring
  have hlen0 : 0 ≤ 3 * (N + 1 / Δ) := by
    have : 0 ≤ 1 / Δ := one_div_nonneg.mpr hΔ.le
    linarith
  have step1 : Δ ^ 2 * I ≤ Q ^ 2 * (3 * (Δ ^ 2 * m ^ 2 * (N + 1 / Δ))) := by
    calc Δ ^ 2 * I ≤ Δ ^ 2 * (len * B ^ 2) := mul_le_mul_of_nonneg_left hI (sq_nonneg Δ)
      _ ≤ Δ ^ 2 * (3 * (N + 1 / Δ) * (Q ^ 2 * m ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg Δ)
          exact mul_le_mul hlen hB2 (sq_nonneg B) hlen0
      _ = Q ^ 2 * (3 * (Δ ^ 2 * m ^ 2 * (N + 1 / Δ))) := by ring
  have step2 : Q ^ 2 * (3 * (Δ ^ 2 * m ^ 2 * (N + 1 / Δ))) ≤ Q ^ 2 * (6 * N) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Q); linarith
  have hNN' : (1 / N) * N = 1 := one_div_mul_cancel hN.ne'
  have hQ2 : Q ^ 2 * (6 * N) = 6 * C ^ 2 * T ^ 2 * k₁ ^ 2 * ((L + 4) * X) ^ 2 * (1 / N) := by
    rw [hQ]
    calc (C * T / N * ((L + 4) * X) * k₁) ^ 2 * (6 * N)
        = 6 * C ^ 2 * T ^ 2 * k₁ ^ 2 * ((L + 4) * X) ^ 2 * (1 / N) * ((1 / N) * N) := by ring
      _ = 6 * C ^ 2 * T ^ 2 * k₁ ^ 2 * ((L + 4) * X) ^ 2 * (1 / N) := by rw [hNN', mul_one]
  have hLX : ((L + 4) * X) ^ 2 ≤ 81 * (ℓ ^ 2 * Y ^ 2) := by
    have h3 : (L + 4) * X ≤ (3 * ℓ) * (3 * Y) := mul_le_mul hLℓ hXY hX (by linarith)
    have h0 : 0 ≤ (L + 4) * X := mul_nonneg hL hX
    calc ((L + 4) * X) ^ 2 ≤ ((3 * ℓ) * (3 * Y)) ^ 2 := pow_le_pow_left₀ h0 h3 2
      _ = 81 * (ℓ ^ 2 * Y ^ 2) := by ring
  have hNi : 1 / N ≤ 3 / N₀ := by rw [div_le_div_iff₀ hN hN₀]; linarith
  calc Δ ^ 2 * I ≤ 6 * C ^ 2 * T ^ 2 * k₁ ^ 2 * ((L + 4) * X) ^ 2 * (1 / N) := by linarith
    _ ≤ 6 * C ^ 2 * T ^ 2 * k₁ ^ 2 * (81 * (ℓ ^ 2 * Y ^ 2)) * (3 / N₀) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hLX (by positivity)) hNi (one_div_nonneg.mpr hN.le)
          (by positivity)
    _ = 1458 * C ^ 2 * k₁ ^ 2 * (T ^ 2 * Y ^ 2 * ℓ ^ 2 / N₀) := by ring

set_option maxHeartbeats 800000 in
open scoped Classical in
theorem Z5R_W' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → (r : ℝ) ≤ Real.exp s₀ →
      ∀ s : ℝ, |s - s₀| ≤ 1 →
      Δ ^ 2 * (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2) ≤ C * EerrW T (Real.exp s₀) r Δ := by
  obtain ⟨C, hC0, hC⟩ := mellin_Vxs_bounds κ hκ hκ1 Ξ hΞ f hf
  obtain ⟨C₁, hC₁0, hdig⟩ := ZR_digamma
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun u => (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  have hGi : Integrable G := by
    rw [hG]; exact integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = ∫ u, G u := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀]; exact integral_nonneg fun u => by simp only [hG]; positivity
  have hK0 : 0 ≤ C₁ * 10 * c₀ / (2 * Real.pi) :=
    div_nonneg (mul_nonneg (mul_nonneg hC₁0 (by norm_num)) hc₀0) (by positivity)
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℝ, k = 1 + C₁ * 10 * c₀ / (2 * Real.pi) := ⟨_, rfl⟩
  have hk₁0 : 0 ≤ k₁ := by rw [hk₁]; linarith
  refine ⟨1458 * C ^ 2 * k₁ ^ 2, ?_⟩
  intro s₀ T Δ hs₀ hT hΔ hΔ1 r _ χ hχ hrN s hs
  have hs1 := (abs_le.mp hs).1
  have hs2 := (abs_le.mp hs).2
  have hN1 : 1 ≤ Real.exp s := Real.one_le_exp (by linarith)
  have hN0 : 0 < Real.exp s := Real.exp_pos s
  have hT0 : 0 ≤ T := by linarith
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hNN : Real.exp s₀ ≤ 3 * Real.exp s := by
    have h := Real.exp_le_exp.mpr (show s₀ ≤ s + 1 by linarith)
    rw [Real.exp_add] at h
    linarith [mul_le_mul_of_nonneg_left he hN0.le]
  have hNN2 : Real.exp s ≤ 3 * Real.exp s₀ := by
    have h := Real.exp_le_exp.mpr (show s ≤ s₀ + 1 by linarith)
    rw [Real.exp_add] at h
    linarith [mul_le_mul_of_nonneg_left he (Real.exp_pos s₀).le]
  have hm0 : 0 ≤ min (1 / Δ) (Real.exp s) := le_min (by positivity) hN0.le
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = C * T * min (1 / Δ) (Real.exp s) / Real.exp s := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = T + Δ * Real.exp s + 1 := ⟨_, rfl⟩
  have hΔN : 0 ≤ Δ * Real.exp s := by positivity
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hX0 : 0 < X := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  have hrX : (1 : ℝ) ≤ r * X := one_le_mul_of_one_le_of_one_le hr1 hX1
  have hL0 : 0 ≤ Real.log (r * X) := Real.log_nonneg hrX
  -- the two Mellin bounds on the lines used
  have hre : ∀ t : ℝ, (1 / 2 + (t : ℂ) * I).re = 1 / 2 := fun t => by simp
  have hw0 : ∀ t : ℝ, (1 / 2 + (t : ℂ) * I) ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp at this
  have hnw : ∀ t : ℝ, ‖(1 / 2 + (t : ℂ) * I)‖ ^ 2 = 1 / 4 + t ^ 2 := fun t => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hb0 : ∀ (x : ℝ) (w : ℂ), 0 ≤ w.re → w.re ≤ 1 / 2 → ‖mellin (VxsW T κ Ξ f Δ s x) w‖ ≤ A := by
    intro x w h0 h1
    refine (hC s₀ T Δ s hs₀ hT hΔ hΔ1 hs x w h0 (by linarith)).1.trans ?_
    have hp : Real.exp s ^ (w.re - 1 / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    rw [hA]
    calc C * T * Real.exp s ^ (w.re - 1 / 2) * min (1 / Δ) (Real.exp s) / Real.exp s
        ≤ C * T * 1 * min (1 / Δ) (Real.exp s) / Real.exp s := by gcongr
      _ = C * T * min (1 / Δ) (Real.exp s) / Real.exp s := by ring
  have hb2 : ∀ (x t : ℝ), ‖mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)‖ ≤ A * X ^ 2 / (1 / 4 + t ^ 2) := by
    intro x t
    have h := (hC s₀ T Δ s hs₀ hT hΔ hΔ1 hs x (1 / 2 + t * I) (by rw [hre]; norm_num)
      (by rw [hre]; norm_num)).2 (hw0 t)
    have hp : Real.exp s ^ ((1 / 2 + (t : ℂ) * I).re - 1 / 2) = 1 := by rw [hre, sub_self, Real.rpow_zero]
    rw [hp, hnw] at h
    refine h.trans (le_of_eq ?_)
    rw [hA, hX]; ring
  -- (a5): pointwise bound for the `t`-integrand
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 10 * A * C₁ * (Real.log (r * X) + 4) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) hC₁0) (by linarith)
  have hpt : ∀ (x t : ℝ), ‖mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)
      * (((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
          + Real.log (r / Real.pi) : ℝ) : ℂ)‖ ≤ M * G (t / X) := by
    intro x t
    have hv0 := norm_nonneg (mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I))
    have h0 := hb0 x (1 / 2 + t * I) (by rw [hre]; norm_num) (by rw [hre])
    have hmin := ZR_min_scaled _ A X t hA0 hX1 hv0 h0 (hb2 x t)
    have hq' : 0 < 1 / 4 + (t / X) ^ 2 := by positivity
    have hv : ‖mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)‖ ≤ 5 / 4 * A / (1 / 4 + (t / X) ^ 2) :=
      (le_div_iff₀ hq').mpr hmin
    have hd := hdig r (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)) (if χ.Even then 0 else 1)
      (by split_ifs <;> norm_num) t
    have hlog : Real.log (r * (|t| + 2)) ≤ Real.log (r * X * (|t / X| + 2)) := by
      apply Real.log_le_log (mul_pos (by linarith) (by positivity))
      have hXt : X * (|t| / X) = |t| := by field_simp
      have e : r * X * (|t / X| + 2) = r * (|t| + 2 * X) := by
        rw [abs_div, abs_of_pos hX0]
        calc (r : ℝ) * X * (|t| / X + 2) = r * (X * (|t| / X)) + r * (2 * X) := by ring
          _ = r * (|t| + 2 * X) := by rw [hXt]; ring
      rw [e]; apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    have hd' : |(Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
          + Real.log (r / Real.pi)| ≤ C₁ * Real.log (r * X * (|t / X| + 2)) :=
      hd.trans (mul_le_mul_of_nonneg_left hlog hC₁0)
    have hlq := log_div_quad_le (r * X) hrX (t / X)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs := abs_nonneg ((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
          + Real.log (r / Real.pi))
    have hAC : 0 ≤ 5 / 4 * A * C₁ := mul_nonneg (mul_nonneg (by norm_num) hA0) hC₁0
    calc ‖mellin (VxsW T κ Ξ f Δ s x) (1 / 2 + t * I)‖
          * |(Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
            + Real.log (r / Real.pi)|
        ≤ (5 / 4 * A / (1 / 4 + (t / X) ^ 2)) * (C₁ * Real.log (r * X * (|t / X| + 2))) :=
          mul_le_mul hv hd' habs (div_nonneg (mul_nonneg (by norm_num) hA0) hq'.le)
      _ = 5 / 4 * A * C₁ * (Real.log (r * X * (|t / X| + 2)) / (1 / 4 + (t / X) ^ 2)) := by ring
      _ ≤ 5 / 4 * A * C₁ * (8 * (Real.log (r * X) + 4) * (1 + |t / X|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hlq hAC
      _ = M * G (t / X) := by simp only [hM, hG, Real.norm_eq_abs]; ring
  have hgi : Integrable (fun t : ℝ => M * G (t / X)) := (hGi.comp_div hX0.ne').const_mul M
  have hint : (∫ t : ℝ, M * G (t / X)) = M * (X * c₀) := by
    rw [integral_const_mul, MeasureTheory.Measure.integral_comp_div G X, abs_of_pos hX0, smul_eq_mul, hc₀]
  have hc2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = A + 1 / (2 * Real.pi) * (M * (X * c₀)) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]; have : 0 ≤ M * (X * c₀) := mul_nonneg hM0 (mul_nonneg hX0.le hc₀0)
    have : 0 ≤ 1 / (2 * Real.pi) * (M * (X * c₀)) := mul_nonneg (by positivity) this
    linarith
  have hrs : ∀ x : ℝ, ‖remPartW χ T κ Ξ f Δ s x‖ ≤ B := by
    intro x
    rw [hB]
    unfold remPartW
    refine (norm_add_le _ _).trans ?_
    gcongr
    · split_ifs
      · exact hb0 x 0 (by simp) (by norm_num)
      · simpa using hA0
    · rw [norm_mul, hc2]
      gcongr
      rw [← hint]
      exact norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall (hpt x))
  -- (a8): support in `x`
  have hzero : ∀ x, x ∉ Set.Icc (Real.exp (s - κ) - 1 / (8 * Δ)) (Real.exp (s + κ) + 1 / (8 * Δ)) →
      remPartW χ T κ Ξ f Δ s x = 0 := by
    intro x hx
    simp only [remPartW, VxsW_eq_zero_of_far T κ hκ Ξ hΞ f hf Δ hΔ s x hx, mellin, smul_zero,
      MeasureTheory.integral_zero, zero_mul, mul_zero, ite_self, zero_add]
  have h8 : 0 ≤ 1 / (8 * Δ) := by positivity
  have hab : Real.exp (s - κ) - 1 / (8 * Δ) ≤ Real.exp (s + κ) + 1 / (8 * Δ) := by
    have := Real.exp_le_exp.mpr (show s - κ ≤ s + κ by linarith); linarith
  have hle : ∀ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2
      ≤ (Set.Icc (Real.exp (s - κ) - 1 / (8 * Δ)) (Real.exp (s + κ) + 1 / (8 * Δ))).indicator
          (fun _ => B ^ 2) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (Real.exp (s - κ) - 1 / (8 * Δ)) (Real.exp (s + κ) + 1 / (8 * Δ))
    · rw [Set.indicator_of_mem hx]; exact pow_le_pow_left₀ (norm_nonneg _) (hrs x) 2
    · rw [Set.indicator_of_notMem hx, hzero x hx]; simp
  have hind : Integrable ((Set.Icc (Real.exp (s - κ) - 1 / (8 * Δ)) (Real.exp (s + κ) + 1 / (8 * Δ))).indicator
      (fun _ => B ^ 2)) :=
    (integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  have hI : (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2)
      ≤ ((Real.exp (s + κ) + 1 / (8 * Δ)) - (Real.exp (s - κ) - 1 / (8 * Δ))) * B ^ 2 := by
    calc (∫ x, ‖remPartW χ T κ Ξ f Δ s x‖ ^ 2)
        ≤ ∫ x, (Set.Icc (Real.exp (s - κ) - 1 / (8 * Δ)) (Real.exp (s + κ) + 1 / (8 * Δ))).indicator
            (fun _ => B ^ 2) x :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity)
            hind (Filter.Eventually.of_forall hle)
      _ = _ := by rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hab, smul_eq_mul]
  have hlen : (Real.exp (s + κ) + 1 / (8 * Δ)) - (Real.exp (s - κ) - 1 / (8 * Δ)) ≤ 3 * (Real.exp s + 1 / Δ) := by
    have h1 : Real.exp (s + κ) ≤ 3 * Real.exp s := by
      calc Real.exp (s + κ) ≤ Real.exp (s + 1) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp s * Real.exp 1 := Real.exp_add s 1
        _ ≤ Real.exp s * 3 := mul_le_mul_of_nonneg_left he hN0.le
        _ = 3 * Real.exp s := by ring
    have h2 : 1 / (8 * Δ) ≤ 1 / Δ := one_div_le_one_div_of_le hΔ (by linarith)
    have h3 : 0 ≤ Real.exp (s - κ) := (Real.exp_pos _).le
    have h4 : 0 ≤ 1 / Δ := by positivity
    linarith
  -- `B ≤ A (L+4) X k₁`
  have hq1 : 1 ≤ (Real.log (r * X) + 4) * X :=
    le_trans (by norm_num : (1 : ℝ) ≤ 4 * 1) (mul_le_mul (by linarith) hX1 (by norm_num) (by linarith))
  have hBle : B ≤ C * T * min (1 / Δ) (Real.exp s) / Real.exp s * ((Real.log (r * X) + 4) * X) * k₁ := by
    rw [← hA, hB, hM, hk₁]
    have e : A + 1 / (2 * Real.pi) * (10 * A * C₁ * (Real.log (r * X) + 4) * (X * c₀))
        = A * (1 + C₁ * 10 * c₀ / (2 * Real.pi) * ((Real.log (r * X) + 4) * X)) := by ring
    rw [e]
    have : 1 + C₁ * 10 * c₀ / (2 * Real.pi) * ((Real.log (r * X) + 4) * X)
        ≤ (Real.log (r * X) + 4) * X * (1 + C₁ * 10 * c₀ / (2 * Real.pi)) := by
      have e2 : (Real.log (r * X) + 4) * X * (1 + C₁ * 10 * c₀ / (2 * Real.pi))
          - (1 + C₁ * 10 * c₀ / (2 * Real.pi) * ((Real.log (r * X) + 4) * X))
          = (Real.log (r * X) + 4) * X - 1 := by ring
      linarith
    calc A * (1 + C₁ * 10 * c₀ / (2 * Real.pi) * ((Real.log (r * X) + 4) * X))
        ≤ A * ((Real.log (r * X) + 4) * X * (1 + C₁ * 10 * c₀ / (2 * Real.pi))) :=
          mul_le_mul_of_nonneg_left this hA0
      _ = _ := by ring
  -- conversions `N ↔ N₀`
  have hN₀4 : 4 ≤ Real.exp s₀ := by
    have := Real.add_one_le_exp (3 : ℝ)
    have := Real.exp_le_exp.mpr hs₀; linarith
  have hXY : X ≤ 3 * (T + Δ * Real.exp s₀ + 1) := by
    have h : Δ * Real.exp s ≤ 3 * (Δ * Real.exp s₀) := by
      calc Δ * Real.exp s ≤ Δ * (3 * Real.exp s₀) := mul_le_mul_of_nonneg_left hNN2 hΔ.le
        _ = 3 * (Δ * Real.exp s₀) := by ring
    rw [hX]; linarith
  have hℓ3 : 3 ≤ Real.log (r * Real.exp s₀ * T) := by
    have h1 : Real.exp s₀ ≤ r * Real.exp s₀ * T := by
      have h5 : Real.exp s₀ ≤ r * Real.exp s₀ := le_mul_of_one_le_left (Real.exp_pos _).le hr1
      have h6 : r * Real.exp s₀ ≤ r * Real.exp s₀ * T :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      linarith
    have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this; linarith
  have hLℓ : Real.log (r * X) + 4 ≤ 3 * Real.log (r * Real.exp s₀ * T) := by
    have hY : T + Δ * Real.exp s₀ + 1 ≤ Real.exp s₀ * T := by
      have h5 : Δ * Real.exp s₀ ≤ Real.exp s₀ := mul_le_of_le_one_left (Real.exp_pos _).le hΔ1
      have h6 : 3 * 1 ≤ (Real.exp s₀ - 1) * (T - 1) :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
      have e : (Real.exp s₀ - 1) * (T - 1) = Real.exp s₀ * T - Real.exp s₀ - T + 1 := by ring
      linarith
    have h1 : r * X ≤ 3 * (r * Real.exp s₀ * T) := by
      have h7 : X ≤ 3 * (Real.exp s₀ * T) := by linarith
      calc (r : ℝ) * X ≤ r * (3 * (Real.exp s₀ * T)) := mul_le_mul_of_nonneg_left h7 (by linarith)
        _ = 3 * (r * Real.exp s₀ * T) := by ring
    have h2 := Real.log_le_log (by linarith) h1
    have hpos3 : (0 : ℝ) < r * Real.exp s₀ * T := mul_pos (mul_pos (by linarith) (Real.exp_pos _)) (by linarith)
    rw [Real.log_mul (show (3 : ℝ) ≠ 0 by norm_num) hpos3.ne'] at h2
    have h3 : Real.log 3 ≤ 2 := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    linarith
  have hfin := ZR_final_alg C k₁ Δ (Real.exp s) (Real.exp s₀) T (min (1 / Δ) (Real.exp s)) X
    (Real.log (r * X)) (Real.log (r * Real.exp s₀ * T)) (T + Δ * Real.exp s₀ + 1) B _ _
    hC0 hk₁0 hΔ hN0 (Real.exp_pos _) hT0 hm0 (min_le_left _ _) (min_le_right _ _) hX0.le (by linarith)
    hB0 hBle hlen hI hNN hXY hLℓ
  refine hfin.trans ?_
  unfold EerrW
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_add_of_nonneg_left (by positivity)

end ZetaShell.PropZ
