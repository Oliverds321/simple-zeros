/-
A2a_S5_Window (L7_8, round 2): **Step 5 of the proof of Lemma 2(a)** (sec_shell.tex l.351–354): the window average
of the profile, given Lemma P's conclusion with a constant `B`. (L7_8: open; L7_11: proved, see below.) Tested numerically
(`numerics/step35_test.py`).

If `|g_r(v) − ḡ| ≤ B(1+log v)²/v` for all `r ≥ 1`, `v ≥ 1` (Lemma P; `g_r = 0` on `[0,1)` by definition), then for
`1 ≤ K ≤ u = rQ|η|`, `δ > 0`: `|∫_{η−δ/2}^{η+δ/2} Q² g_r(rQ|β|) dβ − δQ²ḡ| ≤ C δ Q² (1+log K)³/K`.
Proof (draft, checked by hand): in `u`-units the window is `[u − Δ, u + Δ]`, `Δ = rQδ/2`; if `Δ ≤ u/2` the average of
`E = |g − ḡ|` is `≤ max_{[u/2, 3u/2]} E ≪ (B + ḡ)(1+log K)²/K`; if `Δ > u/2 ≥ K/2` it is
`≤ (2Δ)⁻¹·2∫_0^{3Δ} E ≪ (B + ḡ)(1+log K)³/K` (`(1+log x)³/x` decreasing for `x ≥ e²`).

L7_11 (28 Sep 2026): PROVED (no sorry), statement unchanged. Route: `gProf F r` is measurable (it is
`(v, ⌊v⌋₊) ↦ G`, measurable on `ℝ × ℕ`); `|g_r(v) − ḡ| ≤ 2(B + ḡ)·φ(v + 1)` for all `v ≥ 0`, `φ(x) = (1+log x)²/x`
(for `v < 1`, `g_r(v) = 0`); this continuous majorant gives integrability and the bound. Case `δ ≤ |η|`: pointwise,
via `(1+log x)ⁿ/x ≤ 3·n!·(1+log y)ⁿ/y` for `x ≥ y ≥ 1`. Case `δ > |η|`: enlarge to `[−L, L]`, symmetry, and the
antiderivative `(1 + log(cβ+1))³/(3c)`. Constant `C = 700(B + ḡ)`.
-/
import ZetaShell.Lemma2.A2a_StepDefs

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace TrackF

/-! ### L7_11: auxiliary lemmas for `step5_window` -/

/-- `(1 + log t)ⁿ ≤ 3·n!·t` for `t ≥ 1` (from `sⁿ/n! ≤ eˢ`, `s = 1 + log t`). -/
theorem one_add_log_pow_le (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    (1 + Real.log t) ^ n ≤ (n.factorial : ℝ) * 3 * t := by
  have hl : 0 ≤ Real.log t := Real.log_nonneg ht
  have hs : 0 ≤ 1 + Real.log t := by linarith
  have h1 := Real.pow_div_factorial_le_exp _ hs n
  have he : Real.exp (1 + Real.log t) = Real.exp 1 * t := by
    rw [Real.exp_add, Real.exp_log (by linarith)]
  rw [he] at h1
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h1
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have ht0 : 0 ≤ t := by linarith
  calc (1 + Real.log t) ^ n ≤ Real.exp 1 * t * n.factorial := h1
    _ ≤ 3 * t * n.factorial := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he3 ht0) hf.le
    _ = (n.factorial : ℝ) * 3 * t := by ring

/-- `(1 + log x)ⁿ/x ≤ 3·n!·(1 + log y)ⁿ/y` for `x ≥ y ≥ 1`. -/
theorem log_ratio_le (n : ℕ) {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) :
    (1 + Real.log x) ^ n / x ≤ (n.factorial : ℝ) * 3 * ((1 + Real.log y) ^ n / y) := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  set t := x / y with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hy0]; linarith
  have ht0 : t ≠ 0 := by linarith
  have hxt : x = y * t := by rw [ht]; field_simp
  have hlog : Real.log x = Real.log y + Real.log t := by
    rw [hxt, Real.log_mul hy0.ne' ht0]
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hle : 1 + Real.log x ≤ (1 + Real.log y) * (1 + Real.log t) := by
    rw [hlog]; nlinarith
  have h0 : 0 ≤ 1 + Real.log x := by rw [hlog]; linarith
  have hpow : (1 + Real.log x) ^ n ≤ (1 + Real.log y) ^ n * (1 + Real.log t) ^ n := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h0 hle n
  have hT := one_add_log_pow_le n ht1
  have hA : 0 ≤ (1 + Real.log y) ^ n := pow_nonneg (by linarith) n
  calc (1 + Real.log x) ^ n / x ≤ (1 + Real.log y) ^ n * ((n.factorial : ℝ) * 3 * t) / x := by
        rw [div_le_div_iff_of_pos_right hx0]
        exact hpow.trans (mul_le_mul_of_nonneg_left hT hA)
    _ = (n.factorial : ℝ) * 3 * ((1 + Real.log y) ^ n / y) := by
        rw [hxt]; field_simp

theorem gProf_eq_zero_of_lt_one (F : Fam) (r : ℕ) {v : ℝ} (h1 : v < 1) : gProf F r v = 0 := by
  unfold gProf
  have : ⌊v⌋₊ = 0 := Nat.floor_eq_zero.mpr h1
  simp [this]

/-- the majorant profile `φ(x) = (1 + log x)²/x`. -/
def phiL (x : ℝ) : ℝ := (1 + Real.log x) ^ 2 / x

theorem abs_gProf_sub_le (F : Fam) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ r : ℕ, 1 ≤ r → ∀ v : ℝ, 1 ≤ v → |gProf F r v - gbar F| ≤ B * (1 + Real.log v) ^ 2 / v)
    (r : ℕ) (hr : 1 ≤ r) {v : ℝ} (hv : 0 ≤ v) :
    |gProf F r v - gbar F| ≤ 2 * (B + gbar F) * phiL (v + 1) := by
  have hg := gbar_pos F
  have hv1 : 1 ≤ v + 1 := by linarith
  have hlog1 : 0 ≤ Real.log (v + 1) := Real.log_nonneg hv1
  have hphi : 0 ≤ (1 + Real.log (v + 1)) ^ 2 / (v + 1) := by positivity
  unfold phiL
  by_cases hv' : v < 1
  · rw [gProf_eq_zero_of_lt_one F r hv', zero_sub, abs_neg, abs_of_pos hg]
    have h2 : (1 : ℝ) / 2 ≤ (1 + Real.log (v + 1)) ^ 2 / (v + 1) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    nlinarith
  · push_neg at hv'
    refine (hP r hr v hv').trans ?_
    have hv0 : 0 < v := by linarith
    have hlv : 0 ≤ Real.log v := Real.log_nonneg hv'
    have hlog : Real.log v ≤ Real.log (v + 1) := Real.log_le_log hv0 (by linarith)
    have hsq : (1 + Real.log v) ^ 2 ≤ (1 + Real.log (v + 1)) ^ 2 := by nlinarith
    have hA : 0 ≤ (1 + Real.log (v + 1)) ^ 2 := sq_nonneg _
    have key : B * (1 + Real.log v) ^ 2 / v ≤ 2 * B * ((1 + Real.log (v + 1)) ^ 2 / (v + 1)) := by
      rw [div_le_iff₀ hv0]
      have e : 2 * B * ((1 + Real.log (v + 1)) ^ 2 / (v + 1)) * v
          = B * (1 + Real.log (v + 1)) ^ 2 * (2 * v / (v + 1)) := by
        field_simp
      rw [e]
      have h2v : 1 ≤ 2 * v / (v + 1) := by rw [le_div_iff₀ (by linarith)]; linarith
      have h3 := mul_le_mul_of_nonneg_left hsq hB
      have h4 : 0 ≤ B * (1 + Real.log (v + 1)) ^ 2 := mul_nonneg hB hA
      nlinarith
    have h5 := mul_nonneg hg.le hphi
    nlinarith

theorem Fam.measurable_w (F : Fam) : Measurable F.w := by
  cases F
  · show Measurable (fun x : ℝ => if 0 ≤ x ∧ x ≤ 1 then (1 : ℝ) else 0)
    exact Measurable.ite (measurableSet_Icc (a := (0 : ℝ)) (b := 1)) measurable_const measurable_const
  · show Measurable (fun x : ℝ => if 1 / 2 < x ∧ x ≤ 1 then (1 : ℝ) else 0)
    exact Measurable.ite (measurableSet_Ioc (a := (1 / 2 : ℝ)) (b := 1)) measurable_const measurable_const
  · show Measurable (fun x : ℝ => if 0 ≤ x ∧ x ≤ 1 then (1 - x) ^ 2 else 0)
    exact Measurable.ite (measurableSet_Icc (a := (0 : ℝ)) (b := 1))
      ((measurable_const.sub measurable_id).pow_const 2) measurable_const

theorem measurable_gProf (F : Fam) (r : ℕ) : Measurable (gProf F r) := by
  have hw := F.measurable_w
  let G : ℝ × ℕ → ℝ := fun p => (p.1 ^ 2)⁻¹ * ∑ j ∈ Finset.Icc 1 p.2, (Nat.totient j : ℝ) *
      ∑ e ∈ Finset.Icc 1 p.2, cE F.kind e * F.w ((j : ℝ) * e / p.1) * Ecoef F.kind r j e
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro n
    show Measurable (fun x : ℝ => (x ^ 2)⁻¹ * ∑ j ∈ Finset.Icc 1 n, (Nat.totient j : ℝ) *
      ∑ e ∈ Finset.Icc 1 n, cE F.kind e * F.w ((j : ℝ) * e / x) * Ecoef F.kind r j e)
    refine Measurable.mul ((measurable_id.pow_const 2).inv) ?_
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ (fun e _ => ?_)
    refine Measurable.mul_const ?_ _
    refine Measurable.const_mul ?_ _
    exact hw.comp (measurable_const.div measurable_id)
  have : gProf F r = fun v => G (v, ⌊v⌋₊) := by funext v; rfl
  rw [this]
  exact hG.comp (measurable_id.prodMk Nat.measurable_floor)

set_option maxHeartbeats 1000000 in
theorem step5_window (F : Fam) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ r : ℕ, 1 ≤ r → ∀ v : ℝ, 1 ≤ v → |gProf F r v - gbar F| ≤ B * (1 + Real.log v) ^ 2 / v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q r : ℕ) (η δ K : ℝ), 1 ≤ Q → 1 ≤ r → 0 < δ → 1 ≤ K → K ≤ r * Q * |η| →
      |mProf F Q r η δ - δ * (Q : ℝ) ^ 2 * gbar F| ≤ C * δ * (Q : ℝ) ^ 2 * ((1 + Real.log K) ^ 3 / K) := by
  have hg := gbar_pos F
  refine ⟨700 * (B + gbar F), by positivity, ?_⟩
  intro Q r η δ K hQ hr hδ hK hKu
  set g0 := gbar F with hg0
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hc1 : (1 : ℝ) ≤ (r : ℝ) * Q := by nlinarith
  set c : ℝ := (r : ℝ) * Q with hc
  have hc0 : 0 < c := by linarith
  have hK0 : 0 < K := by linarith
  set a := η - δ / 2 with ha
  set b := η + δ / 2 with hb
  have hab : a ≤ b := by linarith
  have hba : b - a = δ := by linarith
  set A : ℝ := (Q : ℝ) ^ 2 * (2 * (B + g0)) with hA
  have hA0 : 0 ≤ A := by positivity
  -- the continuous majorant
  set P : ℝ → ℝ := fun β => phiL (c * |β| + 1) with hPdef
  have hpos : ∀ β : ℝ, 0 < c * |β| + 1 := fun β => by positivity
  have hlin : Continuous (fun β : ℝ => c * |β| + 1) :=
    (continuous_const.mul continuous_abs).add continuous_const
  have hPcont : Continuous P := by
    simp only [hPdef, phiL]
    exact ((continuous_const.add (hlin.log (fun β => (hpos β).ne'))).pow 2).div hlin
      (fun β => (hpos β).ne')
  have hP0 : ∀ β, 0 ≤ P β := by
    intro β
    simp only [hPdef, phiL]
    have := Real.log_nonneg (show (1 : ℝ) ≤ c * |β| + 1 by have := hpos β; nlinarith [abs_nonneg β])
    positivity
  -- the integrand
  set f : ℝ → ℝ := fun β => (Q : ℝ) ^ 2 * gProf F r (c * |β|) with hfdef
  have hfm : Measurable f :=
    measurable_const.mul ((measurable_gProf F r).comp (continuous_const.mul continuous_abs).measurable)
  have hpt : ∀ β, |f β - (Q : ℝ) ^ 2 * g0| ≤ A * P β := by
    intro β
    have h := abs_gProf_sub_le F B hB hP r hr (v := c * |β|) (by positivity)
    simp only [hfdef, hPdef, hA]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Q : ℝ) ^ 2)]
    have hQ2 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := by positivity
    calc (Q : ℝ) ^ 2 * |gProf F r (c * |β|) - g0|
        ≤ (Q : ℝ) ^ 2 * (2 * (B + g0) * phiL (c * |β| + 1)) := mul_le_mul_of_nonneg_left h hQ2
      _ = (Q : ℝ) ^ 2 * (2 * (B + g0)) * phiL (c * |β| + 1) := by ring
  have hfint : IntervalIntegrable f volume a b := by
    have hgc : Continuous (fun β => A * P β + (Q : ℝ) ^ 2 * g0) :=
      (continuous_const.mul hPcont).add continuous_const
    refine IntervalIntegrable.mono_fun' (hgc.intervalIntegrable a b)
      hfm.aestronglyMeasurable (Filter.Eventually.of_forall (fun β => ?_))
    simp only [Real.norm_eq_abs]
    have h1 := hpt β
    have h2 : |f β| ≤ |f β - (Q : ℝ) ^ 2 * g0| + |(Q : ℝ) ^ 2 * g0| := by
      have := abs_add_le (f β - (Q : ℝ) ^ 2 * g0) ((Q : ℝ) ^ 2 * g0)
      simpa using this
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Q : ℝ) ^ 2 * g0)] at h2
    linarith
  have hm : mProf F Q r η δ = ∫ β in a..b, f β := rfl
  have hsub : mProf F Q r η δ - δ * (Q : ℝ) ^ 2 * g0 = ∫ β in a..b, (f β - (Q : ℝ) ^ 2 * g0) := by
    rw [hm, intervalIntegral.integral_sub hfint intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
    rw [hba]; ring
  have hAPc : Continuous (fun β => A * P β) := continuous_const.mul hPcont
  have hMint : ∀ u v : ℝ, IntervalIntegrable (fun β => A * P β) volume u v :=
    fun u v => hAPc.intervalIntegrable u v
  have hbound : |∫ β in a..b, (f β - (Q : ℝ) ^ 2 * g0)| ≤ ∫ β in a..b, A * P β := by
    have := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun β _ => by rw [Real.norm_eq_abs]; exact hpt β)) (hMint a b)
    rwa [Real.norm_eq_abs] at this
  rw [hsub]
  refine hbound.trans ?_
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hTK : 0 ≤ (1 + Real.log K) ^ 3 / K := by positivity
  -- target: ∫ A P ≤ 700 (B + g0) δ Q² (1+log K)³/K = 350 A δ (1+log K)³/K
  have htarget : 700 * (B + g0) * δ * (Q : ℝ) ^ 2 * ((1 + Real.log K) ^ 3 / K)
      = 350 * A * δ * ((1 + Real.log K) ^ 3 / K) := by rw [hA]; ring
  rw [htarget]
  by_cases hcase : δ ≤ |η|
  · -- Case 1: the window stays at distance `≥ |η|/2` from `0`.
    set y : ℝ := (K + 1) / 2 with hy
    have hy1 : 1 ≤ y := by rw [hy]; linarith
    have hyK : y ≤ K := by rw [hy]; linarith
    have hPy : phiL y ≤ 2 * ((1 + Real.log K) ^ 3 / K) := by
      unfold phiL
      have hly : 0 ≤ Real.log y := Real.log_nonneg hy1
      have hlyK : Real.log y ≤ Real.log K := Real.log_le_log (by linarith) hyK
      have hs1 : (1 + Real.log y) ^ 2 ≤ (1 + Real.log K) ^ 2 := by nlinarith
      have hs2 : (1 + Real.log K) ^ 2 ≤ (1 + Real.log K) ^ 3 := by
        have : 1 ≤ 1 + Real.log K := by linarith
        nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.log K) 2]
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) hK0]
      have h3 : 0 ≤ (1 + Real.log K) ^ 3 := by positivity
      nlinarith
    have hptw : ∀ β ∈ Set.Icc a b, A * P β ≤ A * (12 * ((1 + Real.log K) ^ 3 / K)) := by
      intro β hβ
      apply mul_le_mul_of_nonneg_left _ hA0
      have hβη : |η| ≤ |β| + δ / 2 := by
        have h1 : |η| ≤ |β| + |η - β| := by
          have := abs_add_le β (η - β); simp only [add_sub_cancel] at this; linarith
        have h2 : |η - β| ≤ δ / 2 := by
          rw [abs_le]; constructor <;> linarith [hβ.1, hβ.2]
        linarith
      have hx : y ≤ c * |β| + 1 := by
        have h1 : c * |η| ≤ c * (|β| + δ / 2) := mul_le_mul_of_nonneg_left hβη hc0.le
        have h2 : c * δ ≤ c * |η| := mul_le_mul_of_nonneg_left hcase hc0.le
        rw [hy]; nlinarith
      have := log_ratio_le 2 hy1 hx
      simp only [hPdef]
      unfold phiL at hPy ⊢
      norm_num [Nat.factorial] at this
      linarith
    calc ∫ β in a..b, A * P β ≤ ∫ β in a..b, A * (12 * ((1 + Real.log K) ^ 3 / K)) :=
          intervalIntegral.integral_mono_on hab (hMint a b) intervalIntegrable_const hptw
      _ = (b - a) * (A * (12 * ((1 + Real.log K) ^ 3 / K))) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = δ * (A * (12 * ((1 + Real.log K) ^ 3 / K))) := by rw [hba]
      _ ≤ 350 * A * δ * ((1 + Real.log K) ^ 3 / K) := by
          have h0 : 0 ≤ A * δ * ((1 + Real.log K) ^ 3 / K) := by positivity
          have e : 350 * A * δ * ((1 + Real.log K) ^ 3 / K) - δ * (A * (12 * ((1 + Real.log K) ^ 3 / K)))
              = 338 * (A * δ * ((1 + Real.log K) ^ 3 / K)) := by ring
          linarith
  · -- Case 2: `|η| < δ`; enlarge to `[−L, L]`, `L = |η| + δ/2`.
    push_neg at hcase
    set L : ℝ := |η| + δ / 2 with hL
    have hL0 : 0 ≤ L := by positivity
    have haL : -L ≤ a := by rw [ha, hL]; linarith [neg_abs_le η]
    have hbL : b ≤ L := by rw [hb, hL]; linarith [le_abs_self η]
    have h1 : ∫ β in a..b, A * P β ≤ ∫ β in (-L)..L, A * P β :=
      intervalIntegral.integral_mono_interval haL hab hbL
        (Filter.Eventually.of_forall (fun β => mul_nonneg hA0 (hP0 β))) (hMint (-L) L)
    have hsym : ∫ β in (-L)..0, A * P β = ∫ β in (0 : ℝ)..L, A * P β := by
      have h := intervalIntegral.integral_comp_neg (a := 0) (b := L) (fun β => A * P β)
      rw [neg_zero] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [hPdef, abs_neg]
    have hsplit : ∫ β in (-L)..L, A * P β = 2 * ∫ β in (0 : ℝ)..L, A * P β := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hMint (-L) 0) (hMint 0 L), hsym]
      ring
    -- the antiderivative on `[0, L]`
    have hderiv : ∀ β ∈ Set.uIcc 0 L,
        HasDerivAt (fun β => (1 + Real.log (c * β + 1)) ^ 3 / (3 * c)) (P β) β := by
      intro β hβ
      rw [Set.uIcc_of_le hL0] at hβ
      have hβ0 : 0 ≤ β := hβ.1
      have hpβ : 0 < c * β + 1 := by positivity
      have hd1 : HasDerivAt (fun β => c * β + 1) c β := by
        simpa using ((hasDerivAt_id β).const_mul c).add_const 1
      have hd2 := (((hd1.log hpβ.ne').const_add 1).pow 3).div_const (3 * c)
      have e1 : P β = (1 + Real.log (c * β + 1)) ^ 2 / (c * β + 1) := by
        show phiL (c * |β| + 1) = _
        rw [phiL, abs_of_nonneg hβ0]
      rw [e1]
      refine hd2.congr_deriv ?_
      field_simp
      ring
    have hFTC : ∫ β in (0 : ℝ)..L, P β
        = (1 + Real.log (c * L + 1)) ^ 3 / (3 * c) - (1 + Real.log (c * 0 + 1)) ^ 3 / (3 * c) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hPcont.intervalIntegrable 0 L)
    have hFTC' : ∫ β in (0 : ℝ)..L, P β ≤ (1 + Real.log (c * L + 1)) ^ 3 / (3 * c) := by
      rw [hFTC]
      have : 0 ≤ (1 + Real.log (c * 0 + 1)) ^ 3 / (3 * c) := by
        simp only [mul_zero, zero_add, Real.log_one, add_zero, one_pow]; positivity
      linarith
    -- estimate `(1 + log X)³/c` with `X = cL + 1 ≤ 3D`, `D = cδ ≥ K`
    set D : ℝ := c * δ with hD
    have hDK : K ≤ D := by
      have : c * |η| ≤ c * δ := mul_le_mul_of_nonneg_left hcase.le hc0.le
      rw [hD]; linarith
    have hD1 : 1 ≤ D := le_trans hK hDK
    set X : ℝ := c * L + 1 with hX
    have hX1 : 1 ≤ X := by rw [hX]; nlinarith
    have hX3 : X ≤ 3 * D := by
      have : c * |η| ≤ c * δ := mul_le_mul_of_nonneg_left hcase.le hc0.le
      rw [hX, hL, hD]; nlinarith
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    have hlD : 0 ≤ Real.log D := Real.log_nonneg hD1
    have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hXD : 1 + Real.log X ≤ 3 * (1 + Real.log D) := by
      have h := Real.log_le_log (by linarith) hX3
      rw [Real.log_mul (by norm_num) (by linarith)] at h
      linarith
    have hXD3 : (1 + Real.log X) ^ 3 ≤ 27 * (1 + Real.log D) ^ 3 := by
      have := pow_le_pow_left₀ (by linarith) hXD 3
      rw [mul_pow] at this; norm_num at this; linarith
    have hDK3 := log_ratio_le 3 hK hDK
    norm_num [Nat.factorial] at hDK3
    have hfin : (1 + Real.log X) ^ 3 / (3 * c) ≤ 162 * δ * ((1 + Real.log K) ^ 3 / K) := by
      have e : (1 + Real.log X) ^ 3 / (3 * c) = δ / 3 * ((1 + Real.log X) ^ 3 / D) := by
        rw [hD]; field_simp
      rw [e]
      have h2 : (1 + Real.log X) ^ 3 / D ≤ 27 * ((1 + Real.log D) ^ 3 / D) := by
        rw [mul_div_assoc']; exact (div_le_div_iff_of_pos_right (by linarith)).mpr hXD3
      have h3 : (1 + Real.log X) ^ 3 / D ≤ 27 * (18 * ((1 + Real.log K) ^ 3 / K)) := by
        refine h2.trans ?_
        have := mul_le_mul_of_nonneg_left hDK3 (by norm_num : (0 : ℝ) ≤ 27)
        linarith
      have hδ3 : 0 ≤ δ / 3 := by positivity
      have := mul_le_mul_of_nonneg_left h3 hδ3
      nlinarith
    calc ∫ β in a..b, A * P β ≤ ∫ β in (-L)..L, A * P β := h1
      _ = 2 * (A * ∫ β in (0 : ℝ)..L, P β) := by
          rw [hsplit, intervalIntegral.integral_const_mul]
      _ ≤ 2 * (A * (162 * δ * ((1 + Real.log K) ^ 3 / K))) := by
          have := hFTC'.trans hfin
          have := mul_le_mul_of_nonneg_left this hA0
          linarith
      _ ≤ 350 * A * δ * ((1 + Real.log K) ^ 3 / K) := by
          have h0 : 0 ≤ A * δ * ((1 + Real.log K) ^ 3 / K) := by positivity
          have e : 350 * A * δ * ((1 + Real.log K) ^ 3 / K) - 2 * (A * (162 * δ * ((1 + Real.log K) ^ 3 / K)))
              = 26 * (A * δ * ((1 + Real.log K) ^ 3 / K)) := by ring
          linarith

end TrackF
end ZetaShell
