/-
Node K7a (L7_3, round 3): eq:K-G-applied — the family sum is at most `Q²(‖a‖² − Hole(S)) + (2π𝒳 + R′²)‖a‖²` on the hole
range `ℓ_K ≤ s ≤ log 𝒳 − 1`. DERIVED here (round 3) from K1s (`farey_majorant`) and two sub-nodes:
* K7a2 `farey_zero_set_bound` (open): K2corr (L7_9's `gallagher_with_zero_set_corr`) on the far Farey points
  `Ξ = {b/q : ⌊R⌋ < q ≤ Q}` at `δ = Q⁻²`, `w ≡ 1`, `D_δ ≤ Q²` (strict Farey separation `> Q⁻²`, at most one point per
  `δ`-window), plus Gallagher (`ZetaQ.Gallagher.gallagher_additive_large_sieve`) on the near points `q ≤ ⌊R⌋` at
  `δ = ⌊R⌋⁻²`: `Σ_{q≤Q}Σ*_b|S(b/q)|² ≤ Q²(‖a‖² − ∫_{Z∩[0,1)}|S|²) + (2π𝒳 + R′²)‖a‖²`.
* K7a1 `zero_set_ge_hole` (open): the `Δ`-balls, `Δ = 1/(2RQ)`, around `a/r`, `r ≤ R < Q/2`, are disjoint subsets of `Z`
  mod 1 (K3 (a)–(c), proved), so `Hole(S) ≤ ∫_{Z∩[0,1)}|S|²` — the circle-measure step: for 1-periodic continuous
  `g ≥ 0`, `∫_{c−Δ}^{c+Δ} g = ∫_0^1 g·1[‖θ − c‖ ≤ Δ]`, and `Σ 1[‖θ − c_i‖ ≤ Δ] ≤ 1_Z`.
The hole-range facts (`R ≥ 1`, `R ≤ Q/e < Q/2`, `Δ = 1/(2RQ)`) are proved here (`R0_le_Q_eventually`, K7b's file).
-/
import ZetaShell.LemmaK.LK_K7_Defs
import ZetaShell.LemmaK.LK_K1s_FareySum
import ZetaShell.LemmaK.LK_K7b_HoleLower
import ZetaShell.LemmaK.LK_K2_GallagherZeroSet

noncomputable section
open Filter MeasureTheory

namespace ZetaShell
namespace LemmaK

/-- the far Farey points `b/q`, `⌊R⌋ < q ≤ Q`, `(b,q) = 1`. -/
def farBig (Qn : ℕ) (R : ℝ) : Finset ((_ : ℕ) × ℕ) :=
  (Finset.Ioc ⌊R⌋₊ Qn).sigma (fun q => ZetaQ.reducedResidues q)

/-- `∫_{Z ∩ [0,1)} |S|²`, `Z = {D_δ = 0}` for the far points at `δ = Q⁻²`, `w ≡ 1`. -/
def zeroSetInt (Qn N : ℕ) (a : ℕ → ℂ) (R : ℝ) : ℝ :=
  ∫ θ in Set.Ico (0 : ℝ) 1 ∩ {θ | Ddens (farBig Qn R) (fun x => (x.2 : ℝ) / x.1) (fun _ => 1)
      (1 / (Qn : ℝ) ^ 2) θ = 0}, ‖ZetaQ.expSum N a θ‖ ^ 2

/-- same-denominator Farey gap: `‖b/q − b′/q‖ ≥ 1/q` for `b ≠ b′ < q`. -/
theorem farey_gap_same {q b b' : ℕ} (hq : 0 < q) (hb : b < q) (hb' : b' < q) (hne : b ≠ b') :
    1 / (q : ℝ) ≤ distZ ((b : ℝ) / q - (b' : ℝ) / q) := by
  obtain ⟨m, hm⟩ := distZ_eq ((b : ℝ) / q - (b' : ℝ) / q)
  rw [hm]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hD : (b : ℤ) - (b' : ℤ) - m * (q : ℤ) ≠ 0 := by
    intro h0
    have h1 : (q : ℤ) ∣ (b : ℤ) - (b' : ℤ) := ⟨m, by linarith⟩
    have h2 : |(b : ℤ) - (b' : ℤ)| < q := by
      rw [abs_lt]; constructor <;> omega
    have h3 := Int.eq_zero_of_abs_lt_dvd h1 h2
    omega
  have hz1 : (1 : ℤ) ≤ |(b : ℤ) - (b' : ℤ) - m * (q : ℤ)| := by
    have := abs_pos.mpr hD; linarith
  have hR1 : (1 : ℝ) ≤ |((((b : ℤ) - (b' : ℤ) - m * (q : ℤ)) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hz1
  have key : (b : ℝ) / q - (b' : ℝ) / q - (m : ℝ) = ((((b : ℤ) - (b' : ℤ) - m * (q : ℤ)) : ℤ) : ℝ) / q := by
    push_cast; field_simp
  rw [key, abs_div, abs_of_pos hqR]
  exact div_le_div_of_nonneg_right hR1 hqR.le

/-- **K7a2.** -/
theorem farey_zero_set_bound (Qn N : ℕ) (a : ℕ → ℂ) (R X : ℝ) (hQ : 2 ≤ Qn) (hN : (N : ℝ) ≤ X) :
    ∑ q ∈ Finset.Icc 1 Qn, ∑ b ∈ ZetaQ.reducedResidues q, ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2
      ≤ (Qn : ℝ) ^ 2 * (ZetaQ.l2sq N a - zeroSetInt Qn N a R)
        + (2 * Real.pi * X + (max 2 R) ^ 2) * ZetaQ.l2sq N a := by
  classical
  set f : ((_ : ℕ) × ℕ) → ℝ := fun x => ‖ZetaQ.expSum N a ((x.2 : ℝ) / (x.1 : ℝ))‖ ^ 2 with hf
  set M := ⌊R⌋₊ with hM
  have hQR : (2 : ℝ) ≤ Qn := by exact_mod_cast hQ
  have hl2 : 0 ≤ ZetaQ.l2sq N a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- split the moduli at `M`
  have hsplit : ∑ q ∈ Finset.Icc 1 Qn, ∑ b ∈ ZetaQ.reducedResidues q, ‖ZetaQ.expSum N a ((b : ℝ) / (q : ℝ))‖ ^ 2
      = ∑ x ∈ ((Finset.Icc 1 Qn).filter (fun q => q ≤ M)).sigma (fun q => ZetaQ.reducedResidues q), f x
        + ∑ x ∈ farBig Qn R, f x := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 Qn) (fun q => q ≤ M)]
    congr 1
    · rw [Finset.sum_sigma]
    · have e : (Finset.Icc 1 Qn).filter (fun q => ¬ q ≤ M) = Finset.Ioc M Qn := by
        ext q; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
      rw [e, farBig, Finset.sum_sigma]
  rw [hsplit]
  -- the far part: K2corr at `δ = Q⁻²`
  have hδ : (0 : ℝ) < 1 / (Qn : ℝ) ^ 2 := by positivity
  have hδ1 : 1 / (Qn : ℝ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hDd : ∀ θ : ℝ, Ddens (farBig Qn R) (fun x => (x.2 : ℝ) / x.1) (fun _ => 1) (1 / (Qn : ℝ) ^ 2) θ
      ≤ (Qn : ℝ) ^ 2 := by
    intro θ
    unfold Ddens
    rw [one_div, inv_inv]
    have hcard : ∑ i ∈ farBig Qn R, (if distZ ((i.2 : ℝ) / i.1 - θ) ≤ (Qn : ℝ)⁻¹ ^ 2 / 2 then (1 : ℝ) else 0) ≤ 1 := by
      rw [Finset.sum_boole]
      have : ((farBig Qn R).filter (fun i => distZ ((i.2 : ℝ) / i.1 - θ) ≤ (Qn : ℝ)⁻¹ ^ 2 / 2)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        by_contra hxy
        simp only [Finset.mem_filter, farBig, Finset.mem_sigma, Finset.mem_Ioc, mem_reducedResidues] at hx hy
        obtain ⟨⟨⟨hxM, hxQ⟩, hxb, hxc⟩, hxθ⟩ := hx
        obtain ⟨⟨⟨hyM, hyQ⟩, hyb, hyc⟩, hyθ⟩ := hy
        have htri : distZ ((x.2 : ℝ) / x.1 - (y.2 : ℝ) / y.1) ≤ (Qn : ℝ)⁻¹ ^ 2 := by
          have e : (x.2 : ℝ) / x.1 - (y.2 : ℝ) / y.1 = ((x.2 : ℝ) / x.1 - θ) + (θ - (y.2 : ℝ) / y.1) := by ring
          rw [e]
          have := distZ_add_le ((x.2 : ℝ) / x.1 - θ) (θ - (y.2 : ℝ) / y.1)
          rw [distZ_sub_comm θ] at this
          linarith
        have hx0 : 0 < x.1 := by omega
        have hy0 : 0 < y.1 := by omega
        have hxQR : (x.1 : ℝ) ≤ Qn := by exact_mod_cast hxQ
        have hyQR : (y.1 : ℝ) ≤ Qn := by exact_mod_cast hyQ
        have hx0R : (0 : ℝ) < x.1 := by exact_mod_cast hx0
        have hy0R : (0 : ℝ) < y.1 := by exact_mod_cast hy0
        by_cases hq : x.1 = y.1
        · have hb : x.2 ≠ y.2 := by
            intro hb; apply hxy; exact Sigma.ext hq (heq_of_eq hb)
          have hg := farey_gap_same hx0 hxb (hq ▸ hyb) hb
          rw [← hq] at htri
          have : (Qn : ℝ)⁻¹ ^ 2 < 1 / (x.1 : ℝ) := by
            rw [inv_pow, one_div]
            apply inv_strictAnti₀ hx0R
            nlinarith
          linarith
        · have hne : (x.1, x.2 % x.1) ≠ (y.1, y.2 % y.1) := by
            intro h; exact hq (congrArg Prod.fst h)
          have hg := farey_gap hx0 hy0 hxc hyc hne
          have hlt : (x.1 : ℝ) * y.1 < (Qn : ℝ) ^ 2 := by
            rcases lt_or_gt_of_ne hq with h | h
            · have : (x.1 : ℝ) + 1 ≤ y.1 := by exact_mod_cast h
              nlinarith
            · have : (y.1 : ℝ) + 1 ≤ x.1 := by exact_mod_cast h
              nlinarith
          have : (Qn : ℝ)⁻¹ ^ 2 < 1 / ((x.1 : ℝ) * y.1) := by
            rw [inv_pow, one_div]
            exact inv_strictAnti₀ (by positivity) hlt
          linarith
      exact_mod_cast this
    have hQ2 : (0 : ℝ) ≤ (Qn : ℝ) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hcard hQ2
    simpa [one_div] using this
  have hfar := gallagher_with_zero_set_corr (farBig Qn R) (fun x => (x.2 : ℝ) / x.1) (fun _ => 1)
    (fun _ => zero_le_one) (1 / (Qn : ℝ) ^ 2) hδ hδ1 N a ((Qn : ℝ) ^ 2) hDd
  simp only [one_mul] at hfar
  have hfar' : ∑ x ∈ farBig Qn R, f x ≤ (Qn : ℝ) ^ 2 * (ZetaQ.l2sq N a - zeroSetInt Qn N a R)
      + Real.pi * X * ZetaQ.l2sq N a := by
    have e : (Qn : ℝ) ^ 2 * (ZetaQ.l2sq N a - zeroSetInt Qn N a R + Real.pi * N * (1 / (Qn : ℝ) ^ 2) * ZetaQ.l2sq N a)
        = (Qn : ℝ) ^ 2 * (ZetaQ.l2sq N a - zeroSetInt Qn N a R) + Real.pi * N * ZetaQ.l2sq N a := by
      field_simp
    have hπ : Real.pi * N * ZetaQ.l2sq N a ≤ Real.pi * X * ZetaQ.l2sq N a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN Real.pi_pos.le) hl2
    have h' : ∑ x ∈ farBig Qn R, f x ≤ (Qn : ℝ) ^ 2 * (ZetaQ.l2sq N a - zeroSetInt Qn N a R
        + Real.pi * N * (1 / (Qn : ℝ) ^ 2) * ZetaQ.l2sq N a) := hfar
    linarith
  -- the near part: Gallagher at `δ = M⁻²`
  have hnear : ∑ x ∈ ((Finset.Icc 1 Qn).filter (fun q => q ≤ M)).sigma (fun q => ZetaQ.reducedResidues q), f x
      ≤ ((max 2 R) ^ 2 + Real.pi * X) * ZetaQ.l2sq N a := by
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · have hempty : ((Finset.Icc 1 Qn).filter (fun q => q ≤ M)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro q hq hqM
        rw [Finset.mem_Icc] at hq
        omega
      have hX0 : 0 ≤ X := le_trans hN0 hN
      have h0 : ∑ x ∈ ((Finset.Icc 1 Qn).filter (fun q => q ≤ M)).sigma (fun q => ZetaQ.reducedResidues q), f x
          = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [Finset.mem_sigma, hempty] at hx
        simp at hx
      rw [h0]
      exact mul_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg Real.pi_pos.le hX0)) hl2
    · set S := ((Finset.Icc 1 Qn).filter (fun q => q ≤ M)).sigma (fun q => ZetaQ.reducedResidues q) with hS
      have hMR : (M : ℝ) ≤ max 2 R := by
        have hR0 : 0 ≤ R := by
          by_contra h; push_neg at h
          have : M = 0 := Nat.floor_eq_zero.mpr (by linarith)
          omega
        exact le_trans (Nat.floor_le hR0) (le_max_right _ _)
      have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
      have hsep : ∀ i j : S, i ≠ j → ∀ m : ℤ,
          1 / (M : ℝ) ^ 2 ≤ |(i.1.2 : ℝ) / i.1.1 - (j.1.2 : ℝ) / j.1.1 - (m : ℝ)| := by
        intro i j hij m
        obtain ⟨⟨q, b⟩, hi⟩ := i
        obtain ⟨⟨q', b'⟩, hj⟩ := j
        simp only [hS, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, mem_reducedResidues] at hi hj
        obtain ⟨⟨⟨hq1, _⟩, hqM⟩, hbq, hc⟩ := hi
        obtain ⟨⟨⟨hq1', _⟩, hqM'⟩, hbq', hc'⟩ := hj
        have hne : (q, b % q) ≠ (q', b' % q') := by
          rw [Nat.mod_eq_of_lt hbq, Nat.mod_eq_of_lt hbq']
          intro h
          apply hij
          simp only [Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2; rfl
        have hg := farey_gap (by omega : 0 < q) (by omega : 0 < q') hc hc' hne
        have hd := distZ_le ((b : ℝ) / q - (b' : ℝ) / q') m
        have hqq : (q : ℝ) * q' ≤ (M : ℝ) ^ 2 := by
          have h1 : (q : ℝ) ≤ M := by exact_mod_cast hqM
          have h2 : (q' : ℝ) ≤ M := by exact_mod_cast hqM'
          have h3 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
          nlinarith
        have : 1 / (M : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * q') :=
          one_div_le_one_div_of_le (by
            have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
            have : (1 : ℝ) ≤ q' := by exact_mod_cast hq1'
            positivity) hqq
        simp only
        linarith
      have hδM1 : 1 / (M : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
        nlinarith
      have hG := ZetaQ.Gallagher.gallagher_additive_large_sieve S N a (fun i : S => (i.1.2 : ℝ) / i.1.1)
        (1 / (M : ℝ) ^ 2) (by positivity) hδM1 hsep
      rw [Finset.sum_coe_sort S (fun x => f x)] at hG
      rw [one_div, inv_inv] at hG
      have hM2 : (M : ℝ) ^ 2 ≤ (max 2 R) ^ 2 := pow_le_pow_left₀ hMpos'.le hMR 2
      have hπ : Real.pi * N ≤ Real.pi * X := mul_le_mul_of_nonneg_left hN Real.pi_pos.le
      have : ((M : ℝ) ^ 2 + Real.pi * N) * ZetaQ.l2sq N a ≤ ((max 2 R) ^ 2 + Real.pi * X) * ZetaQ.l2sq N a :=
        mul_le_mul_of_nonneg_right (by linarith) hl2
      exact le_trans hG this
  linarith

theorem sum_integral_le_period_ii {ι : Type*} [Fintype ι] {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (hper : Function.Periodic g 1)
    (θ : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ i j, i ≠ j → ∀ m : ℤ, δ ≤ |θ i - θ j - (m : ℝ)|) :
    ∑ i, (∫ t in (θ i - δ / 2)..(θ i + δ / 2), g t) ≤ ∫ t in (0:ℝ)..1, g t := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact intervalIntegral.integral_nonneg zero_le_one (fun t _ => hg0 t)
  obtain ⟨i₀⟩ := hι
  obtain ⟨k, hk⟩ : ∃ k : ι → ℤ, ∀ i, k i = ⌊θ i - θ i₀⌋ := ⟨_, fun _ => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ι → ℝ, ∀ i, φ i = θ i - (k i : ℝ) := ⟨_, fun _ => rfl⟩
  have hlo : ∀ i, θ i₀ ≤ φ i := by
    intro i
    have := Int.floor_le (θ i - θ i₀)
    rw [hφ, hk]
    linarith
  have hhi : ∀ i, φ i + δ ≤ θ i₀ + 1 := by
    intro i
    by_cases hi : i = i₀
    · rw [hi, hφ, hk, sub_self, Int.floor_zero, Int.cast_zero, sub_zero]
      linarith
    · have h1 := hsep i i₀ hi (k i + 1)
      have h2 := Int.lt_floor_add_one (θ i - θ i₀)
      rw [← hk] at h2
      push_cast at h1
      rw [abs_of_neg (by linarith)] at h1
      rw [hφ]
      linarith
  have hsepφ : ∀ i j, i ≠ j → δ ≤ |φ i - φ j| := by
    intro i j hij
    have e : φ i - φ j = θ i - θ j - ((k i - k j : ℤ) : ℝ) := by
      rw [hφ, hφ]; push_cast; ring
    rw [e]
    exact hsep i j hij (k i - k j)
  have hshift : ∀ i, (∫ t in (θ i - δ / 2)..(θ i + δ / 2), g t)
      = ∫ t in (φ i - δ / 2)..(φ i + δ / 2), g t := by
    intro i
    have hg : ∀ y, g (y + (k i : ℝ)) = g y := fun y => by
      have := hper.int_mul (k i) y
      rwa [mul_one] at this
    have h := intervalIntegral.integral_comp_add_right g (k i : ℝ)
      (a := φ i - δ / 2) (b := φ i + δ / 2)
    simp only [hg] at h
    have e1 : φ i - δ / 2 + (k i : ℝ) = θ i - δ / 2 := by rw [hφ]; ring
    have e2 : φ i + δ / 2 + (k i : ℝ) = θ i + δ / 2 := by rw [hφ]; ring
    rw [h, e1, e2]
  have hint : ∀ a b : ℝ, a ≤ b → IntegrableOn g (Set.Ioc a b) volume := fun a b hab =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (hgi a b)
  have hsum : ∑ i, (∫ t in (θ i - δ / 2)..(θ i + δ / 2), g t)
      = ∫ t in ⋃ i, Set.Ioc (φ i - δ / 2) (φ i + δ / 2), g t := by
    rw [integral_iUnion_fintype (fun i => measurableSet_Ioc) ?_
      (fun i => hint _ _ (by linarith))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hshift i, intervalIntegral.integral_of_le (by linarith)]
    · intro i j hij
      simp only [Function.onFun]
      refine Set.disjoint_left.2 fun t ht1 ht2 => ?_
      rw [Set.mem_Ioc] at ht1 ht2
      have h := hsepφ i j hij
      rcases le_or_gt 0 (φ i - φ j) with h0 | h0
      · rw [abs_of_nonneg h0] at h
        linarith [ht1.1, ht1.2, ht2.1, ht2.2]
      · rw [abs_of_neg h0] at h
        linarith [ht1.1, ht1.2, ht2.1, ht2.2]
  have hsub : (⋃ i, Set.Ioc (φ i - δ / 2) (φ i + δ / 2))
      ⊆ Set.Ioc (θ i₀ - δ / 2) (θ i₀ - δ / 2 + 1) := by
    intro t ht
    rw [Set.mem_iUnion] at ht
    obtain ⟨i, hi⟩ := ht
    rw [Set.mem_Ioc] at hi
    have := hlo i
    have := hhi i
    exact Set.mem_Ioc.2 ⟨by linarith, by linarith⟩
  rw [hsum]
  calc (∫ t in ⋃ i, Set.Ioc (φ i - δ / 2) (φ i + δ / 2), g t)
      ≤ ∫ t in Set.Ioc (θ i₀ - δ / 2) (θ i₀ - δ / 2 + 1), g t :=
        setIntegral_mono_set (hint _ _ (by linarith)) (ae_of_all _ fun t => hg0 t)
          (Filter.Eventually.of_forall fun t ht => hsub ht)
    _ = ∫ t in (θ i₀ - δ / 2)..(θ i₀ - δ / 2 + 1), g t :=
        (intervalIntegral.integral_of_le (by linarith)).symm
    _ = ∫ t in (0:ℝ)..(0 + 1), g t := hper.intervalIntegral_add_eq _ _
    _ = ∫ t in (0:ℝ)..1, g t := by rw [zero_add]

/-- the zero set `Z = {D_δ = 0}` of the far Farey points is measurable. -/
theorem measurable_distZ : Measurable distZ := by
  unfold distZ
  have h : Measurable (fun x : ℝ => Int.fract x) := measurable_fract
  exact h.min (measurable_const.sub h)

theorem measurableSet_zeroSet (Qn : ℕ) (R : ℝ) :
    MeasurableSet {θ : ℝ | Ddens (farBig Qn R) (fun x => (x.2 : ℝ) / x.1) (fun _ => 1) (1 / (Qn : ℝ) ^ 2) θ = 0} := by
  classical
  apply measurableSet_eq_fun _ measurable_const
  unfold Ddens
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (measurable_distZ.comp (measurable_const.sub measurable_id)) measurable_const

/-- **K7a1.** -/
theorem zero_set_ge_hole (Qn N : ℕ) (a : ℕ → ℂ) (R : ℝ) (hQ : 2 ≤ Qn) (hR1 : 1 ≤ R)
    (hRQ : R < (Qn : ℝ) / 2) :
    holeInt N a R (1 / (2 * R * Qn)) ≤ zeroSetInt Qn N a R := by
  classical
  set Δ : ℝ := 1 / (2 * R * Qn) with hΔdef
  set Zs : Set ℝ := {θ : ℝ | Ddens (farBig Qn R) (fun x => (x.2 : ℝ) / x.1) (fun _ => 1) (1 / (Qn : ℝ) ^ 2) θ = 0}
    with hZs
  have hZm : MeasurableSet Zs := measurableSet_zeroSet Qn R
  set g : ℝ → ℝ := fun t => ‖ZetaQ.expSum N a t‖ ^ 2 with hg
  set h : ℝ → ℝ := Zs.indicator g with hh
  have hQR : (2 : ℝ) ≤ Qn := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Qn := by linarith
  have hRpos : 0 < R := by linarith
  have hΔ : 0 < Δ := by positivity
  have h2Δ : 2 * Δ = 1 / (R * Qn) := by rw [hΔdef]; field_simp
  have hΔ1 : 2 * Δ ≤ 1 := by rw [h2Δ, div_le_one (by positivity)]; nlinarith
  have hgc : Continuous g := expSum_normSq_continuous N a
  -- `h` is nonneg, periodic, interval integrable
  have hh0 : ∀ t, 0 ≤ h t := fun t => Set.indicator_nonneg (fun t _ => by rw [hg]; positivity) t
  have hDper : ∀ θ, Ddens (farBig Qn R) (fun x => (x.2 : ℝ) / x.1) (fun _ => 1) (1 / (Qn : ℝ) ^ 2) (θ + 1)
      = Ddens (farBig Qn R) (fun x => (x.2 : ℝ) / x.1) (fun _ => 1) (1 / (Qn : ℝ) ^ 2) θ := by
    intro θ
    unfold Ddens
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (i.2 : ℝ) / i.1 - (θ + 1) = ((i.2 : ℝ) / i.1 - θ) - 1 := by ring
    rw [e]
    unfold distZ
    rw [Int.fract_sub_one]
  have hper : Function.Periodic h 1 := by
    intro t
    rw [hh]
    by_cases ht : t ∈ Zs
    · have ht1 : t + 1 ∈ Zs := by
        simp only [hZs, Set.mem_setOf_eq] at ht ⊢; rw [hDper]; exact ht
      rw [Set.indicator_of_mem ht1, Set.indicator_of_mem ht]
      exact expSum_normSq_periodic N a t
    · have ht1 : t + 1 ∉ Zs := by
        simp only [hZs, Set.mem_setOf_eq] at ht ⊢; rw [hDper]; exact ht
      rw [Set.indicator_of_notMem ht1, Set.indicator_of_notMem ht]
  have hhi : ∀ a b : ℝ, IntervalIntegrable h volume a b := by
    intro a b
    have hgi : IntervalIntegrable g volume a b := hgc.intervalIntegrable a b
    rw [hh]
    exact ⟨hgi.1.indicator hZm, hgi.2.indicator hZm⟩
  obtain ⟨hA, -, hC⟩ := farey_hole_cores Qn R hR1 hRQ
  have hball : ∀ r b : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → b ∈ ZetaQ.reducedResidues r → ∀ t : ℝ,
      |t - (b : ℝ) / r| ≤ Δ → t ∈ Zs := by
    intro r b hr1 hrR hb t ht
    rw [mem_reducedResidues] at hb
    have hrR' : (r : ℝ) ≤ R := le_trans (by exact_mod_cast hrR) (Nat.floor_le hRpos.le)
    have hd : distZ (t - (b : ℝ) / r) ≤ 1 / (2 * R * Qn) := by
      have h0 := distZ_le (t - (b : ℝ) / r) 0
      simp only [Int.cast_zero, sub_zero] at h0
      linarith
    have hcore := hC b r (by omega) hrR' t hd
    simp only [hZs, Set.mem_setOf_eq]
    unfold Ddens
    rw [Finset.sum_eq_zero, mul_zero]
    intro x hx
    simp only [farBig, Finset.mem_sigma, Finset.mem_Ioc, mem_reducedResidues] at hx
    obtain ⟨⟨hxR, hxQ⟩, hxb, hxc⟩ := hx
    have hRx : R < (x.1 : ℝ) := by
      have h1 := Nat.lt_floor_add_one R
      have h2 : ((⌊R⌋₊ : ℕ) : ℝ) + 1 ≤ x.1 := by exact_mod_cast hxR
      linarith
    have hfar := hA b r x.2 x.1 (by omega) hrR' hb.2 (by omega) hxQ hRx hxc t hcore
    have e : 1 / (Qn : ℝ) ^ 2 / 2 = 1 / (2 * (Qn : ℝ) ^ 2) := by ring
    rw [if_neg]
    rw [e]
    exact not_le.mpr hfar
  set A := (Finset.Icc 1 ⌊R⌋₊).sigma (fun r => ZetaQ.reducedResidues r) with hAdef
  have e1 : holeInt N a R Δ
      = ∑ x ∈ A, ∫ t in ((x.2 : ℝ) / x.1 - 2 * Δ / 2)..((x.2 : ℝ) / x.1 + 2 * Δ / 2), h t := by
    unfold holeInt
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun b hb => ?_
    have := intervalIntegral.integral_comp_add_left (fun t => ‖ZetaQ.expSum N a t‖ ^ 2) ((b : ℝ) / r)
      (a := -Δ) (b := Δ)
    rw [this]
    have e2 : (b : ℝ) / r + -Δ = (b : ℝ) / r - 2 * Δ / 2 := by ring
    have e3 : (b : ℝ) / r + Δ = (b : ℝ) / r + 2 * Δ / 2 := by ring
    rw [e2, e3]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    obtain ⟨h1, h2⟩ := ht
    have hmem := hball r b (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 hb t
      (by rw [abs_le]; constructor <;> linarith)
    show ‖ZetaQ.expSum N a t‖ ^ 2 = h t
    rw [hh, Set.indicator_of_mem hmem]
  have hsep : ∀ i j : A, i ≠ j → ∀ m : ℤ,
      2 * Δ ≤ |(i.1.2 : ℝ) / i.1.1 - (j.1.2 : ℝ) / j.1.1 - (m : ℝ)| := by
    intro i j hij m
    obtain ⟨⟨r, b⟩, hi⟩ := i
    obtain ⟨⟨r', b'⟩, hj⟩ := j
    simp only [hAdef, Finset.mem_sigma, Finset.mem_Icc, mem_reducedResidues] at hi hj
    obtain ⟨⟨hr1, hrR⟩, hbr, hcop⟩ := hi
    obtain ⟨⟨hr1', hrR'⟩, hbr', hcop'⟩ := hj
    have hne : (r, b % r) ≠ (r', b' % r') := by
      rw [Nat.mod_eq_of_lt hbr, Nat.mod_eq_of_lt hbr']
      intro hh'
      apply hij
      simp only [Prod.mk.injEq] at hh'
      obtain ⟨h1, h2⟩ := hh'
      subst h1; subst h2; rfl
    have hgap := farey_gap (by omega : 0 < r) (by omega : 0 < r') hcop hcop' hne
    have hd := distZ_le ((b : ℝ) / r - (b' : ℝ) / r') m
    have hr1R : (r : ℝ) ≤ R := le_trans (by exact_mod_cast hrR) (Nat.floor_le hRpos.le)
    have hr2R : (r' : ℝ) ≤ R := le_trans (by exact_mod_cast hrR') (Nat.floor_le hRpos.le)
    have hr10 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hr20 : (1 : ℝ) ≤ r' := by exact_mod_cast hr1'
    have hs : 2 * Δ ≤ 1 / ((r : ℝ) * r') := by
      rw [h2Δ]
      apply one_div_le_one_div_of_le (by positivity)
      have h1 : (r : ℝ) * r' ≤ R * R := mul_le_mul hr1R hr2R (by linarith) (by linarith)
      have h2 : R * R ≤ R * Qn := mul_le_mul_of_nonneg_left (by linarith) hRpos.le
      linarith
    simp only
    linarith
  rw [e1, ← Finset.sum_coe_sort A]
  have hsum := sum_integral_le_period_ii (g := h) hh0 hhi hper (fun i : A => (i.1.2 : ℝ) / i.1.1)
    (by linarith) hΔ1 hsep
  have hfin : ∫ t in (0 : ℝ)..1, h t = zeroSetInt Qn N a R := by
    rw [intervalIntegral.integral_of_le zero_le_one, hh, setIntegral_indicator hZm]
    unfold zeroSetInt
    apply setIntegral_congr_set
    exact (Ico_ae_eq_Ioc.symm).inter (Filter.EventuallyEq.refl _ _)
  linarith


/-- **K7a.** Derived from K1s, K7a1, K7a2 and the hole-range facts. -/
theorem farey_hole_bound (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      ∑ q ∈ Finset.Icc 2 Qn, ∑ χ ∈ ZetaQ.primitiveChars q,
          ‖ZetaQ.charSum q ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
            (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s) χ‖ ^ 2
        ≤ (Qn : ℝ) ^ 2 *
            (ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
              - holeInt ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
                  (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)
                  (ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))
          + (2 * Real.pi * Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)
              + (max 2 (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)) ^ 2)
            * ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s) := by
  have hre : 0 < r + ε := by linarith
  filter_upwards [R0_le_Q_eventually lam r ε hlam1 hlam2 hr hε,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1 + 7), eventually_ge_atTop 2]
    with Qn hRQ hQbig hQ2
  intro s hs1 hs2
  have hQpos : (0 : ℝ) < Qn := by linarith [Real.exp_pos 1]
  have hlogQ0 : 0 < Real.log (Qn : ℝ) := Real.log_pos (by linarith [Real.add_one_le_exp 1])
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  set Lc0 := Lc (Qn : ℝ) T with hLc0
  set R := R0 (Qn : ℝ) T s with hRdef
  set N := ⌊Xlam lam (Qn : ℝ) T⌋₊ with hN
  have hQ7 : (7 : ℝ) < Qn := by linarith [Real.exp_one_gt_d9]
  have hT1 : 1 ≤ T := by
    rw [hT]; unfold ZetaQ.Twin
    exact Real.one_le_rpow (by rw [Real.le_log_iff_exp_le hQpos]; linarith) hre.le
  have hQT : 2 * Real.pi < (Qn : ℝ) * T := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have : (Qn : ℝ) ≤ (Qn : ℝ) * T := le_mul_of_one_le_right hQpos.le hT1
    linarith
  have hLcpos : 0 < Lc0 := by
    rw [hLc0]; unfold Lc
    apply Real.log_pos; rw [lt_div_iff₀ (by positivity)]; linarith
  have hTpos : 0 < T := by linarith
  have hQTL : 0 < (Qn : ℝ) * T * Lc0 := by positivity
  have hellK : ellK (Qn : ℝ) T = Real.log ((Qn : ℝ) * T * Lc0) := rfl
  have hlogR : Real.log R = s - ellK (Qn : ℝ) T := by
    rw [hRdef, hellK]; unfold R0
    rw [← hLc0, Real.log_div (Real.exp_pos s).ne' hQTL.ne', Real.log_exp]
  have hRpos : 0 < R := by rw [hRdef]; unfold R0; positivity
  have hR1 : 1 ≤ R := by
    have : 0 ≤ Real.log R := by rw [hlogR]; linarith
    rwa [Real.log_nonneg_iff hRpos] at this
  have hRQ2 : R < (Qn : ℝ) / 2 := by
    have h := hRQ s hs2
    have h1 : R ≤ Real.exp (Real.log Qn - 1) := by
      rw [← Real.exp_log hRpos]; exact Real.exp_le_exp.mpr h
    rw [Real.exp_sub, Real.exp_log hQpos] at h1
    have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : (Qn : ℝ) / Real.exp 1 < (Qn : ℝ) / 2 := div_lt_div_of_pos_left hQpos (by norm_num) he
    linarith
  have hΔ : T * Lc0 / (2 * Real.exp s) = 1 / (2 * R * Qn) := by
    rw [hRdef]; unfold R0; rw [← hLc0]
    field_simp
  have hX0 : 0 ≤ Xlam lam (Qn : ℝ) T := (Real.exp_pos _).le
  have hNX : ((N : ℕ) : ℝ) ≤ Xlam lam (Qn : ℝ) T := Nat.floor_le hX0
  have h1 := farey_majorant Qn N (acoef T s)
  have h2 := farey_zero_set_bound Qn N (acoef T s) R (Xlam lam (Qn : ℝ) T) hQ2 hNX
  have h3 := zero_set_ge_hole Qn N (acoef T s) R hQ2 hR1 hRQ2
  rw [hΔ]
  have hQ2' : (0 : ℝ) ≤ (Qn : ℝ) ^ 2 := sq_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h3 hQ2'
  nlinarith [h1, h2, h4]

end LemmaK
end ZetaShell
