/-
Node A3 (L7_6 statement, frozen; L7_6 round-2 proof): **Lemma 3, signed Gallagher localisation**
(lem:shell-3, sec_shell.tex l.398–418).

Draft: "Let `(a_n)` be supported in `[Ne^{−κ}, Ne^κ]`, let `𝒲` be real weights on `𝔉_Q` with `|𝒲| ≤ ‖𝒲‖_∞`, and
`δ = ε/N`. Then `|Σ_ξ 𝒲_ξ|S(ξ)|² − ∫₀¹ |S|² D^𝒲_δ| ≤ 2π sinh κ ‖𝒲‖_∞ (εQ² + N)‖a‖²`."

Proof (second reader L8_8, item 4):
(i) two-sided Gallagher bound `|δ f(ξ) − ∫_{I_ξ} f| ≤ (δ/2) ∫_{I_ξ} |f′|` for `f = |S|²` (`point_bound_two_sided`,
    the trunk's `point_bound` argument kept as a difference);
(ii) `|f′| ≤ 2|S||D_c|` with the derivative centred at `c = N cosh κ` (`abs_deriv_normSq_le_c`), and
    `∫₀¹ |D_c|² ≤ (2πN sinh κ)² ‖a‖²` by Parseval (`integral_normSq_expSumDc_le`: the frequencies are integers);
(iii) the windows fold injectively onto `ℝ/ℤ` since `δ < 1` (library `K2Aux.periodize`), so
    `∫₀¹ |S|² D^𝒲_δ = Σ_ξ 𝒲_ξ δ⁻¹ ∫_{I_ξ} |S|²` exactly, and the error sums to `∫₀¹ |S||D_c| · D^{|𝒲|}_δ δ`;
(iv) Lemma 2(b) in A3's variables (library `lemma2b_window`): `Σ_{‖ξ−θ‖≤δ/2} |𝒲_ξ| ≤ ‖𝒲‖_∞(δQ² + 1)`;
(v) `∫₀¹ |S||D_c| ≤ 2πN sinh κ ‖a‖²` (AM–GM at every `λ > 0`, `am_gm_limit`).
-/
import ZetaShell.Lemma2.A2b_DensityBound
import ZetaShell.LemmaK.LK9_K2_Aux

noncomputable section
open MeasureTheory Set

namespace ZetaShell
namespace TrackF
namespace A3Aux

open ZetaQ ZetaQ.Gallagher

/-- **Two-sided Gallagher bound**: `|δ f(x) − ∫_{x−δ/2}^{x+δ/2} f| ≤ (δ/2) ∫_{x−δ/2}^{x+δ/2} |f′|`. -/
theorem point_bound_two_sided {f f' : ℝ → ℝ} {x δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    |δ * f x - ∫ t in (x - δ / 2)..(x + δ / 2), f t|
      ≤ (δ / 2) * ∫ t in (x - δ / 2)..(x + δ / 2), |f' t| := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have h0x : x - δ / 2 ≤ x := by linarith
  have hx1 : x ≤ x + δ / 2 := by linarith
  have hw0 : Continuous (fun u : ℝ => (u - (x - δ / 2)) * f' u) :=
    (continuous_id.sub continuous_const).mul hf'
  have hw1 : Continuous (fun u : ℝ => (u - (x + δ / 2)) * f' u) :=
    (continuous_id.sub continuous_const).mul hf'
  have hL : (∫ u in (x - δ / 2)..x, (f u + (u - (x - δ / 2)) * f' u)) = (δ / 2) * f x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => (u - (x - δ / 2)) * f u)]
    · show (x - (x - δ / 2)) * f x - ((x - δ / 2) - (x - δ / 2)) * f (x - δ / 2) = δ / 2 * f x
      ring
    · intro u _
      have h : HasDerivAt (fun y => (y - (x - δ / 2)) * f y)
          (1 * f u + (u - (x - δ / 2)) * f' u) u :=
        ((hasDerivAt_id' u).sub_const (x - δ / 2)).mul (hf u)
      show HasDerivAt (fun u => (u - (x - δ / 2)) * f u) (f u + (u - (x - δ / 2)) * f' u) u
      rw [one_mul] at h
      exact h
    · exact (hfc.add hw0).intervalIntegrable _ _
  have hR : (∫ u in x..(x + δ / 2), (f u + (u - (x + δ / 2)) * f' u)) = (δ / 2) * f x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => (u - (x + δ / 2)) * f u)]
    · show (x + δ / 2 - (x + δ / 2)) * f (x + δ / 2) - (x - (x + δ / 2)) * f x = δ / 2 * f x
      ring
    · intro u _
      have h : HasDerivAt (fun y => (y - (x + δ / 2)) * f y)
          (1 * f u + (u - (x + δ / 2)) * f' u) u :=
        ((hasDerivAt_id' u).sub_const (x + δ / 2)).mul (hf u)
      show HasDerivAt (fun u => (u - (x + δ / 2)) * f u) (f u + (u - (x + δ / 2)) * f' u) u
      rw [one_mul] at h
      exact h
    · exact (hfc.add hw1).intervalIntegrable _ _
  have hL' : (∫ u in (x - δ / 2)..x, f u) + (∫ u in (x - δ / 2)..x, (u - (x - δ / 2)) * f' u)
      = (δ / 2) * f x := by
    rw [← intervalIntegral.integral_add (hfc.intervalIntegrable _ _) (hw0.intervalIntegrable _ _)]
    exact hL
  have hR' : (∫ u in x..(x + δ / 2), f u) + (∫ u in x..(x + δ / 2), (u - (x + δ / 2)) * f' u)
      = (δ / 2) * f x := by
    rw [← intervalIntegral.integral_add (hfc.intervalIntegrable _ _) (hw1.intervalIntegrable _ _)]
    exact hR
  have hadj : (∫ u in (x - δ / 2)..x, f u) + (∫ u in x..(x + δ / 2), f u)
      = ∫ u in (x - δ / 2)..(x + δ / 2), f u :=
    intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)
  have hb2 : |∫ u in (x - δ / 2)..x, (u - (x - δ / 2)) * f' u|
      ≤ ∫ u in (x - δ / 2)..x, (δ / 2) * |f' u| := by
    refine (intervalIntegral.abs_integral_le_integral_abs h0x).trans ?_
    refine intervalIntegral.integral_mono_on h0x (hw0.abs.intervalIntegrable _ _)
      ((continuous_const.mul hf'.abs).intervalIntegrable _ _) ?_
    intro u hu
    rw [abs_mul]
    have : |u - (x - δ / 2)| ≤ δ / 2 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hb3 : |∫ u in x..(x + δ / 2), (u - (x + δ / 2)) * f' u|
      ≤ ∫ u in x..(x + δ / 2), (δ / 2) * |f' u| := by
    refine (intervalIntegral.abs_integral_le_integral_abs hx1).trans ?_
    refine intervalIntegral.integral_mono_on hx1 (hw1.abs.intervalIntegrable _ _)
      ((continuous_const.mul hf'.abs).intervalIntegrable _ _) ?_
    intro u hu
    rw [abs_mul]
    have : |u - (x + δ / 2)| ≤ δ / 2 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hsum : (∫ u in (x - δ / 2)..x, (δ / 2) * |f' u|) + (∫ u in x..(x + δ / 2), (δ / 2) * |f' u|)
      = (δ / 2) * ∫ u in (x - δ / 2)..(x + δ / 2), |f' u| := by
    have hcf : Continuous (fun u : ℝ => (δ / 2) * |f' u|) := continuous_const.mul hf'.abs
    rw [intervalIntegral.integral_add_adjacent_intervals (hcf.intervalIntegrable _ _)
      (hcf.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  have e : δ * f x - ∫ t in (x - δ / 2)..(x + δ / 2), f t
      = (∫ u in (x - δ / 2)..x, (u - (x - δ / 2)) * f' u)
        + (∫ u in x..(x + δ / 2), (u - (x + δ / 2)) * f' u) := by
    linarith
  rw [e]
  calc _ ≤ |∫ u in (x - δ / 2)..x, (u - (x - δ / 2)) * f' u|
        + |∫ u in x..(x + δ / 2), (u - (x + δ / 2)) * f' u| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- The multiplier `2πi (n − c)`. -/
def cmultC (c : ℝ) (n : ℕ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((((n : ℝ) - c : ℝ)) : ℂ)

/-- The derivative centred at `c`: `D_c(θ) = Σ a_n 2πi (n − c) e(nθ) = S′ − 2πic S`. -/
def expSumDc (N : ℕ) (a : ℕ → ℂ) (c : ℝ) : ℝ → ℂ :=
  trig (Finset.Ioc 0 N) (fun n => a n * cmultC c n)

/-- **Centring at any `c`**: `|(|S|²)′| ≤ 2|S||D_c|`. -/
theorem abs_deriv_normSq_le_c (N : ℕ) (a : ℕ → ℂ) (c θ : ℝ) :
    |2 * inner ℝ (expSum N a θ) (expSumDeriv N a θ)|
      ≤ 2 * (‖expSum N a θ‖ * ‖expSumDc N a c θ‖) := by
  set c' : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((c : ℝ) : ℂ) with hc'
  have hsplit : expSumDeriv N a θ = expSumDc N a c θ + c' * expSum N a θ := by
    simp only [expSumDeriv, expSumDc, expSum, trig, cmultC, hc', Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have hSS : expSum N a θ * (starRingEnd ℂ) (expSum N a θ)
      = ((‖expSum N a θ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj', Complex.ofReal_pow]
  have hz : c' * expSum N a θ * (starRingEnd ℂ) (expSum N a θ)
      = ((2 * Real.pi * c * ‖expSum N a θ‖ ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [mul_assoc c', hSS, hc']
    push_cast
    ring
  have hre : inner ℝ (expSum N a θ) (expSumDeriv N a θ)
      = (expSumDc N a c θ * (starRingEnd ℂ) (expSum N a θ)).re := by
    rw [Complex.inner, hsplit, add_mul, Complex.add_re, hz, Complex.mul_I_re,
      Complex.ofReal_im, neg_zero, add_zero]
  rw [abs_mul, abs_two, hre]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |(expSumDc N a c θ * (starRingEnd ℂ) (expSum N a θ)).re|
      ≤ ‖expSumDc N a c θ * (starRingEnd ℂ) (expSum N a θ)‖ := Complex.abs_re_le_norm _
    _ = ‖expSum N a θ‖ * ‖expSumDc N a c θ‖ := by
        rw [norm_mul, Complex.norm_conj, mul_comm]

/-- **Parseval for the centred derivative**: if `|n − c| ≤ L` whenever `a_n ≠ 0`, then
`∫₀¹ |D_c|² ≤ (2πL)² ‖a‖²`. -/
theorem integral_normSq_expSumDc_le (N : ℕ) (a : ℕ → ℂ) (c L : ℝ) (hL : 0 ≤ L)
    (hsupp : ∀ n ∈ Finset.Ioc 0 N, a n ≠ 0 → |(n : ℝ) - c| ≤ L) :
    (∫ t in (0:ℝ)..1, ‖expSumDc N a c t‖ ^ 2) ≤ (2 * Real.pi * L) ^ 2 * l2sq N a := by
  show (∫ t in (0:ℝ)..1, ‖trig (Finset.Ioc 0 N) (fun n => a n * cmultC c n) t‖ ^ 2) ≤ _
  rw [parseval_trig, l2sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [norm_mul, mul_pow]
  by_cases ha : a n = 0
  · rw [ha, norm_zero]; simp
  · have hnorm : ‖cmultC c n‖ = 2 * Real.pi * |(n : ℝ) - c| := by
      simp only [cmultC, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, mul_one, Complex.norm_ofNat]
    have h1 : ‖cmultC c n‖ ≤ 2 * Real.pi * L := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left (hsupp n hn ha) (by positivity)
    have hc2 : ‖cmultC c n‖ ^ 2 ≤ (2 * Real.pi * L) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have := mul_le_mul_of_nonneg_left hc2 (sq_nonneg ‖a n‖)
    linarith

/-- AM–GM at every scale, including the degenerate scale `λ₀ = 0`. -/
theorem am_gm_limit {I A B l0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hl0 : 0 ≤ l0)
    (hBle : B ≤ l0 ^ 2 * A) (hI : ∀ l : ℝ, 0 < l → I ≤ (1 / 2) * (l * A + l⁻¹ * B)) :
    I ≤ l0 * A := by
  rcases hl0.lt_or_eq with hpos | hzero
  · have h := hI l0 hpos
    have h2 : l0⁻¹ * B ≤ l0 * A := by
      rw [inv_mul_le_iff₀ hpos]
      nlinarith
    linarith
  · subst hzero
    have hB0 : B = 0 := le_antisymm (by simpa using hBle) hB
    subst hB0
    rw [zero_mul]
    rcases hA.lt_or_eq with hApos | hA0
    · by_contra hIpos
      push_neg at hIpos
      have h := hI (I / A) (div_pos hIpos hApos)
      rw [mul_zero, add_zero, div_mul_cancel₀ I hApos.ne'] at h
      linarith
    · have h := hI 1 one_pos
      rw [← hA0] at h
      simpa using h

end A3Aux

open ZetaQ ZetaQ.Gallagher A3Aux

/-- **A3 (lem:shell-3), two-sided form.** -/
theorem signed_gallagher (Q Nmax : ℕ) (a : ℕ → ℂ) (N κ ε : ℝ) (hN : 0 < N) (hκ : 0 ≤ κ)
    (hε : 0 < ε) (hεN : ε < N)
    (hsupp : ∀ n ∈ Finset.Ioc 0 Nmax, a n ≠ 0 →
      N * Real.exp (-κ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ N * Real.exp κ)
    (W : (_ : ℕ) × ℕ → ℝ) (Wmax : ℝ) (hW0 : 0 ≤ Wmax) (hW : ∀ x ∈ fareyIdx Q, |W x| ≤ Wmax) :
    |∑ x ∈ fareyIdx Q, W x * ‖ZetaQ.expSum Nmax a (fareyPt x)‖ ^ 2
        - ∫ θ in Set.Ico (0 : ℝ) 1,
            ‖ZetaQ.expSum Nmax a θ‖ ^ 2 * Ddens (fareyIdx Q) fareyPt W (ε / N) θ|
      ≤ 2 * Real.pi * Real.sinh κ * Wmax * (ε * (Q : ℝ) ^ 2 + N) * ZetaQ.l2sq Nmax a := by
  classical
  set δ : ℝ := ε / N with hδdef
  have hδ : 0 < δ := div_pos hε hN
  have hδ1 : δ < 1 := by rw [hδdef, div_lt_one hN]; exact hεN
  set c : ℝ := N * Real.cosh κ with hcdef
  set L : ℝ := N * Real.sinh κ with hLdef
  have hsinh : 0 ≤ Real.sinh κ := Real.sinh_nonneg_iff.mpr hκ
  have hL0 : 0 ≤ L := mul_nonneg hN.le hsinh
  have hsuppc : ∀ n ∈ Finset.Ioc 0 Nmax, a n ≠ 0 → |(n : ℝ) - c| ≤ L := by
    intro n hn ha
    obtain ⟨h1, h2⟩ := hsupp n hn ha
    rw [hcdef, hLdef, Real.cosh_eq, Real.sinh_eq, abs_le]
    constructor <;> nlinarith
  set S := ZetaQ.expSum Nmax a with hSdef
  set D := expSumDc Nmax a c with hDdef
  have hSc : Continuous S := continuous_trig _ _
  have hDc : Continuous D := continuous_trig _ _
  have hS'c : Continuous (expSumDeriv Nmax a) := continuous_trig _ _
  set f : ℝ → ℝ := fun t => ‖S t‖ ^ 2 with hfdef
  set g : ℝ → ℝ := fun t => ‖S t‖ * ‖D t‖ with hgdef
  have hfc : Continuous f := hSc.norm.pow 2
  have hgc : Continuous g := hSc.norm.mul hDc.norm
  have hfper : Function.Periodic f 1 := fun t => by
    show ‖S (t + 1)‖ ^ 2 = ‖S t‖ ^ 2
    rw [hSdef, expSum_eq_trig, trig_periodic _ _ t]
  have hgper : Function.Periodic g 1 := fun t => by
    show ‖S (t + 1)‖ * ‖D (t + 1)‖ = ‖S t‖ * ‖D t‖
    rw [hSdef, hDdef, expSum_eq_trig, expSumDc, trig_periodic _ _ t, trig_periodic _ _ t]
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  set E : ((_ : ℕ) × ℕ) → Set ℝ := fun x => {t : ℝ | distZ (fareyPt x - t) ≤ δ / 2} with hEdef
  have hEm : ∀ x, MeasurableSet (E x) := fun x => LemmaK.K2Aux.measurableSet_E (fareyPt x) δ
  have hper_int : ∀ (G : ℝ → ℝ), Function.Periodic G 1 → ∀ x,
      ∫ t in Ioc (0 : ℝ) 1, (E x).indicator G t
        = ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), G t := by
    intro G hG x
    exact LemmaK.K2Aux.periodize G hG (fareyPt x) δ hδ hδ1
  have hfint : IntegrableOn f (Ioc (0 : ℝ) 1) volume :=
    (hfc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hgint : IntegrableOn g (Ioc (0 : ℝ) 1) volume :=
    (hgc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- (iii) the main term, exactly
  have hmain : ∫ θ in Set.Ico (0 : ℝ) 1, ‖S θ‖ ^ 2 * Ddens (fareyIdx Q) fareyPt W δ θ
      = ∑ x ∈ fareyIdx Q, W x * (δ⁻¹ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t) := by
    have hpt : ∀ θ, ‖S θ‖ ^ 2 * Ddens (fareyIdx Q) fareyPt W δ θ
        = ∑ x ∈ fareyIdx Q, (δ⁻¹ * W x) * (E x).indicator f θ := by
      intro θ
      unfold Ddens
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h : θ ∈ E x
      · rw [Set.indicator_of_mem h]
        have h' : distZ (fareyPt x - θ) ≤ δ / 2 := h
        rw [if_pos h']
        simp only [hfdef]
        ring
      · rw [Set.indicator_of_notMem h]
        have h' : ¬ distZ (fareyPt x - θ) ≤ δ / 2 := h
        rw [if_neg h']
        ring
    rw [setIntegral_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun x _ => ((hfint.indicator (hEm x)).const_mul _))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_const_mul, hper_int f hfper x]
    ring
  -- (i)+(ii) the pointwise error at each Farey point
  have herr : ∀ x ∈ fareyIdx Q,
      |f (fareyPt x) - δ⁻¹ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t|
        ≤ ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), g t := by
    intro x _
    have hpb : |δ * f (fareyPt x) - ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t|
        ≤ (δ / 2) * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2),
          |2 * inner ℝ (S t) (expSumDeriv Nmax a t)| :=
      point_bound_two_sided (f := f)
        (f' := fun t => 2 * inner ℝ (S t) (expSumDeriv Nmax a t)) (x := fareyPt x) hδ
        (fun t => hasDerivAt_normSq Nmax a t) (continuous_const.mul (hSc.inner hS'c))
    have hle : (∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2),
          |2 * inner ℝ (S t) (expSumDeriv Nmax a t)|)
        ≤ ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), 2 * g t := by
      refine intervalIntegral.integral_mono_on (by linarith)
        ((continuous_const.mul (hSc.inner hS'c)).abs.intervalIntegrable _ _)
        ((continuous_const.mul hgc).intervalIntegrable _ _) ?_
      intro t _
      exact abs_deriv_normSq_le_c Nmax a c t
    rw [intervalIntegral.integral_const_mul] at hle
    have h2 : |δ * f (fareyPt x) - ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t|
        ≤ δ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), g t := by
      have := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ δ / 2)
      linarith
    have e1 : f (fareyPt x) - δ⁻¹ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t
        = δ⁻¹ * (δ * f (fareyPt x) - ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
    rw [e1, abs_mul, abs_of_pos (inv_pos.2 hδ)]
    calc δ⁻¹ * |δ * f (fareyPt x) - ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t|
        ≤ δ⁻¹ * (δ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), g t) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hδ.le)
      _ = ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), g t := by
          rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
  -- (iv) the errors folded onto one period, with Lemma 2(b)
  have hfold : ∑ x ∈ fareyIdx Q, |W x| * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), g t
      ≤ Wmax * (δ * (Q : ℝ) ^ 2 + 1) * ∫ t in (0 : ℝ)..1, g t := by
    have e2 : ∑ x ∈ fareyIdx Q, |W x| * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), g t
        = ∫ t in Ioc (0 : ℝ) 1, ∑ x ∈ fareyIdx Q, |W x| * (E x).indicator g t := by
      rw [integral_finsetSum _ (fun x _ => ((hgint.indicator (hEm x)).const_mul _))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_const_mul, hper_int g hgper x]
    have hpt2 : ∀ t, ∑ x ∈ fareyIdx Q, |W x| * (E x).indicator g t
        ≤ Wmax * (δ * (Q : ℝ) ^ 2 + 1) * g t := by
      intro t
      have e3 : ∑ x ∈ fareyIdx Q, |W x| * (E x).indicator g t
          = (∑ x ∈ fareyIdx Q, (if distZ (fareyPt x - t) ≤ δ / 2 then |W x| else 0)) * g t := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h : t ∈ E x
        · rw [Set.indicator_of_mem h]
          have h' : distZ (fareyPt x - t) ≤ δ / 2 := h
          rw [if_pos h']
        · rw [Set.indicator_of_notMem h]
          have h' : ¬ distZ (fareyPt x - t) ≤ δ / 2 := h
          rw [if_neg h']
          ring
      rw [e3]
      exact mul_le_mul_of_nonneg_right (lemma2b_window Q W Wmax δ t hδ.le hW0 hW) (hg0 t)
    rw [e2]
    have hLint : IntegrableOn (fun t => ∑ x ∈ fareyIdx Q, |W x| * (E x).indicator g t)
        (Ioc (0 : ℝ) 1) volume :=
      integrable_finsetSum _ (fun x _ => ((hgint.indicator (hEm x)).const_mul _))
    calc ∫ t in Ioc (0 : ℝ) 1, ∑ x ∈ fareyIdx Q, |W x| * (E x).indicator g t
        ≤ ∫ t in Ioc (0 : ℝ) 1, Wmax * (δ * (Q : ℝ) ^ 2 + 1) * g t :=
          setIntegral_mono hLint (hgint.const_mul _) hpt2
      _ = Wmax * (δ * (Q : ℝ) ^ 2 + 1) * ∫ t in (0 : ℝ)..1, g t := by
          rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  -- (v) `∫₀¹ |S||D_c| ≤ 2πL ‖a‖²`
  have hgbound : ∫ t in (0 : ℝ)..1, g t ≤ (2 * Real.pi * L) * ZetaQ.l2sq Nmax a := by
    have hA : ∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2 = ZetaQ.l2sq Nmax a := integral_normSq_expSum Nmax a
    have hA0 : 0 ≤ ZetaQ.l2sq Nmax a := Finset.sum_nonneg fun n _ => sq_nonneg _
    have hB0 : 0 ≤ ∫ t in (0 : ℝ)..1, ‖D t‖ ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
    have hBle := integral_normSq_expSumDc_le Nmax a c L hL0 hsuppc
    refine am_gm_limit hA0 hB0 (by positivity) hBle ?_
    intro l hl
    have iS : IntervalIntegrable (fun t => ‖S t‖ ^ 2) volume 0 1 :=
      (hSc.norm.pow 2).intervalIntegrable _ _
    have iD : IntervalIntegrable (fun t => ‖D t‖ ^ 2) volume 0 1 :=
      (hDc.norm.pow 2).intervalIntegrable _ _
    calc ∫ t in (0 : ℝ)..1, g t
        ≤ ∫ t in (0 : ℝ)..1, (1 / 2) * (l * ‖S t‖ ^ 2 + l⁻¹ * ‖D t‖ ^ 2) := by
          refine intervalIntegral.integral_mono_on zero_le_one (hgc.intervalIntegrable _ _)
            ((continuous_const.mul ((continuous_const.mul (hSc.norm.pow 2)).add
              (continuous_const.mul (hDc.norm.pow 2)))).intervalIntegrable _ _) ?_
          intro t _
          have := two_mul_le_kappa hl ‖S t‖ ‖D t‖
          simp only [hgdef]
          linarith
      _ = (1 / 2) * (l * ZetaQ.l2sq Nmax a + l⁻¹ * ∫ t in (0 : ℝ)..1, ‖D t‖ ^ 2) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add (iS.const_mul _) (iD.const_mul _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hA]
  -- assembly
  rw [hmain]
  have hdiff : ∑ x ∈ fareyIdx Q, W x * ‖S (fareyPt x)‖ ^ 2
      - ∑ x ∈ fareyIdx Q, W x * (δ⁻¹ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t)
      = ∑ x ∈ fareyIdx Q, W x * (f (fareyPt x)
          - δ⁻¹ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hfdef]
    ring
  rw [hdiff]
  have hW0' : ∀ x, 0 ≤ |W x| := fun x => abs_nonneg _
  calc |∑ x ∈ fareyIdx Q, W x * (f (fareyPt x)
          - δ⁻¹ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t)|
      ≤ ∑ x ∈ fareyIdx Q, |W x * (f (fareyPt x)
          - δ⁻¹ * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), f t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ fareyIdx Q, |W x| * ∫ t in (fareyPt x - δ / 2)..(fareyPt x + δ / 2), g t := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (herr x hx) (hW0' x)
    _ ≤ Wmax * (δ * (Q : ℝ) ^ 2 + 1) * ∫ t in (0 : ℝ)..1, g t := hfold
    _ ≤ Wmax * (δ * (Q : ℝ) ^ 2 + 1) * ((2 * Real.pi * L) * ZetaQ.l2sq Nmax a) :=
        mul_le_mul_of_nonneg_left hgbound (by positivity)
    _ = 2 * Real.pi * Real.sinh κ * Wmax * (ε * (Q : ℝ) ^ 2 + N) * ZetaQ.l2sq Nmax a := by
        have hNne : N ≠ 0 := hN.ne'
        rw [hδdef, hLdef]
        field_simp

end TrackF
end ZetaShell
