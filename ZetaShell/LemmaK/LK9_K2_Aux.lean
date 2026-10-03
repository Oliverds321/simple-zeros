/-
L7_9 helper for node K2 (`gallagher_with_zero_set`, Lemma K.2 of `tex/sec_lemmaK.tex`, lem:K-G).
Gallagher's pointwise bound (trunk `ZetaQ.Gallagher.point_bound_integral`, centred derivative
`expSumD`, AM–GM at `κ = πN`) integrated against the weighted density `Ddens`; the intervals
`[ξ_i − δ/2, ξ_i + δ/2]` are periodised to `{t ∈ (0,1] : ‖ξ_i − t‖ ≤ δ/2}` (needs `δ < 1`), and on
`Z = {Ddens = 0}` the `|S|²` part of the majorant is dropped.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section
open MeasureTheory Set

namespace ZetaShell
namespace LemmaK
namespace K2Aux

open ZetaQ ZetaQ.Gallagher

lemma distZ_eq_abs {x : ℝ} (h1 : -(1 / 2) ≤ x) (h2 : x < 1 / 2) : distZ x = |x| := by
  unfold distZ
  rcases le_or_gt 0 x with hx | hx
  · have hf : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx, by linarith⟩
    rw [hf, abs_of_nonneg hx]
    exact min_eq_left (by linarith)
  · have hf : Int.fract x = x + 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [hf, abs_of_neg hx, min_eq_right (by linarith)]
    ring

lemma distZ_add_int (x : ℝ) (m : ℤ) : distZ (x + m) = distZ x := by
  unfold distZ
  rw [Int.fract_add_intCast]

lemma measurable_distZ_sub (ξ : ℝ) : Measurable (fun t : ℝ => distZ (ξ - t)) := by
  unfold distZ
  have h : Measurable (fun t : ℝ => Int.fract (ξ - t)) :=
    measurable_fract.comp (measurable_const.sub measurable_id)
  exact h.min (measurable_const.sub h)

lemma measurableSet_E (ξ δ : ℝ) : MeasurableSet {t : ℝ | distZ (ξ - t) ≤ δ / 2} :=
  measurableSet_le (measurable_distZ_sub ξ) measurable_const

lemma measurable_Ddens {ι : Type} (s : Finset ι) (ξ w : ι → ℝ) (δ : ℝ) :
    Measurable (fun θ => Ddens s ξ w δ θ) := by
  unfold Ddens
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum s fun i _ => ?_
  exact Measurable.ite (measurableSet_E (ξ i) δ) measurable_const measurable_const

/-- **Periodisation.** For `G` continuous and 1-periodic and `0 < δ < 1`,
`∫_{(0,1]} 1{‖ξ − t‖ ≤ δ/2} G(t) dt = ∫_{ξ−δ/2}^{ξ+δ/2} G`. -/
lemma periodize (G : ℝ → ℝ) (hGp : Function.Periodic G 1) (ξ δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∫ t in Ioc (0 : ℝ) 1, {t : ℝ | distZ (ξ - t) ≤ δ / 2}.indicator G t
      = ∫ t in (ξ - δ / 2)..(ξ + δ / 2), G t := by
  set E := {t : ℝ | distZ (ξ - t) ≤ δ / 2} with hE
  have hmem1 : ∀ t, (t + 1 ∈ E) ↔ (t ∈ E) := by
    intro t
    simp only [hE, Set.mem_setOf_eq]
    rw [show ξ - (t + 1) = (ξ - t) + ((-1 : ℤ) : ℝ) by push_cast; ring, distZ_add_int]
  have hper : Function.Periodic (E.indicator G) 1 := by
    intro t
    by_cases h : t ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem1 t).mpr h), hGp t]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmem1 t).mp h'))]
  have h1 : ∫ t in Ioc (0 : ℝ) 1, E.indicator G t = ∫ t in (0 : ℝ)..(0 + 1), E.indicator G t := by
    rw [zero_add, intervalIntegral.integral_of_le zero_le_one]
  rw [h1, hper.intervalIntegral_add_eq 0 (ξ - 1 / 2), intervalIntegral.integral_of_le (by linarith)]
  have hEq : EqOn (E.indicator G) ((Icc (ξ - δ / 2) (ξ + δ / 2)).indicator G)
      (Ioc (ξ - 1 / 2) (ξ - 1 / 2 + 1)) := by
    intro t ht
    have hmem : t ∈ E ↔ t ∈ Icc (ξ - δ / 2) (ξ + δ / 2) := by
      rw [Set.mem_Ioc] at ht
      simp only [hE, Set.mem_setOf_eq, Set.mem_Icc]
      rw [distZ_eq_abs (by linarith [ht.2]) (by linarith [ht.1]), abs_le]
      constructor
      · intro h; constructor <;> linarith [h.1, h.2]
      · intro h; constructor <;> linarith [h.1, h.2]
    by_cases h : t ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.mpr h'))]
  rw [setIntegral_congr_fun measurableSet_Ioc hEq, setIntegral_indicator measurableSet_Icc]
  have hsub : Ioc (ξ - 1 / 2) (ξ - 1 / 2 + 1) ∩ Icc (ξ - δ / 2) (ξ + δ / 2)
      = Icc (ξ - δ / 2) (ξ + δ / 2) := by
    apply Set.inter_eq_right.mpr
    intro t ht
    rw [Set.mem_Icc] at ht
    rw [Set.mem_Ioc]
    constructor <;> linarith [ht.1, ht.2]
  rw [hsub, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]

/-- Gallagher's pointwise bound at one point, with the majorant `gMaj` (copied from the proof of
the trunk's `gallagher_additive_large_sieve`, where it is an internal `have`). -/
lemma point_le_gMaj (N : ℕ) (a : ℕ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hN : 0 < N) (x : ℝ) :
    ‖expSum N a x‖ ^ 2
      ≤ ∫ t in (x - δ / 2)..(x + δ / 2), gMaj N a δ (Real.pi * N) t := by
  have hκ : 0 < Real.pi * N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hS'c : Continuous (expSumDeriv N a) := continuous_trig _ _
  have hSc : Continuous (expSum N a) := continuous_trig _ _
  have hpb := point_bound_integral (f := fun t => ‖expSum N a t‖ ^ 2)
    (f' := fun t => 2 * inner ℝ (expSum N a t) (expSumDeriv N a t)) (x := x) hδ
    (fun t => hasDerivAt_normSq N a t) (continuous_const.mul (hSc.inner hS'c))
  rw [abs_of_nonneg (sq_nonneg _)] at hpb
  refine hpb.trans ?_
  refine intervalIntegral.integral_mono_on (by linarith)
    (((hSc.norm.pow 2).abs.intervalIntegrable _ _).const_mul _ |>.add
      (((continuous_const.mul (hSc.inner hS'c)).abs.intervalIntegrable _ _).const_mul _))
    ((continuous_gMaj N a δ _).intervalIntegrable _ _) ?_
  intro t _
  unfold gMaj
  rw [abs_of_nonneg (sq_nonneg ‖expSum N a t‖)]
  have h1 := abs_deriv_normSq_le N a t
  have h2 := two_mul_le_kappa hκ ‖expSum N a t‖ ‖expSumD N a t‖
  linarith

/-- Lemma K.2 with the `Z`-integral PARENTHESISED (the corrected statement; see the report:
without parentheses `∫ θ in A, f θ + c` parses as `∫ θ in A, (f θ + c)`). -/
theorem gallagher_zero_aux {ι : Type} (s : Finset ι) (ξ w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (N : ℕ) (a : ℕ → ℂ) (Dsup : ℝ)
    (hD : ∀ θ : ℝ, Ddens s ξ w δ θ ≤ Dsup) :
    ∑ i ∈ s, w i * ‖ZetaQ.expSum N a (ξ i)‖ ^ 2
      ≤ Dsup * (ZetaQ.l2sq N a
          - (∫ θ in Set.Ico (0 : ℝ) 1 ∩ {θ | Ddens s ξ w δ θ = 0}, ‖ZetaQ.expSum N a θ‖ ^ 2)
          + Real.pi * N * δ * ZetaQ.l2sq N a) := by
  classical
  set Dd := fun θ => Ddens s ξ w δ θ with hDd
  set Z := {θ : ℝ | Ddens s ξ w δ θ = 0} with hZ
  have hZm : MeasurableSet Z := measurableSet_eq_fun (measurable_Ddens s ξ w δ) measurable_const
  have hDnn : ∀ θ, 0 ≤ Ddens s ξ w δ θ := fun θ => by
    unfold Ddens
    refine mul_nonneg (inv_nonneg.2 hδ.le) (Finset.sum_nonneg fun i _ => ?_)
    split_ifs
    · exact hw i
    · exact le_refl 0
  have hDsup : 0 ≤ Dsup := (hDnn 0).trans (hD 0)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [expSum, l2sq]
  set κ : ℝ := Real.pi * N with hκdef
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hκ : 0 < κ := by positivity
  have hL0 : 0 ≤ l2sq N a := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hSc : Continuous (expSum N a) := continuous_trig _ _
  have hDc : Continuous (expSumD N a) := continuous_trig _ _
  set gM := gMaj N a δ κ with hgM
  set E : ι → Set ℝ := fun i => {t : ℝ | distZ (ξ i - t) ≤ δ / 2} with hEdef
  have hEm : ∀ i, MeasurableSet (E i) := fun i => measurableSet_E (ξ i) δ
  have hgMc : Continuous gM := continuous_gMaj N a δ κ
  have hgMint : IntegrableOn gM (Ioc (0 : ℝ) 1) volume :=
    (hgMc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- Step 1–2: pointwise bound, periodised
  have hstep : ∀ i, ‖expSum N a (ξ i)‖ ^ 2 ≤ ∫ t in Ioc (0 : ℝ) 1, (E i).indicator gM t := by
    intro i
    rw [periodize gM (gMaj_periodic N a δ κ) (ξ i) δ hδ hδ1]
    exact point_le_gMaj N a hδ hN (ξ i)
  -- Step 3: sum inside the integral
  have hsum : ∑ i ∈ s, w i * ‖expSum N a (ξ i)‖ ^ 2
      ≤ ∫ t in Ioc (0 : ℝ) 1, ∑ i ∈ s, w i * (E i).indicator gM t := by
    rw [integral_finset_sum s (fun i _ => ((hgMint.indicator (hEm i)).const_mul (w i)))]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hstep i) (hw i)
  -- Step 4: pointwise majorant
  set H : ℝ → ℝ := fun t => δ * ((1 / 2) * (κ * ‖expSum N a t‖ ^ 2 + κ⁻¹ * ‖expSumD N a t‖ ^ 2))
    with hHdef
  have hHnn : ∀ t, 0 ≤ H t := fun t => by
    simp only [hHdef]
    have := inv_pos.2 hκ
    positivity
  have hpt : ∀ t, ∑ i ∈ s, w i * (E i).indicator gM t
      ≤ Dsup * Zᶜ.indicator (fun t => ‖expSum N a t‖ ^ 2) t + Dsup * H t := by
    intro t
    have hsum_eq : ∑ i ∈ s, w i * (E i).indicator gM t
        = Ddens s ξ w δ t * (‖expSum N a t‖ ^ 2 + H t) := by
      have e1 : ∑ i ∈ s, w i * (E i).indicator gM t
          = (∑ i ∈ s, (if distZ (ξ i - t) ≤ δ / 2 then w i else 0)) * gM t := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : t ∈ E i
        · rw [Set.indicator_of_mem h]
          have h' : distZ (ξ i - t) ≤ δ / 2 := h
          rw [if_pos h']
        · rw [Set.indicator_of_notMem h]
          have h' : ¬ distZ (ξ i - t) ≤ δ / 2 := h
          rw [if_neg h']
          ring
      rw [e1]
      have hDdef : Ddens s ξ w δ t
          = δ⁻¹ * ∑ i ∈ s, (if distZ (ξ i - t) ≤ δ / 2 then w i else 0) := rfl
      rw [hDdef]
      generalize (∑ i ∈ s, (if distZ (ξ i - t) ≤ δ / 2 then w i else 0)) = c
      simp only [hgM, hHdef, gMaj]
      field_simp
    rw [hsum_eq]
    by_cases hz : t ∈ Z
    · have h0 : Ddens s ξ w δ t = 0 := hz
      rw [h0, zero_mul]
      have := hHnn t
      have h2 : 0 ≤ Zᶜ.indicator (fun t => ‖expSum N a t‖ ^ 2) t :=
        Set.indicator_nonneg (fun _ _ => sq_nonneg _) t
      positivity
    · rw [Set.indicator_of_mem (show t ∈ Zᶜ from hz)]
      have h1 := hD t
      have h2 : 0 ≤ ‖expSum N a t‖ ^ 2 + H t := add_nonneg (sq_nonneg _) (hHnn t)
      have := mul_le_mul_of_nonneg_right h1 h2
      linarith
  -- Step 5: integrate the majorant
  have hSint : IntegrableOn (fun t => ‖expSum N a t‖ ^ 2) (Ioc (0 : ℝ) 1) volume :=
    ((hSc.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hHc : Continuous H := by
    simp only [hHdef]
    exact continuous_const.mul (continuous_const.mul
      ((continuous_const.mul (hSc.norm.pow 2)).add (continuous_const.mul (hDc.norm.pow 2))))
  have hHint : IntegrableOn H (Ioc (0 : ℝ) 1) volume :=
    (hHc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hI1 : IntegrableOn (fun t => Dsup * Zᶜ.indicator (fun t => ‖expSum N a t‖ ^ 2) t)
      (Ioc (0 : ℝ) 1) volume := (hSint.indicator hZm.compl).const_mul Dsup
  have hI2 : IntegrableOn (fun t => Dsup * H t) (Ioc (0 : ℝ) 1) volume := hHint.const_mul Dsup
  have hLint : IntegrableOn (fun t => ∑ i ∈ s, w i * (E i).indicator gM t) (Ioc (0 : ℝ) 1) volume :=
    integrable_finset_sum s (fun i _ => ((hgMint.indicator (hEm i)).const_mul (w i)))
  have hmono : ∫ t in Ioc (0 : ℝ) 1, ∑ i ∈ s, w i * (E i).indicator gM t
      ≤ ∫ t in Ioc (0 : ℝ) 1, (Dsup * Zᶜ.indicator (fun t => ‖expSum N a t‖ ^ 2) t + Dsup * H t) :=
    setIntegral_mono hLint (hI1.add hI2) hpt
  rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul,
    setIntegral_indicator hZm.compl] at hmono
  -- the `Z`-split
  have hsplit : ∫ t in Ioc (0 : ℝ) 1 ∩ Zᶜ, ‖expSum N a t‖ ^ 2
      = l2sq N a - ∫ t in Ioc (0 : ℝ) 1 ∩ Z, ‖expSum N a t‖ ^ 2 := by
    have h := integral_inter_add_sdiff (t := Z) hZm hSint
    have hpar : ∫ t in Ioc (0 : ℝ) 1, ‖expSum N a t‖ ^ 2 = l2sq N a := by
      rw [← intervalIntegral.integral_of_le zero_le_one, integral_normSq_expSum]
    rw [← Set.diff_eq]
    linarith
  have hIcoIoc : ∫ t in Ioc (0 : ℝ) 1 ∩ Z, ‖expSum N a t‖ ^ 2
      = ∫ t in Ico (0 : ℝ) 1 ∩ Z, ‖expSum N a t‖ ^ 2 := by
    refine setIntegral_congr_set ?_
    exact (Ico_ae_eq_Ioc.symm).inter (Filter.EventuallyEq.refl _ _)
  -- the derivative part
  have hHval : ∫ t in Ioc (0 : ℝ) 1, H t ≤ Real.pi * N * δ * l2sq N a := by
    have hval : ∫ t in Ioc (0 : ℝ) 1, H t
        = δ * ((1 / 2) * (κ * l2sq N a + κ⁻¹ * ∫ t in (0 : ℝ)..1, ‖expSumD N a t‖ ^ 2)) := by
      rw [← intervalIntegral.integral_of_le zero_le_one]
      simp only [hHdef]
      have iS : IntervalIntegrable (fun t => ‖expSum N a t‖ ^ 2) volume 0 1 :=
        (hSc.norm.pow 2).intervalIntegrable _ _
      have iD : IntervalIntegrable (fun t => ‖expSumD N a t‖ ^ 2) volume 0 1 :=
        (hDc.norm.pow 2).intervalIntegrable _ _
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (iS.const_mul _) (iD.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_normSq_expSum]
    rw [hval]
    have hDle := integral_normSq_expSumD_le N a
    have hkey : κ⁻¹ * (∫ t in (0 : ℝ)..1, ‖expSumD N a t‖ ^ 2) ≤ κ * l2sq N a := by
      rw [inv_mul_le_iff₀ hκ]
      have hp : (Real.pi * ((N : ℝ) - 1)) ^ 2 ≤ κ ^ 2 := by
        rw [hκdef]
        exact pow_le_pow_left₀ (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) 2
      have := mul_le_mul_of_nonneg_right hp hL0
      nlinarith
    have : δ * ((1 / 2) * (κ * l2sq N a + κ⁻¹ * ∫ t in (0 : ℝ)..1, ‖expSumD N a t‖ ^ 2))
        ≤ δ * (κ * l2sq N a) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      linarith
    rw [hκdef] at this
    linarith
  rw [hsplit, hIcoIoc] at hmono
  have hfin := hsum.trans hmono
  have h3 := mul_le_mul_of_nonneg_left hHval hDsup
  have e3 : Dsup * (l2sq N a - (∫ t in Ico (0 : ℝ) 1 ∩ Z, ‖expSum N a t‖ ^ 2)
      + Real.pi * N * δ * l2sq N a)
      = Dsup * (l2sq N a - (∫ t in Ico (0 : ℝ) 1 ∩ Z, ‖expSum N a t‖ ^ 2))
        + Dsup * (Real.pi * N * δ * l2sq N a) := by ring
  rw [e3]
  linarith

/-- **The frozen K2 statement is false as parsed.** `∫ θ in A, f θ + c` is `∫ θ in A, (f θ + c)`, so the
frozen right side is `Dsup·(‖a‖² − ∫_{A∩Z}(|S|² + πNδ‖a‖²))`. Counterexample: `s = ∅` (so `Z = ℝ`),
`N = 1`, `a ≡ 1`, `δ = 1/2`, `Dsup = 1`: left side `0`, right side `1 − (1 + π/2) = −π/2`. -/
theorem gallagher_with_zero_set_false :
    ¬ (∀ (s : Finset Unit) (ξ w : Unit → ℝ) (_hw : ∀ i, 0 ≤ w i)
      (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1) (N : ℕ) (a : ℕ → ℂ) (Dsup : ℝ)
      (_hD : ∀ θ : ℝ, Ddens s ξ w δ θ ≤ Dsup),
    ∑ i ∈ s, w i * ‖ZetaQ.expSum N a (ξ i)‖ ^ 2
      ≤ Dsup * (ZetaQ.l2sq N a
          - ∫ θ in Set.Ico (0 : ℝ) 1 ∩ {θ | Ddens s ξ w δ θ = 0}, ‖ZetaQ.expSum N a θ‖ ^ 2
          + Real.pi * N * δ * ZetaQ.l2sq N a)) := by
  intro h
  have hD0 : ∀ θ : ℝ, Ddens (∅ : Finset Unit) (fun _ => 0) (fun _ => 0) (1 / 2) θ = 0 := by
    intro θ; simp [Ddens]
  have H := h ∅ (fun _ => 0) (fun _ => 0) (fun _ => le_refl 0) (1 / 2) (by norm_num) (by norm_num) 1
    (fun _ => 1) 1 (fun θ => by rw [hD0 θ]; norm_num)
  have hset : Set.Ico (0 : ℝ) 1 ∩ {θ | Ddens (∅ : Finset Unit) (fun _ => 0) (fun _ => 0) (1 / 2) θ = 0}
      = Set.Ico (0 : ℝ) 1 :=
    Set.inter_eq_left.mpr (fun θ _ => hD0 θ)
  rw [hset] at H
  have hl2 : l2sq 1 (fun _ => (1 : ℂ)) = 1 := by simp [l2sq]
  have hSc : Continuous (expSum 1 (fun _ => (1 : ℂ))) := continuous_trig _ _
  have hint : IntegrableOn (fun θ => ‖expSum 1 (fun _ => (1 : ℂ)) θ‖ ^ 2) (Set.Ico (0 : ℝ) 1) volume :=
    ((hSc.norm.pow 2).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  have hpar : ∫ θ in Set.Ico (0 : ℝ) 1, ‖expSum 1 (fun _ => (1 : ℂ)) θ‖ ^ 2 = 1 := by
    rw [setIntegral_congr_set Ico_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_normSq_expSum, hl2]
  rw [integral_add hint (integrableOn_const (by simp)), hpar, setIntegral_const, hl2] at H
  simp only [Finset.sum_empty] at H
  have hvol : (volume.real (Set.Ico (0 : ℝ) 1)) = 1 := by simp
  rw [hvol] at H
  have := Real.pi_pos
  norm_num at H
  linarith

end K2Aux
end LemmaK
end ZetaShell
