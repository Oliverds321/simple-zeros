/-
L10c_ASD2 (L7_10c, 3 Oct 2026): **the integrated region split**
`∫_0^1 |S|² D ≤ H′(‖b‖² − Hole − Ring) + B(Ring + Edge)` (eq:shell-assembly, regions (i)–(iv)), from the pointwise
bound `Ddens_le_Phi` and the periodic conversions of `L10c_ASD`.
-/
import ZetaShell.ShellS.L10c_ASD

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace ShellS
namespace ASc

open TrackF

theorem measurable_distZ' : Measurable distZ := by
  unfold distZ
  exact measurable_fract.min (measurable_const.sub measurable_fract)

theorem measurable_distZ_sub (c : ℝ) : Measurable (fun θ : ℝ => distZ (θ - c)) :=
  measurable_distZ'.comp (measurable_id.sub measurable_const)

theorem measurableSet_dist {c : ℝ} {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {θ : ℝ | distZ (θ - c) ∈ S} := (measurable_distZ_sub c) hS

theorem meas_nbZ (Q : ℕ) (K : ℝ) (x : (_ : ℕ) × ℕ) : MeasurableSet (nbZ Q K x) :=
  measurableSet_dist (S := Set.Iio _) measurableSet_Iio
theorem meas_ringZ (Q : ℕ) (K : ℝ) (x : (_ : ℕ) × ℕ) : MeasurableSet (ringZ Q K x) :=
  measurableSet_dist (S := Set.Ico _ _) measurableSet_Ico
theorem meas_spikeZ (δ : ℝ) (x : (_ : ℕ) × ℕ) : MeasurableSet (spikeZ δ x) :=
  measurableSet_dist (S := Set.Iic _) measurableSet_Iic
theorem meas_edgeZ (Q : ℕ) (δ : ℝ) (x : (_ : ℕ) × ℕ) : MeasurableSet (edgeZ Q δ x) :=
  measurableSet_dist (S := Set.Ico _ _) measurableSet_Ico
theorem meas_ballZ (Δ : ℝ) (x : (_ : ℕ) × ℕ) : MeasurableSet (ballZ Δ x) :=
  measurableSet_dist (S := Set.Iic _) measurableSet_Iic

theorem intOn_g_ind (Nx : ℕ) (b : ℕ → ℂ) {S : Set ℝ} (hS : MeasurableSet S) :
    IntegrableOn (fun θ => ‖ZetaQ.expSum Nx b θ‖ ^ 2 * S.indicator (fun _ => (1 : ℝ)) θ) (Set.Ico (0 : ℝ) 1) := by
  refine ((g_cont Nx b).integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self |>.mul_bdd
    (c := 1) ((measurable_const.indicator hS).aestronglyMeasurable) (ae_of_all _ fun θ => ?_)
  by_cases h : θ ∈ S
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simp

theorem measurable_Ddens (Q : ℕ) (W : (_ : ℕ) × ℕ → ℝ) (δ : ℝ) :
    Measurable (Ddens (fareyIdx Q) fareyPt W δ) := by
  unfold Ddens
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (measurable_distZ'.comp (measurable_const.sub measurable_id)) measurable_const

open Classical in
/-- **The integrated region split.** -/
theorem int_split (Q Nx R1n : ℕ) (b : ℕ → ℂ) (K Hp Bm δ R0 Δ : ℝ) (W : (_ : ℕ) × ℕ → ℝ)
    (hR1Q : R1n ≤ Q) (hK1 : 1 ≤ K)
    (hsep : ∀ r r' : ℕ, 1 ≤ r → r ≤ R1n → 1 ≤ r' → r' ≤ R1n → K * ((r : ℝ) + r') ≤ Q)
    (hKhalf : ∀ r : ℕ, 1 ≤ r → r ≤ R1n → K / ((r : ℝ) * Q) ≤ 1 / 2)
    (hHp : 0 ≤ Hp) (hBm : 0 ≤ Bm) (hδ0 : 0 < δ) (hδh : δ / 2 < 1 / 2)
    (hΔ0 : 0 ≤ Δ) (hΔh : Δ < 1 / 2) (hR0 : ⌊R0⌋₊ ≤ R1n)
    (hΔr : ∀ r : ℕ, 1 ≤ r → r ≤ ⌊R0⌋₊ → Δ < 1 / ((r : ℝ) * Q))
    (hoff : ∀ θ, (∀ x ∈ X1 R1n, θ ∉ nbZ Q K x) → Ddens (fareyIdx Q) fareyPt W δ θ ≤ Hp)
    (hall : ∀ θ, |Ddens (fareyIdx Q) fareyPt W δ θ| ≤ Bm) :
    (∫ θ in Set.Ico (0 : ℝ) 1, ‖ZetaQ.expSum Nx b θ‖ ^ 2 * Ddens (fareyIdx Q) fareyPt W δ θ)
      ≤ Hp * (ZetaQ.l2sq Nx b - LemmaK.holeInt Nx b R0 Δ - ringMass Q R1n Nx K b)
        + Bm * (ringMass Q R1n Nx K b
          + ∑ x ∈ X1 R1n, ((∫ β in (-(δ / 2))..(δ / 2), ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
            + (∫ β in (1 / ((x.1 : ℝ) * Q) - δ / 2)..(1 / ((x.1 : ℝ) * Q) + δ / 2),
                ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
            + ∫ β in (-(1 / ((x.1 : ℝ) * Q)) - δ / 2)..(-(1 / ((x.1 : ℝ) * Q)) + δ / 2),
                ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)) := by
  set g : ℝ → ℝ := fun θ => ‖ZetaQ.expSum Nx b θ‖ ^ 2 with hg
  set D := Ddens (fareyIdx Q) fareyPt W δ with hD
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ => sq_nonneg _
  set ind : Set ℝ → ℝ → ℝ := fun S θ => S.indicator (fun _ => (1 : ℝ)) θ with hind
  -- integrability
  have hgI : IntegrableOn g (Set.Ico (0 : ℝ) 1) :=
    ((g_cont Nx b).integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  have hgD : IntegrableOn (fun θ => g θ * D θ) (Set.Ico (0 : ℝ) 1) :=
    hgI.mul_bdd (c := Bm) (measurable_Ddens Q W δ).aestronglyMeasurable
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hall θ)
  have hI : ∀ {S : Set ℝ}, MeasurableSet S → IntegrableOn (fun θ => g θ * ind S θ) (Set.Ico (0 : ℝ) 1) :=
    fun hS => intOn_g_ind Nx b hS
  set Phi : ℝ → ℝ := fun θ => Hp - Hp * ∑ x ∈ X1 R1n, ind (nbZ Q K x) θ
        + Bm * ∑ x ∈ X1 R1n, (ind (ringZ Q K x) θ + ind (spikeZ δ x) θ + ind (edgeZ Q δ x) θ) with hPhi
  have hgPhi_eq : ∀ θ, g θ * Phi θ = Hp * g θ - Hp * ∑ x ∈ X1 R1n, g θ * ind (nbZ Q K x) θ
      + Bm * ∑ x ∈ X1 R1n, (g θ * ind (ringZ Q K x) θ + g θ * ind (spikeZ δ x) θ
          + g θ * ind (edgeZ Q δ x) θ) := by
    intro θ
    have hA : ∑ x ∈ X1 R1n, g θ * ind (nbZ Q K x) θ = g θ * ∑ x ∈ X1 R1n, ind (nbZ Q K x) θ :=
      (Finset.mul_sum _ _ _).symm
    have hB : ∑ x ∈ X1 R1n, (g θ * ind (ringZ Q K x) θ + g θ * ind (spikeZ δ x) θ + g θ * ind (edgeZ Q δ x) θ)
        = g θ * ∑ x ∈ X1 R1n, (ind (ringZ Q K x) θ + ind (spikeZ δ x) θ + ind (edgeZ Q δ x) θ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    rw [hA, hB]
    simp only [hPhi]
    ring
  -- the pieces
  set Inb : ((_ : ℕ) × ℕ) → ℝ := fun x => ∫ θ in Set.Ico (0 : ℝ) 1, g θ * ind (nbZ Q K x) θ with hInb
  set Iri : ((_ : ℕ) × ℕ) → ℝ := fun x => ∫ θ in Set.Ico (0 : ℝ) 1, g θ * ind (ringZ Q K x) θ with hIri
  set Isp : ((_ : ℕ) × ℕ) → ℝ := fun x => ∫ θ in Set.Ico (0 : ℝ) 1, g θ * ind (spikeZ δ x) θ with hIsp
  set Ied : ((_ : ℕ) × ℕ) → ℝ := fun x => ∫ θ in Set.Ico (0 : ℝ) 1, g θ * ind (edgeZ Q δ x) θ with hIed
  have hInt1 : IntegrableOn (fun θ => Hp * g θ) (Set.Ico (0 : ℝ) 1) := hgI.const_mul Hp
  have hInt2 : IntegrableOn (fun θ => Hp * ∑ x ∈ X1 R1n, g θ * ind (nbZ Q K x) θ) (Set.Ico (0 : ℝ) 1) :=
    (integrable_finsetSum _ fun x _ => hI (meas_nbZ Q K x)).const_mul Hp
  have hI3 : ∀ x, IntegrableOn (fun θ => g θ * ind (ringZ Q K x) θ + g θ * ind (spikeZ δ x) θ
      + g θ * ind (edgeZ Q δ x) θ) (Set.Ico (0 : ℝ) 1) := fun x =>
    ((hI (meas_ringZ Q K x)).add (hI (meas_spikeZ δ x))).add (hI (meas_edgeZ Q δ x))
  have hI2' : ∀ x, IntegrableOn (fun θ => g θ * ind (ringZ Q K x) θ + g θ * ind (spikeZ δ x) θ)
      (Set.Ico (0 : ℝ) 1) := fun x => (hI (meas_ringZ Q K x)).add (hI (meas_spikeZ δ x))
  have hInt3 : IntegrableOn (fun θ => Bm * ∑ x ∈ X1 R1n, (g θ * ind (ringZ Q K x) θ + g θ * ind (spikeZ δ x) θ
      + g θ * ind (edgeZ Q δ x) θ)) (Set.Ico (0 : ℝ) 1) :=
    (integrable_finsetSum _ fun x _ => hI3 x).const_mul Bm
  have hInt12 : IntegrableOn (fun θ => Hp * g θ - Hp * ∑ x ∈ X1 R1n, g θ * ind (nbZ Q K x) θ)
      (Set.Ico (0 : ℝ) 1) := hInt1.sub hInt2
  have hPhiInt : (∫ θ in Set.Ico (0 : ℝ) 1, g θ * Phi θ)
      = Hp * (∫ θ in Set.Ico (0 : ℝ) 1, g θ) - Hp * ∑ x ∈ X1 R1n, Inb x
        + Bm * ∑ x ∈ X1 R1n, (Iri x + Isp x + Ied x) := by
    rw [show (fun θ => g θ * Phi θ) = fun θ => Hp * g θ - Hp * ∑ x ∈ X1 R1n, g θ * ind (nbZ Q K x) θ
      + Bm * ∑ x ∈ X1 R1n, (g θ * ind (ringZ Q K x) θ + g θ * ind (spikeZ δ x) θ
          + g θ * ind (edgeZ Q δ x) θ) from funext hgPhi_eq]
    rw [integral_add hInt12 hInt3, integral_sub hInt1 hInt2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun x _ => hI (meas_nbZ Q K x),
      integral_finsetSum _ fun x _ => hI3 x]
    congr 2
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_add (hI2' x) (hI (meas_edgeZ Q δ x)), integral_add (hI (meas_ringZ Q K x)) (hI (meas_spikeZ δ x))]
  have hPhiI : IntegrableOn (fun θ => g θ * Phi θ) (Set.Ico (0 : ℝ) 1) := by
    rw [show (fun θ => g θ * Phi θ) = fun θ => Hp * g θ - Hp * ∑ x ∈ X1 R1n, g θ * ind (nbZ Q K x) θ
      + Bm * ∑ x ∈ X1 R1n, (g θ * ind (ringZ Q K x) θ + g θ * ind (spikeZ δ x) θ
          + g θ * ind (edgeZ Q δ x) θ) from funext hgPhi_eq]
    exact hInt12.add hInt3
  have hstep1 : (∫ θ in Set.Ico (0 : ℝ) 1, g θ * D θ) ≤ ∫ θ in Set.Ico (0 : ℝ) 1, g θ * Phi θ := by
    refine setIntegral_mono_on hgD hPhiI measurableSet_Ico fun θ _ => ?_
    have h := Ddens_le_Phi Q R1n K Hp Bm δ W hR1Q hK1 hsep hHp hBm hoff
      (fun θ => le_trans (le_abs_self _) (hall θ)) θ
    exact mul_le_mul_of_nonneg_left h (hg0 θ)
  -- Parseval
  have hpars : (∫ θ in Set.Ico (0 : ℝ) 1, g θ) = ZetaQ.l2sq Nx b := by
    rw [Ico_eq_interval]; exact ZetaQ.Gallagher.integral_normSq_expSum Nx b
  -- rings
  have hring : ∑ x ∈ X1 R1n, Iri x = ringMass Q R1n Nx K b := by
    unfold ringMass X1
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun c _ => ?_
    have hr' := Finset.mem_Icc.mp hr
    exact ring_int Q Nx b K ⟨r, c⟩ (hKhalf r hr'.1 hr'.2)
  -- holes
  have hhole : ∑ x ∈ X1 R1n, (if x.1 ≤ ⌊R0⌋₊ then
        ∫ θ in Set.Ico (0 : ℝ) 1, g θ * ind (ballZ Δ x) θ else 0) = LemmaK.holeInt Nx b R0 Δ := by
    unfold LemmaK.holeInt X1
    rw [Finset.sum_sigma]
    have e : ∀ r ∈ Finset.Icc 1 R1n, (∑ c ∈ ZetaQ.reducedResidues r, (if (⟨r, c⟩ : (_ : ℕ) × ℕ).1 ≤ ⌊R0⌋₊ then
        ∫ θ in Set.Ico (0 : ℝ) 1, g θ * ind (ballZ Δ ⟨r, c⟩) θ else 0))
        = if r ≤ ⌊R0⌋₊ then ∑ c ∈ ZetaQ.reducedResidues r,
            ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum Nx b ((c : ℝ) / r + β)‖ ^ 2 else 0 := by
      intro r _
      split_ifs with h
      · exact Finset.sum_congr rfl fun c _ => ball_int Nx b Δ hΔ0 hΔh ⟨r, c⟩
      · simp
    rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hR0⟩, h2⟩
  -- the neighbourhood mass dominates rings and holes
  have hnb : ∀ x ∈ X1 R1n, Iri x + (if x.1 ≤ ⌊R0⌋₊ then
      ∫ θ in Set.Ico (0 : ℝ) 1, g θ * ind (ballZ Δ x) θ else 0) ≤ Inb x := by
    intro x hx
    have hx1 := (mem_X1.mp hx).1
    split_ifs with hr
    · rw [hIri, hInb, ← integral_add (hI (meas_ringZ Q K x)) (hI (meas_ballZ Δ x))]
      refine setIntegral_mono_on ((hI (meas_ringZ Q K x)).add (hI (meas_ballZ Δ x))) (hI (meas_nbZ Q K x))
        measurableSet_Ico fun θ _ => ?_
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (hg0 θ)
      have hΔx := hΔr x.1 hx1.1 hr
      by_cases hb : θ ∈ ballZ Δ x
      · have hnr : θ ∉ ringZ Q K x := fun h => by
          have h1 : distZ (θ - fareyPt x) ≤ Δ := hb
          have h2 := h.1
          linarith
        have hnb' : θ ∈ nbZ Q K x := by
          have h1 : distZ (θ - fareyPt x) ≤ Δ := hb
          have : 1 / ((x.1 : ℝ) * Q) ≤ K / ((x.1 : ℝ) * Q) := div_le_div_of_nonneg_right hK1 (by positivity)
          show distZ (θ - fareyPt x) < K / ((x.1 : ℝ) * Q)
          linarith
        simp only [hind]
        rw [Set.indicator_of_notMem hnr, Set.indicator_of_mem hb, Set.indicator_of_mem hnb']
        norm_num
      · simp only [hind]
        rw [Set.indicator_of_notMem hb, add_zero]
        by_cases hrr : θ ∈ ringZ Q K x
        · rw [Set.indicator_of_mem hrr, Set.indicator_of_mem (show θ ∈ nbZ Q K x from hrr.2)]
        · rw [Set.indicator_of_notMem hrr]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) θ
    · rw [add_zero, hIri, hInb]
      refine setIntegral_mono_on (hI (meas_ringZ Q K x)) (hI (meas_nbZ Q K x)) measurableSet_Ico fun θ _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (hg0 θ)
      simp only [hind]
      by_cases hrr : θ ∈ ringZ Q K x
      · rw [Set.indicator_of_mem hrr, Set.indicator_of_mem (show θ ∈ nbZ Q K x from hrr.2)]
      · rw [Set.indicator_of_notMem hrr]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) θ
  have hnbsum : ringMass Q R1n Nx K b + LemmaK.holeInt Nx b R0 Δ ≤ ∑ x ∈ X1 R1n, Inb x := by
    rw [← hring, ← hhole, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hnb
  -- spikes and edges
  have hse : ∀ x ∈ X1 R1n, Isp x + Ied x
      ≤ (∫ β in (-(δ / 2))..(δ / 2), ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
        + (∫ β in (1 / ((x.1 : ℝ) * Q) - δ / 2)..(1 / ((x.1 : ℝ) * Q) + δ / 2),
            ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
        + ∫ β in (-(1 / ((x.1 : ℝ) * Q)) - δ / 2)..(-(1 / ((x.1 : ℝ) * Q)) + δ / 2),
            ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2 := by
    intro x _
    have h1 : Isp x = ∫ β in (-(δ / 2))..(δ / 2), ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2 :=
      ball_int Nx b (δ / 2) (by linarith) hδh x
    have h2 := edge_int Q Nx b δ hδ0.le x
    rw [h1]
    have : Ied x = ∫ θ in Set.Ico (0 : ℝ) 1, ‖ZetaQ.expSum Nx b θ‖ ^ 2 * (edgeZ Q δ x).indicator (fun _ => (1 : ℝ)) θ :=
      rfl
    linarith
  have hse_sum : ∑ x ∈ X1 R1n, (Iri x + Isp x + Ied x) ≤ ringMass Q R1n Nx K b
      + ∑ x ∈ X1 R1n, ((∫ β in (-(δ / 2))..(δ / 2), ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
            + (∫ β in (1 / ((x.1 : ℝ) * Q) - δ / 2)..(1 / ((x.1 : ℝ) * Q) + δ / 2),
                ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
            + ∫ β in (-(1 / ((x.1 : ℝ) * Q)) - δ / 2)..(-(1 / ((x.1 : ℝ) * Q)) + δ / 2),
                ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2) := by
    rw [← hring, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x hx => by have := hse x hx; linarith
  -- combine
  have hfin := hstep1
  rw [hPhiInt, hpars] at hfin
  have h1 := mul_le_mul_of_nonneg_left hnbsum hHp
  have h2 := mul_le_mul_of_nonneg_left hse_sum hBm
  nlinarith

end ASc
end ShellS
end ZetaShell
