/-
L10c_ASD (L7_10c, 3 Oct 2026): **the region split of `∫_0^1 |S|² D^Ω_δ`** (eq:shell-assembly, regions (i)–(iv)).
Pointwise: `D ≤ H′ − H′ Σ_x 1_{nb x} + B Σ_x (1_{ring x} + 1_{spike x} + 1_{edge x})` over the Farey points `x` of
denominator `≤ R₁` (their neighbourhoods `‖θ − ξ_x‖ < K/(rQ)` are disjoint since `K(r + r′) ≤ Q`): off the shells
`D ≤ H′` (Lemma 2(a), as hypothesis), on rings, spikes and hole edges `D ≤ B` (Lemma 2(b)), and inside a hole
`D = 0` (Lemma 2(c)). Then integrate against `|S|²` and convert each piece to the `β`-integrals of `Ring`, `Hole` and
AF1's edge sum by periodicity.
-/
import ZetaShell.ShellS.L10c_ASF
import ZetaShell.Lemma2.A2c_Holes
import ZetaShell.LemmaK.LK_K7_HoleLe

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace ShellS
namespace ASc

open TrackF

/-! ### `distZ` and `Ddens` are 1-periodic -/

theorem distZ_add_int (x : ℝ) (m : ℤ) : distZ (x + m) = distZ x := by
  unfold distZ; rw [Int.fract_add_intCast]

theorem distZ_sub_int (x : ℝ) (m : ℤ) : distZ (x - m) = distZ x := by
  unfold distZ; rw [Int.fract_sub_intCast]

theorem distZ_of_abs_le (x : ℝ) (hx : |x| ≤ 1 / 2) : distZ x = |x| := by
  apply le_antisymm
  · have := distZ_le x 0; simpa using this
  · obtain ⟨m, hm⟩ := distZ_eq x
    rw [hm]
    by_cases h0 : m = 0
    · subst h0; simp
    · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        have : (1 : ℤ) ≤ |m| := Int.one_le_abs h0
        exact_mod_cast this
      have h1 : |(m : ℝ)| ≤ |x - m| + |x| := by
        calc |(m : ℝ)| = |x - (x - m)| := by ring_nf
          _ ≤ |x| + |x - m| := abs_sub _ _
          _ = |x - m| + |x| := by ring
      linarith

theorem Ddens_add_int {ι : Type} (s : Finset ι) (ξ w : ι → ℝ) (δ θ : ℝ) (m : ℤ) :
    Ddens s ξ w δ (θ + m) = Ddens s ξ w δ θ := by
  unfold Ddens
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ξ i - (θ + m) = (ξ i - θ) - m by ring, distZ_sub_int]

/-! ### the pointwise bound -/

/-- the Farey points of denominator `≤ R₁`. -/
def X1 (R1n : ℕ) : Finset ((_ : ℕ) × ℕ) := (Finset.Icc 1 R1n).sigma ZetaQ.reducedResidues

def nbZ (Q : ℕ) (K : ℝ) (x : (_ : ℕ) × ℕ) : Set ℝ := {θ | distZ (θ - fareyPt x) < K / ((x.1 : ℝ) * Q)}
def ringZ (Q : ℕ) (K : ℝ) (x : (_ : ℕ) × ℕ) : Set ℝ :=
  {θ | 1 / ((x.1 : ℝ) * Q) ≤ distZ (θ - fareyPt x) ∧ distZ (θ - fareyPt x) < K / ((x.1 : ℝ) * Q)}
def spikeZ (δ : ℝ) (x : (_ : ℕ) × ℕ) : Set ℝ := {θ | distZ (θ - fareyPt x) ≤ δ / 2}
def edgeZ (Q : ℕ) (δ : ℝ) (x : (_ : ℕ) × ℕ) : Set ℝ :=
  {θ | 1 / ((x.1 : ℝ) * Q) - δ / 2 ≤ distZ (θ - fareyPt x) ∧ distZ (θ - fareyPt x) < 1 / ((x.1 : ℝ) * Q)}
def ballZ (Δ : ℝ) (x : (_ : ℕ) × ℕ) : Set ℝ := {θ | distZ (θ - fareyPt x) ≤ Δ}

theorem mem_X1 {R1n : ℕ} {x : (_ : ℕ) × ℕ} : x ∈ X1 R1n ↔ (1 ≤ x.1 ∧ x.1 ≤ R1n) ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1 := by
  unfold X1
  rw [Finset.mem_sigma, Finset.mem_Icc, ZetaQ.mem_reducedResidues]

theorem X1_sub {Q R1n : ℕ} (h : R1n ≤ Q) {x : (_ : ℕ) × ℕ} (hx : x ∈ X1 R1n) : x ∈ fareyIdx Q := by
  rw [mem_X1] at hx; rw [mem_fareyIdx]
  exact ⟨⟨hx.1.1, le_trans hx.1.2 h⟩, hx.2⟩

/-- the neighbourhoods are pairwise disjoint. -/
theorem nbZ_disjoint {Q R1n : ℕ} {K : ℝ} (hR1Q : R1n ≤ Q)
    (hsep : ∀ r r' : ℕ, 1 ≤ r → r ≤ R1n → 1 ≤ r' → r' ≤ R1n → K * ((r : ℝ) + r') ≤ Q)
    {x y : (_ : ℕ) × ℕ} (hx : x ∈ X1 R1n) (hy : y ∈ X1 R1n) (hxy : x ≠ y) (θ : ℝ)
    (h1 : θ ∈ nbZ Q K x) (h2 : θ ∈ nbZ Q K y) : False := by
  have hgap := farey_gap_idx (X1_sub hR1Q hx) (X1_sub hR1Q hy) hxy
  have hx' := (mem_X1.mp hx).1
  have hy' := (mem_X1.mp hy).1
  have hr : (1 : ℝ) ≤ x.1 := by exact_mod_cast hx'.1
  have hr' : (1 : ℝ) ≤ y.1 := by exact_mod_cast hy'.1
  have hQ : (1 : ℝ) ≤ Q := by
    have : 1 ≤ Q := le_trans hx'.1 (le_trans hx'.2 hR1Q)
    exact_mod_cast this
  have htri : distZ (fareyPt x - fareyPt y) ≤ distZ (θ - fareyPt x) + distZ (θ - fareyPt y) := by
    have := distZ_add_le (-(θ - fareyPt x)) (θ - fareyPt y)
    rw [distZ_neg] at this
    rw [show fareyPt x - fareyPt y = -(θ - fareyPt x) + (θ - fareyPt y) by ring] at *
    linarith
  have hs := hsep x.1 y.1 hx'.1 hx'.2 hy'.1 hy'.2
  have hsum : K / ((x.1 : ℝ) * Q) + K / ((y.1 : ℝ) * Q) ≤ 1 / ((x.1 : ℝ) * y.1) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (K * ((y.1 : ℝ) * Q) + (x.1 : ℝ) * Q * K) * ((x.1 : ℝ) * y.1)
        = (K * ((x.1 : ℝ) + y.1)) * ((x.1 : ℝ) * y.1 * Q) := by ring
    rw [e]
    have : 0 ≤ (x.1 : ℝ) * y.1 * Q := by positivity
    calc (K * ((x.1 : ℝ) + y.1)) * ((x.1 : ℝ) * y.1 * Q) ≤ (Q : ℝ) * ((x.1 : ℝ) * y.1 * Q) :=
          mul_le_mul_of_nonneg_right hs this
      _ = 1 * ((x.1 : ℝ) * Q * ((y.1 : ℝ) * Q)) := by ring
  have h1' : distZ (θ - fareyPt x) < K / ((x.1 : ℝ) * Q) := h1
  have h2' : distZ (θ - fareyPt y) < K / ((y.1 : ℝ) * Q) := h2
  linarith

/-- inside a hole, off the spike and the edges, the density vanishes. -/
theorem Ddens_hole_zero {Q R1n : ℕ} (hR1Q : R1n ≤ Q) (W : (_ : ℕ) × ℕ → ℝ) (δ : ℝ)
    {x : (_ : ℕ) × ℕ} (hx : x ∈ X1 R1n) (θ : ℝ) (h1 : δ / 2 < distZ (θ - fareyPt x))
    (h2 : distZ (θ - fareyPt x) < 1 / ((x.1 : ℝ) * Q) - δ / 2) :
    Ddens (fareyIdx Q) fareyPt W δ θ = 0 := by
  obtain ⟨m, hm⟩ := distZ_eq (θ - fareyPt x)
  have hx0 : (⟨x.1, x.2⟩ : (_ : ℕ) × ℕ) ∈ fareyIdx Q := X1_sub hR1Q hx
  have h := lemma2c_hole Q x.1 x.2 hx0 W δ (θ - fareyPt x - m) (by rw [← hm]; exact h1) (by rw [← hm]; exact h2)
  have e : (x.2 : ℝ) / x.1 + (θ - fareyPt x - m) = θ + ((-m : ℤ) : ℝ) := by
    unfold fareyPt; push_cast; ring
  rw [e, Ddens_add_int] at h
  exact h

open Classical in
/-- **the pointwise bound of the density.** -/
theorem Ddens_le_Phi (Q R1n : ℕ) (K Hp Bm δ : ℝ) (W : (_ : ℕ) × ℕ → ℝ) (hR1Q : R1n ≤ Q) (hK1 : 1 ≤ K)
    (hsep : ∀ r r' : ℕ, 1 ≤ r → r ≤ R1n → 1 ≤ r' → r' ≤ R1n → K * ((r : ℝ) + r') ≤ Q)
    (hHp : 0 ≤ Hp) (hBm : 0 ≤ Bm)
    (hoff : ∀ θ, (∀ x ∈ X1 R1n, θ ∉ nbZ Q K x) → Ddens (fareyIdx Q) fareyPt W δ θ ≤ Hp)
    (hall : ∀ θ, Ddens (fareyIdx Q) fareyPt W δ θ ≤ Bm) (θ : ℝ) :
    Ddens (fareyIdx Q) fareyPt W δ θ
      ≤ Hp - Hp * ∑ x ∈ X1 R1n, (nbZ Q K x).indicator (fun _ => (1 : ℝ)) θ
        + Bm * ∑ x ∈ X1 R1n, ((ringZ Q K x).indicator (fun _ => (1 : ℝ)) θ
            + (spikeZ δ x).indicator (fun _ => (1 : ℝ)) θ + (edgeZ Q δ x).indicator (fun _ => (1 : ℝ)) θ) := by
  have hsubR : ∀ x, ringZ Q K x ⊆ nbZ Q K x := fun x θ h => h.2
  have hsubE : ∀ x, edgeZ Q δ x ⊆ nbZ Q K x := by
    intro x θ h
    have hpos : 0 < (x.1 : ℝ) * Q ∨ (x.1 : ℝ) * Q = 0 := by
      rcases (show (0 : ℝ) ≤ (x.1 : ℝ) * Q by positivity).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    have h2 : 1 / ((x.1 : ℝ) * Q) ≤ K / ((x.1 : ℝ) * Q) := div_le_div_of_nonneg_right hK1 (by positivity)
    exact lt_of_lt_of_le h.2 h2
  have hi0 : ∀ S : Set ℝ, 0 ≤ S.indicator (fun _ => (1 : ℝ)) θ := fun S =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) θ
  have hT0 : ∀ x ∈ X1 R1n, 0 ≤ (ringZ Q K x).indicator (fun _ => (1 : ℝ)) θ
      + (spikeZ δ x).indicator (fun _ => (1 : ℝ)) θ + (edgeZ Q δ x).indicator (fun _ => (1 : ℝ)) θ :=
    fun x _ => by linarith [hi0 (ringZ Q K x), hi0 (spikeZ δ x), hi0 (edgeZ Q δ x)]
  have hS0 := Finset.sum_nonneg hT0
  by_cases hin : ∃ x ∈ X1 R1n, θ ∈ nbZ Q K x
  · obtain ⟨x₀, hx₀, hθ⟩ := hin
    have hothers : ∀ x ∈ X1 R1n, x ≠ x₀ → θ ∉ nbZ Q K x := fun x hx hne h =>
      nbZ_disjoint hR1Q hsep hx hx₀ hne θ h hθ
    have hs1 : ∑ x ∈ X1 R1n, (nbZ Q K x).indicator (fun _ => (1 : ℝ)) θ = 1 := by
      rw [Finset.sum_eq_single x₀ (fun x hx hne => Set.indicator_of_notMem (hothers x hx hne) _)
        (fun h => absurd hx₀ h), Set.indicator_of_mem hθ]
    have hs2 : (ringZ Q K x₀).indicator (fun _ => (1 : ℝ)) θ
          + (spikeZ δ x₀).indicator (fun _ => (1 : ℝ)) θ + (edgeZ Q δ x₀).indicator (fun _ => (1 : ℝ)) θ
        ≤ ∑ x ∈ X1 R1n, ((ringZ Q K x).indicator (fun _ => (1 : ℝ)) θ
          + (spikeZ δ x).indicator (fun _ => (1 : ℝ)) θ + (edgeZ Q δ x).indicator (fun _ => (1 : ℝ)) θ) :=
      Finset.single_le_sum (f := fun x => (ringZ Q K x).indicator (fun _ => (1 : ℝ)) θ
          + (spikeZ δ x).indicator (fun _ => (1 : ℝ)) θ + (edgeZ Q δ x).indicator (fun _ => (1 : ℝ)) θ)
        hT0 hx₀
    rw [hs1, mul_one, sub_self, zero_add]
    by_cases hr : θ ∈ ringZ Q K x₀ ∨ θ ∈ spikeZ δ x₀ ∨ θ ∈ edgeZ Q δ x₀
    · have hge : 1 ≤ (ringZ Q K x₀).indicator (fun _ => (1 : ℝ)) θ
          + (spikeZ δ x₀).indicator (fun _ => (1 : ℝ)) θ + (edgeZ Q δ x₀).indicator (fun _ => (1 : ℝ)) θ := by
        rcases hr with h | h | h
        · rw [Set.indicator_of_mem h]; linarith [hi0 (spikeZ δ x₀), hi0 (edgeZ Q δ x₀)]
        · rw [Set.indicator_of_mem h (f := fun _ => (1 : ℝ))]; linarith [hi0 (ringZ Q K x₀), hi0 (edgeZ Q δ x₀)]
        · rw [Set.indicator_of_mem h (f := fun _ => (1 : ℝ))]; linarith [hi0 (ringZ Q K x₀), hi0 (spikeZ δ x₀)]
      have := mul_le_mul_of_nonneg_left (le_trans hge hs2) hBm
      linarith [hall θ]
    · push Not at hr
      obtain ⟨hr1, hr2, hr3⟩ := hr
      have hd : distZ (θ - fareyPt x₀) < K / ((x₀.1 : ℝ) * Q) := hθ
      have e1 : distZ (θ - fareyPt x₀) < 1 / ((x₀.1 : ℝ) * Q) := by
        by_contra h; push Not at h; exact hr1 ⟨h, hd⟩
      have e2 : δ / 2 < distZ (θ - fareyPt x₀) := by
        by_contra h; push Not at h; exact hr2 h
      have e3 : distZ (θ - fareyPt x₀) < 1 / ((x₀.1 : ℝ) * Q) - δ / 2 := by
        by_contra h; push Not at h; exact hr3 ⟨h, e1⟩
      rw [Ddens_hole_zero hR1Q W δ hx₀ θ e2 e3]
      exact mul_nonneg hBm hS0
  · push Not at hin
    have hz : ∀ x ∈ X1 R1n, (nbZ Q K x).indicator (fun _ => (1 : ℝ)) θ = 0 := fun x hx =>
      Set.indicator_of_notMem (hin x hx) _
    rw [Finset.sum_eq_zero hz, mul_zero, sub_zero]
    have := mul_nonneg hBm hS0
    linarith [hoff θ hin]

/-! ### periodic integrals -/

theorem Ico_eq_interval (f : ℝ → ℝ) : (∫ θ in Set.Ico (0 : ℝ) 1, f θ) = ∫ θ in (0 : ℝ)..1, f θ := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

/-- `∫_0^1 g(θ) ψ(‖θ − c‖) dθ = ∫_{−1/2}^{1/2} g(c + β) ψ(|β|) dβ` for 1-periodic `g`. -/
theorem per_int (g : ℝ → ℝ) (hgp : Function.Periodic g 1) (c : ℝ) (ψ : ℝ → ℝ) :
    (∫ θ in Set.Ico (0 : ℝ) 1, g θ * ψ (distZ (θ - c)))
      = ∫ β in (-(1 / 2) : ℝ)..(1 / 2), g (c + β) * ψ |β| := by
  set h : ℝ → ℝ := fun θ => g θ * ψ (distZ (θ - c)) with hh
  have hper : Function.Periodic h 1 := by
    intro θ
    simp only [hh]
    rw [hgp θ, show θ + 1 - c = (θ - c) + ((1 : ℤ) : ℝ) by push_cast; ring, distZ_add_int]
  rw [Ico_eq_interval]
  have e1 := hper.intervalIntegral_add_eq 0 (c - 1 / 2)
  rw [zero_add] at e1
  rw [e1, show c - 1 / 2 + 1 = c + 1 / 2 by ring]
  have e2 := intervalIntegral.integral_comp_add_left h c (a := -(1 / 2 : ℝ)) (b := 1 / 2)
  rw [show c + -(1 / 2 : ℝ) = c - 1 / 2 by ring] at e2
  rw [← e2]
  refine intervalIntegral.integral_congr fun β hβ => ?_
  rw [Set.uIcc_of_le (by norm_num)] at hβ
  simp only [hh]
  rw [show c + β - c = β by ring, distZ_of_abs_le β (abs_le.mpr ⟨hβ.1, hβ.2⟩)]

theorem g_periodic (Nx : ℕ) (b : ℕ → ℂ) : Function.Periodic (fun θ => ‖ZetaQ.expSum Nx b θ‖ ^ 2) 1 :=
  LemmaK.expSum_normSq_periodic Nx b

theorem g_cont (Nx : ℕ) (b : ℕ → ℂ) : Continuous (fun θ => ‖ZetaQ.expSum Nx b θ‖ ^ 2) :=
  LemmaK.expSum_normSq_continuous Nx b

theorem indicator_distZ (S : Set ℝ) (c θ : ℝ) :
    ({θ' : ℝ | distZ (θ' - c) ∈ S}).indicator (fun _ => (1 : ℝ)) θ
      = S.indicator (fun _ => (1 : ℝ)) (distZ (θ - c)) := by
  by_cases h : distZ (θ - c) ∈ S
  · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ | distZ (θ' - c) ∈ S} from h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ | distZ (θ' - c) ∈ S} from h), Set.indicator_of_notMem h]

/-- the ring integral. -/
theorem ring_int (Q Nx : ℕ) (b : ℕ → ℂ) (K : ℝ) (x : (_ : ℕ) × ℕ) (hK : K / ((x.1 : ℝ) * Q) ≤ 1 / 2) :
    (∫ θ in Set.Ico (0 : ℝ) 1, ‖ZetaQ.expSum Nx b θ‖ ^ 2 * (ringZ Q K x).indicator (fun _ => (1 : ℝ)) θ)
      = ∫ β in ringSet Q K x.1, ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2 := by
  set S : Set ℝ := Set.Ico (1 / ((x.1 : ℝ) * Q)) (K / ((x.1 : ℝ) * Q)) with hS
  have e0 : ∀ θ, (ringZ Q K x).indicator (fun _ => (1 : ℝ)) θ = S.indicator (fun _ => (1 : ℝ)) (distZ (θ - fareyPt x)) := by
    intro θ
    rw [← indicator_distZ]; rfl
  simp_rw [e0]
  rw [per_int _ (g_periodic Nx b) (fareyPt x) (S.indicator fun _ => (1 : ℝ))]
  rw [intervalIntegral.integral_of_le (by norm_num)]
  have e1 : ∀ β, ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2 * S.indicator (fun _ => (1 : ℝ)) |β|
      = (ringSet Q K x.1).indicator (fun β => ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2) β := by
    intro β
    by_cases h : |β| ∈ S
    · rw [Set.indicator_of_mem h, mul_one, Set.indicator_of_mem]
      exact ⟨h.1, h.2⟩
    · rw [Set.indicator_of_notMem h, mul_zero, Set.indicator_of_notMem]
      exact fun h' => h ⟨h'.1, h'.2⟩
  simp_rw [e1]
  have hmeas : MeasurableSet (ringSet Q K x.1) := by
    unfold ringSet
    exact (measurableSet_le measurable_const measurable_abs).inter (measurableSet_lt measurable_abs measurable_const)
  rw [setIntegral_indicator hmeas]
  have hsub : ringSet Q K x.1 ⊆ Set.Ioc (-(1 / 2) : ℝ) (1 / 2) := by
    intro β hβ
    have h1 : |β| < 1 / 2 := lt_of_lt_of_le hβ.2 hK
    exact ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2]⟩
  rw [Set.inter_eq_right.mpr hsub]

/-- the hole ball integral. -/
theorem ball_int (Nx : ℕ) (b : ℕ → ℂ) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ : Δ < 1 / 2) (x : (_ : ℕ) × ℕ) :
    (∫ θ in Set.Ico (0 : ℝ) 1, ‖ZetaQ.expSum Nx b θ‖ ^ 2 * (ballZ Δ x).indicator (fun _ => (1 : ℝ)) θ)
      = ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2 := by
  set S : Set ℝ := Set.Iic Δ with hS
  have e0 : ∀ θ, (ballZ Δ x).indicator (fun _ => (1 : ℝ)) θ = S.indicator (fun _ => (1 : ℝ)) (distZ (θ - fareyPt x)) := by
    intro θ
    rw [← indicator_distZ]; rfl
  simp_rw [e0]
  rw [per_int _ (g_periodic Nx b) (fareyPt x) (S.indicator fun _ => (1 : ℝ))]
  rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by linarith)]
  have e1 : ∀ β, ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2 * S.indicator (fun _ => (1 : ℝ)) |β|
      = (Set.Icc (-Δ) Δ).indicator (fun β => ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2) β := by
    intro β
    by_cases h : |β| ∈ S
    · rw [Set.indicator_of_mem h, mul_one, Set.indicator_of_mem]
      exact abs_le.mp h
    · rw [Set.indicator_of_notMem h, mul_zero, Set.indicator_of_notMem]
      exact fun h' => h (abs_le.mpr h')
  simp_rw [e1]
  rw [setIntegral_indicator measurableSet_Icc]
  have hsub : Set.Icc (-Δ) Δ ⊆ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := fun β hβ =>
    ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  rw [Set.inter_eq_right.mpr hsub, integral_Icc_eq_integral_Ioc]

/-- `∫_{(−1/2,1/2]} f·1_I ≤ ∫_I f` for `f ≥ 0` continuous and `I = [p, q]`, as an interval integral. -/
theorem int_ind_le (f : ℝ → ℝ) (hfc : Continuous f) (hf0 : ∀ t, 0 ≤ f t) (p q : ℝ) (hpq : p ≤ q) :
    (∫ β in Set.Ioc (-(1 / 2) : ℝ) (1 / 2), (Set.Icc p q).indicator f β) ≤ ∫ β in p..q, f β := by
  rw [setIntegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hpq, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_mono_set (hfc.integrableOn_Icc) (ae_of_all _ fun t => hf0 t)
  exact (ae_of_all _ Set.inter_subset_right)

/-- the hole edges, by AF1's intervals `σ = ±1`. -/
theorem edge_int (Q Nx : ℕ) (b : ℕ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (x : (_ : ℕ) × ℕ) :
    (∫ θ in Set.Ico (0 : ℝ) 1, ‖ZetaQ.expSum Nx b θ‖ ^ 2 * (edgeZ Q δ x).indicator (fun _ => (1 : ℝ)) θ)
      ≤ (∫ β in (1 / ((x.1 : ℝ) * Q) - δ / 2)..(1 / ((x.1 : ℝ) * Q) + δ / 2),
            ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
        + ∫ β in (-(1 / ((x.1 : ℝ) * Q)) - δ / 2)..(-(1 / ((x.1 : ℝ) * Q)) + δ / 2),
            ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2 := by
  set u := 1 / ((x.1 : ℝ) * Q) with hu_def
  set c := fareyPt x with hc
  set f : ℝ → ℝ := fun θ => ‖ZetaQ.expSum Nx b θ‖ ^ 2 with hf
  have hfc : Continuous f := g_cont Nx b
  have hf0 : ∀ θ, 0 ≤ f θ := fun θ => sq_nonneg _
  have hfc' : Continuous (fun β => f (c + β)) := hfc.comp (continuous_const.add continuous_id)
  set S2 : Set ℝ := Set.Ico (u - δ / 2) u with hS2
  have e2 : ∀ θ, (edgeZ Q δ x).indicator (fun _ => (1 : ℝ)) θ = S2.indicator (fun _ => (1 : ℝ)) (distZ (θ - c)) := by
    intro θ; rw [← indicator_distZ]; rfl
  simp_rw [e2]
  rw [per_int _ (g_periodic Nx b) c (S2.indicator fun _ => (1 : ℝ)), intervalIntegral.integral_of_le (by norm_num)]
  set I1 := Set.Icc (u - δ / 2) (u + δ / 2)
  set I2 := Set.Icc (-u - δ / 2) (-u + δ / 2)
  have hpt : ∀ β, f (c + β) * S2.indicator (fun _ => (1 : ℝ)) |β|
      ≤ I1.indicator (fun β => f (c + β)) β + I2.indicator (fun β => f (c + β)) β := by
    intro β
    have hi1 : 0 ≤ I1.indicator (fun β => f (c + β)) β := Set.indicator_nonneg (fun _ _ => hf0 _) β
    have hi2 : 0 ≤ I2.indicator (fun β => f (c + β)) β := Set.indicator_nonneg (fun _ _ => hf0 _) β
    by_cases h : |β| ∈ S2
    · rw [Set.indicator_of_mem h, mul_one]
      rcases le_or_gt 0 β with hb | hb
      · rw [abs_of_nonneg hb] at h
        rw [Set.indicator_of_mem (show β ∈ I1 from ⟨h.1, by linarith [h.2]⟩)]
        linarith
      · rw [abs_of_neg hb] at h
        rw [Set.indicator_of_mem (show β ∈ I2 from ⟨by linarith [h.2], by linarith [h.1]⟩)]
        linarith
    · rw [Set.indicator_of_notMem h, mul_zero]; linarith
  have hint : ∀ I : Set ℝ, MeasurableSet I →
      IntegrableOn (fun β => I.indicator (fun β => f (c + β)) β) (Set.Ioc (-(1 / 2) : ℝ) (1 / 2)) := by
    intro I hI
    exact (hfc'.integrableOn_Icc (a := -(1/2)) (b := 1/2)).mono_set Set.Ioc_subset_Icc_self |>.indicator hI
  have hleft : IntegrableOn (fun β => f (c + β) * S2.indicator (fun _ => (1 : ℝ)) |β|)
      (Set.Ioc (-(1 / 2) : ℝ) (1 / 2)) := by
    have hm : Measurable (fun β : ℝ => S2.indicator (fun _ => (1 : ℝ)) |β|) :=
      (measurable_const.indicator measurableSet_Ico).comp measurable_abs
    refine ((hfc'.integrableOn_Icc (a := -(1/2)) (b := 1/2)).mono_set Set.Ioc_subset_Icc_self).mul_bdd
      (c := 1) hm.aestronglyMeasurable (ae_of_all _ fun β => ?_)
    by_cases h : |β| ∈ S2
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  have hI12 : IntegrableOn (fun β => I1.indicator (fun β => f (c + β)) β + I2.indicator (fun β => f (c + β)) β)
      (Set.Ioc (-(1 / 2) : ℝ) (1 / 2)) := (hint I1 measurableSet_Icc).add (hint I2 measurableSet_Icc)
  have h1 := setIntegral_mono_on hleft hI12 measurableSet_Ioc (fun β _ => hpt β)
  rw [integral_add (hint I1 measurableSet_Icc) (hint I2 measurableSet_Icc)] at h1
  have h2 := int_ind_le (fun β => f (c + β)) hfc' (fun β => hf0 _) (u - δ / 2) (u + δ / 2) (by linarith)
  have h3 := int_ind_le (fun β => f (c + β)) hfc' (fun β => hf0 _) (-u - δ / 2) (-u + δ / 2) (by linarith)
  linarith

end ASc
end ShellS
end ZetaShell
