/-
rh72/lean_work/L0_2/CosWindow.lean — node W-cos (track W): the cosine window ψ_α(s) = cos(α s) with a FREE
frequency α (decoupled from the bandwidth λ, which the tree's `ThmD.vStar lam = cos(√2 λ ·)` ties to λ ≤ 1).

Paper passages formalised (quoted):
* sec_zeta.tex l.1013 (thm:zeta-allmarks) and l.1068 (ssec: simple zeros anywhere / distinct zeros):
  "Let ψ(s) = cos(1.6 s)"; l.128 (thm:zeta-mainw): "Let ψ(s) = cos(1.48 s)".
* l.99–103 (eq:zeta-R): "R(ψ) := (∫ψ² + ∬|u−v|ψ(u)ψ(v))/(∫ψ)², H(ψ) := 2 − R(ψ)".
* l.1043: "H(cos1.6s) = 0.67198155100037074656 ± 2·10⁻²¹"; l.134: "H(ψ) = 0.67244181091530534828 ± 2.3·10⁻²¹".
* l.1362 / l.1372 (thm:sigd-Sigma / thm:sigd-D): (H + a₂/2 − ν)/(1 − a₁ + a₂/2), (1 + H + a₂ − a₁ − ν)/(2 − 2a₁ + a₂).

Contents.
1. Exact moments for every α ≠ 0: ∫cos(αs) = 2 sin(α/2)/α, ∫cos² = 1/2 + sin α/(2α),
   ∬|u−v|cos cos = (a/2 + 2cos(α/2)/α²)a − 2b/α², the R-quotient, and the closed form
   H(α) = 3/2 − (1/(2α) + α/4)·cot(α/2) − (α²/2 − 1)/(4 sin²(α/2))   (α = √2: the AF constant 3/2 − cot(1/√2)/√2).
2. Rigorous enclosures of sin, cos at 4/5 and 37/50 (alternating Taylor series, 10/11 terms), hence
   H(8/5) ∈ [0.6719815510003707, 0.6719815510003708], H(37/25) ∈ [0.6724418109153053, 0.6724418109153054],
   and the all-marks constants of thm:sigd-Sigma / thm:sigd-D for the K = 5 and K = 7 certificates.
3. Admissibility: for 0 < α ≤ 8/5, f(u) = √cos(αu/L) is a `XiPrime.ModFactor` with (A, B) = (1, 3), so
   the window `P.phiV (cosW α) T = phiM f ϱ L w` is a `Zeta23.AdmWindow` with c = cMod ϱ 1 3 for all 8w ≤ L.
No `sorry`.
-/
import Zeta23.XiPrime.QuarticWindow.ModWindow
import Zeta23.XiPrime.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace ZetaS
namespace CosWindow

open Zeta23 Zeta23.XiPrime

/-- the profile ψ_α(s) = cos(α s). -/
def cosW (α s : ℝ) : ℝ := Real.cos (α * s)

theorem cosW_even (α s : ℝ) : cosW α (-s) = cosW α s := by
  unfold cosW; rw [mul_neg, Real.cos_neg]

/-! ## 1. Exact moments -/

/-- `a(α) = ∫ψ_α`. -/
def aC (α : ℝ) : ℝ := 2 * Real.sin (α / 2) / α
/-- `b(α) = ∫ψ_α²`. -/
def bC (α : ℝ) : ℝ := 1 / 2 + Real.sin α / (2 * α)
/-- `J(α) = ∬|u−v|ψ_α(u)ψ_α(v)`. -/
def jC (α : ℝ) : ℝ := (aC α / 2 + 2 * Real.cos (α / 2) / α ^ 2) * aC α - 2 * bC α / α ^ 2
/-- `H(α) = 2 − (b + J)/a²` (eq:zeta-R). -/
def HC (α : ℝ) : ℝ := 2 - (bC α + jC α) / aC α ^ 2

theorem integral_cosW {α : ℝ} (hα : α ≠ 0) :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), cosW α s = aC α := by
  unfold cosW aC
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hα, integral_cos, smul_eq_mul,
    show α * -(1 / 2) = -(α / 2) by ring, show α * (1 / 2) = α / 2 by ring, Real.sin_neg]
  field_simp
  ring

theorem integral_cosW_sq {α : ℝ} (hα : α ≠ 0) :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), cosW α s ^ 2 = bC α := by
  unfold cosW bC
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hα, integral_cos_sq, smul_eq_mul,
    show α * -(1 / 2) = -(α / 2) by ring, show α * (1 / 2) = α / 2 by ring, Real.sin_neg, Real.cos_neg,
    show Real.sin α = Real.sin (2 * (α / 2)) by ring_nf, Real.sin_two_mul]
  field_simp
  ring

theorem hasDerivAt_left' (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => (s - x) * Real.sin (ω * x) / ω - Real.cos (ω * x) / ω ^ 2)
      ((s - x) * Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => s - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub s
  have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x := (hasDerivAt_id x).const_mul ω
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_sin (ω * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const ω).sub (h3.div_const (ω ^ 2))
  exact h4.congr_deriv (by field_simp; ring)

theorem hasDerivAt_right' (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => (x - s) * Real.sin (ω * x) / ω + Real.cos (ω * x) / ω ^ 2)
      ((x - s) * Real.cos (ω * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - s) 1 x := by
    simpa using (hasDerivAt_id x).sub_const s
  have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x := (hasDerivAt_id x).const_mul ω
  have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_sin (ω * x)).comp x hlin
  have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * x) * (ω * 1)) x :=
    (Real.hasDerivAt_cos (ω * x)).comp x hlin
  have h4 := ((h1.mul h2).div_const ω).add (h3.div_const (ω ^ 2))
  exact h4.congr_deriv (by field_simp; ring)

/-- the kernel integral `∫|s − s'| cos(α s') ds' = a/2 + 2cos(α/2)/α² − 2cos(αs)/α²` for `|s| ≤ 1/2`. -/
theorem kernel_cos {α : ℝ} (hα : α ≠ 0) {s : ℝ} (hs1 : -(1 / 2 : ℝ) ≤ s) (hs2 : s ≤ 1 / 2) :
    ∫ s' in (-(1 / 2 : ℝ))..(1 / 2), |s - s'| * Real.cos (α * s')
      = aC α / 2 + 2 * Real.cos (α / 2) / α ^ 2 - 2 * Real.cos (α * s) / α ^ 2 := by
  have hcont : ∀ a b : ℝ, IntervalIntegrable
      (fun s' => |s - s'| * Real.cos (α * s')) MeasureTheory.volume a b := fun a b =>
    (Continuous.intervalIntegrable (by fun_prop) a b)
  have hsplit : ∫ s' in (-(1 / 2 : ℝ))..(1 / 2), |s - s'| * Real.cos (α * s')
      = (∫ s' in (-(1 / 2 : ℝ))..s, |s - s'| * Real.cos (α * s'))
        + ∫ s' in s..(1 / 2), |s - s'| * Real.cos (α * s') :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont _ _) (hcont _ _)).symm
  have hleft : ∫ s' in (-(1 / 2 : ℝ))..s, |s - s'| * Real.cos (α * s')
      = ∫ s' in (-(1 / 2 : ℝ))..s, (s - s') * Real.cos (α * s') := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs1] at hx
    show |s - x| * Real.cos (α * x) = (s - x) * Real.cos (α * x)
    rw [abs_of_nonneg (by linarith [hx.2] : (0:ℝ) ≤ s - x)]
  have hleft2 : ∫ s' in (-(1 / 2 : ℝ))..s, (s - s') * Real.cos (α * s')
      = ((s - s) * Real.sin (α * s) / α - Real.cos (α * s) / α ^ 2)
        - ((s - (-(1 / 2 : ℝ))) * Real.sin (α * (-(1 / 2 : ℝ))) / α
            - Real.cos (α * (-(1 / 2 : ℝ))) / α ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_left' α s hα x) (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hright : ∫ s' in s..(1 / 2), |s - s'| * Real.cos (α * s')
      = ∫ s' in s..(1 / 2), (s' - s) * Real.cos (α * s') := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hs2] at hx
    show |s - x| * Real.cos (α * x) = (x - s) * Real.cos (α * x)
    rw [abs_of_nonpos (by linarith [hx.1] : s - x ≤ 0), neg_sub]
  have hright2 : ∫ s' in s..(1 / 2), (s' - s) * Real.cos (α * s')
      = (((1:ℝ) / 2 - s) * Real.sin (α * (1 / 2)) / α + Real.cos (α * (1 / 2)) / α ^ 2)
        - ((s - s) * Real.sin (α * s) / α + Real.cos (α * s) / α ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_right' α s hα x) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [hsplit, hleft, hleft2, hright, hright2,
    show α * (-(1 / 2 : ℝ)) = -(α / 2) by ring, show α * (1 / 2 : ℝ) = α / 2 by ring,
    Real.sin_neg, Real.cos_neg]
  unfold aC
  field_simp
  ring

/-- `J(α) = ∬|u−v|ψ_α(u)ψ_α(v) du dv`. -/
theorem jInt_cosW {α : ℝ} (hα : α ≠ 0) :
    ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * cosW α u * cosW α v
      = jC α := by
  set K0 := aC α / 2 + 2 * Real.cos (α / 2) / α ^ 2 with hK0
  have hstep : ∀ u ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2),
      (∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * cosW α u * cosW α v)
        = K0 * cosW α u - 2 / α ^ 2 * cosW α u ^ 2 := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have e1 : ∀ v : ℝ, |u - v| * cosW α u * cosW α v = cosW α u * (|u - v| * Real.cos (α * v)) := by
      intro v; unfold cosW; ring
    rw [intervalIntegral.integral_congr (fun v _ => e1 v), intervalIntegral.integral_const_mul,
      kernel_cos hα hu.1 hu.2, hK0]
    unfold cosW
    ring
  rw [intervalIntegral.integral_congr hstep]
  have hc : Continuous (cosW α) := by unfold cosW; fun_prop
  have i1 : IntervalIntegrable (fun u => K0 * cosW α u) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    (hc.const_mul K0).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun u => 2 / α ^ 2 * cosW α u ^ 2) volume (-(1 / 2 : ℝ)) (1 / 2) := by
    apply Continuous.intervalIntegrable; unfold cosW; fun_prop
  rw [intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cosW hα, integral_cosW_sq hα, hK0]
  unfold jC
  ring

/-- **the R-quotient of eq:zeta-R for ψ_α** (the body of the architect's `ZetaS.Rpsi (cosW α)`). -/
theorem Rquot_cosW {α : ℝ} (hα : α ≠ 0) :
    ((∫ u in (-(1 / 2 : ℝ))..(1 / 2), cosW α u ^ 2)
      + ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * cosW α u * cosW α v)
      / (∫ u in (-(1 / 2 : ℝ))..(1 / 2), cosW α u) ^ 2 = (bC α + jC α) / aC α ^ 2 := by
  rw [integral_cosW_sq hα, jInt_cosW hα, integral_cosW hα]

/-- **closed form** `H(α) = 3/2 − (1/(2α) + α/4)·cot(α/2) − (α²/2 − 1)/(4 sin²(α/2))`. -/
theorem HC_eq {α : ℝ} (hα : α ≠ 0) (hs : Real.sin (α / 2) ≠ 0) :
    HC α = 3 / 2 - (1 / (2 * α) + α / 4) * (Real.cos (α / 2) / Real.sin (α / 2))
      - (α ^ 2 / 2 - 1) / (4 * Real.sin (α / 2) ^ 2) := by
  unfold HC jC aC bC
  rw [show Real.sin α = Real.sin (2 * (α / 2)) by ring_nf, Real.sin_two_mul]
  field_simp
  ring

/-! ## 2. Enclosures (alternating Taylor series) -/

theorem cos_taylor_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)) ≤ Real.cos x ∧
    Real.cos x ≤ ∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)) := by
  have hs := (Real.hasSum_cos x).tendsto_sum_nat
  have hs' : Tendsto (fun n => ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ))) atTop (𝓝 (Real.cos x)) := by
    simpa only [mul_div_assoc] using hs
  have hanti : Antitone (fun i : ℕ => x ^ (2 * i) / ((2 * i).factorial : ℝ)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    show x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ) ≤ x ^ (2 * n) / ((2 * n).factorial : ℝ)
    have hfac : ((2 * (n + 1)).factorial : ℝ) = (2 * n + 2) * (2 * n + 1) * ((2 * n).factorial : ℝ) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hpow : x ^ (2 * (n + 1)) = x ^ (2 * n) * x ^ 2 := by
      rw [← pow_add]; ring_nf
    have hF : (0:ℝ) < (2 * n).factorial := by exact_mod_cast Nat.factorial_pos _
    have hxn : 0 ≤ x ^ (2 * n) := by positivity
    rw [hfac, hpow, div_le_div_iff₀ (by positivity) hF]
    have hn : (0:ℝ) ≤ n := n.cast_nonneg
    have hx2 : x ^ 2 ≤ (2 * n + 2) * (2 * n + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hx2 (mul_nonneg hxn hF.le)]
  exact ⟨hanti.alternating_series_le_tendsto hs' k, hanti.tendsto_le_alternating_series hs' k⟩

theorem sin_taylor_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))
      ≤ Real.sin x ∧
    Real.sin x ≤ ∑ i ∈ Finset.range (2 * k + 1),
      (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) := by
  have hs := (Real.hasSum_sin x).tendsto_sum_nat
  have hs' : Tendsto (fun n => ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))) atTop (𝓝 (Real.sin x)) := by
    simpa only [mul_div_assoc] using hs
  have hanti : Antitone (fun i : ℕ => x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    show x ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1).factorial : ℝ)
      ≤ x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
    have hfac : ((2 * (n + 1) + 1).factorial : ℝ)
        = (2 * n + 3) * (2 * n + 2) * ((2 * n + 1).factorial : ℝ) := by
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hpow : x ^ (2 * (n + 1) + 1) = x ^ (2 * n + 1) * x ^ 2 := by
      rw [← pow_add]; ring_nf
    have hF : (0:ℝ) < (2 * n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hxn : 0 ≤ x ^ (2 * n + 1) := by positivity
    rw [hfac, hpow, div_le_div_iff₀ (by positivity) hF]
    have hn : (0:ℝ) ≤ n := n.cast_nonneg
    have hx2 : x ^ 2 ≤ (2 * n + 3) * (2 * n + 2) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hx2 (mul_nonneg hxn hF.le)]
  exact ⟨hanti.alternating_series_le_tendsto hs' k, hanti.tendsto_le_alternating_series hs' k⟩

theorem cos_four_fifths :
    (0.696706709347165420 : ℝ) ≤ Real.cos (4 / 5) ∧ Real.cos (4 / 5) ≤ 0.696706709347165421 := by
  obtain ⟨h1, h2⟩ := cos_taylor_bounds (x := 4 / 5) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

theorem sin_four_fifths :
    (0.717356090899522761 : ℝ) ≤ Real.sin (4 / 5) ∧ Real.sin (4 / 5) ≤ 0.717356090899522762 := by
  obtain ⟨h1, h2⟩ := sin_taylor_bounds (x := 4 / 5) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

theorem cos_37_50 :
    (0.738468558729587909 : ℝ) ≤ Real.cos (37 / 50) ∧ Real.cos (37 / 50) ≤ 0.738468558729587910 := by
  obtain ⟨h1, h2⟩ := cos_taylor_bounds (x := 37 / 50) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

theorem sin_37_50 :
    (0.674287911628145067 : ℝ) ≤ Real.sin (37 / 50) ∧ Real.sin (37 / 50) ≤ 0.674287911628145068 := by
  obtain ⟨h1, h2⟩ := sin_taylor_bounds (x := 37 / 50) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  constructor <;> linarith

theorem HC_eight_fifths_eq :
    HC (8 / 5) = 3 / 2 - 57 / 80 * (Real.cos (4 / 5) / Real.sin (4 / 5)) - 7 / 100 / Real.sin (4 / 5) ^ 2 := by
  have hs : 0 < Real.sin (4 / 5) := by linarith [sin_four_fifths.1]
  rw [HC_eq (by norm_num) (by rw [show (8 / 5 : ℝ) / 2 = 4 / 5 by norm_num]; exact hs.ne'),
    show (8 / 5 : ℝ) / 2 = 4 / 5 by norm_num]
  ring

/-- **`H(cos 1.6 s) ∈ [0.6719815510003707, 0.6719815510003708]`** (draft l.1043: 0.67198155100037074656). -/
theorem HC_eight_fifths :
    (0.6719815510003707 : ℝ) ≤ HC (8 / 5) ∧ HC (8 / 5) ≤ 0.6719815510003708 := by
  obtain ⟨c1, c2⟩ := cos_four_fifths
  obtain ⟨s1, s2⟩ := sin_four_fifths
  rw [HC_eight_fifths_eq]
  have hs : 0 < Real.sin (4 / 5) := by linarith
  have hc : 0 < Real.cos (4 / 5) := by linarith
  constructor
  · have hq : Real.cos (4 / 5) / Real.sin (4 / 5) ≤ 0.696706709347165421 / 0.717356090899522761 := by
      gcongr
    have hr : 7 / 100 / Real.sin (4 / 5) ^ 2 ≤ 7 / 100 / 0.717356090899522761 ^ 2 := by gcongr
    have hn : (0.6719815510003707 : ℝ) ≤ 3 / 2 - 57 / 80 * (0.696706709347165421 / 0.717356090899522761)
        - 7 / 100 / 0.717356090899522761 ^ 2 := by norm_num
    linarith
  · have hq : 0.696706709347165420 / 0.717356090899522762 ≤ Real.cos (4 / 5) / Real.sin (4 / 5) := by
      gcongr
    have hr : 7 / 100 / 0.717356090899522762 ^ 2 ≤ 7 / 100 / Real.sin (4 / 5) ^ 2 := by gcongr
    have hn : 3 / 2 - 57 / 80 * (0.696706709347165420 / 0.717356090899522762)
        - 7 / 100 / 0.717356090899522762 ^ 2 ≤ (0.6719815510003708 : ℝ) := by norm_num
    linarith

theorem HC_37_25_eq :
    HC (37 / 25) = 3 / 2 - 2619 / 3700 * (Real.cos (37 / 50) / Real.sin (37 / 50))
      - 119 / 5000 / Real.sin (37 / 50) ^ 2 := by
  have hs : 0 < Real.sin (37 / 50) := by linarith [sin_37_50.1]
  rw [HC_eq (by norm_num) (by rw [show (37 / 25 : ℝ) / 2 = 37 / 50 by norm_num]; exact hs.ne'),
    show (37 / 25 : ℝ) / 2 = 37 / 50 by norm_num]
  ring

/-- **`H(cos 1.48 s) ∈ [0.6724418109153053, 0.6724418109153054]`** (draft l.134: 0.67244181091530534828). -/
theorem HC_37_25 :
    (0.6724418109153053 : ℝ) ≤ HC (37 / 25) ∧ HC (37 / 25) ≤ 0.6724418109153054 := by
  obtain ⟨c1, c2⟩ := cos_37_50
  obtain ⟨s1, s2⟩ := sin_37_50
  rw [HC_37_25_eq]
  have hs : 0 < Real.sin (37 / 50) := by linarith
  have hc : 0 < Real.cos (37 / 50) := by linarith
  constructor
  · have hq : Real.cos (37 / 50) / Real.sin (37 / 50) ≤ 0.738468558729587910 / 0.674287911628145067 := by
      gcongr
    have hr : 119 / 5000 / Real.sin (37 / 50) ^ 2 ≤ 119 / 5000 / 0.674287911628145067 ^ 2 := by gcongr
    have hn : (0.6724418109153053 : ℝ) ≤ 3 / 2 - 2619 / 3700 * (0.738468558729587910 / 0.674287911628145067)
        - 119 / 5000 / 0.674287911628145067 ^ 2 := by norm_num
    linarith
  · have hq : 0.738468558729587909 / 0.674287911628145068 ≤ Real.cos (37 / 50) / Real.sin (37 / 50) := by
      gcongr
    have hr : 119 / 5000 / 0.674287911628145068 ^ 2 ≤ 119 / 5000 / Real.sin (37 / 50) ^ 2 := by gcongr
    have hn : 3 / 2 - 2619 / 3700 * (0.738468558729587909 / 0.674287911628145068)
        - 119 / 5000 / 0.674287911628145068 ^ 2 ≤ (0.6724418109153054 : ℝ) := by norm_num
    linarith

/-! ### the all-marks constants (definitions as the architect's `ZetaS.sigmaConst`, `ZetaS.distConst`) -/

/-- thm:sigd-Sigma (l.1362): `(H + a₂/2 − ν)/(1 − a₁ + a₂/2)`. -/
def sigmaConst (H a₁ a₂ ν : ℝ) : ℝ := (H + a₂ / 2 - ν) / (1 - a₁ + a₂ / 2)
/-- thm:sigd-D (l.1372): `(1 + H + a₂ − a₁ − ν)/(2 − 2a₁ + a₂)`. -/
def distConst (H a₁ a₂ ν : ℝ) : ℝ := (1 + H + a₂ - a₁ - ν) / (2 - 2 * a₁ + a₂)

/-- K = 7 certificate (a₁, a₂, ν) = (1824837/10⁸, 1168069/(5·10⁷), 3/250): simple zeros `> 0.676102666`. -/
theorem sigma_K7 : (0.676102666 : ℝ) < sigmaConst (HC (8 / 5)) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) := by
  have h := HC_eight_fifths.1
  unfold sigmaConst
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-- K = 7: distinct zeros `> 0.838051333`. -/
theorem dist_K7 : (0.838051333 : ℝ) < distConst (HC (8 / 5)) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) := by
  have h := HC_eight_fifths.1
  unfold distConst
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-- K = 5 certificate (thm:zeta-allmarks data (1280197/10⁸, 48749/3125000, 1/125)): `> 0.675158622`. -/
theorem sigma_K5 : (0.675158622 : ℝ) < sigmaConst (HC (8 / 5)) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) := by
  have h := HC_eight_fifths.1
  unfold sigmaConst
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-- K = 5: distinct zeros `> 0.837579311`. -/
theorem dist_K5 : (0.837579311 : ℝ) < distConst (HC (8 / 5)) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) := by
  have h := HC_eight_fifths.1
  unfold distConst
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-! ## 3. Admissibility for 0 < α ≤ 8/5 (the `ModFactor` route of XiPrime/QuarticWindow) -/

/-- `h(u) = cos(α u/L)`. -/
def hC (α L u : ℝ) : ℝ := cosW α (u / L)

/-- the modulating factor `f(u) = √(max 0 (cos(αu/L)))`; `P.phiV (cosW α) T = phiM (fC α (P.L T)) …` (rfl). -/
def fC (α L u : ℝ) : ℝ := Real.sqrt (max 0 (cosW α (u / L)))

variable {α L : ℝ}

lemma fC_even (u : ℝ) : fC α L (-u) = fC α L u := by
  simp only [fC, neg_div, cosW_even]

lemma fC_nonneg (u : ℝ) : 0 ≤ fC α L u := Real.sqrt_nonneg _

lemma fC_le_one (u : ℝ) : fC α L u ≤ 1 := by
  unfold fC
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (max_le zero_le_one (Real.cos_le_one _))

lemma arg_bound (hα0 : 0 < α) (hL : 0 < L) (u : ℝ) : |α * (u / L)| = α * (|u| / L) := by
  rw [abs_mul, abs_div, abs_of_pos hα0, abs_of_pos hL]

lemma hC_pos_of_mem (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) {u : ℝ}
    (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) : 0 < hC α L u := by
  unfold hC cosW
  have hu' : |u| < L / 2 + L / 10 := abs_lt.mpr ⟨by linarith [hu.1], hu.2⟩
  have hq : |u| / L < 3 / 5 := by rw [div_lt_iff₀ hL]; linarith
  have hb : |α * (u / L)| < π / 2 := by
    rw [arg_bound hα0 hL]
    have : α * (|u| / L) ≤ 8 / 5 * (|u| / L) := by gcongr
    have hpi := Real.pi_gt_three
    nlinarith [div_nonneg (abs_nonneg u) hL.le]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [neg_abs_le (α * (u / L)), le_abs_self (α * (u / L))]

lemma hC_core_ge (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) :
    17 / 25 ≤ hC α L u := by
  unfold hC cosW
  have hq : |u| / L ≤ 1 / 2 := by rw [div_le_iff₀ hL]; linarith
  have hb : |α * (u / L)| ≤ 4 / 5 := by
    rw [arg_bound hα0 hL]
    calc α * (|u| / L) ≤ 8 / 5 * (1 / 2) := by
          apply mul_le_mul hα1 hq (div_nonneg (abs_nonneg u) hL.le) (by norm_num)
      _ = 4 / 5 := by norm_num
  have h := Real.one_sub_sq_div_two_le_cos (x := α * (u / L))
  have hsq : (α * (u / L)) ^ 2 ≤ (4 / 5) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  nlinarith

lemma fC_core_ge (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) :
    4 / 5 ≤ fC α L u := by
  have h := hC_core_ge hα0 hα1 hL hu
  unfold fC
  rw [max_eq_right (by unfold hC at h; linarith)]
  refine Real.le_sqrt_of_sq_le ?_
  unfold hC at h; nlinarith

lemma fC_eq_sqrt_of_mem (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) {u : ℝ}
    (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) : fC α L u = Real.sqrt (hC α L u) := by
  show Real.sqrt (max 0 (hC α L u)) = _
  rw [max_eq_right (hC_pos_of_mem hα0 hα1 hL hu).le]

lemma hC_contDiff : ContDiff ℝ ⊤ (hC α L) := by
  have : hC α L = fun u => Real.cos (α * (u / L)) := rfl
  rw [this]; fun_prop

lemma fC_contDiffOn (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) :
    ContDiffOn ℝ 2 (fC α L) (Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) := by
  have h1 : ContDiffOn ℝ 2 (fun u => Real.sqrt (hC α L u)) (Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :=
    ((hC_contDiff (α := α) (L := L)).of_le le_top).contDiffOn.sqrt
      fun u hu => (hC_pos_of_mem hα0 hα1 hL hu).ne'
  exact h1.congr fun u hu => fC_eq_sqrt_of_mem hα0 hα1 hL hu

lemma fC_mul_self_of_mem (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) {u : ℝ}
    (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) : fC α L u * fC α L u = hC α L u := by
  rw [fC_eq_sqrt_of_mem hα0 hα1 hL hu, ← sq, Real.sq_sqrt (hC_pos_of_mem hα0 hα1 hL hu).le]

lemma hasDerivAt_hC (u : ℝ) : HasDerivAt (hC α L) (-Real.sin (α * (u / L)) * (α * (1 / L))) u := by
  have h := (Real.hasDerivAt_cos (α * (u / L))).comp u (((hasDerivAt_id u).div_const L).const_mul α)
  exact h

lemma deriv_hC : deriv (hC α L) = fun u => -Real.sin (α * (u / L)) * (α * (1 / L)) :=
  funext fun u => (hasDerivAt_hC u).deriv

lemma deriv2_hC (u : ℝ) :
    deriv (deriv (hC α L)) u = -(Real.cos (α * (u / L)) * (α * (1 / L))) * (α * (1 / L)) := by
  rw [deriv_hC]
  have h := (((Real.hasDerivAt_sin (α * (u / L))).comp u
    (((hasDerivAt_id u).div_const L).const_mul α)).neg).mul_const (α * (1 / L))
  exact h.deriv

lemma abs_deriv_hC_le (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) (u : ℝ) :
    |deriv (hC α L) u| ≤ 8 / 5 / L := by
  rw [deriv_hC]
  simp only
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < α * (1 / L))]
  have := Real.abs_sin_le_one (α * (u / L))
  calc |Real.sin (α * (u / L))| * (α * (1 / L)) ≤ 1 * (8 / 5 * (1 / L)) := by
        gcongr
    _ = 8 / 5 / L := by ring

lemma abs_deriv2_hC_le (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) (u : ℝ) :
    |deriv (deriv (hC α L)) u| ≤ 64 / 25 / L ^ 2 := by
  rw [deriv2_hC, abs_mul, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < α * (1 / L))]
  have := Real.abs_cos_le_one (α * (u / L))
  calc |Real.cos (α * (u / L))| * (α * (1 / L)) * (α * (1 / L))
      ≤ 1 * (8 / 5 * (1 / L)) * (8 / 5 * (1 / L)) := by gcongr
    _ = 64 / 25 / L ^ 2 := by ring

lemma abs_deriv_fC_le (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) :
    |deriv (fC α L) u| ≤ 1 / L := by
  set U : Set ℝ := Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have huU : u ∈ U := by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have hsm := fC_contDiffOn hα0 hα1 hL
  have hev : (fun v => fC α L v * fC α L v) =ᶠ[nhds u] hC α L := by
    filter_upwards [hU.mem_nhds huU] with v hv using fC_mul_self_of_mem hα0 hα1 hL hv
  have hd : deriv (hC α L) u = deriv (fC α L) u * fC α L u + fC α L u * deriv (fC α L) u := by
    rw [← hev.deriv_eq]; exact deriv_mul_eq hU hsm hsm huU
  have hf := fC_core_ge hα0 hα1 hL hu
  have hh := abs_deriv_hC_le hα0 hα1 hL u
  have e : deriv (fC α L) u = deriv (hC α L) u / (2 * fC α L u) := by
    rw [hd]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fC α L u)]
  rw [div_le_div_iff₀ (by linarith) hL]
  calc |deriv (hC α L) u| * L ≤ 8 / 5 / L * L := by gcongr
    _ = 8 / 5 := by field_simp
    _ ≤ 1 * (2 * (4 / 5)) := by norm_num
    _ ≤ 1 * (2 * fC α L u) := by gcongr

lemma abs_deriv2_fC_le (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) :
    |deriv (deriv (fC α L)) u| ≤ 3 / L ^ 2 := by
  set U : Set ℝ := Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have hmemU : ∀ v, |v| < L / 2 + L / 10 → v ∈ U := fun v hv => by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le v, le_abs_self v]
  have huU : u ∈ U := hmemU u (by linarith)
  have hsm := fC_contDiffOn hα0 hα1 hL
  have hd1 : ∀ v ∈ U, deriv (fun x => fC α L x * fC α L x) v = deriv (hC α L) v := by
    intro v hv
    have hev : (fun x => fC α L x * fC α L x) =ᶠ[nhds v] hC α L := by
      filter_upwards [hU.mem_nhds hv] with x hx using fC_mul_self_of_mem hα0 hα1 hL hx
    exact hev.deriv_eq
  have hev2 : deriv (fun x => fC α L x * fC α L x) =ᶠ[nhds u] deriv (hC α L) := by
    filter_upwards [hU.mem_nhds huU] with v hv using hd1 v hv
  have hd2 : deriv (deriv (hC α L)) u
      = deriv (deriv (fC α L)) u * fC α L u + 2 * (deriv (fC α L) u * deriv (fC α L) u)
        + fC α L u * deriv (deriv (fC α L)) u := by
    rw [← hev2.deriv_eq]; exact deriv2_mul_eq hU hsm hsm huU
  have hf := fC_core_ge hα0 hα1 hL hu
  have h1 := abs_deriv_fC_le hα0 hα1 hL hu
  have h2 := abs_deriv2_hC_le hα0 hα1 hL u
  have e : deriv (deriv (fC α L)) u
      = (deriv (deriv (hC α L)) u - 2 * (deriv (fC α L) u * deriv (fC α L) u)) / (2 * fC α L u) := by
    rw [hd2]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fC α L u), div_le_div_iff₀ (by linarith) (by positivity)]
  have hsq : |deriv (fC α L) u| ^ 2 ≤ (1 / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc |deriv (deriv (hC α L)) u - 2 * (deriv (fC α L) u * deriv (fC α L) u)| * L ^ 2
      ≤ (|deriv (deriv (hC α L)) u| + 2 * |deriv (fC α L) u| ^ 2) * L ^ 2 := by
        gcongr
        calc |deriv (deriv (hC α L)) u - 2 * (deriv (fC α L) u * deriv (fC α L) u)|
            ≤ |deriv (deriv (hC α L)) u| + |2 * (deriv (fC α L) u * deriv (fC α L) u)| := abs_sub _ _
          _ = |deriv (deriv (hC α L)) u| + 2 * |deriv (fC α L) u| ^ 2 := by
              rw [abs_mul, abs_two, abs_mul, sq]
    _ ≤ (64 / 25 / L ^ 2 + 2 * (1 / L) ^ 2) * L ^ 2 := by gcongr
    _ = 64 / 25 + 2 := by field_simp
    _ ≤ 3 * (2 * (4 / 5)) := by norm_num
    _ ≤ 3 * (2 * fC α L u) := by gcongr

/-- **`√cos(α·/L)` is a modulating factor** with `(A, B) = (1, 3)`, for `0 < α ≤ 8/5`. -/
theorem modFactor_fC (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hL : 0 < L) : ModFactor (fC α L) L 1 3 where
  A_nonneg := by norm_num
  B_nonneg := by norm_num
  even := fC_even
  nonneg := fC_nonneg
  le_one := fun u _ => fC_le_one u
  antitone := by
    intro x hx y hy hxy
    unfold fC cosW
    apply Real.sqrt_le_sqrt
    apply max_le_max le_rfl
    have hy2 : y / L ≤ 1 / 2 := by rw [div_le_iff₀ hL]; linarith [hy.2]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg hα0.le (div_nonneg hx.1 hL.le)
    · have := Real.pi_gt_three
      nlinarith [div_nonneg hy.1 hL.le]
    · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hxy hL.le) hα0.le
  smooth := ⟨L / 10, by positivity, fC_contDiffOn hα0 hα1 hL⟩
  deriv_le := fun u hu => abs_deriv_fC_le hα0 hα1 hL hu
  deriv2_le := fun u hu => abs_deriv2_fC_le hα0 hα1 hL hu

/-- the window constant of the cosine windows. -/
def cCos (ϱ : ℝ → ℝ) : ℝ := cMod ϱ 1 3

/-- `P.phiV (cosW α) T` is the modulated taper with factor `fC α (P.L T)` (rfl). -/
theorem phiV_cos_eq (P : Params) (T : ℝ) : P.phiV (cosW α) T = phiM (fC α (P.L T)) P.ϱ (P.L T) P.w := rfl

/-- **The cosine window is admissible** (0 < α ≤ 8/5; in particular α = 8/5 and α = 37/25), all 8w ≤ L. -/
theorem admWindow_cos {ϱ : ℝ → ℝ} {w : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5) (hϱ : TaperProfile ϱ)
    (hw : 1 ≤ w) (hwL : 8 * w ≤ L) : AdmWindow (phiM (fC α L) ϱ L w) L w (cCos ϱ) := by
  have hL : 0 < L := by linarith
  exact admWindow_phiM (modFactor_fC hα0 hα1 hL) hϱ hw hwL

/-- the Params form. -/
theorem admWindow_phiV_cos {P : Params} (hP : P.Valid) {T : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 8 / 5)
    (hwL : 8 * P.w ≤ P.L T) : AdmWindow (P.phiV (cosW α) T) (P.L T) P.w (cCos P.ϱ) := by
  rw [phiV_cos_eq]
  exact admWindow_cos hα0 hα1 hP.taper hP.one_le_w hwL

end CosWindow
end ZetaS

end

#print axioms ZetaS.CosWindow.integral_cosW
#print axioms ZetaS.CosWindow.integral_cosW_sq
#print axioms ZetaS.CosWindow.jInt_cosW
#print axioms ZetaS.CosWindow.Rquot_cosW
#print axioms ZetaS.CosWindow.HC_eq
#print axioms ZetaS.CosWindow.HC_eight_fifths
#print axioms ZetaS.CosWindow.HC_37_25
#print axioms ZetaS.CosWindow.sigma_K7
#print axioms ZetaS.CosWindow.dist_K7
#print axioms ZetaS.CosWindow.sigma_K5
#print axioms ZetaS.CosWindow.dist_K5
#print axioms ZetaS.CosWindow.admWindow_cos
#print axioms ZetaS.CosWindow.admWindow_phiV_cos
