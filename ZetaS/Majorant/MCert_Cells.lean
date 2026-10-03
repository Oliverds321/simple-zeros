/-
M-cert, cell form of the numerical node `NPos` (L2_2, 28 Sep 2026).

A cell certificate for `NPos` (P ≥ 0 on [0, 30]) needs, per cell [m − r, m + r] with rational m, r, only the two point
values P(m) and P′(m) — each a sum of 59 cos/sin of rational multiples of π, exactly what L1_1's `sinCosPiQ`
enclosures give — and the global second-derivative bound |P″| ≤ M₂ ≤ 231 proved here:

  `Pmaj_cell`     : for s ∈ [m − r, m + r],  P(s) ≥ P(m) − |P′(m)|·r − (231/2)·r²;
  `NPos_of_cells` : if finitely many such cells cover [0, 30] and each has P(m) − |P′(m)| r − (231/2) r² ≥ 0, then NPos.
  `NMaj_of_NMaj2` : NPos ∧ NMaj2 ⇒ NMaj, where NMaj2 replaces sinc(x) by σ(x) = 1 − x²/6 − x⁴/100 (Real.sin_bound),
                    so the second numerical node needs only cos/sin enclosures (18 second-order / 1338 first-order cells).

Python estimate (py/mcert_cells.py, adaptive bisection, this second-order form with the exact M₂ = 229.9): 3205 cells;
first-order (Lipschitz) form: 491 583 cells.
-/
import ZetaS.Interfaces
import ZetaS.Majorant.MCert_Majorant

open Real Set Finset

noncomputable section

namespace ZetaS

namespace MCert

/-- `P′(s) = −2 Σ β_j (πj/30) sin(π j s/30)`. -/
def dPmaj (s : ℝ) : ℝ := -2 * ∑ j ∈ Icc 1 59, beta j * (π * (j / 30)) * Real.sin (π * (j * s / 30))

/-- `P″(s) = −2 Σ β_j (πj/30)² cos(π j s/30)`. -/
def d2Pmaj (s : ℝ) : ℝ := -2 * ∑ j ∈ Icc 1 59, beta j * (π * (j / 30)) ^ 2 * Real.cos (π * (j * s / 30))

lemma hasDerivAt_arg (j : ℕ) (s : ℝ) : HasDerivAt (fun s : ℝ => π * (j * s / 30)) (π * (j / 30)) s := by
  have := (((hasDerivAt_id' s).const_mul (j : ℝ)).div_const 30).const_mul π
  exact this.congr_deriv (by ring)

lemma hasDerivAt_Pmaj (s : ℝ) : HasDerivAt Pmaj (dPmaj s) s := by
  have hsum : HasDerivAt (fun s => ∑ j ∈ Icc 1 59, beta j * Real.cos (π * (j * s / 30)))
      (∑ j ∈ Icc 1 59, beta j * (-Real.sin (π * (j * s / 30)) * (π * (j / 30)))) s :=
    HasDerivAt.fun_sum fun j _ => ((hasDerivAt_arg j s).cos).const_mul (beta j)
  have h := (hsum.const_mul 2).const_add (beta 0)
  unfold Pmaj dPmaj
  refine h.congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma hasDerivAt_dPmaj (s : ℝ) : HasDerivAt dPmaj (d2Pmaj s) s := by
  have hsum : HasDerivAt (fun s => ∑ j ∈ Icc 1 59, beta j * (π * (j / 30)) * Real.sin (π * (j * s / 30)))
      (∑ j ∈ Icc 1 59, beta j * (π * (j / 30)) * (Real.cos (π * (j * s / 30)) * (π * (j / 30)))) s :=
    HasDerivAt.fun_sum fun j _ => ((hasDerivAt_arg j s).sin).const_mul (beta j * (π * (j / 30)))
  have h := hsum.const_mul (-2)
  unfold dPmaj d2Pmaj
  refine h.congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `M₂ = 2 Σ |β_j| (πj/30)²`. -/
def M2 : ℝ := 2 * ∑ j ∈ Icc 1 59, |beta j| * (π * (j / 30)) ^ 2

lemma abs_d2Pmaj_le (s : ℝ) : |d2Pmaj s| ≤ M2 := by
  unfold d2Pmaj M2
  rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (π * (j / 30)))]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

lemma M2_le : M2 ≤ 231 := by
  have hπ : π < 3.1416 := Real.pi_lt_d4
  have hπ0 : 0 < π := Real.pi_pos
  have h : M2 ≤ 2 * ∑ j ∈ Icc 1 59, |beta j| * ((3.1416 : ℝ) * (j / 30)) ^ 2 := by
    unfold M2
    gcongr with j hj
    all_goals first | exact hπ.le | positivity
  refine h.trans ?_
  rw [show Finset.Icc 1 59 = Finset.Ico 1 60 by rfl, Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, beta]
  norm_num [betaQ, abs_div]

/-- the second-order cell bound. -/
lemma Pmaj_cell (m r : ℝ) (s : ℝ) (hs : |s - m| ≤ r) :
    Pmaj m - |dPmaj m| * r - 231 / 2 * r ^ 2 ≤ Pmaj s := by
  have hM : ∀ t, |d2Pmaj t| ≤ 231 := fun t => (abs_d2Pmaj_le t).trans M2_le
  have hr : 0 ≤ r := le_trans (abs_nonneg _) hs
  -- h(t) = P(t) − P(m) − P′(m)(t − m) + (231/2)(t − m)² ≥ 0
  set h : ℝ → ℝ := fun t => Pmaj t - Pmaj m - dPmaj m * (t - m) + 231 / 2 * (t - m) ^ 2 with hh
  have hderiv : ∀ t, HasDerivAt h (dPmaj t - dPmaj m + 231 * (t - m)) t := by
    intro t
    have h1 := (((hasDerivAt_Pmaj t).sub_const (Pmaj m)).sub
      (((hasDerivAt_id' t).sub_const m).const_mul (dPmaj m))).add
      ((((hasDerivAt_id' t).sub_const m).pow 2).const_mul (231 / 2))
    refine h1.congr_deriv ?_
    simp; ring
  -- P′ is 231-Lipschitz
  have hlip : ∀ a b, |dPmaj b - dPmaj a| ≤ 231 * |b - a| := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope dPmaj d2Pmaj hab
        (fun x _ => (hasDerivAt_dPmaj x).continuousAt.continuousWithinAt) (fun x _ => hasDerivAt_dPmaj x)
      have hba : 0 < b - a := by linarith
      rw [eq_div_iff hba.ne'] at hc
      rw [← hc, abs_mul, abs_of_pos hba]
      exact mul_le_mul_of_nonneg_right (hM c) hba.le
    · subst hab; simp
    · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope dPmaj d2Pmaj hab
        (fun x _ => (hasDerivAt_dPmaj x).continuousAt.continuousWithinAt) (fun x _ => hasDerivAt_dPmaj x)
      have hab' : 0 < a - b := by linarith
      rw [eq_div_iff hab'.ne'] at hc
      rw [abs_sub_comm, ← hc, abs_mul, abs_of_pos hab', abs_sub_comm, abs_of_pos hab']
      exact mul_le_mul_of_nonneg_right (hM c) hab'.le
  have hm0 : h m = 0 := by simp [hh]
  have hge : 0 ≤ h s := by
    rcases lt_trichotomy m s with hms | hms | hms
    · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope h (fun t => dPmaj t - dPmaj m + 231 * (t - m)) hms
        (fun x _ => (hderiv x).continuousAt.continuousWithinAt) (fun x _ => hderiv x)
      have hpos : 0 ≤ dPmaj c - dPmaj m + 231 * (c - m) := by
        have := hlip m c
        rw [abs_of_pos (by linarith [hc.1] : (0 : ℝ) < c - m)] at this
        linarith [neg_abs_le (dPmaj c - dPmaj m)]
      have hsm : 0 < s - m := by linarith
      rw [eq_div_iff hsm.ne', hm0, sub_zero] at hcs
      rw [← hcs]; exact mul_nonneg hpos hsm.le
    · rw [← hms, hm0]
    · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope h (fun t => dPmaj t - dPmaj m + 231 * (t - m)) hms
        (fun x _ => (hderiv x).continuousAt.continuousWithinAt) (fun x _ => hderiv x)
      have hneg : dPmaj c - dPmaj m + 231 * (c - m) ≤ 0 := by
        have := hlip c m
        rw [abs_of_pos (by linarith [hc.2] : (0 : ℝ) < m - c)] at this
        linarith [neg_abs_le (dPmaj m - dPmaj c)]
      have hms' : 0 < m - s := by linarith
      rw [eq_div_iff (by linarith : m - s ≠ 0), hm0, zero_sub] at hcs
      have : h s = -((dPmaj c - dPmaj m + 231 * (c - m)) * (m - s)) := by linarith
      rw [this]; nlinarith
  simp only [hh] at hge
  have h1 : -(|dPmaj m| * r) ≤ dPmaj m * (s - m) := by
    have := abs_mul (dPmaj m) (s - m)
    have h2 : |dPmaj m * (s - m)| ≤ |dPmaj m| * r := by
      rw [this]; exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    linarith [neg_abs_le (dPmaj m * (s - m))]
  have h3 : (s - m) ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  nlinarith

/-- **NPos from a finite cell cover** (the form a cell certificate proves). -/
theorem NPos_of_cells (cells : List (ℝ × ℝ))
    (hcover : ∀ s ∈ Icc (0 : ℝ) 30, ∃ c ∈ cells, |s - c.1| ≤ c.2)
    (hok : ∀ c ∈ cells, 0 ≤ Pmaj c.1 - |dPmaj c.1| * c.2 - 231 / 2 * c.2 ^ 2) : NPos := by
  intro s hs
  obtain ⟨c, hc, hsc⟩ := hcover s hs
  exact le_trans (hok c hc) (Pmaj_cell c.1 c.2 s hsc)

/-! ### NMaj without sinc -/

/-- `σ(x) = 1 − x²/6 − x⁴/100`, a lower bound for `sinc` on `[0, 1]` (from `Real.sin_bound`). -/
def sigmaLow (x : ℝ) : ℝ := 1 - x ^ 2 / 6 - x ^ 4 / 100

lemma sigmaLow_le_sinc {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : sigmaLow x ≤ Real.sinc x := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx; simp [sigmaLow]
  · rw [Real.sinc_of_ne_zero hx.ne', le_div_iff₀ hx]
    have hb := Real.sin_bound (x := x) (by rw [abs_of_pos hx]; exact h1)
    rw [abs_of_pos hx] at hb
    have := (abs_le.1 hb).1
    unfold sigmaLow
    nlinarith [pow_pos hx 5]

lemma sigmaLow_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ sigmaLow x := by
  unfold sigmaLow
  have h2 : x ^ 2 ≤ 1 := by nlinarith
  have h4 : x ^ 4 ≤ 1 := by nlinarith
  linarith

/-- **NMaj2** — numerical node without `sinc` (cell certificate on [0, 1/2]; needs only cos/sin enclosures):
`cos(8s/5)/((5/4) sin(4/5)) ≤ (1/60) σ(πs/60)² P(s)`. The replacement costs ≤ 10⁻⁸ of the 1.95·10⁻⁵ margin. -/
def NMaj2 : Prop :=
  ∀ s ∈ Icc (0 : ℝ) (1 / 2), Real.cos (8 / 5 * s) / (5 / 4 * Real.sin (4 / 5)) ≤ 1 / 60 * sigmaLow (π * s / 60) ^ 2 * Pmaj s

theorem NMaj_of_NMaj2 (hpos : NPos) (h2 : NMaj2) : NMaj := by
  intro s hs
  refine le_trans (h2 s hs) ?_
  have hx0 : 0 ≤ π * s / 60 := by have := hs.1; positivity
  have hx1 : π * s / 60 ≤ 1 := by
    have := hs.2; have := Real.pi_lt_d2
    rw [div_le_one (by norm_num)]; nlinarith [Real.pi_pos]
  have hσ := sigmaLow_le_sinc hx0 hx1
  have hσ0 := sigmaLow_nonneg hx0 hx1
  have hP := Pmaj_nonneg hpos s
  unfold Bmaj
  have hsq : sigmaLow (π * s / 60) ^ 2 ≤ Real.sinc (π * s / 60) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
  have := mul_le_mul_of_nonneg_right hsq hP
  nlinarith

end MCert

end ZetaS

end
