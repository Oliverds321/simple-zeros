/-
nodes/C05_SinCosTaylor.lean — track C node C05 (L1_1b, 28 Sep 2026).
Depends on: C02, C03, L0_2 CosWindow.sin_taylor_bounds/cos_taylor_bounds.
Expected proof size: ≤ 100 lines.
PROVED (L5_1, 28 Sep 2026). Imports C03_Horner (hence C02, C01).
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C03_Horner

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fact, ih, Nat.factorial_succ]

private lemma list_range_sum_eq' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- the horner sum over a coefficient list `(List.range n).map c`, as a Finset sum. -/
private lemma horner_sum_eq (c : ℕ → ℚ) (n : ℕ) (u : ℝ) :
    ((List.range ((List.range n).map c).length).map
      fun j => ((((List.range n).map c).getD j 0 : ℚ) : ℝ) * u ^ j).sum = ∑ j ∈ Finset.range n, (c j : ℝ) * u ^ j := by
  rw [List.length_map, List.length_range, list_range_sum_eq']
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using Finset.mem_range.mp hj)]
  simp

/-- widening by e ≥ |x − s| of an interval containing s contains x. -/
private lemma contains_widen_of_near {I : QI} {s x : ℝ} {e : ℚ} (hs : I.Contains s) (h : |x - s| ≤ (e : ℝ)) :
    (QI.widen I e).Contains x := by
  obtain ⟨h1, h2⟩ := hs
  obtain ⟨h3, h4⟩ := abs_le.mp h
  simp only [QI.Contains, QI.widen, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

/-- |sin x − S_n(x)| ≤ x^(2n+1)/(2n+1)! on [0, 1] (alternating series, L0_2). -/
private lemma sin_rem_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    |Real.sin x - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))|
      ≤ x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  have e : ∀ k : ℕ, ((-1 : ℝ)) ^ (2 * k) = 1 := fun k => by rw [pow_mul]; norm_num
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨h1, h2⟩ := ZetaS.CosWindow.sin_taylor_bounds hx0 hx1 k
    rw [Finset.sum_range_succ, e, one_mul] at h2
    rw [abs_le]; constructor <;> linarith
  · have h1 := (ZetaS.CosWindow.sin_taylor_bounds hx0 hx1 (k + 1)).1
    have h2 := (ZetaS.CosWindow.sin_taylor_bounds hx0 hx1 k).2
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, pow_succ, e] at h1
    rw [abs_le]; constructor <;> linarith

private lemma cos_rem_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    |Real.cos x - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ))|
      ≤ x ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  have e : ∀ k : ℕ, ((-1 : ℝ)) ^ (2 * k) = 1 := fun k => by rw [pow_mul]; norm_num
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨h1, h2⟩ := ZetaS.CosWindow.cos_taylor_bounds hx0 hx1 k
    rw [Finset.sum_range_succ, e, one_mul] at h2
    rw [abs_le]; constructor <;> linarith
  · have h1 := (ZetaS.CosWindow.cos_taylor_bounds hx0 hx1 (k + 1)).1
    have h2 := (ZetaS.CosWindow.cos_taylor_bounds hx0 hx1 k).2
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, pow_succ, e] at h1
    rw [abs_le]; constructor <;> linarith

private lemma sin_rem {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    |Real.sin t - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))|
      ≤ |t| ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0]; exact sin_rem_nonneg h0 (by rwa [abs_of_nonneg h0] at ht) n
  · obtain ⟨s, rfl⟩ : ∃ s, t = -s := ⟨-t, (neg_neg t).symm⟩
    have s0 : 0 ≤ s := by linarith
    rw [abs_neg, abs_of_nonneg s0] at ht ⊢
    have ev : ∀ i : ℕ, (-s) ^ (2 * i) = s ^ (2 * i) := fun i => by rw [pow_mul, pow_mul, neg_sq]
    have od : ∀ i : ℕ, (-s) ^ (2 * i + 1) = -s ^ (2 * i + 1) := fun i => by
      rw [pow_succ, ev, pow_succ]; ring
    simp only [od, Real.sin_neg, neg_div, mul_neg, Finset.sum_neg_distrib]
    rw [show ∀ a b : ℝ, -a - -b = -(a - b) from fun a b => by ring, abs_neg]
    exact sin_rem_nonneg s0 ht n

private lemma cos_rem {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    |Real.cos t - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (t ^ (2 * i) / ((2 * i).factorial : ℝ))|
      ≤ |t| ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  have ev : ∀ i : ℕ, t ^ (2 * i) = |t| ^ (2 * i) := fun i => by rw [pow_mul, pow_mul, sq_abs]
  simp only [ev]
  rw [← Real.cos_abs t]
  exact cos_rem_nonneg (abs_nonneg t) ht n

/-- degree-(2n−1) sin enclosure on an interval inside [−1, 1] (alternating series, L0_2's bounds + oddness). -/
theorem sinQI_contains (n : ℕ) {T : QI} {t : ℝ} (hT : T.absMax ≤ 1) (ht : T.Contains t) :
    (sinQI n T).Contains (Real.sin t) := by
  have hta : |t| ≤ ((T.absMax : ℚ) : ℝ) := QI.abs_le_absMax ht
  have hT' : ((T.absMax : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hT
  have hH := horner_contains ((List.range n).map fun j => ((-1 : ℚ) ^ j) / ((fact (2 * j + 1) : Nat) : ℚ))
    (QI.contains_sq ht)
  rw [horner_sum_eq] at hH
  have hM := QI.contains_mul hH ht
  unfold sinQI
  refine contains_widen_of_near hM ?_
  have hsum : (∑ j ∈ Finset.range n, (((-1 : ℚ) ^ j / ((fact (2 * j + 1) : ℕ) : ℚ) : ℚ) : ℝ) * (t ^ 2) ^ j) * t
      = ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fact_eq]
    push_cast
    rw [← pow_mul, pow_succ]
    ring
  rw [hsum]
  refine le_trans (sin_rem (le_trans hta hT') n) (le_trans ?_ (Rat.cast_le.mpr (QI.le_rup _)))
  rw [fact_eq]
  push_cast
  gcongr

theorem cosQI_contains (n : ℕ) {T : QI} {t : ℝ} (hT : T.absMax ≤ 1) (ht : T.Contains t) :
    (cosQI n T).Contains (Real.cos t) := by
  have hta : |t| ≤ ((T.absMax : ℚ) : ℝ) := QI.abs_le_absMax ht
  have hT' : ((T.absMax : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hT
  have hH := horner_contains ((List.range n).map fun j => ((-1 : ℚ) ^ j) / ((fact (2 * j) : Nat) : ℚ))
    (QI.contains_sq ht)
  rw [horner_sum_eq] at hH
  unfold cosQI
  refine contains_widen_of_near hH ?_
  have hsum : ∑ j ∈ Finset.range n, (((-1 : ℚ) ^ j / ((fact (2 * j) : ℕ) : ℚ) : ℚ) : ℝ) * (t ^ 2) ^ j
      = ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (t ^ (2 * i) / ((2 * i).factorial : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fact_eq]
    push_cast
    rw [← pow_mul]
    ring
  rw [hsum]
  refine le_trans (cos_rem (le_trans hta hT') n) (le_trans ?_ (Rat.cast_le.mpr (QI.le_rup _)))
  rw [fact_eq]
  push_cast
  gcongr

end ZetaS.CertV2
