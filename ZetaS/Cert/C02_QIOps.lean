/-
nodes/C02_QIOps.lean — track C node C02 (L1_1b, 28 Sep 2026).
Depends on: C01.
Expected proof size: ≤ 120 lines.
PROVED (L5_1, 28 Sep 2026). Imports C01_QIRound for `QI.rdn_le`, `QI.le_rup`.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C01_QIRound

noncomputable section

open Set

namespace ZetaS.CertV2

/-- corner bounds for a product of two interval members. -/
private lemma mul_corner_bounds {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hA : min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_right hx1 hy),
        le_max_of_le_right (mul_le_mul_of_nonneg_right hx2 hy)⟩
    · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_right hx2 hy),
        le_max_of_le_left (mul_le_mul_of_nonpos_right hx1 hy)⟩
  have hB : ∀ u : ℝ, min (u * c) (u * d) ≤ u * y ∧ u * y ≤ max (u * c) (u * d) := by
    intro u
    rcases le_total 0 u with hu | hu
    · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left hy1 hu),
        le_max_of_le_right (mul_le_mul_of_nonneg_left hy2 hu)⟩
    · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left hy2 hu),
        le_max_of_le_left (mul_le_mul_of_nonpos_left hy1 hu)⟩
  obtain ⟨ha1, ha2⟩ := hB a
  obtain ⟨hb1, hb2⟩ := hB b
  refine ⟨le_trans ?_ hA.1, le_trans hA.2 ?_⟩
  · exact le_min (le_trans (min_le_left _ _) ha1) (le_trans (min_le_right _ _) hb1)
  · exact max_le (le_trans ha2 (le_max_left _ _)) (le_trans hb2 (le_max_right _ _))

private lemma rdn_le_real {q : ℚ} {x : ℝ} (h : (q : ℝ) ≤ x) : ((QI.rdn q : ℚ) : ℝ) ≤ x :=
  le_trans (Rat.cast_le.mpr (QI.rdn_le q)) h

private lemma le_rup_real {q : ℚ} {x : ℝ} (h : x ≤ (q : ℝ)) : x ≤ ((QI.rup q : ℚ) : ℝ) :=
  le_trans h (Rat.cast_le.mpr (QI.le_rup q))

private lemma inv_anti_same_sign {a b : ℝ} (hab : a ≤ b) (hpos : 0 < a * b) : b⁻¹ ≤ a⁻¹ := by
  have ha : a ≠ 0 := by rintro rfl; simp at hpos
  have hb : b ≠ 0 := by rintro rfl; simp at hpos
  have h1 : a⁻¹ - b⁻¹ = (b - a) / (a * b) := inv_sub_inv ha hb
  have h2 : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) hpos.le
  linarith

private lemma qabs_eq (q : ℚ) : qabs q = |q| := by
  unfold qabs
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.mp h)).symm

theorem QI.contains_add {I J : QI} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (QI.add I J).Contains (x + y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  simp only [QI.Contains, QI.add, Rat.cast_add]
  constructor <;> linarith
theorem QI.contains_neg {I : QI} {x : ℝ} (hx : I.Contains x) : (QI.neg I).Contains (-x) := by
  obtain ⟨h1, h2⟩ := hx
  simp only [QI.Contains, QI.neg, Rat.cast_neg]
  constructor <;> linarith
theorem QI.contains_sub {I J : QI} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (QI.sub I J).Contains (x - y) := by
  rw [sub_eq_add_neg]; exact QI.contains_add hx (QI.contains_neg hy)
theorem QI.contains_mul {I J : QI} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (QI.mul I J).Contains (x * y) := by
  obtain ⟨h1, h2⟩ := hx; obtain ⟨h3, h4⟩ := hy
  obtain ⟨m1, m2⟩ := mul_corner_bounds h1 h2 h3 h4
  simp only [QI.Contains, QI.mul]
  exact ⟨rdn_le_real (by push_cast; exact m1), le_rup_real (by push_cast; exact m2)⟩
theorem QI.contains_smul (q : ℚ) {I : QI} {x : ℝ} (hx : I.Contains x) : (QI.smul q I).Contains ((q : ℝ) * x) :=
  QI.contains_mul (I := QI.pt q) ⟨le_rfl, le_rfl⟩ hx
theorem QI.contains_sq {I : QI} {x : ℝ} (hx : I.Contains x) : (QI.sq I).Contains (x ^ 2) := by
  obtain ⟨h1, h2⟩ := hx
  unfold QI.sq
  split_ifs with ha hb
  · have ha' : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast ha
    simp only [QI.Contains]
    exact ⟨rdn_le_real (by push_cast; nlinarith), le_rup_real (by push_cast; nlinarith)⟩
  · have hb' : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hb
    simp only [QI.Contains]
    exact ⟨rdn_le_real (by push_cast; nlinarith), le_rup_real (by push_cast; nlinarith)⟩
  · simp only [QI.Contains]
    refine ⟨by push_cast; positivity, le_rup_real ?_⟩
    push_cast
    rcases le_total 0 x with h | h
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
theorem QI.contains_widen {I : QI} {x : ℝ} {e : ℚ} (he : 0 ≤ e) (hx : I.Contains x) : (QI.widen I e).Contains x := by
  obtain ⟨h1, h2⟩ := hx
  have he' : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  simp only [QI.Contains, QI.widen, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith
theorem QI.contains_inv {I : QI} {x : ℝ} (hx : I.Contains x) (h : 0 < I.lo ∨ I.hi < 0) :
    (QI.inv I).Contains x⁻¹ := by
  obtain ⟨h1, h2⟩ := hx
  unfold QI.inv
  rw [if_pos h]
  simp only [QI.Contains]
  have key : 0 < x * (I.hi : ℝ) ∧ 0 < (I.lo : ℝ) * x := by
    rcases h with h | h
    · have h' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast h
      exact ⟨mul_pos (by linarith) (by linarith), mul_pos h' (by linarith)⟩
    · have h' : (I.hi : ℝ) < 0 := by exact_mod_cast h
      exact ⟨mul_pos_of_neg_of_neg (by linarith) h', mul_pos_of_neg_of_neg (by linarith) (by linarith)⟩
  refine ⟨rdn_le_real ?_, le_rup_real ?_⟩
  · push_cast; rw [one_div]; exact inv_anti_same_sign h2 key.1
  · push_cast; rw [one_div]; exact inv_anti_same_sign h1 key.2
theorem QI.contains_of_superset {I J : QI} (h : QI.superset I J = true) {x : ℝ} (hx : J.Contains x) :
    I.Contains x := by
  simp only [QI.superset, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := hx
  have e1 : (I.lo : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast h.1
  have e2 : (J.hi : ℝ) ≤ (I.hi : ℝ) := by exact_mod_cast h.2
  exact ⟨le_trans e1 h1, le_trans h2 e2⟩
theorem QI.abs_le_absMax {I : QI} {x : ℝ} (hx : I.Contains x) : |x| ≤ ((I.absMax : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := hx
  simp only [QI.absMax, qabs_eq]
  push_cast
  exact abs_le_max_abs_abs h1 h2

end ZetaS.CertV2
