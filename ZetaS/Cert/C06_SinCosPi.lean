/-
nodes/C06_SinCosPi.lean — track C node C06 (L1_1b, 28 Sep 2026).
Depends on: C04, C05.
Expected proof size: ≤ 100 lines.
PROVED (L5_1, 28 Sep 2026). Imports C04_PiEncl and C05_SinCosTaylor.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C04_PiEncl
import ZetaS.Cert.C05_SinCosTaylor

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma rdn_ge (q : ℚ) : q - 1 / 2 ^ 64 ≤ QI.rdn q := by
  unfold QI.rdn QI.grid
  have h := Rat.lt_floor_add_one (q * 2 ^ 64)
  have hg : (0 : ℚ) < 2 ^ 64 := by positivity
  rw [le_div_iff₀ hg]
  push_cast at h
  have e : (q - 1 / 2 ^ 64) * 2 ^ 64 = q * 2 ^ 64 - 1 := by field_simp
  rw [e]; linarith

private lemma rup_le' (q : ℚ) : QI.rup q ≤ q + 1 / 2 ^ 64 := by
  unfold QI.rup QI.grid
  have h := Rat.ceil_lt (x := q * 2 ^ 64)
  have hg : (0 : ℚ) < 2 ^ 64 := by positivity
  rw [div_le_iff₀ hg]
  have e : (q + 1 / 2 ^ 64) * 2 ^ 64 = q * 2 ^ 64 + 1 := by field_simp
  rw [e]; linarith

private lemma qabs_le_one {q : ℚ} (h1 : -1 ≤ q) (h2 : q ≤ 1) : qabs q ≤ 1 := by
  unfold qabs; split_ifs <;> linarith

/-- the reduced argument f·π, |f| ≤ 1/4, has an enclosure inside [−1, 1]. -/
private lemma smul_pi_absMax {f : ℚ} (hf : |f| ≤ 1 / 4) : (QI.smul f piQ).absMax ≤ 1 := by
  have hp : ∀ p : ℚ, |p| ≤ 16 / 5 → -4 / 5 ≤ f * p ∧ f * p ≤ 4 / 5 := by
    intro p hp
    have : |f * p| ≤ 4 / 5 := by
      rw [abs_mul]
      calc |f| * |p| ≤ 1 / 4 * (16 / 5) := mul_le_mul hf hp (abs_nonneg p) (by norm_num)
        _ = 4 / 5 := by norm_num
    obtain ⟨a, b⟩ := abs_le.mp this
    constructor <;> linarith
  have hlo := hp piQ.lo (by norm_num [piQ, abs_le])
  have hhi := hp piQ.hi (by norm_num [piQ, abs_le])
  simp only [QI.smul, QI.mul, QI.pt, QI.absMax]
  have g1 := rdn_ge (min (min (f * piQ.lo) (f * piQ.hi)) (min (f * piQ.lo) (f * piQ.hi)))
  have g2 := QI.rdn_le (min (min (f * piQ.lo) (f * piQ.hi)) (min (f * piQ.lo) (f * piQ.hi)))
  have g3 := rup_le' (max (max (f * piQ.lo) (f * piQ.hi)) (max (f * piQ.lo) (f * piQ.hi)))
  have g4 := QI.le_rup (max (max (f * piQ.lo) (f * piQ.hi)) (max (f * piQ.lo) (f * piQ.hi)))
  have m1 : -4 / 5 ≤ min (min (f * piQ.lo) (f * piQ.hi)) (min (f * piQ.lo) (f * piQ.hi)) :=
    le_min (le_min hlo.1 hhi.1) (le_min hlo.1 hhi.1)
  have m2 : min (min (f * piQ.lo) (f * piQ.hi)) (min (f * piQ.lo) (f * piQ.hi)) ≤ 4 / 5 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hlo.2)
  have m3 : max (max (f * piQ.lo) (f * piQ.hi)) (max (f * piQ.lo) (f * piQ.hi)) ≤ 4 / 5 :=
    max_le (max_le hlo.2 hhi.2) (max_le hlo.2 hhi.2)
  have m4 : -4 / 5 ≤ max (max (f * piQ.lo) (f * piQ.hi)) (max (f * piQ.lo) (f * piQ.hi)) :=
    le_trans hlo.1 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hG : (1 : ℚ) / 2 ^ 64 ≤ 1 / 5 := by norm_num
  exact max_le (qabs_le_one (by linarith) (by linarith)) (qabs_le_one (by linarith) (by linarith))

/-- quarter-period reduction x = n/2 + f, |f| ≤ 1/4 (so |πf| ≤ π/4 < 1). -/
theorem sinCosPiQ_contains (x : ℚ) :
    (sinCosPiQ x).1.Contains (Real.sin (Real.pi * x)) ∧ (sinCosPiQ x).2.Contains (Real.cos (Real.pi * x)) := by
  simp only [sinCosPiQ]
  set n : ℤ := (2 * x + 1 / 2).floor with hn
  have hn1 : (n : ℚ) ≤ 2 * x + 1 / 2 := Rat.floor_le _
  have hn2 : 2 * x + 1 / 2 < (n : ℚ) + 1 := by
    have := Rat.lt_floor_add_one (2 * x + 1 / 2); push_cast at this; exact this
  set f : ℚ := x - (n : ℚ) / 2 with hf
  have hf4 : |f| ≤ 1 / 4 := by rw [abs_le]; constructor <;> linarith
  have hT := smul_pi_absMax hf4
  have htc : (QI.smul f piQ).Contains ((f : ℝ) * Real.pi) := QI.contains_smul f piQ_contains
  have hs := sinQI_contains 9 hT htc
  have hc := cosQI_contains 9 hT htc
  have hx : Real.pi * (x : ℝ) = (f : ℝ) * Real.pi + ((n % 4 : ℤ) : ℝ) * (Real.pi / 2) +
      ((n / 4 : ℤ) : ℝ) * (2 * Real.pi) := by
    have h1 : (x : ℝ) = (f : ℝ) + (n : ℝ) / 2 := by rw [hf]; push_cast; ring
    have h2 : (n : ℝ) = ((n % 4 : ℤ) : ℝ) + 4 * ((n / 4 : ℤ) : ℝ) := by
      have : n = n % 4 + 4 * (n / 4) := by omega
      exact_mod_cast this
    rw [h1, h2]; ring
  rw [hx, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with hr | hr | hr | hr
  · simp only [hr, if_true, Int.cast_zero, zero_mul, add_zero]
    exact ⟨hs, hc⟩
  · simp only [hr, Int.cast_one, one_mul, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
    simp only [show ((1 : ℤ) = 0) = False by decide, if_false, if_true]
    exact ⟨hc, QI.contains_neg hs⟩
  · rw [hr, show (((2 : ℤ) : ℝ)) * (Real.pi / 2) = Real.pi by push_cast; ring, Real.sin_add_pi, Real.cos_add_pi]
    simp only [show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false, if_true]
    exact ⟨QI.contains_neg hs, QI.contains_neg hc⟩
  · rw [hr, show (((3 : ℤ) : ℝ)) * (Real.pi / 2) = Real.pi + Real.pi / 2 by push_cast; ring, ← add_assoc,
      Real.sin_add_pi_div_two, Real.cos_add_pi_div_two, Real.sin_add_pi, Real.cos_add_pi, neg_neg]
    simp only [show ((3 : ℤ) = 0) = False by decide, show ((3 : ℤ) = 1) = False by decide,
      show ((3 : ℤ) = 2) = False by decide, if_false]
    exact ⟨QI.contains_neg hc, hs⟩

theorem sinA_contains : sinA.Contains (Real.sin (4 / 5)) := by
  have h := sinQI_contains 9 (T := QI.pt (4 / 5)) (t := ((4 / 5 : ℚ) : ℝ))
    (by norm_num [QI.absMax, QI.pt, qabs]) ⟨le_rfl, le_rfl⟩
  have e : ((4 / 5 : ℚ) : ℝ) = 4 / 5 := by norm_num
  rw [e] at h
  exact h

theorem cosA_contains : cosA.Contains (Real.cos (4 / 5)) := by
  have h := cosQI_contains 9 (T := QI.pt (4 / 5)) (t := ((4 / 5 : ℚ) : ℝ))
    (by norm_num [QI.absMax, QI.pt, qabs]) ⟨le_rfl, le_rfl⟩
  have e : ((4 / 5 : ℚ) : ℝ) = 4 / 5 := by norm_num
  rw [e] at h
  exact h

end ZetaS.CertV2
