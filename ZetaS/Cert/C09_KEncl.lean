/-
nodes/C09_KEncl.lean — track C node C09 (L1_1b, 28 Sep 2026).
Depends on: C02, C06, C07b, C08.
Expected proof size: ≤ 80 lines.
PROVED (L5_1, 28 Sep 2026), statements unchanged, but against the CORRECTED C07b (`sincDerivsQI_contains'`,
file C07b_SincEncl_fix.lean, extra hypothesis `Y.absMax ≤ 1/2 ∨ 0 < Y.lo ∨ Y.hi < 0`), which is discharged here
for the intervals Y = x·π ± 4/5 that `kEnclQ` builds (`Y_ok`: if Y straddles 0 then |x| ≤ 1 and Y has width
≤ 10⁻²⁰ + 2⁻⁶³). C08 is not needed.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C06_SinCosPi
import ZetaS.Cert.C07b_SincEncl

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

/-- the argument intervals of `kEnclQ` satisfy the side condition of the corrected C07b. -/
private lemma Y_ok (x c : ℚ) (hc : |c| ≤ 4 / 5) :
    (QI.add (QI.smul x piQ) (QI.pt c)).absMax ≤ 1 / 2 ∨ 0 < (QI.add (QI.smul x piQ) (QI.pt c)).lo ∨
      (QI.add (QI.smul x piQ) (QI.pt c)).hi < 0 := by
  simp only [QI.add, QI.smul, QI.mul, QI.pt, QI.absMax, min_self, max_self]
  have hP1 : (3 : ℚ) < piQ.lo := by norm_num [piQ]
  have hP2 : piQ.hi < 4 := by norm_num [piQ]
  have hd : piQ.hi - piQ.lo = 1 / 10 ^ 20 := by norm_num [piQ]
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have g1 := rdn_ge (min (x * piQ.lo) (x * piQ.hi))
  have g3 := rup_le' (max (x * piQ.lo) (x * piQ.hi))
  have g2 := QI.rdn_le (min (x * piQ.lo) (x * piQ.hi))
  have g4 := QI.le_rup (max (x * piQ.lo) (x * piQ.hi))
  have hG : (1 : ℚ) / 2 ^ 64 ≤ 1 / 100 := by norm_num
  by_cases h1 : 0 < QI.rdn (min (x * piQ.lo) (x * piQ.hi)) + c
  · exact Or.inr (Or.inl h1)
  by_cases h2 : QI.rup (max (x * piQ.lo) (x * piQ.hi)) + c < 0
  · exact Or.inr (Or.inr h2)
  left
  push Not at h1 h2
  have hx : |x| ≤ 1 := by
    by_contra hcon
    push Not at hcon
    rcases lt_abs.mp hcon with h | h
    · have ha : 3 ≤ x * piQ.lo := by nlinarith
      have hb : 3 ≤ x * piQ.hi := by nlinarith
      have : 3 ≤ min (x * piQ.lo) (x * piQ.hi) := le_min ha hb
      linarith
    · have ha : x * piQ.lo ≤ -3 := by nlinarith
      have hb : x * piQ.hi ≤ -3 := by nlinarith
      have : max (x * piQ.lo) (x * piQ.hi) ≤ -3 := max_le ha hb
      linarith
  have hw : max (x * piQ.lo) (x * piQ.hi) - min (x * piQ.lo) (x * piQ.hi) ≤ 1 / 10 ^ 20 := by
    rw [max_sub_min_eq_abs, ← mul_sub, abs_mul, hd]
    have : |(1 : ℚ) / 10 ^ 20| = 1 / 10 ^ 20 := abs_of_pos (by norm_num)
    rw [this]
    nlinarith [abs_nonneg x]
  have hq : ∀ q : ℚ, qabs q = |q| := fun q => by
    unfold qabs; split_ifs with h
    · exact (abs_of_neg h).symm
    · exact (abs_of_nonneg (not_lt.mp h)).symm
  rw [hq, hq]
  apply max_le
  · rw [abs_of_nonpos h1]; linarith
  · rw [abs_of_nonneg h2]; linarith

/-- the three enclosures that `kEnclQ` combines, for the sign `sg`. -/
private def encD (x sg : ℚ) : QI × QI × QI :=
  sincDerivsQI (QI.add (QI.smul x piQ) (QI.pt (sg * (4 / 5))))
    (QI.add (QI.mul (sinCosPiQ x).1 cosA) (QI.smul sg (QI.mul (sinCosPiQ x).2 sinA)))
    (QI.sub (QI.mul (sinCosPiQ x).2 cosA) (QI.smul sg (QI.mul (sinCosPiQ x).1 sinA)))

private lemma encD_sound (x sg : ℚ) (hsg : sg = 1 ∨ sg = -1) :
    (encD x sg).1.Contains (Real.sinc (Real.pi * x + sg * (4 / 5))) ∧
      (encD x sg).2.1.Contains (sinc1 (Real.pi * x + sg * (4 / 5))) ∧
      (encD x sg).2.2.Contains (sinc2 (Real.pi * x + sg * (4 / 5))) := by
  have hsg' : ((sg : ℚ) : ℝ) = 1 ∨ ((sg : ℚ) : ℝ) = -1 := by rcases hsg with rfl | rfl <;> norm_num
  have hc45 : |sg * (4 / 5)| ≤ 4 / 5 := by rcases hsg with rfl | rfl <;> norm_num
  have hcs : Real.cos ((sg : ℝ) * (4 / 5)) = Real.cos (4 / 5) := by
    rcases hsg' with h | h <;> rw [h] <;> simp
  have hsn : Real.sin ((sg : ℝ) * (4 / 5)) = (sg : ℝ) * Real.sin (4 / 5) := by
    rcases hsg' with h | h <;> rw [h] <;> simp
  obtain ⟨sc1, sc2⟩ := sinCosPiQ_contains x
  have hY := QI.contains_add (J := QI.pt (sg * (4 / 5))) (y := (((sg * (4 / 5) : ℚ)) : ℝ))
    (QI.contains_smul x piQ_contains) ⟨le_rfl, le_rfl⟩
  have eY : (x : ℝ) * Real.pi + (((sg * (4 / 5) : ℚ)) : ℝ) = Real.pi * x + sg * (4 / 5) := by push_cast; ring
  rw [eY] at hY
  have hSY := QI.contains_add (QI.contains_mul sc1 cosA_contains)
    (QI.contains_smul sg (QI.contains_mul sc2 sinA_contains))
  have hCY := QI.contains_sub (QI.contains_mul sc2 cosA_contains)
    (QI.contains_smul sg (QI.contains_mul sc1 sinA_contains))
  have eS : Real.sin (Real.pi * x) * Real.cos (4 / 5) + (sg : ℝ) * (Real.cos (Real.pi * x) * Real.sin (4 / 5)) =
      Real.sin (Real.pi * x + sg * (4 / 5)) := by rw [Real.sin_add, hcs, hsn]; ring
  have eC : Real.cos (Real.pi * x) * Real.cos (4 / 5) - (sg : ℝ) * (Real.sin (Real.pi * x) * Real.sin (4 / 5)) =
      Real.cos (Real.pi * x + sg * (4 / 5)) := by rw [Real.cos_add, hcs, hsn]; ring
  rw [eS] at hSY
  rw [eC] at hCY
  exact sincDerivsQI_contains' (Y_ok x _ hc45) hY hSY hCY

private lemma inv2sincA_contains : inv2sincA.Contains (2 * Real.sinc (4 / 5))⁻¹ := by
  have hpos : 0 < (QI.smul (5 / 2) sinA).lo := by decide +kernel
  have h := QI.contains_inv (QI.contains_smul (5 / 2) sinA_contains) (Or.inl hpos)
  have e : (((5 / 2 : ℚ)) : ℝ) * Real.sin (4 / 5) = 2 * Real.sinc (4 / 5) := by
    rw [Real.sinc_of_ne_zero (by norm_num)]; push_cast; ring
  rw [e] at h
  exact h

theorem kEnclQ_contains (x : ℚ) :
    (kEnclQ x).1.Contains (kCos x) ∧ (kEnclQ x).2.1.Contains (kCos1 x) ∧ (kEnclQ x).2.2.Contains (kCos2 x) := by
  have hk : kEnclQ x =
      (QI.mul (QI.add (encD x (-1)).1 (encD x 1).1) inv2sincA,
       QI.mul (QI.mul (QI.add (encD x (-1)).2.1 (encD x 1).2.1) inv2sincA) piQ,
       QI.mul (QI.mul (QI.mul (QI.add (encD x (-1)).2.2 (encD x 1).2.2) inv2sincA) piQ) piQ) := rfl
  obtain ⟨m1, m2, m3⟩ := encD_sound x (-1) (Or.inr rfl)
  obtain ⟨p1, p2, p3⟩ := encD_sound x 1 (Or.inl rfl)
  have am : Real.pi * (x : ℝ) + (((-1 : ℚ)) : ℝ) * (4 / 5) = Real.pi * x - 4 / 5 := by push_cast; ring
  have ap : Real.pi * (x : ℝ) + (((1 : ℚ)) : ℝ) * (4 / 5) = Real.pi * x + 4 / 5 := by push_cast; ring
  rw [am] at m1 m2 m3
  rw [ap] at p1 p2 p3
  rw [hk]
  refine ⟨?_, ?_, ?_⟩
  · have h := QI.contains_mul (QI.contains_add m1 p1) inv2sincA_contains
    have e : kCos x = (Real.sinc (Real.pi * x - 4 / 5) + Real.sinc (Real.pi * x + 4 / 5)) *
        (2 * Real.sinc (4 / 5))⁻¹ := by unfold kCos; rw [div_eq_mul_inv]
    rw [e]; exact h
  · have h := QI.contains_mul (QI.contains_mul (QI.contains_add m2 p2) inv2sincA_contains) piQ_contains
    have e : kCos1 x = (sinc1 (Real.pi * x - 4 / 5) + sinc1 (Real.pi * x + 4 / 5)) *
        (2 * Real.sinc (4 / 5))⁻¹ * Real.pi := by unfold kCos1; rw [div_eq_mul_inv]; ring
    rw [e]; exact h
  · have h := QI.contains_mul (QI.contains_mul (QI.contains_mul (QI.contains_add m3 p3) inv2sincA_contains)
      piQ_contains) piQ_contains
    have e : kCos2 x = (sinc2 (Real.pi * x - 4 / 5) + sinc2 (Real.pi * x + 4 / 5)) *
        (2 * Real.sinc (4 / 5))⁻¹ * Real.pi * Real.pi := by unfold kCos2; rw [div_eq_mul_inv]; ring
    rw [e]; exact h

/-- every record is sound (from its proof field `ok` and `kEnclQ_contains`). -/
theorem KPt.sound (p : KPt) : p.Sound := by
  have hok := p.ok
  simp only [kptOk, Bool.and_eq_true] at hok
  obtain ⟨⟨h0, h1⟩, h2⟩ := hok
  obtain ⟨e0, e1, e2⟩ := kEnclQ_contains p.x
  exact ⟨QI.contains_of_superset h0 e0, QI.contains_of_superset h1 e1, QI.contains_of_superset h2 e2⟩

end ZetaS.CertV2
