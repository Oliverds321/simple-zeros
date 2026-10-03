/-
nodes/C16_TangentLine.lean — track C node C16 (L1_1b, 28 Sep 2026).
Depends on: C02, C08, C09, C14.
Expected proof size: ≤ 60 lines.
PROVED (L5_1, 28 Sep 2026). Imports C08_KCosDerivs, C09_KEncl (hence C02, corrected C07b), C14_Taylor2Minorant.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C08_KCosDerivs
import ZetaS.Cert.C09_KEncl
import ZetaS.Cert.C14_Taylor2Minorant

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma qabs_eq' (q : ℚ) : qabs q = |q| := by
  unfold qabs
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.mp h)).symm

theorem tangentLine_sound (x0 r tp pen : ℚ) (p : KPt) (hp : p.x = tp) (htp : x0 - r ≤ tp ∧ tp ≤ x0 + r)
    (hpen0 : 0 ≤ pen) (hpen : ∀ ξ ∈ Icc ((x0 : ℝ) - r) (x0 + r), -((pen : ℚ) : ℝ) ≤ wK2 ξ) :
    ∀ x ∈ Icc ((x0 : ℝ) - r) (x0 + r),
      (((tangentLine x0 r tp pen p).1 : ℚ) : ℝ) * x + (((tangentLine x0 r tp pen p).2 : ℚ) : ℝ) ≤ wK x := by
  intro x hx
  obtain ⟨hk0, hk1, -⟩ := KPt.sound p
  rw [hp] at hk0 hk1
  have htpR : (tp : ℝ) ∈ Icc ((x0 : ℝ) - r) (x0 + r) := by
    constructor
    · have := htp.1; exact_mod_cast this
    · have := htp.2; exact_mod_cast this
  have hT := taylor2_minorant (w := wK) (w1 := fun x => 2 * kCos x * kCos1 x) (w2 := wK2)
    hasDerivAt_wK hasDerivAt_wK1 hpen hx htpR
  have hsq := QI.contains_sq hk0
  have hw1 := QI.contains_smul 2 (QI.contains_mul hk0 hk1)
  simp only [tangentLine, qabs_eq']
  set w1 := QI.smul 2 (QI.mul p.k0 p.k1) with hw1def
  set sig := QI.rdn ((w1.lo + w1.hi) / 2) with hsig
  push_cast
  set g := 2 * kCos tp * kCos1 tp with hg
  have hg' : ((2 : ℚ) : ℝ) * (kCos tp * kCos1 tp) = g := by rw [hg]; push_cast; ring
  rw [hg'] at hw1
  obtain ⟨hw1l, hw1h⟩ := hw1
  set D : ℝ := max |(w1.lo : ℝ) - sig| |(w1.hi : ℝ) - sig| with hD
  set rr : ℝ := max |(x0 : ℝ) - r - tp| |(x0 : ℝ) + r - tp| with hrr
  have hgD : |g - sig| ≤ D := by
    rw [abs_le]; constructor
    · have : (sig : ℝ) - w1.lo ≤ |(w1.lo : ℝ) - sig| := by rw [abs_sub_comm]; exact le_abs_self _
      have := le_max_left |(w1.lo : ℝ) - sig| |(w1.hi : ℝ) - sig|
      linarith
    · have : (w1.hi : ℝ) - sig ≤ |(w1.hi : ℝ) - sig| := le_abs_self _
      have := le_max_right |(w1.lo : ℝ) - sig| |(w1.hi : ℝ) - sig|
      linarith
  have hxr : |x - tp| ≤ rr := by
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_le]; constructor
    · have : -((x0 : ℝ) - r - tp) ≤ |(x0 : ℝ) - r - tp| := neg_le_abs _
      have := le_max_left |(x0 : ℝ) - r - tp| |(x0 : ℝ) + r - tp|
      linarith
    · have : (x0 : ℝ) + r - tp ≤ |(x0 : ℝ) + r - tp| := le_abs_self _
      have := le_max_right |(x0 : ℝ) - r - tp| |(x0 : ℝ) + r - tp|
      linarith
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (le_max_left _ _)
  have F1 : -(D * rr) ≤ (g - sig) * (x - tp) := by
    have : |(g - sig) * (x - tp)| ≤ D * rr := by
      rw [abs_mul]; exact mul_le_mul hgD hxr (abs_nonneg _) hD0
    exact (abs_le.mp this).1
  have hpenR : (0 : ℝ) ≤ pen := by exact_mod_cast hpen0
  have F2 : (pen : ℝ) * (x - tp) ^ 2 ≤ pen * (rr * rr) := by
    apply mul_le_mul_of_nonneg_left _ hpenR
    have : (x - tp) ^ 2 = |x - tp| ^ 2 := (sq_abs _).symm
    rw [this]
    nlinarith [abs_nonneg (x - tp)]
  have hwk : wK tp = kCos tp ^ 2 := rfl
  obtain ⟨hsql, -⟩ := hsq
  linarith

end ZetaS.CertV2
