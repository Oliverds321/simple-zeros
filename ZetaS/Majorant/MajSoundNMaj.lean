/-
lean_work/L5_2/MajSoundNMaj.lean — L5_2, 28 Sep 2026. **The NMaj2 cell lemma and the soundness of `MajCheck.majOk`.**

  g(s)  = (1/60) σ(πs/60)² P(s) − cos(8s/5)/Z,  Z = (5/4) sin(4/5),  σ(x) = 1 − x²/6 − x⁴/100;
  NMaj2 ⟺ g ≥ 0 on [0, 1/2].
  * `hasDerivAt_gM`, `hasDerivAt_gM1` : explicit g′, g″ (product and chain rules);
  * `abs_gM2_le`  : |g″| ≤ 7 on [−1, 1]  (|P| ≤ 70, |P′| ≤ 103, |P″| ≤ 231, |σ-factors| small, Z ≥ 0.893);
  * `taylor2_local` : second-order lower bound from a LOCAL bound on f″ (MVT, reflection);
  * `gM_cell`     : g(s) ≥ g(m) − |g′(m)| r − (7/2) r² on cells inside [0, 1/2];
  * `gEncl_sound` : the rational-interval enclosures of `MajCheck.gEncl` contain g(m), g′(m)
                    (C02 interval lemmas — proved by L5_1 —, C04 π, C05 sin/cos Taylor, C06 sin(4/5));
  * `majOk_sound`, `majChainOk_sound`.
-/
import ZetaS.Majorant.MajSoundNPos
import ZetaS.Cert.C02_QIOps
import ZetaS.Cert.C04_PiEncl

open Real Finset

noncomputable section

namespace ZetaS.MajSound

open ZetaS.MCert ZetaS.MajCheck ZetaS.CertV2

/-! ### 1. Second-order Taylor bound from a local bound on f″ -/

lemma taylor2_right {f f1 f2 : ℝ → ℝ} {M a b : ℝ} (h0 : ∀ x, HasDerivAt f (f1 x) x)
    (h1 : ∀ x, HasDerivAt f1 (f2 x) x) (hM : ∀ x, a ≤ x → x ≤ b → |f2 x| ≤ M) {m s : ℝ}
    (ham : a ≤ m) (hms : m ≤ s) (hsb : s ≤ b) :
    f m + f1 m * (s - m) - M / 2 * (s - m) ^ 2 ≤ f s := by
  have st1 : ∀ x, m ≤ x → x ≤ s → 0 ≤ f1 x - f1 m + M * (x - m) := by
    intro x hx hxs
    have := ge_of_deriv_nonneg (ψ := fun t => f1 t + M * t) (ψ' := fun t => f2 t + M)
      (fun t => ((h1 t).add ((hasDerivAt_id' t).const_mul M)).congr_deriv (by ring)) hx
      (fun t ht1 ht2 => by have := (abs_le.1 (hM t (by linarith) (by linarith))).1; linarith)
    try simp only at this
    linarith
  have hd : ∀ t, HasDerivAt (fun t => f t - f m - f1 m * (t - m) + M / 2 * (t - m) ^ 2)
      (f1 t - f1 m + M * (t - m)) t := by
    intro t
    exact ((((h0 t).sub_const (f m)).sub (((hasDerivAt_id' t).sub_const m).const_mul (f1 m))).add
      ((((hasDerivAt_id' t).sub_const m).pow 2).const_mul (M / 2))).congr_deriv (by simp; ring)
  have := ge_of_deriv_nonneg hd hms (fun t ht hts => st1 t ht.le hts.le)
  simp only [sub_self, mul_zero] at this
  norm_num at this
  linarith

lemma taylor2_local {f f1 f2 : ℝ → ℝ} {M a b : ℝ} (h0 : ∀ x, HasDerivAt f (f1 x) x)
    (h1 : ∀ x, HasDerivAt f1 (f2 x) x) (hM : ∀ x, a ≤ x → x ≤ b → |f2 x| ≤ M) {m s : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b) (has : a ≤ s) (hsb : s ≤ b) :
    f m + f1 m * (s - m) - M / 2 * (s - m) ^ 2 ≤ f s := by
  rcases le_total m s with hms | hsm
  · exact taylor2_right h0 h1 hM ham hms hsb
  · have r0 : ∀ x, HasDerivAt (fun y => f (-y)) (-f1 (-x)) x := fun x =>
      ((h0 (-x)).comp x (hasDerivAt_neg x)).congr_deriv (by ring)
    have r1 : ∀ x, HasDerivAt (fun y => -f1 (-y)) (f2 (-x)) x := fun x =>
      (((h1 (-x)).comp x (hasDerivAt_neg x)).neg).congr_deriv (by ring)
    have := taylor2_right (a := -b) (b := -a) r0 r1
      (fun x h1 h2 => hM (-x) (by linarith) (by linarith)) (neg_le_neg hmb) (neg_le_neg hsm) (neg_le_neg has)
    simp only [neg_neg] at this
    convert this using 1
    ring

/-! ### 2. g, g′, g″ -/

def Zc : ℝ := 5 / 4 * Real.sin (4 / 5)
def xs (s : ℝ) : ℝ := π * s / 60
def sg (s : ℝ) : ℝ := 1 - xs s ^ 2 / 6 - xs s ^ 4 / 100
def sg1 (s : ℝ) : ℝ := (-(xs s) / 3 - xs s ^ 3 / 25) * (π / 60)
def sg2 (s : ℝ) : ℝ := (-1 / 3 - 3 * xs s ^ 2 / 25) * (π / 60) ^ 2

def gM (s : ℝ) : ℝ := 1 / 60 * sg s ^ 2 * Pmaj s - Real.cos (8 / 5 * s) / Zc
def gM1 (s : ℝ) : ℝ :=
  1 / 60 * (2 * sg s * sg1 s * Pmaj s + sg s ^ 2 * dPmaj s) + 8 / 5 * Real.sin (8 / 5 * s) / Zc
def gM2 (s : ℝ) : ℝ :=
  1 / 60 * ((2 * sg1 s ^ 2 + 2 * sg s * sg2 s) * Pmaj s + 2 * (2 * sg s * sg1 s) * dPmaj s + sg s ^ 2 * d2Pmaj s)
    + 64 / 25 * Real.cos (8 / 5 * s) / Zc

lemma hasDerivAt_xs (s : ℝ) : HasDerivAt xs (π / 60) s :=
  (((hasDerivAt_id' s).const_mul π).div_const 60).congr_deriv (by ring)

lemma hasDerivAt_sg (s : ℝ) : HasDerivAt sg (sg1 s) s := by
  have h := (((hasDerivAt_xs s).pow 2).div_const 6).const_sub 1 |>.sub (((hasDerivAt_xs s).pow 4).div_const 100)
  unfold sg sg1
  exact h.congr_deriv (by simp; ring)

lemma hasDerivAt_sg1 (s : ℝ) : HasDerivAt sg1 (sg2 s) s := by
  have h := ((((hasDerivAt_xs s).neg).div_const 3).sub (((hasDerivAt_xs s).pow 3).div_const 25)).mul_const (π / 60)
  unfold sg1 sg2
  exact h.congr_deriv (by simp; ring)

lemma hasDerivAt_gM (s : ℝ) : HasDerivAt gM (gM1 s) s := by
  have hq := ((hasDerivAt_sg s).pow 2).const_mul (1 / 60)
  have h1 := hq.mul (hasDerivAt_Pmaj s)
  have hc := (((hasDerivAt_id' s).const_mul (8 / 5)).cos).div_const Zc
  have h := h1.sub hc
  unfold gM gM1
  exact h.congr_deriv (by simp; ring)

lemma hasDerivAt_gM1 (s : ℝ) : HasDerivAt gM1 (gM2 s) s := by
  have ha := (((hasDerivAt_sg s).const_mul 2).mul (hasDerivAt_sg1 s)).mul (hasDerivAt_Pmaj s)
  have hb := ((hasDerivAt_sg s).pow 2).mul (hasDerivAt_dPmaj s)
  have hc := ((((hasDerivAt_id' s).const_mul (8 / 5)).sin).const_mul (8 / 5)).div_const Zc
  have h := ((ha.add hb).const_mul (1 / 60)).add hc
  unfold gM1 gM2
  exact h.congr_deriv (by simp; ring)

/-! ### 3. |g″| ≤ 7 on [−1, 1] -/

lemma abs_Pmaj_le (s : ℝ) : |Pmaj s| ≤ 70 := by
  have h1 : |Pmaj s| ≤ |beta 0| + 2 * ∑ j ∈ Icc 1 59, |beta j| := by
    unfold Pmaj
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  refine h1.trans ?_
  rw [show Finset.Icc 1 59 = Finset.Ico 1 60 by rfl, Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, beta]
  norm_num [betaQ, abs_div]

lemma abs_dPmaj_le (s : ℝ) : |dPmaj s| ≤ 103 := by
  have h1 : |dPmaj s| ≤ 2 * ∑ j ∈ Icc 1 59, |beta j| * (π * (j / 30)) := by
    unfold dPmaj
    rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ π * (j / 30))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  refine h1.trans ?_
  have hπ : π < 3.1416 := Real.pi_lt_d4
  have h : 2 * ∑ j ∈ Icc 1 59, |beta j| * (π * (j / 30)) ≤
      2 * ∑ j ∈ Icc 1 59, |beta j| * ((3.1416 : ℝ) * (j / 30)) := by
    gcongr with j hj
  refine h.trans ?_
  rw [show Finset.Icc 1 59 = Finset.Ico 1 60 by rfl, Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, beta]
  norm_num [betaQ, abs_div]

lemma Zc_ge : (893 / 1000 : ℝ) ≤ Zc := by
  have := Real.sin_gt_sub_cube (x := 4 / 5) (by norm_num)
  unfold Zc; norm_num at this ⊢; linarith

lemma abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

lemma abs_gM2_le {s : ℝ} (h1 : -1 ≤ s) (h2 : s ≤ 1) : |gM2 s| ≤ 7 := by
  have hπ : π < 3.1416 := Real.pi_lt_d4
  have hπ0 : 0 < π := Real.pi_pos
  have hx : |xs s| ≤ 1 / 10 := by
    unfold xs; rw [abs_div, abs_mul, abs_of_pos hπ0, abs_of_pos (by norm_num : (0 : ℝ) < 60)]
    have : |s| ≤ 1 := abs_le.2 ⟨h1, h2⟩
    rw [div_le_iff₀ (by norm_num)]; nlinarith [abs_nonneg s]
  have hx2 : xs s ^ 2 ≤ 1 / 100 := by
    have := sq_abs (xs s); nlinarith [abs_nonneg (xs s)]
  have hx4 : xs s ^ 4 ≤ 1 / 10000 := by
    have : xs s ^ 4 = (xs s ^ 2) ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg (xs s)]
  have hp : |π / 60| ≤ 1 / 10 := by
    rw [abs_of_pos (by positivity)]; linarith
  have hsg0 : 0 ≤ sg s := by unfold sg; nlinarith [sq_nonneg (xs s), pow_two_nonneg (xs s ^ 2)]
  have hsg1' : sg s ≤ 1 := by unfold sg; nlinarith [sq_nonneg (xs s), pow_two_nonneg (xs s ^ 2)]
  have hsg : |sg s| ≤ 1 := by rw [abs_of_nonneg hsg0]; exact hsg1'
  have hs1 : |sg1 s| ≤ 1 / 250 := by
    unfold sg1
    have ha : |-(xs s) / 3 - xs s ^ 3 / 25| ≤ 1 / 25 := by
      have h3 : |xs s| ^ 3 ≤ 1 / 1000 := (pow_le_pow_left₀ (abs_nonneg _) hx 3).trans (by norm_num)
      have := abs_sub (-(xs s) / 3) (xs s ^ 3 / 25)
      rw [abs_div, abs_div, abs_neg, abs_pow] at this
      norm_num at this
      linarith
    calc |(-(xs s) / 3 - xs s ^ 3 / 25) * (π / 60)| ≤ 1 / 25 * (1 / 10) := abs_mul_le_of ha hp
      _ ≤ 1 / 250 := by norm_num
  have hs2 : |sg2 s| ≤ 1 / 250 := by
    unfold sg2
    have ha : |-1 / 3 - 3 * xs s ^ 2 / 25| ≤ 17 / 50 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (xs s)]
    have hp2 : |(π / 60) ^ 2| ≤ 1 / 100 := by
      rw [abs_pow]; calc |π / 60| ^ 2 ≤ (1 / 10) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hp 2
        _ = 1 / 100 := by norm_num
    calc |(-1 / 3 - 3 * xs s ^ 2 / 25) * (π / 60) ^ 2| ≤ 17 / 50 * (1 / 100) := abs_mul_le_of ha hp2
      _ ≤ 1 / 250 := by norm_num
  have hq2 : |2 * sg1 s ^ 2 + 2 * sg s * sg2 s| ≤ 81 / 10000 := by
    have e1 : |2 * sg1 s ^ 2| ≤ 2 * (1 / 250) ^ 2 := by
      rw [abs_mul, abs_pow, show |(2 : ℝ)| = 2 by norm_num]
      gcongr
    have e2 : |2 * sg s * sg2 s| ≤ 2 * 1 * (1 / 250) := by
      rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      gcongr
    have := abs_add_le (2 * sg1 s ^ 2) (2 * sg s * sg2 s)
    linarith
  have hq1 : |2 * (2 * sg s * sg1 s)| ≤ 16 / 1000 := by
    rw [abs_mul, abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    have := mul_le_mul hsg hs1 (abs_nonneg _) zero_le_one
    nlinarith [abs_nonneg (sg s), abs_nonneg (sg1 s)]
  have hq : |sg s ^ 2| ≤ 1 := by
    rw [abs_pow]; calc |sg s| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hsg 2
      _ = 1 := by norm_num
  have hP := abs_Pmaj_le s
  have hP1 := abs_dPmaj_le s
  have hP2 : |d2Pmaj s| ≤ 231 := (abs_d2Pmaj_le s).trans M2_le
  have t1 := abs_mul_le_of hq2 hP
  have t2 := abs_mul_le_of hq1 hP1
  have t3 := abs_mul_le_of hq hP2
  have hZ := Zc_ge
  have hZ0 : 0 < Zc := by linarith
  have t4 : |64 / 25 * Real.cos (8 / 5 * s) / Zc| ≤ 64 / 25 / (893 / 1000) := by
    rw [abs_div, abs_mul, abs_of_pos hZ0, show |(64 / 25 : ℝ)| = 64 / 25 by norm_num]
    rw [div_le_div_iff₀ hZ0 (by norm_num)]
    have := Real.abs_cos_le_one (8 / 5 * s)
    nlinarith [abs_nonneg (Real.cos (8 / 5 * s))]
  unfold gM2
  have tri1 := abs_add_le ((2 * sg1 s ^ 2 + 2 * sg s * sg2 s) * Pmaj s + 2 * (2 * sg s * sg1 s) * dPmaj s)
    (sg s ^ 2 * d2Pmaj s)
  have tri2 := abs_add_le ((2 * sg1 s ^ 2 + 2 * sg s * sg2 s) * Pmaj s) (2 * (2 * sg s * sg1 s) * dPmaj s)
  have tri3 := abs_add_le (1 / 60 * ((2 * sg1 s ^ 2 + 2 * sg s * sg2 s) * Pmaj s +
    2 * (2 * sg s * sg1 s) * dPmaj s + sg s ^ 2 * d2Pmaj s)) (64 / 25 * Real.cos (8 / 5 * s) / Zc)
  rw [abs_mul (1 / 60 : ℝ), show |(1 / 60 : ℝ)| = 1 / 60 by norm_num] at tri3
  linarith

/-- **the NMaj2 cell lemma**: g(s) ≥ g(m) − |g′(m)| r − (7/2) r² for |s − m| ≤ r, [m − r, m + r] ⊆ [−1, 1]. -/
lemma gM_cell {m r s : ℝ} (hl : -1 ≤ m - r) (hu : m + r ≤ 1) (hs : |s - m| ≤ r) :
    gM m - |gM1 m| * r - 7 / 2 * r ^ 2 ≤ gM s := by
  have hr : 0 ≤ r := le_trans (abs_nonneg _) hs
  obtain ⟨hs1, hs2⟩ := abs_le.1 hs
  have h := taylor2_local (a := -1) (b := 1) hasDerivAt_gM hasDerivAt_gM1
    (fun x h1 h2 => abs_gM2_le h1 h2) (by linarith) (by linarith) (by linarith) (by linarith) (m := m) (s := s)
  have e1 : -(|gM1 m| * r) ≤ gM1 m * (s - m) := by
    have : |gM1 m * (s - m)| ≤ |gM1 m| * r := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    linarith [neg_abs_le (gM1 m * (s - m))]
  have hsq : (s - m) ^ 2 ≤ r ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  nlinarith

/-! ### 4. The enclosures of `gEncl` -/

lemma pt_contains (q : ℚ) : (QI.pt q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

lemma absMax_pt_le {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : (QI.pt q).absMax ≤ 1 := by
  unfold QI.absMax QI.pt qabs
  simp only
  rw [if_neg (not_lt.2 h0), max_self]; exact h1

lemma gEncl_sound (hC : CNodes) (mq : ℚ) (hm0 : 0 ≤ mq) (hm1 : mq ≤ 1 / 2) (C1 S1 : ℤ)
    (hst : startErr (sinCosPiQ (mq / 30)) C1 S1 ≤ eps0) (hZpos : 0 < (QI.smul (5 / 4) sinA).lo) :
    (gEncl mq (acc C1 S1 trip (C1, S1) (0, 0, 0))).1.Contains (gM mq) ∧
    (gEncl mq (acc C1 S1 trip (C1, S1) (0, 0, 0))).2.Contains (gM1 mq) := by
  have h0 := start_sound hC (mq / 30) C1 S1 hst
  push_cast at h0
  obtain ⟨E0, -, -, T, hT, E1⟩ := sums_sound (mq : ℝ) C1 S1 h0
  set a := acc C1 S1 trip (C1, S1) (0, 0, 0)
  have hsc : ((sc124 : ℚ) : ℝ) = 1 / 2 ^ 124 := by unfold sc124; norm_num
  have hdl : ((dlt : ℚ) : ℝ) = 1 / 2 ^ 49 := by unfold dlt; norm_num
  -- P(m)
  have hPI : QI.Contains ⟨b0 + 2 * ((a.1 : ℚ) * sc124) - 236 * dlt, b0 + 2 * ((a.1 : ℚ) * sc124) + 236 * dlt⟩
      (Pmaj mq) := by
    unfold QI.Contains; push_cast; rw [hsc, hdl, b0_eq]
    obtain ⟨l, u⟩ := abs_le.1 E0
    constructor <;> [skip; skip] <;> norm_num at l u ⊢ <;> linarith
  -- P′(m)
  have hTI : QI.Contains ⟨(a.2.1 : ℚ) * sc124 - 6962 * dlt, (a.2.1 : ℚ) * sc124 + 6962 * dlt⟩ T := by
    unfold QI.Contains; push_cast; rw [hsc, hdl]
    obtain ⟨l, u⟩ := abs_le.1 E1
    constructor <;> norm_num at l u ⊢ <;> linarith
  have hP1 : (QI.mul (QI.smul (-1 / 15) piQ)
      ⟨(a.2.1 : ℚ) * sc124 - 6962 * dlt, (a.2.1 : ℚ) * sc124 + 6962 * dlt⟩).Contains (dPmaj mq) := by
    have := QI.contains_mul (QI.contains_smul (-1 / 15) piQ_contains) hTI
    rw [hT]; convert this using 1; push_cast; ring
  -- σ-factors
  have hX : (QI.smul (mq / 60) piQ).Contains (xs mq) := by
    have := QI.contains_smul (mq / 60) piQ_contains
    convert this using 1; unfold xs; push_cast; ring
  have hX2 := QI.contains_sq hX
  have hsig : (QI.sub (QI.sub (QI.pt 1) (QI.smul (1 / 6) (QI.sq (QI.smul (mq / 60) piQ))))
      (QI.smul (1 / 100) (QI.sq (QI.sq (QI.smul (mq / 60) piQ))))).Contains (sg mq) := by
    have := QI.contains_sub (QI.contains_sub (pt_contains 1) (QI.contains_smul (1 / 6) hX2))
      (QI.contains_smul (1 / 100) (QI.contains_sq hX2))
    convert this using 1; unfold sg; push_cast; ring
  have hsigp : (QI.sub (QI.smul (-1 / 3) (QI.smul (mq / 60) piQ))
      (QI.smul (1 / 25) (QI.mul (QI.sq (QI.smul (mq / 60) piQ)) (QI.smul (mq / 60) piQ)))).Contains
      (-(xs mq) / 3 - xs mq ^ 3 / 25) := by
    have := QI.contains_sub (QI.contains_smul (-1 / 3) hX) (QI.contains_smul (1 / 25) (QI.contains_mul hX2 hX))
    convert this using 1; push_cast; ring
  have hq := QI.contains_sq hsig
  have hq1 := QI.contains_smul 2 (QI.contains_mul (QI.contains_mul hsig hsigp)
    (QI.contains_smul (1 / 60) piQ_contains))
  -- 1/Z, cos, sin
  have hZ := QI.contains_smul (5 / 4) hC.sinA
  have hZi := QI.contains_inv hZ (Or.inl hZpos)
  have hab : (QI.pt (8 * mq / 5)).absMax ≤ 1 :=
    absMax_pt_le (by positivity) (by linarith)
  have hcI := hC.cosT 9 hab (pt_contains (8 * mq / 5))
  have hsI := hC.sinT 9 hab (pt_contains (8 * mq / 5))
  have hZe : ((5 / 4 : ℚ) : ℝ) * Real.sin (4 / 5) = Zc := by unfold Zc; push_cast; ring
  rw [hZe] at hZi
  have e8 : (((8 * mq / 5 : ℚ)) : ℝ) = 8 / 5 * (mq : ℝ) := by push_cast; ring
  rw [e8] at hcI hsI
  constructor
  · have := QI.contains_sub (QI.contains_smul (1 / 60) (QI.contains_mul hq hPI)) (QI.contains_mul hcI hZi)
    convert this using 1
    · rfl
    · unfold gM; push_cast; ring
  · have := QI.contains_add (QI.contains_smul (1 / 60) (QI.contains_add (QI.contains_mul hq1 hPI)
      (QI.contains_mul hq hP1))) (QI.contains_smul (8 / 5) (QI.contains_mul hsI hZi))
    convert this using 1
    · rfl
    · unfold gM1 sg1; push_cast; ring

/-! ### 5. Soundness of the NMaj2 checker -/

theorem majOk_sound (hC : CNodes) (A B : ℕ) (h : MajCheck.majOk A B = true) (s : ℝ)
    (h1 : (A : ℝ) / 2 ^ 24 ≤ s) (h2 : s ≤ (B : ℝ) / 2 ^ 24) : 0 ≤ gM s := by
  unfold MajCheck.majOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hAB, hB⟩, hZ⟩, hcore⟩ := h
  unfold majCore at hcore
  rw [Bool.and_eq_true, decide_eq_true_eq] at hcore
  obtain ⟨hst, hlb⟩ := hcore
  set mq : ℚ := ((A + B : ℕ) : ℚ) / 33554432 with hmq
  set rq : ℚ := ((B - A : ℕ) : ℚ) / 33554432 with hrq
  have hm0 : 0 ≤ mq := by positivity
  have hBq : (B : ℚ) ≤ 8388608 := by exact_mod_cast hB
  have hABq : (A : ℚ) ≤ B := by exact_mod_cast hAB
  have hm1 : mq ≤ 1 / 2 := by rw [hmq]; push_cast; rw [div_le_iff₀ (by norm_num)]; linarith
  obtain ⟨hg, hg1⟩ := gEncl_sound hC mq hm0 hm1 _ _ hst hZ
  unfold gLbOk at hlb
  rw [decide_eq_true_eq] at hlb
  have hlb' := (Rat.cast_le (K := ℝ)).2 hlb
  push_cast at hlb'
  have hB' : (B : ℝ) ≤ 8388608 := by exact_mod_cast hB
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hmr : (mq : ℝ) = ((A : ℝ) + B) / 33554432 := by rw [hmq]; push_cast; ring
  have hrr : (rq : ℝ) = ((B : ℝ) - A) / 33554432 := by rw [hrq]; push_cast [Nat.cast_sub hAB]; ring
  have hsm : |s - (mq : ℝ)| ≤ (rq : ℝ) := by
    rw [hmr, hrr, abs_le]; norm_num at h1 h2; constructor <;> linarith
  have hcell := gM_cell (m := (mq : ℝ)) (r := (rq : ℝ)) (s := s)
    (by rw [hmr, hrr]; have : (0 : ℝ) ≤ A := Nat.cast_nonneg _; linarith)
    (by rw [hmr, hrr]; linarith) hsm
  have hr0 : (0 : ℝ) ≤ rq := le_trans (abs_nonneg _) hsm
  have hglo : ((gEncl mq (acc _ _ trip _ (0, 0, 0))).1.lo : ℝ) ≤ gM mq := hg.1
  have hg1a := QI.abs_le_absMax hg1
  have : |gM1 mq| * rq ≤ (((gEncl mq (acc _ _ trip _ (0, 0, 0))).2.absMax : ℚ) : ℝ) * rq :=
    mul_le_mul_of_nonneg_right hg1a hr0
  nlinarith

theorem majChainOk_sound (hC : CNodes) : ∀ (a b : ℕ) (rest : List ℕ),
    MajCheck.majChainOk (a :: b :: rest) = true →
    ∀ s : ℝ, (a : ℝ) / 2 ^ 24 ≤ s → s ≤ (lastD b rest : ℝ) / 2 ^ 24 → 0 ≤ gM s
  | a, b, [], h, s, h1, h2 => by
    have h' : (MajCheck.majOk a b && MajCheck.majChainOk [b]) = true := h
    rw [Bool.and_eq_true] at h'
    exact majOk_sound hC a b h'.1 s h1 h2
  | a, b, c :: rest, h, s, h1, h2 => by
    have h' : (MajCheck.majOk a b && MajCheck.majChainOk (b :: c :: rest)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases le_total s ((b : ℝ) / 2 ^ 24) with hs | hs
    · exact majOk_sound hC a b h'.1 s h1 hs
    · exact majChainOk_sound hC b c rest h'.2 s hs h2

/-- NMaj2 from `g ≥ 0` on [0, 1/2]. -/
lemma nmaj2_of_gM (h : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), 0 ≤ gM s) : NMaj2 := by
  intro s hs
  have := h s hs
  unfold gM Zc at this
  have e : sg s = sigmaLow (π * s / 60) := by unfold sg sigmaLow xs; ring
  rw [e] at this
  linarith

end ZetaS.MajSound
