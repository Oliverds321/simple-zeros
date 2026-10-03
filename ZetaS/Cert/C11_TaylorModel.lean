/-
lean_work/L5_2/cnodes/C11_TaylorModel.lean — track C node C11, proved by L5_2 (28 Sep 2026).
Statement byte-identical to `lean_work/L1_1/nodes/C11_TaylorModel.lean`.
Depends on: C01 (`QI.le_rup`, proved), C02 (interval containment, proved by L5_1), C04 (`piQ_contains`, proved),
C08 (`hasDerivAt_kCos`, `hasDerivAt_kCos1`), C09 (`KPt.sound`), C10 (`kCos_d3_bound`, `hasDerivAt_kCos2`).
Proof: third/second/first-order Taylor bounds for k = kCos with |k‴| ≤ π³/4 ≤ M3 (mean-value arguments), then the
interval containments of `taylorModel` step by step.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C01_QIRound
import ZetaS.Cert.C02_QIOps
import ZetaS.Cert.C04_PiEncl
import ZetaS.Cert.C08_KCosDerivs
import ZetaS.Cert.C09_KEncl
import ZetaS.Cert.C10_KCosD3

noncomputable section

open Set

namespace ZetaS.CertV2

namespace C11aux

lemma ge_of_deriv_nonneg {ψ ψ' : ℝ → ℝ} (h : ∀ x, HasDerivAt ψ (ψ' x) x) {m s : ℝ} (hms : m ≤ s)
    (hpos : ∀ x, m < x → x < s → 0 ≤ ψ' x) : ψ m ≤ ψ s := by
  rcases eq_or_lt_of_le hms with h' | hlt
  · rw [h']
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope ψ ψ' hlt
    (fun x _ => (h x).continuousAt.continuousWithinAt) (fun x _ => h x)
  have h1 := hpos c hc.1 hc.2
  have h2 : ψ s - ψ m = ψ' c * (s - m) := by rw [hcs, div_mul_cancel₀ _ (sub_pos.2 hlt).ne']
  nlinarith [sub_pos.2 hlt]

lemma taylor3_right {f f1 f2 f3 : ℝ → ℝ} {M : ℝ}
    (h0 : ∀ x, HasDerivAt f (f1 x) x) (h1 : ∀ x, HasDerivAt f1 (f2 x) x) (h2 : ∀ x, HasDerivAt f2 (f3 x) x)
    (hM : ∀ x, |f3 x| ≤ M) {m s : ℝ} (hms : m ≤ s) :
    f m + f1 m * (s - m) + f2 m * (s - m) ^ 2 / 2 - M * (s - m) ^ 3 / 6 ≤ f s := by
  have st1 : ∀ x, m ≤ x → 0 ≤ f2 x - f2 m + M * (x - m) := by
    intro x hx
    have := ge_of_deriv_nonneg (ψ := fun t => f2 t + M * t) (ψ' := fun t => f3 t + M)
      (fun t => ((h2 t).add ((hasDerivAt_id' t).const_mul M)).congr_deriv (by ring)) hx
      (fun t _ _ => by have := (abs_le.1 (hM t)).1; linarith)
    try simp only at this
    linarith
  have st2 : ∀ x, m ≤ x → 0 ≤ f1 x - f1 m - f2 m * (x - m) + M / 2 * (x - m) ^ 2 := by
    intro x hx
    have hd : ∀ t, HasDerivAt (fun t => f1 t - f1 m - f2 m * (t - m) + M / 2 * (t - m) ^ 2)
        (f2 t - f2 m + M * (t - m)) t := by
      intro t
      exact ((((h1 t).sub_const (f1 m)).sub (((hasDerivAt_id' t).sub_const m).const_mul (f2 m))).add
        ((((hasDerivAt_id' t).sub_const m).pow 2).const_mul (M / 2))).congr_deriv (by simp; ring)
    have := ge_of_deriv_nonneg hd hx (fun t ht _ => st1 t ht.le)
    simp only [sub_self, mul_zero] at this
    norm_num at this
    linarith
  have hd : ∀ t, HasDerivAt (fun t => f t - f m - f1 m * (t - m) - f2 m / 2 * (t - m) ^ 2 + M / 6 * (t - m) ^ 3)
      (f1 t - f1 m - f2 m * (t - m) + M / 2 * (t - m) ^ 2) t := by
    intro t
    exact (((((h0 t).sub_const (f m)).sub (((hasDerivAt_id' t).sub_const m).const_mul (f1 m))).sub
      ((((hasDerivAt_id' t).sub_const m).pow 2).const_mul (f2 m / 2))).add
      ((((hasDerivAt_id' t).sub_const m).pow 3).const_mul (M / 6))).congr_deriv (by simp; ring)
  have := ge_of_deriv_nonneg hd hms (fun t ht _ => st2 t ht.le)
  simp only [sub_self, mul_zero] at this
  norm_num at this
  linarith

lemma taylor3 {f f1 f2 f3 : ℝ → ℝ} {M : ℝ}
    (h0 : ∀ x, HasDerivAt f (f1 x) x) (h1 : ∀ x, HasDerivAt f1 (f2 x) x) (h2 : ∀ x, HasDerivAt f2 (f3 x) x)
    (hM : ∀ x, |f3 x| ≤ M) (m s : ℝ) :
    f m + f1 m * (s - m) + f2 m * (s - m) ^ 2 / 2 - M * |s - m| ^ 3 / 6 ≤ f s := by
  rcases le_total m s with hms | hsm
  · have := taylor3_right h0 h1 h2 hM hms
    rwa [abs_of_nonneg (sub_nonneg.2 hms)]
  · have r0 : ∀ x, HasDerivAt (fun y => f (-y)) (-f1 (-x)) x := fun x =>
      ((h0 (-x)).comp x (hasDerivAt_neg x)).congr_deriv (by ring)
    have r1 : ∀ x, HasDerivAt (fun y => -f1 (-y)) (f2 (-x)) x := fun x =>
      (((h1 (-x)).comp x (hasDerivAt_neg x)).neg).congr_deriv (by ring)
    have r2 : ∀ x, HasDerivAt (fun y => f2 (-y)) (-f3 (-x)) x := fun x =>
      ((h2 (-x)).comp x (hasDerivAt_neg x)).congr_deriv (by ring)
    have := taylor3_right r0 r1 r2 (fun x => by rw [abs_neg]; exact hM (-x)) (neg_le_neg hsm)
    simp only [neg_neg] at this
    rw [abs_of_nonpos (sub_nonpos.2 hsm)]
    convert this using 1
    ring

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



lemma taylor3_abs {f f1 f2 f3 : ℝ → ℝ} {M : ℝ}
    (h0 : ∀ x, HasDerivAt f (f1 x) x) (h1 : ∀ x, HasDerivAt f1 (f2 x) x) (h2 : ∀ x, HasDerivAt f2 (f3 x) x)
    (hM : ∀ x, |f3 x| ≤ M) (m s : ℝ) :
    |f s - (f m + f1 m * (s - m) + f2 m * (s - m) ^ 2 / 2)| ≤ M * |s - m| ^ 3 / 6 := by
  have lo := taylor3 h0 h1 h2 hM m s
  have hi := taylor3 (f := fun y => -f y) (f1 := fun y => -f1 y) (f2 := fun y => -f2 y) (f3 := fun y => -f3 y)
    (fun x => (h0 x).neg) (fun x => (h1 x).neg) (fun x => (h2 x).neg) (fun x => by rw [abs_neg]; exact hM x) m s
  try simp only at hi
  rw [abs_le]; constructor <;> linarith

lemma taylor2_abs {f f1 f2 : ℝ → ℝ} {M : ℝ} (h0 : ∀ x, HasDerivAt f (f1 x) x)
    (h1 : ∀ x, HasDerivAt f1 (f2 x) x) (hM : ∀ x, |f2 x| ≤ M) (m s : ℝ) :
    |f s - (f m + f1 m * (s - m))| ≤ M / 2 * (s - m) ^ 2 := by
  have lo := taylor2_local (a := min m s) (b := max m s) h0 h1 (fun x _ _ => hM x)
    (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _)
  have hi := taylor2_local (a := min m s) (b := max m s) (f := fun y => -f y) (f1 := fun y => -f1 y)
    (f2 := fun y => -f2 y) (fun x => (h0 x).neg) (fun x => (h1 x).neg) (fun x _ _ => by rw [abs_neg]; exact hM x)
    (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _)
  try simp only at hi
  rw [abs_le]; constructor <;> linarith

lemma lip_of_deriv {f f1 : ℝ → ℝ} {M : ℝ} (h0 : ∀ x, HasDerivAt f (f1 x) x) (hM : ∀ x, |f1 x| ≤ M)
    (m s : ℝ) : |f s - f m| ≤ M * |s - m| := by
  have up : ∀ a b : ℝ, a ≤ b → f b - f a ≤ M * (b - a) ∧ f a - f b ≤ M * (b - a) := by
    intro a b hab
    have u1 := ge_of_deriv_nonneg (ψ := fun y => M * y - f y) (ψ' := fun y => M - f1 y)
      (fun y => (((hasDerivAt_id' y).const_mul M).sub (h0 y)).congr_deriv (by ring)) hab
      (fun y _ _ => by have := (abs_le.1 (hM y)).2; linarith)
    have u2 := ge_of_deriv_nonneg (ψ := fun y => M * y + f y) (ψ' := fun y => M + f1 y)
      (fun y => (((hasDerivAt_id' y).const_mul M).add (h0 y)).congr_deriv (by ring)) hab
      (fun y _ _ => by have := (abs_le.1 (hM y)).1; linarith)
    try simp only at u1 u2
    constructor <;> linarith
  rcases le_total m s with h | h
  · obtain ⟨a, b⟩ := up m s h
    rw [abs_of_nonneg (sub_nonneg.2 h), abs_le]; constructor <;> linarith
  · obtain ⟨a, b⟩ := up s m h
    rw [abs_of_nonpos (sub_nonpos.2 h), abs_le]; constructor <;> linarith

lemma contains_widen_of {I : QI} {y z : ℝ} {e : ℚ} (hI : I.Contains y) (hz : |z - y| ≤ (e : ℝ)) :
    (I.widen e).Contains z := by
  obtain ⟨h1, h2⟩ := hI
  obtain ⟨z1, z2⟩ := abs_le.1 hz
  unfold QI.widen QI.Contains; push_cast; constructor <;> linarith

lemma M3_ge : Real.pi ^ 3 / 4 ≤ ((M3 : ℚ) : ℝ) := by
  have hpi : Real.pi ≤ ((piQ.hi : ℚ) : ℝ) := piQ_contains.2
  have h1 : piQ.hi ^ 3 / 4 ≤ M3 := QI.le_rup _
  have h2 : (((piQ.hi ^ 3 / 4 : ℚ)) : ℝ) ≤ ((M3 : ℚ) : ℝ) := Rat.cast_le.2 h1
  have h3 : (((piQ.hi ^ 3 / 4 : ℚ)) : ℝ) = ((piQ.hi : ℚ) : ℝ) ^ 3 / 4 := by
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  have : Real.pi ^ 3 ≤ ((piQ.hi : ℚ) : ℝ) ^ 3 := pow_le_pow_left₀ Real.pi_pos.le hpi 3
  linarith

end C11aux

open C11aux in
theorem taylorModel_sound (p : KPt) (r : ℚ) (hr : 0 ≤ r) :
    ∀ ξ ∈ Icc ((p.x : ℝ) - r) (p.x + r),
      (((taylorModel p.k0 p.k1 p.k2 r).1 : ℚ) : ℝ) ≤ wK2 ξ ∧ wK2 ξ ≤ (((taylorModel p.k0 p.k1 p.k2 r).2.1 : ℚ) : ℝ) ∧
      (((taylorModel p.k0 p.k1 p.k2 r).2.2 : ℚ) : ℝ) ≤ wK ξ := by
  intro ξ hξ
  obtain ⟨h0, h1, h2⟩ := KPt.sound p
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have ht : |ξ - p.x| ≤ (r : ℝ) := abs_le.2 ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hM := M3_ge
  have hM0 : (0 : ℝ) ≤ ((M3 : ℚ) : ℝ) := le_trans (by positivity) hM
  have hd3 : ∀ y, |deriv kCos2 y| ≤ Real.pi ^ 3 / 4 := kCos_d3_bound
  have T0 := taylor3_abs hasDerivAt_kCos hasDerivAt_kCos1 hasDerivAt_kCos2 hd3 (p.x : ℝ) ξ
  have T1 := taylor2_abs hasDerivAt_kCos1 hasDerivAt_kCos2 hd3 (p.x : ℝ) ξ
  have T2 := lip_of_deriv hasDerivAt_kCos2 hd3 (p.x : ℝ) ξ
  set t := ξ - (p.x : ℝ) with htdef
  have hat := abs_nonneg t
  have hT : (⟨-r, r⟩ : QI).Contains t := by
    unfold QI.Contains; push_cast; constructor <;> linarith [(abs_le.1 ht).1, (abs_le.1 ht).2]
  have ht2 : t ^ 2 ≤ (r : ℝ) * r := by rw [← sq_abs]; nlinarith
  have hT2 : (⟨0, r * r⟩ : QI).Contains (t ^ 2) := by
    unfold QI.Contains; push_cast; exact ⟨sq_nonneg t, ht2⟩
  have e0 : |kCos ξ - (kCos p.x + kCos1 p.x * t + ((1 / 2 : ℚ) : ℝ) * (kCos2 p.x * t ^ 2))| ≤
      ((QI.rup (M3 * r ^ 3 / 6) : ℚ) : ℝ) := by
    have hr3 : ((M3 * r ^ 3 / 6 : ℚ) : ℝ) ≤ ((QI.rup (M3 * r ^ 3 / 6) : ℚ) : ℝ) := by exact_mod_cast QI.le_rup _
    push_cast at hr3 ⊢
    have : Real.pi ^ 3 / 4 * |t| ^ 3 / 6 ≤ ((M3 : ℚ) : ℝ) * (r : ℝ) ^ 3 / 6 := by
      have := pow_le_pow_left₀ hat ht 3
      have := mul_le_mul hM this (by positivity) hM0
      linarith
    have e : kCos p.x + kCos1 p.x * t + 1 / 2 * (kCos2 p.x * t ^ 2) =
        kCos p.x + kCos1 p.x * t + kCos2 p.x * t ^ 2 / 2 := by ring
    rw [e]; linarith
  have e1 : |kCos1 ξ - (kCos1 p.x + kCos2 p.x * t)| ≤ ((QI.rup (M3 * r * r / 2) : ℚ) : ℝ) := by
    have hr3 : ((M3 * r * r / 2 : ℚ) : ℝ) ≤ ((QI.rup (M3 * r * r / 2) : ℚ) : ℝ) := by exact_mod_cast QI.le_rup _
    push_cast at hr3 ⊢
    have : Real.pi ^ 3 / 4 / 2 * t ^ 2 ≤ ((M3 : ℚ) : ℝ) * r * r / 2 := by
      have := mul_le_mul hM ht2 (sq_nonneg t) hM0
      nlinarith
    linarith
  have e2 : |kCos2 ξ - kCos2 p.x| ≤ ((QI.rup (M3 * r) : ℚ) : ℝ) := by
    have hr3 : ((M3 * r : ℚ) : ℝ) ≤ ((QI.rup (M3 * r) : ℚ) : ℝ) := by exact_mod_cast QI.le_rup _
    push_cast at hr3 ⊢
    have : Real.pi ^ 3 / 4 * |t| ≤ ((M3 : ℚ) : ℝ) * r := mul_le_mul hM ht hat hM0
    linarith
  have hkI := contains_widen_of (QI.contains_add (QI.contains_add h0 (QI.contains_mul h1 hT))
    (QI.contains_smul (1 / 2) (QI.contains_mul h2 hT2))) e0
  have hk1I := contains_widen_of (QI.contains_add h1 (QI.contains_mul h2 hT)) e1
  have hk2I := contains_widen_of h2 e2
  have hw := QI.contains_smul 2 (QI.contains_add (QI.contains_sq hk1I) (QI.contains_mul hkI hk2I))
  have hsq := QI.contains_sq hkI
  have key : taylorModel p.k0 p.k1 p.k2 r =
      ((QI.smul 2 (QI.add (QI.sq (QI.widen (QI.add p.k1 (QI.mul p.k2 ⟨-r, r⟩)) (QI.rup (M3 * r * r / 2))))
          (QI.mul (QI.widen (QI.add (QI.add p.k0 (QI.mul p.k1 ⟨-r, r⟩)) (QI.smul (1 / 2) (QI.mul p.k2 ⟨0, r * r⟩)))
            (QI.rup (M3 * r ^ 3 / 6))) (QI.widen p.k2 (QI.rup (M3 * r)))))).lo,
       (QI.smul 2 (QI.add (QI.sq (QI.widen (QI.add p.k1 (QI.mul p.k2 ⟨-r, r⟩)) (QI.rup (M3 * r * r / 2))))
          (QI.mul (QI.widen (QI.add (QI.add p.k0 (QI.mul p.k1 ⟨-r, r⟩)) (QI.smul (1 / 2) (QI.mul p.k2 ⟨0, r * r⟩)))
            (QI.rup (M3 * r ^ 3 / 6))) (QI.widen p.k2 (QI.rup (M3 * r)))))).hi,
       max 0 (QI.sq (QI.widen (QI.add (QI.add p.k0 (QI.mul p.k1 ⟨-r, r⟩)) (QI.smul (1 / 2) (QI.mul p.k2 ⟨0, r * r⟩)))
            (QI.rup (M3 * r ^ 3 / 6)))).lo) := rfl
  rw [key]
  have ew : ((2 : ℚ) : ℝ) * (kCos1 ξ ^ 2 + kCos ξ * kCos2 ξ) = wK2 ξ := by unfold wK2; push_cast; ring
  rw [ew] at hw
  refine ⟨hw.1, hw.2, ?_⟩
  simp only
  rw [Rat.cast_max, Rat.cast_zero]
  exact max_le (by unfold wK; positivity) (by unfold wK; exact hsq.1)

end ZetaS.CertV2
