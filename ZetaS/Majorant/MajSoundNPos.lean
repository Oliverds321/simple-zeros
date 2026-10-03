/-
lean_work/L5_2/MajSoundNPos.lean — L5_2, 28 Sep 2026. Soundness of the NPos cell checker `MajCheck.cellOk`.

  * `taylor3`         : third-order Taylor lower bound from a global bound on f‴ (three mean-value steps, reflection);
  * `Pmaj_cell3`      : P(s) ≥ P(m) − |P′(m)| r + min(0, P″(m)) r²/2 − (645/6) r³ for |s − m| ≤ r (|P‴| ≤ 645);
  * `err_bound`       : the fixed-point rotation recurrence z_{k+1} = ⌊z_k z₁/2⁶⁴⌋ stays within (k+1)·2⁻⁵⁵ of e^{i(k+1)θ}
                        (complex norm: the error grows linearly), given |z₁ − e^{iθ}| ≤ 2⁻⁵⁶;
  * `acc_spec`        : the accumulator computes the three exact integer sums;
  * `cellOk_sound`    : `cellOk A B = true → ∀ s ∈ [A/2²⁴, B/2²⁴], 0 ≤ P s`;
  * `chainOk_sound`   : a checked chain of breakpoints gives 0 ≤ P on [first, last].
Dependencies: `MCert_Majorant`/`MCert_Cells` (L2_2, proved), node C06 `sinCosPiQ_contains` (statement; L5_1 proving).
-/
import ZetaS.Majorant.MCert_Cells
import ZetaS.Majorant.MajCheck
import ZetaS.Cert.C05_SinCosTaylor
import ZetaS.Cert.C06_SinCosPi

open Real Finset

noncomputable section

namespace ZetaS.MajSound

open ZetaS.MCert ZetaS.MajCheck ZetaS.CertV2

/-- **The track-C node statements this certificate rests on** (C05, C06; L1_1's statements, L5_1 proving).
Every theorem below that needs them takes `CNodes` as an explicit hypothesis, so that `#print axioms` of the
`_of_CNodes` versions is level A and the `sorryAx` of the instantiated versions is exactly C05/C06. -/
structure CNodes : Prop where
  sc : ∀ x : ℚ, (sinCosPiQ x).1.Contains (Real.sin (Real.pi * x)) ∧ (sinCosPiQ x).2.Contains (Real.cos (Real.pi * x))
  sinA : sinA.Contains (Real.sin (4 / 5))
  sinT : ∀ (n : ℕ) {T : QI} {t : ℝ}, T.absMax ≤ 1 → T.Contains t → (sinQI n T).Contains (Real.sin t)
  cosT : ∀ (n : ℕ) {T : QI} {t : ℝ}, T.absMax ≤ 1 → T.Contains t → (cosQI n T).Contains (Real.cos t)

/-- the node statements, instantiated (C05 `sinQI_contains`/`cosQI_contains`, C06 `sinCosPiQ_contains`/`sinA_contains`). -/
theorem cnodes_of_statements : CNodes :=
  ⟨sinCosPiQ_contains, sinA_contains, fun n _ _ h1 h2 => sinQI_contains n h1 h2,
    fun n _ _ h1 h2 => cosQI_contains n h1 h2⟩

/-! ### 1. Third-order Taylor lower bound -/

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

/-! ### 2. P‴ and the third-order cell bound -/

/-- `P‴(s) = 2 Σ β_j (πj/30)³ sin(π j s/30)`. -/
def d3Pmaj (s : ℝ) : ℝ := 2 * ∑ j ∈ Icc 1 59, beta j * (π * (j / 30)) ^ 3 * Real.sin (π * (j * s / 30))

lemma hasDerivAt_d2Pmaj (s : ℝ) : HasDerivAt d2Pmaj (d3Pmaj s) s := by
  have hsum : HasDerivAt (fun s => ∑ j ∈ Icc 1 59, beta j * (π * (j / 30)) ^ 2 * Real.cos (π * (j * s / 30)))
      (∑ j ∈ Icc 1 59, beta j * (π * (j / 30)) ^ 2 * (-Real.sin (π * (j * s / 30)) * (π * (j / 30)))) s :=
    HasDerivAt.fun_sum fun j _ => ((hasDerivAt_arg j s).cos).const_mul (beta j * (π * (j / 30)) ^ 2)
  have h := hsum.const_mul (-2)
  unfold d2Pmaj d3Pmaj
  refine h.congr_deriv ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma abs_d3Pmaj_le (s : ℝ) : |d3Pmaj s| ≤ 645 := by
  have h1 : |d3Pmaj s| ≤ 2 * ∑ j ∈ Icc 1 59, |beta j| * (π * (j / 30)) ^ 3 := by
    unfold d3Pmaj
    rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ π * (j / 30)) 3)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  refine h1.trans ?_
  have hπ : π < 3.1416 := Real.pi_lt_d4
  have h : 2 * ∑ j ∈ Icc 1 59, |beta j| * (π * (j / 30)) ^ 3 ≤
      2 * ∑ j ∈ Icc 1 59, |beta j| * ((3.1416 : ℝ) * (j / 30)) ^ 3 := by
    gcongr with j hj
    all_goals first | exact hπ.le | positivity
  refine h.trans ?_
  rw [show Finset.Icc 1 59 = Finset.Ico 1 60 by rfl, Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, beta]
  norm_num [betaQ, abs_div]

/-- the third-order cell bound. -/
lemma Pmaj_cell3 (m r s : ℝ) (hs : |s - m| ≤ r) :
    Pmaj m - |dPmaj m| * r + min 0 (d2Pmaj m) * r ^ 2 / 2 - 645 / 6 * r ^ 3 ≤ Pmaj s := by
  have h := taylor3 hasDerivAt_Pmaj hasDerivAt_dPmaj hasDerivAt_d2Pmaj abs_d3Pmaj_le m s
  have hr : 0 ≤ r := le_trans (abs_nonneg _) hs
  have e1 : -(|dPmaj m| * r) ≤ dPmaj m * (s - m) := by
    have : |dPmaj m * (s - m)| ≤ |dPmaj m| * r := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    linarith [neg_abs_le (dPmaj m * (s - m))]
  have hsq : (s - m) ^ 2 ≤ r ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have e2 : min 0 (d2Pmaj m) * r ^ 2 / 2 ≤ d2Pmaj m * (s - m) ^ 2 / 2 := by
    have h0 : min 0 (d2Pmaj m) ≤ 0 := min_le_left _ _
    have h1 : min 0 (d2Pmaj m) ≤ d2Pmaj m := min_le_right _ _
    nlinarith [sq_nonneg (s - m)]
  have e3 : |s - m| ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hs 3
  nlinarith

/-! ### 3. The fixed-point rotation recurrence -/

/-- the complex number of a fixed-point pair (scale 2⁻⁶⁴). -/
def toC (z : ℤ × ℤ) : ℂ := ⟨(z.1 : ℝ) / 2 ^ 64, (z.2 : ℝ) / 2 ^ 64⟩

lemma TK_eq : TK = 2 ^ 64 := by decide

lemma round_err (n : ℤ) : |((n / TK : ℤ) : ℝ) / 2 ^ 64 - (n : ℝ) / 2 ^ 128| ≤ 1 / 2 ^ 64 := by
  rw [TK_eq]
  have h1 := Int.ediv_mul_le n (show (2 : ℤ) ^ 64 ≠ 0 by positivity)
  have h2 := Int.lt_ediv_add_one_mul_self n (show (0 : ℤ) < 2 ^ 64 by positivity)
  have h1' : ((n / 2 ^ 64 : ℤ) : ℝ) * 2 ^ 64 ≤ n := by exact_mod_cast h1
  have h2' : (n : ℝ) < (((n / 2 ^ 64 : ℤ) : ℝ) + 1) * 2 ^ 64 := by exact_mod_cast h2
  set q : ℝ := ((n / 2 ^ 64 : ℤ) : ℝ)
  set N : ℝ := (n : ℝ)
  rw [abs_le]
  constructor
  · rw [show q / 2 ^ 64 - N / 2 ^ 128 = (q * 2 ^ 64 - N) / 2 ^ 128 by ring, le_div_iff₀ (by positivity)]
    norm_num at h2' ⊢; linarith
  · rw [show q / 2 ^ 64 - N / 2 ^ 128 = (q * 2 ^ 64 - N) / 2 ^ 128 by ring, div_le_iff₀ (by positivity)]
    norm_num at h1' ⊢; linarith

lemma rot_err (C1 S1 : ℤ) (z : ℤ × ℤ) : ‖toC (rot C1 S1 z) - toC z * toC (C1, S1)‖ ≤ 2 / 2 ^ 64 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (toC (rot C1 S1 z) - toC z * toC (C1, S1)).re =
      (((z.1 * C1 - z.2 * S1) / TK : ℤ) : ℝ) / 2 ^ 64 - ((z.1 * C1 - z.2 * S1 : ℤ) : ℝ) / 2 ^ 128 := by
    simp only [toC, rot, Complex.sub_re, Complex.mul_re]; push_cast; ring
  have him : (toC (rot C1 S1 z) - toC z * toC (C1, S1)).im =
      (((z.1 * S1 + z.2 * C1) / TK : ℤ) : ℝ) / 2 ^ 64 - ((z.1 * S1 + z.2 * C1 : ℤ) : ℝ) / 2 ^ 128 := by
    simp only [toC, rot, Complex.sub_im, Complex.mul_im]; push_cast; ring
  rw [hre, him]
  have := round_err (z.1 * C1 - z.2 * S1)
  have := round_err (z.1 * S1 + z.2 * C1)
  linarith

/-- the iterates z_k (z_0 = z₁ = (C₁, S₁)). -/
def zs (C1 S1 : ℤ) (k : ℕ) : ℤ × ℤ := (rot C1 S1)^[k] (C1, S1)

/-- e^{i j θ}. -/
def ue (θ : ℝ) (j : ℕ) : ℂ := Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I)

lemma err_bound (θ : ℝ) (C1 S1 : ℤ) (h0 : ‖toC (C1, S1) - ue θ 1‖ ≤ 1 / 2 ^ 56) :
    ∀ k : ℕ, k ≤ 58 → ‖toC (zs C1 S1 k) - ue θ (k + 1)‖ ≤ (k + 1) / 2 ^ 55 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [zs, Function.iterate_zero, id_eq, zero_add, Nat.cast_zero]
    refine h0.trans ?_
    norm_num
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hu : ue θ (k + 1 + 1) = ue θ (k + 1) * ue θ 1 := by
      unfold ue; rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hn1 : ‖ue θ (k + 1)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hw : ‖toC (C1, S1)‖ ≤ 1 + 1 / 2 ^ 56 := by
      have := norm_le_norm_add_norm_sub' (toC (C1, S1)) (ue θ 1)
      have hn : ‖ue θ 1‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      linarith
    have hz : zs C1 S1 (k + 1) = rot C1 S1 (zs C1 S1 k) := Function.iterate_succ_apply' _ _ _
    have hdec : toC (zs C1 S1 (k + 1)) - ue θ (k + 1 + 1) =
        (toC (rot C1 S1 (zs C1 S1 k)) - toC (zs C1 S1 k) * toC (C1, S1)) +
        (toC (zs C1 S1 k) - ue θ (k + 1)) * toC (C1, S1) + ue θ (k + 1) * (toC (C1, S1) - ue θ 1) := by
      rw [hz, hu]; ring
    rw [hdec]
    have hr := rot_err C1 S1 (zs C1 S1 k)
    have t1 := norm_add_le ((toC (rot C1 S1 (zs C1 S1 k)) - toC (zs C1 S1 k) * toC (C1, S1)) +
        (toC (zs C1 S1 k) - ue θ (k + 1)) * toC (C1, S1)) (ue θ (k + 1) * (toC (C1, S1) - ue θ 1))
    have t2 := norm_add_le (toC (rot C1 S1 (zs C1 S1 k)) - toC (zs C1 S1 k) * toC (C1, S1))
        ((toC (zs C1 S1 k) - ue θ (k + 1)) * toC (C1, S1))
    rw [norm_mul, hn1] at t1
    rw [norm_mul] at t2
    have hk' : (k : ℝ) + 1 ≤ 59 := by exact_mod_cast (show k + 1 ≤ 59 by omega)
    have t3 : ‖toC (zs C1 S1 k) - ue θ (k + 1)‖ * ‖toC (C1, S1)‖ ≤ ((k : ℝ) + 1) / 2 ^ 55 * (1 + 1 / 2 ^ 56) :=
      mul_le_mul ih' hw (norm_nonneg _) (by positivity)
    push_cast
    have : ((k : ℝ) + 1) / 2 ^ 55 * (1 + 1 / 2 ^ 56) + 2 / 2 ^ 64 + 1 / 2 ^ 56 ≤ ((k : ℝ) + 1 + 1) / 2 ^ 55 := by
      have : ((k : ℝ) + 1) / 2 ^ 55 * (1 + 1 / 2 ^ 56) = ((k : ℝ) + 1) / 2 ^ 55 + ((k : ℝ) + 1) / 2 ^ 111 := by ring
      rw [this]
      have : ((k : ℝ) + 1) / 2 ^ 111 ≤ 59 / 2 ^ 111 := by gcongr
      have : ((k : ℝ) + 1 + 1) / 2 ^ 55 = ((k : ℝ) + 1) / 2 ^ 55 + 1 / 2 ^ 55 := by ring
      rw [this]
      norm_num at *
      linarith
    linarith

/-! ### 4. The accumulator -/

lemma acc_spec (C1 S1 : ℤ) : ∀ (L : List (ℤ × ℤ × ℤ)) (z : ℤ × ℤ) (a : ℤ × ℤ × ℤ),
    acc C1 S1 L z a =
      (a.1 + ∑ k ∈ range L.length, (L.getD k (0, 0, 0)).1 * ((rot C1 S1)^[k] z).1,
       a.2.1 + ∑ k ∈ range L.length, (L.getD k (0, 0, 0)).2.1 * ((rot C1 S1)^[k] z).2,
       a.2.2 + ∑ k ∈ range L.length, (L.getD k (0, 0, 0)).2.2 * ((rot C1 S1)^[k] z).1)
  | [], z, a => by simp [acc]
  | b :: bs, z, a => by
    rw [acc, acc_spec C1 S1 bs]
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ, List.getD_cons_zero,
      Function.iterate_succ_apply, Function.iterate_zero_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

lemma trip_length : trip.length = 59 := by decide

lemma trip_spec : ∀ k < 59, ((trip.getD k (0, 0, 0)).1 : ℚ) = betaQ (k + 1) * 2 ^ 60 ∧
    (trip.getD k (0, 0, 0)).2.1 = ((k : ℤ) + 1) * (trip.getD k (0, 0, 0)).1 ∧
    (trip.getD k (0, 0, 0)).2.2 = ((k : ℤ) + 1) ^ 2 * (trip.getD k (0, 0, 0)).1 ∧
    -(2 ^ 61) ≤ (trip.getD k (0, 0, 0)).1 ∧ (trip.getD k (0, 0, 0)).1 ≤ 2 ^ 61 := by
  decide +kernel

lemma b0_eq : (b0 : ℝ) = beta 0 := by
  unfold b0 beta betaQ; norm_num

/-! ### 5. From the integer sums to P(m), P′(m), P″(m) -/

lemma qabs_eq (q : ℚ) : qabs q = |q| := by
  unfold qabs; split_ifs with h
  · rw [abs_of_neg h]
  · rw [abs_of_nonneg (not_lt.1 h)]

lemma sum_err (n : ℕ) (w x y : ℕ → ℝ) (W e : ℝ) (hw : ∀ k < n, |w k| ≤ W) (hxy : ∀ k < n, |x k - y k| ≤ e)
    (he : 0 ≤ e) :
    |∑ k ∈ range n, w k * x k - ∑ k ∈ range n, w k * y k| ≤ n * (W * e) := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ k ∈ range n, |w k * x k - w k * y k| ≤ W * e := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (hw k hk') (hxy k hk') (abs_nonneg _) ((abs_nonneg _).trans (hw k hk'))
  refine (Finset.sum_le_sum this).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma Icc_sum (f : ℕ → ℝ) : ∑ j ∈ Icc 1 59, f j = ∑ k ∈ range 59, f (k + 1) := by
  rw [show Finset.Icc 1 59 = Finset.Ico 1 60 by rfl, Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun k _ => by rw [add_comm]

lemma Pmaj_eq (m : ℝ) : Pmaj m =
    beta 0 + 2 * ∑ k ∈ range 59, beta (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * (π * (m / 30))) := by
  unfold Pmaj; rw [Icc_sum]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2; push_cast; ring

lemma dPmaj_eq (m : ℝ) : dPmaj m =
    -(π / 15) * ∑ k ∈ range 59, ((k + 1 : ℕ) * beta (k + 1)) * Real.sin (((k + 1 : ℕ) : ℝ) * (π * (m / 30))) := by
  unfold dPmaj; rw [Icc_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show π * (((k + 1 : ℕ) : ℝ) * m / 30) = ((k + 1 : ℕ) : ℝ) * (π * (m / 30)) by ring]
  ring

lemma d2Pmaj_eq (m : ℝ) : d2Pmaj m =
    -(π ^ 2 / 450) * ∑ k ∈ range 59, ((k + 1 : ℕ) ^ 2 * beta (k + 1)) *
      Real.cos (((k + 1 : ℕ) : ℝ) * (π * (m / 30))) := by
  unfold d2Pmaj; rw [Icc_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show π * (((k + 1 : ℕ) : ℝ) * m / 30) = ((k + 1 : ℕ) : ℝ) * (π * (m / 30)) by ring]
  ring

/-- the real content of one trip entry. -/
lemma trip_real (k : ℕ) (hk : k < 59) :
    ((trip.getD k (0, 0, 0)).1 : ℝ) = beta (k + 1) * 2 ^ 60 ∧
    ((trip.getD k (0, 0, 0)).2.1 : ℝ) = ((k + 1 : ℕ) : ℝ) * (beta (k + 1) * 2 ^ 60) ∧
    ((trip.getD k (0, 0, 0)).2.2 : ℝ) = ((k + 1 : ℕ) : ℝ) ^ 2 * (beta (k + 1) * 2 ^ 60) ∧
    |beta (k + 1)| ≤ 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := trip_spec k hk
  have e1 : ((trip.getD k (0, 0, 0)).1 : ℝ) = beta (k + 1) * 2 ^ 60 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at this
    unfold beta; exact this
  refine ⟨e1, ?_, ?_, ?_⟩
  · rw [h2]; push_cast; rw [e1]
  · rw [h3]; push_cast; rw [e1]
  · have h4' : (-(2 : ℝ) ^ 61) ≤ ((trip.getD k (0, 0, 0)).1 : ℝ) := by exact_mod_cast h4
    have h5' : ((trip.getD k (0, 0, 0)).1 : ℝ) ≤ 2 ^ 61 := by exact_mod_cast h5
    rw [e1] at h4' h5'
    rw [abs_le]; constructor <;> nlinarith

/-- **the three sums, rigorously**: at θ = π m/30, from a start with error ≤ 2⁻⁵⁶. -/
lemma sums_sound (m : ℝ) (C1 S1 : ℤ)
    (h0 : ‖toC (C1, S1) - ue (π * (m / 30)) 1‖ ≤ 1 / 2 ^ 56) :
    let a := acc C1 S1 trip (C1, S1) (0, 0, 0)
    |Pmaj m - (beta 0 + 2 * ((a.1 : ℝ) / 2 ^ 124))| ≤ 236 / 2 ^ 49 ∧
    |dPmaj m| ≤ π / 15 * (|(a.2.1 : ℝ) / 2 ^ 124| + 6962 / 2 ^ 49) ∧
    min 0 (d2Pmaj m) ≥ -(π ^ 2 / 450) * max 0 ((a.2.2 : ℝ) / 2 ^ 124 + 410758 / 2 ^ 49) ∧
    ∃ T : ℝ, dPmaj m = -(π / 15) * T ∧ |T - (a.2.1 : ℝ) / 2 ^ 124| ≤ 6962 / 2 ^ 49 := by
  intro a
  set θ := π * (m / 30) with hθ
  have herr := err_bound θ C1 S1 h0
  have hc : ∀ k < 59, |((zs C1 S1 k).1 : ℝ) / 2 ^ 64 - Real.cos (((k + 1 : ℕ) : ℝ) * θ)| ≤ 1 / 2 ^ 49 := by
    intro k hk
    have e := herr k (by omega)
    have hre := Complex.abs_re_le_norm (toC (zs C1 S1 k) - ue θ (k + 1))
    rw [Complex.sub_re, ue, Complex.exp_ofReal_mul_I_re] at hre
    have hk' : ((k : ℝ) + 1) / 2 ^ 55 ≤ 1 / 2 ^ 49 := by
      have : (k : ℝ) + 1 ≤ 59 := by exact_mod_cast (show k + 1 ≤ 59 by omega)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; norm_num; linarith
    exact (hre.trans e).trans (by push_cast at hk' ⊢; exact hk')
  have hs : ∀ k < 59, |((zs C1 S1 k).2 : ℝ) / 2 ^ 64 - Real.sin (((k + 1 : ℕ) : ℝ) * θ)| ≤ 1 / 2 ^ 49 := by
    intro k hk
    have e := herr k (by omega)
    have him := Complex.abs_im_le_norm (toC (zs C1 S1 k) - ue θ (k + 1))
    rw [Complex.sub_im, ue, Complex.exp_ofReal_mul_I_im] at him
    have hk' : ((k : ℝ) + 1) / 2 ^ 55 ≤ 1 / 2 ^ 49 := by
      have : (k : ℝ) + 1 ≤ 59 := by exact_mod_cast (show k + 1 ≤ 59 by omega)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; norm_num; linarith
    exact (him.trans e).trans (by push_cast at hk' ⊢; exact hk')
  have ha := acc_spec C1 S1 trip (C1, S1) (0, 0, 0)
  rw [trip_length] at ha
  have hA0 : (a.1 : ℝ) / 2 ^ 124 = ∑ k ∈ range 59, beta (k + 1) * (((zs C1 S1 k).1 : ℝ) / 2 ^ 64) := by
    show ((acc C1 S1 trip (C1, S1) (0, 0, 0)).1 : ℝ) / 2 ^ 124 = _
    rw [ha]; simp only [zero_add]; push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [(trip_real k (Finset.mem_range.1 hk)).1]; unfold zs; ring
  have hA1 : (a.2.1 : ℝ) / 2 ^ 124 =
      ∑ k ∈ range 59, ((k + 1 : ℕ) * beta (k + 1)) * (((zs C1 S1 k).2 : ℝ) / 2 ^ 64) := by
    show ((acc C1 S1 trip (C1, S1) (0, 0, 0)).2.1 : ℝ) / 2 ^ 124 = _
    rw [ha]; simp only [zero_add]; push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := (trip_real k (Finset.mem_range.1 hk)).2.1
    push_cast at this
    rw [this]; unfold zs; ring
  have hA2 : (a.2.2 : ℝ) / 2 ^ 124 =
      ∑ k ∈ range 59, ((k + 1 : ℕ) ^ 2 * beta (k + 1)) * (((zs C1 S1 k).1 : ℝ) / 2 ^ 64) := by
    show ((acc C1 S1 trip (C1, S1) (0, 0, 0)).2.2 : ℝ) / 2 ^ 124 = _
    rw [ha]; simp only [zero_add]; push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := (trip_real k (Finset.mem_range.1 hk)).2.2.1
    push_cast at this
    rw [this]; unfold zs; ring
  have hb : ∀ k < 59, |beta (k + 1)| ≤ 2 := fun k hk => (trip_real k hk).2.2.2
  have hδ : (0 : ℝ) ≤ 1 / 2 ^ 49 := by positivity
  -- the three errors
  have E0 := sum_err 59 (fun k => beta (k + 1)) (fun k => ((zs C1 S1 k).1 : ℝ) / 2 ^ 64)
    (fun k => Real.cos (((k + 1 : ℕ) : ℝ) * θ)) 2 (1 / 2 ^ 49) hb hc hδ
  have E1 := sum_err 59 (fun k => (k + 1 : ℕ) * beta (k + 1)) (fun k => ((zs C1 S1 k).2 : ℝ) / 2 ^ 64)
    (fun k => Real.sin (((k + 1 : ℕ) : ℝ) * θ)) 118 (1 / 2 ^ 49)
    (fun k hk => by
      rw [abs_mul, Nat.abs_cast]
      have : ((k + 1 : ℕ) : ℝ) ≤ 59 := by exact_mod_cast (show k + 1 ≤ 59 by omega)
      nlinarith [hb k hk, abs_nonneg (beta (k + 1))]) hs hδ
  have E2 := sum_err 59 (fun k => (k + 1 : ℕ) ^ 2 * beta (k + 1)) (fun k => ((zs C1 S1 k).1 : ℝ) / 2 ^ 64)
    (fun k => Real.cos (((k + 1 : ℕ) : ℝ) * θ)) 6962 (1 / 2 ^ 49)
    (fun k hk => by
      rw [abs_mul, abs_pow, Nat.abs_cast]
      have h59 : ((k + 1 : ℕ) : ℝ) ≤ 59 := by exact_mod_cast (show k + 1 ≤ 59 by omega)
      have hsq : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 3481 := by nlinarith [Nat.cast_nonneg (α := ℝ) (k + 1)]
      nlinarith [hb k hk, abs_nonneg (beta (k + 1)), sq_nonneg ((k + 1 : ℕ) : ℝ)]) hc hδ
  try simp only at E0 E1 E2
  rw [← hA0] at E0; rw [← hA1] at E1; rw [← hA2] at E2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Pmaj_eq]
    rw [abs_sub_comm] at E0
    have : |beta 0 + 2 * ∑ k ∈ range 59, beta (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ) -
        (beta 0 + 2 * ((a.1 : ℝ) / 2 ^ 124))| =
        2 * |∑ k ∈ range 59, beta (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ) - (a.1 : ℝ) / 2 ^ 124| := by
      rw [← abs_two, ← abs_mul]; congr 1; ring
    rw [this]; norm_num at E0 ⊢; linarith
  · rw [dPmaj_eq, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < π / 15)]
    gcongr
    have := abs_sub_abs_le_abs_sub (∑ k ∈ range 59, ((k + 1 : ℕ) * beta (k + 1)) *
      Real.sin (((k + 1 : ℕ) : ℝ) * θ)) ((a.2.1 : ℝ) / 2 ^ 124)
    rw [abs_sub_comm] at E1
    have h59 : ((59 : ℕ) : ℝ) * (118 * (1 / 2 ^ 49)) = 6962 / 2 ^ 49 := by norm_num
    rw [h59] at E1
    linarith
  · rw [d2Pmaj_eq]
    set T := ∑ k ∈ range 59, ((k + 1 : ℕ) ^ 2 * beta (k + 1)) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)
    have hT : T ≤ (a.2.2 : ℝ) / 2 ^ 124 + 410758 / 2 ^ 49 := by
      rw [abs_sub_comm] at E2
      have := (abs_le.1 E2).2; norm_num at this ⊢; linarith
    have hp : 0 ≤ π ^ 2 / 450 := by positivity
    rcases le_total 0 T with hT0 | hT0
    · rw [min_eq_right (by nlinarith)]
      have : T ≤ max 0 ((a.2.2 : ℝ) / 2 ^ 124 + 410758 / 2 ^ 49) := le_max_of_le_right hT
      nlinarith
    · rw [min_eq_left (by nlinarith)]
      have : 0 ≤ max 0 ((a.2.2 : ℝ) / 2 ^ 124 + 410758 / 2 ^ 49) := le_max_left _ _
      nlinarith
  · refine ⟨_, dPmaj_eq m, ?_⟩
    rw [abs_sub_comm]
    have h59 : ((59 : ℕ) : ℝ) * (118 * (1 / 2 ^ 49)) = 6962 / 2 ^ 49 := by norm_num
    rw [h59] at E1
    exact E1

/-- the fixed-point start from an enclosure: |z₁ − e^{iθ}| ≤ startErr. -/
lemma start_sound (hC : CNodes) (x : ℚ) (C1 S1 : ℤ) (h : startErr (sinCosPiQ x) C1 S1 ≤ eps0) :
    ‖toC (C1, S1) - ue (π * x) 1‖ ≤ 1 / 2 ^ 56 := by
  obtain ⟨hs, hc⟩ := hC.sc x
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im, ue, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp only [Nat.cast_one, one_mul]
  have h' : ((startErr (sinCosPiQ x) C1 S1 : ℚ) : ℝ) ≤ ((eps0 : ℚ) : ℝ) := by exact_mod_cast h
  unfold startErr at h'
  unfold eps0 sc64 at h'
  push_cast at h'
  unfold QI.Contains at hs hc
  have hre : |(toC (C1, S1)).re - Real.cos (π * x)| ≤
      max (((sinCosPiQ x).2.hi : ℝ) - (C1 : ℝ) / 18446744073709551616)
        ((C1 : ℝ) / 18446744073709551616 - ((sinCosPiQ x).2.lo : ℝ)) := by
    show |(C1 : ℝ) / 2 ^ 64 - Real.cos (π * x)| ≤ _
    rw [show (2 : ℝ) ^ 64 = 18446744073709551616 by norm_num, abs_le]
    have m1 := le_max_left (((sinCosPiQ x).2.hi : ℝ) - (C1 : ℝ) / 18446744073709551616)
      ((C1 : ℝ) / 18446744073709551616 - ((sinCosPiQ x).2.lo : ℝ))
    have m2 := le_max_right (((sinCosPiQ x).2.hi : ℝ) - (C1 : ℝ) / 18446744073709551616)
      ((C1 : ℝ) / 18446744073709551616 - ((sinCosPiQ x).2.lo : ℝ))
    constructor
    · linarith [hc.2]
    · linarith [hc.1]
  have him : |(toC (C1, S1)).im - Real.sin (π * x)| ≤
      max (((sinCosPiQ x).1.hi : ℝ) - (S1 : ℝ) / 18446744073709551616)
        ((S1 : ℝ) / 18446744073709551616 - ((sinCosPiQ x).1.lo : ℝ)) := by
    show |(S1 : ℝ) / 2 ^ 64 - Real.sin (π * x)| ≤ _
    rw [show (2 : ℝ) ^ 64 = 18446744073709551616 by norm_num, abs_le]
    have m1 := le_max_left (((sinCosPiQ x).1.hi : ℝ) - (S1 : ℝ) / 18446744073709551616)
      ((S1 : ℝ) / 18446744073709551616 - ((sinCosPiQ x).1.lo : ℝ))
    have m2 := le_max_right (((sinCosPiQ x).1.hi : ℝ) - (S1 : ℝ) / 18446744073709551616)
      ((S1 : ℝ) / 18446744073709551616 - ((sinCosPiQ x).1.lo : ℝ))
    constructor
    · linarith [hs.2]
    · linarith [hs.1]
  norm_num at h' ⊢
  linarith

/-- **soundness of one NPos cell** (checker core). -/
theorem cellCore_sound (hC : CNodes) (mq rq : ℚ) (C1 S1 : ℤ)
    (h : cellCore (sinCosPiQ (mq / 30)) C1 S1 rq = true) (s : ℝ) (hs : |s - (mq : ℝ)| ≤ (rq : ℝ)) :
    0 ≤ Pmaj s := by
  unfold cellCore at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hst, hlb⟩ := h
  have h0 := start_sound hC (mq / 30) C1 S1 hst
  push_cast at h0
  obtain ⟨E0, E1, E2, -⟩ := sums_sound (mq : ℝ) C1 S1 h0
  set a := acc C1 S1 trip (C1, S1) (0, 0, 0)
  unfold lbOk at hlb
  rw [decide_eq_true_eq] at hlb
  have hlb' := (Rat.cast_le (K := ℝ)).2 hlb
  have hsc : ((sc124 : ℚ) : ℝ) = 1 / 2 ^ 124 := by unfold sc124; norm_num
  have hdl : ((dlt : ℚ) : ℝ) = 1 / 2 ^ 49 := by unfold dlt; norm_num
  have hpi : ((piHi : ℚ) : ℝ) = 31416 / 10000 := by unfold piHi; norm_num
  rw [qabs_eq] at hlb'
  push_cast at hlb'
  rw [hsc, hdl, hpi, b0_eq] at hlb'
  simp only [mul_one_div] at hlb'
  have hr : (0 : ℝ) ≤ rq := le_trans (abs_nonneg _) hs
  have hcell := Pmaj_cell3 (mq : ℝ) (rq : ℝ) s hs
  have hπ : π < 3.1416 := Real.pi_lt_d4
  have hπ0 : 0 < π := Real.pi_pos
  have hP : beta 0 + 2 * ((a.1 : ℝ) / 2 ^ 124) - 236 / 2 ^ 49 ≤ Pmaj (mq : ℝ) := by linarith [(abs_le.1 E0).1]
  have hD : |dPmaj (mq : ℝ)| * (rq : ℝ) ≤
      31416 / 10000 / 15 * (|(a.2.1 : ℝ) / 2 ^ 124| + 6962 / 2 ^ 49) * (rq : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hr
    refine E1.trans ?_
    gcongr
    linarith
  have hM : 0 ≤ max 0 ((a.2.2 : ℝ) / 2 ^ 124 + 410758 / 2 ^ 49) := le_max_left _ _
  have hD2 : -(31416 / 10000 * (31416 / 10000) / 900 * max 0 ((a.2.2 : ℝ) / 2 ^ 124 + 410758 / 2 ^ 49) *
      (rq : ℝ) * (rq : ℝ)) ≤ min 0 (d2Pmaj (mq : ℝ)) * (rq : ℝ) ^ 2 / 2 := by
    have hpp : π ^ 2 ≤ 31416 / 10000 * (31416 / 10000) := by nlinarith
    have h3 : -(31416 / 10000 * (31416 / 10000) / 450) * max 0 ((a.2.2 : ℝ) / 2 ^ 124 + 410758 / 2 ^ 49) ≤
        min 0 (d2Pmaj (mq : ℝ)) := by
      refine le_trans ?_ (ge_iff_le.1 E2)
      have := mul_le_mul_of_nonneg_right hpp hM
      nlinarith
    have hr2 : 0 ≤ (rq : ℝ) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right h3 hr2
    nlinarith
  have key : 0 ≤ Pmaj (mq : ℝ) - |dPmaj (mq : ℝ)| * (rq : ℝ) + min 0 (d2Pmaj (mq : ℝ)) * (rq : ℝ) ^ 2 / 2 -
      645 / 6 * (rq : ℝ) ^ 3 := by
    have : (rq : ℝ) ^ 3 = (rq : ℝ) * (rq : ℝ) * (rq : ℝ) := by ring
    rw [this]
    linarith
  linarith

/-- **soundness of one NPos cell** `[A/2²⁴, B/2²⁴]`. -/
theorem cellOk_sound (hC : CNodes) (A B : ℕ) (h : MajCheck.cellOk A B = true) (s : ℝ) (h1 : (A : ℝ) / 2 ^ 24 ≤ s)
    (h2 : s ≤ (B : ℝ) / 2 ^ 24) : 0 ≤ Pmaj s := by
  have hAB : A ≤ B := by
    have : (A : ℝ) ≤ B := by
      have := h1.trans h2
      rwa [div_le_div_iff_of_pos_right (by positivity)] at this
    exact_mod_cast this
  unfold MajCheck.cellOk at h
  refine cellCore_sound hC _ _ _ _ h s ?_
  push_cast [Nat.cast_sub hAB]
  norm_num at h1 h2 ⊢
  rw [abs_le]; constructor <;> linarith

/-- a chain of breakpoints. -/
def lastD : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, b :: rest => lastD b rest

theorem chainOk_sound (hC : CNodes) : ∀ (a b : ℕ) (rest : List ℕ), MajCheck.chainOk (a :: b :: rest) = true →
    ∀ s : ℝ, (a : ℝ) / 2 ^ 24 ≤ s → s ≤ (lastD b rest : ℝ) / 2 ^ 24 → 0 ≤ Pmaj s
  | a, b, [], h, s, h1, h2 => by
    have h' : (MajCheck.cellOk a b && MajCheck.chainOk [b]) = true := h
    rw [Bool.and_eq_true] at h'
    exact cellOk_sound hC a b h'.1 s h1 h2
  | a, b, c :: rest, h, s, h1, h2 => by
    have h' : (MajCheck.cellOk a b && MajCheck.chainOk (b :: c :: rest)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases le_total s ((b : ℝ) / 2 ^ 24) with hs | hs
    · exact cellOk_sound hC a b h'.1 s h1 hs
    · exact chainOk_sound hC b c rest h'.2 s hs h2

end ZetaS.MajSound
