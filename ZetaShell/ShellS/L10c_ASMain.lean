/-
L10c_ASMain (L7_10c, 3 Oct 2026): **`AS_pointwise_corr`**, node AS (eq:shell-assembly at `K = ℒ(log ℒ)²`, `ε = 1/ℒ`)
with the hypothesis `αpp < lam` added (SCR-AS, report L7_10 R2.4): `AS_point` (one `(Q, s)`) at `T = (log Q)^{r₀+ε₀}`,
with the eventual scalar facts (`scalars_AS`), Lemma 2(a) (`lemma2a_upper`, sharp family), K6 (`principal_arc_mass`)
and the medium PNT (`theta_pnt`). Statement = `Skeleton/L10_AS.lean`'s `AS_pointwise` plus `(hαl : αpp < lam)`.
-/
import ZetaShell.ShellS.L10c_ASPoint

noncomputable section
open scoped BigOperators Chebyshev
open Filter

namespace ZetaShell
namespace ShellS
namespace ASc

/-- `a + b log y ≤ c y` eventually (`c > 0`). -/
theorem ev_log_lin (a b c : ℝ) (hc : 0 < c) : ∀ᶠ y : ℝ in atTop, a + b * Real.log y ≤ c * y := by
  have hε : 0 < c / (2 * (|b| + 1)) := by positivity
  have h1 := Real.isLittleO_log_id_atTop.def hε
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 * |a| / c)] with y h1 hy1 hy2
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have h1' : Real.log y ≤ c / (2 * (|b| + 1)) * y := by
    have e1 : ‖Real.log y‖ = Real.log y := by rw [Real.norm_eq_abs, abs_of_nonneg hlog0]
    have e2 : ‖id y‖ = y := by rw [id, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [e1, e2] at h1; exact h1
  have hb : b * Real.log y ≤ (|b| + 1) * Real.log y :=
    mul_le_mul_of_nonneg_right (by have := le_abs_self b; linarith) hlog0
  have hb2 : (|b| + 1) * Real.log y ≤ c / 2 * y := by
    have := mul_le_mul_of_nonneg_left h1' (by positivity : (0 : ℝ) ≤ |b| + 1)
    have e : (|b| + 1) * (c / (2 * (|b| + 1)) * y) = c / 2 * y := by field_simp
    linarith
  have ha : a ≤ c / 2 * y := by
    have h2 : 2 * |a| ≤ c * y := by rw [div_le_iff₀ hc] at hy2; linarith
    have := le_abs_self a
    linarith
  linarith

/-- the eventual scalar facts of AS in `y = log Q` (with `p = r₀ + ε₀`, `ℒ = y + p log y − log 2π`). -/
theorem scalars_AS_y (p lam αpp M x₀ : ℝ) (hp : 3 < p) (hl1 : 1 < lam) (hl2 : lam < 2) (hαl : αpp < lam) :
    ∀ᶠ y : ℝ in atTop, 100 ≤ y ∧ y ≤ y + p * Real.log y - Real.log (2 * Real.pi) ∧
      y + p * Real.log y - Real.log (2 * Real.pi) ≤ 2 * y ∧ 1 ≤ (lam - αpp) * y ∧
      Real.log Real.pi + lam * (y + p * Real.log y - Real.log (2 * Real.pi)) ≤ 2 * y ∧
      Real.log 32 + αpp * y + 14 * Real.log y ≤ 2 * y ∧ (4 + 4 * p) * Real.log y ≤ y ∧
      M ≤ y ^ (p - 3) ∧ x₀ ≤ y := by
  have hpi := Real.pi_pos
  have h2pi : 0 < Real.log (2 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  filter_upwards [eventually_ge_atTop (100 : ℝ), eventually_ge_atTop (2 * Real.pi),
    ev_log_lin 0 p 1 one_pos, eventually_ge_atTop (1 / (lam - αpp)),
    ev_log_lin (Real.log Real.pi) (2 * p) (2 - lam) (by linarith),
    ev_log_lin (Real.log 32) 14 (2 - αpp) (by linarith), ev_log_lin 0 (4 + 4 * p) 1 one_pos,
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < p - 3)).eventually_ge_atTop M,
    eventually_ge_atTop x₀] with y h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hy0 : 0 < y := by linarith
  have hlogy : Real.log (2 * Real.pi) ≤ Real.log y := Real.log_le_log (by positivity) h2
  have hlog0 : 0 ≤ Real.log y := by linarith
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · have : Real.log y ≤ p * Real.log y := le_mul_of_one_le_left hlog0 (by linarith)
    linarith
  · linarith
  · rw [div_le_iff₀ (by linarith)] at h4; linarith
  · have e : lam * (y + p * Real.log y - Real.log (2 * Real.pi))
        = lam * y + lam * p * Real.log y - lam * Real.log (2 * Real.pi) := by ring
    have hlp : lam * p * Real.log y ≤ 2 * p * Real.log y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl2.le (by linarith)) hlog0
    have hl2pi : 0 ≤ lam * Real.log (2 * Real.pi) := by positivity
    rw [e]; nlinarith
  · linarith
  · linarith

/-- the eventual scalar facts of AS in `Q`. -/
theorem scalars_AS (r0 ε0 lam αpp M x₀ Q0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (hl1 : 1 < lam) (hl2 : lam < 2)
    (hαl : αpp < lam) :
    ∀ᶠ Q : ℕ in atTop, Q0 ≤ Q ∧ 100 ≤ Real.log Q ∧ 1 ≤ twin Q r0 ε0 ∧
      Real.log Q ≤ LcS Q (twin Q r0 ε0) ∧ LcS Q (twin Q r0 ε0) ≤ 2 * Real.log Q ∧
      1 ≤ Real.log (LcS Q (twin Q r0 ε0)) ∧ 1 ≤ (lam - αpp) * Real.log Q ∧
      Real.pi * XlamS lam Q (twin Q r0 ε0) ≤ (Q : ℝ) ^ 2 ∧
      32 * Real.exp (αpp * Real.log Q) * Real.log Q ^ 14 ≤ (Q : ℝ) ^ 2 ∧
      Real.log Q ^ 4 * twin Q r0 ε0 ^ 4 ≤ Q ∧ M * Real.log Q ^ 3 ≤ twin Q r0 ε0 ∧ x₀ ≤ Real.log Q ∧
      6 * (1 + Real.log Q) ^ 2 ≤ (18 / Real.pi ^ 4 - 1 / 6) * Q := by
  set p := r0 + ε0 with hp
  have hp3 : 3 < p := by linarith
  have hpi4 : 0 < 18 / Real.pi ^ 4 - 1 / 6 := by
    have h1 : Real.pi ^ 4 < 3.15 ^ 4 := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
    have h2 : 0 < Real.pi ^ 4 := by positivity
    rw [sub_pos, lt_div_iff₀ h2]; nlinarith
  have hQ : ∀ᶠ x : ℝ in atTop, 6 * (1 + Real.log x) ^ 2 ≤ (18 / Real.pi ^ 4 - 1 / 6) * x := by
    have hsq := (Real.isLittleO_pow_log_id_atTop (n := 2)).def
      (by positivity : (0 : ℝ) < (18 / Real.pi ^ 4 - 1 / 6) / 24)
    filter_upwards [hsq, eventually_ge_atTop (Real.exp 1)] with x h1 h2
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) h2
    have hl1 : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact h2
    have h1' : Real.log x ^ 2 ≤ (18 / Real.pi ^ 4 - 1 / 6) / 24 * x := by
      have e1 : ‖Real.log x ^ 2‖ = Real.log x ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith) 2)]
      have e2 : ‖id x‖ = x := by rw [id, Real.norm_eq_abs, abs_of_nonneg hx0.le]
      rw [e1, e2] at h1; exact h1
    have e : (1 + Real.log x) ^ 2 ≤ 4 * Real.log x ^ 2 := by nlinarith
    have : 6 * (4 * Real.log x ^ 2) ≤ (18 / Real.pi ^ 4 - 1 / 6) * x := by
      have := mul_le_mul_of_nonneg_left h1' (by norm_num : (0 : ℝ) ≤ 24)
      have e2 : 24 * ((18 / Real.pi ^ 4 - 1 / 6) / 24 * x) = (18 / Real.pi ^ 4 - 1 / 6) * x := by ring
      linarith
    linarith
  filter_upwards [ZetaQ.tendsto_log_nat_atTop.eventually (scalars_AS_y p lam αpp M x₀ hp3 hl1 hl2 hαl),
    tendsto_natCast_atTop_atTop.eventually hQ, tendsto_natCast_atTop_atTop.eventually_ge_atTop Q0]
    with Q hy hQx hQ0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hy
  have hpi := Real.pi_pos
  set y := Real.log (Q : ℝ) with hydef
  have hy0 : 0 < y := by linarith
  have hQ0' : (0 : ℝ) < Q := by
    by_contra h; push Not at h
    have : y ≤ 0 := Real.log_nonpos (Nat.cast_nonneg Q) (by linarith)
    linarith
  have hQexp : Real.exp y = Q := Real.exp_log hQ0'
  have hT : twin Q r0 ε0 = y ^ p := rfl
  have hT0 : 0 < twin Q r0 ε0 := by rw [hT]; positivity
  have hlogT : Real.log (twin Q r0 ε0) = p * Real.log y := by rw [hT, Real.log_rpow hy0]
  have hL : LcS Q (twin Q r0 ε0) = y + p * Real.log y - Real.log (2 * Real.pi) := by
    unfold LcS
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hQ0'.ne' hT0.ne', hlogT]
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  refine ⟨hQ0, h1, ?_, ?_, ?_, ?_, h4, ?_, ?_, ?_, ?_, h9, hQx⟩
  · rw [hT]; exact Real.one_le_rpow (by linarith) (by linarith)
  · rw [hL]; exact h2
  · rw [hL]; exact h3
  · rw [hL]
    have : (1 : ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_le_log (by norm_num) (le_trans h1 h2)
    linarith
  · -- `π X ≤ Q²`
    have e : (Q : ℝ) ^ 2 = Real.exp (2 * y) := by rw [← hQexp, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e]; unfold XlamS; rw [hL]
    have e2 : Real.pi = Real.exp (Real.log Real.pi) := (Real.exp_log hpi).symm
    rw [e2, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by rw [← e2]; linarith)
  · have e : (Q : ℝ) ^ 2 = Real.exp (2 * y) := by rw [← hQexp, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e]
    have e2 : 32 * Real.exp (αpp * y) * y ^ 14 = Real.exp (Real.log 32 + αpp * y + 14 * Real.log y) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
      have : Real.exp (14 * Real.log y) = y ^ 14 := by
        rw [show (14 : ℝ) * Real.log y = ((14 : ℕ) : ℝ) * Real.log y by norm_num, ← Real.log_pow,
          Real.exp_log (by positivity)]
      rw [this]
    rw [e2]; exact Real.exp_le_exp.mpr h6
  · have e2 : y ^ 4 * twin Q r0 ε0 ^ 4 = Real.exp ((4 + 4 * p) * Real.log y) := by
      rw [show (4 + 4 * p) * Real.log y = ((4 : ℕ) : ℝ) * Real.log y + ((4 : ℕ) : ℝ) * (p * Real.log y) by
          push_cast; ring, Real.exp_add,
        ← hlogT, ← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity)]
    rw [e2, ← hQexp]; exact Real.exp_le_exp.mpr h7
  · rw [hT]
    have e : y ^ p = y ^ (p - 3) * y ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; congr 1; push_cast; ring
    rw [e]; exact mul_le_mul_of_nonneg_right h8 (by positivity)

open TrackF in
/-- **AS, corrected** (`AS_pointwise` + `αpp < lam`). -/
theorem AS_pointwise_corr' (lam : ℝ) (hl1 : 1 < lam) (hl2 : lam < 2) (αpp : ℝ) (hαpp : αpp < 2)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : PropZ.NearCutoff Ξ) (c : ℝ) (hc : 0 < c)
    (hΞc : ∀ z, |z| ≤ c → Ξ z = 1) (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (hαl : αpp < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ s : ℝ, Real.log Qn + 4 ≤ s → s ≤ αpp * Real.log Qn →
      TrackF.famF (Finset.Icc 2 Qn) ⌊XlamS lam Qn (twin Qn r0 ε0)⌋₊ (TrackF.acoefS (twin Qn r0 ε0) s)
        ≤ famSize Qn * (twin Qn r0 ε0 / (2 * Real.pi))
            * (LcS Qn (twin Qn r0 ε0) + Real.log (Kstd Qn (twin Qn r0 ε0)) + C)
          + (Qn : ℝ) ^ 2 * (1 + C * (Real.log (LcS Qn (twin Qn r0 ε0)) / LcS Qn (twin Qn r0 ε0)))
            * RingS Qn (twin Qn r0 ε0) κ Ξ (Kstd Qn (twin Qn r0 ε0)) (1 / LcS Qn (twin Qn r0 ε0)) (s - 1) s
          + C * (Real.log (LcS Qn (twin Qn r0 ε0)) / LcS Qn (twin Qn r0 ε0)) * famSize Qn
            * l2S ⌊XlamS lam Qn (twin Qn r0 ε0)⌋₊ (twin Qn r0 ε0) s := by
  obtain ⟨B₂, Q0, hB₂, h2a⟩ := lemma2a_upper .sharp
  obtain ⟨C₆, hK6ev⟩ := LemmaK.principal_arc_mass lam r0 ε0 hl1 hl2 hr0 hε0
  set A : ℝ := 3 * (r0 + ε0) + 1 with hA
  obtain ⟨x₀, hx₀3, hpnt⟩ := ShellK.F1c.theta_pnt A
  refine ⟨Cas B₂ C₆, Cas_nonneg B₂ C₆ hB₂, ?_⟩
  filter_upwards [hK6ev, scalars_AS r0 ε0 lam αpp (4 * Real.pi * (Cf (min c 1 * κ) + 1)) x₀ Q0 hr0 hε0 hl1 hl2 hαl]
    with Q hK6 hsc
  obtain ⟨hQ0, hy100, hT1, hyL, hL2, hlogL, hlα, hX, hsm, hyT, hM, hx0, hQx⟩ := hsc
  intro s hs1 hs2
  have hpi := Real.pi_pos
  have hy0 : 0 < Real.log Q := by linarith
  have hQ0' : (0 : ℝ) < Q := by
    by_contra h; push Not at h
    have : Real.log Q ≤ 0 := Real.log_nonpos (Nat.cast_nonneg Q) (by linarith)
    linarith
  have hs2' : s ≤ 2 * Real.log Q := by
    have := mul_le_mul_of_nonneg_right hαpp.le hy0.le; linarith
  have hsl : s + 1 ≤ lam * LcS Q (twin Q r0 ε0) := by
    have h1 : lam * Real.log Q ≤ lam * LcS Q (twin Q r0 ε0) := mul_le_mul_of_nonneg_left hyL (by linarith)
    have e : (lam - αpp) * Real.log Q = lam * Real.log Q - αpp * Real.log Q := by ring
    linarith
  have hsmall : 32 * Real.exp s * Real.log Q ^ 14 ≤ (Q : ℝ) ^ 2 := by
    have : Real.exp s ≤ Real.exp (αpp * Real.log Q) := Real.exp_le_exp.mpr hs2
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 32))
      (by positivity : (0 : ℝ) ≤ Real.log Q ^ 14)
    linarith
  have hUbig : 2 * (Cf (min c 1 * κ) + 1) * Real.log Q ^ 3 ≤ twin Q r0 ε0 / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    have e : 2 * (Cf (min c 1 * κ) + 1) * Real.log Q ^ 3 * (2 * Real.pi)
        = 4 * Real.pi * (Cf (min c 1 * κ) + 1) * Real.log Q ^ 3 := by ring
    rw [e]; exact hM
  have hHw : (Q : ℝ) ^ 2 / 6 ≤ famSize Q := by
    have hQ1 : 1 ≤ Q := by
      by_contra h; push Not at h
      have : Q = 0 := by omega
      rw [this] at hQ0'; simp at hQ0'
    have h1 := ZetaQ.sizeR_qle_lower' Q hQ1
    have h2 : famSize Q = ZetaQ.Family.qle.sizeR Q := by
      unfold famSize ZetaQ.Family.sizeR ZetaQ.Family.size
      push_cast
      rfl
    have h3 : 6 * (Q : ℝ) * (1 + Real.log Q) ^ 2 ≤ (18 / Real.pi ^ 4 - 1 / 6) * Q * Q := by
      have := mul_le_mul_of_nonneg_left hQx hQ0'.le
      nlinarith
    rw [h2]; nlinarith
  -- PNT on the window
  have hθ : ∀ k : ℕ, Real.exp (s - 1) - 1 ≤ k → (k : ℝ) ≤ Real.exp (s + 1) →
      |θ (k : ℝ) - k| ≤ Real.log Q ^ (-A) * k := by
    intro k hk1 _
    have hey : Real.exp (Real.log Q) ≤ Real.exp (s - 1) - 1 := by
      have h1 : Real.exp (Real.log Q + 3) ≤ Real.exp (s - 1) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (Real.log Q + 3) = Real.exp (Real.log Q) * Real.exp 3 := Real.exp_add _ _
      have h3 : (4 : ℝ) ≤ Real.exp 3 := by
        have := Real.add_one_le_exp (3 : ℝ); linarith
      have h4 : 1 ≤ Real.exp (Real.log Q) := Real.one_le_exp hy0.le
      nlinarith
    have hkQ : Real.exp (Real.log Q) ≤ k := le_trans hey hk1
    have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos _) hkQ
    have hkx : x₀ ≤ k := by
      have := Real.add_one_le_exp (Real.log Q); linarith
    have hlk : Real.log Q ≤ Real.log k := by
      have := Real.log_le_log (Real.exp_pos _) hkQ
      rwa [Real.log_exp] at this
    have h1 := hpnt k hkx
    have h2 : Real.log k ^ (-A) ≤ Real.log Q ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos hy0 hlk (by rw [hA]; linarith)
    have h3 : (k : ℝ) * Real.log k ^ (-A) ≤ k * Real.log Q ^ (-A) := mul_le_mul_of_nonneg_left h2 hk0.le
    linarith
  have h34 : 34 * Real.log Q ^ (-A) * twin Q r0 ε0 ^ 3 ≤ 1 := by
    have e : Real.log Q ^ (-A) * twin Q r0 ε0 ^ 3 = Real.log Q ^ (-1 : ℝ) := by
      have hT : twin Q r0 ε0 = Real.log Q ^ (r0 + ε0) := rfl
      rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le, ← Real.rpow_add hy0, hA]
      congr 1; push_cast; ring
    have e2 : 34 * Real.log Q ^ (-A) * twin Q r0 ε0 ^ 3 = 34 * (Real.log Q ^ (-A) * twin Q r0 ε0 ^ 3) := by
      ring
    rw [e2, e, Real.rpow_neg_one, ← div_eq_mul_inv, div_le_one hy0]
    linarith
  exact AS_point lam (by linarith) hl2 B₂ Q0 hB₂ h2a κ c Ξ hΞ hκ hκ1 hc hΞc C₆ Q (twin Q r0 ε0) s hQ0
    (by linarith) hT1 hyL hL2 hlogL hs1 hs2' hsl hX hsmall hyT hUbig (Real.log Q ^ (-A))
    (Real.rpow_nonneg hy0.le _) hθ h34 hHw (hK6 s)

end ASc

open ZetaShell.PropZ

/-- **AS, corrected** (statement of `Skeleton/L10_AS.lean`'s `AS_pointwise` plus `(hαl : αpp < lam)`). -/
theorem AS_pointwise_corr (lam : ℝ) (hl1 : 1 < lam) (hl2 : lam < 2) (αpp : ℝ) (hαpp : αpp < 2)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (c : ℝ) (hc : 0 < c)
    (hΞc : ∀ z, |z| ≤ c → Ξ z = 1) (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (hαl : αpp < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ s : ℝ, Real.log Qn + 4 ≤ s → s ≤ αpp * Real.log Qn →
      TrackF.famF (Finset.Icc 2 Qn) ⌊XlamS lam Qn (twin Qn r0 ε0)⌋₊ (TrackF.acoefS (twin Qn r0 ε0) s)
        ≤ famSize Qn * (twin Qn r0 ε0 / (2 * Real.pi))
            * (LcS Qn (twin Qn r0 ε0) + Real.log (Kstd Qn (twin Qn r0 ε0)) + C)
          + (Qn : ℝ) ^ 2 * (1 + C * (Real.log (LcS Qn (twin Qn r0 ε0)) / LcS Qn (twin Qn r0 ε0)))
            * RingS Qn (twin Qn r0 ε0) κ Ξ (Kstd Qn (twin Qn r0 ε0)) (1 / LcS Qn (twin Qn r0 ε0)) (s - 1) s
          + C * (Real.log (LcS Qn (twin Qn r0 ε0)) / LcS Qn (twin Qn r0 ε0)) * famSize Qn
            * l2S ⌊XlamS lam Qn (twin Qn r0 ε0)⌋₊ (twin Qn r0 ε0) s :=
  ASc.AS_pointwise_corr' lam hl1 hl2 αpp hαpp κ hκ hκ1 Ξ hΞ c hc hΞc r0 ε0 hr0 hε0 hαl

end ShellS
end ZetaShell
