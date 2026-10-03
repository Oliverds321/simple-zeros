/-
L7_9 round 3, sub-node (c3) of `pnt_step`: the uniform PNT bound for `E(m) = Σ_{j≤m}(Λ′(j) − 1)` on the
support of the smooth weight, eventually in `Q`, at `A = 3 + 3(r+ε)`:
`E(m) = (ψ(m) − m) − Σ_{j≤m, j=p^k, p≤R₀} Λ(j)`; `m ≥ e^{s−1} − 1 ≥ Q`, and
`L7_2.psi_sub_id_isLittleO_log_rpow A` gives `|ψ(m) − m| ≤ m(log m)^{−A} ≤ e^{s+1}(log Q)^{−A}` once `Q` is large;
the truncation is `≤ R₀(log m)²/log 2 = e^s(log m)²/(log 2·QTℒ)`, also `≤ e^{s+1}(log Q)^{−A}` eventually.
-/
import ZetaShell.LemmaK.LK9_K6c_Helpers
import ZetaShell.LemmaK.LK9_K6c3_Aux
import ZetaShell.PNT.PNTMedium

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

set_option maxHeartbeats 1000000 in
theorem E_bound (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      ∀ m : ℕ, Real.exp (s - 1) - 1 ≤ (m : ℝ) → (m : ℝ) ≤ Real.exp (s + 1) →
        ‖K6.psum m (fun j => ((K6.lamP (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s) j - 1 : ℝ) : ℂ))‖
          ≤ 2 * Real.exp (s + 1) * Real.log (Qn : ℝ) ^ (-(3 + 3 * (r + ε))) := by
  set A : ℝ := 3 + 3 * (r + ε) with hA
  have hre : 3 ≤ r + ε := by linarith
  have hA0 : 0 ≤ A := by linarith
  -- PNT at `A`, made uniform
  have hO := (L7_2.psi_sub_id_isLittleO_log_rpow A).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Y₀, hY⟩ := Filter.eventually_atTop.mp hO
  have E1 : ∀ᶠ Qn : ℕ in atTop, (100 : ℝ) ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 100)
  have E2 : ∀ᶠ Qn : ℕ in atTop, (4 : ℝ) ≤ Real.log (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 4)
  have E3 : ∀ᶠ Qn : ℕ in atTop, Real.log (Qn : ℝ) ^ (r + ε) ≤ (Qn : ℝ) := by
    have hO3 := (isLittleO_log_rpow_rpow_atTop (r + ε) (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1)
    have h3 : ∀ᶠ y : ℝ in atTop, Real.log y ^ (r + ε) ≤ y := by
      filter_upwards [hO3, eventually_ge_atTop (1 : ℝ)] with y hy hy1
      have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _), Real.rpow_one,
        Real.norm_of_nonneg (by linarith), one_mul] at hy
      exact hy
    exact tendsto_natCast_atTop_atTop.eventually h3
  have E4 : ∀ᶠ Qn : ℕ in atTop, Y₀ ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Y₀)
  have E5 : ∀ᶠ Qn : ℕ in atTop, 40 * Real.log (Qn : ℝ) ^ (2 + A) ≤ (Qn : ℝ) := by
    have hO5 := (isLittleO_log_rpow_rpow_atTop (2 + A) (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1 / 40)
    have h5 : ∀ᶠ y : ℝ in atTop, 40 * Real.log y ^ (2 + A) ≤ y := by
      filter_upwards [hO5, eventually_ge_atTop (1 : ℝ)] with y hy hy1
      have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _), Real.rpow_one,
        Real.norm_of_nonneg (by linarith)] at hy
      linarith
    exact tendsto_natCast_atTop_atTop.eventually h5
  filter_upwards [E1, E2, E3, E4, E5] with Qn h100 hlog hTQ hY₀ h40 s hs1 hs2 m hm1 hm2
  set x := Real.log (Qn : ℝ) with hx
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  set L := Lc (Qn : ℝ) T with hL
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hT64 : 64 ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 hre
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have : (64 : ℝ) ≤ x ^ 3 := by
      have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hlog 3
      norm_num at h4; linarith
    rw [hT, ZetaQ.Twin]; linarith
  have hTQ2 : T ≤ (Qn : ℝ) := hTQ
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  have he1 := Real.exp_one_lt_d9
  have hL1 : 1 ≤ L := by
    rw [hL, Lc]
    have hz0 : 0 < (Qn : ℝ) * T / (2 * Real.pi) := by positivity
    rw [Real.le_log_iff_exp_le hz0, le_div_iff₀ (by positivity)]
    nlinarith
  have hL2 : L ≤ 2 * x := by
    have h1 : (Qn : ℝ) * T / (2 * Real.pi) ≤ (Qn : ℝ) * (Qn : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hTQ2 hQ0.le]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hQ0.ne' hQ0.ne'] at h2
    rw [hL, Lc]
    linarith
  have hQTL : 0 < (Qn : ℝ) * T * L := by positivity
  have hTL6 : 6 ≤ T * L := le_trans (by norm_num) (mul_le_mul hT64 hL1 (by norm_num) (by linarith))
  have hQle : (Qn : ℝ) ≤ (Qn : ℝ) * T * L := by
    rw [mul_assoc]; exact le_mul_of_one_le_right hQ0.le (by linarith)
  have h6Q : 6 * (Qn : ℝ) ≤ (Qn : ℝ) * T * L := by
    rw [mul_assoc]; nlinarith [mul_le_mul_of_nonneg_left hTL6 hQ0.le]
  have hQTL1 : 1 ≤ (Qn : ℝ) * T * L := by linarith
  have hes : (Qn : ℝ) * T * L ≤ Real.exp s := by
    have h := Real.exp_le_exp.mpr hs1
    rw [ellK, ← hL, Real.exp_log hQTL] at h
    exact h
  have hsX : s ≤ 4 * x := by
    have h := hs2
    rw [Xlam, ← hL, Real.log_exp] at h
    nlinarith
  have hs0 : 0 ≤ s := by
    have : Real.log ((Qn : ℝ) * T * L) ≥ 0 := Real.log_nonneg hQTL1
    rw [ellK, ← hL] at hs1; linarith
  -- `m ≥ Q`
  have hmQ : (Qn : ℝ) ≤ m := by
    have h1 : Real.exp (s - 1) = Real.exp s / Real.exp 1 := Real.exp_sub _ _
    have h2 : 6 * (Qn : ℝ) ≤ Real.exp s := h6Q.trans hes
    have h3 : 2 * (Qn : ℝ) ≤ Real.exp (s - 1) := by
      rw [h1, le_div_iff₀ (Real.exp_pos 1)]; nlinarith
    linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1R : (1 : ℝ) ≤ m := by linarith
  have hm1N : 1 ≤ m := by exact_mod_cast hm1R
  have hlogm : x ≤ Real.log m := Real.log_le_log hQ0 hmQ
  have hlogm_le : Real.log m ≤ s + 1 := by
    rw [← Real.log_exp (s + 1)]; exact Real.log_le_log hm0 hm2
  have hxA : Real.log m ^ (-A) ≤ x ^ (-A) := Real.rpow_le_rpow_of_nonpos hx0 hlogm (by linarith)
  -- the PNT part
  have hpsi : |(∑ j ∈ Finset.Ioc 0 m, ArithmeticFunction.vonMangoldt j) - m|
      ≤ Real.exp (s + 1) * x ^ (-A) := by
    have h := hY (m : ℝ) (hY₀.trans hmQ)
    have hpsi_eq : Chebyshev.psi (m : ℝ) = ∑ j ∈ Finset.Ioc 0 m, ArithmeticFunction.vonMangoldt j := by
      rw [Chebyshev.psi, Nat.floor_natCast]
    simp only [Pi.sub_apply, id, hpsi_eq, Real.norm_eq_abs, one_mul] at h
    have hr0 : 0 ≤ (m : ℝ) * Real.log m ^ (-A) :=
      mul_nonneg hm0.le (Real.rpow_nonneg (by linarith) _)
    rw [abs_of_nonneg hr0] at h
    refine h.trans ?_
    exact mul_le_mul hm2 hxA (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
  -- the truncation part
  set R := R0 (Qn : ℝ) T s with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef, R0, ← hL]; positivity
  have hRle : R ≤ Real.exp s := by
    rw [hRdef, R0, ← hL, div_le_iff₀ hQTL]
    exact le_mul_of_one_le_right (Real.exp_pos s).le hQTL1
  have hB : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ R → Real.log p ≤ s := by
    intro p hp hpR
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have := Real.log_le_log hp0 (hpR.trans hRle)
    rwa [Real.log_exp] at this
  have htr := K6.truncD_le R s m hR0 hs0 hB
  have hK := K6.nat_log_two_le m hm1N
  have htr2 : K6.truncD R m ≤ Real.exp (s + 1) * x ^ (-A) := by
    have h1 : K6.truncD R m ≤ R * (2 * (s + 1)) * s := by
      refine htr.trans ?_
      apply mul_le_mul_of_nonneg_right _ hs0
      apply mul_le_mul_of_nonneg_left _ hR0
      linarith
    have h2 : R ≤ Real.exp s / (Qn : ℝ) := by
      rw [hRdef, R0, ← hL]
      exact div_le_div_of_nonneg_left (Real.exp_pos s).le hQ0 hQle
    have h3 : 2 * (s + 1) * s ≤ 40 * x ^ 2 := by
      have hs5 : s + 1 ≤ 5 * x := by linarith
      calc 2 * (s + 1) * s ≤ 2 * (5 * x) * (4 * x) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hs5 (by norm_num)) hsX hs0 (by positivity)
        _ = 40 * x ^ 2 := by ring
    have h4 : 40 * x ^ 2 / (Qn : ℝ) ≤ x ^ (-A) := by
      rw [div_le_iff₀ hQ0]
      have e : x ^ (2 + A) = x ^ 2 * x ^ A := by
        rw [Real.rpow_add hx0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have e2 : x ^ (-A) * x ^ A = 1 := by
        rw [← Real.rpow_add hx0]; simp
      rw [e] at h40
      have e3 : 40 * x ^ 2 = 40 * x ^ 2 * x ^ A * x ^ (-A) := by
        rw [mul_assoc (40 * x ^ 2), mul_comm (x ^ A), e2, mul_one]
      rw [e3]
      calc 40 * x ^ 2 * x ^ A * x ^ (-A) ≤ (Qn : ℝ) * x ^ (-A) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
            linarith
        _ = x ^ (-A) * (Qn : ℝ) := by ring
    calc K6.truncD R m ≤ R * (2 * (s + 1)) * s := h1
      _ = R * (2 * (s + 1) * s) := by ring
      _ ≤ (Real.exp s / (Qn : ℝ)) * (40 * x ^ 2) :=
          mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = Real.exp s * (40 * x ^ 2 / (Qn : ℝ)) := by ring
      _ ≤ Real.exp s * x ^ (-A) := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
      _ ≤ Real.exp (s + 1) * x ^ (-A) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
            (Real.rpow_nonneg hx0.le _)
  have hD0 := K6.truncD_nonneg R m
  rw [K6.psum_lamP_eq, Complex.norm_real, Real.norm_eq_abs]
  calc |(∑ j ∈ Finset.Ioc 0 m, ArithmeticFunction.vonMangoldt j) - m - K6.truncD R m|
      ≤ |(∑ j ∈ Finset.Ioc 0 m, ArithmeticFunction.vonMangoldt j) - m| + |K6.truncD R m| :=
        abs_sub _ _
    _ ≤ Real.exp (s + 1) * x ^ (-A) + Real.exp (s + 1) * x ^ (-A) := by
        rw [abs_of_nonneg hD0]; exact add_le_add hpsi htr2
    _ = 2 * Real.exp (s + 1) * x ^ (-A) := by ring

end LemmaK
end ZetaShell
