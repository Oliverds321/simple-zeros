/-
Node SD-A7 (L7_7, F1a): **the regime `X ≤ Q^{2−δ}` along the Shell design**, `δ = 9/200` — the bandwidth-lifted
`ZetaQ.design_regime` (`FrobAssembly.lean:1148`, which has `X ≤ Q^{3/2}`, `2Q^{−1/2} ≤ 1/K`). Generic in any profile
with `λ ≤ 191/100` (so it serves D53-L75 at `λ = 93/50` too). Draft: sec_shell rem:shell-lean; L7_2 §6 item 1;
L7_4 1a (the only essential cap is `λ_eff < 2`). The only new step: `λ(1 + log(T/2π)/log Q) ≤ 2 − δ` eventually,
i.e. `(r+ε)·log log Q ≤ 0.0235·log Q`.
Sanity (`sanity_L7_7.py`, `r+ε = 3.5`): `log X − (2−δ)log Q` = +22.8 at `log Q = 10²` (FALSE there), +8.8 at 700,
−2.3 at `10³`, −392 at `10⁴`, −4.5·10⁴ at `10⁶` (crossover near `log Q ≈ 900`); `2Q^{−δ} ≤ 1/K` at `K = 10⁶` from `log Q ≈ 330`.
Deps: the proof of `design_regime` verbatim. Difficulty M (copy + one more `log log ≤ c log` step).
PROVED: `design_regime`'s proof with `LL ≤ 1.02·log Q` (from `(r+ε)·log log Q ≤ 0.02·log Q`) and `2K ≤ Q^{9/200}`.
-/
import ZetaShell.Design.ShellDesignDefs

namespace ZetaShell.Design

open ZetaQ Filter Asymptotics

theorem shellDesign_regime (S : ShellProfile) (hlam : (S.lam : ℝ) ≤ 191 / 100) (r ε : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, ShellDesignM S r ε (Qn : ℝ) P →
      K ≤ Real.log Qn ∧ K ≤ P.T ∧ K * P.LL ^ 2 ≤ P.T ∧ P.LL ≤ 2 * Real.log Qn ∧
      K * (1 + Real.log Qn) ^ 2 ≤ Qn ∧ P.XQ ≤ Real.rpow P.Q (2 - deltaShell) ∧
      2 * Real.rpow P.Q (-deltaShell) ≤ 1 / K ∧
      Real.log ((Qn : ℝ) * (P.T + 2)) ≤ 3 * Real.log Qn := by
  have hre : (3 : ℝ) ≤ r + ε := by linarith
  have hre0 : (0 : ℝ) < r + ε := by linarith
  have hK0 : 0 < K := by linarith
  have hx1 : ∀ᶠ x : ℝ in atTop, (r + ε) * Real.log x ≤ x :=
    FrobAssembly.loglog_le_eventually _ hre0
  have hx2 : ∀ᶠ x : ℝ in atTop, ((r + ε) / 0.02) * Real.log x ≤ x :=
    FrobAssembly.loglog_le_eventually _ (by positivity)
  have hx3 : ∀ᶠ x : ℝ in atTop, K ≤ x := eventually_ge_atTop K
  have hx4 : ∀ᶠ x : ℝ in atTop, 4 * K ≤ x := eventually_ge_atTop (4 * K)
  have hx5 : ∀ᶠ x : ℝ in atTop, 4 * K * x ^ 2 ≤ Real.exp x := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2 (b := (1:ℝ)) (by norm_num)).def
      (by positivity : (0:ℝ) < 1 / (4 * K))
    filter_upwards [h, eventually_ge_atTop (0:ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs, one_mul] at hx
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2), Real.abs_exp] at hx
    calc 4 * K * x ^ 2 ≤ 4 * K * (1 / (4 * K) * Real.exp x) := by gcongr
      _ = Real.exp x := by field_simp
  have hx6 : ∀ᶠ x : ℝ in atTop, 2 * K ≤ Real.exp (9 / 200 * x) := by
    have h := Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (show (0:ℝ) < 9 / 200 by norm_num))
    filter_upwards [h.eventually_ge_atTop (2 * K)] with x hx
    simpa using hx
  have hx7 : ∀ᶠ x : ℝ in atTop, Real.log (2 * Real.pi) ≤ x := eventually_ge_atTop _
  have hlogx : ∀ᶠ x : ℝ in atTop, Real.log 2 + (r + ε) * Real.log x ≤ x := by
    have h := FrobAssembly.loglog_le_eventually (2 * (r + ε)) (by positivity)
    filter_upwards [h, eventually_ge_atTop (2 * Real.log 2)] with x hx hx2
    nlinarith [Real.log_nonneg (show (1:ℝ) ≤ x by linarith [Real.log_two_gt_d9])]
  filter_upwards [tendsto_log_nat_atTop.eventually hx1, tendsto_log_nat_atTop.eventually hx2,
    tendsto_log_nat_atTop.eventually hx3, tendsto_log_nat_atTop.eventually hx4,
    tendsto_log_nat_atTop.eventually hx5,
    tendsto_log_nat_atTop.eventually hx6, tendsto_log_nat_atTop.eventually hx7,
    tendsto_log_nat_atTop.eventually hlogx, eventually_ge_atTop 3]
    with Qn h1 h2 h3 h4 h5 h6 h7 h8 hQn3
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (3 : ℝ) ≤ Qn := by exact_mod_cast hQn3
  have hQn0 : (0 : ℝ) < Qn := by linarith
  set x := Real.log (Qn : ℝ) with hxdef
  have hx0 : 0 < x := by linarith [Real.log_nonneg (show (1:ℝ) ≤ 2 * Real.pi by
    linarith [Real.pi_gt_three])]
  have hxe : Real.exp x = Qn := Real.exp_log hQn0
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog2pi3 : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.exp_one_gt_d9, Real.pi_lt_d2]
  have hTx : P.T = x ^ (r + ε) := by rw [hdes.2.2.1]; rfl
  have hTpos : 0 < P.T := hP.T_pos
  have hlogT : Real.log P.T = (r + ε) * Real.log x := by
    rw [hTx, Real.log_rpow hx0]
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hLL : P.LL = x + (r + ε) * Real.log x - Real.log (2 * Real.pi) := by
    unfold ParamsQ.LL
    rw [hQ, Real.log_div (by positivity) (by positivity), Real.log_mul hQn0.ne' hTpos.ne', hlogT]
  have hLLx : P.LL ≤ 2 * x := by rw [hLL]; linarith
  have hLLge : x ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hx3T : x ^ 3 ≤ P.T := by
    rw [hTx]
    have : x ^ (3:ℝ) ≤ x ^ (r + ε) := Real.rpow_le_rpow_of_exponent_le (by linarith) hre
    rw [show (x:ℝ) ^ (3:ℝ) = x ^ (3:ℕ) by norm_cast] at this
    exact this
  refine ⟨h3, ?_, ?_, hLLx, ?_, ?_, ?_, ?_⟩
  · calc K ≤ x := h3
      _ ≤ x ^ 3 := by nlinarith
      _ ≤ P.T := hx3T
  · calc K * P.LL ^ 2 ≤ K * (2 * x) ^ 2 := by gcongr; linarith
      _ = 4 * K * x ^ 2 := by ring
      _ ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg x)
      _ = x ^ 3 := by ring
      _ ≤ P.T := hx3T
  · rw [← hxe]
    calc K * (1 + x) ^ 2 ≤ 4 * K * x ^ 2 := by nlinarith
      _ ≤ Real.exp x := h5
  · -- `X ≤ Q^{2−δ}`
    have hLB : P.LB = P.lam * P.LL := rfl
    have hlam' : P.lam = (S.lam : ℝ) := hdes.2.2.2.1
    show Real.exp P.LB ≤ P.Q ^ (2 - deltaShell : ℝ)
    rw [hQ, Real.rpow_def_of_pos hQn0, ← hxdef]
    apply Real.exp_le_exp.mpr
    rw [hLB]
    have hLL02 : P.LL ≤ 1.02 * x := by
      rw [hLL]
      have : (r + ε) * Real.log x ≤ 0.02 * x := by
        have := h2
        rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)] at this
        linarith
      linarith
    have hLL0 : 0 ≤ P.LL := by linarith
    have hm : P.lam * P.LL ≤ 191 / 100 * P.LL :=
      mul_le_mul_of_nonneg_right (by rw [hlam']; exact hlam) hLL0
    unfold deltaShell
    nlinarith
  · -- `2 Q^{−δ} ≤ 1/K`
    show 2 * P.Q ^ (-deltaShell : ℝ) ≤ 1 / K
    rw [hQ, Real.rpow_def_of_pos hQn0, ← hxdef, le_div_iff₀ hK0]
    have hpos := Real.exp_pos (x * -deltaShell)
    have hm := mul_le_mul_of_nonneg_left h6 hpos.le
    have e : Real.exp (x * -deltaShell) * Real.exp (9 / 200 * x) = 1 := by
      rw [← Real.exp_add]; unfold deltaShell
      rw [show x * -(9 / 200 : ℝ) + 9 / 200 * x = 0 by ring, Real.exp_zero]
    linarith
  · -- `log(Qn(T+2)) ≤ 3 log Qn`
    have hT2 : P.T + 2 ≤ 2 * P.T := by linarith [hP.T_ge300]
    calc Real.log ((Qn : ℝ) * (P.T + 2)) ≤ Real.log ((Qn : ℝ) * (2 * P.T)) :=
          Real.log_le_log (by positivity) (by gcongr)
      _ = x + (Real.log 2 + Real.log P.T) := by
          rw [Real.log_mul hQn0.ne' (by positivity), Real.log_mul (by norm_num) hTpos.ne']
      _ ≤ 3 * x := by rw [hlogT]; linarith

end ZetaShell.Design
