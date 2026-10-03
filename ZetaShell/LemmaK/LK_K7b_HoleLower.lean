/-
Node K7b (L7_3, round 3): eq:K-hole — `Hole(S) ≥ (s − ℓ_K)·J − 2‖a‖` on the hole range, `J = ∫_{|β|≤Δ} |S′|²`
(the integral exactly as in K6 `principal_arc_mass`). Proof (draft (c)): `a = a′ + a″` (`aPrime`); K4 at each `r ≤ R₀`
integrated over `|β| ≤ Δ` and K4b (`Σ_{r≤R₀} μ²/φ ≥ log(⌊R₀⌋+1) ≥ log R₀ = s − ℓ_K`) give `Hole(S′) ≥ (s − ℓ_K)J`;
`Hole(S′) ≤ ‖a′‖² ≤ ‖a‖²` and `Hole(S″) ≤ ‖a″‖² ≤ 1` (K5) by disjointness of the balls (K3) and Parseval; Cauchy–Schwarz
over the balls: `Hole(S) ≥ Hole(S′) − 2√(Hole(S′)Hole(S″))`. Difficulty: M (shares the circle-measure step with K7a). PROVED (round 3) from `hole_lower_generic`, K5 and
`R0_le_Q_eventually` (`log log Q = o(log Q)`, `λ < 2`).
-/
import ZetaShell.LemmaK.LK_K7_Defs
import ZetaShell.LemmaK.LK_K7_HoleGeneric
import ZetaShell.LemmaK.LK_K5_SmallPrimes

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

/-- `R₀ ≤ Q/e` on the hole range, eventually (`log log Q = o(log Q)`, `λ < 2`): `log R₀ ≤ log Q − 1`. -/
theorem R0_le_Q_eventually (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      Real.log (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s) ≤ Real.log (Qn : ℝ) - 1 := by
  have hre : 0 < r + ε := by linarith
  have hc : 0 < (2 - lam) / ((lam - 1) * (r + ε)) := by
    apply div_pos (by linarith); exact mul_pos (by linarith) hre
  have hlo := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).def hc
  have hlo' := tendsto_natCast_atTop_atTop.eventually hlo
  have hbig : ∀ᶠ Qn : ℕ in atTop, Real.exp (2 * Real.pi + 2) ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hlo', hbig] with Qn hq hQbig
  intro s hs
  simp only [Function.comp, id, Real.norm_eq_abs] at hq
  have hpi := Real.pi_pos
  have hQpos : (0 : ℝ) < Qn := lt_of_lt_of_le (Real.exp_pos _) hQbig
  have hlogQ : 2 * Real.pi + 2 ≤ Real.log Qn := by
    rw [Real.le_log_iff_exp_le hQpos]; exact hQbig
  have hlogQ0 : 0 < Real.log (Qn : ℝ) := by linarith
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  have hT1 : 1 ≤ T := by
    rw [hT]; unfold ZetaQ.Twin
    exact Real.one_le_rpow (by linarith) hre.le
  have hTpos : 0 < T := by linarith
  have hlogT : Real.log T = (r + ε) * Real.log (Real.log Qn) := by
    rw [hT]; unfold ZetaQ.Twin; exact Real.log_rpow hlogQ0 _
  have hloglog : Real.log (Real.log Qn) ≤ (2 - lam) / ((lam - 1) * (r + ε)) * Real.log Qn := by
    have := hq
    rw [abs_of_pos hlogQ0] at this
    exact le_trans (le_abs_self _) this
  -- `ℒ = log Q + log T − log 2π ≥ 1`
  set Lc0 := Lc (Qn : ℝ) T with hLc0
  have hLcdef : Lc0 = Real.log Qn + Real.log T - Real.log (2 * Real.pi) := by
    rw [hLc0]; unfold Lc
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hQpos.ne' hTpos.ne']
  have hlog2pi : Real.log (2 * Real.pi) ≤ 2 * Real.pi := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity); linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hLc1 : 1 ≤ Lc0 := by rw [hLcdef]; linarith
  have hLcpos : 0 < Lc0 := by linarith
  -- `log R₀ = s − log(QTℒ)`, `log X = λℒ`
  have hR : Real.log (R0 (Qn : ℝ) T s) = s - Real.log ((Qn : ℝ) * T * Lc0) := by
    unfold R0
    rw [← hLc0, Real.log_div (Real.exp_pos s).ne' (by positivity), Real.log_exp]
  have hX : Real.log (Xlam lam (Qn : ℝ) T) = lam * Lc0 := by
    unfold Xlam; rw [← hLc0, Real.log_exp]
  have hQTL : Real.log ((Qn : ℝ) * T * Lc0) = Real.log Qn + Real.log T + Real.log Lc0 := by
    rw [Real.log_mul (by positivity) hLcpos.ne', Real.log_mul hQpos.ne' hTpos.ne']
  have hlogL : 0 ≤ Real.log Lc0 := Real.log_nonneg hLc1
  rw [hR, hQTL]
  rw [hX] at hs
  -- `(λ−1) log T ≤ (2−λ) log Q`
  have hkey : (lam - 1) * Real.log T ≤ (2 - lam) * Real.log Qn := by
    rw [hlogT]
    have h1 : (lam - 1) * ((r + ε) * Real.log (Real.log Qn))
        ≤ (lam - 1) * ((r + ε) * ((2 - lam) / ((lam - 1) * (r + ε)) * Real.log Qn)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hloglog hre.le) (by linarith)
    have e : (lam - 1) * ((r + ε) * ((2 - lam) / ((lam - 1) * (r + ε)) * Real.log Qn))
        = (2 - lam) * Real.log Qn := by
      have hl1 : lam - 1 ≠ 0 := ne_of_gt (by linarith)
      have hre' : r + ε ≠ 0 := ne_of_gt hre
      field_simp
    linarith
  have hlam0 : 0 ≤ lam * Real.log (2 * Real.pi) := by
    have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    positivity
  rw [hLcdef] at hs
  nlinarith

/-- **K7b.** -/
theorem hole_lower (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      (s - ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε))
          * (∫ β in (-(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))..
              (ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)),
            ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
              (aPrime (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)) β‖ ^ 2)
        - 2 * Real.sqrt (ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s))
        ≤ holeInt ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
            (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)
            (ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)) := by
  have hre : 0 < r + ε := by linarith
  filter_upwards [small_primes_l2 lam r ε hlam1 hlam2 hr hε, R0_le_Q_eventually lam r ε hlam1 hlam2 hr hε,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1 + 7)] with Qn h5 hRQ hQbig
  intro s hs1 hs2
  have hQpos : (0 : ℝ) < Qn := by linarith [Real.exp_pos 1]
  have hlogQ0 : 0 < Real.log (Qn : ℝ) := Real.log_pos (by linarith [Real.add_one_le_exp 1])
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  have hTpos : 0 < T := by rw [hT]; unfold ZetaQ.Twin; exact Real.rpow_pos_of_pos hlogQ0 _
  set Lc0 := Lc (Qn : ℝ) T with hLc0
  set R := R0 (Qn : ℝ) T s with hRdef
  set N := ⌊Xlam lam (Qn : ℝ) T⌋₊ with hN
  have hQ7 : (7 : ℝ) < Qn := by linarith [Real.exp_one_gt_d9]
  have hT1 : 1 ≤ T := by
    rw [hT]; unfold ZetaQ.Twin
    exact Real.one_le_rpow (by rw [Real.le_log_iff_exp_le hQpos]; linarith) hre.le
  have hQT : 2 * Real.pi < (Qn : ℝ) * T := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have : (Qn : ℝ) ≤ (Qn : ℝ) * T := le_mul_of_one_le_right hQpos.le hT1
    linarith
  have hLcpos : 0 < Lc0 := by
    rw [hLc0]; unfold Lc
    apply Real.log_pos; rw [lt_div_iff₀ (by positivity)]; linarith
  have hQTL : 0 < (Qn : ℝ) * T * Lc0 := by positivity
  have hellK : ellK (Qn : ℝ) T = Real.log ((Qn : ℝ) * T * Lc0) := rfl
  have hlogR : Real.log R = s - ellK (Qn : ℝ) T := by
    rw [hRdef, hellK]; unfold R0
    rw [← hLc0, Real.log_div (Real.exp_pos s).ne' hQTL.ne', Real.log_exp]
  have hRpos : 0 < R := by rw [hRdef]; unfold R0; positivity
  have hR1 : 1 ≤ R := by
    have : 0 ≤ Real.log R := by rw [hlogR]; linarith
    rwa [Real.log_nonneg_iff hRpos] at this
  have hRQ' : R ≤ Qn := by
    have := hRQ s hs2
    have h' : Real.log R ≤ Real.log Qn := by linarith
    rwa [Real.log_le_log_iff hRpos hQpos] at h'
  -- `2Δ = 1/(RQ)`
  set Δ := T * Lc0 / (2 * Real.exp s) with hΔdef
  have hΔ : 0 < Δ := by positivity
  have h2Δ : 2 * Δ = 1 / (R * Qn) := by
    rw [hΔdef, hRdef]; unfold R0; rw [← hLc0]
    field_simp
  have hΔ1 : 2 * Δ ≤ 1 := by
    rw [h2Δ, div_le_one (by positivity)]
    nlinarith
  have hsepΔ : ∀ r r' : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → 1 ≤ r' → r' ≤ ⌊R⌋₊ → 2 * Δ ≤ 1 / ((r : ℝ) * r') := by
    intro r1 r2 h1 h1R h2 h2R
    rw [h2Δ]
    have hr1 : (r1 : ℝ) ≤ R := le_trans (by exact_mod_cast h1R) (Nat.floor_le hRpos.le)
    have hr2 : (r2 : ℝ) ≤ R := le_trans (by exact_mod_cast h2R) (Nat.floor_le hRpos.le)
    have hr10 : (1 : ℝ) ≤ r1 := by exact_mod_cast h1
    have hr20 : (1 : ℝ) ≤ r2 := by exact_mod_cast h2
    apply one_div_le_one_div_of_le (by positivity)
    have : (r1 : ℝ) * r2 ≤ R * R := mul_le_mul hr1 hr2 (by linarith) (by linarith)
    have : R * R ≤ R * Qn := mul_le_mul_of_nonneg_left hRQ' hRpos.le
    linarith
  have hcop : ∀ r : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → ∀ n ∈ Finset.Ioc 0 N, aPrime T s R n ≠ 0 → Nat.Coprime n r := by
    intro r hr1 hrR n _ hn
    unfold aPrime at hn
    by_cases h : IsPrimePow n ∧ R < (n.minFac : ℝ)
    · obtain ⟨hpp, hmin⟩ := h
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
      rw [hp.pow_minFac hk.ne'] at hmin
      apply Nat.Coprime.pow_left
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      have hple : p ≤ r := Nat.le_of_dvd (by omega) hdvd
      have : (r : ℝ) ≤ R := le_trans (by exact_mod_cast hrR) (Nat.floor_le hRpos.le)
      have : (p : ℝ) ≤ r := by exact_mod_cast hple
      linarith
    · exact absurd (if_neg h) hn
  have hA : ZetaQ.l2sq N (aPrime T s R) ≤ ZetaQ.l2sq N (acoef T s) := by
    unfold ZetaQ.l2sq
    refine Finset.sum_le_sum fun n _ => ?_
    unfold aPrime
    split_ifs
    · exact le_rfl
    · have := sq_nonneg ‖acoef T s n‖
      simpa using this
  have hB := h5 s hs1 (by linarith)
  have key := hole_lower_generic N (acoef T s) (aPrime T s R) R Δ hΔ hΔ1 hsepΔ hR1 hcop hA hB
  rw [hlogR] at key
  have hΔ' : T * Lc0 / (2 * Real.exp s) = Δ := rfl
  simpa [hΔ'] using key

end LemmaK
end ZetaShell
