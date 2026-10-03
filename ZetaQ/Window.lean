/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Window.lean — **the design window `φ = p(u/ℒ)·ϱ₂((L/2 − |u|)/w)` is an admissible
window**, and everything the rest of `ZetaQ` used to take from [R]'s FLAT facade
(`Zeta23.Params.*` under `Params.ValidQ`) is re-derived here from [R]'s GENERIC window layer
(`Zeta23.AdmWindow`, `Zeta23/ThmD/WindowCore.lean`) — exactly the route [R] itself takes for its
profile-weighted Theorem-D window (`Zeta23/ThmD/BridgeD.lean`).

Imports `ZetaQ.Defs` and `Zeta23.Taper.GevreyProduct` (the lifted product-window prototype;
`audit/ProductWindow_REPORT.md`). Imported by `ZetaQ.Certificate`, and so by every file below it.

Contents.
  §1  regime facts from `ParamsQ.Valid` (`LL > 0`, `l T > 0`, the scale identity);
  §2  the profile factor: `Mpoly` bounds, `φ = p(u/ℒ)·φ_flat` as functions;
  §3  **`Valid.admWindow : AdmWindow P.phiQ P.LB P.w P.cWin`** (from `8w ≤ L`), and the
      definitional identifications `gQ = gv φ`, `PhiQ = VPhiR φ`, `phiHatR = vHatR φ`,
      `localFun = AdmWindow.localFun φ L`;
  §4  the pointwise/support/smoothness facts the tree consumes (`phiQ` is `C³`, compactly
      supported in `[−L/2, L/2]`, `0 ≤ φ ≤ 1`, `‖φ‖₁ ≤ L`, `φ ≥ 1/6` on the plateau);
  §5  the bulk lower envelope `g ≥ (1/6)⁴·(L − 2w − |y|)₊` (replacing the flat `g ≥ (L − 2w −
      |y|)₊`), `g ≤ aL`, and the Fubini identity `∫ g = (∫ φ²)²` (new; [R] had no use for it);
  §6  Poisson (`ZeroSide.PoissonSq`) and the hat-normalisation positivity for the product window;
  §7  the Gevrey bound `P.toParams.GevreyPhiBound P.T 2 A (gevreyBprod A B)` and the §7.1
      envelope `‖φ̂(z)‖ ≤ e²·max(2B′w, L)·e^{|Im z|L/2}·exp(−(2/e)√(w‖z‖/A))`.

RULE 17. Every hypothesis below is `P.Valid` (no `lam_le_one`), `8w ≤ L` ([eq:wrange], a bound on
the RAMP WIDTH), or a Gevrey hypothesis on the RAMP `ϱ`. No λ-cap, no `X`–`T` comparison, no `D₀`.
-/
import ZetaQ.Defs
import Zeta23.Taper.GevreyProduct

noncomputable section

open Real Set MeasureTheory Filter Topology
open scoped BigOperators

namespace ZetaQ
namespace ParamsQ

variable {P : ParamsQ}

/-! ## §1 regime facts from `Valid` -/

theorem Valid.T_ge300 (hP : P.Valid) : (300 : ℝ) ≤ P.T := by
  have h := hP.T_ge; unfold Zeta23.Tail.T₀ at h; exact h

theorem Valid.T_pos (hP : P.Valid) : 0 < P.T := by linarith [hP.T_ge300]

theorem Valid.LL_pos (hP : P.Valid) : 0 < P.LL := by
  have hQ := hP.Q_ge; have hT := hP.T_ge300
  unfold ParamsQ.LL
  apply Real.log_pos
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Real.pi_le_four, Real.pi_pos]

theorem Valid.LB_pos (hP : P.Valid) : 0 < P.LB := mul_pos hP.lam_pos hP.LL_pos

theorem Valid.l_pos (hP : P.Valid) : 0 < Zeta23.l P.T := by
  have hT := hP.T_ge300
  unfold Zeta23.l
  apply Real.log_pos
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Real.pi_le_four, Real.pi_pos]

theorem Valid.l_ne_zero (hP : P.Valid) : Zeta23.l P.T ≠ 0 := ne_of_gt hP.l_pos

theorem Valid.w_pos (hP : P.Valid) : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w

theorem Valid.toParams_L (hP : P.Valid) : P.toParams.L P.T = P.LB := P.toParams_L hP.l_ne_zero

theorem Valid.toParams_lam_pos (hP : P.Valid) : 0 < P.toParams.lam := by
  show 0 < P.LB / Zeta23.l P.T
  exact div_pos hP.LB_pos hP.l_pos

theorem Valid.LB_div_LL (hP : P.Valid) : P.LB / P.LL = P.lam :=
  mul_div_cancel_right₀ P.lam hP.LL_pos.ne'

theorem Valid.LB_div_two_LL (hP : P.Valid) : P.LB / (2 * P.LL) = P.lam / 2 := by
  rw [div_eq_div_iff (by have := hP.LL_pos; positivity) (by norm_num)]
  unfold LB; ring

/-- `a > 0` (from the `Valid` floor `3/4 ≤ a`). -/
theorem Valid.aQ_pos (hP : P.Valid) : 0 < P.aQ := by linarith [hP.a_ge]

/-- `b > 0` (from the `Valid` floor `1/2 ≤ b`). -/
theorem Valid.bQ_pos (hP : P.Valid) : 0 < P.bQ := by linarith [hP.b_ge]

/-! ## §2 the profile factor -/

/-- `ParamsQ.Mpoly` is (definitionally) the prototype's `Mpoly`. -/
theorem Mpoly_eq_productWindow (pp : Polynomial ℝ) (R : ℝ) (j : ℕ) :
    Mpoly pp R j = Zeta23.ProductWindow.Mpoly pp R j := rfl

/-- `|p^{(j)}(t)| ≤ M_j` on the core `|t| ≤ λ/2`. -/
theorem abs_eval_le_profM (P : ParamsQ) (j : ℕ) {t : ℝ} (ht : |t| ≤ P.lam / 2) :
    |(Polynomial.derivative^[j] P.prof).eval t| ≤ P.profM j :=
  Zeta23.ProductWindow.abs_eval_le_Mpoly P.prof j ht

theorem Valid.profM_nonneg (hP : P.Valid) (j : ℕ) : 0 ≤ P.profM j :=
  (abs_nonneg _).trans (abs_eval_le_profM P j (t := 0) (by rw [abs_zero]; linarith [hP.lam_pos]))

/-- `M₀ ≥ |p(0)| ≥ 1/6`. -/
theorem Valid.profM_zero_ge (hP : P.Valid) : 1 / 6 ≤ P.profM 0 := by
  have h := abs_eval_le_profM P 0 (t := 0) (by rw [abs_zero]; linarith [hP.lam_pos])
  rw [Function.iterate_zero, id] at h
  have hb := hP.profile.bulk 0 (by rw [abs_zero]; linarith [hP.lam_pos])
  exact hb.trans ((le_abs_self _).trans h)

/-- **the window is the product** `φ(u) = p(u/ℒ)·φ_flat(u)`, as functions; the
evenness of `p` removes the `|u|` of `phiQ_eq_prof_mul`. -/
theorem Valid.phiQ_eq (hP : P.Valid) :
    P.phiQ = fun u => P.prof.eval (u / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u := by
  funext u
  rw [P.phiQ_eq_prof_mul hP.l_ne_zero hP.w_pos.ne']
  congr 1
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu, neg_div, hP.profile.even]

/-! ## §3 the admissible-window instance -/

/-- **THE design window is an admissible window**, with constant `cWin`:
`AdmWindow P.phiQ P.LB P.w P.cWin` from `P.Valid` and [eq:wrange] `8w ≤ L`. This is [R]'s
`XiPrime.admWindow_phiM` (support-local form, `Zeta23/Taper/GevreyProduct.lean`
`admWindow_polyQ_mul_phi`) at the polynomial factor `q(u) = p(u/ℒ)`, `A = M₁λ`, `B = M₂λ²`.
Rule 17: hypotheses `Valid` and `8w ≤ L` only.

**The SHARP window constant is NOT carried.** The carried
`cWin = c_ϱ + M₁λ + (M₁λ)² + M₂λ²` (`Defs.lean`; `≈ 548` at the qle design with the `Mpoly`
majorants, `≈ 1064` dyadic) is [R]'s `cMod` bound: it charges the profile's derivative terms
through `|q′| ≤ A/L`, `|q″| ≤ B/L²` against `8w ≤ L` as if they were of the ramp's order `c_ϱ/w`.
But `q(u) = p(u/ℒ)` has `|q′| ≤ M₁/ℒ`, `|q″| ≤ M₂/ℒ²`, and in
`‖(qφ)″‖₁ ≤ ‖q‖_∞‖φ″‖₁ + 2‖q′‖_∞‖φ′‖₁ + ‖q″‖_∞‖φ‖₁` (and the analogous expansion of `(q²φ²)″`,
which is where the `M₁²` and the `λ` factors come from) every profile term is `O(M_j·w/ℒ)`
RELATIVE to `c_ϱ/w`, so the sharp admissible constant is
`c_sharp = c_ϱ + (8M₁ + λ(2M₁² + 2M₂))·w/ℒ ≈ 33` at the design (`w = 1`, `ℒ ≈ 247`,
`c_ϱ(ϱ₂) = 31.26`) against the carried `≈ 548` — a factor `≈ 17` in `c`, `≈ 230×` in the ends
constant `C_ends` (`1.28×10⁷ → 2.93×10⁹`). Carrying it is NOT a ≤ 2-hour
job with no risk to the headline, for three reasons:
  (i) it needs a NEW product-window estimate in `Zeta23/Taper/GevreyProduct.lean` — the four
      `AdmWindow` L¹ fields for `(qφ)′`, `(qφ)″`, `(q²φ²)′`, `(q²φ²)″` with the `w/ℒ`-suppressed
      constants; [R]'s `admWindow_mul_phi` / `ModFactor` route (`Zeta23/XiPrime/QuarticWindow/
      ModWindow.lean`) does not expose them and would have to be re-derived (≈ 300 lines of
      integral estimates);
  (ii) `cWin` is a FROZEN `Defs.lean` field; its sharp value depends on `w` and `ℒ`, so
      `Budget.cWin_of_design : P.cWin = cWinDesign F` — an EQUALITY consumed by `InZone`
      (`crho_bdd`, `famPP_inZone_le`), `FrobAssembly` (`Kerr (cWinDesign F)`, `Kends (cWinDesign F)`,
      `frobSq_le_explicit`, ≈ 8 sites) and `Budget.trace_row_eventually`'s threshold
      `T ≥ 400π·cErr (cWinDesign F)` — would become an upper bound `P.cWin ≤ cWinDesign F` with
      every consumer re-proved monotone in `c`;
  (iii) `Zones`' rescaled constants, `FrobRow8`, `Ends.S2_localHypsCoreW` and `MuqUniform`'s
      per-character error read `P.cWin` directly.
The asymptotics are untouched either way (the ends are absorbed into the certificate slack
eventually, `FrobAssembly.endsMaj ≤ Kends(cWin)·Q²ℒ³`); the gain is §8 / §10.4's finite-`Q`
figures only (the changelog's S3 → S2 scenario). Recorded here; skipped. -/
theorem Valid.admWindow (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    Zeta23.AdmWindow P.phiQ P.LB P.w P.cWin := by
  have hLL := hP.LL_pos
  have hlam := hP.LB_div_LL
  have hcore := hP.LB_div_two_LL
  have hW := Zeta23.ProductWindow.admWindow_polyQ_mul_phi (ϱ := P.ϱ) (L := P.LB) (w := P.w)
    P.prof hLL (hP.profM_nonneg 1) (hP.profM_nonneg 2) hP.profile.even
    (fun t ht => by rw [hcore] at ht; linarith [hP.profile.bulk t ht])
    (fun t ht => by rw [hcore] at ht; exact hP.profile.le_one t ht)
    (by rw [hcore]; exact hP.profile.antitone)
    (fun t ht => by
      rw [hcore] at ht
      have h := abs_eval_le_profM P 1 ht
      rwa [Function.iterate_one] at h)
    (fun t ht => by
      rw [hcore] at ht
      have h := abs_eval_le_profM P 2 ht
      rwa [Function.iterate_succ_apply', Function.iterate_one] at h)
    hP.taper hP.one_le_w hw
  have hc : P.cWin = Zeta23.XiPrime.cMod P.ϱ (P.profM 1 * (P.LB / P.LL))
      (P.profM 2 * (P.LB / P.LL) ^ 2) := by
    unfold cWin Zeta23.XiPrime.cMod; rw [hlam]
  rw [hP.phiQ_eq, hc]
  exact hW

/-- `4 ≤ cWin`. -/
theorem Valid.four_le_cWin (hP : P.Valid) : 4 ≤ P.cWin := by
  have h1 := Zeta23.Taper.four_le_cRho hP.taper
  have h2 := hP.profM_nonneg 1
  have h3 := hP.profM_nonneg 2
  have hl := hP.lam_pos
  unfold cWin
  nlinarith [sq_nonneg (P.profM 1 * P.lam), mul_nonneg h2 hl.le, mul_nonneg h3 (sq_nonneg P.lam)]

theorem Valid.cWin_pos (hP : P.Valid) : 0 < P.cWin := by linarith [hP.four_le_cWin]

/-- the definitional identifications with [R]'s generic window data (all `rfl`). -/
theorem phiQ_eq_toParams_phi (P : ParamsQ) : P.phiQ = P.toParams.phi P.T := rfl
theorem gQ_eq_gv (P : ParamsQ) : P.gQ = Zeta23.AdmWindow.gv P.phiQ := rfl
theorem PhiQ_eq_VPhiR (P : ParamsQ) : P.PhiQ = Zeta23.AdmWindow.VPhiR P.phiQ := rfl
theorem phiHatR_eq_vHatR (P : ParamsQ) :
    P.toParams.phiHatR P.T = Zeta23.AdmWindow.vHatR P.phiQ := rfl
theorem Aphi_eq_Av (P : ParamsQ) : P.toParams.Aphi P.T = Zeta23.AdmWindow.Av P.phiQ := rfl
theorem phiHat_eq_vHat (P : ParamsQ) : P.toParams.phiHat P.T = Zeta23.AdmWindow.vHat P.phiQ := rfl

theorem Valid.aQ_eq_av (hP : P.Valid) : P.aQ = Zeta23.AdmWindow.av P.phiQ P.LB := by
  unfold aQ Zeta23.Params.a Zeta23.AdmWindow.av; rw [hP.toParams_L]; rfl

theorem Valid.bQ_eq_bv (hP : P.Valid) : P.bQ = Zeta23.AdmWindow.bv P.phiQ P.LB := by
  unfold bQ Zeta23.Params.b Zeta23.AdmWindow.bv; rw [hP.toParams_L]; rfl

theorem Valid.localFun_eq (hP : P.Valid) :
    P.toParams.localFun P.T = Zeta23.AdmWindow.localFun P.phiQ P.LB := by
  rw [Zeta23.Params.localFun_eq_admWindow, hP.toParams_L]; rfl

/-- `τ_k = T + k·2π/L` at the paper's scale. -/
theorem Valid.tau_eq (hP : P.Valid) (k : ℤ) :
    P.toParams.tau P.T k = P.T + k * (2 * Real.pi / P.LB) := by
  unfold Zeta23.Params.tau Zeta23.Params.hgrid; rw [hP.toParams_L]

/-! ## §4 pointwise, support, smoothness -/

theorem Valid.phiQ_nonneg (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (u : ℝ) : 0 ≤ P.phiQ u :=
  (hP.admWindow hw).nonneg u

theorem Valid.phiQ_le_one (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (u : ℝ) : P.phiQ u ≤ 1 :=
  (hP.admWindow hw).le_one u

theorem Valid.phiQ_even (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (u : ℝ) : P.phiQ (-u) = P.phiQ u :=
  (hP.admWindow hw).even u

theorem Valid.phiQ_eq_zero (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {u : ℝ} (hu : P.LB / 2 ≤ |u|) :
    P.phiQ u = 0 :=
  (hP.admWindow hw).support u hu

/-- `φ ∈ C³` (the polynomial factor is `C^∞`, the ramp is `C³`). Needs only `2w ≤ L`. -/
theorem Valid.phiQ_contDiff_three (hP : P.Valid) (hwL : 2 * P.w ≤ P.LB) :
    ContDiff ℝ 3 P.phiQ := by
  rw [hP.phiQ_eq]
  exact (Zeta23.ProductWindow.polyQ_contDiff P.prof P.LL 3).mul
    (Zeta23.Taper.phi_contDiff hP.taper hP.w_pos hwL)

/-- `φ ∈ C²` as a ℂ-valued function (the `hφC2` of `EFChi`). -/
theorem Valid.phiC_contDiff_two (hP : P.Valid) (hwL : 2 * P.w ≤ P.LB) :
    ContDiff ℝ 2 (fun u => (P.phiQ u : ℂ)) :=
  (Complex.ofRealCLM.contDiff.of_le le_top).comp ((hP.phiQ_contDiff_three hwL).of_le (by norm_num))

/-- `supp φ ⊆ [−L/2, L/2]` (closed support), from `Valid` alone. -/
theorem Valid.phiQ_tsupport_subset (hP : P.Valid) :
    tsupport P.phiQ ⊆ Set.Icc (-(P.LB / 2)) (P.LB / 2) := by
  refine closure_minimal ?_ isClosed_Icc
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hmem
  apply hu
  rw [hP.phiQ_eq]
  show P.prof.eval (u / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u = 0
  rw [Zeta23.Taper.phi_eq_zero hP.taper hP.w_pos, mul_zero]
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  rcases hmem with h | h
  · rw [abs_of_neg (by linarith [hP.LB_pos])]; linarith
  · rw [abs_of_pos (by linarith [hP.LB_pos])]; linarith

theorem Valid.phiQ_hasCompactSupport (hP : P.Valid) : HasCompactSupport P.phiQ :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (subset_tsupport _ |>.trans hP.phiQ_tsupport_subset)

theorem Valid.phiQ_support_subset (hP : P.Valid) :
    Function.support P.phiQ ⊆ Set.Icc (-(P.LB / 2)) (P.LB / 2) :=
  (subset_tsupport _).trans hP.phiQ_tsupport_subset

theorem Valid.phiQ_continuous (hP : P.Valid) (hwL : 2 * P.w ≤ P.LB) : Continuous P.phiQ :=
  (hP.phiQ_contDiff_three hwL).continuous

/-- `‖φ‖₁ ≤ L` (the `∫‖φ‖ ≤ 2Λ` input of the Gevrey envelope). -/
theorem Valid.integral_norm_phiQ_le (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    ∫ u, ‖(P.phiQ u : ℂ)‖ ≤ P.LB := by
  have hW := hP.admWindow hw
  calc ∫ u, ‖(P.phiQ u : ℂ)‖ = ∫ u, P.phiQ u := by
        congr 1; funext u
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW.nonneg u)]
    _ ≤ P.LB := hW.integral_le

/-- **the bulk floor on the plateau**: `φ ≥ 1/6` for `|u| ≤ L/2 − w` (F58's replacement of
the flat taper's `φ = 1` there: `ϱ = 1` on the plateau and `p ≥ 1/6` on the core). -/
theorem Valid.phiQ_ge_on_plateau (hP : P.Valid) {u : ℝ} (hu : |u| ≤ P.LB / 2 - P.w) :
    1 / 6 ≤ P.phiQ u := by
  rw [hP.phiQ_eq]
  show 1 / 6 ≤ P.prof.eval (u / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u
  rw [Zeta23.Taper.phi_eq_one hP.taper hP.w_pos hu, mul_one]
  apply hP.profile.bulk
  rw [abs_div, abs_of_pos hP.LL_pos, div_le_iff₀ hP.LL_pos]
  have e : P.lam / 2 * P.LL = P.LB / 2 := by unfold LB; ring
  rw [e]; linarith [hP.w_pos]

/-! ## §5 envelopes of `g` -/

/-- the bulk version of `Zeta23.Taper.le_autocorr_of_plateau`: `c ≤ v` on `[−M, M]` and
`v ≥ 0` give `c²·(2M − |y|)₊ ≤ (v⋆v)(y)`. -/
theorem le_autocorr_of_bulk (v : ℝ → ℝ) {M c : ℝ} (hc : 0 ≤ c) (h0 : ∀ u, 0 ≤ v u)
    (hp : ∀ u, |u| ≤ M → c ≤ v u) {y : ℝ} (hint : Integrable fun u => v u * v (u + y)) :
    c ^ 2 * max (2 * M - |y|) 0 ≤ Zeta23.Params.autocorr v y := by
  unfold Zeta23.Params.autocorr
  set S := Icc (-M) M ∩ Icc (-M - y) (M - y) with hS
  have hSm : MeasurableSet S := measurableSet_Icc.inter measurableSet_Icc
  have hle : ∀ u, S.indicator (fun _ => c ^ 2) u ≤ v u * v (u + y) := by
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu]
      simp only [hS, mem_inter_iff, mem_Icc] at hu
      have h1 := hp u (abs_le.mpr ⟨hu.1.1, hu.1.2⟩)
      have h2 := hp (u + y) (abs_le.mpr ⟨by linarith, by linarith⟩)
      calc c ^ 2 = c * c := sq c
        _ ≤ v u * v (u + y) := mul_le_mul h1 h2 hc (h0 u)
    · rw [indicator_of_notMem hu]
      exact mul_nonneg (h0 _) (h0 _)
  have hvol : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.inter_subset_left (t := Icc (-M - y) (M - y))))
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hind : Integrable (S.indicator fun _ : ℝ => c ^ 2) :=
    (integrable_indicator_iff hSm).mpr (integrableOn_const hvol)
  calc c ^ 2 * max (2 * M - |y|) 0 = c ^ 2 * (volume S).toReal := by
        rw [Zeta23.Taper.volume_Icc_inter_shift M y]
    _ = ∫ u, S.indicator (fun _ => c ^ 2) u := by
        rw [integral_indicator_const _ hSm, measureReal_def, smul_eq_mul, mul_comm]
    _ ≤ ∫ u, v u * v (u + y) :=
        integral_mono_of_nonneg
          (ae_of_all _ fun u => Set.indicator_nonneg (fun _ _ => sq_nonneg c) u) hint
          (ae_of_all _ hle)

/-- **the lower envelope of `g` for the design window**: `(1/6)⁴·(L − 2w − |y|)₊ ≤ g(y)`
— the flat taper's `(L − 2w − |y|)₊ ≤ g` (`Zeta23.Params.g_ge`) with the plateau `φ = 1`
replaced by the bulk floor `φ ≥ 1/6`. Rule 17: `Valid` and `8w ≤ L`. -/
theorem Valid.gQ_ge_bulk (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (y : ℝ) :
    (1 / 1296 : ℝ) * max (P.LB - 2 * P.w - |y|) 0 ≤ P.gQ y := by
  have hW := hP.admWindow hw
  have h := le_autocorr_of_bulk (fun u => P.phiQ u ^ 2) (M := P.LB / 2 - P.w)
    (c := (1 / 6 : ℝ) ^ 2) (by positivity) (fun u => sq_nonneg _)
    (fun u hu => pow_le_pow_left₀ (by norm_num) (hP.phiQ_ge_on_plateau hu) 2)
    (hW.integrable_sq_mul_shift y)
  have e1 : 2 * (P.LB / 2 - P.w) = P.LB - 2 * P.w := by ring
  have e2 : ((1 / 6 : ℝ) ^ 2) ^ 2 = 1 / 1296 := by norm_num
  rw [e1, e2] at h
  exact h

/-- `g(y) ≤ aL` pointwise (`φ² ≤ 1`). -/
theorem Valid.gQ_le_aL (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (y : ℝ) : P.gQ y ≤ P.aQ * P.LB := by
  have hW := hP.admWindow hw
  have e : P.aQ * P.LB = ∫ u, P.phiQ u ^ 2 := by
    rw [hP.aQ_eq_av, Zeta23.AdmWindow.av, inv_mul_eq_div, div_mul_cancel₀ _ hP.LB_pos.ne']
  rw [e]
  show Zeta23.Params.autocorr (fun u => P.phiQ u ^ 2) y ≤ _
  unfold Zeta23.Params.autocorr
  refine integral_mono (hW.integrable_sq_mul_shift y) (hW.integrable_pow (by norm_num)) fun u => ?_
  have h1 : P.phiQ (u + y) ^ 2 ≤ 1 := pow_le_one₀ (hW.nonneg _) (hW.le_one _)
  have h2 : 0 ≤ P.phiQ u ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

/-- **Fubini for the autocorrelation**: `∫ (f⋆f) = (∫ f)²` for integrable `f` (via the
measure-preserving shear `(u, y) ↦ (u, u + y)`). [R] never needed this; the F58 repair does,
because the flat plateau's first-moment bound is replaced by the bathtub argument
(`ZetaQ/Zones.lean` `taper_first_moment_ge`), which needs the exact mass `∫_{y≥0} g = ½(aL)²`. -/
theorem integral_autocorr_eq_sq {f : ℝ → ℝ} (hf : Integrable f) :
    ∫ y, Zeta23.Params.autocorr f y = (∫ u, f u) ^ 2 := by
  have hprod : Integrable (fun z : ℝ × ℝ => f z.1 * f z.2) (volume.prod volume) :=
    hf.mul_prod hf
  have hshear : Integrable (fun z : ℝ × ℝ => f z.1 * f (z.1 + z.2)) (volume.prod volume) :=
    (measurePreserving_prod_add (μ := volume) (ν := volume)).integrable_comp_of_integrable hprod
  have h1 : ∫ y, Zeta23.Params.autocorr f y
      = ∫ z : ℝ × ℝ, f z.1 * f (z.1 + z.2) ∂(volume.prod volume) := by
    rw [integral_prod_symm _ hshear]
    rfl
  have h2 : ∫ z : ℝ × ℝ, f z.1 * f (z.1 + z.2) ∂(volume.prod volume)
      = ∫ u, f u * ∫ y, f (u + y) := by
    rw [integral_prod _ hshear]
    congr 1; funext u
    dsimp only
    rw [integral_const_mul]
  rw [h1, h2]
  have h3 : ∀ u : ℝ, ∫ y, f (u + y) = ∫ y, f y := fun u => integral_add_left_eq_self f u
  simp_rw [h3]
  rw [integral_mul_const, sq]

/-- `∫_{y≥0} g = ½ ∫ g` for even integrable `g`. -/
theorem integral_Ici_eq_half_of_even {g : ℝ → ℝ} (hg : Integrable g) (heven : ∀ y, g (-y) = g y) :
    ∫ y in Ici (0 : ℝ), g y = (∫ y, g y) / 2 := by
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Ioi (a := (0 : ℝ))) hg
  rw [Set.compl_Ioi] at hsplit
  have hneg : ∫ y in Iic (0 : ℝ), g y = ∫ y in Ioi (0 : ℝ), g y := by
    rw [show (0 : ℝ) = -0 by ring, ← integral_comp_neg_Ioi]
    simp only [neg_zero]
    congr 1; funext y; rw [heven]
  rw [integral_Ici_eq_integral_Ioi]
  linarith

/-- **the mass of `g`**: `∫ g = (aL)²` and `∫_{y≥0} g = ½(aL)²` (Fubini). -/
theorem Valid.integral_gQ (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    ∫ y, P.gQ y = (P.aQ * P.LB) ^ 2 := by
  have hW := hP.admWindow hw
  have e : P.aQ * P.LB = ∫ u, P.phiQ u ^ 2 := by
    rw [hP.aQ_eq_av, Zeta23.AdmWindow.av, inv_mul_eq_div, div_mul_cancel₀ _ hP.LB_pos.ne']
  rw [e, gQ_eq_gv]
  exact integral_autocorr_eq_sq (hW.integrable_pow (by norm_num))

theorem Valid.integral_gQ_Ici (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    ∫ y in Ici (0 : ℝ), P.gQ y = (P.aQ * P.LB) ^ 2 / 2 := by
  have hW := hP.admWindow hw
  have hint : Integrable P.gQ := by
    rw [gQ_eq_gv]
    exact hW.gv_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -P.LB) (b := P.LB))
        (fun y hy => by
          rw [Function.mem_support] at hy
          by_contra hmem
          apply hy
          apply hW.gv_eq_zero
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
          rcases hmem with h | h
          · rw [abs_of_neg (by linarith [hW.L_pos])]; linarith
          · rw [abs_of_pos (by linarith [hW.L_pos])]; linarith))
  rw [integral_Ici_eq_half_of_even hint (fun y => by rw [gQ_eq_gv]; exact hW.gv_even y),
    hP.integral_gQ hw]

/-! ## §6 Poisson and the hat normalisation -/

/-- [lem:poisson] "in particular" for the design window: `Σ_k φ̂(γ − τ_k)² = aL²`
(`Zeta23.ZeroSide.PoissonSq`), from `AdmWindow.hasSum_vHatR_mul`. -/
theorem Valid.poissonSq (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) :
    Zeta23.ZeroSide.PoissonSq P.T P.toParams := by
  intro γ
  have hW := hP.admWindow hw
  have h := hW.hasSum_vHatR_mul P.T γ γ
  rw [sub_self, hW.VPhiR_zero] at h
  have ha : P.toParams.a P.T * P.toParams.L P.T ^ 2
      = P.LB * (Zeta23.AdmWindow.av P.phiQ P.LB * P.LB) := by
    rw [hP.toParams_L, ← hP.aQ_eq_av]; unfold aQ; ring
  rw [ha]
  convert h using 1
  funext k
  rw [hP.tau_eq k, sq]
  rfl

/-- `aL² > 0` for the design window. -/
theorem Valid.aLsq_pos (hP : P.Valid) : 0 < P.toParams.a P.T * P.toParams.L P.T ^ 2 := by
  rw [hP.toParams_L]
  exact mul_pos hP.aQ_pos (pow_pos hP.LB_pos 2)

/-! ## §7 the Gevrey bound and the §7.1 envelope for the product window -/

/-- `φ ∈ C^∞` when the ramp is a Gevrey profile. -/
theorem Valid.phiQ_smooth (hP : P.Valid) (hwL : 2 * P.w ≤ P.LB) {A B : ℝ}
    (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P.phiQ := by
  rw [hP.phiQ_eq]
  exact (Zeta23.ProductWindow.polyQ_contDiff P.prof P.LL _).mul
    (Zeta23.ProductWindow.phi_contDiff_top hϱ hP.w_pos hwL)

/-- `B′ > 0`. -/
theorem Valid.gevreyBprod_pos (hP : P.Valid) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    0 < P.gevreyBprod A B := by
  unfold gevreyBprod
  have hLL := hP.LL_pos
  have hw := hP.w_pos
  have hl := hP.lam_pos
  have hM0 := hP.profM_zero_ge
  have hS1 : P.profM 0 * (P.w / (P.LL * A)) ^ 0
      ≤ ∑ j ∈ Finset.range (P.prof.natDegree + 1), P.profM j * (P.w / (P.LL * A)) ^ j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hP.profM_nonneg j) (by positivity))
      (Finset.mem_range.mpr (Nat.succ_pos _))
  have hS2 : P.profM 0 * (P.lam / A) ^ 0
      ≤ ∑ j ∈ Finset.range (P.prof.natDegree + 1), P.profM j * (P.lam / A) ^ j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hP.profM_nonneg j) (by positivity))
      (Finset.mem_range.mpr (Nat.succ_pos _))
  simp only [pow_zero, mul_one] at hS1 hS2
  nlinarith [mul_le_mul_of_nonneg_left hS1 hB.le]

/-- **the Gevrey ramp bound for the design window** (`Zeta23.ProductWindow.gevrey_polyQ_mul_phi`):
`P.toParams.GevreyPhiBound P.T 2 A (gevreyBprod A B)` from `GevreyProfile 2 A B` of the RAMP.
Replaces `Zeta23.Params.gevreyPhiBound_of_profile`, which needs `GevreyProfile … toParams.ϱ`
(false for the realising profile). -/
theorem Valid.gevreyPhiBound (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {A B : ℝ}
    (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) :
    P.toParams.GevreyPhiBound P.T 2 A (P.gevreyBprod A B) where
  one_lt := by norm_num
  A_pos := hϱ.A_pos
  B_pos := hP.gevreyBprod_pos hϱ.A_pos hϱ.B_pos
  smooth := by
    have hsm := hP.phiQ_smooth (by linarith [hP.w_pos]) hϱ
    exact Complex.ofRealCLM.contDiff.comp hsm
  bound := by
    intro k hk
    have hsm := hP.phiQ_smooth (by linarith [hP.w_pos]) hϱ
    rw [Zeta23.Taper.iteratedDeriv_ofReal_comp (f := P.toParams.phi P.T) hsm k]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hcore := hP.LB_div_two_LL
    have h := Zeta23.ProductWindow.gevrey_polyQ_mul_phi (L := P.LB) (w := P.w) hϱ hP.w_pos
      (by linarith [hP.w_pos]) P.prof hP.LL_pos P.profM
      (fun j t ht => by rw [hcore] at ht; exact abs_eval_le_profM P j ht) hk
    rw [hP.LB_div_LL] at h
    have e : P.phiQ = fun u => P.prof.eval (u / P.LL) * Zeta23.Taper.phi P.ϱ P.LB P.w u :=
      hP.phiQ_eq
    rw [← phiQ_eq_toParams_phi, e]
    exact h

/-- **§7.1's envelope for the design window**: with the ramp `GevreyProfile 2 A B`,
`‖φ̂(z)‖ ≤ e²·max(2B′w, L)·e^{|Im z|·L/2}·exp(−(2/e)√(w‖z‖/A))` for every `z ∈ ℂ`, `B′ =
gevreyBprod A B`. The product-window twin of `Zeta23.Params.norm_phiHat_le_gevrey`. -/
theorem Valid.norm_phiHat_le_gevrey (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {A B : ℝ}
    (hϱ : Zeta23.Taper.GevreyProfile 2 A B P.ϱ) (z : ℂ) :
    ‖P.toParams.phiHat P.T z‖
      ≤ Real.exp 2 * max (2 * P.gevreyBprod A B * P.w) P.LB
        * Real.exp (|z.im| * (P.LB / 2))
        * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A)) := by
  have hG := hP.gevreyPhiBound hw hϱ
  have hsupp : ∀ u, (fun u : ℝ => (P.phiQ u : ℂ)) u ≠ 0 → |u| ≤ P.LB / 2 := by
    intro u hu
    have : P.phiQ u ≠ 0 := by
      intro h; apply hu; simp [h]
    have hmem := hP.phiQ_support_subset (Function.mem_support.mpr this)
    rw [Set.mem_Icc] at hmem
    rw [abs_le]; exact hmem
  have hbound : ∀ k : ℕ, 1 ≤ k →
      ∫ u, ‖iteratedDeriv k (fun u : ℝ => (P.phiQ u : ℂ)) u‖
        ≤ 2 * P.gevreyBprod A B * P.w * (A / P.w) ^ k * (k : ℝ) ^ ((2:ℝ) * k) :=
    fun k hk => hG.bound k hk
  have hL1' : ∫ u, ‖(P.phiQ u : ℂ)‖ ≤ 2 * (P.LB / 2) := by
    rw [show 2 * (P.LB / 2) = P.LB by ring]
    exact hP.integral_norm_phiQ_le hw
  have h := Zeta23.Taper.norm_paperFT_le_gevrey (Λ := P.LB / 2) hϱ.A_pos
    (hP.gevreyBprod_pos hϱ.A_pos hϱ.B_pos) hP.w_pos (by linarith [hP.LB_pos]) hG.smooth hsupp
    hL1' hbound z
  calc ‖P.toParams.phiHat P.T z‖
      = ‖Zeta23.paperFT (fun u : ℝ => (P.phiQ u : ℂ)) z‖ := rfl
    _ ≤ Real.exp 2 * max (2 * P.gevreyBprod A B * P.w) (2 * (P.LB / 2))
          * Real.exp (|z.im| * (P.LB / 2))
          * Real.exp (-(2 / Real.exp 1) * Real.sqrt (P.w * ‖z‖ / A)) := h
    _ = _ := by rw [show 2 * (P.LB / 2) = P.LB by ring]

/-! ## §8 the `Zeta23.Params.*`-shaped facts, re-derived for the design window

These are the flat facade's statements (`Zeta23/Taper.lean`, under `Params.ValidQ`) in the
shape the rest of `ZetaQ` consumes, now proved from `Valid.admWindow` (so under `P.Valid` and
`8w ≤ L`), with the window constant `cWin` where the facade had `crho`. -/

@[simp] theorem toParams_w (P : ParamsQ) : P.toParams.w = P.w := rfl

section Wrappers
variable (hP : P.Valid) (hw : 8 * P.w ≤ P.LB)
include hP hw

theorem Valid.gQ_continuous : Continuous P.gQ := by
  rw [gQ_eq_gv]; exact (hP.admWindow hw).gv_continuous
theorem Valid.gQ_nonneg (y : ℝ) : 0 ≤ P.gQ y := (hP.admWindow hw).gv_nonneg y
theorem Valid.gQ_eq_zero {y : ℝ} (hy : P.LB ≤ |y|) : P.gQ y = 0 :=
  (hP.admWindow hw).gv_eq_zero hy
theorem Valid.gQ_le_Aphi (y : ℝ) : P.gQ y ≤ P.toParams.Aphi P.T y :=
  (hP.admWindow hw).gv_le_Av y
theorem Valid.Aphi_le (y : ℝ) : P.toParams.Aphi P.T y ≤ max (P.LB - |y|) 0 :=
  (hP.admWindow hw).Av_le y
/-- [eq:gbounds]'s UPPER envelope `g(y) ≤ (L − |y|)₊` (unchanged by F58). -/
theorem Valid.gQ_le_env (y : ℝ) : P.gQ y ≤ max (P.LB - |y|) 0 :=
  (hP.gQ_le_Aphi hw y).trans (hP.Aphi_le hw y)
theorem Valid.gQ_even (y : ℝ) : P.gQ (-y) = P.gQ y := (hP.admWindow hw).gv_even y
theorem Valid.gQ_zero : P.gQ 0 = P.bQ * P.LB := by
  rw [hP.bQ_eq_bv]; exact (hP.admWindow hw).gv_zero
theorem Valid.gQ_hasCompactSupport : HasCompactSupport P.gQ := by
  have hW := hP.admWindow hw
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -P.LB) (b := P.LB))
    fun y hy => ?_
  rw [Function.mem_support] at hy
  by_contra hmem
  apply hy
  apply hP.gQ_eq_zero hw
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  rcases hmem with h | h
  · rw [abs_of_neg (by linarith [hW.L_pos])]; linarith
  · rw [abs_of_pos (by linarith [hW.L_pos])]; linarith
theorem Valid.gQ_integrable : Integrable P.gQ :=
  (hP.gQ_continuous hw).integrable_of_hasCompactSupport (hP.gQ_hasCompactSupport hw)

theorem Valid.PhiQ_even (r : ℝ) : P.PhiQ (-r) = P.PhiQ r := (hP.admWindow hw).VPhiR_even r
theorem Valid.PhiQ_continuous : Continuous P.PhiQ := (hP.admWindow hw).VPhiR_continuous
theorem Valid.PhiQ_contDiff_one : ContDiff ℝ 1 P.PhiQ := (hP.admWindow hw).VPhiR_contDiff_one
theorem Valid.PhiQ_zero : P.PhiQ 0 = P.aQ * P.LB := by
  rw [hP.aQ_eq_av]; exact (hP.admWindow hw).VPhiR_zero
theorem Valid.integrable_PhiQ_sq : Integrable (fun x => P.PhiQ x ^ 2) :=
  (hP.admWindow hw).integrable_VPhiR_sq
theorem Valid.integrable_PhiQ_sq_mul_abs : Integrable (fun x => P.PhiQ x ^ 2 * |x|) :=
  (hP.admWindow hw).integrable_VPhiR_sq_mul_abs
theorem Valid.integral_PhiQ_sq_mul_cos (y : ℝ) :
    ∫ x, P.PhiQ x ^ 2 * Real.cos (x * y) = 2 * Real.pi * P.gQ y :=
  (hP.admWindow hw).integral_VPhiR_sq_mul_cos y
theorem Valid.integral_PhiQ_sq : ∫ x, P.PhiQ x ^ 2 = 2 * Real.pi * P.bQ * P.LB := by
  rw [hP.bQ_eq_bv]; exact (hP.admWindow hw).integral_VPhiR_sq
theorem Valid.abs_PhiQ_le_L (r : ℝ) : |P.PhiQ r| ≤ P.LB := (hP.admWindow hw).abs_VPhiR_le_L r
theorem Valid.abs_PhiQ_mul_abs_le (r : ℝ) : |P.PhiQ r| * |r| ≤ 2 :=
  (hP.admWindow hw).abs_VPhiR_mul_abs_le r
theorem Valid.abs_PhiQ_mul_sq_le (r : ℝ) : |P.PhiQ r| * r ^ 2 ≤ P.cWin / P.w :=
  (hP.admWindow hw).abs_VPhiR_mul_sq_le r
/-- `|Φ| ≤ ψ_C` with the window constant `cWin`. -/
theorem Valid.abs_PhiQ_le_psiC (r : ℝ) : |P.PhiQ r| ≤ Zeta23.PsiC.psiC P.cWin P.LB P.w r := by
  have h := (hP.admWindow hw).abs_VPhiR_le_psiA (P.toParams.toSetting P.T) hP.toParams_L rfl r
  rw [← Zeta23.PsiC.psiC_eq_psiA] at h
  simp only [Zeta23.Params.toSetting_L, Zeta23.Params.toSetting_w, hP.toParams_L] at h
  exact h
theorem Valid.abs_phiHatR_le_psiC (r : ℝ) :
    |P.toParams.phiHatR P.T r| ≤ Zeta23.PsiC.psiC P.cWin P.LB P.w r := by
  have h := (hP.admWindow hw).abs_vHatR_le_psiA (P.toParams.toSetting P.T) hP.toParams_L rfl r
  rw [← Zeta23.PsiC.psiC_eq_psiA] at h
  simp only [Zeta23.Params.toSetting_L, Zeta23.Params.toSetting_w, hP.toParams_L] at h
  exact h
/-- [eq:psiints] for `Φ` with the window constant: `∫Φ²|x| ≤ 8 + 8 log(c_W L/4w)`. -/
theorem Valid.integral_PhiQ_sq_mul_abs_le :
    ∫ x, P.PhiQ x ^ 2 * |x| ≤ 8 + 8 * Real.log (P.cWin * P.LB / (4 * P.w)) :=
  Zeta23.PsiC.integral_sq_mul_abs_le_of_le_psi hP.four_le_cWin hP.one_le_w hw
    (hP.abs_PhiQ_le_psiC hw)
theorem Valid.integrable_PhiQ_sq_mul_sq : Integrable (fun x => P.PhiQ x ^ 2 * x ^ 2) :=
  Zeta23.PsiC.integrable_sq_mul_sq_of_bounds (hP.PhiQ_continuous hw)
    (div_nonneg hP.cWin_pos.le hP.w_pos.le) (hP.abs_PhiQ_mul_abs_le hw) (hP.abs_PhiQ_mul_sq_le hw)
theorem Valid.integral_PhiQ_sq_mul_sq_le :
    ∫ x, P.PhiQ x ^ 2 * x ^ 2 ≤ 8 + 2 * (P.cWin / P.w) ^ 2 :=
  Zeta23.PsiC.integral_sq_mul_sq_le_of_bounds (div_nonneg hP.cWin_pos.le hP.w_pos.le)
    (hP.abs_PhiQ_mul_abs_le hw) (hP.abs_PhiQ_mul_sq_le hw)
theorem Valid.phiQ_sq_integrable : Integrable (fun u => P.phiQ u ^ 2) :=
  (hP.admWindow hw).integrable_pow (by norm_num)

end Wrappers

/-! ## §9 the FLAT taper `prof = 1` (the `Zones` witnesses): its moment floors -/

/-- the profile class at the flat profile `p = 1`. -/
theorem profileQ_one (lam : ℝ) : ProfileQ 1 lam where
  even := fun t => by simp
  bulk := fun t _ => by norm_num
  le_one := fun t _ => by simp
  antitone := by intro x _ y _ _; simp

/-- at `prof = 1` the realising profile IS the ramp: `toParams = ⟨ϱ, L/l T, w⟩`. -/
theorem toParams_flat (P : ParamsQ) (h : P.prof = 1) :
    P.toParams = ⟨P.ϱ, P.LB / Zeta23.l P.T, P.w⟩ := by
  unfold toParams; rw [h]; simp only [Polynomial.eval_one, one_mul]

/-- the two `Valid` moment floors for the FLAT taper, from [R]'s `three_quarters_le_b`. -/
theorem flat_moment_floors {P : ParamsQ} (hϱ : Zeta23.TaperProfile P.ϱ) (hprof : P.prof = 1)
    (hw1 : 1 ≤ P.w) (hwL : 8 * P.w ≤ P.LB) (hl : 0 < Zeta23.l P.T) (hLB : 0 < P.LB) :
    3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hflat : P.toParams = ⟨P.ϱ, P.LB / Zeta23.l P.T, P.w⟩ := toParams_flat P hprof
  have hL : P.toParams.L P.T = P.LB := P.toParams_L hl.ne'
  have hPQ : (⟨P.ϱ, P.LB / Zeta23.l P.T, P.w⟩ : Zeta23.Params).ValidQ :=
    ⟨hϱ, div_pos hLB hl, hw1⟩
  have hwL' : 8 * (⟨P.ϱ, P.LB / Zeta23.l P.T, P.w⟩ : Zeta23.Params).w
      ≤ (⟨P.ϱ, P.LB / Zeta23.l P.T, P.w⟩ : Zeta23.Params).L P.T := by
    rw [← hflat, hL]; exact hwL
  have hb := Zeta23.Params.three_quarters_le_b hPQ hwL'
  have hba := Zeta23.Params.b_le_a hPQ hwL'
  unfold aQ bQ
  rw [hflat]
  exact ⟨hb.trans hba, by linarith⟩

end ParamsQ
end ZetaQ

end
