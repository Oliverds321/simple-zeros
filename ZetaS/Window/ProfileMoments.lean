/-
rh72/lean_work/L0_2/ProfileMoments.lean — nodes W5 (moments a, b of the window vs the profile) and W7
(eventual `LocalHypsCore`) for an ARBITRARY profile ψ with 0 ≤ ψ ≤ 1 on [−1/2, 1/2] (no monotonicity), realised
on the tree's taper as `P.phiV ψ T = √(max 0 (ψ(u/L)))·φ(u)` (AF (2.7); draft eq:zeta-window, sec_zeta.tex l.174).

Generalises XiPrime/QuarticWindow/Moments.lean (`aQ_close`, `bQ_close`, `bV_quartic_ge_half`,
`localHypsCoreQ_eventually`) from `vQuartic` to any `CoreProfile`; the window-specific inputs are only
continuity and the two core bounds (the square is clamped to [0,1] off the core, where the taper vanishes).
  av_close : |L⁻¹∫φ² − ∫ψ|  ≤ 2w/L,     bv_close : |L⁻¹∫φ⁴ − ∫ψ²| ≤ 2w/L      (all 8w ≤ L),
  localHypsCore_eventually : eventual admissibility + ∫ψ² > 1/2  ⟹  ∃ T₀, ∀ T ≥ T₀, LocalHypsCore c … .
No `sorry`.
-/
import Zeta23.XiPrime.QuarticWindow.Moments

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace ZetaS
namespace ProfileMoments

open Zeta23 Zeta23.XiPrime

/-- a window profile on the core: continuous, `0 ≤ ψ ≤ 1` on `[−1/2, 1/2]` (prop:zeta-AF, l.207, minus C²,
which only admissibility uses). -/
structure CoreProfile (v : ℝ → ℝ) : Prop where
  cont : Continuous v
  nonneg : ∀ s, |s| ≤ 1 / 2 → 0 ≤ v s
  le_one : ∀ s, |s| ≤ 1 / 2 → v s ≤ 1

/-- the modulating factor of `P.phiV v T`. -/
def fV (v : ℝ → ℝ) (L u : ℝ) : ℝ := Real.sqrt (max 0 (v (u / L)))

/-- the clamped square `min 1 (max 0 (v(u/L)))` (= `fV²` on the core). -/
def mV (v : ℝ → ℝ) (L u : ℝ) : ℝ := min 1 (max 0 (v (u / L)))

theorem phiV_eq_phiM (P : Params) (v : ℝ → ℝ) (T : ℝ) :
    P.phiV v T = phiM (fV v (P.L T)) P.ϱ (P.L T) P.w := rfl

variable {v : ℝ → ℝ} {ϱ : ℝ → ℝ} {L w : ℝ}

lemma mV_nonneg (u : ℝ) : 0 ≤ mV v L u := le_min zero_le_one (le_max_left _ _)
lemma mV_le_one (u : ℝ) : mV v L u ≤ 1 := min_le_left _ _
lemma abs_mV_le_one (u : ℝ) : |mV v L u| ≤ 1 := by
  rw [abs_of_nonneg (mV_nonneg u)]; exact mV_le_one u

lemma mV_continuous (hv : CoreProfile v) : Continuous (mV v L) := by
  unfold mV
  exact continuous_const.min (continuous_const.max (hv.cont.comp (continuous_id.div_const L)))

lemma core_abs (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |u / L| ≤ 1 / 2 := by
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith

lemma mV_core (hv : CoreProfile v) (hL : 0 < L) {u : ℝ} (hu : u ∈ Icc (-(L / 2)) (L / 2)) :
    mV v L u = v (u / L) := by
  have hc := core_abs hL (abs_le.mpr ⟨hu.1, hu.2⟩)
  unfold mV
  rw [max_eq_right (hv.nonneg _ hc), min_eq_right (hv.le_one _ hc)]

lemma phiV_sq_eq (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (u : ℝ) :
    phiM (fV v L) ϱ L w u ^ 2 = mV v L u * Taper.phi ϱ L w u ^ 2 := by
  rcases le_or_gt (L / 2) |u| with hu | hu
  · simp only [phiM, Taper.phi_eq_zero hϱ hw hu]; ring
  · have hmem : u ∈ Icc (-(L / 2)) (L / 2) := abs_le.mp hu.le
    rw [phiM, mul_pow, mV_core hv hL hmem, fV, Real.sq_sqrt (le_max_left _ _),
      max_eq_right (hv.nonneg _ (core_abs hL hu.le))]

lemma phiV_pow_four_eq (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (u : ℝ) :
    phiM (fV v L) ϱ L w u ^ 4 = mV v L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by
  have : phiM (fV v L) ϱ L w u ^ 4 = (phiM (fV v L) ϱ L w u ^ 2) ^ 2 := by ring
  rw [this, phiV_sq_eq hv hϱ hw hL]; ring

/-- **W5a: `|a_T − ∫ψ| ≤ 2w/L`.** -/
theorem av_close (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |AdmWindow.av (phiM (fV v L) ϱ L w) L - ∫ s in (-(1:ℝ)/2)..(1/2), v s| ≤ 2 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hsub : (∫ s in (-(1:ℝ)/2)..(1/2), v s) = L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mV v L u := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => mV_core hv hL hu),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2), integral_scale hL]
    field_simp
  have hwin : ∫ u, phiM (fV v L) ϱ L w u ^ 2 = ∫ u, mV v L u * Taper.phi ϱ L w u ^ 2 :=
    integral_congr_ae (ae_of_all _ fun u => phiV_sq_eq hv hϱ hw0 hL u)
  unfold AdmWindow.av
  rw [hwin, hsub]
  have hcore := edge_estimate (h := mV v L) (p := fun u => Taper.phi ϱ L w u ^ 2) hL hw0 hwL'
    abs_mV_le_one (fun u => sq_nonneg _)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
        _ = 1 := one_pow 2)
    (fun u hu => by show Taper.phi ϱ L w u ^ 2 = 1; rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by show Taper.phi ϱ L w u ^ 2 = 0; rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow two_ne_zero])
    ((Taper.phi_continuous hϱ hw0 hwL').pow 2) (mV_continuous hv)
  have e : L⁻¹ * (∫ u, mV v L u * Taper.phi ϱ L w u ^ 2) - L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mV v L u
      = L⁻¹ * ((∫ u, mV v L u * Taper.phi ϱ L w u ^ 2) - ∫ u in Set.Icc (-(L/2)) (L/2), mV v L u) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L⁻¹)]
  calc L⁻¹ * |(∫ u, mV v L u * Taper.phi ϱ L w u ^ 2) - ∫ u in Set.Icc (-(L/2)) (L/2), mV v L u|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 2 * w / L := by rw [div_eq_inv_mul]

/-- **W5b: `|b_T − ∫ψ²| ≤ 2w/L`.** -/
theorem bv_close (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |AdmWindow.bv (phiM (fV v L) ϱ L w) L - ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2| ≤ 2 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hsub : (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) = L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mV v L u ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Icc
        (fun u hu => by show mV v L u ^ 2 = v (u / L) ^ 2; rw [mV_core hv hL hu]),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2),
      integral_scale (g := fun s => v s ^ 2) hL]
    field_simp
  have hwin : ∫ u, phiM (fV v L) ϱ L w u ^ 4 = ∫ u, mV v L u ^ 2 * Taper.phi ϱ L w u ^ 4 :=
    integral_congr_ae (ae_of_all _ fun u => phiV_pow_four_eq hv hϱ hw0 hL u)
  unfold AdmWindow.bv
  rw [hwin, hsub]
  have hcore := edge_estimate (h := fun u => mV v L u ^ 2) (p := fun u => Taper.phi ϱ L w u ^ 4) hL hw0 hwL'
    (fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc mV v L u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (mV_nonneg u) (mV_le_one u) 2
        _ = 1 := one_pow 2)
    (fun u => by positivity)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 4
        _ = 1 := one_pow 4)
    (fun u hu => by show Taper.phi ϱ L w u ^ 4 = 1; rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by show Taper.phi ϱ L w u ^ 4 = 0; rw [Taper.phi_eq_zero hϱ hw0 hu]; norm_num)
    ((Taper.phi_continuous hϱ hw0 hwL').pow 4) ((mV_continuous hv).pow 2)
  have e : L⁻¹ * (∫ u, mV v L u ^ 2 * Taper.phi ϱ L w u ^ 4) - L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mV v L u ^ 2
      = L⁻¹ * ((∫ u, mV v L u ^ 2 * Taper.phi ϱ L w u ^ 4)
          - ∫ u in Set.Icc (-(L/2)) (L/2), mV v L u ^ 2) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L⁻¹)]
  calc L⁻¹ * |(∫ u, mV v L u ^ 2 * Taper.phi ϱ L w u ^ 4) - ∫ u in Set.Icc (-(L/2)) (L/2), mV v L u ^ 2|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 2 * w / L := by rw [div_eq_inv_mul]

/-! ### W7: the eventual `LocalHypsCore` for any profiled family -/

/-- `b_T ≥ 1/2` as soon as `L ≥ 2w/(∫ψ² − 1/2)` (and `8w ≤ L`). -/
theorem bv_ge_half (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (hb : 1 / 2 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)
    (hLb : 2 * w / ((∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) - 1 / 2) ≤ L) :
    1 / 2 ≤ AdmWindow.bv (phiM (fV v L) ϱ L w) L := by
  have hL : 0 < L := by linarith
  have h := bv_close hv hϱ hw hwL
  set B := ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2
  have hB : 0 < B - 1 / 2 := by linarith
  have hq : 2 * w / L ≤ B - 1 / 2 := by
    rw [div_le_iff₀ hL]
    rw [div_le_iff₀ hB] at hLb
    linarith
  linarith [(abs_le.mp h).1]

/-- **W7 (generic): eventual admissibility + `∫ψ² > 1/2` ⟹ the §5 `LocalHypsCore` for all large T.** -/
theorem localHypsCore_eventually {P : Params} (hP : P.Valid) (hv : CoreProfile v) {c K : ℝ} (hK : 8 ≤ K)
    (hadm : ∀ T, K * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w c)
    (hb : 1 / 2 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      PrimeSide.LocalHypsCore c (P.toSetting T) (AdmWindow.localFun (P.phiV v T) (P.L T)) := by
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
    filter_upwards [hL.eventually_ge_atTop 0] with T h
    simpa [Params.X] using Real.one_le_exp h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
    ((hL.eventually_ge_atTop (K * P.w)).and ((hL.eventually_ge_atTop
      (2 * P.w / ((∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) - 1 / 2))).and hX)))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, hK8, hLb, hX1⟩ := hT₀ T hT
  have hw := hP.one_le_w
  have h8 : 8 * P.w ≤ P.L T := by nlinarith
  exact AdmWindow.localHypsCore (P.toSetting T) (hadm T hK8) hP.lam_pos hP.lam_le_one h1 hX1
    (by rw [phiV_eq_phiM]; exact bv_ge_half hv hP.taper hw h8 hb hLb)

end ProfileMoments
end ZetaS

end

#print axioms ZetaS.ProfileMoments.av_close
#print axioms ZetaS.ProfileMoments.bv_close
#print axioms ZetaS.ProfileMoments.localHypsCore_eventually
