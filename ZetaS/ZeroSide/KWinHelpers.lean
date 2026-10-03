/-
lean_work/L3_2/KWinHelpers.lean — shared helpers for nodes Z4 (`kWin_close`) and Z5 (`kWin_dominated`)
(agent L3_2, 28 Sep 2026). Namespace `ZetaS.KWinHelpers`. No `sorry`.

For the tree's window φ = `phiM (fV ψ L) ϱ L w` (= `P.phiV ψ T` at `L = P.L T`, `w = P.w`, `ϱ = P.ϱ`, by `rfl`):
  * `VPhiR_eq_integral`   : `VPhiR v r = ∫ v(u)² cos(r u) du` (real part of the paper Fourier transform);
  * `kWin_eq`             : `kWin φ L t = Nφ(t)/Nφ(0)`, `Nφ(t) = ∫ mV(u) cos(2πtu/L) ϱ_L(u)² du` (φ² = mV·ϱ_L²);
  * `kPsi_eq`             : `kPsi ψ t = Nψ(t)/Nψ(0)`, `Nψ(t) = ∫_{[−L/2,L/2]} mV(u) cos(2πtu/L) du` (u = Ls);
  * `Nphi_Npsi_close`     : `|Nφ(t) − Nψ(t)| ≤ 2w` (the ramp occupies `2w` of `[−L/2, L/2]`; tree `edge_estimate`);
  * `isPosDefKernel_of_density` : Bochner, easy direction — `t ↦ ∫_S g(u) cos(κtu) du` is a positive-definite kernel
    whenever `g ≥ 0` on `S` (Σ cᵢcⱼ cos(aᵢ − aⱼ) = (Σ cᵢ cos aᵢ)² + (Σ cᵢ sin aᵢ)²);
  * `kWin_close_at`       : `|kWin φ L t − kPsi ψ t| ≤ 16 w/L` (all t, all 8w ≤ L, if ∫ψ > 1/2);
  * `kWin_dominated_at`   : `(1 + 8w/L) kPsi ψ − kWin φ L` is a positive-definite kernel (same hypotheses).
-/
import ZetaS.InterfacesV2
import ZetaS.Window.ProfileMoments

noncomputable section

open Real Set MeasureTheory Filter Topology
open scoped Matrix

namespace ZetaS
namespace KWinHelpers

open Zeta23 Zeta23.XiPrime ProfileMoments

/-! ### Bochner, easy direction -/

lemma sum_sum_cos_sub {n : ℕ} (c a : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * Real.cos (a i - a j)
      = (∑ i, c i * Real.cos (a i)) ^ 2 + (∑ i, c i * Real.sin (a i)) ^ 2 := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub]; ring

/-- **Bochner (easy direction).** A nonnegative density on `S` gives a positive-definite cosine kernel. -/
theorem isPosDefKernel_of_density {S : Set ℝ} (hS : MeasurableSet S) {g : ℝ → ℝ}
    (hg : IntegrableOn g S) (hg0 : ∀ u ∈ S, 0 ≤ g u) (κ : ℝ) :
    IsPosDefKernel (fun t => ∫ u in S, g u * Real.cos (κ * t * u)) := by
  intro n x
  have hint : ∀ s : ℝ, IntegrableOn (fun u => g u * Real.cos (s * u)) S := fun s =>
    Integrable.mono' hg.norm
      (hg.aestronglyMeasurable.mul
        (by fun_prop : Continuous fun u : ℝ => Real.cos (s * u)).aestronglyMeasurable)
      (ae_of_all _ fun u => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [kerMat, Matrix.of_apply, star_trivial]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    rw [show κ * (x j - x i) * u = -(κ * (x i - x j) * u) by ring, Real.cos_neg]
  · have e1 : ∀ u, g u * ((∑ i, c i * Real.cos (κ * x i * u)) ^ 2
          + (∑ i, c i * Real.sin (κ * x i * u)) ^ 2)
          = ∑ i, ∑ j, c i * c j * (g u * Real.cos (κ * (x i - x j) * u)) := by
      intro u
      rw [← sum_sum_cos_sub, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show κ * (x i - x j) * u = κ * x i * u - κ * x j * u by ring]; ring
    have hq : star c ⬝ᵥ (kerMat (fun t => ∫ u in S, g u * Real.cos (κ * t * u)) x *ᵥ c)
        = ∫ u in S, g u * ((∑ i, c i * Real.cos (κ * x i * u)) ^ 2
          + (∑ i, c i * Real.sin (κ * x i * u)) ^ 2) := by
      simp_rw [e1]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hint _).const_mul _))]
      simp only [dotProduct, Matrix.mulVec, kerMat, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hint _).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]; ring
    rw [hq]
    exact setIntegral_nonneg hS fun u hu => mul_nonneg (hg0 u hu) (by positivity)

/-! ### `VPhiR` as a cosine integral -/

lemma VPhiR_eq_integral {v : ℝ → ℝ} (hc : Continuous v) (hv : Integrable (fun u => v u ^ 2)) (r : ℝ) :
    AdmWindow.VPhiR v r = ∫ u, v u ^ 2 * Real.cos (r * u) := by
  have hrot : ∀ u : ℝ, Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by
    intro u; push_cast; ring
  have hint : Integrable (fun u : ℝ =>
      (((v u) ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    refine (hv.ofReal (𝕜 := ℂ)).norm.mono' ?_ (ae_of_all _ fun u => ?_)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [norm_mul, hrot u, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact le_rfl
  unfold AdmWindow.VPhiR AdmWindow.VPhi
  rw [paperFT_def, ← integral_re_C hint]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [hrot u, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-! ### The two numerators -/

/-- numerator of `kWin` (u-variable, over ℝ; `h·p` form for the tree's `edge_estimate`). -/
def Nphi (v ϱ : ℝ → ℝ) (L w t : ℝ) : ℝ :=
  ∫ u, (mV v L u * Real.cos (2 * π / L * t * u)) * Taper.phi ϱ L w u ^ 2

/-- numerator of `kPsi`, rescaled to the u-variable (`u = Ls`). -/
def Npsi (v : ℝ → ℝ) (L t : ℝ) : ℝ :=
  ∫ u in Icc (-(L / 2)) (L / 2), mV v L u * Real.cos (2 * π / L * t * u)

variable {v ϱ : ℝ → ℝ} {L w : ℝ}

lemma abs_ge_of_not_mem {u : ℝ} (hu : u ∉ Icc (-(L / 2)) (L / 2)) : L / 2 ≤ |u| := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with hc | hc
  · have := neg_abs_le u; linarith
  · have := le_abs_self u; linarith

lemma phiM_continuous (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phiM (fV v L) ϱ L w) := by
  unfold phiM fV
  exact (Real.continuous_sqrt.comp (continuous_const.max (hv.cont.comp (continuous_id.div_const L)))).mul
    (Taper.phi_continuous hϱ hw hwL)

lemma phiM_sq_integrable (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun u => phiM (fV v L) ϱ L w u ^ 2) := by
  refine ((phiM_continuous hv hϱ hw hwL).pow 2).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc fun u hu => ?_
  simp only [Pi.pow_apply, phiM, Taper.phi_eq_zero hϱ hw (abs_ge_of_not_mem hu), mul_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

lemma kWin_eq (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) (t : ℝ) :
    kWin (phiM (fV v L) ϱ L w) L t = Nphi v ϱ L w t / Nphi v ϱ L w 0 := by
  have hw0 : 0 < w := by linarith
  have hL : 0 < L := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  unfold kWin
  rw [VPhiR_eq_integral (phiM_continuous hv hϱ hw0 hwL') (phiM_sq_integrable hv hϱ hw0 hwL')]
  unfold Nphi
  congr 1
  · refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    rw [phiV_sq_eq hv hϱ hw0 hL u, show 2 * π * t / L * u = 2 * π / L * t * u by ring]; ring
  · refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    rw [phiV_sq_eq hv hϱ hw0 hL u]

lemma integral_psi_cos_eq (hv : CoreProfile v) (hL : 0 < L) (t : ℝ) :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), v s * Real.cos (2 * π * t * s) = L⁻¹ * Npsi v L t := by
  have hs := integral_scale (g := fun s => v s * Real.cos (2 * π * t * s)) hL
  rw [show (-(1:ℝ) / 2) = -(1 / 2 : ℝ) by ring] at hs
  have h1 : Npsi v L t = L * ∫ s in (-(1 / 2 : ℝ))..(1 / 2), v s * Real.cos (2 * π * t * s) := by
    unfold Npsi
    rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => by
        show mV v L u * Real.cos (2 * π / L * t * u) = v (u / L) * Real.cos (2 * π * t * (u / L))
        rw [mV_core hv hL hu, show 2 * π / L * t * u = 2 * π * t * (u / L) by ring]),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
    exact hs
  rw [h1, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]

lemma integral_psi_eq (hv : CoreProfile v) (hL : 0 < L) :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), v s = L⁻¹ * Npsi v L 0 := by
  rw [← integral_psi_cos_eq hv hL 0]
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]

lemma kPsi_eq (hv : CoreProfile v) (hL : 0 < L) (t : ℝ) :
    kPsi v t = Npsi v L t / Npsi v L 0 := by
  unfold kPsi
  rw [integral_psi_cos_eq hv hL t, integral_psi_eq hv hL]
  exact mul_div_mul_left _ _ (inv_ne_zero hL.ne')

lemma Nphi_Npsi_close (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) (t : ℝ) :
    |Nphi v ϱ L w t - Npsi v L t| ≤ 2 * w := by
  have hw0 : 0 < w := by linarith
  have hL : 0 < L := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  exact edge_estimate (h := fun u => mV v L u * Real.cos (2 * π / L * t * u))
    (p := fun u => Taper.phi ϱ L w u ^ 2) hL hw0 hwL'
    (fun u => by
      rw [abs_mul]
      exact mul_le_one₀ (abs_mV_le_one u) (abs_nonneg _) (abs_cos_le_one _))
    (fun u => sq_nonneg _)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
        _ = 1 := one_pow 2)
    (fun u hu => by show Taper.phi ϱ L w u ^ 2 = 1; rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by show Taper.phi ϱ L w u ^ 2 = 0; rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow two_ne_zero])
    ((Taper.phi_continuous hϱ hw0 hwL').pow 2) ((mV_continuous hv).mul (by fun_prop))

lemma Npsi_abs_le (hv : CoreProfile v) (t : ℝ) : |Npsi v L t| ≤ Npsi v L 0 := by
  unfold Npsi
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((mV_continuous hv).integrableOn_Icc) (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mV_nonneg u)]
  exact mul_le_of_le_one_right (mV_nonneg u) (abs_cos_le_one _)

/-- `Nφ(t)` as an integral over the core `[−L/2, L/2]`. -/
lemma Nphi_eq_set (hϱ : TaperProfile ϱ) (hw : 0 < w) (t : ℝ) :
    Nphi v ϱ L w t = ∫ u in Icc (-(L / 2)) (L / 2),
      (mV v L u * Real.cos (2 * π / L * t * u)) * Taper.phi ϱ L w u ^ 2 := by
  unfold Nphi
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro u hu
  rw [Taper.phi_eq_zero hϱ hw (abs_ge_of_not_mem hu)]; ring

/-! ### The algebra -/

lemma alg_close {x1 x2 D1 D2 L w : ℝ} (hL : 0 < L) (hD1 : L / 4 ≤ D1) (hD2 : 0 < D2)
    (h12 : |x1 - x2| ≤ 2 * w) (hD : |D1 - D2| ≤ 2 * w) (hx2 : |x2| ≤ D2) :
    |x1 / D1 - x2 / D2| ≤ 16 * w / L := by
  have hD1p : 0 < D1 := by linarith
  have hw0 : 0 ≤ w := by linarith [abs_nonneg (x1 - x2)]
  have hD' : |D2 - D1| ≤ 2 * w := by rwa [abs_sub_comm]
  have e : x1 / D1 - x2 / D2 = ((x1 - x2) * D2 + x2 * (D2 - D1)) / (D1 * D2) := by
    field_simp; ring
  have hDD : 0 < D1 * D2 := mul_pos hD1p hD2
  rw [e, abs_div, abs_of_pos hDD, div_le_iff₀ hDD]
  have h1 : |(x1 - x2) * D2 + x2 * (D2 - D1)| ≤ 4 * w * D2 := by
    calc |(x1 - x2) * D2 + x2 * (D2 - D1)| ≤ |(x1 - x2) * D2| + |x2 * (D2 - D1)| := abs_add_le _ _
      _ = |x1 - x2| * D2 + |x2| * |D2 - D1| := by rw [abs_mul, abs_mul, abs_of_pos hD2]
      _ ≤ 2 * w * D2 + D2 * (2 * w) := by gcongr
      _ = 4 * w * D2 := by ring
  have h2 : 4 * w ≤ 16 * w / L * D1 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]; nlinarith
  calc |(x1 - x2) * D2 + x2 * (D2 - D1)| ≤ 4 * w * D2 := h1
    _ ≤ 16 * w / L * D1 * D2 := by gcongr
    _ = 16 * w / L * (D1 * D2) := by ring

/-! ### The two node-level facts at one height -/

/-- the normalisers: `Nψ(0) = L∫ψ ≥ L/2` and `Nφ(0) ≥ L/4`. -/
lemma norms_bounds (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), v s) :
    L / 2 < Npsi v L 0 ∧ L / 4 ≤ Nphi v ϱ L w 0 := by
  have hL : 0 < L := by linarith
  have h0 := integral_psi_eq hv hL
  have hN : Npsi v L 0 = L * ∫ s in (-(1 / 2 : ℝ))..(1 / 2), v s := by
    rw [h0, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  have h2 : L / 2 < Npsi v L 0 := by rw [hN]; nlinarith
  refine ⟨h2, ?_⟩
  have hc := Nphi_Npsi_close hv hϱ hw hwL 0
  linarith [(abs_le.mp hc).1]

theorem kWin_close_at (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), v s) (t : ℝ) :
    |kWin (phiM (fV v L) ϱ L w) L t - kPsi v t| ≤ 16 * w / L := by
  have hL : 0 < L := by linarith
  obtain ⟨h2, h4⟩ := norms_bounds hv hϱ hw hwL ha
  rw [kWin_eq hv hϱ hw hwL, kPsi_eq hv hL]
  exact alg_close hL h4 (by linarith) (Nphi_Npsi_close hv hϱ hw hwL t)
    (Nphi_Npsi_close hv hϱ hw hwL 0) (Npsi_abs_le hv t)

theorem kWin_dominated_at (hv : CoreProfile v) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L)
    (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), v s) :
    IsPosDefKernel (fun t => (1 + 8 * w / L) * kPsi v t - kWin (phiM (fV v L) ϱ L w) L t) := by
  have hw0 : 0 < w := by linarith
  have hL : 0 < L := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  obtain ⟨h2, h4⟩ := norms_bounds hv hϱ hw hwL ha
  set D1 := Nphi v ϱ L w 0 with hD1
  set D2 := Npsi v L 0 with hD2
  have hD1p : 0 < D1 := by linarith
  have hD2p : 0 < D2 := by linarith
  set e := 8 * w / L with he
  set g : ℝ → ℝ := fun u => mV v L u * ((1 + e) / D2 - Taper.phi ϱ L w u ^ 2 / D1) with hg
  -- the density is nonnegative: (1 + e) D1 ≥ D1 + 2w ≥ D2
  have hdom : 1 / D1 ≤ (1 + e) / D2 := by
    have hc := Nphi_Npsi_close hv hϱ hw hwL 0
    have h8 : 2 * w ≤ e * D1 := by
      rw [he, div_mul_eq_mul_div, le_div_iff₀ hL]; nlinarith
    rw [← hD1, ← hD2] at hc
    rw [div_le_div_iff₀ hD1p hD2p]
    have hx : (1 + e) * D1 = D1 + e * D1 := by ring
    linarith [(abs_le.mp hc).1]
  have hg0 : ∀ u ∈ Icc (-(L / 2)) (L / 2), 0 ≤ g u := by
    intro u _
    refine mul_nonneg (mV_nonneg u) (sub_nonneg.mpr ?_)
    have hp1 : Taper.phi ϱ L w u ^ 2 ≤ 1 := by
      calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 :=
            pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
        _ = 1 := one_pow 2
    calc Taper.phi ϱ L w u ^ 2 / D1 ≤ 1 / D1 := div_le_div_of_nonneg_right hp1 hD1p.le
      _ ≤ (1 + e) / D2 := hdom
  have hgc : Continuous g := by
    rw [hg]
    exact (mV_continuous hv).mul (continuous_const.sub
      (((Taper.phi_continuous hϱ hw0 hwL').pow 2).div_const _))
  have hpd := isPosDefKernel_of_density measurableSet_Icc hgc.integrableOn_Icc hg0 (2 * π / L)
  have hfun : (fun t => (1 + e) * kPsi v t - kWin (phiM (fV v L) ϱ L w) L t)
      = fun t => ∫ u in Icc (-(L / 2)) (L / 2), g u * Real.cos (2 * π / L * t * u) := by
    funext t
    have hi1 : IntegrableOn (fun u => mV v L u * Real.cos (2 * π / L * t * u)) (Icc (-(L / 2)) (L / 2)) :=
      ((mV_continuous hv).mul (by fun_prop)).integrableOn_Icc
    have hi2 : IntegrableOn (fun u => (mV v L u * Real.cos (2 * π / L * t * u)) * Taper.phi ϱ L w u ^ 2)
        (Icc (-(L / 2)) (L / 2)) :=
      (((mV_continuous hv).mul (by fun_prop)).mul ((Taper.phi_continuous hϱ hw0 hwL').pow 2)).integrableOn_Icc
    have hsplit : (fun u => g u * Real.cos (2 * π / L * t * u))
        = fun u => (1 + e) / D2 * (mV v L u * Real.cos (2 * π / L * t * u))
          - D1⁻¹ * ((mV v L u * Real.cos (2 * π / L * t * u)) * Taper.phi ϱ L w u ^ 2) := by
      funext u; simp only [hg]; ring
    rw [hsplit, integral_sub (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
      kWin_eq hv hϱ hw hwL, kPsi_eq hv hL, ← hD1, ← hD2, Nphi_eq_set hϱ hw0 t]
    unfold Npsi
    ring
  rw [hfun]
  exact hpd

end KWinHelpers
end ZetaS

end
