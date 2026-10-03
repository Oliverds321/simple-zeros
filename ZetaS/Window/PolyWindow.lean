/-
rh72/lean_work/L0_2/PolyWindow.lean — board item P0-4 (track W, node W-poly): the polynomial window of
Theorem `thm:zeta-mainw2` (rh72/tex/sec_zeta.tex l.563–571; Remark `rem:zeta-P8` l.585–) against the
tree's admissible-window layer `Zeta23.AdmWindow` (Zeta23/ThmD/WindowCore.lean).

Paper passages formalised (quoted):
* sec_zeta.tex l.566: "ψ̃(s) := (50000/50037)(1 + (127/2500)u − (8997/10000)u² + (6187/10000)u³ + (3/1250)u⁴), u = (2s)²".
* sec_zeta.tex l.174 (eq:zeta-window = AF (2.7)): "φ(u) := χ_w(L/2+u) χ_w(L/2−u) ψ(u/L)^{1/2}".
* sec_zeta.tex l.588–591: "it is not monotone on [0,1/2] … 0.7679 ≤ ψ̃ ≤ 1".
* sec_zeta.tex l.592–593: "Every quantity that the bound uses … is homogeneous of degree 0 in ψ".

FINDING (see report rh72/lean_board/reports/L0_2_window.md).  With the draft's normalisation 50000/50037
the window φ̃ = √ψ̃(u/L)·ramp is NOT an `AdmWindow`: ψ̃ is not monotone, and (exactly, [C])
  ∫|φ̃'| → 2.0091116…,  ∫|(φ̃²)'| → 2.0161657…   (L/w → ∞)
exceed the hard-wired constant 2 of the fields `l1_deriv`, `l1_deriv_sq`.  Since every downstream
quantity is homogeneous of degree 0 in ψ (here: `cRatio_scale` below), we use instead the
normalisation ψ♮ := (4/5)·v, which keeps every existing constant of the tree for ALL 8w ≤ L (the Lean proof
below gives ∫|φ♮'| ≤ 1.9396 and ∫|(φ♮²)'| ≤ 1.8200), with a♮ = (4/5)∫v = 0.7405 and b♮ = (16/25)∫v² = 0.5528
≥ 1/2 + 2w/L once L ≥ 40w.  (Revision of 28 Sep 08:40: the first version used 7/8 and needed 64w ≤ L; 4/5 makes
the window fit the tree's generic `atV` zero side, which asks for admissibility at every 8w ≤ L.)

Status: NO `sorry`, no axioms beyond [propext, Classical.choice, Quot.sound].  Proved: definitions (exact
rationals), 0 < ψ̃ ≤ 1, non-monotonicity, the exact moments a, b, the autocorrelation, J and H, degree-0
homogeneity of the tree's ratio, and `admWindow_phiP8`: φ♮ is a `Zeta23.AdmWindow` (all twelve fields) for
1 ≤ w, 8w ≤ L, with c = cMod ϱ 2 25.  The total-variation fields are proved WITHOUT monotonicity
(generic `tv_mul_ramp_le` + a three-piece bound on v'); the second-derivative fields by the template's
generic `XiPrime.integral_abs_deriv2_mul_le` with three core bounds on √ψ♮ (no `ModFactor` needed).
-/
import Zeta23.ThmD.WindowCore
import Zeta23.ThmD.AssemblyD
import Zeta23.XiPrime.Certificate.Poly
import Zeta23.XiPrime.QuarticWindow.ModWindow

noncomputable section

open Real Set MeasureTheory

namespace ZetaS
namespace PolyWindow

open Zeta23 Zeta23.XiPrime

/-! ## 1. The window (exact rational coefficients) -/

/-- the bracket `v` of `thm:zeta-mainw2` (window `poly8A`, round2/d6_5_numerics/win_poly8A.json),
in the variable u = (2s)². -/
def vP8 (s : ℝ) : ℝ :=
  1 + 127 / 2500 * (2 * s) ^ 2 - 8997 / 10000 * ((2 * s) ^ 2) ^ 2
    + 6187 / 10000 * ((2 * s) ^ 2) ^ 3 + 3 / 1250 * ((2 * s) ^ 2) ^ 4

/-- `v` as a polynomial in u = (2s)². -/
def PU (u : ℝ) : ℝ := 1 + 127 / 2500 * u - 8997 / 10000 * u ^ 2 + 6187 / 10000 * u ^ 3 + 3 / 1250 * u ^ 4

theorem vP8_eq_PU (s : ℝ) : vP8 s = PU ((2 * s) ^ 2) := by unfold vP8 PU; ring

/-- `v` in the variable s (degree 8 in s; degree 4 in u). -/
theorem vP8_eq (s : ℝ) :
    vP8 s = 1 + 127 / 625 * s ^ 2 - 8997 / 625 * s ^ 4 + 24748 / 625 * s ^ 6 + 384 / 625 * s ^ 8 := by
  unfold vP8; ring

theorem vP8_even (s : ℝ) : vP8 (-s) = vP8 s := by unfold vP8; ring

/-- the draft's normalisation ψ̃ = (50000/50037)·v  (sec_zeta.tex l.566). -/
def psiTilde (s : ℝ) : ℝ := 50000 / 50037 * vP8 s

/-- the admissible normalisation ψ♮ = (4/5)·v (same H and same certificate, by degree-0 homogeneity). -/
def psiN (s : ℝ) : ℝ := 4 / 5 * vP8 s

/-! ## 2. Exact bounds (division certificates generated in rh72/lean_work/L0_2/cert.py) -/

/-- `P(u) − 3/4 = (u − 15/16)²·Q(u) + R(u)` with `Q, R > 0` on `u ≥ 0`: so `v ≥ 3/4` on all of ℝ
(minimum 0.768517… at u = 0.93567…, i.e. s = ±0.48365…). -/
theorem PU_ge (u : ℝ) (hu : 0 ≤ u) : 3 / 4 ≤ PU u := by
  have key : PU u - 3 / 4 = (u - 15 / 16) ^ 2 * (3 / 1250 * u ^ 2 + 779 / 1250 * u + 85341 / 320000)
      + (7963 / 2560000 * u + 51131 / 3276800) := by unfold PU; ring
  have hQ : 0 ≤ 3 / 1250 * u ^ 2 + 779 / 1250 * u + 85341 / 320000 := by positivity
  have hR : 0 ≤ 7963 / 2560000 * u + 51131 / 3276800 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (u - 15 / 16)) hQ]

theorem vP8_ge (s : ℝ) : 3 / 4 ≤ vP8 s := by
  rw [vP8_eq_PU]; exact PU_ge _ (sq_nonneg _)

theorem vP8_pos (s : ℝ) : 0 < vP8 s := lt_of_lt_of_le (by norm_num) (vP8_ge s)

/-- `50037/50000 − P(u) = (u − 2911/100000)²·Q(u) + R(u)`, `Q ≥ 0`, `R > 0` on `[0,1]`:
the draft's claim `ψ̃ ≤ 1` (the maximum of `v` is 1.0007317… at u = 0.0291056…; margin 8.3·10⁻⁶). -/
theorem PU_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : PU u ≤ 50037 / 50000 := by
  have key : 50037 / 50000 - PU u = (u - 2911 / 100000) ^ 2 *
      (-3 / 1250 * u ^ 2 - 38677483 / 62500000 * u + 10795914809711 / 12500000000000)
      + (1164486622391 / 156250000000000000 * u + 1016270779778953169 / 125000000000000000000000) := by
    unfold PU; ring
  have hQ : 0 ≤ -3 / 1250 * u ^ 2 - 38677483 / 62500000 * u + 10795914809711 / 12500000000000 := by
    nlinarith [mul_le_mul hu1 hu1 hu0 zero_le_one]
  have hR : 0 ≤ 1164486622391 / 156250000000000000 * u + 1016270779778953169 / 125000000000000000000000 := by
    positivity
  nlinarith [mul_nonneg (sq_nonneg (u - 2911 / 100000)) hQ]

theorem core_u (s : ℝ) (hs : |s| ≤ 1 / 2) : 0 ≤ (2 * s) ^ 2 ∧ (2 * s) ^ 2 ≤ 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have h1 : |2 * s| ≤ 1 := by rw [abs_mul, abs_two]; linarith
  have : (2 * s) ^ 2 = |2 * s| ^ 2 := (sq_abs _).symm
  rw [this]; nlinarith [abs_nonneg (2 * s)]

theorem vP8_le (s : ℝ) (hs : |s| ≤ 1 / 2) : vP8 s ≤ 50037 / 50000 := by
  obtain ⟨h0, h1⟩ := core_u s hs
  rw [vP8_eq_PU]; exact PU_le _ h0 h1

/-- **the draft's bounds** `0 < ψ̃ ≤ 1` on `[−1/2, 1/2]` (sec_zeta.tex l.570, l.591). -/
theorem psiTilde_pos_le (s : ℝ) (hs : |s| ≤ 1 / 2) : 0 < psiTilde s ∧ psiTilde s ≤ 1 := by
  unfold psiTilde
  refine ⟨mul_pos (by norm_num) (vP8_pos s), ?_⟩
  have := vP8_le s hs
  calc 50000 / 50037 * vP8 s ≤ 50000 / 50037 * (50037 / 50000) := by gcongr
    _ = 1 := by norm_num

/-- ψ♮ ∈ [3/5, 4/5·50037/50000] ⊂ (0, 1) on the core, and ψ♮ ≥ 3/5 on all of ℝ. -/
theorem psiN_ge (s : ℝ) : 3 / 5 ≤ psiN s := by unfold psiN; linarith [vP8_ge s]
theorem psiN_pos (s : ℝ) : 0 < psiN s := lt_of_lt_of_le (by norm_num) (psiN_ge s)
theorem psiN_le_one (s : ℝ) (hs : |s| ≤ 1 / 2) : psiN s ≤ 1 := by
  unfold psiN; linarith [vP8_le s hs]

/-! ## 3. Non-monotonicity (sec_zeta.tex l.588: "it is not monotone on [0,1/2]") -/

/-- `v(0) = 1 < v(1/10)`: `v` rises near 0. -/
theorem vP8_not_antitoneOn : ¬ AntitoneOn vP8 (Icc 0 (1 / 2)) := by
  intro h
  have h' := h (a := 0) (b := 1 / 10) ⟨le_rfl, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
  norm_num [vP8] at h'

/-- `v(12/25) < v(1/2)`: `v` rises again at the edge (the minimum is at s = 0.48365…). -/
theorem vP8_edge_rise : vP8 (12 / 25) < vP8 (1 / 2) := by norm_num [vP8]

/-! ## 4. The test function (eq:zeta-window with ψ = ψ♮, ramp = the tree's taper) -/

/-- the modulating factor in the u-variable, `f(u) = √ψ♮(u/L)` (`max 0` as in `Params.phiV`; it is
inert since ψ♮ > 0 everywhere). -/
def fP8 (L u : ℝ) : ℝ := Real.sqrt (max 0 (psiN (u / L)))

/-- the window `φ♮(u) = √ψ♮(u/L) · Taper.phi ϱ L w u`  (AF (2.7)); `= P.phiV psiN T` by `rfl`. -/
def phiP8 (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ := fP8 L u * Taper.phi ϱ L w u

theorem phiV_eq_phiP8 (P : Params) (T : ℝ) : P.phiV psiN T = phiP8 P.ϱ (P.L T) P.w := rfl

theorem fP8_eq (L u : ℝ) : fP8 L u = Real.sqrt (psiN (u / L)) := by
  unfold fP8; rw [max_eq_right (psiN_pos _).le]

theorem fP8_even (L u : ℝ) : fP8 L (-u) = fP8 L u := by
  simp only [fP8, psiN, neg_div, vP8_even]

theorem fP8_contDiff (L : ℝ) : ContDiff ℝ 2 (fP8 L) := by
  have h : fP8 L = fun u => Real.sqrt (psiN (u / L)) := funext (fP8_eq L)
  rw [h]
  refine ContDiff.sqrt ?_ (fun u => (psiN_pos _).ne')
  unfold psiN vP8; fun_prop

variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem phiP8_even (u : ℝ) : phiP8 ϱ L w (-u) = phiP8 ϱ L w u := by
  simp only [phiP8, fP8_even, Taper.phi_even]

theorem phiP8_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phiP8 ϱ L w u :=
  mul_nonneg (Real.sqrt_nonneg _) (Taper.phi_nonneg hϱ u)

theorem phiP8_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phiP8 ϱ L w u = 0 := by
  simp only [phiP8, Taper.phi_eq_zero hϱ hw hu, mul_zero]

theorem phiP8_le_one (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (u : ℝ) : phiP8 ϱ L w u ≤ 1 := by
  rcases le_or_gt (L / 2) |u| with hu | hu
  · rw [phiP8_eq_zero hϱ hw hu]; exact zero_le_one
  · have hs : |u / L| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith
    have hf : fP8 L u ≤ 1 := by
      rw [fP8_eq, Real.sqrt_le_one]; exact psiN_le_one _ hs
    calc phiP8 ϱ L w u ≤ 1 * 1 :=
          mul_le_mul hf (Taper.phi_le_one hϱ u) (Taper.phi_nonneg hϱ u) zero_le_one
      _ = 1 := mul_one 1

theorem phiP8_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (phiP8 ϱ L w) :=
  (fP8_contDiff L).mul ((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num))

/-! ## 4b. Total variation without monotonicity (node W3)

`∫|(fR)'| ≤ ∫_{−L/2}^{L/2}|f'| + 2·sup_{ramp}|f|` (generic), then the bulk variation of `√ψ♮` by
three pieces on `[0,1/2]` (two small pieces bounded by `sup|v'|·length`, one monotone piece by FTC). -/

/-- NODE W3a (generic): total variation of a modulated ramp; no monotonicity of `f` needed. -/
theorem tv_mul_ramp_le {f R : ℝ → ℝ} {L w K : ℝ} (hw : 0 < w) (hwL : 2 * w ≤ L)
    (hf : ContDiff ℝ 1 f) (hR : ContDiff ℝ 1 R)
    (hR0 : ∀ u, L / 2 ≤ |u| → R u = 0) (hR1 : ∀ u, |u| ≤ L / 2 - w → R u = 1)
    (hRnn : ∀ u, 0 ≤ R u) (hRle : ∀ u, R u ≤ 1) (hRtv : ∫ u, |deriv R u| ≤ 2)
    (hK0 : 0 ≤ K) (hK : ∀ u, L / 2 - w ≤ |u| → |u| ≤ L / 2 → |f u| ≤ K) :
    ∫ u, |deriv (fun u => f u * R u) u| ≤ (∫ u in (-(L / 2))..(L / 2), |deriv f u|) + 2 * K := by
  have hL : 0 ≤ L := by linarith
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hRd : Differentiable ℝ R := hR.differentiable (by norm_num)
  have hRd0 : ∀ u, (|u| < L / 2 - w ∨ L / 2 < |u|) → deriv R u = 0 := by
    intro u hu
    rcases hu with hu | hu
    · have hopen : IsOpen {v : ℝ | |v| < L / 2 - w} := continuous_abs.isOpen_preimage _ isOpen_Iio
      have hEq : R =ᶠ[nhds u] (fun _ => (1:ℝ)) := by
        filter_upwards [hopen.mem_nhds hu] with v hv
        exact hR1 v (le_of_lt hv)
      rw [hEq.deriv_eq, deriv_const]
    · have hopen : IsOpen {v : ℝ | L / 2 < |v|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
      have hEq : R =ᶠ[nhds u] (fun _ => (0:ℝ)) := by
        filter_upwards [hopen.mem_nhds hu] with v hv
        exact hR0 v (le_of_lt hv)
      rw [hEq.deriv_eq, deriv_const]
  have hprod : ∀ u, deriv (fun u => f u * R u) u = deriv f u * R u + f u * deriv R u :=
    fun u => deriv_mul (hfd u) (hRd u)
  set g : ℝ → ℝ := fun u => (Icc (-(L / 2)) (L / 2)).indicator (fun u => |deriv f u|) u
    + K * |deriv R u| with hg
  have hpt : ∀ u, |deriv (fun u => f u * R u) u| ≤ g u := by
    intro u
    rw [hprod u, hg]
    by_cases hu : |u| ≤ L / 2
    · have hmem : u ∈ Icc (-(L / 2)) (L / 2) := abs_le.mp hu
      simp only [indicator_of_mem hmem]
      have h1 : |deriv f u * R u| ≤ |deriv f u| := by
        rw [abs_mul, abs_of_nonneg (hRnn u)]
        exact mul_le_of_le_one_right (abs_nonneg _) (hRle u)
      have h2 : |f u * deriv R u| ≤ K * |deriv R u| := by
        rw [abs_mul]
        by_cases hu2 : L / 2 - w ≤ |u|
        · exact mul_le_mul_of_nonneg_right (hK u hu2 hu) (abs_nonneg _)
        · rw [hRd0 u (Or.inl (lt_of_not_ge hu2)), abs_zero, mul_zero, mul_zero]
      calc |deriv f u * R u + f u * deriv R u| ≤ |deriv f u * R u| + |f u * deriv R u| :=
            abs_add_le _ _
        _ ≤ |deriv f u| + K * |deriv R u| := add_le_add h1 h2
    · have hu' : L / 2 < |u| := lt_of_not_ge hu
      rw [hR0 u hu'.le, hRd0 u (Or.inr hu')]
      simp only [mul_zero, add_zero, abs_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ => abs_nonneg _) _)
        (mul_nonneg hK0 (abs_nonneg _))
  have hRcs : HasCompactSupport R :=
    HasCompactSupport.intro (isCompact_Icc (a := -(L / 2)) (b := L / 2)) fun u hu => by
      apply hR0
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · linarith [neg_abs_le u]
      · linarith [le_abs_self u]
  have hRdint : Integrable (fun u => |deriv R u|) :=
    ((hR.continuous_deriv le_rfl).integrable_of_hasCompactSupport hRcs.deriv).abs
  have hind : Integrable (fun u => (Icc (-(L / 2)) (L / 2)).indicator (fun u => |deriv f u|) u) :=
    ((hf.continuous_deriv le_rfl).abs.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hgint : Integrable g := hind.add (hRdint.const_mul K)
  calc ∫ u, |deriv (fun u => f u * R u) u| ≤ ∫ u, g u :=
        integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hgint (ae_of_all _ hpt)
    _ = (∫ u, (Icc (-(L / 2)) (L / 2)).indicator (fun u => |deriv f u|) u)
          + K * ∫ u, |deriv R u| := by
        rw [hg, integral_add hind (hRdint.const_mul K), integral_const_mul]
    _ ≤ (∫ u in (-(L / 2))..(L / 2), |deriv f u|) + 2 * K := by
        rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith)]
        have : K * ∫ u, |deriv R u| ≤ K * 2 := mul_le_mul_of_nonneg_left hRtv hK0
        linarith

/-- `v'`. -/
def dv (s : ℝ) : ℝ := 254 / 625 * s - 35988 / 625 * s ^ 3 + 148488 / 625 * s ^ 5 + 3072 / 625 * s ^ 7

theorem dv_continuous : Continuous dv := by unfold dv; fun_prop

theorem dv_odd (s : ℝ) : dv (-s) = -dv s := by unfold dv; ring

theorem hasDerivAt_vP8 (s : ℝ) : HasDerivAt vP8 (dv s) s := by
  have e : vP8 = fun s => 1 + 127 / 625 * s ^ 2 - 8997 / 625 * s ^ 4 + 24748 / 625 * s ^ 6
      + 384 / 625 * s ^ 8 := funext vP8_eq
  rw [e]
  have h := (((((hasDerivAt_pow 2 s).const_mul (127 / 625 : ℝ)).const_add 1).sub
      ((hasDerivAt_pow 4 s).const_mul (8997 / 625 : ℝ))).add
      ((hasDerivAt_pow 6 s).const_mul (24748 / 625 : ℝ))).add
      ((hasDerivAt_pow 8 s).const_mul (384 / 625 : ℝ))
  refine h.congr_deriv ?_
  unfold dv; push_cast; ring

/-- `v' = s·B(s²)`, `625·B(t) = 254 − 35988t + 148488t² + 3072t³`. -/
theorem dv_eq (s : ℝ) : dv s = s * ((254 - 35988 * s ^ 2 + 148488 * (s ^ 2) ^ 2 + 3072 * (s ^ 2) ^ 3) / 625) := by
  unfold dv; ring

theorem abs_dv_small {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 10) : |dv s| ≤ 1 / 20 := by
  rw [dv_eq, abs_mul, abs_of_nonneg h0]
  set t := s ^ 2 with ht
  have t0 : 0 ≤ t := sq_nonneg s
  have t1 : t ≤ 1 / 100 := by rw [ht]; nlinarith
  have hB : |(254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3) / 625| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg t0 t0, mul_nonneg (mul_nonneg t0 t0) t0]
  nlinarith [abs_nonneg ((254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3) / 625)]

theorem dv_nonpos {s : ℝ} (h0 : 1 / 10 ≤ s) (h1 : s ≤ 9 / 20) : dv s ≤ 0 := by
  rw [dv_eq]
  set t := s ^ 2 with ht
  have ta : 1 / 100 ≤ t := by rw [ht]; nlinarith
  have tb : t ≤ 81 / 400 := by rw [ht]; nlinarith
  have key : 254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3
      = (-5377251 / 1250 * t - 1200253 / 25000) + (t - 1 / 100) * (t - 81 / 400) * (3072 * t + 745704 / 5) := by
    ring
  have hq : 0 ≤ (t - 1 / 100) * (81 / 400 - t) * (3072 * t + 745704 / 5) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hB : (254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3) / 625 ≤ 0 := by
    rw [key]; nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hB

theorem abs_dv_edge {s : ℝ} (h0 : 9 / 20 ≤ s) (h1 : s ≤ 1 / 2) : |dv s| ≤ 3 / 4 := by
  rw [dv_eq, abs_mul, abs_of_nonneg (by linarith)]
  set t := s ^ 2 with ht
  have ta : 81 / 400 ≤ t := by rw [ht]; nlinarith
  have tb : t ≤ 1 / 4 := by rw [ht]; nlinarith
  have keyU : 254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3
      = (39595389 / 1250 * t - 36667889 / 5000) + (t - 81 / 400) * (t - 1 / 4) * (3072 * t + 3746952 / 25) := by
    ring
  have keyL : 254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3
      = -459562391 / 500000 + (t - 81 / 400) * (3072 * t ^ 2 + 3727752 / 25 * t - 7241511 / 1250) := by
    ring
  have hq : 0 ≤ (t - 81 / 400) * (1 / 4 - t) * (3072 * t + 3746952 / 25) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hdd : 0 ≤ 3072 * t ^ 2 + 3727752 / 25 * t - 7241511 / 1250 := by nlinarith
  have hq2 : 0 ≤ (t - 81 / 400) * (3072 * t ^ 2 + 3727752 / 25 * t - 7241511 / 1250) :=
    mul_nonneg (by linarith) hdd
  have hB : |(254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3) / 625| ≤ 3 / 2 := by
    rw [abs_le]; constructor
    · rw [keyL]; nlinarith
    · rw [keyU]; nlinarith
  nlinarith [abs_nonneg ((254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3) / 625)]

theorem integral_abs_le_const {h : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hc : Continuous h)
    (hb : ∀ x ∈ Icc a b, |h x| ≤ c) : ∫ x in a..b, |h x| ≤ (b - a) * c := by
  have := intervalIntegral.integral_mono_on (μ := volume) hab (hc.abs.intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b) hb
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this

/-- `∫₀^{1/2}|v'| ≤ 1/200 + (v(1/10) − v(9/20)) + 3/80` (exact value of the middle term 10997079247/5·10¹⁰). -/
theorem integral_abs_dv_half : ∫ s in (0:ℝ)..(1/2), |dv s| ≤ 1 / 200 + 10997079247 / 50000000000 + 3 / 80 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun s => |dv s|) volume a b :=
    fun a b => dv_continuous.abs.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (1/10)) (hi (1/10) (1/2)),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (1/10) (9/20)) (hi (9/20) (1/2))]
  have h1 : ∫ s in (0:ℝ)..(1/10), |dv s| ≤ 1 / 200 := by
    have := integral_abs_le_const (a := 0) (b := 1/10) (c := 1/20) (by norm_num) dv_continuous
      (fun x hx => abs_dv_small hx.1 hx.2)
    linarith
  have h3 : ∫ s in (9/20 : ℝ)..(1/2), |dv s| ≤ 3 / 80 := by
    have := integral_abs_le_const (a := 9/20) (b := 1/2) (c := 3/4) (by norm_num) dv_continuous
      (fun x hx => abs_dv_edge hx.1 hx.2)
    linarith
  have h2 : ∫ s in (1/10 : ℝ)..(9/20), |dv s| = 10997079247 / 50000000000 := by
    have hcongr : Set.EqOn (fun s => |dv s|) (fun s => -dv s) (Set.uIcc (1/10 : ℝ) (9/20)) := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact abs_of_nonpos (dv_nonpos hs.1 hs.2)
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_vP8 x)
        (dv_continuous.intervalIntegrable _ _)]
    norm_num [vP8]
  linarith

theorem integral_abs_dv : ∫ s in (-(1:ℝ)/2)..(1/2), |dv s| ≤ 2 * (1 / 200 + 10997079247 / 50000000000 + 3 / 80) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun s => |dv s|) volume a b :=
    fun a b => dv_continuous.abs.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-(1:ℝ)/2) 0) (hi 0 (1/2))]
  have hneg : ∫ s in (-(1:ℝ)/2)..0, |dv s| = ∫ s in (0:ℝ)..(1/2), |dv s| := by
    have := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1/2) (fun s => |dv s|)
    simp only [dv_odd, abs_neg, neg_zero] at this
    rw [show (-(1:ℝ)/2) = -(1/2) by norm_num, ← this]
  rw [hneg]
  linarith [integral_abs_dv_half]

end PolyWindow
end ZetaS

namespace ZetaS
namespace PolyWindow
open Zeta23 Zeta23.XiPrime
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! ## 5. Admissibility

The window constant: the template's `cMod ϱ A B = c_ϱ + A + A² + B` with `|f'| ≤ A/L`,
`|f''| ≤ B/L²` on the core; for `f = √ψ♮(·/L)`: sup|(√ψ♮)'| ≤ 0.5678, sup|(√ψ♮)''| ≤ 16.961 [C, arb]
(so `A = 3/5`, `B = 17` would do); the Lean proof uses the cruder `A = 2`, `B = 25` (`fP8_core1/2`). -/

/-- the window constant of φ♮. -/
def cP8 (ϱ : ℝ → ℝ) : ℝ := cMod ϱ 2 25

/-- scaling: `∫_{−L/2}^{L/2} |(F(·/L))'| = ∫_{−1/2}^{1/2} |F'|`. -/
theorem integral_abs_deriv_comp_div {F G : ℝ → ℝ} (hL : 0 < L) (hF : ∀ s, HasDerivAt F (G s) s) :
    ∫ u in (-(L / 2))..(L / 2), |deriv (fun u => F (u / L)) u| = ∫ s in (-(1:ℝ)/2)..(1/2), |G s| := by
  have hd : ∀ u, HasDerivAt (fun u => F (u / L)) (G (u / L) * (1 / L)) u := fun u => by
    have := (hF (u / L)).comp u ((hasDerivAt_id u).div_const L)
    exact this
  calc ∫ u in (-(L / 2))..(L / 2), |deriv (fun u => F (u / L)) u|
      = ∫ u in (-(L / 2))..(L / 2), |G (u / L)| * (1 / L) := by
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        rw [(hd u).deriv, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / L)]
    _ = (∫ u in (-(L / 2))..(L / 2), |G (u / L)|) * (1 / L) := by
        rw [intervalIntegral.integral_mul_const]
    _ = (L • ∫ s in (-(L / 2)) / L..(L / 2) / L, |G s|) * (1 / L) := by
        rw [intervalIntegral.integral_comp_div (fun s => |G s|) hL.ne']
    _ = ∫ s in (-(1:ℝ)/2)..(1/2), |G s| := by
        rw [show (-(L / 2)) / L = -(1:ℝ) / 2 by field_simp, show (L / 2) / L = (1:ℝ) / 2 by field_simp,
          smul_eq_mul]
        field_simp

theorem psiN_continuous : Continuous psiN := by unfold psiN vP8; fun_prop

theorem hasDerivAt_psiN (s : ℝ) : HasDerivAt psiN (4 / 5 * dv s) s := by
  unfold psiN; exact (hasDerivAt_vP8 s).const_mul (4 / 5)

/-- the derivative of `√ψ♮`. -/
def dg (s : ℝ) : ℝ := 4 / 5 * dv s / (2 * Real.sqrt (psiN s))

theorem hasDerivAt_sqrt_psiN (s : ℝ) : HasDerivAt (fun s => Real.sqrt (psiN s)) (dg s) s :=
  (hasDerivAt_psiN s).sqrt (psiN_pos s).ne'

theorem abs_dg_le (s : ℝ) : |dg s| ≤ 13 / 25 * |dv s| := by
  have hs : 10 / 13 ≤ Real.sqrt (psiN s) := by
    rw [show (10 / 13 : ℝ) = Real.sqrt ((10 / 13) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith [psiN_ge s])
  unfold dg
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4 / 5),
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt (psiN s)), div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg (dv s)]

/-- the edge bound: `v ≤ 79/100` for `31/64 ≤ |s| ≤ 1/2` (v increases from its minimum at s = 0.48365…
to v(1/2) = 0.7722; interpolation certificate), hence `ψ♮ ≤ 553/800 ≤ 25/36` there. -/
theorem vP8_edge_le {s : ℝ} (h1 : 31 / 64 ≤ |s|) (h2 : |s| ≤ 1 / 2) : vP8 s ≤ 79 / 100 := by
  have hu0 : 961 / 1024 ≤ (2 * s) ^ 2 := by
    rw [show (2 * s) ^ 2 = 4 * |s| ^ 2 by rw [sq_abs]; ring]; nlinarith
  have hu1 : (2 * s) ^ 2 ≤ 1 := (core_u s h2).2
  rw [vP8_eq_PU]
  set u := (2 * s) ^ 2
  have key : PU u = (16039202983 / 268435456000 * u + 956233280701 / 1342177280000)
      + (u - 961 / 1024) * (u - 1) * (3 / 1250 * u ^ 2 + 797891 / 1280000 * u + 401606659 / 1310720000) := by
    unfold PU; ring
  have hq : 0 ≤ (u - 961 / 1024) * (1 - u) * (3 / 1250 * u ^ 2 + 797891 / 1280000 * u + 401606659 / 1310720000) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  rw [key]; nlinarith

/-- the edge bound used for all `8w ≤ L`: `v ≤ 855/1000` for `3/8 ≤ |s| ≤ 1/2` (v is convex in u = (2s)² there, with
v(3/8) = 0.85426 and v(1/2) = 0.7722; interpolation certificate). -/
theorem vP8_edge_le8 {s : ℝ} (h1 : 3 / 8 ≤ |s|) (h2 : |s| ≤ 1 / 2) : vP8 s ≤ 855 / 1000 := by
  have hu0 : 9 / 16 ≤ (2 * s) ^ 2 := by
    rw [show (2 * s) ^ 2 = 4 * |s| ^ 2 by rw [sq_abs]; ring]; nlinarith
  have hu1 : (2 * s) ^ 2 ≤ 1 := (core_u s h2).2
  rw [vP8_eq_PU]
  set u := (2 * s) ^ 2
  have key : PU u = (4913999 / 5120000 - 192067 / 1024000 * u)
      + (u - 9 / 16) * (u - 1) * (3 / 1250 * u ^ 2 + 12449 / 20000 * u + 22889 / 320000) := by
    unfold PU; ring
  have hq : 0 ≤ (u - 9 / 16) * (1 - u) * (3 / 1250 * u ^ 2 + 12449 / 20000 * u + 22889 / 320000) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  rw [key]; nlinarith

theorem edge_mem {u : ℝ} (hw : 0 < w) (h8 : 8 * w ≤ L) (h1 : L / 2 - w ≤ |u|) (h2 : |u| ≤ L / 2) :
    3 / 8 ≤ |u / L| ∧ |u / L| ≤ 1 / 2 := by
  have hL : 0 < L := by linarith
  rw [abs_div, abs_of_pos hL]
  constructor
  · rw [le_div_iff₀ hL]; linarith
  · rw [div_le_iff₀ hL]; linarith

/-- **NODE W3 (proved): `‖φ♮'‖₁ ≤ 2` without monotonicity**, for all `8w ≤ L`:
`∫|φ♮'| ≤ (13/25)·∫_{−1/2}^{1/2}|v'| + 2·(5/6) ≤ 1.9396`. -/
theorem integral_abs_deriv_phiP8_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (phiP8 ϱ L w) u| ≤ 2 := by
  have hw0 : 0 < w := by linarith
  have hL : 0 < L := by linarith
  have e : phiP8 ϱ L w = fun u => fP8 L u * Taper.phi ϱ L w u := rfl
  have ef : fP8 L = fun u => Real.sqrt (psiN (u / L)) := funext (fP8_eq L)
  rw [e]
  have hTV := tv_mul_ramp_le (f := fP8 L) (R := Taper.phi ϱ L w) (K := 5 / 6) hw0 (by linarith)
    ((fP8_contDiff L).of_le (by norm_num)) ((Taper.phi_contDiff hϱ hw0 (by linarith)).of_le (by norm_num))
    (fun u hu => Taper.phi_eq_zero hϱ hw0 hu) (fun u hu => Taper.phi_eq_one hϱ hw0 hu)
    (fun u => Taper.phi_nonneg hϱ u) (fun u => Taper.phi_le_one hϱ u)
    (Taper.integral_abs_deriv_phi hϱ hw0 (by linarith)).le (by norm_num)
    (fun u h1 h2 => by
      obtain ⟨m1, m2⟩ := edge_mem hw0 hwL h1 h2
      have hv := vP8_edge_le8 m1 m2
      rw [fP8_eq, abs_of_nonneg (Real.sqrt_nonneg _),
        show (5 / 6 : ℝ) = Real.sqrt ((5 / 6) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by unfold psiN; nlinarith))
  have hbulk : ∫ u in (-(L / 2))..(L / 2), |deriv (fP8 L) u| ≤ 13 / 25 *
      (2 * (1 / 200 + 10997079247 / 50000000000 + 3 / 80)) := by
    rw [ef, integral_abs_deriv_comp_div hL hasDerivAt_sqrt_psiN]
    have hdgc : Continuous dg := by
      unfold dg
      refine Continuous.div (continuous_const.mul dv_continuous)
        (continuous_const.mul (psiN_continuous.sqrt)) (fun s => ?_)
      have := Real.sqrt_pos.mpr (psiN_pos s); positivity
    have hmono : ∫ s in (-(1:ℝ)/2)..(1/2), |dg s| ≤ ∫ s in (-(1:ℝ)/2)..(1/2), 13 / 25 * |dv s| :=
      intervalIntegral.integral_mono_on (by norm_num) (hdgc.abs.intervalIntegrable _ _)
        ((dv_continuous.abs.const_mul _).intervalIntegrable _ _) (fun s _ => abs_dg_le s)
    rw [intervalIntegral.integral_const_mul] at hmono
    nlinarith [integral_abs_dv]
  linarith

/-- **NODE W3' (proved): `‖(φ♮²)'‖₁ ≤ 2`** for all `8w ≤ L`: `≤ (4/5)·∫|v'| + 2·(7/10) ≤ 1.8200`. -/
theorem integral_abs_deriv_phiP8_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (fun u => phiP8 ϱ L w u ^ 2) u| ≤ 2 := by
  have hw0 : 0 < w := by linarith
  have hL : 0 < L := by linarith
  have e : (fun u => phiP8 ϱ L w u ^ 2) = fun u => psiN (u / L) * Taper.phi ϱ L w u ^ 2 := by
    funext u
    simp only [phiP8, fP8_eq, mul_pow, Real.sq_sqrt (psiN_pos _).le]
  rw [e]
  have hRc : ContDiff ℝ 1 (fun u => Taper.phi ϱ L w u ^ 2) :=
    ((Taper.phi_contDiff hϱ hw0 (by linarith)).pow 2).of_le (by norm_num)
  have hFc : ContDiff ℝ 1 (fun u => psiN (u / L)) := by unfold psiN vP8; fun_prop
  have hTV := tv_mul_ramp_le (f := fun u => psiN (u / L)) (R := fun u => Taper.phi ϱ L w u ^ 2)
    (K := 7 / 10) hw0 (by linarith) hFc hRc
    (fun u hu => by simp only [Taper.phi_eq_zero hϱ hw0 hu]; norm_num)
    (fun u hu => by simp only [Taper.phi_eq_one hϱ hw0 hu]; norm_num)
    (fun u => sq_nonneg _)
    (fun u => by
      have h0 := Taper.phi_nonneg hϱ (L := L) (w := w) u
      have h1 := Taper.phi_le_one hϱ (L := L) (w := w) u
      nlinarith)
    (Taper.integral_abs_deriv_phi_sq hϱ hw0 (by linarith)).le (by norm_num)
    (fun u h1 h2 => by
      obtain ⟨m1, m2⟩ := edge_mem hw0 hwL h1 h2
      have hv := vP8_edge_le8 m1 m2
      rw [abs_of_nonneg (psiN_pos _).le]
      unfold psiN; nlinarith)
  have hbulk : ∫ u in (-(L / 2))..(L / 2), |deriv (fun u => psiN (u / L)) u| ≤ 4 / 5 *
      (2 * (1 / 200 + 10997079247 / 50000000000 + 3 / 80)) := by
    rw [integral_abs_deriv_comp_div hL hasDerivAt_psiN]
    have h' : ∫ s in (-(1:ℝ)/2)..(1/2), |4 / 5 * dv s| = 4 / 5 * ∫ s in (-(1:ℝ)/2)..(1/2), |dv s| := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4 / 5)]
    rw [h']
    nlinarith [integral_abs_dv]
  linarith

/-! ### second derivatives (nodes W4, W4'): the template proof with the three core bounds of `fP8` -/

/-- `v''`. -/
def ddv (s : ℝ) : ℝ := 254 / 625 - 107964 / 625 * s ^ 2 + 742440 / 625 * s ^ 4 + 21504 / 625 * s ^ 6

theorem hasDerivAt_dv (s : ℝ) : HasDerivAt dv (ddv s) s := by
  have e : dv = fun s => 254 / 625 * s - 35988 / 625 * s ^ 3 + 148488 / 625 * s ^ 5
      + 3072 / 625 * s ^ 7 := rfl
  rw [e]
  have h := ((((hasDerivAt_id s).const_mul (254 / 625 : ℝ)).sub
      ((hasDerivAt_pow 3 s).const_mul (35988 / 625 : ℝ))).add
      ((hasDerivAt_pow 5 s).const_mul (148488 / 625 : ℝ))).add
      ((hasDerivAt_pow 7 s).const_mul (3072 / 625 : ℝ))
  refine h.congr_deriv ?_
  unfold ddv; push_cast; ring

theorem core_t {s : ℝ} (hs : |s| ≤ 1 / 2) : 0 ≤ s ^ 2 ∧ s ^ 2 ≤ 1 / 4 := by
  refine ⟨sq_nonneg _, ?_⟩
  rw [← sq_abs]; nlinarith [abs_nonneg s]

theorem abs_dv_core {s : ℝ} (hs : |s| ≤ 1 / 2) : |dv s| ≤ 2 := by
  obtain ⟨t0, t1⟩ := core_t hs
  rw [dv_eq, abs_mul]
  set t := s ^ 2
  have hB : |(254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3) / 625| ≤ 4 := by
    have key : 254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3
        = (1326 * t + 254) + t * (t - 1 / 4) * (3072 * t + 149256) := by ring
    have hq : 0 ≤ t * (1 / 4 - t) * (3072 * t + 149256) :=
      mul_nonneg (mul_nonneg t0 (by linarith)) (by positivity)
    rw [abs_le]; constructor
    · nlinarith [sq_nonneg (t - 1 / 8), mul_nonneg (mul_nonneg t0 t0) t0]
    · rw [key]; nlinarith
  nlinarith [abs_nonneg s, abs_nonneg ((254 - 35988 * t + 148488 * t ^ 2 + 3072 * t ^ 3) / 625)]

theorem abs_ddv_core {s : ℝ} (hs : |s| ≤ 1 / 2) : |ddv s| ≤ 33 := by
  obtain ⟨t0, t1⟩ := core_t hs
  have e : ddv s = (254 - 107964 * s ^ 2 + 742440 * (s ^ 2) ^ 2 + 21504 * (s ^ 2) ^ 3) / 625 := by
    unfold ddv; ring
  rw [e]
  set t := s ^ 2
  have key : 254 - 107964 * t + 742440 * t ^ 2 + 21504 * t ^ 3
      = (78990 * t + 254) + t * (t - 1 / 4) * (21504 * t + 747816) := by ring
  have hq : 0 ≤ t * (1 / 4 - t) * (21504 * t + 747816) :=
    mul_nonneg (mul_nonneg t0 (by linarith)) (by positivity)
  rw [abs_le]; constructor
  · nlinarith [sq_nonneg (t - 1 / 14), mul_nonneg (mul_nonneg t0 t0) t0]
  · rw [key]; nlinarith

theorem sqrt_psiN_bounds {s : ℝ} (hs : |s| ≤ 1 / 2) :
    3 / 4 ≤ Real.sqrt (psiN s) ∧ Real.sqrt (psiN s) ≤ 1 := by
  constructor
  · rw [show (3 / 4 : ℝ) = Real.sqrt ((3 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith [psiN_ge s])
  · rw [Real.sqrt_le_one]; exact psiN_le_one s hs

/-- `(√ψ♮)''`. -/
def ddg (s : ℝ) : ℝ :=
  ((4 / 5 * ddv s) * (2 * Real.sqrt (psiN s)) - (4 / 5 * dv s) * (2 * dg s)) / (2 * Real.sqrt (psiN s)) ^ 2

theorem hasDerivAt_dg (s : ℝ) : HasDerivAt dg (ddg s) s := by
  have hc : HasDerivAt (fun s => 4 / 5 * dv s) (4 / 5 * ddv s) s := (hasDerivAt_dv s).const_mul _
  have hd : HasDerivAt (fun s => 2 * Real.sqrt (psiN s)) (2 * dg s) s :=
    (hasDerivAt_sqrt_psiN s).const_mul 2
  have hne : 2 * Real.sqrt (psiN s) ≠ 0 := by
    have := Real.sqrt_pos.mpr (psiN_pos s); positivity
  exact hc.div hd hne

theorem abs_ddg_core {s : ℝ} (hs : |s| ≤ 1 / 2) : |ddg s| ≤ 25 := by
  obtain ⟨g0, g1⟩ := sqrt_psiN_bounds hs
  have h1 := abs_dv_core hs
  have h2 := abs_ddv_core hs
  have hdg : |dg s| ≤ 26 / 25 := by
    have := abs_dg_le s; nlinarith [abs_nonneg (dv s)]
  have hden : (2 * Real.sqrt (psiN s)) ^ 2 = 4 * psiN s := by
    rw [mul_pow, Real.sq_sqrt (psiN_pos s).le]; ring
  have hψ := psiN_ge s
  unfold ddg
  rw [abs_div, hden, abs_of_pos (by linarith : (0:ℝ) < 4 * psiN s), div_le_iff₀ (by linarith)]
  have hnum : |(4 / 5 * ddv s) * (2 * Real.sqrt (psiN s)) - (4 / 5 * dv s) * (2 * dg s)|
      ≤ 4 / 5 * 33 * 2 + 4 / 5 * 2 * (2 * (26 / 25)) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4 / 5),
      abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (Real.sqrt_nonneg _)]
    have e2 : |2 * dg s| = 2 * |dg s| := by rw [abs_mul, abs_two]
    rw [e2]
    have := mul_le_mul h2 g1 (Real.sqrt_nonneg _) (by norm_num)
    have := mul_le_mul h1 hdg (abs_nonneg _) (by norm_num)
    nlinarith [abs_nonneg (ddv s), abs_nonneg (dv s), abs_nonneg (dg s)]
  nlinarith

theorem deriv_fP8 (_hL : 0 < L) : deriv (fP8 L) = fun u => dg (u / L) * (1 / L) := by
  funext u
  have ef : fP8 L = fun u => Real.sqrt (psiN (u / L)) := funext (fP8_eq L)
  rw [ef]
  exact ((hasDerivAt_sqrt_psiN (u / L)).comp u ((hasDerivAt_id u).div_const L)).deriv

theorem deriv2_fP8 (hL : 0 < L) (u : ℝ) : deriv (deriv (fP8 L)) u = ddg (u / L) * (1 / L) * (1 / L) := by
  rw [deriv_fP8 hL]
  exact (((hasDerivAt_dg (u / L)).comp u ((hasDerivAt_id u).div_const L)).mul_const (1 / L)).deriv

theorem core_div {u : ℝ} (hL : 0 < L) (hu : |u| ≤ L / 2) : |u / L| ≤ 1 / 2 := by
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith

theorem fP8_core0 (hL : 0 < L) (u : ℝ) (hu : |u| ≤ L / 2) : |fP8 L u| ≤ 1 := by
  rw [fP8_eq, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (sqrt_psiN_bounds (core_div hL hu)).2

theorem fP8_core1 (hL : 0 < L) (u : ℝ) (hu : |u| ≤ L / 2) : |deriv (fP8 L) u| ≤ 2 / L := by
  rw [deriv_fP8 hL]
  simp only
  have hdg : |dg (u / L)| ≤ 2 := by
    have h1 := abs_dv_core (core_div hL hu)
    have := abs_dg_le (u / L); nlinarith [abs_nonneg (dv (u / L))]
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / L)]
  calc |dg (u / L)| * (1 / L) ≤ 2 * (1 / L) := by gcongr
    _ = 2 / L := by ring

theorem fP8_core2 (hL : 0 < L) (u : ℝ) (hu : |u| ≤ L / 2) :
    |deriv (deriv (fP8 L)) u| ≤ 25 / L ^ 2 := by
  rw [deriv2_fP8 hL, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / L)]
  calc |ddg (u / L)| * (1 / L) * (1 / L) ≤ 25 * (1 / L) * (1 / L) := by
        gcongr; exact abs_ddg_core (core_div hL hu)
    _ = 25 / L ^ 2 := by ring

/-- **NODE W4 (proved): `‖φ♮''‖₁ ≤ cP8/w`** — the template proof of
`XiPrime.integral_abs_deriv2_phiM_le`, with the three core bounds `fP8_core0/1/2` in place of a
`ModFactor` (whose `antitone` field φ♮ cannot supply and which that proof never uses). -/
theorem integral_abs_deriv2_phiP8_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (deriv (phiP8 ϱ L w)) u| ≤ cP8 ϱ / w := by
  have hw0 : 0 < w := by linarith
  have h2wL : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hmain := integral_abs_deriv2_mul_le (F := fP8 L) (G := Taper.phi ϱ L w) (L := L) (δ := 1) one_pos
    (by positivity : (0:ℝ) ≤ 2 / L) (by positivity : (0:ℝ) ≤ 25 / L ^ 2) (fP8_contDiff L).contDiffOn
    (fP8_core0 hL) (fP8_core1 hL) (fP8_core2 hL)
    ((Taper.phi_contDiff hϱ hw0 h2wL).of_le (by norm_num)) (Taper.phi_hasCompactSupport hϱ hw0)
    (fun u hu => Taper.phi_eq_zero hϱ hw0 hu.le) (phiP8_contDiff hϱ hw0 h2wL)
    (phiM_hasCompactSupport (f := fP8 L) (L := L) hϱ hw0)
  have hI0 := integral_abs_phi_le hϱ hw0 h2wL
  have hI1 : ∫ u, |deriv (Taper.phi ϱ L w) u| = 2 := Taper.integral_abs_deriv_phi hϱ hw0 h2wL
  have hI2 : ∫ u, |deriv (deriv (Taper.phi ϱ L w)) u| = 2 * Taper.l1Deriv2 ϱ / w :=
    Taper.integral_abs_deriv2_phi hϱ hw0 h2wL
  rw [hI1, hI2] at hmain
  have hc := Taper.two_mul_l1Deriv2_le_cRho hϱ
  have hl1 := l1Deriv2_nonneg' ϱ
  show ∫ u, |deriv (deriv (fun u => fP8 L u * Taper.phi ϱ L w u)) u| ≤ cP8 ϱ / w
  refine hmain.trans ?_
  have e1 : 25 / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ 25 / w := by
    calc 25 / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ 25 / L ^ 2 * L := by gcongr
      _ = 25 / L := by field_simp
      _ ≤ 25 / w := div_le_div_of_nonneg_left (by norm_num) hw0 (by linarith)
  have e2 : 2 * (2 / L) * 2 ≤ 2 / w := by
    rw [show 2 * (2 / L) * 2 = 8 / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
  have e3 : 2 * Taper.l1Deriv2 ϱ / w ≤ Taper.cRho ϱ / w := div_le_div_of_nonneg_right hc hw0.le
  have e4 : 0 ≤ (2:ℝ) ^ 2 / w := by positivity
  calc 25 / L ^ 2 * (∫ u, |Taper.phi ϱ L w u|) + 2 * (2 / L) * 2 + 2 * Taper.l1Deriv2 ϱ / w
      ≤ 25 / w + 2 / w + Taper.cRho ϱ / w + (2:ℝ) ^ 2 / w := by linarith
    _ = cP8 ϱ / w := by simp only [cP8, cMod]; ring

/-- **NODE W4' (proved): `‖(φ♮²)''‖₁ ≤ cP8/w`** (template `integral_abs_deriv2_phiM_sq_le`, same substitution). -/
theorem integral_abs_deriv2_phiP8_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ u, |deriv (deriv (fun u => phiP8 ϱ L w u ^ 2)) u| ≤ cP8 ϱ / w := by
  have hw0 : 0 < w := by linarith
  have h2wL : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  set f := fP8 L with hfdef
  set U : Set ℝ := Ioo (-(L / 2 + 1)) (L / 2 + 1) with hUdef
  have hU : IsOpen U := isOpen_Ioo
  have hcore : ∀ u, |u| ≤ L / 2 → u ∈ U := fun u hu => by
    simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  have hsm : ContDiffOn ℝ 2 f U := (fP8_contDiff L).contDiffOn
  have hsm2 : ContDiffOn ℝ 2 (fun u => f u * f u) U := hsm.mul hsm
  have hF0 : ∀ u, |u| ≤ L / 2 → |f u * f u| ≤ 1 := fun u hu => by
    rw [abs_mul]; have := fP8_core0 hL u hu; nlinarith [abs_nonneg (f u)]
  have hF1 : ∀ u, |u| ≤ L / 2 → |deriv (fun u => f u * f u) u| ≤ 2 * 2 / L := fun u hu => by
    rw [deriv_mul_eq hU hsm hsm (hcore u hu)]
    have h0 := fP8_core0 hL u hu; have h1 := fP8_core1 hL u hu
    calc |deriv f u * f u + f u * deriv f u| = 2 * (|f u| * |deriv f u|) := by
          rw [show deriv f u * f u + f u * deriv f u = 2 * (f u * deriv f u) by ring, abs_mul, abs_mul,
            abs_two]
      _ ≤ 2 * (1 * (2 / L)) := by gcongr
      _ = 2 * 2 / L := by ring
  have hF2 : ∀ u, |u| ≤ L / 2 → |deriv (deriv (fun u => f u * f u)) u| ≤ (2 * 25 + 2 * 2 ^ 2) / L ^ 2 :=
    fun u hu => by
    rw [deriv2_mul_eq hU hsm hsm (hcore u hu)]
    have h0 := fP8_core0 hL u hu; have h1 := fP8_core1 hL u hu; have h2 := fP8_core2 hL u hu
    have hd0 := abs_nonneg (deriv f u)
    calc |deriv (deriv f) u * f u + 2 * (deriv f u * deriv f u) + f u * deriv (deriv f) u|
        ≤ |deriv (deriv f) u * f u| + |2 * (deriv f u * deriv f u)| + |f u * deriv (deriv f) u| :=
          abs_add_three _ _ _
      _ = 2 * (|deriv (deriv f) u| * |f u|) + 2 * (|deriv f u| * |deriv f u|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
      _ ≤ 2 * (25 / L ^ 2 * 1) + 2 * (2 / L * (2 / L)) := by gcongr
      _ = (2 * 25 + 2 * 2 ^ 2) / L ^ 2 := by field_simp
  have hφ := Taper.phi_contDiff hϱ hw0 h2wL
  have hG : ContDiff ℝ 2 (fun u => Taper.phi ϱ L w u ^ 2) := (hφ.pow 2).of_le (by norm_num)
  have hGcs : HasCompactSupport (fun u => Taper.phi ϱ L w u ^ 2) :=
    (Taper.phi_hasCompactSupport hϱ (L := L) hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hGzero : ∀ u, L / 2 < |u| → Taper.phi ϱ L w u ^ 2 = 0 := fun u hu => by
    rw [Taper.phi_eq_zero hϱ hw0 hu.le, zero_pow two_ne_zero]
  have hH : ContDiff ℝ 2 (fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2)) := by
    rw [← phiM_sq_eq]; exact (phiP8_contDiff hϱ hw0 h2wL).pow 2
  have hHcs : HasCompactSupport (fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2)) := by
    rw [← phiM_sq_eq]
    exact (phiM_hasCompactSupport (f := f) (L := L) hϱ hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hmain := integral_abs_deriv2_mul_le (F := fun u => f u * f u) (G := fun u => Taper.phi ϱ L w u ^ 2)
    (L := L) one_pos (by positivity : (0:ℝ) ≤ 2 * 2 / L)
    (by positivity : (0:ℝ) ≤ (2 * 25 + 2 * 2 ^ 2) / L ^ 2)
    hsm2 hF0 hF1 hF2 hG hGcs hGzero hH hHcs
  show ∫ u, |deriv (deriv (fun u => phiM f ϱ L w u ^ 2)) u| ≤ cP8 ϱ / w
  rw [phiM_sq_eq]
  have hI0 := integral_abs_phi_sq_le hϱ hw0 h2wL
  have hI1 : ∫ u, |deriv (fun u => Taper.phi ϱ L w u ^ 2) u| = 2 := Taper.integral_abs_deriv_phi_sq hϱ hw0 h2wL
  have hI2 : ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u| ≤ Taper.cRho ϱ / w :=
    Taper.integral_abs_deriv2_phi_sq_le hϱ hw h2wL
  rw [hI1] at hmain
  refine hmain.trans ?_
  have e1 : (2 * 25 + 2 * 2 ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2| ≤ (25 + 2 ^ 2) / w := by
    calc (2 * 25 + 2 * 2 ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2|
        ≤ (2 * 25 + 2 * 2 ^ 2) / L ^ 2 * L := by gcongr
      _ = (2 * 25 + 2 * 2 ^ 2) / L := by field_simp
      _ ≤ (25 + 2 ^ 2) / w := by rw [div_le_div_iff₀ hL hw0]; nlinarith
  have e2 : 2 * (2 * 2 / L) * 2 ≤ 2 / w := by
    rw [show 2 * (2 * 2 / L) * 2 = 16 / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
  calc (2 * 25 + 2 * 2 ^ 2) / L ^ 2 * (∫ u, |Taper.phi ϱ L w u ^ 2|) + 2 * (2 * 2 / L) * 2
        + ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u|
      ≤ (25 + 2 ^ 2) / w + 2 / w + Taper.cRho ϱ / w := by linarith
    _ = cP8 ϱ / w := by simp only [cP8, cMod]; ring

/-- **φ♮ is an admissible window** with `(w, c) = (w, cMod ϱ 2 25)`, for every `1 ≤ w`, `8w ≤ L`
(eventually in T, which is all that `localHypsCore` consumes).  All twelve fields proved. -/
theorem admWindow_phiP8 (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    AdmWindow (phiP8 ϱ L w) L w (cP8 ϱ) where
  one_le_w := hw
  w8 := hwL
  four_le_c := four_le_cMod hϱ (by norm_num) (by norm_num)
  even := phiP8_even
  nonneg := phiP8_nonneg hϱ
  le_one := phiP8_le_one hϱ (by linarith) (by linarith)
  contDiff := phiP8_contDiff hϱ (by linarith) (by linarith)
  support := fun _ hu => phiP8_eq_zero hϱ (by linarith) hu
  l1_deriv := integral_abs_deriv_phiP8_le hϱ hw hwL
  l1_deriv_sq := integral_abs_deriv_phiP8_sq_le hϱ hw hwL
  l1_deriv2 := integral_abs_deriv2_phiP8_le hϱ hw (by linarith)
  l1_deriv2_sq := integral_abs_deriv2_phiP8_sq_le hϱ hw (by linarith)

/-! ## 6. The window moments a, b, J (exact rationals; the device of XiPrime/Certificate/Poly.lean) -/

/-- `∫_{−1/2}^{1/2} v = 40497/43750`. -/
theorem integral_vP8 : ∫ s in (-(1:ℝ)/2)..(1/2), vP8 s = 40497 / 43750 := by
  have h : (fun s => vP8 s) = polyEval [1, 0, 127/625, 0, -8997/625, 0, 24748/625, 0, 384/625] := by
    ext s; simp [vP8_eq, polyEval, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]
  simp [polyInt, Finset.sum_range_succ]
  norm_num

/-- `∫_{−1/2}^{1/2} v² = 16536677606497/19144125000000`. -/
theorem integral_vP8_sq :
    ∫ s in (-(1:ℝ)/2)..(1/2), vP8 s ^ 2 = 16536677606497 / 19144125000000 := by
  have h : (fun s => vP8 s ^ 2) = polyEval [1, 0, 254/625, 0, -11230121/390625, 0, 28649762/390625, 0,
      87712001/390625, 0, -445217976/390625, 0, 605553808/390625, 0, 19006464/390625, 0, 147456/390625] := by
    ext s; simp [vP8_eq, polyEval, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]
  simp [polyInt, Finset.sum_range_succ]
  norm_num

/-- closed form of the autocorrelation `(v⋆v)(r) = ∫_{−1/2}^{1/2−r} v(s)v(s+r) ds` (degree 17 in r). -/
def convP8 (r : ℝ) : ℝ :=
  16536677606497/19144125000000 - 14907321/25000000 * r + 7775220529/46921875000 * r ^ 2
    - 12301277/1500000 * r ^ 3 + 686819781833/23460937500 * r ^ 4 - 1779182309/37500000 * r ^ 5
    + 17087558678/451171875 * r ^ 6 - 168708258/13671875 * r ^ 7 + 7775424/13671875 * r ^ 8
    - 130260989/246093750 * r ^ 9 + 222430172/451171875 * r ^ 11 - 749456756/5865234375 * r ^ 13
    - 6335488/5865234375 * r ^ 15 - 8192/4748046875 * r ^ 17

/-- the coefficients (in s) of `s ↦ v(s)·v(s+r)`. -/
def coeffS8 (r : ℝ) : List ℝ :=
  [1 + 127/625 * r ^ 2 - 8997/625 * r ^ 4 + 24748/625 * r ^ 6 + 384/625 * r ^ 8,
   254/625 * r - 35988/625 * r ^ 3 + 148488/625 * r ^ 5 + 3072/625 * r ^ 7,
   254/625 - 33722621/390625 * r ^ 2 + 230869881/390625 * r ^ 4 + 9862996/390625 * r ^ 6 + 48768/390625 * r ^ 8,
   -22460242/390625 * r + 304779524/390625 * r ^ 3 + 32297976/390625 * r ^ 5 + 390144/390625 * r ^ 7,
   -11230121/390625 + 224014167/390625 * r ^ 2 + 144890949/390625 * r ^ 4 - 221292252/390625 * r ^ 6
     - 3454848/390625 * r ^ 8,
   85949286/390625 * r + 400083956/390625 * r ^ 3 - 1333215528/390625 * r ^ 5 - 27638784/390625 * r ^ 7,
   28649762/390625 + 108536798/78125 * r ^ 2 - 3559110336/390625 * r ^ 4 + 103145552/78125 * r ^ 6
     + 9503232/390625 * r ^ 8,
   350848004/390625 * r - 5341055136/390625 * r ^ 3 + 3481309536/390625 * r ^ 5 + 76025856/390625 * r ^ 7,
   87712001/390625 - 4674398604/390625 * r ^ 2 + 8941658352/390625 * r ^ 4 + 275593728/390625 * r ^ 6
     + 147456/390625 * r ^ 8,
   -445217976/78125 * r + 481679168/15625 * r ^ 3 + 589200384/390625 * r ^ 5 + 1179648/390625 * r ^ 7,
   -445217976/390625 + 9069487728/390625 * r ^ 2 + 161554944/78125 * r ^ 4 + 4128768/390625 * r ^ 6,
   3633322848/390625 * r + 722245632/390625 * r ^ 3 + 8257536/390625 * r ^ 5,
   605553808/390625 + 408638976/390625 * r ^ 2 + 2064384/78125 * r ^ 4,
   133045248/390625 * r + 8257536/390625 * r ^ 3,
   19006464/390625 + 4128768/390625 * r ^ 2,
   1179648/390625 * r,
   147456/390625]

theorem vConv_vP8 (r : ℝ) : vConv vP8 r = convP8 r := by
  unfold vConv
  have h : (fun s => vP8 s * vP8 (s + r)) = polyEval (coeffS8 r) := by
    ext s; simp [vP8_eq, polyEval, coeffS8, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]
  simp [polyInt, coeffS8, Finset.sum_range_succ, convP8]
  ring

/-- `J := 2∫₀¹ r·(v⋆v)(r) dr (= ∬|s−s'| v(s)v(s') ds ds') = 166041852098299/606230625000000`. -/
theorem jP8 : 2 * ∫ r in (0:ℝ)..1, r * vConv vP8 r = 166041852098299 / 606230625000000 := by
  have h : (fun r => r * vConv vP8 r) = polyEval [0, 16536677606497/19144125000000, -14907321/25000000,
      7775220529/46921875000, -12301277/1500000, 686819781833/23460937500, -1779182309/37500000,
      17087558678/451171875, -168708258/13671875, 7775424/13671875, -130260989/246093750, 0,
      222430172/451171875, 0, -749456756/5865234375, 0, -6335488/5865234375, 0, -8192/4748046875] := by
    ext r; rw [vConv_vP8]; simp [convP8, polyEval, Finset.sum_range_succ]; ring
  rw [h, integral_polyEval]
  simp [polyInt, Finset.sum_range_succ]
  norm_num

/-! ## 7. The constant: exact H, and degree-0 homogeneity -/

/-- `H(v) = 2 − (b + J)/a² = 26957030199857/40103091391077` (the draft's value, sec_zeta.tex l.596). -/
theorem H_P8 :
    2 - (16536677606497 / 19144125000000 + 166041852098299 / 606230625000000) / (40497 / 43750 : ℝ) ^ 2
      = 26957030199857 / 40103091391077 := by
  norm_num

/-- the tree's ratio (Zeta23/ThmD/AssemblyD.lean) is invariant under ψ ↦ κψ
(a ↦ κa, b ↦ κ²b, J ↦ κ²J): the normalisation of the window is immaterial. -/
theorem cRatio_scale (lam1 a b J κ : ℝ) (hκ : κ ≠ 0) :
    ThmD.cRatio lam1 (κ * a) (κ ^ 2 * b) (κ ^ 2 * J) = ThmD.cRatio lam1 a b J := by
  unfold ThmD.cRatio
  rw [show lam1 * (κ * a) ^ 2 = κ ^ 2 * (lam1 * a ^ 2) by ring,
    show κ ^ 2 * b + lam1 ^ 2 * (κ ^ 2 * J) = κ ^ 2 * (b + lam1 ^ 2 * J) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hκ)]

/-- the moments of ψ♮ = (4/5)v: `a♮ = (4/5)·40497/43750`, `b♮ = (16/25)·16536677606497/19144125000000`. -/
theorem integral_psiN : ∫ s in (-(1:ℝ)/2)..(1/2), psiN s = 4 / 5 * (40497 / 43750) := by
  unfold psiN; rw [intervalIntegral.integral_const_mul, integral_vP8]

theorem integral_psiN_sq :
    ∫ s in (-(1:ℝ)/2)..(1/2), psiN s ^ 2 = 16 / 25 * (16536677606497 / 19144125000000) := by
  have h : (fun s => psiN s ^ 2) = fun s => 16 / 25 * vP8 s ^ 2 := by ext s; unfold psiN; ring
  rw [h, intervalIntegral.integral_const_mul, integral_vP8_sq]

/-- `b♮ ≥ 1/2 + 1/20`, i.e. `b♮ ≥ 1/2 + 2w/L` once `L ≥ 40w` (needed for `LocalHypsCore.b_ge_half`). -/
theorem bN_margin : (1 : ℝ) / 2 + 1 / 20 ≤ 16 / 25 * (16536677606497 / 19144125000000) := by norm_num

end PolyWindow
end ZetaS

end

#print axioms ZetaS.PolyWindow.psiTilde_pos_le
#print axioms ZetaS.PolyWindow.vP8_not_antitoneOn
#print axioms ZetaS.PolyWindow.tv_mul_ramp_le
#print axioms ZetaS.PolyWindow.integral_abs_deriv_phiP8_le
#print axioms ZetaS.PolyWindow.integral_abs_deriv_phiP8_sq_le
#print axioms ZetaS.PolyWindow.admWindow_phiP8
#print axioms ZetaS.PolyWindow.integral_vP8
#print axioms ZetaS.PolyWindow.integral_vP8_sq
#print axioms ZetaS.PolyWindow.vConv_vP8
#print axioms ZetaS.PolyWindow.jP8
#print axioms ZetaS.PolyWindow.H_P8
#print axioms ZetaS.PolyWindow.cRatio_scale
