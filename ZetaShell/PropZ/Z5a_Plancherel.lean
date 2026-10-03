/-
L7_5 (28 Sep 2026): proof of the Plancherel half of Z5a (lem:shell-5a), for
ν = Σ_{y∈F} a_y δ_y + g(y) dy (g continuous, compactly supported). With φ(z) = f(Δz):
G = Σ a_y φ(· − y) + g ⋆ φ is a compactly supported smooth (Schwartz) function, 𝓕G(β) = φ̂(β)·S(−β),
φ̂(β) = Δ⁻¹ f̂(β/Δ), and Plancherel (`SchwartzMap.integral_norm_sq_fourier`) gives the identity.
-/
import ZetaShell.PropZ.ZDefs

open MeasureTheory Complex FourierTransform

namespace ZetaShell.PropZ

theorem eA_eq_fourierChar (x : ℝ) : eA x = ((Real.fourierChar x : Circle) : ℂ) := by
  rw [eA, Real.fourierChar_apply]; congr 1; push_cast; ring

theorem eA_add (u v : ℝ) : eA (u + v) = eA u * eA v := by
  rw [eA, eA, eA, ← Complex.exp_add]; congr 1; push_cast; ring

theorem fhat_neg (f : ℝ → ℝ) (hf : TestFn f) (η : ℝ) : fhat f (-η) = fhat f η := by
  unfold fhat
  rw [← integral_neg_eq_self]
  congr 1; funext z
  rw [hf.even]; congr 2; ring

theorem testFn_hasCompactSupport (f : ℝ → ℝ) (hf : TestFn f) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset (isCompact_Icc (a := -(1 / 8 : ℝ)) (b := 1 / 8)) (isClosed_tsupport f)
    (hf.supp.trans Set.Ioo_subset_Icc_self)

theorem norm_eA (x : ℝ) : ‖eA x‖ = 1 := by
  rw [eA, show (2 * Real.pi * I * x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem integrable_char_smul {G : ℝ → ℂ} (hG : Integrable G) (β : ℝ) :
    Integrable (fun v : ℝ => (Real.fourierChar (-(v * β)) : Circle) • G v) := by
  have e : (fun v : ℝ => (Real.fourierChar (-(v * β)) : Circle) • G v) = fun v => eA (-(v * β)) * G v := by
    funext v; rw [Circle.smul_def, smul_eq_mul, eA_eq_fourierChar]
  have hc : Continuous (fun v : ℝ => eA (-(v * β))) := by unfold eA; fun_prop
  rw [e]
  exact hG.bdd_mul (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun v => (norm_eA _).le)

/-- `φ(z) = f(Δz)` as a complex function. -/
noncomputable def phiD (f : ℝ → ℝ) (Δ : ℝ) (z : ℝ) : ℂ := ((f (Δ * z) : ℝ) : ℂ)

theorem phiD_contDiff (f : ℝ → ℝ) (hf : TestFn f) (Δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phiD f Δ) := by
  unfold phiD
  exact ofRealCLM.contDiff.comp (hf.smooth.comp (contDiff_const.mul contDiff_id))

theorem phiD_hasCompactSupport (f : ℝ → ℝ) (hf : TestFn f) (Δ : ℝ) (hΔ : 0 < Δ) :
    HasCompactSupport (phiD f Δ) := by
  unfold phiD
  have h1 : HasCompactSupport (fun z : ℝ => f (Δ * z)) := by
    have := (testFn_hasCompactSupport f hf).comp_smul (hΔ.ne')
    simpa [smul_eq_mul] using this
  exact h1.comp_left (g := Complex.ofReal) Complex.ofReal_zero

theorem phiD_integrable (f : ℝ → ℝ) (hf : TestFn f) (Δ : ℝ) (hΔ : 0 < Δ) : Integrable (phiD f Δ) :=
  (phiD_contDiff f hf Δ).continuous.integrable_of_hasCompactSupport (phiD_hasCompactSupport f hf Δ hΔ)

/-- `φ̂(β) = Δ⁻¹ f̂(β/Δ)`. -/
theorem fourier_phiD (f : ℝ → ℝ) (Δ : ℝ) (hΔ : 0 < Δ) (β : ℝ) :
    𝓕 (phiD f Δ) β = (Δ⁻¹ : ℂ) * fhat f (β / Δ) := by
  rw [Real.fourier_real_eq]
  have e : ∀ v : ℝ, (Real.fourierChar (-(v * β)) : Circle) • phiD f Δ v
      = (fun z : ℝ => (f z : ℂ) * eA (-(z * (β / Δ)))) (Δ * v) := by
    intro v
    simp only [phiD, Circle.smul_def, smul_eq_mul, ← eA_eq_fourierChar]
    rw [mul_comm]; congr 2; field_simp
  simp_rw [e]
  rw [Measure.integral_comp_mul_left (fun z : ℝ => (f z : ℂ) * eA (-(z * (β / Δ)))) Δ, fhat,
    abs_of_pos (inv_pos.mpr hΔ)]
  rw [Complex.real_smul]; push_cast; ring

/-- `∫ 𝐞(−vβ) φ(v − y) dv = e(−yβ) φ̂(β)`. -/
theorem fourier_translate (φ : ℝ → ℂ) (y β : ℝ) :
    𝓕 (fun v => φ (v - y)) β = eA (-(y * β)) * 𝓕 φ β := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have := integral_sub_right_eq_self (μ := volume)
    (fun u : ℝ => (Real.fourierChar (-((u + y) * β)) : Circle) • φ u) y
  simp only [sub_add_cancel] at this
  rw [this, ← integral_const_mul]
  congr 1; funext u
  simp only [Circle.smul_def, smul_eq_mul, ← eA_eq_fourierChar]
  rw [show -((u + y) * β) = -(y * β) + -(u * β) by ring, eA_add]; ring

theorem hasCompactSupport_finsum (F : Finset ℝ) (a : ℝ → ℂ) (φ : ℝ → ℂ) (hφs : HasCompactSupport φ) :
    HasCompactSupport (fun x => ∑ y ∈ F, a y * φ (x - y)) := by
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.zero
  | insert y F hy ih =>
    simp only [Finset.sum_insert hy]
    exact (HasCompactSupport.mul_left (f := fun _ : ℝ => a y)
      (hφs.comp_homeomorph (Homeomorph.subRight y))).add ih

/-- the compactly supported smooth function `G` of Lemma 5a and its Fourier transform. -/
theorem exists_G (f : ℝ → ℝ) (hf : TestFn f)
    (F : Finset ℝ) (a : ℝ → ℂ) (g : ℝ → ℂ) (hg : Continuous g) (hgs : HasCompactSupport g)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ G : ℝ → ℂ, ∃ _ : ContDiff ℝ (⊤ : ℕ∞) G, ∃ _ : HasCompactSupport G,
      (∀ x, ∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ) = G x) ∧
      ∀ β, 𝓕 G β = (Δ⁻¹ : ℂ) * fhat f (β / Δ) * (∑ y ∈ F, a y * eA (y * (-β)) + ∫ y, g y * eA (y * (-β))) := by
  set φ := phiD f Δ with hφ
  have hφc : Continuous φ := (phiD_contDiff f hf Δ).continuous
  have hφs : HasCompactSupport φ := phiD_hasCompactSupport f hf Δ hΔ
  have hφi : Integrable φ := phiD_integrable f hf Δ hΔ
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgs
  -- the function G
  set Gd : ℝ → ℂ := fun x => ∑ y ∈ F, a y * φ (x - y) with hGd
  set Gc : ℝ → ℂ := convolution g φ (ContinuousLinearMap.mul ℂ ℂ) volume with hGc
  have hGeq : ∀ x, ∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)
      = Gd x + Gc x := by
    intro x
    have hev : ∀ y, (f (Δ * (y - x)) : ℂ) = φ (x - y) := by
      intro y
      simp only [hφ, phiD]
      rw [show Δ * (y - x) = -(Δ * (x - y)) by ring, hf.even]
    simp only [hGd, hGc, convolution_def, ContinuousLinearMap.mul_apply', hev]
  have hGd_smooth : ContDiff ℝ (⊤ : ℕ∞) Gd := by
    simp only [hGd]
    exact ContDiff.sum fun y _ => contDiff_const.mul ((phiD_contDiff f hf Δ).comp (contDiff_id.sub contDiff_const))
  have hGc_eq : Gc = convolution g φ (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext x; simp only [hGc, convolution_def, ContinuousLinearMap.mul_apply']
  have hGc_smooth : ContDiff ℝ (⊤ : ℕ∞) Gc := by
    rw [hGc_eq]
    exact hφs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hg.locallyIntegrable
      (phiD_contDiff f hf Δ)
  have hGd_supp : HasCompactSupport Gd := hasCompactSupport_finsum F a φ hφs
  have hGc_supp : HasCompactSupport Gc := hgs.convolution _ hφs
  set G : ℝ → ℂ := Gd + Gc with hG
  have hG_smooth : ContDiff ℝ (⊤ : ℕ∞) G := hGd_smooth.add hGc_smooth
  have hG_supp : HasCompactSupport G := hGd_supp.add hGc_supp
  -- its Fourier transform
  have hFG : ∀ β, 𝓕 G β = 𝓕 φ β * (∑ y ∈ F, a y * eA (y * (-β)) + ∫ y, g y * eA (y * (-β))) := by
    intro β
    have hGdi : Integrable Gd := hGd_smooth.continuous.integrable_of_hasCompactSupport hGd_supp
    have hGci : Integrable Gc := hGc_smooth.continuous.integrable_of_hasCompactSupport hGc_supp
    have hadd : 𝓕 G β = 𝓕 Gd β + 𝓕 Gc β := by
      rw [hG, Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq, ← integral_add]
      · congr 1; funext v; simp [smul_add]
      · exact integrable_char_smul hGdi β
      · exact integrable_char_smul hGci β
    have hd : 𝓕 Gd β = ∑ y ∈ F, a y * (eA (-(y * β)) * 𝓕 φ β) := by
      rw [Real.fourier_real_eq]
      simp only [hGd, Finset.smul_sum]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun y _ => ?_
        rw [← fourier_translate φ y β, Real.fourier_real_eq, ← integral_const_mul]
        congr 1; funext v; simp only [Circle.smul_def, smul_eq_mul]; ring
      · intro y _
        have : Integrable (fun v => a y * φ (v - y)) :=
          (hφi.comp_sub_right y).const_mul (a y)
        exact integrable_char_smul this β
    have hc : 𝓕 Gc β = 𝓕 g β * 𝓕 φ β := Real.fourier_mul_convolution_eq hgi hφi β
    have hgF : 𝓕 g β = ∫ y, g y * eA (y * (-β)) := by
      rw [Real.fourier_real_eq]; congr 1; funext y
      simp only [Circle.smul_def, smul_eq_mul, ← eA_eq_fourierChar]; rw [mul_comm]; congr 2; ring
    rw [hadd, hd, hc, hgF, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [show y * -β = -(y * β) by ring]; ring
    · ring
  refine ⟨G, hG_smooth, hG_supp, fun x => by rw [hGeq x]; rfl, fun β => ?_⟩
  rw [hFG β, fourier_phiD f Δ hΔ β]

theorem norm_inv_ofReal (Δ : ℝ) (hΔ : 0 < Δ) : ‖(Δ⁻¹ : ℂ)‖ = Δ⁻¹ := by
  rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΔ)]

/-- pointwise: `|S(β)|² Φ(β/Δ) = (Δ²/c) |Ĝ(−β)|²`. -/
theorem S_Phi_eq (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c)
    (F : Finset ℝ) (a : ℝ → ℂ) (g : ℝ → ℂ) (Δ : ℝ) (hΔ : 0 < Δ) (G : ℝ → ℂ)
    (hFG : ∀ β, 𝓕 G β = (Δ⁻¹ : ℂ) * fhat f (β / Δ) * (∑ y ∈ F, a y * eA (y * (-β)) + ∫ y, g y * eA (y * (-β))))
    (β : ℝ) :
    ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2 * Phi f c (β / Δ) = Δ ^ 2 / c * ‖𝓕 G (-β)‖ ^ 2 := by
  rw [hFG (-β), norm_mul, norm_mul, norm_inv_ofReal Δ hΔ, show (-β) / Δ = -(β / Δ) by ring, fhat_neg f hf]
  simp only [neg_neg, Phi]
  generalize ‖fhat f (β / Δ)‖ = A
  generalize ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ = B
  have hΔ0 : Δ ≠ 0 := hΔ.ne'
  first | (field_simp; ring) | field_simp

theorem plancherel_identity' (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c)
    (F : Finset ℝ) (a : ℝ → ℂ) (g : ℝ → ℂ) (hg : Continuous g) (hgs : HasCompactSupport g)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ∫ β, ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2 * Phi f c (β / Δ)
      = Δ ^ 2 / c * ∫ x, ‖∑ y ∈ F, a y * (f (Δ * (y - x)) : ℂ) + ∫ y, g y * (f (Δ * (y - x)) : ℂ)‖ ^ 2 := by
  obtain ⟨G, hG_smooth, hG_supp, hGeq, hFG⟩ := exists_G f hf F a g hg hgs Δ hΔ
  have hPl : ∫ β, ‖𝓕 G β‖ ^ 2 = ∫ x, ‖G x‖ ^ 2 := by
    have := SchwartzMap.integral_norm_sq_fourier (hG_supp.toSchwartzMap hG_smooth)
    have hcoe : ⇑(hG_supp.toSchwartzMap hG_smooth) = G := rfl
    rw [SchwartzMap.fourier_coe, hcoe] at this
    exact this
  simp_rw [S_Phi_eq f hf c hc0 F a g Δ hΔ G hFG, hGeq]
  rw [integral_const_mul, integral_neg_eq_self (fun β => ‖𝓕 G β‖ ^ 2) volume, hPl]

theorem plancherel_integrable (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c)
    (F : Finset ℝ) (a : ℝ → ℂ) (g : ℝ → ℂ) (hg : Continuous g) (hgs : HasCompactSupport g)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    Integrable (fun β => ‖∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β)‖ ^ 2 * Phi f c (β / Δ)) := by
  obtain ⟨G, hG_smooth, hG_supp, hGeq, hFG⟩ := exists_G f hf F a g hg hgs Δ hΔ
  set h := 𝓕 (hG_supp.toSchwartzMap hG_smooth) with hh
  have hhG : ∀ β, h β = 𝓕 G β := fun β => rfl
  have hint : Integrable (fun β => ‖h β‖ ^ 2) := by
    refine (h.integrable.norm.const_mul ‖h.toBoundedContinuousFunction‖).mono'
      (h.continuous.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hb : ‖h x‖ ≤ ‖h.toBoundedContinuousFunction‖ := h.toBoundedContinuousFunction.norm_coe_le_norm x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hint' : Integrable (fun β => ‖𝓕 G (-β)‖ ^ 2) := by
    simp_rw [← hhG]; exact hint.comp_neg
  simp_rw [S_Phi_eq f hf c hc0 F a g Δ hΔ G hFG]
  exact hint'.const_mul _

end ZetaShell.PropZ
