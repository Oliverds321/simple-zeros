/-
Sub-node Z9a3 (agent L3_1) — the window matrix in frame form: in hat units,
  hat(Az) = Σ_{ρ ∈ 𝒵(I′), β = ½} m_ρ u_ρ u_ρᵀ + toC(Qoff),   Qoff = Σ_{ρ ∈ 𝒵(I′), β > ½} 2m_ρ (x_ρx_ρᵀ − y_ρy_ρᵀ),
with u_ρ = (uC φ_T L T γ_ρ k)_{k<d}, x + iy = u (draft eq:zeta-Ghat and l.198–203). Steps: finsum over ZIprime = Finset
sum over `ZeroSide.ZI`; (P.atV ψ T).phiHat = vHat φ_T (`Params.atV_phiHat`), (aL²)⁻¹φ̂φ̂ = uC·uC (aL² = L∫φ², √·√);
split 𝒵(I′) = {β = ½} ⊔ {β > ½} ⊔ reflect{β > ½}; u_{1−ρ̄} = conj u_ρ (Z8 with `gammaOf_reflect`), m_{1−ρ̄} = m_ρ
(`ZeroConfig.mult_reflect`), and uuᵀ + ūūᵀ = 2(xxᵀ − yyᵀ).
-/
import ZetaS.ZeroSide.Z9s_Spec
import ZetaS.ZeroSide.Z9a2_OffBlock
import ZetaS.ZeroSide.Z8_VHatConj
import Zeta23.XiPrime.QuarticWindow.ZeroSide

noncomputable section

open Matrix

namespace ZetaS
namespace Z9

open Zeta23

/-- the normalised evaluation vector of a zero (complex ordinate `gammaOf ρ`), on the grid `k < d`. -/
def uvec (P : Params) (ψ : ℝ → ℝ) (T : ℝ) (ρ : ℂ) : Fin (P.d T) → ℂ :=
  fun k => uC (P.phiV ψ T) (P.L T) T (gammaOf ρ) ((k : ℕ) : ℤ)

theorem hatAz_decomp (Z : ZeroConfig) {P : Params} (hP : P.Valid) {ψ : ℝ → ℝ} (heven : ∀ s, ψ (-s) = ψ s)
    {c : ℝ} {T : ℝ} (hW : AdmWindow (P.phiV ψ T) (P.L T) P.w c) :
    (P.atV ψ T).hat T (Z.Az (P.atV ψ T) T)
      = ∑ ρ ∈ (ZeroSide.ZI Z T).filter (fun ρ => ρ.re = 1 / 2),
            (Z.mult ρ : ℂ) • vecMulVec (uvec P ψ T ρ) (uvec P ψ T ρ)
        + toC (offBlock ((ZeroSide.ZI Z T).filter (fun ρ => 1 / 2 < ρ.re)) (fun ρ => 2 * (Z.mult ρ : ℝ))
            (fun ρ k => (uvec P ψ T ρ k).re) (fun ρ k => (uvec P ψ T ρ k).im)) := by
  classical
  have hL0 : 0 < P.L T := hW.L_pos
  have hD0 : 0 ≤ P.L T * ∫ u, P.phiV ψ T u ^ 2 :=
    mul_nonneg hL0.le (MeasureTheory.integral_nonneg fun u => sq_nonneg _)
  have hc : (P.atV ψ T).a T * (P.atV ψ T).L T ^ 2 = P.L T * ∫ u, P.phiV ψ T u ^ 2 := by
    rw [Params.atV_a T hP heven]
    show AdmWindow.av (P.phiV ψ T) (P.L T) * P.L T ^ 2 = _
    simp only [AdmWindow.av]; field_simp
  have huu : ∀ z w : ℂ,
      (AdmWindow.vHat (P.phiV ψ T) z / ((Real.sqrt (P.L T * ∫ u, P.phiV ψ T u ^ 2) : ℝ) : ℂ)) *
        (AdmWindow.vHat (P.phiV ψ T) w / ((Real.sqrt (P.L T * ∫ u, P.phiV ψ T u ^ 2) : ℝ) : ℂ))
      = (((P.L T * ∫ u, P.phiV ψ T u ^ 2)⁻¹ : ℝ) : ℂ) *
          (AdmWindow.vHat (P.phiV ψ T) z * AdmWindow.vHat (P.phiV ψ T) w) := by
    intro z w
    rw [div_mul_div_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt hD0, div_eq_inv_mul, Complex.ofReal_inv]
  set S := (ZeroSide.ZI Z T).filter (fun ρ => ρ.re = 1 / 2) with hS
  set A := (ZeroSide.ZI Z T).filter (fun ρ => 1 / 2 < ρ.re) with hA
  set B := (ZeroSide.ZI Z T).filter (fun ρ => ρ.re < 1 / 2) with hB
  refine Matrix.ext fun (k : Fin (P.d T)) (l : Fin (P.d T)) => ?_
  set f : ℂ → ℂ := fun ρ => (Z.mult ρ : ℂ) * (uvec P ψ T ρ k * uvec P ψ T ρ l) with hf
  have hLHS : (P.atV ψ T).hat T (Z.Az (P.atV ψ T) T) k l = ∑ ρ ∈ ZeroSide.ZI Z T, f ρ := by
    rw [ZeroSide.hat_eq]
    show ((((P.atV ψ T).a T * (P.atV ψ T).L T ^ 2)⁻¹ : ℝ) : ℂ) * Z.Az (P.atV ψ T) T k l = _
    rw [hc]
    change _ * ∑ᶠ ρ ∈ Z.ZIprime T, Z.Gsummand (P.atV ψ T) T k l ρ = _
    rw [finsum_mem_eq_finite_toFinset_sum _ (ZeroSide.ZIprime_finite Z T), Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hf, ZeroConfig.Gsummand, uvec, uC, Params.atV_phiHat T hP heven, XiPrime.atV_tau_eq]
    rw [huu]; push_cast; ring
  have hsplit : ∑ ρ ∈ ZeroSide.ZI Z T, f ρ = ∑ ρ ∈ S, f ρ + ∑ ρ ∈ A, f ρ + ∑ ρ ∈ B, f ρ := by
    rw [← Finset.sum_filter_add_sum_filter_not (ZeroSide.ZI Z T) (fun ρ => ρ.re = 1 / 2),
      ← Finset.sum_filter_add_sum_filter_not ((ZeroSide.ZI Z T).filter (fun ρ => ¬ ρ.re = 1 / 2))
        (fun ρ => 1 / 2 < ρ.re), Finset.filter_filter, Finset.filter_filter, add_assoc]
    congr 2
    · refine Finset.sum_congr (Finset.filter_congr fun ρ _ => ?_) fun _ _ => rfl
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by linarith, h⟩
    · refine Finset.sum_congr (Finset.filter_congr fun ρ _ => ?_) fun _ _ => rfl
      constructor
      · rintro ⟨h1, h2⟩; push Not at h2; exact lt_of_le_of_ne h2 h1
      · intro h; exact ⟨by linarith, by linarith⟩
  have hrefl : ∑ ρ ∈ B, f ρ = ∑ ρ ∈ A, f (reflect ρ) := by
    refine Finset.sum_nbij' reflect reflect ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      simp only [hA, hB, Finset.mem_filter] at hρ ⊢
      exact ⟨ZeroSide.reflect_mem_ZI Z T hρ.1, by rw [ZeroSide.reflect_re]; linarith⟩
    · intro ρ hρ
      simp only [hA, hB, Finset.mem_filter] at hρ ⊢
      exact ⟨ZeroSide.reflect_mem_ZI Z T hρ.1, by rw [ZeroSide.reflect_re]; linarith⟩
    · intro ρ _; exact ZeroSide.reflect_reflect ρ
    · intro ρ _; exact ZeroSide.reflect_reflect ρ
    · intro ρ _; rw [ZeroSide.reflect_reflect]
  have hpair : ∀ ρ ∈ A, f ρ + f (reflect ρ) = (((2 * (Z.mult ρ : ℝ)) *
      ((uvec P ψ T ρ k).re * (uvec P ψ T ρ l).re - (uvec P ψ T ρ k).im * (uvec P ψ T ρ l).im) : ℝ) : ℂ) := by
    intro ρ hρ
    have hcar : ρ ∈ Z.carrier :=
      ZeroSide.mem_carrier_of_mem_ZI Z T (Finset.mem_filter.mp hρ).1
    have hm : Z.mult (reflect ρ) = Z.mult ρ := Z.mult_reflect ρ hcar
    have hu : ∀ j, uvec P ψ T (reflect ρ) j = (starRingEnd ℂ) (uvec P ψ T ρ j) := by
      intro j; simp only [uvec]; rw [ZeroSide.gammaOf_reflect, uC_conj hW]
    show (Z.mult ρ : ℂ) * (uvec P ψ T ρ k * uvec P ψ T ρ l)
        + (Z.mult (reflect ρ) : ℂ) * (uvec P ψ T (reflect ρ) k * uvec P ψ T (reflect ρ) l) = _
    rw [hm, hu k, hu l]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hLHS, hsplit, hrefl, add_assoc, ← Finset.sum_add_distrib, Finset.sum_congr rfl hpair]
  rw [Matrix.add_apply]
  congr 1
  · simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, hf]
  · simp only [toC, offBlock, Matrix.map_apply, Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply,
      Matrix.sub_apply, vecMulVec_apply, smul_eq_mul, Complex.ofReal_sum]

end Z9
end ZetaS
