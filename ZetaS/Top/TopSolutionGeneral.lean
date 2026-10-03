/-
ZetaS/Top/TopSolutionGeneral.lean — the ζ headlines for a GENERAL majorant threshold β < λ_c, and the forms
conditional on the open nodes (L3_2's proofs, moved here from TopSolution.lean and A8K.lean by the integrator L0_5,
28 Sep 2026, lead's ruling b of 12:25). These rest on the open node A7g/A8g (`ZetaS.Skeleton.A8g_SigmaDistGeneral`,
`sorry`); neither `TopFinal` nor `TopSSC` imports this module, so the certificate-only headlines and the comparator
Solution have a sorry-free import closure. The β-forms are renamed `_of_majorant` (one name per statement: the
comparator's `zeta_simple_K5` … are the certificate-only statements).
-/
import ZetaS.Top.TopSolution
import ZetaS.Skeleton.A8g_SigmaDistGeneral
import ZetaS.Top.A8K

open Filter Topology Asymptotics

namespace ZetaS

namespace A8K

/-- A7g's statement from the open node `OLL_gen` (moved from A8K.lean). -/
theorem a7g_holds : A7gStmt := fun _ _ Fm _ W hc _ hm hr hML => OLL_gen Fm W hc hm hr hML

end A8K

namespace Top

/-! ### The statements of the open node A8g, as Props -/

/-- The statement of the open node **A8g** (simple zeros). -/
def A8gSimpleStmt : Prop := ∀ (N : ℝ → ℝ) (R : ℝ) (Fm : FrameFamily N R (kPsi psiCos16)) (K : ℕ)
    (W : MarkWeights K), LocalCertAM (kPsi psiCos16) W → ∀ β : ℝ, MajorantCert psiCos16 β →
    RobustAM (W.a 0) (W.a 1) W.nu β → ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (W.a 0) (W.a 1) W.nu - ε) * N T ≤ ((Fm.F T).NsW : ℝ)

/-- The statement of the open node **A8g** (distinct zeros). -/
def A8gDistStmt : Prop := ∀ (N : ℝ → ℝ) (R : ℝ) (Fm : FrameFamily N R (kPsi psiCos16)) (K : ℕ)
    (W : MarkWeights K), LocalCertAM (kPsi psiCos16) W → ∀ β : ℝ, MajorantCert psiCos16 β →
    RobustAM (W.a 0) (W.a 1) W.nu β → ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (W.a 0) (W.a 1) W.nu - ε) * N T ≤ ((Fm.F T).NdW : ℝ)

theorem a8g_simple_holds : A8gSimpleStmt := fun _ _ Fm _ W hc _ hm hr => sigma_abstract_gen Fm W hc hm hr
theorem a8g_dist_holds : A8gDistStmt := fun _ _ Fm _ W hc _ hm hr => dist_abstract_gen Fm W hc hm hr

/-! ### The headlines, conditional on the statements of the open nodes (level A) -/

theorem zeta_simple_K5_cond (hW2L : W2LStmt) (hA8g : A8gSimpleStmt) (hcert : CertAM5) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) := by
  obtain ⟨W, ha1, ha2, hnu, hW⟩ := hcert
  have hrob : RobustAM (W.a 0) (W.a 1) W.nu β := by rw [ha1, ha2, hnu]; exact robust_K5 hβ
  have hA := fun N R (Fm : FrameFamily N R (kPsi psiCos16)) => hA8g N R Fm 5 W hW β hmaj hrob
  simp only [ha1, ha2, hnu] at hA
  exact headline_simple hW2L hA num_sigma_K5

theorem zeta_distinct_K5_cond (hW2L : W2LStmt) (hA8g : A8gDistStmt) (hcert : CertAM5) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  obtain ⟨W, ha1, ha2, hnu, hW⟩ := hcert
  have hrob : RobustAM (W.a 0) (W.a 1) W.nu β := by rw [ha1, ha2, hnu]; exact robust_K5 hβ
  have hA := fun N R (Fm : FrameFamily N R (kPsi psiCos16)) => hA8g N R Fm 5 W hW β hmaj hrob
  simp only [ha1, ha2, hnu] at hA
  exact headline_dist hW2L hA num_dist_K5

theorem zeta_simple_K7_cond (hW2L : W2LStmt) (hA8g : A8gSimpleStmt) (hcert : CertAM7) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) := by
  obtain ⟨W, ha1, ha2, hnu, hW⟩ := hcert
  have hrob : RobustAM (W.a 0) (W.a 1) W.nu β := by rw [ha1, ha2, hnu]; exact robust_K7 hβ
  have hA := fun N R (Fm : FrameFamily N R (kPsi psiCos16)) => hA8g N R Fm 7 W hW β hmaj hrob
  simp only [ha1, ha2, hnu] at hA
  exact headline_simple hW2L hA num_sigma

theorem zeta_distinct_K7_cond (hW2L : W2LStmt) (hA8g : A8gDistStmt) (hcert : CertAM7) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  obtain ⟨W, ha1, ha2, hnu, hW⟩ := hcert
  have hrob : RobustAM (W.a 0) (W.a 1) W.nu β := by rw [ha1, ha2, hnu]; exact robust_K7 hβ
  have hA := fun N R (Fm : FrameFamily N R (kPsi psiCos16)) => hA8g N R Fm 7 W hW β hmaj hrob
  simp only [ha1, ha2, hnu] at hA
  exact headline_dist hW2L hA num_dist

/-! ### The headlines, conditional on W2L-cos and A7g only (A8 at the two certificates is proved in `A8K.lean`) -/

theorem zeta_simple_K5_cond7 (hW2L : W2LStmt) (hA7 : A8K.A7gStmt) (hcert : CertAM5) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  headline_simple hW2L (fun _ _ Fm => A8K.sigma_K5 hA7 Fm hcert hmaj hβ) num_sigma_K5

theorem zeta_distinct_K5_cond7 (hW2L : W2LStmt) (hA7 : A8K.A7gStmt) (hcert : CertAM5) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  headline_dist hW2L (fun _ _ Fm => A8K.dist_K5 hA7 Fm hcert hmaj hβ) num_dist_K5

theorem zeta_simple_K7_cond7 (hW2L : W2LStmt) (hA7 : A8K.A7gStmt) (hcert : CertAM7) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  headline_simple hW2L (fun _ _ Fm => A8K.sigma_K7b hA7 Fm hcert hmaj hβ) num_sigma

theorem zeta_distinct_K7_cond7 (hW2L : W2LStmt) (hA7 : A8K.A7gStmt) (hcert : CertAM7) {β : ℝ}
    (hmaj : MajorantCert psiCos16 β) (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  headline_dist hW2L (fun _ _ Fm => A8K.dist_K7b hA7 Fm hcert hmaj hβ) num_dist

/-! ### The headlines for a general majorant threshold β (the open nodes W2L-cos and A7g enter as their compiled
skeleton statements; W2L-cos is proved) -/

theorem zeta_simple_K5_of_majorant (hcert : CertAM5) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  zeta_simple_K5_cond7 w2l_holds A8K.a7g_holds hcert hmaj hβ

theorem zeta_distinct_K5_of_majorant (hcert : CertAM5) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  zeta_distinct_K5_cond7 w2l_holds A8K.a7g_holds hcert hmaj hβ

theorem zeta_simple_K7_of_majorant (hcert : CertAM7) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  zeta_simple_K7_cond7 w2l_holds A8K.a7g_holds hcert hmaj hβ

theorem zeta_distinct_K7_of_majorant (hcert : CertAM7) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  zeta_distinct_K7_cond7 w2l_holds A8K.a7g_holds hcert hmaj hβ

end Top
end ZetaS
