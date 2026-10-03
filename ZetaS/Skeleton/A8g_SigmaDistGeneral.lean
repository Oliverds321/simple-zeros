/-
Nodes A7g, A8g (NEW statements, L3_2, 28 Sep 2026) — thm:sigd-OLL and thm:sigd-Sigma/D for ANY all-marks certificate
(K; γ, μ, b) of k_ψ, ψ = cos 1.6s, with claims (a₁, a₂, ν) = (W.a 0, W.a 1, W.nu), and any majorant threshold β, under the
robustness conditions of rem:sigd-robust (`RobustAM`, node N2).

Why: the skeleton A7 (`OLL`) and A8 (`sigma_abstract`, `dist_abstract`) hard-code the K = 7 constants and the
architect's `CertMaj` threshold 3.2063638853, so they cannot give the lead's first hypothesis-free pair (K = 5).
The draft says (l.1069, rem:sigd-cert "Transfer"): "Nothing below depends on K except through o(N) terms and
through (a₁,a₂,ν)". These statements say exactly that. `sigma_abstract_of_gen`/`dist_abstract_of_gen` below
PROVE the skeleton A8 from A8g + N2 (`robust_K7`), so replacing A8 by A8g loses nothing.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L7_SchurLocalisation
import ZetaS.Top.N2_Robust

open Filter Asymptotics Finset

namespace ZetaS

/-- **A7g** — (OL_L) for any all-marks certificate with robust claims. -/
theorem OLL_gen {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) {K : ℕ} (W : MarkWeights K)
    (hcert : LocalCertAM (kPsi psiCos16) W) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hrob : RobustAM (W.a 0) (W.a 1) W.nu β) (hML : ∀ T, ((Fm.F T).ML).IsHermitian) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      trFun (hML T) (kappaCh (2 - 2 * W.a 0))
        ≤ (Fm.F T).slackOn (Fm.F T).light ((Fm.F T).sEq 1)
          - W.a 0 * ((Fm.F T).sEq 1 : ℝ) - W.a 1 * ((Fm.F T).sEq 2 : ℝ) + W.nu * (Fm.F T).Λ + r T := by
  sorry

/-- **A8g, simple zeros** — thm:sigd-Sigma for any robust all-marks certificate. -/
theorem sigma_abstract_gen {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) {K : ℕ}
    (W : MarkWeights K) (hcert : LocalCertAM (kPsi psiCos16) W) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hrob : RobustAM (W.a 0) (W.a 1) W.nu β) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (W.a 0) (W.a 1) W.nu - ε) * N T ≤ ((Fm.F T).NsW : ℝ) := by
  sorry

/-- **A8g, distinct zeros** — thm:sigd-D for any robust all-marks certificate. -/
theorem dist_abstract_gen {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) {K : ℕ}
    (W : MarkWeights K) (hcert : LocalCertAM (kPsi psiCos16) W) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hrob : RobustAM (W.a 0) (W.a 1) W.nu β) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (W.a 0) (W.a 1) W.nu - ε) * N T ≤ ((Fm.F T).NdW : ℝ) := by
  sorry

/-- consistency: the skeleton A8 (K = 7, `CertMaj`) is an instance of A8g + N2. -/
theorem sigma_abstract_of_gen {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM7) (hmaj : CertMaj) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NsW : ℝ) := by
  obtain ⟨W, ha1, ha2, hnu, hW⟩ := hcert
  have h := sigma_abstract_gen Fm W hW hmaj (by rw [ha1, ha2, hnu]; exact robust_K7 certMaj_lt_K7)
  rwa [ha1, ha2, hnu] at h

theorem dist_abstract_of_gen {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM7) (hmaj : CertMaj) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NdW : ℝ) := by
  obtain ⟨W, ha1, ha2, hnu, hW⟩ := hcert
  have h := dist_abstract_gen Fm W hW hmaj (by rw [ha1, ha2, hnu]; exact robust_K7 certMaj_lt_K7)
  rwa [ha1, ha2, hnu] at h

end ZetaS
