/-
lean_work/L3_2/top/A8K.lean — A8 (thm:sigd-Sigma/D, Steps 2–4) for the K = 5 certificate and for K = 7 with any majorant
threshold β < λ_c, PROVED from A7g (the statement `A7gStmt` = `OLL_gen`) (L3_2, 28 Sep 2026).

L2_2's proof of the skeleton A8 (`A8_SigmaDistAbstract.lean`) is constant-specific only in its call of A7 and in the
final `linarith`; its per-height frame inequality `A8b.frame_ineq_at` is already general in (c*, a₁, a₂, ν). Here:
  * `frame_step2_gen` — (FI) for any robust certificate, from `A7gStmt` (+ L5, L8 through `frame_ineq_at`);
  * `sigma_K5`, `dist_K5`, `sigma_K7b`, `dist_K7b` — L2_2's Steps 3–4, with the K = 5 (resp. K = 7) numerals.
So the K = 5 pair needs A7g, not A8g: A8g at the two certificates is proved here.
-/
import ZetaS.SigmaDist.A8_SigmaDistAbstract
-- (L0_5: the sorry-free imports of Skeleton/A8g_SigmaDistGeneral, instead of that file)
import ZetaS.Interfaces
import ZetaS.LinAlg.L7_SchurLocalisation
import ZetaS.Top.N2_Robust
import ZetaS.Top.TopDefs

open Filter Asymptotics Finset Matrix RHLinalg

namespace ZetaS
namespace A8K

open A8b A8aux

/-- The statement of the open node **A7g** (`OLL_gen`). -/
def A7gStmt : Prop := ∀ (N : ℝ → ℝ) (R : ℝ) (Fm : FrameFamily N R (kPsi psiCos16)) (K : ℕ) (W : MarkWeights K),
    LocalCertAM (kPsi psiCos16) W → ∀ β : ℝ, MajorantCert psiCos16 β → RobustAM (W.a 0) (W.a 1) W.nu β →
    ∀ hML : (∀ T, ((Fm.F T).ML).IsHermitian),
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      trFun (hML T) (kappaCh (2 - 2 * W.a 0))
        ≤ (Fm.F T).slackOn (Fm.F T).light ((Fm.F T).sEq 1)
          - W.a 0 * ((Fm.F T).sEq 1 : ℝ) - W.a 1 * ((Fm.F T).sEq 2 : ℝ) + W.nu * (Fm.F T).Λ + r T

-- `a7g_holds` (A7gStmt from the open node `OLL_gen`) is in ZetaS/Top/TopSolutionGeneral.lean (L0_5, ruling b).

/-- **(FI)** for any robust all-marks certificate, from A7g. -/
theorem frame_step2_gen (hA7 : A7gStmt) {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16)) {K : ℕ}
    (W : MarkWeights K) (hcert : LocalCertAM (kPsi psiCos16) W) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hrob : RobustAM (W.a 0) (W.a 1) W.nu β) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (W.a 0 - 1) * ((Fm.F T).sEq 1 : ℝ) + W.a 1 * ((Fm.F T).sEq 2 : ℝ)
          - W.nu * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * W.a 0) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt := by
  obtain ⟨ρ, hρ, hOLL⟩ := hA7 N R Fm K W hcert β hmaj hrob (fun T => ML_herm (Fm.F T))
  refine ⟨fun T => ρ T + 2 * (((Fm.F T).Nw : ℝ) - rtrace (Fm.F T).Gt), ?_, ?_⟩
  · have := (hρ.add (Fm.window.const_mul_left 2)).sub (Fm.trace.const_mul_left 2)
    exact this.congr_left (fun T => by ring)
  · filter_upwards [hOLL] with T hT
    have hc : (0 : ℝ) ≤ 2 - 2 * W.a 0 := hrob.cstar_pos.le
    have hc0 : kappaCh (2 - 2 * W.a 0) 0 = 0 := by
      unfold kappaCh
      have : max ((0 : ℝ) - 2) 0 = 0 := by norm_num
      rw [this]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub]
      exact max_eq_right (by linarith)
    exact frame_ineq_at (Fm.F T) _ _ _ _ _ hc hc0 hT

/-- the K = 5 instance of (FI). -/
theorem frame_step2_K5 (hA7 : A7gStmt) {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM5) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1280197 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 48749 / 3125000 * ((Fm.F T).sEq 2 : ℝ)
          - 1 / 125 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1280197 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt := by
  obtain ⟨W, ha1, ha2, hnu, hW⟩ := hcert
  have hrob : RobustAM (W.a 0) (W.a 1) W.nu β := by rw [ha1, ha2, hnu]; exact robust_K5 hβ
  have h := frame_step2_gen hA7 Fm W hW hmaj hrob
  rwa [ha1, ha2, hnu] at h

/-- the K = 7 instance of (FI), any `β < λ_c`. -/
theorem frame_step2_K7 (hA7 : A7gStmt) {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM7) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1824837 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 1168069 / (5 * 10 ^ 7) * ((Fm.F T).sEq 2 : ℝ)
          - 3 / 250 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1824837 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt := by
  obtain ⟨W, ha1, ha2, hnu, hW⟩ := hcert
  have hrob : RobustAM (W.a 0) (W.a 1) W.nu β := by rw [ha1, ha2, hnu]; exact robust_K7 hβ
  have h := frame_step2_gen hA7 Fm W hW hmaj hrob
  rwa [ha1, ha2, hnu] at h

/-! ### Steps 3–4 (L2_2's proof, with the K = 5 numerals) -/

/-- Steps 3–4 for K = 5 from the frame inequality (FI) at the K = 5 constants. -/
theorem sigma_K5_of_FI {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hFI0 : ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1280197 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 48749 / 3125000 * ((Fm.F T).sEq 2 : ℝ)
          - 1 / 125 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1280197 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) - ε) * N T
        ≤ ((Fm.F T).NsW : ℝ) := by
  obtain ⟨r, hr, hFI⟩ := hFI0
  obtain ⟨r', hr', hspan⟩ := Fm.span
  let e : ℝ → ℝ := fun T => -((48749 / 3125000 : ℝ) / 2 * (((Fm.F T).Nw : ℝ) - N T)
      + 2 * (RHLinalg.rtrace (Fm.F T).Gt - N T)
      - (RHLinalg.frobSq (Fm.F T).Gt - R * N T) - r T - (1 / 125 : ℝ) * r' T)
  have he : e =o[atTop] N := by
    have := (((((Fm.window.const_mul_left ((48749 / 3125000 : ℝ) / 2)).add
      (Fm.trace.const_mul_left 2)).sub Fm.frob).sub hr).sub (hr'.const_mul_left (1 / 125 : ℝ))).neg_left
    exact this.congr_left (fun T => rfl)
  have hD : (0 : ℝ) < 1 - 1280197 / 10 ^ 8 + 48749 / 3125000 / 2 := by norm_num
  have hmain := eps_form (X := fun T => ((Fm.F T).NsW : ℝ))
    (c0 := (2 - R) + 48749 / 3125000 / 2 - 1 / 125) Fm.N_nonneg hD he (by
    filter_upwards [hFI, hspan] with T hT hsp
    have c3 := NH_ge (Fm.F T); have c4 := Noff_ge' (Fm.F T); have c5 := Nw_eq (Fm.F T)
    have hp1 : ((Fm.F T).p1 : ℝ) ≤ (Fm.F T).p := by exact_mod_cast (Fm.F T).p1_le
    have hX : ((Fm.F T).NsW : ℝ) = (Fm.F T).sEq 1 + 2 * (Fm.F T).p1 := by
      unfold ZeroFrame.NsW; push_cast; ring
    have hsH : (0 : ℝ) ≤ (Fm.F T).sH := Nat.cast_nonneg _
    simp only [e]
    rw [hX]
    linarith)
  intro ε hε
  obtain ⟨T₀, h⟩ := hmain ε hε
  exact ⟨T₀, fun T hT => by unfold sigmaConst; exact h T hT⟩


theorem sigma_K5 (hA7 : A7gStmt) {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM5) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) - ε) * N T
        ≤ ((Fm.F T).NsW : ℝ) :=
  sigma_K5_of_FI Fm (frame_step2_K5 hA7 Fm hcert hmaj hβ)

/-- Steps 3–4 for K = 5 from the frame inequality (FI) at the K = 5 constants. -/
theorem dist_K5_of_FI {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hFI0 : ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1280197 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 48749 / 3125000 * ((Fm.F T).sEq 2 : ℝ)
          - 1 / 125 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1280197 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) - ε) * N T
        ≤ ((Fm.F T).NdW : ℝ) := by
  obtain ⟨r, hr, hFI⟩ := hFI0
  obtain ⟨r', hr', hspan⟩ := Fm.span
  let e : ℝ → ℝ := fun T => -((1 + 48749 / 3125000 - 1280197 / 10 ^ 8 : ℝ) * (((Fm.F T).Nw : ℝ) - N T)
      + 2 * (RHLinalg.rtrace (Fm.F T).Gt - N T)
      - (RHLinalg.frobSq (Fm.F T).Gt - R * N T) - r T - (1 / 125 : ℝ) * r' T)
  have he : e =o[atTop] N := by
    have := (((((Fm.window.const_mul_left (1 + 48749 / 3125000 - 1280197 / 10 ^ 8 : ℝ)).add
      (Fm.trace.const_mul_left 2)).sub Fm.frob).sub hr).sub (hr'.const_mul_left (1 / 125 : ℝ))).neg_left
    exact this.congr_left (fun T => rfl)
  have hD : (0 : ℝ) < 2 - 2 * (1280197 / 10 ^ 8) + 48749 / 3125000 := by norm_num
  have hmain := eps_form (X := fun T => ((Fm.F T).NdW : ℝ))
    (c0 := 1 + (2 - R) + 48749 / 3125000 - 1280197 / 10 ^ 8 - 1 / 125) Fm.N_nonneg hD he (by
    filter_upwards [hFI, hspan] with T hT hsp
    have c1 := n_eq (Fm.F T); have c3 := NH_ge (Fm.F T); have c4 := Noff_ge' (Fm.F T)
    have c5 := Nw_eq (Fm.F T)
    have hp1 : ((Fm.F T).p1 : ℝ) ≤ (Fm.F T).p := by exact_mod_cast (Fm.F T).p1_le
    have hX : ((Fm.F T).NdW : ℝ) = (Fm.F T).n + 2 * (Fm.F T).p := by
      unfold ZeroFrame.NdW; push_cast; ring
    have hsH : (0 : ℝ) ≤ (Fm.F T).sH := Nat.cast_nonneg _
    simp only [e]
    rw [hX]
    linarith)
  intro ε hε
  obtain ⟨T₀, h⟩ := hmain ε hε
  exact ⟨T₀, fun T hT => by unfold distConst; exact h T hT⟩


theorem dist_K5 (hA7 : A7gStmt) {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM5) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) - ε) * N T
        ≤ ((Fm.F T).NdW : ℝ) :=
  dist_K5_of_FI Fm (frame_step2_K5 hA7 Fm hcert hmaj hβ)

/-! ### Steps 3–4 with the K = 7 numerals, any `β < λ_c` -/

/-- Steps 3–4 for K = 7 from the frame inequality (FI) at the K = 7 constants. -/
theorem sigma_K7b_of_FI {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hFI0 : ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1824837 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 1168069 / (5 * 10 ^ 7) * ((Fm.F T).sEq 2 : ℝ)
          - 3 / 250 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1824837 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NsW : ℝ) := by
  obtain ⟨r, hr, hFI⟩ := hFI0
  obtain ⟨r', hr', hspan⟩ := Fm.span
  let e : ℝ → ℝ := fun T => -((1168069 / (5 * 10 ^ 7) : ℝ) / 2 * (((Fm.F T).Nw : ℝ) - N T)
      + 2 * (RHLinalg.rtrace (Fm.F T).Gt - N T)
      - (RHLinalg.frobSq (Fm.F T).Gt - R * N T) - r T - (3 / 250 : ℝ) * r' T)
  have he : e =o[atTop] N := by
    have := (((((Fm.window.const_mul_left ((1168069 / (5 * 10 ^ 7) : ℝ) / 2)).add
      (Fm.trace.const_mul_left 2)).sub Fm.frob).sub hr).sub (hr'.const_mul_left (3 / 250 : ℝ))).neg_left
    exact this.congr_left (fun T => rfl)
  have hD : (0 : ℝ) < 1 - 1824837 / 10 ^ 8 + 1168069 / (5 * 10 ^ 7) / 2 := by norm_num
  have hmain := eps_form (X := fun T => ((Fm.F T).NsW : ℝ))
    (c0 := (2 - R) + 1168069 / (5 * 10 ^ 7) / 2 - 3 / 250) Fm.N_nonneg hD he (by
    filter_upwards [hFI, hspan] with T hT hsp
    have c3 := NH_ge (Fm.F T); have c4 := Noff_ge' (Fm.F T); have c5 := Nw_eq (Fm.F T)
    have hp1 : ((Fm.F T).p1 : ℝ) ≤ (Fm.F T).p := by exact_mod_cast (Fm.F T).p1_le
    have hX : ((Fm.F T).NsW : ℝ) = (Fm.F T).sEq 1 + 2 * (Fm.F T).p1 := by
      unfold ZeroFrame.NsW; push_cast; ring
    have hsH : (0 : ℝ) ≤ (Fm.F T).sH := Nat.cast_nonneg _
    simp only [e]
    rw [hX]
    linarith)
  intro ε hε
  obtain ⟨T₀, h⟩ := hmain ε hε
  exact ⟨T₀, fun T hT => by unfold sigmaConst; exact h T hT⟩


theorem sigma_K7b (hA7 : A7gStmt) {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM7) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NsW : ℝ) :=
  sigma_K7b_of_FI Fm (frame_step2_K7 hA7 Fm hcert hmaj hβ)

/-- Steps 3–4 for K = 7 from the frame inequality (FI) at the K = 7 constants. -/
theorem dist_K7b_of_FI {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hFI0 : ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1824837 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 1168069 / (5 * 10 ^ 7) * ((Fm.F T).sEq 2 : ℝ)
          - 3 / 250 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1824837 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NdW : ℝ) := by
  obtain ⟨r, hr, hFI⟩ := hFI0
  obtain ⟨r', hr', hspan⟩ := Fm.span
  let e : ℝ → ℝ := fun T => -((1 + 1168069 / (5 * 10 ^ 7) - 1824837 / 10 ^ 8 : ℝ) * (((Fm.F T).Nw : ℝ) - N T)
      + 2 * (RHLinalg.rtrace (Fm.F T).Gt - N T)
      - (RHLinalg.frobSq (Fm.F T).Gt - R * N T) - r T - (3 / 250 : ℝ) * r' T)
  have he : e =o[atTop] N := by
    have := (((((Fm.window.const_mul_left (1 + 1168069 / (5 * 10 ^ 7) - 1824837 / 10 ^ 8 : ℝ)).add
      (Fm.trace.const_mul_left 2)).sub Fm.frob).sub hr).sub (hr'.const_mul_left (3 / 250 : ℝ))).neg_left
    exact this.congr_left (fun T => rfl)
  have hD : (0 : ℝ) < 2 - 2 * (1824837 / 10 ^ 8) + 1168069 / (5 * 10 ^ 7) := by norm_num
  have hmain := eps_form (X := fun T => ((Fm.F T).NdW : ℝ))
    (c0 := 1 + (2 - R) + 1168069 / (5 * 10 ^ 7) - 1824837 / 10 ^ 8 - 3 / 250) Fm.N_nonneg hD he (by
    filter_upwards [hFI, hspan] with T hT hsp
    have c1 := n_eq (Fm.F T); have c3 := NH_ge (Fm.F T); have c4 := Noff_ge' (Fm.F T)
    have c5 := Nw_eq (Fm.F T)
    have hp1 : ((Fm.F T).p1 : ℝ) ≤ (Fm.F T).p := by exact_mod_cast (Fm.F T).p1_le
    have hX : ((Fm.F T).NdW : ℝ) = (Fm.F T).n + 2 * (Fm.F T).p := by
      unfold ZeroFrame.NdW; push_cast; ring
    have hsH : (0 : ℝ) ≤ (Fm.F T).sH := Nat.cast_nonneg _
    simp only [e]
    rw [hX]
    linarith)
  intro ε hε
  obtain ⟨T₀, h⟩ := hmain ε hε
  exact ⟨T₀, fun T hT => by unfold distConst; exact h T hT⟩


theorem dist_K7b (hA7 : A7gStmt) {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM7) {β : ℝ} (hmaj : MajorantCert psiCos16 β)
    (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NdW : ℝ) :=
  dist_K7b_of_FI Fm (frame_step2_K7 hA7 Fm hcert hmaj hβ)

end A8K
end ZetaS
