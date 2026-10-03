/-
Node F1c-chain (L7_10's statement, VERBATIM; proof by L7_3, round 4, 28 Sep 2026). Drop-in replacement for
`lean_work/L7_10/L10_F1cChain.lean`: same module name, same namespace, same theorem statement (checked by `diff` of the
statement block against `orig/L10_F1cChain.lean`); only the imports and the proof are new.

Original docstring (L7_10): **everything F1c needs besides Theorem K** (thm:shell-1pp's proof in the frame vocabulary):
for a Shell design (S53-L75, `λ = 191/100`, `α′ = 2497/1500`), IF the out-zone of the family functional obeys
Theorem K's bound with some constant `c₀`, THEN the Frobenius row is at the certified Shell constant:
`‖Ĝ_fam‖²_F ≤ (2 − 0.9059137927 + c(log Q)^{−θ})·𝒩`.

PROOF (L7_3). DERIVED from the sub-nodes F1c-1 … F1c-11 (files `LF_*.lean`):
  PP ≤ inCrossRHS(e) + 2∫_{out} g·F                                   F1c-1 `shell_master` (proved)
     ≤ W(K0a(a) + η)𝒩 + (1 + c₀ρ)·2|𝔉|·outShell                     F1c-2 `shell_inzone`; Theorem K (the hypothesis)
     ≤ W(K0a(a) + η)𝒩 + (1 + c₀ρ)·W(KoutShell(a) + η)𝒩               F1c-3 `shell_outDiag`
  frobSq ≤ (ψ_d(0) + Y + η)𝒩,  Y = K0a + η + (1 + c₀ρ)(KoutShell + η)  F1c-4 `shell_assembly`
  ψ_d(0) + K0a + KoutShell = B_{α′}(v_d) + (C−1)Jzone(a)              F1c-5 `kernel_split` (proved)
  B_{α′}(v_d) ≤ c²·B_{α′}(v_p),  v_p = S53L75.v                        F1c-6, F1c-7 (proved)
  B_{α′}(v_p) ≤ 2 − P_cert − δ₀                                       F1c-8 `cert_strict`
  (C−1)Jzone(a) ≤ η,  c² ≤ 1 + η,  c₀ρ ≤ η                             F1c-9 `zone_small`, F1c-10, F1c-11 (proved)
so with `η = min(δ₀/20, 1/100)` the coefficient is `≤ 2 − P_cert − δ₀ + 9η ≤ 2 − P_cert`, and the conclusion holds
with `c = 1` (the rate term is `≥ 0`). `W = (aL)²`, `ρ = (log Q)^{−θ}`, `a = zoneFactor P`, `v_d = vDesign P`.
-/
import ZetaShell.ShellK.L10_KDefs
import ZetaShell.ShellK.LF_1_Master
import ZetaShell.ShellK.LF_OutFinal
import ZetaShell.ShellK.LF_InZone
import ZetaShell.ShellK.LF_Assembly
import ZetaShell.ShellK.LF_Small

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ

theorem F1c_chain (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) (c₀ : ℝ)
    (hc₀ : 0 ≤ c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (∫ s in (inZone P)ᶜ, P.gQ s * FfamZ P Qn s)
          ≤ (1 + c₀ * Real.log Qn ^ (-θ)) * Family.qle.sizeR Qn
              * (∫ s in (inZone P)ᶜ, P.gQ s * (normA2 P s * shellWt P (2497 / 1500) s)) →
      frobSqGhatFam P Family.qle Qn
        ≤ (2 - ((PcertS53 : ℚ) : ℝ) + c * shellRate θ Qn) * NfamQ P Family.qle Qn := by
  obtain ⟨δ₀, hδ₀, hcert⟩ := F1c.cert_strict
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (δ₀ / 20) (1 / 100) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min (by linarith) (by norm_num)
  have hηδ : η ≤ δ₀ / 20 := by rw [hηdef]; exact min_le_left _ _
  have hη1 : η ≤ 1 / 100 := by rw [hηdef]; exact min_le_right _ _
  obtain ⟨e, he, hin⟩ := F1c.shell_inzone r ε hr hε η hη
  have hc₀1 : 0 < c₀ + 1 := by linarith
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [F1c.shell_master r ε hr hε, hin, F1c.shell_outDiag r ε hr hε η hη,
    F1c.shell_assembly r ε hr hε η hη, F1c.zone_small r ε hr hε η hη, F1c.ramp_small r ε hr η hη,
    F1c.rate_small θ hθ (η / (c₀ + 1)) (div_pos hη hc₀1)] with Qn hM hI hO hA hZ hR hρ
  intro P hdes hK
  have hP : P.Valid := hdes.1
  have hN0 : 0 ≤ NfamQ P Family.qle Qn := NfamQ_nonneg P Family.qle Qn
  have hW0 : 0 ≤ (P.aQ * P.LB) ^ 2 := sq_nonneg _
  obtain ⟨hρ0, hρη⟩ := hρ
  have hc₀ρ0 : 0 ≤ c₀ * Real.log (Qn : ℝ) ^ (-θ) := mul_nonneg hc₀ hρ0
  have hc₀ρ : c₀ * Real.log (Qn : ℝ) ^ (-θ) ≤ η := by
    have h1 : c₀ * Real.log (Qn : ℝ) ^ (-θ) ≤ c₀ * (η / (c₀ + 1)) := mul_le_mul_of_nonneg_left hρη hc₀
    have h2 : c₀ * (η / (c₀ + 1)) ≤ η := by
      rw [mul_div_assoc', div_le_iff₀ hc₀1]
      nlinarith
    linarith
  -- Theorem K, then F1c-3
  have hK1 : (∫ s in (inZone P)ᶜ, P.gQ s * FfamZ P Qn s)
      ≤ (1 + c₀ * Real.log (Qn : ℝ) ^ (-θ)) * (Family.qle.sizeR Qn * F1c.outShell P) := by
    have e1 : (1 + c₀ * Real.log (Qn : ℝ) ^ (-θ)) * (Family.qle.sizeR Qn * F1c.outShell P)
        = (1 + c₀ * Real.log (Qn : ℝ) ^ (-θ)) * Family.qle.sizeR Qn * F1c.outShell P := by ring
    rw [e1]
    exact hK
  have hO' := mul_le_mul_of_nonneg_left (hO P hdes) (by linarith : (0 : ℝ) ≤ 1 + c₀ * Real.log (Qn : ℝ) ^ (-θ))
  have hout : 2 * (∫ s in (inZone P)ᶜ, P.gQ s * FfamZ P Qn s)
      ≤ (1 + c₀ * Real.log (Qn : ℝ) ^ (-θ))
          * ((P.aQ * P.LB) ^ 2 * (F1c.KoutShell Cfam (2497 / 1500) (zoneFactor P) (Payoff.vDesign P) + η)
            * NfamQ P Family.qle Qn) := by
    linarith
  -- the PP block in the form `W·Y·𝒩`
  have hPP : familySum Family.qle Qn (fun _ χ => Mform P (Zones.PXchi P χ) (Zones.PXchi P χ))
      ≤ (P.aQ * P.LB) ^ 2
          * (FrobAssembly.K0a (zoneFactor P) (Payoff.vDesign P) + η
            + (1 + c₀ * Real.log (Qn : ℝ) ^ (-θ))
              * (F1c.KoutShell Cfam (2497 / 1500) (zoneFactor P) (Payoff.vDesign P) + η))
          * NfamQ P Family.qle Qn := by
    have h1 := hM P hdes e he
    have h2 := hI P hdes
    have e2 : (P.aQ * P.LB) ^ 2
          * (FrobAssembly.K0a (zoneFactor P) (Payoff.vDesign P) + η
            + (1 + c₀ * Real.log (Qn : ℝ) ^ (-θ))
              * (F1c.KoutShell Cfam (2497 / 1500) (zoneFactor P) (Payoff.vDesign P) + η))
          * NfamQ P Family.qle Qn
        = (P.aQ * P.LB) ^ 2 * (FrobAssembly.K0a (zoneFactor P) (Payoff.vDesign P) + η) * NfamQ P Family.qle Qn
          + (1 + c₀ * Real.log (Qn : ℝ) ^ (-θ))
            * ((P.aQ * P.LB) ^ 2 * (F1c.KoutShell Cfam (2497 / 1500) (zoneFactor P) (Payoff.vDesign P) + η)
              * NfamQ P Family.qle Qn) := by ring
    rw [e2]
    linarith
  have hfrob := hA P hdes _ hPP
  -- the coefficient
  have hadm := Payoff.vDesign_admissible hP
  obtain ⟨ha0, ha1, hz⟩ := hZ P hdes
  have hsplit := F1c.kernel_split hadm Cfam (2497 / 1500) (zoneFactor P) (by norm_num) ha0 ha1
  have hCfam0 : (0 : ℝ) ≤ Cfam := by unfold Cfam; positivity
  have hramp := F1c.Bshell_vDesign_le hP hCfam0 (2497 / 1500)
  rw [F1c.vProfile_S53 hdes] at hramp
  obtain ⟨hc1, hc2⟩ := hR P hdes
  have hcsq1 : 1 ≤ F1c.cRampS P ^ 2 := by nlinarith
  have hPc0 : (0 : ℝ) ≤ ((PcertS53 : ℚ) : ℝ) := by norm_num [PcertS53]
  have hψ0 : 0 ≤ Payoff.psi (Payoff.vDesign P) 0 := Payoff.psi_nonneg hadm 0
  have hK0a0 : 0 ≤ FrobAssembly.K0a (zoneFactor P) (Payoff.vDesign P) := by
    unfold FrobAssembly.K0a
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun α _ => mul_nonneg (abs_nonneg α) (Payoff.psi_nonneg hadm α))
  -- `B_{α′}(v_d) ≤ X + 2η`, `X = 2 − P_cert − δ₀`
  have hBd : Bshell 1 (2497 / 1500) Cfam (Payoff.vDesign P) ≤ (2 - ((PcertS53 : ℚ) : ℝ) - δ₀) + 2 * η := by
    have h1 := mul_le_mul_of_nonneg_left hcert (sq_nonneg (F1c.cRampS P))
    have h2 := mul_nonneg (sub_nonneg.mpr hcsq1)
      (sub_nonneg.mpr (show 2 - ((PcertS53 : ℚ) : ℝ) - δ₀ ≤ 2 by linarith))
    linarith
  have hKout : F1c.KoutShell Cfam (2497 / 1500) (zoneFactor P) (Payoff.vDesign P) + η ≤ 3 := by linarith
  have hprod : c₀ * Real.log (Qn : ℝ) ^ (-θ)
      * (F1c.KoutShell Cfam (2497 / 1500) (zoneFactor P) (Payoff.vDesign P) + η) ≤ 3 * η := by
    have := mul_le_mul_of_nonneg_left hKout hc₀ρ0
    linarith
  have hcoef : Payoff.psi (Payoff.vDesign P) 0
        + (FrobAssembly.K0a (zoneFactor P) (Payoff.vDesign P) + η
          + (1 + c₀ * Real.log (Qn : ℝ) ^ (-θ))
            * (F1c.KoutShell Cfam (2497 / 1500) (zoneFactor P) (Payoff.vDesign P) + η)) + η
      ≤ 2 - ((PcertS53 : ℚ) : ℝ) + 1 * shellRate θ Qn := by
    have hr0 : 0 ≤ shellRate θ Qn := hρ0
    linarith
  exact le_trans hfrob (mul_le_mul_of_nonneg_right hcoef hN0)

end ShellK
end ZetaShell
