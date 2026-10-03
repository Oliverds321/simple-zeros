/-
CertMajV2 (L2_2, 28 Sep 2026) — the majorant certificate of lem:sigd-env restated with the round threshold 33/10
(lead's ruling of 28 Sep; any threshold < λ_c = 2 + √(2 − 2a₁) = 3.40125… serves A5/A7), and its reduction to the
M-cert nodes of `MCert_Majorant.lean`:

  certMajV2_of_nodes : MCert.FP → MCert.NPos → MCert.NMaj → CertMajV2
  certMajV2_of_numerics : MCert.NPos → MCert.NMaj → CertMajV2      (FP is proved: `MCert.fp_holds`, FP_FourierPair.lean)
  certMajV2_of_NPos_NMaj2 : MCert.NPos → MCert.NMaj2 → CertMajV2    (NMaj2: sinc replaced by σ, MCert_Cells.lean)

with the explicit witness B = `MCert.Bmaj` (the d7_6 majorant built from majorant_delta1_beta.npy, sha256 fd909f79…)
and β* = |β₅₂|.
-/
import ZetaS.Interfaces
import ZetaS.Majorant.MCert_Majorant
import ZetaS.Majorant.FP_FourierPair
import ZetaS.Majorant.MCert_Cells

open Real MeasureTheory Set

namespace ZetaS

/-- **CertMajV2** — `MajorantCert psiCos16 (33/10)`. -/
def CertMajV2 : Prop := MajorantCert psiCos16 (33 / 10)

theorem certMajV2_of_nodes (hFP : MCert.FP) (hpos : MCert.NPos) (hmaj : MCert.NMaj) : CertMajV2 := by
  refine ⟨MCert.Bmaj, MCert.Bmaj_integrable, MCert.Bmaj_neg, ?_, ?_, ?_, |MCert.beta 52|, ?_, ?_⟩
  · -- B ≥ 0
    intro s
    unfold MCert.Bmaj
    exact mul_nonneg (by positivity) (MCert.Pmaj_nonneg hpos s)
  · -- B ≥ v_ψ on [−1/2, 1/2]
    intro s hs
    rw [MCert.integral_psiCos16]
    unfold psiCos16
    rcases le_total 0 s with h0 | h0
    · exact hmaj s ⟨h0, hs.2⟩
    · have := hmaj (-s) ⟨by linarith, by linarith [hs.1]⟩
      rwa [MCert.Bmaj_neg, show 8 / 5 * -s = -(8 / 5 * s) by ring, Real.cos_neg] at this
  · -- band limitation
    intro t ht
    rw [MCert.Bmaj_transform hFP]
    exact MCert.BhatPL_zero_of_one_le ht
  · -- sup on [3/4, 1]
    intro t ht
    rw [MCert.Bmaj_transform hFP]
    exact MCert.BhatPL_bound ht
  · -- the rational inequality
    have hint : ∫ s, MCert.Bmaj s = MCert.beta 0 := by
      have := MCert.Bmaj_transform hFP 0
      simp only [mul_zero, zero_mul, Real.cos_zero, mul_one] at this
      rw [this, MCert.BhatPL_at_zero]
    rw [hint]
    exact MCert.final_rational

/-- **CertMajV2 from the two numerical nodes alone** (the Fourier pair is proved, `MCert.fp_holds`). -/
theorem certMajV2_of_numerics (hpos : MCert.NPos) (hmaj : MCert.NMaj) : CertMajV2 :=
  certMajV2_of_nodes MCert.fp_holds hpos hmaj

/-- **CertMajV2 from NPos and the sinc-free NMaj2** (both cell certificates; NPos also has the cell reduction
`MCert.NPos_of_cells`). -/
theorem certMajV2_of_NPos_NMaj2 (hpos : MCert.NPos) (h2 : MCert.NMaj2) : CertMajV2 :=
  certMajV2_of_numerics hpos (MCert.NMaj_of_NMaj2 hpos h2)

end ZetaS
