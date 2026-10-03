/-
ZetaS/Majorant/CertMajProof.lean — the architect's `CertMaj` (threshold 3.2063638853) as a THEOREM (L9_1, 28 Sep 2026).
Proposed library file (L9_1, for the integrator): checked against the green tree (e34f5b9), where
`ZetaS.MajSound.certMajV2_proved : CertMajV2` is level A. Same witness B = `MCert.Bmaj`; only the final rational
inequality changes: 2β₀ + 4|β₅₂| = 3.2063638852430… < 3.2063638853 (margin 5.69·10⁻¹¹, exact rationals).
-/
import ZetaS.Majorant.CertMajV2Proof

open Real MeasureTheory Set

namespace ZetaS

/-- The architect's `CertMaj` (threshold 3.2063638853) from the two numerical cell nodes that `CertMajV2` uses
(L2_2's proof of `certMajV2_of_nodes`, with the final rational inequality at the tighter threshold). -/
theorem MajSound.certMaj_of_NPos_NMaj2 (hpos : MCert.NPos) (h2 : MCert.NMaj2) : CertMaj := by
  have hFP := MCert.fp_holds
  have hmaj := MCert.NMaj_of_NMaj2 hpos h2
  refine ⟨MCert.Bmaj, MCert.Bmaj_integrable, MCert.Bmaj_neg, ?_, ?_, ?_, |MCert.beta 52|, ?_, ?_⟩
  · intro s
    unfold MCert.Bmaj
    exact mul_nonneg (by positivity) (MCert.Pmaj_nonneg hpos s)
  · intro s hs
    rw [MCert.integral_psiCos16]
    unfold psiCos16
    rcases le_total 0 s with h0 | h0
    · exact hmaj s ⟨h0, hs.2⟩
    · have := hmaj (-s) ⟨by linarith, by linarith [hs.1]⟩
      rwa [MCert.Bmaj_neg, show 8 / 5 * -s = -(8 / 5 * s) by ring, Real.cos_neg] at this
  · intro t ht
    rw [MCert.Bmaj_transform hFP]
    exact MCert.BhatPL_zero_of_one_le ht
  · intro t ht
    rw [MCert.Bmaj_transform hFP]
    exact MCert.BhatPL_bound ht
  · have hint : ∫ s, MCert.Bmaj s = MCert.beta 0 := by
      have := MCert.Bmaj_transform hFP 0
      simp only [mul_zero, zero_mul, Real.cos_zero, mul_one] at this
      rw [this, MCert.BhatPL_at_zero]
    rw [hint]
    unfold MCert.beta
    simp only [MCert.betaQ]
    norm_num [abs_div]

/-- **`CertMaj` holds** (level A, given L5_1's proved C-nodes, exactly as `certMajV2_proved`). -/
theorem MajSound.certMaj_proved : CertMaj :=
  MajSound.certMaj_of_NPos_NMaj2 MajSound.npos_proved (MajSound.nmaj2_of_CNodes MajSound.cnodes_of_statements)

end ZetaS

#print axioms ZetaS.MajSound.certMaj_proved
