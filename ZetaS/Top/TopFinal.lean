/-
Certificate-only headline theorems (L0_1, 28 Sep 2026, lead's note of 11:06): the K = 5 and K = 7 pairs of
`ZetaS.Top.TopSolution` with the majorant hypothesis discharged by `certMajV2_proved` (track M-cert, L5_2). Their only
hypothesis is the class certificate `CertAM5` resp. `CertAM7`.
-/
import ZetaS.Top.TopSolution
import ZetaS.Majorant.CertMajV2Proof

namespace ZetaS
namespace Top

/-- `zeta_simple_K5_V2` with the majorant certificate proved (`MajSound.certMajV2_proved`). -/
theorem zeta_simple_K5_final (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  zeta_simple_K5_V2 hcert MajSound.certMajV2_proved

/-- `zeta_distinct_K5_V2` with the majorant certificate proved (`MajSound.certMajV2_proved`). -/
theorem zeta_distinct_K5_final (hcert : CertAM5) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  zeta_distinct_K5_V2 hcert MajSound.certMajV2_proved

/-- `zeta_simple_K7_V2` with the majorant certificate proved (`MajSound.certMajV2_proved`). -/
theorem zeta_simple_K7_final (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  zeta_simple_K7_V2 hcert MajSound.certMajV2_proved

/-- `zeta_distinct_K7_V2` with the majorant certificate proved (`MajSound.certMajV2_proved`). -/
theorem zeta_distinct_K7_final (hcert : CertAM7) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  zeta_distinct_K7_V2 hcert MajSound.certMajV2_proved

end Top
end ZetaS
