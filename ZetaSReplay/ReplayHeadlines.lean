/- replay: the two hypothesis-free K = 5 theorems (L1_1e). `ZetaS.Top.zeta_simple_K5_final` and
`zeta_distinct_K5_final` (library, ZetaS.Top.TopFinal) applied to `certAM5_replayed : ZetaS.CertAM5`; the statements are
those of the two headlines without the hypothesis `hcert`. -/
import ReplayAM5
import ZetaS.Top.TopFinal

namespace ZetaS
namespace Top

/-- **Simple zeros, K = 5, hypothesis-free** (thm:sigd-Sigma with the K = 5 certificate). -/
theorem zeta_simple_K5_uncond :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  zeta_simple_K5_final ZetaS.CertV2.certAM5_replayed

/-- **Distinct zeros, K = 5, hypothesis-free** (thm:sigd-D with the K = 5 certificate). -/
theorem zeta_distinct_K5_uncond :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  zeta_distinct_K5_final ZetaS.CertV2.certAM5_replayed

end Top
end ZetaS
