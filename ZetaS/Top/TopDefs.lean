/-
lean_work/L3_2/top/TopDefs.lean — the one new definition of the top-level statements (L3_2, 28 Sep 2026).
Mathlib-only layer: imports only `ChallengeZetaS` (hence `ChallengeDeps`).

`CertAM5` — the K = 5 all-marks certificate (X2, thm:zeta-allmarks, rem:sigd-cert K = 5 row), stated exactly as the
architect's `CertAM7` with the K = 5 constants; the same text as L1_1's `ZetaS.CertV2.CertAM5`
(lean_work/L1_1/CertSpecAM5.lean l.108), which the certificate track proves from 20 checked class certificates.
-/
import ZetaS.ChallengeZetaS

namespace ZetaS

/-- **Certificate AM5**: all-marks data with `a₁ = 1280197/10⁸`, `a₂ = 48749/3125000`, `ν = 1/125` for which (LI_m)
holds for `k_ψ`, `ψ = cos 1.6s` (X2's `round1/X2_numerics/xpat_K5_*.json`, `claims_d15e6_a1.6_K5_mu500.json`). -/
def CertAM5 : Prop :=
  ∃ W : MarkWeights 5, W.a 0 = 1280197 / 10 ^ 8 ∧ W.a 1 = 48749 / 3125000 ∧ W.nu = 1 / 125 ∧
    LocalCertAM (kPsi psiCos16) W

end ZetaS
