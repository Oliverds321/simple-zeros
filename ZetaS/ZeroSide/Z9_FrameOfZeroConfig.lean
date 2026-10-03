/-
Node Z9 (track W → K, assembly; replaces the analytic content of v1's W2) — at every bandwidth λ = P.lam < 1, an abstract
zero configuration with the paper's inputs yields a FrameFamilyL against N(T,2T) with R = R_λ(ψ) and kernel k_ψ, and the
window counts are the configuration's counts up to o(N):
  Nˢ(I′) ≤ Ns + o(N), N^d(I′) ≤ Nd + o(N), N^sc(I′) ≤ N0 + Ns − N0s + o(N).
Hypotheses are the tree's (L0_2b M2): ψ even, continuous, 0 ≤ ψ ≤ 1 on the core, admissibility of `P.phiV ψ T` at every
8w ≤ L, ∫ψ > 1/2, ∫ψ² > 1/2.
Deps: Z1–Z8, R1, K0-type bookkeeping, W9.4/W9.8 of L0_2b (two-sided tr/Frobenius in o(N) form: `trace`, `frob` with
R_λ; `window` from RvM + `Tail.eventually_NII_le`), lem:sigd-residue (v) (`span_lam`: Λ = |I′|L/2π = λN + o(N)).
-/
import ZetaS.InterfacesV2
import Zeta23.Hypotheses
import ZetaS.ZeroSide.Z9_FrameOfZeroConfig_fix

open Filter Asymptotics

namespace ZetaS

theorem frameFamily_of_zeroConfig (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z) {P : Zeta23.Params}
    (hP : P.Valid) (hlam : P.lam < 1) {ψ : ℝ → ℝ} (heven : ∀ s, ψ (-s) = ψ s) (hcont : Continuous ψ)
    (hcore : ∀ s, |s| ≤ 1 / 2 → 0 ≤ ψ s ∧ ψ s ≤ 1) {c : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → Zeta23.AdmWindow (P.phiV ψ T) (P.L T) P.w c)
    (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s) (hb : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s ^ 2) :
    ∃ Fm : FrameFamilyL P.lam (fun T => (Z.N T (2 * T) : ℝ)) (Rlam P.lam ψ) (kPsi ψ),
      ∃ r : ℝ → ℝ, r =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧ ∀ᶠ T in atTop,
        ((Fm.F T).NsW : ℝ) ≤ Z.Ns T (2 * T) + r T ∧
        ((Fm.F T).NdW : ℝ) ≤ Z.Nd T (2 * T) + r T ∧
        ((Fm.F T).NscW : ℝ) ≤ (Z.N0 T (2 * T) : ℝ) + Z.Ns T (2 * T) - Z.N0s T (2 * T) + r T := by
  obtain ⟨Fm, r, hr, hev⟩ := frameFamily_of_zeroConfig_fix Z H hP hlam heven hcont hcore hadm ha hb
  exact ⟨Fm, r, hr, hev.mono fun T h => ⟨h.1, h.2.1, h.2.2.1⟩⟩

end ZetaS
