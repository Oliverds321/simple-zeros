/-
Node Z6, profile form (agent L3_2, 28 Sep 2026). Superseded by `Z6_Defect.lean`, which proves the skeleton statement
AS WRITTEN; kept because it gives the explicit normalisation κ = 1/4 (∫φ_T² ≥ L/4 for 8w ≤ L) under the hypotheses of
Z4/Z5/Z9 (`Continuous ψ`, `0 ≤ ψ ≤ 1` on the core, `∫ψ > 1/2`), with no dichotomy.
-/
import ZetaS.InterfacesV2
import Zeta23.Hypotheses
import ZetaS.ZeroSide.Z6Core

open Filter Asymptotics

namespace ZetaS
namespace Z6

open Zeta23 Zeta23.XiPrime ProfileMoments KWinHelpers

theorem defect_littleO_fix (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z) {P : Zeta23.Params}
    (hP : P.Valid) (_hlam : P.lam < 1) {ψ : ℝ → ℝ} {c : ℝ}
    (hadm : ∀ T, 8 * P.w ≤ P.L T → Zeta23.AdmWindow (P.phiV ψ T) (P.L T) P.w c)
    (hcont : Continuous ψ) (hcore : ∀ s, |s| ≤ 1 / 2 → 0 ≤ ψ s ∧ ψ s ≤ 1)
    (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s) :
    (fun T => ∑ᶠ ρ ∈ Z.window (T - Real.sqrt T) (2 * T + Real.sqrt T) ∩ {ρ : ℂ | ρ.re = 1 / 2},
        (Z.mult ρ : ℝ) * deltaW (P.phiV ψ T) (P.L T) T (P.d T) ρ.im)
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  have hv : CoreProfile ψ := ⟨hcont, fun s hs => (hcore s hs).1, fun s hs => (hcore s hs).2⟩
  have hl : Tendsto Zeta23.l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hLt : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hw := hP.one_le_w
  refine defect_core Z H hP (κ := 1 / 4) (by norm_num) hadm ?_
  filter_upwards [hLt.eventually_ge_atTop (8 * P.w)] with T h8
  have hL : 0 < P.L T := by linarith
  rw [ProfileMoments.phiV_eq_phiM, integral_sq_eq_Nphi hv hP.taper (by linarith) hL]
  have := (norms_bounds hv hP.taper hw h8 ha).2
  linarith

end Z6
end ZetaS
