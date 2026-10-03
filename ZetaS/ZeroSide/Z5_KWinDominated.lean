/-
Node Z5 (track W) — `dominate` field (lem:sigd-env, l.1286–1291): v_φ ≤ (1 + ε′_T)v_ψ pointwise, hence
(1 + ε′_T)k_ψ − k_φ is a positive-definite kernel, with ε′_T = δ₀/(1 − δ₀) → 0.

Proof (L3_2): `e T = 8 w/L(T)`. In the u-variable, `(1 + e)kPsi ψ t − kWin φ L t = ∫_{[−L/2,L/2]} g(u) cos(2πtu/L) du`
with density `g = mV·((1 + e)/Nψ(0) − ϱ_L²/Nφ(0))`, where `mV = ψ(·/L) ≥ 0` on the core and `0 ≤ ϱ_L² ≤ 1` is the
squared ramp. `g ≥ 0` because `(1 + e)Nφ(0) ≥ Nφ(0) + 2w ≥ Nψ(0)` (`Nφ(0) ≥ L/4`, `|Nφ(0) − Nψ(0)| ≤ 2w`), and a
cosine transform of a nonnegative density is positive definite (Bochner, easy direction:
Σ cᵢcⱼ cos(aᵢ − aⱼ) = (Σ cᵢ cos aᵢ)² + (Σ cᵢ sin aᵢ)²) — `KWinHelpers.kWin_dominated_at`.
The sharp ε′ is `∫ψ/∫(ϱ_L²ψ) − 1 ≈ (w/L)` for a smooth ramp (numerics `z45_numcheck.py`); ε′ = 0 is false.
-/
import ZetaS.InterfacesV2
import ZetaS.ZeroSide.KWinHelpers

open Filter Topology

namespace ZetaS

theorem kWin_dominated {P : Zeta23.Params} (hP : P.Valid) {ψ : ℝ → ℝ} (hcont : Continuous ψ)
    (hcore : ∀ s, |s| ≤ 1 / 2 → 0 ≤ ψ s ∧ ψ s ≤ 1) (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ T in atTop, IsPosDefKernel (fun t => (1 + e T) * kPsi ψ t - kWin (P.phiV ψ T) (P.L T) t) := by
  have hv : ProfileMoments.CoreProfile ψ := ⟨hcont, fun s hs => (hcore s hs).1, fun s hs => (hcore s hs).2⟩
  have hl : Tendsto Zeta23.l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  refine ⟨fun T => 8 * P.w / P.L T, tendsto_const_nhds.div_atTop hL, ?_⟩
  filter_upwards [hL.eventually_ge_atTop (8 * P.w)] with T hT
  rw [ProfileMoments.phiV_eq_phiM]
  exact KWinHelpers.kWin_dominated_at hv hP.taper hP.one_le_w hT ha

end ZetaS
