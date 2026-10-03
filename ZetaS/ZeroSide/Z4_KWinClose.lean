/-
Node Z4 (track W) — `kernel` field: for the tree's window `P.phiV ψ T` (any bandwidth λ = P.lam),
sup_t |k_φ(t) − k_ψ(t)| ≤ ‖v_φ − v_ψ‖₁ = O(w/L) → 0 (lem:sigd-residue (iii); W5-type moment closeness, L0_2).
Hypotheses as the tree needs them (L0_2b M2): ψ continuous, 0 ≤ ψ ≤ 1 on the core, ∫ψ > 1/2.

Proof (L3_2): `e T = 16 w/L(T)`. At each height with 8w ≤ L: `kWin φ L t = Nφ(t)/Nφ(0)`, `kPsi ψ t = Nψ(t)/Nψ(0)` with
`|Nφ(t) − Nψ(t)| ≤ 2w` for every t (the ramp has total length 2w; tree `edge_estimate`), `|Nψ(t)| ≤ Nψ(0) = L∫ψ > L/2`,
hence `Nφ(0) ≥ L/4` and `|kWin − kPsi| ≤ 4w/Nφ(0) ≤ 16w/L` (`KWinHelpers.kWin_close_at`).
-/
import ZetaS.InterfacesV2
import ZetaS.ZeroSide.KWinHelpers

open Filter Topology

namespace ZetaS

theorem kWin_close {P : Zeta23.Params} (hP : P.Valid) {ψ : ℝ → ℝ} (hcont : Continuous ψ)
    (hcore : ∀ s, |s| ≤ 1 / 2 → 0 ≤ ψ s ∧ ψ s ≤ 1) (ha : 1 / 2 < ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ T in atTop, ∀ t, |kWin (P.phiV ψ T) (P.L T) t - kPsi ψ t| ≤ e T := by
  have hv : ProfileMoments.CoreProfile ψ := ⟨hcont, fun s hs => (hcore s hs).1, fun s hs => (hcore s hs).2⟩
  have hl : Tendsto Zeta23.l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  refine ⟨fun T => 16 * P.w / P.L T, tendsto_const_nhds.div_atTop hL, ?_⟩
  filter_upwards [hL.eventually_ge_atTop (8 * P.w)] with T hT t
  rw [ProfileMoments.phiV_eq_phiM]
  exact KWinHelpers.kWin_close_at hv hP.taper hP.one_le_w hT ha t

end ZetaS
