/-
Node KL3 (track T, bandwidth) — R_λ(ψ) → R(ψ) as λ → 1⁻ (a rational function of λ; `Rlam_one` is proved in
InterfacesV2). With KL2 and the continuity of the constants in H this turns the fixed-λ constants into the draft's.
-/
import ZetaS.InterfacesV2

open Filter Topology

namespace ZetaS

theorem tendsto_Rlam_one (ψ : ℝ → ℝ) (ha : (∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u) ≠ 0) :
    Tendsto (fun lam => Rlam lam ψ) (𝓝[<] 1) (𝓝 (Rpsi ψ)) := by
  have hc : ContinuousAt (fun lam => Rlam lam ψ) 1 := by
    unfold Rlam
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using pow_ne_zero 2 ha
  rw [← Rlam_one ψ]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

end ZetaS
