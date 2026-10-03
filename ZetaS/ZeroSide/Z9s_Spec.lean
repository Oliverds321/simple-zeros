/-
lean_work/L3_1/Z9s_Spec.lean — node Z9 (assembly), definitions shared by its sub-nodes (agent L3_1, 28 Sep 2026).
No `sorry`.

`FrameSpec Z P ψ T F` is what the construction of the frame at ONE height T (sub-node Z9a) promises about the
`ZeroFrame` it builds from the zero configuration `Z` with the window `φ_T = P.phiV ψ T`, `L = P.L T`,
I′ = (T − √T, 2T + √T] (tree `ZIprime`, `D0 T = √T`):
  * the kernel is the true-window kernel `kWin φ_T L` (feeds Z4 `kernel`, Z5 `dominate`);
  * trace and Frobenius norm of `Ĝ = U diag(m) Uᵀ + Qoff` are those of the tree's hat-units window matrix
    `(P.atV ψ T).hat T (Z.Az (P.atV ψ T) T)` (feeds W9.8 via the tail transfer Z9b);
  * the window count is `N(I′)`, the span is `|I′| L/2π`, the weighted defect is the one of node Z6;
  * the three window counts of the statistics are the configuration's counts on I′ (feeds the seams Z9e).
-/
import ZetaS.InterfacesV2
import Zeta23.Hypotheses

noncomputable section

open Filter Asymptotics

namespace ZetaS
namespace Z9

open Zeta23

/-- The on-line window I′ = (T − √T, 2T + √T] as the pair of endpoints used by the tree's counts. -/
abbrev lo (T : ℝ) : ℝ := T - Real.sqrt T
abbrev hi (T : ℝ) : ℝ := 2 * T + Real.sqrt T

/-- What the frame at height `T` must satisfy (see the file header). -/
structure FrameSpec (Z : ZeroConfig) (P : Params) (ψ : ℝ → ℝ) (T : ℝ) (F : ZeroFrame) : Prop where
  k_eq : F.k = kWin (P.phiV ψ T) (P.L T)
  tr_eq : RHLinalg.rtrace F.Gt = RHLinalg.rtrace ((P.atV ψ T).hat T (Z.Az (P.atV ψ T) T))
  frob_eq : RHLinalg.frobSq F.Gt = RHLinalg.frobSq ((P.atV ψ T).hat T (Z.Az (P.atV ψ T) T))
  Nw_eq : F.Nw = Z.NIprime T
  Λ_eq : F.Λ = (T + 2 * Real.sqrt T) * P.L T / (2 * Real.pi)
  defect_eq : ∑ i, (F.m i : ℝ) * F.delta i
      = ∑ᶠ ρ ∈ Z.window (lo T) (hi T) ∩ {ρ : ℂ | ρ.re = 1 / 2},
          (Z.mult ρ : ℝ) * deltaW (P.phiV ψ T) (P.L T) T (P.d T) ρ.im
  NsW_eq : F.NsW = Z.Ns (lo T) (hi T)
  /-- the simple on-line zeros of I′ (needed for W1L: s₁ ≤ N₀ˢ + o(N)). -/
  sEq1_eq : F.sEq 1 = Z.N0s (lo T) (hi T)
  NdW_eq : F.NdW = Z.Nd (lo T) (hi T)
  NscW_eq : (F.NscW : ℝ) = (Z.N0 (lo T) (hi T) : ℝ) + Z.Ns (lo T) (hi T) - Z.N0s (lo T) (hi T)

end Z9
end ZetaS
