/-
lean_work/L0_4/InterfacesV2.lean — interface version 2 (L0_4, 28 Sep 2026, after L0_2b §4 M1–M4).

Imports `Interfaces` (v1, unchanged: the proved nodes L1, L2, L3, L3b, L5, L6, L8 import it) and adds:

  §1 BANDWIDTH λ (M1). The tree proves the prime side at fixed λ < 1 only (L = λ·l). In the tree's normalisation the
     zeros are seen at x = γL/2π, the kernel between two on-line zeros is k(x − x′) with
     k(t) = V_φ(2πt/L)/∫φ² = k_φ(t) → k_ψ(t) — the SAME kernel as at bandwidth one — and only the density changes:
     the x-length of I′ is Λ = |I′|L/2π = λ·N(1 + o(1)). Hence every K-side statement (GramData, ZeroFrame, the
     families, LocalCert, LocalCertAM, K1–K7, A1–A8) is bandwidth-free; the bandwidth enters only through
     R_λ(ψ) = (∫ψ² + λ²J)/(λ(∫ψ)²) in the Frobenius field and through Λ ≤ λN + o(N) (≤ N + o(N), the v1 field).
     New here: `Jpsi`, `Rlam`, `Hlam` (with `Rlam 1 ψ = Rpsi ψ`, proved), `LocalWeights.scaleMu` (the y-unit reading of
     a certificate), and `FrameFamilyL`/`GramFamilyL` (the families with the sharper span `Λ ≤ λN + o(N)`).
  §2 TREE-LEVEL FRAME OBJECTS (M3). Per-zero vectors `uR`/`uC` on the grid τ_k = T + 2πk/L, the window kernel
     `kWin v L t = V_v(2πt/L)/∫v²` (x-units), the off-grid index set, the defect `deltaW`. The M3 nodes Z1–Z9 are stated
     about these.
  §3 SCALARS (M4). Convention: `GramData`/`ZeroFrame` stay REAL; the tree's ℂ-matrices with real entries are
     converted by `Matrix.map Complex.ofReal` (node R1). L1–L8 are stated over `RCLike 𝕜` and apply to both.

Compile: bash lean_tools/leanrun.sh InterfacesV2.lean <L0_4>/olean -- -o <L0_4>/olean/InterfacesV2.olean
The file contains no `sorry`.
-/
import ZetaS.Interfaces
import Zeta23.ThmD.WindowCore
import Zeta23.XiPrime.Defs

noncomputable section

open scoped BigOperators
open Matrix Filter Topology Asymptotics Finset

namespace ZetaS

/-! ## §1 Bandwidth -/

/-- `J(ψ) = ∬_{[−1/2,1/2]²} |u − v| ψ(u)ψ(v)` (eq:zeta-R). The tree's `jWin id λ ψ = λ·J(ψ)`
(`2∫₀¹ r (ψ⋆ψ)(r) dr = J(ψ)`; L0_2: `jvConv_cosW` for cos α, `jWin_psiN` for poly8A). -/
def Jpsi (ψ : ℝ → ℝ) : ℝ :=
  ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * ψ u * ψ v

/-- `R_λ(ψ) = (∫ψ² + λ²J)/(λ(∫ψ)²) = 1/c_λ(ψ)` — the Frobenius constant at bandwidth `λ`
(tree: `1/XiPrime.cWin id λ ψ`, `ThmD.cRatio`). -/
def Rlam (lam : ℝ) (ψ : ℝ → ℝ) : ℝ :=
  ((∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u ^ 2) + lam ^ 2 * Jpsi ψ)
    / (lam * (∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u) ^ 2)

/-- `H_λ(ψ) = 2 − R_λ(ψ)`. -/
def Hlam (lam : ℝ) (ψ : ℝ → ℝ) : ℝ := 2 - Rlam lam ψ

/-- At bandwidth one, `R_1 = R(ψ)` of eq:zeta-R (v1's `Rpsi`). -/
theorem Rlam_one (ψ : ℝ → ℝ) : Rlam 1 ψ = Rpsi ψ := by
  simp [Rlam, Rpsi, Jpsi]

theorem Hlam_one (ψ : ℝ → ℝ) : Hlam 1 ψ = Hpsi ψ := by
  simp [Hlam, Hpsi, Rlam_one]

/-- The y-unit (mean-spacing) reading of a certificate at bandwidth `λ`: penalties `μ ↦ λμ`.
`LocalCert k W c ↔ LocalCert (k(λ·)) (W.scaleMu λ) c` for `λ > 0` (node KL1). -/
def LocalWeights.scaleMu {K : ℕ} (W : LocalWeights K) (lam : ℝ) (hlam : 0 ≤ lam) : LocalWeights K where
  γ := W.γ
  μ := fun l => lam * W.μ l
  two_le := W.two_le
  γ_nonneg := W.γ_nonneg
  γ_sum := W.γ_sum
  μ_nonneg := fun l => mul_nonneg hlam (W.μ_nonneg l)

/-- `GramFamily` at bandwidth `λ`: the v1 family plus the sharp span `Λ ≤ λN + o(N)`. -/
structure GramFamilyL (lam : ℝ) (N : ℝ → ℝ) (R : ℝ) (kψ : ℝ → ℝ) extends GramFamily N R kψ where
  lam_pos : 0 < lam
  lam_le_one : lam ≤ 1
  span_lam : ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop, (G T).Λ ≤ lam * N T + r T

/-- `FrameFamily` at bandwidth `λ`: the v1 family plus the sharp span `Λ ≤ λN + o(N)`. -/
structure FrameFamilyL (lam : ℝ) (N : ℝ → ℝ) (R : ℝ) (kψ : ℝ → ℝ) extends FrameFamily N R kψ where
  lam_pos : 0 < lam
  lam_le_one : lam ≤ 1
  span_lam : ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop, (F T).Λ ≤ lam * N T + r T

/-- Fixed-λ constants with the sharp span (the τ- and ν-terms carry a factor λ); at `λ = 1` they are v1's. -/
def stabConstL (lam H : ℝ) (K : ℕ) (ν c : ℝ) (m : ℕ) : ℝ := stabConst H K (lam * ν) c m
def sigmaConstL (lam H a₁ a₂ ν : ℝ) : ℝ := sigmaConst H a₁ a₂ (lam * ν)
def distConstL (lam H a₁ a₂ ν : ℝ) : ℝ := distConst H a₁ a₂ (lam * ν)

/-! ## §2 Tree-level frame objects (x-units) -/

/-- The off-grid indices `k ∉ [0, d)`. -/
def offGrid (d : ℕ) : Type := {k : ℤ // k < 0 ∨ (d : ℤ) ≤ k}

/-- Normalised per-zero vector at a REAL ordinate `γ` (on-line zero `½ + iγ`), all `k ∈ ℤ`:
`u_γ(k) = v̂(γ − τ_k)/√(L ∫v²)`, `τ_k = T + k·2π/L` (eq:zeta-Ghat with `aL² = L∫v²`). -/
def uR (v : ℝ → ℝ) (L T γ : ℝ) (k : ℤ) : ℝ :=
  Zeta23.AdmWindow.vHatR v (γ - (T + k * (2 * Real.pi / L))) / Real.sqrt (L * ∫ u, v u ^ 2)

/-- The same at a COMPLEX ordinate (off-line zero `½ + iγ`, `γ ∉ ℝ`); used only to build `Qoff`. -/
def uC (v : ℝ → ℝ) (L T : ℝ) (γ : ℂ) (k : ℤ) : ℂ :=
  Zeta23.AdmWindow.vHat v (γ - (T + k * (2 * Real.pi / L))) / (Real.sqrt (L * ∫ u, v u ^ 2) : ℂ)

/-- The window kernel in x-units (`x = γL/2π`): `k(t) = V_v(2πt/L)/∫v²`, `V_v = (v²)^` (tree: `VPhiR`).
For `v = P.phiV ψ T` it equals `k_φ(t)` of eq:zeta-poisson and tends to `kPsi ψ t` uniformly (node Z4). -/
def kWin (v : ℝ → ℝ) (L t : ℝ) : ℝ :=
  Zeta23.AdmWindow.VPhiR v (2 * Real.pi * t / L) / ∫ u, v u ^ 2

/-- The defect `δ_γ = Σ_{k ∉ [0,d)} u_γ(k)²` of an on-line zero (lem:sigd-residue (i)). -/
def deltaW (v : ℝ → ℝ) (L T : ℝ) (d : ℕ) (γ : ℝ) : ℝ :=
  ∑' k : offGrid d, uR v L T γ k.1 ^ 2

/-! ## §3 Scalars -/

/-- Real matrices seen as complex ones (the tree's convention; entries real). -/
def toC {n : Type*} (A : Matrix n n ℝ) : Matrix n n ℂ := A.map (fun r => (r : ℂ))

end ZetaS
