/-
lean_work/L1_1/nodes/NodeDefs.lean — shared real-side definitions for the track-C nodes (L1_1b, 28 Sep 2026).
Imports the checker (v3, `CheckerCoreV3`, computable, core only), the specification (`CertSpecAM5`: `kCos`, `LIQ.F`,
`LIQ.Holds`, `Cert`, `CertAM5`, `W5`, `classData`) and L0_2's `CosWindow` (alternating Taylor bounds for sin/cos,
moments of cos(αs)). No sorry here.
-/
import ZetaS.Cert.CertSpecAM5
import ZetaS.Window.CosWindow

noncomputable section

namespace ZetaS.CertV2

/-- `x ∈ [lo, hi]`. -/
def QI.Contains (I : QI) (x : ℝ) : Prop := ((I.lo : ℚ) : ℝ) ≤ x ∧ x ≤ ((I.hi : ℚ) : ℝ)

/-- sinc′ and sinc″ in closed form (values at 0 by continuity). -/
def sinc1 (y : ℝ) : ℝ := if y = 0 then 0 else (Real.cos y - Real.sinc y) / y
def sinc2 (y : ℝ) : ℝ := if y = 0 then -1 / 3 else -Real.sinc y - 2 * sinc1 y / y

/-- k′ and k″ of the cosine-window kernel in closed form. -/
def kCos1 (x : ℝ) : ℝ :=
  Real.pi * (sinc1 (Real.pi * x - 4 / 5) + sinc1 (Real.pi * x + 4 / 5)) / (2 * Real.sinc (4 / 5))
def kCos2 (x : ℝ) : ℝ :=
  Real.pi ^ 2 * (sinc2 (Real.pi * x - 4 / 5) + sinc2 (Real.pi * x + 4 / 5)) / (2 * Real.sinc (4 / 5))

/-- w = k², and w″ = 2k′² + 2kk″. -/
def wK (x : ℝ) : ℝ := kCos x ^ 2
def wK2 (x : ℝ) : ℝ := 2 * kCos1 x ^ 2 + 2 * kCos x * kCos2 x

/-- What a `KPt` record asserts. -/
def KPt.Sound (p : KPt) : Prop :=
  p.k0.Contains (kCos p.x) ∧ p.k1.Contains (kCos1 p.x) ∧ p.k2.Contains (kCos2 p.x)

/-- `g` lies in the box `B` (first `d` coordinates). -/
def Box.Mem (B : Box) (d : ℕ) (g : ℕ → ℝ) : Prop :=
  ∀ l < d, (((B.getD l (0, 0)).1 : ℚ) : ℝ) ≤ g l ∧ g l ≤ (((B.getD l (0, 0)).2 : ℚ) : ℝ)

end ZetaS.CertV2
