/-
nodes/C01_QIRound.lean — track C node C01 (L1_1b, 28 Sep 2026).
Depends on: none.
PROVED (L1_1b, 28 Sep 09:57).
-/
import ZetaS.Cert.NodeDefs

noncomputable section

open Set

namespace ZetaS.CertV2

theorem QI.rdn_le (q : ℚ) : QI.rdn q ≤ q := by
  unfold QI.rdn QI.grid
  have hg : (0 : ℚ) < 2 ^ 64 := by positivity
  have h : (((q * 2 ^ 64).floor : ℤ) : ℚ) ≤ q * 2 ^ 64 := by
    first
    | exact Rat.floor_le _
    | exact (Rat.le_floor.mp le_rfl)
    | (rw [← Rat.floor_intCast_div_natCast] at *; exact Int.floor_le _)
    | exact Int.floor_le (q * 2 ^ 64)
  rw [div_le_iff₀ hg]; exact h

theorem QI.le_rup (q : ℚ) : q ≤ QI.rup q := by
  unfold QI.rup QI.grid
  have hg : (0 : ℚ) < 2 ^ 64 := by positivity
  have h : q * 2 ^ 64 ≤ (((q * 2 ^ 64).ceil : ℤ) : ℚ) := by
    first
    | exact Rat.le_ceil
    | exact (Rat.le_ceil (x := q * 2 ^ 64))
    | exact (Rat.ceil_le.mp le_rfl)
    | exact Int.le_ceil (q * 2 ^ 64)
  rw [le_div_iff₀ hg]; exact h

end ZetaS.CertV2
