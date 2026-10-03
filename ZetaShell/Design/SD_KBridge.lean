/-
L7_7 round 2: **the bridge from L7_1's row-form `ShellFrame` to L7_3's bracket-form `KFrame`**, so that L7_3's proved
`k_assembly` can consume a Shell frame. Every row `rᵢ := c·rate` and, once `c·rate ≤ 1`, the bracket
`4r₁ + r₂ + 3r₃ + 4r₄ + 2r₅√(κ + r₂) + r₅² ≤ (17 + 2κ)·c·rate` (F2's arithmetic). The profiles are related by
`K.lam = S.lam` and `K.p = S.p` pointwise (the two profile structures differ: `KProfile` is Horner in `t²`,
`ShellProfile` is in `(2t/λ)²`). Imports L7_3's `LK_Defs` (source unchanged; olean compiled in my folder).
-/
import ZetaShell.Interfaces
import ZetaShell.Defs.LK_Defs

namespace ZetaShell.Design

open Filter Topology

theorem shellFrame_toKFrame (F : ZetaQ.Family) (r ε : ℝ) (S : ShellProfile) (K : LemmaK.KProfile)
    (hlam : ((K.lam : ℚ) : ℝ) = ((S.lam : ℚ) : ℝ)) (hp : ∀ t, K.p t = S.p t)
    (κ : ℝ) (hκ : 0 ≤ κ) (rate : ℕ → ℝ) (hrate : Tendsto rate atTop (𝓝 0))
    (hrate0 : ∀ᶠ Qn : ℕ in atTop, 0 ≤ rate Qn)
    (Fr : ShellFrame F r ε S κ rate) : Nonempty (LemmaK.KFrame F r ε K κ rate) := by
  obtain ⟨c, hc, hrows⟩ := Fr.rows
  have hsmall : ∀ᶠ Qn : ℕ in atTop, rate Qn ≤ 1 / c :=
    hrate.eventually (ge_mem_nhds (by positivity))
  refine ⟨{
    Des := Fr.Des
    exists_design := Fr.exists_design
    T_eq := Fr.T_eq
    Q_eq := Fr.Q_eq
    lam_eq := fun Q P h => by rw [Fr.lam_eq Q P h, hlam]
    valid := Fr.valid
    prof_eq := fun Q P h t => by rw [Fr.prof_eq Q P h t, hp]
    rows := ?_ }⟩
  refine ⟨c * (17 + 2 * κ), by positivity, ?_⟩
  filter_upwards [hrows, hrate0, hsmall] with Qn hrow hr0 hr1
  intro P hP
  obtain ⟨θ₀, hθ, hBtr0, hBF0, hdisp, htr, hfrob, hNII, hBtr, hBF⟩ := hrow P hP
  set x := c * rate Qn with hx
  have hx0 : 0 ≤ x := mul_nonneg hc.le hr0
  have hx1 : x ≤ 1 := by
    rw [hx]
    calc c * rate Qn ≤ c * (1 / c) := by gcongr
      _ = 1 := by field_simp
  refine ⟨x, x, x, x, x, θ₀, hθ, hBtr0, hBF0, by linarith, hdisp, htr, hfrob, hNII, hBtr, hBF, ?_⟩
  have hsq : Real.sqrt (κ + x) ≤ κ + 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have h1 : 2 * x * Real.sqrt (κ + x) ≤ 2 * x * (κ + 2) := by gcongr
  have h2 : x ^ 2 ≤ x := by nlinarith
  have e : c * (17 + 2 * κ) * rate Qn = (17 + 2 * κ) * x := by rw [hx]; ring
  rw [e]
  nlinarith

end ZetaShell.Design
