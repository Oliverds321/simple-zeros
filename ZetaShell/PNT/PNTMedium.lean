import Zeta23.FromPNTPlus.MediumPNT

/-!
# L7_2: the PNT input of the Shell chain, in the form the existing tree supplies

`L7_1`'s `PNTErrorTerm` (ChallengeShell.lean l.134) asks for the de la Vallée Poussin form
`|ψ y − y| ≤ c₁ y exp(−c₂ √(log y))`.  The tree's `MediumPNT` gives only
`ψ − id = O(x exp(−c (log x)^{1/10}))`.  The asymptotic Shell chain (lem:K-P / lem:shell-4 and the
norm identity `‖a(s)‖² = U(s+O(1))`) needs only `ψ(y) − y = o(y (log y)^{−A})` for one fixed
`A = A(r)`, which the medium form gives.  This file records the medium form as a `Prop` and
discharges it from the tree (trust level A), plus the `∀ A` corollary in `IsLittleO` form.
-/

open Filter Real Asymptotics
open scoped Chebyshev

namespace L7_2

/-- The PNT input in the form the tree proves (`Zeta23.FromPNTPlus.MediumPNT`). -/
def PNTErrorTermMedium : Prop :=
  ∃ c > 0, (ψ - id) =O[atTop] fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))

theorem pntErrorTermMedium : PNTErrorTermMedium := MediumPNT

/-- `exp(−c u^{1/10}) = o(u^{−A})` as `u → ∞`, for every `A` and `c > 0`. -/
theorem exp_rpow_tenth_isLittleO (c A : ℝ) (hc : 0 < c) :
    (fun u : ℝ ↦ Real.exp (-c * u ^ ((1 : ℝ) / 10))) =o[atTop] fun u ↦ u ^ (-A) := by
  -- substitute u = v^10 : exp(-c v) = o(v^{-10A})
  have h1 : Tendsto (fun u : ℝ ↦ u ^ ((1 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h2 : (fun v : ℝ ↦ Real.exp (-c * v)) =o[atTop] fun v ↦ v ^ (-(10 * A)) := by
    have := isLittleO_exp_neg_mul_rpow_atTop hc (-(10 * A))
    simpa using this
  have h3 := h2.comp_tendsto h1
  refine h3.congr' (Eventually.of_forall fun u ↦ rfl) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  simp only [Function.comp]
  rw [← Real.rpow_mul hu]
  congr 1
  ring

/-- **The form the Shell chain consumes**: for every `A`, `ψ(x) − x = o(x (log x)^{−A})`.
(lem:K-P needs `E*/N = o(K^{-1} T^{-3/2})` at `N ≥ QTK` with `K T^{3/2}` a fixed power of `log Q`;
the norm identity needs relative error `o(1/T)` in intervals of relative length `1/T`.) -/
theorem psi_sub_id_isLittleO_log_rpow (A : ℝ) :
    (ψ - id) =o[atTop] fun x : ℝ ↦ x * (Real.log x) ^ (-A) := by
  obtain ⟨c, hc, hO⟩ := pntErrorTermMedium
  have h := (exp_rpow_tenth_isLittleO c A hc).comp_tendsto Real.tendsto_log_atTop
  have h' : (fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) =o[atTop]
      fun x : ℝ ↦ x * (Real.log x) ^ (-A) :=
    (isBigO_refl (fun x : ℝ ↦ x) atTop).mul_isLittleO h
  exact hO.trans_isLittleO h'

end L7_2

#print axioms L7_2.pntErrorTermMedium
#print axioms L7_2.exp_rpow_tenth_isLittleO
#print axioms L7_2.psi_sub_id_isLittleO_log_rpow
