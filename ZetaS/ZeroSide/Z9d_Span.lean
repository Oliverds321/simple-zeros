/-
Sub-node Z9d (agent L3_1) — `span_lam` (lem:sigd-residue (v) at bandwidth λ): Λ = |I′|L/2π = (T + 2√T)λℓ/2π
≤ λN(T,2T) + o(N), from H-RvM `main` (N(T,2T) = (T/2π)(ℓ + 2log2 − 1) + O(log T)); in fact Λ ≤ λN eventually,
since 2log 2 − 1 > 0.
-/
import ZetaS.ZeroSide.Z9s_Spec
import Zeta23.Assembly

noncomputable section

open Filter Asymptotics

namespace ZetaS
namespace Z9

open Zeta23

theorem span_bound (Z : ZeroConfig) (H : PaperInputs Z) {P : Params} (hP : P.Valid) :
    ∃ r : ℝ → ℝ, r =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧ ∀ᶠ T in atTop,
      (T + 2 * Real.sqrt T) * P.L T / (2 * Real.pi) ≤ P.lam * (Z.N T (2 * T) : ℝ) + r T := by
  obtain ⟨C, T₀, hC⟩ := H.RvM.main
  refine ⟨fun T => P.lam * (|C| * Real.log T + (1 / Real.pi) * (Real.sqrt T * l T)), ?_, ?_⟩
  · have h1 : (fun T => |C| * Real.log T + (1 / Real.pi) * (Real.sqrt T * l T)) =o[atTop]
        fun T => T * l T :=
      (Assembly.isLittleO_log_Tl.const_mul_left |C|).add
        (Assembly.isLittleO_sqrt_mul_l_Tl.const_mul_left (1 / Real.pi))
    exact (Assembly.isLittleO_N_of_isLittleO_Tl Z H.RvM h1).const_mul_left P.lam
  · filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop 0, Assembly.eventually_l_pos,
      Assembly.eventually_log_nonneg] with T hT hT0 hl hlog
    have h1 := (abs_le.mp (hC T hT)).1
    have hc := Assembly.c₀_pos
    have hℓ : l T ≤ ell1 T := by rw [Assembly.ell1_eq]; linarith
    have hpi := Real.pi_pos
    have h3 : T / (2 * Real.pi) * l T ≤ T / (2 * Real.pi) * ell1 T :=
      mul_le_mul_of_nonneg_left hℓ (by positivity)
    have h2 : C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlog
    have key : T * l T / (2 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) + |C| * Real.log T := by
      have : T / (2 * Real.pi) * l T = T * l T / (2 * Real.pi) := by ring
      linarith
    have hlam := hP.lam_pos
    have hL : P.L T = P.lam * l T := rfl
    rw [hL]
    have e : (T + 2 * Real.sqrt T) * (P.lam * l T) / (2 * Real.pi)
        = P.lam * (T * l T / (2 * Real.pi)) + P.lam * ((1 / Real.pi) * (Real.sqrt T * l T)) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left key hlam.le
    nlinarith

end Z9
end ZetaS
