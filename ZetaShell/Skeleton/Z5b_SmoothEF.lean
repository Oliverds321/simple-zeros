/-
Node Z5b (L7_5, 28 Sep 2026): Lemma 5b, smooth explicit formula (sec_shell.tex, lem:shell-5b):
"For χ primitive mod r, V ∈ C_c^∞((0,∞)) and Ṽ(w) = ∫ V(y) y^{w−1} dy,
 Σ_n Λ(n)χ(n)V(n) = δ_{r=1}Ṽ(1) − Σ_ρ Ṽ(ρ) − δ_{r>1,χ(−1)=1}Ṽ(0) − (1/2πi)∫_{(−1/2)} (L′/L)(w,χ)Ṽ(w) dw,
 with |(L′/L)(−1/2+it, χ)| ≪ log(r(|t|+2))."
Zeros: `IsNtZero χ ρ` (nontrivial zero of Mathlib's `χ.LFunction`), counted with `zmult` (analytic order); these
are definitionally Zeta23's `IsNontrivialZeroL`, `zeroMultL`. For `r = 1`, `χ.LFunction` is `riemannZeta`.
`(1/2πi)∫_{(−1/2)} F(w) dw = (1/2π)∫ F(−1/2+it) dt`. `V` is complex-valued (Proposition Z applies it to
`V_{x,s}(y) = A_s(y) f(Δ(y−x))`, which is complex because `D_T` is); the formula is linear in `V`.
-/
import ZetaShell.PropZ.ZDefs
import ZetaShell.PropZ.Z5b_Weil
import ZetaShell.PropZ.Z5b_WeilOne

open MeasureTheory Complex

namespace ZetaShell.PropZ

open scoped Classical in
/-- **Z5b, formula.** -/
theorem smooth_explicit_formula {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (V : ℝ → ℂ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (hVpos : tsupport V ⊆ Set.Ioi 0) :
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℂ) * mellin V ρ.1) ∧
    Integrable (fun t : ℝ => logDeriv χ.LFunction (-1 / 2 + t * I) * mellin V (-1 / 2 + t * I)) ∧
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * V n
      = (if r = 1 then mellin V 1 else 0)
        - ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin V ρ.1
        - (if r ≠ 1 ∧ χ.Even then mellin V 0 else 0)
        - (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, logDeriv χ.LFunction (-1 / 2 + t * I) * mellin V (-1 / 2 + t * I) := by
  sorry

/-- **Z5b, bound**, uniform in the modulus, the character and `t`. -/
theorem logDeriv_bound : ∃ C : ℝ, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
    ∀ t : ℝ, ‖logDeriv χ.LFunction (-1 / 2 + t * I)‖ ≤ C * Real.log (r * (|t| + 2)) := by
  sorry

open scoped Classical in
/-- Z5b-W, the case `r = 1` (ζ), from `Zeta23.WeilEF.EF_lit_zetaZeroConfig` (see `Z5b_WeilOne.lean`). -/
theorem smooth_explicit_formula_weil_one {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (h1 : r = 1)
    (hχ : χ.IsPrimitive)
    (V : ℝ → ℂ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (hVpos : tsupport V ⊆ Set.Ioi 1) :
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℂ) * mellin V ρ.1) ∧
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * V n
      = (if r = 1 then mellin V 1 + mellin V 0 else 0)
        - ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin V ρ.1
        + (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, mellin V (1 / 2 + t * I)
            * (((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
                + Real.log (r / Real.pi) : ℝ) : ℂ) := by
  subst h1
  obtain ⟨hs, he⟩ := smooth_explicit_formula_weil_mod1 χ V hV hVc hVpos
  refine ⟨hs, ?_⟩
  have hEven : χ.Even := by
    show χ (-1) = 1
    rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  have hg : ∀ t : ℝ, ((((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
      + Real.log ((1 : ℕ) / Real.pi) : ℝ) : ℂ)) = ((Zeta23.EF.gammaBracket t : ℝ) : ℂ) := by
    intro t
    have harg : (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * t / 2) = 1 / 4 + I * t / 2 := by push_cast; ring
    rw [if_pos hEven, harg, Zeta23.EF.gammaBracket, Nat.cast_one, Real.log_div one_ne_zero Real.pi_ne_zero,
      Real.log_one]
    push_cast; ring
  rw [if_pos rfl]
  simp only [hg]
  exact he

open scoped Classical in
/-- **Z5b-W (proposed replacement, Weil form)**: what `Zeta23.ThmE.EF_lit_chi_L` (r > 1) and
`Zeta23.WeilEF.EF_lit_zeta` (r = 1) give after `k(u) = e^{u/2}V(e^u)`: the conjugate leg vanishes because
`V = 0` on `(0, 1]`, and the archimedean term stays on the critical line. Checked numerically for `ζ` (L7_5 T6). -/
theorem smooth_explicit_formula_weil {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (V : ℝ → ℂ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVc : HasCompactSupport V)
    (hVpos : tsupport V ⊆ Set.Ioi 1) :
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℂ) * mellin V ρ.1) ∧
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * V n
      = (if r = 1 then mellin V 1 + mellin V 0 else 0)
        - ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℂ) * mellin V ρ.1
        + (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, mellin V (1 / 2 + t * I)
            * (((Complex.digamma (1 / 4 + ((if χ.Even then 0 else 1 : ℕ) : ℂ) / 2 + I * t / 2)).re
                + Real.log (r / Real.pi) : ℝ) : ℂ) := by
  rcases eq_or_ne r 1 with h1 | h1
  · exact smooth_explicit_formula_weil_one χ h1 hχ V hV hVc hVpos
  · have hr : 1 < r := by have := NeZero.pos r; omega
    obtain ⟨hs, he⟩ := smooth_explicit_formula_weil_gt1 χ hr hχ V hV hVc hVpos
    refine ⟨hs, ?_⟩
    rw [he, if_neg h1]; ring

end ZetaShell.PropZ
