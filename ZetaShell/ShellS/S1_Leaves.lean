/-
S1_Leaves (L7_5b, 1 Oct 2026): the inputs of S1 other than A⋆ and Proposition Z, as named nodes.
Status per node in the report (Round 10). Statements quote sec_shell.tex (thm:shell-S proof, lem:shell-5c(1),
lem:shell-star's hypothesis on `Σ μ²/φ`).
-/
import ZetaShell.ShellS.S1_Defs
import ZetaShell.ShellS.S1L_Twist
import ZetaShell.ShellS.S1L_TestFn
import ZetaShell.ShellS.S1L_Eventually
import ZetaShell.ShellS.S1L_Meas
import ZetaShell.ShellS.S1L_Model
import ZetaShell.ShellS.S1L_MuSq
import ZetaShell.ShellS.S1L_PP

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- `Σ_{y ≤ m < Ky, m ≤ R₁} μ²(m)/φ(m) ≤ D (log K + 1)` for every `y > 0`, `K ≥ 1` (the window hypothesis of A⋆,
with `Cμ = D(log K + 1) − log K`). Proof route: `m/φ(m) = Σ_{d|m} μ²(d)/φ(d)`, then the harmonic window
`Σ_{a ≤ j < Ka} 1/j ≤ log K + 1` and `Σ_d μ²(d)/(dφ(d)) < ∞`. -/
theorem musq_window : ∃ D : ℝ, 1 ≤ D ∧ ∀ (R1 : ℕ) (K : ℝ), 1 ≤ K → ∀ y : ℝ, 0 < y →
    ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
      ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) ≤ D * (Real.log K + 1) :=
  musq_window'

/-- Lemma 5c(1) core: the prime powers `p^k`, `k ≥ 2`, in the window `(e^{s−1}, e^{s+1}]` carry
`Σ Λ(n) n^{−1/2} ≤ Cp`, uniformly in `s` (Chebyshev: `θ(x) ≤ x log 4`). -/
theorem pp_window : ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ s : ℝ,
    ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Cp :=
  pp_window'

/-- a test function with `f̂² ≥ c > 0` on `[−1, 1]` (a smooth even bump on `(−1/8, 1/8)`: `cos(2πzη) ≥ cos(π/4)`). -/
theorem exists_testFn : ∃ (f : ℝ → ℝ) (c : ℝ), TestFn f ∧ 0 < c ∧
    ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2 :=
  exists_testFn'

/-- the model `M_s` is continuous and `∫_{−1/2}^{1/2} |M_s|² ≤ CU·T` (Plancherel: `≤ (2π)⁻² ∫|A_s|²`, and
`∫_0^∞ |A_s(y)|² dy = ∫ |D_T(u)|² Ξ² du ≪ T`). -/
theorem Mmod_props (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) :
    ∃ CU : ℝ, 0 ≤ CU ∧ ∀ T : ℝ, 2 ≤ T → ∀ s : ℝ,
      Continuous (Mmod T κ Ξ s) ∧ (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖Mmod T κ Ξ s β‖ ^ 2) ≤ CU * T :=
  Mmod_props' κ hκ hκ1 Ξ hΞ

/-- `s ↦ W(s−s₀) Ring(s)` is a.e.-strongly measurable. -/
theorem ringS_aesm (Qn : ℕ) (T κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (K ε s₀ : ℝ)
    (W : ℝ → ℝ) (hW : AvgWeight W) :
    AEStronglyMeasurable (fun s => W (s - s₀) * RingS Qn T κ Ξ K ε s₀ s) volume :=
  ringS_aesm' Qn T κ hκ hκ1 Ξ hΞ K ε s₀ W hW

/-- the twisted near-prime sum minus the model is `−(2π)⁻¹ (S_χ − P_χ)`: the primes `n ≤ Q` lie outside the near
window when `Q ≤ e^{s−1}`, and `n > N(s)` lies above it. -/
theorem twist_sub_model (Qn : ℕ) (T κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (s : ℝ)
    (hQ : (Qn : ℝ) ≤ Real.exp (s - 1)) (r : ℕ) (χ : DirichletCharacter ℂ r) (β : ℝ) :
    TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β - (if r = 1 then Mmod T κ Ξ s β else 0)
      = -(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (Schi χ T κ Ξ s β - PPart χ T κ Ξ s β) :=
  twist_sub_model' Qn T κ hκ hκ1 Ξ hΞ s hQ r χ β

/-- the parameter conditions of Theorem S's range that S1 uses, for all large `Q`. -/
theorem S1_eventually (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (αp B : ℝ) (hα2 : αp < 2) (hB : 1 ≤ B) :
    ∀ᶠ Qn : ℕ in Filter.atTop, 2 ≤ twin Qn r0 ε0 ∧ 1 ≤ (Qn : ℝ) ∧ ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      2 * K * (R1S Qn ε s₀ : ℝ) ≤ Qn ∧ (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀ ∧ K / Qn ≤ 1 :=
  S1_eventually' r0 ε0 hr0 hε0 αp B hα2 hB

end ShellS
end ZetaShell
