/-
Node S1 (L7_10): **Theorem S, step 1: from the windowed ring mass to the zero side** (proof of thm:shell-S, first
three sentences: "Start from Lemma ⋆. Apply Lemma 5a with `Δ_r = K/(rQ)`, then Proposition Z to each primitive
`χ* mod r* ≤ R₁` (ζ with `M̃_s`), and Lemma 5c for the errors. What remains is `(log K) T 𝔷`").
Lean form: for `W ∈ C_c^∞((−1,1))`, `W ≥ 0`, on Theorem S's range,
`∫ W(s−s₀) Ring(s) ds ≤ C ‖W‖_{C^A} (log K + 2) [T 𝔷 + Σ_{r≤R₁} r E′(r,Δ_r) + (T²KR₁/Q + T)]`:
`T𝔷` = Proposition Z's zero pairs summed with the weight `r/φ(r)` (at most `φ(r)` primitive `χ` mod `r`);
`Σ r E′` = its Weil-form error (L7_5 R2.1, `EerrW`); `T²KR₁/Q` = Lemma 5c(1) (prime powers); `T` = the principal-arc
term `2(log K + 1.4708)U` of Lemma ⋆ with `∫W ≤ 2‖W‖_{C^A}` (`log K + 1.4708 ≤ log K + 2`).
Inputs: A⋆ (`ring_le_primitive`, L7_6), 5c(1) (not formalised), 5c(4) (positivity), Z5a (proved), `propZ_W` (L7_5,
8 leaves), Fubini for `∫ds Σ_r Σ_χ ∫dβ`, the Poisson step `M ↦ M̃_s` (`O(N^{−m})`), the `R₁`-monotonicity of Ring.
Difficulty: M (bookkeeping on top of the inputs).
DROP-IN (L7_5b, 1 Oct 2026, for `ZetaShell/Skeleton/L10_S1.lean`): statement unchanged (byte-identical to the library's
at green 1d7f91a); the body is `S1_ring_to_zeros_of_astar` (ShellS/S1_FromZ) applied to `astarCorr_of_L76`
(ShellS/S1_AstarLink), so the only sorry-leaf is A⋆ `ring_le_primitive_corr` (Skeleton/Astar_Corr, L7_6, open).
-/
import ZetaShell.ShellS.L10_Defs
import ZetaShell.ShellS.S1_FromZ
import ZetaShell.ShellS.S1_AstarLink

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem S1_ring_to_zeros (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (A : ℕ) (hA : 2 ≤ A)
    (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (αp B : ℝ) (hα1 : 1 < αp) (hα2 : αp < 2) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      ∀ W : ℝ → ℝ, AvgWeight W →
        Integrable (fun s => W (s - s₀) * RingS Qn (twin Qn r0 ε0) κ Ξ K ε s₀ s) ∧
        (∫ s, W (s - s₀) * RingS Qn (twin Qn r0 ε0) κ Ξ K ε s₀ s)
          ≤ C * normCA W A * (Real.log K + 2) *
            (twin Qn r0 ε0 * zeroPairSum Qn (twin Qn r0 ε0) K ε s₀ A 3
              + famErrSum Qn (twin Qn r0 ε0) K ε s₀
              + (twin Qn r0 ε0 ^ 2 * K * (R1S Qn ε s₀ : ℝ) / Qn + twin Qn r0 ε0)) :=
  S1_ring_to_zeros_of_astar astarCorr_of_L76 κ hκ hκ1 Ξ hΞ A hA r0 ε0 hr0 hε0 αp B hα1 hα2 hB

end ShellS
end ZetaShell
