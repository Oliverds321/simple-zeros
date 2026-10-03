/-
**Theorem S (the Shell Lemma, s-averaged)** (thm:shell-S, sec_shell.tex l.848–873), (D1′) instantiation, L7_10.
Draft: "Assume (B) and (LF), fix `1 < α′ < α₀` and `W` as above, and let `K → ∞` with `log K ≪ log log Q`. Then,
uniformly for `log Q + 3 ≤ s₀ ≤ α′ log Q`, `∫W(s−s₀)Ring(s)ds ≤ η_Q ∫W(s−s₀)‖a(s)‖²ds`,
`η_Q ≪ log K/log Q + (log log Q)^{O(1)}(log Q)^{−θ(α′)} + Q^{−c}`. The implied constants depend on `W` only through
`‖W‖_{C^A}`."
Lean form (changes, see the report): (i) `∫W‖a‖² ≍ Ts₀` is replaced by `T s₀` itself, and the `W`-dependence is the
explicit factor `‖W‖_{C^A}` (what the transfer to `g` needs: `‖W_j‖_{C^A} ≪ g(j)`); (ii) the rate is stated as
`(log Q)^{−θ}` for every `θ < θ(α′)` (absorbs `log K/log Q`, `(log log Q)^{O(1)}`, `Q^{−c}`); (iii) `ε` (which fixes
`R₁`) is explicit, `(log Q)^{−B} ≤ ε ≤ 1`; (iv) the only classical hypothesis is `ZeroDensityInput`.
THIS FILE: Theorem S DERIVED from the nodes S1–S4 (sorry only in those nodes).
-/
import ZetaShell.Skeleton.L10_S1
import ZetaShell.ShellS.L12c_S2
import ZetaShell.ShellS.L12_S3
import ZetaShell.ShellS.L10_S4

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem thetaD1p_le_one (αp : ℝ) : thetaD1p αp ≤ 1 := min_le_left _ _

theorem shell_S (hD : ZeroDensityInput) (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (A : ℕ) (hA : 2 ≤ A)
    (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (B θ : ℝ) (hB : 1 ≤ B) (hθ : θ < thetaD1p αp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      ∀ W : ℝ → ℝ, AvgWeight W →
        Integrable (fun s => W (s - s₀) * RingS Qn (twin Qn r0 ε0) κ Ξ K ε s₀ s) ∧
        (∫ s, W (s - s₀) * RingS Qn (twin Qn r0 ε0) κ Ξ K ε s₀ s)
          ≤ C * normCA W A * Real.log Qn ^ (-θ) * (twin Qn r0 ε0 * s₀) := by
  have hα2' : αp < 2 := by linarith
  have hθ1 : θ < 1 := lt_of_lt_of_le hθ (thetaD1p_le_one αp)
  obtain ⟨C1, hC1, h1⟩ := S1_ring_to_zeros κ hκ hκ1 Ξ hΞ A hA r0 ε0 hr0 hε0 αp B hα1 hα2' hB
  obtain ⟨C2, hC2, h2⟩ := S2_zero_side hD αp hα1 hα2 A hA r0 ε0 hr0 hε0 B θ hB hθ
  obtain ⟨C3, hC3, h3⟩ := S3_family_errors αp hα1 hα2' r0 ε0 hr0 hε0 B θ hB
  obtain ⟨C4, hC4, h4⟩ := S4_elementary αp hα1 hα2' r0 ε0 hr0 hε0 B θ hB hθ1
  refine ⟨C1 * (C2 + C3 + C4), mul_nonneg hC1 (by linarith), ?_⟩
  filter_upwards [h1, h2, h3, h4] with Qn e1 e2 e3 e4
  intro K ε s₀ hR W hW
  obtain ⟨hint, hb⟩ := e1 K ε s₀ hR W hW
  refine ⟨hint, ?_⟩
  have b2 := e2 K ε s₀ hR
  have b3 := e3 K ε s₀ hR
  have b4 := e4 K ε s₀ hR
  set T := twin (Qn : ℝ) r0 ε0
  set Z := zeroPairSum Qn T K ε s₀ A 3
  set E := famErrSum Qn T K ε s₀
  set P := T ^ 2 * K * (R1S Qn ε s₀ : ℝ) / Qn + T
  set r := Real.log Qn ^ (-θ)
  set nW := normCA W A
  have hnW : 0 ≤ nW := normCA_nonneg' W A
  have hsum : (Real.log K + 2) * (T * Z + E + P) ≤ (C2 + C3 + C4) * r * (T * s₀) := by
    have hsplit : (Real.log K + 2) * (T * Z + E + P)
        = (Real.log K + 2) * (T * Z) + (Real.log K + 2) * E + (Real.log K + 2) * P := by ring
    rw [hsplit]
    have hr3 : (C2 + C3 + C4) * r * (T * s₀)
        = C2 * r * (T * s₀) + C3 * r * (T * s₀) + C4 * r * (T * s₀) := by ring
    rw [hr3]
    linarith [b2, b3, b4]
  calc (∫ s, W (s - s₀) * RingS Qn T κ Ξ K ε s₀ s)
      ≤ C1 * nW * (Real.log K + 2) * (T * Z + E + P) := hb
    _ = (C1 * nW) * ((Real.log K + 2) * (T * Z + E + P)) := by ring
    _ ≤ (C1 * nW) * ((C2 + C3 + C4) * r * (T * s₀)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hC1 hnW)
    _ = C1 * (C2 + C3 + C4) * nW * r * (T * s₀) := by ring

end ShellS
end ZetaShell
