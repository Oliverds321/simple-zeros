/-
Node AS (L7_10): **the pointwise assembly** (eq:shell-assembly, sec_shell.tex l.880–895), with the two lines that
follow it ("By Lemma 4 and `‖a‖² = U(s+O(1))`, `‖a‖² − Hole ≤ U(ℒ + log K + O(1))`"), at the draft's choices of
ssec:shell-rate: `K = ℒ(log ℒ)²`, `ε = 1/ℒ` (sharp family `𝔉_Q`).
Draft: "Let `log Q + 4 ≤ s ≤ (2−η)log Q` and `S = S^{near,P}`. […]
`F(s) ≤ (1+η₀)[|𝔉_Q|(1+E_g)(‖a‖² − Hole − Ring) + Q²(1+o(1))(Ring + Edge) + 2π sinh κ(εQ² + N)‖a‖²]
 + (1+η₀⁻¹) C|𝔉_Q| O((κT)⁻¹ + (δ₁²T log Q)⁻¹)‖a‖²`."
Lean form: the `−Ring` inside the first bracket is dropped (it only helps), `Edge = o(‖a‖²)` (AF1), `E_g`, `η₀`,
`ε sinh κ`, `N/Q²`, Lemma 1′'s costs are collected in `C·log ℒ/ℒ` relative to `|𝔉_Q|‖a‖²` (the elementary rate of
ssec:shell-rate, `(1+log K)³/K ≍ log ℒ/ℒ` at `K = ℒ(log ℒ)²`), and the Hole is used through Lemma 4's lower bound:
`F(s) ≤ |𝔉_Q|·(T/2π)(ℒ + log K + C) + Q²(1 + C log ℒ/ℒ)·Ring(s) + C (log ℒ/ℒ)|𝔉_Q|·‖a(s)‖²`,
with `Ring(s)` at the draft's pointwise `R₁ = e^s(log Q)⁶/(εQ)` (= `R1S Q ε (s−1)`).
Hypothesis added (L7_6's correction to Lemma 1′): `Ξ = 1` on `[−c, c]`.
Inputs: A1 (signed Farey identity, L7_6), A1′ (L7_6), A2 (Lemma 2 (a),(b),(c); L7_8: (b),(c) proved, (a) five leaves),
A3 (signed Gallagher, L7_6 draft), AF1 (hole-edge mass, L7_6 proved), A4 (hole lower bound, Lemma K's K3–K6 with
`PNTMedium`), the PNT upper bound `‖a‖² ≤ U(s + C)` (medium form, a theorem). Tao's inequality `|Ω| ≤ 1`, or
L7_8's "ring points have `q > Q/K`" step. Difficulty: M (bookkeeping on top of the inputs).
-/
import ZetaShell.ShellS.L10_Defs

noncomputable section

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem AS_pointwise (lam : ℝ) (hl1 : 1 < lam) (hl2 : lam < 2) (αpp : ℝ) (hαpp : αpp < 2)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (c : ℝ) (hc : 0 < c)
    (hΞc : ∀ z, |z| ≤ c → Ξ z = 1) (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ s : ℝ, Real.log Qn + 4 ≤ s → s ≤ αpp * Real.log Qn →
      TrackF.famF (Finset.Icc 2 Qn) ⌊XlamS lam Qn (twin Qn r0 ε0)⌋₊ (TrackF.acoefS (twin Qn r0 ε0) s)
        ≤ famSize Qn * (twin Qn r0 ε0 / (2 * Real.pi))
            * (LcS Qn (twin Qn r0 ε0) + Real.log (Kstd Qn (twin Qn r0 ε0)) + C)
          + (Qn : ℝ) ^ 2 * (1 + C * (Real.log (LcS Qn (twin Qn r0 ε0)) / LcS Qn (twin Qn r0 ε0)))
            * RingS Qn (twin Qn r0 ε0) κ Ξ (Kstd Qn (twin Qn r0 ε0)) (1 / LcS Qn (twin Qn r0 ε0)) (s - 1) s
          + C * (Real.log (LcS Qn (twin Qn r0 ε0)) / LcS Qn (twin Qn r0 ε0)) * famSize Qn
            * l2S ⌊XlamS lam Qn (twin Qn r0 ε0)⌋₊ (twin Qn r0 ε0) s := by
  sorry

/-- **Ring monotonicity** (used by the transfer: the pointwise `R₁(s) = R1S Q ε (s−1)` is at most the window's
`R1S Q ε s₀` for `s ≤ s₀ + 1`, and Ring is monotone in `R₁`). Difficulty E. -/
theorem ringMass_mono (Q N : ℕ) (K : ℝ) (a : ℕ → ℂ) {R R' : ℕ} (h : R ≤ R') :
    TrackF.ringMass Q R N K a ≤ TrackF.ringMass Q R' N K a := by
  unfold TrackF.ringMass
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
  intro r _ _
  exact Finset.sum_nonneg fun b _ => MeasureTheory.integral_nonneg fun β => sq_nonneg _

theorem R1S_mono (Q ε : ℝ) (hQ : 0 < Q) (hε : 0 < ε) {s t : ℝ} (h : s ≤ t) : R1S Q ε s ≤ R1S Q ε t := by
  unfold R1S
  apply Nat.floor_le_floor
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)

end ShellS
end ZetaShell
