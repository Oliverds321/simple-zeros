/-
Node N2 (NEW statement, L4_1, 28 Sep 2026) — the one numeric input of lem:sigd-tight used by thm:sigd-OLL
(sec_zeta.tex l.1316: "k_ψ(3/4) = 0.3556941746…", certified in Arb in the draft): a crude rational lower bound suffices,
  "k_ψ(3/4) ≥ 1/4"  for ψ = cos 1.6s.
Closed form: with c₁ = 3π/2 − 8/5, c₂ = 3π/2 + 8/5,
  ∫_{−1/2}^{1/2} cos(8s/5) cos(3πs/2) ds = sin(c₁/2)/c₁ + sin(c₂/2)/c₂,   ∫_{−1/2}^{1/2} cos(8s/5) ds = (5/4) sin(4/5),
and sin(c₁/2) = cos(π/4 − 4/5) ≥ 0.99, sin(c₂/2) = sin(π/4 − 4/5) ≥ −1/50, c₁ ≤ 16/5, c₂ ≥ 6, 0 < (5/4) sin(4/5) ≤ 1
(3.14 < π < 3.15). Value 0.35569417… [C, L4_1 numtest_A7.py; draft l.1316]; the bound proved here is ≥ 0.306 · (1/Den).
Proof: fundamental theorem of calculus with explicit antiderivatives; no numerics beyond Mathlib's π bounds. Level A.
-/
import ZetaS.Interfaces
import Mathlib.Analysis.Real.Pi.Bounds

open Real intervalIntegral

namespace ZetaS

namespace N2

lemma hasDerivAt_sin_div {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => Real.sin (c * s) / c) (Real.cos (c * s)) s := by
  have h := ((hasDerivAt_id' s).const_mul c).sin.div_const c
  refine h.congr_deriv ?_
  field_simp

lemma den_eq : ∫ s in (-(1 / 2 : ℝ))..(1 / 2), psiCos16 s = 5 / 4 * Real.sin (4 / 5) := by
  have hd : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2),
      HasDerivAt (fun s => Real.sin (8 / 5 * s) / (8 / 5)) (psiCos16 x) x := by
    intro x _; unfold psiCos16; exact hasDerivAt_sin_div (by norm_num) x
  have hi : IntervalIntegrable psiCos16 MeasureTheory.volume (-(1 / 2 : ℝ)) (1 / 2) :=
    (by unfold psiCos16; fun_prop : Continuous psiCos16).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hd hi]
  have e1 : (8 / 5 : ℝ) * (1 / 2) = 4 / 5 := by norm_num
  have e2 : (8 / 5 : ℝ) * (-(1 / 2)) = -(4 / 5) := by norm_num
  simp only [e1, e2, Real.sin_neg]
  ring

lemma num_eq :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), psiCos16 s * Real.cos (2 * Real.pi * (3 / 4) * s)
      = Real.sin ((2 * Real.pi * (3 / 4) - 8 / 5) * (1 / 2)) / (2 * Real.pi * (3 / 4) - 8 / 5)
        + Real.sin ((2 * Real.pi * (3 / 4) + 8 / 5) * (1 / 2)) / (2 * Real.pi * (3 / 4) + 8 / 5) := by
  set c₁ : ℝ := 2 * Real.pi * (3 / 4) - 8 / 5 with hc₁
  set c₂ : ℝ := 2 * Real.pi * (3 / 4) + 8 / 5 with hc₂
  have hp := Real.pi_gt_d2
  have hc₁0 : c₁ ≠ 0 := by rw [hc₁]; nlinarith
  have hc₂0 : c₂ ≠ 0 := by rw [hc₂]; nlinarith
  have hd : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2),
      HasDerivAt (fun s => (Real.sin (c₁ * s) / c₁ + Real.sin (c₂ * s) / c₂) / 2)
        (psiCos16 x * Real.cos (2 * Real.pi * (3 / 4) * x)) x := by
    intro x _
    have h := ((hasDerivAt_sin_div hc₁0 x).add (hasDerivAt_sin_div hc₂0 x)).div_const 2
    refine h.congr_deriv ?_
    unfold psiCos16
    have ea : c₁ * x = 2 * Real.pi * (3 / 4) * x - 8 / 5 * x := by rw [hc₁]; ring
    have eb : c₂ * x = 2 * Real.pi * (3 / 4) * x + 8 / 5 * x := by rw [hc₂]; ring
    rw [ea, eb, Real.cos_sub, Real.cos_add]
    ring
  have hi : IntervalIntegrable (fun x => psiCos16 x * Real.cos (2 * Real.pi * (3 / 4) * x))
      MeasureTheory.volume (-(1 / 2 : ℝ)) (1 / 2) :=
    (by unfold psiCos16; fun_prop : Continuous fun x => psiCos16 x * Real.cos (2 * Real.pi * (3 / 4) * x)).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hd hi]
  have e1 : c₁ * (-(1 / 2)) = -(c₁ * (1 / 2)) := by ring
  have e2 : c₂ * (-(1 / 2)) = -(c₂ * (1 / 2)) := by ring
  simp only [e1, e2, Real.sin_neg]
  ring

end N2

theorem kPsi_cos16_three_quarters : 1 / 4 ≤ kPsi psiCos16 (3 / 4) := by
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  unfold kPsi
  rw [N2.num_eq, N2.den_eq]
  set y : ℝ := Real.pi / 4 - 4 / 5 with hy
  have hy1 : -(3 / 200 : ℝ) ≤ y := by rw [hy]; norm_num at hp1 ⊢; linarith
  have hy2 : y ≤ 0 := by rw [hy]; norm_num at hp2 ⊢; linarith
  -- sin(c₁/2) = cos y ≥ 99/100
  have ha : Real.sin ((2 * Real.pi * (3 / 4) - 8 / 5) * (1 / 2)) = Real.cos y := by
    rw [← Real.sin_add_pi_div_two]; congr 1; rw [hy]; ring
  have hcos : (99 / 100 : ℝ) ≤ Real.cos y := by
    have := Real.one_sub_sq_div_two_le_cos (x := y)
    nlinarith
  -- sin(c₂/2) = sin y ≥ y ≥ −3/200
  have hb : Real.sin ((2 * Real.pi * (3 / 4) + 8 / 5) * (1 / 2)) = Real.sin y := by
    rw [← Real.sin_pi_sub]; congr 1; rw [hy]; ring
  have hsin : -(3 / 200 : ℝ) ≤ Real.sin y := by
    have h := Real.sin_le (x := -y) (by linarith)
    rw [Real.sin_neg] at h
    linarith
  rw [ha, hb]
  set c₁ : ℝ := 2 * Real.pi * (3 / 4) - 8 / 5 with hc₁
  set c₂ : ℝ := 2 * Real.pi * (3 / 4) + 8 / 5 with hc₂
  have hc₁0 : 0 < c₁ := by rw [hc₁]; nlinarith
  have hc₁1 : c₁ ≤ 16 / 5 := by rw [hc₁]; nlinarith
  have hc₂0 : 6 ≤ c₂ := by rw [hc₂]; nlinarith
  have h1 : 99 / 320 ≤ Real.cos y / c₁ := by
    rw [le_div_iff₀ hc₁0]; nlinarith
  have h2 : -(1 / 300 : ℝ) ≤ Real.sin y / c₂ := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  -- the denominator
  have hs0 : 0 < Real.sin (4 / 5) := Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith)
  have hs1 : Real.sin (4 / 5) ≤ 4 / 5 := Real.sin_le (by norm_num)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end ZetaS
