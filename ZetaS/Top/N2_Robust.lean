/-
Node N2 (track T, numerics; NEW statement by L3_2, 28 Sep 2026) — the robustness conditions of rem:sigd-robust
(sec_zeta.tex l.1468–1478) for all-marks claims (a₁, a₂, ν) and a majorant threshold β, and the value
k_ψ(3/4) = 0.3556941746… (lem:sigd-tight, l.1316) for ψ = cos 1.6s.

Draft: "The chain uses the claims (a₁,a₂,ν) only through: an (LI_m) certificate for them; c* = 2 − 2a₁ > (2β₀ + 4β* − 2)²
(Lemma sigd-env); μ(k_ψ(3/4)) ≥ max(a₁,a₂) (Lemma sigd-tight); and the positivity of the table in the proof above."

`RobustAM a₁ a₂ ν β` packages exactly these. The majorant enters through its threshold β (`MajorantCert ψ β` asserts
2β₀ + 4β* < β), so the chain's condition is β < λ_c = 2 + √c*. Added: the sign conditions a₁, a₂, ν ≥ 0 that
lem:sigd-tight needs (L2_2's A6 counterexample), and the positivity of the two denominators of Step 4. μ(k_ψ(3/4)) is
required STRICTLY above max(a₁, a₂), so that k* = k_ψ(3/4) − ε_T works for small ε_T.
Proved for the K = 5 and K = 7 data, with β = 33/10 (L2_2's restated threshold) and with the architect's
β = 32063638853/10¹⁰.

The value of k_ψ(3/4): closed form (after L4_1's `N2_KPsiThreeQuarters`, re-derived here) with t := 4/5 − π/4,
  k_ψ(3/4) = (cos t/(16/5 − 6t) − sin t/(32/5 − 6t)) / ((5/4) sin(4/5)),
Mathlib's π ∈ (3.14159265358979323846, …847), `Real.cos_bound`, `Real.sin_bound` (0 ≤ t ≤ 0.0147) and L0_2's
`CosWindow.sin_four_fifths` (width 10⁻¹⁸): 0.35569417 ≤ k_ψ(3/4) ≤ 0.35569418. Level A.
-/
import ZetaS.Interfaces
import ZetaS.Window.CosWindow
import Mathlib.Analysis.Real.Pi.Bounds

open Real intervalIntegral

namespace ZetaS

namespace N2r

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

lemma num_eq (c₁ c₂ : ℝ) (hc₁ : c₁ = 2 * Real.pi * (3 / 4) - 8 / 5) (hc₂ : c₂ = 2 * Real.pi * (3 / 4) + 8 / 5)
    (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0) :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), psiCos16 s * Real.cos (2 * Real.pi * (3 / 4) * s)
      = Real.sin (c₁ * (1 / 2)) / c₁ + Real.sin (c₂ * (1 / 2)) / c₂ := by
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
    (by unfold psiCos16; fun_prop :
      Continuous fun x => psiCos16 x * Real.cos (2 * Real.pi * (3 / 4) * x)).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hd hi]
  have e1 : c₁ * (-(1 / 2)) = -(c₁ * (1 / 2)) := by ring
  have e2 : c₂ * (-(1 / 2)) = -(c₂ * (1 / 2)) := by ring
  simp only [e1, e2, Real.sin_neg]
  ring

/-- closed form in `t = 4/5 − π/4`. -/
lemma kPsi_34_eq :
    kPsi psiCos16 (3 / 4) = (Real.cos (4 / 5 - π / 4) / (16 / 5 - 6 * (4 / 5 - π / 4))
      - Real.sin (4 / 5 - π / 4) / (32 / 5 - 6 * (4 / 5 - π / 4))) / (5 / 4 * Real.sin (4 / 5)) := by
  have hp := Real.pi_gt_d2
  unfold kPsi
  rw [num_eq (2 * Real.pi * (3 / 4) - 8 / 5) (2 * Real.pi * (3 / 4) + 8 / 5) rfl rfl
    (by nlinarith) (by nlinarith), den_eq]
  congr 1
  have h1 : (2 * π * (3 / 4) - 8 / 5) * (1 / 2) = π / 2 - (4 / 5 - π / 4) := by ring
  have h5 : Real.sin ((2 * π * (3 / 4) + 8 / 5) * (1 / 2)) = -Real.sin (4 / 5 - π / 4) := by
    rw [show (2 * π * (3 / 4) + 8 / 5) * (1 / 2) = π - (-(4 / 5 - π / 4)) by ring, Real.sin_pi_sub,
      Real.sin_neg]
  have h3 : 2 * π * (3 / 4) - 8 / 5 = 16 / 5 - 6 * (4 / 5 - π / 4) := by ring
  have h4 : 2 * π * (3 / 4) + 8 / 5 = 32 / 5 - 6 * (4 / 5 - π / 4) := by ring
  rw [h1, Real.sin_pi_div_two_sub, h5, h3, h4]
  ring

end N2r

set_option maxHeartbeats 2000000 in
/-- **k_ψ(3/4) for ψ = cos 1.6s**: `0.35569417 ≤ k_ψ(3/4) ≤ 0.35569418` (draft: 0.3556941746…). -/
theorem kPsi_cos16_34_bounds :
    (35569417 : ℝ) / 10 ^ 8 ≤ kPsi psiCos16 (3 / 4) ∧ kPsi psiCos16 (3 / 4) ≤ 35569418 / 10 ^ 8 := by
  rw [N2r.kPsi_34_eq]
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  obtain ⟨s1, s2⟩ := CosWindow.sin_four_fifths
  set t₁ : ℝ := 4 / 5 - 3.14159265358979323847 / 4 with ht₁
  set t₂ : ℝ := 4 / 5 - 3.14159265358979323846 / 4 with ht₂
  set t := 4 / 5 - π / 4 with ht
  have ht1 : t₁ ≤ t := by rw [ht, ht₁]; linarith
  have ht2 : t ≤ t₂ := by rw [ht, ht₂]; linarith
  have ht₁0 : 0 ≤ t₁ := by rw [ht₁]; norm_num
  have ht0 : 0 ≤ t := le_trans ht₁0 ht1
  have ht₂1 : t₂ ≤ 1 := by rw [ht₂]; norm_num
  have ht1' : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  have hc := Real.cos_bound ht1'
  have hs := Real.sin_bound ht1'
  rw [abs_of_nonneg ht0] at hc hs
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  have e2a : t₁ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ht₁0 ht1 2
  have e2b : t ^ 2 ≤ t₂ ^ 2 := pow_le_pow_left₀ ht0 ht2 2
  have e3a : t₁ ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ ht₁0 ht1 3
  have e3b : t ^ 3 ≤ t₂ ^ 3 := pow_le_pow_left₀ ht0 ht2 3
  have e4 : t ^ 4 ≤ t₂ ^ 4 := pow_le_pow_left₀ ht0 ht2 4
  have e5 : t ^ 5 ≤ t₂ ^ 5 := pow_le_pow_left₀ ht0 ht2 5
  have e40 : 0 ≤ t ^ 4 := by positivity
  have e50 : 0 ≤ t ^ 5 := by positivity
  set C := Real.cos t with hC
  set S := Real.sin t with hS
  clear_value C S t t₁ t₂
  have C1 : 1 - t₂ ^ 2 / 2 - t₂ ^ 4 * (5 / 96) ≤ C := by linarith
  have C2 : C ≤ 1 - t₁ ^ 2 / 2 + t₂ ^ 4 * (5 / 96) := by linarith
  have S1 : t₁ - t₂ ^ 3 / 6 - t₂ ^ 5 / 100 ≤ S := by linarith
  have S2 : S ≤ t₂ - t₁ ^ 3 / 6 + t₂ ^ 5 / 100 := by linarith
  have hd₁ : 0 < 16 / 5 - 6 * t₂ := by rw [ht₂]; norm_num
  have hd₂ : 0 < 32 / 5 - 6 * t₂ := by rw [ht₂]; norm_num
  have d₁pos : 0 < 16 / 5 - 6 * t := by linarith
  have d₂pos : 0 < 32 / 5 - 6 * t := by linarith
  have hC0 : 0 ≤ 1 - t₂ ^ 2 / 2 - t₂ ^ 4 * (5 / 96) := by rw [ht₂]; norm_num
  have hC0' : 0 ≤ 1 - t₁ ^ 2 / 2 + t₂ ^ 4 * (5 / 96) := by rw [ht₁, ht₂]; norm_num
  have hS0 : 0 ≤ t₁ - t₂ ^ 3 / 6 - t₂ ^ 5 / 100 := by rw [ht₁, ht₂]; norm_num
  have hS0' : 0 ≤ t₂ - t₁ ^ 3 / 6 + t₂ ^ 5 / 100 := by rw [ht₁, ht₂]; norm_num
  have q1a : (1 - t₂ ^ 2 / 2 - t₂ ^ 4 * (5 / 96)) / (16 / 5 - 6 * t₁) ≤ C / (16 / 5 - 6 * t) :=
    le_trans (div_le_div_of_nonneg_left hC0 d₁pos (by linarith))
      (div_le_div_of_nonneg_right C1 d₁pos.le)
  have q1b : C / (16 / 5 - 6 * t) ≤ (1 - t₁ ^ 2 / 2 + t₂ ^ 4 * (5 / 96)) / (16 / 5 - 6 * t₂) :=
    le_trans (div_le_div_of_nonneg_right C2 d₁pos.le) (div_le_div_of_nonneg_left hC0' hd₁ (by linarith))
  have q2a : (t₁ - t₂ ^ 3 / 6 - t₂ ^ 5 / 100) / (32 / 5 - 6 * t₁) ≤ S / (32 / 5 - 6 * t) :=
    le_trans (div_le_div_of_nonneg_left hS0 d₂pos (by linarith))
      (div_le_div_of_nonneg_right S1 d₂pos.le)
  have q2b : S / (32 / 5 - 6 * t) ≤ (t₂ - t₁ ^ 3 / 6 + t₂ ^ 5 / 100) / (32 / 5 - 6 * t₂) :=
    le_trans (div_le_div_of_nonneg_right S2 d₂pos.le) (div_le_div_of_nonneg_left hS0' hd₂ (by linarith))
  have hD : 0 < 5 / 4 * Real.sin (4 / 5) := by linarith
  constructor
  · rw [le_div_iff₀ hD]
    have hlow : (1 - t₂ ^ 2 / 2 - t₂ ^ 4 * (5 / 96)) / (16 / 5 - 6 * t₁)
        - (t₂ - t₁ ^ 3 / 6 + t₂ ^ 5 / 100) / (32 / 5 - 6 * t₂) ≤ C / (16 / 5 - 6 * t) - S / (32 / 5 - 6 * t) := by
      linarith
    refine le_trans ?_ hlow
    have hval : (35569417 : ℝ) / 10 ^ 8 * (5 / 4 * 0.717356090899522762) ≤
        (1 - t₂ ^ 2 / 2 - t₂ ^ 4 * (5 / 96)) / (16 / 5 - 6 * t₁)
          - (t₂ - t₁ ^ 3 / 6 + t₂ ^ 5 / 100) / (32 / 5 - 6 * t₂) := by
      rw [ht₁, ht₂]; norm_num
    linarith
  · rw [div_le_iff₀ hD]
    have hup : C / (16 / 5 - 6 * t) - S / (32 / 5 - 6 * t) ≤ (1 - t₁ ^ 2 / 2 + t₂ ^ 4 * (5 / 96)) / (16 / 5 - 6 * t₂)
        - (t₁ - t₂ ^ 3 / 6 - t₂ ^ 5 / 100) / (32 / 5 - 6 * t₁) := by
      linarith
    refine le_trans hup ?_
    have hval : (1 - t₁ ^ 2 / 2 + t₂ ^ 4 * (5 / 96)) / (16 / 5 - 6 * t₂)
          - (t₁ - t₂ ^ 3 / 6 - t₂ ^ 5 / 100) / (32 / 5 - 6 * t₁)
        ≤ (35569418 : ℝ) / 10 ^ 8 * (5 / 4 * 0.717356090899522761) := by
      rw [ht₁, ht₂]; norm_num
    linarith

/-! ### The robustness conditions -/

/-- `μ(k)` of lem:sigd-tight (l.1301). Equal (up to `min_assoc`) to L2_2s `ZetaS.muTight` in `A6_TightChains.lean`; renamed to avoid the clash. -/
noncomputable def muChain (a₁ a₂ k : ℝ) : ℝ :=
  min (2 * k ^ 2 - 2 * a₁) (min (4 * k ^ 2 - 2 * a₂) ((1 / 2 + Real.sqrt (1 / 4 + 2 * k ^ 2)) ^ 2 - 1 - a₁ - a₂))

/-- **Robustness conditions** of rem:sigd-robust for all-marks claims `(a₁, a₂, ν)` and majorant threshold `β`
(`MajorantCert psiCos16 β`). With `c* = 2 − 2a₁`. -/
structure RobustAM (a₁ a₂ ν β : ℝ) : Prop where
  a₁_nonneg : 0 ≤ a₁
  a₂_nonneg : 0 ≤ a₂
  ν_nonneg : 0 ≤ ν
  /-- `c* = 2 − 2a₁ > 0` (the draft's `c* > (2β₀ + 4β* − 2)² ≥ 0`; `kappaCh c* 0 = 0` needs `c* ≥ 0`) -/
  cstar_pos : 0 < 2 - 2 * a₁
  /-- lem:sigd-env: `β < λ_c = 2 + √c*` (⇔ `(β − 2)² < c*` for `β ≥ 2`) -/
  beta_lt : β < 2 + Real.sqrt (2 - 2 * a₁)
  /-- lem:sigd-tight: `μ(k_ψ(3/4)) > max(a₁, a₂)` -/
  tight : max a₁ a₂ < muChain a₁ a₂ (kPsi psiCos16 (3 / 4))
  /-- Step 3 table, pairs of multiplicity `m ≥ 2` (`Nˢ`, `N^d`) -/
  pair_s : ∀ m : ℕ, 2 ≤ m → 0 ≤ (4 - a₂) * m - 4 - (2 - 2 * a₁)
  pair_d : ∀ m : ℕ, 2 ≤ m → 0 ≤ 2 * m * (1 - a₂ + a₁) - 4 * a₁ + 2 * a₂ - (2 - 2 * a₁)
  /-- Step 3 table, heavy on-line sites `m ≥ 3` (`Nˢ`, `N^d`) -/
  heavy_s : ∀ m : ℕ, 3 ≤ m → 0 ≤ (2 - a₂ / 2) * m - 4
  heavy_d : ∀ m : ℕ, 3 ≤ m → 0 ≤ m * (1 - a₂ + a₁) - 2 - 2 * a₁ + a₂
  /-- Step 4 denominators -/
  den_s : 0 < 1 - a₁ + a₂ / 2
  den_d : 0 < 2 - 2 * a₁ + a₂

/-- `33/10 < λ_c = 2 + √(2 − 2a₁)` for small claims (`λ_c = 3.40125…` at K = 7, `3.40513…` at K = 5). -/
theorem thirtythree_lt_lambdaC {a₁ : ℝ} (h1' : a₁ ≤ 1 / 40) : (33 / 10 : ℝ) < 2 + Real.sqrt (2 - 2 * a₁) := by
  have hsq : (135 / 100 : ℝ) ≤ Real.sqrt (2 - 2 * a₁) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  linarith

/-- the generic check: small claims, `k_ψ(3/4) ≥ 0.3556`, and any threshold `β < λ_c`. -/
theorem robustAM_of_small {a₁ a₂ ν β : ℝ} (h1 : 0 ≤ a₁) (h1' : a₁ ≤ 1 / 40) (h2 : 0 ≤ a₂) (h2' : a₂ ≤ 1 / 40)
    (hν : 0 ≤ ν) (hβ : β < 2 + Real.sqrt (2 - 2 * a₁)) : RobustAM a₁ a₂ ν β := by
  have hk := (kPsi_cos16_34_bounds).1
  set k := kPsi psiCos16 (3 / 4)
  have hk0 : (3556 : ℝ) / 10000 ≤ k := by linarith
  have hk2 : (3556 : ℝ) / 10000 * (3556 / 10000) ≤ k ^ 2 := by nlinarith
  have hsq2 : (70 / 100 : ℝ) ≤ Real.sqrt (1 / 4 + 2 * k ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  refine ⟨h1, h2, hν, by linarith, hβ, ?_, ?_, ?_, ?_, ?_, by linarith, by linarith⟩
  · unfold muChain
    have hm : max a₁ a₂ ≤ 1 / 40 := max_le h1' h2'
    refine lt_min (by nlinarith) (lt_min (by nlinarith) ?_)
    have h3 : (1 / 2 + 70 / 100 : ℝ) ^ 2 ≤ (1 / 2 + Real.sqrt (1 / 4 + 2 * k ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    nlinarith
  · intro m hm
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  · intro m hm
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  · intro m hm
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  · intro m hm
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- **N2, K = 7** (rem:sigd-cert, K = 7 row), any majorant threshold `β < λ_c`. -/
theorem robust_K7 {β : ℝ} (hβ : β < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8))) :
    RobustAM (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) β :=
  robustAM_of_small (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hβ

/-- **N2, K = 5** (X2's certificate, thm:zeta-allmarks), any majorant threshold `β < λ_c`. -/
theorem robust_K5 {β : ℝ} (hβ : β < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8))) :
    RobustAM (1280197 / 10 ^ 8) (48749 / 3125000) (1 / 125) β :=
  robustAM_of_small (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hβ

/-- L2_2's restated threshold `33/10` and the architect's `CertMaj` threshold are below `λ_c` (K = 7 and K = 5). -/
theorem beta33_lt_K7 : (33 / 10 : ℝ) < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8)) :=
  thirtythree_lt_lambdaC (by norm_num)
theorem beta33_lt_K5 : (33 / 10 : ℝ) < 2 + Real.sqrt (2 - 2 * (1280197 / 10 ^ 8)) :=
  thirtythree_lt_lambdaC (by norm_num)
theorem certMaj_lt_K7 : (32063638853 / 10 ^ 10 : ℝ) < 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8)) :=
  lt_trans (by norm_num) beta33_lt_K7

end ZetaS
