/-
F1c-3 (L7_3, round 6): `shell_mertens` DERIVED from `mertens_hsup` (F1c-3b′, open), the tail bound and the family size;
`shell_outDiag` DERIVED from `smear_upper` (proved) and `shell_mertens`. (Split out of `LF_OutDiag.lean` so that
`LF_Mertens.lean` can use its definitions.)
-/
import ZetaShell.ShellK.LF_Mertens

noncomputable section
open scoped BigOperators
open scoped ArithmeticFunction
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

set_option maxHeartbeats 2000000 in
/-- **F1c-3b.** DERIVED from `mertens_hsup` (F1c-3b′), the tail bound (`sumA2Q_le`, A7's `Kℒ² ≤ T`), the family size
(`sizeR_LL_le_NfamQ_shell`) and `KoutShell_bounds`. -/
theorem shell_mertens (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      2 * (Family.qle.sizeR Qn * (1 / (4 * Real.pi ^ 2) * ∑ n ∈ primeRangeQ P,
          (Λ n : ℝ) ^ 2 / (n : ℝ) * (2 * Real.pi * P.T * hsupP P (Real.log (n : ℝ)) + 8 * HP P)))
        ≤ (P.aQ * P.LB) ^ 2 * (KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) + η)
            * NfamQ P Family.qle Qn := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  obtain ⟨c0, hc0def⟩ : ∃ c0 : ℝ, c0 = 1 / 2 + (2 * (Real.log 4 + 4) + 1537 / Real.log 2) / 8 := ⟨_, rfl⟩
  have hc0 : 0 < c0 := by rw [hc0def]; positivity
  have hpi := Real.pi_pos
  have hC0 : (0 : ℝ) < Cfam := by unfold Cfam; positivity
  obtain ⟨KC, hKCdef⟩ : ∃ KC : ℝ, KC = 4 * Cfam + 3 + η := ⟨_, rfl⟩
  have hKC : 0 < KC := by rw [hKCdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (η / (4 * KC)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδη : δ * KC ≤ η / 4 := by
    have h : δ ≤ η / (4 * KC) := by rw [hδdef]; exact min_le_right _ _
    calc δ * KC ≤ η / (4 * KC) * KC := mul_le_mul_of_nonneg_right h hKC.le
      _ = η / 4 := by field_simp
  obtain ⟨Kth, hKthdef⟩ : ∃ Kth : ℝ, Kth = max 1 (256 * c0 * (Cfam + 1) / (3 * Real.pi * η)) := ⟨_, rfl⟩
  have hKth1 : 1 ≤ Kth := by rw [hKthdef]; exact le_max_left _ _
  have hKth2 : 256 * c0 * (Cfam + 1) / (3 * Real.pi * η) ≤ Kth := by rw [hKthdef]; exact le_max_right _ _
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  filter_upwards [mertens_hsup r ε hr hε (η / 4) (by positivity),
    sizeR_LL_le_NfamQ_shell r ε hr hε (η := δ) hδ0 hδ1,
    Design.shellDesign_regime S53L75 hS2 r ε hr hε Kth hKth1, design_basic_shell r ε hr hε] with Qn hM hS hreg hbas
  intro P hdes
  have hP : P.Valid := hdes.1
  obtain ⟨-, -, hKLL, -, -, -, -, -⟩ := hreg P hdes
  obtain ⟨hLL30, hL8, hlam1, hw, hQn2⟩ := hbas P hdes
  have hM1 := hM P hdes
  have hS1 := hS P hdes
  have hSg0 : ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) ≤ c0 * P.LB ^ 2 := by
    rw [hc0def]; exact sumA2Q_le P hL8
  have hSg00 : 0 ≤ ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hKb := KoutShell_bounds (vDesign_admissible hP) hP.lam_lt_two.le (C := Cfam) (αp := 2497 / 1500)
    (a := zoneFactor P) hC0.le (by norm_num)
  obtain ⟨hK0, hK1⟩ := hKb
  -- abbreviations
  set K := KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) with hKdef
  set N := NfamQ P Family.qle Qn with hNdef
  set S := Family.qle.sizeR Qn with hSdef
  set Sg1 := ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * hsupP P (Real.log (n : ℝ)) with hSg1def
  set Sg0 := ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) with hSg0def
  set U := P.T / (2 * Real.pi) with hUdef
  set W := (P.aQ * P.LB) ^ 2 with hWdef
  have hN0 : 0 ≤ N := NfamQ_nonneg P Family.qle Qn
  have hS0 : 0 ≤ S := by rw [hSdef]; unfold Family.sizeR; positivity
  have hW0 : 0 ≤ W := sq_nonneg _
  have hLL0 : 0 < P.LL := by linarith
  have hT0 : 0 < P.T := hP.T_pos
  have hU0 : 0 < U := by rw [hUdef]; positivity
  have ha0 := hP.aQ_pos
  have ha34 : 3 / 4 ≤ P.aQ := hP.a_ge
  have hLB0 := hP.LB_pos
  have hLB2 : P.LB ≤ 2 * P.LL := by
    show P.lam * P.LL ≤ 2 * P.LL
    nlinarith [hP.lam_lt_two]
  -- the sum splits
  have hsplit : ∑ n ∈ primeRangeQ P,
      (Λ n : ℝ) ^ 2 / (n : ℝ) * (2 * Real.pi * P.T * hsupP P (Real.log (n : ℝ)) + 8 * HP P)
      = 2 * Real.pi * P.T * Sg1 + 8 * HP P * Sg0 := by
    rw [hSg1def, hSg0def, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hsplit]
  have e1 : 2 * (S * (1 / (4 * Real.pi ^ 2) * (2 * Real.pi * P.T * Sg1 + 8 * HP P * Sg0)))
      = 2 * S * U * Sg1 + 2 * S * (2 / Real.pi ^ 2 * HP P * Sg0) := by
    rw [hUdef]; field_simp; ring
  rw [e1]
  -- Part A
  have hA : 2 * S * U * Sg1 ≤ N * W * (K + η / 2) := by
    have h1 : 2 * S * U * Sg1 ≤ 2 * S * U * (P.LL * W / 2 * (K + η / 4)) :=
      mul_le_mul_of_nonneg_left hM1 (by positivity)
    have h2 : 2 * S * U * (P.LL * W / 2 * (K + η / 4)) = (S * (U * P.LL)) * (W * (K + η / 4)) := by ring
    have hWK : 0 ≤ W * (K + η / 4) := mul_nonneg hW0 (by linarith)
    have h3 : (S * (U * P.LL)) * (W * (K + η / 4)) ≤ ((1 + δ) * N) * (W * (K + η / 4)) :=
      mul_le_mul_of_nonneg_right hS1 hWK
    have h4 : (1 + δ) * (K + η / 4) ≤ K + η / 2 := by
      have hKle : K + η / 4 ≤ KC := by rw [hKCdef]; linarith
      have := mul_le_mul_of_nonneg_left hKle hδ0.le
      linarith
    have h5 : ((1 + δ) * N) * (W * (K + η / 4)) ≤ N * W * (K + η / 2) := by
      have := mul_le_mul_of_nonneg_left h4 (mul_nonneg hN0 hW0)
      linarith
    linarith
  -- Part B (the tail)
  have hB : 2 * S * (2 / Real.pi ^ 2 * HP P * Sg0) ≤ N * W * (η / 2) := by
    have hHP0 : 0 ≤ HP P := by unfold HP; positivity
    have hX0 : 0 ≤ 2 / Real.pi ^ 2 * HP P * Sg0 := by positivity
    -- `S·U·ℒ ≤ 2N`
    have hSUL : S * (U * P.LL) ≤ 2 * N := by
      have : (1 + δ) * N ≤ 2 * N := by
        have := mul_le_mul_of_nonneg_right hδ1 hN0
        linarith
      linarith
    -- `HP·Sg0 ≤ aL(C+ℒ)·c0·L²`
    have hHS : HP P * Sg0 ≤ P.aQ * P.LB * (Cfam + P.LL) * (c0 * P.LB ^ 2) := by
      unfold HP
      exact mul_le_mul_of_nonneg_left hSg0 (by positivity)
    -- the key size condition `(8/π²)·HP·Sg0 ≤ (η/2)·W·U·ℒ`
    have hkey : 8 / Real.pi ^ 2 * (HP P * Sg0) ≤ η / 2 * W * (U * P.LL) := by
      -- `U ≥ Kth ℒ/(2π)`
      have hU1 : Kth * P.LL ≤ 2 * Real.pi * U := by
        rw [hUdef]
        have hLLsq : P.LL ≤ P.LL ^ 2 := by
          have h1 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ P.LL by linarith) hLL0.le
          rw [mul_one] at h1
          rw [pow_two]; exact h1
        have : Kth * P.LL ≤ Kth * P.LL ^ 2 := mul_le_mul_of_nonneg_left hLLsq (by linarith)
        have e : 2 * Real.pi * (P.T / (2 * Real.pi)) = P.T := by field_simp
        rw [e]
        linarith
      have hK2' : 256 * c0 * (Cfam + 1) ≤ Kth * (3 * Real.pi * η) := by
        rwa [div_le_iff₀ (by positivity)] at hKth2
      -- reduce to `(8/π²)·aL(C+ℒ)c0L² ≤ (η/2)(aL)²Uℒ`
      have hred : 8 / Real.pi ^ 2 * (P.aQ * P.LB * (Cfam + P.LL) * (c0 * P.LB ^ 2))
          ≤ η / 2 * W * (U * P.LL) := by
        rw [hWdef]
        -- divide by `aQ·LB² > 0`: need `(8/π²)(C+ℒ)c0·LB ≤ (η/2)·aQ·U·ℒ`
        have hCL : Cfam + P.LL ≤ (Cfam + 1) * P.LL := by nlinarith
        have hq : 8 / Real.pi ^ 2 * ((Cfam + P.LL) * c0 * P.LB) ≤ η / 2 * P.aQ * (U * P.LL) := by
          have hstep1 : (Cfam + P.LL) * c0 * P.LB ≤ ((Cfam + 1) * P.LL) * c0 * (2 * P.LL) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hCL hc0.le) hLB2 hLB0.le (by positivity)
          have hstep2 : 8 / Real.pi ^ 2 * (((Cfam + 1) * P.LL) * c0 * (2 * P.LL))
              ≤ η / 2 * (3 / 4) * (U * P.LL) := by
            -- `16 c0 (C+1) ℒ² /π² ≤ (3η/8) U ℒ`  ⟸  `128 c0 (C+1) ℒ ≤ 3π²η U`
            have hmain : 128 * c0 * (Cfam + 1) * P.LL ≤ 3 * Real.pi ^ 2 * η * U := by
              have h1 := mul_le_mul_of_nonneg_right hK2' hLL0.le
              have h2 : Kth * (3 * Real.pi * η) * P.LL = (3 * Real.pi * η) * (Kth * P.LL) := by ring
              have h3 : (3 * Real.pi * η) * (Kth * P.LL) ≤ (3 * Real.pi * η) * (2 * Real.pi * U) :=
                mul_le_mul_of_nonneg_left hU1 (by positivity)
              nlinarith
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            have hm2 := mul_le_mul_of_nonneg_right hmain hLL0.le
            nlinarith
          have hstep3 : η / 2 * (3 / 4) * (U * P.LL) ≤ η / 2 * P.aQ * (U * P.LL) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith
          have hstep1' : 8 / Real.pi ^ 2 * ((Cfam + P.LL) * c0 * P.LB)
              ≤ 8 / Real.pi ^ 2 * (((Cfam + 1) * P.LL) * c0 * (2 * P.LL)) :=
            mul_le_mul_of_nonneg_left hstep1 (by positivity)
          linarith
        have hfac : 0 ≤ P.aQ * P.LB ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hq hfac
        have e2 : P.aQ * P.LB ^ 2 * (8 / Real.pi ^ 2 * ((Cfam + P.LL) * c0 * P.LB))
            = 8 / Real.pi ^ 2 * (P.aQ * P.LB * (Cfam + P.LL) * (c0 * P.LB ^ 2)) := by ring
        have e3 : P.aQ * P.LB ^ 2 * (η / 2 * P.aQ * (U * P.LL)) = η / 2 * (P.aQ * P.LB) ^ 2 * (U * P.LL) := by
          ring
        linarith
      have := mul_le_mul_of_nonneg_left hHS (by positivity : (0 : ℝ) ≤ 8 / Real.pi ^ 2)
      linarith
    -- multiply through by `U·ℒ > 0`
    have hUL : 0 < U * P.LL := by positivity
    have hlhs : (2 * S * (2 / Real.pi ^ 2 * HP P * Sg0)) * (U * P.LL)
        = (4 / Real.pi ^ 2 * (HP P * Sg0)) * (S * (U * P.LL)) := by ring
    have h1 : (4 / Real.pi ^ 2 * (HP P * Sg0)) * (S * (U * P.LL)) ≤ (4 / Real.pi ^ 2 * (HP P * Sg0)) * (2 * N) :=
      mul_le_mul_of_nonneg_left hSUL (by positivity)
    have h2 : (4 / Real.pi ^ 2 * (HP P * Sg0)) * (2 * N) ≤ (η / 2 * W * (U * P.LL)) * N := by
      have e : (4 / Real.pi ^ 2 * (HP P * Sg0)) * (2 * N) = (8 / Real.pi ^ 2 * (HP P * Sg0)) * N := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hkey hN0
    have h3 : (2 * S * (2 / Real.pi ^ 2 * HP P * Sg0)) * (U * P.LL) ≤ (N * W * (η / 2)) * (U * P.LL) := by
      rw [hlhs]
      have e : (η / 2 * W * (U * P.LL)) * N = (N * W * (η / 2)) * (U * P.LL) := by ring
      linarith
    exact le_of_mul_le_mul_right h3 hUL
  have e2 : W * (K + η) * N = N * W * (K + η / 2) + N * W * (η / 2) := by ring
  rw [e2]
  linarith

/-- **F1c-3.** DERIVED from F1c-3a (proved) and F1c-3b. -/
theorem shell_outDiag (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      2 * (Family.qle.sizeR Qn * outShell P)
        ≤ (P.aQ * P.LB) ^ 2 * (KoutShell Cfam (2497 / 1500) (zoneFactor P) (vDesign P) + η)
            * NfamQ P Family.qle Qn := by
  filter_upwards [shell_mertens r ε hr hε η hη] with Qn hM
  intro P hdes
  have hP : P.Valid := hdes.1
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hT : 0 ≤ P.T := hP.T_pos.le
  have hg0 := fun s => hP.gQ_nonneg hw s
  have hgle := fun s => hP.gQ_le_aL hw s
  have haL : 0 ≤ P.aQ * P.LB := mul_nonneg hP.aQ_pos.le hP.LB_pos.le
  have h0 : ∀ s, 0 ≤ P.gQ s * wOut P s := fun s => mul_nonneg (hg0 s) (wOut_nonneg_le hP s).1
  have hH : ∀ s, P.gQ s * wOut P s ≤ HP P := by
    intro s
    obtain ⟨hw0, hw1⟩ := wOut_nonneg_le hP s
    unfold HP
    exact mul_le_mul (hgle s) hw1 hw0 haL
  have hm : Measurable (fun s => P.gQ s * wOut P s) :=
    (hP.gQ_continuous hw).measurable.mul (wOut_measurable P)
  have hdom : ∀ s y, |s - y| < 1 → P.gQ s * wOut P s ≤ hsupP P y := by
    intro s y hsy
    unfold hsupP
    refine le_csSup ⟨HP P, ?_⟩ ⟨s, ?_, rfl⟩
    · rintro _ ⟨t, _, rfl⟩
      exact hH t
    · rw [Metric.mem_ball, Real.dist_eq]; exact hsy
  have hsm := smear_upper P hT (fun s => P.gQ s * wOut P s) (hsupP P) (HP P) hm h0 hH hdom
  beta_reduce at hsm
  have hS0 : 0 ≤ Family.qle.sizeR Qn := by unfold Family.sizeR; positivity
  rw [outShell_eq]
  have := mul_le_mul_of_nonneg_left hsm hS0
  have hM' := hM P hdes
  linarith

end F1c
end ShellK
end ZetaShell
