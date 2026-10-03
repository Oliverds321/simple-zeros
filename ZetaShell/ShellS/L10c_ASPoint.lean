/-
L10c_ASPoint (L7_10c, 3 Oct 2026): **AS at one point `(Q, s)`** (eq:shell-assembly at `K = ℒ(log ℒ)²`, `ε = 1/ℒ`),
every asymptotic input a hypothesis: the hole choice (`hole_exists`, Lemma 4 through K6/K7 when `ℓ_K ≤ s`, the empty
hole otherwise) and the assembly `AS_point` (A1′ replacement, `AS_core`, the size bounds of `L10c_ASBounds`, `AS_arith`).
-/
import ZetaShell.ShellS.L10c_ASBounds
import ZetaShell.Farey.A1p_ReplaceCost

noncomputable section
open scoped BigOperators Chebyshev

namespace ZetaShell
namespace ShellS
namespace ASc

theorem holeInt_nonneg (N : ℕ) (b : ℕ → ℂ) (R Δ : ℝ) (hΔ : 0 ≤ Δ) : 0 ≤ LemmaK.holeInt N b R Δ := by
  unfold LemmaK.holeInt
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity

theorem holeInt_zero (N : ℕ) (b : ℕ → ℂ) : LemmaK.holeInt N b 0 0 = 0 := by
  unfold LemmaK.holeInt; simp

set_option maxHeartbeats 2000000 in
/-- the hole used in the assembly: Lemma 4 (K6 + K7) when `ℓ_K ≤ s`, the empty hole when `s < ℓ_K`. -/
theorem hole_exists (lam : ℝ) (κ c : ℝ) (Ξ : ℝ → ℝ) (hΞ : PropZ.NearCutoff Ξ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hc : 0 < c) (hΞc : ∀ z, |z| ≤ c → Ξ z = 1) (C₆ : ℝ) (Q : ℕ) (T s : ℝ)
    (hy16 : 16 ≤ Real.log Q) (hT1 : 1 ≤ T) (hyL : Real.log Q ≤ LcS Q T) (hL2 : LcS Q T ≤ 2 * Real.log Q)
    (hlogL : 1 ≤ Real.log (LcS Q T)) (hs1 : Real.log Q + 4 ≤ s) (hs2 : s ≤ 2 * Real.log Q)
    (hsl : s + 1 ≤ lam * LcS Q T) (hsmall : 32 * Real.exp s * Real.log Q ^ 14 ≤ (Q : ℝ) ^ 2)
    (hNnx : Nnear s ≤ ⌊XlamS lam Q T⌋₊) (hlogX : Real.log ⌊XlamS lam Q T⌋₊ ≤ 4 * Real.log Q)
    (hUbig : 2 * (Cf (min c 1 * κ) + 1) * Real.log Q ^ 3 ≤ T / (2 * Real.pi))
    (htiny : (4 * Real.pi ^ 2)⁻¹ * (s + 1) * T ^ 2 * Real.exp (1 - s) * (2 * Real.exp ((s + 1) / 2) * (s + 1)) ≤ 1)
    (hl2 : ZetaQ.l2sq (Nnear s) (aNearP Q T κ Ξ s) ≤ T / (2 * Real.pi) * (s + 2))
    (hK6 : LemmaK.ellK Q T ≤ s → s ≤ Real.log (LemmaK.Xlam lam Q T) - 1 →
      (1 - C₆ / Real.log Q) * (T / (2 * Real.pi))
        ≤ ∫ β in (-(T * LemmaK.Lc Q T / (2 * Real.exp s)))..(T * LemmaK.Lc Q T / (2 * Real.exp s)),
            ‖ZetaQ.expSum ⌊LemmaK.Xlam lam Q T⌋₊ (LemmaK.aPrime T s (LemmaK.R0 Q T s)) β‖ ^ 2) :
    ∃ R0' Δ' : ℝ, 0 ≤ Δ' ∧ Δ' < 1 / 2 ∧ ⌊R0'⌋₊ ≤ ⌊TrackF.R1shell Q (Real.exp s) (1 / LcS Q T)⌋₊ ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ ⌊R0'⌋₊ → Δ' < 1 / ((r : ℝ) * Q)) ∧
      0 ≤ LemmaK.holeInt (Nnear s) (aNearP Q T κ Ξ s) R0' Δ' ∧
      ZetaQ.l2sq (Nnear s) (aNearP Q T κ Ξ s) - LemmaK.holeInt (Nnear s) (aNearP Q T κ Ξ s) R0' Δ'
        ≤ T / (2 * Real.pi) * (LcS Q T + Real.log (Kstd Q T) + (8 + 2 * |C₆|)) := by
  have hpi := Real.pi_pos
  have hes : 0 < Real.exp s := Real.exp_pos s
  have hT0 : 0 < T := by linarith
  have hQ1 : (1 : ℝ) ≤ Q := by
    by_contra h; push Not at h
    have : Real.log Q ≤ 0 := Real.log_nonpos (Nat.cast_nonneg Q) h.le
    linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  set y := Real.log (Q : ℝ) with hy
  set L := LcS Q T with hLdef
  set U := T / (2 * Real.pi) with hUdef
  have hU0 : 0 ≤ U := by positivity
  have hL1 : 1 ≤ L := by linarith
  have hLc : LemmaK.Lc Q T = L := rfl
  have hKdef : Kstd Q T = L * Real.log L ^ 2 := rfl
  have hlogK : Real.log L ≤ Real.log (Kstd Q T) := by
    rw [hKdef]; apply Real.log_le_log (by linarith)
    have : 1 ≤ Real.log L ^ 2 := one_le_pow₀ hlogL
    nlinarith
  have hlogK0 : 0 ≤ Real.log L := by linarith
  have hell : LemmaK.ellK Q T ≤ L + Real.log (Kstd Q T) + 2 := by
    have := ell_le (Q : ℝ) T hQ0 hT0 (show 0 < L by linarith) (show 1 ≤ Real.log L from hlogL)
    unfold LemmaK.ellK; exact this
  set Nn := Nnear s with hNndef
  set b := aNearP Q T κ Ξ s with hbdef
  have hl2b0 : 0 ≤ ZetaQ.l2sq Nn b := Finset.sum_nonneg fun _ _ => by positivity
  by_cases hcase : LemmaK.ellK Q T ≤ s
  · -- Lemma 4
    set Nx := ⌊XlamS lam Q T⌋₊ with hNxdef
    have hXl : LemmaK.Xlam lam Q T = XlamS lam Q T := rfl
    have hlogXl : Real.log (LemmaK.Xlam lam Q T) = lam * L := by
      rw [hXl]; unfold XlamS; rw [Real.log_exp]
    have hA := hK6 hcase (by rw [hlogXl]; linarith)
    rw [hLc, hXl, ← hNxdef] at hA
    have hR0eq : LemmaK.R0 Q T s = Real.exp s / ((Q : ℝ) * T * L) := rfl
    rw [hR0eq] at hA
    have hsQ : Real.exp s < (Q : ℝ) ^ 2 := by
      have h1 : 1 ≤ y ^ 14 := one_le_pow₀ (by linarith)
      have : Real.exp s ≤ Real.exp s * y ^ 14 := le_mul_of_one_le_right hes.le h1
      linarith
    have hQTL1 : 1 ≤ (Q : ℝ) * T * L := by
      rw [mul_assoc]; exact one_le_mul_of_one_le_of_one_le hQ1 (one_le_mul_of_one_le_of_one_le hT1 hL1)
    have hQTL : 0 < (Q : ℝ) * T * L := by linarith
    have hRQ : Real.exp s / ((Q : ℝ) * T * L) < Q := by
      rw [div_lt_iff₀ hQTL]
      have : (Q : ℝ) ^ 2 ≤ (Q : ℝ) * ((Q : ℝ) * T * L) := by
        have e : (Q : ℝ) * ((Q : ℝ) * T * L) = (Q : ℝ) ^ 2 * (T * L) := by ring
        rw [e]; exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hT1 hL1)
      linarith
    have hdiff := diff_aP_b (Q : ℝ) T κ c (Real.exp s / ((Q : ℝ) * T * L)) Ξ hΞ hκ hκ1 hΞc s
      (by linarith) hQ1 hRQ
    have hd0 : 0 < min c 1 * κ := mul_pos (lt_min hc one_pos) hκ
    have hd1 : min c 1 * κ ≤ 1 := by
      have : min c 1 ≤ 1 := min_le_right _ _
      have : 0 ≤ min c 1 := (lt_min hc one_pos).le
      nlinarith
    have hE := compl_bound Nx T s (min c 1 * κ) y hd0 hd1 hlogX (by linarith) hT0.le (by linarith)
      (fun n => LemmaK.aPrime T s (Real.exp s / ((Q : ℝ) * T * L)) n - b n) hdiff.1
      (fun n hp hn => hdiff.2 n hp hn) htiny
    have hbP : ∀ n, b n ≠ 0 → n.Prime ∧ Q < n := by
      intro n hn
      obtain ⟨hp, hQn, _⟩ := aNearP_support (Q : ℝ) T κ Ξ hΞ hκ s n hn
      exact ⟨hp, by exact_mod_cast hQn⟩
    have hbz : ∀ n, Nn < n → b n = 0 := fun n hn => aNearP_zero_beyond (Q : ℝ) T κ Ξ hΞ hκ hκ1 s n hn
    have hℓ : Real.log ((Q : ℝ) * T * L) ≤ s := hcase
    have hH := hole_case2 Q Nx Nn b (LemmaK.aPrime T s (Real.exp s / ((Q : ℝ) * T * L))) s y T L U C₆
      (Cf (min c 1 * κ)) hy16 hQ1 hT1 hL1 hU0 hℓ hs2 hsQ hbP hNnx hbz hA hE (Cf_nonneg _) hUbig hl2
    refine ⟨Real.exp s / ((Q : ℝ) * T * L), T * L / (2 * Real.exp s), by positivity, ?_, ?_, ?_,
      holeInt_nonneg _ _ _ _ (by positivity), ?_⟩
    · -- `Δ < 1/2`
      rw [div_lt_iff₀ (by positivity)]
      have hle : (Q : ℝ) * T * L ≤ Real.exp s := (Real.log_le_iff_le_exp hQTL).mp hℓ
      have : T * L < (Q : ℝ) * T * L := by
        have hQ' : (1 : ℝ) < Q := by
          by_contra h; push Not at h
          have : Real.log Q ≤ 0 := Real.log_nonpos (Nat.cast_nonneg Q) h
          linarith
        have : 0 < T * L := by positivity
        nlinarith
      linarith
    · -- `⌊R₀⌋ ≤ ⌊R₁⌋`
      apply Nat.floor_le_floor
      have e1 : TrackF.R1shell Q (Real.exp s) (1 / L) = Real.exp s / Q * (y ^ 6 * L) := by
        unfold TrackF.R1shell; rw [← hy]; field_simp
      have e2 : Real.exp s / ((Q : ℝ) * T * L) = Real.exp s / Q * (1 / (T * L)) := by
        field_simp
      rw [e1, e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : 1 / (T * L) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact one_le_mul_of_one_le_of_one_le hT1 hL1
      have h2 : 1 ≤ y ^ 6 * L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hL1
      linarith
    · -- `Δ < 1/(rQ)` for `r ≤ R₀`
      intro r hr hrR
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hrR' : (r : ℝ) ≤ Real.exp s / ((Q : ℝ) * T * L) :=
        le_trans (Nat.cast_le.mpr hrR) (Nat.floor_le (by positivity))
      rw [lt_div_iff₀ (by positivity)]
      have h1 : T * L / (2 * Real.exp s) * ((r : ℝ) * Q)
          ≤ T * L / (2 * Real.exp s) * (Real.exp s / ((Q : ℝ) * T * L) * Q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrR' hQ0.le) (by positivity)
      have e : T * L / (2 * Real.exp s) * (Real.exp s / ((Q : ℝ) * T * L) * Q) = 1 / 2 := by
        field_simp
      linarith
    · -- the bound
      have : Real.log ((Q : ℝ) * T * L) ≤ L + Real.log (Kstd Q T) + 2 := hell
      have h2 : U * (Real.log ((Q : ℝ) * T * L) + 6 + 2 * |C₆|)
          ≤ U * (L + Real.log (Kstd Q T) + (8 + 2 * |C₆|)) :=
        mul_le_mul_of_nonneg_left (by linarith) hU0
      linarith
  · -- the empty hole
    push Not at hcase
    refine ⟨0, 0, le_rfl, by norm_num, by simp, ?_, ?_, ?_⟩
    · intro r hr hrR; simp at hrR; omega
    · rw [holeInt_zero]
    · rw [holeInt_zero, sub_zero]
      have h1 : U * (s + 2) ≤ U * (L + Real.log (Kstd Q T) + (8 + 2 * |C₆|)) :=
        mul_le_mul_of_nonneg_left (by have := abs_nonneg C₆; linarith) hU0
      linarith

/-- the ring count `R₁ = N(log Q)⁶/(εQ)` at `N = e^s`, `ε = 1/ℒ`: `1 ≤ R₁ ≤ Q/(2K)`, and `⌊R₁⌋Q ≤ e^s y⁶ ℒ`. -/
theorem R1_facts (Q : ℕ) (s y L : ℝ) (hy : y = Real.log Q) (hQ1 : 1 ≤ (Q : ℝ)) (hy16 : 16 ≤ y) (hyL : y ≤ L)
    (hL2 : L ≤ 2 * y) (hlogL : 1 ≤ Real.log L) (hs1 : y + 4 ≤ s)
    (hsmall : 32 * Real.exp s * y ^ 14 ≤ (Q : ℝ) ^ 2) :
    1 ≤ TrackF.R1shell Q (Real.exp s) (1 / L) ∧
      TrackF.R1shell Q (Real.exp s) (1 / L) ≤ (Q : ℝ) / (2 * (L * Real.log L ^ 2)) ∧
      (⌊TrackF.R1shell Q (Real.exp s) (1 / L)⌋₊ : ℝ) * Q ≤ Real.exp s * y ^ 6 * L := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hL0 : 0 < L := by linarith
  have hy0 : 0 < y := by linarith
  have hes : 0 < Real.exp s := Real.exp_pos s
  have e1 : TrackF.R1shell Q (Real.exp s) (1 / L) = Real.exp s * y ^ 6 * L / Q := by
    unfold TrackF.R1shell; rw [← hy]; field_simp
  have hQe : (Q : ℝ) ≤ Real.exp s := by
    have : Real.exp y = Q := by rw [hy]; exact Real.exp_log hQ0
    rw [← this]; exact Real.exp_le_exp.mpr (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, le_div_iff₀ hQ0, one_mul]
    have h1 : 1 ≤ y ^ 6 * L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (by linarith)
    have : Real.exp s * 1 ≤ Real.exp s * (y ^ 6 * L) := mul_le_mul_of_nonneg_left h1 hes.le
    linarith
  · rw [e1, div_le_div_iff₀ hQ0 (by positivity)]
    have hlL : Real.log L ≤ L := by have := Real.log_le_sub_one_of_pos hL0; linarith
    have hlL2 : Real.log L ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hlL 2
    have hL4 : L ^ 2 ≤ 4 * y ^ 2 := by
      have := pow_le_pow_left₀ hL0.le hL2 2
      have e : (2 * y) ^ 2 = 4 * y ^ 2 := by ring
      linarith
    have e2 : Real.exp s * y ^ 6 * L * (2 * (L * Real.log L ^ 2))
        = 2 * (Real.exp s * y ^ 6) * (L ^ 2 * Real.log L ^ 2) := by ring
    have h1 : L ^ 2 * Real.log L ^ 2 ≤ (4 * y ^ 2) * (4 * y ^ 2) :=
      mul_le_mul hL4 (le_trans hlL2 hL4) (by positivity) (by positivity)
    have h2 : 2 * (Real.exp s * y ^ 6) * (L ^ 2 * Real.log L ^ 2) ≤ 2 * (Real.exp s * y ^ 6) * ((4 * y ^ 2) * (4 * y ^ 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e3 : 2 * (Real.exp s * y ^ 6) * ((4 * y ^ 2) * (4 * y ^ 2)) = 32 * (Real.exp s * y ^ 10) := by ring
    have h10 : y ^ 10 ≤ y ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h3 : Real.exp s * y ^ 10 ≤ Real.exp s * y ^ 14 := mul_le_mul_of_nonneg_left h10 hes.le
    have e4 : 32 * Real.exp s * y ^ 14 = 32 * (Real.exp s * y ^ 14) := by ring
    have e5 : (Q : ℝ) * Q = (Q : ℝ) ^ 2 := by ring
    rw [e2, e5]; linarith
  · have h0 : 0 ≤ TrackF.R1shell Q (Real.exp s) (1 / L) := by rw [e1]; positivity
    have h1 := Nat.floor_le h0
    rw [e1] at h1
    have := mul_le_mul_of_nonneg_right h1 hQ0.le
    rw [div_mul_cancel₀ _ hQ0.ne'] at this
    rw [e1]; exact this

/-- `log K ≤ ℒ` and `0 ≤ log K` for `K = ℒ(log ℒ)²`, `log ℒ ≥ 1`. -/
theorem logK_facts (L : ℝ) (hL : 16 ≤ L) (hlogL : 1 ≤ Real.log L) :
    0 ≤ Real.log (L * Real.log L ^ 2) ∧ Real.log (L * Real.log L ^ 2) ≤ L := by
  have hL0 : 0 < L := by linarith
  have hlL0 : 0 < Real.log L := by linarith
  have e : Real.log (L * Real.log L ^ 2) = Real.log L + 2 * Real.log (Real.log L) := by
    rw [Real.log_mul hL0.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hll0 : 0 ≤ Real.log (Real.log L) := Real.log_nonneg hlogL
  have hll : Real.log (Real.log L) ≤ Real.log L - 1 := Real.log_le_sub_one_of_pos hlL0
  have hl6 : Real.log L ≤ L / 6 + 1 := by
    have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < L / 6)
    rw [Real.log_div hL0.ne' (by norm_num)] at h1
    have h6 : Real.log 6 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  rw [e]; constructor <;> linarith

open TrackF in
/-- the constant of AS. -/
def Cas (B₂ C₆ : ℝ) : ℝ := (2 * (8 + 2 * |C₆|) + 2 + 2 * 1080 + 2 * 300 + 2 * 1) + 4 + 2 * (67 * B₂)

theorem Cas_nonneg (B₂ C₆ : ℝ) (hB₂ : 0 ≤ B₂) : 0 ≤ Cas B₂ C₆ := by
  unfold Cas; have := abs_nonneg C₆; positivity

open TrackF in
set_option maxHeartbeats 4000000 in
/-- **AS at one point `(Q, s)`**: every asymptotic input a hypothesis. -/
theorem AS_point (lam : ℝ) (hl0 : 0 ≤ lam) (hlam2 : lam < 2) (B₂ Q0 : ℝ) (hB₂ : 0 ≤ B₂)
    (h2a : ∀ (Q : ℕ) (N ε K Omax t : ℝ), Q0 ≤ Q → 0 < N → 0 < ε → 1 ≤ K →
      (∀ d ∈ Finset.Icc 1 Q, |ZetaShell.OmegaW Q (Fam.omega .sharp Q) d| ≤ Omax) →
      1 ≤ R1shell Q N ε → R1shell Q N ε ≤ (Q : ℝ) / (2 * K) → t ∉ shellSet Q K (R1shell Q N ε) →
      max (Ddens (fareyIdx Q) fareyPt (fareyWeight .sharp Q) (ε / N) t) 0
        ≤ Hw .sharp Q * (1 + B₂ * bracket2a Q N ε K Omax (Hw .sharp Q)))
    (κ c : ℝ) (Ξ : ℝ → ℝ) (hΞ : PropZ.NearCutoff Ξ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hc : 0 < c) (hΞc : ∀ z, |z| ≤ c → Ξ z = 1) (C₆ : ℝ) (Q : ℕ) (T s : ℝ) (hQ0 : Q0 ≤ Q)
    (hy16 : 16 ≤ Real.log Q) (hT1 : 1 ≤ T) (hyL : Real.log Q ≤ LcS Q T) (hL2 : LcS Q T ≤ 2 * Real.log Q)
    (hlogL : 1 ≤ Real.log (LcS Q T)) (hs1 : Real.log Q + 4 ≤ s) (hs2 : s ≤ 2 * Real.log Q)
    (hsl : s + 1 ≤ lam * LcS Q T) (hX : Real.pi * XlamS lam Q T ≤ (Q : ℝ) ^ 2)
    (hsmall : 32 * Real.exp s * Real.log Q ^ 14 ≤ (Q : ℝ) ^ 2) (hyT : Real.log Q ^ 4 * T ^ 4 ≤ Q)
    (hUbig : 2 * (Cf (min c 1 * κ) + 1) * Real.log Q ^ 3 ≤ T / (2 * Real.pi))
    (εθ : ℝ) (hε0 : 0 ≤ εθ)
    (hθ : ∀ k : ℕ, Real.exp (s - 1) - 1 ≤ k → (k : ℝ) ≤ Real.exp (s + 1) → |θ (k : ℝ) - k| ≤ εθ * k)
    (h34 : 34 * εθ * T ^ 3 ≤ 1) (hHw : (Q : ℝ) ^ 2 / 6 ≤ famSize Q)
    (hK6 : LemmaK.ellK Q T ≤ s → s ≤ Real.log (LemmaK.Xlam lam Q T) - 1 →
      (1 - C₆ / Real.log Q) * (T / (2 * Real.pi))
        ≤ ∫ β in (-(T * LemmaK.Lc Q T / (2 * Real.exp s)))..(T * LemmaK.Lc Q T / (2 * Real.exp s)),
            ‖ZetaQ.expSum ⌊LemmaK.Xlam lam Q T⌋₊ (LemmaK.aPrime T s (LemmaK.R0 Q T s)) β‖ ^ 2) :
    TrackF.famF (Finset.Icc 2 Q) ⌊XlamS lam Q T⌋₊ (TrackF.acoefS T s)
      ≤ famSize Q * (T / (2 * Real.pi)) * (LcS Q T + Real.log (Kstd Q T) + Cas B₂ C₆)
        + (Q : ℝ) ^ 2 * (1 + Cas B₂ C₆ * (Real.log (LcS Q T) / LcS Q T))
          * RingS Q T κ Ξ (Kstd Q T) (1 / LcS Q T) (s - 1) s
        + Cas B₂ C₆ * (Real.log (LcS Q T) / LcS Q T) * famSize Q * l2S ⌊XlamS lam Q T⌋₊ T s := by
  have hpi := Real.pi_pos
  have hes : 0 < Real.exp s := Real.exp_pos s
  have hT0 : 0 < T := by linarith
  have hQ1 : (1 : ℝ) ≤ Q := by
    by_contra h; push Not at h
    have : Real.log Q ≤ 0 := Real.log_nonpos (Nat.cast_nonneg Q) h.le
    linarith
  have hQ0' : (0 : ℝ) < Q := by linarith
  have hexpy : Real.exp (Real.log Q) = Q := Real.exp_log hQ0'
  have hHw' : (Q : ℝ) ^ 2 / 6 ≤ Hw .sharp Q := by rw [Hw_sharp_famSize]; exact hHw
  have hHw0 : 0 ≤ Hw .sharp Q := le_trans (by positivity) hHw'
  -- PNT upper bound and the tail (before the abbreviations)
  have h100 : 100 * T ^ 3 ≤ Real.exp s := by
    have h1 : (16 : ℝ) ^ 4 ≤ Real.log Q ^ 4 := pow_le_pow_left₀ (by norm_num) hy16 4
    have h2 : 100 * T ^ 3 ≤ Real.log Q ^ 4 * T ^ 4 := by
      have e : Real.log Q ^ 4 * T ^ 4 = (Real.log Q ^ 4 * T) * T ^ 3 := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (16 : ℝ) ^ 4 * 1 ≤ Real.log Q ^ 4 * T := mul_le_mul h1 hT1 (by norm_num) (by positivity)
      linarith
    have h3 : (Q : ℝ) ≤ Real.exp s := by rw [← hexpy]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsT : s + 1 ≤ Real.pi * T := by
    have hCf := Cf_nonneg (min c 1 * κ)
    have h1 : 3 * Real.log Q ≤ 2 * (Cf (min c 1 * κ) + 1) * Real.log Q ^ 3 := by
      have hy2 : 2 ≤ Real.log Q ^ 2 := by nlinarith
      have e : 2 * (Cf (min c 1 * κ) + 1) * Real.log Q ^ 3
          = (2 * (Cf (min c 1 * κ) + 1) * Real.log Q ^ 2) * Real.log Q := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      have : Real.log Q ^ 2 ≤ (Cf (min c 1 * κ) + 1) * Real.log Q ^ 2 :=
        le_mul_of_one_le_left (by positivity) (by linarith)
      linarith
    have h2 : T / (2 * Real.pi) ≤ Real.pi * T := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ 2 * Real.pi * Real.pi := by nlinarith [Real.pi_gt_three]
      nlinarith
    linarith
  have hl2 := l2b_upper (Q : ℝ) T κ Ξ hΞ hκ hκ1 s (by linarith) (Nnear s) hT1 h100 εθ hε0 hθ h34 hsT
  have htiny := tiny_le s (Real.log Q) T hy16 hs1 hs2 hT0.le (by rw [hexpy]; exact hyT)
  have hXeq : XlamS lam Q T = Real.exp (lam * LcS Q T) := rfl
  have hNnx : Nnear s ≤ ⌊XlamS lam Q T⌋₊ := by
    unfold Nnear; apply Nat.floor_le_floor; rw [hXeq]; exact Real.exp_le_exp.mpr hsl
  have hlogX : Real.log ⌊XlamS lam Q T⌋₊ ≤ 4 * Real.log Q := by
    rcases Nat.eq_zero_or_pos ⌊XlamS lam Q T⌋₊ with h | h
    · rw [h]; simp; linarith
    · have h1 : Real.log ⌊XlamS lam Q T⌋₊ ≤ Real.log (XlamS lam Q T) :=
        Real.log_le_log (by exact_mod_cast h) (Nat.floor_le (by rw [hXeq]; positivity))
      have hlx : Real.log (XlamS lam Q T) = lam * LcS Q T := by rw [hXeq, Real.log_exp]
      rw [hlx] at h1
      have : lam * LcS Q T ≤ 2 * LcS Q T := mul_le_mul_of_nonneg_right hlam2.le (by linarith)
      linarith
  -- the hole
  obtain ⟨R0', Δ', hΔ0, hΔh, hR0', hΔr, hhole0, hhole⟩ := hole_exists lam κ c Ξ hΞ hκ hκ1 hc hΞc C₆ Q T s
    hy16 hT1 hyL hL2 hlogL hs1 hs2 hsl hsmall hNnx hlogX hUbig htiny hl2 hK6
  -- the complement `a − b`
  have hdiff := diff_a_b (Q : ℝ) T κ c Ξ hΞ hκ hκ1 hΞc s (by linarith) hQ1
  have hd0 : 0 < min c 1 * κ := mul_pos (lt_min hc one_pos) hκ
  have hd1 : min c 1 * κ ≤ 1 := by
    have h1 : min c 1 ≤ 1 := min_le_right _ _
    have h2 : 0 ≤ min c 1 := (lt_min hc one_pos).le
    calc min c 1 * κ ≤ 1 * 1 := mul_le_mul h1 hκ1 hκ.le (by norm_num)
      _ = 1 := by norm_num
  have hcomp := compl_bound ⌊XlamS lam Q T⌋₊ T s (min c 1 * κ) (Real.log Q) hd0 hd1 hlogX (by linarith)
    hT0.le (by linarith) (fun n => TrackF.acoefS T s n - aNearP Q T κ Ξ s n) hdiff.1
    (fun n hp hn => hdiff.2 n hp hn) htiny
  -- A1′
  have hA : famF (Finset.Icc 2 Q) ⌊XlamS lam Q T⌋₊ (TrackF.acoefS T s)
      ≤ (Real.sqrt (famF (Finset.Icc 2 Q) (Nnear s) (aNearP Q T κ Ξ s))
          + Real.sqrt (ZetaQ.Gallagher.gallagherBudget ⌊XlamS lam Q T⌋₊ Q
              * ZetaQ.l2sq ⌊XlamS lam Q T⌋₊ (fun n => TrackF.acoefS T s n - aNearP Q T κ Ξ s n))) ^ 2 := by
    have h := replace_cost Q ⌊XlamS lam Q T⌋₊ (Finset.Icc 2 Q) (Finset.Icc_subset_Icc (by norm_num) le_rfl)
      (aNearP Q T κ Ξ s) (fun n => TrackF.acoefS T s n - aNearP Q T κ Ξ s n)
    have e : (fun n => aNearP Q T κ Ξ s n + (TrackF.acoefS T s n - aNearP Q T κ Ξ s n)) = TrackF.acoefS T s := by
      funext n; ring
    rw [e, famF_trunc (Finset.Icc 2 Q) (Nnear s) ⌊XlamS lam Q T⌋₊ hNnx (aNearP Q T κ Ξ s)
      (fun n hn => aNearP_zero_beyond (Q : ℝ) T κ Ξ hΞ hκ hκ1 s n hn)] at h
    exact h
  -- AS_core
  have hL1 : 1 ≤ LcS Q T := by linarith
  have hL0 : 0 < LcS Q T := by linarith
  obtain ⟨hR1, hR1K, hR1n⟩ := R1_facts Q s (Real.log Q) (LcS Q T) rfl hQ1 hy16 hyL hL2 hlogL hs1 hsmall
  have hKdef : Kstd Q T = LcS Q T * Real.log (LcS Q T) ^ 2 := rfl
  have hK1 : 1 ≤ Kstd Q T := by
    rw [hKdef]; exact one_le_mul_of_one_le_of_one_le hL1 (one_le_pow₀ hlogL)
  have hbP : ∀ n, aNearP Q T κ Ξ s n ≠ 0 → n.Prime ∧ Q < n := by
    intro n hn
    obtain ⟨hp, hQn, _⟩ := aNearP_support (Q : ℝ) T κ Ξ hΞ hκ s n hn
    exact ⟨hp, by exact_mod_cast hQn⟩
  have hsupp : ∀ n ∈ Finset.Ioc 0 (Nnear s), aNearP Q T κ Ξ s n ≠ 0 →
      Real.exp s * Real.exp (-κ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ Real.exp s * Real.exp κ := by
    intro n _ hn
    obtain ⟨hp, _, hcl⟩ := aNearP_support (Q : ℝ) T κ Ξ hΞ hκ s n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
    have he : Real.exp (Real.log n) = n := Real.exp_log hn0
    rw [abs_lt] at hcl
    rw [← Real.exp_add, ← Real.exp_add, ← he]
    exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩
  have hεN : 1 / LcS Q T < Real.exp s := by
    have h1 : 1 / LcS Q T ≤ 1 := by rw [div_le_one hL0]; exact hL1
    have h2 : 1 < Real.exp s := by
      have := Real.add_one_lt_exp (x := s) (by intro h; linarith)
      linarith
    linarith
  have hcore := AS_core B₂ Q0 hB₂ h2a Q (Nnear s) (aNearP Q T κ Ξ s) (Real.exp s) κ (1 / LcS Q T) (Kstd Q T)
    hQ0 hes hκ.le (by positivity) hεN hK1 hR1 (by rw [hKdef]; exact hR1K) hbP hsupp R0' Δ' hΔ0 hΔh hR0' hΔr
  -- the size bounds
  have hlm0 : 0 ≤ Real.log (LcS Q T) / LcS Q T := by positivity
  have hlm1 : Real.log (LcS Q T) / LcS Q T ≤ 1 := by
    rw [div_le_one hL0]; have := Real.log_le_sub_one_of_pos hL0; linarith
  have hlmL : 1 / LcS Q T ≤ Real.log (LcS Q T) / LcS Q T := div_le_div_of_nonneg_right hlogL hL0.le
  obtain ⟨hlogK0, hlogKL⟩ := logK_facts (LcS Q T) (by linarith) hlogL
  rw [← hKdef] at hlogK0 hlogKL
  have hBr : B₂ * bracket2a Q (Real.exp s) (1 / LcS Q T) (Kstd Q T) 1 (Hw .sharp Q)
      ≤ (67 * B₂) * (Real.log (LcS Q T) / LcS Q T) := by
    have h := bracket_bound Q s (Real.log Q) (LcS Q T) (Hw .sharp Q) rfl hy16 hyL hL2 hlogL hHw' hsmall
    rw [← hKdef] at h
    have := mul_le_mul_of_nonneg_left h hB₂
    linarith
  have hBr0 : 0 ≤ B₂ * bracket2a Q (Real.exp s) (1 / LcS Q T) (Kstd Q T) 1 (Hw .sharp Q) := by
    apply mul_nonneg hB₂
    unfold bracket2a R1shell
    have hlK : 0 ≤ 1 + Real.log (Kstd Q T) := by linarith
    have hK0 : 0 < Kstd Q T := by linarith
    have t1 : 0 ≤ (1 + Real.log (Kstd Q T)) ^ 3 / Kstd Q T := div_nonneg (pow_nonneg hlK 3) hK0.le
    have t2 : 0 ≤ Real.exp s * Real.log Q ^ 2 / (1 / LcS Q T * Q * (Real.exp s * Real.log Q ^ 6 / (1 / LcS Q T * Q))) := by
      positivity
    have t3 : 0 ≤ Real.exp s * Real.log Q ^ 8 / (1 / LcS Q T * (Q : ℝ) ^ 2) := by positivity
    have t4 : 0 ≤ 1 * Real.exp s / (1 / LcS Q T * Hw .sharp Q) := by positivity
    linarith
  have hBm := Bm_bound Q s (Real.log Q) (LcS Q T) hy16 hyL hL2 hlogL hsmall
  have hl2b0 : 0 ≤ ZetaQ.l2sq (Nnear s) (aNearP Q T κ Ξ s) := Finset.sum_nonneg fun _ _ => by positivity
  have hNn : ((Nnear s : ℕ) : ℝ) ≤ Real.exp (s + 1) := by unfold Nnear; exact Nat.floor_le (by positivity)
  have hEd := Ed_bound Q (⌊R1shell Q (Real.exp s) (1 / LcS Q T)⌋₊ : ℝ) (Nnear s : ℝ) s (Real.log Q) (LcS Q T)
    (T / (2 * Real.pi)) (Hw .sharp Q) (ZetaQ.l2sq (Nnear s) (aNearP Q T κ Ξ s)) hQ0' hy16 hyL hL2 hs2
    (by positivity) hR1n hNn (by positivity) hsmall hHw' (by positivity) hl2b0 hl2
  have hGa := Ga_bound Q κ s (Real.log Q) (LcS Q T) (T / (2 * Real.pi)) (Hw .sharp Q)
    (ZetaQ.l2sq (Nnear s) (aNearP Q T κ Ξ s)) hκ.le hκ1 hy16 hyL hs2 hsmall hHw' (by positivity) hl2b0 hl2
  have hl2c0 : 0 ≤ ZetaQ.l2sq ⌊XlamS lam Q T⌋₊ (fun n => TrackF.acoefS T s n - aNearP Q T κ Ξ s n) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hNx' : Real.pi * (⌊XlamS lam Q T⌋₊ : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have : (⌊XlamS lam Q T⌋₊ : ℝ) ≤ XlamS lam Q T := Nat.floor_le (by rw [hXeq]; positivity)
    have := mul_le_mul_of_nonneg_left this hpi.le
    linarith
  have hGE := GE_bound Q (⌊XlamS lam Q T⌋₊ : ℝ) (Cf (min c 1 * κ)) (Real.log Q) (LcS Q T) (T / (2 * Real.pi))
    (Hw .sharp Q) _ hy16 hyL hL2 hNx' (Cf_nonneg _) hl2c0 hcomp hUbig hHw'
  have hGE' : ZetaQ.Gallagher.gallagherBudget ⌊XlamS lam Q T⌋₊ Q
        * ZetaQ.l2sq ⌊XlamS lam Q T⌋₊ (fun n => TrackF.acoefS T s n - aNearP Q T κ Ξ s n)
      ≤ 1 * Hw .sharp Q * (T / (2 * Real.pi)) / LcS Q T := by
    unfold ZetaQ.Gallagher.gallagherBudget; exact hGE
  have hGE0 : 0 ≤ ZetaQ.Gallagher.gallagherBudget ⌊XlamS lam Q T⌋₊ Q
        * ZetaQ.l2sq ⌊XlamS lam Q T⌋₊ (fun n => TrackF.acoefS T s n - aNearP Q T κ Ξ s n) := by
    unfold ZetaQ.Gallagher.gallagherBudget; positivity
  have hFb0 : 0 ≤ famF (Finset.Icc 2 Q) (Nnear s) (aNearP Q T κ Ξ s) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hl2ba := l2b_le_l2a (Nnear s) ⌊XlamS lam Q T⌋₊ hNnx T s (aNearP Q T κ Ξ s)
    (aNearP_norm_le (Q : ℝ) T κ Ξ hΞ s)
  have hfin := AS_arith _ _ _ (Hw .sharp Q) _ _ _ _ _ (l2S ⌊XlamS lam Q T⌋₊ T s) _ _ (T / (2 * Real.pi))
    (LcS Q T) (Real.log (Kstd Q T)) (Real.log (LcS Q T) / LcS Q T) (8 + 2 * |C₆|) (67 * B₂) 1080 300 1
    ((Q : ℝ) ^ 2) hFb0 hGE0 hHw0 hBr0 (ringMass_nonneg' _ _ _ _ _) (by positivity) hL1 hlm0 hlm1 hlmL
    (by positivity) hl2b0 hhole0 (by have := abs_nonneg C₆; positivity) (by positivity) (by norm_num)
    (by norm_num) (by norm_num) hlogK0 hlogKL hA hcore hhole hl2ba hBr hBm hEd hGa hGE'
  -- conclude
  have hRing : RingS Q T κ Ξ (Kstd Q T) (1 / LcS Q T) (s - 1) s
      = ringMass Q ⌊R1shell Q (Real.exp s) (1 / LcS Q T)⌋₊ (Nnear s) (Kstd Q T) (aNearP Q T κ Ξ s) := by
    unfold RingS R1S R1shell; rw [sub_add_cancel]
  rw [hRing, ← Hw_sharp_famSize]
  have hC := Cas_nonneg B₂ C₆ hB₂
  set Ring := ringMass Q ⌊R1shell Q (Real.exp s) (1 / LcS Q T)⌋₊ (Nnear s) (Kstd Q T) (aNearP Q T κ Ξ s)
  have hRing0 : 0 ≤ Ring := ringMass_nonneg' _ _ _ _ _
  set lm := Real.log (LcS Q T) / LcS Q T
  set H := Hw .sharp Q
  set l2a := l2S ⌊XlamS lam Q T⌋₊ T s
  have hl2a0 : 0 ≤ l2a := Finset.sum_nonneg fun _ _ => by positivity
  set U := T / (2 * Real.pi)
  have hU0 : 0 ≤ U := by positivity
  have k1 : H * U * (LcS Q T + Real.log (Kstd Q T) + (2 * (8 + 2 * |C₆|) + 2 + 2 * 1080 + 2 * 300 + 2 * 1))
      ≤ H * U * (LcS Q T + Real.log (Kstd Q T) + Cas B₂ C₆) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold Cas; linarith
  have k2 : (Q : ℝ) ^ 2 * (1 + 4 * lm) * Ring ≤ (Q : ℝ) ^ 2 * (1 + Cas B₂ C₆ * lm) * Ring := by
    apply mul_le_mul_of_nonneg_right _ hRing0
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 4 ≤ Cas B₂ C₆ := by unfold Cas; have := abs_nonneg C₆; linarith
    nlinarith
  have k3 : 2 * (67 * B₂) * lm * H * l2a ≤ Cas B₂ C₆ * lm * H * l2a := by
    have : 2 * (67 * B₂) ≤ Cas B₂ C₆ := by unfold Cas; have := abs_nonneg C₆; linarith
    have h0 : 0 ≤ lm * H * l2a := by positivity
    have e1 : 2 * (67 * B₂) * lm * H * l2a = 2 * (67 * B₂) * (lm * H * l2a) := by ring
    have e2 : Cas B₂ C₆ * lm * H * l2a = Cas B₂ C₆ * (lm * H * l2a) := by ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right this h0
  linarith

end ASc
end ShellS
end ZetaShell
