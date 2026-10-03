/-
L7_9 round 2, sub-node K6d (tails, lem:K-P Step 4) of `principal_arc_mass` (K6).
Draft: `E₂² ≤ Σ_{n≤𝒳, |log n − s| ≥ 1/2} Λ(n)²|w(n)|² ≤ (log 𝒳/π²) Σ_{n≤𝒳} Λ(n)/n·f(log n)` with
`f(u) = (s−u)^{−2}1{|s−u| ≥ 1/2}`, and Mertens (tree: `Mertens.sum_mangoldt_div_eq_log`, constant `log 4 + 4`) gives
`E₂² ≤ c·λℒ`; the interval `[−Δ, Δ]` lies in one period (`Δ ≤ 1/(2Q)`), so Parseval bounds the integral by `E₂²`.
Since `r + ε > 3`, `λℒ ≤ C·U/(log Q)²` eventually.
-/
import ZetaShell.LemmaK.LK9_K6_Defs
import ZetaShell.LemmaK.LK9_K6d_Aux

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

theorem tails (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 →
      ∫ β in (-(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)))..(ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s)),
          ‖ZetaQ.expSum ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
            (fun n => aPrime (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s) n - K6.asmooth (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s) n) β‖ ^ 2
        ≤ C * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi)) / Real.log (Qn : ℝ) ^ 2 := by
  set K₀ : ℝ := (4 * Real.pi ^ 2)⁻¹ * 32 * (2 + 2 * (Real.log 4 + 4)) * K6.Cz with hK₀
  have hCz : 0 ≤ K6.Cz := tsum_nonneg fun k => by positivity
  have hK₀0 : 0 ≤ K₀ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hre : 3 ≤ r + ε := by linarith
  refine ⟨8 * Real.pi * K₀, ?_⟩
  have E1 : ∀ᶠ Qn : ℕ in atTop, (100 : ℝ) ≤ (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 100)
  have E2 : ∀ᶠ Qn : ℕ in atTop, (1 : ℝ) ≤ Real.log (Qn : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  have E3 : ∀ᶠ Qn : ℕ in atTop, Real.log (Qn : ℝ) ^ (r + ε) ≤ (Qn : ℝ) := by
    have hO := (isLittleO_log_rpow_rpow_atTop (r + ε) (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1)
    have h' : ∀ᶠ y : ℝ in atTop, Real.log y ^ (r + ε) ≤ y := by
      filter_upwards [hO, eventually_ge_atTop (1 : ℝ)] with y hy hy1
      have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _), Real.rpow_one,
        Real.norm_of_nonneg (by linarith), one_mul] at hy
      exact hy
    exact tendsto_natCast_atTop_atTop.eventually h'
  filter_upwards [E1, E2, E3] with Qn h100 hlog hTQ s hs1 hs2
  set x := Real.log (Qn : ℝ) with hx
  set T := ZetaQ.Twin (Qn : ℝ) r ε with hT
  set L := Lc (Qn : ℝ) T with hL
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hT1 : 1 ≤ T := Real.one_le_rpow hlog (by linarith)
  have hTQ' : T ≤ (Qn : ℝ) := hTQ
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  have hL0 : 0 < L := by
    rw [hL, Lc]
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hQTL : 0 < (Qn : ℝ) * T * L := by positivity
  -- Δ ∈ [0, 1/2]
  have hes : (Qn : ℝ) * T * L ≤ Real.exp s := by
    have h := Real.exp_le_exp.mpr hs1
    rw [ellK, ← hL, Real.exp_log hQTL] at h
    exact h
  have hΔ0 : 0 ≤ T * L / (2 * Real.exp s) := by positivity
  have hΔ1 : T * L / (2 * Real.exp s) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : T * L ≤ (Qn : ℝ) * T * L := by
      have h1 : (1 : ℝ) ≤ Qn := by linarith
      nlinarith [mul_pos (by linarith : (0 : ℝ) < T) hL0]
    linarith
  -- log X = λℒ
  have hlogX : Real.log (Xlam lam (Qn : ℝ) T) = lam * L := by rw [Xlam, ← hL, Real.log_exp]
  have hX1 : 1 ≤ Xlam lam (Qn : ℝ) T := by
    rw [Xlam]; exact Real.one_le_exp (by rw [← hL]; nlinarith)
  have step1 := K6.integral_short_le_l2sq ⌊Xlam lam (Qn : ℝ) T⌋₊
    (fun n => aPrime T s (R0 (Qn : ℝ) T s) n - K6.asmooth T s (R0 (Qn : ℝ) T s) n) _ hΔ0 hΔ1
  have step2 := K6.l2_tail T s (R0 (Qn : ℝ) T s) (Xlam lam (Qn : ℝ) T) hX1
  rw [hlogX] at step2
  -- ℒ ≤ 2 log Q
  have hL2 : L ≤ 2 * x := by
    have h1 : (Qn : ℝ) * T / (2 * Real.pi) ≤ (Qn : ℝ) * (Qn : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hTQ' hQ0.le]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hQ0.ne' hQ0.ne'] at h2
    rw [hL, Lc]
    linarith
  -- log Q ≤ T/(log Q)²
  have hx0 : 0 < x := by linarith
  have hT3 : x ^ 3 ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le hlog hre
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h
  have hfin : K₀ * (lam * L) ≤ 8 * Real.pi * K₀ * (T / (2 * Real.pi)) / x ^ 2 := by
    have e : 8 * Real.pi * K₀ * (T / (2 * Real.pi)) / x ^ 2 = 4 * K₀ * (T / x ^ 2) := by
      field_simp
      ring
    rw [e]
    have hTx : x ≤ T / x ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h1 : lam * L ≤ 4 * x := by nlinarith
    have h2 : K₀ * (lam * L) ≤ K₀ * (4 * x) := mul_le_mul_of_nonneg_left h1 hK₀0
    have h3 : K₀ * (4 * x) ≤ 4 * K₀ * (T / x ^ 2) := by nlinarith
    linarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = K₀ * (lam * L) := by rw [hK₀]
    _ ≤ _ := hfin

end LemmaK
end ZetaShell
