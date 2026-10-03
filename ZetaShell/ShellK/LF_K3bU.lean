/-
K3b-U (L7_3, round 8): the first brick of K3b. It is also the generic Abel step that K3 reuses.
* `mertens_of_majorant` (generic): for ANY `h` with a `C¹` majorant `F` on `[0, L]` (`|F′| ≤ 2M`, `F ≥ 0`, `F = 0`
  beyond `L + 2`):
    `Σ_{n ≤ 𝒳} (Λ(n)²/n)·h(log n) ≤ ∫₀^{L+2} F(y)·y + M(2|C₀| + 10)(L + 2)²`.
  This is `mertens_hsup`'s Abel step with `hsupP` replaced by any `h`.
* `GW g L = g + 2(1 − st(y − L))`: `C¹`, `|GW′| ≤ 2 + 2S`, `GW = g + 2` on `(−∞, L]`, `GW = 0` beyond `L + 1`
  when `g = 0` beyond `L`.
* `wholeLine_upper`: the whole-line upper evaluation, with NO jump, so `M = 1 + S` and the Abel error is
  `O(ℒ²)`, i.e. a relative error `O(1/ℒ)`:
    `∫ g‖a‖² ≤ (1/4π²)(2πT(∫₀^{L+2} GW·y + (1 + S)(2|C₀| + 10)(L + 2)²) + 8aL·Σ_{n≤𝒳} Λ(n)²/n)`.
-/
import ZetaShell.ShellK.LF_Mertens
import ZetaShell.ShellK.LF_MajConstr3

noncomputable section
open scoped BigOperators
open scoped ArithmeticFunction
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.Payoff ZetaQ.FrobAssembly

/-- **Generic Abel step** (from `mertens_hsup`, with `hsupP` replaced by any `h`). -/
theorem mertens_of_majorant (P : ParamsQ) {C₀ : ℝ}
    (hC₀ : ∀ t : ℝ, 2 ≤ t → |(∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n) k)
      - Real.log t ^ 2 / 2| ≤ C₀ * Real.log t)
    (hL' : (8 : ℝ) ≤ P.LB + 2) (h F : ℝ → ℝ) (M : ℝ) (hM0 : 0 < M) (hFd : Differentiable ℝ F)
    (hFc : Continuous (deriv F)) (hFb : ∀ y, |deriv F y| ≤ 2 * M) (hF0L : ∀ y, P.LB + 2 ≤ y → F y = 0)
    (hF0 : ∀ y, 0 ≤ F y) (hdom : ∀ y, 0 ≤ y → y ≤ P.LB → h y ≤ F y) :
    ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * h (Real.log (n : ℝ))
      ≤ (∫ y in (0 : ℝ)..(P.LB + 2), F y * y) + M * ((2 * |C₀| + 10) * (P.LB + 2) ^ 2) := by
  have hderiv : deriv (fun y => F y / M) = fun y => deriv F y / M := by
    funext y; exact deriv_div_const M
  have hgd : Differentiable ℝ (fun y => F y / M) := hFd.div_const M
  have hgc : Continuous (deriv (fun y => F y / M)) := by rw [hderiv]; exact hFc.div_const M
  have hgb : ∀ y, |deriv (fun y => F y / M) y| ≤ 2 := by
    intro y
    rw [hderiv]
    show |deriv F y / M| ≤ 2
    rw [abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
    linarith [hFb y]
  have hgs : ∀ y, P.LB + 2 ≤ y → F y / M = 0 := fun y hy => by rw [hF0L y hy, zero_div]
  have hab := Zeta23.ThmD.abel_sum_close (c := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n)
    (by simp) (by simp [ArithmeticFunction.vonMangoldt_apply_one]) hC₀ (P.LB + 2) (Real.exp (P.LB + 2))
    (fun y => F y / M) hL' rfl hgd hgc hgb hgs
  have e1 : (∑ n ∈ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)),
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n) n * (fun y => F y / M) (Real.log n))
      = (∑ n ∈ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)),
          (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ))) / M := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only
    ring
  have e2 : (∫ y in (0 : ℝ)..(P.LB + 2), (fun y => F y / M) y * y)
      = (∫ y in (0 : ℝ)..(P.LB + 2), F y * y) / M := by
    rw [← intervalIntegral.integral_div]
    congr 1
    funext y
    simp only
    ring
  rw [e1, e2] at hab
  have hab2 : (∑ n ∈ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)),
        (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ)))
      ≤ (∫ y in (0 : ℝ)..(P.LB + 2), F y * y) + M * ((2 * |C₀| + 10) * (P.LB + 2) ^ 2) := by
    have h := (abs_le.mp hab).2
    rw [← sub_div, div_le_iff₀ hM0] at h
    linarith
  have hterm : ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * h (Real.log (n : ℝ))
      ≤ ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊ := hn
    rw [Finset.mem_Ioc] at hn'
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'.1
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hnX : (n : ℝ) ≤ P.XQ := le_trans (by exact_mod_cast hn'.2) (Nat.floor_le (Real.exp_pos _).le)
    have hlogL : Real.log (n : ℝ) ≤ P.LB := by
      have := Real.log_le_log (by linarith) hnX
      rwa [show P.XQ = Real.exp P.LB from rfl, Real.log_exp] at this
    exact mul_le_mul_of_nonneg_left (hdom _ hlog0 hlogL) (by positivity)
  have hsub : primeRangeQ P ⊆ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)) := by
    intro n hn
    have hn' : n ∈ Finset.Ioc 0 ⌊P.XQ⌋₊ := hn
    show n ∈ Finset.Ioc 0 ⌊Real.exp (P.LB + 2)⌋₊
    rw [Finset.mem_Ioc] at hn' ⊢
    refine ⟨hn'.1, le_trans hn'.2 (Nat.floor_le_floor ?_)⟩
    show Real.exp P.LB ≤ Real.exp (P.LB + 2)
    exact Real.exp_le_exp.mpr (by linarith)
  have henl : ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ))
      ≤ ∑ n ∈ Zeta23.PrimeSide.primeRange (Real.exp (P.LB + 2)),
          (Λ n : ℝ) ^ 2 / (n : ℝ) * F (Real.log (n : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg (by positivity) (hF0 _))
  linarith

/-- the jump-free window majorant `g + 2(1 − st(y − L))`. -/
def GW (g : ℝ → ℝ) (L : ℝ) (y : ℝ) : ℝ := g y + 2 * (1 - Real.smoothTransition (y - L))

theorem GW_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (L : ℝ) : ContDiff ℝ 1 (GW g L) := by
  have hE : ContDiff ℝ 1 (fun y => Real.smoothTransition (y - L)) :=
    st_contDiff.comp (contDiff_id.sub contDiff_const)
  exact hg.add (contDiff_const.mul (contDiff_const.sub hE))

theorem GW_deriv_abs_le {g : ℝ → ℝ} (hgd : Differentiable ℝ g) (hg' : ∀ y, |deriv g y| ≤ 2) {L S : ℝ}
    (hS : ∀ x, |deriv Real.smoothTransition x| ≤ S) (y : ℝ) : |deriv (GW g L) y| ≤ 2 * (1 + S) := by
  have h1 := (st_hasDerivAt (y - L)).comp y ((hasDerivAt_id' y).sub_const L)
  have hE : HasDerivAt (GW g L) (deriv g y + 2 * -(deriv Real.smoothTransition (y - L) * 1)) y :=
    (hgd y).hasDerivAt.add ((h1.const_sub 1).const_mul 2)
  rw [hE.deriv]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_neg, mul_one, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have := hS (y - L)
  linarith [hg' y]

/-- **K3b-U.** The whole-line upper evaluation of `∫ g‖a‖²` (no jump). -/
theorem wholeLine_upper (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) {C₀ : ℝ}
    (hC₀ : ∀ t : ℝ, 2 ≤ t → |(∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n) k)
      - Real.log t ^ 2 / 2| ≤ C₀ * Real.log t)
    (hL' : (8 : ℝ) ≤ P.LB + 2) {S : ℝ} (hS : ∀ x, |deriv Real.smoothTransition x| ≤ S) :
    (∫ s, P.gQ s * normA2 P s)
      ≤ 1 / (4 * Real.pi ^ 2) * (2 * Real.pi * P.T
          * ((∫ y in (0 : ℝ)..(P.LB + 2), GW P.gQ P.LB y * y) + (1 + S) * ((2 * |C₀| + 10) * (P.LB + 2) ^ 2))
        + 8 * (P.aQ * P.LB) * ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ)) := by
  obtain ⟨hgd, hgc, hg'⟩ := gQ_deriv_facts P hP hw
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS 0)
  have hT : 0 ≤ P.T := hP.T_pos.le
  have hsm := smear_upper P hT P.gQ (fun y => P.gQ y + 2) (P.aQ * P.LB) hgd.continuous.measurable
    (fun s => hP.gQ_nonneg hw s) (fun s => hP.gQ_le_aL hw s)
    (fun s y hsy => by have := lip2_le hgd hg' s y; linarith)
  have hC1 : ContDiff ℝ 1 (GW P.gQ P.LB) := GW_contDiff (contDiff_one_iff_deriv.mpr ⟨hgd, hgc⟩) P.LB
  have hab := mertens_of_majorant P hC₀ hL' (fun y => P.gQ y + 2) (GW P.gQ P.LB) (1 + S) (by linarith)
    (hC1.differentiable one_ne_zero) (hC1.continuous_deriv le_rfl) (GW_deriv_abs_le hgd hg' hS)
    (fun y hy => by
      unfold GW
      rw [hP.gQ_eq_zero hw (by rw [abs_of_nonneg (by linarith [(mul_pos hP.lam_pos hP.LL_pos).le])]; linarith),
        Real.smoothTransition.one_of_one_le (by linarith)]
      ring)
    (fun y => by
      unfold GW
      have := Real.smoothTransition.le_one (y - P.LB)
      linarith [hP.gQ_nonneg hw y])
    (fun y _ hyL => by
      unfold GW
      rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
      norm_num)
  have hsplit : (∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ)
        * (2 * Real.pi * P.T * (P.gQ (Real.log (n : ℝ)) + 2) + 8 * (P.aQ * P.LB)))
      = 2 * Real.pi * P.T * (∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * (P.gQ (Real.log (n : ℝ)) + 2))
        + 8 * (P.aQ * P.LB) * ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hsm' : (∫ s, P.gQ s * normA2 P s)
      ≤ 1 / (4 * Real.pi ^ 2) * ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ)
          * (2 * Real.pi * P.T * (P.gQ (Real.log (n : ℝ)) + 2) + 8 * (P.aQ * P.LB)) := hsm
  rw [hsplit] at hsm'
  have hab' : ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ) * (P.gQ (Real.log (n : ℝ)) + 2)
      ≤ (∫ y in (0 : ℝ)..(P.LB + 2), GW P.gQ P.LB y * y) + (1 + S) * ((2 * |C₀| + 10) * (P.LB + 2) ^ 2) := hab
  have h2 := mul_le_mul_of_nonneg_left hab' (by positivity : (0:ℝ) ≤ 2 * Real.pi * P.T)
  have h4 : (0:ℝ) ≤ 1 / (4 * Real.pi ^ 2) := by positivity
  have h3 := mul_le_mul_of_nonneg_left (add_le_add_right h2 (8 * (P.aQ * P.LB) * ∑ n ∈ primeRangeQ P, (Λ n : ℝ) ^ 2 / (n : ℝ))) h4
  linarith

end F1c
end ShellK
end ZetaShell
