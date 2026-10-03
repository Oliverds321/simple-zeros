/-
L7_9 round 2: proof of sub-node K6d (`tails`, lem:K-P Step 4).
* The interval `[−Δ, Δ]` (`Δ ≤ 1/2`) lies in one period: `∫_{−Δ}^{Δ}|F|² ≤ ∫_0^1|F|² = ‖c‖²` (Parseval).
* `a′ − ϱa′ = (1 − ϱ)a′` vanishes for `|log n − s| ≤ 1/2`; otherwise `|D_T| ≤ 2/|log n − s|` and
  `1/u² ≤ 8/(⌊u⌋² + 1)` for `|u| > 1/2`.
* Unit blocks `⌊log n − s⌋ = k`: each block lies in `(e^{s+k−1}, e^{s+k+1}]`, where Mertens
  (`Mertens.sum_mangoldt_div_eq_log`, `|Σ_{n≤x}Λ(n)/n − log x| ≤ log 4 + 4`) gives `Σ Λ(n)/n ≤ 2 + 2(log 4 + 4)`;
  `Σ_k 1/(k² + 1) < ∞`.
* So `E₂² ≤ K₀ log 𝒳 = K₀λℒ`, and `λℒ ≤ C·U/(log Q)²` since `T = (log Q)^{r+ε}` with `r + ε ≥ 3`.
-/
import ZetaShell.LemmaK.LK9_K6_Defs
import ZetaShell.LemmaK.LK9_K5_Main

noncomputable section
open Filter Finset

namespace ZetaShell
namespace LemmaK
namespace K6

/-- Parseval on a short symmetric interval. -/
lemma integral_short_le_l2sq (N : ℕ) (c : ℕ → ℂ) (Δ : ℝ) (h0 : 0 ≤ Δ) (h1 : Δ ≤ 1 / 2) :
    ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N c β‖ ^ 2 ≤ ZetaQ.l2sq N c := by
  have hc : Continuous (fun β => ‖ZetaQ.expSum N c β‖ ^ 2) :=
    (ZetaQ.Gallagher.continuous_trig _ c).norm.pow 2
  have hper : Function.Periodic (fun β => ‖ZetaQ.expSum N c β‖ ^ 2) 1 := by
    intro β
    show ‖ZetaQ.expSum N c (β + 1)‖ ^ 2 = ‖ZetaQ.expSum N c β‖ ^ 2
    rw [show ZetaQ.expSum N c (β + 1) = ZetaQ.expSum N c β from
      ZetaQ.Gallagher.trig_periodic _ _ β]
  have hmono : ∫ β in (-Δ)..Δ, ‖ZetaQ.expSum N c β‖ ^ 2
      ≤ ∫ β in (-(1 / 2 : ℝ))..(-(1 / 2 : ℝ) + 1), ‖ZetaQ.expSum N c β‖ ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun β => by simp only [Pi.zero_apply]; exact sq_nonneg _)
      (hc.intervalIntegrable _ _)
  rw [hper.intervalIntegral_add_eq (-(1 / 2)) 0, zero_add,
    ZetaQ.Gallagher.integral_normSq_expSum] at hmono
  exact hmono

lemma inv_sq_le_floor (u : ℝ) (hu : 1 / 2 < |u|) :
    1 / u ^ 2 ≤ 8 / ((⌊u⌋ : ℝ) ^ 2 + 1) := by
  have hk1 := Int.floor_le u
  have hk2 := Int.lt_floor_add_one u
  have hsq : 1 / 4 < u ^ 2 := by
    have := sq_abs u
    nlinarith [abs_nonneg u]
  have hu2 : 0 < u ^ 2 := by linarith
  rw [div_le_div_iff₀ hu2 (by positivity)]
  rcases (show ⌊u⌋ ≥ 1 ∨ ⌊u⌋ = 0 ∨ ⌊u⌋ = -1 ∨ ⌊u⌋ ≤ -2 by omega) with h | h | h | h
  · have hk : (1 : ℝ) ≤ (⌊u⌋ : ℝ) := by exact_mod_cast h
    nlinarith
  · have hk : (⌊u⌋ : ℝ) = 0 := by exact_mod_cast h
    rw [hk]; nlinarith
  · have hk : (⌊u⌋ : ℝ) = -1 := by exact_mod_cast h
    rw [hk]; nlinarith
  · have hk : (⌊u⌋ : ℝ) ≤ -2 := by exact_mod_cast h
    nlinarith [mul_pos (sub_pos.mpr hk2) (show 0 < -(u + (⌊u⌋ : ℝ) + 1) by linarith)]

lemma rho6_eq_one {u : ℝ} (hu : |u| ≤ 1 / 2) : rho6 u = 1 := by
  unfold rho6
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma coef_bound (T s R : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖aPrime T s R n - asmooth T s R n‖ ^ 2
      ≤ (4 * Real.pi ^ 2)⁻¹ * (ArithmeticFunction.vonMangoldt n ^ 2 / n)
          * (32 * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1))) := by
  set u := Real.log n - s with hudef
  have hdiff : aPrime T s R n - asmooth T s R n = ((1 - rho6 u : ℝ) : ℂ) * aPrime T s R n := by
    unfold asmooth; push_cast; ring
  have hrhs0 : 0 ≤ (4 * Real.pi ^ 2)⁻¹ * (ArithmeticFunction.vonMangoldt n ^ 2 / n)
      * (32 * (1 / ((⌊u⌋ : ℝ) ^ 2 + 1))) := by positivity
  by_cases hu : |u| ≤ 1 / 2
  · rw [hdiff, rho6_eq_one hu, sub_self, Complex.ofReal_zero, zero_mul, norm_zero]
    exact (by norm_num : (0 : ℝ) ^ 2 = 0).trans_le hrhs0
  · rw [not_le] at hu
    have hρ0 : 0 ≤ rho6 u := le_max_left _ _
    have hρ1 : rho6 u ≤ 1 := max_le zero_le_one (min_le_left _ _)
    have h1 : ‖((1 - rho6 u : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
    have h2 : ‖aPrime T s R n‖ ≤ ‖acoef T s n‖ := by
      unfold aPrime; split_ifs
      · exact le_refl _
      · rw [norm_zero]; exact norm_nonneg _
    have hdn : ‖aPrime T s R n - asmooth T s R n‖ ≤ ‖acoef T s n‖ := by
      rw [hdiff, norm_mul]
      calc ‖((1 - rho6 u : ℝ) : ℂ)‖ * ‖aPrime T s R n‖ ≤ 1 * ‖acoef T s n‖ :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = ‖acoef T s n‖ := one_mul _
    have h3 := K5Aux.norm_acoef_sq T s n hn
    have hu0 : u ≠ 0 := by
      intro h; rw [h, abs_zero] at hu; linarith
    have hv : s - Real.log n ≠ 0 := by
      intro h; apply hu0; rw [hudef]; linarith
    have h4 := K5Aux.DT_le_two_div T _ hv
    have habs : |s - Real.log n| = |u| := by rw [hudef, abs_sub_comm]
    rw [habs] at h4
    have hupos : 0 < |u| := abs_pos.mpr hu0
    have h5 : ‖DT T (s - Real.log n)‖ ^ 2 ≤ 4 * (1 / u ^ 2) := by
      have := pow_le_pow_left₀ (norm_nonneg _) h4 2
      rw [div_pow, sq_abs] at this
      calc _ ≤ 2 ^ 2 / u ^ 2 := this
        _ = 4 * (1 / u ^ 2) := by ring
    have h6 : 4 * (1 / u ^ 2) ≤ 32 * (1 / ((⌊u⌋ : ℝ) ^ 2 + 1)) := by
      have := inv_sq_le_floor u hu
      have e : 32 * (1 / ((⌊u⌋ : ℝ) ^ 2 + 1)) = 4 * (8 / ((⌊u⌋ : ℝ) ^ 2 + 1)) := by ring
      rw [e]
      linarith
    have hc0 : 0 ≤ (4 * Real.pi ^ 2)⁻¹ * (ArithmeticFunction.vonMangoldt n ^ 2 / n) := by positivity
    calc ‖aPrime T s R n - asmooth T s R n‖ ^ 2 ≤ ‖acoef T s n‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hdn 2
      _ = (4 * Real.pi ^ 2)⁻¹ * (ArithmeticFunction.vonMangoldt n ^ 2 / n)
            * ‖DT T (s - Real.log n)‖ ^ 2 := h3
      _ ≤ (4 * Real.pi ^ 2)⁻¹ * (ArithmeticFunction.vonMangoldt n ^ 2 / n)
            * (32 * (1 / ((⌊u⌋ : ℝ) ^ 2 + 1))) :=
          mul_le_mul_of_nonneg_left (h5.trans h6) hc0

/-- one unit block `⌊log n − s⌋ = k` carries `Σ Λ(n)/n ≤ 2 + 2(log 4 + 4)`. -/
lemma fiber_mertens (M : ℕ) (s : ℝ) (k : ℤ) :
    ∑ n ∈ (Finset.Ioc 0 M).filter (fun n : ℕ => ⌊Real.log n - s⌋ = k),
        ArithmeticFunction.vonMangoldt n / (n : ℝ)
      ≤ 2 + 2 * (Real.log 4 + 4) := by
  classical
  set c₁ : ℝ := Real.log 4 + 4 with hc₁
  have hc₁0 : 0 ≤ c₁ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  set y₁ := Real.exp (s + k - 1) with hy₁
  set y₂ := Real.exp (s + k + 1) with hy₂
  have hsub : (Finset.Ioc 0 M).filter (fun n : ℕ => ⌊Real.log n - s⌋ = k)
      ⊆ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊ := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn0, _⟩, hk⟩ := hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hk1 := Int.floor_le (Real.log n - s)
    have hk2 := Int.lt_floor_add_one (Real.log n - s)
    rw [hk] at hk1 hk2
    have hexp : Real.exp (Real.log n) = n := Real.exp_log hnR
    rw [Finset.mem_Ioc]
    constructor
    · rw [Nat.floor_lt (Real.exp_pos _).le, ← hexp]
      exact Real.exp_lt_exp.mpr (by linarith)
    · apply Nat.le_floor
      rw [← hexp]
      exact Real.exp_le_exp.mpr (by linarith)
  have hab : ⌊y₁⌋₊ ≤ ⌊y₂⌋₊ := Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hnn : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) := fun n => by
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity
  have hsplit := Finset.sum_Ioc_consecutive (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ))
    (Nat.zero_le ⌊y₁⌋₊) hab
  have hFa0 : 0 ≤ ∑ n ∈ Finset.Ioc 0 ⌊y₁⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
    Finset.sum_nonneg fun n _ => hnn n
  have hblock : ∑ n ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)
      ≤ 2 + 2 * c₁ := by
    by_cases h2 : 1 ≤ y₂
    · have hM2 := (abs_le.mp (Mertens.sum_mangoldt_div_eq_log h2)).2
      rw [hy₂, Real.log_exp] at hM2
      by_cases h1 : 1 ≤ y₁
      · have hM1 := (abs_le.mp (Mertens.sum_mangoldt_div_eq_log h1)).1
        rw [hy₁, Real.log_exp] at hM1
        linarith
      · rw [not_le] at h1
        have : s + k - 1 < 0 := by
          by_contra hc; rw [not_lt] at hc
          have := Real.one_le_exp hc
          linarith
        linarith
    · rw [not_le] at h2
      have hb0 : ⌊y₂⌋₊ = 0 := Nat.floor_eq_zero.mpr h2
      have ha0 : ⌊y₁⌋₊ = 0 := by omega
      rw [ha0, hb0, Finset.Ioc_self, Finset.sum_empty]
      linarith
  calc ∑ n ∈ (Finset.Ioc 0 M).filter (fun n : ℕ => ⌊Real.log n - s⌋ = k),
        ArithmeticFunction.vonMangoldt n / (n : ℝ)
      ≤ ∑ n ∈ Finset.Ioc ⌊y₁⌋₊ ⌊y₂⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
    _ ≤ 2 + 2 * c₁ := hblock

/-- `Σ_{k ∈ ℤ} 1/(k² + 1)`. -/
def Cz : ℝ := ∑' k : ℤ, 1 / ((k : ℝ) ^ 2 + 1)

lemma summable_Cz : Summable (fun k : ℤ => 1 / ((k : ℝ) ^ 2 + 1)) := by
  have hmaj : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2 + (if k = 0 then (1 : ℝ) else 0)) :=
    (Real.summable_one_div_int_pow.mpr one_lt_two).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk, add_zero]
    have hk' : (0 : ℝ) < (k : ℝ) ^ 2 := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    exact one_div_le_one_div_of_le hk' (by linarith)

lemma weighted_sum (M : ℕ) (s : ℝ) :
    ∑ n ∈ Finset.Ioc 0 M, ArithmeticFunction.vonMangoldt n / (n : ℝ)
        * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1))
      ≤ (2 + 2 * (Real.log 4 + 4)) * Cz := by
  classical
  set g : ℕ → ℤ := fun n => ⌊Real.log n - s⌋ with hg
  set t := (Finset.Ioc 0 M).image g with ht
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := t)
    (fun n hn => Finset.mem_image_of_mem g hn)]
  have hB0 : 0 ≤ 2 + 2 * (Real.log 4 + 4) := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  calc ∑ k ∈ t, ∑ n ∈ (Finset.Ioc 0 M).filter (fun n => g n = k),
        ArithmeticFunction.vonMangoldt n / (n : ℝ) * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1))
      = ∑ k ∈ t, (1 / ((k : ℝ) ^ 2 + 1)) * ∑ n ∈ (Finset.Ioc 0 M).filter (fun n => g n = k),
          ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_filter] at hn
        have : (⌊Real.log n - s⌋ : ℝ) = (k : ℝ) := by
          have h := hn.2; simp only [hg] at h; exact_mod_cast h
        rw [this]; ring
    _ ≤ ∑ k ∈ t, (1 / ((k : ℝ) ^ 2 + 1)) * (2 + 2 * (Real.log 4 + 4)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (fiber_mertens M s k) (by positivity)
    _ = (2 + 2 * (Real.log 4 + 4)) * ∑ k ∈ t, 1 / ((k : ℝ) ^ 2 + 1) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (2 + 2 * (Real.log 4 + 4)) * Cz :=
        mul_le_mul_of_nonneg_left (summable_Cz.sum_le_tsum t (fun k _ => by positivity)) hB0

/-- the deterministic tail bound: `‖a′ − ϱa′‖² ≤ K₀ log X` with `K₀ = (4π²)⁻¹·32·(2 + 2(log 4 + 4))·Cz`. -/
lemma l2_tail (T s R X : ℝ) (hX : 1 ≤ X) :
    ZetaQ.l2sq ⌊X⌋₊ (fun n => aPrime T s R n - asmooth T s R n)
      ≤ (4 * Real.pi ^ 2)⁻¹ * 32 * (2 + 2 * (Real.log 4 + 4)) * Cz * Real.log X := by
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hc0 : 0 ≤ (4 * Real.pi ^ 2)⁻¹ * 32 := by positivity
  have hpt : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖aPrime T s R n - asmooth T s R n‖ ^ 2
      ≤ (4 * Real.pi ^ 2)⁻¹ * 32 * Real.log X
          * (ArithmeticFunction.vonMangoldt n / (n : ℝ) * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1))) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff (by linarith)).mp hn.2
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log X :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnX)
    have hw0 : 0 ≤ 1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1) := by positivity
    refine (coef_bound T s R n hn.1).trans ?_
    have hsq : ArithmeticFunction.vonMangoldt n ^ 2 ≤ Real.log X * ArithmeticFunction.vonMangoldt n := by
      nlinarith
    have hk : 0 ≤ (4 * Real.pi ^ 2)⁻¹ * 32 * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1)) / n := by positivity
    have := mul_le_mul_of_nonneg_left hsq hk
    calc (4 * Real.pi ^ 2)⁻¹ * (ArithmeticFunction.vonMangoldt n ^ 2 / n)
          * (32 * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1)))
        = (4 * Real.pi ^ 2)⁻¹ * 32 * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1)) / n
            * ArithmeticFunction.vonMangoldt n ^ 2 := by ring
      _ ≤ (4 * Real.pi ^ 2)⁻¹ * 32 * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1)) / n
            * (Real.log X * ArithmeticFunction.vonMangoldt n) := this
      _ = _ := by ring
  unfold ZetaQ.l2sq
  calc ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖aPrime T s R n - asmooth T s R n‖ ^ 2
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (4 * Real.pi ^ 2)⁻¹ * 32 * Real.log X
          * (ArithmeticFunction.vonMangoldt n / (n : ℝ) * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1))) :=
        Finset.sum_le_sum hpt
    _ = (4 * Real.pi ^ 2)⁻¹ * 32 * Real.log X * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
          (ArithmeticFunction.vonMangoldt n / (n : ℝ) * (1 / ((⌊Real.log n - s⌋ : ℝ) ^ 2 + 1))) := by
        rw [Finset.mul_sum]
    _ ≤ (4 * Real.pi ^ 2)⁻¹ * 32 * Real.log X * ((2 + 2 * (Real.log 4 + 4)) * Cz) :=
        mul_le_mul_of_nonneg_left (weighted_sum ⌊X⌋₊ s) (by positivity)
    _ = _ := by ring

end K6
end LemmaK
end ZetaShell
