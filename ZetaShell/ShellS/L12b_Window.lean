/-
L7_12c (3 Oct 2026): unit-window sums for Lemma 6a (lem:shell-6a, sec_shell.tex l.655–665: "Group zeros into unit
windows ... Schur's test with the summable kernel `(1+|m−m'|)^{−A}`").
Abstract setting: a finite family `s` with ordinates `γ`, weights `m ≥ 0`, and a window count
`Σ_{ρ∈s', t<γ≤t+1} m ≤ ℓ(t) := a + c log(|t|+3)` for every `s' ⊆ s`. Then, for every `γ₀`,
* (S) `Σ_{ρ∈s} m_ρ (1+|γ₀−γ_ρ|)^{−2} ≤ cW · ℓ(γ₀)`;
* (U) `Σ_{ρ∈s} m_ρ (1+|γ₀−γ_ρ|)^{−2} / ℓ(γ_ρ) ≤ cW`,
with one absolute constant `cW` (a convergent series over `ℤ`). Mathlib only.
-/
import Mathlib

noncomputable section

namespace ZetaShell
namespace ShellS

/-- the window weight `w(k) = max(1,|k|)^{−2}`. -/
def L12bW (k : ℤ) : ℝ := 1 / max 1 |(k : ℝ)| ^ 2

/-- `g(k) = w(k)(1 + log(|k|+2))`. -/
def L12bG (k : ℤ) : ℝ := L12bW k * (1 + Real.log (|(k : ℝ)| + 2))

lemma L12bW_nonneg (k : ℤ) : 0 ≤ L12bW k := by unfold L12bW; positivity

lemma L12bW_le_G (k : ℤ) : L12bW k ≤ L12bG k := by
  unfold L12bG
  have h1 : 0 ≤ Real.log (|(k : ℝ)| + 2) := Real.log_nonneg (by linarith [abs_nonneg (k : ℝ)])
  have h2 := L12bW_nonneg k
  nlinarith

lemma L12bG_nonneg (k : ℤ) : 0 ≤ L12bG k := (L12bW_nonneg k).trans (L12bW_le_G k)

/-- `1 + log(x+2) ≤ 5 √x` for `x ≥ 1`. -/
lemma L12b_one_add_log_le (x : ℝ) (hx : 1 ≤ x) : 1 + Real.log (x + 2) ≤ 5 * Real.sqrt x := by
  have h1 : Real.log (x + 2) ≤ (x + 2) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have hs : Real.sqrt (x + 2) ≤ Real.sqrt 3 * Real.sqrt x := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have h3 : Real.sqrt 3 ≤ 7 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsx : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  have hsx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have : Real.sqrt (x + 2) ≤ 7 / 4 * Real.sqrt x := hs.trans (mul_le_mul_of_nonneg_right h3 hsx0)
  linarith

lemma L12bG_summable : Summable L12bG := by
  have hA : Summable (fun k : ℤ => 5 * |(k : ℝ)| ^ (-(3 / 2 : ℝ))) :=
    (Real.summable_abs_int_rpow (b := 3 / 2) (by norm_num)).mul_left 5
  have hB : Summable (fun k : ℤ => if k = 0 then (2 : ℝ) else 0) := (hasSum_ite_eq (0 : ℤ) (2 : ℝ)).summable
  refine Summable.of_nonneg_of_le L12bG_nonneg (fun k => ?_) (hA.add hB)
  by_cases hk : k = 0
  · subst hk
    simp only [L12bG, L12bW, Int.cast_zero, abs_zero, if_true]
    have hl : Real.log (0 + 2) ≤ 1 := by
      rw [zero_add]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h0 : (0 : ℝ) ≤ 5 * |(0 : ℝ)| ^ (-(3 / 2 : ℝ)) := by positivity
    norm_num at hl h0 ⊢
    linarith
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
    simp only [hk, if_false, add_zero]
    unfold L12bG L12bW
    rw [max_eq_right hk1]
    set x := |(k : ℝ)| with hx
    have hx0 : 0 < x := by linarith
    have hlog := L12b_one_add_log_le x hk1
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hrp : x ^ (-(3 / 2 : ℝ)) = 1 / (x * Real.sqrt x) := by
      rw [Real.rpow_neg hx0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one,
        ← Real.sqrt_eq_rpow, one_div]
    rw [hrp]
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    calc 1 + Real.log (x + 2) ≤ 5 * Real.sqrt x := hlog
      _ = 5 * (1 / (x * Real.sqrt x)) * x ^ 2 := by
          field_simp
          rw [Real.sq_sqrt hx0.le]

/-- the absolute constant `cW = Σ_{k∈ℤ} w(k)(1 + log(|k|+2))`. -/
def L12bcW : ℝ := ∑' k : ℤ, L12bG k

lemma L12bcW_nonneg : 0 ≤ L12bcW := tsum_nonneg L12bG_nonneg

lemma L12b_sumG_le (F : Finset ℤ) : ∑ k ∈ F, L12bG k ≤ L12bcW :=
  L12bG_summable.sum_le_tsum F (fun k _ => L12bG_nonneg k)

/-- **general window sum** (finite form): group by the key `⌈γ − γ₀⌉`. -/
lemma L12b_window_sum {ι : Type*} (s : Finset ι) (γ m F : ι → ℝ) (Λ : ℝ → ℝ) (Φ : ℤ → ℝ) (γ₀ : ℝ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hF : ∀ ρ ∈ s, F ρ ≤ Φ ⌈γ ρ - γ₀⌉) (hΦ : ∀ k, 0 ≤ Φ k)
    (hcount : ∀ t : ℝ, ∀ s' : Finset ι, s' ⊆ s → (∀ ρ ∈ s', t < γ ρ ∧ γ ρ ≤ t + 1) →
      ∑ ρ ∈ s', m ρ ≤ Λ t) :
    ∑ ρ ∈ s, m ρ * F ρ ≤ ∑ k ∈ s.image (fun ρ => ⌈γ ρ - γ₀⌉), Φ k * Λ (γ₀ + k - 1) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ρ => ⌈γ ρ - γ₀⌉)
    (t := s.image (fun ρ => ⌈γ ρ - γ₀⌉)) (fun ρ hρ => Finset.mem_image_of_mem _ hρ)]
  apply Finset.sum_le_sum
  intro k _
  calc ∑ ρ ∈ s with ⌈γ ρ - γ₀⌉ = k, m ρ * F ρ ≤ ∑ ρ ∈ s with ⌈γ ρ - γ₀⌉ = k, m ρ * Φ k := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        apply mul_le_mul_of_nonneg_left _ (hm ρ hρ.1)
        have h := hF ρ hρ.1
        rw [hρ.2] at h
        exact h
    _ = Φ k * ∑ ρ ∈ s with ⌈γ ρ - γ₀⌉ = k, m ρ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ ≤ Φ k * Λ (γ₀ + k - 1) := by
        apply mul_le_mul_of_nonneg_left _ (hΦ k)
        apply hcount _ _ (Finset.filter_subset _ _)
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        have h := Int.ceil_eq_iff.mp hρ.2
        constructor <;> linarith [h.1, h.2]

/-- `1 + |γ₀ − γ| ≥ max(1, |⌈γ − γ₀⌉|)`. -/
lemma L12b_max_le (γ γ₀ : ℝ) : max 1 |((⌈γ - γ₀⌉ : ℤ) : ℝ)| ≤ 1 + |γ₀ - γ| := by
  have h := Int.ceil_eq_iff.mp (rfl : ⌈γ - γ₀⌉ = ⌈γ - γ₀⌉)
  set k := ⌈γ - γ₀⌉
  apply max_le (by linarith [abs_nonneg (γ₀ - γ)])
  rcases le_or_gt (k : ℝ) 0 with hk | hk
  · rw [abs_of_nonpos hk]
    have : -(k : ℝ) ≤ |γ₀ - γ| := le_trans (by linarith [h.2]) (le_abs_self _)
    linarith
  · rw [abs_of_pos hk]
    have : (k : ℝ) - 1 ≤ |γ₀ - γ| := by
      rw [abs_sub_comm]; exact le_trans h.1.le (le_abs_self _)
    linarith

/-- the kernel bound `(1+|γ₀−γ|)^{−2} ≤ w(⌈γ−γ₀⌉)`. -/
lemma L12b_kernel_le (γ γ₀ : ℝ) : 1 / (1 + |γ₀ - γ|) ^ 2 ≤ L12bW ⌈γ - γ₀⌉ := by
  unfold L12bW
  have h := L12b_max_le γ γ₀
  have h1 : (0 : ℝ) < max 1 |((⌈γ - γ₀⌉ : ℤ) : ℝ)| := lt_of_lt_of_le one_pos (le_max_left _ _)
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ h1.le h 2

/-- the window count `ℓ(t) = a + c log(|t|+3)`. -/
def L12bL (a c t : ℝ) : ℝ := a + c * Real.log (|t| + 3)

lemma L12b_log3_ge_one (t : ℝ) : 1 ≤ Real.log (|t| + 3) := by
  have he : Real.exp 1 ≤ |t| + 3 := by linarith [Real.exp_one_lt_d9, abs_nonneg t]
  have := Real.log_le_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

lemma L12bL_nonneg (a c t : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) : 0 ≤ L12bL a c t := by
  unfold L12bL; have := L12b_log3_ge_one t; positivity

lemma L12bL_pos (a c t : ℝ) (ha : 0 ≤ a) (hc : 0 < c) : 0 < L12bL a c t := by
  unfold L12bL; have := L12b_log3_ge_one t; positivity

/-- `ℓ(γ₀ + k − 1) ≤ ℓ(γ₀)(1 + log(|k|+2))`. -/
lemma L12bL_shift (a c γ₀ : ℝ) (k : ℤ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    L12bL a c (γ₀ + k - 1) ≤ L12bL a c γ₀ * (1 + Real.log (|(k : ℝ)| + 2)) := by
  unfold L12bL
  have hk2 : 0 < |(k : ℝ)| + 2 := by positivity
  have hg3 : 0 < |γ₀| + 3 := by positivity
  have h1 : |γ₀ + k - 1| + 3 ≤ (|γ₀| + 3) * (|(k : ℝ)| + 2) := by
    have h0 : |γ₀ + k - 1| ≤ |γ₀| + |(k : ℝ)| + 1 := by
      have h5 := abs_sub (γ₀ + k) 1
      have h6 := abs_add_le γ₀ (k : ℝ)
      rw [abs_one] at h5
      linarith
    nlinarith [abs_nonneg γ₀, abs_nonneg (k : ℝ), mul_nonneg (abs_nonneg γ₀) (abs_nonneg (k : ℝ))]
  have h2 : Real.log (|γ₀ + k - 1| + 3) ≤ Real.log (|γ₀| + 3) + Real.log (|(k : ℝ)| + 2) := by
    rw [← Real.log_mul hg3.ne' hk2.ne']
    exact Real.log_le_log (by positivity) h1
  have hl1 := L12b_log3_ge_one γ₀
  have hlk : 0 ≤ Real.log (|(k : ℝ)| + 2) := Real.log_nonneg (by linarith [abs_nonneg (k : ℝ)])
  nlinarith [mul_le_mul_of_nonneg_left h2 hc, mul_nonneg ha hlk, mul_nonneg hc hlk,
    mul_le_mul_of_nonneg_left hl1 (mul_nonneg hc hlk)]

/-- **(S)**: `Σ_{ρ∈s} m (1+|γ₀−γ|)^{−2} ≤ cW ℓ(γ₀)`. -/
theorem L12b_WS {ι : Type*} (s : Finset ι) (γ m : ι → ℝ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ)
    (hcount : ∀ t : ℝ, ∀ s' : Finset ι, s' ⊆ s → (∀ ρ ∈ s', t < γ ρ ∧ γ ρ ≤ t + 1) →
      ∑ ρ ∈ s', m ρ ≤ L12bL a c t) (γ₀ : ℝ) :
    ∑ ρ ∈ s, m ρ * (1 / (1 + |γ₀ - γ ρ|) ^ 2) ≤ L12bcW * L12bL a c γ₀ := by
  have h := L12b_window_sum s γ m (fun ρ => 1 / (1 + |γ₀ - γ ρ|) ^ 2) (L12bL a c) L12bW γ₀ hm
    (fun ρ _ => L12b_kernel_le (γ ρ) γ₀) L12bW_nonneg hcount
  refine h.trans ?_
  have hL0 := L12bL_nonneg a c γ₀ ha hc
  calc ∑ k ∈ s.image (fun ρ => ⌈γ ρ - γ₀⌉), L12bW k * L12bL a c (γ₀ + k - 1)
      ≤ ∑ k ∈ s.image (fun ρ => ⌈γ ρ - γ₀⌉), L12bL a c γ₀ * L12bG k := by
        apply Finset.sum_le_sum
        intro k _
        have := L12bL_shift a c γ₀ k ha hc
        unfold L12bG
        calc L12bW k * L12bL a c (γ₀ + k - 1)
            ≤ L12bW k * (L12bL a c γ₀ * (1 + Real.log (|(k : ℝ)| + 2))) :=
              mul_le_mul_of_nonneg_left this (L12bW_nonneg k)
          _ = _ := by ring
    _ = L12bL a c γ₀ * ∑ k ∈ s.image (fun ρ => ⌈γ ρ - γ₀⌉), L12bG k := by rw [Finset.mul_sum]
    _ ≤ L12bL a c γ₀ * L12bcW := mul_le_mul_of_nonneg_left (L12b_sumG_le _) hL0
    _ = L12bcW * L12bL a c γ₀ := mul_comm _ _

/-- `ℓ(t) ≤ 2ℓ(γ)` for `t < γ ≤ t + 1`. -/
lemma L12bL_window (a c t γ : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (h1 : t < γ) (h2 : γ ≤ t + 1) :
    L12bL a c t ≤ 2 * L12bL a c γ := by
  unfold L12bL
  have hg3 : 0 < |γ| + 3 := by positivity
  have ht : |t| + 3 ≤ 4 / 3 * (|γ| + 3) := by
    have : |t| ≤ |γ| + 1 := by
      have h3 : |t - γ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have := abs_sub_abs_le_abs_sub t γ
      linarith
    nlinarith [abs_nonneg γ]
  have h4 : Real.log (|t| + 3) ≤ Real.log (4 / 3) + Real.log (|γ| + 3) := by
    rw [← Real.log_mul (by norm_num) hg3.ne']
    exact Real.log_le_log (by positivity) ht
  have h43 : Real.log (4 / 3) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num); linarith
  have hl1 := L12b_log3_ge_one γ
  nlinarith [mul_le_mul_of_nonneg_left h4 hc, mul_le_mul_of_nonneg_left h43 hc,
    mul_le_mul_of_nonneg_left hl1 hc]

/-- **(U)**: `Σ_{ρ∈s} m (1+|γ₀−γ|)^{−2}/ℓ(γ) ≤ 2 cW`. -/
theorem L12b_WU {ι : Type*} (s : Finset ι) (γ m : ι → ℝ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 < c)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ)
    (hcount : ∀ t : ℝ, ∀ s' : Finset ι, s' ⊆ s → (∀ ρ ∈ s', t < γ ρ ∧ γ ρ ≤ t + 1) →
      ∑ ρ ∈ s', m ρ ≤ L12bL a c t) (γ₀ : ℝ) :
    ∑ ρ ∈ s, m ρ * (1 / (1 + |γ₀ - γ ρ|) ^ 2 / L12bL a c (γ ρ)) ≤ 2 * L12bcW := by
  set Φ : ℤ → ℝ := fun k => 2 * L12bW k / L12bL a c (γ₀ + k - 1) with hΦ
  have hF : ∀ ρ ∈ s, 1 / (1 + |γ₀ - γ ρ|) ^ 2 / L12bL a c (γ ρ) ≤ Φ ⌈γ ρ - γ₀⌉ := by
    intro ρ _
    have hk := Int.ceil_eq_iff.mp (rfl : ⌈γ ρ - γ₀⌉ = ⌈γ ρ - γ₀⌉)
    have hw := L12bL_window a c (γ₀ + ⌈γ ρ - γ₀⌉ - 1) (γ ρ) ha hc.le (by linarith [hk.1]) (by linarith [hk.2])
    have hLγ := L12bL_pos a c (γ ρ) ha hc
    have hLt := L12bL_pos a c (γ₀ + ⌈γ ρ - γ₀⌉ - 1) ha hc
    have hker := L12b_kernel_le (γ ρ) γ₀
    simp only [hΦ]
    rw [div_le_div_iff₀ hLγ hLt]
    have hW0 := L12bW_nonneg ⌈γ ρ - γ₀⌉
    have hk0 : 0 ≤ 1 / (1 + |γ₀ - γ ρ|) ^ 2 := by positivity
    calc 1 / (1 + |γ₀ - γ ρ|) ^ 2 * L12bL a c (γ₀ + ↑⌈γ ρ - γ₀⌉ - 1)
        ≤ L12bW ⌈γ ρ - γ₀⌉ * (2 * L12bL a c (γ ρ)) := mul_le_mul hker hw hLt.le hW0
      _ = 2 * L12bW ⌈γ ρ - γ₀⌉ * L12bL a c (γ ρ) := by ring
  have hΦ0 : ∀ k, 0 ≤ Φ k := fun k => by
    simp only [hΦ]; have := L12bL_pos a c (γ₀ + k - 1) ha hc; have := L12bW_nonneg k; positivity
  have h := L12b_window_sum s γ m _ (L12bL a c) Φ γ₀ hm hF hΦ0 hcount
  refine h.trans ?_
  calc ∑ k ∈ s.image (fun ρ => ⌈γ ρ - γ₀⌉), Φ k * L12bL a c (γ₀ + k - 1)
      = ∑ k ∈ s.image (fun ρ => ⌈γ ρ - γ₀⌉), 2 * L12bW k := by
        apply Finset.sum_congr rfl
        intro k _
        have := L12bL_pos a c (γ₀ + k - 1) ha hc
        simp only [hΦ]; field_simp
    _ ≤ ∑ k ∈ s.image (fun ρ => ⌈γ ρ - γ₀⌉), 2 * L12bG k :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (L12bW_le_G k) (by norm_num)
    _ = 2 * ∑ k ∈ s.image (fun ρ => ⌈γ ρ - γ₀⌉), L12bG k := by rw [Finset.mul_sum]
    _ ≤ 2 * L12bcW := mul_le_mul_of_nonneg_left (L12b_sumG_le _) (by norm_num)

end ShellS
end ZetaShell
