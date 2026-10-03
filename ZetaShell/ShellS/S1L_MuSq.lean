/-
S1L_MuSq (L7_5b, 1 Oct 2026): leaf `musq_window` of S1 — for `y > 0`, `K ≥ 1`:
`Σ_{y ≤ m < Ky, m ≤ R₁} μ²(m)/φ(m) ≤ D (log K + 1)`, `D = max(1, (Σ n⁻²)²)`.
Route: `μ²(m)/φ(m) ≤ 1/φ(m) = (1/m) Σ_{d|m} μ²(d)/φ(d)` (L7_11's `sum_musq_div_totient`), swap the sums
(L7_11's `divisor_sum_swap`), the harmonic window `Σ_{a ≤ j < Ka} 1/j ≤ log K + 1` (`harmonic_le_one_add_log`,
`log_add_one_le_harmonic`), and `Σ_d μ²(d)/(dφ(d)) ≤ Σ_d τ(d)/d² ≤ (Σ n⁻²)²` (L7_11's `inv_totient_le`,
`sum_tau_div_sq_le`). Uses L7_11's module, imported from the library as `ZetaShell.Lemma2.L711_MuSqPhi` (green cef9ecf).
-/
import ZetaShell.ShellS.S1_Defs
import ZetaShell.Lemma2.L711_MuSqPhi

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- the harmonic window: `Σ_{j ≤ M, a ≤ j < Ka} 1/j ≤ log K + 1` for `a > 0`, `K ≥ 1`. -/
theorem harm_window (a K : ℝ) (ha : 0 < a) (hK : 1 ≤ K) (M : ℕ) :
    ∑ j ∈ (Finset.Icc 1 M).filter (fun j : ℕ => a ≤ (j : ℝ) ∧ (j : ℝ) < K * a), (1 / (j : ℝ))
      ≤ Real.log K + 1 := by
  set A := ⌈a⌉₊ with hAdef
  set B := ⌈K * a⌉₊ with hBdef
  have hA1 : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ha).ne'
  have hsub : (Finset.Icc 1 M).filter (fun j : ℕ => a ≤ (j : ℝ) ∧ (j : ℝ) < K * a) ⊆ Finset.Ico A B := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_Ico]
    exact ⟨Nat.ceil_le.mpr hj.2.1, Nat.lt_ceil.mpr hj.2.2⟩
  have hle : ∑ j ∈ (Finset.Icc 1 M).filter (fun j : ℕ => a ≤ (j : ℝ) ∧ (j : ℝ) < K * a), (1 / (j : ℝ))
      ≤ ∑ j ∈ Finset.Ico A B, (1 / (j : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
  refine hle.trans ?_
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  rcases le_or_gt B A with hBA | hAB
  · rw [Finset.Ico_eq_empty_of_le hBA, Finset.sum_empty]; linarith
  -- harmonic numbers
  have hH : ∀ n : ℕ, ∑ j ∈ Finset.Ico 1 (n + 1), (1 / (j : ℝ)) = (harmonic n : ℝ) := by
    intro n
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [← Finset.Ico_add_one_right_eq_Icc]
    apply Finset.sum_congr rfl; intro j _; rw [one_div]
  have hcons := Finset.sum_Ico_consecutive (fun j : ℕ => 1 / (j : ℝ)) hA1 hAB.le
  have hB1 : 1 ≤ B - 1 := by omega
  have hBeq : B = (B - 1) + 1 := by omega
  have hAeq : A = (A - 1) + 1 := by omega
  have hup := harmonic_le_one_add_log (B - 1)
  have hlow := log_add_one_le_harmonic (A - 1)
  have e1 : ∑ j ∈ Finset.Ico 1 B, (1 / (j : ℝ)) = (harmonic (B - 1) : ℝ) := by
    rw [hBeq]; exact hH (B - 1)
  have e2 : ∑ j ∈ Finset.Ico 1 A, (1 / (j : ℝ)) = (harmonic (A - 1) : ℝ) := by
    rw [hAeq]; exact hH (A - 1)
  have hAa : a ≤ (A : ℝ) := Nat.le_ceil a
  have hBK : ((B - 1 : ℕ) : ℝ) ≤ K * a := by
    have h1 : (B : ℝ) < K * a + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [h2]; linarith
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA1
  have hBpos : (0 : ℝ) < ((B - 1 : ℕ) : ℝ) := by exact_mod_cast hB1
  have hlogA : Real.log ((A - 1 + 1 : ℕ) : ℝ) = Real.log A := by rw [← hAeq]
  rw [hlogA] at hlow
  have hlog1 : Real.log ((B - 1 : ℕ) : ℝ) ≤ Real.log (K * a) := Real.log_le_log hBpos hBK
  have hlog2 : Real.log a ≤ Real.log A := Real.log_le_log ha hAa
  have hlog3 : Real.log (K * a) = Real.log K + Real.log a := Real.log_mul (by linarith) ha.ne'
  linarith

theorem musq_window' : ∃ D : ℝ, 1 ≤ D ∧ ∀ (R1 : ℕ) (K : ℝ), 1 ≤ K → ∀ y : ℝ, 0 < y →
    ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
      ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) ≤ D * (Real.log K + 1) := by
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ 2 with hZ
  refine ⟨max 1 (Z ^ 2), le_max_left _ _, fun R1 K hK y hy => ?_⟩
  set g : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ) with hg
  have hg0 : ∀ d, 0 ≤ g d := fun d => by simp only [hg]; positivity
  set F : ℕ → ℕ → ℝ := fun d j => g d / d *
    (if y ≤ (d : ℝ) * j ∧ (d : ℝ) * j < K * y then 1 / (j : ℝ) else 0) with hF
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  -- step 1: each term is bounded by the divisor sum
  have h1 : ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
      ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 R1, ∑ d ∈ m.divisors, F d (m / d) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum; intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : m ≠ 0 := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    have hφ : (0 : ℝ) < (Nat.totient m : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm1
    have hterm : ∀ d ∈ m.divisors, F d (m / d)
        = (if y ≤ (m : ℝ) ∧ (m : ℝ) < K * y then 1 / (m : ℝ) else 0) * g d := by
      intro d hd
      have hdm : d * (m / d) = m := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hdmR : (d : ℝ) * ((m / d : ℕ) : ℝ) = m := by exact_mod_cast hdm
      have hd0 : (d : ℝ) ≠ 0 := by
        have : d ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_mem_divisors hd); exact_mod_cast this
      have hq0 : ((m / d : ℕ) : ℝ) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hdmR; linarith
      simp only [hF, hdmR]
      split_ifs
      · rw [← hdmR]; field_simp
      · ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, MuSqPhi.sum_musq_div_totient m hm0]
    split_ifs with h
    · have hμ : ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 ≤ 1 := by
        have : |((ArithmeticFunction.moebius m : ℤ) : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        nlinarith [abs_nonneg ((ArithmeticFunction.moebius m : ℤ) : ℝ), sq_abs ((ArithmeticFunction.moebius m : ℤ) : ℝ)]
      calc ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 / (Nat.totient m : ℝ) ≤ 1 / (Nat.totient m : ℝ) :=
            div_le_div_of_nonneg_right hμ hφ.le
        _ = 1 / (m : ℝ) * ((m : ℝ) / (Nat.totient m : ℝ)) := by field_simp
    · simp
  rw [MuSqPhi.divisor_sum_swap] at h1
  -- step 3: the inner (harmonic) sums
  have h3 : ∀ d ∈ Finset.Icc 1 R1, ∑ j ∈ Finset.Icc 1 (R1 / d), F d j ≤ g d / d * (Real.log K + 1) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    simp only [hF]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (hg0 d) hdpos.le)
    rw [← Finset.sum_filter]
    have hfilt : (Finset.Icc 1 (R1 / d)).filter (fun j : ℕ => y ≤ (d : ℝ) * j ∧ (d : ℝ) * j < K * y)
        = (Finset.Icc 1 (R1 / d)).filter (fun j : ℕ => y / d ≤ (j : ℝ) ∧ (j : ℝ) < K * (y / d)) := by
      apply Finset.filter_congr
      intro j _
      rw [div_le_iff₀ hdpos, mul_comm (j : ℝ) d, ← mul_div_assoc, lt_div_iff₀ hdpos, mul_comm (j : ℝ) d]
    rw [hfilt]
    exact harm_window (y / d) K (div_pos hy hdpos) hK (R1 / d)
  -- step 4: Σ μ²(d)/(dφ(d)) ≤ Z²
  have h4 : ∑ d ∈ Finset.Icc 1 R1, g d / d ≤ Z ^ 2 := by
    refine le_trans (Finset.sum_le_sum (fun d hd => ?_)) (MuSqPhi.sum_tau_div_sq_le R1)
    have hd0 : d ≠ 0 := by rw [Finset.mem_Icc] at hd; omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have hμ : ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 ≤ 1 := by
      have : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [abs_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ), sq_abs ((ArithmeticFunction.moebius d : ℤ) : ℝ)]
    have hφ := MuSqPhi.inv_totient_le d hd0
    simp only [hg]
    calc ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / (Nat.totient d : ℝ) / d ≤ 1 / (Nat.totient d : ℝ) / d := by
          apply div_le_div_of_nonneg_right _ hdR.le
          exact div_le_div_of_nonneg_right hμ (by positivity)
      _ ≤ (d.divisors.card : ℝ) / d / d := div_le_div_of_nonneg_right hφ hdR.le
      _ = (d.divisors.card : ℝ) / (d : ℝ) ^ 2 := by field_simp
  have hK1 : 0 ≤ Real.log K + 1 := by linarith
  calc ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
        ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 R1, ∑ j ∈ Finset.Icc 1 (R1 / d), F d j := h1
    _ ≤ ∑ d ∈ Finset.Icc 1 R1, g d / d * (Real.log K + 1) := Finset.sum_le_sum h3
    _ = (∑ d ∈ Finset.Icc 1 R1, g d / d) * (Real.log K + 1) := by rw [Finset.sum_mul]
    _ ≤ Z ^ 2 * (Real.log K + 1) := mul_le_mul_of_nonneg_right h4 hK1
    _ ≤ max 1 (Z ^ 2) * (Real.log K + 1) := mul_le_mul_of_nonneg_right (le_max_right _ _) hK1

end ShellS
end ZetaShell
