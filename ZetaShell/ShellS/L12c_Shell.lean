/-
L7_12c (3 Oct 2026): Lemma 6d (lem:shell-6d), the per-character height-shell bound (lem:shell-6c: "up to the height
shells `2^{j−1}H_i < |γ| ≤ 2^jH_i` (where `ϖ ≪ 2^{−k(j−1)}`)"), in `ℝ≥0∞`:
for `H ≥ 2T + 1 + μ`, a zone predicate `P` and counts `N j` of the `P`-zeros with `|γ| ≤ 2^j H`,
`Σ_ρ m_ρ ϖ_ρ 1[P ρ] ≤ Σ_j w_j N_j`, `w_0 = 1`, `w_{j+1} = 2^{−jk}`.
-/
import ZetaShell.ShellS.L10_Z6c
import ZetaShell.ShellS.L12b_Char

noncomputable section
open Complex
open scoped ENNReal

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- shell weights `w_0 = 1`, `w_{j+1} = (2^j)^{−k}`. -/
def L12cw (k : ℕ) : ℕ → ℝ
  | 0 => 1
  | (j + 1) => ((2 : ℝ) ^ j)⁻¹ ^ k

lemma L12cw_nonneg (k j : ℕ) : 0 ≤ L12cw k j := by
  cases j with
  | zero => simp [L12cw]
  | succ j => simp only [L12cw]; positivity

lemma L12c_shell_pt (T μ H : ℝ) (k : ℕ) (hT : 1 ≤ T) (hμ : 0 ≤ μ) (hH : 2 * T + 1 + μ ≤ H) (ρ : ℂ) (j : ℕ)
    (hj : j = 0 ∨ (2 : ℝ) ^ (j - 1) * H < |ρ.im|) : varpi T μ k ρ ≤ L12cw k j := by
  cases j with
  | zero => simpa [L12cw] using L12b_varpi_le_one T μ k ρ hμ
  | succ j =>
    simp only [L12cw]
    rcases hj with h | h
    · exact absurd h (Nat.succ_ne_zero j)
    · simp only [Nat.add_sub_cancel] at h
      apply Z6c_shell T hT μ k j ρ hμ
      have : (2 : ℝ) ^ j * (2 * T + 1 + μ) ≤ (2 : ℝ) ^ j * H :=
        mul_le_mul_of_nonneg_left hH (by positivity)
      linarith

open Classical in
/-- **the per-character shell bound** (`ℝ≥0∞`). -/
theorem L12c_shell {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T μ H : ℝ) (k : ℕ) (hT : 1 ≤ T)
    (hμ : 0 ≤ μ) (hH : 2 * T + 1 + μ ≤ H) (P : ℂ → Prop) (N : ℕ → ℝ)
    (hN : ∀ (j : ℕ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}), (∀ ρ ∈ s, P ρ.1 ∧ |ρ.1.im| ≤ 2 ^ j * H) →
      ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ N j) :
    ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
        ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * (if P ρ.1 then 1 else 0))
      ≤ ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (N j) := by
  have hH0 : 0 < H := by linarith
  -- the shell index of a zero
  have hex : ∀ ρ : ℂ, ∃ j : ℕ, |ρ.im| ≤ 2 ^ j * H := by
    intro ρ
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (|ρ.im| / H) (by norm_num : (1 : ℝ) < 2)
    refine ⟨j, ?_⟩
    rw [div_lt_iff₀ hH0] at hj
    exact hj.le
  -- pointwise: each term is bounded by the tsum over shells
  set g : {ρ : ℂ // IsNtZero χ ρ} → ℕ → ℝ≥0∞ := fun ρ j =>
    ENNReal.ofReal (L12cw k j) * (if P ρ.1 ∧ |ρ.1.im| ≤ 2 ^ j * H then ENNReal.ofReal (zmult χ ρ.1 : ℝ) else 0)
    with hg
  have hpt : ∀ ρ : {ρ : ℂ // IsNtZero χ ρ},
      ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * (if P ρ.1 then 1 else 0)) ≤ ∑' j, g ρ j := by
    intro ρ
    by_cases hP : P ρ.1
    · set J := Nat.find (hex ρ.1) with hJ
      have hJs : |ρ.1.im| ≤ 2 ^ J * H := Nat.find_spec (hex ρ.1)
      have hJm : J = 0 ∨ (2 : ℝ) ^ (J - 1) * H < |ρ.1.im| := by
        rcases Nat.eq_zero_or_pos J with h | h
        · exact Or.inl h
        · right
          have := Nat.find_min (hex ρ.1) (show J - 1 < J by omega)
          push Not at this
          exact this
      have hv := L12c_shell_pt T μ H k hT hμ hH ρ.1 J hJm
      refine le_trans ?_ (ENNReal.le_tsum J)
      simp only [hg, if_pos hP, if_pos (And.intro hP hJs), mul_one]
      rw [← ENNReal.ofReal_mul (L12cw_nonneg k J)]
      apply ENNReal.ofReal_le_ofReal
      have hm : (0 : ℝ) ≤ zmult χ ρ.1 := Nat.cast_nonneg _
      calc (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 ≤ (zmult χ ρ.1 : ℝ) * L12cw k J :=
            mul_le_mul_of_nonneg_left hv hm
        _ = L12cw k J * (zmult χ ρ.1 : ℝ) := mul_comm _ _
    · simp [hP]
  calc ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
        ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * (if P ρ.1 then 1 else 0))
      ≤ ∑' ρ, ∑' j, g ρ j := ENNReal.tsum_le_tsum hpt
    _ = ∑' j, ∑' ρ, g ρ j := ENNReal.tsum_comm
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (N j) := by
        apply ENNReal.tsum_le_tsum
        intro j
        simp only [hg]
        rw [ENNReal.tsum_mul_left]
        gcongr
        rw [ENNReal.tsum_eq_iSup_sum]
        apply iSup_le
        intro s
        rw [← Finset.sum_filter]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        apply hN j
        intro ρ hρ
        exact (Finset.mem_filter.mp hρ).2

end ShellS
end ZetaShell
