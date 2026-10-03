/-
L7_12c (3 Oct 2026): Lemma 6d (lem:shell-6d), the family zone count on the `O(1/ε′)` blocks of Lemma 6c
(`Z6c_cover`), in `ℝ≥0∞`:
`W(P) = Σ_{r≤R₁} Σ*_χ Σ_ρ m_ρ ϖ_ρ(μ_r) 1[P ρ] ≤ Σ_{i ≤ ⌈1/ε′⌉} Σ_j w_j F(i, j)`
for any per-character counts `N_{r,χ}(Y)` of the `P`-zeros with `|γ| ≤ Y` whose block sums at the heights
`2^j H_i` are `≤ F(i, j)`. Also the closed form of `Σ_j w_j (2^j)^a` for `0 ≤ a ≤ 2`, `k ≥ 3`.
-/
import ZetaShell.ShellS.L12c_Shell

noncomputable section
open Complex
open scoped ENNReal

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

open Classical in
/-- the family zone count `W(P)` (`ℝ≥0∞`). -/
def L12cW (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (P : ℂ → Prop) : ℝ≥0∞ :=
  ∑ r ∈ Finset.Icc 1 (R1S Qn ε s₀), ∑ χ ∈ primChars r, (if h : r = 0 then 0 else
    haveI : NeZero r := ⟨h⟩; ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
      ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T (muR Qn K s₀ r) k ρ.1 * (if P ρ.1 then 1 else 0)))

/-- the moduli of block `i`. -/
def L12cS (Qn : ℕ) (T K ε s₀ ε' : ℝ) (i : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R1S Qn ε s₀)).filter (fun r => (r : ℝ) ≤ Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i ∧
    2 * T + 1 + muR Qn K s₀ r ≤ Hblk T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' i)

/-- **the family zone count on blocks**. -/
theorem L12c_family (Qn : ℕ) (T K ε s₀ ε' : ℝ) (k : ℕ) (P : ℂ → Prop)
    (hT : 1 ≤ T) (hK : 0 ≤ K) (hQ : 0 < (Qn : ℝ)) (hs : 0 < s₀) (hR1 : 1 ≤ (R1S Qn ε s₀ : ℝ))
    (hR1N : (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀) (hε' : 0 < ε') (hε1 : ε' ≤ 1)
    (N : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℝ) (hN0 : ∀ r χ Y, 0 ≤ N r χ Y)
    (hN : ∀ r ∈ Finset.Icc 1 (R1S Qn ε s₀), ∀ χ ∈ primChars r, ∀ (h : r ≠ 0),
      haveI : NeZero r := ⟨h⟩;
      ∀ (Y : ℝ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}), (∀ ρ ∈ s, P ρ.1 ∧ |ρ.1.im| ≤ Y) →
        ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ N r χ Y)
    (F : ℕ → ℕ → ℝ)
    (hF : ∀ i ≤ ⌈1 / ε'⌉₊, ∀ j : ℕ, ∑ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r,
      N r χ (2 ^ j * Hblk T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' i) ≤ F i j) :
    L12cW Qn T K ε s₀ k P ≤ ∑ i ∈ Finset.range (⌈1 / ε'⌉₊ + 1),
      ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (F i j) := by
  classical
  set R₁ := R1S Qn ε s₀ with hR₁
  set I := ⌈1 / ε'⌉₊ with hI
  set D : ℕ → ℝ≥0∞ := fun r => ∑ χ ∈ primChars r, (if h : r = 0 then 0 else
    haveI : NeZero r := ⟨h⟩; ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
      ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T (muR Qn K s₀ r) k ρ.1 * (if P ρ.1 then 1 else 0))) with hD
  have hW : L12cW Qn T K ε s₀ k P = ∑ r ∈ Finset.Icc 1 R₁, D r := rfl
  have hN0' : 1 < Real.exp s₀ := by have := Real.add_one_le_exp s₀; linarith
  -- step 1: cover by blocks
  have hcover : ∀ r ∈ Finset.Icc 1 R₁, ∃ i ∈ Finset.range (I + 1), r ∈ L12cS Qn T K ε s₀ ε' i := by
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    obtain ⟨i, hiI, _, hri, hHi⟩ := Z6c_cover T K (Real.exp s₀) Qn R₁ ε' hT hK hQ hN0' hR1 hR1N hε' hε1 r
      hr'.1 (by exact_mod_cast hr'.2)
    refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    unfold L12cS
    rw [Finset.mem_filter]
    exact ⟨hr, hri, hHi⟩
  have hstep1 : ∑ r ∈ Finset.Icc 1 R₁, D r ≤ ∑ i ∈ Finset.range (I + 1), ∑ r ∈ L12cS Qn T K ε s₀ ε' i, D r := by
    calc ∑ r ∈ Finset.Icc 1 R₁, D r
        ≤ ∑ r ∈ Finset.Icc 1 R₁, ∑ i ∈ Finset.range (I + 1),
            (if r ∈ L12cS Qn T K ε s₀ ε' i then D r else 0) := by
          apply Finset.sum_le_sum; intro r hr
          obtain ⟨i, hi, hri⟩ := hcover r hr
          calc D r = (if r ∈ L12cS Qn T K ε s₀ ε' i then D r else 0) := by rw [if_pos hri]
            _ ≤ _ := Finset.single_le_sum (f := fun i => if r ∈ L12cS Qn T K ε s₀ ε' i then D r else 0)
                (fun _ _ => by positivity) hi
      _ = ∑ i ∈ Finset.range (I + 1), ∑ r ∈ Finset.Icc 1 R₁,
            (if r ∈ L12cS Qn T K ε s₀ ε' i then D r else 0) := Finset.sum_comm
      _ = ∑ i ∈ Finset.range (I + 1), ∑ r ∈ L12cS Qn T K ε s₀ ε' i, D r := by
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext r
          simp only [Finset.mem_filter, L12cS]
          constructor
          · rintro ⟨_, h⟩; exact h
          · rintro h; exact ⟨h.1, h⟩
  rw [hW]
  refine hstep1.trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hiI : i ≤ I := by have := Finset.mem_range.mp hi; omega
  set Hi := Hblk T K (Real.exp s₀) Qn R₁ ε' i with hHi
  -- step 2: per character
  have hchar : ∀ r ∈ L12cS Qn T K ε s₀ ε' i, ∀ χ ∈ primChars r,
      (if h : r = 0 then 0 else haveI : NeZero r := ⟨h⟩; ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
        ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T (muR Qn K s₀ r) k ρ.1 * (if P ρ.1 then 1 else 0)))
        ≤ ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (N r χ (2 ^ j * Hi)) := by
    intro r hr χ hχ
    have hr' := Finset.mem_filter.mp hr
    have hr1 := (Finset.mem_Icc.mp hr'.1).1
    have h0 : r ≠ 0 := by omega
    rw [dif_neg h0]
    have : NeZero r := ⟨h0⟩
    have hμ : 0 ≤ muR Qn K s₀ r := by
      unfold muR; have : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero h0
      positivity
    exact L12c_shell χ T (muR Qn K s₀ r) Hi k hT hμ hr'.2.2 P (fun j => N r χ (2 ^ j * Hi))
      (fun j s hs => hN r hr'.1 χ hχ h0 (2 ^ j * Hi) s hs)
  calc ∑ r ∈ L12cS Qn T K ε s₀ ε' i, D r
      ≤ ∑ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r,
          ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (N r χ (2 ^ j * Hi)) :=
        Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun χ hχ => hchar r hr χ hχ
    _ = ∑' j : ℕ, ∑ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r,
          ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (N r χ (2 ^ j * Hi)) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        apply Finset.sum_congr rfl; intro r _
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (F i j) := by
        apply ENNReal.tsum_le_tsum; intro j
        simp_rw [← Finset.mul_sum]
        gcongr
        have : ∀ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r, ENNReal.ofReal (N r χ (2 ^ j * Hi))
            = ENNReal.ofReal (∑ χ ∈ primChars r, N r χ (2 ^ j * Hi)) := fun r _ =>
          (ENNReal.ofReal_sum_of_nonneg (fun _ _ => hN0 _ _ _)).symm
        rw [Finset.sum_congr rfl this, ← ENNReal.ofReal_sum_of_nonneg
          (fun r _ => Finset.sum_nonneg fun _ _ => hN0 _ _ _)]
        exact ENNReal.ofReal_le_ofReal (hF i hiI j)

/-- `Σ_j w_j (2^j)^a ≤ 9` for `0 ≤ a ≤ 2`, `k ≥ 3`. -/
lemma L12c_wsum (k : ℕ) (hk : 3 ≤ k) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ a) ≤ ENNReal.ofReal 9 := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : ENNReal.ofReal (L12cw k 0) * ENNReal.ofReal (((2 : ℝ) ^ 0) ^ a) = 1 := by
    simp [L12cw]
  rw [h0]
  -- the tail: w_{j+1} (2^{j+1})^a ≤ 4 (1/2)^j
  have htail : ∀ j : ℕ, ENNReal.ofReal (L12cw k (j + 1)) * ENNReal.ofReal (((2 : ℝ) ^ (j + 1)) ^ a)
      ≤ ENNReal.ofReal 4 * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    intro j
    rw [← ENNReal.ofReal_mul (L12cw_nonneg k _), ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    simp only [L12cw]
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hpow : ((2 : ℝ) ^ (j + 1)) ^ a ≤ ((2 : ℝ) ^ (j + 1)) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) ha2
    have hsq : ((2 : ℝ) ^ (j + 1)) ^ (2 : ℝ) = 4 * ((2 : ℝ) ^ j) ^ 2 := by
      rw [Real.rpow_two]; ring
    have hk' : ((2 : ℝ) ^ j)⁻¹ ^ k ≤ ((2 : ℝ) ^ j)⁻¹ ^ 3 :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h2j) hk
    have hinv : ((2 : ℝ) ^ j)⁻¹ ^ 3 * (4 * ((2 : ℝ) ^ j) ^ 2) = 4 * (1 / 2 : ℝ) ^ j := by
      field_simp
      rw [← mul_pow]; norm_num
    calc ((2 : ℝ) ^ j)⁻¹ ^ k * ((2 : ℝ) ^ (j + 1)) ^ a
        ≤ ((2 : ℝ) ^ j)⁻¹ ^ 3 * (4 * ((2 : ℝ) ^ j) ^ 2) :=
          mul_le_mul hk' (hpow.trans hsq.le) (by positivity) (by positivity)
      _ = 4 * (1 / 2 : ℝ) ^ j := hinv
  calc 1 + ∑' j : ℕ, ENNReal.ofReal (L12cw k (j + 1)) * ENNReal.ofReal (((2 : ℝ) ^ (j + 1)) ^ a)
      ≤ 1 + ∑' j : ℕ, ENNReal.ofReal 4 * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
        exact add_le_add_right (ENNReal.tsum_le_tsum htail) 1
    _ = 1 + ENNReal.ofReal 4 * ENNReal.ofReal 2 := by
        rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)), tsum_geometric_two]
    _ = ENNReal.ofReal 9 := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num)
          (by norm_num)]
        norm_num

end ShellS
end ZetaShell
