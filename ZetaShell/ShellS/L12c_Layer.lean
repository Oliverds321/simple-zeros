/-
L7_12c (3 Oct 2026): Lemma 6d (lem:shell-6d), the layer-cake bookkeeping in `ℝ≥0∞`:
* `L12cWg g = Σ_{r≤R₁} Σ*_χ Σ_ρ m_ρ ϖ_ρ(μ_r) g(ρ)` (so `L12cW P = L12cWg 1_P`);
* domination: `g ≤ Σ_j c_j h_j` on `0 < β < 1` gives `L12cWg g ≤ Σ_j c_j L12cWg h_j`;
* `ofReal (nearSum) ≤ L12cWg (1[x_ρ ≤ X₀] e^{−x_ρ})`, `ofReal (restSq) ≤ L12cWg (1[x_ρ > X₀] e^{−2x_ρ})`.
-/
import ZetaShell.ShellS.L12c_Zones

noncomputable section
open Complex
open scoped ENNReal

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- `Σ_{r≤R₁} Σ*_χ Σ_ρ m_ρ ϖ_ρ(μ_r) g(ρ)` in `ℝ≥0∞`. -/
def L12cWg (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (g : ℂ → ℝ) : ℝ≥0∞ :=
  ∑ r ∈ Finset.Icc 1 (R1S Qn ε s₀), ∑ χ ∈ primChars r, (if h : r = 0 then 0 else
    haveI : NeZero r := ⟨h⟩; ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
      ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T (muR Qn K s₀ r) k ρ.1 * g ρ.1))

open Classical in
lemma L12cW_eq (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (P : ℂ → Prop) :
    L12cW Qn T K ε s₀ k P = L12cWg Qn T K ε s₀ k (fun ρ => if P ρ then 1 else 0) := rfl

lemma L12c_muR_nonneg (Qn : ℕ) (K s₀ : ℝ) (hK : 0 ≤ K) (r : ℕ) : 0 ≤ muR Qn K s₀ r :=
  div_nonneg (mul_nonneg hK (Real.exp_pos _).le) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- per character domination. -/
lemma L12c_char_dom {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T μ : ℝ) (k : ℕ) (hμ : 0 ≤ μ)
    (g : ℂ → ℝ) {ι : Type*} (J : Finset ι) (c : ι → ℝ) (h : ι → ℂ → ℝ) (hc : ∀ j ∈ J, 0 ≤ c j)
    (hh : ∀ j ∈ J, ∀ ρ : ℂ, 0 ≤ h j ρ)
    (hg : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → g ρ ≤ ∑ j ∈ J, c j * h j ρ) :
    ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * g ρ.1)
      ≤ ∑ j ∈ J, ENNReal.ofReal (c j) * ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
          ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * h j ρ.1) := by
  have hpt : ∀ ρ : {ρ : ℂ // IsNtZero χ ρ},
      ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * g ρ.1)
        ≤ ∑ j ∈ J, ENNReal.ofReal (c j) * ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * h j ρ.1) := by
    intro ρ
    have hm : 0 ≤ (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 :=
      mul_nonneg (Nat.cast_nonneg _) (varpi_nonneg0 T μ k ρ.1 hμ)
    have h1 : (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * g ρ.1
        ≤ ∑ j ∈ J, c j * ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * h j ρ.1) := by
      calc (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * g ρ.1
          ≤ (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * ∑ j ∈ J, c j * h j ρ.1 :=
            mul_le_mul_of_nonneg_left (hg ρ.1 ρ.2.2.1 ρ.2.2.2) hm
        _ = ∑ j ∈ J, c j * ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * h j ρ.1) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    calc ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * g ρ.1)
        ≤ ENNReal.ofReal (∑ j ∈ J, c j * ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * h j ρ.1)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ∑ j ∈ J, ENNReal.ofReal (c j) * ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * h j ρ.1) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (hc j hj) (mul_nonneg hm (hh j hj ρ.1)))]
          apply Finset.sum_congr rfl; intro j hj
          rw [ENNReal.ofReal_mul (hc j hj)]
  calc ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * g ρ.1)
      ≤ ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, ∑ j ∈ J,
          ENNReal.ofReal (c j) * ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * h j ρ.1) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑ j ∈ J, ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
          ENNReal.ofReal (c j) * ENNReal.ofReal ((zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1 * h j ρ.1) :=
        Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ = _ := by
        apply Finset.sum_congr rfl; intro j _; rw [ENNReal.tsum_mul_left]

/-- **family domination**. -/
theorem L12c_Wg_dom (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (g : ℂ → ℝ) {ι : Type*} (J : Finset ι)
    (c : ι → ℝ) (h : ι → ℂ → ℝ) (hc : ∀ j ∈ J, 0 ≤ c j) (hh : ∀ j ∈ J, ∀ ρ : ℂ, 0 ≤ h j ρ)
    (hg : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → g ρ ≤ ∑ j ∈ J, c j * h j ρ) :
    L12cWg Qn T K ε s₀ k g ≤ ∑ j ∈ J, ENNReal.ofReal (c j) * L12cWg Qn T K ε s₀ k (h j) := by
  unfold L12cWg
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro χ _
  by_cases h0 : r = 0
  · simp only [dif_pos h0]; exact zero_le
  · simp only [dif_neg h0]
    have : NeZero r := ⟨h0⟩
    exact L12c_char_dom χ T (muR Qn K s₀ r) k (L12c_muR_nonneg Qn K s₀ hK r) g J c h hc hh hg

/-- domination by indicator combinations. -/
theorem L12c_Wg_le_W (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (g : ℂ → ℝ) {ι : Type*} (J : Finset ι)
    (c : ι → ℝ) (P : ι → ℂ → Prop) (hc : ∀ j ∈ J, 0 ≤ c j)
    (hg : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      g ρ ≤ ∑ j ∈ J, c j * (haveI := Classical.propDecidable (P j ρ); if P j ρ then 1 else 0)) :
    L12cWg Qn T K ε s₀ k g ≤ ∑ j ∈ J, ENNReal.ofReal (c j) * L12cW Qn T K ε s₀ k (P j) := by
  classical
  have := L12c_Wg_dom Qn T K ε s₀ k hK g J c
    (fun j ρ => haveI := Classical.propDecidable (P j ρ); if P j ρ then 1 else 0) hc
    (fun j _ ρ => by split_ifs <;> norm_num) hg
  refine this.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro j _
  rw [L12cW_eq]

/-- monotonicity in the zone predicate. -/
theorem L12cW_mono (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (P P' : ℂ → Prop)
    (hPP : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → P ρ → P' ρ) :
    L12cW Qn T K ε s₀ k P ≤ L12cW Qn T K ε s₀ k P' := by
  classical
  have := L12c_Wg_le_W Qn T K ε s₀ k hK (fun ρ => haveI := Classical.propDecidable (P ρ); if P ρ then 1 else 0)
    ({()} : Finset Unit) (fun _ => 1) (fun _ => P') (fun _ _ => zero_le_one) (by
      intro ρ h1 h2
      simp only [Finset.sum_singleton, one_mul]
      by_cases hP : P ρ
      · rw [if_pos hP, if_pos (hPP ρ h1 h2 hP)]
      · rw [if_neg hP]; split_ifs <;> norm_num)
  rw [Finset.sum_singleton, ENNReal.ofReal_one, one_mul] at this
  rw [L12cW_eq]; exact this

/-- three-term split. -/
theorem L12c_Wg_add3 (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (g g₁ g₂ g₃ : ℂ → ℝ)
    (h1 : ∀ ρ, 0 ≤ g₁ ρ) (h2 : ∀ ρ, 0 ≤ g₂ ρ) (h3 : ∀ ρ, 0 ≤ g₃ ρ)
    (hg : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → g ρ ≤ g₁ ρ + g₂ ρ + g₃ ρ) :
    L12cWg Qn T K ε s₀ k g ≤ L12cWg Qn T K ε s₀ k g₁ + L12cWg Qn T K ε s₀ k g₂ + L12cWg Qn T K ε s₀ k g₃ := by
  have := L12c_Wg_dom Qn T K ε s₀ k hK g (Finset.range 3) (fun _ => 1)
    (fun j => if j = 0 then g₁ else if j = 1 then g₂ else g₃)
    (fun _ _ => zero_le_one) (by
      intro j _ ρ
      split_ifs
      · exact h1 ρ
      · exact h2 ρ
      · exact h3 ρ) (by
      intro ρ hr1 hr2
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, one_mul, zero_add]
      exact hg ρ hr1 hr2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ENNReal.ofReal_one, one_mul, zero_add] at this
  exact this

/-- `ofReal (Σ' f) ≤ Σ' ofReal f` for `f ≥ 0`. -/
lemma L12c_ofReal_tsum_le {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∑' a, f a) ≤ ∑' a, ENNReal.ofReal (f a) := by
  by_cases hs : Summable f
  · rw [ENNReal.ofReal_tsum_of_nonneg hf hs]
  · rw [tsum_eq_zero_of_not_summable hs, ENNReal.ofReal_zero]; exact zero_le

/-- `ofReal (famZeroSum g₀) ≤ L12cWg h` when `0 ≤ g₀(μ, ·) ≤ ϖ(μ, ·) h`. -/
theorem L12c_ofReal_fam (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (g₀ : ℝ → ℂ → ℝ) (h : ℂ → ℝ)
    (hg0 : ∀ μ, 0 ≤ μ → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → 0 ≤ g₀ μ ρ)
    (hgh : ∀ μ, 0 ≤ μ → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → g₀ μ ρ ≤ varpi T μ k ρ * h ρ) :
    ENNReal.ofReal (famZeroSum Qn K ε s₀ g₀) ≤ L12cWg Qn T K ε s₀ k h := by
  unfold famZeroSum L12cWg
  have hnn : ∀ r ∈ Finset.Icc 1 (R1S Qn ε s₀), ∀ χ ∈ primChars r, 0 ≤ (if h : r = 0 then (0 : ℝ) else
      haveI : NeZero r := ⟨h⟩;
        ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℝ) * g₀ (muR Qn K s₀ r) ρ.1) := by
    intro r _ χ _
    by_cases h0 : r = 0
    · rw [dif_pos h0]
    · rw [dif_neg h0]
      have : NeZero r := ⟨h0⟩
      exact tsum_nonneg fun (ρ : {ρ : ℂ // IsNtZero χ ρ}) => mul_nonneg (Nat.cast_nonneg _)
        (hg0 _ (L12c_muR_nonneg Qn K s₀ hK r) ρ.1 ρ.2.2.1 ρ.2.2.2)
  rw [ENNReal.ofReal_sum_of_nonneg (fun r hr => Finset.sum_nonneg (hnn r hr))]
  apply Finset.sum_le_sum; intro r hr
  rw [ENNReal.ofReal_sum_of_nonneg (hnn r hr)]
  apply Finset.sum_le_sum; intro χ _
  by_cases h0 : r = 0
  · simp only [dif_pos h0, ENNReal.ofReal_zero]; exact zero_le
  · simp only [dif_neg h0]
    have : NeZero r := ⟨h0⟩
    have hμ := L12c_muR_nonneg Qn K s₀ hK r
    refine (L12c_ofReal_tsum_le _ (fun (ρ : {ρ : ℂ // IsNtZero χ ρ}) => mul_nonneg (Nat.cast_nonneg _)
      (hg0 _ hμ ρ.1 ρ.2.2.1 ρ.2.2.2))).trans ?_
    apply ENNReal.tsum_le_tsum; intro ρ
    apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hgh _ hμ ρ.1 ρ.2.2.1 ρ.2.2.2) (Nat.cast_nonneg _)

open Classical in
/-- the near weight without `ϖ`: `1[x_ρ ≤ X₀] e^{−x_ρ}`. -/
def L12cGn (s₀ X₀ : ℝ) (ρ : ℂ) : ℝ := if xRho s₀ ρ ≤ X₀ then Real.exp (-xRho s₀ ρ) else 0

open Classical in
/-- the rest weight without `ϖ`: `1[x_ρ > X₀] e^{−2x_ρ}`. -/
def L12cGr (s₀ X₀ : ℝ) (ρ : ℂ) : ℝ := if X₀ < xRho s₀ ρ then Real.exp (-(2 * xRho s₀ ρ)) else 0

lemma L12c_exp_pow (s₀ : ℝ) (ρ : ℂ) : Real.exp s₀ ^ (ρ.re - 1) = Real.exp (-xRho s₀ ρ) := by
  rw [← Real.exp_mul]; congr 1; unfold xRho; ring

theorem L12c_near_le (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (X₀ : ℝ) (hK : 0 ≤ K) :
    ENNReal.ofReal (nearSum Qn T K ε s₀ k X₀) ≤ L12cWg Qn T K ε s₀ k (L12cGn s₀ X₀) := by
  unfold nearSum
  apply L12c_ofReal_fam Qn T K ε s₀ k hK
  · intro μ hμ ρ _ _; exact L12b_gNear_nonneg T s₀ k X₀ μ ρ hμ
  · intro μ hμ ρ _ _
    unfold gNear L12cGn bRho
    split_ifs
    · rw [L12c_exp_pow]; exact le_of_eq (mul_comm _ _)
    · simp

theorem L12c_rest_le (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (X₀ : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s₀) :
    ENNReal.ofReal (restSq Qn T K ε s₀ k X₀) ≤ L12cWg Qn T K ε s₀ k (L12cGr s₀ X₀) := by
  unfold restSq
  apply L12c_ofReal_fam Qn T K ε s₀ k hK
  · intro μ _ ρ _ _; exact L12b_gRest_nonneg T s₀ k X₀ μ ρ
  · intro μ hμ ρ _ hρ1
    unfold gRest L12cGr bRho
    split_ifs
    · rw [L12c_exp_pow]
      have hv0 := varpi_nonneg0 T μ k ρ hμ
      have hv1 := L12b_varpi_le_one T μ k ρ hμ
      have he : Real.exp (-(2 * xRho s₀ ρ)) = Real.exp (-xRho s₀ ρ) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [he]
      have hE : 0 ≤ Real.exp (-xRho s₀ ρ) ^ 2 := sq_nonneg _
      calc (Real.exp (-xRho s₀ ρ) * varpi T μ k ρ) ^ 2
          = varpi T μ k ρ * varpi T μ k ρ * Real.exp (-xRho s₀ ρ) ^ 2 := by ring
        _ ≤ varpi T μ k ρ * 1 * Real.exp (-xRho s₀ ρ) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv1 hv0) hE
        _ = varpi T μ k ρ * Real.exp (-xRho s₀ ρ) ^ 2 := by ring
    · simp

end ShellS
end ZetaShell
