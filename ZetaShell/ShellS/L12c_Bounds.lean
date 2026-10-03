/-
L7_12c (3 Oct 2026): Lemma 6d (lem:shell-6d), the four zone sums from zone counts (deterministic: no `Qn → ∞`).
With `x_ρ = (1−β)s₀` and `N(x) = Σ_{x_ρ ≤ x} m ϖ ≤ C_A e^{κ₁x}` for `0 ≤ x ≤ s₀/5` (the (LF) range):
* (near) `Σ_{x_ρ≤X₀} b ≤ 2e C_A e^{p}(1+X₀)e^{pX₀}`, `p = (κ₁−1)₊`, for `X₀ ≤ s₀/5`
  (the paper's "partial summation in `x`", on unit layers `x ∈ (j−1, j]`);
* (mid) `Σ_{X₀<x_ρ≤s₀/5} m ϖ e^{−2x} ≤ e^{−(2−κ₂)X₀} e^{κ₂} C_A/(1−e^{−(κ₂−κ₁)})` for `κ₁ < κ₂ ≤ 2`;
* (bulk) `Σ_{s₀/5<x_ρ≤s₀/2} m ϖ e^{−2x} ≤ (s₀/2+2)e²C_B e^{−m′s₀/10}` from Montgomery's count
  `W(β ≥ σ) ≤ C_B e^{(3(1−σ)/(2−σ)+ε_M)δ′s₀}` on `1/2 ≤ σ ≤ 4/5` (`m′ ≤ 2 − 5δ′/2`, `ε_M ≤ m′/10`);
* (low) `Σ_{x_ρ>s₀/2} m ϖ e^{−2x} ≤ C_L e^{−s₀/10}` from `W(all) ≤ C_L e^{9s₀/10}`.
-/
import ZetaShell.ShellS.L12c_Layer

noncomputable section
open Complex
open scoped ENNReal

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- unit layers: `0 ≤ x ≤ Y` lies in `(j−1, j]` for some `j ≤ ⌈Y⌉`. -/
lemma L12c_layer (lam x Y : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) (hxY : x ≤ Y) :
    ∃ j ∈ Finset.range (⌈Y⌉₊ + 1), x ≤ min (j : ℝ) Y ∧
      Real.exp (-(lam * x)) ≤ Real.exp lam * Real.exp (-(lam * j)) ∧ x ≤ j := by
  refine ⟨⌈x⌉₊, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono hxY)),
    le_min (Nat.le_ceil x) hxY, ?_, Nat.le_ceil x⟩
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  nlinarith [mul_nonneg hlam (by linarith : (0 : ℝ) ≤ x + 1 - ⌈x⌉₊)]

lemma L12c_single_ind {ι : Type*} (J : Finset ι) (c : ι → ℝ) (P : ι → Prop) (hc : ∀ j ∈ J, 0 ≤ c j)
    (j₀ : ι) (hj₀ : j₀ ∈ J) (hP : P j₀) (a : ℝ) (ha : a ≤ c j₀) :
    a ≤ ∑ j ∈ J, c j * (haveI := Classical.propDecidable (P j); if P j then 1 else 0) := by
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun j => c j * (haveI := Classical.propDecidable (P j); if P j then (1 : ℝ) else 0))
    (fun j hj => mul_nonneg (hc j hj) (by split_ifs <;> norm_num)) hj₀)
  simp only [if_pos hP, mul_one]; exact ha

lemma L12c_zero_ind {ι : Type*} (J : Finset ι) (c : ι → ℝ) (P : ι → Prop) (hc : ∀ j ∈ J, 0 ≤ c j) :
    (0 : ℝ) ≤ ∑ j ∈ J, c j * (haveI := Classical.propDecidable (P j); if P j then 1 else 0) :=
  Finset.sum_nonneg fun j hj => mul_nonneg (hc j hj) (by split_ifs <;> norm_num)

lemma L12c_xRho_nonneg (s₀ : ℝ) (hs : 0 ≤ s₀) (ρ : ℂ) (h : ρ.re < 1) : 0 ≤ xRho s₀ ρ := by
  unfold xRho; exact mul_nonneg (by linarith) hs

/-- the sum `Σ_j ofReal(c_j) W(P_j)` with counts `W(P_j) ≤ ofReal(d_j)` is `≤ ofReal(Σ c_j d_j)`. -/
lemma L12c_sum_ofReal {ι : Type*} (J : Finset ι) (c d : ι → ℝ) (w : ι → ℝ≥0∞) (hc : ∀ j ∈ J, 0 ≤ c j)
    (hd : ∀ j ∈ J, 0 ≤ d j) (hw : ∀ j ∈ J, w j ≤ ENNReal.ofReal (d j)) :
    ∑ j ∈ J, ENNReal.ofReal (c j) * w j ≤ ENNReal.ofReal (∑ j ∈ J, c j * d j) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (hc j hj) (hd j hj))]
  apply Finset.sum_le_sum; intro j hj
  rw [ENNReal.ofReal_mul (hc j hj)]
  exact mul_le_mul_right (hw j hj) _

/-- **near**. -/
theorem L12c_near_bound (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (hs : 0 < s₀) (CA κ₁ : ℝ)
    (hCA : 0 ≤ CA) (hκ₁ : 0 ≤ κ₁)
    (hN : ∀ x : ℝ, 0 ≤ x → 5 * x ≤ s₀ →
      L12cW Qn T K ε s₀ k (fun ρ => xRho s₀ ρ ≤ x) ≤ ENNReal.ofReal (CA * Real.exp (κ₁ * x)))
    (X₀ : ℝ) (hX₀ : 0 ≤ X₀) (h5 : 5 * X₀ ≤ s₀) :
    nearSum Qn T K ε s₀ k X₀
      ≤ 2 * Real.exp 1 * CA * Real.exp (max (κ₁ - 1) 0) * (1 + X₀) * Real.exp (max (κ₁ - 1) 0 * X₀) := by
  set p := max (κ₁ - 1) 0 with hp
  have hp0 : 0 ≤ p := le_max_right _ _
  have hp1 : κ₁ - 1 ≤ p := le_max_left _ _
  set J := ⌈X₀⌉₊ with hJ
  have hJX : (J : ℝ) < X₀ + 1 := Nat.ceil_lt_add_one hX₀
  set c : ℕ → ℝ := fun j => Real.exp 1 * Real.exp (-(1 * (j : ℝ))) with hc
  set d : ℕ → ℝ := fun j => CA * Real.exp (κ₁ * min (j : ℝ) X₀) with hd
  have hc0 : ∀ j ∈ Finset.range (J + 1), 0 ≤ c j := fun j _ => by positivity
  have hd0 : ∀ j ∈ Finset.range (J + 1), 0 ≤ d j := fun j _ => by positivity
  have h1 := L12c_Wg_le_W Qn T K ε s₀ k hK (L12cGn s₀ X₀) (Finset.range (J + 1)) c
    (fun j ρ => xRho s₀ ρ ≤ min (j : ℝ) X₀) hc0 (by
      intro ρ _ hρ1
      unfold L12cGn
      by_cases hx : xRho s₀ ρ ≤ X₀
      · rw [if_pos hx]
        obtain ⟨j, hj, hmin, hexp, -⟩ := L12c_layer 1 (xRho s₀ ρ) X₀ zero_le_one
          (L12c_xRho_nonneg s₀ hs.le ρ hρ1) hx
        exact L12c_single_ind _ c (fun j => xRho s₀ ρ ≤ min (j : ℝ) X₀) hc0 j hj hmin _
          (by simp only [hc]; simpa only [one_mul] using hexp)
      · rw [if_neg hx]
        exact L12c_zero_ind _ c (fun j => xRho s₀ ρ ≤ min (j : ℝ) X₀) hc0)
  have h2 := L12c_sum_ofReal (Finset.range (J + 1)) c d
    (fun j => L12cW Qn T K ε s₀ k (fun ρ => xRho s₀ ρ ≤ min (j : ℝ) X₀)) hc0 hd0 (by
      intro j _
      have hm0 : 0 ≤ min (j : ℝ) X₀ := le_min (Nat.cast_nonneg j) hX₀
      have hm5 : 5 * min (j : ℝ) X₀ ≤ s₀ := by
        have := min_le_right (j : ℝ) X₀; linarith
      exact hN _ hm0 hm5)
  have hW := (L12c_near_le Qn T K ε s₀ k X₀ hK).trans (h1.trans h2)
  have hbound : ∑ j ∈ Finset.range (J + 1), c j * d j
      ≤ 2 * Real.exp 1 * CA * Real.exp p * (1 + X₀) * Real.exp (p * X₀) := by
    have hterm : ∀ j ∈ Finset.range (J + 1), c j * d j ≤ Real.exp 1 * CA * Real.exp (p * (X₀ + 1)) := by
      intro j hj
      have hjJ : (j : ℝ) ≤ J := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      simp only [hc, hd]
      have hexp : Real.exp (-(1 * (j : ℝ))) * Real.exp (κ₁ * min (j : ℝ) X₀) ≤ Real.exp (p * (X₀ + 1)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hmin : κ₁ * min (j : ℝ) X₀ ≤ κ₁ * j := mul_le_mul_of_nonneg_left (min_le_left _ _) hκ₁
        have h3 : (κ₁ - 1) * j ≤ p * j := mul_le_mul_of_nonneg_right hp1 hj0
        have h4 : p * j ≤ p * (X₀ + 1) := mul_le_mul_of_nonneg_left (by linarith) hp0
        nlinarith
      calc Real.exp 1 * Real.exp (-(1 * (j : ℝ))) * (CA * Real.exp (κ₁ * min (j : ℝ) X₀))
          = Real.exp 1 * CA * (Real.exp (-(1 * (j : ℝ))) * Real.exp (κ₁ * min (j : ℝ) X₀)) := by ring
        _ ≤ Real.exp 1 * CA * Real.exp (p * (X₀ + 1)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
    have hcard : ((Finset.range (J + 1)).card : ℝ) ≤ 2 * (1 + X₀) := by
      rw [Finset.card_range]; push_cast; linarith
    calc ∑ j ∈ Finset.range (J + 1), c j * d j
        ≤ (Finset.range (J + 1)).card • (Real.exp 1 * CA * Real.exp (p * (X₀ + 1))) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((Finset.range (J + 1)).card : ℝ) * (Real.exp 1 * CA * Real.exp (p * (X₀ + 1))) := by
          rw [nsmul_eq_mul]
      _ ≤ (2 * (1 + X₀)) * (Real.exp 1 * CA * Real.exp (p * (X₀ + 1))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * Real.exp 1 * CA * Real.exp p * (1 + X₀) * Real.exp (p * X₀) := by
          rw [show p * (X₀ + 1) = p + p * X₀ by ring, Real.exp_add]; ring
  have hb0 : 0 ≤ 2 * Real.exp 1 * CA * Real.exp p * (1 + X₀) * Real.exp (p * X₀) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hb0).mp (hW.trans (ENNReal.ofReal_le_ofReal hbound))

open Classical in
/-- mid zone weight: `1[X₀ < x_ρ ≤ s₀/5] e^{−2x_ρ}`. -/
def L12cG1 (s₀ X₀ : ℝ) (ρ : ℂ) : ℝ :=
  if X₀ < xRho s₀ ρ ∧ xRho s₀ ρ ≤ s₀ / 5 then Real.exp (-(2 * xRho s₀ ρ)) else 0

open Classical in
/-- bulk zone weight: `1[s₀/5 < x_ρ ≤ s₀/2] e^{−2x_ρ}`. -/
def L12cG2 (s₀ : ℝ) (ρ : ℂ) : ℝ :=
  if s₀ / 5 < xRho s₀ ρ ∧ xRho s₀ ρ ≤ s₀ / 2 then Real.exp (-(2 * xRho s₀ ρ)) else 0

open Classical in
/-- low zone weight: `1[x_ρ > s₀/2] e^{−2x_ρ}`. -/
def L12cG3 (s₀ : ℝ) (ρ : ℂ) : ℝ :=
  if s₀ / 2 < xRho s₀ ρ then Real.exp (-(2 * xRho s₀ ρ)) else 0

lemma L12cG1_nonneg (s₀ X₀ : ℝ) (ρ : ℂ) : 0 ≤ L12cG1 s₀ X₀ ρ := by
  unfold L12cG1; split_ifs <;> positivity

lemma L12cG2_nonneg (s₀ : ℝ) (ρ : ℂ) : 0 ≤ L12cG2 s₀ ρ := by
  unfold L12cG2; split_ifs <;> positivity

lemma L12cG3_nonneg (s₀ : ℝ) (ρ : ℂ) : 0 ≤ L12cG3 s₀ ρ := by
  unfold L12cG3; split_ifs <;> positivity

lemma L12c_rest_split (s₀ X₀ : ℝ) (ρ : ℂ) :
    L12cGr s₀ X₀ ρ ≤ L12cG1 s₀ X₀ ρ + L12cG2 s₀ ρ + L12cG3 s₀ ρ := by
  have e1 := L12cG1_nonneg s₀ X₀ ρ
  have e2 := L12cG2_nonneg s₀ ρ
  have e3 := L12cG3_nonneg s₀ ρ
  unfold L12cGr
  by_cases h : X₀ < xRho s₀ ρ
  · rw [if_pos h]
    by_cases h1 : xRho s₀ ρ ≤ s₀ / 5
    · unfold L12cG1; rw [if_pos ⟨h, h1⟩]; linarith
    · by_cases h2 : xRho s₀ ρ ≤ s₀ / 2
      · unfold L12cG2; rw [if_pos ⟨lt_of_not_ge h1, h2⟩]; linarith
      · unfold L12cG3; rw [if_pos (lt_of_not_ge h2)]; linarith
  · rw [if_neg h]; linarith

/-- **mid**. -/
theorem L12c_mid_bound (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (hs : 0 < s₀) (CA κ₁ κ₂ : ℝ)
    (hCA : 0 ≤ CA) (hκ₁ : 0 ≤ κ₁) (hκ12 : κ₁ < κ₂) (hκ₂ : κ₂ ≤ 2)
    (hN : ∀ x : ℝ, 0 ≤ x → 5 * x ≤ s₀ →
      L12cW Qn T K ε s₀ k (fun ρ => xRho s₀ ρ ≤ x) ≤ ENNReal.ofReal (CA * Real.exp (κ₁ * x)))
    (X₀ : ℝ) (hX₀ : 0 ≤ X₀) :
    L12cWg Qn T K ε s₀ k (L12cG1 s₀ X₀)
      ≤ ENNReal.ofReal (Real.exp (-((2 - κ₂) * X₀)) * Real.exp κ₂ * CA / (1 - Real.exp (-(κ₂ - κ₁)))) := by
  have hκ₂0 : 0 ≤ κ₂ := by linarith
  set J := ⌈s₀ / 5⌉₊ with hJ
  set E := Real.exp (-((2 - κ₂) * X₀)) with hE
  set c : ℕ → ℝ := fun j => E * (Real.exp κ₂ * Real.exp (-(κ₂ * (j : ℝ)))) with hc
  set d : ℕ → ℝ := fun j => CA * Real.exp (κ₁ * min (j : ℝ) (s₀ / 5)) with hd
  have hc0 : ∀ j ∈ Finset.range (J + 1), 0 ≤ c j := fun j _ => by positivity
  have hd0 : ∀ j ∈ Finset.range (J + 1), 0 ≤ d j := fun j _ => by positivity
  have h1 := L12c_Wg_le_W Qn T K ε s₀ k hK (L12cG1 s₀ X₀) (Finset.range (J + 1)) c
    (fun j ρ => xRho s₀ ρ ≤ min (j : ℝ) (s₀ / 5)) hc0 (by
      intro ρ _ hρ1
      unfold L12cG1
      by_cases hx : X₀ < xRho s₀ ρ ∧ xRho s₀ ρ ≤ s₀ / 5
      · rw [if_pos hx]
        obtain ⟨j, hj, hmin, hexp, -⟩ := L12c_layer κ₂ (xRho s₀ ρ) (s₀ / 5) hκ₂0
          (L12c_xRho_nonneg s₀ hs.le ρ hρ1) hx.2
        refine L12c_single_ind _ c (fun j => xRho s₀ ρ ≤ min (j : ℝ) (s₀ / 5)) hc0 j hj hmin _ ?_
        simp only [hc]
        have hsplit : Real.exp (-(2 * xRho s₀ ρ))
            = Real.exp (-((2 - κ₂) * xRho s₀ ρ)) * Real.exp (-(κ₂ * xRho s₀ ρ)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hE' : Real.exp (-((2 - κ₂) * xRho s₀ ρ)) ≤ E := by
          rw [hE]; apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hx.1.le (by linarith : (0 : ℝ) ≤ 2 - κ₂)
          linarith
        rw [hsplit]
        exact mul_le_mul hE' hexp (Real.exp_pos _).le (Real.exp_pos _).le
      · rw [if_neg hx]
        exact L12c_zero_ind _ c (fun j => xRho s₀ ρ ≤ min (j : ℝ) (s₀ / 5)) hc0)
  have h2 := L12c_sum_ofReal (Finset.range (J + 1)) c d
    (fun j => L12cW Qn T K ε s₀ k (fun ρ => xRho s₀ ρ ≤ min (j : ℝ) (s₀ / 5))) hc0 hd0 (by
      intro j _
      have hm0 : 0 ≤ min (j : ℝ) (s₀ / 5) := le_min (Nat.cast_nonneg j) (by positivity)
      have hm5 : 5 * min (j : ℝ) (s₀ / 5) ≤ s₀ := by
        have := min_le_right (j : ℝ) (s₀ / 5); linarith
      exact hN _ hm0 hm5)
  refine (h1.trans h2).trans (ENNReal.ofReal_le_ofReal ?_)
  set q := Real.exp (-(κ₂ - κ₁)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hterm : ∀ j ∈ Finset.range (J + 1), c j * d j ≤ E * Real.exp κ₂ * CA * q ^ j := by
    intro j _
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [hc, hd]
    have hqj : q ^ j = Real.exp ((j : ℝ) * (-(κ₂ - κ₁))) := by rw [hq, Real.exp_nat_mul]
    have hexp : Real.exp (-(κ₂ * (j : ℝ))) * Real.exp (κ₁ * min (j : ℝ) (s₀ / 5)) ≤ q ^ j := by
      rw [hqj, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hmin : κ₁ * min (j : ℝ) (s₀ / 5) ≤ κ₁ * j := mul_le_mul_of_nonneg_left (min_le_left _ _) hκ₁
      nlinarith
    calc E * (Real.exp κ₂ * Real.exp (-(κ₂ * (j : ℝ)))) * (CA * Real.exp (κ₁ * min (j : ℝ) (s₀ / 5)))
        = E * Real.exp κ₂ * CA * (Real.exp (-(κ₂ * (j : ℝ))) * Real.exp (κ₁ * min (j : ℝ) (s₀ / 5))) := by ring
      _ ≤ E * Real.exp κ₂ * CA * q ^ j := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hgeom : ∑ j ∈ Finset.range (J + 1), q ^ j ≤ 1 / (1 - q) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J + 1) hq0 hq1
    rw [Finset.range_eq_Ico]; simpa using this
  calc ∑ j ∈ Finset.range (J + 1), c j * d j ≤ ∑ j ∈ Finset.range (J + 1), E * Real.exp κ₂ * CA * q ^ j :=
        Finset.sum_le_sum hterm
    _ = E * Real.exp κ₂ * CA * ∑ j ∈ Finset.range (J + 1), q ^ j := by rw [Finset.mul_sum]
    _ ≤ E * Real.exp κ₂ * CA * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = E * Real.exp κ₂ * CA / (1 - q) := by ring

/-- `3u/(1+u) ≤ 5u/2` for `u ≥ 1/5`. -/
lemma L12c_bulk_exp (u : ℝ) (hu : 1 / 5 ≤ u) : 3 * u / (1 + u) ≤ 5 / 2 * u := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u) (by linarith : (0 : ℝ) ≤ 5 * u - 1)]

/-- **bulk**. -/
theorem L12c_bulk_bound (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (hs : 0 < s₀) (CB δ' εM m' : ℝ)
    (hCB : 0 ≤ CB) (hδ'0 : 0 ≤ δ') (hδ'1 : δ' ≤ 1) (hm' : 0 < m') (hm'δ : m' ≤ 2 - 5 / 2 * δ')
    (hεM0 : 0 ≤ εM) (hεM : εM ≤ m' / 10)
    (hB : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 4 / 5 → L12cW Qn T K ε s₀ k (fun ρ => σ ≤ ρ.re)
      ≤ ENNReal.ofReal (CB * Real.exp ((3 * (1 - σ) / (2 - σ) + εM) * δ' * s₀))) :
    L12cWg Qn T K ε s₀ k (L12cG2 s₀)
      ≤ ENNReal.ofReal ((s₀ / 2 + 2) * (Real.exp 2 * CB * Real.exp (-(m' / 10 * s₀)))) := by
  set J := (Finset.range (⌈s₀ / 2⌉₊ + 1)).filter (fun j : ℕ => s₀ / 5 < (j : ℝ)) with hJ
  set σ : ℕ → ℝ := fun j => max (1 - (j : ℝ) / s₀) (1 / 2) with hσ
  set c : ℕ → ℝ := fun j => Real.exp 2 * Real.exp (-(2 * (j : ℝ))) with hc
  set d : ℕ → ℝ := fun j => CB * Real.exp ((3 * (1 - σ j) / (2 - σ j) + εM) * δ' * s₀) with hd
  have hc0 : ∀ j ∈ J, 0 ≤ c j := fun j _ => by positivity
  have hd0 : ∀ j ∈ J, 0 ≤ d j := fun j _ => by positivity
  have h1 := L12c_Wg_le_W Qn T K ε s₀ k hK (L12cG2 s₀) J c (fun j ρ => σ j ≤ ρ.re) hc0 (by
      intro ρ _ hρ1
      unfold L12cG2
      by_cases hx : s₀ / 5 < xRho s₀ ρ ∧ xRho s₀ ρ ≤ s₀ / 2
      · rw [if_pos hx]
        obtain ⟨j, hj, -, hexp, hxj⟩ := L12c_layer 2 (xRho s₀ ρ) (s₀ / 2) zero_le_two
          (L12c_xRho_nonneg s₀ hs.le ρ hρ1) hx.2
        have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨hj, lt_of_lt_of_le hx.1 hxj⟩
        refine L12c_single_ind _ c (fun j => σ j ≤ ρ.re) hc0 j hjJ ?_ _ hexp
        show max (1 - (j : ℝ) / s₀) (1 / 2) ≤ ρ.re
        have hxr : xRho s₀ ρ = (1 - ρ.re) * s₀ := rfl
        apply max_le
        · have : 1 - ρ.re ≤ (j : ℝ) / s₀ := by rw [le_div_iff₀ hs]; linarith
          linarith
        · have h2 : (1 - ρ.re) * s₀ ≤ 1 / 2 * s₀ := by linarith [hx.2]
          have := le_of_mul_le_mul_right h2 hs
          linarith
      · rw [if_neg hx]
        exact L12c_zero_ind _ c (fun j => σ j ≤ ρ.re) hc0)
  have h2 := L12c_sum_ofReal J c d (fun j => L12cW Qn T K ε s₀ k (fun ρ => σ j ≤ ρ.re)) hc0 hd0 (by
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have hσ1 : 1 / 2 ≤ σ j := le_max_right _ _
      have hσ2 : σ j ≤ 4 / 5 := by
        apply max_le _ (by norm_num)
        have : 1 / 5 < (j : ℝ) / s₀ := by rw [lt_div_iff₀ hs]; linarith
        linarith
      exact hB (σ j) hσ1 hσ2)
  refine (h1.trans h2).trans (ENNReal.ofReal_le_ofReal ?_)
  have hterm : ∀ j ∈ J, c j * d j ≤ Real.exp 2 * CB * Real.exp (-(m' / 10 * s₀)) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    simp only [hc, hd]
    -- `u = 1 − σ_j = min(j/s₀, 1/2) ∈ [1/5, j/s₀]`
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 - σ j := ⟨_, rfl⟩
    have hu1 : 1 / 5 ≤ u := by
      have h1 : σ j ≤ 4 / 5 := by
        apply max_le _ (by norm_num)
        have : 1 / 5 < (j : ℝ) / s₀ := by rw [lt_div_iff₀ hs]; linarith
        linarith
      linarith
    have hu2 : u ≤ (j : ℝ) / s₀ := by
      have : 1 - (j : ℝ) / s₀ ≤ σ j := le_max_left _ _
      linarith
    have h2s : 2 - σ j = 1 + u := by rw [hu]; ring
    have h3 : 3 * (1 - σ j) / (2 - σ j) ≤ 5 / 2 * u := by
      rw [h2s, ← hu]; exact L12c_bulk_exp u hu1
    have hjs : (j : ℝ) / s₀ * s₀ = j := div_mul_cancel₀ _ hs.ne'
    have hexp : Real.exp (-(2 * (j : ℝ))) * Real.exp ((3 * (1 - σ j) / (2 - σ j) + εM) * δ' * s₀)
        ≤ Real.exp (-(m' / 10 * s₀)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e1 : (3 * (1 - σ j) / (2 - σ j) + εM) * δ' * s₀
          ≤ (5 / 2 * u + εM) * δ' * s₀ := by
        apply mul_le_mul_of_nonneg_right _ hs.le
        exact mul_le_mul_of_nonneg_right (by linarith) hδ'0
      have e2 : 5 / 2 * u * δ' * s₀ ≤ 5 / 2 * δ' * j := by
        have : u * s₀ ≤ j := by
          calc u * s₀ ≤ (j : ℝ) / s₀ * s₀ := mul_le_mul_of_nonneg_right hu2 hs.le
            _ = j := hjs
        nlinarith
      have e3 : εM * δ' * s₀ ≤ m' / 10 * s₀ := by
        have : εM * δ' ≤ m' / 10 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hs.le
      have e4 : m' * (s₀ / 5) ≤ m' * j := mul_le_mul_of_nonneg_left hj'.le hm'.le
      have e5 : (2 - 5 / 2 * δ') * j ≥ m' * j := mul_le_mul_of_nonneg_right hm'δ (Nat.cast_nonneg j)
      linarith
    calc Real.exp 2 * Real.exp (-(2 * (j : ℝ))) * (CB * Real.exp ((3 * (1 - σ j) / (2 - σ j) + εM) * δ' * s₀))
        = Real.exp 2 * CB * (Real.exp (-(2 * (j : ℝ))) *
            Real.exp ((3 * (1 - σ j) / (2 - σ j) + εM) * δ' * s₀)) := by ring
      _ ≤ Real.exp 2 * CB * Real.exp (-(m' / 10 * s₀)) := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hcard : (J.card : ℝ) ≤ s₀ / 2 + 2 := by
    have h1 : J.card ≤ ⌈s₀ / 2⌉₊ + 1 := by
      calc J.card ≤ (Finset.range (⌈s₀ / 2⌉₊ + 1)).card := Finset.card_filter_le _ _
        _ = ⌈s₀ / 2⌉₊ + 1 := Finset.card_range _
    have h2 : (⌈s₀ / 2⌉₊ : ℝ) < s₀ / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : (J.card : ℝ) ≤ (⌈s₀ / 2⌉₊ : ℝ) + 1 := by exact_mod_cast h1
    linarith
  calc ∑ j ∈ J, c j * d j ≤ J.card • (Real.exp 2 * CB * Real.exp (-(m' / 10 * s₀))) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (J.card : ℝ) * (Real.exp 2 * CB * Real.exp (-(m' / 10 * s₀))) := by rw [nsmul_eq_mul]
    _ ≤ (s₀ / 2 + 2) * (Real.exp 2 * CB * Real.exp (-(m' / 10 * s₀))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **low**. -/
theorem L12c_low_bound (Qn : ℕ) (T K ε s₀ : ℝ) (k : ℕ) (hK : 0 ≤ K) (CL : ℝ) (hCL : 0 ≤ CL)
    (hLw : L12cW Qn T K ε s₀ k (fun _ => True) ≤ ENNReal.ofReal (CL * Real.exp (9 / 10 * s₀))) :
    L12cWg Qn T K ε s₀ k (L12cG3 s₀) ≤ ENNReal.ofReal (CL * Real.exp (-(s₀ / 10))) := by
  have h1 := L12c_Wg_le_W Qn T K ε s₀ k hK (L12cG3 s₀) ({()} : Finset Unit) (fun _ => Real.exp (-s₀))
    (fun _ _ => True) (fun _ _ => (Real.exp_pos _).le) (by
      intro ρ _ _
      simp only [Finset.sum_singleton, if_pos trivial, mul_one]
      unfold L12cG3
      split_ifs with hx
      · apply Real.exp_le_exp.mpr; linarith
      · exact (Real.exp_pos _).le)
  rw [Finset.sum_singleton] at h1
  refine h1.trans ?_
  calc ENNReal.ofReal (Real.exp (-s₀)) * L12cW Qn T K ε s₀ k (fun _ => True)
      ≤ ENNReal.ofReal (Real.exp (-s₀)) * ENNReal.ofReal (CL * Real.exp (9 / 10 * s₀)) :=
        mul_le_mul_right hLw _
    _ = ENNReal.ofReal (CL * Real.exp (-(s₀ / 10))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        rw [show -(s₀ / 10) = -s₀ + 9 / 10 * s₀ by ring, Real.exp_add]; ring

end ShellS
end ZetaShell
