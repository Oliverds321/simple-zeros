/-
L7_12c (3 Oct 2026): Lemma 6a (lem:shell-6a) for ONE primitive character `χ` mod `r`:
`Σ_{ρ,ρ'} m m' b b' (1+|γ−γ'|)^{−A} ≤ (1+2cW)(Σ_{x_ρ≤X₀} m b)² + (1+cW)(18A₀ s₀ Σ_{x_ρ>X₀} m b² + 2048A₀²cW e^{−4s₀})`
for `A ≥ 2`, `k ≥ 3`, `2 ≤ T ≤ N₀ = e^{s₀}`, `0 ≤ μ ≤ N₀`, `s₀ ≥ 3`, `log r ≤ s₀`, given the uniform local count
with constant `A₀` (`L12b_local_count`). The near and rest series are summable.
Proof: finite sums first (`L12b_pair` with the Schur bounds `L12b_WS`, `L12b_WU` and the window count
`ℓ(t) = A₀(log r + log(|t|+3))`); on the rest part `ℓ(γ) ≤ 18A₀s₀` for `|γ| ≤ H = e^{16s₀}`, and for `|γ| > H`
`ϖ ≤ (4N₀/|γ|)³` and `ℓ(γ) ≤ A₀(s₀+4)√|γ|`, so the tall rest zeros cost `≤ 2048A₀²cW e^{−4s₀}` (`L12b_WS` at `γ₀ = 0`);
then pass to the `tsum`s (all terms `≥ 0`; `PropZ.Z5Z_summable`, `zero_sum_inv_sq`).
-/
import ZetaShell.ShellS.L10_Defs
import ZetaShell.ShellS.L12b_LocalCount
import ZetaShell.ShellS.L12b_Window
import ZetaShell.ShellS.L12b_Pair

noncomputable section
open Complex

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

lemma L12b_varpi_le_one (T μ : ℝ) (k : ℕ) (ρ : ℂ) (hμ : 0 ≤ μ) : varpi T μ k ρ ≤ 1 := by
  unfold varpi
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have : 0 ≤ max (|ρ.im| - 2 * T) 0 / (μ + 1) := div_nonneg (le_max_right _ _) (by linarith)
    linarith
  · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

lemma L12b_bRho_nonneg (T μ s₀ : ℝ) (k : ℕ) (ρ : ℂ) (hμ : 0 ≤ μ) : 0 ≤ bRho T μ s₀ k ρ :=
  mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) (varpi_nonneg0 T μ k ρ hμ)

lemma L12b_bRho_le_varpi (T μ s₀ : ℝ) (k : ℕ) (ρ : ℂ) (hμ : 0 ≤ μ) (hs : 0 ≤ s₀) (hβ : ρ.re ≤ 1) :
    bRho T μ s₀ k ρ ≤ varpi T μ k ρ := by
  unfold bRho
  have h1 : Real.exp s₀ ^ (ρ.re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_exp hs) (by linarith)
  have h2 := varpi_nonneg0 T μ k ρ hμ
  calc Real.exp s₀ ^ (ρ.re - 1) * varpi T μ k ρ ≤ 1 * varpi T μ k ρ := mul_le_mul_of_nonneg_right h1 h2
    _ = varpi T μ k ρ := one_mul _

lemma L12b_bRho_le_one (T μ s₀ : ℝ) (k : ℕ) (ρ : ℂ) (hμ : 0 ≤ μ) (hs : 0 ≤ s₀) (hβ : ρ.re ≤ 1) :
    bRho T μ s₀ k ρ ≤ 1 :=
  (L12b_bRho_le_varpi T μ s₀ k ρ hμ hs hβ).trans (L12b_varpi_le_one T μ k ρ hμ)

open Classical in
/-- the rest part of `b`: `b_ρ` if `x_ρ > X₀`, else `0` (so `gRest = L12bR²`). -/
def L12bR (T s₀ : ℝ) (k : ℕ) (X₀ μ : ℝ) (ρ : ℂ) : ℝ :=
  if X₀ < xRho s₀ ρ then bRho T μ s₀ k ρ else 0

lemma L12b_split_b (T s₀ : ℝ) (k : ℕ) (X₀ μ : ℝ) (ρ : ℂ) :
    gNear T s₀ k X₀ μ ρ + L12bR T s₀ k X₀ μ ρ = bRho T μ s₀ k ρ := by
  unfold gNear L12bR
  split_ifs with h1 h2 h2
  · linarith
  · simp
  · simp
  · exfalso; push Not at h1 h2; linarith

lemma L12b_gRest_eq (T s₀ : ℝ) (k : ℕ) (X₀ μ : ℝ) (ρ : ℂ) :
    gRest T s₀ k X₀ μ ρ = L12bR T s₀ k X₀ μ ρ ^ 2 := by
  unfold gRest L12bR
  split_ifs <;> simp

lemma L12b_gNear_nonneg (T s₀ : ℝ) (k : ℕ) (X₀ μ : ℝ) (ρ : ℂ) (hμ : 0 ≤ μ) : 0 ≤ gNear T s₀ k X₀ μ ρ := by
  unfold gNear; split_ifs
  · exact L12b_bRho_nonneg T μ s₀ k ρ hμ
  · exact le_rfl

lemma L12bR_nonneg (T s₀ : ℝ) (k : ℕ) (X₀ μ : ℝ) (ρ : ℂ) (hμ : 0 ≤ μ) : 0 ≤ L12bR T s₀ k X₀ μ ρ := by
  unfold L12bR; split_ifs
  · exact L12b_bRho_nonneg T μ s₀ k ρ hμ
  · exact le_rfl

lemma L12b_gNear_le (T s₀ : ℝ) (k : ℕ) (X₀ μ : ℝ) (ρ : ℂ) (hμ : 0 ≤ μ) (hs : 0 ≤ s₀) (hβ : ρ.re ≤ 1) :
    gNear T s₀ k X₀ μ ρ ≤ varpi T μ k ρ := by
  unfold gNear; split_ifs
  · exact L12b_bRho_le_varpi T μ s₀ k ρ hμ hs hβ
  · exact varpi_nonneg0 T μ k ρ hμ

lemma L12b_gRest_le (T s₀ : ℝ) (k : ℕ) (X₀ μ : ℝ) (ρ : ℂ) (hμ : 0 ≤ μ) (hs : 0 ≤ s₀) (hβ : ρ.re ≤ 1) :
    gRest T s₀ k X₀ μ ρ ≤ varpi T μ k ρ := by
  unfold gRest; split_ifs
  · have h0 := L12b_bRho_nonneg T μ s₀ k ρ hμ
    have h1 := L12b_bRho_le_one T μ s₀ k ρ hμ hs hβ
    have h2 := L12b_bRho_le_varpi T μ s₀ k ρ hμ hs hβ
    nlinarith
  · exact varpi_nonneg0 T μ k ρ hμ

lemma L12b_gRest_nonneg (T s₀ : ℝ) (k : ℕ) (X₀ μ : ℝ) (ρ : ℂ) : 0 ≤ gRest T s₀ k X₀ μ ρ := by
  rw [L12b_gRest_eq]; exact sq_nonneg _

lemma L12b_pairTerm_eq {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T μ s₀ : ℝ) (A k : ℕ)
    (p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) :
    ShellS.pairTerm χ T μ s₀ A k p = (zmult χ p.1.1 : ℝ) * zmult χ p.2.1 * bRho T μ s₀ k p.1.1
      * bRho T μ s₀ k p.2.1 * (1 / (1 + |p.1.1.im - p.2.1.im|) ^ A) := by
  unfold ShellS.pairTerm bRho
  have h : Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2)
      = Real.exp s₀ ^ (p.1.1.re - 1) * Real.exp s₀ ^ (p.2.1.re - 1) := by
    rw [← Real.rpow_add (Real.exp_pos s₀)]; ring_nf
  rw [h]; ring

/-- **per-character pair bound, finite form**. -/
theorem L12b_char_finite {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (t : ℝ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}), (∀ ρ ∈ s, t < ρ.1.im ∧ ρ.1.im ≤ t + 1) →
      ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ A₀ * (Real.log r + Real.log (|t| + 3)))
    (A k : ℕ) (hA : 2 ≤ A) (T μ s₀ X₀ : ℝ) (hμ : 0 ≤ μ)
    (s : Finset {ρ : ℂ // IsNtZero χ ρ}) :
    ∑ ρ ∈ s, ∑ ρ' ∈ s, ShellS.pairTerm χ T μ s₀ A k (ρ, ρ')
      ≤ (1 + 2 * L12bcW) * (∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ μ ρ.1) ^ 2
        + (1 + L12bcW) * ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1
            * L12bL (A₀ * Real.log r) A₀ ρ.1.im := by
  have hlr : 0 ≤ Real.log r :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
  have ha : 0 ≤ A₀ * Real.log r := mul_nonneg (by linarith) hlr
  have hc : (0 : ℝ) < A₀ := by linarith
  have hm : ∀ ρ ∈ s, (0 : ℝ) ≤ (zmult χ ρ.1 : ℝ) := fun _ _ => Nat.cast_nonneg _
  have hcount : ∀ (t : ℝ) (s' : Finset {ρ : ℂ // IsNtZero χ ρ}), s' ⊆ s →
      (∀ ρ ∈ s', t < ρ.1.im ∧ ρ.1.im ≤ t + 1) → ∑ ρ ∈ s', (zmult χ ρ.1 : ℝ) ≤ L12bL (A₀ * Real.log r) A₀ t := by
    intro t s' _ h
    have := hloc t s' h
    unfold L12bL; linarith
  have hKle : ∀ ρ ρ' : {ρ : ℂ // IsNtZero χ ρ},
      1 / (1 + |ρ.1.im - ρ'.1.im|) ^ A ≤ 1 / (1 + |ρ.1.im - ρ'.1.im|) ^ 2 := by
    intro ρ ρ'
    have h1 : 1 ≤ 1 + |ρ.1.im - ρ'.1.im| := by linarith [abs_nonneg (ρ.1.im - ρ'.1.im)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hA)
  have key := L12b_pair s (fun ρ => (zmult χ ρ.1 : ℝ)) (fun ρ => gNear T s₀ k X₀ μ ρ.1)
    (fun ρ => L12bR T s₀ k X₀ μ ρ.1) (fun ρ => L12bL (A₀ * Real.log r) A₀ ρ.1.im)
    (fun ρ ρ' => 1 / (1 + |ρ.1.im - ρ'.1.im|) ^ A) L12bcW (2 * L12bcW) hm
    (fun ρ _ => L12b_gNear_nonneg T s₀ k X₀ μ ρ.1 hμ) (fun ρ _ => L12bR_nonneg T s₀ k X₀ μ ρ.1 hμ)
    (fun ρ _ => L12bL_pos _ _ _ ha hc)
    (fun ρ _ ρ' _ => by positivity)
    (fun ρ _ ρ' _ => by
      have h1 : 1 ≤ (1 + |ρ.1.im - ρ'.1.im|) ^ A :=
        one_le_pow₀ (by linarith [abs_nonneg (ρ.1.im - ρ'.1.im)])
      exact (div_le_one (by positivity)).mpr h1)
    (fun ρ ρ' => by rw [abs_sub_comm])
    (fun ρ _ => by
      calc ∑ ρ' ∈ s, (zmult χ ρ'.1 : ℝ) * (1 / (1 + |ρ.1.im - ρ'.1.im|) ^ A)
          ≤ ∑ ρ' ∈ s, (zmult χ ρ'.1 : ℝ) * (1 / (1 + |ρ.1.im - ρ'.1.im|) ^ 2) :=
            Finset.sum_le_sum fun ρ' _ => mul_le_mul_of_nonneg_left (hKle ρ ρ') (Nat.cast_nonneg _)
        _ ≤ L12bcW * L12bL (A₀ * Real.log r) A₀ ρ.1.im :=
            L12b_WS s (fun ρ => ρ.1.im) (fun ρ => (zmult χ ρ.1 : ℝ)) _ _ ha hc.le hm hcount ρ.1.im)
    (fun ρ _ => by
      calc ∑ ρ' ∈ s, (zmult χ ρ'.1 : ℝ) * (1 / (1 + |ρ.1.im - ρ'.1.im|) ^ A)
            / L12bL (A₀ * Real.log r) A₀ ρ'.1.im
          ≤ ∑ ρ' ∈ s, (zmult χ ρ'.1 : ℝ) * (1 / (1 + |ρ.1.im - ρ'.1.im|) ^ 2
            / L12bL (A₀ * Real.log r) A₀ ρ'.1.im) := by
            apply Finset.sum_le_sum; intro ρ' _
            rw [mul_div_assoc]
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            exact div_le_div_of_nonneg_right (hKle ρ ρ') (L12bL_pos _ _ _ ha hc).le
        _ ≤ 2 * L12bcW :=
            L12b_WU s (fun ρ => ρ.1.im) (fun ρ => (zmult χ ρ.1 : ℝ)) _ _ ha hc hm hcount ρ.1.im)
  calc ∑ ρ ∈ s, ∑ ρ' ∈ s, ShellS.pairTerm χ T μ s₀ A k (ρ, ρ')
      = ∑ ρ ∈ s, ∑ ρ' ∈ s, (zmult χ ρ.1 : ℝ) * (zmult χ ρ'.1 : ℝ)
          * (gNear T s₀ k X₀ μ ρ.1 + L12bR T s₀ k X₀ μ ρ.1)
          * (gNear T s₀ k X₀ μ ρ'.1 + L12bR T s₀ k X₀ μ ρ'.1) * (1 / (1 + |ρ.1.im - ρ'.1.im|) ^ A) := by
        apply Finset.sum_congr rfl; intro ρ _; apply Finset.sum_congr rfl; intro ρ' _
        rw [L12b_pairTerm_eq, L12b_split_b, L12b_split_b]
    _ ≤ _ := key
    _ = _ := by
        congr 2
        apply Finset.sum_congr rfl; intro ρ _
        rw [L12b_gRest_eq]

/-- `ϖ ≤ 64 N₀³/|γ|³` for `|γ| ≥ 4T`, `0 ≤ μ ≤ N₀`, `N₀ ≥ 1`, `k ≥ 3`. -/
lemma L12b_varpi_decay (T μ N₀ : ℝ) (k : ℕ) (hk : 3 ≤ k) (hT : 0 ≤ T) (hμ : 0 ≤ μ) (hμN : μ ≤ N₀)
    (hN : 1 ≤ N₀) (ρ : ℂ) (hγ : 4 * T ≤ |ρ.im|) (hγ1 : 1 ≤ |ρ.im|) :
    varpi T μ k ρ ≤ 64 * N₀ ^ 3 / |ρ.im| ^ 3 := by
  unfold varpi
  set g := |ρ.im| with hg
  set B := 1 + max (g - 2 * T) 0 / (μ + 1) with hB
  have hD : g / 2 ≤ max (g - 2 * T) 0 := le_trans (by linarith) (le_max_left _ _)
  have hB1 : 1 ≤ B := by
    have : 0 ≤ max (g - 2 * T) 0 / (μ + 1) := div_nonneg (le_max_right _ _) (by linarith)
    linarith
  have hBg : g / (4 * N₀) ≤ B := by
    have h1 : g / (4 * N₀) ≤ (g / 2) / (μ + 1) := by
      rw [div_div]; apply div_le_div_of_nonneg_left (by linarith) (by positivity); linarith
    have h2 : (g / 2) / (μ + 1) ≤ max (g - 2 * T) 0 / (μ + 1) :=
      div_le_div_of_nonneg_right hD (by linarith)
    linarith
  have hk3 : B ^ (-(k : ℝ)) ≤ B ^ (-(3 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hB1
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB3 : B ^ (-(3 : ℝ)) = 1 / B ^ 3 := by
    rw [Real.rpow_neg (by linarith), one_div]
    norm_cast
  rw [hB3] at hk3
  refine hk3.trans ?_
  have hg0 : 0 < g := by linarith
  have hBpos : 0 < B := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h3 : (g / (4 * N₀)) ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ (by positivity) hBg 3
  have h4 : (g / (4 * N₀)) ^ 3 * (64 * N₀ ^ 3) = g ^ 3 := by field_simp; ring
  nlinarith [h3, h4, pow_pos (show (0 : ℝ) < N₀ by linarith) 3]

/-- `log(x+3) ≤ 4√x` for `x ≥ 1`. -/
lemma L12b_log_le_sqrt (x : ℝ) (hx : 1 ≤ x) : Real.log (x + 3) ≤ 4 * Real.sqrt x := by
  have h1 : Real.log (x + 3) ≤ (x + 3) ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div (by linarith) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have h2 : Real.sqrt (x + 3) ≤ Real.sqrt 4 * Real.sqrt x := by
    rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at h2
  linarith

/-- the tall rest zeros: for `|γ| ≥ H = e^{16 s₀}`, `ϖ ℓ(γ) ≤ 256 A₀(s₀+4) e^{−5s₀} (1+|γ|)^{−2}`. -/
lemma L12b_tail_pt (A₀ a T μ s₀ : ℝ) (k : ℕ) (hk : 3 ≤ k) (hA₀ : 0 ≤ A₀) (ha : a ≤ A₀ * s₀)
    (hT : 0 ≤ T) (hTN : T ≤ Real.exp s₀) (hμ : 0 ≤ μ) (hμN : μ ≤ Real.exp s₀) (hs : 3 ≤ s₀) (ρ : ℂ)
    (hγ : Real.exp (16 * s₀) < |ρ.im|) :
    varpi T μ k ρ * L12bL a A₀ ρ.im
      ≤ 256 * A₀ * (s₀ + 4) / Real.exp (5 * s₀) * (1 / (1 + |0 - ρ.im|) ^ 2) := by
  set g := |ρ.im| with hg
  set N₀ := Real.exp s₀ with hN₀
  have hN1 : 1 ≤ N₀ := Real.one_le_exp (by linarith)
  have hH1 : 1 ≤ Real.exp (16 * s₀) := Real.one_le_exp (by linarith)
  have hg1 : 1 ≤ g := by linarith
  have hg0 : 0 < g := by linarith
  have h4T : 4 * T ≤ g := by
    have : 4 * N₀ ≤ Real.exp (16 * s₀) := by
      rw [hN₀, show 16 * s₀ = s₀ + 15 * s₀ by ring, Real.exp_add]
      have : (4 : ℝ) ≤ Real.exp (15 * s₀) := by
        have := Real.add_one_le_exp (15 * s₀); linarith
      nlinarith [Real.exp_pos s₀]
    linarith
  have hv := L12b_varpi_decay T μ N₀ k hk hT hμ hμN hN1 ρ h4T hg1
  have hv0 := varpi_nonneg0 T μ k ρ hμ
  have hsq : Real.sqrt (Real.exp (16 * s₀)) = Real.exp (8 * s₀) := by
    have e : Real.exp (16 * s₀) = Real.exp (8 * s₀) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e, Real.sqrt_sq (Real.exp_pos _).le]
  have hsg : Real.exp (8 * s₀) ≤ Real.sqrt g := by
    rw [← hsq]; exact Real.sqrt_le_sqrt hγ.le
  have hsg0 : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg0
  have hsg1 : 1 ≤ Real.sqrt g := by rw [Real.one_le_sqrt]; exact hg1
  -- ℓ(γ) ≤ A₀(s₀ + 4)√g
  have hl : L12bL a A₀ ρ.im ≤ A₀ * (s₀ + 4) * Real.sqrt g := by
    unfold L12bL
    have h1 := L12b_log_le_sqrt g hg1
    have h2 : A₀ * s₀ ≤ A₀ * s₀ * Real.sqrt g := le_mul_of_one_le_right (by positivity) hsg1
    nlinarith [mul_le_mul_of_nonneg_left h1 hA₀]
  have hl0 : 0 ≤ L12bL a A₀ ρ.im ∨ L12bL a A₀ ρ.im < 0 := le_or_gt _ _
  -- (1+|γ|)² ≤ 4 g²
  have h1g : (1 + |0 - ρ.im|) ^ 2 ≤ 4 * g ^ 2 := by
    rw [zero_sub, abs_neg]; nlinarith
  have hkey : varpi T μ k ρ * L12bL a A₀ ρ.im ≤ 64 * N₀ ^ 3 / g ^ 3 * (A₀ * (s₀ + 4) * Real.sqrt g) := by
    rcases hl0 with hl0 | hl0
    · exact mul_le_mul hv hl hl0 (by positivity)
    · have : varpi T μ k ρ * L12bL a A₀ ρ.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv0 hl0.le
      exact this.trans (by positivity)
  refine hkey.trans ?_
  have hN3 : N₀ ^ 3 * Real.exp (5 * s₀) = Real.exp (8 * s₀) := by
    rw [hN₀, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have hE : 0 < Real.exp (5 * s₀) := Real.exp_pos _
  have h1pos : 0 < (1 + |0 - ρ.im|) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  -- 64 N₀³ A₀(s₀+4)√g · (e^{5s₀}(1+|γ|)²) ≤ 256 A₀(s₀+4) · g³
  have hA4 : 0 ≤ A₀ * (s₀ + 4) := by positivity
  have hgsq : g = Real.sqrt g * Real.sqrt g := (Real.mul_self_sqrt hg0.le).symm
  calc 64 * N₀ ^ 3 * (A₀ * (s₀ + 4) * Real.sqrt g) * ((1 + |0 - ρ.im|) ^ 2 * Real.exp (5 * s₀))
      = 64 * (A₀ * (s₀ + 4)) * Real.sqrt g * (N₀ ^ 3 * Real.exp (5 * s₀)) * (1 + |0 - ρ.im|) ^ 2 := by ring
    _ = 64 * (A₀ * (s₀ + 4)) * Real.sqrt g * Real.exp (8 * s₀) * (1 + |0 - ρ.im|) ^ 2 := by rw [hN3]
    _ ≤ 64 * (A₀ * (s₀ + 4)) * Real.sqrt g * Real.sqrt g * (4 * g ^ 2) := by
        apply mul_le_mul _ h1g (le_of_lt h1pos) (by positivity)
        exact mul_le_mul_of_nonneg_left hsg (by positivity)
    _ = 64 * (A₀ * (s₀ + 4)) * (Real.sqrt g * Real.sqrt g) * (4 * g ^ 2) := by ring
    _ = 256 * A₀ * (s₀ + 4) * g ^ 3 := by rw [← hgsq]; ring

/-- `(s₀+4)(s₀+2) ≤ 8 e^{s₀}` for `s₀ ≥ 0`. -/
lemma L12b_quad_le_exp (s₀ : ℝ) (hs : 0 ≤ s₀) : (s₀ + 4) * (s₀ + 2) ≤ 8 * Real.exp s₀ := by
  have := Real.quadratic_le_exp_of_nonneg hs
  nlinarith

/-- the rest sum with the window weight: `Σ m gRest ℓ ≤ 18A₀s₀ Σ m gRest + 2048 A₀² cW e^{−4s₀}`. -/
theorem L12b_rest_finite {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (t : ℝ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}), (∀ ρ ∈ s, t < ρ.1.im ∧ ρ.1.im ≤ t + 1) →
      ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ A₀ * (Real.log r + Real.log (|t| + 3)))
    (k : ℕ) (hk : 3 ≤ k) (T μ s₀ X₀ : ℝ) (hT : 2 ≤ T) (hTN : T ≤ Real.exp s₀) (hμ : 0 ≤ μ)
    (hμN : μ ≤ Real.exp s₀) (hs : 3 ≤ s₀) (hr : Real.log r ≤ s₀)
    (s : Finset {ρ : ℂ // IsNtZero χ ρ}) :
    ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 * L12bL (A₀ * Real.log r) A₀ ρ.1.im
      ≤ 18 * A₀ * s₀ * ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1
        + 2048 * A₀ ^ 2 * L12bcW / Real.exp (4 * s₀) := by
  classical
  have hlr : 0 ≤ Real.log r :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
  have ha : 0 ≤ A₀ * Real.log r := mul_nonneg (by linarith) hlr
  have hc : (0 : ℝ) < A₀ := by linarith
  have has : A₀ * Real.log r ≤ A₀ * s₀ := mul_le_mul_of_nonneg_left hr hc.le
  set H := Real.exp (16 * s₀) with hH
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.1.im| ≤ H)]
  -- short zeros
  have hshort : ∑ ρ ∈ s.filter (fun ρ => |ρ.1.im| ≤ H),
      (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 * L12bL (A₀ * Real.log r) A₀ ρ.1.im
      ≤ 18 * A₀ * s₀ * ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 := by
    have hpt : ∀ ρ ∈ s.filter (fun ρ => |ρ.1.im| ≤ H),
        (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 * L12bL (A₀ * Real.log r) A₀ ρ.1.im
          ≤ 18 * A₀ * s₀ * ((zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hlog : Real.log (|ρ.1.im| + 3) ≤ 17 * s₀ := by
        have h1 : |ρ.1.im| + 3 ≤ Real.exp (17 * s₀) := by
          have h2 : Real.exp (16 * s₀) + 3 ≤ Real.exp (17 * s₀) := by
            rw [show 17 * s₀ = 16 * s₀ + s₀ by ring, Real.exp_add]
            have h3 : 4 ≤ Real.exp s₀ := by have := Real.add_one_le_exp s₀; linarith
            have h4 : 1 ≤ Real.exp (16 * s₀) := Real.one_le_exp (by linarith)
            nlinarith
          linarith [hρ.2]
        have := Real.log_le_log (by positivity) h1
        rwa [Real.log_exp] at this
      have hl : L12bL (A₀ * Real.log r) A₀ ρ.1.im ≤ 18 * A₀ * s₀ := by
        unfold L12bL; nlinarith [mul_le_mul_of_nonneg_left hlog hc.le]
      have h0 : 0 ≤ (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 :=
        mul_nonneg (Nat.cast_nonneg _) (L12b_gRest_nonneg _ _ _ _ _ _)
      nlinarith
    calc _ ≤ ∑ ρ ∈ s.filter (fun ρ => |ρ.1.im| ≤ H), 18 * A₀ * s₀ * ((zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1) :=
          Finset.sum_le_sum hpt
      _ = 18 * A₀ * s₀ * ∑ ρ ∈ s.filter (fun ρ => |ρ.1.im| ≤ H), (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 := by
          rw [Finset.mul_sum]
      _ ≤ 18 * A₀ * s₀ * ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro ρ _ _; exact mul_nonneg (Nat.cast_nonneg _) (L12b_gRest_nonneg _ _ _ _ _ _)
  -- tall zeros
  have htall : ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ H),
      (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 * L12bL (A₀ * Real.log r) A₀ ρ.1.im
      ≤ 2048 * A₀ ^ 2 * L12bcW / Real.exp (4 * s₀) := by
    set D := 256 * A₀ * (s₀ + 4) / Real.exp (5 * s₀) with hD
    have hD0 : 0 ≤ D := by positivity
    have hpt : ∀ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ H),
        (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 * L12bL (A₀ * Real.log r) A₀ ρ.1.im
          ≤ (zmult χ ρ.1 : ℝ) * (D * (1 / (1 + |0 - ρ.1.im|) ^ 2)) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      push Not at hρ
      have hβ : ρ.1.re ≤ 1 := ρ.2.2.2.le
      have hg := L12b_gRest_le T s₀ k X₀ μ ρ.1 hμ (by linarith) hβ
      have hg0 := L12b_gRest_nonneg T s₀ k X₀ μ ρ.1
      have hL0 := L12bL_pos (A₀ * Real.log r) A₀ ρ.1.im ha hc
      have ht := L12b_tail_pt A₀ (A₀ * Real.log r) T μ s₀ k hk hc.le has (by linarith) hTN hμ hμN hs ρ.1 hρ.2
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc gRest T s₀ k X₀ μ ρ.1 * L12bL (A₀ * Real.log r) A₀ ρ.1.im
          ≤ varpi T μ k ρ.1 * L12bL (A₀ * Real.log r) A₀ ρ.1.im := mul_le_mul_of_nonneg_right hg hL0.le
        _ ≤ D * (1 / (1 + |0 - ρ.1.im|) ^ 2) := ht
    have hcount : ∀ (t : ℝ) (s' : Finset {ρ : ℂ // IsNtZero χ ρ}),
        s' ⊆ s.filter (fun ρ => ¬ |ρ.1.im| ≤ H) →
        (∀ ρ ∈ s', t < ρ.1.im ∧ ρ.1.im ≤ t + 1) → ∑ ρ ∈ s', (zmult χ ρ.1 : ℝ) ≤ L12bL (A₀ * Real.log r) A₀ t := by
      intro t s' _ h
      have := hloc t s' h
      unfold L12bL; linarith
    have hWS := L12b_WS (s.filter (fun ρ => ¬ |ρ.1.im| ≤ H)) (fun ρ => ρ.1.im) (fun ρ => (zmult χ ρ.1 : ℝ))
      _ _ ha hc.le (fun _ _ => Nat.cast_nonneg _) hcount 0
    have hl0 : L12bL (A₀ * Real.log r) A₀ 0 ≤ A₀ * (s₀ + 2) := by
      unfold L12bL
      have : Real.log (|(0 : ℝ)| + 3) ≤ 2 := by
        rw [abs_zero, zero_add]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
      nlinarith [mul_le_mul_of_nonneg_left this hc.le]
    have hcW := L12bcW_nonneg
    calc _ ≤ ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ H), (zmult χ ρ.1 : ℝ) * (D * (1 / (1 + |0 - ρ.1.im|) ^ 2)) :=
          Finset.sum_le_sum hpt
      _ = D * ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.1.im| ≤ H), (zmult χ ρ.1 : ℝ) * (1 / (1 + |0 - ρ.1.im|) ^ 2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ρ _; ring
      _ ≤ D * (L12bcW * L12bL (A₀ * Real.log r) A₀ 0) := mul_le_mul_of_nonneg_left hWS hD0
      _ ≤ D * (L12bcW * (A₀ * (s₀ + 2))) := by
          apply mul_le_mul_of_nonneg_left _ hD0; exact mul_le_mul_of_nonneg_left hl0 hcW
      _ = 256 * A₀ ^ 2 * L12bcW * ((s₀ + 4) * (s₀ + 2)) / Real.exp (5 * s₀) := by rw [hD]; ring
      _ ≤ 256 * A₀ ^ 2 * L12bcW * (8 * Real.exp s₀) / Real.exp (5 * s₀) := by
          apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left (L12b_quad_le_exp s₀ (by linarith)) (by positivity)
      _ = 2048 * A₀ ^ 2 * L12bcW / Real.exp (4 * s₀) := by
          rw [show 5 * s₀ = s₀ + 4 * s₀ by ring, Real.exp_add]
          field_simp
          ring
  linarith

end ShellS
end ZetaShell
