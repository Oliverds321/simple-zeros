/-
A6 helpers (L2_2, 28 Sep 2026) — the per-block bounds of lem:sigd-tight WITHOUT Weyl monotonicity, for 2×2 blocks
X of the true matrix M_𝒯 (f(t) = (2 − t)₊², d_i = 1 − δ_i, off-diagonal √(m m′)(κ − e) with |e| ≤ √(δ₁δ₂), κ = k_φ(gap)):
  * `trFun_two_ge`       : tr f(X) ≥ f(λ_min(X)), λ_min = (X₀₀ + X₁₁ − √((X₀₀ − X₁₁)² + 4X₀₁²))/2 (from trace and ‖X‖²);
  * `block11_ge`         : marks (1,1): tr f(X) ≥ 2 + 2κ²   (both eigenvalues ≤ 2, tr f = ‖2I − X‖²);
  * `block22_ge`         : marks (2,2): tr f(X) ≥ 4κ²        (λ_min ≤ 2 − 2κ).
  * `block12_ge`         : marks (1,2): tr f(X) ≥ (1/2 + (1/4 + 2κ²)^{1/2})² (Rayleigh at the Ê = 0 eigenvector).
The chain partition/counting, the reindexing of blocks to `Fin 2`, and the pinching step (L4) remain.
-/
import ZetaS.Interfaces

open Matrix RHLinalg

namespace ZetaS

namespace A6aux

/-- `f(t) = (2 − t)₊²`. -/
noncomputable def fT (t : ℝ) : ℝ := (max (2 - t) 0) ^ 2

lemma fT_nonneg (t : ℝ) : 0 ≤ fT t := sq_nonneg _

lemma fT_antitone : Antitone fT := by
  intro a b hab
  unfold fT
  have h1 : max (2 - b) 0 ≤ max (2 - a) 0 := max_le_max (by linarith) le_rfl
  exact pow_le_pow_left₀ (le_max_right _ _) h1 2

lemma fT_of_le {t : ℝ} (ht : t ≤ 2) : fT t = (2 - t) ^ 2 := by
  unfold fT; rw [max_eq_left (by linarith)]

/-- trace and Frobenius norm of a real symmetric 2×2 matrix in terms of its eigenvalues. -/
lemma two_eig (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.IsHermitian) :
    hX.eigenvalues 0 + hX.eigenvalues 1 = X 0 0 + X 1 1 ∧
      hX.eigenvalues 0 ^ 2 + hX.eigenvalues 1 ^ 2 = X 0 0 ^ 2 + X 1 1 ^ 2 + 2 * X 0 1 ^ 2 := by
  have h10 : X 1 0 = X 0 1 := by
    have := hX.apply 1 0
    simpa using this.symm
  constructor
  · have := rtrace_eq_sum_eigenvalues hX
    rw [Fin.sum_univ_two] at this
    rw [← this]
    simp [rtrace, Matrix.trace_fin_two]
  · have := frobSq_hermitian_eq_sum_sq_eigenvalues hX
    rw [Fin.sum_univ_two] at this
    rw [← this]
    simp only [frobSq, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      star_trivial, RCLike.re_to_real, h10]
    ring

lemma trFun_two_ge (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.IsHermitian) :
    fT ((X 0 0 + X 1 1 - Real.sqrt ((X 0 0 - X 1 1) ^ 2 + 4 * X 0 1 ^ 2)) / 2) ≤ trFun hX fT := by
  obtain ⟨h1, h2⟩ := two_eig X hX
  set l0 := hX.eigenvalues 0
  set l1 := hX.eigenvalues 1
  have e : (X 0 0 - X 1 1) ^ 2 + 4 * X 0 1 ^ 2 = (l0 - l1) ^ 2 := by
    have h1sq : (l0 + l1) ^ 2 = (X 0 0 + X 1 1) ^ 2 := by rw [h1]
    nlinarith [h1sq, h2]
  rw [e, Real.sqrt_sq_eq_abs, ← h1]
  unfold trFun
  rw [Fin.sum_univ_two]
  rcases le_total l0 l1 with h | h
  · rw [abs_of_nonpos (by linarith), show (l0 + l1 - -(l0 - l1)) / 2 = l0 by ring]
    linarith [fT_nonneg l1]
  · rw [abs_of_nonneg (by linarith), show (l0 + l1 - (l0 - l1)) / 2 = l1 by ring]
    linarith [fT_nonneg l0]

/-- if both eigenvalues are `≤ 2`, `tr f(X) = ‖2I − X‖²`. -/
lemma trFun_two_eq (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.IsHermitian)
    (hmax : (X 0 0 + X 1 1 + Real.sqrt ((X 0 0 - X 1 1) ^ 2 + 4 * X 0 1 ^ 2)) / 2 ≤ 2) :
    trFun hX fT = (2 - X 0 0) ^ 2 + (2 - X 1 1) ^ 2 + 2 * X 0 1 ^ 2 := by
  obtain ⟨h1, h2⟩ := two_eig X hX
  set l0 := hX.eigenvalues 0
  set l1 := hX.eigenvalues 1
  have e : (X 0 0 - X 1 1) ^ 2 + 4 * X 0 1 ^ 2 = (l0 - l1) ^ 2 := by
    have h1sq : (l0 + l1) ^ 2 = (X 0 0 + X 1 1) ^ 2 := by rw [h1]
    nlinarith [h1sq, h2]
  rw [e, Real.sqrt_sq_eq_abs, ← h1] at hmax
  have hl0 : l0 ≤ 2 := by
    rcases le_total l0 l1 with h | h
    · rw [abs_of_nonpos (by linarith)] at hmax; linarith
    · rw [abs_of_nonneg (by linarith)] at hmax; linarith
  have hl1 : l1 ≤ 2 := by
    rcases le_total l0 l1 with h | h
    · rw [abs_of_nonpos (by linarith)] at hmax; linarith
    · rw [abs_of_nonneg (by linarith)] at hmax; linarith
  unfold trFun
  rw [Fin.sum_univ_two, fT_of_le hl0, fT_of_le hl1]
  nlinarith [h1, h2]

/-- **(1,1) block**: diagonal `1 − δᵢ`, off-diagonal `κ − e`, `|e| ≤ (δ₁ + δ₂)/2`, `(κ − e)² ≤ (1 − δ₁)(1 − δ₂)`
(PSD), `0 ≤ δᵢ ≤ 1`, `0 ≤ κ ≤ 1`: `tr f(X) ≥ 2 + 2κ²`. -/
lemma block11_ge (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.IsHermitian) {δ₁ δ₂ κ e : ℝ}
    (h00 : X 0 0 = 1 - δ₁) (h11 : X 1 1 = 1 - δ₂) (h01 : X 0 1 = κ - e)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₁' : δ₁ ≤ 1) (hδ₂' : δ₂ ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (he : |e| ≤ (δ₁ + δ₂) / 2) (hpsd : (κ - e) ^ 2 ≤ (1 - δ₁) * (1 - δ₂)) :
    2 + 2 * κ ^ 2 ≤ trFun hX fT := by
  have hmax : (X 0 0 + X 1 1 + Real.sqrt ((X 0 0 - X 1 1) ^ 2 + 4 * X 0 1 ^ 2)) / 2 ≤ 2 := by
    rw [h00, h11, h01]
    have hs : Real.sqrt ((1 - δ₁ - (1 - δ₂)) ^ 2 + 4 * (κ - e) ^ 2) ≤ 2 - δ₁ - δ₂ := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  rw [trFun_two_eq X hX hmax, h00, h11, h01]
  have := abs_le.1 he
  nlinarith [sq_nonneg (κ - e), sq_nonneg δ₁, sq_nonneg δ₂, mul_nonneg hκ0 hδ₁]

/-- **(2,2) block**: diagonal `2(1 − δᵢ)`, off-diagonal `2(κ − e)`, `e² ≤ δ₁δ₂`, `δᵢ ≥ 0`, `0 ≤ κ ≤ 1`:
`tr f(X) ≥ 4κ²`. -/
lemma block22_ge (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.IsHermitian) {δ₁ δ₂ κ e : ℝ}
    (h00 : X 0 0 = 2 * (1 - δ₁)) (h11 : X 1 1 = 2 * (1 - δ₂)) (h01 : X 0 1 = 2 * (κ - e))
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (he : e ^ 2 ≤ δ₁ * δ₂) :
    4 * κ ^ 2 ≤ trFun hX fT := by
  refine le_trans ?_ (trFun_two_ge X hX)
  -- λ_min ≤ 2 − 2κ
  have hmin : (X 0 0 + X 1 1 - Real.sqrt ((X 0 0 - X 1 1) ^ 2 + 4 * X 0 1 ^ 2)) / 2 ≤ 2 - 2 * κ := by
    rw [h00, h11, h01]
    have key : 2 * κ - δ₁ - δ₂ ≤ Real.sqrt ((δ₁ - δ₂) ^ 2 + 4 * (κ - e) ^ 2) := by
      rcases le_or_gt (2 * κ - δ₁ - δ₂) 0 with h | h
      · exact h.trans (Real.sqrt_nonneg _)
      · rw [Real.le_sqrt h.le (by positivity)]
        set r := Real.sqrt (δ₁ * δ₂) with hr
        have hr0 : 0 ≤ r := Real.sqrt_nonneg _
        have hr2 : r ^ 2 = δ₁ * δ₂ := Real.sq_sqrt (mul_nonneg hδ₁ hδ₂)
        have her : |e| ≤ r := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt he
        have hS : 2 * r ≤ δ₁ + δ₂ := by nlinarith [sq_nonneg (δ₁ - δ₂), sq_nonneg (δ₁ + δ₂ - 2 * r)]
        have he1 := (abs_le.1 her).2
        have hke : κ - r ≤ κ - e := by linarith
        have hkr : 0 ≤ κ - r := by linarith
        have hsq : (κ - r) ^ 2 ≤ (κ - e) ^ 2 := pow_le_pow_left₀ hkr hke 2
        nlinarith [hsq, hr2, hS, mul_nonneg hκ0 (sub_nonneg.2 hS)]
    have e4 : (2 * (1 - δ₁) - 2 * (1 - δ₂)) ^ 2 + 4 * (2 * (κ - e)) ^ 2
        = 4 * ((δ₁ - δ₂) ^ 2 + 4 * (κ - e) ^ 2) := by ring
    rw [e4, Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    linarith
  calc 4 * κ ^ 2 = fT (2 - 2 * κ) := by rw [fT_of_le (by linarith)]; ring
    _ ≤ _ := fT_antitone hmin

/-- 2×2 Rayleigh bound from the explicit smallest eigenvalue `λ = (p + q − s)/2`, `s = √((p − q)² + 4c²)`. -/
lemma rayleigh_two (p q c v₀ v₁ : ℝ) :
    (p + q - Real.sqrt ((p - q) ^ 2 + 4 * c ^ 2)) / 2 * (v₀ ^ 2 + v₁ ^ 2)
      ≤ p * v₀ ^ 2 + 2 * c * v₀ * v₁ + q * v₁ ^ 2 := by
  set s := Real.sqrt ((p - q) ^ 2 + 4 * c ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (p - q) ^ 2 + 4 * c ^ 2 := Real.sq_sqrt (by positivity)
  have hα : 0 ≤ (p - q + s) / 2 := by
    have : |p - q| ≤ s := by
      rw [hs, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg c])
    linarith [neg_abs_le (p - q)]
  have hβ : 0 ≤ (q - p + s) / 2 := by
    have : |p - q| ≤ s := by
      rw [hs, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg c])
    linarith [le_abs_self (p - q)]
  have hαβ : (p - q + s) / 2 * ((q - p + s) / 2) = c ^ 2 := by nlinarith [hs2]
  -- form = α v₀² + 2c v₀v₁ + β v₁² ≥ 0
  set α := (p - q + s) / 2
  set β := (q - p + s) / 2
  have hform : 0 ≤ α * v₀ ^ 2 + 2 * c * v₀ * v₁ + β * v₁ ^ 2 := by
    rcases eq_or_lt_of_le hα with h | h
    · have hc : c = 0 := by
        have : c ^ 2 = 0 := by rw [← hαβ, ← h]; ring
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      rw [← h, hc]; nlinarith [sq_nonneg v₁]
    · have : 0 ≤ α * (α * v₀ ^ 2 + 2 * c * v₀ * v₁ + β * v₁ ^ 2) := by
        have e : α * (α * v₀ ^ 2 + 2 * c * v₀ * v₁ + β * v₁ ^ 2) = (α * v₀ + c * v₁) ^ 2 := by
          nlinarith [hαβ]
        rw [e]; positivity
      nlinarith [this, h]
  have : p * v₀ ^ 2 + 2 * c * v₀ * v₁ + q * v₁ ^ 2 - (p + q - s) / 2 * (v₀ ^ 2 + v₁ ^ 2)
      = α * v₀ ^ 2 + 2 * c * v₀ * v₁ + β * v₁ ^ 2 := by simp only [α, β]; ring
  linarith

/-- **(1,2) block**: diagonal `1 − δ₁`, `2(1 − δ₂)`, off-diagonal `√2(κ − e)`, `e² ≤ δ₁δ₂`, `δᵢ ≥ 0`, `κ ≥ 0`:
`tr f(X) ≥ (1/2 + (1/4 + 2κ²)^{1/2})²`. Proof: Rayleigh quotient of `X` at the λ_min-eigenvector
`(√2κ, 1/2 − s)` of the `Ê = 0` matrix, `s = (1/4 + 2κ²)^{1/2}`; the `Ê`-part of the form is `≥ 0`. -/
lemma block12_ge (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.IsHermitian) {δ₁ δ₂ κ e : ℝ}
    (h00 : X 0 0 = 1 - δ₁) (h11 : X 1 1 = 2 * (1 - δ₂)) (h01 : X 0 1 = Real.sqrt 2 * (κ - e))
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hκ0 : 0 ≤ κ) (he : e ^ 2 ≤ δ₁ * δ₂) :
    (1 / 2 + Real.sqrt (1 / 4 + 2 * κ ^ 2)) ^ 2 ≤ trFun hX fT := by
  refine le_trans ?_ (trFun_two_ge X hX)
  set s := Real.sqrt (1 / 4 + 2 * κ ^ 2) with hs
  have hs2 : s ^ 2 = 1 / 4 + 2 * κ ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs12 : 1 / 2 ≤ s := by
    rw [hs, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg κ])
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  set lmin := (X 0 0 + X 1 1 - Real.sqrt ((X 0 0 - X 1 1) ^ 2 + 4 * X 0 1 ^ 2)) / 2 with hlmin
  have hle : lmin ≤ 3 / 2 - s := by
    rcases eq_or_lt_of_le hκ0 with hk | hk
    · -- κ = 0: test vector (1, 0)
      have := rayleigh_two (X 0 0) (X 1 1) (X 0 1) 1 0
      have hk' : κ = 0 := hk.symm
      have hs' : s = 1 / 2 := by
        rw [hs, hk']; norm_num
      simp only [one_pow, zero_pow two_ne_zero, add_zero, mul_one, mul_zero, zero_mul] at this
      rw [hlmin, hs']; linarith [h00, hδ₁]
    · -- test vector v = (√2κ, 1/2 − s)
      have hR := rayleigh_two (X 0 0) (X 1 1) (X 0 1) (Real.sqrt 2 * κ) (1 / 2 - s)
      rw [← hlmin] at hR
      have hv : 0 < (Real.sqrt 2 * κ) ^ 2 + (1 / 2 - s) ^ 2 := by
        have : 0 < (Real.sqrt 2 * κ) ^ 2 := by
          have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
          positivity
        nlinarith [sq_nonneg (1 / 2 - s)]
      -- the Ê-free form equals (3/2 − s)|v|², the Ê-part is ≥ 0
      have hform : X 0 0 * (Real.sqrt 2 * κ) ^ 2 + 2 * X 0 1 * (Real.sqrt 2 * κ) * (1 / 2 - s)
            + X 1 1 * (1 / 2 - s) ^ 2
          ≤ (3 / 2 - s) * ((Real.sqrt 2 * κ) ^ 2 + (1 / 2 - s) ^ 2) := by
        rw [h00, h11, h01]
        have key : 0 ≤ δ₁ * κ ^ 2 + 2 * e * κ * (1 / 2 - s) + δ₂ * (1 / 2 - s) ^ 2 := by
          rcases eq_or_lt_of_le (add_nonneg hδ₁ hδ₂) with h0 | hpos
          · have hd1 : δ₁ = 0 := by linarith
            have hd2 : δ₂ = 0 := by linarith
            have he2 : e ^ 2 = 0 := le_antisymm (by rw [hd1, zero_mul] at he; exact he) (sq_nonneg e)
            have he0 : e = 0 := pow_eq_zero_iff two_ne_zero |>.1 he2
            rw [hd1, hd2, he0]; ring_nf; exact le_rfl
          · have hmul : 0 ≤ (δ₁ + δ₂) * (δ₁ * κ ^ 2 + 2 * e * κ * (1 / 2 - s) + δ₂ * (1 / 2 - s) ^ 2) := by
              nlinarith [sq_nonneg (δ₁ * κ + e * (1 / 2 - s)), sq_nonneg (δ₂ * (1 / 2 - s) + e * κ),
                mul_nonneg (sub_nonneg.2 he) (add_nonneg (sq_nonneg κ) (sq_nonneg (1 / 2 - s)))]
            nlinarith [hmul, hpos]
        have hEform : 0 ≤ δ₁ * (2 * κ ^ 2) + 2 * (2 * e * κ) * (1 / 2 - s) + 2 * δ₂ * (1 / 2 - s) ^ 2 := by
          nlinarith [key]
        have e1 : (1 - δ₁) * (Real.sqrt 2 * κ) ^ 2 + 2 * (Real.sqrt 2 * (κ - e)) * (Real.sqrt 2 * κ) * (1 / 2 - s)
              + 2 * (1 - δ₂) * (1 / 2 - s) ^ 2
            = (2 * κ ^ 2 + 4 * κ * κ * (1 / 2 - s) + 2 * (1 / 2 - s) ^ 2)
              - (δ₁ * (2 * κ ^ 2) + 2 * (2 * e * κ) * (1 / 2 - s) + 2 * δ₂ * (1 / 2 - s) ^ 2) := by
          have : (Real.sqrt 2 * κ) ^ 2 = 2 * κ ^ 2 := by rw [mul_pow, hr2]
          have h2 : 2 * (Real.sqrt 2 * (κ - e)) * (Real.sqrt 2 * κ) = 4 * (κ - e) * κ := by
            have : Real.sqrt 2 * Real.sqrt 2 = 2 := by rw [← sq, hr2]
            calc 2 * (Real.sqrt 2 * (κ - e)) * (Real.sqrt 2 * κ)
                = 2 * (Real.sqrt 2 * Real.sqrt 2) * (κ - e) * κ := by ring
              _ = 4 * (κ - e) * κ := by rw [this]; ring
          rw [this, h2]; ring
        have e2 : (3 / 2 - s) * ((Real.sqrt 2 * κ) ^ 2 + (1 / 2 - s) ^ 2)
            = 2 * κ ^ 2 + 4 * κ * κ * (1 / 2 - s) + 2 * (1 / 2 - s) ^ 2 := by
          rw [mul_pow, hr2]; linear_combination (1 / 2 - s) * hs2
        rw [e1, e2]; linarith
      have := le_trans hR hform
      exact le_of_mul_le_mul_right (by linarith) hv
  calc (1 / 2 + s) ^ 2 = fT (3 / 2 - s) := by rw [fT_of_le (by linarith)]; ring
    _ ≤ fT lmin := fT_antitone hle

end A6aux

end ZetaS
