/-
Node Z6c (L7_10): **Lemma 6c, `O(1/ε′)` blocks** (lem:shell-6c, sec_shell.tex l.691–697):
"Put `R_i := R₁N₀^{−iε′}`, `𝔅_i := {R_{i+1} < r ≤ R_i}`, `0 ≤ i ≤ ⌈1/ε′⌉`. For `r ∈ 𝔅_i`, `H_r ≤ H_i :=
2T+1+KN₀^{1+ε′}/(R_iQ)`. Hence `𝔛` is covered, up to the height shells `2^{j−1}H_i < |γ| ≤ 2^jH_i` (where
`ϖ ≪ 2^{−k(j−1)}`), by `⌈1/ε′⌉+1` rectangles with `R_i²H_i^h ≤ 𝒵N₀^{2ε′}`. Every block has `R ≥ 1` (or is `{r=1}`)
and `H ≥ 2T+1 ≥ 2`."
Lean form, four parts:
 (1) cover: every `1 ≤ r ≤ R₁` lies in a block `i ≤ ⌈1/ε′⌉` and `H_r = 2T+1+μ_r ≤ H_i` (needs `R₁ ≤ N₀`);
 (2) rectangles: a NONEMPTY block has `R_i ≥ 1`, and then `R_i² H_i^h ≤ 𝒵 N₀^{2ε′}` for `h ∈ [0,2]` (Z6b at `j = 0`);
 (3) shells: `2^j (2T+1+μ) < |γ|` implies `ϖ_ρ(μ) ≤ 2^{−kj}` (the draft's `2^{−k(j−1)}` with the shell index shifted);
 (4) `H_i ≥ 2T+1`.
Dependencies: Z6b (`shell_rectangles`, proved by L7_6), real powers. Difficulty: E–M.
-/
import ZetaShell.ShellS.L10_Defs

noncomputable section

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- `R_i = R₁ N₀^{−iε′}`. -/
def Rblk (R1 N0 ε' : ℝ) (i : ℕ) : ℝ := R1 * N0 ^ (-((i : ℝ) * ε'))

/-- `H_i = 2T + 1 + K N₀^{1+ε′}/(R_i Q)`. -/
def Hblk (T K N0 Q R1 ε' : ℝ) (i : ℕ) : ℝ := 2 * T + 1 + K * N0 ^ (1 + ε') / (Rblk R1 N0 ε' i * Q)

theorem Z6c_cover (T K N0 Q R1 ε' : ℝ) (hT : 1 ≤ T) (hK : 0 ≤ K) (hQ : 0 < Q) (hN0 : 1 < N0) (hR1 : 1 ≤ R1)
    (hR1N : R1 ≤ N0) (hε' : 0 < ε') (hε1 : ε' ≤ 1) :
    ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ R1 → ∃ i : ℕ, i ≤ ⌈1 / ε'⌉₊ ∧ Rblk R1 N0 ε' (i + 1) < r ∧
        (r : ℝ) ≤ Rblk R1 N0 ε' i ∧ 2 * T + 1 + K * N0 / (r * Q) ≤ Hblk T K N0 Q R1 ε' i := by
  intro r hr1 hrR
  have hN0pos : 0 < N0 := by linarith
  have hL : 0 < Real.log N0 := Real.log_pos hN0
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hR1pos : 0 < R1 := by linarith
  have key : ∀ y : ℝ, R1 * N0 ^ y = Real.exp (Real.log R1 + Real.log N0 * y) := by
    intro y; rw [Real.rpow_def_of_pos hN0pos, Real.exp_add, Real.exp_log hR1pos]
  have hlogdiv : Real.log (R1 / r) = Real.log R1 - Real.log r := Real.log_div hR1pos.ne' hrpos.ne'
  have hεL : 0 < ε' * Real.log N0 := mul_pos hε' hL
  set x := Real.log (R1 / r) / (ε' * Real.log N0) with hx
  have hRr : 1 ≤ R1 / r := (one_le_div hrpos).mpr hrR
  have hx0 : 0 ≤ x := div_nonneg (Real.log_nonneg hRr) hεL.le
  have hxL : x * (ε' * Real.log N0) = Real.log R1 - Real.log r := by
    rw [hx, div_mul_cancel₀ _ hεL.ne', hlogdiv]
  set i := ⌊x⌋₊ with hi
  have hi_le : (i : ℝ) ≤ x := Nat.floor_le hx0
  have hi_lt : x < (i : ℝ) + 1 := Nat.lt_floor_add_one x
  -- `r ≤ R_i`
  have hc : (r : ℝ) ≤ Rblk R1 N0 ε' i := by
    unfold Rblk; rw [key, ← Real.exp_log hrpos]
    apply Real.exp_le_exp.mpr
    have : (i : ℝ) * (ε' * Real.log N0) ≤ x * (ε' * Real.log N0) := mul_le_mul_of_nonneg_right hi_le hεL.le
    nlinarith [this, hxL]
  -- `R_{i+1} < r`
  have hb : Rblk R1 N0 ε' (i + 1) < r := by
    unfold Rblk; rw [key, ← Real.exp_log hrpos]
    apply Real.exp_lt_exp.mpr
    have : x * (ε' * Real.log N0) < ((i : ℝ) + 1) * (ε' * Real.log N0) := mul_lt_mul_of_pos_right hi_lt hεL
    push_cast
    nlinarith [this, hxL]
  refine ⟨i, ?_, hb, hc, ?_⟩
  · -- `i ≤ ⌈1/ε'⌉`
    have hxle : x ≤ 1 / ε' := by
      rw [hx, div_le_div_iff₀ hεL hε']
      have h1 : R1 / r ≤ N0 := le_trans (div_le_self hR1pos.le hr1') hR1N
      have h2 : Real.log (R1 / r) ≤ Real.log N0 := Real.log_le_log (by positivity) h1
      nlinarith [h2, hε']
    exact le_trans (Nat.floor_le_ceil x) (Nat.ceil_mono hxle)
  · -- `H_r ≤ H_i`
    have hRi_pos : 0 < Rblk R1 N0 ε' i := by unfold Rblk; positivity
    have hRi_lt : Rblk R1 N0 ε' i < N0 ^ ε' * r := by
      have e1 : Rblk R1 N0 ε' i = Real.exp (Real.log R1 + Real.log N0 * (-((i : ℝ) * ε'))) := by
        unfold Rblk; rw [key]
      have e2 : N0 ^ ε' * r = Real.exp (Real.log N0 * ε' + Real.log r) := by
        rw [Real.rpow_def_of_pos hN0pos, Real.exp_add, Real.exp_log hrpos]
      rw [e1, e2]
      apply Real.exp_lt_exp.mpr
      have : x * (ε' * Real.log N0) < ((i : ℝ) + 1) * (ε' * Real.log N0) := mul_lt_mul_of_pos_right hi_lt hεL
      nlinarith [this, hxL]
    have hpow : N0 ^ (1 + ε') = N0 * N0 ^ ε' := by
      rw [Real.rpow_add hN0pos, Real.rpow_one]
    unfold Hblk
    have hfrac : K * N0 / (r * Q) ≤ K * N0 ^ (1 + ε') / (Rblk R1 N0 ε' i * Q) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), hpow]
      have hmono : K * N0 * Q * Rblk R1 N0 ε' i ≤ K * N0 * Q * (N0 ^ ε' * r) :=
        mul_le_mul_of_nonneg_left hRi_lt.le (by positivity)
      nlinarith [hmono]
    linarith

theorem Z6c_rect (T K N0 Q R1 ε' : ℝ) (hT : 1 ≤ T) (hK : 0 ≤ K) (hQ : 0 < Q) (hN0 : 1 < N0) (hR1 : 1 ≤ R1)
    (hε' : 0 < ε') (i : ℕ) (h : ℝ) (hRi : 1 ≤ Rblk R1 N0 ε' i) (hh0 : 0 ≤ h) (hh2 : h ≤ 2) :
    Rblk R1 N0 ε' i ^ 2 * Hblk T K N0 Q R1 ε' i ^ h ≤ Zsize R1 T K N0 Q * N0 ^ (2 * ε') := by
  have hx : N0 ^ (-((i : ℝ) * ε')) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN0.le (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg i) hε'.le))
  have hle : Rblk R1 N0 ε' i ≤ R1 := by
    unfold Rblk; exact mul_le_of_le_one_right (by linarith) hx
  have hRi0 : 0 ≤ Rblk R1 N0 ε' i := by linarith
  have hy : 0 ≤ K * N0 ^ (1 + ε') / (Rblk R1 N0 ε' i * Q) :=
    div_nonneg (mul_nonneg hK (Real.rpow_nonneg (by linarith) _)) (mul_nonneg hRi0 hQ.le)
  have hH0 : 0 ≤ Hblk T K N0 Q R1 ε' i := by unfold Hblk; linarith
  have hHle : Hblk T K N0 Q R1 ε' i ≤ 2 ^ 0 * (2 * T + 1 + K * N0 ^ (1 + ε') / (Rblk R1 N0 ε' i * Q)) := by
    unfold Hblk; simp
  have := shell_rectangles (Rblk R1 N0 ε' i) R1 (Hblk T K N0 Q R1 ε' i) T K N0 Q ε' h 0 hRi0 hle (by linarith)
    hK hN0.le hQ hε'.le hH0 hHle hh0 hh2
  simpa using this

theorem Z6c_shell (T : ℝ) (hT : 1 ≤ T) (μ : ℝ) (k j : ℕ) (ρ : ℂ) (hμ : 0 ≤ μ)
    (hγ : 2 ^ j * (2 * T + 1 + μ) < |ρ.im|) :
    varpi T μ k ρ ≤ ((2 : ℝ) ^ j)⁻¹ ^ k := by
  unfold varpi
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hμ1 : 0 < μ + 1 := by linarith
  have hT2 : 0 ≤ 2 * T * (2 ^ j - 1) := mul_nonneg (by linarith) (by linarith)
  have hkey : (2 : ℝ) ^ j * (μ + 1) ≤ max (|ρ.im| - 2 * T) 0 := by
    have hm : |ρ.im| - 2 * T ≤ max (|ρ.im| - 2 * T) 0 := le_max_left _ _
    nlinarith [hγ, hT2]
  have hdiv : (2 : ℝ) ^ j ≤ max (|ρ.im| - 2 * T) 0 / (μ + 1) := by
    rw [le_div_iff₀ hμ1]; exact hkey
  have hx : (2 : ℝ) ^ j ≤ 1 + max (|ρ.im| - 2 * T) 0 / (μ + 1) := by linarith
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  calc (1 + max (|ρ.im| - 2 * T) 0 / (μ + 1)) ^ (-(k : ℝ))
      ≤ ((2 : ℝ) ^ j) ^ (-(k : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos hx (neg_nonpos.mpr (Nat.cast_nonneg k))
    _ = ((2 : ℝ) ^ j)⁻¹ ^ k := by
        rw [Real.rpow_neg hpos.le, Real.rpow_natCast, inv_pow]

theorem Z6c_Hge (T K N0 Q R1 ε' : ℝ) (hK : 0 ≤ K) (hQ : 0 < Q) (hN0 : 1 < N0) (hR1 : 1 ≤ R1) (i : ℕ) :
    2 * T + 1 ≤ Hblk T K N0 Q R1 ε' i := by
  have hRi0 : 0 ≤ Rblk R1 N0 ε' i := mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
  have hy : 0 ≤ K * N0 ^ (1 + ε') / (Rblk R1 N0 ε' i * Q) :=
    div_nonneg (mul_nonneg hK (Real.rpow_nonneg (by linarith) _)) (mul_nonneg hRi0 hQ.le)
  unfold Hblk; linarith

theorem Z6c_blocks (T K N0 Q R1 ε' : ℝ) (hT : 1 ≤ T) (hK : 0 ≤ K) (hQ : 0 < Q) (hN0 : 1 < N0) (hR1 : 1 ≤ R1)
    (hR1N : R1 ≤ N0) (hε' : 0 < ε') (hε1 : ε' ≤ 1) :
    (∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ R1 → ∃ i : ℕ, i ≤ ⌈1 / ε'⌉₊ ∧ Rblk R1 N0 ε' (i + 1) < r ∧
        (r : ℝ) ≤ Rblk R1 N0 ε' i ∧ 2 * T + 1 + K * N0 / (r * Q) ≤ Hblk T K N0 Q R1 ε' i) ∧
    (∀ (i : ℕ) (h : ℝ), 1 ≤ Rblk R1 N0 ε' i → 0 ≤ h → h ≤ 2 →
        Rblk R1 N0 ε' i ^ 2 * Hblk T K N0 Q R1 ε' i ^ h ≤ Zsize R1 T K N0 Q * N0 ^ (2 * ε')) ∧
    (∀ (μ : ℝ) (k j : ℕ) (ρ : ℂ), 0 ≤ μ → 2 ^ j * (2 * T + 1 + μ) < |ρ.im| →
        varpi T μ k ρ ≤ ((2 : ℝ) ^ j)⁻¹ ^ k) ∧
    (∀ i : ℕ, 2 * T + 1 ≤ Hblk T K N0 Q R1 ε' i) :=
  ⟨Z6c_cover T K N0 Q R1 ε' hT hK hQ hN0 hR1 hR1N hε' hε1,
   fun i h hRi hh0 hh2 => Z6c_rect T K N0 Q R1 ε' hT hK hQ hN0 hR1 hε' i h hRi hh0 hh2,
   fun μ k j ρ hμ hγ => Z6c_shell T hT μ k j ρ hμ hγ,
   fun i => Z6c_Hge T K N0 Q R1 ε' hK hQ hN0 hR1 i⟩

end ShellS
end ZetaShell
