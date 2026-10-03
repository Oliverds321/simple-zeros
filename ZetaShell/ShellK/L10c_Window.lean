/-
L10c_Window (L7_10c, 3 Oct 2026): the window bookkeeping shared by `KT_transfer` and the K2 derivation.
* `bumpW`: a smooth bump, `= 1` on `[−1/2, 1/2]`, `0 ≤ · ≤ 1`, support in `[−3/4, 3/4]`; it is both an
  `AvgWeight` (Theorem S's averaging weight) and a `NearCutoff` (the near cutoff `Ξ` of AS / S).
* `cover`: every `s ∈ (a, b]` lies within `1/2` of a centre `a + k`, `k ≤ ⌈b − a⌉₊`.
* `dom_pointwise`: if `R ≤ R_k` near the centre `a + k`, then `R ≤ Σ_k W₀(s − (a+k)) R_k(s)` on `(a, b]`.
* `setIntegral_mul_le`: `∫_Z g·H ≤ G·∫ H` for `0 ≤ g ≤ G` continuous and `H ≥ 0` integrable.
-/
import ZetaShell.ShellK.L10_KDefs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellK
namespace K2c

open ZetaShell.PropZ

/-- `W₀(z) = smoothTransition((16/5)(9/16 − z²))`. -/
def bumpW (z : ℝ) : ℝ := Real.smoothTransition ((16 / 5) * (9 / 16 - z ^ 2))

theorem bumpW_support : Function.support bumpW ⊆ Set.Icc (-(3 / 4 : ℝ)) (3 / 4) := by
  intro z hz
  by_contra h
  apply hz
  apply Real.smoothTransition.zero_of_nonpos
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h <;> nlinarith

theorem bumpW_smooth : ContDiff ℝ (⊤ : ℕ∞) bumpW :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub (contDiff_id.pow 2)))

theorem bumpW_tsupport : tsupport bumpW ⊆ Set.Ioo (-1 : ℝ) 1 :=
  (closure_minimal bumpW_support isClosed_Icc).trans (Set.Icc_subset_Ioo (by norm_num) (by norm_num))

theorem bumpW_nonneg (z : ℝ) : 0 ≤ bumpW z := Real.smoothTransition.nonneg _

theorem bumpW_le_one (z : ℝ) : bumpW z ≤ 1 := Real.smoothTransition.le_one _

theorem bumpW_eq_one {z : ℝ} (hz : |z| ≤ 1 / 2) : bumpW z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h1 : z ^ 2 ≤ 1 / 4 := by
    have : |z| ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg z) hz 2
    rw [sq_abs] at this; linarith
  nlinarith

theorem bumpW_avg : AvgWeight bumpW := ⟨bumpW_smooth, bumpW_tsupport, bumpW_nonneg⟩

theorem bumpW_near : NearCutoff bumpW := ⟨bumpW_smooth, bumpW_tsupport, bumpW_nonneg, bumpW_le_one⟩

theorem bumpW_continuous : Continuous bumpW := bumpW_smooth.continuous

theorem bumpW_hasCompactSupport : HasCompactSupport bumpW :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (bumpW_tsupport.trans Set.Ioo_subset_Icc_self)

/-- every `s ∈ (a, b]` is within `1/2` of a centre `a + k`, `k ≤ ⌈b − a⌉₊`. -/
theorem cover (a b s : ℝ) (hs : a < s) (hsb : s ≤ b) :
    ∃ k ∈ Finset.range (⌈b - a⌉₊ + 1), |s - (a + k)| ≤ 1 / 2 := by
  have hx0 : 0 ≤ s - a + 1 / 2 := by linarith
  refine ⟨⌊s - a + 1 / 2⌋₊, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    have h1 : s - a + 1 / 2 < (⌈b - a⌉₊ : ℝ) + 1 := by linarith [Nat.le_ceil (b - a)]
    have h2 : ⌊s - a + 1 / 2⌋₊ < ⌈b - a⌉₊ + 1 := by
      rw [Nat.floor_lt hx0]; push_cast; exact h1
    omega
  · have h1 := Nat.floor_le hx0
    have h2 := Nat.lt_floor_add_one (s - a + 1 / 2)
    rw [abs_le]; constructor <;> linarith

/-- the pointwise window domination. -/
theorem dom_pointwise (a b : ℝ) (R : ℝ → ℝ) (Rk : ℕ → ℝ → ℝ) (hRk0 : ∀ k s, 0 ≤ Rk k s)
    (hmono : ∀ (k : ℕ) (s : ℝ), |s - (a + k)| ≤ 1 / 2 → R s ≤ Rk k s) (s : ℝ) (hs : s ∈ Set.Ioc a b) :
    R s ≤ ∑ k ∈ Finset.range (⌈b - a⌉₊ + 1), bumpW (s - (a + k)) * Rk k s := by
  obtain ⟨k, hk, hks⟩ := cover a b s hs.1 hs.2
  have h1 : R s ≤ bumpW (s - (a + k)) * Rk k s := by
    rw [bumpW_eq_one hks, one_mul]; exact hmono k s hks
  refine le_trans h1 ?_
  exact Finset.single_le_sum (f := fun j : ℕ => bumpW (s - (a + (j : ℝ))) * Rk j s)
    (fun j _ => mul_nonneg (bumpW_nonneg _) (hRk0 j s)) hk

/-- `∫_Z g·H ≤ G·∫ H`. -/
theorem setIntegral_mul_le (Z : Set ℝ) (hZ : MeasurableSet Z) (G : ℝ) (g H : ℝ → ℝ) (hg0 : ∀ s, 0 ≤ g s)
    (hgG : ∀ s, g s ≤ G) (hgc : Continuous g) (hH0 : ∀ s, 0 ≤ H s) (hHi : Integrable H) :
    (∫ s in Z, g s * H s) ≤ G * ∫ s, H s := by
  have hG0 : 0 ≤ G := le_trans (hg0 0) (hgG 0)
  have hgH : Integrable (fun s => g s * H s) := by
    refine Integrable.bdd_mul (c := G) hHi hgc.aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hgG s
  have h1 : (∫ s in Z, g s * H s) ≤ ∫ s in Z, G * H s := by
    apply setIntegral_mono_on hgH.integrableOn (hHi.const_mul G).integrableOn hZ
    intro s _
    exact mul_le_mul_of_nonneg_right (hgG s) (hH0 s)
  have h2 : (∫ s in Z, G * H s) ≤ G * ∫ s, H s := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hHi (ae_of_all _ hH0)) hG0
  linarith

end K2c
end ShellK
end ZetaShell
