/-
A2a_S2c_Reparam (L7_8, round 4): if the admissible `k` (`g | k`, `f | rk − r′j`) are exactly `k ≡ k₀ (mod m)`, then
`Pg = Σ_{i : lo ≤ q₀ + rm·i ≤ hi} w((q₀ + rm·i)e/Q)`, `q₀ = rk₀ − r′j` (`Pg_reparam`).
-/
import ZetaShell.Lemma2.A2a_S2s_Defs

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem ceil_le_iff_mul {x y : ℝ} (hy : 0 < y) (z : ℤ) : ⌈x / y⌉ ≤ z ↔ x ≤ y * z := by
  rw [Int.ceil_le, div_le_iff₀ hy, mul_comm]

theorem le_floor_iff_mul {x y : ℝ} (hy : 0 < y) (z : ℤ) : z ≤ ⌊x / y⌋ ↔ y * z ≤ x := by
  rw [Int.le_floor, le_div_iff₀ hy, mul_comm]

theorem Pg_reparam (F : Fam) (Q : ℕ) (r r' j : ℤ) (e f g : ℕ) (lo hi : ℝ) (hr : 1 ≤ r) (k0 : ℤ) (m : ℕ)
    (hm : 0 < m) (hS : ∀ k : ℤ, ((g : ℤ) ∣ k ∧ (f : ℤ) ∣ r * k - r' * j) ↔ (m : ℤ) ∣ k - k0) :
    Pg F Q r r' j e f g lo hi
      = ∑ i ∈ Finset.Icc ⌈(lo - ((r * k0 - r' * j : ℤ) : ℝ)) / ((r : ℝ) * (m : ℝ))⌉
          ⌊(hi - ((r * k0 - r' * j : ℤ) : ℝ)) / ((r : ℝ) * (m : ℝ))⌋,
          F.w ((((r * k0 - r' * j : ℤ) : ℝ) + (r : ℝ) * (m : ℝ) * i) * e / Q) := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : (0 : ℝ) < (r : ℝ) * (m : ℝ) := mul_pos hrR hmR
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  -- the q-value of k = k0 + m t
  have hq : ∀ t : ℤ, (((r * (k0 + m * t) - r' * j : ℤ)) : ℝ)
      = ((r * k0 - r' * j : ℤ) : ℝ) + (r : ℝ) * (m : ℝ) * t := by
    intro t; push_cast; ring
  -- range of k in terms of q
  have hk : ∀ k : ℤ, k ∈ Finset.Icc ⌈(lo + r' * j) / r⌉ ⌊(hi + r' * j) / r⌋ ↔
      lo ≤ ((r * k - r' * j : ℤ) : ℝ) ∧ ((r * k - r' * j : ℤ) : ℝ) ≤ hi := by
    intro k
    rw [Finset.mem_Icc, ceil_le_iff_mul hrR, le_floor_iff_mul hrR]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hi' : ∀ i : ℤ, i ∈ Finset.Icc ⌈(lo - ((r * k0 - r' * j : ℤ) : ℝ)) / ((r : ℝ) * (m : ℝ))⌉
      ⌊(hi - ((r * k0 - r' * j : ℤ) : ℝ)) / ((r : ℝ) * (m : ℝ))⌋ ↔
      lo ≤ ((r * k0 - r' * j : ℤ) : ℝ) + (r : ℝ) * (m : ℝ) * i ∧
        ((r * k0 - r' * j : ℤ) : ℝ) + (r : ℝ) * (m : ℝ) * i ≤ hi := by
    intro i
    rw [Finset.mem_Icc, ceil_le_iff_mul hh, le_floor_iff_mul hh]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  unfold Pg
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun k => (k - k0) / m) (fun i => k0 + m * i)
  · intro k hk'
    rw [Finset.mem_filter] at hk'
    obtain ⟨t, ht⟩ := (hS k).mp hk'.2
    have hkt : k = k0 + m * t := by linarith
    have hdiv : (k - k0) / (m : ℤ) = t := by rw [ht]; exact Int.mul_ediv_cancel_left t hmZ.ne'
    rw [hdiv, hi', ← hq, ← hkt]
    exact (hk k).mp hk'.1
  · intro i hi''
    rw [Finset.mem_filter]
    refine ⟨(hk _).mpr ?_, (hS _).mpr ⟨i, by ring⟩⟩
    rw [hq]
    exact (hi' i).mp hi''
  · intro k hk'
    rw [Finset.mem_filter] at hk'
    obtain ⟨t, ht⟩ := (hS k).mp hk'.2
    have hdiv : (k - k0) / (m : ℤ) = t := by rw [ht]; exact Int.mul_ediv_cancel_left t hmZ.ne'
    rw [hdiv]
    linarith
  · intro i _
    rw [show k0 + (m : ℤ) * i - k0 = (m : ℤ) * i by ring]
    exact Int.mul_ediv_cancel_left i hmZ.ne'
  · intro k hk'
    rw [Finset.mem_filter] at hk'
    obtain ⟨t, ht⟩ := (hS k).mp hk'.2
    have hdiv : (k - k0) / (m : ℤ) = t := by rw [ht]; exact Int.mul_ediv_cancel_left t hmZ.ne'
    have hkt : k = k0 + m * t := by linarith
    rw [hdiv, ← hq, ← hkt]

end TrackF
end ZetaShell
