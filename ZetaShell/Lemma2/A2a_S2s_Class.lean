/-
A2a_S2s_Class (L7_8, round 3): one Möbius term: for squarefree `g | j`, the `k` with `g | k`, `f | q` form one class
mod `m = lcm(g, f_(r))` or none (`oneClass_closed`, `oneClass_unique`, `admissible_exists`, `admissible_necessary`,
proved), so `q` runs through a progression of step `rm`, and the sum of `w(qe/Q)` over it differs from
`(1/(rm))∫_{lo}^{hi} w(qe/Q)dq` by at most `2V*` (`Var(w·1_{[lo,hi]}) ≤ Var(w) + 2‖w‖_∞`; for `w` an indicator this is
`progression_count`).
Round 4: PROVED (sorry-free) via `Pg_reparam`, `fam_prog_data`, `prog_general` (error `≤ 4 ≤ 2V*`).
-/
import ZetaShell.Lemma2.A2a_S2s_Defs
import ZetaShell.Lemma2.A2a_S2c_ProgGeneral
import ZetaShell.Lemma2.A2a_S2c_FamData
import ZetaShell.Lemma2.A2a_S2c_Reparam
import ZetaShell.Lemma2.A2a_S2_CRTExist
import ZetaShell.Lemma2.A2a_S2s_MainAux

noncomputable section
open scoped BigOperators
open Classical

namespace ZetaShell
namespace TrackF

theorem s2_class (F : Fam) (Q : ℕ) (hQ : 1 ≤ Q) (r r' j : ℤ) (e f g : ℕ) (lo hi : ℝ) (hr : 1 ≤ r)
    (hrr' : Int.gcd r r' = 1) (hj : j ≠ 0) (he : 1 ≤ e) (hf : Squarefree f) (hg : g ∈ j.natAbs.divisors)
    (hgsq : Squarefree g) (hlh : lo ≤ hi) :
    |Pg F Q r r' j e f g lo hi
        - (if admissibleP r j f then (1 / ((r : ℝ) * (Nat.lcm g (fOff f r) : ℝ))) * (∫ q in lo..hi, F.w (q * e / Q))
            else 0)|
      ≤ 2 * Vstar F := by
  have hV : 2 ≤ Vstar F := by cases F <;> simp only [Vstar] <;> norm_num
  have hcop : IsCoprime r r' := Int.isCoprime_iff_gcd_eq_one.mpr hrr'
  have hgpos : 0 < g := Nat.pos_of_mem_divisors hg
  have hgj : (g : ℤ) ∣ j := Int.natCast_dvd.mpr (Nat.dvd_of_mem_divisors hg)
  by_cases hadm : admissibleP r j f
  · rw [if_pos hadm]
    obtain ⟨k0, hk0⟩ := admissible_exists r r' j g f hf hgj hadm
    have hm : 0 < Nat.lcm g (fOff f r) := Nat.lcm_pos hgpos (fOff_pos f r)
    have hS : ∀ k : ℤ, ((g : ℤ) ∣ k ∧ (f : ℤ) ∣ r * k - r' * j) ↔ ((Nat.lcm g (fOff f r) : ℕ) : ℤ) ∣ k - k0 := by
      intro k
      constructor
      · intro hk
        exact oneClass_unique f g r r' j k k0 hk hk0
      · rintro ⟨t, ht⟩
        have hkk : k = k0 + t * ((Nat.lcm g (fOff f r) : ℕ) : ℤ) := by linarith
        rw [hkk]
        exact oneClass_closed f g hf r r' j k0 t hk0
    rw [Pg_reparam F Q r r' j e f g lo hi hr k0 (Nat.lcm g (fOff f r)) hm hS]
    obtain ⟨a, b, φ, hab, hanti, hφ0, hφ1, hWin, hWout, hW0, hW1⟩ := fam_prog_data F Q e hQ he
    have hrR : (0 : ℝ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
    have hmR : (0 : ℝ) < ((Nat.lcm g (fOff f r) : ℕ) : ℝ) := by exact_mod_cast hm
    have hG := prog_general (fun x => F.w (x * e / Q)) φ a b lo hi ((r * k0 - r' * j : ℤ) : ℝ)
      ((r : ℝ) * ((Nat.lcm g (fOff f r) : ℕ) : ℝ)) (mul_pos hrR hmR) hab hlh hanti hφ0 hφ1 hWin hWout hW0 hW1
    exact le_trans hG (by linarith)
  · rw [if_neg hadm, sub_zero]
    have h0 : Pg F Q r r' j e f g lo hi = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg]
      intro hk
      exact hadm (admissible_necessary r r' j f hcop k hk.2)
    rw [h0, abs_zero]
    linarith

end TrackF
end ZetaShell
