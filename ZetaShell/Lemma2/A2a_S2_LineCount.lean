/-
A2a_S2_LineCount (L7_8, round 2 statement; round 3 derivation): **Step 2 of the proof of Lemma 2(a)**, one line `j`,
one `(e, f)` (sec_shell.tex l.323–333), with the per-class error `2V*` (ruling of 14:27).

`N_j(e,f) = Σ_{k : (k,j)=1, q = rk − r′j ∈ [lo,hi], f | q} w(qe/Q) = (1/r)∫_{lo}^{hi} w(qe/Q)dq · (φ(|j|)/|j|) ∏_{p|f} δ_p
+ ϑ·2V*·2^{ω(|j|)}`, `|ϑ| ≤ 1`, for `f` squarefree, `(r, r′) = 1`, `r ≥ 1`, `j ≠ 0`, `e ≥ 1`, `lo ≤ hi`.
Statement unchanged since round 2.

Round 3: DERIVED here from the sub-nodes `s2_expand` (Möbius expansion over `g | |j|`), `s2_class` (one class per `g`,
error `2V*`), `s2_main` (the Möbius main-term identity), `s2_abs_mu` (`Σ_{g|n}|μ(g)| = 2^{ω(n)}`).
-/
import ZetaShell.Lemma2.A2a_S2s_Expand
import ZetaShell.Lemma2.A2a_S2s_Class
import ZetaShell.Lemma2.A2a_S2s_Main
import ZetaShell.Lemma2.A2a_S2s_AbsMu

noncomputable section
open scoped BigOperators
open Classical

namespace ZetaShell
namespace TrackF

theorem step2_line_count (F : Fam) (Q : ℕ) (hQ : 1 ≤ Q) (r r' j : ℤ) (e f : ℕ) (lo hi : ℝ)
    (hr : 1 ≤ r) (hrr' : Int.gcd r r' = 1) (hj : j ≠ 0) (he : 1 ≤ e) (hf : Squarefree f) (hlh : lo ≤ hi) :
    |lineCount F Q r r' j e f lo hi
        - (1 / (r : ℝ)) * (∫ q in lo..hi, F.w (q * e / Q)) * ((Nat.totient j.natAbs : ℝ) / j.natAbs) *
            deltaProd r j f|
      ≤ 2 * Vstar F * 2 ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) := by
  rw [s2_expand F Q r r' j e f lo hi hj]
  have hmain := s2_main r j f hr hj hf
  have key : (1 / (r : ℝ)) * (∫ q in lo..hi, F.w (q * e / Q)) * ((Nat.totient j.natAbs : ℝ) / j.natAbs) *
        deltaProd r j f
      = ∑ g ∈ j.natAbs.divisors, ((ArithmeticFunction.moebius g : ℤ) : ℝ) *
          (if admissibleP r j f then (1 / ((r : ℝ) * (Nat.lcm g (fOff f r) : ℝ))) *
              (∫ q in lo..hi, F.w (q * e / Q)) else 0) := by
    have e1 : (1 / (r : ℝ)) * (∫ q in lo..hi, F.w (q * e / Q)) * ((Nat.totient j.natAbs : ℝ) / j.natAbs) *
          deltaProd r j f
        = ((1 / (r : ℝ)) * ((Nat.totient j.natAbs : ℝ) / j.natAbs) * deltaProd r j f) *
            (∫ q in lo..hi, F.w (q * e / Q)) := by ring
    rw [e1, ← hmain, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> ring
  rw [key, ← Finset.sum_sub_distrib]
  have hV : 0 ≤ Vstar F := by cases F <;> simp only [Vstar] <;> norm_num
  calc |∑ g ∈ j.natAbs.divisors, (((ArithmeticFunction.moebius g : ℤ) : ℝ) * Pg F Q r r' j e f g lo hi
          - ((ArithmeticFunction.moebius g : ℤ) : ℝ) *
            (if admissibleP r j f then (1 / ((r : ℝ) * (Nat.lcm g (fOff f r) : ℝ))) *
                (∫ q in lo..hi, F.w (q * e / Q)) else 0))|
      ≤ ∑ g ∈ j.natAbs.divisors, |((ArithmeticFunction.moebius g : ℤ) : ℝ)| * (2 * Vstar F) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun g hg => ?_))
        rw [← mul_sub, abs_mul]
        by_cases hmu : (ArithmeticFunction.moebius g : ℤ) = 0
        · simp [hmu]
        · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have hsq : Squarefree g := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
          exact s2_class F Q hQ r r' j e f g lo hi hr hrr' hj he hf hg hsq hlh
    _ = 2 * Vstar F * 2 ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) := by
        rw [← Finset.sum_mul, s2_abs_mu j.natAbs (Int.natAbs_ne_zero.mpr hj)]
        ring

end TrackF
end ZetaShell
