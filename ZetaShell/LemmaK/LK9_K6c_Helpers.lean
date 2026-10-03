/-
L7_9 round 2: groundwork for the open sub-node K6c′ (`pnt_step`), step (c1) of the split proposed in the report:
Abel summation for the partial sums of a product, `C₀(n) = E(n)w(n) − Σ_{m<n} E(m)(w(m+1) − w(m))` with
`E = psum · a`. Not yet used by any proof.
-/
import ZetaShell.LemmaK.LK9_K6_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK
namespace K6

open Classical in
/-- `Λ′(n) = Λ(n)·1{n = p^k, p > R}` (the weight of `aPrime`). -/
def lamP (R : ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ R < (n.minFac : ℝ) then ArithmeticFunction.vonMangoldt n else 0

/-- `ϱa′ − w̃ = (Λ′ − 1)w̃`. -/
theorem asmooth_sub_wmod (T s R : ℝ) (n : ℕ) :
    asmooth T s R n - wmod T s n = ((lamP R n - 1 : ℝ) : ℂ) * wmod T s n := by
  unfold asmooth aPrime acoef wmod lamP
  split_ifs
  · push_cast; ring
  · push_cast; ring

/-- **(c1)** Abel summation for `psum` of a product. -/
theorem psum_mul_abel (n : ℕ) (a w : ℕ → ℂ) :
    psum n (fun m => a m * w m)
      = psum n a * w n - ∑ m ∈ Finset.range n, psum m a * (w (m + 1) - w m) := by
  induction n with
  | zero => simp [psum]
  | succ n ih =>
    have h1 : psum (n + 1) (fun m => a m * w m) = psum n (fun m => a m * w m) + a (n + 1) * w (n + 1) := by
      unfold psum
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
    have h2 : psum (n + 1) a = psum n a + a (n + 1) := by
      unfold psum
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
    rw [h1, ih, h2, Finset.sum_range_succ]
    ring

end K6
end LemmaK
end ZetaShell
