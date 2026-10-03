/-
A2a_S3_Defs (L7_8, round 3, 28 Sep 2026): objects for the split of `step3_count` (Steps 0–3 of the proof of Lemma
2(a), sec_shell.tex l.306–341).
* `lineM Q r η δ = ⌊rQ(|η| + δ/2)⌋ + 1` and `lineSet M = {j : 0 < |j| ≤ M}` (the lines of `mainSum`).
* `lineIv Q r j η δ = (lo, hi)`: the `q`-interval `I_j = {q ∈ [1,Q] : j/(qr) ∈ [η − δ/2, η + δ/2]}` of line `j`
  (closed; `(1/2, 1/2)` when empty, so that no integer lies in it and `∫_{lo}^{hi} = 0`).
* `lam k e f = λ_e(f)`: `∏_{p|f}(h_e(p) − 1)` for squarefree `f`, `0` otherwise (Step 1, l.315–316).
* `mainJEF`: Step 2's main term `(1/r)(∫_{lo}^{hi} w(qe/Q)dq)(φ(|j|)/|j|)∏_{p|f}δ_p`.
-/
import ZetaShell.Lemma2.A2a_S2_LineCount

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

def lineM (Q r : ℕ) (η δ : ℝ) : ℕ := ⌊(r : ℝ) * Q * (|η| + δ / 2)⌋₊ + 1

def lineSet (M : ℕ) : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun j => j ≠ 0)

def lineIv (Q r : ℕ) (j : ℤ) (η δ : ℝ) : ℝ × ℝ :=
  if 0 < j then
    (if 0 < η + δ / 2 ∧ max 1 (|(j : ℝ)| / (r * (η + δ / 2)))
          ≤ (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ))
      then (max 1 (|(j : ℝ)| / (r * (η + δ / 2))),
            (if 0 < η - δ / 2 then min (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))) else (Q : ℝ)))
      else (1 / 2, 1 / 2))
  else
    (if η - δ / 2 < 0 ∧ max 1 (|(j : ℝ)| / (r * (-(η - δ / 2))))
          ≤ (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ))
      then (max 1 (|(j : ℝ)| / (r * (-(η - δ / 2)))),
            (if η + δ / 2 < 0 then min (Q : ℝ) (|(j : ℝ)| / (r * (-(η + δ / 2)))) else (Q : ℝ)))
      else (1 / 2, 1 / 2))

def lam (k : FKind) (e f : ℕ) : ℝ :=
  if Squarefree f then ∏ p ∈ f.primeFactors, (hE k e p - 1) else 0

def mainJEF (F : Fam) (Q : ℕ) (r j : ℤ) (e f : ℕ) (lo hi : ℝ) : ℝ :=
  (1 / (r : ℝ)) * (∫ q in lo..hi, F.w (q * e / Q)) * ((Nat.totient j.natAbs : ℝ) / j.natAbs) * deltaProd r j f

theorem lineIv_le (Q r : ℕ) (j : ℤ) (η δ : ℝ) : (lineIv Q r j η δ).1 ≤ (lineIv Q r j η δ).2 := by
  unfold lineIv
  split_ifs with h1 h2 h3 <;> simp_all

end TrackF
end ZetaShell
