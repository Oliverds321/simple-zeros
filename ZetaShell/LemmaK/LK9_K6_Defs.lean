/-
L7_9 round 2: objects of the proof of Lemma K.6 (lem:K-P, `tex/sec_lemmaK.tex`), for the four sub-nodes of
`principal_arc_mass`.
* `rho6`: the cutoff `ϱ` (`1` on `|u| ≤ 1/2`, `0` on `|u| ≥ 1`, linear between; Lipschitz with constant 2,
  replacing the draft's `C^∞` cutoff with `|ϱ′| ≤ 3`).
* `wmod T s n = w̃(n) = −(2π)⁻¹ n^{−1/2} D_T(s − log n) ϱ(log n − s)`: the smooth model (weight 1 on every `n`).
* `asmooth T s R n = ϱ(log n − s)·a′_n = Λ′(n) w̃(n)` (`a′ = aPrime`, `Λ′ = Λ·1{p > R}`).
* `blockSum N c h x = C(x) = Σ_{x < n ≤ x + h, 0 < n ≤ N} c_n` (Gallagher's `L²` lemma, Step 2; not used after
  round 2's switch to summation by parts).
* `psum n c = Σ_{0 < m ≤ n} c_m` (Step 2′, summation by parts).
-/
import ZetaShell.Defs.LK_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK
namespace K6

/-- the cutoff `ϱ(u) = max(0, min(1, 2 − 2|u|))`. -/
def rho6 (u : ℝ) : ℝ := max 0 (min 1 (2 - 2 * |u|))

/-- the smooth model coefficients `w̃(n)`. -/
def wmod (T s : ℝ) (n : ℕ) : ℂ :=
  -(((2 * Real.pi)⁻¹ * ((n : ℝ) ^ (-(1 / 2 : ℝ))) * rho6 (Real.log n - s) : ℝ) : ℂ) *
    DT T (s - Real.log n)

/-- the smoothed prime coefficients `Λ′(n) w̃(n) = ϱ(log n − s) a′_n`. -/
def asmooth (T s R : ℝ) (n : ℕ) : ℂ := ((rho6 (Real.log n - s) : ℝ) : ℂ) * aPrime T s R n

open Classical in
/-- the block sum `C(x) = Σ_{x < n ≤ x + h, 0 < n ≤ N} c_n`. -/
def blockSum (N : ℕ) (c : ℕ → ℂ) (h x : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), c n

/-- the partial sums `C₀(n) = Σ_{0 < m ≤ n} c_m` (discrete summation by parts, Step 2′). -/
def psum (n : ℕ) (c : ℕ → ℂ) : ℂ := ∑ m ∈ Finset.Ioc 0 n, c m

end K6
end LemmaK
end ZetaShell
