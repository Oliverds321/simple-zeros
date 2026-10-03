/-
TF_Defs (L7_6, 28 Sep 2026): shared objects for the Track F statement drafts A⋆ (lem:shell-star), AF1
(lem:shell-F1), A3 (lem:shell-3) and A1′ (lem:shell-1prime) of `rh72/tex/sec_shell.tex` §2–§3.

Built on ZetaQ's objects only (trunk, no unintegrated module):
* `ZetaQ.expSum N a θ = Σ_{0<n≤N} a_n e(nθ)`, `ZetaQ.charSum q N a χ = Σ_{0<n≤N} a_n χ(n)`,
  `ZetaQ.l2sq N a = Σ_{0<n≤N} |a_n|²`, `ZetaQ.reducedResidues q = {0 ≤ b < q, (b,q) = 1}`,
  `ZetaQ.primitiveChars q`, `ZetaQ.e x = exp(2πix)`, `ZetaQ.Gallagher.gallagherBudget N Q = Q² + πN`.
* `distZ`, `Ddens`, `DTk`, `acoefS` are verbatim copies of L7_3's `LemmaK.distZ`, `LemmaK.Ddens`, `LemmaK.DT`,
  `LemmaK.acoef` (`lean_work/L7_3/skeleton/LK_Defs.lean` §4). **Integrator: unify them with L7_3's copies.**
Intended home: `ZetaShell/Skeleton/TF_Defs.lean` (or merge into `ZetaShell/LemmaK/Defs.lean`).
-/
import ZetaQ.Gallagher

noncomputable section

namespace ZetaShell
namespace TrackF

/-- `‖x‖`, the distance from `x` to the nearest integer (= L7_3 `LemmaK.distZ`). -/
def distZ (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

/-- the weighted local density `D^𝒲_δ(θ) = δ⁻¹ Σ_{‖ξᵢ − θ‖ ≤ δ/2} 𝒲ᵢ` (distance on `ℝ/ℤ`; = L7_3 `LemmaK.Ddens`). -/
def Ddens {ι : Type} (s : Finset ι) (ξ w : ι → ℝ) (δ θ : ℝ) : ℝ :=
  δ⁻¹ * ∑ i ∈ s, (if distZ (ξ i - θ) ≤ δ / 2 then w i else 0)

/-- the Farey index set `{(d, b) : 1 ≤ d ≤ Q, 0 ≤ b < d, (b, d) = 1}` of `𝔉_Q` (sec_shell l.171–172). -/
def fareyIdx (Q : ℕ) : Finset ((_ : ℕ) × ℕ) := (Finset.Icc 1 Q).sigma ZetaQ.reducedResidues

/-- the Farey point `b/d` of an index `(d, b)`. -/
def fareyPt (x : (_ : ℕ) × ℕ) : ℝ := (x.2 : ℝ) / (x.1 : ℝ)

/-- the twisted sum `S_χ(β) = Σ_{0<n≤N} a_n χ(n) e(nβ)` (lem:shell-4). -/
def twistSum (N : ℕ) (a : ℕ → ℂ) {r : ℕ} (χ : DirichletCharacter ℂ r) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, a n * χ (n : ZMod r) * ZetaQ.e ((n : ℝ) * β)

/-- the ring of modulus `r`: `1/(rQ) ≤ |β| < K/(rQ)` (sec_shell l.184–185). -/
def ringSet (Q : ℕ) (K : ℝ) (r : ℕ) : Set ℝ :=
  {β : ℝ | 1 / ((r : ℝ) * Q) ≤ |β| ∧ |β| < K / ((r : ℝ) * Q)}

/-- `Ring(s) = Σ_{r ≤ R₁} Σ*_{a mod r} ∫_{ring} |S(a/r + β)|² dβ` (sec_shell l.188), for the coefficients `a`
(the draft applies it to `a^near`). -/
def ringMass (Q R1 N : ℕ) (K : ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R1, ∑ b ∈ ZetaQ.reducedResidues r,
    ∫ β in ringSet Q K r, ‖ZetaQ.expSum N a ((b : ℝ) / r + β)‖ ^ 2

/-- the family functional `F = Σ_{q ∈ M} Σ*_{χ mod q} |Σ_n a_n χ(n)|²` over a set of moduli `M`
(eq:shell-Fbold at fixed `s`; `M = Icc 2 Q` is `𝔉_Q`). -/
def famF (M : Finset ℕ) (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ q ∈ M, ∑ χ ∈ ZetaQ.primitiveChars q, ‖ZetaQ.charSum q N a χ‖ ^ 2

/-- `D_T(v) = ∫_T^{2T} e^{iτv} dτ` (= L7_3 `LemmaK.DT`). -/
def DTk (T v : ℝ) : ℂ := ∫ τ in T..(2 * T), Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ))

/-- `a_n(s) = −(2π)⁻¹ Λ(n) n^{−1/2} D_T(s − log n)` (sec_shell l.45; = L7_3 `LemmaK.acoef`). -/
def acoefS (T s : ℝ) (n : ℕ) : ℂ :=
  -((2 * Real.pi)⁻¹ * ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) *
    DTk T (s - Real.log n)

end TrackF
end ZetaShell
