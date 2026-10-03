/-
L10_Defs (L7_10, 28 Sep 2026): vocabulary for the Track F nodes Z6a, Z6c, Z6d, Theorem S (thm:shell-S) and the
pointwise assembly AS (eq:shell-assembly) of `rh72/tex/sec_shell.tex`.

Sources of the objects (copied, unchanged, into this folder):
* Farey objects: L7_6's `TF_Defs` (`TrackF.ringMass`, `TrackF.acoefS`, `TrackF.famF`) -- per the lead, L7_6's copy is
  the one used for Farey objects;
* Proposition Z objects: L7_5's `ZDefs`/`ZDefsW` (`pairTerm`, `varpi`, `normCA`, `AvgWeight`, `NearCutoff`, `EerrW`);
* `Zsize` (eq:shell-Zsize) from L7_6's `Z6b_Rectangles`;
* zeros, `primChars`, `twin`, `ZeroDensityInput` from L7_1's `ChallengeShell`.
Namespace `ZetaShell.ShellS`.
-/
import ZetaShell.PropZ.ZDefsW
import ZetaShell.Defs.TF_Defs
import ZetaShell.Farey.Z6b_Rectangles

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- `R₁ = e^{s₀+1}(log Q)⁶/(εQ)` (sec_shell l.673: "fixed on `|s − s₀| ≤ 1`"), as a natural number (floor). -/
def R1S (Q ε s₀ : ℝ) : ℕ := ⌊Real.exp (s₀ + 1) * Real.log Q ^ 6 / (ε * Q)⌋₊

/-- the cutoff of the near exponential sum: `n ≤ e^{s+1}` contains the near window `[Ne^{−κ}, Ne^{κ}]`, `κ ≤ 1`. -/
def Nnear (s : ℝ) : ℕ := ⌊Real.exp (s + 1)⌋₊

open Classical in
/-- `a^{near,P}_n(s) = a_n(s) Ξ((log n − s)/κ)` on primes `n > Q`, `0` otherwise (sec_shell l.175, and l.880:
"`S = S^{near,P}`"). -/
def aNearP (Q T κ : ℝ) (Ξ : ℝ → ℝ) (s : ℝ) (n : ℕ) : ℂ :=
  if n.Prime ∧ Q < (n : ℝ) then TrackF.acoefS T s n * ((Ξ ((Real.log n - s) / κ) : ℝ) : ℂ) else 0

/-- `Ring(s)` (sec_shell l.188) for `S^{near,P}(s)`, with the ring count `R₁ = R1S Q ε s₀`. For the pointwise
assembly at `s` the draft's `R₁ = N(log Q)⁶/(εQ)` is `R1S Q ε (s − 1)`. -/
def RingS (Qn : ℕ) (T κ : ℝ) (Ξ : ℝ → ℝ) (K ε s₀ s : ℝ) : ℝ :=
  TrackF.ringMass Qn (R1S Qn ε s₀) (Nnear s) K (aNearP Qn T κ Ξ s)

/-- the summand of Proposition Z's double zero sum: a VERBATIM copy of L7_5's `ZetaShell.PropZ.pairTerm`
(`lean_work/L7_5/Z/Z5_PropZ.lean` l.17, which lives in a file with a `sorry`; copied so that this vocabulary imports
no `sorry`). Integrator: identify with `PropZ.pairTerm` (`rfl`). -/
def pairTerm {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (T μ s₀ : ℝ) (A k : ℕ)
    (p : {ρ : ℂ // IsNtZero χ ρ} × {ρ : ℂ // IsNtZero χ ρ}) : ℝ :=
  (zmult χ p.1.1 : ℝ) * zmult χ p.2.1 * Real.exp s₀ ^ (p.1.1.re + p.2.1.re - 2)
    * varpi T μ k p.1.1 * varpi T μ k p.2.1 / (1 + |p.1.1.im - p.2.1.im|) ^ A

/-- `μ_r = Δ_r N₀ = K N₀/(rQ)`, `N₀ = e^{s₀}` (sec_shell l.672). -/
def muR (Q K s₀ : ℝ) (r : ℕ) : ℝ := K * Real.exp s₀ / (r * Q)

/-- **the zero-pair sum `𝔷`** of Lemma 6a (lem:shell-6a):
`Σ_{r ≤ R₁} (r/φ(r)) Σ*_{χ mod r} Σ_{ρ,ρ'} m_ρ m_ρ' N₀^{β+β'−2} ϖ_ρ ϖ_ρ' / (1+|γ−γ'|)^A`, with `ϖ` at `μ = μ_r`
(`ζ` is the character mod 1). -/
def zeroPairSum (Q T K ε s₀ : ℝ) (A k : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (R1S Q ε s₀), ((r : ℝ) / (Nat.totient r : ℝ)) *
    ∑ χ ∈ primChars r, (if h : r = 0 then 0 else
      haveI : NeZero r := ⟨h⟩; ∑' p, pairTerm χ T (muR Q K s₀ r) s₀ A k p)

/-- `b_ρ = N₀^{β−1} ϖ_ρ` (sec_shell l.645). -/
def bRho (T μ s₀ : ℝ) (k : ℕ) (ρ : ℂ) : ℝ := Real.exp s₀ ^ (ρ.re - 1) * varpi T μ k ρ

/-- `x_ρ = (1 − β) s₀` (sec_shell l.645). -/
def xRho (s₀ : ℝ) (ρ : ℂ) : ℝ := (1 - ρ.re) * s₀

/-- `Σ_{(χ,ρ) ∈ 𝔛} m_ρ g(μ_r, ρ)` over `𝔛 = {(χ,ρ) : χ primitive mod r ≤ R₁}` (with multiplicity). -/
def famZeroSum (Q K ε s₀ : ℝ) (g : ℝ → ℂ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (R1S Q ε s₀), ∑ χ ∈ primChars r, (if h : r = 0 then 0 else
    haveI : NeZero r := ⟨h⟩;
      ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℝ) * g (muR Q K s₀ r) ρ.1)

/-- every zero sum of `famZeroSum` is a genuine (summable) series, guarding the `tsum` junk value. -/
def famZeroSummable (Q K ε s₀ : ℝ) (g : ℝ → ℂ → ℝ) : Prop :=
  ∀ r ∈ Finset.Icc 1 (R1S Q ε s₀), ∀ χ ∈ primChars r, ∀ h : r ≠ 0,
    haveI : NeZero r := ⟨h⟩;
      Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℝ) * g (muR Q K s₀ r) ρ.1)

open Classical in
/-- the near weight `b` restricted to `x_ρ ≤ X₀`. -/
def gNear (T s₀ : ℝ) (k : ℕ) (X₀ : ℝ) (μ : ℝ) (ρ : ℂ) : ℝ :=
  if xRho s₀ ρ ≤ X₀ then bRho T μ s₀ k ρ else 0

open Classical in
/-- the rest weight `b²` restricted to `x_ρ > X₀`. -/
def gRest (T s₀ : ℝ) (k : ℕ) (X₀ : ℝ) (μ : ℝ) (ρ : ℂ) : ℝ :=
  if X₀ < xRho s₀ ρ then bRho T μ s₀ k ρ ^ 2 else 0

/-- `Σ_{𝔛, x_ρ ≤ X₀} b_ρ` (Lemma 6a, near part). -/
def nearSum (Q T K ε s₀ : ℝ) (k : ℕ) (X₀ : ℝ) : ℝ := famZeroSum Q K ε s₀ (gNear T s₀ k X₀)

/-- `Σ_{𝔛, x_ρ > X₀} b_ρ²` (Lemma 6a, rest part). -/
def restSq (Q T K ε s₀ : ℝ) (k : ℕ) (X₀ : ℝ) : ℝ := famZeroSum Q K ε s₀ (gRest T s₀ k X₀)

/-- `θ(α′)` for (D1′): `min(1, (2−κ′)/κ′)` with `κ′ = c₀(2 − 2/α′) = 4 − 4/α′` (ε″ = 0; eq:shell-etaQ,
thm:shell-S53). The proofs give every `θ < thetaD1p α′` (L7_4 correction 3). -/
def thetaD1p (αp : ℝ) : ℝ := min 1 ((2 - (4 - 4 / αp)) / (4 - 4 / αp))

/-- `κ′ = c₀(2 − 2/α′) + ε″` with `c₀ = 2` (Jutila). -/
def kappaD1p (αp ε'' : ℝ) : ℝ := 2 * (2 - 2 / αp) + ε''

/-- **The parameter range of Theorem S** at level `Q`: `2 ≤ K ≤ (log Q)^B` (the draft's `log K ≪ log log Q`),
`(log Q)^{−B} ≤ ε ≤ 1` (the draft's `ε = 1/ℒ`; see the report: `log(1/ε) = O(log log Q)` is what Lemma 6d's
`𝒵 = N₀^{2−2/α+o(1)}` needs, and it implies L7_5's `ε ≥ Q^{−η/3}`), and `log Q + 3 ≤ s₀ ≤ α′ log Q`. -/
structure SRange (αp B : ℝ) (Qn : ℕ) (K ε s₀ : ℝ) : Prop where
  K_ge : 2 ≤ K
  K_le : K ≤ Real.log Qn ^ B
  eps_ge : Real.log Qn ^ (-B) ≤ ε
  eps_le : ε ≤ 1
  s_ge : Real.log Qn + 3 ≤ s₀
  s_le : s₀ ≤ αp * Real.log Qn

/-- `Σ_{r ≤ R₁} r E′(r, Δ_r)` with `Δ_r = K/(rQ)` (Lemma 5c(2′), L7_5's `family_EW_sum`). -/
def famErrSum (Q T K ε s₀ : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (R1S Q ε s₀), (r : ℝ) * EerrW T (Real.exp s₀) r (K / (r * Q))

/-- `ℒ = log(QT/2π)`. -/
def LcS (Q T : ℝ) : ℝ := Real.log (Q * T / (2 * Real.pi))

/-- the shell width of record `K = ℒ(log ℒ)²` (ssec:shell-rate). -/
def Kstd (Q T : ℝ) : ℝ := LcS Q T * Real.log (LcS Q T) ^ 2

/-- `X = e^{λℒ}`. -/
def XlamS (lam Q T : ℝ) : ℝ := Real.exp (lam * LcS Q T)

/-- `|𝔉_Q| = Σ_{1<q≤Q} #{χ primitive mod q}` (sec_shell l.37). -/
def famSize (Qn : ℕ) : ℝ := ∑ q ∈ Finset.Icc 2 Qn, ((primChars q).card : ℝ)

/-- `‖a‖² = Σ_{0<n≤N} |a_n|²` for the coefficients `a_n(s)`. -/
def l2S (N : ℕ) (T s : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 N, ‖TrackF.acoefS T s n‖ ^ 2

lemma normCA_nonneg' (W : ℝ → ℝ) (A : ℕ) : 0 ≤ normCA W A :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => abs_nonneg _

end ShellS
end ZetaShell
