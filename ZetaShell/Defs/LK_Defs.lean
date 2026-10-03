/-
lean_work/L7_3/skeleton/LK_Defs.lean — interfaces for LEMMA K (the killed kernel) and THEOREM 1′ of the family paper,
agent L7_3, 28 Sep 2026. Namespace `ZetaShell.LemmaK`. Intended home: `ZetaShell/LemmaK/Defs.lean`.

Source: `rh72/tex/sec_lemmaK.tex` (lem:K, lem:K-farey, lem:K-G, lem:K-Z, lem:K-R, lem:K-S, lem:K-P, eq:BK,
thm:one-prime, tab:K-profiles). Built on ZetaQ's objects only (trunk; no L7_1 module is imported, so this file
has no dependency on unintegrated work).

Contents
  §1 the killed kernel `k_C(α) = min(|α|,1)·…` in the draft's form (eq:BK): `killedKernel C α = |α|` on `|α| ≤ 1`,
     `= C` on `|α| > 1`; the functional `BK C v = ψ(0) + ∫ k_C ψ` against ZetaQ's `Payoff.psi`; `K1kill v = ∫_{|α|>1} ψ`.
  §2 `KProfile` (λ, C⁺, even polynomial `p(t) = Σ cᵢ t^{2i}`), `v_p = p²/∫p²`, the artifact's side conditions
     (`p` decreasing, `1/6 ≤ p ≤ 1`, `a ≥ 3/4`, `b ≥ 1/2`), and the certificate Prop `KCert S Pc`.
     Data: `profDesignQle` = ZetaQ's own design profile `designProfileQle` at `λ* = 1.2507321515` (killed value
     0.7235110849…, exact), and `profLamStar8`, a degree-8 profile at the SAME `λ*` (killed value 0.7237495018…,
     exact; L7_3 numerics `incap_opt.out`). Constants: `PcertKD = 0.7235`, `PcertK = 0.7237` (the draft's `P_K`).
  §3 `KFrame F r ε S κ rate` — what ZetaQ's Proposition 3.1 consumes (display H1 and the five rows of
     `Margin.assembly_at_lamStar_provedM`'s bundle), along a design at the profile `S`, with the Frobenius row at `κ`.
     Mirror of L7_1's `ShellFrame` (lean_work/L7_1/ShellInterfaces.lean §2), without the Shell profile type.
     `rateLL Q = log log Q / log Q`, the rate of ZetaQ's headlines.
  §4 the objects of Lemma K's proof: `distZ` (‖·‖ to ℤ), the weighted Farey density `Ddens` (lem:K-G), the
     Dirichlet-polynomial coefficients `acoef T s n = −(2π)⁻¹ Λ(n) n^{−1/2} D_T(s − log n)` with
     `D_T(v) = ∫_T^{2T} e^{iτv} dτ`, the scales `Lc`, `ellK`, `Xlam`, `R0`, and the prime-power split `aPrime`.
-/
import ZetaQ.Margin
import ZetaQ.HFrob

noncomputable section
open scoped BigOperators
open Filter MeasureTheory

namespace ZetaShell
namespace LemmaK

/-! ## §1 The killed kernel and its functional (eq:BK) -/

/-- The killed kernel of eq:BK: `|α|` on `|α| ≤ 1` (in-zone and zone edge), `C` on `|α| > 1` (out-zone, Lemma K (ii):
`u ↦ min(u, ℒ)` in `s`-units). Against ZetaQ's `Payoff.W C α = C|α|` on `|α| > 1`. -/
def killedKernel (C α : ℝ) : ℝ := if |α| ≤ 1 then |α| else C

/-- `B^K_C(v) = ψ(0) + ∫_{|α|≤1}|α|ψ + C∫_{|α|>1}ψ` (eq:BK; `ψ = v⋆v` vanishes beyond `λ`). -/
def BK (C : ℝ) (v : ℝ → ℝ) : ℝ := ZetaQ.Payoff.psi v 0 + ∫ α, killedKernel C α * ZetaQ.Payoff.psi v α

/-- the killed out-zone moment `∫_{|α|>1} ψ` (ZetaQ's `K1 v = ∫_{|α|>1}|α|ψ` with the weight `|α|` removed). -/
def K1kill (v : ℝ → ℝ) : ℝ := ∫ α in {α : ℝ | 1 < |α|}, ZetaQ.Payoff.psi v α

/-! ## §2 Profiles and the certificate (ssec:K-constants, tab:K-profiles) -/

/-- A killed-kernel profile: bandwidth `λ`, the rational upper bound `C⁺` for the family constant, and the even
polynomial `p(t) = Σᵢ cᵢ t^{2i}` (coefficients of `t^0, t^2, t^4, …`, as in tab:K-profiles). -/
structure KProfile where
  lam : ℚ
  Cplus : ℚ
  c : List ℚ

namespace KProfile
variable (S : KProfile)

/-- `p(t) = Σᵢ cᵢ t^{2i}`, by Horner in `t²` (ZetaQ's `Payoff.evalPoly`, whose soundness lemmas then apply). -/
def p (t : ℝ) : ℝ := ZetaQ.Payoff.evalPoly S.c (t ^ 2)

def mass : ℝ := ∫ t in (-((S.lam : ℝ) / 2))..((S.lam : ℝ) / 2), S.p t ^ 2

/-- `v_p = p²/∫p²` on `[−λ/2, λ/2]`, zero outside. -/
def v (t : ℝ) : ℝ := if |t| ≤ (S.lam : ℝ) / 2 then S.p t ^ 2 / S.mass else 0

/-- The side conditions of the formal artifact (ssec:K-constants: "`a ≥ 3/4`, `b ≥ 1/2`, `1/6 ≤ p ≤ 1`",
`p` even and decreasing on `[0, λ/2]`). -/
structure Side : Prop where
  pos : ∀ t, |t| ≤ (S.lam : ℝ) / 2 → 0 < S.p t
  le_one : ∀ t, |t| ≤ (S.lam : ℝ) / 2 → S.p t ≤ 1
  anti : StrictAntiOn S.p (Set.Icc 0 ((S.lam : ℝ) / 2))
  a_ge : (3 : ℝ) / 4 ≤ S.mass / (S.lam : ℝ)
  b_ge : (1 : ℝ) / 2 ≤ (∫ t in (-((S.lam : ℝ) / 2))..((S.lam : ℝ) / 2), S.p t ^ 4) / (S.lam : ℝ)
  end_ge : (1 : ℝ) / 6 ≤ S.p ((S.lam : ℝ) / 2)

end KProfile

/-- **The killed-kernel certificate** (ssec:K-constants): `1 < λ < 2`, `π⁴/18 ≤ C⁺`, `v_p` admissible, the side
conditions, and `B^K_{C⁺}(v_p) ≤ 2 − P_c` for the real-valued Mathlib functional. -/
def KCert (S : KProfile) (Pc : ℚ) : Prop :=
  1 < (S.lam : ℝ) ∧ (S.lam : ℝ) < 2 ∧ ZetaQ.Cfam ≤ (S.Cplus : ℝ) ∧ ZetaQ.Payoff.Admissible S.lam S.v ∧ S.Side ∧
    BK S.Cplus S.v ≤ 2 - (Pc : ℝ)

/-- `λ* = 1.2507321515` as an exact rational (ZetaQ's `lamStar`, the design bandwidth of `Family.qle`). -/
def lamStarQ : ℚ := 2501464303 / 2000000000

/-- ZetaQ's own design profile `designProfileQle` (DesignProfile.lean) at `λ*`: killed value
`2 − B^K_{C⁺}(v_p) = 0.7235110849…` (exact rational, L7_3 `numerics/kconst.out`), against 0.7212536292 for
ZetaQ's kernel `C|α|`. -/
def profDesignQle : KProfile where
  lam := lamStarQ
  Cplus := 541161617 / 100000000
  c := [1, -81257 / 125000, 3458583 / 1000000, -3669851 / 200000]

/-- A degree-8 killed-kernel profile at the SAME `λ* = 1.2507321515` (L7_3 `numerics/incap_opt.out`):
`2 − B^K_{C⁺}(v_p) = 0.7237495018…` exact, `a = 0.7860`, `b = 0.6831`, `p(λ/2) = 0.2756`, decreasing (Sturm).
It certifies the draft's `P_K = 0.7237` (thm:one-prime) INSIDE ZetaQ's bandwidth pin `P.lam = lamStar`. -/
def profLamStar8 : KProfile where
  lam := lamStarQ
  Cplus := 541161617 / 100000000
  c := [1, -204581936 / 297214369, 2511259929 / 554894287, -16394872054 / 595414977, 14897653256 / 697578907]

/-- the constant of the design-profile route (no new design data): `0.7235`. -/
def PcertKD : ℚ := 7235 / 10000

/-- the draft's constant `P_K = 0.7237` of Theorem 1′ (thm:one-prime). -/
def PcertK : ℚ := 7237 / 10000

/-- the rate of ZetaQ's headlines, `log log Q / log Q`. -/
def rateLL (Qn : ℕ) : ℝ := Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)

/-! ## §3 The frame (what Proposition 3.1 consumes) -/

/-- **`KFrame F r ε S κ rate`**: a design `Des Q P` along `Q → ∞` at `T = (log Q)^{r+ε}`, bandwidth `S.lam` and profile
`S.p`, carrying the display (H1) and the five rows of `ZetaQ.Margin.assembly_at_lamStar_provedM`'s bundle, the
Frobenius row at `κ` (for Theorem 1′: `κ = 2 − P_c`, `P_c` certified by `KCert S P_c`), and Proposition 3.1's
bracket `4r₁ + r₂ + 3r₃ + 4r₄ + 2r₅√(κ + r₂) + r₅² ≤ c·rate` — the BRACKET form, which is what ZetaQ's
assembly delivers (`budgetTotalProved = O(log log Q/log Q)`), weaker than bounding each row by `c·rate`
(L7_1's `ShellFrame` has the row form; it implies this one). Only the Frobenius row differs from ZetaQ's
(Lemma K (ii) in place of Lemma 6.1 in the out-zone of Lemma 4.3; thm:one-prime's proof). -/
structure KFrame (F : ZetaQ.Family) (r ε : ℝ) (S : KProfile) (κ : ℝ) (rate : ℕ → ℝ) where
  Des : ℝ → ZetaQ.ParamsQ → Prop
  exists_design : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∃ P : ZetaQ.ParamsQ, Des Q P
  T_eq : ∀ Q P, Des Q P → P.T = ZetaQ.Twin Q r ε
  Q_eq : ∀ Q P, Des Q P → P.Q = Q
  lam_eq : ∀ Q P, Des Q P → P.lam = (S.lam : ℝ)
  valid : ∀ Q P, Des Q P → P.Valid
  prof_eq : ∀ Q P, Des Q P → ∀ t : ℝ, P.prof.eval t = S.p t
  rows : ∃ c : ℝ, 0 < c ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ZetaQ.ParamsQ, Des (Qn : ℝ) P →
    ∃ r₁ r₂ r₃ r₄ r₅ θ₀ : ℝ, 0 ≤ θ₀ ∧ 0 ≤ ZetaQ.Btr P F Qn θ₀ ∧ 0 ≤ ZetaQ.BF P F Qn θ₀ ∧ 0 ≤ κ + r₂ ∧
      ZetaQ.CertificateDisplay (ZetaQ.N0sFamQ P F Qn) (ZetaQ.NfamQ P F Qn) (ZetaQ.NIIFamQ P F Qn)
        (ZetaQ.trGhatFam P F Qn) (ZetaQ.frobSqGhatFam P F Qn) (ZetaQ.Btr P F Qn θ₀) (ZetaQ.BF P F Qn θ₀) ∧
      (1 - r₁) * ZetaQ.NfamQ P F Qn ≤ ZetaQ.trGhatFam P F Qn ∧
      ZetaQ.frobSqGhatFam P F Qn ≤ (κ + r₂) * ZetaQ.NfamQ P F Qn ∧
      ZetaQ.NIIFamQ P F Qn ≤ r₃ * ZetaQ.NfamQ P F Qn ∧
      ZetaQ.Btr P F Qn θ₀ ≤ r₄ * ZetaQ.NfamQ P F Qn ∧
      ZetaQ.BF P F Qn θ₀ ≤ r₅ * Real.sqrt (ZetaQ.NfamQ P F Qn) ∧
      4 * r₁ + r₂ + 3 * r₃ + 4 * r₄ + 2 * r₅ * Real.sqrt (κ + r₂) + r₅ ^ 2 ≤ c * rate Qn

/-! ## §4 The objects of Lemma K's proof -/

/-- `‖x‖`, the distance from `x` to the nearest integer. -/
def distZ (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

/-- the weighted local density of lem:K-G: `D_δ(θ) = δ⁻¹ Σ_{‖ξᵢ − θ‖ ≤ δ/2} wᵢ`. -/
def Ddens {ι : Type} (s : Finset ι) (ξ w : ι → ℝ) (δ θ : ℝ) : ℝ :=
  δ⁻¹ * ∑ i ∈ s, (if distZ (ξ i - θ) ≤ δ / 2 then w i else 0)

/-- `D_T(v) = ∫_T^{2T} e^{iτv} dτ` (so `|D_T| ≤ min(T, 2/|v|)`, `‖D_T‖₂² = 2πT`). -/
def DT (T v : ℝ) : ℂ := ∫ τ in T..(2 * T), Complex.exp (Complex.I * (τ : ℂ) * (v : ℂ))

/-- the coefficients of Lemma K's standing notation: `a_n(s) = −(2π)⁻¹ Λ(n) n^{−1/2} D_T(s − log n)`. -/
def acoef (T s : ℝ) (n : ℕ) : ℂ :=
  -((2 * Real.pi)⁻¹ * ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) *
    DT T (s - Real.log n)

/-- `ℒ = log(QT/2π)`. -/
def Lc (Q T : ℝ) : ℝ := Real.log (Q * T / (2 * Real.pi))

/-- `ℓ_K = log(QTK)` with `K = ℒ`. -/
def ellK (Q T : ℝ) : ℝ := Real.log (Q * T * Lc Q T)

/-- `𝒳 = e^{λℒ}`. -/
def Xlam (lam Q T : ℝ) : ℝ := Real.exp (lam * Lc Q T)

/-- `R₀ = N/(QTK)`, `N = e^s`. -/
def R0 (Q T s : ℝ) : ℝ := Real.exp s / (Q * T * Lc Q T)

open Classical in
/-- `a′_n = a_n·1{n = p^k, p > R₀}` (lem:K-S). -/
def aPrime (T s R : ℝ) (n : ℕ) : ℂ := if IsPrimePow n ∧ R < (n.minFac : ℝ) then acoef T s n else 0

end LemmaK
end ZetaShell
