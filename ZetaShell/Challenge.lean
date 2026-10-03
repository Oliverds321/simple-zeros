/-
lean_work/L7_1/ChallengeShell.lean — the MATHLIB-ONLY statement layer of the FAMILY follow-up (L7_1, 28 Sep 2026).
Intended home: `comparator/Challenge/FollowUpFamily.lean` (LEAN_PLAN §2). It imports only Mathlib, so a reader
auditing WHAT is claimed about the family paper reads this file only.

Source: `rh72/tex/sec_shell.tex` (thm:shell-S53, thm:shell-1pp, thm:shell-K, def:shell-kernel, ssec:shell-density,
rem:shell-S53-inputs, ssec:shell-cert, ssec:shell-cert-53) and `rh72/tex/sec_bounded.tex` (thm:bh-S).

Contents
  §1 primitive characters, nontrivial zeros of `DirichletCharacter.LFunction`, multiplicity, the window counts
     `famN`, `famN0s` (same shapes as `Zeta23.ThmE.NcountL` / `N0simpleL`, which `ZetaQ.NfamCount` wraps);
  §2 the rectangle count `Nstar Q σ T = Σ_{q≤Q} Σ*_χ N(σ,T,χ)` (ζ = the character mod 1 INCLUDED) and the
     named analytic hypothesis `ZeroDensityInput` := Jutila 1977 Thm 1 (1.8) ∧ Montgomery's hybrid estimate
     (Bombieri, Astérisque 18, §10 Théorème 20), stated in the SOURCES' form (no strengthening; see the docstrings);
  §3 the Shell kernel (def:shell-kernel), the functional `Bshell` (eq:shell-B), the profile data of
     ssec:shell-cert-53 and the certificate Props `CertS53`, `CertD53` (Track R);
  §4 the headline statements, LEAN_PLAN level C (displayed hypotheses `ZeroDensityInput`, `PNTErrorTerm` and the
     certificate),
     `sorry` proofs (challenge side).
-/
import Mathlib

noncomputable section
open scoped BigOperators
open Complex

namespace ZetaShell

/-! ## §1 Primitive characters, zeros, window counts -/

open DirichletCharacter in
/-- `Σ*_{χ mod q}`: the primitive Dirichlet characters mod `q` (character-identical to `ZetaQ.primitiveChars`). -/
def primChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  Finset.univ.filter (fun χ => χ.IsPrimitive)

section zeros
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- `ρ` is a nontrivial zero of `L(s,χ)` (same as `Zeta23.ThmE.IsNontrivialZeroL`). -/
def IsNtZero (ρ : ℂ) : Prop := χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- `m_ρ`: order of vanishing of `L(·,χ)` at `ρ` (same as `Zeta23.ThmE.zeroMultL`). -/
def zmult (ρ : ℂ) : ℕ := (analyticOrderAt χ.LFunction ρ).toNat

/-- nontrivial zeros with `T₁ < γ ≤ T₂`. -/
def zerosWin (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNtZero χ ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- `N_χ(T₁,T₂)`, with multiplicity. -/
def Nwin (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosWin χ T₁ T₂, zmult χ ρ

/-- `N^s_{0,χ}(T₁,T₂)`: simple zeros on the critical line. -/
def N0sWin (T₁ T₂ : ℝ) : ℕ :=
  (zerosWin χ T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zmult χ ρ = 1}).ncard

/-- zeros in Jutila's / Bombieri's closed rectangle `σ ≤ β ≤ 1, |γ| ≤ T` (all zeros there are nontrivial
for `σ > 0`). -/
def zerosRect (σ T : ℝ) : Set ℂ := {ρ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T}

/-- `N(σ,T,χ)`, with multiplicity. -/
def NrectC (σ T : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosRect χ σ T, zmult χ ρ

end zeros

/-- `N_χ(T₁,T₂)` as a real, with the (never used) guard `q = 0` (as `ZetaQ.NcountQ`). -/
def Nchi (q : ℕ) (χ : DirichletCharacter ℂ q) (T₁ T₂ : ℝ) : ℝ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩; ((Nwin χ T₁ T₂ : ℕ) : ℝ)

/-- `N^s_{0,χ}(T₁,T₂)` as a real (as `ZetaQ.N0sQ`). -/
def N0schi (q : ℕ) (χ : DirichletCharacter ℂ q) (T₁ T₂ : ℝ) : ℝ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩; ((N0sWin χ T₁ T₂ : ℕ) : ℝ)

/-- `N(σ,T,χ)` as a real. -/
def Nrect (q : ℕ) (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℝ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩; ((NrectC χ σ T : ℕ) : ℝ)

/-- The moduli of the family `𝔉_Q` of sec_shell.tex l.37: `1 < q ≤ Q` (as `ZetaQ.Family.moduli Family.qle`). -/
def modQle (Q : ℕ) : Finset ℕ := Finset.Icc 2 Q

/-- The dyadic family's moduli `Q/2 < q ≤ Q` (as `ZetaQ.Family.moduli Family.dyadic`). -/
def modDyadic (Q : ℕ) : Finset ℕ := Finset.Ioc (Q / 2) Q

/-- `𝒩 = Σ_{q∈M} Σ*_χ N_χ(T₁,T₂)`. -/
def famN (M : Finset ℕ) (T₁ T₂ : ℝ) : ℝ := ∑ q ∈ M, ∑ χ ∈ primChars q, Nchi q χ T₁ T₂

/-- `Σ_{q∈M} Σ*_χ N^s_{0,χ}(T₁,T₂)`. -/
def famN0s (M : Finset ℕ) (T₁ T₂ : ℝ) : ℝ := ∑ q ∈ M, ∑ χ ∈ primChars q, N0schi q χ T₁ T₂

/-- The window height of the paper's Theorem 1: `T = (log Q)^{r+ε}` (as `ZetaQ.Twin`). -/
def twin (Q r ε : ℝ) : ℝ := Real.log Q ^ (r + ε)

/-! ## §2 The zero-density input (trust level C: the one named analytic hypothesis) -/

/-- `N*(σ,T,Q) = Σ_{q ≤ Q} Σ*_{χ mod q} N(σ,T,χ)`, over PRIMITIVE characters, `q = 1` (i.e. `ζ`) INCLUDED
(sec_shell.tex l.742–744: "In every source below the count is over primitive characters, in the closed rectangle
`β ≥ σ, |γ| ≤ T`, and the character mod 1 (that is, ζ) is included"). -/
def Nstar (Q : ℕ) (σ T : ℝ) : ℝ := ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primChars q, Nrect q χ σ T

/-- **Jutila 1977, Theorem 1, (1.8)** [Math. Scand. 41 (1977), p. 46], as quoted in rem:shell-S53-inputs (a)
(sec_shell.tex l.791–796): "For `4/5 ≤ α ≤ 1`, `T ≥ 1`, we have … (1.8) `N*(α,T,Q) ≪_ε (Q²T)^{(2+ε)(1−α)}`",
"the constants implied by Vinogradov's symbol `≪` depend on `ε`"; no factor of `log`; no relation between `T` and `Q`.
Used as (LF) of (D1′) with `h_LF = 1`, `c₀ = 2`, `σ_LF = 4/5` (sec_shell.tex l.757).
Range of `Q`: `Q ≥ 1` (the sum over `q ≤ Q` is empty-free from `Q = 1`; TZ22 quote it for `Q ≥ 3`, which is
equivalent up to the constant since `N*` is monotone in `Q`). -/
def JutilaHybrid : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T → ∀ α : ℝ, 4 / 5 ≤ α → α ≤ 1 →
    Nstar Q α T ≤ C * ((Q : ℝ) ^ 2 * T) ^ ((2 + ε) * (1 - α))

/-- **Montgomery's hybrid estimate, in the form of Bombieri, Astérisque 18, §10, Théorème 20** (p. 77), as quoted in
rem:shell-S53-inputs (b) (sec_shell.tex l.802–807): for `T ≥ 2`, `1/2 ≤ α ≤ 1`,
"`Σ_{q≤Q} Σ*_{χ mod q} N(α,T;χ) ≪ (TQ²)^{3(1−α)/(2−α)} (log TQ)^A`", absolute implied constant.
The power `A` is EXISTENTIAL here.
(B) consumes only a finite `b₀`. So this Prop is implied by the printed statement for every admissible `A`, i.e.
it does NOT strengthen the source. -/
def MontgomeryHybrid : Prop :=
  ∃ A C : ℝ, ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 2 ≤ T → ∀ α : ℝ, 1 / 2 ≤ α → α ≤ 1 →
    Nstar Q α T ≤ C * ((T * (Q : ℝ) ^ 2) ^ (3 * (1 - α) / (2 - α)) * Real.log (T * Q) ^ A)

/-- **`ZeroDensityInput`** (LEAN_PLAN §1.4): instantiation (D1′) of sec_shell.tex l.756–762 — "Montgomery bulk +
Jutila hybrid (all inputs primary, [V])" — which gives `A* = M = 5/2` and `α₀ = 5/3` (thm:shell-S53).
Both fields are classical unconditional theorems (Track D would prove them); here they are hypotheses. -/
structure ZeroDensityInput : Prop where
  jutila : JutilaHybrid
  montgomery : MontgomeryHybrid

/-- **The prime number theorem with de la Vallée Poussin's error term** (sec_lemmaK.tex eq:PNT, l.46–54):
`|ψ(y) − y| ≤ c₁ y exp(−c₂ √(log y))` for `y ≥ 2` (FKS give `c₂ < 0.8476836` explicitly; any `c₂ > 0` is used).
NOT a density estimate, but a second classical input of the Shell chain: Lemma 4 (lem:shell-4, the hole bound, via
lem:K-P Step 3, "Gallagher's lemma with the PNT error term") and `‖a(s)‖² = U(s + O(1))` (ssec:shell-farey) use it in
short intervals `[N e^{−1/T}, N e^{1/T}]`, `T` a power of `log Q`. Mathlib has Chebyshev's `ψ` but not the PNT
(rem:K-lean item 6: "a new cited input unless the strong form of the PrimeNumberTheoremAnd project is imported").
Proposed as a SECOND displayed hypothesis (report, open question 1). -/
def PNTErrorTerm : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₂ ∧ ∀ y : ℝ, 2 ≤ y →
    |Chebyshev.psi y - y| ≤ c₁ * y * Real.exp (-(c₂ * Real.sqrt (Real.log y)))

/-! ## §3 The Shell kernel, the functional, the certified profiles -/

/-- `ψ = v ⋆ v` read as the autocorrelation `ψ(α) = ∫ v(t) v(t−α) dt` (character-identical to
`ZetaQ.Payoff.psi`; for even `v` it is the convolution). -/
def psiS (v : ℝ → ℝ) (α : ℝ) : ℝ := ∫ t, v t * v (t - α)

/-- **The Shell kernel** (def:shell-kernel, sec_shell.tex l.56–59, in the normalisation of ssec:shell-cert
"Kernel and constants", l.1016–1018): `|α|` on `|α| ≤ 1`, the level `ℓ` on `1 < |α| ≤ α′`, the constant `C` on
`α′ < |α|` (only `|α| ≤ λ` is ever read, since `supp ψ ⊆ [−λ, λ]`). `ℓ = 1` for the full families. -/
def shellKernel (ℓ αp C : ℝ) (α : ℝ) : ℝ :=
  if |α| ≤ 1 then |α| else if |α| ≤ αp then ℓ else C

/-- **`B_{α′}(v) = ψ(0) + ∫ k_{α′}(α) ψ(α) dα`** (eq:shell-B with `k = k_{α′}`, def:shell-kernel). -/
def Bshell (ℓ αp C : ℝ) (v : ℝ → ℝ) : ℝ := psiS v 0 + ∫ α, shellKernel ℓ αp C α * psiS v α

/-- Admissible profiles (paper §11; field-identical to `ZetaQ.Payoff.Admissible`). -/
structure AdmissibleS (lam : ℝ) (v : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ v t
  integrable : MeasureTheory.Integrable v
  mass : ∫ t, v t = 1
  supp : ∀ t, v t ≠ 0 → |t| ≤ lam / 2

/-- A certified profile of ssec:shell-cert "Method" (l.1025–1036): rationals `1 < λ < 2`, `α′`, the level `ℓ`, the
rational upper bound `C⁺` of the family constant, and `d = (d₀ = 1, d₁, …)` with `p(t) = Σ_i d_i (2t/λ)^{2i}`. -/
structure ShellProfile where
  lam : ℚ
  alphaP : ℚ
  level : ℚ
  Cplus : ℚ
  d : List ℚ

namespace ShellProfile
variable (S : ShellProfile)

/-- `p(t) = Σ_i d_i (2t/λ)^{2i}`. -/
def p (t : ℝ) : ℝ := ∑ i : Fin S.d.length, ((S.d.get i : ℚ) : ℝ) * (2 * t / (S.lam : ℝ)) ^ (2 * (i : ℕ))

/-- `∫_{−λ/2}^{λ/2} p²`. -/
def mass : ℝ := ∫ t in (-((S.lam : ℝ) / 2))..((S.lam : ℝ) / 2), S.p t ^ 2

/-- `v_p = p² / ∫p²` on `[−λ/2, λ/2]`, `0` outside. -/
def v (t : ℝ) : ℝ := if |t| ≤ (S.lam : ℝ) / 2 then S.p t ^ 2 / S.mass else 0

/-- **The Lean side conditions "L75"** (ssec:shell-cert "Lean side conditions", l.1080–1082: `p` decreasing,
`a ≥ 3/4` (`Valid.a_ge`), `b ≥ 1/2` (H5), `p(λ/2) ≥ 1/6`), with `0 < p ≤ 1` of "Method" (l.1033–1034);
`a = ⟨p²⟩ = λ⁻¹∫p²`, `b = ⟨p⁴⟩ = λ⁻¹∫p⁴` as in `check_profile.py`. -/
structure L75 : Prop where
  pos : ∀ t, |t| ≤ (S.lam : ℝ) / 2 → 0 < S.p t
  le_one : ∀ t, |t| ≤ (S.lam : ℝ) / 2 → S.p t ≤ 1
  anti : StrictAntiOn S.p (Set.Icc 0 ((S.lam : ℝ) / 2))
  a_ge : (3 : ℝ) / 4 ≤ S.mass / (S.lam : ℝ)
  b_ge : (1 : ℝ) / 2 ≤ (∫ t in (-((S.lam : ℝ) / 2))..((S.lam : ℝ) / 2), S.p t ^ 4) / (S.lam : ℝ)
  end_ge : (1 : ℝ) / 6 ≤ S.p ((S.lam : ℝ) / 2)

end ShellProfile

/-- **The certificate Prop (Track R)**: the profile is admissible at `λ`, meets L75, `1 < α′`, `1 < λ < 2`, and
`B_{α′}(v_p) ≤ 2 − P_c` at the kernel `(ℓ, α′, C⁺)`. -/
def ShellCert (S : ShellProfile) (Pc : ℚ) : Prop :=
  1 < (S.lam : ℝ) ∧ (S.lam : ℝ) < 2 ∧ 1 < (S.alphaP : ℝ) ∧ AdmissibleS S.lam S.v ∧ S.L75 ∧
    Bshell S.level S.alphaP S.Cplus S.v ≤ 2 - (Pc : ℝ)

/-- Profile **S53-L75** (ssec:shell-cert-53, l.1224; `round2/d2_1_numerics/profiles53.json`):
`α′ = 2497/1500 = 5/3 − 1/500`, `λ = 191/100`, `ℓ = 1`, `C⁺ = 541161617/10⁸ ≥ π⁴/18`. -/
def S53L75 : ShellProfile where
  lam := 191 / 100
  alphaP := 2497 / 1500
  level := 1
  Cplus := 541161617 / 100000000
  d := [1, -109245641 / 315967035, -484609675 / 903872491, 1126440115 / 499347366,
        -1244916364 / 475100341, 381673291 / 981251350, 37853428 / 698475165]

/-- Profile **D53-L75** (l.1230): `α′ = 2497/1500`, `λ = 93/50`, `ℓ = 1`, `C⁺ = 721548823/10⁸ ≥ 2π⁴/27`. -/
def D53L75 : ShellProfile where
  lam := 93 / 50
  alphaP := 2497 / 1500
  level := 1
  Cplus := 721548823 / 100000000
  d := [1, -390353034 / 798066593, 1309177511 / 918253499, -6068806879 / 896328244,
        13364613432 / 870778397, -12836034741 / 854019032, 4242100897 / 905838731]

/-- `0.9059137927` — the 10-digit truncation of `2 − B(v_{S53-L75})` (exact rational `0.90591379273786…`,
`p_cert_exact53.txt`). -/
def PcertS53 : ℚ := 9059137927 / 10000000000

/-- `0.9031776196` — the 10-digit truncation for D53-L75 (exact `0.90317761969178…`). -/
def PcertD53 : ℚ := 9031776196 / 10000000000

/-- The certificate of the headline (sharp family). -/
def CertS53 : Prop := ShellCert S53L75 PcertS53

/-- The certificate of the dyadic headline. -/
def CertD53 : Prop := ShellCert D53L75 PcertD53

/-! ## §4 Headline statements (level C; `sorry` = the challenge) -/

/-- **Theorem S(5/3), family `1 < q ≤ Q`** (thm:shell-S53 with thm:shell-1pp at `α′ = 2497/1500`, `λ = 191/100`,
profile S53-L75): for `T = (log Q)^{r+ε}`, `r ≥ 3`, and every rate exponent `θ < θ(α′) = 503/1994`
(thm:shell-S53: `θ(α′) = min(1, (2−α′)/(2(α′−1)))`, `κ′ = 4 − 4/α′ + ε″`; the `(log log Q)^{O(1)}` factor and the
`ε″` are absorbed by `θ < 503/1994`),
`(0.9059137927 − c (log Q)^{−θ}) · Σ_χ N_χ(T,2T) ≤ Σ_χ N^s_{0,χ}(T,2T)`.
Same shape as `ZetaQ.JoinProved.theorem_one_generic_proved'`, with `0.7212 ↦ 0.9059137927` and the rate
`log log Q / log Q ↦ (log Q)^{−θ}`. -/
theorem shell_S53_qle (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertS53) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertS53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * famN (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
  sorry

/-- **Theorem S(5/3), dyadic family `Q/2 < q ≤ Q`** (thm:shell-S53 table, profile D53-L75, `λ = 93/50`):
constant `0.9031776196`. -/
theorem shell_S53_dyadic (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertD53) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertD53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * famN (modDyadic Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modDyadic Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
  sorry

/-! ### Bounded height (thm:bh-S (a), (a′)) -/

/-- The weight class of thm:bh-S (sec_bounded.tex l.335–337): `W` Schwartz, `0 ≤ W ≤ 1`,
`supp Ŵ ⊆ [−σ, σ]` in the draft's normalisation `Ŵ(s) = ∫ W(τ) e^{iτs} dτ` (sec_bounded.tex l.33), and
`TV(w) < ∞` for `w = W²`. -/
structure BandLimitedWeight (W : ℝ → ℝ) (σ : ℝ) : Prop where
  schwartz : ∃ f : SchwartzMap ℝ ℝ, ⇑f = W
  nonneg : ∀ x, 0 ≤ W x
  le_one : ∀ x, W x ≤ 1
  band : ∀ s : ℝ, σ < |s| → ∫ τ, (W τ : ℂ) * Complex.exp (Complex.I * τ * s) = 0
  bv : BoundedVariationOn (fun x => W x ^ 2) Set.univ

/-- `Σ_ρ w(γ_ρ) m_ρ` over the nontrivial zeros of `L(s,χ)` (a `tsum`; its summability is part of the headline). -/
def wSum (q : ℕ) (χ : DirichletCharacter ℂ q) (w : ℝ → ℝ) : ℝ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩;
    ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, w ρ.1.im * (zmult χ ρ.1 : ℝ)

/-- `Σ_ρ w(γ_ρ) 1[ρ simple, β = 1/2]`. -/
def wSumSC (q : ℕ) (χ : DirichletCharacter ℂ q) (w : ℝ → ℝ) : ℝ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩;
    ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (if ρ.1.re = 1 / 2 ∧ zmult χ ρ.1 = 1 then w ρ.1.im else 0)

/-- the weighted zero sums are genuinely summable for every member of the family (guards the `tsum` junk value). -/
def wSummable (M : Finset ℕ) (w : ℝ → ℝ) : Prop :=
  ∀ q ∈ M, ∀ χ ∈ primChars q, ∀ h : q ≠ 0, haveI : NeZero q := ⟨h⟩;
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => w ρ.1.im * (zmult χ ρ.1 : ℝ))

/-- **Theorem 1♮-S (a)**, bounded and low height, family `1 < q ≤ Q` (sec_bounded.tex l.334–348): for
`T_* ≤ T₀ ≤ (log Q)^{1+ε}` and `w_{T₀} = W(·/T₀)²`,
`Σ_χ Σ_ρ w_{T₀}(γ) 1[simple, β = ½] ≥ (0.9059137927 − c E_Q) Σ_χ Σ_ρ w_{T₀}(γ) m_ρ` with
`E_Q = log log Q/(T₀ log Q)^{1/2} + (log log Q)⁴ (log Q)^{−(503/1994 − O(ε″))} + log log Q/log Q`, written here, for
every `θ < 503/1994`, as `E_Q ≤ log log Q/(T₀ log Q)^{1/2} + (log Q)^{−θ}` (up to the constant `c`).
NB the draft marks this theorem a referee sketch with a [gap] (the per-layer tail `𝔓`) and a [CHECK] (λ-uniformity
of Lemma W.2 at `λ ∈ [1.86, 1.91]`); see the report. -/
theorem shell_S53_bounded (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertS53) (W : ℝ → ℝ) (σ : ℝ)
    (hW : BandLimitedWeight W σ) (Tstar ε θ : ℝ) (hT : 0 < Tstar) (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) → ∀ T₀ : ℝ, Tstar ≤ T₀ →
      T₀ ≤ Real.log (Qn : ℝ) ^ (1 + ε) →
      wSummable (modQle Qn) (fun γ => W (γ / T₀) ^ 2) ∧
      (((PcertS53 : ℚ) : ℝ) - c * (Real.log (Real.log (Qn : ℝ)) / Real.sqrt (T₀ * Real.log (Qn : ℝ))
          + Real.log (Qn : ℝ) ^ (-θ)))
          * (∑ q ∈ modQle Qn, ∑ χ ∈ primChars q, wSum q χ (fun γ => W (γ / T₀) ^ 2))
        ≤ ∑ q ∈ modQle Qn, ∑ χ ∈ primChars q, wSumSC q χ (fun γ => W (γ / T₀) ^ 2) := by
  sorry

/-- **Theorem 1♮-S (a′)**, dyadic family, constant `0.9031776196` (profile D53-L75). -/
theorem shell_S53_bounded_dyadic (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertD53) (W : ℝ → ℝ) (σ : ℝ)
    (hW : BandLimitedWeight W σ) (Tstar ε θ : ℝ) (hT : 0 < Tstar) (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) → ∀ T₀ : ℝ, Tstar ≤ T₀ →
      T₀ ≤ Real.log (Qn : ℝ) ^ (1 + ε) →
      wSummable (modDyadic Qn) (fun γ => W (γ / T₀) ^ 2) ∧
      (((PcertD53 : ℚ) : ℝ) - c * (Real.log (Real.log (Qn : ℝ)) / Real.sqrt (T₀ * Real.log (Qn : ℝ))
          + Real.log (Qn : ℝ) ^ (-θ)))
          * (∑ q ∈ modDyadic Qn, ∑ χ ∈ primChars q, wSum q χ (fun γ => W (γ / T₀) ^ 2))
        ≤ ∑ q ∈ modDyadic Qn, ∑ χ ∈ primChars q, wSumSC q χ (fun γ => W (γ / T₀) ^ 2) := by
  sorry

end ZetaShell
