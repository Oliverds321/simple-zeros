/-
lean_work/L0_4/ChallengeZetaS.lean — the MATHLIB-ONLY statement layer of the ζ follow-up (L0_4, 28 Sep 2026).

Intended home: `comparator/Challenge/FollowUpZeta.lean` (LEAN_PLAN §2). It imports only `ChallengeDeps` (the tree's
trusted, Mathlib-only definition layer: `Ncount`, `Ndist`, `N0`, `N0simple`, `Nsimple`, `zerosIn`, `zeroMult`), so a
reader auditing WHAT is claimed reads ChallengeDeps.lean and this file only.

Contents
  §1 the windows of the draft (`psiPoly8A` of thm:zeta-mainw2, `psiCos16` of thm:sigd-Sigma/D) and the normalised
     kernel `kPsi ψ` (sec_zeta.tex l.107);
  §2 `LocalCert`   — the position-weighted local inequality (LI′) of lem:zeta-Dprime, eq:zeta-LIw (l.514–522);
     `LocalCertAM` — the all-marks local inequality (LI_m) of def:zeta-LIm (l.973–986);
     `MajorantCert` — the certified Beurling–Selberg-type majorant of lem:sigd-env (l.1274–1297);
  §3 `Nsc` — the simple-or-critical count of cor:oll-SC (l.667–669);
  §4 the three certificates as displayed Props (`CertS8`, `CertAM7`, `CertMaj`, with the sha256 of their data);
  §5 (removed 28 Sep 2026: the headline statements live in comparator/Challenge/FollowUpZeta.lean).

Design choices (see report §4, open questions):
  * Each certificate Prop is existential in the weight data: it asserts SOME weights `W` with the stated
    `ν = Σμ` (and site-credit sums `a₁, a₂`) for which the local inequality holds with the stated claim. The
    constants of thm:zeta-G / thm:sigd-Sigma depend on the weights only through `(K, ν, c)` resp. `(K, ν, a₁, a₂)`,
    so no JSON data enters a statement; the certificate track proves the Prop with the file's `W` as witness.
  * Gap vectors live in `Fin (K−1) → ℝ` with all entries `≥ 0` — the full orthant `[0,∞)^{K−1}` of eq:zeta-LI.
    Reversal symmetry, box pruning at large gaps and pattern-class reductions used by the certifiers are NOT part
    of these Props; they are theorems of the reduction/certificate tracks (nodes C-rev, C-prune, C-class).
  * Penalties `μ_i ≥ 0` (the draft says `> 0`; only `≥ 0` is used) — a weaker hypothesis.

No `sorry` (since 28 Sep 2026; the four challenge-side `sorry` statements of §5 were removed).
-/
import ChallengeDeps

noncomputable section

open scoped BigOperators
open Finset

namespace ZetaS

/-! ## §1 Windows and kernels -/

/-- The polynomial window `ψ̃` of `thm:zeta-mainw2` (sec_zeta.tex l.566):
`ψ̃(s) = (50000/50037)(1 + (127/2500)u − (8997/10000)u² + (6187/10000)u³ + (3/1250)u⁴)`, `u = (2s)²`,
on `[−1/2, 1/2]` (values outside are never read). -/
def psiPoly8A (s : ℝ) : ℝ :=
  50000 / 50037 * (1 + 127 / 2500 * (2 * s) ^ 2 - 8997 / 10000 * ((2 * s) ^ 2) ^ 2
    + 6187 / 10000 * ((2 * s) ^ 2) ^ 3 + 3 / 1250 * ((2 * s) ^ 2) ^ 4)

/-- The window `ψ(s) = cos(1.6 s)` of `thm:sigd-Sigma`, `thm:sigd-D` (sec_zeta.tex l.1068). -/
def psiCos16 (s : ℝ) : ℝ := Real.cos (8 / 5 * s)

/-- The normalised Fourier transform of a window (sec_zeta.tex l.107):
`k_ψ(x) = ∫_{−1/2}^{1/2} ψ(s) cos(2πxs) ds / ∫_{−1/2}^{1/2} ψ`. (For even `ψ` this is `∫ψ(s)e(xs)ds/∫ψ`.) -/
def kPsi (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s * Real.cos (2 * Real.pi * x * s))
    / ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s

/-! ## §2 The certified local inequalities -/

/-- Position weights for windows of `K` consecutive points (lem:zeta-Dprime, l.515–516), 0-based:
pair weights `γ s i` for spans `1 ≤ s ≤ K−1` and positions `0 ≤ i < K−s`, nonnegative, summing to `2` for every
span; gap penalties `μ l ≥ 0`, `l : Fin (K−1)`. Values of `γ` outside the index range are never read. -/
structure LocalWeights (K : ℕ) where
  γ : ℕ → ℕ → ℝ
  μ : Fin (K - 1) → ℝ
  two_le : 2 ≤ K
  γ_nonneg : ∀ s ∈ Icc 1 (K - 1), ∀ i ∈ range (K - s), 0 ≤ γ s i
  γ_sum : ∀ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), γ s i = 2
  μ_nonneg : ∀ l, 0 ≤ μ l

/-- `ν := Σ_i μ_i` (lem:zeta-Dprime). -/
def LocalWeights.nu {K : ℕ} (W : LocalWeights K) : ℝ := ∑ l, W.μ l

/-- The span `g_i + ⋯ + g_{i+s−1}` of a gap vector (0-based; indices `≥ K−1` contribute nothing). -/
def gapSpan {K : ℕ} (g : Fin (K - 1) → ℝ) (i s : ℕ) : ℝ :=
  ∑ l ∈ univ.filter (fun l : Fin (K - 1) => i ≤ l.val ∧ l.val < i + s), g l

/-- `F_{γ,μ}(g) = Σ_i μ_i g_i + Σ_{s=1}^{K−1} Σ_{i} γ_{s,i} k(g_i + ⋯ + g_{i+s−1})²` (eq:zeta-LIw, l.518). -/
def localF (k : ℝ → ℝ) {K : ℕ} (W : LocalWeights K) (g : Fin (K - 1) → ℝ) : ℝ :=
  (∑ l, W.μ l * g l)
    + ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * k (gapSpan g i s) ^ 2

/-- **`LocalCert k W c`** — the position-weighted local inequality (LI′) (eq:zeta-LIw):
`F_{γ,μ}(g) ≥ c` for every gap vector `g ∈ [0,∞)^{K−1}`. With `γ s i = 2/(K−s)`, `μ l = μ` it is (LI) of
def:zeta-LI (l.109–116). This is the Prop the certificate track proves and the reduction track assumes. -/
def LocalCert (k : ℝ → ℝ) {K : ℕ} (W : LocalWeights K) (c : ℝ) : Prop :=
  ∀ g : Fin (K - 1) → ℝ, (∀ l, 0 ≤ g l) → c ≤ localF k W g

/-- All-marks data (def:zeta-LIm, l.974–979): position weights as in `LocalWeights` and site credits
`b i j` for site `i : Fin K` and capped mark `j : Fin 2` (`j = 0` ↦ mark 1, `j = 1` ↦ mark 2); no sign condition. -/
structure MarkWeights (K : ℕ) extends LocalWeights K where
  b : Fin K → Fin 2 → ℝ

/-- `a_j := Σ_i b_i(j)` (def:zeta-LIm); `a 0 = a₁`, `a 1 = a₂`. -/
def MarkWeights.a {K : ℕ} (W : MarkWeights K) (j : Fin 2) : ℝ := ∑ i, W.b i j

/-- The numerical mark `m_i ∈ {1, 2}` at 0-based position `i` of a pattern (`0` outside `[0, K)`). -/
def markVal {K : ℕ} (m : Fin K → Fin 2) (i : ℕ) : ℝ :=
  if h : i < K then ((m ⟨i, h⟩ : ℕ) : ℝ) + 1 else 0

/-- `F_𝐦(g) = Σ_{s,i} γ_{s,i} m_i m_{i+s} k(g_i + ⋯ + g_{i+s−1})² + Σ_i μ_i g_i` (def:zeta-LIm, l.982). -/
def localFm (k : ℝ → ℝ) {K : ℕ} (W : MarkWeights K) (m : Fin K → Fin 2) (g : Fin (K - 1) → ℝ) : ℝ :=
  (∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s),
      W.γ s i * markVal m i * markVal m (i + s) * k (gapSpan g i s) ^ 2)
    + ∑ l, W.μ l * g l

/-- **`LocalCertAM k W`** — (LI_m) of def:zeta-LIm: for every mark pattern `𝐦 ∈ {1,2}^K` and every
`g ∈ [0,∞)^{K−1}`, `F_𝐦(g) ≥ C(𝐦) := Σ_i b_i(m_i)`. -/
def LocalCertAM (k : ℝ → ℝ) {K : ℕ} (W : MarkWeights K) : Prop :=
  ∀ m : Fin K → Fin 2, ∀ g : Fin (K - 1) → ℝ, (∀ l, 0 ≤ g l) → ∑ i, W.b i (m i) ≤ localFm k W m g

/-- **`MajorantCert ψ λ`** — the certified input of lem:sigd-env (l.1283–1296), in the form the proof uses:
an even integrable `B ≥ 0` on `ℝ` with `B ≥ v_ψ := ψ/∫ψ` on `[−1/2,1/2]`, whose Fourier transform
`B̂(t) = ∫ B(s) cos(2πts) ds` vanishes for `|t| ≥ 1`, and with `2 B̂(0) + 4 sup_{[3/4,1]} |B̂| < λ`.
The draft's instance: `B̂` piecewise linear with nodes `j/60`, `β₀ = 1.5556524027186915`, `β* = |β₅₂|`,
and `λ = λ_c = 2 + √(2 − 2a₁)`. -/
def MajorantCert (ψ : ℝ → ℝ) (lam : ℝ) : Prop :=
  ∃ B : ℝ → ℝ, MeasureTheory.Integrable B ∧ (∀ s, B (-s) = B s) ∧ (∀ s, 0 ≤ B s) ∧
    (∀ s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ψ s / (∫ t in (-(1 / 2 : ℝ))..(1 / 2), ψ t) ≤ B s) ∧
    (∀ t : ℝ, 1 ≤ |t| → ∫ s, B s * Real.cos (2 * Real.pi * t * s) = 0) ∧
    ∃ βstar : ℝ, (∀ t ∈ Set.Icc (3 / 4 : ℝ) 1, |∫ s, B s * Real.cos (2 * Real.pi * t * s)| ≤ βstar) ∧
      2 * (∫ s, B s) + 4 * βstar < lam

/-! ## §3 The simple-or-critical count -/

/-- `N^sc(T₁,T₂)` (cor:oll-SC, l.667–669): the zeros with `T₁ < Im ρ ≤ T₂` on the critical line counted WITH
multiplicity, plus the simple zeros off the line (both members of each simple off-line pair). An off-line zero
in the set is simple, so its weight `zeroMult ρ` is `1`. -/
def Nsc (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ ({ρ | ρ.re = 1 / 2} ∪ {ρ | zeroMult ρ = 1}), zeroMult ρ

/-! ## §4 The certificates as displayed hypotheses (one Prop per certificate; upstream `EnclOK` idiom)

Each Prop below is the whole content of one external certificate. Until the certificate track replays it in the kernel
(LEAN_PLAN Revision 1: level A target), the headline theorems take it as one displayed hypothesis (level C). The data
files that realise the existential witnesses are identified by sha256 (computed 28 Sep 2026 by L0_4). -/

/-- **Certificate S8** (thm:zeta-mainw2, rem:zeta-P8): weights with `ν = 7/1700` for which (LI′) holds for `k_ψ̃`
at claim `c = 0.00796`, `K = 8`. Data: `rh72/round2/d6_5_numerics/w_poly8A_K8_mu1700.json`,
sha256 `257b340d9da4f343600a21589f16d8915f3e082499d475e153c5453980671e78`
(identical copy in `round2/d8_2_numerics/`). Certified by LB3 interval branch-and-bound, ≈ 4.5·10⁸ boxes. -/
def CertS8 : Prop :=
  ∃ W : LocalWeights 8, W.nu = 7 / 1700 ∧ LocalCert (kPsi psiPoly8A) W (199 / 25000)

/-- **Certificate AM7** (thm:sigd-Sigma/D, rem:sigd-cert, `K = 7` row): all-marks data with
`a₁ = 1824837/10⁸`, `a₂ = 1168069/(5·10⁷)`, `ν = 3/250` for which (LI_m) holds for `k_ψ`, `ψ = cos 1.6s`.
Data: claims `rh72/round2/d8_9_numerics/k7m500/rerun/claims_a1.6_K7_mu500_L1e5.json`,
sha256 `d2cf393019407bdc797c73147ec8e3dc66ec41fe745600c84173f74ac66bfc5c`; the 72 class files
`xpat_K7_*.json` of the same folder, sha256 of their concatenation in sorted file-name order
`33c4c8c5762bcebdf8f544ab34a137a6a7ba4065d08f5caee0a51188e1a67514`. The certifier ran on 72 reversal classes
covering the 128 patterns; the reduction to classes is a theorem of the certificate track (node C-rev), not part
of this Prop. -/
def CertAM7 : Prop :=
  ∃ W : MarkWeights 7, W.a 0 = 1824837 / 10 ^ 8 ∧ W.a 1 = 1168069 / (5 * 10 ^ 7) ∧ W.nu = 3 / 250 ∧
    LocalCertAM (kPsi psiCos16) W

/-- **Certificate Maj** (lem:sigd-env): the majorant for `ψ = cos 1.6s` with `2β₀ + 4β* < 3.2063638853`
(draft: `2β₀ + 4β* = 3.2063638852…`, `< λ_c = 3.40125…`). Data:
`rh72/round2/d6_6b_numerics/majorant_delta1_beta.npy` (60 binary64 coefficients `β_j`, read as exact rationals),
sha256 `fd909f79669e2fc1ba5fd4e44d01d6007ccf5303b7ce62d4c5ee08f7ef024845`; certifier `round2/d7_6_numerics/r4_majorant_arb.py`. -/
def CertMaj : Prop := MajorantCert psiCos16 (32063638853 / 10 ^ 10)

/-! ## §5 (removed)
The four `sorry` headline statements of this section were removed on 28 Sep 2026 (integrator L0_5, lead's ruling
D7 of 12:25): the headline statements are now `comparator/Challenge/FollowUpZeta.lean` (fourteen statements,
proved in `comparator/Solution/FollowUpZeta.lean`); the library's proofs are `ZetaS.Top.zeta_*_final`
(`Top/TopFinal`), `ZetaS.Top.zeta_simple_on_line` and `ZetaS.Top.zeta_simple_or_critical` (`Top/TopSSC`). -/

end ZetaS
