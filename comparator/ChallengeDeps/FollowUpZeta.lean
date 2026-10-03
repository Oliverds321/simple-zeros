/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ChallengeDeps/FollowUpZeta.lean — the TRUSTED definition layer of the comparator topic `FollowUpZeta`
(the ζ follow-up paper: simple zeros, distinct zeros, simple zeros on the critical line, zeros that are simple or on the
critical line). Definitions only; no theorem. Imports only `ChallengeDeps` (itself Mathlib-only), from which it takes the
nontrivial zeros of Mathlib's `riemannZeta`, `zeroMult` (via `analyticOrderAt`), `zerosIn` (window T₁ < Im ρ ≤ T₂) and the
counting functions `Ncount` (with multiplicity), `Ndist`, `N0`, `N0simple`, `Nsimple`.

Everything here lives in the namespace `FollowUpZeta`. Each `def`/`structure` is a copy of the corresponding one of the
Lean development (`ZetaS/ChallengeZetaS.lean`, `ZetaS/Top/TopDefs.lean`, namespace `ZetaS`); `Solution/FollowUpZeta.lean`
converts between the two (the conversions are proofs, checked by comparator, not trusted).

Contents
  §1 `Nsc`, the count of zeros that are simple or on the critical line (cor:oll-SC);
  §2 the two windows of the paper and the normalised kernel `kPsi` (sec_zeta.tex, eq:zeta-R and the definition of k_ψ);
  §3 the local functionals: position weights, (LI′) = `LocalCert` (lem:zeta-Dprime, eq:zeta-LIw) and the all-marks
     inequality (LI_m) = `LocalCertAM` (def:zeta-LIm);
  §4 the three certificate hypotheses `CertS8`, `CertAM5`, `CertAM7`, each an explicit inequality about explicit numbers,
     established outside Lean by interval arithmetic (provenance in each doc-string; README_followup.md).
The majorant certificate of lem:sigd-env is NOT a hypothesis: it is a theorem of the development (kernel-checked).
-/
import ChallengeDeps

open scoped BigOperators
open Finset

noncomputable section

namespace FollowUpZeta

/-! ## §1 Zeros that are simple or on the critical line -/

/-- N^sc(T₁,T₂) (cor:oll-SC): the nontrivial zeros with T₁ < Im ρ ≤ T₂ that lie ON the critical line, counted WITH
multiplicity, plus those OFF the line that are simple (both members ρ, 1 − ρ̄ of each simple off-line pair; multiple
off-line zeros are not counted). An off-line zero in the set is simple, so its weight `zeroMult ρ` is 1. -/
def Nsc (T₁ T₂ : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ ({ρ | ρ.re = 1 / 2} ∪ {ρ | zeroMult ρ = 1}), zeroMult ρ

/-! ## §2 Windows and the normalised kernel -/

/-- The polynomial window ψ̃ of thm:zeta-mainw2:
ψ̃(s) = (50000/50037)(1 + (127/2500)u − (8997/10000)u² + (6187/10000)u³ + (3/1250)u⁴), u = (2s)²,
on [−1/2, 1/2] (values outside are never read). -/
def psiPoly8A (s : ℝ) : ℝ :=
  50000 / 50037 * (1 + 127 / 2500 * (2 * s) ^ 2 - 8997 / 10000 * ((2 * s) ^ 2) ^ 2
    + 6187 / 10000 * ((2 * s) ^ 2) ^ 3 + 3 / 1250 * ((2 * s) ^ 2) ^ 4)

/-- The window ψ(s) = cos(1.6 s) of thm:sigd-Sigma and thm:sigd-D. -/
def psiCos16 (s : ℝ) : ℝ := Real.cos (8 / 5 * s)

/-- The normalised Fourier transform of a window: k_ψ(x) = ∫_{−1/2}^{1/2} ψ(s) cos(2πxs) ds / ∫_{−1/2}^{1/2} ψ. -/
def kPsi (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s * Real.cos (2 * Real.pi * x * s))
    / ∫ s in (-(1 / 2 : ℝ))..(1 / 2), ψ s

/-! ## §3 The local inequalities -/

/-- Position weights for K consecutive points (lem:zeta-Dprime), 0-based: pair weights `γ s i` for spans
1 ≤ s ≤ K − 1 and positions 0 ≤ i < K − s, nonnegative and summing to 2 for every span; gap penalties `μ l ≥ 0`,
l : Fin (K − 1). Values of `γ` outside the index range are never read. -/
structure LocalWeights (K : ℕ) where
  γ : ℕ → ℕ → ℝ
  μ : Fin (K - 1) → ℝ
  two_le : 2 ≤ K
  γ_nonneg : ∀ s ∈ Icc 1 (K - 1), ∀ i ∈ range (K - s), 0 ≤ γ s i
  γ_sum : ∀ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), γ s i = 2
  μ_nonneg : ∀ l, 0 ≤ μ l

/-- ν := Σ_i μ_i. -/
def LocalWeights.nu {K : ℕ} (W : LocalWeights K) : ℝ := ∑ l, W.μ l

/-- The span g_i + ⋯ + g_{i+s−1} of a gap vector (0-based; indices ≥ K − 1 contribute nothing). -/
def gapSpan {K : ℕ} (g : Fin (K - 1) → ℝ) (i s : ℕ) : ℝ :=
  ∑ l ∈ univ.filter (fun l : Fin (K - 1) => i ≤ l.val ∧ l.val < i + s), g l

/-- F_{γ,μ}(g) = Σ_i μ_i g_i + Σ_{s=1}^{K−1} Σ_i γ_{s,i} k(g_i + ⋯ + g_{i+s−1})² (eq:zeta-LIw). -/
def localF (k : ℝ → ℝ) {K : ℕ} (W : LocalWeights K) (g : Fin (K - 1) → ℝ) : ℝ :=
  (∑ l, W.μ l * g l)
    + ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * k (gapSpan g i s) ^ 2

/-- (LI′) of lem:zeta-Dprime: F_{γ,μ}(g) ≥ c for every gap vector g ∈ [0,∞)^{K−1}. -/
def LocalCert (k : ℝ → ℝ) {K : ℕ} (W : LocalWeights K) (c : ℝ) : Prop :=
  ∀ g : Fin (K - 1) → ℝ, (∀ l, 0 ≤ g l) → c ≤ localF k W g

/-- All-marks data (def:zeta-LIm): position weights as in `LocalWeights` and site credits `b i j` for site i : Fin K and
capped mark j : Fin 2 (j = 0 ↦ mark 1, j = 1 ↦ mark 2); no sign condition. -/
structure MarkWeights (K : ℕ) extends LocalWeights K where
  b : Fin K → Fin 2 → ℝ

/-- a_j := Σ_i b_i(j); `a 0 = a₁`, `a 1 = a₂`. -/
def MarkWeights.a {K : ℕ} (W : MarkWeights K) (j : Fin 2) : ℝ := ∑ i, W.b i j

/-- The numerical mark m_i ∈ {1, 2} at 0-based position i of a pattern (0 outside [0, K)). -/
def markVal {K : ℕ} (m : Fin K → Fin 2) (i : ℕ) : ℝ :=
  if h : i < K then ((m ⟨i, h⟩ : ℕ) : ℝ) + 1 else 0

/-- F_𝐦(g) = Σ_{s,i} γ_{s,i} m_i m_{i+s} k(g_i + ⋯ + g_{i+s−1})² + Σ_i μ_i g_i (def:zeta-LIm). -/
def localFm (k : ℝ → ℝ) {K : ℕ} (W : MarkWeights K) (m : Fin K → Fin 2) (g : Fin (K - 1) → ℝ) : ℝ :=
  (∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s),
      W.γ s i * markVal m i * markVal m (i + s) * k (gapSpan g i s) ^ 2)
    + ∑ l, W.μ l * g l

/-- (LI_m) of def:zeta-LIm: for EVERY mark pattern 𝐦 ∈ {1,2}^K and every g ∈ [0,∞)^{K−1}, F_𝐦(g) ≥ Σ_i b_i(m_i). -/
def LocalCertAM (k : ℝ → ℝ) {K : ℕ} (W : MarkWeights K) : Prop :=
  ∀ m : Fin K → Fin 2, ∀ g : Fin (K - 1) → ℝ, (∀ l, 0 ≤ g l) → ∑ i, W.b i (m i) ≤ localFm k W m g

/-! ## §4 The certificate hypotheses

Each Prop asserts that SOME weights with the stated constants satisfy the local inequality on the whole orthant. The
weights that realise it are exact rationals in the data files named below (identified by sha256); the inequality for those
weights was established outside Lean by interval branch-and-bound (Arb ball arithmetic, every box accepted only when a
rigorous lower bound exceeds the claim; the unbounded part of the orthant is discarded exactly, since
F ≥ (min μ)·Σ g there). Paths are relative to the development's project folder; the files named here are in
`supplementary/certificates/` of the repository, some logs under new names (map: `supplementary/README.md`). -/

/-- **Certificate S8** (thm:zeta-mainw2, rem:zeta-P8, lem:zeta-Dprime): K = 8, window ψ̃, weights with ν = 7/1700 for
which (LI′) holds at the claim c = 0.00796.
Data: `round2/d6_5_numerics/w_poly8A_K8_mu1700.json`, sha256
`257b340d9da4f343600a21589f16d8915f3e082499d475e153c5453980671e78`; window `round2/d6_5_numerics/win_poly8A.json`,
sha256 `c4005f57a7920f78aa2df33b093c9c5030efac2b8e39fc6cf7371b0c0f32dc14` (the unnormalised v = (50037/50000)ψ̃; the kernel
is homogeneous of degree 0). Certifier `round2/d6_5_numerics/bnb_lb3.py` with `polywin.py`; runs
`round2/d6_5_numerics/runs/P8/DRIVER.log` and the independent re-run `runs/P8b/DRIVER.log`, both ending
`ALL SHARDS OK: certificate claim=0.00796 holds` (about 4.5·10⁸ boxes each). -/
def CertS8 : Prop :=
  ∃ W : LocalWeights 8, W.nu = 7 / 1700 ∧ LocalCert (kPsi psiPoly8A) W (199 / 25000)

/-- **Certificate AM5** (thm:zeta-allmarks, rem:sigd-cert, the K = 5 row): all-marks data with a₁ = 1280197/10⁸,
a₂ = 48749/3125000, ν = 1/125 for which (LI_m) holds for k_ψ, ψ = cos 1.6s.
Data: `round1/X2_numerics/claims_a1.6_K5_mu500.json` (byte-identical to `claims_d15e6_a1.6_K5_mu500.json`), sha256
`cf055dd2ee9a9e469b6510fe70b5fbc416b8a40515cc6746bc390d40d88777f2`; the 20 class files `xpat_K5_*.json` of the same
folder, sha256 of their concatenation in sorted file-name order
`a5947c01d34ddcbc7366861b35e83942099fcbf7ac71e13fcd432796882dd34e`. Certifier `round1/X2_numerics/bnb_interval_w.py`;
logs `cert_K5_w_a16_mu500_d15e6.txt` and `cert_K5_w_a16_mu500_d15e6_b.txt` (20/20 reversal classes ok, covering the 32
patterns; the weights are reversal-symmetric). A replay of this certificate by the Lean kernel was completed on
28 September 2026: `ZetaS.CertV2.certAM5_replayed` proves the library's copy `ZetaS.CertAM5`, and the hypothesis-free
K = 5 theorems are in the module `ReplayHeadlines` of the library `ZetaSReplay`. In the statements of this topic the
Prop remains a displayed hypothesis, like the other two. -/
def CertAM5 : Prop :=
  ∃ W : MarkWeights 5, W.a 0 = 1280197 / 10 ^ 8 ∧ W.a 1 = 48749 / 3125000 ∧ W.nu = 1 / 125 ∧
    LocalCertAM (kPsi psiCos16) W

/-- **Certificate AM7** (thm:sigd-Sigma, thm:sigd-D, rem:sigd-cert, the K = 7 row): all-marks data with
a₁ = 1824837/10⁸, a₂ = 1168069/(5·10⁷), ν = 3/250 for which (LI_m) holds for k_ψ, ψ = cos 1.6s.
Data: `round2/d8_9_numerics/k7m500/rerun/claims_a1.6_K7_mu500_L1e5.json` (the final claims, every claim of the LP lowered by
exactly 10⁻⁵), sha256 `d2cf393019407bdc797c73147ec8e3dc66ec41fe745600c84173f74ac66bfc5c`; the 72 class files
`xpat_K7_*.json` of the same folder, sha256 of their concatenation in sorted file-name order
`33c4c8c5762bcebdf8f544ab34a137a6a7ba4065d08f5caee0a51188e1a67514`. Certifier `round2/d8_9_numerics/bnb_lb3_w.py`
(driver `runlb3.sh`); certificate log `round2/d8_9_numerics/k7m500/rerun/cert_lb3_rerun.txt` (72/72 reversal classes ok,
each at exactly the final claim); completeness (the 72 classes cover all 128 patterns, each certified at a claim ≥ the
required one) `round2/d8_21_numerics/k7_verify_pexact2.txt`. The weights are reversal-symmetric. -/
def CertAM7 : Prop :=
  ∃ W : MarkWeights 7, W.a 0 = 1824837 / 10 ^ 8 ∧ W.a 1 = 1168069 / (5 * 10 ^ 7) ∧ W.nu = 3 / 250 ∧
    LocalCertAM (kPsi psiCos16) W

end FollowUpZeta
