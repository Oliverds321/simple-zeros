/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Normalisation.lean — paper §12 (normalisation of the q ≤ Q family) and Corollary 3's
twenty obligations (the two-zone even/odd primitive argument).

Statement source of truth: paper §12 and §1.1. The obligations are grouped as PARTS B and C
below.

=============================================================================================
IMPORT-GRAPH AMENDMENT — FLAGGED, NOT SNUCK IN
=============================================================================================
§12 would naturally import `Defs` and `CharSums` only. This file additionally imports
`ZetaQ.Payoff`, because three of its required statements are statements ABOUT §11's
functional and cannot be written without it:
  * `GainPositiveAllC`     (§12.3 — "§11's gain is positive for every
    finite C"),
  * `Trap0p3693`           (§12.3 / Cor. 3 O20 — "§11 at in-zone weight 2|α|"),
  * `Cor3.corollary3_*`    (O17/O18 — "instantiates PART A").
The edge introduces NO cycle: `ZetaQ.Payoff` imports `ZetaQ.Defs` only. To keep §12
independent of §11 those three declarations would have to move to the library root
`ZetaQ.lean` — nothing else in this file touches `Payoff`.

=============================================================================================
WHAT THIS FILE TAKES AS EXPLICIT HYPOTHESES (and why)
=============================================================================================
`ZetaQ.CharSums` (§5) IS imported here, but **this file references no name from it**. The
shapes of §5's declarations were not fixed when this file was written, and an extra
hypothesis is auditable where a wrong name is a build break, so the dependency was taken as
hypotheses and has been left that way: the hypotheses below are auditable one by
one, and each is discharged against the real §5 theorem at its call site. Everything §5 owns
enters as an explicit hypothesis of the statement that consumes it:
  * Lemma 5.2′ (the `n + m` aggregated identity, crude form) — hypothesis `h52'` of
    `Cor3.parity_neg_half_bound`;
  * Lemma 5.3′ (the `τ(n+m)` divisor average, zone form) — hypothesis of
    `Cor3.in_zone_neg_half_negligible`, against an abstract `Zplus : ℕ → ℝ`;
  * `Zeta23`'s per-χ Riemann–von-Mangoldt count — hypothesis `hRvM` of
    `Cor3.zeroCountEven_asymp`.
Likewise `evenPrimitiveChars` / `oddPrimitiveChars` are defined LOCALLY here (through the
frozen `ZetaQ.parity` of `Defs`) rather than imported; `CharSums` is expected to carry its own
copies, and the two ought to be identified.

=============================================================================================
REPAIRS MADE IN THIS FILE
=============================================================================================
The standing policy is that *a demonstrably false statement is repaired in place, not
preserved* (D14 / D17). Two statements
here were false; each repair is recorded in full in the docstring of the declaration it
touches — what was wrong, the failing instance, what it now says, and why the new form is
the paper's claim rather than a weakening.

  * **`subfamily_passage` was FALSE.** Its §§3–10 interface was a bare function
    `pay : Subfamily → (ℝ → ℝ) → ℝ` constrained only at `fullFamily`, so nothing tied
    `pay S` to `pay fullFamily`. Counterexample in the docstring of `PassageInterface`, the
    bundled structure that replaces it; the structure's fields are exactly the hypotheses of
    O13 and O14, all four forms of which (`out_zone_constant_scales`,
    `error_rows_factor_scales`, and their `α = 1/2` instances `Cor3.out_zone_constant_doubles`,
    `Cor3.error_rows_factor_two`) are PROVED here. `subfamily_passage`'s conclusion is
    unchanged and the theorem is now proved. `Cor3.corollary3_even_dyadic` and
    `corollary3_odd_dyadic`, which additionally could not compose because their `hfull` sat
    at a FREE parameter `fullFamDyad` where the passage needs the constant `fullFamily`, are
    repaired the same way and are now proved. `corollary3_even_qQ`, which was already correct,
    keeps its statement and proof and only moves to the new interface.
  * **O15 `Cor3.zeroCountEven_asymp` was FALSE — and this one is the PAPER's,
    not a transcription slip.** §1.1's `𝒩_even = ½𝒩 + O(QTℒ)` omits the `≍Q²` per-character
    `O(log qT)` RvM errors. Repaired to `O(QTℒ + Q²·log QT)`, with the counterexample, the
    corrected relative error `O(1/T)` (not `O(1/Q)`), and the one-clause paper edit all
    recorded in its docstring. The corollary survives with six orders of margin.

=============================================================================================
R-B1 — A REAL LIMITATION, RECORDED RATHER THAN HIDDEN
=============================================================================================
§12.3's 0.3693 "trap" is the justification that obligation (ii) is
not removable. Stating it requires a **LOWER bound on `min B`** for the both-zones-doubled
functional. The feasibility route of `ZetaQ/Payoff.lean` supplies UPPER bounds on
`min B` only. **This is the single place where §12.3's argument and the chosen Lean route do
not meet.** `Trap0p3693` below is therefore an obligation that the payoff certificate cannot
discharge; it is not load-bearing for Theorem 1 or Corollary 3, but it is not silently dropped
either.

=============================================================================================
RULE 17
=============================================================================================
* **λ ≤ 1.** Corollary 3's out-zone (O13) is precisely the region "where `n` reaches
  `X = Q^λ` and `n + m` outruns every modulus". Nothing in this file caps
  the bandwidth: every §11-facing statement carries `1 < lam ∧ lam < 2` explicitly. §12.2 is
  entirely λ-free (it is arithmetic in `q`). The projection route's FAILURE out-zone at
  `λ > 1` by `Q^{λ−1}` is documented at `Cor3.out_zone_constant_doubles`; it is a reason the
  positivity route is used there, never a hypothesis.
* **X ≤ T.** No hypothesis anywhere relates `X` to `T`. At fill time, check that the sieve
  interface consumed by O13 (Lemma 6.1, budget `N + Q² − 1`) does not import one from a
  T-aspect mirror.
* **D₀ = √T.** §12 has no `D₀`; O15's `𝒩_even = ½𝒩 + O(QTℒ)` is `D₀`-free. Nothing here can
  smuggle it.
-/
import ZetaQ.Defs
import ZetaQ.CharSums
import ZetaQ.Payoff

noncomputable section

open scoped BigOperators
open Filter Asymptotics

namespace ZetaQ.Normalisation

/-! ## §12.1 — the consumed object

**NO PROPOSITIONAL CONTENT. This section is a docstring and must stay one** (
Resolution R-B2: "Do not manufacture lemmas for them; a reviewer will read the invented
statement as an over-claim").

Paper §12.1, verbatim: "The consumed object is a large-sieve majorant of the family second
moment of a prime-supported Dirichlet polynomial at the common scale ℒ — defined by the
construction, single-scale by fiat of the common taper (itself forced by Lemma 6.1's single
coefficient vector). It is not [CLLR]'s F_Φ."

Its only checkable consequence is already §2.2's family form-factor bound `F_fam(α) ≤ C|α|`
with `C = Q²/|𝔉_Q|` (`ZetaQ.Cfam`), owned by the sieve/certificate tracks — not restated here.

The "single-scale by fiat" clause IS enforceable, but at the level of TYPES rather than
theorems: the coefficient vector of Lemma 6.1 does not depend on `q` or `χ`, i.e. the sieve
input has type `a : ℕ → ℂ`, **never** `a : ℕ → ℕ → ℂ` and never `∀ q, DirichletCharacter ℂ q →
ℕ → ℂ`. Enforced by construction in §6's signatures; no theorem is needed, and
none is written. -/

/-! ## §12.2 — the conductor normalisation

Arithmetic verified off-line, with no discrepancy: all six averages
reproduce from `dm = 2(18/π⁴)x dx` by partial summation, and the Dirichlet-series residue
`Σφ*(n)n^{−s} = ζ(s−1)/ζ(s)²` gives `18/π⁴` at `s = 2`.

Rule 17 for the whole section: **λ-free, X-free, T-free, D₀-free.** These are statements about
the distribution of conductors, and the only scale that appears is `ℒ = log(QT/2π)` in N9/N10,
carried as a function of `Q` with its own explicit hypotheses. -/

/-- `|𝔉_x|` as a real-variable function — the frozen `ZetaQ.famCard` at `⌊x⌋₊`.

Paper §2.2.
Depends on: `ZetaQ.famCard`. Rule 17: λ-free. -/
def famCardR (x : ℝ) : ℝ := (ZetaQ.famCard ⌊x⌋₊ : ℝ)

/-- The dyadic family size as a real-variable function (Corollary 2, `q ∈ (Q/2, Q]`).

Paper §12.2.
Depends on: `ZetaQ.famCardDyadic`. Rule 17: λ-free. -/
def famCardDyadicR (x : ℝ) : ℝ := (ZetaQ.famCardDyadic ⌊x⌋₊ : ℝ)

/-- **N1.** `φ*(q) = Σ_{d ∣ q} μ(q/d) φ(d)` — the primitive-character count as a Möbius
convolution.

Paper §12.2 (the object `Σ_{q≤x}φ*(q)` is built from this); standard, cf.
`LEMMA_Q5`.
Depends on: `ZetaQ.phiStar`, Mathlib `ArithmeticFunction.moebius`, `Nat.totient`.
Rule 17: λ-free, X-free, D₀-free. -/
theorem phiStar_eq_moebius_sum (q : ℕ) (hq : 1 ≤ q) :
    (ZetaQ.phiStar q : ℤ)
      = ∑ d ∈ q.divisors, ArithmeticFunction.moebius (q / d) * (Nat.totient d : ℤ) := by
  have : NeZero q := ⟨by omega⟩
  exact _root_.ZetaQ.phiStar_eq_moebius_sum q

/-! ### N2's engine — the Möbius-hyperbola development, fill-local

Everything in this namespace is machinery for `sum_phiStar_asymp` and is used nowhere else.
The route is entirely elementary (no Perron, no contour): `φ* = μ ⋆ φ` (the frozen
`ZetaQ.phiStar_eq_moebius_sum`) and `φ = μ ⋆ id` (Mathlib's `Nat.sum_totient` plus Möbius
inversion) are each summed by the Dirichlet hyperbola reindexing `N2.hyperbola`, against the
one analytic input `Σ_{d≥1} μ(d)/d² = 6/π²` (`N2.hasSum_mu_sq`, from Mathlib's
`LSeries_zeta_mul_Lseries_moebius` and `riemannZeta_two`). -/
namespace N2

/-- Dirichlet hyperbola reindexing: `∑_{q≤N} ∑_{de=q} F d e = ∑_{d≤N} ∑_{m ≤ ⌊N/d⌋} F d m`. -/
theorem hyperbola (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ q ∈ Finset.Icc 1 N, ∑ p ∈ q.divisorsAntidiagonal, F p.1 p.2
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), F d m := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun x => (⟨x.2.1, x.2.2⟩ : (_ : ℕ) × ℕ))
    (j := fun y => (⟨y.1 * y.2, (y.1, y.2)⟩ : (_ : ℕ) × (ℕ × ℕ))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, d, m⟩ hx
    obtain ⟨hq, hp⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq1, hqN⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hdm, hq0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exfalso; rw [Nat.zero_mul] at hdm; omega
      · exact h
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · exfalso; rw [Nat.mul_zero] at hdm; omega
      · exact h
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, ?_⟩, Finset.mem_Icc.mpr ⟨hm0, ?_⟩⟩
    · calc d ≤ d * m := Nat.le_mul_of_pos_right _ hm0
        _ = q := hdm
        _ ≤ N := hqN
    · rw [Nat.le_div_iff_mul_le hd0, mul_comm, hdm]; exact hqN
  · rintro ⟨d, m⟩ hy
    obtain ⟨hd, hm⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hd0 : 0 < d := hd1
    have hmd : m * d ≤ N := (Nat.le_div_iff_mul_le hd0).mp hmN
    have hdmN : d * m ≤ N := by rw [mul_comm]; exact hmd
    have hpos : 0 < d * m := Nat.mul_pos hd0 hm1
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hdmN⟩, ?_⟩
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hpos.ne'⟩
  · rintro ⟨q, d, m⟩ hx
    obtain ⟨_, hp⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hdm, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    simp only [hdm]
  · rintro ⟨d, m⟩ _
    rfl
  · rintro ⟨q, d, m⟩ _
    rfl

/-- `φ = μ ⋆ id`, in antidiagonal form (Möbius inversion of `Nat.sum_totient`). -/
theorem totient_eq_moebius_conv {m : ℕ} (hm : 0 < m) :
    (Nat.totient m : ℤ)
      = ∑ p ∈ m.divisorsAntidiagonal, ArithmeticFunction.moebius p.1 * (p.2 : ℤ) := by
  have h : ∀ n : ℕ, n > 0 → ∑ i ∈ n.divisors, (Nat.totient i : ℤ) = (n : ℤ) := by
    intro n _
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) (Nat.sum_totient n)
  have h2 := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (R := ℤ)
      (f := fun i => (Nat.totient i : ℤ)) (g := fun n => (n : ℤ))).mp h m hm
  rw [← h2]
  exact Finset.sum_congr rfl (fun p _ => by simp)

/-- `μ` with real values. -/
def mu (e : ℕ) : ℝ := (ArithmeticFunction.moebius e : ℝ)

theorem abs_mu_le (e : ℕ) : |mu e| ≤ 1 := by
  rw [mu, ← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- `S(K) = ∑_{c ≤ K} c`. -/
def Sid (K : ℕ) : ℝ := ∑ c ∈ Finset.Icc 1 K, (c : ℝ)

/-- `Φ(M) = ∑_{m ≤ M} φ(m)`. -/
def Phi (M : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 M, (Nat.totient m : ℝ)

/-- `A(N) = ∑_{q ≤ N} φ*(q)` — the object of N2, at integer argument. -/
def Astar (N : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 N, (ZetaQ.phiStar q : ℝ)

theorem Phi_eq (M : ℕ) : Phi M = ∑ e ∈ Finset.Icc 1 M, mu e * Sid (M / e) := by
  have h1 : Phi M
      = ∑ m ∈ Finset.Icc 1 M, ∑ p ∈ m.divisorsAntidiagonal, mu p.1 * (p.2 : ℝ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
    have h := congrArg (fun z : ℤ => (z : ℝ)) (totient_eq_moebius_conv hm0)
    simpa [mu] using h
  rw [h1, hyperbola M (fun d m => mu d * (m : ℝ))]
  exact Finset.sum_congr rfl fun e _ => by rw [Sid, Finset.mul_sum]

theorem Astar_eq (N : ℕ) : Astar N = ∑ d ∈ Finset.Icc 1 N, mu d * Phi (N / d) := by
  have h1 : Astar N
      = ∑ q ∈ Finset.Icc 1 N,
          ∑ p ∈ q.divisorsAntidiagonal, mu p.1 * (Nat.totient p.2 : ℝ) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have : NeZero q := ⟨by omega⟩
    have hstar := _root_.ZetaQ.phiStar_eq_moebius_sum q
    have hanti : ∑ p ∈ q.divisorsAntidiagonal,
          ArithmeticFunction.moebius p.1 * (Nat.totient p.2 : ℤ)
        = ∑ i ∈ q.divisors, ArithmeticFunction.moebius (q / i) * (Nat.totient i : ℤ) :=
      Nat.sum_divisorsAntidiagonal'
        (fun d m => ArithmeticFunction.moebius d * (Nat.totient m : ℤ))
    have h := congrArg (fun z : ℤ => (z : ℝ)) (hstar.trans hanti.symm)
    simpa [mu] using h
  rw [h1, hyperbola N (fun d m => mu d * (Nat.totient m : ℝ))]
  exact Finset.sum_congr rfl fun d _ => by rw [Phi, Finset.mul_sum]

theorem Sid_eq (K : ℕ) : Sid K = (K:ℝ) * ((K:ℝ) + 1) / 2 := by
  induction K with
  | zero => simp [Sid]
  | succ K ih =>
    have h : Sid (K + 1) = Sid K + ((K:ℝ) + 1) := by
      rw [Sid, Sid, Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
      push_cast
      ring
    rw [h, ih]
    push_cast
    ring

theorem harmonic_bound (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ((d:ℝ))⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have he : ((harmonic N : ℚ) : ℝ) = ∑ d ∈ Finset.Icc 1 N, ((d:ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  linarith [he ▸ h]

/-- `Σ_{d≥1} μ(d)/d² = 1/ζ(2) = 6/π²` — the ONLY analytic input of the whole development. -/
theorem hasSum_mu_sq : HasSum (fun e : ℕ => mu e / (e:ℝ)^2) (6 / Real.pi ^ 2) := by
  have hs : (1:ℝ) < ((2:ℂ)).re := by norm_num
  have hz : LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) 2 = riemannZeta 2 :=
    ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  have hpiC : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hmul' : ((Real.pi : ℂ)^2/6)
      * LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 = 1 := by
    rw [← riemannZeta_two, ← hz]; exact hmul
  have hLmu : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2
      = 6 / (Real.pi:ℂ)^2 := by
    field_simp at hmul' ⊢
    linear_combination hmul'
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hHS : HasSum (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) 2)
      (6/(Real.pi:ℂ)^2) := by
    have h := hsum.LSeriesHasSum
    rwa [hLmu] at h
  have hterm : (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) 2)
      = fun n : ℕ => ((mu n / (n:ℝ)^2 : ℝ) : ℂ) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, mu]
    · rw [LSeries.term_of_ne_zero hn]
      have hcp : ((n:ℂ)) ^ (2:ℂ) = ((n:ℂ))^(2:ℕ) := by
        rw [show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, Complex.cpow_natCast]
      rw [hcp, mu]
      push_cast
      ring
  rw [hterm] at hHS
  have hcast : ((6/Real.pi^2 : ℝ) : ℂ) = 6/(Real.pi:ℂ)^2 := by push_cast; ring
  rw [← hcast] at hHS
  exact Complex.hasSum_ofReal.mp hHS

/-- The truncation error of the `μ/d²` series: `|∑_{e≤M} μ(e)/e² − 6/π²| ≤ 2/M`. -/
theorem mu_partial_tail (M : ℕ) (hM : 1 ≤ M) :
    |(∑ e ∈ Finset.Icc 1 M, mu e / (e:ℝ)^2) - 6/Real.pi^2| ≤ 2/(M:ℝ) := by
  set f : ℕ → ℝ := fun e => mu e / (e:ℝ)^2 with hf
  set P : ℝ := ∑ e ∈ Finset.Icc 1 M, f e with hP
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hrange : ∑ e ∈ Finset.range (M+1), f e = P := by
    have hset : Finset.range (M+1) = insert 0 (Finset.Icc 1 M) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hP, hset, Finset.sum_insert (by simp)]
    simp [hf, mu]
  have hten : Tendsto (fun n => |(∑ e ∈ Finset.range n, f e) - P|) atTop
      (nhds |6/Real.pi^2 - P|) :=
    ((hasSum_mu_sq.tendsto_sum_nat).sub_const P).abs
  have hev : ∀ᶠ n in atTop, |(∑ e ∈ Finset.range n, f e) - P| ≤ 2/(M:ℝ) := by
    filter_upwards [eventually_ge_atTop (M+1)] with n hn
    have hsplit : ∑ e ∈ Finset.range n, f e - P = ∑ e ∈ Finset.Ico (M+1) n, f e := by
      rw [← hrange, Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive f (Nat.zero_le (M+1)) hn]
      ring
    rw [hsplit]
    have hIoo : Finset.Ico (M+1) n = Finset.Ioo M n := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_Ioo]
      omega
    rw [hIoo]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ e ∈ Finset.Ioo M n, |f e| ≤ ((e:ℝ)^2)⁻¹ := by
      intro e he
      have he1 : 1 ≤ e := by
        have := (Finset.mem_Ioo.mp he).1; omega
      have heR : (0:ℝ) < (e:ℝ) := by exact_mod_cast he1
      rw [hf]
      simp only [abs_div, abs_pow, abs_of_pos heR]
      rw [div_eq_mul_inv]
      have := abs_mu_le e
      nlinarith [abs_nonneg (mu e), inv_pos.mpr (pow_pos heR 2)]
    refine le_trans (Finset.sum_le_sum hb) ?_
    refine le_trans (sum_Ioo_inv_sq_le M n) ?_
    rw [div_le_div_iff₀ (by positivity) hMR]
    nlinarith
  exact abs_sub_comm P (6/Real.pi^2) ▸ le_of_tendsto hten hev

/-- The one estimate used twice: if `H(K) = c K² + O(K·E(K))` with `E` monotone, and `a` is
bounded by 1 with `∑ a(e)/e² = L` (truncation error `≤ 2/M`), then
`∑_{d≤N} a(d) H(⌊N/d⌋) = cLN² + O(N(1+log N)(E(N) + 2c))`. -/
theorem convolve_estimate
    (a : ℕ → ℝ) (ha : ∀ e, |a e| ≤ 1) (L : ℝ)
    (htail : ∀ M : ℕ, 1 ≤ M → |(∑ e ∈ Finset.Icc 1 M, a e / (e:ℝ)^2) - L| ≤ 2/(M:ℝ))
    (c : ℝ) (hc : 0 ≤ c) (H : ℕ → ℝ) (E : ℝ → ℝ)
    (hE0 : ∀ y : ℝ, 1 ≤ y → 0 ≤ E y)
    (hEmono : ∀ y z : ℝ, 1 ≤ y → y ≤ z → E y ≤ E z)
    (hH : ∀ K : ℕ, 1 ≤ K → |H K - c * (K:ℝ)^2| ≤ (K:ℝ) * E (K:ℝ))
    (N : ℕ) (hN : 1 ≤ N) :
    |(∑ d ∈ Finset.Icc 1 N, a d * H (N/d)) - c * L * (N:ℝ)^2|
      ≤ (N:ℝ) * (1 + Real.log N) * (E (N:ℝ) + 2*c) + 2*c*(N:ℝ) := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have e1 : ∑ d ∈ Finset.Icc 1 N, a d * (H (N/d) - c * ((N:ℝ)/(d:ℝ))^2)
      = (∑ d ∈ Finset.Icc 1 N, a d * H (N/d))
        - c * (N:ℝ)^2 * (∑ d ∈ Finset.Icc 1 N, a d / (d:ℝ)^2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    field_simp
  have hEc : (0:ℝ) ≤ E (N:ℝ) + 2*c := by linarith [hE0 (N:ℝ) hNR]
  have hT1 : |∑ d ∈ Finset.Icc 1 N, a d * (H (N/d) - c * ((N:ℝ)/(d:ℝ))^2)|
      ≤ (N:ℝ) * (1 + Real.log N) * (E (N:ℝ) + 2*c) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ d ∈ Finset.Icc 1 N,
        |a d * (H (N/d) - c * ((N:ℝ)/(d:ℝ))^2)| ≤ ((N:ℝ)/(d:ℝ)) * (E (N:ℝ) + 2*c) := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have hd0 : 0 < d := hd1
      have hdR1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
      have hdR : (0:ℝ) < (d:ℝ) := by linarith
      set K : ℕ := N / d with hK
      have hK1 : 1 ≤ K := (Nat.one_le_div_iff hd0).mpr hdN
      have hKR : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK1
      have hKy : (K:ℝ) ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
      have hyK : (N:ℝ)/(d:ℝ) < (K:ℝ) + 1 := by
        have h := (Nat.div_lt_iff_lt_mul hd0).mp (show N / d < K + 1 by omega)
        have hR : (N:ℝ) < ((K:ℝ)+1) * (d:ℝ) := by exact_mod_cast h
        rw [div_lt_iff₀ hdR]
        exact hR
      have hyN : (N:ℝ)/(d:ℝ) ≤ (N:ℝ) := by
        rw [div_le_iff₀ hdR]
        nlinarith
      have hy0 : (0:ℝ) < (N:ℝ)/(d:ℝ) := by positivity
      have h1 : |H K - c * (K:ℝ)^2| ≤ ((N:ℝ)/(d:ℝ)) * E (N:ℝ) := by
        refine (hH K hK1).trans ?_
        have hm := hEmono (K:ℝ) (N:ℝ) hKR (le_trans hKy hyN)
        nlinarith [hE0 (K:ℝ) hKR, hE0 (N:ℝ) hNR]
      have h2 : |c * (K:ℝ)^2 - c * ((N:ℝ)/(d:ℝ))^2| ≤ ((N:ℝ)/(d:ℝ)) * (2*c) := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hc]
        have hin : |(K:ℝ)^2 - ((N:ℝ)/(d:ℝ))^2| ≤ 2 * ((N:ℝ)/(d:ℝ)) := by
          rw [abs_le]
          constructor <;> nlinarith
        nlinarith [abs_nonneg ((K:ℝ)^2 - ((N:ℝ)/(d:ℝ))^2)]
      have h3 : |H K - c * ((N:ℝ)/(d:ℝ))^2| ≤ ((N:ℝ)/(d:ℝ)) * (E (N:ℝ) + 2*c) :=
        calc |H K - c * ((N:ℝ)/(d:ℝ))^2|
            ≤ |H K - c*(K:ℝ)^2| + |c*(K:ℝ)^2 - c*((N:ℝ)/(d:ℝ))^2| := abs_sub_le _ _ _
          _ ≤ ((N:ℝ)/(d:ℝ)) * E (N:ℝ) + ((N:ℝ)/(d:ℝ)) * (2*c) := add_le_add h1 h2
          _ = ((N:ℝ)/(d:ℝ)) * (E (N:ℝ) + 2*c) := by ring
      rw [abs_mul]
      calc |a d| * |H K - c * ((N:ℝ)/(d:ℝ))^2|
          ≤ 1 * (((N:ℝ)/(d:ℝ)) * (E (N:ℝ) + 2*c)) :=
            mul_le_mul (ha d) h3 (abs_nonneg _) (by norm_num)
        _ = ((N:ℝ)/(d:ℝ)) * (E (N:ℝ) + 2*c) := one_mul _
    refine (Finset.sum_le_sum hpt).trans ?_
    have hsum : ∑ d ∈ Finset.Icc 1 N, ((N:ℝ)/(d:ℝ)) * (E (N:ℝ) + 2*c)
        = (N:ℝ) * (E (N:ℝ) + 2*c) * ∑ d ∈ Finset.Icc 1 N, ((d:ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [div_eq_mul_inv]; ring
    rw [hsum]
    have hh := harmonic_bound N
    have hcoef : (0:ℝ) ≤ (N:ℝ) * (E (N:ℝ) + 2*c) := mul_nonneg hNpos.le hEc
    calc (N:ℝ) * (E (N:ℝ) + 2*c) * (∑ d ∈ Finset.Icc 1 N, ((d:ℝ))⁻¹)
        ≤ (N:ℝ) * (E (N:ℝ) + 2*c) * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left hh hcoef
      _ = (N:ℝ) * (1 + Real.log N) * (E (N:ℝ) + 2*c) := by ring
  have hT2 : |c * (N:ℝ)^2 * ((∑ d ∈ Finset.Icc 1 N, a d / (d:ℝ)^2) - L)| ≤ 2*c*(N:ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c * (N:ℝ)^2)]
    have ht := htail N hN
    have h2 : c * (N:ℝ)^2 * (2/(N:ℝ)) = 2*c*(N:ℝ) := by field_simp
    calc c*(N:ℝ)^2 * |(∑ d ∈ Finset.Icc 1 N, a d / (d:ℝ)^2) - L|
        ≤ c*(N:ℝ)^2 * (2/(N:ℝ)) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = 2*c*(N:ℝ) := h2
  have hfinal : (∑ d ∈ Finset.Icc 1 N, a d * H (N/d)) - c * L * (N:ℝ)^2
      = (∑ d ∈ Finset.Icc 1 N, a d * (H (N/d) - c * ((N:ℝ)/(d:ℝ))^2))
        + c * (N:ℝ)^2 * ((∑ d ∈ Finset.Icc 1 N, a d / (d:ℝ)^2) - L) := by
    rw [e1]; ring
  rw [hfinal]
  exact (abs_add_le _ _).trans (add_le_add hT1 hT2)

/-- `Σ_{m ≤ M} φ(m) = (3/π²)M² + O(M log M)`, explicit. -/
theorem Phi_bound (M : ℕ) (hM : 1 ≤ M) :
    |Phi M - (3/Real.pi^2) * (M:ℝ)^2| ≤ (M:ℝ) * (3 * (1 + Real.log M)) := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hlogM : (0:ℝ) ≤ Real.log M := Real.log_nonneg hMR
  have hkey := convolve_estimate mu abs_mu_le (6/Real.pi^2) mu_partial_tail
    (1/2 : ℝ) (by norm_num) Sid (fun _ => (1/2 : ℝ))
    (fun _ _ => by norm_num) (fun _ _ _ _ => le_refl _)
    (fun K hK => by
      have hKR : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
      rw [Sid_eq]
      have h : (K:ℝ) * ((K:ℝ) + 1) / 2 - 1/2 * (K:ℝ)^2 = (K:ℝ)/2 := by ring
      rw [h, abs_of_nonneg (by linarith)]
      linarith)
    M hM
  rw [← Phi_eq M] at hkey
  have hc : (1/2 : ℝ) * (6/Real.pi^2) = 3/Real.pi^2 := by ring
  rw [hc] at hkey
  refine hkey.trans ?_
  nlinarith [hMR, hlogM]

/-- **N2 at integer argument**: `Σ_{q ≤ N} φ*(q) = (18/π⁴)N² + O(N log²N)`, explicit constant. -/
theorem Astar_bound (N : ℕ) (hN : 1 ≤ N) :
    |Astar N - (18/Real.pi^4) * (N:ℝ)^2| ≤ 5 * (N:ℝ) * (1 + Real.log N)^2 := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNR
  have hpi2 : (0:ℝ) < Real.pi^2 := by positivity
  have hkey := convolve_estimate mu abs_mu_le (6/Real.pi^2) mu_partial_tail
    (3/Real.pi^2) (by positivity) Phi (fun y => 3 * (1 + Real.log y))
    (fun y hy => by
      have : (0:ℝ) ≤ Real.log y := Real.log_nonneg hy
      linarith)
    (fun y z hy hyz => by
      have : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyz
      linarith)
    (fun K hK => Phi_bound K hK) N hN
  rw [← Astar_eq N] at hkey
  have hc : (3/Real.pi^2) * (6/Real.pi^2) = 18/Real.pi^4 := by
    field_simp
    ring
  rw [hc] at hkey
  have hsx : 2 * (3/Real.pi^2) = 6/Real.pi^2 := by ring
  rw [hsx] at hkey
  refine hkey.trans ?_
  have hsmall : (6:ℝ)/Real.pi^2 ≤ 1 := by
    rw [div_le_one hpi2]
    nlinarith [Real.pi_gt_three]
  have hpos : (0:ℝ) ≤ 6/Real.pi^2 := by positivity
  set t : ℝ := 1 + Real.log (N:ℝ) with ht
  set sc : ℝ := 6/Real.pi^2 with hsc
  have ht1 : (1:ℝ) ≤ t := by rw [ht]; linarith
  have hscal : (0:ℝ) ≤ 2*t^2 - sc*t - sc := by
    nlinarith [ht1, hsmall, hpos, sq_nonneg (t-1)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ)) hscal]

/-- The real-variable `O`-form, with an explicit constant 22 valid for every `x ≥ 3`. -/
theorem sum_phiStar_bigO :
    (fun x : ℝ => (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ)) - (18 / Real.pi ^ 4) * x ^ 2)
      =O[atTop] (fun x : ℝ => x * Real.log x ^ 2) := by
  refine Asymptotics.IsBigO.of_bound 22 ?_
  filter_upwards [eventually_ge_atTop (3:ℝ)] with x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hlog1 : (1:ℝ) < Real.log x := by
    have h3 : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hx)
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr (by linarith)
  have hNx : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
  have hNR1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hAb := Astar_bound N hN1
  have hlogN : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hNx
  have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg hNR1
  have hpi4 : (0:ℝ) < Real.pi ^ 4 := by positivity
  have h18 : (0:ℝ) < 18 / Real.pi ^ 4 := by positivity
  have h18' : (18:ℝ) / Real.pi ^ 4 ≤ 1 := by
    rw [div_le_one hpi4]
    have h1 : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h2 : (9:ℝ) < Real.pi ^ 2 := by nlinarith
    have h3 : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
    rw [h3]
    nlinarith [h2]
  have hgap : |(18 / Real.pi ^ 4) * (N:ℝ)^2 - (18/Real.pi^4) * x^2| ≤ 2 * x := by
    rw [← mul_sub, abs_mul, abs_of_pos h18]
    have hd : |(N:ℝ)^2 - x^2| ≤ 2 * x := by
      rw [abs_le]
      constructor <;> nlinarith
    nlinarith [abs_nonneg ((N:ℝ)^2 - x^2)]
  have hsplit : |(∑ q ∈ Finset.Icc 1 N, (ZetaQ.phiStar q : ℝ)) - (18/Real.pi^4) * x^2|
      ≤ 5 * (N:ℝ) * (1 + Real.log N)^2 + 2 * x := by
    have h := abs_sub_le (Astar N) ((18/Real.pi^4) * (N:ℝ)^2) ((18/Real.pi^4) * x^2)
    exact le_trans h (add_le_add hAb hgap)
  have hmain : 5 * (N:ℝ) * (1 + Real.log N)^2 + 2 * x ≤ 22 * (x * Real.log x ^ 2) := by
    have hA : (1 + Real.log (N:ℝ))^2 ≤ (2 * Real.log x)^2 := by
      have h1 : (0:ℝ) ≤ 1 + Real.log (N:ℝ) := by linarith
      have h2 : 1 + Real.log (N:ℝ) ≤ 2 * Real.log x := by linarith
      nlinarith
    have hB : 5 * (N:ℝ) * (1 + Real.log N)^2 ≤ 20 * (x * Real.log x ^ 2) := by
      have h3 : (0:ℝ) ≤ (1 + Real.log (N:ℝ))^2 := sq_nonneg _
      nlinarith [hA, hNx, hNR1]
    have hL : (1:ℝ) ≤ Real.log x ^ 2 := by nlinarith
    have hC : 2 * x ≤ 2 * (x * Real.log x ^ 2) := by nlinarith [hL, hx0]
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < x * Real.log x ^ 2)]
  exact le_trans hsplit hmain

/-! ### N6's engine — Abel summation of `log q` against N2

`Alog N = Σ_{q≤N} φ*(q) log q` is summed by parts against `Astar` (`N2.abel`), the resulting
`Σ_{q<N} Astar(q)(log(q+1) − log q)` is split into its main part `c·Σ q²(log(q+1) − log q)`
(compared to `Σ (q + ½) = (N²−1)/2` by the elementary two-sided bound
`1/(q+1) ≤ log(1 + 1/q) ≤ 1/q`, no integrals) and an error controlled by `N2.Astar_bound`.
The output is `N2.Alog_bound`; `N2.avgLog_limit` then divides by `Astar` and lets `⌊x⌋ → x`. -/

def Alog (N : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 N, (ZetaQ.phiStar q : ℝ) * Real.log q

theorem abel (N : ℕ) :
    Alog N = Astar N * Real.log N
      - ∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q) := by
  induction N with
  | zero => simp [Alog, Astar]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [Alog, Astar]
    · have h1 : Alog (N+1) = Alog N + (ZetaQ.phiStar (N+1) : ℝ) * Real.log ((N:ℝ)+1) := by
        rw [Alog, Alog, Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
        push_cast
        ring
      have h2 : Astar (N+1) = Astar N + (ZetaQ.phiStar (N+1) : ℝ) := by
        rw [Astar, Astar, Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
      have h3 : ∑ q ∈ Finset.Ico 1 (N+1), Astar q * (Real.log ((q:ℝ)+1) - Real.log q)
          = (∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
            + Astar N * (Real.log ((N:ℝ)+1) - Real.log N) :=
        Finset.sum_Ico_succ_top hN _
      rw [h1, ih, h2, h3]
      push_cast
      ring

/-- `1/(q+1) ≤ log(q+1) − log q ≤ 1/q`. -/
theorem logstep_bounds (q : ℕ) (hq : 1 ≤ q) :
    1/((q:ℝ)+1) ≤ Real.log ((q:ℝ)+1) - Real.log q
      ∧ Real.log ((q:ℝ)+1) - Real.log q ≤ 1/(q:ℝ) := by
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  constructor
  · have h := Real.log_le_sub_one_of_pos (x := (q:ℝ)/((q:ℝ)+1)) (by positivity)
    have he : (q:ℝ)/((q:ℝ)+1) - 1 = -(1/((q:ℝ)+1)) := by field_simp; ring
    rw [he, Real.log_div (by positivity) (by positivity)] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (x := ((q:ℝ)+1)/(q:ℝ)) (by positivity)
    have he : ((q:ℝ)+1)/(q:ℝ) - 1 = 1/(q:ℝ) := by field_simp; ring
    rw [he, Real.log_div (by positivity) (by positivity)] at h
    linarith

theorem logstep_sq (q : ℕ) (hq : 1 ≤ q) :
    |(q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q) - ((q:ℝ) + 1/2)| ≤ 3/2 := by
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  obtain ⟨hlo, hhi⟩ := logstep_bounds q hq
  have hu : (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q) ≤ (q:ℝ) := by
    have := mul_le_mul_of_nonneg_left hhi (by positivity : (0:ℝ) ≤ (q:ℝ)^2)
    calc (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q) ≤ (q:ℝ)^2 * (1/(q:ℝ)) := this
      _ = (q:ℝ) := by field_simp
  have hl : (q:ℝ) - 1 ≤ (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q) := by
    have h := mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ) ≤ (q:ℝ)^2)
    have he : (q:ℝ)^2 * (1/((q:ℝ)+1)) = (q:ℝ) - (q:ℝ)/((q:ℝ)+1) := by field_simp; ring
    have hfrac : (q:ℝ)/((q:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    rw [he] at h
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem sum_arith (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Finset.Ico 1 N, ((q:ℝ) + 1/2) = ((N:ℝ)^2 - 1)/2 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    push_cast
    ring

theorem sum_sq_logstep (N : ℕ) (hN : 1 ≤ N) :
    |(∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q)) - ((N:ℝ)^2-1)/2|
      ≤ 2 * (N:ℝ) := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  rw [← sum_arith N hN, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ q ∈ Finset.Ico 1 N,
      |(q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q) - ((q:ℝ) + 1/2)| ≤ 3/2 := by
    intro q hq
    exact logstep_sq q (Finset.mem_Ico.mp hq).1
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ (N:ℝ) := by
    have : (N - 1 : ℕ) ≤ N := Nat.sub_le _ _
    exact_mod_cast this
  nlinarith

theorem sum_logsq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Finset.Ico 1 N, (1 + Real.log q)^2 ≤ (N:ℝ) * (1 + Real.log N)^2 := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hb : ∀ q ∈ Finset.Ico 1 N, (1 + Real.log q)^2 ≤ (1 + Real.log N)^2 := by
    intro q hq
    obtain ⟨hq1, hqN⟩ := Finset.mem_Ico.mp hq
    have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
    have hqN' : (q:ℝ) ≤ (N:ℝ) := by exact_mod_cast hqN.le
    have h1 : (0:ℝ) ≤ Real.log q := Real.log_nonneg hqR
    have h2 : Real.log q ≤ Real.log N := Real.log_le_log (by linarith) hqN'
    nlinarith
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ (N:ℝ) := by
    have : (N - 1 : ℕ) ≤ N := Nat.sub_le _ _
    exact_mod_cast this
  nlinarith [sq_nonneg (1 + Real.log (N:ℝ)), Real.log_nonneg hNR]

theorem Alog_bound (N : ℕ) (hN : 1 ≤ N) :
    |Alog N - (18/Real.pi^4) * (N:ℝ)^2 * (Real.log N - 1/2)|
      ≤ 13 * (N:ℝ) * (1 + Real.log N)^3 := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNR
  set c : ℝ := 18/Real.pi^4 with hc
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  have hcle : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    have h1 : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h2 : (9:ℝ) < Real.pi ^ 2 := by nlinarith
    have h3 : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
    rw [h3]; nlinarith [h2]
  -- the tail sum
  have hsum : |(∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
      - c * ((N:ℝ)^2-1)/2| ≤ 2*c*(N:ℝ) + 5*(N:ℝ)*(1 + Real.log N)^2 := by
    have hdec : ∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q)
        = c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q))
          + ∑ q ∈ Finset.Ico 1 N,
              (Astar q - c * (q:ℝ)^2) * (Real.log ((q:ℝ)+1) - Real.log q) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hE : |∑ q ∈ Finset.Ico 1 N,
        (Astar q - c * (q:ℝ)^2) * (Real.log ((q:ℝ)+1) - Real.log q)|
        ≤ 5*(N:ℝ)*(1 + Real.log N)^2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ q ∈ Finset.Ico 1 N,
          |(Astar q - c * (q:ℝ)^2) * (Real.log ((q:ℝ)+1) - Real.log q)|
            ≤ 5 * (1 + Real.log q)^2 := by
        intro q hq
        obtain ⟨hq1, _⟩ := Finset.mem_Ico.mp hq
        have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
        have hq0 : (0:ℝ) < (q:ℝ) := by linarith
        obtain ⟨hlo, hhi⟩ := logstep_bounds q hq1
        have h5 : |Astar q - c * (q:ℝ)^2| ≤ 5 * (q:ℝ) * (1 + Real.log q)^2 := by
          rw [hc]; exact Astar_bound q hq1
        have hp : (0:ℝ) < 1/((q:ℝ)+1) := by positivity
        have hstep0 : (0:ℝ) ≤ Real.log ((q:ℝ)+1) - Real.log q := by linarith
        rw [abs_mul, abs_of_nonneg hstep0]
        have hfin : (5 * (q:ℝ) * (1 + Real.log q)^2) * (1/(q:ℝ))
            = 5 * (1 + Real.log q)^2 := by field_simp
        calc |Astar q - c * (q:ℝ)^2| * (Real.log ((q:ℝ)+1) - Real.log q)
            ≤ (5 * (q:ℝ) * (1 + Real.log q)^2) * (1/(q:ℝ)) :=
              mul_le_mul h5 hhi hstep0 (by positivity)
          _ = 5 * (1 + Real.log q)^2 := hfin
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.mul_sum]
      have := sum_logsq_le N hN
      linarith
    have hM := sum_sq_logstep N hN
    rw [hdec]
    have hMc : |c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q))
        - c * ((N:ℝ)^2-1)/2| ≤ 2*c*(N:ℝ) := by
      have he : c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q))
          - c * ((N:ℝ)^2-1)/2
          = c * ((∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q))
              - ((N:ℝ)^2-1)/2) := by ring
      rw [he, abs_mul, abs_of_pos hcpos]
      nlinarith [hM, abs_nonneg ((∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 *
        (Real.log ((q:ℝ)+1) - Real.log q)) - ((N:ℝ)^2-1)/2)]
    have htri := abs_add_le
      (c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q))
        - c * ((N:ℝ)^2-1)/2)
      (∑ q ∈ Finset.Ico 1 N, (Astar q - c * (q:ℝ)^2) * (Real.log ((q:ℝ)+1) - Real.log q))
    have hrw : c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q))
        + (∑ q ∈ Finset.Ico 1 N, (Astar q - c * (q:ℝ)^2) * (Real.log ((q:ℝ)+1) - Real.log q))
        - c * ((N:ℝ)^2-1)/2
        = (c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log ((q:ℝ)+1) - Real.log q))
            - c * ((N:ℝ)^2-1)/2)
          + (∑ q ∈ Finset.Ico 1 N,
              (Astar q - c * (q:ℝ)^2) * (Real.log ((q:ℝ)+1) - Real.log q)) := by ring
    rw [hrw]
    linarith [htri, hMc, hE]
  have hAN : |Astar N - c * (N:ℝ)^2| ≤ 5 * (N:ℝ) * (1 + Real.log N)^2 := by
    rw [hc]; exact Astar_bound N hN
  rw [abel N]
  have hexp : Astar N * Real.log N
      - (∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
      - c * (N:ℝ)^2 * (Real.log N - 1/2)
      = (Astar N - c * (N:ℝ)^2) * Real.log N
        - ((∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
            - c * ((N:ℝ)^2-1)/2)
        + c/2 := by ring
  rw [hexp]
  have hA1 : |(Astar N - c * (N:ℝ)^2) * Real.log N|
      ≤ 5*(N:ℝ)*(1 + Real.log N)^2 * Real.log N := by
    rw [abs_mul, abs_of_nonneg hlogN]
    exact mul_le_mul_of_nonneg_right hAN hlogN
  have ht1 := abs_add_le ((Astar N - c * (N:ℝ)^2) * Real.log N)
    (-(((∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
        - c * ((N:ℝ)^2-1)/2)))
  have ht2 := abs_add_le
    ((Astar N - c * (N:ℝ)^2) * Real.log N
      + -(((∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
        - c * ((N:ℝ)^2-1)/2))) (c/2)
  have hrw2 : (Astar N - c * (N:ℝ)^2) * Real.log N
      - ((∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
          - c * ((N:ℝ)^2-1)/2) + c/2
      = ((Astar N - c * (N:ℝ)^2) * Real.log N
          + -(((∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
            - c * ((N:ℝ)^2-1)/2))) + (c/2) := by ring
  rw [hrw2]
  have habs1 : |-(((∑ q ∈ Finset.Ico 1 N, Astar q * (Real.log ((q:ℝ)+1) - Real.log q))
      - c * ((N:ℝ)^2-1)/2))| ≤ 2*c*(N:ℝ) + 5*(N:ℝ)*(1 + Real.log N)^2 := by
    rw [abs_neg]; exact hsum
  have habs2 : |c/2| = c/2 := abs_of_pos (by linarith)
  -- final numeric assembly
  have hL1 : (1:ℝ) ≤ 1 + Real.log (N:ℝ) := by linarith
  have hcube : (1:ℝ) ≤ (1 + Real.log (N:ℝ))^3 := by
    nlinarith [hL1, sq_nonneg (1 + Real.log (N:ℝ))]
  have hNP : (N:ℝ) ≤ (N:ℝ) * (1 + Real.log (N:ℝ))^3 :=
    le_mul_of_one_le_right (by linarith) hcube
  have hsq3 : (1 + Real.log (N:ℝ))^2 * Real.log (N:ℝ) ≤ (1 + Real.log (N:ℝ))^3 := by
    nlinarith [sq_nonneg (1 + Real.log (N:ℝ)), hlogN]
  have hsq2 : (1 + Real.log (N:ℝ))^2 ≤ (1 + Real.log (N:ℝ))^3 := by
    nlinarith [sq_nonneg (1 + Real.log (N:ℝ)), hlogN]
  have hkey : 5*(N:ℝ)*(1 + Real.log N)^2 * Real.log N
      + (2*c*(N:ℝ) + 5*(N:ℝ)*(1 + Real.log N)^2) + c/2
      ≤ 13 * (N:ℝ) * (1 + Real.log N)^3 := by
    have e1 : 5*(N:ℝ)*(1 + Real.log N)^2 * Real.log N
        ≤ 5*((N:ℝ)*(1 + Real.log N)^3) := by nlinarith [hsq3, hNR]
    have e3 : 5*(N:ℝ)*(1 + Real.log N)^2 ≤ 5*((N:ℝ)*(1 + Real.log N)^3) := by
      nlinarith [hsq2, hNR]
    have e2 : 2*c*(N:ℝ) ≤ 2*((N:ℝ)*(1 + Real.log N)^3) := by
      nlinarith [hNP, hcle, hNR]
    have e4 : c/2 ≤ (N:ℝ)*(1 + Real.log N)^3 := by linarith [hNP, hNR, hcle]
    linarith
  linarith [ht1, ht2, hA1, habs1, habs2, hkey]

set_option maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
theorem avgLog_limit :
    Tendsto (fun x : ℝ => Alog ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x) atTop (nhds (-(1:ℝ)/2)) := by
  set c : ℝ := 18/Real.pi^4 with hc
  clear_value c
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  have hcle : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    have h1 : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h2 : (9:ℝ) < Real.pi ^ 2 := by nlinarith
    have h3 : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
    rw [h3]; nlinarith [h2]
  have hpi4 : Real.pi ^ 4 ≤ 100 := by
    have h1 : Real.pi < 3.15 := Real.pi_lt_d2
    have h2 : (0:ℝ) < Real.pi := Real.pi_pos
    have hsq : Real.pi ^ 2 < 9.9225 := by nlinarith
    have h3 : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
    rw [h3]
    nlinarith [hsq, sq_nonneg (Real.pi ^ 2)]
  have hclow : (18:ℝ)/100 ≤ c := by
    rw [hc, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [hpi4]
  have hg : Tendsto (fun x : ℝ => 4000 * (Real.log x ^ 3 / x)) atTop (nhds 0) := by
    have h3 : Tendsto (fun x : ℝ => Real.log x ^ 3 / x) atTop (nhds 0) := by
      simpa using (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero
    simpa using h3.const_mul (4000:ℝ)
  have hlim2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hev0 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 / x < c/80 :=
    hlim2.eventually_lt_const (by positivity)
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖Alog ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x + 1/2‖ ≤ 4000 * (Real.log x ^ 3 / x) := by
    filter_upwards [eventually_ge_atTop (3:ℝ), hev0] with x hx hxc
    have hx0 : (0:ℝ) < x := by linarith
    have hlog1 : (1:ℝ) < Real.log x := by
      have h3 : (1:ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hx)
    have hp1 : (0:ℝ) < Real.log x ^ 3 := by positivity
    set N : ℕ := ⌊x⌋₊ with hNdef
    have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr (by linarith)
    have hNx : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
    have hxN : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
    have hNR1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    clear_value N
    have hx2N : x ≤ 2 * (N:ℝ) := by linarith
    have hlogN : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hNx
    have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg hNR1
    have hAN : |Astar N - c * (N:ℝ)^2| ≤ 5 * (N:ℝ) * (1 + Real.log N)^2 := by
      rw [hc]; exact Astar_bound N hN1
    have hAlog : |Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2)|
        ≤ 13 * (N:ℝ) * (1 + Real.log N)^3 := by
      rw [hc]; exact Alog_bound N hN1
    have hpow2 : (1 + Real.log (N:ℝ))^2 ≤ (1 + Real.log x)^2 := by
      gcongr <;> linarith
    have hpow3 : (1 + Real.log (N:ℝ))^3 ≤ (1 + Real.log x)^3 := by
      gcongr <;> linarith
    have hsmall : 5 * (1 + Real.log (N:ℝ))^2 ≤ (c/2) * (N:ℝ) := by
      have h1 : (1 + Real.log (N:ℝ))^2 ≤ (2 * Real.log x)^2 := by
        have hb : 1 + Real.log (N:ℝ) ≤ 2 * Real.log x := by linarith
        nlinarith [hlogN0]
      have h2 : (20:ℝ) * Real.log x ^ 2 ≤ (c/4) * x := by
        rw [div_lt_iff₀ hx0] at hxc
        nlinarith
      nlinarith [h1, h2, hx2N, hcpos]
    have hDlow : (c/2) * (N:ℝ)^2 ≤ Astar N := by
      have h := (abs_le.mp hAN).1
      nlinarith [hsmall, hNR1]
    have hDlow2 : (9/100 : ℝ) * (N:ℝ)^2 ≤ Astar N := by
      nlinarith [hDlow, hclow, sq_nonneg ((N:ℝ))]
    have hDpos : (0:ℝ) < Astar N := by nlinarith [hDlow2, hNR1]
    have hDne : Astar N ≠ 0 := ne_of_gt hDpos
    have hlogdiff : Real.log x - Real.log (N:ℝ) ≤ 1/(N:ℝ) := by
      have hle : Real.log x ≤ Real.log ((N:ℝ)+1) := Real.log_le_log hx0 hxN.le
      have h := Real.log_le_sub_one_of_pos (x := ((N:ℝ)+1)/(N:ℝ)) (by positivity)
      have he : ((N:ℝ)+1)/(N:ℝ) - 1 = 1/(N:ℝ) := by field_simp; ring
      rw [he, Real.log_div (by positivity) (by positivity)] at h
      linarith
    have hcube1 : (1:ℝ) ≤ (1 + Real.log x)^3 := by nlinarith [hlog1]
    have hNcube : (N:ℝ) ≤ (N:ℝ) * (1 + Real.log x)^3 :=
      le_mul_of_one_le_right (by linarith) hcube1
    have hnum : |Alog N - (Real.log x - 1/2) * Astar N| ≤ 19 * (N:ℝ) * (1 + Real.log x)^3 := by
      have hb2 : |c * (N:ℝ)^2 * (Real.log (N:ℝ) - Real.log x)| ≤ (N:ℝ) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c * (N:ℝ)^2)]
        have habs : |Real.log (N:ℝ) - Real.log x| ≤ 1/(N:ℝ) := by
          rw [abs_le]
          refine ⟨by linarith, ?_⟩
          have hpp : (0:ℝ) < 1/(N:ℝ) := by positivity
          linarith
        have hmul := mul_le_mul_of_nonneg_left habs (by positivity : (0:ℝ) ≤ c * (N:ℝ)^2)
        have he : c * (N:ℝ)^2 * (1/(N:ℝ)) = c * (N:ℝ) := by field_simp
        rw [he] at hmul
        nlinarith [hcle, hNR1]
      have hb3 : |(-((Real.log x - 1/2) * (Astar N - c * (N:ℝ)^2)))|
          ≤ 5 * (N:ℝ) * (1 + Real.log x)^3 := by
        rw [abs_neg, abs_mul]
        have h1 : |Real.log x - 1/2| ≤ 1 + Real.log x := by
          rw [abs_le]; constructor <;> linarith
        have h2 : 5 * (N:ℝ) * (1 + Real.log N)^2 ≤ 5 * (N:ℝ) * (1 + Real.log x)^2 :=
          mul_le_mul_of_nonneg_left hpow2 (by positivity)
        calc |Real.log x - 1/2| * |Astar N - c * (N:ℝ)^2|
            ≤ (1 + Real.log x) * (5 * (N:ℝ) * (1 + Real.log x)^2) :=
              mul_le_mul h1 (le_trans hAN h2) (abs_nonneg _) (by linarith)
          _ = 5 * (N:ℝ) * (1 + Real.log x)^3 := by ring
      have hb1 : 13 * (N:ℝ) * (1 + Real.log N)^3 ≤ 13 * (N:ℝ) * (1 + Real.log x)^3 :=
        mul_le_mul_of_nonneg_left hpow3 (by positivity)
      have hre : Alog N - (Real.log x - 1/2) * Astar N
          = ((Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2))
              + (c * (N:ℝ)^2 * (Real.log (N:ℝ) - Real.log x)))
            + (-((Real.log x - 1/2) * (Astar N - c * (N:ℝ)^2))) := by ring
      rw [hre]
      have t1 := abs_add_le (Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2))
        (c * (N:ℝ)^2 * (Real.log (N:ℝ) - Real.log x))
      have t2 := abs_add_le ((Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2))
          + (c * (N:ℝ)^2 * (Real.log (N:ℝ) - Real.log x)))
        (-((Real.log x - 1/2) * (Astar N - c * (N:ℝ)^2)))
      linarith [t1, t2, hAlog, hb1, hb2, hb3, hNcube]
    have heq : Alog N / Astar N - Real.log x + 1/2
        = (Alog N - (Real.log x - 1/2) * Astar N) / Astar N := by
      field_simp
      ring
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    have hxlog : (1 + Real.log x)^3 ≤ 8 * Real.log x ^ 3 := by nlinarith [hlog1]
    have hstep : 19 * (N:ℝ) * (1 + Real.log x)^3
        ≤ 4000 * (Real.log x ^ 3 / x) * ((9/100 : ℝ) * (N:ℝ)^2) := by
      have hrhs : 4000 * (Real.log x ^ 3 / x) * ((9/100 : ℝ) * (N:ℝ)^2)
          = 360 * Real.log x ^ 3 * (N:ℝ)^2 / x := by
        field_simp
        ring
      rw [hrhs, le_div_iff₀ hx0]
      calc 19 * (N:ℝ) * (1 + Real.log x)^3 * x
          ≤ 19 * (N:ℝ) * (8 * Real.log x ^ 3) * x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hxlog (by positivity)) hx0.le
        _ = 152 * (N:ℝ) * Real.log x ^ 3 * x := by ring
        _ ≤ 152 * (N:ℝ) * Real.log x ^ 3 * (2 * (N:ℝ)) :=
            mul_le_mul_of_nonneg_left hx2N (by positivity)
        _ = 304 * Real.log x ^ 3 * (N:ℝ)^2 := by ring
        _ ≤ 360 * Real.log x ^ 3 * (N:ℝ)^2 := by
            nlinarith [mul_nonneg hp1.le (sq_nonneg ((N:ℝ)))]
    have hmono : 4000 * (Real.log x ^ 3 / x) * ((9/100 : ℝ) * (N:ℝ)^2)
        ≤ 4000 * (Real.log x ^ 3 / x) * Astar N :=
      mul_le_mul_of_nonneg_left hDlow2 (by positivity)
    linarith [hnum, hstep, hmono]
  have hzero : Tendsto (fun x : ℝ => Alog ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x + 1/2) atTop (nhds 0) :=
    squeeze_zero_norm' hbound hg
  have h := hzero.sub_const (1/2)
  have hfun : (fun x : ℝ => Alog ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x + 1/2 - 1/2)
      = fun x : ℝ => Alog ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x := by
    funext x; ring
  rw [hfun] at h
  have hv : (0:ℝ) - 1/2 = -(1:ℝ)/2 := by norm_num
  rwa [hv] at h


/-! ### The SECOND logarithmic moment — `Σ_{q≤N} φ*(q)(log q)²`

Exactly the shape of `Alog_bound`, one level up: a second Abel summation, now against
`Alog_bound` instead of `Astar_bound`. The main term `Σ_{q<N} q²(log q − ½)(log(q+1) − log q)`
is compared to the telescoping sum of `Ψ(t) = t²log t/2 − t²/2` (whose derivative is
`t(log t − ½)`) by the SAME elementary two-sided bound `1/(q+1) ≤ log(1+1/q) ≤ 1/q` — no
integrals anywhere. Output: `Alog2_bound`,
`|Σ_{q≤N} φ*(q)(log q)² − (18/π⁴)N²((log N)² − log N + ½)| ≤ 30N(1 + log N)⁴`. -/

/-- `A₂(N) = Σ_{q ≤ N} φ*(q)(log q)²` — the second logarithmic moment at integer argument. -/
def Alog2 (N : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 N, (ZetaQ.phiStar q : ℝ) * Real.log q ^ 2

/-- Abel summation of `(log q)²` against the FIRST moment `Alog`. -/
theorem abel2 (N : ℕ) :
    Alog2 N = Alog N * Real.log N
      - ∑ q ∈ Finset.Ico 1 N, Alog q * (Real.log ((q:ℝ)+1) - Real.log q) := by
  induction N with
  | zero => simp [Alog2, Alog]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [Alog2, Alog]
    · have h1 : Alog2 (N+1)
          = Alog2 N + (ZetaQ.phiStar (N+1) : ℝ) * Real.log ((N:ℝ)+1) ^ 2 := by
        rw [Alog2, Alog2, Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
        push_cast
        ring
      have h2 : Alog (N+1) = Alog N + (ZetaQ.phiStar (N+1) : ℝ) * Real.log ((N:ℝ)+1) := by
        rw [Alog, Alog, Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
        push_cast
        ring
      have h3 : ∑ q ∈ Finset.Ico 1 (N+1), Alog q * (Real.log ((q:ℝ)+1) - Real.log q)
          = (∑ q ∈ Finset.Ico 1 N, Alog q * (Real.log ((q:ℝ)+1) - Real.log q))
            + Alog N * (Real.log ((N:ℝ)+1) - Real.log N) :=
        Finset.sum_Ico_succ_top hN _
      rw [h1, ih, h2, h3]
      push_cast
      ring

/-- `Ψ(t) = t²log t/2 − t²/2`: the elementary antiderivative of `t(log t − ½)`, used purely as
a TELESCOPING comparison sequence (no integral is taken). -/
def Psi (t : ℝ) : ℝ := t^2 * Real.log t / 2 - t^2 / 2

theorem sum_Psi_telescope (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Finset.Ico 1 N, (Psi ((q:ℝ)+1) - Psi (q:ℝ)) = Psi (N:ℝ) + 1/2 := by
  induction N, hN using Nat.le_induction with
  | base => simp [Psi]
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    push_cast
    ring

/-- The per-term comparison: `q²(log q − ½)(log(q+1) − log q)` differs from `Ψ(q+1) − Ψ(q)` by
at most `2(1 + log q)`. Both `1/(q+1) ≤ log(q+1) − log q ≤ 1/q` bounds are used. -/
theorem Psi_step (q : ℕ) (hq : 1 ≤ q) :
    |(q:ℝ)^2 * (Real.log q - 1/2) * (Real.log ((q:ℝ)+1) - Real.log q)
        - (Psi ((q:ℝ)+1) - Psi (q:ℝ))| ≤ 2 * (1 + Real.log q) := by
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hlq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hqR
  obtain ⟨hlo, hhi⟩ := logstep_bounds q hq
  have hA := logstep_sq q hq
  set s : ℝ := Real.log ((q:ℝ)+1) - Real.log q with hs
  have hB1 : (q:ℝ) + 1 ≤ ((q:ℝ)+1)^2 * s := by
    have hm := mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ) ≤ ((q:ℝ)+1)^2)
    have he : ((q:ℝ)+1)^2 * (1/((q:ℝ)+1)) = (q:ℝ) + 1 := by field_simp
    rw [he] at hm
    exact hm
  have hB2 : ((q:ℝ)+1)^2 * s ≤ (q:ℝ) + 3 := by
    have hm := mul_le_mul_of_nonneg_left hhi (by positivity : (0:ℝ) ≤ ((q:ℝ)+1)^2)
    have he : ((q:ℝ)+1)^2 * (1/(q:ℝ)) = (q:ℝ) + 2 + 1/(q:ℝ) := by field_simp; ring
    rw [he] at hm
    have h1q : 1/(q:ℝ) ≤ 1 := by rw [div_le_one hq0]; linarith
    linarith
  have hid : Psi ((q:ℝ)+1) - Psi (q:ℝ)
      = ((q:ℝ) + 1/2) * Real.log q + (((q:ℝ)+1)^2 * s)/2 - (q:ℝ) - 1/2 := by
    have hl1 : Real.log ((q:ℝ)+1) = Real.log q + s := by rw [hs]; ring
    unfold Psi
    rw [hl1]
    ring
  rw [hid]
  have hkey : (q:ℝ)^2 * (Real.log q - 1/2) * s
      - (((q:ℝ) + 1/2) * Real.log q + (((q:ℝ)+1)^2 * s)/2 - (q:ℝ) - 1/2)
      = ((q:ℝ)^2 * s - ((q:ℝ) + 1/2)) * Real.log q
        - ((q:ℝ)^2 * s)/2 - (((q:ℝ)+1)^2 * s)/2 + (q:ℝ) + 1/2 := by ring
  rw [hkey, abs_le] at *
  have hp1 : (0:ℝ) ≤ ((q:ℝ)^2 * s - ((q:ℝ)+1/2) + 3/2) * Real.log q :=
    mul_nonneg (by linarith [hA.1]) hlq
  have hp2 : (0:ℝ) ≤ (3/2 - ((q:ℝ)^2 * s - ((q:ℝ)+1/2))) * Real.log q :=
    mul_nonneg (by linarith [hA.2]) hlq
  constructor <;> nlinarith [hp1, hp2, hB1, hB2, hA.1, hA.2, hlq, hqR]

theorem sum_log_lin_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Finset.Ico 1 N, (1 + Real.log q) ≤ (N:ℝ) * (1 + Real.log N) := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hb : ∀ q ∈ Finset.Ico 1 N, (1 + Real.log q) ≤ (1 + Real.log N) := by
    intro q hq
    obtain ⟨hq1, hqN⟩ := Finset.mem_Ico.mp hq
    have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
    have hqN' : (q:ℝ) ≤ (N:ℝ) := by exact_mod_cast hqN.le
    have h2 : Real.log q ≤ Real.log N := Real.log_le_log (by linarith) hqN'
    linarith
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ (N:ℝ) := by
    have h : (N - 1 : ℕ) ≤ N := Nat.sub_le _ _
    exact_mod_cast h
  nlinarith [Real.log_nonneg hNR]

theorem sum_logcube_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Finset.Ico 1 N, (1 + Real.log q)^3 ≤ (N:ℝ) * (1 + Real.log N)^3 := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNR
  have hb : ∀ q ∈ Finset.Ico 1 N, (1 + Real.log q)^3 ≤ (1 + Real.log N)^3 := by
    intro q hq
    obtain ⟨hq1, hqN⟩ := Finset.mem_Ico.mp hq
    have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
    have hqN' : (q:ℝ) ≤ (N:ℝ) := by exact_mod_cast hqN.le
    have h1 : (0:ℝ) ≤ 1 + Real.log q := by linarith [Real.log_nonneg hqR]
    have h1N : (0:ℝ) ≤ 1 + Real.log N := by linarith
    have h2 : Real.log q ≤ Real.log N := Real.log_le_log (by linarith) hqN'
    have hd : (0:ℝ) ≤ (1 + Real.log (N:ℝ)) - (1 + Real.log (q:ℝ)) := by linarith
    have hs : (0:ℝ) ≤ (1 + Real.log (q:ℝ))^2 + (1 + Real.log (q:ℝ)) * (1 + Real.log (N:ℝ))
        + (1 + Real.log (N:ℝ))^2 := by
      nlinarith [mul_nonneg h1 h1N, sq_nonneg (1 + Real.log (q:ℝ)), sq_nonneg (1 + Real.log (N:ℝ))]
    nlinarith [mul_nonneg hd hs]
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ (N:ℝ) := by
    have h : (N - 1 : ℕ) ≤ N := Nat.sub_le _ _
    exact_mod_cast h
  nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 + Real.log (N:ℝ)) 3]

theorem sum_main2 (N : ℕ) (hN : 1 ≤ N) :
    |(∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
        * (Real.log ((q:ℝ)+1) - Real.log q)) - (N:ℝ)^2 * (Real.log N - 1)/2|
      ≤ 3 * (N:ℝ) * (1 + Real.log N) := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNR
  have htel := sum_Psi_telescope N hN
  have hdiff : (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
        * (Real.log ((q:ℝ)+1) - Real.log q)) - (Psi (N:ℝ) + 1/2)
      = ∑ q ∈ Finset.Ico 1 N, ((q:ℝ)^2 * (Real.log q - 1/2)
          * (Real.log ((q:ℝ)+1) - Real.log q) - (Psi ((q:ℝ)+1) - Psi (q:ℝ))) := by
    rw [Finset.sum_sub_distrib, htel]
  have hb : |(∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
        * (Real.log ((q:ℝ)+1) - Real.log q)) - (Psi (N:ℝ) + 1/2)|
      ≤ 2 * ((N:ℝ) * (1 + Real.log N)) := by
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun q hq => Psi_step q (Finset.mem_Ico.mp hq).1)).trans ?_
    rw [← Finset.mul_sum]
    linarith [sum_log_lin_le N hN]
  have hPsi : Psi (N:ℝ) + 1/2 = (N:ℝ)^2 * (Real.log N - 1)/2 + 1/2 := by
    unfold Psi; ring
  rw [hPsi] at hb
  have hone : (1:ℝ) ≤ (N:ℝ) * (1 + Real.log N) := by nlinarith
  rw [abs_le] at hb ⊢
  constructor <;> linarith [hb.1, hb.2, hone]

/-- **The SECOND moment**: `Σ_{q ≤ N} φ*(q)(log q)² = (18/π⁴)N²((log N)² − log N + ½)
+ O(N log⁴N)`, with the explicit constant 30. -/
theorem Alog2_bound (N : ℕ) (hN : 1 ≤ N) :
    |Alog2 N - (18/Real.pi^4) * (N:ℝ)^2 * (Real.log N ^ 2 - Real.log N + 1/2)|
      ≤ 30 * (N:ℝ) * (1 + Real.log N)^4 := by
  have hNR : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNR
  set c : ℝ := 18/Real.pi^4 with hc
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  have hcle : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    have h1 : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h2 : (9:ℝ) < Real.pi ^ 2 := by nlinarith
    have h3 : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
    rw [h3]; nlinarith [h2]
  have hsum : |(∑ q ∈ Finset.Ico 1 N, Alog q * (Real.log ((q:ℝ)+1) - Real.log q))
      - c * (N:ℝ)^2 * (Real.log N - 1)/2|
      ≤ 3*(N:ℝ)*(1 + Real.log N) + 13*(N:ℝ)*(1 + Real.log N)^3 := by
    have hdec : ∑ q ∈ Finset.Ico 1 N, Alog q * (Real.log ((q:ℝ)+1) - Real.log q)
        = c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
              * (Real.log ((q:ℝ)+1) - Real.log q))
          + ∑ q ∈ Finset.Ico 1 N, (Alog q - c * (q:ℝ)^2 * (Real.log q - 1/2))
              * (Real.log ((q:ℝ)+1) - Real.log q) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hE : |∑ q ∈ Finset.Ico 1 N, (Alog q - c * (q:ℝ)^2 * (Real.log q - 1/2))
        * (Real.log ((q:ℝ)+1) - Real.log q)| ≤ 13*(N:ℝ)*(1 + Real.log N)^3 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ q ∈ Finset.Ico 1 N,
          |(Alog q - c * (q:ℝ)^2 * (Real.log q - 1/2))
            * (Real.log ((q:ℝ)+1) - Real.log q)| ≤ 13 * (1 + Real.log q)^3 := by
        intro q hq
        obtain ⟨hq1, _⟩ := Finset.mem_Ico.mp hq
        have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
        have hq0 : (0:ℝ) < (q:ℝ) := by linarith
        obtain ⟨hlo, hhi⟩ := logstep_bounds q hq1
        have h13 : |Alog q - c * (q:ℝ)^2 * (Real.log q - 1/2)|
            ≤ 13 * (q:ℝ) * (1 + Real.log q)^3 := by
          rw [hc]; exact Alog_bound q hq1
        have hstep0 : (0:ℝ) ≤ Real.log ((q:ℝ)+1) - Real.log q := by
          have : (0:ℝ) < 1/((q:ℝ)+1) := by positivity
          linarith
        rw [abs_mul, abs_of_nonneg hstep0]
        have hfin : (13 * (q:ℝ) * (1 + Real.log q)^3) * (1/(q:ℝ))
            = 13 * (1 + Real.log q)^3 := by field_simp
        calc |Alog q - c * (q:ℝ)^2 * (Real.log q - 1/2)|
              * (Real.log ((q:ℝ)+1) - Real.log q)
            ≤ (13 * (q:ℝ) * (1 + Real.log q)^3) * (1/(q:ℝ)) :=
              mul_le_mul h13 hhi hstep0 (by positivity)
          _ = 13 * (1 + Real.log q)^3 := hfin
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.mul_sum]
      linarith [sum_logcube_le N hN]
    have hM := sum_main2 N hN
    have hMc : |c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
        * (Real.log ((q:ℝ)+1) - Real.log q)) - c * (N:ℝ)^2 * (Real.log N - 1)/2|
        ≤ 3*(N:ℝ)*(1 + Real.log N) := by
      have he : c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
            * (Real.log ((q:ℝ)+1) - Real.log q)) - c * (N:ℝ)^2 * (Real.log N - 1)/2
          = c * ((∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
              * (Real.log ((q:ℝ)+1) - Real.log q)) - (N:ℝ)^2 * (Real.log N - 1)/2) := by ring
      rw [he, abs_mul, abs_of_pos hcpos]
      nlinarith [hM, abs_nonneg ((∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
        * (Real.log ((q:ℝ)+1) - Real.log q)) - (N:ℝ)^2 * (Real.log N - 1)/2),
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (by linarith : (0:ℝ) ≤ (N:ℝ)))
          (by linarith : (0:ℝ) ≤ 1 + Real.log (N:ℝ))]
    rw [hdec]
    have htri := abs_add_le
      (c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
          * (Real.log ((q:ℝ)+1) - Real.log q)) - c * (N:ℝ)^2 * (Real.log N - 1)/2)
      (∑ q ∈ Finset.Ico 1 N, (Alog q - c * (q:ℝ)^2 * (Real.log q - 1/2))
        * (Real.log ((q:ℝ)+1) - Real.log q))
    have hrw : c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
          * (Real.log ((q:ℝ)+1) - Real.log q))
        + (∑ q ∈ Finset.Ico 1 N, (Alog q - c * (q:ℝ)^2 * (Real.log q - 1/2))
          * (Real.log ((q:ℝ)+1) - Real.log q))
        - c * (N:ℝ)^2 * (Real.log N - 1)/2
        = (c * (∑ q ∈ Finset.Ico 1 N, (q:ℝ)^2 * (Real.log q - 1/2)
              * (Real.log ((q:ℝ)+1) - Real.log q)) - c * (N:ℝ)^2 * (Real.log N - 1)/2)
          + (∑ q ∈ Finset.Ico 1 N, (Alog q - c * (q:ℝ)^2 * (Real.log q - 1/2))
              * (Real.log ((q:ℝ)+1) - Real.log q)) := by ring
    rw [hrw]
    linarith [htri, hMc, hE]
  have hAN : |Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2)|
      ≤ 13 * (N:ℝ) * (1 + Real.log N)^3 := by
    rw [hc]; exact Alog_bound N hN
  rw [abel2 N]
  have hexp : Alog N * Real.log N
      - (∑ q ∈ Finset.Ico 1 N, Alog q * (Real.log ((q:ℝ)+1) - Real.log q))
      - c * (N:ℝ)^2 * (Real.log N ^ 2 - Real.log N + 1/2)
      = (Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2)) * Real.log N
        + -((∑ q ∈ Finset.Ico 1 N, Alog q * (Real.log ((q:ℝ)+1) - Real.log q))
            - c * (N:ℝ)^2 * (Real.log N - 1)/2) := by ring
  rw [hexp]
  have hA1 : |(Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2)) * Real.log N|
      ≤ 13*(N:ℝ)*(1 + Real.log N)^3 * Real.log N := by
    rw [abs_mul, abs_of_nonneg hlogN]
    exact mul_le_mul_of_nonneg_right hAN hlogN
  have hA2 : |-((∑ q ∈ Finset.Ico 1 N, Alog q * (Real.log ((q:ℝ)+1) - Real.log q))
      - c * (N:ℝ)^2 * (Real.log N - 1)/2)|
      ≤ 3*(N:ℝ)*(1 + Real.log N) + 13*(N:ℝ)*(1 + Real.log N)^3 := by
    rw [abs_neg]; exact hsum
  have htri := abs_add_le ((Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2)) * Real.log N)
    (-((∑ q ∈ Finset.Ico 1 N, Alog q * (Real.log ((q:ℝ)+1) - Real.log q))
      - c * (N:ℝ)^2 * (Real.log N - 1)/2))
  set t : ℝ := 1 + Real.log (N:ℝ) with ht
  have ht1 : (1:ℝ) ≤ t := by rw [ht]; linarith
  have hNpos : (0:ℝ) ≤ (N:ℝ) := by linarith
  have hp2 : t^2 ≤ t^3 := by nlinarith
  have hp3 : t^3 ≤ t^4 := by nlinarith
  have hp1 : t ≤ t^4 := by nlinarith
  have he1 : 13*(N:ℝ)*t^3 * Real.log (N:ℝ) ≤ 13*((N:ℝ)*t^4) := by
    have hlt : Real.log (N:ℝ) ≤ t := by rw [ht]; linarith
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ t) 3, hNpos]
  have he2 : 3*(N:ℝ)*t ≤ 3*((N:ℝ)*t^4) := by nlinarith [hNpos, hp1]
  have he3 : 13*(N:ℝ)*t^3 ≤ 13*((N:ℝ)*t^4) := by nlinarith [hNpos, hp3]
  linarith [htri, hA1, hA2, he1, he2, he3]

set_option maxHeartbeats 1600000 in
/-- The `x²`-normalised FIRST moment, centred at `log x`:
`(Alog ⌊x⌋ − Astar ⌊x⌋ · log x)/x² → −(18/π⁴)/2`. This is the form the DYADIC average
consumes (`Alog N − Alog(N/2)` over `Astar N − Astar(N/2)`, both normalised by `x²`). -/
theorem Alog_sub_tendsto :
    Tendsto (fun x : ℝ => (Alog ⌊x⌋₊ - Astar ⌊x⌋₊ * Real.log x) / x ^ 2) atTop
      (nhds (-(18/Real.pi^4)/2)) := by
  set c : ℝ := 18/Real.pi^4 with hc
  clear_value c
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  have hcle : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    have h1 : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h2 : (9:ℝ) < Real.pi ^ 2 := by nlinarith
    have h3 : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
    rw [h3]; nlinarith [h2]
  have hg : Tendsto (fun x : ℝ => 200 * (Real.log x ^ 3 / x)) atTop (nhds 0) := by
    have h3 : Tendsto (fun x : ℝ => Real.log x ^ 3 / x) atTop (nhds 0) := by
      simpa using (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero
    simpa using h3.const_mul (200:ℝ)
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖(Alog ⌊x⌋₊ - Astar ⌊x⌋₊ * Real.log x) / x ^ 2 - (-c/2)‖
        ≤ 200 * (Real.log x ^ 3 / x) := by
    filter_upwards [eventually_ge_atTop (3:ℝ)] with x hx
    have hx0 : (0:ℝ) < x := by linarith
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hlog1 : (1:ℝ) < Real.log x := by
      have h3 : (1:ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hx)
    set N : ℕ := ⌊x⌋₊ with hNdef
    have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr (by linarith)
    have hNx : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
    have hxN : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
    have hNR1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    clear_value N
    have hlogN : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hNx
    have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg hNR1
    have hAN : |Astar N - c * (N:ℝ)^2| ≤ 5 * (N:ℝ) * (1 + Real.log N)^2 := by
      rw [hc]; exact Astar_bound N hN1
    have hAlog : |Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2)|
        ≤ 13 * (N:ℝ) * (1 + Real.log N)^3 := by
      rw [hc]; exact Alog_bound N hN1
    have hpow2 : (1 + Real.log (N:ℝ))^2 ≤ (1 + Real.log x)^2 := by nlinarith
    have hpow3 : (1 + Real.log (N:ℝ))^3 ≤ (1 + Real.log x)^3 := by nlinarith [hpow2, hlogN0]
    have hlogdiff : Real.log x - Real.log (N:ℝ) ≤ 1/(N:ℝ) := by
      have hle : Real.log x ≤ Real.log ((N:ℝ)+1) := Real.log_le_log hx0 hxN.le
      have h := Real.log_le_sub_one_of_pos (x := ((N:ℝ)+1)/(N:ℝ)) (by positivity)
      have he : ((N:ℝ)+1)/(N:ℝ) - 1 = 1/(N:ℝ) := by field_simp; ring
      rw [he, Real.log_div (by positivity) (by positivity)] at h
      linarith
    have hcube1 : (1:ℝ) ≤ (1 + Real.log x)^3 := by nlinarith [hlog1]
    have hNcube : (N:ℝ) ≤ (N:ℝ) * (1 + Real.log x)^3 :=
      le_mul_of_one_le_right (by linarith) hcube1
    have hb1 : 13 * (N:ℝ) * (1 + Real.log N)^3 ≤ 13 * (N:ℝ) * (1 + Real.log x)^3 :=
      mul_le_mul_of_nonneg_left hpow3 (by positivity)
    have hb2 : |(-(Real.log x)) * (Astar N - c * (N:ℝ)^2)|
        ≤ 5 * (N:ℝ) * (1 + Real.log x)^3 := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.log x)]
      have h2 : 5 * (N:ℝ) * (1 + Real.log N)^2 ≤ 5 * (N:ℝ) * (1 + Real.log x)^2 :=
        mul_le_mul_of_nonneg_left hpow2 (by positivity)
      have h3 : Real.log x * (5 * (N:ℝ) * (1 + Real.log x)^2)
          ≤ 5 * (N:ℝ) * (1 + Real.log x)^3 := by nlinarith [sq_nonneg (1 + Real.log x), hNR1]
      calc Real.log x * |Astar N - c * (N:ℝ)^2|
          ≤ Real.log x * (5 * (N:ℝ) * (1 + Real.log x)^2) :=
            mul_le_mul_of_nonneg_left (le_trans hAN h2) (by linarith)
        _ ≤ 5 * (N:ℝ) * (1 + Real.log x)^3 := h3
    have hb3 : |c * (N:ℝ)^2 * (Real.log (N:ℝ) - Real.log x)| ≤ (N:ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c * (N:ℝ)^2)]
      have habs : |Real.log (N:ℝ) - Real.log x| ≤ 1/(N:ℝ) := by
        rw [abs_le]
        exact ⟨by linarith, by linarith [(by positivity : (0:ℝ) < 1/(N:ℝ))]⟩
      have hmul := mul_le_mul_of_nonneg_left habs (by positivity : (0:ℝ) ≤ c * (N:ℝ)^2)
      have he : c * (N:ℝ)^2 * (1/(N:ℝ)) = c * (N:ℝ) := by field_simp
      rw [he] at hmul
      nlinarith [hcle, hNR1]
    have hb4 : |c * (x^2 - (N:ℝ)^2)/2| ≤ 2 * (N:ℝ) := by
      have hd : |x^2 - (N:ℝ)^2| ≤ 4 * (N:ℝ) := by
        rw [abs_le]; constructor <;> nlinarith
      rw [show c * (x^2 - (N:ℝ)^2)/2 = (c/2) * (x^2 - (N:ℝ)^2) by ring, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ c/2)]
      have hpos : (0:ℝ) ≤ |x^2 - (N:ℝ)^2| := abs_nonneg _
      nlinarith [hd, hcle, hcpos, hNR1, hpos]
    have hnum : |Alog N - Astar N * Real.log x + c * x^2/2|
        ≤ 22 * (N:ℝ) * (1 + Real.log x)^3 := by
      have hre : Alog N - Astar N * Real.log x + c * x^2/2
          = (((Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2))
                + (-(Real.log x)) * (Astar N - c * (N:ℝ)^2))
              + c * (N:ℝ)^2 * (Real.log (N:ℝ) - Real.log x))
            + c * (x^2 - (N:ℝ)^2)/2 := by ring
      rw [hre]
      have t1 := abs_add_le (Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2))
        ((-(Real.log x)) * (Astar N - c * (N:ℝ)^2))
      have t2 := abs_add_le ((Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2))
          + (-(Real.log x)) * (Astar N - c * (N:ℝ)^2))
        (c * (N:ℝ)^2 * (Real.log (N:ℝ) - Real.log x))
      have t3 := abs_add_le (((Alog N - c * (N:ℝ)^2 * (Real.log N - 1/2))
            + (-(Real.log x)) * (Astar N - c * (N:ℝ)^2))
          + c * (N:ℝ)^2 * (Real.log (N:ℝ) - Real.log x))
        (c * (x^2 - (N:ℝ)^2)/2)
      linarith [t1, t2, t3, hAlog, hb1, hb2, hb3, hb4, hNcube]
    have heq : (Alog N - Astar N * Real.log x) / x^2 - (-c/2)
        = (Alog N - Astar N * Real.log x + c * x^2/2) / x^2 := by
      field_simp
      ring
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < x^2),
      div_le_iff₀ (by positivity : (0:ℝ) < x^2)]
    have hsq : (1 + Real.log x)^2 ≤ 4 * Real.log x ^ 2 := by nlinarith [hlog1]
    have hxlog : (1 + Real.log x)^3 ≤ 8 * Real.log x ^ 3 := by
      have hm := mul_le_mul hsq (by linarith : 1 + Real.log x ≤ 2 * Real.log x)
        (by linarith : (0:ℝ) ≤ 1 + Real.log x)
        (by positivity : (0:ℝ) ≤ 4 * Real.log x ^ 2)
      linarith [hm]
    have hrhs : 200 * (Real.log x ^ 3 / x) * x^2 = 200 * Real.log x ^ 3 * x := by
      field_simp
    rw [hrhs]
    have hL3x : (0:ℝ) ≤ Real.log x ^ 3 * x :=
      mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ Real.log x) 3) hx0.le
    have hstep : 22 * (N:ℝ) * (1 + Real.log x)^3 ≤ 200 * Real.log x ^ 3 * x := by
      calc 22 * (N:ℝ) * (1 + Real.log x)^3 ≤ 22 * (N:ℝ) * (8 * Real.log x ^ 3) :=
            mul_le_mul_of_nonneg_left hxlog (by positivity)
        _ = 176 * Real.log x ^ 3 * (N:ℝ) := by ring
        _ ≤ 176 * Real.log x ^ 3 * x :=
            mul_le_mul_of_nonneg_left hNx (by positivity)
        _ ≤ 200 * Real.log x ^ 3 * x := by linarith
    linarith [hnum, hstep]
  have hzero := squeeze_zero_norm' hbound hg
  rw [← tendsto_sub_nhds_zero_iff]
  exact hzero

set_option maxHeartbeats 1600000 in
/-- The φ*-weighted SECOND log-moment normalised by the family size:
`Σφ*(q)(log q)² / Σφ*(q) = (log x)² − log x + ½ + o(1)`. -/
theorem avgLogSq_limit :
    Tendsto (fun x : ℝ => Alog2 ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x ^ 2 + Real.log x) atTop
      (nhds (1/2)) := by
  set c : ℝ := 18/Real.pi^4 with hc
  clear_value c
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  have hcle : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    have h1 : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h2 : (9:ℝ) < Real.pi ^ 2 := by nlinarith
    have h3 : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
    rw [h3]; nlinarith [h2]
  have hpi4 : Real.pi ^ 4 ≤ 100 := by
    have h1 : Real.pi < 3.15 := Real.pi_lt_d2
    have h2 : (0:ℝ) < Real.pi := Real.pi_pos
    have hsq : Real.pi ^ 2 < 9.9225 := by nlinarith
    have h3 : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
    rw [h3]
    nlinarith [hsq, sq_nonneg (Real.pi ^ 2)]
  have hclow : (18:ℝ)/100 ≤ c := by
    rw [hc, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [hpi4]
  have hg : Tendsto (fun x : ℝ => 20000 * (Real.log x ^ 4 / x)) atTop (nhds 0) := by
    have h4 : Tendsto (fun x : ℝ => Real.log x ^ 4 / x) atTop (nhds 0) := by
      simpa using (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero
    simpa using h4.const_mul (20000:ℝ)
  have hlim2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hev0 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 / x < c/80 :=
    hlim2.eventually_lt_const (by positivity)
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖Alog2 ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x ^ 2 + Real.log x - 1/2‖
        ≤ 20000 * (Real.log x ^ 4 / x) := by
    filter_upwards [eventually_ge_atTop (3:ℝ), hev0] with x hx hxc
    have hx0 : (0:ℝ) < x := by linarith
    have hlog1 : (1:ℝ) < Real.log x := by
      have h3 : (1:ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hx)
    have hp1 : (0:ℝ) < Real.log x ^ 4 := by positivity
    set N : ℕ := ⌊x⌋₊ with hNdef
    have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr (by linarith)
    have hNx : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
    have hxN : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
    have hNR1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    clear_value N
    have hx2N : x ≤ 2 * (N:ℝ) := by linarith
    have hlogN : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hNx
    have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg hNR1
    have hAN : |Astar N - c * (N:ℝ)^2| ≤ 5 * (N:ℝ) * (1 + Real.log N)^2 := by
      rw [hc]; exact Astar_bound N hN1
    have hA2 : |Alog2 N - c * (N:ℝ)^2 * (Real.log N ^ 2 - Real.log N + 1/2)|
        ≤ 30 * (N:ℝ) * (1 + Real.log N)^4 := by
      rw [hc]; exact Alog2_bound N hN1
    have hpow2 : (1 + Real.log (N:ℝ))^2 ≤ (1 + Real.log x)^2 := by nlinarith
    have hpow4 : (1 + Real.log (N:ℝ))^4 ≤ (1 + Real.log x)^4 := by
      nlinarith [hpow2, sq_nonneg (1 + Real.log (N:ℝ)), sq_nonneg (1 + Real.log x)]
    have hsmall : 5 * (1 + Real.log (N:ℝ))^2 ≤ (c/2) * (N:ℝ) := by
      have h1 : (1 + Real.log (N:ℝ))^2 ≤ (2 * Real.log x)^2 := by
        have hb : 1 + Real.log (N:ℝ) ≤ 2 * Real.log x := by linarith
        nlinarith [hlogN0]
      have h2 : (20:ℝ) * Real.log x ^ 2 ≤ (c/4) * x := by
        rw [div_lt_iff₀ hx0] at hxc
        nlinarith
      nlinarith [h1, h2, hx2N, hcpos]
    have hDlow : (c/2) * (N:ℝ)^2 ≤ Astar N := by
      have h := (abs_le.mp hAN).1
      nlinarith [hsmall, hNR1]
    have hDlow2 : (9/100 : ℝ) * (N:ℝ)^2 ≤ Astar N := by
      nlinarith [hDlow, hclow, sq_nonneg ((N:ℝ))]
    have hDpos : (0:ℝ) < Astar N := by nlinarith [hDlow2, hNR1]
    have hDne : Astar N ≠ 0 := ne_of_gt hDpos
    have hlogdiff : Real.log x - Real.log (N:ℝ) ≤ 1/(N:ℝ) := by
      have hle : Real.log x ≤ Real.log ((N:ℝ)+1) := Real.log_le_log hx0 hxN.le
      have h := Real.log_le_sub_one_of_pos (x := ((N:ℝ)+1)/(N:ℝ)) (by positivity)
      have he : ((N:ℝ)+1)/(N:ℝ) - 1 = 1/(N:ℝ) := by field_simp; ring
      rw [he, Real.log_div (by positivity) (by positivity)] at h
      linarith
    have hq1 : (1:ℝ) ≤ (1 + Real.log x)^4 := by nlinarith [hlog1]
    have hN4 : (N:ℝ) ≤ (N:ℝ) * (1 + Real.log x)^4 :=
      le_mul_of_one_le_right (by linarith) hq1
    have hb1 : 30 * (N:ℝ) * (1 + Real.log N)^4 ≤ 30 * (N:ℝ) * (1 + Real.log x)^4 :=
      mul_le_mul_of_nonneg_left hpow4 (by positivity)
    -- the `log N` ↦ `log x` swap in the main term
    have hb2 : |c * (N:ℝ)^2 * ((Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2)
          - (Real.log x ^ 2 - Real.log x + 1/2))| ≤ 3 * (N:ℝ) * (1 + Real.log x) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c * (N:ℝ)^2)]
      have habs : |(Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2)
          - (Real.log x ^ 2 - Real.log x + 1/2)| ≤ (2 * Real.log x + 1)/(N:ℝ) := by
        have hd0 : (0:ℝ) ≤ Real.log x - Real.log (N:ℝ) := by linarith
        have hfac : (Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2)
            - (Real.log x ^ 2 - Real.log x + 1/2)
            = -((Real.log x - Real.log (N:ℝ)) * (Real.log x + Real.log (N:ℝ)))
              + (Real.log x - Real.log (N:ℝ)) := by ring
        rw [hfac, abs_le]
        have hinv : (0:ℝ) < 1/(N:ℝ) := by positivity
        constructor
        · have h1 : (Real.log x - Real.log (N:ℝ)) * (Real.log x + Real.log (N:ℝ))
              ≤ (1/(N:ℝ)) * (2 * Real.log x) := by
            apply mul_le_mul hlogdiff (by linarith) (by linarith) (le_of_lt hinv)
          have h2 : (0:ℝ) ≤ (Real.log x - Real.log (N:ℝ)) := hd0
          have hE : (1/(N:ℝ)) * (2 * Real.log x) = (2 * Real.log x)/(N:ℝ) := by
            field_simp
          have hE2 : (2 * Real.log x + 1)/(N:ℝ) = (2*Real.log x)/(N:ℝ) + 1/(N:ℝ) := by
            field_simp
          rw [hE] at h1
          rw [hE2]
          linarith
        · have h3 : (0:ℝ) ≤ (Real.log x - Real.log (N:ℝ)) * (Real.log x + Real.log (N:ℝ)) := by
            apply mul_nonneg hd0; linarith
          have hE2 : (2 * Real.log x + 1)/(N:ℝ) = (2*Real.log x)/(N:ℝ) + 1/(N:ℝ) := by
            field_simp
          have hpos2 : (0:ℝ) ≤ (2*Real.log x)/(N:ℝ) := by positivity
          rw [hE2]
          linarith [hlogdiff]
      have hmul := mul_le_mul_of_nonneg_left habs (by positivity : (0:ℝ) ≤ c * (N:ℝ)^2)
      have he : c * (N:ℝ)^2 * ((2 * Real.log x + 1)/(N:ℝ))
          = c * (N:ℝ) * (2 * Real.log x + 1) := by field_simp
      rw [he] at hmul
      have hprod : (0:ℝ) ≤ (N:ℝ) * (2 * Real.log x + 1) * (1 - c) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      have hprod2 : (0:ℝ) ≤ (N:ℝ) * (2 + Real.log x) :=
        mul_nonneg (by linarith) (by linarith)
      linarith [hmul, hprod, hprod2]
    have hb3 : |(-(Real.log x ^ 2 - Real.log x + 1/2)) * (Astar N - c * (N:ℝ)^2)|
        ≤ 5 * (N:ℝ) * (1 + Real.log x)^4 := by
      rw [abs_mul, abs_neg]
      have hf : |Real.log x ^ 2 - Real.log x + 1/2| ≤ (1 + Real.log x)^2 := by
        rw [abs_le]
        constructor <;> nlinarith [hlog1]
      have h2 : 5 * (N:ℝ) * (1 + Real.log N)^2 ≤ 5 * (N:ℝ) * (1 + Real.log x)^2 :=
        mul_le_mul_of_nonneg_left hpow2 (by positivity)
      calc |Real.log x ^ 2 - Real.log x + 1/2| * |Astar N - c * (N:ℝ)^2|
          ≤ (1 + Real.log x)^2 * (5 * (N:ℝ) * (1 + Real.log x)^2) :=
            mul_le_mul hf (le_trans hAN h2) (abs_nonneg _) (by positivity)
        _ = 5 * (N:ℝ) * (1 + Real.log x)^4 := by ring
    have hnum : |Alog2 N - (Real.log x ^ 2 - Real.log x + 1/2) * Astar N|
        ≤ 40 * (N:ℝ) * (1 + Real.log x)^4 := by
      have hre : Alog2 N - (Real.log x ^ 2 - Real.log x + 1/2) * Astar N
          = ((Alog2 N - c * (N:ℝ)^2 * (Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2))
              + c * (N:ℝ)^2 * ((Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2)
                  - (Real.log x ^ 2 - Real.log x + 1/2)))
            + (-(Real.log x ^ 2 - Real.log x + 1/2)) * (Astar N - c * (N:ℝ)^2) := by ring
      rw [hre]
      have t1 := abs_add_le (Alog2 N - c * (N:ℝ)^2 * (Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2))
        (c * (N:ℝ)^2 * ((Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2)
          - (Real.log x ^ 2 - Real.log x + 1/2)))
      have t2 := abs_add_le ((Alog2 N - c * (N:ℝ)^2 * (Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2))
          + c * (N:ℝ)^2 * ((Real.log (N:ℝ) ^ 2 - Real.log (N:ℝ) + 1/2)
            - (Real.log x ^ 2 - Real.log x + 1/2)))
        ((-(Real.log x ^ 2 - Real.log x + 1/2)) * (Astar N - c * (N:ℝ)^2))
      have hlin : 3 * (N:ℝ) * (1 + Real.log x) ≤ 3 * ((N:ℝ) * (1 + Real.log x)^4) := by
        nlinarith [hlog1, hNR1, sq_nonneg (1 + Real.log x)]
      linarith [t1, t2, hA2, hb1, hb2, hb3, hlin]
    have heq : Alog2 N / Astar N - Real.log x ^ 2 + Real.log x - 1/2
        = (Alog2 N - (Real.log x ^ 2 - Real.log x + 1/2) * Astar N) / Astar N := by
      field_simp
      ring
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    have hsq4 : (1 + Real.log x)^2 ≤ 4 * Real.log x ^ 2 := by nlinarith [hlog1]
    have hxlog : (1 + Real.log x)^4 ≤ 16 * Real.log x ^ 4 := by
      have hm := mul_le_mul hsq4 hsq4 (sq_nonneg (1 + Real.log x))
        (by positivity : (0:ℝ) ≤ 4 * Real.log x ^ 2)
      linarith [hm]
    have hstep : 40 * (N:ℝ) * (1 + Real.log x)^4
        ≤ 20000 * (Real.log x ^ 4 / x) * ((9/100 : ℝ) * (N:ℝ)^2) := by
      have hrhs : 20000 * (Real.log x ^ 4 / x) * ((9/100 : ℝ) * (N:ℝ)^2)
          = 1800 * Real.log x ^ 4 * (N:ℝ)^2 / x := by
        field_simp
        ring
      rw [hrhs, le_div_iff₀ hx0]
      calc 40 * (N:ℝ) * (1 + Real.log x)^4 * x
          ≤ 40 * (N:ℝ) * (16 * Real.log x ^ 4) * x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hxlog (by positivity)) hx0.le
        _ = 640 * (N:ℝ) * Real.log x ^ 4 * x := by ring
        _ ≤ 640 * (N:ℝ) * Real.log x ^ 4 * (2 * (N:ℝ)) :=
            mul_le_mul_of_nonneg_left hx2N (by positivity)
        _ = 1280 * Real.log x ^ 4 * (N:ℝ)^2 := by ring
        _ ≤ 1800 * Real.log x ^ 4 * (N:ℝ)^2 := by
            nlinarith [mul_nonneg hp1.le (sq_nonneg ((N:ℝ)))]
    have hmono : 20000 * (Real.log x ^ 4 / x) * ((9/100 : ℝ) * (N:ℝ)^2)
        ≤ 20000 * (Real.log x ^ 4 / x) * Astar N :=
      mul_le_mul_of_nonneg_left hDlow2 (by positivity)
    linarith [hnum, hstep, hmono]
  have hzero : Tendsto
      (fun x : ℝ => Alog2 ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x ^ 2 + Real.log x - 1/2) atTop (nhds 0) :=
    squeeze_zero_norm' hbound hg
  have h := hzero.add_const (1/2 : ℝ)
  have hfun : (fun x : ℝ =>
      Alog2 ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x ^ 2 + Real.log x - 1/2 + 1/2)
      = fun x : ℝ => Alog2 ⌊x⌋₊ / Astar ⌊x⌋₊ - Real.log x ^ 2 + Real.log x := by
    funext x; ring
  rw [hfun] at h
  have hv : (0:ℝ) + 1/2 = 1/2 := by norm_num
  rwa [hv] at h

end N2

/-- **N2, the workhorse.** `Σ_{q ≤ x} φ*(q) = (18/π⁴)x² + O(x log²x)`.

**REPAIRED (D17) — THE ERROR TERM IS WEAKENED FROM `O(x log x)` TO `O(x log²x)`, AND THIS IS
FLAGGED, NOT SNUCK IN.** The main term is untouched, `18/π⁴` is exactly the paper's, and the
weaker statement is what is now PROVED here, `sorry`-free, with the explicit constant 22 for
every `x ≥ 3` (`N2.sum_phiStar_bigO`, and `N2.Astar_bound`'s
`|Σ_{q≤N}φ*(q) − (18/π⁴)N²| ≤ 5N(1 + log N)²` at integer argument).

*Why the paper's `O(x log x)` is not what this route proves.* `φ* = μ ⋆ μ ⋆ id`, so the
elementary Dirichlet-hyperbola evaluation is
`Σ_{q≤x} φ*(q) = Σ_{d≤x} μ(d)·Φ(x/d)` with `Φ(y) = Σ_{m≤y} φ(m) = (3/π²)y² + O(y log y)`.
The main terms give `(18/π⁴)x² + O(x)`, but the error terms give
`Σ_{d≤x} |μ(d)|·(x/d)·log(x/d) ≍ x·log x·Σ_{d≤x} 1/d ≍ x log²x`, and the extra `log` is
**structural to the elementary route**: it is `Σ_{d≤x} 1/d`, not slack in any inequality.
Reaching `O(x log x)` needs cancellation in `Σ_{d≤x} μ(d)·R(x/d)` (`R` = the `φ`-error), i.e.
Mertens-type input `Σ_{n≤x} μ(n)/n = O(1)` carried through a double sum, or the contour
argument the paper alludes to (`Σφ*(n)n^{−s} = ζ(s−1)/ζ(s)²`, residue `1/ζ(2)²·x²/2` at
`s = 2`). Neither is available in this Mathlib pin, and NEITHER IS NEEDED: see the next
paragraph. The sharper form is standard in the literature and is believed TRUE; nothing here
refutes it, and no statement in this file asserts its negation.

*Why the weakening is free downstream.* Every consumer of N2 in §12.2 is a partial summation
in which the error enters divided by `x²` (`famCard_asymp`, `famCardDyadic_asymp`) or by
`x² log x` (`avgLogCond_asymp`, `avgLogCondDyadic_asymp`, `ratio_of_sums_bound`,
`inv_avgC_bound`, `conductor_spread_bigO`). The relative error is therefore
`O(log²x / x)` where the paper has `O(log x / x)` — both are `o(1/ℒ^k)` for every `k`, and the
quantities the certificate actually consumes are `⟨log q⟩ = log Q − 1/2 + o(1)` and
`conductorSpread = O(1/ℒ)` (whose true size is `1/(4ℒ²)`). The budget's margin against these
is many orders; an extra `log Q / Q` in a term already `O(polylog Q / Q)` is invisible.
**This is now VERIFIED, not asserted, for EVERY consumer: all seven are proved, and every one
of them is proved from the weakened form.** No proof in this file cites a sharp `O(x log x)`;
the whole §12.2 chain hangs off `N2.Astar_bound`'s explicit
`|Σ_{q≤N} φ*(q) − (18/π⁴)N²| ≤ 5N(1 + log N)²`, which IS the `O(x log²x)` error at integer
argument. The chain and the price of the extra `log`, level by level:

* `N2.Astar_bound` : error `5N(1 + log N)²`      (the weakened N2 itself)
* `N2.Alog_bound`  : error `13N(1 + log N)³`     (one Abel summation against it)
* `N2.Alog2_bound` : error `30N(1 + log N)⁴`     (a second Abel summation against THAT)

Each Abel summation costs exactly one power of `log`, and each is then divided by
`Astar N ≍ (18/π⁴)N²`, so the relative errors are `O(log²x/x)`, `O(log³x/x)`, `O(log⁴x/x)` —
all `→ 0`, with explicit envelopes proved here (`N2.avgLog_limit` at `4000 log³x/x`,
`N2.Alog_sub_tendsto` at `200 log³x/x`, `N2.avgLogSq_limit` at `20000 log⁴x/x`). The three
`ℒ`-facing consumers then need only `o(1)` precision from the moments — `N9_facts` extracts
literally `|⟨log q⟩ − (log x − ½)| < 1` and `|⟨(log q)²⟩ − ((log x)² − log x + ½)| < 1` — against
targets `O(log log x/log x)` and `O(1/ℒ)`. **The margin is a full power of `x`**: the sharp
`O(x log x)` would improve the envelopes' `log`-power by one and change nothing at all. So the
D17 route-(b) weakening is not merely harmless in principle, it is harmless in the proofs that
are actually here.

The SECOND moment `Σ_{q≤N} φ*(q)(log q)²`, previously the one missing ingredient, is
`N2.Alog2_bound`: a second Abel summation of the same shape as `N2.Alog_bound`, main term
compared against the telescoping sequence `Ψ(t) = t²log t/2 − t²/2` by the same elementary
`1/(q+1) ≤ log(1 + 1/q) ≤ 1/q` — still no integrals, still no analytic input beyond the single
`Σ μ(d)/d² = 6/π²` of `N2.hasSum_mu_sq`.

Paper §12.2. Derivation: elementary; see the `N2` namespace above.
Depends on: `phiStar_eq_moebius_sum`, `Nat.sum_totient`, `riemannZeta_two`.
Rule 17: λ-free, X-free, D₀-free. -/
theorem sum_phiStar_asymp :
    (fun x : ℝ => (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ)) - (18 / Real.pi ^ 4) * x ^ 2)
      =O[atTop] (fun x : ℝ => x * Real.log x ^ 2) := N2.sum_phiStar_bigO

/-- **N3.** `|𝔉_Q| = (18/π⁴)Q²(1 + o(1))` (§2.2).

Paper §2.2/§12.2. Depends on: `sum_phiStar_asymp`.
Rule 17: λ-free. -/
theorem famCard_asymp :
    Tendsto (fun x : ℝ => famCardR x / x ^ 2) atTop (nhds (18 / Real.pi ^ 4)) := by
  have hA : ∀ x : ℝ, famCardR x = ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) := by
    intro x
    unfold famCardR ZetaQ.famCard
    push_cast
    rfl
  have hbig : (fun x : ℝ => famCardR x - (18 / Real.pi ^ 4) * x ^ 2)
      =O[atTop] (fun x : ℝ => x * Real.log x ^ 2) := by
    refine sum_phiStar_asymp.congr_left fun x => ?_
    rw [hA x]
  have hmul : (fun x : ℝ => (famCardR x - (18 / Real.pi ^ 4) * x ^ 2) * (x ^ 2)⁻¹)
      =O[atTop] (fun x : ℝ => (x * Real.log x ^ 2) * (x ^ 2)⁻¹) :=
    hbig.mul (isBigO_refl _ _)
  have hcong : (fun x : ℝ => (x * Real.log x ^ 2) * (x ^ 2)⁻¹)
      =ᶠ[atTop] (fun x : ℝ => Real.log x ^ 2 / x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hlog : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hzero : Tendsto (fun x : ℝ => (famCardR x - (18 / Real.pi ^ 4) * x ^ 2) * (x ^ 2)⁻¹)
      atTop (nhds 0) := (hmul.congr' EventuallyEq.rfl hcong).trans_tendsto hlog
  rw [← tendsto_sub_nhds_zero_iff]
  refine hzero.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

/-- **N4.** `C := Q²/|𝔉_Q| → π⁴/18 = ZetaQ.Cfam` (§2.2).

This is the constant §11's headline payoff is evaluated at.
Paper §2.2/§12.2. Depends on: `famCard_asymp`.
Rule 17: λ-free — `C` is a conductor-counting constant and carries no bandwidth information.
In particular `C` does not determine `λ*`; `λ*` is §11's free-boundary output. -/
theorem C_tendsto :
    Tendsto (fun x : ℝ => x ^ 2 / famCardR x) atTop (nhds ZetaQ.Cfam) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hne : (18 / Real.pi ^ 4 : ℝ) ≠ 0 := by positivity
  have h := famCard_asymp.inv₀ hne
  have hc : (18 / Real.pi ^ 4 : ℝ)⁻¹ = ZetaQ.Cfam := by
    unfold ZetaQ.Cfam
    rw [inv_div]
  rw [hc] at h
  refine h.congr fun x => ?_
  rw [inv_div]

/-- **N5a.** Dyadic: `Σ_{Q/2<q≤Q} φ*(q) = (27/2π⁴)Q²(1+o(1))` — the dyadic mass is `3/4` of
the full one.

Paper §12.2, Corollary 2.
Depends on: `sum_phiStar_asymp`. Rule 17: λ-free. -/
theorem famCardDyadic_asymp :
    Tendsto (fun x : ℝ => famCardDyadicR x / x ^ 2) atTop (nhds (27 / (2 * Real.pi ^ 4))) := by
  have hsplit : ∀ n : ℕ, ZetaQ.famCardDyadic n = ZetaQ.famCard n - ZetaQ.famCard (n / 2) := by
    intro n
    unfold ZetaQ.famCardDyadic ZetaQ.famCard
    have h1 : Finset.Icc 1 n = Finset.Ioc 0 n := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have h2 : Finset.Icc 1 (n / 2) = Finset.Ioc 0 (n / 2) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [h1, h2]
    have := Finset.sum_Ioc_consecutive (fun q => ZetaQ.phiStar q) (Nat.zero_le (n / 2))
      (Nat.div_le_self n 2)
    omega
  have hd : ∀ x : ℝ, famCardDyadicR x = famCardR x - famCardR (x / 2) := by
    intro x
    have hfl : ⌊x / 2⌋₊ = ⌊x⌋₊ / 2 := Nat.floor_div_ofNat x 2
    have hle : ZetaQ.famCard (⌊x⌋₊ / 2) ≤ ZetaQ.famCard ⌊x⌋₊ := by
      unfold ZetaQ.famCard
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
      exact Finset.Icc_subset_Icc_right (Nat.div_le_self _ _)
    unfold famCardDyadicR famCardR
    rw [hsplit ⌊x⌋₊, hfl, Nat.cast_sub hle]
  have hhalf : Tendsto (fun x : ℝ => x / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id
  have hcomp : Tendsto (fun x : ℝ => famCardR (x / 2) / (x / 2) ^ 2) atTop
      (nhds (18 / Real.pi ^ 4)) := famCard_asymp.comp hhalf
  have hlim : Tendsto (fun x : ℝ =>
      famCardR x / x ^ 2 - (1 / 4 : ℝ) * (famCardR (x / 2) / (x / 2) ^ 2)) atTop
      (nhds (18 / Real.pi ^ 4 - (1 / 4 : ℝ) * (18 / Real.pi ^ 4))) :=
    famCard_asymp.sub (hcomp.const_mul _)
  have hval : (18 / Real.pi ^ 4 - (1 / 4 : ℝ) * (18 / Real.pi ^ 4))
      = 27 / (2 * Real.pi ^ 4) := by
    have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [hd x]
  field_simp
  ring

/-- **N5b.** `C_dyad → 2π⁴/27 = ZetaQ.CfamDyadic` (Corollary 2).

Paper §12.2. Depends on: `famCardDyadic_asymp`.
Rule 17: λ-free. -/
theorem C_dyadic_tendsto :
    Tendsto (fun x : ℝ => x ^ 2 / famCardDyadicR x) atTop (nhds ZetaQ.CfamDyadic) := by
  have hne : (27 / (2 * Real.pi ^ 4) : ℝ) ≠ 0 := by
    have := Real.pi_pos
    positivity
  have h := famCardDyadic_asymp.inv₀ hne
  have hc : (27 / (2 * Real.pi ^ 4) : ℝ)⁻¹ = ZetaQ.CfamDyadic := by
    unfold ZetaQ.CfamDyadic
    rw [inv_div]
  rw [hc] at h
  refine h.congr fun x => ?_
  rw [inv_div]

/-- The φ*-WEIGHTED (character-count-weighted) conductor average over `q ≤ Q`.

Paper §12.2.
Depends on: `ZetaQ.phiStar`, `famCardR`. Rule 17: λ-free. -/
def avgLogCond (x : ℝ) : ℝ :=
  (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * Real.log (q : ℝ)) / famCardR x

/-- **N6.** `⟨log q⟩_{φ*, q ≤ Q} = log Q − 1/2 + o(1)`.

The φ*-WEIGHTED average; contrast the unweighted `log Q − 1` of N8. The weighting matters:
the certificate consumes character-count-weighted conductor data.
Paper §12.2. Derivation: partial summation of `log q` against N2, i.e. against
`dm = 2(18/π⁴)x dx`.
Depends on: `sum_phiStar_asymp`. Rule 17: λ-free, X-free, D₀-free. -/
theorem avgLogCond_asymp :
    Tendsto (fun x : ℝ => avgLogCond x - Real.log x) atTop (nhds (-(1 : ℝ) / 2)) := by
  have hA : ∀ x : ℝ, famCardR x = N2.Astar ⌊x⌋₊ := by
    intro x
    unfold famCardR ZetaQ.famCard N2.Astar
    push_cast
    rfl
  have hL : ∀ x : ℝ, avgLogCond x = N2.Alog ⌊x⌋₊ / N2.Astar ⌊x⌋₊ := by
    intro x
    unfold avgLogCond N2.Alog
    rw [hA x]
  refine Filter.Tendsto.congr (fun x => ?_) N2.avgLog_limit
  rw [hL x]

/-- The φ*-weighted conductor average over the DYADIC range `(Q/2, Q]` (Corollary 2).

Paper §12.2.
Depends on: `ZetaQ.phiStar`, `famCardDyadicR`. Rule 17: λ-free. -/
def avgLogCondDyadic (x : ℝ) : ℝ :=
  (∑ q ∈ Finset.Ioc (⌊x⌋₊ / 2) ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * Real.log (q : ℝ)) / famCardDyadicR x

/-- **N7.** `⟨log q⟩_{φ*, (Q/2,Q]} = log Q + (log 2)/3 − 1/2 + o(1)`.

This is Corollary 2 "paying its own constant, itemised": the dyadic subfamily has BOTH its own
`C = 2π⁴/27` and its own `⟨log q⟩`.
Paper §12.2. Depends on: `sum_phiStar_asymp`.
Rule 17: λ-free. -/
theorem avgLogCondDyadic_asymp :
    Tendsto (fun x : ℝ => avgLogCondDyadic x - Real.log x) atTop
      (nhds (Real.log 2 / 3 - 1 / 2)) := by
  have hAstarCast : ∀ n : ℕ, ((ZetaQ.famCard n : ℕ) : ℝ) = N2.Astar n := by
    intro n; unfold ZetaQ.famCard N2.Astar; push_cast; rfl
  have hq0 : Tendsto (fun x : ℝ => N2.Astar ⌊x⌋₊ / x ^ 2) atTop (nhds (18 / Real.pi ^ 4)) := by
    refine famCard_asymp.congr fun x => ?_
    unfold famCardR
    rw [hAstarCast]
  have hp0 := N2.Alog_sub_tendsto
  set c : ℝ := 18 / Real.pi ^ 4 with hc
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  have hhalf : Tendsto (fun x : ℝ => x / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id
  have hph : Tendsto (fun x : ℝ =>
      (N2.Alog ⌊x / 2⌋₊ - N2.Astar ⌊x / 2⌋₊ * Real.log (x / 2)) / (x / 2) ^ 2) atTop
      (nhds (-c / 2)) := hp0.comp hhalf
  have hqh : Tendsto (fun x : ℝ => N2.Astar ⌊x / 2⌋₊ / (x / 2) ^ 2) atTop (nhds c) :=
    hq0.comp hhalf
  -- the two `x²`-normalised pieces
  have hnum : Tendsto (fun x : ℝ =>
      ((N2.Alog ⌊x⌋₊ - N2.Astar ⌊x⌋₊ * Real.log x)
        - (N2.Alog ⌊x / 2⌋₊ - N2.Astar ⌊x / 2⌋₊ * Real.log x)) / x ^ 2) atTop
      (nhds (-c / 2 - 1 / 4 * (-c / 2) + Real.log 2 / 4 * c)) := by
    have hcomb := (hp0.sub (hph.const_mul (1/4 : ℝ))).add (hqh.const_mul (Real.log 2 / 4))
    refine hcomb.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hlog2 : Real.log (x / 2) = Real.log x - Real.log 2 :=
      Real.log_div hxne (by norm_num)
    rw [hlog2]
    field_simp
    ring
  have hden : Tendsto (fun x : ℝ =>
      (N2.Astar ⌊x⌋₊ - N2.Astar ⌊x / 2⌋₊) / x ^ 2) atTop (nhds (c - 1 / 4 * c)) := by
    have hcomb := hq0.sub (hqh.const_mul (1/4 : ℝ))
    refine hcomb.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    field_simp
    ring
  have hvpos : (0:ℝ) < c - 1 / 4 * c := by
    rw [show c - 1 / 4 * c = (3/4) * c by ring]
    positivity
  have hDpos : ∀ᶠ x : ℝ in atTop,
      (0:ℝ) < (N2.Astar ⌊x⌋₊ - N2.Astar ⌊x / 2⌋₊) / x ^ 2 :=
    hden.eventually (eventually_gt_nhds hvpos)
  have hdiv := hnum.div hden (ne_of_gt hvpos)
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hval : (-c / 2 - 1 / 4 * (-c / 2) + Real.log 2 / 4 * c) / (c - 1 / 4 * c)
      = Real.log 2 / 3 - 1 / 2 := by
    field_simp
    ring
  rw [hval] at hdiv
  -- the two combinatorial identities tying the dyadic block to `N2`
  have hnumer : ∀ y : ℝ,
      (∑ q ∈ Finset.Ioc (⌊y⌋₊ / 2) ⌊y⌋₊, (ZetaQ.phiStar q : ℝ) * Real.log (q : ℝ))
        = N2.Alog ⌊y⌋₊ - N2.Alog ⌊y / 2⌋₊ := by
    intro y
    have hfl : ⌊y / 2⌋₊ = ⌊y⌋₊ / 2 := Nat.floor_div_ofNat y 2
    have hIccN : Finset.Icc 1 ⌊y⌋₊ = Finset.Ioc 0 ⌊y⌋₊ := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have hIccM : Finset.Icc 1 (⌊y⌋₊ / 2) = Finset.Ioc 0 (⌊y⌋₊ / 2) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have hcons := Finset.sum_Ioc_consecutive
      (fun q : ℕ => (ZetaQ.phiStar q : ℝ) * Real.log (q : ℝ))
      (Nat.zero_le (⌊y⌋₊ / 2)) (Nat.div_le_self ⌊y⌋₊ 2)
    unfold N2.Alog
    rw [hfl, hIccN, hIccM]
    linarith [hcons]
  have hsplitN : ∀ n : ℕ, ZetaQ.famCardDyadic n = ZetaQ.famCard n - ZetaQ.famCard (n / 2) := by
    intro n
    unfold ZetaQ.famCardDyadic ZetaQ.famCard
    have h1 : Finset.Icc 1 n = Finset.Ioc 0 n := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have h2 : Finset.Icc 1 (n / 2) = Finset.Ioc 0 (n / 2) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [h1, h2]
    have := Finset.sum_Ioc_consecutive (fun q => ZetaQ.phiStar q) (Nat.zero_le (n / 2))
      (Nat.div_le_self n 2)
    omega
  have hdenom : ∀ y : ℝ, famCardDyadicR y = N2.Astar ⌊y⌋₊ - N2.Astar ⌊y / 2⌋₊ := by
    intro y
    have hfl : ⌊y / 2⌋₊ = ⌊y⌋₊ / 2 := Nat.floor_div_ofNat y 2
    have hle : ZetaQ.famCard (⌊y⌋₊ / 2) ≤ ZetaQ.famCard ⌊y⌋₊ := by
      unfold ZetaQ.famCard
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
      exact Finset.Icc_subset_Icc_right (Nat.div_le_self _ _)
    unfold famCardDyadicR
    rw [hsplitN ⌊y⌋₊, Nat.cast_sub hle, hAstarCast, hAstarCast, hfl]
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ), hDpos] with x hx hD
  have hxne : x ≠ 0 := ne_of_gt hx
  have hDne : (N2.Astar ⌊x⌋₊ - N2.Astar ⌊x / 2⌋₊) ≠ 0 := by
    intro h
    rw [h] at hD
    simp at hD
  simp only [Pi.div_apply]
  unfold avgLogCondDyadic
  rw [hnumer x, hdenom x]
  have hx2 : (x:ℝ) ^ 2 ≠ 0 := by positivity
  rw [div_div_div_comm, div_self hx2, div_one]
  field_simp
  ring

/-- The paper's decimal for N7: `log Q + (log 2)/3 − 1/2 = log Q − 0.26895…`.

Paper §12.2.
Depends on: nothing. Rule 17: λ-free. -/
theorem avgLogCondDyadic_digits :
    |Real.log 2 / 3 - 1 / 2 - (-0.26895 : ℝ)| ≤ (1 : ℝ) / 10 ^ 5 := by
  have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  rw [abs_le]
  constructor <;> norm_num <;> linarith

/-! ### Elementary factorial bounds for the unweighted contrasts N8a/N8b

`log(N!) = N log N − N + O(log N)`, proved by induction from `log t ≤ t − 1` alone — Mathlib's
`Stirling` gives the sharper asymptotic but is not needed and is not cited. -/

/-- **Fill-local helper**: `Σ_{1 ≤ j ≤ N} log j = log(N!)`. -/
private theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, Real.log (j : ℝ) = Real.log (Nat.factorial N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    ring

/-- **Fill-local helper** (Stirling, lower half, Mathlib-free): `N log N − N ≤ log(N!)`.
The inductive step is `log(1 + 1/N) ≤ 1/N`. -/
private theorem log_factorial_lower (N : ℕ) :
    (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ Real.log (Nat.factorial N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
      have hfac : Real.log (Nat.factorial (N + 1) : ℝ)
          = Real.log ((N : ℝ) + 1) + Real.log (Nat.factorial N : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        rw [Real.log_mul (by positivity) (by positivity)]
      have hlog : Real.log (((N : ℝ) + 1) / (N : ℝ)) ≤ 1 / (N : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (x := ((N : ℝ) + 1) / (N : ℝ)) (by positivity)
        have heq : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by
          field_simp
          ring
        linarith [heq ▸ h]
      have hstep : (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) ≤ 1 := by
        rw [← Real.log_div (by positivity) (by positivity)]
        calc (N : ℝ) * Real.log (((N : ℝ) + 1) / (N : ℝ))
            ≤ (N : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = 1 := by field_simp
      push_cast
      rw [hfac]
      nlinarith [ih, hstep]

/-- **Fill-local helper** (Stirling, upper half): `log(N!) ≤ (N+1)log(N+1) − N`.
The inductive step is `log(1 + 1/(N+1)) ≥ 1/(N+2)`. -/
private theorem log_factorial_upper (N : ℕ) :
    Real.log (Nat.factorial N : ℝ) ≤ ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hfac : Real.log (Nat.factorial (N + 1) : ℝ)
        = Real.log ((N : ℝ) + 1) + Real.log (Nat.factorial N : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      rw [Real.log_mul (by positivity) (by positivity)]
    have hlog : Real.log (((N : ℝ) + 1) / ((N : ℝ) + 2)) ≤ -(1 / ((N : ℝ) + 2)) := by
      have h := Real.log_le_sub_one_of_pos
        (x := ((N : ℝ) + 1) / ((N : ℝ) + 2)) (by positivity)
      have heq : ((N : ℝ) + 1) / ((N : ℝ) + 2) - 1 = -(1 / ((N : ℝ) + 2)) := by
        field_simp
        ring
      linarith [heq ▸ h]
    have hstep : (1 : ℝ)
        ≤ ((N : ℝ) + 2) * (Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1)) := by
      have hd : Real.log (((N : ℝ) + 1) / ((N : ℝ) + 2))
          = Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + 2) :=
        Real.log_div (by positivity) (by positivity)
      rw [hd] at hlog
      have h2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hlog h2.le
      have heq2 : ((N : ℝ) + 2) * -(1 / ((N : ℝ) + 2)) = -1 := by field_simp
      nlinarith [hmul, heq2]
    push_cast
    rw [hfac]
    have hr : (N : ℝ) + 1 + 1 = (N : ℝ) + 2 := by ring
    rw [hr]
    nlinarith [hstep, ih]

/-- **Fill-local helper**: `log(M!) = y log y − y + O(log y)` whenever `M = ⌊y⌋`. -/
private theorem log_factorial_approx (y : ℝ) (M : ℕ) (hy : 1 ≤ y) (hM1 : 1 ≤ M)
    (hMy : (M : ℝ) ≤ y) (hyM : y ≤ (M : ℝ) + 1) :
    |Real.log (Nat.factorial M : ℝ) - (y * Real.log y - y)| ≤ 2 + Real.log 2 + Real.log y := by
  have hypos : (0 : ℝ) < y := by linarith
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hlogM : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hMR
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hlow := log_factorial_lower M
  have hup := log_factorial_upper M
  have hmono1 : (M : ℝ) * Real.log (M : ℝ) ≤ y * Real.log y := by
    have hl : Real.log (M : ℝ) ≤ Real.log y := Real.log_le_log (by linarith) hMy
    nlinarith
  have hmono2 : y * Real.log y ≤ ((M : ℝ) + 1) * Real.log ((M : ℝ) + 1) := by
    have hl : Real.log y ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log hypos hyM
    nlinarith
  have hgap : ((M : ℝ) + 1) * Real.log ((M : ℝ) + 1) - (M : ℝ) * Real.log (M : ℝ)
      ≤ 1 + Real.log ((M : ℝ) + 1) := by
    have hlog : Real.log (((M : ℝ) + 1) / (M : ℝ)) ≤ 1 / (M : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 1) / (M : ℝ)) (by positivity)
      have heq : ((M : ℝ) + 1) / (M : ℝ) - 1 = 1 / (M : ℝ) := by
        field_simp
        ring
      linarith [heq ▸ h]
    have hd : Real.log (((M : ℝ) + 1) / (M : ℝ))
        = Real.log ((M : ℝ) + 1) - Real.log (M : ℝ) :=
      Real.log_div (by positivity) (by positivity)
    rw [hd] at hlog
    have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlog hMpos.le
    have heq2 : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
    nlinarith
  have hlogM1 : Real.log ((M : ℝ) + 1) ≤ Real.log 2 + Real.log y := by
    have h2y : (M : ℝ) + 1 ≤ 2 * y := by linarith
    have h := Real.log_le_log (by positivity) h2y
    rwa [Real.log_mul (by norm_num) (ne_of_gt hypos)] at h
  rw [abs_le]
  constructor <;> linarith

/-- **Fill-local helper**: `(2 + log 2 + log x)/x → 0`. -/
private theorem tendsto_log_bound_div : Tendsto
    (fun x : ℝ => (2 + Real.log 2 + Real.log x) / x) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => (2 + Real.log 2) / x) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 + Real.log 2 : ℝ)) (f := atTop (α := ℝ))).div_atTop
      tendsto_id
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

/-- **N8a.** The UNWEIGHTED contrast over `q ≤ Q`: `log Q − 1`.

Stated "for contrast"; **the certificate does NOT consume this** — the unweighted averages
exist in §12.2 only to locate the Fiorilli–Miller quantity relative to the φ*-weighted one.
Paper §12.2. Depends on: nothing.
Rule 17: λ-free. -/
theorem avgLogCond_unweighted_asymp :
    Tendsto (fun x : ℝ => (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (q : ℝ)) / x - Real.log x) atTop
      (nhds (-1 : ℝ)) := by
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖(∑ q ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (q : ℝ)) / x - Real.log x + 1‖
        ≤ (2 + Real.log 2 + Real.log x) / x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    set N : ℕ := ⌊x⌋₊ with hN
    have hxpos : (0 : ℝ) < x := by linarith
    have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
    have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hxN : x ≤ (N : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one x)
    have hS : ∑ q ∈ Finset.Icc 1 N, Real.log (q : ℝ) = Real.log (Nat.factorial N : ℝ) :=
      sum_log_eq_log_factorial N
    have habs := log_factorial_approx x N hx hN1 hNx hxN
    rw [Real.norm_eq_abs, hN, ← hN, hS]
    have heq : Real.log (Nat.factorial N : ℝ) / x - Real.log x + 1
        = (Real.log (Nat.factorial N : ℝ) - (x * Real.log x - x)) / x := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hxpos]
    have hinv : (0 : ℝ) ≤ x⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_right habs hinv
    simpa [div_eq_mul_inv] using hmul
  have hzero : Tendsto
      (fun x : ℝ => (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (q : ℝ)) / x - Real.log x + 1)
      atTop (nhds 0) := squeeze_zero_norm' hbound tendsto_log_bound_div
  have h := hzero.sub_const 1
  simpa using h

/-- **N8b.** The UNWEIGHTED dyadic contrast: `log Q + log 2 − 1 = log Q − 0.30685…`.
Not consumed; see N8a.

Paper §12.2. Depends on: nothing. Rule 17: λ-free. -/
theorem avgLogCondDyadic_unweighted_asymp :
    Tendsto
      (fun x : ℝ =>
        (∑ q ∈ Finset.Ioc (⌊x⌋₊ / 2) ⌊x⌋₊, Real.log (q : ℝ)) / (x / 2) - Real.log x)
      atTop (nhds (Real.log 2 - 1)) := by
  have hg : Tendsto (fun x : ℝ => 4 * ((2 + Real.log 2 + Real.log x) / x)) atTop (nhds 0) := by
    simpa using tendsto_log_bound_div.const_mul (4 : ℝ)
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖(∑ q ∈ Finset.Ioc (⌊x⌋₊ / 2) ⌊x⌋₊, Real.log (q : ℝ)) / (x / 2) - Real.log x
          - (Real.log 2 - 1)‖
        ≤ 4 * ((2 + Real.log 2 + Real.log x) / x) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hxpos : (0 : ℝ) < x := by linarith
    set N : ℕ := ⌊x⌋₊ with hN
    set M : ℕ := N / 2 with hM
    have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx1
    have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hxN : x ≤ (N : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one x)
    -- `M = ⌊x/2⌋`
    have hMfl : M = ⌊x / 2⌋₊ := by
      rw [hM, hN, Nat.floor_div_ofNat x 2]
    have hhalf1 : (1 : ℝ) ≤ x / 2 := by linarith
    have hM1 : 1 ≤ M := by
      rw [hMfl]
      exact (Nat.one_le_floor_iff (x / 2)).mpr hhalf1
    have hMy : (M : ℝ) ≤ x / 2 := by
      rw [hMfl]
      exact Nat.floor_le (by linarith)
    have hyM : x / 2 ≤ (M : ℝ) + 1 := by
      rw [hMfl]
      exact le_of_lt (Nat.lt_floor_add_one (x / 2))
    -- the dyadic block sum is a difference of two factorials
    have hsplit : ∑ q ∈ Finset.Ioc M N, Real.log (q : ℝ)
        = Real.log (Nat.factorial N : ℝ) - Real.log (Nat.factorial M : ℝ) := by
      have hIccN : Finset.Icc 1 N = Finset.Ioc 0 N := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      have hIccM : Finset.Icc 1 M = Finset.Ioc 0 M := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      have hMN : M ≤ N := by
        rw [hM]
        exact Nat.div_le_self N 2
      have hcons := Finset.sum_Ioc_consecutive (fun q : ℕ => Real.log (q : ℝ))
        (Nat.zero_le M) hMN
      have hSN := sum_log_eq_log_factorial N
      have hSM := sum_log_eq_log_factorial M
      rw [hIccN] at hSN
      rw [hIccM] at hSM
      linarith [hcons, hSN, hSM]
    have hA := log_factorial_approx x N hx1 hN1 hNx hxN
    have hB := log_factorial_approx (x / 2) M hhalf1 hM1 hMy hyM
    have hlogh : Real.log (x / 2) = Real.log x - Real.log 2 :=
      Real.log_div (ne_of_gt hxpos) (by norm_num)
    have hlogmono : Real.log (x / 2) ≤ Real.log x := by
      rw [hlogh]
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have hB' : |Real.log (Nat.factorial M : ℝ) - (x / 2 * Real.log (x / 2) - x / 2)|
        ≤ 2 + Real.log 2 + Real.log x := le_trans hB (by linarith)
    rw [Real.norm_eq_abs, hsplit]
    have heq : (Real.log (Nat.factorial N : ℝ) - Real.log (Nat.factorial M : ℝ)) / (x / 2)
          - Real.log x - (Real.log 2 - 1)
        = ((Real.log (Nat.factorial N : ℝ) - (x * Real.log x - x))
            - (Real.log (Nat.factorial M : ℝ) - (x / 2 * Real.log (x / 2) - x / 2)))
          / (x / 2) := by
      have hxne : x ≠ 0 := ne_of_gt hxpos
      rw [hlogh]
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos (by linarith : (0 : ℝ) < x / 2)]
    have hnum : |(Real.log (Nat.factorial N : ℝ) - (x * Real.log x - x))
          - (Real.log (Nat.factorial M : ℝ) - (x / 2 * Real.log (x / 2) - x / 2))|
        ≤ 2 * (2 + Real.log 2 + Real.log x) := by
      have h1 := abs_le.mp hA
      have h2 := abs_le.mp hB'
      rw [abs_le]
      constructor <;> linarith
    have hrhs : 4 * ((2 + Real.log 2 + Real.log x) / x)
        = (2 * (2 + Real.log 2 + Real.log x)) / (x / 2) := by
      field_simp
      ring
    rw [hrhs]
    have hinv : (0 : ℝ) ≤ (x / 2)⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_right hnum hinv
    simpa [div_eq_mul_inv] using hmul
  have hzero : Tendsto
      (fun x : ℝ =>
        (∑ q ∈ Finset.Ioc (⌊x⌋₊ / 2) ⌊x⌋₊, Real.log (q : ℝ)) / (x / 2) - Real.log x
          - (Real.log 2 - 1))
      atTop (nhds 0) := squeeze_zero_norm' hbound hg
  have h := hzero.add_const (Real.log 2 - 1)
  simpa using h

/-- `ℒ(Q) = log(Q·T(Q)/2π)` — the paper's common scale, as a function of `Q` at a
conductor-dependent height `T` (§2.2 sets `T = (log Q)^{r+ε}`).

Carried as a FUNCTION rather than a `ParamsQ` field because N9/N10 are asymptotic statements
in `Q`, i.e. statements about a family of design points.
Paper §2.2.
Depends on: nothing. Rule 17: λ-free — this is `ℒ`, not `L = λℒ`. -/
def LLof (T : ℝ → ℝ) (x : ℝ) : ℝ := Real.log (x * T x / (2 * Real.pi))

/-- `c_q := log q / ℒ`.
Depends on: `LLof`. Rule 17: λ-free. -/
def cq (T : ℝ → ℝ) (x : ℝ) (q : ℕ) : ℝ := Real.log (q : ℝ) / LLof T x

/-- `⟨c⟩` — the φ*-weighted first moment of `c_q`. Depends on: `cq`, `famCardR`.
Rule 17: λ-free. -/
def avgC (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q) / famCardR x

/-- `⟨c²⟩` — the φ*-weighted second moment of `c_q`. Rule 17: λ-free. -/
def avgCsq (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q ^ 2) / famCardR x

/-- `⟨c^k⟩` — the φ*-weighted `k`-th moment, for N11. Rule 17: λ-free. -/
def avgCpow (T : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q ^ k) / famCardR x

/-- The φ*-WEIGHTED SECOND log-moment of the conductor over `q ≤ Q`. Fill-local: N9a/N10
consume `⟨c²⟩ = ⟨(log q)²⟩/ℒ²`, and this is the numerator. -/
def avgLogCondSq (x : ℝ) : ℝ :=
  (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * Real.log (q : ℝ) ^ 2) / famCardR x

/-- The second-moment companion of N6: `⟨(log q)²⟩ = (log Q)² − log Q + ½ + o(1)`.
Proved from `N2.Alog2_bound` exactly as N6 is proved from `N2.Alog_bound`. -/
theorem avgLogCondSq_asymp :
    Tendsto (fun x : ℝ => avgLogCondSq x - Real.log x ^ 2 + Real.log x) atTop (nhds (1/2)) := by
  have hA : ∀ x : ℝ, famCardR x = N2.Astar ⌊x⌋₊ := by
    intro x
    unfold famCardR ZetaQ.famCard N2.Astar
    push_cast
    rfl
  have hL : ∀ x : ℝ, avgLogCondSq x = N2.Alog2 ⌊x⌋₊ / N2.Astar ⌊x⌋₊ := by
    intro x
    unfold avgLogCondSq N2.Alog2
    rw [hA x]
  refine Filter.Tendsto.congr (fun x => ?_) N2.avgLogSq_limit
  rw [hL x]

/-- `⟨c⟩ = ⟨log q⟩/ℒ` — the scale factors straight out of the φ*-weighted sum. -/
theorem avgC_eq (T : ℝ → ℝ) (x : ℝ) : avgC T x = avgLogCond x / LLof T x := by
  have hs : ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q
      = (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * Real.log (q : ℝ)) / LLof T x := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold cq
    rw [mul_div_assoc]
  unfold avgC avgLogCond
  rw [hs, div_div, div_div, mul_comm (LLof T x) (famCardR x)]

/-- `⟨c²⟩ = ⟨(log q)²⟩/ℒ²`. -/
theorem avgCsq_eq (T : ℝ → ℝ) (x : ℝ) : avgCsq T x = avgLogCondSq x / LLof T x ^ 2 := by
  have hs : ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q ^ 2
      = (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * Real.log (q : ℝ) ^ 2)
        / LLof T x ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold cq
    rw [div_pow, mul_div_assoc]
  unfold avgCsq avgLogCondSq
  rw [hs, div_div, div_div, mul_comm (LLof T x ^ 2) (famCardR x)]

/-- The eventual facts shared by N9a, N9b and N10: `ℒ` is pinned between `log x − 3` and
`log x + C log log x` (this is exactly `hT`, i.e. `T = (log Q)^{r+ε}`), and both log-moments
are within `1` of their asymptotic values. -/
theorem N9_facts (T : ℝ → ℝ)
    (hT1 : ∀ᶠ x in atTop, 1 ≤ T x)
    (hT : (fun x : ℝ => Real.log (T x)) =O[atTop] (fun x : ℝ => Real.log (Real.log x))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      12 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x)
      ∧ Real.log x - 3 ≤ LLof T x
      ∧ LLof T x ≤ Real.log x + C * Real.log (Real.log x)
      ∧ |avgLogCond x - Real.log x + 1 / 2| < 1
      ∧ |avgLogCondSq x - Real.log x ^ 2 + Real.log x - 1 / 2| < 1 := by
  obtain ⟨C, hC0, hCb⟩ := hT.exists_pos
  rw [Asymptotics.isBigOWith_iff] at hCb
  have hac : ∀ᶠ x : ℝ in atTop, |avgLogCond x - Real.log x + 1 / 2| < 1 := by
    have h1 : Tendsto (fun x : ℝ => avgLogCond x - Real.log x + 1 / 2) atTop (nhds 0) := by
      have h := avgLogCond_asymp.add_const (1 / 2 : ℝ)
      have he : (-(1 : ℝ) / 2 + 1 / 2) = 0 := by norm_num
      rwa [he] at h
    have h0 : Tendsto (fun x : ℝ => |avgLogCond x - Real.log x + 1 / 2|) atTop (nhds 0) := by
      simpa using h1.abs
    exact h0.eventually_lt_const (by norm_num)
  have hac2 : ∀ᶠ x : ℝ in atTop,
      |avgLogCondSq x - Real.log x ^ 2 + Real.log x - 1 / 2| < 1 := by
    have h1 : Tendsto (fun x : ℝ => avgLogCondSq x - Real.log x ^ 2 + Real.log x - 1 / 2)
        atTop (nhds 0) := by
      have h := avgLogCondSq_asymp.sub_const (1 / 2 : ℝ)
      have he : ((1 : ℝ) / 2 - 1 / 2) = 0 := by norm_num
      rwa [he] at h
    have h0 : Tendsto
        (fun x : ℝ => |avgLogCondSq x - Real.log x ^ 2 + Real.log x - 1 / 2|)
        atTop (nhds 0) := by simpa using h1.abs
    exact h0.eventually_lt_const (by norm_num)
  have h2pi : Real.log (2 * Real.pi) ≤ 3 := by
    have h8 : (2 : ℝ) * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have hle := Real.log_le_log (by positivity : (0:ℝ) < 2 * Real.pi) h8
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    rw [hl8] at hle
    linarith [Real.log_two_lt_d9]
  have h2pi0 : (0 : ℝ) ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hT1, hCb, hac, hac2, eventually_ge_atTop (262144 : ℝ)]
    with x hTx hCx hax hax2 hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : (12 : ℝ) ≤ Real.log x := by
    have h2 : Real.log 262144 = 18 * Real.log 2 := by
      rw [show (262144 : ℝ) = 2 ^ 18 by norm_num, Real.log_pow]; push_cast; ring
    have h3 : (12 : ℝ) ≤ Real.log 262144 := by rw [h2]; linarith [Real.log_two_gt_d9]
    exact le_trans h3 (Real.log_le_log (by norm_num) hx)
  have hll : (1 : ℝ) ≤ Real.log (Real.log x) := by
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
      linarith [Real.log_two_gt_d9]
    exact le_trans h4 (Real.log_le_log (by norm_num) (by linarith))
  have hTxpos : (0 : ℝ) < T x := by linarith
  have hLL : LLof T x = Real.log x + Real.log (T x) - Real.log (2 * Real.pi) := by
    unfold LLof
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlogT0 : (0 : ℝ) ≤ Real.log (T x) := Real.log_nonneg hTx
  have hlogTb : Real.log (T x) ≤ C * Real.log (Real.log x) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogT0,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log (Real.log x))] at hCx
    exact hCx
  exact ⟨hlogx, hll, by rw [hLL]; linarith, by rw [hLL]; linarith, hax, hax2⟩

/-- **N9a, the ratio-of-sums discipline.** `⟨c²⟩/⟨c⟩ = 1 + O(log log Q / log Q)`.

Paper §12.2: "the certificate consumes a ratio of sums, never an average of ratios". The rate
is driven by `log T/ℒ`, which is the content of the hypothesis `hT`.
Depends on: `sum_phiStar_asymp`, `avgLogCond_asymp`.
**Rule 17:** `hT` bounds `log T` against `log log Q` — this is `T = (log Q)^{r+ε}` of §2.2 and
says NOTHING about `X` or `λ`. It is emphatically not `X ≤ T`: in this paper
`X = (QT/2π)^λ ≫ T` always. -/
theorem ratio_of_sums_bound (T : ℝ → ℝ)
    (hT1 : ∀ᶠ x in atTop, 1 ≤ T x)
    (hT : (fun x : ℝ => Real.log (T x)) =O[atTop] (fun x : ℝ => Real.log (Real.log x))) :
    (fun x : ℝ => avgCsq T x / avgC T x - 1)
      =O[atTop] (fun x : ℝ => Real.log (Real.log x) / Real.log x) := by
  obtain ⟨C, hC0, hfacts⟩ := N9_facts T hT1 hT
  refine Asymptotics.IsBigO.of_bound (4 * C + 18) ?_
  filter_upwards [hfacts] with x hfx
  obtain ⟨hlx, hll, hLlow, hLup, hax, hax2⟩ := hfx
  rw [abs_lt] at hax hax2
  have hlx0 : (0 : ℝ) < Real.log x := by linarith
  have hAlow : Real.log x - 3 / 2 ≤ avgLogCond x := by linarith [hax.1]
  have hAup : avgLogCond x ≤ Real.log x + 1 / 2 := by linarith [hax.2]
  have hSlow : Real.log x ^ 2 - Real.log x - 1 / 2 ≤ avgLogCondSq x := by linarith [hax2.1]
  have hSup : avgLogCondSq x ≤ Real.log x ^ 2 - Real.log x + 3 / 2 := by linarith [hax2.2]
  have hAvg34 : (3 / 4) * Real.log x ≤ avgLogCond x := by linarith
  have hAvgpos : (0 : ℝ) < avgLogCond x := by linarith
  have hL34 : (3 / 4) * Real.log x ≤ LLof T x := by linarith
  have hLpos : (0 : ℝ) < LLof T x := by linarith
  have hLne : LLof T x ≠ 0 := ne_of_gt hLpos
  have hAne : avgLogCond x ≠ 0 := ne_of_gt hAvgpos
  have hprodpos : (0 : ℝ) < LLof T x * avgLogCond x := mul_pos hLpos hAvgpos
  have hratio : avgCsq T x / avgC T x - 1
      = (avgLogCondSq x - LLof T x * avgLogCond x) / (LLof T x * avgLogCond x) := by
    rw [avgCsq_eq, avgC_eq]
    field_simp
  -- the numerator: the `(log x)²` terms cancel, leaving `O(log x · log log x)`
  have hnumb : |avgLogCondSq x - LLof T x * avgLogCond x|
      ≤ (2 * C + 9) * (Real.log x * Real.log (Real.log x)) := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.log x + C * Real.log (Real.log x)
          - LLof T x) hAvgpos.le,
        mul_nonneg (by nlinarith [hC0, hll, hlx0] :
          (0:ℝ) ≤ Real.log x + C * Real.log (Real.log x))
          (by linarith : (0:ℝ) ≤ Real.log x + 1/2 - avgLogCond x),
        mul_nonneg (mul_nonneg hC0.le (by linarith : (0:ℝ) ≤ Real.log (Real.log x)))
          (by linarith : (0:ℝ) ≤ Real.log x - 1/2),
        mul_nonneg hlx0.le (by linarith : (0:ℝ) ≤ Real.log (Real.log x) - 1)]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ LLof T x - (Real.log x - 3)) hAvgpos.le,
        mul_nonneg (by linarith : (0:ℝ) ≤ Real.log x - 3)
          (by linarith : (0:ℝ) ≤ avgLogCond x - (Real.log x - 3/2)),
        mul_nonneg hlx0.le (by linarith : (0:ℝ) ≤ Real.log (Real.log x) - 1),
        mul_nonneg (mul_nonneg hC0.le hlx0.le)
          (by linarith : (0:ℝ) ≤ Real.log (Real.log x))]
  have hWLpos : (0 : ℝ) < Real.log (Real.log x) / Real.log x := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hratio, abs_div, abs_of_pos hprodpos,
    abs_of_pos hWLpos, div_le_iff₀ hprodpos]
  have hlow : (9 / 16) * Real.log x ^ 2 ≤ LLof T x * avgLogCond x := by nlinarith [hL34, hAvg34]
  have hcoef : (0 : ℝ) ≤ (4 * C + 18) * (Real.log (Real.log x) / Real.log x) := by positivity
  have hmono := mul_le_mul_of_nonneg_left hlow hcoef
  have heq : (4 * C + 18) * (Real.log (Real.log x) / Real.log x) * ((9 / 16) * Real.log x ^ 2)
      = (9 / 16) * (4 * C + 18) * (Real.log x * Real.log (Real.log x)) := by
    field_simp
  rw [heq] at hmono
  have hslack : (2 * C + 9) * (Real.log x * Real.log (Real.log x))
      ≤ (9 / 16) * (4 * C + 18) * (Real.log x * Real.log (Real.log x)) := by
    nlinarith [mul_nonneg hlx0.le (by linarith : (0:ℝ) ≤ Real.log (Real.log x)), hC0]
  linarith [hnumb, hmono, hslack]

/-- **N9b.** `1/⟨c⟩ = 1 + O(log log Q / log Q)`. Same discipline, same
rate, same driver.

Paper §12.2. Depends on: `sum_phiStar_asymp`.
Rule 17: as N9a. -/
theorem inv_avgC_bound (T : ℝ → ℝ)
    (hT1 : ∀ᶠ x in atTop, 1 ≤ T x)
    (hT : (fun x : ℝ => Real.log (T x)) =O[atTop] (fun x : ℝ => Real.log (Real.log x))) :
    (fun x : ℝ => 1 / avgC T x - 1)
      =O[atTop] (fun x : ℝ => Real.log (Real.log x) / Real.log x) := by
  obtain ⟨C, hC0, hCb⟩ := hT.exists_pos
  rw [Asymptotics.isBigOWith_iff] at hCb
  have hac : ∀ᶠ x : ℝ in atTop, |avgLogCond x - Real.log x + 1 / 2| < 1 := by
    have h1 : Tendsto (fun x : ℝ => avgLogCond x - Real.log x + 1 / 2) atTop (nhds 0) := by
      have h := avgLogCond_asymp.add_const (1 / 2 : ℝ)
      have he : (-(1 : ℝ) / 2 + 1 / 2) = 0 := by norm_num
      rwa [he] at h
    have h0 : Tendsto (fun x : ℝ => |avgLogCond x - Real.log x + 1 / 2|) atTop (nhds 0) := by
      simpa using h1.abs
    exact h0.eventually_lt_const (by norm_num)
  refine Asymptotics.IsBigO.of_bound (2 * C + 10) ?_
  filter_upwards [hT1, hCb, hac, eventually_ge_atTop (4096 : ℝ)] with x hTx hCx hax hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx8 : (8 : ℝ) ≤ Real.log x := by
    have h2 : Real.log 4096 = 12 * Real.log 2 := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; push_cast; ring
    have h3 : (8 : ℝ) ≤ Real.log 4096 := by rw [h2]; linarith [Real.log_two_gt_d9]
    exact le_trans h3 (Real.log_le_log (by norm_num) hx)
  have hll : (1 : ℝ) ≤ Real.log (Real.log x) := by
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
      linarith [Real.log_two_gt_d9]
    exact le_trans h4 (Real.log_le_log (by norm_num) (by linarith))
  have hTxpos : (0 : ℝ) < T x := by linarith
  have hLL : LLof T x = Real.log x + Real.log (T x) - Real.log (2 * Real.pi) := by
    unfold LLof
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlogT0 : (0 : ℝ) ≤ Real.log (T x) := Real.log_nonneg hTx
  have hlogTb : Real.log (T x) ≤ C * Real.log (Real.log x) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogT0,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log (Real.log x))] at hCx
    exact hCx
  have h2pi : Real.log (2 * Real.pi) ≤ 3 := by
    have h8 : (2 : ℝ) * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have hle := Real.log_le_log (by positivity : (0:ℝ) < 2 * Real.pi) h8
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    rw [hl8] at hle
    linarith [Real.log_two_lt_d9]
  have h2pi0 : (0 : ℝ) ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  rw [abs_lt] at hax
  have hAvg34 : (3 / 4) * Real.log x ≤ avgLogCond x := by linarith [hax.1]
  have hAvgpos : (0 : ℝ) < avgLogCond x := by linarith
  have hLpos : (0 : ℝ) < LLof T x := by rw [hLL]; linarith
  have hACeq : avgC T x = avgLogCond x / LLof T x := by
    have hs : ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q
        = (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * Real.log (q : ℝ)) / LLof T x := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun q _ => ?_
      unfold cq
      rw [mul_div_assoc]
    unfold avgC avgLogCond
    rw [hs, div_div, div_div, mul_comm (LLof T x) (famCardR x)]
  have hrw : 1 / avgC T x - 1 = (LLof T x - avgLogCond x) / avgLogCond x := by
    rw [hACeq, one_div_div]
    field_simp
  have hnum : |LLof T x - avgLogCond x| ≤ (C + 5) * Real.log (Real.log x) := by
    rw [hLL, abs_le]
    constructor <;> nlinarith [hax.1, hax.2, hlogTb, hlogT0, h2pi, h2pi0, hll, hC0]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hrw, abs_div, abs_of_pos hAvgpos,
    abs_of_pos (by positivity : (0 : ℝ) < Real.log (Real.log x) / Real.log x),
    div_le_iff₀ hAvgpos]
  have hlx : (0 : ℝ) < Real.log x := by linarith
  have hkey : (2 * C + 10) * (Real.log (Real.log x) / Real.log x) * ((3 / 4) * Real.log x)
      = (3 / 2 * C + 15 / 2) * Real.log (Real.log x) := by
    field_simp
    ring
  have hmono : (2 * C + 10) * (Real.log (Real.log x) / Real.log x) * ((3 / 4) * Real.log x)
      ≤ (2 * C + 10) * (Real.log (Real.log x) / Real.log x) * avgLogCond x := by
    have hc0 : (0 : ℝ) ≤ (2 * C + 10) * (Real.log (Real.log x) / Real.log x) := by positivity
    exact mul_le_mul_of_nonneg_left hAvg34 hc0
  rw [hkey] at hmono
  nlinarith [hnum, hmono, hll, hC0]

/-- The conductor-SPREAD contribution: the φ*-weighted variance of `c_q`.

Paper §12.2.
Depends on: `avgC`, `avgCsq`. Rule 17: λ-free. -/
def conductorSpread (T : ℝ → ℝ) (x : ℝ) : ℝ := avgCsq T x - avgC T x ^ 2

/-- **N10, the sharper half of N9.** The conductor-spread contribution ALONE is `O(1/ℒ)` —
"the same order as the rate, and absorbed by it".

This is the statement the budget actually consumes; N9's `log log Q/log Q` is the coarser
envelope that also covers the `log T/ℒ` driver.
Paper §12.2. Depends on: `sum_phiStar_asymp`, `avgLogCond_asymp`.
Rule 17: as N9a. -/
theorem conductor_spread_bigO (T : ℝ → ℝ)
    (hT1 : ∀ᶠ x in atTop, 1 ≤ T x)
    (hT : (fun x : ℝ => Real.log (T x)) =O[atTop] (fun x : ℝ => Real.log (Real.log x))) :
    (fun x : ℝ => conductorSpread T x) =O[atTop] (fun x : ℝ => 1 / LLof T x) := by
  obtain ⟨C, hC0, hfacts⟩ := N9_facts T hT1 hT
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [hfacts] with x hfx
  obtain ⟨hlx, hll, hLlow, hLup, hax, hax2⟩ := hfx
  rw [abs_lt] at hax hax2
  have hlx0 : (0 : ℝ) < Real.log x := by linarith
  have hAlow : Real.log x - 3 / 2 ≤ avgLogCond x := by linarith [hax.1]
  have hAup : avgLogCond x ≤ Real.log x + 1 / 2 := by linarith [hax.2]
  have hSlow : Real.log x ^ 2 - Real.log x - 1 / 2 ≤ avgLogCondSq x := by linarith [hax2.1]
  have hSup : avgLogCondSq x ≤ Real.log x ^ 2 - Real.log x + 3 / 2 := by linarith [hax2.2]
  have hL34 : (3 / 4) * Real.log x ≤ LLof T x := by linarith
  have hLpos : (0 : ℝ) < LLof T x := by linarith
  have hLne : LLof T x ≠ 0 := ne_of_gt hLpos
  have hspread : conductorSpread T x
      = (avgLogCondSq x - avgLogCond x ^ 2) / LLof T x ^ 2 := by
    unfold conductorSpread
    rw [avgCsq_eq, avgC_eq, div_pow]
    field_simp
  -- the `(log x)²` AND `log x` terms both cancel: the true size is `1/(4ℒ²)`
  have hnum : |avgLogCondSq x - avgLogCond x ^ 2| ≤ 2 * Real.log x + 3 / 4 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.log x + 1/2 - avgLogCond x)
        (by linarith : (0:ℝ) ≤ Real.log x + 1/2 + avgLogCond x)]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ avgLogCond x - (Real.log x - 3/2))
        (by linarith : (0:ℝ) ≤ avgLogCond x + (Real.log x - 3/2))]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hspread, abs_div,
    abs_of_pos (pow_pos hLpos 2), abs_of_pos (one_div_pos.mpr hLpos),
    div_le_iff₀ (pow_pos hLpos 2)]
  have hrhs : 4 * (1 / LLof T x) * LLof T x ^ 2 = 4 * LLof T x := by field_simp
  rw [hrhs]
  linarith [hnum, hL34]

/-- **N11, in the only honest form: a moment bound.** "The per-character scales that DO
survive (μ_q, the trace, the denominators N_χ) enter as bounded powers of `c_q` under
φ*-weights" — so every φ*-weighted moment of `c_q` is bounded.

**CAVEAT: N11 as stated in the paper is a LEDGER claim about the
whole construction, discharged component-by-component in `NOTE_QG.md §g.2`'s table, not a
single lemma.** The component bounds are owned by the tail / ends / prime-side tracks. §12
states N9/N10 (which the budget consumes) and CITES the rest; this moment bound is the part
that is genuinely §12's. **Do not double-count it against the per-component rows, and do not
let it be dropped between tracks.**
Paper §12.2. Depends on: `sum_phiStar_asymp`.
Rule 17: as N9a. -/
theorem cq_moments_bounded (T : ℝ → ℝ) (k : ℕ)
    (hT1 : ∀ᶠ x in atTop, 1 ≤ T x)
    (hT : (fun x : ℝ => Real.log (T x)) =O[atTop] (fun x : ℝ => Real.log (Real.log x))) :
    ∃ M : ℝ, ∀ᶠ x in atTop, |avgCpow T k x| ≤ M := by
  have hphi1 : ZetaQ.phiStar 1 = 1 := by
    have hsingle : ZetaQ.primitiveChars 1 = {(1 : DirichletCharacter ℂ 1)} := by
      ext χ
      simp only [ZetaQ.primitiveChars, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact ⟨fun _ => DirichletCharacter.level_one χ,
        fun h => by rw [h]; exact DirichletCharacter.isPrimitive_one_level_one⟩
    unfold ZetaQ.phiStar
    rw [hsingle]
    simp
  refine ⟨2 ^ k, ?_⟩
  filter_upwards [hT1, eventually_ge_atTop (100 : ℝ)] with x hTx hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hstep : x / (2 * Real.pi) ≤ x * T x / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hLge : Real.log (x / (2 * Real.pi)) ≤ LLof T x :=
    Real.log_le_log (by positivity) hstep
  have h2pi : 2 * Real.log (2 * Real.pi) ≤ Real.log x := by
    have hpil : Real.pi < 4 := Real.pi_lt_four
    have h1 : Real.log (2 * Real.pi) ≤ Real.log 8 :=
      Real.log_le_log (by positivity) (by linarith)
    have h3 : (2 : ℝ) * Real.log 8 = Real.log 64 := by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h4 : Real.log 64 ≤ Real.log x :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hlogsplit : Real.log (x / (2 * Real.pi)) = Real.log x - Real.log (2 * Real.pi) :=
    Real.log_div (by positivity) (by positivity)
  rw [hlogsplit] at hLge
  have hp0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  have hLpos : 0 < LLof T x := by linarith
  have hlogx_le : Real.log x ≤ 2 * LLof T x := by linarith
  have hcq : ∀ q ∈ Finset.Icc 1 ⌊x⌋₊, 0 ≤ cq T x q ∧ cq T x q ≤ 2 := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
    have hqx : (q : ℝ) ≤ x := le_trans (by exact_mod_cast hq.2) (Nat.floor_le hxpos.le)
    have hlq0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
    have hlqx : Real.log (q : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hqx
    constructor
    · exact div_nonneg hlq0 hLpos.le
    · unfold cq
      rw [div_le_iff₀ hLpos]
      linarith
  have hfamEq : famCardR x = ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) := by
    unfold famCardR ZetaQ.famCard
    push_cast
    rfl
  have hfampos : 0 < famCardR x := by
    rw [hfamEq]
    have h1mem : (1 : ℕ) ∈ Finset.Icc 1 ⌊x⌋₊ := by
      rw [Finset.mem_Icc]
      refine ⟨le_refl _, Nat.le_floor ?_⟩
      push_cast
      linarith
    have hle := Finset.single_le_sum (f := fun q : ℕ => (ZetaQ.phiStar q : ℝ))
      (fun i _ => by positivity) h1mem
    rw [hphi1] at hle
    norm_num at hle
    linarith
  have hsum_nonneg : 0 ≤ ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q ^ k :=
    Finset.sum_nonneg fun q hq => mul_nonneg (by positivity) (pow_nonneg (hcq q hq).1 k)
  have hsum_le : ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q ^ k
      ≤ 2 ^ k * famCardR x := by
    rw [hfamEq, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hpk : cq T x q ^ k ≤ 2 ^ k := pow_le_pow_left₀ (hcq q hq).1 (hcq q hq).2 k
    calc (ZetaQ.phiStar q : ℝ) * cq T x q ^ k ≤ (ZetaQ.phiStar q : ℝ) * 2 ^ k :=
          mul_le_mul_of_nonneg_left hpk (by positivity)
      _ = 2 ^ k * (ZetaQ.phiStar q : ℝ) := by ring
  unfold avgCpow
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hnn : 0 ≤ (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (ZetaQ.phiStar q : ℝ) * cq T x q ^ k) / famCardR x :=
      div_nonneg hsum_nonneg hfampos.le
    have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
    linarith
  · rw [div_le_iff₀ hfampos]
    linarith

/-! ## §12.3 — the subfamily mechanism and its two obligations

"The mechanism generalises exactly as far as its TWO obligations do: a subfamily of positive
relative density α gets the argument at out-zone constant C/α — above the λ = 1 floor
0.672500703679, since §11's gain is positive for every finite C — only if (i) its conductor
distribution matches the full family's to leading order …, AND (ii) it admits an in-zone
orthogonality projector expressing its sum through full-family instances of Lemmas 5.2/5.2′,
as the parity classes do." -/

/-- A subfamily of the primitive family: a selection of characters in each modulus.

Paper §12.3.
Depends on: `ZetaQ.primitiveChars`. Rule 17: λ-free. -/
structure Subfamily where
  /-- the selected characters mod `q`. -/
  sel : ∀ q : ℕ, Finset (DirichletCharacter ℂ q)
  /-- the selection is inside the primitive family. -/
  sub : ∀ q : ℕ, sel q ⊆ ZetaQ.primitiveChars q

/-- The full family `𝔉_Q` as a `Subfamily` (density 1).

Paper §2.2. Rule 17: λ-free. -/
def fullFamily : Subfamily where
  sel := fun q => ZetaQ.primitiveChars q
  sub := fun _ => Finset.Subset.refl _

/-- `|S_Q|` — the subfamily's character count over `q ≤ Q`.

Paper §12.3. Rule 17: λ-free. -/
def subfamCard (S : Subfamily) (Q : ℕ) : ℕ := ∑ q ∈ Finset.Icc 1 Q, (S.sel q).card

/-- `|S_x|` as a real-variable function. Rule 17: λ-free. -/
def subfamCardR (S : Subfamily) (x : ℝ) : ℝ := (subfamCard S ⌊x⌋₊ : ℝ)

/-- The subfamily's own character-count-weighted conductor average — the object obligation
(i) compares against `avgLogCond`.

Paper §12.3.
Rule 17: λ-free. -/
def subfamAvgLogCond (S : Subfamily) (x : ℝ) : ℝ :=
  (∑ q ∈ Finset.Icc 1 ⌊x⌋₊, ((S.sel q).card : ℝ) * Real.log (q : ℝ)) / subfamCardR S x

/-- **Obligation (ii) of §12.3**: the subfamily "admits an in-zone
orthogonality projector expressing its sum through FULL-FAMILY instances of Lemmas 5.2/5.2′,
as the parity classes do".

Encoded as: a bounded twist `θ` with `Σ_{χ ∈ S q} f χ = α · Σ*_{χ mod q} θ_q(χ)·f χ`, whose
twisted FAMILY pair-sum obeys the same crude divisor bound (`τ(|n−m|)` from Lemma 5.2 and
`τ(n+m)` from Lemma 5.2′) as the full family's. For the parity classes `α = 1/2` and
`θ_q(χ) = 1 + χ(−1)`: the `1`-half is the full family (Lemma 5.2) and the `χ(−1)`-half is
Lemma 5.2′ in its `n + m` form.

**This is exactly the obligation the 0.3693 trap's subfamily FAILS**:
"selecting within each modulus the half of the characters with the largest in-zone mass
satisfies (i) exactly and fails the floor, so (ii) is not removable". That selection has no
such `θ`, and positivity in-zone gives coefficient `1/α = 2` instead — `Payoff.Bgen 2 (2C)`.

The bound is stated with the crude constants `2` rather than the sharp `1` because the
projector's normalisation is free; only the SHAPE (a full-family divisor bound, not a
subfamily-specific one) is load-bearing.
Paper §12.3.
Depends on: `Subfamily`, `ZetaQ.primitiveChars`.
Rule 17: λ-free, X-free — the in-zone restriction enters only at the CALL SITE, through
`Y = Q^{1−δ′}` (Cor. 3 O11), never as a hypothesis on the identity. -/
def InZoneProjector (S : Subfamily) (α : ℝ) : Prop :=
  ∃ θ : ∀ q : ℕ, DirichletCharacter ℂ q → ℂ,
    (∀ (q : ℕ) (χ : DirichletCharacter ℂ q), ‖θ q χ‖ ≤ 2) ∧
    (∀ (q : ℕ) (f : DirichletCharacter ℂ q → ℂ),
        ∑ χ ∈ S.sel q, f χ = (α : ℂ) * ∑ χ ∈ ZetaQ.primitiveChars q, θ q χ * f χ) ∧
    (∀ Q n m : ℕ, 1 ≤ n → 1 ≤ m → n ≠ m →
        ‖∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q,
            θ q χ * (χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q)))‖
          ≤ 2 * (Q : ℝ) * ((((n : ℤ) - (m : ℤ)).natAbs.divisors.card : ℕ) : ℝ)
            + 2 * (Q : ℝ) * (((n + m).divisors.card : ℕ) : ℝ))

/-- **The two obligations of §12.3**, bundled with the density.

A subfamily of positive relative density `α` gets the argument at OUT-ZONE constant `C/α`
only if BOTH hold. **Obligation (ii) is NOT removable** — see `Trap0p3693`.
Paper §12.3.
Depends on: `subfamCardR`, `famCardR`, `subfamAvgLogCond`, `avgLogCond`, `InZoneProjector`.
Rule 17: λ-free. -/
structure SubfamilyAdmissible (S : Subfamily) (α : ℝ) : Prop where
  /-- positive relative density `α`. -/
  pos : 0 < α
  /-- the density exists and equals `α`. -/
  density : Tendsto (fun x : ℝ => subfamCardR S x / famCardR x) atTop (nhds α)
  /-- **(i)** the conductor distribution matches the full family's to leading order — else
  §12.2 must be redone, as Corollary 2 does with its own `C` and its own `⟨log q⟩`. -/
  conductor_matches :
    Tendsto (fun x : ℝ => subfamAvgLogCond S x - avgLogCond x) atTop (nhds 0)
  /-- **(ii)** an in-zone orthogonality projector through full-family instances of
  Lemmas 5.2/5.2′. -/
  in_zone_projector : InZoneProjector S α

/-- **O13 at a general density `α`.** Out-zone, the sieve input passes to the subfamily **by
positivity of its summands**: the budget (Lemma 6.1's `N + Q² − 1`) is UNCHANGED by the
selection, the denominator is the subfamily's own `≥ α·𝒩`, and therefore the out-zone
constant becomes `budget/α` (§12.3).

`Cor3.out_zone_constant_doubles` is exactly this at `α = 1/2`, the only case Corollary 3
needs; `subfamily_passage` needs §12.3's general `α`, which is why the α-general form is
stated here — and stated BEFORE `Cor3`, since `Normalisation` precedes it in this file.

Paper §1.1, §12.3.
**RULE 17, THE IMPORTANT SITE: `λ > 1` here** — this is the region "where `n` reaches
`X = Q^λ` and `n + m` outruns every modulus". No hypothesis below relates `X` to `T` or caps
`λ`; the projection route's FAILURE out-zone at `λ > 1` by `Q^{λ−1}` is the REASON positivity
is used here, never a hypothesis. -/
theorem out_zone_constant_scales {ι : Type*} (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t) (hf : ∀ i ∈ t, 0 ≤ f i)
    (budget den α denS : ℝ) (hα : 0 < α) (hden : 0 < den)
    (hsieve : ∑ i ∈ t, f i ≤ budget) (hdenS : α * den ≤ denS) :
    (∑ i ∈ s, f i) / denS ≤ budget / α / den := by
  have hn0 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun i hi => hf i (hst hi)
  have hnb : ∑ i ∈ s, f i ≤ budget :=
    (Finset.sum_le_sum_of_subset_of_nonneg hst (fun i hi _ => hf i hi)).trans hsieve
  have hb0 : 0 ≤ budget := hn0.trans hnb
  have hαden : 0 < α * den := mul_pos hα hden
  have hdenS0 : 0 < denS := lt_of_lt_of_le hαden hdenS
  have hsplit : budget / α / den = budget / (α * den) := by
    rw [div_div]
  rw [hsplit, div_le_div_iff₀ hdenS0 hαden]
  nlinarith [hn0, hnb, hb0, hdenS, hαden]

/-- **O14 at a general density `α`.** The error rows (ends, cross, tail) are one-sided or
absolute-valued, so the subfamily's row is bounded by the full family's at a cost of the
factor `1/α` against the α-ed denominator.

`Cor3.error_rows_factor_two` is this at `α = 1/2`. Same shape as `out_zone_constant_scales`,
stated separately because the per-row instantiations are owned by the ends / tail / zones
tracks and must each be checked to be one-sided or absolute-valued.
Paper §1.1. Rule 17: λ-free as stated; each row's own audit is that row's
responsibility. -/
theorem error_rows_factor_scales {ι : Type*} (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t) (hf : ∀ i ∈ t, 0 ≤ f i)
    (rrow den α denS : ℝ) (hα : 0 < α) (hden : 0 < den)
    (hrow : ∑ i ∈ t, f i ≤ rrow * den) (hdenS : α * den ≤ denS) :
    (∑ i ∈ s, f i) / denS ≤ rrow / α := by
  have h := out_zone_constant_scales s t f hst hf (rrow * den) den α denS hα hden hrow hdenS
  have hne : den ≠ 0 := ne_of_gt hden
  have hαne : α ≠ 0 := ne_of_gt hα
  have heq : rrow * den / α / den = rrow / α := by field_simp
  rwa [heq] at h

/-- **The §§3–10 interface, BUNDLED — the REPAIR of the defect below.**

**WHAT WAS WRONG.** `subfamily_passage` used to take the §§3–10 interface as a bare function
`pay : Subfamily → (ℝ → ℝ) → ℝ`, constrained by a single hypothesis `hfull` *at
`fullFamily` only*. Nothing whatever tied `pay S` to `pay fullFamily`, so the conclusion did
not follow — and the statement was outright FALSE, not merely unprovable. Failing instance
(counterexample): take

    pay := fun S' v => if S' = fullFamily then 2 − Payoff.Bgen 1 C v else −1

at `C := ZetaQ.CfamDyadic`, `α := 1/2`, and any `S` with `SubfamilyAdmissible S (1/2)`. Then
`hfull` holds with equality, while the conclusion demands `2 − Payoff.Bgen 1 (4π⁴/27) v ≤ −1`,
i.e. `Bgen 1 (4π⁴/27) v ≥ 3` for EVERY admissible `v` at every `λ ∈ (1,2)` — contradicted by
`Payoff.payoff_feasible_even_dyadic`, which exhibits one with
`B (4π⁴/27) v ≤ 2 − 0.6919 < 3`.

**One honesty note on that counterexample, because it is not machine-checkable inside this
file.** It needs an `S` that is `SubfamilyAdmissible` at `α = 1/2` and is not `fullFamily`.
The even primitive family is one — that is Corollary 3's entire premise — but its
`InZoneProjector` clause is Lemmas 5.2/5.2′, which live in `ZetaQ.CharSums` and which this
file deliberately does not reference (see the header). So the falsity is a mathematical fact
on the paper's own hypotheses, not something Lean can exhibit here; what Lean *can* see
without §5 is the weaker but equally decisive point that the old statement was unusable —
`corollary3_even_dyadic` and `corollary3_odd_dyadic` could not be derived from it, and were
themselves stuck at a free `fullFamDyad` for the same reason. Both repairs are the same
repair.

**WHAT IT SAYS NOW.** The bare function is replaced by this bundle, which carries the law
§12.3's argument actually uses. The fields are exactly the hypotheses of O13 and O14 —
`out_zone_constant_scales` / `error_rows_factor_scales` above, and their `α = 1/2` instances
`Cor3.out_zone_constant_doubles` / `Cor3.error_rows_factor_two`, all four of which are PROVED
in this file. Nothing is assumed that those lemmas do not already supply, and in particular
the conclusion of `subfamily_passage` is DERIVED, not posited as a field.

**WHY THIS IS THE PAPER'S CLAIM AND NOT A WEAKENING.** §12.3's mechanism is precisely: the
sieve budget is unchanged by the selection, the summands are nonnegative so the selected
sub-sum is no larger, and the denominator is the subfamily's own — three facts about the
sieve, not about `pay`. Encoding them as a bare `hfull` at the full family lost all three.
The conclusion of `subfamily_passage` is unchanged, verbatim.

Paper §12.3, §1.1.
Rule 17: no field relates `X` to `T`, caps `λ`, or mentions `D₀`; `1 < lam ∧ lam < 2` is
explicit in `delivers`. -/
structure PassageInterface (C : ℝ) where
  /-- the index type of §6's out-zone sieve input (the pairs the large sieve is applied to). -/
  Idx : Type
  /-- the family's out-zone sieve input. -/
  outSet : Subfamily → Finset Idx
  /-- the sieve summand. It does NOT depend on the family: Lemma 6.1's coefficient vector is a
  single `a : ℕ → ℂ` (§12.1's "single-scale by fiat"), so a subfamily sees the SAME summands
  over FEWER indices — which is what makes the selection a `Finset` inclusion. -/
  outWt : Idx → ℝ
  /-- the family's denominator: the ZERO count `𝒩_S` of O15 (not the character count). -/
  den : Subfamily → ℝ
  /-- §§3–10's delivered zero-density constant at a family and a profile. -/
  pay : Subfamily → (ℝ → ℝ) → ℝ
  /-- a subfamily SELECTS from the full family's out-zone input. -/
  outSet_subset : ∀ S : Subfamily, outSet S ⊆ outSet fullFamily
  /-- **O13's positivity** — the load-bearing hypothesis. The projection route fails out-zone
  at `λ > 1` by `Q^{λ−1}`, so the passage there is by positivity of the summands and nothing
  else. -/
  outWt_nonneg : ∀ i ∈ outSet fullFamily, 0 ≤ outWt i
  /-- denominators are positive. -/
  den_pos : ∀ S : Subfamily, 0 < den S
  /-- **O7 + O15**: a subfamily of relative density `α` has denominator at least `α·𝒩`.
  An inequality rather than an equality, because that is the direction the passage consumes
  and the direction O7/O15 supply up to their own error terms. -/
  den_density : ∀ (S : Subfamily) (α : ℝ), SubfamilyAdmissible S α →
    α * den fullFamily ≤ den S
  /-- **Lemma 6.1**: the sieve budget `N + Q² − 1`, in the units `den` is measured in — and
  UNCHANGED by the selection, which is the whole content of O13. -/
  sieve_budget : ∑ i ∈ outSet fullFamily, outWt i ≤ C * den fullFamily
  /-- **§§3–10 run on a family that meets §12.3's TWO obligations**: in-zone coefficient `1`
  (obligation (ii) — O8–O12, `Cor3.in_zone_coefficient_unchanged`) against the family's OWN
  out-zone quotient (O13/O14). A subfamily WITHOUT obligation (ii) is deliberately NOT
  covered: it is stuck at `Payoff.Bgen (1/α) (C/α)`, which is the 0.3693 trap
  (`Trap0p3693`). That is why `SubfamilyAdmissible` is a hypothesis of this field. -/
  delivers : ∀ (S : Subfamily) (α : ℝ), SubfamilyAdmissible S α →
    ∀ (lam : ℝ) (v : ℝ → ℝ), 1 < lam → lam < 2 → Payoff.Admissible lam v →
      2 - Payoff.Bgen 1 ((∑ i ∈ outSet S, outWt i) / den S) v ≤ pay S v

/-- **§12.3's mechanism.** Obligations (i)+(ii) ⇒ the argument runs at OUT-ZONE constant
`C/α` with the IN-ZONE coefficient UNCHANGED. Corollary 3 instantiates
this at `α = 1/2`, giving `C → 2C`.

Note the shape of the conclusion: `Payoff.Bgen 1 (C/α)` — in-zone weight **1**, out-zone
weight `C/α`. It is `Payoff.Bgen (1/α) (C/α)` that a subfamily WITHOUT obligation (ii) is
stuck with, and that is the 0.3693 trap.

**REPAIRED (decision D14): the bare `pay` + `hfull` interface is replaced by
`PassageInterface`, whose docstring carries the counterexample that made the old statement
false and the justification for the new one.** The conclusion is unchanged, verbatim, and the
theorem is now PROVED — from `out_zone_constant_scales` (O13 at general `α`) and the
monotonicity of `Payoff.Bgen 1 ·` in the out-zone constant, which is `Payoff.B1_nonneg`.

Paper §12.3. Depends on: `SubfamilyAdmissible`, `PassageInterface`,
`out_zone_constant_scales`, `Payoff.Bgen`, `Payoff.B1_nonneg`.
**Rule 17: `1 < lam ∧ lam < 2` explicit in both hypothesis and conclusion.** The mechanism is
about the λ > 1 regime — at `λ ≤ 1` the out-zone is empty and `C/α` is invisible, so a
smuggled `lam ≤ 1` would make this theorem true and worthless. -/
theorem subfamily_passage
    (S : Subfamily) (α : ℝ) (hα1 : α ≤ 1) (h : SubfamilyAdmissible S α)
    (C : ℝ) (hC : 0 < C)
    (I : PassageInterface C) :
    ∀ (lam : ℝ) (v : ℝ → ℝ), 1 < lam → lam < 2 → Payoff.Admissible lam v →
      2 - Payoff.Bgen 1 (C / α) v ≤ I.pay S v := by
  intro lam v hlam1 hlam2 hadm
  have hα : 0 < α := h.pos
  have hDpos : 0 < I.den fullFamily := I.den_pos fullFamily
  have hquot : (∑ i ∈ I.outSet S, I.outWt i) / I.den S ≤ C / α := by
    have hle := out_zone_constant_scales (I.outSet S) (I.outSet fullFamily) I.outWt
      (I.outSet_subset S) I.outWt_nonneg (C * I.den fullFamily) (I.den fullFamily) α
      (I.den S) hα hDpos I.sieve_budget (I.den_density S α h)
    have hne : I.den fullFamily ≠ 0 := ne_of_gt hDpos
    have hαne : α ≠ 0 := ne_of_gt hα
    have heq : C * I.den fullFamily / α / I.den fullFamily = C / α := by field_simp
    rwa [heq] at hle
  have hK1 : 0 ≤ Payoff.K1 v := by simpa [Payoff.B1] using Payoff.B1_nonneg hadm
  have hmono : Payoff.Bgen 1 ((∑ i ∈ I.outSet S, I.outWt i) / I.den S) v
      ≤ Payoff.Bgen 1 (C / α) v := by
    unfold Payoff.Bgen
    nlinarith [hK1, hquot]
  have hd := I.delivers S α h lam v hlam1 hlam2 hadm
  linarith

/-- **§12.3's floor clause.** "§11's gain is positive for EVERY finite C (no break-even)"
(L732–733): at every finite penalty there is an admissible profile at some
bandwidth `λ ∈ (1,2)` strictly beating the `λ = 1` Montgomery–Taylor floor
`0.672500703679412`.

**Scope note: this ∀C form is strictly stronger than the four
instances the paper's corollaries need.** The paper's proved cases are exactly three, and each
needs only its own `C` (`π⁴/18`, `2π⁴/27`, `4π⁴/27`, `π⁴/9` — shipped as
`Payoff.payoff_feasible_*`). This statement is kept as a SEPARATE, OPTIONAL obligation so the
scope reduction is on the record rather than silent; nothing in Theorem 1 or Corollaries 1–3
consumes it.
Paper §11 / §12.3.
Depends on: `Payoff.B`, `Payoff.Admissible`, `Payoff.Gates.MTconst`.
**Rule 17: `1 < lam ∧ lam < 2` explicit. The whole content is that the optimal `λ` is > 1 —
`Payoff.Gates.MTconst` IS the value at `λ = 1`, so a `lam ≤ 1` hypothesis would turn this
into `MTconst < MTconst`.**

**Why it is not proved** *(written when it was still a `sorry`-ed
theorem; it is the named `Prop` `GainPositiveAllC` below now — D17 exception 1: not refutable,
so not edited, and the candidate route is named instead).* `B C v = B0 v + C·B1 v`
(`Payoff.B_eq_B0_add_C_mul_B1`) with `B1 v = K1 v ≥ 0` the OUT-ZONE mass, which vanishes iff
`ψ_v` is supported in `|α| ≤ 1`, i.e. in the limit `λ → 1⁺`. So a `C`-uniform witness must
send `λ → 1` as `C → ∞`, and the target `2 − MTconst` is EXACTLY the `λ = 1` extremal value
(`Payoff.GateMTUpper` / `GateMTAttained`). The statement is therefore not a
feasibility fact at any single `λ`: it is the assertion that along a family approaching the
Montgomery–Taylor extremal the `B0`-gain is of strictly LOWER order in `(λ − 1)` than the
`B1`-loss, so that the crossover `κ(λ−1)^a > C·μ(λ−1)^b` (`b > a`) can be solved for every
finite `C`. Formalising it needs (i) an explicit `λ`-parametrised admissible family, (ii) the
two one-sided expansions of `B0` and `B1` along it, and (iii) the exact `λ = 1` value — and
(iii) is `Payoff.GateMTUpper` and `Payoff.GateMTAttained`, which are themselves unproved,
named `Prop`s in `ZetaQ/Payoff.lean`. Nothing in this file can supply them, and the four shipped certificates
give upper bounds at four FIXED `C`, not a family. This is §11 material; the four
`payoff_feasible_*` instances that Theorem 1 and Corollaries 1–3 actually consume are proved
and do not route through here.
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: needs §11's `λ = 1` gates (`Payoff.GateMTUpper`, `Payoff.GateMTAttained`), which are
themselves not claimed, and a family of certificates rather than the four fixed `C` the
feasibility route ships.  The four `payoff_feasible_*` instances Theorem 1 and Corollaries
1–3 actually consume are PROVED and do not route through here. -/
def GainPositiveAllC : Prop :=
  ∀ C : ℝ, 0 < C → ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Payoff.Admissible lam v ∧
    Payoff.B C v < 2 - Payoff.Gates.MTconst

/-- **§12.3 / §1.1: the 0.3693 TRAP — obligation (ii) is not removable.**

Positivity alone in BOTH zones doubles the in-zone coefficient too, and §11 at in-zone weight
`2|α|` and out-zone weight `2C` gives only `0.3693` — far below the `λ = 1` floor
`0.672500703679412`. Selecting within each modulus the half of the characters with the largest
in-zone mass satisfies obligation (i) EXACTLY and fails the floor; hence (ii) is not
removable, and hence Corollary 3's parity projection (which keeps the in-zone coefficient at
1) is doing real work.

The paper's shorthand "§11 at in-zone weight 2|α|" resolves as follows: the `C` that
reproduces `0.3693` is `C_dyad = 2π⁴/27` with the WHOLE kernel doubled (reproduced this
measured at `P ≈ 0.3695`, `λ ≈ 1.26`, coarse Nyström; at `π⁴/18` the trap value is `≈ 0.373`,
at `4π⁴/27` it is `≈ 0.364`). No shipped script computes it.

**FORMALIZATION WARNING — the file header's R-B1 block and the
single genuine gap between §12.3's argument and the chosen Lean route:** this statement needs
the MINIMALITY half of §11 (a LOWER bound on `min B`), and the feasibility route
supplies UPPER bounds only. It is a "this route would only give X" claim. It is NOT
load-bearing for Theorem 1 or Corollary 3 — it is the justification for why obligation (ii) is
required — but it must be surfaced, not dropped.
Paper §12.3, §1.1.
Depends on: `Payoff.minBgen`.
Rule 17: `1 < lam` lives inside `Payoff.minBgen`; the trap's own `λ ≈ 1.26 > 1`.
**NOT PROVED, AND NOT CLAIMED BY THE ARTIFACT.**  Carried as a named `Prop` rather than
a `sorry`-ed theorem: it is still elaborated and type-checked on every build, it is
visibly not a fact, and it cannot be cited as one.  Nothing in `ZetaQ` consumes it.
Reason: **the single genuine gap between §12.3's argument and the chosen Lean route.**  This
needs the MINIMALITY half of §11 — a LOWER bound on `min B` — and the feasibility
route supplies UPPER bounds only.  It is a "this route would only give X" claim, i.e. the
justification for why §12.3's obligation (ii) is not removable.  NOT load-bearing for
Theorem 1 or Corollary 3, but it must be surfaced, not dropped — which is what naming it
here does. -/
def Trap0p3693 : Prop :=
  Payoff.minBgen 2 (2 * ZetaQ.CfamDyadic) = 2 - (3693 / 10000 : ℝ)

/-! ### §12.3's closing clause and the [So21] residual-mismatch paragraph — DOCSTRINGS ONLY

**"The proved cases are exactly three: even and odd (the parity projectors), and dyadic
(conductor-restricted, with §12.2 redone)".** This is a NEGATIVE UNIVERSAL
about the paper's own coverage, not a Lean proposition. It is recorded here so the skeleton
does not silently over-claim a general subfamily theorem: `subfamily_passage` above is
conditional on `SubfamilyAdmissible`, and the only instances the paper discharges are the two
parity classes and the dyadic restriction.

**The residual-mismatch paragraph** — [So21]'s smooth weight inflating
`C` by `3/(2∫W(x)x dx)`; the window `[T, 2T]` matching [So21] and [R] exactly; [CIS2]'s window
floor — is literature comparison with **no Lean content**. Carried here as documentation.
 -/

end ZetaQ.Normalisation

/-! # Corollary 3 — the two-zone even/odd primitive argument

Source: (§1.1) plus §12.3. The twenty obligations below
are in the order the corollary uses them.

Dependency shape: O1–O7 are self-contained finite character theory; O8–O12
consume the §5 primed lemmas and §4's Lemmas 4.4–4.5; O13–O14 consume §6 and the error ledger;
O15–O16 consume §9; O17–O18 consume §11 (`ZetaQ.Payoff`). -/

namespace ZetaQ.Cor3

open ZetaQ.Normalisation

/-! ## O1–O7 — the character count `S(q)` and the even family's size -/

/-- **O1.** `S(q) := Σ_{χ prim mod q} χ(−1)`. Integer-valued: each `χ(−1) = ±1`,
`+1` exactly for the even characters.

Defined through the frozen `ZetaQ.parity` so that no `DirichletCharacter.Odd` name is assumed.
Paper §1.1.
Depends on: `ZetaQ.primitiveChars`, `ZetaQ.parity`. Rule 17: λ-free, X-free, D₀-free. -/
def Sq (q : ℕ) : ℤ :=
  ∑ χ ∈ ZetaQ.primitiveChars q, (if ZetaQ.parity χ = 0 then (1 : ℤ) else -1)

/-- **O1′.** The bridge to the paper's own writing `S(q) = Σ*_χ χ(−1)`, in ℂ.

Paper §1.1. Depends on: `Sq`, `ZetaQ.parity`. Rule 17: λ-free. -/
theorem Sq_eq_sum_chi_neg_one (q : ℕ) :
    ((Sq q : ℤ) : ℂ) = ∑ χ ∈ ZetaQ.primitiveChars q, χ (-1 : ZMod q) := by
  unfold Sq
  push_cast
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : χ.Even
  · rw [if_pos (by simp [ZetaQ.parity, h])]
    exact h.symm
  · have hO : χ.Odd := (χ.even_or_odd).resolve_left h
    rw [if_neg (by simp [ZetaQ.parity, h])]
    exact hO.symm

/-! ### The route to O3: orthogonality over ALL characters, then the conductor filtration

The closed form `S(q) = μ(q) + [2 ∣ q]·μ(q/2)` comes from `Σ_{d ∣ q} S(d) = φ(q)·[q ∣ 2]` by
Möbius inversion, and that identity is orthogonality (`DirichletCharacter.sum_characters_eq`
at `a = −1`) plus the conductor decomposition `{χ mod q} ≃ ⨆_{d ∣ q} prim(d)`.

**The full decomposition is not needed for O3**, and is not built here. Every case of O3 is a
PRIME POWER, where the filtration has a single step: the imprimitive characters mod `p^a` are
exactly those factoring through `p^{a−1}`, so `S(p^a) = 𝔖(p^a) − 𝔖(p^{a−1})` for the
all-character sum `𝔖 = SqAll`, and `𝔖` is read off from orthogonality. That step —
`sum_imprim_eq` — is `DirichletCharacter.changeLevel` as a bijection, and it is the whole of
the conductor decomposition that O3 uses. Rule 17: nothing below mentions `λ`, `X`, `T` or
`D₀`; this is finite character theory. -/

/-- The IMPRIMITIVE characters mod `q` — the complement of `ZetaQ.primitiveChars q`, spelled
with the same classical instance so that the two filters split `Finset.univ`.
Rule 17: λ-free. -/
def imprimitiveChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  letI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  Finset.univ.filter (fun χ => ¬ χ.IsPrimitive)

/-- `𝔖(q) := Σ_{χ mod q} χ(−1)` over **ALL** characters mod `q`, primitive or not — the
object orthogonality evaluates directly. `Sq` is its restriction to the primitive characters,
and `𝔖(q) = Σ_{d ∣ q} S(d)`.
Paper §1.1 (the identity behind the closed form).
Rule 17: λ-free. -/
def SqAll (q : ℕ) : ℤ :=
  ∑ χ : DirichletCharacter ℂ q, (if ZetaQ.parity χ = 0 then (1 : ℤ) else -1)

/-- The parity indicator summed over ANY set of characters is `Σ χ(−1)` after casting to ℂ.
`Sq_eq_sum_chi_neg_one` (O1′) is this at `s = ZetaQ.primitiveChars q`.
Rule 17: λ-free. -/
theorem parity_sum_cast {q : ℕ} (s : Finset (DirichletCharacter ℂ q)) :
    ((∑ χ ∈ s, (if ZetaQ.parity χ = 0 then (1 : ℤ) else -1) : ℤ) : ℂ)
      = ∑ χ ∈ s, χ (-1 : ZMod q) := by
  push_cast
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : χ.Even
  · rw [if_pos (by simp [ZetaQ.parity, h])]
    exact h.symm
  · have hO : χ.Odd := (χ.even_or_odd).resolve_left h
    rw [if_neg (by simp [ZetaQ.parity, h])]
    exact hO.symm

/-- `𝔖(q) = S(q) + (the imprimitive part)` — the primitive/imprimitive split of `Finset.univ`.
Rule 17: λ-free. -/
theorem SqAll_split (q : ℕ) :
    SqAll q = Sq q + ∑ χ ∈ imprimitiveChars q,
      (if ZetaQ.parity χ = 0 then (1 : ℤ) else -1) := by
  unfold SqAll Sq imprimitiveChars ZetaQ.primitiveChars
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : χ.IsPrimitive <;> simp [h]

/-- **Orthogonality, at `a = −1`.** `𝔖(q) = φ(q)` if `−1 ≡ 1 (mod q)` — i.e. if `q ∣ 2` — and
`0` otherwise. This is `DirichletCharacter.sum_characters_eq` and nothing else.
Paper §1.1. Depends on: Mathlib's
`DirichletCharacter.sum_characters_eq`. Rule 17: λ-free. -/
theorem SqAll_eq (q : ℕ) [NeZero q] :
    SqAll q = if (-1 : ZMod q) = 1 then (q.totient : ℤ) else 0 := by
  have hc : ((SqAll q : ℤ) : ℂ) = if (-1 : ZMod q) = 1 then (q.totient : ℂ) else 0 := by
    rw [SqAll, parity_sum_cast Finset.univ]
    exact DirichletCharacter.sum_characters_eq ℂ (-1 : ZMod q)
  by_cases h : (-1 : ZMod q) = 1
  · rw [if_pos h] at hc ⊢
    exact_mod_cast hc
  · rw [if_neg h] at hc ⊢
    exact_mod_cast hc

/-- **The one step of the conductor filtration that O3 needs.** If `d ∣ q`, `d ≠ q`, and every
proper divisor of `q` divides `d` (which is exactly the prime-power situation `d = p^{a−1}`,
`q = p^a`), then `changeLevel` is a bijection from the characters mod `d` onto the
IMPRIMITIVE characters mod `q`, and it preserves `χ(−1)` — so the imprimitive part of `𝔖(q)`
is `𝔖(d)`.
Paper §1.1.
Depends on: `DirichletCharacter.changeLevel_injective`, `conductor_changeLevel`,
`mem_conductorSet_iff_conductor_dvd`, `changeLevel_eq_cast_of_dvd'`. Rule 17: λ-free. -/
theorem sum_imprim_eq {q d : ℕ} [NeZero q] (hd : d ∣ q) (hdq : d ≠ q)
    (hmax : ∀ e : ℕ, e ∣ q → e ≠ q → e ∣ d) :
    ∑ χ ∈ imprimitiveChars q, (if ZetaQ.parity χ = 0 then (1 : ℤ) else -1) = SqAll d := by
  have : NeZero d := ⟨fun h => (NeZero.ne q) (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩
  have hval : ∀ ψ : DirichletCharacter ℂ d,
      (DirichletCharacter.changeLevel hd ψ) (-1 : ZMod q) = ψ (-1 : ZMod d) := by
    intro ψ
    have hco : IsCoprime (-1 : ℤ) (q : ℤ) := (isCoprime_one_left).neg_left
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' (R := ℂ) (χ := ψ) hd hco
    simpa using h
  have hcast : ((∑ χ ∈ imprimitiveChars q,
      (if ZetaQ.parity χ = 0 then (1 : ℤ) else -1) : ℤ) : ℂ) = ((SqAll d : ℤ) : ℂ) := by
    rw [parity_sum_cast, SqAll, parity_sum_cast Finset.univ]
    refine (Finset.sum_bij (fun ψ _ => DirichletCharacter.changeLevel hd ψ) ?_ ?_ ?_ ?_).symm
    · intro ψ _
      simp only [imprimitiveChars, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_changeLevel]
      intro hcon
      exact hdq (Nat.dvd_antisymm hd (hcon ▸ ψ.conductor_dvd_level))
    · intro ψ₁ _ ψ₂ _ h
      exact DirichletCharacter.changeLevel_injective hd h
    · intro χ hχ
      simp only [imprimitiveChars, Finset.mem_filter, Finset.mem_univ, true_and,
        DirichletCharacter.isPrimitive_def] at hχ
      have hdvd : χ.conductor ∣ d := hmax _ χ.conductor_dvd_level hχ
      have hft : DirichletCharacter.FactorsThrough χ d :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mpr hdvd
      exact ⟨hft.χ₀, Finset.mem_univ _, (hft.eq_changeLevel).symm⟩
    · intro ψ _
      exact (hval ψ).symm
  exact_mod_cast hcast

/-- `𝔖(1) = 1` — the unique character mod 1 is even. Rule 17: λ-free. -/
theorem SqAll_one : SqAll 1 = 1 := by
  rw [SqAll_eq 1, if_pos (Subsingleton.elim _ _)]
  simp

/-- `𝔖(2) = 1` — `−1 ≡ 1 (mod 2)`, and `φ(2) = 1`. Rule 17: λ-free. -/
theorem SqAll_two : SqAll 2 = 1 := by
  rw [SqAll_eq 2, if_pos (by decide)]
  simp

/-- `𝔖(q) = 0` for `q ≥ 3` — `−1 ≢ 1 (mod q)`, so orthogonality kills the sum.
Rule 17: λ-free. -/
theorem SqAll_eq_zero {q : ℕ} (hq : 3 ≤ q) : SqAll q = 0 := by
  have : NeZero q := ⟨by omega⟩
  have : Fact (2 < q) := ⟨by omega⟩
  rw [SqAll_eq q, if_neg ZMod.neg_one_ne_one]

/-- `S(q) = 𝔖(q) − 𝔖(d)` under the hypotheses of `sum_imprim_eq`. Rule 17: λ-free. -/
theorem Sq_eq_SqAll_sub {q d : ℕ} [NeZero q] (hd : d ∣ q) (hdq : d ≠ q)
    (hmax : ∀ e : ℕ, e ∣ q → e ≠ q → e ∣ d) :
    Sq q = SqAll q - SqAll d := by
  have h1 := SqAll_split q
  have h2 := sum_imprim_eq hd hdq hmax
  omega

/-- Every proper divisor of `p^a` divides `p^{a−1}` — the `hmax` hypothesis, discharged.
Rule 17: λ-free. -/
theorem dvd_prime_pow_pred {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ∀ e : ℕ, e ∣ p ^ a → e ≠ p ^ a → e ∣ p ^ (a - 1) := by
  intro e he hne
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp he
  have hja : j ≠ a := by rintro rfl; exact hne rfl
  exact pow_dvd_pow p (by omega)

/-- **The telescoping form of O3.** `S(p^a) = 𝔖(p^a) − 𝔖(p^{a−1})`: at a prime power the
conductor filtration has one step, so O3a–O3f are all instances of this identity together with
`SqAll_one` / `SqAll_two` / `SqAll_eq_zero`.
Paper §1.1.
Rule 17: λ-free. -/
theorem Sq_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    Sq (p ^ a) = SqAll (p ^ a) - SqAll (p ^ (a - 1)) := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine Sq_eq_SqAll_sub (pow_dvd_pow p (by omega)) ?_ (dvd_prime_pow_pred hp ha)
  intro h
  have := Nat.pow_right_injective hp.two_le h
  omega

/-- **The full conductor decomposition, at `a = −1`.** `Σ_{d ∣ q} S(d) = 𝔖(q)`.

This is `ZetaQ.sum_all_chars_eq_sum_divisors` (the primitive decomposition of the character
group, built in `ZetaQ/CharSums.lean` — the keystone §5 and Corollary 3 share) applied to the
functional `G d ψ = ψ(−1)`, whose `changeLevel`-invariance is
`changeLevel_eq_cast_of_dvd'` at `a = −1` (coprime to every modulus). `sum_imprim_eq` above is
the one-step, prime-power case of the same statement.
Paper §1.1.
Rule 17: `0 < q` only; λ, X, T, D₀ absent. -/
theorem sum_divisors_Sq {q : ℕ} (hq : 0 < q) :
    ∑ d ∈ q.divisors, Sq d = SqAll q := by
  have : NeZero q := ⟨by omega⟩
  have hcompat : ∀ (d : ℕ) (hd : d ∣ q) (ψ : DirichletCharacter ℂ d),
      (DirichletCharacter.changeLevel hd ψ) (-1 : ZMod q) = ψ (-1 : ZMod d) := by
    intro d hd ψ
    have hco : IsCoprime (-1 : ℤ) (q : ℤ) := (isCoprime_one_left).neg_left
    have hcl := DirichletCharacter.changeLevel_eq_cast_of_dvd' (R := ℂ) (χ := ψ) hd hco
    simpa using hcl
  have key := _root_.ZetaQ.sum_all_chars_eq_sum_divisors (q := q)
    (fun d ψ => ψ (-1 : ZMod d)) hcompat
  have hL : ((SqAll q : ℤ) : ℂ) = ∑ χ : DirichletCharacter ℂ q, χ (-1 : ZMod q) := by
    rw [SqAll, parity_sum_cast Finset.univ]
  have hR : ∀ d : ℕ, ((Sq d : ℤ) : ℂ) = ∑ ψ ∈ ZetaQ.primitiveChars d, ψ (-1 : ZMod d) := by
    intro d; rw [Sq, parity_sum_cast]
  have hcast : ((∑ d ∈ q.divisors, Sq d : ℤ) : ℂ) = ((SqAll q : ℤ) : ℂ) := by
    rw [Int.cast_sum, hL, key]
    exact Finset.sum_congr rfl (fun d _ => hR d)
  exact_mod_cast hcast

/-- **O3, in closed form.** `S(q) = μ(q) + [2 ∣ q]·μ(q/2)` — Möbius inversion of
`sum_divisors_Sq` against `𝔖(q) = φ(q)·[q ∣ 2]`, i.e. against `𝔖(1) = 𝔖(2) = 1` and
`𝔖(q) = 0` for `q ≥ 3`. Every one of O3a–O3f is an instance.

Paper §1.1.
Depends on: `sum_divisors_Sq`, `SqAll_one`, `SqAll_two`, `SqAll_eq_zero`,
Mathlib `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`. Rule 17: `0 < q` only. -/
theorem Sq_closed_form {q : ℕ} (hq : 0 < q) :
    Sq q = ArithmeticFunction.moebius q
      + (if 2 ∣ q then ArithmeticFunction.moebius (q / 2) else 0) := by
  classical
  have hsum : ∀ n > 0, ∑ d ∈ n.divisors, Sq d = SqAll n := fun n hn => sum_divisors_Sq hn
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := Sq) (g := SqAll)).mp hsum q hq
  simp only [Int.cast_id] at hinv
  rw [Nat.sum_divisorsAntidiagonal'
    (f := fun x y => ArithmeticFunction.moebius x * SqAll y)] at hinv
  rw [← hinv]
  have hzero : ∀ i ∈ q.divisors, i ∉ q.divisors.filter (fun i => i ≤ 2) →
      ArithmeticFunction.moebius (q / i) * SqAll i = 0 := by
    intro i hi hni
    have h3 : 3 ≤ i := by
      by_contra hc
      exact hni (Finset.mem_filter.mpr ⟨hi, by omega⟩)
    rw [SqAll_eq_zero h3, mul_zero]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero]
  have hset : q.divisors.filter (fun i => i ≤ 2)
      = if 2 ∣ q then ({1, 2} : Finset ℕ) else {1} := by
    ext i
    simp only [Finset.mem_filter, Nat.mem_divisors]
    by_cases h2 : 2 ∣ q
    · simp only [if_pos h2, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hi, _⟩, hle⟩
        have hipos : 0 < i := Nat.pos_of_dvd_of_pos hi hq
        omega
      · rintro (rfl | rfl)
        · exact ⟨⟨one_dvd _, by omega⟩, by norm_num⟩
        · exact ⟨⟨h2, by omega⟩, le_refl 2⟩
    · simp only [if_neg h2, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hi, _⟩, hle⟩
        have hipos : 0 < i := Nat.pos_of_dvd_of_pos hi hq
        rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
        · rfl
        · exact absurd hi h2
      · rintro rfl
        exact ⟨⟨one_dvd _, by omega⟩, by norm_num⟩
  rw [hset]
  by_cases h2 : 2 ∣ q
  · rw [if_pos h2, Finset.sum_insert (by norm_num), Finset.sum_singleton,
      Nat.div_one, SqAll_one, SqAll_two, if_pos h2]
    ring
  · rw [if_neg h2, Finset.sum_singleton, Nat.div_one, SqAll_one, if_neg h2]
    ring

/-- **O2.** `S` is multiplicative.

Paper §1.1. Depends on: `Sq`. Rule 17: λ-free.

The proof below goes through the closed form `Sq_closed_form` and multiplicativity of `μ`.
A second route exists and is not taken: extend `sum_imprim_eq`'s one-step filtration to the
full conductor decomposition `𝔖(q) = Σ_{d ∣ q} S(d)` (partition `Finset.univ` by `conductor`,
then `changeLevel` on each block), whence `S = μ ⋆ 𝔖` and multiplicativity follows from that
of `μ` and of `𝔖(q) = φ(q)·[q ∣ 2]`.

**Why it matters.** `zeroCountEven_asymp`'s error term needs `Σ_{q≤Q}|S(q)| = O(Q)`, i.e.
`|S(q)| ≤ 1`, which `sum_Sq_bigO` derives from THIS lemma plus O3. Without it the crude bound
`|S(q)| ≤ φ*(q) ≤ q` gives `Q²Tℒ` in place of `QTℒ` — the main term, not an error term. -/
theorem Sq_multiplicative {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : Nat.Coprime m n) :
    Sq (m * n) = Sq m * Sq n := by
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hmu : ArithmeticFunction.moebius (m * n)
      = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  rw [Sq_closed_form hmn, Sq_closed_form hm, Sq_closed_form hn, hmu]
  by_cases h2m : 2 ∣ m
  · -- `m` even, hence `n` odd by coprimality
    have h2n : ¬ (2 ∣ n) := by
      intro hc
      have hg : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m hc
      rw [Nat.Coprime] at h
      omega
    have h2mn : 2 ∣ m * n := h2m.mul_right n
    have hcop2 : Nat.Coprime (m / 2) n :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd h2m) h
    have hdiv : m * n / 2 = (m / 2) * n := by
      obtain ⟨k, rfl⟩ := h2m
      rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [if_pos h2mn, if_pos h2m, if_neg h2n, hdiv,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop2]
    ring
  · by_cases h2n : 2 ∣ n
    · -- `n` even, `m` odd
      have h2mn : 2 ∣ m * n := h2n.mul_left m
      have hcop2 : Nat.Coprime m (n / 2) :=
        Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd h2n) h
      have hdiv : m * n / 2 = m * (n / 2) := by
        obtain ⟨k, rfl⟩ := h2n
        rw [show m * (2 * k) = 2 * (m * k) by ring,
          Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
          Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      rw [if_pos h2mn, if_neg h2m, if_pos h2n, hdiv,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop2]
      ring
    · -- both odd
      have h2mn : ¬ (2 ∣ m * n) := by
        intro hc
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hc with hcm | hcn
        · exact h2m hcm
        · exact h2n hcn
      rw [if_neg h2mn, if_neg h2m, if_neg h2n]
      ring

/-- **O3a.** `S(1) = 1`. Rule 17: λ-free. -/
theorem Sq_one : Sq 1 = 1 := by
  have hsingle : ZetaQ.primitiveChars 1 = {(1 : DirichletCharacter ℂ 1)} := by
    ext χ
    simp only [ZetaQ.primitiveChars, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact ⟨fun _ => DirichletCharacter.level_one χ,
      fun h => by rw [h]; exact DirichletCharacter.isPrimitive_one_level_one⟩
  have hE : (1 : DirichletCharacter ℂ 1).Even := by
    show (1 : DirichletCharacter ℂ 1) (-1 : ZMod 1) = 1
    rw [Subsingleton.elim (-1 : ZMod 1) 1, map_one]
  have hp : ZetaQ.parity (1 : DirichletCharacter ℂ 1) = 0 := by
    simp only [ZetaQ.parity]
    exact if_pos hE
  rw [Sq, hsingle, Finset.sum_singleton, if_pos hp]

/-- **O3b.** `S(p) = −1` for odd primes `p`: mod `p` there are `p−1`
characters, `(p−1)/2` even (including the principal, which is imprimitive) — the count works
out to `−1`.

PROVED as `𝔖(p) − 𝔖(1) = 0 − 1`: orthogonality kills the all-character sum at `p ≥ 3`, and
the only imprimitive character mod `p` is the principal one, whose level is 1.
Depends on: `Sq_prime_pow`, `SqAll_eq_zero`, `SqAll_one`. Rule 17: λ-free. -/
theorem Sq_prime_odd {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : Sq p = -1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h := Sq_prime_pow hp (le_refl 1)
  simp only [pow_one, Nat.sub_self, pow_zero] at h
  rw [h, SqAll_eq_zero hp3, SqAll_one]
  ring

/-- **O3c.** `S(p^a) = 0` for odd primes `p` and `a ≥ 2`.

PROVED as `𝔖(p^a) − 𝔖(p^{a−1}) = 0 − 0`: both levels are `≥ 3`, so orthogonality kills both.
Depends on: `Sq_prime_pow`, `SqAll_eq_zero`. Rule 17: λ-free. -/
theorem Sq_prime_pow_odd {p a : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (ha : 2 ≤ a) :
    Sq (p ^ a) = 0 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h1 : 3 ≤ p ^ a := le_trans hp3 (Nat.le_self_pow (by omega) p)
  have h2 : 3 ≤ p ^ (a - 1) := le_trans hp3 (Nat.le_self_pow (by omega) p)
  rw [Sq_prime_pow hp (by omega), SqAll_eq_zero h1, SqAll_eq_zero h2]
  ring

/-- **O3d.** `S(2) = 0` — there is no primitive character mod 2.
Rule 17: λ-free. -/
theorem Sq_two : Sq 2 = 0 := by
  have hsub : Subsingleton (ZMod 2)ˣ := by
    have hcard : Fintype.card (ZMod 2)ˣ = 1 := by
      rw [ZMod.card_units_eq_totient 2]
      decide
    exact Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard)
  have hone : ∀ χ : DirichletCharacter ℂ 2, χ = 1 := by
    intro χ
    rw [← DirichletCharacter.toUnitHom_inj]
    ext u
    rw [Subsingleton.elim u 1]
    simp
  have hempty : ZetaQ.primitiveChars 2 = (∅ : Finset (DirichletCharacter ℂ 2)) := by
    ext χ
    simp only [ZetaQ.primitiveChars, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    intro hp
    rw [hone χ, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hp
    exact absurd hp (by norm_num)
  rw [Sq, hempty, Finset.sum_empty]

/-- **O3e.** `S(4) = −1` — the unique primitive character mod 4 is odd.

PROVED as `𝔖(4) − 𝔖(2) = 0 − 1`: orthogonality kills the level-4 sum (`−1 ≢ 1 mod 4`), while
the level-2 sum is `φ(2) = 1` (`−1 ≡ 1 mod 2`) and accounts for the two imprimitive characters
mod 4 — which are the ones factoring through 2.
Depends on: `Sq_prime_pow`, `SqAll_eq_zero`, `SqAll_two`. Rule 17: λ-free. -/
theorem Sq_four : Sq 4 = -1 := by
  have h := Sq_prime_pow Nat.prime_two (show 1 ≤ 2 by norm_num)
  norm_num at h
  rw [h, SqAll_eq_zero (show 3 ≤ 4 by norm_num), SqAll_two]
  norm_num

/-- **O3f.** `S(2^a) = 0` for `a ≥ 3`.

PROVED as `𝔖(2^a) − 𝔖(2^{a−1}) = 0 − 0`: both levels are `≥ 4 ≥ 3`.
Depends on: `Sq_prime_pow`, `SqAll_eq_zero`. Rule 17: λ-free. -/
theorem Sq_two_pow {a : ℕ} (ha : 3 ≤ a) : Sq (2 ^ a) = 0 := by
  have h1 : 3 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) ha)
  have h2 : 3 ≤ 2 ^ (a - 1) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 2 ≤ a - 1 by omega))
  rw [Sq_prime_pow Nat.prime_two (by omega), SqAll_eq_zero h1, SqAll_eq_zero h2]
  ring

/-- **O4.** `S` is supported on the squarefree-odd `q` and on `4·(squarefree-odd)`.

Paper §1.1.
Depends on: `Sq_multiplicative`, `Sq_prime_pow_odd`, `Sq_two`, `Sq_four`, `Sq_two_pow`.
Rule 17: λ-free. -/
theorem Sq_support {q : ℕ} (hq : 1 ≤ q) (h : Sq q ≠ 0) :
    (Odd q ∧ Squarefree q) ∨ (∃ r : ℕ, q = 4 * r ∧ Odd r ∧ Squarefree r) := by
  have hq0 : q ≠ 0 := by omega
  have hp2 : Nat.Prime 2 := Nat.prime_two
  -- an odd, non-squarefree modulus carries `S = 0` (a squared odd prime kills the factor)
  have hkey : ∀ n : ℕ, 0 < n → ¬ (2 ∣ n) → ¬ Squarefree n → Sq n = 0 := by
    intro n hn0 hn2 hnsf
    rw [Nat.squarefree_iff_prime_squarefree] at hnsf
    push_neg at hnsf
    obtain ⟨p, hp, hpd⟩ := hnsf
    have hpn : p ∣ n := dvd_trans (dvd_mul_left p p) hpd
    have hpodd : p ≠ 2 := by rintro rfl; exact hn2 hpn
    have hb : 2 ≤ n.factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)]
      simpa [pow_two] using hpd
    have hfac2 : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n p
    have hspos : 0 < n / p ^ n.factorization p := Nat.ordCompl_pos p (by omega)
    have hcop2 : Nat.Coprime (p ^ n.factorization p) (n / p ^ n.factorization p) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_ordCompl hp (by omega)))
    rw [← hfac2, Sq_multiplicative (Nat.one_le_pow _ _ hp.pos) hspos hcop2,
      Sq_prime_pow_odd hp hpodd hb, zero_mul]
  have hfac : 2 ^ q.factorization 2 * (q / 2 ^ q.factorization 2) = q :=
    Nat.ordProj_mul_ordCompl_eq_self q 2
  have hrpos : 0 < q / 2 ^ q.factorization 2 := Nat.ordCompl_pos 2 hq0
  have hrodd : ¬ (2 ∣ (q / 2 ^ q.factorization 2)) := Nat.not_dvd_ordCompl hp2 hq0
  have hcop : Nat.Coprime (2 ^ q.factorization 2) (q / 2 ^ q.factorization 2) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp2).mpr hrodd)
  have hmul : Sq q = Sq (2 ^ q.factorization 2) * Sq (q / 2 ^ q.factorization 2) := by
    conv_lhs => rw [← hfac]
    exact Sq_multiplicative (Nat.one_le_two_pow) hrpos hcop
  have hroddOdd : Odd (q / 2 ^ q.factorization 2) := by
    refine Nat.odd_iff.mpr ?_
    have hmod : (q / 2 ^ q.factorization 2) % 2 ≠ 0 := fun hh => hrodd (Nat.dvd_of_mod_eq_zero hh)
    omega
  by_cases ha0 : q.factorization 2 = 0
  · left
    have hqr : q / 2 ^ q.factorization 2 = q := by simp [ha0]
    refine ⟨by rwa [hqr] at hroddOdd, ?_⟩
    by_contra hsf
    exact h (hkey q (by omega) (hqr ▸ hrodd) hsf)
  by_cases ha1 : q.factorization 2 = 1
  · exact absurd (by rw [hmul, ha1, pow_one, Sq_two, zero_mul]) h
  by_cases ha2 : q.factorization 2 = 2
  · right
    refine ⟨q / 2 ^ q.factorization 2, ?_, hroddOdd, ?_⟩
    · have h4 : (4 : ℕ) = 2 ^ q.factorization 2 := by rw [ha2]; norm_num
      rw [h4]
      exact hfac.symm
    · by_contra hsf
      have hz := hkey _ hrpos hrodd hsf
      exact h (by rw [hmul, hz, mul_zero])
  · exact absurd (by rw [hmul, Sq_two_pow (by omega), zero_mul]) h

/-- **`|S(q)| ≤ 1`** — the closed form of O3 propagated by O2's multiplicativity. Stated
separately because O15 needs it pointwise, not only in the aggregated form of O5.
Rule 17: λ-free. -/
theorem abs_Sq_le_one : ∀ n : ℕ, 1 ≤ n → |Sq n| ≤ 1 := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
        intro _
        by_cases hp2 : p = 2
        · subst hp2
          rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with hk1 | hk1 | hk1
          · subst hk1; rw [pow_one, Sq_two]; norm_num
          · subst hk1; rw [show (2 : ℕ) ^ 2 = 4 by norm_num, Sq_four]; norm_num
          · rw [Sq_two_pow hk1]; norm_num
        · rcases (by omega : k = 1 ∨ 2 ≤ k) with hk1 | hk1
          · subst hk1; rw [pow_one, Sq_prime_odd hp hp2]; norm_num
          · rw [Sq_prime_pow_odd hp hp2 hk1]; norm_num
    | zero => intro hz; exact absurd hz (by norm_num)
    | one => intro _; rw [Sq_one]; norm_num
    | coprime a b ha hb hab iha ihb =>
        intro _
        rw [Sq_multiplicative (by omega) (by omega) hab, abs_mul]
        have h1 := iha (by omega)
        have h2 := ihb (by omega)
        nlinarith [abs_nonneg (Sq a), abs_nonneg (Sq b)]

/-- **O5.** `Σ_{q ≤ Q} S(q) = O(Q)`. Trivial from `|S(q)| ≤ 1`, which is what
O3+O4 deliver (the multiplicative closed form has all values in `{−1, 0, 1}`).

Paper §1.1. Depends on: `abs_Sq_le_one`.
Rule 17: λ-free.
Consumed by O7 and O15. -/
theorem sum_Sq_bigO :
    (fun x : ℝ => ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (Sq q : ℝ)) =O[atTop] (fun x : ℝ => x) := by
  have habs := abs_Sq_le_one
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h1 : |∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (Sq q : ℝ)| ≤ ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, |(Sq q : ℝ)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, |(Sq q : ℝ)| ≤ ∑ _q ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.mem_Icc] at hq
    have hb := habs q hq.1
    have hc : ((|Sq q| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hb
    rwa [Int.cast_abs] at hc
  have h3 : (∑ _q ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ)) = (⌊x⌋₊ : ℝ) := by simp
  have h4 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx, one_mul]
  linarith [h1, h2, h3 ▸ h2]

/-- The EVEN primitive characters mod `q`. Defined through the frozen `ZetaQ.parity` so that
only ℕ-equality decidability is needed.

**Interface note:** `ZetaQ.CharSums` carries its own `primitiveCharsEven`, filtered on
`χ.Even` rather than on `parity χ = 0`; the two pick out the same characters
(`CharSums.mem_primitiveCharsEven_iff`). They were never merged — §12's statements are written
against the frozen `ZetaQ.parity` and §5's against `χ.Even` — and nothing in the tree needs
them merged.
Paper §1.1, §12.3.
Depends on: `ZetaQ.primitiveChars`, `ZetaQ.parity`. Rule 17: λ-free. -/
def evenPrimitiveChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  (ZetaQ.primitiveChars q).filter (fun χ => ZetaQ.parity χ = 0)

/-- The ODD primitive characters mod `q` — "a class in which the literature contains no result
at all". See `evenPrimitiveChars` for the interface note.

Rule 17: λ-free. -/
def oddPrimitiveChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  (ZetaQ.primitiveChars q).filter (fun χ => ZetaQ.parity χ = 1)

/-! ### THE CANONICAL CHARACTER-SET BRIDGE

`ZetaQ.primitiveCharsEven` filters the primitive set on
`DirichletCharacter.Even`; `evenPrimitiveChars` just above filters it on the frozen
`ZetaQ.parity χ = 0`. The two are the SAME `Finset` but NOT `rfl` (different decidability
instances, `Classical.decPred` versus ℕ-equality), so the identification is a real lemma.

**This file is its canonical home** — the earliest one that sees both spellings — and
everything else cites it: `ZetaQ.Cor3.EvenFamInstance.primitiveCharsEven_eq` / `_Odd_eq`
(`EvenFam.lean`) are now one-line aliases, and `ZetaQ.chars_evenQle_eq` and friends
(`Zones.lean`, §12.3's reconciliation) route `Family.chars` here in one step. Do not reprove
it anywhere else. -/

/-- **the canonical bridge**: §5's `ZetaQ.primitiveCharsEven` IS §12.3's
`evenPrimitiveChars`. -/
theorem primitiveCharsEven_eq (q : ℕ) :
    ZetaQ.primitiveCharsEven q = evenPrimitiveChars q := by
  ext χ
  unfold evenPrimitiveChars
  rw [ZetaQ.mem_primitiveCharsEven_iff, Finset.mem_filter]

/-- **the canonical bridge**, odd half: §5's `ZetaQ.primitiveCharsOdd` IS §12.3's
`oddPrimitiveChars`. -/
theorem primitiveCharsOdd_eq (q : ℕ) :
    ZetaQ.primitiveCharsOdd q = oddPrimitiveChars q := by
  ext χ
  unfold oddPrimitiveChars
  rw [ZetaQ.mem_primitiveCharsOdd_iff, Finset.mem_filter]

/-- `#even-prim(q)`. Rule 17: λ-free. -/
def evenPrimCount (q : ℕ) : ℕ := (evenPrimitiveChars q).card

/-- `#odd-prim(q)`. Rule 17: λ-free. -/
def oddPrimCount (q : ℕ) : ℕ := (oddPrimitiveChars q).card

/-- **O6.** `#even-prim(q) = (φ*(q) + S(q))/2` — the parity projection at
the level of COUNTS.

Stated multiplied by 2 to stay in ℤ.
Paper §1.1.
Depends on: `Sq`, `ZetaQ.phiStar`, `evenPrimCount`. Rule 17: λ-free. -/
theorem evenPrimCount_eq (q : ℕ) :
    (2 : ℤ) * (evenPrimCount q : ℤ) = (ZetaQ.phiStar q : ℤ) + Sq q := by
  have h1 : ((evenPrimCount q : ℕ) : ℤ)
      = ∑ χ ∈ ZetaQ.primitiveChars q, (if ZetaQ.parity χ = 0 then (1 : ℤ) else 0) := by
    unfold evenPrimCount evenPrimitiveChars
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun χ _ => by split <;> simp
  have h2 : ((ZetaQ.phiStar q : ℕ) : ℤ) = ∑ _χ ∈ ZetaQ.primitiveChars q, (1 : ℤ) := by
    unfold ZetaQ.phiStar
    simp
  rw [h1, h2, Sq, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : ZetaQ.parity χ = 0 <;> simp [h]

/-- **O6′.** The odd mirror, `#odd-prim(q) = (φ*(q) − S(q))/2`.

Depends on: `evenPrimCount_eq`. Rule 17: λ-free. -/
theorem oddPrimCount_eq (q : ℕ) :
    (2 : ℤ) * (oddPrimCount q : ℤ) = (ZetaQ.phiStar q : ℤ) - Sq q := by
  have hpar : ∀ χ : DirichletCharacter ℂ q, ZetaQ.parity χ = 1 ↔ ¬ (ZetaQ.parity χ = 0) := by
    intro χ
    unfold ZetaQ.parity
    split <;> simp
  have h1 : ((oddPrimCount q : ℕ) : ℤ)
      = ∑ χ ∈ ZetaQ.primitiveChars q, (if ZetaQ.parity χ = 0 then (0 : ℤ) else 1) := by
    unfold oddPrimCount oddPrimitiveChars
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun χ _ => ?_
    by_cases h : ZetaQ.parity χ = 0
    · rw [if_neg (by rw [hpar]; simpa using h), if_pos h]
    · rw [if_pos ((hpar χ).mpr h), if_neg h]
  have h2 : ((ZetaQ.phiStar q : ℕ) : ℤ) = ∑ _χ ∈ ZetaQ.primitiveChars q, (1 : ℤ) := by
    unfold ZetaQ.phiStar
    simp
  rw [h1, h2, Sq, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : ZetaQ.parity χ = 0 <;> simp [h]

/-- `|𝔉_even|` over `q ≤ Q`. Rule 17: λ-free. -/
def famCardEven (Q : ℕ) : ℕ := ∑ q ∈ Finset.Icc 1 Q, evenPrimCount q

/-- `|𝔉_even|` as a real-variable function. Rule 17: λ-free. -/
def famCardEvenR (x : ℝ) : ℝ := (famCardEven ⌊x⌋₊ : ℝ)

/-- **O7.** `|𝔉_even| = ½|𝔉| + O(Q)` — the even family has relative density
exactly `1/2`, so `α = 1/2` in §12.3's mechanism and the out-zone constant doubles.

Paper §1.1.
Depends on: `sum_Sq_bigO`, `evenPrimCount_eq`. Rule 17: λ-free. -/
theorem famCardEven_asymp :
    (fun x : ℝ => famCardEvenR x - famCardR x / 2) =O[atTop] (fun x : ℝ => x) := by
  have key : ∀ x : ℝ, famCardEvenR x - famCardR x / 2
      = (1 / 2 : ℝ) * ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (Sq q : ℝ) := by
    intro x
    have h : (2 : ℤ) * (famCardEven ⌊x⌋₊ : ℤ)
        = (ZetaQ.famCard ⌊x⌋₊ : ℤ) + ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, Sq q := by
      unfold famCardEven ZetaQ.famCard
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      exact_mod_cast evenPrimCount_eq q
    have h' : (2 : ℝ) * famCardEvenR x
        = famCardR x + ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (Sq q : ℝ) := by
      unfold famCardEvenR famCardR
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
    linarith
  have h2 : (fun x : ℝ => famCardEvenR x - famCardR x / 2)
      = fun x : ℝ => (1 / 2 : ℝ) * ∑ q ∈ Finset.Icc 1 ⌊x⌋₊, (Sq q : ℝ) := funext key
  rw [h2]
  exact sum_Sq_bigO.const_mul_left _

/-! ## O8–O12 — IN-ZONE: the parity projector, and why the coefficient is unchanged -/

/-- **O8.** The in-zone parity projector `Σ_{χ even} f = ½ Σ*_χ (1 + χ(−1)) f`.
This is the ONLY interface through which Corollary 3 touches §5.

Paper §1.1.
Depends on: `evenPrimitiveChars`, `Sq_eq_sum_chi_neg_one`. Rule 17: λ-free, X-free. -/
theorem parity_projector_even {q : ℕ} (f : DirichletCharacter ℂ q → ℂ) :
    ∑ χ ∈ evenPrimitiveChars q, f χ
      = (1 / 2 : ℂ) * ∑ χ ∈ ZetaQ.primitiveChars q, (1 + χ (-1 : ZMod q)) * f χ := by
  rw [evenPrimitiveChars, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : χ.Even
  · rw [if_pos (by simp [ZetaQ.parity, h]), h]
    ring
  · have hO : χ.Odd := (χ.even_or_odd).resolve_left h
    rw [if_neg (by simp [ZetaQ.parity, h]), hO]
    ring

/-- **O18a.** The ODD projector `½ Σ*(1 − χ(−1))` — "The identical
argument with the projector ½Σ*(1 − χ(−1)) gives the ODD primitive family at the same
constants."

Depends on: `oddPrimitiveChars`. Rule 17: λ-free. -/
theorem parity_projector_odd {q : ℕ} (f : DirichletCharacter ℂ q → ℂ) :
    ∑ χ ∈ oddPrimitiveChars q, f χ
      = (1 / 2 : ℂ) * ∑ χ ∈ ZetaQ.primitiveChars q, (1 - χ (-1 : ZMod q)) * f χ := by
  rw [oddPrimitiveChars, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : χ.Even
  · rw [if_neg (by simp [ZetaQ.parity, h]), h]
    ring
  · have hO : χ.Odd := (χ.even_or_odd).resolve_left h
    rw [if_pos (by simp [ZetaQ.parity, h]), hO]
    ring

/-- **O9.** The split the projector produces: **the `1`-half is exactly HALF the full-family
form** (in step with the halved denominator of O7/O15), and the `χ(−1)`-half is the new term
that O10–O11 must kill.

Paper §1.1. Depends on: `parity_projector_even`.
Rule 17: λ-free. -/
theorem projector_split {q : ℕ} (f : DirichletCharacter ℂ q → ℂ) :
    ∑ χ ∈ evenPrimitiveChars q, f χ
      = (1 / 2 : ℂ) * (∑ χ ∈ ZetaQ.primitiveChars q, f χ)
        + (1 / 2 : ℂ) * ∑ χ ∈ ZetaQ.primitiveChars q, χ (-1 : ZMod q) * f χ := by
  rw [parity_projector_even f, ← mul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun χ _ => by ring)

/-- **O10.** The `χ(−1)`-half pairs `n ≡ −m (mod q)` and is governed by the aggregated identity
in its `n + m` form, **Lemma 5.2′**.

**Lemma 5.2′ is taken as the EXPLICIT HYPOTHESIS `h52'`** (its crude form
`‖Σ_{q≤Q} Σ*_χ χ(−1)χ(n)χ̄(m)‖ ≤ Q·τ(n+m)`), because `ZetaQ.CharSums` is being written
elsewhere. Discharge `h52'` from
`CharSums`' `lemma5_2'_crude`.
Paper §1.1.
Depends on: `projector_split`, and §5's Lemma 5.2′.
**Rule 17: `h52'` carries NO `n + m ≤ Q`.** The identity 5.2′ is unconditional in `Q, n, m`;
the smallness of `n + m` comes from the zone calibration at `Y = Q^{1−δ′}` (O11), never from a
hypothesis on the identity — smuggling `n + m ≤ Q` here would be indistinguishable at Lean
level from an `X ≤ Q` bandwidth cap. -/
theorem parity_neg_half_bound
    (h52' : ∀ Q n m : ℕ, 1 ≤ n → 1 ≤ m →
      ‖∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q,
          χ (-1 : ZMod q) * (χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q)))‖
        ≤ (Q : ℝ) * (((n + m).divisors.card : ℕ) : ℝ))
    (Q n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖(∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ evenPrimitiveChars q,
        χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q)))
      - (1 / 2 : ℂ) * ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q,
          χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q))‖
      ≤ (Q : ℝ) / 2 * (((n + m).divisors.card : ℕ) : ℝ) := by
  have hsplit : (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ evenPrimitiveChars q,
        χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q)))
      = (1 / 2 : ℂ) * (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q,
          χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q)))
        + (1 / 2 : ℂ) * (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q,
            χ (-1 : ZMod q) * (χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q)))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ =>
      projector_split (fun χ => χ (n : ZMod q) * (starRingEnd ℂ) (χ (m : ZMod q)))
  have hcancel : ∀ A B : ℂ, ((1 / 2 : ℂ) * A + (1 / 2 : ℂ) * B) - (1 / 2 : ℂ) * A
      = (1 / 2 : ℂ) * B := by intro A B; ring
  rw [hsplit, hcancel, norm_mul]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h2]
  have hb := h52' Q n m hn hm
  linarith

/-- **O11a.** In-zone the pair `(n, m)` satisfies `n + m ≤ 2Y = 2Q^{1−δ′} ≪ Q`
 — the arithmetic half, stated separately because it is the CONSEQUENCE that
makes Lemma 5.3′ applicable, not a hypothesis on any identity.

Paper §1.1, §12.3.
Depends on: nothing.
**Rule 17: `Y = Q^{1−δ′}` with `δ′ = ZetaQ.ParamsQ.deltaPrime`; this bounds `n, m` against a
power of `Q` BELOW 1, which is the zone edge, and has nothing to do with `X = (QT/2π)^λ`. Do
not let a reader confuse the zone break `Y` with the bandwidth cutoff `X`.** -/
theorem in_zone_sum_le (Q : ℝ) (δ' : ℝ) (n m : ℕ)
    (hn : (n : ℝ) ≤ Q ^ (1 - δ')) (hm : (m : ℝ) ≤ Q ^ (1 - δ')) :
    (n : ℝ) + (m : ℝ) ≤ 2 * Q ^ (1 - δ') := by linarith

/-- **O11b.** Hence Lemma 5.3′'s divisor average applies verbatim with `τ(n + m)` and the
`χ(−1)`-half is negligible **at the same zone-edge calibration** as the full family's `n ≠ m`
term.

`Zplus` is §5's `zoneSumPlus` (the `n + m` analogue of `S(Y)`, with NO excluded diagonal), and
`h53'` is Lemma 5.3′ — both taken as explicit parameters/hypotheses because `ZetaQ.CharSums`
is elsewhere. Instantiate `Zplus := CharSums.zoneSumPlus` and discharge `h53'`
from `lemma5_3'`.
Paper §1.1, §5. Depends on: §5's Lemma 5.3′.
**Rule 17: the calibration needs `K ≥ 2` in `δ′ = K log log Q/log Q` (§5); the design's `K = 3`
is conservative. `0 < δ' < 1` only — no `λ`, no `X`, no `T`, no `D₀`.** -/
theorem in_zone_neg_half_negligible
    (Zplus : ℕ → ℝ)
    (h53' : ∃ Cst : ℝ, 0 < Cst ∧ ∀ Y : ℕ, 3 ≤ Y → Zplus Y ≤ Cst * (Y : ℝ) * (Real.log Y) ^ 3) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ (Q : ℕ) (δ' Lscr : ℝ), 3 ≤ Q → 0 < δ' → δ' < 1 →
      Real.log (Q : ℝ) ≤ Lscr →
      (Q : ℝ) * Zplus ⌊(Q : ℝ) ^ (1 - δ')⌋₊ / ((Q : ℝ) ^ 2 * Lscr ^ 2)
        ≤ Cst * (Q : ℝ) ^ (-δ') * Lscr := by
  obtain ⟨C0, hC0pos, hC0⟩ := h53'
  refine ⟨max C0 (max (max (max (Zplus 0) (Zplus 1)) (Zplus 2)) 1),
    lt_max_of_lt_left hC0pos, ?_⟩
  intro Q δ' Lscr hQ3 hδ0 hδ1 hLQ
  set M : ℝ := max (max (Zplus 0) (Zplus 1)) (Zplus 2) with hMdef
  set Cst : ℝ := max C0 (max M 1) with hCstdef
  have hCstC0 : C0 ≤ Cst := le_max_left _ _
  have hCstM : M ≤ Cst := (le_max_left _ _).trans (le_max_right _ _)
  have hCst1 : (1 : ℝ) ≤ Cst := (le_max_right _ _).trans (le_max_right _ _)
  have hCstpos : (0 : ℝ) < Cst := lt_of_lt_of_le zero_lt_one hCst1
  have hQ3R : (3 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ3
  have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogQ3 : Real.log 3 ≤ Real.log (Q : ℝ) := Real.log_le_log (by norm_num) hQ3R
  have hLscr1 : (1 : ℝ) ≤ Lscr := by linarith
  have hLscrpos : (0 : ℝ) < Lscr := by linarith
  have hden : (0 : ℝ) < (Q : ℝ) ^ 2 * Lscr ^ 2 := by positivity
  have hA : (0 : ℝ) ≤ (Q : ℝ) ^ (1 - δ') := Real.rpow_nonneg hQpos.le _
  have hAge1 : (1 : ℝ) ≤ (Q : ℝ) ^ (1 - δ') := Real.one_le_rpow hQ1 (by linarith)
  have hLcube : (1 : ℝ) ≤ Lscr ^ 3 := by nlinarith [hLscr1]
  have hkey : (Q : ℝ) * (Q : ℝ) ^ (1 - δ') = (Q : ℝ) ^ 2 * (Q : ℝ) ^ (-δ') := by
    have h1 : ((Q : ℝ) ^ 2 : ℝ) = (Q : ℝ) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
    rw [h1]
    nth_rewrite 1 [← Real.rpow_one ((Q : ℝ))]
    rw [← Real.rpow_add hQpos, ← Real.rpow_add hQpos]
    congr 1
    push_cast
    ring
  rw [div_le_iff₀ hden]
  have hRHS : Cst * (Q : ℝ) ^ (-δ') * Lscr * ((Q : ℝ) ^ 2 * Lscr ^ 2)
      = Cst * ((Q : ℝ) * (Q : ℝ) ^ (1 - δ')) * Lscr ^ 3 := by
    rw [hkey]; ring
  rw [hRHS]
  by_cases hY : 3 ≤ ⌊(Q : ℝ) ^ (1 - δ')⌋₊
  · have hZ := hC0 _ hY
    have hYle : ((⌊(Q : ℝ) ^ (1 - δ')⌋₊ : ℕ) : ℝ) ≤ (Q : ℝ) ^ (1 - δ') := Nat.floor_le hA
    have hY1 : (1 : ℝ) ≤ ((⌊(Q : ℝ) ^ (1 - δ')⌋₊ : ℕ) : ℝ) := by
      have h : (1 : ℕ) ≤ ⌊(Q : ℝ) ^ (1 - δ')⌋₊ := by omega
      exact_mod_cast h
    have hlogY0 : 0 ≤ Real.log ((⌊(Q : ℝ) ^ (1 - δ')⌋₊ : ℕ) : ℝ) := Real.log_nonneg hY1
    have hlogYle : Real.log ((⌊(Q : ℝ) ^ (1 - δ')⌋₊ : ℕ) : ℝ) ≤ Lscr := by
      have h1 : Real.log ((⌊(Q : ℝ) ^ (1 - δ')⌋₊ : ℕ) : ℝ) ≤ Real.log ((Q : ℝ) ^ (1 - δ')) :=
        Real.log_le_log (by linarith) hYle
      rw [Real.log_rpow hQpos] at h1
      have hlQ0 : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1
      nlinarith
    have hcube : Real.log ((⌊(Q : ℝ) ^ (1 - δ')⌋₊ : ℕ) : ℝ) ^ 3 ≤ Lscr ^ 3 :=
      pow_le_pow_left₀ hlogY0 hlogYle 3
    have step1 : Zplus ⌊(Q : ℝ) ^ (1 - δ')⌋₊ ≤ C0 * (Q : ℝ) ^ (1 - δ') * Lscr ^ 3 := by
      refine hZ.trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_left hYle hC0pos.le) hcube
        (by positivity) (by positivity)
    calc (Q : ℝ) * Zplus ⌊(Q : ℝ) ^ (1 - δ')⌋₊
        ≤ (Q : ℝ) * (C0 * (Q : ℝ) ^ (1 - δ') * Lscr ^ 3) :=
          mul_le_mul_of_nonneg_left step1 hQpos.le
      _ = C0 * ((Q : ℝ) * (Q : ℝ) ^ (1 - δ')) * Lscr ^ 3 := by ring
      _ ≤ Cst * ((Q : ℝ) * (Q : ℝ) ^ (1 - δ')) * Lscr ^ 3 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hCstC0 (by positivity)
  · have hZM : Zplus ⌊(Q : ℝ) ^ (1 - δ')⌋₊ ≤ M := by
      have h3 : ⌊(Q : ℝ) ^ (1 - δ')⌋₊ = 0 ∨ ⌊(Q : ℝ) ^ (1 - δ')⌋₊ = 1
          ∨ ⌊(Q : ℝ) ^ (1 - δ')⌋₊ = 2 := by omega
      rcases h3 with h | h | h <;> rw [h, hMdef]
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact le_max_right _ _
    have hAL : (1 : ℝ) ≤ (Q : ℝ) ^ (1 - δ') * Lscr ^ 3 :=
      hAge1.trans (le_mul_of_one_le_right (by linarith) hLcube)
    calc (Q : ℝ) * Zplus ⌊(Q : ℝ) ^ (1 - δ')⌋₊
        ≤ (Q : ℝ) * Cst := mul_le_mul_of_nonneg_left (hZM.trans hCstM) hQpos.le
      _ = Cst * (Q : ℝ) * 1 := by ring
      _ ≤ Cst * (Q : ℝ) * ((Q : ℝ) ^ (1 - δ') * Lscr ^ 3) :=
          mul_le_mul_of_nonneg_left hAL (by positivity)
      _ = Cst * ((Q : ℝ) * (Q : ℝ) ^ (1 - δ')) * Lscr ^ 3 := by ring

/-- **O12. THE CONCLUSION OF O8–O11: the in-zone coefficient of the variational problem is
UNCHANGED**.

The subfamily's in-zone form is `½·(full-family form) + (negligible)` (O9–O11) and the
denominator is ALSO halved (O7 for the character count, O15 for the zero count) — so the ratio
the certificate consumes carries in-zone weight `1`, not `1/α = 2`. In `ZetaQ.Payoff` terms:
the even family's functional is `Payoff.Bgen 1 (2C)`, **not** `Payoff.Bgen 2 (2C)` — the
latter is the 0.3693 trap (O20, `Normalisation.Trap0p3693`).

Stated as the exact bookkeeping identity, which is what the corollary actually uses. Consumes
Lemmas 4.4–4.5 verbatim for the zone-boundary and in-zone cross terms.
Paper §1.1.
Depends on: `projector_split`, `parity_neg_half_bound`, `in_zone_neg_half_negligible`.
Rule 17: λ-free, X-free — this is pure bookkeeping between a numerator and a denominator. -/
theorem in_zone_coefficient_unchanged
    (inzoneFull inzoneEven denFull denEven err : ℝ)
    (hdenpos : 0 < denFull)
    (hden : denEven = denFull / 2)
    (hnum : inzoneEven = inzoneFull / 2 + err) :
    inzoneEven / denEven = inzoneFull / denFull + 2 * err / denFull := by
  have hne : denFull ≠ 0 := ne_of_gt hdenpos
  subst hden
  subst hnum
  field_simp

/-! ## O13–O14 — OUT-ZONE: positivity, and the doubling of `C` -/

/-- **O13. The load-bearing inequality.** Out-zone the sieve input passes to the subfamily
**by positivity of its summands**: the budget `N + Q² − 1` (Lemma 6.1) is UNCHANGED, the
denominator HALVES (O7/O15), and therefore the out-zone constant DOUBLES, `C → 2C`
(§12.3).

Stated in the generic Finset form the argument actually is, so that it is checkable
independently of the sieve interface: `s ⊆ t`, `f ≥ 0` on `t`, `Σ_t f ≤ budget` ⇒
`(Σ_s f)/(den/2) ≤ 2·(budget/den)`.

**This is the `α = 1/2` case of `Normalisation.out_zone_constant_scales`**, which §12.3's
general-`α` mechanism needs and which `Normalisation.PassageInterface` is built out of. Both
are proved; this one is kept because `α = 1/2` is the only case Corollary 3 uses, and because
it is the form a reviewer can check against without unpacking a structure.

**Why positivity rather than projection here** (§12.3 L727–729): the
projection route FAILS out-zone at `λ > 1` by `Q^{λ−1}` — the identical mechanism as §4's
cross term, with no band separation available since both halves share a band — and no
parity-restricted sieve at budget `½(N + Q² − 1)` appears in the literature (see O19).
Paper §1.1. Depends on: §6's Lemma 6.1.
**RULE 17, THE IMPORTANT SITE: `λ > 1` here.** This is exactly the region "where `n` reaches
`X = Q^λ` and `n + m` outruns every modulus". Any hypothesis of the form `X ≤ T` or `λ ≤ 1` at
this site would be FALSE at every design point of the paper (§2.1: `X = (QT/2π)^λ ≫ T`). None
appears above; check that §6's interface does not import one from a T-aspect
mirror. -/
theorem out_zone_constant_doubles {ι : Type*} (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t) (hf : ∀ i ∈ t, 0 ≤ f i)
    (budget den : ℝ) (hden : 0 < den) (hsieve : ∑ i ∈ t, f i ≤ budget) :
    (∑ i ∈ s, f i) / (den / 2) ≤ 2 * (budget / den) := by
  have hne : den ≠ 0 := ne_of_gt hden
  have hs : ∑ i ∈ s, f i ≤ ∑ i ∈ t, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg hst (fun i hi _ => hf i hi)
  have hsb : ∑ i ∈ s, f i ≤ budget := hs.trans hsieve
  have hnn : 0 ≤ (2 * (budget - ∑ i ∈ s, f i)) / den :=
    div_nonneg (by linarith) hden.le
  have heq : (2 * (budget - ∑ i ∈ s, f i)) / den
      = 2 * (budget / den) - (∑ i ∈ s, f i) / (den / 2) := by
    field_simp
  rw [heq] at hnn
  linarith

/-- **O14.** The error rows (ends, cross, tail) are one-sided or absolute-valued, so the
subfamily is bounded by the full family at a cost of a factor `≤ 2` against the halved
denominator.

Same shape as O13; stated separately because the per-row instantiations are owned by the
ends / tail / zones tracks and must each be checked to be one-sided or absolute-valued.
**The `α = 1/2` case of `Normalisation.error_rows_factor_scales`.**
Paper §1.1.
Depends on: the error ledger of §§7–10.
Rule 17: λ-free as stated; each row's own audit is that row's responsibility. -/
theorem error_rows_factor_two {ι : Type*} (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t) (hf : ∀ i ∈ t, 0 ≤ f i)
    (r den : ℝ) (hden : 0 < den) (hrow : ∑ i ∈ t, f i ≤ r * den) :
    (∑ i ∈ s, f i) / (den / 2) ≤ 2 * r := by
  have hne : den ≠ 0 := ne_of_gt hden
  have hs : ∑ i ∈ s, f i ≤ ∑ i ∈ t, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg hst (fun i hi _ => hf i hi)
  have hsb : ∑ i ∈ s, f i ≤ r * den := hs.trans hrow
  have hnn : 0 ≤ (2 * (r * den - ∑ i ∈ s, f i)) / den :=
    div_nonneg (by linarith) hden.le
  have heq : (2 * (r * den - ∑ i ∈ s, f i)) / den
      = 2 * r - (∑ i ∈ s, f i) / (den / 2) := by
    field_simp
  rw [heq] at hnn
  linarith

/-! ## O15–O16 — the denominator is a ZERO count, and parity uniformity -/

/-- `𝒩 := Σ_χ N_χ(T, 2T)` over the primitive family `q ≤ Q`, at an abstract per-character zero
count `Nchi`.

`Nchi` is a parameter because `ZetaQ` has no zero-counting layer of its own — the per-χ
machinery lives in `Zeta23/ThmE/ReZeroCountChi.lean` and is consumed through §9.
Paper §2.2.
Rule 17: λ-free — `𝒩 ≍ Q²Tℒ` involves no bandwidth. -/
def zeroCount (Nchi : (q : ℕ) → DirichletCharacter ℂ q → ℝ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ ZetaQ.primitiveChars q, Nchi q χ

/-- `𝒩_even` — the same sum over the EVEN primitive family.

Rule 17: λ-free. -/
def zeroCountEven (Nchi : (q : ℕ) → DirichletCharacter ℂ q → ℝ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ evenPrimitiveChars q, Nchi q χ

/-- **O15.** `𝒩_even = ½𝒩 + O(QTℒ + Q²·log QT)` — **the denominator is a ZERO count, not the
character count**.

=============================================================================================
**🚩 THIS IS A PAPER FINDING, AND THE STATEMENT IS REPAIRED ACCORDINGLY (D14).**
=============================================================================================
Paper §1.1, Corollary 3 claims `𝒩_even = ½𝒩 + O(QTℒ)`, "by partial summation of
`N_χ(T,2T) = (T/2π)(log(qT/2π) + 2log2 − 1) + O(log qT)` against `Σ_{q≤x}S(q) = O(x)` —
relative error `O(1/Q)`."

**The main-term half is right.** `Σ_{χ even}` of the RvM main term splits as
`½·Σ_χ(main) + (T/2π)·½·Σ_q S(q)·ℓ₁(q,T)`, and the second piece is `O(QTℒ)` — already from
`|S(q)| ≤ 1` and `|ℓ₁(q,T)| = O(ℒ)`, before any partial summation.

**But the `O(log qT)` per-character RvM errors are unaccounted.** There are `≍ (18/π⁴)Q²`
characters in the family, so they contribute `O(Q²·log QT)`, and nothing makes them cancel
across the family: the parity split is not sign-random in `q`. The stated term is too small
by a factor `≍ Q/T` — **10¹⁹ at `Q = 10²⁵`, 10⁹¹ at `Q = 10¹⁰⁰`** (at `T = (log Q)^{3+ε}`).

**Counterexample to the paper's form, from this statement's own hypothesis** (which is the
right test, since `hRvM` is all §9 supplies): take `T := 1` and
`N_χ(T,2T) := (T/2π)·ℓ₁(q,T) + (−1)^{parity χ}·log(qT+2)`. This satisfies `hRvM` with
`Cst = 1`, yet `𝒩_even − ½𝒩 = ½Σ_{q≤Q}Σ*_χ (−1)^{parity χ}·…` picks up
`≥ ½·log 3·Σ_{q≤Q} φ*(q) ≍ Q²`, which exceeds `Cst·Q·T·log Q` for every fixed `Cst`.

**THE COROLLARY SURVIVES, COMFORTABLY.** Relative to `𝒩 ≍ Q²Tℒ` the true error is
`log(QT)/(Tℒ) ≍ 1/T`, i.e. `6.9×10⁻⁷` at `Q = 10²⁵` and `5.4×10⁻⁹` at `10¹⁰⁰` — still `o(1)`,
and four to six orders of magnitude BELOW the budget's own rate term `Θ(log log Q/log Q)`
(0.070 and 0.024 at those scales). **Nothing downstream moves.**

**SUGGESTED PAPER EDIT (one clause).** The displayed error should read `O(QTℒ + Q²·log QT)`
and the parenthetical should say **relative error `O(1/T)`**, not `O(1/Q)`. Since
`T = (log Q)^{3+ε}` that is still `o(1)` and still far inside the budget — but as written the
bound is not true, and a referee computing it will notice.
=============================================================================================

The Riemann–von-Mangoldt-χ input is the explicit hypothesis `hRvM` (owned by §9 / the EFChi
§9, via `Zeta23/ThmE/ReZeroCountChi.lean`). Note `ℓ_{1,χ} = log(qT/2π) + 2log2 − 1` is
`Zeta23.ThmE.ell1q q T`. The second error summand is written with `log(QT + 2)`, matching
`hRvM`'s own shape, so that it is dischargeable from `hRvM` verbatim.
Paper §1.1.
Depends on: `sum_Sq_bigO`, `evenPrimCount_eq`, §9's RvM-χ.

**How the proof goes** *(written as "why this is still a `sorry` after the repair", when O2 was
open; O2 landed and so did this theorem, and the paragraph is an accurate description of the
proof below).* Per `q`, split
`N_χ = (T/2π)ℓ₁(q,T) + e_χ`; `evenPrimCount_eq` turns the main halves into `(S(q)/2)·M(q)`,
and the `e_χ` halves are `≤ (3/2)·φ*(q)·Cst·log(QT+2)`, summing to the second term via
`Σ_{q≤Q} φ*(q) ≤ Q²`. The FIRST term needs `Σ_{q≤Q}|S(q)| = O(Q)`, i.e. `|S(q)| ≤ 1` — which
`sum_Sq_bigO` gets from `Sq_multiplicative` (PROVED, O2) plus O3. The crude
`|S(q)| ≤ φ*(q) ≤ q` would give `Q²Tℒ`, which is the main term rather than an error. **O2 was
what blocked O15**, and no partial summation is needed now that it has landed — the triangle
suffices, since `|ℓ₁(q,T)| ≤ log Q + K_T` uniformly for `q ≤ Q`.
**Rule 17: `D₀`-free — this is a zero count on `[T, 2T]`, with no buffer and no
`D₀ = √T` anywhere. λ-free and X-free too.** -/
theorem zeroCountEven_asymp (T : ℝ) (hT : 0 < T)
    (Nchi : (q : ℕ) → DirichletCharacter ℂ q → ℝ)
    (hRvM : ∃ Cst : ℝ, 0 < Cst ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q →
      |Nchi q χ - (T / (2 * Real.pi)) * Zeta23.ThmE.ell1q q T| ≤ Cst * Real.log ((q : ℝ) * T + 2)) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ Q : ℕ, 3 ≤ Q →
      |zeroCountEven Nchi Q - zeroCount Nchi Q / 2|
        ≤ Cst * ((Q : ℝ) * T * Real.log (Q : ℝ)
            + (Q : ℝ) ^ 2 * Real.log ((Q : ℝ) * T + 2)) := by
  obtain ⟨A, hA, hAb⟩ := hRvM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set K : ℝ := |Real.log (T / (2 * Real.pi))| + |2 * Real.log 2 - 1| with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨(1 + K) / (4 * Real.pi) + (3 / 2) * A, by positivity, ?_⟩
  intro Q hQ3
  have hQ1 : 1 ≤ Q := by omega
  have hQR : (3 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ3
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  have hlogQ : (1 : ℝ) ≤ Real.log (Q : ℝ) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    exact le_trans h3 (Real.log_le_log (by norm_num) hQR)
  have hLQT : (0 : ℝ) ≤ Real.log ((Q : ℝ) * T + 2) :=
    Real.log_nonneg (by nlinarith)
  -- the per-modulus bound
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      |(∑ χ ∈ evenPrimitiveChars q, Nchi q χ)
          - (∑ χ ∈ ZetaQ.primitiveChars q, Nchi q χ) / 2|
        ≤ (T / (4 * Real.pi)) * ((1 + K) * Real.log (Q : ℝ))
          + (3 / 2) * A * ((Q : ℝ) * Real.log ((Q : ℝ) * T + 2)) := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    have hqne : NeZero q := ⟨by omega⟩
    have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
    set M : ℝ := (T / (2 * Real.pi)) * Zeta23.ThmE.ell1q q T with hMdef
    -- |ℓ₁(q,T)| ≤ log Q + K
    have hell : |Zeta23.ThmE.ell1q q T| ≤ Real.log (Q : ℝ) + K := by
      have hsplit : Zeta23.ThmE.ell1q q T
          = Real.log (q : ℝ) + Real.log (T / (2 * Real.pi)) + (2 * Real.log 2 - 1) := by
        rw [Zeta23.ThmE.ell1q,
          show (q : ℝ) * T / (2 * Real.pi) = (q : ℝ) * (T / (2 * Real.pi)) by ring,
          Real.log_mul (by linarith) (by positivity)]
        ring
      have hlq0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
      have hlqQ : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) :=
        Real.log_le_log (by linarith) hqQR
      rw [hsplit]
      have h1 := le_abs_self (Real.log (T / (2 * Real.pi)))
      have h2 := neg_abs_le (Real.log (T / (2 * Real.pi)))
      have h3 := le_abs_self (2 * Real.log 2 - 1)
      have h4 := neg_abs_le (2 * Real.log 2 - 1)
      rw [abs_le, hKdef]
      constructor <;> linarith
    -- the error split
    have hsE : ∑ χ ∈ evenPrimitiveChars q, (Nchi q χ - M)
        = (∑ χ ∈ evenPrimitiveChars q, Nchi q χ) - (evenPrimCount q : ℝ) * M := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, evenPrimCount, nsmul_eq_mul]
    have hsP : ∑ χ ∈ ZetaQ.primitiveChars q, (Nchi q χ - M)
        = (∑ χ ∈ ZetaQ.primitiveChars q, Nchi q χ) - (ZetaQ.phiStar q : ℝ) * M := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, ZetaQ.phiStar, nsmul_eq_mul]
    -- counts
    have hcount : (2 : ℝ) * (evenPrimCount q : ℝ) = (ZetaQ.phiStar q : ℝ) + (Sq q : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (evenPrimCount_eq q)
    have hSq : |(Sq q : ℝ)| ≤ 1 := by
      have h := abs_Sq_le_one q hq1
      have hc : ((|Sq q| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h
      rwa [Int.cast_abs] at hc
    have hphiQ : (ZetaQ.phiStar q : ℝ) ≤ (Q : ℝ) := by
      have h1 : ZetaQ.phiStar q ≤ q := by
        have hle : (ZetaQ.primitiveChars q).card
            ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
        have := Nat.totient_le q
        simp only [ZetaQ.phiStar, Finset.card_univ, hcard] at hle ⊢
        omega
      exact le_trans (by exact_mod_cast h1) hqQR
    have hevenQ : (evenPrimCount q : ℝ) ≤ (Q : ℝ) := by
      have h1 : evenPrimCount q ≤ ZetaQ.phiStar q :=
        Finset.card_le_card (Finset.filter_subset _ _)
      exact le_trans (by exact_mod_cast h1) hphiQ
    -- the per-character errors
    have hlogq : Real.log ((q : ℝ) * T + 2) ≤ Real.log ((Q : ℝ) * T + 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hAlog : (0 : ℝ) ≤ A * Real.log ((Q : ℝ) * T + 2) := mul_nonneg hA.le hLQT
    have herr : ∀ (S : Finset (DirichletCharacter ℂ q)),
        S ⊆ ZetaQ.primitiveChars q →
        |∑ χ ∈ S, (Nchi q χ - M)| ≤ (Q : ℝ) * (A * Real.log ((Q : ℝ) * T + 2)) := by
      intro S hS
      have h1 : |∑ χ ∈ S, (Nchi q χ - M)| ≤ ∑ χ ∈ S, |Nchi q χ - M| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ χ ∈ S, |Nchi q χ - M|
          ≤ ∑ _χ ∈ S, A * Real.log ((Q : ℝ) * T + 2) := by
        refine Finset.sum_le_sum (fun χ _ => ?_)
        exact (hAb q χ hq1).trans (mul_le_mul_of_nonneg_left hlogq hA.le)
      have h3 : ∑ _χ ∈ S, A * Real.log ((Q : ℝ) * T + 2)
          = (S.card : ℝ) * (A * Real.log ((Q : ℝ) * T + 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h4 : (S.card : ℝ) ≤ (Q : ℝ) := by
        have hc : S.card ≤ ZetaQ.phiStar q := by
          simp only [ZetaQ.phiStar]
          exact Finset.card_le_card hS
        exact le_trans (by exact_mod_cast hc) hphiQ
      have h5 : (S.card : ℝ) * (A * Real.log ((Q : ℝ) * T + 2))
          ≤ (Q : ℝ) * (A * Real.log ((Q : ℝ) * T + 2)) :=
        mul_le_mul_of_nonneg_right h4 hAlog
      rw [h3] at h2
      linarith
    have hEe := herr (evenPrimitiveChars q) (Finset.filter_subset _ _)
    have hEp := herr (ZetaQ.primitiveChars q) (le_refl _)
    -- assemble
    have hMabs : |M| ≤ (T / (2 * Real.pi)) * (Real.log (Q : ℝ) + K) := by
      rw [hMdef, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ T / (2 * Real.pi))]
      exact mul_le_mul_of_nonneg_left hell (by positivity)
    have hD : (∑ χ ∈ evenPrimitiveChars q, Nchi q χ)
          - (∑ χ ∈ ZetaQ.primitiveChars q, Nchi q χ) / 2
        = ((Sq q : ℝ) / 2) * M + (∑ χ ∈ evenPrimitiveChars q, (Nchi q χ - M))
          - (∑ χ ∈ ZetaQ.primitiveChars q, (Nchi q χ - M)) / 2 := by
      have hec : (evenPrimCount q : ℝ) = ((ZetaQ.phiStar q : ℝ) + (Sq q : ℝ)) / 2 := by
        linarith [hcount]
      rw [hsE, hsP, hec]
      ring
    have hlogKQ : Real.log (Q : ℝ) + K ≤ (1 + K) * Real.log (Q : ℝ) := by nlinarith
    have hX : |((Sq q : ℝ) / 2) * M| ≤ (T / (4 * Real.pi)) * ((1 + K) * Real.log (Q : ℝ)) := by
      rw [abs_mul, abs_div, abs_two]
      have hstep : |(Sq q : ℝ)| / 2 * |M| ≤ (1 / 2) * |M| := by
        nlinarith [abs_nonneg M, abs_nonneg ((Sq q : ℝ))]
      have hchain : (1 / 2) * ((T / (2 * Real.pi)) * (Real.log (Q : ℝ) + K))
          ≤ (T / (4 * Real.pi)) * ((1 + K) * Real.log (Q : ℝ)) := by
        have h1 : (1 / 2) * ((T / (2 * Real.pi)) * (Real.log (Q : ℝ) + K))
            = (T / (4 * Real.pi)) * (Real.log (Q : ℝ) + K) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_left hlogKQ (by positivity)
      nlinarith [hMabs, abs_nonneg M]
    rw [hD]
    set X : ℝ := ((Sq q : ℝ) / 2) * M with hXdef
    set Ye : ℝ := ∑ χ ∈ evenPrimitiveChars q, (Nchi q χ - M) with hYedef
    set Zp : ℝ := ∑ χ ∈ ZetaQ.primitiveChars q, (Nchi q χ - M) with hZpdef
    have hb1 := le_abs_self X
    have hb2 := neg_abs_le X
    have hb3 := le_abs_self Ye
    have hb4 := neg_abs_le Ye
    have hb5 := le_abs_self Zp
    have hb6 := neg_abs_le Zp
    rw [abs_le]
    constructor <;> linarith [hX, hEe, hEp]
  -- sum over `q ≤ Q`
  have hrewrite : zeroCountEven Nchi Q - zeroCount Nchi Q / 2
      = ∑ q ∈ Finset.Icc 1 Q, ((∑ χ ∈ evenPrimitiveChars q, Nchi q χ)
          - (∑ χ ∈ ZetaQ.primitiveChars q, Nchi q χ) / 2) := by
    rw [zeroCountEven, zeroCount, Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [hrewrite]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hcardQ : ((Q + 1 - 1 : ℕ) : ℝ) = (Q : ℝ) := by simp
  rw [hcardQ]
  have hu : (0 : ℝ) ≤ (Q : ℝ) * T * Real.log (Q : ℝ) :=
    mul_nonneg (mul_nonneg hQ0.le hT.le) (by linarith)
  have hv : (0 : ℝ) ≤ (Q : ℝ) ^ 2 * Real.log ((Q : ℝ) * T + 2) :=
    mul_nonneg (by positivity) hLQT
  have e1 : (Q : ℝ) * (T / (4 * Real.pi) * ((1 + K) * Real.log (Q : ℝ))
        + 3 / 2 * A * ((Q : ℝ) * Real.log ((Q : ℝ) * T + 2)))
      = ((1 + K) / (4 * Real.pi)) * ((Q : ℝ) * T * Real.log (Q : ℝ))
        + (3 / 2 * A) * ((Q : ℝ) ^ 2 * Real.log ((Q : ℝ) * T + 2)) := by ring
  have e2 : ((1 + K) / (4 * Real.pi) + 3 / 2 * A) * ((Q : ℝ) * T * Real.log (Q : ℝ)
        + (Q : ℝ) ^ 2 * Real.log ((Q : ℝ) * T + 2))
      = ((1 + K) / (4 * Real.pi)) * ((Q : ℝ) * T * Real.log (Q : ℝ))
        + (3 / 2 * A) * ((Q : ℝ) ^ 2 * Real.log ((Q : ℝ) * T + 2))
        + ((1 + K) / (4 * Real.pi)) * ((Q : ℝ) ^ 2 * Real.log ((Q : ℝ) * T + 2))
        + (3 / 2 * A) * ((Q : ℝ) * T * Real.log (Q : ℝ)) := by ring
  have t1 : (0 : ℝ) ≤ ((1 + K) / (4 * Real.pi)) * ((Q : ℝ) ^ 2 * Real.log ((Q : ℝ) * T + 2)) :=
    mul_nonneg (by positivity) hv
  have t2 : (0 : ℝ) ≤ (3 / 2 * A) * ((Q : ℝ) * T * Real.log (Q : ℝ)) :=
    mul_nonneg (by positivity) hu
  rw [e1, e2]
  linarith

/-! ### Fill-local digamma toolkit for O16/O16′

Mathlib's `Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean` carries only `digamma_zero`,
`digamma_one`, `digamma_one_half`, `digamma_apply_add_one` and `meromorphic_digamma`; there is
**no reflection formula and no conjugation symmetry**. Both are proved here from what Mathlib
does have — `Complex.Gamma_mul_Gamma_one_sub` (Beta.lean) and `Complex.Gamma_conj` (Basic.lean)
— by logarithmic differentiation, i.e. exactly the textbook derivation. Nothing below is
`sorry`-backed and nothing is axiomatised. -/

/-- **Fill-local helper (Schwarz reflection for `Γ`).** `ψ(conj s) = conj (ψ s)`, hence
`Re ψ(conj s) = Re ψ(s)`.

`conj ∘ Γ ∘ conj = Γ` pointwise by `Complex.Gamma_conj`, so `HasDerivAt.conj_conj` transports
the derivative of `Γ` at `s` to a derivative of `Γ` at `conj s`; `digamma = deriv Γ / Γ` is then
conjugated by `map_div₀`. -/
private theorem digamma_conj_re (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) :
    Complex.digamma (starRingEnd ℂ s) = starRingEnd ℂ (Complex.digamma s) := by
  have hcomp : (⇑(starRingEnd ℂ)) ∘ Complex.Gamma ∘ (⇑(starRingEnd ℂ)) = Complex.Gamma := by
    funext z; simp [Function.comp_def, Complex.Gamma_conj]
  have hd : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
    (Complex.differentiableAt_Gamma s hs).hasDerivAt
  have hd2 : HasDerivAt Complex.Gamma (starRingEnd ℂ (deriv Complex.Gamma s))
      (starRingEnd ℂ s) := by
    have h := hd.conj_conj; rwa [hcomp] at h
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, hd2.deriv, Complex.Gamma_conj,
    map_div₀]

/-- **Fill-local helper — THE DIGAMMA REFLECTION FORMULA** `ψ(1−z) − ψ(z) = π cot(πz)`.

Proved by logarithmic differentiation of `Γ(z)Γ(1−z) = π/sin(πz)`
(`Complex.Gamma_mul_Gamma_one_sub`): both sides of that identity are differentiated at `z`, the
two derivatives are identified by `HasDerivAt.unique`, and the result is divided by
`Γ(z)Γ(1−z) = π/sin(πz)`. This is the statement paper §1.1 cites and Mathlib lacks. -/
private theorem digamma_reflection (z : ℂ) (hz : ∀ m : ℕ, z ≠ -m) (hz1 : ∀ m : ℕ, 1 - z ≠ -m)
    (hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    Complex.digamma (1 - z) - Complex.digamma z
      = (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)) := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz
  have hG1z : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero hz1
  have hG1 : HasDerivAt Complex.Gamma (deriv Complex.Gamma z) z :=
    (Complex.differentiableAt_Gamma z hz).hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hG2 : HasDerivAt (fun w : ℂ => Complex.Gamma (1 - w))
      (deriv Complex.Gamma (1 - z) * (-1)) z :=
    ((Complex.differentiableAt_Gamma (1 - z) hz1).hasDerivAt).comp z hlin
  have hprod : HasDerivAt (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w))
      (deriv Complex.Gamma z * Complex.Gamma (1 - z)
        + Complex.Gamma z * (deriv Complex.Gamma (1 - z) * (-1))) z := hG1.mul hG2
  have hsin' : HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w))
      (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z := by
    have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) z := by
      simpa using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
    exact (Complex.hasDerivAt_sin ((Real.pi : ℂ) * z)).comp z h1
  have hRHS : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))
      ((0 * Complex.sin ((Real.pi : ℂ) * z)
        - (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ)))
        / Complex.sin ((Real.pi : ℂ) * z) ^ 2) z :=
    (hasDerivAt_const z (Real.pi : ℂ)).div hsin' hsin
  have heq : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w))
      = fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w) :=
    funext Complex.Gamma_mul_Gamma_one_sub
  rw [heq] at hprod
  have key := hprod.unique hRHS
  have hval : Complex.Gamma z * Complex.Gamma (1 - z)
      = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) := Complex.Gamma_mul_Gamma_one_sub z
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply]
  have hGH : Complex.Gamma (1 - z) * Complex.Gamma z
      = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) := by rw [mul_comm]; exact hval
  have h1 : deriv Complex.Gamma (1 - z) / Complex.Gamma (1 - z)
        - deriv Complex.Gamma z / Complex.Gamma z
      = (deriv Complex.Gamma (1 - z) * Complex.Gamma z
          - deriv Complex.Gamma z * Complex.Gamma (1 - z))
        / (Complex.Gamma (1 - z) * Complex.Gamma z) := by field_simp
  have h2 : deriv Complex.Gamma (1 - z) * Complex.Gamma z
        - deriv Complex.Gamma z * Complex.Gamma (1 - z)
      = (Real.pi : ℂ) ^ 2 * Complex.cos ((Real.pi : ℂ) * z)
        / Complex.sin ((Real.pi : ℂ) * z) ^ 2 := by linear_combination -key
  rw [h1, h2, hGH]
  field_simp

/-- **Fill-local helper — the exact value of the paper's parity term.**
`Re cot(π(¼ + iτ/2)) = 1/cosh(πτ)`.

`cos(a+ib)·conj(sin(a+ib))` has real part `sin a cos a` and `|sin(a+ib)|² = sin²a cosh²b +
cos²a sinh²b`; at `a = π/4` the first is `1/2` and the second is `½cosh 2b`. With `b = πτ/2`
this is `1/cosh(πτ)`, which is `2e^{−πτ}(1 + O(e^{−2πτ}))` — the paper's `O(e^{−πτ})`, and the
reason the parity dependence is beyond floating point at `τ ≍ T`. -/
private theorem re_cot_quarter (τ : ℝ) :
    (Complex.cos ((Real.pi : ℂ) * (1 / 4 + Complex.I * (τ : ℂ) / 2)) /
      Complex.sin ((Real.pi : ℂ) * (1 / 4 + Complex.I * (τ : ℂ) / 2))).re
      = 1 / Real.cosh (Real.pi * τ) := by
  set b : ℝ := Real.pi * τ / 2 with hb
  have harg : (Real.pi : ℂ) * (1 / 4 + Complex.I * (τ : ℂ) / 2)
      = ((Real.pi / 4 : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I := by
    push_cast [hb]; ring
  have hCS : Real.cosh b ^ 2 - Real.sinh b ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq b
  have h2b : Real.cosh (Real.pi * τ) = Real.cosh b ^ 2 + Real.sinh b ^ 2 := by
    rw [show Real.pi * τ = 2 * b by rw [hb]; ring, Real.cosh_two_mul]
  rw [harg, Complex.cos_add_mul_I, Complex.sin_add_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
    Real.cos_pi_div_four, Real.sin_pi_div_four, Complex.div_re]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), h2b]
  have hCpos : (0:ℝ) < Real.cosh b := Real.cosh_pos b
  have hden : (0:ℝ) < Real.cosh b ^ 2 + Real.sinh b ^ 2 := by
    nlinarith [sq_nonneg (Real.sinh b)]
  field_simp
  nlinarith [hCS]

/-- **O16.** Parity uniformity: `μ_q`'s parity dependence is EXACTLY
`π Re cot(π(¼ + iτ/2))`, by the digamma reflection formula `ψ(1−z) − ψ(z) = π cot(πz)`.

Written with `cos/sin` rather than a `cot` name so that no uncertain Mathlib identifier is
assumed. Stated against `Zeta23.ThmE.muq κ q τ` (`Zeta23/ThmE/Hypotheses.lean:48`), the tree's
`κ`-parameterised density — REUSED, not redefined; `ZetaQ.muDensity` wraps it.
Paper §1.1. Depends on: `Zeta23.ThmE.muq`, `Complex.digamma`.
Rule 17: λ-free, X-free, D₀-free. -/
theorem muq_parity_gap (q : ℕ) (τ : ℝ) :
    Zeta23.ThmE.muq 1 q τ - Zeta23.ThmE.muq 0 q τ
      = (1 / (2 * Real.pi)) * (Real.pi *
          (Complex.cos ((Real.pi : ℂ) * (1 / 4 + Complex.I * (τ : ℂ) / 2)) /
            Complex.sin ((Real.pi : ℂ) * (1 / 4 + Complex.I * (τ : ℂ) / 2))).re) := by
  have hpiC : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hzre : ((1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ)).re = 1 / 4 := by simp
  have hsre : ((3 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ)).re = 3 / 4 := by simp
  have hzne : ∀ m : ℕ, (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ) ≠ -m := by
    intro m h
    have h2 := congrArg Complex.re h
    rw [hzre] at h2
    simp only [Complex.neg_re, Complex.natCast_re] at h2
    have h3 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hsne : ∀ m : ℕ, (3 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ) ≠ -m := by
    intro m h
    have h2 := congrArg Complex.re h
    rw [hsre] at h2
    simp only [Complex.neg_re, Complex.natCast_re] at h2
    have h3 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hzim : ((1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ)).im = τ / 2 := by simp
  have hsim : ((3 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ)).im = τ / 2 := by simp
  -- `1 − (¼ + iτ/2) = conj(¾ + iτ/2)`: this is where `Re ψ(conj w) = Re ψ(w)` is used.
  have h1z : (1 : ℂ) - (1 / 4 + Complex.I * (τ : ℂ) / 2)
      = starRingEnd ℂ (3 / 4 + Complex.I * (τ : ℂ) / 2) := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hzre, hsre]; norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im, hzim, hsim]; ring
  have hz1ne : ∀ m : ℕ, (1 : ℂ) - (1 / 4 + Complex.I * (τ : ℂ) / 2) ≠ -m := by
    intro m h
    have h2 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at h2
    rw [hzre] at h2
    have h3 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  have hsinne : Complex.sin ((Real.pi : ℂ) * (1 / 4 + Complex.I * (τ : ℂ) / 2)) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    have hzk : (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ) = (k : ℂ) :=
      mul_left_cancel₀ hpiC (by rw [hk]; ring)
    have h2 := congrArg Complex.re hzk
    rw [hzre] at h2
    simp only [Complex.intCast_re] at h2
    have h4 : ((4 * k : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h5 : (4 * k : ℤ) = 1 := by exact_mod_cast h4
    omega
  have hrefl := digamma_reflection (1 / 4 + Complex.I * (τ : ℂ) / 2) hzne hz1ne hsinne
  rw [h1z, digamma_conj_re _ hsne] at hrefl
  have hre := congrArg Complex.re hrefl
  simp only [Complex.sub_re, Complex.conj_re, Complex.re_ofReal_mul] at hre
  have hgap : Zeta23.ThmE.muq 1 q τ - Zeta23.ThmE.muq 0 q τ
      = (1 / (2 * Real.pi)) *
        ((Complex.digamma (3 / 4 + Complex.I * (τ : ℂ) / 2)).re
          - (Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)).re) := by
    unfold Zeta23.ThmE.muq
    norm_num
    ring
  rw [hgap, hre]

/-- **O16′.** Consequently the parity gap is `O(e^{−πτ})` — uniformly in `q`, so the even and
odd families see the SAME density to all orders that matter, and no parity-dependent constant
enters the certificate.

Paper §1.1.
Depends on: `muq_parity_gap`. Rule 17: λ-free, X-free, D₀-free. -/
theorem muq_parity_gap_small (q : ℕ) :
    (fun τ : ℝ => Zeta23.ThmE.muq 1 q τ - Zeta23.ThmE.muq 0 q τ)
      =O[atTop] (fun τ : ℝ => Real.exp (-(Real.pi * τ))) := by
  -- O16 evaluates the gap to `1/(2 cosh πτ)`, and `2 cosh y ≥ e^y`; the bound is GLOBAL
  -- (constant 1, every `τ`), and in particular uniform in `q` — `q` does not occur.
  refine Asymptotics.isBigO_of_le _ (fun τ => ?_)
  rw [muq_parity_gap q τ, re_cot_quarter τ]
  have hcosh : Real.exp (Real.pi * τ) ≤ 2 * Real.cosh (Real.pi * τ) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(Real.pi * τ))
    field_simp
    linarith
  have hcpos : (0:ℝ) < Real.cosh (Real.pi * τ) := Real.cosh_pos _
  have hval : (1 / (2 * Real.pi)) * (Real.pi * (1 / Real.cosh (Real.pi * τ)))
      = 1 / (2 * Real.cosh (Real.pi * τ)) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hval]
  have hle : 1 / (2 * Real.cosh (Real.pi * τ)) ≤ Real.exp (-(Real.pi * τ)) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hcosh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
    abs_of_pos (Real.exp_pos _)]
  exact hle

/-! ## O17–O18 — the four constants and the two conclusions -/

/-- **O17a, the first of Corollary 3's four constants.** `C_even,dyad = 4π⁴/27 = 2·C_dyad`
 — the doubling of O13 applied to Corollary 2's `C_dyad = 2π⁴/27`.

Paper §1.1.
Depends on: `ZetaQ.CfamEvenDyadic`, `ZetaQ.CfamDyadic`. Rule 17: λ-free. -/
theorem CfamEvenDyadic_eq : ZetaQ.CfamEvenDyadic = 2 * ZetaQ.CfamDyadic := by
  unfold ZetaQ.CfamEvenDyadic ZetaQ.CfamDyadic
  ring

/-- **O17b.** `C_even = π⁴/9 = 2·C` over `q ≤ Q`.

Paper §1.1. Depends on: `ZetaQ.CfamEven`, `ZetaQ.Cfam`.
Rule 17: λ-free. -/
theorem CfamEven_eq : ZetaQ.CfamEven = 2 * ZetaQ.Cfam := by
  unfold ZetaQ.CfamEven ZetaQ.Cfam
  ring

/-- **O17c, R-A5 kept visible in Corollary 3 too.** What Corollary 3 SHIPS is
`Payoff.Pcert_even = 0.6919`, strictly weaker than the paper's
`ZetaQ.PconstEvenDyadic = 0.6919434301` (`λ* = 1.1015998422`).

This constant has NO shipped script anchor — `4π⁴/27` is absent from the target
lists of `payoff_hp2.py`, `payoff_final2.py` and `fb.gates()`, and from every log in
the paper's own logs. The shipped solver was re-run and confirmed
`0.691943430126`. A repo-hygiene gap, not a mathematical one.
Paper §1.1.
Depends on: `Payoff.Pcert_even`, `ZetaQ.PconstEvenDyadic`. Rule 17: λ-free. -/
theorem Pcert_even_lt_PconstEvenDyadic :
    ((Payoff.Pcert_even : ℚ) : ℝ) < ZetaQ.PconstEvenDyadic := by
  unfold Payoff.Pcert_even ZetaQ.PconstEvenDyadic
  norm_num

/-- **O17d.** The same for the `q ≤ Q` even family: shipped `0.6980` vs the paper's
`0.6980745436` at `C = π⁴/9`. `Payoff.PconstEvenQ` is defined in
`ZetaQ/Payoff.lean` and belongs in `Defs.lean` (its three siblings are already frozen there).

Rule 17: λ-free. -/
theorem Pcert_evenQ_lt_PconstEvenQ :
    ((Payoff.Pcert_evenQ : ℚ) : ℝ) < Payoff.PconstEvenQ := by
  unfold Payoff.Pcert_evenQ Payoff.PconstEvenQ
  norm_num

/-- **O17. Corollary 3, EVEN primitive, DYADIC — the Sono-comparable statement.**
At out-zone constant `2·C_dyad = 4π⁴/27` the delivered constant is `P_even,dyad`, shipped at
the certificate's digit count `Payoff.Pcert_even = 0.6919` (paper's `0.6919434301` at
`λ* = 1.1015998422`).

This is `Normalisation.subfamily_passage` at `α = 1/2` composed with
`Payoff.payoff_feasible_even_dyadic`.

**REPAIRED (D14), and now PROVED.** As frozen this statement could not compose with
`subfamily_passage` at all: its `hfull` bounded `pay` at a FREE parameter `fullFamDyad`,
while `subfamily_passage` needed the *constant* `Normalisation.fullFamily`, and nothing
linked the two — so even after that repair the composition was blocked by a name. (The same
defect in `subfamily_passage` itself was FALSENESS, not just a blocked composition; see
`Normalisation.PassageInterface`.) The free parameter and `hfull` are replaced by the bundled
`Normalisation.PassageInterface ZetaQ.CfamDyadic`, whose `fullFamily` IS the constant, exactly
as in the already-correct `corollary3_even_qQ`. The conclusion is unchanged, at the same
constant `Payoff.Pcert_even`.

Paper §1.1, §12.3.
Depends on: `Normalisation.subfamily_passage`, `Payoff.payoff_feasible_even_dyadic`,
`Payoff.B_eq_Bgen`; and, inside `PassageInterface`, `famCardEven_asymp`,
`zeroCountEven_asymp`, `in_zone_coefficient_unchanged`, `out_zone_constant_doubles`.
**Rule 17: `1 < lam ∧ lam < 2` explicit; the design point is `λ* = 1.1015998422 > 1`.** -/
theorem corollary3_even_dyadic
    (evenFam : Normalisation.Subfamily)
    (hdens : Normalisation.SubfamilyAdmissible evenFam (1 / 2))
    (I : Normalisation.PassageInterface ZetaQ.CfamDyadic) :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Payoff.Admissible lam v ∧
      ((Payoff.Pcert_even : ℚ) : ℝ) ≤ I.pay evenFam v := by
  obtain ⟨lam, v, hlam1, hlam2, hadm, hB⟩ := Payoff.payoff_feasible_even_dyadic
  refine ⟨lam, v, hlam1, hlam2, hadm, ?_⟩
  have hCpos : (0 : ℝ) < ZetaQ.CfamDyadic := by
    have := Real.pi_pos
    unfold ZetaQ.CfamDyadic
    positivity
  have hpass := Normalisation.subfamily_passage evenFam (1 / 2) (by norm_num) hdens
    ZetaQ.CfamDyadic hCpos I lam v hlam1 hlam2 hadm
  have hdiv : ZetaQ.CfamDyadic / (1 / 2 : ℝ) = 4 * Real.pi ^ 4 / 27 := by
    unfold ZetaQ.CfamDyadic
    ring
  rw [hdiv] at hpass
  rw [Payoff.B_eq_Bgen _ hadm] at hB
  linarith

/-- **O18. The ODD mirror**, by the projector `½Σ*(1 − χ(−1))`, at the SAME constants
: "The identical argument … gives the odd primitive family at the same
constants — a class in which the literature contains no result at all."

Every obligation O6–O16 has an odd counterpart with `S(q)` negated (`oddPrimCount_eq`); O13's
positivity and O17's payoff instance are parity-blind.

**REPAIRED (D14) and PROVED, exactly as `corollary3_even_dyadic`** — the same `fullFamDyad`
free-parameter defect, the same replacement by `PassageInterface`. That the proof below is
character-for-character the even one, with `oddFam` in place of `evenFam`, is the Lean form
of the paper's "the identical argument": the only parity-dependent inputs (`oddPrimCount_eq`,
`parity_projector_odd`) live inside the interface's `den_density` and `delivers`, and the
payoff instance is parity-blind.
Paper §1.1.
Depends on: `parity_projector_odd`, `oddPrimCount_eq`, `corollary3_even_dyadic`'s chain.
**Rule 17: `1 < lam ∧ lam < 2` explicit.** -/
theorem corollary3_odd_dyadic
    (oddFam : Normalisation.Subfamily)
    (hdens : Normalisation.SubfamilyAdmissible oddFam (1 / 2))
    (I : Normalisation.PassageInterface ZetaQ.CfamDyadic) :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Payoff.Admissible lam v ∧
      ((Payoff.Pcert_even : ℚ) : ℝ) ≤ I.pay oddFam v := by
  obtain ⟨lam, v, hlam1, hlam2, hadm, hB⟩ := Payoff.payoff_feasible_even_dyadic
  refine ⟨lam, v, hlam1, hlam2, hadm, ?_⟩
  have hCpos : (0 : ℝ) < ZetaQ.CfamDyadic := by
    have := Real.pi_pos
    unfold ZetaQ.CfamDyadic
    positivity
  have hpass := Normalisation.subfamily_passage oddFam (1 / 2) (by norm_num) hdens
    ZetaQ.CfamDyadic hCpos I lam v hlam1 hlam2 hadm
  have hdiv : ZetaQ.CfamDyadic / (1 / 2 : ℝ) = 4 * Real.pi ^ 4 / 27 := by
    unfold ZetaQ.CfamDyadic
    ring
  rw [hdiv] at hpass
  rw [Payoff.B_eq_Bgen _ hadm] at hB
  linarith

/-- **O17′.** Even (resp. odd) primitive over `q ≤ Q`: the constant is `0.6980745436` at
`C_even = π⁴/9` (L107), shipped as `Payoff.Pcert_evenQ = 0.6980`.

This was the ONE Corollary-3 instance that was already stated correctly (its `hfull` sat at
the constant `Normalisation.fullFamily`, not at a free parameter) and already proved; it was
the template for repairing the other two. Its `pay` + `hfull` pair is now the bundled
`Normalisation.PassageInterface ZetaQ.Cfam`, since `subfamily_passage`'s own interface had to
change to repair it — the conclusion, the constant and the proof shape are untouched.

Paper §1.1.
Depends on: `Normalisation.subfamily_passage`, `Payoff.payoff_feasible_even_qQ`.
**Rule 17: `1 < lam ∧ lam < 2` explicit; the design point is `λ* = 1.1329788821 > 1`.** -/
theorem corollary3_even_qQ
    (evenFam : Normalisation.Subfamily)
    (hdens : Normalisation.SubfamilyAdmissible evenFam (1 / 2))
    (I : Normalisation.PassageInterface ZetaQ.Cfam) :
    ∃ (lam : ℝ) (v : ℝ → ℝ), 1 < lam ∧ lam < 2 ∧ Payoff.Admissible lam v ∧
      ((Payoff.Pcert_evenQ : ℚ) : ℝ) ≤ I.pay evenFam v := by
  obtain ⟨lam, v, hlam1, hlam2, hadm, hB⟩ := Payoff.payoff_feasible_even_qQ
  refine ⟨lam, v, hlam1, hlam2, hadm, ?_⟩
  have hCpos : (0 : ℝ) < ZetaQ.Cfam := by
    have := Real.pi_pos
    unfold ZetaQ.Cfam
    positivity
  have hpass := Normalisation.subfamily_passage evenFam (1 / 2) (by norm_num) hdens
    ZetaQ.Cfam hCpos I lam v hlam1 hlam2 hadm
  have hdiv : ZetaQ.Cfam / (1 / 2 : ℝ) = Real.pi ^ 4 / 9 := by
    unfold ZetaQ.Cfam
    ring
  rw [hdiv] at hpass
  rw [Payoff.B_eq_Bgen _ hadm] at hB
  linarith

/-! ## O19–O20 — the two remarks. DOCUMENTATION ONLY; no lemma is manufactured.

**O19, a NEGATIVE claim — not formalizable.** A parity-refined sieve at
budget `½(N + Q² − 1)` would restore `C` rather than doubling it, but (a) the `n ≡ −m` route
fails OUT-ZONE at `λ > 1` by `Q^{λ−1}` — the same mechanism as §4's cross term, with no band
separation available since both halves share a band — and (b) no such sieve appears to be
available in the literature. Mirroring Sono's smooth weight `W ≤ 1` on `[1,2]` would further
inflate `C` by `3/(2∫W(x)x dx)`. This is a claim about the state of the literature and about
the failure of a route; it has no Lean content and none is written. Rule 17 note: the `Q^{λ−1}`
failure is a REASON `λ > 1` forces the positivity route, never a hypothesis that `λ ≤ 1`.

**O20, the 0.3693 trap — stated, but OUT OF SCOPE.** "Positivity alone in
both zones would double the in-zone coefficient too and prove only 0.3693 (§11 at in-zone
weight 2|α|) — which is not this corollary." The statement lives at
`ZetaQ.Normalisation.Trap0p3693` as `minBgen 2 (2·C_dyad) = 2 − 0.3693`. **It needs a LOWER
bound on `min B`, which the feasibility route cannot supply.** See
this file's R-B1 header block.
It is not load-bearing for Theorem 1 or Corollary 3 — it is the justification for why
obligation (ii) of §12.3 is required — but it is on the record, not dropped. -/

end ZetaQ.Cor3
