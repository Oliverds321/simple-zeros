/-
A2a_S1_Expansion (L7_8, 28 Sep 2026): **Step 1 of the proof of Lemma 2(a)** (sec_shell.tex l.277–278 and l.314–317),
pointwise form, sorry-free.

Draft: "`Ω_ω(d) = Σ_e c_e w(de/Q) h_e(d)` with `c_e = μ(e)/e`, `h_e(q) = (φ(q)/q)1[(e,q)=1]` (plain), respectively
`c_e = μ(e)/φ(e)`, `h_e(q) = 1[(e,q)=1]` (`q/φ` kind)." "Each `h_e` is multiplicative with `h_e(p^k) = h_e(p)`
and `h_e = 1 * λ_e`, where `λ_e` is supported on squarefree numbers with `λ_e(p) = h_e(p) − 1`."

Proved:
* `omegaW_expand`: L7_6's `OmegaW Q ω d` (lem:shell-1's weight, the object in `lemma2a`) equals
  `Σ_{1≤e≤Q/d} c_e w(de/Q) h_e(d)` for the three families (`1 ≤ d`). This ties the Lean weights to the family
  formula of l.277 used by the proof (and by `Ecoef`, `gProf`).
* `hFull_eq_prod`: `h_e(d) = ∏_{p | d} h_e(p)` (`1 ≤ d`), from Euler's product for `φ` (Mathlib
  `Nat.totient_eq_mul_prod_factors`).
* `hFull_eq_sum_subsets`: `h_e(d) = Σ_{t ⊆ primes(d)} ∏_{p∈t} λ_e(p)` with `λ_e(p) = h_e(p) − 1`, i.e.
  `h_e = 1 * λ_e` with `λ_e` on squarefree `f = ∏ t` (Mathlib `Finset.prod_one_add`).
-/
import ZetaShell.Lemma2.A2a_OutsideShells

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- `h_e(d)` for every `d`. -/
def hFull (k : FKind) (e d : ℕ) : ℝ :=
  match k with
  | .plain => if Nat.Coprime e d then (Nat.totient d : ℝ) / d else 0
  | .qphi => if Nat.Coprime e d then 1 else 0

/-- **Step 1, the weight.** `Ω_ω(d) = Σ_{1≤e≤Q/d} c_e w(de/Q) h_e(d)`. -/
theorem omegaW_expand (F : Fam) (Q d : ℕ) (hd : 1 ≤ d) :
    ZetaShell.OmegaW Q (F.omega Q) d =
      ∑ e ∈ Finset.Icc 1 (Q / d), cE F.kind e * F.w ((d : ℝ) * e / Q) * hFull F.kind e d := by
  unfold ZetaShell.OmegaW
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  have hdR : (d : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  have heR : (e : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ e := by exact_mod_cast he1
                               linarith
  by_cases hc : Nat.Coprime e d
  · cases F
    · simp only [Fam.omega, Fam.kind, cE, hFull, if_pos hc]
      push_cast
      field_simp
    · simp only [Fam.omega, Fam.kind, cE, hFull, if_pos hc]
      push_cast
      field_simp
    · simp only [Fam.omega, Fam.kind, cE, hFull, if_pos hc]
      have hphi : Nat.totient (d * e) = Nat.totient d * Nat.totient e := Nat.totient_mul hc.symm
      have hpd : (Nat.totient d : ℝ) ≠ 0 := by
        have : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
        exact_mod_cast this.ne'
      have hpe : (Nat.totient e : ℝ) ≠ 0 := by
        have : 0 < Nat.totient e := Nat.totient_pos.mpr (by omega)
        exact_mod_cast this.ne'
      rw [hphi]
      push_cast
      field_simp
  · cases F <;> simp [Fam.kind, hFull, if_neg hc]

/-- `h_e(d) = ∏_{p | d} h_e(p)` for `d ≥ 1`. -/
theorem hFull_eq_prod (k : FKind) (e d : ℕ) (hd : 1 ≤ d) :
    hFull k e d = ∏ p ∈ d.primeFactors, hE k e p := by
  by_cases hc : Nat.Coprime e d
  · have hnd : ∀ p ∈ d.primeFactors, ¬ p ∣ e := by
      intro p hp hpe
      have hp' := Nat.mem_primeFactors.mp hp
      have : p ∣ Nat.gcd e d := Nat.dvd_gcd hpe hp'.2.1
      rw [hc] at this
      exact hp'.1.one_lt.ne' (Nat.dvd_one.mp this)
    cases k
    · simp only [hFull, hE, if_pos hc]
      rw [Finset.prod_congr rfl (fun p hp => if_neg (hnd p hp))]
      have h := Nat.totient_eq_mul_prod_factors d
      have hR : (Nat.totient d : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - ((p : ℕ) : ℝ)⁻¹) := by
        have := congrArg (fun x : ℚ => (x : ℝ)) h
        push_cast at this
        exact this
      have hdR : (d : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                                   linarith
      rw [hR]
      field_simp
    · simp only [hFull, hE, if_pos hc]
      rw [Finset.prod_congr rfl (fun p hp => if_neg (hnd p hp))]
      simp
  · obtain ⟨p, hp, hpe, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
    cases k
    · simp only [hFull, if_neg hc]
      symm
      apply Finset.prod_eq_zero hmem
      simp [hE, hpe]
    · simp only [hFull, if_neg hc]
      symm
      apply Finset.prod_eq_zero hmem
      simp [hE, hpe]

/-- **Step 1, `h_e = 1 * λ_e`.** `h_e(d) = Σ_{t ⊆ primes(d)} ∏_{p ∈ t} λ_e(p)`, `λ_e(p) = h_e(p) − 1`. -/
theorem hFull_eq_sum_subsets (k : FKind) (e d : ℕ) (hd : 1 ≤ d) :
    hFull k e d = ∑ t ∈ d.primeFactors.powerset, ∏ p ∈ t, (hE k e p - 1) := by
  rw [hFull_eq_prod k e d hd, ← Finset.prod_one_add]
  apply Finset.prod_congr rfl
  intro p _
  ring

/-- **Step 1, combined (pointwise).** `Ω_ω(d) = Σ_e c_e w(de/Q) Σ_{f | d squarefree} λ_e(f)`. -/
theorem omegaW_step1 (F : Fam) (Q d : ℕ) (hd : 1 ≤ d) :
    ZetaShell.OmegaW Q (F.omega Q) d =
      ∑ e ∈ Finset.Icc 1 (Q / d), cE F.kind e * F.w ((d : ℝ) * e / Q) *
        ∑ t ∈ d.primeFactors.powerset, ∏ p ∈ t, (hE F.kind e p - 1) := by
  rw [omegaW_expand F Q d hd]
  apply Finset.sum_congr rfl
  intro e _
  rw [hFull_eq_sum_subsets F.kind e d hd]

end TrackF
end ZetaShell
