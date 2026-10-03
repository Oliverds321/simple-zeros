/-
A2a_S3e_TailParts (L7_8, round 5): split of `s3_tail` (Step 3 tail, sec_shell.tex l.338) into three nodes.

* `s3_tail_qphi_pt`: for the `q/φ` kind the truncated sum is exact,
  `Σ_{1≤f≤Q} λ_e(f) ∏_{p|f} δ_p = 𝔈_{j,r}(e)` for `1 ≤ e ≤ Q` (`λ_e` lives on `f | rad e`).
* `s3_tail_plain_pt`: for the plain kind, `|Σ_{1≤f≤Q} λ_e(f) ∏δ_p − 𝔈_{j,r}(e)| ≤ 2^{ω(e)+1} σ(r) / Q`
  (Euler product with `ζ(2) = π²/6`, then the tail over `f > Q`: `f = f₁f₂f₃f₄` with weight
  `1/(f₁ f₃² f₄)`, `Σ_{f₃ > Y} f₃⁻² ≤ 2/Y`).
* `s3_tail_sum`: the sum over lines and `e` of `|c_e| |∫_{I_j} w(qe/Q)|` against that bound is
  `≪ δ Q r (1 + log Q)`, for the plain kind.
* `s3_tail` (in `A2a_S3e_Tail`) follows from the three.
-/
import ZetaShell.Lemma2.A2a_S3_Defs
import ZetaShell.Lemma2.A2a_S3e_TailGeom
import ZetaShell.Lemma2.A2a_S3e_TailPlain

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem tp_nf_toFinset (n : ℕ) :
    (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
  rw [Nat.factors_eq]
  rfl

theorem s3_tail_qphi_pt (Q r : ℕ) (j : ℤ) (e : ℕ) (hr : 1 ≤ r) (hj : j ≠ 0) (he : 1 ≤ e) (heQ : e ≤ Q) :
    ∑ f ∈ Finset.Icc 1 Q, lam FKind.qphi e f * deltaProd r j f = Ecoef FKind.qphi r j.natAbs e := by
  classical
  have he0 : e ≠ 0 := by omega
  have hvan : ∀ f ∈ Finset.Icc 1 Q, f ∉ e.divisors → lam FKind.qphi e f * deltaProd r j f = 0 := by
    intro f _ hfd
    unfold lam
    split_ifs with hsq
    · have hex : ∃ p ∈ f.primeFactors, ¬ p ∣ e := by
        by_contra hcon
        push Not at hcon
        apply hfd
        rw [Nat.mem_divisors]
        refine ⟨?_, he0⟩
        rw [← Nat.prod_primeFactors_of_squarefree hsq]
        exact Finset.prod_primes_dvd e (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hcon
      obtain ⟨p, hp, hpe⟩ := hex
      rw [Finset.prod_eq_zero hp (by simp [hE, hpe]), zero_mul]
    · rw [zero_mul]
  have hsub : e.divisors ⊆ Finset.Icc 1 Q := by
    intro f hf
    rw [Nat.mem_divisors] at hf
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_dvd_of_pos hf.1 (by omega), le_trans (Nat.le_of_dvd (by omega) hf.1) heQ⟩
  rw [← Finset.sum_subset hsub hvan]
  have hsq : ∑ f ∈ e.divisors, lam FKind.qphi e f * deltaProd r j f
      = ∑ f ∈ e.divisors with Squarefree f, lam FKind.qphi e f * deltaProd r j f := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro f _
    unfold lam
    split_ifs <;> simp
  rw [hsq, Nat.sum_divisors_filter_squarefree he0, tp_nf_toFinset]
  have hterm : ∀ t ∈ e.primeFactors.powerset, lam FKind.qphi e t.val.prod * deltaProd r j t.val.prod
      = ∏ p ∈ t, (-(if ¬ (p : ℤ) ∣ r ∧ ¬ (p : ℤ) ∣ j then 1 / (p : ℝ)
          else if (p : ℤ) ∣ r ∧ (p : ℤ) ∣ j then 1 else 0)) := by
    intro t ht
    have htP : t ⊆ e.primeFactors := Finset.mem_powerset.mp ht
    have htp : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (htP hp)
    have hval : t.val.prod = ∏ p ∈ t, p := by simpa using (Finset.prod_val t)
    have hsqf : Squarefree (∏ p ∈ t, p) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp p' hp' hne
        exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (htp p hp) (htp p' hp')).mpr hne)
      · intro p hp
        exact (htp p hp).prime.squarefree
    rw [hval]
    unfold lam deltaProd
    rw [if_pos hsqf, Nat.primeFactors_prod htp, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpe : p ∣ e := Nat.dvd_of_mem_primeFactors (htP hp)
    simp only [hE, hpe, if_true]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, ← Finset.prod_one_add]
  have hdr : ∀ p : ℕ, ((p : ℤ) ∣ (r : ℤ) ↔ p ∣ r) := fun p => Int.natCast_dvd_natCast
  have hdj : ∀ p : ℕ, ((p : ℤ) ∣ j ↔ p ∣ j.natAbs) := fun p => Int.natCast_dvd
  have hg0 : Nat.gcd r j.natAbs ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by omega)).ne'
  unfold Ecoef
  simp only [one_mul]
  by_cases hc : ∃ p ∈ e.primeFactors, p ∣ r ∧ p ∣ j.natAbs
  · obtain ⟨p, hp, hpr, hpj⟩ := hc
    have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpe : p ∣ e := Nat.dvd_of_mem_primeFactors hp
    have hpg : p ∈ (Nat.gcd r j.natAbs).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpP, Nat.dvd_gcd hpr hpj, hg0⟩
    rw [Finset.prod_eq_zero hp (by simp [hdr, hdj, hpr, hpj]),
      Finset.prod_eq_zero (i := p) hpg (by simp [hE, hpe]), mul_zero]
  · push Not at hc
    have h2 : ∏ p ∈ (Nat.gcd r j.natAbs).primeFactors, hE FKind.qphi e p = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpg : p ∣ Nat.gcd r j.natAbs := Nat.dvd_of_mem_primeFactors hp
      have hpe : ¬ p ∣ e := by
        intro hpe
        exact hc p (Nat.mem_primeFactors.mpr ⟨hpP, hpe, he0⟩) (Nat.dvd_trans hpg (Nat.gcd_dvd_left _ _))
          (Nat.dvd_trans hpg (Nat.gcd_dvd_right _ _))
      simp [hE, hpe]
    rw [h2, mul_one, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hcp := hc p hp
    by_cases hpr : p ∣ r
    · have hpj : ¬ p ∣ j.natAbs := hcp hpr
      have hmul : p ∣ r * j.natAbs := Dvd.dvd.mul_right hpr _
      simp [hdr, hdj, hpr, hpj, hmul]
    · by_cases hpj : p ∣ j.natAbs
      · have hmul : p ∣ r * j.natAbs := Dvd.dvd.mul_left hpj _
        simp [hdr, hdj, hpr, hpj, hmul]
      · have hmul : ¬ p ∣ r * j.natAbs := by
          intro h
          rcases (Nat.Prime.dvd_mul hpP).mp h with h' | h'
          · exact hpr h'
          · exact hpj h'
        simp [hdr, hdj, hpr, hpj, hmul, sub_eq_add_neg]

theorem s3_tail_plain_pt (Q r : ℕ) (j : ℤ) (e : ℕ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (hj : j ≠ 0) (he : 1 ≤ e) :
    |∑ f ∈ Finset.Icc 1 Q, lam FKind.plain e f * deltaProd r j f - Ecoef FKind.plain r j.natAbs e|
      ≤ 2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * (ArithmeticFunction.sigma 1 r : ℝ) / Q := by
  exact s3_tail_plain_pt_proof Q r j e hQ hr hj he

theorem s3_tail_sum (F : Fam) (hF : F.kind = FKind.plain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q r : ℕ) (R1 η δ : ℝ), 2 ≤ Q → 1 ≤ r → (r : ℝ) ≤ R1 →
    2 * R1 ≤ Q → |η| ≤ 1 / (r * R1) → 0 < δ → δ < 1 →
    ∑ j ∈ lineSet (lineM Q r η δ), ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
      ∑ e ∈ Finset.Icc 1 Q, |cE FKind.plain e| *
        |∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)| *
        (2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * (ArithmeticFunction.sigma 1 r : ℝ) / Q)
      ≤ C * (δ * Q * r * (1 + Real.log Q)) := by
  exact s3_tail_sum_of_geom F

end TrackF
end ZetaShell
