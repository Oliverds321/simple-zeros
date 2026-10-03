/-
A2a_S3a_Collapse (L7_8, round 4): Step 1 in the form used by `s3_reindex`:
* `omega_lam_expand`: `Ω_ω(q) = Σ_{1≤e≤Q} c_e w(qe/Q) Σ_{1≤f≤Q, f|q} λ_e(f)` for `1 ≤ q ≤ Q`;
* `line_collapse`: `Σ_{e≤Q} c_e Σ_{f≤Q} λ_e(f) N_j(e,f) = Σ_{k ∈ K_j} 1[(k,j)=1] Ω(rk − r′j)` when every `q = rk − r′j`
  with `k ∈ K_j` lies in `[1, Q]`.
-/
import ZetaShell.Lemma2.A2a_S3_Defs
import ZetaShell.Lemma2.A2a_S1_Expansion
import ZetaShell.Lemma2.A2a_S3c_Irrelevant

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem sum_dvd_lam (k : FKind) (e q Q : ℕ) (hq1 : 1 ≤ q) (hqQ : q ≤ Q) :
    ∑ f ∈ Finset.Icc 1 Q, (if f ∣ q then lam k e f else 0) = hFull k e q := by
  classical
  rw [hFull_eq_sum_subsets k e q hq1, ← Finset.sum_filter]
  have hfilt : (Finset.Icc 1 Q).filter (fun f => f ∣ q) = q.divisors := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hf⟩; exact ⟨hf, by omega⟩
    · rintro ⟨hf, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hf (by omega), le_trans (Nat.le_of_dvd (by omega) hf) hqQ⟩, hf⟩
  rw [hfilt]
  have hsq : ∑ f ∈ q.divisors, lam k e f = ∑ f ∈ q.divisors with Squarefree f, lam k e f := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro f _
    unfold lam
    split_ifs <;> rfl
  rw [hsq, Nat.sum_divisors_filter_squarefree (by omega), normalizedFactors_toFinset]
  apply Finset.sum_congr rfl
  intro t ht
  have htP : t ⊆ q.primeFactors := Finset.mem_powerset.mp ht
  have htp : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (htP hp)
  have hval : t.val.prod = ∏ p ∈ t, p := by simpa using (Finset.prod_val t)
  have hsqf : Squarefree (∏ p ∈ t, p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp p' hp' hne
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (htp p hp) (htp p' hp')).mpr hne)
    · intro p hp
      exact (htp p hp).prime.squarefree
  rw [hval]
  unfold lam
  rw [if_pos hsqf, Nat.primeFactors_prod htp]

theorem omega_lam_expand (F : Fam) (Q q : ℕ) (hq1 : 1 ≤ q) (hqQ : q ≤ Q) :
    ZetaShell.OmegaW Q (F.omega Q) q = ∑ e ∈ Finset.Icc 1 Q, cE F.kind e * F.w ((q : ℝ) * e / Q) *
      ∑ f ∈ Finset.Icc 1 Q, (if f ∣ q then lam F.kind e f else 0) := by
  rw [omegaW_expand F Q q hq1]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self Q q))]
  · apply Finset.sum_congr rfl
    intro e _
    rw [sum_dvd_lam F.kind e q Q hq1 hqQ]
  · intro e he1 he2
    rw [Finset.mem_Icc] at he1 he2
    have hgt : Q / q < e := by
      by_contra h; push_neg at h; exact he2 ⟨he1.1, h⟩
    have h1 : Q < q * e := lt_of_lt_of_le (Nat.lt_mul_div_succ Q (by omega)) (Nat.mul_le_mul_left q hgt)
    have h2 : (Q : ℝ) < (q : ℝ) * e := by exact_mod_cast h1
    rw [F.w_eq_zero_of_gt_one (by rw [lt_div_iff₀ hQpos]; linarith)]
    ring

theorem line_collapse (F : Fam) (Q : ℕ) (r r' j : ℤ) (lo hi : ℝ)
    (hq : ∀ k ∈ Finset.Icc ⌈(lo + r' * j) / r⌉ ⌊(hi + r' * j) / r⌋, 1 ≤ r * k - r' * j ∧ r * k - r' * j ≤ Q) :
    ∑ e ∈ Finset.Icc 1 Q, cE F.kind e * ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * lineCount F Q r r' j e f lo hi
      = ∑ k ∈ Finset.Icc ⌈(lo + r' * j) / r⌉ ⌊(hi + r' * j) / r⌋,
          (if Int.gcd k j = 1 then ZetaShell.OmegaW Q (F.omega Q) (r * k - r' * j).toNat else 0) := by
  classical
  unfold lineCount
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun e _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := hq k hk
  set qn : ℕ := (r * k - r' * j).toNat with hqn
  have hqnZ : ((qn : ℕ) : ℤ) = r * k - r' * j := Int.toNat_of_nonneg (by omega)
  have hqnR : ((r * k - r' * j : ℤ) : ℝ) = (qn : ℝ) := by rw [← hqnZ]; push_cast; ring
  have hq1 : 1 ≤ qn := by omega
  have hqQ : qn ≤ Q := by omega
  by_cases hg : Int.gcd k j = 1
  · rw [if_pos hg, omega_lam_expand F Q qn hq1 hqQ]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    have hdiv : ((f : ℤ) ∣ r * k - r' * j) ↔ f ∣ qn := by
      rw [← hqnZ]; exact Int.natCast_dvd_natCast
    by_cases hf : f ∣ qn
    · rw [if_pos ⟨hg, hdiv.mpr hf⟩, if_pos hf, hqnR]; ring
    · rw [if_neg (fun h => hf (hdiv.mp h.2)), if_neg hf]; ring
  · rw [if_neg hg]
    apply Finset.sum_eq_zero
    intro e _
    apply Finset.sum_eq_zero
    intro f _
    rw [if_neg (fun h => hg h.1)]
    ring

end TrackF
end ZetaShell
