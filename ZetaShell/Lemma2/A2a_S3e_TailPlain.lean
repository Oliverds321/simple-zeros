/-
A2a_S3e_TailPlain (L7_8c, cloud, 3 Oct 2026): proof of `s3_tail_plain_pt` (plain kind, Step 3 tail,
sec_shell.tex l.338), as `s3_tail_plain_pt_proof` with the statement of the node.

Write `a(f) = λ_e(f) ∏_{p|f} δ_p` (`tpa`), `m = r |j| e`. Then `a = c ⋆ b` with `c = a·1[· | m]` (finitely supported) and
`b = a·1[(·, m) = 1]`, and `b(v) = μ(v)/v²` on `(v, m) = 1`. So
`Σ_{f≤Q} a(f) = Σ_{u | m} c(u) Σ_{v ≤ Q/u} b(v)` (`divisor_sum_swap`), `Σ_v b(v) = (6/π²) ∏_{p|m}(1 − p⁻²)⁻¹`
(`hasProd_sqfree`, `hasProd_m2f`), `𝔈_{j,r}(e) = (Σ_v b(v)) Σ_{u|m} c(u)` (finite Euler product), and the error is
`Σ_{u|m} c(u)(Σ_{v≤Q/u} b(v) − Σ_v b(v))`, at most `Σ_{u|m} |c(u)| 2u/Q = (2/Q) ∏_{p|m}(1 + |a(p)| p)
≤ 2^{ω(e)+1} σ(r)/Q` (`tail_generic`).
-/
import ZetaShell.Lemma2.A2a_S3_Defs
import ZetaShell.Lemma2.A2a_S3d_InnerAux

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- the local factor `a(p) = (h_e(p) − 1) δ_p` (plain kind), with `J = |j|`. -/
def tpA (r J e p : ℕ) : ℝ := (hE FKind.plain e p - 1) *
  (if ¬ p ∣ r ∧ ¬ p ∣ J then 1 / (p : ℝ) else if p ∣ r ∧ p ∣ J then 1 else 0)

/-- `a(f) = λ_e(f) ∏_{p|f} δ_p`. -/
def tpa (r J e f : ℕ) : ℝ := if Squarefree f then ∏ p ∈ f.primeFactors, tpA r J e p else 0

theorem tpa_eq (r : ℕ) (j : ℤ) (e f : ℕ) :
    lam FKind.plain e f * deltaProd r j f = tpa r j.natAbs e f := by
  have hdr : ∀ p : ℕ, ((p : ℤ) ∣ (r : ℤ) ↔ p ∣ r) := fun p => Int.natCast_dvd_natCast
  have hdj : ∀ p : ℕ, ((p : ℤ) ∣ j ↔ p ∣ j.natAbs) := fun p => Int.natCast_dvd
  unfold lam deltaProd tpa tpA
  split_ifs with hsq
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    simp only [hdr, hdj]
  · simp

theorem tpa_zero (r J e : ℕ) : tpa r J e 0 = 0 := by
  unfold tpa; simp

theorem tpa_one (r J e : ℕ) : tpa r J e 1 = 1 := by
  unfold tpa; simp

theorem tpa_mul (r J e : ℕ) {u v : ℕ} (h : Nat.Coprime u v) :
    tpa r J e (u * v) = tpa r J e u * tpa r J e v := by
  unfold tpa
  by_cases hu : Squarefree u
  · by_cases hv : Squarefree v
    · rw [if_pos (Nat.squarefree_mul_iff.mpr ⟨h, hu, hv⟩), if_pos hu, if_pos hv,
        Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]
    · rw [if_neg (fun hs => hv (Nat.squarefree_mul_iff.mp hs).2.2), if_neg hv, mul_zero]
  · rw [if_neg (fun hs => hu (Nat.squarefree_mul_iff.mp hs).2.1), if_neg hu, zero_mul]

theorem tpa_prime_pow (r J e p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) : tpa r J e (p ^ k) = 0 := by
  unfold tpa
  rw [if_neg]
  intro hs
  have := (Nat.squarefree_pow_iff hp.ne_one (by omega)).mp hs
  omega

/-- the local factor at a prime not dividing `m = r J e`. -/
theorem tpA_of_not_dvd (r J e p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ r * J * e) :
    tpA r J e p = -(1 / (p : ℝ) ^ 2) := by
  have hpe : ¬ p ∣ e := fun h => hpm (Dvd.dvd.mul_left h _)
  have hpr : ¬ p ∣ r := fun h => hpm (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
  have hpJ : ¬ p ∣ J := fun h => hpm (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold tpA hE
  simp only [hpe, hpr, hpJ, if_false, not_false_eq_true, and_self, if_true]
  field_simp
  ring

/-- on `f` coprime to `m`, `|a(f)| ≤ 1/f²`. -/
theorem abs_tpa_coprime_le (r J e f : ℕ) (hf : Nat.Coprime f (r * J * e)) :
    |tpa r J e f| ≤ 1 / (f : ℝ) ^ 2 := by
  unfold tpa
  split_ifs with hsq
  · have hval : ∏ p ∈ f.primeFactors, tpA r J e p = ∏ p ∈ f.primeFactors, (-(1 / (p : ℝ) ^ 2)) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
      apply tpA_of_not_dvd r J e p hpP
      intro hpm
      have := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hf
      exact hpP.ne_one (Nat.Coprime.eq_one_of_dvd this hpm)
    rw [hval, Finset.abs_prod]
    have h2 : ∏ p ∈ f.primeFactors, |(-(1 / (p : ℝ) ^ 2))| = 1 / (f : ℝ) ^ 2 := by
      conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
      push_cast
      rw [← Finset.prod_pow, one_div, ← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro p _
      rw [abs_neg, abs_of_nonneg (by positivity), one_div]
    rw [h2]
  · simp only [abs_zero]; positivity

/-- `c(u) = a(u)·1[u | m]`. -/
def tpc (r J e u : ℕ) : ℝ := if u ∣ r * J * e then tpa r J e u else 0

/-- `b(v) = a(v)·1[(v, m) = 1]`. -/
def tpb (r J e v : ℕ) : ℝ := if Nat.Coprime v (r * J * e) then tpa r J e v else 0

theorem tpa_conv (r J e f : ℕ) (hf : f ≠ 0) :
    tpa r J e f = ∑ u ∈ f.divisors, tpc r J e u * tpb r J e (f / u) := by
  by_cases hsq : Squarefree f
  · have hu0f : Nat.gcd f (r * J * e) ∣ f := Nat.gcd_dvd_left f _
    have hu0m : Nat.gcd f (r * J * e) ∣ r * J * e := Nat.gcd_dvd_right f _
    have hfuv : f = Nat.gcd f (r * J * e) * (f / Nat.gcd f (r * J * e)) := (Nat.mul_div_cancel' hu0f).symm
    have hcop : Nat.Coprime (f / Nat.gcd f (r * J * e)) (r * J * e) := by
      apply Nat.coprime_of_dvd
      intro p hp hpv hpm
      have hpf : p ∣ f := dvd_trans hpv (Dvd.intro_left _ hfuv.symm)
      have hpu : p ∣ Nat.gcd f (r * J * e) := Nat.dvd_gcd hpf hpm
      have hpp : p * p ∣ f := by rw [hfuv]; exact Nat.mul_dvd_mul hpu hpv
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp hpp
    have hcop2 : Nat.Coprime (Nat.gcd f (r * J * e)) (f / Nat.gcd f (r * J * e)) :=
      (Nat.Coprime.coprime_dvd_right hu0m hcop).symm
    rw [Finset.sum_eq_single (Nat.gcd f (r * J * e))]
    · unfold tpc tpb
      rw [if_pos hu0m, if_pos hcop, ← tpa_mul r J e hcop2, ← hfuv]
    · intro u hu hne
      have hud : u ∣ f := Nat.dvd_of_mem_divisors hu
      unfold tpc tpb
      by_cases h1 : u ∣ r * J * e
      · by_cases h2 : Nat.Coprime (f / u) (r * J * e)
        · exfalso
          apply hne
          have h3 : Nat.gcd f (r * J * e) = Nat.gcd u (r * J * e) := by
            conv_lhs => rw [← Nat.mul_div_cancel' hud]
            exact Nat.Coprime.gcd_mul_right_cancel u h2
          rw [h3, Nat.gcd_eq_left h1]
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro hnot
      exfalso; exact hnot (Nat.mem_divisors.mpr ⟨hu0f, hf⟩)
  · have h0 : tpa r J e f = 0 := by unfold tpa; rw [if_neg hsq]
    rw [h0]; symm
    apply Finset.sum_eq_zero
    intro u hu
    have hud : u ∣ f := Nat.dvd_of_mem_divisors hu
    unfold tpc tpb
    by_cases h1 : u ∣ r * J * e
    · by_cases h2 : Nat.Coprime (f / u) (r * J * e)
      · rw [if_pos h1, if_pos h2]
        by_cases hsu : Squarefree u
        · by_cases hsv : Squarefree (f / u)
          · exfalso; apply hsq
            rw [← Nat.mul_div_cancel' hud]
            exact Nat.squarefree_mul_iff.mpr ⟨(Nat.Coprime.coprime_dvd_right h1 h2).symm, hsu, hsv⟩
          · have h4 : tpa r J e (f / u) = 0 := by unfold tpa; rw [if_neg hsv]
            rw [h4, mul_zero]
        · have h4 : tpa r J e u = 0 := by unfold tpa; rw [if_neg hsu]
          rw [h4, zero_mul]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem tpa_sum_swap (r J e Q : ℕ) :
    ∑ f ∈ Finset.Icc 1 Q, tpa r J e f
      = ∑ u ∈ Finset.Icc 1 Q, tpc r J e u * ∑ v ∈ Finset.Icc 1 (Q / u), tpb r J e v := by
  rw [Finset.sum_congr rfl (fun f hf => tpa_conv r J e f (by have := (Finset.mem_Icc.mp hf).1; omega))]
  rw [MuSqPhi.divisor_sum_swap (fun u v => tpc r J e u * tpb r J e v) Q]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]

theorem tpb_zero (r J e : ℕ) : tpb r J e 0 = 0 := by
  unfold tpb; split_ifs <;> simp [tpa_zero]

theorem tpb_one (r J e : ℕ) : tpb r J e 1 = 1 := by
  unfold tpb; rw [if_pos (Nat.coprime_one_left _), tpa_one]

theorem tpb_mul (r J e : ℕ) {u v : ℕ} (h : Nat.Coprime u v) :
    tpb r J e (u * v) = tpb r J e u * tpb r J e v := by
  unfold tpb
  by_cases hu : Nat.Coprime u (r * J * e)
  · by_cases hv : Nat.Coprime v (r * J * e)
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hu, hv⟩), if_pos hu, if_pos hv, tpa_mul r J e h]
    · rw [if_neg (fun h' => hv (Nat.coprime_mul_iff_left.mp h').2), if_neg hv, mul_zero]
  · rw [if_neg (fun h' => hu (Nat.coprime_mul_iff_left.mp h').1), if_neg hu, zero_mul]

theorem tpb_prime_pow (r J e p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) : tpb r J e (p ^ k) = 0 := by
  unfold tpb; split_ifs
  · exact tpa_prime_pow r J e p k hp hk
  · rfl

theorem abs_tpb_le (r J e v : ℕ) : |tpb r J e v| ≤ 1 / (v : ℝ) ^ 2 := by
  unfold tpb
  split_ifs with h
  · exact abs_tpa_coprime_le r J e v h
  · simp only [abs_zero]; positivity

theorem tpb_hasSum (r J e : ℕ) : HasSum (tpb r J e) (∑' v, tpb r J e v) :=
  (Summable.of_norm (summable_of_inv_sq (abs_tpb_le r J e))).hasSum

/-- the Euler product: `(Σ_v b(v)) ∏_{p|m} (1 − p⁻²) = 6/π²`. -/
theorem tpb_tsum_mul (r J e : ℕ) (hm : r * J * e ≠ 0) :
    (∑' v, tpb r J e v) * ∏ p ∈ (r * J * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2) = 6 / Real.pi ^ 2 := by
  have h1 := hasProd_sqfree (tpb r J e) (tpb_zero r J e) (tpb_one r J e) (fun h => tpb_mul r J e h)
    (tpb_prime_pow r J e) (summable_of_inv_sq (abs_tpb_le r J e))
  set T' : ℕ → ℝ := fun n => if n ∣ r * J * e then 1 + m2f n else 1 with hT'
  have h2 : HasProd (fun p : Nat.Primes => T' p)
      (∏ p ∈ ((r * J * e).primeFactors.subtype Nat.Prime : Finset Nat.Primes), T' p) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    have hpn : ¬ (p : ℕ) ∣ r * J * e := by
      intro hd
      apply hp
      exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.2, hd, hm⟩)
    simp only [hT', if_neg hpn]
  have h3 := h1.mul h2
  have h4 : (fun p : Nat.Primes => (1 + tpb r J e p) * T' p) = fun p : Nat.Primes => 1 + m2f p := by
    funext p
    by_cases hpm : (p : ℕ) ∣ r * J * e
    · have hb : tpb r J e p = 0 := by
        unfold tpb
        rw [if_neg ((Nat.Prime.coprime_iff_not_dvd p.2).not.mpr (not_not.mpr hpm))]
      simp only [hT', if_pos hpm, hb]
      ring
    · have hb : tpb r J e p = m2f p := by
        unfold tpb
        rw [if_pos ((Nat.Prime.coprime_iff_not_dvd p.2).mpr hpm)]
        unfold tpa m2f
        rw [if_pos p.2.prime.squarefree, Nat.Prime.primeFactors p.2, Finset.prod_singleton,
          tpA_of_not_dvd r J e p p.2 hpm, ArithmeticFunction.moebius_apply_prime p.2]
        push_cast
        ring
      simp only [hT', if_neg hpm, hb]
      ring
  rw [h4] at h3
  have h5 := h3.unique hasProd_m2f
  rw [← h5]
  congr 1
  rw [Finset.prod_subtype_eq_prod_filter (f := T'), Finset.filter_true_of_mem
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  apply Finset.prod_congr rfl
  intro p hp
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  simp only [hT', if_pos (Nat.dvd_of_mem_primeFactors hp)]
  unfold m2f
  rw [ArithmeticFunction.moebius_apply_prime hpP]
  push_cast
  ring

theorem tpb_tsum_eq (r J e : ℕ) (hm : r * J * e ≠ 0) :
    ∑' v, tpb r J e v = 6 / Real.pi ^ 2 * ∏ p ∈ (r * J * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  have hP : ∏ p ∈ (r * J * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : 1 / (p : ℝ) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  rw [Finset.prod_inv_distrib, ← tpb_tsum_mul r J e hm]
  field_simp

theorem tpl_nf_toFinset (n : ℕ) :
    (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
  rw [Nat.factors_eq]
  rfl

/-- finite Euler product over the squarefree divisors. -/
theorem tpl_divisor_sum (g : ℕ → ℝ) (m : ℕ) (hm0 : m ≠ 0) :
    ∑ u ∈ m.divisors, (if Squarefree u then ∏ p ∈ u.primeFactors, g p else 0)
      = ∏ p ∈ m.primeFactors, (1 + g p) := by
  rw [← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hm0, tpl_nf_toFinset, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t ht
  have htP : t ⊆ m.primeFactors := Finset.mem_powerset.mp ht
  have htp : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (htP hp)
  have hval : t.val.prod = ∏ p ∈ t, p := by simp
  rw [hval, Nat.primeFactors_prod htp]

/-- the local identity `1 + a(p) = F₁(p) F₂(p)` for `p | m`. -/
theorem tpA_local (r J e p : ℕ) (hp : p.Prime) (hpm : p ∣ r * J * e) :
    1 + tpA r J e p = (if p ∣ e ∧ ¬ p ∣ r * J then 1 - 1 / (p : ℝ) else 1) *
      (if p ∣ r ∧ p ∣ J then hE FKind.plain e p else 1) := by
  have hrJ : p ∣ r * J ↔ p ∣ r ∨ p ∣ J := hp.dvd_mul
  have hm : p ∣ r * J * e ↔ (p ∣ r ∨ p ∣ J) ∨ p ∣ e := by rw [hp.dvd_mul, hrJ]
  rw [hm] at hpm
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold tpA hE
  simp only [hrJ]
  by_cases he : p ∣ e <;> by_cases hr : p ∣ r <;> by_cases hJ : p ∣ J <;>
    simp only [he, hr, hJ, if_true, if_false, true_and, and_true, true_or, or_true, not_true_eq_false,
      not_false_eq_true, and_false, false_and, or_false, false_or] <;> ring_nf
  simp [he, hr, hJ] at hpm

theorem tp_Ecoef (r J e : ℕ) (hm : r * J * e ≠ 0) :
    Ecoef FKind.plain r J e = (∑' v, tpb r J e v) * ∑ u ∈ (r * J * e).divisors, tpc r J e u := by
  have he0 : e ≠ 0 := by rintro rfl; simp at hm
  have hr0 : r ≠ 0 := by rintro rfl; simp at hm
  have hc : ∑ u ∈ (r * J * e).divisors, tpc r J e u
      = ∏ p ∈ (r * J * e).primeFactors, (1 + tpA r J e p) := by
    rw [← tpl_divisor_sum (tpA r J e) _ hm]
    apply Finset.sum_congr rfl
    intro u hu
    unfold tpc tpa
    rw [if_pos (Nat.dvd_of_mem_divisors hu)]
  have hF1 : ∏ p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * J), (1 - 1 / (p : ℝ))
      = ∏ p ∈ (r * J * e).primeFactors, (if p ∣ e ∧ ¬ p ∣ r * J then 1 - 1 / (p : ℝ) else 1) := by
    have h1 : ∏ p ∈ e.primeFactors, (if ¬ p ∣ r * J then 1 - 1 / (p : ℝ) else 1)
        = ∏ p ∈ e.primeFactors, (if p ∣ e ∧ ¬ p ∣ r * J then 1 - 1 / (p : ℝ) else 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpe := Nat.dvd_of_mem_primeFactors hp
      simp only [hpe, true_and]
    rw [Finset.prod_filter, h1]
    apply Finset.prod_subset (Nat.primeFactors_mono (Dvd.intro_left _ rfl) hm)
    intro p hpm hpe
    have : ¬ p ∣ e := fun h => hpe (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpm, h, he0⟩)
    simp only [this, false_and, if_false]
  have hF2 : ∏ p ∈ (Nat.gcd r J).primeFactors, hE FKind.plain e p
      = ∏ p ∈ (r * J * e).primeFactors, (if p ∣ r ∧ p ∣ J then hE FKind.plain e p else 1) := by
    have hg0 : Nat.gcd r J ≠ 0 := Nat.gcd_ne_zero_left hr0
    have h1 : ∏ p ∈ (Nat.gcd r J).primeFactors, hE FKind.plain e p
        = ∏ p ∈ (Nat.gcd r J).primeFactors, (if p ∣ r ∧ p ∣ J then hE FKind.plain e p else 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpg := Nat.dvd_of_mem_primeFactors hp
      rw [if_pos ⟨dvd_trans hpg (Nat.gcd_dvd_left _ _), dvd_trans hpg (Nat.gcd_dvd_right _ _)⟩]
    rw [h1]
    apply Finset.prod_subset (Nat.primeFactors_mono
      (dvd_trans (Nat.gcd_dvd_left r J) (dvd_mul_of_dvd_left (dvd_mul_right r J) e)) hm)
    intro p hpm hpg
    have : ¬ (p ∣ r ∧ p ∣ J) := fun h =>
      hpg (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpm, Nat.dvd_gcd h.1 h.2, hg0⟩)
    rw [if_neg this]
  simp only [Ecoef]
  rw [hF1, hF2, ← tpb_tsum_eq r J e hm, hc, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  exact (tpA_local r J e p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)).symm

theorem tpA_bound (r J e p : ℕ) (hp : p.Prime) (hpm : p ∣ r * J * e) :
    1 + |tpA r J e p| * p ≤ (if p ∣ e then 2 else 1) * (if p ∣ r then 1 + (p : ℝ) else 1) := by
  have hm : p ∣ r * J * e ↔ (p ∣ r ∨ p ∣ J) ∨ p ∣ e := by rw [hp.dvd_mul, hp.dvd_mul]
  rw [hm] at hpm
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  unfold tpA hE
  by_cases he : p ∣ e <;> by_cases hr : p ∣ r <;> by_cases hJ : p ∣ J <;>
    simp only [he, hr, hJ, if_true, if_false, true_and, and_true, not_true_eq_false,
      not_false_eq_true, and_false, false_and]
  · norm_num <;> linarith
  · norm_num <;> linarith
  · norm_num
  · rw [show ((0 : ℝ) - 1) * (1 / (p : ℝ)) = -(1 / p) by ring, abs_neg, abs_of_pos (by positivity)]
    field_simp
    norm_num
  · rw [show ((1 : ℝ) - 1 / p - 1) * 1 = -(1 / p) by ring, abs_neg, abs_of_pos (by positivity)]
    field_simp
    linarith
  · norm_num <;> linarith
  · norm_num
  · simp [he, hr, hJ] at hpm

theorem tp_prod_le_sigma (r : ℕ) (hr : r ≠ 0) :
    ∏ p ∈ r.primeFactors, (1 + (p : ℝ)) ≤ (ArithmeticFunction.sigma 1 r : ℝ) := by
  rw [← tpl_divisor_sum (fun p => (p : ℝ)) r hr, ArithmeticFunction.sigma_one_apply]
  push_cast
  apply Finset.sum_le_sum
  intro u _
  split_ifs with hsq
  · rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  · positivity

theorem tp_weighted_sum (r J e : ℕ) (hm : r * J * e ≠ 0) :
    ∑ u ∈ (r * J * e).divisors, |tpc r J e u| * u
      ≤ 2 ^ (ArithmeticFunction.cardDistinctFactors e) * (ArithmeticFunction.sigma 1 r : ℝ) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at hm
  have hr0 : r ≠ 0 := by rintro rfl; simp at hm
  have h1 : ∑ u ∈ (r * J * e).divisors, |tpc r J e u| * u
      = ∏ p ∈ (r * J * e).primeFactors, (1 + |tpA r J e p| * p) := by
    rw [← tpl_divisor_sum (fun p => |tpA r J e p| * p) _ hm]
    apply Finset.sum_congr rfl
    intro u hu
    unfold tpc tpa
    rw [if_pos (Nat.dvd_of_mem_divisors hu)]
    split_ifs with hsq
    · rw [Finset.abs_prod, Finset.prod_mul_distrib]
      congr 1
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
      push_cast
      rfl
    · simp
  rw [h1]
  calc ∏ p ∈ (r * J * e).primeFactors, (1 + |tpA r J e p| * p)
      ≤ ∏ p ∈ (r * J * e).primeFactors,
          ((if p ∣ e then (2 : ℝ) else 1) * (if p ∣ r then 1 + (p : ℝ) else 1)) := by
        apply Finset.prod_le_prod
        · intro p _; positivity
        · intro p hp
          exact tpA_bound r J e p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    _ = (∏ p ∈ (r * J * e).primeFactors, (if p ∣ e then (2 : ℝ) else 1)) *
          ∏ p ∈ (r * J * e).primeFactors, (if p ∣ r then 1 + (p : ℝ) else 1) := Finset.prod_mul_distrib
    _ = 2 ^ (ArithmeticFunction.cardDistinctFactors e) * ∏ p ∈ r.primeFactors, (1 + (p : ℝ)) := by
        congr 1
        · rw [← Finset.prod_filter, Finset.prod_const, omega_eq_card_primeFactors]
          congr 2
          ext p
          simp only [Finset.mem_filter, Nat.mem_primeFactors]
          constructor
          · rintro ⟨⟨hp, _, _⟩, hpe⟩; exact ⟨hp, hpe, he0⟩
          · rintro ⟨hp, hpe, _⟩; exact ⟨⟨hp, dvd_trans hpe (Dvd.intro_left _ rfl), hm⟩, hpe⟩
        · rw [← Finset.prod_filter]
          congr 1
          ext p
          simp only [Finset.mem_filter, Nat.mem_primeFactors]
          constructor
          · rintro ⟨⟨hp, _, _⟩, hpr⟩; exact ⟨hp, hpr, hr0⟩
          · rintro ⟨hp, hpr, _⟩
            exact ⟨⟨hp, dvd_trans hpr (dvd_mul_of_dvd_left (dvd_mul_right r J) e), hm⟩, hpr⟩
    _ ≤ 2 ^ (ArithmeticFunction.cardDistinctFactors e) * (ArithmeticFunction.sigma 1 r : ℝ) :=
        mul_le_mul_of_nonneg_left (tp_prod_le_sigma r hr0) (by positivity)

/-- the partial sums of `b` against its sum. -/
theorem tpb_partial (r J e N u Q : ℕ) (hu : 1 ≤ u) (hQ : 1 ≤ Q) (hN : N = Q / u) :
    |∑ v ∈ Finset.Icc 1 N, tpb r J e v - ∑' v, tpb r J e v| ≤ 2 * u / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have htail : ∀ M : ℕ, 1 ≤ M →
      |∑ v ∈ Finset.Icc 1 M, tpb r J e v - ∑' v, tpb r J e v| ≤ 1 / M := by
    intro M hM
    exact tail_generic (tpb r J e) _ 1 (tpb_hasSum r J e) (abs_tpb_le r J e) M hM
  by_cases huQ : u ≤ Q
  · have hN1 : 1 ≤ N := by rw [hN]; exact (Nat.one_le_div_iff (by omega)).mpr huQ
    refine le_trans (htail N hN1) ?_
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [div_le_div_iff₀ hN' hQ']
    have h1 : Q < u * (Q / u + 1) := Nat.lt_mul_div_succ Q (by omega)
    rw [← hN] at h1
    have h2 : Q ≤ 2 * N * u := by nlinarith
    have h3 : (Q : ℝ) ≤ 2 * N * u := by exact_mod_cast h2
    linarith
  · have hN0 : N = 0 := by rw [hN]; exact Nat.div_eq_of_lt (by omega)
    have h1 := htail 1 le_rfl
    simp only [Finset.Icc_self, Finset.sum_singleton, tpb_one, Nat.cast_one, div_one] at h1
    rw [hN0]
    simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty, zero_sub, abs_neg]
    have hB : |∑' v, tpb r J e v| ≤ 2 := by
      have := abs_sub_abs_le_abs_sub (∑' v, tpb r J e v) 1
      rw [abs_sub_comm] at h1
      rw [abs_one] at this
      linarith
    refine le_trans hB ?_
    rw [le_div_iff₀ hQ']
    have : (Q : ℝ) < u := by exact_mod_cast (show Q < u by omega)
    linarith

/-- **`s3_tail_plain_pt`** (statement of the node in `A2a_S3e_TailParts`). -/
theorem s3_tail_plain_pt_proof (Q r : ℕ) (j : ℤ) (e : ℕ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (hj : j ≠ 0)
    (he : 1 ≤ e) :
    |∑ f ∈ Finset.Icc 1 Q, lam FKind.plain e f * deltaProd r j f - Ecoef FKind.plain r j.natAbs e|
      ≤ 2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * (ArithmeticFunction.sigma 1 r : ℝ) / Q := by
  have hJ : 1 ≤ j.natAbs := Int.natAbs_pos.mpr hj
  have hm : r * j.natAbs * e ≠ 0 := by positivity
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  simp only [tpa_eq r j e]
  rw [tpa_sum_swap, tp_Ecoef _ _ _ hm]
  have hsw : ∑ u ∈ Finset.Icc 1 Q, tpc r j.natAbs e u * ∑ v ∈ Finset.Icc 1 (Q / u), tpb r j.natAbs e v
      = ∑ u ∈ (r * j.natAbs * e).divisors,
          tpc r j.natAbs e u * ∑ v ∈ Finset.Icc 1 (Q / u), tpb r j.natAbs e v := by
    rw [← Finset.sum_filter_of_ne (p := fun u => u ∣ r * j.natAbs * e) (s := Finset.Icc 1 Q)]
    · rw [← Finset.sum_filter_of_ne (p := fun u => u ≤ Q) (s := (r * j.natAbs * e).divisors)]
      · congr 1
        ext u
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨_, huQ⟩, hum⟩; exact ⟨⟨hum, hm⟩, huQ⟩
        · rintro ⟨⟨hum, _⟩, huQ⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hum (Nat.pos_of_ne_zero hm), huQ⟩, hum⟩
      · intro u _ hne
        by_contra huQ
        apply hne
        rw [Nat.div_eq_of_lt (not_le.mp huQ)]
        simp
    · intro u _ hne
      by_contra hum
      apply hne
      unfold tpc
      rw [if_neg hum, zero_mul]
  rw [hsw, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ u ∈ (r * j.natAbs * e).divisors, (tpc r j.natAbs e u *
          ∑ v ∈ Finset.Icc 1 (Q / u), tpb r j.natAbs e v - (∑' v, tpb r j.natAbs e v) * tpc r j.natAbs e u)|
      ≤ ∑ u ∈ (r * j.natAbs * e).divisors, |tpc r j.natAbs e u *
          ∑ v ∈ Finset.Icc 1 (Q / u), tpb r j.natAbs e v - (∑' v, tpb r j.natAbs e v) * tpc r j.natAbs e u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ (r * j.natAbs * e).divisors, |tpc r j.natAbs e u| * (2 * u / Q) := by
        apply Finset.sum_le_sum
        intro u hu
        have hu1 : 1 ≤ u := Nat.pos_of_mem_divisors hu
        rw [show tpc r j.natAbs e u * ∑ v ∈ Finset.Icc 1 (Q / u), tpb r j.natAbs e v
            - (∑' v, tpb r j.natAbs e v) * tpc r j.natAbs e u
            = tpc r j.natAbs e u * (∑ v ∈ Finset.Icc 1 (Q / u), tpb r j.natAbs e v
              - ∑' v, tpb r j.natAbs e v) by ring, abs_mul]
        exact mul_le_mul_of_nonneg_left (tpb_partial r j.natAbs e (Q / u) u Q hu1 hQ rfl) (abs_nonneg _)
    _ = (2 / Q) * ∑ u ∈ (r * j.natAbs * e).divisors, |tpc r j.natAbs e u| * u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
    _ ≤ (2 / Q) * (2 ^ (ArithmeticFunction.cardDistinctFactors e) * (ArithmeticFunction.sigma 1 r : ℝ)) :=
        mul_le_mul_of_nonneg_left (tp_weighted_sum r j.natAbs e hm) (by positivity)
    _ = 2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * (ArithmeticFunction.sigma 1 r : ℝ) / Q := by
        rw [pow_succ]
        ring

end TrackF
end ZetaShell
