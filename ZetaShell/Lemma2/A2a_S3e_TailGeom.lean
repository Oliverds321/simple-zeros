/-
A2a_S3e_TailGeom (L7_8, round 5 draft; finished by L7_8c, cloud, 3 Oct 2026): `s3_tail_sum` reduced to one
geometric node, and that node proved.

* `s3_tail_geom`: `Σ_{0<|j|≤M} |∫_{I_j} w(qe/Q) dq| ≤ 6 r δ (Q/e)²` for `1 ≤ e ≤ Q`
  (`w(qe/Q) = 0` for `q > X = Q/e` and `|w| ≤ 1`, so each line contributes at most `X`; lines meeting `[1, X]` have
  `|j| ≤ J = X r (|η| + δ/2)` (`s3_irrelevant`); when `|η| ≤ δ` there are `2⌊J⌋ ≤ 3 X r δ` of them; when `|η| > δ`,
  `|I_j| ≤ (|j|/r) δ / (η² − δ²/4)`, and `2 J² δ / (r (η² − δ²/4)) ≤ 6 X² r δ`).
* `sigma_one_le_log`: `σ(r) ≤ r (1 + log r)`.
* `s3_tail_sum_of_geom`: `|c_e| 2^{ω(e)+1} σ(r)/Q ≤ 2σ(r)/Q`, `φ(|j|)/|j| ≤ 1`, swap the sums, `Σ_{e≤Q} e⁻² ≤ 2`:
  the sum is `≤ 4 C σ(r) δ Q ≤ 4 C δ Q r (1 + log Q)`.
Imports: all Lemma2 modules below `A2a_S3e_TailParts` (none of them imports it), so `A2a_S3e_TailParts` may import
this module.
-/
import ZetaShell.Lemma2.A2a_S3_Defs
import ZetaShell.Lemma2.A2a_S3c_Irrelevant
import ZetaShell.Lemma2.A2a_S3d_InnerAux
import ZetaShell.Lemma2.A2a_S4_Profile
import ZetaShell.Lemma2.L711_QphiSum

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem tg_abs_w_le_one (F : Fam) (x : ℝ) : |F.w x| ≤ 1 := by
  cases F
  · simp only [Fam.w]; split_ifs <;> norm_num
  · simp only [Fam.w]; split_ifs <;> norm_num
  · simp only [Fam.w]
    split_ifs with h
    · rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [h.1, h.2]
    · norm_num

theorem tg_meas (F : Fam) (e Q : ℕ) : Measurable (fun q : ℝ => F.w (q * e / Q)) :=
  F.measurable_w.comp ((measurable_id.mul_const _).div_const _)

theorem tg_int_le_len (F : Fam) (e Q : ℕ) (a b : ℝ) (hab : a ≤ b) :
    |∫ q in a..b, F.w (q * e / Q)| ≤ b - a := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := fun q : ℝ => F.w (q * e / Q)) (fun x _ => by rw [Real.norm_eq_abs]; exact tg_abs_w_le_one F _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a), one_mul] at h
  exact h

theorem tg_int_zero (F : Fam) (e Q : ℕ) (he : 1 ≤ e) (hQ : 1 ≤ Q) (a b : ℝ) (hab : a ≤ b)
    (ha : (Q : ℝ) / e ≤ a) : |∫ q in a..b, F.w (q * e / Q)| ≤ 0 := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 0)
    (f := fun q : ℝ => F.w (q * e / Q)) (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      have hx1 : (Q : ℝ) / e < x := lt_of_le_of_lt ha hx.1
      rw [div_lt_iff₀ he'] at hx1
      rw [F.w_eq_zero_of_gt_one, norm_zero]
      rw [lt_div_iff₀ hQ']
      linarith)
  rw [Real.norm_eq_abs, zero_mul] at h
  exact h

theorem tg_int_le_X (F : Fam) (e Q : ℕ) (he : 1 ≤ e) (hQ : 1 ≤ Q) (a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ a) :
    |∫ q in a..b, F.w (q * e / Q)| ≤ (Q : ℝ) / e := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hX0 : 0 < (Q : ℝ) / e := div_pos hQ' he'
  by_cases hbX : b ≤ (Q : ℝ) / e
  · exact le_trans (tg_int_le_len F e Q a b hab) (by linarith)
  · have hbX' : (Q : ℝ) / e < b := not_le.mp hbX
    by_cases haX : (Q : ℝ) / e ≤ a
    · exact le_trans (tg_int_zero F e Q he hQ a b hab haX) hX0.le
    · have haX' : a < (Q : ℝ) / e := not_le.mp haX
      have hii : ∀ c d : ℝ, IntervalIntegrable (fun q : ℝ => F.w (q * e / Q)) MeasureTheory.volume c d :=
        fun c d => intervalIntegrable_of_bdd (tg_meas F e Q) 1 (fun x => tg_abs_w_le_one F _) c d
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii a ((Q : ℝ) / e)) (hii ((Q : ℝ) / e) b)]
      have h1 := tg_int_le_len F e Q a ((Q : ℝ) / e) haX'.le
      have h2 := tg_int_zero F e Q he hQ ((Q : ℝ) / e) b hbX'.le le_rfl
      calc _ ≤ |∫ q in a..((Q : ℝ) / e), F.w (q * e / Q)| + |∫ q in ((Q : ℝ) / e)..b, F.w (q * e / Q)| :=
            abs_add_le _ _
        _ ≤ ((Q : ℝ) / e - a) + 0 := add_le_add h1 h2
        _ ≤ (Q : ℝ) / e := by linarith

theorem tg_card_lineSet (K : ℕ) : (lineSet K).card = 2 * K := by
  unfold lineSet
  rw [Finset.filter_ne', Finset.card_erase_of_mem (by simp), Int.card_Icc]
  omega

theorem tg_lineIv_fst_nonneg (Q r : ℕ) (j : ℤ) (η δ : ℝ) : 0 ≤ (lineIv Q r j η δ).1 := by
  unfold lineIv
  split_ifs <;> dsimp only <;> norm_num

/-- the length of a line's `q`-interval when `|η| > δ/2`. -/
theorem tg_lineIv_len (Q r : ℕ) (j : ℤ) (η δ : ℝ) (hr : 1 ≤ r) (hδ : 0 < δ) (hη : δ / 2 < |η|) :
    (lineIv Q r j η δ).2 - (lineIv Q r j η δ).1
      ≤ |(j : ℝ)| * δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hpos : 0 < |η| - δ / 2 := by linarith
  have hpos2 : 0 < |η| + δ / 2 := by linarith
  have hRHS : 0 ≤ |(j : ℝ)| * δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))) := by positivity
  have hid : |(j : ℝ)| / (r * (|η| - δ / 2)) - |(j : ℝ)| / (r * (|η| + δ / 2))
      = |(j : ℝ)| * δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))) := by
    rw [div_sub_div _ _ (ne_of_gt (mul_pos hr' hpos)) (ne_of_gt (mul_pos hr' hpos2)),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hη0 : η ≠ 0 := by
    intro h; rw [h, abs_zero] at hη; linarith
  unfold lineIv
  rcases lt_or_gt_of_ne hη0 with hneg | hpo
  · -- η < 0
    have habs : |η| = -η := abs_of_neg hneg
    have e1 : -(η - δ / 2) = |η| + δ / 2 := by rw [habs]; ring
    have e2 : -(η + δ / 2) = |η| - δ / 2 := by rw [habs]; ring
    have hc1 : η + δ / 2 < 0 := by linarith
    by_cases hj : 0 < j
    · rw [if_pos hj, if_neg (by intro h; linarith [h.1])]
      simpa using hRHS
    · rw [if_neg hj]
      simp only [if_pos hc1, e1, e2]
      split_ifs
      · dsimp only
        linarith [min_le_right (Q : ℝ) (|(j : ℝ)| / (r * (|η| - δ / 2))),
          le_max_right (1 : ℝ) (|(j : ℝ)| / (r * (|η| + δ / 2)))]
      · simpa using hRHS
  · -- η > 0
    have habs : |η| = η := abs_of_pos hpo
    have hc1 : 0 < η - δ / 2 := by linarith
    have hc2 : 0 < η + δ / 2 := by linarith
    by_cases hj : 0 < j
    · rw [if_pos hj]
      simp only [if_pos hc1]
      rw [habs] at hid ⊢
      split_ifs
      · dsimp only
        linarith [min_le_right (Q : ℝ) (|(j : ℝ)| / (r * (η - δ / 2))),
          le_max_right (1 : ℝ) (|(j : ℝ)| / (r * (η + δ / 2)))]
      · simpa [habs] using hRHS
    · rw [if_neg hj, if_neg (by intro h; linarith [h.1])]
      simpa using hRHS

theorem s3_tail_geom (F : Fam) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q r : ℕ) (η δ : ℝ) (e : ℕ), 1 ≤ Q → 1 ≤ r → 0 < δ →
    1 ≤ e → e ≤ Q →
    ∑ j ∈ lineSet (lineM Q r η δ), |∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)|
      ≤ C * ((r : ℝ) * δ * ((Q : ℝ) / e) ^ 2) := by
  refine ⟨6, by norm_num, ?_⟩
  intro Q r η δ e hQ hr hδ he heQ
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set X : ℝ := (Q : ℝ) / e with hXdef
  have hX0 : 0 < X := div_pos hQ' he'
  set t : ℤ → ℝ := fun j =>
    |∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)| with htdef
  set J : ℝ := X * r * (|η| + δ / 2) with hJdef
  have hJ0 : 0 ≤ J := by positivity
  set K : ℕ := ⌊J⌋₊ with hKdef
  have hKJ : (K : ℝ) ≤ J := Nat.floor_le hJ0
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ht0 : ∀ j, 0 ≤ t j := fun j => abs_nonneg _
  -- lines beyond `K` contribute nothing
  have hzero : ∀ j : ℤ, j ≠ 0 → K < j.natAbs → t j = 0 := by
    intro j hj hK
    have hJlt : J < |(j : ℝ)| := by
      have h1 : (K : ℝ) + 1 ≤ (j.natAbs : ℝ) := by exact_mod_cast hK
      have h2 : J < K + 1 := Nat.lt_floor_add_one J
      rw [Nat.cast_natAbs, Int.cast_abs] at h1
      linarith
    have hX : (r : ℝ) * Q * (|η| + δ / 2) < (e : ℝ) * |(j : ℝ)| := by
      have h3 : (r : ℝ) * Q * (|η| + δ / 2) = e * J := by
        rw [hJdef, hXdef]; field_simp
      rw [h3]
      exact mul_lt_mul_of_pos_left hJlt he'
    have h4 := (s3_irrelevant F Q r 0 j e 1 η δ hQ hr hj he hδ hX).2
    simp only [htdef, h4, abs_zero]
  have hstep1 : ∑ j ∈ lineSet (lineM Q r η δ), t j ≤ ∑ j ∈ lineSet K, t j := by
    rw [← Finset.sum_filter_of_ne (p := fun j : ℤ => j.natAbs ≤ K) (fun j hj hne => ?_)]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rw [Finset.mem_filter] at hj
        have hj1 := hj.1
        unfold lineSet at hj1 ⊢
        rw [Finset.mem_filter, Finset.mem_Icc] at hj1 ⊢
        exact ⟨⟨by omega, by omega⟩, hj1.2⟩
      · intro j _ _; exact ht0 j
    · by_contra hle
      have hj0 : j ≠ 0 := by unfold lineSet at hj; exact (Finset.mem_filter.mp hj).2
      exact hne (hzero j hj0 (not_le.mp hle))
  have hcard : ∑ j ∈ lineSet K, t j ≤ (2 * K : ℝ) * (if |η| ≤ δ then X
      else K * (δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))))) := by
    have hb : ∀ j ∈ lineSet K, t j ≤ (if |η| ≤ δ then X
        else K * (δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))))) := by
      intro j hj
      have hjK : j.natAbs ≤ K := by
        unfold lineSet at hj
        rw [Finset.mem_filter, Finset.mem_Icc] at hj
        omega
      split_ifs with hη
      · exact tg_int_le_X F e Q he hQ _ _ (lineIv_le Q r j η δ) (tg_lineIv_fst_nonneg Q r j η δ)
      · have hη' : δ < |η| := not_le.mp hη
        have hl := tg_lineIv_len Q r j η δ hr hδ (by linarith)
        have h1 := tg_int_le_len F e Q _ _ (lineIv_le Q r j η δ)
        have hjK' : |(j : ℝ)| ≤ K := by
          have : (j.natAbs : ℝ) ≤ K := by exact_mod_cast hjK
          rwa [Nat.cast_natAbs, Int.cast_abs] at this
        have hpos : 0 < |η| - δ / 2 := by linarith
        have hc0 : 0 ≤ δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))) := by positivity
        calc t j ≤ (lineIv Q r j η δ).2 - (lineIv Q r j η δ).1 := h1
          _ ≤ |(j : ℝ)| * δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))) := hl
          _ = |(j : ℝ)| * (δ / (r * ((|η| - δ / 2) * (|η| + δ / 2)))) := by ring
          _ ≤ K * (δ / (r * ((|η| - δ / 2) * (|η| + δ / 2)))) := mul_le_mul_of_nonneg_right hjK' hc0
    calc ∑ j ∈ lineSet K, t j ≤ ∑ j ∈ lineSet K, (if |η| ≤ δ then X
          else K * (δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))))) := Finset.sum_le_sum hb
      _ = (2 * K : ℝ) * (if |η| ≤ δ then X
          else K * (δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))))) := by
        rw [Finset.sum_const, tg_card_lineSet, nsmul_eq_mul]
        push_cast
        ring
  refine le_trans hstep1 (le_trans hcard ?_)
  split_ifs with hη
  · -- `|η| ≤ δ`: `2 K X ≤ 2 J X ≤ 3 r δ X²`
    have h1 : (2 * K : ℝ) * X ≤ 2 * J * X := by
      have := mul_le_mul_of_nonneg_right hKJ hX0.le
      linarith
    have h2 : 2 * J * X ≤ 6 * (r * δ * X ^ 2) := by
      rw [hJdef]
      have h3 : |η| + δ / 2 ≤ 3 * δ := by linarith
      have h4 : 0 ≤ X * r := by positivity
      have h5 := mul_le_mul_of_nonneg_left h3 h4
      nlinarith [h5, hX0]
    linarith
  · -- `|η| > δ`: `2 K² c ≤ 2 J² c ≤ 6 r δ X²`
    have hη' : δ < |η| := not_le.mp hη
    have hpos : 0 < |η| - δ / 2 := by linarith
    have hpos2 : 0 < |η| + δ / 2 := by linarith
    set c : ℝ := δ / (r * ((|η| - δ / 2) * (|η| + δ / 2))) with hcdef
    have hc0 : 0 ≤ c := by positivity
    have hKK : (K : ℝ) * K ≤ J * J := mul_self_le_mul_self hK0 hKJ
    have h1 : (2 * K : ℝ) * (K * c) ≤ 2 * (J * J) * c := by
      have := mul_le_mul_of_nonneg_right hKK hc0
      nlinarith [this]
    have h2 : J * J * c = X ^ 2 * r * δ * ((|η| + δ / 2) / (|η| - δ / 2)) := by
      rw [hJdef, hcdef]
      field_simp
    have h3 : (|η| + δ / 2) / (|η| - δ / 2) ≤ 3 := by
      rw [div_le_iff₀ hpos]; linarith
    have h4 : 0 ≤ X ^ 2 * r * δ := by positivity
    have h5 := mul_le_mul_of_nonneg_left h3 h4
    nlinarith [h1, h2, h5]

theorem sigma_one_le_log (r : ℕ) : (ArithmeticFunction.sigma 1 r : ℝ) ≤ r * (1 + Real.log r) := by
  have h1 : (ArithmeticFunction.sigma 1 r : ℝ) = ∑ d ∈ r.divisors, (r : ℝ) / d := by
    rw [ArithmeticFunction.sigma_one_apply]
    push_cast
    rw [← Nat.sum_div_divisors r (fun d => (d : ℝ))]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by positivity)]
  rw [h1]
  calc ∑ d ∈ r.divisors, (r : ℝ) / d ≤ ∑ d ∈ Finset.Icc 1 r, (r : ℝ) / d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_Icc]
          exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
        · intro d _ _
          positivity
    _ = r * ∑ d ∈ Finset.Icc 1 r, (1 : ℝ) / d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
    _ ≤ r * (1 + Real.log r) :=
        mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log r) (by positivity)

theorem cE_plain_T_le (e r Q : ℕ) (he : 1 ≤ e) :
    |cE FKind.plain e| * (2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) *
        (ArithmeticFunction.sigma 1 r : ℝ) / Q) ≤ 2 * (ArithmeticFunction.sigma 1 r : ℝ) / Q := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hmu : |((ArithmeticFunction.moebius e : ℤ) : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := e)
    exact_mod_cast this
  have hom : (2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors e) ≤ e :=
    le_trans (two_pow_omega_le_tau e (by omega)) (by exact_mod_cast Nat.card_divisors_le_self e)
  have hs : (0 : ℝ) ≤ (ArithmeticFunction.sigma 1 r : ℝ) := by positivity
  have hQ : (0 : ℝ) ≤ Q := by positivity
  simp only [cE]
  rw [abs_div, abs_of_pos he', pow_succ]
  calc |((ArithmeticFunction.moebius e : ℤ) : ℝ)| / e *
        (2 ^ (ArithmeticFunction.cardDistinctFactors e) * 2 * (ArithmeticFunction.sigma 1 r : ℝ) / Q)
      ≤ 1 / e * (e * 2 * (ArithmeticFunction.sigma 1 r : ℝ) / Q) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hmu he'.le
        · apply div_le_div_of_nonneg_right _ hQ
          apply mul_le_mul_of_nonneg_right _ hs
          linarith
        · positivity
        · positivity
    _ = 2 * (ArithmeticFunction.sigma 1 r : ℝ) / Q := by
        field_simp

theorem s3_tail_sum_of_geom (F : Fam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q r : ℕ) (R1 η δ : ℝ), 2 ≤ Q → 1 ≤ r → (r : ℝ) ≤ R1 →
    2 * R1 ≤ Q → |η| ≤ 1 / (r * R1) → 0 < δ → δ < 1 →
    ∑ j ∈ lineSet (lineM Q r η δ), ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
      ∑ e ∈ Finset.Icc 1 Q, |cE FKind.plain e| *
        |∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)| *
        (2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * (ArithmeticFunction.sigma 1 r : ℝ) / Q)
      ≤ C * (δ * Q * r * (1 + Real.log Q)) := by
  obtain ⟨C, hC, hG⟩ := s3_tail_geom F
  refine ⟨4 * C, by positivity, ?_⟩
  intro Q r R1 η δ hQ hr hrR hRQ _ hδ _
  set S : ℝ := (ArithmeticFunction.sigma 1 r : ℝ) with hSdef
  set I : ℤ → ℕ → ℝ := fun j e =>
    |∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)| with hIdef
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrQ : (r : ℝ) ≤ Q := by linarith
  have hS0 : 0 ≤ S := by positivity
  have hSle : S ≤ r * (1 + Real.log Q) := by
    refine le_trans (sigma_one_le_log r) (mul_le_mul_of_nonneg_left ?_ hrpos.le)
    have := Real.log_le_log hrpos hrQ
    linarith
  have hI0 : ∀ j e, 0 ≤ I j e := fun j e => abs_nonneg _
  have hterm : ∀ j ∈ lineSet (lineM Q r η δ),
      ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
        ∑ e ∈ Finset.Icc 1 Q, |cE FKind.plain e| * I j e *
          (2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * S / Q)
      ≤ (2 * S / (r * Q)) * ∑ e ∈ Finset.Icc 1 Q, I j e := by
    intro j _
    have hphi : (Nat.totient j.natAbs : ℝ) / j.natAbs ≤ 1 := by
      rcases Nat.eq_zero_or_pos j.natAbs with h0 | hpos
      · rw [h0]; simp
      · rw [div_le_one (by exact_mod_cast hpos)]
        exact_mod_cast Nat.totient_le _
    have hphi0 : 0 ≤ (Nat.totient j.natAbs : ℝ) / j.natAbs := by positivity
    calc ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
          ∑ e ∈ Finset.Icc 1 Q, |cE FKind.plain e| * I j e *
            (2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * S / Q)
        ≤ 1 * (1 / (r : ℝ)) * ∑ e ∈ Finset.Icc 1 Q, (2 * S / Q) * I j e := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hphi (by positivity)
          · apply Finset.sum_le_sum
            intro e he
            have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
            have h := cE_plain_T_le e r Q he1
            rw [← hSdef] at h
            calc |cE FKind.plain e| * I j e * (2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * S / Q)
                = (|cE FKind.plain e| * (2 ^ (ArithmeticFunction.cardDistinctFactors e + 1) * S / Q)) *
                    I j e := by ring
              _ ≤ (2 * S / Q) * I j e := mul_le_mul_of_nonneg_right h (hI0 j e)
          · exact Finset.sum_nonneg (fun e _ => by
              have := hI0 j e
              positivity)
          · positivity
      _ = (2 * S / (r * Q)) * ∑ e ∈ Finset.Icc 1 Q, I j e := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          field_simp
  have hsumQ : ∑ e ∈ Finset.Icc 1 Q, (1 : ℝ) / (e : ℝ) ^ 2 ≤ 2 := inv_sq_partial_le_two Q
  calc _ ≤ ∑ j ∈ lineSet (lineM Q r η δ), (2 * S / (r * Q)) * ∑ e ∈ Finset.Icc 1 Q, I j e :=
        Finset.sum_le_sum hterm
    _ = (2 * S / (r * Q)) * ∑ e ∈ Finset.Icc 1 Q, ∑ j ∈ lineSet (lineM Q r η δ), I j e := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (2 * S / (r * Q)) * ∑ e ∈ Finset.Icc 1 Q, C * ((r : ℝ) * δ * ((Q : ℝ) / e) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro e he
        have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
        have heQ : e ≤ Q := (Finset.mem_Icc.mp he).2
        exact hG Q r η δ e (by omega) hr hδ he1 heQ
    _ = (2 * S / (r * Q)) * (C * r * δ * Q ^ 2) * ∑ e ∈ Finset.Icc 1 Q, (1 : ℝ) / (e : ℝ) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
        have he' : (0 : ℝ) < e := by exact_mod_cast he1
        field_simp
    _ ≤ (2 * S / (r * Q)) * (C * r * δ * Q ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hsumQ (by positivity)
    _ = 4 * C * S * δ * Q := by
        field_simp
        ring
    _ ≤ 4 * C * (r * (1 + Real.log Q)) * δ * Q := by
        have h4 : 0 ≤ 4 * C * δ * Q := by positivity
        have := mul_le_mul_of_nonneg_left hSle h4
        linarith
    _ = 4 * C * (δ * Q * r * (1 + Real.log Q)) := by ring

end TrackF
end ZetaShell
