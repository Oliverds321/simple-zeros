/-
A2a_S3_Count (L7_8, round 2 statement; round 3 derivation): **Steps 0–3 of the proof of Lemma 2(a)**
(sec_shell.tex l.306–341): the window sum equals the spike plus the main term, up to the count error.

For `a/r` reduced (`(a, r) = 1`, `1 ≤ r ≤ R₁`, `2R₁ ≤ Q`), `θ = a/r + η` with `|η| ≤ 1/(rR₁)`, `0 < δ < 1`:
`|δ D^Ω_δ(θ) − Ω(r)1[|η| ≤ δ/2] − mainSum| ≤ C·(J(1 + log J)(1 + log Q) + δ Q r (1 + log Q))`,
`J = Q/R₁ + R₁Qδ + 1` (the draft's `J`, l.311). Statement unchanged since round 2 (tested numerically,
`numerics/step35_test.py`, `Q = 200, 400`: worst ratio 0.0083).

Round 3: `step3_count` is DERIVED here from the sub-nodes
* `s3_reindex` (A2a_S3a_Reindex): window sum = spike + `Σ_j Σ_e c_e Σ_f λ_e(f) N_j(e,f)`;
* `s3_lineInt` (A2a_S3b_LineInt): `lineInt` = interval integral over `lineIv`;
* `s3_irrelevant` (A2a_S3c_Irrelevant): `e|j| > rQ(|η|+δ/2)` contributes `0`;
* `step2_line_count` (A2a_S2_LineCount): `|N_j(e,f) − main| ≤ 2V*2^{ω(|j|)}`;
* `s3_arith` (A2a_S3d_Arith): the `j, e, f` sums with `2^ω` and logs;
* `s3_tail` (A2a_S3e_Tail): the tail `f > Q` of the main term (L7_8's bound).
-/
import ZetaShell.Lemma2.A2a_S3a_Reindex
import ZetaShell.Lemma2.A2a_S3b_LineInt
import ZetaShell.Lemma2.A2a_S3c_Irrelevant
import ZetaShell.Lemma2.A2a_S3d_Arith
import ZetaShell.Lemma2.A2a_S3e_Tail

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem Vstar_nonneg (F : Fam) : 0 ≤ Vstar F := by
  cases F <;> simp only [Vstar] <;> norm_num

/-- the per-`(j, e)` algebra: count minus main term splits into the Step 2 error and the tail. -/
theorem s3_split_je (F : Fam) (Q r : ℕ) (r' j : ℤ) (e : ℕ) (lo hi : ℝ) :
    cE F.kind e * ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * lineCount F Q r r' j e f lo hi
      - ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
          (cE F.kind e * Ecoef F.kind r j.natAbs e * (∫ q in lo..hi, F.w (q * e / Q)))
    = cE F.kind e * ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f *
          (lineCount F Q r r' j e f lo hi - mainJEF F Q r j e f lo hi)
      + cE F.kind e * (((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
          (∫ q in lo..hi, F.w (q * e / Q))) *
          (∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * deltaProd r j f - Ecoef F.kind r j.natAbs e) := by
  have h : ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * (lineCount F Q r r' j e f lo hi - mainJEF F Q r j e f lo hi)
      = ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * lineCount F Q r r' j e f lo hi
        - ((1 / (r : ℝ)) * (∫ q in lo..hi, F.w (q * e / Q)) * ((Nat.totient j.natAbs : ℝ) / j.natAbs)) *
          ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * deltaProd r j f := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f _
    simp only [mainJEF, Int.cast_natCast]
    ring
  rw [h]
  ring

theorem step3_count (F : Fam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q r : ℕ) (a : ℤ) (R1 η δ : ℝ), 2 ≤ Q → 1 ≤ r → (r : ℝ) ≤ R1 → 2 * R1 ≤ Q →
      Int.gcd a r = 1 → |η| ≤ 1 / (r * R1) → 0 < δ → δ < 1 →
      |δ * Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) δ ((a : ℝ) / r + η) - spike F Q r η δ
          - mainSum F Q r η δ|
        ≤ C * ((Q / R1 + R1 * Q * δ + 1) * (1 + Real.log (Q / R1 + R1 * Q * δ + 1)) * (1 + Real.log Q)
          + δ * Q * r * (1 + Real.log Q)) := by
  obtain ⟨C4, hC4, h4⟩ := s3_arith
  obtain ⟨C5, hC5, h5⟩ := s3_tail F
  have hV := Vstar_nonneg F
  refine ⟨2 * Vstar F * C4 + C5, by positivity, ?_⟩
  intro Q r a R1 η δ hQ hr hrR hR1Q hgcd hη hδ hδ1
  -- Bezout
  obtain ⟨r', a', hdet⟩ : ∃ r' a' : ℤ, a * r' - a' * (r : ℤ) = 1 := by
    obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
    exact ⟨u, -v, by linear_combination huv⟩
  have hrr' : Int.gcd (r : ℤ) r' = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    exact ⟨-a', a, by linear_combination hdet⟩
  have hrpos : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hR1pos : 0 < R1 := by linarith
  have hQpos : (0 : ℝ) < Q := by
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hrQ : r ≤ Q := by
    have : (r : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  have hQ1 : 1 ≤ Q := by omega
  rw [s3_reindex F Q r a a' r' η δ hQ hr hrQ hdet hδ hδ1]
  set Ls := lineSet (lineM Q r η δ) with hLs
  set X : ℝ := (r : ℝ) * Q * (|η| + δ / 2) with hXdef
  have hX0 : 0 ≤ X := by positivity
  -- mainSum in interval-integral form
  have hmain : mainSum F Q r η δ = ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q,
      ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
        (cE F.kind e * Ecoef F.kind r j.natAbs e *
          (∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q))) := by
    simp only [mainSum, hLs, lineSet, lineM]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [s3_lineInt F Q r j e η δ hr hj0 hδ]
  rw [hmain]
  have hsplit : spike F Q r η δ + ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, cE F.kind e *
        ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f *
          lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2
      - spike F Q r η δ
      - ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
          (cE F.kind e * Ecoef F.kind r j.natAbs e *
            (∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)))
      = ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q,
          (cE F.kind e * ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f *
              (lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2
                - mainJEF F Q r j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2)
            + cE F.kind e * (((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
                (∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q))) *
              (∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * deltaProd r j f - Ecoef F.kind r j.natAbs e)) := by
    rw [add_sub_cancel_left, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    exact s3_split_je F Q r r' j e _ _
  rw [hsplit]
  -- bound the two parts
  set U : ℤ → ℕ → ℝ := fun j e => |cE F.kind e| * ∑ f ∈ Finset.Icc 1 Q, |lam F.kind e f| *
      |lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2
        - mainJEF F Q r j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2| with hU
  set V : ℤ → ℕ → ℝ := fun j e => ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
      (|cE F.kind e| * |∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q)| *
        |∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * deltaProd r j f - Ecoef F.kind r j.natAbs e|) with hVdef
  have hterm : ∀ j ∈ Ls, ∀ e ∈ Finset.Icc 1 Q,
      |cE F.kind e * ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f *
              (lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2
                - mainJEF F Q r j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2)
            + cE F.kind e * (((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
                (∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q))) *
              (∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * deltaProd r j f - Ecoef F.kind r j.natAbs e)|
        ≤ U j e + V j e := by
    intro j _ e _
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [hU, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro f _; rw [abs_mul]
    · rw [hVdef]
      have hphi : 0 ≤ ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) := by positivity
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hphi]
      apply le_of_eq; ring
  have hsum1 : |∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q,
          (cE F.kind e * ∑ f ∈ Finset.Icc 1 Q, lam F.kind e f *
              (lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2
                - mainJEF F Q r j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2)
            + cE F.kind e * (((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
                (∫ q in (lineIv Q r j η δ).1..(lineIv Q r j η δ).2, F.w (q * e / Q))) *
              (∑ f ∈ Finset.Icc 1 Q, lam F.kind e f * deltaProd r j f - Ecoef F.kind r j.natAbs e))|
      ≤ ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, U j e + ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, V j e := by
    rw [← Finset.sum_add_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j hj => ?_))
    rw [← Finset.sum_add_distrib]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun e he => hterm j hj e he))
  -- the tail part
  have hV5 : ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, V j e ≤ C5 * (δ * Q * r * (1 + Real.log Q)) := by
    have := h5 Q r R1 η δ hQ hr hrR hR1Q hη hδ hδ1
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl; intro j _
    rw [hVdef, ← Finset.mul_sum]
  -- the Step 2 part
  have hU2 : ∀ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, U j e
      ≤ 2 * Vstar F * ((2 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) *
        ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X),
          |cE F.kind e| * ∑ f ∈ Finset.Icc 1 Q, |lam F.kind e f|) := by
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hfilt : ∑ e ∈ Finset.Icc 1 Q, U j e
        = ∑ e ∈ (Finset.Icc 1 Q).filter (fun e : ℕ => (e : ℝ) * |(j : ℝ)| ≤ X), U j e := by
      symm
      apply Finset.sum_filter_of_ne
      intro e he hne
      by_contra hcon
      apply hne
      have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      have hirr := s3_irrelevant F Q r r' j e 1 η δ hQ1 hr hj0 he1 hδ (by rw [hXdef] at hcon; linarith [not_le.mp hcon])
      rw [hU]
      simp only
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro f _
      have h1 := (s3_irrelevant F Q r r' j e f η δ hQ1 hr hj0 he1 hδ
        (by rw [hXdef] at hcon; linarith [not_le.mp hcon])).1
      have h2 := hirr.2
      rw [h1]
      simp only [mainJEF, h2, mul_zero, zero_mul, sub_zero, abs_zero]
    rw [hfilt, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
    rw [hU]
    simp only
    have hper : ∀ f ∈ Finset.Icc 1 Q, |lam F.kind e f| *
        |lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2
          - mainJEF F Q r j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2|
        ≤ |lam F.kind e f| * (2 * Vstar F * 2 ^ (ArithmeticFunction.cardDistinctFactors j.natAbs)) := by
      intro f _
      by_cases hsq : Squarefree f
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have h2 := step2_line_count F Q hQ1 r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2
          (by exact_mod_cast hr) hrr' hj0 he1 hsq (lineIv_le Q r j η δ)
        simp only [mainJEF]
        exact h2
      · have : lam F.kind e f = 0 := by simp [lam, hsq]
        rw [this]; simp
    have hsumf := Finset.sum_le_sum hper
    rw [← Finset.sum_mul] at hsumf
    calc |cE F.kind e| * ∑ f ∈ Finset.Icc 1 Q, |lam F.kind e f| *
          |lineCount F Q r r' j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2
            - mainJEF F Q r j e f (lineIv Q r j η δ).1 (lineIv Q r j η δ).2|
        ≤ |cE F.kind e| * ((∑ f ∈ Finset.Icc 1 Q, |lam F.kind e f|) *
            (2 * Vstar F * 2 ^ (ArithmeticFunction.cardDistinctFactors j.natAbs))) :=
          mul_le_mul_of_nonneg_left hsumf (abs_nonneg _)
      _ = 2 * Vstar F * (2 ^ (ArithmeticFunction.cardDistinctFactors j.natAbs) *
            (|cE F.kind e| * ∑ f ∈ Finset.Icc 1 Q, |lam F.kind e f|)) := by ring
  have hU4 : ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, U j e
      ≤ 2 * Vstar F * (C4 * ((X + 1) * (1 + Real.log (X + 1)) * (1 + Real.log Q))) := by
    refine le_trans (Finset.sum_le_sum hU2) ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := h4 F.kind Q X hQ hX0
    simpa [hLs, lineM, hXdef] using this
  -- X + 1 ≤ J
  set J := (Q : ℝ) / R1 + R1 * Q * δ + 1 with hJ
  have hXJ : X + 1 ≤ J := by
    have h1 : (r : ℝ) * Q * |η| ≤ Q / R1 := by
      have := mul_le_mul_of_nonneg_left hη (by positivity : (0 : ℝ) ≤ (r : ℝ) * Q)
      calc (r : ℝ) * Q * |η| ≤ (r : ℝ) * Q * (1 / (r * R1)) := this
        _ = Q / R1 := by field_simp
    have h2 : (r : ℝ) * Q * (δ / 2) ≤ R1 * Q * δ := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrR hQpos.le) hδ.le
      have h0 : 0 ≤ (r : ℝ) * Q * δ := by positivity
      have e : (r : ℝ) * Q * (δ / 2) = (1 / 2) * ((r : ℝ) * Q * δ) := by ring
      rw [e]; linarith
    rw [hXdef, hJ]
    have e : (r : ℝ) * Q * (|η| + δ / 2) = (r : ℝ) * Q * |η| + (r : ℝ) * Q * (δ / 2) := by ring
    rw [e]; linarith
  have hlog : (X + 1) * (1 + Real.log (X + 1)) ≤ J * (1 + Real.log J) := by
    have hX1 : (0 : ℝ) < X + 1 := by linarith
    have hl := Real.log_le_log hX1 hXJ
    have hl0 : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
    exact mul_le_mul hXJ (by linarith) (by linarith) (by linarith)
  have hlQ : 0 ≤ 1 + Real.log Q := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Q by linarith); linarith
  have hfinal1 : (X + 1) * (1 + Real.log (X + 1)) * (1 + Real.log Q) ≤ J * (1 + Real.log J) * (1 + Real.log Q) :=
    mul_le_mul_of_nonneg_right hlog hlQ
  have hJpos : 0 ≤ J * (1 + Real.log J) * (1 + Real.log Q) := by
    have hJ1 : 1 ≤ J := by
      have : 0 ≤ (Q : ℝ) / R1 := by positivity
      have : 0 ≤ R1 * Q * δ := by positivity
      rw [hJ]; linarith
    have := Real.log_nonneg hJ1
    positivity
  have hT : 0 ≤ δ * Q * r * (1 + Real.log Q) := by positivity
  calc _ ≤ ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, U j e + ∑ j ∈ Ls, ∑ e ∈ Finset.Icc 1 Q, V j e := hsum1
    _ ≤ 2 * Vstar F * (C4 * (J * (1 + Real.log J) * (1 + Real.log Q))) + C5 * (δ * Q * r * (1 + Real.log Q)) := by
        have := mul_le_mul_of_nonneg_left hfinal1 hC4
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * Vstar F)
        linarith
    _ ≤ (2 * Vstar F * C4 + C5) * (J * (1 + Real.log J) * (1 + Real.log Q) + δ * Q * r * (1 + Real.log Q)) := by
        have a1 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hV) hC4) hT
        have a2 := mul_nonneg hC5 hJpos
        nlinarith

end TrackF
end ZetaShell
