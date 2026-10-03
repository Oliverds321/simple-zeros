/-
Node K3 (L7_3): Lemma K.3 (lem:K-Z), hole cores. Draft: "Let `ℓ_K ≤ s ≤ log 𝒳` and `Q ≥ Q₀`. Then `R₀ < Q/2`. Put
`Ξ := 𝔉_Q \ 𝔉_{R₀}`, `δ = Q⁻²`, and for `r ≤ R₀`, `(a,r) = 1`, `H_{a/r} := {θ : ‖θ − a/r‖ < 1/(rQ) − δ/2}`. Then
(a) `H_{a/r} ⊆ Z`; (b) the `H_{a/r}`, `r ≤ R₀`, are pairwise disjoint; (c) `H_{a/r} ⊇ {θ : ‖θ − a/r‖ ≤ Δ}`."
Lean form: pure Farey arithmetic with `R` (= `R₀`) a parameter, `1 ≤ R < Q/2` (the analytic part "`R₀ < Q/2` since
`λ < 2`" is not part of this node); (a) is stated pointwise as `‖b/q − θ‖ > δ/2` for every Farey point `b/q` of
`Ξ` (i.e. `D_δ(θ) = 0` for `w ≡ 1`); (c) with `Δ = 1/(2R₀Q)` (`= KT/(2N)`, since `1/(R₀Q) = KT/N`).
Remark (proof): (b) holds for all `r, r′ ≤ Q` — `1/(rQ) + 1/(r′Q) − 1/Q² ≤ 1/(rr′)` is `(Q − r)(Q − r′) ≥ 0`; the
draft's `r + r′ ≤ Q` is more than needed.
Numerics: `numerics/ktests.py` (exact rationals, `Q = 3..29`, four values of `R` each: 0 violations).
Dependencies: the integer-numerator argument of trunk `ZetaQ.farey_spaced` (re-run here at `1/(qq′)`).
Difficulty: M. PROVED.
-/
import ZetaShell.Defs.LK_Defs

noncomputable section

namespace ZetaShell
namespace LemmaK

theorem distZ_le (x : ℝ) (m : ℤ) : distZ x ≤ |x - m| := by
  unfold distZ
  have hx := Int.floor_add_fract x
  rcases le_or_gt m ⌊x⌋ with h | h
  · have hm : (m : ℝ) ≤ ⌊x⌋ := by exact_mod_cast h
    calc min (Int.fract x) (1 - Int.fract x) ≤ Int.fract x := min_le_left _ _
      _ ≤ x - m := by linarith
      _ ≤ |x - m| := le_abs_self _
  · have h' : ⌊x⌋ + 1 ≤ m := h
    have hm : ((⌊x⌋ : ℤ) : ℝ) + 1 ≤ m := by exact_mod_cast h'
    calc min (Int.fract x) (1 - Int.fract x) ≤ 1 - Int.fract x := min_le_right _ _
      _ ≤ m - x := by linarith
      _ ≤ |x - m| := by rw [abs_sub_comm]; exact le_abs_self _

theorem distZ_eq (x : ℝ) : ∃ m : ℤ, distZ x = |x - m| := by
  unfold distZ
  have hf := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hx := Int.floor_add_fract x
  by_cases h : Int.fract x ≤ 1 - Int.fract x
  · refine ⟨⌊x⌋, ?_⟩
    rw [min_eq_left h, abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨⌊x⌋ + 1, ?_⟩
    have h' : 1 - Int.fract x ≤ Int.fract x := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h']
    push_cast
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem distZ_add_le (x y : ℝ) : distZ (x + y) ≤ distZ x + distZ y := by
  obtain ⟨m, hm⟩ := distZ_eq x
  obtain ⟨n, hn⟩ := distZ_eq y
  have e : x + y - (((m + n : ℤ)) : ℝ) = (x - m) + (y - n) := by push_cast; ring
  calc distZ (x + y) ≤ |x + y - (((m + n : ℤ)) : ℝ)| := distZ_le _ _
    _ = |(x - m) + (y - n)| := by rw [e]
    _ ≤ |x - m| + |y - n| := abs_add_le _ _
    _ = distZ x + distZ y := by rw [hm, hn]

theorem distZ_neg (x : ℝ) : distZ (-x) = distZ x := by
  apply le_antisymm
  · obtain ⟨m, hm⟩ := distZ_eq x
    have e : -x - (((-m : ℤ)) : ℝ) = -(x - m) := by push_cast; ring
    calc distZ (-x) ≤ |-x - (((-m : ℤ)) : ℝ)| := distZ_le _ _
      _ = distZ x := by rw [e, abs_neg, hm]
  · obtain ⟨m, hm⟩ := distZ_eq (-x)
    have e : x - (((-m : ℤ)) : ℝ) = -(-x - m) := by push_cast; ring
    calc distZ x ≤ |x - (((-m : ℤ)) : ℝ)| := distZ_le _ _
      _ = distZ (-x) := by rw [e, abs_neg, hm]

theorem distZ_sub_comm (x y : ℝ) : distZ (x - y) = distZ (y - x) := by
  rw [← distZ_neg (y - x), neg_sub]

/-- the Farey gap `‖a/q − a′/q′‖ ≥ 1/(qq′)` for distinct reduced fractions (the numerator argument of
`ZetaQ.farey_spaced`, re-run at `1/(qq′)` in place of `Q⁻²`). -/
theorem farey_gap {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime a' q')
    (hne : (q, a % q) ≠ (q', a' % q')) :
    1 / ((q : ℝ) * q') ≤ distZ ((a : ℝ) / q - (a' : ℝ) / q') := by
  obtain ⟨m, hm⟩ := distZ_eq ((a : ℝ) / q - (a' : ℝ) / q')
  rw [hm]
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq'R : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'
  have hDne : (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - m * (q : ℤ) * (q' : ℤ) ≠ 0 := by
    intro h0
    apply hne
    have hdvd1 : q ∣ a * q' := by
      have h : ((q : ℕ) : ℤ) ∣ ((a * q' : ℕ) : ℤ) :=
        ⟨(a' : ℤ) + m * (q' : ℤ), by push_cast; linear_combination h0⟩
      exact_mod_cast h
    have hdvd2 : q' ∣ a' * q := by
      have h : ((q' : ℕ) : ℤ) ∣ ((a' * q : ℕ) : ℤ) :=
        ⟨(a : ℤ) - m * (q : ℤ), by push_cast; linear_combination -h0⟩
      exact_mod_cast h
    have e1 : q ∣ q' := hcop.symm.dvd_of_dvd_mul_left hdvd1
    have e2 : q' ∣ q := hcop'.symm.dvd_of_dvd_mul_left hdvd2
    have heq : q = q' := Nat.dvd_antisymm e1 e2
    subst heq
    have hq0 : ((q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have hz : (q : ℤ) * ((a : ℤ) - (a' : ℤ) - m * (q : ℤ)) = 0 := by linear_combination h0
    have h2 := (mul_eq_zero.mp hz).resolve_left hq0
    have hmod : Nat.ModEq q a a' :=
      Nat.modEq_iff_dvd.mpr ⟨-m, by linear_combination -h2⟩
    exact congrArg (fun z : ℕ => ((q : ℕ), z)) hmod
  set D : ℤ := (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - m * (q : ℤ) * (q' : ℤ) with hDdef
  have hz1 : (1 : ℤ) ≤ |D| := by
    have := abs_pos.mpr hDne
    linarith
  have hR1 : (1 : ℝ) ≤ |(D : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hz1
  have key : (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) - (m : ℝ)
      = (D : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    rw [hDdef]
    push_cast
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q : ℝ) * (q' : ℝ))]
  gcongr

/-- **K3 (Lemma K.3).** -/
theorem farey_hole_cores (Q : ℕ) (R : ℝ) (hR1 : 1 ≤ R) (hRQ : R < (Q : ℝ) / 2) :
    (∀ a r b q : ℕ, 0 < r → (r : ℝ) ≤ R → Nat.Coprime a r → 0 < q → q ≤ Q → R < (q : ℝ) →
        Nat.Coprime b q → ∀ θ : ℝ,
        distZ (θ - (a : ℝ) / r) < 1 / ((r : ℝ) * Q) - 1 / (2 * (Q : ℝ) ^ 2) →
        1 / (2 * (Q : ℝ) ^ 2) < distZ ((b : ℝ) / q - θ)) ∧
    (∀ a r a' r' : ℕ, 0 < r → (r : ℝ) ≤ R → Nat.Coprime a r → 0 < r' → (r' : ℝ) ≤ R →
        Nat.Coprime a' r' → (r, a % r) ≠ (r', a' % r') → ∀ θ : ℝ,
        distZ (θ - (a : ℝ) / r) < 1 / ((r : ℝ) * Q) - 1 / (2 * (Q : ℝ) ^ 2) →
        ¬ distZ (θ - (a' : ℝ) / r') < 1 / ((r' : ℝ) * Q) - 1 / (2 * (Q : ℝ) ^ 2)) ∧
    (∀ a r : ℕ, 0 < r → (r : ℝ) ≤ R → ∀ θ : ℝ,
        distZ (θ - (a : ℝ) / r) ≤ 1 / (2 * R * Q) →
        distZ (θ - (a : ℝ) / r) < 1 / ((r : ℝ) * Q) - 1 / (2 * (Q : ℝ) ^ 2)) := by
  have hQ : (2 : ℝ) < Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- (a)
    intro a r b q hr hrR hcop hq hqQ hRq hcopb θ hθ
    have hrR' : (0 : ℝ) < r := by exact_mod_cast hr
    have hqR' : (0 : ℝ) < q := by exact_mod_cast hq
    have hne : (q, b % q) ≠ (r, a % r) := by
      intro h
      have : q = r := congrArg Prod.fst h
      have : (q : ℝ) = r := by exact_mod_cast this
      linarith
    have hgap := farey_gap hq hr hcopb hcop hne
    have htri : distZ ((b : ℝ) / q - (a : ℝ) / r)
        ≤ distZ ((b : ℝ) / q - θ) + distZ (θ - (a : ℝ) / r) := by
      have e : (b : ℝ) / q - (a : ℝ) / r = ((b : ℝ) / q - θ) + (θ - (a : ℝ) / r) := by ring
      rw [e]; exact distZ_add_le _ _
    have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hle : 1 / ((r : ℝ) * Q) ≤ 1 / ((q : ℝ) * r) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith
  · -- (b)
    intro a r a' r' hr hrR hcop hr' hr'R hcop' hne θ h1 h2
    have hrR' : (0 : ℝ) < r := by exact_mod_cast hr
    have hr'R' : (0 : ℝ) < r' := by exact_mod_cast hr'
    have hgap := farey_gap hr hr' hcop hcop' hne
    have htri : distZ ((a : ℝ) / r - (a' : ℝ) / r')
        ≤ distZ (θ - (a : ℝ) / r) + distZ (θ - (a' : ℝ) / r') := by
      have e : (a : ℝ) / r - (a' : ℝ) / r' = ((a : ℝ) / r - θ) + (θ - (a' : ℝ) / r') := by ring
      rw [e]
      calc distZ (((a : ℝ) / r - θ) + (θ - (a' : ℝ) / r'))
          ≤ distZ ((a : ℝ) / r - θ) + distZ (θ - (a' : ℝ) / r') := distZ_add_le _ _
        _ = distZ (θ - (a : ℝ) / r) + distZ (θ - (a' : ℝ) / r') := by
          rw [distZ_sub_comm ((a : ℝ) / r) θ]
    have hkey : 1 / ((r : ℝ) * r') - (1 / ((r : ℝ) * Q) - 1 / (2 * (Q : ℝ) ^ 2)
        + (1 / ((r' : ℝ) * Q) - 1 / (2 * (Q : ℝ) ^ 2)))
        = ((Q : ℝ) - r) * ((Q : ℝ) - r') / ((r : ℝ) * r' * (Q : ℝ) ^ 2) := by
      field_simp; ring
    have hnn : 0 ≤ ((Q : ℝ) - r) * ((Q : ℝ) - r') / ((r : ℝ) * r' * (Q : ℝ) ^ 2) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg <;> linarith
    linarith
  · -- (c)
    intro a r hr hrR θ hθ
    have hrR' : (0 : ℝ) < r := by exact_mod_cast hr
    have hle : 1 / (R * Q) ≤ 1 / ((r : ℝ) * Q) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hkey : 1 / (R * Q) - 1 / (2 * R * Q) - 1 / (2 * (Q : ℝ) ^ 2)
        = ((Q : ℝ) - R) / (2 * R * (Q : ℝ) ^ 2) := by
      field_simp; ring
    have hpos : 0 < ((Q : ℝ) - R) / (2 * R * (Q : ℝ) ^ 2) := by
      apply div_pos (by linarith) (by positivity)
    linarith

end LemmaK
end ZetaShell
