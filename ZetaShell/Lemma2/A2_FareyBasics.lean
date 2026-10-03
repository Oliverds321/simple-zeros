/-
A2_FareyBasics (L7_8, 28 Sep 2026): elementary Farey facts on `ℝ/ℤ` used by Lemma 2 (b), (c) of
`rh72/tex/sec_shell.tex` (lem:shell-2, l.283–304).

Objects: `distZ`, `Ddens`, `fareyIdx`, `fareyPt` of L7_6's `TF_Defs` (copied verbatim into this folder, sha256
d8415488…e534, and imported), so that the consumer A3 (L7_6's `A3_SignedGallagher`) reads the same objects.

Contents
* `distZ_le`, `distZ_eq`, `distZ_add_le`, `distZ_neg`, `distZ_sub_comm`, `farey_gap`: copied from L7_3's
  `LK_K3_HoleCores.lean` (proved there for `LemmaK.distZ`), restated for `TrackF.distZ` (same body).
  **Integrator: unify with L7_3's copies when `TrackF.distZ` and `LemmaK.distZ` are merged.**
* `card_mul_le_of_sep`: a finite set of reals in `[lo, hi]`, pairwise `≥ g` apart, has `card · g ≤ hi − lo + g`.
* `fareyWin`, `fareyWin_card`: a closed window of length `δ` on `ℝ/ℤ` holds at most `δQ² + 1` points of `𝔉_Q`
  (the draft's "consecutive points of `𝔉_Q` are `≥ Q⁻²` apart, so a window of length `δ` holds at most `δQ² + 1`
  points", proof of Lemma 2(b), l.303).
All sorry-free.
-/
import ZetaShell.Defs.TF_Defs

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

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

/-- the Farey gap `‖a/q − a′/q′‖ ≥ 1/(qq′)` for distinct reduced fractions (L7_3's `farey_gap`, the numerator
argument of trunk `ZetaQ.farey_spaced`). -/
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

/-- membership in `fareyIdx Q`, unfolded. -/
theorem mem_fareyIdx {Q : ℕ} {x : (_ : ℕ) × ℕ} :
    x ∈ fareyIdx Q ↔ (1 ≤ x.1 ∧ x.1 ≤ Q) ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1 := by
  unfold fareyIdx
  rw [Finset.mem_sigma, Finset.mem_Icc, ZetaQ.mem_reducedResidues]

/-- two distinct Farey indices give points at `ℝ/ℤ`-distance `≥ 1/(d d′)`. -/
theorem farey_gap_idx {Q : ℕ} {x y : (_ : ℕ) × ℕ} (hx : x ∈ fareyIdx Q) (hy : y ∈ fareyIdx Q)
    (hxy : x ≠ y) : 1 / ((x.1 : ℝ) * y.1) ≤ distZ (fareyPt x - fareyPt y) := by
  rw [mem_fareyIdx] at hx hy
  have hne : (x.1, x.2 % x.1) ≠ (y.1, y.2 % y.1) := by
    rw [Nat.mod_eq_of_lt hx.2.1, Nat.mod_eq_of_lt hy.2.1]
    intro h
    apply hxy
    have h1 : x.1 = y.1 := congrArg Prod.fst h
    have h2 : x.2 = y.2 := congrArg Prod.snd h
    exact Sigma.ext h1 (heq_of_eq h2)
  exact farey_gap (by omega) (by omega) hx.2.2 hy.2.2 hne

/-- ... and at distance `≥ Q⁻²`. -/
theorem farey_gap_Q {Q : ℕ} {x y : (_ : ℕ) × ℕ} (hx : x ∈ fareyIdx Q) (hy : y ∈ fareyIdx Q)
    (hxy : x ≠ y) : 1 / (Q : ℝ) ^ 2 ≤ distZ (fareyPt x - fareyPt y) := by
  have h := farey_gap_idx hx hy hxy
  rw [mem_fareyIdx] at hx hy
  have h1 : (1 : ℝ) ≤ x.1 := by exact_mod_cast hx.1.1
  have h2 : (1 : ℝ) ≤ y.1 := by exact_mod_cast hy.1.1
  have h3 : (x.1 : ℝ) ≤ Q := by exact_mod_cast hx.1.2
  have h4 : (y.1 : ℝ) ≤ Q := by exact_mod_cast hy.1.2
  have hle : (x.1 : ℝ) * y.1 ≤ (Q : ℝ) ^ 2 := by nlinarith
  calc 1 / (Q : ℝ) ^ 2 ≤ 1 / ((x.1 : ℝ) * y.1) :=
        one_div_le_one_div_of_le (by positivity) hle
    _ ≤ _ := h

/-- **Packing bound.** A finite set of reals in `[lo, hi]` that is pairwise `≥ g` apart (`g ≥ 0`) satisfies
`card · g ≤ hi − lo + g`. -/
theorem card_mul_le_of_sep (g lo : ℝ) (hg : 0 ≤ g) (s : Finset ℝ) :
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → g ≤ |x - y|) →
    ∀ hi : ℝ, lo - g ≤ hi → (∀ x ∈ s, lo ≤ x ∧ x ≤ hi) → (s.card : ℝ) * g ≤ hi - lo + g := by
  induction s using Finset.induction_on_max with
  | empty =>
    intro _ hi hhi _
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith
  | insert a s ha ih =>
    intro hsep hi hhi hmem
    have hsep' : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → g ≤ |x - y| := fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have haI := hmem a (Finset.mem_insert_self a s)
    have hle : ∀ x ∈ s, lo ≤ x ∧ x ≤ a - g := by
      intro x hx
      have h1 := hmem x (Finset.mem_insert_of_mem hx)
      have hxa := ha x hx
      have h2 := hsep a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx) (ne_of_gt hxa)
      rw [abs_of_pos (by linarith)] at h2
      exact ⟨h1.1, by linarith⟩
    have hih := ih hsep' (a - g) (by linarith [haI.1]) hle
    have hcard : ((insert a s).card : ℝ) ≤ (s.card : ℝ) + 1 := by
      exact_mod_cast Finset.card_insert_le a s
    calc ((insert a s).card : ℝ) * g ≤ ((s.card : ℝ) + 1) * g := mul_le_mul_of_nonneg_right hcard hg
      _ = (s.card : ℝ) * g + g := by ring
      _ ≤ hi - lo + g := by linarith [haI.2]

/-- the Farey window `{x ∈ 𝔉_Q : ‖b/d − θ‖ ≤ δ/2}` (the support of the sum in `Ddens`). -/
def fareyWin (Q : ℕ) (θ δ : ℝ) : Finset ((_ : ℕ) × ℕ) :=
  (fareyIdx Q).filter (fun x => distZ (fareyPt x - θ) ≤ δ / 2)

/-- **Window count.** A closed window of length `δ ≥ 0` on `ℝ/ℤ` holds at most `δQ² + 1` points of `𝔉_Q`. -/
theorem fareyWin_card (Q : ℕ) (θ δ : ℝ) (hδ : 0 ≤ δ) :
    ((fareyWin Q θ δ).card : ℝ) ≤ δ * (Q : ℝ) ^ 2 + 1 := by
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    have : fareyWin 0 θ δ = ∅ := by
      unfold fareyWin fareyIdx
      simp
    rw [this]
    simp
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  -- representatives in `[θ − δ/2, θ + δ/2]`
  let m : ((_ : ℕ) × ℕ) → ℤ := fun x => Classical.choose (distZ_eq (fareyPt x - θ))
  have hm : ∀ x, distZ (fareyPt x - θ) = |fareyPt x - θ - (m x : ℝ)| :=
    fun x => Classical.choose_spec (distZ_eq (fareyPt x - θ))
  let rep : ((_ : ℕ) × ℕ) → ℝ := fun x => fareyPt x - (m x : ℝ)
  set s := fareyWin Q θ δ with hs
  have hmemS : ∀ x ∈ s, x ∈ fareyIdx Q ∧ distZ (fareyPt x - θ) ≤ δ / 2 := by
    intro x hx
    rw [hs, fareyWin, Finset.mem_filter] at hx
    exact hx
  have hsepR : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 / (Q : ℝ) ^ 2 ≤ |rep x - rep y| := by
    intro x hx y hy hxy
    have h1 := farey_gap_Q (hmemS x hx).1 (hmemS y hy).1 hxy
    have e : rep x - rep y = fareyPt x - fareyPt y - (((m x - m y : ℤ)) : ℝ) := by
      simp only [rep]; push_cast; ring
    rw [e]
    exact le_trans h1 (distZ_le _ _)
  have hinj : Set.InjOn rep s := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hsepR x hx y hy hne
    rw [hxy, sub_self, abs_zero] at h1
    have : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
    linarith
  have hcard : (s.image rep).card = s.card := Finset.card_image_of_injOn hinj
  have hsep2 : ∀ u ∈ s.image rep, ∀ v ∈ s.image rep, u ≠ v → 1 / (Q : ℝ) ^ 2 ≤ |u - v| := by
    intro u hu v hv huv
    rw [Finset.mem_image] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    have hxy : x ≠ y := fun h => huv (by rw [h])
    exact hsepR x hx y hy hxy
  have hin : ∀ u ∈ s.image rep, θ - δ / 2 ≤ u ∧ u ≤ θ + δ / 2 := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have h1 := (hmemS x hx).2
    rw [hm x] at h1
    have e : fareyPt x - θ - (m x : ℝ) = rep x - θ := by simp only [rep]; ring
    rw [e] at h1
    have := abs_le.mp h1
    constructor <;> linarith [this.1, this.2]
  have hg : (0 : ℝ) ≤ 1 / (Q : ℝ) ^ 2 := by positivity
  have key := card_mul_le_of_sep (1 / (Q : ℝ) ^ 2) (θ - δ / 2) hg (s.image rep) hsep2 (θ + δ / 2)
    (by have : (0:ℝ) ≤ δ := hδ; linarith) hin
  rw [hcard] at key
  have hQ2 : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  have e2 : θ + δ / 2 - (θ - δ / 2) + 1 / (Q : ℝ) ^ 2 = (δ * (Q : ℝ) ^ 2 + 1) * (1 / (Q : ℝ) ^ 2) := by
    field_simp
    ring
  rw [e2] at key
  exact le_of_mul_le_mul_right key (by positivity)

end TrackF
end ZetaShell
