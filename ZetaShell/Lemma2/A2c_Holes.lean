/-
Node A2(c) (L7_8, 28 Sep 2026): **Lemma 2(c), holes and the spike** (lem:shell-2 (c), sec_shell.tex l.294–295, proof
l.304).

Draft: "(c) (Holes.) For any weights `𝒲`, any `r ≤ Q` and `δ/2 < |β| < 1/(rQ) − δ/2`, `D^𝒲_δ(a/r + β) = 0`; on
`|β| ≤ δ/2`, `D^𝒲_δ = 𝒲(r)/δ` (the spike)." Proof: "If `b/q ≠ a/r` and `q ≤ Q` then `|b/q − a/r| ≥ 1/(qr) ≥ 1/(rQ)`."

Lean form: `a/r` is a point of `𝔉_Q` (index `⟨r, a⟩ ∈ fareyIdx Q`: `1 ≤ r ≤ Q`, `0 ≤ a < r`, `(a, r) = 1`; the draft's
"`a/r` reduced", l.184); `θ = a/r + β` read on `ℝ/ℤ`; any real weights `W`.
* `lemma2c_hole`: the hole statement exactly as drafted (no condition on `δ` beyond the displayed range, which forces
  `δ < 1/(rQ)` when non-empty).
* `lemma2c_spike`: the spike **needs the extra hypothesis `δ < 1/(rQ)`**, which the draft omits. Without it the
  statement is false: `Q = 2`, `a/r = 0/1`, `δ = 1/2 = 1/(rQ)`, `β = δ/2 = 1/4`: the window `[0, 1/2]` contains `0/1`
  and `1/2`, so `D = (𝒲(0/1) + 𝒲(1/2))/δ ≠ 𝒲(0/1)/δ` when `𝒲(1/2) ≠ 0` (for every `Q`: `a/r = 0/1`, `δ = 1/Q`,
  `β = δ/2`, the window `[0, 1/Q]` also contains `1/Q`; numerics `numerics/lemma2_test.py`). In the Shell zone
  `rQδ ≤ R₁Qε/N = (log Q)⁶`, so `δ ≥ 1/(rQ)` does occur for `r` near `R₁`; the spike formula is not used by the
  assembly (the spikes lie in `𝒳_δ`, charged at part (b)), so this is a wording fix only. `W(r)` of the draft is
  the weight of the point `a/r`, `W ⟨r, a⟩`.
Consumer: eq:shell-assembly region (iii) ("the holes of `r ≤ R₁`, minus `𝒳_δ`": `δ < |β| < 1/(rQ) − δ`, inside the
range of `lemma2c_hole`), and rem:shell-holes-K.
Status: PROVED (sorry-free).
-/
import ZetaShell.Lemma2.A2_FareyBasics

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- every Farey point other than `a/r` is at distance `≥ 1/(rQ) − |β|` from `a/r + β`. -/
theorem far_from_hole_centre {Q r a : ℕ} (hx0 : (⟨r, a⟩ : (_ : ℕ) × ℕ) ∈ fareyIdx Q)
    {x : (_ : ℕ) × ℕ} (hx : x ∈ fareyIdx Q) (hne : x ≠ ⟨r, a⟩) (β : ℝ) :
    1 / ((r : ℝ) * Q) - |β| ≤ distZ (fareyPt x - ((a : ℝ) / r + β)) := by
  have hgap := farey_gap_idx hx hx0 hne
  have hx' := (mem_fareyIdx.mp hx)
  have hx0' := (mem_fareyIdx.mp hx0)
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast hx0'.1.1
  have hd1 : (1 : ℝ) ≤ x.1 := by exact_mod_cast hx'.1.1
  have hdQ : (x.1 : ℝ) ≤ Q := by exact_mod_cast hx'.1.2
  have hle : 1 / ((r : ℝ) * Q) ≤ 1 / ((x.1 : ℝ) * r) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hpt : fareyPt (⟨r, a⟩ : (_ : ℕ) × ℕ) = (a : ℝ) / r := rfl
  rw [hpt] at hgap
  have htri : distZ (fareyPt x - (a : ℝ) / r)
      ≤ distZ (fareyPt x - ((a : ℝ) / r + β)) + distZ β := by
    have e : fareyPt x - (a : ℝ) / r = (fareyPt x - ((a : ℝ) / r + β)) + β := by ring
    rw [e]; exact distZ_add_le _ _
  have hb : distZ β ≤ |β| := by
    have := distZ_le β 0
    simpa using this
  linarith

/-- **A2(c), the hole.** For any real weights `W`, any `a/r ∈ 𝔉_Q` and `δ/2 < |β| < 1/(rQ) − δ/2`:
`D^W_δ(a/r + β) = 0`. -/
theorem lemma2c_hole (Q r a : ℕ) (hx0 : (⟨r, a⟩ : (_ : ℕ) × ℕ) ∈ fareyIdx Q)
    (W : (_ : ℕ) × ℕ → ℝ) (δ β : ℝ) (h1 : δ / 2 < |β|) (h2 : |β| < 1 / ((r : ℝ) * Q) - δ / 2) :
    Ddens (fareyIdx Q) fareyPt W δ ((a : ℝ) / r + β) = 0 := by
  unfold Ddens
  have hsum : ∑ x ∈ fareyIdx Q,
      (if distZ (fareyPt x - ((a : ℝ) / r + β)) ≤ δ / 2 then W x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg]
    intro hle
    by_cases hne : x = ⟨r, a⟩
    · subst hne
      have e : fareyPt (⟨r, a⟩ : (_ : ℕ) × ℕ) - ((a : ℝ) / r + β) = -β := by
        simp only [fareyPt]; ring
      rw [e, distZ_neg] at hle
      obtain ⟨m, hm⟩ := distZ_eq β
      rw [hm] at hle
      have hx0' := mem_fareyIdx.mp hx0
      have hr : (1 : ℝ) ≤ r := by exact_mod_cast hx0'.1.1
      have hQ : (1 : ℝ) ≤ Q := by
        have : r ≤ Q := hx0'.1.2
        exact_mod_cast (le_trans hx0'.1.1 this)
      have hrQ : 1 / ((r : ℝ) * Q) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      rcases eq_or_ne m 0 with hm0 | hm0
      · subst hm0
        simp only [Int.cast_zero, sub_zero] at hle
        linarith
      · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
        have htri : |(m : ℝ)| ≤ |β - m| + |β| := by
          have := abs_sub_abs_le_abs_sub (m : ℝ) β
          rw [abs_sub_comm (m : ℝ) β] at this
          linarith
        linarith
    · have h := far_from_hole_centre hx0 hx hne β
      linarith
  rw [hsum, mul_zero]

/-- **A2(c), the spike (corrected: needs `δ < 1/(rQ)`).** On `|β| ≤ δ/2`: `D^W_δ(a/r + β) = W(a/r)/δ`. -/
theorem lemma2c_spike (Q r a : ℕ) (hx0 : (⟨r, a⟩ : (_ : ℕ) × ℕ) ∈ fareyIdx Q)
    (W : (_ : ℕ) × ℕ → ℝ) (δ β : ℝ) (hδr : δ < 1 / ((r : ℝ) * Q)) (hβ : |β| ≤ δ / 2) :
    Ddens (fareyIdx Q) fareyPt W δ ((a : ℝ) / r + β) = δ⁻¹ * W ⟨r, a⟩ := by
  unfold Ddens
  congr 1
  rw [Finset.sum_eq_single_of_mem (⟨r, a⟩ : (_ : ℕ) × ℕ) hx0]
  · rw [if_pos]
    have e : fareyPt (⟨r, a⟩ : (_ : ℕ) × ℕ) - ((a : ℝ) / r + β) = -β := by
      simp only [fareyPt]; ring
    rw [e, distZ_neg]
    have := distZ_le β 0
    simp only [Int.cast_zero, sub_zero] at this
    linarith
  · intro x hx hne
    rw [if_neg]
    intro hle
    have h := far_from_hole_centre hx0 hx hne β
    linarith

/-- **A2(c) (lem:shell-2 (c)), corrected form**: the hole and the spike together. -/
theorem lemma2c (Q r a : ℕ) (hx0 : (⟨r, a⟩ : (_ : ℕ) × ℕ) ∈ fareyIdx Q) (W : (_ : ℕ) × ℕ → ℝ) (δ : ℝ) :
    (∀ β : ℝ, δ / 2 < |β| → |β| < 1 / ((r : ℝ) * Q) - δ / 2 →
        Ddens (fareyIdx Q) fareyPt W δ ((a : ℝ) / r + β) = 0) ∧
    (δ < 1 / ((r : ℝ) * Q) → ∀ β : ℝ, |β| ≤ δ / 2 →
        Ddens (fareyIdx Q) fareyPt W δ ((a : ℝ) / r + β) = δ⁻¹ * W ⟨r, a⟩) :=
  ⟨fun β h1 h2 => lemma2c_hole Q r a hx0 W δ β h1 h2,
   fun hδr β hβ => lemma2c_spike Q r a hx0 W δ β hδr hβ⟩

end TrackF
end ZetaShell
