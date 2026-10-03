/-
Node K7 (L7_3): Lemma K (i) (lem:K, eq:K-pointwise), pointwise in `s`. Draft: "For every `s ∈ ℝ`,
`Σ_{χ∈𝔉_Q} |A_χ(s)|² ≤ Q²[‖a(s)‖² − (1 − η_P) U (s − ℓ_K)₊ 1{s ≤ log 𝒳 − 1} + 2‖a(s)‖] + (2π𝒳 + R′²)‖a(s)‖²`",
with `sup_{s≥ℓ_K} η_P = O((ℒ/T)^{1/2} + ℒ^{−2}) = O(1/log Q)` for `r ≥ 3`.
Lean form: the family `𝔉_Q` is `1 < q ≤ Q` with `ZetaQ.primitiveChars` (ZetaQ's `Family.qle`, ζ excluded),
`A_χ(s) = ZetaQ.charSum q ⌊𝒳⌋ (acoef T s) χ`, `η_P` replaced by `C/log Q` (eventually), `R′ = max(2, R₀)`.
Proof (draft (a)–(c) + assembly): K1s (Farey majorant) → K2 on `Ξ = 𝔉_Q \ 𝔉_{R₀}` at `δ = Q⁻²` and on `𝔉_{R′}` at
`δ = R′⁻²` → K3 (holes are disjoint subsets of `Z` containing the `Δ`-balls) → eq:K-hole from K4, K4b, K5 and
`(x − y)² ≥ x² − 2xy` → K6. Difficulty: M (given K1s–K6).
ROUND 3 (L7_3): DERIVED here from K7a `farey_hole_bound`, K7b `hole_lower`, K7c `plain_bound` (off the hole range) and
K6 `principal_arc_mass` (frozen statement); the statement of K7 is unchanged.
-/
import ZetaShell.Defs.LK_Defs
import ZetaShell.LemmaK.LK_K6_ArcMass
import ZetaShell.LemmaK.LK_K7a_FareyHole
import ZetaShell.LemmaK.LK_K7b_HoleLower
import ZetaShell.LemmaK.LK_K7c_Plain

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

/-- **K7 (Lemma K (i)), asymptotic form.** -/
theorem killed_pointwise (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ∑ q ∈ Finset.Icc 2 Qn, ∑ χ ∈ ZetaQ.primitiveChars q,
          ‖ZetaQ.charSum q ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
            (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s) χ‖ ^ 2
        ≤ (Qn : ℝ) ^ 2 *
            (ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
              - (1 - C / Real.log (Qn : ℝ)) * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi))
                  * max (s - ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) 0
                  * (if s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 then 1 else 0)
              + 2 * Real.sqrt (ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
                  (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)))
          + (2 * Real.pi * Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)
              + (max 2 (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)) ^ 2)
            * ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s) := by
  obtain ⟨C, hK6⟩ := principal_arc_mass lam r ε hlam1 hlam2 hr hε
  refine ⟨C, ?_⟩
  filter_upwards [hK6, farey_hole_bound lam r ε hlam1 hlam2 hr hε, hole_lower lam r ε hlam1 hlam2 hr hε]
    with Qn h6 ha hb
  intro s
  have hl20 : 0 ≤ ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq0 := Real.sqrt_nonneg
    (ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s))
  have hQ2 : 0 ≤ (Qn : ℝ) ^ 2 := sq_nonneg _
  have hX0 : 0 ≤ Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) := (Real.exp_pos _).le
  by_cases hs : ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s ∧
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1
  · obtain ⟨hs1, hs2⟩ := hs
    have hA := ha s hs1 hs2
    have hB := hb s hs1 hs2
    have hJ := h6 s hs1 hs2
    rw [if_pos hs2, max_eq_left (by linarith)]
    have h1 := mul_le_mul_of_nonneg_left hJ (by linarith : 0 ≤ s - ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε))
    have h2 := mul_le_mul_of_nonneg_left (show
      ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
          - holeInt ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
              (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)
              (ZetaQ.Twin (Qn : ℝ) r ε * Lc (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) / (2 * Real.exp s))
        ≤ ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
          - (1 - C / Real.log (Qn : ℝ)) * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi))
              * (s - ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) * 1
          + 2 * Real.sqrt (ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
              (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)) by linarith) hQ2
    linarith
  · have hz : (1 - C / Real.log (Qn : ℝ)) * (ZetaQ.Twin (Qn : ℝ) r ε / (2 * Real.pi))
        * max (s - ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) 0
        * (if s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 then 1 else 0) = 0 := by
      by_cases h1 : ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s
      · have h2 : ¬ s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) - 1 := fun h => hs ⟨h1, h⟩
        rw [if_neg h2]; ring
      · rw [max_eq_right (by linarith [not_le.mp h1])]; ring
    rw [hz]
    have hP := plain_bound Qn ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ (acoef (ZetaQ.Twin (Qn : ℝ) r ε) s)
    have hN : ((⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ : ℕ) : ℝ) ≤ Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) :=
      Nat.floor_le hX0
    have hc : Real.pi * ((⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊ : ℕ) : ℝ)
        ≤ 2 * Real.pi * Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)
          + (max 2 (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hN Real.pi_pos.le
      nlinarith [sq_nonneg (max 2 (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s)), Real.pi_pos]
    have h3 := mul_le_mul_of_nonneg_right hc hl20
    have h4 := mul_nonneg hQ2 hsq0
    nlinarith [hP, h3, h4]

end LemmaK
end ZetaShell
