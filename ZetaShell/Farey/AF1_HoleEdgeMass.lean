/-
Node AF1 (L7_6 statement draft): **hole and hole-edge mass, repair F1** (lem:shell-F1, sec_shell.tex l.461–473).

Draft: "Let `𝒳 := {a/r, a/r ± 1/(rQ) : r ≤ R₁}`. Then
`Σ_{ξ∈𝒳} ∫_{|θ−ξ|≤δ} |S(θ)|² dθ ≪ δ(N + R₁²)‖a‖² = O(ε + N(log Q)¹²/(εQ²))‖a‖² = o(‖a‖²)`."
Proof in the draft: three families, each `1/(2R₁²)`-spaced (for the shifted ones because `R₁ ≤ Q/(2K)`), large sieve
at every shift `|t| ≤ δ`, integrate over `t`.

Lean form and hypotheses added:
* `≪` made explicit with the trunk's **proved** large sieve (Gallagher's constant, `ZetaQ.Gallagher.gallagher_additive_large_sieve`):
  each family at spacing `1/(2R₁²)` costs `(2R₁² + πN)‖a‖²` per shift, so the constant is `3·2δ·(2R₁² + πN)`;
  with Selberg's constant one would get `N − 1 + 2R₁²` in place of `πN + 2R₁²` (same order);
* `a` is read on `0 < n ≤ N` (`ZetaQ.expSum N a`); the draft's `N` (centre of the support window) is `≍` this `N`;
* the spacing needs only `2R₁ ≤ Q` (the draft's `R₁ ≤ Q/(2K)` with `K ≥ 1` implies it); `K` does not enter;
* `𝒳` is summed as a multiset (three families over `r ≤ R₁`, `(a, r) = 1`, `0 ≤ a < r`), which is ≥ the sum over the set;
* `0 ≤ δ`; no upper bound on `δ` is needed (a translate of a spaced family is spaced).
The draft's second equality (`δ = ε/N`, `R₁ = N(log Q)⁶/(εQ)`) is arithmetic and not part of the node.
Dependencies: trunk `ZetaQ.Gallagher.gallagher_additive_large_sieve`; interval integrals. Difficulty: M.
**PROVED (L7_6)**, axioms `[propext, Classical.choice, Quot.sound]`; the spacing of the shifted families is
`farey_shift_spaced` below (`|b/r − b′/r′ − m| ≥ 1/(rr′)` absorbs the shift difference `≤ R₁/(rr′Q) ≤ 1/(2rr′)`).
-/
import ZetaShell.Defs.TF_Defs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace TrackF

/-- Shifted Farey fractions `b/r + σ/(rQ)`, `r ≤ R₁`, `2R₁ ≤ Q`, `|σ| ≤ 1`, are `1/(2R₁²)`-spaced modulo 1. -/
theorem farey_shift_spaced (Q R1 : ℕ) (hRQ : 2 * R1 ≤ Q) (σ : ℤ) (hσ : |σ| ≤ 1)
    {r r' b b' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r') (hrR : r ≤ R1) (hr'R : r' ≤ R1)
    (hb : b < r) (hb' : b' < r') (hcb : Nat.Coprime b r) (hcb' : Nat.Coprime b' r')
    (hne : (r, b) ≠ (r', b')) (m : ℤ) :
    1 / (2 * (R1 : ℝ) ^ 2)
      ≤ |((b : ℝ) / r + (σ : ℝ) / ((r : ℝ) * Q)) - ((b' : ℝ) / r' + (σ : ℝ) / ((r' : ℝ) * Q))
          - (m : ℝ)| := by
  have hn0 : (b : ℤ) * r' - (b' : ℤ) * r - m * r * r' ≠ 0 := by
    intro h0
    apply hne
    have h1 : (b : ℤ) * r' = (b' : ℤ) * r + m * r * r' := by linarith
    have hrd : (r : ℤ) ∣ (r' : ℤ) := by
      have hdv : (r : ℤ) ∣ (b : ℤ) * r' := ⟨b' + m * r', by rw [h1]; ring⟩
      have hco : IsCoprime (r : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcb.symm
      exact hco.dvd_of_dvd_mul_left hdv
    have hr'd : (r' : ℤ) ∣ (r : ℤ) := by
      have hdv : (r' : ℤ) ∣ (b' : ℤ) * r := ⟨b - m * r, by linear_combination -h1⟩
      have hco : IsCoprime (r' : ℤ) (b' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcb'.symm
      exact hco.dvd_of_dvd_mul_left hdv
    have hrr : (r : ℤ) = r' := Int.dvd_antisymm (by positivity) (by positivity) hrd hr'd
    have hrr' : r = r' := by exact_mod_cast hrr
    subst hrr'
    have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    have h2 : (b : ℤ) = b' + m * r := by
      apply mul_right_cancel₀ hr0
      linear_combination h1
    have hbr : (b : ℤ) < r := by exact_mod_cast hb
    have hb'r : (b' : ℤ) < r := by exact_mod_cast hb'
    have hb0 : (0 : ℤ) ≤ b := by positivity
    have hb'0 : (0 : ℤ) ≤ b' := by positivity
    have hrpos : (0 : ℤ) ≤ r := by positivity
    have hm : m = 0 := by
      rcases lt_trichotomy m 0 with h | h | h
      · have hm1 : m ≤ -1 := by omega
        have : m * (r : ℤ) ≤ -1 * r := mul_le_mul_of_nonneg_right hm1 hrpos
        linarith
      · exact h
      · have hm1 : 1 ≤ m := by omega
        have : 1 * (r : ℤ) ≤ m * r := mul_le_mul_of_nonneg_right hm1 hrpos
        linarith
    subst hm
    have hbb : b = b' := by
      have : (b : ℤ) = b' := by linarith
      exact_mod_cast this
    rw [hbb]
  have hR1 : (1 : ℝ) ≤ R1 := by exact_mod_cast (le_trans hr hrR)
  have hx : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hy : (1 : ℝ) ≤ r' := by exact_mod_cast hr'
  have hxR : (r : ℝ) ≤ R1 := by exact_mod_cast hrR
  have hyR : (r' : ℝ) ≤ R1 := by exact_mod_cast hr'R
  have hQ2 : 2 * (R1 : ℝ) ≤ Q := by exact_mod_cast hRQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hxy : (0 : ℝ) < (r : ℝ) * r' := by positivity
  set D : ℝ := (b : ℝ) / r - (b' : ℝ) / r' - (m : ℝ) with hD
  set s : ℝ := (σ : ℝ) / ((r : ℝ) * Q) - (σ : ℝ) / ((r' : ℝ) * Q) with hs
  have hsplit : ((b : ℝ) / r + (σ : ℝ) / ((r : ℝ) * Q)) - ((b' : ℝ) / r' + (σ : ℝ) / ((r' : ℝ) * Q))
      - (m : ℝ) = D + s := by rw [hD, hs]; ring
  rw [hsplit]
  have hDn : D = (((b : ℤ) * r' - (b' : ℤ) * r - m * r * r' : ℤ) : ℝ) / ((r : ℝ) * r') := by
    rw [hD]; push_cast; field_simp
  have hnabs : (1 : ℝ) ≤ |(((b : ℤ) * r' - (b' : ℤ) * r - m * r * r' : ℤ) : ℝ)| := by
    have := Int.one_le_abs hn0
    exact_mod_cast this
  have hDabs : 1 / ((r : ℝ) * r') ≤ |D| := by
    rw [hDn, abs_div, abs_of_pos hxy]
    exact div_le_div_of_nonneg_right hnabs hxy.le
  have hs_eq : s = ((σ : ℝ) * ((r' : ℝ) - r)) / ((r : ℝ) * r' * Q) := by
    rw [hs]; field_simp
  have hnum : |(σ : ℝ) * ((r' : ℝ) - r)| ≤ R1 := by
    rw [abs_mul]
    have h1 : |(σ : ℝ)| ≤ 1 := by exact_mod_cast hσ
    have h2 : |(r' : ℝ) - r| ≤ R1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (σ : ℝ), abs_nonneg ((r' : ℝ) - r)]
  have hxyQ : (0 : ℝ) < (r : ℝ) * r' * Q := by positivity
  have hsabs : |s| ≤ 1 / (2 * ((r : ℝ) * r')) := by
    rw [hs_eq, abs_div, abs_of_pos hxyQ, div_le_div_iff₀ hxyQ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hnum (show (0 : ℝ) ≤ 2 * ((r : ℝ) * r') by positivity)]
  have htri : |D| - |s| ≤ |D + s| := by
    have := abs_sub_abs_le_abs_sub D (-s)
    rwa [abs_neg, sub_neg_eq_add] at this
  have hhalf : 1 / ((r : ℝ) * r') = 2 * (1 / (2 * ((r : ℝ) * r'))) := by field_simp
  have hRR : (r : ℝ) * r' ≤ (R1 : ℝ) ^ 2 := by nlinarith
  have hfin : 1 / (2 * (R1 : ℝ) ^ 2) ≤ 1 / (2 * ((r : ℝ) * r')) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- **AF1 (lem:shell-F1).** -/
theorem hole_edge_mass (Q R1 N : ℕ) (δ : ℝ) (a : ℕ → ℂ) (hRQ : 2 * R1 ≤ Q) (hδ : 0 ≤ δ) :
    ∑ r ∈ Finset.Icc 1 R1, ∑ b ∈ ZetaQ.reducedResidues r, ∑ σ ∈ ({-1, 0, 1} : Finset ℤ),
        ∫ θ in ((b : ℝ) / r + (σ : ℝ) / ((r : ℝ) * Q) - δ)..((b : ℝ) / r + (σ : ℝ) / ((r : ℝ) * Q) + δ),
          ‖ZetaQ.expSum N a θ‖ ^ 2
      ≤ 3 * (2 * δ) * (2 * (R1 : ℝ) ^ 2 + Real.pi * N) * ZetaQ.l2sq N a := by
  classical
  have hl2 : 0 ≤ ZetaQ.l2sq N a := by unfold ZetaQ.l2sq; positivity
  rcases Nat.eq_zero_or_pos R1 with hR0 | hRpos
  · subst hR0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  have hR1 : (1 : ℝ) ≤ R1 := by exact_mod_cast hRpos
  have hcont : Continuous (fun θ : ℝ => ‖ZetaQ.expSum N a θ‖ ^ 2) := by
    unfold ZetaQ.expSum ZetaQ.e
    fun_prop
  set T : Finset ((_ : ℕ) × ℕ) := (Finset.Icc 1 R1).sigma ZetaQ.reducedResidues with hT
  set C : ℝ := (2 * (R1 : ℝ) ^ 2 + Real.pi * N) * ZetaQ.l2sq N a with hC
  -- the pointwise large sieve for one shifted family
  have hpt : ∀ (σ : ℤ), |σ| ≤ 1 → ∀ t : ℝ,
      ∑ x ∈ T, ‖ZetaQ.expSum N a (t + ((x.2 : ℝ) / x.1 + (σ : ℝ) / ((x.1 : ℝ) * Q)))‖ ^ 2 ≤ C := by
    intro σ hσ t
    have hδ0 : (0 : ℝ) < 1 / (2 * (R1 : ℝ) ^ 2) := by positivity
    have hδ1 : 1 / (2 * (R1 : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have hsep : ∀ i j : {x // x ∈ T}, i ≠ j → ∀ m : ℤ, 1 / (2 * (R1 : ℝ) ^ 2)
        ≤ |(t + ((i.1.2 : ℝ) / i.1.1 + (σ : ℝ) / ((i.1.1 : ℝ) * Q)))
            - (t + ((j.1.2 : ℝ) / j.1.1 + (σ : ℝ) / ((j.1.1 : ℝ) * Q))) - (m : ℝ)| := by
      rintro ⟨⟨r, b⟩, hi⟩ ⟨⟨r', b'⟩, hj⟩ hij m
      have hi' := hi
      have hj' := hj
      rw [hT, Finset.mem_sigma, Finset.mem_Icc, ZetaQ.mem_reducedResidues] at hi' hj'
      have hne : (r, b) ≠ (r', b') := by
        intro h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hij rfl
      have := farey_shift_spaced Q R1 hRQ σ hσ hi'.1.1 hj'.1.1 hi'.1.2 hj'.1.2 hi'.2.1 hj'.2.1
        hi'.2.2 hj'.2.2 hne m
      simp only
      rw [show ∀ u v w : ℝ, (t + u) - (t + v) - w = u - v - w by intros; ring]
      exact this
    have hG := ZetaQ.Gallagher.gallagher_additive_large_sieve {x // x ∈ T} N a
      (fun i => t + ((i.1.2 : ℝ) / i.1.1 + (σ : ℝ) / ((i.1.1 : ℝ) * Q))) _ hδ0 hδ1 hsep
    rw [one_div, inv_inv] at hG
    rw [hC, ← Finset.sum_coe_sort T]
    exact hG
  -- integrate one family over the shifts `|t| ≤ δ`
  have hfam : ∀ (σ : ℤ), |σ| ≤ 1 →
      ∑ x ∈ T, ∫ θ in ((x.2 : ℝ) / x.1 + (σ : ℝ) / ((x.1 : ℝ) * Q) - δ)..((x.2 : ℝ) / x.1
          + (σ : ℝ) / ((x.1 : ℝ) * Q) + δ), ‖ZetaQ.expSum N a θ‖ ^ 2 ≤ 2 * δ * C := by
    intro σ hσ
    have hshift : ∀ x ∈ T,
        ∫ θ in ((x.2 : ℝ) / x.1 + (σ : ℝ) / ((x.1 : ℝ) * Q) - δ)..((x.2 : ℝ) / x.1
          + (σ : ℝ) / ((x.1 : ℝ) * Q) + δ), ‖ZetaQ.expSum N a θ‖ ^ 2
        = ∫ t in (-δ)..δ, ‖ZetaQ.expSum N a (t + ((x.2 : ℝ) / x.1 + (σ : ℝ) / ((x.1 : ℝ) * Q)))‖ ^ 2 := by
      intro x _
      rw [intervalIntegral.integral_comp_add_right (fun θ => ‖ZetaQ.expSum N a θ‖ ^ 2)]
      congr 1 <;> ring
    rw [Finset.sum_congr rfl hshift, ← intervalIntegral.integral_finsetSum]
    · calc ∫ t in (-δ)..δ, ∑ x ∈ T,
            ‖ZetaQ.expSum N a (t + ((x.2 : ℝ) / x.1 + (σ : ℝ) / ((x.1 : ℝ) * Q)))‖ ^ 2
          ≤ ∫ t in (-δ)..δ, C := by
            apply intervalIntegral.integral_mono_on (by linarith)
            · apply Continuous.intervalIntegrable
              exact continuous_finsetSum _ (fun x _ => hcont.comp (continuous_id.add continuous_const))
            · exact intervalIntegrable_const
            · intro t _
              exact hpt σ hσ t
        _ = 2 * δ * C := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
    · intro x _
      exact (hcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  -- assemble the three families
  rw [Finset.sum_sigma' (Finset.Icc 1 R1) ZetaQ.reducedResidues]
  rw [← hT, Finset.sum_comm]
  calc ∑ σ ∈ ({-1, 0, 1} : Finset ℤ), ∑ x ∈ T,
        ∫ θ in ((x.2 : ℝ) / x.1 + (σ : ℝ) / ((x.1 : ℝ) * Q) - δ)..((x.2 : ℝ) / x.1
          + (σ : ℝ) / ((x.1 : ℝ) * Q) + δ), ‖ZetaQ.expSum N a θ‖ ^ 2
      ≤ ∑ σ ∈ ({-1, 0, 1} : Finset ℤ), 2 * δ * C := by
        refine Finset.sum_le_sum (fun σ hσ => hfam σ ?_)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
        rcases hσ with rfl | rfl | rfl <;> norm_num
    _ = 3 * (2 * δ) * (2 * (R1 : ℝ) ^ 2 + Real.pi * N) * ZetaQ.l2sq N a := by
        rw [Finset.sum_const, hC]
        simp
        ring

end TrackF
end ZetaShell
