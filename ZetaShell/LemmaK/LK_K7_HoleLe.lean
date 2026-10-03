/-
lean_work/L7_3/skeleton/LK_K7_HoleLe.lean (L7_3, round 3): `Hole(S) ≤ ‖a‖²` — the `Δ`-balls around the Farey points
`b/r`, `r ≤ R`, are pairwise `2Δ`-separated mod 1 when `2Δ ≤ 1/(rr′)`, so their integrals fit in one period
(trunk `ZetaQ.Gallagher.sum_integral_le_period`) and Parseval (`integral_normSq_expSum`) closes. PROVED.
-/
import ZetaShell.LemmaK.LK_K7_Defs
import ZetaShell.LemmaK.LK_K3_HoleCores

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace LemmaK

theorem mem_reducedResidues {r b : ℕ} : b ∈ ZetaQ.reducedResidues r ↔ b < r ∧ Nat.Coprime b r := by
  classical
  unfold ZetaQ.reducedResidues
  simp [Finset.mem_filter, Finset.mem_range]

theorem expSum_normSq_continuous (N : ℕ) (a : ℕ → ℂ) : Continuous (fun t => ‖ZetaQ.expSum N a t‖ ^ 2) := by
  have h : Continuous (ZetaQ.expSum N a) := by
    rw [show ZetaQ.expSum N a = ZetaQ.Gallagher.trig (Finset.Ioc 0 N) a from rfl]
    exact ZetaQ.Gallagher.continuous_trig _ _
  exact h.norm.pow 2

theorem expSum_normSq_periodic (N : ℕ) (a : ℕ → ℂ) :
    Function.Periodic (fun t => ‖ZetaQ.expSum N a t‖ ^ 2) 1 := by
  intro t
  have h := ZetaQ.Gallagher.trig_periodic (Finset.Ioc 0 N) a t
  show ‖ZetaQ.Gallagher.trig (Finset.Ioc 0 N) a (t + 1)‖ ^ 2 = ‖ZetaQ.Gallagher.trig (Finset.Ioc 0 N) a t‖ ^ 2
  rw [h]

/-- **`Hole(S) ≤ ‖a‖²`.** -/
theorem holeInt_le_l2sq (N : ℕ) (a : ℕ → ℂ) (R Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : 2 * Δ ≤ 1)
    (hsepΔ : ∀ r r' : ℕ, 1 ≤ r → r ≤ ⌊R⌋₊ → 1 ≤ r' → r' ≤ ⌊R⌋₊ → 2 * Δ ≤ 1 / ((r : ℝ) * r')) :
    holeInt N a R Δ ≤ ZetaQ.l2sq N a := by
  classical
  set g : ℝ → ℝ := fun t => ‖ZetaQ.expSum N a t‖ ^ 2 with hg
  set A := (Finset.Icc 1 ⌊R⌋₊).sigma (fun r => ZetaQ.reducedResidues r) with hA
  have e1 : holeInt N a R Δ = ∑ x ∈ A, ∫ t in ((x.2 : ℝ) / x.1 - 2 * Δ / 2)..((x.2 : ℝ) / x.1 + 2 * Δ / 2), g t := by
    unfold holeInt
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => ?_
    have := intervalIntegral.integral_comp_add_left (fun t => ‖ZetaQ.expSum N a t‖ ^ 2) ((b : ℝ) / r)
      (a := -Δ) (b := Δ)
    rw [this]
    congr 1 <;> ring
  rw [e1, ← Finset.sum_coe_sort A]
  have hsep : ∀ i j : A, i ≠ j → ∀ m : ℤ,
      2 * Δ ≤ |(i.1.2 : ℝ) / i.1.1 - (j.1.2 : ℝ) / j.1.1 - (m : ℝ)| := by
    intro i j hij m
    obtain ⟨⟨r, b⟩, hi⟩ := i
    obtain ⟨⟨r', b'⟩, hj⟩ := j
    simp only [hA, Finset.mem_sigma, Finset.mem_Icc, mem_reducedResidues] at hi hj
    obtain ⟨⟨hr1, hrR⟩, hbr, hcop⟩ := hi
    obtain ⟨⟨hr1', hrR'⟩, hbr', hcop'⟩ := hj
    have hne : (r, b % r) ≠ (r', b' % r') := by
      rw [Nat.mod_eq_of_lt hbr, Nat.mod_eq_of_lt hbr']
      intro h
      apply hij
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2; rfl
    have hgap := farey_gap (by omega : 0 < r) (by omega : 0 < r') hcop hcop' hne
    have hd := distZ_le ((b : ℝ) / r - (b' : ℝ) / r') m
    have hs := hsepΔ r r' hr1 hrR hr1' hrR'
    simp only
    linarith
  have h := ZetaQ.Gallagher.sum_integral_le_period (g := g) (fun t => by rw [hg]; positivity)
    (expSum_normSq_continuous N a) (expSum_normSq_periodic N a)
    (fun i : A => (i.1.2 : ℝ) / i.1.1) (by linarith) hΔ1 hsep
  rw [ZetaQ.Gallagher.integral_normSq_expSum] at h
  exact h

end LemmaK
end ZetaShell
