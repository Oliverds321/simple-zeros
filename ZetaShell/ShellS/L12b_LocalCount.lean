/-
L7_12c (3 Oct 2026): the q-uniform unit-window zero count, in the finite-subset form used by the proof of
Lemma 6a (lem:shell-6a, sec_shell.tex l.645–647: "The unit-window count is `n(χ;t) ≤ C₀ log(r(|t|+2))`").
For every primitive `χ` mod `r ≥ 1` (ζ = the character mod 1 included), every real `t` and every finite set `s` of
nontrivial zeros with `t < γ ≤ t + 1`: `Σ_{ρ∈s} m_ρ ≤ A₀ (log r + log(|t|+3))`, with ONE absolute `A₀`.
Inputs (green, no `sorry`): `Zeta23.ThmE.localCountChi_uniform_proof` (`r > 1`), `Zeta23.RvM.zetaZeroConfig_local_count`
(`r = 1`).
-/
import ZetaShell.PropZ.ZZ4_Count

noncomputable section
open Complex

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- a finite family of points of a window, with the multiplicities of `Z`, has total multiplicity `≤ Z.N`. -/
lemma L12b_sum_le_N (Z : Zeta23.ZeroConfig) {ι : Type*} (s : Finset ι) (f : ι ↪ ℂ) (m : ι → ℕ) (t : ℝ)
    (hmem : ∀ i ∈ s, f i ∈ Z.window t (t + 1)) (hm : ∀ i ∈ s, m i = Z.mult (f i)) :
    ∑ i ∈ s, (m i : ℝ) ≤ (Z.N t (t + 1) : ℝ) := by
  classical
  have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
  unfold Zeta23.ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : s.map f ⊆ hfin.toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Set.Finite.mem_toFinset]
    exact hmem i hi
  have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
  rw [Finset.sum_map] at h
  have h2 : ∑ i ∈ s, m i = ∑ i ∈ s, Z.mult (f i) := Finset.sum_congr rfl hm
  have h3 : ∑ i ∈ s, m i ≤ ∑ x ∈ hfin.toFinset, Z.mult x := h2 ▸ h
  exact_mod_cast h3

/-- **uniform local count** (finite-subset form): one absolute `A₀ ≥ 1` with
`Σ_{ρ∈s} m_ρ ≤ A₀ (log r + log(|t|+3))` for every primitive `χ` mod `r` (`r = 1`: ζ). -/
theorem L12b_local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → ∀ (t : ℝ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}),
      (∀ ρ ∈ s, t < ρ.1.im ∧ ρ.1.im ≤ t + 1) →
        ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ A₀ * (Real.log r + Real.log (|t| + 3)) := by
  obtain ⟨A₁, hA₁, hloc₁⟩ := Zeta23.ThmE.localCountChi_uniform_proof
  obtain ⟨A₂, hA₂, hloc₂⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨max A₁ A₂, le_trans hA₁ (le_max_left _ _), ?_⟩
  intro r _ χ hχ t s hs
  have ht3 : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have hl3 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hlr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
  rcases Nat.lt_or_ge 1 r with hr | hr
  · have hseam := Zeta23.ThmE.LSeam_of hr hχ
    have h1 := hloc₁ r χ hr hχ t
    rw [← Zeta23.ThmE.LZeros_N hseam] at h1
    have h2 : ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ ((Zeta23.ThmE.LZeros hseam).N t (t + 1) : ℝ) :=
      L12b_sum_le_N (Zeta23.ThmE.LZeros hseam) s (Function.Embedding.subtype _) (fun ρ => zmult χ ρ.1) t
        (fun ρ hρ => ⟨ρ.2, hs ρ hρ⟩) (fun ρ _ => rfl)
    rw [Real.log_mul hr0.ne' ht3.ne'] at h1
    calc ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ A₁ * (Real.log r + Real.log (|t| + 3)) := h2.trans h1
      _ ≤ max A₁ A₂ * (Real.log r + Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · have h1 : r = 1 := le_antisymm hr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
    subst h1
    have hL : χ.LFunction = riemannZeta := DirichletCharacter.LFunction_modOne_eq
    have hmem : ∀ ρ ∈ s, (Function.Embedding.subtype _ ρ : ℂ) ∈ Zeta23.zetaZeroConfig.window t (t + 1) := by
      intro ρ hρ
      refine ⟨?_, hs ρ hρ⟩
      have h := ρ.2
      show riemannZeta ρ.1 = 0 ∧ 0 < ρ.1.re ∧ ρ.1.re < 1
      rw [← hL]; exact h
    have hm : ∀ ρ ∈ s, zmult χ ρ.1 = Zeta23.zetaZeroConfig.mult (Function.Embedding.subtype _ ρ) := by
      intro ρ _
      show (analyticOrderAt χ.LFunction ρ.1).toNat = (analyticOrderAt riemannZeta ρ.1).toNat
      rw [hL]
    have h2 := L12b_sum_le_N Zeta23.zetaZeroConfig s (Function.Embedding.subtype _) (fun ρ => zmult χ ρ.1) t
      hmem hm
    have h3 := hloc₂ t
    simp only [Nat.cast_one, Real.log_one, zero_add]
    calc ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ A₂ * Real.log (|t| + 3) := h2.trans h3
      _ ≤ max A₁ A₂ * Real.log (|t| + 3) := mul_le_mul_of_nonneg_right (le_max_right _ _) hl3

end ShellS
end ZetaShell
