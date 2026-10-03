/-
Sub-node Z9e (agent L3_1) — the count seams I′ versus (T, 2T]: I′ ⊇ (T, 2T], and every zero of I′ ∖ (T, 2T] is
counted at most once, with multiplicity at most its weight in N(I′) − N(T, 2T).
-/
import ZetaS.ZeroSide.Z9s_Spec

noncomputable section

namespace ZetaS
namespace Z9

open Zeta23

lemma window_subset (Z : ZeroConfig) (T : ℝ) : Z.window T (2 * T) ⊆ Z.window (lo T) (hi T) := by
  rintro ρ ⟨hc, h1, h2⟩
  have := Real.sqrt_nonneg T
  exact ⟨hc, by simp only [lo]; linarith, by simp only [hi]; linarith⟩

lemma ncard_inter_eq_sum {W : Set ℂ} (hW : W.Finite) (p : ℂ → Prop) [DecidablePred p] :
    ((W ∩ {ρ | p ρ}).ncard : ℝ) = ∑ ρ ∈ hW.toFinset, if p ρ then (1 : ℝ) else 0 := by
  have : W ∩ {ρ | p ρ} = ↑(hW.toFinset.filter p) := by ext ρ; simp
  rw [this, Set.ncard_coe_finset, Finset.card_filter]; push_cast; rfl

lemma finsum_inter_eq_sum {W : Set ℂ} (hW : W.Finite) (p : ℂ → Prop) [DecidablePred p] (f : ℂ → ℕ) :
    ((∑ᶠ ρ ∈ W ∩ {ρ | p ρ}, f ρ : ℕ) : ℝ) = ∑ ρ ∈ hW.toFinset, if p ρ then (f ρ : ℝ) else 0 := by
  have : W ∩ {ρ | p ρ} = ↑(hW.toFinset.filter p) := by ext ρ; simp
  rw [this, finsum_mem_coe_finset, Finset.sum_filter]; push_cast; rfl

lemma finsum_eq_sum {W : Set ℂ} (hW : W.Finite) (f : ℂ → ℕ) :
    ((∑ᶠ ρ ∈ W, f ρ : ℕ) : ℝ) = ∑ ρ ∈ hW.toFinset, (f ρ : ℝ) := by
  rw [finsum_mem_eq_finite_toFinset_sum f hW]; push_cast; rfl

lemma ncard_eq_sum {W : Set ℂ} (hW : W.Finite) : (W.ncard : ℝ) = ∑ ρ ∈ hW.toFinset, (1 : ℝ) := by
  rw [Set.ncard_eq_toFinset_card W hW, Finset.card_eq_sum_ones]; push_cast; rfl

/-- The seam inequality on finsets: a count `g ≤ m` on `s \ s₀` grows by at most `Σ_s m − Σ_{s₀} m`. -/
lemma sum_le_sum_add_diff {s₀ s : Finset ℂ} (h : s₀ ⊆ s) (g m : ℂ → ℝ) (hg : ∀ ρ ∈ s \ s₀, g ρ ≤ m ρ) :
    ∑ ρ ∈ s, g ρ ≤ ∑ ρ ∈ s₀, g ρ + (∑ ρ ∈ s, m ρ - ∑ ρ ∈ s₀, m ρ) := by
  classical
  rw [← Finset.sum_sdiff h (f := g), ← Finset.sum_sdiff h (f := m)]
  have := Finset.sum_le_sum hg
  linarith

theorem count_seams (Z : ZeroConfig) (T : ℝ) :
    (Z.Ns (lo T) (hi T) : ℝ) ≤ Z.Ns T (2 * T) + ((Z.NIprime T : ℝ) - Z.N T (2 * T)) ∧
    (Z.Nd (lo T) (hi T) : ℝ) ≤ Z.Nd T (2 * T) + ((Z.NIprime T : ℝ) - Z.N T (2 * T)) ∧
    (Z.N0 (lo T) (hi T) : ℝ) + Z.Ns (lo T) (hi T) - Z.N0s (lo T) (hi T)
      ≤ (Z.N0 T (2 * T) : ℝ) + Z.Ns T (2 * T) - Z.N0s T (2 * T) + ((Z.NIprime T : ℝ) - Z.N T (2 * T)) ∧
    (Z.N0s (lo T) (hi T) : ℝ) ≤ Z.N0s T (2 * T) + ((Z.NIprime T : ℝ) - Z.N T (2 * T)) := by
  classical
  have hW : (Z.window (lo T) (hi T)).Finite := Z.finite_window (lo T) (hi T)
  have hW₀ : (Z.window T (2 * T)).Finite := Z.finite_window T (2 * T)
  have hsub : hW₀.toFinset ⊆ hW.toFinset := Set.Finite.toFinset_subset_toFinset.mpr (window_subset Z T)
  have hm : ∀ ρ ∈ hW.toFinset \ hW₀.toFinset, (1 : ℝ) ≤ Z.mult ρ := by
    intro ρ hρ
    have : ρ ∈ Z.carrier := ((Set.Finite.mem_toFinset _).mp (Finset.mem_sdiff.mp hρ).1).1
    exact_mod_cast Z.one_le_mult ρ this
  have hN : (Z.NIprime T : ℝ) - Z.N T (2 * T)
      = ∑ ρ ∈ hW.toFinset, (Z.mult ρ : ℝ) - ∑ ρ ∈ hW₀.toFinset, (Z.mult ρ : ℝ) := by
    rw [← finsum_eq_sum hW, ← finsum_eq_sum hW₀]; rfl
  rw [hN]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 := ncard_inter_eq_sum hW (fun ρ => Z.mult ρ = 1)
    have e2 := ncard_inter_eq_sum hW₀ (fun ρ => Z.mult ρ = 1)
    simp only [ZeroConfig.Ns, ZeroConfig.simple] at e1 e2 ⊢
    rw [e1, e2]
    refine sum_le_sum_add_diff hsub _ _ fun ρ hρ => ?_
    have := hm ρ hρ
    split_ifs <;> linarith
  · simp only [ZeroConfig.Nd]
    rw [ncard_eq_sum hW, ncard_eq_sum hW₀]
    exact sum_le_sum_add_diff hsub _ _ fun ρ hρ => hm ρ hρ
  · have a1 := finsum_inter_eq_sum hW (fun ρ => ρ.re = 1 / 2) Z.mult
    have a2 := finsum_inter_eq_sum hW₀ (fun ρ => ρ.re = 1 / 2) Z.mult
    have b1 := ncard_inter_eq_sum hW (fun ρ => Z.mult ρ = 1)
    have b2 := ncard_inter_eq_sum hW₀ (fun ρ => Z.mult ρ = 1)
    have c1 := ncard_inter_eq_sum hW (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)
    have c2 := ncard_inter_eq_sum hW₀ (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)
    simp only [ZeroConfig.N0, ZeroConfig.Ns, ZeroConfig.N0s, ZeroConfig.simple, ZeroConfig.onLine] at a1 a2 b1 b2 ⊢
    rw [Set.inter_assoc (Z.window (lo T) (hi T)), Set.inter_assoc (Z.window T (2 * T)), ← Set.setOf_and,
      a1, a2, b1, b2, c1, c2]
    have key := sum_le_sum_add_diff hsub
      (fun ρ => (if ρ.re = 1 / 2 then (Z.mult ρ : ℝ) else 0) + (if Z.mult ρ = 1 then (1 : ℝ) else 0)
        - (if ρ.re = 1 / 2 ∧ Z.mult ρ = 1 then (1 : ℝ) else 0)) (fun ρ => (Z.mult ρ : ℝ))
      (fun ρ hρ => by
        have := hm ρ hρ
        split_ifs <;> first | linarith | (exfalso; tauto))
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
    linarith
  · have c1 := ncard_inter_eq_sum hW (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)
    have c2 := ncard_inter_eq_sum hW₀ (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)
    simp only [ZeroConfig.N0s, ZeroConfig.simple, ZeroConfig.onLine]
    rw [Set.inter_assoc (Z.window (lo T) (hi T)), Set.inter_assoc (Z.window T (2 * T)), ← Set.setOf_and,
      c1, c2]
    refine sum_le_sum_add_diff hsub _ _ fun ρ hρ => ?_
    have := hm ρ hρ
    split_ifs <;> linarith


end Z9
end ZetaS
