/-
Sub-node Z9a6 (agent L3_1) — the counts of the frame of Z9a4 are the configuration's counts on I′, through the
partition 𝒵(I′) = {β = ½} ⊔ {β > ½} ⊔ reflect{β > ½} (multiplicity and simplicity are reflection-invariant).
-/
import ZetaS.ZeroSide.Z9a4_Frame

noncomputable section

open Matrix RHLinalg

namespace ZetaS
namespace Z9

open Zeta23

variable (Z : ZeroConfig) {P : Params} (ψ : ℝ → ℝ) (T : ℝ) (hP : P.Valid) (heven : ∀ s, ψ (-s) = ψ s) {c : ℝ}
  (hW : AdmWindow (P.phiV ψ T) (P.L T) P.w c) (hv : (∫ u, P.phiV ψ T u ^ 2) ≠ 0) (hT : 0 < T)

omit hP heven in
/-- 𝒵(I′) = {β = ½} ⊔ {β > ½} ⊔ reflect{β > ½}, as a sum identity. -/
lemma sum_ZI_split {M : Type*} [AddCommMonoid M] (g : ℂ → M) :
    ∑ ρ ∈ ZeroSide.ZI Z T, g ρ = ∑ ρ ∈ Son Z T, g ρ + ∑ ρ ∈ Aoff Z T, g ρ + ∑ ρ ∈ Aoff Z T, g (reflect ρ) := by
  classical
  have hrefl : ∑ ρ ∈ (ZeroSide.ZI Z T).filter (fun ρ => ρ.re < 1 / 2), g ρ
      = ∑ ρ ∈ Aoff Z T, g (reflect ρ) := by
    refine Finset.sum_nbij' reflect reflect ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      simp only [Finset.mem_filter] at hρ ⊢
      exact ⟨ZeroSide.reflect_mem_ZI Z T hρ.1, by rw [ZeroSide.reflect_re]; linarith⟩
    · intro ρ hρ
      simp only [Finset.mem_filter] at hρ ⊢
      exact ⟨ZeroSide.reflect_mem_ZI Z T hρ.1, by rw [ZeroSide.reflect_re]; linarith⟩
    · intro ρ _; exact ZeroSide.reflect_reflect ρ
    · intro ρ _; exact ZeroSide.reflect_reflect ρ
    · intro ρ _; rw [ZeroSide.reflect_reflect]
  rw [← hrefl, ← Finset.sum_filter_add_sum_filter_not (ZeroSide.ZI Z T) (fun ρ => ρ.re = 1 / 2),
    ← Finset.sum_filter_add_sum_filter_not ((ZeroSide.ZI Z T).filter (fun ρ => ¬ ρ.re = 1 / 2))
      (fun ρ => 1 / 2 < ρ.re), Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  · refine Finset.sum_congr (Finset.filter_congr fun ρ _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by linarith, h⟩
  · refine Finset.sum_congr (Finset.filter_congr fun ρ _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨h1, h2⟩; push Not at h2; exact lt_of_le_of_ne h2 h1
    · intro h; exact ⟨by linarith, by linarith⟩

omit hP heven in
lemma window_eq_ZI : Z.window (lo T) (hi T) = ↑(ZeroSide.ZI Z T) := (ZeroSide.coe_ZI Z T).symm

omit hP heven in
lemma mult_reflect_of_mem {ρ : ℂ} (h : ρ ∈ Aoff Z T) : Z.mult (reflect ρ) = Z.mult ρ :=
  Z.mult_reflect ρ (ZeroSide.mem_carrier_of_mem_ZI Z T (Finset.mem_filter.mp h).1)

omit hP heven in
/-- reindexing the on-line zeros by the sorted enumeration. -/
lemma sum_Son {M : Type*} [AddCommMonoid M] (g : ℂ → M) :
    ∑ ρ ∈ Son Z T, g ρ = ∑ i, g (eOn Z T i) := by
  rw [← Finset.sum_coe_sort (Son Z T), ← Equiv.sum_comp (eOn Z T)]

/-- the counts of the frame are the configuration's counts on I′. -/
theorem frameAt_counts :
    (frameAt Z ψ T hP heven hW hv hT).Nw = Z.NIprime T ∧
    (frameAt Z ψ T hP heven hW hv hT).NsW = Z.Ns (lo T) (hi T) ∧
    (frameAt Z ψ T hP heven hW hv hT).sEq 1 = Z.N0s (lo T) (hi T) ∧
    (frameAt Z ψ T hP heven hW hv hT).NdW = Z.Nd (lo T) (hi T) ∧
    ((frameAt Z ψ T hP heven hW hv hT).NscW : ℝ)
      = (Z.N0 (lo T) (hi T) : ℝ) + Z.Ns (lo T) (hi T) - Z.N0s (lo T) (hi T) := by
  classical
  have hw := window_eq_ZI Z T
  -- counts of the configuration as finset sums over 𝒵(I′)
  have eN : Z.NIprime T = ∑ ρ ∈ ZeroSide.ZI Z T, Z.mult ρ := by
    show ∑ᶠ ρ ∈ Z.window (lo T) (hi T), Z.mult ρ = _
    rw [hw, finsum_mem_coe_finset]
  have ecard : ∀ p : ℂ → Prop, ∀ [DecidablePred p], (Z.window (lo T) (hi T) ∩ {ρ | p ρ}).ncard
      = ∑ ρ ∈ ZeroSide.ZI Z T, if p ρ then 1 else 0 := by
    intro p _
    rw [hw, show (↑(ZeroSide.ZI Z T) : Set ℂ) ∩ {ρ | p ρ} = ↑((ZeroSide.ZI Z T).filter p) by ext; simp,
      Set.ncard_coe_finset, Finset.card_filter]
  have eNs : Z.Ns (lo T) (hi T) = ∑ ρ ∈ ZeroSide.ZI Z T, if Z.mult ρ = 1 then 1 else 0 :=
    ecard (fun ρ => Z.mult ρ = 1)
  have eN0s : Z.N0s (lo T) (hi T) = ∑ ρ ∈ ZeroSide.ZI Z T, if ρ.re = 1 / 2 ∧ Z.mult ρ = 1 then 1 else 0 := by
    rw [← ecard (fun ρ => ρ.re = 1 / 2 ∧ Z.mult ρ = 1)]
    simp only [ZeroConfig.N0s, ZeroConfig.onLine, ZeroConfig.simple, Set.inter_assoc, Set.setOf_and]
  have eNd : Z.Nd (lo T) (hi T) = ∑ ρ ∈ ZeroSide.ZI Z T, 1 := by
    simp only [ZeroConfig.Nd]; rw [hw, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  have eN0 : Z.N0 (lo T) (hi T) = ∑ ρ ∈ ZeroSide.ZI Z T, if ρ.re = 1 / 2 then Z.mult ρ else 0 := by
    simp only [ZeroConfig.N0, ZeroConfig.onLine]
    rw [hw, show (↑(ZeroSide.ZI Z T) : Set ℂ) ∩ {ρ | ρ.re = 1 / 2}
        = ↑((ZeroSide.ZI Z T).filter (fun ρ => ρ.re = 1 / 2)) by ext; simp,
      finsum_mem_coe_finset, Finset.sum_filter]
  -- the frame's counts
  have fS : ∀ q : ℂ → ℕ, ∑ ρ ∈ Son Z T, q ρ = ∑ i, q (eOn Z T i) := fun q => sum_Son Z T q
  have hA1 : ∀ q : ℂ → ℕ, (∀ ρ, q (reflect ρ) = q ρ ∨ ρ ∉ Aoff Z T) →
      ∑ ρ ∈ Aoff Z T, q (reflect ρ) = ∑ ρ ∈ Aoff Z T, q ρ := by
    intro q hq
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rcases hq ρ with h | h
    · exact h
    · exact absurd hρ h
  have hmA : ∀ ρ ∈ Aoff Z T, Z.mult (reflect ρ) = Z.mult ρ := fun ρ h => mult_reflect_of_mem Z T h
  have hS_on : ∀ ρ ∈ Son Z T, ρ.re = 1 / 2 := Son_re Z T
  have hA_off : ∀ ρ ∈ Aoff Z T, ¬ ρ.re = 1 / 2 := fun ρ h => by
    have := (Finset.mem_filter.mp h).2; linarith
  have hAr_off : ∀ ρ ∈ Aoff Z T, ¬ (reflect ρ).re = 1 / 2 := fun ρ h => by
    have := (Finset.mem_filter.mp h).2; rw [ZeroSide.reflect_re]; linarith
  have sM := sum_ZI_split Z T Z.mult
  have s1 := sum_ZI_split Z T (fun ρ => if Z.mult ρ = 1 then 1 else 0)
  have s2 := sum_ZI_split Z T (fun ρ => if ρ.re = 1 / 2 ∧ Z.mult ρ = 1 then 1 else 0)
  have s3 := sum_ZI_split Z T (fun _ => (1 : ℕ))
  have s4 := sum_ZI_split Z T (fun ρ => if ρ.re = 1 / 2 then Z.mult ρ else 0)
  have a1 : ∑ ρ ∈ Aoff Z T, Z.mult (reflect ρ) = ∑ ρ ∈ Aoff Z T, Z.mult ρ := Finset.sum_congr rfl hmA
  have a2 : ∑ ρ ∈ Aoff Z T, (if Z.mult (reflect ρ) = 1 then 1 else 0)
      = ∑ ρ ∈ Aoff Z T, (if Z.mult ρ = 1 then 1 else 0) :=
    Finset.sum_congr rfl fun ρ h => by rw [hmA ρ h]
  have a3 : ∑ ρ ∈ Aoff Z T, (if ρ.re = 1 / 2 ∧ Z.mult ρ = 1 then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun ρ h => if_neg fun h' => hA_off ρ h h'.1
  have a3' : ∑ ρ ∈ Aoff Z T, (if (reflect ρ).re = 1 / 2 ∧ Z.mult (reflect ρ) = 1 then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun ρ h => if_neg fun h' => hAr_off ρ h h'.1
  have a4 : ∑ ρ ∈ Aoff Z T, (if ρ.re = 1 / 2 then Z.mult ρ else 0) = 0 :=
    Finset.sum_eq_zero fun ρ h => if_neg (hA_off ρ h)
  have a4' : ∑ ρ ∈ Aoff Z T, (if (reflect ρ).re = 1 / 2 then Z.mult (reflect ρ) else 0) = 0 :=
    Finset.sum_eq_zero fun ρ h => if_neg (hAr_off ρ h)
  have b2 : ∑ ρ ∈ Son Z T, (if ρ.re = 1 / 2 ∧ Z.mult ρ = 1 then 1 else 0)
      = ∑ ρ ∈ Son Z T, (if Z.mult ρ = 1 then 1 else 0) :=
    Finset.sum_congr rfl fun ρ h => by simp [hS_on ρ h]
  have b4 : ∑ ρ ∈ Son Z T, (if ρ.re = 1 / 2 then Z.mult ρ else 0) = ∑ ρ ∈ Son Z T, Z.mult ρ :=
    Finset.sum_congr rfl fun ρ h => by simp [hS_on ρ h]
  have fsEq : (frameAt Z ψ T hP heven hW hv hT).sEq 1 = ∑ ρ ∈ Son Z T, (if Z.mult ρ = 1 then 1 else 0) := by
    show (Finset.univ.filter fun i => Z.mult (eOn Z T i) = 1).card = _
    rw [Finset.card_filter, fS]
  have fp1 : ((Aoff Z T).filter (fun ρ => Z.mult ρ = 1)).card
      = ∑ ρ ∈ Aoff Z T, (if Z.mult ρ = 1 then 1 else 0) := Finset.card_filter _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (∑ i, Z.mult (eOn Z T i)) + 2 * ∑ ρ ∈ Aoff Z T, Z.mult ρ = Z.NIprime T
    rw [eN, sM, a1, ← fS]; ring
  · show (frameAt Z ψ T hP heven hW hv hT).sEq 1 + 2 * ((Aoff Z T).filter (fun ρ => Z.mult ρ = 1)).card
      = Z.Ns (lo T) (hi T)
    rw [fsEq, fp1, eNs, s1, a2]; ring
  · rw [fsEq, eN0s, s2, a3, a3', b2]; ring
  · show (Son Z T).card + 2 * (Aoff Z T).card = Z.Nd (lo T) (hi T)
    rw [eNd, s3, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]; ring
  · show (((∑ i, Z.mult (eOn Z T i)) + 2 * ((Aoff Z T).filter (fun ρ => Z.mult ρ = 1)).card : ℕ) : ℝ) = _
    rw [eN0, eNs, eN0s, s4, s1, s2, a4, a4', a2, a3, a3', b2, b4, fp1, ← fS]
    push_cast; ring

end Z9
end ZetaS
