/-
Node C-rev (track C) — the reversal-class reduction used by the certifiers (rem:sigd-cert: 72 classes cover the 128
patterns; LB3 "exact reversal symmetry"): if γ, μ and the site credits b are reversal-symmetric, then (LI_m) for one
representative of each class {𝐦, 𝐦 ∘ rev} gives (LI_m) for all patterns. `rep` is any class selector.

Proof (L2_2): reversing both the pattern and the gap vector leaves `localFm` and the claim `Σ b_i(m_i)` unchanged
(`localFm_rev`, `claim_rev` below): the pair slot (s, i) goes to (s, K−s−1−i), the gap span over [i, i+s) goes to
the span over [K−s−1−i, K−1−i), and the marks at i, i+s go to those at K−1−i, K−s−1−i.
-/
import ZetaS.Interfaces

open Finset

namespace ZetaS

/-- reversal symmetry of all-marks data: `γ_{s,i} = γ_{s,K−s−1−i}`, `μ_l = μ_{K−2−l}`, `b_i(j) = b_{K−1−i}(j)`. -/
def MarkWeights.IsRevSymm {K : ℕ} (W : MarkWeights K) : Prop :=
  (∀ s ∈ Icc 1 (K - 1), ∀ i ∈ range (K - s), W.γ s i = W.γ s (K - s - 1 - i)) ∧
  (∀ l : Fin (K - 1), W.μ l = W.μ l.rev) ∧ (∀ i : Fin K, ∀ j, W.b i j = W.b i.rev j)

/-- marks of the reversed pattern. -/
private lemma markVal_rev {K : ℕ} (m : Fin K → Fin 2) {i : ℕ} (hi : i < K) :
    markVal (m ∘ Fin.rev) i = markVal m (K - 1 - i) := by
  have hi' : K - 1 - i < K := by omega
  have hr : Fin.rev (⟨i, hi⟩ : Fin K) = ⟨K - 1 - i, hi'⟩ := by
    ext
    simp only [Fin.val_rev]
    omega
  unfold markVal
  rw [dif_pos hi, dif_pos hi', Function.comp_apply, hr]

/-- gap spans of the reversed gap vector. -/
private lemma gapSpan_rev {K : ℕ} (g : Fin (K - 1) → ℝ) {i s : ℕ} (his : i + s ≤ K - 1) :
    gapSpan (g ∘ Fin.rev) i s = gapSpan g (K - s - 1 - i) s := by
  unfold gapSpan
  apply Finset.sum_equiv (Fin.revPerm)
  · intro l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.revPerm_apply, Fin.val_rev]
    have := l.2
    omega
  · intro l _
    simp [Fin.revPerm_apply]

private lemma claim_rev {K : ℕ} (W : MarkWeights K) (hb : ∀ i : Fin K, ∀ j, W.b i j = W.b i.rev j)
    (m : Fin K → Fin 2) : ∑ i, W.b i ((m ∘ Fin.rev) i) = ∑ i, W.b i (m i) := by
  calc ∑ i, W.b i ((m ∘ Fin.rev) i) = ∑ i, W.b (Fin.rev i) (m (Fin.rev i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hb i]; rfl
    _ = ∑ i, W.b i (m i) := Equiv.sum_comp Fin.revPerm (fun i => W.b i (m i))

private lemma localFm_rev {K : ℕ} (W : MarkWeights K) (k : ℝ → ℝ) (hsym : W.IsRevSymm)
    (m : Fin K → Fin 2) (g : Fin (K - 1) → ℝ) :
    localFm k W (m ∘ Fin.rev) (g ∘ Fin.rev) = localFm k W m g := by
  obtain ⟨hγ, hμ, _⟩ := hsym
  unfold localFm
  congr 1
  · -- the pair part
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_Icc.1 hs
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    -- j' := K - s - 1 - j is the reflected slot
    have hjs : K - s - 1 - j + s ≤ K - 1 := by omega
    have e1 : K - s - 1 - (K - s - 1 - j) = j := by omega
    have e2 : K - 1 - (K - s - 1 - j) = j + s := by omega
    have e3 : K - 1 - (K - s - 1 - j + s) = j := by omega
    rw [markVal_rev m (by omega : K - s - 1 - j < K), markVal_rev m (by omega : K - s - 1 - j + s < K),
      gapSpan_rev g hjs, e1, e2, e3,
      hγ s hs (K - s - 1 - j) (Finset.mem_range.2 (by omega)), e1]
    ring
  · -- the gap penalty
    calc ∑ l, W.μ l * (g ∘ Fin.rev) l = ∑ l, W.μ (Fin.rev l) * g (Fin.rev l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hμ l]; rfl
      _ = ∑ l, W.μ l * g l := Equiv.sum_comp Fin.revPerm (fun l => W.μ l * g l)

theorem localCertAM_of_classes {K : ℕ} (W : MarkWeights K) (k : ℝ → ℝ) (hsym : W.IsRevSymm)
    (rep : (Fin K → Fin 2) → Prop) (hrep : ∀ m, rep m ∨ rep (m ∘ Fin.rev))
    (hcls : ∀ m, rep m → ∀ g : Fin (K - 1) → ℝ, (∀ l, 0 ≤ g l) → ∑ i, W.b i (m i) ≤ localFm k W m g) :
    LocalCertAM k W := by
  intro m g hg
  rcases hrep m with h | h
  · exact hcls m h g hg
  · have := hcls (m ∘ Fin.rev) h (g ∘ Fin.rev) (fun l => hg _)
    rwa [claim_rev W hsym.2.2 m, localFm_rev W k hsym m g] at this

end ZetaS
