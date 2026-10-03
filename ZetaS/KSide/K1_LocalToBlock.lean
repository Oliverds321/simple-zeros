/-
Node K1 (track K) — lem:zeta-local (l.379–392) in the position-weighted form of lem:zeta-Dprime (l.524–527):
for points y₀ < ⋯ < y_{m−1} (m ≥ K) with gaps g_j = y_{j+1} − y_j and LocalCert k W c,
"E(G) := Σ_{i≠j} k(y_i − y_j)² ≥ c(m − K + 1) − Σ_{t} Σ_{l<K−1} μ_l g_{t+l}".
Proof: apply the certificate to window t (gap vector l ↦ g_{t+l}), sum over t = 0, …, m − K; a pair at index
distance s < K receives ≤ Σ_i γ_{s,i} = 2 (γ ≥ 0) and has weight 2k² in E (k even); pairs at distance ≥ K dropped.
Deps: ChallengeZetaS (LocalWeights, LocalCert, localF, gapSpan).
-/
import ZetaS.Interfaces
import ZetaS.SigmaDist.A2_AggTrueWindow

open Finset

namespace ZetaS

theorem local_to_block {K : ℕ} (W : LocalWeights K) (k : ℝ → ℝ) (hk : ∀ t, k (-t) = k t) {c : ℝ}
    (hLI : LocalCert k W c) {m : ℕ} (hKm : K ≤ m) (y : ℕ → ℝ) (hy : StrictMono y) :
    c * ((m : ℝ) - K + 1)
        - ∑ t ∈ range (m - K + 1), ∑ l : Fin (K - 1), W.μ l * (y (t + l + 1) - y (t + l))
      ≤ ∑ i ∈ range m, ∑ j ∈ range m, if i = j then 0 else k (y i - y j) ^ 2 := by
  classical
  have hK2 : 2 ≤ K := W.two_le
  set Lw := m - K + 1 with hLw
  let w : ℕ → ℕ → ℝ := fun s p => k (y (p + s) - y p) ^ 2
  have hw0 : ∀ s p, 0 ≤ w s p := fun s p => sq_nonneg _
  let Pφ : ℕ → ℝ := fun t => ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * w s (t + i)
  -- (1) one window: the certificate at the gap vector of window t
  have hF : ∀ t, c ≤ (∑ l : Fin (K - 1), W.μ l * (y (t + l + 1) - y (t + l))) + Pφ t := by
    intro t
    have hg : ∀ l : Fin (K - 1), 0 ≤ y (t + l + 1) - y (t + l) :=
      fun l => sub_nonneg.2 (hy.monotone (by omega))
    have h := hLI (fun l : Fin (K - 1) => y (t + l + 1) - y (t + l)) hg
    unfold localF at h
    have hP : (∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s),
        W.γ s i * k (gapSpan (fun l : Fin (K - 1) => y (t + l + 1) - y (t + l)) i s) ^ 2) = Pφ t := by
      apply Finset.sum_congr rfl; intro s hs; apply Finset.sum_congr rfl; intro i hi
      have hs' := Finset.mem_Icc.1 hs; have hi' := Finset.mem_range.1 hi
      rw [A2fix.gapSpan_tele y t (by omega : i + s ≤ K - 1)]
    rw [hP] at h
    exact h
  -- (2) sum over the windows
  have hsumF : c * (Lw : ℝ) ≤ (∑ t ∈ range Lw, ∑ l : Fin (K - 1), W.μ l * (y (t + l + 1) - y (t + l)))
      + ∑ t ∈ range Lw, Pφ t := by
    rw [← Finset.sum_add_distrib]
    have := Finset.sum_le_sum fun t (_ : t ∈ range Lw) => hF t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hLwR : (Lw : ℝ) = (m : ℝ) - K + 1 := by
    rw [hLw, Nat.cast_add, Nat.cast_sub hKm]; push_cast; ring
  -- (3) the pair parts add up to at most E
  let f : ℕ → ℕ → ℝ := fun p q => k (y p - y q) ^ 2
  have hf0 : ∀ p q, 0 ≤ f p q := fun p q => sq_nonneg _
  have hE : (∑ i ∈ range m, ∑ j ∈ range m, if i = j then (0 : ℝ) else k (y i - y j) ^ 2)
      = ∑ q ∈ ((range m) ×ˢ (range m)).filter (fun q => q.1 ≠ q.2), f q.1 q.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases h : p = q <;> simp [h, f]
  have step1 : ∑ t ∈ range Lw, Pφ t
      = ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * ∑ t ∈ range Lw, w s (t + i) := by
    simp only [Pφ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have step2 : ∀ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * ∑ t ∈ range Lw, w s (t + i)
      ≤ 2 * ∑ p ∈ range (m - s), w s p := by
    intro s hs
    have hs' := Finset.mem_Icc.1 hs
    calc ∑ i ∈ range (K - s), W.γ s i * ∑ t ∈ range Lw, w s (t + i)
        ≤ ∑ i ∈ range (K - s), W.γ s i * ∑ p ∈ range (m - s), w s p := by
          apply Finset.sum_le_sum; intro i hi
          have hi' := Finset.mem_range.1 hi
          apply mul_le_mul_of_nonneg_left _ (W.γ_nonneg s hs i hi)
          exact A2fix.sum_shift_le (w s) (hw0 s) (fun t ht => by omega)
      _ = 2 * ∑ p ∈ range (m - s), w s p := by rw [← Finset.sum_mul, W.γ_sum s hs]
  have step3 : ∀ s ∈ Icc 1 (K - 1), 2 * ∑ p ∈ range (m - s), w s p
      = ∑ p ∈ range (m - s), (f p (p + s) + f (p + s) p) := by
    intro s _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [w, f]
    rw [show y p - y (p + s) = -(y (p + s) - y p) by ring, hk]
    ring
  have step4 : ∑ s ∈ Icc 1 (K - 1), ∑ p ∈ range (m - s), (f p (p + s) + f (p + s) p)
      ≤ ∑ q ∈ ((range m) ×ˢ (range m)).filter (fun q => q.1 ≠ q.2), f q.1 q.2 := by
    rw [Finset.sum_sigma']
    set S := (Icc 1 (K - 1)).sigma (fun s => range (m - s)) with hS
    let φ1 : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun y => (y.2, y.2 + y.1)
    let φ2 : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun y => (y.2 + y.1, y.2)
    have hmemS : ∀ y ∈ S, 1 ≤ y.1 ∧ y.2 + y.1 < m := by
      intro y hy
      rw [hS, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hy
      omega
    have inj1 : ∀ a ∈ S, ∀ b ∈ S, φ1 a = φ1 b → a = b := by
      rintro ⟨s, p⟩ _ ⟨s', p'⟩ _ h
      simp only [φ1, Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have : s = s' := by omega
      subst this; rfl
    have inj2 : ∀ a ∈ S, ∀ b ∈ S, φ2 a = φ2 b → a = b := by
      rintro ⟨s, p⟩ _ ⟨s', p'⟩ _ h
      simp only [φ2, Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      have : s = s' := by omega
      subst this; rfl
    have hdisj : Disjoint (S.image φ1) (S.image φ2) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨z, hz, hyz⟩ := hb
      have := hmemS y hy; have := hmemS z hz
      simp only [φ1, φ2, Prod.mk.injEq] at hyz
      omega
    have hsub : S.image φ1 ∪ S.image φ2 ⊆ ((range m) ×ˢ (range m)).filter (fun q => q.1 ≠ q.2) := by
      intro a ha
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ha
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      rcases ha with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · have := hmemS y hy; simp only [φ1]; omega
      · have := hmemS y hy; simp only [φ2]; omega
    calc ∑ y ∈ S, (f y.2 (y.2 + y.1) + f (y.2 + y.1) y.2)
        = ∑ q ∈ S.image φ1, f q.1 q.2 + ∑ q ∈ S.image φ2, f q.1 q.2 := by
          rw [Finset.sum_image inj1, Finset.sum_image inj2, ← Finset.sum_add_distrib]
      _ = ∑ q ∈ S.image φ1 ∪ S.image φ2, f q.1 q.2 := (Finset.sum_union hdisj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hf0 q.1 q.2)
  have hP : ∑ t ∈ range Lw, Pφ t
      ≤ ∑ q ∈ ((range m) ×ˢ (range m)).filter (fun q => q.1 ≠ q.2), f q.1 q.2 := by
    calc ∑ t ∈ range Lw, Pφ t
        = ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * ∑ t ∈ range Lw, w s (t + i) := step1
      _ ≤ ∑ s ∈ Icc 1 (K - 1), 2 * ∑ p ∈ range (m - s), w s p := Finset.sum_le_sum step2
      _ = ∑ s ∈ Icc 1 (K - 1), ∑ p ∈ range (m - s), (f p (p + s) + f (p + s) p) :=
          Finset.sum_congr rfl step3
      _ ≤ _ := step4
  rw [hE, ← hLwR]
  linarith

end ZetaS
