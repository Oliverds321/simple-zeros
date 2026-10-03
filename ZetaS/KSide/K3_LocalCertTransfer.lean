/-
Node K3 (track K) — the kernel-transfer step of lem:zeta-transfer (l.482–483): "|w_φ − w_ψ| ≤ 2|k_φ − k_ψ|, so F_K for
k_φ differs from F_K for k_ψ by at most 4(K − 1) sup|k_φ − k_ψ|. Hence (LI) holds for k_φ with c′".
Deps: ChallengeZetaS (LocalCert). Elementary.
-/
import ZetaS.Interfaces

open Finset

namespace ZetaS

theorem localCert_transfer {K : ℕ} (W : LocalWeights K) {k k' : ℝ → ℝ} {c e : ℝ}
    (hLI : LocalCert k W c) (hk1 : ∀ t, |k t| ≤ 1) (hk1' : ∀ t, |k' t| ≤ 1)
    (hkk : ∀ t, |k' t - k t| ≤ e) :
    LocalCert k' W (c - 4 * ((K : ℝ) - 1) * e) := by
  intro g hg
  have h := hLI g hg
  unfold localF at h ⊢
  have he : 0 ≤ e := (abs_nonneg _).trans (hkk 0)
  have hterm : ∀ s ∈ Icc 1 (K - 1), ∀ i ∈ range (K - s),
      W.γ s i * k (gapSpan g i s) ^ 2 - 2 * e * W.γ s i ≤ W.γ s i * k' (gapSpan g i s) ^ 2 := by
    intro s hs i hi
    have hγ := W.γ_nonneg s hs i hi
    set u := gapSpan g i s
    have h1 := hk1 u; have h2 := hk1' u; have h3 := hkk u
    have hsum2 : |k u + k' u| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    have hd : k u ^ 2 - k' u ^ 2 ≤ 2 * e := by
      have hfac : k u ^ 2 - k' u ^ 2 = (k u - k' u) * (k u + k' u) := by ring
      rw [hfac]
      calc (k u - k' u) * (k u + k' u) ≤ |(k u - k' u) * (k u + k' u)| := le_abs_self _
        _ = |k' u - k u| * |k u + k' u| := by rw [abs_mul, abs_sub_comm]
        _ ≤ e * 2 := mul_le_mul h3 hsum2 (abs_nonneg _) he
        _ = 2 * e := by ring
    nlinarith
  have hsum : (∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * k (gapSpan g i s) ^ 2)
      - 2 * e * (∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i)
      ≤ ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * k' (gapSpan g i s) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro s hs
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i hi => hterm s hs i hi
  have hγ : (∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i) = 2 * ((K : ℝ) - 1) := by
    rw [Finset.sum_congr rfl fun s hs => W.γ_sum s hs, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hK := W.two_le
    rw [show K - 1 + 1 - 1 = K - 1 by omega, Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hγ] at hsum
  linarith

end ZetaS
