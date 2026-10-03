/-
Node KL1 (track K, bandwidth) — the K-λ transfer. At bandwidth λ the kernel seen by two on-line zeros whose ordinates
differ by h mean spacings is k_ψ(λh) (x = γL/2π = λ·γℓ/2π). A certificate for the bandwidth-one functional is EXACTLY
a certificate for the bandwidth-λ functional in mean-spacing units with penalties λμ (g = λh), and a fortiori with
penalties μ (the extra (1 − λ)Σ μ_l h_l is ≥ 0). No slack is consumed. [Test: bandwidth_check.py on X2's K = 5 data.]
The chain itself works in x-units, where nothing changes; KL1 is the dictionary to the draft's mean-spacing reading.
-/
import ZetaS.InterfacesV2

namespace ZetaS

namespace KL1aux

lemma gapSpan_smul {K : ℕ} (g : Fin (K - 1) → ℝ) (lam : ℝ) (i s : ℕ) :
    gapSpan (fun l => lam * g l) i s = lam * gapSpan g i s := by
  unfold gapSpan; rw [Finset.mul_sum]

/-- `F^{(λ)}_{γ,λμ}(h) = F_{γ,μ}(λh)`. -/
lemma localF_scaleMu {K : ℕ} (W : LocalWeights K) (k : ℝ → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : Fin (K - 1) → ℝ) :
    localF (fun t => k (lam * t)) (W.scaleMu lam hlam) h = localF k W (fun l => lam * h l) := by
  unfold localF
  congr 1
  · exact Finset.sum_congr rfl fun l _ => by simp only [LocalWeights.scaleMu]; ring
  · refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [LocalWeights.scaleMu, gapSpan_smul]

end KL1aux

open KL1aux

/-- exact form: `LocalCert k W c ↔ LocalCert (k(λ·)) (W.scaleMu λ) c` for `λ > 0`. -/
theorem localCert_scaleMu_iff {K : ℕ} (W : LocalWeights K) (k : ℝ → ℝ) (c : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    LocalCert k W c ↔ LocalCert (fun t => k (lam * t)) (W.scaleMu lam hlam.le) c := by
  constructor
  · intro hLI h hh
    rw [localF_scaleMu W k hlam.le h]
    exact hLI _ fun l => mul_nonneg hlam.le (hh l)
  · intro hLI g hg
    have := hLI (fun l => lam⁻¹ * g l) fun l => mul_nonneg (inv_nonneg.2 hlam.le) (hg l)
    rw [localF_scaleMu W k hlam.le] at this
    have e : (fun l => lam * (lam⁻¹ * g l)) = g := by
      funext l; rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
    rwa [e] at this

/-- unscaled penalties: `LocalCert k W c → LocalCert (k(λ·)) W c` for `0 < λ ≤ 1`. -/
theorem localCert_rescale {K : ℕ} (W : LocalWeights K) {k : ℝ → ℝ} {c lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) (hLI : LocalCert k W c) : LocalCert (fun t => k (lam * t)) W c := by
  intro h hh
  have h1 := (localCert_scaleMu_iff W k c hlam0).1 hLI h hh
  refine h1.trans ?_
  unfold localF
  simp only [LocalWeights.scaleMu]
  have : ∑ l, lam * W.μ l * h l ≤ ∑ l, W.μ l * h l := by
    apply Finset.sum_le_sum; intro l _
    have := mul_nonneg (W.μ_nonneg l) (hh l)
    nlinarith
  linarith

end ZetaS
