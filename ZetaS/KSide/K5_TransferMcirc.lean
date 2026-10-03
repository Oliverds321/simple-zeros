/-
Node K5 (track K) — lem:zeta-transfer (l.461–486), asymptotic form: under GramFamily and LocalCert k_ψ W c
(|k_ψ| ≤ 1), for every c′ ∈ (0, c) and m ≥ K, with A′ = c′(m − K + 1), B′ = Φ_m(A′), τ = ν(m − K + 1)/m:
"tr Ψ(M°) ≥ (B′/m)s₁ − (B′/A′)τN − o(N)".
Proof: L4 (drop nothing: Ê is handled by Lidskii / 2-Lipschitz Ψ, ‖Ê‖₁ = tr Ê = o(N)), K3, K2 with Λ ≤ N + o(N).
[Note: the draft first restricts to interior zeros; with `GramFamily.trunc` (tr Ê = o(N) for all simple zeros,
lem:sigd-residue (iv)) the restriction is unnecessary.]
Deps: K2, K3, L4, node L6 (Lidskii for 2-Lipschitz f: |tr f(A) − tr f(B)| ≤ 2‖A − B‖₁ for A, B ⪰ 0).
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L6_TraceLipschitz
import ZetaS.KSide.K2_Packing
import ZetaS.KSide.K3_LocalCertTransfer
import ZetaS.KSide.KHelpers

open Filter Asymptotics RHLinalg Matrix

namespace ZetaS

theorem transfer_Mcirc {N : ℝ → ℝ} {R : ℝ} {kψ : ℝ → ℝ} (Fm : GramFamily N R kψ)
    (hk1 : ∀ t, |kψ t| ≤ 1) {K : ℕ} (W : LocalWeights K) {c : ℝ} (hLI : LocalCert kψ W c)
    {c' : ℝ} (hc' : 0 < c') (hcc : c' < c) {m : ℕ} (hKm : K ≤ m) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      PhiM m (c' * ((m : ℝ) - K + 1)) / m * ((Fm.G T).s1 : ℝ)
          - PhiM m (c' * ((m : ℝ) - K + 1)) / (c' * ((m : ℝ) - K + 1))
            * (W.nu * ((m : ℝ) - K + 1) / m) * N T - r T
        ≤ trFun (Matrix.isHermitian_conjTranspose_mul_self (Fm.G T).V) Psi := by
  classical
  obtain ⟨e, he, hke⟩ := Fm.kernel
  obtain ⟨rs, hrs, hspan⟩ := Fm.span
  have hK2 : 2 ≤ K := W.two_le
  have hKmR : (K : ℝ) ≤ m := by exact_mod_cast hKm
  set A' := c' * ((m : ℝ) - K + 1) with hA'
  set B' := PhiM m A' with hB'
  set τ := W.nu * ((m : ℝ) - K + 1) / m with hτ
  have hA'0 : 0 < A' := mul_pos hc' (by linarith)
  have hB'0 : 0 ≤ B' := K2aux.PhiM_nonneg (le_trans hK2 hKm) hA'0.le
  have hnu : 0 ≤ W.nu := Finset.sum_nonneg fun l _ => W.μ_nonneg l
  have hτ0 : 0 ≤ τ := div_nonneg (mul_nonneg hnu (by linarith)) (by linarith)
  set C := B' / A' * τ with hC
  have hC0 : 0 ≤ C := mul_nonneg (div_nonneg hB'0 hA'0.le) hτ0
  refine ⟨fun T => 2 * B' + C * rs T + 2 * RHLinalg.rtrace (Fm.G T).Etr, ?_, ?_⟩
  · have h1 : (fun _ : ℝ => 2 * B') =o[atTop] N :=
      isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp Fm.N_tendsto))
    exact (h1.add (hrs.const_mul_left C)).add (Fm.trunc.const_mul_left 2)
  · have hsmall : ∀ᶠ T in atTop, 4 * ((K : ℝ) - 1) * e T ≤ c - c' := by
      have hlim : Tendsto (fun T => 4 * ((K : ℝ) - 1) * e T) atTop (nhds 0) := by
        simpa using he.const_mul (4 * ((K : ℝ) - 1))
      exact hlim.eventually (ge_mem_nhds (by linarith))
    filter_upwards [hke, hspan, hsmall] with T hkT hsT hsmT
    set D := Fm.G T
    -- (a) the certificate for the true kernel at c′
    have hkD1 : ∀ t, |D.k t| ≤ 1 := KHelp.kernel_abs_le_one D.k_posDef D.k_zero
    have hLI' : LocalCert D.k W c' :=
      KHelp.localCert_mono (localCert_transfer W hLI hk1 hkD1 hkT) (by linarith)
    -- (b) packing on the kernel matrix of the simple zeros
    have hpack := packing_fix W D.k D.k_zero D.k_even D.k_posDef hc' hLI' D.x D.x_mono D.Λ_nonneg D.x_span hKm
    -- (c) Lidskii: Ψ is 2-Lipschitz, kerMat − M° = Ê ⪰ 0
    have hM : (D.Vᴴ * D.V).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self D.V
    have hdiff : kerMat D.k D.x - D.Vᴴ * D.V = D.Etr := by
      rw [conjTranspose_eq_transpose_of_trivial, D.gram_eq]; abel
    have hL6 := trFun_sub_le_of_psd_le (D.k_posDef D.s1 D.x) hM (by rw [hdiff]; exact D.Etr_psd)
      (f := Psi) (Lf := 2) (by norm_num) KHelp.psi_lipschitz
    rw [hdiff, abs_le] at hL6
    have hΛ := mul_le_mul_of_nonneg_left hsT hC0
    have hdef : trFun (Matrix.isHermitian_conjTranspose_mul_self D.V) Psi = trFun hM.isHermitian Psi := rfl
    rw [hdef]
    have hpack' : B' / m * D.s1 - 2 * B' - C * D.Λ ≤ trFun (D.k_posDef D.s1 D.x).isHermitian Psi := by
      simpa only [hC, mul_assoc] using hpack
    nlinarith [hL6.1]

end ZetaS
