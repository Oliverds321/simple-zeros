/-
Node Z2, corrected (agent L3_1, 28 Sep 2026). STATEMENT-CHANGE REQUEST: the skeleton `kWin_posDef`
(skeleton_v2/Z2_KWinPosDef.lean) is FALSE as written — `AdmWindow` does not exclude `v = 0`, and then
`kWin v L 0 = VPhiR v 0 / ∫ v² = 0/0 = 0 ≠ 1` (`kWin_posDef_false` below, with v = 0, L = 8, w = 1, c = 4).
Positive definiteness and evenness hold unconditionally; only `k(0) = 1` needs the nondegeneracy `∫ v² ≠ 0`.

  * `kWin_posDef_false`       — the counterexample, as a theorem.
  * `kWin_isPosDefKernel`     — `IsPosDefKernel (kWin v L)` for EVERY admissible v (no Fourier analysis: the kernel
                                matrix at points t_i is the full-lattice Gram matrix of the vectors u_{2πt_i/L} by the
                                tree's Poisson identity `hasSum_vHatR_mul`, hence PSD).
  * `kWin_posDef_fix`         — the skeleton statement plus `hv : ∫ u, v u ^ 2 ≠ 0`   (recommended form).
  * `kWin_posDef_of_ne_zero`  — the skeleton statement plus `h : v u₀ ≠ 0` for some u₀.

Draft: prop:zeta-pack "k positive definite with k(0) = 1"; eq:zeta-poisson (k_φ = V/∫φ²); lem:sigd-residue (i).
INTEGRATED (L0_1, 28 Sep 2026): the node's original name `ZetaS.kWin_posDef` (end of this file) carries the
statement of `kWin_posDef_fix` (the skeleton statement plus `hv : ∫ u, v u ^ 2 ≠ 0`), the statement change
accepted by the lead; the skeleton statement (false as written) is withdrawn.
-/
import ZetaS.InterfacesV2
import ZetaS.ZeroSide.Helpers

namespace ZetaS

/-- The skeleton statement of Z2 is false: the zero window is admissible and has `kWin 0 = 0`. -/
theorem kWin_posDef_false :
    ¬ ∀ (v : ℝ → ℝ) (L w c : ℝ), Zeta23.AdmWindow v L w c →
      IsPosDefKernel (kWin v L) ∧ kWin v L 0 = 1 ∧ ∀ t, kWin v L (-t) = kWin v L t := by
  intro h
  have hW : Zeta23.AdmWindow (fun _ => (0 : ℝ)) 8 1 4 := by
    refine ⟨le_rfl, by norm_num, le_rfl, fun _ => rfl, fun _ => le_rfl, fun _ => zero_le_one,
      contDiff_const, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩ <;> simp
  have h0 := (h _ _ _ _ hW).2.1
  simp [kWin] at h0

/-- Positive definiteness needs no nondegeneracy: kernel matrices of `kWin` are full-lattice Gram matrices. -/
theorem kWin_isPosDefKernel {v : ℝ → ℝ} {L w c : ℝ} (hW : Zeta23.AdmWindow v L w c) :
    IsPosDefKernel (kWin v L) := by
  intro n x
  have hL0 : L ≠ 0 := hW.L_pos.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ZeroSide.posSemidef_of_hasSum (fun i (k : ℤ) => uR v L 0 (2 * Real.pi * x i / L) k) _
    fun i j => ?_
  have h := ZeroSide.hasSum_uR_mul hW 0 (2 * Real.pi * x i / L) (2 * Real.pi * x j / L)
  have e : (2 * Real.pi * x i / L - 2 * Real.pi * x j / L) * L / (2 * Real.pi) = x i - x j := by
    field_simp
  rw [e] at h
  simpa only [kerMat, Matrix.of_apply] using h

/-- **Z2 (corrected, recommended).** The skeleton statement with the added hypothesis `∫ v² ≠ 0`. -/
theorem kWin_posDef_fix {v : ℝ → ℝ} {L w c : ℝ} (hW : Zeta23.AdmWindow v L w c)
    (hv : ∫ u, v u ^ 2 ≠ 0) :
    IsPosDefKernel (kWin v L) ∧ kWin v L 0 = 1 ∧ ∀ t, kWin v L (-t) = kWin v L t :=
  ⟨kWin_isPosDefKernel hW, ZeroSide.kWin_zero hW hv, ZeroSide.kWin_even hW⟩

/-- **Z2 (corrected, pointwise form).** The skeleton statement for a window that is not identically zero. -/
theorem kWin_posDef_of_ne_zero {v : ℝ → ℝ} {L w c : ℝ} (hW : Zeta23.AdmWindow v L w c)
    {u₀ : ℝ} (h : v u₀ ≠ 0) :
    IsPosDefKernel (kWin v L) ∧ kWin v L 0 = 1 ∧ ∀ t, kWin v L (-t) = kWin v L t :=
  kWin_posDef_fix hW (ZeroSide.integral_sq_pos hW h).ne'

end ZetaS

namespace ZetaS

/-- **Node Z2** under the node's original name, with the statement change ACCEPTED by the lead (28 Sep 2026): the
skeleton statement plus `hv : ∫ u, v u ^ 2 ≠ 0` — the statement of `kWin_posDef_fix` (L3_1). -/
theorem kWin_posDef {v : ℝ → ℝ} {L w c : ℝ} (hW : Zeta23.AdmWindow v L w c)
    (hv : ∫ u, v u ^ 2 ≠ 0) :
    IsPosDefKernel (kWin v L) ∧ kWin v L 0 = 1 ∧ ∀ t, kWin v L (-t) = kWin v L t :=
  kWin_posDef_fix hW hv

end ZetaS
