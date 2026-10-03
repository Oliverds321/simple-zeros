/-
Node T1 (L7_1): the tree-form headlines `shell_S53_qle_tree`, `shell_S53_dyadic_tree` (ShellInterfaces §3) FROM the
statements of F1 (frame) and F2 (assembly): with `κ = 2 − P_cert`, `2 − κ − c·rate = P_cert − c·(log Q)^{−θ}`.
The Mathlib-only headlines `ChallengeShell.shell_S53_qle/_dyadic` follow by node B1 (`rfl`).
Dependencies: F1, F2, B1. Difficulty: E. PROVED here modulo F1, F2.
-/
import ZetaShell.Skeleton.F1_ShellFrameQle
import ZetaShell.Frame.F2_ShellAssembly

namespace ZetaShell

open Filter Topology

theorem shellRate_tendsto (θ : ℝ) (hθ : 0 < θ) : Tendsto (shellRate θ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun Qn : ℕ => Real.log (Qn : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop hθ).comp h1

theorem shellRate_nonneg (θ : ℝ) : ∀ᶠ Qn : ℕ in atTop, 0 ≤ shellRate θ Qn := by
  filter_upwards [eventually_ge_atTop 1] with Qn hQn
  have : 0 ≤ Real.log (Qn : ℝ) := Real.log_nonneg (by exact_mod_cast hQn)
  exact Real.rpow_nonneg this _

theorem shell_S53_qle_tree' (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertS53) (r ε θ : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertS53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * ZetaQ.NfamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε)
            (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  obtain ⟨Fr⟩ := shell_frame_qle hD hP hcert r ε θ hr hε hθ hθ'
  have hκ : (0 : ℝ) ≤ 2 - ((PcertS53 : ℚ) : ℝ) := by norm_num [PcertS53]
  obtain ⟨Q₀, c, hc, h⟩ := shell_assembly _ r ε _ _ _ (shellRate_tendsto θ hθ) (shellRate_nonneg θ) hκ Fr
  refine ⟨Q₀, c, hc, fun Qn hQn => ?_⟩
  have := h Qn hQn
  simp only [shellRate] at this
  convert this using 2
  ring

theorem shell_S53_dyadic_tree' (hD : ZeroDensityInput) (hP : PNTErrorTerm) (hcert : CertD53) (r ε θ : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertD53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * ZetaQ.NfamCount ZetaQ.Family.dyadic Qn (ZetaQ.Twin (Qn : ℝ) r ε)
              (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.dyadic Qn (ZetaQ.Twin (Qn : ℝ) r ε)
            (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  obtain ⟨Fr⟩ := shell_frame_dyadic hD hP hcert r ε θ hr hε hθ hθ'
  have hκ : (0 : ℝ) ≤ 2 - ((PcertD53 : ℚ) : ℝ) := by norm_num [PcertD53]
  obtain ⟨Q₀, c, hc, h⟩ := shell_assembly _ r ε _ _ _ (shellRate_tendsto θ hθ) (shellRate_nonneg θ) hκ Fr
  refine ⟨Q₀, c, hc, fun Qn hQn => ?_⟩
  have := h Qn hQn
  simp only [shellRate] at this
  convert this using 2
  ring

end ZetaShell

#print axioms ZetaShell.shell_S53_qle_tree'
#print axioms ZetaShell.shellRate_tendsto
