/-
L7_1c (round 2, cloud, 3 Oct 2026): **node T1 without `PNTErrorTerm` and without the certificate hypothesis.**
`shell_S53_qle_tree_noP` is `Top/T1_Headline.shell_S53_qle_tree'` (L7_1) with the frame taken from
`Design.shell_frame_qle_of_K_noP` (`ShellK/LF_FrameNoP`: Theorem K + `F1c_chain` + the design layer's rows,
hypothesis `ZeroDensityInput` only) instead of the skeleton node `shell_frame_qle` (F1, `sorry`), and F2
(`shell_assembly`, ZetaQ's Proposition 3.1) as before. In `shell_S53_qle_tree'`, `hP` and `hcert` are only passed on
to `shell_frame_qle`, whose proof is `sorry`. The original `shell_S53_qle_tree'` is kept unchanged in `Top/T1_Headline`.
-/
import ZetaShell.Top.T1_Headline
import ZetaShell.ShellK.LF_FrameNoP

namespace ZetaShell

open Filter Topology

/-- **Theorem S(5/3), `1 < q ≤ Q`, tree form, hypothesis `ZeroDensityInput` only** (the conclusion of
`shell_S53_qle_tree` / `shell_S53_qle_tree'`, without `hP : PNTErrorTerm` and `hcert : CertS53`). -/
theorem shell_S53_qle_tree_noP (hD : ZeroDensityInput) (r ε θ : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertS53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * ZetaQ.NfamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε)
            (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  obtain ⟨Fr⟩ := Design.shell_frame_qle_of_K_noP hD r ε θ hr hε hθ hθ'
  have hκ : (0 : ℝ) ≤ 2 - ((PcertS53 : ℚ) : ℝ) := by norm_num [PcertS53]
  obtain ⟨Q₀, c, hc, h⟩ := shell_assembly _ r ε _ _ _ (shellRate_tendsto θ hθ) (shellRate_nonneg θ) hκ Fr
  refine ⟨Q₀, c, hc, fun Qn hQn => ?_⟩
  have := h Qn hQn
  simp only [shellRate] at this
  convert this using 2
  ring

end ZetaShell
