/-
ZetaShell/Top/HeadlineReduced.lean (L0_6, integration of the family library, 28 Sep 2026).

**The reduced headline statements are the statements of record** (lead's ruling, 28 Sep 2026). The four headlines of
the architect (`ZetaShell.shell_S53_qle`, `shell_S53_dyadic`, `shell_S53_bounded`, `shell_S53_bounded_dyadic`,
module `ZetaShell.Challenge`, L7_1) carry three displayed hypotheses: `hD : ZeroDensityInput`,
`hP : PNTErrorTerm` and the certificate (`hcert : CertS53`, resp. `CertD53`). Two of them are no longer needed:
- the certificate is a theorem, `ZetaShell.certS53 : CertS53` and `ZetaShell.certD53 : CertD53` (Track R, L7_5,
  module `ZetaShell.Cert.R4_CertS53`, level A);
- the prime number theorem is used only in its medium form, which is a theorem of the tree
  (`ZetaShell.PNT.PNTMedium`, L7_2), not in the strong form `PNTErrorTerm`.
The reduced statements below have the SAME conclusions, and as hypotheses only `ZeroDensityInput` and the quantifier
hypotheses. The architect's statements in `ZetaShell.Challenge` are kept unchanged.

**Status (L7_1c, 3 Oct 2026).** `shell_S53_qle_reduced` is PROVED here from the frame route without `PNTErrorTerm`:
`Top.T1_HeadlineNoP.shell_S53_qle_tree_noP` (F2 = ZetaQ's Proposition 3.1 on the frame
`ShellK.LF_FrameNoP.Design.shell_frame_qle_of_K_noP`, itself Theorem K + `F1c_chain` + the design layer's rows; the
medium PNT enters below Theorem K), then node B1 (`famN_qle_eq`, `famN0s_qle_eq`, `twin_eq`, all `rfl`). Its only
open leaf is that of Theorem K (`K2_shellZone` at the time of writing). The other three reduced headlines are open
(`sorry`): the dyadic family and bounded height have no frame route in the library yet.

Proved implications (no `sorry` of their own):
- reduced ⇒ architect's form, for each of the four (the two extra hypotheses are dropped);
- architect's form ⇒ reduced form, GIVEN `PNTErrorTerm` (the certificate is supplied by `certS53`/`certD53`).
  The unconditional converse is not available: it would need `PNTErrorTerm` (the de la Vallée Poussin error term),
  which is not proved in the tree.
-/
import ZetaShell.Challenge
import ZetaShell.Cert.R4_CertS53
import ZetaShell.Frame.B1_CountBridge
import ZetaShell.Top.T1_HeadlineNoP

noncomputable section

namespace ZetaShell

/-- **Reduced headline, family `1 < q ≤ Q`** (statement of record): `shell_S53_qle` without `hP` and `hcert`. -/
theorem shell_S53_qle_reduced (hD : ZeroDensityInput) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertS53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * famN (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₀, c, hc, h⟩ := shell_S53_qle_tree_noP hD r ε θ hr hε hθ hθ'
  refine ⟨Q₀, c, hc, fun Qn hQn => ?_⟩
  rw [famN_qle_eq, famN0s_qle_eq, twin_eq]
  exact h Qn hQn

/-- **Reduced headline, dyadic family `Q/2 < q ≤ Q`** (statement of record): `shell_S53_dyadic` without `hP` and
`hcert`. -/
theorem shell_S53_dyadic_reduced (hD : ZeroDensityInput) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertD53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * famN (modDyadic Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modDyadic Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
  sorry

/-- **Reduced bounded-height headline, family `1 < q ≤ Q`** (statement of record): `shell_S53_bounded` without
`hP` and `hcert`. -/
theorem shell_S53_bounded_reduced (hD : ZeroDensityInput) (W : ℝ → ℝ) (σ : ℝ)
    (hW : BandLimitedWeight W σ) (Tstar ε θ : ℝ) (hT : 0 < Tstar) (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) → ∀ T₀ : ℝ, Tstar ≤ T₀ →
      T₀ ≤ Real.log (Qn : ℝ) ^ (1 + ε) →
      wSummable (modQle Qn) (fun γ => W (γ / T₀) ^ 2) ∧
      (((PcertS53 : ℚ) : ℝ) - c * (Real.log (Real.log (Qn : ℝ)) / Real.sqrt (T₀ * Real.log (Qn : ℝ))
          + Real.log (Qn : ℝ) ^ (-θ)))
          * (∑ q ∈ modQle Qn, ∑ χ ∈ primChars q, wSum q χ (fun γ => W (γ / T₀) ^ 2))
        ≤ ∑ q ∈ modQle Qn, ∑ χ ∈ primChars q, wSumSC q χ (fun γ => W (γ / T₀) ^ 2) := by
  sorry

/-- **Reduced bounded-height headline, dyadic family** (statement of record): `shell_S53_bounded_dyadic` without
`hP` and `hcert`. -/
theorem shell_S53_bounded_dyadic_reduced (hD : ZeroDensityInput) (W : ℝ → ℝ) (σ : ℝ)
    (hW : BandLimitedWeight W σ) (Tstar ε θ : ℝ) (hT : 0 < Tstar) (hε : 0 < ε) (hθ : 0 < θ)
    (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) → ∀ T₀ : ℝ, Tstar ≤ T₀ →
      T₀ ≤ Real.log (Qn : ℝ) ^ (1 + ε) →
      wSummable (modDyadic Qn) (fun γ => W (γ / T₀) ^ 2) ∧
      (((PcertD53 : ℚ) : ℝ) - c * (Real.log (Real.log (Qn : ℝ)) / Real.sqrt (T₀ * Real.log (Qn : ℝ))
          + Real.log (Qn : ℝ) ^ (-θ)))
          * (∑ q ∈ modDyadic Qn, ∑ χ ∈ primChars q, wSum q χ (fun γ => W (γ / T₀) ^ 2))
        ≤ ∑ q ∈ modDyadic Qn, ∑ χ ∈ primChars q, wSumSC q χ (fun γ => W (γ / T₀) ^ 2) := by
  sorry

namespace Top

/-! ### Reduced ⇒ architect's form (the two dropped hypotheses are simply not used) -/

theorem shell_S53_qle_of_reduced :
    type_of% @shell_S53_qle_reduced → type_of% @shell_S53_qle :=
  fun h hD _ _ => h hD

theorem shell_S53_dyadic_of_reduced :
    type_of% @shell_S53_dyadic_reduced → type_of% @shell_S53_dyadic :=
  fun h hD _ _ => h hD

theorem shell_S53_bounded_of_reduced :
    type_of% @shell_S53_bounded_reduced → type_of% @shell_S53_bounded :=
  fun h hD _ _ => h hD

theorem shell_S53_bounded_dyadic_of_reduced :
    type_of% @shell_S53_bounded_dyadic_reduced → type_of% @shell_S53_bounded_dyadic :=
  fun h hD _ _ => h hD

/-! ### Architect's form ⇒ reduced form, given `PNTErrorTerm` (the certificate is `certS53` / `certD53`).
The converse without `PNTErrorTerm` is not available: `PNTErrorTerm` (strong form) is not proved in the tree. -/

theorem shell_S53_qle_reduced_of_arch :
    type_of% @shell_S53_qle → PNTErrorTerm → type_of% @shell_S53_qle_reduced :=
  fun h hP hD => h hD hP certS53

theorem shell_S53_dyadic_reduced_of_arch :
    type_of% @shell_S53_dyadic → PNTErrorTerm → type_of% @shell_S53_dyadic_reduced :=
  fun h hP hD => h hD hP certD53

theorem shell_S53_bounded_reduced_of_arch :
    type_of% @shell_S53_bounded → PNTErrorTerm → type_of% @shell_S53_bounded_reduced :=
  fun h hP hD => h hD hP certS53

theorem shell_S53_bounded_dyadic_reduced_of_arch :
    type_of% @shell_S53_bounded_dyadic → PNTErrorTerm → type_of% @shell_S53_bounded_dyadic_reduced :=
  fun h hP hD => h hD hP certD53

end Top

end ZetaShell
