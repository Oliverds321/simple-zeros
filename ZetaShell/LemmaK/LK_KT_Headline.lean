/-
Node KT (L7_3): THEOREM 1′ (thm:one-prime) in the exact form of ZetaQ's `JoinProved.theorem_one_generic_proved'`
(same counts `NfamCount`/`N0sFamCount`, family `Family.qle`, `Twin`, quantifiers `∃ Q₀ c, 0 < c ∧ ∀ Qn ≥ Q₀`, rate
`c·log log Q/log Q`), no hypothesis beyond `3 ≤ r`, `0 < ε`:
* `theorem_one_prime`         `P = 0.7237` (the draft's `P_K`), degree-8 killed profile at ZetaQ's `λ* = 1.2507321515`;
* `theorem_one_prime_design`  `P = 0.7235`, ZetaQ's own design profile, killed kernel (no new design data).
Both from the frames (K9) and the assembly (KA). PROVED here modulo K9.
The draft's "0.72375" is NOT claimed: at `λ ≤ λ*` a degree-8 profile gives 0.72374950 < 0.72375 and the draft's
in-cap profile (iv-5/4) gives 0.72374711; 0.72375 needs degree 10 at `λ*` (0.72375026, slack 2.6·10⁻⁷) or
`λ = 32/25` (0.72375738, outside ZetaQ's pins). See the report.
-/
import ZetaShell.Skeleton.LK_K9_Frame
import ZetaShell.LemmaK.LK_KA_Assembly

noncomputable section
open Filter Topology

namespace ZetaShell
namespace LemmaK

theorem rateLL_tendsto : Tendsto rateLL atTop (𝓝 0) := by
  have h1 : Tendsto (fun Qn : ℕ => Real.log (Qn : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact h2.comp h1

theorem rateLL_nonneg : ∀ᶠ Qn : ℕ in atTop, 0 ≤ rateLL Qn := by
  filter_upwards [eventually_ge_atTop 3] with Qn hQn
  have h3 : (3 : ℝ) ≤ Qn := by exact_mod_cast hQn
  have hl : 1 ≤ Real.log (Qn : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h3
  unfold rateLL
  exact div_nonneg (Real.log_nonneg hl) (by linarith)

/-- The generic step: a killed frame at `κ = 2 − P` and rate `log log Q/log Q` gives ZetaQ's headline shape. -/
theorem headline_of_frame (r ε : ℝ) (S : KProfile) (Pc : ℚ)
    (Fr : KFrame ZetaQ.Family.qle r ε S (2 - (Pc : ℝ)) rateLL) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ((Pc : ℝ) - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * ZetaQ.NfamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₀, c, hc, h⟩ := k_assembly _ r ε S _ rateLL Fr
  refine ⟨Q₀, c, hc, fun Qn hQn => ?_⟩
  have := h Qn hQn
  simp only [rateLL] at this
  convert this using 2
  ring

/-- **THEOREM 1′ (killed kernel), `P = 0.7237`.** -/
theorem theorem_one_prime (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertK : ℚ) : ℝ) - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * ZetaQ.NfamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  obtain ⟨Fr⟩ := killed_frame_lamStar8 r ε hr hε
  exact headline_of_frame r ε _ _ Fr

/-- **THEOREM 1′ at ZetaQ's own design profile, `P = 0.7235`.** -/
theorem theorem_one_prime_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertKD : ℚ) : ℝ) - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * ZetaQ.NfamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
  obtain ⟨Fr⟩ := killed_frame_design r ε hr hε
  exact headline_of_frame r ε _ _ Fr

end LemmaK
end ZetaShell
