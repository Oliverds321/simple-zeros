/-
Node F1c-1 (L7_3, round 4): **the master inequality at the Shell design, out-zone left open.** ZetaQ's
`InZone.famPP_total_le` stops at the pointwise sieve on the out-zone; here the out-zone half is kept as the family
integral `∫_{inZoneᶜ} g·F` that Theorem K bounds:
  `Σ_χ M(P_Xχ, P_Xχ) ≤ inCrossRHS(e) + 2∫_{inZoneᶜ} g·F`   (`F = Σ_χ |A_χ|²`, `FfamZ`).
Proof: `famPP_total_le`'s steps (1)–(4) verbatim (Parseval `lemma41_parseval_diag`, `zone_expansion`, the B-mirror
`integral_B_eq_A`, the zone split `integral_add_compl`), `inFormF_full_le` on the in-zone, `cross_integral_family`
on the cross term, and the swap of the family sum with the out-zone integral (as in L7_3's K8a-1). Only design facts
used: `P.Valid`, `8w ≤ L` (`SideCondWrange`, a conjunct of `ShellDesignM`), `P.Q = Qn`, and `s₀ ≥ 0` (eventually:
`3 log log Q ≤ log Q`). No bandwidth enters. Difficulty M.
-/
import ZetaShell.ShellK.LF_Defs

noncomputable section
open Filter MeasureTheory Set

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaQ.Payoff

/-- `s₀ = (1 − δ′) log Q ≥ 0` along the Shell design, eventually. -/
theorem s0_nonneg_eventually (r ε : ℝ) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P → 0 ≤ P.s0 := by
  filter_upwards [tendsto_log_nat_atTop.eventually (FrobAssembly.loglog_le_eventually 3 (by norm_num)),
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with Qn h3 h1
  intro P hdes
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hL0 : 0 < Real.log (Qn : ℝ) := by linarith
  have e : P.s0 = Real.log (Qn : ℝ) - 3 * Real.log (Real.log (Qn : ℝ)) := by
    unfold ParamsQ.s0 ParamsQ.deltaPrime
    rw [hQ]
    field_simp
  rw [e]
  linarith

/-- **F1c-1.** -/
theorem shell_master (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P → ∀ e : ℝ, 0 < e →
      familySum Family.qle Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
        ≤ inCrossRHS Qn P e + 2 * (∫ s in (inZone P)ᶜ, P.gQ s * FfamZ P Qn s) := by
  filter_upwards [s0_nonneg_eventually r ε] with Qn hs0'
  intro P hdes e he
  have hP : P.Valid := hdes.1
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hs0 : 0 ≤ P.s0 := hs0' P hdes
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQn : Qn ≤ ⌊P.Q⌋₊ := by rw [hQ, Nat.floor_natCast]
  have hLS := largeSieveFamily_holds
  have hphi := phiQ_sq_integrable P hP hw
  have hUm : MeasurableSet (inZone P) := measurableSet_inZone P
  -- (1)–(4): famPP_total_le's steps, verbatim
  have h1 : familySum Family.qle Qn (fun _ χ => Mform P (PXchi P χ) (PXchi P χ))
      = familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2) := by
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact lemma41_parseval_diag P (PXchi P χ) hphi (FrobAssembly.PXchi_integrableOn P χ)
      (FrobAssembly.PXchi_sq_integrableOn P χ)
  have h2 : familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Fwin P (PXchi P χ) s‖ ^ 2)
      = familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2)
        + familySum Family.qle Qn (fun _ χ => 2 * ∫ s : ℝ,
            P.gQ s * (Achi P χ s * (starRingEnd ℂ) (Bchi P χ s)).re) := by
    rw [← familySum_add', ← familySum_add']
    refine familySum_congr_prim Family.qle Qn fun q χ hχ => ?_
    have := zone_expansion P hP hw χ hχ Set.univ
    simpa only [MeasureTheory.setIntegral_univ] using this
  have h3 : familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Bchi P χ s‖ ^ 2)
      = familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2) := by
    unfold familySum
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => integral_B_eq_A P χ
  have h4 : familySum Family.qle Qn (fun _ χ => ∫ s : ℝ, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = familySum Family.qle Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
        + familySum Family.qle Qn (fun _ χ => ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2) := by
    rw [← familySum_add']
    unfold familySum
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    exact (MeasureTheory.integral_add_compl hUm
      (gQ_mul_integrable P hP hw ((Achi_continuous P χ).norm.pow 2))).symm
  have hin : familySum Family.qle Qn (fun _ χ => ∫ s in inZone P, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = inFormF Family.qle Qn P (acoefS P) := rfl
  have hfull := inFormF_full_le Family.qle Qn P hP hw hLS hQn hs0 he
  have hcross := (abs_le.mp (cross_integral_family Family.qle Qn P hP hw hLS hQn Set.univ
    MeasurableSet.univ)).2
  simp only [MeasureTheory.setIntegral_univ] at hcross
  -- (5) the out-zone half: swap the family sum and the integral
  have hAint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      Integrable (fun s => P.gQ s * ‖Achi P χ s‖ ^ 2) :=
    fun q χ => gQ_mul_integrable P hP hw ((Achi_continuous P χ).norm.pow 2)
  have hswap : familySum Family.qle Qn (fun _ χ => ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2)
      = ∫ s in (inZone P)ᶜ, P.gQ s * FfamZ P Qn s := by
    have hin' : ∀ q ∈ Family.qle.moduli Qn,
        ∫ s in (inZone P)ᶜ, ∑ χ ∈ Family.qle.chars q, P.gQ s * ‖Achi P χ s‖ ^ 2
          = ∑ χ ∈ Family.qle.chars q, ∫ s in (inZone P)ᶜ, P.gQ s * ‖Achi P χ s‖ ^ 2 :=
      fun q _ => integral_finset_sum _ (fun χ _ => (hAint q χ).integrableOn)
    have hout' : ∫ s in (inZone P)ᶜ, ∑ q ∈ Family.qle.moduli Qn, ∑ χ ∈ Family.qle.chars q,
          P.gQ s * ‖Achi P χ s‖ ^ 2
        = ∑ q ∈ Family.qle.moduli Qn, ∫ s in (inZone P)ᶜ, ∑ χ ∈ Family.qle.chars q,
          P.gQ s * ‖Achi P χ s‖ ^ 2 :=
      integral_finset_sum _ (fun q _ =>
        (integrable_finset_sum _ (fun χ _ => hAint q χ)).integrableOn)
    have hfun : (fun s => P.gQ s * FfamZ P Qn s)
        = fun s => ∑ q ∈ Family.qle.moduli Qn, ∑ χ ∈ Family.qle.chars q, P.gQ s * ‖Achi P χ s‖ ^ 2 := by
      funext s; unfold FfamZ familySum; simp [Finset.mul_sum]
    rw [hfun, hout']
    unfold familySum
    exact (Finset.sum_congr rfl hin').symm
  unfold inCrossRHS
  rw [h1, h2, h3, h4, hin, hswap]
  linarith

end F1c
end ShellK
end ZetaShell
