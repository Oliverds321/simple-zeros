/-
Nodes F1c-8 … F1c-11 (L7_3, round 4): the certificate with a strict slack, the zone edge, the ramp constant and the
rate, each a small eventual fact at the Shell design.
* F1c-8 `cert_strict`: `B_{α′}(v_{S53}) ≤ 2 − P_cert − 3·10⁻¹¹` at `C = π⁴/18`. From the certificate's own rounding
  slack (exact `2 − B = 0.90591379273786…` against `P_cert = 0.9059137927`): a second kernel evaluation of L7_5's
  `CertQ.BS53` (`BS53_le_strict`), L7_5's `Bshell_eq_shellBq`, R1 `π⁴/18 ≤ C⁺` (`Real.pi_lt_d20`) and R2 (monotonicity
  in `C`, from `kernel_split` at `a = 1`). The Frobenius row's errors are all `o(1)`, so this slack absorbs them; no
  rate is needed from the in-zone rows.
* F1c-9 `zone_small`: `0 ≤ a ≤ 1` and `(C − 1)·Jzone(a)(v_design) ≤ η` eventually, `a = zoneFactor P`. Round 5: no
  longer uses C2; the crude bound `ψ_{v_p} ≤ 4/(3λ)` suffices, with the ramp link and `1 − a = O(log log Q/log Q)`.
* F1c-10 `ramp_small`: `1 ≤ c` and `c² ≤ 1 + η` eventually (`HFrob.one_le_c`, `c_le`, A8's `w = 1`, `ℒ ≥ log Q`).
* F1c-11 `rate_small`: `0 ≤ (log Q)^{−θ} ≤ η` eventually.
-/
import ZetaShell.ShellK.LF_Kernel
import ZetaShell.Design.SD_A8_Scales
import ZetaShell.Cert.R4_CertS53

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaQ.Payoff ZetaQ.FrobAssembly

/-- The certificate's own rounding slack, made explicit: `B(v_{S53}) ≤ 2 − 0.90591379273` at `C⁺` (exact value
`2 − 0.90591379273786…`; `PcertS53 = 0.9059137927`). Kernel evaluation of L7_5's `CertQ.BS53`, as `CertQ.BS53_le`. -/
theorem BS53_le_strict : CertQ.BS53 ≤ 2 - 90591379273 / 100000000000 := by decide +kernel

/-- R1: `π⁴/18 ≤ C⁺ = 5.41161617` (`Real.pi_lt_d20`). -/
theorem Cfam_le_Cplus : Cfam ≤ 541161617 / 100000000 := by
  unfold Cfam
  have h := Real.pi_lt_d20
  have h0 := Real.pi_pos
  have h4 : Real.pi ^ 4 ≤ (3.14159265358979323847 : ℝ) ^ 4 := pow_le_pow_left₀ h0.le h.le 4
  norm_num at h4
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **F1c-8.** `B_{α′}(v_{S53}) ≤ 2 − P_cert − 3·10⁻¹¹` at `C = π⁴/18`: R2 (monotonicity in `C`, from `kernel_split` at
`a = 1` for `C⁺` and `C`), R1, L7_5's `Bshell_eq_shellBq` and `BS53_le_strict`. -/
theorem cert_strict :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ Bshell 1 (2497 / 1500) Cfam S53L75.v ≤ 2 - ((PcertS53 : ℚ) : ℝ) - δ₀ := by
  refine ⟨3 / 100000000000, by norm_num, ?_⟩
  have hL := S53L75_L75
  have hl : (0 : ℝ) < (S53L75.lam : ℝ) := by norm_num [S53L75]
  have hm := mass_pos_of_L75 S53L75 hl hL
  have hB := Bshell_eq_shellBq S53L75 (by norm_num [S53L75]) (by norm_num [S53L75]) (by norm_num [S53L75]) hm
  rw [shellBq_S53] at hB
  have hk : ((CertQ.BS53 : ℚ) : ℝ) ≤ ((2 - 90591379273 / 100000000000 : ℚ) : ℝ) := by
    exact_mod_cast BS53_le_strict
  have e1 : ((S53L75.level : ℚ) : ℝ) = 1 := by norm_num [S53L75]
  have e2 : ((S53L75.alphaP : ℚ) : ℝ) = 2497 / 1500 := by norm_num [S53L75]
  have e3 : ((S53L75.Cplus : ℚ) : ℝ) = 541161617 / 100000000 := by norm_num [S53L75]
  rw [e1, e2, e3] at hB
  have hA := admissible_of_L75 S53L75 hl hL
  have hadm : Admissible ((S53L75.lam : ℚ) : ℝ) S53L75.v := ⟨hA.nonneg, hA.integrable, hA.mass, hA.supp⟩
  have k1 := kernel_split hadm Cfam (2497 / 1500) 1 (by norm_num) zero_le_one le_rfl
  have k2 := kernel_split hadm (541161617 / 100000000) (2497 / 1500) 1 (by norm_num) zero_le_one le_rfl
  unfold KoutShell at k1 k2
  have htop : 0 ≤ ∫ α in {α : ℝ | 2497 / 1500 < |α|}, psi S53L75.v α :=
    setIntegral_nonneg (measurableSet_lt measurable_const continuous_abs.measurable)
      (fun α _ => psi_nonneg hadm α)
  have hC := Cfam_le_Cplus
  have hprod := mul_nonneg (sub_nonneg.mpr hC) htop
  have hPc : ((PcertS53 : ℚ) : ℝ) = 9059137927 / 10000000000 := by norm_num [PcertS53]
  have hk' : ((2 - 90591379273 / 100000000000 : ℚ) : ℝ) = 2 - 90591379273 / 100000000000 := by norm_num
  rw [hk'] at hk
  rw [hPc]
  linarith

/-- **F1c-10.** -/
theorem ramp_small (r ε : ℝ) (hr : 3 ≤ r) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      1 ≤ cRampS P ∧ cRampS P ^ 2 ≤ 1 + η := by
  filter_upwards [tendsto_log_nat_atTop.eventually (eventually_ge_atTop (13 / η + 1)),
    eventually_ge_atTop 1] with Qn hlog hQn1
  intro P hdes
  have hP : P.Valid := hdes.1
  have hS : (1 : ℝ) ≤ ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  obtain ⟨-, hLL, -, hw1⟩ := Design.scales_of_shellDesignM hS hdes hr hQn1
  have hlam : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
  have hlam1 : 1 ≤ P.lam := by rw [hlam]; exact hS
  have h13 : 13 / η ≤ P.LL := by linarith
  have hLL1 : 1 ≤ P.LL := by
    have : 0 ≤ 13 / η := by positivity
    linarith
  have hw : P.w = 1 := hw1 hLL1
  have hc1 : 1 ≤ cRampS P := HFrob.one_le_c hP
  have hcle : cRampS P ≤ 1 + 8 / 3 * (P.w / P.LL) := HFrob.c_le hP hlam1
  rw [hw] at hcle
  have hLL0 : 0 < P.LL := by linarith
  have hinv : 1 / P.LL ≤ η / 13 := by
    rw [div_le_div_iff₀ hLL0 (by norm_num)]
    have := (div_le_iff₀ hη).mp h13
    linarith
  have hinv0 : 0 ≤ 1 / P.LL := by positivity
  have hinv1 : 1 / P.LL ≤ 1 := by rw [div_le_one hLL0]; exact hLL1
  refine ⟨hc1, ?_⟩
  have hc2 : cRampS P ≤ 1 + 8 / 3 * (1 / P.LL) := hcle
  have hsq : cRampS P ^ 2 ≤ (1 + 8 / 3 * (1 / P.LL)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hc2 2
  nlinarith

/-- `1 − zoneFactor P ≤ θ` eventually along the Shell design: `FrobAssembly.one_sub_zoneFactor_le_eventually`'s
proof verbatim, with `design_basic`/`Q_of_design`/`T_of_design` replaced by the Shell design's conjuncts and A8. -/
theorem one_sub_zoneFactor_shell (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      0 ≤ zoneFactor P ∧ 0 ≤ 1 - zoneFactor P ∧ 1 - zoneFactor P ≤ θ := by
  have hre : (0:ℝ) < r + ε := by linarith
  have h1 : ∀ᶠ x : ℝ in atTop, (2 * (r + ε) / θ) * Real.log x ≤ x :=
    loglog_le_eventually _ (by positivity)
  have h2 : ∀ᶠ x : ℝ in atTop, (6 / θ) * Real.log x ≤ x := loglog_le_eventually _ (by positivity)
  have h3 : ∀ᶠ x : ℝ in atTop, (3:ℝ) * Real.log x ≤ x := loglog_le_eventually 3 (by norm_num)
  filter_upwards [tendsto_log_nat_atTop.eventually h1, tendsto_log_nat_atTop.eventually h2,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (3:ℝ)), eventually_ge_atTop 1,
    tendsto_log_nat_atTop.eventually h3]
    with Qn hx1 hx2 hx3 hQn1 hx4
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hS : (1 : ℝ) ≤ ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  obtain ⟨hT, hLLge, -, -⟩ := Design.scales_of_shellDesignM hS hdes hr hQn1
  set x := Real.log (Qn : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hLL0 : 0 < P.LL := by linarith
  have hδ : P.deltaPrime = 3 * Real.log x / x := by
    unfold ParamsQ.deltaPrime; rw [hQ]
  have hδ0 : 0 ≤ P.deltaPrime := by
    rw [hδ]
    have : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    positivity
  have hδθ : P.deltaPrime ≤ θ / 2 := by
    rw [hδ, div_le_iff₀ hx0]
    have := hx2; rw [div_mul_eq_mul_div, div_le_iff₀ hθ] at this
    linarith
  have hl0 := l_nonneg hP
  have hl : Zeta23.l P.T ≤ (r + ε) * Real.log x := by
    unfold Zeta23.l
    rw [hT]
    have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc Real.log (x ^ (r + ε) / (2 * Real.pi)) ≤ Real.log (x ^ (r + ε)) :=
          Real.log_le_log (by positivity) (by
            rw [div_le_iff₀ (by positivity)]
            have : 0 ≤ x ^ (r + ε) := by positivity
            nlinarith)
      _ = (r + ε) * Real.log x := Real.log_rpow hx0 _
  have hlL : Zeta23.l P.T / P.LL ≤ θ / 2 := by
    rw [div_le_iff₀ hLL0]
    have := hx1; rw [div_mul_eq_mul_div, div_le_iff₀ hθ] at this
    calc Zeta23.l P.T ≤ (r + ε) * Real.log x := hl
      _ ≤ θ / 2 * x := by linarith
      _ ≤ θ / 2 * P.LL := by gcongr
  have hlL0 : 0 ≤ Zeta23.l P.T / P.LL := by positivity
  have hδ1 : P.deltaPrime ≤ 1 := by
    rw [hδ, div_le_one hx0]; linarith
  have hlL1 : Zeta23.l P.T / P.LL ≤ 1 := by
    rw [div_le_one hLL0]; exact l_le_LL hP
  unfold zoneFactor
  refine ⟨?_, ?_, ?_⟩
  · exact mul_nonneg (by linarith) (by linarith)
  · nlinarith
  · nlinarith

/-- `ψ_{v_profile}(α) ≤ 4/(3λ)` for every `α` (`v_profile ≤ 4/(3λ)` pointwise, `RampLink.vProfile_le_four_div`, and
`∫ v_profile = 1`). The crude bound that replaces C2 (round 5). -/
theorem psi_vProfile_le {P : ParamsQ} (hP : P.Valid) (α : ℝ) : psi (vProfile P) α ≤ 4 / (3 * P.lam) := by
  have hadm := vProfile_admissible hP
  have hint1 : Integrable (fun t => vProfile P t * vProfile P (t - α)) := by
    refine Integrable.bdd_mul (c := 1 / profMass P) ((vProfile_integrable P).comp_sub_right α)
      (vProfile_integrable P).aestronglyMeasurable (ae_of_all _ (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (vProfile_nonneg hP t)]
    exact vProfile_le hP t
  unfold psi
  calc ∫ t, vProfile P t * vProfile P (t - α)
      ≤ ∫ t, vProfile P t * (4 / (3 * P.lam)) :=
        integral_mono hint1 (hadm.integrable.mul_const _)
          (fun t => mul_le_mul_of_nonneg_left (vProfile_le_four_div hP (t - α)) (vProfile_nonneg hP t))
    _ = (∫ t, vProfile P t) * (4 / (3 * P.lam)) := integral_mul_const _ _
    _ = 4 / (3 * P.lam) := by rw [hadm.mass, one_mul]

/-- **F1c-9.** The zone edge, WITHOUT C2 (round 5): ZetaQ's generic `zone_compare_of_lipschitz` with the crude data
`ψ_{v_p} ≤ 4/3` on `[0, 1]` (`psi_vProfile_le`, `λ ≥ 1`), Lipschitz constant `0` and slope `s₀ = 2(C−1)·4/3`, then
the ramp link `HFrob.Jzone_vDesign_le`, `c² ≤ 2` and `1 − a → 0`. The certificate's slack needs only
`(C − 1)·Jzone(a) → 0`, so no margin against a zone slope is needed. -/
theorem zone_small (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      0 ≤ zoneFactor P ∧ zoneFactor P ≤ 1 ∧ (Cfam - 1) * Jzone (zoneFactor P) (vDesign P) ≤ η := by
  have hC1 : (1 : ℝ) ≤ Cfam := by
    unfold Cfam
    have h3 := Real.pi_gt_three
    have : (3 : ℝ) ^ 4 ≤ Real.pi ^ 4 := pow_le_pow_left₀ (by norm_num) h3.le 4
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hC0 : 0 ≤ Cfam - 1 := by linarith
  set s₀ : ℝ := 2 * (Cfam - 1) * (4 / 3) with hs₀def
  have hs₀ : 0 ≤ s₀ := by rw [hs₀def]; positivity
  set θ : ℝ := η / (2 * s₀ + 1) with hθdef
  have hθ : 0 < θ := div_pos hη (by linarith)
  filter_upwards [one_sub_zoneFactor_shell r ε hr hε θ hθ, ramp_small r ε hr 1 one_pos] with Qn hz hR
  intro P hdes
  have hP : P.Valid := hdes.1
  obtain ⟨ha0, h1a0, h1aθ⟩ := hz P hdes
  obtain ⟨hc1, hc2⟩ := hR P hdes
  have ha1 : zoneFactor P ≤ 1 := by linarith
  refine ⟨ha0, ha1, ?_⟩
  have hv := vProfile_admissible hP
  have hlam1 : 1 ≤ P.lam := by rw [hdes.2.2.2.1]; norm_num [S53L75]
  have hlip : ∀ α, zoneFactor P ≤ α → α ≤ 1 → psi (vProfile P) α ≤ 4 / 3 + 0 * (1 - α) := by
    intro α _ _
    have h := psi_vProfile_le hP α
    have h' : 4 / (3 * P.lam) ≤ 4 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hmar : 2 * (Cfam - 1) * (4 / 3) + (Cfam - 1) * 0 * (1 - zoneFactor P) ≤ s₀ := by
    have : (Cfam - 1) * 0 * (1 - zoneFactor P) = 0 := by ring
    linarith
  have hcmp := zone_compare_of_lipschitz hv ha0 ha1 le_rfl hC1 hlip hmar
  have hJd := HFrob.Jzone_vDesign_le hP (zoneFactor P)
  have hs0 : 0 ≤ s₀ * (1 - zoneFactor P) := mul_nonneg hs₀ h1a0
  have hcs0 : 0 ≤ cRampS P ^ 2 := sq_nonneg _
  have step1 : (Cfam - 1) * Jzone (zoneFactor P) (vDesign P)
      ≤ cRampS P ^ 2 * ((Cfam - 1) * Jzone (zoneFactor P) (vProfile P)) := by
    have := mul_le_mul_of_nonneg_left hJd hC0
    unfold cRampS
    linarith
  have step2 : cRampS P ^ 2 * ((Cfam - 1) * Jzone (zoneFactor P) (vProfile P))
      ≤ cRampS P ^ 2 * (s₀ * (1 - zoneFactor P)) := mul_le_mul_of_nonneg_left hcmp hcs0
  have step3 : cRampS P ^ 2 * (s₀ * (1 - zoneFactor P)) ≤ 2 * (s₀ * (1 - zoneFactor P)) := by
    have : cRampS P ^ 2 ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hs0
  have step4 : 2 * (s₀ * (1 - zoneFactor P)) ≤ η := by
    have h1 : 2 * s₀ * (1 - zoneFactor P) ≤ 2 * s₀ * θ :=
      mul_le_mul_of_nonneg_left h1aθ (by positivity)
    have h2 : 2 * s₀ * θ ≤ η := by
      rw [hθdef, mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  linarith

/-- **F1c-11.** -/
theorem rate_small (θ : ℝ) (hθ : 0 < θ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Qn : ℕ in atTop, 0 ≤ Real.log (Qn : ℝ) ^ (-θ) ∧ Real.log (Qn : ℝ) ^ (-θ) ≤ η := by
  have h := (tendsto_rpow_neg_atTop hθ).comp tendsto_log_nat_atTop
  filter_upwards [h.eventually (eventually_le_nhds hη),
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with Qn h1 h2
  exact ⟨Real.rpow_nonneg h2 _, h1⟩

end F1c
end ShellK
end ZetaShell
