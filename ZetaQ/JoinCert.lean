/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/JoinCert.lean — **the CERTIFIED-CONSTANT JOIN**: the eight-clause
assembly, the rate step, Theorem 1 and Corollary 2 at `P_cert` instead of the ten-digit `P`, written
as NEW theorems beside the frozen `assembly_at_lamStar` / `payoff_rate_of_assembly` /
`theorem_one_generic` / `corollary_two_dyadic` (none of which is restated or touched).

Why a new constant: with the FIXED degree-6 profile the §11 certificate gives
`B(v_profile) = 1.27874639 > F.kappaC = 2 − 0.7212835668 = 1.2787164`, and `rowR2 → 0`, so the frozen
`frobenius_row` with `Family.payoff = Pconst` is not provable asymptotically. The
Lean headline must ship `κ_cert := 2 − P_cert`, `P_cert = 0.7212` (`qle`) / `0.7098` (`dyadic`) —
`ZetaQ.Payoff.Pcert_qQ_smooth` / `Pcert_dyad_smooth` of `ZetaQ/PayoffSmooth.lean`.

Which frozen clauses needed `κ_cert` (recorded per the task):
  * clause 3  `frobSqGhatFam ≤ (κ + r₂)·𝒩`            — the INPUT `hfrob`, now at `κ_cert`;
  * clause 7  `4r₁ + r₂ + 3r₃ + 4r₄ + 2r₅√(κ + r₂) + r₅² ≤ budgetTotal` — the bracket, through `hpair`
    (§7's absorbed pair block carries `√(κ + r₂)`; `pair_absorbed_of_theta_small`,
    `tail_clauses_at_design`, `tail_clauses_at_design_of_closing_A0`, `hregime_eventually`,
    `tail_clauses_eventually` are re-proved verbatim at `κ_cert` below — NOTHING breaks, because the
    only fact about `κ` those proofs use is `κ ≤ 2` (`hregime_eventually` bounds `√(κ + r₂) ≤ 9`
    from `κ ≤ 2`, `r₂ ≤ 79`); the `√(κ_cert + r₂) ≥ √(κ_C + r₂)` direction is therefore never an
    issue — the margin is the whole `ℒ^{(7−r−ε)/2}·log ℒ → ∞` of `rhs_lower_design`, not `3·10⁻⁵`);
  * clause 8  `(2 − κ − budgetTotal)·𝒩 ≤ N0sFamQ`    — Prop 3.1, which is generic in `κ`
    (`prop_3_1_pair_moment_certificate {κC}`), so only the display changes.
  Clauses 1, 2, 4, 5, 6 do not mention `κ`.

Hypotheses that stay NAMED (the tree does not yet discharge them):
  * `hsharp` — `SharpZeroDensity`, the paper's declared assumption;
  * `hfrob`  — the Frobenius row at `κ_cert`, eventually along the design
    (`FrobAssembly.frobenius_sieve_eventually` reaches only `ψ(0) + C·(K0+K1)` ≈ `B_{C,C}`, and at
    the time of writing the in-zone §5 evaluation was absent), so it is taken ABSTRACTLY, not
    routed through `hsep`;
  * `hre : r + ε ≤ 7` — the regime of `HPre.hregime_eventually` (the margin-m design that
    restores every `r ≥ 3` is quantified in `HPre_REPORT.md` but not in the tree, so no variant is
    stated here);
  * `hrvm` (dyadic only) — `FamRvMLower Family.dyadic` is NOT proved along the design
    (`famRvMLower_of_design` is `qle`-only), so `corollary_two_dyadic_cert` names it and
    `theorem_one_generic_cert` discharges it.
Everything else is the tree's: `exists_designOfRecord` (the design point), `trace_row_eventually_aux`
(`r₁`), `buffer_row_sharp` (`r₃`), `pair_rows` (`r₄`, `r₅`), `EFChi.localCountChi_uniform` (`hloc`,
`A₀`), `gevreyProfile_rhoTwoQ` + `DesignOfRecord`'s `P.ϱ = rhoTwo` (`hϱ`), `famRvMLower_of_design`
(`qle`'s `hrvm`), `HPre.theta0Fam_le_of_design_A0` / `rhs_lower_design` / `rowR2_le_design` (§7),
`EFChi.certificate_display_fam_of_bridge` + `prop_3_1_pair_moment_certificate` (clause 8),
`budgetTotal_isBigO_of_design` (the rate).

Note on the rate step: `payoff_rate_of_assembly`'s proof consumes the PRIVATE
`D0_le_of_design` / `budgetTotal_le_of_regime` of `Budget.lean`, so it cannot be mirrored from outside
the file; `payoff_rate_of_assembly_cert` below instead builds a real-variable design map by choice
(the assembly's own points at the naturals, `exists_designOfRecord`'s elsewhere) and consumes the
PUBLIC `budgetTotal_isBigO_of_design`. The conclusion is the same shape; the rate constant is
existential (`|c0| + 1`) rather than the explicit `20(r+ε) + 120200`.

Rule 17: nothing here bounds λ by 1, relates `X` to `T`, or pins `D₀`; every hypothesis is at the
design of record. Axioms: `[propext, Classical.choice, Quot.sound]` expected throughout (nothing
below routes through `trace_row`/`frobenius_row`/`assembly_at_lamStar`/the Sieve sorry).
-/
import ZetaQ.HPre
import ZetaQ.PayoffSmooth
-- Corollary 3's two smooth certificates (`Pcert_even_dyad_smooth`, `Pcert_evenQ_smooth`) live
-- here; the import is acyclic (`Cor3Smooth` sits on the `PayoffSmooth → DesignProfile` chain
-- and knows nothing of `HPre` / `Budget`).
import ZetaQ.Cor3Smooth
-- `trace_row_eventually_aux` (used in `assembly_eventually_cert` below) lives at the foot of
-- `ZetaQ/FrobRow9.lean`, not in `ZetaQ/Budget.lean`: its parity branch needs
-- `FamRows.abs_trGhatFam_sub_muPartChars_le`, and `FrobRow9` imports `Budget`. The import is
-- acyclic (`FrobRow9` imports `Budget` and nothing else).
import ZetaQ.FrobRow9

noncomputable section

open Filter Asymptotics

namespace ZetaQ

/-! ## 1. The certified constants -/

/-- `P_cert` by family: `0.7212` (`qle`, `Pcert_qQ_smooth`) / `0.7098` (`dyadic`,
`Pcert_dyad_smooth`) — the four-digit constants the smooth degree-6 profile certificates deliver. -/
def Family.payoffCert : Family → ℝ
  | Family.qle => ((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
  | Family.dyadic => ((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
  | Family.evenQle => ((Payoff.Pcert_evenQ_smooth : ℚ) : ℝ)
  | Family.oddQle => ((Payoff.Pcert_evenQ_smooth : ℚ) : ℝ)
  | Family.evenDyadic => ((Payoff.Pcert_even_dyad_smooth : ℚ) : ℝ)
  | Family.oddDyadic => ((Payoff.Pcert_even_dyad_smooth : ℚ) : ℝ)
  | Family.evenQleR => ((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
  | Family.oddQleR => ((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
  | Family.evenDyadicR => ((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
  | Family.oddDyadicR => ((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)

/-- `κ_cert := 2 − P_cert` by family: `1.2788` / `1.2902`. -/
def Family.kappaCert (F : Family) : ℝ := kappaCof F.payoffCert

theorem two_sub_kappaCert (F : Family) : 2 - F.kappaCert = F.payoffCert := by
  unfold Family.kappaCert kappaCof; ring

theorem payoffCert_qle : Family.qle.payoffCert = 7212 / 10000 := by
  simp [Family.payoffCert, Payoff.Pcert_qQ_smooth]

theorem payoffCert_dyadic : Family.dyadic.payoffCert = 7098 / 10000 := by
  simp [Family.payoffCert, Payoff.Pcert_dyad_smooth]

theorem kappaCert_qle : Family.qle.kappaCert = 2 - 7212 / 10000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_qle]

theorem kappaCert_dyadic : Family.dyadic.kappaCert = 2 - 7098 / 10000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_dyadic]

theorem payoffCert_evenQle : Family.evenQle.payoffCert = 698 / 1000 := by
  simp [Family.payoffCert, Payoff.Pcert_evenQ_smooth]; norm_num

theorem payoffCert_oddQle : Family.oddQle.payoffCert = 698 / 1000 := by
  simp [Family.payoffCert, Payoff.Pcert_evenQ_smooth]; norm_num

theorem payoffCert_evenDyadic : Family.evenDyadic.payoffCert = 6919 / 10000 := by
  simp [Family.payoffCert, Payoff.Pcert_even_dyad_smooth]

theorem payoffCert_oddDyadic : Family.oddDyadic.payoffCert = 6919 / 10000 := by
  simp [Family.payoffCert, Payoff.Pcert_even_dyad_smooth]

theorem kappaCert_evenQle : Family.evenQle.kappaCert = 2 - 698 / 1000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_evenQle]

theorem kappaCert_oddQle : Family.oddQle.kappaCert = 2 - 698 / 1000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_oddQle]

theorem kappaCert_evenDyadic : Family.evenDyadic.kappaCert = 2 - 6919 / 10000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_evenDyadic]

theorem kappaCert_oddDyadic : Family.oddDyadic.kappaCert = 2 - 6919 / 10000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_oddDyadic]

theorem payoffCert_evenQleR : Family.evenQleR.payoffCert = 7212 / 10000 := by
  simp [Family.payoffCert, Payoff.Pcert_qQ_smooth]

theorem payoffCert_oddQleR : Family.oddQleR.payoffCert = 7212 / 10000 := by
  simp [Family.payoffCert, Payoff.Pcert_qQ_smooth]

theorem payoffCert_evenDyadicR : Family.evenDyadicR.payoffCert = 7098 / 10000 := by
  simp [Family.payoffCert, Payoff.Pcert_dyad_smooth]

theorem payoffCert_oddDyadicR : Family.oddDyadicR.payoffCert = 7098 / 10000 := by
  simp [Family.payoffCert, Payoff.Pcert_dyad_smooth]

theorem kappaCert_evenQleR : Family.evenQleR.kappaCert = 2 - 7212 / 10000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_evenQleR]

theorem kappaCert_oddQleR : Family.oddQleR.kappaCert = 2 - 7212 / 10000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_oddQleR]

theorem kappaCert_evenDyadicR : Family.evenDyadicR.kappaCert = 2 - 7098 / 10000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_evenDyadicR]

theorem kappaCert_oddDyadicR : Family.oddDyadicR.kappaCert = 2 - 7098 / 10000 := by
  rw [Family.kappaCert, kappaCof, payoffCert_oddDyadicR]

/-- `κ_C ≤ κ_cert` (the certified constant is the LARGER Frobenius constant: `3.1·10⁻⁵` for `qle`,
`1.2·10⁻⁴` for `dyadic`). -/
theorem kappaC_le_kappaCert (F : Family) : F.kappaC ≤ F.kappaCert := by
  cases F
  · rw [kappaCert_qle]; norm_num [Family.kappaC, kappaCof, Family.payoff, Pconst]
  · rw [kappaCert_dyadic]; norm_num [Family.kappaC, kappaCof, Family.payoff, PconstDyadic]
  · rw [kappaCert_evenQle]; norm_num [Family.kappaC, kappaCof, Family.payoff, PconstEven]
  · rw [kappaCert_oddQle]; norm_num [Family.kappaC, kappaCof, Family.payoff, PconstEven]
  · rw [kappaCert_evenDyadic]
    norm_num [Family.kappaC, kappaCof, Family.payoff, PconstEvenDyadic]
  · rw [kappaCert_oddDyadic]
    norm_num [Family.kappaC, kappaCof, Family.payoff, PconstEvenDyadic]
  · rw [kappaCert_evenQleR]; norm_num [Family.kappaC, kappaCof, Family.payoff, Pconst]
  · rw [kappaCert_oddQleR]; norm_num [Family.kappaC, kappaCof, Family.payoff, Pconst]
  · rw [kappaCert_evenDyadicR]; norm_num [Family.kappaC, kappaCof, Family.payoff, PconstDyadic]
  · rw [kappaCert_oddDyadicR]; norm_num [Family.kappaC, kappaCof, Family.payoff, PconstDyadic]

theorem kappaCert_nonneg (F : Family) : 0 ≤ F.kappaCert := by
  cases F
  · rw [kappaCert_qle]; norm_num
  · rw [kappaCert_dyadic]; norm_num
  · rw [kappaCert_evenQle]; norm_num
  · rw [kappaCert_oddQle]; norm_num
  · rw [kappaCert_evenDyadic]; norm_num
  · rw [kappaCert_oddDyadic]; norm_num
  · rw [kappaCert_evenQleR]; norm_num
  · rw [kappaCert_oddQleR]; norm_num
  · rw [kappaCert_evenDyadicR]; norm_num
  · rw [kappaCert_oddDyadicR]; norm_num

theorem kappaCert_le_two (F : Family) : F.kappaCert ≤ 2 := by
  cases F
  · rw [kappaCert_qle]; norm_num
  · rw [kappaCert_dyadic]; norm_num
  · rw [kappaCert_evenQle]; norm_num
  · rw [kappaCert_oddQle]; norm_num
  · rw [kappaCert_evenDyadic]; norm_num
  · rw [kappaCert_oddDyadic]; norm_num
  · rw [kappaCert_evenQleR]; norm_num
  · rw [kappaCert_oddQleR]; norm_num
  · rw [kappaCert_evenDyadicR]; norm_num
  · rw [kappaCert_oddDyadicR]; norm_num

namespace JoinCert

/-! ## 2. §7's two clauses at `κ_cert` — verbatim mirrors of the `κ_C` chain
(`Budget.pair_absorbed_of_theta_small` → `tail_clauses_at_design` →
`HPre.tail_clauses_at_design_of_closing_A0` → `HPre.hregime_eventually` → `HPre.tail_clauses_eventually`).
`Budget.pair_arith` is `private`, hence copied. -/

private theorem pair_arith_cert {θ m X k Lr : ℝ} (hθ : 0 ≤ θ) (hm : 0 < m) (hX : 1 ≤ X)
    (hone : θ ≤ m * Real.sqrt X)
    (hsmall : θ * (5 + 2 * k) ≤ m * Real.sqrt X * Lr) :
    4 * (θ / (m * X)) + 2 * (θ / (m * Real.sqrt X)) * k
        + (θ / (m * Real.sqrt X)) ^ 2 ≤ Lr := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt X := by
    have h := Real.sqrt_le_sqrt hX
    simpa using h
  have hs0 : (0 : ℝ) < Real.sqrt X := by linarith
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsX : Real.sqrt X ≤ X := by nlinarith
  have hms : (0 : ℝ) < m * Real.sqrt X := mul_pos hm hs0
  have hmX : (0 : ℝ) < m * X := mul_pos hm hX0
  have hu0 : (0 : ℝ) ≤ θ / (m * Real.sqrt X) := div_nonneg hθ hms.le
  have hu1 : θ / (m * Real.sqrt X) ≤ 1 := (div_le_one hms).2 hone
  have hu2 : (θ / (m * Real.sqrt X)) ^ 2 ≤ θ / (m * Real.sqrt X) := by nlinarith
  have huL : θ / (m * Real.sqrt X) * (5 + 2 * k) ≤ Lr := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hms, mul_comm Lr]
    exact hsmall
  have h4 : θ / (m * X) ≤ θ / (m * Real.sqrt X) := by
    rw [div_le_div_iff₀ hmX hms]
    nlinarith [mul_le_mul_of_nonneg_left hsX (mul_nonneg hθ hm.le)]
  nlinarith [h4, hu2, huL, hu0]

/-- `pair_absorbed_of_theta_small` at `κ_cert`. -/
theorem pair_absorbed_of_theta_small_cert (F : Family) (P : ParamsQ) (θ₀ : ℝ)
    (hP : P.Valid) (hwr : SideCondWrange P) (hθ : 0 ≤ θ₀)
    (hone : θ₀ ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P))
    (hsmall : θ₀ * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
        ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) * (L₅ P + L₉ P)) :
    4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P := by
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have ha0 : (0 : ℝ) < P.aQ := hP.aQ_pos
  have hm0 : (0 : ℝ) < P.aQ * P.LB := mul_pos ha0 hLB0
  unfold rowR4 rowR5
  exact pair_arith_cert hθ hm0 (one_le_TfamAvg F P hP) hone hsmall

/-- `tail_clauses_at_design` at `κ_cert`. -/
theorem tail_clauses_at_design_cert (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hQn : 2 ≤ Qn) (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hone : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
        ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P))
    (hsmall : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
          * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
        ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P)) :
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
      (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) ∧
      (∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
        Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hCenv0 : (0 : ℝ) ≤ CenvDesign P :=
    mul_nonneg (Real.exp_pos (2 : ℝ)).le (le_trans hLB0.le (le_max_right _ _))
  have hθ0 : 0 ≤ theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) :=
    theta0Fam_nonneg P A₀ (CenvDesign P) (Qn : ℝ) hP hwr hA₀ hCenv0
      (by exact_mod_cast Nat.one_le_of_lt hQn)
  exact ⟨_, hθ0,
    pair_absorbed_of_theta_small_cert F P _ hP hwr hθ0 hone hsmall,
    famTailInputsD_at F Qn P A₀ hQn hP hwr hϱ hA₀ hloc⟩

/-- `HPre.tail_clauses_at_design_of_closing_A0` at `κ_cert`. -/
theorem tail_clauses_at_design_of_closing_A0_cert (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (A₀ : ℝ) (hQn : 2 ≤ Qn) (hdes : DesignOfRecord F r ε (Qn : ℝ) P)
    (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hregime : A₀ * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
        ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P)) :
    ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
      (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) ∧
      (∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
        Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hA₀0 : (0 : ℝ) < A₀ := by linarith
  have hθle := HPre.theta0Fam_le_of_design_A0 F r ε Qn P A₀ hdes hr hLL hA₀
  have hk : (0 : ℝ) ≤ Real.sqrt (F.kappaCert + rowR2 F P) := Real.sqrt_nonneg _
  have hL59 := HPre.L5_add_L9_le_one hdes
  have ha0 : (0 : ℝ) ≤ P.aQ := by linarith [hP.a_ge]
  have hpos : 0 ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) :=
    mul_nonneg (mul_nonneg ha0 (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hsmall : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
        * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
      ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
        * (L₅ P + L₉ P) := by
    have hstep : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
          * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
        ≤ A₀ / P.LB * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P)) :=
      mul_le_mul_of_nonneg_right hθle (by linarith)
    refine le_trans hstep ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hLB0]
    have e : P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) * P.LB
        = P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) := by ring
    rw [e]; exact hregime
  have hone : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
      ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) := by
    refine le_trans hθle ?_
    rw [div_le_iff₀ hLB0]
    have h5 : 5 * A₀ ≤ A₀ * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P)) := by
      linarith [mul_nonneg hA₀0.le hk]
    have h6 := mul_le_mul_of_nonneg_left hL59 hpos
    linarith
  exact tail_clauses_at_design_cert F r ε Qn P A₀ hQn hdes hϱ hA₀ hloc hone hsmall

/-- `HPre.hregime_eventually` at `κ_cert` — the same proof: the left side is bounded by `23·A₀`
from `κ_cert ≤ 2` and `r₂ ≤ 79`, the right side grows like `ℒ^{(7−r−ε)/2}·log ℒ`. -/
theorem hregime_cert_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 ≤ ε)
    (hre : r + ε ≤ 7) (A₀ : ℝ) (hA₀ : 1 ≤ A₀) :
    ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      A₀ * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
        ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) := by
  have h1 : ∀ᶠ Qn : ℕ in Filter.atTop, (200 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 200
  have h2 : ∀ᶠ Qn : ℕ in Filter.atTop, 16 * A₀ ≤ Real.log (Real.log (Qn : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (16 * A₀)
  filter_upwards [h1, h2] with Qn hu hlu
  intro P hdes
  have hrow := HPre.rowR2_le_design hdes hr hu
  have hrhs := HPre.rhs_lower_design hdes hr hε hre hu
  have hκ := kappaCert_le_two F
  have hr2 : 0 ≤ rowR2 F P := rowR2_nonneg F P hdes.1
  have hsq : Real.sqrt (F.kappaCert + rowR2 F P) ≤ 9 := by
    have := Real.sqrt_le_sqrt (show F.kappaCert + rowR2 F P ≤ 9 ^ 2 by linarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hA₀0 : 0 < A₀ := by linarith
  have hlhs : A₀ * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P)) ≤ 23 * A₀ := by
    have := mul_le_mul_of_nonneg_left hsq hA₀0.le
    linarith
  have hpow1 : 1 ≤ Real.log (Qn : ℝ) ^ (7 / 2 - (r + ε) / 2) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hprod : 16 * A₀ ≤ Real.log (Qn : ℝ) ^ (7 / 2 - (r + ε) / 2)
      * Real.log (Real.log (Qn : ℝ)) := by
    have h0 : 0 ≤ Real.log (Real.log (Qn : ℝ)) := by linarith
    have := mul_le_mul_of_nonneg_right hpow1 h0
    linarith
  linarith

/-- `HPre.tail_clauses_eventually` at `κ_cert`: §7's two clauses, eventually in `Q`, for every
`r + ε ≤ 7`. -/
theorem tail_clauses_cert_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 ≤ ε)
    (hre : r + ε ≤ 7) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ →
      ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
        (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
          + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) ∧
        (∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
          Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have h1 : ∀ᶠ Qn : ℕ in Filter.atTop, (200 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 200
  filter_upwards [h1, hregime_cert_eventually F r ε hr hε hre A₀ hA₀,
    Filter.eventually_ge_atTop 2] with Qn hu hreg hQn
  intro P hdes hϱ
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : 100 ≤ P.LL := le_trans (by linarith) (LL_ge_log_of_design hdes hQn1)
  exact tail_clauses_at_design_of_closing_A0_cert F r ε Qn P A₀ hQn hdes hr hLL hϱ hA₀ hloc
    (hreg P hdes)

/-! ## 3. Prop 3.1's bracket at `κ_cert`, and the eight clauses at ONE design point -/

/-- `propBracket` at `κ_cert`. -/
def propBracketCert (F : Family) (P : ParamsQ) (θ₀ : ℝ) : ℝ :=
  4 * rowR1 F P + rowR2 F P + 3 * rowR3 P + 4 * rowR4 F P θ₀
    + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P) + rowR5 F P θ₀ ^ 2

/-- `propBracket_le_budgetTotal` at `κ_cert` — the same exact ring identity (D35): the folded
coefficients cancel and what is left is `(L₅ + L₉) − (pair block)`, i.e. `hpair`. -/
theorem propBracketCert_le_budgetTotal (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (θ₀ : ℝ)
    (_hdes : DesignOfRecord F r ε (Qn : ℝ) P) (_hθ : 0 ≤ θ₀)
    (hpair : 4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) :
    propBracketCert F P θ₀ ≤ budgetTotal F P := by
  have key : budgetTotal F P - propBracketCert F P θ₀
      = (L₅ P + L₉ P)
        - (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
            + rowR5 F P θ₀ ^ 2) := by
    unfold budgetTotal propBracketCert minorRows rowR1 rowR2 rowR3
    ring
  linarith

/-- **The eight-clause body of the assembly at ONE design point, at `κ_cert`, with every input
named** — `assembly_clauses_at_design` with (i) `trace_row` replaced by the hypothesis `htr`
(delivered eventually by `trace_row_eventually_aux`), (ii) `frobenius_row` replaced by the
hypothesis `hfrob` at `κ_cert`, (iii) the §9 bundles discharged at the canonical `famZc`
(`EFChi.famZeroConfig_famZc`, `famGramBridge_famZc`), (iv) Prop 3.1 taken from the `κ`-generic
`prop_3_1_pair_moment_certificate` through `EFChi.certificate_display_fam_of_bridge`. -/
theorem assembly_clauses_at_design_cert (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (θ₀ : ℝ)
    (hQn : 2 ≤ Qn) (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hθ : 0 ≤ θ₀)
    (htr : (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn)
    (hfrob : frobSqGhatFam P F Qn ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn)
    (hsharp : SharpZeroDensity F Qn P) (hrvm : FamRvMLower F Qn P)
    (hpair : 4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P)
    (hblock : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
      Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) :
    ∃ r₁ r₂ r₃ r₄ r₅ θ : ℝ,
      0 ≤ θ ∧
      (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn ∧
      frobSqGhatFam P F Qn ≤ (F.kappaCert + r₂) * NfamQ P F Qn ∧
      NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn ∧
      Btr P F Qn θ ≤ r₄ * NfamQ P F Qn ∧
      BF P F Qn θ ≤ r₅ * Real.sqrt (NfamQ P F Qn) ∧
      4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
          + 2 * r₅ * Real.sqrt (F.kappaCert + r₂) + r₅ ^ 2 ≤ budgetTotal F P ∧
      (2 - F.kappaCert - budgetTotal F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLB : (0 : ℝ) < P.LB := EFChi.LB_pos_of_valid hP
  have ha0 : (0 : ℝ) < P.aQ := hP.aQ_pos
  have haL : (0 : ℝ) < P.aQ * P.LB := mul_pos ha0 hLB
  have hB0 : (0 : ℝ) ≤ θ₀ / (P.aQ * P.LB) := div_nonneg hθ haL.le
  have hS : (0 : ℝ) ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hBtr0 : (0 : ℝ) ≤ Btr P F Qn θ₀ := by
    show (0 : ℝ) ≤ F.sizeR Qn * θ₀ / (P.aQ * P.LB)
    exact div_nonneg (mul_nonneg hS hθ) haL.le
  have hBF0 : (0 : ℝ) ≤ BF P F Qn θ₀ := by
    show (0 : ℝ) ≤ Real.sqrt (F.sizeR Qn) * θ₀ / (P.aQ * P.LB)
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hθ) haL.le
  have hκ : (0 : ℝ) ≤ F.kappaCert + rowR2 F P := by
    linarith [kappaCert_nonneg F, rowR2_nonneg F P hP]
  -- §10.3's rows 3, 4, 5 and the bracket
  have hNII := buffer_row_sharp F r ε Qn P hdes hsharp hrvm
  obtain ⟨hBtr', hBF'⟩ := pair_rows F r ε Qn P θ₀ hdes hθ hrvm
  have hbr := propBracketCert_le_budgetTotal F r ε Qn P θ₀ hdes hθ hpair
  -- §9's family display joined to §7.3's pair split, then Prop 3.1 (generic in `κ`)
  have hdisp := EFChi.certificate_display_fam_of_bridge P hP F Qn θ₀ EFChi.famZc
    (EFChi.famZeroConfig_famZc F Qn hQn) (EFChi.famGramBridge_famZc P hP F Qn hQn hwr) hwr
    (abs_trGz_sub_trAhat_fam_le_Btr P F Qn θ₀ EFChi.famZc hl hblock)
    (sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF P F Qn θ₀ EFChi.famZc hl hB0 hblock)
    hBtr0 hBF0
  have hlast := prop_3_1_pair_moment_certificate (NfamQ_nonneg P F Qn) hBtr0 hBF0 hκ hdisp
    htr hfrob hNII hBtr' hBF'
  have hN : (0 : ℝ) ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hbracket : propBracketCert F P θ₀
      = 4 * rowR1 F P + rowR2 F P + 3 * rowR3 P + 4 * rowR4 F P θ₀
        + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P) + rowR5 F P θ₀ ^ 2 := rfl
  refine ⟨rowR1 F P, rowR2 F P, rowR3 P, rowR4 F P θ₀, rowR5 F P θ₀, θ₀,
    hθ, htr, hfrob, hNII, hBtr', hBF', ?_, ?_⟩
  · rw [← hbracket]; exact hbr
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hN) hlast
    linarith [hbr, hbracket.le, hbracket.ge]

/-! ## 4. The assembly, eventually in `Q`, and in the frozen `∃ Q₀` shape -/

/-- **The eight clauses at EVERY design point, eventually in `Q`**, from the named eventual inputs
`hsharp`, `hfrob`, `hrvm` and the tree (`trace_row_eventually_aux`, `tail_clauses_cert_eventually`
with `A₀`/`hloc` from `EFChi.localCountChi_uniform` and `hϱ` from `gevreyProfile_rhoTwoQ`). -/
theorem assembly_eventually_cert (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hre : r + ε ≤ 7)
    (hsharp : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      SharpZeroDensity F Qn P)
    (hfrob : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      frobSqGhatFam P F Qn ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn)
    (hrvm : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      FamRvMLower F Qn P) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      ∃ r₁ r₂ r₃ r₄ r₅ θ₀ : ℝ,
        0 ≤ θ₀ ∧
        (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn ∧
        frobSqGhatFam P F Qn ≤ (F.kappaCert + r₂) * NfamQ P F Qn ∧
        NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn ∧
        Btr P F Qn θ₀ ≤ r₄ * NfamQ P F Qn ∧
        BF P F Qn θ₀ ≤ r₅ * Real.sqrt (NfamQ P F Qn) ∧
        4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
            + 2 * r₅ * Real.sqrt (F.kappaCert + r₂) + r₅ ^ 2 ≤ budgetTotal F P ∧
        (2 - F.kappaCert - budgetTotal F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  filter_upwards [trace_row_eventually_aux F r ε hr hε,
    tail_clauses_cert_eventually F r ε hr hε.le hre A₀ hA₀ hloc, hsharp, hfrob, hrvm,
    eventually_ge_atTop 2] with Qn htr htail hs hf hv hQn
  intro P hdes
  have hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.1]; exact gevreyProfile_rhoTwoQ
  obtain ⟨θ₀, hθ, hpair, hblock⟩ := htail P hdes hϱ
  exact assembly_clauses_at_design_cert F r ε Qn P θ₀ hQn hdes hθ (htr P hdes) (hf P hdes)
    (hs P hdes) (hv P hdes) hpair hblock

/-- **`assembly_at_lamStar` at the certified constant `κ_cert`, with its inputs NAMED** — the
frozen statement verbatim with `F.kappaC ↦ F.kappaCert`, under
  * `hre : r + ε ≤ 7` (F52's regime for §7's `hregime`),
  * `hsharp` (`SharpZeroDensity`, the paper's declared assumption, D35),
  * `hfrob` (the Frobenius row at `κ_cert`, eventually along the design — the remaining §§4–6 work),
  * `hrvm` (`FamRvMLower` eventually along the design — a THEOREM for `Family.qle`,
    `famRvMLower_of_design`; open for `Family.dyadic`).
The design point is `exists_designOfRecord`'s; `Q₀` is the max of its threshold and the eventual
inputs'. -/
theorem assembly_at_lamStar_cert (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hre : r + ε ≤ 7)
    (hsharp : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      SharpZeroDensity F Qn P)
    (hfrob : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      frobSqGhatFam P F Qn ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn)
    (hrvm : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      FamRvMLower F Qn P) :
    ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ∃ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P ∧
        ∃ r₁ r₂ r₃ r₄ r₅ θ₀ : ℝ,
          0 ≤ θ₀ ∧
          (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn ∧
          frobSqGhatFam P F Qn ≤ (F.kappaCert + r₂) * NfamQ P F Qn ∧
          NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn ∧
          Btr P F Qn θ₀ ≤ r₄ * NfamQ P F Qn ∧
          BF P F Qn θ₀ ≤ r₅ * Real.sqrt (NfamQ P F Qn) ∧
          4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
              + 2 * r₅ * Real.sqrt (F.kappaCert + r₂) + r₅ ^ 2 ≤ budgetTotal F P ∧
          (2 - F.kappaCert - budgetTotal F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  obtain ⟨Q₁, hQ₁⟩ := exists_designOfRecord F r ε hr hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (assembly_eventually_cert F r ε hr hε hre hsharp hfrob hrvm)
  refine ⟨max Q₁ (N : ℝ), fun Qn hQn => ?_⟩
  obtain ⟨P, hdes⟩ := hQ₁ (Qn : ℝ) (le_trans (le_max_left _ _) hQn)
  have hNQ : N ≤ Qn := by exact_mod_cast le_trans (le_max_right _ _) hQn
  exact ⟨P, hdes, hN Qn hNQ P hdes⟩

/-- `assembly_at_lamStar_cert` for Theorem 1's family, with `hrvm` DISCHARGED
(`famRvMLower_of_design`): exactly the task's signature — `hsharp` and `hfrob` are the only named
inputs besides the regime `r + ε ≤ 7`. -/
theorem assembly_at_lamStar_cert_qle (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hre : r + ε ≤ 7)
    (hsharp : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      SharpZeroDensity Family.qle Qn P)
    (hfrob : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.qle Qn
        ≤ (Family.qle.kappaCert + rowR2 Family.qle P) * NfamQ P Family.qle Qn) :
    ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ∃ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P ∧
        ∃ r₁ r₂ r₃ r₄ r₅ θ₀ : ℝ,
          0 ≤ θ₀ ∧
          (1 - r₁) * NfamQ P Family.qle Qn ≤ trGhatFam P Family.qle Qn ∧
          frobSqGhatFam P Family.qle Qn
            ≤ (Family.qle.kappaCert + r₂) * NfamQ P Family.qle Qn ∧
          NIIFamQ P Family.qle Qn ≤ r₃ * NfamQ P Family.qle Qn ∧
          Btr P Family.qle Qn θ₀ ≤ r₄ * NfamQ P Family.qle Qn ∧
          BF P Family.qle Qn θ₀ ≤ r₅ * Real.sqrt (NfamQ P Family.qle Qn) ∧
          4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
              + 2 * r₅ * Real.sqrt (Family.qle.kappaCert + r₂) + r₅ ^ 2
            ≤ budgetTotal Family.qle P ∧
          (2 - Family.qle.kappaCert - budgetTotal Family.qle P) * NfamQ P Family.qle Qn
            ≤ N0sFamQ P Family.qle Qn :=
  assembly_at_lamStar_cert Family.qle r ε hr hε hre hsharp hfrob
    (famRvMLower_of_design r ε hr hε)

/-! ## 5. The rate step and the headline theorems at `P_cert` -/

/-- **`payoff_rate_of_assembly` at the certified constants** — takes the assembly EXACTLY in
`assembly_at_lamStar_cert`'s conclusion shape (only its last clause is used) and delivers Theorem 1's
rate with `F.payoffCert` in place of `F.payoff`.

Proof route: `payoff_rate_of_assembly`'s own proof consumes the PRIVATE `D0_le_of_design` /
`budgetTotal_le_of_regime`, which cannot be cited from outside `Budget.lean`; instead a real-variable
design map is built by choice — the assembly's own points at the naturals `≥ Q₀`,
`exists_designOfRecord`'s elsewhere — and the PUBLIC `budgetTotal_isBigO_of_design` gives
`budgetTotal = O(log log Q/log Q)` along it; the rest is `payoff_rate_of_designs`' arithmetic with
`two_sub_kappaCert`. The rate constant is `|c₀| + 1` (existential), not the explicit
`20(r+ε) + 120200`. -/
theorem payoff_rate_of_assembly_cert (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hassembly : ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ∃ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P ∧
        (2 - F.kappaCert - budgetTotal F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (F.payoffCert - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₀, hQ₀⟩ := hassembly
  obtain ⟨Q₁, hQ₁⟩ := exists_designOfRecord F r ε hr hε
  -- the design map on the naturals: the assembly's own points above `Q₀`
  have hchoiceN : ∀ n : ℕ, ∃ P : ParamsQ, Q₀ ≤ (n : ℝ) →
      DesignOfRecord F r ε (n : ℝ) P ∧
        (2 - F.kappaCert - budgetTotal F P) * NfamQ P F n ≤ N0sFamQ P F n := by
    intro n
    by_cases hn : Q₀ ≤ (n : ℝ)
    · obtain ⟨P, hP⟩ := hQ₀ n hn
      exact ⟨P, fun _ => hP⟩
    · exact ⟨Classical.choose (hQ₁ Q₁ le_rfl), fun h => absurd h hn⟩
  choose designN hdesN using hchoiceN
  -- its extension to the reals: `exists_designOfRecord`'s points off the naturals
  have hchoiceR : ∀ Q : ℝ, ∃ P : ParamsQ,
      (∀ n : ℕ, (n : ℝ) = Q → P = designN n) ∧
      ((¬ ∃ n : ℕ, (n : ℝ) = Q) → Q₁ ≤ Q → DesignOfRecord F r ε Q P) := by
    intro Q
    by_cases hn : ∃ n : ℕ, (n : ℝ) = Q
    · obtain ⟨n, rfl⟩ := hn
      refine ⟨designN n, fun m hm => ?_, fun h => absurd ⟨n, rfl⟩ h⟩
      rw [Nat.cast_injective hm]
    · by_cases hQ : Q₁ ≤ Q
      · obtain ⟨P, hP⟩ := hQ₁ Q hQ
        exact ⟨P, fun n hn' => absurd ⟨n, hn'⟩ hn, fun _ _ => hP⟩
      · exact ⟨Classical.choose (hQ₁ Q₁ le_rfl), fun n hn' => absurd ⟨n, hn'⟩ hn,
          fun _ h => absurd h hQ⟩
  choose design hdesign1 hdesign2 using hchoiceR
  have hdesign : ∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q) := by
    filter_upwards [eventually_ge_atTop Q₀, eventually_ge_atTop Q₁] with Q h0 h1
    by_cases hn : ∃ n : ℕ, (n : ℝ) = Q
    · obtain ⟨n, rfl⟩ := hn
      rw [hdesign1 (n : ℝ) n rfl]
      exact (hdesN n h0).1
    · exact hdesign2 Q hn h1
  -- the budget along it is `O(log log Q/log Q)`
  obtain ⟨c0, hc0⟩ :=
    Asymptotics.isBigO_iff.mp (budgetTotal_isBigO_of_design F r ε hr hε design hdesign)
  have hev : ∀ᶠ Q in atTop,
      ‖budgetTotal F (design Q)‖ ≤ c0 * ‖Real.log (Real.log Q) / Real.log Q‖ ∧
      (1 : ℝ) ≤ Real.log Q ∧ (0 : ℝ) ≤ Real.log (Real.log Q) := by
    filter_upwards [hc0,
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (0 : ℝ)]
      with Q h2 h3 h4
    exact ⟨h2, h3, h4⟩
  obtain ⟨Q₂, hQ₂⟩ := eventually_atTop.mp hev
  refine ⟨max Q₀ Q₂, |c0| + 1, by positivity, ?_⟩
  intro Qn hQn
  obtain ⟨hdes, hlast⟩ := hdesN Qn (le_trans (le_max_left _ _) hQn)
  obtain ⟨hb, hu1, hv0⟩ := hQ₂ (Qn : ℝ) (le_trans (le_max_right _ _) hQn)
  rw [hdesign1 (Qn : ℝ) Qn rfl] at hb
  have hu0 : (0 : ℝ) < Real.log (Qn : ℝ) := by linarith
  have hvu : (0 : ℝ) ≤ Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ) :=
    div_nonneg hv0 hu0.le
  have hT : (designN Qn).T = Twin (Qn : ℝ) r ε := hdes.2.2.1
  -- the rate bound on the budget total, at a nonnegative constant
  have hbt : budgetTotal F (designN Qn)
      ≤ (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hvu] at hb
    have h1 : budgetTotal F (designN Qn) ≤ |budgetTotal F (designN Qn)| := le_abs_self _
    have h2 : c0 * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
        ≤ (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self c0]) hvu
    linarith
  -- the assembly's last clause, at the design's own window `I = [T, 2T]`
  have hNfam : NfamQ (designN Qn) F Qn
      = NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
    unfold NfamQ; rw [hT]
  have hN0s : N0sFamQ (designN Qn) F Qn
      = N0sFamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
    unfold N0sFamQ; rw [hT]
  rw [hNfam, hN0s] at hlast
  have hN : (0 : ℝ) ≤ NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) :=
    NfamCount_nonneg _ _ _ _
  have hcoef : F.payoffCert - (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
      ≤ 2 - F.kappaCert - budgetTotal F (designN Qn) := by
    rw [two_sub_kappaCert]; linarith
  have hgd : (|c0| + 1) * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)
      = (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)) :=
    mul_div_assoc _ _ _
  rw [hgd]
  exact le_trans (mul_le_mul_of_nonneg_right hcoef hN) hlast

/-- **Theorem 1, r-generic, at the CERTIFIED constant `P_cert = 0.7212`** (B7 option 1), under the
two named assumptions `hsharp` (the paper's `SharpZeroDensity`) and `hfrob` (the Frobenius row at
`κ_cert`, eventually along the design) and the F52 regime `r + ε ≤ 7`. `hrvm` is discharged by
`famRvMLower_of_design`; everything else is the tree's. -/
theorem theorem_one_generic_cert (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hre : r + ε ≤ 7)
    (hsharp : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      SharpZeroDensity Family.qle Qn P)
    (hfrob : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.qle Qn
        ≤ (Family.qle.kappaCert + rowR2 Family.qle P) * NfamQ P Family.qle Qn) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  have h := payoff_rate_of_assembly_cert Family.qle r ε hr hε ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_cert Family.qle r ε hr hε hre hsharp hfrob
    (famRvMLower_of_design r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- **Corollary 2 (dyadic) at the CERTIFIED constant `P_cert = 0.7098`**, under `hsharp`, `hfrob`,
`r + ε ≤ 7` AND `hrvm` — `FamRvMLower Family.dyadic` is not proved along the design (F59 note:
`famRvMLower_of_design` is `qle`-only), so it stays named here. -/
theorem corollary_two_dyadic_cert (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hre : r + ε ≤ 7)
    (hsharp : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord Family.dyadic r ε (Qn : ℝ) P → SharpZeroDensity Family.dyadic Qn P)
    (hfrob : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.dyadic Qn
        ≤ (Family.dyadic.kappaCert + rowR2 Family.dyadic P) * NfamQ P Family.dyadic Qn)
    (hrvm : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord Family.dyadic r ε (Qn : ℝ) P → FamRvMLower Family.dyadic Qn P) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  have h := payoff_rate_of_assembly_cert Family.dyadic r ε hr hε ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_cert Family.dyadic r ε hr hε hre hsharp hfrob hrvm
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

end JoinCert
end ZetaQ

end

