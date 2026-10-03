/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/Margin.lean — **Theorem 1 WITHOUT the regime `r + ε ≤ 7`.**

`JoinProved.theorem_one_generic_proved` rests on `hre : r + ε ≤ 7` because §7's regime inequality
`hregime` (`HPre.hregime_eventually`) compares the tail target `θ₀_fam ≤ A₀/L` of the margin-0
closing condition against the pair rows `L₅ + L₉ ≈ 6ℒ log ℒ/T`, which needs
`√T ≲ 0.4·ℒ^{3.5} log ℒ/A₀` (`audit/HPre_REPORT.md` §(a)–(c)). The repair (§(c) there): meet the
closing condition with a MARGIN `m = ½ log T` nats — `ClosingAtDesignM` / `DesignOfRecordM` of
`ZetaQ/Budget.lean` — so that the tail target becomes `θ₀_fam ≤ A₀ e^{−m}/L = A₀/(L√T)`
(`theta0Fam_le_of_designM_A0`), and `hregime` becomes `√T`-free: `A₀(5 + 2√(κ + r₂)) ≤ a L² T
√(⟨ℒ⟩/2π)(L₅ + L₉) ≳ 4.5 ℒ³ log ℒ` — true eventually for EVERY `r ≥ 3` (`hregime_M_eventually`).

What this file does:
  * §1 the margin design's scales (`T`, `ℒ ≥ log Q`, `w = 1`, `L ≥ ℒ`), verbatim at `DesignOfRecordM`;
  * §2 **the `D₀`-substitution transfer** (`exists_twin`, `eventually_M_of_D0free`): a margin design
    point and `exists_designOfRecord_at`'s margin-0 point at the same `Q` share `(Q, T, λ, w, ϱ, prof)`
    and differ only in `D₀`, so every eventual input whose conclusion does not read `D₀` — the trace
    row, the Frobenius row (`HFrob`), `FamRvMLower` — transfers from `DesignOfRecord` to
    `DesignOfRecordM` with a one-line `fun _ _ _ h => h` (the conclusions are definitionally invariant
    under `{P with D0 := d}`); nothing in `FrobAssembly`/`InZone`/`Ends`/`Zones`/`HFrob` is restated;
  * §3–§5 `hpre`, `θ₀_fam ≤ A₀e^{−m}/L`, and §7's two clauses at the margin design, eventually in `Q`,
    with NO hypothesis on `r + ε` (mirrors of `HPre`/`JoinCert` through the cores
    `HPre.hpre_of_closing`, `HPre.rowR2_le_of_facts`, `HPre.L5_add_L9_le_one_of`);
  * §6 the eight-clause assembly at the proved buffer row along `DesignOfRecordM`
    (`Budget.buffer_row_proved_of_valid`, `Budget.pair_rows_of_valid`), the rate
    (`JoinProved.budgetTotalProved_isBigO_core` + `Budget.budgetTotal_isBigO_of_designM` +
    `Budget.designM_D0_isBigO`), and the headline theorems `JoinProved.theorem_one_generic_proved'`
    (no named hypothesis at all) and `JoinProved.corollary_two_dyadic_proved'` (no named hypothesis
    either: `hfrob_dyadic_of_designM` transfers `JoinProved.hfrob_dyadic_of_design`),
    through `JoinProved.payoff_rate_of_assembly_of_design`;
  * §6b **Corollary 3's two counting rows at the four PARITY families** — `FamNIIUpper` at `4A₀`
    (`famNIIUpper_parity_of_valid`: `Budget.NIIFam_avg_le` prices each modulus at the full `φ*(q)`,
    so a parity family pays a second factor of two, which every `A₀`-generic consumer absorbs) and
    `FamRvMLower` for the two DYADIC parity families (`famRvMLower_parity_dyadic_of_design`, the
    dyadic twin of `Budget.famRvMLower_parity_of_design`), both carried to the margin design by
    §2's `eventually_M_of_D0free` alongside the four parity Frobenius rows of `HFrob` §§9–10;
  * §8 **COROLLARY 3**, `JoinProved.corollary_three_{even,odd}_{dyadic,qQ}_proved'` — the parity
    analogues of the two headlines at `P_cert = 0.6919` (dyadic) and `0.698` (`q ≤ Q`), again with
    NO named hypothesis beyond `3 ≤ r` and `0 < ε`.

Rule 17: nothing here bounds λ by 1, relates `X` to `T`, or pins `D₀`; the margin is a function of `T`
alone and `D₀` stays free, pinned only by the shifted closing equality. Axioms:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx` since the Gallagher rethread (Lemma 6.1 at `Q² + πN`, `ZetaQ/Gallagher.lean`). (Before it: `sorryAx` ONLY from `ZetaQ.multiplicative_large_sieve`, through
`HFrob.hsep_of_design`.)
-/
import ZetaQ.JoinProved

noncomputable section

open Filter Asymptotics

namespace ZetaQ
namespace Margin

open JoinCert JoinProved

/-! ## 1. The margin design's scales -/

theorem T_of_designM {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) : P.T = Real.log (Qn : ℝ) ^ (r + ε) := by
  obtain ⟨-, -, hT, -⟩ := hdes
  rw [hT]; rfl

theorem LL_ge_log_of_designM {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) (hQn : 1 ≤ Qn) : Real.log Qn ≤ P.LL :=
  (log_Qn_le_LL hdes.1 hQn hdes.2.1).1

/-- `w = 1` at the margin design for `r ≥ 3`. -/
theorem w_eq_one_of_designM {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hLL1 : 1 ≤ P.LL) : P.w = 1 := by
  have hw : P.w = wDesign P.LL r := hdes.2.2.2.2.1
  rw [hw]
  unfold wDesign wStar
  exact max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hLL1 (by linarith))

/-- `L ≥ ℒ` at the margin design (`λ* ≥ 1`). -/
theorem LB_ge_LL_of_designM {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) (hLL0 : 0 ≤ P.LL) : P.LL ≤ P.LB := by
  have hlam1 : (1 : ℝ) ≤ P.lam := by rw [hdes.2.2.2.1]; exact HPre.lamStar_ge_one F
  unfold ParamsQ.LB; nlinarith

/-! ## 2. The `D₀`-substitution transfer -/

/-- `K·log log Q ≤ log Q` eventually along the naturals (`log log Q = o(log Q)`). -/
theorem loglog_le_log_eventually (K : ℝ) (hK : 0 < K) :
    ∀ᶠ Qn : ℕ in atTop, K * Real.log (Real.log (Qn : ℝ)) ≤ Real.log (Qn : ℝ) := by
  have hlo : (fun Q : ℝ => Real.log (Real.log Q)) =o[atTop] (fun Q : ℝ => Real.log Q) :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have h1 := hlo.def (c := 1 / K) (by positivity)
  have h2 : ∀ᶠ Qn : ℕ in atTop,
      ‖Real.log (Real.log (Qn : ℝ))‖ ≤ 1 / K * ‖Real.log (Qn : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually h1
  have h3 : ∀ᶠ Qn : ℕ in atTop, (3 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3
  filter_upwards [h2, h3] with Qn h hu
  have hu0 : (0 : ℝ) < Real.log (Qn : ℝ) := by linarith
  have hv0 : (0 : ℝ) < Real.log (Real.log (Qn : ℝ)) := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0.le, abs_of_nonneg hu0.le] at h
  have h4 := mul_le_mul_of_nonneg_left h hK.le
  rw [show K * (1 / K * Real.log (Qn : ℝ)) = Real.log (Qn : ℝ) by field_simp] at h4
  exact h4

/-- **The twin**: in `exists_designOfRecord_at`'s regime, a margin design point `P` has a margin-0
design point `P'` with the same `(Q, T, λ, w, ϱ, prof)`, i.e. `P = {P' with D0 := P.D0}`. -/
theorem exists_twin (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (Q : ℝ)
    (hQ3 : 3 ≤ Q) (hQ0 : 0 < Q) (hu : 200 ≤ Real.log Q)
    (hvu : (2 * (r + ε) + 10) * Real.log (Real.log Q) ≤ Real.log Q)
    (P : ParamsQ) (hdes : DesignOfRecordM F r ε Q P) :
    ∃ P' : ParamsQ, DesignOfRecord F r ε Q P' ∧ { P' with D0 := P.D0 } = P := by
  obtain ⟨P', hdes'⟩ := exists_designOfRecord_at F r ε Q hr hε hQ3 hQ0 hu hvu
  refine ⟨P', hdes', ?_⟩
  obtain ⟨-, hQ, hT, hlam, hw, -, -, -, -, -, hϱ, hprof⟩ := hdes
  obtain ⟨-, hQ', hT', hlam', hw', -, -, -, -, -, hϱ', hprof'⟩ := hdes'
  have hLL : P'.LL = P.LL := by unfold ParamsQ.LL; rw [hQ, hQ', hT, hT']
  have hweq : P'.w = P.w := by rw [hw, hw', hLL]
  have hQQ : P'.Q = P.Q := by rw [hQ, hQ']
  have hTT : P'.T = P.T := by rw [hT, hT']
  have hll : P'.lam = P.lam := by rw [hlam, hlam']
  have hrr : P'.ϱ = P.ϱ := by rw [hϱ, hϱ']
  have hpp : P'.prof = P.prof := by rw [hprof, hprof']
  clear hQ hT hlam hw hϱ hprof hQ' hT' hlam' hw' hϱ' hprof' hLL
  cases P; cases P'
  simp only at hweq hQQ hTT hll hrr hpp
  subst hweq hQQ hTT hll hrr hpp
  rfl

/-- **The `D₀`-free transfer**: if `X Qn P` does not read `P.D0` (`hX`: it is invariant under
`{P with D0 := d}` — for the trace/Frobenius rows and `FamRvMLower` this is `fun _ _ _ h => h`), then
`∀ᶠ Qn, ∀ P, DesignOfRecord → X Qn P` gives `∀ᶠ Qn, ∀ P, DesignOfRecordM → X Qn P`. -/
theorem eventually_M_of_D0free (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (X : ℕ → ParamsQ → Prop)
    (hX : ∀ (Qn : ℕ) (P : ParamsQ) (d : ℝ), X Qn P → X Qn { P with D0 := d })
    (h : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P → X Qn P) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P → X Qn P := by
  have hK : (0 : ℝ) < 2 * (r + ε) + 10 := by linarith
  have h200 : ∀ᶠ Qn : ℕ in atTop, (200 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 200
  filter_upwards [h, loglog_le_log_eventually _ hK, eventually_ge_atTop 3, h200]
    with Qn hQ hvu hQn3 hu
  intro P hdes
  have hQ3 : (3 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn3
  obtain ⟨P', hdes', hPP⟩ :=
    exists_twin F r ε hr hε (Qn : ℝ) hQ3 (by linarith) hu hvu P hdes
  rw [← hPP]
  exact hX Qn P' P.D0 (hQ P' hdes')

/-! ## 3. The transferred eventual inputs (conclusions that do not read `D₀`) -/

/-- `trace_row_eventually_aux` along the margin design. -/
theorem trace_row_eventually_M (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn :=
  eventually_M_of_D0free F r ε hr hε
    (fun Qn P => (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn)
    (fun _ _ _ h => h) (trace_row_eventually_aux F r ε hr hε)

/-- `JoinProved.hfrob_qle_of_design` (the Frobenius row at `κ_cert`, `hsep` discharged)
along the margin design. -/
theorem hfrob_qle_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.qle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.qle Qn
        ≤ (Family.qle.kappaCert + rowR2 Family.qle P) * NfamQ P Family.qle Qn :=
  eventually_M_of_D0free Family.qle r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.qle Qn
      ≤ (Family.qle.kappaCert + rowR2 Family.qle P) * NfamQ P Family.qle Qn)
    (fun _ _ _ h => h) (hfrob_qle_of_design r ε hr hε)

/-- `JoinProved.hfrob_dyadic_of_design` (the exact dyadic Frobenius row at `κ_cert`, `hsep`
discharged) along the margin design. -/
theorem hfrob_dyadic_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.dyadic r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.dyadic Qn
        ≤ (Family.dyadic.kappaCert + rowR2 Family.dyadic P) * NfamQ P Family.dyadic Qn :=
  eventually_M_of_D0free Family.dyadic r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.dyadic Qn
      ≤ (Family.dyadic.kappaCert + rowR2 Family.dyadic P) * NfamQ P Family.dyadic Qn)
    (fun _ _ _ h => h) (hfrob_dyadic_of_design r ε hr hε)

/-- `famRvMLower_of_design` along the margin design. -/
theorem famRvMLower_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.qle r ε (Qn : ℝ) P →
      FamRvMLower Family.qle Qn P :=
  eventually_M_of_D0free Family.qle r ε hr hε (fun Qn P => FamRvMLower Family.qle Qn P)
    (fun _ _ _ h => h) (famRvMLower_of_design r ε hr hε)

/-- `famRvMLower_dyadic_of_design` along the margin design. -/
theorem famRvMLower_dyadic_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.dyadic r ε (Qn : ℝ) P →
      FamRvMLower Family.dyadic Qn P :=
  eventually_M_of_D0free Family.dyadic r ε hr hε (fun Qn P => FamRvMLower Family.dyadic Qn P)
    (fun _ _ _ h => h) (famRvMLower_dyadic_of_design r ε hr hε)

/-- `FamNIIUpper Family.qle` at `2A₀` along the margin design (reads `Valid` and `Q` only). -/
theorem famNIIUpper_qle_of_designM (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.qle r ε (Qn : ℝ) P →
      FamNIIUpper Family.qle Qn P (2 * A₀) := by
  filter_upwards [residue_small_eventually (ε := 1) one_pos, eventually_ge_atTop 2]
    with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  exact famNIIUpper_double_of_eps Family.qle Qn P hP hA₀
    (famNII_upper_of_residue_small P hP Qn hQn hQ hA₀ hloc hres)

/-- `FamNIIUpper Family.dyadic` at `2A₀` along the margin design. -/
theorem famNIIUpper_dyadic_of_designM (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.dyadic r ε (Qn : ℝ) P →
      FamNIIUpper Family.dyadic Qn P (2 * A₀) := by
  filter_upwards [residue_small_eventually_dyadic (ε := 1) one_pos, eventually_ge_atTop 2]
    with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  exact famNIIUpper_double_of_eps Family.dyadic Qn P hP hA₀
    (famNII_upper_dyadic_of_residue_small P hP Qn hQn hQ hA₀ hloc hres)

/-! ## 4. `hpre` and `θ₀_fam ≤ A₀ e^{−m}/L` at the margin design -/

/-- `HPre.hpre_of_design` at the margin design: the closing clause's lower half carries `+ m ≥ 0`,
which only helps (`HPre.hpre_of_closing` reads `needed ≤ c₄ t_{D₀}` alone). -/
theorem hpre_of_designM (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hA₀ : 1 ≤ A₀) (hA₀L : 8 * A₀ ≤ P.LB) :
    0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) ∧
    Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        ≤ logPrefactorGev P :=
  HPre.hpre_of_closing Qn P A₀ hdes.1 hdes.2.1 hdes.2.2.2.2.2.2.2.1
    (w_eq_one_of_designM hdes hr (by linarith)) hLL
    (le_trans hLL (LB_ge_LL_of_designM hdes (by linarith)))
    (closingCondition_of_closingAtDesignM P hdes.1 hdes.2.2.2.2.2.2.2.2.2.1) hA₀ hA₀L

/-- `HPre.hpre_of_design_A0` at the margin design. -/
theorem hpre_of_designM_A0 (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hA₀ : 1 ≤ A₀) :
    0 < prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ) ∧
    Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        ≤ logPrefactorGev P + Real.log A₀ := by
  have hLB : (100 : ℝ) ≤ P.LB := le_trans hLL (LB_ge_LL_of_designM hdes (by linarith))
  obtain ⟨h0, h1⟩ := hpre_of_designM F r ε Qn P 1 hdes hr hLL le_rfl (by linarith)
  have e : prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
      = A₀ * prefactorQ P.toParams P.T 1 gevreyA (CenvDesign P) P.D0 (Qn : ℝ) := by
    unfold prefactorQ; ring
  have hA₀0 : 0 < A₀ := by linarith
  refine ⟨by rw [e]; positivity, ?_⟩
  rw [e, Real.log_mul (ne_of_gt hA₀0) (ne_of_gt h0)]
  linarith

/-- **`θ₀_fam ≤ A₀ e^{−m}/L = A₀/(L√T)` at the margin design**: `ClosingAtDesignM`'s lower
half, read through `Tail.theta0Q_le_of_closing` at `η = A₀ e^{−m}` (`log(L/η) = log L − log A₀ + m`),
with `hpre` discharged by `hpre_of_designM_A0`. No hypothesis on `r + ε`. -/
theorem theta0Fam_le_of_designM_A0 (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hA₀ : 1 ≤ A₀) :
    theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
      ≤ A₀ * Real.exp (-marginDesign P) / P.LB := by
  obtain ⟨hpre0, hpre⟩ := hpre_of_designM_A0 F r ε Qn P A₀ hdes hr hLL hA₀
  have hP : P.Valid := hdes.1
  have hwr : SideCondWrange P := hdes.2.2.2.2.2.1
  have hcl : ClosingAtDesignM P := hdes.2.2.2.2.2.2.2.2.2.1
  have hl : Zeta23.l P.T ≠ 0 := EFChi.l_ne_zero_of_valid hP
  have hLb : P.toParams.L P.T = P.LB := P.toParams_L hl
  have hww : P.toParams.w = P.w := rfl
  have hw : (0 : ℝ) < P.w := EFChi.w_pos_of_valid hP
  have hw1 : (1 : ℝ) ≤ P.w := hP.one_le_w
  have hwrange : 8 * P.w ≤ P.LB := hwr
  have hLB0 : (0 : ℝ) < P.LB := by linarith
  have hL0 : (0 : ℝ) < P.toParams.L P.T := by rw [hLb]; exact hLB0
  have hA : (0 : ℝ) < gevreyA := by unfold gevreyA; positivity
  have hD0 : (0 : ℝ) ≤ P.D0 := by linarith [one_le_D0Q hP]
  have hA₀0 : (0 : ℝ) < A₀ := by linarith
  have hη0 : (0 : ℝ) < A₀ * Real.exp (-marginDesign P) := by positivity
  have hcc : P.LB / 2 + (logPrefactorGev P + marginDesign P) + Real.log (P.LB / 1)
      ≤ c4 * Real.sqrt (P.w * P.D0 / gevreyA) := hcl.1
  have hc4 : c4 = 4 / Real.exp 1 := rfl
  rw [hc4, div_one] at hcc
  have hlogdiv : Real.log (P.LB / (A₀ * Real.exp (-marginDesign P)))
      = Real.log P.LB - Real.log A₀ + marginDesign P := by
    rw [Real.log_div (ne_of_gt hLB0) (ne_of_gt hη0),
      Real.log_mul (ne_of_gt hA₀0) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hclose : P.toParams.L P.T / 2
        + Real.log (prefactorQ P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ))
        + Real.log (P.toParams.L P.T / (A₀ * Real.exp (-marginDesign P)))
      ≤ (4 / Real.exp 1) * Real.sqrt (P.toParams.w * P.D0 / gevreyA) := by
    rw [hLb, hww, hlogdiv]
    linarith
  have h := theta0Q_le_of_closing (η := A₀ * Real.exp (-marginDesign P)) hL0 hη0 hw hA hD0
    hpre0 hclose
  rw [hLb] at h
  exact h

/-! ## 5. §7's regime inequality and the two clauses at the margin design, for EVERY `r ≥ 3` -/

/-- `L₅ + L₉ ≤ 1` at the margin design. -/
theorem L5_add_L9_le_oneM {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) : L₅ P + L₉ P ≤ 1 :=
  HPre.L5_add_L9_le_one_of hdes.1 hdes.2.2.2.2.2.2.2.2.1

/-- The crude bound `r₂ ≤ 79` at any margin design point with `log Q ≥ 200`. -/
theorem rowR2_le_designM {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) (hr : 3 ≤ r) (hu : 200 ≤ Real.log (Qn : ℝ)) :
    rowR2 F P ≤ 79 := by
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hQn1 : 1 ≤ Qn := by
    have : (1 : ℝ) ≤ (Qn : ℝ) := by rw [← hQ]; linarith
    exact_mod_cast this
  have hLLu : Real.log (Qn : ℝ) ≤ P.LL := LL_ge_log_of_designM hdes hQn1
  have hLL0 : 0 < P.LL := by linarith
  exact HPre.rowR2_le_of_facts hP hQ hLLu (LB_ge_LL_of_designM hdes hLL0.le)
    (w_eq_one_of_designM hdes hr (by linarith)) hu

/-- **The right side of `hregime` TIMES `√T` at the margin design: `≥ 4.5·u³·log u`, `u = log Q`**
(`a ≥ 3/4`, `L ≥ ℒ ≥ u`, `√(T/2π·⟨ℒ⟩_low) ≥ √T` as `⟨ℒ⟩_low ≥ 0.9ℒ ≥ 2π`, `L₅ ≥ 6ℒ log ℒ/T`).
No hypothesis on `r + ε`: the `√T` of the margin cancels the `1/√T` of the pair rows' `1/T`. -/
theorem rhs_lower_designM {F : Family} {r ε : ℝ} {Qn : ℕ} {P : ParamsQ}
    (hdes : DesignOfRecordM F r ε (Qn : ℝ) P) (hu : 200 ≤ Real.log (Qn : ℝ)) :
    4.5 * Real.log (Qn : ℝ) ^ 3 * Real.log (Real.log (Qn : ℝ))
      ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) * Real.sqrt P.T := by
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQ3 : (3 : ℝ) ≤ P.Q := hP.Q_ge
  have hQn1 : 1 ≤ Qn := by
    have : (1 : ℝ) ≤ (Qn : ℝ) := by rw [← hQ]; linarith
    exact_mod_cast this
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Real.log (Qn : ℝ) := ⟨_, rfl⟩
  rw [← hudef] at hu ⊢
  have hu0 : 0 < u := by linarith
  have hLLu : u ≤ P.LL := by rw [hudef]; exact LL_ge_log_of_designM hdes hQn1
  have hLL : 200 ≤ P.LL := le_trans hu hLLu
  have hLL0 : 0 < P.LL := by linarith
  have hLB : P.LL ≤ P.LB := LB_ge_LL_of_designM hdes hLL0.le
  have hLB0 : 0 < P.LB := by linarith
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : 0 < P.T := by linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  have ha : 3 / 4 ≤ P.aQ := hP.a_ge
  have ha0 : 0 ≤ P.aQ := by linarith
  -- `⟨ℒ⟩_low ≥ 0.9ℒ ≥ 2π`, so `√(T/2π·⟨ℒ⟩_low) ≥ √T`
  have hfam : 0.9 * P.LL ≤ famAvgLlow F P := by
    unfold famAvgLlow famAvgL rvmSlack
    have := conductorShift_le_half F
    have := Real.log_two_gt_d9
    linarith
  have hY : Real.sqrt P.T ≤ Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) := by
    apply Real.sqrt_le_sqrt
    have h1 : 2 * Real.pi ≤ famAvgLlow F P := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left h1 hT0.le
  -- `L₅ + L₉ ≥ 6ℒ log ℒ/T`
  have hL59 : 6 * P.LL * Real.log P.LL / P.T ≤ L₅ P + L₉ P := by
    have h9 : 0 ≤ L₉ P := by
      unfold L₉
      obtain ⟨hd0, -⟩ := HPre.dPdlogC_bounds'
      positivity
    have h5 : L₅ P = 6 * P.LL * Real.log P.LL / P.T := rfl
    linarith
  have hlogLL0 : 0 ≤ Real.log P.LL := Real.log_nonneg (by linarith)
  have hL59' : 0 ≤ 6 * P.LL * Real.log P.LL / P.T := by positivity
  have hsT0 : 0 ≤ Real.sqrt P.T := Real.sqrt_nonneg _
  have hsTsq : Real.sqrt P.T * Real.sqrt P.T = P.T := Real.mul_self_sqrt hT0.le
  have hLB2 : P.LL ^ 2 ≤ P.LB ^ 2 := pow_le_pow_left₀ hLL0.le hLB 2
  -- assemble: `(3/4 ℒ² √T · 6ℒ log ℒ/T)·√T = 4.5 ℒ³ log ℒ ≤ (a L² Y (L₅+L₉))·√T`
  have hstep : 3 / 4 * P.LL ^ 2 * Real.sqrt P.T * (6 * P.LL * Real.log P.LL / P.T)
        * Real.sqrt P.T
      ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) * Real.sqrt P.T := by
    apply mul_le_mul_of_nonneg_right _ hsT0
    have h1 : 3 / 4 * P.LL ^ 2 ≤ P.aQ * P.LB ^ 2 := mul_le_mul ha hLB2 (by positivity) ha0
    have h2 : 3 / 4 * P.LL ^ 2 * Real.sqrt P.T
        ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) :=
      mul_le_mul h1 hY hsT0 (by positivity)
    exact mul_le_mul h2 hL59 hL59' (by positivity)
  have hstep2 : 3 / 4 * P.LL ^ 2 * Real.sqrt P.T * (6 * P.LL * Real.log P.LL / P.T)
        * Real.sqrt P.T
      = 4.5 * P.LL ^ 3 * Real.log P.LL := by
    have e : 3 / 4 * P.LL ^ 2 * Real.sqrt P.T * (6 * P.LL * Real.log P.LL / P.T)
          * Real.sqrt P.T
        = Real.sqrt P.T * Real.sqrt P.T * (4.5 * P.LL ^ 3 * Real.log P.LL) / P.T := by ring
    rw [e, hsTsq]
    field_simp
  -- `u ≤ ℒ`
  have hu3 : u ^ 3 ≤ P.LL ^ 3 := pow_le_pow_left₀ hu0.le hLLu 3
  have hlog : Real.log u ≤ Real.log P.LL := Real.log_le_log hu0 hLLu
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have c3 : 4.5 * u ^ 3 * Real.log u ≤ 4.5 * P.LL ^ 3 * Real.log P.LL := by
    have := mul_le_mul hu3 hlog hlogu0 (by positivity)
    linarith
  linarith [hstep, hstep2, c3]

/-- **§7's regime inequality at the margin design, eventually in `Q`, for EVERY `r ≥ 3`**:
`A₀ e^{−m}·(5 + 2√(κ + r₂)) ≤ a L² √(T/2π·⟨ℒ⟩_low)(L₅ + L₉)` for any `κ ≤ 2` (both `κ_C` and
`κ_cert`). With `e^{−m} = 1/√T` this is `A₀(5 + 2√(κ + r₂)) ≤ (RHS)·√T`: the left side is `≤ 23A₀`
(`κ ≤ 2`, `r₂ ≤ 79`), the right side `≥ 4.5 u³ log u` (`rhs_lower_designM`). -/
theorem hregime_M_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r)
    (κ : ℝ) (hκ : κ ≤ 2) (A₀ : ℝ) (hA₀ : 1 ≤ A₀) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      A₀ * Real.exp (-marginDesign P) * (5 + 2 * Real.sqrt (κ + rowR2 F P))
        ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
          * (L₅ P + L₉ P) := by
  have h1 : ∀ᶠ Qn : ℕ in atTop, (200 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 200
  have h2 : ∀ᶠ Qn : ℕ in atTop, 16 * A₀ ≤ Real.log (Real.log (Qn : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (16 * A₀)
  filter_upwards [h1, h2] with Qn hu hlu
  intro P hdes
  have hP : P.Valid := hdes.1
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : 0 < P.T := by linarith
  have hrow := rowR2_le_designM hdes hr hu
  have hrhs := rhs_lower_designM hdes hu
  have hr2 : 0 ≤ rowR2 F P := rowR2_nonneg F P hP
  have hsq : Real.sqrt (κ + rowR2 F P) ≤ 9 := by
    have := Real.sqrt_le_sqrt (show κ + rowR2 F P ≤ 9 ^ 2 by linarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hA₀0 : 0 < A₀ := by linarith
  have hlhs : A₀ * (5 + 2 * Real.sqrt (κ + rowR2 F P)) ≤ 23 * A₀ := by
    have := mul_le_mul_of_nonneg_left hsq hA₀0.le
    linarith
  have hu1 : (1 : ℝ) ≤ Real.log (Qn : ℝ) := by linarith
  have hu3 : 1 ≤ Real.log (Qn : ℝ) ^ 3 := one_le_pow₀ hu1
  have hlu0 : 0 ≤ Real.log (Real.log (Qn : ℝ)) := by linarith
  have hprod : 16 * A₀ ≤ Real.log (Qn : ℝ) ^ 3 * Real.log (Real.log (Qn : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hu3 hlu0
    linarith
  -- divide by `√T = e^{m}`
  have hsT0 : 0 < Real.sqrt P.T := Real.sqrt_pos.mpr hT0
  rw [exp_neg_marginDesign P hT0]
  have key : A₀ * (Real.sqrt P.T)⁻¹ * (5 + 2 * Real.sqrt (κ + rowR2 F P))
      = A₀ * (5 + 2 * Real.sqrt (κ + rowR2 F P)) / Real.sqrt P.T := by ring
  rw [key, div_le_iff₀ hsT0]
  linarith

/-- `JoinCert.tail_clauses_at_design_cert` at the margin design (reads `Valid`, `SideCondWrange`). -/
theorem tail_clauses_at_design_certM (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ) (A₀ : ℝ)
    (hQn : 2 ≤ Qn) (hdes : DesignOfRecordM F r ε (Qn : ℝ) P)
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

/-- `JoinCert.tail_clauses_at_design_of_closing_A0_cert` at the margin design: `hregime` now carries
`A₀ e^{−m}` on the left (the tail target is `θ₀_fam ≤ A₀ e^{−m}/L`). -/
theorem tail_clauses_at_design_of_closing_A0_certM (F : Family) (r ε : ℝ) (Qn : ℕ)
    (P : ParamsQ) (A₀ : ℝ) (hQn : 2 ≤ Qn) (hdes : DesignOfRecordM F r ε (Qn : ℝ) P)
    (hr : 3 ≤ r) (hLL : 100 ≤ P.LL)
    (hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hregime : A₀ * Real.exp (-marginDesign P) * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
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
  have hA₀0 : (0 : ℝ) < A₀ * Real.exp (-marginDesign P) := by positivity
  have hθle := theta0Fam_le_of_designM_A0 F r ε Qn P A₀ hdes hr hLL hA₀
  have hk : (0 : ℝ) ≤ Real.sqrt (F.kappaCert + rowR2 F P) := Real.sqrt_nonneg _
  have hL59 := L5_add_L9_le_oneM hdes
  have ha0 : (0 : ℝ) ≤ P.aQ := by linarith [hP.a_ge]
  have hpos : 0 ≤ P.aQ * P.LB ^ 2 * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P) :=
    mul_nonneg (mul_nonneg ha0 (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hsmall : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
        * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
      ≤ P.aQ * P.LB * Real.sqrt (P.T / (2 * Real.pi) * famAvgLlow F P)
        * (L₅ P + L₉ P) := by
    have hstep : theta0Fam P.toParams P.T A₀ gevreyA (CenvDesign P) P.D0 (Qn : ℝ)
          * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P))
        ≤ A₀ * Real.exp (-marginDesign P) / P.LB
          * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P)) :=
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
    have h5 : 5 * (A₀ * Real.exp (-marginDesign P))
        ≤ A₀ * Real.exp (-marginDesign P) * (5 + 2 * Real.sqrt (F.kappaCert + rowR2 F P)) := by
      linarith [mul_nonneg hA₀0.le hk]
    have h6 := mul_le_mul_of_nonneg_left hL59 hpos
    linarith
  exact tail_clauses_at_design_certM F r ε Qn P A₀ hQn hdes hϱ hA₀ hloc hone hsmall

/-- **§7's two clauses at the margin design, eventually in `Q`, for EVERY `r ≥ 3`** —
`JoinCert.tail_clauses_cert_eventually` WITHOUT `r + ε ≤ 7`. -/
theorem tail_clauses_certM_eventually (F : Family) (r ε : ℝ) (hr : 3 ≤ r)
    (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ →
      ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧
        (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
          + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) ∧
        (∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q,
          Zeta23.Assembly.TailInputsD (EFChi.famZc q χ) P.toParams P.T P.D0 θ₀) := by
  have h1 : ∀ᶠ Qn : ℕ in atTop, (200 : ℝ) ≤ Real.log (Qn : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 200
  filter_upwards [h1,
    hregime_M_eventually F r ε hr F.kappaCert (kappaCert_le_two F) A₀ hA₀,
    eventually_ge_atTop 2] with Qn hu hreg hQn
  intro P hdes hϱ
  have hQn1 : 1 ≤ Qn := by omega
  have hLL : 100 ≤ P.LL := le_trans (by linarith) (LL_ge_log_of_designM hdes hQn1)
  exact tail_clauses_at_design_of_closing_A0_certM F r ε Qn P A₀ hQn hdes hr hLL hϱ hA₀ hloc
    (hreg P hdes)

/-! ## 6. The assembly at the proved buffer row along the margin design, and the rate -/

/-- `JoinProved.propBracketProved_le_budgetTotalProved` — the same exact ring identity, without the
(unused) design hypothesis. -/
theorem propBracketProved_le_budgetTotalProved' (A₀ : ℝ) (F : Family) (P : ParamsQ) (θ₀ : ℝ)
    (hpair : 4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
        + rowR5 F P θ₀ ^ 2 ≤ L₅ P + L₉ P) :
    propBracketProved A₀ F P θ₀ ≤ budgetTotalProved A₀ F P := by
  have key : budgetTotalProved A₀ F P - propBracketProved A₀ F P θ₀
      = (L₅ P + L₉ P)
        - (4 * rowR4 F P θ₀ + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P)
            + rowR5 F P θ₀ ^ 2) := by
    unfold budgetTotalProved budgetTotal propBracketProved minorRows rowR1 rowR2 rowR3Proved
    ring
  linarith

/-- `JoinProved.assembly_clauses_at_design_proved` over the two facts of the design it reads
(`Valid`, `SideCondWrange`; `buffer_row_proved_of_valid`, `pair_rows_of_valid`). -/
theorem assembly_clauses_at_design_proved_of_valid (F : Family) (Qn : ℕ) (P : ParamsQ)
    (θ₀ A₀ : ℝ) (hQn : 2 ≤ Qn) (hP : P.Valid) (hwr : SideCondWrange P) (hθ : 0 ≤ θ₀)
    (hA₀ : 1 ≤ A₀)
    (hloc : ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q, ∀ t : ℝ,
      NcountQ q χ t (t + 1) ≤ A₀ * Real.log ((q : ℝ) * (|t| + 3)))
    (htr : (1 - rowR1 F P) * NfamQ P F Qn ≤ trGhatFam P F Qn)
    (hfrob : frobSqGhatFam P F Qn ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn)
    (hNII : FamNIIUpper F Qn P A₀) (hrvm : FamRvMLower F Qn P)
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
          + 2 * r₅ * Real.sqrt (F.kappaCert + r₂) + r₅ ^ 2 ≤ budgetTotalProved A₀ F P ∧
      (2 - F.kappaCert - budgetTotalProved A₀ F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
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
  -- §10.3's rows 3 (PROVED), 4, 5 and the bracket
  have hNII' : NIIFamQ P F Qn ≤ rowR3Proved A₀ P * NfamQ P F Qn := by
    unfold rowR3Proved
    exact buffer_row_proved_of_valid F Qn P A₀ hP hA₀ hloc hNII hrvm
  obtain ⟨hBtr', hBF'⟩ := pair_rows_of_valid F Qn P θ₀ hP hwr hθ hrvm
  have hbr := propBracketProved_le_budgetTotalProved' A₀ F P θ₀ hpair
  -- §9's family display joined to §7.3's pair split, then Prop 3.1 (generic in `κ`, `r₃`)
  have hdisp := EFChi.certificate_display_fam_of_bridge P hP F Qn θ₀ EFChi.famZc
    (EFChi.famZeroConfig_famZc F Qn hQn) (EFChi.famGramBridge_famZc P hP F Qn hQn hwr) hwr
    (abs_trGz_sub_trAhat_fam_le_Btr P F Qn θ₀ EFChi.famZc hl hblock)
    (sqrt_frobSqAhat_sub_sqrt_frobSqGz_fam_le_BF P F Qn θ₀ EFChi.famZc hl hB0 hblock)
    hBtr0 hBF0
  have hlast := prop_3_1_pair_moment_certificate (NfamQ_nonneg P F Qn) hBtr0 hBF0 hκ hdisp
    htr hfrob hNII' hBtr' hBF'
  have hN : (0 : ℝ) ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hbracket : propBracketProved A₀ F P θ₀
      = 4 * rowR1 F P + rowR2 F P + 3 * rowR3Proved A₀ P + 4 * rowR4 F P θ₀
        + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P) + rowR5 F P θ₀ ^ 2 := rfl
  refine ⟨rowR1 F P, rowR2 F P, rowR3Proved A₀ P, rowR4 F P θ₀, rowR5 F P θ₀, θ₀,
    hθ, htr, hfrob, hNII', hBtr', hBF', ?_, ?_⟩
  · rw [← hbracket]; exact hbr
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hN) hlast
    linarith [hbr, hbracket.le, hbracket.ge]

/-- **The eight clauses at EVERY margin design point, eventually in `Q`, at the proved buffer row,
for EVERY `r ≥ 3`** — `JoinProved.assembly_eventually_proved` WITHOUT `r + ε ≤ 7`. -/
theorem assembly_eventually_provedM (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hNII : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      FamNIIUpper F Qn P A₀)
    (hfrob : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      frobSqGhatFam P F Qn ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn)
    (hrvm : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      FamRvMLower F Qn P) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      ∃ r₁ r₂ r₃ r₄ r₅ θ₀ : ℝ,
        0 ≤ θ₀ ∧
        (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn ∧
        frobSqGhatFam P F Qn ≤ (F.kappaCert + r₂) * NfamQ P F Qn ∧
        NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn ∧
        Btr P F Qn θ₀ ≤ r₄ * NfamQ P F Qn ∧
        BF P F Qn θ₀ ≤ r₅ * Real.sqrt (NfamQ P F Qn) ∧
        4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
            + 2 * r₅ * Real.sqrt (F.kappaCert + r₂) + r₅ ^ 2 ≤ budgetTotalProved A₀ F P ∧
        (2 - F.kappaCert - budgetTotalProved A₀ F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  filter_upwards [trace_row_eventually_M F r ε hr hε,
    tail_clauses_certM_eventually F r ε hr A₀ hA₀ hloc, hNII, hfrob, hrvm,
    eventually_ge_atTop 2] with Qn htr htail hs hf hv hQn
  intro P hdes
  have hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.1]; exact gevreyProfile_rhoTwoQ
  obtain ⟨θ₀, hθ, hpair, hblock⟩ := htail P hdes hϱ
  exact assembly_clauses_at_design_proved_of_valid F Qn P θ₀ A₀ hQn hdes.1 hdes.2.2.2.2.2.1 hθ
    hA₀ (hloc_moduli_of_uniform F Qn hQn hloc) (htr P hdes) (hf P hdes) (hs P hdes) (hv P hdes)
    hpair hblock

/-- **`JoinProved.assembly_at_lamStar_proved` along the margin design, WITHOUT `r + ε ≤ 7`**: the
eight clauses at a margin design point at every large `Q` (`exists_designOfRecordM`), from `A₀`,
`hloc`, `hNII`, `hfrob`, `hrvm` along `DesignOfRecordM`. -/
theorem assembly_at_lamStar_provedM (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hNII : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      FamNIIUpper F Qn P A₀)
    (hfrob : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      frobSqGhatFam P F Qn ≤ (F.kappaCert + rowR2 F P) * NfamQ P F Qn)
    (hrvm : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      FamRvMLower F Qn P) :
    ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ∃ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P ∧
        ∃ r₁ r₂ r₃ r₄ r₅ θ₀ : ℝ,
          0 ≤ θ₀ ∧
          (1 - r₁) * NfamQ P F Qn ≤ trGhatFam P F Qn ∧
          frobSqGhatFam P F Qn ≤ (F.kappaCert + r₂) * NfamQ P F Qn ∧
          NIIFamQ P F Qn ≤ r₃ * NfamQ P F Qn ∧
          Btr P F Qn θ₀ ≤ r₄ * NfamQ P F Qn ∧
          BF P F Qn θ₀ ≤ r₅ * Real.sqrt (NfamQ P F Qn) ∧
          4 * r₁ + r₂ + 3 * r₃ + 4 * r₄
              + 2 * r₅ * Real.sqrt (F.kappaCert + r₂) + r₅ ^ 2 ≤ budgetTotalProved A₀ F P ∧
          (2 - F.kappaCert - budgetTotalProved A₀ F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  obtain ⟨Q₁, hQ₁⟩ := exists_designOfRecordM F r ε hr hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (assembly_eventually_provedM F r ε hr hε A₀ hA₀ hloc hNII hfrob hrvm)
  refine ⟨max Q₁ (N : ℝ), fun Qn hQn => ?_⟩
  obtain ⟨P, hdes⟩ := hQ₁ (Qn : ℝ) (le_trans (le_max_left _ _) hQn)
  have hNQ : N ≤ Qn := by exact_mod_cast le_trans (le_max_right _ _) hQn
  exact ⟨P, hdes, hN Qn hNQ P hdes⟩

/-- **`budgetTotalProved = O(log log Q/log Q)` along every MARGIN design map** —
`JoinProved.budgetTotalProved_isBigO_core` with `budgetTotal_isBigO_of_designM` and
`designM_D0_isBigO`. -/
theorem budgetTotalProved_isBigO_of_designM (A₀ : ℝ) (hA₀ : 1 ≤ A₀) (F : Family) (r ε : ℝ)
    (hr : 3 ≤ r) (hε : 0 < ε) (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop, DesignOfRecordM F r ε Q (design Q)) :
    (fun Q => budgetTotalProved A₀ F (design Q))
      =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q) :=
  budgetTotalProved_isBigO_core A₀ hA₀ F r ε hr hε design
    (hdesign.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (budgetTotal_isBigO_of_designM F r ε hr hε design hdesign)
    (designM_D0_isBigO F r ε hr hε design hdesign)


/-! ## 6b. Corollary 3's parity rows: `FamNIIUpper` and `FamRvMLower` at the four parity families.

Both of §10's counting rows are statements about the FULL character set, so neither transfers to
a parity family for free; §12.3's count (`Budget.ParityCount`, `|2|𝔉_Q| − Σ_q φ*(q)| ≤ Q`) is what
converts them, at a cost of `Q` per row:

  * `FamNIIUpper` — `Budget.NIIFam_avg_le` is `F`-generic but prices each modulus at `φ*(q)`,
    i.e. at about TWICE a parity family's own weight. So the parity families carry the buffer row
    at `4A₀` where the full families carry it at `2A₀` (`famNIIUpper_parity_of_valid`); the
    doubling is free downstream, since every consumer of `A₀` is `A₀`-generic and
    `budgetTotalProved A₀ F` is `O(log log Q/log Q)` at every fixed `A₀`.
  * `FamRvMLower` — `Budget.famRvMLower_parity_of_design` already covers the two `Icc 2 Qn`
    parity families; `famRvMLower_parity_dyadic_of_design` below is its dyadic twin, with
    `Dyadic.famLogCond_dyadic_bound` in place of `famLogCond_qle_bound` and the §12.3 count
    against `Budget.two_sizeR_parity_dyadic`. The residue grows from `28` to `30`.

Nothing here reads `D₀`, so §2's `eventually_M_of_D0free` carries all four rows to the margin
design. -/

/-- **The §12.2+§12.3 residue is eventually below any fixed multiple of `|𝔉_Q|`, for the two
DYADIC parity families** — `Budget.residue_small_parity_eventually`'s dyadic twin, at the larger
constant `30` and against `|𝔉_Q| ≥ ½(|𝔉^dyad_Q| − Q)`. -/
theorem residue_small_parity_dyadic_eventually {F : Family} (hF : ¬ F.IsFull)
    (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.dyadic.moduli Qn) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 30 * (N : ℝ) * (1 + Real.log N) ^ 3 ≤ ε * Family.sizeR F N := by
  have hc : (0 : ℝ) < ε * (3 / 4 * (18 / Real.pi ^ 4)) := by
    have : (0 : ℝ) < 18 / Real.pi ^ 4 := by positivity
    positivity
  have hH : Tendsto (fun x : ℝ =>
      60 * ((1 + Real.log x) ^ 3 / x) + 9 * ε * ((1 + Real.log x) ^ 2 / x))
      atTop (nhds 0) := by
    simpa using (one_add_log_cube_div_tendsto''.const_mul 60).add
      (one_add_log_sq_div_tendsto'.const_mul (9 * ε))
  have hev : ∀ᶠ x : ℝ in atTop,
      60 * ((1 + Real.log x) ^ 3 / x) + 9 * ε * ((1 + Real.log x) ^ 2 / x)
        < ε * (3 / 4 * (18 / Real.pi ^ 4)) := hH.eventually_lt_const hc
  have hevN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  filter_upwards [hevN, eventually_ge_atTop 2] with N hN1 hN2
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hsq1 : (1 : ℝ) ≤ (1 + Real.log (N : ℝ)) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hN1.le (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
  have hexpand : (60 * ((1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ))
        + 9 * ε * ((1 + Real.log (N : ℝ)) ^ 2 / (N : ℝ))) * (N : ℝ) ^ 2
      = 60 * (N : ℝ) * (1 + Real.log N) ^ 3
        + 9 * ε * (N : ℝ) * (1 + Real.log N) ^ 2 := by
    field_simp
  rw [hexpand] at hmul
  have hsz2 := mul_le_mul_of_nonneg_left (sizeR_dyadic_lower N hN2) hε.le
  have hpar := (abs_le.mp (two_sizeR_parity_dyadic hF N (hmod N))).1
  have hqeq := sizeR_dyadic_eq N
  have hsQ : Family.sizeR Family.dyadic N - (N : ℝ) ≤ 2 * Family.sizeR F N := by
    rw [hqeq]; linarith
  have hsQ' := mul_le_mul_of_nonneg_left hsQ hε.le
  have hstepN : (N : ℝ) * 1 ≤ (N : ℝ) * (1 + Real.log N) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq1 (by positivity : (0 : ℝ) ≤ (N : ℝ))
  rw [mul_one] at hstepN
  have hNsq : ε * (N : ℝ) ≤ ε * ((N : ℝ) * (1 + Real.log N) ^ 2) :=
    mul_le_mul_of_nonneg_left hstepN hε.le
  linarith [hmul, hsz2, hsQ', hNsq]

theorem two_le_log_eight_pi : (2 : ℝ) ≤ Real.log (8 * Real.pi) := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 1 ^ (2 : ℕ) = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hle : Real.exp 1 ^ (2 : ℕ) ≤ (2.7182818286 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he.le 2
  rw [← h2]
  nlinarith

/-- **`FamNIIUpper` at `4A₀` for a PARITY family**, from `Budget.NIIFam_avg_le` (which prices each
modulus at the FULL `φ*(q)`), §12.3's count `Σ_q φ*(q) ≤ 2|𝔉_Q| + Q`
(`Budget.ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn`) and §12.2's conductor average on the
partner FULL family (`hcond`, residue `R`). The side condition `Q + R ≤ 2|𝔉_Q|` is what makes the
two costs of the transfer negligible; `1 ≤ ℒ − ⟨shift⟩ + log 8π` supplies the rest. -/
theorem famNIIUpper_parity_of_valid {F Ff : Family} (hF : ¬ F.IsFull) (hFf : Ff.IsFull)
    (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn) (hQ : P.Q = (Qn : ℝ))
    (hmod : F.moduli Qn = Ff.moduli Qn) (hsh : F.conductorShift = Ff.conductorShift)
    {A₀ R : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hR : 0 ≤ R)
    (hcond : (∑ q ∈ Ff.moduli Qn, (phiStar q : ℝ) * Real.log q)
      ≤ Ff.sizeR Qn * (Real.log Qn - Ff.conductorShift) + R)
    (hres : (Qn : ℝ) + R ≤ 2 * F.sizeR Qn) :
    FamNIIUpper F Qn P (4 * A₀) := by
  have hbase := NIIFam_avg_le P hP F Qn hQn hA₀ hloc
  have hmodsum : ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T))
      = ∑ q ∈ Ff.moduli Qn, (phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T)) := by rw [hmod]
  have hsplit : ∑ q ∈ Ff.moduli Qn, (phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T))
      = (∑ q ∈ Ff.moduli Qn, (phiStar q : ℝ) * Real.log q)
        + Ff.sizeR Qn * Real.log (4 * P.T) := by
    rw [sizeR_eq_sum_phiStar hFf, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have hcount : Ff.sizeR Qn ≤ 2 * F.sizeR Qn + (Qn : ℝ) := by
    have h := (abs_le.mp (ParityCount.abs_two_sizeR_sub_sum_phiStar_le_Qn hF Qn)).1
    have he : ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) = Ff.sizeR Qn := by
      rw [hmod, ← sizeR_eq_sum_phiStar hFf]
    rw [he] at h; linarith
  set M : ℝ := P.LL - F.conductorShift + Real.log (8 * Real.pi) with hMdef
  have hMeq : M = (Real.log (Qn : ℝ) - Ff.conductorShift) + Real.log (4 * P.T) := by
    have h := LL_add_log8pi_eq P hP Qn hQn hQ
    rw [hMdef, hsh]; linarith
  have hM1 : (1 : ℝ) ≤ M := by
    have hLL : (0 : ℝ) < P.LL := EFChi.LL_pos_of_valid hP
    have hs : F.conductorShift ≤ 1 / 2 := conductorShift_le_half F
    have := two_le_log_eight_pi
    rw [hMdef]; linarith
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hD0 : (0 : ℝ) ≤ P.D0 := by linarith [hP.two_le_D0]
  have hA0D : (0 : ℝ) ≤ 3 * A₀ * P.D0 := by nlinarith
  have hkey : ∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T))
      ≤ 4 * M * F.sizeR Qn := by
    rw [hmodsum, hsplit]
    have h1 : (∑ q ∈ Ff.moduli Qn, (phiStar q : ℝ) * Real.log q)
          + Ff.sizeR Qn * Real.log (4 * P.T)
        ≤ Ff.sizeR Qn * M + R := by
      have e : Ff.sizeR Qn * M + R
          = (Ff.sizeR Qn * (Real.log Qn - Ff.conductorShift) + R)
            + Ff.sizeR Qn * Real.log (4 * P.T) := by rw [hMeq]; ring
      rw [e]; linarith
    have h2 : Ff.sizeR Qn * M + R ≤ (2 * F.sizeR Qn + (Qn : ℝ)) * M + R := by
      have := mul_le_mul_of_nonneg_right hcount hM0
      linarith
    have h3 : (2 * F.sizeR Qn + (Qn : ℝ)) * M + R ≤ 4 * M * F.sizeR Qn := by
      have ha : ((Qn : ℝ) + R) * M ≤ (2 * F.sizeR Qn) * M := mul_le_mul_of_nonneg_right hres hM0
      have hb : R * 1 ≤ R * M := mul_le_mul_of_nonneg_left hM1 hR
      nlinarith [ha, hb]
    linarith
  unfold FamNIIUpper
  calc NIIFamQ P F Qn
      ≤ 3 * A₀ * P.D0
          * (∑ q ∈ F.moduli Qn, (phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T))) := hbase
    _ ≤ 3 * A₀ * P.D0 * (4 * M * F.sizeR Qn) := mul_le_mul_of_nonneg_left hkey hA0D
    _ = 3 * (4 * A₀) * P.D0 * (P.LL - F.conductorShift + Real.log (8 * Real.pi))
          * F.sizeR Qn := by rw [hMdef]; ring

theorem Qn_le_cube {Qn : ℕ} (hQn : 2 ≤ Qn) :
    (Qn : ℝ) ≤ (Qn : ℝ) * (1 + Real.log Qn) ^ 3 := by
  have hQnR : (2 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn
  have hlog0 : (0 : ℝ) ≤ Real.log (Qn : ℝ) := Real.log_nonneg (by linarith)
  nlinarith [mul_nonneg hlog0 hlog0, mul_nonneg (mul_nonneg hlog0 hlog0) hlog0]

/-- `FamNIIUpper F Qn P (4A₀)` along the design for the two DYADIC parity families. -/
theorem famNIIUpper_parity_dyadic_of_design {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = Family.dyadic.conductorShift)
    (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.dyadic.moduli Qn) (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      FamNIIUpper F Qn P (4 * A₀) := by
  filter_upwards [residue_small_parity_dyadic_eventually hF hmod (ε := 1) one_pos,
    eventually_ge_atTop 2] with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hQnR : (2 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn
  have hlog0 : (0 : ℝ) ≤ Real.log (Qn : ℝ) := Real.log_nonneg (by linarith)
  have hcube := Qn_le_cube hQn
  have hcond : (∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Real.log q)
      ≤ Family.sizeR Family.dyadic Qn * (Real.log Qn - Family.dyadic.conductorShift)
        + 28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 := by
    have h := (abs_le.mp (famLogCond_dyadic_bound Qn hQn)).2
    simp only [Family.conductorShift]
    linarith
  refine famNIIUpper_parity_of_valid hF Family.isFull_dyadic P hP Qn hQn hQ (hmod Qn) hsh hA₀
    hloc (by positivity) hcond ?_
  linarith [hres]

/-- `FamNIIUpper F Qn P (4A₀)` along the design for the two `Icc 2 Qn` parity families. -/
theorem famNIIUpper_parity_qle_of_design {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = Family.qle.conductorShift)
    (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.qle.moduli Qn) (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      FamNIIUpper F Qn P (4 * A₀) := by
  filter_upwards [residue_small_parity_eventually hF hmod (ε := 1) one_pos,
    eventually_ge_atTop 2] with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hcube := Qn_le_cube hQn
  have hcond : (∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Real.log q)
      ≤ Family.sizeR Family.qle Qn * (Real.log Qn - Family.qle.conductorShift)
        + 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 :=
    by linarith [(abs_le.mp (famLogCond_qle_bound Qn hQn)).2]
  refine famNIIUpper_parity_of_valid hF Family.isFull_qle P hP Qn hQn hQ (hmod Qn) hsh hA₀
    hloc (by positivity) hcond ?_
  linarith [hres]

/-- **`FamRvMLower`'s content for the two DYADIC parity families, both residues explicit** — the
dyadic twin of `Budget.famRvM_lower_with_residue_parity`: the per-modulus weight is `|F.chars q|`
(`famRvM_lower_weight`, `sizeR_eq_sum_weight`) and §12.2's dyadic conductor bound
(`Dyadic.famLogCond_dyadic_bound`, residue `28`) is transported across §12.3's count
(`ParityCount.abs_two_sum_weight_log_sub_le`, `two_sizeR_parity_dyadic`); the residue grows from
`28` to `30`. `famAvgL F P = famAvgL Family.dyadic P` because the shift agrees. -/
theorem famRvM_lower_with_residue_parity_dyadic (P : ParamsQ) (hP : P.Valid) {F : Family}
    (hF : ¬ F.IsFull) (hsh : F.conductorShift = Family.dyadic.conductorShift) (Qn : ℕ)
    (hQn : 2 ≤ Qn) (hmod : F.moduli Qn = Family.dyadic.moduli Qn)
    (hQ : P.Q = (Qn : ℝ)) {A T₀ : ℝ} (hA : 0 ≤ A)
    (hrvm : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
        ∀ T : ℝ, T₀ ≤ T →
          |(Zeta23.ThmE.NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ThmE.ell1q q T|
            ≤ A * Real.log (q * (T + 2)))
    (hT : T₀ ≤ P.T) :
    F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgL F P)
        - P.T / (2 * Real.pi) * (30 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
        - A * (F.sizeR Qn * Real.log ((Qn : ℝ) * (P.T + 2)))
      ≤ NfamQ P F Qn := by
  have hbase := famRvM_lower_weight P F Qn hQn hrvm hT
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hT300 : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hM : (0 : ℝ) ≤ P.T / (2 * Real.pi) := by positivity
  have hdiv : (0 : ℝ) < P.T / (2 * Real.pi) := div_pos hT0 (by linarith)
  set G : ℝ := Real.log (P.T / (2 * Real.pi)) + 2 * Real.log 2 - 1 with hG
  have hLLsplit : P.LL = Real.log (Qn : ℝ) + Real.log (P.T / (2 * Real.pi)) := by
    unfold ParamsQ.LL
    rw [hQ, show (Qn : ℝ) * P.T / (2 * Real.pi) = (Qn : ℝ) * (P.T / (2 * Real.pi)) by ring]
    exact Real.log_mul (ne_of_gt hQ0) (ne_of_gt hdiv)
  have hell : ∀ q ∈ F.moduli Qn, Zeta23.ThmE.ell1q q P.T = Real.log (q : ℝ) + G := by
    intro q hq
    have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    unfold Zeta23.ThmE.ell1q
    rw [show (q : ℝ) * P.T / (2 * Real.pi) = (q : ℝ) * (P.T / (2 * Real.pi)) by ring,
      Real.log_mul (ne_of_gt hqR) (ne_of_gt hdiv), hG]
    ring
  have hsum1 : ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Zeta23.ThmE.ell1q q P.T
      = (∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Real.log q) + F.sizeR Qn * G := by
    rw [sizeR_eq_sum_weight, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [hell q hq]; ring
  have hsum2 : ∑ q ∈ F.moduli Qn,
        (((F.chars q).card : ℕ) : ℝ) * Real.log ((q : ℝ) * (P.T + 2))
      ≤ F.sizeR Qn * Real.log ((Qn : ℝ) * (P.T + 2)) := by
    rw [sizeR_eq_sum_weight, Finset.sum_mul]
    refine Finset.sum_le_sum (fun q hq => ?_)
    have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
    have hqle : (q : ℝ) ≤ (Qn : ℝ) := by
      exact_mod_cast ParityCount.le_Qn_of_mem hq
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    have hmono : Real.log ((q : ℝ) * (P.T + 2)) ≤ Real.log ((Qn : ℝ) * (P.T + 2)) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hsplitL : ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) *
        (P.T / (2 * Real.pi) * Zeta23.ThmE.ell1q q P.T
          - A * Real.log ((q : ℝ) * (P.T + 2)))
      = P.T / (2 * Real.pi)
          * (∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Zeta23.ThmE.ell1q q P.T)
        - A * (∑ q ∈ F.moduli Qn,
            (((F.chars q).card : ℕ) : ℝ) * Real.log ((q : ℝ) * (P.T + 2))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  -- §12.3's conductor average, against §12.2's `famLogCond_dyadic_bound`
  have hlogQ0 : (0 : ℝ) ≤ Real.log (Qn : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL2 : Real.log 2 ≤ Real.log (Qn : ℝ) := Real.log_le_log (by norm_num) hQnR
  have hshv : Family.dyadic.conductorShift = 1 / 2 - Real.log 2 / 3 := rfl
  have hL12 : (0 : ℝ) ≤ Real.log (Qn : ℝ) - Family.dyadic.conductorShift := by
    rw [hshv]; linarith
  have hcube : Real.log (Qn : ℝ) ≤ (1 + Real.log (Qn : ℝ)) ^ 3 := by
    nlinarith [hlogQ0, mul_nonneg hlogQ0 hlogQ0,
      mul_nonneg (mul_nonneg hlogQ0 hlogQ0) hlogQ0]
  have hNL : (Qn : ℝ) * Real.log (Qn : ℝ) ≤ (Qn : ℝ) * (1 + Real.log (Qn : ℝ)) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  have hshift_le : Family.dyadic.conductorShift ≤ 1 / 2 := conductorShift_le_half Family.dyadic
  have hshift_nn : 0 ≤ Family.dyadic.conductorShift := conductorShift_nonneg Family.dyadic
  have hQsh : (Qn : ℝ) * (Real.log (Qn : ℝ) - Family.dyadic.conductorShift)
      ≤ (Qn : ℝ) * (1 + Real.log (Qn : ℝ)) ^ 3 := by
    have : Real.log (Qn : ℝ) - Family.dyadic.conductorShift ≤ (1 + Real.log (Qn : ℝ)) ^ 3 := by
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2s : ∑ q ∈ F.moduli Qn, 2 * (((F.chars q).card : ℕ) : ℝ) * Real.log q
      = 2 * ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Real.log q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hpc := abs_le.mp (ParityCount.abs_two_sum_weight_log_sub_le hF Qn)
  rw [h2s] at hpc
  have hfl := (abs_le.mp (famLogCond_dyadic_bound Qn hQn)).1
  rw [← hshv] at hfl
  rw [← hmod] at hfl
  have hpar := (abs_le.mp (two_sizeR_parity_dyadic hF Qn hmod)).2
  have hqeq := sizeR_dyadic_eq Qn
  have hsQ : 2 * F.sizeR Qn - (Qn : ℝ) ≤ Family.sizeR Family.dyadic Qn := by
    rw [hqeq]; linarith
  have hmul := mul_le_mul_of_nonneg_right hsQ hL12
  have hS : F.sizeR Qn * (Real.log (Qn : ℝ) - Family.dyadic.conductorShift)
        - 30 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3
      ≤ ∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Real.log q := by
    nlinarith [hpc.1, hfl, hmul, hNL, hQsh, hlogQ0, hQ0]
  have hfa : famAvgL F P = (Real.log (Qn : ℝ) - Family.dyadic.conductorShift) + G := by
    unfold famAvgL
    rw [hsh, hLLsplit, hG]
    ring
  have step1 : P.T / (2 * Real.pi)
        * ((F.sizeR Qn * (Real.log (Qn : ℝ) - Family.dyadic.conductorShift)
              - 30 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
            + F.sizeR Qn * G)
      ≤ P.T / (2 * Real.pi)
        * (∑ q ∈ F.moduli Qn, (((F.chars q).card : ℕ) : ℝ) * Zeta23.ThmE.ell1q q P.T) := by
    rw [hsum1]
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  have step2 : A * (∑ q ∈ F.moduli Qn,
        (((F.chars q).card : ℕ) : ℝ) * Real.log ((q : ℝ) * (P.T + 2)))
      ≤ A * (F.sizeR Qn * Real.log ((Qn : ℝ) * (P.T + 2))) :=
    mul_le_mul_of_nonneg_left hsum2 hA
  have heq : F.sizeR Qn * (P.T / (2 * Real.pi) * famAvgL F P)
        - P.T / (2 * Real.pi) * (30 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
      = P.T / (2 * Real.pi)
        * ((F.sizeR Qn * (Real.log (Qn : ℝ) - Family.dyadic.conductorShift)
              - 30 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3)
            + F.sizeR Qn * G) := by
    rw [hfa]; ring
  refine le_trans ?_ hbase
  rw [hsplitL, heq]
  linarith

/-- **`FamRvMLower` ALONG THE DESIGN OF RECORD FOR THE TWO DYADIC PARITY FAMILIES** —
`Budget.famRvMLower_parity_of_design`'s dyadic twin, with
`famRvM_lower_with_residue_parity_dyadic` and `residue_small_parity_dyadic_eventually` in place
of their `Icc 2 Qn` counterparts. Both residues are again absorbed into half of `rvmSlack`. -/
theorem famRvMLower_parity_dyadic_of_design {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = Family.dyadic.conductorShift)
    (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.dyadic.moduli Qn) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord F r ε (n : ℝ) P → FamRvMLower F n P := by
  obtain ⟨A, T₀, hA, hrvm⟩ := EFChi.rvmChi_main_uniform
  have hTtop : Tendsto (fun n : ℕ => Twin (n : ℝ) r ε) atTop atTop := by
    have hre : (0 : ℝ) < r + ε := by linarith
    exact (tendsto_rpow_atTop hre).comp tendsto_log_nat_atTop
  filter_upwards [residue_small_parity_dyadic_eventually hF hmod (ε := 1 / 200) (by norm_num),
    rvm_error_small r ε A hr hε hA, hTtop.eventually_ge_atTop T₀,
    eventually_ge_atTop 2] with n hres herr hT0 hn2
  intro P hdes
  obtain ⟨hP, hQ, hT, -⟩ := hdes
  have hTpos : (0 : ℝ) < P.T := T_posQ hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey := famRvM_lower_with_residue_parity_dyadic P hP hF hsh n hn2 (hmod n) hQ hA.le hrvm
    (by rw [hT]; exact hT0)
  have hM0 : (0 : ℝ) < P.T / (2 * Real.pi) := by positivity
  have hS0 : (0 : ℝ) ≤ Family.sizeR F n := by unfold Family.sizeR; positivity
  have h1 : P.T / (2 * Real.pi) * (30 * (n : ℝ) * (1 + Real.log n) ^ 3)
      ≤ Family.sizeR F n * (P.T / (2 * Real.pi)) / 200 := by
    have h := mul_le_mul_of_nonneg_left hres hM0.le
    nlinarith [h]
  have hlogpos : (0 : ℝ) ≤ Real.log ((n : ℝ) * (P.T + 2)) := by
    apply Real.log_nonneg
    have hn : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    nlinarith
  have h2 : A * (Family.sizeR F n * Real.log ((n : ℝ) * (P.T + 2)))
      ≤ Family.sizeR F n * (P.T / (2 * Real.pi)) / 200 := by
    have herr' : 400 * Real.pi * A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T := by
      rw [hT]; exact herr
    have hstep : A * Real.log ((n : ℝ) * (P.T + 2)) ≤ P.T / (2 * Real.pi) / 200 := by
      rw [div_div, le_div_iff₀ (by positivity)]
      nlinarith [herr']
    nlinarith [mul_le_mul_of_nonneg_left hstep hS0]
  unfold FamRvMLower famAvgLlow rvmSlack
  have hexp : Family.sizeR F n * (P.T / (2 * Real.pi) * (famAvgL F P - 1 / 100))
      = Family.sizeR F n * (P.T / (2 * Real.pi) * famAvgL F P)
        - Family.sizeR F n * (P.T / (2 * Real.pi)) / 200
        - Family.sizeR F n * (P.T / (2 * Real.pi)) / 200 := by ring
  rw [hexp]
  linarith [hkey, h1, h2]

/-! ### The four parity rows along the MARGIN design (`eventually_M_of_D0free`) -/

theorem hfrob_evenDyadic_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.evenDyadic r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.evenDyadic Qn
        ≤ (Family.evenDyadic.kappaCert + rowR2 Family.evenDyadic P)
            * NfamQ P Family.evenDyadic Qn :=
  eventually_M_of_D0free Family.evenDyadic r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.evenDyadic Qn
      ≤ (Family.evenDyadic.kappaCert + rowR2 Family.evenDyadic P) * NfamQ P Family.evenDyadic Qn)
    (fun _ _ _ h => h) (HFrob.hfrob_evenDyadic_of_design r ε hr hε)

theorem hfrob_oddDyadic_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.oddDyadic r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.oddDyadic Qn
        ≤ (Family.oddDyadic.kappaCert + rowR2 Family.oddDyadic P)
            * NfamQ P Family.oddDyadic Qn :=
  eventually_M_of_D0free Family.oddDyadic r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.oddDyadic Qn
      ≤ (Family.oddDyadic.kappaCert + rowR2 Family.oddDyadic P) * NfamQ P Family.oddDyadic Qn)
    (fun _ _ _ h => h) (HFrob.hfrob_oddDyadic_of_design r ε hr hε)

theorem hfrob_evenQle_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.evenQle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.evenQle Qn
        ≤ (Family.evenQle.kappaCert + rowR2 Family.evenQle P) * NfamQ P Family.evenQle Qn :=
  eventually_M_of_D0free Family.evenQle r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.evenQle Qn
      ≤ (Family.evenQle.kappaCert + rowR2 Family.evenQle P) * NfamQ P Family.evenQle Qn)
    (fun _ _ _ h => h) (HFrob.hfrob_evenQle_of_design r ε hr hε)

theorem hfrob_oddQle_of_designM (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM Family.oddQle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.oddQle Qn
        ≤ (Family.oddQle.kappaCert + rowR2 Family.oddQle P) * NfamQ P Family.oddQle Qn :=
  eventually_M_of_D0free Family.oddQle r ε hr hε
    (fun Qn P => frobSqGhatFam P Family.oddQle Qn
      ≤ (Family.oddQle.kappaCert + rowR2 Family.oddQle P) * NfamQ P Family.oddQle Qn)
    (fun _ _ _ h => h) (HFrob.hfrob_oddQle_of_design r ε hr hε)

theorem famRvMLower_parity_of_designM {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = 1 / 2) (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.qle.moduli Qn)
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      FamRvMLower F Qn P :=
  eventually_M_of_D0free F r ε hr hε (fun Qn P => FamRvMLower F Qn P)
    (fun _ _ _ h => h) (famRvMLower_parity_of_design hF hsh hmod r ε hr hε)

theorem famRvMLower_parity_dyadic_of_designM {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = Family.dyadic.conductorShift)
    (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.dyadic.moduli Qn)
    (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      FamRvMLower F Qn P :=
  eventually_M_of_D0free F r ε hr hε (fun Qn P => FamRvMLower F Qn P)
    (fun _ _ _ h => h) (famRvMLower_parity_dyadic_of_design hF hsh hmod r ε hr hε)

/-- `FamNIIUpper` at `4A₀` along the MARGIN design, dyadic parity (reads `Valid` and `Q` only). -/
theorem famNIIUpper_parity_dyadic_of_designM {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = Family.dyadic.conductorShift)
    (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.dyadic.moduli Qn) (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      FamNIIUpper F Qn P (4 * A₀) := by
  filter_upwards [residue_small_parity_dyadic_eventually hF hmod (ε := 1) one_pos,
    eventually_ge_atTop 2] with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hcube := Qn_le_cube hQn
  have hcond : (∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Real.log q)
      ≤ Family.sizeR Family.dyadic Qn * (Real.log Qn - Family.dyadic.conductorShift)
        + 28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 := by
    have h := (abs_le.mp (famLogCond_dyadic_bound Qn hQn)).2
    simp only [Family.conductorShift]
    linarith
  refine famNIIUpper_parity_of_valid hF Family.isFull_dyadic P hP Qn hQn hQ (hmod Qn) hsh hA₀
    hloc (by positivity) hcond ?_
  linarith [hres]

/-- `FamNIIUpper` at `4A₀` along the MARGIN design, `Icc 2 Qn` parity. -/
theorem famNIIUpper_parity_qle_of_designM {F : Family} (hF : ¬ F.IsFull)
    (hsh : F.conductorShift = Family.qle.conductorShift)
    (hmod : ∀ Qn : ℕ, F.moduli Qn = Family.qle.moduli Qn) (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecordM F r ε (Qn : ℝ) P →
      FamNIIUpper F Qn P (4 * A₀) := by
  filter_upwards [residue_small_parity_eventually hF hmod (ε := 1) one_pos,
    eventually_ge_atTop 2] with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hcube := Qn_le_cube hQn
  have hcond : (∑ q ∈ Family.qle.moduli Qn, (phiStar q : ℝ) * Real.log q)
      ≤ Family.sizeR Family.qle Qn * (Real.log Qn - Family.qle.conductorShift)
        + 19 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 :=
    by linarith [(abs_le.mp (famLogCond_qle_bound Qn hQn)).2]
  refine famNIIUpper_parity_of_valid hF Family.isFull_qle P hP Qn hQn hQ (hmod Qn) hsh hA₀
    hloc (by positivity) hcond ?_
  linarith [hres]

end Margin

namespace JoinProved

open Margin

/-! ## 7. The headline theorems WITHOUT `r + ε ≤ 7` -/

/-- **Theorem 1, r-generic, at the CERTIFIED constant `P_cert = 0.7212`, WITHOUT `SharpZeroDensity`
and WITHOUT the regime `r + ε ≤ 7`** — `theorem_one_generic_proved` with its only remaining
hypothesis removed: the Gevrey closing condition is met with the margin `m = ½ log T`
(`DesignOfRecordM`), so §7's regime inequality holds for every `r ≥ 3`
(`Margin.hregime_M_eventually`). Every input is the tree's: the design point
(`exists_designOfRecordM`), `hNII` (`Margin.famNIIUpper_qle_of_designM`), `hfrob`
(`Margin.hfrob_qle_of_designM`: the Frobenius row at `κ_cert` and Lemma 8.1′, transferred along the
margin design by `Margin.eventually_M_of_D0free`), `hrvm` (`Margin.famRvMLower_of_designM`), the
rate (`Margin.budgetTotalProved_isBigO_of_designM`, through `payoff_rate_of_assembly_of_design`).
Axioms: `[propext, Classical.choice, Quot.sound]` — no `sorryAx` since the Gallagher rethread (Lemma 6.1 at `Q² + πN`, `ZetaQ/Gallagher.lean`); `audit/final_axioms.lean`. -/
theorem theorem_one_generic_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 2 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 2 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.qle r ε (DesignOfRecordM Family.qle r ε)
    (exists_designOfRecordM Family.qle r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (2 * A₀) Family.qle)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (2 * A₀) hA₀' Family.qle r ε hr hε design hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.qle r ε hr hε (2 * A₀) hA₀' hloc'
    (famNIIUpper_qle_of_designM r ε hA₀ hloc) (hfrob_qle_of_designM r ε hr hε)
    (famRvMLower_of_designM r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- **Corollary 2 (dyadic) at the CERTIFIED constant `P_cert = 0.7098`, WITHOUT `SharpZeroDensity`,
WITHOUT the regime `r + ε ≤ 7` and with NO named hypothesis at all**. Every input is
the tree's: the margin design point (`exists_designOfRecordM`), `hNII`
(`Margin.famNIIUpper_dyadic_of_designM`), `hfrob` (`Margin.hfrob_dyadic_of_designM`: the exact dyadic
Frobenius row at the family-aware `rowR2`, Lemma 8.1′ discharged, transferred along the margin design
by `Margin.eventually_M_of_D0free`), `hrvm` (`Margin.famRvMLower_dyadic_of_designM`), the rate
(`Margin.budgetTotalProved_isBigO_of_designM`). Axioms: `[propext, Classical.choice, Quot.sound]` — no `sorryAx` since the Gallagher rethread (Lemma 6.1 at `Q² + πN`, `ZetaQ/Gallagher.lean`). -/
theorem corollary_two_dyadic_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 2 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 2 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.dyadic r ε
    (DesignOfRecordM Family.dyadic r ε)
    (exists_designOfRecordM Family.dyadic r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (2 * A₀) Family.dyadic)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (2 * A₀) hA₀' Family.dyadic r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.dyadic r ε hr hε (2 * A₀) hA₀' hloc'
    (famNIIUpper_dyadic_of_designM r ε hA₀ hloc) (hfrob_dyadic_of_designM r ε hr hε)
    (famRvMLower_dyadic_of_designM r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩


/-! ## 8. **COROLLARY 3** — the four parity headlines, WITHOUT `r + ε ≤ 7` and with NO named
hypothesis at all.

Same five inputs as `theorem_one_generic_proved'` / `corollary_two_dyadic_proved'`, at the parity
families: the margin design point (`exists_designOfRecordM`), `hNII`
(`Margin.famNIIUpper_parity_*_of_designM`, at `4A₀` — see §6b for why the parity buffer row costs
a second factor of two), `hfrob` (`Margin.hfrob_*_of_designM`, transporting
`HFrob.hfrob_*_of_design`: the exact parity Frobenius row at the family-aware `rowR2`, priced at
`sZoneEvenDyadic`/`sZoneEvenQ` and certified by `ZoneData.zoneLipschitzData_*`, with Lemma 8.1′
discharged by `HFrob.hsep_of_design_parity`), `hrvm` (`Margin.famRvMLower_parity_*_of_designM`),
and the rate (`Margin.budgetTotalProved_isBigO_of_designM`). Axioms: `[propext, Classical.choice, Quot.sound]` — no `sorryAx` since the Gallagher rethread (Lemma 6.1 at `Q² + πN`, `ZetaQ/Gallagher.lean`),
exactly as the two earlier headlines. -/

/-- **Corollary 3 (even dyadic) at the CERTIFIED constant `P_cert = 0.6919`** — `q ∈ (Q/2, Q]`,
`χ` EVEN. This is the family that carries the Sono comparison. -/
theorem corollary_three_even_dyadic_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_even_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.evenDyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.evenDyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 4 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 4 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.evenDyadic r ε
    (DesignOfRecordM Family.evenDyadic r ε)
    (exists_designOfRecordM Family.evenDyadic r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (4 * A₀) Family.evenDyadic)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (4 * A₀) hA₀' Family.evenDyadic r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.evenDyadic r ε hr hε (4 * A₀) hA₀' hloc'
    (famNIIUpper_parity_dyadic_of_designM not_isFull_evenDyadic rfl (fun _ => rfl) r ε hA₀ hloc)
    (hfrob_evenDyadic_of_designM r ε hr hε)
    (famRvMLower_parity_dyadic_of_designM not_isFull_evenDyadic rfl (fun _ => rfl) r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- **Corollary 3 (odd dyadic) at `P_cert = 0.6919`** — `q ∈ (Q/2, Q]`, `χ` ODD. -/
theorem corollary_three_odd_dyadic_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_even_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.oddDyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.oddDyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 4 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 4 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.oddDyadic r ε
    (DesignOfRecordM Family.oddDyadic r ε)
    (exists_designOfRecordM Family.oddDyadic r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (4 * A₀) Family.oddDyadic)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (4 * A₀) hA₀' Family.oddDyadic r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.oddDyadic r ε hr hε (4 * A₀) hA₀' hloc'
    (famNIIUpper_parity_dyadic_of_designM not_isFull_oddDyadic rfl (fun _ => rfl) r ε hA₀ hloc)
    (hfrob_oddDyadic_of_designM r ε hr hε)
    (famRvMLower_parity_dyadic_of_designM not_isFull_oddDyadic rfl (fun _ => rfl) r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- **Corollary 3 (even, `q ≤ Q`) at `P_cert = 0.698`**. -/
theorem corollary_three_even_qQ_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_evenQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.evenQle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.evenQle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 4 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 4 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.evenQle r ε
    (DesignOfRecordM Family.evenQle r ε)
    (exists_designOfRecordM Family.evenQle r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (4 * A₀) Family.evenQle)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (4 * A₀) hA₀' Family.evenQle r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.evenQle r ε hr hε (4 * A₀) hA₀' hloc'
    (famNIIUpper_parity_qle_of_designM not_isFull_evenQle rfl (fun _ => rfl) r ε hA₀ hloc)
    (hfrob_evenQle_of_designM r ε hr hε)
    (famRvMLower_parity_of_designM not_isFull_evenQle rfl (fun _ => rfl) r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- **Corollary 3 (odd, `q ≤ Q`) at `P_cert = 0.698`**. -/
theorem corollary_three_odd_qQ_proved' (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_evenQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.oddQle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.oddQle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 4 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 4 * A₀) hloc
  have h := payoff_rate_of_assembly_of_design Family.oddQle r ε
    (DesignOfRecordM Family.oddQle r ε)
    (exists_designOfRecordM Family.oddQle r ε hr hε) (fun _ _ h => h.2.2.1)
    (budgetTotalProved (4 * A₀) Family.oddQle)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_designM (4 * A₀) hA₀' Family.oddQle r ε hr hε design
        hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_provedM Family.oddQle r ε hr hε (4 * A₀) hA₀' hloc'
    (famNIIUpper_parity_qle_of_designM not_isFull_oddQle rfl (fun _ => rfl) r ε hA₀ hloc)
    (hfrob_oddQle_of_designM r ε hr hε)
    (famRvMLower_parity_of_designM not_isFull_oddQle rfl (fun _ => rfl) r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

end JoinProved
end ZetaQ

end
