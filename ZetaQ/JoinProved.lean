/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/JoinProved.lean — **Theorem 1 at the certified constant WITHOUT `SharpZeroDensity`.**

The artifact's Theorem 1 must not assume the paper's sharp zero density: an unproved density
hypothesis in the headline would make the headline conditional. The buffer row is charged instead at the PROVED q-uniform local-count constant —
`bufferRowProved A₀` (§9/H6 through `FamNIIUpper` + `FamRvMLower`, `buffer_row_proved`) in place of
the paper's `L₄ = 3·rowR3` (`buffer_row_sharp`, hypothesis `SharpZeroDensity`). Paper §10.3:
charging the proved constant "would move the finite-Q thresholds, never the asymptotics" — and it
does not: `bufferRowProved A₀ ≤ 8A₀·L₄` once `log 4T ≤ ℒ` (`bufferRowProved_le_L4_mul`), so the total
stays `O(log log Q/log Q)` (`budgetTotalProved_isBigO_of_design`) and the rate step goes through
verbatim (`payoff_rate_of_assembly_gen`).

What is NEW here (nothing frozen is restated or touched; `budgetTotal` is untouched):
  * `rowR3Proved A₀ P := bufferRowProved A₀ P`, `budgetTotalProved A₀ F P :=
    budgetTotal F P − L₄ P + 3·bufferRowProved A₀ P` — Prop 3.1's bracket charges `3·r₃`, and the
    frozen bracket's `3·rowR3 = L₄`, so the swap `L₄ ↦ 3·bufferRowProved` keeps the bracket
    identity of `propBracket_le_budgetTotal` EXACT (`propBracketProved_le_budgetTotalProved`);
  * `assembly_clauses_at_design_proved` / `assembly_eventually_proved` / `assembly_at_lamStar_proved`
    — `JoinCert.assembly_at_lamStar_cert` with `buffer_row_proved` in place of `buffer_row_sharp`:
    `hsharp` is gone; the inputs are `A₀`, `hA₀ : 1 ≤ A₀`, the q-uniform local count `hloc` at `A₀`
    and `hNII : FamNIIUpper F Qn P A₀` eventually along the design (plus `hfrob`, `hrvm` as in
    `JoinCert`);
  * `payoff_rate_of_assembly_gen` — `JoinCert.payoff_rate_of_assembly_cert` with the budget total
    abstracted to any `B : ParamsQ → ℝ` that is `O(log log Q/log Q)` along every design map;
  * `theorem_one_generic_proved` — **Theorem 1 at `P_cert = 0.7212` for `Family.qle` with NO named
    hypothesis beyond `r + ε ≤ 7`**: `hNII` from `famNII_upper_of_residue_small` +
    `residue_small_eventually` (the ε-relaxed `FamNIIUpper`, promoted to the exact `Prop` at `2A₀`
    by `famNIIUpper_double_of_eps`), `hloc`/`A₀` from `EFChi.localCountChi_uniform`, `hfrob` from
    `HFrob.hfrob_qle_of_sep` + `HFrob.hsep_of_design`, `hrvm` from `famRvMLower_of_design`;
  * `corollary_two_dyadic_proved` — the dyadic twin, with NO named hypothesis beyond `r + ε ≤ 7`
    (the zone row is priced at the family's OWN zone secant, so `HFrob.hfrob_dyadic_of_sep` is the
    EXACT dyadic Frobenius row and `hfrob_dyadic_of_design` discharges it with
    `HFrob.hsep_of_design_dyadic`; while both families' zone rows were priced at the `q ≤ Q` secant
    `sZone` this `hfrob` had to be NAMED here — see `ZetaQ/Budget.lean`'s `sZoneDyadic`), `hNII` from the
    dyadic conductor average (`famNII_upper_dyadic_of_residue_small`, new here), `hrvm` from
    `famRvMLower_dyadic_of_design`.

Rule 17: nothing here bounds λ by 1, relates `X` to `T`, or pins `D₀`; every hypothesis is at the
design of record. Axioms: `[propext, Classical.choice, Quot.sound]`, nothing else (before the
Gallagher rethread: plus the single `sorryAx` of `ZetaQ.multiplicative_large_sieve`, through
`HFrob.hsep_of_design`).
-/
import ZetaQ.HFrob
import ZetaQ.Dyadic

noncomputable section

open Filter Asymptotics

namespace ZetaQ
namespace JoinProved

open JoinCert

/-! ## 1. The budget total at the PROVED buffer row -/

/-- `r₃` at the proved constant: `bufferRowProved A₀ P` — what `buffer_row_proved` delivers
(`NIIFamQ ≤ bufferRowProved A₀ P · NfamQ`). Prop 3.1's bracket charges `3·r₃`. -/
def rowR3Proved (A₀ : ℝ) (P : ParamsQ) : ℝ := bufferRowProved A₀ P

/-- **`budgetTotal` with the buffer row re-charged at the proved constant**: the paper's
`L₄ = 3·rowR3` is replaced by `3·rowR3Proved A₀ = 3·bufferRowProved A₀`; every other row is the
frozen one. -/
def budgetTotalProved (A₀ : ℝ) (F : Family) (P : ParamsQ) : ℝ :=
  budgetTotal F P - L₄ P + 3 * bufferRowProved A₀ P

theorem budgetTotalProved_eq (A₀ : ℝ) (F : Family) (P : ParamsQ) :
    budgetTotalProved A₀ F P
      = zoneRowLinear F P + L₃ P + 3 * bufferRowProved A₀ P + L₅ P + minorRows F P := by
  unfold budgetTotalProved budgetTotal; ring

/-- `propBracketCert` with `rowR3 ↦ rowR3Proved A₀`. -/
def propBracketProved (A₀ : ℝ) (F : Family) (P : ParamsQ) (θ₀ : ℝ) : ℝ :=
  4 * rowR1 F P + rowR2 F P + 3 * rowR3Proved A₀ P + 4 * rowR4 F P θ₀
    + 2 * rowR5 F P θ₀ * Real.sqrt (F.kappaCert + rowR2 F P) + rowR5 F P θ₀ ^ 2

/-- `propBracketCert_le_budgetTotal` at the proved row — the SAME exact ring identity: the swapped
row appears as `3·rowR3Proved` on the left and `3·bufferRowProved` on the right, and what is left is
`(L₅ + L₉) − (pair block)`, i.e. `hpair`. -/
theorem propBracketProved_le_budgetTotalProved (A₀ : ℝ) (F : Family) (r ε : ℝ) (Qn : ℕ)
    (P : ParamsQ) (θ₀ : ℝ)
    (_hdes : DesignOfRecord F r ε (Qn : ℝ) P) (_hθ : 0 ≤ θ₀)
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

/-! ## 2. The proved row is `O(L₄)` in the regime, hence the total is still `O(log log Q/log Q)` -/

/-- `bufferRowProved A₀ ≤ 8A₀·L₄` once `log 4T ≤ ℒ` (the exact ratio is `πA₀(ℒ + log 4T)/ℒ ≤ 2πA₀`). -/
theorem bufferRowProved_le_L4_mul (A₀ : ℝ) (P : ParamsQ) (hA₀ : 0 ≤ A₀) (hTpos : 0 < P.T)
    (hD0 : 0 ≤ P.D0) (hLL0 : 0 < P.LL) (hlog4T : Real.log (4 * P.T) ≤ P.LL) :
    bufferRowProved A₀ P ≤ 8 * A₀ * L₄ P := by
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hden : (0 : ℝ) < P.T / (2 * Real.pi) * P.LL :=
    mul_pos (div_pos hTpos (by linarith)) hLL0
  have hL4 : 8 * A₀ * L₄ P = 48 * A₀ * P.D0 / P.T := by unfold L₄ cBuffer; ring
  rw [hL4]
  unfold bufferRowProved
  rw [div_le_div_iff₀ hden hTpos]
  have hAD : (0 : ℝ) ≤ A₀ * P.D0 := mul_nonneg hA₀ hD0
  have hY : P.LL + Real.log (4 * P.T) ≤ 2 * P.LL := by linarith
  have e1 : 3 * A₀ * P.D0 * (P.LL + Real.log (4 * P.T)) * P.T
      ≤ 6 * A₀ * P.D0 * P.LL * P.T := by
    have h := mul_le_mul_of_nonneg_left hY (by linarith : (0 : ℝ) ≤ 3 * A₀ * P.D0)
    have h' := mul_le_mul_of_nonneg_right h hTpos.le
    linarith
  have hstep : P.T / 8 ≤ P.T / (2 * Real.pi) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have e2 : 6 * A₀ * P.D0 * P.LL * P.T ≤ 48 * A₀ * P.D0 * (P.T / (2 * Real.pi) * P.LL) := by
    have h0 : (0 : ℝ) ≤ 48 * A₀ * P.D0 * P.LL := by
      have := mul_nonneg hAD hLL0.le; linarith
    have h := mul_le_mul_of_nonneg_left hstep h0
    calc 6 * A₀ * P.D0 * P.LL * P.T = 48 * A₀ * P.D0 * P.LL * (P.T / 8) := by ring
      _ ≤ 48 * A₀ * P.D0 * P.LL * (P.T / (2 * Real.pi)) := h
      _ = 48 * A₀ * P.D0 * (P.T / (2 * Real.pi) * P.LL) := by ring
  linarith

/-- **`budgetTotalProved = O(log log Q/log Q)` along any map of `Valid` points with the design's
`Q`, `T`, given `budgetTotal = O(log log Q/log Q)` and `D₀ = O((log Q)²)` along it** — the core of
`budgetTotalProved_isBigO_of_design`: `bufferRowProved ≤ 8A₀·L₄` and `L₄ = 6D₀/T ≤ 6c/log Q`
(`T = (log Q)^{r+ε}`, `r ≥ 3`). The implied constant is `|c₀| + 144·A₀·|c|`. Factored out
so that it serves the margin design too (`Margin.budgetTotalProved_isBigO_of_designM`). -/
theorem budgetTotalProved_isBigO_core (A₀ : ℝ) (hA₀ : 1 ≤ A₀) (F : Family) (r ε : ℝ)
    (hr : 3 ≤ r) (hε : 0 < ε) (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop,
      (design Q).Valid ∧ (design Q).Q = Q ∧ (design Q).T = Twin Q r ε)
    (hB0 : (fun Q => budgetTotal F (design Q))
      =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q))
    (hD0 : (fun Q => (design Q).D0) =O[atTop] (fun Q => Real.log Q ^ 2)) :
    (fun Q => budgetTotalProved A₀ F (design Q))
      =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q) := by
  obtain ⟨c0, hc0⟩ := isBigO_iff.mp hB0
  obtain ⟨c, hc⟩ := isBigO_iff.mp hD0
  rw [isBigO_iff]
  refine ⟨|c0| + 144 * A₀ * |c|, ?_⟩
  filter_upwards [hdesign, hc0, hc, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (8 * Real.pi)] with Q hdes hb0 hb hu hv' hQ8
  have hv : (1 : ℝ) ≤ Real.log (Real.log Q) := hv'
  have hP : (design Q).Valid := hdes.1
  have hQeq : (design Q).Q = Q := hdes.2.1
  have hT : (design Q).T = Twin Q r ε := hdes.2.2
  have hu0 : (0 : ℝ) < Real.log Q := by linarith
  have hv0 : (0 : ℝ) ≤ Real.log (Real.log Q) := by linarith
  have hvu : (0 : ℝ) ≤ Real.log (Real.log Q) / Real.log Q := div_nonneg hv0 hu0.le
  have hT300 : (300 : ℝ) ≤ (design Q).T := hP.T_ge
  have hTpos : (0 : ℝ) < (design Q).T := by linarith
  have hD0pos : (0 : ℝ) < (design Q).D0 := by linarith [hP.two_le_D0]
  have hLL0 : (0 : ℝ) < (design Q).LL := EFChi.LL_pos_of_valid hP
  have hA0 : (0 : ℝ) ≤ A₀ := by linarith
  -- `D₀ ≤ |c|·(log Q)²`
  have hD : (design Q).D0 ≤ |c| * Real.log Q ^ 2 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0pos.le,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log Q ^ 2)] at hb
    have : c * Real.log Q ^ 2 ≤ |c| * Real.log Q ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    linarith
  -- `(log Q)³ ≤ T`
  have hT3 : Real.log Q ^ (3 : ℕ) ≤ (design Q).T := by
    rw [hT]; unfold Twin
    have h1 : Real.log Q ^ (3 : ℝ) ≤ Real.log Q ^ (r + ε) :=
      Real.rpow_le_rpow_of_exponent_le hu (by linarith)
    have h2 : Real.log Q ^ (3 : ℝ) = Real.log Q ^ (3 : ℕ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← h2]; exact h1
  -- `L₄ ≤ 6|c|·(log log Q/log Q)`
  have hL40 : (0 : ℝ) ≤ L₄ (design Q) := by
    unfold L₄ cBuffer; exact div_nonneg (by linarith) hTpos.le
  have hL4 : L₄ (design Q) ≤ 6 * |c| * (Real.log (Real.log Q) / Real.log Q) := by
    unfold L₄ cBuffer
    rw [div_le_iff₀ hTpos]
    have hvuu : Real.log (Real.log Q) / Real.log Q * Real.log Q = Real.log (Real.log Q) := by
      field_simp
    have h3 : 6 * |c| * (Real.log (Real.log Q) / Real.log Q) * Real.log Q ^ (3 : ℕ)
        ≤ 6 * |c| * (Real.log (Real.log Q) / Real.log Q) * (design Q).T :=
      mul_le_mul_of_nonneg_left hT3 (by positivity)
    have h4 : 6 * |c| * Real.log Q ^ 2
        ≤ 6 * |c| * (Real.log (Real.log Q) / Real.log Q) * Real.log Q ^ (3 : ℕ) := by
      have e : 6 * |c| * (Real.log (Real.log Q) / Real.log Q) * Real.log Q ^ (3 : ℕ)
          = 6 * |c| * (Real.log (Real.log Q) / Real.log Q * Real.log Q) * Real.log Q ^ 2 := by
        ring
      rw [e, hvuu]
      have : 6 * |c| ≤ 6 * |c| * Real.log (Real.log Q) := by
        nlinarith [abs_nonneg c]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  -- `log 4T ≤ ℒ` (i.e. `8π ≤ Q`) and the proved row against `L₄`
  have hlog4T0 : (0 : ℝ) ≤ Real.log (4 * (design Q).T) := Real.log_nonneg (by linarith)
  have hlog4T : Real.log (4 * (design Q).T) ≤ (design Q).LL := by
    unfold ParamsQ.LL
    apply Real.log_le_log (by linarith)
    rw [hQeq, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hQ8) hTpos.le]
  have hbr0 : (0 : ℝ) ≤ bufferRowProved A₀ (design Q) := by
    unfold bufferRowProved
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hD0pos.le) (by linarith))
      (mul_nonneg (by positivity) hLL0.le)
  have hbr := bufferRowProved_le_L4_mul A₀ (design Q) hA0 hTpos hD0pos.le hLL0 hlog4T
  -- assemble
  have hb0' : |budgetTotal F (design Q)| ≤ |c0| * (Real.log (Real.log Q) / Real.log Q) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hvu] at hb0
    have : c0 * (Real.log (Real.log Q) / Real.log Q)
        ≤ |c0| * (Real.log (Real.log Q) / Real.log Q) :=
      mul_le_mul_of_nonneg_right (le_abs_self c0) hvu
    linarith
  have hdiff : |budgetTotalProved A₀ F (design Q) - budgetTotal F (design Q)|
      ≤ 24 * A₀ * L₄ (design Q) := by
    have e : budgetTotalProved A₀ F (design Q) - budgetTotal F (design Q)
        = 3 * bufferRowProved A₀ (design Q) - L₄ (design Q) := by
      unfold budgetTotalProved; ring
    rw [e, abs_le]
    constructor
    · nlinarith [mul_nonneg hA0 hL40]
    · nlinarith [mul_nonneg hA0 hL40]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hvu]
  calc |budgetTotalProved A₀ F (design Q)|
      = |(budgetTotalProved A₀ F (design Q) - budgetTotal F (design Q))
          + budgetTotal F (design Q)| := by ring_nf
    _ ≤ |budgetTotalProved A₀ F (design Q) - budgetTotal F (design Q)|
          + |budgetTotal F (design Q)| := abs_add_le _ _
    _ ≤ 24 * A₀ * L₄ (design Q) + |c0| * (Real.log (Real.log Q) / Real.log Q) := by
        linarith
    _ ≤ 24 * A₀ * (6 * |c| * (Real.log (Real.log Q) / Real.log Q))
          + |c0| * (Real.log (Real.log Q) / Real.log Q) := by
        have := mul_le_mul_of_nonneg_left hL4 (by linarith : (0 : ℝ) ≤ 24 * A₀)
        linarith
    _ = (|c0| + 144 * A₀ * |c|) * (Real.log (Real.log Q) / Real.log Q) := by ring

/-- **`budgetTotalProved = O(log log Q/log Q)` along every design map** — `budgetTotal_isBigO_of_design`
plus `bufferRowProved ≤ 8A₀·L₄` and `L₄ = 6D₀/T ≤ 6c/log Q` (`design_D0_isBigO`, `T = (log Q)^{r+ε}`,
`r ≥ 3`). The implied constant is `|c₀| + 144·A₀·|c|`. -/
theorem budgetTotalProved_isBigO_of_design (A₀ : ℝ) (hA₀ : 1 ≤ A₀) (F : Family) (r ε : ℝ)
    (hr : 3 ≤ r) (hε : 0 < ε) (design : ℝ → ParamsQ)
    (hdesign : ∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q)) :
    (fun Q => budgetTotalProved A₀ F (design Q))
      =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q) :=
  budgetTotalProved_isBigO_core A₀ hA₀ F r ε hr hε design
    (hdesign.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (budgetTotal_isBigO_of_design F r ε hr hε design hdesign)
    (design_D0_isBigO F r ε hr hε design hdesign)

/-! ## 3. The rate step with the budget total ABSTRACTED -/

/-- **`JoinCert.payoff_rate_of_assembly_cert` with the budget total AND the design predicate
abstracted**: any `B : ParamsQ → ℝ` that is `O(log log Q/log Q)` along every `Des`-map serves, for
any design predicate `Des` that has points at every large `Q` and pins `T = (log Q)^{r+ε}` (the
proof is that one verbatim, with `budgetTotal F ↦ B`, `DesignOfRecord F r ε ↦ Des`). **F52:**
factored out so that it serves `DesignOfRecordM` too (`JoinProved.theorem_one_generic_proved'`). -/
theorem payoff_rate_of_assembly_of_design (F : Family) (r ε : ℝ)
    (Des : ℝ → ParamsQ → Prop)
    (hex : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∃ P : ParamsQ, Des Q P)
    (hT : ∀ (Q : ℝ) (P : ParamsQ), Des Q P → P.T = Twin Q r ε)
    (B : ParamsQ → ℝ)
    (hB : ∀ design : ℝ → ParamsQ, (∀ᶠ Q in atTop, Des Q (design Q)) →
      (fun Q => B (design Q)) =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q))
    (hassembly : ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ∃ P : ParamsQ, Des (Qn : ℝ) P ∧
        (2 - F.kappaCert - B P) * NfamQ P F Qn ≤ N0sFamQ P F Qn) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (F.payoffCert - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨Q₀, hQ₀⟩ := hassembly
  obtain ⟨Q₁, hQ₁⟩ := hex
  -- the design map on the naturals: the assembly's own points above `Q₀`
  have hchoiceN : ∀ n : ℕ, ∃ P : ParamsQ, Q₀ ≤ (n : ℝ) →
      Des (n : ℝ) P ∧
        (2 - F.kappaCert - B P) * NfamQ P F n ≤ N0sFamQ P F n := by
    intro n
    by_cases hn : Q₀ ≤ (n : ℝ)
    · obtain ⟨P, hP⟩ := hQ₀ n hn
      exact ⟨P, fun _ => hP⟩
    · exact ⟨Classical.choose (hQ₁ Q₁ le_rfl), fun h => absurd h hn⟩
  choose designN hdesN using hchoiceN
  -- its extension to the reals: `exists_designOfRecord`'s points off the naturals
  have hchoiceR : ∀ Q : ℝ, ∃ P : ParamsQ,
      (∀ n : ℕ, (n : ℝ) = Q → P = designN n) ∧
      ((¬ ∃ n : ℕ, (n : ℝ) = Q) → Q₁ ≤ Q → Des Q P) := by
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
  have hdesign : ∀ᶠ Q in atTop, Des Q (design Q) := by
    filter_upwards [eventually_ge_atTop Q₀, eventually_ge_atTop Q₁] with Q h0 h1
    by_cases hn : ∃ n : ℕ, (n : ℝ) = Q
    · obtain ⟨n, rfl⟩ := hn
      rw [hdesign1 (n : ℝ) n rfl]
      exact (hdesN n h0).1
    · exact hdesign2 Q hn h1
  -- the budget along it is `O(log log Q/log Q)`
  obtain ⟨c0, hc0⟩ := Asymptotics.isBigO_iff.mp (hB design hdesign)
  have hev : ∀ᶠ Q in atTop,
      ‖B (design Q)‖ ≤ c0 * ‖Real.log (Real.log Q) / Real.log Q‖ ∧
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
  have hT : (designN Qn).T = Twin (Qn : ℝ) r ε := hT _ _ hdes
  -- the rate bound on the budget total, at a nonnegative constant
  have hbt : B (designN Qn)
      ≤ (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hvu] at hb
    have h1 : B (designN Qn) ≤ |B (designN Qn)| := le_abs_self _
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
      ≤ 2 - F.kappaCert - B (designN Qn) := by
    rw [two_sub_kappaCert]; linarith
  have hgd : (|c0| + 1) * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)
      = (|c0| + 1) * (Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ)) :=
    mul_div_assoc _ _ _
  rw [hgd]
  exact le_trans (mul_le_mul_of_nonneg_right hcoef hN) hlast

/-- **`JoinCert.payoff_rate_of_assembly_cert` with the budget total abstracted**: any `B : ParamsQ → ℝ`
that is `O(log log Q/log Q)` along every design map serves (the proof is that one verbatim, with
`budgetTotal F ↦ B`). -/
theorem payoff_rate_of_assembly_gen (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (B : ParamsQ → ℝ)
    (hB : ∀ design : ℝ → ParamsQ, (∀ᶠ Q in atTop, DesignOfRecord F r ε Q (design Q)) →
      (fun Q => B (design Q)) =O[atTop] (fun Q => Real.log (Real.log Q) / Real.log Q))
    (hassembly : ∃ Q₀ : ℝ, ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      ∃ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P ∧
        (2 - F.kappaCert - B P) * NfamQ P F Qn ≤ N0sFamQ P F Qn) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (F.payoffCert - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount F Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) :=
  payoff_rate_of_assembly_of_design F r ε (DesignOfRecord F r ε)
    (exists_designOfRecord F r ε hr hε) (fun _ _ h => h.2.2.1) B hB hassembly

/-! ## 4. The local-count bookkeeping -/

/-- `EFChi.localCountChi_uniform`'s shape of the q-uniform local count, in the shape
`buffer_row_proved` names it (over the family's moduli, at `NcountQ`). -/
theorem hloc_moduli_of_uniform (F : Family) (Qn : ℕ) (hQn : 2 ≤ Qn) {A₀ : ℝ}
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ q ∈ F.moduli Qn, ∀ χ ∈ primitiveChars q, ∀ t : ℝ,
      NcountQ q χ t (t + 1) ≤ A₀ * Real.log ((q : ℝ) * (|t| + 3)) := by
  intro q hq χ hχ t
  have hq1 : 1 < q := EFChi.one_lt_of_mem_moduli hQn hq
  have : NeZero q := ⟨by omega⟩
  have hp : χ.IsPrimitive := EFChi.isPrimitive_of_mem_primitiveChars hχ
  have hNc : NcountQ q χ t (t + 1) = ((Zeta23.ThmE.NcountL χ t (t + 1) : ℕ) : ℝ) := by
    unfold NcountQ; rw [dif_neg (show ¬ q = 0 by omega)]
  rw [hNc]
  exact hloc q χ hq1 hp t

/-- the q-uniform local count is monotone in its constant. -/
theorem hloc_mono {A₀ A₁ : ℝ} (h : A₀ ≤ A₁)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₁ * Real.log (q * (|t| + 3)) := by
  intro q _ χ hq hp t
  refine (hloc q χ hq hp t).trans (mul_le_mul_of_nonneg_right h ?_)
  apply Real.log_nonneg
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.le
  nlinarith [abs_nonneg t]

/-- The ε-relaxed `FamNIIUpper` at `ε = 1` (what the tree delivers, `famNII_upper_of_residue_small`)
IS the exact `FamNIIUpper` at `2A₀`, since `1 ≤ ℒ − ⟨shift⟩ + log 8π` (`log 8π ≥ 2`, `⟨shift⟩ ≤ 1/2`). -/
theorem famNIIUpper_double_of_eps (F : Family) (Qn : ℕ) (P : ParamsQ) (hP : P.Valid)
    {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (h : NIIFamQ P F Qn
      ≤ 3 * A₀ * P.D0 * (P.LL - (F.conductorShift - 1) + Real.log (8 * Real.pi))
          * F.sizeR Qn) :
    FamNIIUpper F Qn P (2 * A₀) := by
  unfold FamNIIUpper
  refine h.trans ?_
  have hLL : (0 : ℝ) < P.LL := EFChi.LL_pos_of_valid hP
  have hD0 : (0 : ℝ) ≤ P.D0 := by linarith [hP.two_le_D0]
  have hsz : (0 : ℝ) ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hs : F.conductorShift ≤ 1 / 2 := conductorShift_le_half F
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog : (2 : ℝ) ≤ Real.log (8 * Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : Real.exp 1 ^ (2 : ℕ) = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    have hle : Real.exp 1 ^ (2 : ℕ) ≤ (2.7182818286 : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he.le 2
    rw [← h2]
    nlinarith
  have hc : (0 : ℝ) ≤ 3 * A₀ * P.D0 * F.sizeR Qn := by
    have h1 : (0 : ℝ) ≤ 3 * A₀ * P.D0 := mul_nonneg (by linarith) hD0
    exact mul_nonneg h1 hsz
  have hb : P.LL - (F.conductorShift - 1) + Real.log (8 * Real.pi)
      ≤ 2 * (P.LL - F.conductorShift + Real.log (8 * Real.pi)) := by linarith
  have hkey := mul_le_mul_of_nonneg_left hb hc
  calc 3 * A₀ * P.D0 * (P.LL - (F.conductorShift - 1) + Real.log (8 * Real.pi)) * F.sizeR Qn
      = 3 * A₀ * P.D0 * F.sizeR Qn
          * (P.LL - (F.conductorShift - 1) + Real.log (8 * Real.pi)) := by ring
    _ ≤ 3 * A₀ * P.D0 * F.sizeR Qn
          * (2 * (P.LL - F.conductorShift + Real.log (8 * Real.pi))) := hkey
    _ = 3 * (2 * A₀) * P.D0 * (P.LL - F.conductorShift + Real.log (8 * Real.pi))
          * F.sizeR Qn := by ring

/-! ## 5. The eight clauses at the proved buffer row -/

/-- **`JoinCert.assembly_clauses_at_design_cert` with `buffer_row_proved` in place of
`buffer_row_sharp`**: `hsharp` is gone; in its place the q-uniform local count at `A₀` (`hloc`,
retained by `buffer_row_proved` for provenance), §9's family aggregate `hNII : FamNIIUpper F Qn P A₀`
and `hrvm`. `r₃ := rowR3Proved A₀ P = bufferRowProved A₀ P`; clauses 7 and 8 are at
`budgetTotalProved A₀ F P`. -/
theorem assembly_clauses_at_design_proved (F : Family) (r ε : ℝ) (Qn : ℕ) (P : ParamsQ)
    (θ₀ A₀ : ℝ)
    (hQn : 2 ≤ Qn) (hdes : DesignOfRecord F r ε (Qn : ℝ) P) (hθ : 0 ≤ θ₀) (hA₀ : 1 ≤ A₀)
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
  -- §10.3's rows 3 (PROVED), 4, 5 and the bracket
  have hNII' : NIIFamQ P F Qn ≤ rowR3Proved A₀ P * NfamQ P F Qn := by
    unfold rowR3Proved
    exact buffer_row_proved F r ε Qn P A₀ hdes hA₀ hloc hNII hrvm
  obtain ⟨hBtr', hBF'⟩ := pair_rows F r ε Qn P θ₀ hdes hθ hrvm
  have hbr := propBracketProved_le_budgetTotalProved A₀ F r ε Qn P θ₀ hdes hθ hpair
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

/-- **The eight clauses at EVERY design point, eventually in `Q`, at the proved buffer row** — from
the named eventual inputs `hNII`, `hfrob`, `hrvm`, the q-uniform local count `hloc` at `A₀`, and
the tree (`trace_row_eventually_aux`, `tail_clauses_cert_eventually` at the SAME `A₀`, `hϱ` from
`gevreyProfile_rhoTwoQ`). -/
theorem assembly_eventually_proved (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hre : r + ε ≤ 7) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hNII : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      FamNIIUpper F Qn P A₀)
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
            + 2 * r₅ * Real.sqrt (F.kappaCert + r₂) + r₅ ^ 2 ≤ budgetTotalProved A₀ F P ∧
        (2 - F.kappaCert - budgetTotalProved A₀ F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  filter_upwards [trace_row_eventually_aux F r ε hr hε,
    tail_clauses_cert_eventually F r ε hr hε.le hre A₀ hA₀ hloc, hNII, hfrob, hrvm,
    eventually_ge_atTop 2] with Qn htr htail hs hf hv hQn
  intro P hdes
  have hϱ : Zeta23.Taper.GevreyProfile 2 gevreyA gevreyB P.ϱ := by
    rw [hdes.2.2.2.2.2.2.2.2.2.2.1]; exact gevreyProfile_rhoTwoQ
  obtain ⟨θ₀, hθ, hpair, hblock⟩ := htail P hdes hϱ
  exact assembly_clauses_at_design_proved F r ε Qn P θ₀ A₀ hQn hdes hθ hA₀
    (hloc_moduli_of_uniform F Qn hQn hloc) (htr P hdes) (hf P hdes) (hs P hdes) (hv P hdes)
    hpair hblock

/-- **`JoinCert.assembly_at_lamStar_cert` at the PROVED buffer row, with its inputs NAMED** — the
frozen `assembly_at_lamStar` shape with `F.kappaC ↦ F.kappaCert`, `r₃ ↦ bufferRowProved A₀ P`,
`budgetTotal ↦ budgetTotalProved A₀`, under
  * `hre : r + ε ≤ 7` (F52's regime for §7's `hregime`),
  * `A₀`, `hA₀ : 1 ≤ A₀`, `hloc` (the q-uniform local count at `A₀` — H6, `EFChi.localCountChi_uniform`),
  * `hNII` (`FamNIIUpper F · · A₀` eventually along the design — §9's family aggregate, the tree's
    for both families up to the ε-relaxation absorbed by doubling `A₀`),
  * `hfrob` (the Frobenius row at `κ_cert`, eventually along the design — `HFrob.hfrob_qle_of_sep` +
    `HFrob.hsep_of_design` for `qle`),
  * `hrvm` (`FamRvMLower` eventually along the design — `famRvMLower_of_design` /
    `famRvMLower_dyadic_of_design`).
`SharpZeroDensity` is NOT among them. -/
theorem assembly_at_lamStar_proved (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hre : r + ε ≤ 7) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hNII : ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord F r ε (Qn : ℝ) P →
      FamNIIUpper F Qn P A₀)
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
              + 2 * r₅ * Real.sqrt (F.kappaCert + r₂) + r₅ ^ 2 ≤ budgetTotalProved A₀ F P ∧
          (2 - F.kappaCert - budgetTotalProved A₀ F P) * NfamQ P F Qn ≤ N0sFamQ P F Qn := by
  obtain ⟨Q₁, hQ₁⟩ := exists_designOfRecord F r ε hr hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (assembly_eventually_proved F r ε hr hε hre A₀ hA₀ hloc hNII hfrob hrvm)
  refine ⟨max Q₁ (N : ℝ), fun Qn hQn => ?_⟩
  obtain ⟨P, hdes⟩ := hQ₁ (Qn : ℝ) (le_trans (le_max_left _ _) hQn)
  have hNQ : N ≤ Qn := by exact_mod_cast le_trans (le_max_right _ _) hQn
  exact ⟨P, hdes, hN Qn hNQ P hdes⟩

/-! ## 6. The tree's inputs for the two families -/

/-- `hfrob` for `Family.qle` along the design, from the tree: `HFrob.hfrob_qle_of_sep` with `hsep`
discharged by `HFrob.hsep_of_design`. -/
theorem hfrob_qle_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.qle Qn
        ≤ (Family.qle.kappaCert + rowR2 Family.qle P) * NfamQ P Family.qle Qn := by
  filter_upwards [HFrob.hfrob_qle_of_sep r ε hr hε, HFrob.hsep_of_design r ε hr hε]
    with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

/-- `hfrob` for `Family.dyadic` along the design, from the tree: `HFrob.hfrob_dyadic_of_sep`
(the exact dyadic row at the family-aware `rowR2`) with `hsep` discharged by
`HFrob.hsep_of_design_dyadic`. -/
theorem hfrob_dyadic_of_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      frobSqGhatFam P Family.dyadic Qn
        ≤ (Family.dyadic.kappaCert + rowR2 Family.dyadic P) * NfamQ P Family.dyadic Qn := by
  filter_upwards [HFrob.hfrob_dyadic_of_sep r ε hr hε, HFrob.hsep_of_design_dyadic r ε hr hε]
    with Qn h1 h2
  intro P hdes
  exact h1 P hdes (h2 P hdes)

/-- `FamNIIUpper Family.qle` at `2A₀` along the design, from the tree (`famNII_upper_of_residue_small`
at `ε = 1`, `residue_small_eventually`, `famNIIUpper_double_of_eps`), for any `A₀` at which the
q-uniform local count holds. -/
theorem famNIIUpper_qle_of_design (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.qle r ε (Qn : ℝ) P →
      FamNIIUpper Family.qle Qn P (2 * A₀) := by
  filter_upwards [residue_small_eventually (ε := 1) one_pos, eventually_ge_atTop 2]
    with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  exact famNIIUpper_double_of_eps Family.qle Qn P hP hA₀
    (famNII_upper_of_residue_small P hP Qn hQn hQ hA₀ hloc hres)

/-- `ℒ + log 8π = log Q + log 4T` at `P.Q = Qn` (the private `Budget.log_LL_add_log8pi`, re-proved). -/
theorem LL_add_log8pi_eq (P : ParamsQ) (hP : P.Valid) (Qn : ℕ) (hQn : 2 ≤ Qn)
    (hQ : P.Q = (Qn : ℝ)) :
    P.LL + Real.log (8 * Real.pi) = Real.log (Qn : ℝ) + Real.log (4 * P.T) := by
  have hQnR : (2 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn
  have hQ0 : (0 : ℝ) < (Qn : ℝ) := by linarith
  have hT : (300 : ℝ) ≤ P.T := hP.T_ge
  have hT0 : (0 : ℝ) < P.T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : (0 : ℝ) < (Qn : ℝ) * P.T / (2 * Real.pi) :=
    div_pos (mul_pos hQ0 hT0) (by linarith)
  have h2 : (0 : ℝ) < 8 * Real.pi := by linarith
  have h3 : (0 : ℝ) < 4 * P.T := by linarith
  unfold ParamsQ.LL
  rw [hQ, ← Real.log_mul (ne_of_gt h1) (ne_of_gt h2),
    ← Real.log_mul (ne_of_gt hQ0) (ne_of_gt h3)]
  congr 1
  field_simp
  ring

/-- **`FamNIIUpper` for `Family.dyadic` under the explicit smallness side-condition** — the dyadic
twin of `famNII_upper_of_residue_small`: `NIIFam_avg_le` (F-generic) + the dyadic conductor average
`famLogCond_dyadic_bound` (exact shift `1/2 − log 2/3 ≥` the frozen `0.26895`,
`conductorShift_dyadic_err`). -/
theorem famNII_upper_dyadic_of_residue_small (P : ParamsQ) (hP : P.Valid) (Qn : ℕ)
    (hQn : 2 ≤ Qn) (hQ : P.Q = (Qn : ℝ)) {A₀ ε : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    (hres : 28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 ≤ ε * Family.sizeR Family.dyadic Qn) :
    NIIFamQ P Family.dyadic Qn
      ≤ 3 * A₀ * P.D0
          * (P.LL - (Family.dyadic.conductorShift - ε) + Real.log (8 * Real.pi))
          * Family.sizeR Family.dyadic Qn := by
  have hbase := NIIFam_avg_le P hP Family.dyadic Qn hQn hA₀ hloc
  have hD := hP.two_le_D0
  have hA0D : (0 : ℝ) ≤ 3 * A₀ * P.D0 := by nlinarith
  have hsz : (0 : ℝ) ≤ Family.sizeR Family.dyadic Qn := by unfold Family.sizeR; positivity
  have hsplit : ∑ q ∈ Family.dyadic.moduli Qn,
        (phiStar q : ℝ) * (Real.log q + Real.log (4 * P.T))
      = (∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Real.log q)
        + Family.sizeR Family.dyadic Qn * Real.log (4 * P.T) := by
    rw [sizeR_eq_sum_phiStar Family.isFull_dyadic, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  obtain ⟨hsh0, -⟩ := conductorShift_dyadic_err
  have hbound : (∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Real.log q)
      ≤ Family.sizeR Family.dyadic Qn * (Real.log Qn - Family.dyadic.conductorShift)
        + 28 * (Qn : ℝ) * (1 + Real.log Qn) ^ 3 := by
    have h1 := (abs_le.mp (famLogCond_dyadic_bound Qn hQn)).2
    have h2 : Family.sizeR Family.dyadic Qn * (Real.log Qn - (1 / 2 - Real.log 2 / 3))
        ≤ Family.sizeR Family.dyadic Qn * (Real.log Qn - Family.dyadic.conductorShift) :=
      mul_le_mul_of_nonneg_left (by linarith) hsz
    linarith
  have hrw : P.LL - (Family.dyadic.conductorShift - ε) + Real.log (8 * Real.pi)
      = (Real.log (Qn : ℝ) - Family.dyadic.conductorShift) + Real.log (4 * P.T) + ε := by
    have := LL_add_log8pi_eq P hP Qn hQn hQ
    linarith
  refine hbase.trans ?_
  rw [hsplit]
  have hgoal : (∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Real.log q)
        + Family.sizeR Family.dyadic Qn * Real.log (4 * P.T)
      ≤ (P.LL - (Family.dyadic.conductorShift - ε) + Real.log (8 * Real.pi))
          * Family.sizeR Family.dyadic Qn := by
    rw [hrw]
    have e : ((Real.log (Qn : ℝ) - Family.dyadic.conductorShift) + Real.log (4 * P.T) + ε)
          * Family.sizeR Family.dyadic Qn
        = Family.sizeR Family.dyadic Qn * (Real.log Qn - Family.dyadic.conductorShift)
          + Family.sizeR Family.dyadic Qn * Real.log (4 * P.T)
          + ε * Family.sizeR Family.dyadic Qn := by ring
    rw [e]
    linarith
  calc 3 * A₀ * P.D0 * ((∑ q ∈ Family.dyadic.moduli Qn, (phiStar q : ℝ) * Real.log q)
          + Family.sizeR Family.dyadic Qn * Real.log (4 * P.T))
      ≤ 3 * A₀ * P.D0 * ((P.LL - (Family.dyadic.conductorShift - ε) + Real.log (8 * Real.pi))
          * Family.sizeR Family.dyadic Qn) := mul_le_mul_of_nonneg_left hgoal hA0D
    _ = 3 * A₀ * P.D0 * (P.LL - (Family.dyadic.conductorShift - ε) + Real.log (8 * Real.pi))
          * Family.sizeR Family.dyadic Qn := by ring

/-- `FamNIIUpper Family.dyadic` at `2A₀` along the design, from the tree. -/
theorem famNIIUpper_dyadic_of_design (r ε : ℝ) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (Zeta23.ThmE.NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3))) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, DesignOfRecord Family.dyadic r ε (Qn : ℝ) P →
      FamNIIUpper Family.dyadic Qn P (2 * A₀) := by
  filter_upwards [residue_small_eventually_dyadic (ε := 1) one_pos, eventually_ge_atTop 2]
    with Qn hres hQn
  intro P hdes
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  exact famNIIUpper_double_of_eps Family.dyadic Qn P hP hA₀
    (famNII_upper_dyadic_of_residue_small P hP Qn hQn hQ hA₀ hloc hres)

/-! ## 7. The headline theorems -/

/-- **Theorem 1, r-generic, at the CERTIFIED constant `P_cert = 0.7212`, WITHOUT `SharpZeroDensity`
and with NO named hypothesis beyond the F52 regime `r + ε ≤ 7`**. The buffer row is charged at
the proved q-uniform local-count constant (`2A₀`, `A₀` from `EFChi.localCountChi_uniform`); every
input is the tree's: `hNII` (`famNIIUpper_qle_of_design`), `hfrob` (`hfrob_qle_of_design`: the Frobenius row at
`κ_cert` together with Lemma 8.1′), `hrvm` (`famRvMLower_of_design`), the rate
(`budgetTotalProved_isBigO_of_design`). Axioms: `[propext, Classical.choice, Quot.sound]` — no `sorryAx` since the Gallagher rethread (Lemma 6.1 at `Q² + πN`, `ZetaQ/Gallagher.lean`). -/
theorem theorem_one_generic_proved (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hre : r + ε ≤ 7) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_qQ_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.qle Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 2 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 2 * A₀) hloc
  have h := payoff_rate_of_assembly_gen Family.qle r ε hr hε
    (budgetTotalProved (2 * A₀) Family.qle)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_design (2 * A₀) hA₀' Family.qle r ε hr hε design hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_proved Family.qle r ε hr hε hre (2 * A₀) hA₀' hloc'
    (famNIIUpper_qle_of_design r ε hA₀ hloc) (hfrob_qle_of_design r ε hr hε)
    (famRvMLower_of_design r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

/-- **Corollary 2 (dyadic) at the CERTIFIED constant `P_cert = 0.7098`, WITHOUT `SharpZeroDensity`
and with NO named hypothesis beyond `r + ε ≤ 7`**. Every input is the tree's: `hNII`
(`famNIIUpper_dyadic_of_design`), `hfrob` (`hfrob_dyadic_of_design`: the exact dyadic Frobenius row
at the family-aware `rowR2` — F63 — with Lemma 8.1′ discharged), `hrvm`
(`famRvMLower_dyadic_of_design`). (Before F63 `hfrob` was NAMED: the frozen dyadic zone row was
priced at `sZone`, against which the dyadic zone comparison is FALSE — `ZoneData.dyadic_margin_fails`.)
Axioms: as `theorem_one_generic_proved` (no `sorryAx` since the Gallagher rethread). -/
theorem corollary_two_dyadic_proved (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (hre : r + ε ≤ 7) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((Payoff.Pcert_dyad_smooth : ℚ) : ℝ)
          - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * NfamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε)
        ≤ N0sFamCount Family.dyadic Qn (Twin (Qn : ℝ) r ε) (2 * Twin (Qn : ℝ) r ε) := by
  obtain ⟨A₀, hA₀, hloc⟩ := EFChi.localCountChi_uniform
  have hA₀' : (1 : ℝ) ≤ 2 * A₀ := by linarith
  have hloc' := hloc_mono (by linarith : A₀ ≤ 2 * A₀) hloc
  have h := payoff_rate_of_assembly_gen Family.dyadic r ε hr hε
    (budgetTotalProved (2 * A₀) Family.dyadic)
    (fun design hdesign =>
      budgetTotalProved_isBigO_of_design (2 * A₀) hA₀' Family.dyadic r ε hr hε design hdesign) ?_
  · exact h
  obtain ⟨Q₀, hQ₀⟩ := assembly_at_lamStar_proved Family.dyadic r ε hr hε hre (2 * A₀) hA₀' hloc'
    (famNIIUpper_dyadic_of_design r ε hA₀ hloc) (hfrob_dyadic_of_design r ε hr hε)
    (famRvMLower_dyadic_of_design r ε hr hε)
  refine ⟨Q₀, fun Qn hQn => ?_⟩
  obtain ⟨P, hdes, _r₁, _r₂, _r₃, _r₄, _r₅, _θ₀, hbundle⟩ := hQ₀ Qn hQn
  exact ⟨P, hdes, hbundle.2.2.2.2.2.2.2⟩

end JoinProved
end ZetaQ

end
