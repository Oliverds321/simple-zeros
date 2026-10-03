/-
L7_3 (round 4): **the design-family transfer at the Shell design** — infrastructure for the open sub-nodes F1c-2 and
F1c-4. ZetaQ proves most of its eventual in-zone facts along an abstract `DesignFamily` (`Zones.lean:1336`: eventually
`Valid`, `Q = Q`, `T = (log Q)^r` with `r ≥ 3`, `cWin` bounded, `L → ∞`, `8w ≤ L` — NO bandwidth clause) and moves
them to the design of record by `InZone.transfer_of_designFamily`. The same transfer works along `ShellDesignM S53L75`:
`designFamily_of_shell` is `InZone.designFamily_of_DoR` with `λ* ≥ 1` replaced by `λ = 1.91 ≥ 1` and `cWinDesign` by
C1's `cWinShell`; `transfer_of_shellDesign` is `transfer_of_designFamily` with A6 (`exists_shellDesignM`) in place of
`exists_designOfRecord`. As a first use, `zone_facts_shell` (ZetaQ's `zone_facts_family`) holds along the Shell design.
PROVED (no `sorry`).
-/
import ZetaShell.ShellK.LF_Defs
import ZetaShell.Design.SD_A6_Exists
import ZetaShell.Design.SD_C1_CWin
import ZetaShell.Cert.R5_ProfileL75

noncomputable section
open Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone

theorem designFamily_of_shell (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (D : ℝ → ParamsQ) (hD : ∀ᶠ Q : ℝ in atTop, Design.ShellDesignM S53L75 r ε Q (D Q)) :
    DesignFamily D (r + ε) where
  valid := hD.mono fun _ h => h.1
  Q_eq := hD.mono fun _ h => h.2.1
  r_ge := by linarith
  T_eq := hD.mono fun Q h => by rw [h.2.2.1]; rfl
  crho_bdd := ⟨Design.cWinShell S53L75, hD.mono fun _ h => le_of_eq (Design.cWin_of_shellDesignM h)⟩
  LB_atTop := by
    have hlow : ∀ᶠ Q : ℝ in atTop, Real.log Q + (-2) ≤ (D Q).LB := by
      filter_upwards [hD, eventually_gt_atTop (0 : ℝ)] with Q h hQ0
      have hv := h.1
      have hQ := h.2.1
      have hlam : 1 ≤ (D Q).lam := by rw [h.2.2.2.1]; norm_num [S53L75]
      have hT1 : (1 : ℝ) ≤ (D Q).T := by linarith [hv.T_ge300]
      have hT0 : (0 : ℝ) < (D Q).T := by linarith
      have hpi0 : 0 < Real.pi := Real.pi_pos
      have h2pi : Real.log (2 * Real.pi) ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by positivity)]
        have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [this]
        have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        have he2 : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 := by
          nlinarith
        have hpi : Real.pi < 3.15 := Real.pi_lt_d2
        linarith
      have hLL : Real.log Q + (-2) ≤ (D Q).LL := by
        unfold ParamsQ.LL
        rw [hQ, Real.log_div (by positivity) (by positivity), Real.log_mul hQ0.ne' hT0.ne']
        have := Real.log_nonneg hT1
        linarith
      have hLL0 : 0 ≤ (D Q).LL := hv.LL_pos.le
      show Real.log Q + (-2) ≤ (D Q).lam * (D Q).LL
      nlinarith
    exact tendsto_atTop_mono' _ hlow (tendsto_atTop_add_const_right _ _ Real.tendsto_log_atTop)
  wrange := hD.mono fun _ h => h.2.2.2.2.2.1

/-- **The transfer to the Shell design**: a predicate holding eventually along every design family holds eventually
at every Shell design point. -/
theorem transfer_of_shellDesign (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (X : ParamsQ → Prop)
    (h : ∀ D : ℝ → ParamsQ, DesignFamily D (r + ε) → ∀ᶠ Q : ℝ in atTop, X (D Q)) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P → X P := by
  classical
  obtain ⟨Q₀, hQ₀⟩ := Design.exists_shellDesignM S53L75_L75 r ε hr hε
  obtain ⟨P₀⟩ : Nonempty ParamsQ := ⟨⟨0, 0, 0, 0, 0, fun _ => 0, 0⟩⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ → ParamsQ, D = fun Q =>
      if h1 : ∃ P, Design.ShellDesignM S53L75 r ε Q P ∧ ¬ X P then Classical.choose h1
      else if h2 : ∃ P, Design.ShellDesignM S53L75 r ε Q P then Classical.choose h2 else P₀ := ⟨_, rfl⟩
  have hDoR : ∀ᶠ Q : ℝ in atTop, Design.ShellDesignM S53L75 r ε Q (D Q) := by
    filter_upwards [eventually_ge_atTop Q₀] with Q hQ
    rw [hDdef]
    dsimp only
    split_ifs with h1 h2
    · exact (Classical.choose_spec h1).1
    · exact Classical.choose_spec h2
    · exact absurd (hQ₀ Q hQ) h2
  have hX := h D (designFamily_of_shell r ε hr hε D hDoR)
  obtain ⟨Q₁, hQ₁⟩ := eventually_atTop.mp hX
  refine eventually_atTop.mpr ⟨⌈Q₁⌉₊, fun Qn hQn P hP => ?_⟩
  by_contra hnot
  have h1 : ∃ P', Design.ShellDesignM S53L75 r ε (Qn : ℝ) P' ∧ ¬ X P' := ⟨P, hP, hnot⟩
  have hQ : Q₁ ≤ (Qn : ℝ) := le_trans (Nat.le_ceil Q₁) (by exact_mod_cast hQn)
  have hXD := hQ₁ (Qn : ℝ) hQ
  rw [hDdef] at hXD
  dsimp only at hXD
  rw [dif_pos h1] at hXD
  exact (Classical.choose_spec h1).2 hXD

/-- ZetaQ's `zone_facts_family` along the Shell design (an input of F1c-2). -/
theorem zone_facts_shell (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      |zoneP P - P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u|
          ≤ ε₀ * (P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u)
        ∧ zoneR P ≤ ε₀ * zoneP P :=
  transfer_of_shellDesign r ε hr hε _ (fun D hD => zone_facts_family D (r + ε) hD hε₀)

end F1c
end ShellK
end ZetaShell
