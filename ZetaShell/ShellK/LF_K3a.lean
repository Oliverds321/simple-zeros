/-
K3a (L7_3, round 8): **K7 at the Shell design**, in ZetaQ's objects. The bandwidth is `S53L75.lam = 191/100`.
K7 (`ZetaShell.LemmaK.killed_pointwise`, imported from green, followup-trunk 5c4c62d) is stated for every
`1 < λ < 2` (checked in its source: `(hlam1 : 1 < lam) (hlam2 : lam < 2)`), so no new analysis is needed. The proof
is `killed_pointwise_at`'s bridge (K8d: `charSum = Achi`, `l2sq = normA2`, `Xlam λ Q T = 𝒳`) with `λ* ↦ λ_Shell`
and `DesignOfRecord ↦ ShellDesignM` (same field order for `Q`, `T`, `λ`).
-/
import ZetaShell.ShellK.L10_KDefs
import ZetaShell.LemmaK.LK_K8a1_KilledMaster

noncomputable section
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaShell.LemmaK

/-- **K3a.** `F(s) ≤ sieveBudgetQ·‖a‖² − Q²·savWeight + errWeight` for every `s`, eventually along the Shell design. -/
theorem killed_pointwise_shell (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ C₁ : ℝ, ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      ∀ s : ℝ, FfamZ P Qn s ≤ sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s := by
  have hl1 : (1 : ℝ) < ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  have hl2 : ((S53L75.lam : ℚ) : ℝ) < 2 := by norm_num [S53L75]
  obtain ⟨C₁, hK7⟩ := killed_pointwise ((S53L75.lam : ℚ) : ℝ) r ε hl1 hl2 hr hε
  refine ⟨C₁, ?_⟩
  filter_upwards [hK7] with Qn hk
  intro P hdes s
  have hQR : P.Q = (Qn : ℝ) := hdes.2.1
  have hTT : ZetaQ.Twin (Qn : ℝ) r ε = P.T := hdes.2.2.1.symm
  have hlam : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
  have hXX : Xlam ((S53L75.lam : ℚ) : ℝ) (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) = P.XQ := by
    rw [hTT, ← hlam, ← hQR]; exact Xlam_eq_XQ P
  have hcs : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ZetaQ.charSum q ⌊P.XQ⌋₊ (acoef P.T s) χ = Achi P χ s := by
    intro q χ
    have h := charSum_eq_AchiC P χ s
    rw [Xlam_eq_XQ] at h
    exact h
  have hl2' : ZetaQ.l2sq ⌊P.XQ⌋₊ (acoef P.T s) = normA2 P s := by
    have h := l2sq_eq_normA2 P s
    rw [Xlam_eq_XQ] at h
    exact h
  have hk' := hk s
  rw [hXX, hTT, hl2'] at hk'
  simp only [hcs] at hk'
  have hfs : FfamZ P Qn s = ∑ q ∈ Finset.Icc 2 Qn, ∑ χ ∈ ZetaQ.primitiveChars q, ‖Achi P χ s‖ ^ 2 := rfl
  rw [hfs]
  unfold savWeight errWeight sieveBudgetQ
  rw [hQR]
  linarith [hk']

end F1c
end ShellK
end ZetaShell
