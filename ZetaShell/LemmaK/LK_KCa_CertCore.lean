/-
Node KCa (L7_3): the CORE of the killed-kernel certificate at ZetaQ's design profile — the three facts K8b consumes —
`Cfam ≤ C⁺`, `v_p` admissible at `λ*`, and `B^K_{C⁺}(v_p) ≤ 2 − 0.72351` for the REAL-VALUED functional.
(The full `KCert profDesignQle`, with the artifact's side conditions `Side`, stays node KC; K8b does not use `Side`.)

Proof:
* `B^K_C = Bshell C α′ C` for ANY `α′` (the Shell kernel with level `ℓ = C` is the killed kernel), so at
  `α′ = 6/5 ∈ (1, λ*)` L7_5's analytic identity R3 (`ZetaShell.Bshell_eq_shellBq`, level A, `lean_work/L7_5/`,
  imported from its compiled modules) gives the exact rational `CertQ.shellBq λ* (6/5) C⁺ C⁺ d`, with
  `dᵢ = cᵢ(λ*/2)^{2i}`;
* that rational is `≤ 2 − 0.72351` by `decide +kernel` (value 0.72351108…; the level term and the `C⁺` term
  merge);
* admissibility and `mass > 0` come from ZetaQ at any design point (`vProfile_admissible`, `profMass_pos`) through
  `vProfile P = profDesignQle.v`;
* `π⁴/18 ≤ C⁺` from `Real.pi_lt_d20`.
Level A.
-/
import ZetaShell.LemmaK.LK_K01_BKmonoC
import ZetaShell.Cert.R3_ShellPayoffFormula

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Payoff

/-- ZetaQ's certified profile `vProfile P` at any point with ZetaQ's design `λ*` and profile is `profDesignQle.v`. -/
theorem vProfile_eq_profDesignQle' {P : ParamsQ} (hlam : P.lam = Family.qle.lamStar)
    (hprof : P.prof = Family.qle.designProfile) : vProfile P = profDesignQle.v := by
  have hlam' : P.lam = ((profDesignQle.lam : ℚ) : ℝ) := by
    rw [hlam]
    simp only [Family.lamStar, profDesignQle, lamStarQ, ZetaQ.lamStar]
    norm_num
  have hprof' : ∀ t, P.prof.eval t = profDesignQle.p t := by
    intro t
    rw [hprof]
    simp [Family.designProfile, designProfileQle, KProfile.p, profDesignQle, ZetaQ.Payoff.evalPoly]
    ring
  funext t
  simp only [vProfile, KProfile.v, KProfile.mass, hlam', hprof']

/-- the y-unit data of `profDesignQle`: `dᵢ = cᵢ (λ*/2)^{2i}`. -/
def dDesign : List ℚ :=
  [1, (-81257 / 125000) * (2501464303 / 4000000000) ^ 2, (3458583 / 1000000) * (2501464303 / 4000000000) ^ 4,
    (-3669851 / 200000) * (2501464303 / 4000000000) ^ 6]

/-- `profDesignQle` as a Shell profile with `α′ = 6/5`, level `= C⁺` (so the Shell kernel is the killed kernel). -/
def shellDesign : ShellProfile where
  lam := lamStarQ
  alphaP := 6 / 5
  level := 541161617 / 100000000
  Cplus := 541161617 / 100000000
  d := dDesign

theorem shellDesign_p (t : ℝ) : shellDesign.p t = profDesignQle.p t := by
  rw [ZetaShell.TR.p_eq]
  simp [shellDesign, dDesign, profDesignQle, lamStarQ, ZetaShell.TR.pR, KProfile.p, ZetaQ.Payoff.evalPoly]
  ring

theorem shellDesign_v : shellDesign.v = profDesignQle.v := by
  have hl : ((shellDesign.lam : ℚ) : ℝ) = ((profDesignQle.lam : ℚ) : ℝ) := rfl
  funext t
  simp only [ShellProfile.v, ShellProfile.mass, KProfile.v, KProfile.mass, hl, shellDesign_p]

theorem shellKernel_level_eq (C αp α : ℝ) : shellKernel C αp C α = killedKernel C α := by
  unfold shellKernel killedKernel
  split_ifs <;> rfl

theorem BK_eq_Bshell (C αp : ℝ) (v : ℝ → ℝ) : BK C v = Bshell C αp C v := by
  unfold BK Bshell
  simp only [shellKernel_level_eq]
  rfl

/-- the kernel computation (L7_1's `CertQ.shellBq`, as consumed by R3). -/
theorem shellBq_design_le :
    ZetaShell.CertQ.shellBq lamStarQ (6 / 5) (541161617 / 100000000) (541161617 / 100000000) dDesign
      ≤ 2 - 72351 / 100000 := by
  unfold lamStarQ dDesign
  decide +kernel

theorem Cfam_le_Cplus : ZetaQ.Cfam ≤ ((541161617 / 100000000 : ℚ) : ℝ) := by
  have h := Real.pi_lt_d20
  have h0 := Real.pi_pos
  have h4 : Real.pi ^ 4 ≤ (3.14159265358979323847 : ℝ) ^ 4 := pow_le_pow_left₀ h0.le h.le 4
  unfold ZetaQ.Cfam
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

/-- **KCa.** The certificate core at ZetaQ's design profile. -/
theorem certKD_core :
    ZetaQ.Cfam ≤ ((profDesignQle.Cplus : ℚ) : ℝ) ∧
      Admissible ((profDesignQle.lam : ℚ) : ℝ) profDesignQle.v ∧
      BK ((profDesignQle.Cplus : ℚ) : ℝ) profDesignQle.v ≤ 2 - 72351 / 100000 := by
  -- a design point of ZetaQ (any r ≥ 3, ε > 0)
  obtain ⟨Q₀, hQ₀⟩ := exists_designOfRecordM Family.qle 3 1 le_rfl one_pos
  obtain ⟨P, hdes⟩ := hQ₀ Q₀ le_rfl
  have hP := hdes.1
  have hlam : P.lam = Family.qle.lamStar := hdes.2.2.2.1
  have hprof : P.prof = Family.qle.designProfile := hdes.2.2.2.2.2.2.2.2.2.2.2
  have hv := vProfile_eq_profDesignQle' hlam hprof
  have hlam' : P.lam = ((profDesignQle.lam : ℚ) : ℝ) := by
    rw [hlam]; simp only [Family.lamStar, profDesignQle, lamStarQ, ZetaQ.lamStar]; norm_num
  have hadm : Admissible ((profDesignQle.lam : ℚ) : ℝ) profDesignQle.v := by
    have := vProfile_admissible hP
    rw [hv, hlam'] at this
    exact this
  refine ⟨Cfam_le_Cplus, hadm, ?_⟩
  -- mass > 0: `shellDesign.mass = profMass P`
  have hmass : 0 < shellDesign.mass := by
    have hpm := profMass_pos hP
    have e : shellDesign.mass = profMass P := by
      unfold ShellProfile.mass profMass
      rw [hlam']
      congr 1
      funext t
      rw [shellDesign_p]
      have : P.prof.eval t = profDesignQle.p t := by
        rw [hprof]
        simp [Family.designProfile, designProfileQle, KProfile.p, profDesignQle, ZetaQ.Payoff.evalPoly]
        ring
      rw [this]
    rw [e]; exact hpm
  have hR3 := ZetaShell.Bshell_eq_shellBq shellDesign (by norm_num [shellDesign])
    (by norm_num [shellDesign, lamStarQ]) (by norm_num [shellDesign, lamStarQ]) hmass
  have hk : ((ZetaShell.CertQ.shellBq shellDesign.lam shellDesign.alphaP shellDesign.level shellDesign.Cplus
      shellDesign.d : ℚ) : ℝ) ≤ 2 - 72351 / 100000 := by
    have := shellBq_design_le
    have h' : ((ZetaShell.CertQ.shellBq lamStarQ (6 / 5) (541161617 / 100000000) (541161617 / 100000000) dDesign
        : ℚ) : ℝ) ≤ ((2 - 72351 / 100000 : ℚ) : ℝ) := by exact_mod_cast this
    simpa [shellDesign] using h'
  rw [BK_eq_Bshell _ ((shellDesign.alphaP : ℚ) : ℝ), ← shellDesign_v]
  have hlev : ((profDesignQle.Cplus : ℚ) : ℝ) = ((shellDesign.level : ℚ) : ℝ) := rfl
  have hcp : ((profDesignQle.Cplus : ℚ) : ℝ) = ((shellDesign.Cplus : ℚ) : ℝ) := rfl
  calc Bshell ((profDesignQle.Cplus : ℚ) : ℝ) ((shellDesign.alphaP : ℚ) : ℝ) ((profDesignQle.Cplus : ℚ) : ℝ)
        shellDesign.v
      = Bshell ((shellDesign.level : ℚ) : ℝ) ((shellDesign.alphaP : ℚ) : ℝ) ((shellDesign.Cplus : ℚ) : ℝ)
        shellDesign.v := by rw [← hlev, ← hcp]
    _ = _ := hR3
    _ ≤ _ := hk

end LemmaK
end ZetaShell
