/-
REORGANISED at integration (L0_5, 28 Sep 2026, lead's ruling b of 12:25): the declarations that need the open
node A7g/A8g (`A8gSimpleStmt`, `A8gDistStmt`, `a8g_*_holds`, the `_cond`/`_cond7` forms and the β-forms, now
`zeta_{simple,distinct}_K{5,7}_of_majorant`) are in `ZetaS/Top/TopSolutionGeneral.lean`; the architect's
`zeta_simple`/`zeta_distinct` (hypothesis `CertMaj`) are removed, superseded by `TopFinal`'s `_K7_final`.
This module is sorry-free in its import closure; its `_V2` forms are the proof route of `TopFinal`.
`TopChallenge.lean` (the four β-form statements with `sorry`) and §5 of `ChallengeZetaS.lean` were removed
(ruling a); the statements below keep their original doc-strings.

lean_work/L3_2/top/TopSolution.lean — PROOFS of the headline statements of `TopChallenge.lean` (K = 5, K = 7) and of
the architect's `zeta_simple`/`zeta_distinct` (`ChallengeZetaS.lean`, K = 7 with `CertMaj`), from the named nodes
(L3_2, 28 Sep 2026). Every node not yet proved enters as its compiled skeleton statement, so `#print axioms` of the
headlines shows `sorryAx` exactly through the open nodes. The `_cond` forms take the statements of the open nodes as
explicit hypotheses (`W2LStmt`, `A8gSimpleStmt`, `A8gDistStmt`) and are level A: this is the proof that the open
nodes are exactly W2L-cos (→ Z9) and A8g (→ A7g) for the K = 5 and K = 7 pairs (report `reports/L3_2b_top.md` §3).

The chain, for X ∈ {Nˢ, N^d} (thm:sigd-Sigma/D proof, Steps 1–4, then the bandwidth limit):
  1. W2L-cos (skeleton; the ζ instance of Z9): for every λ ∈ (0,1) a `FrameFamilyL λ N (R_λ) k_ψ` for ψ = cos 1.6s,
     with the window seams Nˢ(I′) ≤ Nsimple + o(N), N^d(I′) ≤ Ndist + o(N);
  2. A8 (`sigma_abstract`/`dist_abstract`, L2_2, proved modulo A7) for K = 7 with `CertMaj`, or A8g
     (`sigma_abstract_gen`/`dist_abstract_gen`, new skeleton) for any certificate with robust claims (N2 `RobustAM`):
     eventually (Σ(2 − R_λ) − ε)N ≤ Nˢ(I′). The frame family is used through `toFrameFamily` (x-units: the kernel is
     k_ψ at every λ, and Λ ≤ λN + o(N) ≤ N + o(N)); no certificate transfer (KL1m) is needed;
  3. `eps_seam`: the o(N) seam error is absorbed into ε;
     (A8 at the two certificates, from A7g: `A8K.lean`; so the new headlines need A7g, W2L-cos only);
  4. KL2 (`eps_form_of_lam_limit`, proved) with f(λ) = Σ(2 − R_λ(ψ)), KL3 (`tendsto_Rlam_one`, proved) for
     f(λ) → Σ(H(ψ)), and N1 (`num_sigma`, `num_sigma_K5`, proved) for c < Σ(H(ψ)).
-/
import ZetaS.Top.TopDefs
import ZetaS.Top.N1_Numerics
import ZetaS.Top.N2_Robust
import ZetaS.SigmaDist.A8_SigmaDistAbstract
import ZetaS.Bandwidth.KL2_LamLimit
import ZetaS.Bandwidth.KL3_TendstoRlam
import ZetaS.Window.W2L_ZetaFrameCos
import ZetaS.Top.A8K
import ZetaS.Top.A7K5
import ZetaS.Top.A7K7b

open Filter Topology Asymptotics

namespace ZetaS
namespace Top

/-! ### The statements of the open nodes, as Props -/

/-- The statement of the open node **W2L-cos** at α = 8/5 (skeleton `zeta_frameFamily_cos`, the ζ instance of Z9). -/
def W2LStmt : Prop := ∀ {lam : ℝ}, 0 < lam → lam < 1 →
    ∃ Fm : FrameFamilyL lam (fun T => (Ncount T (2 * T) : ℝ)) (Rlam lam (fun s => Real.cos (8 / 5 * s)))
        (kPsi (fun s => Real.cos (8 / 5 * s))),
      ∃ r : ℝ → ℝ, r =o[atTop] (fun T => (Ncount T (2 * T) : ℝ)) ∧ ∀ᶠ T in atTop,
        ((Fm.F T).NsW : ℝ) ≤ Nsimple T (2 * T) + r T ∧
        ((Fm.F T).NdW : ℝ) ≤ Ndist T (2 * T) + r T ∧
        ((Fm.F T).NscW : ℝ) ≤ Nsc T (2 * T) + r T

theorem w2l_holds : W2LStmt := fun h0 h1 => zeta_frameFamily_cos (by norm_num) le_rfl h0 h1

/-! ### The assembly -/

lemma int_psiCos16_ne : (∫ s in (-(1 / 2 : ℝ))..(1 / 2), psiCos16 s) ≠ 0 := by
  rw [N2r.den_eq]
  have := CosWindow.sin_four_fifths.1
  exact ne_of_gt (by linarith)

/-- A frame bound up to an `o(N)` seam error gives the ε-form for the count. -/
lemma eps_seam {N Y X r : ℝ → ℝ} {f : ℝ} (hN : ∀ T, 0 ≤ N T)
    (hY : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (f - ε) * N T ≤ Y T)
    (hr : r =o[atTop] N) (hseam : ∀ᶠ T in atTop, Y T ≤ X T + r T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (f - ε) * N T ≤ X T := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := hY (ε / 2) (by linarith)
  have hb := hr.bound (show (0 : ℝ) < ε / 2 by linarith)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (hb.and hseam)
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  obtain ⟨h2, h3⟩ := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hN T)] at h2
  have h4 := le_abs_self (r T)
  nlinarith

/-- Steps 1–3 at one bandwidth, simple zeros. -/
theorem simple_at_lam (hW2L : W2LStmt) {f : ℝ → ℝ}
    (hA : ∀ (N : ℝ → ℝ) (R : ℝ) (Fm : FrameFamily N R (kPsi psiCos16)),
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (f R - ε) * N T ≤ ((Fm.F T).NsW : ℝ))
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (f (Rlam lam psiCos16) - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) := by
  obtain ⟨Fm, r, hr, hseam⟩ := hW2L h0 h1
  exact eps_seam (fun T => Nat.cast_nonneg _) (hA _ _ Fm.toFrameFamily) hr (hseam.mono fun T h => h.1)

/-- Steps 1–3 at one bandwidth, distinct zeros. -/
theorem dist_at_lam (hW2L : W2LStmt) {f : ℝ → ℝ}
    (hA : ∀ (N : ℝ → ℝ) (R : ℝ) (Fm : FrameFamily N R (kPsi psiCos16)),
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (f R - ε) * N T ≤ ((Fm.F T).NdW : ℝ))
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (f (Rlam lam psiCos16) - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  obtain ⟨Fm, r, hr, hseam⟩ := hW2L h0 h1
  exact eps_seam (fun T => Nat.cast_nonneg _) (hA _ _ Fm.toFrameFamily) hr (hseam.mono fun T h => h.2.1)

theorem sigma_lim (a₁ a₂ ν : ℝ) :
    Tendsto (fun lam => sigmaConst (2 - Rlam lam psiCos16) a₁ a₂ ν) (𝓝[<] 1)
      (𝓝 (sigmaConst (Hpsi psiCos16) a₁ a₂ ν)) := by
  have h := tendsto_Rlam_one psiCos16 int_psiCos16_ne
  unfold sigmaConst Hpsi
  exact (((tendsto_const_nhds.sub h).add tendsto_const_nhds).sub tendsto_const_nhds).div_const _

theorem dist_lim (a₁ a₂ ν : ℝ) :
    Tendsto (fun lam => distConst (2 - Rlam lam psiCos16) a₁ a₂ ν) (𝓝[<] 1)
      (𝓝 (distConst (Hpsi psiCos16) a₁ a₂ ν)) := by
  have h := tendsto_Rlam_one psiCos16 int_psiCos16_ne
  unfold distConst Hpsi
  exact ((((tendsto_const_nhds.add (tendsto_const_nhds.sub h)).add tendsto_const_nhds).sub
    tendsto_const_nhds).sub tendsto_const_nhds).div_const _

/-- Step 4: the bandwidth limit (KL2 + KL3) and the closing numerics. -/
theorem headline_simple (hW2L : W2LStmt) {a₁ a₂ ν c : ℝ}
    (hA : ∀ (N : ℝ → ℝ) (R : ℝ) (Fm : FrameFamily N R (kPsi psiCos16)), ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) a₁ a₂ ν - ε) * N T ≤ ((Fm.F T).NsW : ℝ))
    (hc : c < sigmaConst (Hpsi psiCos16) a₁ a₂ ν) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  eps_form_of_lam_limit (lam₀ := 0) (f := fun lam => sigmaConst (2 - Rlam lam psiCos16) a₁ a₂ ν) (by norm_num)
    (Eventually.of_forall fun T => Nat.cast_nonneg _)
    (fun lam hl => simple_at_lam hW2L (f := fun R => sigmaConst (2 - R) a₁ a₂ ν) hA hl.1 hl.2)
    (sigma_lim a₁ a₂ ν) hc.le

theorem headline_dist (hW2L : W2LStmt) {a₁ a₂ ν c : ℝ}
    (hA : ∀ (N : ℝ → ℝ) (R : ℝ) (Fm : FrameFamily N R (kPsi psiCos16)), ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) a₁ a₂ ν - ε) * N T ≤ ((Fm.F T).NdW : ℝ))
    (hc : c < distConst (Hpsi psiCos16) a₁ a₂ ν) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  eps_form_of_lam_limit (lam₀ := 0) (f := fun lam => distConst (2 - Rlam lam psiCos16) a₁ a₂ ν) (by norm_num)
    (Eventually.of_forall fun T => Nat.cast_nonneg _)
    (fun lam hl => dist_at_lam hW2L (f := fun R => distConst (2 - R) a₁ a₂ ν) hA hl.1 hl.2)
    (dist_lim a₁ a₂ ν) hc.le

/-! ### With L2_2's `CertMajV2 := MajorantCert psiCos16 (33/10)` (lean_work/L2_2/CertMajV2.lean; stated here by its
body, so that this file does not import the M-cert modules). The K = 5 pair goes through `A7K5` (A7 and A8 at K = 5,
proved: L4_1's proof with the K = 5 numerals), and the K = 7 pair through `A7K7b` (L4_1's `OLL.oll_height` at any
β ≤ 33/10); so their only open node is W2L-cos (→ Z9, whose last open lemma is the Fubini identity). -/

theorem zeta_simple_K5_V2 (hcert : CertAM5) (hmaj : MajorantCert psiCos16 (33 / 10)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((675158622 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  headline_simple w2l_holds (fun _ _ Fm => A7K5.sigma_K5' Fm hcert hmaj le_rfl) num_sigma_K5

theorem zeta_distinct_K5_V2 (hcert : CertAM5) (hmaj : MajorantCert psiCos16 (33 / 10)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((837579311 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  headline_dist w2l_holds (fun _ _ Fm => A7K5.dist_K5' Fm hcert hmaj le_rfl) num_dist_K5

theorem zeta_simple_K7_V2 (hcert : CertAM7) (hmaj : MajorantCert psiCos16 (33 / 10)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((676102666 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Nsimple T (2 * T) :=
  headline_simple w2l_holds (fun _ _ Fm => A7K7b.sigma_K7' Fm hcert hmaj le_rfl) num_sigma

theorem zeta_distinct_K7_V2 (hcert : CertAM7) (hmaj : MajorantCert psiCos16 (33 / 10)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((838051333 : ℝ) / 10 ^ 9 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  headline_dist w2l_holds (fun _ _ Fm => A7K7b.dist_K7' Fm hcert hmaj le_rfl) num_dist

end Top
end ZetaS
