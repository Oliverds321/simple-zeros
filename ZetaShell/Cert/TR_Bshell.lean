/-
L7_5 (28 Sep 2026), Track R, node R3 proper: `Bshell ℓ α′ C⁺ v_p = shellBq(λ, α′, ℓ, C⁺, d)` (as reals).
Steps: `ψ` even and the kernel depends on `|α|` → `∫ k ψ = 2 ∫_{(0,∞)} k ψ` (`integral_comp_abs`); `ψ = 0` beyond `λ`;
split `(0, λ]` at `1` and `α′` (on each piece `k` is `α`, `ℓ`, `C⁺`); `ψ` there is the polynomial
`(λ/2) ψ̂(α/(λ/2))/mass²` (`TR_Psi`); integrate by `α = (λ/2)β` and the soundness of `pint` (`TR_Poly`);
`mass = (λ/2) Z`. Hypotheses: `1 < α′ < λ` and `mass > 0` (the frozen statement also assumes `λ < 2`, unused).
-/
import ZetaShell.Cert.TR_Psi

open MeasureTheory intervalIntegral

namespace ZetaShell.TR
open ZetaShell.CertQ

theorem cast_pdefint' (p : List ℚ) (lo hi : ℚ) :
    ((pdefint p lo hi : ℚ) : ℝ) = pR (pint p) (hi : ℝ) - pR (pint p) (lo : ℝ) := by
  simp only [pdefint]; push_cast; rw [pR_cast, pR_cast]

theorem kernel_abs (ℓ αp C α : ℝ) : shellKernel ℓ αp C |α| = shellKernel ℓ αp C α := by
  simp only [shellKernel, abs_abs]

/-- the integrand of `Bshell` beyond `ψ(0)`, as a function of `α`. -/
noncomputable def Gk (ℓ αp C : ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ := shellKernel ℓ αp C x * psiS v x

/-- `ψ` on `[0, λ]` in closed form. -/
noncomputable def psiT (S : ShellProfile) (x : ℝ) : ℝ :=
  (S.lam : ℝ) / 2 * pR (psiHat (Ph S)) (x / ((S.lam : ℝ) / 2)) / S.mass ^ 2

theorem continuous_psiT (S : ShellProfile) : Continuous (psiT S) := by
  unfold psiT
  exact (continuous_const.mul ((continuous_pR _).comp (continuous_id.div_const _))).div_const _

theorem psiT_zero (S : ShellProfile) :
    psiT S 0 = (S.lam : ℝ) / 2 * pR (psiHat (Ph S)) 0 / S.mass ^ 2 := by
  unfold psiT; rw [zero_div]

theorem Bshell_eq_formula (S : ShellProfile) (hα : (1 : ℝ) < S.alphaP) (hαl : (S.alphaP : ℝ) < S.lam) :
    Bshell S.level S.alphaP S.Cplus S.v = psiT S 0 + 2 * ((∫ x in (0 : ℝ)..1, x * psiT S x)
      + ((∫ x in (1 : ℝ)..(S.alphaP : ℝ), (S.level : ℝ) * psiT S x)
        + ∫ x in (S.alphaP : ℝ)..(S.lam : ℝ), (S.Cplus : ℝ) * psiT S x)) := by
  have hl : (0 : ℝ) < S.lam := by linarith
  have hψ : ∀ x, 0 ≤ x → x ≤ (S.lam : ℝ) → psiS S.v x = psiT S x :=
    fun x h0 h1 => psiS_eq_psiHat S hl h0 h1
  unfold Bshell
  rw [hψ 0 le_rfl hl.le]
  congr 1
  have hG : (fun α => shellKernel (S.level : ℝ) S.alphaP S.Cplus α * psiS S.v α)
      = fun α => Gk (S.level : ℝ) S.alphaP S.Cplus S.v |α| := by
    funext α; simp only [Gk, kernel_abs, psiS_abs]
  rw [hG, integral_comp_abs]
  congr 1
  have hsub : ∫ x in Set.Ioi (0 : ℝ), Gk (S.level : ℝ) S.alphaP S.Cplus S.v x
      = ∫ x in Set.Ioc (0 : ℝ) S.lam, Gk (S.level : ℝ) S.alphaP S.Cplus S.v x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self
      fun x hx => ?_
    have hx1 : (S.lam : ℝ) < x := not_le.mp fun h => hx.2 ⟨hx.1, h⟩
    simp only [Gk]; rw [psiS_eq_zero S hx1 hl, mul_zero]
  have eq1 : Set.EqOn (fun x => x * psiT S x) (Gk (S.level : ℝ) S.alphaP S.Cplus S.v) (Set.uIoc 0 1) := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    simp only [Gk, shellKernel]
    rw [abs_of_pos hx.1, if_pos hx.2, hψ x hx.1.le (by linarith [hx.2])]
  have eq2 : Set.EqOn (fun x => (S.level : ℝ) * psiT S x) (Gk (S.level : ℝ) S.alphaP S.Cplus S.v)
      (Set.uIoc 1 (S.alphaP : ℝ)) := by
    intro x hx
    rw [Set.uIoc_of_le hα.le] at hx
    simp only [Gk, shellKernel]
    rw [abs_of_pos (by linarith [hx.1] : (0 : ℝ) < x), if_neg (not_le.mpr hx.1), if_pos hx.2,
      hψ x (by linarith [hx.1]) (by linarith [hx.2])]
  have eq3 : Set.EqOn (fun x => (S.Cplus : ℝ) * psiT S x) (Gk (S.level : ℝ) S.alphaP S.Cplus S.v)
      (Set.uIoc (S.alphaP : ℝ) (S.lam : ℝ)) := by
    intro x hx
    rw [Set.uIoc_of_le hαl.le] at hx
    simp only [Gk, shellKernel]
    rw [abs_of_pos (by linarith [hx.1] : (0 : ℝ) < x),
      if_neg (not_le.mpr (by linarith [hx.1] : (1 : ℝ) < x)), if_neg (not_le.mpr hx.1),
      hψ x (by linarith [hx.1]) hx.2]
  have c1 : Continuous (fun x => x * psiT S x) := continuous_id.mul (continuous_psiT S)
  have c2 : Continuous (fun x => (S.level : ℝ) * psiT S x) := continuous_const.mul (continuous_psiT S)
  have c3 : Continuous (fun x => (S.Cplus : ℝ) * psiT S x) := continuous_const.mul (continuous_psiT S)
  have i1 : IntervalIntegrable (Gk (S.level : ℝ) S.alphaP S.Cplus S.v) volume 0 1 :=
    (intervalIntegrable_congr eq1).mp (c1.intervalIntegrable 0 1)
  have i2 : IntervalIntegrable (Gk (S.level : ℝ) S.alphaP S.Cplus S.v) volume 1 (S.alphaP : ℝ) :=
    (intervalIntegrable_congr eq2).mp (c2.intervalIntegrable _ _)
  have i3 : IntervalIntegrable (Gk (S.level : ℝ) S.alphaP S.Cplus S.v) volume (S.alphaP : ℝ) (S.lam : ℝ) :=
    (intervalIntegrable_congr eq3).mp (c3.intervalIntegrable _ _)
  have j1 : ∫ x in (0 : ℝ)..1, Gk (S.level : ℝ) S.alphaP S.Cplus S.v x = ∫ x in (0 : ℝ)..1, x * psiT S x :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => (eq1 hx).symm)
  have j2 : ∫ x in (1 : ℝ)..(S.alphaP : ℝ), Gk (S.level : ℝ) S.alphaP S.Cplus S.v x
      = ∫ x in (1 : ℝ)..(S.alphaP : ℝ), (S.level : ℝ) * psiT S x :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => (eq2 hx).symm)
  have j3 : ∫ x in (S.alphaP : ℝ)..(S.lam : ℝ), Gk (S.level : ℝ) S.alphaP S.Cplus S.v x
      = ∫ x in (S.alphaP : ℝ)..(S.lam : ℝ), (S.Cplus : ℝ) * psiT S x :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => (eq3 hx).symm)
  rw [hsub, ← intervalIntegral.integral_of_le hl.le,
    ← intervalIntegral.integral_add_adjacent_intervals i1 (i2.trans i3),
    ← intervalIntegral.integral_add_adjacent_intervals i2 i3, j1, j2, j3]

theorem integral_pR_div (p : List ℚ) {b : ℝ} (hb : b ≠ 0) (lo hi : ℝ) :
    ∫ x in lo..hi, pR p (x / b) = b * (pR (pint p) (hi / b) - pR (pint p) (lo / b)) := by
  rw [intervalIntegral.integral_comp_div (pR p) hb, smul_eq_mul, integral_pR]

theorem I1_eq (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) (hm : S.mass ≠ 0) :
    ∫ x in (0 : ℝ)..1, x * psiT S x = ((S.lam : ℝ) / 2) ^ 2 / S.mass ^ 2 * (((S.lam : ℝ) / 2) *
      (pR (pint (pmul [0, 1] (psiHat (Ph S)))) (1 / ((S.lam : ℝ) / 2))
        - pR (pint (pmul [0, 1] (psiHat (Ph S)))) 0)) := by
  have hb : (S.lam : ℝ) / 2 ≠ 0 := by positivity
  have e : ∀ x, x * psiT S x
      = ((S.lam : ℝ) / 2) ^ 2 / S.mass ^ 2 * pR (pmul [0, 1] (psiHat (Ph S))) (x / ((S.lam : ℝ) / 2)) := by
    intro x; unfold psiT; rw [pR_pmul]; simp only [pR_cons, pR_nil]; push_cast; field_simp; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_pR_div _ hb, zero_div]

theorem I2_eq (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) (ℓ lo hi : ℝ) :
    ∫ x in lo..hi, ℓ * psiT S x = ℓ * ((S.lam : ℝ) / 2 / S.mass ^ 2 * ((S.lam : ℝ) / 2 *
      (pR (pint (psiHat (Ph S))) (hi / ((S.lam : ℝ) / 2))
        - pR (pint (psiHat (Ph S))) (lo / ((S.lam : ℝ) / 2))))) := by
  have hb : (S.lam : ℝ) / 2 ≠ 0 := by positivity
  have e : ∀ x, ℓ * psiT S x
      = ℓ * ((S.lam : ℝ) / 2 / S.mass ^ 2 * pR (psiHat (Ph S)) (x / ((S.lam : ℝ) / 2))) := by
    intro x; unfold psiT; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pR_div _ hb]

/-- **R3** (as proved; `λ < 2` not needed). -/
theorem Bshell_eq_shellBq' (S : ShellProfile) (h1 : 1 < S.alphaP) (h2 : S.alphaP < S.lam)
    (hm : 0 < S.mass) :
    Bshell S.level S.alphaP S.Cplus S.v
      = ((CertQ.shellBq S.lam S.alphaP S.level S.Cplus S.d : ℚ) : ℝ) := by
  have hα : (1 : ℝ) < S.alphaP := by exact_mod_cast h1
  have hαl : (S.alphaP : ℝ) < S.lam := by exact_mod_cast h2
  have hl : (0 : ℝ) < S.lam := by linarith
  have hb : (S.lam : ℝ) / 2 ≠ 0 := by positivity
  have hZpos : 0 < ((pdefint (Ph S) (-1) 1 : ℚ) : ℝ) := by
    have h := hm
    rw [mass_eq S hl] at h
    exact pos_of_mul_pos_right h (by positivity)
  rw [Bshell_eq_formula S hα hαl, I1_eq S hl hm.ne', I2_eq S hl, I2_eq S hl, psiT_zero]
  have h2l : (S.lam : ℝ) / ((S.lam : ℝ) / 2) = 2 := by field_simp
  rw [h2l, mass_eq S hl]
  simp only [CertQ.shellBq]
  push_cast
  rw [show pmul (spread S.d) (spread S.d) = Ph S from rfl]
  generalize ((pdefint (Ph S) (-1) 1 : ℚ) : ℝ) = Z at hZpos ⊢
  simp only [pR_cast, cast_pdefint']
  push_cast
  have hZ : Z ≠ 0 := hZpos.ne'
  field_simp
  ring

end ZetaShell.TR
