/-
L7_5 (28 Sep 2026), round 9: the non-stationary phase estimate `nsp_core` (the content of the leaf `nsp_single`):
  `|∫ Ξ(u/κ) e^{σu} e^{i(λu − c e^u)} du| ≤ C |λ|^{−m}`  for `4|c|e^κ ≤ |λ|`, uniformly in `σ = β − 1/2 ∈ [−1/2, 1/2]`.
With `s = c/λ` (`|s|e^κ ≤ 1/4`), `r = 1/(1 − s e^u)`, `M f = (f r)′`:
  `∫ f E = (i/λ) ∫ (M f) E`  for `f` smooth with support in `[−κ, κ]`  (`ibp_step`),
and on the family `P_{i,a,p} = Ξ^{(i)}(u/κ) e^{σu} · s^a e^{au} r^p`:
  `M P_{i,a,p} = κ^{−1} P_{i+1,a,p+1} + (σ + a) P_{i,a,p+1} + (p+1) P_{i,a+1,p+2}`,
so `|M^n P_{i,a,p}| ≤ κ^{−n} (a+p+3n+3)^n 2^{p+2n} Z` (`Mit_bound`).
-/
import ZetaShell.PropZ.ZDefs

open MeasureTheory Complex
open ZetaShell.PropZ (NearCutoff)

namespace ZetaShell.NSP

noncomputable def rr (s u : ℝ) : ℝ := (1 - s * Real.exp u)⁻¹

noncomputable def QQ (s : ℝ) (a p : ℕ) (u : ℝ) : ℝ := s ^ a * Real.exp (a * u) * rr s u ^ p

noncomputable def XX (κ : ℝ) (Ξ : ℝ → ℝ) (σ : ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  iteratedDeriv i Ξ (u / κ) * Real.exp (σ * u)

noncomputable def PP (κ : ℝ) (Ξ : ℝ → ℝ) (σ s : ℝ) (i a p : ℕ) (u : ℝ) : ℝ := XX κ Ξ σ i u * QQ s a p u

noncomputable def MM (s : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun u => deriv (fun v => f v * rr s v) u

noncomputable def Mit (s : ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Mit s n (MM s f)

def Good (κ : ℝ) (f : ℝ → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ Set.Icc (-κ) κ

theorem tsupport_iD (F : ℝ → ℝ) : ∀ n : ℕ, tsupport (iteratedDeriv n F) ⊆ tsupport F
  | 0 => by simp only [iteratedDeriv_zero]; exact le_rfl
  | n + 1 => by rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans (tsupport_iD F n)

theorem iD_smooth (F : ℝ → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n F) := by
  rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv n hF

section fixed

variable (κ : ℝ) (Ξ : ℝ → ℝ) (σ s : ℝ)

/-- the open set where `r` is smooth. -/
def OO : Set ℝ := {u | |s * Real.exp u| < 1 / 2}

theorem OO_open : IsOpen (OO s) := isOpen_lt (by fun_prop) continuous_const

theorem Icc_sub_OO (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) : Set.Icc (-κ) κ ⊆ OO s := by
  intro u hu
  show |s * Real.exp u| < 1 / 2
  rw [abs_mul, abs_of_pos (Real.exp_pos u)]
  have : Real.exp u ≤ Real.exp κ := Real.exp_le_exp.mpr hu.2
  have := mul_le_mul_of_nonneg_left this (abs_nonneg s)
  linarith

theorem rr_ne (u : ℝ) (hu : u ∈ OO s) : 1 - s * Real.exp u ≠ 0 := by
  intro h
  have : s * Real.exp u = 1 := by linarith
  have hu' : |s * Real.exp u| < 1 / 2 := hu
  rw [this, abs_one] at hu'; linarith

theorem rr_contDiffAt (u : ℝ) (hu : u ∈ OO s) : ContDiffAt ℝ (⊤ : ℕ∞) (rr s) u :=
  (contDiffAt_const.sub (contDiffAt_const.mul Real.contDiff_exp.contDiffAt)).inv (rr_ne s u hu)

theorem QQ_contDiffAt (a p : ℕ) (u : ℝ) (hu : u ∈ OO s) : ContDiffAt ℝ (⊤ : ℕ∞) (QQ s a p) u :=
  (contDiffAt_const.mul (Real.contDiff_exp.contDiffAt.comp u (contDiffAt_const.mul contDiffAt_id))).mul
    ((rr_contDiffAt s u hu).pow p)

theorem mul_good (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) (f g : ℝ → ℝ) (hf : Good κ f)
    (hg : ∀ u ∈ OO s, ContDiffAt ℝ (⊤ : ℕ∞) g u) : Good κ (fun u => f u * g u) := by
  refine ⟨contDiff_iff_contDiffAt.mpr fun u => ?_, (tsupport_mul_subset_left).trans hf.2⟩
  by_cases hu : u ∈ OO s
  · exact hf.1.contDiffAt.mul (hg u hu)
  · have hnt : u ∉ tsupport f := fun h => hu (Icc_sub_OO κ s hκ hs (hf.2 h))
    have hev := notMem_tsupport_iff_eventuallyEq.mp hnt
    have : (fun v => f v * g v) =ᶠ[nhds u] fun _ => (0 : ℝ) := hev.mono fun v hv => by
      simp only [Pi.zero_apply] at hv; show f v * g v = 0; rw [hv, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem XX_good (hκ : 0 < κ) (hΞ : NearCutoff Ξ) (i : ℕ) : Good κ (XX κ Ξ σ i) := by
  refine ⟨((iD_smooth Ξ hΞ.smooth i).comp (contDiff_id.div_const κ)).mul
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)), ?_⟩
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have h1 : iteratedDeriv i Ξ (u / κ) ≠ 0 := fun h => hu (by simp only [XX, h, zero_mul])
  have h2 : u / κ ∈ Set.Ioo (-1 : ℝ) 1 := hΞ.supp (tsupport_iD Ξ i (subset_tsupport _ h1))
  have h3 := h2.1; have h4 := h2.2
  rw [lt_div_iff₀ hκ] at h3; rw [div_lt_iff₀ hκ] at h4
  exact ⟨by linarith, by linarith⟩

theorem PP_good (hκ : 0 < κ) (hΞ : NearCutoff Ξ) (hs : |s| * Real.exp κ ≤ 1 / 4) (i a p : ℕ) :
    Good κ (PP κ Ξ σ s i a p) :=
  mul_good κ s hκ hs _ _ (XX_good κ Ξ σ hκ hΞ i) (fun u hu => QQ_contDiffAt s a p u hu)

theorem fr_smooth (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) (f : ℝ → ℝ) (hf : Good κ f) :
    Good κ (fun u => f u * rr s u) :=
  mul_good κ s hκ hs _ _ hf (fun u hu => rr_contDiffAt s u hu)

theorem MM_good (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) (f : ℝ → ℝ) (hf : Good κ f) :
    Good κ (MM s f) := by
  have h := fr_smooth κ s hκ hs f hf
  refine ⟨(contDiff_infty_iff_deriv.mp h.1).2, ?_⟩
  exact tsupport_deriv_subset.trans h.2

theorem diff_of_good (f : ℝ → ℝ) (hf : Good κ f) : Differentiable ℝ f :=
  (hf.1.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 f).differentiable one_ne_zero

theorem MM_add (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) (f g : ℝ → ℝ) (hf : Good κ f) (hg : Good κ g) :
    MM s (fun u => f u + g u) = fun u => MM s f u + MM s g u := by
  funext u
  unfold MM
  have e : (fun v => (f v + g v) * rr s v) = fun v => f v * rr s v + g v * rr s v := by funext v; ring
  rw [e]
  exact deriv_add (diff_of_good κ _ (fr_smooth κ s hκ hs f hf) u) (diff_of_good κ _ (fr_smooth κ s hκ hs g hg) u)

theorem MM_smul (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) (k : ℝ) (f : ℝ → ℝ) (hf : Good κ f) :
    MM s (fun u => k * f u) = fun u => k * MM s f u := by
  funext u
  unfold MM
  have e : (fun v => k * f v * rr s v) = fun v => k * (f v * rr s v) := by funext v; ring
  rw [e]
  exact deriv_const_mul k (diff_of_good κ _ (fr_smooth κ s hκ hs f hf) u)

theorem good_add (f g : ℝ → ℝ) (hf : Good κ f) (hg : Good κ g) : Good κ (fun u => f u + g u) :=
  ⟨hf.1.add hg.1, (tsupport_add f g).trans (Set.union_subset hf.2 hg.2)⟩

theorem good_smul (k : ℝ) (f : ℝ → ℝ) (hf : Good κ f) : Good κ (fun u => k * f u) :=
  ⟨contDiff_const.mul hf.1, (tsupport_mul_subset_right (f := fun _ => k) (g := f)).trans hf.2⟩

theorem Mit_good (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) :
    ∀ (n : ℕ) (f : ℝ → ℝ), Good κ f → Good κ (Mit s n f)
  | 0, f, hf => hf
  | n + 1, f, hf => Mit_good hκ hs n (MM s f) (MM_good κ s hκ hs f hf)

theorem Mit_add (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) :
    ∀ (n : ℕ) (f g : ℝ → ℝ), Good κ f → Good κ g →
      Mit s n (fun u => f u + g u) = fun u => Mit s n f u + Mit s n g u
  | 0, f, g, _, _ => rfl
  | n + 1, f, g, hf, hg => by
    show Mit s n (MM s (fun u => f u + g u)) = fun u => Mit s n (MM s f) u + Mit s n (MM s g) u
    rw [MM_add κ s hκ hs f g hf hg]
    exact Mit_add hκ hs n _ _ (MM_good κ s hκ hs f hf) (MM_good κ s hκ hs g hg)

theorem Mit_smul (hκ : 0 < κ) (hs : |s| * Real.exp κ ≤ 1 / 4) :
    ∀ (n : ℕ) (k : ℝ) (f : ℝ → ℝ), Good κ f → Mit s n (fun u => k * f u) = fun u => k * Mit s n f u
  | 0, k, f, _ => rfl
  | n + 1, k, f, hf => by
    show Mit s n (MM s (fun u => k * f u)) = fun u => k * Mit s n (MM s f) u
    rw [MM_smul κ s hκ hs k f hf]
    exact Mit_smul hκ hs n k _ (MM_good κ s hκ hs f hf)

end fixed


section fixed2

variable (κ : ℝ) (Ξ : ℝ → ℝ) (σ s : ℝ)

theorem PP_r (i a p : ℕ) (u : ℝ) : PP κ Ξ σ s i a p u * rr s u = PP κ Ξ σ s i a (p + 1) u := by
  simp only [PP, QQ, pow_succ]; ring

theorem hasDerivAt_rr (u : ℝ) (hu : u ∈ OO s) : HasDerivAt (rr s) (s * Real.exp u * rr s u ^ 2) u := by
  have h := ((hasDerivAt_const u (1 : ℝ)).sub ((Real.hasDerivAt_exp u).const_mul s)).inv (rr_ne s u hu)
  refine h.congr_deriv ?_
  simp only [rr, Pi.sub_apply]; field_simp; ring

theorem XX_zero (hκ : 0 < κ) (hΞ : NearCutoff Ξ) (i : ℕ) (u : ℝ) (hu : u ∉ Set.Icc (-κ) κ) : XX κ Ξ σ i u = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hu ((XX_good κ Ξ σ hκ hΞ i).2 h)

theorem hasDerivAt_PP (hκ : 0 < κ) (hΞ : NearCutoff Ξ) (hs : |s| * Real.exp κ ≤ 1 / 4) (i a p : ℕ) (u : ℝ) :
    HasDerivAt (PP κ Ξ σ s i a (p + 1))
      (κ⁻¹ * PP κ Ξ σ s (i + 1) a (p + 1) u + (σ + a) * PP κ Ξ σ s i a (p + 1) u
        + (p + 1) * PP κ Ξ σ s i (a + 1) (p + 2) u) u := by
  by_cases hu : u ∈ OO s
  · have hd : Differentiable ℝ (iteratedDeriv i Ξ) :=
      ((iD_smooth Ξ hΞ.smooth i).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 _).differentiable one_ne_zero
    have h1 : HasDerivAt (iteratedDeriv i Ξ) (iteratedDeriv (i + 1) Ξ (u / κ)) (u / κ) := by
      rw [iteratedDeriv_succ]; exact (hd (u / κ)).hasDerivAt
    have h3 := h1.comp u ((hasDerivAt_id' u).div_const κ)
    have h4 : HasDerivAt (fun u => Real.exp (σ * u)) (Real.exp (σ * u) * (σ * 1)) u :=
      (Real.hasDerivAt_exp _).comp u ((hasDerivAt_id' u).const_mul σ)
    have hX := h3.mul h4
    have h5 : HasDerivAt (fun u => Real.exp (a * u)) (Real.exp (a * u) * (a * 1)) u :=
      (Real.hasDerivAt_exp _).comp u ((hasDerivAt_id' u).const_mul (a : ℝ))
    have hQ := ((hasDerivAt_const u (s ^ a)).mul h5).mul ((hasDerivAt_rr s u hu).pow (p + 1))
    have := hX.mul hQ
    refine this.congr_deriv ?_
    simp only [PP, XX, QQ, Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel, add_mul, one_mul, Real.exp_add, pow_add, pow_one]
    ring
  · have hIcc : u ∉ Set.Icc (-κ) κ := fun h => hu (Icc_sub_OO κ s hκ hs h)
    have hev : PP κ Ξ σ s i a (p + 1) =ᶠ[nhds u] fun _ => (0 : ℝ) := by
      have hnt : u ∉ tsupport (PP κ Ξ σ s i a (p + 1)) :=
        fun h => hIcc ((PP_good κ Ξ σ s hκ hΞ hs i a (p + 1)).2 h)
      exact notMem_tsupport_iff_eventuallyEq.mp hnt
    refine ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [PP, XX_zero κ Ξ σ hκ hΞ _ u hIcc, zero_mul, mul_zero, add_zero]

theorem MM_PP (hκ : 0 < κ) (hΞ : NearCutoff Ξ) (hs : |s| * Real.exp κ ≤ 1 / 4) (i a p : ℕ) :
    MM s (PP κ Ξ σ s i a p) = fun u => κ⁻¹ * PP κ Ξ σ s (i + 1) a (p + 1) u
      + (σ + a) * PP κ Ξ σ s i a (p + 1) u + (p + 1) * PP κ Ξ σ s i (a + 1) (p + 2) u := by
  funext u
  unfold MM
  rw [show (fun v => PP κ Ξ σ s i a p v * rr s v) = PP κ Ξ σ s i a (p + 1) from
    funext fun v => PP_r κ Ξ σ s i a p v]
  exact (hasDerivAt_PP κ Ξ σ s hκ hΞ hs i a p u).deriv

theorem PP_bound (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hΞ : NearCutoff Ξ) (hσ : |σ| ≤ 1 / 2)
    (hs : |s| * Real.exp κ ≤ 1 / 4) (i a p : ℕ) (Zc : ℝ) (hZ : ∀ x, |iteratedDeriv i Ξ x| ≤ Zc) (u : ℝ) :
    |PP κ Ξ σ s i a p u| ≤ 2 ^ p * (Zc * Real.exp (1 / 2)) := by
  have hZ0 : 0 ≤ Zc := (abs_nonneg _).trans (hZ 0)
  by_cases hu : u ∈ Set.Icc (-κ) κ
  · have hu' : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have hexp : Real.exp (σ * u) ≤ Real.exp (1 / 2) := by
      apply Real.exp_le_exp.mpr
      have := abs_mul σ u
      have h5 : |σ| * |u| ≤ 1 / 2 * 1 := mul_le_mul hσ hu' (abs_nonneg _) (by norm_num)
      linarith [le_abs_self (σ * u)]
    have hX : |XX κ Ξ σ i u| ≤ Zc * Real.exp (1 / 2) := by
      simp only [XX]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hZ _) hexp (Real.exp_pos _).le hZ0
    have hse : |s * Real.exp u| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos u)]
      have := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) (abs_nonneg s)
      linarith
    have hr : |rr s u| ≤ 2 := by
      simp only [rr]; rw [abs_inv]
      have h1 : 1 / 2 ≤ |1 - s * Real.exp u| := by
        have := abs_sub_abs_le_abs_sub 1 (s * Real.exp u); rw [abs_one] at this; linarith
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hQ : |QQ s a p u| ≤ 2 ^ p := by
      simp only [QQ]
      rw [Real.exp_nat_mul, ← mul_pow, abs_mul, abs_pow, abs_pow]
      have h1 : |s * Real.exp u| ^ a ≤ 1 := pow_le_one₀ (abs_nonneg _) (by linarith)
      have h2 : |rr s u| ^ p ≤ 2 ^ p := pow_le_pow_left₀ (abs_nonneg _) hr p
      calc |s * Real.exp u| ^ a * |rr s u| ^ p ≤ 1 * 2 ^ p :=
            mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = 2 ^ p := one_mul _
    simp only [PP]; rw [abs_mul]
    calc |XX κ Ξ σ i u| * |QQ s a p u| ≤ (Zc * Real.exp (1 / 2)) * 2 ^ p :=
          mul_le_mul hX hQ (abs_nonneg _) (by positivity)
      _ = 2 ^ p * (Zc * Real.exp (1 / 2)) := by ring
  · simp only [PP, XX_zero κ Ξ σ hκ hΞ i u hu, zero_mul, abs_zero]; positivity

theorem Mit_bound (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hΞ : NearCutoff Ξ) (hσ : |σ| ≤ 1 / 2)
    (hs : |s| * Real.exp κ ≤ 1 / 4) (m : ℕ) (Zc : ℝ) (hZ : ∀ i ≤ m, ∀ x, |iteratedDeriv i Ξ x| ≤ Zc) :
    ∀ n : ℕ, ∀ i a p : ℕ, i + n ≤ m → ∀ u,
      |Mit s n (PP κ Ξ σ s i a p) u|
        ≤ κ⁻¹ ^ n * ((a : ℝ) + p + 3 * n + 3) ^ n * 2 ^ (p + 2 * n) * (Zc * Real.exp (1 / 2)) := by
  have hZ0 : 0 ≤ Zc := (abs_nonneg _).trans (hZ 0 (Nat.zero_le _) 0)
  have hk1 : 1 ≤ κ⁻¹ := one_le_inv_iff₀.mpr ⟨hκ, hκ1⟩
  intro n
  induction n with
  | zero =>
    intro i a p hi u
    simp only [pow_zero, one_mul, mul_zero, add_zero]
    exact PP_bound κ Ξ σ s hκ hκ1 hΞ hσ hs i a p Zc (hZ i (by omega)) u
  | succ n ih =>
    intro i a p hi u
    have g1 := PP_good κ Ξ σ s hκ hΞ hs (i + 1) a (p + 1)
    have g2 := PP_good κ Ξ σ s hκ hΞ hs i a (p + 1)
    have g3 := PP_good κ Ξ σ s hκ hΞ hs i (a + 1) (p + 2)
    have e : Mit s (n + 1) (PP κ Ξ σ s i a p)
        = fun u => κ⁻¹ * Mit s n (PP κ Ξ σ s (i + 1) a (p + 1)) u
          + (σ + a) * Mit s n (PP κ Ξ σ s i a (p + 1)) u + (p + 1) * Mit s n (PP κ Ξ σ s i (a + 1) (p + 2)) u := by
      show Mit s n (MM s (PP κ Ξ σ s i a p)) = _
      rw [MM_PP κ Ξ σ s hκ hΞ hs i a p]
      rw [Mit_add κ s hκ hs n _ _ (good_add κ _ _ (good_smul κ _ _ g1) (good_smul κ _ _ g2)) (good_smul κ _ _ g3),
        Mit_add κ s hκ hs n _ _ (good_smul κ _ _ g1) (good_smul κ _ _ g2),
        Mit_smul κ s hκ hs n _ _ g1, Mit_smul κ s hκ hs n _ _ g2, Mit_smul κ s hκ hs n _ _ g3]
    rw [e]
    set Z := Zc * Real.exp (1 / 2) with hZdef
    have hZp : 0 ≤ Z := by positivity
    set N : ℝ := (a : ℝ) + p + 3 * n + 6 with hN
    have hN0 : 0 ≤ N := by positivity
    set Wb := κ⁻¹ ^ n * N ^ n * 2 ^ (p + 2 * n) * Z with hW
    have hW0 : 0 ≤ Wb := by positivity
    have t1 := ih (i + 1) a (p + 1) (by omega) u
    have t2 := ih i a (p + 1) (by omega) u
    have t3 := ih i (a + 1) (p + 2) (by omega) u
    have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ N → κ⁻¹ ^ n * x ^ n ≤ κ⁻¹ ^ n * N ^ n := fun x h0 h1 =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 n) (by positivity)
    have b1 : |Mit s n (PP κ Ξ σ s (i + 1) a (p + 1)) u| ≤ 2 * Wb := by
      refine t1.trans ?_
      have := hpow ((a : ℝ) + ((p + 1 : ℕ) : ℝ) + 3 * n + 3) (by positivity) (by push_cast; linarith)
      rw [hW, show p + 1 + 2 * n = (p + 2 * n) + 1 by ring, pow_succ]
      have h2 : (0 : ℝ) ≤ 2 ^ (p + 2 * n) * Z := by positivity
      nlinarith
    have b2 : |Mit s n (PP κ Ξ σ s i a (p + 1)) u| ≤ 2 * Wb := by
      refine t2.trans ?_
      have := hpow ((a : ℝ) + ((p + 1 : ℕ) : ℝ) + 3 * n + 3) (by positivity) (by push_cast; linarith)
      rw [hW, show p + 1 + 2 * n = (p + 2 * n) + 1 by ring, pow_succ]
      have h2 : (0 : ℝ) ≤ 2 ^ (p + 2 * n) * Z := by positivity
      nlinarith
    have b3 : |Mit s n (PP κ Ξ σ s i (a + 1) (p + 2)) u| ≤ 4 * Wb := by
      refine t3.trans (le_of_eq ?_)
      rw [hW, hN, show p + 2 + 2 * n = (p + 2 * n) + 2 by ring, pow_add]
      push_cast; ring
    have hsa : |σ + a| ≤ a + 1 / 2 := by
      have h1 := abs_add_le σ (a : ℝ)
      have h2 : |(a : ℝ)| = a := abs_of_nonneg (Nat.cast_nonneg a)
      linarith
    have htri : |κ⁻¹ * Mit s n (PP κ Ξ σ s (i + 1) a (p + 1)) u
          + (σ + a) * Mit s n (PP κ Ξ σ s i a (p + 1)) u + (p + 1) * Mit s n (PP κ Ξ σ s i (a + 1) (p + 2)) u|
        ≤ κ⁻¹ * (2 * Wb) + (a + 1 / 2) * (2 * Wb) + (p + 1) * (4 * Wb) := by
      set X1 := Mit s n (PP κ Ξ σ s (i + 1) a (p + 1)) u with hX1
      set X2 := Mit s n (PP κ Ξ σ s i a (p + 1)) u with hX2
      set X3 := Mit s n (PP κ Ξ σ s i (a + 1) (p + 2)) u with hX3
      have n1 := abs_add_le (κ⁻¹ * X1 + (σ + a) * X2) ((p + 1) * X3)
      have n2 := abs_add_le (κ⁻¹ * X1) ((σ + a) * X2)
      have e1 : |κ⁻¹ * X1| = κ⁻¹ * |X1| := by rw [abs_mul, abs_of_pos (inv_pos.mpr hκ)]
      have e2 : |(σ + a) * X2| = |σ + a| * |X2| := abs_mul _ _
      have e3 : |((p : ℝ) + 1) * X3| = ((p : ℝ) + 1) * |X3| := by rw [abs_mul, abs_of_nonneg (by positivity)]
      have m1 := mul_le_mul_of_nonneg_left b1 (inv_pos.mpr hκ).le
      have m2 := mul_le_mul hsa b2 (abs_nonneg _) (by positivity)
      have m3 := mul_le_mul_of_nonneg_left b3 (by positivity : (0 : ℝ) ≤ p + 1)
      linarith
    refine htri.trans ?_
    have target : κ⁻¹ ^ (n + 1) * ((a : ℝ) + p + 3 * ((n + 1 : ℕ) : ℝ) + 3) ^ (n + 1) * 2 ^ (p + 2 * (n + 1)) * Z
        = 4 * κ⁻¹ * N * Wb := by
      rw [hW, hN]; push_cast; ring
    rw [target]
    have hc : κ⁻¹ * 2 + (a + 1 / 2) * 2 + (p + 1) * 4 ≤ 4 * κ⁻¹ * N := by
      rw [hN]
      have h1 : (a : ℝ) ≤ κ⁻¹ * a := le_mul_of_one_le_left (Nat.cast_nonneg a) hk1
      have h2 : (p : ℝ) ≤ κ⁻¹ * p := le_mul_of_one_le_left (Nat.cast_nonneg p) hk1
      have h3 : (0 : ℝ) ≤ κ⁻¹ * (3 * n) := by positivity
      nlinarith
    nlinarith

end fixed2

/-- one integration by parts for the phase `λ(u − s e^u)`. -/
theorem ibp_step (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs : |s| * Real.exp κ ≤ 1 / 4) (lam : ℝ) (hlam : lam ≠ 0)
    (f : ℝ → ℝ) (hf : Good κ f) :
    ∫ u : ℝ, (f u : ℂ) * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ))
      = (I / lam) * ∫ u : ℝ, ((MM s f u : ℝ) : ℂ) * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ)) := by
  set E : ℝ → ℂ := fun u => Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ)) with hE
  set E' : ℝ → ℂ := fun u => I * (((lam - s * lam * Real.exp u : ℝ)) : ℂ) * E u with hE'
  have hEd : ∀ u, HasDerivAt E (E' u) u := fun u => by
    have h1 : HasDerivAt (fun u : ℝ => lam * u - s * lam * Real.exp u) (lam - s * lam * Real.exp u) u :=
      (((hasDerivAt_id' u).const_mul lam).sub ((Real.hasDerivAt_exp u).const_mul (s * lam))).congr_deriv (by ring)
    have h2 := (h1.ofReal_comp.const_mul I).cexp
    refine h2.congr_deriv ?_
    simp only [hE']; ring
  have hEc : Continuous E := by simp only [hE]; fun_prop
  have hE'c : Continuous E' := by simp only [hE', hE]; fun_prop
  set g : ℝ → ℝ := fun u => f u * rr s u with hg
  have hgG := fr_smooth κ s hκ hs f hf
  have hgd := diff_of_good κ g hgG
  have hgc : HasCompactSupport g := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hgG.2
  have hgC : HasCompactSupport (fun u => (g u : ℂ)) := hgc.comp_left Complex.ofReal_zero
  have hdg : Continuous (deriv g) := (contDiff_infty_iff_deriv.mp hgG.1).2.continuous
  have hdgC : HasCompactSupport (fun u => ((deriv g u : ℝ) : ℂ)) :=
    (hgc.deriv).comp_left Complex.ofReal_zero
  have i1 : Integrable ((fun u => (g u : ℂ)) * E') :=
    ((Complex.continuous_ofReal.comp hgG.1.continuous).mul hE'c).integrable_of_hasCompactSupport hgC.mul_right
  have i2 : Integrable ((fun u => ((deriv g u : ℝ) : ℂ)) * E) :=
    ((Complex.continuous_ofReal.comp hdg).mul hEc).integrable_of_hasCompactSupport hdgC.mul_right
  have i3 : Integrable ((fun u => (g u : ℂ)) * E) :=
    ((Complex.continuous_ofReal.comp hgG.1.continuous).mul hEc).integrable_of_hasCompactSupport hgC.mul_right
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun u => (g u : ℂ))
    (u' := fun u => ((deriv g u : ℝ) : ℂ)) (v := E) (v' := E')
    (fun x _ => (hgd x).hasDerivAt.ofReal_comp) (fun x _ => hEd x) i1 i2 i3
  have hpt : ∀ u, (g u : ℂ) * E' u = (I * lam) * ((f u : ℂ) * E u) := by
    intro u
    by_cases hu : u ∈ OO s
    · have h1 : rr s u * (1 - s * Real.exp u) = 1 := inv_mul_cancel₀ (rr_ne s u hu)
      have h2 : g u * (lam - s * lam * Real.exp u) = f u * lam := by
        simp only [hg]
        calc f u * rr s u * (lam - s * lam * Real.exp u) = f u * lam * (rr s u * (1 - s * Real.exp u)) := by ring
          _ = f u * lam := by rw [h1, mul_one]
      simp only [hE']
      calc (g u : ℂ) * (I * (((lam - s * lam * Real.exp u : ℝ)) : ℂ) * E u)
          = I * (((g u * (lam - s * lam * Real.exp u) : ℝ)) : ℂ) * E u := by push_cast; ring
        _ = I * (((f u * lam : ℝ)) : ℂ) * E u := by rw [h2]
        _ = (I * lam) * ((f u : ℂ) * E u) := by push_cast; ring
    · have hnt : u ∉ tsupport f := fun h => hu (Icc_sub_OO κ s hκ hs (hf.2 h))
      have hf0 : f u = 0 := image_eq_zero_of_notMem_tsupport hnt
      simp only [hg, hf0, zero_mul, Complex.ofReal_zero, mul_zero]
  have hL : (∫ u, (g u : ℂ) * E' u) = (I * lam) * ∫ u, (f u : ℂ) * E u := by
    rw [← integral_const_mul]; congr 1; funext u; exact hpt u
  have key' : (I * lam) * (∫ u, (f u : ℂ) * E u) = -∫ u, ((MM s f u : ℝ) : ℂ) * E u := by
    rw [← hL]; exact key
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hY : (∫ u, ((MM s f u : ℝ) : ℂ) * E u) = -((I * lam) * ∫ u, (f u : ℂ) * E u) := by
    rw [key']; ring
  rw [hY]
  calc (∫ u, (f u : ℂ) * E u) = (-(I * I)) * ((lam : ℂ) / lam) * ∫ u, (f u : ℂ) * E u := by
        rw [Complex.I_mul_I, div_self hlamC]; ring
    _ = I / lam * -(I * lam * ∫ u, (f u : ℂ) * E u) := by ring

theorem ibp_iter (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs : |s| * Real.exp κ ≤ 1 / 4) (lam : ℝ) (hlam : lam ≠ 0) :
    ∀ (n : ℕ) (f : ℝ → ℝ), Good κ f →
    ∫ u : ℝ, (f u : ℂ) * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ))
      = (I / lam) ^ n * ∫ u : ℝ, ((Mit s n f u : ℝ) : ℂ) * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ))
  | 0, f, _ => by simp [Mit]
  | n + 1, f, hf => by
    rw [ibp_step κ hκ s hs lam hlam f hf, ibp_iter κ hκ s hs lam hlam n (MM s f) (MM_good κ s hκ hs f hf), pow_succ]
    show _ = _ * ∫ u : ℝ, ((Mit s n (MM s f) u : ℝ) : ℂ) * _
    ring

theorem nsp_core (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 → ∀ lam c : ℝ, lam ≠ 0 → 4 * |c| * Real.exp κ ≤ |lam| →
      ‖∫ u : ℝ, ((Ξ (u / κ) * Real.exp ((β - 1 / 2) * u) : ℝ) : ℂ)
          * Complex.exp (I * ((lam : ℂ) * u - (c : ℂ) * (Real.exp u : ℂ)))‖ ≤ C / |lam| ^ m := by
  have hΞc : HasCompactSupport Ξ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ξ) (hΞ.supp.trans Set.Ioo_subset_Icc_self)
  have hbdd : ∀ j : ℕ, BddAbove (Set.range fun x => |iteratedDeriv j Ξ x|) := fun j => by
    have hjc : HasCompactSupport (iteratedDeriv j Ξ) :=
      IsCompact.of_isClosed_subset hΞc (isClosed_tsupport _) (tsupport_iD Ξ j)
    obtain ⟨B, hB⟩ := (iD_smooth Ξ hΞ.smooth j).continuous.bounded_above_of_compact_support hjc
    exact ⟨B, by rintro _ ⟨x, rfl⟩; have := hB x; rwa [Real.norm_eq_abs] at this⟩
  set Zc := ∑ j ∈ Finset.range (m + 1), ⨆ x, |iteratedDeriv j Ξ x| with hZc
  have hZ : ∀ i ≤ m, ∀ x, |iteratedDeriv i Ξ x| ≤ Zc := fun i hi x =>
    (le_ciSup (hbdd i) x).trans (Finset.single_le_sum (f := fun j => ⨆ x, |iteratedDeriv j Ξ x|)
      (fun j _ => Real.iSup_nonneg fun x => abs_nonneg _) (Finset.mem_range.mpr (by omega)))
  have hZ0 : 0 ≤ Zc := (abs_nonneg _).trans (hZ 0 (Nat.zero_le _) 0)
  set Bd := κ⁻¹ ^ m * ((3 : ℝ) * m + 3) ^ m * 2 ^ (2 * m) * (Zc * Real.exp (1 / 2)) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  refine ⟨2 * κ * Bd, by positivity, fun β hβ0 hβ1 lam c hlam hc => ?_⟩
  set σ := β - 1 / 2 with hσdef
  have hσ : |σ| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  set s := c / lam with hsdef
  have hlp : 0 < |lam| := abs_pos.mpr hlam
  have hs : |s| * Real.exp κ ≤ 1 / 4 := by
    rw [hsdef, abs_div, div_mul_eq_mul_div, div_le_iff₀ hlp]; linarith
  have hcs : c = s * lam := by rw [hsdef]; field_simp
  -- rewrite the integrand
  have hint : (∫ u : ℝ, ((Ξ (u / κ) * Real.exp ((β - 1 / 2) * u) : ℝ) : ℂ)
      * Complex.exp (I * ((lam : ℂ) * u - (c : ℂ) * (Real.exp u : ℂ))))
      = ∫ u : ℝ, ((PP κ Ξ σ s 0 0 0 u : ℝ) : ℂ)
          * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ)) := by
    congr 1; funext u
    simp only [PP, XX, QQ, iteratedDeriv_zero, pow_zero, Nat.cast_zero, zero_mul, Real.exp_zero, mul_one, hσdef]
    rw [hcs]; push_cast; ring_nf
  rw [hint, ibp_iter κ hκ s hs lam hlam m _ (PP_good κ Ξ σ s hκ hΞ hs 0 0 0)]
  have hMg := Mit_good κ s hκ hs m _ (PP_good κ Ξ σ s hκ hΞ hs 0 0 0)
  have hMb := Mit_bound κ Ξ σ s hκ hκ1 hΞ hσ hs m Zc hZ m 0 0 0 (by omega)
  have hMb' : ∀ u, |Mit s m (PP κ Ξ σ s 0 0 0) u| ≤ Bd := fun u => by
    refine (hMb u).trans (le_of_eq ?_); rw [hBd]; push_cast; ring
  have hIi : Integrable ((Set.Icc (-κ) κ).indicator (fun _ => Bd)) :=
    (integrableOn_const (s := Set.Icc (-κ) κ) (C := Bd) (hs := measure_Icc_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  have hnorm : ‖∫ u : ℝ, ((Mit s m (PP κ Ξ σ s 0 0 0) u : ℝ) : ℂ)
      * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ))‖ ≤ 2 * κ * Bd := by
    refine (norm_integral_le_integral_norm _).trans ?_
    calc (∫ u : ℝ, ‖((Mit s m (PP κ Ξ σ s 0 0 0) u : ℝ) : ℂ)
            * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ))‖)
        ≤ ∫ u : ℝ, (Set.Icc (-κ) κ).indicator (fun _ => Bd) u := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => by
            simp only [Pi.zero_apply]; exact norm_nonneg _) hIi (Filter.Eventually.of_forall fun u => ?_)
          show ‖((Mit s m (PP κ Ξ σ s 0 0 0) u : ℝ) : ℂ)
            * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ))‖ ≤ _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            show I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ) = (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ) * I
              by ring, Complex.norm_exp_ofReal_mul_I, mul_one]
          by_cases hm : u ∈ Set.Icc (-κ) κ
          · rw [Set.indicator_of_mem hm]; exact hMb' u
          · rw [Set.indicator_of_notMem hm, image_eq_zero_of_notMem_tsupport (fun h => hm (hMg.2 h)), abs_zero]
      _ = 2 * κ * Bd := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
          ring
  rw [norm_mul, norm_pow, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  calc (1 / |lam|) ^ m * ‖∫ u : ℝ, ((Mit s m (PP κ Ξ σ s 0 0 0) u : ℝ) : ℂ)
          * Complex.exp (I * (((lam * u - s * lam * Real.exp u : ℝ)) : ℂ))‖
      ≤ (1 / |lam|) ^ m * (2 * κ * Bd) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 2 * κ * Bd / |lam| ^ m := by rw [div_pow, one_pow]; ring

end ZetaShell.NSP
