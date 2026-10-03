/-
L10c_KT (L7_10c, 3 Oct 2026): the transfer from unit windows to `g` at one design point (`KT_point`), and the eventual
scalar facts it needs. `KT_transfer` (library node, `Skeleton/L10_KT.lean`) is derived from these in the drop-in.

Route: `g ≤ L` (`gQ_le_env`) and `R ≤ Σ_k W₀(s − (a+k))R(s)` on the zone `(a, b]` (`dom_pointwise`), so
`∫_{zone} gR ≤ L Σ_k ∫W₀(s−(a+k))R(s) ≤ L(M+1)ηN_W T(b+1)`; and `g ≥ (L − 2 − b)/1296 ≥ ℒ/11664` on the zone
(`Valid.gQ_ge_bulk`, `w = 1`), so `∫_{zone} g T s ≥ (ℒ/11664) T a (b − a)`. No derivative of `g` is used.
-/
import ZetaShell.ShellK.L10c_Scales

noncomputable section
open MeasureTheory Filter

namespace ZetaShell
namespace ShellK
namespace K2c

open ZetaQ ZetaShell.PropZ

theorem bumpW_shift_hasCompactSupport (c : ℝ) : HasCompactSupport (fun s => bumpW (s - c)) := by
  refine HasCompactSupport.intro (K := Set.Icc (c - 3 / 4) (c + 3 / 4)) isCompact_Icc fun x hx => ?_
  by_contra h
  have h1 := bumpW_support h
  apply hx
  constructor <;> linarith [h1.1, h1.2]

theorem bumpW_shift_mul_integrable (c : ℝ) {R : ℝ → ℝ} (hR : Continuous R) :
    Integrable (fun s => bumpW (s - c) * R s) := by
  have hc : Continuous (fun s => bumpW (s - c) * R s) :=
    (bumpW_continuous.comp (continuous_id.sub continuous_const)).mul hR
  exact hc.integrable_of_hasCompactSupport (bumpW_shift_hasCompactSupport c).mul_right

/-- **The transfer at one design point.** `a = log Q + 4`, `b = α′ℒ`; the window hypothesis is asked for the
centres `s₀ ∈ [a, b + 1]` only. -/
theorem KT_point (P : ParamsQ) (hP : P.Valid) (hw8 : 8 * P.w ≤ P.LB) (hw1 : P.w = 1) (αp : ℝ) (A : ℕ)
    (hT : 0 < P.T) (hab : Real.log P.Q + 4 + 1 ≤ αp * P.LL)
    (hbL : αp * P.LL ≤ P.LB - 2 - P.LL / 9) (hb1 : αp * P.LL + 1 ≤ 2 * P.LL) (hLB : P.LB ≤ 2 * P.LL)
    (ha : P.LL ≤ 2 * (Real.log P.Q + 4)) (R : ℝ → ℝ) (η : ℝ) (hη : 0 ≤ η) (hR0 : ∀ s, 0 ≤ R s)
    (hRc : Continuous R)
    (hwin : ∀ s₀ : ℝ, Real.log P.Q + 4 ≤ s₀ → s₀ ≤ αp * P.LL + 1 →
      (∫ s, bumpW (s - s₀) * R s) ≤ η * normCA bumpW A * (P.T * s₀)) :
    (∫ s in shellZone P αp, P.gQ s * R s)
      ≤ 279936 * normCA bumpW A * η * ∫ s in shellZone P αp, P.gQ s * (P.T * s) := by
  set a := Real.log P.Q + 4 with ha_def
  set b := αp * P.LL with hb_def
  set NW := normCA bumpW A with hNW_def
  have hNW : 0 ≤ NW := ShellS.normCA_nonneg' bumpW A
  set M := ⌈b - a⌉₊ with hM
  have hLL : 0 < P.LL := hP.LL_pos
  have hZ : shellZone P αp = Set.Ioc a b := rfl
  have hgc : Continuous P.gQ := hP.gQ_continuous hw8
  have hg0 : ∀ s, 0 ≤ P.gQ s := hP.gQ_nonneg hw8
  have hgL : ∀ s, P.gQ s ≤ P.LB := fun s => by
    have h := gQ_le_env P hP hw8 s
    have : max (P.LB - |s|) 0 ≤ P.LB := max_le (by linarith [abs_nonneg s]) (by linarith)
    linarith
  -- the dominating function
  set H : ℝ → ℝ := fun s => ∑ k ∈ Finset.range (M + 1), bumpW (s - (a + k)) * R s with hH
  have hHi : Integrable H := integrable_finsetSum _ fun k _ => bumpW_shift_mul_integrable _ hRc
  have hH0 : ∀ s, 0 ≤ H s := fun s => Finset.sum_nonneg fun k _ => mul_nonneg (bumpW_nonneg _) (hR0 s)
  have hdom : ∀ s ∈ Set.Ioc a b, R s ≤ H s := fun s hs =>
    dom_pointwise a b R (fun _ => R) (fun _ => hR0) (fun _ _ _ => le_rfl) s hs
  -- step 1: `∫_Z g R ≤ ∫_Z g H ≤ L ∫ H`
  have hgR : IntegrableOn (fun s => P.gQ s * R s) (Set.Ioc a b) :=
    ((hgc.mul hRc).integrableOn_Icc (a := a) (b := b)).mono_set Set.Ioc_subset_Icc_self
  have hgH : Integrable (fun s => P.gQ s * H s) := by
    refine Integrable.bdd_mul (c := P.LB) hHi hgc.aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hgL s
  have h1 : (∫ s in Set.Ioc a b, P.gQ s * R s) ≤ ∫ s in Set.Ioc a b, P.gQ s * H s :=
    setIntegral_mono_on hgR hgH.integrableOn measurableSet_Ioc fun s hs =>
      mul_le_mul_of_nonneg_left (hdom s hs) (hg0 s)
  have h2 := setIntegral_mul_le (Set.Ioc a b) measurableSet_Ioc P.LB P.gQ H hg0 hgL hgc hH0 hHi
  -- step 2: the windows
  have hba : 1 ≤ b - a := by linarith
  have hMle : (M : ℝ) ≤ b - a + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have h3 : (∫ s, H s) ≤ ((M : ℝ) + 1) * (η * NW * (P.T * (b + 1))) := by
    rw [hH, integral_finsetSum _ fun k _ => bumpW_shift_mul_integrable _ hRc]
    have hk : ∀ k ∈ Finset.range (M + 1), (∫ s, bumpW (s - (a + k)) * R s) ≤ η * NW * (P.T * (b + 1)) := by
      intro k hk
      have hk' : (k : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      refine le_trans (hwin (a + k) (by linarith) (by linarith)) ?_
      have : P.T * (a + k) ≤ P.T * (b + 1) := mul_le_mul_of_nonneg_left (by linarith) hT.le
      exact mul_le_mul_of_nonneg_left this (mul_nonneg hη hNW)
    refine le_trans (Finset.sum_le_sum hk) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; exact le_rfl
  -- step 3: the lower bound of the right side
  set c₀ := (P.LL / 11664) * (P.T * a) with hc₀
  have hpt : ∀ s ∈ Set.Ioc a b, c₀ ≤ P.gQ s * (P.T * s) := by
    intro s hs
    have hs0 : 0 < s := by
      have : 0 ≤ Real.log P.Q := Real.log_nonneg (by linarith [hP.Q_ge])
      linarith [hs.1]
    have hgl := hP.gQ_ge_bulk hw8 s
    rw [hw1, abs_of_pos hs0] at hgl
    have hg1 : P.LL / 9 / 1296 ≤ P.gQ s := by
      have : P.LL / 9 ≤ max (P.LB - 2 * 1 - s) 0 := le_trans (by linarith [hs.2]) (le_max_left _ _)
      linarith
    have hTs : P.T * a ≤ P.T * s := mul_le_mul_of_nonneg_left hs.1.le hT.le
    have hc0 : 0 ≤ P.T * a := mul_nonneg hT.le (by linarith)
    calc c₀ = (P.LL / 9 / 1296) * (P.T * a) := by rw [hc₀]; ring
      _ ≤ P.gQ s * (P.T * s) := mul_le_mul hg1 hTs hc0 (hg0 s)
  have hgTs : IntegrableOn (fun s => P.gQ s * (P.T * s)) (Set.Ioc a b) :=
    ((hgc.mul (continuous_const.mul continuous_id)).integrableOn_Icc (a := a) (b := b)).mono_set
      Set.Ioc_subset_Icc_self
  have h4 : c₀ * (b - a) ≤ ∫ s in Set.Ioc a b, P.gQ s * (P.T * s) := by
    have hc := setIntegral_mono_on (integrableOn_const (by simp)) hgTs measurableSet_Ioc hpt
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith)] at hc
    linarith
  -- assembly
  rw [hZ]
  have hM1 : (M : ℝ) + 1 ≤ 3 * (b - a) := by linarith
  have hX : 0 ≤ η * NW * P.T := mul_nonneg (mul_nonneg hη hNW) hT.le
  have hb1' : 0 ≤ b + 1 := by linarith
  have hfin : P.LB * (((M : ℝ) + 1) * (η * NW * (P.T * (b + 1))))
      ≤ 279936 * NW * η * (c₀ * (b - a)) := by
    have hLB0 : 0 ≤ P.LB := by linarith
    calc P.LB * (((M : ℝ) + 1) * (η * NW * (P.T * (b + 1))))
        = P.LB * (((M : ℝ) + 1) * ((η * NW * P.T) * (b + 1))) := by ring
      _ ≤ (2 * P.LL) * ((3 * (b - a)) * ((η * NW * P.T) * (2 * P.LL))) := by
          gcongr
      _ = 12 * (η * NW * P.T) * P.LL * (b - a) * P.LL := by ring
      _ ≤ 12 * (η * NW * P.T) * P.LL * (b - a) * (2 * a) := by gcongr
      _ = 279936 * NW * η * (c₀ * (b - a)) := by rw [hc₀]; ring
  have hcoef : 0 ≤ 279936 * NW * η := by positivity
  calc (∫ s in Set.Ioc a b, P.gQ s * R s) ≤ P.LB * ∫ s, H s := le_trans h1 h2
    _ ≤ P.LB * (((M : ℝ) + 1) * (η * NW * (P.T * (b + 1)))) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
    _ ≤ 279936 * NW * η * (c₀ * (b - a)) := hfin
    _ ≤ 279936 * NW * η * ∫ s in Set.Ioc a b, P.gQ s * (P.T * s) := mul_le_mul_of_nonneg_left h4 hcoef

/-- the scalar facts of the transfer, eventually in `Qn`. -/
theorem scalars_KT (αp αpp r ε : ℝ) (hα1 : 1 < αp) (hαα : αp < αpp) (hre : 0 < r + ε) :
    ∀ᶠ Qn : ℕ in atTop, 16 ≤ Real.log Qn ∧ 5 ≤ (αp - 1) * Real.log Qn ∧
      αp * (r + ε) * Real.log (Real.log Qn) + 1 ≤ (αpp - αp) * Real.log Qn := by
  have hd : 0 < αpp - αp := by linarith
  have hK : 0 < 2 * αp * (r + ε) / (αpp - αp) := by
    have : 0 < αp := by linarith
    positivity
  have h : ∀ᶠ y : ℝ in atTop, 16 ≤ y ∧ 5 ≤ (αp - 1) * y ∧ αp * (r + ε) * Real.log y + 1 ≤ (αpp - αp) * y := by
    filter_upwards [FrobAssembly.loglog_le_eventually _ hK, eventually_ge_atTop 16,
      eventually_ge_atTop (5 / (αp - 1)), eventually_ge_atTop (2 / (αpp - αp))] with y h1 h2 h3 h4
    have hα0 : 0 < αp - 1 := by linarith
    refine ⟨h2, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left h3 hα0.le
      rwa [mul_div_cancel₀ _ hα0.ne'] at this
    · have e1 : αp * (r + ε) * Real.log y = (αpp - αp) / 2 * (2 * αp * (r + ε) / (αpp - αp) * Real.log y) := by
        field_simp
      have e2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (αpp - αp) / 2)
      have e3 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (αpp - αp) / 2)
      rw [show (αpp - αp) / 2 * (2 / (αpp - αp)) = 1 by field_simp] at e3
      nlinarith
  exact tendsto_log_nat_atTop.eventually h

end K2c
end ShellK
end ZetaShell
