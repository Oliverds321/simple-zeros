/-
L7_5 (28 Sep 2026), round 6: `ZR_phi_pw2K'`, the second-derivative bound for
  `φ(u) = e^{−u/2} · D_T(s − u) · Ξ((u − s)/κ) · f(Δ(e^u − x))`   on `|u − s| ≤ κ`:
  `|φ″(u)| ≤ 52 M² κ^{−2} (T + ΔN + 1)² T e^{−u/2}`,   `M = 1 + Σ sup|Ξ^{(i)}| + Σ sup|f^{(i)}|` (`i ≤ 2`).
Product rule (`Bnd_mul`, three times) and chain rule (`castBnd` for the real factors), with
`|D_T| ≤ T`, `|D_T′| ≤ 2T²`, `|D_T″| ≤ 4T³` (DT_Facts, DT_Facts2) and `Δe^u ≤ 3X` for `|u − s| ≤ 1`.
-/
import ZetaShell.PropZ.ZR_PhiPw0
import ZetaShell.PropZ.DT_Facts2

open MeasureTheory

namespace ZetaShell.PropZ

/-- second-order bounds of a product, with differentiability carried along. -/
theorem Bnd_mul (g h : ℝ → ℂ) (hg1 : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (hh1 : Differentiable ℝ h) (hh2 : Differentiable ℝ (deriv h)) (u a0 a1 a2 b0 b1 b2 : ℝ)
    (ha0 : ‖g u‖ ≤ a0) (ha1 : ‖deriv g u‖ ≤ a1) (ha2 : ‖deriv (deriv g) u‖ ≤ a2)
    (hb0 : ‖h u‖ ≤ b0) (hb1 : ‖deriv h u‖ ≤ b1) (hb2 : ‖deriv (deriv h) u‖ ≤ b2) :
    Differentiable ℝ (fun v => g v * h v) ∧ Differentiable ℝ (deriv (fun v => g v * h v)) ∧
    ‖g u * h u‖ ≤ a0 * b0 ∧ ‖deriv (fun v => g v * h v) u‖ ≤ a1 * b0 + a0 * b1 ∧
    ‖deriv (deriv (fun v => g v * h v)) u‖ ≤ a2 * b0 + 2 * (a1 * b1) + a0 * b2 := by
  have e1 : deriv (fun v => g v * h v) = fun v => deriv g v * h v + g v * deriv h v :=
    funext fun v => ((hg1 v).hasDerivAt.mul (hh1 v).hasDerivAt).deriv
  have e2 : deriv (deriv (fun v => g v * h v)) u
      = deriv (deriv g) u * h u + deriv g u * deriv h u
        + (deriv g u * deriv h u + g u * deriv (deriv h) u) := by
    rw [e1]
    exact (((hg2 u).hasDerivAt.mul (hh1 u).hasDerivAt).add ((hg1 u).hasDerivAt.mul (hh2 u).hasDerivAt)).deriv
  have a0n : 0 ≤ a0 := (norm_nonneg _).trans ha0
  have a1n : 0 ≤ a1 := (norm_nonneg _).trans ha1
  have a2n : 0 ≤ a2 := (norm_nonneg _).trans ha2
  refine ⟨hg1.mul hh1, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact (hg2.mul hh1).add (hg1.mul hh2)
  · rw [norm_mul]; exact mul_le_mul ha0 hb0 (norm_nonneg _) a0n
  · rw [e1]
    calc ‖deriv g u * h u + g u * deriv h u‖ ≤ ‖deriv g u * h u‖ + ‖g u * deriv h u‖ := norm_add_le _ _
      _ = ‖deriv g u‖ * ‖h u‖ + ‖g u‖ * ‖deriv h u‖ := by rw [norm_mul, norm_mul]
      _ ≤ a1 * b0 + a0 * b1 :=
          add_le_add (mul_le_mul ha1 hb0 (norm_nonneg _) a1n) (mul_le_mul ha0 hb1 (norm_nonneg _) a0n)
  · rw [e2]
    have t1 := mul_le_mul ha2 hb0 (norm_nonneg _) a2n
    have t2 := mul_le_mul ha1 hb1 (norm_nonneg _) a1n
    have t3 := mul_le_mul ha0 hb2 (norm_nonneg _) a0n
    calc ‖deriv (deriv g) u * h u + deriv g u * deriv h u + (deriv g u * deriv h u + g u * deriv (deriv h) u)‖
        ≤ ‖deriv (deriv g) u * h u‖ + ‖deriv g u * deriv h u‖
          + (‖deriv g u * deriv h u‖ + ‖g u * deriv (deriv h) u‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ = ‖deriv (deriv g) u‖ * ‖h u‖ + ‖deriv g u‖ * ‖deriv h u‖
          + (‖deriv g u‖ * ‖deriv h u‖ + ‖g u‖ * ‖deriv (deriv h) u‖) := by simp only [norm_mul]
      _ ≤ a2 * b0 + 2 * (a1 * b1) + a0 * b2 := by linarith

/-- a real factor, cast to `ℂ`: derivatives are the casts of the real derivatives. -/
theorem castBnd (p p1 p2 : ℝ → ℝ) (h1 : ∀ v, HasDerivAt p (p1 v) v) (h2 : ∀ v, HasDerivAt p1 (p2 v) v) :
    Differentiable ℝ (fun v => ((p v : ℝ) : ℂ)) ∧ Differentiable ℝ (deriv (fun v => ((p v : ℝ) : ℂ))) ∧
    ∀ u, ‖((p u : ℝ) : ℂ)‖ = |p u| ∧ ‖deriv (fun v => ((p v : ℝ) : ℂ)) u‖ = |p1 u| ∧
      ‖deriv (deriv (fun v => ((p v : ℝ) : ℂ))) u‖ = |p2 u| := by
  have e1 : deriv (fun v => ((p v : ℝ) : ℂ)) = fun v => ((p1 v : ℝ) : ℂ) :=
    funext fun v => (h1 v).ofReal_comp.deriv
  refine ⟨fun v => (h1 v).ofReal_comp.differentiableAt, ?_, fun u => ⟨?_, ?_, ?_⟩⟩
  · rw [e1]; exact fun v => (h2 v).ofReal_comp.differentiableAt
  · rw [Complex.norm_real, Real.norm_eq_abs]
  · rw [e1, Complex.norm_real, Real.norm_eq_abs]
  · rw [e1, (h2 u).ofReal_comp.deriv, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 1000000 in
theorem ZR_phi_pw2K' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 → ∀ (x u : ℝ),
      |u - s| ≤ κ →
      ‖deriv (deriv (fun u => VxsW T κ Ξ f Δ s x (Real.exp u))) u‖
          ≤ C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp (-(u / 2)) := by
  -- sup bounds for `Ξ, Ξ′, Ξ″, f, f′, f″`
  have hΞc : HasCompactSupport Ξ :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ξ) (hΞ.supp.trans Set.Ioo_subset_Icc_self)
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) (hf.supp.trans Set.Ioo_subset_Icc_self)
  have hΞ1 := contDiff_infty_iff_deriv.mp hΞ.smooth
  have hΞ2 := contDiff_infty_iff_deriv.mp hΞ1.2
  have hf1 := contDiff_infty_iff_deriv.mp hf.smooth
  have hf2 := contDiff_infty_iff_deriv.mp hf1.2
  obtain ⟨M1, hM1⟩ := hΞ.smooth.continuous.bounded_above_of_compact_support hΞc
  obtain ⟨M2, hM2⟩ := hΞ1.2.continuous.bounded_above_of_compact_support hΞc.deriv
  obtain ⟨M3, hM3⟩ := hΞ2.2.continuous.bounded_above_of_compact_support hΞc.deriv.deriv
  obtain ⟨M4, hM4⟩ := hf.smooth.continuous.bounded_above_of_compact_support hfc
  obtain ⟨M5, hM5⟩ := hf1.2.continuous.bounded_above_of_compact_support hfc.deriv
  obtain ⟨M6, hM6⟩ := hf2.2.continuous.bounded_above_of_compact_support hfc.deriv.deriv
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + |M1| + |M2| + |M3| + |M4| + |M5| + |M6| := ⟨_, rfl⟩
  have hMs := fun (a : ℝ) => abs_nonneg a
  have hM1' : ∀ z, |Ξ z| ≤ M := fun z => by
    have := hM1 z; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M1, hMs M2, hMs M3, hMs M4, hMs M5, hMs M6]
  have hM2' : ∀ z, |deriv Ξ z| ≤ M := fun z => by
    have := hM2 z; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M2, hMs M1, hMs M3, hMs M4, hMs M5, hMs M6]
  have hM3' : ∀ z, |deriv (deriv Ξ) z| ≤ M := fun z => by
    have := hM3 z; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M3, hMs M1, hMs M2, hMs M4, hMs M5, hMs M6]
  have hM4' : ∀ z, |f z| ≤ M := fun z => by
    have := hM4 z; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M4, hMs M1, hMs M2, hMs M3, hMs M5, hMs M6]
  have hM5' : ∀ z, |deriv f z| ≤ M := fun z => by
    have := hM5 z; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M5, hMs M1, hMs M2, hMs M3, hMs M4, hMs M6]
  have hM6' : ∀ z, |deriv (deriv f) z| ≤ M := fun z => by
    have := hM6 z; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M6, hMs M1, hMs M2, hMs M3, hMs M4, hMs M5]
  have hM0 : 1 ≤ M := by rw [hM]; linarith [hMs M1, hMs M2, hMs M3, hMs M4, hMs M5, hMs M6]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / κ := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by rw [hc]; exact one_le_one_div hκ hκ1
  refine ⟨52 * M ^ 2 * c ^ 2, by positivity, ?_⟩
  intro s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u hu
  have hT0 : 0 ≤ T := by linarith
  have hN0 := Real.exp_pos s
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = T + Δ * Real.exp s + 1 := ⟨_, rfl⟩
  have hΔN : 0 ≤ Δ * Real.exp s := by positivity
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hTX : T ≤ X := by rw [hX]; linarith
  rw [← hX]
  -- the product form
  have hφ : (fun u => VxsW T κ Ξ f Δ s x (Real.exp u))
      = fun v => ((Real.exp (v * -(1 / 2)) : ℝ) : ℂ) * ZetaShell.DTFacts.DTf T (s - v)
          * ((Ξ ((v - s) / κ) : ℝ) : ℂ) * ((f (Δ * (Real.exp v - x)) : ℝ) : ℂ) := by
    funext v; unfold VxsW As; rw [Real.log_exp, ← Real.exp_mul, DT_eq_DTf]
  rw [hφ]
  obtain ⟨E₀, hE₀⟩ : ∃ E : ℝ, E = Real.exp (u * -(1 / 2)) := ⟨_, rfl⟩
  have hE₀p : 0 < E₀ := by rw [hE₀]; exact Real.exp_pos _
  have hhalf : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
  -- factor `e^{−u/2}`
  obtain ⟨dE1, dE2, bE⟩ := castBnd (fun v => Real.exp (v * -(1 / 2)))
    (fun v => Real.exp (v * -(1 / 2)) * -(1 / 2)) (fun v => Real.exp (v * -(1 / 2)) * -(1 / 2) * -(1 / 2))
    (fun v => (Real.hasDerivAt_exp _).comp v (hasDerivAt_mul_const _))
    (fun v => ((Real.hasDerivAt_exp _).comp v (hasDerivAt_mul_const _)).mul_const _)
  obtain ⟨bE0, bE1, bE2⟩ := bE u
  have iE0 : ‖((Real.exp (u * -(1 / 2)) : ℝ) : ℂ)‖ ≤ E₀ := by
    rw [bE0, ← hE₀, abs_of_pos hE₀p]
  have iE1 : ‖deriv (fun v => ((Real.exp (v * -(1 / 2)) : ℝ) : ℂ)) u‖ ≤ E₀ := by
    rw [bE1, ← hE₀, abs_mul, abs_of_pos hE₀p, hhalf]; linarith
  have iE2 : ‖deriv (deriv (fun v => ((Real.exp (v * -(1 / 2)) : ℝ) : ℂ))) u‖ ≤ E₀ := by
    rw [bE2, ← hE₀, abs_mul, abs_mul, abs_of_pos hE₀p, hhalf]; linarith
  -- factor `D_T(s − u)`
  have hDT := contDiff_infty_iff_deriv.mp (ZetaShell.DTFacts.DTf_contDiff T (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have hDT2 := contDiff_infty_iff_deriv.mp hDT.2
  have hD1 : ∀ v, HasDerivAt (fun v => ZetaShell.DTFacts.DTf T (s - v))
      (-(deriv (ZetaShell.DTFacts.DTf T) (s - v))) v :=
    fun v => HasDerivAt.comp_const_sub s v (hDT.1 (s - v)).hasDerivAt
  have eD1 : deriv (fun v => ZetaShell.DTFacts.DTf T (s - v))
      = fun v => -(deriv (ZetaShell.DTFacts.DTf T) (s - v)) := funext fun v => (hD1 v).deriv
  have hD2 : ∀ v, HasDerivAt (fun v => -(deriv (ZetaShell.DTFacts.DTf T) (s - v)))
      (deriv (deriv (ZetaShell.DTFacts.DTf T)) (s - v)) v := fun v =>
    ((HasDerivAt.comp_const_sub s v (hDT2.1 (s - v)).hasDerivAt).neg).congr_deriv (neg_neg _)
  have dD1 : Differentiable ℝ (fun v => ZetaShell.DTFacts.DTf T (s - v)) := fun v => (hD1 v).differentiableAt
  have dD2 : Differentiable ℝ (deriv (fun v => ZetaShell.DTFacts.DTf T (s - v))) := by
    rw [eD1]; exact fun v => (hD2 v).differentiableAt
  have iD0 : ‖ZetaShell.DTFacts.DTf T (s - u)‖ ≤ T := ZetaShell.DTFacts.norm_DTf_le hT0 _
  have iD1 : ‖deriv (fun v => ZetaShell.DTFacts.DTf T (s - v)) u‖ ≤ 2 * T * X := by
    rw [eD1, norm_neg]
    have := ZetaShell.DTFacts.norm_deriv_DTf_le hT0 (s - u)
    have hTT : T * T ≤ T * X := mul_le_mul_of_nonneg_left hTX hT0
    linarith
  have iD2 : ‖deriv (deriv (fun v => ZetaShell.DTFacts.DTf T (s - v))) u‖ ≤ 4 * T * X ^ 2 := by
    rw [eD1, (hD2 u).deriv]
    have := ZetaShell.DTFacts.norm_deriv2_DTf_le hT0 (s - u)
    have hT2 : T ^ 3 ≤ T * X ^ 2 := by
      have h22 : T ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hT0 hTX 2
      have := mul_le_mul_of_nonneg_left h22 hT0
      linarith
    linarith
  -- factor `Ξ((u − s)/κ)`
  have hk : ∀ v, HasDerivAt (fun v => (v - s) / κ) (1 / κ) v := fun v =>
    ((hasDerivAt_id' v).sub_const s).div_const κ
  obtain ⟨dX1, dX2, bX⟩ := castBnd (fun v => Ξ ((v - s) / κ))
    (fun v => deriv Ξ ((v - s) / κ) * (1 / κ)) (fun v => deriv (deriv Ξ) ((v - s) / κ) * (1 / κ) * (1 / κ))
    (fun v => (hΞ1.1 _).hasDerivAt.comp v (hk v))
    (fun v => ((hΞ2.1 _).hasDerivAt.comp v (hk v)).mul_const _)
  obtain ⟨bX0, bX1, bX2⟩ := bX u
  rw [← hc] at bX1 bX2
  have hc0 : 0 ≤ c := by linarith
  have hcc : c ≤ c ^ 2 := by nlinarith
  have hMc : M ≤ M * c ^ 2 := le_mul_of_one_le_right (by linarith) (by linarith)
  have hMc1 : M * c ≤ M * c ^ 2 := mul_le_mul_of_nonneg_left hcc (by linarith)
  have iX0 : ‖((Ξ ((u - s) / κ) : ℝ) : ℂ)‖ ≤ M * c ^ 2 := by rw [bX0]; linarith [hM1' ((u - s) / κ)]
  have iX1 : ‖deriv (fun v => ((Ξ ((v - s) / κ) : ℝ) : ℂ)) u‖ ≤ M * c ^ 2 := by
    rw [bX1, abs_mul, abs_of_nonneg hc0]
    have := mul_le_mul_of_nonneg_right (hM2' ((u - s) / κ)) hc0
    linarith
  have iX2 : ‖deriv (deriv (fun v => ((Ξ ((v - s) / κ) : ℝ) : ℂ))) u‖ ≤ M * c ^ 2 := by
    rw [bX2, abs_mul, abs_mul, abs_of_nonneg hc0]
    have := mul_le_mul_of_nonneg_right (hM3' ((u - s) / κ)) (mul_nonneg hc0 hc0)
    calc |deriv (deriv Ξ) ((u - s) / κ)| * c * c = |deriv (deriv Ξ) ((u - s) / κ)| * (c * c) := by ring
      _ ≤ M * (c * c) := this
      _ = M * c ^ 2 := by ring
  -- factor `f(Δ(e^u − x))`
  have hh : ∀ v, HasDerivAt (fun v => Δ * (Real.exp v - x)) (Δ * Real.exp v) v := fun v =>
    ((Real.hasDerivAt_exp v).sub_const x).const_mul Δ
  have hh' : ∀ v, HasDerivAt (fun v => Δ * Real.exp v) (Δ * Real.exp v) v := fun v =>
    (Real.hasDerivAt_exp v).const_mul Δ
  obtain ⟨dF1, dF2, bF⟩ := castBnd (fun v => f (Δ * (Real.exp v - x)))
    (fun v => deriv f (Δ * (Real.exp v - x)) * (Δ * Real.exp v))
    (fun v => deriv (deriv f) (Δ * (Real.exp v - x)) * (Δ * Real.exp v) * (Δ * Real.exp v)
      + deriv f (Δ * (Real.exp v - x)) * (Δ * Real.exp v))
    (fun v => (hf1.1 _).hasDerivAt.comp v (hh v))
    (fun v => ((hf2.1 _).hasDerivAt.comp v (hh v)).mul (hh' v))
  obtain ⟨bF0, bF1, bF2⟩ := bF u
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hY0 : 0 ≤ Δ * Real.exp u := by positivity
  have hY : Δ * Real.exp u ≤ 3 * X := by
    have h1 : Real.exp u ≤ 3 * Real.exp s := by
      calc Real.exp u ≤ Real.exp (s + 1) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hu).2])
        _ = Real.exp s * Real.exp 1 := Real.exp_add s 1
        _ ≤ Real.exp s * 3 := mul_le_mul_of_nonneg_left he hN0.le
        _ = 3 * Real.exp s := by ring
    have h2 : Δ * Real.exp u ≤ Δ * (3 * Real.exp s) := mul_le_mul_of_nonneg_left h1 hΔ.le
    rw [hX]; linarith
  have iF0 : ‖((f (Δ * (Real.exp u - x)) : ℝ) : ℂ)‖ ≤ M := by rw [bF0]; exact hM4' _
  have iF1 : ‖deriv (fun v => ((f (Δ * (Real.exp v - x)) : ℝ) : ℂ)) u‖ ≤ 3 * M * X := by
    rw [bF1, abs_mul, abs_of_nonneg hY0]
    have := mul_le_mul (hM5' (Δ * (Real.exp u - x))) hY hY0 (by linarith)
    linarith
  have iF2 : ‖deriv (deriv (fun v => ((f (Δ * (Real.exp v - x)) : ℝ) : ℂ))) u‖ ≤ 12 * M * X ^ 2 := by
    rw [bF2]
    have a1 := hM6' (Δ * (Real.exp u - x))
    have a2 := hM5' (Δ * (Real.exp u - x))
    have hYY : (Δ * Real.exp u) * (Δ * Real.exp u) ≤ 9 * X ^ 2 := by
      have := mul_le_mul hY hY hY0 (by linarith)
      linarith
    have t1 : |deriv (deriv f) (Δ * (Real.exp u - x)) * (Δ * Real.exp u) * (Δ * Real.exp u)| ≤ M * (9 * X ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hY0, mul_assoc]
      exact mul_le_mul a1 hYY (by positivity) (by linarith)
    have t2 : |deriv f (Δ * (Real.exp u - x)) * (Δ * Real.exp u)| ≤ M * (3 * X) := by
      rw [abs_mul, abs_of_nonneg hY0]
      exact mul_le_mul a2 hY hY0 (by linarith)
    have t3 := abs_add_le (deriv (deriv f) (Δ * (Real.exp u - x)) * (Δ * Real.exp u) * (Δ * Real.exp u))
      (deriv f (Δ * (Real.exp u - x)) * (Δ * Real.exp u))
    have hXX2 : X ≤ X ^ 2 := by nlinarith
    have hXX : M * (3 * X) ≤ 3 * M * X ^ 2 := by
      have := mul_le_mul_of_nonneg_left hXX2 (show (0 : ℝ) ≤ 3 * M by linarith)
      linarith
    linarith
  -- products
  have hET : 0 ≤ E₀ * T := mul_nonneg hE₀p.le hT0
  obtain ⟨dED1, dED2, nED0, nED1, nED2⟩ := Bnd_mul _ _ dE1 dE2 dD1 dD2 u E₀ E₀ E₀ T (2 * T * X) (4 * T * X ^ 2)
    iE0 iE1 iE2 iD0 iD1 iD2
  have q1 : E₀ * T ≤ E₀ * T * X := le_mul_of_one_le_right hET hX1
  have q2 : E₀ * T * X ≤ E₀ * T * X ^ 2 := by
    calc E₀ * T * X = E₀ * T * X * 1 := by ring
      _ ≤ E₀ * T * X * X := mul_le_mul_of_nonneg_left hX1 (by positivity)
      _ = E₀ * T * X ^ 2 := by ring
  have jED1 : ‖deriv (fun v => ((Real.exp (v * -(1 / 2)) : ℝ) : ℂ) * ZetaShell.DTFacts.DTf T (s - v)) u‖
      ≤ 3 * (E₀ * T * X) := by linarith
  have jED2 : ‖deriv (deriv (fun v => ((Real.exp (v * -(1 / 2)) : ℝ) : ℂ)
      * ZetaShell.DTFacts.DTf T (s - v))) u‖ ≤ 9 * (E₀ * T * X ^ 2) := by linarith
  have jED0 : ‖((Real.exp (u * -(1 / 2)) : ℝ) : ℂ) * ZetaShell.DTFacts.DTf T (s - u)‖ ≤ E₀ * T := by
    linarith
  obtain ⟨dEX1, dEX2, nEX0, nEX1, nEX2⟩ := Bnd_mul _ _ dED1 dED2 dX1 dX2 u (E₀ * T) (3 * (E₀ * T * X))
    (9 * (E₀ * T * X ^ 2)) (M * c ^ 2) (M * c ^ 2) (M * c ^ 2) jED0 jED1 jED2 iX0 iX1 iX2
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = E₀ * T * (M * c ^ 2) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact mul_nonneg hET (by positivity)
  have r1 : Q ≤ Q * X := le_mul_of_one_le_right hQ0 hX1
  have r2 : Q * X ≤ Q * X ^ 2 := by
    calc Q * X = Q * X * 1 := by ring
      _ ≤ Q * X * X := mul_le_mul_of_nonneg_left hX1 (by positivity)
      _ = Q * X ^ 2 := by ring
  have kEX0 : ‖((Real.exp (u * -(1 / 2)) : ℝ) : ℂ) * ZetaShell.DTFacts.DTf T (s - u)
      * ((Ξ ((u - s) / κ) : ℝ) : ℂ)‖ ≤ Q := by rw [hQ]; exact nEX0
  have kEX1 : ‖deriv (fun v => ((Real.exp (v * -(1 / 2)) : ℝ) : ℂ) * ZetaShell.DTFacts.DTf T (s - v)
      * ((Ξ ((v - s) / κ) : ℝ) : ℂ)) u‖ ≤ 4 * (Q * X) := by
    have e : 3 * (E₀ * T * X) * (M * c ^ 2) + E₀ * T * (M * c ^ 2) = 3 * (Q * X) + Q := by rw [hQ]; ring
    linarith
  have kEX2 : ‖deriv (deriv (fun v => ((Real.exp (v * -(1 / 2)) : ℝ) : ℂ) * ZetaShell.DTFacts.DTf T (s - v)
      * ((Ξ ((v - s) / κ) : ℝ) : ℂ))) u‖ ≤ 16 * (Q * X ^ 2) := by
    have e : 9 * (E₀ * T * X ^ 2) * (M * c ^ 2) + 2 * (3 * (E₀ * T * X) * (M * c ^ 2))
        + E₀ * T * (M * c ^ 2) = 9 * (Q * X ^ 2) + 6 * (Q * X) + Q := by rw [hQ]; ring
    linarith
  obtain ⟨-, -, -, -, nF2⟩ := Bnd_mul _ _ dEX1 dEX2 dF1 dF2 u Q (4 * (Q * X)) (16 * (Q * X ^ 2))
    M (3 * M * X) (12 * M * X ^ 2) kEX0 kEX1 kEX2 iF0 iF1 iF2
  refine nF2.trans (le_of_eq ?_)
  have hEu : Real.exp (-(u / 2)) = E₀ := by rw [hE₀]; congr 1; ring
  rw [hEu, hQ]; ring

end ZetaShell.PropZ
