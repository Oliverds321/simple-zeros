/-
L7_5 (28 Sep 2026), round 8: `ZP_deriv_bound'` (the statement of the leaf `ZP_deriv_bound`).
Family `G_{a,b,c}(s) = W^{(c)}(s−s₀) · p(s) · Q_{a,b}(s)`, `p(s) = (Δe^s)² e^{s(β+β′−2)}`:
  `G_{a,b,c}′ = G_{a,b,c+1} + (β+β′) G_{a,b,c} + G_{a+1,b,c} + G_{a,b+1,c}`,
so every `G` is `C^∞` and `|∂^n G_{a,b,c}| ≤ 5^n M⋆` when `a+b+c+n ≤ A`, where `M⋆` bounds all `|G_{a,b,c}|`,
`a+b+c ≤ A`: Step 4 (`hone`) with Cauchy–Schwarz (`Qab_sq_le`), `e^{s(β+β′−2)} ≤ 9 N₀^{β+β′−2}`, `ϖ(μ_s) ≤ 3^k ϖ(μ)`.
-/
import ZetaShell.PropZ.ZZ3c_Q
import ZetaShell.PropZ.ZZ2a_OneZeroSplit

open MeasureTheory

namespace ZetaShell.PropZ

theorem iD_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n F) := by
  rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv n hF

theorem iD_diff (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (n : ℕ) : Differentiable ℝ (iteratedDeriv n F) :=
  ((iD_smooth F hF n).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 _).differentiable one_ne_zero

theorem iD_add (F G : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ∀ n : ℕ, iteratedDeriv n (fun x => F x + G x) = fun x => iteratedDeriv n F x + iteratedDeriv n G x
  | 0 => by simp only [iteratedDeriv_zero]
  | n + 1 => by
    rw [iteratedDeriv_succ, iD_add F G hF hG n, iteratedDeriv_succ, iteratedDeriv_succ]
    funext x
    exact deriv_add (iD_diff F hF n x) (iD_diff G hG n x)

theorem iD_cmul (c : ℂ) (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∀ n : ℕ, iteratedDeriv n (fun x => c * F x) = fun x => c * iteratedDeriv n F x
  | 0 => by simp only [iteratedDeriv_zero]
  | n + 1 => by
    rw [iteratedDeriv_succ, iD_cmul c F hF n, iteratedDeriv_succ]
    funext x
    exact deriv_const_mul c (iD_diff F hF n x)

theorem tsupport_iD (F : ℝ → ℂ) : ∀ n : ℕ, tsupport (iteratedDeriv n F) ⊆ tsupport F
  | 0 => by simp only [iteratedDeriv_zero]; exact le_rfl
  | n + 1 => by rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans (tsupport_iD F n)

theorem tsupport_iD_real (F : ℝ → ℝ) : ∀ n : ℕ, tsupport (iteratedDeriv n F) ⊆ tsupport F
  | 0 => by simp only [iteratedDeriv_zero]; exact le_rfl
  | n + 1 => by rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans (tsupport_iD_real F n)

theorem varpi_shift (T μ₀ μ : ℝ) (k : ℕ) (ρ : ℂ) (hμ₀ : 0 ≤ μ₀) (hμ : 0 ≤ μ) (h : μ ≤ 3 * μ₀) :
    varpi T μ k ρ ≤ 3 ^ k * varpi T μ₀ k ρ := by
  unfold varpi
  set D := max (|ρ.im| - 2 * T) 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  set x := 1 + D / (μ + 1) with hx
  set y := 1 + D / (μ₀ + 1) with hy
  have hx1 : 1 ≤ x := by have : 0 ≤ D / (μ + 1) := by positivity
                         linarith
  have hy1 : 1 ≤ y := by have : 0 ≤ D / (μ₀ + 1) := by positivity
                         linarith
  have hyx : y ≤ 3 * x := by
    have h1 : D / (μ₀ + 1) ≤ 3 * (D / (μ + 1)) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith), Real.rpow_natCast, Real.rpow_natCast,
    ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc y ^ k ≤ (3 * x) ^ k := pow_le_pow_left₀ (by linarith) hyx k
    _ = 3 ^ k * x ^ k := mul_pow 3 x k

set_option maxHeartbeats 1000000 in
theorem ZP_deriv_bound' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (A k : ℕ) (hA : 2 ≤ A) (hk : 2 ≤ k)
    (hone : ∃ C : ℝ, OneZeroBound κ Ξ f A k C) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (W : ℝ → ℝ), AvgWeight W → ∀ (s₀ T Δ : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 →
      ∀ (ρ ρ' : ℂ), 0 < ρ.re → ρ.re < 1 → 0 < ρ'.re → ρ'.re < 1 →
      ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => ((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s) ∧
      HasCompactSupport (fun s : ℝ => ((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s) ∧
      (∫ s : ℝ, ‖((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s‖)
        + (∫ s : ℝ, ‖iteratedDeriv A (fun s : ℝ => ((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s) s‖)
        ≤ C₂ * normCA W A * T * (Real.exp s₀ ^ (ρ.re + ρ'.re - 2) * varpi T (Δ * Real.exp s₀) k ρ
            * varpi T (Δ * Real.exp s₀) k ρ') := by
  obtain ⟨C₀, hC₀⟩ := hone
  set C := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨2 * (1 + 5 ^ A) * (C * 9 * 9 ^ k), by positivity, ?_⟩
  intro W hW s₀ T Δ hs₀ hT hΔ hΔ1 ρ ρ' hρ0 hρ1 hρ0' hρ1'
  have hT0 : 0 ≤ T := by linarith
  set σ := ρ.re + ρ'.re - 2 with hσ
  have hσ2 : |σ| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hσp : |σ + 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  -- the weight
  have hWc : HasCompactSupport W :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport W) (hW.supp.trans Set.Ioo_subset_Icc_self)
  have hWs : ∀ c : ℕ, ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv c W) := fun c => by
    rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv c hW.smooth
  have hWd : ∀ (c : ℕ) (x : ℝ), HasDerivAt (iteratedDeriv c W) (iteratedDeriv (c + 1) W x) x := fun c x => by
    rw [iteratedDeriv_succ]
    exact (((hWs c).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 _).differentiable one_ne_zero x).hasDerivAt
  have hWz : ∀ (c : ℕ) (z : ℝ), z ∉ Set.Ioo (-1 : ℝ) 1 → iteratedDeriv c W z = 0 := fun c z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hW.supp (tsupport_iD_real W c h))
  have hWb : ∀ (c : ℕ), c ≤ A → ∀ z, |iteratedDeriv c W z| ≤ normCA W A := by
    intro c hc z
    have hbdd : ∀ j : ℕ, BddAbove (Set.range fun x => |iteratedDeriv j W x|) := fun j => by
      have hjc : HasCompactSupport (iteratedDeriv j W) :=
        IsCompact.of_isClosed_subset hWc (isClosed_tsupport _) (tsupport_iD_real W j)
      obtain ⟨B, hB⟩ := (hWs j).continuous.bounded_above_of_compact_support hjc
      exact ⟨B, by rintro _ ⟨x, rfl⟩; have := hB x; rwa [Real.norm_eq_abs] at this⟩
    calc |iteratedDeriv c W z| ≤ ⨆ x, |iteratedDeriv c W x| := le_ciSup (hbdd c) z
      _ ≤ normCA W A := by
        unfold normCA
        exact Finset.single_le_sum (f := fun j => ⨆ x, |iteratedDeriv j W x|)
          (fun j _ => Real.iSup_nonneg fun x => abs_nonneg _) (Finset.mem_range.mpr (by omega))
  -- the prefactor `p`
  set p : ℝ → ℝ := fun s => (Δ * Real.exp s) ^ 2 * Real.exp (s * σ) with hp
  have hpd : ∀ s, HasDerivAt p ((σ + 2) * p s) s := fun s => by
    have h1 : HasDerivAt (fun s => Δ * Real.exp s) (Δ * Real.exp s) s := (Real.hasDerivAt_exp s).const_mul Δ
    have h2 : HasDerivAt (fun s => Real.exp (s * σ)) (Real.exp (s * σ) * σ) s :=
      (Real.hasDerivAt_exp _).comp s (hasDerivAt_mul_const σ)
    have := (h1.pow 2).mul h2
    refine this.congr_deriv ?_
    simp only [hp, Pi.pow_apply, Pi.mul_apply]; ring
  -- the family
  set G : ℕ → ℕ → ℕ → ℝ → ℂ := fun a b c s =>
    ((iteratedDeriv c W (s - s₀) : ℝ) : ℂ) * (((p s : ℝ) : ℂ) * Qab T κ Ξ f ρ ρ' Δ a b s) with hG
  have hGd : ∀ a b c s, HasDerivAt (G a b c)
      (G a b (c + 1) s + (((σ + 2 : ℝ)) : ℂ) * G a b c s + G (a + 1) b c s + G a (b + 1) c s) s := by
    intro a b c s
    have hw := ((hWd c (s - s₀)).comp_sub_const s s₀).ofReal_comp
    have hP := (hpd s).ofReal_comp
    have hQ := Qab_hasDerivAt κ hκ Ξ hΞ f hf T ρ ρ' hρ0 hρ1 hρ0' hρ1' Δ hΔ a b s
    have := hw.mul (hP.mul hQ)
    refine this.congr_deriv ?_
    simp only [hG, Pi.mul_apply]; push_cast; ring
  have hGeq : ∀ a b c, deriv (G a b c) = fun s =>
      G a b (c + 1) s + (((σ + 2 : ℝ)) : ℂ) * G a b c s + G (a + 1) b c s + G a (b + 1) c s :=
    fun a b c => funext fun s => (hGd a b c s).deriv
  have hGsm : ∀ m : ℕ, ∀ a b c, ContDiff ℝ m (G a b c) := by
    intro m
    induction m with
    | zero => intro a b c; exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun s => (hGd a b c s).continuousAt)
    | succ m ih =>
      intro a b c
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun s => (hGd a b c s).differentiableAt, fun h => by simp at h, ?_⟩
      rw [hGeq]
      exact (((ih a b (c + 1)).add (contDiff_const.mul (ih a b c))).add (ih (a + 1) b c)).add (ih a (b + 1) c)
  have hGs : ∀ a b c, ContDiff ℝ (⊤ : ℕ∞) (G a b c) := fun a b c => contDiff_infty.mpr fun m => hGsm m a b c
  -- the uniform bound `M⋆`
  set μ₀ := Δ * Real.exp s₀ with hμ₀
  have hμ₀0 : 0 < μ₀ := by positivity
  set Ms := normCA W A * (C * T * (9 * Real.exp s₀ ^ σ) * (9 ^ k * (varpi T μ₀ k ρ * varpi T μ₀ k ρ'))) with hMs
  have hvp : ∀ (μ : ℝ) (r : ℂ), 0 ≤ μ → 0 ≤ varpi T μ k r := fun μ r hμ => by
    unfold varpi
    have : 0 ≤ max (|r.im| - 2 * T) 0 / (μ + 1) := div_nonneg (le_max_right _ _) (by linarith)
    exact Real.rpow_nonneg (by linarith) _
  have hnorm0 : 0 ≤ normCA W A := (abs_nonneg _).trans (hWb 0 (by omega) 0)
  have hMs0 : 0 ≤ Ms := by
    rw [hMs]
    exact mul_nonneg hnorm0 (mul_nonneg (mul_nonneg (mul_nonneg hC0 hT0) (by positivity))
      (mul_nonneg (by positivity) (mul_nonneg (hvp _ _ hμ₀0.le) (hvp _ _ hμ₀0.le))))
  have he2 : Real.exp 2 ≤ 9 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith [Real.exp_pos 1]
  have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hGb : ∀ a b c, a ≤ A → b ≤ A → c ≤ A → ∀ s, ‖G a b c s‖ ≤ Ms := by
    intro a b c ha hb hc s
    by_cases hin : s - s₀ ∈ Set.Ioo (-1 : ℝ) 1
    swap
    · simp only [hG, hWz c _ hin, Complex.ofReal_zero, zero_mul, norm_zero]; exact hMs0
    have hss := abs_lt.mpr ⟨hin.1, hin.2⟩
    set μ := Δ * Real.exp s with hμdef
    have hμ : 0 < μ := by positivity
    have hI : ∀ (j : ℕ) (r : ℂ), j ≤ A → 0 < r.re → r.re < 1 →
        (∫ ξ, ‖Irho T κ Ξ f j r μ ξ‖ ^ 2) ≤ C * T * varpi T μ k r ^ 2 / μ ^ 2 := by
      intro j r hj h0 h1
      have h := hC₀ T hT μ hμ r h0 h1 j hj
      have h' : C₀ * T * varpi T μ k r ^ 2 ≤ C * T * varpi T μ k r ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hT0) (sq_nonneg _)
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have hQ2 := Qab_sq_le κ hκ Ξ hΞ f hf T ρ ρ' hρ0 hρ1 hρ0' hρ1' Δ hΔ a b s
    rw [← hμdef] at hQ2
    have hQ2' : ‖Qab T κ Ξ f ρ ρ' Δ a b s‖ ^ 2 ≤ (C * T * (varpi T μ k ρ * varpi T μ k ρ') / μ ^ 2) ^ 2 := by
      refine hQ2.trans ?_
      have e : (C * T * (varpi T μ k ρ * varpi T μ k ρ') / μ ^ 2) ^ 2
          = (C * T * varpi T μ k ρ ^ 2 / μ ^ 2) * (C * T * varpi T μ k ρ' ^ 2 / μ ^ 2) := by ring
      rw [e]
      exact mul_le_mul (hI a ρ ha hρ0 hρ1) (hI b ρ' hb hρ0' hρ1') (integral_nonneg fun _ => sq_nonneg _)
        (by have := hvp μ ρ hμ.le; positivity)
    have hQ : ‖Qab T κ Ξ f ρ ρ' Δ a b s‖ ≤ C * T * (varpi T μ k ρ * varpi T μ k ρ') / μ ^ 2 :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := hvp μ ρ hμ.le; have := hvp μ ρ' hμ.le; positivity)
        two_ne_zero).mp hQ2'
    have hps : p s = μ ^ 2 * Real.exp (s * σ) := by simp only [hp, hμdef]
    have hexp : Real.exp (s * σ) ≤ 9 * Real.exp s₀ ^ σ := by
      rw [← Real.exp_mul]
      have h1 : s * σ ≤ 2 + s₀ * σ := by
        have := abs_mul (s - s₀) σ
        have h5 : |s - s₀| * |σ| ≤ 1 * 2 := mul_le_mul hss.le hσ2 (abs_nonneg _) (by norm_num)
        nlinarith [le_abs_self ((s - s₀) * σ)]
      calc Real.exp (s * σ) ≤ Real.exp (2 + s₀ * σ) := Real.exp_le_exp.mpr h1
        _ = Real.exp 2 * Real.exp (s₀ * σ) := Real.exp_add _ _
        _ ≤ 9 * Real.exp (s₀ * σ) := mul_le_mul_of_nonneg_right he2 (Real.exp_pos _).le
    have hμ3 : μ ≤ 3 * μ₀ := by
      rw [hμdef, hμ₀]
      have : Real.exp s ≤ 3 * Real.exp s₀ := by
        calc Real.exp s ≤ Real.exp (s₀ + 1) := Real.exp_le_exp.mpr (by linarith [(abs_lt.mp hss).2])
          _ = Real.exp s₀ * Real.exp 1 := Real.exp_add _ _
          _ ≤ Real.exp s₀ * 3 := mul_le_mul_of_nonneg_left he1 (Real.exp_pos _).le
          _ = 3 * Real.exp s₀ := by ring
      nlinarith
    have hv1 := varpi_shift T μ₀ μ k ρ hμ₀0.le hμ.le hμ3
    have hv2 := varpi_shift T μ₀ μ k ρ' hμ₀0.le hμ.le hμ3
    have hvv : varpi T μ k ρ * varpi T μ k ρ' ≤ 9 ^ k * (varpi T μ₀ k ρ * varpi T μ₀ k ρ') := by
      calc varpi T μ k ρ * varpi T μ k ρ' ≤ (3 ^ k * varpi T μ₀ k ρ) * (3 ^ k * varpi T μ₀ k ρ') :=
            mul_le_mul hv1 hv2 (hvp μ ρ' hμ.le) (by have := hvp μ₀ ρ hμ₀0.le; positivity)
        _ = 9 ^ k * (varpi T μ₀ k ρ * varpi T μ₀ k ρ') := by rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]; ring
    simp only [hG]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (show 0 < p s by rw [hps]; positivity)]
    have hWc' := hWb c hc (s - s₀)
    have hpQ : p s * ‖Qab T κ Ξ f ρ ρ' Δ a b s‖
        ≤ C * T * (9 * Real.exp s₀ ^ σ) * (9 ^ k * (varpi T μ₀ k ρ * varpi T μ₀ k ρ')) := by
      calc p s * ‖Qab T κ Ξ f ρ ρ' Δ a b s‖
          ≤ p s * (C * T * (varpi T μ k ρ * varpi T μ k ρ') / μ ^ 2) :=
            mul_le_mul_of_nonneg_left hQ (by rw [hps]; positivity)
        _ = C * T * Real.exp (s * σ) * (varpi T μ k ρ * varpi T μ k ρ') := by rw [hps]; field_simp
        _ ≤ C * T * (9 * Real.exp s₀ ^ σ) * (9 ^ k * (varpi T μ₀ k ρ * varpi T μ₀ k ρ')) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hexp (mul_nonneg hC0 hT0)) hvv
              (mul_nonneg (hvp μ ρ hμ.le) (hvp μ ρ' hμ.le))
            exact mul_nonneg (mul_nonneg hC0 hT0) (by positivity)
    rw [hMs]
    exact mul_le_mul hWc' hpQ (mul_nonneg (by rw [hps]; positivity) (norm_nonneg _)) hnorm0
  have hGn : ∀ n : ℕ, ∀ a b c, a + b + c + n ≤ A → ∀ s, ‖iteratedDeriv n (G a b c) s‖ ≤ 5 ^ n * Ms := by
    intro n
    induction n with
    | zero =>
      intro a b c habc s
      rw [iteratedDeriv_zero, pow_zero, one_mul]
      exact hGb a b c (by omega) (by omega) (by omega) s
    | succ n ih =>
      intro a b c habc s
      rw [iteratedDeriv_succ', hGeq a b c]
      have e : iteratedDeriv n (fun s => G a b (c + 1) s + (((σ + 2 : ℝ)) : ℂ) * G a b c s + G (a + 1) b c s
            + G a (b + 1) c s) s
          = iteratedDeriv n (G a b (c + 1)) s + (((σ + 2 : ℝ)) : ℂ) * iteratedDeriv n (G a b c) s
            + iteratedDeriv n (G (a + 1) b c) s + iteratedDeriv n (G a (b + 1) c) s := by
        rw [iD_add _ _ (((hGs a b (c + 1)).add (contDiff_const.mul (hGs a b c))).add (hGs (a + 1) b c))
            (hGs a (b + 1) c),
          iD_add _ _ ((hGs a b (c + 1)).add (contDiff_const.mul (hGs a b c))) (hGs (a + 1) b c),
          iD_add _ _ (hGs a b (c + 1)) (contDiff_const.mul (hGs a b c)),
          iD_cmul _ _ (hGs a b c)]
      rw [e]
      have t1 := ih a b (c + 1) (by omega) s
      have t2 := ih a b c (by omega) s
      have t3 := ih (a + 1) b c (by omega) s
      have t4 := ih a (b + 1) c (by omega) s
      have hc2 : ‖(((σ + 2 : ℝ)) : ℂ) * iteratedDeriv n (G a b c) s‖ ≤ 2 * (5 ^ n * Ms) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hσp t2 (norm_nonneg _) (by norm_num)
      calc ‖iteratedDeriv n (G a b (c + 1)) s + (((σ + 2 : ℝ)) : ℂ) * iteratedDeriv n (G a b c) s
            + iteratedDeriv n (G (a + 1) b c) s + iteratedDeriv n (G a (b + 1) c) s‖
          ≤ ‖iteratedDeriv n (G a b (c + 1)) s‖ + ‖(((σ + 2 : ℝ)) : ℂ) * iteratedDeriv n (G a b c) s‖
            + ‖iteratedDeriv n (G (a + 1) b c) s‖ + ‖iteratedDeriv n (G a (b + 1) c) s‖ :=
            by
              have n1 := norm_add_le (iteratedDeriv n (G a b (c + 1)) s + (((σ + 2 : ℝ)) : ℂ) * iteratedDeriv n (G a b c) s
                + iteratedDeriv n (G (a + 1) b c) s) (iteratedDeriv n (G a (b + 1) c) s)
              have n2 := norm_add_le (iteratedDeriv n (G a b (c + 1)) s + (((σ + 2 : ℝ)) : ℂ) * iteratedDeriv n (G a b c) s)
                (iteratedDeriv n (G (a + 1) b c) s)
              have n3 := norm_add_le (iteratedDeriv n (G a b (c + 1)) s) ((((σ + 2 : ℝ)) : ℂ) * iteratedDeriv n (G a b c) s)
              linarith
        _ ≤ 5 ^ n * Ms + 2 * (5 ^ n * Ms) + 5 ^ n * Ms + 5 ^ n * Ms := by linarith
        _ = 5 ^ (n + 1) * Ms := by ring
  have hg : (fun s : ℝ => ((W (s - s₀) : ℝ) : ℂ) * PsiP T κ Ξ f ρ ρ' Δ s) = G 0 0 0 := by
    funext s; simp only [hG, hp, iteratedDeriv_zero]; unfold PsiP Qab; rfl
  have hsuppG : tsupport (G 0 0 0) ⊆ Set.Icc (s₀ - 1) (s₀ + 1) := by
    apply closure_minimal _ isClosed_Icc
    intro s hs
    by_contra hc
    apply hs
    have hin : s - s₀ ∉ Set.Ioo (-1 : ℝ) 1 := fun h => hc ⟨by linarith [h.1], by linarith [h.2]⟩
    simp only [hG, hWz 0 _ hin, Complex.ofReal_zero, zero_mul]
  have hzero : ∀ n : ℕ, ∀ s, s ∉ Set.Icc (s₀ - 1) (s₀ + 1) → iteratedDeriv n (G 0 0 0) s = 0 :=
    fun n s hs => image_eq_zero_of_notMem_tsupport fun h => hs (hsuppG (tsupport_iD _ n h))
  have hint : ∀ n : ℕ, n ≤ A → (∫ s : ℝ, ‖iteratedDeriv n (G 0 0 0) s‖) ≤ 2 * (5 ^ n * Ms) := by
    intro n hn
    have hIi : Integrable ((Set.Icc (s₀ - 1) (s₀ + 1)).indicator (fun _ => 5 ^ n * Ms)) :=
      (integrableOn_const (s := Set.Icc (s₀ - 1) (s₀ + 1)) (C := 5 ^ n * Ms)
        (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
    calc (∫ s : ℝ, ‖iteratedDeriv n (G 0 0 0) s‖)
        ≤ ∫ s : ℝ, (Set.Icc (s₀ - 1) (s₀ + 1)).indicator (fun _ => 5 ^ n * Ms) s :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => by
            simp only [Pi.zero_apply]; exact norm_nonneg _) hIi (Filter.Eventually.of_forall fun s => by
            by_cases hm : s ∈ Set.Icc (s₀ - 1) (s₀ + 1)
            · rw [Set.indicator_of_mem hm]; exact hGn n 0 0 0 (by omega) s
            · rw [Set.indicator_of_notMem hm]
              show ‖iteratedDeriv n (G 0 0 0) s‖ ≤ 0
              rw [hzero n s hm, norm_zero])
      _ = 2 * (5 ^ n * Ms) := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
            smul_eq_mul]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]; exact hGs 0 0 0
  · rw [hg]; exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsuppG
  · rw [hg]
    have h0 := hint 0 (by omega)
    have hA' := hint A le_rfl
    simp only [iteratedDeriv_zero, pow_zero, one_mul] at h0
    calc (∫ s : ℝ, ‖G 0 0 0 s‖) + (∫ s : ℝ, ‖iteratedDeriv A (G 0 0 0) s‖)
        ≤ 2 * Ms + 2 * (5 ^ A * Ms) := add_le_add h0 hA'
      _ = 2 * (1 + 5 ^ A) * (C * 9 * 9 ^ k) * normCA W A * T
            * (Real.exp s₀ ^ σ * varpi T μ₀ k ρ * varpi T μ₀ k ρ') := by rw [hMs]; ring

end ZetaShell.PropZ
