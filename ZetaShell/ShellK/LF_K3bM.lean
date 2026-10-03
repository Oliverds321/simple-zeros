/-
K3b-M (L7_3c, round 10, resumed): the K3b assembly along the Shell design, on `S = (α′ℒ, ∞)`, at a rate
`(log Q)^{−θ}` with `0 < θ < 1` and constant `c = 1`.
Scales: `y = log Q`, `x = y^{(1+θ)/2}`, `t = y^{−θ}` (so `t·x = y^{(1−θ)/2} → ∞`), `δ₁ = 2/x`, `c₁ = |C₁|/y`,
`D = log(2πℒ)` (`ℓ_K = ℒ + D`), `κ = 1/3240000` (`∫_S g ≥ κℒ²`), `s₁ = √y` (where `normA2_lower` starts).
* `K3b_point`: one design point, all asymptotic inputs as hypotheses. Inputs: `K3b_I` (from `integrand_le`),
  `AS_upper` + `wholeLine_le` (the whole-line route), `K3b_W`, `K3b_B`, `G_lower`, `Y_le`, `sizeR_qle_lower'`, the
  regime `𝒳 ≤ Q^{2−9/200}`; then the real-number lemma `final_arith_K3b`.
* `K3b_main`: eventually along the Shell design (`shellDesign_regime`, `scales_of_shellDesignM`, `normA2_lower`).
-/
import ZetaShell.ShellK.LF_K3bI
import ZetaShell.ShellK.LF_K3bArith

noncomputable section
open scoped BigOperators ArithmeticFunction
open MeasureTheory Set Filter

namespace ZetaShell
namespace ShellK
namespace F1c

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaShell.LemmaK

theorem aQ_le_one (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) : P.aQ ≤ 1 :=
  (Ends.S2_localHypsCoreW P hP (by linarith) (one_le_l_of_valid hP) (one_le_XQ_of_valid hP)).a_le_one

/-- `12y ≤ e^{9y/200}` for `y ≥ 11852`. -/
theorem exp_regime_aux {y : ℝ} (hy : 11852 ≤ y) : 12 * y ≤ Real.exp (9 / 200 * y) := by
  have h := Real.pow_div_factorial_le_exp _ (show (0 : ℝ) ≤ 9 / 200 * y by linarith) 2
  have e : (9 / 200 * y) ^ 2 / (Nat.factorial 2 : ℝ) = 81 / 80000 * y ^ 2 := by
    norm_num [Nat.factorial]; ring
  rw [e] at h
  nlinarith

/-- `36(1 + y)³ ≤ eʸ` for `y ≥ 6912`. -/
theorem exp_cube_aux {y : ℝ} (hy : 6912 ≤ y) : 36 * (1 + y) ^ 3 ≤ Real.exp y := by
  have h := Real.pow_div_factorial_le_exp _ (show (0 : ℝ) ≤ y by linarith) 4
  have e : y ^ 4 / (Nat.factorial 4 : ℝ) = y ^ 4 / 24 := by norm_num [Nat.factorial]
  rw [e] at h
  have h1 : (1 + y) ^ 3 ≤ 8 * y ^ 3 := by
    have : 1 + y ≤ 2 * y := by linarith
    have h0 : 0 ≤ 1 + y := by linarith
    calc (1 + y) ^ 3 ≤ (2 * y) ^ 3 := pow_le_pow_left₀ h0 this 3
      _ = 8 * y ^ 3 := by ring
  have h2 : 288 * y ^ 3 ≤ y ^ 4 / 24 := by
    have hy3 : 0 ≤ y ^ 3 := by positivity
    have : y ^ 4 = y * y ^ 3 := by ring
    rw [this]
    nlinarith
  linarith

theorem self_le_sq_aux {a : ℝ} (h : 1 ≤ a) : a ≤ a ^ 2 := by nlinarith

theorem aux48 {y : ℝ} (hy : 1 ≤ y) : 48 * y ≤ 36 * (1 + y) ^ 3 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ y) (sq_nonneg y), sq_nonneg y]

/-- `Q²(x − 1) ≤ x·C·|𝔉_Q|` from `|𝔉_Q| ≥ (18/π⁴)Q² − 6Q(1 + log Q)²`. -/
theorem sizeR_aux {Q x y sR Cf : ℝ} (hCf : 0 < Cf) (hCf6 : Cf ≤ 6) (hx0 : 0 < x) (hxy : x ≤ 1 + y)
    (hsR : Q ^ 2 - 6 * Cf * Q * (1 + y) ^ 2 ≤ Cf * sR) (hbig : 36 * (1 + y) ^ 3 ≤ Q) (hQ : 0 ≤ Q) :
    Q ^ 2 * (x - 1) ≤ x * (Cf * sR) := by
  have hy1 : 0 ≤ 1 + y := le_trans hx0.le hxy
  have h1 : 6 * Cf * x * (1 + y) ^ 2 ≤ Q := by
    have h0 : 6 * Cf * x ≤ 36 * (1 + y) := by nlinarith
    have h2 : 0 ≤ (1 + y) ^ 2 := sq_nonneg _
    calc 6 * Cf * x * (1 + y) ^ 2 ≤ 36 * (1 + y) * (1 + y) ^ 2 := mul_le_mul_of_nonneg_right h0 h2
      _ = 36 * (1 + y) ^ 3 := by ring
      _ ≤ Q := hbig
  have h3 := mul_le_mul_of_nonneg_left hsR hx0.le
  have h4 : Q * (6 * Cf * x * (1 + y) ^ 2) ≤ Q * Q := mul_le_mul_of_nonneg_left h1 hQ
  linear_combination h3 + h4

/-- the error term `V/U` of the whole-line route. -/
theorem V_aux {a L LL U C₀ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hL0 : 0 ≤ L) (hL : L ≤ 2 * LL) (hLL1 : 1 ≤ LL)
    (hU : LL ≤ U) :
    2 * a * L / Real.pi ^ 2 * (L ^ 2 / 2 + C₀ * L) / U ≤ (4 + 4 * |C₀|) * LL ^ 2 := by
  have hpi := Real.pi_gt_three
  have hU0 : 0 < U := by linarith
  have hpi2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have hm0 : 0 ≤ 2 * a * L / Real.pi ^ 2 := by positivity
  have hmL : 2 * a * L / Real.pi ^ 2 ≤ L := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 2 * a * L ≤ 2 * L := by nlinarith
    have h2 : 2 * L ≤ L * Real.pi ^ 2 := by nlinarith
    linarith
  have hq : L ^ 2 / 2 + C₀ * L ≤ L ^ 2 / 2 + |C₀| * L := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C₀) hL0; linarith
  have hq0 : 0 ≤ L ^ 2 / 2 + |C₀| * L := by positivity
  have h1 : 2 * a * L / Real.pi ^ 2 * (L ^ 2 / 2 + C₀ * L) ≤ L * (L ^ 2 / 2 + |C₀| * L) :=
    le_trans (mul_le_mul_of_nonneg_left hq hm0) (mul_le_mul_of_nonneg_right hmL hq0)
  have h2 : L * (L ^ 2 / 2 + |C₀| * L) ≤ (4 + 4 * |C₀|) * LL ^ 2 * U := by
    have hLL0 : 0 ≤ LL := by linarith
    have hL2 : L ^ 2 ≤ 4 * LL ^ 2 := by nlinarith
    have hL3 : L ^ 3 ≤ 8 * LL ^ 3 := by
      have := pow_le_pow_left₀ hL0 hL 3; nlinarith
    have hc : 0 ≤ |C₀| := abs_nonneg _
    have hLL23 : LL ^ 2 ≤ LL ^ 3 := by nlinarith
    have hLLU : LL ^ 3 ≤ LL ^ 2 * U := by
      have := mul_le_mul_of_nonneg_left hU (by positivity : (0:ℝ) ≤ LL ^ 2); nlinarith
    have e : L * (L ^ 2 / 2 + |C₀| * L) = L ^ 3 / 2 + |C₀| * L ^ 2 := by ring
    rw [e]
    have h5 : |C₀| * L ^ 2 ≤ |C₀| * (4 * LL ^ 2) := mul_le_mul_of_nonneg_left hL2 hc
    have h6 : |C₀| * (4 * LL ^ 2) ≤ |C₀| * (4 * (LL ^ 2 * U)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hc
    nlinarith
  rw [div_le_iff₀ hU0]
  linarith

set_option maxHeartbeats 1000000 in
/-- **K3b at one design point**, all asymptotic inputs as hypotheses. -/
theorem K3b_point (P : ParamsQ) (hP : P.Valid) (hw : 8 * P.w ≤ P.LB) (hw1 : P.w = 1)
    (αp C₁ C₀ S : ℝ) (Qn : ℕ) (hQn1 : 1 ≤ Qn) (hα1 : 1 < αp) (hα2 : αp < 5 / 3)
    (hC₀ : ∀ t : ℝ, 2 ≤ t → |(∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 / n) k)
      - Real.log t ^ 2 / 2| ≤ C₀ * Real.log t)
    (hS0 : 0 ≤ S) (hS : ∀ x, |deriv Real.smoothTransition x| ≤ S)
    (y x t : ℝ) (hyQ : Real.log (Qn : ℝ) = y) (hQ : P.Q = (Qn : ℝ)) (hLB : P.LB = 191 / 100 * P.LL)
    (hy : 11852 ≤ y) (hyC : |C₁| + 1 ≤ y) (hyα : 4 / (αp - 1) ≤ y)
    (hLL : y ≤ P.LL) (hLL2y : P.LL ≤ 2 * y) (hTLL : 2 * Real.pi * P.LL ^ 2 ≤ P.T)
    (hXr : P.XQ ≤ P.Q ^ ((2 : ℝ) - Design.deltaShell))
    (hlow : ∀ s, Real.sqrt y ≤ s → s ≤ P.LB - 1 → P.T / (2 * Real.pi) * (s - 1) ≤ normA2 P s)
    (hx2 : 2 ≤ x) (hxy : x ≤ y) (hκx : 1 ≤ 1 / 3240000 * x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsmall : 11 + 3 * |C₁| + (2 * (14 + 16 * (1 + (1 + S) * (2 * |C₀| + 10)) + 4 * |C₀|) + 4) / (1 / 3240000)
      + 2 * (Real.log (4 * Real.pi) + Real.log y) ≤ t * x) :
    IntegrableOn
        (fun s => P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
        (Ioi (αp * P.LL)) ∧
      IntegrableOn (fun s => P.gQ s * (normA2 P s * shellWt P αp s)) (Ioi (αp * P.LL)) ∧
      (∫ s in Ioi (αp * P.LL),
          P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
        ≤ (1 + t) * Family.qle.sizeR Qn * ∫ s in Ioi (αp * P.LL), P.gQ s * (normA2 P s * shellWt P αp s) ∧
      P.s0 ≤ αp * P.LL ∧ 0 ≤ αp * P.LL := by
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = 1 + (1 + S) * (2 * |C₀| + 10) := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  obtain ⟨KE, hKE⟩ : ∃ KE : ℝ, KE = 14 + 16 * Kc + 4 * |C₀| := ⟨_, rfl⟩
  have hKE0 : 0 ≤ KE := by rw [hKE]; positivity
  rw [← hKc, ← hKE] at hsmall
  have hpi3 := Real.pi_gt_three
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hy1 : 1 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have hLL1 : 1 ≤ P.LL := by linarith
  have hLL0 : 0 < P.LL := by linarith
  have hLB0 : 0 < P.LB := by rw [hLB]; positivity
  have hLB2 : P.LB ≤ 2 * P.LL := by rw [hLB]; linarith
  have hT := hP.T_pos
  have hpi0 : 0 < 2 * Real.pi := by positivity
  have hU0 : 0 < P.T / (2 * Real.pi) := by positivity
  have hULL : P.LL ^ 2 ≤ P.T / (2 * Real.pi) := by rw [le_div_iff₀ hpi0]; linarith
  have hLLU : P.LL ≤ P.T / (2 * Real.pi) := le_trans (self_le_sq_aux hLL1) hULL
  have hQnpos : (0 : ℝ) < Qn := by exact_mod_cast hQn1
  have hQ0 : 0 < P.Q := by rw [hQ]; exact hQnpos
  have hQe : Real.exp y = P.Q := by rw [hQ, ← hyQ, Real.exp_log hQnpos]
  have hQbig : 36 * (1 + y) ^ 3 ≤ P.Q := by rw [← hQe]; exact exp_cube_aux (by linarith)
  have hQδ : 12 * y ≤ P.Q ^ Design.deltaShell := by
    rw [Real.rpow_def_of_pos hQ0, ← hQe, Real.log_exp]
    calc 12 * y ≤ Real.exp (9 / 200 * y) := exp_regime_aux hy
      _ = Real.exp (y * Design.deltaShell) := by unfold Design.deltaShell; ring_nf
  have hx0 : 0 < x := by linarith
  -- the cut `a = α′ℒ`
  have haLL : P.LL ≤ αp * P.LL := le_mul_of_one_le_left hLL0.le hα1.le
  have ha0 : 0 < αp * P.LL := by linarith
  have h187 : (2 / 10) * P.LL ≤ (187 / 100 - αp) * P.LL := mul_le_mul_of_nonneg_right (by linarith) hLL0.le
  have haLB : αp * P.LL + 2 ≤ P.LB := by rw [hLB]; linarith
  have hcut : P.LL / 25 ≤ P.LB - 2 - αp * P.LL := by rw [hLB]; linarith
  have hstrip : Real.log P.Q + 4 ≤ αp * P.LL := by
    rw [hQ, hyQ]
    have hα0 : 0 < αp - 1 := by linarith
    have h4' : 4 ≤ (αp - 1) * y := by
      have := hyα
      rw [div_le_iff₀ hα0] at this
      linarith
    have h5 : αp * y ≤ αp * P.LL := mul_le_mul_of_nonneg_left hLL (by linarith)
    linarith
  have hs0 : P.s0 ≤ αp * P.LL := by
    have hdp : 0 ≤ P.deltaPrime := by
      unfold ParamsQ.deltaPrime
      rw [hQ, hyQ]
      have : 0 ≤ Real.log y := Real.log_nonneg hy1
      exact div_nonneg (mul_nonneg (by norm_num) this) hypos.le
    have hs0' : P.s0 = (1 - P.deltaPrime) * Real.log P.Q := rfl
    rw [hs0', hQ, hyQ]
    have : 0 ≤ P.deltaPrime * y := mul_nonneg hdp hypos.le
    have e : (1 - P.deltaPrime) * y = y - P.deltaPrime * y := by ring
    rw [e]
    linarith
  -- `ℓ_K = ℒ + log(2πℒ)`
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Real.log (2 * Real.pi * P.LL) := ⟨_, rfl⟩
  have hell : ellK P.Q P.T = P.LL + D := by
    unfold ellK
    rw [Lc_eq_LL, hD]
    have hQT : 0 < P.Q * P.T / (2 * Real.pi) := by positivity
    have e : P.Q * P.T * P.LL = (P.Q * P.T / (2 * Real.pi)) * (2 * Real.pi * P.LL) := by field_simp
    rw [e, Real.log_mul hQT.ne' (by positivity)]
    rfl
  have h2piLL : 2 * Real.pi * 1 ≤ 2 * Real.pi * P.LL := mul_le_mul_of_nonneg_left hLL1 hpi0.le
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.log_nonneg (by linarith)
  have hell0 : 0 ≤ ellK P.Q P.T := by rw [hell]; linarith
  have hDy : D ≤ Real.log (4 * Real.pi) + Real.log y := by
    rw [hD, ← Real.log_mul (by positivity) hypos.ne']
    have h2 : 2 * Real.pi * P.LL ≤ 2 * Real.pi * (2 * y) := mul_le_mul_of_nonneg_left hLL2y hpi0.le
    exact Real.log_le_log (by positivity) (by linarith)
  -- `δ₁ = 2/x`
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = P.Q ^ 2 / (12 * x) := ⟨_, rfl⟩
  have hX0 : 0 ≤ P.XQ := (Real.exp_pos _).le
  have hXZ : P.XQ ≤ Z := by
    have hsplit : P.Q ^ ((2 : ℝ) - Design.deltaShell) = P.Q ^ 2 / P.Q ^ Design.deltaShell := by
      rw [Real.rpow_sub hQ0, Real.rpow_two]
    have h12 : 12 * x ≤ P.Q ^ Design.deltaShell := by linarith
    rw [hZ]
    calc P.XQ ≤ P.Q ^ 2 / P.Q ^ Design.deltaShell := by rw [← hsplit]; exact hXr
      _ ≤ P.Q ^ 2 / (12 * x) := div_le_div_of_nonneg_left (by positivity) (by positivity) h12
  have hQQ : P.Q ≤ P.Q ^ 2 := self_le_sq_aux (by linarith [aux48 hy1])
  have h4Z : 4 ≤ Z := by
    rw [hZ, le_div_iff₀ (by positivity)]
    have := aux48 hy1
    linarith
  have hZQ : Z ≤ P.Q ^ 2 := by
    rw [hZ]; exact div_le_self (by positivity) (by linarith)
  have hXQ2 : P.XQ / P.Q ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hXsq : (P.XQ / P.Q) ^ 2 ≤ Z := by
    have e : (P.XQ / P.Q) ^ 2 = P.XQ * (P.XQ / P.Q ^ 2) := by field_simp
    rw [e]
    calc P.XQ * (P.XQ / P.Q ^ 2) ≤ P.XQ * 1 := mul_le_mul_of_nonneg_left hXQ2 hX0
      _ ≤ Z := by linarith
  have hQLL : P.Q ^ 2 / P.LL ≤ 12 * Z := by
    have e : 12 * Z = P.Q ^ 2 / x := by rw [hZ]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) hx0 (le_trans hxy hLL)
  have h2piX : 2 * Real.pi * P.XQ ≤ 7 * Z := mul_le_mul (by linarith) hXZ hX0 (by norm_num)
  have hδ : 2 * Real.pi * P.XQ + 4 + (P.XQ / P.Q) ^ 2 + P.Q ^ 2 / P.LL ≤ 2 / x * P.Q ^ 2 := by
    have e : 2 / x * P.Q ^ 2 = 24 * Z := by rw [hZ]; field_simp; ring
    rw [e]
    linarith
  have hδ₁0 : 0 ≤ 2 / x := by positivity
  have hδ₁x : 2 / x * x ≤ 2 := by rw [div_mul_cancel₀ _ hx0.ne']
  have hδ₁1 : 2 / x ≤ 1 := by rw [div_le_one hx0]; exact hx2
  -- `κ_C = 1 − C₁/y`
  have hc₁0 : 0 ≤ |C₁| / y := by positivity
  have hc₁x : |C₁| / y * x ≤ |C₁| := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hypos]
    exact mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
  have hc₁1 : |C₁| / y ≤ 1 := by rw [div_le_one hypos]; linarith
  have hκ1 : 1 - |C₁| / y ≤ 1 - C₁ / y := by
    have : C₁ / y ≤ |C₁| / y := div_le_div_of_nonneg_right (le_abs_self _) hypos.le
    linarith
  have hκ2 : 1 - C₁ / y ≤ 1 + |C₁| / y := by
    have : -C₁ / y ≤ |C₁| / y := div_le_div_of_nonneg_right (neg_le_abs _) hypos.le
    rw [neg_div] at this
    linarith
  have hκC0 : 0 ≤ 1 - C₁ / y := by linarith
  -- the family size
  have hCf0 : 0 < Cfam := by unfold Cfam; positivity
  have hCf6 : Cfam ≤ 6 := by
    unfold Cfam
    have : Real.pi ^ 4 ≤ 3.15 ^ 4 := pow_le_pow_left₀ (by linarith) hpi4.le 4
    rw [div_le_iff₀ (by norm_num)]
    norm_num at this ⊢
    linarith
  have hsR := sizeR_qle_lower' Qn hQn1
  have hsR' : P.Q ^ 2 - 6 * Cfam * P.Q * (1 + y) ^ 2 ≤ Cfam * Family.qle.sizeR Qn := by
    have hCf : Cfam * (18 / Real.pi ^ 4) = 1 := by unfold Cfam; field_simp
    have h1 := mul_le_mul_of_nonneg_left hsR hCf0.le
    rw [hQ, ← hyQ]
    have e : Cfam * (18 / Real.pi ^ 4 * (Qn : ℝ) ^ 2 - 6 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2)
        = (Cfam * (18 / Real.pi ^ 4)) * (Qn : ℝ) ^ 2 - 6 * Cfam * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by ring
    rw [e, hCf, one_mul] at h1
    exact h1
  have hsRx : P.Q ^ 2 * (x - 1) ≤ x * (Cfam * Family.qle.sizeR Qn) :=
    sizeR_aux hCf0 hCf6 hx0 (by linarith) hsR' hQbig hQ0.le
  have hsR0 : 0 ≤ Family.qle.sizeR Qn := by unfold Family.sizeR; positivity
  -- the integrated pieces
  have hTL : 1 ≤ P.T * P.LL := by
    have h1 : 2 * Real.pi * 1 ≤ 2 * Real.pi * P.LL ^ 2 :=
      mul_le_mul_of_nonneg_left (le_trans hLL1 (self_le_sq_aux hLL1)) hpi0.le
    have hT1 : 1 ≤ P.T := by linarith
    exact one_le_mul_of_one_le_of_one_le hT1 hLL1
  obtain ⟨hIint, hI⟩ := K3b_I P hP hw C₁ Qn hTL (2 / x) hδ (αp * P.LL)
  have hsq : Real.sqrt y ≤ y := Real.sqrt_le_iff.mpr ⟨hypos.le, self_le_sq_aux hy1⟩
  have hlowB : ∀ s, αp * P.LL < s → s ≤ P.LB - 1 → P.T / (2 * Real.pi) * (s - 1) ≤ normA2 P s :=
    fun s hs hs' =>
    hlow s (by linarith) hs'
  obtain ⟨hBint, hB⟩ := K3b_B P hP hw αp hLL1 hstrip haLL hlowB
  have hlowA : ∀ s, Real.sqrt y < s → s ≤ αp * P.LL → P.T / (2 * Real.pi) * (s - 1) ≤ normA2 P s :=
    fun s hs hs' =>
    hlow s hs.le (by linarith)
  have hwhole := wholeLine_le P hP hw hC₀ (by linarith) hS
  have hAS := AS_upper P hP hw (Real.sqrt y) (αp * P.LL) _ _ (Real.sqrt_nonneg _) (by linarith) (by linarith)
    hlowA hwhole
  rw [← hKc] at hAS
  have hWb := K3b_W P hP hw C₁ Qn (by rw [hyQ]; exact hκC0) hell0 (by linarith) (αp * P.LL)
  rw [hyQ] at hWb
  have hG := G_lower P hP hw hw1 (αp * P.LL) ha0.le haLB
  have hYL := Y_le P hP hw (αp * P.LL)
  have hY0 : 0 ≤ ∫ s in Ioi (αp * P.LL), P.gQ s * s :=
    setIntegral_nonneg measurableSet_Ioi fun s hs =>
      mul_nonneg (hP.gQ_nonneg hw s) (by have : αp * P.LL < s := hs; linarith)
  -- `G ≥ κℒ²`
  have hGκ : 1 / 3240000 * P.LL ^ 2 ≤ ∫ s in Ioi (αp * P.LL), P.gQ s := by
    have h1 : (P.LL / 25) ^ 2 ≤ (P.LB - 2 - αp * P.LL) ^ 2 := pow_le_pow_left₀ (by positivity) hcut 2
    have e : 1 / 3240000 * P.LL ^ 2 = (P.LL / 25) ^ 2 / 5184 := by ring
    rw [e]
    linarith
  -- `E ≤ K_E ℒ²`
  have ha1 := aQ_le_one P hP hw
  have ha0' : 0 ≤ P.aQ := hP.aQ_pos.le
  have hV := V_aux (C₀ := C₀) ha0' ha1 hLB0.le hLB2 hLL1 hLLU
  have hgall : (∫ s, P.gQ s) ≤ 4 * P.LL ^ 2 := by
    rw [integral_gQ_eq hP hw]
    have h1 : P.aQ * P.LB ≤ P.LB := mul_le_of_le_one_left hLB0.le ha1
    have h2 : (P.aQ * P.LB) ^ 2 ≤ P.LB ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : P.LB ^ 2 ≤ (2 * P.LL) ^ 2 := pow_le_pow_left₀ hLB0.le hLB2 2
    have e : (2 * P.LL) ^ 2 = 4 * P.LL ^ 2 := by ring
    linarith
  have hLBs : P.LB * Real.sqrt y ^ 2 ≤ 2 * P.LL ^ 2 := by
    rw [Real.sq_sqrt hypos.le]
    have := mul_le_mul hLB2 hLL hypos.le (by linarith)
    have e : 2 * P.LL * P.LL = 2 * P.LL ^ 2 := by ring
    linarith
  have hKterm : Kc * (P.LB + 2) ^ 2 ≤ 16 * Kc * P.LL ^ 2 := by
    have h1 : (P.LB + 2) ^ 2 ≤ (4 * P.LL) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 := mul_le_mul_of_nonneg_left h1 hKc0
    have e : Kc * (4 * P.LL) ^ 2 = 16 * Kc * P.LL ^ 2 := by ring
    linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = P.LB * Real.sqrt y ^ 2 + (∫ s, P.gQ s) + Kc * (P.LB + 2) ^ 2
      + 2 * P.aQ * P.LB / Real.pi ^ 2 * (P.LB ^ 2 / 2 + C₀ * P.LB) / (P.T / (2 * Real.pi)) := ⟨_, rfl⟩
  have hEle : E ≤ KE * P.LL ^ 2 := by
    rw [hE, hKE]
    have hc : 0 ≤ |C₀| * P.LL ^ 2 := by positivity
    have hc2 : 0 ≤ P.LL ^ 2 := sq_nonneg _
    linarith
  have hA : (∫ s in Ioi (αp * P.LL), P.gQ s * normA2 P s)
      ≤ P.T / (2 * Real.pi) * ((∫ s in Ioi (αp * P.LL), P.gQ s * s) + E) := by
    refine le_trans hAS (le_of_eq ?_)
    rw [hE]
    field_simp
    ring
  -- the closing arithmetic
  have hsmall' : 11 + 3 * |C₁| + (2 * KE + 4) / (1 / 3240000) + 2 * D ≤ t * x := by linarith
  have hfin := final_arith_K3b (Q2 := P.Q ^ 2) (U := P.T / (2 * Real.pi)) (LL := P.LL) (L := P.LB) (x := x)
    (G := ∫ s in Ioi (αp * P.LL), P.gQ s) (Y := ∫ s in Ioi (αp * P.LL), P.gQ s * s)
    (A := ∫ s in Ioi (αp * P.LL), P.gQ s * normA2 P s)
    (W := ∫ s in Ioi (αp * P.LL), P.gQ s * savWeight C₁ Qn P s)
    (Bs := ∫ s in Ioi (αp * P.LL), P.gQ s * (normA2 P s * shellWt P αp s))
    (I := ∫ s in Ioi (αp * P.LL),
      P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
    (E := E) (sR := Family.qle.sizeR Qn) (κC := 1 - C₁ / y) (c₁ := |C₁| / y) (δ₁ := 2 / x)
    (ℓ := ellK P.Q P.T) (t := t) (κ := 1 / 3240000) (KE := KE) (D := D) (C₁' := |C₁|) (Cf := Cfam)
    (by linarith) (le_trans hxy (le_trans hLL hLLU)) (le_trans hxy hLL) hLB2 hLB0.le (sq_nonneg _)
    (by norm_num) hκx hGκ hEle hKE0 hδ₁0 hδ₁x hδ₁1 hc₁0 hc₁x hc₁1 hκ1 hκ2 hell0 (le_of_eq hell) hD0 hI hA
    hWb hY0 hYL hCf0 hB hsRx hsR0 ht0 ht1 hsmall'
  exact ⟨hIint, hBint, hfin, hs0, ha0.le⟩

set_option maxHeartbeats 1000000 in
/-- **K3b along the Shell design** on `(α′ℒ, ∞)`, rate `(log Q)^{−θ}`, `0 < θ < 1`, constant `1`. -/
theorem K3b_main (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ0 : 0 < θ) (hθ : θ < 1) (C₁ : ℝ) :
    ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      IntegrableOn
          (fun s => P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
          (Ioi (αp * P.LL)) ∧
        IntegrableOn (fun s => P.gQ s * (normA2 P s * shellWt P αp s)) (Ioi (αp * P.LL)) ∧
        (∫ s in Ioi (αp * P.LL),
            P.gQ s * (sieveBudgetQ P * normA2 P s - P.Q ^ 2 * savWeight C₁ Qn P s + errWeight P s))
          ≤ (1 + Real.log Qn ^ (-θ)) * Family.qle.sizeR Qn
              * ∫ s in Ioi (αp * P.LL), P.gQ s * (normA2 P s * shellWt P αp s) ∧
        P.s0 ≤ αp * P.LL ∧ 0 ≤ αp * P.LL ∧ 1 ≤ Real.log Qn := by
  obtain ⟨S, hS0, hS⟩ := st_deriv_bound
  obtain ⟨C₀, hC₀⟩ := Zeta23.Cheb.chebyshevMertens.cheb2a
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = 11 + 3 * |C₁|
      + (2 * (14 + 16 * (1 + (1 + S) * (2 * |C₀| + 10)) + 4 * |C₀|) + 4) / (1 / 3240000)
      + 2 * Real.log (4 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨θ₂, hθ₂⟩ : ∃ θ₂ : ℝ, θ₂ = (1 + θ) / 2 := ⟨_, rfl⟩
  have hθ₂0 : 0 < θ₂ := by rw [hθ₂]; linarith
  have hθ₂1 : θ₂ ≤ 1 := by rw [hθ₂]; linarith
  have hβ0 : 0 < -θ + θ₂ := by rw [hθ₂]; linarith
  have e1 : ∀ᶠ y : ℝ in atTop, max (max 11852 (|C₁| + 1)) (4 / (αp - 1)) ≤ y := eventually_ge_atTop _
  have e2 : ∀ᶠ y : ℝ in atTop, 3240000 ≤ y ^ θ₂ := (tendsto_rpow_atTop hθ₂0).eventually_ge_atTop _
  have e3 : ∀ᶠ y : ℝ in atTop, 2 * M₀ ≤ y ^ (-θ + θ₂) := (tendsto_rpow_atTop hβ0).eventually_ge_atTop _
  have e4 : ∀ᶠ y : ℝ in atTop, ‖Real.log y‖ ≤ (1 / 4) * ‖y ^ (-θ + θ₂)‖ :=
    (isLittleO_log_rpow_atTop hβ0).def (by norm_num)
  have hS2 : ((S53L75.lam : ℚ) : ℝ) ≤ 191 / 100 := by norm_num [S53L75]
  have hS1 : (1 : ℝ) ≤ ((S53L75.lam : ℚ) : ℝ) := by norm_num [S53L75]
  have hpi3 := Real.pi_gt_three
  filter_upwards [tendsto_log_nat_atTop.eventually e1, tendsto_log_nat_atTop.eventually e2,
    tendsto_log_nat_atTop.eventually e3, tendsto_log_nat_atTop.eventually e4,
    Design.shellDesign_regime S53L75 hS2 r ε hr hε (2 * Real.pi) (by linarith),
    normA2_lower r ε hr hε, eventually_ge_atTop 3] with Qn h1 h2 h3 h4 hreg hlowQ hQn3
  intro P hdes
  have hy0 : 11852 ≤ Real.log (Qn : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
  have hyC : |C₁| + 1 ≤ Real.log (Qn : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
  have hyα : 4 / (αp - 1) ≤ Real.log (Qn : ℝ) := le_trans (le_max_right _ _) h1
  have hy1 : 1 ≤ Real.log (Qn : ℝ) := by linarith
  have hypos : 0 < Real.log (Qn : ℝ) := by linarith
  have hP : P.Valid := hdes.1
  have hQ : P.Q = (Qn : ℝ) := hdes.2.1
  have hw : 8 * P.w ≤ P.LB := hdes.2.2.2.2.2.1
  have hlam : P.lam = ((S53L75.lam : ℚ) : ℝ) := hdes.2.2.2.1
  have hLB : P.LB = 191 / 100 * P.LL := by
    show P.lam * P.LL = _
    rw [hlam]; norm_num [S53L75]
  have hQn1 : 1 ≤ Qn := by omega
  obtain ⟨-, -, hKLL, hLL2y, -, hXr, -, -⟩ := hreg P hdes
  obtain ⟨-, hyLL, -, hw1⟩ := Design.scales_of_shellDesignM hS1 hdes hr hQn1
  have hLL1 : 1 ≤ P.LL := by linarith
  -- `x = y^θ₂`, `t = y^{−θ}`
  have hx1 : Real.log (Qn : ℝ) ^ θ₂ ≤ Real.log (Qn : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 hθ₂1
    rwa [Real.rpow_one] at this
  have hκx : 1 ≤ 1 / 3240000 * Real.log (Qn : ℝ) ^ θ₂ := by linarith
  have hx2 : 2 ≤ Real.log (Qn : ℝ) ^ θ₂ := by linarith
  have ht0 : 0 ≤ Real.log (Qn : ℝ) ^ (-θ) := by positivity
  have ht1 : Real.log (Qn : ℝ) ^ (-θ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have htx : Real.log (Qn : ℝ) ^ (-θ) * Real.log (Qn : ℝ) ^ θ₂ = Real.log (Qn : ℝ) ^ (-θ + θ₂) := by
    rw [← Real.rpow_add hypos]
  have hlogy : Real.log (Real.log (Qn : ℝ)) ≤ 1 / 4 * Real.log (Qn : ℝ) ^ (-θ + θ₂) := by
    have h := h4
    rw [Real.norm_of_nonneg (Real.log_nonneg hy1), Real.norm_of_nonneg (by positivity)] at h
    exact h
  have hsmall : 11 + 3 * |C₁| + (2 * (14 + 16 * (1 + (1 + S) * (2 * |C₀| + 10)) + 4 * |C₀|) + 4) / (1 / 3240000)
      + 2 * (Real.log (4 * Real.pi) + Real.log (Real.log (Qn : ℝ)))
      ≤ Real.log (Qn : ℝ) ^ (-θ) * Real.log (Qn : ℝ) ^ θ₂ := by
    rw [htx]
    rw [hM₀] at h3
    linarith
  have hpt := K3b_point P hP hw (hw1 hLL1) αp C₁ C₀ S Qn hQn1 hα1 hα2 hC₀ hS0 hS (Real.log (Qn : ℝ))
    (Real.log (Qn : ℝ) ^ θ₂) (Real.log (Qn : ℝ) ^ (-θ)) rfl hQ hLB hy0 hyC hyα hyLL hLL2y hKLL hXr
    (hlowQ P hdes) hx2 hx1 hκx ht0 ht1 hsmall
  exact ⟨hpt.1, hpt.2.1, hpt.2.2.1, hpt.2.2.2.1, hpt.2.2.2.2, hy1⟩

end F1c
end ShellK
end ZetaShell
