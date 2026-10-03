/-
L10c_K2Point (L7_10c, 3 Oct 2026): **the K2 inequality at one design point**, with every analytic input a hypothesis:
the pointwise assembly AS in ZetaQ's objects (`hAS`, with an abstract ring `R`), the window bounds of Theorem S for
rings `R_k` that dominate `R` near the centre `a + k` (`hmono`, `hwin`), the PNT lower bound `‖a(s)‖² ≥ U(s − 1)`
(`hlow`), `Q² ≤ 6|𝔉_Q|`, and the scalar facts. Rate `y^{−θ₁}`, `y = log Q`.

Route [A, here checked in Lean]: on the zone `Z = (a, b]`, `a = log Q + 4`, `b = α′ℒ`:
`F ≤ m₁ + m₂ H + m₃‖a‖²` with `H = Σ_k W₀(s−(a+k))R_k(s) ≥ R(s)`, so
`∫_Z gF ≤ m₁∫_Z g + m₂ L Σ_k∫W₀R_k + m₃∫_Z g‖a‖²`; and `J = ∫_Z g‖a‖²ℒ/s ≥ Uℒ(1 − 1/a)∫_Z g`,
`∫_Z g ≥ (ℒ/11664)(b − a)`, `∫_Z g‖a‖² ≤ α′J`.
-/
import ZetaShell.ShellK.L10c_KT

noncomputable section
open MeasureTheory Filter

namespace ZetaShell
namespace ShellK
namespace K2c

open ZetaQ ZetaShell.PropZ

theorem shellZone_sub_outZone (P : ParamsQ) (αp : ℝ) (hQ : 16 ≤ Real.log P.Q) :
    shellZone P αp ⊆ (inZone P)ᶜ := by
  intro s hs hin
  have hs1 : Real.log P.Q + 4 < s := hs.1
  have hll : 0 ≤ Real.log (Real.log P.Q) := Real.log_nonneg (by linarith)
  have hdp : 0 ≤ P.deltaPrime := by unfold ParamsQ.deltaPrime; positivity
  have hs0 : P.s0 ≤ Real.log P.Q := by
    unfold ParamsQ.s0; nlinarith
  have hin' : |s| ≤ P.s0 := hin
  have := (abs_le.mp hin').2
  linarith

/-- the closing arithmetic of K2, in real numbers. -/
theorem K2_arith (Fint I₀ I₂ IH J sR U L y a b t αp T Kc CA CS NW lam Q2 θ₁ : ℝ)
    (hy0 : 0 < y) (hyL : y ≤ L) (hL2 : L ≤ 2 * y) (ha2 : 2 ≤ a) (hLa : L ≤ 2 * a) (hab : a + 1 ≤ b)
    (hαp : αp ≤ 2) (hU : 0 < U) (hUT : T = 2 * Real.pi * U) (ht0 : 0 ≤ t) (hty : t * y = y ^ (1 - θ₁))
    (hsR : Q2 ≤ 6 * sR) (hQ2 : 0 ≤ Q2) (hCA : 0 ≤ CA) (hCS : 0 ≤ CS) (hNW : 0 ≤ NW)
    (hlam0 : 0 ≤ lam) (hlamt : lam ≤ t) (hCAlam : CA * lam ≤ 1)
    (hKc : Real.log Kc ≤ 3 * Real.log (2 * y)) (hk2 : 3 * Real.log (2 * y) + CA + 2 ≤ y ^ (1 - θ₁) / 2)
    (hF : Fint ≤ sR * U * (L + Real.log Kc + CA) * I₀ + Q2 * (1 + CA * lam) * IH + CA * lam * sR * I₂)
    (hIH0 : 0 ≤ IH) (hIH : IH ≤ 12 * (CS * NW * t * T) * L * L * (b - a))
    (hJ1 : U * L * (1 - 1 / a) * I₀ ≤ J) (hJ2 : I₂ ≤ αp * J) (hI0 : L / 11664 * (b - a) ≤ I₀)
    (hI20 : 0 ≤ I₂) :
    Fint ≤ (1 + (1 + 22000000 * CS * NW + 2 * CA) * t) * sR * J := by
  have hsR0 : 0 ≤ sR := by linarith
  have hLpos : 0 < L := by linarith
  have e3 : 1 / 2 ≤ 1 - 1 / a := by
    have : 1 / a ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) ha2
    linarith
  have hba : 0 ≤ b - a := by linarith
  have hI00 : 0 ≤ I₀ := le_trans (by positivity) hI0
  have h1a : 0 ≤ 1 - 1 / a := by linarith
  have hJ0 : 0 ≤ J := le_trans (by positivity) hJ1
  -- (i)
  have hK1 : L + Real.log Kc + CA ≤ L * (1 - 1 / a) * (1 + t) := by
    have e1 : L / a ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have e4 : y * (1 / 2) ≤ L * (1 - 1 / a) := mul_le_mul hyL e3 (by norm_num) (by linarith)
    have e4' : t * (y * (1 / 2)) ≤ t * (L * (1 - 1 / a)) := mul_le_mul_of_nonneg_left e4 ht0
    have e5 : L * (1 - 1 / a) = L - L / a := by
      rw [mul_sub, mul_one, mul_one_div]
    have e6 : L * (1 - 1 / a) * (1 + t) = L * (1 - 1 / a) + t * (L * (1 - 1 / a)) := by ring
    have e7 : t * (y * (1 / 2)) = t * y / 2 := by ring
    rw [e6]
    linarith
  have hmain : sR * U * (L + Real.log Kc + CA) * I₀ ≤ (1 + t) * sR * J := by
    calc sR * U * (L + Real.log Kc + CA) * I₀ = sR * (U * (L + Real.log Kc + CA) * I₀) := by ring
      _ ≤ sR * (U * (L * (1 - 1 / a) * (1 + t)) * I₀) := by gcongr
      _ = (1 + t) * sR * (U * L * (1 - 1 / a) * I₀) := by ring
      _ ≤ (1 + t) * sR * J := by gcongr
  -- (ii)
  have hm₂le : Q2 * (1 + CA * lam) ≤ 12 * sR := by
    calc Q2 * (1 + CA * lam) ≤ Q2 * 2 := mul_le_mul_of_nonneg_left (by linarith) hQ2
      _ ≤ 12 * sR := by linarith
  have hJlow : T * L * L * (b - a) ≤ 4 * Real.pi * 11664 * J := by
    have h1 : U * L * (1 / 2) * (L / 11664 * (b - a)) ≤ U * L * (1 - 1 / a) * I₀ := by
      gcongr
    have h2 : T * L * L * (b - a) = 4 * Real.pi * 11664 * (U * L * (1 / 2) * (L / 11664 * (b - a))) := by
      rw [hUT]; ring
    rw [h2]
    have : 0 ≤ 4 * Real.pi * 11664 := by positivity
    exact mul_le_mul_of_nonneg_left (le_trans h1 hJ1) this
  have hpi : 4 * Real.pi * 11664 * 144 ≤ 22000000 := by nlinarith [Real.pi_lt_d2]
  have hX : 0 ≤ CS * NW * t := by positivity
  have hring : Q2 * (1 + CA * lam) * IH ≤ 22000000 * CS * NW * t * sR * J := by
    calc Q2 * (1 + CA * lam) * IH ≤ (12 * sR) * (12 * (CS * NW * t * T) * L * L * (b - a)) := by
          apply mul_le_mul hm₂le hIH hIH0 (by positivity)
      _ = 144 * (CS * NW * t) * sR * (T * L * L * (b - a)) := by ring
      _ ≤ 144 * (CS * NW * t) * sR * (4 * Real.pi * 11664 * J) := by gcongr
      _ = (4 * Real.pi * 11664 * 144) * (CS * NW * t * sR * J) := by ring
      _ ≤ 22000000 * (CS * NW * t * sR * J) := by gcongr
      _ = 22000000 * CS * NW * t * sR * J := by ring
  -- (iii)
  have hthird : CA * lam * sR * I₂ ≤ 2 * CA * t * sR * J := by
    calc CA * lam * sR * I₂ ≤ (CA * t * sR) * (αp * J) := by
          apply mul_le_mul _ hJ2 hI20 (by positivity)
          gcongr
      _ ≤ (CA * t * sR) * (2 * J) := by gcongr
      _ = 2 * CA * t * sR * J := by ring
  calc Fint ≤ sR * U * (L + Real.log Kc + CA) * I₀ + Q2 * (1 + CA * lam) * IH + CA * lam * sR * I₂ := hF
    _ ≤ (1 + t) * sR * J + 22000000 * CS * NW * t * sR * J + 2 * CA * t * sR * J := by linarith
    _ = (1 + (1 + 22000000 * CS * NW + 2 * CA) * t) * sR * J := by ring

/-- the three integral bounds of `J = ∫_Z g‖a‖²·shellWt` and of `∫_Z g`. -/
theorem K2_Jbounds (P : ParamsQ) (hP : P.Valid) (hw8 : 8 * P.w ≤ P.LB) (hw1 : P.w = 1) (αp a b U : ℝ)
    (ha2 : 2 ≤ a) (hab : a ≤ b) (hb : b = αp * P.LL) (hbL : b ≤ P.LB - 2 - P.LL / 9)
    (hwt : ∀ s ∈ Set.Ioc a b, shellWt P αp s = P.LL / s)
    (hlow : ∀ s ∈ Set.Ioc a b, U * (s - 1) ≤ normA2 P s) (hU : 0 < U)
    (hint2 : IntegrableOn (fun s => P.gQ s * (normA2 P s * shellWt P αp s)) (Set.Ioc a b)) :
    U * P.LL * (1 - 1 / a) * (∫ s in Set.Ioc a b, P.gQ s)
        ≤ ∫ s in Set.Ioc a b, P.gQ s * (normA2 P s * shellWt P αp s) ∧
      (∫ s in Set.Ioc a b, P.gQ s * normA2 P s)
        ≤ αp * ∫ s in Set.Ioc a b, P.gQ s * (normA2 P s * shellWt P αp s) ∧
      P.LL / 11664 * (b - a) ≤ ∫ s in Set.Ioc a b, P.gQ s := by
  have hg0 : ∀ s, 0 ≤ P.gQ s := hP.gQ_nonneg hw8
  have hgI : Integrable P.gQ := hP.gQ_integrable hw8
  have hLpos : 0 < P.LL := hP.LL_pos
  have hspos : ∀ s ∈ Set.Ioc a b, 0 < s := fun s hs => by linarith [hs.1]
  have hT : 0 < P.T := hP.T_pos
  have hgnA : Integrable (fun s => P.gQ s * normA2 P s) := gQ_mul_integrable P hP hw8 (normA2_continuous P hT.le)
  have hnA0 : ∀ s, 0 ≤ normA2 P s := fun s => Finset.sum_nonneg fun n _ => by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [← integral_const_mul]
    refine setIntegral_mono_on (hgI.const_mul _).integrableOn hint2 measurableSet_Ioc fun s hs => ?_
    rw [hwt s hs]
    have hs0 := hspos s hs
    have hsa : 1 - 1 / a ≤ 1 - 1 / s := by
      have : 1 / s ≤ 1 / a := one_div_le_one_div_of_le (by linarith) hs.1.le
      linarith
    have e1 : U * P.LL * (1 - 1 / s) = U * (s - 1) * (P.LL / s) := by field_simp
    have e2 : U * (s - 1) * (P.LL / s) ≤ normA2 P s * (P.LL / s) :=
      mul_le_mul_of_nonneg_right (hlow s hs) (by positivity)
    have e3 : U * P.LL * (1 - 1 / a) ≤ normA2 P s * (P.LL / s) := by
      have : U * P.LL * (1 - 1 / a) ≤ U * P.LL * (1 - 1 / s) :=
        mul_le_mul_of_nonneg_left hsa (by positivity)
      linarith
    exact mul_comm (U * P.LL * (1 - 1 / a)) (P.gQ s) ▸ mul_le_mul_of_nonneg_left e3 (hg0 s)
  · rw [← integral_const_mul]
    refine setIntegral_mono_on hgnA.integrableOn (hint2.const_mul αp) measurableSet_Ioc fun s hs => ?_
    rw [hwt s hs]
    have hs0 := hspos s hs
    have h1 : 1 ≤ αp * (P.LL / s) := by
      rw [mul_div_assoc', le_div_iff₀ hs0]; rw [hb] at hs; linarith [hs.2]
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (hg0 s) (hnA0 s))
    have e : αp * (P.gQ s * (normA2 P s * (P.LL / s))) = P.gQ s * normA2 P s * (αp * (P.LL / s)) := by ring
    rw [e]; linarith
  · have hpt : ∀ s ∈ Set.Ioc a b, P.LL / 11664 ≤ P.gQ s := by
      intro s hs
      have hs0 := hspos s hs
      have hgl := hP.gQ_ge_bulk hw8 s
      rw [hw1, abs_of_pos hs0] at hgl
      have : P.LL / 9 ≤ max (P.LB - 2 * 1 - s) 0 := le_trans (by linarith [hs.2]) (le_max_left _ _)
      linarith
    have hc := setIntegral_mono_on (integrableOn_const (by simp)) hgI.integrableOn measurableSet_Ioc hpt
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hab] at hc
    linarith

/-- the integrated majorant: `∫_Z gF ≤ m₁∫_Z g + m₂∫_Z gH + m₃∫_Z g‖a‖²` and `∫_Z gH ≤ L(M+1)·(window bound)`. -/
theorem K2_majorant (P : ParamsQ) (hP : P.Valid) (hw8 : 8 * P.w ≤ P.LB) (hLB0 : 0 ≤ P.LB) (Qn : ℕ) (a b m₁ m₂ m₃ B : ℝ)
    (hm₂ : 0 ≤ m₂) (hab : a ≤ b) (hB : 0 ≤ B)
    (R : ℝ → ℝ) (Rk : ℕ → ℝ → ℝ) (hRk0 : ∀ k s, 0 ≤ Rk k s)
    (hmono : ∀ (k : ℕ) (s : ℝ), |s - (a + k)| ≤ 1 / 2 → R s ≤ Rk k s)
    (hwin : ∀ k ∈ Finset.range (⌈b - a⌉₊ + 1), Integrable (fun s => bumpW (s - (a + k)) * Rk k s) ∧
      (∫ s, bumpW (s - (a + k)) * Rk k s) ≤ B)
    (hAS : ∀ s ∈ Set.Ioc a b, FfamZ P Qn s ≤ m₁ + m₂ * R s + m₃ * normA2 P s)
    (hint1 : IntegrableOn (fun s => P.gQ s * FfamZ P Qn s) (Set.Ioc a b)) :
    ∃ IH : ℝ, 0 ≤ IH ∧ IH ≤ P.LB * (((⌈b - a⌉₊ : ℝ) + 1) * B) ∧
      (∫ s in Set.Ioc a b, P.gQ s * FfamZ P Qn s)
        ≤ m₁ * (∫ s in Set.Ioc a b, P.gQ s) + m₂ * IH + m₃ * (∫ s in Set.Ioc a b, P.gQ s * normA2 P s) := by
  set M := ⌈b - a⌉₊ with hM
  have hgc : Continuous P.gQ := hP.gQ_continuous hw8
  have hg0 : ∀ s, 0 ≤ P.gQ s := hP.gQ_nonneg hw8
  have hgL : ∀ s, P.gQ s ≤ P.LB := fun s => by
    have h := gQ_le_env P hP hw8 s
    have : max (P.LB - |s|) 0 ≤ P.LB := max_le (by linarith [abs_nonneg s]) hLB0
    linarith
  have hgI : Integrable P.gQ := hP.gQ_integrable hw8
  have hT : 0 < P.T := hP.T_pos
  have hgnA : Integrable (fun s => P.gQ s * normA2 P s) := gQ_mul_integrable P hP hw8 (normA2_continuous P hT.le)
  let H : ℝ → ℝ := fun s => ∑ k ∈ Finset.range (M + 1), bumpW (s - (a + k)) * Rk k s
  have hHi : Integrable H := integrable_finsetSum _ fun k hk => (hwin k hk).1
  have hH0 : ∀ s, 0 ≤ H s := fun s => Finset.sum_nonneg fun k _ => mul_nonneg (bumpW_nonneg _) (hRk0 k s)
  have hdom : ∀ s ∈ Set.Ioc a b, R s ≤ H s := fun s hs => dom_pointwise a b R Rk hRk0 hmono s hs
  have hHint : (∫ s, H s) ≤ ((M : ℝ) + 1) * B := by
    show (∫ s, ∑ k ∈ Finset.range (M + 1), bumpW (s - (a + k)) * Rk k s) ≤ _
    rw [integral_finsetSum _ fun k hk => (hwin k hk).1]
    refine le_trans (Finset.sum_le_sum fun k hk => (hwin k hk).2) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; exact le_rfl
  have hgH : Integrable (fun s => P.gQ s * H s) := by
    refine Integrable.bdd_mul (c := P.LB) hHi hgc.aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hgL s
  have hIH := setIntegral_mul_le (Set.Ioc a b) measurableSet_Ioc P.LB P.gQ H hg0 hgL hgc hH0 hHi
  refine ⟨∫ s in Set.Ioc a b, P.gQ s * H s, setIntegral_nonneg measurableSet_Ioc fun s _ =>
    mul_nonneg (hg0 s) (hH0 s), le_trans hIH (mul_le_mul_of_nonneg_left hHint hLB0), ?_⟩
  have hA1 : Integrable (fun s => m₁ * P.gQ s) (volume.restrict (Set.Ioc a b)) := (hgI.const_mul m₁).integrableOn
  have hA2 : Integrable (fun s => m₂ * (P.gQ s * H s)) (volume.restrict (Set.Ioc a b)) :=
    (hgH.const_mul m₂).integrableOn
  have hA : Integrable (fun s => m₁ * P.gQ s + m₂ * (P.gQ s * H s)) (volume.restrict (Set.Ioc a b)) := hA1.add hA2
  have hB' : Integrable (fun s => m₃ * (P.gQ s * normA2 P s)) (volume.restrict (Set.Ioc a b)) :=
    (hgnA.const_mul m₃).integrableOn
  have hstep : (∫ s in Set.Ioc a b, P.gQ s * FfamZ P Qn s)
      ≤ ∫ s in Set.Ioc a b, (m₁ * P.gQ s + m₂ * (P.gQ s * H s) + m₃ * (P.gQ s * normA2 P s)) := by
    refine setIntegral_mono_on hint1 (hA.add hB') measurableSet_Ioc fun s hs => ?_
    have h3 : FfamZ P Qn s ≤ m₁ + m₂ * H s + m₃ * normA2 P s := by
      have := hAS s hs
      have := mul_le_mul_of_nonneg_left (hdom s hs) hm₂
      linarith
    have := mul_le_mul_of_nonneg_left h3 (hg0 s)
    calc P.gQ s * FfamZ P Qn s ≤ P.gQ s * (m₁ + m₂ * H s + m₃ * normA2 P s) := this
      _ = m₁ * P.gQ s + m₂ * (P.gQ s * H s) + m₃ * (P.gQ s * normA2 P s) := by ring
  rw [integral_add hA hB', integral_add hA1 hA2, integral_const_mul, integral_const_mul,
    integral_const_mul] at hstep
  exact hstep

set_option maxHeartbeats 1000000 in
/-- **K2 at one design point.** -/
theorem K2_point (P : ParamsQ) (hP : P.Valid) (hw8 : 8 * P.w ≤ P.LB) (hw1 : P.w = 1) (Qn : ℕ) (αp : ℝ)
    (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (hLB : P.LB = 191 / 100 * P.LL)
    (y : ℝ) (hy : Real.log P.Q = y) (hyLL : y ≤ P.LL) (hLL2 : P.LL ≤ 2 * y) (h16 : 16 ≤ y)
    (h5 : 5 ≤ (αp - 1) * y)
    (CA CS NW θ₁ : ℝ) (hCA : 0 ≤ CA) (hCS : 0 ≤ CS) (hNW : 0 ≤ NW)
    (hk2 : 3 * Real.log (2 * y) + CA + 2 ≤ y ^ (1 - θ₁) / 2)
    (hk3 : Real.log (2 * y) ≤ y ^ (1 - θ₁)) (hk3' : CA * Real.log (2 * y) ≤ y)
    (sR : ℝ) (hsR : (Qn : ℝ) ^ 2 ≤ 6 * sR)
    (Kc : ℝ) (hKc : Real.log Kc ≤ 3 * Real.log P.LL)
    (R : ℝ → ℝ) (Rk : ℕ → ℝ → ℝ) (hRk0 : ∀ k s, 0 ≤ Rk k s)
    (hmono : ∀ (k : ℕ) (s : ℝ), |s - (Real.log P.Q + 4 + k)| ≤ 1 / 2 → R s ≤ Rk k s)
    (hwin : ∀ k : ℕ, Real.log P.Q + 4 + k ≤ αp * P.LL + 1 →
      Integrable (fun s => bumpW (s - (Real.log P.Q + 4 + k)) * Rk k s) ∧
      (∫ s, bumpW (s - (Real.log P.Q + 4 + k)) * Rk k s)
        ≤ CS * NW * y ^ (-θ₁) * (P.T * (Real.log P.Q + 4 + k)))
    (hAS : ∀ s ∈ shellZone P αp, FfamZ P Qn s ≤ sR * (P.T / (2 * Real.pi)) * (P.LL + Real.log Kc + CA)
        + (Qn : ℝ) ^ 2 * (1 + CA * (Real.log P.LL / P.LL)) * R s
        + CA * (Real.log P.LL / P.LL) * sR * normA2 P s)
    (hlow : ∀ s ∈ shellZone P αp, P.T / (2 * Real.pi) * (s - 1) ≤ normA2 P s)
    (hint1 : IntegrableOn (fun s => P.gQ s * FfamZ P Qn s) (inZone P)ᶜ)
    (hint2 : IntegrableOn (fun s => P.gQ s * (normA2 P s * shellWt P αp s)) (inZone P)ᶜ) :
    (∫ s in (inZone P)ᶜ ∩ shellZone P αp, P.gQ s * FfamZ P Qn s)
      ≤ (1 + (1 + 22000000 * CS * NW + 2 * CA) * y ^ (-θ₁)) * sR
          * ∫ s in (inZone P)ᶜ ∩ shellZone P αp, P.gQ s * (normA2 P s * shellWt P αp s) := by
  have hy0 : 0 < y := by linarith
  have hLpos : 0 < P.LL := by linarith
  have hT : 0 < P.T := hP.T_pos
  obtain ⟨a, ha⟩ : ∃ a, Real.log P.Q + 4 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, αp * P.LL = b := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, y ^ (-θ₁) = t := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam, Real.log P.LL / P.LL = lam := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, P.T / (2 * Real.pi) = U := ⟨_, rfl⟩
  rw [ha] at hmono hwin
  rw [ht] at hwin ⊢
  rw [hlam, hU] at hAS
  rw [hU] at hlow
  have hU0 : 0 < U := by rw [← hU]; positivity
  have hUT : P.T = 2 * Real.pi * U := by rw [← hU]; field_simp
  have ht0 : 0 ≤ t := by rw [← ht]; exact Real.rpow_nonneg hy0.le _
  have hsR0 : 0 ≤ sR := by nlinarith [sq_nonneg (Qn : ℝ)]
  -- the zone
  have hZ' : (inZone P)ᶜ ∩ shellZone P αp = Set.Ioc a b := by
    rw [Set.inter_eq_right.mpr (shellZone_sub_outZone P αp (by rw [hy]; exact h16))]
    show Set.Ioc (Real.log P.Q + 4) (αp * P.LL) = _
    rw [ha, hb]
  have hZ : shellZone P αp = Set.Ioc a b := by
    show Set.Ioc (Real.log P.Q + 4) (αp * P.LL) = _
    rw [ha, hb]
  rw [hZ']
  rw [hZ] at hAS hlow
  have hsub : Set.Ioc a b ⊆ (inZone P)ᶜ := hZ' ▸ Set.inter_subset_left
  -- scalar facts
  have ha' : a = y + 4 := by rw [← ha, hy]
  have hab : a + 1 ≤ b := by rw [ha', ← hb]; nlinarith
  have hbL : b ≤ P.LB - 2 - P.LL / 9 := by rw [hLB, ← hb]; nlinarith
  have hb1 : b + 1 ≤ 2 * P.LL := by rw [← hb]; nlinarith
  have hLB2 : P.LB ≤ 2 * P.LL := by rw [hLB]; nlinarith
  have hLa : P.LL ≤ 2 * a := by rw [ha']; linarith
  have ha2 : 2 ≤ a := by rw [ha']; linarith
  have hlogL : Real.log P.LL ≤ Real.log (2 * y) := Real.log_le_log hLpos hLL2
  have hlogL0 : 0 ≤ Real.log P.LL := Real.log_nonneg (by linarith)
  have hlam0 : 0 ≤ lam := by rw [← hlam]; exact div_nonneg hlogL0 hLpos.le
  have hlamy : lam ≤ Real.log (2 * y) / y := by
    rw [← hlam]
    calc Real.log P.LL / P.LL ≤ Real.log (2 * y) / P.LL := div_le_div_of_nonneg_right hlogL hLpos.le
      _ ≤ Real.log (2 * y) / y := div_le_div_of_nonneg_left (by linarith) hy0 hyLL
  have hty : t * y = y ^ (1 - θ₁) := by
    rw [← ht, show (1 - θ₁) = -θ₁ + 1 by ring, Real.rpow_add hy0, Real.rpow_one]
  have hlamt : lam ≤ t := by
    refine le_trans hlamy ?_
    rw [div_le_iff₀ hy0]; linarith
  have hCAlam : CA * lam ≤ 1 := by
    have e : CA * (Real.log (2 * y) / y) ≤ 1 := by
      rw [mul_div_assoc', div_le_one hy0]; exact hk3'
    have := mul_le_mul_of_nonneg_left hlamy hCA
    linarith
  -- the majorant
  have hwin' : ∀ k ∈ Finset.range (⌈b - a⌉₊ + 1), Integrable (fun s => bumpW (s - (a + k)) * Rk k s) ∧
      (∫ s, bumpW (s - (a + k)) * Rk k s) ≤ CS * NW * t * (P.T * (b + 1)) := by
    intro k hk
    have hMle : (⌈b - a⌉₊ : ℝ) ≤ b - a + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    have hk' : (k : ℝ) ≤ ⌈b - a⌉₊ := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    obtain ⟨hi, hbd⟩ := hwin k (by rw [hb]; linarith)
    refine ⟨hi, le_trans hbd ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hT.le
  have hAS' : ∀ s ∈ Set.Ioc a b, FfamZ P Qn s
      ≤ sR * U * (P.LL + Real.log Kc + CA) + (Qn : ℝ) ^ 2 * (1 + CA * lam) * R s + CA * lam * sR * normA2 P s :=
    fun s hs => hAS s hs
  obtain ⟨IH, hIH0, hIHle, hF⟩ := K2_majorant P hP hw8 (by linarith) Qn a b (sR * U * (P.LL + Real.log Kc + CA))
    ((Qn : ℝ) ^ 2 * (1 + CA * lam)) (CA * lam * sR) (CS * NW * t * (P.T * (b + 1)))
    (mul_nonneg (sq_nonneg _) (by nlinarith [mul_nonneg hCA hlam0]))
    (by linarith) (by have : 0 ≤ b + 1 := by linarith
                      positivity) R Rk hRk0 hmono hwin' hAS' (hint1.mono_set hsub)
  have hwt : ∀ s ∈ Set.Ioc a b, shellWt P αp s = P.LL / s := by
    intro s hs
    unfold shellWt
    have h1 : ¬ s ≤ Real.log P.Q + 4 := not_le.mpr (by rw [ha]; exact hs.1)
    have h2 : s ≤ αp * P.LL := by rw [hb]; exact hs.2
    rw [if_neg h1, if_pos h2]
  obtain ⟨hJ1, hJ2, hI0⟩ := K2_Jbounds P hP hw8 hw1 αp a b U ha2 (by linarith) hb.symm hbL hwt hlow hU0
    (hint2.mono_set hsub)
  have hIH : IH ≤ 12 * (CS * NW * t * P.T) * P.LL * P.LL * (b - a) := by
    have hMle : (⌈b - a⌉₊ : ℝ) + 1 ≤ 3 * (b - a) := by
      have := (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ b - a)).le
      linarith
    refine le_trans hIHle ?_
    have hX : 0 ≤ CS * NW * t * P.T := by positivity
    calc P.LB * (((⌈b - a⌉₊ : ℝ) + 1) * (CS * NW * t * (P.T * (b + 1))))
        = P.LB * (((⌈b - a⌉₊ : ℝ) + 1) * ((CS * NW * t * P.T) * (b + 1))) := by ring
      _ ≤ (2 * P.LL) * ((3 * (b - a)) * ((CS * NW * t * P.T) * (2 * P.LL))) := by
          have : 0 ≤ P.LB := by linarith
          have : 0 ≤ b + 1 := by linarith
          have : 0 ≤ 3 * (b - a) := by linarith
          gcongr
      _ = 12 * (CS * NW * t * P.T) * P.LL * P.LL * (b - a) := by ring
  have hI20 : 0 ≤ ∫ s in Set.Ioc a b, P.gQ s * normA2 P s :=
    setIntegral_nonneg measurableSet_Ioc fun s _ => mul_nonneg (hP.gQ_nonneg hw8 s)
      (Finset.sum_nonneg fun n _ => by positivity)
  exact K2_arith _ _ _ IH _ sR U P.LL y a b t αp P.T Kc CA CS NW lam ((Qn : ℝ) ^ 2) θ₁ hy0 hyLL hLL2 ha2 hLa
    hab (by linarith) hU0 hUT ht0 hty hsR (sq_nonneg _) hCA hCS hNW hlam0 hlamt hCAlam
    (by linarith) hk2 hF hIH0 hIH hJ1 hJ2 hI0 hI20

end K2c
end ShellK
end ZetaShell
