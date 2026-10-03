/-
Node S4 (L7_10): **Theorem S, the elementary terms**: the prime-power term of Lemma 5c(1) (`T²KR₁/Q`) and the
principal-arc term `2(log K + 1.4708)U` of Lemma ⋆ (`≪ (log K)/s₀` relative, thm:shell-S proof, last lines):
`(log K + 2)(T²KR₁/Q + T) ≤ C (log Q)^{−θ} T s₀` on Theorem S's range, for every `θ < 1`.
Proof: `log K ≤ B log log Q`, `s₀ ≥ log Q`, `R₁ ≤ e Q^{α′−1}(log Q)^{6+B}`, `α′ < 2`. Pure asymptotic arithmetic.
Dependencies: none. Difficulty: E.
-/
import ZetaShell.ShellS.L10_Defs

noncomputable section

namespace ZetaShell
namespace ShellS

theorem S4_elementary (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 2) (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0)
    (B θ : ℝ) (hB : 1 ≤ B) (hθ : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      (Real.log K + 2) * (twin Qn r0 ε0 ^ 2 * K * (R1S Qn ε s₀ : ℝ) / Qn + twin Qn r0 ε0)
        ≤ C * Real.log Qn ^ (-θ) * (twin Qn r0 ε0 * s₀) := by
  refine ⟨1, zero_le_one, ?_⟩
  have hℓ : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : 0 < 1 - θ := by linarith
  have hB0 : 0 < B := by linarith
  have E1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have E2a : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ (1 / (8 * B)) * ‖x ^ (1 - θ)‖ :=
    (isLittleO_log_rpow_atTop hr).bound (by positivity)
  have E2b : ∀ᶠ x : ℝ in Filter.atTop, 8 ≤ x ^ (1 - θ) :=
    (tendsto_rpow_atTop hr).eventually (Filter.eventually_ge_atTop 8)
  have E3 : ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (2 * (r0 + ε0) + 2 * B + 6) * Real.exp (-(2 - αp) * x) ≤ Real.exp (-1) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by linarith)).eventually
      (ge_mem_nhds (Real.exp_pos _))
  filter_upwards [hℓ.eventually E1, hℓ.eventually E2a, hℓ.eventually E2b, hℓ.eventually E3,
    Filter.eventually_ge_atTop 1] with Qn e1 e2a e2b e3 hQn1
  intro K ε s₀ hR
  set ℓ := Real.log (Qn : ℝ) with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have hQpos : (0 : ℝ) < Qn := by exact_mod_cast hQn1
  have hQexp : (Qn : ℝ) = Real.exp ℓ := (Real.exp_log hQpos).symm
  have hT : twin (Qn : ℝ) r0 ε0 = ℓ ^ (r0 + ε0) := rfl
  set T := twin (Qn : ℝ) r0 ε0 with hTdef
  have hT1 : 1 ≤ T := by rw [hT]; exact Real.one_le_rpow e1 (by linarith)
  have hK0 : 0 < K := by linarith [hR.K_ge]
  have hlogK : Real.log K ≤ B * Real.log ℓ := by
    have h := Real.log_le_log hK0 hR.K_le
    rwa [Real.log_rpow hℓ0] at h
  have hε0' : 0 < ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hℓ0 _) hR.eps_ge
  have hinvε : 1 / ε ≤ ℓ ^ B := by
    rw [div_le_iff₀ hε0']
    have h1 : ℓ ^ B * ℓ ^ (-B) = 1 := by
      rw [Real.rpow_neg hℓ0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hℓ0 _).ne']
    have h2 := mul_le_mul_of_nonneg_left hR.eps_ge (Real.rpow_pos_of_pos hℓ0 B).le
    linarith
  -- the prime-power term is at most 1
  have hR1 : (R1S Qn ε s₀ : ℝ) ≤ Real.exp (s₀ + 1) * ℓ ^ 6 / (ε * Qn) := by
    unfold R1S; exact Nat.floor_le (by positivity)
  have hprod : T ^ 2 * ℓ ^ B * ℓ ^ 6 * ℓ ^ B = ℓ ^ (2 * (r0 + ε0) + 2 * B + 6) := by
    rw [hT, show (ℓ ^ (r0 + ε0)) ^ 2 = ℓ ^ (r0 + ε0) * ℓ ^ (r0 + ε0) by ring,
      show ℓ ^ 6 = ℓ ^ ((6 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_add hℓ0, ← Real.rpow_add hℓ0,
      ← Real.rpow_add hℓ0, ← Real.rpow_add hℓ0]
    congr 1; push_cast; ring
  have hexp : Real.exp (s₀ + 1) / ((Qn : ℝ) * Qn) ≤ Real.exp 1 * Real.exp (-(2 - αp) * ℓ) := by
    rw [hQexp, ← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hR.s_le]
  have hP : T ^ 2 * K * (R1S Qn ε s₀ : ℝ) / Qn ≤ 1 := by
    have hTK : 0 ≤ T ^ 2 * K / Qn := by positivity
    calc T ^ 2 * K * (R1S Qn ε s₀ : ℝ) / Qn = (T ^ 2 * K / Qn) * (R1S Qn ε s₀ : ℝ) := by ring
      _ ≤ (T ^ 2 * K / Qn) * (Real.exp (s₀ + 1) * ℓ ^ 6 / (ε * Qn)) := mul_le_mul_of_nonneg_left hR1 hTK
      _ = (T ^ 2 * K * ℓ ^ 6) * (1 / ε) * (Real.exp (s₀ + 1) / ((Qn : ℝ) * Qn)) := by
          field_simp
      _ ≤ (T ^ 2 * ℓ ^ B * ℓ ^ 6) * ℓ ^ B * (Real.exp 1 * Real.exp (-(2 - αp) * ℓ)) := by
          have hA : T ^ 2 * K * ℓ ^ 6 ≤ T ^ 2 * ℓ ^ B * ℓ ^ 6 := by
            have := hR.K_le
            have h6 : 0 ≤ T ^ 2 * ℓ ^ 6 := by positivity
            nlinarith
          have hA0 : 0 ≤ T ^ 2 * K * ℓ ^ 6 := by positivity
          have hE0 : 0 ≤ Real.exp (s₀ + 1) / ((Qn : ℝ) * Qn) := by positivity
          calc (T ^ 2 * K * ℓ ^ 6) * (1 / ε) * (Real.exp (s₀ + 1) / ((Qn : ℝ) * Qn))
              ≤ (T ^ 2 * ℓ ^ B * ℓ ^ 6) * ℓ ^ B * (Real.exp (s₀ + 1) / ((Qn : ℝ) * Qn)) := by
                apply mul_le_mul_of_nonneg_right _ hE0
                exact mul_le_mul hA hinvε (by positivity) (by positivity)
            _ ≤ (T ^ 2 * ℓ ^ B * ℓ ^ 6) * ℓ ^ B * (Real.exp 1 * Real.exp (-(2 - αp) * ℓ)) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp 1 * (ℓ ^ (2 * (r0 + ε0) + 2 * B + 6) * Real.exp (-(2 - αp) * ℓ)) := by
          rw [← hprod]; ring
      _ ≤ Real.exp 1 * Real.exp (-1) := mul_le_mul_of_nonneg_left e3 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  -- the log factor
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg e1
  have habs : Real.log ℓ ≤ (1 / (8 * B)) * ℓ ^ (1 - θ) := by
    have h := e2a
    rw [Real.norm_of_nonneg hlogℓ, Real.norm_of_nonneg (Real.rpow_nonneg hℓ0.le _)] at h
    exact h
  have hL2 : 2 * (Real.log K + 2) ≤ ℓ ^ (1 - θ) := by
    have h8 : B * (1 / (8 * B)) = 1 / 8 := by field_simp
    nlinarith [hlogK, habs, e2b, h8]
  have hLK0 : 0 ≤ Real.log K + 2 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ K by linarith [hR.K_ge]); linarith
  have hsplit : ℓ ^ (1 - θ) = ℓ ^ (-θ) * ℓ := by
    rw [show (1 - θ) = -θ + 1 by ring, Real.rpow_add hℓ0, Real.rpow_one]
  have hs₀ : ℓ ≤ s₀ := by linarith [hR.s_ge]
  calc (Real.log K + 2) * (T ^ 2 * K * (R1S Qn ε s₀ : ℝ) / Qn + T)
      ≤ (Real.log K + 2) * (2 * T) := by
        apply mul_le_mul_of_nonneg_left _ hLK0; linarith
    _ = (2 * (Real.log K + 2)) * T := by ring
    _ ≤ ℓ ^ (1 - θ) * T := mul_le_mul_of_nonneg_right hL2 (by linarith)
    _ = ℓ ^ (-θ) * ℓ * T := by rw [hsplit]
    _ ≤ ℓ ^ (-θ) * s₀ * T := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hs₀ (Real.rpow_nonneg hℓ0.le _)
    _ = 1 * ℓ ^ (-θ) * (T * s₀) := by ring

end ShellS
end ZetaShell
