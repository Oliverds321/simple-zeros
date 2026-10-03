/-
Node K2 (L7_10): **Theorem K on the Shell zone `(log Q + 4, α′ℒ]`** (proof of thm:shell-K, "On `[log Q+4, α′ℒ]`" and
"Transfer from unit windows to `g`"): `∫_{zone} g F ≤ (1 + c(log Q)^{−θ})|𝔉_Q| ∫_{zone} g ‖a‖² ℒ/s`, every `θ < θ(α′)`.
Derivation (L7_10's plan): (1) AS (`AS_pointwise`, λ = 1.91, α″ ∈ (α′, 5/3)) bridged to ZetaQ's objects;
(2) `U(ℒ + log K + C) ≤ ‖a‖²(ℒ/s)(1 + C log ℒ/ℒ)` from `‖a‖² ≥ U(s − C)` (PNT medium) and `log K ≪ log ℒ`;
(3) `∫_{zone} g Ring ≤ c (log Q)^{−θ} ∫_{zone} g T s` from Theorem S (`shell_S`, `K = ℒ(log ℒ)²`, `ε = 1/ℒ`, `B = 2`,
windows at `s₀ ≤ α″ log Q`), `ringMass_mono`/`R1S_mono`; (4) `T s ≪ ‖a‖²ℒ/s`; (5) `Q²/|𝔉_Q| ≤ C`, `log ℒ/ℒ ≤ (log Q)^{−θ}`.

DERIVED (L7_10c, 3 Oct 2026; statement unchanged, moved from `Skeleton/`): `K2c.K2_point` at each design point, with
* AS = `ShellS.AS_pointwise_corr` (= `AS_pointwise` + `αpp < lam`; module `ShellS.L10c_ASMain`, proved) at
  `lam = 191/100`, `αpp = α″ < 5/3`, `κ = 1`, `Ξ = K2c.bumpW`, `c = 1/2`, through the bridges
  `K2c.bridge_F`, `bridge_size`, `bridge_l2`, `LcS_eq` (all `rfl`-level);
* Theorem S = `ShellS.shell_S` at `α″` (`K2c.exists_alpha2`: `θ₁ = max(θ, θ(α′)/2) < θ(α″)`), `κ = 1`, `Ξ = bumpW`,
  `A = 2`, `B = 2`, `K = ℒ(log ℒ)²`, `ε = 1/ℒ`, windows `W = bumpW` at the centres `log Q + 4 + k`;
  the pointwise ring `RingS … (s−1) s` is dominated by `Σ_k bumpW(s − s_k)·RingS … s_k s` (`R1S_mono`,
  `ringMass_mono`), whose summands are integrable by Theorem S's own conclusion (so KT's continuity is not needed);
* `‖a(s)‖² ≥ U(s − 1)`: `F1c.normA2_lower` (L7_3c); `Q² ≤ 6|𝔉_Q|`: `sizeR_qle_lower'`; integrability: `K_int`.
The rate: `c = 1 + 22·10⁶·C_S‖W₀‖_{C²} + 2C_A`, at `θ₁ ≥ θ`.
-/
import ZetaShell.ShellK.L10c_K2Aux
import ZetaShell.ShellS.L10_S
import ZetaShell.Skeleton.L10_AS
import ZetaShell.ShellS.L10c_ASMain
import ZetaShell.ShellK.LF_K3bP
import ZetaShell.ShellK.L10_KInt

noncomputable section

namespace ZetaShell
namespace ShellK

open ZetaQ ZetaShell.ShellS ZetaShell.PropZ

set_option maxHeartbeats 1000000 in
theorem K2_shellZone (hD : ZeroDensityInput) (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r ε θ : ℝ) (hr : 3 ≤ r)
    (hε : 0 < ε) (hθ : θ < thetaD1p αp) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ P : ParamsQ, Design.ShellDesignM S53L75 r ε (Qn : ℝ) P →
      (∫ s in (inZone P)ᶜ ∩ shellZone P αp, P.gQ s * FfamZ P Qn s)
        ≤ (1 + c * Real.log Qn ^ (-θ)) * Family.qle.sizeR Qn
            * ∫ s in (inZone P)ᶜ ∩ shellZone P αp, P.gQ s * (normA2 P s * shellWt P αp s) := by
  have hre : 0 < r + ε := by linarith
  -- the rate `θ₁`
  have htp : 0 < thetaD1p αp := by
    have h1 : 4 / αp < 4 := by rw [div_lt_iff₀ (by linarith)]; linarith
    have h2 : 2 < 4 / αp := by rw [lt_div_iff₀ (by linarith)]; linarith
    exact lt_min one_pos (div_pos (by linarith) (by linarith))
  set θ₁ := max θ (thetaD1p αp / 2) with hθ₁def
  have hθ₁ : θ₁ < thetaD1p αp := max_lt hθ (by linarith)
  have hθ₁0 : 0 < θ₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hθ₁1 : θ₁ < 1 := lt_of_lt_of_le hθ₁ (thetaD1p_le_one αp)
  have hθθ₁ : θ ≤ θ₁ := le_max_left _ _
  obtain ⟨α₂, hαα, hα₂, hθα₂⟩ := K2c.exists_alpha2 αp θ₁ hα1 hα2 hθ₁
  -- AS and S
  obtain ⟨CA, hCA, hAS⟩ := AS_pointwise_corr (191 / 100) (by norm_num) (by norm_num) α₂ (by linarith) 1 one_pos
    le_rfl K2c.bumpW K2c.bumpW_near (1 / 2) (by norm_num) (fun z hz => K2c.bumpW_eq_one hz) r ε hr hε (by linarith)
  obtain ⟨CS, hCS, hS⟩ := shell_S hD α₂ (by linarith) hα₂ 1 one_pos le_rfl K2c.bumpW K2c.bumpW_near 2 le_rfl
    r ε hr hε 2 θ₁ (by norm_num) hθα₂
  have hNW : 0 ≤ normCA K2c.bumpW 2 := normCA_nonneg' _ _
  refine ⟨1 + 22000000 * CS * normCA K2c.bumpW 2 + 2 * CA, by positivity, ?_⟩
  filter_upwards [K2c.design_facts r ε hr hε, K2c.scalars_K2 αp α₂ r ε CA θ₁ hα1 hαα hre hθ₁1 hCA, hAS, hS,
    F1c.normA2_lower r ε hr hε, K_int αp hα1 hα2 r ε hr hε, Filter.eventually_ge_atTop 1]
    with Qn hfac hsc hASQ hSQ hlowQ hintQ hQn1
  intro P hdes
  obtain ⟨hP, hw8, hw1, hQ, hT, hlam, hLB, hyLL, hLL2, hLLu, hy1⟩ := hfac P hdes
  obtain ⟨⟨h16, h5, hll⟩, hk2, hk3, hk3', hk4, hk5⟩ := hsc
  obtain ⟨hint1, hint2, hg0, hw0, -⟩ := hintQ P hdes
  have hy0 : 0 < Real.log (Qn : ℝ) := by linarith
  have hTw : P.T = twin (Qn : ℝ) r ε := hT
  have hLpos : 0 < P.LL := by linarith
  have hQpos : (0 : ℝ) < (Qn : ℝ) := by exact_mod_cast hQn1
  have hlogQ : Real.log P.Q = Real.log (Qn : ℝ) := by rw [hQ]
  -- bridges
  have hLc : LcS (Qn : ℝ) (twin (Qn : ℝ) r ε) = P.LL := K2c.LcS_eq P Qn _ hQ hTw
  have hKs : Kstd (Qn : ℝ) (twin (Qn : ℝ) r ε) = P.LL * Real.log P.LL ^ 2 := by unfold Kstd; rw [hLc]
  -- `|𝔉_Q| ≥ Q²/6`
  have hsR : ((Qn : ℝ)) ^ 2 ≤ 6 * Family.qle.sizeR Qn := by
    have h1 := sizeR_qle_lower' Qn hQn1
    have h2 := mul_le_mul_of_nonneg_left hk5 hQpos.le
    have e1 : (Qn : ℝ) * (6 * (1 + Real.log Qn) ^ 2) = 6 * (Qn : ℝ) * (1 + Real.log Qn) ^ 2 := by ring
    have e2 : (Qn : ℝ) * ((18 / Real.pi ^ 4 - 1 / 6) * Qn) = 18 / Real.pi ^ 4 * (Qn : ℝ) ^ 2 - (Qn : ℝ) ^ 2 / 6 := by
      ring
    linarith
  -- `log K ≤ 3 log ℒ`
  have hlogL1 : 1 ≤ Real.log P.LL := by
    rw [Real.le_log_iff_exp_le hLpos]; linarith [Real.exp_one_lt_d9]
  have hKc : Real.log (P.LL * Real.log P.LL ^ 2) ≤ 3 * Real.log P.LL := by
    rw [Real.log_mul hLpos.ne' (by positivity), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log P.LL)
    push_cast; linarith
  -- the rings
  set Kc := P.LL * Real.log P.LL ^ 2 with hKcdef
  set R : ℝ → ℝ := fun s => RingS Qn P.T 1 K2c.bumpW Kc (1 / P.LL) (s - 1) s with hRdef
  set Rk : ℕ → ℝ → ℝ := fun k s => RingS Qn P.T 1 K2c.bumpW Kc (1 / P.LL) (Real.log P.Q + 4 + k) s with hRkdef
  have hRk0 : ∀ k s, 0 ≤ Rk k s := fun k s => RingS_nonneg _ _ _ _ _ _ _ _
  have hmono : ∀ (k : ℕ) (s : ℝ), |s - (Real.log P.Q + 4 + k)| ≤ 1 / 2 → R s ≤ Rk k s := by
    intro k s hks
    have h := (abs_le.mp hks).2
    show RingS Qn P.T 1 K2c.bumpW Kc (1 / P.LL) (s - 1) s
      ≤ RingS Qn P.T 1 K2c.bumpW Kc (1 / P.LL) (Real.log P.Q + 4 + k) s
    unfold RingS
    exact ringMass_mono _ _ _ _ (R1S_mono _ _ hQpos (by positivity) (by linarith))
  have hwin : ∀ k : ℕ, Real.log P.Q + 4 + k ≤ αp * P.LL + 1 →
      MeasureTheory.Integrable (fun s => K2c.bumpW (s - (Real.log P.Q + 4 + k)) * Rk k s) ∧
      (∫ s, K2c.bumpW (s - (Real.log P.Q + 4 + k)) * Rk k s)
        ≤ CS * normCA K2c.bumpW 2 * Real.log (Qn : ℝ) ^ (-θ₁) * (P.T * (Real.log P.Q + 4 + k)) := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hSR : SRange α₂ 2 Qn Kc (1 / P.LL) (Real.log P.Q + 4 + k) := by
      have hlog2L : Real.log P.LL ≤ Real.log (2 * Real.log Qn) := Real.log_le_log hLpos hLL2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hl2 : 1 ≤ Real.log P.LL ^ 2 := one_le_pow₀ hlogL1
        have : P.LL * 1 ≤ P.LL * Real.log P.LL ^ 2 := mul_le_mul_of_nonneg_left hl2 hLpos.le
        rw [hKcdef]; linarith
      · have hsq : Real.log (Qn : ℝ) ^ (2 : ℝ) = Real.log (Qn : ℝ) ^ 2 := by norm_cast
        rw [hsq, hKcdef]
        have e1 : Real.log P.LL ^ 2 ≤ Real.log (2 * Real.log Qn) ^ 2 := by
          exact pow_le_pow_left₀ (by linarith) hlog2L 2
        calc P.LL * Real.log P.LL ^ 2 ≤ (2 * Real.log Qn) * Real.log (2 * Real.log Qn) ^ 2 := by
              gcongr
          _ = Real.log Qn * (2 * Real.log (2 * Real.log Qn) ^ 2) := by ring
          _ ≤ Real.log Qn * Real.log Qn := mul_le_mul_of_nonneg_left hk4 hy0.le
          _ = Real.log Qn ^ 2 := by ring
      · have hsq : Real.log (Qn : ℝ) ^ (-2 : ℝ) = 1 / Real.log (Qn : ℝ) ^ 2 := by
          rw [Real.rpow_neg hy0.le, one_div]; norm_cast
        rw [hsq]
        apply one_div_le_one_div_of_le hLpos
        have : 2 * Real.log (Qn : ℝ) ≤ Real.log Qn * Real.log Qn :=
          mul_le_mul_of_nonneg_right (by linarith) hy0.le
        rw [sq]; linarith
      · rw [div_le_one hLpos]; linarith
      · rw [hlogQ]; linarith
      · have : αp * P.LL ≤ αp * (Real.log Qn + (r + ε) * Real.log (Real.log Qn)) :=
          mul_le_mul_of_nonneg_left hLLu (by linarith)
        have e : αp * (Real.log Qn + (r + ε) * Real.log (Real.log Qn))
            = αp * Real.log Qn + αp * (r + ε) * Real.log (Real.log Qn) := by ring
        have e2 : (α₂ - αp) * Real.log Qn = α₂ * Real.log Qn - αp * Real.log Qn := by ring
        linarith
    obtain ⟨hi, hbd⟩ := hSQ Kc (1 / P.LL) (Real.log P.Q + 4 + k) hSR K2c.bumpW K2c.bumpW_avg
    rw [← hTw] at hi hbd
    exact ⟨hi, hbd⟩
  -- AS in ZetaQ form
  have hASZ : ∀ s ∈ shellZone P αp, FfamZ P Qn s
      ≤ Family.qle.sizeR Qn * (P.T / (2 * Real.pi)) * (P.LL + Real.log Kc + CA)
        + (Qn : ℝ) ^ 2 * (1 + CA * (Real.log P.LL / P.LL)) * R s
        + CA * (Real.log P.LL / P.LL) * Family.qle.sizeR Qn * normA2 P s := by
    intro s hs
    have h1 : Real.log Qn + 4 ≤ s := by rw [← hlogQ]; exact hs.1.le
    have h2 : s ≤ α₂ * Real.log Qn := by
      have := hs.2
      have : αp * P.LL ≤ αp * (Real.log Qn + (r + ε) * Real.log (Real.log Qn)) :=
        mul_le_mul_of_nonneg_left hLLu (by linarith)
      have e : αp * (Real.log Qn + (r + ε) * Real.log (Real.log Qn))
          = αp * Real.log Qn + αp * (r + ε) * Real.log (Real.log Qn) := by ring
      have e2 : (α₂ - αp) * Real.log Qn = α₂ * Real.log Qn - αp * Real.log Qn := by ring
      linarith
    have h := hASQ s h1 h2
    rw [hLc, hKs, K2c.bridge_F P Qn _ hQ hTw hlam, K2c.bridge_size, K2c.bridge_l2 P Qn _ hQ hTw hlam,
      ← hTw] at h
    exact h
  have hlowZ : ∀ s ∈ shellZone P αp, P.T / (2 * Real.pi) * (s - 1) ≤ normA2 P s := by
    intro s hs
    have hs1 := hs.1
    have hs2 := hs.2
    refine hlowQ P hdes s ?_ ?_
    · have h2 : Real.log (Qn : ℝ) ≤ Real.log Qn ^ 2 := by
        have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ Real.log Qn) hy0.le
        rw [sq]; linarith
      have : Real.sqrt (Real.log Qn) ≤ Real.log Qn :=
        (Real.sqrt_le_sqrt h2).trans_eq (Real.sqrt_sq hy0.le)
      rw [hlogQ] at hs1; linarith
    · have : αp * P.LL ≤ 5 / 3 * P.LL := mul_le_mul_of_nonneg_right hα2.le hLpos.le
      rw [hLB]; linarith
  have key := K2c.K2_point P hP hw8 hw1 Qn αp hα1 hα2 hLB (Real.log Qn) hlogQ hyLL hLL2 h16 h5 CA CS
    (normCA K2c.bumpW 2) θ₁ hCA hCS hNW hk2 hk3 hk3' (Family.qle.sizeR Qn) hsR Kc hKc R Rk hRk0 hmono hwin
    hASZ hlowZ hint1 hint2
  -- from `θ₁` to `θ`
  have hJ0 : 0 ≤ ∫ s in (inZone P)ᶜ ∩ shellZone P αp, P.gQ s * (normA2 P s * shellWt P αp s) :=
    MeasureTheory.setIntegral_nonneg ((measurableSet_outZone P).inter measurableSet_Ioc)
      fun s hs => mul_nonneg (hg0 s) (hw0 s hs.1)
  have hsR0 : 0 ≤ Family.qle.sizeR Qn := by nlinarith [sq_nonneg (Qn : ℝ)]
  have hrate : Real.log (Qn : ℝ) ^ (-θ₁) ≤ Real.log (Qn : ℝ) ^ (-θ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  refine le_trans key ?_
  have hc0 : 0 ≤ 1 + 22000000 * CS * normCA K2c.bumpW 2 + 2 * CA := by positivity
  gcongr

end ShellK
end ZetaShell
