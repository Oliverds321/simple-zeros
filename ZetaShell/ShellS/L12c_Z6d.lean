/-
L7_12c (3 Oct 2026): node Z6d with the corrected near clause, **`Z6d_counts_corr`** (statement-change request
SCR-Z6d, report `lean_board/reports/L7_12_zero_side.md`, Round 3, R3.3): the near clause carries `5 X₀ ≤ s₀`
(the paper proves it, lem:shell-6d "(mid/near, σ ≥ σ_LF)", only in the (LF) range `x ≤ (1 − σ_LF)s₀ = s₀/5`);
the rest clause is the frozen one, for every `X₀ ≥ 0`.
Proof (lem:shell-6d): `ZeroDensityInput` on the `O(1/ε′)` blocks of Lemma 6c (`L12c_Zones`), `𝒵 = N₀^{δ+o(1)}`,
`δ = 2 − 2/α′` (`L12c_Zsize`), unit layers in `x` (`L12c_Bounds`). Exponents: `ε₁ = min(ε″, 4/5 − δ)`,
`t = ε₁/20` (`ε′ = ε_J = η = t`), `κ₁ = 2δ + ε₁/2` (the (LF) count exponent), `κ₂ = 2δ + ε₁ ≤ κ′`,
`δ′ = δ + 3t < 4/5`, `m′ = min(2 − 5δ′/2, 1)`, `ε_M = m′/10`, `ε_L = 1/8`, `c = m′/20`.
-/
import ZetaShell.ShellS.L12c_Bounds
import ZetaShell.ShellS.L12c_Zsize

noncomputable section
open Complex
open scoped ENNReal

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- `(𝒵 N₀^{2t})^a ≤ e^{a(δ+3t)s₀}` from `log 𝒵 ≤ (δ+t)s₀`. -/
lemma L12c_Zp_rpow (Z s₀ δ t a : ℝ) (hZ : 0 < Z) (hlog : Real.log Z ≤ (δ + t) * s₀) (ha : 0 ≤ a) :
    (Z * Real.exp s₀ ^ (2 * t)) ^ a ≤ Real.exp (a * (δ + 3 * t) * s₀) := by
  have hE : 0 < Real.exp s₀ ^ (2 * t) := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hZ' : 0 < Z * Real.exp s₀ ^ (2 * t) := mul_pos hZ hE
  have hlog' : Real.log (Z * Real.exp s₀ ^ (2 * t)) ≤ (δ + 3 * t) * s₀ := by
    rw [Real.log_mul hZ.ne' hE.ne', Real.log_rpow (Real.exp_pos _), Real.log_exp]
    linarith
  rw [Real.rpow_def_of_pos hZ']
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right hlog' ha
  linarith

/-- **the three zone counts, eventually on `SRange`** (with `T = (log Q)^{r₀+ε₀}`). -/
theorem L12c_counts_ev (hD : ZeroDensityInput) (αp : ℝ) (hα1 : 1 < αp) (r0 ε0 : ℝ) (hr0 : 3 ≤ r0)
    (hε0 : 0 < ε0) (B : ℝ) (hB : 1 ≤ B) (δ : ℝ) (hδ : δ = 2 - 2 / αp) (t εM εL : ℝ) (ht : 0 < t)
    (ht1 : t ≤ 1) (hεM : 0 < εM) (hεM1 : εM ≤ 1) (hεL : 0 < εL) (hεL1 : εL ≤ 1) :
    ∃ CA CB CL : ℝ, 0 ≤ CA ∧ 0 ≤ CB ∧ 0 ≤ CL ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ,
      SRange αp B Qn K ε s₀ → ∀ k : ℕ, 3 ≤ k →
      0 < s₀ ∧ 0 ≤ K ∧
      (∀ x : ℝ, 0 ≤ x → 5 * x ≤ s₀ → L12cW Qn (twin Qn r0 ε0) K ε s₀ k (fun ρ => xRho s₀ ρ ≤ x)
        ≤ ENNReal.ofReal (CA * Real.exp ((2 + t) * (δ + 3 * t) * x))) ∧
      (∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 4 / 5 → L12cW Qn (twin Qn r0 ε0) K ε s₀ k (fun ρ => σ ≤ ρ.re)
        ≤ ENNReal.ofReal (CB * Real.exp ((3 * (1 - σ) / (2 - σ) + εM) * (δ + 3 * t) * s₀))) ∧
      L12cW Qn (twin Qn r0 ε0) K ε s₀ k (fun _ => True)
        ≤ ENNReal.ofReal (CL * Real.exp ((1 + εL) * (δ + 3 * t) * s₀)) := by
  subst hδ
  obtain ⟨CJ, hCJ, hJ⟩ := L12c_zone_LF hD t ht ht1
  obtain ⟨CM, hCM, hM⟩ := L12c_zone_bulk hD εM hεM hεM1
  obtain ⟨CL₀, hCL₀, hL₀⟩ := L12c_zone_all εL hεL hεL1
  have hI0 : (0 : ℝ) ≤ (⌈1 / t⌉₊ : ℝ) + 1 := by positivity
  refine ⟨((⌈1 / t⌉₊ : ℝ) + 1) * (9 * CJ), ((⌈1 / t⌉₊ : ℝ) + 1) * (9 * CM), ((⌈1 / t⌉₊ : ℝ) + 1) * (9 * CL₀),
    by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [L12c_Zsize_ev αp hα1 r0 ε0 hr0 hε0 B hB t ht, L12_log_eventually_ge 3] with Qn hZ hL
  intro K ε s₀ hR k hk
  obtain ⟨hQ, hT1, hR1, hR1N, hZpos, hZlog⟩ := hZ K ε s₀ hR
  have hs : 0 < s₀ := by have := hR.s_ge; linarith
  have hK : 0 ≤ K := by have := hR.K_ge; linarith
  refine ⟨hs, hK, ?_, ?_, ?_⟩
  · intro x hx h5
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 - x / s₀ := ⟨_, rfl⟩
    have hxs : x / s₀ ≤ 1 / 5 := by rw [div_le_iff₀ hs]; linarith
    have hx0 : 0 ≤ x / s₀ := div_nonneg hx hs.le
    have hσ1 : 4 / 5 ≤ σ := by rw [hσ]; linarith
    have hσ2 : σ ≤ 1 := by rw [hσ]; linarith
    have hmono := L12cW_mono Qn (twin Qn r0 ε0) K ε s₀ k hK (fun ρ => xRho s₀ ρ ≤ x)
      (fun ρ => σ ≤ ρ.re) (by
        intro ρ _ _ h
        have h' : (1 - ρ.re) * s₀ ≤ x := h
        have : 1 - ρ.re ≤ x / s₀ := by rw [le_div_iff₀ hs]; exact h'
        show σ ≤ ρ.re
        rw [hσ]; linarith)
    refine hmono.trans ((hJ Qn (twin Qn r0 ε0) K ε s₀ t k hk hT1 hK hQ hs hR1 hR1N ht ht1 σ hσ1 hσ2).trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have h1σ : 1 - σ = x / s₀ := by rw [hσ]; ring
    have ha : 0 ≤ (2 + t) * (1 - σ) := by rw [h1σ]; positivity
    have hrp := L12c_Zp_rpow _ s₀ (2 - 2 / αp) t ((2 + t) * (1 - σ)) hZpos hZlog ha
    have he : (2 + t) * (1 - σ) * (2 - 2 / αp + 3 * t) * s₀ = (2 + t) * (2 - 2 / αp + 3 * t) * x := by
      rw [h1σ]
      have hxs' : x / s₀ * s₀ = x := div_mul_cancel₀ x hs.ne'
      calc (2 + t) * (x / s₀) * (2 - 2 / αp + 3 * t) * s₀ = (2 + t) * (2 - 2 / αp + 3 * t) * (x / s₀ * s₀) := by
            ring
        _ = (2 + t) * (2 - 2 / αp + 3 * t) * x := by rw [hxs']
    rw [he] at hrp
    calc _ ≤ ((⌈1 / t⌉₊ : ℝ) + 1) * (9 * CJ * Real.exp ((2 + t) * (2 - 2 / αp + 3 * t) * x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp (by linarith)) hI0
      _ = _ := by ring
  · intro σ hσ1 hσ2
    have ha : 0 ≤ 3 * (1 - σ) / (2 - σ) + εM := by
      have : 0 ≤ 3 * (1 - σ) / (2 - σ) := div_nonneg (by linarith) (by linarith)
      linarith
    have hrp := L12c_Zp_rpow _ s₀ (2 - 2 / αp) t _ hZpos hZlog ha
    refine (hM Qn (twin Qn r0 ε0) K ε s₀ t k hk hT1 hK hQ hs hR1 hR1N ht ht1 σ hσ1 hσ2).trans ?_
    apply ENNReal.ofReal_le_ofReal
    calc _ ≤ ((⌈1 / t⌉₊ : ℝ) + 1) * (9 * CM * Real.exp ((3 * (1 - σ) / (2 - σ) + εM) *
            (2 - 2 / αp + 3 * t) * s₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp (by linarith)) hI0
      _ = _ := by ring
  · have hrp := L12c_Zp_rpow _ s₀ (2 - 2 / αp) t (1 + εL) hZpos hZlog (by linarith)
    refine (hL₀ Qn (twin Qn r0 ε0) K ε s₀ t k hk hT1 hK hQ hs hR1 hR1N ht ht1).trans ?_
    apply ENNReal.ofReal_le_ofReal
    calc _ ≤ ((⌈1 / t⌉₊ : ℝ) + 1) * (9 * CL₀ * Real.exp ((1 + εL) * (2 - 2 / αp + 3 * t) * s₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp (by linarith)) hI0
      _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **Node Z6d, corrected (SCR-Z6d)**: Lemma 6d, counts, with the near clause on `5 X₀ ≤ s₀`. -/
theorem Z6d_counts_corr (hD : ZeroDensityInput) (αp : ℝ) (hα1 : 1 < αp) (hα2 : αp < 5 / 3) (r0 ε0 : ℝ)
    (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (B : ℝ) (hB : 1 ≤ B) (ε'' : ℝ) (hε'' : 0 < ε'') (k : ℕ) (hk : 3 ≤ k) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      ∀ X₀ : ℝ, 0 ≤ X₀ →
        s₀ * restSq Qn (twin Qn r0 ε0) K ε s₀ k X₀
            ≤ C * (Real.exp s₀ ^ (-c) + s₀ * Real.exp (-((2 - kappaD1p αp ε'') * X₀))) ∧
        (5 * X₀ ≤ s₀ → nearSum Qn (twin Qn r0 ε0) K ε s₀ k X₀
            ≤ C * (1 + X₀) * Real.exp (max (kappaD1p αp ε'' - 1) 0 * X₀)) := by
  -- the exponents
  have hαpos : 0 < αp := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 2 - 2 / αp := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    have : 2 / αp < 2 := by rw [div_lt_iff₀ hαpos]; linarith
    rw [hδ]; linarith
  have hδ45 : δ < 4 / 5 := by
    have : 6 / 5 < 2 / αp := by rw [lt_div_iff₀ hαpos]; linarith
    rw [hδ]; linarith
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = min ε'' (4 / 5 - δ) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; exact lt_min hε'' (by linarith)
  have hε₁e : ε₁ ≤ ε'' := by rw [hε₁]; exact min_le_left _ _
  have hε₁δ : ε₁ ≤ 4 / 5 - δ := by rw [hε₁]; exact min_le_right _ _
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε₁ / 20 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; linarith
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  have hδ'0 : 0 ≤ δ + 3 * t := by linarith
  have hδ'1 : δ + 3 * t < 4 / 5 := by rw [ht]; linarith
  obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁ : ℝ, κ₁ = 2 * δ + ε₁ / 2 := ⟨_, rfl⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ κ₂ : ℝ, κ₂ = 2 * δ + ε₁ := ⟨_, rfl⟩
  have hκ₁0 : 0 ≤ κ₁ := by rw [hκ₁]; linarith
  have hκ12 : κ₁ < κ₂ := by rw [hκ₁, hκ₂]; linarith
  have hκ₂2 : κ₂ ≤ 2 := by rw [hκ₂]; linarith
  have hκ' : kappaD1p αp ε'' = 2 * δ + ε'' := by unfold kappaD1p; rw [hδ]
  have hκ₂κ' : κ₂ ≤ kappaD1p αp ε'' := by rw [hκ', hκ₂]; linarith
  have hκ₁κ' : κ₁ ≤ kappaD1p αp ε'' := by linarith
  have hLF : (2 + t) * (δ + 3 * t) ≤ κ₁ := by
    have htt : t * t ≤ t := by nlinarith
    have htδ : t * δ ≤ t := by nlinarith
    have : (2 + t) * (δ + 3 * t) = 2 * δ + 6 * t + t * δ + 3 * (t * t) := by ring
    rw [this, hκ₁]
    have : ε₁ = 20 * t := by rw [ht]; ring
    rw [this]; linarith
  obtain ⟨m', hm'⟩ : ∃ m' : ℝ, m' = min (2 - 5 / 2 * (δ + 3 * t)) 1 := ⟨_, rfl⟩
  have hm'0 : 0 < m' := by rw [hm']; exact lt_min (by linarith) one_pos
  have hm'1 : m' ≤ 1 := by rw [hm']; exact min_le_right _ _
  have hm'δ : m' ≤ 2 - 5 / 2 * (δ + 3 * t) := by rw [hm']; exact min_le_left _ _
  have hεM0 : 0 < m' / 10 := div_pos hm'0 (by norm_num)
  have hεM1 : m' / 10 ≤ 1 := by linarith
  have hlowe : (1 + 1 / 8) * (δ + 3 * t) ≤ 9 / 10 := by linarith
  -- the counts
  obtain ⟨CA, CB, CL, hCA, hCB, hCL, hcnt⟩ := L12c_counts_ev hD αp hα1 r0 ε0 hr0 hε0 B hB δ hδ t (m' / 10)
    (1 / 8) ht0 ht1 hεM0 hεM1 (by norm_num) (by norm_num)
  obtain ⟨S, hS1, hS⟩ := L12c_poly_le_exp 1 2 (m' / 20) one_pos (div_pos hm'0 (by norm_num))
  -- the constants
  set q := Real.exp (-(κ₂ - κ₁)) with hq
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have h1q : 0 < 1 - q := by linarith
  set Cn := 2 * Real.exp 1 * CA * Real.exp (max (κ₁ - 1) 0) with hCn
  set Cm := Real.exp κ₂ * CA / (1 - q) with hCm
  set Ct := Real.exp 2 * CB + CL with hCt
  have hCn0 : 0 ≤ Cn := by
    rw [hCn]; exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) hCA) (Real.exp_pos _).le
  have hCm0 : 0 ≤ Cm := by rw [hCm]; exact div_nonneg (mul_nonneg (Real.exp_pos _).le hCA) h1q.le
  have hCt0 : 0 ≤ Ct := by rw [hCt]; exact add_nonneg (mul_nonneg (Real.exp_pos _).le hCB) hCL
  refine ⟨Cn + Cm + Ct, m' / 20, by linarith, div_pos hm'0 (by norm_num), ?_⟩
  filter_upwards [hcnt, L12_log_eventually_ge (max S 4)] with Qn hc hL
  intro K ε s₀ hR X₀ hX₀
  obtain ⟨hs, hK, hNx, hBσ, hAll⟩ := hc K ε s₀ hR k hk
  have hsS : S ≤ s₀ := by have := hR.s_ge; have := le_max_left S 4; linarith
  have hs4 : 4 ≤ s₀ := by have := hR.s_ge; have := le_max_right S 4; linarith
  -- the counts in the form used
  have hN : ∀ x : ℝ, 0 ≤ x → 5 * x ≤ s₀ →
      L12cW Qn (twin Qn r0 ε0) K ε s₀ k (fun ρ => xRho s₀ ρ ≤ x) ≤ ENNReal.ofReal (CA * Real.exp (κ₁ * x)) := by
    intro x hx h5
    refine (hNx x hx h5).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hCA
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hLF hx
  have hLw : L12cW Qn (twin Qn r0 ε0) K ε s₀ k (fun _ => True) ≤ ENNReal.ofReal (CL * Real.exp (9 / 10 * s₀)) := by
    refine hAll.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hCL
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hlowe hs.le
  constructor
  · -- the rest clause
    have hr1 := L12c_rest_le Qn (twin Qn r0 ε0) K ε s₀ k X₀ hK hs.le
    have hr2 := L12c_Wg_add3 Qn (twin Qn r0 ε0) K ε s₀ k hK (L12cGr s₀ X₀) (L12cG1 s₀ X₀) (L12cG2 s₀)
      (L12cG3 s₀) (L12cG1_nonneg s₀ X₀) (L12cG2_nonneg s₀) (L12cG3_nonneg s₀)
      (fun ρ _ _ => L12c_rest_split s₀ X₀ ρ)
    have hm1 := L12c_mid_bound Qn (twin Qn r0 ε0) K ε s₀ k hK hs CA κ₁ κ₂ hCA hκ₁0 hκ12 hκ₂2 hN X₀ hX₀
    have hb1 := L12c_bulk_bound Qn (twin Qn r0 ε0) K ε s₀ k hK hs CB (δ + 3 * t) (m' / 10) m' hCB hδ'0
      (by linarith) hm'0 hm'δ hεM0.le le_rfl hBσ
    have hl1 := L12c_low_bound Qn (twin Qn r0 ε0) K ε s₀ k hK CL hCL hLw
    set E := Real.exp (-((2 - κ₂) * X₀)) with hE
    set Mid := E * Real.exp κ₂ * CA / (1 - Real.exp (-(κ₂ - κ₁))) with hMid
    set Bulk := (s₀ / 2 + 2) * (Real.exp 2 * CB * Real.exp (-(m' / 10 * s₀))) with hBulk
    set Low := CL * Real.exp (-(s₀ / 10)) with hLow
    have hMid0 : 0 ≤ Mid := by
      rw [hMid, hE]
      exact div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hCA) h1q.le
    have hBulk0 : 0 ≤ Bulk := by
      rw [hBulk]; exact mul_nonneg (by linarith) (mul_nonneg (mul_nonneg (Real.exp_pos _).le hCB) (Real.exp_pos _).le)
    have hLow0 : 0 ≤ Low := by rw [hLow]; exact mul_nonneg hCL (Real.exp_pos _).le
    have htot : ENNReal.ofReal (restSq Qn (twin Qn r0 ε0) K ε s₀ k X₀) ≤ ENNReal.ofReal (Mid + Bulk + Low) := by
      calc ENNReal.ofReal (restSq Qn (twin Qn r0 ε0) K ε s₀ k X₀)
          ≤ L12cWg Qn (twin Qn r0 ε0) K ε s₀ k (L12cGr s₀ X₀) := hr1
        _ ≤ _ := hr2
        _ ≤ ENNReal.ofReal Mid + ENNReal.ofReal Bulk + ENNReal.ofReal Low := add_le_add (add_le_add hm1 hb1) hl1
        _ = ENNReal.ofReal (Mid + Bulk + Low) := by
            rw [ENNReal.ofReal_add (add_nonneg hMid0 hBulk0) hLow0, ENNReal.ofReal_add hMid0 hBulk0]
    have hrs : restSq Qn (twin Qn r0 ε0) K ε s₀ k X₀ ≤ Mid + Bulk + Low :=
      (ENNReal.ofReal_le_ofReal_iff (add_nonneg (add_nonneg hMid0 hBulk0) hLow0)).mp htot
    -- the mid term
    have hEk : E ≤ Real.exp (-((2 - kappaD1p αp ε'') * X₀)) := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hκ₂κ' hX₀
      linarith
    have hMidle : s₀ * Mid ≤ Cm * (s₀ * Real.exp (-((2 - kappaD1p αp ε'') * X₀))) := by
      have e : s₀ * Mid = Cm * (s₀ * E) := by rw [hMid, hCm, hq]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEk hs.le) hCm0
    -- the bulk and low terms
    have hdec : Real.exp (-(s₀ / 10)) ≤ Real.exp (-(m' / 10 * s₀)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hm'1 hs.le
      linarith
    have hBL : Bulk + Low ≤ (s₀ / 2 + 2) * (Ct * Real.exp (-(m' / 10 * s₀))) := by
      have h1 : Low ≤ (s₀ / 2 + 2) * (CL * Real.exp (-(m' / 10 * s₀))) := by
        rw [hLow]
        calc CL * Real.exp (-(s₀ / 10)) ≤ CL * Real.exp (-(m' / 10 * s₀)) :=
              mul_le_mul_of_nonneg_left hdec hCL
          _ ≤ (s₀ / 2 + 2) * (CL * Real.exp (-(m' / 10 * s₀))) :=
              le_mul_of_one_le_left (mul_nonneg hCL (Real.exp_pos _).le) (by linarith)
      have e : (s₀ / 2 + 2) * (Ct * Real.exp (-(m' / 10 * s₀)))
          = Bulk + (s₀ / 2 + 2) * (CL * Real.exp (-(m' / 10 * s₀))) := by rw [hBulk, hCt]; ring
      rw [e]; linarith
    have hsq : s₀ * (s₀ / 2 + 2) ≤ Real.exp (m' / 20 * s₀) := by
      have h1 := hS s₀ hsS
      rw [one_mul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
      have h2 : s₀ * (s₀ / 2 + 2) ≤ s₀ ^ 2 := by nlinarith
      linarith
    have hBLle : s₀ * (Bulk + Low) ≤ Ct * Real.exp s₀ ^ (-(m' / 20)) := by
      have e1 : Real.exp s₀ ^ (-(m' / 20)) = Real.exp (-(m' / 20 * s₀)) := by
        rw [← Real.exp_mul]; congr 1; ring
      rw [e1]
      calc s₀ * (Bulk + Low) ≤ s₀ * ((s₀ / 2 + 2) * (Ct * Real.exp (-(m' / 10 * s₀)))) :=
            mul_le_mul_of_nonneg_left hBL hs.le
        _ = (s₀ * (s₀ / 2 + 2)) * (Ct * Real.exp (-(m' / 10 * s₀))) := by ring
        _ ≤ Real.exp (m' / 20 * s₀) * (Ct * Real.exp (-(m' / 10 * s₀))) :=
            mul_le_mul_of_nonneg_right hsq (mul_nonneg hCt0 (Real.exp_pos _).le)
        _ = Ct * Real.exp (-(m' / 20 * s₀)) := by
            rw [show Real.exp (-(m' / 20 * s₀)) = Real.exp (m' / 20 * s₀) * Real.exp (-(m' / 10 * s₀)) by
              rw [← Real.exp_add]; congr 1; ring]
            ring
    -- assembly
    have hP0 : 0 ≤ Real.exp s₀ ^ (-(m' / 20)) := (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
    have hQ0 : 0 ≤ s₀ * Real.exp (-((2 - kappaD1p αp ε'') * X₀)) := mul_nonneg hs.le (Real.exp_pos _).le
    calc s₀ * restSq Qn (twin Qn r0 ε0) K ε s₀ k X₀ ≤ s₀ * (Mid + Bulk + Low) :=
          mul_le_mul_of_nonneg_left hrs hs.le
      _ = s₀ * Mid + s₀ * (Bulk + Low) := by ring
      _ ≤ Cm * (s₀ * Real.exp (-((2 - kappaD1p αp ε'') * X₀))) + Ct * Real.exp s₀ ^ (-(m' / 20)) :=
          add_le_add hMidle hBLle
      _ ≤ (Cn + Cm + Ct) * (Real.exp s₀ ^ (-(m' / 20)) + s₀ * Real.exp (-((2 - kappaD1p αp ε'') * X₀))) := by
          nlinarith [mul_nonneg hCn0 hP0, mul_nonneg hCn0 hQ0, mul_nonneg hCm0 hP0, mul_nonneg hCt0 hQ0]
  · -- the near clause
    intro h5
    have hn := L12c_near_bound Qn (twin Qn r0 ε0) K ε s₀ k hK hs CA κ₁ hCA hκ₁0 hN X₀ hX₀ h5
    have hp : max (κ₁ - 1) 0 ≤ max (kappaD1p αp ε'' - 1) 0 := max_le_max (by linarith) le_rfl
    have hexp : Real.exp (max (κ₁ - 1) 0 * X₀) ≤ Real.exp (max (kappaD1p αp ε'' - 1) 0 * X₀) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hp hX₀)
    have hX1 : 0 ≤ 1 + X₀ := by linarith
    calc nearSum Qn (twin Qn r0 ε0) K ε s₀ k X₀
        ≤ 2 * Real.exp 1 * CA * Real.exp (max (κ₁ - 1) 0) * (1 + X₀) * Real.exp (max (κ₁ - 1) 0 * X₀) := hn
      _ = Cn * (1 + X₀) * Real.exp (max (κ₁ - 1) 0 * X₀) := by rw [hCn]
      _ ≤ (Cn + Cm + Ct) * (1 + X₀) * Real.exp (max (kappaD1p αp ε'' - 1) 0 * X₀) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hX1) hexp (Real.exp_pos _).le
            (mul_nonneg (by linarith) hX1)

end ShellS
end ZetaShell
