/-
Node K8a-4 (L7_3, round 2): ZetaQ's zone-split chain (`InZone.famPP_le_zone_split`: the diagonal `lemma43_diagonal`,
the Mertens evaluation `sumA2gQ_close`, the budget `B ≤ Q²(1+δ)`, `Q²(T/2π)ℒ ≤ C(1+δ/3)𝒩`, the zone facts, the cross
term `ρ ≤ δ`, and `final_arith`) run on `masterRHS − 2Q²S + 2E`, for ANY `S`, `E` obeying the conclusions of K8a-2 and
K8a-3. The saving is combined with the main term BEFORE the conversion to `𝒩` (only `Q²(T/2π)ℒ ≤ C(1+δ)𝒩` is
available in the tree, not its converse): `B·D_ℝ − Q²(T/2π)ℒ(aL)²(K1 − K1kill − η) ≤ Q²(T/2π)ℒ(aL)²[(1+δ)(K1a + 16δ) −
(K1 − K1kill) + η] + …`, the bracket is `≥ 0`, then convert. Result: in-zone coefficient 1 (K0a), zone edge `C·Jzone`,
out-zone `C·K1kill` (sec_lemmaK (e), eq:BK).
PROVED here: `final_arith_killed` is ZetaQ's `InZone.final_arith` with the saving and the error term added (steps A–E
verbatim; the last step re-done so that the saving meets the main term in `Q²` units), and `killed_chain_gen` is
`famPP_le_zone_split`'s proof verbatim (δ-threshold `70C+10 → 150C+10`) ending in `final_arith_killed`.
-/
import ZetaShell.LemmaK.LK_K8a_Defs

noncomputable section
open Filter MeasureTheory Set

namespace ZetaShell
namespace LemmaK

open ZetaQ ZetaQ.Zones ZetaQ.InZone ZetaQ.Payoff

set_option maxHeartbeats 800000 in
/-- **The arithmetic of the killed zone split** (ZetaQ's `final_arith` plus the saving `2Q²S` and the error `2E′`). -/
theorem final_arith_killed {total B K Pz Rz Dr Nr ρ M X W N C k k0 k1 E ε₀ δ ε' Q2 S E' s η : ℝ}
    (h1 : total ≤ B * Dr + 2 * B * Nr - 2 * (B - (1 + ε₀) * K) * Pz + (2 / ε₀) * B * Rz
      - 2 * (Q2 * S) + 2 * E')
    (hN : 2 * Nr ≤ ρ * Dr) (_hρ0 : 0 ≤ ρ) (hρ : ρ ≤ δ) (hD0 : 0 ≤ Dr)
    (hD : Dr ≤ (X * W * k + E) * (1 + δ)) (hE : B * E ≤ δ * W * N) (hE0 : 0 ≤ E)
    (hP1 : M * (1 - ε₀) ≤ Pz) (hP2 : Pz ≤ M * (1 + ε₀)) (hR : Rz ≤ ε₀ ^ 2 * Pz)
    (hM : 2 * M = X * W * k0) (hM0 : 0 ≤ M)
    (hε₀ : 0 < ε₀) (hε₀δ : ε₀ ≤ δ) (hδ1 : δ ≤ 1)
    (hK0 : 0 ≤ K) (hKB : K ≤ B) (hBX : B * X ≤ (1 + δ) ^ 2 * C * N)
    (hKX : K * X ≤ (1 + δ) ^ 2 * N)
    (hk : k = k0 + k1) (hk0 : 0 ≤ k0) (hk1 : 0 ≤ k1) (hk2 : k ≤ 2) (hC : 0 < C)
    (hW : 0 ≤ W) (hNn : 0 ≤ N) (hX : 0 ≤ X)
    (hδε : δ * (150 * C + 10) ≤ ε')
    (hQ20 : 0 ≤ Q2) (hBQ : B ≤ Q2 * (1 + δ)) (hQX : Q2 * X ≤ (1 + δ) ^ 2 * C * N)
    (hS : X * W * (s - η) ≤ 2 * S) (hE' : 2 * E' ≤ η * (Q2 * X * W))
    (hks : 0 ≤ k1 - s) (hks2 : k1 - s ≤ 2) (hη0 : 0 ≤ η) (hηδ : η ≤ δ) :
    total ≤ W * (k0 + C * (k1 - s) + ε') * N := by
  have hB0 : 0 ≤ B := hK0.trans hKB
  have hδ0 : 0 ≤ δ := hε₀.le.trans hε₀δ
  have hε₀1 : ε₀ ≤ 1 := hε₀δ.trans hδ1
  have hδδ : δ ^ 2 ≤ δ := by
    have := mul_le_mul_of_nonneg_left hδ1 hδ0
    rw [mul_one] at this
    rw [pow_two]
    exact this
  have hPz0 : 0 ≤ Pz := le_trans (mul_nonneg hM0 (by linarith)) hP1
  -- Step A: `(2/ε₀) B Rz ≤ 2 ε₀ B Pz`
  have hA : (2 / ε₀) * B * Rz ≤ 2 * ε₀ * B * Pz := by
    have h : (2 / ε₀) * B * Rz ≤ (2 / ε₀) * B * (ε₀ ^ 2 * Pz) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    have e : (2 / ε₀) * B * (ε₀ ^ 2 * Pz) = 2 * ε₀ * B * Pz := by
      field_simp
    linarith
  -- Step B: `total ≤ B Dr (1+δ) − 2(B−K)Pz + 4 ε₀ B Pz`
  have hB1 : 2 * B * Nr ≤ B * (δ * Dr) := by
    have e : 2 * B * Nr = B * (2 * Nr) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (hN.trans (mul_le_mul_of_nonneg_right hρ hD0)) hB0
  have hKPz : 2 * ε₀ * K * Pz ≤ 2 * ε₀ * B * Pz := by
    have h := mul_le_mul_of_nonneg_right hKB hPz0
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * ε₀)
    linarith
  have hB2 : total ≤ B * Dr * (1 + δ) - 2 * (B - K) * Pz + 4 * ε₀ * B * Pz
      - 2 * (Q2 * S) + 2 * E' := by
    linarith [h1, hA, hB1, hKPz]
  -- Step C: replace `Pz` by `M`
  have hBK : 0 ≤ B - K := by linarith
  have hC1 : -(2 * (B - K) * Pz) ≤ -(2 * (B - K) * M) + 2 * ε₀ * B * M := by
    have h := mul_le_mul_of_nonneg_left hP1 hBK
    have h' : 0 ≤ ε₀ * K * M := by positivity
    linarith
  have hC2 : 4 * ε₀ * B * Pz ≤ 8 * ε₀ * B * M := by
    have h := mul_le_mul_of_nonneg_left hP2 (by positivity : 0 ≤ 4 * ε₀ * B)
    have h'' : ε₀ * ε₀ * B * M ≤ ε₀ * B * M := by
      have h0 : 0 ≤ ε₀ * B * M := by positivity
      have := mul_le_mul_of_nonneg_right hε₀1 h0
      linarith
    linarith
  have hC3 : total ≤ B * Dr * (1 + δ) - 2 * (B - K) * M + 10 * δ * B * M
      - 2 * (Q2 * S) + 2 * E' := by
    have h : 10 * ε₀ * B * M ≤ 10 * δ * B * M := by
      have := mul_le_mul_of_nonneg_right hε₀δ (mul_nonneg hB0 hM0)
      linarith
    linarith [hB2, hC1, hC2, h]
  -- Step D: `B Dr (1+δ) ≤ B X W k (1+δ)² + 4 δ W N`
  have hD1 : B * Dr * (1 + δ) ≤ B * X * W * k * (1 + δ) ^ 2 + 4 * δ * W * N := by
    have h1' : B * Dr ≤ B * ((X * W * k + E) * (1 + δ)) := mul_le_mul_of_nonneg_left hD hB0
    have h2' : B * E * (1 + δ) ^ 2 ≤ 4 * δ * W * N := by
      have h4 : (1 + δ) ^ 2 ≤ 4 := by linarith only [hδδ, hδ1]
      have h3 : 0 ≤ B * E := mul_nonneg hB0 hE0
      calc B * E * (1 + δ) ^ 2 ≤ B * E * 4 := mul_le_mul_of_nonneg_left h4 h3
        _ ≤ δ * W * N * 4 := mul_le_mul_of_nonneg_right hE (by norm_num)
        _ = 4 * δ * W * N := by ring
    have h3' : B * Dr * (1 + δ) ≤ B * ((X * W * k + E) * (1 + δ)) * (1 + δ) :=
      mul_le_mul_of_nonneg_right h1' (by linarith)
    have e : B * ((X * W * k + E) * (1 + δ)) * (1 + δ)
        = B * X * W * k * (1 + δ) ^ 2 + B * E * (1 + δ) ^ 2 := by ring
    linarith
  -- Step E: collect
  have hE1 : 2 * (B - K) * M = B * X * W * k0 - K * X * W * k0 := by
    have e : 2 * (B - K) * M = (B - K) * (2 * M) := by ring
    rw [e, hM]; ring
  have hE2 : 10 * δ * B * M = 5 * δ * (B * X * W * k0) := by
    have e : 10 * δ * B * M = 5 * δ * B * (2 * M) := by ring
    rw [e, hM]; ring
  have hBXW : 0 ≤ B * X * W := by positivity
  have hF : total ≤ B * X * W * (k * (1 + δ) ^ 2 - k0 + 5 * δ * k0) + K * X * W * k0
      + 4 * δ * W * N - 2 * (Q2 * S) + 2 * E' := by
    linarith [hC3, hD1, hE1, hE2]
  have hG : k * (1 + δ) ^ 2 - k0 + 5 * δ * k0 ≤ k1 + 16 * δ := by
    have e : k * (1 + δ) ^ 2 - k0 + 5 * δ * k0
        = k1 + (k0 + k1) * (2 * δ + δ ^ 2) + 5 * δ * k0 := by rw [hk]; ring
    rw [e]
    have hkδ : (k0 + k1) * (2 * δ + δ ^ 2) ≤ 2 * (2 * δ + δ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hδδ : δ ^ 2 ≤ δ := by
      have := mul_le_mul_of_nonneg_left hδ1 hδ0
      rw [mul_one] at this
      rw [pow_two]
      exact this
    have h5 : 5 * δ * k0 ≤ 5 * δ * 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith only [hkδ, hδδ, h5]
  have hH : B * X * W * (k * (1 + δ) ^ 2 - k0 + 5 * δ * k0) ≤ B * X * W * (k1 + 16 * δ) :=
    mul_le_mul_of_nonneg_left hG hBXW
  have hsq : (1 + δ) ^ 2 ≤ 1 + 3 * δ := by linarith only [hδδ]
  -- the saving, absorbed BEFORE the conversion to `N`
  have hk1le : k1 ≤ 2 := by linarith
  have hXW : 0 ≤ X * W := mul_nonneg hX hW
  have hS' : Q2 * (X * W * (s - η)) ≤ 2 * (Q2 * S) := by
    have := mul_le_mul_of_nonneg_left hS hQ20
    linarith
  have hk1δ : 0 ≤ k1 + 16 * δ := by linarith
  have hBQ' : B * X * W * (k1 + 16 * δ) ≤ Q2 * (1 + δ) * X * W * (k1 + 16 * δ) := by
    have h0 : 0 ≤ X * W * (k1 + 16 * δ) := mul_nonneg hXW hk1δ
    have := mul_le_mul_of_nonneg_right hBQ h0
    linarith
  have hbr : (1 + δ) * (k1 + 16 * δ) - (s - η) ≤ (k1 - s) + 34 * δ + η := by
    have h1' : δ * k1 ≤ δ * 2 := mul_le_mul_of_nonneg_left hk1le hδ0
    have h2' : 16 * δ ^ 2 ≤ 16 * δ := by linarith only [hδδ]
    have e : (1 + δ) * (k1 + 16 * δ) = k1 + 16 * δ + δ * k1 + 16 * δ ^ 2 := by ring
    rw [e]
    linarith only [h1', h2']
  have hQXW : 0 ≤ Q2 * X * W := by positivity
  have hsave : Q2 * (1 + δ) * X * W * (k1 + 16 * δ) - Q2 * (X * W * (s - η))
      ≤ Q2 * X * W * ((k1 - s) + 34 * δ + η) := by
    have e : Q2 * (1 + δ) * X * W * (k1 + 16 * δ) - Q2 * (X * W * (s - η))
        = Q2 * X * W * ((1 + δ) * (k1 + 16 * δ) - (s - η)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hbr hQXW
  have hbr0 : 0 ≤ (k1 - s) + 34 * δ + η := by linarith
  have hI : Q2 * X * W * ((k1 - s) + 34 * δ + η) ≤ (1 + 3 * δ) * C * N * W * ((k1 - s) + 34 * δ + η) := by
    have h1' : Q2 * X * W ≤ (1 + δ) ^ 2 * C * N * W := mul_le_mul_of_nonneg_right hQX hW
    have h2' : (1 + δ) ^ 2 * C * N * W ≤ (1 + 3 * δ) * C * N * W := by
      have h0 : 0 ≤ C * N * W := by positivity
      have := mul_le_mul_of_nonneg_right hsq h0
      linarith
    exact mul_le_mul_of_nonneg_right (h1'.trans h2') hbr0
  have hEE : 2 * E' ≤ η * ((1 + 3 * δ) * C * N * W) := by
    have h1' : Q2 * X * W ≤ (1 + δ) ^ 2 * C * N * W := mul_le_mul_of_nonneg_right hQX hW
    have h2' : (1 + δ) ^ 2 * C * N * W ≤ (1 + 3 * δ) * C * N * W := by
      have h0 : 0 ≤ C * N * W := by positivity
      have := mul_le_mul_of_nonneg_right hsq h0
      linarith
    have := mul_le_mul_of_nonneg_left (h1'.trans h2') hη0
    linarith
  have hJ : K * X * W * k0 ≤ (1 + 3 * δ) * N * W * k0 := by
    have h1' : K * X * W ≤ (1 + δ) ^ 2 * N * W := mul_le_mul_of_nonneg_right hKX hW
    have h2' : (1 + δ) ^ 2 * N * W ≤ (1 + 3 * δ) * N * W := by
      have h0 : 0 ≤ N * W := by positivity
      have := mul_le_mul_of_nonneg_right hsq h0
      linarith
    exact mul_le_mul_of_nonneg_right (h1'.trans h2') hk0
  have hWN : 0 ≤ W * N := mul_nonneg hW hNn
  have hk0' : k0 ≤ 2 := by linarith
  have hfin0 : (1 + 3 * δ) * C * ((k1 - s) + 34 * δ + η) + η * ((1 + 3 * δ) * C) + (1 + 3 * δ) * k0 + 4 * δ
      ≤ k0 + C * (k1 - s) + ε' := by
    have hC0 : 0 ≤ C := hC.le
    have h1' : 3 * δ * C * (k1 - s) ≤ 3 * δ * C * 2 :=
      mul_le_mul_of_nonneg_left hks2 (by positivity)
    have h3' : 3 * δ * k0 ≤ 3 * δ * 2 := mul_le_mul_of_nonneg_left hk0' (by positivity)
    have h4' : (1 + 3 * δ) * C * (34 * δ + 2 * η) ≤ 4 * C * (36 * δ) := by
      have ha : 1 + 3 * δ ≤ 4 := by linarith
      have hb : 34 * δ + 2 * η ≤ 36 * δ := by linarith
      have hb0 : 0 ≤ 34 * δ + 2 * η := by linarith
      calc (1 + 3 * δ) * C * (34 * δ + 2 * η) ≤ 4 * C * (34 * δ + 2 * η) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hC0) hb0
        _ ≤ 4 * C * (36 * δ) := mul_le_mul_of_nonneg_left hb (by positivity)
    have e : (1 + 3 * δ) * C * ((k1 - s) + 34 * δ + η) + η * ((1 + 3 * δ) * C) + (1 + 3 * δ) * k0 + 4 * δ
        = C * (k1 - s) + 3 * δ * C * (k1 - s) + (1 + 3 * δ) * C * (34 * δ + 2 * η)
          + k0 + 3 * δ * k0 + 4 * δ := by ring
    rw [e]
    linarith only [h1', h3', h4', hδε]
  have hfin : (1 + 3 * δ) * C * N * W * ((k1 - s) + 34 * δ + η) + η * ((1 + 3 * δ) * C * N * W)
      + (1 + 3 * δ) * N * W * k0 + 4 * δ * W * N ≤ W * (k0 + C * (k1 - s) + ε') * N := by
    have := mul_le_mul_of_nonneg_left hfin0 hWN
    have e1 : W * N * ((1 + 3 * δ) * C * ((k1 - s) + 34 * δ + η) + η * ((1 + 3 * δ) * C)
        + (1 + 3 * δ) * k0 + 4 * δ)
        = (1 + 3 * δ) * C * N * W * ((k1 - s) + 34 * δ + η) + η * ((1 + 3 * δ) * C * N * W)
          + (1 + 3 * δ) * N * W * k0 + 4 * δ * W * N := by ring
    have e2 : W * N * (k0 + C * (k1 - s) + ε') = W * (k0 + C * (k1 - s) + ε') * N := by ring
    linarith
  linarith only [hF, hH, hBQ', hS', hsave, hI, hEE, hJ, hfin]

set_option maxHeartbeats 800000 in
/-- **K8a-4, for every family.** -/
theorem killed_chain_gen (F : Family) (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∃ e η : ℝ, 0 < e ∧ 0 < η ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord F r ε (Qn : ℝ) P → ∀ S E : ℝ,
      P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K1 (vDesign P) - K1kill (vDesign P) - η) ≤ 2 * S →
      2 * E ≤ η * (P.Q ^ 2 * (P.T / (2 * Real.pi) * P.LL) * (P.aQ * P.LB) ^ 2) →
      masterRHS F Qn P e - 2 * (P.Q ^ 2 * S) + 2 * E
        ≤ (P.aQ * P.LB) ^ 2
            * (FrobAssembly.K0a (zoneFactor P) (vDesign P)
              + F.Cconst * (FrobAssembly.Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P)) + ε')
            * NfamQ P F Qn := by
  obtain ⟨Cs, hCs0, hdiag⟩ := lemma43_diagonal (cWinDesign F)
  obtain ⟨CM, hCM0, hclose⟩ := sumA2gQ_close
  obtain ⟨Lρ, Tρ, hρ⟩ := FrobAssembly.rhoU_univ_le_pointwise (cWinDesign F)
  have hC := FrobAssembly.Cconst_pos F
  have hpi := Real.pi_pos
  -- the small parameter
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (ε' / (150 * F.Cconst + 10)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδδ : δ ^ 2 ≤ δ := by
    have := mul_le_mul_of_nonneg_left hδ1 hδ0.le
    rw [mul_one] at this
    rw [pow_two]
    exact this
  have hδε : δ * (150 * F.Cconst + 10) ≤ ε' := by
    have h : δ ≤ ε' / (150 * F.Cconst + 10) := by rw [hδdef]; exact min_le_right _ _
    have hpos : 0 < 150 * F.Cconst + 10 := by positivity
    calc δ * (150 * F.Cconst + 10) ≤ ε' / (150 * F.Cconst + 10) * (150 * F.Cconst + 10) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = ε' := div_mul_cancel₀ _ hpos.ne'
  have hδ3 : 0 < δ / 3 := by positivity
  have hδ31 : δ / 3 ≤ 1 := by linarith
  refine ⟨δ, δ, hδ0, hδ0, ?_⟩
  -- the thresholds
  have hK₁ : (1:ℝ) ≤ max 1 (Cs / δ + 1) := le_max_left _ _
  have hK₂ : (1:ℝ) ≤ max 1 (96 / (Real.pi * δ ^ 2)) := le_max_left _ _
  have hK₃ : (1:ℝ) ≤ max 1 (max Lρ Tρ) := le_max_left _ _
  have hK₄ : (1:ℝ) ≤ 500 := by norm_num
  have hK₅ : (1:ℝ) ≤ max 1 (3 / δ) := le_max_left _ _
  have hK₆ : (1:ℝ) ≤ max 1 (128 * F.Cconst * CM / (9 * δ)) := le_max_left _ _
  filter_upwards [FrobAssembly.design_regime F r ε hr hε _ hK₁, FrobAssembly.design_regime F r ε hr hε _ hK₂,
    FrobAssembly.design_regime F r ε hr hε _ hK₃, FrobAssembly.design_regime F r ε hr hε _ hK₄,
    FrobAssembly.design_regime F r ε hr hε _ hK₅, FrobAssembly.design_regime F r ε hr hε _ hK₆,
    FrobAssembly.design_basic F r ε hr hε,
    FrobAssembly.NfamQ_sharp_eventually F r ε hr hε hδ3 hδ31,
    zone_facts_eventually F r ε hr hε hδ0,
    zone_facts_eventually F r ε hr hε (ε₀ := δ ^ 2) (by positivity),
    ERRin_small_eventually F r ε hr hε hδ3,
    sizeR_LL_le_NfamQ_eventually F r ε hr hε hδ3 hδ31,
    reg_eventually F r ε hr hε, FrobAssembly.one_sub_zoneFactor_le_eventually F r ε hr hε 1 one_pos]
    with Qn hreg₁ hreg₂ hreg₃ hreg₄ hreg₅ hreg₆ hbas hsharp hz1 hz2 herr hsN hregQ hzf
  intro P hdes S E hS hE
  have hP := hdes.1
  have hQ := FrobAssembly.Q_of_design hdes
  obtain ⟨hlogK₁, hTK₁, -, -, -, hX32, -, -⟩ := hreg₁ P hdes
  obtain ⟨-, hTK₂, -, -, -, -, -, -⟩ := hreg₂ P hdes
  obtain ⟨hlogK₃, hTK₃, -, -, -, -, -, -⟩ := hreg₃ P hdes
  obtain ⟨-, -, -, -, hszK₄, -, -, -⟩ := hreg₄ P hdes
  obtain ⟨-, -, -, -, -, -, hQhalf₅, -⟩ := hreg₅ P hdes
  obtain ⟨hlogK₆, -, -, -, -, -, -, -⟩ := hreg₆ P hdes
  obtain ⟨hLL30, hL8, hlam, hw, hQn2⟩ := hbas P hdes
  obtain ⟨-, -, -, hs8, -, -, -, -, -⟩ := hregQ P hdes
  obtain ⟨hz1a, -⟩ := hz1 P hdes
  obtain ⟨-, hz2b⟩ := hz2 P hdes
  have hN := hsharp P hdes
  have herr' := herr P hdes
  have hsN' := hsN P hdes
  have hs0 : 0 ≤ P.s0 := by linarith
  have hQn : Qn ≤ ⌊P.Q⌋₊ := by rw [hQ, Nat.floor_natCast]
  have hQn1 : 1 ≤ Qn := by omega
  have hQnR : (2:ℝ) ≤ Qn := by exact_mod_cast hQn2
  have hQn0 : (0:ℝ) < Qn := by linarith
  have hTpos : 0 < P.T := hP.T_pos
  have hLL0 : 0 < P.LL := hP.LL_pos
  have hL0 : 0 < P.LB := hP.LB_pos
  have ha := hP.a_ge
  have ha0 := hP.aQ_pos
  have hcW : P.cWin = cWinDesign F := cWin_of_design hdes
  have hreg' : RegimeQ P := FrobAssembly.regimeQ_of hP hL8
  have hLS := largeSieveFamily_holds
  have hlogQ : Real.log Qn ≤ P.LL := (log_Qn_le_LL hP hQn1 hQ).1
  have hadm := vDesign_admissible hP
  -- ── (1) the master inequality
  have h1 : masterRHS F Qn P δ - 2 * (P.Q ^ 2 * S) + 2 * E
      ≤ sieveBudgetQ P * (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
        + 2 * sieveBudgetQ P * (∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))
        - 2 * (sieveBudgetQ P - (1 + δ) * (F.sizeR Qn + ERRin P Qn)) * zoneP P
        + (2 / δ) * sieveBudgetQ P * zoneR P - 2 * (P.Q ^ 2 * S) + 2 * E := by
    unfold masterRHS
    rw [outZone_normA2_eq P hP hw]
    apply le_of_eq
    field_simp
    ring
  -- ── (2) the diagonal: `D_ℝ = (T/π) S (1+Esm)`, `|Esm| ≤ Cs/T ≤ δ`, `D_ℝ > 0`
  obtain ⟨Esm, hEsm, hdg⟩ := hdiag P hP hreg' hw (by rw [hcW])
  have hSpos : (0:ℝ) < sumA2gQ P := by
    have h := sumA2gQ_lower_const P hP hreg' hw
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have h6 : 0 < 6 - Real.log 2 := by linarith
    have h7 : 0 < Real.log 2 ^ 2 / 2 * (6 - Real.log 2) / 1296 := by positivity
    linarith only [h, h7]
  have hTCs : Cs / δ + 1 ≤ P.T := le_trans (le_max_right _ _) hTK₁
  have hCsδ : Cs ≤ P.T * δ := by
    have : Cs / δ ≤ P.T := by linarith
    rwa [div_le_iff₀ hδ0] at this
  have hEsmδ : |Esm| ≤ δ := by
    refine hEsm.trans ?_
    rw [div_le_iff₀ hTpos]
    linarith
  have hEsm1 : |Esm| < 1 := by
    refine lt_of_le_of_lt hEsm ?_
    rw [div_lt_one hTpos]
    have : Cs / δ ≥ Cs := by
      rw [ge_iff_le, le_div_iff₀ hδ0]
      exact mul_le_of_le_one_right hCs0.le hδ1
    linarith
  have hTS : 0 < P.T / Real.pi * sumA2gQ P := by positivity
  have hDpos : 0 < ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := by
    rw [hdg]
    exact mul_pos hTS (by linarith [(abs_lt.mp hEsm1).1])
  have hD0 : 0 ≤ ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := hDpos.le
  -- ── (3) the cross term: `2 N_ℝ = ρ D_ℝ`, `ρ ≤ δ`
  have hρ0 : 0 ≤ rhoU P Set.univ := rhoU_nonneg P Set.univ MeasurableSet.univ
  have hNρ : 2 * (∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s))
      ≤ rhoU P Set.univ * ∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s) := by
    have hDne : (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s)) ≠ 0 := hDpos.ne'
    have e : rhoU P Set.univ * (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
        = 2 * ∫ s : ℝ, P.gQ s * Real.sqrt (normA2 P s) * Real.sqrt (normB2 P s) := by
      unfold rhoU
      simp only [MeasureTheory.setIntegral_univ]
      field_simp
    rw [e]
  have hρδ : rhoU P Set.univ ≤ δ := by
    have hLρ : Lρ ≤ P.LB := by
      have : Lρ ≤ max 1 (max Lρ Tρ) := le_trans (le_max_left _ _) (le_max_right _ _)
      linarith [this.trans hlogK₃, hlogQ, FrobAssembly.LL_le_LB hP hlam]
    have hTρ : Tρ ≤ P.T := by
      have : Tρ ≤ max 1 (max Lρ Tρ) := le_trans (le_max_right _ _) (le_max_right _ _)
      linarith [this.trans hTK₃]
    have h := hρ P hP hw (by rw [hcW]) hLρ hTρ
    refine h.trans ?_
    have hT96 : 96 / (Real.pi * δ ^ 2) ≤ P.T := le_trans (le_max_right _ _) hTK₂
    unfold rhoConstConservative
    rw [← Real.sqrt_mul (by positivity)]
    have harg : 48 / Real.pi * (2 / P.T) ≤ δ ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hT96
      rw [show 48 / Real.pi * (2 / P.T) = 96 / (Real.pi * P.T) by
          rw [div_mul_div_comm]; norm_num, div_le_iff₀ (by positivity)]
      linarith
    calc Real.sqrt (48 / Real.pi * (2 / P.T)) ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt harg
      _ = δ := Real.sqrt_sq hδ0.le
  -- ── (4) the Mertens evaluation: `D_ℝ ≤ (X W k + E)(1+δ)`
  have hIL := FrobAssembly.intervalIntegral_gQ_mul_eq hP hw
  have hSle : sumA2gQ P
      ≤ P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2 + CM * P.LB ^ 2 := by
    have h := (abs_le.mp (hclose P hP hw hL8)).2
    rw [hIL] at h
    linarith
  have hDle : (∫ s : ℝ, P.gQ s * (normA2 P s + normB2 P s))
      ≤ (P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P))
          + P.T / Real.pi * (CM * P.LB ^ 2)) * (1 + δ) := by
    rw [hdg]
    have hE1 : P.T / Real.pi * sumA2gQ P
        ≤ P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P))
          + P.T / Real.pi * (CM * P.LB ^ 2) := by
      have := mul_le_mul_of_nonneg_left hSle (by positivity : 0 ≤ P.T / Real.pi)
      calc P.T / Real.pi * sumA2gQ P
          ≤ P.T / Real.pi * (P.LL * (P.aQ * P.LB) ^ 2 * (K0 (vDesign P) + K1 (vDesign P)) / 2
              + CM * P.LB ^ 2) := this
        _ = _ := by ring
    have hE2 : 1 + Esm ≤ 1 + δ := by linarith [(abs_le.mp hEsmδ).2]
    exact mul_le_mul hE1 hE2 (by linarith [(abs_lt.mp hEsm1).1])
      (add_nonneg (mul_nonneg (by positivity) (FrobAssembly.K0_add_K1_nonneg hadm)) (by positivity))
  -- ── (5) the budget: `B ≤ Q²(1+δ)`, `B X ≤ (1+δ)² C N`
  have hQ1 : (1:ℝ) ≤ P.Q := by rw [hQ]; linarith
  have hQ2pos : 0 < P.Q ^ 2 := by rw [hQ]; positivity
  have hBQ : sieveBudgetQ P ≤ P.Q ^ 2 * (1 + δ) := by
    have hbud := lemma43_budget_is_Qsq P (δ := 1 / 2) (by norm_num) (by norm_num) hX32 hQ1
    have h3 : sieveBudgetQ P / P.Q ^ 2 ≤ 1 + 4 * Real.rpow P.Q (-(1 / 2)) := by
      linarith [(abs_le.mp hbud).2]
    -- Gallagher budget: `lemma43_budget_is_Qsq`'s constant is `4` (was `2`); `design_regime`'s
    -- unchanged `2Q^{−1/2} ≤ 1/max 1 (3/δ) ≤ δ/3` still gives `4Q^{−1/2} ≤ 2δ/3 ≤ δ`.
    have h4 : 4 * Real.rpow P.Q (-(1 / 2)) ≤ δ := by
      have hm : 3 / δ ≤ max 1 (3 / δ) := le_max_right _ _
      have hmpos : 0 < max 1 (3 / δ) := by positivity
      have h5 : 3 ≤ max 1 (3 / δ) * δ := by
        have := mul_le_mul_of_nonneg_right hm hδ0.le
        rwa [div_mul_cancel₀ _ hδ0.ne'] at this
      have h6 : 1 / max 1 (3 / δ) ≤ δ / 3 := by
        rw [div_le_div_iff₀ hmpos (by norm_num)]
        linarith
      linarith [hQhalf₅]
    calc sieveBudgetQ P = sieveBudgetQ P / P.Q ^ 2 * P.Q ^ 2 :=
          (div_mul_cancel₀ _ hQ2pos.ne').symm
      _ ≤ (1 + δ) * P.Q ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hQ2pos.le
      _ = P.Q ^ 2 * (1 + δ) := by ring
  have hX0 : 0 ≤ P.T / (2 * Real.pi) * P.LL := by positivity
  have hN0 : 0 ≤ NfamQ P F Qn := NfamQ_nonneg P F Qn
  have hQ2X : P.Q ^ 2 * (P.T / (2 * Real.pi) * P.LL) ≤ F.Cconst * (1 + δ / 3) * NfamQ P F Qn := by
    rw [hQ]
    calc (Qn:ℝ) ^ 2 * (P.T / (2 * Real.pi) * P.LL)
        = (Qn:ℝ) ^ 2 * (P.T / (2 * Real.pi)) * P.LL := by ring
      _ ≤ _ := hN
  have hCN0 : 0 ≤ F.Cconst * NfamQ P F Qn := by positivity
  have hBX : sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)
      ≤ (1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn := by
    calc sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)
        ≤ P.Q ^ 2 * (1 + δ) * (P.T / (2 * Real.pi) * P.LL) :=
          mul_le_mul_of_nonneg_right hBQ hX0
      _ = (1 + δ) * (P.Q ^ 2 * (P.T / (2 * Real.pi) * P.LL)) := by ring
      _ ≤ (1 + δ) * (F.Cconst * (1 + δ / 3) * NfamQ P F Qn) :=
          mul_le_mul_of_nonneg_left hQ2X (by linarith)
      _ = (1 + δ) * (1 + δ / 3) * (F.Cconst * NfamQ P F Qn) := by ring
      _ ≤ (1 + δ) * (1 + δ) * (F.Cconst * NfamQ P F Qn) := by
          apply mul_le_mul_of_nonneg_right _ hCN0
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn := by ring
  -- ── (6) `K_f X ≤ (1+δ)² N`, `K_f ≤ B`, `0 ≤ K_f`
  have hS0 : 0 ≤ F.sizeR Qn := by unfold Family.sizeR; positivity
  have hERR0 : 0 ≤ ERRin P Qn := ERRin_nonneg P Qn hs0
  have hK0 : 0 ≤ F.sizeR Qn + ERRin P Qn := by linarith
  have hKfle : F.sizeR Qn + ERRin P Qn ≤ (1 + δ / 3) * F.sizeR Qn := by linarith
  have hKX : (F.sizeR Qn + ERRin P Qn) * (P.T / (2 * Real.pi) * P.LL)
      ≤ (1 + δ) ^ 2 * NfamQ P F Qn := by
    calc (F.sizeR Qn + ERRin P Qn) * (P.T / (2 * Real.pi) * P.LL)
        ≤ (1 + δ / 3) * F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL) :=
          mul_le_mul_of_nonneg_right hKfle hX0
      _ = (1 + δ / 3) * (F.sizeR Qn * (P.T / (2 * Real.pi) * P.LL)) := by ring
      _ ≤ (1 + δ / 3) * ((1 + δ / 3) * NfamQ P F Qn) :=
          mul_le_mul_of_nonneg_left hsN' (by linarith)
      _ = (1 + δ / 3) * (1 + δ / 3) * NfamQ P F Qn := by ring
      _ ≤ (1 + δ) * (1 + δ) * NfamQ P F Qn := by
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      _ = (1 + δ) ^ 2 * NfamQ P F Qn := by ring
  have hsize := FrobAssembly.sizeR_le_point F Qn hQn1 hszK₄
  have hXQ1 : (1:ℝ) ≤ P.XQ := by
    unfold ParamsQ.XQ
    exact Real.one_le_exp hL0.le
  have hKB : F.sizeR Qn + ERRin P Qn ≤ sieveBudgetQ P := by
    have h1' : F.sizeR Qn + ERRin P Qn ≤ (1 + δ / 3) * (0.2 * (Qn:ℝ) ^ 2) :=
      hKfle.trans (mul_le_mul_of_nonneg_left hsize (by linarith))
    have h2' : (1 + δ / 3) * (0.2 * (Qn:ℝ) ^ 2) ≤ (4 / 3) * (0.2 * (Qn:ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3' : (Qn:ℝ) ^ 2 ≤ sieveBudgetQ P := by
      have hπX : 0 ≤ Real.pi * P.XQ := mul_nonneg Real.pi_pos.le (by linarith)
      unfold sieveBudgetQ; rw [hQ]; linarith
    linarith only [h1', h2', h3', sq_nonneg (Qn:ℝ)]
  -- ── (7) the zone facts
  have hP1 : P.T / (2 * Real.pi) * (∫ u in Set.Icc 0 P.s0, u * P.gQ u) * (1 - δ) ≤ zoneP P := by
    have := (abs_le.mp hz1a).1; linarith only [this]
  have hP2 : zoneP P ≤ P.T / (2 * Real.pi) * (∫ u in Set.Icc 0 P.s0, u * P.gQ u) * (1 + δ) := by
    have := (abs_le.mp hz1a).2; linarith only [this]
  have hR : zoneR P ≤ δ ^ 2 * zoneP P := hz2b
  have hI₀0 : 0 ≤ ∫ u in Set.Icc 0 P.s0, u * P.gQ u :=
    setIntegral_nonneg measurableSet_Icc fun u hu => mul_nonneg hu.1 (lemma42_g_nonneg P u)
  have hM0 : 0 ≤ P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u := by positivity
  have hM : 2 * (P.T / (2 * Real.pi) * ∫ u in Set.Icc 0 P.s0, u * P.gQ u)
      = P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * FrobAssembly.K0a (zoneFactor P) (vDesign P) :=
    zoneMain_eq P hP hw hs0
  -- ── (8) the kernel pieces
  have hk : K0 (vDesign P) + K1 (vDesign P)
      = FrobAssembly.K0a (zoneFactor P) (vDesign P) + FrobAssembly.K1a (zoneFactor P) (vDesign P) := by
    rw [FrobAssembly.K0a_add_K1a hadm, K0_add_K1 hadm]
  have hk0 : 0 ≤ FrobAssembly.K0a (zoneFactor P) (vDesign P) := FrobAssembly.K0a_nonneg hadm _
  have hk1 : 0 ≤ FrobAssembly.K1a (zoneFactor P) (vDesign P) := FrobAssembly.K1a_nonneg hadm _
  have hk2 : K0 (vDesign P) + K1 (vDesign P) ≤ 2 :=
    FrobAssembly.K0_add_K1_le_two hadm hP.lam_lt_two.le
  have hW0 : 0 ≤ (P.aQ * P.LB) ^ 2 := by positivity
  -- ── (9) the Mertens-remainder term: `B E ≤ δ W N`
  have hE0 : 0 ≤ P.T / Real.pi * (CM * P.LB ^ 2) := by positivity
  have hBE : sieveBudgetQ P * (P.T / Real.pi * (CM * P.LB ^ 2))
      ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by
    have hLL128 : 128 * F.Cconst * CM / (9 * δ) ≤ P.LL :=
      le_trans (le_trans (le_max_right _ _) hlogK₆) hlogQ
    have hB0 : 0 ≤ sieveBudgetQ P := hK0.trans hKB
    have e1 : sieveBudgetQ P * (P.T / Real.pi * (CM * P.LB ^ 2))
        = (sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL) := by
      field_simp
    have hLB2 : P.LB ^ 2 ≤ 16 / 9 * (P.aQ * P.LB) ^ 2 := by
      have : (3 / 4) ^ 2 ≤ P.aQ ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
      have h0 : 0 ≤ P.LB ^ 2 := sq_nonneg _
      calc P.LB ^ 2 = 16 / 9 * ((3 / 4) ^ 2 * P.LB ^ 2) := by ring
        _ ≤ 16 / 9 * (P.aQ ^ 2 * P.LB ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_right this h0
        _ = 16 / 9 * (P.aQ * P.LB) ^ 2 := by ring
    have hq : 2 * CM * P.LB ^ 2 / P.LL ≤ 32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL := by
      apply div_le_div_of_nonneg_right _ hLL0.le
      have := mul_le_mul_of_nonneg_left hLB2 (by positivity : 0 ≤ 2 * CM)
      linarith only [this]
    have h3 : (sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL)
        ≤ ((1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn)
            * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL) :=
      mul_le_mul hBX hq (by positivity) (mul_nonneg (mul_nonneg (by positivity) hC.le) hN0)
    have h4 : (1 + δ) ^ 2 ≤ 4 := by linarith only [hδδ, hδ1]
    have h5 : 128 / 9 * F.Cconst * CM / P.LL ≤ δ := by
      rw [div_le_iff₀ hLL0]
      rw [div_le_iff₀ (by positivity)] at hLL128
      linarith only [hLL128]
    have h6 : ((1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn)
          * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL)
        = (1 + δ) ^ 2 * (32 / 9 * F.Cconst * CM / P.LL)
            * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
      field_simp
    have hWN0 : 0 ≤ (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by positivity
    have h7 : (1 + δ) ^ 2 * (32 / 9 * F.Cconst * CM / P.LL)
          * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn)
        ≤ 4 * (32 / 9 * F.Cconst * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
      have h0 : 0 ≤ (32 / 9 * F.Cconst * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := by
        positivity
      have := mul_le_mul_of_nonneg_right h4 h0
      linarith only [this]
    have h8 : 4 * (32 / 9 * F.Cconst * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn)
        ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := by
      have e : 4 * (32 / 9 * F.Cconst * CM / P.LL) = 128 / 9 * F.Cconst * CM / P.LL := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right h5 hWN0
      linarith only [this]
    calc sieveBudgetQ P * (P.T / Real.pi * (CM * P.LB ^ 2))
        = (sieveBudgetQ P * (P.T / (2 * Real.pi) * P.LL)) * (2 * CM * P.LB ^ 2 / P.LL) := e1
      _ ≤ ((1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn)
            * (32 / 9 * CM * (P.aQ * P.LB) ^ 2 / P.LL) := h3
      _ = (1 + δ) ^ 2 * (32 / 9 * F.Cconst * CM / P.LL)
            * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := h6
      _ ≤ 4 * (32 / 9 * F.Cconst * CM / P.LL) * ((P.aQ * P.LB) ^ 2 * NfamQ P F Qn) := h7
      _ ≤ δ * (P.aQ * P.LB) ^ 2 * NfamQ P F Qn := h8
  -- ── (10) assemble
  -- ── (11) the extra facts for the saving
  have hQB : P.Q ^ 2 * (1 : ℝ) ≤ sieveBudgetQ P := by
    have hπX : 0 ≤ Real.pi * P.XQ := mul_nonneg Real.pi_pos.le (by linarith)
    unfold sieveBudgetQ; linarith
  have hQX : P.Q ^ 2 * (P.T / (2 * Real.pi) * P.LL) ≤ (1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn := by
    have h' : F.Cconst * (1 + δ / 3) * NfamQ P F Qn ≤ (1 + δ) ^ 2 * F.Cconst * NfamQ P F Qn := by
      have hc : (1 + δ / 3) ≤ (1 + δ) ^ 2 := by
        have e : (1 + δ) ^ 2 = 1 + 2 * δ + δ ^ 2 := by ring
        rw [e]; linarith only [sq_nonneg δ, hδ0.le]
      have := mul_le_mul_of_nonneg_left hc hCN0
      linarith
    exact hQ2X.trans h'
  have hK1kill : K1kill (vDesign P) ≤ K1 (vDesign P) := by
    unfold K1kill K1
    apply setIntegral_mono_on ((psi_integrable hadm).integrableOn) ((absPsi_integrable hadm).integrableOn)
      (measurableSet_lt measurable_const continuous_abs.measurable)
    intro α hα
    have h1a : (1 : ℝ) ≤ |α| := le_of_lt hα
    have hp := psi_nonneg hadm α
    have := mul_le_mul_of_nonneg_right h1a hp
    linarith only [this]
  have hK1kill0 : 0 ≤ K1kill (vDesign P) := by
    unfold K1kill
    exact integral_nonneg (fun α => psi_nonneg hadm α)
  obtain ⟨hza0, hza1', -⟩ := hzf P hdes
  have hza1 : zoneFactor P ≤ 1 := by linarith
  have hsplit : FrobAssembly.K1a (zoneFactor P) (vDesign P)
      = FrobAssembly.Jzone (zoneFactor P) (vDesign P) + K1 (vDesign P) :=
    FrobAssembly.K1a_eq_Jzone_add_K1 hadm hza1
  have hJz0 : 0 ≤ FrobAssembly.Jzone (zoneFactor P) (vDesign P) := by
    unfold FrobAssembly.Jzone
    exact integral_nonneg (fun α => mul_nonneg (abs_nonneg α) (psi_nonneg hadm α))
  have hks : 0 ≤ FrobAssembly.K1a (zoneFactor P) (vDesign P) - (K1 (vDesign P) - K1kill (vDesign P)) := by
    rw [hsplit]; linarith
  have hks2 : FrobAssembly.K1a (zoneFactor P) (vDesign P) - (K1 (vDesign P) - K1kill (vDesign P)) ≤ 2 := by
    linarith
  have hS' : P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K1 (vDesign P) - K1kill (vDesign P) - δ)
      ≤ 2 * S := hS
  have key := final_arith_killed (ρ := rhoU P Set.univ) (X := P.T / (2 * Real.pi) * P.LL)
    (k := K0 (vDesign P) + K1 (vDesign P)) (Q2 := P.Q ^ 2) (S := S) (E' := E)
    (s := K1 (vDesign P) - K1kill (vDesign P)) (η := δ) h1 hNρ hρ0 hρδ hD0 hDle hBE hE0 hP1 hP2 hR hM hM0
    hδ0 le_rfl hδ1 hK0 hKB hBX hKX hk hk0 hk1 hk2 hC hW0 hN0 hX0 hδε (sq_nonneg _) (by linarith [hBQ])
    hQX (by linarith [hS']) (by linarith [hE]) hks hks2 hδ0.le le_rfl
  have e : FrobAssembly.K1a (zoneFactor P) (vDesign P) - (K1 (vDesign P) - K1kill (vDesign P))
      = FrobAssembly.Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P) := by rw [hsplit]; ring
  rw [e] at key
  exact key


/-- **K8a-4.** -/
theorem killed_chain (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) (ε' : ℝ) (hε' : 0 < ε') :
    ∃ e η : ℝ, 0 < e ∧ 0 < η ∧ ∀ᶠ Qn : ℕ in atTop, ∀ P : ParamsQ,
      DesignOfRecord Family.qle r ε (Qn : ℝ) P → ∀ S E : ℝ,
      P.T / (2 * Real.pi) * P.LL * (P.aQ * P.LB) ^ 2 * (K1 (vDesign P) - K1kill (vDesign P) - η) ≤ 2 * S →
      2 * E ≤ η * (P.Q ^ 2 * (P.T / (2 * Real.pi) * P.LL) * (P.aQ * P.LB) ^ 2) →
      masterRHS Family.qle Qn P e - 2 * (P.Q ^ 2 * S) + 2 * E
        ≤ (P.aQ * P.LB) ^ 2
            * (FrobAssembly.K0a (zoneFactor P) (vDesign P)
              + Family.qle.Cconst * (FrobAssembly.Jzone (zoneFactor P) (vDesign P) + K1kill (vDesign P)) + ε')
            * NfamQ P Family.qle Qn :=
  killed_chain_gen Family.qle r ε hr hε ε' hε'

end LemmaK
end ZetaShell
