/-
K3b-arith (L7_3c, round 10): the closing arithmetic of K3b, as a statement about real numbers.
From `I ≤ Q²((1+δ₁)A + ℒG − W)`, `A ≤ U(Y + E)`, `W ≥ κ_C U(Y − ℓG − L)`, `0 ≤ Y ≤ LG`,
`Bs ≥ C U(ℒ − 1)(G − 1)`, `x·C·sR ≥ Q²(x − 1)` and the smallness of the error ratios against `t·x`:
`I ≤ (1 + t)·sR·Bs`.
-/
import Mathlib

namespace ZetaShell
namespace ShellK
namespace F1c

set_option maxHeartbeats 1000000 in
theorem final_arith_K3b {Q2 U LL L x G Y A W Bs I E sR κC c₁ δ₁ ℓ t κ KE D C₁' Cf : ℝ}
    (hx : 1 ≤ x) (hU : x ≤ U) (hLLx : x ≤ LL) (hL : L ≤ 2 * LL) (hL0 : 0 ≤ L) (hQ2 : 0 ≤ Q2)
    (hκ : 0 < κ) (hκx : 1 ≤ κ * x) (hG : κ * LL ^ 2 ≤ G)
    (hE : E ≤ KE * LL ^ 2) (hKE : 0 ≤ KE)
    (hδ₁0 : 0 ≤ δ₁) (hδ₁ : δ₁ * x ≤ 2) (hδ₁1 : δ₁ ≤ 1)
    (hc₁0 : 0 ≤ c₁) (hc₁ : c₁ * x ≤ C₁') (hc₁1 : c₁ ≤ 1)
    (hκ1 : 1 - c₁ ≤ κC) (hκ2 : κC ≤ 1 + c₁)
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ LL + D) (hD : 0 ≤ D)
    (hI : I ≤ Q2 * ((1 + δ₁) * A + LL * G - W))
    (hA : A ≤ U * (Y + E))
    (hW : κC * U * (Y - ℓ * G - L) ≤ W)
    (hY0 : 0 ≤ Y) (hYL : Y ≤ L * G)
    (hCf : 0 < Cf) (hB : Cf * U * (LL - 1) * (G - 1) ≤ Bs)
    (hsR : Q2 * (x - 1) ≤ x * (Cf * sR)) (hsR0 : 0 ≤ sR)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsmall : 11 + 3 * C₁' + (2 * KE + 4) / κ + 2 * D ≤ t * x) :
    I ≤ (1 + t) * sR * Bs := by
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < U := by linarith
  have hLL1 : 1 ≤ LL := by linarith
  have hLL0 : 0 < LL := by linarith
  have hC₁' : 0 ≤ C₁' := le_trans (mul_nonneg hc₁0 hx0.le) hc₁
  have hκLL : κ * x * LL ≤ G := by
    have h1 : κ * x * LL ≤ κ * LL * LL :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLLx hκ.le) hLL0.le
    calc κ * x * LL ≤ κ * LL * LL := h1
      _ = κ * LL ^ 2 := by ring
      _ ≤ G := hG
  have hκLL1 : 1 ≤ κ * LL := le_trans hκx (mul_le_mul_of_nonneg_left hLLx hκ.le)
  have hGx : x ≤ G := by
    calc x = x * 1 := by ring
      _ ≤ x * (κ * LL) := mul_le_mul_of_nonneg_left hκLL1 hx0.le
      _ = κ * x * LL := by ring
      _ ≤ G := hκLL
  have hG0 : 0 < G := by linarith
  have hG1 : 1 ≤ G := by linarith
  have hP00 : 0 < LL * G := by positivity
  have hxLL : x * LL ≤ LL * G := by
    calc x * LL = LL * x := by ring
      _ ≤ LL * G := mul_le_mul_of_nonneg_left hGx hLL0.le
  have hxG : x * G ≤ LL * G := mul_le_mul_of_nonneg_right hLLx hG0.le
  have hκxG : κ * x ≤ G := by
    calc κ * x = κ * x * 1 := by ring
      _ ≤ κ * x * LL := mul_le_mul_of_nonneg_left hLL1 (by positivity)
      _ ≤ G := hκLL
  -- Step a: `I ≤ Q²·U·Φ`
  have ha2 : (1 + δ₁ - κC) * Y ≤ (δ₁ + c₁) * (L * G) := by
    rcases le_total 0 (1 + δ₁ - κC) with h | h
    · calc (1 + δ₁ - κC) * Y ≤ (1 + δ₁ - κC) * (L * G) := mul_le_mul_of_nonneg_left hYL h
        _ ≤ (δ₁ + c₁) * (L * G) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · have h1 : (1 + δ₁ - κC) * Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hY0
      have h2 : 0 ≤ (δ₁ + c₁) * (L * G) := by positivity
      linarith
  have ha3 : κC * (ℓ * G) ≤ (1 + c₁) * (ℓ * G) := mul_le_mul_of_nonneg_right hκ2 (by positivity)
  have ha4 : κC * L ≤ (1 + c₁) * L := mul_le_mul_of_nonneg_right hκ2 hL0
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = (δ₁ + c₁) * (L * G) + (1 + δ₁) * E + (1 + c₁) * (ℓ * G)
      + (1 + c₁) * L + LL * G / U := ⟨_, rfl⟩
  have hbr : (1 + δ₁) * A + LL * G - W ≤ U * Φ := by
    have h1 : (1 + δ₁) * A ≤ (1 + δ₁) * (U * (Y + E)) := mul_le_mul_of_nonneg_left hA (by linarith)
    have e1 : U * (LL * G / U) = LL * G := by field_simp
    have e2 : U * Φ = U * ((δ₁ + c₁) * (L * G)) + U * ((1 + δ₁) * E) + U * ((1 + c₁) * (ℓ * G))
        + U * ((1 + c₁) * L) + LL * G := by
      rw [hΦ, mul_add, mul_add, mul_add, mul_add, e1]
    have h2 : U * ((1 + δ₁ - κC) * Y) ≤ U * ((δ₁ + c₁) * (L * G)) := mul_le_mul_of_nonneg_left ha2 hU0.le
    have h3 : U * (κC * (ℓ * G)) ≤ U * ((1 + c₁) * (ℓ * G)) := mul_le_mul_of_nonneg_left ha3 hU0.le
    have h4 : U * (κC * L) ≤ U * ((1 + c₁) * L) := mul_le_mul_of_nonneg_left ha4 hU0.le
    rw [e2]
    linear_combination h1 + hW + h2 + h3 + h4
  have hIa : I ≤ Q2 * (U * Φ) := le_trans hI (mul_le_mul_of_nonneg_left hbr hQ2)
  -- Step b: `x·Φ ≤ LL·G·(x + K₁ + 2D)`
  have hb1 : x * ((δ₁ + c₁) * (L * G)) ≤ (2 + C₁') * (2 * (LL * G)) := by
    have h1 : (δ₁ + c₁) * x ≤ 2 + C₁' := by linarith
    have h2 : L * G ≤ 2 * (LL * G) := by
      have := mul_le_mul_of_nonneg_right hL hG0.le
      linarith
    calc x * ((δ₁ + c₁) * (L * G)) = ((δ₁ + c₁) * x) * (L * G) := by ring
      _ ≤ (2 + C₁') * (2 * (LL * G)) := mul_le_mul h1 h2 (by positivity) (by linarith)
  have hb2 : x * ((1 + δ₁) * E) ≤ 2 * KE / κ * (LL * G) := by
    have hE' : (1 + δ₁) * E ≤ 2 * (KE * LL ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_left hE (by linarith))
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    have h2 : κ * (x * LL ^ 2) ≤ LL * G := by
      calc κ * (x * LL ^ 2) = LL * (κ * x * LL) := by ring
        _ ≤ LL * G := mul_le_mul_of_nonneg_left hκLL hLL0.le
    have h3 : x * LL ^ 2 ≤ LL * G / κ := by rw [le_div_iff₀ hκ]; linarith
    calc x * ((1 + δ₁) * E) ≤ x * (2 * (KE * LL ^ 2)) := mul_le_mul_of_nonneg_left hE' hx0.le
      _ = 2 * KE * (x * LL ^ 2) := by ring
      _ ≤ 2 * KE * (LL * G / κ) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * KE / κ * (LL * G) := by ring
  have hb3 : x * ((1 + c₁) * (ℓ * G)) ≤ LL * G * (x + C₁' + 2 * D) := by
    have h1 : (1 + c₁) * (ℓ * G) ≤ (1 + c₁) * ((LL + D) * G) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hℓ hG0.le) (by linarith)
    have h2 : x * ((1 + c₁) * ((LL + D) * G))
        = x * (LL * G) + (c₁ * x) * (LL * G) + (1 + c₁) * D * (x * G) := by ring
    have h3 : (c₁ * x) * (LL * G) ≤ C₁' * (LL * G) := mul_le_mul_of_nonneg_right hc₁ hP00.le
    have h5 : (1 + c₁) * D * (x * G) ≤ 2 * D * (LL * G) := by
      have : (1 + c₁) * D ≤ 2 * D := mul_le_mul_of_nonneg_right (by linarith) hD
      calc (1 + c₁) * D * (x * G) ≤ 2 * D * (x * G) := mul_le_mul_of_nonneg_right this (by positivity)
        _ ≤ 2 * D * (LL * G) := mul_le_mul_of_nonneg_left hxG (by positivity)
    calc x * ((1 + c₁) * (ℓ * G)) ≤ x * ((1 + c₁) * ((LL + D) * G)) := mul_le_mul_of_nonneg_left h1 hx0.le
      _ ≤ x * (LL * G) + C₁' * (LL * G) + 2 * D * (LL * G) := by rw [h2]; linarith
      _ = LL * G * (x + C₁' + 2 * D) := by ring
  have hb4 : x * ((1 + c₁) * L) ≤ 4 / κ * (LL * G) := by
    have h1 : (1 + c₁) * L ≤ 4 * LL := by
      have := mul_le_mul_of_nonneg_right (by linarith : 1 + c₁ ≤ 2) hL0
      linarith
    have h3 : x * LL ≤ LL * G / κ := by
      rw [le_div_iff₀ hκ]
      calc x * LL * κ = LL * (κ * x) := by ring
        _ ≤ LL * G := mul_le_mul_of_nonneg_left hκxG hLL0.le
    calc x * ((1 + c₁) * L) ≤ x * (4 * LL) := mul_le_mul_of_nonneg_left h1 hx0.le
      _ = 4 * (x * LL) := by ring
      _ ≤ 4 * (LL * G / κ) := by linarith
      _ = 4 / κ * (LL * G) := by ring
  have hb5 : x * (LL * G / U) ≤ LL * G := by
    have h1 : x / U ≤ 1 := by rw [div_le_one hU0]; exact hU
    calc x * (LL * G / U) = (x / U) * (LL * G) := by ring
      _ ≤ 1 * (LL * G) := mul_le_mul_of_nonneg_right h1 hP00.le
      _ = LL * G := one_mul _
  have hb : x * Φ ≤ LL * G * (x + (5 + 3 * C₁' + (2 * KE + 4) / κ) + 2 * D) := by
    have e : x * Φ = x * ((δ₁ + c₁) * (L * G)) + x * ((1 + δ₁) * E) + x * ((1 + c₁) * (ℓ * G))
        + x * ((1 + c₁) * L) + x * (LL * G / U) := by rw [hΦ]; ring
    have e2 : LL * G * (x + (5 + 3 * C₁' + (2 * KE + 4) / κ) + 2 * D)
        = (2 + C₁') * (2 * (LL * G)) + 2 * KE / κ * (LL * G) + LL * G * (x + C₁' + 2 * D)
          + 4 / κ * (LL * G) + LL * G := by
      field_simp; ring
    rw [e, e2]
    linarith
  -- Steps c, d, e: the right side
  have hd1 : LL * G * (x - 2) ≤ x * ((LL - 1) * (G - 1)) := by
    linear_combination hxLL + hxG + hx0.le
  have hd2 : LL * G * (x - 3) ≤ (x - 1) * ((LL - 1) * (G - 1)) := by
    have h1 : (x - 1) * (LL * G * (x - 2)) ≤ (x - 1) * (x * ((LL - 1) * (G - 1))) :=
      mul_le_mul_of_nonneg_left hd1 (by linarith)
    have h2 : 0 ≤ 2 * (LL * G) := by positivity
    have h3 : x * (LL * G * (x - 3)) ≤ x * ((x - 1) * ((LL - 1) * (G - 1))) := by
      linear_combination h1 + h2
    exact le_of_mul_le_mul_left h3 hx0
  have he : LL * G * (x + (5 + 3 * C₁' + (2 * KE + 4) / κ) + 2 * D) ≤ (1 + t) * (LL * G * (x - 3)) := by
    have h1 : x + (5 + 3 * C₁' + (2 * KE + 4) / κ) + 2 * D ≤ (1 + t) * (x - 3) := by
      linear_combination hsmall + 3 * ht1
    calc LL * G * (x + (5 + 3 * C₁' + (2 * KE + 4) / κ) + 2 * D) ≤ LL * G * ((1 + t) * (x - 3)) :=
          mul_le_mul_of_nonneg_left h1 hP00.le
      _ = (1 + t) * (LL * G * (x - 3)) := by ring
  -- combine
  have hRHS : (1 + t) * sR * (Cf * U * (LL - 1) * (G - 1)) ≤ (1 + t) * sR * Bs :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hm : 0 ≤ (LL - 1) * (G - 1) := mul_nonneg (by linarith) (by linarith)
  have s1 : x * I ≤ Q2 * U * (x * Φ) := by
    calc x * I ≤ x * (Q2 * (U * Φ)) := mul_le_mul_of_nonneg_left hIa hx0.le
      _ = Q2 * U * (x * Φ) := by ring
  have s2 : Q2 * U * (x * Φ) ≤ Q2 * U * ((1 + t) * (LL * G * (x - 3))) :=
    mul_le_mul_of_nonneg_left (hb.trans he) (by positivity)
  have s3 : Q2 * U * ((1 + t) * (LL * G * (x - 3)))
      ≤ Q2 * U * ((1 + t) * ((x - 1) * ((LL - 1) * (G - 1)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd2 (by linarith)) (by positivity)
  have s5 : (1 + t) * U * ((LL - 1) * (G - 1)) * (Q2 * (x - 1))
      ≤ (1 + t) * U * ((LL - 1) * (G - 1)) * (x * (Cf * sR)) :=
    mul_le_mul_of_nonneg_left hsR (by positivity)
  have hfin : x * I ≤ x * ((1 + t) * sR * (Cf * U * (LL - 1) * (G - 1))) := by
    have e4 : Q2 * U * ((1 + t) * ((x - 1) * ((LL - 1) * (G - 1))))
        = (1 + t) * U * ((LL - 1) * (G - 1)) * (Q2 * (x - 1)) := by ring
    have e6 : (1 + t) * U * ((LL - 1) * (G - 1)) * (x * (Cf * sR))
        = x * ((1 + t) * sR * (Cf * U * (LL - 1) * (G - 1))) := by ring
    calc x * I ≤ Q2 * U * (x * Φ) := s1
      _ ≤ Q2 * U * ((1 + t) * (LL * G * (x - 3))) := s2
      _ ≤ Q2 * U * ((1 + t) * ((x - 1) * ((LL - 1) * (G - 1)))) := s3
      _ = (1 + t) * U * ((LL - 1) * (G - 1)) * (Q2 * (x - 1)) := e4
      _ ≤ (1 + t) * U * ((LL - 1) * (G - 1)) * (x * (Cf * sR)) := s5
      _ = x * ((1 + t) * sR * (Cf * U * (LL - 1) * (G - 1))) := e6
  exact le_trans (le_of_mul_le_mul_left hfin hx0) hRHS

end F1c
end ShellK
end ZetaShell
