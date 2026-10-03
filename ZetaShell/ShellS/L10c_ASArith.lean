/-
L10c_ASArith (L7_10c, 3 Oct 2026): the closing arithmetic of AS in real numbers: the replacement cost
`F(a) ≤ (√F(b) + √E)² ≤ (1 + 1/ℒ)F(b) + (1 + ℒ)E`, and the bounds of the core.
-/
import ZetaShell.ShellS.L10c_ASH

noncomputable section

namespace ZetaShell
namespace ShellS
namespace ASc

theorem sq_sqrt_add_le (F G L : ℝ) (hF : 0 ≤ F) (hG : 0 ≤ G) (hL : 0 < L) :
    (Real.sqrt F + Real.sqrt G) ^ 2 ≤ (1 + 1 / L) * F + (1 + L) * G := by
  set p := Real.sqrt F with hp
  set q := Real.sqrt G with hq
  have hp2 : p ^ 2 = F := Real.sq_sqrt hF
  have hq2 : q ^ 2 = G := Real.sq_sqrt hG
  have h0 := sq_nonneg (p - L * q)
  -- `2pq ≤ p²/L + L q²`
  have key : 2 * p * q ≤ p ^ 2 / L + L * q ^ 2 := by
    have e : p ^ 2 / L + L * q ^ 2 - 2 * p * q = (p - L * q) ^ 2 / L := by field_simp; ring
    have : 0 ≤ (p - L * q) ^ 2 / L := div_nonneg h0 hL.le
    linarith
  have e1 : (p + q) ^ 2 = p ^ 2 + 2 * p * q + q ^ 2 := by ring
  have e2 : (1 + 1 / L) * F + (1 + L) * G = p ^ 2 + p ^ 2 / L + q ^ 2 + L * q ^ 2 := by
    rw [← hp2, ← hq2]; ring
  rw [e1, e2]
  linarith

set_option maxHeartbeats 1000000 in
theorem AS_arith (Fa Fb GE Hw Br Bm Ring Ed Ga l2a l2b hole U Lc logK lam C₁ Cb C₂ C₃ C₄ Q2 : ℝ)
    (hFb0 : 0 ≤ Fb) (hGE0 : 0 ≤ GE) (hHw0 : 0 ≤ Hw) (hBr0 : 0 ≤ Br) (hRing0 : 0 ≤ Ring) (hU : 0 ≤ U)
    (hLc : 1 ≤ Lc) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlamL : 1 / Lc ≤ lam) (hQ2 : 0 ≤ Q2)
    (hl2b0 : 0 ≤ l2b) (hhole0 : 0 ≤ hole) (hC₁ : 0 ≤ C₁) (hCb : 0 ≤ Cb) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hC₄ : 0 ≤ C₄) (hlogK : 0 ≤ logK) (hlogKL : logK ≤ Lc)
    (hA : Fa ≤ (Real.sqrt Fb + Real.sqrt GE) ^ 2)
    (hcore : Fb ≤ Hw * (1 + Br) * (l2b - hole) + Bm * Ring + Ed + Ga)
    (hhole : l2b - hole ≤ U * (Lc + logK + C₁)) (hl2ba : l2b ≤ l2a)
    (hBr : Br ≤ Cb * lam) (hBm : Bm ≤ Q2 * (1 + lam))
    (hEd : Ed ≤ C₂ * Hw * U) (hGa : Ga ≤ C₃ * Hw * U) (hGE : GE ≤ C₄ * Hw * U / Lc) :
    Fa ≤ Hw * U * (Lc + logK + (2 * C₁ + 2 + 2 * C₂ + 2 * C₃ + 2 * C₄)) + Q2 * (1 + 4 * lam) * Ring
      + (2 * Cb) * lam * Hw * l2a := by
  have hLc0 : 0 < Lc := by linarith
  set τ := 1 / Lc with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hτlam : τ ≤ lam := hlamL
  have hτLc : τ * Lc = 1 := by rw [hτ, one_div_mul_cancel hLc0.ne']
  have hτlog : τ * logK ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hlogKL hτ0
    linarith
  have hHU : 0 ≤ Hw * U := mul_nonneg hHw0 hU
  have hl2a0 : 0 ≤ l2a := le_trans hl2b0 hl2ba
  have hsq := sq_sqrt_add_le Fb GE Lc hFb0 hGE0 hLc0
  -- the core
  have hmain : Hw * (l2b - hole) ≤ Hw * U * (Lc + logK + C₁) := by
    have := mul_le_mul_of_nonneg_left hhole hHw0
    linarith [mul_assoc Hw U (Lc + logK + C₁)]
  have hBrt : Hw * Br * (l2b - hole) ≤ Cb * lam * Hw * l2a := by
    have h1 : l2b - hole ≤ l2a := by linarith
    rcases le_or_gt 0 (l2b - hole) with h2 | h2
    · have := mul_le_mul (mul_le_mul_of_nonneg_left hBr hHw0) h1 h2 (mul_nonneg hHw0 (by positivity))
      linarith [show Hw * (Cb * lam) * l2a = Cb * lam * Hw * l2a by ring]
    · have : Hw * Br * (l2b - hole) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hHw0 hBr0) h2.le
      have : 0 ≤ Cb * lam * Hw * l2a := by positivity
      linarith
  have hR : Bm * Ring ≤ Q2 * (1 + lam) * Ring := mul_le_mul_of_nonneg_right hBm hRing0
  set M1 := Hw * U * (Lc + logK + C₁) with hM1
  set M2 := Cb * lam * Hw * l2a with hM2
  set M3 := Q2 * (1 + lam) * Ring with hM3
  set M4 := C₂ * Hw * U + C₃ * Hw * U with hM4
  have hcore' : Fb ≤ M1 + M2 + M3 + M4 := by
    have e : Hw * (1 + Br) * (l2b - hole) = Hw * (l2b - hole) + Hw * Br * (l2b - hole) := by ring
    linarith
  have hM2n : 0 ≤ M2 := by positivity
  have hM3' : 0 ≤ M3 := by positivity
  have hM4' : 0 ≤ M4 := by positivity
  have hM1' : 0 ≤ M1 := by positivity
  -- multiply by `1 + τ`
  have h1 : (1 + τ) * Fb ≤ (1 + τ) * (M1 + M2 + M3 + M4) := mul_le_mul_of_nonneg_left hcore' (by linarith)
  have t1 : (1 + τ) * M1 ≤ Hw * U * (Lc + logK + (2 * C₁ + 2)) := by
    have e : (1 + τ) * M1 = Hw * U * (Lc + logK + C₁ + (τ * Lc + τ * logK + τ * C₁)) := by rw [hM1]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hHU
    have : τ * C₁ ≤ C₁ := mul_le_of_le_one_left hC₁ (le_trans hτlam hlam1)
    linarith
  have t2 : (1 + τ) * M2 ≤ 2 * Cb * lam * Hw * l2a := by
    have hτ1 : τ ≤ 1 := le_trans hτlam hlam1
    have : (1 + τ) * M2 ≤ 2 * M2 := mul_le_mul_of_nonneg_right (by linarith) hM2n
    linarith [show 2 * M2 = 2 * Cb * lam * Hw * l2a by rw [hM2]; ring]
  have t3 : (1 + τ) * M3 ≤ Q2 * (1 + 4 * lam) * Ring := by
    have h0 : 0 ≤ Q2 * Ring := mul_nonneg hQ2 hRing0
    have e : (1 + τ) * M3 = Q2 * Ring * ((1 + τ) * (1 + lam)) := by rw [hM3]; ring
    have e2 : Q2 * (1 + 4 * lam) * Ring = Q2 * Ring * (1 + 4 * lam) := by ring
    rw [e, e2]
    apply mul_le_mul_of_nonneg_left _ h0
    have : τ * lam ≤ lam := mul_le_of_le_one_left hlam0 (le_trans hτlam hlam1)
    have e3 : (1 + τ) * (1 + lam) = 1 + lam + τ + τ * lam := by ring
    rw [e3]; linarith
  have t4 : (1 + τ) * M4 ≤ 2 * C₂ * Hw * U + 2 * C₃ * Hw * U := by
    have hτ1 : τ ≤ 1 := le_trans hτlam hlam1
    have : (1 + τ) * M4 ≤ 2 * M4 := mul_le_mul_of_nonneg_right (by linarith) hM4'
    linarith [show 2 * M4 = 2 * C₂ * Hw * U + 2 * C₃ * Hw * U by rw [hM4]; ring]
  have t5 : (1 + Lc) * GE ≤ 2 * C₄ * Hw * U := by
    have h1 : (1 + Lc) * GE ≤ (1 + Lc) * (C₄ * Hw * U / Lc) := mul_le_mul_of_nonneg_left hGE (by linarith)
    have h2 : (1 + Lc) * (C₄ * Hw * U / Lc) = C₄ * Hw * U * (1 + τ) := by rw [hτ]; field_simp; ring
    have hC4HU : 0 ≤ C₄ * Hw * U := by positivity
    have hτ1 : τ ≤ 1 := le_trans hτlam hlam1
    have h3 : C₄ * Hw * U * (1 + τ) ≤ C₄ * Hw * U * 2 := mul_le_mul_of_nonneg_left (by linarith) hC4HU
    linarith
  have e1 : (1 + τ) * (M1 + M2 + M3 + M4) = (1 + τ) * M1 + (1 + τ) * M2 + (1 + τ) * M3 + (1 + τ) * M4 := by ring
  have e2 : (1 + 1 / Lc) * Fb = (1 + τ) * Fb := rfl
  have hfin : Hw * U * (Lc + logK + (2 * C₁ + 2 + 2 * C₂ + 2 * C₃ + 2 * C₄))
      = Hw * U * (Lc + logK + (2 * C₁ + 2)) + 2 * C₂ * Hw * U + 2 * C₃ * Hw * U + 2 * C₄ * Hw * U := by ring
  rw [hfin]
  linarith

end ASc
end ShellS
end ZetaShell
