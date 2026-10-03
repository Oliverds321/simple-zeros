/-
L7_3 (round 5): **the arithmetic of the in-zone and cross half** (for F1c-2 `shell_inzone`). ZetaQ's
`InZone.final_arith` bounds the whole PP block; this is its in-zone-and-cross part alone: with `M = XWk₀/2`,
  `2(1+ε₀)K·P_z ≤ (1+δ)⁴·W k₀ 𝒩`,  `2(1+1/ε₀)B·R_z ≤ 32δC·W𝒩`,  `2B·N_r ≤ δ(16C + 2)·W𝒩`,
so the sum is `≤ W(k₀ + η)𝒩` once `δ(48C + 32) ≤ η` (`ε₀ ≤ δ ≤ 1`, `k₀ ≤ 2`, `k ≤ 2`). Pure real arithmetic.
-/
import ZetaShell.ShellK.LF_Defs

namespace ZetaShell
namespace ShellK
namespace F1c

set_option maxHeartbeats 1000000 in
theorem inzone_arith {B K Pz Rz Dr Nr ρ M X W N C k k0 E ε₀ δ η : ℝ}
    (hN : 2 * Nr ≤ ρ * Dr) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ δ) (hD0 : 0 ≤ Dr)
    (hD : Dr ≤ (X * W * k + E) * (1 + δ)) (hE : B * E ≤ δ * W * N) (hE0 : 0 ≤ E)
    (hPz0 : 0 ≤ Pz) (hP2 : Pz ≤ M * (1 + ε₀)) (hR : Rz ≤ ε₀ ^ 2 * Pz)
    (hM : 2 * M = X * W * k0) (hM0 : 0 ≤ M)
    (hε₀ : 0 < ε₀) (hε₀δ : ε₀ ≤ δ) (hδ1 : δ ≤ 1)
    (hK0 : 0 ≤ K) (hKB : K ≤ B) (hBX : B * X ≤ (1 + δ) ^ 2 * C * N)
    (hKX : K * X ≤ (1 + δ) ^ 2 * N)
    (hk0 : 0 ≤ k0) (hk02 : k0 ≤ 2) (hk : 0 ≤ k) (hk2 : k ≤ 2) (hC : 0 < C)
    (hW : 0 ≤ W) (hNn : 0 ≤ N) (hX : 0 ≤ X)
    (hδη : δ * (48 * C + 32) ≤ η) :
    2 * ((1 + ε₀) * (K * Pz) + (1 + 1 / ε₀) * (B * Rz)) + 2 * B * Nr ≤ W * (k0 + η) * N := by
  have hδ0 : 0 < δ := lt_of_lt_of_le hε₀ hε₀δ
  have hε₀1 : ε₀ ≤ 1 := hε₀δ.trans hδ1
  have hB0 : 0 ≤ B := hK0.trans hKB
  have hWN : 0 ≤ W * N := mul_nonneg hW hNn
  have hWk0 : 0 ≤ W * k0 := mul_nonneg hW hk0
  -- `(1+δ)² ≤ 4`, `(1+δ)⁴ ≤ 1 + 15δ`
  have hδδ : δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ1 hδ0.le
  have hεε : ε₀ * ε₀ ≤ ε₀ * 1 := mul_le_mul_of_nonneg_left hε₀1 hε₀.le
  have hd2 : (1 + δ) ^ 2 ≤ 1 + 3 * δ := by linarith
  have hd24 : (1 + δ) ^ 2 ≤ 4 := by linarith
  -- T1: `2(1+ε₀)K·P_z ≤ (1+ε₀)²(1+δ)²·W k₀ N`
  have a1 : K * Pz ≤ K * (M * (1 + ε₀)) := mul_le_mul_of_nonneg_left hP2 hK0
  have a2 : 2 * (K * M) = (K * X) * (W * k0) := by
    have : 2 * (K * M) = K * (2 * M) := by ring
    rw [this, hM]; ring
  have a3 : (K * X) * (W * k0) ≤ ((1 + δ) ^ 2 * N) * (W * k0) := mul_le_mul_of_nonneg_right hKX hWk0
  have hq1 : (1 + ε₀) ^ 2 ≤ 1 + 3 * δ := by linarith
  have hA : 2 * ((1 + ε₀) * (K * Pz)) ≤ (1 + ε₀) ^ 2 * ((1 + δ) ^ 2 * N * (W * k0)) := by
    have h1 : 2 * ((1 + ε₀) * (K * Pz)) ≤ 2 * ((1 + ε₀) * (K * (M * (1 + ε₀)))) := by
      have := mul_le_mul_of_nonneg_left a1 (by linarith : (0 : ℝ) ≤ 1 + ε₀)
      linarith
    have h2 : 2 * ((1 + ε₀) * (K * (M * (1 + ε₀)))) = (1 + ε₀) ^ 2 * (2 * (K * M)) := by ring
    have h3 : (1 + ε₀) ^ 2 * (2 * (K * M)) ≤ (1 + ε₀) ^ 2 * ((1 + δ) ^ 2 * N * (W * k0)) := by
      rw [a2]
      exact mul_le_mul_of_nonneg_left (by linarith [a3]) (sq_nonneg _)
    linarith
  -- `(1+ε₀)²(1+δ)² ≤ (1+3δ)² ≤ 1 + 15δ`
  have hprod : (1 + ε₀) ^ 2 * (1 + δ) ^ 2 ≤ 1 + 15 * δ := by
    have h1 : (1 + ε₀) ^ 2 * (1 + δ) ^ 2 ≤ (1 + 3 * δ) * (1 + 3 * δ) :=
      mul_le_mul hq1 hd2 (sq_nonneg _) (by linarith)
    linarith
  have hNWk0 : 0 ≤ N * (W * k0) := mul_nonneg hNn hWk0
  have hT1 : 2 * ((1 + ε₀) * (K * Pz)) ≤ W * k0 * N + 30 * δ * (W * N) := by
    have h1 : (1 + ε₀) ^ 2 * ((1 + δ) ^ 2 * N * (W * k0))
        = ((1 + ε₀) ^ 2 * (1 + δ) ^ 2) * (N * (W * k0)) := by ring
    have h2 : ((1 + ε₀) ^ 2 * (1 + δ) ^ 2) * (N * (W * k0)) ≤ (1 + 15 * δ) * (N * (W * k0)) :=
      mul_le_mul_of_nonneg_right hprod hNWk0
    have h3 : N * (W * k0) ≤ 2 * (W * N) := by
      have := mul_le_mul_of_nonneg_left hk02 hWN
      linarith
    have h4 : 15 * δ * (N * (W * k0)) ≤ 15 * δ * (2 * (W * N)) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    linarith
  -- T2: `2(1+1/ε₀)B·R_z ≤ 32δC·W𝒩`
  have hT2 : 2 * ((1 + 1 / ε₀) * (B * Rz)) ≤ 32 * δ * C * (W * N) := by
    have b1 : B * Rz ≤ B * (ε₀ ^ 2 * Pz) := mul_le_mul_of_nonneg_left hR hB0
    have b2 : 2 * ((1 + 1 / ε₀) * (B * (ε₀ ^ 2 * Pz))) = 2 * (ε₀ ^ 2 + ε₀) * (B * Pz) := by
      field_simp
    have b3 : 2 * ((1 + 1 / ε₀) * (B * Rz)) ≤ 2 * ((1 + 1 / ε₀) * (B * (ε₀ ^ 2 * Pz))) := by
      have hpos : 0 ≤ 1 + 1 / ε₀ := by positivity
      have := mul_le_mul_of_nonneg_left b1 hpos
      linarith
    have b4 : B * Pz ≤ B * (M * (1 + ε₀)) := mul_le_mul_of_nonneg_left hP2 hB0
    have b5 : B * (M * (1 + ε₀)) ≤ B * (2 * M) := by
      apply mul_le_mul_of_nonneg_left _ hB0
      have := mul_le_mul_of_nonneg_left hε₀1 hM0
      linarith
    have b6 : B * (2 * M) = (B * X) * (W * k0) := by rw [hM]; ring
    have b7 : (B * X) * (W * k0) ≤ ((1 + δ) ^ 2 * C * N) * (W * k0) := mul_le_mul_of_nonneg_right hBX hWk0
    have b8 : ((1 + δ) ^ 2 * C * N) * (W * k0) ≤ (4 * C * N) * (W * 2) := by
      apply mul_le_mul _ _ hWk0 (by positivity)
      · have := mul_le_mul_of_nonneg_right hd24 (mul_nonneg hC.le hNn)
        linarith
      · exact mul_le_mul_of_nonneg_left hk02 hW
    have b9 : 2 * (ε₀ ^ 2 + ε₀) ≤ 4 * δ := by linarith
    have hBPz0 : 0 ≤ B * Pz := mul_nonneg hB0 hPz0
    have b10 : 2 * (ε₀ ^ 2 + ε₀) * (B * Pz) ≤ 4 * δ * (B * Pz) := mul_le_mul_of_nonneg_right b9 hBPz0
    have b11 : B * Pz ≤ 8 * C * (W * N) := by linarith
    have b12 : 4 * δ * (B * Pz) ≤ 4 * δ * (8 * C * (W * N)) := mul_le_mul_of_nonneg_left b11 (by linarith)
    rw [b2] at b3
    linarith
  -- T3: `2B·N_r ≤ δ(16C + 2)·W𝒩`
  have hT3 : 2 * B * Nr ≤ δ * (16 * C + 2) * (W * N) := by
    have c1 : 2 * B * Nr ≤ B * (ρ * Dr) := by
      have := mul_le_mul_of_nonneg_left hN hB0
      linarith
    have c2 : B * (ρ * Dr) ≤ B * (δ * Dr) := by
      apply mul_le_mul_of_nonneg_left _ hB0
      exact mul_le_mul_of_nonneg_right hρ hD0
    have c3 : B * (δ * Dr) ≤ B * (δ * ((X * W * k + E) * (1 + δ))) := by
      apply mul_le_mul_of_nonneg_left _ hB0
      exact mul_le_mul_of_nonneg_left hD hδ0.le
    have c4 : B * (δ * ((X * W * k + E) * (1 + δ))) = δ * (1 + δ) * ((B * X) * (W * k) + B * E) := by ring
    have hWk : 0 ≤ W * k := mul_nonneg hW hk
    have c5 : (B * X) * (W * k) ≤ ((1 + δ) ^ 2 * C * N) * (W * k) := mul_le_mul_of_nonneg_right hBX hWk
    have c6 : ((1 + δ) ^ 2 * C * N) * (W * k) ≤ (4 * C * N) * (W * 2) := by
      apply mul_le_mul _ _ hWk (by positivity)
      · have := mul_le_mul_of_nonneg_right hd24 (mul_nonneg hC.le hNn)
        linarith
      · exact mul_le_mul_of_nonneg_left hk2 hW
    have c7 : B * E ≤ W * N := by
      have := mul_le_mul_of_nonneg_right hδ1 hWN
      linarith
    have c8 : (B * X) * (W * k) + B * E ≤ (8 * C + 1) * (W * N) := by linarith
    have c9 : δ * (1 + δ) ≤ 2 * δ := by linarith
    have c10 : 0 ≤ (B * X) * (W * k) + B * E := by
      have := mul_nonneg hB0 hX
      have := mul_nonneg hB0 hE0
      positivity
    have c11 : δ * (1 + δ) * ((B * X) * (W * k) + B * E) ≤ 2 * δ * ((8 * C + 1) * (W * N)) := by
      apply mul_le_mul c9 c8 c10 (by linarith)
    linarith
  -- total
  have hfin : W * k0 * N + 30 * δ * (W * N) + 32 * δ * C * (W * N) + δ * (16 * C + 2) * (W * N)
      ≤ W * (k0 + η) * N := by
    have h1 : δ * (48 * C + 32) * (W * N) ≤ η * (W * N) := mul_le_mul_of_nonneg_right hδη hWN
    linarith
  have e : 2 * ((1 + ε₀) * (K * Pz) + (1 + 1 / ε₀) * (B * Rz)) + 2 * B * Nr
      = 2 * ((1 + ε₀) * (K * Pz)) + 2 * ((1 + 1 / ε₀) * (B * Rz)) + 2 * B * Nr := by ring
  rw [e]
  linarith [hT1, hT2, hT3, hfin]

end F1c
end ShellK
end ZetaShell
