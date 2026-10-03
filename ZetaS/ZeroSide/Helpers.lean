/-
lean_work/L3_1/ZeroSideHelpers.lean — shared helpers for the zero-side nodes Z1, Z2, Z3, Z8 (agent L3_1, 28 Sep 2026).

  * `hasSum_uR_mul`          — Poisson over the FULL lattice k ∈ ℤ in the normalisation of `InterfacesV2` §2:
                               Σ_{k∈ℤ} u_γ(k) u_γ′(k) = kWin((γ − γ′)L/2π)  (tree `AdmWindow.hasSum_vHatR_mul`,
                               divided by L∫v²; draft eq:zeta-poisson).
  * `sum_fin_add_tsum_offGrid` — splitting a summable ℤ-series into the grid block [0, d) and `offGrid d`.
  * `posSemidef_of_hasSum`   — a Gram matrix of ℓ²-type families (entries given as `HasSum`s) is PSD.
  * `vHat_conj`, `uC_ofReal` — reflection v̂(z̄) = conj v̂(z) for a real even window; `uC` at a real ordinate is `uR`.
  * `kWin_zero`, `kWin_even` — kWin 0 = 1 (needs ∫v² ≠ 0), kWin even.
  * `integral_sq_pos`        — ∫v² > 0 as soon as v is not identically 0 (for the Z2 fix).
  * `sum_sq_add_deltaW`, `deltaW_nonneg`, `deltaW_le_one` — lem:sigd-residue (i): Σ_{k<d} u_γ(k)² = 1 − δ_γ, 0 ≤ δ_γ ≤ 1.
  * `gram_eq_matrix`, `offGrid_diag` — Z1 in the exact matrix shape of `ZeroFrame.gram_eq` (x_i = γ_i L/2π), and
                               `Etr i i = deltaW` (for Z9).

Compile: bash lean_tools/leanrun.sh ZeroSideHelpers.lean <L3_1>/olean -- -o <L3_1>/olean/ZeroSideHelpers.olean
-/
import ZetaS.InterfacesV2

noncomputable section

open scoped BigOperators
open Matrix

namespace ZetaS

namespace ZeroSide

variable {v : ℝ → ℝ} {L w c : ℝ}

/-- Poisson over the full lattice, normalised: `Σ_{k∈ℤ} u_γ(k) u_γ′(k) = kWin v L ((γ − γ′)L/2π)`. -/
theorem hasSum_uR_mul (hW : Zeta23.AdmWindow v L w c) (T γ γ' : ℝ) :
    HasSum (fun k : ℤ => uR v L T γ k * uR v L T γ' k) (kWin v L ((γ - γ') * L / (2 * Real.pi))) := by
  have hL : 0 < L := hW.L_pos
  have hL0 : L ≠ 0 := hL.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hI : 0 ≤ ∫ u, v u ^ 2 := MeasureTheory.integral_nonneg fun u => sq_nonneg _
  have hD : 0 ≤ L * ∫ u, v u ^ 2 := mul_nonneg hL.le hI
  have h := (hW.hasSum_vHatR_mul T γ γ').div_const (L * ∫ u, v u ^ 2)
  have hfun : (fun k : ℤ => uR v L T γ k * uR v L T γ' k) = fun k : ℤ =>
      Zeta23.AdmWindow.vHatR v (γ - (T + k * (2 * Real.pi / L))) *
        Zeta23.AdmWindow.vHatR v (γ' - (T + k * (2 * Real.pi / L))) / (L * ∫ u, v u ^ 2) := by
    funext k
    simp only [uR]
    rw [div_mul_div_comm, Real.mul_self_sqrt hD]
  have e : kWin v L ((γ - γ') * L / (2 * Real.pi))
      = L * Zeta23.AdmWindow.VPhiR v (γ - γ') / (L * ∫ u, v u ^ 2) := by
    unfold kWin
    rw [show 2 * Real.pi * ((γ - γ') * L / (2 * Real.pi)) / L = γ - γ' by field_simp]
    rw [mul_div_mul_left _ _ hL0]
  rw [hfun, e]
  exact h

/-- Split a summable ℤ-series into the grid block `[0, d)` and the off-grid indices. -/
theorem sum_fin_add_tsum_offGrid {f : ℤ → ℝ} (hf : Summable f) (d : ℕ) :
    ∑ k : Fin d, f ((k : ℕ) : ℤ) + ∑' k : offGrid d, f k.1 = ∑' k, f k := by
  set s : Finset ℤ := (Finset.range d).map ⟨((↑) : ℕ → ℤ), Nat.cast_injective⟩ with hs
  have h1 : ∑ k : Fin d, f ((k : ℕ) : ℤ) = ∑ x ∈ s, f x := by
    rw [hs, Finset.sum_map]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ℤ)) d
  have hmem : ∀ x : ℤ, (x < 0 ∨ (d : ℤ) ≤ x) ↔ x ∈ ((s : Set ℤ)ᶜ) := by
    intro x
    simp only [hs, Set.mem_compl_iff, Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Function.Embedding.coeFn_mk, not_exists, not_and]
    constructor
    · rintro h n hn rfl
      omega
    · intro h
      by_contra h'
      exact h x.toNat (by omega) (by omega)
  have h2 : ∑' k : offGrid d, f k.1 = ∑' x : ↑((s : Set ℤ)ᶜ), f x :=
    (Equiv.subtypeEquivRight hmem).tsum_eq (fun x : ↑((s : Set ℤ)ᶜ) => f x)
  rw [h1, h2]
  exact hf.sum_add_tsum_compl

/-- A Gram matrix of ℓ²-type families is positive semidefinite: if `M i j = Σ_k u_i(k) u_j(k)` (as `HasSum`),
then `M ⪰ 0`. -/
theorem posSemidef_of_hasSum {ι : Type*} {n : ℕ} (u : Fin n → ι → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, HasSum (fun k => u i k * u j k) (M i j)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial]
    refine (hM j i).unique ?_
    simpa only [mul_comm] using hM i j
  · intro x
    simp only [star_trivial]
    have h : HasSum (fun k => ∑ i, ∑ j, x i * (u i k * u j k) * x j) (∑ i, ∑ j, x i * M i j * x j) := by
      refine hasSum_sum fun i _ => hasSum_sum fun j _ => ?_
      exact ((hM i j).mul_left (x i)).mul_right (x j)
    have hs : HasSum (fun k => (∑ i, x i * u i k) ^ 2) (x ⬝ᵥ (M *ᵥ x)) := by
      convert h using 1
      · funext k
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      · simp only [dotProduct, mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    exact hs.nonneg fun k => sq_nonneg _

/-- Reflection for a real even window: `v̂(z̄) = conj v̂(z)` (tree `conj_paperFT_ofReal`, `paperFT_neg_of_even`). -/
theorem vHat_conj (hW : Zeta23.AdmWindow v L w c) (z : ℂ) :
    Zeta23.AdmWindow.vHat v ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Zeta23.AdmWindow.vHat v z) := by
  unfold Zeta23.AdmWindow.vHat
  rw [Zeta23.Taper.conj_paperFT_ofReal, Zeta23.Taper.paperFT_neg_of_even hW.even]

/-- `uC` at a real ordinate is `uR` (so the on-line vectors of `ZeroFrame` may be taken real). -/
theorem uC_ofReal (hW : Zeta23.AdmWindow v L w c) (T γ : ℝ) (k : ℤ) :
    uC v L T (γ : ℂ) k = (uR v L T γ k : ℂ) := by
  have h := hW.vHat_ofReal' (γ - (T + k * (2 * Real.pi / L)))
  push_cast at h
  rw [uC, uR, h, Complex.ofReal_div]

/-- `kWin 0 = 1` — needs the nondegeneracy `∫ v² ≠ 0` (false for the admissible window `v = 0`). -/
theorem kWin_zero (hW : Zeta23.AdmWindow v L w c) (hv : ∫ u, v u ^ 2 ≠ 0) : kWin v L 0 = 1 := by
  have hL0 : L ≠ 0 := hW.L_pos.ne'
  simp only [kWin, mul_zero, zero_div]
  rw [hW.VPhiR_zero, Zeta23.AdmWindow.av]
  field_simp

theorem kWin_even (hW : Zeta23.AdmWindow v L w c) (t : ℝ) : kWin v L (-t) = kWin v L t := by
  simp only [kWin]
  rw [show 2 * Real.pi * -t / L = -(2 * Real.pi * t / L) by ring, hW.VPhiR_even]

/-- `∫ v² > 0` for an admissible window that is not identically zero. -/
theorem integral_sq_pos (hW : Zeta23.AdmWindow v L w c) {u₀ : ℝ} (h : v u₀ ≠ 0) : 0 < ∫ u, v u ^ 2 :=
  hW.sq_continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hW.sq_hasCompactSupport
    (fun u => sq_nonneg (v u)) (pow_ne_zero 2 h)

/-- lem:sigd-residue (i): `Σ_{k<d} u_γ(k)² + δ_γ = 1` (given `∫ v² ≠ 0`). -/
theorem sum_sq_add_deltaW (hW : Zeta23.AdmWindow v L w c) (hv : ∫ u, v u ^ 2 ≠ 0) (T : ℝ) (d : ℕ) (γ : ℝ) :
    ∑ k : Fin d, uR v L T γ (k : ℕ) ^ 2 + deltaW v L T d γ = 1 := by
  have h := hasSum_uR_mul hW T γ γ
  rw [sub_self, zero_mul, zero_div, kWin_zero hW hv] at h
  have := sum_fin_add_tsum_offGrid h.summable d
  rw [h.tsum_eq] at this
  simpa only [deltaW, sq] using this

/-- Z1 in the matrix shape of `ZeroFrame.gram_eq`/`GramData.gram_eq`: with `U k i = u_{γ_i}(k)` (k < d),
`x i = γ_i L/2π` and `Etr` the off-grid Gram matrix, `Uᵀ U = kerMat (kWin v L) x − Etr`. -/
theorem gram_eq_matrix (hW : Zeta23.AdmWindow v L w c) (T : ℝ) (d : ℕ) {n : ℕ} (γ : Fin n → ℝ) :
    (Matrix.of fun (k : Fin d) (i : Fin n) => uR v L T (γ i) (k : ℕ))ᵀ *
        (Matrix.of fun (k : Fin d) (i : Fin n) => uR v L T (γ i) (k : ℕ))
      = kerMat (kWin v L) (fun i => γ i * L / (2 * Real.pi))
        - Matrix.of fun i j => ∑' k : offGrid d, uR v L T (γ i) k.1 * uR v L T (γ j) k.1 := by
  ext i j
  have h := hasSum_uR_mul hW T (γ i) (γ j)
  have hs := sum_fin_add_tsum_offGrid h.summable d
  rw [h.tsum_eq] at hs
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.sub_apply, kerMat]
  rw [show γ i * L / (2 * Real.pi) - γ j * L / (2 * Real.pi) = (γ i - γ j) * L / (2 * Real.pi) by ring]
  linarith

/-- The diagonal of the off-grid Gram matrix is the defect `deltaW` (so `ZeroFrame.delta = deltaW`). -/
theorem offGrid_diag (T : ℝ) (d : ℕ) (γ : ℝ) :
    ∑' k : offGrid d, uR v L T γ k.1 * uR v L T γ k.1 = deltaW v L T d γ := by
  simp only [deltaW, sq]

theorem deltaW_nonneg (T : ℝ) (d : ℕ) (γ : ℝ) : 0 ≤ deltaW v L T d γ :=
  tsum_nonneg fun _ => sq_nonneg _

theorem deltaW_le_one (hW : Zeta23.AdmWindow v L w c) (hv : ∫ u, v u ^ 2 ≠ 0) (T : ℝ) (d : ℕ) (γ : ℝ) :
    deltaW v L T d γ ≤ 1 := by
  have h := sum_sq_add_deltaW hW hv T d γ
  have : 0 ≤ ∑ k : Fin d, uR v L T γ (k : ℕ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

end ZeroSide

end ZetaS
