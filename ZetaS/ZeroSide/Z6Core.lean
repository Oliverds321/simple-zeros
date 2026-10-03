/-
lean_work/L3_2/Z6Core.lean — helpers and the core estimate for node Z6 (agent L3_2, 28 Sep 2026).
Used by `Z6_Defect.lean` (the skeleton statement, proved as written) and `Z6_Defect_fix.lean` (the profile form).
Original header of the proof, kept for reference:

Skeleton statement `defect_littleO` (skeleton_v2/Z6_Defect.lean) assumes only admissibility of the family. The proof
below needs a lower bound `∫φ_T² ≥ L/4` for the normalisation `u = v̂/√(L∫φ²)` (without it the decay
`|v̂(ξ)| ≤ (c/w)ξ⁻²` does not control `u`). We therefore add the three profile hypotheses that Z4/Z5 (and Z9) carry:
`Continuous ψ`, `0 ≤ ψ ≤ 1` on the core, `∫ψ > 1/2`. The hypothesis `λ < 1` is NOT used.

Proof. Let `s` be the (finite) set of on-line zeros with `γ ∈ I′ = (T − √T, 2T + √T]`, `h = 2π/L`, `D = √T`.
  * every zero: `δ_γ ≤ Σ_{k∈ℤ} u_γ(k)² = 1` (tree Poisson `hasSum_vHatR_mul` at τ = τ′ = γ, `VPhiR 0 = ∫φ²`);
  * "bulk" zeros `T + √T < γ ≤ 2T − √T − 1`: every off-grid node satisfies `|γ − τ_k| ≥ √T + j h` with `j ≥ 0` injective
    on each side, `u_γ(k)² ≤ 4(c/w)²L⁻²|γ − τ_k|⁻⁴` (tree `abs_vHatR_mul_sq_le`, `∫φ² ≥ L/4`), and the tree's grid sum
    `Σ_j (D + jh)⁻⁴ ≤ D⁻⁴ + D⁻³/(3h)` give `δ_γ ≤ 16(c/w)²/T`;
  * "edge" zeros (the rest) lie in two intervals of length ≤ 2√T + 2, so their count with multiplicity is
    ≤ (4√T + 3)·A₀ log 4T by the local count (H-RvM `local_count`); all of I′ holds ≤ 2T·A₀ log 4T.
Hence `Σ m δ ≤ A₀(7 + 32(c/w)²)·√T·log 4T ≤ 2A₀(7 + 32(c/w)²)·√T·l = o(T l) = o(N)` (tree
`isLittleO_sqrt_mul_l_Tl`, `isLittleO_N_of_isLittleO_Tl`).
-/
import ZetaS.InterfacesV2
import Zeta23.Hypotheses
import Zeta23.Tail
import Zeta23.Assembly
import ZetaS.ZeroSide.KWinHelpers

noncomputable section

open Filter Asymptotics Real Set MeasureTheory Topology

namespace ZetaS
namespace Z6

open Zeta23 Zeta23.XiPrime ProfileMoments KWinHelpers

/-! ### Counting zeros in an interval by unit windows -/

lemma sum_mult_le_N (Z : ZeroConfig) (t : ℝ) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, ρ ∈ Z.window t (t + 1)) :
    ∑ ρ ∈ s, (Z.mult ρ : ℝ) ≤ Z.N t (t + 1) := by
  classical
  have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : s ⊆ hfin.toFinset := fun x hx => (Set.Finite.mem_toFinset _).mpr (hs x hx)
  have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
  exact_mod_cast h

lemma count_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (a : ℝ) (K : ℕ) (s : Finset ℂ) (hs : ∀ ρ ∈ s, ρ ∈ Z.carrier ∧ a < ρ.im ∧ ρ.im ≤ a + K) :
    ∑ ρ ∈ s, (Z.mult ρ : ℝ) ≤ K * (A₀ * Real.log (|a| + K + 3)) := by
  classical
  apply Tail.sum_mult_le_of_windows s Z.mult (fun ρ => ⌈ρ.im - a⌉₊ - 1) K
  · intro ρ hρ
    obtain ⟨_, h1, h2⟩ := hs ρ hρ
    have hc : ⌈ρ.im - a⌉₊ ≤ K := Nat.ceil_le.mpr (by linarith)
    have hc1 : 1 ≤ ⌈ρ.im - a⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    show ⌈ρ.im - a⌉₊ - 1 < K
    omega
  · intro j hj
    refine (sum_mult_le_N Z (a + j) _ fun ρ hρ => ?_).trans ((hloc (a + j)).trans ?_)
    · simp only [Finset.mem_filter] at hρ
      obtain ⟨hρs, hρj⟩ := hρ
      obtain ⟨hc, h1, h2⟩ := hs ρ hρs
      have hc1 : 1 ≤ ⌈ρ.im - a⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
      have hceq : ⌈ρ.im - a⌉₊ = j + 1 := by omega
      have h3 := (Nat.ceil_eq_iff (by omega : j + 1 ≠ 0)).mp hceq
      have h4 : (j : ℝ) < ρ.im - a ∧ ρ.im - a ≤ (j : ℝ) + 1 := by
        simpa using h3
      exact ⟨hc, by linarith [h4.1], by linarith [h4.2]⟩
    · apply mul_le_mul_of_nonneg_left _ hA₀
      apply Real.log_le_log (by positivity)
      have hj' : |a + (j : ℝ)| ≤ |a| + j := by
        calc |a + (j : ℝ)| ≤ |a| + |(j : ℝ)| := abs_add_le _ _
          _ = |a| + j := by rw [Nat.abs_cast]
      have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj.le
      linarith

/-! ### The defect of one zero -/

lemma integral_sq_eq_Nphi {v ϱ : ℝ → ℝ} {L w : ℝ} (hv : CoreProfile v) (hϱ : TaperProfile ϱ)
    (hw : 0 < w) (hL : 0 < L) :
    ∫ u, phiM (fV v L) ϱ L w u ^ 2 = Nphi v ϱ L w 0 := by
  unfold Nphi
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  rw [phiV_sq_eq hv hϱ hw hL u]

lemma uR_sq_hasSum {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (hD : 0 < ∫ u, v u ^ 2)
    (T γ : ℝ) : HasSum (fun k : ℤ => uR v L T γ k ^ 2) 1 := by
  have h := hW.hasSum_vHatR_mul T γ γ
  rw [sub_self, hW.VPhiR_zero] at h
  have hLD : 0 < L * ∫ u, v u ^ 2 := mul_pos hW.L_pos hD
  have hav : AdmWindow.av v L * L = ∫ u, v u ^ 2 := by
    unfold AdmWindow.av; field_simp [hW.L_pos.ne']
  rw [hav] at h
  have h2 := h.div_const (L * ∫ u, v u ^ 2)
  rw [div_self hLD.ne'] at h2
  have hfun : (fun k : ℤ => uR v L T γ k ^ 2) = fun k : ℤ =>
      AdmWindow.vHatR v (γ - (T + k * (2 * π / L))) * AdmWindow.vHatR v (γ - (T + k * (2 * π / L)))
        / (L * ∫ u, v u ^ 2) := by
    funext k
    unfold uR
    rw [div_pow, Real.sq_sqrt hLD.le, sq]
  rw [hfun]
  exact h2

lemma deltaW_nonneg (v : ℝ → ℝ) (L T : ℝ) (d : ℕ) (γ : ℝ) : 0 ≤ deltaW v L T d γ :=
  tsum_nonneg fun _ => sq_nonneg _

lemma deltaW_le_one {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (hD : 0 < ∫ u, v u ^ 2)
    (T : ℝ) (d : ℕ) (γ : ℝ) : deltaW v L T d γ ≤ 1 := by
  unfold deltaW
  refine Real.tsum_le_of_sum_le (fun k => sq_nonneg _) fun s => ?_
  have h := uR_sq_hasSum hW hD T γ
  classical
  calc ∑ k ∈ s, uR v L T γ k.1 ^ 2
      = ∑ k ∈ s.image Subtype.val, uR v L T γ k ^ 2 :=
        (Finset.sum_image (f := fun k : ℤ => uR v L T γ k ^ 2) (fun x _ y _ hxy => Subtype.ext hxy)).symm
    _ ≤ 1 := sum_le_hasSum _ (fun k _ => sq_nonneg _) h

lemma uR_sq_le {v : ℝ → ℝ} {L w c κ : ℝ} (hW : AdmWindow v L w c) (hκ : 0 < κ)
    (hD : κ * L ≤ ∫ u, v u ^ 2)
    (T γ : ℝ) (k : ℤ) {ξ : ℝ} (hξ : 0 < ξ) (hk : ξ ≤ |γ - (T + k * (2 * π / L))|) :
    uR v L T γ k ^ 2 ≤ (c / w) ^ 2 / (κ * L ^ 2) * (ξ ^ 4)⁻¹ := by
  have hL := hW.L_pos
  have hκL : 0 < κ * L := mul_pos hκ hL
  have hLD : 0 < L * ∫ u, v u ^ 2 := mul_pos hL (by linarith)
  set r := γ - (T + k * (2 * π / L)) with hr
  unfold uR
  rw [← hr, div_pow, Real.sq_sqrt hLD.le]
  have h1 := hW.abs_vHatR_mul_sq_le r
  have hr2 : ξ ^ 2 ≤ r ^ 2 := by rw [← sq_abs r]; exact pow_le_pow_left₀ hξ.le hk 2
  have hv2 : AdmWindow.vHatR v r ^ 2 * ξ ^ 4 ≤ (c / w) ^ 2 := by
    have h3 : |AdmWindow.vHatR v r| * ξ ^ 2 ≤ c / w :=
      le_trans (mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)) h1
    have h0 : 0 ≤ |AdmWindow.vHatR v r| * ξ ^ 2 := by positivity
    calc AdmWindow.vHatR v r ^ 2 * ξ ^ 4 = (|AdmWindow.vHatR v r| * ξ ^ 2) ^ 2 := by
          rw [mul_pow, sq_abs]; ring
      _ ≤ (c / w) ^ 2 := pow_le_pow_left₀ h0 h3 2
  have hLI : κ * L ^ 2 ≤ L * ∫ u, v u ^ 2 := by nlinarith
  have hξ4 : 0 < ξ ^ 4 := by positivity
  rw [div_le_iff₀ hLD]
  have h5 : AdmWindow.vHatR v r ^ 2 ≤ (c / w) ^ 2 * (ξ ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hξ4]; exact hv2
  have h6 : 0 ≤ (c / w) ^ 2 / (κ * L ^ 2) * (ξ ^ 4)⁻¹ := by positivity
  calc AdmWindow.vHatR v r ^ 2 ≤ (c / w) ^ 2 * (ξ ^ 4)⁻¹ := h5
    _ = (c / w) ^ 2 / (κ * L ^ 2) * (ξ ^ 4)⁻¹ * (κ * L ^ 2) := by field_simp
    _ ≤ (c / w) ^ 2 / (κ * L ^ 2) * (ξ ^ 4)⁻¹ * (L * ∫ u, v u ^ 2) :=
        mul_le_mul_of_nonneg_left hLI h6

/-- one side of the off-grid sum: an injective relabelling into `ℕ` and the tree's grid sum. -/
lemma side_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (j : ι → ℕ) (hj : Set.InjOn j s)
    {B D h : ℝ} (hB : 0 ≤ B) (hD : 0 < D) (hh : 0 < h)
    (hf : ∀ i ∈ s, f i ≤ B * ((D + j i * h) ^ 4)⁻¹) :
    ∑ i ∈ s, f i ≤ B * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
  classical
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, B * ((D + j i * h) ^ 4)⁻¹ := Finset.sum_le_sum hf
    _ = B * ∑ n ∈ s.image j, ((D + n * h) ^ 4)⁻¹ := by
        rw [Finset.sum_image hj, Finset.mul_sum]
    _ ≤ B * ∑ n ∈ Finset.range ((s.image j).sup id + 1), ((D + n * h) ^ 4)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hB
        · intro n hn
          rw [Finset.mem_range]
          have := Finset.le_sup (f := id) hn
          simp only [id] at this
          omega
        · intro n _ _; positivity
    _ ≤ B * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) :=
        mul_le_mul_of_nonneg_left (Tail.sum_inv_pow_four_le hD hh _) hB

lemma deltaW_le_bulk {v : ℝ → ℝ} {L w c κ : ℝ} (hW : AdmWindow v L w c) (hκ : 0 < κ)
    (hDv : κ * L ≤ ∫ u, v u ^ 2)
    (T : ℝ) (d : ℕ) (γ D : ℝ) (hD : 0 < D)
    (hlo : ∀ k : ℤ, k < 0 → D + ((-k - 1).toNat : ℝ) * (2 * π / L) ≤ |γ - (T + k * (2 * π / L))|)
    (hhi : ∀ k : ℤ, (d : ℤ) ≤ k → D + ((k - d).toNat : ℝ) * (2 * π / L) ≤ |γ - (T + k * (2 * π / L))|) :
    deltaW v L T d γ ≤ 2 * ((c / w) ^ 2 / (κ * L ^ 2) * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * (2 * π / L)))) := by
  classical
  have hL := hW.L_pos
  have hh : 0 < 2 * π / L := by positivity
  set B := (c / w) ^ 2 / (κ * L ^ 2) with hBdef
  have hB : 0 ≤ B := by positivity
  unfold deltaW
  refine Real.tsum_le_of_sum_le (fun k => sq_nonneg _) fun s => ?_
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k : offGrid d => k.1 < 0)]
  have hpos : ∀ n : ℕ, 0 < D + n * (2 * π / L) := fun n => by positivity
  have hlo' : ∑ k ∈ s.filter (fun k : offGrid d => k.1 < 0), uR v L T γ k.1 ^ 2
      ≤ B * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * (2 * π / L))) := by
    refine side_sum_le _ _ (fun k : offGrid d => (-k.1 - 1).toNat) ?_ hB hD hh ?_
    · intro k hk k' hk' he
      simp only [Finset.mem_coe, Finset.mem_filter] at hk hk'
      have h1 : ((-k.1 - 1).toNat : ℤ) = -k.1 - 1 := Int.toNat_of_nonneg (by omega)
      have h2 : ((-k'.1 - 1).toNat : ℤ) = -k'.1 - 1 := Int.toNat_of_nonneg (by omega)
      simp only at he
      apply Subtype.ext
      omega
    · intro k hk
      simp only [Finset.mem_filter] at hk
      exact uR_sq_le hW hκ hDv T γ k.1 (hpos _) (hlo k.1 hk.2)
  have hhi' : ∑ k ∈ s.filter (fun k : offGrid d => ¬ k.1 < 0), uR v L T γ k.1 ^ 2
      ≤ B * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * (2 * π / L))) := by
    refine side_sum_le _ _ (fun k : offGrid d => (k.1 - d).toNat) ?_ hB hD hh ?_
    · intro k hk k' hk' he
      simp only [Finset.mem_coe, Finset.mem_filter] at hk hk'
      have hk1 : (d : ℤ) ≤ k.1 := by rcases k.2 with h | h <;> omega
      have hk1' : (d : ℤ) ≤ k'.1 := by rcases k'.2 with h | h <;> omega
      have h1 : ((k.1 - d).toNat : ℤ) = k.1 - d := Int.toNat_of_nonneg (by omega)
      have h2 : ((k'.1 - d).toNat : ℤ) = k'.1 - d := Int.toNat_of_nonneg (by omega)
      simp only at he
      apply Subtype.ext
      omega
    · intro k hk
      simp only [Finset.mem_filter] at hk
      have hk1 : (d : ℤ) ≤ k.1 := by rcases k.2 with h | h <;> omega
      exact uR_sq_le hW hκ hDv T γ k.1 (hpos _) (hhi k.1 hk1)
  linarith

/-! ### Grid geometry -/

lemma toNat_cast_real (n : ℤ) (hn : 0 ≤ n) : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
  have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn
  rw [← this]; push_cast; rfl

/-- `d·h > T − h` for `d = ⌊LT/2π⌋₊`, `h = 2π/L`. -/
lemma d_mul_h_gt {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) :
    T - 2 * π / L < (⌊L * T / (2 * π)⌋₊ : ℝ) * (2 * π / L) := by
  have h1 := Nat.lt_floor_add_one (L * T / (2 * π))
  have hh : 0 < 2 * π / L := by positivity
  have : L * T / (2 * π) * (2 * π / L) = T := by field_simp
  nlinarith

/-! ### The node -/

set_option maxHeartbeats 1600000 in
/-- **Z6 core.** The defect sum is `o(N)` as soon as the family is admissible and `∫φ_T² ≥ κ·L(T)` eventually. -/
theorem defect_core (Z : Zeta23.ZeroConfig) (H : Zeta23.PaperInputs Z) {P : Zeta23.Params}
    (hP : P.Valid) {ψ : ℝ → ℝ} {c κ : ℝ} (hκ : 0 < κ)
    (hadm : ∀ T, 8 * P.w ≤ P.L T → Zeta23.AdmWindow (P.phiV ψ T) (P.L T) P.w c)
    (hlow : ∀ᶠ T in atTop, κ * P.L T ≤ ∫ u, P.phiV ψ T u ^ 2) :
    (fun T => ∑ᶠ ρ ∈ Z.window (T - Real.sqrt T) (2 * T + Real.sqrt T) ∩ {ρ : ℂ | ρ.re = 1 / 2},
        (Z.mult ρ : ℝ) * deltaW (P.phiV ψ T) (P.L T) T (P.d T) ρ.im)
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hA₀0 : 0 ≤ A₀ := by linarith
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hLt : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hw := hP.one_le_w
  have hw0 : 0 < P.w := by linarith
  refine Assembly.isLittleO_N_of_isLittleO_Tl Z H.RvM ?_
  refine IsBigO.trans_isLittleO ?_ Assembly.isLittleO_sqrt_mul_l_Tl
  set C₂ := (c / P.w) ^ 2 / κ with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set K := A₀ * (7 + 8 * C₂) with hK
  refine IsBigO.of_bound (2 * K) ?_
  filter_upwards [hLt.eventually_ge_atTop (8 * P.w), hLt.eventually_ge_atTop (2 * π),
    eventually_ge_atTop Tail.T₀, hlow] with T h8 h2π hT hlowT
  have hT300 : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set L := P.L T with hLdef
  have hL : 0 < L := by linarith [Real.pi_pos]
  set h := 2 * π / L with hhdef
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := by rw [hhdef, div_le_one hL]; linarith
  have hW := hadm T h8
  have hc0 : 0 ≤ c := hW.c_nonneg
  set φ := P.phiV ψ T with hφ
  -- the normalisation `∫φ² ≥ L/4`
  have hDv : κ * L ≤ ∫ u, φ u ^ 2 := hlowT
  have hDv0 : 0 < ∫ u, φ u ^ 2 := lt_of_lt_of_le (mul_pos hκ hL) hDv
  -- √T facts
  set D := Real.sqrt T with hDdef
  have hD2 : D ^ 2 = T := Real.sq_sqrt hT0
  have hD17 : 17 ≤ D := by
    rw [hDdef, Real.le_sqrt (by norm_num) hT0]; linarith
  have hDT : D ≤ T := by nlinarith
  have hlog4 : 1 ≤ Real.log (4 * T) := Tail.one_le_log_four_mul hT
  have hlogl : Real.log (4 * T) ≤ 2 * l T := Tail.log_four_mul_le_two_mul_l hT
  -- the zero set
  set F := Z.window (T - D) (2 * T + D) ∩ {ρ : ℂ | ρ.re = 1 / 2} with hF
  have hfin : F.Finite := (Z.finite_window (T - D) (2 * T + D)).subset Set.inter_subset_left
  set s := hfin.toFinset with hs
  have hmem : ∀ ρ ∈ s, ρ ∈ Z.carrier ∧ T - D < ρ.im ∧ ρ.im ≤ 2 * T + D := by
    intro ρ hρ
    rw [hs, Set.Finite.mem_toFinset] at hρ
    exact hρ.1
  set δ : ℂ → ℝ := fun ρ => deltaW φ L T (P.d T) ρ.im with hδ
  have hδ0 : ∀ ρ, 0 ≤ δ ρ := fun ρ => deltaW_nonneg _ _ _ _ _
  have hδ1 : ∀ ρ, δ ρ ≤ 1 := fun ρ => deltaW_le_one hW hDv0 T _ _
  -- the bulk bound
  have hδbulk : ∀ ρ, T + D < ρ.im → ρ.im ≤ 2 * T - D - 1 → δ ρ ≤ 4 * C₂ / T := by
    intro ρ h1 h2
    have hdh := d_mul_h_gt hL hT0
    have hb := deltaW_le_bulk hW hκ hDv T (P.d T) ρ.im D (by linarith)
      (fun k hk => by
        have hk' : ((-k - 1).toNat : ℝ) = -(k : ℝ) - 1 := by
          rw [toNat_cast_real _ (by omega)]; push_cast; ring
        rw [hk']
        have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith)
      (fun k hk => by
        have hk' : ((k - (P.d T : ℤ)).toNat : ℝ) = (k : ℝ) - (P.d T : ℝ) := by
          rw [toNat_cast_real _ (by omega)]; push_cast; ring
        rw [hk']
        have hkr : (P.d T : ℝ) ≤ k := by exact_mod_cast hk
        have hdT : (P.d T : ℝ) * h > T - h := by
          simpa [Params.d, hLdef, hhdef] using hdh
        rw [abs_of_nonpos (by nlinarith)]
        nlinarith)
    refine hb.trans ?_
    -- 2·(4(c/w)²/L²)·(D⁻⁴ + D⁻³/(3h)) ≤ 16(c/w)²/T
    have hD4 : (D ^ 4)⁻¹ ≤ T⁻¹ := by
      rw [show D ^ 4 = T ^ 2 by rw [← hD2]; ring]
      exact inv_anti₀ (by positivity) (by nlinarith)
    have hD3 : (D ^ 3)⁻¹ / (3 * h) ≤ L * T⁻¹ := by
      rw [hhdef, div_le_iff₀ (by positivity)]
      have h3 : T ≤ D ^ 3 := by nlinarith
      have hTinv : (D ^ 3)⁻¹ ≤ T⁻¹ := inv_anti₀ (by positivity) h3
      have : L * T⁻¹ * (3 * (2 * π / L)) = 6 * π * T⁻¹ := by field_simp; ring
      rw [this]
      have hTi : 0 ≤ T⁻¹ := by positivity
      calc (D ^ 3)⁻¹ ≤ T⁻¹ := hTinv
        _ ≤ 6 * π * T⁻¹ := le_mul_of_one_le_left hTi (by linarith [Real.pi_gt_three])
    have hL1 : 1 ≤ L := by linarith [Real.pi_gt_three]
    have hC : 0 ≤ (c / P.w) ^ 2 := sq_nonneg _
    have hTi : 0 < T⁻¹ := by positivity
    calc 2 * ((c / P.w) ^ 2 / (κ * L ^ 2) * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)))
        ≤ 2 * ((c / P.w) ^ 2 / (κ * L ^ 2) * (T⁻¹ + L * T⁻¹)) := by gcongr
      _ = 2 * C₂ * T⁻¹ * (1 / L ^ 2 + 1 / L) := by rw [hC₂]; field_simp
      _ ≤ 2 * C₂ * T⁻¹ * (1 + 1) := by
          gcongr
          · rw [div_le_one (by positivity)]; nlinarith
          · rw [div_le_one hL]; exact hL1
      _ = 4 * C₂ / T := by ring
  -- split the sum
  have hl0 : 0 ≤ l T := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg T) hl0)]
  have hsum_eq : (∑ᶠ ρ ∈ F, (Z.mult ρ : ℝ) * δ ρ) = ∑ ρ ∈ s, (Z.mult ρ : ℝ) * δ ρ :=
    finsum_mem_eq_finite_toFinset_sum _ hfin
  have hS0 : 0 ≤ ∑ ρ ∈ s, (Z.mult ρ : ℝ) * δ ρ :=
    Finset.sum_nonneg fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (hδ0 ρ)
  show |∑ᶠ ρ ∈ F, (Z.mult ρ : ℝ) * δ ρ| ≤ 2 * K * (Real.sqrt T * l T)
  rw [hsum_eq, abs_of_nonneg hS0]
  set edge := s.filter (fun ρ => ρ.im ≤ T + D ∨ 2 * T - D - 1 < ρ.im) with hedge
  set bulk := s.filter (fun ρ => ¬ (ρ.im ≤ T + D ∨ 2 * T - D - 1 < ρ.im)) with hbulk
  have hsplit : ∑ ρ ∈ s, (Z.mult ρ : ℝ) * δ ρ
      = ∑ ρ ∈ edge, (Z.mult ρ : ℝ) * δ ρ + ∑ ρ ∈ bulk, (Z.mult ρ : ℝ) * δ ρ :=
    (Finset.sum_filter_add_sum_filter_not s _ _).symm
  -- edge: δ ≤ 1 and the local count
  have hE : ∑ ρ ∈ edge, (Z.mult ρ : ℝ) * δ ρ ≤ (4 * D + 3) * (A₀ * Real.log (4 * T)) := by
    have h1 : ∑ ρ ∈ edge, (Z.mult ρ : ℝ) * δ ρ ≤ ∑ ρ ∈ edge, (Z.mult ρ : ℝ) :=
      Finset.sum_le_sum fun ρ _ => mul_le_of_le_one_right (Nat.cast_nonneg _) (hδ1 ρ)
    refine h1.trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not edge (fun ρ => ρ.im ≤ T + D)]
    have hK1 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * D by positivity)
    have hK2 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * D + 1 by positivity)
    have hc1 := count_le Z hA₀0 hloc (T - D) ⌈2 * D⌉₊ (edge.filter (fun ρ => ρ.im ≤ T + D)) (by
      intro ρ hρ
      simp only [hedge, Finset.mem_filter] at hρ
      obtain ⟨hc, h1, h2⟩ := hmem ρ hρ.1.1
      exact ⟨hc, h1, by linarith [Nat.le_ceil (2 * D), hρ.2]⟩)
    have hc2 := count_le Z hA₀0 hloc (2 * T - D - 1) ⌈2 * D + 1⌉₊
      (edge.filter (fun ρ => ¬ ρ.im ≤ T + D)) (by
      intro ρ hρ
      simp only [hedge, Finset.mem_filter] at hρ
      obtain ⟨hc, h1, h2⟩ := hmem ρ hρ.1.1
      have h3 : 2 * T - D - 1 < ρ.im := by
        rcases hρ.1.2 with h | h
        · exact absurd h hρ.2
        · exact h
      exact ⟨hc, h3, by linarith [Nat.le_ceil (2 * D + 1)]⟩)
    have hlog1 : Real.log (|T - D| + ⌈2 * D⌉₊ + 3) ≤ Real.log (4 * T) := by
      apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg (by linarith)]; linarith
    have hlog2 : Real.log (|2 * T - D - 1| + ⌈2 * D + 1⌉₊ + 3) ≤ Real.log (4 * T) := by
      apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg (by linarith)]; linarith
    have hlp : 0 ≤ Real.log (4 * T) := by linarith
    calc _ ≤ ⌈2 * D⌉₊ * (A₀ * Real.log (|T - D| + ⌈2 * D⌉₊ + 3))
          + ⌈2 * D + 1⌉₊ * (A₀ * Real.log (|2 * T - D - 1| + ⌈2 * D + 1⌉₊ + 3)) := add_le_add hc1 hc2
      _ ≤ (2 * D + 1) * (A₀ * Real.log (4 * T)) + (2 * D + 2) * (A₀ * Real.log (4 * T)) := by
          have a1 := abs_nonneg (T - D)
          have a2 := abs_nonneg (2 * T - D - 1)
          have n1 := Nat.cast_nonneg (α := ℝ) ⌈2 * D⌉₊
          have n2 := Nat.cast_nonneg (α := ℝ) ⌈2 * D + 1⌉₊
          refine add_le_add (mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hlog1 hA₀0)
            (mul_nonneg hA₀0 (Real.log_nonneg (by linarith))) (by positivity))
            (mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hlog2 hA₀0)
            (mul_nonneg hA₀0 (Real.log_nonneg (by linarith))) (by positivity))
      _ = (4 * D + 3) * (A₀ * Real.log (4 * T)) := by ring
  -- bulk: δ ≤ 16(c/w)²/T and the count of all of I′
  have hB : ∑ ρ ∈ bulk, (Z.mult ρ : ℝ) * δ ρ ≤ 8 * C₂ * (A₀ * Real.log (4 * T)) := by
    have hβ0 : 0 ≤ 4 * C₂ / T := by positivity
    have h1 : ∑ ρ ∈ bulk, (Z.mult ρ : ℝ) * δ ρ ≤ ∑ ρ ∈ s, (Z.mult ρ : ℝ) * (4 * C₂ / T) := by
      refine (Finset.sum_le_sum fun ρ hρ => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ s) fun ρ _ _ =>
          mul_nonneg (Nat.cast_nonneg _) hβ0)
      simp only [hbulk, Finset.mem_filter, not_or, not_le, not_lt] at hρ
      exact mul_le_mul_of_nonneg_left (hδbulk ρ hρ.2.1 hρ.2.2) (Nat.cast_nonneg _)
    refine h1.trans ?_
    rw [← Finset.sum_mul]
    have hK3 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ T + 2 * D by positivity)
    have hc3 := count_le Z hA₀0 hloc (T - D) ⌈T + 2 * D⌉₊ s (by
      intro ρ hρ
      obtain ⟨hc, h1, h2⟩ := hmem ρ hρ
      exact ⟨hc, h1, by linarith [Nat.le_ceil (T + 2 * D)]⟩)
    have hlog3 : Real.log (|T - D| + ⌈T + 2 * D⌉₊ + 3) ≤ Real.log (4 * T) := by
      apply Real.log_le_log (by positivity)
      rw [abs_of_nonneg (by linarith)]; linarith
    have hcount : ∑ ρ ∈ s, (Z.mult ρ : ℝ) ≤ 2 * T * (A₀ * Real.log (4 * T)) := by
      refine hc3.trans ?_
      have e0 : 2 * D + 1 ≤ T := by nlinarith
      have e1 : (⌈T + 2 * D⌉₊ : ℝ) ≤ 2 * T := by linarith
      have e2 : A₀ * Real.log (|T - D| + ⌈T + 2 * D⌉₊ + 3) ≤ A₀ * Real.log (4 * T) :=
        mul_le_mul_of_nonneg_left hlog3 hA₀0
      have e3 : 0 ≤ A₀ * Real.log (|T - D| + ⌈T + 2 * D⌉₊ + 3) :=
        mul_nonneg hA₀0 (Real.log_nonneg (by
          have := abs_nonneg (T - D); have := Nat.cast_nonneg (α := ℝ) ⌈T + 2 * D⌉₊; linarith))
      exact mul_le_mul e1 e2 e3 (by positivity)
    have hfin2 : 2 * T * (A₀ * Real.log (4 * T)) * (4 * C₂ / T)
        = 8 * C₂ * (A₀ * Real.log (4 * T)) := by
      field_simp; ring
    rw [← hfin2]
    exact mul_le_mul_of_nonneg_right hcount hβ0
  -- total
  have hlp : 0 ≤ A₀ * Real.log (4 * T) := by positivity
  have hD1 : 1 ≤ D := by linarith
  rw [hsplit]
  calc _ ≤ (4 * D + 3) * (A₀ * Real.log (4 * T)) + 8 * C₂ * (A₀ * Real.log (4 * T)) :=
        add_le_add hE hB
    _ ≤ K * D * Real.log (4 * T) := by
        rw [hK]
        have hlg : 0 ≤ Real.log (4 * T) := by linarith
        have e1 : (4 * D + 3) ≤ 7 * D := by linarith
        have e2 : 8 * C₂ ≤ 8 * C₂ * D := by nlinarith
        have := mul_le_mul_of_nonneg_right (add_le_add e1 e2) hlp
        nlinarith
    _ ≤ K * D * (2 * l T) := by
        have hK0 : 0 ≤ K := by rw [hK]; positivity
        gcongr
    _ = 2 * K * (Real.sqrt T * l T) := by rw [hDdef]; ring

end Z6
end ZetaS

end
