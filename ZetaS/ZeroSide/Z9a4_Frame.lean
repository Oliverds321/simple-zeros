/-
Sub-node Z9a4 (agent L3_1) — the frame at one height, as a definition: every field of the architect's `ZeroFrame`
is produced from the tree-level objects (so `ZeroFrame` is satisfiable as stated):
  on-line zeros of I′ sorted by ordinate (Z9a1), U = (u_{γ_i}(k)), x_i = γ_iL/2π, k = kWin (Z2 fix), Etr = off-grid
  Gram (Z3), gram_eq (Z1, `ZeroSide.gram_eq_matrix`), Qoff = off-line block over β > ½ with n₊, n₋ ≤ p (Z9a2),
  p₁ = simple representatives, N_off = 2Σ_{β>½} m ≥ 2p₁ + 4(p − p₁), Λ = |I′|L/2π with x_j − x_i ≤ Λ.
Also the trivial frame `dummyFrame` (d = n = 0) for heights where the window is not admissible.
-/
import ZetaS.ZeroSide.Z9a1_OnLineSort
import ZetaS.ZeroSide.Z9a3_HatDecomp
import ZetaS.ZeroSide.Z2_KWinPosDef
import ZetaS.ZeroSide.Z3_OffGridPSD

noncomputable section

open Matrix RHLinalg

namespace ZetaS
namespace Z9

open Zeta23

/-- the trivial frame (no grid, no zeros). -/
def dummyFrame : ZeroFrame where
  d := 0
  n := 0
  m := Fin.elim0
  one_le_m := fun i => i.elim0
  x := Fin.elim0
  x_mono := fun i => i.elim0
  U := 0
  k := fun _ => 1
  k_zero := rfl
  k_even := fun _ => rfl
  k_posDef := fun n x => by
    refine ZeroSide.posSemidef_of_hasSum (fun (_ : Fin n) (_ : Unit) => (1 : ℝ)) _ fun i j => ?_
    simpa [kerMat] using hasSum_fintype (fun (_ : Unit) => (1 : ℝ) * 1)
  Etr := 0
  Etr_psd := PosSemidef.zero
  gram_eq := by ext i; exact i.elim0
  Qoff := 0
  Qoff_herm := isHermitian_zero
  p := 0
  p1 := 0
  p1_le := le_rfl
  nplus_off := (posIndex_le_card _).trans_eq (by simp)
  nminus_off := by
    rw [negIndex_eq_posIndex_neg]; exact (posIndex_le_card _).trans_eq (by simp)
  Noff := 0
  Noff_ge := le_rfl
  Λ := 0
  Λ_nonneg := le_rfl
  x_span := fun i => i.elim0

variable (Z : ZeroConfig) {P : Params} (ψ : ℝ → ℝ) (T : ℝ)

/-- the on-line zeros of I′ and the off-line representatives (β > ½). -/
abbrev Son : Finset ℂ := (ZeroSide.ZI Z T).filter (fun ρ => ρ.re = 1 / 2)
abbrev Aoff : Finset ℂ := (ZeroSide.ZI Z T).filter (fun ρ => 1 / 2 < ρ.re)

lemma Son_re (ρ : ℂ) (h : ρ ∈ Son Z T) : ρ.re = 1 / 2 := (Finset.mem_filter.mp h).2

/-- the sorted ordinates of the on-line zeros and the enumeration. -/
def gOn : Fin (Son Z T).card → ℝ := Classical.choose (onLine_enum (Son Z T) (Son_re Z T))
lemma gOn_mono : StrictMono (gOn Z T) := (Classical.choose_spec (onLine_enum (Son Z T) (Son_re Z T))).1
def eOn : Fin (Son Z T).card ≃ Son Z T :=
  Classical.choose (Classical.choose_spec (onLine_enum (Son Z T) (Son_re Z T))).2
lemma eOn_eq (i : Fin (Son Z T).card) : (eOn Z T i : ℂ) = (1 / 2 : ℂ) + (gOn Z T i : ℂ) * Complex.I :=
  Classical.choose_spec (Classical.choose_spec (onLine_enum (Son Z T) (Son_re Z T))).2 i

lemma eOn_mem_ZIprime (i : Fin (Son Z T).card) : (eOn Z T i : ℂ) ∈ Z.ZIprime T :=
  (ZeroSide.mem_ZI Z T).mp (Finset.mem_filter.mp (eOn Z T i).2).1

lemma eOn_im (i : Fin (Son Z T).card) : (eOn Z T i : ℂ).im = gOn Z T i := by
  rw [eOn_eq]; simp

lemma gOn_mem (i : Fin (Son Z T).card) :
    T - Real.sqrt T < gOn Z T i ∧ gOn Z T i ≤ 2 * T + Real.sqrt T := by
  have h := (ZeroSide.mem_ZIprime_iff Z T).mp (eOn_mem_ZIprime Z T i)
  rw [eOn_im] at h
  exact ⟨h.2.1, h.2.2⟩

/-- **the frame at height `T`** (for an admissible window with `∫ φ_T² ≠ 0`). -/
def frameAt (hP : P.Valid) (heven : ∀ s, ψ (-s) = ψ s) {c : ℝ}
    (hW : AdmWindow (P.phiV ψ T) (P.L T) P.w c) (hv : (∫ u, P.phiV ψ T u ^ 2) ≠ 0) (hT : 0 < T) :
    ZeroFrame where
  d := P.d T
  n := (Son Z T).card
  m := fun i => Z.mult (eOn Z T i)
  one_le_m := fun i => Z.one_le_mult _ (ZeroSide.mem_carrier_of_mem_ZI Z T (Finset.mem_filter.mp (eOn Z T i).2).1)
  x := fun i => gOn Z T i * P.L T / (2 * Real.pi)
  x_mono := fun i j hij => by
    have := gOn_mono Z T hij
    have hL := hW.L_pos
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right this hL) (by positivity)
  U := Matrix.of fun (k : Fin (P.d T)) (i : Fin (Son Z T).card) => uR (P.phiV ψ T) (P.L T) T (gOn Z T i) (k : ℕ)
  k := kWin (P.phiV ψ T) (P.L T)
  k_zero := (kWin_posDef_fix hW hv).2.1
  k_even := (kWin_posDef_fix hW hv).2.2
  k_posDef := (kWin_posDef_fix hW hv).1
  Etr := Matrix.of fun i j => ∑' k : offGrid (P.d T),
    uR (P.phiV ψ T) (P.L T) T (gOn Z T i) k.1 * uR (P.phiV ψ T) (P.L T) T (gOn Z T j) k.1
  Etr_psd := offGrid_psd hW T (P.d T) (gOn Z T)
  gram_eq := ZeroSide.gram_eq_matrix hW T (P.d T) (gOn Z T)
  Qoff := offBlock (Aoff Z T) (fun ρ => 2 * (Z.mult ρ : ℝ))
    (fun ρ k => (uvec P ψ T ρ k).re) (fun ρ k => (uvec P ψ T ρ k).im)
  Qoff_herm := offBlock_herm _ _ _ _
  p := (Aoff Z T).card
  p1 := ((Aoff Z T).filter (fun ρ => Z.mult ρ = 1)).card
  p1_le := Finset.card_filter_le _ _
  nplus_off := (offBlock_inertia _ _ (fun ρ _ => by positivity) _ _).1
  nminus_off := (offBlock_inertia _ _ (fun ρ _ => by positivity) _ _).2
  Noff := 2 * ∑ ρ ∈ Aoff Z T, Z.mult ρ
  Noff_ge := by
    classical
    have hsplit := Finset.sum_filter_add_sum_filter_not (Aoff Z T) (fun ρ => Z.mult ρ = 1) Z.mult
    have hcard := Finset.card_filter_add_card_filter_not (s := Aoff Z T) (fun ρ => Z.mult ρ = 1)
    have h1 : ((Aoff Z T).filter (fun ρ => Z.mult ρ = 1)).card
        ≤ ∑ ρ ∈ (Aoff Z T).filter (fun ρ => Z.mult ρ = 1), Z.mult ρ := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun ρ hρ => (Finset.mem_filter.mp hρ).2.ge
    have h2 : 2 * ((Aoff Z T).filter (fun ρ => ¬ Z.mult ρ = 1)).card
        ≤ ∑ ρ ∈ (Aoff Z T).filter (fun ρ => ¬ Z.mult ρ = 1), Z.mult ρ := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have hne := (Finset.mem_filter.mp hρ).2
      have hA := (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).1
      have h1 := Z.one_le_mult ρ (ZeroSide.mem_carrier_of_mem_ZI Z T hA)
      omega
    omega
  Λ := (T + 2 * Real.sqrt T) * P.L T / (2 * Real.pi)
  Λ_nonneg := by have := hW.L_pos; have := Real.sqrt_nonneg T; positivity
  x_span := fun i j => by
    have hi := gOn_mem Z T i
    have hj := gOn_mem Z T j
    have hL := hW.L_pos
    rw [← sub_div, ← sub_mul]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) hL.le

end Z9
end ZetaS
