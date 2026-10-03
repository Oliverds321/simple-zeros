/-
lean_work/L6_1/C25_ClassBridge.lean — track C node C25 (agent L6_1, 28 Sep 2026; statement from
lean_work/L1_1/nodes/C25_ClassBridge.lean, unchanged): one checker instance `classData` ⟺ the all-marks inequality
(LI_m) of `W5` for that pattern (index translation ℕ → ℝ versus Fin 4 → ℝ; pattern weights; claim).
Proof: `classData_F` — for every g : ℕ → ℝ, `(classData ..).F g = localFm (kPsi psiCos16) W5 m (g ∘ val)` (spans:
`gapSpan = spanVal` for i + s ≤ 4; the ten span terms and four penalty terms expanded; k = kCos by node C23);
`classData_claim` — the claim is Σ_i b_i(m_i). Then extend g : Fin 4 → ℝ by zero.
Imports C23 (L6_1) for `kPsi_psiCos16_eq'`.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C23_KPsiCos

noncomputable section

open Set

namespace ZetaS.CertV2

theorem gapSpan_eq_spanVal (g : ℕ → ℝ) {i s : ℕ} (h : i + s ≤ 4) :
    gapSpan (K := 5) (fun l : Fin (5 - 1) => g l) i s = spanVal g i s := by
  unfold gapSpan spanVal
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun l => if i ≤ l ∧ l < i + s then g l else 0) (5 - 1),
    ← Finset.sum_filter]
  have hset : (Finset.range (5 - 1)).filter (fun l => i ≤ l ∧ l < i + s) = Finset.Ico i (i + s) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

theorem mL_getD (m : Fin 5 → Fin 2) {i : ℕ} (hi : i < 5) :
    ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1).getD i 1 = (m ⟨i, hi⟩ : ℕ) + 1 := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem markVal_lt (m : Fin 5 → Fin 2) {i : ℕ} (hi : i < 5) : markVal m i = ((m ⟨i, hi⟩ : ℕ) : ℝ) + 1 := by
  unfold markVal
  rw [dif_pos hi]

/-- the span list of a class instance as a double Finset sum. -/
theorem spans_sum (T : ℕ → ℕ → ℚ) (Φ : ℕ × ℕ × ℚ → ℝ) :
    (((List.range 4).flatMap fun s => (List.range (4 - s)).map fun i => (i, s + 1, T s i)).map Φ).sum
      = ∑ s ∈ Finset.range 4, ∑ i ∈ Finset.range (4 - s), Φ (i, s + 1, T s i) := by
  have r4 : List.range 4 = [0, 1, 2, 3] := rfl
  have r3 : List.range 3 = [0, 1, 2] := rfl
  have r2 : List.range 2 = [0, 1] := rfl
  have r1 : List.range 1 = [0] := rfl
  simp only [r4, List.flatMap_cons, List.flatMap_nil, Nat.sub_zero, Nat.reduceSub, r3, r2, r1, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.append_nil, List.sum_cons, List.sum_nil,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- the (s, i) double sum of `localFm` re-indexed from s ∈ [1, 4] to s + 1, s ∈ [0, 4). -/
theorem Icc_sum (f : ℕ → ℕ → ℝ) :
    ∑ s ∈ Finset.Icc 1 (5 - 1), ∑ i ∈ Finset.range (5 - s), f s i
      = ∑ s ∈ Finset.range 4, ∑ i ∈ Finset.range (4 - s), f (s + 1) i := by
  rw [show Finset.Icc 1 (5 - 1) = {1, 2, 3, 4} by rfl]
  simp [Finset.sum_range_succ]
  ring

theorem classData_F (m : Fin 5 → Fin 2) (g : ℕ → ℝ) :
    (classData ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1)).F g
      = localFm (kPsi psiCos16) W5 m (fun l => g l) := by
  have hk : kPsi psiCos16 = kCos := funext kPsi_psiCos16_eq'
  rw [hk]
  unfold localFm LIQ.F classData
  simp only []
  congr 1
  · rw [spans_sum, Icc_sum]
    refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hs hi
    rw [gapSpan_eq_spanVal g (by omega), mL_getD m (by omega : i < 5), mL_getD m (by omega : i + s + 1 < 5),
      markVal_lt m (by omega : i < 5), markVal_lt m (by omega : i + (s + 1) < 5)]
    have e : (⟨i + (s + 1), (by omega : i + (s + 1) < 5)⟩ : Fin 5) = ⟨i + s + 1, by omega⟩ := by
      ext; simp only; omega
    rw [e]
    show _ = (gam5 (s + 1) i : ℝ) * _ * _ * _
    push_cast
    ring

theorem classData_claim (m : Fin 5 → Fin 2) :
    (((classData ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1)).claim : ℚ) : ℝ)
      = ∑ i, W5.b i (m i) := by
  have hsum : ∀ f : ℕ → ℚ, ((List.range 5).map f).sum = ∑ i : Fin 5, f i := by
    intro f
    rw [show List.range 5 = [0, 1, 2, 3, 4] from rfl, Fin.sum_univ_five]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
    rfl
  have hfin : ∀ j : Fin 2, (if (j : ℕ) + 1 = 2 then (1 : Fin 2) else 0) = j := by decide
  unfold classData
  simp only []
  rw [hsum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.2, mL_getD m i.2, hfin]
  rfl

/-- = `classData_holds_iff` of CertSpecAM5. -/
theorem classData_holds_iff' (m : Fin 5 → Fin 2) :
    (classData ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1)).Holds ↔
      ∀ g : Fin 4 → ℝ, (∀ l, 0 ≤ g l) → ∑ i, W5.b i (m i) ≤ localFm (kPsi psiCos16) W5 m g := by
  unfold LIQ.Holds
  rw [classData_claim]
  constructor
  · intro h g hg
    have := h (fun l => if hl : l < 4 then g ⟨l, hl⟩ else 0) (fun l => by
      by_cases hl : l < 4
      · simp only [hl, dif_pos]; exact hg _
      · simp only [hl, dif_neg, not_false_eq_true, le_refl])
    rw [classData_F] at this
    convert this using 2
    funext l
    simp [l.2]
  · intro h g hg
    rw [classData_F]
    exact h _ fun l => hg l

end ZetaS.CertV2
