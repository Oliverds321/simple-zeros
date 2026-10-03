/-
L7_9 round 4: the difference `D_T(s − log(m+1)) − D_T(s − log m)` with the decay of `D_T′`
(L7_5's shared `DT_Facts`: `‖D_T′‖ ≤ 2T²`, `‖D_T′(v)‖ ≤ 4T/|v|`), in the block form
`≤ (1/m)·16T²/(|k| + 1)`, `k = ⌊T(log m − s)⌋`, for `m ≥ T ≥ 1`; and a counting lemma.
-/
import ZetaShell.Defs.LK_Defs
import ZetaShell.PropZ.DT_Facts

noncomputable section

namespace ZetaShell
namespace LemmaK
namespace K6

lemma DT_eq_DTf (T v : ℝ) : DT T v = ZetaShell.DTFacts.DTf T v := rfl

lemma deriv_bound_block (T : ℝ) (hT : 1 ≤ T) (k : ℤ) (u : ℝ)
    (hu1 : (k : ℝ) / T ≤ -u) (hu2 : -u ≤ ((k : ℝ) + 2) / T) :
    ‖deriv (ZetaShell.DTFacts.DTf T) u‖ ≤ 16 * T ^ 2 / (|(k : ℝ)| + 1) := by
  have hT0 : 0 < T := by linarith
  have hb2 := ZetaShell.DTFacts.norm_deriv_DTf_le (T := T) (by linarith) u
  rcases (show k ≥ 1 ∨ (-2 ≤ k ∧ k ≤ 0) ∨ k ≤ -3 by omega) with h | h | h
  · have hk : (1 : ℝ) ≤ k := by exact_mod_cast h
    have hkT : 0 < (k : ℝ) / T := div_pos (by linarith) hT0
    have hneg : u < 0 := by linarith
    have hu0 : (k : ℝ) / T ≤ |u| := by rw [abs_of_neg hneg]; linarith
    have hupos : 0 < |u| := lt_of_lt_of_le (by positivity) hu0
    have hb := ZetaShell.DTFacts.norm_deriv_DTf_le_div (T := T) (by linarith)
      (v := u) (abs_pos.mp hupos)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ k)]
    refine hb.trans ?_
    rw [div_le_div_iff₀ hupos (by linarith)]
    have : (k : ℝ) ≤ T * |u| := by rwa [div_le_iff₀ hT0, mul_comm] at hu0
    nlinarith
  · have hk1 : (-2 : ℝ) ≤ k := by exact_mod_cast h.1
    have hk2 : (k : ℝ) ≤ 0 := by exact_mod_cast h.2
    refine hb2.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have : |(k : ℝ)| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  · have hk : (k : ℝ) ≤ -3 := by exact_mod_cast h
    have hu0 : (-(k : ℝ) - 2) / T ≤ u := by
      have : -u ≤ ((k : ℝ) + 2) / T := hu2
      rw [show (-(k : ℝ) - 2) / T = -(((k : ℝ) + 2) / T) by ring]; linarith
    have hpos : 0 < (-(k : ℝ) - 2) / T := by apply div_pos _ hT0; linarith
    have hupos : 0 < u := lt_of_lt_of_le hpos hu0
    have hb := ZetaShell.DTFacts.norm_deriv_DTf_le_div (T := T) (by linarith)
      (v := u) hupos.ne'
    rw [abs_of_pos hupos] at hb
    rw [abs_of_neg (by linarith : (k : ℝ) < 0)]
    refine hb.trans ?_
    rw [div_le_div_iff₀ hupos (by linarith)]
    have : -(k : ℝ) - 2 ≤ T * u := by rwa [div_le_iff₀ hT0, mul_comm] at hu0
    nlinarith

/-- the block bound for one step of `D_T(s − log ·)`. -/
theorem dD_block (T s : ℝ) (hT : 1 ≤ T) (m : ℕ) (hm : T ≤ (m : ℝ)) :
    ‖DT T (s - Real.log ((m + 1 : ℕ) : ℝ)) - DT T (s - Real.log m)‖
      ≤ (1 / (m : ℝ)) * (16 * T ^ 2 / (|((⌊T * (Real.log m - s)⌋ : ℤ) : ℝ)| + 1)) := by
  set k : ℤ := ⌊T * (Real.log m - s)⌋ with hk
  have hT0 : 0 < T := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hk1 := Int.floor_le (T * (Real.log m - s))
  have hk2 := Int.lt_floor_add_one (T * (Real.log m - s))
  rw [← hk] at hk1 hk2
  set a := s - Real.log ((m + 1 : ℕ) : ℝ) with ha
  set b := s - Real.log m with hb
  have hlog : Real.log ((m + 1 : ℕ) : ℝ) - Real.log m ≤ 1 / m := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((m + 1 : ℕ) : ℝ) / m by positivity)
    rw [Real.log_div (by positivity) hm0.ne'] at h
    have e : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by push_cast; field_simp; ring
    linarith
  have hlog0 : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log m :=
    sub_nonneg.mpr (Real.log_le_log hm0 (by push_cast; linarith))
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hinvT : 1 / (m : ℝ) ≤ 1 / T := one_div_le_one_div_of_le hT0 hm
  -- MVT on `[a, b]`
  have hderiv : ∀ x ∈ Set.Icc a b, HasDerivWithinAt (ZetaShell.DTFacts.DTf T)
      (deriv (ZetaShell.DTFacts.DTf T) x) (Set.Icc a b) x := by
    intro x _
    exact ((ZetaShell.DTFacts.hasDerivAt_DTf T x).differentiableAt.hasDerivAt).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b, ‖deriv (ZetaShell.DTFacts.DTf T) x‖
      ≤ 16 * T ^ 2 / (|(k : ℝ)| + 1) := by
    intro x hx
    apply deriv_bound_block T hT k x
    · have : (k : ℝ) / T ≤ Real.log m - s := by rw [div_le_iff₀ hT0]; linarith
      linarith [hx.2]
    · have h1 : Real.log m - s < ((k : ℝ) + 1) / T := by rw [lt_div_iff₀ hT0]; linarith
      have h2 : -x ≤ Real.log ((m + 1 : ℕ) : ℝ) - s := by linarith [hx.1]
      have h3 : ((k : ℝ) + 1) / T + 1 / T = ((k : ℝ) + 2) / T := by field_simp; ring
      linarith
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b ⟨hab, le_refl b⟩
  rw [← DT_eq_DTf, ← DT_eq_DTf] at hmvt
  rw [norm_sub_rev]
  refine hmvt.trans ?_
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [ha, hb]; linarith

/-- the naturals in `[a, b)` number at most `b − a + 1`. -/
lemma card_le_of_Ico (S : Finset ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ x ∈ S, a ≤ (x : ℝ) ∧ (x : ℝ) < b) : (S.card : ℝ) ≤ b - a + 1 := by
  have hsub : S ⊆ Finset.Ico ⌈a⌉₊ ⌈b⌉₊ := by
    intro x hx
    obtain ⟨h1, h2⟩ := h x hx
    rw [Finset.mem_Ico]
    exact ⟨Nat.ceil_le.mpr h1, Nat.lt_ceil.mpr h2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hb0 : 0 ≤ b := le_trans ha hab
  have hcb := Nat.ceil_lt_add_one hb0
  have hca := Nat.le_ceil a
  by_cases hle : ⌈a⌉₊ ≤ ⌈b⌉₊
  · have : ((⌈b⌉₊ - ⌈a⌉₊ : ℕ) : ℝ) = (⌈b⌉₊ : ℝ) - ⌈a⌉₊ := Nat.cast_sub hle
    have hc' : (S.card : ℝ) ≤ ((⌈b⌉₊ - ⌈a⌉₊ : ℕ) : ℝ) := by exact_mod_cast hc
    linarith
  · rw [not_le] at hle
    have : ⌈b⌉₊ - ⌈a⌉₊ = 0 := by omega
    rw [this] at hc
    have : S.card = 0 := by omega
    rw [this]; push_cast; linarith

end K6
end LemmaK
end ZetaShell
